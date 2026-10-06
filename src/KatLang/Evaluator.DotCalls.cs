using System.Collections;
using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang;

/// <summary>
/// Dot-call evaluation: sequence-pipeline recognition, ordinary lexical receiver injection, and structural-first dot-call dispatch (the "DotCall evaluation" section).
/// Part of the <see cref="Evaluator"/> partial class; the central state, lookup and open resolution,
/// the built-in prelude, and the run entry points remain in <c>Evaluator.cs</c>.
/// </summary>
public static partial class Evaluator
{
    // ── DotCall evaluation ────────────────────────────────────────────────

    /// <summary>
    /// Evaluates dotCall <c>a.f</c> / <c>a.f(args)</c> with plain Result
    /// output. This is the value projection of
    /// <see cref="EvalDotCallCounted"/>: the counted twin owns the whole
    /// dot-call dispatch (sequence-pipeline hook, receiver resolution,
    /// value-based intrinsics, structural property precedence and exposure,
    /// conditional dispatch, and lexical fallback with receiver injection),
    /// and the non-counted path only discards the emitted-count metadata —
    /// mirroring Lean, where <c>evalDotCall</c> projects
    /// <c>evalDotCallCounted</c>.
    /// Lean: evalDotCall.
    /// </summary>
    private static EvalResult<Result> EvalDotCall(
        Expr.DotCall dotCall,
        EvalCtx ctx,
        ValEnv valEnv)
        => ProjectCountedValue(EvalDotCallCounted(dotCall, ctx, valEnv));

    /// <summary>
    /// Assemble the argument bundle for extension dot-call fallback: DOT-CALL
    /// PASSES A VALUE — <c>receiver.F(C, D)</c> is exactly the bundle of the
    /// written call <c>F(receiver, C, D)</c>, the ORIGINAL receiver expression
    /// as the ordinary first argument slot followed by the written extra
    /// arguments. Assembly is independent of the resolved callee: the receiver
    /// is never pre-expanded, never unwrapped, never given a supply of its
    /// own, and no parameter shape is inspected; a spread receiver is the
    /// ordinary spread slot <c>F(R*, …)</c>.
    /// Lean: <c>prepareLexicalDotCallArgs</c> (laws
    /// <c>dot_receiver_is_ordinary_leading_argument</c>,
    /// <c>spread_dot_receiver_is_ordinary_spread_argument</c>).
    /// </summary>
    private static OutputBundle BuildLexicalReceiverCallArgs(
        Expr receiver,
        OutputBundle? extraArgs)
    {
        var outputExprs = new Expr[1 + (extraArgs?.Count ?? 0)];
        outputExprs[0] = receiver;
        if (extraArgs is not null)
        {
            for (var i = 0; i < extraArgs.Count; i++)
                outputExprs[i + 1] = extraArgs[i];
        }

        // outputExprs is this call's exclusively owned fresh array, so
        // ownership transfers without a snapshot copy.
        return OutputBundle.TakeOwnership(outputExprs);
    }

    /// <summary>
    /// The production allocation-free sequence-pipeline gate shared by the two expression-position
    /// dispatch sites (<see cref="EvalCallCountedExpr"/> and
    /// <see cref="EvalDotCallCounted"/>). PERFORMANCE ORDERING IS LOAD-BEARING:
    /// recognition is intentionally performed BEFORE entering
    /// <see cref="TryEvaluateRecognizedSequencePipeline"/>, the separate helper that
    /// contains the run-specific captured delegates. This helper boundary makes it
    /// structurally impossible for the C# compiler to hoist their display-class
    /// allocation onto an ordinary miss path; allocation freedom does not depend on
    /// current JIT escape analysis. (An explicitly attached internal diagnostics
    /// collector may allocate its own records.) A fusion-disabled run with no diagnostics attached
    /// skips even recognition: nothing recognition could do there is observable
    /// (recognition charges no budget, and <see cref="SequencePipelineDiagnostics"/> is
    /// an internal harness channel that production runs never attach). Pinned by
    /// <c>SequencePipelineDispatchTests</c> and the dispatch benchmarks.
    /// </summary>
    private static bool TryEvaluateSequencePipeline(
        SequencePipelineInvocation invocation,
        EvalCtx ctx,
        ValEnv valEnv,
        out EvalResult<CountedResult> result)
    {
        result = default;
        var diagnostics = ctx.SequenceDiagnostics;

        if (!ctx.EnableSequencePipelineOptimization && diagnostics is null)
            return false;

        if (!SequencePipelineOptimizer.TryRecognize(
            invocation,
            ctx.EnableSequencePipelineOptimization,
            diagnostics,
            out var syntax))
            return false;

        return TryEvaluateRecognizedSequencePipeline(
            syntax,
            invocation,
            ctx,
            valEnv,
            diagnostics,
            out result);
    }

    /// <summary>
    /// The closure-bearing half of the sequence-pipeline dispatch. This method is
    /// entered only after the allocation-free gate recognized an enabled candidate,
    /// so its one display class and five capturing delegates are candidate-only by
    /// source structure, independently of compiler/JIT allocation sinking.
    /// </summary>
    private static bool TryEvaluateRecognizedSequencePipeline(
        FilterCountPipelineSyntax syntax,
        SequencePipelineInvocation invocation,
        EvalCtx ctx,
        ValEnv valEnv,
        SequencePipelineDiagnostics? diagnostics,
        out EvalResult<CountedResult> result)
    {
        ctx.Observations?.RecordSequencePipelineServiceConstruction();
        var services = new SequencePipelineEvaluationServices(
            GetDotCallLexicalBuiltinFallbackReason: (stageDotCall, expectedBuiltin) =>
                GetDotCallLexicalBuiltinFallbackReason(stageDotCall, expectedBuiltin, ctx),
            EvaluateDotReceiverIterationItems: receiver => EvaluateDotReceiverIterationItemsForSequenceOptimizer(receiver, ctx, valEnv),
            ResolveArgumentAlgorithms: args => ResolveArgAlgsWithSequenceSpread(args, ctx, valEnv),
            // Recognition resolves CALLEES (`filter` in `count(filter(…))`, `range` in its source),
            // so it reads the ONE callee identity the generic call reads (DOT-09).
            ResolveAlgorithm: expr => ResolveCallee(expr, ctx),
            EvaluateRangeCallArguments: (function, args, callSpan) => EvaluateRangeCallArgumentsForSequenceOptimizer(function, args, callSpan, ctx, valEnv));

        return SequencePipelineOptimizer.TryExecuteRecognized(
            syntax,
            invocation,
            services,
            ctx,
            valEnv,
            diagnostics,
            out result);
    }

    /// <summary>
    /// Semantic dot-receiver item collection shared with the sequence optimizer.
    /// DOT-CALL PASSES A VALUE: the receiver of <c>R.filter(P)</c> is the
    /// builtin's ordinary <c>collection</c> argument — exactly the first written
    /// argument of <c>filter(R, P)</c> — so it is resolved and demanded through
    /// the ONE builtin argument funnel the generic path uses
    /// (<see cref="ResolveArgAlgsWithSequenceSpread"/> +
    /// <see cref="BuildCallableCallItems"/> with <c>filter</c>'s metadata, whose position 0
    /// is the VALUE slot <c>collection</c> +
    /// <see cref="BindSequenceBuiltinCollectionArgument"/>): a named property is
    /// read through its ordinary property access (the run cache), a parameterized
    /// receiver is the collection-argument demand rejection, and the bound value opens
    /// through the shared post-binding collection view. The fused and generic
    /// strategies therefore evaluate, charge, and reject the receiver identically.
    /// </summary>
    private static EvalResult<IReadOnlyList<CountedResult>> EvaluateDotReceiverIterationItemsForSequenceOptimizer(
        Expr receiver,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var receiverArgsR = ResolveArgAlgsWithSequenceSpread(OutputBundle.TakeOwnership([receiver]), ctx, valEnv);
        if (receiverArgsR.IsError)
            return receiverArgsR.Error;

        var itemsR = BuildCallableCallItems(
            receiverArgsR.Value,
            ctx,
            valEnv,
            GetSequenceBuiltinMetadata(BuiltinId.@filter)!.Value);
        if (itemsR.IsError)
            return itemsR.Error;

        // A spread receiver never reaches this adapter (the optimizer declines it),
        // so the receiver is exactly one call item — the collection argument.
        if (itemsR.Value.Count != 1)
            return new EvalError.ArityMismatch(1, itemsR.Value.Count);

        var collectionValuesR = BindSequenceBuiltinCollectionArgument(itemsR.Value[0], ctx, valEnv);
        if (collectionValuesR.IsError)
            return collectionValuesR.Error;

        return EvalResult<IReadOnlyList<CountedResult>>.Ok(
            collectionValuesR.Value
                .Select(static item => new CountedResult(item, item.ValueCount()))
                .ToList());
    }

    /// <summary>
    /// Evaluate already-recognized builtin <c>range(...)</c> arguments for the
    /// sequence optimizer while preserving the generic range call diagnostics, and RESERVE
    /// the item slots the generic range call materializes (the per-collection ceiling and
    /// the cumulative materialization budget alike, with the generic range's limit-error
    /// span) without building the list: the cumulative budget is charged exactly as the
    /// generic composition charges it, so a configured <see cref="EvaluationLimits.MaxMaterializedItems"/>
    /// needs no strategy of its own (Q-09b).
    /// </summary>
    private static EvalResult<InclusiveRange> EvaluateRangeCallArgumentsForSequenceOptimizer(
        Expr function,
        OutputBundle args,
        SourceSpan? callSpan,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // Range arguments use the same supply cells as an ordinary range call. No
        // hidden argument wrapper introduces a language invocation level.
        var rangeR = WithSpan(callSpan, WithCallCtx(CallDiagnosticName.FromExpression(function),
            ctx, EvalBuiltinRangeCallArguments(args, ctx, valEnv)));
        if (rangeR.IsError) return rangeR;
        // The generic range call reserves its list right here (BuildInclusiveRangeChecked),
        // after its bounds; a refusal is unspanned there until the range call's own boundary
        // positions it, which is the span attached here.
        return ctx.Budget.TryReserveCollection(CountInclusiveRangeValues(rangeR.Value)) is { } limitError
            ? AtSpanIfMissing(limitError, callSpan) : rangeR;
    }

    private static EvalResult<InclusiveRange> EvalBuiltinRangeCallArguments(
        OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var argAlgsR = ResolveArgAlgsWithSequenceSpread(args, ctx, valEnv);
        if (argAlgsR.IsError) return argAlgsR.Error;

        var expandedArgsR = ExpandSequenceSpreadBuiltinArguments(argAlgsR.Value, ctx, valEnv);
        if (expandedArgsR.IsError) return expandedArgsR.Error;

        return EvalBuiltinRangeArguments(expandedArgsR.Value, ctx, valEnv);
    }

    /// <summary>
    /// Non-Resolve lexical-fallback dispatch: resolve the dot edge's STORED
    /// fallback identity (normally <see cref="Expr.Param"/>; an invalid
    /// host-built expression follows its ordinary <c>ResolveAlg</c> behavior)
    /// and call with
    /// the receiver as the ordinary leading argument (dot-call passes a
    /// value). This is pure consumption
    /// of the front-end's Param-vs-Resolve decision — no runtime environment
    /// is probed to reconstruct it. Kept out of
    /// <see cref="CallLexicalWithReceiverCounted"/> so its temporaries never
    /// enlarge that recursive frame (native stack-margin calibration).
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> CallLexicalFallbackCalleeWithReceiverCounted(
        Expr.DotCall dotCall,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var calleeR = ResolveAlg(dotCall.EffectiveLexicalFallback, ctx);
        if (calleeR.IsError) return calleeR.Error;
        return EvalResolvedCallCounted(
            calleeR.Value,
            BuildLexicalReceiverCallArgs(dotCall.Target, dotCall.Args),
            ctx,
            valEnv,
            CallDiagnosticName.FromKnown(dotCall.Name));
    }

    /// <summary>
    /// Check whether a dot call would fall through to a specific lexical
    /// builtin after structural shadowing rules are applied. The elaborated
    /// dot-edge facts are CONSUMED from the node: a non-Resolve
    /// (parameter-bound) fallback never dispatches through the dotted
    /// sequence-builtin view, so fusion must fall back to the generic path
    /// for those edges — no runtime environment is probed.
    /// </summary>
    private static string? GetDotCallLexicalBuiltinFallbackReason(
        Expr.DotCall dotCall,
        BuiltinId expectedBuiltin,
        EvalCtx ctx)
    {
        var name = dotCall.Name;
        if (dotCall.EffectiveLexicalFallback is not Expr.Resolve(var fallbackName))
            return $"{name} is bound as a parameter in the calling context";

        var targetResult = ResolveDotReceiver(dotCall.Target, ctx, out _);
        if (targetResult.IsOk)
        {
            if (LookupPropBinding(targetResult.Value, name, ctx.Budget) is not null)
                return $"{name} is shadowed by a structural property";

            if (targetResult.Value.DefinesConditionalBranchProperty(name))
                return $"{name} is shadowed by a conditional structural property";
        }
        else if (targetResult.Error is not EvalError.NotAnAlgorithm)
        {
            return $"{name} receiver resolution failed";
        }

        var calleeR = ResolveNamedAlgorithm(fallbackName, span: null, ctx);
        if (calleeR.IsError
            || calleeR.Value is not Algorithm.Builtin(var builtin)
            || builtin != expectedBuiltin)
        {
            return $"{name} does not resolve to builtin";
        }

        return null;
    }

    /// <summary>
    /// Resolve a dot edge's RECEIVER in algorithm position — the structural
    /// half of the ordinary DotCall law applied at EVERY level of a chain.
    /// Every receiver shape resolves through canonical <see cref="ResolveAlg"/>
    /// except an argumentless dot edge <c>X.M</c>, which NAVIGATES: when
    /// <c>X</c> (resolved the same way, recursively) is an algorithm that
    /// declares <c>M</c> (any visibility; selection never depends on exposure),
    /// the receiver IS that member algorithm wired to <c>X</c> — so
    /// <c>Lib.Sub.Q</c> reads <c>Sub</c>'s own <c>Q</c> before any lexical
    /// <c>Q(x)</c> is considered, exactly as <c>Lib.Q</c> reads <c>Lib</c>'s.
    /// A member named <c>string</c> is navigated like any member (Q-17 S-C:
    /// <c>Obj.string.Q</c> reads the declared <c>string</c>'s own <c>Q</c>).
    /// A declared <c>M</c> that is inaccessible from the site (a local-only
    /// member outside its owner's activation), or one defined only inside
    /// conditional branches, is the same structural error that evaluating
    /// <c>X.M</c> itself reports — never a fallback. When <c>X</c> does not
    /// declare <c>M</c> (or is not an algorithm at all), the edge is an ordinary
    /// dot RESULT — its lexical fallback's value, or, for <c>string</c>, the
    /// intrinsic's text — and resolves to <see cref="ResolveAlg"/>'s memberless
    /// wrapper, the internal carrier of that VALUE, so the chain continues by
    /// value (<c>3.A.B</c> stays <c>B(A(3))</c>). An argument-bearing edge
    /// is a call, hence a value, and never navigates; a capture receiver keeps
    /// suppressing structural identity (<c>(A, B).V</c> and <c>(A*).V</c> fall
    /// back — a redundant group never reaches the evaluator, so <c>(Obj).V</c>
    /// and <c>(Lib.Sub).Q</c> are simply <c>Obj.V</c> and <c>Lib.Sub.Q</c>:
    /// parentheses group syntax and never change which receiver is navigated).
    /// <para>The resolution is identity navigation only: no intermediate edge
    /// is evaluated, so a parameterized or output-less container navigates
    /// exactly as it does at the first level (<c>F.Q</c> works while <c>F</c>
    /// alone is an arity or missing-output error), and the recursion is bounded
    /// by the structural depth preflight like the dot-chain evaluation it
    /// mirrors. A dot expression's CALLABLE identity is read from this
    /// navigation by <see cref="ProjectDotPathCallable"/> alone.
    /// <paramref name="isStructuralMember"/> reports whether the receiver was
    /// reached by navigation, i.e. is a name-resolved property algorithm rather
    /// than a written value shape (the <c>.string</c> intrinsic uses it to
    /// select the depth-charged value-demand funnel exactly as for a bare
    /// <see cref="Expr.Resolve"/> receiver).</para>
    /// Lean: <c>resolveDotReceiver</c>.
    /// </summary>
    private static EvalResult<Algorithm> ResolveDotReceiver(Expr target, EvalCtx ctx, out bool isStructuralMember)
    {
        isStructuralMember = false;
        if (target is not Expr.DotCall { Args: null } edge)
            return ResolveReceiverHead(target, ctx);

        var receiverResult = ResolveDotReceiver(edge.Target, ctx, out _);
        if (receiverResult.IsError)
        {
            return receiverResult.Error is EvalError.NotAnAlgorithm
                ? ResolveAlg(target, ctx)
                : receiverResult.Error;
        }

        var receiver = receiverResult.Value;
        var member = LookupPropBinding(receiver, edge.Name, ctx.Budget);
        if (member is not null)
        {
            if (!IsAccessibleFrom(member, receiver, ctx))
                return LocalOnlyPropertyError(OpenExprName(edge.Target), member) with { Span = edge.Span };

            isStructuralMember = true;
            return EvalResult<Algorithm>.Ok(ChildOfInContext(receiver, member.Value, ctx));
        }

        if (receiver.DefinesConditionalBranchProperty(edge.Name))
            return new EvalError.LocalOnlyProperty(OpenExprName(edge.Target), edge.Name, PropertyExposure.LocalOnlyConditionalAlgorithm)
            { Span = edge.Span };

        return ResolveAlg(target, ctx);
    }

    /// <summary>
    /// THE ONE CALLABLE PROJECTION of a dot expression (DOT-09; NEED-06 for a supplied
    /// argument, Q-18 C-B3 for a callee): a dot expression carries ONE callable identity in
    /// every algorithm-capable position — supplied, forwarded, callback, loop step and
    /// callee alike. An ARGUMENTLESS path whose every edge selects a DECLARED structural
    /// member (<see cref="ResolveDotReceiver"/>'s navigation, accessibility checked after
    /// selection) is its member's own callable, an alias member normalized to its target
    /// (FWD-02); every other dot expression — an argument-bearing edge (a call), an edge
    /// whose receiver lacks the member (the extension call's or the <c>.string</c>
    /// intrinsic's VALUE), a value receiver — is a calculation value with NO callable
    /// identity (<c>null</c>; the result-value boundary). Identity only: nothing is
    /// evaluated and no VALUE is demanded. A structural failure on the path
    /// (<c>LocalOnlyProperty</c>) is the projection's own error; a receiver that is simply
    /// not an algorithm is no identity. Lean: <c>projectNeedStructuralMember</c> followed by
    /// <c>resolveAliasTarget</c>.
    /// </summary>
    private static EvalResult<Algorithm?> ProjectDotPathCallable(Expr.DotCall edge, EvalCtx ctx)
    {
        if (edge.Args is not null)
            return EvalResult<Algorithm?>.Ok(null);

        var member = ResolveDotReceiver(edge, ctx, out var isStructuralMember);
        if (member.IsError)
            return IsLiftableError(member.Error) ? EvalResult<Algorithm?>.Ok(null) : member.Error;
        if (!isStructuralMember)
            return EvalResult<Algorithm?>.Ok(null);

        var target = member.Value is Algorithm.Alias alias
            ? ResolveAliasTarget(alias, ctx)
            : EvalResult<Algorithm>.Ok(member.Value);
        return target.IsError ? target.Error : EvalResult<Algorithm?>.Ok(target.Value);
    }

    /// <summary>
    /// A zero-argument structural member read's outcome (<c>R.n</c>, DOT-01), a bare missing output
    /// marked as the SELECTED MEMBER's own (<see cref="EvalError.MissingOutput.IsSelectedMemberOutput"/>)
    /// so the renderer names the member reference — <c>Obj.string</c> for a declared member named
    /// <c>string</c> (Q-17 S-C) — never the receiver the <c>.string</c> intrinsic would blame.
    /// Diagnostic-only: kind, payload and equality are unchanged.
    /// </summary>
    private static EvalResult<CountedResult> MarkSelectedMemberOutput(EvalResult<CountedResult> result)
        => result.IsError && result.Error is EvalError.MissingOutput missing
            ? missing with { IsSelectedMemberOutput = true }
            : result;

    /// <summary>
    /// The <c>.string</c> intrinsic is a ZERO-parameter member. A written argument list is
    /// assembled exactly like every call's (each written slot evaluated once, left to
    /// right, spreads opened — <see cref="FormNeedSupply"/>) and then rejected by
    /// arity, the same outcome as <c>Obj.V(1)</c> for a declared zero-parameter member, so a
    /// written bundle is never silently dropped; an EMPTY written list (<c>x.string()</c>)
    /// stays the intrinsic, as <c>A()</c> stays a call of <c>A</c>. Returns <c>null</c> when
    /// the intrinsic may proceed. Lean: <c>rejectDotStringIntrinsicArguments</c>.
    /// </summary>
    private static EvalError? RejectDotStringIntrinsicArguments(
        OutputBundle? argsOpt,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (argsOpt is null)
            return null;

        var inputsR = FormNeedSupply(argsOpt, ctx, valEnv, asynchronous: false).GetAwaiter().GetResult();
        if (inputsR.IsError)
            return inputsR.Error;

        return inputsR.Value.Count == 0 ? null : new EvalError.ArityMismatch(0, inputsR.Value.Count);
    }

    /// <summary>
    /// Counted dotCall evaluation — the CANONICAL owner of dot-call dispatch
    /// (<see cref="EvalDotCall"/> is its value projection).
    /// The ROUTE is decided first, member-first at every edge (DOT-01; Q-17 S-C):
    /// 0. Receiver resolution through <see cref="ResolveDotReceiver"/>: a
    ///    chained receiver navigates its declared structural members (each
    ///    selected member then checked for accessibility), so the
    ///    property-first rule below holds at every level of <c>A.B.C.D</c>
    /// 1. ONE structural lookup of the member on the resolved receiver — a member
    ///    named <c>string</c> included:
    ///    - selected → accessibility checked AFTER selection (K1-08), an alias
    ///      member read or called as its target;
    ///    - No args → the zero-argument value demand (a 0-param member is a
    ///      cached value access; a parameterized one the arity rejection);
    ///    - Has args → delegate to <see cref="EvalResolvedCallCounted"/>
    ///      (dual-view binding, no receiver injection)
    /// 2. A member declared only in conditional branches → <c>LocalOnlyProperty</c>
    ///    (an error, never a miss route).
    /// 3. A STRUCTURAL MISS takes the edge's miss route:
    ///    - spelled <c>string</c> → the number-to-text intrinsic (DOT-08): the
    ///      receiver's VALUE converted; a lexical <c>string</c> is never consulted;
    ///    - otherwise → extension fallback (<see cref="CallLexicalWithReceiverCounted"/>):
    ///      DOT-CALL PASSES A VALUE — <c>a.f(args)</c> is exactly the call
    ///      <c>f(a, args)</c>, the receiver being the ordinary first argument slot
    ///      (never a supply of its own; only the spread receiver <c>a*.f</c>, lowered
    ///      by the parser to <c>f(a*)</c>, opens a boundary).
    ///    Dot resolution therefore has three classes — structural member access (1),
    ///    the intrinsic <c>.string</c> and extension fallback (3) — and only the
    ///    extension call injects the receiver.
    /// When receiver resolution returns notAnAlgorithm (a value receiver, e.g. a numeric
    /// literal), there is no member to select: the miss route applies directly.
    /// (The graced sources <c>a~.f</c> / <c>a.~f</c> arrive here as the SAME
    /// node as <c>a.f</c>: Grace is a front-end parameter-order annotation that
    /// elaboration consumes, so this method — and every diagnostic it produces
    /// — cannot tell the sources apart.)
    /// Lean: <c>evalDotCallCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalDotCallCounted(
        Expr.DotCall dotCall,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (TryEvaluateSequencePipeline(
            SequencePipelineInvocation.DotCall(dotCall),
            ctx,
            valEnv,
            out var sequencePipelineR))
            return sequencePipelineR;

        var target = dotCall.Target;
        var name = dotCall.Name;
        var argsOpt = dotCall.Args;

        var targetResult = ResolveDotReceiver(target, ctx, out var receiverIsStructuralMember);
        if (targetResult.IsError)
        {
            if (targetResult.Error is EvalError.NotAnAlgorithm)
            {
                // A value receiver declares no member: the edge's miss route applies directly.
                if (dotCall.UsesOrdinaryDotStringIntrinsic())
                {
                    if (RejectDotStringIntrinsicArguments(argsOpt, ctx, valEnv) is { } arityRejection)
                        return arityRejection;
                    var val = Eval(target, ctx, valEnv);
                    if (val.IsError) return val.Error;
                    var outR = ResultToString(ctx, val.Value);
                    if (outR.IsError) return outR.Error;
                    return EvalResult<CountedResult>.Ok(new CountedResult(outR.Value, outR.Value.ValueCount()));
                }
                return CallLexicalWithReceiverCounted(dotCall, ctx, valEnv);
            }

            return targetResult.Error;
        }

        var targetAlg = targetResult.Value;

        // ONE structural lookup decides the route, whatever the member's spelling: a declared
        // member wins (a member named `string` included — Q-17 S-C), then a branch-only member
        // is the local-only error, and only a structural MISS takes the miss route below.
        var prop = LookupPropBinding(targetAlg, name, ctx.Budget);
        if (prop is not null)
        {
            // Selection is by declaration (structural access ignores `public`); the
            // member's accessibility from THIS site is decided afterwards.
            if (!IsAccessibleFrom(prop, targetAlg, ctx))
                return LocalOnlyPropertyError(OpenExprName(target), prop);

            var wired = ChildOfInContext(targetAlg, prop.Value, ctx);
            if (wired is Algorithm.Alias)
                return EvalAliasMemberCounted(targetAlg, prop, wired, argsOpt, name, ctx, valEnv);
            if (argsOpt is null)
            {
                // A structurally navigated member read with NO argument list is an
                // ordinary zero-argument value demand, so the ONE law decides
                // (AcceptsZeroArgumentValueDemand) and the rejection names the member's
                // true minimum supply, never its flattened declared capture count.
                var simpleCallee = TryGetFlatBinderUserEquivalent(wired);
                if (simpleCallee is not null)
                {
                    return AcceptsZeroArgumentValueDemand(simpleCallee)
                        ? MarkSelectedMemberOutput(ReCountValueBoundary(EvalZeroArgPropertyAccessCounted(targetAlg, prop, ZeroArgPropertyAccessKind.CountedStructural, simpleCallee, ctx, valEnv)))
                        : ZeroArgumentDemandArityMismatch(simpleCallee);
                }

                if (AcceptsZeroArgumentValueDemand(wired))
                    return MarkSelectedMemberOutput(ReCountValueBoundary(EvalZeroArgPropertyAccessCounted(targetAlg, prop, ZeroArgPropertyAccessKind.CountedStructural, wired, ctx, valEnv)));

                if (wired is Algorithm.Conditional)
                    return new EvalError.NoMatchingBranch(name);

                return ZeroArgumentDemandArityMismatch(wired);
            }

            return EvalResolvedCallCounted(
                wired,
                argsOpt,
                ctx,
                valEnv,
                CallDiagnosticName.FromKnown(name));
        }

        if (targetAlg.DefinesConditionalBranchProperty(name))
            return new EvalError.LocalOnlyProperty(OpenExprName(target), name, PropertyExposure.LocalOnlyConditionalAlgorithm);

        // A structural miss: `string` is the number-to-text intrinsic (DOT-08) — it takes the
        // extension call's place, so a lexical `string` is never consulted — and every other
        // member is the extension call `name(target, args)` (DOT-03).
        if (dotCall.UsesOrdinaryDotStringIntrinsic())
        {
            if (RejectDotStringIntrinsicArguments(argsOpt, ctx, valEnv) is { } arityRejection)
                return arityRejection;
            if (targetAlg is Algorithm.Alias)
                return EvalAliasDotStringCounted(target, targetAlg, receiverIsStructuralMember, ctx, valEnv);
            var val = EvalDotStringReceiverAlgOutput(target, targetAlg, receiverIsStructuralMember, ctx, valEnv);
            if (val.IsError) return val.Error;
            var outR = ResultToString(ctx, val.Value);
            if (outR.IsError) return outR.Error;
            return EvalResult<CountedResult>.Ok(new CountedResult(outR.Value, outR.Value.ValueCount()));
        }

        return CallLexicalWithReceiverCounted(dotCall, ctx, valEnv);
    }

    /// <summary>
    /// Counted extension-call fallback — the ONE receiver-injection
    /// implementation (the plain dot-call spelling reaches it through
    /// <see cref="EvalDotCallCounted"/> and the value projection).
    /// DOT-CALL PASSES A VALUE (September 2026): <c>R.F(args)</c> resolves the
    /// callee and dispatches exactly <c>F(R, args)</c> — the receiver
    /// expression becomes the ordinary FIRST written argument slot of the ONE
    /// shared call assembly (<see cref="BuildLexicalReceiverCallArgs"/> +
    /// <see cref="EvalResolvedCallCounted"/>), so every callable shape
    /// (builtin, flat, collecting, patterned, clause family) binds, demands,
    /// caches, orders, charges, and rejects the receiver exactly as it would
    /// that written argument: a builtin's <c>collection</c> slot demands a
    /// named receiver through the zero-argument value-demand law like
    /// <c>count(A)</c> does, <c>while</c>/<c>repeat</c> take the receiver as
    /// their step algorithm, a collecting parameter collects the receiver as
    /// one item (<c>(1, 2).Coll</c> is <c>[(1, 2)]</c>, <c>().Coll</c> is
    /// <c>[()]</c>), and only a spread receiver — the fluent <c>R*.F</c> form,
    /// which the parser lowers to <c>F(R*)</c> — opens a boundary. There is no
    /// dotted receiver view, no raw receiver supply, and no builtin-specific
    /// receiver placement.
    /// Lean: <c>callLexicalWithReceiverCounted</c> (the Lean plain path is the
    /// projection <c>evalDotCall</c>, so only the counted helper exists).
    /// </summary>
    private static EvalResult<CountedResult> CallLexicalWithReceiverCounted(
        Expr.DotCall dotCall,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // The STORED lexical-fallback identity decides the callee channel —
        // the front-end's Param-vs-Resolve decision is CONSUMED here, never
        // reconstructed from runtime environments. A Param fallback (or any
        // non-Resolve host-built expression) resolves through canonical
        // ResolveAlg out of line, so a parameter shadows a same-name builtin
        // exactly as in plain-call position; the dispatch stays out of line so
        // its temporaries never enlarge this recursive dot-chain frame
        // (native stack-margin calibration; see the near-boundary dot-call
        // chain pin in AstStructuralDepthProcessTests).
        if (dotCall.EffectiveLexicalFallback is not Expr.Resolve(var fallbackName))
            return CallLexicalFallbackCalleeWithReceiverCounted(dotCall, ctx, valEnv);

        var calleeR = ResolveNamedAlgorithm(fallbackName, span: null, ctx);
        if (calleeR.IsError) return calleeR.Error;
        return EvalResolvedCallCounted(
            calleeR.Value,
            BuildLexicalReceiverCallArgs(dotCall.Target, dotCall.Args),
            ctx,
            valEnv,
            CallDiagnosticName.FromKnown(fallbackName));
    }
}
