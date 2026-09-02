using System.Collections;
using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using KatLang.Runtime;

namespace KatLang;

/// <summary>
/// Dot-call evaluation: sequence-builtin dot receivers, sequence-pipeline recognition, lexical receiver injection, and structural-first dot-call dispatch (the "DotCall evaluation" section).
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
        IReadOnlyList<(string, Result)> valEnv)
        => ProjectCountedValue(EvalDotCallCounted(dotCall, ctx, valEnv));

    private readonly record struct SequenceBuiltinDotCall(
        BuiltinId Builtin,
        IReadOnlyList<ResolvedArgumentAlgorithm> Args);

    /// <summary>
    /// Sequence builtins in dot-call form evaluate the receiver to ONE value,
    /// re-counted to <c>Result.ValueCount</c>, and pass it as the ordinary
    /// fixed <c>collection</c> argument (the post-binding collection view
    /// opens it, exactly as for the plain call form).
    /// A direct inline receiver block first exposes its inner algorithm output
    /// count, which strips exactly one receiver-scoping block layer for forms
    /// like <c>(1, 2, 3).take(2)</c> while still keeping
    /// <c>((1, 2, 3)).take(2)</c> and named sequence-valued helpers intact.
    /// Any extra dot-call arguments still follow the plain-call argument path.
    /// This keeps plain-call boundary preservation unchanged while making
    /// <c>receiver.builtin(...)</c> operate on the same top-level collection
    /// that <c>receiver:i</c> and higher-order callback projection observe.
    /// </summary>
    private static EvalResult<CountedResult> EvalSequenceBuiltinDotReceiverCounted(
        Expr receiver,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // The receiver is this builtin call's collection ARGUMENT, so it consumes
        // one depth-only argument-evaluation level exactly like the plain-call
        // spelling's argument funnel (EvalArgumentAlgOutputCounted). This keeps the
        // plain/dot work observations identical — including PeakDepth — and bounds
        // a self-referential receiver (`A = A.count`) by the same deterministic
        // depth limit instead of the machine-dependent stack backstop.
        if (ctx.Budget.TryEnterArgumentEvaluation() is { } limitError)
            return limitError;
        try
        {
            var valueR = Eval(receiver, ctx, valEnv);
            return valueR.IsError
                ? valueR.Error
                : EvalResult<CountedResult>.Ok(new CountedResult(valueR.Value, valueR.Value.ValueCount()));
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    private static EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>> SequenceBuiltinDotReceiverArgs(
        Expr receiver,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var receiverR = EvalSequenceBuiltinDotReceiverCounted(receiver, ctx, valEnv);
        if (receiverR.IsError) return receiverR.Error;

        // The receiver has just been evaluated — exactly once — to dispatch on it. Carry
        // that counted result forward as the argument's PREPARED value only: the value
        // channel reads it directly and must never reconstruct or re-evaluate it. No
        // algorithm channel is built here — reifying the result as an expression tree
        // (CountedArgAlgorithm → ResultToExpr) costs O(receiver size), and the ordinary
        // value path (`A.count`, `A.take(2)`, `A.map(F)`) never consumes it because
        // PreparedValue short-circuits evaluation. If an algorithm-only consumer does
        // request the channel, ResolveArgumentAlgorithm / PrepareSequenceBuiltinSuffixArg
        // synthesize the legacy counted-value wrapper lazily at that point.
        return EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>>.Ok(
            [new ResolvedArgumentAlgorithm(Algorithm: null, SpreadsSequence: false)
            {
                PreparedValue = receiverR.Value,
            }]);
    }

    private static EvalResult<SequenceBuiltinDotCall?> TryBuildSequenceBuiltinDotCall(
        string name,
        Expr receiver,
        OutputBundle? extraArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var calleeR = ResolveNamedAlgorithm(name, span: null, ctx);
        if (calleeR.IsError
            || calleeR.Value is not Algorithm.Builtin(var builtin)
            || GetSequenceBuiltinMetadata(builtin) is null)
        {
            return EvalResult<SequenceBuiltinDotCall?>.Ok(null);
        }

        var receiverArgAlgsR = SequenceBuiltinDotReceiverArgs(receiver, ctx, valEnv);
        if (receiverArgAlgsR.IsError) return receiverArgAlgsR.Error;

        var argAlgs = new List<ResolvedArgumentAlgorithm>(receiverArgAlgsR.Value);

        if (extraArgs is not null)
        {
            var extraArgAlgsR = ResolveArgAlgsWithSequenceSpread(extraArgs, ctx, valEnv);
            if (extraArgAlgsR.IsError) return extraArgAlgsR.Error;
            if (builtin == BuiltinId.@reduce
                && extraArgAlgsR.Value is [{ Algorithm: { Params.Count: > 0 } reducerAlgorithm }])
            {
                return ReduceInitialAccumulatorRequiresValueError(reducerAlgorithm);
            }

            argAlgs.AddRange(extraArgAlgsR.Value);
        }

        return EvalResult<SequenceBuiltinDotCall?>.Ok(
            new SequenceBuiltinDotCall(builtin, argAlgs));
    }

    /// <summary>
    /// Assemble the argument bundle for ordinary lexical dot-call fallback:
    /// <c>receiver.F(C, D)</c> calls <c>F</c> with the ORIGINAL receiver
    /// expression as one injected leading segment followed by the written
    /// extra arguments. Assembly is independent of the resolved callee: the
    /// receiver is never pre-expanded, never unwrapped, and no parameter
    /// shape is inspected. The paired
    /// <see cref="CallArgumentAssembly.InjectedDotReceiverLeading"/> marker
    /// makes the receiver one segment for allocation whose evaluated
    /// top-level supply only a flat top-level collecting parameter consumes.
    /// Lean: <c>prepareLexicalDotCallArgs</c>.
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
        IReadOnlyList<(string, Result)> valEnv,
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
        IReadOnlyList<(string, Result)> valEnv,
        SequencePipelineDiagnostics? diagnostics,
        out EvalResult<CountedResult> result)
    {
        ctx.Observations?.RecordSequencePipelineServiceConstruction();
        var services = new SequencePipelineEvaluationServices(
            GetDotCallLexicalBuiltinFallbackReason: (stageDotCall, expectedBuiltin) =>
                GetDotCallLexicalBuiltinFallbackReason(stageDotCall, expectedBuiltin, ctx),
            EvaluateDotReceiverIterationItems: receiver => EvaluateDotReceiverIterationItemsForSequenceOptimizer(receiver, ctx, valEnv),
            ResolveArgumentAlgorithms: args => ResolveArgAlgs(args, ctx, valEnv),
            ResolveAlgorithm: expr => ResolveAlg(expr, ctx),
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
    /// Semantic dot-receiver item collection shared with the sequence optimizer;
    /// this preserves the generic dot-call sequence builtin boundary rules.
    /// </summary>
    private static EvalResult<IReadOnlyList<CountedResult>> EvaluateDotReceiverIterationItemsForSequenceOptimizer(
        Expr receiver,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var receiverR = EvalSequenceBuiltinDotReceiverCounted(receiver, ctx, valEnv);
        if (receiverR.IsError)
            return receiverR.Error;

        // Mirror the generic builtin collection binding: the receiver value is
        // the bound collection, so exactly one outer sequence OR list boundary
        // is opened by the shared builtin collection-item view; any other value
        // supplies itself as one item.
        var items = BuiltinCollectionItems(receiverR.Value.Value);

        return EvalResult<IReadOnlyList<CountedResult>>.Ok(
            items
                .Select(static item => new CountedResult(item, item.ValueCount()))
                .ToList());
    }

    /// <summary>
    /// Evaluate already-recognized builtin <c>range(...)</c> arguments for the
    /// sequence optimizer while preserving the generic range call diagnostics.
    /// </summary>
    private static EvalResult<InclusiveRange> EvaluateRangeCallArgumentsForSequenceOptimizer(
        Expr function,
        OutputBundle args,
        SourceSpan? callSpan,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // Depth parity with the generic strategy: the fused pipeline consumes this
        // `range(...)` call as the FILTER's collection argument, which the generic
        // spelling evaluates inside one depth-only argument-evaluation level
        // (EvalSequenceBuiltinDotReceiverCounted for the dotted form, the builtin
        // argument funnel for the plain one). The generic-source adapter
        // (EvaluateDotReceiverIterationItemsForSequenceOptimizer) already charges its
        // equivalent level; charging it here too keeps every fused source shape on the
        // same dynamic depth as the generic path, so a `MaxDepth` verdict cannot depend
        // on which strategy an unrelated configured budget selected. The outer
        // collection-argument level is charged once by
        // SequencePipelineOptimizer.TryExecuteRecognized.
        if (ctx.Budget.TryEnterArgumentEvaluation() is { } depthError)
            return AtSpanIfMissing(depthError, callSpan);

        try
        {
            var rangeR = WithSpan(
                callSpan,
                WithCallCtx(
                    CallDiagnosticName.FromExpression(function),
                    ctx,
                    EvalBuiltinRangeCallArguments(args, ctx, valEnv)));
            if (rangeR.IsError)
                return rangeR;

            // Optimizer/generic boundary parity: a fused pipeline evaluates the range's
            // bounds and then iterates them WITHOUT materializing the list, so it must still
            // reject exactly the sizes the generic `range` builtin rejects. The check
            // consumes no cumulative budget precisely because nothing is materialized here —
            // and if the pipeline is not fused after all, the generic path reserves for real,
            // so the same range is never charged twice.
            return ctx.Budget.CheckCollectionSize(CountInclusiveRangeValues(rangeR.Value)) is { } limitError
                ? AtSpanIfMissing(limitError, callSpan)
                : rangeR;
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    private static EvalResult<InclusiveRange> EvalBuiltinRangeCallArguments(
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
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
    /// the receiver as one injected leading segment. This is pure consumption
    /// of the front-end's Param-vs-Resolve decision — no runtime environment
    /// is probed to reconstruct it. Kept out of
    /// <see cref="CallLexicalWithReceiverCounted"/> so its temporaries never
    /// enlarge that recursive frame (native stack-margin calibration).
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> CallLexicalFallbackCalleeWithReceiverCounted(
        Expr.DotCall dotCall,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var calleeR = ResolveAlg(dotCall.EffectiveLexicalFallback, ctx);
        if (calleeR.IsError) return calleeR.Error;
        return EvalResolvedCallCounted(
            calleeR.Value,
            BuildLexicalReceiverCallArgs(dotCall.Target, dotCall.Args),
            ctx,
            valEnv,
            CallDiagnosticName.FromKnown(dotCall.Name),
            CallArgumentAssembly.InjectedDotReceiverLeading);
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

        var targetResult = ResolveAlg(dotCall.Target, ctx);
        if (targetResult.IsOk)
        {
            if (LookupPropBinding(targetResult.Value, name) is not null)
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
    /// Counted dotCall evaluation — the CANONICAL owner of dot-call dispatch
    /// (<see cref="EvalDotCall"/> is its value projection).
    /// Smart dispatch:
    /// 1. Value-based intrinsic (string) → evaluate target, convert numeric result to string
    /// 2. Structural property found (navigation-only):
    ///    - No args + 0-param → value access
    ///    - No args + has params → arity mismatch error
    ///    - Has args → delegate to <see cref="EvalResolvedCallCounted"/>
    ///      (dual-view binding, no receiver injection)
    /// 3. No property → lexical fallback (receiver injection via
    ///    <see cref="CallLexicalWithReceiverCounted"/>)
    /// When resolveAlg returns notAnAlgorithm (e.g. numeric literal target),
    /// value-based intrinsics are checked before lexical fallback.
    /// (The graced sources <c>a~.f</c> / <c>a.~f</c> arrive here as the SAME
    /// node as <c>a.f</c>: Grace is a front-end parameter-order annotation that
    /// elaboration consumes, so this method — and every diagnostic it produces
    /// — cannot tell the sources apart.)
    /// Lean: <c>evalDotCallCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalDotCallCounted(
        Expr.DotCall dotCall,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
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

        var targetResult = ResolveAlg(target, ctx);
        if (targetResult.IsError)
        {
            if (targetResult.Error is EvalError.NotAnAlgorithm)
            {
                if (dotCall.UsesOrdinaryDotStringIntrinsic())
                {
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

        if (dotCall.UsesOrdinaryDotStringIntrinsic())
        {
            var val = EvalDotStringReceiverAlgOutput(target, targetAlg, ctx, valEnv);
            if (val.IsError) return val.Error;
            var outR = ResultToString(ctx, val.Value);
            if (outR.IsError) return outR.Error;
            return EvalResult<CountedResult>.Ok(new CountedResult(outR.Value, outR.Value.ValueCount()));
        }

        var prop = LookupPropBinding(targetAlg, name);
        if (prop is not null)
        {
            if (!IsExported(prop))
                return new EvalError.LocalOnlyProperty(OpenExprName(target), name, prop.Exposure);

            var wired = ChildOf(targetAlg, prop.Value);
            if (argsOpt is null)
            {
                var simpleCallee = TryGetFlatBinderUserEquivalent(wired);
                if (simpleCallee is not null)
                    return new EvalError.ArityMismatch(simpleCallee.Params.Count, 0);

                if (wired is Algorithm.Conditional)
                    return new EvalError.NoMatchingBranch(name);

                if (wired.Params.Count == 0)
                    return ReCountValueBoundary(EvalZeroArgPropertyAccessCounted(targetAlg, prop, ZeroArgPropertyAccessKind.CountedStructural, wired, ctx, valEnv));
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

        return CallLexicalWithReceiverCounted(dotCall, ctx, valEnv);
    }

    /// <summary>
    /// Counted lexical fallback with receiver injection — the ONE lexical
    /// receiver-injection implementation (the plain dot-call spelling reaches
    /// it through <see cref="EvalDotCallCounted"/> and the value projection).
    /// The injected receiver remains one argument expression for flat fixed
    /// user calls; sequence builtin dot-call expansion is handled before the
    /// resolved-call path. DotCall lexical fallback to <c>while</c> and
    /// <c>repeat</c> keeps explicit init arguments intact; the loop builtin
    /// turns each init argument into one initial state slot after structural
    /// property lookup has had priority.
    /// Lean: <c>callLexicalWithReceiverCounted</c> (the Lean plain path is the
    /// projection <c>evalDotCall</c>, so only the counted helper exists).
    /// </summary>
    private static EvalResult<CountedResult> CallLexicalWithReceiverCounted(
        Expr.DotCall dotCall,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
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

        var sequenceDotCallR = TryBuildSequenceBuiltinDotCall(fallbackName, dotCall.Target, dotCall.Args, ctx, valEnv);
        if (sequenceDotCallR.IsError) return sequenceDotCallR.Error;
        if (sequenceDotCallR.Value is { } sequenceDotCall)
            return ApplyBuiltinCountedResolved(sequenceDotCall.Builtin, sequenceDotCall.Args, ctx, valEnv);

        var calleeR = ResolveNamedAlgorithm(fallbackName, span: null, ctx);
        if (calleeR.IsError) return calleeR.Error;
        var combinedArgs = BuildLexicalReceiverCallArgs(dotCall.Target, dotCall.Args);
        return EvalResolvedCallCounted(
            calleeR.Value,
            combinedArgs,
            ctx,
            valEnv,
            CallDiagnosticName.FromKnown(fallbackName),
            CallArgumentAssembly.InjectedDotReceiverLeading);
    }
}
