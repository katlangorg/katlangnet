using System.Runtime.CompilerServices;
using KatLang.Evaluation.Caching;

namespace KatLang;

/// <summary>
/// CALLABLE ALIASES (FWD-02, binding indirection; decided October 1 2026). An
/// <see cref="Algorithm.Alias"/> is a BINDING whose callable is the one its written target
/// resolves to in the alias's OWN scope. The evaluator keeps the two identities apart:
/// <list type="bullet">
///   <item>the BINDING is the alias's own — a property read <c>A</c> is keyed by the alias's own
///   property in the zero-argument cache (<see cref="ResolvedLexicalProperty.Binding"/>), and written
///   member access <c>A.K</c> navigates the alias's own declarations (<see cref="ResolveDotReceiver"/>
///   resolves a written receiver RAW);</item>
///   <item>the CALLABLE is the target's — every place a binding becomes a callable normalizes the
///   alias to its target (<see cref="ResolveAliasTarget"/>): lexical lookup
///   (<see cref="LookupLexical"/>), a structurally navigated member, an inline block, and a top-level
///   property read. Calls, callbacks and loop steps, the callable channel of an argument, value
///   demands, builtin adapters, clause dispatch and Math and host wrappers therefore all receive the
///   target itself, and an alias is never an invocation: it charges no step and no depth.</item>
/// </list>
/// Every alias branch lives OUT OF LINE (no alias local in a calibrated recursive frame): the
/// recursive dispatch frames only test the variant and delegate here.
/// </summary>
public static partial class Evaluator
{
    /// <summary>
    /// THE ONE NORMALIZATION: <c>ResolveCallable(A) = A is an alias ? ResolveCallable(target of A,
    /// resolved in A's own scope) : A</c>. Iterative — an alias chain never grows the host stack — and
    /// each step resolves the alias's written target exactly where the alias's body would be
    /// evaluated (the alias pushed as the head): a name by the ownership-first lexical lookup, a dotted
    /// path by structural receiver navigation, so a member reached is the declared member and a target
    /// that is itself an alias continues the chase.
    /// <para>NORMALIZED ONCE: every alias BINDING the chase passes through — <paramref name="binding"/>
    /// itself and each named link — remembers the final target under its <see cref="AliasTargetKey"/>,
    /// so a chain is chased once per declaring scope (and activation), and a later normalization of
    /// any of its links is one lookup. Only a successful chase is remembered.</para>
    /// <para>A step reaching an alias declaration the chase has already visited IN THE SAME RESOLVING
    /// SCOPE is an alias CYCLE, which only a host-built tree can form (the front end never does, and
    /// the pre-evaluation gate rejects every static one): <see cref="EvalError.IllegalInEval"/>, never
    /// a hop limit and never a stack overflow. (A declaration shared by two scopes of a host DAG may
    /// legitimately be reached twice, once per scope.)</para>
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<Algorithm> ResolveAliasTarget(Algorithm.Alias alias, EvalCtx ctx, Property? binding = null)
    {
        List<(Dictionary<AliasTargetKey, Algorithm> Memo, AliasTargetKey Key)>? pending = null;
        if (binding is not null && ReadAliasTargetMemo(binding, alias, ctx, ref pending) is { } known)
            return EvalResult<Algorithm>.Ok(known);

        Algorithm current = alias;
        HashSet<(DeclarationIdentity? Declaration, Evaluation.Caching.StructuralOwnerIdentity Scope)>? visited = null;
        while (current is Algorithm.Alias step)
        {
            if (!(visited ??= []).Add((step.Declaration, Evaluation.Caching.StructuralOwnerIdentity.FromScope(step.Parent))))
                return AliasCycleError(step);

            var next = ResolveAliasStep(step, ctx, out var nextBinding);
            if (next.IsError)
                return next.Error;
            current = next.Value;
            if (current is Algorithm.Alias nextAlias
                && nextBinding is not null
                && ReadAliasTargetMemo(nextBinding, nextAlias, ctx, ref pending) is { } memoized)
            {
                current = memoized;
                break;
            }
        }

        if (pending is not null)
        {
            foreach (var (memo, key) in pending)
                memo[key] = current;
        }

        return EvalResult<Algorithm>.Ok(current);
    }

    /// <summary>
    /// The remembered target of the alias BINDING <paramref name="binding"/> wired as
    /// <paramref name="wired"/>, or null after queueing its key for the chase's result. The entry
    /// lives on the nearest activation of the declaring scope chain (so it is forgotten with that
    /// call), or run-wide when the chain has none.
    /// </summary>
    private static Algorithm? ReadAliasTargetMemo(
        Property binding,
        Algorithm.Alias wired,
        EvalCtx ctx,
        ref List<(Dictionary<AliasTargetKey, Algorithm> Memo, AliasTargetKey Key)>? pending)
    {
        var memo = ctx.Budget.AliasTargets;
        for (var level = wired.Parent; level is not null; level = level.Parent)
        {
            if (level.Activation is { } activation)
            {
                memo = activation.AliasTargets;
                break;
            }
        }

        var key = new AliasTargetKey(binding, Evaluation.Caching.StructuralOwnerIdentity.FromScope(wired.Parent));
        if (memo.TryGetValue(key, out var target))
            return target;
        (pending ??= []).Add((memo, key));
        return null;
    }

    /// <summary>
    /// The memo key of an alias BINDING: the binding itself (by reference) and the resolving identity
    /// of the scope chain it is wired under (each level's opens and properties, by reference) —
    /// everything its target's resolution reads besides the activation, which selects the memo the
    /// key lives in. A <see cref="Property"/> is a record, so the binding compares by reference here.
    /// </summary>
    internal readonly struct AliasTargetKey(Property binding, Evaluation.Caching.StructuralOwnerIdentity scope) : IEquatable<AliasTargetKey>
    {
        private readonly Property _binding = binding;
        private readonly Evaluation.Caching.StructuralOwnerIdentity _scope = scope;

        public bool Equals(AliasTargetKey other)
            => ReferenceEquals(_binding, other._binding) && _scope.Equals(other._scope);

        public override bool Equals(object? obj) => obj is AliasTargetKey other && Equals(other);

        public override int GetHashCode()
            => HashCode.Combine(RuntimeHelpers.GetHashCode(_binding), _scope.GetHashCode());
    }

    /// <summary>
    /// One step of <see cref="ResolveAliasTarget"/>: the callable the alias's written target names in
    /// its own scope, and the binding that selected it, including a declared member path.
    /// </summary>
    private static EvalResult<Algorithm> ResolveAliasStep(Algorithm.Alias step, EvalCtx ctx, out Property? binding)
    {
        binding = null;
        var stepCtx = ctx.Push(step);
        switch (step.Target)
        {
            case Expr.Resolve(var name):
            {
                var resolved = LookupLexicalRaw(step, name, stepCtx);
                if (resolved.IsError)
                    return AtSpanIfMissing(resolved.Error, step.Target.Span);
                binding = resolved.Value.Binding;
                return EvalResult<Algorithm>.Ok(resolved.Value.ResolvedAlgorithm);
            }

            case Expr.DotCall { Args: null } edge:
            {
                // A declared member path, a member named `string` included (Q-17 S-C): an edge whose
                // receiver lacks the member is a computed value, never an alias target.
                var member = ResolveDotReceiver(edge, stepCtx, out var isStructuralMember);
                if (member.IsError)
                    return AtSpanIfMissing(member.Error, step.Target.Span);
                if (isStructuralMember && member.Value is Algorithm.Alias { Parent: { } owner })
                    binding = owner.Properties.FirstOrDefault(property => property.Name == edge.Name);
                return isStructuralMember ? member : NotAStaticAliasTarget(step);
            }

            default:
                return NotAStaticAliasTarget(step);
        }
    }

    private static EvalError AliasCycleError(Algorithm.Alias step)
        => new EvalError.IllegalInEval(AliasCycleMessage) { Span = step.Target.Span };

    private static EvalError NotAStaticAliasTarget(Algorithm.Alias step)
        => new EvalError.IllegalInEval(AliasTargetNotStaticPathMessage(step.Target)) { Span = step.Target.Span };

    /// <summary>Lean: <c>aliasCycleMessage</c>.</summary>
    internal const string AliasCycleMessage
        = "callable alias cycle: an alias target leads back to an alias already on its chain";

    /// <summary>Lean: <c>aliasTargetNotStaticPathMessage</c>.</summary>
    internal static string AliasTargetNotStaticPathMessage(Expr target)
        => $"callable alias target {ExprNameRenderer.Render(target, ExprNameMode.Open)} is not a name or a declared member path";

    /// <summary>
    /// The normalized callable of an alias BINDING wired as <paramref name="wired"/>: remembered under
    /// the binding's <see cref="AliasTargetKey"/> (see <see cref="ResolveAliasTarget"/>), so a binding
    /// read again in an equivalent scope reuses the resolved chain instead of chasing it again. Only a
    /// resolved callable is remembered; a failure is resolved (and reported) afresh.
    /// </summary>
    private static EvalResult<Algorithm> ResolveBindingAliasTarget(Property binding, Algorithm.Alias wired, EvalCtx ctx)
        => ResolveAliasTarget(wired, ctx, binding);

    /// <summary>
    /// A lexical lookup that selected an alias binding: the BINDING stays the alias's own property
    /// (the zero-argument cache key, exposure, accessibility), the resolved algorithm becomes the
    /// alias's callable target.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<ResolvedLexicalProperty> NormalizeAliasBinding(ResolvedLexicalProperty resolved, EvalCtx ctx)
    {
        var target = ResolveBindingAliasTarget(resolved.Binding, (Algorithm.Alias)resolved.ResolvedAlgorithm, ctx);
        return target.IsError
            ? target.Error
            : EvalResult<ResolvedLexicalProperty>.Ok(resolved with { ResolvedAlgorithm = target.Value });
    }

    /// <summary>An inline block that is an alias (<c>{ F }</c>), wired to the caller and normalized (no binding, so not memoized).</summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<Algorithm> ResolveInlineAliasTarget(Algorithm alias, EvalCtx ctx)
        => ResolveAliasTarget((Algorithm.Alias)WireToCaller(ctx, alias), ctx);

    /// <summary>
    /// An inline block alias in VALUE position: exactly the value demand of its target — the ONE
    /// zero-argument law judged on the TARGET and reported as its written target reference reports
    /// it (<see cref="ZeroArgumentValueDemandError"/>: <c>{ Inc }</c> with <c>Inc(x)</c> is Inc's
    /// own <see cref="EvalError.ArityMismatch"/>, never the written block's
    /// <see cref="EvalError.UnresolvedImplicitParams"/>; FA-OQ-1, Option B), then the target's
    /// zero-supply demand. An inline block is no property, so nothing is cached. The counterpart
    /// of <see cref="EvalAlgorithmExprValue"/>.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<Result> EvalInlineAliasValue(Expr expr, Algorithm alias, EvalCtx ctx, ValEnv valEnv)
    {
        var targetR = ResolveInlineAliasTarget(alias, ctx);
        if (targetR.IsError)
            return AtSpanIfMissing(targetR.Error, expr.Span);

        var target = targetR.Value;
        if (ZeroArgumentValueDemandError(expr, target) is { } rejection)
            return rejection;
        return WithSpan(expr.Span, EvalZeroArgumentDemandOutput(target, ctx, valEnv));
    }

    /// <summary>
    /// An inline block alias as a SPREAD operand (<c>{ F }*</c>): the same value demand as
    /// <see cref="EvalInlineAliasValue"/> — the ONE zero-argument law judged on the TARGET and
    /// reported as its written target reference reports it — whose items are spread; an operand
    /// without output is the spread-specific <see cref="EvalError.SpreadMissingOutput"/>. The
    /// counterpart of the block arm of <see cref="EvalSequenceSpreadOperandItems"/>.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<IReadOnlyList<Result>> EvalAliasSpreadOperandItems(Expr expr, Algorithm alias, EvalCtx ctx, ValEnv valEnv)
    {
        var targetR = ResolveInlineAliasTarget(alias, ctx);
        if (targetR.IsError)
            return AtSpanIfMissing(targetR.Error, expr.Span);

        var target = targetR.Value;
        if (ZeroArgumentValueDemandError(expr, target) is { } rejection)
            return rejection;

        var blockR = EvalZeroArgumentDemandOutput(target, ctx, valEnv);
        if (blockR.IsError)
            return IsMissingOutputError(blockR.Error) ? SpreadMissingOutput(expr.Span) : blockR.Error;
        return EvalResult<IReadOnlyList<Result>>.Ok(blockR.Value.SpreadItems());
    }

    /// <summary>
    /// The dispatch safety net: a call whose callee reached dispatch as an unnormalized alias (a
    /// host-built tree) calls the alias's target with the same written arguments in the caller's
    /// context. Every binding lookup normalizes first, so front-end programs never reach this.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalAliasCallCounted(
        Algorithm callee,
        OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        var target = ResolveAliasTarget((Algorithm.Alias)callee, ctx);
        return target.IsError ? target.Error : EvalResolvedCallCounted(target.Value, args, ctx, valEnv, calleeName);
    }

    /// <summary>The callback counterpart of <see cref="EvalAliasCallCounted"/>: normalized BEFORE the callback's invocation charge, so an alias charges nothing.</summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalAliasCallbackCallCounted(
        Algorithm callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        ValEnv valEnv,
        string calleeName)
    {
        var target = ResolveAliasTarget((Algorithm.Alias)callee, ctx);
        return target.IsError ? target.Error : EvalResolvedCallbackCallCounted(target.Value, args, ctx, valEnv, calleeName);
    }

    /// <summary>The demand funnel's alias arm: an alias demanded with zero arguments is its target's zero-supply demand.</summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalAliasZeroArgumentDemandCounted(Algorithm algorithm, EvalCtx ctx, ValEnv valEnv)
    {
        var target = ResolveAliasTarget((Algorithm.Alias)algorithm, ctx);
        return target.IsError ? target.Error : EvalZeroArgumentDemandOutputCounted(target.Value, ctx, valEnv);
    }

    /// <summary>
    /// A top-level property read of an alias binding (<see cref="EvalTopLevelZeroArgPropertyCounted"/>):
    /// the binding's normalized target, the binding itself unchanged.
    /// </summary>
    private static EvalResult<Algorithm> NormalizeTopLevelBinding(Property binding, Algorithm resolvedAlgorithm, EvalCtx ctx)
        => resolvedAlgorithm is Algorithm.Alias alias
            ? ResolveBindingAliasTarget(binding, alias, ctx)
            : EvalResult<Algorithm>.Ok(resolvedAlgorithm);

    /// <summary>
    /// The structurally navigated member arm of <see cref="EvalDotCallCounted"/> for a member that is an
    /// alias (<c>Lib.A</c>, <c>Lib.A(args)</c>): the member's BINDING keys the zero-argument read, its
    /// normalized target is read or called — the same steps as the member arm, over the target.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalAliasMemberCounted(
        Algorithm targetAlg,
        Property prop,
        Algorithm wiredAlias,
        OutputBundle? argsOpt,
        string name,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var wiredR = ResolveBindingAliasTarget(prop, (Algorithm.Alias)wiredAlias, ctx);
        if (wiredR.IsError)
            return wiredR.Error;

        var wired = wiredR.Value;
        if (argsOpt is null)
        {
            // MIRROR OF the member arm of EvalDotCallCounted (zero-argument read), over the target.
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

        return EvalResolvedCallCounted(wired, argsOpt, ctx, valEnv, CallDiagnosticName.FromKnown(name));
    }

    /// <summary>
    /// The <c>.string</c> intrinsic on a receiver that resolved to an alias binding (<c>A.string</c>,
    /// <c>Lib.A.string</c>): the receiver is a VALUE demand, judged on the alias's target and read
    /// through the alias's own binding — the same steps as the intrinsic arm of
    /// <see cref="EvalDotCallCounted"/>.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalAliasDotStringCounted(
        Expr target,
        Algorithm aliasAlg,
        bool receiverIsStructuralMember,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var receiverR = ResolveAliasTarget((Algorithm.Alias)aliasAlg, ctx);
        if (receiverR.IsError)
            return receiverR.Error;
        var val = EvalDotStringReceiverAlgOutput(target, receiverR.Value, receiverIsStructuralMember, ctx, valEnv);
        if (val.IsError) return val.Error;
        var outR = ResultToString(ctx, val.Value);
        if (outR.IsError) return outR.Error;
        return EvalResult<CountedResult>.Ok(new CountedResult(outR.Value, outR.Value.ValueCount()));
    }

    /// <summary>
    /// A written RECEIVER head (<see cref="ResolveDotReceiver"/>): a receiver is NAVIGATED, so a name or a
    /// block is the binding's own algorithm — an alias declares only its own members, never its
    /// target's (written member access never follows an alias). Every other receiver shape resolves
    /// through <see cref="ResolveAlg"/> as before.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<Algorithm> ResolveReceiverHead(Expr target, EvalCtx ctx)
        => target switch
        {
            Expr.Resolve(var name) => ctx.CallStack.Count == 0
                ? new EvalError.UnknownName(name) { Span = target.Span }
                : ProjectRawLookup(LookupLexicalRaw(ctx.CallStack[0], name, ctx), target.Span),
            Expr.AlgorithmExpr(var block) => EvalResult<Algorithm>.Ok(WireToCaller(ctx, block)),
            _ => ResolveAlg(target, ctx),
        };

    private static EvalResult<Algorithm> ProjectRawLookup(EvalResult<ResolvedLexicalProperty> resolved, SourceSpan? span)
        => resolved.IsError
            ? (resolved.Error.Span is null ? resolved.Error with { Span = span } : resolved.Error)
            : EvalResult<Algorithm>.Ok(resolved.Value.ResolvedAlgorithm);

    // ── Async twins (normalization itself is synchronous lookup work; only what follows awaits) ──

    /// <summary>MIRROR OF <see cref="EvalInlineAliasValue"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> EvalInlineAliasValueAsync(Expr expr, Algorithm alias, EvalCtx ctx, ValEnv valEnv)
    {
        var targetR = ResolveInlineAliasTarget(alias, ctx);
        if (targetR.IsError)
            return AtSpanIfMissing(targetR.Error, expr.Span);

        var target = targetR.Value;
        if (ZeroArgumentValueDemandError(expr, target) is { } rejection)
            return rejection;
        return WithSpan(expr.Span, await EvalZeroArgumentDemandOutputAsync(target, ctx, valEnv).ConfigureAwait(false));
    }

    /// <summary>MIRROR OF <see cref="EvalAliasSpreadOperandItems"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<IReadOnlyList<Result>>> EvalAliasSpreadOperandItemsAsync(Expr expr, Algorithm alias, EvalCtx ctx, ValEnv valEnv)
    {
        var targetR = ResolveInlineAliasTarget(alias, ctx);
        if (targetR.IsError)
            return AtSpanIfMissing(targetR.Error, expr.Span);

        var target = targetR.Value;
        if (ZeroArgumentValueDemandError(expr, target) is { } rejection)
            return rejection;

        var blockR = await EvalZeroArgumentDemandOutputAsync(target, ctx, valEnv).ConfigureAwait(false);
        if (blockR.IsError)
            return IsMissingOutputError(blockR.Error) ? SpreadMissingOutput(expr.Span) : blockR.Error;
        return EvalResult<IReadOnlyList<Result>>.Ok(blockR.Value.SpreadItems());
    }

    /// <summary>MIRROR OF <see cref="EvalAliasCallCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalAliasCallCountedAsync(
        Algorithm callee,
        OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        var target = ResolveAliasTarget((Algorithm.Alias)callee, ctx);
        return target.IsError
            ? target.Error
            : await EvalResolvedCallCountedAsync(target.Value, args, ctx, valEnv, calleeName).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalAliasCallbackCallCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalAliasCallbackCallCountedAsync(
        Algorithm callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        ValEnv valEnv,
        string calleeName)
    {
        var target = ResolveAliasTarget((Algorithm.Alias)callee, ctx);
        return target.IsError
            ? target.Error
            : await EvalResolvedCallbackCallCountedAsync(target.Value, args, ctx, valEnv, calleeName).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalAliasZeroArgumentDemandCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalAliasZeroArgumentDemandCountedAsync(Algorithm algorithm, EvalCtx ctx, ValEnv valEnv)
    {
        var target = ResolveAliasTarget((Algorithm.Alias)algorithm, ctx);
        return target.IsError
            ? target.Error
            : await EvalZeroArgumentDemandOutputCountedAsync(target.Value, ctx, valEnv).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalAliasMemberCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalAliasMemberCountedAsync(
        Algorithm targetAlg,
        Property prop,
        Algorithm wiredAlias,
        OutputBundle? argsOpt,
        string name,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var wiredR = ResolveBindingAliasTarget(prop, (Algorithm.Alias)wiredAlias, ctx);
        if (wiredR.IsError)
            return wiredR.Error;

        var wired = wiredR.Value;
        if (argsOpt is null)
        {
            var simpleCallee = TryGetFlatBinderUserEquivalent(wired);
            if (simpleCallee is not null)
            {
                return AcceptsZeroArgumentValueDemand(simpleCallee)
                    ? MarkSelectedMemberOutput(ReCountValueBoundary(
                        await EvalZeroArgPropertyAccessCountedAsync(
                            targetAlg, prop, ZeroArgPropertyAccessKind.CountedStructural, simpleCallee, ctx, valEnv).ConfigureAwait(false)))
                    : ZeroArgumentDemandArityMismatch(simpleCallee);
            }

            if (AcceptsZeroArgumentValueDemand(wired))
                return MarkSelectedMemberOutput(ReCountValueBoundary(
                    await EvalZeroArgPropertyAccessCountedAsync(
                        targetAlg, prop, ZeroArgPropertyAccessKind.CountedStructural, wired, ctx, valEnv).ConfigureAwait(false)));

            if (wired is Algorithm.Conditional)
                return new EvalError.NoMatchingBranch(name);

            return ZeroArgumentDemandArityMismatch(wired);
        }

        return await EvalResolvedCallCountedAsync(wired, argsOpt, ctx, valEnv, CallDiagnosticName.FromKnown(name)).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalAliasDotStringCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalAliasDotStringCountedAsync(
        Expr target,
        Algorithm aliasAlg,
        bool receiverIsStructuralMember,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var receiverR = ResolveAliasTarget((Algorithm.Alias)aliasAlg, ctx);
        if (receiverR.IsError)
            return receiverR.Error;
        var val = await EvalDotStringReceiverAlgOutputAsync(target, receiverR.Value, receiverIsStructuralMember, ctx, valEnv).ConfigureAwait(false);
        if (val.IsError) return val.Error;
        var outR = ResultToString(ctx, val.Value);
        if (outR.IsError) return outR.Error;
        return EvalResult<CountedResult>.Ok(new CountedResult(outR.Value, outR.Value.ValueCount()));
    }
}
