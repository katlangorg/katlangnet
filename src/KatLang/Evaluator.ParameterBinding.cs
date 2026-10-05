using System.Collections;
using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang;

/// <summary>
/// Parameter binding: call-argument assembly, flat/collecting/patterned parameter binding, deconstruction binding, and loop-step binding preparation (the "Bind parameters" section).
/// Part of the <see cref="Evaluator"/> partial class; the central state, lookup and open resolution,
/// the built-in prelude, and the run entry points remain in <c>Evaluator.cs</c>.
/// </summary>
public static partial class Evaluator
{
    // ── Bind parameters ─────────────────────────────────────────────────────

    private readonly record struct VariadicCallItem(
        Result? Value,
        Algorithm? Algorithm,
        EvalError? ValueError,
        CountedResult? PreparedValue = null,
        Expr? Source = null,
        Algorithm? Callable = null,
        NeedCell? Cell = null)
    {
        /// <summary>
        /// The algorithm this item NAMES (<see cref="ResolvedArgumentAlgorithm.InvokedAlgorithm"/>):
        /// the identity the zero-argument value-demand law judges, while a VALUE demand
        /// evaluates the value-side <see cref="Algorithm"/>. Lean: <c>CallableCallItem.named?</c>.
        /// </summary>
        public Algorithm? NamedAlgorithm => Callable ?? Algorithm;
    }

    internal readonly record struct ResolvedArgumentAlgorithm(
        Algorithm? Algorithm,
        bool SpreadsSequence)
    {
        internal NeedCell? Cell { get; init; }
        /// <summary>
        /// An argument that NAMES a binding resolves to its value side (<see cref="Algorithm"/>,
        /// a wrapper that performs the ordinary value read of the written name) and keeps the
        /// named algorithm here: a parameter bound on BOTH channels (the wrapper reads the bound
        /// value, so a VALUE slot never re-runs the argument's body), and a lexical property
        /// reference <c>A</c> (the wrapper is the ordinary property read — the zero-argument
        /// property access with its run cache — so a VALUE slot never re-runs the property's
        /// body: how a property value is consumed does not affect caching). A slot that
        /// INVOKES its argument — a sequence callback or a loop step — calls
        /// <see cref="InvokedAlgorithm"/>, so <c>Apply(f, xs) = map(xs, f)</c> applies the
        /// callable <c>f</c> exactly as <c>map(xs, Cnt)</c> does even when <c>Cnt</c> also
        /// satisfies a zero-argument value demand. <c>null</c> for every other argument,
        /// whose <see cref="Algorithm"/> already is its algorithm-channel identity.
        /// Lean: <c>ResolvedArgumentAlgorithm.callable?</c>.
        /// </summary>
        public Algorithm? Callable { get; init; }

        /// <summary>
        /// The algorithm this argument NAMES: the callable an ALGORITHM slot (a sequence
        /// callback or a loop step) invokes, and the identity the zero-argument value-demand
        /// law and every signature classification judge — the named binding's algorithm when
        /// it has one, otherwise the resolved algorithm. VALUE slots demand
        /// <see cref="Algorithm"/>. Lean: <c>ResolvedArgumentAlgorithm.invoked</c>.
        /// </summary>
        public Algorithm? InvokedAlgorithm => Callable ?? Algorithm;

        /// <summary>
        /// The already-computed value of this argument, when the caller evaluated it before
        /// assembling the call. Used for dotted receivers and builtin callback arguments,
        /// both of which have already been evaluated before builtin binding begins.
        ///
        /// <para><see cref="Algorithm"/> retains a source-backed algorithm channel when one
        /// exists. Callback data values and dotted sequence-builtin receivers leave that
        /// channel null so their structure is not eagerly rebuilt as an AST; an
        /// algorithm-only consumer can recreate the legacy channel lazily from this counted
        /// value. The value channel always uses this field directly and never re-evaluates
        /// a reconstructed literal.</para>
        /// </summary>
        public CountedResult? PreparedValue { get; init; }

        /// <summary>
        /// The written argument expression <see cref="Algorithm"/> was resolved from
        /// (<see cref="ResolveArgAlgsWithSequenceSpread"/>): the demand-site identity the
        /// zero-argument value-demand law (<see cref="ZeroArgumentValueDemandError"/>)
        /// reports through — its span, and whether the algorithm was named as a property,
        /// a parameter, a dot receiver, or a written block — when a builtin VALUE slot
        /// demands the algorithm with zero arguments. <c>null</c> for value-reified
        /// arguments (prepared callback data, expanded spread items, dotted receivers),
        /// whose algorithms carry no parameters. Diagnostic identity only: it never
        /// changes which algorithm a slot resolves to. Lean: <c>source?</c>.
        /// </summary>
        public Expr? Source { get; init; }
    }

    private readonly record struct GenericLoopStepBindingContract(
        IReadOnlyList<ParameterDeclaration> Parameters,
        IReadOnlyList<ParameterPattern> ParameterPatterns,
        IReadOnlyList<string> ParameterNames);

    private static CallableBindingPlan? TryCreateUserLoopStepBindingPlan(Algorithm step)
    {
        if (step is not Algorithm.User userStep)
            return null;

        try
        {
            var signature = CallableSignature.FromUserAlgorithm("loop step", userStep);
            return CallableBindingPlan.FromSignature(signature);
        }
        catch (InvalidOperationException)
        {
            return null;
        }
    }

    private static bool IsOptimizedLoopShapeEligible(
        Algorithm step,
        out string? fallbackReason)
    {
        var plan = TryCreateUserLoopStepBindingPlan(step);
        if (plan is null)
        {
            fallbackReason = null;
            return true;
        }

        if (plan.RequiresPatternedBinding || plan.HasTopLevelCollecting)
        {
            fallbackReason = "variadic loop step";
            return false;
        }

        fallbackReason = null;
        return true;
    }

    /// <summary>
    /// The loop-invariant part of generic loop-step execution, prepared ONCE per loop
    /// invocation and reused by every iteration (M16). Everything here depends only on
    /// the step algorithm and the loop's own context — never on iteration state — so
    /// per-iteration recomputation was pure waste: the snapshot of the step's parameter
    /// patterns, their need-pattern view, and the shadowed environments would refilter
    /// the same invariant inputs every iteration.
    /// Iteration-varying work (state binding, the fresh counted-environment
    /// concatenation whose list identity is a zero-arg-cache key component, and step
    /// output evaluation) stays in <see cref="RunStepSlots"/>.
    /// Nothing prepared here is consulted when the step's rows form the next state: the
    /// parameter patterns BIND the incoming state only, and the next state is the step's
    /// row supply (<see cref="EvalAlgOutputSlots"/>) whatever the pattern category
    /// (LOOP-03; Q-24 retired the former pattern-triggered packing of a spread row).
    /// </summary>
    private readonly record struct PreparedGenericLoopStep(
        GenericLoopStepBindingContract BindingContract,
        IReadOnlyList<NeedPattern> NeedPatterns,
        AlgEnv ShadowedAlgEnv,
        CountedParamEnv ShadowedCountedParamEnv);

    /// <summary>
    /// Freezes the temporary algorithm-shaped view used to derive the step's binding
    /// contract. Public
    /// host-built AST records may retain caller-owned <see cref="IReadOnlyList{T}"/>
    /// instances, so reading the original user algorithm again after a callback could
    /// mix a prepared binding for the old shape with parameter lists mutated to a new
    /// shape. The returned copy is used only while preparation derives the narrow
    /// <see cref="GenericLoopStepBindingContract"/> and its need patterns; it is not stored
    /// in the prepared object. Executable body, scope, properties, and opens remain on
    /// <paramref name="step"/> and are evaluated normally every iteration.
    /// </summary>
    private static Algorithm SnapshotGenericLoopStepBindingContract(Algorithm step)
    {
        if (step is not Algorithm.User user)
            return step;

        // The ONE parameter channel is snapshotted; Parameters and Params derive from it, so the
        // prepared view cannot observe a host mutation of the original pattern lists.
        return user with { ParameterPatterns = SnapshotParameterPatterns(user.ParameterPatterns) };
    }

    /// <summary>
    /// Iterative, DAG-preserving snapshot of recursive pattern-list membership. Capture
    /// records are immutable and can be shared; structural nodes (sequence and list
    /// patterns) are rebuilt with their kind so a host cannot mutate a retained nested
    /// <c>Items</c> list during the loop.
    /// Structural preflight has already rejected cycles before evaluation reaches this
    /// helper.
    /// </summary>
    private static IReadOnlyList<ParameterPattern> SnapshotParameterPatterns(
        IReadOnlyList<ParameterPattern> source)
    {
        if (source.Count == 0)
            return [];

        var snapshots = new Dictionary<ParameterPattern, ParameterPattern>(
            ReferenceEqualityComparer.Instance);
        var states = new Dictionary<ParameterPattern, byte>(
            ReferenceEqualityComparer.Instance);
        var stack = new Stack<(ParameterPattern Group, bool Expanded)>();

        foreach (var pattern in source)
        {
            if (ParameterPattern.StructuralItems(pattern) is null || snapshots.ContainsKey(pattern))
                continue;

            stack.Push((pattern, Expanded: false));
            while (stack.Count != 0)
            {
                var (group, expanded) = stack.Pop();
                if (snapshots.ContainsKey(group))
                    continue;

                if (!expanded)
                {
                    if (states.TryGetValue(group, out var state) && state == 1)
                        throw new InvalidOperationException("Cyclic parameter pattern reached loop preparation after structural preflight.");

                    states[group] = 1;
                    stack.Push((group, Expanded: true));
                    var groupItems = ParameterPattern.StructuralItems(group)!;
                    for (var index = groupItems.Count - 1; index >= 0; index--)
                    {
                        var child = groupItems[index];
                        if (ParameterPattern.StructuralItems(child) is not null
                            && !snapshots.ContainsKey(child))
                        {
                            stack.Push((child, Expanded: false));
                        }
                    }

                    continue;
                }

                var sourceItems = ParameterPattern.StructuralItems(group)!;
                var items = new ParameterPattern[sourceItems.Count];
                for (var index = 0; index < sourceItems.Count; index++)
                {
                    var item = sourceItems[index];
                    items[index] = ParameterPattern.StructuralItems(item) is not null
                        ? snapshots[item]
                        : item;
                }

                snapshots[group] = ParameterPattern.WithStructuralItems(group, items);
                states[group] = 2;
            }
        }

        var result = new ParameterPattern[source.Count];
        for (var index = 0; index < source.Count; index++)
        {
            var pattern = source[index];
            result[index] = ParameterPattern.StructuralItems(pattern) is not null
                ? snapshots[pattern]
                : pattern;
        }

        return result;
    }

    /// <summary>
    /// Prepares the invariant generic loop-step state. Non-evaluating and infallible:
    /// it charges no budget, observes no cancellation, resolves no names, and invokes
    /// no callbacks, so both the synchronous generic loops and their async twins share
    /// this ONE implementation (the M7/M10 twin rule: share non-evaluating
    /// preparation, mirror evaluating work). Callers prepare only when the loop will
    /// run at least one iteration — a zero-iteration loop must not gain preparation
    /// work it never had.
    /// </summary>
    private static PreparedGenericLoopStep PrepareGenericLoopStep(Algorithm step, EvalCtx ctx)
    {
        ctx.Observations?.RecordGenericLoopStepBindingPreparation();
        var bindingContract = SnapshotGenericLoopStepBindingContract(step);
        var parameterNames = bindingContract.Params.ToArray();
        // Both inherited tiers are shadowed once per loop invocation through the
        // shared callee-context helper; RunStepSlots prepends the per-iteration
        // counted bindings on top of the prepared counted tier.
        var inherited = ShadowInheritedParameterEnvironments(ctx, parameterNames);
        return new PreparedGenericLoopStep(
            new GenericLoopStepBindingContract(
                bindingContract.Parameters,
                bindingContract.ParameterPatterns,
                parameterNames),
            NeedParameterPatterns(bindingContract.ParameterPatterns),
            inherited.AlgEnv,
            inherited.CountedParamEnv);
    }

    private static EvalResult<IReadOnlyList<Result>> EvalExplicitSequenceValueItems(
        Algorithm alg,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (alg is Algorithm.Builtin(var builtin))
        {
            var countedR = EvalBuiltinValueCounted(builtin);
            return countedR.IsError
                ? countedR.Error
                : EvalResult<IReadOnlyList<Result>>.Ok(CountedTopLevelValues(countedR.Value));
        }

        if (alg.FindDuplicatePropName() is { } duplicateName)
            return new EvalError.DuplicateProperty(duplicateName);

        if (ConditionalValueAccessError("conditional", alg) is { } conditionalError)
            return conditionalError;

        if (alg is Algorithm.User { Output.Count: 0 })
            return new EvalError.MissingOutput();

        return EvalExplicitSequenceValueRowSlots(alg.Output, EnterAlgorithmBody(alg, ctx, valEnv), valEnv);
    }

    /// <summary>
    /// The shared written-slot loop over ordered bundle rows: each row
    /// contributes its explicit written slots. Algorithm-shaped groupings reach
    /// it after pushing their own scope; a <see cref="Expr.Capture"/> body
    /// reaches it directly (captures own no scope).
    ///
    /// <para>Carries the structural-nesting stack backstop (mirrored verbatim by the
    /// async twin <see cref="EvalExplicitSequenceValueRowSlotsAsync"/>; rationale on
    /// <see cref="EvalOutputRowsPreparedCore"/>): nested written groups recurse through
    /// this family without touching the ordinary dispatch or any invocation
    /// chokepoint, so the probe fires once per nesting level here too.</para>
    /// </summary>
    private static EvalResult<IReadOnlyList<Result>> EvalExplicitSequenceValueRowSlots(
        IReadOnlyList<Expr> rows,
        EvalCtx rowCtx,
        ValEnv valEnv)
    {
        if (!RuntimeHelpers.TryEnsureSufficientExecutionStack())
            return new EvalError.EvaluationStackExhausted();

        var slots = new List<Result>();
        foreach (var expr in rows)
        {
            var exprSlotsR = EvalExplicitSequenceValueExprSlots(expr, rowCtx, valEnv);
            if (exprSlotsR.IsError) return exprSlotsR.Error;
            slots.AddRange(exprSlotsR.Value);
        }

        return EvalResult<IReadOnlyList<Result>>.Ok(slots);
    }

    private static EvalResult<IReadOnlyList<Result>> EvalExplicitSequenceValueExprSlots(
        Expr expr,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // A nested capture element (a multi-slot group `((1, 2), 3)`, a lone
        // spread group `(A*)`, or a host-built single-row capture — the parser
        // writes `(A)` as `A`) materializes exactly one element, combined with
        // the same shallow singleton-erasing rule as ordinary capture
        // evaluation (CombineOutputSlots): a lone row IS its already-evaluated
        // value and an all-spread-empty group is `()` — never a
        // literal-unwritable orphan such as `(5)`. This is the same value
        // EvalCounted produces for the node, unfolded one level so nested
        // groups recurse through this family (see the stack backstop note on
        // EvalExplicitSequenceValueRowSlots); a zero-parameter scoped block
        // element unfolds through its algorithm the same way.
        // Both unfolding arms POSITION their failure at the written slot with the very
        // rule EvalCounted applies to the same node, because they are the only two arms
        // that bypass it: every other slot kind falls through to EvalCounted below and is
        // positioned there. Without this a written block element reported its missing
        // output with NO span at all (`[1, { }, 3]`), while the same element inside a
        // parenthesized group — which reaches EvalCounted's own Capture arm — was located
        // exactly. AtSpanIfMissing keeps a span the inner failure already carries, so a
        // nested slot still reports at its own precise location.
        if (expr is Expr.Capture(var captureBody))
        {
            var nestedItemsR = WithPreferredSpanOf(
                expr, captureBody, EvalExplicitSequenceValueRowSlots(captureBody, ctx, valEnv));
            if (nestedItemsR.IsError) return nestedItemsR.Error;

            return EvalResult<IReadOnlyList<Result>>.Ok([CombineOutputSlots(nestedItemsR.Value)]);
        }

        if (expr is Expr.AlgorithmExpr(var algorithm))
        {
            var wired = WireToCaller(ctx, algorithm);
            // Only the plain-output arm may bypass the demand funnel. Zero captures
            // do not imply zero supplied slots, and a family must dispatch its branch.
            if (!RequiresZeroArgumentSupplyBinding(wired))
            {
                // The block span rule is EvalAlgorithmExprValue's: the written block, else
                // its first positioned output row.
                var nestedItemsR = WithPreferredSpanOf(
                    expr, wired.Output, EvalExplicitSequenceValueItems(wired, ctx, valEnv));
                if (nestedItemsR.IsError) return nestedItemsR.Error;

                return EvalResult<IReadOnlyList<Result>>.Ok([CombineOutputSlots(nestedItemsR.Value)]);
            }
        }

        var countedR = EvalCounted(expr, ctx, valEnv);
        if (countedR.IsError) return countedR.Error;

        // WRITTEN-SLOT REIFICATION: a non-spread expression occupying one
        // written slot contributes exactly ONE persistent value — the value its
        // counted supply denotes — regardless of how many items the expression
        // emitted (zero, one, or many; a counted-multi supply such as a loop
        // result is already represented by one structural value). Only an
        // explicit spread supplies the value's items into the surrounding item slots.
        return expr is Expr.SequenceSpread
            ? EvalResult<IReadOnlyList<Result>>.Ok(CountedTopLevelValues(countedR.Value))
            : EvalResult<IReadOnlyList<Result>>.Ok([countedR.Value.Value]);
    }

    /// <summary>
    /// An ordinary structural pattern that received a value of another kind — a sequence
    /// pattern given a list or a scalar, a list pattern given a sequence or a scalar — fails
    /// its binding with this <see cref="EvalError.TypeMismatch"/>, naming the written pattern
    /// and the value received. A right-kind value with the wrong number of elements is the
    /// group's ordinary arity mismatch instead (<see cref="StructuralPatternArityMismatch"/>).
    /// A clause family never raises it: there a mismatch only rejects the clause.
    /// Lean: <c>structuralPatternKindMismatch</c>.
    /// </summary>
    private static EvalError StructuralPatternKindMismatch(ParameterPattern pattern, Result value)
        => new EvalError.TypeMismatch(pattern is ListValueParameterPattern
            ? $"list pattern `{pattern.DisplayName}` expects a list value, but received {DescribeOperand(value)}"
            : $"sequence pattern `{pattern.DisplayName}` expects a sequence value, but received {DescribeOperand(value)}");

    /// <summary>
    /// Arity mismatch produced by binding one nested structural pattern's OWN items — a
    /// right-kind value with the wrong number of elements. The structured payload keeps the
    /// innermost Lean-aligned <see cref="EvalError.ArityMismatch"/> unchanged; the added
    /// context only attributes the failure to the written pattern (e.g. <c>(b, c)</c> or
    /// <c>[b, c]</c>) instead of the enclosing call's argument count: a sequence pattern
    /// through <see cref="SequenceValueParameterBindingContext"/>, a list pattern through
    /// <see cref="ListValueParameterBindingContext"/>. Genuine top-level call-arity mismatches
    /// and argument evaluation errors passing through the binder are never wrapped.
    /// </summary>
    private static EvalError StructuralPatternArityMismatch(
        ParameterPattern group,
        int required,
        int actual)
    {
        var items = ParameterPattern.StructuralItems(group)
            ?? throw new InvalidOperationException("Only a structural pattern has its own items to bind.");
        var hasCollecting = items.Any(static item => item is CaptureParameterPattern { Kind: ParameterKind.Collecting });
        ErrorContext context = group is ListValueParameterPattern
            ? new ListValueParameterBindingContext(group.DisplayName, hasCollecting)
            : new SequenceValueParameterBindingContext(group.DisplayName, hasCollecting);
        return new EvalError.WithContext(context, new EvalError.ArityMismatch(required, actual));
    }

    /// <summary>
    /// The context of NEED-04's value verdict: the occurrences of one repeated parameter
    /// name received unequal VALUE contributions (the binder's <c>BadArity</c>, unchanged by
    /// Q-27). Lean: <c>bindNeedPatterns</c>.
    /// </summary>
    private static string RepeatedParameterContext(string name)
        => $"repeated parameter '{name}' requires equal arguments";

    /// <summary>
    /// One bound range of a pattern level: its first-occurrence binding set, the per-pattern
    /// contributions the cross merges read (for a range of more than one pattern), and whether
    /// some name repeated inside it — a repeat the range may have left to the cross merges
    /// because the level binds the name on the other side of the collector too.
    /// </summary>
    private static bool SameRepeatedCallableIdentity(Algorithm left, Algorithm right)
    {
        if (ReferenceEquals(left, right))
            return true;
        if (left is Algorithm.Builtin leftBuiltin)
            return right is Algorithm.Builtin rightBuiltin && leftBuiltin.Id == rightBuiltin.Id;
        return ReferenceEquals(left.Declaration, right.Declaration)
            && IsSameDeclaringScope(left.Parent, right.Parent)
            && CompatibleActivations(left.Parent, right.Parent)
            && CompatibleActivations(right.Parent, left.Parent);
    }

    /// <summary>
    /// The names one slice of a pattern level binds at any depth (Lean
    /// <c>ParameterPattern.anyBindsName</c>), plus an extra name (the collector's) — indexed
    /// lazily, only when a repeated name actually has to be decided.
    /// </summary>
    private static EvalResult<Result>? TryProjectSharedDeconstructionTarget(
        Algorithm.User helper,
        AssignmentDeconstructionTarget target,
        OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        var execution = new DeconstructionBindingExecution(target.Group, DeconstructionOwnerIdentity(ctx),
            ctx.NeedEnv.Count == 0 ? ValueEnvironmentCacheIdentity(valEnv) : ctx.NeedEnv, ctx.AlgEnv, ctx.CountedParamEnv);
        var sharedR = ctx.DeconstructionBindingCache.GetOrBind(execution,
            () => BindNeedDeconstruction(helper, args, ctx, valEnv, asynchronous: false).GetAwaiter().GetResult());
        if (sharedR.IsError) return sharedR.Error;
        if ((uint)target.Index >= (uint)sharedR.Value.Count) return null;
        return ProjectCountedValue(sharedR.Value[target.Index].Demand());
    }



    /// <summary>
    /// Builtin collection-item view of the bound collection argument: opens
    /// exactly one outer sequence or exact-list boundary to its immediate
    /// items; any other value supplies itself as one item (a scalar is a
    /// one-element collection). Never recursive — nested sequence values and
    /// nested list values stay intact as single items.
    /// Applied strictly AFTER ordinary fixed parameter binding, to the already
    /// bound <c>collection</c> parameter only — argument boundaries are never
    /// altered before binding. Shared by generic collection-builtin binding
    /// and by the sequence-pipeline optimizer's receiver mirror so both open
    /// collections identically.
    /// Lean: <c>builtinCollectionItems</c>.
    /// </summary>
    private static IReadOnlyList<Result> BuiltinCollectionItems(Result value)
        => value is Result.ListValue(var listItems) ? listItems : value.ToItems();



    /// <summary>
    /// RESOURCE LIMITS ARE TERMINAL FOR THE RUN (Q-02 / PV-06, September 2026) — the ONE
    /// decision of every evaluation site that could otherwise DEFER a failure it actually
    /// encountered instead of raising it. Such a site may defer an ORDINARY failure under
    /// its own rule: user-call argument assembly records it beside the slot's algorithm
    /// channel as the parameter's value outcome (<see cref="FormNeedSupply"/>,
    /// <see cref="NeedCell"/>), and the builtin argument adapter retains a value
    /// or surplus item's failure behind the arity verdict until binding demands the slot
    /// (<see cref="BuildCallableCallItems"/>; the fused filter-count pipeline shares that
    /// adapter). A resource-limit failure (<see cref="EvalError.IsResourceLimit"/>) is
    /// never deferrable: the limit is a property of the RUN, not a latent value of one slot,
    /// so the site returns it at once and nothing after it runs — no later argument, callee
    /// body, consumer, random draw, or host operation. An unused parameter, a retained
    /// algorithm channel, a deferred value demand, forwarding, or consumer choice therefore
    /// cannot absorb it. (Before this rule a limit reached inside an argument the callee
    /// never read was retained and dropped, so the run SUCCEEDED after partial evaluation,
    /// with random draws and host effects shifted by where the limit struck: a lower limit
    /// changed one successful value into another, and the value depended on the route and
    /// the host stack.) A resource limit may stop a run; it never redefines the value of a
    /// run that succeeds. Laziness is untouched: an argument the language does not evaluate
    /// — an unselected <c>if</c> branch, an invoking callback slot — reaches no limit.
    /// No Lean counterpart: Lean models no resource limits.
    /// </summary>
    internal static bool IsDeferrableEvaluationFailure(EvalError failure) => !failure.IsResourceLimit;


}
