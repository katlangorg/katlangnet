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

    /// <summary>Lean: bindParams → EvalM ValEnv. Errors with ArityMismatch.</summary>
    private static EvalResult<ValEnv> BindParams(
        IReadOnlyList<string> paramNames,
        IReadOnlyList<Result> values)
    {
        if (paramNames.Count != values.Count)
            return new EvalError.ArityMismatch(paramNames.Count, values.Count);

        var result = new List<(string Name, Result Value)>(paramNames.Count);
        for (var i = 0; i < paramNames.Count; i++)
            result.Add((paramNames[i], values[i]));
        return EvalResult<ValEnv>.Ok(result);
    }

    private readonly record struct VariadicCallItem(
        Result? Value,
        Algorithm? Algorithm,
        EvalError? ValueError,
        CountedResult? PreparedValue = null,
        Expr? Source = null,
        Algorithm? Callable = null);

    internal readonly record struct ResolvedArgumentAlgorithm(
        Algorithm? Algorithm,
        bool SpreadsSequence)
    {
        /// <summary>
        /// A parameter argument bound on BOTH channels resolves to its value side
        /// (<see cref="Algorithm"/>, a wrapper that reads the bound value, so a VALUE slot
        /// never re-runs the argument's body) and keeps its ALGORITHM-channel binding here.
        /// A slot that INVOKES its argument — a sequence callback or a loop step — calls
        /// <see cref="InvokedAlgorithm"/>, so <c>Apply(f, xs) = map(xs, f)</c> applies the
        /// callable <c>f</c> exactly as <c>map(xs, Cnt)</c> does even when <c>Cnt</c> also
        /// satisfies a zero-argument value demand. <c>null</c> for every other argument,
        /// whose <see cref="Algorithm"/> already is its algorithm-channel identity.
        /// Lean: <c>ResolvedArgumentAlgorithm.callable?</c>.
        /// </summary>
        public Algorithm? Callable { get; init; }

        /// <summary>
        /// The algorithm an ALGORITHM slot (a sequence callback or a loop step) invokes:
        /// the parameter's algorithm-channel binding when it has one, otherwise the resolved
        /// algorithm. VALUE slots read <see cref="Algorithm"/>. Lean:
        /// <c>ResolvedArgumentAlgorithm.invoked</c>.
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

    private readonly record struct UserCallBindings(
        ValEnv ValueBindings,
        CountedParamEnv CountedBindings,
        AlgEnv AlgorithmBindings);

    private readonly record struct CountedParameterPatternBindings(
        CountedParamEnv CountedBindings);

    private readonly record struct FlatFixedCallSlot(
        Result? Value,
        Algorithm? Algorithm,
        EvalError? ValueError);

    /// <summary>
    /// A bound user call's callee-side environments: the context carrying the
    /// algorithm and counted tiers, and the value environment. Produced by every
    /// user-call binding shape (flat fixed, patterned, item supply).
    /// </summary>
    private readonly record struct UserCallEnvironments(
        EvalCtx Context,
        ValEnv ValueEnvironment);

    private readonly record struct EvaluatedSlotBindings(
        ValEnv ValueBindings,
        CountedParamEnv CountedBindings);

    private enum GenericLoopStepBindingShape
    {
        Legacy,
        Patterned,
        FlatFixed,
        FlatCollecting,
    }

    private readonly record struct GenericLoopStepBindingSelection(
        GenericLoopStepBindingShape Shape,
        FlatCollectingBindingLayout? FlatCollectingLayout);

    private readonly record struct GenericLoopStepBindingContract(
        IReadOnlyList<ParameterDeclaration> Parameters,
        IReadOnlyList<ParameterPattern> ParameterPatterns,
        IReadOnlyList<string> ParameterNames);

    private readonly record struct CallableArgumentBindings<T>(
        IReadOnlyList<(string ParameterName, T Item)> NormalBindings,
        string? CollectingParameterName,
        IReadOnlyList<T> CollectingItems);

    private readonly record struct FlatCollectingBindingLayout(
        CallableSignature Signature,
        string CollectingName);

    private readonly record struct CollectingCapture(
        string Name,
        Result Value,
        CountedResult CountedValue);

    /// <summary>
    /// One supplied item prepared for parameter binding: its value view
    /// (<see cref="Value"/>), its algorithm view where resolvable, and a retained
    /// value error. VALUES STAY VALUES (September 2026): every item is exactly ONE
    /// argument whatever supplied it — a non-spread written argument (whatever its
    /// value: scalar, sequence, list, <c>()</c>, <c>[]</c>), an explicit spread
    /// item, an extension dot-call receiver (<c>R.F(args)</c> assembles exactly the
    /// items of <c>F(R, args)</c>), a pattern-opened item, or a loop-state slot. No
    /// item records how it was written, because no binder reinterprets one item as
    /// several: only explicit spread and explicit structural patterns open a value.
    /// Lean: <c>ParameterPatternInput</c>.
    /// </summary>
    private readonly record struct ParameterPatternInput(
        Result? Value,
        Algorithm? Algorithm,
        EvalError? ValueError)
    {
        /// <summary>
        /// The written argument expression this slot was assembled from, retained for the
        /// ONE written-argument blame (<see cref="BlameWrittenArgumentSlot"/>) when a
        /// demand later surfaces <see cref="ValueError"/>. This is the user-call twin of
        /// <see cref="ResolvedArgumentAlgorithm.Source"/>: diagnostic identity only, never
        /// consulted for binding, and <c>null</c> for a slot no single written expression
        /// produced (an explicit spread's items, a pattern-opened item, a loop state slot).
        ///
        /// <para>Retaining the node rather than a rendered description is what keeps the
        /// deferred path free: a slot whose value is never demanded (<c>F(x, y) = x</c>
        /// called as <c>F(1, { })</c>) costs nothing, because the description is rendered
        /// only where an error actually surfaces.</para>
        /// </summary>
        public Expr? Source { get; init; }
    }

    private static bool HasStructuredParameterPattern(Algorithm algorithm)
        => algorithm.ParameterPatterns.Any(static parameter => parameter is SequenceValueParameterPattern);

    // User-call routing uses CallableBindingPlan.RequiresPatternedBinding.
    // This helper remains for runtime paths that inspect Algorithm patterns
    // directly, including callbacks, evaluated loop slots, and loop fallbacks.
    private static bool UsesPatternBinding(Algorithm algorithm)
        => HasStructuredParameterPattern(algorithm)
            || ParameterPattern.HasRepeatedCaptureNames(algorithm.ParameterPatterns);

    private static bool UsesPatternBinding(IReadOnlyList<ParameterPattern> parameterPatterns)
        => parameterPatterns.Any(static parameter => parameter is SequenceValueParameterPattern)
            || ParameterPattern.HasRepeatedCaptureNames(parameterPatterns);

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

    private static GenericLoopStepBindingSelection SelectGenericLoopStepBinding(Algorithm step)
    {
        var plan = TryCreateUserLoopStepBindingPlan(step);
        if (plan is null)
            return new GenericLoopStepBindingSelection(
                GenericLoopStepBindingShape.Legacy,
                FlatCollectingLayout: null);

        if (plan.RequiresPatternedBinding)
            return new GenericLoopStepBindingSelection(
                GenericLoopStepBindingShape.Patterned,
                FlatCollectingLayout: null);

        if (TryGetFlatCollectingBindingLayout(plan, out var collectingLayout))
            return new GenericLoopStepBindingSelection(
                GenericLoopStepBindingShape.FlatCollecting,
                collectingLayout);

        if (plan.TryGetFlatFixedLayout(out _))
            return new GenericLoopStepBindingSelection(
                GenericLoopStepBindingShape.FlatFixed,
                FlatCollectingLayout: null);

        return new GenericLoopStepBindingSelection(
            GenericLoopStepBindingShape.Legacy,
            FlatCollectingLayout: null);
    }

    private static bool ShouldPreserveLoopStepSequenceSpreadExpressionBoundaries(
        Algorithm step,
        GenericLoopStepBindingSelection bindingSelection)
        => bindingSelection.Shape switch
        {
            GenericLoopStepBindingShape.Patterned => true,
            GenericLoopStepBindingShape.Legacy => UsesPatternBinding(step),
            _ => false,
        };

    /// <summary>
    /// The loop-invariant part of generic loop-step execution, prepared ONCE per loop
    /// invocation and reused by every iteration (M16). Everything here depends only on
    /// the step algorithm and the loop's own context — never on iteration state — so
    /// per-iteration recomputation was pure waste: the binding selection rebuilt the
    /// step's callable signature, binding plan, and display text every iteration, and
    /// the shadowed counted environment refiltered the same invariant inputs.
    /// Iteration-varying work (state binding, the fresh counted-environment
    /// concatenation whose list identity is a zero-arg-cache key component, and step
    /// output evaluation) stays in <see cref="RunStepSlots"/>.
    /// </summary>
    private readonly record struct PreparedGenericLoopStep(
        GenericLoopStepBindingContract BindingContract,
        GenericLoopStepBindingSelection BindingSelection,
        AlgEnv ShadowedAlgEnv,
        CountedParamEnv ShadowedCountedParamEnv,
        bool PreserveSequenceSpreadExpressionBoundaries);

    /// <summary>
    /// Freezes the temporary algorithm-shaped view used to derive callable metadata.
    /// Public
    /// host-built AST records may retain caller-owned <see cref="IReadOnlyList{T}"/>
    /// instances, so reading the original user algorithm again after a callback could
    /// mix a prepared plan for the old shape with parameter lists mutated to a new
    /// shape. The returned copy is used only while preparation derives the narrow
    /// <see cref="GenericLoopStepBindingContract"/> and binding plan; it is not stored
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
    /// records are immutable and can be shared; sequence-pattern nodes are rebuilt so a
    /// host cannot mutate a retained nested <c>Items</c> list during the loop.
    /// Structural preflight has already rejected cycles before evaluation reaches this
    /// helper.
    /// </summary>
    private static IReadOnlyList<ParameterPattern> SnapshotParameterPatterns(
        IReadOnlyList<ParameterPattern> source)
    {
        if (source.Count == 0)
            return [];

        var snapshots = new Dictionary<SequenceValueParameterPattern, SequenceValueParameterPattern>(
            ReferenceEqualityComparer.Instance);
        var states = new Dictionary<SequenceValueParameterPattern, byte>(
            ReferenceEqualityComparer.Instance);
        var stack = new Stack<(SequenceValueParameterPattern Group, bool Expanded)>();

        foreach (var pattern in source)
        {
            if (pattern is not SequenceValueParameterPattern root || snapshots.ContainsKey(root))
                continue;

            stack.Push((root, Expanded: false));
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
                    for (var index = group.Items.Count - 1; index >= 0; index--)
                    {
                        if (group.Items[index] is SequenceValueParameterPattern child
                            && !snapshots.ContainsKey(child))
                        {
                            stack.Push((child, Expanded: false));
                        }
                    }

                    continue;
                }

                var items = new ParameterPattern[group.Items.Count];
                for (var index = 0; index < group.Items.Count; index++)
                {
                    var item = group.Items[index];
                    items[index] = item is SequenceValueParameterPattern child
                        ? snapshots[child]
                        : item;
                }

                snapshots[group] = new SequenceValueParameterPattern(items);
                states[group] = 2;
            }
        }

        var result = new ParameterPattern[source.Count];
        for (var index = 0; index < source.Count; index++)
        {
            var pattern = source[index];
            result[index] = pattern is SequenceValueParameterPattern group
                ? snapshots[group]
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
        var bindingSelection = SelectGenericLoopStepBinding(bindingContract);
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
            bindingSelection,
            inherited.AlgEnv,
            inherited.CountedParamEnv,
            ShouldPreserveLoopStepSequenceSpreadExpressionBoundaries(bindingContract, bindingSelection));
    }

    private static bool TryGetFlatCollectingBindingLayout(
        CallableBindingPlan plan,
        out FlatCollectingBindingLayout layout)
    {
        if (!plan.TryGetFlatCollectingLayout(out var prefix, out var collecting, out var suffix))
        {
            layout = default;
            return false;
        }

        layout = new FlatCollectingBindingLayout(
            plan.Signature,
            collecting.Name);
        return true;
    }

    private static bool TryGetLegacyFlatCollectingBindingLayout(
        IReadOnlyList<ParameterDeclaration> parameters,
        string callableName,
        out FlatCollectingBindingLayout layout)
    {
        for (var index = 0; index < parameters.Count; index++)
        {
            var parameter = parameters[index];
            if (parameter.Kind != ParameterKind.Collecting)
                continue;

            var signature = new CallableSignature(
                callableName,
                parameters
                    .Select(static parameter => new CallableParameter(parameter.Name, parameter.Kind))
                    .ToArray());
            layout = new FlatCollectingBindingLayout(
                signature,
                parameter.Name);
            return true;
        }

        layout = default;
        return false;
    }

    private static bool TryGetPlanDerivedFlatFixedParameterNames(
        CallableBindingPlan plan,
        out IReadOnlyList<string> parameterNames)
    {
        if (!plan.TryGetFlatFixedLayout(out var captures))
        {
            parameterNames = [];
            return false;
        }

        parameterNames = captures.Select(static capture => capture.Name).ToArray();
        return true;
    }

    private static EvalResult<CallableArgumentBindings<T>> BindCallableArguments<T>(
        CallableSignature signature,
        IReadOnlyList<T> items,
        Func<int, int, EvalError> arityMismatch)
    {
        if (signature.Validate() is { } validationError)
            return validationError;

        var collectingIndex = signature.CollectingParameterIndex;
        if (collectingIndex < 0)
        {
            if (items.Count != signature.Parameters.Count)
                return arityMismatch(signature.Parameters.Count, items.Count);

            return EvalResult<CallableArgumentBindings<T>>.Ok(new CallableArgumentBindings<T>(
                signature.Parameters.Zip(items, static (parameter, item) => (parameter.Name, item)).ToList(),
                CollectingParameterName: null,
                CollectingItems: []));
        }

        // The minimum is the FIXED (non-collecting) parameter count: like every
        // other collecting binding, the collecting parameter may collect ZERO items
        // (an empty collected segment is the exact list `[]`). This is the same rule the shared pattern
        // binder applies (BindParameterPatternList: required = patterns - 1).
        // (Collection builtins no longer bind here: they are ordinary
        // fixed-arity callables bound in BindSequenceBuiltinArguments.)
        var requiredNormalItemCount = signature.Parameters.Count - 1;
        if (items.Count < requiredNormalItemCount)
            return arityMismatch(requiredNormalItemCount, items.Count);

        var suffixCount = signature.Parameters.Count - collectingIndex - 1;
        var suffixStart = items.Count - suffixCount;
        var normalBindings = new List<(string ParameterName, T Item)>(requiredNormalItemCount);

        for (var index = 0; index < collectingIndex; index++)
            normalBindings.Add((signature.Parameters[index].Name, items[index]));

        for (var suffixIndex = 0; suffixIndex < suffixCount; suffixIndex++)
        {
            var parameterIndex = collectingIndex + 1 + suffixIndex;
            var itemIndex = suffixStart + suffixIndex;
            normalBindings.Add((signature.Parameters[parameterIndex].Name, items[itemIndex]));
        }

        var collectingItems = items
            .Skip(collectingIndex)
            .Take(suffixStart - collectingIndex)
            .ToList();

        return EvalResult<CallableArgumentBindings<T>>.Ok(new CallableArgumentBindings<T>(
            normalBindings,
            signature.Parameters[collectingIndex].Name,
            collectingItems));
    }

    /// <summary>
    /// Collect the item segment assigned to a collecting binding as ONE list value.
    ///
    /// KatLang distinguishes three item-supply operations by receiver purpose:
    /// <c>capture</c> — ordinary value/output capture, the normalizing
    /// boundary (<see cref="Result.FromItems"/>, singleton erasure applies);
    /// <c>collect</c> — THIS operation: a collecting binding (collecting parameter) materializes
    /// exactly the assigned items as one list
    /// (<c>CollectSegment([]) == []</c>, <c>CollectSegment([v]) == [v]</c>, never
    /// erased); and <c>spread</c> — the postfix spread marker
    /// (<see cref="Result.SpreadItems"/>), which opens one sequence OR list
    /// boundary. The round trip <c>SpreadItems(CollectSegment(xs)) == xs</c>
    /// makes collecting-parameter forwarding ordinary list spread with no hidden
    /// raw-supply metadata. Snapshot construction: the public
    /// <see cref="Result.ListValue"/> constructor copies the supplied items,
    /// so no caller-retained buffer can mutate the collected value.
    /// Lean: <c>collectSegment</c>.
    /// </summary>
    private static EvalResult<Result.ListValue> CollectSegment(
        EvalCtx ctx,
        IReadOnlyList<Result> capturedValues,
        SourceSpan? span = null)
    {
        if (ReserveCollection(ctx, capturedValues.Count, span) is { } error)
            return error;

        return EvalResult<Result.ListValue>.Ok(
            Result.ListValue.TakeOwnership(capturedValues.ToArray()));
    }

    /// <summary>
    /// True when an argument's resolved algorithm meaning is genuinely
    /// callable-shaped — a builtin, a conditional clause family, or an
    /// algorithm declaring parameters/patterns — as opposed to a
    /// zero-parameter VALUE property that merely resolved through the dual
    /// algorithm channel. Used to decide whether a valueless argument
    /// bound by a collecting parameter gets the targeted "collects values, but ... is a callable"
    /// diagnostic or surfaces its genuine value-evaluation error.
    /// Lean: <c>Algorithm.isFunctionShaped</c>.
    /// </summary>
    private static bool IsFunctionShapedAlgorithm(Algorithm algorithm)
        => algorithm switch
        {
            Algorithm.Builtin => true,
            Algorithm.Conditional => true,
            Algorithm.User user => user.ParameterCount > 0 || user.ParameterPatterns.Count > 0,
        };

    private static EvalResult<CollectingCapture> CreateCollectingCapture(
        EvalCtx ctx,
        string name,
        IReadOnlyList<Result> capturedValues,
        SourceSpan? span = null)
    {
        var capturedResultR = CollectSegment(ctx, capturedValues, span);
        if (capturedResultR.IsError) return capturedResultR.Error;
        var capturedResult = capturedResultR.Value;
        // A list value is one visible value, so a collecting binding always carries
        // emitted count 1 (including the empty collected list `[]`).
        return EvalResult<CollectingCapture>.Ok(new CollectingCapture(
            name,
            capturedResult,
            new CountedResult(capturedResult, 1)));
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
    /// The items a sequence-value parameter pattern binds against: the slot's VALUE,
    /// opened one level. PATTERN PARENTHESES ARE CALL-SHAPE SYNTAX, NOT A RUNTIME
    /// BOUNDARY (September 2026): a received sequence value or exact list value opens to
    /// its immediate items (Lean: <c>Result.structureItems?</c> — the deconstruction
    /// receiver opens ONE lone structure boundary of either kind, so
    /// <c>x, y, z = [1, 2, 3]</c> binds like <c>x, y, z = [1, 2, 3]*</c>), and any other
    /// value is a one-item supply for the prefix/collecting/suffix matcher. Nothing about
    /// how the slot was WRITTEN survives here: <c>F((1, 2))</c>, <c>F(S)</c> with
    /// <c>S = 1, 2</c>, <c>F(((1, 2)))</c>, <c>F({S})</c>, and <c>F((S*))</c> all bind the
    /// value <c>(1, 2)</c>. (The former written-slot view, which let a group's own written
    /// rows override its value, is gone: parentheses group syntax and never suspend
    /// normalization.) Lean: the <c>.sequenceValue</c> arm of <c>bindParameterPattern</c>.
    /// </summary>
    private static EvalResult<IReadOnlyList<Result>> GetSequenceValuePatternItems(ParameterPatternInput input)
    {
        if (input.Value is { } value)
            return EvalResult<IReadOnlyList<Result>>.Ok(SequenceValuePatternItems(value));

        return SurfacedSlotValueError(input);
    }

    /// <summary>
    /// NESTED-PATTERN OPENING (September 2026, S3): the items a sequence-value parameter
    /// pattern binds against, given the ONE value its slot supplies. This is the ONE rule
    /// shared by the ordinary binder (<see cref="GetSequenceValuePatternItems"/>) and the
    /// counted callback binder (<see cref="BindCountedParameterPattern"/>), so a callback
    /// that supplies one value <c>V</c> to a pattern <c>P</c> binds exactly as the ordinary
    /// call <c>P(V)</c> does — callback provenance changes nothing. A sequence value or exact
    /// list value opens to its immediate items (<see cref="Result.StructureItems"/>, ONE
    /// boundary of either kind); any other value — a number, a string, a Boolean — is a
    /// ONE-item supply (the scalar one-item fallback), at every pattern level and for every
    /// group size: <c>(x)</c>, <c>(x, *rest)</c>, <c>(*xs)</c>, and <c>(*init, z)</c> bind it,
    /// while <c>(x, y)</c> and <c>(x, *r, z)</c> reject it through the nested group's
    /// ordinary arity check (one value supplied). The fallback supplies one value, never
    /// zero, and it never opens anything further.
    /// Lean: <c>Result.sequenceValuePatternItems</c>.
    /// </summary>
    private static IReadOnlyList<Result> SequenceValuePatternItems(Result value)
        => value.StructureItems() ?? [value];

    /// <summary>
    /// Raises a written slot's retained value error at the demand that needs its VALUE,
    /// blaming the written argument when the slot produced no output at all (F5 — the ONE
    /// <see cref="BlameWrittenArgumentSlot"/>). Every other retained error is raised
    /// exactly as before, and a slot with no retained error at all is the binder's own
    /// <see cref="EvalError.BadArity"/>.
    /// </summary>
    private static EvalError SurfacedSlotValueError(ParameterPatternInput input)
        => input.ValueError is not { } valueError
            ? new EvalError.BadArity()
            : input.Source is { } source
                ? BlameWrittenArgumentSlot(source, valueError)
                : valueError;

    /// <summary>
    /// Arity mismatch produced by binding one nested sequence-value parameter
    /// pattern group's OWN items. The structured payload keeps the innermost
    /// Lean-aligned <see cref="EvalError.ArityMismatch"/> unchanged; the added
    /// context only attributes the failure to the written group (e.g.
    /// <c>(b, c)</c>) instead of the enclosing call's argument count.
    /// Genuine top-level call-arity mismatches and argument evaluation errors
    /// passing through the binder are never wrapped.
    /// </summary>
    private static EvalError SequenceValuePatternArityMismatch(
        SequenceValueParameterPattern group,
        int required,
        int actual)
        => new EvalError.WithContext(
            new SequenceValueParameterBindingContext(
                group.DisplayName,
                group.Items.Any(static item => item is CaptureParameterPattern { Kind: ParameterKind.Collecting })),
            new EvalError.ArityMismatch(required, actual));

    private static EvalResult<UserCallBindings> BindParameterPattern(
        ParameterPattern pattern,
        ParameterPatternInput input,
        EvalCtx ctx,
        bool allowAlgorithmBindings)
    {
        switch (pattern)
        {
            case CaptureParameterPattern { Kind: ParameterKind.Normal } capture:
                {
                    var valueBindings = new List<(string Name, Result Value)>(1);
                    var algorithmBindings = new List<(string Name, Algorithm Value, EvalError? ValueError)>(1);

                    if (input.Value is not null)
                        valueBindings.Add((capture.Name, input.Value));

                    if (allowAlgorithmBindings && input.Algorithm is not null)
                    {
                        algorithmBindings.Add((
                            capture.Name,
                            input.Algorithm,
                            RetainResourceLimitForAlgorithmBinding(input.ValueError)));
                    }

                    if (input.Value is null && (!allowAlgorithmBindings || input.Algorithm is null))
                        return SurfacedSlotValueError(input);

                    return EvalResult<UserCallBindings>.Ok(new UserCallBindings(valueBindings, [], algorithmBindings));
                }

            case CaptureParameterPattern { Kind: ParameterKind.Collecting }:
                return new EvalError.BadArity();

            case SequenceValueParameterPattern group:
                {
                    // A non-structure value is a one-item supply for the
                    // prefix/collecting/suffix matcher (SequenceValuePatternItems, the
                    // rule the counted callback binder shares), so a scalar right-hand
                    // side binds a collecting pattern that captures zero items, e.g.
                    // `first, *tail = 1` (first = 1, tail = []). Only a slot with no
                    // value at all fails here, with its retained value error.
                    var itemsR = GetSequenceValuePatternItems(input);
                    if (itemsR.IsError) return itemsR.Error;

                    var nestedInputs = itemsR.Value
                        .Select(static item => new ParameterPatternInput(item, Algorithm: null, ValueError: null))
                        .ToList();
                    return BindParameterPatternList(
                        group.Items,
                        nestedInputs,
                        ctx,
                        allowAlgorithmBindings: false,
                        (required, actual) => SequenceValuePatternArityMismatch(group, required, actual));
                }

            default:
                return new EvalError.BadArity();
        }
    }

    /// <summary>
    /// Binds a parameter-pattern list against its supplied inputs in Lean's order
    /// (<c>bindParameterPatternList</c>):
    /// <list type="number">
    /// <item>the arity check against the ONE minimum-supply rule;</item>
    /// <item>every pattern of a range binds, left to right, BEFORE any repeated name is
    /// decided (Lean <c>bindPairs</c>), so a later pattern's binding failure — its nested arity
    /// mismatch, or its argument's retained value error — outranks the range's repeated-name
    /// conflicts (<see cref="BindParameterPatternRange"/>);</item>
    /// <item>with a collecting capture, the prefix binds and settles, then the suffix, then the
    /// collector's values are collected and materialized, and the names shared across the
    /// collector are decided last (<see cref="FindCrossRepeatedNameFailure"/>).</item>
    /// </list>
    /// REPEATED-NAME BINDING IS ORDER-INDEPENDENT (September 2026): a repeated name is decided
    /// ONCE per level, when its last contribution joins, by requiring every PAIR of its
    /// contributions to be compatible (<see cref="RepeatedNameAggregate"/>), so no permutation
    /// of the arguments changes its effective binding. Multiple callable contributions must
    /// also share one declaration and captured activation identity, including two occurrences. The first collecting capture is
    /// the list's collector (Lean <c>findCollecting</c>); a second one — a host-built shape the
    /// parser never produces — is an ordinary suffix pattern that
    /// <see cref="BindParameterPattern"/> rejects. A successful binding keeps each name's first
    /// binding on each channel.
    /// </summary>
    private static EvalResult<UserCallBindings> BindParameterPatternList(
        IReadOnlyList<ParameterPattern> patterns,
        IReadOnlyList<ParameterPatternInput> inputs,
        EvalCtx ctx,
        bool allowAlgorithmBindings,
        Func<int, int, EvalError> arityMismatch)
    {
        var collectingIndex = FirstCollectingCaptureIndex(patterns);

        // The accepted supply is the ONE minimum-supply rule
        // (ParameterPattern.MinimumSuppliedSlots): without a collecting capture every
        // pattern needs its own slot, so the count is EXACT; with one the minimum is a
        // lower bound and the collector takes whatever is left over.
        var requiredCount = ParameterPattern.MinimumSuppliedSlots(patterns);

        if (collectingIndex < 0)
        {
            if (inputs.Count != requiredCount)
                return arityMismatch(requiredCount, inputs.Count);

            var rangeR = BindParameterPatternRange(
                patterns, inputs, 0, 0, patterns.Count, ctx, allowAlgorithmBindings, outside: null);
            if (rangeR.IsError) return rangeR.Error;
            return EvalResult<UserCallBindings>.Ok(rangeR.Value.Merged);
        }

        if (inputs.Count < requiredCount)
            return arityMismatch(requiredCount, inputs.Count);

        var collectingCapture = (CaptureParameterPattern)patterns[collectingIndex];
        var suffixStart = collectingIndex + 1;
        var suffixCount = patterns.Count - suffixStart;
        var suffixInputStart = inputs.Count - suffixCount;

        // A range's repeated name waits for the cross merges when the level also binds it on
        // the other side of the collector, or as the collector.
        var prefixR = BindParameterPatternRange(
            patterns, inputs, 0, 0, collectingIndex, ctx, allowAlgorithmBindings,
            new LevelNames(patterns, suffixStart, suffixCount, collectingCapture.Name));
        if (prefixR.IsError) return prefixR.Error;

        var suffixR = BindParameterPatternRange(
            patterns, inputs, suffixStart, suffixInputStart, suffixCount, ctx, allowAlgorithmBindings,
            new LevelNames(patterns, 0, collectingIndex, collectingCapture.Name));
        if (suffixR.IsError) return suffixR.Error;

        var capturedValues = new List<Result>(suffixInputStart - collectingIndex);
        for (var inputIndex = collectingIndex; inputIndex < suffixInputStart; inputIndex++)
        {
            var input = inputs[inputIndex];
            if (input.Value is null)
            {
                // A collecting binding collects VALUES. A callable-shaped argument
                // (a builtin, a clause family, or a parameterized algorithm)
                // has no value to collect — only fixed parameters keep the
                // dual algorithm channel — so name the actual conflict instead
                // of surfacing the argument's incidental value-evaluation
                // error. A zero-parameter VALUE property whose body failed is
                // NOT callable-shaped: its genuine evaluation error surfaces.
                if (input.Algorithm is { } algorithm && IsFunctionShapedAlgorithm(algorithm))
                {
                    return new EvalError.TypeMismatch(
                        $"Collecting parameter `*{collectingCapture.Name}` collects values, but a supplied argument is a callable. " +
                        "Pass a value, or call the callable so its result is collected.");
                }

                // A collector accepts zero SUPPLIED items, but an ordinary written argument
                // that produced no output never becomes "nothing was supplied": it is that
                // argument's failure (F5), so `Coll({ })` can never collapse to `Coll()`.
                return SurfacedSlotValueError(input);
            }

            // Every item allocated to the flat top-level collecting position
            // contributes its ONE reified value, unopened: the collector collects
            // exactly the items allocated to it (THE EXACT COLLECTOR LAW).
            capturedValues.Add(input.Value);
        }

        var captureR = CreateCollectingCapture(
            ctx,
            collectingCapture.Name,
            capturedValues,
            collectingCapture.Span);
        if (captureR.IsError) return captureR.Error;
        var capture = captureR.Value;
        var collector = new UserCallBindings(
            [(capture.Name, capture.Value)],
            [(capture.Name, capture.CountedValue)],
            []);

        // The cross merges decide every name shared across the collector, including a repeat a
        // range left to them — so they run whenever a range repeated a name, not only when the
        // merged ranges repeat one (a range's merged set has already dropped its duplicates).
        var bindings = new PatternBindingAccumulator();
        bindings.Add(prefixR.Value.Merged);
        bindings.Add(suffixR.Value.Merged);
        bindings.Add(collector);
        if ((bindings.SawRepeatedName || prefixR.Value.HadRepeatedName || suffixR.Value.HadRepeatedName)
            && FindCrossRepeatedNameFailure(
                prefixR.Value,
                collectingCapture.Name,
                collector,
                suffixR.Value,
                new LevelNames(patterns, suffixStart, suffixCount, extraName: null)) is { } failure)
        {
            return failure;
        }

        return EvalResult<UserCallBindings>.Ok(bindings.ToBindings());
    }

    /// <summary>
    /// Lean <c>findCollecting</c>: the index of the FIRST collecting capture at this pattern
    /// level, or <c>-1</c>.
    /// </summary>
    private static int FirstCollectingCaptureIndex(IReadOnlyList<ParameterPattern> patterns)
    {
        for (var index = 0; index < patterns.Count; index++)
        {
            if (patterns[index] is CaptureParameterPattern { Kind: ParameterKind.Collecting })
                return index;
        }

        return -1;
    }

    /// <summary>
    /// One bound range of a pattern level: its first-occurrence binding set, the per-pattern
    /// contributions the cross merges read (for a range of more than one pattern), and whether
    /// some name repeated inside it — a repeat the range may have left to the cross merges
    /// because the level binds the name on the other side of the collector too.
    /// </summary>
    private readonly record struct PatternRangeBindings(
        UserCallBindings Merged,
        IReadOnlyList<UserCallBindings>? Bound,
        bool HadRepeatedName = false)
    {
        public IReadOnlyList<UserCallBindings> Contributions => Bound ?? [Merged];
    }

    /// <summary>
    /// Lean <c>bindPairs</c> plus its merges over one contiguous range of fixed patterns:
    /// EVERY pattern binds, left to right, before any repeated name is decided, and the range
    /// then decides the repeated names whose every contribution it holds
    /// (<see cref="FindRangeRepeatedNameFailure"/>; a name <paramref name="outside"/> also binds
    /// waits for the cross merges).
    /// </summary>
    private static EvalResult<PatternRangeBindings> BindParameterPatternRange(
        IReadOnlyList<ParameterPattern> patterns,
        IReadOnlyList<ParameterPatternInput> inputs,
        int patternStart,
        int inputStart,
        int count,
        EvalCtx ctx,
        bool allowAlgorithmBindings,
        LevelNames? outside)
    {
        if (count == 0)
            return EvalResult<PatternRangeBindings>.Ok(new PatternRangeBindings(new UserCallBindings([], [], []), null));

        if (count == 1)
        {
            var singleR = BindParameterPattern(patterns[patternStart], inputs[inputStart], ctx, allowAlgorithmBindings);
            if (singleR.IsError) return singleR.Error;
            return EvalResult<PatternRangeBindings>.Ok(new PatternRangeBindings(singleR.Value, null));
        }

        var bound = new UserCallBindings[count];
        for (var offset = 0; offset < count; offset++)
        {
            var boundR = BindParameterPattern(
                patterns[patternStart + offset], inputs[inputStart + offset], ctx, allowAlgorithmBindings);
            if (boundR.IsError) return boundR.Error;
            bound[offset] = boundR.Value;
        }

        var bindings = new PatternBindingAccumulator();
        foreach (var patternBindings in bound)
            bindings.Add(patternBindings);

        // Only a name bound by more than one pattern can fail.
        if (bindings.SawRepeatedName && FindRangeRepeatedNameFailure(bound, outside) is { } failure)
            return failure;

        return EvalResult<PatternRangeBindings>.Ok(
            new PatternRangeBindings(bindings.ToBindings(), bound, bindings.SawRepeatedName));
    }

    /// <summary>
    /// The repeated-name failure of one bound range, in Lean's merge order
    /// (<c>settlePatternRange</c>): <c>merge c₁ (merge c₂ (… cₙ))</c> runs the innermost merge
    /// first, and a repeated name is decided at the ONE merge where its last contribution
    /// joins — the step of its FIRST occurrence — so the failing name whose first occurrence is
    /// rightmost is reported; within one step an unequal value (<see cref="EvalError.BadArity"/>)
    /// outranks an algorithm-channel conflict (<see cref="EvalError.TypeMismatch"/>). A name
    /// <paramref name="outside"/> also binds is not complete here. <c>null</c> when every
    /// complete repeated name binds.
    /// </summary>
    private static EvalError? FindRangeRepeatedNameFailure(IReadOnlyList<UserCallBindings> bound, LevelNames? outside)
    {
        var failingStep = -1;
        var failingKind = RepeatedNameFailureKind.None;
        foreach (var aggregate in RepeatedNameAggregate.Collect(bound).Values)
        {
            if (aggregate.ContributionCount < 2 || outside?.Contains(aggregate.Name) == true)
                continue;

            var kind = aggregate.Failure;
            if (kind == RepeatedNameFailureKind.None)
                continue;

            if (aggregate.FirstIndex > failingStep)
            {
                failingStep = aggregate.FirstIndex;
                failingKind = kind;
            }
            else if (aggregate.FirstIndex == failingStep && kind > failingKind)
            {
                failingKind = kind;
            }
        }

        return failingStep < 0
            ? null
            : RepeatedNameFailureError(failingKind);
    }

    /// <summary>
    /// The cross merges of a collecting list (Lean: merge the prefix with the collector, then
    /// that with the suffix): the collector's name is decided at the first merge unless the
    /// suffix binds it too, and every name the suffix shares with the prefix or the collector
    /// at the second — each with every one of its contributions in hand.
    /// </summary>
    private static EvalError? FindCrossRepeatedNameFailure(
        PatternRangeBindings prefix,
        string collectorName,
        UserCallBindings collector,
        PatternRangeBindings suffix,
        LevelNames suffixNames)
    {
        var leftSide = new List<UserCallBindings>(prefix.Contributions) { collector };
        var left = RepeatedNameAggregate.Collect(leftSide);
        if (left.TryGetValue(collectorName, out var atCollector)
            && atCollector.ContributionCount >= 2
            && !suffixNames.Contains(collectorName)
            && atCollector.Failure is not RepeatedNameFailureKind.None and var collectorFailure)
        {
            return RepeatedNameFailureError(collectorFailure);
        }

        var suffixContributions = suffix.Contributions;
        var all = RepeatedNameAggregate.Collect([.. leftSide, .. suffixContributions]);
        var worst = RepeatedNameFailureKind.None;
        foreach (var name in RepeatedNameAggregate.Collect(suffixContributions).Keys)
        {
            if (!left.ContainsKey(name))
                continue;

            var kind = all[name].Failure;
            if (kind == RepeatedNameFailureKind.Value)
                return RepeatedNameFailureError(kind);
            if (kind > worst)
                worst = kind;
        }

        return worst == RepeatedNameFailureKind.None ? null : RepeatedNameFailureError(worst);
    }

    private static EvalError RepeatedNameFailureError(RepeatedNameFailureKind kind)
        => kind switch
        {
            RepeatedNameFailureKind.Value => new EvalError.BadArity(),
            RepeatedNameFailureKind.CallableIdentity => new EvalError.TypeMismatch(
                "Repeated bind equality requires the same callable identity"),
            _ => new EvalError.TypeMismatch("Repeated bind equality is not supported for algorithm-only arguments"),
        };

    private enum RepeatedNameFailureKind
    {
        None,

        /// <summary>Equal values cannot make different callables interchangeable.</summary>
        CallableIdentity,

        /// <summary>Two or more contributions bind the name on the algorithm channel and one of them carries no value.</summary>
        Algorithm,

        /// <summary>Two contributions carry unequal values or unequal counted values.</summary>
        Value,
    }

    /// <summary>
    /// REPEATED-NAME VERDICT (September 2026): every contribution of one name at one pattern
    /// level, summarized so the verdict is a function of the MULTISET of contributions
    /// (Lean <c>repeatedNameFailure</c>): the name binds iff every PAIR of its contributions is
    /// compatible — equal values, equal counted values, and two algorithm-channel bindings only
    /// when each carries a value and all share the same callable identity.
    /// <see cref="Result.ValueComparer"/> is an equivalence, so "some pair differs" is "some
    /// value differs from the first".
    /// </summary>
    private sealed class RepeatedNameAggregate(string name)
    {
        public string Name { get; } = name;

        public int ContributionCount { get; private set; }

        public int FirstIndex { get; private set; } = -1;

        private int _lastIndex = -1;
        private Result? _firstValue;
        private bool _valueConflict;
        private CountedResult? _firstCounted;
        private bool _countedConflict;
        private int _algorithmCount;
        private bool _algorithmWithoutValue;
        private Algorithm? _firstAlgorithm;
        private bool _callableIdentityConflict;

        public RepeatedNameFailureKind Failure
            => _valueConflict || _countedConflict
                ? RepeatedNameFailureKind.Value
                : _algorithmCount >= 2 && _algorithmWithoutValue
                    ? RepeatedNameFailureKind.Algorithm
                    : _callableIdentityConflict
                        ? RepeatedNameFailureKind.CallableIdentity
                        : RepeatedNameFailureKind.None;

        /// <summary>Aggregates every name of the given contributions, in order.</summary>
        public static Dictionary<string, RepeatedNameAggregate> Collect(IReadOnlyList<UserCallBindings> contributions)
        {
            var aggregates = new Dictionary<string, RepeatedNameAggregate>(StringComparer.Ordinal);
            RepeatedNameAggregate For(string name, int index)
            {
                if (!aggregates.TryGetValue(name, out var aggregate))
                    aggregates[name] = aggregate = new RepeatedNameAggregate(name);
                aggregate.Touch(index);
                return aggregate;
            }

            for (var index = 0; index < contributions.Count; index++)
            {
                var contribution = contributions[index];
                foreach (var (valueName, value) in contribution.ValueBindings)
                    For(valueName, index).AddValue(value);
                foreach (var (countedName, counted) in contribution.CountedBindings)
                    For(countedName, index).AddCounted(counted);

                HashSet<string>? valueNames = null;
                foreach (var binding in contribution.AlgorithmBindings)
                {
                    valueNames ??= contribution.ValueBindings.Select(static value => value.Name).ToHashSet(StringComparer.Ordinal);
                    For(binding.Name, index).AddAlgorithm(binding.Value, hasValue: valueNames.Contains(binding.Name));
                }
            }

            return aggregates;
        }

        private void Touch(int index)
        {
            if (_lastIndex == index)
                return;

            ContributionCount++;
            if (FirstIndex < 0)
                FirstIndex = index;
            _lastIndex = index;
        }

        private void AddValue(Result value)
        {
            if (_firstValue is null)
                _firstValue = value;
            else if (!Result.ValueComparer.Equals(_firstValue, value))
                _valueConflict = true;
        }

        private void AddCounted(CountedResult counted)
        {
            // Compatibility applies to the complete counted channel, even when a
            // caller supplies counts that are not canonical value-boundary counts.
            if (_firstCounted is not { } first)
                _firstCounted = counted;
            else if (first.EmittedCount != counted.EmittedCount
                || !Result.ValueComparer.Equals(first.Value, counted.Value))
                _countedConflict = true;
        }

        private void AddAlgorithm(Algorithm algorithm, bool hasValue)
        {
            _algorithmCount++;
            if (!hasValue)
                _algorithmWithoutValue = true;
            if (_firstAlgorithm is null)
                _firstAlgorithm = algorithm;
            else if (!SameRepeatedCallableIdentity(_firstAlgorithm, algorithm))
                _callableIdentityConflict = true;
        }
    }

    /// <summary>
    /// Identity of a callable, including its lexical activation. Parent-wired copies of one
    /// declaration keep their identity; a different declaration or captured activation does
    /// not become the same callable merely because its zero-argument value compares equal.
    /// This comparison executes no body and reads no value/cache channel.
    /// Lean: <c>sameRepeatedCallableIdentity</c>.
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
    private sealed class LevelNames(IReadOnlyList<ParameterPattern> patterns, int start, int count, string? extraName)
    {
        private HashSet<string>? _names;

        public bool Contains(string name) => (_names ??= Build()).Contains(name);

        private HashSet<string> Build()
        {
            var names = ParameterPattern.FlattenCaptures(patterns.Skip(start).Take(count))
                .Select(static capture => capture.Name)
                .ToHashSet(StringComparer.Ordinal);
            if (extraName is not null)
                names.Add(extraName);
            return names;
        }
    }

    /// <summary>
    /// First-occurrence accumulation of pattern bindings — the merged binding set of a level
    /// (each name keeps its first binding on each channel; every repeated name has passed its
    /// verdict, so discarded entries have equal complete values/counts or the same callable
    /// identity; choosing a storage representative gives no callable positional precedence), built in one
    /// linear pass. It records whether any name repeated, the only situation in which a
    /// repeated-name verdict can fail, so the binders decide verdicts only then.
    /// </summary>
    private sealed class PatternBindingAccumulator
    {
        private readonly List<(string Name, Result Value)> _values = [];
        private readonly List<(string Name, CountedResult Value)> _counted = [];
        private readonly List<(string Name, Algorithm Value, EvalError? ValueError)> _algorithms = [];
        private readonly HashSet<string> _valueNames = new(StringComparer.Ordinal);
        private readonly HashSet<string> _countedNames = new(StringComparer.Ordinal);
        private readonly HashSet<string> _algorithmNames = new(StringComparer.Ordinal);

        public bool SawRepeatedName { get; private set; }

        public void Add(UserCallBindings bindings)
        {
            foreach (var binding in bindings.ValueBindings)
            {
                if (_valueNames.Add(binding.Name))
                    _values.Add(binding);
                else
                    SawRepeatedName = true;
            }

            foreach (var binding in bindings.CountedBindings)
            {
                if (_countedNames.Add(binding.Name))
                    _counted.Add(binding);
                else
                    SawRepeatedName = true;
            }

            foreach (var binding in bindings.AlgorithmBindings)
            {
                if (_algorithmNames.Add(binding.Name))
                    _algorithms.Add(binding);
                else
                    SawRepeatedName = true;
            }
        }

        public UserCallBindings ToBindings() => new(_values, _counted, _algorithms);
    }

    private static EvalResult<UserCallBindings> BindPatternedUserCall(
        Algorithm callee,
        OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        // Passive, run-scoped observation: this is the one path that binds a deconstruction helper's
        // shared N-capture pattern in both the old per-target and new shared-bind implementations, so
        // a run's observer counts N binds under the old design and exactly one under the shared bind.
        // Null for ordinary runs (no material effect); an observed run records through this context.
        if (callee is Algorithm.User { AssignmentDeconstructionTarget: not null })
            ctx.Observations?.RecordDeconstructionFullBind();

        var inputsR = BuildCallArgumentInputs(args, ctx, valEnv);
        if (inputsR.IsError) return inputsR.Error;

        var bindingsR = BindParameterPatternList(
            callee.ParameterPatterns,
            inputsR.Value,
            ctx,
            allowAlgorithmBindings: true,
            (required, actual) => new EvalError.ArityMismatch(required, actual)
            {
                Signature = CallableSignature.FromAlgorithm(calleeName.Render(ctx), callee),
                InferredImplicitParameters = ImplicitParameterProvenance.CollectFrom(callee.Parameters),
            });

        // Assignment deconstruction is parser-elaborated into an anonymous
        // inline helper; phrase its binding failures against the WRITTEN
        // assignment pattern instead of leaking the synthetic call shape
        // ("Algorithm `(inline library)` expects ..."). Wrap ONLY genuine
        // shape failures: when an input slot carried no value, the surfaced
        // ArityMismatch is (or reflects) that argument's own value-evaluation
        // error — re-wording it would misattribute unrelated numbers to the
        // written pattern (e.g. `x, y = sum` leaking sum's 0/0 arity error).
        // The helper binds through one synthetic inline sequence-value pattern,
        // so its shape failure may arrive wrapped in that pattern's
        // SequenceValueParameterBindingContext — the assignment-focused
        // DeconstructionBindingContext takes precedence and replaces it.
        if (bindingsR.IsError
            && callee is Algorithm.User { AssignmentDeconstructionTarget: not null }
            && TryGetDeconstructionShapeMismatch(bindingsR.Error) is { } deconstructionMismatch
            && inputsR.Value.All(static input => input.Value is not null))
        {
            return new EvalError.WithContext(
                new DeconstructionBindingContext(
                    callee.Parameters.Select(static parameter => parameter.DisplayName).ToList(),
                    callee.Parameters.Any(static parameter => parameter.Kind == ParameterKind.Collecting)),
                deconstructionMismatch);
        }

        return bindingsR;
    }

    /// <summary>
    /// Recognize a deconstruction helper's genuine binding-shape failure: either
    /// a bare top-level <see cref="EvalError.ArityMismatch"/>, or one wrapped in
    /// the nested-group <see cref="SequenceValueParameterBindingContext"/> the
    /// helper's synthetic inline pattern produced (at most one such layer exists:
    /// only the innermost failing group attaches its context). Returns the inner
    /// mismatch to re-wrap in the assignment-focused context, or null when the
    /// error is not a shape mismatch (e.g. a passed-through argument error).
    /// </summary>
    private static EvalError.ArityMismatch? TryGetDeconstructionShapeMismatch(EvalError error)
        => error switch
        {
            EvalError.ArityMismatch direct => direct,
            EvalError.WithContext { ErrorContext: SequenceValueParameterBindingContext, Inner: EvalError.ArityMismatch nested } => nested,
            _ => null,
        };

    /// <summary>
    /// Shared lazy binding of one assignment-deconstruction group. All N target helpers of a
    /// deconstruction apply the SAME shared N-capture pattern to the SAME hoisted source value,
    /// so the whole bind is computed once per (group, binding context) and each target projects
    /// its own slot. The first demanded target pays the full bind (RHS evaluation, one pattern
    /// bind, one collected-list materialization); every later target of the same group projects in
    /// O(1). Deferred semantics are unchanged: nothing binds until a target is demanded, and a
    /// binding failure (wrong arity, phrased against the written pattern by
    /// <see cref="BindPatternedUserCall"/>) surfaces from the first demanded target with its span
    /// intact. Returns <c>null</c> only when <paramref name="target"/> projects an index outside the
    /// shared bind (a hand-built helper whose metadata disagrees with its parameter list), so the
    /// caller falls back to the ordinary per-call binding path.
    /// </summary>
    private static EvalResult<Result>? TryProjectSharedDeconstructionTarget(
        Algorithm.User helper,
        AssignmentDeconstructionTarget target,
        OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        var execution = new DeconstructionBindingExecution(
            target.Group,
            // The CALLER lexical scope resolves the hoisted `$deconstruct$` source, so the bind
            // is a function of it too. A structural scope identity (not the caller REFERENCE)
            // keeps the N targets of one group in one scope sharing a single bind — the
            // evaluator rebuilds that caller record for every demanded target — while separating
            // owners that resolve the same hoisted source differently.
            DeconstructionOwnerIdentity(ctx),
            ValueEnvironmentCacheIdentity(valEnv),
            ctx.AlgEnv,
            ctx.CountedParamEnv);

        var sharedR = ctx.DeconstructionBindingCache.GetOrBind(
            execution,
            () =>
            {
                var bindingsR = BindPatternedUserCall(helper, args, ctx, valEnv, calleeName);
                if (bindingsR.IsError)
                    return bindingsR.Error;

                // Materialize the shared bind as the bound values in TARGET order. Index the bind by
                // capture name and read the values out in the helper's parameter order (the written
                // target order): the front/collecting/back matcher may emit bindings in a different order
                // than the written targets (a movable collecting binding binds the fixed prefix and suffix before
                // the middle). The helper body is `Param(xi)`, which resolves xi from the counted
                // parameter environment first and the value environment second; deconstruction
                // captures populate the value bindings (the counted bindings stay empty), so seed the
                // index from the value bindings and let any counted binding win, matching that lookup
                // order exactly. The counted result then re-counts the value at the boundary and the
                // non-counted result is the value itself, so the value alone reproduces both without
                // the O(N) environment scan.
                var bindings = bindingsR.Value;
                var valueByName = new Dictionary<string, Result>(bindings.ValueBindings.Count, StringComparer.Ordinal);
                foreach (var (name, value) in bindings.ValueBindings)
                    valueByName[name] = value;
                foreach (var (name, counted) in bindings.CountedBindings)
                    valueByName[name] = counted.Value;

                var parameters = helper.Parameters;
                var projected = new Result[parameters.Count];
                for (var i = 0; i < parameters.Count; i++)
                {
                    if (!valueByName.TryGetValue(parameters[i].Name, out var value))
                        return new EvalError.UnknownName(parameters[i].Name);
                    projected[i] = value;
                }
                return EvalResult<IReadOnlyList<Result>>.Ok(projected);
            });

        if (sharedR.IsError)
            return sharedR.Error;

        var values = sharedR.Value;
        if ((uint)target.Index >= (uint)values.Count)
            return null;

        return EvalResult<Result>.Ok(values[target.Index]);
    }

    /// <summary>
    /// Shared call argument-slot assembly used by EVERY callable shape (flat
    /// fixed, flat/mixed variadic, patterned, and multi-clause conditional):
    /// each written argument slot is evaluated exactly once, left to right; every non-spread slot is
    /// reified as exactly ONE argument value (with its dual algorithm view
    /// where resolvable) whatever that value is — a scalar, a sequence, a list,
    /// <c>()</c>, or <c>[]</c> — and every explicit spread slot is expanded by
    /// exactly one value boundary into ordinary argument slots. VALUES STAY
    /// VALUES: this is the ONLY place a call turns one value into several
    /// supplied items, and it does so only for a written spread. The final
    /// argument supply is formed BEFORE any arity checking, clause selection,
    /// conditional dispatch, or pattern binding, and no binder reinterprets an
    /// item afterwards — the callee's internal representation never influences
    /// the meaning of caller-side spread.
    /// DOT-CALL PASSES A VALUE: an extension dot-call receiver reaches this
    /// assembly as the ordinary FIRST slot of <c>F(R, args)</c>
    /// (<see cref="BuildLexicalReceiverCallArgs"/>) — one reified value like
    /// any written argument, never a supply of its own; only a spread receiver
    /// <c>R*</c> (the fluent form lowers to <c>F(R*, args)</c>) opens one
    /// boundary, exactly as a written spread slot does.
    /// Lean: <c>collectVariadicCallItems</c>.
    /// </summary>
    private static EvalResult<IReadOnlyList<ParameterPatternInput>> BuildCallArgumentInputs(
        OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var maybeAlgsR = TryResolveArgAlgs(args, ctx);
        if (maybeAlgsR.IsError) return maybeAlgsR.Error;

        // Argument slots evaluate directly in the CALLER's context: the bundle
        // owns no scope, so there is no argument-level lexical frame to push.
        // (An argument frame would necessarily be empty and caller-wired, so
        // lookup behavior is identical to pushing one — none exists.)
        var maybeAlgs = maybeAlgsR.Value;
        var inputs = new List<ParameterPatternInput>();

        for (var index = 0; index < args.Count; index++)
        {
            var argExpr = args[index];
            var maybeAlg = index < maybeAlgs.Count ? maybeAlgs[index] : null;

            if (argExpr is Expr.SequenceSpread)
            {
                var suppliedR = EvalCounted(argExpr, ctx, valEnv);
                if (suppliedR.IsError)
                    return suppliedR.Error;

                // Explicit spread supplies the operand's items, one level.
                foreach (var value in CountedTopLevelValues(suppliedR.Value))
                    inputs.Add(new ParameterPatternInput(value, Algorithm: null, ValueError: null));

                continue;
            }

            // Every non-spread slot is evaluated at its VALUE boundary through the
            // ONE EvalCounted — a capture, a block, a name, a call, and a literal
            // alike. No callee shape receives a second, written-slot view of a
            // slot (PARENTHESES GROUP SYNTAX, September 2026: a patterned callee
            // opens the slot's value in GetSequenceValuePatternItems, never the
            // rows a group was written with).
            var evaluatedR = EvalCounted(argExpr, ctx, valEnv);
            if (evaluatedR.IsOk)
            {
                // A non-spread slot is exactly ONE item: its value, never opened.
                inputs.Add(new ParameterPatternInput(
                    evaluatedR.Value.Value,
                    maybeAlg,
                    ValueError: null)
                {
                    Source = argExpr,
                });
                continue;
            }

            if (maybeAlg is not null)
            {
                // The failure is RETAINED, not raised: an argument nobody demands is not an
                // error (`F(x, y) = x` called as `F(1, { })` is 1). The written expression
                // travels with it so the demand that does surface it can blame the argument.
                inputs.Add(new ParameterPatternInput(
                    Value: null,
                    maybeAlg,
                    evaluatedR.Error)
                {
                    Source = argExpr,
                });
                continue;
            }

            // No algorithm channel to defer behind: this slot can only fail the call, so
            // blame the written argument here (F5).
            return BlameWrittenArgumentSlot(argExpr, evaluatedR.Error);
        }

        return EvalResult<IReadOnlyList<ParameterPatternInput>>.Ok(inputs);
    }

    private static EvalError VariadicBindingArityMismatch(
        string? calleeName,
        int requiredNormalItemCount,
        int actualItemCount,
        CallableSignature? signature = null)
        => string.IsNullOrWhiteSpace(calleeName)
            ? new EvalError.ArityMismatch(requiredNormalItemCount, actualItemCount)
            : new EvalError.VariadicArityMismatch(calleeName, requiredNormalItemCount, actualItemCount)
            {
                Signature = signature,
            };


    /// <summary>
    /// True when a callable's top-level parameter list captures the supplied call
    /// argument supply: any top-level collecting capture, including a lone
    /// collecting binding <c>*name</c> and mixed fixed/collecting shapes such
    /// as <c>x, *y, z</c>.
    /// Checked only after patterned (sequence-value / repeated-name) binding has
    /// been ruled out.
    /// Lean: <c>Algorithm.usesItemSupplyBinding</c>.
    /// </summary>
    private static bool IsDeconstructionUserCallShape(CallableSignature signature)
        => signature.HasCollectingParameter;

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
    /// Binds a call to an item-supply parameter list (any top-level collecting parameter).
    /// The call argument supply is already the receiver for parameter binding:
    /// a plain sequence-valued argument contributes one item, while explicit
    /// spread contributes the operand's items.
    /// Lean: <c>bindDeconstructionUserCall</c>.
    /// </summary>
    private static EvalResult<UserCallBindings> BindDeconstructionUserCall(
        Algorithm callee,
        OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        var inputsR = BuildCallArgumentInputs(args, ctx, valEnv);
        if (inputsR.IsError) return inputsR.Error;

        // A deconstruction parameter list always carries a collecting binding, so a
        // too-few-items failure reports the fixed-binding minimum ("at least N")
        // rather than the exact-count wording used by strict callables.
        return BindParameterPatternList(
            callee.ParameterPatterns,
            inputsR.Value,
            ctx,
            allowAlgorithmBindings: true,
            (required, actual) =>
            {
                var renderedName = calleeName.Render(ctx);
                return VariadicBindingArityMismatch(
                    renderedName,
                    required,
                    actual,
                    CallableSignature.FromAlgorithm(renderedName, callee));
            });
    }

    /// <summary>
    /// The callee's three environments for a patterned or item-supply user call:
    /// the algorithm and counted tiers on the returned context, and the value
    /// tier as the returned environment. All THREE inherited tiers are shadowed
    /// by the callee's parameter names, so a parameter bound on only one channel
    /// can never be answered by a same-named binding inherited from the caller
    /// (see <see cref="ShadowInheritedParameterEnvironments"/> and
    /// <see cref="ShadowValEnv"/>); the callee's own bindings are prepended and
    /// win regardless. Shared by the synchronous path and its async twin, so the
    /// two cannot drift.
    /// Lean: <c>EvalCtx.bindParameters</c> inside <c>evalUserCallCounted</c>.
    /// </summary>
    private static UserCallEnvironments WithUserCallBindingEnvironments(
        EvalCtx ctx,
        UserCallBindings bindings,
        ValEnv valEnv,
        IReadOnlyList<string> shadowedNames)
    {
        var inherited = ShadowInheritedParameterEnvironments(ctx, shadowedNames);
        return new(
            inherited
                .WithAlgEnv(Concat(bindings.AlgorithmBindings, inherited.AlgEnv))
                .WithCountedParamEnv(Concat(bindings.CountedBindings, inherited.CountedParamEnv)),
            Concat(bindings.ValueBindings, ShadowValEnv(valEnv, shadowedNames)));
    }

    /// <summary>
    /// Callback-binding context (flat, patterned, collecting, and clause-family
    /// callbacks of the sequence builtins): the callee's counted bindings
    /// prepended to the inherited tiers shadowed by the callee's parameter
    /// names (<see cref="ShadowInheritedParameterEnvironments"/>). A callback
    /// parameter is bound on the counted channel only, so the algorithm tier
    /// must be shadowed here too — otherwise <c>[5].map(Inner)</c> with
    /// <c>Inner(f) = f(2)</c> would still invoke an enclosing callable <c>f</c>.
    /// Lean: <c>EvalCtx.bindParameters</c> at the callback sites of
    /// <c>evalResolvedCallbackCallCounted</c>.
    /// </summary>
    private static EvalCtx WithCountedParameterEnvironments(
        EvalCtx ctx,
        CountedParamEnv countedBindings,
        IReadOnlyList<string> shadowedNames)
    {
        var inherited = ShadowInheritedParameterEnvironments(ctx, shadowedNames);
        return inherited.WithCountedParamEnv(Concat(countedBindings, inherited.CountedParamEnv));
    }

    /// <summary>
    /// <see cref="WithCountedParameterEnvironments(EvalCtx, CountedParamEnv, IReadOnlyList{string})"/>
    /// for a lazily projected name sequence, materialized once so the tier shadowing
    /// scans a stable list instead of re-enumerating the projection.
    /// </summary>
    private static EvalCtx WithCountedParameterEnvironments(
        EvalCtx ctx,
        CountedParamEnv countedBindings,
        IEnumerable<string> shadowedNames)
        => WithCountedParameterEnvironments(ctx, countedBindings, shadowedNames.ToArray());

    internal static EvalError? RetainResourceLimitForAlgorithmBinding(EvalError? valueError)
        => valueError is { IsResourceLimit: true } ? valueError : null;

    private static EvalResult<UserCallEnvironments> BindFlatFixedUserCallArguments(
        Algorithm callee,
        CallDiagnosticName calleeName,
        IReadOnlyList<string> parameterNames,
        OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var paramCount = parameterNames.Count;

        // Shared argument-slot assembly (spread expansion happens there, before
        // any arity checking). Dot-call fixed receivers that must stay one
        // boundary are wrapped before this path, so they do not arrive here as
        // Expr.SequenceSpread.
        var inputsR = BuildCallArgumentInputs(args, ctx, valEnv);
        if (inputsR.IsError) return inputsR.Error;

        var slots = inputsR.Value
            .Select(static input => new FlatFixedCallSlot(input.Value, input.Algorithm, input.ValueError))
            .ToList();

        if (slots.Count > paramCount)
            return new EvalError.ArityMismatch(paramCount, slots.Count)
            {
                Signature = CallableSignature.FromAlgorithm(calleeName.Render(ctx), callee),
                InferredImplicitParameters = ImplicitParameterProvenance.CollectFrom(callee.Parameters),
            };

        var algBindings = new List<(string Name, Algorithm Value, EvalError? ValueError)>();
        var valueParams = new List<string>();
        var valueResults = new List<Result>();

        for (var i = 0; i < paramCount; i++)
        {
            if (i >= slots.Count)
            {
                valueParams.Add(parameterNames[i]);
                continue;
            }

            var slot = slots[i];
            if (slot.Algorithm is not null)
            {
                algBindings.Add((
                    parameterNames[i],
                    slot.Algorithm,
                    RetainResourceLimitForAlgorithmBinding(slot.ValueError)));
            }

            if (slot.Value is not null)
            {
                valueParams.Add(parameterNames[i]);
                valueResults.Add(slot.Value);
            }
        }

        var argEnvR = BindParams(valueParams, valueResults);
        if (argEnvR.IsError)
        {
            if (argEnvR.Error is EvalError.ArityMismatch arityMismatch)
                return arityMismatch with
                {
                    Signature = CallableSignature.FromAlgorithm(calleeName.Render(ctx), callee),
                    InferredImplicitParameters = ImplicitParameterProvenance.CollectFrom(callee.Parameters),
                };

            return argEnvR.Error;
        }

        var inherited = ShadowInheritedParameterEnvironments(ctx, parameterNames);
        var boundCtx = inherited.WithAlgEnv(Concat(algBindings, inherited.AlgEnv));
        var boundEnv = Concat(argEnvR.Value, ShadowValEnv(valEnv, parameterNames));
        return EvalResult<UserCallEnvironments>.Ok(new UserCallEnvironments(boundCtx, boundEnv));
    }
}
