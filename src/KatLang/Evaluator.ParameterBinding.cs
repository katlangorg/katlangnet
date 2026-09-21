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

    /// <summary>
    /// Argument passing rule: a single atom is wrapped in a one-element list;
    /// a sequence value is unpacked into its elements. Exact list values are
    /// NOT unpacked: call-argument binding preserves a list as one argument;
    /// only an explicit caller-site <c>spread</c> opens it. Lean: unpackArgs.
    /// </summary>
    private static IReadOnlyList<Result> UnpackArgs(Result r) => r switch
    {
        Result.Atom(var n) => [new Result.Atom(n)],
        Result.Str _ => [r],
        Result.Bool _ => [r],
        Result.SequenceValue(var items) => items,
        Result.ListValue _ => [r],
    };

    private readonly record struct VariadicCallItem(
        Result? Value,
        Algorithm? Algorithm,
        EvalError? ValueError,
        CountedResult? PreparedValue = null,
        Expr? Source = null);

    private readonly record struct ResolvedArgumentAlgorithm(
        Algorithm? Algorithm,
        bool SpreadsSequence)
    {
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
    /// One call argument slot prepared for parameter binding: its value view
    /// (<see cref="Value"/>), its algorithm view where resolvable, a retained
    /// value error, and — for patterned callees — the written item view of a
    /// group. Every slot is exactly ONE argument whatever spelling supplied it:
    /// a written argument, an explicit spread item, or an extension dot-call
    /// receiver (DOT-CALL PASSES A VALUE, September 2026: <c>R.F(args)</c>
    /// assembles exactly the slots of <c>F(R, args)</c>; no slot carries a raw
    /// supply of its own).
    /// Lean: <c>ParameterPatternInput</c>.
    /// </summary>
    private readonly record struct ParameterPatternInput(
        Result? Value,
        Algorithm? Algorithm,
        EvalError? ValueError,
        IReadOnlyList<Result>? ExplicitSequenceValueItems);

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
        // A nested written grouping level materializes exactly one item,
        // combined with the same shallow singleton-erasing rule as ordinary
        // capture evaluation (CombineOutputSlots). A singleton group such as
        // `(A)` IS its single already-evaluated item and an all-spread-empty
        // group is `()` — never a literal-unwritable orphan such as `(5)`.
        // Both node kinds keep this written-slot view: a capture body directly,
        // and a zero-parameter scoped block through its algorithm.
        if (expr is Expr.Capture(var captureBody))
        {
            var nestedItemsR = EvalExplicitSequenceValueRowSlots(captureBody, ctx, valEnv);
            if (nestedItemsR.IsError) return nestedItemsR.Error;

            return EvalResult<IReadOnlyList<Result>>.Ok([CombineOutputSlots(nestedItemsR.Value)]);
        }

        if (expr is Expr.AlgorithmExpr(var algorithm))
        {
            var wired = WireToCaller(ctx, algorithm);
            if (wired.ParameterCount == 0)
            {
                var nestedItemsR = EvalExplicitSequenceValueItems(wired, ctx, valEnv);
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

    private static EvalResult<IReadOnlyList<Result>> GetSequenceValuePatternItems(ParameterPatternInput input)
    {
        if (input.ExplicitSequenceValueItems is not null)
            return EvalResult<IReadOnlyList<Result>>.Ok(input.ExplicitSequenceValueItems);

        // A received sequence value or exact list value opens to its immediate
        // items (Lean: Result.structureItems?): the deconstruction receiver
        // opens ONE lone structure boundary of either kind, so
        // `x, y, z = [1, 2, 3]` binds like `x, y, z = [1, 2, 3]*`.
        if (input.Value?.StructureItems() is { } structureItems)
            return EvalResult<IReadOnlyList<Result>>.Ok(structureItems);

        return input.ValueError ?? new EvalError.BadArity();
    }

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
                        return input.ValueError ?? new EvalError.BadArity();

                    return EvalResult<UserCallBindings>.Ok(new UserCallBindings(valueBindings, [], algorithmBindings));
                }

            case CaptureParameterPattern { Kind: ParameterKind.Collecting }:
                return new EvalError.BadArity();

            case SequenceValueParameterPattern group:
                {
                    var itemsR = GetSequenceValuePatternItems(input);
                    // A non-grouped scalar value is a one-item supply for the
                    // prefix/collecting/suffix matcher (the same normalization the call-parameter
                    // deconstruction path applies via rule 4). This lets a scalar
                    // right-hand side bind a collecting pattern that captures zero items,
                    // e.g. `first, *tail = 1` (first = 1, tail = []), instead of being
                    // rejected before the matcher runs.
                    if (itemsR.IsError && input.Value is not null)
                    {
                        itemsR = EvalResult<IReadOnlyList<Result>>.Ok([input.Value]);
                    }

                    if (itemsR.IsError) return itemsR.Error;

                    var nestedInputs = itemsR.Value
                        .Select(static item => new ParameterPatternInput(item, Algorithm: null, ValueError: null, ExplicitSequenceValueItems: null))
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

    private static EvalResult<UserCallBindings> BindParameterPatternList(
        IReadOnlyList<ParameterPattern> patterns,
        IReadOnlyList<ParameterPatternInput> inputs,
        EvalCtx ctx,
        bool allowAlgorithmBindings,
        Func<int, int, EvalError> arityMismatch)
    {
        var collectingIndex = -1;
        for (var index = 0; index < patterns.Count; index++)
        {
            if (patterns[index] is not CaptureParameterPattern { Kind: ParameterKind.Collecting })
                continue;

            if (collectingIndex >= 0)
                return new EvalError.BadArity();

            collectingIndex = index;
        }

        var valueBindings = new List<(string Name, Result Value)>();
        var countedBindings = new List<(string Name, CountedResult Value)>();
        var algorithmBindings = new List<(string Name, Algorithm Value, EvalError? ValueError)>();
        // Running name -> value indexes over the accumulators. The prior implementation rebuilt a
        // name set and linear-scanned the accumulators on EVERY added binding, which is O(k) per
        // binding and O(patterns^2) across a whole pattern list — the residual quadratic in one
        // wide-deconstruction bind. These indexes keep the repeated-bind equality check (same name
        // must carry an equal value; unequal is an arity error) O(1) amortized without changing it.
        var valueBindingIndex = new Dictionary<string, Result>(StringComparer.Ordinal);
        var countedBindingIndex = new Dictionary<string, CountedResult>(StringComparer.Ordinal);

        EvalResult<bool> AddBindings(UserCallBindings bindings)
        {
            // The two name sets are only consulted by the algorithm-binding repeated-bind rule
            // below. Compute them (over the pre-add accumulator state) only when this binding set
            // actually carries algorithm bindings, so the common value/counted-only path — every
            // deconstruction capture — never pays for them.
            HashSet<string>? existingValueNames = null;
            HashSet<string>? incomingValueNames = null;
            if (bindings.AlgorithmBindings.Count > 0)
            {
                existingValueNames = valueBindingIndex.Keys.ToHashSet(StringComparer.Ordinal);
                incomingValueNames = bindings.ValueBindings
                    .Select(static binding => binding.Name)
                    .ToHashSet(StringComparer.Ordinal);
            }

            foreach (var binding in bindings.ValueBindings)
            {
                if (valueBindingIndex.TryGetValue(binding.Name, out var existing))
                {
                    if (!Result.ValueComparer.Equals(existing, binding.Value))
                        return new EvalError.BadArity();
                    continue;
                }

                valueBindings.Add(binding);
                valueBindingIndex[binding.Name] = binding.Value;
            }

            foreach (var binding in bindings.CountedBindings)
            {
                if (countedBindingIndex.TryGetValue(binding.Name, out var existing))
                {
                    if (!Result.ValueComparer.Equals(existing.Value, binding.Value.Value))
                        return new EvalError.BadArity();
                    continue;
                }

                countedBindings.Add(binding);
                countedBindingIndex[binding.Name] = binding.Value;
            }

            foreach (var binding in bindings.AlgorithmBindings)
            {
                var existingIndex = algorithmBindings.FindIndex(
                    existing => string.Equals(existing.Name, binding.Name, StringComparison.Ordinal));
                if (existingIndex < 0)
                {
                    algorithmBindings.Add(binding);
                    continue;
                }

                if (!existingValueNames!.Contains(binding.Name) || !incomingValueNames!.Contains(binding.Name))
                {
                    return new EvalError.TypeMismatch(
                        "Repeated bind equality is not supported for algorithm-only arguments");
                }
            }

            return EvalResult<bool>.Ok(true);
        }

        EvalResult<bool> BindOne(int patternIndex, int inputIndex)
        {
            var boundR = BindParameterPattern(patterns[patternIndex], inputs[inputIndex], ctx, allowAlgorithmBindings);
            if (boundR.IsError) return boundR.Error;

            return AddBindings(boundR.Value);
        }

        if (collectingIndex < 0)
        {
            if (patterns.Count != inputs.Count)
                return arityMismatch(patterns.Count, inputs.Count);

            for (var index = 0; index < patterns.Count; index++)
            {
                var boundR = BindOne(index, index);
                if (boundR.IsError) return boundR.Error;
            }

            return EvalResult<UserCallBindings>.Ok(new UserCallBindings(valueBindings, countedBindings, algorithmBindings));
        }

        var requiredCount = patterns.Count - 1;
        if (inputs.Count < requiredCount)
            return arityMismatch(requiredCount, inputs.Count);

        for (var index = 0; index < collectingIndex; index++)
        {
            var boundR = BindOne(index, index);
            if (boundR.IsError) return boundR.Error;
        }

        var suffixCount = patterns.Count - collectingIndex - 1;
        var suffixInputStart = inputs.Count - suffixCount;
        for (var suffixIndex = 0; suffixIndex < suffixCount; suffixIndex++)
        {
            var boundR = BindOne(collectingIndex + 1 + suffixIndex, suffixInputStart + suffixIndex);
            if (boundR.IsError) return boundR.Error;
        }

        var collectingCapture = (CaptureParameterPattern)patterns[collectingIndex];
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

                return input.ValueError ?? new EvalError.BadArity();
            }

            // Every slot allocated to the flat top-level collecting position
            // contributes its ONE reified value — a written argument, an
            // explicit spread item, and an extension dot-call receiver alike
            // (dot-call passes a value; only the spread marker opens one).
            // Nothing is opened here.
            capturedValues.Add(input.Value);
        }

        var captureR = CreateCollectingCapture(ctx, collectingCapture.Name, capturedValues, collectingCapture.Span);
        if (captureR.IsError) return captureR.Error;
        var capture = captureR.Value;
        var captureBindingsR = AddBindings(new UserCallBindings(
            [(capture.Name, capture.Value)],
            [(capture.Name, capture.CountedValue)],
            []));
        if (captureBindingsR.IsError) return captureBindingsR.Error;

        return EvalResult<UserCallBindings>.Ok(new UserCallBindings(valueBindings, countedBindings, algorithmBindings));
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

        var inputsR = BuildCallArgumentInputs(
            args,
            ctx,
            valEnv,
            includeExplicitSequenceValueItems: true);
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
    /// where resolvable), and every explicit spread slot is expanded by
    /// exactly one value boundary into ordinary argument slots. The final
    /// argument supply is formed BEFORE any arity checking, clause selection,
    /// conditional dispatch, or pattern binding — the callee's internal
    /// representation never influences the meaning of caller-side spread.
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
        ValEnv valEnv,
        bool includeExplicitSequenceValueItems = false)
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

                foreach (var value in CountedTopLevelValues(suppliedR.Value))
                    inputs.Add(new ParameterPatternInput(value, Algorithm: null, ValueError: null, ExplicitSequenceValueItems: null));

                continue;
            }

            var preparedR = PrepareCallArgumentEvaluation(
                argExpr,
                ctx,
                valEnv,
                includeExplicitSequenceValueItems);
            if (preparedR.IsOk)
            {
                inputs.Add(new ParameterPatternInput(
                    preparedR.Value.Counted.Value,
                    maybeAlg,
                    ValueError: null,
                    preparedR.Value.ExplicitSequenceValueItems));
                continue;
            }

            if (maybeAlg is not null)
            {
                inputs.Add(new ParameterPatternInput(Value: null, maybeAlg, preparedR.Error, ExplicitSequenceValueItems: null));
                continue;
            }

            return preparedR.Error;
        }

        return EvalResult<IReadOnlyList<ParameterPatternInput>>.Ok(inputs);
    }

    /// <summary>
    /// Evaluates one non-expanded call argument at its VALUE boundary (every non-spread
    /// slot — written argument or extension dot-call receiver alike — reifies to exactly
    /// one value). Patterned calls need an additional written-slot
    /// view for a capture or a zero-parameter AlgorithmExpr; that view is captured by the
    /// corresponding prepared-output evaluator during the SAME output pass that constructs the
    /// counted argument value. Multi-parameter algorithms stay on the ordinary dual-channel
    /// fallback and are never forced merely to request explicit pattern items.
    /// Lean: <c>evalVariadicCallItemPrepared</c>.
    /// </summary>
    private static EvalResult<PreparedCallArgumentEvaluation> PrepareCallArgumentEvaluation(
        Expr argExpr,
        EvalCtx ctx,
        ValEnv valEnv,
        bool includeExplicitSequenceValueItems)
    {
        if (includeExplicitSequenceValueItems && argExpr is Expr.Capture(var captureBody))
        {
            // The caller context owns the value evaluation and its
            // explicit-slot view (argument bundles have no scope of their own).
            var captureSpan = PreferExpressionSpan(argExpr.Span, captureBody);
            var capturePreparedR = WithSpan(captureSpan, EvalCapturePreparedCore(captureBody, ctx, valEnv));
            if (capturePreparedR.IsError) return capturePreparedR.Error;

            return EvalResult<PreparedCallArgumentEvaluation>.Ok(new(
                ReCountValueBoundary(capturePreparedR.Value.Counted),
                capturePreparedR.Value.OutputSlots));
        }

        if (includeExplicitSequenceValueItems && argExpr is Expr.AlgorithmExpr(var algorithm))
        {
            var wired = WireToCaller(ctx, algorithm);
            if (wired.ParameterCount == 0)
            {
                var blockSpan = PreferExpressionSpan(argExpr.Span, wired.Output);
                var preparedR = WithSpan(blockSpan, EvalAlgOutputPreparedCore(wired, ctx, valEnv));
                if (preparedR.IsError) return preparedR.Error;

                return EvalResult<PreparedCallArgumentEvaluation>.Ok(new(
                    ReCountValueBoundary(preparedR.Value.Counted),
                    preparedR.Value.OutputSlots));
            }
        }

        var evaluatedR = EvalCounted(argExpr, ctx, valEnv);
        return evaluatedR.IsError
            ? evaluatedR.Error
            : EvalResult<PreparedCallArgumentEvaluation>.Ok(new(evaluatedR.Value, null));
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
