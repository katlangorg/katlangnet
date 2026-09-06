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
/// Builtins: collection materialization budget, value-boundary re-counting, the zero-argument property cache, sequence join/spread evaluation, sequence-builtin argument binding, the collection builtins, and resolved builtin dispatch (the "Collection materialization budget" section).
/// Part of the <see cref="Evaluator"/> partial class; the central state, lookup and open resolution,
/// the built-in prelude, and the run entry points remain in <c>Evaluator.cs</c>.
/// </summary>
public static partial class Evaluator
{
    // ── Collection materialization budget ────────────────────────────────────

    /// <summary>
    /// RESERVES <paramref name="itemCount"/> item slots for a persistent collection that
    /// is about to be created. Every caller must reserve BEFORE allocating: a rejected
    /// request must never materialize the collection it is rejecting.
    /// </summary>
    private static EvalError? ReserveCollection(EvalCtx ctx, long itemCount, SourceSpan? span = null)
        => ctx.Budget.TryReserveCollection(itemCount) is { } error
            ? AtSpanIfMissing(error, span)
            : null;

    /// <summary>
    /// Charged form of <see cref="MakeCollectionListResult(IEnumerable{Result})"/>: the
    /// item count is already known, so the reservation happens before the exact list is
    /// built. Collection-producing builtins charge their TRUE output count here rather
    /// than an upper bound, so a cumulative budget is never over-charged.
    /// </summary>
    /// <summary>
    /// Sequence CAPTURE reserves only when a sequence value is actually created: ordinary
    /// construction erases singleton and empty structure (`(x)` is `x`, `()` stores no item
    /// slots), so fewer than two slots materialize no collection and cost nothing. Exact
    /// lists are different — `[x]` really does store one slot — and use
    /// <see cref="ReserveCollection"/> directly.
    /// </summary>
    private static EvalError? ReserveSequenceCapture(EvalCtx ctx, int slotCount, SourceSpan? span = null)
        => slotCount >= 2 ? ReserveCollection(ctx, slotCount, span) : null;

    /// <summary>
    /// Canonically captures an item supply after reserving only the slots that the
    /// resulting persistent sequence actually stores. Empty capture stores no item
    /// slots, singleton capture returns the existing child value, and two or more
    /// items create and charge one sequence value.
    /// </summary>
    private static EvalResult<Result> MakeCheckedSequenceCapture(
        EvalCtx ctx,
        IReadOnlyList<Result> items,
        SourceSpan? span = null)
        => ReserveSequenceCapture(ctx, items.Count, span) is { } error
            ? error
            : EvalResult<Result>.Ok(CombineOutputSlots(items));

    internal static EvalResult<CountedResult> MakeCheckedLoopStateResult(
        EvalCtx ctx,
        IReadOnlyList<Result> stateSlots,
        SourceSpan? span = null)
    {
        var valueR = MakeCheckedSequenceCapture(ctx, stateSlots, span);
        return valueR.IsError
            ? valueR.Error
            : EvalResult<CountedResult>.Ok(new CountedResult(valueR.Value, stateSlots.Count));
    }

    private static EvalResult<CountedResult> MakeCollectionListResult(
        EvalCtx ctx,
        IReadOnlyList<Result> items,
        SourceSpan? span = null)
        => ReserveCollection(ctx, items.Count, span) is { } error
            ? error
            : EvalResult<CountedResult>.Ok(MakeCollectionListResult(items));

    /// <summary>
    /// <c>atoms</c> result construction. Unlike every other collection builtin its output
    /// is not bounded by its input's item count, so the traversal itself is bounded and
    /// abandoned as soon as it passes the limit — no oversized intermediate is ever built,
    /// and no unbounded counting prepass is needed.
    /// </summary>
    private static EvalResult<CountedResult> MakeLanguageAtomsResult(
        EvalCtx ctx,
        Result value,
        SourceSpan? span = null)
    {
        var limit = ctx.Budget.MaxCollectionItems;
        if (!value.TryLanguageAtoms(limit, out var atoms))
            return AtSpanIfMissing(new EvalError.CollectionSizeLimitExceeded(limit, limit + 1L), span);

        return MakeCollectionListResult(ctx, atoms.Select(static n => (Result)new Result.Atom(n)).ToList(), span);
    }

    /// <summary>
    /// <c>range(start, stop)</c> result construction. The cardinality is computed from the
    /// bounds WITHOUT enumerating, so an oversized request is rejected before a single item
    /// is allocated — this is the path that made <c>range(1, 10000000)</c> a process risk.
    /// </summary>
    private static EvalResult<Result> BuildInclusiveRangeChecked(
        EvalCtx ctx,
        InclusiveRange range,
        SourceSpan? span = null)
        => ReserveCollection(ctx, CountInclusiveRangeValues(range), span) is { } error
            ? error
            : EvalResult<Result>.Ok(BuildInclusiveRange(range));

    // Re-count a counted result at a public property/call/builtin RESULT boundary.
    // A property/call boundary always returns ONE value: the body may internally
    // produce an item supply of count 0, 1, or many, but the caller observes the
    // same structural value with emitted count <see cref="Result.ValueCount"/>
    // (0 for the empty sequence value, otherwise 1). A multi-output body therefore
    // becomes one sequence value at the boundary; only an explicit caller-site
    // `spread` re-spreads it (via ToItems, which reads the value, not this count).
    //
    // This re-counts without normalizing or rebuilding the value; ordinary value
    // construction has already canonicalized redundant unary empty structure.
    // It is applied only to public result boundaries, never to internal
    // body/root output accumulation (EvalAlgOutputCountedCore) or to multi-slot
    // while/repeat loop state, both of which must keep their multi-item counts.
    // (Collecting bindings need no re-count: CollectSegment stores one exact list with
    // emitted count 1.) Lexical zero-arg property access (EvalCounted
    // Expr.Resolve) and the `if` builtin already perform this same re-count
    // inline; this helper generalizes it.
    // Lean: reCountValueBoundary.
    private static CountedResult ReCountValueBoundary(CountedResult r)
        => new(r.Value, r.Value.ValueCount());

    // Re-count a successful counted result at a public boundary, propagating errors
    // unchanged. Convenience overload for the call/access dispatch sites.
    private static EvalResult<CountedResult> ReCountValueBoundary(EvalResult<CountedResult> r)
        => r.IsError ? r.Error : EvalResult<CountedResult>.Ok(ReCountValueBoundary(r.Value));

    /// <summary>
    /// The ONE value-projection helper for plain results over counted
    /// evaluation: discards only the emitted-count metadata, propagating
    /// values and errors unchanged. Every plain twin of a counted family is
    /// expressed through this projection (mirroring Lean, where each plain
    /// evaluator returns <c>Prod.fst</c> of its counted twin), so plain and
    /// counted semantics cannot drift.
    /// </summary>
    private static EvalResult<Result> ProjectCountedValue(EvalResult<CountedResult> counted)
        => counted.IsError
            ? counted.Error
            : EvalResult<Result>.Ok(counted.Value.Value);

    private static EvalResult<CountedResult> EvalAlgOutputCounted(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => EvalAlgOutputCountedCore(alg, ctx, valEnv);

    private static EvalResult<CountedResult> EvalProgramOutputCounted(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => EvalAlgOutputCountedCore(alg, ctx, valEnv);

    // No builtin is valid as a bare zero-argument value; every builtin requires
    // a call. (The empty sequence value is written `()`, not a builtin.)
    private static EvalResult<CountedResult> EvalBuiltinValueCounted(BuiltinId builtin)
        => WrongBuiltinArity(builtin, 0);

    private static EvalResult<ZeroArgPropertyResult> EvaluateZeroArgPropertyResult(
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var countedR = EvalAlgOutputCounted(resolvedAlgorithm, ctx, valEnv);
        if (countedR.IsError)
            return countedR.Error;

        return EvalResult<ZeroArgPropertyResult>.Ok(
            new ZeroArgPropertyResult(countedR.Value.Value, countedR.Value.EmittedCount));
    }

    /// <summary>
    /// Charged dynamic invocation boundary, entered BEFORE the cache is consulted so
    /// that recursive property access (<c>A = A</c>) is bounded by depth. A cache HIT
    /// charges exactly this one access step and never re-charges the cached
    /// computation; a MISS additionally charges everything its body evaluates. The
    /// level is entered through the shared <see cref="TryEnterDynamicInvocation"/> helper
    /// and released by its <see cref="BudgetLevel"/> — the planned loop temp read
    /// (<c>LoopExprPlan.TempSlot</c>) enters the same one, so the two strategies' charges
    /// cannot drift (see <c>Evaluator.BudgetScopes.cs</c>).
    /// </summary>
    private static EvalResult<ZeroArgPropertyResult> GetOrEvaluateZeroArgPropertyResult(
        Algorithm? owner,
        Property binding,
        ZeroArgPropertyAccessKind accessKind,
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (TryEnterDynamicInvocation(ctx, binding.DeclarationSpans.FirstOrDefault(), out var level) is { } limitError)
            return limitError;

        using (level)
        {
            return GetOrEvaluateZeroArgPropertyResultCore(owner, binding, accessKind, resolvedAlgorithm, ctx, valEnv);
        }
    }

    private static EvalResult<ZeroArgPropertyResult> GetOrEvaluateZeroArgPropertyResultCore(
        Algorithm? owner,
        Property binding,
        ZeroArgPropertyAccessKind accessKind,
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (owner is null)
            return EvaluateZeroArgPropertyResult(resolvedAlgorithm, ctx, valEnv);

        return ctx.ZeroArgPropertyResultCache.GetOrEvaluate(
            new ZeroArgPropertyExecution(
                owner,
                binding,
                accessKind,
                ValueEnvironmentCacheIdentity(valEnv),
                ctx.AlgEnv,
                ctx.CountedParamEnv,
                // The budget is created fresh per run (CreateRootCtx) and threaded by
                // reference through every derived ctx, so it is the run identity:
                // entries can never be served across runs even when a host shares
                // one cache instance between runs.
                ctx.Budget),
            () => EvaluateZeroArgPropertyResult(resolvedAlgorithm, ctx, valEnv));
    }

    private static EvalResult<CountedResult> EvalZeroArgPropertyAccessCounted(
        Algorithm? owner,
        Property binding,
        ZeroArgPropertyAccessKind accessKind,
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var propertyR = GetOrEvaluateZeroArgPropertyResult(owner, binding, accessKind, resolvedAlgorithm, ctx, valEnv);
        return propertyR.IsError
            ? propertyR.Error
            : EvalResult<CountedResult>.Ok(new CountedResult(propertyR.Value.Value, propertyR.Value.EmittedCount));
    }

    private static EvalResult<CountedResult> EvalZeroArgPropertyAccessCounted(
        ResolvedLexicalProperty resolvedProperty,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => EvalZeroArgPropertyAccessCounted(
            resolvedProperty.Owner,
            resolvedProperty.Binding,
            ZeroArgPropertyAccessKind.CountedLexical,
            resolvedProperty.ResolvedAlgorithm,
            ctx,
            valEnv);

    private static EvalResult<CountedResult> EvalConditionalCallbackCallCounted(
        Algorithm callee,
        IReadOnlyList<CountedResult> explicitArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
    {
        if (callee.HasDuplicateBranchPatterns())
            return new EvalError.DuplicateBranchPattern();

        var match = MatchCountedCallBranches(callee.Branches, explicitArgs);
        if (match is null)
            return new EvalError.NoMatchingBranch(calleeName);

        var (branch, bindings) = match.Value;
        var wiredBody = ChildOf(callee, SelectedBranchBody(branch));
        var newCtx = WithCountedParameterEnvironments(
            ctx.Push(callee),
            bindings,
            bindings.Select(static binding => binding.Item1));
        var newEnv = Concat(bindings.Select(static binding => (binding.Item1, binding.Item2.Value)).ToList(), valEnv);
        return EvalAlgOutputCounted(wiredBody, newCtx, newEnv);
    }

    private static bool ReducerAccumulatorSideHasTopLevelCollecting(Algorithm.User reducer)
    {
        try
        {
            var signature = CallableSignature.FromUserAlgorithm("reduce step", reducer);
            var plan = CallableBindingPlan.FromSignature(signature);
            return plan.TopLevelPatternList.Nodes
                .Skip(1)
                .Any(static node => node is CollectingCaptureBindingNode { IsTopLevel: true });
        }
        catch (InvalidOperationException)
        {
            return false;
        }
    }

    private static EvalResult<CountedResult> EvalReducerAccumulatorCollectingCallbackCallCounted(
        Algorithm.User callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // Charged dynamic invocation boundary. This reducer shape is dispatched INSTEAD
        // of EvalResolvedCallbackCallCounted, never in addition to it, so charging here
        // keeps one reduce step at exactly one charged invocation.
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return limitError;

        try
        {
            return EvalReducerAccumulatorCollectingCallbackCallCountedCore(callee, args, ctx, valEnv);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    private static EvalResult<CountedResult> EvalReducerAccumulatorCollectingCallbackCallCountedCore(
        Algorithm.User callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (callee.Output.Count == 0)
            return new EvalError.MissingOutput();

        var countedPatternEnvR = BindCountedParameterPatternList(
            callee.ParameterPatterns,
            args,
            ctx,
            (required, actual) => new EvalError.ArityMismatch(required, actual));
        if (countedPatternEnvR.IsError)
            return AttachImplicitParameterProvenance(countedPatternEnvR.Error, callee);

        var patternBindings = countedPatternEnvR.Value;
        var callbackCtx = WithCountedParameterEnvironments(
            ctx,
            patternBindings.CountedBindings,
            patternBindings.CountedBindings.Select(static binding => binding.Item1));
        return EvalAlgOutputCounted(callee, callbackCtx, valEnv);
    }

    /// <summary>
    /// Evaluate a <c>reduce</c> step on one collected iteration item. Reducers
    /// with a top-level collecting accumulator parameter bind accumulator state
    /// slots like loop state; other reducers keep ordinary structural
    /// accumulator binding.
    /// </summary>
    private static EvalResult<CountedResult> EvalSequenceReduceStepCounted(
        Algorithm callee,
        CountedResult element,
        Result accumulator,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
    {
        var elementArg = CountedSequenceCallbackItem(element);
        if (callee is Algorithm.User userReducer && ReducerAccumulatorSideHasTopLevelCollecting(userReducer))
        {
            var accumulatorSlots = accumulator.ToItems();
            var args = new List<CountedResult>(1 + accumulatorSlots.Count) { elementArg };
            foreach (var slot in accumulatorSlots)
                args.Add(new CountedResult(slot, slot.ValueCount()));

            return EvalReducerAccumulatorCollectingCallbackCallCounted(userReducer, args, ctx, valEnv);
        }

        return EvalResolvedCallbackCallCounted(
            callee,
            [elementArg, new CountedResult(accumulator, accumulator.ValueCount())],
            ctx,
            valEnv,
            calleeName);
    }

    /// <summary>
    /// Recover the top-level values emitted at one algorithm boundary from a
    /// counted result.
    /// A sequence value emitted as one top-level result stays intact, while a
    /// multi-output result is expanded back to its top-level items.
    /// </summary>
    private static List<Result> CountedTopLevelValues(CountedResult output)
    {
        var items = new List<Result>();
        AddCountedTopLevelValues(items, output);
        return items;
    }

    private static void AddCountedTopLevelValues(List<Result> into, CountedResult output)
    {
        if (output.EmittedCount == 0)
            return;

        if (output.EmittedCount == 1)
        {
            into.Add(output.Value);
            return;
        }

        ResultItems(into, output.Value);
    }

    private static List<Expr> SequenceConstructLeaves(Expr expr)
    {
        var leaves = new List<Expr>();
        var stack = new Stack<Expr>();
        stack.Push(expr);

        while (stack.Count != 0)
        {
            var current = stack.Pop();
            if (current is Expr.SequenceConstruct(var left, var right))
            {
                stack.Push(right);
                stack.Push(left);
                continue;
            }

            leaves.Add(current);
        }

        return leaves;
    }

    /// <summary>
    /// Evaluate the INTERNAL <see cref="Expr.SequenceConstruct"/> join node as
    /// one sequence value. Join semantics, not written-parentheses semantics:
    /// a non-spread leaf whose value is <c>()</c> contributes NO item (an
    /// empty join contribution), a spread leaf splices its operand's items,
    /// and the result is recursively normalized. Written parentheses parse to
    /// <see cref="Expr.Capture"/> and always keep a non-spread <c>()</c> item
    /// visible — surface syntax must never route through this node
    /// (enforced by <c>SequenceConstructContainmentTests</c>).
    /// Lean: <c>evalSequenceConstructCounted</c>; plain evaluation is this
    /// function's value projection on both sides.
    /// </summary>
    private static EvalResult<CountedResult> EvalSequenceConstructCounted(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var leaves = SequenceConstructLeaves(expr);
        var items = new List<Result>(leaves.Count);

        foreach (var leaf in leaves)
        {
            if (leaf is Expr.SequenceSpread)
            {
                var suppliedItemsR = EvalSequenceSpreadOperandItems(leaf, ctx, valEnv);
                if (suppliedItemsR.IsError) return suppliedItemsR.Error;

                items.AddRange(suppliedItemsR.Value);
                continue;
            }

            var valueR = Eval(leaf, ctx, valEnv);
            if (valueR.IsError) return valueR.Error;

            if (valueR.Value.ValueCount() != 0)
                items.Add(valueR.Value);
        }

        if (ReserveSequenceCapture(ctx, items.Count) is { } sequenceLimitError)
            return sequenceLimitError;

        var value = CombineOutputSlots(items);
        return EvalResult<CountedResult>.Ok(new CountedResult(
            value,
            value.ValueCount()));
    }

    private static EvalError SpreadMissingOutput(SourceSpan? span)
        => new EvalError.SpreadMissingOutput() { Span = span };

    private static bool IsMissingOutputError(EvalError error) => error switch
    {
        EvalError.MissingOutput => true,
        EvalError.WithContext(_, var inner) => IsMissingOutputError(inner),
        _ => false,
    };

    private static EvalResult<IReadOnlyList<Result>> EvalSequenceSpreadOperandItems(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (expr is Expr.Capture(var captureBody))
        {
            var captureSpan = PreferExpressionSpan(expr.Span, captureBody);
            var captureR = WithSpan(captureSpan, EvalCaptureValue(captureBody, ctx, valEnv));
            if (captureR.IsError)
                return IsMissingOutputError(captureR.Error)
                    ? SpreadMissingOutput(captureSpan)
                    : captureR.Error;

            return EvalResult<IReadOnlyList<Result>>.Ok(captureR.Value.SpreadItems());
        }

        if (expr is Expr.AlgorithmExpr(var alg))
        {
            var wired = WireToCaller(ctx, alg);
            var blockSpan = PreferExpressionSpan(expr.Span, wired.Output);
            if (wired.Params.Count != 0)
                return MissingImplicitArguments<IReadOnlyList<Result>>(wired, blockSpan);

            var blockR = EvalAlgOutput(wired, ctx, valEnv);
            if (blockR.IsError)
                return IsMissingOutputError(blockR.Error)
                    ? SpreadMissingOutput(blockSpan)
                    : blockR.Error;

            return EvalResult<IReadOnlyList<Result>>.Ok(blockR.Value.SpreadItems());
        }

        var outputR = Eval(expr, ctx, valEnv);
        if (outputR.IsError)
            return IsMissingOutputError(outputR.Error)
                ? SpreadMissingOutput(expr.Span)
                : outputR.Error;

        return EvalResult<IReadOnlyList<Result>>.Ok(outputR.Value.SpreadItems());
    }

    // Evaluate a unary `sequenceSpread` node by evaluating its single operand
    // once and spreading immediate top-level items. Directly-nested spreads
    // (`A**`) are unwrapped iteratively (stack-safe for deep nesting) and
    // then each written layer is applied COMPOSITIONALLY: every spread layer
    // opens exactly one boundary of the value the previous layer would have
    // captured, so `A**` agrees with `(A*)*`. For sequence values the extra
    // layers are fixed points (value-equivalent to a single spread); a
    // singleton-list chain opens one list boundary per layer (`[[7]]**`
    // supplies `7`), while a multi-element list re-captures as a sequence
    // after the first layer and then stays fixed (`[[1, 2], [3, 4]]**`
    // supplies the two inner lists unchanged).
    // Lean: evalSequenceSpreadCounted.
    private static EvalResult<CountedResult> EvalSequenceSpreadCounted(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var operand = expr;
        var layers = 0;
        while (operand is Expr.SequenceSpread(var supplied))
        {
            operand = supplied;
            layers++;
        }

        var operandR = EvalSequenceSpreadOperandItems(operand, ctx, valEnv);
        if (operandR.IsError) return operandR.Error;

        var items = operandR.Value;
        for (var layer = 0; layer < layers; layer++)
        {
            var capturedR = MakeCheckedSequenceCapture(ctx, items, expr.Span);
            if (capturedR.IsError) return capturedR.Error;

            if (layer == layers - 1)
                return EvalResult<CountedResult>.Ok(new CountedResult(capturedR.Value, items.Count));

            items = capturedR.Value.SpreadItems();
        }

        throw new InvalidOperationException("Sequence spread must contain at least one layer.");
    }

    private readonly record struct BoundSequenceBuiltinArguments(
        PreparedSequenceBuiltinInput PreparedInput,
        IReadOnlyList<CountedResult> IterationItems,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> SuffixArgs);

    private static EvalResult<IReadOnlyList<VariadicCallItem>> BuildCallableCallItems(
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var items = new List<VariadicCallItem>();
        foreach (var resolvedArg in args)
        {
            var arg = resolvedArg.Algorithm;

            // A callback/function argument (one that declares parameters) is applied
            // per element by the consuming sequence builtin, never used as a value
            // here. Its parameters are unbound at this collection point, so evaluating
            // its body standalone would resolve those parameter names against the
            // surrounding scope. When a sibling argument shares a parameter name and
            // was deferred as a self-referential thunk, that stray lookup re-enters the
            // same builtin call and recurses without ever settling on a value. Keep the
            // algorithm unevaluated so it can be applied with bound parameters later;
            // only value-shaped arguments (no parameters) are materialized eagerly.
            if (arg is not null && (arg.Params.Count > 0 || arg.ParameterPatterns.Count > 0))
            {
                items.Add(new VariadicCallItem(
                    Value: null,
                    arg,
                    ValueError: null,
                    resolvedArg.PreparedValue));
                continue;
            }

            // A prepared argument (a dotted receiver or builtin callback value) already
            // holds its counted value and must not be recomputed: re-evaluating the reified
            // value would repeat every allocation and charged unit the first evaluation paid.
            var outputR = resolvedArg.PreparedValue is { } prepared
                ? EvalResult<CountedResult>.Ok(prepared)
                : arg is { } algorithm
                    ? EvalArgumentAlgOutputCounted(algorithm, ctx, valEnv)
                    : EvalResult<CountedResult>.Err(new EvalError.BadArity());
            if (outputR.IsOk)
            {
                if (resolvedArg.SpreadsSequence)
                {
                    foreach (var value in CountedTopLevelValues(outputR.Value))
                    {
                        items.Add(new VariadicCallItem(
                            value,
                            arg,
                            ValueError: null,
                            new CountedResult(value, 1)));
                    }
                }
                else
                {
                    items.Add(new VariadicCallItem(
                        outputR.Value.Value,
                        arg,
                        ValueError: null,
                        outputR.Value));
                }

                continue;
            }

            items.Add(new VariadicCallItem(Value: null, arg, outputR.Error));
        }

        return EvalResult<IReadOnlyList<VariadicCallItem>>.Ok(items);
    }

    private static EvalResult<PreparedSequenceBuiltinSuffixArg> PrepareSequenceBuiltinSuffixArg(
        BuiltinId builtin,
        SequenceBuiltinSuffixArgDescriptor descriptor,
        VariadicCallItem item,
        EvalCtx ctx)
    {
        switch (descriptor.Kind)
        {
            case SequenceBuiltinSuffixArgKind.Algorithm:
                {
                    // A resource-limit failure from the slot's eager value evaluation is
                    // STICKY: the limit is a property of the run, and falling through to
                    // the algorithm channel would re-run the same body — each active
                    // level retrying once turns a failing self-referential argument
                    // (`A = xs.reduce(F, A)`) into work exponential in the depth limit.
                    // Non-limit value errors keep the legacy fall-through, which is what
                    // lets a genuine callback reference reach the algorithm channel.
                    if (item.ValueError is { IsResourceLimit: true } stickyLimit)
                        return stickyLimit;

                    var algorithm = item.Algorithm
                        ?? (item.PreparedValue is { } prepared
                            ? CountedArgAlgorithm(prepared, ctx)
                            : null);
                    if (algorithm is not null)
                    {
                        return EvalResult<PreparedSequenceBuiltinSuffixArg>.Ok(
                            new PreparedSequenceBuiltinSuffixArg.AlgorithmArg(
                                NormalizeSequenceCallableSuffixAlgorithm(algorithm, ctx))
                            {
                                PreparedValue = item.PreparedValue,
                            });
                    }

                    return item.ValueError ?? new EvalError.WithContext(
                        SequenceBuiltinSuffixArgErrorContext(builtin, descriptor),
                        new EvalError.BadArity());
                }

            case SequenceBuiltinSuffixArgKind.Value:
                if (item.Value is not null)
                {
                    return EvalResult<PreparedSequenceBuiltinSuffixArg>.Ok(
                        new PreparedSequenceBuiltinSuffixArg.ValueArg(item.Value));
                }

                return item.ValueError ?? new EvalError.WithContext(
                    SequenceBuiltinSuffixArgErrorContext(builtin, descriptor),
                    new EvalError.BadArity());

            case SequenceBuiltinSuffixArgKind.WholeNumber:
                {
                    if (item.Value is null)
                        return item.ValueError ?? new EvalError.WithContext(
                            SequenceBuiltinSuffixArgErrorContext(builtin, descriptor),
                            new EvalError.BadArity());

                    var numeric = item.Value.SingleAtomicNumber();
                    if (numeric is null || !Decimal128.IsInteger(numeric.Value))
                    {
                        return new EvalError.WithContext(
                            SequenceBuiltinSuffixArgErrorContext(builtin, descriptor),
                            new EvalError.BadArity());
                    }

                    return EvalResult<PreparedSequenceBuiltinSuffixArg>.Ok(
                        new PreparedSequenceBuiltinSuffixArg.WholeNumberArg(numeric.Value));
                }

            default:
                return InternalSequenceBuiltinSuffixArgMetadataError<PreparedSequenceBuiltinSuffixArg>(
                    builtin,
                    "used an unknown suffix-argument kind");
        }
    }

    private static Algorithm NormalizeSequenceCallableSuffixAlgorithm(Algorithm algorithm, EvalCtx ctx)
    {
        if (algorithm is Algorithm.User { Params.Count: 0, Output.Count: 1 } user
            && user.Output[0] is Expr.Resolve(var name) resolve)
        {
            var resolvedR = ResolveNamedAlgorithm(name, resolve.Span, ctx);
            if (resolvedR.IsOk)
                return resolvedR.Value;
        }

        return algorithm;
    }

    private static EvalResult<CollectedSequenceBuiltinInput> ApplySequenceBuiltinEmptyPolicy(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        CollectedSequenceBuiltinInput collected)
    {
        return metadata.EmptyPolicy switch
        {
            SequenceBuiltinEmptyPolicy.AllowEmpty => EvalResult<CollectedSequenceBuiltinInput>.Ok(collected),
            SequenceBuiltinEmptyPolicy.RequireAnyItem when collected.TotalItemCount == 0 => new EvalError.WithContext(
                $"{BuiltinDisplayName(builtin)} requires a non-empty collection",
                new EvalError.BadArity()),
            SequenceBuiltinEmptyPolicy.RequireEachInputNonEmpty when collected.AnyInputEmpty => new EvalError.WithContext(
                $"{BuiltinDisplayName(builtin)} requires each input collection to be non-empty",
                new EvalError.BadArity()),
            _ => EvalResult<CollectedSequenceBuiltinInput>.Ok(collected),
        };
    }

    private static string DescribeSequenceItem(Result item) => item switch
    {
        Result.Atom(var n) => $"numeric value {n.ToString(System.Globalization.CultureInfo.InvariantCulture)}",
        Result.Str(var s) => $"string value {Rendering.DiagnosticValueRenderer.RenderDoubleQuotedString(s)}",
        Result.SequenceValue(var items) when items.Count == 0 => "empty sequence value",
        Result.SequenceValue => "sequence value",
        Result.ListValue(var items) when items.Count == 0 => "empty list value",
        Result.ListValue => "list value",
        _ => "value",
    };

    private static string NumericSequenceItemErrorContext(BuiltinId builtin, int index, Result item)
        => $"{BuiltinDisplayName(builtin)} expects each collection element to be a single numeric value; item {index} was {DescribeSequenceItem(item)}";

    private static EvalError ReduceInitialAccumulatorRequiresValueError(Algorithm initialAlg)
        => new EvalError.WithContext(
            new ReduceInitialAccumulatorContext(initialAlg.Params.ToList()),
            new EvalError.BadArity());

    private static bool IsLikelyUnevaluatedParameterError(Algorithm algorithm, EvalError error)
    {
        if (algorithm.Params.Count == 0)
            return false;

        var parameterNames = algorithm.Params.ToHashSet(StringComparer.Ordinal);
        return ErrorReferencesAnyName(error, parameterNames);
    }

    private static bool ErrorReferencesAnyName(EvalError error, IReadOnlySet<string> names)
        => error switch
        {
            EvalError.UnknownName(var name) => names.Contains(name),
            EvalError.UnresolvedImplicitParams(var paramNames) => paramNames.Any(names.Contains),
            EvalError.WithContext(_, var inner) => ErrorReferencesAnyName(inner, names),
            _ => false,
        };

    /// <summary>
    /// Evaluate <c>reduce(collection, reducer, initial)</c> while
    /// preserving the accumulator's emitted-value count for the empty-sequence
    /// case. The fixed <c>collection</c> argument supplies the items through
    /// the post-binding collection view; the reducer and initial accumulator
    /// are fixed control arguments.
    /// The current item is passed to the reducer exactly as collected;
    /// nested sequence values stay intact.
    /// Normal accumulator parameters keep ordinary structural semantics; a
    /// top-level collecting accumulator parameter receives accumulator state
    /// slots.
    /// Lean: <c>evalReduceCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalReduceCounted(
        IReadOnlyList<CountedResult> items,
        Algorithm stepAlg,
        Algorithm initialAlg,
        CountedResult? preparedInitial,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // The initial accumulator is a written value slot: when call-item assembly
        // already evaluated it (a value-shaped argument), that result IS the slot's
        // value — evaluating the algorithm channel again would run the body twice.
        var initialR = preparedInitial is { } preparedValue
            ? EvalResult<CountedResult>.Ok(preparedValue)
            : EvalArgumentAlgOutputCounted(initialAlg, ctx, valEnv);
        if (initialR.IsError)
        {
            if (IsLikelyUnevaluatedParameterError(initialAlg, initialR.Error))
                return ReduceInitialAccumulatorRequiresValueError(initialAlg);

            return initialR.Error;
        }

        // The initial accumulator expression occupies ONE written accumulator
        // slot: its result is reified as one persistent value at the ordinary
        // value boundary (ReCountValueBoundary) BEFORE reduction begins, so an
        // initial expression that emitted multiple items cannot leak that
        // supply through the empty-collection return.
        var accumulator = ReCountValueBoundary(initialR.Value);
        foreach (var item in items)
        {
            var stepR = WithCtx(
                "while evaluating reduce step (reduce passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list, nested sequence and list values stay intact, and top-level collecting accumulator parameters receive state slots)",
                EvalSequenceReduceStepCounted(stepAlg, item, accumulator.Value, ctx, valEnv, "reduce step"));
            if (stepR.IsError) return stepR.Error;

            var nextR = ExpectSingleAccumulator(stepR.Value);
            if (nextR.IsError) return nextR.Error;

            accumulator = new CountedResult(nextR.Value, 1);
        }

        return EvalResult<CountedResult>.Ok(accumulator);
    }

    /// <summary>
    /// Evaluate <c>filter(collection, predicate)</c>. The fixed
    /// <c>collection</c> argument supplies the items through the post-binding
    /// collection view, and <c>predicate</c> is a fixed control argument.
    /// Each iterated item is passed to the predicate exactly as collected;
    /// nested sequence values and nested list values stay intact.
    /// The kept items remain the original collection items and are
    /// materialized as one exact immutable list value.
    /// </summary>
    private static EvalResult<CountedResult> EvalFilterCounted(
        IReadOnlyList<CountedResult> items,
        Algorithm predicateAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var kept = new List<Result>();
        for (var index = 0; index < items.Count; index++)
        {
            var item = items[index];
            var truthR = EvalFilterPredicateTruth(predicateAlg, item, index, ctx, valEnv);
            if (truthR.IsError)
                return truthR.Error;

            if (truthR.Value)
                kept.Add(item.Value);
        }

        return MakeCollectionListResult(ctx, kept);
    }

    /// <summary>
    /// Evaluate a filter predicate with the same callback and truthiness rules
    /// used by generic <c>filter</c>; sequence optimizers call this to avoid
    /// duplicating callback semantics.
    /// </summary>
    internal static EvalResult<bool> EvalFilterPredicateTruth(
        Algorithm predicateAlg,
        CountedResult item,
        int index,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var predicateR = WithFilterItemCtx(
            item.Value,
            index,
            ctx,
            EvalSequenceCallbackCall(predicateAlg, item, ctx, valEnv, "filter predicate"));
        if (predicateR.IsError)
            return predicateR.Error;

        var truth = predicateR.Value.SingleAtomicTruthValue();
        if (truth is null)
        {
            return new EvalError.WithContext(
                "filter predicate must return exactly one atomic numeric value",
                new EvalError.BadArity());
        }

        return EvalResult<bool>.Ok(truth.Value);
    }

    /// <summary>
    /// Evaluate <c>map(collection, mapper)</c> while preserving the number of
    /// top-level mapped elements. <c>mapper</c> is a fixed control argument.
    /// Each callback item is passed to the mapper exactly as collected from
    /// the post-binding collection view; nested sequence values and
    /// nested list values stay intact. Each captured callback result becomes
    /// one element of the exact immutable list result (mapped elements are
    /// never flattened into the outer list).
    /// Lean: <c>evalMapCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalMapCounted(
        IReadOnlyList<CountedResult> items,
        Algorithm transformAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var mapped = new List<Result>(items.Count);
        foreach (var item in items)
        {
            var transformR = WithCtx(
                "while evaluating map transform (map passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)",
                EvalSequenceCallbackCallCounted(transformAlg, item, ctx, valEnv, "map transform"));
            if (transformR.IsError) return transformR.Error;

            var mappedElementR = ExpectSingleMappedElement(transformR.Value);
            if (mappedElementR.IsError) return mappedElementR.Error;

            mapped.Add(mappedElementR.Value);
        }

        return MakeCollectionListResult(ctx, mapped);
    }

    /// <summary>
    /// Collect top-level sequence items as single atomic numeric values.
    /// Used by numeric ordering and aggregation builtins that only accept
    /// clearly comparable numeric elements and reject strings or sequence values.
    /// Diagnostics include the 0-based item index after counted top-level
    /// extraction so numeric shape failures are easier to debug.
    /// </summary>
    private static EvalResult<List<Decimal128>> CollectSingleAtomicNumbers(
        BuiltinId builtin,
        IReadOnlyList<Result> elements)
    {
        var numbers = new List<Decimal128>(elements.Count);
        for (var index = 0; index < elements.Count; index++)
        {
            var item = elements[index];
            var numeric = item.SingleAtomicNumber();
            if (numeric is null)
            {
                return new EvalError.WithContext(
                    NumericSequenceItemErrorContext(builtin, index, item),
                    new EvalError.BadArity());
            }

            numbers.Add(numeric.Value);
        }

        return EvalResult<List<Decimal128>>.Ok(numbers);
    }

    private static EvalResult<PreparedSequenceBuiltinInput> PrepareSequenceBuiltinInput(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        CollectedSequenceBuiltinInput collected)
    {
        var validatedItemsR = ApplySequenceBuiltinEmptyPolicy(builtin, metadata, collected);
        if (validatedItemsR.IsError) return validatedItemsR.Error;

        IReadOnlyList<Decimal128>? numericItems = null;
        switch (metadata.ItemShapeConstraint)
        {
            case SequenceBuiltinItemShapeConstraint.Any:
                break;

            case SequenceBuiltinItemShapeConstraint.SingleNumeric:
                {
                    var numbersR = CollectSingleAtomicNumbers(builtin, validatedItemsR.Value.FlattenedItems);
                    if (numbersR.IsError) return numbersR.Error;
                    numericItems = numbersR.Value;
                    break;
                }
        }

        return EvalResult<PreparedSequenceBuiltinInput>.Ok(
            new PreparedSequenceBuiltinInput(validatedItemsR.Value, numericItems));
    }

    private static string DescribeSequenceBuiltinSuffixArgRequirement(
        SequenceBuiltinSuffixArgKind kind)
        => kind switch
        {
            SequenceBuiltinSuffixArgKind.Algorithm => "an algorithm",
            SequenceBuiltinSuffixArgKind.Value => "exactly one value",
            SequenceBuiltinSuffixArgKind.WholeNumber => "exactly one whole-number value",
            _ => "a valid suffix argument",
        };

    private static string DescribeSequenceBuiltinSuffixArgKind(
        SequenceBuiltinSuffixArgKind kind)
        => kind switch
        {
            SequenceBuiltinSuffixArgKind.Algorithm => "algorithm",
            SequenceBuiltinSuffixArgKind.Value => "value",
            SequenceBuiltinSuffixArgKind.WholeNumber => "whole-number value",
            _ => "unknown",
        };

    private static string SequenceBuiltinSuffixArgErrorContext(
        BuiltinId builtin,
        SequenceBuiltinSuffixArgDescriptor descriptor)
        => $"{BuiltinDisplayName(builtin)} {descriptor.Name} must be {DescribeSequenceBuiltinSuffixArgRequirement(descriptor.Kind)}";

    private static EvalResult<T> InternalSequenceBuiltinSuffixArgMetadataError<T>(
        BuiltinId builtin,
        string detail)
        => new EvalError.WithContext(
            $"internal sequence metadata for {BuiltinDisplayName(builtin)} {detail}",
            new EvalError.BadArity());

    private static EvalResult<BoundSequenceBuiltinArguments> BindSequenceBuiltinArguments(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var descriptor = BuiltinRegistry.GetBuiltin(builtin);
        var signature = descriptor.PlainSignature;
        var itemsR = BuildCallableCallItems(args, ctx, valEnv);
        if (itemsR.IsError) return itemsR.Error;

        // A collection builtin is an ordinary fixed-arity callable: exactly one
        // collection argument followed by its fixed control arguments
        // (`count(collection)`, `take(collection, count)`,
        // `map(collection, mapper)`). An unspread sequence or list value is ONE
        // argument at this call boundary, exactly like at every other call
        // boundary; only explicit caller-site spread alters argument
        // boundaries, and the spread items obey the same fixed arity
        // (`count([1, 2, 3]*)` supplies three arguments and is an arity
        // error). Nothing is opened before binding.
        var items = itemsR.Value;
        var expectedArgCount = 1 + metadata.SuffixArgs.Count;
        if (items.Count != expectedArgCount)
        {
            return new EvalError.ArityMismatch(expectedArgCount, items.Count)
            {
                Signature = signature,
            };
        }

        var collectionItem = items[0];
        if (collectionItem.Value is null)
            return collectionItem.ValueError ?? new EvalError.BadArity();

        // The one-level builtin collection view applies AFTER binding, to the
        // bound collection value only: a lone sequence or exact list value
        // opens to its immediate items, and any other value is a one-element
        // collection (`count(7)` is 1). Opening is never recursive — nested
        // sequence/list elements stay intact as single items.
        var collectionValues = BuiltinCollectionItems(collectionItem.Value);

        var collected = new CollectedSequenceBuiltinInput([collectionValues], collectionValues);
        var preparedInputR = PrepareSequenceBuiltinInput(builtin, metadata, collected);
        if (preparedInputR.IsError) return preparedInputR.Error;

        var suffixArgs = new List<PreparedSequenceBuiltinSuffixArg>(metadata.SuffixArgs.Count);
        for (var index = 0; index < metadata.SuffixArgs.Count; index++)
        {
            var preparedArgR = PrepareSequenceBuiltinSuffixArg(
                builtin,
                metadata.SuffixArgs[index],
                items[1 + index],
                ctx);
            if (preparedArgR.IsError) return preparedArgR.Error;

            suffixArgs.Add(preparedArgR.Value);
        }

        var iterationItems = collectionValues
            .Select(static value => new CountedResult(value, 1))
            .ToList();

        return EvalResult<BoundSequenceBuiltinArguments>.Ok(
            new BoundSequenceBuiltinArguments(preparedInputR.Value, iterationItems, suffixArgs));
    }

    private static EvalResult<T> ExpectPreparedSequenceBuiltinSuffixArgAt<T>(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> args,
        int index,
        SequenceBuiltinSuffixArgKind expectedKind,
        Func<SequenceBuiltinSuffixArgDescriptor, PreparedSequenceBuiltinSuffixArg, EvalResult<T>> projector)
    {
        if (descriptors.Count != args.Count)
        {
            return InternalSequenceBuiltinSuffixArgMetadataError<T>(
                builtin,
                "mismatched suffix arguments");
        }

        if ((uint)index >= (uint)descriptors.Count)
        {
            return InternalSequenceBuiltinSuffixArgMetadataError<T>(
                builtin,
                $"expected suffix argument {index + 1} to have metadata kind {DescribeSequenceBuiltinSuffixArgKind(expectedKind)}");
        }

        var descriptor = descriptors[index];
        if (descriptor.Kind != expectedKind)
        {
            return InternalSequenceBuiltinSuffixArgMetadataError<T>(
                builtin,
                $"expected suffix argument {index + 1} ({descriptor.Name}) to have metadata kind {DescribeSequenceBuiltinSuffixArgKind(expectedKind)}, but found {DescribeSequenceBuiltinSuffixArgKind(descriptor.Kind)}");
        }

        return projector(descriptor, args[index]);
    }

    private static EvalResult<Algorithm> ExpectPreparedAlgorithmSuffixArg(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> args,
        int index)
    {
        var argR = ExpectPreparedAlgorithmSuffixArgFull(builtin, descriptors, args, index);
        return argR.IsError
            ? argR.Error
            : EvalResult<Algorithm>.Ok(argR.Value.AlgorithmValue);
    }

    private static EvalResult<PreparedSequenceBuiltinSuffixArg.AlgorithmArg> ExpectPreparedAlgorithmSuffixArgFull(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> args,
        int index)
        => ExpectPreparedSequenceBuiltinSuffixArgAt(
            builtin,
            descriptors,
            args,
            index,
            SequenceBuiltinSuffixArgKind.Algorithm,
            (descriptor, arg) => arg is PreparedSequenceBuiltinSuffixArg.AlgorithmArg algorithmArg
                ? EvalResult<PreparedSequenceBuiltinSuffixArg.AlgorithmArg>.Ok(algorithmArg)
                : InternalSequenceBuiltinSuffixArgMetadataError<PreparedSequenceBuiltinSuffixArg.AlgorithmArg>(
                    builtin,
                    $"prepared suffix argument {index + 1} ({descriptor.Name}) did not match metadata kind {DescribeSequenceBuiltinSuffixArgKind(SequenceBuiltinSuffixArgKind.Algorithm)}"));

    private static EvalResult<Decimal128> ExpectPreparedWholeNumberSuffixArg(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> args,
        int index)
        => ExpectPreparedSequenceBuiltinSuffixArgAt(
            builtin,
            descriptors,
            args,
            index,
            SequenceBuiltinSuffixArgKind.WholeNumber,
            (descriptor, arg) => arg is PreparedSequenceBuiltinSuffixArg.WholeNumberArg(var value)
                ? EvalResult<Decimal128>.Ok(value)
                : InternalSequenceBuiltinSuffixArgMetadataError<Decimal128>(
                    builtin,
                    $"prepared suffix argument {index + 1} ({descriptor.Name}) did not match metadata kind {DescribeSequenceBuiltinSuffixArgKind(SequenceBuiltinSuffixArgKind.WholeNumber)}"));

    private static EvalResult<Result> ExpectPreparedValueSuffixArg(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> args,
        int index)
        => ExpectPreparedSequenceBuiltinSuffixArgAt(
            builtin,
            descriptors,
            args,
            index,
            SequenceBuiltinSuffixArgKind.Value,
            (descriptor, arg) => arg is PreparedSequenceBuiltinSuffixArg.ValueArg(var value)
                ? EvalResult<Result>.Ok(value)
                : InternalSequenceBuiltinSuffixArgMetadataError<Result>(
                    builtin,
                    $"prepared suffix argument {index + 1} ({descriptor.Name}) did not match metadata kind {DescribeSequenceBuiltinSuffixArgKind(SequenceBuiltinSuffixArgKind.Value)}"));

    private static EvalResult<IReadOnlyList<Decimal128>> ExpectPreparedNumericItems(
        BuiltinId builtin,
        PreparedSequenceBuiltinInput prepared)
    {
        if (prepared.NumericItems is { } numbers)
            return EvalResult<IReadOnlyList<Decimal128>>.Ok(numbers);

        return new EvalError.WithContext(
            $"internal sequence metadata for {BuiltinDisplayName(builtin)} did not produce numeric items",
            new EvalError.BadArity());
    }

    /// <summary>
    /// Evaluate <c>order(collection)</c> by eagerly sorting the top-level numeric
    /// collection items in ascending order and materializing them as one exact
    /// immutable list value.
    /// Duplicates are preserved, sequence values are not flattened, strings are
    /// rejected, and empty collections yield the empty list <c>[]</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalOrderCounted(
        EvalCtx ctx,
        IReadOnlyList<Decimal128> numbers)
    {
        // Decimal128.CompareTo is a total order over every value, including the IEEE
        // specials: NaN sorts before every other value (mirroring double), the
        // infinities take the extremes, and -0 compares equal to 0.
        var sorted = numbers.ToList();
        sorted.Sort();
        return MakeCollectionListResult(ctx, sorted.Select(static value => (Result)new Result.Atom(value)).ToList());
    }

    /// <summary>
    /// Evaluate <c>orderDesc(collection)</c> by eagerly sorting the top-level
    /// numeric collection items in descending order and materializing them as
    /// one exact immutable list value.
    /// Duplicates are preserved, sequence values are not flattened, strings are
    /// rejected, and empty collections yield the empty list <c>[]</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalOrderDescCounted(
        EvalCtx ctx,
        IReadOnlyList<Decimal128> numbers)
    {
        var sorted = numbers.ToList();
        sorted.Sort(static (left, right) => right.CompareTo(left));
        return MakeCollectionListResult(ctx, sorted.Select(static value => (Result)new Result.Atom(value)).ToList());
    }

    /// <summary>
    /// Evaluate <c>count(collection)</c> by counting the top-level sequence
    /// elements from left to right.
    /// Each atom, string, or sequence value counts as one top-level element;
    /// sequence values are not flattened or inspected recursively, and empty collections
    /// return <c>0</c>.
    /// Lean: <c>evalCountCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalCountCounted(
        IReadOnlyList<Result> items)
        => EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(items.Count), 1));

    /// <summary>
    /// Evaluate <c>contains(collection, item)</c> by checking whether any
    /// extracted top-level item equals the searched suffix item under ordinary
    /// KatLang value semantics.
    /// Search is top-level only: sequence values compare structurally as single
    /// items and are not searched recursively.
    /// </summary>
    private static EvalResult<CountedResult> EvalContainsCounted(
        IReadOnlyList<Result> items,
        Result searchedItem)
        => EvalResult<CountedResult>.Ok(new CountedResult(
            new Result.Atom(items.Any(item => Result.ValueComparer.Equals(item, searchedItem)) ? 1 : 0),
            1));

    /// <summary>
    /// Evaluate <c>distinct(collection)</c> by removing later duplicate top-level
    /// items while preserving the original order of first occurrence, then
    /// materializing the kept items as one exact immutable list value.
    /// Duplicate detection follows KatLang value
    /// semantics, so atoms compare by numeric value, strings by exact string
    /// value, and sequence/list values structurally by their elements.
    /// </summary>
    private static EvalResult<CountedResult> EvalDistinctCounted(
        EvalCtx ctx,
        IReadOnlyList<Result> items)
    {
        var distinctItems = new List<Result>(items.Count);
        var seen = new HashSet<Result>(Result.ValueComparer);
        foreach (var item in items)
        {
            if (seen.Add(item))
                distinctItems.Add(item);
        }

        return MakeCollectionListResult(ctx, distinctItems);
    }

    /// <summary>
    /// Evaluate <c>first(collection)</c> by returning the first top-level
    /// collection element unchanged.
    /// Atoms, strings, and sequence values each count as one top-level element;
    /// sequence values are preserved whole, and the collection must be non-empty.
    /// </summary>
    private static EvalResult<CountedResult> EvalFirstCounted(
        IReadOnlyList<Result> items)
    {
        if (items.Count == 0)
            return new EvalError.BadArity();

        return EvalResult<CountedResult>.Ok(new CountedResult(items[0], 1));
    }

    /// <summary>
    /// Evaluate <c>last(collection)</c> by returning the last top-level
    /// collection element unchanged.
    /// Atoms, strings, and sequence values each count as one top-level element;
    /// sequence values are preserved whole, and the collection must be non-empty.
    /// </summary>
    private static EvalResult<CountedResult> EvalLastCounted(
        IReadOnlyList<Result> items)
    {
        if (items.Count == 0)
            return new EvalError.BadArity();

        return EvalResult<CountedResult>.Ok(new CountedResult(items[^1], 1));
    }

    /// <summary>
    /// Evaluate <c>take(collection, count)</c> by returning the first
    /// <paramref name="count"/> extracted top-level items as one exact
    /// immutable list value. <paramref name="count"/> is a suffix parameter.
    /// Non-positive counts return the empty list <c>[]</c>, oversized counts
    /// return all items, nested sequence/list values stay intact as exact
    /// elements, and original order is preserved.
    /// </summary>
    private static EvalResult<CountedResult> EvalTakeCounted(
        EvalCtx ctx,
        IReadOnlyList<Result> items,
        Decimal128 count)
    {
        // Saturate before narrowing: `count` is a validated whole number that may
        // exceed int.MaxValue, and an oversized count means "all items" by
        // specification, so it must never reach the host (int) conversion.
        IReadOnlyList<Result> taken = count <= 0
            ? []
            : items.Take(count >= items.Count ? items.Count : (int)count).ToList();

        return MakeCollectionListResult(ctx, taken);
    }

    /// <summary>
    /// Evaluate <c>skip(collection, count)</c> by returning the extracted
    /// top-level items after the first <paramref name="count"/> items as one
    /// exact immutable list value.
    /// <paramref name="count"/> is a suffix parameter. Non-positive counts keep
    /// all items, oversized counts return the empty list <c>[]</c>, nested
    /// sequence/list values stay intact as exact elements, and original order
    /// is preserved.
    /// </summary>
    private static EvalResult<CountedResult> EvalSkipCounted(
        EvalCtx ctx,
        IReadOnlyList<Result> items,
        Decimal128 count)
    {
        // Saturate before narrowing, mirroring EvalTakeCounted: an oversized count
        // means "skip everything" and must never reach the host (int) conversion.
        IReadOnlyList<Result> remaining = count <= 0
            ? items.ToList()
            : items.Skip(count >= items.Count ? items.Count : (int)count).ToList();

        return MakeCollectionListResult(ctx, remaining);
    }

    /// <summary>
    /// Evaluate <c>min(collection)</c> by comparing top-level sequence elements
    /// from left to right and returning the smallest numeric element.
    /// The collection must be non-empty, and each top-level element must be
    /// exactly one atomic numeric value; sequence values are not flattened and strings
    /// are rejected.
    /// Lean: <c>evalMinCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalMinCounted(
        IReadOnlyList<Decimal128> numbers)
    {
        if (numbers.Count == 0)
            return new EvalError.BadArity();

        // Decimal128.Min propagates NaN (any NaN element makes the result NaN),
        // so the outcome never depends on where in the collection a NaN sits —
        // a bare `<` scan would be order-dependent because every IEEE comparison
        // against NaN is false.
        var minimum = numbers[0];
        for (var i = 1; i < numbers.Count; i++)
            minimum = Decimal128.Min(numbers[i], minimum);

        return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(minimum), 1));
    }

    /// <summary>
    /// Evaluate <c>max(collection)</c> by comparing top-level sequence elements
    /// from left to right and returning the largest numeric element.
    /// The collection must be non-empty, and each top-level element must be
    /// exactly one atomic numeric value; sequence values are not flattened and strings
    /// are rejected.
    /// Lean: <c>evalMaxCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalMaxCounted(
        IReadOnlyList<Decimal128> numbers)
    {
        if (numbers.Count == 0)
            return new EvalError.BadArity();

        // NaN-propagating for the same reason as EvalMinCounted.
        var maximum = numbers[0];
        for (var i = 1; i < numbers.Count; i++)
            maximum = Decimal128.Max(numbers[i], maximum);

        return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(maximum), 1));
    }

    /// <summary>
    /// Evaluate <c>sum(collection)</c> by adding the top-level sequence elements
    /// from left to right.
    /// Each element must be exactly one atomic numeric value; sequence values are not
    /// flattened, strings are rejected, and empty collections return <c>0</c>.
    /// Implementation note: Lean <c>Int</c> is unbounded; the Decimal128 runtime
    /// follows IEEE 754 — an accumulation past the representable range saturates
    /// to an infinity instead of raising an error.
    /// Lean: <c>evalSumCounted</c>.
    /// </summary>
    private static Decimal128 SumNumbers(IReadOnlyList<Decimal128> numbers)
    {
        Decimal128 total = Decimal128.Zero;
        foreach (var numeric in numbers)
            total += numeric;

        return total;
    }

    /// <summary>
    /// Evaluate <c>sum(collection)</c> by adding the prepared numeric elements
    /// from left to right.
    /// Lean: <c>evalSumCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalSumCounted(IReadOnlyList<Decimal128> numbers)
        => EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(SumNumbers(numbers)), 1));

    /// <summary>
    /// Evaluate <c>avg(collection)</c> by averaging the top-level sequence
    /// elements from left to right.
    /// The collection must be non-empty, and each top-level element must be
    /// exactly one atomic numeric value; sequence values are not flattened and strings
    /// are rejected.
    /// The Decimal128 runtime returns the true arithmetic mean (total / count),
    /// correctly rounded to 34 significant digits. Lean's Int-only core
    /// approximates this with truncation toward zero (Int.tdiv); that integer
    /// approximation is a Lean model limitation, not the C# runtime contract.
    /// Lean: <c>evalAvgCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalAvgCounted(IReadOnlyList<Decimal128> numbers)
    {
        if (numbers.Count == 0)
            return new EvalError.BadArity();

        var total = SumNumbers(numbers);
        // Preserve the ordinary left-to-right IEEE result, including explicit
        // NaN/infinity inputs. Only an overflow created from entirely finite inputs
        // needs the exact fallback: a finite arithmetic mean is bounded by its
        // extrema and therefore remains representable even when the intermediate
        // sum is not (MaxValue averaged with itself is the simplest case).
        var average = Decimal128.IsFinite(total)
            || numbers.Any(static number => !Decimal128.IsFinite(number))
            ? total / numbers.Count
            : AverageFiniteNumbersExactly(numbers);

        return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(average), 1));
    }

    /// <summary>
    /// Computes the correctly rounded arithmetic mean of finite Decimal128 values
    /// without a Decimal128-sized intermediate sum. Every finite Decimal128 is an
    /// integer coefficient times a power-of-ten quantum, so a BigInteger sum at the
    /// smallest input quantum is exact. The final rational division is rounded once,
    /// using IEEE round-to-nearest/ties-to-even, to either 34 significant digits or
    /// the Decimal128 subnormal quantum floor.
    /// </summary>
    private static Decimal128 AverageFiniteNumbersExactly(IReadOnlyList<Decimal128> numbers)
    {
        var coefficientsByExponent = new Dictionary<int, BigInteger>();
        var minimumExponent = int.MaxValue;

        foreach (var number in numbers)
        {
            if (number == Decimal128.Zero)
                continue;

            var quantum = Decimal128.GetQuantum(number);
            var exponent = Decimal128.ILogB(quantum);
            var coefficient = BigInteger.CreateChecked((Int128)(number / quantum));
            coefficientsByExponent[exponent] = coefficientsByExponent.TryGetValue(exponent, out var existing)
                ? existing + coefficient
                : coefficient;
            if (exponent < minimumExponent)
                minimumExponent = exponent;
        }

        if (coefficientsByExponent.Count == 0)
            return Decimal128.Zero;

        var exactScaledSum = BigInteger.Zero;
        foreach (var (exponent, coefficient) in coefficientsByExponent)
        {
            if (!coefficient.IsZero)
                exactScaledSum += coefficient * BigInteger.Pow(10, exponent - minimumExponent);
        }

        if (exactScaledSum.IsZero)
            return Decimal128.Zero;

        return RoundScaledRationalToDecimal128(exactScaledSum, numbers.Count, minimumExponent);
    }

    /// <summary>
    /// Rounds <paramref name="scaledNumerator"/> / <paramref name="denominator"/>
    /// times 10^<paramref name="decimalScale"/> directly into Decimal128.
    /// </summary>
    private static Decimal128 RoundScaledRationalToDecimal128(
        BigInteger scaledNumerator,
        int denominator,
        int decimalScale)
    {
        const int DecimalPrecision = 34;
        const int MinimumQuantumExponent = -6176;

        var negative = scaledNumerator.Sign < 0;
        var magnitude = BigInteger.Abs(scaledNumerator);
        var numeratorDigits = magnitude.ToString(System.Globalization.CultureInfo.InvariantCulture).Length;

        // Division by the positive item count can lower the scientific exponent by
        // only a handful of places. Start at the numerator's exponent and compare
        // exactly, avoiding a binary floating-point logarithm in this numeric path.
        var scientificExponent = numeratorDigits - 1 + decimalScale;
        while (!ScaledRatioIsAtLeastPowerOfTen(
                   magnitude,
                   denominator,
                   decimalScale,
                   scientificExponent))
        {
            scientificExponent--;
        }

        var precisionQuantumExponent = scientificExponent - (DecimalPrecision - 1);
        var targetQuantumExponent = precisionQuantumExponent < MinimumQuantumExponent
            ? MinimumQuantumExponent
            : precisionQuantumExponent;

        var scaleShift = decimalScale - targetQuantumExponent;
        BigInteger quotient;
        BigInteger remainder;
        BigInteger roundingDenominator;
        if (scaleShift >= 0)
        {
            var roundingNumerator = magnitude * BigInteger.Pow(10, scaleShift);
            quotient = BigInteger.DivRem(roundingNumerator, denominator, out remainder);
            roundingDenominator = denominator;
        }
        else
        {
            roundingDenominator = denominator * BigInteger.Pow(10, -scaleShift);
            quotient = BigInteger.DivRem(magnitude, roundingDenominator, out remainder);
        }

        var doubledRemainder = remainder << 1;
        if (doubledRemainder > roundingDenominator
            || (doubledRemainder == roundingDenominator && !quotient.IsEven))
        {
            quotient++;
        }

        if (quotient.IsZero)
            return negative ? Decimal128.NegativeZero : Decimal128.Zero;

        var tenToPrecision = BigInteger.Pow(10, DecimalPrecision);
        if (quotient == tenToPrecision)
        {
            quotient /= 10;
            targetQuantumExponent++;
        }

        var result = Decimal128.ScaleB((Decimal128)(Int128)quotient, targetQuantumExponent);
        return negative ? -result : result;
    }

    private static bool ScaledRatioIsAtLeastPowerOfTen(
        BigInteger magnitude,
        int denominator,
        int decimalScale,
        int power)
    {
        var shift = decimalScale - power;
        return shift >= 0
            ? magnitude * BigInteger.Pow(10, shift) >= denominator
            : magnitude >= denominator * BigInteger.Pow(10, -shift);
    }

    private static EvalResult<CountedResult> ApplyBuiltinCountedSequence(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var boundR = BindSequenceBuiltinArguments(builtin, metadata, args, ctx, valEnv);
        if (boundR.IsError) return boundR.Error;

        var bound = boundR.Value;

        EvalResult<CountedResult> WithPreparedFlatItems(
            Func<IReadOnlyList<Result>, EvalResult<CountedResult>> handler)
            => handler(bound.PreparedInput.FlattenedItems);

        EvalResult<CountedResult> WithPreparedNumericItems(
            Func<IReadOnlyList<Decimal128>, EvalResult<CountedResult>> handler)
        {
            var numbersR = ExpectPreparedNumericItems(builtin, bound.PreparedInput);
            if (numbersR.IsError) return numbersR.Error;

            return handler(numbersR.Value);
        }

        EvalResult<CountedResult> WithPreparedSuffixArgs(
            Func<IReadOnlyList<PreparedSequenceBuiltinSuffixArg>, EvalResult<CountedResult>> handler)
            => handler(bound.SuffixArgs);

        return builtin switch
        {
            BuiltinId.@filter => WithPreparedSuffixArgs(
                    preparedSuffixArgs =>
                    {
                        var predicateR = ExpectPreparedAlgorithmSuffixArg(
                            builtin,
                            metadata.SuffixArgs,
                            preparedSuffixArgs,
                            0);
                        if (predicateR.IsError) return predicateR.Error;

                        return EvalFilterCounted(bound.IterationItems, predicateR.Value, ctx, valEnv);
                    }),
            BuiltinId.@map => WithPreparedSuffixArgs(
                    preparedSuffixArgs =>
                    {
                        var transformR = ExpectPreparedAlgorithmSuffixArg(
                            builtin,
                            metadata.SuffixArgs,
                            preparedSuffixArgs,
                            0);
                        if (transformR.IsError) return transformR.Error;

                        return EvalMapCounted(bound.IterationItems, transformR.Value, ctx, valEnv);
                    }),
            BuiltinId.@order => WithPreparedNumericItems(numbers => EvalOrderCounted(ctx, numbers)),
            BuiltinId.@orderDesc => WithPreparedNumericItems(numbers => EvalOrderDescCounted(ctx, numbers)),
            BuiltinId.@count => WithPreparedFlatItems(EvalCountCounted),
            BuiltinId.@contains => WithPreparedSuffixArgs(
                    preparedSuffixArgs =>
                    {
                        var searchedItemR = ExpectPreparedValueSuffixArg(
                            builtin,
                            metadata.SuffixArgs,
                            preparedSuffixArgs,
                            0);
                        if (searchedItemR.IsError) return searchedItemR.Error;

                        return WithPreparedFlatItems(items => EvalContainsCounted(items, searchedItemR.Value));
                    }),
            BuiltinId.@distinct => WithPreparedFlatItems(items => EvalDistinctCounted(ctx, items)),
            BuiltinId.@first => WithPreparedFlatItems(EvalFirstCounted),
            BuiltinId.@last => WithPreparedFlatItems(EvalLastCounted),
            BuiltinId.@take => WithPreparedSuffixArgs(
                    preparedSuffixArgs =>
                    {
                        var countR = ExpectPreparedWholeNumberSuffixArg(
                            builtin,
                            metadata.SuffixArgs,
                            preparedSuffixArgs,
                            0);
                        if (countR.IsError) return countR.Error;

                        return WithPreparedFlatItems(items => EvalTakeCounted(ctx, items, countR.Value));
                    }),
            BuiltinId.@skip => WithPreparedSuffixArgs(
                    preparedSuffixArgs =>
                    {
                        var countR = ExpectPreparedWholeNumberSuffixArg(
                            builtin,
                            metadata.SuffixArgs,
                            preparedSuffixArgs,
                            0);
                        if (countR.IsError) return countR.Error;

                        return WithPreparedFlatItems(items => EvalSkipCounted(ctx, items, countR.Value));
                    }),
            BuiltinId.@min => WithPreparedNumericItems(EvalMinCounted),
            BuiltinId.@max => WithPreparedNumericItems(EvalMaxCounted),
            BuiltinId.@sum => WithPreparedNumericItems(EvalSumCounted),
            BuiltinId.@avg => WithPreparedNumericItems(EvalAvgCounted),
            BuiltinId.@reduce => WithPreparedSuffixArgs(
                    preparedSuffixArgs =>
                    {
                        var stepR = ExpectPreparedAlgorithmSuffixArg(
                            builtin,
                            metadata.SuffixArgs,
                            preparedSuffixArgs,
                            0);
                        if (stepR.IsError) return stepR.Error;

                        var initialR = ExpectPreparedAlgorithmSuffixArgFull(
                            builtin,
                            metadata.SuffixArgs,
                            preparedSuffixArgs,
                            1);
                        if (initialR.IsError) return initialR.Error;

                        return EvalReduceCounted(
                            bound.IterationItems,
                            stepR.Value,
                            initialR.Value.AlgorithmValue,
                            initialR.Value.PreparedValue,
                            ctx,
                            valEnv);
                    }),
            _ => WrongBuiltinArity(builtin, args.Count),
        };
    }

    /// <summary>
    /// Evaluate a builtin argument's algorithm body through the depth-charged
    /// chokepoint (<see cref="EvaluationBudget.TryEnterArgumentEvaluation"/>).
    /// Builtin argument evaluation re-enters an algorithm body exactly like a call
    /// does, so it must consume depth: without the charge, a zero-parameter
    /// property that reaches itself through a builtin argument (<c>A = count(A)</c>,
    /// <c>A = if(1, A, 0)</c>, <c>A = range(1, A)</c>, a loop's initial state or
    /// count) recurses outside every budget chokepoint and terminates the process
    /// with an uncatchable <see cref="StackOverflowException"/>. It charges no STEP,
    /// preserving the frozen step accounting (steps count dynamic invocations and
    /// loop iterations only) and the plain/dot work-parity pins. The level is entered
    /// through the shared <see cref="TryEnterArgumentEvaluationLevel"/> helper and
    /// released by its <see cref="BudgetLevel"/> — a planned loop <c>if</c> enters the
    /// same one per condition and selected branch, so the two strategies' depth charges
    /// cannot drift (see <c>Evaluator.BudgetScopes.cs</c>).
    /// </summary>
    private static EvalResult<CountedResult> EvalArgumentAlgOutputCounted(
        Algorithm algorithm,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (TryEnterArgumentEvaluationLevel(ctx, out var level) is { } limitError)
            return limitError;

        using (level)
        {
            return EvalAlgOutputCounted(algorithm, ctx, valEnv);
        }
    }

    /// <summary>
    /// Evaluate an algorithm body demanded for its VALUE outside the dynamic-invocation
    /// chokepoints: a zero-parameter <c>AlgEnv</c> thunk demanded from parameter value
    /// position (both <c>Expr.Param</c> twins), or the ordinary-dot <c>string</c>
    /// intrinsic's name-resolved receiver. Each re-enters an algorithm body, so it uses
    /// the same depth-only charge as builtin argument evaluation; left uncharged, a
    /// demand-time re-entry recurses outside every budget chokepoint (exponential
    /// dual-channel retry for <c>F(v) = v.string; x = F(x)</c>, an uncatchable process
    /// <see cref="StackOverflowException"/> for <c>A = A.string</c>). In particular, a
    /// value-channel failure may still retain this algorithm for the established
    /// dual-channel fallback; charging each re-entry keeps that fallback bounded by
    /// the deterministic evaluator depth limit.
    /// </summary>
    private static EvalResult<Result> EvalResolvedAlgOutputForValueDemand(
        Algorithm algorithm,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (TryEnterArgumentEvaluationLevel(ctx, out var level) is { } limitError)
            return limitError;

        using (level)
        {
            return EvalAlgOutput(algorithm, ctx, valEnv);
        }
    }

    /// <summary>
    /// Evaluate the ordinary-dot <c>string</c> intrinsic's algorithm-resolving receiver
    /// for its value (shared by the plain and counted dot-call twins — the intrinsic
    /// needs ONE value either way, so plain/counted behavior stays identical by
    /// construction). Name-resolved receivers — a lexical <c>Resolve</c> or an
    /// <c>AlgEnv</c>-bound <c>Param</c> — are the shapes that can re-enter recursively,
    /// so they go through the depth-charged demand funnel, and a <c>Param</c> receiver
    /// first honors its binding's retained resource-limit value error exactly like the
    /// ordinary <c>Expr.Param</c> value paths (retention stays governed by the
    /// <c>IsResourceLimit</c> policy at the binding sites; this consumer only reads it).
    /// Written receiver shapes (brace block, capture, dot-chain wrapper) carry no name
    /// to cycle back through and their nesting is parser-bounded, so they stay on the
    /// uncharged written-syntax policy like every other block/capture evaluation.
    /// </summary>
    private static EvalResult<Result> EvalDotStringReceiverAlgOutput(
        Expr target,
        Algorithm targetAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        switch (target)
        {
            case Expr.Param(var name):
                if (LookupAlgBinding(ctx.AlgEnv, name) is { ValueError: { } stickyLimit })
                    return AtSpanIfMissing(stickyLimit, target.Span);
                return EvalResolvedAlgOutputForValueDemand(targetAlg, ctx, valEnv);

            case Expr.Resolve:
                return EvalResolvedAlgOutputForValueDemand(targetAlg, ctx, valEnv);

            default:
                return EvalAlgOutput(targetAlg, ctx, valEnv);
        }
    }

    private static EvalResult<CountedResult> EvalResolvedArgumentCounted(
        ResolvedArgumentAlgorithm arg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => arg.PreparedValue is { } prepared
            ? EvalResult<CountedResult>.Ok(prepared)
            : arg.Algorithm is { } algorithm
                ? EvalArgumentAlgOutputCounted(algorithm, ctx, valEnv)
                : new EvalError.BadArity();

    /// <summary>
    /// Returns the argument's algorithm channel. Already evaluated callback data and dotted
    /// sequence-builtin receivers normally never need one; if an algorithm-only builtin
    /// position does request it, build the legacy counted-value wrapper at that point rather
    /// than for every prepared argument.
    /// </summary>
    private static EvalResult<Algorithm> ResolveArgumentAlgorithm(ResolvedArgumentAlgorithm arg, EvalCtx ctx)
        => arg.Algorithm is { } algorithm
            ? EvalResult<Algorithm>.Ok(algorithm)
            : arg.PreparedValue is { } prepared
                ? EvalResult<Algorithm>.Ok(CountedArgAlgorithm(prepared, ctx))
                : new EvalError.BadArity();

    private static EvalResult<Result> EvalResolvedArgument(
        ResolvedArgumentAlgorithm arg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => ProjectCountedValue(EvalResolvedArgumentCounted(arg, ctx, valEnv));

    private static EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>> ExpandSequenceSpreadBuiltinArguments(
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var expanded = new List<ResolvedArgumentAlgorithm>(args.Count);
        foreach (var arg in args)
        {
            if (!arg.SpreadsSequence)
            {
                expanded.Add(arg);
                continue;
            }

            var outputR = EvalResolvedArgumentCounted(arg, ctx, valEnv);
            if (outputR.IsError) return outputR.Error;

            foreach (var value in CountedTopLevelValues(outputR.Value))
            {
                var prepared = new CountedResult(value, 1);
                expanded.Add(new ResolvedArgumentAlgorithm(
                    Algorithm: null,
                    SpreadsSequence: false)
                {
                    PreparedValue = prepared,
                });
            }
        }

        return EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>>.Ok(expanded);
    }

    private static EvalResult<CountedResult> ApplyBuiltinCountedResolved(
        BuiltinId builtin,
        IReadOnlyList<ResolvedArgumentAlgorithm> resolvedArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (GetSequenceBuiltinMetadata(builtin) is { } metadata)
            return ApplyBuiltinCountedSequence(builtin, metadata, resolvedArgs, ctx, valEnv);

        var expandedArgsR = ExpandSequenceSpreadBuiltinArguments(resolvedArgs, ctx, valEnv);
        if (expandedArgsR.IsError) return expandedArgsR.Error;
        var args = expandedArgsR.Value;

        switch (builtin, args.Count)
        {
            case (BuiltinId.@if, 3):
                {
                    var condR = EvalResolvedArgument(args[0], ctx, valEnv);
                    if (condR.IsError) return condR.Error;
                    var truth = condR.Value.TruthValue();
                    if (truth is null) return new EvalError.BadArity();

                    // The selected branch is one argument expression, so `if` observes
                    // it as a single value boundary — exactly like value-position
                    // property access. A multi-output branch property such as
                    // `X = 1, 2, 3` therefore yields the grouped sequence value
                    // `(1, 2, 3)` with emitted count 1, not three separate outputs.
                    // Explicit spread (`if(1, X, X)*`) is the way to open it.
                    // Unlike `while`/`repeat`, which intentionally preserve multi-slot
                    // loop state, `if` re-counts the chosen branch value here.
                    var branchR = truth.Value
                        ? EvalResolvedArgumentCounted(args[1], ctx, valEnv)
                        : EvalResolvedArgumentCounted(args[2], ctx, valEnv);
                    if (branchR.IsError) return branchR.Error;
                    return EvalResult<CountedResult>.Ok(
                        new CountedResult(branchR.Value.Value, branchR.Value.Value.ValueCount()));
                }

            case (BuiltinId.@while, _) when args.Count >= 2:
                {
                    var stepR = ResolveArgumentAlgorithm(args[0], ctx);
                    if (stepR.IsError) return stepR.Error;
                    var initialStateR = EvalInitialLoopStateSlots(args.Skip(1).ToList(), ctx, valEnv);
                    if (initialStateR.IsError) return initialStateR.Error;
                    return WhileLoopCounted(stepR.Value, initialStateR.Value, ctx, valEnv);
                }

            case (BuiltinId.@repeat, _) when args.Count >= 3:
                {
                    var stepR = ResolveArgumentAlgorithm(args[0], ctx);
                    if (stepR.IsError) return stepR.Error;
                    var countR = EvalResolvedArgument(args[1], ctx, valEnv);
                    if (countR.IsError) return countR.Error;
                    var nR = ExpectWholeInt(countR.Value, "Repeat count");
                    if (nR.IsError) return nR.Error;
                    // Domain check BEFORE narrowing: the validated whole number may lie
                    // outside long's range, so the (long) conversion is only safe after
                    // rejecting negatives and saturating oversized counts (behaviorally
                    // identical: both exceed any finite budget).
                    if (nR.Value < 0) return new EvalError.IllegalInEval("Repeat count must be >= 0");
                    var n = nR.Value >= long.MaxValue ? long.MaxValue : (long)nR.Value;

                    var initialStateR = EvalInitialLoopStateSlots(args.Skip(2).ToList(), ctx, valEnv);
                    if (initialStateR.IsError) return initialStateR.Error;
                    return RepeatLoopCounted(stepR.Value, n, initialStateR.Value, ctx, valEnv);
                }

            case (BuiltinId.@atoms, 1):
                {
                    var atomsR = EvalResolvedArgument(args[0], ctx, valEnv);
                    if (atomsR.IsError) return atomsR.Error;
                    // `atoms` materializes a collection: one exact immutable list
                    // of the recursively collected numeric atoms (sequence AND
                    // list boundaries open; truth testing stays list-opaque).
                    return MakeLanguageAtomsResult(ctx, atomsR.Value);
                }

            case (BuiltinId.@range, 2):
                {
                    var rangeR = EvalBuiltinRangeArguments(args, ctx, valEnv);
                    if (rangeR.IsError) return rangeR.Error;

                    // A list value is always one visible value, including `[]`.
                    var rangeValueR = BuildInclusiveRangeChecked(ctx, rangeR.Value);
                    return rangeValueR.IsError
                        ? rangeValueR.Error
                        : EvalResult<CountedResult>.Ok(new CountedResult(rangeValueR.Value, 1));
                }

            default:
                return WrongBuiltinArity(builtin, args.Count);
        }
    }
}
