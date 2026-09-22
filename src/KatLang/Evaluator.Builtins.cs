using System.Collections;
using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

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
    /// <see cref="ReserveSequenceCapture"/> positioned at the first positioned row of
    /// <paramref name="rows"/>, read only when the reservation is REFUSED: the row-loop
    /// funnel that calls this sits on every call-recursion level, and an eager span copy
    /// (a 20-byte value) per level measurably fattened that frame (frame-size discipline).
    /// </summary>
    private static EvalError? ReserveSequenceCaptureAtRows(EvalCtx ctx, int slotCount, IReadOnlyList<Expr> rows)
        => slotCount >= 2 && ctx.Budget.TryReserveCollection(slotCount) is { } error
            ? AtFirstSpanIfMissing(error, rows)
            : null;

    /// <summary>The attach-if-missing law positioned at the first positioned expression of <paramref name="exprs"/>, computed in this leaf frame.</summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalError AtFirstSpanIfMissing(EvalError error, IReadOnlyList<Expr> exprs)
        => AtSpanIfMissing(error, FirstSpan(exprs));

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
    // `spread` re-spreads it (via SpreadItems, which reads the value, not this count).
    //
    // This re-counts without normalizing or rebuilding the value; ordinary value
    // construction has already normalized redundant unary empty structure.
    // Selection and callback items cross this same value boundary. Never apply it to
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

    // The counted view of ONE plain value — a leaf, a native result, a captured
    // group, an empty sequence, a value-position block: it emits Result.ValueCount
    // values (0 for `()`, otherwise 1). Errors propagate unchanged.
    private static EvalResult<CountedResult> CountValue(Result value)
        => EvalResult<CountedResult>.Ok(new CountedResult(value, value.ValueCount()));

    private static EvalResult<CountedResult> CountValue(EvalResult<Result> r)
        => r.IsError ? r.Error : CountValue(r.Value);

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
        ValEnv valEnv)
        => EvalAlgOutputCountedCore(alg, ctx, valEnv);

    /// <summary>Counted twin of <see cref="EvalProgramOutput"/>.</summary>
    private static EvalResult<CountedResult> EvalProgramOutputCounted(
        Algorithm alg,
        EvalCtx ctx,
        ValEnv valEnv)
        => EvalZeroArgumentDemandOutputCounted(alg, ctx, valEnv);

    // No builtin is valid as a bare zero-argument value; every builtin requires
    // a call. (The empty sequence value is written `()`, not a builtin.)
    private static EvalResult<CountedResult> EvalBuiltinValueCounted(BuiltinId builtin)
        => WrongBuiltinArity(builtin, 0);

    /// <summary>
    /// Evaluate a callable that the ONE zero-argument value-demand law
    /// (<see cref="ZeroArgumentValueDemandRejection"/>) has ACCEPTED, as the zero-argument
    /// value it denotes. This is the demand's evaluation half, the counterpart of that
    /// law's rejection half, and the ONE funnel every demand site evaluates through:
    /// <list type="bullet">
    ///   <item>a callable that declares no top-level pattern is its output, exactly as
    ///   before — the overwhelmingly common path, untouched;</item>
    ///   <item>a callable whose pattern list accepts an EMPTY supply (a collecting-only
    ///   signature such as <c>Only(*xs) = xs</c>) is bound by the ORDINARY binder against
    ///   the empty supply first, so its collecting parameter holds the exact empty list
    ///   while the body runs, and the callee's names shadow all three inherited tiers
    ///   exactly as a written call's do;</item>
    ///   <item>a clause family that accepts zero supplied arguments dispatches its
    ///   zero-argument branch through ordinary conditional dispatch, so branch selection,
    ///   duplicate-pattern rejection and the value boundary are the call's own.</item>
    /// </list>
    /// ELIGIBILITY is what the September 2026 rule changed; the CACHE is untouched: a
    /// property-style demand still reaches this funnel through
    /// <see cref="GetOrEvaluateZeroArgPropertyResult"/> (the run cache), while
    /// <c>Only()</c> stays an ordinary call that bypasses it.
    ///
    /// <para>FRAME-SIZE DISCIPLINE: nested blocks and property reads recurse through this
    /// funnel inside the calibrated 1 MiB evaluator envelopes, so the overwhelmingly
    /// common arm — a callable with no top-level pattern — is a bare delegation to the
    /// very core the demand sites called before, holding no locals, and the binding arm's
    /// locals live in a separate non-inlined frame that only a collecting-only or clause
    /// signature ever enters. Lean: <c>evalZeroArgumentDemandOutputCounted</c>.</para>
    /// </summary>
    private static EvalResult<CountedResult> EvalZeroArgumentDemandOutputCounted(
        Algorithm algorithm,
        EvalCtx ctx,
        ValEnv valEnv)
        => RequiresZeroArgumentSupplyBinding(algorithm)
            ? EvalBoundZeroArgumentDemandOutputCounted(algorithm, ctx, valEnv)
            : EvalAlgOutputCountedCore(algorithm, ctx, valEnv);

    /// <summary>Value projection of <see cref="EvalZeroArgumentDemandOutputCounted"/>.</summary>
    private static EvalResult<Result> EvalZeroArgumentDemandOutput(
        Algorithm algorithm,
        EvalCtx ctx,
        ValEnv valEnv)
        => RequiresZeroArgumentSupplyBinding(algorithm)
            ? ProjectCountedValue(EvalBoundZeroArgumentDemandOutputCounted(algorithm, ctx, valEnv))
            : EvalAlgOutputCore(algorithm, ctx, valEnv);

    /// <summary>
    /// Whether a zero-argument demand needs more than the callable's plain output: a
    /// clause family (which DISPATCHES its zero-argument branch) or a parameter list that
    /// must BIND the empty supply. False for every ordinary zero-parameter property,
    /// every written value thunk, and every builtin (whose own arity rejection follows).
    /// </summary>
    private static bool RequiresZeroArgumentSupplyBinding(Algorithm algorithm)
        => algorithm is Algorithm.Conditional || algorithm.ParameterPatterns.Count != 0;

    // The demand funnel's binding arm. Kept out of the funnel's own frame (its locals
    // would otherwise be paid for on the common no-pattern path, which recurses through
    // nested blocks inside the calibrated stack envelopes).
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalBoundZeroArgumentDemandOutputCounted(
        Algorithm algorithm,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (algorithm is Algorithm.Conditional)
        {
            return EvalConditionalCallCounted(
                algorithm,
                OutputBundle.Empty,
                ctx,
                valEnv,
                CallDiagnosticName.FromKnown("conditional"));
        }

        var bindingsR = BindZeroArgumentSupply(algorithm, ctx);
        if (bindingsR.IsError) return bindingsR.Error;

        var environments = WithUserCallBindingEnvironments(ctx, bindingsR.Value, valEnv, algorithm.Params);
        return EvalAlgOutputCountedCore(algorithm, environments.Context, environments.ValueEnvironment);
    }

    /// <summary>
    /// Bind a callable's parameter list against the EMPTY argument supply, through the
    /// ordinary binder — the same call the demand law's acceptance decision is derived
    /// from, so the two cannot disagree about what an empty supply binds. Shared by the
    /// synchronous funnel and its async twin (argument evaluation cannot suspend: there
    /// are no arguments).
    /// </summary>
    private static EvalResult<UserCallBindings> BindZeroArgumentSupply(Algorithm algorithm, EvalCtx ctx)
        => BindParameterPatternList(
            algorithm.ParameterPatterns,
            [],
            ctx,
            allowAlgorithmBindings: true,
            static (required, actual) => new EvalError.ArityMismatch(required, actual));

    private static EvalResult<ZeroArgPropertyResult> EvaluateZeroArgPropertyResult(
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // The cached body evaluation goes through the ONE demand funnel, so a newly
        // eligible collecting-only property (`Only(*xs) = xs`) takes the very same
        // demand/cache path an ordinary zero-parameter property takes.
        var countedR = EvalZeroArgumentDemandOutputCounted(resolvedAlgorithm, ctx, valEnv);
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
        ValEnv valEnv)
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
        ValEnv valEnv)
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
        ValEnv valEnv)
    {
        var propertyR = GetOrEvaluateZeroArgPropertyResult(owner, binding, accessKind, resolvedAlgorithm, ctx, valEnv);
        return propertyR.IsError
            ? propertyR.Error
            : EvalResult<CountedResult>.Ok(new CountedResult(propertyR.Value.Value, propertyR.Value.EmittedCount));
    }

    private static EvalResult<CountedResult> EvalZeroArgPropertyAccessCounted(
        ResolvedLexicalProperty resolvedProperty,
        EvalCtx ctx,
        ValEnv valEnv)
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
        ValEnv valEnv,
        string calleeName = "conditional")
    {
        if (callee.HasDuplicateBranchPatterns())
            return new EvalError.DuplicateBranchPattern();

        var match = MatchCountedCallBranches(callee.Branches, explicitArgs);
        if (match is null)
            return new EvalError.NoMatchingBranch(calleeName);

        var (branch, bindings) = match.Value;
        var binderNames = bindings.Select(static binding => binding.Name).ToArray();
        var newCtx = WithCountedParameterEnvironments(
            ctx.Push(callee),
            bindings,
            binderNames);
        var newEnv = Concat(bindings.Select(static binding => (binding.Name, binding.Value.Value)).ToList(), valEnv);
        var wiredBody = ChildOfConditionalCall(callee, SelectedBranchBody(branch), binderNames, newCtx, newEnv);
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
        ValEnv valEnv)
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
        ValEnv valEnv)
    {
        if (callee.Output.Count == 0)
            return new EvalError.MissingOutput();

        // Accumulator state slots are already the opened accumulator
        // (Result.ToItems), so every slot here is a FINAL item: the collector
        // collects the presented slots exactly, like loop state.
        var countedPatternEnvR = BindCountedParameterPatternList(
            callee.ParameterPatterns,
            FinalCallbackInputs(args),
            ctx,
            (required, actual) => new EvalError.ArityMismatch(required, actual));
        if (countedPatternEnvR.IsError)
            return AttachImplicitParameterProvenance(countedPatternEnvR.Error, callee);

        var patternBindings = countedPatternEnvR.Value;
        var callbackCtx = WithCountedParameterEnvironments(
            ctx,
            patternBindings.CountedBindings,
            patternBindings.CountedBindings.Select(static binding => binding.Name));
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
        ValEnv valEnv,
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
        ValEnv valEnv)
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
        ValEnv valEnv)
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
            // A spread operand is demanded for its VALUE with zero arguments, so the ONE
            // law decides and shapes its report here too: a block whose parameter list
            // accepts an empty supply is demanded through the shared funnel.
            if (ZeroArgumentValueDemandRejection(ZeroArgumentDemandShape.Block, name: null, blockSpan, wired) is { } rejection)
                return rejection;

            var blockR = EvalZeroArgumentDemandOutput(wired, ctx, valEnv);
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
        ValEnv valEnv)
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

    /// <summary>Only arguments without callback parameters are eagerly value-evaluated.</summary>
    private static bool IsValueShapedArgument(Algorithm argument)
        => argument is not Algorithm.Conditional && argument.ParameterPatterns.Count == 0;

    // The collection occupies slot zero; suffix descriptors classify the remaining
    // bound slots. Surplus arguments are not value positions of this signature.
    private static bool IsSequenceBuiltinValueSlot(SequenceBuiltinMetadata metadata, int slot)
        => slot == 0 || slot <= metadata.SuffixArgs.Count
            && metadata.SuffixArgs[slot - 1].Kind != SequenceBuiltinSuffixArgKind.Algorithm;

    /// <summary>
    /// Prepares a filter predicate through the generic call-item and suffix binding
    /// helpers: one eager value attempt, sticky resource-limit retention, and the
    /// original callable identity. Used after fusion commits, with caller environments.
    /// A failed collection in a plain call still requires this attempt; its earlier
    /// error takes precedence over this result, just as in BindSequenceBuiltinArguments.
    /// </summary>
    internal static EvalResult<Algorithm> PrepareFilterPredicateArgument(
        Algorithm argument,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var itemsR = BuildCallableCallItems(
            [new ResolvedArgumentAlgorithm(argument, SpreadsSequence: false)], ctx, valEnv);
        if (itemsR.IsError) return itemsR.Error;

        var descriptor = BuiltinRegistry.GetBuiltin(BuiltinId.@filter).SequenceMetadata!.Value.SuffixArgs[0];
        var preparedR = PrepareSequenceBuiltinSuffixArg(BuiltinId.@filter, descriptor, itemsR.Value[0], ctx, valEnv);
        if (preparedR.IsError) return preparedR.Error;
        return preparedR.Value is PreparedSequenceBuiltinSuffixArg.AlgorithmArg callback
            ? EvalResult<Algorithm>.Ok(callback.AlgorithmValue)
            : throw new InvalidOperationException("The filter predicate must be an algorithm argument.");
    }

    private static EvalResult<IReadOnlyList<VariadicCallItem>> BuildCallableCallItems(
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        ValEnv valEnv,
        SequenceBuiltinMetadata? valueSlots = null)
    {
        var items = new List<VariadicCallItem>();
        foreach (var resolvedArg in args)
        {
            var arg = resolvedArg.Algorithm;

            // A callback argument (a callable that declares parameters) is applied
            // per element by the consuming sequence builtin, never used as a value
            // here. Its parameters are unbound at this collection point, so evaluating
            // its body standalone would resolve those parameter names against the
            // surrounding scope. When a sibling argument shares a parameter name and
            // was deferred as a self-referential thunk, that stray lookup re-enters the
            // same builtin call and recurses without ever settling on a value. Keep the
            // algorithm unevaluated so it can be applied with bound parameters later;
            // only value-shaped arguments (no parameters) are materialized eagerly
            // (IsValueShapedArgument — the classification the fused filter-count
            // pipeline shares).
            if (arg is not null && !IsValueShapedArgument(arg))
            {
                var item = new VariadicCallItem(
                    Value: null,
                    arg,
                    ValueError: null,
                    resolvedArg.PreparedValue,
                    resolvedArg.Source);
                // Binding already knows this emitted slot's role. Demand a VALUE here,
                // before later slots' eager effects, through the same once-only helper
                // used below. A callback slot still carries the unexecuted algorithm.
                items.Add(valueSlots is { } metadata && IsSequenceBuiltinValueSlot(metadata, items.Count)
                    ? DemandSequenceBuiltinCallItemValue(item, ctx, valEnv)
                    : item);
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
                        outputR.Value,
                        resolvedArg.Source));
                }

                continue;
            }

            // A value-shaped NAMED argument with no output is that property's failure when a
            // value position later demands it (BlameDemandedArgumentForMissingOutput), never
            // the callee's; callback positions ignore the value error as before.
            items.Add(new VariadicCallItem(
                Value: null,
                arg,
                BlameDemandedArgumentForMissingOutput(resolvedArg.Source, outputR).Error,
                Source: resolvedArg.Source));
        }

        return EvalResult<IReadOnlyList<VariadicCallItem>>.Ok(items);
    }

    /// <summary>
    /// Call-item assembly preserves callable arguments without entering their bodies.
    /// Once binding selects a VALUE position, report its zero-argument demand using
    /// the original source, or preserve the failure of a valid value's body. Callback
    /// positions never call this helper; retained resource limits remain authoritative.
    /// </summary>
    private static EvalError? SequenceBuiltinValueDemandError(VariadicCallItem item)
        => RetainResourceLimitForAlgorithmBinding(item.ValueError)
            ?? (item.Algorithm is { } algorithm ? ZeroArgumentValueDemandError(item.Source, algorithm) : null)
            ?? item.ValueError;

    /// <summary>
    /// Demand ONE collection-builtin call item that binding has placed in a VALUE
    /// position. Call-item assembly leaves a callable-shaped CALLBACK item
    /// unevaluated (a CALLBACK slot must receive the algorithm, never a value — and
    /// eagerly evaluating a collecting-only callback such as <c>map(xs, Only)</c> would
    /// run its body an extra time), so the demand happens HERE, once the descriptor has
    /// decided the slot is a value: an item the ONE law accepts
    /// (<see cref="AcceptsZeroArgumentValueDemand"/> — a collecting-only signature
    /// alongside every zero-parameter property) is evaluated through the shared demand
    /// funnel, charged exactly as the eager value-shaped path charges it, and every other
    /// item is returned untouched for <see cref="SequenceBuiltinValueDemandError"/> to
    /// report. An item that was already evaluated, or whose evaluation already failed, is
    /// never re-entered. Lean: <c>demandSequenceBuiltinCallItemValue</c>.
    /// </summary>
    private static VariadicCallItem DemandSequenceBuiltinCallItemValue(
        VariadicCallItem item,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (item.Value is not null
            || item.ValueError is not null
            || item.Algorithm is not { } algorithm
            || !AcceptsZeroArgumentValueDemand(algorithm))
        {
            return item;
        }

        var demandedR = EvalArgumentAlgOutputCounted(algorithm, ctx, valEnv);
        return demandedR.IsError
            ? item with { ValueError = BlameDemandedArgumentForMissingOutput(item.Source, demandedR).Error }
            : item with { Value = demandedR.Value.Value, PreparedValue = demandedR.Value };
    }

    private static EvalResult<PreparedSequenceBuiltinSuffixArg> PrepareSequenceBuiltinSuffixArg(
        BuiltinId builtin,
        SequenceBuiltinSuffixArgDescriptor descriptor,
        VariadicCallItem item,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // A Value / WholeNumber control is a VALUE position, so it is demanded through
        // the ONE law; an Algorithm control is a CALLBACK slot and is never demanded.
        if (descriptor.Kind != SequenceBuiltinSuffixArgKind.Algorithm)
            item = DemandSequenceBuiltinCallItemValue(item, ctx, valEnv);

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
                    // lets a genuine callback reference reach the algorithm channel. The
                    // retention policy is the shared algorithm-binding one, and the fused
                    // filter-count pipeline applies the same attempt-and-retain step
                    // through PrepareFilterPredicateArgument.
                    if (RetainResourceLimitForAlgorithmBinding(item.ValueError) is { } stickyLimit)
                        return stickyLimit;

                    var algorithm = item.Algorithm
                        ?? (item.PreparedValue is { } prepared
                            ? CountedArgAlgorithm(prepared, ctx)
                            : null);
                    if (algorithm is not null)
                    {
                        return EvalResult<PreparedSequenceBuiltinSuffixArg>.Ok(
                            new PreparedSequenceBuiltinSuffixArg.AlgorithmArg(algorithm)
                            {
                                PreparedValue = item.PreparedValue,
                                Source = item.Source,
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

                return SequenceBuiltinValueDemandError(item) ?? new EvalError.WithContext(
                    SequenceBuiltinSuffixArgErrorContext(builtin, descriptor),
                    new EvalError.BadArity());

            case SequenceBuiltinSuffixArgKind.WholeNumber:
                {
                    if (item.Value is null)
                        return SequenceBuiltinValueDemandError(item) ?? new EvalError.WithContext(
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
            _ => EvalResult<CollectedSequenceBuiltinInput>.Ok(collected),
        };
    }

    private static string DescribeSequenceItem(Result item) => item switch
    {
        Result.Atom(var n) => $"numeric value {Rendering.ValueTextRenderer.FormatNumberInvariant(n)}",
        Result.Str(var s) => $"string value {Rendering.DiagnosticValueRenderer.RenderDoubleQuotedString(s)}",
        Result.Bool(var b) => $"Boolean value {Rendering.ValueTextRenderer.FormatBool(b)}",
        Result.SequenceValue(var items) when items.Count == 0 => "empty sequence value",
        Result.SequenceValue => "sequence value",
        Result.ListValue(var items) when items.Count == 0 => "empty list value",
        Result.ListValue => "list value",
    };

    private static string NumericSequenceItemErrorContext(BuiltinId builtin, int index, Result item)
        => $"{BuiltinDisplayName(builtin)} expects each collection element to be a single numeric value; item {index} was {DescribeSequenceItem(item)}";

    private static EvalError ReduceInitialAccumulatorRequiresValueError(Algorithm initialAlg)
        => new EvalError.WithContext(
            new ReduceInitialAccumulatorContext(initialAlg.Params.ToList()),
            new EvalError.BadArity());

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
        Expr? initialSource,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // The initial accumulator is a written VALUE slot: when call-item assembly
        // already evaluated it (a value-shaped argument), that result IS the slot's
        // value — evaluating the algorithm channel again would run the body twice.
        // A parameterized algorithm there is rejected from its signature at this
        // boundary — never by entering its body and reinterpreting the failure —
        // with reduce's dedicated hint, the same rejection the dotted
        // `Values.reduce(Add)` form reports for a visibly parameterized reducer.
        if (preparedInitial is null && ZeroArgumentValueDemandError(initialSource, initialAlg) is { } rejection)
            return initialAlg.ParameterCount != 0
                ? ReduceInitialAccumulatorRequiresValueError(initialAlg)
                : rejection;

        var initialR = preparedInitial is { } preparedValue
            ? EvalResult<CountedResult>.Ok(preparedValue)
            : BlameDemandedArgumentForMissingOutput(initialSource, EvalArgumentAlgOutputCounted(initialAlg, ctx, valEnv));
        if (initialR.IsError) return initialR.Error;

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
    /// materialized as one list value.
    /// </summary>
    private static EvalResult<CountedResult> EvalFilterCounted(
        IReadOnlyList<CountedResult> items,
        Algorithm predicateAlg,
        EvalCtx ctx,
        ValEnv valEnv)
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
    /// Evaluate a filter predicate with the same callback and Boolean-result rule
    /// used by generic <c>filter</c>; sequence optimizers call this to avoid
    /// duplicating callback semantics.
    /// </summary>
    internal static EvalResult<bool> EvalFilterPredicateTruth(
        Algorithm predicateAlg,
        CountedResult item,
        int index,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var predicateR = WithFilterItemCtx(
            item.Value,
            index,
            ctx,
            EvalSequenceCallbackCall(predicateAlg, item, ctx, valEnv, "filter predicate"));
        if (predicateR.IsError)
            return predicateR.Error;

        // The predicate must return a Boolean value; a numeric result (`filter{x}` over
        // numbers) is a value-kind error, never a nonzero truth test. Lean: evalFilterCounted.
        var truth = predicateR.Value.AsBool();
        if (truth is null)
            return new EvalError.TypeMismatch(BooleanRequiredMessage("filter predicate result", predicateR.Value));

        return EvalResult<bool>.Ok(truth.Value);
    }

    /// <summary>
    /// Evaluate <c>map(collection, mapper)</c> while preserving the number of
    /// top-level mapped elements. <c>mapper</c> is a fixed control argument.
    /// Each callback item is passed to the mapper exactly as collected from
    /// the post-binding collection view; nested sequence values and
    /// nested list values stay intact. Each captured callback result becomes
    /// one element of the list result (mapped elements are
    /// never flattened into the outer list).
    /// Lean: <c>evalMapCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalMapCounted(
        IReadOnlyList<CountedResult> items,
        Algorithm transformAlg,
        EvalCtx ctx,
        ValEnv valEnv)
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

    /// <summary>
    /// Bind the ONE <c>collection</c> argument of a collection builtin from its
    /// prepared call item and open it through the post-binding collection view.
    /// A VALUE position demands the item: a callable that accepts an empty supply
    /// is evaluated, otherwise it keeps the zero-argument value-demand rejection
    /// (<see cref="SequenceBuiltinValueDemandError"/>); a value's retained
    /// evaluation error surfaces as is. The one-level builtin collection view
    /// applies AFTER binding, to the bound collection value only: a lone
    /// sequence or exact list value opens to its immediate items, and any other
    /// value is a one-element collection (<c>count(7)</c> is 1). Opening is never
    /// recursive — nested sequence/list elements stay intact as single items.
    /// Shared by generic collection-builtin binding and by the sequence-pipeline
    /// optimizer's receiver adapter, so the dotted receiver of <c>R.filter(P)</c>
    /// (the ordinary first argument of <c>filter(R, P)</c>) is demanded and opened
    /// identically under both strategies.
    /// Lean: <c>bindSequenceBuiltinArguments</c> (the collection-item step) /
    /// <c>builtinCollectionItems</c>.
    /// </summary>
    private static EvalResult<IReadOnlyList<Result>> BindSequenceBuiltinCollectionArgument(
        VariadicCallItem collectionItem,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // The `collection` parameter is a VALUE position, so demand the bound item
        // through the ONE zero-argument value-demand law before reading its value.
        collectionItem = DemandSequenceBuiltinCallItemValue(collectionItem, ctx, valEnv);

        if (collectionItem.Value is null)
            return SequenceBuiltinValueDemandError(collectionItem) ?? new EvalError.BadArity();

        return EvalResult<IReadOnlyList<Result>>.Ok(BuiltinCollectionItems(collectionItem.Value));
    }

    private static EvalResult<BoundSequenceBuiltinArguments> BindSequenceBuiltinArguments(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var descriptor = BuiltinRegistry.GetBuiltin(builtin);
        var signature = descriptor.PlainSignature;
        var itemsR = BuildCallableCallItems(args, ctx, valEnv, metadata);
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

        var collectionValuesR = BindSequenceBuiltinCollectionArgument(items[0], ctx, valEnv);
        if (collectionValuesR.IsError) return collectionValuesR.Error;
        var collectionValues = collectionValuesR.Value;

        var collected = new CollectedSequenceBuiltinInput(collectionValues);
        var preparedInputR = PrepareSequenceBuiltinInput(builtin, metadata, collected);
        if (preparedInputR.IsError) return preparedInputR.Error;

        var suffixArgs = new List<PreparedSequenceBuiltinSuffixArg>(metadata.SuffixArgs.Count);
        for (var index = 0; index < metadata.SuffixArgs.Count; index++)
        {
            var preparedArgR = PrepareSequenceBuiltinSuffixArg(
                builtin,
                metadata.SuffixArgs[index],
                items[1 + index],
                ctx,
                valEnv);
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
        // infinities take the extremes, and -0 compares equal to 0. The sort is STABLE
        // like Lean's insertion sort (`sortIntsAsc`): equal-comparing values keep their
        // written order, which is observable through the quantum and zero sign that
        // display preserves (`order((1.0, 1))` is `[1.0, 1]` however long the input) and
        // must not depend on the runtime sort algorithm.
        return MakeCollectionListResult(ctx, SortStable(numbers).Select(static value => (Result)new Result.Atom(value)).ToList());
    }

    /// <summary>
    /// Stable ascending sort under <see cref="Decimal128.CompareTo(Decimal128)"/>'s total
    /// order: equal-comparing values keep their input order (the index breaks ties), so
    /// the arrangement never depends on the runtime's sort algorithm.
    /// </summary>
    private static List<Decimal128> SortStable(IReadOnlyList<Decimal128> numbers)
    {
        var keyed = new (Decimal128 Value, int Index)[numbers.Count];
        for (var i = 0; i < keyed.Length; i++)
            keyed[i] = (numbers[i], i);

        Array.Sort(keyed, static (left, right) =>
        {
            var order = left.Value.CompareTo(right.Value);
            return order != 0 ? order : left.Index.CompareTo(right.Index);
        });

        var sorted = new List<Decimal128>(keyed.Length);
        foreach (var (value, _) in keyed)
            sorted.Add(value);
        return sorted;
    }

    /// <summary>
    /// Evaluate <c>orderDesc(collection)</c> by eagerly sorting the top-level
    /// numeric collection items in descending order and materializing them as
    /// one list value.
    /// Duplicates are preserved, sequence values are not flattened, strings are
    /// rejected, and empty collections yield the empty list <c>[]</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalOrderDescCounted(
        EvalCtx ctx,
        IReadOnlyList<Decimal128> numbers)
    {
        // Lean `sortIntsDesc`: the reverse of the stable ascending order.
        var sorted = SortStable(numbers);
        sorted.Reverse();
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
    /// KatLang value semantics. The result is a Boolean value (<c>true</c> when
    /// some item equals the searched item, otherwise <c>false</c>).
    /// Search is top-level only: sequence values compare structurally as single
    /// items and are not searched recursively.
    /// </summary>
    private static EvalResult<CountedResult> EvalContainsCounted(
        IReadOnlyList<Result> items,
        Result searchedItem)
        => EvalResult<CountedResult>.Ok(new CountedResult(
            new Result.Bool(items.Any(item => Result.ValueComparer.Equals(item, searchedItem))),
            1));

    /// <summary>
    /// Evaluate <c>distinct(collection)</c> by removing later duplicate top-level
    /// items while preserving the original order of first occurrence, then
    /// materializing the kept items as one list value.
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
    /// Evaluate <c>first(collection)</c> by SELECTING the first top-level
    /// collection element: the element is returned exactly as stored and
    /// re-counted through the ordinary value boundary (<see cref="CountValue(Result)"/>),
    /// exactly like <c>collection:0</c> — a selected sequence or list stays one
    /// value, a selected <c>()</c> emits zero values, and only an explicit
    /// spread opens the selection. The collection must be non-empty.
    /// Lean: <c>evalFirstCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalFirstCounted(
        IReadOnlyList<Result> items)
    {
        if (items.Count == 0)
            return new EvalError.BadArity();

        return CountValue(items[0]);
    }

    /// <summary>
    /// Evaluate <c>last(collection)</c> by SELECTING the last top-level
    /// collection element through the same value boundary as
    /// <see cref="EvalFirstCounted"/> and <c>collection:(count - 1)</c>.
    /// The collection must be non-empty.
    /// Lean: <c>evalLastCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalLastCounted(
        IReadOnlyList<Result> items)
    {
        if (items.Count == 0)
            return new EvalError.BadArity();

        return CountValue(items[^1]);
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
    /// list value.
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
    /// times 10^<paramref name="decimalScale"/> directly into Decimal128 — one
    /// IEEE round-to-nearest/ties-to-even rounding of the exact rational, through
    /// the shared <see cref="Decimal128Numerics.RoundRational"/> (the same rounding
    /// the integer-power path certifies against).
    /// </summary>
    private static Decimal128 RoundScaledRationalToDecimal128(
        BigInteger scaledNumerator,
        int denominator,
        int decimalScale)
    {
        var negative = scaledNumerator.Sign < 0;
        return Decimal128Numerics
            .RoundRational(BigInteger.Abs(scaledNumerator), denominator, decimalScale)
            .ToDecimal128(negative);
    }

    private static EvalResult<CountedResult> ApplyBuiltinCountedSequence(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        ValEnv valEnv)
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
                            initialR.Value.Source,
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
        ValEnv valEnv)
    {
        if (TryEnterArgumentEvaluationLevel(ctx, out var level) is { } limitError)
            return limitError;

        using (level)
        {
            return EvalZeroArgumentDemandOutputCounted(algorithm, ctx, valEnv);
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
        ValEnv valEnv)
    {
        if (TryEnterArgumentEvaluationLevel(ctx, out var level) is { } limitError)
            return limitError;

        using (level)
        {
            return EvalZeroArgumentDemandOutput(algorithm, ctx, valEnv);
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
    /// A dot chain that <see cref="ResolveDotReceiver"/> navigated structurally
    /// (<paramref name="receiverIsStructuralMember"/>) is such a name-resolved property
    /// algorithm too — <c>Lib.Sub.string</c> re-enters <c>Sub</c>'s body exactly as
    /// <c>Sub.string</c> would — so it takes the same charged funnel.
    /// Written receiver shapes (brace block, capture, dot-result wrapper) carry no name
    /// to cycle back through and their nesting is parser-bounded, so they stay on the
    /// uncharged written-syntax policy like every other block/capture evaluation.
    /// Whatever the shape, the receiver is demanded for its VALUE with zero
    /// arguments, so the ONE zero-argument value-demand law
    /// (<see cref="ZeroArgumentValueDemandError"/>) decides from the resolved
    /// receiver's signature BEFORE its body is entered: <c>Inc.string</c> with
    /// <c>Inc(x)</c> is the property arity error, a navigated parameterized member
    /// the bare one, and a written parameterized block
    /// <see cref="EvalError.UnresolvedImplicitParams"/> — never <c>Unknown name: x</c>
    /// from inside the receiver. Lean: the <c>string</c> arm of <c>evalDotCallCounted</c>.
    /// </summary>
    private static EvalResult<Result> EvalDotStringReceiverAlgOutput(
        Expr target,
        Algorithm targetAlg,
        bool receiverIsStructuralMember,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (target is Expr.Param(var paramName)
            && LookupAlgBinding(ctx.AlgEnv, paramName) is { ValueError: { } stickyLimit })
        {
            return AtSpanIfMissing(stickyLimit, target.Span);
        }

        if (ZeroArgumentValueDemandError(target, targetAlg) is { } rejection)
            return rejection;

        switch (target)
        {
            case Expr.Param(var name):
                // The receiver is a PARAMETER read for its value: an output-less argument is
                // that parameter's failure (never "Property 'a' has no defined output"),
                // exactly as the value-position read `a` reports it.
                return WithParameterContextOnMissingOutput(name, target.Span, EvalResolvedAlgOutputForValueDemand(targetAlg, ctx, valEnv));

            case Expr.Resolve:
                return EvalResolvedAlgOutputForValueDemand(targetAlg, ctx, valEnv);

            case Expr.DotCall when receiverIsStructuralMember:
                return EvalResolvedAlgOutputForValueDemand(targetAlg, ctx, valEnv);

            default:
                return EvalZeroArgumentDemandOutput(targetAlg, ctx, valEnv);
        }
    }

    /// <summary>
    /// Demand a builtin argument slot for its VALUE with zero explicit arguments. The
    /// ONE zero-argument value-demand law (<see cref="ZeroArgumentValueDemandError"/>)
    /// decides from the resolved algorithm's effective signature BEFORE any body is
    /// entered — and before the depth-only argument level is entered, exactly as the
    /// value-position arms reject before their invocation chokepoint — so a selected
    /// <c>if</c> branch, a loop's initial state, the <c>repeat</c> count, and the
    /// <c>atoms</c>/<c>range</c> arguments reject a parameterized algorithm exactly like
    /// value-position access does (<c>if(1, Inc, 0)</c> with <c>Inc(x)</c> is the
    /// property arity error, never <c>Unknown name: x</c> from inside <c>Inc</c>), while
    /// a zero-parameter algorithm evaluates its output through the charged funnel as
    /// before. Laziness is untouched: a slot is demanded only when the builtin selects
    /// it, so an unselected parameterized branch is never even signature-checked.
    /// Lean: <c>evalArgumentValueCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalResolvedArgumentCounted(
        ResolvedArgumentAlgorithm arg,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (arg.PreparedValue is { } prepared)
            return EvalResult<CountedResult>.Ok(prepared);
        if (arg.Algorithm is not { } algorithm)
            return new EvalError.BadArity();
        if (ZeroArgumentValueDemandError(arg.Source, algorithm) is { } rejection)
            return rejection;

        return BlameDemandedArgumentForMissingOutput(arg.Source, EvalArgumentAlgOutputCounted(algorithm, ctx, valEnv));
    }

    /// <summary>
    /// A demanded VALUE argument with no defined output is the argument's failure, not the
    /// callee's: a NAMED argument (`sum(L)`, `if(1, L, 0)`) is reported through the same
    /// property context a value-position read of `L` attaches
    /// (<see cref="WithPropertyContextOnMissingOutput{T}"/>), so the enclosing call context
    /// renders "Property 'L' has no defined output" instead of blaming the callee.
    /// </summary>
    private static EvalResult<CountedResult> BlameDemandedArgumentForMissingOutput(
        Expr? source,
        EvalResult<CountedResult> result)
    {
        if (!result.IsError || result.Error is not EvalError.MissingOutput)
            return result;

        return source switch
        {
            // A BUILTIN argument slot is always a written argument, so the resolved
            // algorithm is never deconstruction plumbing: the parser emits
            // `Resolve($deconstruct$N)` only as the single argument of that
            // deconstruction's own target helper, which is an Algorithm.User call.
            Expr.Resolve(var name) => WithPropertyContextOnMissingOutput(name, source.Span, resolvedAlgorithm: null, result),
            // A PARAMETER read in the slot (`F(a) = sum(a)` with an output-less argument):
            // the parameter's failure, exactly as a value-position read reports it.
            Expr.Param(var name) => WithSpan<CountedResult>(source.Span, new EvalError.WithContext(new ParameterEvaluationContext(name), result.Error)),
            _ => result,
        };
    }

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
        ValEnv valEnv)
        => ProjectCountedValue(EvalResolvedArgumentCounted(arg, ctx, valEnv));

    private static EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>> ExpandSequenceSpreadBuiltinArguments(
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        ValEnv valEnv)
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
        ValEnv valEnv)
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
                    // The condition must be a Boolean value: `if(1, a, b)` is a
                    // value-kind error, not a truth test. Lean: the `.ifBuiltin` arm.
                    var truth = condR.Value.AsBool();
                    if (truth is null)
                        return new EvalError.TypeMismatch(BooleanRequiredMessage("if condition", condR.Value));

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
                    // `atoms` materializes a collection: one list
                    // of the recursively collected numeric atoms (sequence AND
                    // list boundaries open; strings and Booleans contribute no atoms).
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
