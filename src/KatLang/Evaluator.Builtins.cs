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

    /// <summary>
    /// The completed <c>while</c>/<c>repeat</c> result (LOOP-07, Q-26 decided October 2026):
    /// ONE value — the canonical capture of the final state's slots (<c>()</c> for zero
    /// slots, the slot itself for one, a sequence for several) — crossing the ordinary
    /// RESULT value boundary like every other builtin and call result, so its emitted count
    /// is <see cref="Result.ValueCount"/> of that value (<see cref="ReCountValueBoundary(CountedResult)"/>),
    /// never the slot count. The slot count is the loop's own protocol and is not observable
    /// outside the loop; only an explicit spread <c>L*</c> opens the result into items. This
    /// is the ONE construction site of a loop result: the generic loops (sync and async),
    /// the planned frame and every handover reach it. Lean: <c>loopResultCounted</c>.
    /// </summary>
    internal static EvalResult<CountedResult> MakeCheckedLoopStateResult(
        EvalCtx ctx,
        IReadOnlyList<Result> stateSlots,
        SourceSpan? span = null)
    {
        var valueR = MakeCheckedSequenceCapture(ctx, stateSlots, span);
        return valueR.IsError
            ? valueR.Error
            : EvalResult<CountedResult>.Ok(ReCountValueBoundary(new CountedResult(valueR.Value, stateSlots.Count)));
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
    // Selection, callback items and the completed while/repeat result
    // (MakeCheckedLoopStateResult, Q-26) cross this same value boundary. Never apply it
    // to body/root output accumulation (EvalAlgOutputCountedCore) or to a loop step's
    // own row supply (EvalAlgOutputSlots), both of which must keep their multi-item counts.
    // (Collecting bindings need no re-count: a collector cell's VALUE is one exact list,
    // materialized by MakeCollectionListResult with emitted count 1 — CollectorCell.) Lexical zero-arg property access (EvalCounted
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
        => algorithm is Algorithm.Conditional or Algorithm.Alias || algorithm.ParameterPatterns.Count != 0;

    // The demand funnel's binding arm. Kept out of the funnel's own frame (its locals
    // would otherwise be paid for on the common no-pattern path, which recurses through
    // nested blocks inside the calibrated stack envelopes).
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalBoundZeroArgumentDemandOutputCounted(
        Algorithm algorithm,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (algorithm is Algorithm.Alias)
            return EvalAliasZeroArgumentDemandCounted(algorithm, ctx, valEnv);

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

        var boundCtx = WithNeedBindings(ctx, bindingsR.Value!, algorithm.Params);
        var boundValues = ShadowValEnv(valEnv, algorithm.Params);
        return EvalAlgOutputCountedCore(algorithm, boundCtx, boundValues);
    }

    /// <summary>
    /// Bind a callable's parameter list against the EMPTY argument supply, through the
    /// ordinary binder — the same call the demand law's acceptance decision is derived
    /// from, so the two cannot disagree about what an empty supply binds. Shared by the
    /// synchronous funnel and its async twin (argument evaluation cannot suspend: there
    /// are no arguments).
    /// </summary>
    private static EvalResult<NeedEnv?> BindZeroArgumentSupply(Algorithm algorithm, EvalCtx ctx)
        => BindNeedPatterns(NeedParameterPatterns(algorithm.ParameterPatterns), [],
            ctx, asynchronous: false, family: false).GetAwaiter().GetResult();

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
        if (TryEnterDynamicInvocation(ctx, binding.FirstDeclarationSpan, out var level) is { } limitError)
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
                ctx.NeedEnv.Count == 0 ? ValueEnvironmentCacheIdentity(valEnv) : ctx.NeedEnv,
                ctx.AlgEnv,
                ctx.CountedParamEnv,
                // The budget is created fresh per run (CreateRootCtx) and threaded by
                // reference through every derived ctx, so it is the run identity:
                // entries can never be served across runs even when a host shares
                // one cache instance between runs.
                ctx.Budget)
            { DeclaringScope = resolvedAlgorithm.Parent },
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

    /// <summary>
    /// Evaluate a <c>reduce</c> step on one collected iteration item. The reducer is an
    /// ordinary two-argument callback (THE CALLBACK LAW): it receives the element and the
    /// accumulator as exactly two arguments, each ONE value — <c>reduce(xs, R, init)</c>
    /// calls <c>R(E, Acc)</c> — so a collecting parameter on either side collects those
    /// argument values exactly and a structured accumulator is opened only by the
    /// reducer's own explicit pattern (<c>R(x, (a, b))</c>). The accumulator is always one
    /// value: the initial accumulator is reified at the value boundary and every step must
    /// return exactly one value. Lean: <c>evalSequenceReduceStepCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalSequenceReduceStepCounted(
        Algorithm callee,
        CountedResult element,
        Result accumulator,
        EvalCtx ctx,
        ValEnv valEnv,
        string calleeName = "conditional")
        => EvalResolvedCallbackCallCounted(
            callee,
            [CountedSequenceCallbackItem(element), new CountedResult(accumulator, accumulator.ValueCount())],
            ctx,
            valEnv,
            calleeName);

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
            if (alg is Algorithm.Alias)
                return EvalAliasSpreadOperandItems(expr, alg, ctx, valEnv);

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

    /// <summary>
    /// The call item of an argument that assembly does not evaluate: its value-side
    /// algorithm, its prepared value (if any), its written source, and the callable it
    /// NAMES. A CALLBACK position always receives this item (CALL-03 — supplying a
    /// callback evaluates nothing); a callable-shaped VALUE item starts from it before
    /// its zero-argument demand.
    /// </summary>
    private static VariadicCallItem UnevaluatedCallItem(ResolvedArgumentAlgorithm resolvedArg)
        => new(
            Value: null,
            resolvedArg.Algorithm,
            ValueError: null,
            resolvedArg.PreparedValue,
            resolvedArg.Source,
            resolvedArg.Callable,
            resolvedArg.Cell);

    /// <summary>
    /// Prepares a filter predicate exactly as the generic filter binds its CALLBACK slot:
    /// the unevaluated call item (a callback slot is never value-evaluated merely because it
    /// was supplied, CALL-03) through the ONE suffix preparation, keeping the original
    /// callable identity. Used after fusion commits, with caller environments. The predicate
    /// keeps its algorithm-channel binding (<see cref="ResolvedArgumentAlgorithm.Callable"/>),
    /// so a callable forwarded through a parameter is invoked exactly as the generic filter
    /// invokes it. Evaluates nothing: an unused predicate runs no effect, draws nothing and
    /// cannot fail or recurse. Called only once the source is known to be non-empty, so a
    /// predicate with no CALLABLE identity is reported exactly where the generic filter
    /// reports it (<see cref="ResolvePreparedCallback"/>).
    /// </summary>
    internal static EvalResult<Algorithm> PrepareFilterPredicateArgument(
        ResolvedArgumentAlgorithm predicate,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var descriptor = BuiltinRegistry.GetBuiltin(BuiltinId.@filter).SequenceMetadata!.Value.SuffixArgs[0];
        var preparedR = PrepareSequenceBuiltinSuffixArg(BuiltinId.@filter, descriptor, UnevaluatedCallItem(predicate), ctx, valEnv);
        if (preparedR.IsError) return preparedR.Error;
        return preparedR.Value is PreparedSequenceBuiltinSuffixArg.AlgorithmArg callback
            ? ResolvePreparedCallback(BuiltinId.@filter, callback)
            : throw new InvalidOperationException("The filter predicate must be an algorithm argument.");
    }

    /// <summary>
    /// Form the ordinary cell supply before checking arity. Arbitrary explicit spreads
    /// demand their operand here; an existing collector slice transports its addresses.
    /// VALUE and surplus slots remain suspended. After cardinality succeeds, each builtin
    /// demands its value controls in its established order and projects callbacks only
    /// when an invocation is required. Lean: <c>collectSequenceCallableCallItems</c>.
    /// </summary>
    private static EvalResult<IReadOnlyList<VariadicCallItem>> BuildCallableCallItems(
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        ValEnv valEnv,
        SequenceBuiltinMetadata metadata)
    {
        var expanded = ExpandSequenceSpreadBuiltinArguments(args, ctx, valEnv);
        return expanded.IsError ? expanded.Error : EvalResult<IReadOnlyList<VariadicCallItem>>.Ok(expanded.Value.Select(UnevaluatedCallItem).ToArray());
    }

    /// <summary>
    /// Call-item assembly preserves callable arguments without entering their bodies.
    /// Once binding selects a VALUE position, report its zero-argument demand using
    /// the original source — judging the callable the item NAMES
    /// (<see cref="VariadicCallItem.NamedAlgorithm"/>), never its value wrapper — or
    /// preserve the failure of a valid value's body. Callback positions never call this
    /// helper. A resource limit the item's own demand reached is authoritative: it is the
    /// demand's failure, never replaced by a classification of the callable channel
    /// (RESOURCE LIMITS ARE TERMINAL — a demand checks the shared budget before observing completion). A
    /// parameter's established failure takes precedence over classification of its
    /// independent callable channel. With <paramref name="reduceInitial"/> the item is
    /// <c>reduce</c>'s <c>initial</c> — an ordinary VALUE slot, demanded once like every
    /// other — whose zero-argument REJECTION alone is reported with reduce's dedicated hint
    /// (<see cref="ReduceInitialRejection"/>).
    /// Lean: <c>sequenceBuiltinValueDemandErrorWith?</c>.
    /// </summary>
    private static EvalError? SequenceBuiltinValueDemandError(VariadicCallItem item, bool reduceInitial = false)
        => (item.Source is Expr.Param ? item.ValueError : null)
            ?? (item.ValueError is { } failure && !IsDeferrableEvaluationFailure(failure) ? failure : null)
            ?? (item.NamedAlgorithm is { } algorithm
                ? reduceInitial
                    ? ReduceInitialRejection(algorithm, ZeroArgumentValueDemandError(item.Source, algorithm))
                    : ZeroArgumentValueDemandError(item.Source, algorithm)
                : null)
            ?? item.ValueError;

    /// <summary>
    /// <c>reduce</c>'s <c>initial</c> is an ordinary VALUE slot (HO-04); only the REPORT of a
    /// zero-argument demand rejection is reduce's own. A rejected callable that declares
    /// parameters is the reducer written where the initial accumulator belongs
    /// (<c>reduce(xs, Add, Inc)</c>), so it gets reduce's dedicated accumulator hint; any
    /// other rejection (a clause family's <c>NoMatchingBranch</c>) keeps the law's report.
    /// Lean: <c>reduceInitialRejection</c>.
    /// </summary>
    private static EvalError? ReduceInitialRejection(Algorithm named, EvalError? rejection)
        => rejection is not null && named.ParameterCount != 0
            ? ReduceInitialAccumulatorRequiresValueError(named)
            : rejection;

    /// <summary>
    /// Demand ONE collection-builtin call item that binding has placed in a VALUE
    /// position. Call-item assembly leaves a callable-shaped CALLBACK item
    /// unevaluated (a CALLBACK slot must receive the algorithm, never a value — and
    /// eagerly evaluating a collecting-only callback such as <c>map(xs, Only)</c> would
    /// run its body an extra time), so the demand happens HERE, once the descriptor has
    /// decided the slot is a value: an item whose NAMED callable
    /// (<see cref="VariadicCallItem.NamedAlgorithm"/>) the ONE law accepts
    /// (<see cref="AcceptsZeroArgumentValueDemand"/> — a collecting-only signature
    /// alongside every zero-parameter property) is evaluated through the shared demand
    /// funnel on its VALUE side — for a named property the ordinary property read with its
    /// run cache — charged exactly as the eager value-shaped path charges it, and every
    /// other item is returned untouched for <see cref="SequenceBuiltinValueDemandError"/>
    /// to report. An item that was already evaluated, or whose evaluation already failed,
    /// is never re-entered. Lean: <c>demandSequenceBuiltinCallItemValue</c>.
    /// </summary>
    private static VariadicCallItem FinishNeedCallItemDemand(VariadicCallItem item, NeedCell cell, EvalResult<CountedResult> result)
    {
        if (!result.IsError) return item with { Value = result.Value.Value, PreparedValue = result.Value };
        if (item.Source is Expr.Param(var name))
            return item with { ValueError = DemandParameter(cell, result, name, item.Source.Span).Error };
        if (result.Error.IsResourceLimit) return item with { ValueError = result.Error };
        var callable = cell.ProjectCallable();
        return item with { ValueError = result.Error, Callable = callable.IsOk ? callable.Value : null };
    }

    private static VariadicCallItem DemandSequenceBuiltinCallItemValue(
        VariadicCallItem item,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (item.Cell is { } cell && item.Value is null && item.ValueError is null)
        {
            var result = cell.Demand();
            return FinishNeedCallItemDemand(item, cell, result);
        }
        if (item.Value is null && item.ValueError is null
            && ParameterValueFailure(item.Source, ctx, valEnv) is { } slotFailure)
            return item with { ValueError = slotFailure };

        if (item.Value is not null
            || item.ValueError is not null
            || item.Algorithm is not { } algorithm
            || !AcceptsZeroArgumentValueDemand(item.Callable ?? algorithm))
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
                    if (item.Cell is { } cell)
                        return EvalResult<PreparedSequenceBuiltinSuffixArg>.Ok(
                            new PreparedSequenceBuiltinSuffixArg.AlgorithmArg(null) { Cell = cell, WrittenSource = item.Source });
                    return EvalResult<PreparedSequenceBuiltinSuffixArg>.Ok(
                        new PreparedSequenceBuiltinSuffixArg.AlgorithmArg(item.Algorithm) { Callable = item.Callable, WrittenSource = item.Source });
                }

            case SequenceBuiltinSuffixArgKind.Value:
                if (item.Value is not null)
                {
                    return EvalResult<PreparedSequenceBuiltinSuffixArg>.Ok(
                        new PreparedSequenceBuiltinSuffixArg.ValueArg(item.Value));
                }

                return SequenceBuiltinValueDemandError(item, reduceInitial: builtin == BuiltinId.@reduce)
                    ?? new EvalError.WithContext(
                        SequenceBuiltinSuffixArgErrorContext(builtin, descriptor),
                        new EvalError.BadArity());

            case SequenceBuiltinSuffixArgKind.WholeNumber:
                {
                    if (item.Value is null)
                        return SequenceBuiltinValueDemandError(item) ?? new EvalError.WithContext(
                            SequenceBuiltinSuffixArgErrorContext(builtin, descriptor),
                            new EvalError.BadArity());

                    // A whole-number control follows the one numeric-control rule (Q-27): a
                    // present value of the wrong KIND is TypeMismatch, a number outside the
                    // control's domain (a fraction, NaN, an infinity) is IllegalInEval —
                    // exactly as `range`, `repeat` and `randomInt` report their bounds.
                    var numeric = item.Value.SingleAtomicNumber();
                    if (numeric is null)
                    {
                        return new EvalError.TypeMismatch(
                            $"{SequenceBuiltinSuffixArgErrorContext(builtin, descriptor)}, but was {DescribeOperand(item.Value)}");
                    }

                    if (!Decimal128.IsInteger(numeric.Value))
                    {
                        return new EvalError.IllegalInEval(
                            $"{SequenceBuiltinSuffixArgErrorContext(builtin, descriptor)}, but was {Rendering.ValueTextRenderer.FormatNumberInvariant(numeric.Value)}");
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
        // The empty collection is a DOMAIN failure of an aggregate and a missing POSITION of
        // a selection (Q-27): never an arity error, because the argument count is correct.
        return metadata.EmptyPolicy switch
        {
            SequenceBuiltinEmptyPolicy.AllowEmpty => EvalResult<CollectedSequenceBuiltinInput>.Ok(collected),
            SequenceBuiltinEmptyPolicy.RequireAnyItem when collected.TotalItemCount == 0 => new EvalError.IllegalInEval(
                $"{BuiltinDisplayName(builtin)} requires a non-empty collection"),
            SequenceBuiltinEmptyPolicy.RequireSelectablePosition when collected.TotalItemCount == 0 => new EvalError.WithContext(
                $"{BuiltinDisplayName(builtin)} selects from an empty collection, which has no position to select",
                new EvalError.BadIndex()),
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
    /// The current item is passed to the reducer exactly as collected and the
    /// accumulator as ONE value — two ordinary callback arguments (THE CALLBACK
    /// LAW); nested sequence values stay intact, and only the reducer's own
    /// explicit pattern opens a structured element or accumulator.
    /// The initial accumulator is an ordinary VALUE slot (HO-04): binding already
    /// demanded it ONCE — a failure there is the call's failure and is never retried —
    /// so this function receives its <paramref name="initial"/> value, never an
    /// algorithm to evaluate again. A callable that cannot supply a zero-argument value
    /// was rejected at binding, with reduce's dedicated hint when it declares parameters
    /// (<see cref="SequenceBuiltinValueDemandError"/>).
    /// Lean: <c>evalReduceCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalReduceCounted(
        IReadOnlyList<CountedResult> items,
        Algorithm stepAlg,
        Result initial,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // The initial accumulator occupies ONE written accumulator slot: its value is
        // reified as one persistent value at the ordinary value boundary (the count
        // ReCountValueBoundary computes) BEFORE reduction begins, so an initial
        // expression that emitted multiple items cannot leak that supply through the
        // empty-collection return.
        var accumulator = new CountedResult(initial, initial.ValueCount());
        foreach (var item in items)
        {
            var stepR = WithCtx(
                "while evaluating reduce step (reduce passes each iterated collection item as collected and the accumulator as one value; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)",
                EvalSequenceReduceStepCounted(stepAlg, item, accumulator.Value, ctx, valEnv, ReduceStepFrameName));
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
            EvalSequenceCallbackCall(predicateAlg, item, ctx, valEnv, FilterPredicateFrameName));
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
                EvalSequenceCallbackCallCounted(transformAlg, item, ctx, valEnv, MapTransformFrameName));
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
    /// extraction so numeric shape failures are easier to debug. An element that
    /// is not one number is a present value of the wrong KIND — <c>TypeMismatch</c>
    /// (Q-27), never an arity error. Lean: <c>collectSingleAtomicNumbers</c>.
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
                return new EvalError.TypeMismatch(NumericSequenceItemErrorContext(builtin, index, item));

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

    /// <summary>
    /// The CALLBACK a sequence builtin invokes from an algorithm suffix slot (the
    /// <c>filter</c> predicate, the <c>map</c> mapper, the <c>reduce</c> reducer): the
    /// argument's algorithm-channel identity (<see cref="PreparedSequenceBuiltinSuffixArg.AlgorithmArg.InvokedAlgorithm"/>),
    /// projected through the ONE invoking-slot rule (<see cref="ProjectInvokingSlot"/>) only
    /// once the builtin is about to invoke it (a non-empty collection).
    /// Lean: <c>expectPreparedSequenceBuiltinAlgorithmSuffixArg</c>.
    /// </summary>
    private static EvalResult<Algorithm> ResolvePreparedCallback(BuiltinId builtin, PreparedSequenceBuiltinSuffixArg.AlgorithmArg arg)
        => ProjectInvokingSlot(arg.Cell, arg.InvokedAlgorithm, InvokingSlotRoles.Of(builtin), arg.WrittenSource?.Span);

    /// <summary>
    /// The ROLE of every invoking (CALLABLE) builtin slot: the description of its missing-callability
    /// verdict, <see cref="EvalError.NotAnAlgorithm"/> (Q-06), and the closed set the renderer
    /// recognizes to name the slot in a sentence (<c>KatLangError.FormatNotAnAlgorithm</c>) — a
    /// structured description owned here, never a fake zero-parameter callable. The per-item
    /// invocation frames keep their own names (<see cref="FilterPredicateFrameName"/>,
    /// <see cref="MapTransformFrameName"/>, <see cref="ReduceStepFrameName"/>).
    /// Lean: <c>invokingSlotRole</c>.
    /// </summary>
    internal static class InvokingSlotRoles
    {
        internal const string MapTransform = "map transform";
        internal const string FilterPredicate = "filter predicate";
        internal const string ReduceReducer = "reduce reducer";
        internal const string RepeatStep = "repeat step";
        internal const string WhileStep = "while step";

        /// <summary>The role of a builtin's invoking slot: its callback, or a loop's step.</summary>
        internal static string Of(BuiltinId builtin) => builtin switch
        {
            BuiltinId.@map => MapTransform,
            BuiltinId.@filter => FilterPredicate,
            BuiltinId.@reduce => ReduceReducer,
            BuiltinId.@repeat => RepeatStep,
            BuiltinId.@while => WhileStep,
            _ => throw new InvalidOperationException($"The builtin {BuiltinDisplayName(builtin)} has no invoking slot."),
        };

        /// <summary>Whether a <see cref="EvalError.NotAnAlgorithm"/> description names an invoking builtin slot.</summary>
        internal static bool Contains(string description)
            => description is MapTransform or FilterPredicate or ReduceReducer or RepeatStep or WhileStep;
    }

    // The callee names of the per-item callback invocations (their call frames), unchanged by Q-06.
    private const string FilterPredicateFrameName = "filter predicate";
    private const string MapTransformFrameName = "map transform";
    private const string ReduceStepFrameName = "reduce step";

    /// <summary>
    /// CALLABLE projection of ONE invoking builtin slot — a collection builtin's callback (the
    /// <c>filter</c> predicate, the <c>map</c> transform, the <c>reduce</c> reducer) or a
    /// <c>while</c>/<c>repeat</c> step — made only when the builtin is about to invoke it, so
    /// an unused invoking slot is never projected or validated (CALL-03, LOOP-05). It reads
    /// the argument's algorithm channel alone and never demands its VALUE (NEED-06): a slot
    /// with no CALLABLE identity — a literal, a capture, a list, a selection, a call result,
    /// any computed value — is <c>NotAnAlgorithm</c> (Q-06) described by the slot's ROLE
    /// (<see cref="InvokingSlotRoles"/>), the verdict a user higher-order parameter reports,
    /// positioned at the supplied argument (a cell keeps the original argument's span across
    /// transport) and raised before any invocation is charged. A slot that HAS callable
    /// identity keeps every ordinary binder verdict when it is invoked (a zero-parameter
    /// callable given an item is <c>ArityMismatch</c>). Lean: <c>projectInvokingSlot</c>.
    /// </summary>
    private static EvalResult<Algorithm> ProjectInvokingSlot(NeedCell? cell, Algorithm? invoked, string role, SourceSpan? span)
    {
        var projected = cell is not null ? cell.ProjectCallable() : EvalResult<Algorithm?>.Ok(invoked);
        if (projected.IsError) return projected.Error;
        return projected.Value is { } callable
            ? EvalResult<Algorithm>.Ok(callable)
            : new EvalError.NotAnAlgorithm(role) { Span = cell?.Span ?? span };
    }

    private static EvalResult<Algorithm> ExpectPreparedAlgorithmSuffixArg(
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
                ? ResolvePreparedCallback(builtin, algorithmArg)
                : InternalSequenceBuiltinSuffixArgMetadataError<Algorithm>(
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
    /// spread opens the selection. An empty collection has no position to
    /// select: <c>BadIndex</c>, the outcome of <c>collection:0</c> (SEQ-04, Q-27;
    /// the empty policy reports it before this point).
    /// Lean: <c>evalFirstCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalFirstCounted(
        IReadOnlyList<Result> items)
    {
        if (items.Count == 0)
            return new EvalError.BadIndex();

        return CountValue(items[0]);
    }

    /// <summary>
    /// Evaluate <c>last(collection)</c> by SELECTING the last top-level
    /// collection element through the same value boundary as
    /// <see cref="EvalFirstCounted"/> and <c>collection:(count - 1)</c>.
    /// An empty collection has no position to select: <c>BadIndex</c>.
    /// Lean: <c>evalLastCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalLastCounted(
        IReadOnlyList<Result> items)
    {
        if (items.Count == 0)
            return new EvalError.BadIndex();

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
            return new EvalError.IllegalInEval("min requires a non-empty collection");

        // Decimal128.Min propagates NaN (any NaN element makes the result NaN),
        // so the outcome never depends on where in the collection a NaN sits —
        // a bare `<` scan would be order-dependent because every IEEE comparison
        // against NaN is false. It is IEEE 754 `minimum` for signed zero too, the
        // frozen signed-zero extremum rule: -0 counts below 0, so a zero minimum is
        // -0 whenever a negative zero takes part, in every element order (a `<`
        // scan would keep whichever equal zero came first).
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
            return new EvalError.IllegalInEval("max requires a non-empty collection");

        // NaN-propagating for the same reason as EvalMinCounted, and IEEE 754
        // `maximum` for signed zero: a zero maximum is 0 whenever an ordinary zero
        // takes part, in every element order.
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
        => SumNumbers(numbers, noteExactness: false, out _);

    /// <summary>
    /// The ONE left-to-right Decimal128 sum behind <c>sum</c> and <c>avg</c>, starting
    /// from zero. With <paramref name="noteExactness"/> it also reports whether every
    /// addition was PROVABLY exact: an IEEE sum whose result carries the preferred
    /// quantum (the smaller operand quantum) or a finer one is exact, because an inexact
    /// sum needs all 34 digits at a coarser quantum. The converse does not hold — an
    /// exact sum can need a coarser quantum (<c>9999999999999999999999999999999999 + 1</c>
    /// is exactly <c>1e34</c> at quantum 1) — so "not provably exact" is only a reason
    /// for the caller to decide exactness exactly. A NaN or infinite operand or result is
    /// never provably exact.
    /// </summary>
    private static Decimal128 SumNumbers(IReadOnlyList<Decimal128> numbers, bool noteExactness, out bool provablyExact)
    {
        Decimal128 total = Decimal128.Zero;
        var totalQuantumExponent = 0; // Decimal128.Zero's
        provablyExact = noteExactness;
        foreach (var numeric in numbers)
        {
            var next = total + numeric;
            if (provablyExact)
            {
                if (Decimal128.IsFinite(numeric) && Decimal128.IsFinite(next))
                {
                    var nextQuantumExponent = Decimal128Numerics.QuantumExponent(next);
                    provablyExact = nextQuantumExponent
                        <= Math.Min(totalQuantumExponent, Decimal128Numerics.QuantumExponent(numeric));
                    totalQuantumExponent = nextQuantumExponent;
                }
                else
                {
                    provablyExact = false;
                }
            }

            total = next;
        }

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
    /// Evaluate <c>avg(collection)</c>: the arithmetic mean of the top-level sequence
    /// elements — their EXACT total divided by the count, rounded ONCE to 34 significant
    /// digits (IEEE round-to-nearest, ties to even).
    /// The collection must be non-empty, and each top-level element must be
    /// exactly one atomic numeric value; sequence values are not flattened and strings
    /// are rejected.
    /// The left-to-right Decimal128 sum that <c>sum</c> returns can round (or overflow)
    /// on the way, so the mean is NOT that sum divided by the count whenever the sum was
    /// inexact: <c>avg((1, 1e34, -1e34))</c> is <c>0.333…</c>, not <c>0 / 3</c>
    /// (numeric audit #6, September 2026 — the mean was correctly rounded only when
    /// the sum overflowed). When every addition was exact, <c>total / count</c> IS the
    /// correctly rounded mean and is kept bit-for-bit, IEEE quantum included
    /// (<c>avg((1.0, 2.00))</c> is <c>1.50</c>); a NaN or infinite element keeps that
    /// ordinary IEEE result. Lean's Int-only core approximates the mean with truncation
    /// toward zero (Int.tdiv); that integer approximation is a Lean model limitation,
    /// not the C# runtime contract.
    /// Lean: <c>evalAvgCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalAvgCounted(IReadOnlyList<Decimal128> numbers)
    {
        if (numbers.Count == 0)
            return new EvalError.IllegalInEval("avg requires a non-empty collection");

        var total = SumNumbers(numbers, noteExactness: true, out var provablyExact);
        var average = provablyExact || numbers.Any(static number => !Decimal128.IsFinite(number))
            ? total / numbers.Count
            : AverageFiniteNumbersExactly(numbers, total);

        return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(average), 1));
    }

    /// <summary>
    /// The correctly rounded arithmetic mean of finite Decimal128 values whose
    /// left-to-right sum <paramref name="sequentialTotal"/> was not provably exact
    /// (it rounded, overflowed, or needed a coarser quantum). Every finite Decimal128 is
    /// an integer coefficient times a power-of-ten quantum, so a BigInteger sum at the
    /// smallest element quantum is the exact total. When that exact total is a Decimal128,
    /// it is divided once by the correctly rounded Decimal128 division — as the
    /// sequential total itself when the two are equal (an exact sum at a coarser quantum,
    /// kept bit-for-bit), otherwise at the quantum an exact left-to-right sum carries
    /// (the smallest element quantum, or zero's). A total that is not a Decimal128 (more
    /// than 34 significant digits, or beyond the range: a finite mean is bounded by its
    /// extrema, so it stays representable when the sum is not — MaxValue averaged with
    /// itself is the simplest case) is rounded once as the exact rational, to 34
    /// significant digits or the subnormal quantum floor.
    /// </summary>
    private static Decimal128 AverageFiniteNumbersExactly(IReadOnlyList<Decimal128> numbers, Decimal128 sequentialTotal)
    {
        var coefficientsByExponent = new Dictionary<int, BigInteger>();
        var minimumExponent = 0; // the zero the left-to-right sum starts from
        var nonzeroMinimumExponent = int.MaxValue;

        foreach (var number in numbers)
        {
            var exponent = Decimal128Numerics.QuantumExponent(number);
            if (exponent < minimumExponent)
                minimumExponent = exponent;
            if (number == Decimal128.Zero)
                continue;

            var coefficient = Decimal128Numerics.CoefficientOf(Decimal128.Abs(number), out _);
            if (Decimal128.IsNegative(number))
                coefficient = -coefficient;
            coefficientsByExponent[exponent] = coefficientsByExponent.TryGetValue(exponent, out var existing)
                ? existing + coefficient
                : coefficient;
            if (exponent < nonzeroMinimumExponent)
                nonzeroMinimumExponent = exponent;
        }

        // Horner's scheme over the distinct quanta, largest first, lands the exact total at
        // the smallest nonzero quantum with one small power-of-ten multiplication per
        // distinct quantum — never one power of ten spanning the whole exponent range per
        // quantum, which made thousands of distinct quanta cost seconds.
        var exactScaledSum = BigInteger.Zero;
        int? previousExponent = null;
        foreach (var (exponent, coefficient) in coefficientsByExponent.OrderByDescending(static entry => entry.Key))
        {
            if (previousExponent is { } previous)
                exactScaledSum *= BigInteger.Pow(10, previous - exponent);
            exactScaledSum += coefficient;
            previousExponent = exponent;
        }

        if (Decimal128Numerics.TryExactDecimal128(exactScaledSum, nonzeroMinimumExponent, minimumExponent, out var exactTotal))
            return (sequentialTotal == exactTotal ? sequentialTotal : exactTotal) / numbers.Count;

        return RoundScaledRationalToDecimal128(exactScaledSum, numbers.Count, nonzeroMinimumExponent);
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
                        if (bound.IterationItems.Count == 0) return MakeCollectionListResult(ctx, []);
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
                        if (bound.IterationItems.Count == 0) return MakeCollectionListResult(ctx, []);
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
                        var initialR = ExpectPreparedValueSuffixArg(
                            builtin,
                            metadata.SuffixArgs,
                            preparedSuffixArgs,
                            1);
                        if (initialR.IsError) return initialR.Error;
                        if (bound.IterationItems.Count == 0) return EvalResult<CountedResult>.Ok(new(initialR.Value, initialR.Value.ValueCount()));

                        var stepR = ExpectPreparedAlgorithmSuffixArg(
                            builtin,
                            metadata.SuffixArgs,
                            preparedSuffixArgs,
                            0);
                        if (stepR.IsError) return stepR.Error;

                        return EvalReduceCounted(
                            bound.IterationItems,
                            stepR.Value,
                            initialR.Value,
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
    /// <c>A = if(true, A, 0)</c>, <c>A = range(1, A)</c>, a loop's initial state or
    /// count) recurses outside every budget chokepoint and terminates the process
    /// with an uncatchable <see cref="StackOverflowException"/>. It charges no STEP,
    /// preserving the frozen step accounting (steps count dynamic invocations and
    /// loop iterations only) and the plain/dot work-parity pins. The level is entered
    /// through the shared <see cref="TryEnterArgumentEvaluationLevel"/> helper and
    /// released by its <see cref="BudgetLevel"/> (see <c>Evaluator.BudgetScopes.cs</c>). A
    /// Model-C supply cell — every written argument of an ordinary call, the generic and the
    /// planned <c>if</c> alike — is demanded without such a level.
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
    /// chokepoints — the ordinary-dot <c>string</c> intrinsic's structurally resolved
    /// receiver fallback. It re-enters an algorithm body, so it uses the same depth-only
    /// charge as builtin argument evaluation; left uncharged, a demand-time re-entry would
    /// recurse outside every budget chokepoint. A PARAMETER's value is never demanded
    /// through this funnel: its value outcome is established once, at argument assembly,
    /// and every read reuses it (AT-MOST-ONCE ARGUMENT VALUE EVALUATION,
    /// <see cref="EvalParamCounted"/>).
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
    /// construction). HOW A PROPERTY VALUE IS CONSUMED DOES NOT AFFECT CACHING, so a
    /// name-resolved receiver is READ exactly as a value position reads it: a lexical
    /// <c>Resolve</c> through its binding's zero-argument property access (the run cache
    /// and its charged dynamic-invocation boundary — <c>A.string</c> converts the value
    /// <c>A</c> reads), a dot chain that <see cref="ResolveDotReceiver"/> navigated
    /// structurally (<paramref name="receiverIsStructuralMember"/>) through the selected
    /// member's structural property access (<c>Lib.Sub.string</c> converts the value
    /// <c>Lib.Sub</c> reads), and a <c>Param</c> through the ordinary value-position
    /// parameter read — its bound value, or the failure its argument slot established,
    /// which that read reports before anything else (AT-MOST-ONCE ARGUMENT VALUE
    /// EVALUATION: a parameter's value is never re-derived from its algorithm channel).
    /// The name-resolved shapes that can re-enter recursively each cross a charged
    /// boundary. Written receiver shapes (brace block, capture, dot-result wrapper) carry
    /// no name to cycle back through and their nesting is parser-bounded, so they stay on
    /// the uncharged written-syntax policy like every other block/capture evaluation.
    /// Whatever the shape, the receiver is demanded for its VALUE with zero
    /// arguments, so the ONE zero-argument value-demand law
    /// (<see cref="ZeroArgumentValueDemandError"/>) decides from the resolved
    /// receiver's signature BEFORE its body is entered: <c>Inc.string</c> with
    /// <c>Inc(x)</c> is the property arity error, a navigated parameterized member
    /// the bare one, a written parameterized block
    /// <see cref="EvalError.UnresolvedImplicitParams"/>, and an inline callable alias
    /// <c>{ Inc }.string</c> its written target reference's report (the property arity
    /// error, FA-OQ-1) — never <c>Unknown name: x</c>
    /// from inside the receiver. Lean: the <c>string</c> arm of <c>evalDotCallCounted</c>
    /// and <c>evalDotStringReceiverValue</c>.
    /// </summary>
    private static EvalResult<Result> EvalDotStringReceiverAlgOutput(
        Expr target,
        Algorithm targetAlg,
        bool receiverIsStructuralMember,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (target is Expr.Param(var needName) && LookupNeed(ParameterContext(needName, ctx, ref valEnv).NeedEnv, needName) is not null)
            return ProjectCountedValue(EvalParamCounted(needName, target.Span, ctx, valEnv));

        // A parameter without a supplied cell (the legacy Ready tiers; every Model-C parameter
        // took the cell read above) reports a failure recorded on its algorithm binding first,
        // before the law judges its algorithm channel (AT-MOST-ONCE ARGUMENT VALUE EVALUATION);
        // no Model-C binding path records one.
        if (target is Expr.Param(var paramName)
            && ParameterValueFailure(paramName, ctx, valEnv) is { } slotFailure)
        {
            return ParameterSlotFailure(paramName, target.Span, slotFailure);
        }

        if (ZeroArgumentValueDemandError(target, targetAlg) is { } rejection)
            return rejection;

        // The accepted receiver is READ exactly as a value position reads it: HOW A
        // PROPERTY VALUE IS CONSUMED DOES NOT AFFECT CACHING, so `A.string` converts the
        // very value `A` reads, `Obj.A.string` the value `Obj.A` reads, and `v.string` the
        // value a parameter was bound to. Lean: evalDotStringReceiverValue.
        switch (target)
        {
            case Expr.Param(var name):
                // The ordinary value-position PARAMETER read: its bound VALUE when it has one
                // (a forwarded property value is never re-run through the parameter's
                // algorithm channel), otherwise the algorithm-channel demand, whose
                // output-less argument is that parameter's failure (never "Property 'a' has
                // no defined output"), exactly as the value-position read `a` reports it.
                return ProjectCountedValue(EvalParamCountedOf(target, name, ctx, valEnv));

            case Expr.Resolve(var name):
                return EvalDotStringLexicalPropertyReceiver(target, name, ctx, valEnv);

            case Expr.DotCall edge when receiverIsStructuralMember:
                return EvalDotStringStructuralMemberReceiver(edge, targetAlg, ctx, valEnv);

            default:
                return EvalZeroArgumentDemandOutput(targetAlg, ctx, valEnv);
        }
    }

    /// <summary>
    /// A <c>.string</c> receiver that names a lexical property is that property's ordinary
    /// zero-argument property access — the SAME binding <see cref="ResolveDotReceiver"/>
    /// resolved, read through the run cache — so <c>A.string</c> converts the value
    /// <c>A</c> reads and never re-runs A's body. The receiver is a builtin VALUE slot, so
    /// the read happens inside one depth-only argument-evaluation level exactly as
    /// <c>sum(A)</c>'s value channel is read: the argument level, then the property access's
    /// own dynamic invocation — which also keeps a self-referential <c>A = A.string</c>
    /// bounded by the deterministic depth limit. Kept out of the receiver dispatch's own frame
    /// (<c>.string</c> chains recurse through it).
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<Result> EvalDotStringLexicalPropertyReceiver(
        Expr target,
        string name,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (ctx.CallStack.Count == 0)
            return new EvalError.UnknownName(name) { Span = target.Span };

        var resolvedR = LookupLexical(ctx.CallStack[0], name, ctx);
        if (resolvedR.IsError)
            return AtSpanIfMissing(resolvedR.Error, target.Span);

        if (TryEnterArgumentEvaluationLevel(ctx, out var level) is { } limitError)
            return limitError;

        using (level)
        {
            return ProjectCountedValue(EvalZeroArgPropertyAccessCounted(resolvedR.Value, ctx, valEnv));
        }
    }

    /// <summary>
    /// A <c>.string</c> receiver that <see cref="ResolveDotReceiver"/> navigated to a
    /// declared structural member is that member's structural zero-argument property
    /// access — keyed by the container and the selected binding exactly as the member read
    /// <c>Obj.A</c> in <see cref="EvalDotCallCounted"/> is — so <c>Obj.A.string</c> converts
    /// the value <c>Obj.A</c> reads. The navigation is re-derived from the SAME receiver
    /// resolution and member selection (its accessibility was already enforced there). Like
    /// the lexical case, the read happens inside one depth-only argument-evaluation level.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<Result> EvalDotStringStructuralMemberReceiver(
        Expr.DotCall edge,
        Algorithm targetAlg,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var containerR = ResolveDotReceiver(edge.Target, ctx, out _);
        if (containerR.IsOk && LookupPropBinding(containerR.Value, edge.Name, ctx.Budget) is { } member)
        {
            if (TryEnterArgumentEvaluationLevel(ctx, out var level) is { } limitError)
                return limitError;

            using (level)
            {
                return ProjectCountedValue(EvalZeroArgPropertyAccessCounted(
                    containerR.Value,
                    member,
                    ZeroArgPropertyAccessKind.CountedStructural,
                    TryGetFlatBinderUserEquivalent(targetAlg) ?? targetAlg,
                    ctx,
                    valEnv));
            }
        }

        // Unreachable while ResolveDotReceiver reported a structural member; demanding the
        // resolved algorithm keeps the intrinsic total.
        return EvalResolvedAlgOutputForValueDemand(targetAlg, ctx, valEnv);
    }

    /// <summary>
    /// Demand a builtin argument slot for its VALUE with zero explicit arguments. An
    /// already-bound parameter first reports its established failure. Otherwise the
    /// ONE zero-argument value-demand law (<see cref="ZeroArgumentValueDemandError"/>)
    /// decides from the resolved algorithm's effective signature BEFORE any body is
    /// entered — and before the depth-only argument level is entered, exactly as the
    /// value-position arms reject before their invocation chokepoint — so a selected
    /// <c>if</c> branch, a loop's initial state, the <c>repeat</c> count, and the
    /// <c>atoms</c>/<c>range</c> arguments reject a parameterized algorithm exactly like
    /// value-position access does (<c>if(true, Inc, 0)</c> with <c>Inc(x)</c> is the
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
        if (arg.Cell is { } cell)
        {
            var result = cell.Demand();
            return arg.Source is Expr.Param(var name) ? DemandParameter(cell, result, name, arg.Source.Span) : result;
        }
        if (arg.PreparedValue is { } prepared)
            return EvalResult<CountedResult>.Ok(prepared);
        if (ParameterValueFailure(arg.Source, ctx, valEnv) is { } slotFailure)
            return slotFailure;
        if (arg.Algorithm is not { } algorithm)
            return new EvalError.BadArity();
        // The law judges the callable the argument NAMES; the accepted demand evaluates
        // the VALUE side, which for a named property is the ordinary property read — so
        // the slot reads the property's cached value and never re-runs its body.
        if (ZeroArgumentValueDemandError(arg.Source, arg.InvokedAlgorithm ?? algorithm) is { } rejection)
            return rejection;

        return BlameDemandedArgumentForMissingOutput(arg.Source, EvalArgumentAlgOutputCounted(algorithm, ctx, valEnv));
    }

    /// <summary>
    /// A demanded VALUE argument with no defined output is the argument's failure, not the
    /// callee's: a NAMED argument (`sum(L)`, `if(true, L, 0)`) is reported through the same
    /// property context a value-position read of `L` attaches
    /// (<see cref="WithPropertyContextOnMissingOutput{T}"/>), so the enclosing call context
    /// renders "Property 'L' has no defined output" instead of blaming the callee, and
    /// every OTHER written shape is blamed as the written argument it is
    /// (<see cref="BlameWrittenArgumentForMissingOutput"/>).
    /// </summary>
    private static EvalResult<CountedResult> BlameDemandedArgumentForMissingOutput(
        Expr? source,
        EvalResult<CountedResult> result)
    {
        if (!result.IsError || result.Error is not EvalError.MissingOutput || source is null)
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
            // F5: a written block, capture, call, selection, or operator expression has no
            // name to report. Blaming the written argument is what keeps `count({ })` from
            // reading as though `count` itself had no output — or as though the source had
            // been the argumentless `count()`.
            _ => BlameWrittenArgumentForMissingOutput(source, result.Error),
        };
    }

    /// <summary>
    /// The algorithm a <c>while</c>/<c>repeat</c> step INVOKES: the argument's algorithm-channel
    /// identity (<see cref="ResolvedArgumentAlgorithm.InvokedAlgorithm"/>), so a step forwarded
    /// through a parameter is the callable itself, never its demanded value — projected through
    /// the ONE invoking-slot rule (<see cref="ProjectInvokingSlot"/>) only when an iteration needs
    /// it, and positioned at the step argument. Lean: <c>projectInvokingSlot</c> over
    /// <c>invokeNeed step</c>.
    /// </summary>
    private static EvalResult<Algorithm> ProjectLoopStep(ResolvedArgumentAlgorithm step, BuiltinId loop)
        => ProjectInvokingSlot(step.Cell, step.InvokedAlgorithm, InvokingSlotRoles.Of(loop), step.Source?.Span);

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
                    // Explicit spread (`if(true, X, X)*`) is the way to open it.
                    // `if` re-counts the chosen branch value here, exactly as a completed
                    // `while`/`repeat` re-counts its final state (MakeCheckedLoopStateResult).
                    var branchR = truth.Value
                        ? EvalResolvedArgumentCounted(args[1], ctx, valEnv)
                        : EvalResolvedArgumentCounted(args[2], ctx, valEnv);
                    if (branchR.IsError) return branchR.Error;
                    return EvalResult<CountedResult>.Ok(
                        new CountedResult(branchR.Value.Value, branchR.Value.Value.ValueCount()));
                }

            case (BuiltinId.@while, _) when args.Count >= 2:
            case (BuiltinId.@repeat, _) when args.Count >= 3:
                return EvalNeedLoop(builtin, args, ctx, valEnv, asynchronous: false).GetAwaiter().GetResult();

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
