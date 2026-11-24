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
    /// The formation state of one TRANSIENT item supply under the SEC-01 bound
    /// (<see cref="AdmitTransient"/>). Every item supply a written expression list or row loop
    /// forms carries one: call and selection supplies (<see cref="FormNeedSupply"/>,
    /// <see cref="FormSelectionSupply"/>), list literal slots, output-row and written-group slot
    /// accumulators, loop step rows (generic and planned), and internal sequence joins.
    ///
    /// <para>Once a supply containing a spread passes the per-collection ceiling, the
    /// supply OVERFLOWS: nothing more is retained, but formation continues COUNT-ONLY through
    /// every remaining slot exactly as it would have run — later spreads are still evaluated in
    /// written order, with their effects, failures, and reservations — so the bound changes no
    /// outcome except the one that needed the oversized supply. At the end of formation an
    /// overflowed supply is refused: a supply that becomes a persistent collection (list, capture,
    /// join) by that collection's own reservation over <see cref="Total"/> — exactly the error the
    /// unbounded supply reached — and a supply that is bound or selected from by
    /// <see cref="RefuseTransientSupply"/>.</para>
    /// </summary>
    internal struct TransientSupply
    {
        /// <summary>Every item the supply holds or, once overflowed, would hold.</summary>
        internal long Total;

        /// <summary>The supply opens a spread, a multi-item row, or an internal join.</summary>
        internal bool HasExpansion;

        /// <summary>The expanded supply passed the ceiling: formation continues count-only.</summary>
        internal bool Overflowed;
    }

    /// <summary>
    /// Admits <paramref name="count"/> items of one slot into <paramref name="supply"/> BEFORE they
    /// are appended, copied, or created, and returns whether to RETAIN them; <c>false</c> means the
    /// supply overflowed (now or earlier) and the slot is only counted. Once an explicit spread
    /// contributes (<paramref name="expansion"/>), the WHOLE destination, including written prefix
    /// and suffix slots, is bounded by <see cref="EvaluationBudget.AdmitsTransientExpansion"/>.
    /// A purely written supply remains source-bounded; internal joins opt in for every leaf
    /// because a shared AST can unfold beyond its node count. Moves no materialization counter.
    /// </summary>
    internal static bool AdmitTransient(EvaluationBudget budget, ref TransientSupply supply, int count, bool expansion)
    {
        supply.Total = supply.Total > long.MaxValue - count ? long.MaxValue : supply.Total + count;
        supply.HasExpansion |= expansion;
        if (supply.Overflowed)
            return false;
        // A spread grows the WHOLE destination, including written prefix/suffix slots.
        // Purely written supplies stay source-bounded (e.g. a fixed-arity call under a
        // tiny collection limit), but once opened, every subsequent slot shares the bound.
        if (supply.HasExpansion && !budget.AdmitsTransientExpansion(supply.Total))
        {
            supply.Overflowed = true;
            return false;
        }
        return true;
    }

    /// <summary>
    /// The end-of-formation refusal of an overflowed supply that is bound or selected from (calls,
    /// selections, loop step rows): <see cref="EvalError.CollectionSizeLimitExceeded"/> with the
    /// supply's full size, positioned at <paramref name="span"/> when the failure has none.
    /// </summary>
    internal static EvalError RefuseTransientSupply(EvaluationBudget budget, in TransientSupply supply, SourceSpan? span)
        => AtSpanIfMissing(budget.RefuseTransientSupply(supply.Total), span);

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
    private static EvalError? ReserveSequenceCaptureAtRows(EvaluationBudget budget, int slotCount, IReadOnlyList<Expr> rows)
        => slotCount >= 2 && budget.TryReserveCollection(slotCount) is { } error
            ? AtFirstSpanIfMissing(error, rows)
            : null;

    /// <summary>
    /// The capture refusal of a row-slot accumulator that OVERFLOWED its SEC-01 bound
    /// (<see cref="TransientSupply"/>): the reservation <see cref="ReserveSequenceCaptureAtRows"/>
    /// would have made over the full counted size — which exceeds the ceiling, so it always refuses
    /// with the error the unbounded accumulator reached — without the accumulator ever holding it.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalError RefuseOverflowedCaptureAtRows(EvaluationBudget budget, in TransientSupply supply, IReadOnlyList<Expr> rows)
        => budget.TryReserveCollection(supply.Total) is { } error
            ? AtFirstSpanIfMissing(error, rows)
            : throw new InvalidOperationException("An overflowed transient supply exceeds the collection ceiling.");

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
    /// Materializes a completed output-slot supply, ordinary or unfolded as a nested
    /// list element. Every sequence owns its immediate-item reservation exactly once;
    /// its resulting value subsequently occupies one parent slot. Call only after all
    /// rows succeed. Preserve the ordinary row-positioned refusal and lazy span read.
    /// Takes the run's budget, not the context: its callers sit on recursive frames,
    /// and a by-value <see cref="EvalCtx"/> argument costs each call site a context copy.
    /// </summary>
    private static EvalResult<Result> MakeCheckedSequenceCaptureAtRows(
        EvaluationBudget budget,
        IReadOnlyList<Result> items,
        IReadOnlyList<Expr> rows)
        => ReserveSequenceCaptureAtRows(budget, items.Count, rows) is { } error
            ? error
            : EvalResult<Result>.Ok(CombineOutputSlots(items));

    /// <summary>
    /// The unfolded nested list element's own materialization (a written capture or a
    /// plain block; <see cref="EvalExplicitSequenceValueExprSlots"/> and its async twin):
    /// <see cref="MakeCheckedSequenceCaptureAtRows"/> over the element's completed
    /// supply, positioned by the rule the ordinary dispatch applies to the same node, and
    /// returned as the element's ONE slot. A leaf frame: the recursive written-slot frames
    /// of both twins hold none of its temporaries (frame-size discipline).
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<IReadOnlyList<Result>> MakeCheckedUnfoldedSlot(
        EvaluationBudget budget,
        IReadOnlyList<Result> items,
        Expr expr,
        IReadOnlyList<Expr> rows)
    {
        var capturedR = WithPreferredSpanOf(expr, rows, MakeCheckedSequenceCaptureAtRows(budget, items, rows));
        return capturedR.IsError
            ? capturedR.Error
            : EvalResult<IReadOnlyList<Result>>.Ok([capturedR.Value]);
    }

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
    /// and no unbounded counting prepass is needed. The walk replays shared structures
    /// instead of re-descending them and observes the run's cancellation token during the
    /// walk, but charges no step or structural unit (that cost policy is a separate decision).
    /// The one helper of the generic and async routes.
    /// </summary>
    private static EvalResult<CountedResult> MakeLanguageAtomsResult(
        EvalCtx ctx,
        Result value,
        SourceSpan? span = null)
    {
        // An argument view has no atoms to collect without materializing it (CallReference S2).
        if (IsArgumentView(value))
            return ArgumentViewUnsupported(BuiltinId.@atoms);
        var limit = ctx.Budget.MaxCollectionItems;
        IReadOnlyList<Decimal128> atoms;
        try
        {
            if (!value.TryLanguageAtomsObserved(limit, ctx.Observations?.StructuralTraversal, out atoms, ctx.Budget))
                return AtSpanIfMissing(new EvalError.CollectionSizeLimitExceeded(limit, limit + 1L), span);
        }
        catch (OperationCanceledException cancellation) when (ctx.Budget.CarriesCancellation(cancellation))
        {
            return ctx.Budget.RetainHostTermination(cancellation);
        }

        if (ReserveExactListItems(ctx, atoms.Count, out var items, span) is { } error)
            return error;
        for (var index = 0; index < items.Length; index++)
            items[index] = new Result.Atom(atoms[index]);
        return HandOverListResult(items);
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
    // Selection, callback items, map/reduce callback RESULTS (every callback invocation is
    // the ordinary call, HO-03/Q-25) and the completed while/repeat result
    // (MakeCheckedLoopStateResult, Q-26) cross this same value boundary. Never apply it
    // to body/root output accumulation (EvalAlgOutputCountedCore) or to a loop step's
    // own row supply (EvalAlgOutputSlots), both of which must keep their multi-item counts.
    // (Collecting bindings need no re-count: a collector cell's VALUE is one exact list,
    // materialized by HandOverListResult with emitted count 1 — CollectorCell.) Lexical zero-arg property access (EvalCounted
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

    // No builtin is valid as a bare zero-argument value; every builtin requires
    // a call. (The empty sequence value is written `()`, not a builtin.) A builtin whose
    // arity IS zero (`tick`) is refused as an INVOCATION-REQUIRED demand, never with the
    // misleading "expected 0, received 0" arity report; every other builtin keeps the very
    // arity error its empty call reports. Lean: `evalBuiltinValueCounted`.
    private static EvalResult<CountedResult> EvalBuiltinValueCounted(BuiltinId builtin)
        => BuiltinRegistry.GetBuiltin(builtin).FixedArity == 0
            ? new EvalError.IllegalInEval(BuiltinInvocationRequiredMessage(builtin))
            : WrongBuiltinArity(builtin, 0);

    /// <summary>
    /// The refusal of a bare VALUE demand of a zero-arity builtin. Lean:
    /// <c>builtinInvocationRequiredMessage</c>.
    /// </summary>
    internal static string BuiltinInvocationRequiredMessage(BuiltinId builtin)
    {
        var name = BuiltinRegistry.GetBuiltin(builtin).Name;
        return $"`{name}` is a builtin operation that runs only when it is invoked: write `{name}()`.";
    }

    /// <summary>The refusal of a <c>tick()</c> whose run counter is exhausted. Lean: <c>tickExhaustedMessage</c>.</summary>
    internal const string TickExhaustedMessage =
        "`tick()` cannot advance: the run's counter has reached its limit of 9223372036854775807.";

    /// <summary>
    /// ONE execution of the <c>tick()</c> primitive, reached only by the dispatch arm of an accepted
    /// zero-argument call (after its route's admission, arity, step and depth checks): the run's
    /// terminal state and cancellation are observed first, then the run counter advances once and its
    /// new value is the ONE numeric result (emitted count 1). An exhausted counter is the ordinary
    /// <see cref="EvalError.IllegalInEval"/> domain failure and does not move. Nothing is rolled back
    /// when a surrounding computation later fails. Shared by the sync and async dispatch twins.
    /// Lean: the <c>.tickBuiltin</c> arm of <c>applyBuiltinCounted</c> (<c>runTick</c>).
    /// </summary>
    private static EvalResult<CountedResult> ExecuteTick(EvalCtx ctx)
    {
        if (ctx.Budget.CheckContinuation() is { } terminal)
            return terminal;
        if (!ctx.Budget.TryAdvanceTick(out var value))
            return new EvalError.IllegalInEval(TickExhaustedMessage);
        return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(value), 1));
    }

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
    ///   while the body runs, and the callee's names shadow every inherited tier (need
    ///   cells, algorithm, counted, value) exactly as a written call's do;</item>
    ///   <item>a clause family that accepts zero supplied arguments dispatches its
    ///   zero-argument branch through ordinary conditional dispatch, so branch selection,
    ///   duplicate-pattern rejection and the value boundary are the call's own.</item>
    /// </list>
    /// ELIGIBILITY is what the September 2026 rule changed; the CACHE is untouched: a
    /// property-style demand still reaches this funnel through
    /// <see cref="GetOrEvaluateZeroArgPropertyResult"/> (the run cache), while
    /// <c>Only()</c> stays an ordinary call that never reads it (and, finding Only's entry empty,
    /// establishes it through the same publication law — CACHE-PUB-1, <c>Evaluator.PropertyInvocations.cs</c>).
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

        // ONE projection of the names: it shadows both inherited tiers and enters the body.
        var names = algorithm.Params;
        var boundCtx = WithNeedBindings(ctx, bindingsR.Value!, names);
        var boundValues = ShadowValEnv(valEnv, names);
        return EvalBoundUserBodyCounted(algorithm, boundCtx, boundValues, names, invoked: false);
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
        // demand/cache path an ordinary zero-parameter property takes — except that a
        // user owner whose entry records an activation for local-only properties enters in its
        // DECLARING context (CACHE-OWNER-D1; COLLECT-CACHE-1 for a collecting-only signature).
        var countedR = EntersInDeclaringContext(resolvedAlgorithm)
            ? EvalPropertyOwnerBodyCounted(resolvedAlgorithm, ctx, valEnv)
            : EvalZeroArgumentDemandOutputCounted(resolvedAlgorithm, ctx, valEnv);
        if (countedR.IsError)
            return countedR.Error;

        return EvalResult<ZeroArgPropertyResult>.Ok(
            new ZeroArgPropertyResult(countedR.Value.Value, countedR.Value.EmittedCount));
    }

    /// <summary>
    /// <see cref="EvaluateZeroArgPropertyResult"/> of an EXPORTED binding: the same calculation over the
    /// DETACHED context (<see cref="DetachedEvaluation"/>, "exported means detached"). It serves the
    /// miss and a re-entrant calculation alike, since both run the read's one calculation. Inlined
    /// into the calculation's delegate, so an exported miss adds no frame. Lean: the exported arm of
    /// <c>EvalBody.evalZeroArgPropertyAccessCounted</c>.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    private static EvalResult<ZeroArgPropertyResult> EvaluateDetachedZeroArgPropertyResult(
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // The exported evaluation is SERVED while it runs (ledger R-1; Lean `servingDetached`): an input
        // read it demands in a retained cell's computation, however deferred, is judged against its watermark.
        var detached = DetachedEvaluation(ctx, valEnv, out var values);
        detached.Budget.EnterServing(detached.DetachedBefore);
        try { return EvaluateZeroArgPropertyResult(resolvedAlgorithm, detached, values); }
        finally { detached.Budget.ExitServing(); }
    }

    /// <summary>
    /// THE LOCAL-ONLY READ REFUSAL (EXPORTED-DETACHED, November 2026): a property-style read of a
    /// local-only <paramref name="binding"/> whose key names a DETACHED activation — the nearest
    /// activated level of its declaring chain was recorded before the exported evaluation this
    /// context is inside started (<see cref="IsDetached"/>) — is refused with the existing
    /// <see cref="EvalError.LocalOnlyProperty"/>, or <c>null</c> when the read may proceed. Its entry
    /// is a value of an enclosing call, which the exported evaluation must not depend on; the check
    /// runs BEFORE the cache is consulted, so a HIT is refused exactly like a miss, which no
    /// evaluation would expose. An exported binding is never refused, and neither is a local-only
    /// one whose keying activation the exported evaluation itself recorded. Out of line: only a read
    /// inside an exported evaluation comes here (<see cref="EvalCtx.DetachedBefore"/> is nonzero).
    /// Lean: <c>localOnlyReadRefused</c>.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalError? DetachedLocalOnlyRead(
        PropertyDeclaringOwner owner,
        Property binding,
        Algorithm resolvedAlgorithm,
        EvalCtx ctx)
    {
        if (IsExported(binding))
            return null;

        // The nearest activated level of the declaring chain: the very activation the key is keyed on
        // (DeclaringActivation reads the chain's memoized key facts, so the check costs the same at any depth).
        return DeclaringActivation(resolvedAlgorithm.Parent) is { } activation && IsDetached(activation, ctx)
            ? LocalOnlyPropertyError(DeclaringOwnerDescription(owner), binding)
            : null;
    }

    /// <summary>
    /// A property-style read at an ANNOTATED reader (inside an exported evaluation or a retained cell's
    /// computation): refused when it is keyed on a detached activation (<see cref="DetachedLocalOnlyRead"/>);
    /// otherwise, inside a retained runtime-alias cell's computation, an admitted LOCAL-only read is that
    /// cell's INPUT READ through the activation its key names, with the refusal a reader detaching it reports
    /// (ledger R-1; Lean <c>noteLocalOnlyRead</c>) — and that refusal when the read lands below a reader
    /// already admitted to the cell. Out of line: an unannotated reader never comes here.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalError? AnnotatedLocalOnlyRead(
        PropertyDeclaringOwner owner,
        Property binding,
        Algorithm resolvedAlgorithm,
        EvalCtx ctx)
    {
        if (ctx.DetachedBefore != 0 && DetachedLocalOnlyRead(owner, binding, resolvedAlgorithm, ctx) is { } refused)
            return refused;
        if (ctx.InputRecord is { } record && !IsExported(binding)
            && DeclaringActivation(resolvedAlgorithm.Parent) is { } activation && record.Note(activation.Serial))
            return LocalOnlyPropertyError(DeclaringOwnerDescription(owner), binding);
        return null;
    }

    // How a refused detached read names the declaring owner: its path when it has one. Presentation only.
    private static string DeclaringOwnerDescription(PropertyDeclaringOwner owner)
        => owner.Algorithm is { } algorithm && TryGetAlgorithmPath(algorithm) is { } path ? path : "its declaring scope";

    /// <summary>
    /// Whether a property-style read of <paramref name="algorithm"/> enters a body that records an
    /// activation keying its local-only properties: a user owner (no deferred region) declaring a
    /// property that is not exported — parameterless (CACHE-OWNER-D1), or with a pattern list the
    /// read binds against the EMPTY supply (a collecting-only signature such as <c>Only(*xs)</c>,
    /// COLLECT-CACHE-1). Exactly these reads inherit the declaring context
    /// (<see cref="EvalPropertyOwnerBodyCounted"/>); every other read — a family, an alias, an owner
    /// of exported members only — keeps the demand funnel unchanged, since its entry records nothing
    /// that keys a local-only property. A pattern list that refuses the empty supply fails in the
    /// shared binder exactly as the funnel fails. Lean: the <c>.mk</c> arms of
    /// <c>EvalBody.evalPropertyDemandCounted</c>.
    /// </summary>
    private static bool EntersInDeclaringContext(Algorithm algorithm)
        => algorithm is Algorithm.User { DeferredRegion: null }
           && HasLocalOnlyProperty(algorithm);

    /// <summary>
    /// The binding identity a property-style READ records on its owner's activation: the
    /// declaring activation's (<see cref="DeclaringBindingIdentity"/>, the identity the owner's own
    /// cache key carries), or the READER's when its declaring chain has no activated level — never
    /// the fresh identity a collecting owner's binder mints. Non-evaluating; shared by the
    /// parameterless and collecting READ entries and their async twins. Lean: <c>inherited</c> in
    /// <c>EvalBody.evalPropertyDemandCounted</c>.
    /// </summary>
    private static object PropertyReadBindingIdentity(Algorithm algorithm, EvalCtx readerCtx, ValEnv readerValues)
        => DeclaringBindingIdentity(algorithm.Parent) ?? BindingContextIdentity(readerCtx, readerValues);

    /// <summary>
    /// A property-style READ of a parameterless owner (CACHE-OWNER-D1, owner decision October 23
    /// 2026): DECLARING-CONTEXT INHERITANCE. The body is checked and evaluated exactly as
    /// <see cref="EvalAlgOutputPreparedCore"/> evaluates it — the same access errors
    /// (<see cref="OutputRowsAccessError"/>), the same rows over one entered context — except that
    /// its activation retains the binding identity of the nearest activation on its in-context
    /// declaring chain (<see cref="DeclaringBindingIdentity"/>, the very identity its own cache key
    /// carries), falling back to the reader's only when there is none. So its local-only properties
    /// are keyed on the declaring activation whichever consumer (callback, helper, loop step,
    /// branch, <c>R.Invoke()</c>) reads it first, and a lexical read inside the body, a structural
    /// <c>B.V</c> and an opened <c>V</c> select one entry. Only the identity changes: the entered
    /// context keeps the reader's need tier, values and call stack. An explicit <c>B()</c> never
    /// comes here (it binds a fresh context). An owner with a pattern list is read through
    /// <see cref="EvalCollectingPropertyOwnerBodyCounted"/>. Kept out of the property seam's frame
    /// like the demand funnel's binding arm. Lean: <c>EvalBody.evalPropertyDemandCounted</c>.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalPropertyOwnerBodyCounted(
        Algorithm algorithm,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (algorithm.ParameterPatterns.Count != 0)
            return EvalCollectingPropertyOwnerBodyCounted(algorithm, ctx, valEnv);

        if (OutputRowsAccessError(algorithm, ctx) is { } accessError)
            return accessError;

        var bodyCtx = EnterAlgorithmBody(algorithm, ctx, valEnv,
            inheritedBindingIdentity: PropertyReadBindingIdentity(algorithm, ctx, valEnv));
        var preparedR = EvalOutputRowsPrepared(algorithm.Output, bodyCtx, ctx, valEnv);
        return preparedR.IsError
            ? preparedR.Error
            : EvalResult<CountedResult>.Ok(preparedR.Value.Counted);
    }

    /// <summary>
    /// A property-style READ of an owner whose pattern list accepts the EMPTY supply — a
    /// collecting-only signature such as <c>Only(*xs)</c> (COLLECT-CACHE-1, October 23 2026). The
    /// empty supply is bound exactly as the demand funnel's binding arm binds it
    /// (<see cref="EvalBoundZeroArgumentDemandOutputCounted"/>: <see cref="BindZeroArgumentSupply"/>,
    /// <see cref="WithNeedBindings"/>, <see cref="ShadowValEnv"/>), so <c>xs</c> is the exact empty
    /// list, the callee's names shadow every inherited tier, and a refused supply fails as there.
    /// The body is then checked and entered over the BOUND context as
    /// <see cref="EvalPropertyOwnerBodyCounted"/> enters a parameterless owner: its activation
    /// records the declaring identity (<see cref="PropertyReadBindingIdentity"/>), never the fresh
    /// identity of the bound tier, so <c>Only</c> read by a callback and a structural <c>Only.V</c>
    /// key <c>V</c> on one activation. Only the recorded identity differs from the funnel; an
    /// explicit <c>Only()</c> never comes here. Its locals live in this separate frame, which only
    /// such a read enters. Lean: the pattern arm of <c>EvalBody.evalPropertyDemandCounted</c>.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalCollectingPropertyOwnerBodyCounted(
        Algorithm algorithm,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var bindingsR = BindZeroArgumentSupply(algorithm, ctx);
        if (bindingsR.IsError) return bindingsR.Error;

        if (OutputRowsAccessError(algorithm, ctx) is { } accessError)
            return accessError;

        // ONE projection of the names: it shadows both inherited tiers and enters the body.
        var names = algorithm.Params;
        var boundCtx = WithNeedBindings(ctx, bindingsR.Value!, names);
        var boundValues = ShadowValEnv(valEnv, names);
        var bodyCtx = EnterAlgorithmBody(algorithm, boundCtx, boundValues, names,
            inheritedBindingIdentity: PropertyReadBindingIdentity(algorithm, ctx, valEnv));
        var preparedR = EvalOutputRowsPrepared(algorithm.Output, bodyCtx, boundCtx, boundValues);
        return preparedR.IsError
            ? preparedR.Error
            : EvalResult<CountedResult>.Ok(preparedR.Value.Counted);
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
        PropertyDeclaringOwner owner,
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

    /// <summary>
    /// Every zero-argument property read consults the cache, whoever declares the binding: an
    /// ownerless host-built level is its own declaring owner (CACHE-OWNER-D3; formerly such reads
    /// bypassed the cache and re-evaluated on every read, a C#-only divergence from Lean).
    /// <para>THE EVALUATOR ENFORCES THE EXPOSURE CLASSIFICATION HERE (EXPORTED-DETACHED, November
    /// 2026). An <see cref="PropertyExposure.Exported"/> binding's calculation runs DETACHED
    /// (<see cref="EvaluateDetachedZeroArgPropertyResult"/>), so the run-wide entry it publishes cannot
    /// depend on the call that read it first; its KEY is still computed from the reader's context
    /// (<see cref="ZeroArgPropertyReadExecution"/>) and is the key it always was. A local-only
    /// binding is read in the reader's context, except that a read keyed on a detached activation is
    /// refused before the cache is consulted (<see cref="DetachedLocalOnlyRead"/>). Lean:
    /// <c>EvalBody.evalZeroArgPropertyAccessCounted</c> over <c>zeroArgPropertyPublication</c>.</para>
    /// </summary>
    private static EvalResult<ZeroArgPropertyResult> GetOrEvaluateZeroArgPropertyResultCore(
        PropertyDeclaringOwner owner,
        Property binding,
        ZeroArgPropertyAccessKind accessKind,
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (ctx.CallStack is AnnotatedReadOnlyList<Algorithm> && AnnotatedLocalOnlyRead(owner, binding, resolvedAlgorithm, ctx) is { } refused)
            return refused;

        return ctx.PropertyAccessCache.GetOrEvaluate(
            ZeroArgPropertyReadExecution(owner, binding, accessKind, resolvedAlgorithm, ctx, valEnv),
            IsExported(binding)
                ? () => EvaluateDetachedZeroArgPropertyResult(resolvedAlgorithm, ctx, valEnv)
                : () => EvaluateZeroArgPropertyResult(resolvedAlgorithm, ctx, valEnv));
    }

    /// <summary>
    /// The cache request of a property-style read of <paramref name="binding"/> in <paramref name="ctx"/>:
    /// the ONE construction shared by the synchronous and async property seams and by the deconstruction
    /// source lookup (<see cref="SharedDeconstructionBind"/>), so a key computed ahead of a read is the
    /// key that read uses. Inlined, so the seams' frames are the ones they had with the construction
    /// written in place.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    private static ZeroArgPropertyExecution ZeroArgPropertyReadExecution(
        PropertyDeclaringOwner owner,
        Property binding,
        ZeroArgPropertyAccessKind accessKind,
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        ValEnv valEnv)
        => new(
            owner,
            binding,
            accessKind,
            BindingContextIdentity(ctx, valEnv),
            // The budget is created fresh per run (CreateRootCtx) and threaded by
            // reference through every derived ctx, so it is the run identity:
            // entries can never be served across runs even when a host shares
            // one cache instance between runs.
            ctx.Budget)
        { DeclaringScope = resolvedAlgorithm.Parent };

    private static EvalResult<CountedResult> EvalZeroArgPropertyAccessCounted(
        PropertyDeclaringOwner owner,
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

    /// <summary>
    /// How many items <see cref="AddCountedTopLevelValues"/> appends for <paramref name="output"/>,
    /// computed without appending, so a transient accumulator is admitted first (SEC-01).
    /// </summary>
    private static int CountedTopLevelValueCount(CountedResult output)
        => output.EmittedCount switch
        {
            0 => 0,
            1 => 1,
            _ => ResultItemCount(output.Value),
        };

    /// <summary>
    /// <see cref="AddCountedTopLevelValues"/> behind the transient-supply bound
    /// (<see cref="AdmitTransient"/>): appended only when the supply retains them.
    /// </summary>
    private static void AddCountedTopLevelValuesBounded(
        List<Result> into, CountedResult output, EvaluationBudget budget, ref TransientSupply supply, bool expansion)
    {
        if (AdmitTransient(budget, ref supply, CountedTopLevelValueCount(output), expansion))
            AddCountedTopLevelValues(into, output);
    }

    /// <summary>
    /// <c>List.AddRange</c> behind the transient-supply bound (<see cref="AdmitTransient"/>):
    /// appended only when the supply retains them.
    /// </summary>
    private static void AddSlotsBounded(
        List<Result> into, IReadOnlyList<Result> slots, EvaluationBudget budget, ref TransientSupply supply, bool expansion)
    {
        if (AdmitTransient(budget, ref supply, slots.Count, expansion))
            into.AddRange(slots);
    }

    /// <summary>One written slot behind the transient-supply bound (<see cref="AdmitTransient"/>).</summary>
    private static void AddSlotBounded(List<Result> into, Result slot, EvaluationBudget budget, ref TransientSupply supply)
    {
        if (AdmitTransient(budget, ref supply, 1, expansion: false))
            into.Add(slot);
    }

    // Stream occurrences: a shared host AST can have exponentially more leaves than nodes.
    // The traversal stack holds only the pending right branches, never a flattened leaf list.
    private static IEnumerable<Expr> SequenceConstructLeaves(Expr expr)
    {
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

            yield return current;
        }
    }

    /// <summary>
    /// Evaluate the INTERNAL <see cref="Expr.SequenceConstruct"/> join node as
    /// one sequence value. Join semantics, not written-parentheses semantics:
    /// a non-spread leaf whose value is <c>()</c> contributes NO item (an
    /// empty join contribution), a spread leaf contributes exactly the items the
    /// spread expression supplies — read back like a spread output row
    /// (<see cref="EvalCounted"/> + <see cref="AddCountedTopLevelValues"/>), one
    /// boundary per written star, never reopened, a spread-produced <c>()</c>
    /// item included — and the items are combined with the shallow
    /// <see cref="CombineOutputSlots"/> (Lean normalizes; the two agree on the
    /// canonical items evaluation produces). Written parentheses parse to
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
        var items = new List<Result>();
        // Internal joins expand AST occurrences, including plain leaves of a shared DAG.
        // They have no written-slot source bound, so every contributed item is admitted.
        TransientSupply bound = new() { HasExpansion = true };

        foreach (var leaf in leaves)
        {
            if (leaf is Expr.SequenceSpread)
            {
                // A spread leaf supplies exactly the spread EXPRESSION's items, read
                // back like a spread output row: one boundary per written star, never
                // reopened. Lean: the `.sequenceSpread` arm of evalSequenceConstructCounted.
                var spreadR = EvalCounted(leaf, ctx, valEnv);
                // A leaf is a SUBORDINATE computation of the join (Q-36).
                if (spreadR.IsError) return NestMissingOutput(spreadR.Error);

                AddCountedTopLevelValuesBounded(items, spreadR.Value, ctx.Budget, ref bound, expansion: true);
                continue;
            }

            var valueR = Eval(leaf, ctx, valEnv);
            if (valueR.IsError) return NestMissingOutput(valueR.Error);

            if (valueR.Value.ValueCount() != 0)
                AddSlotBounded(items, valueR.Value, ctx.Budget, ref bound);
        }

        // SEC-01: an overflowed join was formed count-only; its reservation refuses the full size.
        if ((bound.Overflowed ? ReserveCollection(ctx, bound.Total) : ReserveSequenceCapture(ctx, items.Count)) is { } sequenceLimitError)
            return sequenceLimitError;

        var value = CombineOutputSlots(items);
        return EvalResult<CountedResult>.Ok(new CountedResult(
            value,
            value.ValueCount()));
    }

    private static EvalError SpreadMissingOutput(SourceSpan? span)
        => new EvalError.SpreadMissingOutput() { Span = span };

    // THE Q-36 CONTEXT-CHAIN READERS (November 2026, implementation only). They decide on a failure's
    // terminal or rebuild its chain of context frames, and the consumers run once per level a failure
    // leaves. A run's chain grows with its nesting, which the async route does not bound by the host stack
    // (a stack hop continues recursion routed through loop steps on fresh stacks), and a completing twin
    // runs its continuation on whatever stack is left above the runtime's reserve: one native frame per
    // context frame there overflowed the process at about 1,200 frames, and walking the chain for each
    // verdict made a deep failure's unwinding quadratic (about 5 s for 10,000 loop-step levels). They
    // therefore read the terminal each frame recorded when it was built (EvalError.UnwrapContext: constant
    // work and stack, so an unaffected failure costs nothing per level) and rebuild through
    // WithContextTerminal, in constant stack, only when the terminal changes. The verdicts, the copied
    // frames (span and runtime slots), their order and the terminal are unchanged.

    /// <summary>Any missing output, whatever its origin and context frames (the category test).</summary>
    private static bool IsMissingOutputError(EvalError error)
        => error.UnwrapContext() is EvalError.MissingOutput;

    /// <summary>
    /// The failure is the OWN missing output of the computation whose outcome it is (Q-36): raised
    /// by that computation's output check and carried through its context frames only.
    /// Lean: <c>isOwnMissingOutputError</c>.
    /// </summary>
    internal static bool IsOwnMissingOutputError(EvalError error)
        => error.UnwrapContext() is EvalError.MissingOutput { IsNested: false };

    /// <summary>
    /// The same context frames, outermost first, around <paramref name="terminal"/> in place of the
    /// failure they carried: every frame is copied with its span and runtime slots
    /// (<see cref="EvalError.WithContext.WithInner"/>), innermost first, so nothing is shared with
    /// <paramref name="outermost"/> but the contexts themselves. Constant stack: the frames are
    /// collected in a heap buffer, never on one native frame each.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalError.WithContext WithContextTerminal(EvalError.WithContext outermost, EvalError terminal)
    {
        if (outermost.Inner is not EvalError.WithContext second)
            return outermost.WithInner(terminal);

        var frames = new List<EvalError.WithContext> { outermost, second };
        while (frames[^1].Inner is EvalError.WithContext next)
            frames.Add(next);
        var rebuilt = frames[^1].WithInner(terminal);
        for (var i = frames.Count - 2; i >= 0; i--)
            rebuilt = frames[i].WithInner(rebuilt);
        return rebuilt;
    }

    /// <summary>
    /// THE ONE BLAME TEST (2026-11-08): may a report NAME the subject of the frame that holds
    /// <paramref name="missing"/> as output-less — "Property 'P' …", "Parameter 'x' …",
    /// "Cannot call 'F' …", "The value <c>R.n</c> …"? Only when the missing output is that
    /// subject's OWN (<see cref="EvalError.MissingOutput.IsNested"/> is <c>false</c>), or was
    /// nested only after its subject was identified (<see cref="EvalError.MissingOutput.KeepsOwnBlame"/>:
    /// nested under the subject's own frame, or through deconstruction plumbing alone). A nested
    /// missing output is someone else's (<c>H2 = { } + 1</c>: the <c>{ }</c> operand's), so it keeps
    /// the innermost generic report at its own span, and the enclosing frames render as ordinary
    /// context. Reads stored provenance only: it evaluates nothing and never decides by name,
    /// spelling or span. Lean: the <c>.missingOutput .own</c> arm of <c>withMissingOutputCtx</c>.
    /// </summary>
    internal static bool IsOwnForBlame(EvalError.MissingOutput missing)
        => !missing.IsNested || missing.KeepsOwnBlame;

    /// <summary>
    /// The same failure as part of a CONSUMING computation's outcome (Q-36): a missing output in
    /// it is nested; its context frames, spans and every other error are unchanged. Never mutates
    /// <paramref name="error"/> (a memoized failure is shared by every consumer): an own missing
    /// output is copied. Lean: <c>Error.nestMissingOutput</c> / <c>withNestedMissingOutput</c>.
    ///
    /// <para>An own missing output that already sits DIRECTLY under a context frame was claimed by
    /// that frame's subject before it was nested (<c>F() + 1</c>: the call frame of an output-less
    /// <c>F</c>), so its copy also keeps that blame (<see cref="EvalError.MissingOutput.KeepsOwnBlame"/>,
    /// <see cref="IsOwnForBlame"/>); the origin itself is nested exactly as before.</para>
    ///
    /// <para>Uses constant stack. A failure whose
    /// terminal is not an own missing output is returned as it is, the same object, decided in constant
    /// work from the terminal its outermost frame recorded; otherwise every
    /// context frame is copied around the nested copy of the terminal
    /// (<see cref="WithContextTerminal"/>), once: the copy's terminal is nested. Out of line (FRAME-SIZE
    /// DISCIPLINE): it runs on error paths only, while its callers sit on the evaluator's recursion
    /// spines.</para>
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    internal static EvalError NestMissingOutput(EvalError error)
    {
        if (error.UnwrapContext() is not EvalError.MissingOutput { IsNested: false } own)
            return error;
        return error is EvalError.WithContext outermost
            ? WithContextTerminal(outermost, own with { IsNested = true, KeepsOwnBlame = true })
            : own with { IsNested = true };
    }

    /// <summary>
    /// <see cref="NestMissingOutput(EvalError)"/> through a TRANSPARENT layer whose subject the next
    /// frame already names: a BARE own missing output is nested exactly as before, and its copy keeps
    /// its blame (<see cref="EvalError.MissingOutput.KeepsOwnBlame"/>); any other failure nests as
    /// <see cref="NestMissingOutput(EvalError)"/> does, so a missing output that was already nested
    /// stays someone else's. Two layers are transparent this way:
    /// <list type="bullet">
    /// <item>the deconstruction plumbing (F3): the written right-hand side's failure, nested into the
    /// synthetic frames that carry it to the targets, so the target's read names the target exactly as
    /// <c>x = { }</c> does, while <c>x, y = { } + 1</c> stays the operand's;</item>
    /// <item>a structural carrier crossed by a VALUE read of its terminal (M4★: a transparent reference
    /// IS its target): <c>A = { P }</c> with an output-less <c>P</c> reads as P's own missing output,
    /// which the read's frame names ("Property 'P' …"), while the Q-36 origin is nested.</item>
    /// </list>
    /// <para>Out of line (FRAME-SIZE DISCIPLINE): it runs on error paths only, but its callers sit on
    /// the lexical read and output-row recursion spines, so its record copy must not be inlined into
    /// their frames.</para>
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalError NestKeepingOwnBlame(EvalError error)
        => error is EvalError.MissingOutput { IsNested: false } missing
            ? missing with { IsNested = true, KeepsOwnBlame = true }
            : NestMissingOutput(error);

    /// <summary>
    /// The deconstruction binder's nesting of the right-hand side's failure (F3 parity,
    /// <see cref="NestKeepingOwnBlame"/>).
    /// </summary>
    private static EvalError NestDeconstructionSourceFailure(EvalError error) => NestKeepingOwnBlame(error);

    /// <summary>
    /// A VALUE read that crosses a structural carrier is nested (Q-36 with M4★); the terminal's own
    /// missing output keeps the terminal's blame (<see cref="NestKeepingOwnBlame"/>).
    /// </summary>
    private static EvalResult<T> NestCarrierCrossing<T>(EvalResult<T> result)
        => result.IsError ? NestKeepingOwnBlame(result.Error) : result;

    /// <summary>
    /// The output-row loop's nesting of a failed row (Q-36), shared by the sync and async loops. The
    /// rows of a deconstruction's synthetic frame (<see cref="Algorithm.IsSyntheticDeconstructionFrame"/>:
    /// the hoisted <c>$deconstruct$N</c> source, whose one row IS the written right-hand side, or a
    /// target helper) are plumbing, so they nest through <see cref="NestDeconstructionSourceFailure"/>;
    /// every other row loop, a capture's rows evaluated inside such a frame included (its rows are
    /// not the frame's own output list), nests as before. Structural provenance and reference
    /// identity only; this runs on the error path only, out of line (FRAME-SIZE DISCIPLINE: the row
    /// loops are the structural-nesting recursion spine, so this test must not widen their frames).
    /// The row context arrives by reference: passing <c>rowCtx.CallStack</c> made the caller hold the
    /// getter's result in one more frame slot, 16 bytes per row-loop frame in Debug and in Release
    /// Tier-0 code (848 instead of 832 and 592 instead of 576 bytes, measured on Windows x64 in
    /// November 2026), about 2 KiB over the 100 levels of the one-name open-chain control.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalError NestOutputRowFailure(EvalError error, IReadOnlyList<Expr> rows, in EvalCtx rowCtx)
        => rowCtx.CallStack is [Algorithm.User { IsSyntheticDeconstructionPlumbing: true } frame, ..]
            && ReferenceEquals(frame.Output, rows)
                ? NestDeconstructionSourceFailure(error)
                : NestMissingOutput(error);

    /// <inheritdoc cref="NestMissingOutput(EvalError)"/>
    private static EvalResult<T> NestMissingOutput<T>(EvalResult<T> result)
        => result.IsError ? NestMissingOutput(result.Error) : result;

    // Keep the demand's property/call/argument frames when changing its own missing-output kind
    // (rebuilt in constant stack, WithContextTerminal).
    private static EvalError ConvertOwnSpreadMissingOutput(EvalError error, SourceSpan? span)
        => error is EvalError.WithContext outermost
            ? WithContextTerminal(outermost, SpreadMissingOutput(span))
            : SpreadMissingOutput(span);

    /// <summary>
    /// What a spread reports when evaluating its (peeled) operand failed (X-29 / Q-36, decided
    /// 2026-10-24): the operand's OWN missing output — the computation it directly denotes has no
    /// written output — is <see cref="EvalError.SpreadMissingOutput"/> at the operand; a NESTED
    /// missing output — one originating in a dependency, argument, output row or other subordinate
    /// computation of the operand — keeps its category, cause and blame (span included), with the
    /// spread operand as added context; every other failure is the operand's own, unchanged. Reads
    /// the completed failure only: nothing is evaluated. Lean: <c>spreadOperandFailure</c>.
    /// </summary>
    internal static EvalError SpreadOperandFailure(Expr operand, SourceSpan? span, EvalError error)
    {
        if (IsOwnMissingOutputError(error)) return ConvertOwnSpreadMissingOutput(error, span);
        if (IsMissingOutputError(error))
        {
            // A transported frame can have no span while its cause has one. Prefer the existing
            // blame anywhere in that chain to the consumer's spread fallback.
            var cause = error;
            while (cause.Span is null && cause is EvalError.WithContext context) cause = context.Inner;
            return new EvalError.WithContext(new SpreadOperandContext(OpenExprName(operand)), error) { Span = cause.Span ?? span };
        }
        return error;
    }

    // Supplies a spread's PEELED operand's VALUE (the written stars then open it, OpenSpreadLayers);
    // EvalSequenceSpreadCounted and the supply's spread slot (FormSpreadSupplySlot) are its callers.
    // A consumer holding a whole spread EXPRESSION reads its items through EvalCounted +
    // AddCountedTopLevelValues instead — handing this the spread node itself would spread the
    // spread's captured value again (one boundary too many). A failed operand is reported by
    // SpreadOperandFailure on every arm (X-29 / Q-36): only its OWN missing output is the spread's.
    // Lean: evalSequenceSpreadOperandValue.
    private static EvalResult<Result> EvalSequenceSpreadOperandValue(
        Expr expr,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (expr is Expr.Capture(var captureBody))
        {
            var captureSpan = PreferExpressionSpan(expr.Span, captureBody);
            var captureR = WithSpan(captureSpan, EvalCaptureValue(captureBody, ctx, valEnv));
            if (captureR.IsError)
                return SpreadOperandFailure(expr, captureSpan, captureR.Error);

            return captureR;
        }

        if (expr is Expr.AlgorithmExpr(var alg))
        {
            if (alg is Algorithm.Alias)
                return EvalAliasSpreadOperandValue(expr, alg, ctx, valEnv);

            var wired = WireToCaller(ctx, alg);
            var blockSpan = PreferExpressionSpan(expr.Span, wired.Output);
            // A spread operand is demanded for its VALUE with zero arguments, so the ONE
            // law decides and shapes its report here too: a block whose parameter list
            // accepts an empty supply is demanded through the shared funnel.
            if (ZeroArgumentValueDemandRejection(ZeroArgumentDemandShape.Block, name: null, blockSpan, wired) is { } rejection)
                return rejection;

            var blockR = EvalZeroArgumentDemandOutput(wired, ctx, valEnv);
            if (blockR.IsError)
                return SpreadOperandFailure(expr, blockSpan, blockR.Error);

            return blockR;
        }

        var outputR = Eval(expr, ctx, valEnv);
        if (outputR.IsError)
            return SpreadOperandFailure(expr, expr.Span, outputR.Error);

        return outputR;
    }

    /// <summary>The innermost operand of a (possibly stacked) spread and its number of written stars.</summary>
    private static Expr PeelSpreadLayers(Expr expr, out int layers)
    {
        var operand = expr;
        layers = 0;
        while (operand is Expr.SequenceSpread(var supplied))
        {
            operand = supplied;
            layers++;
        }

        return operand;
    }

    /// <summary>
    /// The written stars of a spread over its operand VALUE: each star opens exactly one boundary of the
    /// value the previous star re-captured, so <c>A**</c> agrees with <c>(A*)*</c>, and the result is the
    /// last capture with the last star's item count. An ARGUMENT VIEW (CallReference S2) is never opened
    /// into values: a star that would open one is <see cref="ArgumentViewSpreadMessage"/>, except that
    /// with <paramref name="transportView"/> (an argument supply's spread slot) the view the LAST star
    /// opens is returned as <see cref="OpenedSpread.View"/> for its cells to be transported (the returned
    /// items are then meaningless). A star that opens a list evaluated on demand reads that level first
    /// (<see cref="OpenLazySpreadLayers"/>, issue #204). Lean: <c>openSpreadItems</c> /
    /// <c>openSupplySpread</c> after <c>peelSpreadLayers</c>.
    /// </summary>
    private static ValueTask<OpenedSpread> OpenSpreadLayers(
        Result value, int layers, Expr expr, EvalCtx ctx, bool transportView, bool asynchronous)
        => ctx.Budget.HasLazyLists
            ? OpenLazySpreadLayers(value, layers, expr, ctx, transportView, asynchronous)
            : new(OpenConcreteSpreadLayers(value, layers, expr, ctx, transportView));

    /// <summary>
    /// What the written stars of one spread opened: its counted items, or — for an argument supply
    /// whose LAST star opens an argument view — that view, whose original cells the supply
    /// transports (<see cref="Items"/> is then the default success).
    /// </summary>
    private readonly record struct OpenedSpread(EvalResult<CountedResult> Items, Result.CallReference? View = null);

    // The layers of a run that has created no list evaluated on demand: every opened value is
    // concrete, so nothing is read.
    private static OpenedSpread OpenConcreteSpreadLayers(
        Result value, int layers, Expr expr, EvalCtx ctx, bool transportView)
    {
        var opened = value;
        for (var layer = 0; layer < layers; layer++)
        {
            if (opened is Result.CallReference { IsArgumentView: true } argumentView)
            {
                if (transportView && layer == layers - 1)
                    return new(EvalResult<CountedResult>.Ok(default), argumentView);

                return new(new EvalError.TypeMismatch(ArgumentViewSpreadMessage) { Span = expr.Span });
            }

            var items = opened.SpreadItems();
            var capturedR = MakeCheckedSequenceCapture(ctx, items, expr.Span);
            if (capturedR.IsError) return new(capturedR.Error);

            if (layer == layers - 1)
                return new(EvalResult<CountedResult>.Ok(new CountedResult(capturedR.Value, items.Count)));

            opened = capturedR.Value;
        }

        throw new InvalidOperationException("Sequence spread must contain at least one layer.");
    }

    /// <summary>
    /// AN EXPLICIT SPREAD READS THE LEVEL IT OPENS (lazy collections, issue #204): before a star
    /// opens a list evaluated on demand, the list's positions are found and read in order
    /// (<see cref="ForceLevel"/>) and supplied as values; the items' own contents stay as they
    /// are. Otherwise exactly <see cref="OpenConcreteSpreadLayers"/>. One body for both evaluation
    /// routes. Lean: <c>peelSpreadLayers</c> over <c>forceLevel</c>, then <c>openSpreadItems</c>.
    /// </summary>
    private static async ValueTask<OpenedSpread> OpenLazySpreadLayers(
        Result value, int layers, Expr expr, EvalCtx ctx, bool transportView, bool asynchronous)
    {
        FoldTrampoline.ForkHostScope();
        var opened = value;
        for (var layer = 0; layer < layers; layer++)
        {
            // A position that fails while its level is read is that position's own failure —
            // nested, with its own frames (Q-36): the operand itself evaluated, so no operand
            // frame is added. Lean: `forceLevel` inside `peelSpreadLayers`.
            var levelR = await ForceLevel(opened, ctx, asynchronous).ConfigureAwait(FoldTrampoline.CaptureFoldContext);
            if (levelR.IsError) return new(levelR.Error);

            opened = levelR.Value;
            if (opened is Result.CallReference { IsArgumentView: true } argumentView)
            {
                if (transportView && layer == layers - 1)
                    return new(EvalResult<CountedResult>.Ok(default), argumentView);

                return new(new EvalError.TypeMismatch(ArgumentViewSpreadMessage) { Span = expr.Span });
            }

            var items = opened.SpreadItems();
            var capturedR = MakeCheckedSequenceCapture(ctx, items, expr.Span);
            if (capturedR.IsError) return new(capturedR.Error);

            if (layer == layers - 1)
                return new(EvalResult<CountedResult>.Ok(new CountedResult(capturedR.Value, items.Count)));

            opened = capturedR.Value;
        }

        throw new InvalidOperationException("Sequence spread must contain at least one layer.");
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
        var operand = PeelSpreadLayers(expr, out var layers);
        var operandR = EvalSequenceSpreadOperandValue(operand, ctx, valEnv);
        if (operandR.IsError) return operandR.Error;
        var opened = OpenSpreadLayers(operandR.Value, layers, expr, ctx, transportView: false, asynchronous: false).GetAwaiter().GetResult();
        return opened.Items;
    }

    // `ArgumentView` (CallReference S2): the view bound as the whole collection of count/first/last,
    // whose cells the builtin reads instead of a collection value (Lean `BoundSequenceBuiltinArguments.view?`).
    // `RetainedSlice` (NEED-07): a retained collector bound as the whole collection of count/first/last/take,
    // whose cells the builtin reads instead of a collection value (Lean `slice?`).
    // The callback builtins (filter, map, reduce) iterate the prepared input's items through a
    // CollectionIterationItems view made in their own dispatch arms (implementation-only, November 2026:
    // the view was made at binding for every collection builtin, 24 bytes per call that only these read).
    // `Positions` (lazy collections, issue #204): the positional source bound as the whole collection
    // of a builtin that reads positions — `map` / `filter` over any collection, and
    // `count` / `first` / `last` / `take` over a list evaluated on demand (Lean `pending?` and the
    // `collectionPositions` view).
    private readonly record struct BoundSequenceBuiltinArguments(
        PreparedSequenceBuiltinInput PreparedInput,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> SuffixArgs,
        Result.CallReference? ArgumentView = null,
        IReadOnlyList<NeedCell>? RetainedSlice = null)
    {
        public LazyList? Positions { get; init; }
    }

    /// <summary>
    /// Whether <paramref name="builtin"/> binds <paramref name="collection"/> as POSITIONS
    /// (<see cref="EvalPositionalBuiltin"/>): the two callback stages always do, and the other
    /// position readers do over a list evaluated on demand (over a concrete collection their
    /// eager form reads the same positions).
    /// </summary>
    private static bool BindsPositions(BuiltinId builtin, Result collection)
        => builtin is BuiltinId.@map or BuiltinId.@filter
            || (ReadsPositions(builtin) && collection is Result.ListValue { Lazy: not null });

    /// <summary>
    /// The call item of an argument that assembly does not evaluate: its supplied cell, its
    /// written source, and (for an argument without a cell) its algorithm. A CALLBACK
    /// position always receives this item (CALL-03 — supplying a callback evaluates
    /// nothing); a VALUE item starts from it before its one demand.
    /// </summary>
    private static VariadicCallItem UnevaluatedCallItem(ResolvedArgumentAlgorithm resolvedArg)
        => new(
            Value: null,
            resolvedArg.Algorithm,
            ValueError: null,
            resolvedArg.Source,
            Cell: resolvedArg.Cell);

    /// <summary>
    /// Prepares a filter predicate exactly as the generic filter binds its CALLBACK slot:
    /// the unevaluated call item (a callback slot is never value-evaluated merely because it
    /// was supplied, CALL-03) through the ONE suffix preparation, keeping the original
    /// callable identity. Used after fusion commits, with caller environments. The predicate
    /// keeps its supplied cell, so a callable forwarded through a parameter is projected
    /// exactly as the generic filter projects it. Evaluates nothing: an unused predicate runs
    /// no effect, draws nothing and cannot fail or recurse. Called only once the source is
    /// known to be non-empty, so a predicate with no CALLABLE identity is reported exactly
    /// where the generic filter reports it (<see cref="ResolvePreparedCallback"/>).
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
    /// The builtin's call items, evaluating NOTHING: every argument is already a supplied
    /// cell — a builtin loop step's state cells, a builtin callback's element cells, or a
    /// call's supply formed before this (<see cref="ResolveNeedSupply"/> — arbitrary
    /// explicit spreads demanded their operand there, an existing collector slice
    /// transported its cells) — and every item keeps its cell. After cardinality succeeds, each builtin demands its value
    /// controls in its established order and projects callbacks only when an invocation is
    /// required. Shared by the sync and async engines (no suspending operation). One direct
    /// array fill in argument order, so a collection-builtin call allocates no LINQ iterator
    /// here (as <see cref="ResolvedSupply"/>). Lean: <c>collectSequenceCallableCallItems</c>.
    /// </summary>
    private static IReadOnlyList<VariadicCallItem> BuildCallableCallItems(IReadOnlyList<ResolvedArgumentAlgorithm> args)
    {
        var items = new VariadicCallItem[args.Count];
        for (var i = 0; i < items.Length; i++)
            items[i] = UnevaluatedCallItem(args[i]);
        return items;
    }

    /// <summary>
    /// Call-item assembly preserves callable arguments without entering their bodies.
    /// Once binding selects a VALUE position, report its zero-argument demand using
    /// the original source — judging the callable the item NAMES
    /// (<see cref="VariadicCallItem.NamedAlgorithm"/>: a failed cell's CALLABLE projection,
    /// or a hand-built item's algorithm) — or
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
        => rejection is not null && named.HasAnyParameter
            ? ReduceInitialAccumulatorRequiresValueError(named)
            : rejection;

    /// <summary>
    /// FA-OQ-1 under M4★: when a failed slot's cell projects a structural CARRIER (an inline <c>{ F }</c>, a named
    /// <c>C = { F }</c>), the callable the slot NAMES is the carrier's VALUE terminal — the callable whose bare view
    /// the carrier's VALUE read delegated to — so the slot's rejection report, reduce's accumulator hint included
    /// (<see cref="SequenceBuiltinValueDemandError"/>), is the one its written target reference reports. The chase is
    /// the static VALUE chase (<see cref="ResolveAliasValueTerminal"/>) observed WITHOUT initiating anything
    /// (<see cref="PeekResolve{TState,T}"/>, META-S3-0b: this is diagnostic enrichment): a terminal that would need a
    /// runtime step not yet taken, a runtime terminal or a failed chase keeps the carrier. Lean: the carrier arm of
    /// <c>EvalBody.demandSequenceBuiltinCallItemValue</c>.
    /// </summary>
    private static VariadicCallItem NameCarrierValueTerminal(VariadicCallItem item, Algorithm.Alias carrier, EvalCtx ctx)
        => PeekResolve(ctx, (carrier, ctx), static state => ResolveAliasValueTerminal(state.carrier, state.ctx)) is { IsOk: true } terminal
            && !terminal.Value.IsRuntime
            ? item with { Callable = terminal.Value.Algorithm }
            : item;

    /// <summary>
    /// The outcome of demanding a slot's supplied <paramref name="cell"/>: its value, or — on an ordinary failure —
    /// the failure with the callable the slot NAMES (<see cref="VariadicCallItem.NamedAlgorithm"/>), read from the
    /// cell's CALLABLE projection WITHOUT initiating it (META-S3-0b: a runtime projection not yet completed names
    /// nothing), a carrier naming its VALUE terminal (<see cref="NameCarrierValueTerminal"/>). A parameter slot reports
    /// its parameter's own failure, and a resource limit names nothing. Never inlined: the demand that precedes it is
    /// the recursion of every nested builtin argument, so its temporaries stay out of that frame (FRAME-SIZE
    /// DISCIPLINE).
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static VariadicCallItem FinishNeedCallItemDemand(VariadicCallItem item, NeedCell cell, EvalResult<CountedResult> result, EvalCtx ctx)
    {
        if (!result.IsError) return item with { Value = result.Value.Value };
        if (item.Source is Expr.Param(var name))
            return item with { ValueError = DemandParameter(cell, result, name, item.Source.Span).Error };
        if (result.Error.IsTerminalForRun) return item with { ValueError = result.Error };
        // Diagnostic enrichment only (the message choice): a NON-INITIATING read (META-S3-0b).
        var named = item with { ValueError = result.Error, Callable = cell.PeekCallable() };
        return named.Callable is Algorithm.Alias { IsReference: false } carrier ? NameCarrierValueTerminal(named, carrier, ctx) : named;
    }

    /// <summary>
    /// Demand ONE collection-builtin call item that binding has placed in a VALUE
    /// position: the demand happens HERE, once the descriptor has decided the slot is a
    /// value — a CALLBACK item is never demanded (a CALLBACK slot receives the callable,
    /// never a value; eagerly evaluating a collecting-only callback such as
    /// <c>map(xs, Only)</c> would run its body an extra time). An item that was already
    /// evaluated, or whose evaluation already failed, is never re-entered. A supplied cell
    /// — every item the evaluator builds — is demanded once; on an ordinary failure this
    /// records the cell's CALLABLE projection as the callable the slot NAMES
    /// (<see cref="VariadicCallItem.NamedAlgorithm"/>; a carrier names its VALUE terminal,
    /// <see cref="NameCarrierValueTerminal"/>), unless the written slot is a parameter, so the
    /// slot's rejection report judges it (<see cref="SequenceBuiltinValueDemandError"/>). An
    /// item WITHOUT a cell (a hand-built plan) is evaluated through the shared demand funnel
    /// only when the ONE law accepts its callable (<see cref="AcceptsZeroArgumentValueDemand"/>
    /// — a collecting-only signature alongside every zero-parameter property); every other
    /// such item is returned untouched for <see cref="SequenceBuiltinValueDemandError"/> to
    /// report. Lean: <c>demandSequenceBuiltinCallItemValue</c>.
    /// </summary>
    private static VariadicCallItem DemandSequenceBuiltinCallItemValue(
        VariadicCallItem item,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (item.Cell is { } cell && item.Value is null && item.ValueError is null)
        {
            var result = cell.Demand();
            return FinishNeedCallItemDemand(item, cell, result, ctx);
        }

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
            : item with { Value = demandedR.Value.Value };
    }

    /// <summary>
    /// The VALUE a value control's demand established, or that demand's report: the item's
    /// retained failure, refined for <c>reduce</c>'s <c>initial</c>
    /// (<see cref="ReduceInitialRejection"/>), else the slot's own requirement. The item was
    /// demanded before (<see cref="DemandSequenceBuiltinCallItemValue"/>): at binding, or — a
    /// DEFERRED control — by the builtin when its execution needed the value; nothing is
    /// evaluated here. Lean: <c>demandedSequenceBuiltinValue</c>.
    /// </summary>
    private static EvalResult<Result> DemandedSequenceBuiltinValue(
        BuiltinId builtin,
        SequenceBuiltinSuffixArgDescriptor descriptor,
        VariadicCallItem item)
    {
        if (item.Value is not null) return EvalResult<Result>.Ok(item.Value);

        return SequenceBuiltinValueDemandError(item, reduceInitial: builtin == BuiltinId.@reduce)
            ?? new EvalError.WithContext(
                SequenceBuiltinSuffixArgErrorContext(builtin, descriptor),
                new EvalError.BadArity());
    }

    private static EvalResult<PreparedSequenceBuiltinSuffixArg> PrepareSequenceBuiltinSuffixArg(
        BuiltinId builtin,
        SequenceBuiltinSuffixArgDescriptor descriptor,
        VariadicCallItem item,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // A DEFERRED value control (reduce's initial) is retained undemanded: the builtin
        // demands it through the same law when its execution needs the value.
        if (descriptor is { Kind: SequenceBuiltinSuffixArgKind.Value, Deferred: true })
            return EvalResult<PreparedSequenceBuiltinSuffixArg>.Ok(new PreparedSequenceBuiltinSuffixArg.DeferredArg(item));

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
                        new PreparedSequenceBuiltinSuffixArg.AlgorithmArg(item.Algorithm) { WrittenSource = item.Source });
                }

            case SequenceBuiltinSuffixArgKind.Value:
                {
                    var valueR = DemandedSequenceBuiltinValue(builtin, descriptor, item);
                    return valueR.IsError
                        ? valueR.Error
                        : EvalResult<PreparedSequenceBuiltinSuffixArg>.Ok(new PreparedSequenceBuiltinSuffixArg.ValueArg(valueR.Value));
                }

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
        // A list evaluated on demand is described without reading it (issue #204).
        Result.ListValue { Lazy: { IsPending: true } } => "list value",
        Result.ListValue { Lazy: { } positions } => positions.Discovered == 0 ? "empty list value" : "list value",
        Result.ListValue(var items) when items.Count == 0 => "empty list value",
        Result.ListValue => "list value",
        Result.CallReference { IsArgumentView: true } => "argument view",
        Result.CallReference => "call reference",
    };

    private static string NumericSequenceItemErrorContext(BuiltinId builtin, int index, Result item)
        => $"{BuiltinDisplayName(builtin)} expects each collection element to be a single numeric value; item {index} was {DescribeSequenceItem(item)}";

    private static EvalError ReduceInitialAccumulatorRequiresValueError(Algorithm initialAlg)
        => new EvalError.WithContext(
            new ReduceInitialAccumulatorContext(SafeReadOnlyCollection.Over(ParameterPattern.CaptureNamesSkippingBarrenNodes(initialAlg.ParameterPatterns))),
            new EvalError.BadArity());

    /// <summary>
    /// The kept positions of one <c>distinct</c> call over <paramref name="itemCount"/> items:
    /// one bit per item, set when it is a first occurrence. Implementation-only (November 2026):
    /// the kept items used to fill a <c>List&lt;Result&gt;</c> presized to every item and were then
    /// copied into the exact list; the bit set is 1/64 of the item array and stays on the
    /// small-object heap up to about 680,000 items.
    /// </summary>
    private static ulong[] NewKeptPositions(int itemCount)
        => new ulong[(itemCount + 63) >> 6];

    private static void MarkKeptPosition(ulong[] kept, int index)
        => kept[index >> 6] |= 1UL << (index & 63);

    /// <summary>
    /// The result list of a collection builtin whose exact item count is known before its items
    /// are placed (<c>take</c>, <c>skip</c>, <c>distinct</c>, <c>order</c>, <c>orderDesc</c>,
    /// <c>atoms</c>): exactly what <see cref="MakeCollectionListResult(EvalCtx, IReadOnlyList{Result}, SourceSpan?)"/>
    /// makes of those items — the same reservation of the same count with the same span, at the same
    /// point (nothing observable happens between computing the count and placing the items) — then
    /// ONE exactly sized array that the caller fills and hands over
    /// (<see cref="HandOverListResult"/>). Implementation-only (November 2026): each of these
    /// builtins built a list of its result items and <c>MakeCollectionListResult</c> copied it again,
    /// a second 0.8 MB large-object-heap array per 100,000-item result. On a refusal no item array
    /// is allocated.
    /// </summary>
    private static EvalError? ReserveExactListItems(EvalCtx ctx, int count, out Result[] items, SourceSpan? span = null)
    {
        if (ReserveCollection(ctx, count, span) is { } error)
        {
            items = [];
            return error;
        }

        items = count == 0 ? [] : new Result[count];
        return null;
    }

    /// <summary>Takes ownership of the filled array and emits one list. The caller reserves the item count before handover.</summary>
    private static EvalResult<CountedResult> HandOverListResult(Result[] items)
        => EvalResult<CountedResult>.Ok(new CountedResult(Result.ListValue.TakeOwnership(items), 1));

    /// <summary>
    /// Evaluate a filter predicate on one item with the callback and Boolean-result rule of
    /// <c>filter</c>: the verdict step of a lazy <c>filter</c> stage (<c>FilteredList</c>) and
    /// the sequence optimizers call it, so the callback semantics are written once.
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
    /// Collect top-level sequence items as single atomic numeric values.
    /// Used by numeric ordering and aggregation builtins that only accept
    /// clearly comparable numeric elements and reject strings or sequence values.
    /// Diagnostics include the 0-based item index after counted top-level
    /// extraction so numeric shape failures are easier to debug. An element that
    /// is not one number is a present value of the wrong KIND — <c>TypeMismatch</c>
    /// (Q-27), never an arity error. Lean: <c>collectSingleAtomicNumbers</c>.
    /// <para>Every item is checked here, in index order, before the builtin reads any number, so
    /// the first non-number is the reported item exactly as before; the accepted numbers are then
    /// read through a view over the checked items (<see cref="SingleAtomicNumberItems"/>) instead
    /// of a copied list (implementation-only, November 2026).</para>
    /// </summary>
    private static EvalResult<SingleAtomicNumberItems> CollectSingleAtomicNumbers(
        BuiltinId builtin,
        IReadOnlyList<Result> elements)
    {
        for (var index = 0; index < elements.Count; index++)
        {
            var item = elements[index];
            if (item.SingleAtomicNumber() is null)
                return new EvalError.TypeMismatch(NumericSequenceItemErrorContext(builtin, index, item));
        }

        return EvalResult<SingleAtomicNumberItems>.Ok(new SingleAtomicNumberItems(elements));
    }

    private static EvalResult<PreparedSequenceBuiltinInput> PrepareSequenceBuiltinInput(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        CollectedSequenceBuiltinInput collected)
    {
        var validatedItemsR = ApplySequenceBuiltinEmptyPolicy(builtin, metadata, collected);
        if (validatedItemsR.IsError) return validatedItemsR.Error;

        SingleAtomicNumberItems? numericItems = null;
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

    /// <summary>The demanded VALUE of a collection builtin's <c>collection</c> argument, before any view.</summary>
    private static EvalResult<Result> BindSequenceBuiltinCollectionValue(
        VariadicCallItem collectionItem,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // The `collection` parameter is a VALUE position, so demand the bound item
        // through the ONE zero-argument value-demand law before reading its value.
        collectionItem = DemandSequenceBuiltinCallItemValue(collectionItem, ctx, valEnv);

        if (collectionItem.Value is null)
            return SequenceBuiltinValueDemandError(collectionItem) ?? new EvalError.BadArity();

        return EvalResult<Result>.Ok(collectionItem.Value);
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
        var items = BuildCallableCallItems(args);

        // A collection builtin is an ordinary fixed-arity callable: exactly one
        // collection argument followed by its fixed control arguments
        // (`count(collection)`, `take(collection, count)`,
        // `map(collection, mapper)`). An unspread sequence or list value is ONE
        // argument at this call boundary, exactly like at every other call
        // boundary; only explicit caller-site spread alters argument
        // boundaries, and the spread items obey the same fixed arity
        // (`count([1, 2, 3]*)` supplies three arguments and is an arity
        // error). Nothing is opened before binding.
        var expectedArgCount = 1 + metadata.SuffixArgs.Count;
        if (items.Count != expectedArgCount)
        {
            return new EvalError.ArityMismatch(expectedArgCount, items.Count)
            {
                Signature = signature,
            };
        }

        // A RETAINED COLLECTOR bound as the whole collection of a selective observer (NEED-07): its slice
        // is obtained without a VALUE demand, and the controls are demanded and validated BEFORE any
        // element (EvalRetainedCollectorBuiltin then reads the cells). Selected by the resolved builtin's
        // identity, never its spelling; every other builtin consumes the ordinary whole VALUE.
        if (ReadsRetainedCollector(builtin) && items[0].Cell is { } collectionCell && RetainedCellSlice(collectionCell) is { } retained)
        {
            var retainedControls = PrepareSequenceBuiltinControls(builtin, metadata, items, ctx, valEnv);
            return retainedControls.IsError
                ? retainedControls.Error
                : EvalResult<BoundSequenceBuiltinArguments>.Ok(new BoundSequenceBuiltinArguments(default!, retainedControls.Value, null, retained));
        }

        var collectionValueR = BindSequenceBuiltinCollectionValue(items[0], ctx, valEnv);
        if (collectionValueR.IsError) return collectionValueR.Error;
        // An argument view bound as the whole collection (CallReference S2): count/first/last read
        // its cells; every other builtin refuses it before any control argument is demanded.
        if (collectionValueR.Value is Result.CallReference { IsArgumentView: true } view)
            return ReadsArgumentView(builtin)
                ? EvalResult<BoundSequenceBuiltinArguments>.Ok(new BoundSequenceBuiltinArguments(default!, [], view))
                : ArgumentViewUnsupported(builtin);
        // LAZY COLLECTIONS (issue #204). A builtin that reads POSITIONS binds them as they are —
        // nothing is found or read here; the controls are demanded and validated first. A STRICT
        // builtin reads every position of a lazy list, in order, before its controls.
        var collectionValue = collectionValueR.Value;
        if (BindsPositions(builtin, collectionValue))
        {
            var positionalControls = PrepareSequenceBuiltinControls(builtin, metadata, items, ctx, valEnv);
            return positionalControls.IsError
                ? positionalControls.Error
                : EvalResult<BoundSequenceBuiltinArguments>.Ok(
                    new BoundSequenceBuiltinArguments(default!, positionalControls.Value) { Positions = PositionsOf(collectionValue) });
        }

        if (collectionValue is Result.ListValue { Lazy: not null })
        {
            var level = ForceLevel(collectionValue, ctx, asynchronous: false).GetAwaiter().GetResult();
            if (level.IsError) return level.Error;
            collectionValue = level.Value;
        }

        var collectionValues = BuiltinCollectionItems(collectionValue);

        var collected = new CollectedSequenceBuiltinInput(collectionValues);
        var preparedInputR = PrepareSequenceBuiltinInput(builtin, metadata, collected);
        if (preparedInputR.IsError) return preparedInputR.Error;

        var suffixArgsR = PrepareSequenceBuiltinControls(builtin, metadata, items, ctx, valEnv);
        if (suffixArgsR.IsError) return suffixArgsR.Error;

        return EvalResult<BoundSequenceBuiltinArguments>.Ok(
            new BoundSequenceBuiltinArguments(preparedInputR.Value, suffixArgsR.Value));
    }

    /// <summary>
    /// The fixed control arguments of a collection builtin, in order, each prepared by the ONE
    /// <see cref="PrepareSequenceBuiltinSuffixArg"/>; the first failure ends them. The control count is
    /// fixed by the registry metadata, so they fill an exactly sized array — the shared empty array for a
    /// builtin without controls (<c>count</c>, <c>sum</c>, <c>first</c>, …; implementation-only,
    /// November 2026: 24 bytes per call). Lean: <c>prepareControls</c>.
    /// </summary>
    private static EvalResult<IReadOnlyList<PreparedSequenceBuiltinSuffixArg>> PrepareSequenceBuiltinControls(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        IReadOnlyList<VariadicCallItem> items,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var suffixArgs = metadata.SuffixArgs.Count == 0 ? [] : new PreparedSequenceBuiltinSuffixArg[metadata.SuffixArgs.Count];
        for (var index = 0; index < suffixArgs.Length; index++)
        {
            var preparedArgR = PrepareSequenceBuiltinSuffixArg(
                builtin,
                metadata.SuffixArgs[index],
                items[1 + index],
                ctx,
                valEnv);
            if (preparedArgR.IsError) return preparedArgR.Error;

            suffixArgs[index] = preparedArgR.Value;
        }

        return EvalResult<IReadOnlyList<PreparedSequenceBuiltinSuffixArg>>.Ok(suffixArgs);
    }

    /// <summary>
    /// The builtins that observe a retained collector selectively (NEED-07): <c>count</c> reads its
    /// length, <c>first</c>/<c>last</c> demand one cell and <c>take</c> its prefix. Every other builtin
    /// consumes the ordinary whole VALUE. Lean: <c>Builtin.readsRetainedCollector</c>.
    /// </summary>
    private static bool ReadsRetainedCollector(BuiltinId builtin)
        => builtin is BuiltinId.@count or BuiltinId.@first or BuiltinId.@last or BuiltinId.@take;

    /// <summary>
    /// SELECTIVE OBSERVATION OF A RETAINED COLLECTOR (November 2026; NEED-07): <c>count</c>, <c>first</c>,
    /// <c>last</c> and <c>take</c> over the collector's exact slice, read as positions and never
    /// materialized, so no whole list is reserved or built. <c>count</c> reads the slice's length and
    /// demands nothing; <c>first</c>/<c>last</c> report the ordinary empty-collection failure or demand
    /// exactly one cell, selected through the ordinary value boundary; <c>take</c> demands exactly the
    /// prefix its ALREADY VALIDATED count keeps (<see cref="TakeLength"/>), in source order, and reserves
    /// only that list. Every demand is the element's own cell, so its outcome is shared with every other
    /// read and with a later whole VALUE. Lean: <c>retainedCollectorBuiltin</c>.
    /// </summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalRetainedCollectorBuiltin(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> suffixArgs,
        IReadOnlyList<NeedCell> slice,
        EvalCtx ctx,
        bool asynchronous)
    {
        FoldTrampoline.ForkHostScope();
        if (RetainedObservationTerminal(ctx) is { } entry)
            return entry;
        if (builtin == BuiltinId.@count)
            return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(slice.Count), 1));

        if (builtin == BuiltinId.@take)
        {
            var countR = ExpectPreparedWholeNumberSuffixArg(builtin, metadata.SuffixArgs, suffixArgs, 0);
            if (countR.IsError) return countR.Error;
            var length = TakeLength(countR.Value, slice.Count);
            // The prefix fills the exact array that becomes the list (implementation-only, November 2026:
            // it filled a List<Result> of this length that the list then copied). The list is reserved
            // after the last demand and the terminal check, as before, with the same count.
            var taken = length == 0 ? [] : new Result[length];
            for (var index = 0; index < length; index++)
            {
                var element = await DemandCell(slice[index], asynchronous).ConfigureAwait(FoldTrampoline.CaptureFoldContext);
                if (element.IsError) return element.Error;
                taken.AsSpan()[index] = element.Value.Value;
            }
            if (RetainedObservationTerminal(ctx) is { } afterPrefix)
                return afterPrefix;
            return ReserveCollection(ctx, length) is { } limitError ? limitError : HandOverListResult(taken);
        }

        if (slice.Count == 0)
            return ArgumentViewEmptySelection(builtin);
        var selected = await DemandCell(slice[builtin == BuiltinId.@first ? 0 : slice.Count - 1], asynchronous).ConfigureAwait(FoldTrampoline.CaptureFoldContext);
        if (selected.IsError) return selected.Error;
        return RetainedObservationTerminal(ctx) is { } afterElement ? afterElement : CountValue(selected.Value.Value);
    }

    /// <summary>
    /// The prepared control at <paramref name="index"/>, when the metadata declares that position
    /// as <paramref name="expectedKind"/> and it was prepared as that kind (<typeparamref name="TArg"/>);
    /// any mismatch is an internal metadata error. Shared by the per-kind readers below, so a read
    /// allocates no closure or delegate.
    /// </summary>
    private static EvalResult<TArg> ExpectPreparedSequenceBuiltinSuffixArgAt<TArg>(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> args,
        int index,
        SequenceBuiltinSuffixArgKind expectedKind)
        where TArg : PreparedSequenceBuiltinSuffixArg
    {
        if (descriptors.Count != args.Count)
        {
            return InternalSequenceBuiltinSuffixArgMetadataError<TArg>(
                builtin,
                "mismatched suffix arguments");
        }

        if ((uint)index >= (uint)descriptors.Count)
        {
            return InternalSequenceBuiltinSuffixArgMetadataError<TArg>(
                builtin,
                $"expected suffix argument {index + 1} to have metadata kind {DescribeSequenceBuiltinSuffixArgKind(expectedKind)}");
        }

        var descriptor = descriptors[index];
        if (descriptor.Kind != expectedKind)
        {
            return InternalSequenceBuiltinSuffixArgMetadataError<TArg>(
                builtin,
                $"expected suffix argument {index + 1} ({descriptor.Name}) to have metadata kind {DescribeSequenceBuiltinSuffixArgKind(expectedKind)}, but found {DescribeSequenceBuiltinSuffixArgKind(descriptor.Kind)}");
        }

        return args[index] is TArg prepared
            ? EvalResult<TArg>.Ok(prepared)
            : InternalSequenceBuiltinSuffixArgMetadataError<TArg>(
                builtin,
                $"prepared suffix argument {index + 1} ({descriptor.Name}) did not match metadata kind {DescribeSequenceBuiltinSuffixArgKind(expectedKind)}");
    }

    /// <summary>
    /// The CALLBACK a sequence builtin invokes from an algorithm suffix slot (the
    /// <c>filter</c> predicate, the <c>map</c> mapper, the <c>reduce</c> reducer): the
    /// argument's supplied cell's CALLABLE projection (or, for an argument without a cell,
    /// its <see cref="PreparedSequenceBuiltinSuffixArg.AlgorithmArg.AlgorithmValue"/>),
    /// through the ONE invoking-slot rule (<see cref="ProjectInvokingSlot"/>) only once the
    /// builtin is about to invoke it (a non-empty collection).
    /// Lean: <c>expectPreparedSequenceBuiltinAlgorithmSuffixArg</c>.
    /// </summary>
    private static EvalResult<Algorithm> ResolvePreparedCallback(BuiltinId builtin, PreparedSequenceBuiltinSuffixArg.AlgorithmArg arg)
        => ProjectInvokingSlot(arg.Cell, arg.AlgorithmValue, InvokingSlotRoles.Of(builtin), arg.WrittenSource?.Span);

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
    /// positioned at the current written argument occurrence when known (META-DIAG-2), with
    /// the cell's original span as fallback, and raised before any invocation is charged.
    /// A failure originating inside the projection keeps its own provenance. A slot that HAS callable
    /// identity keeps every ordinary binder verdict when it is invoked (a zero-parameter
    /// callable given an item is <c>ArityMismatch</c>). Lean: <c>projectInvokingSlot</c>.
    /// </summary>
    private static EvalResult<Algorithm> ProjectInvokingSlot(NeedCell? cell, Algorithm? invoked, string role, SourceSpan? span)
    {
        var projected = cell is not null ? cell.ProjectCallable() : EvalResult<Algorithm?>.Ok(invoked);
        if (projected.IsError) return projected.Error;
        return projected.Value is { } callable
            ? EvalResult<Algorithm>.Ok(callable)
            : new EvalError.NotAnAlgorithm(role) { Span = span ?? cell?.Span };
    }

    private static EvalResult<Algorithm> ExpectPreparedAlgorithmSuffixArg(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> args,
        int index)
    {
        var callbackR = ExpectPreparedSequenceBuiltinSuffixArgAt<PreparedSequenceBuiltinSuffixArg.AlgorithmArg>(
            builtin, descriptors, args, index, SequenceBuiltinSuffixArgKind.Algorithm);
        return callbackR.IsError ? callbackR.Error : ResolvePreparedCallback(builtin, callbackR.Value);
    }

    private static EvalResult<Decimal128> ExpectPreparedWholeNumberSuffixArg(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> args,
        int index)
    {
        var countR = ExpectPreparedSequenceBuiltinSuffixArgAt<PreparedSequenceBuiltinSuffixArg.WholeNumberArg>(
            builtin, descriptors, args, index, SequenceBuiltinSuffixArgKind.WholeNumber);
        return countR.IsError ? countR.Error : EvalResult<Decimal128>.Ok(countR.Value.WholeNumberValue);
    }

    private static EvalResult<Result> ExpectPreparedValueSuffixArg(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> args,
        int index)
    {
        var valueR = ExpectPreparedSequenceBuiltinSuffixArgAt<PreparedSequenceBuiltinSuffixArg.ValueArg>(
            builtin, descriptors, args, index, SequenceBuiltinSuffixArgKind.Value);
        return valueR.IsError ? valueR.Error : EvalResult<Result>.Ok(valueR.Value.ResultValue);
    }

    /// <summary>
    /// The undemanded call item of a DEFERRED value control: the builtin demands it itself
    /// (<see cref="DemandSequenceBuiltinCallItemValue"/>, then
    /// <see cref="DemandedSequenceBuiltinValue"/>). Lean:
    /// <c>expectPreparedSequenceBuiltinDeferredSuffixArg</c>.
    /// </summary>
    private static EvalResult<VariadicCallItem> ExpectPreparedDeferredSuffixArg(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> args,
        int index)
    {
        var deferredR = ExpectPreparedSequenceBuiltinSuffixArgAt<PreparedSequenceBuiltinSuffixArg.DeferredArg>(
            builtin, descriptors, args, index, SequenceBuiltinSuffixArgKind.Value);
        return deferredR.IsError ? deferredR.Error : EvalResult<VariadicCallItem>.Ok(deferredR.Value.Item);
    }

    private static EvalResult<SingleAtomicNumberItems> ExpectPreparedNumericItems(
        BuiltinId builtin,
        PreparedSequenceBuiltinInput prepared)
    {
        if (prepared.NumericItems is { } numbers)
            return EvalResult<SingleAtomicNumberItems>.Ok(numbers);

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
        SingleAtomicNumberItems numbers)
    {
        // Decimal128.CompareTo is a total order over every value, including the IEEE
        // specials: NaN sorts before every other value (mirroring double), the
        // infinities take the extremes, and -0 compares equal to 0. The sort is STABLE
        // like Lean's insertion sort (`sortIntsAsc`): equal-comparing values keep their
        // written order, which is observable through the quantum and zero sign that
        // display preserves (`order((1.0, 1))` is `[1.0, 1]` however long the input) and
        // must not depend on the runtime sort algorithm.
        return MakeSortedNumberListResult(ctx, numbers, descending: false);
    }

    /// <summary>
    /// Sort the input positions by the validated numbers, breaking ties by position.
    /// Reserve the result after sorting, where the budget also checks for cancellation,
    /// then write one fresh atom per item in the ascending order or its exact reverse.
    /// Dense whole numbers take a counting sort instead (<see cref="DenseWholeNumberBucketStarts"/>),
    /// with the same order, reservation point and result.
    /// </summary>
    private static EvalResult<CountedResult> MakeSortedNumberListResult(
        EvalCtx ctx,
        SingleAtomicNumberItems numbers,
        bool descending)
    {
        if (DenseWholeNumberBucketStarts(numbers, out var lowest) is { } bucketStarts)
            return MakeBucketSortedNumberListResult(ctx, numbers, bucketStarts, lowest, descending);

        var positions = new int[numbers.Count];
        for (var i = 0; i < positions.Length; i++)
            positions[i] = i;
        if (positions.Length > 1)
            Array.Sort(positions, new StableNumberOrder(numbers));

        if (ReserveExactListItems(ctx, positions.Length, out var items) is { } error)
            return error;
        for (var i = 0; i < positions.Length; i++)
        {
            var position = positions[descending ? positions.Length - 1 - i : i];
            items[i] = new Result.Atom(numbers[position]);
        }
        return HandOverListResult(items);
    }

    /// <summary>
    /// The bucket starts of a stable counting sort, when every number is a whole number in
    /// <see cref="int"/> range and the values span no more integers than there are items;
    /// otherwise <see langword="null"/>, and the comparison sort runs. Bucket <c>k</c> holds the
    /// value <c>lowest + k</c> and starts at the result index stored for it.
    /// <see cref="Decimal128.CompareTo(Decimal128)"/> orders whole numbers by their integer values
    /// and makes equal values compare equal (<c>1</c> and <c>1.0</c>, <c>0</c> and <c>-0</c>), so
    /// filling each bucket in input order is exactly the stable order. The bucket array is never
    /// longer than the position array of the comparison sort.
    /// <para>Implementation-only (November 2026). Over 100,000 dense whole numbers (sorted,
    /// reversed, permuted, or repeated, some spelled like <c>1.0</c>) the comparison sort took
    /// 23–47 ms and this takes 2.5–4.5 ms. Other inputs pay for the check until it fails, at
    /// most one conversion per item: within 5% of the comparison sort alone, as measured.</para>
    /// </summary>
    private static int[]? DenseWholeNumberBucketStarts(SingleAtomicNumberItems numbers, out int lowest)
    {
        lowest = 0;
        var count = numbers.Count;
        if (count < 2)
            return null;

        int low = int.MaxValue, high = int.MinValue;
        for (var i = 0; i < count; i++)
        {
            // The conversion saturates and truncates, so the round trip holds exactly for whole
            // numbers in int range, -0 included; NaN and the infinities fail it.
            var value = numbers.AtomAt(i).Value;
            var whole = (int)value;
            if ((Decimal128)whole != value)
                return null;
            if (whole < low) low = whole;
            if (whole > high) high = whole;
            if ((long)high - low >= count)
                return null;
        }

        var starts = new int[high - low + 1];
        for (var i = 0; i < count; i++)
            starts[(int)numbers.AtomAt(i).Value - low]++;
        var next = 0;
        for (var bucket = 0; bucket < starts.Length; bucket++)
        {
            var size = starts[bucket];
            starts[bucket] = next;
            next += size;
        }

        lowest = low;
        return starts;
    }

    /// <summary>
    /// The counting sort's result, reserved where the comparison sort reserves it: after every
    /// number has been read for the order. Each input atom takes its bucket's next ascending
    /// index (mirrored for <c>orderDesc</c>), then one fresh atom of the same number replaces it in
    /// result order, as the comparison sort writes them.
    /// </summary>
    private static EvalResult<CountedResult> MakeBucketSortedNumberListResult(
        EvalCtx ctx,
        SingleAtomicNumberItems numbers,
        int[] bucketStarts,
        int lowest,
        bool descending)
    {
        var count = numbers.Count;
        if (ReserveExactListItems(ctx, count, out var items) is { } error)
            return error;

        var slots = items.AsSpan();
        for (var i = 0; i < count; i++)
        {
            var atom = numbers.AtomAt(i);
            var slot = bucketStarts[(int)atom.Value - lowest]++;
            slots[descending ? count - 1 - slot : slot] = atom;
        }
        for (var i = 0; i < count; i++)
            slots[i] = new Result.Atom(((Result.Atom)slots[i]).Value);
        return HandOverListResult(items);
    }

    private sealed class StableNumberOrder(SingleAtomicNumberItems numbers) : IComparer<int>
    {
        public int Compare(int left, int right)
        {
            var order = numbers.AtomAt(left).Value.CompareTo(numbers.AtomAt(right).Value);
            return order != 0 ? order : left.CompareTo(right);
        }
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
        SingleAtomicNumberItems numbers)
    {
        // Lean `sortIntsDesc`: the reverse of the stable ascending order.
        return MakeSortedNumberListResult(ctx, numbers, descending: true);
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
    ///
    /// <para>The scan stops at the first match. Its comparisons share ONE operation comparer
    /// (SEC-02, <see cref="Result.CreateOperationComparer"/>): the same value equality as
    /// <see cref="Result.ValueComparer"/>, with equality knowledge (classes of equal references, unequal pairs) reused
    /// across the whole scan and the walks' work charged to the run's budget.</para>
    /// </summary>
    private static EvalResult<CountedResult> EvalContainsCounted(
        EvalCtx ctx,
        IReadOnlyList<Result> items,
        Result searchedItem)
    {
        var comparer = Result.CreateOperationComparer(ctx.Budget, ctx.Observations?.StructuralTraversal);
        bool found;
        try
        {
            found = ContainsItem(comparer, items, searchedItem);
        }
        catch (StructuralWorkRefusedException refused)
        {
            return refused.Error;
        }

        if (comparer.CompleteOperation() is { } error)
            return error;

        return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Bool(found), 1));
    }

    // The scans live outside the protected regions so the tiered JIT can promote their loops by
    // on-stack replacement within one long builtin call (measured: a 100,000-item flat scan inside
    // the try block stayed in unoptimized code for the whole call).
    private static bool ContainsItem(Result.ValueSemanticComparer comparer, IReadOnlyList<Result> items, Result searchedItem)
    {
        for (var i = 0; i < items.Count; i++)
        {
            if (comparer.Equals(items[i], searchedItem))
                return true;
        }

        return false;
    }

    /// <summary>
    /// Marks first occurrences in input order. Small inputs keep the ordinary BCL set.
    /// For a large input, grow storage with the number of distinct keys actually observed.
    /// </summary>
    private static int KeepFirstOccurrences(Result.ValueSemanticComparer comparer, IReadOnlyList<Result> items, ulong[] firstOccurrences)
    {
        // A BCL set smaller than this input threshold fits in small-object storage.
        if (items.Count >= 4_000)
            return MarkDistinctPositions(comparer, items, firstOccurrences);

        var seen = new HashSet<Result>(comparer);
        for (var i = 0; i < items.Count; i++)
        {
            if (seen.Add(items[i]))
                MarkKeptPosition(firstOccurrences, i);
        }
        return seen.Count;
    }

    private static int MarkDistinctPositions(IEqualityComparer<Result> comparer, IReadOnlyList<Result> items, ulong[] firstOccurrences)
    {
        var seen = new DistinctPositionSet();
        for (var i = 0; i < items.Count; i++)
        {
            if (seen.Add(items, i, comparer))
                MarkKeptPosition(firstOccurrences, i);
        }
        return seen.Count;
    }

    // An append-only set over immutable input positions. A slot stores both one bucket head
    // and one entry. Links are one-based, with zero marking the end of a chain. Pages keep
    // entries off the large-object heap and stay in place when the bucket count doubles.
    private sealed class DistinctPositionSet
    {
        private const int PageSize = 1024;
        private struct Slot
        {
            public int Head, Next, Hash, Position;
        }

        private Slot[][] pages = [new Slot[4]];
        private int capacity = 4;
        internal int Count { get; private set; }

        private ref Slot At(int i) => ref pages[i / PageSize][i % PageSize];
        private int Bucket(int hash) => hash & (capacity - 1);

        internal bool Add(IReadOnlyList<Result> items, int position, IEqualityComparer<Result> comparer)
        {
            var item = items[position];
            var hash = item is null ? 0 : comparer.GetHashCode(item);
            var bucket = Bucket(hash);
            for (int link = At(bucket).Head; link != 0;)
            {
                ref var entry = ref At(link - 1);
                if (entry.Hash == hash && comparer.Equals(items[entry.Position], item))
                    return false;
                link = entry.Next;
            }

            if (Count == capacity)
            {
                Grow();
                bucket = Bucket(hash);
            }

            ref var added = ref At(Count);
            ref var head = ref At(bucket).Head;
            added.Hash = hash;
            added.Position = position;
            added.Next = head;
            head = ++Count;
            return true;
        }

        private void Grow()
        {
            capacity *= 2;
            if (capacity <= PageSize)
                Array.Resize(ref pages[0], capacity);
            else
            {
                var previous = pages.Length;
                Array.Resize(ref pages, capacity / PageSize);
                for (var i = previous; i < pages.Length; i++)
                    pages[i] = new Slot[PageSize];
            }

            // Re-bucket stored hashes in insertion order. As in HashSet, an Add compares
            // equal raw hashes newest first, including across resizes, with no comparer
            // calls during rehash. The value comparer supplies the mixed hash.
            for (var i = 0; i < Count; i++)
                At(i).Head = 0;
            for (var i = 0; i < Count; i++)
            {
                ref var entry = ref At(i);
                ref var head = ref At(Bucket(entry.Hash)).Head;
                entry.Next = head;
                head = i + 1;
            }
        }
    }

    /// <summary>
    /// Evaluate <c>distinct(collection)</c> by removing later duplicate top-level
    /// items while preserving the original order of first occurrence, then
    /// materializing the kept items as one list value.
    /// Duplicate detection follows KatLang value
    /// semantics, so atoms compare by numeric value, strings by exact string
    /// value, and sequence/list values structurally by their elements.
    ///
    /// <para>Every hash and duplicate comparison shares ONE operation comparer (SEC-02,
    /// <see cref="Result.CreateOperationComparer"/>): node hashes and equality knowledge are reused
    /// across the whole collection, and the walks' work is charged to the run's budget before
    /// the kept items are materialized.</para>
    /// <para>The first occurrences are recorded as kept positions (<see cref="NewKeptPositions"/>)
    /// and their exact list is reserved and filled once, in source order
    /// (<see cref="ReserveExactListItems"/>; implementation-only, November 2026).</para>
    /// </summary>
    private static EvalResult<CountedResult> EvalDistinctCounted(
        EvalCtx ctx,
        IReadOnlyList<Result> items)
    {
        var firstOccurrences = NewKeptPositions(items.Count);
        var comparer = Result.CreateOperationComparer(ctx.Budget, ctx.Observations?.StructuralTraversal);
        int keptCount;
        try
        {
            keptCount = KeepFirstOccurrences(comparer, items, firstOccurrences);
        }
        catch (StructuralWorkRefusedException refused)
        {
            return refused.Error;
        }

        if (comparer.CompleteOperation() is { } error)
            return error;

        if (ReserveExactListItems(ctx, keptCount, out var distinctItems) is { } limitError)
            return limitError;

        var next = 0;
        for (var wordIndex = 0; wordIndex < firstOccurrences.Length; wordIndex++)
        {
            for (var bits = firstOccurrences[wordIndex]; bits != 0; bits &= bits - 1)
                distinctItems[next++] = items[(wordIndex << 6) + BitOperations.TrailingZeroCount(bits)];
        }

        return HandOverListResult(distinctItems);
    }

    /// <summary>
    /// Evaluate <c>first(collection)</c> by SELECTING the first top-level
    /// collection element: the element is returned exactly as stored and
    /// re-counted through the ordinary value boundary (<see cref="CountValue(Result)"/>),
    /// exactly like <c>collection[0]</c> — a selected sequence or list stays one
    /// value, a selected <c>()</c> emits zero values, and only an explicit
    /// spread opens the selection. An empty collection has no position to
    /// select: <c>BadIndex</c>, the outcome of <c>collection[0]</c> (SEQ-04, Q-27;
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
    /// <see cref="EvalFirstCounted"/> and <c>collection[count(collection) - 1]</c>.
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
        => MakeCollectionSliceListResult(ctx, items, 0, TakeLength(count, items.Count));

    /// <summary>
    /// The <c>take</c>/<c>skip</c> result: the <paramref name="length"/> items from
    /// <paramref name="start"/>, in order, reserved and copied once into the exact array that
    /// becomes the list (<see cref="ReserveExactListItems"/>). A whole collection is copied in bulk.
    /// </summary>
    private static EvalResult<CountedResult> MakeCollectionSliceListResult(
        EvalCtx ctx,
        IReadOnlyList<Result> items,
        int start,
        int length)
    {
        if (ReserveExactListItems(ctx, length, out var slice) is { } error)
            return error;

        if (length > 0 && length == items.Count && items is ICollection<Result> whole)
        {
            whole.CopyTo(slice, 0);
        }
        else
        {
            // Through a span: a store into the Result[] itself pays a covariant array-store check per item.
            var destination = slice.AsSpan();
            for (var i = 0; i < destination.Length; i++)
                destination[i] = items[start + i];
        }

        return HandOverListResult(slice);
    }

    /// <summary>
    /// THE length of the prefix <c>take</c> keeps of <paramref name="available"/> items, values or a
    /// retained collector's cells alike: nothing for a non-positive count, all items for an oversized
    /// one. Saturates before narrowing: <paramref name="count"/> is a validated whole number that may
    /// exceed <see cref="int.MaxValue"/>, and an oversized count means "all items" by specification, so
    /// it must never reach the host (int) conversion. Lean: <c>takePrefix</c>.
    /// </summary>
    private static int TakeLength(Decimal128 count, int available)
        => count <= 0 ? 0 : count >= available ? available : (int)count;

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
        var skipped = count <= 0 ? 0 : count >= items.Count ? items.Count : (int)count;

        return MakeCollectionSliceListResult(ctx, items, skipped, items.Count - skipped);
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
        SingleAtomicNumberItems numbers)
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
        SingleAtomicNumberItems numbers)
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
    private static Decimal128 SumNumbers(SingleAtomicNumberItems numbers)
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
    private static Decimal128 SumNumbers(SingleAtomicNumberItems numbers, bool noteExactness, out bool provablyExact)
    {
        Decimal128 total = Decimal128.Zero;
        var totalQuantumExponent = 0; // Decimal128.Zero's
        provablyExact = noteExactness;
        // Indexed, left to right: the numbers are read from the checked items (SingleAtomicNumberItems).
        for (var index = 0; index < numbers.Count; index++)
        {
            var numeric = numbers[index];
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
    private static EvalResult<CountedResult> EvalSumCounted(SingleAtomicNumberItems numbers)
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
    private static EvalResult<CountedResult> EvalAvgCounted(SingleAtomicNumberItems numbers)
    {
        if (numbers.Count == 0)
            return new EvalError.IllegalInEval("avg requires a non-empty collection");

        var total = SumNumbers(numbers, noteExactness: true, out var provablyExact);
        var average = provablyExact || HasNonFiniteNumber(numbers)
            ? total / numbers.Count
            : AverageFiniteNumbersExactly(numbers, total);

        return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(average), 1));
    }

    private static bool HasNonFiniteNumber(SingleAtomicNumberItems numbers)
    {
        for (var index = 0; index < numbers.Count; index++)
        {
            if (!Decimal128.IsFinite(numbers[index]))
                return true;
        }

        return false;
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
    private static Decimal128 AverageFiniteNumbersExactly(SingleAtomicNumberItems numbers, Decimal128 sequentialTotal)
    {
        var coefficientsByExponent = new Dictionary<int, BigInteger>();
        var minimumExponent = 0; // the zero the left-to-right sum starts from
        var nonzeroMinimumExponent = int.MaxValue;

        for (var index = 0; index < numbers.Count; index++)
        {
            var number = numbers[index];
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

        if (boundR.Value.ArgumentView is { } argumentView)
            return EvalArgumentViewBuiltin(builtin, argumentView, ctx);
        if (boundR.Value.RetainedSlice is { } retainedSlice)
            return EvalRetainedCollectorBuiltin(builtin, metadata, boundR.Value.SuffixArgs, retainedSlice, ctx, asynchronous: false).GetAwaiter().GetResult();
        // POSITIONS READ ON DEMAND (issue #204): `map` and `filter` build their lazy stage, and
        // `count` / `first` / `last` / `take` read a lazy list's positions.
        if (boundR.Value.Positions is { } positions)
            return EvalPositionalBuiltin(builtin, metadata, boundR.Value.SuffixArgs, positions, ctx, valEnv, asynchronous: false).GetAwaiter().GetResult();
        // An ordinary call: the view, slice and position routes have returned above.
        var (preparedInput, suffixArgs, _, _) = boundR.Value;
        // The callback arm iterates these items through a CollectionIterationItems view made in the arm.
        var collectionItems = preparedInput.FlattenedItems;

        // `contains` and `distinct` compare WHOLE values (issue #204): the collection's positions
        // were read at binding (one level); here every item, in order, and then the searched value
        // are materialized.
        if (builtin is BuiltinId.@contains or BuiltinId.@distinct && ctx.Budget.HasLazyLists)
        {
            var comparedR = MaterializeComparedOperands(builtin, preparedInput, suffixArgs, ctx, asynchronous: false).GetAwaiter().GetResult();
            if (comparedR.IsError) return comparedR.Error;
            (preparedInput, suffixArgs) = comparedR.Value;
        }

        // Only the callback-driven builtin left on this route (reduce) is dispatched here, because
        // the asynchronous twin awaits exactly it. Every other builtin goes to the shared
        // ApplyValueSequenceBuiltinCounted, which both twins call.
        switch (builtin)
        {
            case BuiltinId.@reduce:
                {
                    // `initial` is a DEFERRED control: binding retained the supplied computation
                    // undemanded, and the fold demands it when it reaches its start.
                    var initialR = ExpectPreparedDeferredSuffixArg(builtin, metadata.SuffixArgs, suffixArgs, 1);
                    if (initialR.IsError) return initialR.Error;
                    // An empty collection demands the start once and returns its value; the fold
                    // finishes without projecting the reducer.
                    if (collectionItems.Count == 0)
                        return EvalReduceInitial(initialR.Value, metadata.SuffixArgs[1], ctx, valEnv);

                    var stepR = ExpectPreparedAlgorithmSuffixArg(builtin, metadata.SuffixArgs, suffixArgs, 0);
                    if (stepR.IsError) return stepR.Error;

                    return EvalReduceCounted(
                        new CollectionIterationItems(collectionItems),
                        stepR.Value,
                        initialR.Value,
                        metadata.SuffixArgs[1],
                        ctx,
                        valEnv,
                        asynchronous: false).GetAwaiter().GetResult();
                }

            default:
                return ApplyValueSequenceBuiltinCounted(builtin, metadata.SuffixArgs, preparedInput, suffixArgs, args.Count, ctx);
        }
    }

    /// <summary>
    /// The sequence builtins that take no callback (<c>order</c>, <c>orderDesc</c>, <c>count</c>,
    /// <c>contains</c>, <c>distinct</c>, <c>first</c>, <c>last</c>, <c>take</c>, <c>skip</c>,
    /// <c>min</c>, <c>max</c>, <c>sum</c>, <c>avg</c>) over an ordinary bound call, and the arity
    /// error of any other builtin. None of them suspends, so <see cref="ApplyBuiltinCountedSequence"/>
    /// and its asynchronous twin both call this ONE switch and keep only their callback arms
    /// (<c>filter</c>, <c>map</c>, <c>reduce</c>). A numeric builtin checks its prepared numeric
    /// items before its handler runs. A builtin with a control checks it before reading the items.
    /// Out of line so that these arms' locals stay out of the twins' frames.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> ApplyValueSequenceBuiltinCounted(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> descriptors,
        PreparedSequenceBuiltinInput preparedInput,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> suffixArgs,
        int argumentCount,
        EvalCtx ctx)
    {
        switch (builtin)
        {
            case BuiltinId.@order:
                {
                    var numbersR = ExpectPreparedNumericItems(builtin, preparedInput);
                    if (numbersR.IsError) return numbersR.Error;

                    return EvalOrderCounted(ctx, numbersR.Value);
                }

            case BuiltinId.@orderDesc:
                {
                    var numbersR = ExpectPreparedNumericItems(builtin, preparedInput);
                    if (numbersR.IsError) return numbersR.Error;

                    return EvalOrderDescCounted(ctx, numbersR.Value);
                }

            case BuiltinId.@count:
                return EvalCountCounted(preparedInput.FlattenedItems);

            case BuiltinId.@contains:
                {
                    var searchedItemR = ExpectPreparedValueSuffixArg(builtin, descriptors, suffixArgs, 0);
                    if (searchedItemR.IsError) return searchedItemR.Error;

                    return EvalContainsCounted(ctx, preparedInput.FlattenedItems, searchedItemR.Value);
                }

            case BuiltinId.@distinct:
                return EvalDistinctCounted(ctx, preparedInput.FlattenedItems);
            case BuiltinId.@first:
                return EvalFirstCounted(preparedInput.FlattenedItems);
            case BuiltinId.@last:
                return EvalLastCounted(preparedInput.FlattenedItems);

            case BuiltinId.@take:
                {
                    var countR = ExpectPreparedWholeNumberSuffixArg(builtin, descriptors, suffixArgs, 0);
                    if (countR.IsError) return countR.Error;

                    return EvalTakeCounted(ctx, preparedInput.FlattenedItems, countR.Value);
                }

            case BuiltinId.@skip:
                {
                    var countR = ExpectPreparedWholeNumberSuffixArg(builtin, descriptors, suffixArgs, 0);
                    if (countR.IsError) return countR.Error;

                    return EvalSkipCounted(ctx, preparedInput.FlattenedItems, countR.Value);
                }

            case BuiltinId.@min:
                {
                    var numbersR = ExpectPreparedNumericItems(builtin, preparedInput);
                    if (numbersR.IsError) return numbersR.Error;

                    return EvalMinCounted(numbersR.Value);
                }

            case BuiltinId.@max:
                {
                    var numbersR = ExpectPreparedNumericItems(builtin, preparedInput);
                    if (numbersR.IsError) return numbersR.Error;

                    return EvalMaxCounted(numbersR.Value);
                }

            case BuiltinId.@sum:
                {
                    var numbersR = ExpectPreparedNumericItems(builtin, preparedInput);
                    if (numbersR.IsError) return numbersR.Error;

                    return EvalSumCounted(numbersR.Value);
                }

            case BuiltinId.@avg:
                {
                    var numbersR = ExpectPreparedNumericItems(builtin, preparedInput);
                    if (numbersR.IsError) return numbersR.Error;

                    return EvalAvgCounted(numbersR.Value);
                }

            default:
                return WrongBuiltinArity(builtin, argumentCount);
        }
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
    /// through this funnel: its value outcome is established once, by its supplied cell's
    /// first VALUE demand, and every read reuses it (AT-MOST-ONCE ARGUMENT VALUE EVALUATION,
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
    /// The receiver is demanded for its VALUE with zero arguments. A <c>Param</c> bound to a
    /// supplied cell is a VALUE demand of that cell and nothing else (CALL-06): its first
    /// demand evaluates the written argument once, and the outcome is reported exactly as
    /// that argument reports it — <c>Show(v) = v.string</c> / <c>Show(Inc)</c> is Inc's
    /// property-context arity error, <c>Show({ x + 1 })</c> the block's
    /// <see cref="EvalError.UnresolvedImplicitParams"/>, a clause family its own
    /// <see cref="EvalError.NoMatchingBranch"/> — the report every other read of the
    /// parameter gives, never one re-judged against the parameter's callable. Every other
    /// receiver is judged by the ONE zero-argument value-demand law
    /// (<see cref="ZeroArgumentValueDemandError"/>) from the resolved receiver's signature
    /// BEFORE its body is entered: <c>Inc.string</c> with <c>Inc(x)</c> is the property
    /// arity error, a navigated parameterized member the bare one, a written parameterized
    /// block <see cref="EvalError.UnresolvedImplicitParams"/>, and an inline callable alias
    /// <c>{ Inc }.string</c> its written target reference's report (the property arity
    /// error, FA-OQ-1) — never <c>Unknown name: x</c> from inside the receiver. An ALIAS receiver
    /// (OD-E, M4★) is judged on its VALUE terminal's algorithm (<paramref name="demandAlg"/>) while it is
    /// READ as the alias, so every shape reaches the TERMINAL binding's cached entry — an inline carrier
    /// <c>{ F }</c> through the demand funnel's alias arm — exactly as the value position reads it. Lean:
    /// the <c>string</c> arm of <c>evalDotCallCounted</c> (<c>hasSuppliedParameterCell</c>) and
    /// <c>evalDotStringReceiverValue</c>.
    /// </summary>
    private static EvalResult<Result> EvalDotStringReceiverAlgOutput(
        Expr target,
        Algorithm targetAlg,
        bool receiverIsStructuralMember,
        EvalCtx ctx,
        ValEnv valEnv,
        Algorithm? demandAlg = null)
    {
        // A parameter bound to a supplied cell is a VALUE demand of that cell, reported as the
        // written argument reports it, before (and instead of) the zero-argument law (CALL-06).
        // Lean: `hasSuppliedParameterCell` in the `string` arm of `evalDotCallCounted`.
        if (target is Expr.Param(var needName) && LookupNeed(ParameterContext(needName, ctx, ref valEnv).NeedEnv, needName) is not null)
            return ProjectCountedValue(EvalParamCounted(needName, target.Span, ctx, valEnv));

        if (ZeroArgumentValueDemandError(target, demandAlg ?? targetAlg) is { } rejection)
            return rejection;

        // The accepted receiver is READ exactly as a value position reads it: HOW A
        // PROPERTY VALUE IS CONSUMED DOES NOT AFFECT CACHING, so `A.string` converts the
        // very value `A` reads, `Obj.A.string` the value `Obj.A` reads, and `v.string` the
        // value a parameter was bound to. Lean: evalDotStringReceiverValue.
        switch (target)
        {
            case Expr.Param(var name):
                // The ordinary value-position PARAMETER read (a parameter with a supplied
                // cell returned above): its counted or bound VALUE when it has one (a
                // forwarded property value is never re-run through the parameter's algorithm
                // channel), and BadArity for a binding that has only an algorithm channel,
                // which is never evaluated — exactly as the value-position read `a` reports it.
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

        var resolvedR = LookupLexicalRaw(ctx.CallStack[0], name, ctx);
        if (resolvedR.IsError)
            return AtSpanIfMissing(resolvedR.Error, target.Span);

        // OD-E (M4★): a receiver reached THROUGH an alias reads its VALUE terminal — the terminal binding's
        // entry, or a runtime-target alias's binding cell — out of this frame.
        if (resolvedR.Value.ResolvedAlgorithm is Algorithm.Alias)
            return EvalAliasDotStringLexicalReceiver(target, resolvedR.Value, ctx, valEnv);

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
                // A member that is an alias reads its VALUE terminal (OD-E, M4★): never an entry of its own.
                if (ChildOfInContext(containerR.Value, member.Value, ctx) is Algorithm.Alias memberAlias)
                {
                    var terminal = ResolveAliasValueTerminal(memberAlias, ctx, member);
                    return terminal.IsError ? terminal.Error : ProjectCountedValue(ReadAliasTerminalCounted(terminal.Value, ctx, valEnv));
                }

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
    /// Demand a builtin argument slot for its VALUE with zero explicit arguments. A slot
    /// with a supplied cell is that cell's demand (its completed outcome is reused).
    /// Otherwise the ONE zero-argument value-demand law (<see cref="ZeroArgumentValueDemandError"/>)
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
        if (arg.Algorithm is not { } algorithm)
            return new EvalError.BadArity();
        // An argument without a cell (a hand-built plan): the ONE law judges its algorithm
        // before any body is entered, and the accepted demand evaluates it.
        if (ZeroArgumentValueDemandError(arg.Source, algorithm) is { } rejection)
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
            // the parameter's failure, exactly as a value-position read reports it — so only
            // when it is the argument's own (IsOwnForBlame); a nested one keeps the span only.
            Expr.Param(var name) => result.Error is EvalError.MissingOutput missing && IsOwnForBlame(missing)
                ? WithSpan<CountedResult>(source.Span, new EvalError.WithContext(new ParameterEvaluationContext(name), result.Error))
                : WithSpan(source.Span, result),
            // F5: a written block, capture, call, selection, or operator expression has no
            // name to report. Blaming the written argument is what keeps `count({ })` from
            // reading as though `count` itself had no output — or as though the source had
            // been the argumentless `count()`.
            _ => BlameWrittenArgumentForMissingOutput(source, result.Error),
        };
    }

    /// <summary>
    /// The algorithm a <c>while</c>/<c>repeat</c> step INVOKES: the step argument's supplied
    /// cell's CALLABLE projection (or, for an argument without a cell, its
    /// <see cref="ResolvedArgumentAlgorithm.Algorithm"/>), so a step forwarded through a
    /// parameter is the callable itself, never its demanded value — projected through the ONE
    /// invoking-slot rule (<see cref="ProjectInvokingSlot"/>) only when an iteration needs it,
    /// and positioned at the step argument. Lean: <c>projectInvokingSlot</c> over
    /// <c>invokeNeed step</c>.
    /// </summary>
    private static EvalResult<Algorithm> ProjectLoopStep(ResolvedArgumentAlgorithm step, BuiltinId loop)
        => ProjectInvokingSlot(step.Cell, step.Algorithm, InvokingSlotRoles.Of(loop), step.Source?.Span);

    private static EvalResult<Result> EvalResolvedArgument(
        ResolvedArgumentAlgorithm arg,
        EvalCtx ctx,
        ValEnv valEnv)
        => ProjectCountedValue(EvalResolvedArgumentCounted(arg, ctx, valEnv));

    // A builtin always has output, so a missing output escaping an application is an argument's, a
    // callback's or a step's: EVERY caller nests it (`NestMissingOutput`, Q-36; Lean: inside
    // `applyBuiltinCounted`), keeping this recursive frame unchanged.
    private static EvalResult<CountedResult> ApplyBuiltinCountedResolved(
        BuiltinId builtin,
        IReadOnlyList<ResolvedArgumentAlgorithm> resolvedArgs,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (GetSequenceBuiltinMetadata(builtin) is { } metadata)
            return ApplyBuiltinCountedSequence(builtin, metadata, resolvedArgs, ctx, valEnv);

        // The arguments are supplied cells: a call's supply (explicit spreads already
        // opened at formation, ResolveNeedSupply), a loop step's state cells, or a
        // callback's element cells.
        var args = resolvedArgs;

        // A builtin declaring a META parameter binds through the ONE binder first (META-S3-3).
        if (BuiltinRegistry.GetBuiltin(builtin) is { DeclaresMetaParameter: true } metaBuiltin)
            return ApplyMetaBuiltinCounted(metaBuiltin, args, ctx, valEnv, asynchronous: false).GetAwaiter().GetResult();

        switch (builtin, args.Count)
        {
            // `tick()`: the accepted zero-argument call executes the primitive once. Any supplied
            // argument falls to the default arm's arity rejection before anything is demanded.
            case (BuiltinId.@tick, 0):
                return ExecuteTick(ctx);

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

            case (BuiltinId.@atoms, 1):
                {
                    var atomsR = EvalResolvedArgument(args[0], ctx, valEnv);
                    if (atomsR.IsError) return atomsR.Error;
                    // `atoms` reads the WHOLE value (issue #204): every position of every list it
                    // holds is read first, left to right and depth first.
                    var wholeR = MaterializeValue(atomsR.Value, ctx, asynchronous: false).GetAwaiter().GetResult();
                    if (wholeR.IsError) return wholeR.Error;
                    // `atoms` materializes a collection: one list
                    // of the recursively collected numeric atoms (sequence AND
                    // list boundaries open; strings and Booleans contribute no atoms).
                    return MakeLanguageAtomsResult(ctx, wholeR.Value);
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
