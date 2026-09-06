using KatLang.Evaluation;

namespace KatLang;

/// <summary>
/// Budget chokepoint scopes: the ONE definition of each balanced dynamic-depth
/// protocol an evaluation strategy may enter around a re-entered algorithm body.
/// Part of the <see cref="Evaluator"/> partial class.
///
/// <para>The loop planner replaces three generic chokepoints: a builtin ARGUMENT level
/// (<see cref="EvalArgumentAlgOutputCounted"/>:
/// depth only), a zero-argument PROPERTY ACCESS (<see cref="GetOrEvaluateZeroArgPropertyResult"/>:
/// one invocation, entered before the cache is consulted), and a USER CALL
/// (<see cref="EvalUserCallCounted"/>: one invocation). The loop optimizer replaces
/// those constructs with planned nodes (<c>LoopExprPlan.If</c>, <c>TempSlot</c>,
/// <c>TempCall</c>) that never reach the generic sites, so their charges used to be
/// re-implemented — or, as the B3 review found, omitted — beside them. Every such site,
/// generic or planned, synchronous or async twin, now enters its level through one of
/// the two <c>TryEnter…</c> helpers below and releases it by disposing the returned
/// <see cref="BudgetLevel"/> from a <c>using</c>: the charge, the non-mutating
/// rejection, the limit-error span stamping, and the exactly-once release are defined
/// once and cannot drift apart. Dynamic depth is an always-active budget with a verdict
/// on every run, which is why the strategies must be EQUALIZED rather than one of them
/// forced (see <see cref="EvaluationBudget.HasConfiguredMaterializationLimit"/> and
/// <c>BudgetCrossTalkMatrixTests</c>).</para>
///
/// <para>The helpers are deliberately NOT delegate-taking wrappers. A wrapper adds
/// frames to every user-call level, and the per-level stack cost of that spine is what
/// calibrates the deterministic depth ceiling
/// (<see cref="EvaluationLimits.MaxSupportedDepth"/>) against the stack backstop on the
/// smallest supported stack — two extra Debug frames per level were enough to turn a
/// runaway recursion's deterministic depth verdict into a stack verdict on an ordinary
/// test thread. Entering through a call that returns before the body runs, and
/// releasing through a struct's <c>Dispose</c>, leaves the calling frame the only frame
/// on the spine — exactly the inline <c>try</c>/<c>finally</c> it replaces.</para>
/// </summary>
public static partial class Evaluator
{
    /// <summary>
    /// One admitted budget level, released exactly once by <see cref="Dispose"/> — always
    /// from a <c>using</c>, so the release runs on success, structured failure, and
    /// exceptional unwind alike (in an async twin the <c>using</c> spans the await, so a
    /// suspended seam unwinds through it too). A level that was NOT admitted is the
    /// default value and releases nothing: a rejected enter mutated nothing, so there is
    /// nothing to undo.
    /// </summary>
    internal readonly struct BudgetLevel : IDisposable
    {
        private readonly EvaluationBudget? _budget;

        private BudgetLevel(EvaluationBudget budget) => _budget = budget;

        internal static BudgetLevel Admitted(EvaluationBudget budget) => new(budget);

        public void Dispose() => _budget?.ExitInvocation();
    }

    /// <summary>
    /// Enters ONE depth-only argument-evaluation level
    /// (<see cref="EvaluationBudget.TryEnterArgumentEvaluation"/>): the protocol of every
    /// builtin argument and control argument — a planned <c>if</c> condition or selected
    /// branch charges exactly this, per argument, like the generic
    /// <see cref="EvalArgumentAlgOutputCounted"/> funnel it replaces. Returns the
    /// structured limit error — UNSPANNED, with nothing mutated and
    /// <paramref name="level"/> empty — when the level is refused; otherwise <c>null</c>
    /// and the admitted level, which the caller MUST dispose from a <c>using</c>.
    /// </summary>
    internal static EvalError? TryEnterArgumentEvaluationLevel(EvalCtx ctx, out BudgetLevel level)
    {
        if (ctx.Budget.TryEnterArgumentEvaluation() is { } limitError)
        {
            level = default;
            return limitError;
        }

        level = BudgetLevel.Admitted(ctx.Budget);
        return null;
    }

    /// <summary>
    /// Enters ONE charged dynamic invocation (<see cref="EvaluationBudget.TryEnterInvocation"/>:
    /// one step, one depth level): the protocol of a user call and of a zero-argument
    /// property access (entered BEFORE the property cache is consulted, so a cache hit and
    /// a miss charge the same access). A refused enter is stamped with
    /// <paramref name="limitSpan"/> when it carries no span of its own
    /// (<see cref="AtSpanIfMissing"/>), mutates nothing, and leaves
    /// <paramref name="level"/> empty; an admitted invocation is returned as the level the
    /// caller MUST dispose from a <c>using</c>.
    /// </summary>
    internal static EvalError? TryEnterDynamicInvocation(EvalCtx ctx, SourceSpan? limitSpan, out BudgetLevel level)
    {
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
        {
            level = default;
            return AtSpanIfMissing(limitError, limitSpan);
        }

        level = BudgetLevel.Admitted(ctx.Budget);
        return null;
    }

    /// <summary>
    /// The span a REJECTED user-call enter is stamped with: the first written argument's
    /// span, or <c>null</c> for an argumentless call (the enclosing call-expression
    /// boundary then attaches the call's own span). Shared by
    /// <see cref="EvalUserCallCounted"/>, its async twin, and the planned temp call so the
    /// stamping rule exists once.
    /// </summary>
    internal static SourceSpan? UserCallLimitSpan(OutputBundle args)
        => FirstSpan(args);
}
