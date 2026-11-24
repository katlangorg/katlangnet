namespace KatLang.Evaluation;

/// <summary>
/// THE EVALUATOR'S FLOW-LOCAL STATE where the host has suppressed <see cref="ExecutionContext"/> flow
/// (November 2026, finding <c>async-route-suppressed-flow-cycle-self-join-hang</c> of the adversarial
/// performance audit of 2026-11-21; C#-only host-execution policy, no Lean counterpart).
///
/// <para><b>The state.</b> Two values describe where a logical flow of evaluation is: the wait-for
/// node whose computation it is running (<see cref="NeedNode"/>, NEED-09 — the parent of the flow's
/// next demand, and what a re-entrant demand is recognized by) and the invocation plans whose supply
/// it is preparing (<c>Evaluator.PreparingInvocations</c>, what a re-entrant preparation is recognized
/// by). Both live in the logical context (<see cref="AsyncLocal{T}"/>), because a fork started inside
/// a computation must inherit them and an unrelated flow must not. Everything else of the wait-for
/// graph is explicit: the edges, the flights and each observation's own parent.</para>
///
/// <para><b>The hazard.</b> The runtime carries the logical context across a suspension only when
/// flow is not suppressed. An <c>async</c> method that suspends while the host has suppressed flow
/// captures no context: its continuation runs in whatever context the resuming thread has, an
/// ancestor's continuation likewise, including one the runtime queues to the thread pool when the
/// resuming stack is low. The flow then no longer knows its node. A demand cycle is read as an
/// unrelated demand, joins its own flight and never completes, whatever the run's cancellation
/// token does; a re-entrant plan preparation waits for itself the same way.</para>
///
/// <para><b>The rule.</b> Flow-local state is established only where the context flows, and a
/// continuation the evaluator schedules itself receives it explicitly:</para>
/// <list type="bullet">
///   <item>An asynchronous need-cell computation (VALUE or runtime CALLABLE projection) and an
///   invocation-initiated plan preparation of the asynchronous family first continue on the thread
///   pool when <see cref="IsSuppressed"/> holds (a <see cref="StackHop"/>). The method installing
///   the node or preparation frame awaits the hop directly. Its execution context then carries
///   that identity through further awaits.</item>
///   <item>A <see cref="StackHop"/> and a fold's trampoline (<see cref="FoldTrampoline"/>) give their
///   continuation the state themselves when the context does not (<see cref="CaptureIfSuppressed"/>):
///   the hop's queued work starts in an empty context, and a trampoline item queued without a context
///   starts in its drain loop's. A synchronous run's fold pump runs with flow restored, so its own
///   items carry their contexts.</item>
/// </list>
///
/// <para><b>What a host observes.</b> Under a flowing context nothing changes: no hop is added and
/// nothing is captured. A computation or preparation that takes this hop runs on a worker
/// without the caller's ambient state. A host operation reached there can observe the thread
/// and context change even when its awaitable completes synchronously. The hop itself does no
/// language work and consumes no budget. The synchronous routes never suspend, so they need no hop; only
/// the twins a long fold continues on under its pump do (<see cref="FoldTrampoline"/>), and that pump
/// restores flow while it runs and resumes their hops itself. A deferred region's held gate turn
/// (<see cref="DeferredModuleRegion"/>) is deliberately not part of this state: the host contract of
/// <see cref="RunOptions.DownloadCode"/> defines it by the execution context, and suppressing flow is
/// that contract's way out of it.</para>
/// </summary>
internal static class EvaluationFlow
{
    /// <summary>
    /// Whether the host has suppressed execution-context flow on the current thread: an
    /// <c>async</c> method that suspends now captures no context. An observation only.
    /// </summary>
    internal static bool IsSuppressed => ExecutionContext.IsFlowSuppressed();

    /// <summary>
    /// The current flow's state for a continuation that will start in an empty context, or
    /// <c>null</c> when the context flows (the runtime carries it) or the state is the default one
    /// (an empty context already holds it).
    /// </summary>
    internal static Handover? CaptureIfSuppressed()
    {
        if (!ExecutionContext.IsFlowSuppressed()) return null;
        var node = NeedNode.FlowNode;
        var preparing = Evaluator.FlowPreparingInvocations;
        return node is null && preparing is null ? null : new Handover(node, preparing);
    }

    /// <summary>One flow's state, handed to a continuation the execution context does not reach.</summary>
    internal sealed class Handover(NeedNode? node, Evaluator.InvocationPreparationFrame? preparing)
    {
        /// <summary>
        /// Makes the current thread's context continue the captured flow. The caller owns that
        /// context: a thread-pool work item, or a fold segment inside its saved execution context.
        /// </summary>
        internal void Install()
        {
            NeedNode.FlowNode = node;
            Evaluator.FlowPreparingInvocations = preparing;
        }
    }
}
