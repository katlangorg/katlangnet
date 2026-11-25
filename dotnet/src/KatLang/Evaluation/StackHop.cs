using System.Runtime.CompilerServices;

namespace KatLang.Evaluation;

/// <summary>
/// The async twin route's STACK HOP (2026-11-14; C#-only host-execution policy under Q-09a, no Lean
/// counterpart). Awaiting it always suspends the awaiting twin and resumes it on a thread-pool thread,
/// so evaluation continues on a FRESH host stack instead of stopping with
/// <see cref="EvalError.EvaluationStackExhausted"/>.
///
/// <para><b>Where.</b> Only the asynchronous twin family awaits it, and only as
/// <c>if (StackHop.HostStackIsLow()) await new StackHop();</c> immediately before one of the
/// probes it shares with the synchronous family: before a twin enters
/// <see cref="EvaluationBudget.TryEnterInvocation"/> or
/// <see cref="EvaluationBudget.TryEnterArgumentEvaluation"/>, at the head of the two twin
/// row-loop funnels, before a <see cref="NeedCell"/>'s asynchronous VALUE or runtime
/// CALLABLE computation, and before a loop that will run a round passes its entry probe
/// (<see cref="EvaluationBudget.TryAdmitLoopEntry"/>; that site is ONE body with an
/// <c>asynchronous</c> flag, <c>Evaluator.EvalNeedLoop</c>, so the hop is guarded by the flag).
/// Each hop site is marked TWIN-ONLY. Synchronous helpers a twin calls (alias
/// chases, receiver and open navigation, sync-delegated leaves) keep their own probes, so they
/// can still reach the backstop.</para>
///
/// <para><b>Why it changes no run's meaning.</b> <see cref="HostStackIsLow"/> holds wherever the
/// probe that follows the hop would fail (it tests <see cref="ChokepointMargin"/> bytes deeper than
/// its caller, below the chokepoint helpers that run that probe), so a twin reaches the shared
/// probe's failure only on a fresh stack that is itself low; otherwise it holds only within that
/// margin of the reserve. The hop itself evaluates nothing, charges nothing, and reads no limit or
/// configuration (Q-09b): value, evaluation order, effects, random draws, budgets and cancellation
/// chokepoints are those of the same run without the hop. A run that hops completes asynchronously;
/// before the hop existed it would have stopped with <see cref="EvalError.EvaluationStackExhausted"/>
/// (or, at an invocation chokepoint, with the limit verdict that chokepoint still reports first),
/// unless it came within the margin of the reserve without reaching it. Once hopping, invocation
/// recursion is bounded by the deterministic <see cref="EvaluationLimits.MaxDepth"/>, as for a twin that
/// genuinely suspends before descending. Recursion routed through LOOP STEPS charges no depth, so on
/// this route its active levels can accumulate on the heap across hops. A finite
/// <see cref="EvaluationLimits.MaxSteps"/> bounds the rounds executed. A separate limit on loop
/// nesting is an open owner decision. The hop happens at most once per site
/// visit, so a fresh stack that is still low falls through to the probe and its structured error.</para>
///
/// <para><b>Suppressed flow.</b> A second condition makes a twin hop, at three sites only: a
/// <see cref="NeedCell"/>'s asynchronous VALUE or runtime CALLABLE computation and an
/// invocation-initiated plan preparation hop when the host has suppressed
/// <see cref="ExecutionContext"/> flow (<see cref="EvaluationFlow.IsSuppressed"/>), because the
/// flow-local state they install must be installed where the context flows
/// (<see cref="EvaluationFlow"/>). Thread-pool work runs with flow not suppressed, so it happens at
/// most once per suppressed stretch of a run, and never under a flowing context. Like every hop it
/// evaluates and charges nothing.</para>
///
/// <para><b>Held state.</b> The awaiting flow keeps its <see cref="ExecutionContext"/>, so every
/// <see cref="AsyncLocal{T}"/> it reads — the <see cref="NeedCell"/> wait-for graph, the invocation
/// preparation frames, a deferred region's held gate turn — resumes with it. Where the host has
/// suppressed flow there is no context to keep: the hop then hands the wait-for node and the
/// preparation frames to its continuation itself (<see cref="EvaluationFlow.CaptureIfSuppressed"/>),
/// and nothing else, so a held gate turn and the host's own ambient state do not follow, as
/// suppression asks. No hop site is reached
/// while thread-affine state is held: a <c>lock</c> cannot span an await, and a non-initiating
/// <see cref="NeedCell"/> observation (the one <c>[ThreadStatic]</c> scope) is synchronous and refuses
/// asynchronous starts. Plan-preparation markers, need-cell flights and the loader's materialization
/// gate are awaitable (<see cref="TaskCompletionSource"/>, <see cref="SemaphoreSlim"/>), which a
/// genuine suspension already holds across awaits.</para>
///
/// <para><b>A synchronous run's fold pump.</b> Where a synchronous run continues a long <c>reduce</c>
/// fold on the heap (<see cref="FoldTrampoline"/>), the twins run on the calling thread under that
/// fold's pump, and nothing may leave it: <see cref="HostStackIsLow"/> answers <c>false</c> there, so a
/// twin takes no hop for the host stack and the probe after the site decides, as on the synchronous
/// family (genuine recursion inside a reducer reaches the structured
/// <see cref="EvalError.EvaluationStackExhausted"/> or the depth limit), and a hop that suppressed flow
/// asks for is resumed by the pump on the same thread, with the same hand-over.</para>
///
/// <para><b>Hosts.</b> The continuation is queued to the thread pool, never to a captured
/// <see cref="SynchronizationContext"/> or <see cref="TaskScheduler"/>, and the
/// evaluator captures only a fold's private scheduling context, so a host that blocks on a deep run from a
/// single-threaded context does not deadlock where the runtime has a thread pool. A run that hops
/// completes asynchronously even when nothing else suspends; blocking on such a run on a host
/// without worker threads (browser WebAssembly) stays unsupported, as it already is for genuinely
/// asynchronous operations.</para>
/// </summary>
internal readonly struct StackHop : ICriticalNotifyCompletion
{
    /// <summary>
    /// How far below its caller <see cref="HostStackIsLow"/> tests the runtime's reserve. A hop site
    /// tests in the twin's own frame, but the probe it guards at an invocation chokepoint runs two
    /// small helper frames deeper (<c>Evaluator.TryEnterDynamicInvocation</c> or
    /// <c>Evaluator.TryEnterArgumentEvaluationLevel</c>, then the <see cref="EvaluationBudget"/>
    /// enter). An exact test left a window of a few hundred bytes where the check passed and that
    /// probe then failed: a full-suite run reported <see cref="EvalError.EvaluationStackExhausted"/>
    /// at the call <c>wait(F(n - 1))</c> on a 1 MiB thread. One KiB covers those frames several
    /// times over in Debug and Release; it is a fixed amount of host stack, never a limit.
    /// </summary>
    internal const int ChokepointMargin = 1024;

    /// <summary>
    /// Whether the current thread's remaining stack is below the runtime's execution reserve — the
    /// condition under which <see cref="RuntimeHelpers.TryEnsureSufficientExecutionStack"/> refuses —
    /// measured <see cref="ChokepointMargin"/> bytes below the caller, so it holds wherever the probe
    /// after a hop site would fail, and otherwise only within that margin of it. An observation only:
    /// no side effect and no charge, and it depends on the host stack alone.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    internal static bool HostStackIsLow()
    {
        // A synchronous run's fold pump (FoldTrampoline) takes no hop for the host stack: the probe after
        // the site decides, as on the synchronous family, and nothing leaves the calling thread.
        if (FoldTrampoline.IsPumping) return false;
        Span<byte> margin = stackalloc byte[ChokepointMargin];
        return IsBelowReserve(margin);
    }

    // Receives the margin so the allocation stays live; it tests the reserve from below it.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static bool IsBelowReserve(Span<byte> margin) => !RuntimeHelpers.TryEnsureSufficientExecutionStack();

    /// <summary>The awaiter is the hop itself.</summary>
    public StackHop GetAwaiter() => this;

    /// <summary>A skipped hop, for callers that choose whether their own continuation must move.</summary>
    internal static StackHop Skipped => new() { IsCompleted = true };

    /// <summary>A requested hop always suspends the method awaiting it.</summary>
    public bool IsCompleted { get; private init; }

    /// <summary>Resuming a hop yields nothing and cannot fail.</summary>
    public void GetResult()
    {
    }

    /// <summary>
    /// Queues the continuation to the thread pool, flowing the current <see cref="ExecutionContext"/>.
    /// Where the host has suppressed flow there is none to flow, and the continuation receives the
    /// evaluator's flow-local state instead (<see cref="QueueWithHandover"/>). On a thread that pumps a
    /// synchronous run's fold (<see cref="FoldTrampoline"/>) the pump resumes it instead, on that thread.
    /// </summary>
    public void OnCompleted(Action continuation)
    {
        if (FoldTrampoline.TryPostHop(continuation)) return;
        if (EvaluationFlow.CaptureIfSuppressed() is { } handover)
            QueueWithHandover(handover, continuation);
        else
            ThreadPool.QueueUserWorkItem(static run => run(), continuation, preferLocal: false);
    }

    /// <summary>
    /// Queues the continuation to the thread pool without capturing the context: the async method
    /// builder's continuation restores the awaiting method's own <see cref="ExecutionContext"/>.
    /// Where the host has suppressed flow the builder captured none, and the continuation receives
    /// the evaluator's flow-local state instead (<see cref="QueueWithHandover"/>). On a thread that
    /// pumps a synchronous run's fold (<see cref="FoldTrampoline"/>) the pump resumes it instead, on
    /// that thread, with the same state.
    /// </summary>
    public void UnsafeOnCompleted(Action continuation)
    {
        if (FoldTrampoline.TryPostHop(continuation)) return;
        if (EvaluationFlow.CaptureIfSuppressed() is { } handover)
            QueueWithHandover(handover, continuation);
        else
            ThreadPool.UnsafeQueueUserWorkItem(static run => run(), continuation, preferLocal: false);
    }

    // The hop of a flow whose context does not flow (EvaluationFlow): the work item starts in the
    // pool's empty context, installs the flow's node and preparation frames there, and then runs
    // the continuation, so the flow continues with them and with nothing else of the host's. The
    // pool resets a worker's context after every work item, so nothing leaks to later work.
    private static void QueueWithHandover(EvaluationFlow.Handover handover, Action continuation)
        => ThreadPool.UnsafeQueueUserWorkItem(static resumed =>
        {
            resumed.handover.Install();
            resumed.continuation();
        }, (handover, continuation), preferLocal: false);
}
