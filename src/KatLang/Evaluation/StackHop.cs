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
/// row-loop funnels, and before a <see cref="NeedCell"/>'s asynchronous VALUE or runtime
/// CALLABLE computation. Each such site is marked TWIN-ONLY beside its <c>// MIRROR OF</c>
/// counterpart; the synchronous family never hops. Synchronous helpers a twin calls (alias
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
/// genuinely suspends before descending. The hop happens at most once per site visit, so a fresh
/// stack that is still low falls through to the probe and its structured error.</para>
///
/// <para><b>Held state.</b> The awaiting flow keeps its <see cref="ExecutionContext"/>, so every
/// <see cref="AsyncLocal{T}"/> it reads — the <see cref="NeedCell"/> wait-for graph, the invocation
/// preparation frames, a deferred region's held gate turn — resumes with it. No hop site is reached
/// while thread-affine state is held: a <c>lock</c> cannot span an await, and a non-initiating
/// <see cref="NeedCell"/> observation (the one <c>[ThreadStatic]</c> scope) is synchronous and refuses
/// asynchronous starts. Plan-preparation markers, need-cell flights and the loader's materialization
/// gate are awaitable (<see cref="TaskCompletionSource"/>, <see cref="SemaphoreSlim"/>), which a
/// genuine suspension already holds across awaits.</para>
///
/// <para><b>Hosts.</b> The continuation is queued to the thread pool, never to a captured
/// <see cref="SynchronizationContext"/> or <see cref="TaskScheduler"/>, and every await of the
/// library uses <c>ConfigureAwait(false)</c>, so a host that blocks on a deep run from a
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
        Span<byte> margin = stackalloc byte[ChokepointMargin];
        return IsBelowReserve(margin);
    }

    // Receives the margin so the allocation stays live; it tests the reserve from below it.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static bool IsBelowReserve(Span<byte> margin) => !RuntimeHelpers.TryEnsureSufficientExecutionStack();

    /// <summary>The awaiter is the hop itself.</summary>
    public StackHop GetAwaiter() => this;

    /// <summary>Never complete: awaiting a hop always suspends.</summary>
    public bool IsCompleted => false;

    /// <summary>Resuming a hop yields nothing and cannot fail.</summary>
    public void GetResult()
    {
    }

    /// <summary>Queues the continuation to the thread pool, flowing the current <see cref="ExecutionContext"/>.</summary>
    public void OnCompleted(Action continuation)
        => ThreadPool.QueueUserWorkItem(static run => run(), continuation, preferLocal: false);

    /// <summary>
    /// Queues the continuation to the thread pool without capturing the context: the async method
    /// builder's continuation restores the awaiting method's own <see cref="ExecutionContext"/>.
    /// </summary>
    public void UnsafeOnCompleted(Action continuation)
        => ThreadPool.UnsafeQueueUserWorkItem(static run => run(), continuation, preferLocal: false);
}
