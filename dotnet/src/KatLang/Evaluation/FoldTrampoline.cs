using System.Runtime.CompilerServices;
using System.Runtime.ExceptionServices;
using System.Threading.Tasks.Sources;

namespace KatLang.Evaluation;

/// <summary>
/// THE HEAP-RESIDENT CONTINUATIONS OF ONE <c>reduce</c> FOLD (lazy <c>reduce</c> accumulators, issue #203;
/// single-thread fold progress, November 2026; C#-only host-execution policy under Q-09a, no Lean
/// counterpart). A step that demands its accumulator stays suspended while the preceding step runs, and
/// that step may demand its own accumulator in turn: a fold whose reducer uses every accumulator holds one
/// suspended step per element. Nested on the host stack, that chain grows the stack with the length of the
/// fold. This trampoline keeps the chain on the heap instead and runs it on the thread that demands it.
///
/// <para><b>Segments.</b> The computation of one accumulator — the start, or the step over the element
/// before it — is a SEGMENT (<see cref="FoldSegment"/>). A segment runs on the asynchronous twin family, so a
/// step that demands its own accumulator suspends as heap state machines (it returns to its caller instead
/// of waiting on the stack). The demand of a segment from inside another segment never runs it nested: it
/// QUEUES the segment here and returns a pending value task, and the demanding step suspends at its demand
/// site. The trampoline's DRAIN LOOP then starts the queued segment from its own frame. When a segment ends,
/// its outcome is delivered to the step that demanded it by queueing that step's continuation, never by
/// running it inside the completing segment. So the native stack holds the drain loop and ONE step's own
/// frames, at descent and at completion alike, however long the fold is; every suspended step is heap
/// state. The order is exactly the nested order: at any time one chain can run — the newest demand's
/// segment on the way down, the step whose accumulator just completed on the way up — so the queue holds at
/// most one item of a fold's own descent or ascent.</para>
///
/// <para><b>Who drains.</b> Whoever queues work while no drain loop of this trampoline runs becomes its
/// drain loop, on its own thread, and drains until nothing is queued: the first accumulator demand of the
/// fold, or a continuation resumed after a genuine asynchronous suspension. Work queued while a drain loop
/// runs is left to it. The asynchronous twin route therefore needs no thread and no thread pool for the
/// length of a fold: a fold whose steps never genuinely suspend runs entirely on the thread that demanded
/// it. A step that genuinely suspends (an asynchronous host operation, an awaited module download) unwinds
/// to the drain loop, which finds nothing queued and returns; the demand that started it hands its caller a
/// pending task, and the step's own awaitable later resumes it on whatever thread completes it, where its
/// next demand or completion drains the trampoline again.</para>
///
/// <para><b>The synchronous route</b> (<see cref="TryRunSynchronously"/>). The synchronous evaluator keeps
/// a short chain on the host stack: at most <see cref="HostStackAllowance"/> fold continuations nested on one
/// thread, and no more than <see cref="HostStackByteAllowance"/> of its stack. Beyond it, an accumulator
/// demand continues its fold here, with the asynchronous twins as the
/// segments, and PUMPS: the calling thread drains until the demanded segment has completed and returns its
/// outcome. It is the drain loop described above, run to completion on the calling thread, which never hands
/// evaluator work to another thread. While it pumps: the run carries a host exception or a cancellation by value (the
/// asynchronous twin run's boundary, <see cref="EvaluationBudget.CarriesHostTermination"/>, opened and closed
/// here, and the retained exception rethrown on the calling thread as the same object); no twin takes a
/// <see cref="StackHop"/> to the thread pool — a hop that the host stack would ask for falls through to the
/// probe it guards, so genuine recursion inside a reducer reaches the structured
/// <see cref="EvalError.EvaluationStackExhausted"/> or the depth limit as on the synchronous family, and a
/// hop that suppressed flow asks for is resumed by this pump; and execution-context flow is not suppressed
/// (a host that suppressed it gets it back suppressed), because the heap continuations carry their flow in
/// the execution context.</para>
///
/// <para><b>Inline resumptions</b> (the cost of a heap step, November 2026). A suspended step is a chain of
/// suspended state machines, one per evaluator frame between the step and its accumulator read (about eighteen
/// for a reducer such as <c>if(item &gt; acc, item, acc)</c>), and each one waits for the frame below it. A
/// pump resumes them INLINE where it safely can: the frames register their continuations directly (no
/// synchronization context captured, so no continuation object or delegate per frame), and when the step's
/// accumulator completes, the runtime resumes them one inside the other in the pump's completion cascade, as
/// any completed task's continuations run. The runtime does so only under the default task scheduler, with no
/// synchronization context current, and with enough stack below the completing frame; elsewhere it would send
/// the continuation to the thread pool. So a pump resumes inline only where all three hold for every cascade
/// it runs (<see cref="TryRunSynchronously"/>): it starts under the default scheduler and finds the headroom
/// below itself that the deepest admitted cascade needs; it runs its work with no synchronization context; and
/// a step suspends inline only from the pump's own segment start, whose cascade the pump runs from its own
/// frame, and only for its frames within <see cref="InlineResumeByteAllowance"/> and
/// <see cref="InlineResumeFrameAllowance"/> of the demand. Every other suspension in such a pump — a frame
/// beyond the allowances, a step that suspends again after resuming, a demand of another trampoline, a stack
/// hop, a joined flight — registers POSTED resumptions (<see cref="BeginPostingUnwinding"/>): each suspending
/// frame captures a pump context, chosen per unwinding and installed by <see cref="CaptureFoldContext"/> for
/// that frame alone, because the method builder restores a frame's caller's context when the frame suspends.
/// Posted frames that no inline frame waits above capture the CASCADING context: what they are posted runs in
/// it, so they resume one inside the other wherever the runtime can inline them, as in every other pump. Only a
/// resumed inline step that suspends again leaves inline frames waiting above posting ones; its posting frames
/// capture the per-frame context, each resumes from the queue with no context current, and the inline frames
/// above resume inline from there. The work that inline frames may wait above runs with no context current
/// (each segment's waiting step records how it registered; <see cref="RegistersBelowInlineFrames"/>). Every
/// other pump, and every drain loop of the asynchronous route, runs its work in its scheduling context, which
/// every evaluator await captures, as before. Only where a frame resumes differs, never what it computes
/// (<c>FoldInlineResumptionTests</c>).</para>
///
/// <para><b>Why it changes no run's meaning.</b> A segment is exactly the computation the demanding frame
/// would have run in place, started at the demand and finished before the demanding step resumes: value,
/// evaluation order, effects, random draws, budgets, limit verdicts and cancellation chokepoints are those of
/// the nested evaluation, and the twin family is the synchronous family's pinned mirror. Each segment starts
/// under the demanding flow's execution context, so the wait-for node, the invocation preparation frames and
/// the host's ambient state (NEED-09, <see cref="EvaluationFlow"/>) are the demander's; each resumed step
/// continues under its own. Evaluator awaits inside a drain loop capture its private scheduling
/// context, except where a pump resumes inline (above). Deferred continuations are posted back to the calling
/// thread, including when the runtime declines to inline at low stack. Each step keeps its own host execution
/// and synchronization contexts for synchronous callbacks. A genuine suspension returns to its caller and
/// resumes the queue on completion.</para>
/// </summary>
internal sealed class FoldTrampoline
{
    /// <summary>
    /// How many fold continuations the synchronous evaluator keeps nested on one thread's stack before an
    /// accumulator demand continues its fold on the heap (<see cref="HostStackByteAllowance"/> can stop the
    /// chain earlier): a short fold never leaves the synchronous family. A fixed count of host frames per
    /// thread, never a limit; it bounds the chain on the host stack on every platform, however its stack
    /// addresses behave.
    /// </summary>
    internal const int HostStackAllowance = 16;

    /// <summary>
    /// How far below the thread's outermost in-place accumulator demand the chain may reach before a demand
    /// continues on the heap, measured by stack addresses (they decrease as a stack grows on every supported
    /// runtime; where a platform's addresses do not, the count alone applies). It keeps the pump and one
    /// step's frames far from the runtime's reserve where frames are large (a Debug build uses tens of KiB
    /// per suspended step). A fixed amount of host stack, never a limit.
    /// </summary>
    internal const int HostStackByteAllowance = 128 * 1024;

    /// <summary>
    /// How far above its accumulator demand a pumped step's suspending frames may register INLINE resumptions
    /// (see <see cref="TryRunSynchronously"/>), measured by stack addresses like
    /// <see cref="HostStackByteAllowance"/>; the frames above it register posted ones. It bounds how deep the
    /// step's completion cascade can reach below the pump. A fixed amount of host stack, never a limit.
    /// </summary>
    internal const int InlineResumeByteAllowance = 96 * 1024;

    /// <summary>
    /// How many of a pumped step's suspending frames may register inline resumptions, whatever their stack
    /// addresses say: it bounds the runtime's completion frames that a cascade adds to each resumed frame.
    /// </summary>
    internal const int InlineResumeFrameAllowance = 128;

    // The stack a pump must find below itself, beyond the runtime's own sufficient-stack reserve, to resume its
    // steps inline: the deepest cascade the two allowances admit (measured ascents reach at most 1.3 times their
    // descent, plus the runtime's completion frames, well under 1 KiB a frame), with a margin. Probed in steps
    // smaller than half of the smallest reserve, so the probe never nears the end of the stack.
    private const int InlineHeadroomStep = 32 * 1024;
    private const int InlineHeadroomSteps = 14;

    // The innermost synchronous pump running on this thread, or null.
    [ThreadStatic] private static FoldTrampoline? t_pump;
    // The pump whose segment START phase runs in the pump's own drain loop on this thread: the one place where
    // an accumulator demand suspends a step with inline resumptions. Null everywhere else.
    [ThreadStatic] private static FoldTrampoline? t_inlineStart;
    // The pump whose step is unwinding with inline resumptions, the frames registered so far, and the stack
    // position of the demand that suspended it.
    [ThreadStatic] private static FoldTrampoline? t_inlineUnwinding;
    [ThreadStatic] private static int t_inlineFrames;
    [ThreadStatic] private static nint t_inlineOrigin;
    // The pump context that every suspending frame of an inline pump's posting unwinding captures, or null.
    [ThreadStatic] private static PumpContext? t_postingUnwinding;
    // Whether inline-registered frames may wait above the frames the current work item of an inline pump resumes:
    // a resumed inline step, or anything resumed from it. Its posting unwindings then post frame by frame.
    [ThreadStatic] private static bool t_inlineFramesMayWait;
    // A stack position of this thread known to have the inline headroom below it, and one known to lack it
    // (0: none known). Positions above the first have it, positions below the second lack it.
    [ThreadStatic] private static nint t_headroomAt;
    [ThreadStatic] private static nint t_headroomLackedAt;
    // The drain loops (of any trampoline, pumping or not) running on this thread, innermost first.
    [ThreadStatic] private static DrainScope? t_drains;
    // How many fold continuations the synchronous evaluator keeps nested on this thread's stack, and the
    // stack position of the outermost one (0: none).
    [ThreadStatic] private static int t_hostStackContinuations;
    [ThreadStatic] private static nint t_hostStackOrigin;

    // A fixed address to measure stack positions from. Only differences between two readings of one thread
    // are used, so its own location does not matter.
    [FixedAddressValueType] private static byte s_anchor = 0;

    private static readonly AsyncLocal<HostContext?> HostFrame = new();
    private static long s_stalledPumps;
    private static long s_pumps;

    // The run whose fold this trampoline belongs to.
    private readonly EvaluationBudget _run;
    // A segment to start or resume, a stack hop, or a continuation posted by the runtime.
    // The monitor guards the queue and the drain flag.
    private readonly Queue<object> _work = new();
    private bool _draining;
    private readonly PumpContext _schedulingContext;
    // The context of an inline pump's posting unwinding that inline frames may wait above: each frame it resumes
    // runs from the queue with no synchronization context, where a completed inline frame's waiter resumes inline.
    // Created by the first such unwinding (only the pump's own thread reads it).
    private PumpContext? _postingContext;
    // Whether this trampoline's current synchronous pump resumes its steps inline: decided when the pump starts.
    private bool _inlineResumes;

    /// <summary>The trampoline of one fold of the run <paramref name="run"/>.</summary>
    internal FoldTrampoline(EvaluationBudget run)
    {
        _run = run;
        _schedulingContext = new PumpContext(this, cascading: true);
    }

    /// <summary>
    /// Synchronous pumps that exhausted their queue with an incomplete segment. An invariant violation;
    /// no evaluator path causes one (see the class remarks).
    /// </summary>
    internal static long StalledPumps => Interlocked.Read(ref s_stalledPumps);

    /// <summary>
    /// Synchronous pumps started in this process: synchronous accumulator demands that continued their
    /// fold on the heap. Process-wide observation only.
    /// </summary>
    internal static long Pumps => Interlocked.Read(ref s_pumps);

    /// <summary>Whether a synchronous pump runs on this thread: no twin hops to the thread pool here.</summary>
    internal static bool IsPumping => t_pump is not null;

    internal static bool IsPumpingRun(EvaluationBudget budget) => ReferenceEquals(t_pump?._run, budget);

    /// <summary>
    /// Evaluator awaits capture only a fold's ready queue. No host scheduler is captured. Inside an inline pump's
    /// work with no synchronization context current, a frame of a step's inline unwinding captures nothing while it
    /// stays within the inline allowances, and every frame of a posting unwinding captures the pump context the
    /// unwinding chose, installed here for the one await that reads it: the method builder restores the frame's
    /// caller's context when the frame suspends, so each suspending frame decides again (see
    /// <see cref="TryRunSynchronously"/>).
    /// </summary>
    internal static bool CaptureFoldContext
    {
        get
        {
            if (SynchronizationContext.Current is PumpContext) return true;
            if (t_postingUnwinding is { } posting)
            {
                SynchronizationContext.SetSynchronizationContext(posting);
                return true;
            }

            return t_inlineUnwinding is { } pump && pump.LeavesInlineAllowance();
        }
    }

    // One more frame of a pumped step's inline unwinding registers its continuation: true, turning the rest of the
    // unwinding (this frame included) into a cascading posting one, when it lies beyond either inline allowance. A
    // segment start's unwinding holds the step's whole chain, so no inline frame waits above its posting frames.
    private bool LeavesInlineAllowance()
    {
        var frames = ++t_inlineFrames;
        if (frames <= InlineResumeFrameAllowance && Position() - t_inlineOrigin <= InlineResumeByteAllowance)
            return false;
        t_inlineUnwinding = null;
        t_postingUnwinding = _schedulingContext;
        SynchronizationContext.SetSynchronizationContext(_schedulingContext);
        _run.NoteInlineFoldUnwindingCut();
        return true;
    }

    /// <summary>
    /// Called where a suspension other than an inline-eligible accumulator demand begins inside an inline pump's
    /// work (a stack hop, a joined flight, any other demand): every frame that now suspends registers a posted
    /// resumption, which returns through the pump's queue wherever its awaitable completes. In work that inline
    /// frames may wait above (a resumed inline step, see <see cref="RunItem"/>), each such frame is resumed from
    /// the queue on its own; elsewhere they resume one inside the other wherever the runtime can inline them, as
    /// in every other pump. Nothing changes outside an inline pump's work without a synchronization context: the
    /// evaluator awaits capture the drain loop's context already. Only the unwinding that follows reads it: the
    /// drain loop clears it when the work item ends.
    /// </summary>
    internal static void BeginPostingUnwinding()
    {
        if (t_pump is not { _inlineResumes: true } pump || SynchronizationContext.Current is not null || t_postingUnwinding is not null)
            return;
        t_inlineUnwinding = null;
        t_postingUnwinding = t_inlineFramesMayWait
            ? (pump._postingContext ??= new PumpContext(pump, cascading: false))
            : pump._schedulingContext;
        pump._run.NotePostedFoldUnwinding();
    }

    // Whether a frame registering its continuation now may have inline-registered frames waiting above it once it
    // resumes: it registers inline itself, or in work inline frames may wait above, or without the cascading
    // context. Read by a segment's waiting step (FoldSegment), whose resumption then runs with no context.
    internal static bool RegistersBelowInlineFrames()
        => t_inlineFramesMayWait || SynchronizationContext.Current is not PumpContext { Cascading: true };

    /// <summary>
    /// Whether a synchronous accumulator demanded at the current frame continues its fold on the heap: this
    /// thread keeps <see cref="HostStackAllowance"/> fold continuations on its stack already, or its chain
    /// has reached <see cref="HostStackByteAllowance"/> below the outermost of them. An observation of the
    /// host stack alone: no charge, no side effect.
    /// </summary>
    internal static bool HostStackAllowanceIsUsed
    {
        get
        {
            if (t_hostStackContinuations >= HostStackAllowance) return true;
            var origin = t_hostStackOrigin;
            return origin != 0 && origin - Position() > HostStackByteAllowance;
        }
    }

    /// <summary>
    /// Opens one fold continuation nested in place on this thread's stack (the outermost one records where
    /// the chain began). Returns the count before it, for <see cref="LeaveHostStackContinuation"/>.
    /// </summary>
    internal static int EnterHostStackContinuation()
    {
        var nested = t_hostStackContinuations;
        if (nested == 0) t_hostStackOrigin = Position();
        t_hostStackContinuations = nested + 1;
        return nested;
    }

    /// <summary>Closes the continuation <see cref="EnterHostStackContinuation"/> opened.</summary>
    internal static void LeaveHostStackContinuation(int nested)
    {
        t_hostStackContinuations = nested;
        if (nested == 0) t_hostStackOrigin = 0;
    }

    // The current stack position: the address of a local of this frame, relative to the anchor.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static nint Position()
    {
        byte marker = 0;
        return Unsafe.ByteOffset(ref s_anchor, ref marker);
    }

    // Whether stack addresses decrease as this runtime's stacks grow, which the inline allowances and the headroom
    // memo measure by: where they do not, a pump never resumes inline.
    private static readonly bool s_stackGrowsDown = DeeperPosition(Position());

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static bool DeeperPosition(nint caller) => Position() < caller;

    // Whether the stack below the current frame holds the inline headroom beyond the runtime's reserve. Each
    // thread memoizes the deepest position found to have it and the shallowest found to lack it: a thread's
    // stack never moves, so a position above the first has it and one below the second lacks it.
    private static bool HasInlineHeadroom()
    {
        if (!s_stackGrowsDown) return false;
        var here = Position();
        if (t_headroomAt != 0 && here >= t_headroomAt) return true;
        if (t_headroomLackedAt != 0 && here <= t_headroomLackedAt) return false;
        if (HasStackBeyondReserve(InlineHeadroomSteps))
        {
            t_headroomAt = here;
            return true;
        }

        t_headroomLackedAt = here;
        return false;
    }

    // Whether `steps` more InlineHeadroomStep blocks fit below the caller with the runtime's sufficient-stack
    // reserve still below them. A block is taken only once the reserve is known to remain beneath it.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static bool HasStackBeyondReserve(int steps)
    {
        if (!RuntimeHelpers.TryEnsureSufficientExecutionStack()) return false;
        if (steps == 0) return true;
        Span<byte> block = stackalloc byte[InlineHeadroomStep];
        return HasStackBeyondReserveBelow(block, steps - 1);
    }

    // Receives the block so the allocation stays live while the next one is probed.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static bool HasStackBeyondReserveBelow(Span<byte> block, int steps) => HasStackBeyondReserve(steps);

    /// <summary>
    /// The twin route's demand of <paramref name="segment"/>: queued here, and run now if no drain loop of
    /// this trampoline is running (this call then drains until nothing is queued). Returns the segment's
    /// outcome, pending while the segment waits for a demand of its own or for a genuine suspension.
    /// </summary>
    internal ValueTask<EvalResult<Evaluator.CountedResult>> Demand(FoldSegment segment)
    {
        segment.PrepareStart(this);
        if (Queue(segment))
        {
            Drain(target: null, pumpContext: null);
            if (!segment.IsCompleted) BeginPostingUnwinding();
        }
        else if (ReferenceEquals(t_inlineStart, this))
        {
            // The pump's own segment start suspends its step: the frames resume inline (see TryRunSynchronously).
            t_inlineStart = null;
            t_inlineUnwinding = this;
            t_inlineFrames = 0;
            t_inlineOrigin = Position();
            _run.NoteInlineFoldUnwinding();
        }
        else
        {
            BeginPostingUnwinding();
        }

        return new ValueTask<EvalResult<Evaluator.CountedResult>>(segment, 0);
    }

    /// <summary>
    /// The synchronous route's demand of <paramref name="segment"/>, on the calling thread: queued here and
    /// pumped until it has completed (see the class remarks). Returns <c>false</c>, running nothing, where it
    /// cannot pump, and the caller then evaluates in place: a drain loop of this trampoline runs already, or
    /// one of the same run runs on this thread (synchronous code inside a drained segment, whose pump could
    /// wait for work queued to that loop). A drain loop of another run — a host operation inside a heap step
    /// that starts a run of its own — does not stop it: no work of one run reaches another's trampoline.
    /// Throws the run's host exception or cancellation, the original object, when the segment ended with one.
    /// <para>The pump RESUMES INLINE (see the class remarks) when it starts under the default task scheduler and
    /// finds, below itself, the runtime's sufficient-stack reserve plus <c>InlineHeadroomSteps</c> blocks of
    /// <c>InlineHeadroomStep</c> bytes — the deepest completion cascade the inline allowances admit, with a margin
    /// (memoized per thread by stack position). Otherwise it posts every resumption, as every pump did before.</para>
    /// </summary>
    internal bool TryRunSynchronously(FoldSegment segment, EvaluationBudget budget, out EvalResult<Evaluator.CountedResult> outcome)
    {
        outcome = default;
        for (var scope = t_drains; scope is not null; scope = scope.Outer)
        {
            if (ReferenceEquals(scope.Run, _run)) return false;
        }

        lock (_work)
        {
            if (_draining) return false;
            _draining = true;
        }

        Interlocked.Increment(ref s_pumps);
        var previousPump = t_pump;
        // Heap continuations carry the flow in the execution context, so the pump runs with flow.
        var suppressed = ExecutionContext.IsFlowSuppressed();
        if (suppressed) ExecutionContext.RestoreFlow();
        var previousHost = HostFrame.Value;
        // A host exception or a cancellation crosses many state machines on the way back: carried by value.
        var openedBoundary = !budget.CarriesHostTermination;
        if (openedBoundary) budget.OpenHostTerminationBoundary();
        // Inline resumptions need the runtime to inline a completed task's continuations here: the default task
        // scheduler, and the stack for the deepest cascade the inline allowances admit.
        _inlineResumes = !FoldResumeTestSeam.WithholdsInlineResumes
            && TaskScheduler.Current == TaskScheduler.Default
            && HasInlineHeadroom();
        t_pump = this;
        try
        {
            if (budget.HostOperations is not null)
                HostFrame.Value = new HostContext(ExecutionContext.Capture()!, SynchronizationContext.Current, suppressed);
            segment.PrepareStart(this);
            lock (_work) _work.Enqueue(segment);
            Drain(segment, ExecutionContext.Capture());
        }
        finally
        {
            t_pump = previousPump;
            HostFrame.Value = previousHost;
            if (openedBoundary) budget.CloseHostTerminationBoundary();
            if (suppressed && !ExecutionContext.IsFlowSuppressed()) ExecutionContext.SuppressFlow();
        }

        // The run's retained host termination is thrown here, on the calling thread, as the same object.
        if (openedBoundary) budget.RethrowHostTermination();
        outcome = segment.Outcome();
        return true;
    }

    /// <summary>
    /// Hands a stack hop's continuation to the synchronous pump running on this thread, if one runs:
    /// returns <c>false</c> otherwise (the hop then uses the thread pool). Only a hop that suppressed flow
    /// asks for reaches it (see <see cref="StackHop"/>); the continuation receives the flow's state.
    /// </summary>
    internal static bool TryPostHop(Action continuation)
    {
        if (t_pump is not { } pump) return false;
        // The hop suspends its frame: the frames above it post their resumptions.
        BeginPostingUnwinding();
        pump.QueueOrRun(new HopContinuation(continuation, EvaluationFlow.CaptureIfSuppressed()));
        return true;
    }

    // Queues a resumed step or a hop continuation, and drains here when no drain loop runs.
    internal void QueueOrRun(object work)
    {
        if (Queue(work))
            Drain(target: null, pumpContext: null);
    }

    // Queues `work`; true when the caller must drain (no drain loop ran, and the caller now is one).
    private bool Queue(object work)
    {
        lock (_work)
        {
            _work.Enqueue(work);
            if (_draining) return false;
            _draining = true;
            return true;
        }
    }

    // THE DRAIN LOOP: runs queued work until none is left — and, for a pump, until its target has
    // completed. The caller has set _draining; this loop clears it when it returns.
    private void Drain(FoldSegment? target, ExecutionContext? pumpContext)
    {
        var scope = new DrainScope(this, t_drains);
        t_drains = scope;
        try
        {
            while (true)
            {
                object work;
                lock (_work)
                {
                    if (_work.Count == 0)
                    {
                        if (target is null || target.IsCompleted)
                        {
                            _draining = false;
                            return;
                        }

                        Interlocked.Increment(ref s_stalledPumps);
                        throw new InvalidOperationException("The synchronous fold has an incomplete segment and no ready continuation.");
                    }

                    work = _work.Dequeue();
                }

                // A pump's own segment start is where a step may suspend with inline resumptions.
                var outerStart = t_inlineStart;
                var outerUnwinding = t_inlineUnwinding;
                var outerPosting = t_postingUnwinding;
                var outerMayWait = t_inlineFramesMayWait;
                t_inlineStart = target is not null && _inlineResumes && work is FoldSegment { IsStarting: true } ? this : null;
                t_inlineUnwinding = null;
                t_postingUnwinding = null;
                t_inlineFramesMayWait = InlineFramesMayWaitAbove(work);
                try
                {
                    Run(work, pumpContext);
                }
                finally
                {
                    t_inlineStart = outerStart;
                    t_inlineUnwinding = outerUnwinding;
                    t_postingUnwinding = outerPosting;
                    t_inlineFramesMayWait = outerMayWait;
                }
            }
        }
        catch
        {
            // An evaluator fault (never a language outcome): the trampoline stops draining.
            lock (_work) _draining = false;
            throw;
        }
        finally
        {
            t_drains = scope.Outer;
        }
    }

    // One drain loop running on this thread, and the one it runs inside.
    private sealed class DrainScope(FoldTrampoline trampoline, DrainScope? outer)
    {
        internal FoldTrampoline Trampoline { get; } = trampoline;
        internal EvaluationBudget Run => Trampoline._run;
        internal DrainScope? Outer { get; } = outer;
    }

    // Each phase runs in its captured execution context, with the pump owning evaluator scheduling.
    private static void Run(object work, ExecutionContext? pumpContext)
    {
        var context = (work as FoldSegment)?.WorkContext ?? pumpContext;
        if (context is not null)
        {
            ExecutionContext.Run(context, RunItem, work);
            return;
        }

        var synchronization = SynchronizationContext.Current;
        try { RunItem(work); }
        finally { SynchronizationContext.SetSynchronizationContext(synchronization); }
    }

    // Whether inline-registered frames may wait above what `work` resumes (see t_inlineFramesMayWait): a segment
    // start resumes nothing; a resumed step's waiter records how it registered; a cascading post resumes a frame
    // whose waiters all captured the cascading context; anything else may sit below inline frames.
    private static bool InlineFramesMayWaitAbove(object work) => work switch
    {
        FoldSegment segment => !segment.IsStarting && segment.InlineFramesMayWaitAbove,
        PostedContinuation posted => !posted.Cascading,
        _ => true,
    };

    // Every drain loop but an inline pump's runs its work in the pump's or its own scheduling context, which every
    // evaluator await captures. An inline pump's drain loops run with no synchronization context, where the
    // runtime inlines a completed task's continuations, the work that inline-registered frames may wait above
    // (whose completion would resume them) and every segment start (whose demand may suspend inline); they run
    // any other work in the pump's scheduling context, so that its posting frames resume one inside the other.
    private static readonly ContextCallback RunItem = static work =>
    {
        var pump = t_pump;
        SynchronizationContext.SetSynchronizationContext(pump is not { _inlineResumes: true }
            ? (pump ?? t_drains!.Trampoline)._schedulingContext
            : work is FoldSegment { IsStarting: true } || t_inlineFramesMayWait ? null : pump._schedulingContext);
        if (work is FoldSegment segment)
        {
            segment.RunPhase();
            return;
        }

        if (work is PostedContinuation posted)
        {
            posted.Callback(posted.State);
            return;
        }

        var hop = (HopContinuation)work!;
        hop.Handover?.Install();
        hop.Continuation();
    };

    // A stack hop's continuation queued to a pump: the flow's state where the context does not carry it.
    private sealed class HopContinuation(Action continuation, EvaluationFlow.Handover? handover)
    {
        internal Action Continuation { get; } = continuation;
        internal EvaluationFlow.Handover? Handover { get; } = handover;
    }

    private sealed record PostedContinuation(SendOrPostCallback Callback, object? State, bool Cascading);

    // A trampoline's private scheduling context: what it is posted runs from its queue. A CASCADING context's
    // posts run in it, so the frames that captured it resume one inside the other wherever the runtime can inline
    // them; the other one's posts run with no synchronization context (an inline pump's per-frame posting).
    private sealed class PumpContext(FoldTrampoline pump, bool cascading) : SynchronizationContext
    {
        internal bool Cascading => cascading;

        public override void Post(SendOrPostCallback callback, object? state)
        {
            pump._run.NotePostedFoldResumption();
            pump.QueueOrRun(new PostedContinuation(callback, state, cascading));
        }
    }

    /// <summary>
    /// Mirrors an execution-context boundary that exists on the synchronous evaluator. The shared
    /// asynchronous methods that also run synchronously start a new host scope here: their method
    /// builder restores the parent on return or suspension. A plain method retaining that same
    /// boundary uses <see cref="CallbackHostScope"/> to restore its caller. Twin-only frames share the current
    /// host scope, just as their plain synchronous counterparts do.
    /// </summary>
    internal static void ForkHostScope() => ForkHostFrame();

    private static HostContext? ForkHostFrame()
    {
        if (t_pump is null) return null;
        var parent = HostFrame.Value;
        if (parent is not null) HostFrame.Value = parent.Fork();
        return parent;
    }

    internal readonly struct CallbackHostScope : IDisposable
    {
        private readonly HostContext? _parent;
        public CallbackHostScope() => _parent = ForkHostFrame();

        public void Dispose()
        {
            if (_parent is not null) HostFrame.Value = _parent;
        }
    }

    internal static Result InvokeHost(
        Func<IReadOnlyList<Result>, CancellationToken, Result> implementation,
        IReadOnlyList<Result> arguments, CancellationToken token)
    {
        if (t_pump is not { } pump || HostFrame.Value is not { } host)
            return InvokeExternal(implementation, arguments, token);

        t_pump = null;
        try { return host.Invoke(implementation, arguments, token); }
        finally { t_pump = pump; }
    }

    // An async host operation or downloader owns its own scheduling. The evaluator captures the fold
    // context when it subsequently awaits the returned computation. A nested host run starts independently.
    internal static T InvokeExternal<TArg, T>(Func<TArg, CancellationToken, T> implementation, TArg argument, CancellationToken token)
    {
        if (SynchronizationContext.Current is not PumpContext context) return implementation(argument, token);
        SynchronizationContext.SetSynchronizationContext(null);
        try { return implementation(argument, token); }
        finally { SynchronizationContext.SetSynchronizationContext(context); }
    }

    private sealed class HostContext(ExecutionContext execution, SynchronizationContext? synchronization, bool suppressed)
    {
        internal HostContext Fork() => new(execution, synchronization, suppressed);

        internal Result Invoke(Func<IReadOnlyList<Result>, CancellationToken, Result> implementation,
            IReadOnlyList<Result> arguments, CancellationToken token)
        {
            var node = NeedNode.FlowNode;
            var preparing = Evaluator.FlowPreparingInvocations;
            Result? result = null;
            ExecutionContext.Run(execution, _ =>
            {
                HostFrame.Value = null;
                NeedNode.FlowNode = node;
                Evaluator.FlowPreparingInvocations = preparing;
                SynchronizationContext.SetSynchronizationContext(synchronization);
                if (suppressed) ExecutionContext.SuppressFlow();
                result = implementation(arguments, token);
                synchronization = SynchronizationContext.Current;
                suppressed = ExecutionContext.IsFlowSuppressed();
                if (suppressed) ExecutionContext.RestoreFlow();
                execution = ExecutionContext.Capture()!;
            }, null);
            return result!;
        }
    }
}

/// <summary>
/// ONE SEGMENT of a fold (<see cref="FoldTrampoline"/>): the asynchronous computation of one accumulator,
/// started by a trampoline's drain loop under the demanding flow's contexts, and delivering its outcome to
/// the step that demanded it through that loop. It is the source of the value task its demand returns
/// (<see cref="IValueTaskSource{TResult}"/>): one object per accumulator computed on the heap, used once,
/// allocated only when the computation goes there (an accumulator demanded in place has none).
/// </summary>
internal abstract class FoldSegment : IValueTaskSource<EvalResult<Evaluator.CountedResult>>
{
    // The marker of a completed segment in _waiter.
    private static readonly Action<object?> Completed = static _ => throw new InvalidOperationException("A fold segment's completion marker was invoked.");

    private FoldTrampoline? _trampoline;
    // The demanding flow's contexts, for the start.
    private ExecutionContext? _startContext;
    private EvaluationFlow.Handover? _startHandover;
    // The waiting step: its continuation (then Completed), its state and its contexts, for the resume.
    private Action<object?>? _waiter;
    private object? _waiterState;
    private ExecutionContext? _waiterContext;
    private EvaluationFlow.Handover? _waiterHandover;
    // Whether inline-registered frames may wait above the waiting step's frames (see FoldTrampoline.RunItem).
    private bool _inlineFramesMayWaitAbove;
    // Set when the resume is queued: the drain loop then resumes the waiter instead of starting.
    private Action<object?>? _resume;
    // The outcome, and the running computation while it is pending.
    private EvalResult<Evaluator.CountedResult> _result;
    private ExceptionDispatchInfo? _exception;
    private ValueTask<EvalResult<Evaluator.CountedResult>> _pending;
    private Action? _onPendingCompleted;

    /// <summary>The asynchronous computation of the accumulator: the twin family's segment.</summary>
    protected abstract ValueTask<EvalResult<Evaluator.CountedResult>> RunSegment();

    internal bool IsCompleted => ReferenceEquals(Volatile.Read(ref _waiter), Completed);

    // Whether the queued phase is the start (otherwise it resumes the waiting step).
    internal bool IsStarting => _resume is null;

    // Whether inline-registered frames may wait above the waiting step: it registered inline, or in work that
    // inline frames may wait above, or with no cascading context.
    internal bool InlineFramesMayWaitAbove => _inlineFramesMayWaitAbove;

    // The execution context of the queued phase (null: the pump's own, or none).
    internal ExecutionContext? WorkContext => _resume is null ? _startContext : _waiterContext;

    // Before the start is queued: the demanding flow's contexts.
    internal void PrepareStart(FoldTrampoline trampoline)
    {
        _trampoline = trampoline;
        _startContext = ExecutionContext.Capture();
        _startHandover = _startContext is null ? EvaluationFlow.CaptureIfSuppressed() : null;
    }

    // The drain loop runs the queued phase: the start, or the waiting step's resume.
    internal void RunPhase()
    {
        if (_resume is { } resume)
        {
            var state = _waiterState;
            _resume = null;
            _waiterState = null;
            _waiterHandover?.Install();
            resume(state);
            return;
        }

        _startHandover?.Install();
        ValueTask<EvalResult<Evaluator.CountedResult>> pending;
        try
        {
            pending = RunSegment();
        }
        catch (Exception error)
        {
            CompleteException(error);
            return;
        }

        if (pending.IsCompleted)
        {
            CompleteFrom(pending);
            return;
        }

        // The computation waits for a demand of its own (a step suspended at its accumulator) or for a
        // genuine suspension; it completes this segment from its last frame when it ends.
        _pending = pending;
        pending.ConfigureAwait(FoldTrampoline.CaptureFoldContext).GetAwaiter().UnsafeOnCompleted(_onPendingCompleted ??= OnPendingCompleted);
    }

    private void OnPendingCompleted()
    {
        var pending = _pending;
        _pending = default;
        CompleteFrom(pending);
    }

    private void CompleteFrom(ValueTask<EvalResult<Evaluator.CountedResult>> pending)
    {
        EvalResult<Evaluator.CountedResult> result;
        try
        {
            result = pending.GetAwaiter().GetResult();
        }
        catch (Exception error)
        {
            CompleteException(error);
            return;
        }

        _result = result;
        Publish();
    }

    private void CompleteException(Exception error)
    {
        _exception = ExceptionDispatchInfo.Capture(error);
        Publish();
    }

    // Publishes the outcome. A step already waiting for it is resumed through the trampoline, never here.
    private void Publish()
    {
        var waiting = Interlocked.Exchange(ref _waiter, Completed);
        if (waiting is not null)
            QueueResume(waiting);
    }

    private void QueueResume(Action<object?> continuation)
    {
        _resume = continuation;
        _trampoline!.QueueOrRun(this);
    }

    /// <summary>The outcome of a completed segment: its result, or its exception rethrown.</summary>
    internal EvalResult<Evaluator.CountedResult> Outcome()
    {
        _exception?.Throw();
        return _result;
    }

    // ── IValueTaskSource: the demanding step awaits its accumulator's segment ───────────────────────────

    ValueTaskSourceStatus IValueTaskSource<EvalResult<Evaluator.CountedResult>>.GetStatus(short token)
        => !IsCompleted ? ValueTaskSourceStatus.Pending
            : _exception is null ? ValueTaskSourceStatus.Succeeded
            : _exception.SourceException is OperationCanceledException ? ValueTaskSourceStatus.Canceled
            : ValueTaskSourceStatus.Faulted;

    EvalResult<Evaluator.CountedResult> IValueTaskSource<EvalResult<Evaluator.CountedResult>>.GetResult(short token) => Outcome();

    // The waiting step registers its continuation, resumed later by the drain loop under its own contexts.
    void IValueTaskSource<EvalResult<Evaluator.CountedResult>>.OnCompleted(
        Action<object?> continuation, object? state, short token, ValueTaskSourceOnCompletedFlags flags)
    {
        _waiterState = state;
        _waiterContext = ExecutionContext.Capture();
        _waiterHandover = _waiterContext is null ? EvaluationFlow.CaptureIfSuppressed() : null;
        _inlineFramesMayWaitAbove = FoldTrampoline.RegistersBelowInlineFrames();
        if (Interlocked.CompareExchange(ref _waiter, continuation, null) is null)
            return;

        // The segment completed meanwhile: resume the step through the trampoline now.
        QueueResume(continuation);
    }
}
