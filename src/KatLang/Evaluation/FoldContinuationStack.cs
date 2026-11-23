using System.Runtime.CompilerServices;
using System.Runtime.ExceptionServices;

namespace KatLang.Evaluation;

/// <summary>
/// THE SYNCHRONOUS ROUTE'S FRESH STACK FOR FOLD CONTINUATIONS (lazy <c>reduce</c> accumulators,
/// November 2026; C#-only host-execution policy under Q-09a, no Lean counterpart). A <c>reduce</c>
/// step that demands its accumulator stays suspended while the preceding step runs, and that step
/// may demand its own accumulator in turn: a fold whose reducer uses every accumulator holds one
/// suspended step per element. The asynchronous twins keep those suspended steps on the heap
/// (<see cref="StackHop"/>). The synchronous evaluator keeps them on the host stack, which a long
/// fold would exhaust, so it continues such a chain on a FRESH stack: the demanded accumulator is
/// evaluated on a new thread with its own stack while the demanding thread waits for it.
///
/// <para><b>Where.</b> Only the synchronous VALUE computation of a fold's accumulator cell asks
/// (<c>Evaluator.ReduceFold</c>), immediately before it evaluates the accumulator. Nothing else
/// continues on another stack: every other recursion keeps the probes and the structured
/// <see cref="EvalError.EvaluationStackExhausted"/> backstop it has.</para>
///
/// <para><b>When.</b> A thread this type started knows how much stack it was given, so it
/// continues elsewhere once less than <see cref="Headroom"/> of it is left: every accumulator
/// starts with at least the documented minimum stack below it, so a step runs wherever it ran
/// while every step started from the fold's own frame. A thread it did not start has unknown
/// bounds. There the chain may use <see cref="ForeignAllowance"/> below the frame where the
/// thread's outermost fold work began, so short folds never start a thread, and it also
/// continues elsewhere once the stack is within <see cref="ReserveMargin"/> of the runtime's
/// own reserve.</para>
///
/// <para><b>Why it changes no run's meaning.</b> The fresh stack evaluates exactly the
/// computation the demanding frame would have evaluated in place, and the demanding thread does
/// nothing until it has the outcome: value, evaluation order, effects, random draws, budgets and
/// cancellation chokepoints are those of the same run on one sufficiently deep stack. It reads no
/// limit and no configuration (Q-09b). The logical flow is the demander's: the new thread runs
/// under the demander's <see cref="ExecutionContext"/>, so every <see cref="AsyncLocal{T}"/> the
/// evaluator reads (the <see cref="NeedCell"/> wait-for graph, the invocation preparation frames)
/// continues with it, and what the computation writes there it restores before it ends. An
/// exception it throws — a host operation's, or a cancellation — is rethrown on the demanding
/// thread as the same object with its original stack trace. No evaluator lock is held across the
/// demand of a cell, and a non-initiating observation never starts a VALUE computation, so no
/// thread-affine evaluator state spans the continuation.</para>
///
/// <para><b>Hosts.</b> A host operation a deep fold reaches can therefore run on a thread other
/// than the one that called the synchronous entry point, as it already can on the asynchronous
/// route: its thread-static state and any lock the calling thread holds are not available there.
/// Where a thread cannot be started (a platform without threads, or no memory for its stack), the
/// accumulator is evaluated in place and the ordinary backstop applies.</para>
/// </summary>
internal static class FoldContinuationStack
{
    /// <summary>
    /// The stack a fresh thread is given. A fixed amount of address space per thread, committed
    /// only as far as a chain reaches; never a limit.
    /// </summary>
    internal static readonly int SegmentSize = nint.Size >= 8 ? 64 * 1024 * 1024 : 4 * 1024 * 1024;

    /// <summary>
    /// The least stack an accumulator starts with on a thread this type started: the documented
    /// minimum host stack, which is what a step had to itself while steps ran in a loop.
    /// </summary>
    internal const int Headroom = 1024 * 1024;

    /// <summary>
    /// How far below its outermost fold frame a chain may reach on a thread this type did not
    /// start, whose bounds are unknown. It keeps the short folds of ordinary programs on the
    /// calling thread.
    /// </summary>
    internal const int ForeignAllowance = 256 * 1024;

    /// <summary>
    /// How far above the runtime's execution reserve an accumulator must start. The demand that
    /// reaches this test has just passed the reserve test itself (<see cref="NeedCell.Demand"/>),
    /// so this much stack is there to test with; it covers the frames of one shallow step, whose
    /// own accumulator demand would otherwise meet the reserve first.
    /// </summary>
    internal const int ReserveMargin = 32 * 1024;

    // The stack address the thread's accounting starts at (0: none is open) and how many bytes
    // below it the chain may reach before it continues elsewhere.
    [ThreadStatic] private static nint t_origin;
    [ThreadStatic] private static int t_allowance;

    // Fresh threads started and not yet finished, and the most at once. Observation only.
    private static int s_active;
    private static int s_peak;

    /// <summary>Fresh stacks this process has started for fold continuations. Observation only.</summary>
    internal static long Started => Interlocked.Read(ref s_started);

    private static long s_started;

    /// <summary>The most fresh stacks alive at once in this process. Observation only.</summary>
    internal static int PeakActive => Volatile.Read(ref s_peak);

    // A fixed address to measure stack positions from. Only differences between two readings of
    // one thread are used, so its own location does not matter.
    [FixedAddressValueType] private static byte s_anchor = 0;

    // The current stack position: the address of a local of this frame, relative to the anchor.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static nint Position()
    {
        byte marker = 0;
        return Unsafe.ByteOffset(ref s_anchor, ref marker);
    }

    /// <summary>
    /// Opens the calling thread's stack accounting at the current frame unless one is already
    /// open: the outermost fold work of a thread this type did not start. Returns whether it
    /// opened one, for <see cref="Leave"/>.
    /// </summary>
    internal static bool Enter()
    {
        if (t_origin != 0) return false;
        t_origin = Position();
        t_allowance = ForeignAllowance;
        return true;
    }

    /// <summary>Closes the accounting <see cref="Enter"/> opened.</summary>
    internal static void Leave(bool entered)
    {
        if (entered) t_origin = 0;
    }

    /// <summary>
    /// Whether an accumulator demanded at the current frame continues on a fresh stack: the chain
    /// has used its allowance on this thread, or the stack is near the runtime's reserve here. An
    /// observation only: no side effect and no charge, and it depends on the host stack alone.
    /// </summary>
    internal static bool MustContinueElsewhere()
    {
        var origin = t_origin;
        // The stack grows toward lower addresses on every supported platform; a position above
        // the origin (a shallower frame than the one that opened the accounting) has used none.
        if (origin != 0 && origin - Position() > t_allowance) return true;
        return IsNearReserve();
    }

    // Whether less than ReserveMargin of stack is left above the runtime's execution reserve.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static bool IsNearReserve()
    {
        Span<byte> margin = stackalloc byte[ReserveMargin];
        return IsBelowReserve(margin);
    }

    // Receives the margin so the allocation stays live; it tests the reserve from below it.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static bool IsBelowReserve(Span<byte> margin) => !RuntimeHelpers.TryEnsureSufficientExecutionStack();

    /// <summary>
    /// Evaluates <paramref name="evaluate"/> on a fresh stack and returns its outcome; an exception
    /// it throws is rethrown here, the original object. Returns <c>null</c> when no thread could be
    /// started: the caller then evaluates in place.
    /// </summary>
    internal static EvalResult<Evaluator.CountedResult>? Continue<TState>(
        TState state, Func<TState, EvalResult<Evaluator.CountedResult>> evaluate)
    {
        var run = new Run<TState>(state, evaluate);
        Thread thread;
        try
        {
            thread = new Thread(run.Execute, SegmentSize) { IsBackground = true, Name = "KatLang fold continuation" };
            thread.Start();
        }
        catch (Exception error) when (error is PlatformNotSupportedException or OutOfMemoryException or ThreadStartException)
        {
            return null;
        }

        thread.Join();
        run.Exception?.Throw();
        return run.Outcome;
    }

    private sealed class Run<TState>(TState state, Func<TState, EvalResult<Evaluator.CountedResult>> evaluate)
    {
        internal EvalResult<Evaluator.CountedResult>? Outcome;
        internal ExceptionDispatchInfo? Exception;

        internal void Execute()
        {
            Interlocked.Increment(ref s_started);
            var active = Interlocked.Increment(ref s_active);
            int peak;
            while (active > (peak = Volatile.Read(ref s_peak)) && Interlocked.CompareExchange(ref s_peak, active, peak) != peak)
            {
            }

            // This thread's whole stack is the chain's, less the headroom every accumulator keeps.
            t_origin = Position();
            t_allowance = SegmentSize - Headroom;
            try
            {
                Outcome = evaluate(state);
            }
            catch (Exception error)
            {
                Exception = ExceptionDispatchInfo.Capture(error);
            }
            finally
            {
                Interlocked.Decrement(ref s_active);
            }
        }
    }
}
