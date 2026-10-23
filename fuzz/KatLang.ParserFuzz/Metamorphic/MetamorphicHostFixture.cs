using System.Collections.Concurrent;
using System.Diagnostics;
using System.Globalization;
using System.Numerics;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Raised when the asynchronous driver's WATCHDOG expires. A watchdog is a harness bound, never a
/// semantic trigger: it classifies a run as a harness/resource failure and is never reported as a
/// language-level cancellation, error, or success.
/// </summary>
internal sealed class MetamorphicWatchdogException(string message) : Exception(message);

/// <summary>
/// The deterministic host operations generated programs may call (SEM-2B), with one per-run event
/// log and, in asynchronous mode, a release gate that proves genuine suspension.
///
/// <para><b>Operations.</b> <c>trace(x)</c> records <c>trace:x</c> and returns <c>x</c>;
/// <c>wait(x)</c> records <c>wait:x</c> and returns <c>x</c>. A synchronous fixture implements both
/// synchronously, so every synchronous surface can run the same source. An asynchronous fixture
/// implements <c>wait</c> with <see cref="HostOperation.CreateAsync"/>: each call records its event,
/// parks an incomplete task, and is released only by <see cref="Drive{T}"/> after the driver has
/// WITNESSED that the run is suspended on it. Nothing here sleeps or depends on timing.</para>
///
/// <para><b>Witness.</b> A suspension is witnessed when the driver holds a pending, unreleased
/// <c>wait</c> while the run's task is incomplete. The first witness additionally requires that the
/// run's start call RETURNED control to the driver before any release — which a synchronous
/// evaluator that blocked on the host task could never do. An async API call that completes
/// synchronously records no witness at all.</para>
///
/// <para><b>Freshness.</b> One fixture serves exactly one run: a new instance per observation, so
/// no event, gate, or cancellation state can cross from one run into the next.</para>
/// </summary>
internal sealed class MetamorphicHostFixture
{
    /// <summary>Durable identity of the operation set and their event texts.</summary>
    internal const string FixtureId = "sem2b-host/1";

    /// <summary>The fixed host operation names, outside every generated name pool.</summary>
    internal static readonly IReadOnlyList<string> OperationNames = ["trace", "wait"];

    /// <summary>Suspension schedule identity: every wait is released in arrival order.</summary>
    internal const string ReleaseInOrderSchedule = "release-each-in-order";

    /// <summary>Default asynchronous watchdog; a harness bound only.</summary>
    internal static readonly TimeSpan DefaultWatchdog = TimeSpan.FromSeconds(30);

    private readonly object _gate = new();
    private readonly List<string> _events = [];
    private readonly ConcurrentQueue<PendingWait> _pending = new();
    private readonly SemaphoreSlim _pendingSignal = new(0);
    private int _waitCalls;
    private int _witnessed;
    private bool _firstWitnessAfterStartReturned;

    private MetamorphicHostFixture(bool asynchronous, int? cancelAtSuspension)
    {
        Asynchronous = asynchronous;
        CancelAtSuspension = cancelAtSuspension;
        Operations = HostOperations.Create(
            HostOperation.Create("trace", (args, _) => Record("trace", args[0]), "x"),
            asynchronous
                ? HostOperation.CreateAsync("wait", WaitAsync, "x")
                : HostOperation.Create("wait", (args, _) => Record("wait", args[0]), "x"));
    }

    /// <summary>A synchronous fixture: both operations complete immediately.</summary>
    internal static MetamorphicHostFixture Synchronous() => new(asynchronous: false, cancelAtSuspension: null);

    /// <summary>
    /// An asynchronous fixture. With <paramref name="cancelAtSuspension"/> set, the driver cancels the
    /// run's token when it witnesses that (1-based) suspension, before releasing it.
    /// </summary>
    internal static MetamorphicHostFixture Gated(int? cancelAtSuspension = null) => new(asynchronous: true, cancelAtSuspension);

    public bool Asynchronous { get; }

    public int? CancelAtSuspension { get; }

    public HostOperations Operations { get; }

    /// <summary>Durable schedule identity for descriptors and reports.</summary>
    public string ScheduleId => !Asynchronous
        ? "synchronous"
        : CancelAtSuspension is { } k
            ? "cancel-at-suspension-" + k.ToString(CultureInfo.InvariantCulture)
            : ReleaseInOrderSchedule;

    /// <summary>The host events in the order the run performed them.</summary>
    public IReadOnlyList<string> Events
    {
        get
        {
            lock (_gate) return _events.ToArray();
        }
    }

    /// <summary>How many <c>wait</c> calls the run made.</summary>
    public int WaitCalls => Volatile.Read(ref _waitCalls);

    /// <summary>How many suspensions the driver witnessed (asynchronous mode only).</summary>
    public int SuspensionsWitnessed => Volatile.Read(ref _witnessed);

    /// <summary>True when the first witnessed suspension had already returned control to the driver.</summary>
    public bool FirstSuspensionReturnedControl => Volatile.Read(ref _firstWitnessAfterStartReturned);

    /// <summary>True when a run actually reached a cancellation point this fixture scheduled.</summary>
    public bool CancellationRequested { get; private set; }

    /// <summary>Stable event text: an integral atom as its invariant decimal, anything else as its kl-struct-v1 identity.</summary>
    internal static string DescribeValue(Result value) => value is Result.Atom atom
        ? atom.Value.ToString(CultureInfo.InvariantCulture)
        : MetamorphicStructuralIdentity.Encode(value);

    private Result Record(string operation, Result value)
    {
        lock (_gate) _events.Add(operation + ":" + DescribeValue(value));
        return value;
    }

    private ValueTask<Result> WaitAsync(IReadOnlyList<Result> args, CancellationToken cancellationToken)
    {
        Record("wait", args[0]);
        Interlocked.Increment(ref _waitCalls);
        var pending = new PendingWait(args[0], new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously));
        if (cancellationToken.CanBeCanceled)
            pending.Registration = cancellationToken.Register(static state => ((PendingWait)state!).Completion.TrySetCanceled(), pending);
        _pending.Enqueue(pending);
        _pendingSignal.Release();
        return new ValueTask<Result>(pending.Completion.Task);
    }

    /// <summary>
    /// Runs one asynchronous evaluation to completion on a dedicated thread, releasing each pending
    /// <c>wait</c> only after witnessing the suspension. The watchdog bounds the WHOLE drive —
    /// including a start call that never returns because something blocked synchronously — and its
    /// expiry is a <see cref="MetamorphicWatchdogException"/>, never a semantic outcome.
    /// </summary>
    internal T Drive<T>(Func<CancellationToken, Task<T>> start, TimeSpan watchdog)
    {
        ArgumentNullException.ThrowIfNull(start);
        if (!Asynchronous)
            throw new MetamorphicHarnessException("Only an asynchronous host fixture has a suspension driver.");

        T result = default!;
        Exception? failure = null;
        using var cancellation = new CancellationTokenSource();
        var thread = new Thread(() =>
        {
            try
            {
                result = DriveOnThisThread(start, cancellation, watchdog);
            }
            catch (Exception exception)
            {
                failure = exception;
            }
        })
        {
            IsBackground = true,
            Name = "sem2b-async-driver",
        };

        thread.Start();
        if (!thread.Join(watchdog + TimeSpan.FromSeconds(5)))
        {
            // The driver itself is wedged (a start call that blocked). Release every parked wait so
            // the abandoned background thread can unwind, and report the harness bound.
            ReleaseAllPending();
            throw new MetamorphicWatchdogException(
                $"asynchronous drive did not finish within {watchdog.TotalSeconds.ToString(CultureInfo.InvariantCulture)} s (driver blocked).");
        }

        if (failure is not null)
            System.Runtime.ExceptionServices.ExceptionDispatchInfo.Capture(failure).Throw();
        return result;
    }

    private T DriveOnThisThread<T>(Func<CancellationToken, Task<T>> start, CancellationTokenSource cancellation, TimeSpan watchdog)
    {
        var clock = Stopwatch.StartNew();
        var run = start(cancellation.Token);
        var startReturned = true; // reaching this line IS the evidence: the start call gave control back
        while (true)
        {
            if (_pending.TryDequeue(out var pending))
            {
                _pendingSignal.Wait(0);
                if (!run.IsCompleted && !pending.Completion.Task.IsCompleted)
                {
                    var count = Interlocked.Increment(ref _witnessed);
                    if (count == 1) Volatile.Write(ref _firstWitnessAfterStartReturned, startReturned);
                    if (CancelAtSuspension == count)
                    {
                        CancellationRequested = true;
                        cancellation.Cancel();
                    }
                }

                pending.Registration.Dispose();
                pending.Completion.TrySetResult(pending.Value);
                continue;
            }

            if (run.IsCompleted) break;

            var remaining = watchdog - clock.Elapsed;
            if (remaining <= TimeSpan.Zero)
            {
                ReleaseAllPending();
                throw new MetamorphicWatchdogException(
                    $"asynchronous run did not complete within {watchdog.TotalSeconds.ToString(CultureInfo.InvariantCulture)} s.");
            }

            // Wake on whichever comes first: a new pending wait, or the run finishing.
            var signal = _pendingSignal.WaitAsync(remaining);
            Task.WaitAny([run, signal]);
            if (signal.IsCompletedSuccessfully && signal.Result) _pendingSignal.Release(); // re-arm: the dequeue above consumes it
        }

        return run.GetAwaiter().GetResult();
    }

    private void ReleaseAllPending()
    {
        while (_pending.TryDequeue(out var pending))
            pending.Completion.TrySetResult(pending.Value);
    }

    private sealed class PendingWait(Result value, TaskCompletionSource<Result> completion)
    {
        public Result Value { get; } = value;

        public TaskCompletionSource<Result> Completion { get; } = completion;

        public CancellationTokenRegistration Registration { get; set; }
    }
}
