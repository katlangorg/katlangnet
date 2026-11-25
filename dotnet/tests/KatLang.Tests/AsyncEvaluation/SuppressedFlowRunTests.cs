using System.Numerics;
using System.Threading.Tasks.Sources;
using KatLang.Evaluation;

namespace KatLang.Tests.AsyncEvaluation;

/// <summary>How a host starts a run or a demand: with its execution context flowing, or inside
/// <see cref="ExecutionContext.SuppressFlow"/>.</summary>
public enum Flow
{
    Normal,
    Suppressed,
}

/// <summary>Where a suspended host operation is completed, which decides where its continuation runs.</summary>
public enum Resume
{
    /// <summary>The completion queues its continuations to the thread pool.</summary>
    Pool,

    /// <summary>The completion runs its continuations inline, on a host thread whose context flows.</summary>
    Inline,

    /// <summary>The completion runs its continuations inline, on a host thread that has suppressed flow.</summary>
    InlineSuppressed,
}

/// <summary>
/// Starts host work under a <see cref="Flow"/> on a dedicated host thread, so the work's
/// synchronous prefix never runs on a test-runner thread and a suppression never outlives its
/// call: it is undone on the same thread before the thread ends.
/// </summary>
internal static class HostFlow
{
    private const int OneMiB = 1_048_576;

    /// <summary>Runs <paramref name="body"/> on the current thread under <paramref name="flow"/>.</summary>
    public static T Under<T>(Flow flow, Func<T> body)
    {
        if (flow == Flow.Normal) return body();
        var control = ExecutionContext.SuppressFlow();
        try { return body(); }
        finally { control.Undo(); }
    }

    /// <summary>
    /// Runs <paramref name="body"/> to its return on a fresh background thread under
    /// <paramref name="flow"/>. The task completes with the body's value or exception; a body that
    /// never returns leaves it incomplete, which the caller's hang guard reports.
    /// </summary>
    public static Task<T> OnHostThread<T>(Flow flow, Func<T> body)
    {
        var completion = new TaskCompletionSource<T>(TaskCreationOptions.RunContinuationsAsynchronously);
        var thread = new Thread(() =>
        {
            try { completion.SetResult(Under(flow, body)); }
            catch (Exception error) { completion.SetException(error); }
        }, OneMiB) { IsBackground = true, Name = "host thread of a flow test" };
        thread.Start();
        return completion.Task;
    }

    /// <summary>The asynchronous form: the returned task is the work <paramref name="start"/> started.</summary>
    public static Task<T> StartOnHostThread<T>(Flow flow, Func<Task<T>> start)
        => OnHostThread(flow, start).Unwrap();
}

/// <summary>
/// A run of the asynchronous twin route whose host has suppressed <see cref="ExecutionContext"/>
/// flow (November 2026; finding <c>async-route-suppressed-flow-cycle-self-join-hang</c> of the
/// adversarial performance audit of 2026-11-21).
///
/// <para><b>The defect.</b> The NEED-09 wait-for graph reads the demanding computation from the
/// logical context. An <c>async</c> method started while flow is suppressed captures no context,
/// so after its first genuine suspension — a host operation's incomplete awaitable, or a stack
/// hop — the continuation no longer knew which need cell it was computing. A demand cycle was then
/// read as an unrelated demand: it joined its own flight and never completed, whatever the run's
/// cancellation token did. An invocation plan's re-entrant preparation waited for itself the same
/// way.</para>
///
/// <para><b>The contract.</b> A cycle is <see cref="KatLangErrorCode.DemandCycle"/> under either
/// flow and wherever the host completes its operation; programs without a cycle keep their value
/// and their one evaluation per shared argument; a cancellation observed while the run is
/// suspended ends it with the host's token; runs nested in a host operation and runs resumed
/// inside another run's host operation keep their cycles apart. Every wait is a hang guard, never
/// a latency claim; suspension is established by the operation's own signal. C# host execution
/// only: Lean models neither host operations nor the execution context.</para>
/// </summary>
public class SuppressedFlowRunTests
{
    private const int OneMiB = 1_048_576;

    // The guard of a wait that only a signal or a completed gate stands behind.
    private static readonly TimeSpan HangGuard = TimeSpan.FromSeconds(60);

    // The guard of a row that does deep work of its own (a recursion of 120 levels across stack
    // hops, a fold of 3,000 suspended steps across fresh threads), which a loaded machine slows.
    private static readonly TimeSpan DeepWorkGuard = TimeSpan.FromMinutes(5);

    private const string Capture = "Capture(meta operation) = operation\nId(x) = x\n";

    /// <summary>The audit's reproducer: the cycle's computation first awaits the host operation.</summary>
    private const string CycleThroughWait = Capture + "R = Capture(Id(wait(0) + R.Invoke()))\nR.Invoke()";

    /// <summary>The audit's minimized reproducer: a builtin argument instead of a user call's.</summary>
    private const string BuiltinCycleThroughWait =
        "Capture(meta operation) = operation\nR = Capture(abs(wait(0) + R.Invoke()))\nR.Invoke()";

    /// <summary>A plan whose supply formation suspends and then reads its own supply again.</summary>
    private const string ReentrantPreparation =
        "Capture(meta operation) = operation\nAdd(*xs) = sum(xs)\n"
        + "Q = Capture(Add((wait(0), 1)*, Q.Arguments*))\nQ.Arguments.count";

    private static Result Atom(Decimal128 value) => new Result.Atom(value);

    /// <summary>
    /// A host whose asynchronous <c>wait(x)</c> genuinely suspends: its first call signals
    /// <see cref="Entered"/> and stays incomplete until <see cref="Release"/>, completed as the
    /// <see cref="Resume"/> says; every later call yields to the thread pool once.
    /// </summary>
    private sealed class SuspendingHost(Resume resume) : IDisposable, IValueTaskSource<Result>
    {
        private ManualResetValueTaskSourceCore<Result> _release = new() { RunContinuationsAsynchronously = resume == Resume.Pool };
        private Result? _firstValue;
        private CancellationTokenRegistration _registration;

        public int WaitCalls;
        public int PauseCalls;
        public OperationCanceledException? Thrown;
        public bool HonorsToken;

        public CancellationTokenSource Cancellation { get; } = new();

        public TaskCompletionSource Entered { get; } = new(TaskCreationOptions.RunContinuationsAsynchronously);

        public void Dispose()
        {
            _registration.Dispose();
            Cancellation.Dispose();
        }

        /// <summary>Further operations of this host, configured beside <c>wait</c> and <c>pause</c>.</summary>
        public List<HostOperation> Extra { get; } = [];

        public HostOperations Operations => HostOperations.Create(
        [
            HostOperation.CreateAsync("wait", (arguments, token) =>
            {
                if (Interlocked.Increment(ref WaitCalls) > 1)
                    return new ValueTask<Result>(YieldThen(arguments[0]));

                _firstValue = arguments[0];
                if (HonorsToken)
                    _registration = token.Register(() => _release.SetException(Thrown = new OperationCanceledException(token)));
                return new ValueTask<Result>(this, _release.Version);
            }, "x"),
            HostOperation.CreateAsync("pause", async (arguments, _) =>
            {
                Interlocked.Increment(ref PauseCalls);
                await Task.Yield();
                return arguments[0];
            }, "x"),
            .. Extra,
        ]);

        public RunOptions Options => new()
        {
            HostOperations = Operations,
            EvaluationCancellationToken = Cancellation.Token,
        };

        /// <summary>Completes the held operation on the calling thread.</summary>
        public void ReleaseHere() => _release.SetResult(_firstValue!);

        /// <summary>Completes the held operation where <see cref="Resume"/> says.</summary>
        public Task Release()
        {
            if (resume == Resume.Pool)
            {
                ReleaseHere();
                return Task.CompletedTask;
            }
            return HostFlow.OnHostThread(resume == Resume.InlineSuppressed ? Flow.Suppressed : Flow.Normal,
                () => { ReleaseHere(); return true; });
        }

        Result IValueTaskSource<Result>.GetResult(short token) => _release.GetResult(token);
        ValueTaskSourceStatus IValueTaskSource<Result>.GetStatus(short token) => _release.GetStatus(token);

        void IValueTaskSource<Result>.OnCompleted(Action<object?> continuation, object? state, short token,
            ValueTaskSourceOnCompletedFlags flags)
        {
            _release.OnCompleted(continuation, state, token, flags);
            // The evaluator observed the incomplete awaitable and registered its continuation.
            Entered.TrySetResult();
        }
    }

    private static void RequireCleanParse(string source, HostOperations operations)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
    }

    // One suspended run: started on a host thread under `flow`, observed suspended in `wait`,
    // optionally cancelled there, released, and awaited.
    private static async Task<RunResult> RunSuspended(Flow flow, SuspendingHost host, string source, bool cancelWhileSuspended = false)
    {
        RequireCleanParse(source, host.Operations);
        var pending = HostFlow.StartOnHostThread(flow, () => KatLangEngine.RunAsync(source, host.Options));
        await host.Entered.Task.WaitAsync(HangGuard);
        Assert.False(pending.IsCompleted, "the run did not suspend in the host operation");
        if (cancelWhileSuspended) host.Cancellation.Cancel();
        await host.Release().WaitAsync(HangGuard);
        return await pending.WaitAsync(HangGuard);
    }

    private static void AssertDemandCycle(RunResult result)
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        Assert.Equal(KatLangErrorCode.DemandCycle, Assert.Single(failure.Errors).Code);
    }

    private static void AssertValue(RunResult result, Decimal128 expected)
    {
        var success = result as RunResult.Success;
        Assert.True(success is not null, result is RunResult.EvalFailure failure
            ? string.Join(" | ", failure.Errors.Select(static e => e.Message)) : result.GetType().Name);
        Assert.Equal([expected], success!.Atoms);
    }

    public static TheoryData<Flow, Resume> FlowsAndResumes()
    {
        var rows = new TheoryData<Flow, Resume>();
        foreach (var flow in Enum.GetValues<Flow>())
            foreach (var resume in Enum.GetValues<Resume>())
                rows.Add(flow, resume);
        return rows;
    }

    // ── A cycle whose computation suspended in a host operation ──────────────────────────────

    [Theory]
    [MemberData(nameof(FlowsAndResumes))]
    public async Task ACycleThroughASuspendedHostCall_IsADemandCycle(Flow flow, Resume resume)
    {
        using var host = new SuspendingHost(resume);

        AssertDemandCycle(await RunSuspended(flow, host, CycleThroughWait));

        // The operation ran once: nothing was replayed and the cycle evaluated nothing again.
        Assert.Equal(1, host.WaitCalls);
        Assert.False(NeedNode.HasCurrentNode);
    }

    [Theory]
    [MemberData(nameof(FlowsAndResumes))]
    public async Task ACycleThroughASuspendedBuiltinArgument_IsADemandCycle(Flow flow, Resume resume)
    {
        using var host = new SuspendingHost(resume);

        AssertDemandCycle(await RunSuspended(flow, host, BuiltinCycleThroughWait));

        Assert.Equal(1, host.WaitCalls);
    }

    /// <summary>
    /// The invocation plan's own re-entrancy check: forming <c>Q</c>'s supply suspends in the
    /// spread operand and then opens <c>Q.Arguments</c>, which reads the supply being formed.
    /// </summary>
    [Theory]
    [MemberData(nameof(FlowsAndResumes))]
    public async Task AReentrantPlanPreparation_AfterASuspendedHostCall_IsADemandCycle(Flow flow, Resume resume)
    {
        using var host = new SuspendingHost(resume);

        AssertDemandCycle(await RunSuspended(flow, host, ReentrantPreparation));

        Assert.Equal(1, host.WaitCalls);
    }

    /// <summary>
    /// The host operation suspends at the bottom of a recursion and the re-entry follows only after
    /// the whole chain has unwound: every frame of the chain is a suspended continuation, and the
    /// runtime resumes them one inside the other, or on the thread pool where the resuming stack
    /// runs low. Each of them must still belong to the argument's computation.
    /// </summary>
    [Theory]
    [MemberData(nameof(FlowsAndResumes))]
    public async Task ACycleAfterADeepSuspendedChainUnwinds_IsADemandCycle(Flow flow, Resume resume)
    {
        using var host = new SuspendingHost(resume);
        const string source = Capture
            + "Deep(n) = if(n == 0, wait(0), Deep(n - 1) + 0)\n"
            + "R = Capture(Id(Deep(80) + R.Invoke()))\nR.Invoke()";

        AssertDemandCycle(await RunSuspended(flow, host, source));

        Assert.Equal(1, host.WaitCalls);
    }

    /// <summary>
    /// The suspension is a stack hop instead of a host operation: <c>Deep(120)</c> outgrows a
    /// 1 MiB thread on the twin route, so the level that re-enters <c>R</c> runs on a fresh
    /// thread-pool stack. The asynchronous operation only selects the twin route.
    /// </summary>
    [Theory]
    [InlineData(Flow.Normal)]
    [InlineData(Flow.Suppressed)]
    public async Task ACycleReachedAcrossAStackHop_IsADemandCycle(Flow flow)
    {
        var bottomOnPool = -1;
        var operations = HostOperations.Create(
            HostOperation.CreateAsync("Ping", (_, _) => ValueTask.FromResult(Atom(1))),
            HostOperation.Create("here", (arguments, _) =>
            {
                Volatile.Write(ref bottomOnPool, Thread.CurrentThread.IsThreadPoolThread ? 1 : 0);
                return arguments[0];
            }, "value"));
        const string source = Capture
            + "Deep(n) = if(n == 0, here(0) + R.Invoke(), Deep(n - 1) + 0)\n"
            + "R = Capture(Id(Deep(120)))\nR.Invoke()";
        RequireCleanParse(source, operations);

        var pending = AstStructuralDepthProcessTests.RunOnThreadWithStack(OneMiB, () => HostFlow.Under(flow,
            () => KatLangEngine.RunAsync(source, new RunOptions { HostOperations = operations })));

        AssertDemandCycle(await pending.WaitAsync(DeepWorkGuard));
        Assert.Equal(1, Volatile.Read(ref bottomOnPool));
    }

    // ── Programs without a cycle ────────────────────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(FlowsAndResumes))]
    public async Task AProgramWithoutACycle_SuspendsAndCompletes(Flow flow, Resume resume)
    {
        using var captured = new SuspendingHost(resume);
        AssertValue(await RunSuspended(flow, captured, Capture + "R = Capture(Id(wait(5) + 1))\nR.Invoke()"), 6);
        Assert.Equal(1, captured.WaitCalls);

        // Three suspensions in one argument and one after it: the node survives each.
        using var several = new SuspendingHost(resume);
        AssertValue(await RunSuspended(flow, several, "Id(x) = x\nId(wait(1) + wait(2) + pause(3)) + wait(4)"), 10);
        Assert.Equal(3, several.WaitCalls);
        Assert.Equal(1, several.PauseCalls);
    }

    /// <summary>
    /// One supplied computation demanded twice is one evaluation: the second demand reads the
    /// first one's outcome, under either flow. A cycle is the only demand that is refused.
    /// </summary>
    [Theory]
    [MemberData(nameof(FlowsAndResumes))]
    public async Task ASharedArgument_IsEvaluatedOnce(Flow flow, Resume resume)
    {
        using var host = new SuspendingHost(resume);

        AssertValue(await RunSuspended(flow, host, "Twice(x) = x + x\nTwice(wait(5) + pause(1))"), 12);

        Assert.Equal(1, host.WaitCalls);
        Assert.Equal(1, host.PauseCalls);
    }

    // ── Cancellation ─────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// The token is cancelled while the run is suspended in an operation that ignores it. The run
    /// observes it when it resumes, before the re-entry of the cyclic program is reached, and ends
    /// with the host's token.
    /// </summary>
    [Theory]
    [MemberData(nameof(FlowsAndResumes))]
    public async Task ACancellationWhileSuspended_EndsTheRunWithTheHostsToken(Flow flow, Resume resume)
    {
        foreach (var source in new[] { CycleThroughWait, Capture + "R = Capture(Id(wait(5) + 1))\nR.Invoke()" })
        {
            using var host = new SuspendingHost(resume);

            var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(
                () => RunSuspended(flow, host, source, cancelWhileSuspended: true));

            Assert.Equal(host.Cancellation.Token, thrown.CancellationToken);
            Assert.Equal(1, host.WaitCalls);
        }
    }

    /// <summary>
    /// The operation honors the token: the exception it throws is the run's outcome, the same
    /// object, carrying the host's token.
    /// </summary>
    [Theory]
    [InlineData(Flow.Normal)]
    [InlineData(Flow.Suppressed)]
    public async Task ACancellationThrownByTheSuspendedOperation_IsTheRunsOutcome(Flow flow)
    {
        using var host = new SuspendingHost(Resume.Pool) { HonorsToken = true };
        RequireCleanParse(CycleThroughWait, host.Operations);
        var pending = HostFlow.StartOnHostThread(flow, () => KatLangEngine.RunAsync(CycleThroughWait, host.Options));
        await host.Entered.Task.WaitAsync(HangGuard);
        Assert.False(pending.IsCompleted, "the run did not suspend in the host operation");

        host.Cancellation.Cancel();
        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => pending.WaitAsync(HangGuard));

        Assert.Same(host.Thrown, thrown);
        Assert.Equal(host.Cancellation.Token, thrown.CancellationToken);
    }

    // ── Runs inside runs, and runs beside runs ───────────────────────────────────────────────

    public static TheoryData<Flow, Flow, bool, bool> NestedRuns()
    {
        var rows = new TheoryData<Flow, Flow, bool, bool>();
        foreach (var outer in Enum.GetValues<Flow>())
            foreach (var inner in Enum.GetValues<Flow>())
                foreach (var outerCyclic in new[] { false, true })
                    foreach (var innerCyclic in new[] { false, true })
                        rows.Add(outer, inner, outerCyclic, innerCyclic);
        return rows;
    }

    /// <summary>
    /// A host operation of the outer run starts a whole inner run, inside the outer run's suspended
    /// argument, and awaits it. Each run reports its own cycle and neither sees the other's.
    /// </summary>
    [Theory]
    [MemberData(nameof(NestedRuns))]
    public async Task ARunNestedInAHostOperation_KeepsEachRunsCycleApart(Flow outerFlow, Flow innerFlow, bool outerCyclic, bool innerCyclic)
    {
        var innerOperations = HostOperations.Create(HostOperation.CreateAsync("pause", async (arguments, _) =>
        {
            await Task.Yield();
            return arguments[0];
        }, "x"));
        var innerSource = innerCyclic
            ? Capture + "R = Capture(Id(pause(0) + R.Invoke()))\nR.Invoke()"
            : "Id(x) = x\nId(pause(4) + 1)";
        RequireCleanParse(innerSource, innerOperations);
        RunResult? innerResult = null;
        var nestedCalls = 0;
        var outerOperations = HostOperations.Create(HostOperation.CreateAsync("nested", async (arguments, _) =>
        {
            Interlocked.Increment(ref nestedCalls);
            await Task.Yield();
            innerResult = await HostFlow.Under(innerFlow,
                () => KatLangEngine.RunAsync(innerSource, new RunOptions { HostOperations = innerOperations }));
            return arguments[0];
        }, "x"));
        var outerSource = outerCyclic
            ? Capture + "R = Capture(Id(nested(0) + R.Invoke()))\nR.Invoke()"
            : "Id(x) = x\nId(nested(7) + 1)";
        RequireCleanParse(outerSource, outerOperations);

        var outerResult = await HostFlow.StartOnHostThread(outerFlow,
            () => KatLangEngine.RunAsync(outerSource, new RunOptions { HostOperations = outerOperations })).WaitAsync(HangGuard);

        if (outerCyclic) AssertDemandCycle(outerResult);
        else AssertValue(outerResult, 8);
        if (innerCyclic) AssertDemandCycle(innerResult!);
        else AssertValue(innerResult!, 5);
        Assert.Equal(1, nestedCalls);
    }

    /// <summary>
    /// Run B is suspended in its cyclic argument when a synchronous operation of run A completes
    /// B's awaitable inline: B's continuation runs on A's thread, inside A's argument. B reports
    /// its cycle from there, and A, which then suspends itself and re-enters its own argument,
    /// reports its own.
    /// </summary>
    [Theory]
    [InlineData(Flow.Normal, Flow.Normal)]
    [InlineData(Flow.Normal, Flow.Suppressed)]
    [InlineData(Flow.Suppressed, Flow.Normal)]
    [InlineData(Flow.Suppressed, Flow.Suppressed)]
    public async Task ARunResumedInsideAnotherRunsHostOperation_KeepsEachRunsCycleApart(Flow flowA, Flow flowB)
    {
        using var hostB = new SuspendingHost(Resume.Inline);
        RequireCleanParse(CycleThroughWait, hostB.Operations);
        var runB = HostFlow.StartOnHostThread(flowB, () => KatLangEngine.RunAsync(CycleThroughWait, hostB.Options));
        await hostB.Entered.Task.WaitAsync(HangGuard);
        Assert.False(runB.IsCompleted, "run B did not suspend in its host operation");

        using var hostA = new SuspendingHost(Resume.Pool);
        var pokes = 0;
        hostA.Extra.Add(HostOperation.Create("poke", (arguments, _) =>
        {
            Interlocked.Increment(ref pokes);
            // Inline: B's continuations run here, on this thread, before the completion returns.
            hostB.ReleaseHere();
            return arguments[0];
        }, "x"));
        const string sourceA = Capture + "R = Capture(Id(poke(0) + wait(0) + R.Invoke()))\nR.Invoke()";
        RequireCleanParse(sourceA, hostA.Operations);
        var runA = HostFlow.StartOnHostThread(flowA, () => KatLangEngine.RunAsync(sourceA, hostA.Options));
        await hostA.Entered.Task.WaitAsync(HangGuard);
        await hostA.Release().WaitAsync(HangGuard);

        AssertDemandCycle(await runB.WaitAsync(HangGuard));
        AssertDemandCycle(await runA.WaitAsync(HangGuard));
        Assert.Equal(1, pokes);
        Assert.Equal(1, hostA.WaitCalls);
        Assert.Equal(1, hostB.WaitCalls);
    }

    // ── A host operation that suppresses flow itself ─────────────────────────────────────────

    private static async Task<Result> YieldThen(Result value)
    {
        await Task.Yield();
        return value;
    }

    /// <summary>
    /// A host operation that returns with flow still suppressed (a <c>SuppressFlow</c> it never
    /// undoes) changes the context only of the twin that invoked it, which evaluates nothing
    /// afterwards: the argument that suspends next still knows its node, and its cycle is
    /// reported. The operation is synchronous, or asynchronous with a synchronous part that
    /// suppresses flow before it returns its incomplete awaitable.
    /// </summary>
    [Theory]
    [InlineData(Flow.Normal, false)]
    [InlineData(Flow.Normal, true)]
    [InlineData(Flow.Suppressed, false)]
    [InlineData(Flow.Suppressed, true)]
    public async Task AHostOperationThatLeavesFlowSuppressed_DoesNotHideACycle(Flow flow, bool asynchronousOperation)
    {
        using var host = new SuspendingHost(Resume.Pool);
        var leaks = 0;
        host.Extra.Add(asynchronousOperation
            ? HostOperation.CreateAsync("leak", (arguments, _) =>
            {
                Interlocked.Increment(ref leaks);
                if (!ExecutionContext.IsFlowSuppressed()) ExecutionContext.SuppressFlow();
                return new ValueTask<Result>(YieldThen(arguments[0]));
            }, "x")
            : HostOperation.Create("leak", (arguments, _) =>
            {
                Interlocked.Increment(ref leaks);
                if (!ExecutionContext.IsFlowSuppressed()) ExecutionContext.SuppressFlow();
                return arguments[0];
            }, "x"));
        // One list, so the three elements are evaluated one after another by the same frame.
        const string source = Capture + "R = Capture(Id([leak(0), wait(0), R.Invoke()]))\nR.Invoke()";

        AssertDemandCycle(await RunSuspended(flow, host, source));

        Assert.Equal(1, leaks);
        Assert.Equal(1, host.WaitCalls);
    }

    // ── The synchronous route: a fold continued on the heap ─────────────────────────────────────

    /// <summary>
    /// The synchronous route never suspends, but a long lazy <c>reduce</c> continues its chain of
    /// accumulators on the heap, pumped on the calling thread (<see cref="FoldTrampoline"/>). The start of
    /// this fold is reached in such a segment and re-enters <c>R</c>'s argument, which the same flow is
    /// still computing: the segment runs under the demander's context, so that demand is a cycle, never a
    /// wait for the computation the pump itself belongs to. The pump restores flow while it runs, so a
    /// host that suppressed it gets the same answer.
    /// </summary>
    [Theory]
    [InlineData(Flow.Normal)]
    [InlineData(Flow.Suppressed)]
    public async Task ACycleReachedOnAFoldsHeapContinuation_IsADemandCycle(Flow flow)
    {
        const string source = Capture
            + "Add(item, acc) = Id(item) + acc\n"
            + "R = Capture(Id(reduce(range(1, 3000), Add, R.Invoke())))\nR.Invoke()";
        SourceProvenance.ParseValid(source);
        var pumpsBefore = FoldTrampoline.Pumps;
        var waitsBefore = FoldTrampoline.StalledPumps;

        var result = await HostFlow.OnHostThread(flow, () => KatLangEngine.Run(source)).WaitAsync(DeepWorkGuard);

        AssertDemandCycle(result);
        // Three thousand suspended steps exceed the host stack's allowance: the start ran in a pumped segment.
        Assert.True(FoldTrampoline.Pumps > pumpsBefore);
        Assert.Equal(waitsBefore, FoldTrampoline.StalledPumps);
    }

    [Theory]
    [InlineData(Flow.Normal)]
    [InlineData(Flow.Suppressed)]
    public async Task ALongFoldWithoutACycle_CompletesOnTheHeap(Flow flow)
    {
        const string source = Capture
            + "Add(item, acc) = Id(item) + acc\n"
            + "R = Capture(Id(reduce(range(1, 3000), Add, 0)))\nR.Invoke()";
        SourceProvenance.ParseValid(source);
        var pumpsBefore = FoldTrampoline.Pumps;
        var waitsBefore = FoldTrampoline.StalledPumps;

        var result = await HostFlow.OnHostThread(flow, () => KatLangEngine.Run(source)).WaitAsync(DeepWorkGuard);

        AssertValue(result, 3000 * 3001 / 2);
        Assert.True(FoldTrampoline.Pumps > pumpsBefore);
        Assert.Equal(waitsBefore, FoldTrampoline.StalledPumps);
    }
}
