using KatLang.Evaluation;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// The NEED-09 single flight and wait-for graph of a need cell whose host has suppressed
/// <see cref="ExecutionContext"/> flow (November 2026; finding
/// <c>async-route-suppressed-flow-cycle-self-join-hang</c> of the adversarial performance audit of
/// 2026-11-21), beside the same contracts under a flowing context.
///
/// <para>The graph's edges are explicit, but the node a demand records as its parent is the
/// flow's current node, which lives in the logical context. An asynchronous computation started
/// while flow is suppressed would lose it at its first genuine suspension, so such a computation
/// first continues on the thread pool, where its node is installed in a context that flows; a
/// stack hop and a fold continuation thread hand the node over themselves when the context does
/// not. These tests build the cells by hand, so the suspension is the computation's own await of
/// a gate: host code, as a host operation's awaitable is. <see cref="SuppressedFlowRunTests"/>
/// covers whole runs.</para>
///
/// <para>Overlap is established by observed state, never by a delay; every bounded wait is a
/// hang guard. C# host execution only.</para>
/// </summary>
public class NeedCellSuppressedFlowTests
{
    private static readonly TimeSpan HangGuard = TimeSpan.FromSeconds(60);

    private static readonly SourceSpan SpanA = new(1, 1, 1, 2);
    private static readonly SourceSpan SpanB = new(2, 1, 2, 2);

    private static readonly EvalResult<Evaluator.CountedResult> Seven
        = EvalResult<Evaluator.CountedResult>.Ok(new(new Result.Atom(7), 1));

    private static readonly EvalResult<Algorithm?> Nothing = EvalResult<Algorithm?>.Ok(null);

    private static TaskCompletionSource Signal() => new(TaskCreationOptions.RunContinuationsAsynchronously);

    // A gate whose completion resumes the waiting computation on the thread pool, or inline on
    // the completing thread.
    private static TaskCompletionSource Gate(bool inline)
        => new(inline ? TaskCreationOptions.None : TaskCreationOptions.RunContinuationsAsynchronously);

    // Completes a gate from a host thread of its own. An inline gate continues the waiting
    // computation on that thread, so a continuation that never returns fails the hang guard
    // here instead of blocking the test.
    private static Task Release(TaskCompletionSource gate)
        => HostFlow.OnHostThread(Flow.Normal, () => gate.TrySetResult()).WaitAsync(HangGuard);

    private static async Task Until(Func<bool> condition)
    {
        var deadline = DateTime.UtcNow + HangGuard;
        while (!condition())
        {
            Assert.True(DateTime.UtcNow < deadline, "The awaited condition did not hold in time.");
            await Task.Delay(5);
        }
    }

    public static TheoryData<Flow, bool> FlowsAndBooleans()
    {
        var rows = new TheoryData<Flow, bool>();
        foreach (var flow in Enum.GetValues<Flow>())
            foreach (var flag in new[] { false, true })
                rows.Add(flow, flag);
        return rows;
    }

    public static TheoryData<Flow, bool, bool> FlowsAndTwoBooleans()
    {
        var rows = new TheoryData<Flow, bool, bool>();
        foreach (var flow in Enum.GetValues<Flow>())
            foreach (var first in new[] { false, true })
                foreach (var second in new[] { false, true })
                    rows.Add(flow, first, second);
        return rows;
    }

    // ── Re-entry after a genuine suspension ──────────────────────────────────────────────────

    /// <summary>
    /// A VALUE computation that suspends at a gate and then demands its own cell — through
    /// either family — is refused that demand as a <see cref="EvalError.DemandCycle"/> blamed on
    /// the cell, and continues. Before the repair the suppressed-flow demand joined the cell's
    /// own flight and never completed.
    /// </summary>
    [Theory]
    [MemberData(nameof(FlowsAndTwoBooleans))]
    public async Task AValueReentry_AfterAGenuineSuspension_IsADemandCycle(Flow flow, bool reenterAsynchronously, bool resumeInline)
    {
        var budget = EvaluationBudget.Create(null);
        var entered = Signal();
        var gate = Gate(resumeInline);
        NeedCell? cell = null;
        EvalError? reentry = null;
        string? afterSuspension = null;
        cell = new NeedCell(() => throw new InvalidOperationException("synchronous family"), async () =>
        {
            entered.SetResult();
            await gate.Task.ConfigureAwait(false);
            afterSuspension = $"current={cell!.IsEvaluatingInCurrentFlow()} edges={cell.ActiveDependencyCount}";
            var again = reenterAsynchronously ? await cell.DemandAsync() : cell.Demand();
            reentry = again.IsError ? again.Error : null;
            return Seven;
        }, span: SpanA, budget: budget);

        var pending = HostFlow.StartOnHostThread(flow, () => cell.DemandAsync().AsTask());
        await entered.Task.WaitAsync(HangGuard);
        Assert.True(cell.HasValueInFlight);
        Assert.False(pending.IsCompleted);
        await Release(gate);
        var outcome = await pending.WaitAsync(HangGuard);

        // The refused re-entry is the re-entering observation's alone: the computation completed.
        Assert.True(outcome.IsOk, outcome.IsError ? outcome.Error.ToString() : null);
        Assert.Equal("current=True edges=0", afterSuspension);
        Assert.Equal(SpanA, Assert.IsType<EvalError.DemandCycle>(reentry).Span);
        Assert.True(cell.HasCompletedValue);
        Assert.False(cell.HasValueInFlight);
        Assert.False(cell.HasJoinedValueFlight);
        Assert.Equal(0, cell.ActiveDependencyCount);
        Assert.False(NeedNode.HasCurrentNode);
    }

    /// <summary>The same for a runtime CALLABLE projection that suspends and then projects itself.</summary>
    [Theory]
    [MemberData(nameof(FlowsAndTwoBooleans))]
    public async Task AProjectionReentry_AfterAGenuineSuspension_IsADemandCycle(Flow flow, bool reenterAsynchronously, bool resumeInline)
    {
        var budget = EvaluationBudget.Create(null);
        var entered = Signal();
        var gate = Gate(resumeInline);
        NeedCell? cell = null;
        EvalError? reentry = null;
        cell = NeedCell.WithRuntimeProjection(() => Seven, () => new(Seven),
            () => throw new InvalidOperationException("synchronous family"),
            async () =>
            {
                entered.SetResult();
                await gate.Task.ConfigureAwait(false);
                var again = reenterAsynchronously ? await cell!.ProjectCallableAsync() : cell!.ProjectCallable();
                reentry = again.IsError ? again.Error : null;
                return Nothing;
            }, SpanA, budget);

        var pending = HostFlow.StartOnHostThread(flow, () => cell.ProjectCallableAsync().AsTask());
        await entered.Task.WaitAsync(HangGuard);
        Assert.True(cell.HasProjectionInFlight);
        await Release(gate);
        var outcome = await pending.WaitAsync(HangGuard);

        Assert.True(outcome.IsOk, outcome.IsError ? outcome.Error.ToString() : null);
        Assert.Equal(SpanA, Assert.IsType<EvalError.DemandCycle>(reentry).Span);
        Assert.Equal(1, cell.ProjectionComputations);
        Assert.False(cell.HasProjectionInFlight);
        Assert.False(cell.HasJoinedProjectionFlight);
        Assert.Equal(0, cell.ProjectionActiveDependencyCount);
        Assert.False(NeedNode.HasCurrentNode);
    }

    /// <summary>
    /// An indirect cycle with a suspension on each side: A suspends and demands B, B suspends and
    /// demands A. B's demand of A would close the cycle, so it is refused; B completes with that
    /// failure, and A, which waited for B, with B's outcome.
    /// </summary>
    [Theory]
    [MemberData(nameof(FlowsAndBooleans))]
    public async Task AnIndirectCycle_AcrossTwoSuspensions_IsADemandCycle(Flow flow, bool resumeInline)
    {
        var budget = EvaluationBudget.Create(null);
        var enteredA = Signal();
        var enteredB = Signal();
        var gateA = Gate(resumeInline);
        var gateB = Gate(resumeInline);
        NeedCell? a = null, b = null;
        var startsA = 0;
        var startsB = 0;
        a = new NeedCell(() => throw new InvalidOperationException("synchronous family"), async () =>
        {
            Interlocked.Increment(ref startsA);
            enteredA.SetResult();
            await gateA.Task.ConfigureAwait(false);
            return await b!.DemandAsync();
        }, span: SpanA, budget: budget);
        b = new NeedCell(() => throw new InvalidOperationException("synchronous family"), async () =>
        {
            Interlocked.Increment(ref startsB);
            enteredB.SetResult();
            await gateB.Task.ConfigureAwait(false);
            return await a.DemandAsync();
        }, span: SpanB, budget: budget);

        var pending = HostFlow.StartOnHostThread(flow, () => a.DemandAsync().AsTask());
        await enteredA.Task.WaitAsync(HangGuard);
        await Release(gateA);
        await enteredB.Task.WaitAsync(HangGuard);
        Assert.Equal(1, a.ActiveDependencyCount);
        await Release(gateB);
        var outcome = await pending.WaitAsync(HangGuard);

        // Blamed on the cell whose demand would have closed the cycle: A.
        Assert.Equal(SpanA, Assert.IsType<EvalError.DemandCycle>(outcome.Error).Span);
        Assert.Same(outcome.Error, b.Demand().Error);
        Assert.Equal((1, 1), (startsA, startsB));
        Assert.Equal((0, 0), (a.ActiveDependencyCount, b.ActiveDependencyCount));
        Assert.False(a.HasValueInFlight || b.HasValueInFlight);
        Assert.False(NeedNode.HasCurrentNode);
    }

    /// <summary>
    /// The existing hop shape (<see cref="StackHopTests.SelfDemandAcrossAHop_IsStillADemandCycle"/>)
    /// under both flows: the suspension is a stack hop inside the computation.
    /// </summary>
    [Theory]
    [MemberData(nameof(FlowsAndBooleans))]
    public async Task AReentry_AcrossAStackHop_IsADemandCycle(Flow flow, bool projection)
    {
        var budget = EvaluationBudget.Create(null);
        NeedCell? cell = null;
        cell = projection
            ? NeedCell.WithRuntimeProjection(() => Seven, () => new(Seven),
                () => throw new InvalidOperationException("synchronous family"),
                async () =>
                {
                    await new StackHop();
                    return await cell!.ProjectCallableAsync();
                }, SpanA, budget)
            : new NeedCell(() => throw new InvalidOperationException("synchronous family"), async () =>
            {
                await new StackHop();
                return await cell!.DemandAsync();
            }, span: SpanA, budget: budget);

        var error = projection
            ? (await HostFlow.StartOnHostThread(flow, () => cell.ProjectCallableAsync().AsTask()).WaitAsync(HangGuard)).Error
            : (await HostFlow.StartOnHostThread(flow, () => cell.DemandAsync().AsTask()).WaitAsync(HangGuard)).Error;

        Assert.Equal(SpanA, Assert.IsType<EvalError.DemandCycle>(error).Span);
        Assert.Equal(0, projection ? cell.ProjectionActiveDependencyCount : cell.ActiveDependencyCount);
    }

    // ── Independent flights ──────────────────────────────────────────────────────────────────

    public static TheoryData<Flow, Flow, bool> StarterAndJoinerFlows()
    {
        var rows = new TheoryData<Flow, Flow, bool>();
        foreach (var starter in Enum.GetValues<Flow>())
            foreach (var joiner in Enum.GetValues<Flow>())
                foreach (var projection in new[] { false, true })
                    rows.Add(starter, joiner, projection);
        return rows;
    }

    /// <summary>
    /// Legitimate sharing: a second, unrelated flow that demands a cell whose computation is
    /// suspended joins that one flight, whichever flow each of them was started under. One
    /// computation runs, and both observers receive its outcome.
    /// </summary>
    [Theory]
    [MemberData(nameof(StarterAndJoinerFlows))]
    public async Task AnUnrelatedDemand_JoinsTheOneFlight(Flow starterFlow, Flow joinerFlow, bool projection)
    {
        var budget = EvaluationBudget.Create(null);
        var entered = Signal();
        var gate = Gate(inline: false);
        var starts = 0;
        var algorithm = new Algorithm.User(null, [], [], [], [new Expr.Num(7)]);
        async ValueTask Compute()
        {
            Interlocked.Increment(ref starts);
            entered.SetResult();
            await gate.Task.ConfigureAwait(false);
        }
        var cell = projection
            ? NeedCell.WithRuntimeProjection(() => Seven, () => new(Seven),
                () => throw new InvalidOperationException("synchronous family"),
                async () => { await Compute(); return EvalResult<Algorithm?>.Ok(algorithm); }, SpanA, budget)
            : new NeedCell(() => throw new InvalidOperationException("synchronous family"),
                async () => { await Compute(); return Seven; }, span: SpanA, budget: budget);
        Task<bool> Observe(Flow flow) => projection
            ? HostFlow.StartOnHostThread(flow, async () => ReferenceEquals((await cell.ProjectCallableAsync()).Value, algorithm))
            : HostFlow.StartOnHostThread(flow, async () => (await cell.DemandAsync()).Value.Value is Result.Atom(var seven) && seven == 7);

        var starter = Observe(starterFlow);
        await entered.Task.WaitAsync(HangGuard);
        var joiner = Observe(joinerFlow);
        await Until(() => projection ? cell.HasJoinedProjectionFlight : cell.HasJoinedValueFlight);
        Assert.False(starter.IsCompleted || joiner.IsCompleted);
        await Release(gate);

        Assert.True(await starter.WaitAsync(HangGuard));
        Assert.True(await joiner.WaitAsync(HangGuard));
        Assert.Equal(1, starts);
        Assert.False(projection ? cell.HasProjectionInFlight : cell.HasValueInFlight);
        Assert.Equal(0, projection ? cell.ProjectionActiveDependencyCount : cell.ActiveDependencyCount);
        Assert.False(NeedNode.HasCurrentNode);
    }

    /// <summary>
    /// A cycle across two independently started chains: one flow computes A, another computes B;
    /// A's computation then waits for B's flight, so B's demand of A would close a cycle and is
    /// refused. Both flows end, with one failure.
    /// </summary>
    [Theory]
    [InlineData(Flow.Normal, Flow.Normal)]
    [InlineData(Flow.Normal, Flow.Suppressed)]
    [InlineData(Flow.Suppressed, Flow.Normal)]
    [InlineData(Flow.Suppressed, Flow.Suppressed)]
    public async Task ACycle_AcrossIndependentlyStartedChains_IsDetected(Flow flowA, Flow flowB)
    {
        var budget = EvaluationBudget.Create(null);
        var enteredA = Signal();
        var enteredB = Signal();
        var gateA = Gate(inline: false);
        var gateB = Gate(inline: false);
        NeedCell? a = null, b = null;
        a = new NeedCell(() => throw new InvalidOperationException("synchronous family"), async () =>
        {
            enteredA.SetResult();
            await gateA.Task.ConfigureAwait(false);
            return await b!.DemandAsync();
        }, span: SpanA, budget: budget);
        b = new NeedCell(() => throw new InvalidOperationException("synchronous family"), async () =>
        {
            enteredB.SetResult();
            await gateB.Task.ConfigureAwait(false);
            return await a.DemandAsync();
        }, span: SpanB, budget: budget);

        var chainA = HostFlow.StartOnHostThread(flowA, () => a.DemandAsync().AsTask());
        var chainB = HostFlow.StartOnHostThread(flowB, () => b.DemandAsync().AsTask());
        await enteredA.Task.WaitAsync(HangGuard);
        await enteredB.Task.WaitAsync(HangGuard);
        await Release(gateA);
        // A's computation has joined B's flight: its wait-for edge is recorded before it waits.
        await Until(() => b.HasJoinedValueFlight);
        Assert.Equal(1, a.ActiveDependencyCount);
        await Release(gateB);

        var outcomeB = await chainB.WaitAsync(HangGuard);
        var outcomeA = await chainA.WaitAsync(HangGuard);
        Assert.Equal(SpanA, Assert.IsType<EvalError.DemandCycle>(outcomeB.Error).Span);
        Assert.Same(outcomeB.Error, outcomeA.Error);
        Assert.Equal((0, 0), (a.ActiveDependencyCount, b.ActiveDependencyCount));
        Assert.False(a.HasValueInFlight || b.HasValueInFlight);
    }

    // ── Cancellation and host exceptions ─────────────────────────────────────────────────────

    /// <summary>
    /// A computation that ends with the host's cancellation after a suspension: the starter, a
    /// joiner that waited for the flight, and every later observer of either family receive the
    /// one exception object with the host's token. Nothing is restarted and no edge or flight is
    /// left behind.
    /// </summary>
    [Theory]
    [MemberData(nameof(FlowsAndBooleans))]
    public async Task ACancelledComputation_ReachesEveryObserver_WithTheOriginalExceptionAndToken(Flow flow, bool projection)
    {
        using var host = new CancellationTokenSource();
        var thrown = new OperationCanceledException("host cancellation", host.Token);
        var budget = EvaluationBudget.Create(null);
        var entered = Signal();
        var gate = Gate(inline: false);
        var starts = 0;
        async ValueTask Compute()
        {
            Interlocked.Increment(ref starts);
            entered.SetResult();
            await gate.Task.ConfigureAwait(false);
            throw thrown;
        }
        var cell = projection
            ? NeedCell.WithRuntimeProjection(() => Seven, () => new(Seven),
                () => throw new InvalidOperationException("synchronous family"),
                async () => { await Compute(); return Nothing; }, SpanA, budget)
            : new NeedCell(() => throw new InvalidOperationException("synchronous family"),
                async () => { await Compute(); return Seven; }, span: SpanA, budget: budget);
        Task<bool> Observe() => projection
            ? HostFlow.StartOnHostThread(flow, async () => (await cell.ProjectCallableAsync()).IsOk)
            : HostFlow.StartOnHostThread(flow, async () => (await cell.DemandAsync()).IsOk);

        var starter = Observe();
        await entered.Task.WaitAsync(HangGuard);
        var joiner = Observe();
        await Until(() => projection ? cell.HasJoinedProjectionFlight : cell.HasJoinedValueFlight);
        await Release(gate);

        Assert.Same(thrown, await Assert.ThrowsAnyAsync<OperationCanceledException>(() => starter.WaitAsync(HangGuard)));
        Assert.Same(thrown, await Assert.ThrowsAnyAsync<OperationCanceledException>(() => joiner.WaitAsync(HangGuard)));
        Assert.Same(thrown, await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Observe().WaitAsync(HangGuard)));
        Assert.Same(thrown, Assert.ThrowsAny<OperationCanceledException>(
            () => projection ? cell.ProjectCallable().IsOk : cell.Demand().IsOk));
        Assert.Equal(host.Token, thrown.CancellationToken);
        Assert.Equal(1, starts);
        Assert.False(projection ? cell.HasProjectionInFlight : cell.HasValueInFlight);
        Assert.Equal(0, projection ? cell.ProjectionActiveDependencyCount : cell.ActiveDependencyCount);
        Assert.False(NeedNode.HasCurrentNode);
    }

    /// <summary>
    /// A cell whose own token is cancelled refuses at its observation entry under either flow:
    /// nothing is started, so nothing leaves the calling thread.
    /// </summary>
    [Theory]
    [InlineData(Flow.Normal)]
    [InlineData(Flow.Suppressed)]
    public async Task APreCancelledCell_ThrowsItsOwnToken_BeforeAnythingStarts(Flow flow)
    {
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var starts = 0;
        var cell = new NeedCell(() => Seven, () => { Interlocked.Increment(ref starts); return new(Seven); },
            budget: EvaluationBudget.Create(null), token: cancellation.Token);

        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(
            () => HostFlow.StartOnHostThread(flow, () => cell.DemandAsync().AsTask()).WaitAsync(HangGuard));

        Assert.Equal(cancellation.Token, thrown.CancellationToken);
        Assert.Equal(0, starts);
        Assert.False(cell.HasValueInFlight);
    }

    // ── Separate runs ────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// A cell of another run demanded inside a suspended computation records no edge on the
    /// demanding run's node, and its own re-entry is its own cycle: each run has its own graph.
    /// </summary>
    [Theory]
    [MemberData(nameof(FlowsAndBooleans))]
    public async Task ACellOfAnotherRun_DemandedInsideASuspendedComputation_KeepsTheGraphsApart(Flow flow, bool resumeInline)
    {
        var outerBudget = EvaluationBudget.Create(null);
        var innerBudget = EvaluationBudget.Create(null);
        var entered = Signal();
        var gate = Gate(resumeInline);
        NeedCell? outer = null, inner = null;
        EvalError? innerReentry = null;
        var observed = new List<string>();
        inner = new NeedCell(() => throw new InvalidOperationException("synchronous family"), async () =>
        {
            await Task.Yield();
            lock (observed)
                observed.Add($"outerEdges={outer!.ActiveDependencyCount} outerCurrent={outer.IsEvaluatingInCurrentFlow()} innerCurrent={inner!.IsEvaluatingInCurrentFlow()}");
            var again = await inner!.DemandAsync();
            innerReentry = again.IsError ? again.Error : null;
            return Seven;
        }, span: SpanB, budget: innerBudget);
        outer = new NeedCell(() => throw new InvalidOperationException("synchronous family"), async () =>
        {
            entered.SetResult();
            await gate.Task.ConfigureAwait(false);
            var nested = await inner.DemandAsync();
            lock (observed)
                observed.Add($"nestedOk={nested.IsOk} outerCurrent={outer!.IsEvaluatingInCurrentFlow()} outerEdges={outer.ActiveDependencyCount}");
            return await outer!.DemandAsync();
        }, span: SpanA, budget: outerBudget);

        var pending = HostFlow.StartOnHostThread(flow, () => outer.DemandAsync().AsTask());
        await entered.Task.WaitAsync(HangGuard);
        await Release(gate);
        var outcome = await pending.WaitAsync(HangGuard);

        Assert.Equal(SpanA, Assert.IsType<EvalError.DemandCycle>(outcome.Error).Span);
        Assert.Equal(SpanB, Assert.IsType<EvalError.DemandCycle>(innerReentry).Span);
        Assert.Equal(
        [
            "outerEdges=0 outerCurrent=False innerCurrent=True",
            "nestedOk=True outerCurrent=True outerEdges=0",
        ], observed);
        Assert.False(NeedNode.HasCurrentNode);
    }

    // ── Where a computation runs ─────────────────────────────────────────────────────────────

    /// <summary>
    /// Under a flowing context nothing changed: an asynchronous computation that does not suspend
    /// runs on the calling thread, in the caller's context, and its demand completes synchronously.
    /// Under suppressed flow it first continues on the thread pool, where the context flows and
    /// none of the caller's ambient state is present, and the caller's suppression stays in place.
    /// </summary>
    [Theory]
    [MemberData(nameof(FlowsAndBooleans))]
    public async Task AnAsynchronousComputation_RunsWhereItsNodeCanFlow(Flow flow, bool projection)
    {
        var ambient = new AsyncLocal<string?>();
        var budget = EvaluationBudget.Create(null);
        NeedCell? cell = null;
        string? inside = null;
        var computationThread = 0;
        void Compute()
        {
            computationThread = Environment.CurrentManagedThreadId;
            inside = $"pool={Thread.CurrentThread.IsThreadPoolThread} suppressed={ExecutionContext.IsFlowSuppressed()} "
                + $"ambient={ambient.Value ?? "none"} current={NeedNode.HasCurrentNode}";
        }
        cell = projection
            ? NeedCell.WithRuntimeProjection(() => Seven, () => new(Seven),
                () => throw new InvalidOperationException("synchronous family"),
                () => { Compute(); return new(Nothing); }, SpanA, budget)
            : new NeedCell(() => throw new InvalidOperationException("synchronous family"),
                () => { Compute(); return new(Seven); }, span: SpanA, budget: budget);

        var (pending, callerThread, callerAfter, completedAtReturn) = await HostFlow.OnHostThread(Flow.Normal, () =>
        {
            ambient.Value = "host";
            return HostFlow.Under(flow, () =>
            {
                Task started = projection ? cell.ProjectCallableAsync().AsTask() : cell.DemandAsync().AsTask();
                var completed = started.IsCompleted;
                return (started, Environment.CurrentManagedThreadId,
                    $"suppressed={ExecutionContext.IsFlowSuppressed()} ambient={ambient.Value} current={NeedNode.HasCurrentNode}",
                    completed);
            });
        }).WaitAsync(HangGuard);
        await pending.WaitAsync(HangGuard);

        if (flow == Flow.Normal)
        {
            Assert.True(completedAtReturn, "a computation that does not suspend must complete synchronously under a flowing context");
            Assert.Equal(callerThread, computationThread);
            Assert.Equal("pool=False suppressed=False ambient=host current=True", inside);
            Assert.Equal("suppressed=False ambient=host current=False", callerAfter);
        }
        else
        {
            Assert.NotEqual(callerThread, computationThread);
            Assert.Equal("pool=True suppressed=False ambient=none current=True", inside);
            Assert.Equal("suppressed=True ambient=host current=False", callerAfter);
        }
    }

    // ── The hand-over itself ─────────────────────────────────────────────────────────────────

    [Fact]
    public async Task InvocationPreparation_HopsTheAwaitingFrame()
    {
        // Select the hop before entering a computation. Only the frame that actually awaits
        // it owns the continuation and can supply the node that continuation must inherit.
        var hop = HostFlow.Under(Flow.Suppressed,
            () => Evaluator.EnterInvocationFrameFlow(byInvocation: true, asynchronous: true));
        NeedCell? cell = null;
        async Task Observe()
        {
            await hop;
            Assert.False(ExecutionContext.IsFlowSuppressed());
            Assert.True(cell!.IsEvaluatingInCurrentFlow());
        }
        cell = new NeedCell(() =>
        {
            Observe().GetAwaiter().GetResult();
            return Seven;
        }, () => throw new InvalidOperationException("synchronous demand"));

        Assert.True((await HostFlow.OnHostThread(Flow.Suppressed, cell.Demand).WaitAsync(HangGuard)).IsOk);
    }

    // Blocks the calling thread on the hop: the caller is a synchronous computation on a
    // dedicated host thread.
    private static string HopAndObserve(NeedCell cell, AsyncLocal<string?> ambient)
    {
        return Hop().GetAwaiter().GetResult();

        async Task<string> Hop()
        {
            await new StackHop();
            return $"current={cell.IsEvaluatingInCurrentFlow()} pool={Thread.CurrentThread.IsThreadPoolThread} "
                + $"suppressed={ExecutionContext.IsFlowSuppressed()} ambient={ambient.Value ?? "none"}";
        }
    }

    /// <summary>
    /// A stack hop taken inside a computation keeps the flow's node: through the execution
    /// context when it flows, and handed over by the hop itself when the host has suppressed flow —
    /// where none of the host's own ambient state follows.
    /// </summary>
    [Theory]
    [InlineData(Flow.Normal, "current=True pool=True suppressed=False ambient=host")]
    [InlineData(Flow.Suppressed, "current=True pool=True suppressed=False ambient=none")]
    public async Task AStackHop_InsideAComputation_KeepsTheFlowsNode(Flow flow, string expected)
    {
        var ambient = new AsyncLocal<string?>();
        var budget = EvaluationBudget.Create(null);
        NeedCell? cell = null;
        string? afterHop = null;
        cell = new NeedCell(() =>
        {
            afterHop = HopAndObserve(cell!, ambient);
            return Seven;
        }, () => throw new InvalidOperationException("asynchronous family"), span: SpanA, budget: budget);

        var outcome = await HostFlow.OnHostThread(Flow.Normal, () =>
        {
            ambient.Value = "host";
            return HostFlow.Under(flow, () => cell.Demand());
        }).WaitAsync(HangGuard);

        Assert.True(outcome.IsOk);
        Assert.Equal(expected, afterHop);
    }

    /// <summary>
    /// The awaiter's two registrations under suppressed flow, inside a computation: both hand the
    /// node to the continuation and nothing else. Outside a computation there is nothing to hand
    /// over, and under a flowing context the unsafe registration still leaves the context to the
    /// awaiting method's builder (<see cref="StackHopTests"/>).
    /// </summary>
    [Fact]
    public async Task ASuppressedHopRegistration_HandsOverTheNode_AndNothingElse()
    {
        var ambient = new AsyncLocal<string?>();
        var budget = EvaluationBudget.Create(null);
        var safe = new TaskCompletionSource<string>(TaskCreationOptions.RunContinuationsAsynchronously);
        var raw = new TaskCompletionSource<string>(TaskCreationOptions.RunContinuationsAsynchronously);
        var outside = new TaskCompletionSource<string>(TaskCreationOptions.RunContinuationsAsynchronously);
        NeedCell? cell = null;
        string Observation() => $"current={cell!.IsEvaluatingInCurrentFlow()} ambient={ambient.Value ?? "none"} pool={Thread.CurrentThread.IsThreadPoolThread}";
        cell = new NeedCell(() =>
        {
            new StackHop().OnCompleted(() => safe.SetResult(Observation()));
            new StackHop().UnsafeOnCompleted(() => raw.SetResult(Observation()));
            return Seven;
        }, () => throw new InvalidOperationException("asynchronous family"), span: SpanA, budget: budget);

        await HostFlow.OnHostThread(Flow.Normal, () =>
        {
            ambient.Value = "host";
            return HostFlow.Under(Flow.Suppressed, () =>
            {
                var demanded = cell.Demand().IsOk;
                new StackHop().UnsafeOnCompleted(() => outside.SetResult(Observation()));
                return demanded;
            });
        }).WaitAsync(HangGuard);

        Assert.Equal("current=True ambient=none pool=True", await safe.Task.WaitAsync(HangGuard));
        Assert.Equal("current=True ambient=none pool=True", await raw.Task.WaitAsync(HangGuard));
        Assert.Equal("current=False ambient=none pool=True", await outside.Task.WaitAsync(HangGuard));
    }

    /// <summary>
    /// A fold continuation thread (<see cref="FoldContinuationStack"/>) runs inside the demanding
    /// computation: a demand of the demander's own cell from that thread is a cycle. Under
    /// suppressed flow the new thread inherits no context, so the node is handed to it; before
    /// the repair that demand waited for the cell while the cell's thread waited for the fold thread.
    /// </summary>
    [Theory]
    [InlineData(Flow.Normal, "current=True suppressed=False ambient=host")]
    [InlineData(Flow.Suppressed, "current=True suppressed=False ambient=none")]
    public async Task AFoldContinuationThread_RunsInsideTheDemandingComputation(Flow flow, string expected)
    {
        var ambient = new AsyncLocal<string?>();
        var budget = EvaluationBudget.Create(null);
        NeedCell? cell = null;
        string? onFreshThread = null;
        EvalResult<Evaluator.CountedResult>? reentry = null;
        var demandingThread = 0;
        var freshThread = 0;
        cell = new NeedCell(() =>
        {
            demandingThread = Environment.CurrentManagedThreadId;
            reentry = FoldContinuationStack.Continue(cell!, self =>
            {
                freshThread = Environment.CurrentManagedThreadId;
                onFreshThread = $"current={self.IsEvaluatingInCurrentFlow()} suppressed={ExecutionContext.IsFlowSuppressed()} ambient={ambient.Value ?? "none"}";
                return self.Demand();
            });
            return Seven;
        }, () => throw new InvalidOperationException("asynchronous family"), span: SpanA, budget: budget);

        var outcome = await HostFlow.OnHostThread(Flow.Normal, () =>
        {
            ambient.Value = "host";
            return HostFlow.Under(flow, () => cell.Demand());
        }).WaitAsync(HangGuard);

        Assert.True(outcome.IsOk);
        Assert.NotEqual(demandingThread, freshThread);
        Assert.Equal(expected, onFreshThread);
        Assert.Equal(SpanA, Assert.IsType<EvalError.DemandCycle>(reentry!.Value.Error).Span);
        Assert.Equal(0, cell.ActiveDependencyCount);
    }
}
