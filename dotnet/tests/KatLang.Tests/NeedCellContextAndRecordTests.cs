using KatLang.Evaluation;
using KatLang.TestInfrastructure;

namespace KatLang.Tests;

/// <summary>
/// The current node's restoration and the asynchronous resolution record (2026-11-20, C#
/// implementation only). A computation that ends with the flow's context unchanged since its node
/// was installed restores the context object captured before. Restoring that object allocates
/// nothing, and a caller of a nested computation finds its own context object in place. Any other
/// change made meanwhile, such as a host's AsyncLocal, is kept by writing only the node back. A
/// resolution's first recorded pair is held inline, and later pairs go to their channel's table.
/// Overlap is established by observed state, never by a delay; the bounded waits are hang guards.
/// </summary>
public class NeedCellContextAndRecordTests
{
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);

    private static readonly SourceSpan SpanA = new(1, 1, 1, 2);
    private static readonly SourceSpan SpanB = new(2, 1, 2, 2);

    private static readonly EvalResult<Evaluator.CountedResult> Seven
        = EvalResult<Evaluator.CountedResult>.Ok(new(new Result.Atom(7), 1));

    private static readonly EvalResult<Algorithm?> Nothing = EvalResult<Algorithm?>.Ok(null);

    private static async Task Until(Func<bool> condition)
    {
        var deadline = DateTime.UtcNow + WaitLimit;
        while (!condition())
        {
            Assert.True(DateTime.UtcNow < deadline, "The awaited condition did not hold in time.");
            await Task.Delay(5);
        }
    }

    // A cell whose VALUE computation (both families) or runtime CALLABLE projection (both families) runs `body`.
    private static NeedCell Child(EvaluationBudget? budget, bool projection, Action body, SourceSpan? span = null)
        => projection
            ? NeedCell.WithRuntimeProjection(() => Seven, () => new(Seven),
                () => { body(); return Nothing; }, () => { body(); return new(Nothing); }, span, budget)
            : new NeedCell(() => { body(); return Seven; }, () => { body(); return new(Seven); }, span: span, budget: budget);

    // The child's channel, observed by the given family without awaiting. The synchronous family is
    // called directly: an async method around it would restore the caller's context on return and
    // hide what the synchronous family leaves behind.
    private static bool ObserveSynchronously(NeedCell cell, bool projection, bool asynchronous)
    {
        if (!asynchronous) return projection ? cell.ProjectCallable().IsOk : cell.Demand().IsOk;
        if (projection)
        {
            var projected = cell.ProjectCallableAsync();
            Assert.True(projected.IsCompleted, "The observation must not suspend here.");
            return projected.Result.IsOk;
        }
        var demanded = cell.DemandAsync();
        Assert.True(demanded.IsCompleted, "The observation must not suspend here.");
        return demanded.Result.IsOk;
    }

    // The child's channel, observed and awaited by the asynchronous family. Bodies spell the choice
    // inline (`asynchronous ? await ObserveAsync(..) : ObserveSynchronously(..)`), so the synchronous
    // branch runs in the body's own frame.
    private static async ValueTask<bool> ObserveAsync(NeedCell cell, bool projection)
        => projection ? (await cell.ProjectCallableAsync()).IsOk : (await cell.DemandAsync()).IsOk;

    // A VALUE cell whose computation, in the given family, runs `body` inside it.
    private static NeedCell Outer(EvaluationBudget budget, bool asynchronous, Func<NeedCell, ValueTask> body)
    {
        NeedCell? outer = null;
        outer = asynchronous
            ? new NeedCell(() => throw new InvalidOperationException("synchronous family"), async () =>
            {
                await body(outer!);
                return Seven;
            }, budget: budget)
            : new NeedCell(() =>
            {
                var running = body(outer!);
                Assert.True(running.IsCompleted, "A synchronous computation must not suspend.");
                running.GetAwaiter().GetResult();
                return Seven;
            }, () => throw new InvalidOperationException("asynchronous family"), budget: budget);
        return outer;
    }

    private static async Task<EvalResult<Evaluator.CountedResult>> DemandOuterAsync(NeedCell cell, bool asynchronous)
        => asynchronous ? await cell.DemandAsync().AsTask().WaitAsync(WaitLimit) : cell.Demand();

    // ── The caller's context after a nested computation ──────────────────────────────────────────

    /// <summary>
    /// After a nested computation of either family and channel, its caller's computation sees its own
    /// context object again, still runs as the current node, and holds no edge. Before 2026-11-20 a
    /// synchronous nested computation wrote a new context for its caller instead.
    /// </summary>
    [Theory]
    [InlineData(false, false, false)]
    [InlineData(false, false, true)]
    [InlineData(false, true, false)]
    [InlineData(false, true, true)]
    [InlineData(true, false, false)]
    [InlineData(true, false, true)]
    [InlineData(true, true, false)]
    [InlineData(true, true, true)]
    public async Task ANestedComputation_LeavesItsCallersContextObjectInPlace(bool outerAsynchronous, bool childAsynchronous, bool projection)
    {
        var budget = EvaluationBudget.Create(null);
        var child = Child(budget, projection, static () => { });
        var observed = new List<string>();
        var outer = Outer(budget, outerAsynchronous, async self =>
        {
            var before = ExecutionContext.Capture();
            Assert.True(childAsynchronous ? await ObserveAsync(child, projection) : ObserveSynchronously(child, projection, false));
            observed.Add($"same={ReferenceEquals(before, ExecutionContext.Capture())} current={self.IsEvaluatingInCurrentFlow()} edges={self.ActiveDependencyCount}");
        });

        Assert.True((await DemandOuterAsync(outer, outerAsynchronous)).IsOk);
        Assert.Equal(["same=True current=True edges=0"], observed);
        Assert.False(NeedNode.HasCurrentNode);
    }

    /// <summary>
    /// A host AsyncLocal written inside a synchronous computation stays written after the demand, as for
    /// any synchronous call, and the caller's node is current again; restoring the earlier context
    /// object there would lose the host's write. An asynchronous computation's writes stay inside it, as
    /// for any async method.
    /// </summary>
    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void AHostWrite_InsideAComputation_FlowsAsForAnyCallOfItsFamily(bool asynchronous, bool projection)
    {
        var host = new AsyncLocal<string?>();
        var budget = EvaluationBudget.Create(null);
        var child = Child(budget, projection, () => host.Value = "written inside");
        var observed = new List<string>();
        var outer = Outer(budget, asynchronous: false, self =>
        {
            Assert.True(ObserveSynchronously(child, projection, asynchronous));
            observed.Add($"host={host.Value ?? "none"} current={self.IsEvaluatingInCurrentFlow()} edges={self.ActiveDependencyCount}");
            return ValueTask.CompletedTask;
        });

        Assert.True(outer.Demand().IsOk);
        Assert.Equal([$"host={(asynchronous ? "none" : "written inside")} current=True edges=0"], observed);
        Assert.Equal(asynchronous ? null : "written inside", host.Value);
        Assert.False(NeedNode.HasCurrentNode);

        // An unnested computation as well: the node is gone afterwards, the host's write is not.
        host.Value = null;
        var top = Child(budget, projection, () => host.Value = "written at the top");
        Assert.True(ObserveSynchronously(top, projection, asynchronous));
        Assert.Equal(asynchronous ? null : "written at the top", host.Value);
        Assert.False(NeedNode.HasCurrentNode);
        host.Value = null;
    }

    /// <summary>
    /// A synchronous computation that suppresses flow and leaves it suppressed has changed the context,
    /// so only the node is written back. The suppression survives the demand, as after any synchronous
    /// call, and the caller is the current node again. Restoring the earlier context object there would
    /// silently lift the suppression.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AComputationThatLeavesFlowSuppressed_KeepsTheSuppression_AndRestoresTheNode(bool projection)
    {
        var budget = EvaluationBudget.Create(null);
        var child = Child(budget, projection, static () => ExecutionContext.SuppressFlow());
        var observed = new List<string>();
        var outer = Outer(budget, asynchronous: false, self =>
        {
            Assert.True(ObserveSynchronously(child, projection, false));
            observed.Add($"suppressed={ExecutionContext.IsFlowSuppressed()} current={self.IsEvaluatingInCurrentFlow()} edges={self.ActiveDependencyCount}");
            ExecutionContext.RestoreFlow();
            return ValueTask.CompletedTask;
        });

        Assert.True(outer.Demand().IsOk);
        Assert.Equal(["suppressed=True current=True edges=0"], observed);
        Assert.False(ExecutionContext.IsFlowSuppressed());
        Assert.False(NeedNode.HasCurrentNode);
    }

    /// <summary>
    /// Restoring the earlier context object raises no AsyncLocal change notification: only the current
    /// node differs between the two contexts, and it has no handler.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task AHostChangeHandler_IsNotNotifiedByNestedComputations(bool asynchronous)
    {
        var notifications = new System.Collections.Concurrent.ConcurrentQueue<string>();
        var host = new AsyncLocal<string?>(change => notifications.Enqueue($"{change.PreviousValue}->{change.CurrentValue} thread={change.ThreadContextChanged}"));
        host.Value = "host";
        var budget = EvaluationBudget.Create(null);
        var value = Child(budget, projection: false, static () => { });
        var projection = Child(budget, projection: true, static () => { });
        var during = new List<string>();
        var outer = Outer(budget, asynchronous, async _ =>
        {
            var before = notifications.Count;
            Assert.True(asynchronous ? await ObserveAsync(value, false) : ObserveSynchronously(value, false, false));
            Assert.True(asynchronous ? await ObserveAsync(projection, true) : ObserveSynchronously(projection, true, false));
            during.Add($"notifications={notifications.Count - before} host={host.Value}");
        });

        Assert.True((await DemandOuterAsync(outer, asynchronous)).IsOk);
        Assert.Equal(["notifications=0 host=host"], during);
        host.Value = null;
    }

    // ── Re-entry, cancellation, concurrent joins and separate runs ─────────────────────────────────

    /// <summary>
    /// Re-entering the caller from a nested computation is a DemandCycle for the re-entry only. The
    /// re-entry installs nothing, and the caller's context object is in place afterwards. A second
    /// re-entry, now from the caller itself, is a cycle again, and no edge survives.
    /// </summary>
    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public async Task AReentry_FromANestedComputation_IsACycle_AndLeavesTheCallersContextInPlace(bool asynchronous, bool projection)
    {
        var budget = EvaluationBudget.Create(null);
        NeedCell? outer = null;
        var reentries = new List<EvalError?>();
        var middle = Child(budget, projection, () =>
        {
            var before = ExecutionContext.Capture();
            var again = outer!.Demand();
            reentries.Add(again.IsError ? again.Error : null);
            Assert.Same(before, ExecutionContext.Capture());
        });
        var observed = new List<string>();
        outer = Outer(budget, asynchronous, async self =>
        {
            var before = ExecutionContext.Capture();
            Assert.True(asynchronous ? await ObserveAsync(middle, projection) : ObserveSynchronously(middle, projection, false));
            var self2 = self.Demand();
            reentries.Add(self2.IsError ? self2.Error : null);
            observed.Add($"same={ReferenceEquals(before, ExecutionContext.Capture())} current={self.IsEvaluatingInCurrentFlow()} edges={self.ActiveDependencyCount}");
        });

        Assert.True((await DemandOuterAsync(outer, asynchronous)).IsOk);
        Assert.Equal(["same=True current=True edges=0"], observed);
        Assert.Collection(reentries,
            first => Assert.Equal(KatLangErrorCode.DemandCycle, Assert.IsType<EvalError.DemandCycle>(first).Code),
            second => Assert.Equal(KatLangErrorCode.DemandCycle, Assert.IsType<EvalError.DemandCycle>(second).Code));
        Assert.Equal(0, middle.ActiveDependencyCount);
        Assert.Equal(0, middle.ProjectionActiveDependencyCount);
        Assert.False(NeedNode.HasCurrentNode);
    }

    /// <summary>
    /// A nested computation that throws the host's cancellation leaves through the same restoration:
    /// the caller, which catches it, finds its context object in place and is still the current node.
    /// The original exception and token stay sticky for the child. A cell whose own token is already
    /// cancelled throws before it installs anything.
    /// </summary>
    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public async Task ACancelledNestedComputation_LeavesTheCallersContextInPlace(bool asynchronous, bool projection)
    {
        using var host = new CancellationTokenSource();
        var thrown = new OperationCanceledException("host cancellation", host.Token);
        using var cellToken = new CancellationTokenSource();
        cellToken.Cancel();
        var budget = EvaluationBudget.Create(null);
        var child = Child(budget, projection, () => throw thrown);
        var precancelled = projection
            ? NeedCell.WithRuntimeProjection(() => Seven, () => new(Seven), () => Nothing, () => new(Nothing), budget: budget, token: cellToken.Token)
            : new NeedCell(() => Seven, () => new(Seven), budget: budget, token: cellToken.Token);
        var observed = new List<string>();
        var outer = Outer(budget, asynchronous, async self =>
        {
            var before = ExecutionContext.Capture();
            // Caught in this body's own frame: a wrapping async lambda would restore the context itself.
            OperationCanceledException? caught = null;
            try { _ = asynchronous ? await ObserveAsync(child, projection) : ObserveSynchronously(child, projection, false); }
            catch (OperationCanceledException exception) { caught = exception; }
            Assert.Same(thrown, caught);
            Assert.Equal(host.Token, caught!.CancellationToken);
            observed.Add($"same={ReferenceEquals(before, ExecutionContext.Capture())} current={self.IsEvaluatingInCurrentFlow()} edges={self.ActiveDependencyCount}");
            caught = null;
            try { _ = asynchronous ? await ObserveAsync(precancelled, projection) : ObserveSynchronously(precancelled, projection, false); }
            catch (OperationCanceledException exception) { caught = exception; }
            Assert.Equal(cellToken.Token, caught?.CancellationToken);
            observed.Add($"same={ReferenceEquals(before, ExecutionContext.Capture())}");
        });

        Assert.True((await DemandOuterAsync(outer, asynchronous)).IsOk);
        Assert.Equal(["same=True current=True edges=0", "same=True"], observed);
        Assert.Same(thrown, Assert.ThrowsAny<OperationCanceledException>(() => ObserveSynchronously(child, projection, false)));
        Assert.Same(thrown, await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await ObserveAsync(child, projection)));
        Assert.Equal(0, child.ActiveDependencyCount);
        Assert.Equal(0, child.ProjectionActiveDependencyCount);
        Assert.False(NeedNode.HasCurrentNode);
    }

    /// <summary>
    /// A joiner on another thread waits for the one computation without installing anything, so its own
    /// context object is untouched; the starter's caller finds its context object in place once the
    /// computation it started has ended. Both receive the one outcome.
    /// </summary>
    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public async Task AJoiner_KeepsItsContext_AndTheStartersCallerFindsItsOwnInPlace(bool starterAsynchronous, bool joinerAsynchronous)
    {
        var budget = EvaluationBudget.Create(null);
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var starts = 0;
        var child = new NeedCell(() =>
        {
            Interlocked.Increment(ref starts);
            entered.SetResult();
            release.Task.WaitAsync(WaitLimit).GetAwaiter().GetResult();
            return Seven;
        }, async () =>
        {
            Interlocked.Increment(ref starts);
            entered.SetResult();
            await release.Task.WaitAsync(WaitLimit);
            return Seven;
        }, budget: budget);
        var observed = new System.Collections.Concurrent.ConcurrentQueue<string>();
        NeedCell Caller(string role, bool asynchronous) => asynchronous
            ? new NeedCell(() => throw new InvalidOperationException(), async () =>
            {
                var before = ExecutionContext.Capture();
                var outcome = await child.DemandAsync();
                observed.Enqueue($"{role} ok={outcome.IsOk} same={ReferenceEquals(before, ExecutionContext.Capture())}");
                return Seven;
            }, budget: budget)
            : new NeedCell(() =>
            {
                var before = ExecutionContext.Capture();
                var outcome = child.Demand();
                observed.Enqueue($"{role} ok={outcome.IsOk} same={ReferenceEquals(before, ExecutionContext.Capture())}");
                return Seven;
            }, () => throw new InvalidOperationException(), budget: budget);
        var starterCaller = Caller("starter", starterAsynchronous);
        var joinerCaller = Caller("joiner", joinerAsynchronous);

        var starter = starterAsynchronous
            ? Task.Run(async () => await starterCaller.DemandAsync())
            : Task.Factory.StartNew(() => starterCaller.Demand(), TaskCreationOptions.LongRunning);
        await entered.Task.WaitAsync(WaitLimit);
        var joiner = joinerAsynchronous
            ? Task.Run(async () => await joinerCaller.DemandAsync())
            : Task.Factory.StartNew(() => joinerCaller.Demand(), TaskCreationOptions.LongRunning);
        await Until(() => child.HasJoinedValueFlight || joiner.IsCompleted);
        Assert.False(joiner.IsCompleted);
        release.SetResult();

        Assert.True((await starter.WaitAsync(WaitLimit)).IsOk);
        Assert.True((await joiner.WaitAsync(WaitLimit)).IsOk);
        Assert.Equal(1, starts);
        Assert.Equal(["joiner ok=True same=True", "starter ok=True same=True"], observed.Order(StringComparer.Ordinal).ToList());
        Assert.Equal(0, starterCaller.ActiveDependencyCount);
        Assert.Equal(0, joinerCaller.ActiveDependencyCount);
        Assert.False(child.HasValueInFlight);
    }

    /// <summary>
    /// A run started inside another run's computation records no edge from the outer parent, and its
    /// cells' restorations leave the outer computation's context object in place.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task AnotherRunsCells_InsideAComputation_LeaveTheOuterContextInPlace(bool asynchronous)
    {
        var outerBudget = EvaluationBudget.Create(null);
        var innerBudget = EvaluationBudget.Create(null);
        NeedCell? outer = null, innerParent = null;
        var during = new List<string>();
        var innerChild = Child(innerBudget, projection: false,
            () => during.Add($"outer={outer!.ActiveDependencyCount} innerParent={innerParent!.ActiveDependencyCount}"));
        innerParent = new NeedCell(() => innerChild.Demand(), () => innerChild.DemandAsync(), budget: innerBudget);
        var observed = new List<string>();
        outer = Outer(outerBudget, asynchronous, async self =>
        {
            var before = ExecutionContext.Capture();
            Assert.True(asynchronous ? (await innerParent.DemandAsync()).IsOk : innerParent.Demand().IsOk);
            observed.Add($"same={ReferenceEquals(before, ExecutionContext.Capture())} current={self.IsEvaluatingInCurrentFlow()}");
        });

        Assert.True((await DemandOuterAsync(outer, asynchronous)).IsOk);
        Assert.Equal(["outer=0 innerParent=1"], during);
        Assert.Equal(["same=True current=True"], observed);
        Assert.Equal(0, innerParent.ActiveDependencyCount);
        Assert.False(NeedNode.HasCurrentNode);
    }

    // ── The resolution record ────────────────────────────────────────────────────────────────────

    /// <summary>
    /// Every recorded pair answers with its own outcome object, whichever channel was recorded first and
    /// however many pairs follow; a pair of the same cell on the other channel, or of another cell, is
    /// absent. Recording a pair twice is refused for the inline pair and a table pair alike.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ARecord_AnswersEveryPairWithItsOwnOutcome_WhicheverChannelComesFirst(bool valueFirst)
    {
        var budget = EvaluationBudget.Create(null);
        var cells = Enumerable.Range(0, 12)
            .Select(_ => NeedCell.WithRuntimeProjection(() => Seven, () => new(Seven), () => Nothing, () => new(Nothing), budget: budget))
            .ToArray();
        var values = new Dictionary<NeedCell, EvalResult<Evaluator.CountedResult>>();
        var callables = new Dictionary<NeedCell, EvalResult<Algorithm?>>();
        var record = new NeedCell.ResolutionRecord();
        for (var i = 0; i < cells.Length; i++)
        {
            // Mixed channels and outcome kinds, starting with the channel under test; every third cell
            // then records its other channel as well.
            var cell = cells[i];
            var number = i;
            void Value()
            {
                EvalResult<Evaluator.CountedResult> outcome = number % 4 == 1
                    ? new EvalError.DemandCycle { Span = SpanA }
                    : EvalResult<Evaluator.CountedResult>.Ok(new(new Result.Atom(number), number + 2));
                record.RecordValue(cell, outcome);
                values.Add(cell, outcome);
            }
            void Callable()
            {
                EvalResult<Algorithm?> outcome = number % 4 == 3
                    ? new EvalError.DemandCycle { Span = SpanB }
                    : number % 4 == 0 ? Nothing : EvalResult<Algorithm?>.Ok(new Algorithm.Builtin(BuiltinId.@count));
                record.RecordCallable(cell, outcome);
                callables.Add(cell, outcome);
            }
            var both = i % 3 == 0;
            if ((i % 2 == 0) == valueFirst)
            {
                Value();
                if (both) Callable();
            }
            else
            {
                Callable();
                if (both) Value();
            }

            foreach (var probe in cells)
            {
                Assert.Equal(values.ContainsKey(probe), record.Contains(probe, NeedCell.Channel.Value));
                Assert.Equal(callables.ContainsKey(probe), record.Contains(probe, NeedCell.Channel.Callable));
                Assert.Equal(values.TryGetValue(probe, out var expectedValue), record.TryGetValue(probe, out var value));
                Assert.Equal(callables.TryGetValue(probe, out var expectedCallable), record.TryGetCallable(probe, out var callable));
                AssertSameOutcome(expectedValue, value);
                AssertSameOutcome(expectedCallable, callable);
            }
        }

        // The inline pair (cell 0 on the channel under test), then table pairs on both channels
        // (cells 3 and 6 recorded both channels).
        Assert.Throws<ArgumentException>(() =>
        {
            if (valueFirst) record.RecordValue(cells[0], Seven);
            else record.RecordCallable(cells[0], Nothing);
        });
        Assert.Throws<ArgumentException>(() => record.RecordValue(cells[3], Seven));
        Assert.Throws<ArgumentException>(() => record.RecordCallable(cells[6], Nothing));
        Assert.Throws<ArgumentException>(() =>
        {
            if (valueFirst) record.RecordCallable(cells[0], Nothing);
            else record.RecordValue(cells[0], Seven);
        });
    }

    // A successful VALUE replay preserves both the payload object and the emitted count.
    private static void AssertSameOutcome(EvalResult<Evaluator.CountedResult> expected, EvalResult<Evaluator.CountedResult> actual)
    {
        Assert.Equal(expected.IsError, actual.IsError);
        if (expected.IsError) Assert.Same(expected.Error, actual.Error);
        else
        {
            Assert.Same(expected.Value.Value, actual.Value.Value);
            Assert.Equal(expected.Value.EmittedCount, actual.Value.EmittedCount);
        }
    }

    // A successful CALLABLE replay preserves the algorithm object itself (or the absent callable).
    private static void AssertSameOutcome(EvalResult<Algorithm?> expected, EvalResult<Algorithm?> actual)
    {
        Assert.Equal(expected.IsError, actual.IsError);
        if (expected.IsError) Assert.Same(expected.Error, actual.Error);
        else Assert.Same(expected.Value, actual.Value);
    }

    /// <summary>
    /// Through the adapter: a resolution running inside a VALUE computation and a runtime projection of
    /// the same flow needs both again. Each step is a flow-local DemandCycle that is never published, so
    /// only the record holds it. The first step is held inline and the second in its channel's table,
    /// and the resolver reads both where it asked for them.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task AResolution_ReplaysTwoFlowLocalOutcomes_FromTheInlinePairAndTheTable(bool valueFirst)
    {
        var budget = EvaluationBudget.Create(null);
        budget.MarkAsynchronousRun();
        var ctx = Evaluator.EvalCtx.Empty with { Budget = budget };
        NeedCell? a = null, b = null;
        (EvalError? Value, EvalError? Callable)? replayed = null;
        a = new NeedCell(() => throw new InvalidOperationException(), async () =>
        {
            var resolved = await Evaluator.ResolveAsync(ctx, 0, _ =>
            {
                EvalResult<Evaluator.CountedResult> value = default;
                EvalResult<Algorithm?> callable = default;
                if (valueFirst) value = a!.Demand();
                callable = b!.ProjectCallable();
                if (!valueFirst) value = a!.Demand();
                foreach (var error in new[] { value.IsError ? value.Error : null, callable.IsError ? callable.Error : null })
                    if (error is not null && NeedCell.IsObservationPending(error))
                        return EvalResult<int>.Err(error);
                replayed = (value.IsError ? value.Error : null, callable.IsError ? callable.Error : null);
                return EvalResult<int>.Ok(1);
            });
            Assert.True(resolved.IsOk);
            return Seven;
        }, span: SpanA, budget: budget);
        b = NeedCell.WithRuntimeProjection(() => Seven, () => new(Seven), () => throw new InvalidOperationException(), async () =>
        {
            var value = await a.DemandAsync();
            return value.IsError ? value.Error : Nothing;
        }, SpanB, budget);

        var projected = await b.ProjectCallableAsync().AsTask().WaitAsync(WaitLimit);

        Assert.True(projected.IsOk, projected.IsError ? projected.Error.ToString() : null);
        Assert.NotNull(replayed);
        Assert.Equal(SpanA, Assert.IsType<EvalError.DemandCycle>(replayed.Value.Value).Span);
        Assert.Equal(SpanB, Assert.IsType<EvalError.DemandCycle>(replayed.Value.Callable).Span);
        Assert.Equal(2, budget.ResolutionRetries);
        Assert.True(a.HasCompletedValue);
        Assert.Equal(1, b.ProjectionComputations);
        Assert.False(NeedNode.HasCurrentNode);
    }

    private static long Bytes(Action action)
    {
        var before = GC.GetAllocatedBytesForCurrentThread();
        action();
        return GC.GetAllocatedBytesForCurrentThread() - before;
    }

    /// <summary>
    /// A record that holds one pair, whichever channel, costs the record object alone: recording,
    /// replaying and the progress guard's question allocate nothing (HEAD allocated one table per
    /// channel, 240 bytes or more on .NET 11 x64). The second pair allocates its channel's table.
    /// </summary>
    [Fact]
    public void ARecordsFirstPair_AllocatesNoTable_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var budget = EvaluationBudget.Create(null);
        var cell = NeedCell.WithRuntimeProjection(() => Seven, () => new(Seven), () => Nothing, () => new(Nothing), budget: budget);
        var other = NeedCell.WithRuntimeProjection(() => Seven, () => new(Seven), () => Nothing, () => new(Nothing), budget: budget);
        NeedCell.ResolutionRecord? kept = null;
        void Empty() => kept = new NeedCell.ResolutionRecord();
        void OneValue()
        {
            var record = kept = new NeedCell.ResolutionRecord();
            record.RecordValue(cell, Seven);
            _ = record.Contains(cell, NeedCell.Channel.Value) && record.TryGetValue(cell, out _)
                && !record.Contains(cell, NeedCell.Channel.Callable) && !record.TryGetCallable(cell, out _)
                && !record.Contains(other, NeedCell.Channel.Value);
        }
        void OneCallable()
        {
            var record = kept = new NeedCell.ResolutionRecord();
            record.RecordCallable(cell, Nothing);
            _ = record.Contains(cell, NeedCell.Channel.Callable) && record.TryGetCallable(cell, out _)
                && !record.Contains(cell, NeedCell.Channel.Value) && !record.TryGetValue(cell, out _)
                && !record.Contains(other, NeedCell.Channel.Callable);
        }
        void Two()
        {
            var record = kept = new NeedCell.ResolutionRecord();
            record.RecordCallable(cell, Nothing);
            record.RecordCallable(other, Nothing);
        }
        foreach (var warm in new Action[] { Empty, OneValue, OneCallable, Two }) warm();

        var empty = Bytes(Empty);
        Assert.Equal(empty, Bytes(OneValue));
        Assert.Equal(empty, Bytes(OneCallable));
        Assert.True(Bytes(Two) > empty);
        GC.KeepAlive(kept);
        GcIsolatedAllocation.Complete();
    }
}
