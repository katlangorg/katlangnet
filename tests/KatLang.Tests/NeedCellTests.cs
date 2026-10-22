using KatLang.Evaluation;
using System.Numerics;

namespace KatLang.Tests;

public class NeedCellTests
{
    // Every bounded wait in this file is a hang guard, never a latency claim: what it waits for
    // runs as thread-pool work, which a loaded CI runner can delay well past a tight bound (a
    // 10 s guard timed out in CI in October 2026).
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);

    private static EvalResult<Evaluator.CountedResult> Value(int number = 7)
        => EvalResult<Evaluator.CountedResult>.Ok(new(new Result.Atom((Decimal128)number), 1));

    [Fact]
    public async Task SixtyFourOverlappingDemandsStartOnceAndReuseCompletion()
    {
        var starts = 0;
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var cell = new NeedCell(() => throw new InvalidOperationException(), async () =>
        {
            Interlocked.Increment(ref starts);
            entered.SetResult();
            await release.Task;
            return Value();
        });
        var demands = Enumerable.Range(0, 64).Select(_ => Task.Run(async () => await cell.DemandAsync())).ToArray();
        await entered.Task.WaitAsync(WaitLimit);
        release.SetResult();
        var values = await Task.WhenAll(demands).WaitAsync(WaitLimit);
        Assert.All(values, value => Assert.True(value.IsOk));
        Assert.Equal(1, starts);
        Assert.True(cell.Demand().IsOk);
        Assert.Equal(1, starts);
    }

    [Fact]
    public async Task OrdinaryFailureAndHostExceptionAreStickyAcrossSyncAndAsync()
    {
        var starts = 0;
        EvalResult<Evaluator.CountedResult> Fail() { starts++; return new EvalError.DivByZero(); }
        var cell = new NeedCell(Fail, () => new(Fail()));
        var first = cell.Demand();
        Assert.Equal(KatLangErrorCode.DivisionByZero, first.Error.Code);
        Assert.Same(first.Error, (await cell.DemandAsync()).Error);
        Assert.Same(first.Error, cell.Demand().Error);
        Assert.Equal(1, starts);

        var thrown = new InvalidOperationException("original host failure");
        var hostStarts = 0;
        EvalResult<Evaluator.CountedResult> Throw() { hostStarts++; throw thrown; }
        var host = new NeedCell(Throw, () => new(Throw()));
        Assert.Same(thrown, Assert.Throws<InvalidOperationException>(() => host.Demand()));
        Assert.Same(thrown, await Assert.ThrowsAsync<InvalidOperationException>(async () => await host.DemandAsync()));
        Assert.Equal(1, hostStarts);
    }

    [Fact]
    public async Task CancellationDuringSuspensionNeverRestarts()
    {
        using var stop = new CancellationTokenSource();
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var starts = 0;
        var cell = new NeedCell(() => throw new InvalidOperationException(), async () =>
        {
            starts++;
            entered.SetResult();
            await Task.Delay(Timeout.Infinite, stop.Token);
            return Value();
        });
        var first = cell.DemandAsync().AsTask();
        await entered.Task;
        stop.Cancel();
        await Assert.ThrowsAnyAsync<OperationCanceledException>(() => first);
        Assert.True(first.IsCanceled);
        await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await cell.DemandAsync());
        Assert.ThrowsAny<OperationCanceledException>(() => cell.Demand());
        Assert.Equal(1, starts);
    }

    [Fact]
    public void PreCancelledDemandHasNoEffectAndCallableProjectionDoesNotForce()
    {
        using var stop = new CancellationTokenSource();
        stop.Cancel();
        var starts = 0;
        EvalResult<Evaluator.CountedResult> Evaluate() { starts++; return Value(); }
        var cancelled = new NeedCell(Evaluate, () => new(Evaluate()), token: stop.Token);
        Assert.ThrowsAny<OperationCanceledException>(() => cancelled.Demand());
        Assert.Equal(0, starts);
        var algorithm = new Algorithm.Builtin(BuiltinId.@map);
        var callable = new NeedCell(Evaluate, () => new(Evaluate()), () => EvalResult<Algorithm?>.Ok(algorithm));
        Assert.Same(algorithm, callable.ProjectCallable().Value);
        Assert.Equal(0, starts);
        Assert.True(callable.Demand().IsOk);
        Assert.Equal(1, starts);
    }

    [Fact]
    public async Task HostCancellationWithoutTheRunToken_IsStickyOnBothChannels()
    {
        var cancelled = new OperationCanceledException("host cancelled");
        var starts = 0;
        EvalResult<Evaluator.CountedResult> Cancel()
        {
            starts++;
            throw cancelled;
        }
        var algorithm = new Algorithm.User(null, [], [], [], [new Expr.Num(7)]);
        var cell = new NeedCell(Cancel, () => new(Cancel()), () => EvalResult<Algorithm?>.Ok(algorithm));
        Assert.Same(cancelled, await Assert.ThrowsAsync<OperationCanceledException>(() => cell.DemandAsync().AsTask()));
        Assert.Same(cancelled, Assert.Throws<OperationCanceledException>(() => cell.Demand()));
        Assert.Same(cancelled, Assert.Throws<OperationCanceledException>(() => cell.ProjectCallable()));
        Assert.Equal(1, starts);
    }

    [Fact]
    public async Task DirectAndIndirectAsyncCyclesCompleteWithDemandCycle()
    {
        var span = new SourceSpan(new SourcePosition(2, 3), new SourcePosition(2, 4));
        NeedCell? direct = null;
        direct = new NeedCell(() => direct!.Demand(), () => direct!.DemandAsync(), span: span);
        Assert.Equal(KatLangErrorCode.DemandCycle, direct.Demand().Error.Code);
        Assert.Equal(span, direct.Demand().Error.Span);

        NeedCell? left = null, right = null;
        left = new NeedCell(() => right!.Demand(), async () => { await Task.Yield(); return await right!.DemandAsync(); });
        right = new NeedCell(() => left.Demand(), async () => { await Task.Yield(); return await left.DemandAsync(); });
        var result = await left.DemandAsync().AsTask().WaitAsync(WaitLimit);
        Assert.Equal(KatLangErrorCode.DemandCycle, result.Error.Code);
        Assert.Equal(KatLangErrorCode.DemandCycle, right.Demand().Error.Code);
    }

    [Fact]
    public async Task IndependentlyStartedChainsDetectWaitGraphCycle()
    {
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var starts = 0;
        NeedCell? left = null, right = null;
        async ValueTask<EvalResult<Evaluator.CountedResult>> Evaluate(Func<NeedCell> next)
        {
            if (Interlocked.Increment(ref starts) == 2) entered.SetResult();
            await entered.Task;
            return await next().DemandAsync();
        }
        left = new NeedCell(() => right!.Demand(), () => Evaluate(() => right!));
        right = new NeedCell(() => left.Demand(), () => Evaluate(() => left));
        var results = await Task.WhenAll(Task.Run(async () => await left.DemandAsync()), Task.Run(async () => await right.DemandAsync()))
            .WaitAsync(WaitLimit);
        Assert.All(results, result => Assert.Equal(KatLangErrorCode.DemandCycle, result.Error.Code));
        Assert.Equal(2, starts);
    }
    [Fact]
    public void ReachedResourceLimitEndsBothChannelsWithoutChangingCompletedValue()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 1 });
        var starts = 0;
        EvalResult<Evaluator.CountedResult> Evaluate() { starts++; return Value(); }
        var callable = new Algorithm.Builtin(BuiltinId.@map);
        var completed = new NeedCell(Evaluate, () => new(Evaluate()), () => EvalResult<Algorithm?>.Ok(callable), budget: budget);
        Assert.True(completed.Demand().IsOk);
        Assert.Null(budget.TryEnterInvocation());
        var failure = Assert.IsType<EvalError.EvaluationDepthExceeded>(budget.TryEnterInvocation());
        budget.ExitInvocation();
        Assert.Same(failure, completed.Demand().Error);
        Assert.Same(failure, completed.ProjectCallable().Error);
        Assert.Same(failure, budget.TryChargeStep());
        Assert.Equal(1, starts);
        Assert.Equal(1, budget.ConsumedSteps);
        Assert.Equal(0, budget.CurrentDepth);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ResourceFailureDuringFirstDemand_IsStickyAndStopsOtherCells(bool asynchronousFirst)
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxSteps = 1 });
        var span = new SourceSpan(2, 3, 2, 4);
        var failure = new EvalError.EvaluationStepLimitExceeded(1) { Span = span };
        var starts = 0;
        var projections = 0;
        EvalResult<Evaluator.CountedResult> Fail() { starts++; return failure; }
        var cell = new NeedCell(Fail, () => new(Fail()),
            () => { projections++; return EvalResult<Algorithm?>.Ok(new Algorithm.Builtin(BuiltinId.@map)); },
            span: span, budget: budget);

        var first = asynchronousFirst ? await cell.DemandAsync() : cell.Demand();
        Assert.Same(failure, first.Error);
        Assert.Same(failure, cell.Demand().Error);
        Assert.Same(failure, (await cell.DemandAsync()).Error);
        var projection = cell.ProjectCallable();
        Assert.True(projection.IsError);
        Assert.Same(failure, projection.Error);
        Assert.Equal(span, first.Error.Span);
        Assert.Equal(1, starts);
        Assert.Equal(0, projections);

        var otherStarts = 0;
        EvalResult<Evaluator.CountedResult> Other() { otherStarts++; return Value(); }
        var other = new NeedCell(Other, () => new(Other()), budget: budget);
        Assert.Same(failure, other.Demand().Error);
        Assert.Same(failure, (await other.DemandAsync()).Error);
        Assert.Equal(0, otherStarts);
        Assert.Equal(0, budget.ConsumedSteps);
    }

    [Fact]
    public void OneHundredThousandProductionParameterTransports_ShareOneAddressOnAConstrainedStack()
    {
        AstStructuralDepthProcessTests.RunOnThreadWithStack(512 * 1024, () =>
        {
            var starts = 0;
            var projections = 0;
            var span = new SourceSpan(2, 3, 2, 4);
            var algorithm = new Algorithm.User(null, [], [], [], [new Expr.Num(7)]);
            var budget = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 1, MaxSteps = 1 });
            EvalResult<Evaluator.CountedResult> Evaluate() { starts++; return Value(); }
            var original = new NeedCell(Evaluate, () => new(Evaluate()),
                () => { projections++; return EvalResult<Algorithm?>.Ok(algorithm); }, span: span, budget: budget);
            var current = original;
            var ctx = Evaluator.EvalCtx.Empty with { Budget = budget };
            for (var hop = 0; hop < 100_000; hop++)
            {
                ctx = ctx.WithNeedEnv([("x", current)]);
                current = Evaluator.SupplyCell(new Expr.Param("x"), ctx, []);
                Assert.Same(original, current);
            }
            Assert.Equal(0, starts);
            Assert.Equal(0, budget.ConsumedSteps);
            Assert.Equal(0, budget.PeakDepth);
            Assert.Equal(span, current.Span);
            Assert.Same(algorithm, current.ProjectCallable().Value);
            Assert.Equal(0, starts);
            Assert.True(current.Demand().IsOk);
            Assert.True(current.DemandAsync().GetAwaiter().GetResult().IsOk);
            Assert.Equal(1, starts);
            Assert.Equal(1, projections);
            Assert.Equal(0, budget.ConsumedSteps);
        }, TimeSpan.FromSeconds(30));
    }

    // ── META-LIFE-2: a completed VALUE releases its flight ───────────────────────────────────
    // The shared completion exists only while the computation is active: the memo or stored
    // exception is published and `_flight` cleared in one gate section, a joined observer keeps
    // its own task, and every later observer reads the memo first. Overlap is established by
    // observed state (a computation's entry signal, an observer cell's wait-for edge), never by a
    // settle delay; bounded waits are hang guards.

    private static async Task Until(Func<bool> condition)
    {
        var deadline = DateTime.UtcNow + WaitLimit;
        while (!condition())
        {
            if (DateTime.UtcNow > deadline) throw new TimeoutException("controlled-overlap handshake");
            await Task.Delay(1);
        }
    }

    // A cell whose VALUE computation, started on either path, signals `entered` and holds until
    // `release` completes; `outcome` is its result (it may throw).
    private static NeedCell GatedCell(EvaluationBudget? budget, TaskCompletionSource entered, Task release,
        Func<EvalResult<Evaluator.CountedResult>> outcome, Action? started = null, CancellationToken token = default)
        => new(() =>
        {
            started?.Invoke();
            entered.TrySetResult();
            release.WaitAsync(WaitLimit).GetAwaiter().GetResult();
            return outcome();
        }, async () =>
        {
            started?.Invoke();
            entered.TrySetResult();
            await release.WaitAsync(WaitLimit);
            return outcome();
        }, budget: budget, token: token);

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task CompletedSuccess_ReleasesTheFlight_AndLaterDemandsReadTheMemo(bool asynchronousFirst)
    {
        var budget = EvaluationBudget.Create(null);
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var value = Value(41);
        var starts = 0;
        var cell = GatedCell(budget, entered, release.Task, () => value, () => Interlocked.Increment(ref starts));
        Assert.False(cell.HasValueInFlight);
        var first = asynchronousFirst
            ? cell.DemandAsync().AsTask()
            : Task.Factory.StartNew(() => cell.Demand(), TaskCreationOptions.LongRunning);
        await entered.Task.WaitAsync(WaitLimit);
        Assert.True(cell.HasValueInFlight);
        Assert.False(cell.HasCompletedValue);
        release.SetResult();
        var result = await first.WaitAsync(WaitLimit);

        Assert.False(cell.HasValueInFlight);
        Assert.True(cell.HasCompletedValue);
        Assert.Same(value.Value.Value, result.Value.Value);
        Assert.Same(value.Value.Value, cell.Demand().Value.Value);
        Assert.Same(value.Value.Value, (await cell.DemandAsync()).Value.Value);
        Assert.False(cell.HasValueInFlight);
        Assert.Equal(1, starts);
        Assert.Equal(0, cell.ActiveDependencyCount);
        Assert.False(NeedNode.HasCurrentNode);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task CompletedOrdinaryFailure_ReleasesTheFlight_AndKeepsTheErrorObject(bool asynchronousFirst)
    {
        var failure = new EvalError.DivByZero { Span = new SourceSpan(2, 3, 2, 4) };
        var starts = 0;
        NeedCell? cell = null;
        EvalResult<Evaluator.CountedResult> Fail()
        {
            starts++;
            Assert.True(cell!.HasValueInFlight);
            return failure;
        }
        cell = new NeedCell(Fail, () => new(Fail()), budget: EvaluationBudget.Create(null));
        var first = asynchronousFirst ? await cell.DemandAsync() : cell.Demand();
        Assert.Same(failure, first.Error);
        Assert.False(cell.HasValueInFlight);
        Assert.Same(failure, cell.Demand().Error);
        Assert.Same(failure, (await cell.DemandAsync()).Error);
        Assert.False(cell.HasValueInFlight);
        Assert.Equal(1, starts);
    }

    [Fact]
    public async Task CompletedHostException_ReleasesTheFlight_EveryJoinedObserverAndLaterDemandRethrowsTheOriginal()
    {
        var budget = EvaluationBudget.Create(null);
        var thrown = new InvalidOperationException("original host failure");
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var starts = 0;
        var target = GatedCell(budget, entered, release.Task, () => throw thrown, () => Interlocked.Increment(ref starts));
        // Observers are cells of the same run, so each one's wait-for edge proves it is inside its
        // observation of the active computation before the computation is released.
        var observers = Enumerable.Range(0, 8)
            .Select(_ => new NeedCell(() => target.Demand(), () => target.DemandAsync(), budget: budget)).ToArray();
        var demands = observers.Select((observer, index) => index % 2 == 0
            ? observer.DemandAsync().AsTask()
            : Task.Factory.StartNew(() => observer.Demand(), TaskCreationOptions.LongRunning)).ToArray();
        await entered.Task.WaitAsync(WaitLimit);
        await Until(() => observers.All(observer => observer.ActiveDependencyCount == 1));
        Assert.True(target.HasValueInFlight);
        release.SetResult();

        foreach (var demand in demands)
            Assert.Same(thrown, await Assert.ThrowsAsync<InvalidOperationException>(() => demand.WaitAsync(WaitLimit)));
        Assert.False(target.HasValueInFlight);
        Assert.All(observers, observer => Assert.False(observer.HasValueInFlight));
        Assert.All(observers, observer => Assert.Equal(0, observer.ActiveDependencyCount));
        Assert.Same(thrown, Assert.Throws<InvalidOperationException>(() => target.Demand()));
        var replayed = await Assert.ThrowsAsync<InvalidOperationException>(async () => await target.DemandAsync());
        Assert.Same(thrown, replayed);
        // EDI replay appends the rethrow site to the original trace instead of replacing it.
        Assert.Contains(nameof(GatedCell), replayed.StackTrace);
        Assert.Equal(1, starts);
    }

    [Fact]
    public async Task RunTokenCancellationDuringSuspension_ReleasesTheFlight_WithTheOriginalExceptionAndToken()
    {
        var budget = EvaluationBudget.Create(null);
        using var stop = new CancellationTokenSource();
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var starts = 0;
        var target = new NeedCell(() => throw new InvalidOperationException("synchronous start"), async () =>
        {
            Interlocked.Increment(ref starts);
            entered.TrySetResult();
            await Task.Delay(Timeout.Infinite, stop.Token);
            return Value();
        }, budget: budget, token: stop.Token);
        var observers = Enumerable.Range(0, 8)
            .Select(_ => new NeedCell(() => target.Demand(), () => target.DemandAsync(), budget: budget)).ToArray();
        var first = target.DemandAsync().AsTask();
        await entered.Task.WaitAsync(WaitLimit);
        var joined = observers.Select(observer => observer.DemandAsync().AsTask()).ToArray();
        await Until(() => observers.All(observer => observer.ActiveDependencyCount == 1));
        Assert.True(target.HasValueInFlight);
        stop.Cancel();

        var original = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => first.WaitAsync(WaitLimit));
        Assert.True(first.IsCanceled);
        Assert.Equal(stop.Token, original.CancellationToken);
        foreach (var observer in joined)
            Assert.Same(original, await Assert.ThrowsAnyAsync<OperationCanceledException>(() => observer.WaitAsync(WaitLimit)));
        Assert.False(target.HasValueInFlight);
        Assert.True(target.HasCompletedValue);
        // The run's token is cancelled, so a later observation stops at its entry check.
        Assert.Equal(stop.Token, Assert.ThrowsAny<OperationCanceledException>(() => target.Demand()).CancellationToken);
        Assert.Equal(stop.Token, (await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await target.DemandAsync())).CancellationToken);
        Assert.Equal(1, starts);
        Assert.All(observers, observer => Assert.Equal(0, observer.ActiveDependencyCount));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task HostCancellation_ReleasesTheFlight_AndReplaysTheOriginalInstanceAndToken(bool asynchronousFirst)
    {
        using var host = new CancellationTokenSource();
        host.Cancel();
        var cancelled = new OperationCanceledException("host cancelled", host.Token);
        var starts = 0;
        NeedCell? cell = null;
        EvalResult<Evaluator.CountedResult> Cancel()
        {
            starts++;
            Assert.True(cell!.HasValueInFlight);
            throw cancelled;
        }
        cell = new NeedCell(Cancel, async () => { await Task.Yield(); return Cancel(); }, budget: EvaluationBudget.Create(null));
        var first = asynchronousFirst
            ? await Assert.ThrowsAsync<OperationCanceledException>(() => cell.DemandAsync().AsTask())
            : Assert.Throws<OperationCanceledException>(() => cell.Demand());
        Assert.Same(cancelled, first);
        Assert.False(cell.HasValueInFlight);
        Assert.Same(cancelled, Assert.Throws<OperationCanceledException>(() => cell.Demand()));
        var later = await Assert.ThrowsAsync<OperationCanceledException>(() => cell.DemandAsync().AsTask());
        Assert.Same(cancelled, later);
        Assert.Equal(host.Token, later.CancellationToken);
        Assert.Equal(1, starts);
    }

    [Fact]
    public async Task ThirtyTwoOverlappingObservers_JoinOneFlight_ThatIsReleasedOnceAllSettle()
    {
        var budget = EvaluationBudget.Create(null);
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var value = Value(9);
        var starts = 0;
        var target = GatedCell(budget, entered, release.Task, () => value, () => Interlocked.Increment(ref starts));
        var observers = Enumerable.Range(0, 32)
            .Select(_ => new NeedCell(() => target.Demand(), () => target.DemandAsync(), budget: budget)).ToArray();
        // A quarter observe synchronously on dedicated threads, the rest asynchronously.
        var demands = observers.Select((observer, index) => index % 4 == 0
            ? Task.Factory.StartNew(() => observer.Demand(), TaskCreationOptions.LongRunning)
            : Task.Run(async () => await observer.DemandAsync())).ToArray();
        await entered.Task.WaitAsync(WaitLimit);
        await Until(() => observers.All(observer => observer.ActiveDependencyCount == 1));
        Assert.True(target.HasValueInFlight);
        Assert.False(target.HasCompletedValue);
        Assert.Equal(1, starts);
        release.SetResult();

        var results = await Task.WhenAll(demands).WaitAsync(WaitLimit);
        Assert.All(results, result => Assert.Same(value.Value.Value, result.Value.Value));
        Assert.Equal(1, starts);
        Assert.False(target.HasValueInFlight);
        Assert.All(observers, observer => Assert.False(observer.HasValueInFlight));
        Assert.All(observers, observer => Assert.Equal(0, observer.ActiveDependencyCount));
        Assert.Equal(0, target.ActiveDependencyCount);
        for (var again = 0; again < 4; again++)
        {
            Assert.Same(value.Value.Value, target.Demand().Value.Value);
            Assert.Same(value.Value.Value, (await target.DemandAsync()).Value.Value);
            Assert.Same(value.Value.Value, observers[again].Demand().Value.Value);
        }
        Assert.Equal(1, starts);
        Assert.False(target.HasValueInFlight);
    }

    [Fact]
    public async Task ObserverArrivingDuringCompletion_ReadsTheFlightOrTheMemo_NeverRestarts()
    {
        // The test holds the cell's own gate while the producer finishes, so the producer's
        // publication (memo + release + settle, one gate section) and the late observers' entry
        // contend for it: each late observer is started before publication can be visible, and it
        // then enters before, between or after the producer's section (whichever the gate admits
        // in that iteration); in every case it reads the flight or the memo, never a restart.
        var gateField = typeof(NeedCell).GetField("_gate", System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Instance)!;
        for (var iteration = 0; iteration < 64; iteration++)
        {
            var budget = EvaluationBudget.Create(null);
            var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
            var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
            var returning = 0;
            var starts = 0;
            var value = Value(iteration);
            var target = GatedCell(budget, entered, release.Task, () => { Volatile.Write(ref returning, 1); return value; },
                () => Interlocked.Increment(ref starts));
            var producer = target.DemandAsync().AsTask();
            await entered.Task.WaitAsync(WaitLimit);
            var gate = gateField.GetValue(target)!;
            using var arrivals = new CountdownEvent(2);
            Task<EvalResult<Evaluator.CountedResult>>[] late;
            Monitor.Enter(gate);
            try
            {
                release.SetResult();
                Assert.True(SpinWait.SpinUntil(() => Volatile.Read(ref returning) == 1, WaitLimit));
                late =
                [
                    Task.Factory.StartNew(() => { arrivals.Signal(); return target.Demand(); }, TaskCreationOptions.LongRunning),
                    Task.Run(async () => { arrivals.Signal(); return await target.DemandAsync(); }),
                ];
                // Both observers have actually started while publication is blocked; merely
                // scheduling tasks would allow them to start only after completion.
                Assert.True(arrivals.Wait(WaitLimit));
                Assert.All(late, observer => Assert.False(observer.IsCompleted));
                Assert.False(target.HasCompletedValue); // reentrant on this thread: the memo is not yet published
            }
            finally { Monitor.Exit(gate); }

            Assert.Same(value.Value.Value, (await producer.WaitAsync(WaitLimit)).Value.Value);
            foreach (var observer in late)
                Assert.Same(value.Value.Value, (await observer.WaitAsync(WaitLimit)).Value.Value);
            Assert.Equal(1, starts);
            Assert.False(target.HasValueInFlight);
            Assert.True(target.HasCompletedValue);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ReentrantDemand_IsDemandCycleForTheReentry_TheOwnerCompletesOnceAndReleases(bool asynchronous)
    {
        var budget = EvaluationBudget.Create(null);
        var span = new SourceSpan(5, 1, 5, 2);
        var value = Value(3);
        var starts = 0;
        NeedCell? direct = null;
        void CheckReentry(EvalResult<Evaluator.CountedResult> reentry)
        {
            Assert.Equal(span, Assert.IsType<EvalError.DemandCycle>(reentry.Error).Span);
            Assert.True(direct!.HasValueInFlight);
            Assert.False(direct.HasCompletedValue);
        }
        direct = new NeedCell(() =>
        {
            starts++;
            CheckReentry(direct!.Demand());
            return value;
        }, async () =>
        {
            starts++;
            await Task.Yield();
            CheckReentry(await direct!.DemandAsync());
            return value;
        }, span: span, budget: budget);
        var result = asynchronous ? await direct.DemandAsync().AsTask().WaitAsync(WaitLimit) : direct.Demand();
        Assert.Same(value.Value.Value, result.Value.Value);
        Assert.False(direct.HasValueInFlight);
        Assert.Same(value.Value.Value, direct.Demand().Value.Value);
        Assert.Equal(1, starts);

        // Indirect: left → right → left. The re-entering observation (right's) is refused; right
        // returns that refusal as its own sticky outcome, and left then completes normally.
        NeedCell? left = null, right = null;
        var leftValue = Value(4);
        left = new NeedCell(() =>
        {
            Assert.Equal(KatLangErrorCode.DemandCycle, right!.Demand().Error.Code);
            Assert.True(left!.HasValueInFlight);
            Assert.False(right.HasValueInFlight);
            return leftValue;
        }, async () =>
        {
            await Task.Yield();
            Assert.Equal(KatLangErrorCode.DemandCycle, (await right!.DemandAsync()).Error.Code);
            Assert.True(left!.HasValueInFlight);
            Assert.False(right.HasValueInFlight);
            return leftValue;
        }, budget: budget);
        right = new NeedCell(() => left.Demand(), async () => { await Task.Yield(); return await left.DemandAsync(); }, budget: budget);
        var leftResult = asynchronous ? await left.DemandAsync().AsTask().WaitAsync(WaitLimit) : left.Demand();
        Assert.Same(leftValue.Value.Value, leftResult.Value.Value);
        Assert.False(left.HasValueInFlight);
        Assert.False(right.HasValueInFlight);
        var cycle = right.Demand().Error;
        Assert.IsType<EvalError.DemandCycle>(cycle);
        Assert.Same(cycle, (await right.DemandAsync()).Error);
        Assert.Equal(0, left.ActiveDependencyCount);
        Assert.Equal(0, right.ActiveDependencyCount);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task MixedValueCallableCycle_ReleasesBothFlights_AndChannelsStayIndependent(bool asynchronous)
    {
        var budget = EvaluationBudget.Create(null);
        var count = new Algorithm.Builtin(BuiltinId.@count);
        var valueStarts = 0;
        var projections = 0;
        NeedCell? valueCell = null;
        // CALLABLE → VALUE → CALLABLE: the projection demands the cell whose VALUE projects it.
        var projected = NeedCell.WithRuntimeProjection(() => Value(), () => new(Value()), () =>
        {
            projections++;
            var demanded = valueCell!.Demand();
            return demanded.IsError ? demanded.Error : EvalResult<Algorithm?>.Ok(count);
        }, async () =>
        {
            projections++;
            await Task.Yield();
            var demanded = await valueCell!.DemandAsync();
            return demanded.IsError ? demanded.Error : EvalResult<Algorithm?>.Ok(count);
        }, budget: budget);
        valueCell = new NeedCell(() =>
        {
            valueStarts++;
            var projection = projected.ProjectCallable();
            Assert.True(valueCell!.HasValueInFlight);
            return projection.IsError ? projection.Error : Value();
        }, async () =>
        {
            valueStarts++;
            await Task.Yield();
            var projection = await projected.ProjectCallableAsync();
            Assert.True(valueCell!.HasValueInFlight);
            return projection.IsError ? projection.Error : Value();
        }, () => EvalResult<Algorithm?>.Ok(count), budget: budget);

        var result = asynchronous ? await valueCell.DemandAsync().AsTask().WaitAsync(WaitLimit) : valueCell.Demand();
        var cycle = Assert.IsType<EvalError.DemandCycle>(result.Error);
        Assert.False(valueCell.HasValueInFlight);
        Assert.False(projected.HasProjectionInFlight);
        Assert.Same(cycle, valueCell.Demand().Error);
        Assert.Same(cycle, (await valueCell.DemandAsync()).Error);
        Assert.Equal(KatLangErrorCode.DemandCycle, projected.ProjectCallable().Error.Code);
        Assert.Equal(1, valueStarts);
        Assert.Equal(1, projections);
        // The VALUE cell's own CALLABLE and the projected cell's own VALUE are untouched.
        Assert.Same(count, valueCell.ProjectCallable().Value);
        Assert.False(projected.HasCompletedValue);
        Assert.True(projected.Demand().IsOk);
        Assert.False(projected.HasValueInFlight);
        Assert.Equal(0, valueCell.ActiveDependencyCount);
        Assert.Equal(0, projected.ProjectionActiveDependencyCount);

        // Noncyclic: a completed (released) VALUE serves a later runtime projection from its memo.
        var sourceStarts = 0;
        var source = new NeedCell(() => { sourceStarts++; return Value(5); }, () => { sourceStarts++; return new(Value(5)); }, budget: budget);
        Assert.True(source.Demand().IsOk);
        Assert.False(source.HasValueInFlight);
        var link = NeedCell.WithRuntimeProjection(() => Value(), () => new(Value()),
            () => source.Demand().IsOk ? EvalResult<Algorithm?>.Ok(count) : EvalResult<Algorithm?>.Ok(null),
            async () => (await source.DemandAsync()).IsOk ? EvalResult<Algorithm?>.Ok(count) : EvalResult<Algorithm?>.Ok(null),
            budget: budget);
        Assert.Same(count, (asynchronous ? await link.ProjectCallableAsync() : link.ProjectCallable()).Value);
        Assert.Equal(1, sourceStarts);
        Assert.False(source.HasValueInFlight);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ResourceLimit_ReleasesTheFlight_KeepsItsIdentity_AndTerminalityWinsOverAReleasedSuccess(bool asynchronousFirst)
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxSteps = 1 });
        var failure = new EvalError.EvaluationStepLimitExceeded(1) { Span = new SourceSpan(2, 3, 2, 4) };
        var starts = 0;
        EvalResult<Evaluator.CountedResult> Fail() { starts++; return failure; }
        var cell = new NeedCell(Fail, () => new(Fail()), budget: budget);
        var first = asynchronousFirst ? await cell.DemandAsync() : cell.Demand();
        Assert.Same(failure, first.Error);
        Assert.False(cell.HasValueInFlight);
        Assert.Same(failure, cell.Demand().Error);
        Assert.Same(failure, (await cell.DemandAsync()).Error);
        Assert.Equal(1, starts);

        // A released SUCCESS of a run that later becomes terminal answers the terminal outcome.
        var depth = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 1 });
        var completed = new NeedCell(() => Value(), () => new(Value()), budget: depth);
        Assert.True((asynchronousFirst ? await completed.DemandAsync() : completed.Demand()).IsOk);
        Assert.False(completed.HasValueInFlight);
        Assert.Null(depth.TryEnterInvocation());
        var terminal = Assert.IsType<EvalError.EvaluationDepthExceeded>(depth.TryEnterInvocation());
        depth.ExitInvocation();
        Assert.Same(terminal, completed.Demand().Error);
        Assert.Same(terminal, (await completed.DemandAsync()).Error);
        Assert.False(completed.HasValueInFlight);
    }

    [Fact]
    public async Task PreCancelledAndTerminalDemands_StartNoComputationAndNoFlight()
    {
        using var stop = new CancellationTokenSource();
        stop.Cancel();
        var starts = 0;
        EvalResult<Evaluator.CountedResult> Evaluate() { starts++; return Value(); }
        var cancelled = new NeedCell(Evaluate, () => new(Evaluate()), budget: EvaluationBudget.Create(null), token: stop.Token);
        Assert.ThrowsAny<OperationCanceledException>(() => cancelled.Demand());
        await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await cancelled.DemandAsync());
        Assert.False(cancelled.HasValueInFlight);
        Assert.False(cancelled.HasCompletedValue);

        var depth = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 1 });
        Assert.Null(depth.TryEnterInvocation());
        var terminal = depth.TryEnterInvocation();
        depth.ExitInvocation();
        var unstarted = new NeedCell(Evaluate, () => new(Evaluate()), budget: depth);
        Assert.Same(terminal, unstarted.Demand().Error);
        Assert.Same(terminal, (await unstarted.DemandAsync()).Error);
        Assert.False(unstarted.HasValueInFlight);
        Assert.False(unstarted.HasCompletedValue);
        Assert.Equal(0, starts);
    }

    [Fact]
    public async Task CancellationAfterReleasedSuccess_PrecedesTheMemo_WithoutRestartingOrCharging()
    {
        using var stop = new CancellationTokenSource();
        var budget = EvaluationBudget.Create(null, cancellationToken: stop.Token);
        var starts = 0;
        EvalResult<Evaluator.CountedResult> Evaluate() { starts++; return Value(); }
        var cell = new NeedCell(Evaluate, () => new(Evaluate()), budget: budget, token: stop.Token);
        Assert.True((await cell.DemandAsync()).IsOk);
        Assert.True(cell.HasCompletedValue);
        Assert.False(cell.HasValueInFlight);
        var steps = budget.ConsumedSteps;

        stop.Cancel();
        Assert.Equal(stop.Token, Assert.ThrowsAny<OperationCanceledException>(() => cell.Demand()).CancellationToken);
        var asynchronous = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => cell.DemandAsync().AsTask());
        Assert.Equal(stop.Token, asynchronous.CancellationToken);
        Assert.True(cell.HasCompletedValue);
        Assert.False(cell.HasValueInFlight);
        Assert.Equal(1, starts);
        Assert.Equal(steps, budget.ConsumedSteps);
    }

    [Fact]
    public async Task ReadyCell_IsCompleteWithoutAFlight()
    {
        var value = Value(8).Value;
        var ready = NeedCell.Ready(value);
        Assert.False(ready.HasValueInFlight);
        Assert.True(ready.HasCompletedValue);
        Assert.Same(value.Value, ready.Demand().Value.Value);
        Assert.Same(value.Value, (await ready.DemandAsync()).Value.Value);
        Assert.False(ready.HasValueInFlight);
    }

    [Fact]
    public async Task ReleasedCellOfOneRun_DoesNotLinkOrEndAnotherRun()
    {
        var first = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 1 });
        var second = EvaluationBudget.Create(null);
        var starts = 0;
        var shared = new NeedCell(() => { starts++; return Value(1); }, () => { starts++; return new(Value(1)); }, budget: first);
        Assert.True(shared.Demand().IsOk);
        Assert.False(shared.HasValueInFlight);
        NeedCell? other = null;
        other = new NeedCell(() =>
        {
            Assert.True(shared.Demand().IsOk);
            Assert.Equal(0, other!.ActiveDependencyCount); // a parent of another run records no edge
            return Value(2);
        }, async () =>
        {
            Assert.True((await shared.DemandAsync()).IsOk);
            Assert.Equal(0, other!.ActiveDependencyCount);
            return Value(2);
        }, budget: second);
        Assert.True((await other.DemandAsync()).IsOk);
        Assert.False(other.HasValueInFlight);

        // Ending the first run ends its released cell's observations, never the second run's.
        Assert.Null(first.TryEnterInvocation());
        var terminal = first.TryEnterInvocation();
        first.ExitInvocation();
        Assert.Same(terminal, shared.Demand().Error);
        Assert.True(other.Demand().IsOk);
        Assert.Null(second.CheckContinuation());
        Assert.Equal(1, starts);
    }

    [Fact]
    public async Task ReleasedFlight_IsCollectibleWhileItsCellStaysReachable()
    {
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var cell = GatedCell(EvaluationBudget.Create(null), entered, release.Task, () => Value());
        var demands = Enumerable.Range(0, 4).Select(_ => Task.Run(async () => (await cell.DemandAsync()).IsOk)).ToArray();
        await entered.Task.WaitAsync(WaitLimit);
        var (source, task) = WeakFlight(cell);
        Assert.True(source.IsAlive);
        release.SetResult();
        Assert.All(await Task.WhenAll(demands).WaitAsync(WaitLimit), Assert.True);
        Assert.False(cell.HasValueInFlight);

        // Every observer has unwound; the cell is the only remaining candidate root.
        for (var attempt = 0; attempt < 10 && (source.IsAlive || task.IsAlive); attempt++)
        {
            GC.Collect();
            GC.WaitForPendingFinalizers();
            GC.Collect();
            if (source.IsAlive || task.IsAlive) await Task.Delay(10);
        }
        Assert.False(source.IsAlive);
        Assert.False(task.IsAlive);
        Assert.True(cell.Demand().IsOk);
        GC.KeepAlive(cell);
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static (WeakReference Source, WeakReference Task) WeakFlight(NeedCell cell)
    {
        var flight = (TaskCompletionSource<EvalResult<Evaluator.CountedResult>>)typeof(NeedCell)
            .GetField("_flight", System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Instance)!
            .GetValue(cell)!;
        return (new WeakReference(flight), new WeakReference(flight.Task));
    }
}
