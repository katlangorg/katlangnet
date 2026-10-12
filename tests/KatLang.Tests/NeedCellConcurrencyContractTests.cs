using System.Collections.Concurrent;
using System.Numerics;
using KatLang.Evaluation;
using KatLang.Formatting;

namespace KatLang.Tests;

/// <summary>
/// The concurrency contract of <see cref="NeedCell"/> (C# evaluator cleanup, October 2026).
/// <list type="bullet">
///   <item>A cell belongs to the run whose budget it carries, and the run's wait-for graph lives under
///   that budget's gate (<see cref="EvaluationBudget.NeedDependencyGate"/>), so independent runs
///   never contend for one process-wide lock.</item>
///   <item>A parent from another run records no edge. Such a parent is the AsyncLocal current cell
///   flowing into a run that a host operation starts.</item>
///   <item>Cycles among one run's cells are still detected, across independently started flows.</item>
///   <item>An edge lives exactly while its demand frame is active, on every exit.</item>
/// </list>
/// The single-flight and sticky-outcome laws are <see cref="NeedCellTests"/>; this class pins what
/// the per-run graph adds. The hang guards are generous bounds, never latency claims.
/// </summary>
public sealed class NeedCellConcurrencyContractTests
{
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);
    // The 16-worker integration stress run shares CPU and continuation scheduling with the full
    // suite. October 2026 V3 timed out its former 30 s worker budget (42 s including the sequential
    // controls), while the unchanged check took about 1 s alone. Keep the cell-level hang guards
    // above at 30 s; give this whole workload the heavy probe tests' 120 s budget.
    private static readonly TimeSpan ParallelRunBudget = TimeSpan.FromSeconds(120);

    private static EvalResult<Evaluator.CountedResult> Value(int number = 7)
        => EvalResult<Evaluator.CountedResult>.Ok(new(new Result.Atom((Decimal128)number), 1));

    [Fact]
    public async Task OneRunsCells_DetectDirectIndirectAndCrossFlowCycles()
    {
        var budget = EvaluationBudget.Create(null);
        NeedCell? direct = null;
        direct = new NeedCell(() => direct!.Demand(), () => direct!.DemandAsync(), budget: budget);
        Assert.Equal(KatLangErrorCode.DemandCycle, direct.Demand().Error.Code);

        NeedCell? left = null, right = null;
        left = new NeedCell(() => right!.Demand(), async () => { await Task.Yield(); return await right!.DemandAsync(); }, budget: budget);
        right = new NeedCell(() => left.Demand(), async () => { await Task.Yield(); return await left.DemandAsync(); }, budget: budget);
        Assert.Equal(KatLangErrorCode.DemandCycle, (await left.DemandAsync().AsTask().WaitAsync(WaitLimit)).Error.Code);
        Assert.Equal(KatLangErrorCode.DemandCycle, right.Demand().Error.Code);

        // Two independently started flows over one run's cells close a wait-graph cycle.
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var starts = 0;
        NeedCell? first = null, second = null;
        async ValueTask<EvalResult<Evaluator.CountedResult>> Evaluate(Func<NeedCell> next)
        {
            if (Interlocked.Increment(ref starts) == 2) entered.SetResult();
            await entered.Task;
            return await next().DemandAsync();
        }
        first = new NeedCell(() => second!.Demand(), () => Evaluate(() => second!), budget: budget);
        second = new NeedCell(() => first.Demand(), () => Evaluate(() => first), budget: budget);
        var results = await Task.WhenAll(Task.Run(async () => await first.DemandAsync()), Task.Run(async () => await second.DemandAsync()))
            .WaitAsync(WaitLimit);
        Assert.All(results, result => Assert.Equal(KatLangErrorCode.DemandCycle, result.Error.Code));
        Assert.Equal(0, first.ActiveDependencyCount);
        Assert.Equal(0, second.ActiveDependencyCount);
    }

    [Fact]
    public async Task OverlappingDemandsOfOneRunsCell_StartOnce()
    {
        var budget = EvaluationBudget.Create(null);
        var starts = 0;
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var cell = new NeedCell(() => throw new InvalidOperationException(), async () =>
        {
            Interlocked.Increment(ref starts);
            entered.SetResult();
            await release.Task;
            return Value();
        }, budget: budget);
        var demands = Enumerable.Range(0, 64).Select(_ => Task.Run(async () => await cell.DemandAsync())).ToArray();
        await entered.Task.WaitAsync(WaitLimit);
        release.SetResult();
        var values = await Task.WhenAll(demands).WaitAsync(WaitLimit);
        Assert.All(values, value => Assert.True(value.IsOk));
        Assert.Equal(1, starts);
    }

    public static TheoryData<string, bool> Exits => new()
    {
        { "success", false }, { "success", true },
        { "failure", false }, { "failure", true },
        { "host exception", false }, { "host exception", true },
        { "cancellation", false }, { "cancellation", true },
        { "cycle", false }, { "cycle", true },
    };

    /// <summary>
    /// The edge parent → child exists while the child's evaluation runs for the parent, and it is gone
    /// after every kind of exit: success, an ordinary failure, a host exception, a cancellation, or a
    /// cycle the child closes back to its waiting parent.
    /// </summary>
    [Theory]
    [MemberData(nameof(Exits))]
    public async Task AnEdgeLivesExactlyWhileItsDemandIsActive(string exit, bool asynchronous)
    {
        var budget = EvaluationBudget.Create(null);
        NeedCell? parent = null;
        var during = -1;
        EvalResult<Evaluator.CountedResult> Finish()
        {
            during = parent!.ActiveDependencyCount;
            return exit switch
            {
                "success" => Value(),
                "failure" => new EvalError.DivByZero(),
                "host exception" => throw new InvalidOperationException("host failure"),
                "cancellation" => throw new OperationCanceledException("cancelled"),
                "cycle" => parent!.Demand(),
                _ => throw new ArgumentOutOfRangeException(nameof(exit)),
            };
        }
        async ValueTask<EvalResult<Evaluator.CountedResult>> FinishAsync()
        {
            await Task.Yield();
            if (exit == "cycle")
            {
                during = parent!.ActiveDependencyCount;
                return await parent.DemandAsync();
            }

            return Finish();
        }

        var child = new NeedCell(Finish, FinishAsync, budget: budget);
        parent = new NeedCell(() => child.Demand(), async () => await child.DemandAsync(), budget: budget);
        try
        {
            var outcome = asynchronous ? await parent.DemandAsync().AsTask().WaitAsync(WaitLimit) : parent.Demand();
            Assert.Equal(exit is "success", outcome.IsOk);
            if (exit == "cycle") Assert.Equal(KatLangErrorCode.DemandCycle, outcome.Error.Code);
        }
        catch (Exception error) when (exit is "host exception" or "cancellation")
        {
            Assert.IsAssignableFrom(exit == "host exception" ? typeof(InvalidOperationException) : typeof(OperationCanceledException), error);
        }

        Assert.Equal(1, during);
        Assert.Equal(0, parent.ActiveDependencyCount);
        Assert.Equal(0, child.ActiveDependencyCount);
    }

    /// <summary>
    /// Independent runs never contend for one graph gate. While a test holds one run's gate, another
    /// run's demands record and remove their edges unimpeded. A demand of the held run waits for its
    /// own gate, so the edge it records is that run's. The negative check cannot pass falsely: a
    /// demand that completes while the gate is held fails it.
    /// </summary>
    [Fact]
    public async Task HoldingOneRunsGraphGate_NeverDelaysAnotherRun()
    {
        var held = EvaluationBudget.Create(null);
        var other = EvaluationBudget.Create(null);
        Assert.True(held.NeedDependencyGate != other.NeedDependencyGate);
        static Task<EvalResult<Evaluator.CountedResult>> Chain(EvaluationBudget budget)
        {
            var child = new NeedCell(() => Value(4), () => new(Value(4)), budget: budget);
            var parent = new NeedCell(() => child.Demand(), () => child.DemandAsync(), budget: budget);
            return Task.Run(() => parent.Demand());
        }

        // A dedicated thread holds the run's gate (a Lock is thread-affine, so it cannot be held
        // across this method's awaits).
        var acquired = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        using var release = new ManualResetEventSlim();
        var holder = new Thread(() =>
        {
            lock (held.NeedDependencyGate)
            {
                acquired.SetResult();
                release.Wait();
            }
        });
        holder.Start();
        try
        {
            await acquired.Task.WaitAsync(WaitLimit);
            Assert.True((await Chain(other).WaitAsync(WaitLimit)).IsOk);

            var entering = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
            var waiting = new TaskCompletionSource<EvalResult<Evaluator.CountedResult>>(TaskCreationOptions.RunContinuationsAsynchronously);
            var child = new NeedCell(() => Value(4), () => new(Value(4)), budget: held);
            var parent = new NeedCell(() => { entering.SetResult(); return child.Demand(); }, () => child.DemandAsync(), budget: held);
            var worker = new Thread(() =>
            {
                try { waiting.SetResult(parent.Demand()); }
                catch (Exception error) { waiting.SetException(error); }
            });
            worker.Start();
            await entering.Task.WaitAsync(WaitLimit);
            // After entering the synchronous parent there is no wait except the child's graph
            // gate. Observe that wait (or an incorrect completion), instead of assuming a worker
            // has reached the lock after a fixed delay.
            Assert.True(await Task.Run(() => SpinWait.SpinUntil(
                () => waiting.Task.IsCompleted || (worker.ThreadState & ThreadState.WaitSleepJoin) != 0, WaitLimit)));
            Assert.False(waiting.Task.IsCompleted);

            release.Set();
            Assert.True((await waiting.Task.WaitAsync(WaitLimit)).IsOk);
            worker.Join();
        }
        finally
        {
            release.Set();
            holder.Join();
        }
    }

    /// <summary>
    /// A cell of another run never takes an edge from this run's parent. The control case is a cell
    /// of the parent's own run, which does take one.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task AParentOfAnotherRun_RecordsNoEdge(bool asynchronous)
    {
        var outer = EvaluationBudget.Create(null);
        foreach (var (childBudget, expectedEdges) in new[] { (EvaluationBudget.Create(null), 0), (outer, 1) })
        {
            NeedCell? parent = null;
            var during = -1;
            var child = new NeedCell(
                () => { during = parent!.ActiveDependencyCount; return Value(3); },
                async () => { await Task.Yield(); during = parent!.ActiveDependencyCount; return Value(3); },
                budget: childBudget);
            parent = new NeedCell(() => child.Demand(), async () => await child.DemandAsync(), budget: outer);
            var outcome = asynchronous ? await parent.DemandAsync().AsTask().WaitAsync(WaitLimit) : parent.Demand();
            Assert.True(outcome.IsOk);
            Assert.Equal(expectedEdges, during);
            Assert.Equal(0, parent.ActiveDependencyCount);
        }

        // A cell with no budget (only a test builds one) and a run's cell are different graphs too.
        NeedCell? unowned = null;
        var unownedDuring = -1;
        var owned = new NeedCell(() => { unownedDuring = unowned!.ActiveDependencyCount; return Value(); },
            () => new(Value()), budget: outer);
        unowned = new NeedCell(() => owned.Demand(), () => owned.DemandAsync());
        Assert.True(unowned.Demand().IsOk);
        Assert.Equal(0, unownedDuring);
    }

    [Fact]
    public async Task CancellationDuringASuspendedDemand_LeavesNoEdge()
    {
        var budget = EvaluationBudget.Create(null);
        using var stop = new CancellationTokenSource();
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var child = new NeedCell(() => throw new InvalidOperationException(), async () =>
        {
            entered.SetResult();
            await Task.Delay(Timeout.Infinite, stop.Token);
            return Value();
        }, budget: budget);
        var parent = new NeedCell(() => throw new InvalidOperationException(), async () => await child.DemandAsync(), budget: budget);

        var demand = parent.DemandAsync().AsTask();
        await entered.Task.WaitAsync(WaitLimit);
        Assert.Equal(1, parent.ActiveDependencyCount);
        stop.Cancel();
        await Assert.ThrowsAnyAsync<OperationCanceledException>(() => demand.WaitAsync(WaitLimit));
        Assert.Equal(0, parent.ActiveDependencyCount);
        Assert.Equal(0, child.ActiveDependencyCount);
        await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await child.DemandAsync());
    }

    [Fact]
    public void FailedChildDemands_LeaveNoEdgeBehindALaterSuccess()
    {
        var budget = EvaluationBudget.Create(null);
        var failing = new NeedCell(() => new EvalError.DivByZero(), () => new(new EvalError.DivByZero()), budget: budget);
        var throwing = new NeedCell(() => throw new InvalidOperationException("host failure"),
            () => throw new InvalidOperationException("host failure"), budget: budget);
        var succeeding = new NeedCell(() => Value(5), () => new(Value(5)), budget: budget);
        NeedCell? parent = null;
        var afterFailures = -1;
        parent = new NeedCell(() =>
        {
            if (!failing.Demand().IsError) throw new InvalidOperationException("expected the ordinary failure");
            try { throwing.Demand(); }
            catch (InvalidOperationException) { }
            afterFailures = parent!.ActiveDependencyCount;
            return succeeding.Demand();
        }, () => throw new InvalidOperationException(), budget: budget);

        Assert.True(parent.Demand().IsOk);
        Assert.Equal(0, afterFailures);
        Assert.Equal(0, parent.ActiveDependencyCount);
        Assert.Equal(KatLangErrorCode.DivisionByZero, failing.Demand().Error.Code);
    }

    // Each program and its twin that calls a genuinely suspending host operation in a demanded
    // position (the arity error is refused before any demand, so its twin never suspends).
    private static readonly (string Synchronous, string Suspending)[] Programs =
    [
        ("Fib(n) = if(n < 2, n, Fib(n - 1) + Fib(n - 2))\nFib(12)",
            "Fib(n) = if(id(n) < 2, n, Fib(n - 1) + Fib(n - 2))\nFib(12)"),
        ("S(*xs) = sum(xs)\nStep(i, acc) = i + 1, acc + S(i, i, i) + S()\nrepeat(Step, 150, 0, 0)",
            "S(*xs) = sum(xs)\nStep(i, acc) = i + 1, acc + S(id(i), i, i) + S()\nrepeat(Step, 150, 0, 0)"),
        ("P((a, b), [c, *d]) = a + b + c + count(d)\nP((1, 2), [3, 4, 5]) + P((6, 7), [8])",
            "P((a, b), [c, *d]) = a + b + c + count(d)\nP((id(1), 2), [3, 4, 5]) + P((6, 7), [id(8)])"),
        ("Fact(0) = 1\nFact(n) = n * Fact(n - 1)\nmap([3, 4, 5], Fact)",
            "Fact(0) = 1\nFact(n) = n * Fact(id(n) - 1)\nmap([3, 4, 5], Fact)"),
        ("Same(x, x) = x\nAdd(a, b) = a + b\nreduce([1, 2, 3, 4], Add, Same(5, 5))",
            "Same(x, x) = x\nAdd(a, b) = id(a) + b\nreduce([1, 2, 3, 4], Add, Same(5, id(5)))"),
        ("x, *y, z = 1, 2, 3, 4\nx + count(y) + z",
            "x, *y, z = id(1), 2, 3, id(4)\nx + count(y) + z"),
        ("F(a, b) = a + b\nF(1, 2, 3)",
            "F(a, b) = a + b\nF(id(1), 2, 3)"),
        ("G(x) = x + x + x\nH(y) = G(y) + G(y + 1)\nH(H(1))",
            "G(x) = x + x + x\nH(y) = G(id(y)) + G(y + 1)\nH(H(1))"),
    ];

    /// <summary>
    /// Independent runs on many threads at once each agree with the result the same run gives alone.
    /// That holds on the sync engine, and on the async engine where every program but the refused
    /// call suspends in a genuinely suspending host operation whose continuations hop threads.
    /// </summary>
    [Fact]
    public async Task IndependentRunsInParallel_AgreeWithTheirSequentialResults()
    {
        var expected = Programs.Select(program => Render(KatLangEngine.Run(program.Synchronous))).ToArray();
        using var workerCancellation = new CancellationTokenSource();
        var synchronousOptions = new RunOptions
        {
            SourceProcessingCancellationToken = workerCancellation.Token,
            EvaluationCancellationToken = workerCancellation.Token,
        };
        var suspending = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.CreateAsync("id", async (args, _) => { await Task.Yield(); return args[0]; }, "x")),
            SourceProcessingCancellationToken = workerCancellation.Token,
            EvaluationCancellationToken = workerCancellation.Token,
        };
        var asyncExpected = new string[Programs.Length];
        for (var index = 0; index < Programs.Length; index++)
            asyncExpected[index] = Render(await KatLangEngine.RunAsync(Programs[index].Suspending, suspending));

        const int threads = 16;
        const int iterations = 12;
        using var start = new Barrier(threads);
        var failures = new ConcurrentQueue<string>();
        var workers = Enumerable.Range(0, threads).Select(worker => Task.Factory.StartNew(() =>
        {
            try
            {
                start.SignalAndWait(workerCancellation.Token);
                for (var iteration = 0; iteration < iterations; iteration++)
                {
                    workerCancellation.Token.ThrowIfCancellationRequested();
                    var index = (worker + iteration) % Programs.Length;
                    var synchronous = worker % 2 == 0;
                    var actual = synchronous
                        ? Render(KatLangEngine.Run(Programs[index].Synchronous, synchronousOptions))
                        : Render(KatLangEngine.RunAsync(Programs[index].Suspending, suspending).GetAwaiter().GetResult());
                    var wanted = synchronous ? expected[index] : asyncExpected[index];
                    if (actual != wanted) failures.Enqueue($"{Programs[index]}: expected {wanted}, got {actual}");
                }
            }
            catch (OperationCanceledException) when (workerCancellation.IsCancellationRequested) { }
        }, CancellationToken.None, TaskCreationOptions.LongRunning, TaskScheduler.Default)).ToArray();

        var completedWorkers = Task.WhenAll(workers);
        try { await completedWorkers.WaitAsync(ParallelRunBudget); }
        catch (TimeoutException)
        {
            // A failed guard must not leave independent runs executing behind later tests.
            workerCancellation.Cancel();
            await completedWorkers.WaitAsync(WaitLimit);
            throw;
        }
        Assert.Empty(failures);
    }

    /// <summary>
    /// A host operation may start a nested run inside a cell's evaluation (HostOperations allows
    /// reentrant runs). The nested run's cells see the outer cell as their AsyncLocal parent. That
    /// parent belongs to another run, so it records no edge (pinned directly by
    /// <see cref="AParentOfAnotherRun_RecordsNoEdge"/>). Here both runs keep their values, on the same
    /// thread and on another thread that inherits the execution context, repeatedly and in parallel.
    /// </summary>
    [Fact]
    public async Task NestedRunsInsideAHostOperation_AreIndependentOfTheOuterGraph()
    {
        const string inner = "Fib(n) = if(n < 2, n, Fib(n - 1) + Fib(n - 2))\nFib(10)";
        static Result Nested(Result offset) => KatLangEngine.Run(inner) is RunResult.Success success
            ? new Result.Atom(((Result.Atom)success.Value).Value + ((Result.Atom)offset).Value)
            : throw new InvalidOperationException("the nested run failed");
        // A dedicated thread inherits the execution context (and with it the outer current cell)
        // without competing for the thread pool.
        static Result Elsewhere(Result offset)
        {
            Result? value = null;
            Exception? failure = null;
            var thread = new Thread(() =>
            {
                try { value = Nested(offset); }
                catch (Exception error) { failure = error; }
            });
            thread.Start();
            thread.Join();
            return failure is null ? value! : throw new InvalidOperationException("the nested run failed", failure);
        }
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("inner", (args, _) => Nested(args[0]), "x"),
                HostOperation.Create("innerElsewhere", (args, _) => Elsewhere(args[0]), "x")),
        };
        // inner(0) = 55; G(55) = F(55, inner(55)) + F(innerElsewhere(55), 55) = 165 + 165.
        const string outer = "F(x, y) = x + y\nG(x) = F(x, inner(x)) + F(innerElsewhere(x), x)\nG(inner(0))";

        for (var repetition = 0; repetition < 10; repetition++)
            Assert.Equal("330", Render(KatLangEngine.Run(outer, options)));

        var parallel = Enumerable.Range(0, 8).Select(_ => Task.Run(() => Render(KatLangEngine.Run(outer, options)))).ToArray();
        Assert.All(await Task.WhenAll(parallel).WaitAsync(WaitLimit), value => Assert.Equal("330", value));
        Assert.Equal("330", Render(await KatLangEngine.RunAsync(outer, options)));
    }

    private static string Render(RunResult result) => result switch
    {
        RunResult.Success => OutputFormatters.Exact.Format(result),
        RunResult.EvalFailure failure => string.Join(" | ", failure.Errors.Select(error => $"{error.Code} {error.Span} {error.Message}")),
        _ => result.GetType().Name,
    };
}
