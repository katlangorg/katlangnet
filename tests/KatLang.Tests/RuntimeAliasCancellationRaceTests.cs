using System.Reflection;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// ALIAS-CANCEL-1: cancellation racing a runtime alias's CALLABLE projection, end to end. The generic
/// flight (<see cref="NeedCellProjectionFlightTests"/>) and resolution (<see cref="NeedCellAsyncResolutionTests"/>)
/// suites prove the protocol over delegate cells; the corpus' cancellation rows
/// (<see cref="RuntimeCallableAliasCorpusTests"/>) cancel inside the host operation itself. What only these
/// cases pin is the same protocol ON THE ALIAS'S OWN ROUTE: the real binding cell, its one receiver and the
/// chase's replay, under a suspension held open at a known boundary while cancellation arrives from outside.
/// <para>Every schedule is established by observed state: a host gate signals entry, an observer's wait-for
/// edge is seen before anything is released, and the bounded waits are hang guards, never latency claims.</para>
/// </summary>
public sealed class RuntimeAliasCancellationRaceTests
{
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);

    private const string Lib = """
        Capture(meta op) = op
        F(x) = x + 1
        Hold(g) = Capture(g(0))
        T(x) = trace(7)

        """;

    private const string Receiver = "R = if(gate(), Capture(F(0)), 0)\n";

    private sealed class Gate
    {
        private readonly TaskCompletionSource _entered = new(TaskCreationOptions.RunContinuationsAsynchronously);
        private readonly TaskCompletionSource _release = new(TaskCreationOptions.RunContinuationsAsynchronously);
        private int _calls;

        public int Calls => Volatile.Read(ref _calls);
        public Task Entered => _entered.Task;
        public void Release() => _release.TrySetResult();

        // What the suspended operation does once released; by default it returns true, deliberately
        // ignoring the token, so the evaluator's own boundary is what observes the cancellation.
        public Action<CancellationToken>? Finish { get; set; }

        public async ValueTask<Result> Run(CancellationToken token)
        {
            Interlocked.Increment(ref _calls);
            _entered.TrySetResult();
            await _release.Task.WaitAsync(WaitLimit);
            Finish?.Invoke(token);
            return new Result.Bool(true);
        }
    }

    private sealed class Host : IAsyncDisposable
    {
        private readonly List<string> _traces = [];
        private readonly List<Task> _tasks = [];
        private IDisposable? _preparation;
        private int _tocks;

        public Gate Receiver { get; } = new();
        public Gate After { get; } = new();
        public int Tocks => Volatile.Read(ref _tocks);
        public string Traces { get { lock (_traces) return string.Join(",", _traces); } }

        public HostOperations Operations => HostOperations.Create(
            HostOperation.CreateAsync("gate", (_, token) => Receiver.Run(token)),
            HostOperation.CreateAsync("after", (_, token) => After.Run(token)),
            HostOperation.Create("tock", (_, _) => new Result.Atom(Interlocked.Increment(ref _tocks))),
            HostOperation.Create("trace", (args, _) =>
            {
                lock (_traces) _traces.Add(SixRouteAgreement.Neutral(args[0]));
                return args[0];
            }, "x"));

        public void ReleaseAll()
        {
            Receiver.Release();
            After.Release();
        }

        public Task<T> Track<T>(Task<T> task)
        {
            _tasks.Add(task);
            return task;
        }

        public void RetainPreparation(IDisposable preparation) => _preparation = preparation;

        public async ValueTask DisposeAsync()
        {
            // Assertion failures must release and observe every launched operation too. Keep the
            // reflected run alive until its observers finish, then use its ordinary EndRun owner.
            ReleaseAll();
            try { await Drain(_tasks.ToArray()); }
            finally { _preparation?.Dispose(); }
        }
    }

    private static Expr.AlgorithmExpr Program(string source, Host host)
    {
        var parsed = Parser.Parse(Lib + source, new RunOptions { HostOperations = host.Operations });
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(static d => d.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    private static Task<(EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget)> RunPublic(
        Expr program, Host host, CancellationToken token)
        => host.Track(Task.Run(async () => await Evaluator.RunCountedObservedAsync(program, hostOperations: host.Operations, cancellationToken: token)));

    private static string Show(EvalResult<Evaluator.CountedResult> result)
        => result.IsOk ? "ok " + SixRouteAgreement.Neutral(result.Value.Value) : "err " + result.Error.Code;

    // ── Public runs: every alias route, cancellation from outside the suspended receiver ──────────

    /// <summary>The routes a projected identity can take into an invocation: the matched direct control first.</summary>
    public static TheoryData<string, string, string> Routes() => new()
    {
        { "direct", Receiver + "R.Algorithm(5), trace(99)", "ok S[6, 99]" },
        { "alias", Receiver + "A = R.Algorithm\nA(5), trace(99)", "ok S[6, 99]" },
        { "chain", Receiver + "B = A\nA = R.Algorithm\nB(5), trace(99)", "ok S[6, 99]" },
        { "parameter", Receiver + "Use(p) = {\n  A = p\n  A(5)\n}\nUse(R.Algorithm), trace(99)", "ok S[6, 99]" },
        { "parameter-chain", Receiver + "Use(p) = {\n  B = A\n  A = p\n  B(5)\n}\nUse(R.Algorithm), trace(99)", "ok S[6, 99]" },
        { "zero-parameter", "Z = tock()\nR = if(gate(), Capture(Z()), 0)\nA = R.Algorithm\nA(), trace(99)", "ok S[1, 99]" },
        { "callback", Receiver + "A = R.Algorithm\nmap([1], A), trace(99)", "ok S[L[2], 99]" },
        { "loop-step", Receiver + "A = R.Algorithm\nA(1).repeat(2), trace(99)", "ok S[3, 99]" },
    };

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task UncancelledControl_ReachesTheRoutesOrdinaryResult(string route, string source, string expected)
    {
        await using var host = new Host();
        host.ReleaseAll();
        var (result, _) = await RunPublic(Program(source, host), host, default).WaitAsync(WaitLimit);
        Assert.True(expected == Show(result), $"{route}: {Show(result)}");
        Assert.Equal(1, host.Receiver.Calls);
        Assert.Equal("99", host.Traces);
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task PreCancelledRun_StartsNoReceiverWork(string route, string source, string expected)
    {
        _ = (route, expected);
        using var stop = new CancellationTokenSource();
        stop.Cancel();
        await using var host = new Host();
        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => RunPublic(Program(source, host), host, stop.Token).WaitAsync(WaitLimit));
        Assert.Equal(stop.Token, thrown.CancellationToken);
        Assert.Equal(0, host.Receiver.Calls);
        Assert.Equal(0, host.Tocks);
        Assert.Equal("", host.Traces);
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task CancellationWhileTheReceiverSuspends_EndsTheRunWithTheRunToken_AndNoLaterWork(string route, string source, string expected)
    {
        _ = (route, expected);
        foreach (var hostObservesToken in new[] { false, true })
        {
            using var stop = new CancellationTokenSource();
            await using var host = new Host();
            if (hostObservesToken) host.Receiver.Finish = token => token.ThrowIfCancellationRequested();
            var run = RunPublic(Program(source, host), host, stop.Token);
            try
            {
                await host.Receiver.Entered.WaitAsync(WaitLimit);
                await stop.CancelAsync();
            }
            finally { host.ReleaseAll(); }
            var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.WaitAsync(WaitLimit));
            Assert.Equal(stop.Token, thrown.CancellationToken);
            Assert.Equal(1, host.Receiver.Calls);
            // Neither the fallback nor the callee ran: cancellation is not callable absence.
            Assert.Equal(0, host.Tocks);
            Assert.Equal("", host.Traces);
        }
    }

    [Theory]
    [InlineData("generic", false)]
    [InlineData("generic", true)]
    [InlineData("optimized", false)]
    [InlineData("optimized", true)]
    [InlineData("async", false)]
    [InlineData("async", true)]
    public async Task CancellationBetweenProjectionAndInvocation_StartsNoBody_OnEveryEngine(string engine, bool cancels)
    {
        // The chase has its identity, and the supply's spread cancels before the fresh call binds: an
        // identity the chase already holds authorizes no invocation. The spread runs during formation,
        // so the callee's body is the very next semantic work.
        using var stop = new CancellationTokenSource();
        var traces = new List<string>();
        void Stop() { if (cancels) stop.Cancel(); }
        var operations = HostOperations.Create(
            engine == "async"
                ? HostOperation.CreateAsync("halt", async (_, _) => { await Task.Yield(); Stop(); return new Result.Bool(true); })
                : HostOperation.Create("halt", (_, _) => { Stop(); return new Result.Bool(true); }),
            HostOperation.Create("trace", (args, _) => { lock (traces) traces.Add(SixRouteAgreement.Neutral(args[0])); return args[0]; }, "x"));
        var parsed = Parser.Parse(Lib + "R = Capture(T(0))\nA = R.Algorithm\nA(if(halt(), 5, 0)*), trace(99)", new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(static d => d.Message)));
        var program = new Expr.AlgorithmExpr(parsed.Root);

        Task<(EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget)> Run() => engine == "async"
            ? Task.Run(async () => await Evaluator.RunCountedObservedAsync(program, hostOperations: operations, cancellationToken: stop.Token))
            : Task.Run(() => Evaluator.RunCountedObserved(program, null, enableOptimizations: engine == "optimized",
                hostOperations: operations, cancellationToken: stop.Token));

        if (cancels)
        {
            var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Run().WaitAsync(WaitLimit));
            Assert.Equal(stop.Token, thrown.CancellationToken);
            Assert.Empty(traces);
        }
        else
        {
            Assert.Equal("ok S[7, 99]", Show((await Run().WaitAsync(WaitLimit)).Result));
            Assert.Equal(["7", "99"], traces);
        }
    }

    [Fact]
    public async Task IndependentRunAfterACancelledRun_SharesNoCellMemoOrOwner()
    {
        // One program and one host table across two runs: everything the cancelled run established
        // (binding cell, link, receiver, target memo, publication owner) belonged to its budget.
        await using var host = new Host();
        var program = Program("Z = tock()\nR = if(gate(), Capture(Z()), 0)\nA = R.Algorithm\nA(), A, trace(99)", host);
        using var stop = new CancellationTokenSource();
        var cancelled = RunPublic(program, host, stop.Token);
        try
        {
            await host.Receiver.Entered.WaitAsync(WaitLimit);
            await stop.CancelAsync();
        }
        finally { host.ReleaseAll(); }
        await Assert.ThrowsAnyAsync<OperationCanceledException>(() => cancelled.WaitAsync(WaitLimit));
        Assert.Equal(0, host.Tocks);

        var (result, budget) = await RunPublic(program, host, default).WaitAsync(WaitLimit);
        Assert.Equal("ok S[1, 1, 99]", Show(result));
        Assert.Equal(2, host.Receiver.Calls);
        Assert.Equal(1, host.Tocks);
        Assert.Null(budget.CheckContinuation());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task HostExceptionAndForeignCancellation_LeaveTheRunAsTheOriginalObject(bool cancellation)
    {
        // A host-thrown OperationCanceledException with its own token is not relabelled with the run's.
        using var foreign = new CancellationTokenSource();
        Exception original = cancellation ? new OperationCanceledException("host's own", foreign.Token) : new InvalidOperationException("host failed");
        await using var host = new Host();
        host.Receiver.Finish = _ => throw original;
        host.ReleaseAll();
        var thrown = await Assert.ThrowsAnyAsync<Exception>(() =>
            RunPublic(Program(Receiver + "A = R.Algorithm\nA(5), trace(99)", host), host, default).WaitAsync(WaitLimit));
        Assert.Same(original, thrown);
        Assert.Equal(1, host.Receiver.Calls);
        Assert.Equal("", host.Traces);
    }

    [Theory]
    [InlineData("R = if(gate(), 1 / 0, 0)\nA = R.Algorithm\nA(5), trace(99)", KatLangErrorCode.DivisionByZero)]
    [InlineData("R = if(gate(), 5, 0)\nA = R.Algorithm\nA(5), trace(99)", KatLangErrorCode.TypeMismatch)]
    [InlineData("R = if(gate(), Hold(R.Algorithm), 0)\nA = R.Algorithm\nA(5), trace(99)", KatLangErrorCode.DemandCycle)]
    public async Task OrdinaryFailureAndCycleControls_KeepTheirKind_WhileCancellationWins(string source, KatLangErrorCode code)
    {
        await using var host = new Host();
        host.ReleaseAll();
        var (result, _) = await RunPublic(Program(source, host), host, default).WaitAsync(WaitLimit);
        Assert.Equal(code, result.Error.Code);
        Assert.Equal("", host.Traces);

        using var stop = new CancellationTokenSource();
        await using var cancelledHost = new Host();
        var run = RunPublic(Program(source, cancelledHost), cancelledHost, stop.Token);
        try
        {
            await cancelledHost.Receiver.Entered.WaitAsync(WaitLimit);
            await stop.CancelAsync();
        }
        finally { cancelledHost.ReleaseAll(); }
        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.WaitAsync(WaitLimit));
        Assert.Equal(stop.Token, thrown.CancellationToken);
        Assert.Equal("", cancelledHost.Traces);
    }

    // ── The real binding cell under a held receiver ───────────────────────────────────────────────

    private static readonly MethodInfo EvalRootProgramCountedAsyncMethod = typeof(Evaluator).GetMethod("EvalRootProgramCountedAsync",
        BindingFlags.Static | BindingFlags.NonPublic,
        [typeof(Algorithm), typeof(SourceSpan?), typeof(Evaluator.EvalCtx)])!;

    private static readonly MethodInfo PrepareAsyncTwinRunMethod = typeof(Evaluator).GetMethod("PrepareAsyncTwinRun",
        BindingFlags.Static | BindingFlags.NonPublic)!;

    /// <summary>
    /// A source program evaluated by the async twin below the public entry point, so the test can read the
    /// run's own budget: its root alias's retained binding cell and that link's one receiver.
    /// </summary>
    private sealed class HeldRun
    {
        public required EvaluationBudget Budget { get; init; }
        public required RunScopedAsyncZeroArgPropertyResultCache Cache { get; init; }
        public required Task<EvalResult<Evaluator.CountedResult>> Completion { get; init; }

        public async Task Reaches(Gate gate)
        {
            await Task.WhenAny(gate.Entered, Completion).WaitAsync(WaitLimit);
            Assert.True(gate.Entered.IsCompleted, Completion.IsCompleted ? $"run ended early: {await Describe(Completion)}" : "gate not reached");
        }

        private static async Task<string> Describe(Task<EvalResult<Evaluator.CountedResult>> run)
        {
            try { return Show(await run); }
            catch (Exception error) { return error.ToString(); }
        }

        public NeedCell Link => Assert.Single(Budget.AliasBindingCells).Value;

        public NeedCell ReceiverCell
            => ((Evaluator.LinkSuspension)Link.Suspension!).Receiver((Expr.DotCall)Link.Source!);

        public static HeldRun Start(string source, Host host, CancellationToken token)
        {
            var program = Program(source, host);
            // The real admission of an async run: preflight facts, prelude and root context.
            var cache = new RunScopedAsyncZeroArgPropertyResultCache();
            var preparation = PrepareAsyncTwinRunMethod.Invoke(null,
                [program, cache, null, null, null, null, host.Operations, null, null, token])!;
            host.RetainPreparation((IDisposable)preparation);
            var ctx = (Evaluator.EvalCtx)preparation.GetType().GetProperty("Ctx", BindingFlags.Instance | BindingFlags.NonPublic)!.GetValue(preparation)!;
            var completion = host.Track(Task.Run(async () => await (ValueTask<EvalResult<Evaluator.CountedResult>>)EvalRootProgramCountedAsyncMethod.Invoke(null,
                [program.Algorithm, program.Span, ctx])!));
            return new HeldRun { Budget = ctx.Budget, Cache = cache, Completion = completion };
        }
    }

    private static async Task Until(Func<bool> condition)
    {
        var deadline = DateTime.UtcNow + WaitLimit;
        while (!condition())
        {
            if (DateTime.UtcNow > deadline) throw new TimeoutException("controlled-overlap handshake");
            await Task.Delay(1);
        }
    }

    // An independent observer of the run: the VALUE computation of another cell, so its wait-for edge
    // onto the alias's binding cell is observable before anything is released.
    private static (NeedCell Parent, Task<EvalResult<Evaluator.CountedResult>> Demand) Observer(EvaluationBudget budget, NeedCell link)
    {
        var parent = new NeedCell(() => throw new InvalidOperationException("async observer"), async () =>
        {
            var projected = await link.ProjectCallableAsync();
            return EvalResult<Evaluator.CountedResult>.Ok(new(new Result.Bool(projected.IsOk), 1));
        }, budget: budget);
        return (parent, Task.Run(async () => await parent.DemandAsync()));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task JoinedObserver_SharesTheCancelledFlight_WithOneReceiverAttemptAndNoResidue(bool hostObservesToken)
    {
        using var stop = new CancellationTokenSource();
        await using var host = new Host();
        if (hostObservesToken) host.Receiver.Finish = token => token.ThrowIfCancellationRequested();
        var run = HeldRun.Start(Receiver + "A = R.Algorithm\nA(5), trace(99)", host, stop.Token);
        Task<EvalResult<Evaluator.CountedResult>>? demand = null;
        NeedCell link, parent;
        try
        {
            await run.Reaches(host.Receiver);
            link = run.Link;
            Assert.True(link.HasProjectionInFlight);
            Assert.True(run.ReceiverCell.HasValueInFlight);
            Assert.Equal(1, run.Cache.ActiveOwnerCount);   // R's property read owns its publication
            (parent, demand) = Observer(run.Budget, link);
            _ = host.Track(demand);
            await Until(() => parent.ActiveDependencyCount == 1 || demand.IsCompleted);
            Assert.False(demand.IsCompleted);
            await stop.CancelAsync();
        }
        finally { host.ReleaseAll(); }

        var starter = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.Completion.WaitAsync(WaitLimit));
        var joined = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => demand!.WaitAsync(WaitLimit));
        Assert.Equal(stop.Token, starter.CancellationToken);
        Assert.Same(starter, joined);
        Assert.Equal(1, host.Receiver.Calls);
        Assert.Equal(1, link.ProjectionComputations);
        Assert.False(link.HasCallableMemo);
        Assert.False(link.HasProjectionInFlight);
        Assert.False(run.ReceiverCell.HasValueInFlight);
        Assert.True(run.ReceiverCell.HasCompletedValue);
        Assert.Equal(0, link.ProjectionActiveDependencyCount);
        Assert.Equal(0, run.ReceiverCell.ActiveDependencyCount);
        Assert.Equal(0, parent.ActiveDependencyCount);
        Assert.Equal(0, run.Cache.ActiveOwnerCount);
        Assert.Equal(0, run.Cache.PublishedCount);
        Assert.False(NeedNode.HasCurrentNode);
        Assert.False(NeedCell.IsObserving);

        // Later observations meet the run's cancellation at entry: never a restart.
        var later = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => link.ProjectCallableAsync().AsTask());
        Assert.Equal(stop.Token, later.CancellationToken);
        Assert.Equal(1, link.ProjectionComputations);
        Assert.Equal(1, host.Receiver.Calls);
        Assert.Equal("", host.Traces);
    }

    [Fact]
    public async Task CompletedProjection_KeepsItsOutcome_WhileLaterObservationAndInvocationAreRejected()
    {
        // The opposite ordering: the projection completes, an observer reuses it, and only then does
        // cancellation arrive, while the fresh call waits on its own argument.
        using var stop = new CancellationTokenSource();
        await using var host = new Host();
        var run = HeldRun.Start(Receiver + "A = R.Algorithm\nA(if(after(), 5, 0)), trace(99)", host, stop.Token);
        NeedCell link;
        try
        {
            host.Receiver.Release();
            await run.Reaches(host.After);
            link = run.Link;
            Assert.True(link.HasCallableMemo);
            Assert.NotNull((await link.ProjectCallableAsync()).Value);
            await stop.CancelAsync();
        }
        finally { host.ReleaseAll(); }

        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.Completion.WaitAsync(WaitLimit));
        Assert.Equal(stop.Token, thrown.CancellationToken);
        Assert.True(link.HasCallableMemo);   // not rewritten by the later cancellation
        var later = Assert.ThrowsAny<OperationCanceledException>(() => link.ProjectCallable());
        Assert.Equal(stop.Token, later.CancellationToken);
        Assert.Equal(1, link.ProjectionComputations);
        Assert.Equal(1, host.Receiver.Calls);
        Assert.Equal(0, link.ProjectionActiveDependencyCount);
        Assert.Equal("", host.Traces);
    }

    [Fact]
    public async Task ValueAndCallableOverOneReceiver_ShareItsCancellation_WithoutForcingTheCallee()
    {
        // The bare read starts the link's VALUE, whose receiver suspends; the CALLABLE then waits on that
        // same receiver. Cancelling it reaches both channels, one attempt, and the callee never runs.
        using var stop = new CancellationTokenSource();
        await using var host = new Host();
        var run = HeldRun.Start("Z = tock()\nR = if(gate(), Capture(Z()), 0)\nA = R.Algorithm\nA, A(), trace(99)", host, stop.Token);
        Task<EvalResult<Evaluator.CountedResult>>? demand = null;
        NeedCell link, parent;
        try
        {
            await run.Reaches(host.Receiver);
            link = run.Link;
            Assert.True(link.HasValueInFlight);
            Assert.False(link.HasProjectionInFlight);
            (parent, demand) = Observer(run.Budget, link);
            _ = host.Track(demand);
            await Until(() => link.ProjectionActiveDependencyCount == 1 || demand.IsCompleted);
            Assert.False(demand.IsCompleted);
            Assert.True(link.HasProjectionInFlight);
            await stop.CancelAsync();
        }
        finally { host.ReleaseAll(); }

        var starter = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.Completion.WaitAsync(WaitLimit));
        var joined = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => demand!.WaitAsync(WaitLimit));
        Assert.Same(starter, joined);
        Assert.Equal(stop.Token, starter.CancellationToken);
        Assert.Equal(1, host.Receiver.Calls);
        Assert.Equal(0, host.Tocks);
        Assert.Equal(1, link.ProjectionComputations);
        Assert.False(link.HasCallableMemo);
        Assert.True(link.HasCompletedValue);
        Assert.False(link.HasValueInFlight);
        Assert.False(link.HasProjectionInFlight);
        Assert.Equal(0, link.ActiveDependencyCount);
        Assert.Equal(0, link.ProjectionActiveDependencyCount);
        Assert.Equal(0, run.ReceiverCell.ActiveDependencyCount);
        Assert.Equal(0, parent.ActiveDependencyCount);
    }

    // ── The chase's replay over a held projection (the cancellation twins of the mechanism suite) ──

    private static readonly Algorithm.User Target =
        new(null, [new CaptureParameterPattern("x")], [], [], [new Expr.Param("x")]);

    private static (Algorithm.Alias Alias, Evaluator.EvalCtx Ctx) ParameterAlias(NeedCell cell, EvaluationBudget budget)
    {
        var ctx = (Evaluator.EvalCtx.Empty with { Budget = budget }).WithNeedEnv([("f", cell)]);
        var scope = new ScopeCtx(null, [], [], ["f"]) { Activation = ParameterActivation.Capture(["f"], ctx, []) };
        return (new Algorithm.Alias(null, [], [], new Expr.Param("f")) with { Parent = scope }, ctx);
    }

    public enum HeldOutcome { Identity, RunCancellation, ForeignCancellation }

    [Theory]
    [InlineData(HeldOutcome.Identity)]
    [InlineData(HeldOutcome.RunCancellation)]
    [InlineData(HeldOutcome.ForeignCancellation)]
    public async Task ConcurrentChases_OverACancelledFlight_ShareOneComputation_AndNeverReturnIdentity(HeldOutcome outcome)
    {
        using var stop = new CancellationTokenSource();
        using var foreign = new CancellationTokenSource();
        var budget = EvaluationBudget.Create(null, cancellationToken: stop.Token);
        budget.MarkAsynchronousRun();
        budget.DecideRuntimeAliasReach(true, false);
        var started = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var original = new OperationCanceledException("host's own", foreign.Token);
        var computations = 0;
        var cell = NeedCell.WithRuntimeProjection(
            () => throw new InvalidOperationException("CALLABLE must not demand VALUE"),
            () => throw new InvalidOperationException("CALLABLE must not demand VALUE"),
            () => throw new InvalidOperationException("Async resolution must await the projection"),
            async () =>
            {
                Interlocked.Increment(ref computations);
                started.TrySetResult();
                await release.Task;
                if (outcome == HeldOutcome.RunCancellation) stop.Token.ThrowIfCancellationRequested();
                if (outcome == HeldOutcome.ForeignCancellation) throw original;
                return EvalResult<Algorithm?>.Ok(Target);
            }, null, budget, stop.Token);
        var (alias, ctx) = ParameterAlias(cell, budget);

        var chases = Enumerable.Range(0, 16).Select(_ => Evaluator.ResolveAliasTargetAsync(alias, ctx).AsTask()).ToArray();
        // A direct observation admitted to the same flight: only IT may receive the completion.
        var (parent, demand) = Observer(budget, cell);
        try
        {
            await started.Task.WaitAsync(WaitLimit);
            await Until(() => parent.ActiveDependencyCount == 1 || demand.IsCompleted);
            Assert.False(demand.IsCompleted);
            Assert.All(chases, chase => Assert.False(chase.IsCompleted));
            if (outcome != HeldOutcome.ForeignCancellation) await stop.CancelAsync();
        }
        finally
        {
            release.TrySetResult();
            await Drain(chases.Cast<Task>().Append(demand).ToArray());
        }

        Assert.All(await Task.WhenAll(chases.Select(Outcome)).WaitAsync(WaitLimit), failure =>
        {
            if (outcome == HeldOutcome.ForeignCancellation) Assert.Same(original, failure);
            else Assert.Equal(stop.Token, Assert.IsAssignableFrom<OperationCanceledException>(failure).CancellationToken);
        });
        var admitted = await Outcome(demand);
        switch (outcome)
        {
            case HeldOutcome.Identity:
                // Admitted before the independent cancellation: its flight's authoritative completion...
                Assert.Null(admitted);
                Assert.True(cell.HasCallableMemo);
                break;
            case HeldOutcome.RunCancellation:
                Assert.Equal(stop.Token, Assert.IsAssignableFrom<OperationCanceledException>(admitted).CancellationToken);
                Assert.False(cell.HasCallableMemo);
                break;
            case HeldOutcome.ForeignCancellation:
                Assert.Same(original, admitted);
                Assert.False(cell.HasCallableMemo);
                break;
        }

        Assert.Equal(1, computations);
        Assert.Equal(1, cell.ProjectionComputations);
        Assert.False(cell.HasProjectionInFlight);
        Assert.False(cell.HasCompletedValue);
        Assert.Equal(0, cell.ProjectionActiveDependencyCount);
        Assert.Equal(0, parent.ActiveDependencyCount);
        Assert.False(NeedCell.IsObserving);
        Assert.False(NeedNode.HasCurrentNode);

        // ...while a later chase never replays it, and nothing restarts.
        var replay = await Outcome(Evaluator.ResolveAliasTargetAsync(alias, ctx).AsTask());
        if (outcome == HeldOutcome.ForeignCancellation) Assert.Same(original, replay);
        else Assert.Equal(stop.Token, Assert.IsAssignableFrom<OperationCanceledException>(replay).CancellationToken);
        Assert.Equal(1, computations);
    }

    private static async Task<Exception?> Outcome(Task task)
    {
        try { await task.WaitAsync(WaitLimit); return null; }
        catch (Exception error) { return error; }
    }

    private static async Task Drain(params Task[] tasks)
    {
        var completion = Task.WhenAll(tasks);
        try { await completion.WaitAsync(WaitLimit); }
        // Expected cancellation/host exceptions are asserted by each test. Awaiting WhenAll
        // observes every task even when an earlier assertion aborts the test body.
        catch when (completion.IsCompleted) { }
    }

    [Fact]
    public async Task AbortedSchedule_ReleasesAndJoinsItsWork_AndEndsTheReflectedRun()
    {
        var host = new Host();
        HeldRun? run = null;
        NeedCell? parent = null;
        Task<EvalResult<Evaluator.CountedResult>>? demand = null;
        var abort = new InvalidOperationException("abort before releasing the receiver");
        var thrown = await Assert.ThrowsAsync<InvalidOperationException>(async () =>
        {
            await using (host)
            {
                run = HeldRun.Start(Receiver + "A = R.Algorithm\nA(5), trace(99)", host, default);
                await run.Reaches(host.Receiver);
                (parent, demand) = Observer(run.Budget, run.Link);
                _ = host.Track(demand);
                await Until(() => parent.ActiveDependencyCount == 1 || demand.IsCompleted);
                Assert.False(demand.IsCompleted);
                throw abort;
            }
        });

        Assert.Same(abort, thrown);
        Assert.True(run!.Completion.IsCompletedSuccessfully);
        Assert.True(demand!.IsCompletedSuccessfully);
        Assert.True(run.Budget.RunEnded);
        Assert.False(run.Link.HasProjectionInFlight);
        Assert.Equal(0, parent!.ActiveDependencyCount);
        Assert.Equal(0, run.Cache.ActiveOwnerCount);
        Assert.Equal(1, host.Receiver.Calls);
    }

    [Fact]
    public async Task CancellationAdjacentToAnAliasCycle_LeavesEveryFrameRestored()
    {
        // The projection re-enters itself through the alias (the flow-local DemandCycle), then the run is
        // cancelled before the computation returns: the cycle is the computation's outcome, the chase's
        // replay meets cancellation first, and no edge, node or observation frame remains.
        using var stop = new CancellationTokenSource();
        var budget = EvaluationBudget.Create(null, cancellationToken: stop.Token);
        budget.MarkAsynchronousRun();
        budget.DecideRuntimeAliasReach(true, false);
        Algorithm.Alias? alias = null;
        var ctx = Evaluator.EvalCtx.Empty;
        EvalResult<Algorithm>? reentered = null;
        var cell = NeedCell.WithRuntimeProjection(
            () => throw new InvalidOperationException("CALLABLE must not demand VALUE"),
            () => throw new InvalidOperationException("CALLABLE must not demand VALUE"),
            () => throw new InvalidOperationException("Async resolution must await the projection"),
            async () =>
            {
                await Task.Yield();
                var inner = await Evaluator.ResolveAliasTargetAsync(alias!, ctx);
                reentered = inner;
                await stop.CancelAsync();
                return inner.IsError ? inner.Error : EvalResult<Algorithm?>.Ok(inner.Value);
            }, new SourceSpan(2, 3, 2, 9), budget, stop.Token);
        (alias, ctx) = ParameterAlias(cell, budget);

        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Evaluator.ResolveAliasTargetAsync(alias, ctx).AsTask().WaitAsync(WaitLimit));
        Assert.Equal(stop.Token, thrown.CancellationToken);
        Assert.Equal(KatLangErrorCode.DemandCycle, reentered!.Value.Error.Code);
        Assert.Equal(1, cell.ProjectionComputations);
        Assert.True(cell.HasCallableMemo);
        Assert.False(cell.HasProjectionInFlight);
        Assert.Equal(0, cell.ProjectionActiveDependencyCount);
        Assert.False(NeedNode.HasCurrentNode);
        Assert.False(NeedCell.IsObserving);
    }
}
