using System.Numerics;
using System.Runtime.ExceptionServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// A run its HOST ends — a host operation's exception, a faulted host awaitable, host
/// cancellation — on the asynchronous twin route (November 2026, adversarial performance audit
/// finding 2).
///
/// <para><b>The contract, unchanged.</b> The run ends with an EXCEPTION at the public entry
/// point: the host's own exception object with the stack trace it was thrown with, or
/// <see cref="OperationCanceledException"/> carrying the cancelled token. The first such
/// exception is the run's outcome, nothing is evaluated after it, and no consumer — clause
/// dispatch, a callable alternative, a repeated-name group, a callback, a loop — absorbs it.</para>
///
/// <para><b>The transport, changed.</b> Thrown through the twins, the exception crossed about
/// twenty <c>async</c> frames per KatLang call level and each of them froze and restored its
/// growing stack trace: one host failure at depth 120 raised the exception 2,317 times and
/// allocated 727 MB, and at depth 1,000 through loop steps 20,037 times and 41.9 GB. The run now
/// retains the exception once and carries its marker upward by value
/// (<see cref="EvaluationBudget.CarriesHostTermination"/>); the entry point rethrows it. These
/// tests gate that with DETERMINISTIC work and allocation measures, never wall time:
/// <see cref="OutcomeThrows"/> counts how often the runtime raises the run's own exception, and
/// the allocation tests compare a host-ended run with the successful control of the same
/// program on one thread.</para>
///
/// <para>Every program is run through <see cref="KatLangEngine"/>, so an illegal source is a
/// returned <see cref="RunResult.ParseFailure"/>, never the asserted exception. The synchronous
/// route is the oracle for outcomes and effect counts. C# host execution only: Lean models
/// neither host operations nor cancellation.</para>
/// </summary>
public class AsyncHostTerminationTests
{
    /// <summary>A hang guard, never a latency claim.</summary>
    private static readonly TimeSpan HangGuard = TimeSpan.FromSeconds(180);

    /// <summary>
    /// How often one host-ended run may raise its own exception, at ANY depth: the host's throw,
    /// the entry point's one rethrow, and one rethrow per awaiting frame above it (the engine's
    /// entry and the test's awaits). Measured: 3 to 5. Thrown through the twins it was about 19 per
    /// call level.
    /// </summary>
    private const int MaxOutcomeThrows = 10;

    /// <summary>
    /// The recursion depth of the tests that also run the synchronous route as their oracle: it
    /// must fit the oracle's thread in a Debug build under every shape (the callback shape is the
    /// most stack-expensive one). The twin route's own depth tests go far deeper.
    /// </summary>
    private const int OracleDepth = 12;

    private sealed class HostFailure(string message) : Exception(message);

    private static Result Atom(Decimal128 value) => new Result.Atom(value);

    private static async Task<T> Complete<T>(Task<T> task)
    {
        var completed = await Task.WhenAny(task, Task.Delay(HangGuard));
        Assert.True(ReferenceEquals(task, completed), "hang guard: the run did not complete");
        return await task;
    }

    /// <summary>
    /// One run's host: its token, its failure object and its operations. Every operation exists on
    /// both routes under the same name, so one source runs on the synchronous route (the oracle)
    /// and on the twin route; the names starting with <c>a</c> are asynchronous on the twin route.
    /// </summary>
    private sealed class Host : IDisposable
    {
        public CancellationTokenSource Cancellation { get; } = new();
        public HostFailure Failure { get; } = new("host operation failed");
        public OperationCanceledException? HostCancellation { get; private set; }
        public int FailCalls;
        public int MarkCalls;
        public int GateThreshold = int.MaxValue;
        public TaskCompletionSource HeldReached { get; } = new(TaskCreationOptions.RunContinuationsAsynchronously);
        public TaskCompletionSource<Result> HeldRelease { get; } = new(TaskCreationOptions.RunContinuationsAsynchronously);

        public CancellationToken Token => Cancellation.Token;

        public void Dispose() => Cancellation.Dispose();

        public RunOptions Options(bool twinRoute, EvaluationLimits? limits = null) => new()
        {
            HostOperations = Operations(twinRoute),
            EvaluationCancellationToken = Token,
            EvaluationLimits = limits,
        };

        // A named frame of host code: the dispatch information the entry point must preserve.
        [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
        private Result ThrowHostFailure()
        {
            Interlocked.Increment(ref FailCalls);
            throw Failure;
        }

        private Result ThrowHostCancellation(CancellationToken token)
        {
            Cancellation.Cancel();
            HostCancellation = new OperationCanceledException("the host cancelled", token);
            throw HostCancellation;
        }

        private Result Gate(Result value)
        {
            if (value is Result.Atom(var level) && level >= GateThreshold)
                Cancellation.Cancel();
            return value;
        }

        public HostOperations Operations(bool twinRoute)
        {
            var operations = new List<HostOperation>
            {
                HostOperation.Create("pass", (a, _) => a[0], "x"),
                HostOperation.Create("mark", (a, _) => { Interlocked.Increment(ref MarkCalls); return a[0]; }, "x"),
                HostOperation.Create("fail", (_, _) => ThrowHostFailure(), "x"),
                HostOperation.Create("cancelnow", (a, _) => { Cancellation.Cancel(); return a[0]; }, "x"),
                HostOperation.Create("throwcancel", (_, token) => ThrowHostCancellation(token), "x"),
                // The token is cancelled first and the operation then fails: the failure is the outcome.
                HostOperation.Create("cancelfail", (_, _) => { Cancellation.Cancel(); return ThrowHostFailure(); }, "x"),
                HostOperation.Create("gate", (a, _) => Gate(a[0]), "x"),
            };

            if (!twinRoute)
            {
                operations.Add(HostOperation.Create("wait", (a, _) => a[0], "x"));
                operations.Add(HostOperation.Create("afail", (_, _) => ThrowHostFailure(), "x"));
                operations.Add(HostOperation.Create("afail0", (_, _) => ThrowHostFailure(), "x"));
                operations.Add(HostOperation.Create("afaulted", (_, _) => ThrowHostFailure(), "x"));
                operations.Add(HostOperation.Create("acancel", (a, _) => { Cancellation.Cancel(); return a[0]; }, "x"));
                operations.Add(HostOperation.Create("athrowcancel", (_, token) => ThrowHostCancellation(token), "x"));
                operations.Add(HostOperation.Create("agate", (a, _) => Gate(a[0]), "x"));
                return HostOperations.Create(operations.ToArray());
            }

            operations.Add(HostOperation.CreateAsync("wait", async (a, _) => { await Task.Yield(); return a[0]; }, "x"));
            // A GENUINE suspension, then the failure.
            operations.Add(HostOperation.CreateAsync("afail", async (_, _) => { await Task.Yield(); return ThrowHostFailure(); }, "x"));
            // The delegate throws before it returns an awaitable.
            operations.Add(HostOperation.CreateAsync("afail0", (_, _) => new ValueTask<Result>(ThrowHostFailure()), "x"));
            // An awaitable that is already faulted: the exception was never thrown.
            operations.Add(HostOperation.CreateAsync("afaulted", (_, _) =>
            {
                Interlocked.Increment(ref FailCalls);
                return new ValueTask<Result>(Task.FromException<Result>(Failure));
            }, "x"));
            // Cancelled while suspended, then a normal return: the observation after the await.
            operations.Add(HostOperation.CreateAsync("acancel", async (a, _) =>
            {
                await Task.Yield();
                Cancellation.Cancel();
                return a[0];
            }, "x"));
            operations.Add(HostOperation.CreateAsync("athrowcancel", async (_, token) =>
            {
                await Task.Yield();
                return ThrowHostCancellation(token);
            }, "x"));
            operations.Add(HostOperation.CreateAsync("agate", async (a, _) => { await Task.Yield(); return Gate(a[0]); }, "x"));
            // Held until the test releases or cancels it: cancellation WHILE suspended.
            operations.Add(HostOperation.CreateAsync("held", async (_, token) =>
            {
                HeldReached.TrySetResult();
                return await HeldRelease.Task.WaitAsync(token);
            }, "x"));
            return HostOperations.Create(operations.ToArray());
        }
    }

    /// <summary>
    /// Counts every time the runtime RAISES this run's own outcome: one first-chance notification
    /// per throw and per rethrow, so a count that grows with the evaluation depth is an exception
    /// crossing the evaluator's frames. Filtered by identity (the host's failure object, or a
    /// cancellation carrying this run's token), so tests running beside this one add nothing.
    /// </summary>
    private sealed class OutcomeThrows : IDisposable
    {
        private readonly Host _host;
        private int _count;

        public OutcomeThrows(Host host)
        {
            _host = host;
            AppDomain.CurrentDomain.FirstChanceException += OnFirstChance;
        }

        public int Count => Volatile.Read(ref _count);

        public void Dispose() => AppDomain.CurrentDomain.FirstChanceException -= OnFirstChance;

        private void OnFirstChance(object? sender, FirstChanceExceptionEventArgs raised)
        {
            if (ReferenceEquals(raised.Exception, _host.Failure)
                || (raised.Exception is OperationCanceledException cancelled && cancelled.CancellationToken == _host.Token))
                Interlocked.Increment(ref _count);
        }
    }

    private sealed record Outcome(RunResult? Result, Exception? Thrown, int FailCalls, int MarkCalls, int Throws);

    private static async Task<Outcome> RunOnTwinRoute(Host host, string source, EvaluationLimits? limits = null)
    {
        using var throws = new OutcomeThrows(host);
        RunResult? result = null;
        Exception? thrown = null;
        try
        {
            result = await Complete(KatLangEngine.RunAsync(source, host.Options(twinRoute: true, limits)));
        }
        catch (Exception error)
        {
            thrown = error;
        }

        return new Outcome(result, thrown, host.FailCalls, host.MarkCalls, throws.Count);
    }

    private static Outcome RunOnSynchronousRoute(Host host, string source, EvaluationLimits? limits = null)
    {
        RunResult? result = null;
        Exception? thrown = null;
        try
        {
            result = KatLangEngine.Run(source, host.Options(twinRoute: false, limits));
        }
        catch (Exception error)
        {
            thrown = error;
        }

        return new Outcome(result, thrown, host.FailCalls, host.MarkCalls, Throws: 0);
    }

    private static string Describe(Outcome outcome)
        => outcome.Thrown is { } thrown
            ? "threw " + thrown.GetType().Name + ": " + thrown.Message
            : outcome.Result switch
            {
                RunResult.ParseFailure parse => "parse failure: " + string.Join(" | ", parse.Errors.Select(error => error.Message)),
                RunResult.EvalFailure eval => "evaluation failure: " + string.Join(" | ", eval.Errors.Select(error => error.Message)),
                var other => "returned " + other,
            };

    // ── The recursion shapes ────────────────────────────────────────────────

    /// <summary>
    /// A recursion of <paramref name="depth"/> levels whose innermost level calls the host
    /// operation <paramref name="operation"/>, followed by a marked effect that must never run.
    /// <c>if</c>: one supplied cell per level. <c>family</c>: clause dispatch, no cell on the
    /// recursion spine. <c>map</c>: a callback per level. <c>loop</c>: a loop step per level, which
    /// charges no depth, so it also reaches levels beyond the depth limit.
    /// </summary>
    private static string Recursion(string shape, string operation, int depth) => shape switch
    {
        "if" => $"F(n) = if(n == 0, {operation}(1), F(n - 1) + 1)\nF({depth}) + mark(1)",
        "family" => $"F(0) = {operation}(1)\nF(n) = F(n - 1) + 1\nF({depth}) + mark(1)",
        "map" => $"F(n) = if(n == 0, {operation}(1), first(map([n - 1], F)) + 1)\nF({depth}) + mark(1)",
        "loop" => $"R(n) = if(n == 0, {operation}(1), R(n - 1).repeat(1))\nR({depth}) + mark(1)",
        _ => throw new ArgumentOutOfRangeException(nameof(shape), shape, null),
    };

    private static readonly string[] Shapes = ["if", "family", "map", "loop"];

    public static TheoryData<string, string> EveryShapeAndFailure()
    {
        var data = new TheoryData<string, string>();
        foreach (var shape in Shapes)
            foreach (var operation in new[] { "fail", "afail", "afail0", "afaulted", "cancelfail" })
                data.Add(shape, operation);
        return data;
    }

    public static TheoryData<string, string> EveryShapeAndCancellation()
    {
        var data = new TheoryData<string, string>();
        foreach (var shape in Shapes)
            foreach (var operation in new[] { "cancelnow", "acancel", "throwcancel", "athrowcancel" })
                data.Add(shape, operation);
        return data;
    }

    public static TheoryData<string, string> EveryShapeAndOutcome()
    {
        var data = new TheoryData<string, string>();
        foreach (var shape in Shapes)
            foreach (var operation in new[] { "fail", "afail", "afail0", "afaulted", "cancelnow", "acancel", "throwcancel", "athrowcancel" })
                data.Add(shape, operation);
        return data;
    }

    // ── 1. Identity and dispatch information ────────────────────────────────

    [Theory]
    [MemberData(nameof(EveryShapeAndFailure))]
    public async Task HostFailure_IsTheSameObject_WithItsHostFrames_AndNothingRunsAfterIt(string shape, string operation)
    {
        var source = Recursion(shape, operation, depth: OracleDepth);
        using var oracleHost = new Host();
        var oracle = RunOnSynchronousRoute(oracleHost, source);
        Assert.True(ReferenceEquals(oracleHost.Failure, oracle.Thrown), "synchronous oracle: " + Describe(oracle));

        using var host = new Host();
        var twin = await RunOnTwinRoute(host, source);

        Assert.True(ReferenceEquals(host.Failure, twin.Thrown), Describe(twin));
        Assert.Equal(oracle.FailCalls, twin.FailCalls);
        Assert.Equal(1, twin.FailCalls);
        Assert.Equal(0, twin.MarkCalls);
        // `cancelfail` cancelled the token before it failed: the failure, raised first, stays the outcome.
        Assert.Equal(operation == "cancelfail", host.Token.IsCancellationRequested);
        if (operation != "afaulted")
        {
            // Dispatch information: the frames the host threw from are still in the trace.
            Assert.Contains("ThrowHostFailure", twin.Thrown!.StackTrace);
        }
    }

    [Theory]
    [MemberData(nameof(EveryShapeAndCancellation))]
    public async Task Cancellation_CarriesTheRunToken_AndAHostThrownOneIsTheSameObject(string shape, string operation)
    {
        var source = Recursion(shape, operation, depth: OracleDepth);
        using var oracleHost = new Host();
        var oracle = RunOnSynchronousRoute(oracleHost, source);
        var oracleCancelled = Assert.IsAssignableFrom<OperationCanceledException>(oracle.Thrown);
        Assert.Equal(oracleHost.Token, oracleCancelled.CancellationToken);

        using var host = new Host();
        var twin = await RunOnTwinRoute(host, source);

        var cancelled = Assert.IsAssignableFrom<OperationCanceledException>(twin.Thrown);
        Assert.Equal(host.Token, cancelled.CancellationToken);
        Assert.Equal(0, twin.MarkCalls);
        Assert.Equal(oracle.MarkCalls, twin.MarkCalls);
        if (operation is "throwcancel" or "athrowcancel")
            Assert.Same(host.HostCancellation, cancelled);
        else
            Assert.Null(host.HostCancellation);
    }

    [Fact]
    public async Task AHostCancellationWithAForeignToken_IsAHostException_PropagatedByIdentity()
    {
        using var foreign = new CancellationTokenSource();
        var hostOwn = new OperationCanceledException("the host's own cancellation", foreign.Token);
        using var cancellation = new CancellationTokenSource();
        var options = new RunOptions
        {
            EvaluationCancellationToken = cancellation.Token,
            HostOperations = HostOperations.Create(
                HostOperation.Create("own", (_, _) => throw hostOwn, "x"),
                HostOperation.CreateAsync("wait", async (a, _) => { await Task.Yield(); return a[0]; }, "x")),
        };

        var thrown = await Assert.ThrowsAsync<OperationCanceledException>(
            () => Complete(KatLangEngine.RunAsync("F(n) = if(n == 0, own(1), F(n - 1) + 1)\nF(30)", options)));

        Assert.Same(hostOwn, thrown);
        Assert.Equal(foreign.Token, thrown.CancellationToken);
        Assert.False(cancellation.IsCancellationRequested);
    }

    [Fact]
    public async Task CancellationWhileAHostOperationIsSuspended_EndsTheRunWithTheRunToken()
    {
        using var host = new Host();
        using var throws = new OutcomeThrows(host);
        var run = KatLangEngine.RunAsync(Recursion("if", "held", depth: 100), host.Options(twinRoute: true));
        await host.HeldReached.Task.WaitAsync(HangGuard);
        Assert.False(run.IsCompleted);

        host.Cancellation.Cancel();

        var cancelled = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Complete(run));
        Assert.Equal(host.Token, cancelled.CancellationToken);
        Assert.True(run.IsCanceled);
        Assert.Equal(0, host.MarkCalls);
        Assert.InRange(throws.Count, 1, MaxOutcomeThrows);
    }

    // ── 2. Unwind work: the outcome is raised a constant number of times ────

    [Theory]
    [MemberData(nameof(EveryShapeAndOutcome))]
    public async Task OutcomeThrows_DoNotGrowWithTheEvaluationDepth(string shape, string operation)
    {
        var counts = new List<int>();
        foreach (var depth in new[] { 15, 60, 120 })
        {
            using var host = new Host();
            var twin = await RunOnTwinRoute(host, Recursion(shape, operation, depth));
            Assert.True(twin.Thrown is not null, $"depth {depth}: {Describe(twin)}");
            Assert.Equal(0, twin.MarkCalls);
            counts.Add(twin.Throws);
        }

        // Thrown through the twins this was about 19 raises per level: 322, 1,177 and 2,317 for
        // `fail` under `if`.
        Assert.All(counts, count => Assert.InRange(count, 1, MaxOutcomeThrows));
        Assert.Equal(counts[0], counts[1]);
        Assert.Equal(counts[0], counts[2]);
    }

    [Theory]
    [InlineData("fail")]
    [InlineData("afail")]
    [InlineData("acancel")]
    [InlineData("athrowcancel")]
    public async Task OutcomeThrows_StayConstant_BeyondTheDepthLimit_ThroughLoopSteps(string operation)
    {
        // Loop steps charge no depth, so this route nests far past MaxDepth (128). At 1,000 levels
        // one host failure used to be raised 20,037 times and allocate 41.9 GB.
        using var host = new Host();
        var twin = await RunOnTwinRoute(host, Recursion("loop", operation, depth: 1000));

        Assert.True(twin.Thrown is not null, Describe(twin));
        if (operation is "fail" or "afail")
            Assert.Same(host.Failure, twin.Thrown);
        else
            Assert.Equal(host.Token, Assert.IsAssignableFrom<OperationCanceledException>(twin.Thrown).CancellationToken);
        Assert.Equal(0, twin.MarkCalls);
        Assert.InRange(twin.Throws, 1, MaxOutcomeThrows);
    }

    [Fact]
    public async Task ASuccessfulRun_RaisesNothing_AndReturnsItsValue()
    {
        foreach (var shape in Shapes)
        {
            using var host = new Host();
            var twin = await RunOnTwinRoute(host, Recursion(shape, "wait", depth: 60));

            Assert.True(twin.Result is RunResult.Success, shape + ": " + Describe(twin));
            Assert.Equal(0, twin.Throws);
            Assert.Equal(1, twin.MarkCalls);
        }
    }

    // ── 3. Whole-run allocation against the successful control ──────────────

    /// <summary>
    /// The bytes one whole engine run allocates, parse included, on the calling thread. The thread
    /// has stack to spare, so the twin run completes synchronously on it (asserted): no stack hop
    /// moves work, and its allocation, to another thread.
    /// </summary>
    private static long AllocatedByOneRun(string shape, string operation, int depth)
    {
        using var host = new Host();
        var options = host.Options(twinRoute: true);
        var source = Recursion(shape, operation, depth);

        var before = GC.GetAllocatedBytesForCurrentThread();
        var run = KatLangEngine.RunAsync(source, options);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.True(run.IsCompleted, "the run was expected to complete synchronously on a thread with stack to spare");
        if (operation == "pass")
            Assert.True(run.Result is RunResult.Success, run.Result.ToString());
        else
            Assert.True(run.IsFaulted || run.IsCanceled, "the run was expected to be ended by its host");
        // Observed, so no unobserved task exception is left behind.
        _ = run.Exception;
        return allocated;
    }

    [Theory]
    [InlineData("if", "fail")]
    [InlineData("if", "cancelnow")]
    [InlineData("if", "throwcancel")]
    [InlineData("family", "fail")]
    [InlineData("family", "cancelnow")]
    [InlineData("map", "fail")]
    public void AHostEndedRun_AllocatesWhatItsSuccessfulControlAllocates(string shape, string operation)
    {
        int[] depths = [30, 60, 120];
        var control = new long[depths.Length];
        var ended = new long[depths.Length];
        AstStructuralDepthProcessTests.RunOnThreadWithStack(64 * 1024 * 1024, () =>
        {
            // Warm up outside the measured windows: type loading, static state, tiered code.
            for (var i = 0; i < 3; i++)
            {
                AllocatedByOneRun(shape, "pass", 8);
                AllocatedByOneRun(shape, operation, 8);
            }

            for (var i = 0; i < depths.Length; i++)
            {
                control[i] = AllocatedByOneRun(shape, "pass", depths[i]);
                ended[i] = AllocatedByOneRun(shape, operation, depths[i]);
            }
        });

        // A coarse in-process bound (AGENTS.md, Testing Expectations): the per-thread counter can be
        // off by one allocation quantum (~8 KB), and tiering can add a little after the warm-up.
        // Measured: the ended run allocates within 2% of its control (1.29 MB against 1.31 MB at
        // depth 120 under `if`). Thrown through the twins it allocated 50 MB, 188 MB and 727 MB at
        // these depths, 557 times its control at depth 120.
        const long Slack = 256 * 1024;
        for (var i = 0; i < depths.Length; i++)
        {
            Assert.True(
                ended[i] <= 2 * control[i] + Slack,
                $"{shape}/{operation} at depth {depths[i]}: the host-ended run allocated {ended[i]:N0} bytes, its successful control {control[i]:N0}");
        }

        // Linear in the depth: doubling the depth at most doubles the allocation (it was x3.9).
        Assert.True(
            ended[2] <= 2 * ended[1] + Slack,
            $"{shape}/{operation}: {ended[1]:N0} bytes at depth {depths[1]}, {ended[2]:N0} at depth {depths[2]}");
    }

    // ── 4. Cancellation of a deep loop-step recursion ───────────────────────

    [Theory]
    [InlineData("gate")]
    [InlineData("agate")]
    public async Task ARunawayLoopStepRecursion_CancelledAtDepth_ReturnsWithConstantUnwindWork(string operation)
    {
        // An unbounded recursion through loop steps: nothing but cancellation stops it, and the
        // twin route continues it on fresh stacks (StackHop). The host cancels when the recursion
        // reaches level 2,000; `gate` returns normally and the next chokepoint observes the token,
        // `agate` suspends at every level and the observation after its await sees it. Thrown
        // through the twins, cancelling at depth 1,000 took 9 to 27 s and 36 GB, and the audit's
        // free-running case did not return within 200 s.
        using var host = new Host { GateThreshold = 2000 };
        var twin = await RunOnTwinRoute(host, $"R(n) = if({operation}(n) < 0, 0, R(n + 1).repeat(1))\nR(0) + mark(1)");

        var cancelled = Assert.IsAssignableFrom<OperationCanceledException>(twin.Thrown);
        Assert.Equal(host.Token, cancelled.CancellationToken);
        Assert.Equal(0, twin.MarkCalls);
        Assert.InRange(twin.Throws, 1, MaxOutcomeThrows);
    }

    [Fact]
    public async Task ADeepLoopStepRecursion_CancelledWhileItsHostOperationIsSuspended_ReturnsWithConstantUnwindWork()
    {
        using var host = new Host();
        using var throws = new OutcomeThrows(host);
        var run = KatLangEngine.RunAsync(Recursion("loop", "held", depth: 2000), host.Options(twinRoute: true));
        await host.HeldReached.Task.WaitAsync(HangGuard);

        host.Cancellation.Cancel();

        var cancelled = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Complete(run));
        Assert.Equal(host.Token, cancelled.CancellationToken);
        Assert.Equal(0, host.MarkCalls);
        Assert.InRange(throws.Count, 1, MaxOutcomeThrows);
    }

    // ── 5. The first terminal outcome, and no consumer absorbs it ───────────

    /// <summary>
    /// Programs in which a consumer INSPECTS a failed demand and has somewhere else to go: a later
    /// clause, a callable alternative, a second member of a repeated-name group, the next item of a
    /// callback, the next round of a loop, a second read of a property. The host's failure must
    /// end the run at its first call; <c>mark</c> counts anything that ran after it.
    /// </summary>
    public static TheoryData<string> AbsorptionCandidates => new()
    {
        // Clause dispatch: the literal head demands the argument; the later clause must not run.
        "G(0) = 1\nG(n) = mark(2)\nG(fail(1))",
        "G(0, n) = 1\nG(m, n) = mark(2)\nG(fail(1), mark(3))",
        // A repeated-name group compares its two members: the second is never demanded.
        "Same(x, x) = 1\nSame(x, y) = mark(2)\nSame(fail(1), fail(2))",
        // Dot call: the receiver is a computed value, so the edge is the extension call.
        "Twice(x) = mark(x) * 2\nfail(1).Twice",
        "fail(1).string.count + mark(1)",
        // A callable parameter and the host operation as a callback.
        "Apply(f, x) = f(x) + mark(1)\nApply(fail, 3)",
        "map([1, 2, 3], fail).count + mark(1)",
        "filter([1, 2, 3], fail).count + mark(1)",
        "Keep(x) = mark(x) > 0\nfilter([fail(1), 2, 3], Keep).count",
        // Loops: the first round's failure ends the loop.
        "Step(x) = fail(x) + mark(1)\nStep(1).repeat(3)",
        "Step(x) = fail(x), mark(x) < 3\nStep(1).while",
        // Selection and laziness.
        "if(fail(1) > 0, mark(1), mark(2))",
        "[fail(1), mark(2)].count",
        "Pick(*xs) = xs[0] + mark(9)\nPick(fail(1), mark(2))",
        // The property cache, and an exported member evaluated detached.
        "A = fail(1)\nA + A + mark(1)",
        "Lib = {\n    public P = fail(1)\n}\nLib.P + Lib.P + mark(1)",
        // A captured call invoked through its reference.
        "Twice(meta r) = r.Invoke() + r.Invoke() + mark(1)\nId(x) = x\nTwice(Id(fail(1)))",
        // A spread opened while the supply is formed.
        "Sum2(a, b) = a + b + mark(1)\nPair = [fail(1), 2]\nSum2(Pair*)",
    };

    [Theory]
    [MemberData(nameof(AbsorptionCandidates))]
    public async Task NoConsumerAbsorbsTheHostFailure_AndTheTwinRouteAgreesWithTheSynchronousRoute(string source)
    {
        using var oracleHost = new Host();
        var oracle = RunOnSynchronousRoute(oracleHost, source);
        Assert.True(ReferenceEquals(oracleHost.Failure, oracle.Thrown), "synchronous oracle: " + Describe(oracle));

        using var host = new Host();
        var twin = await RunOnTwinRoute(host, source);

        Assert.True(ReferenceEquals(host.Failure, twin.Thrown), Describe(twin));
        Assert.Equal(1, twin.FailCalls);
        Assert.Equal(oracle.FailCalls, twin.FailCalls);
        Assert.Equal(oracle.MarkCalls, twin.MarkCalls);
        Assert.InRange(twin.Throws, 1, MaxOutcomeThrows);
    }

    [Theory]
    [MemberData(nameof(AbsorptionCandidates))]
    public async Task NoConsumerAbsorbsACancellation_AndTheTwinRouteAgreesWithTheSynchronousRoute(string failing)
    {
        // The same programs with the failing operation replaced by one that cancels the token and
        // returns: whatever would have run after the failure now meets a cancelled run instead.
        var source = System.Text.RegularExpressions.Regex.Replace(failing, @"\bfail\b", "cancelnow");
        using var oracleHost = new Host();
        var oracle = RunOnSynchronousRoute(oracleHost, source);
        Assert.True(oracle.Thrown is OperationCanceledException, "synchronous oracle: " + Describe(oracle));

        using var host = new Host();
        var twin = await RunOnTwinRoute(host, source);

        var cancelled = Assert.IsAssignableFrom<OperationCanceledException>(twin.Thrown);
        Assert.Equal(host.Token, cancelled.CancellationToken);
        Assert.Equal(oracle.MarkCalls, twin.MarkCalls);
        Assert.InRange(twin.Throws, 1, MaxOutcomeThrows);
    }

    [Fact]
    public async Task AReachedResourceLimit_StaysTheRunsOutcome_WhenNothingCancelsIt()
    {
        // The limit is a returned evaluation failure on both routes; the marker of a host-ended
        // run never stands in for it.
        const string Source = "F(n) = if(n == 0, pass(1), F(n - 1) + 1)\nF(60) + mark(1)";
        var limits = new EvaluationLimits { MaxSteps = 20 };
        using var oracleHost = new Host();
        var oracle = RunOnSynchronousRoute(oracleHost, Source, limits);
        var oracleFailure = Assert.IsType<RunResult.EvalFailure>(oracle.Result);

        using var host = new Host();
        var twin = await RunOnTwinRoute(host, Source, limits);

        var failure = Assert.IsType<RunResult.EvalFailure>(twin.Result);
        Assert.Equal(KatLangErrorCode.EvaluationStepLimitExceeded, Assert.Single(failure.Errors).Code);
        Assert.Equal(Assert.Single(oracleFailure.Errors).Message, Assert.Single(failure.Errors).Message);
        Assert.Equal(0, twin.MarkCalls);
        Assert.Equal(0, twin.Throws);
    }

    [Fact]
    public void ACancellationObservedAfterALimitWasReached_OutranksTheLimit_InsideAndOutsideTheBoundary()
    {
        // The chokepoints' order: host cancellation is observed before a retained limit is
        // reported. A thrown cancellation never lost to an error value; neither does a carried one.
        foreach (var insideBoundary in new[] { false, true })
        {
            using var cancellation = new CancellationTokenSource();
            var budget = EvaluationBudget.Create(new EvaluationLimits { MaxSteps = 1 }, cancellationToken: cancellation.Token);
            budget.MarkAsynchronousRun();
            if (insideBoundary) budget.OpenHostTerminationBoundary();
            Assert.Null(budget.TryChargeStep());
            var limit = Assert.IsType<EvalError.EvaluationStepLimitExceeded>(budget.TryChargeStep());
            Assert.Same(limit, budget.CheckContinuation());

            cancellation.Cancel();

            if (insideBoundary)
            {
                Assert.True(budget.CheckContinuation()!.IsHostTermination);
                Assert.True(budget.TryChargeStep()!.IsHostTermination);
                budget.CloseHostTerminationBoundary();
                Assert.Equal(cancellation.Token, Assert.Throws<OperationCanceledException>(budget.RethrowHostTermination).CancellationToken);
            }
            else
            {
                Assert.Equal(cancellation.Token, Assert.Throws<OperationCanceledException>(() => budget.CheckContinuation()).CancellationToken);
                budget.RethrowHostTermination();
            }

            Assert.Equal(1, budget.ConsumedSteps);
        }
    }

    [Fact]
    public async Task ACancelledRun_NeverReportsALimitItWouldHaveReached()
    {
        // The token is cancelled before the recursion that would exhaust the step limit: the run
        // ends with the cancellation on both routes, and the limit is never the verdict.
        const string Source = "F(n) = if(n == 0, pass(1), F(n - 1) + 1)\ncancelnow(1) + F(60)";
        var limits = new EvaluationLimits { MaxSteps = 20 };
        using var oracleHost = new Host();
        var oracle = RunOnSynchronousRoute(oracleHost, Source, limits);
        Assert.True(oracle.Thrown is OperationCanceledException, "synchronous oracle: " + Describe(oracle));

        using var host = new Host();
        var twin = await RunOnTwinRoute(host, Source, limits);

        Assert.Equal(host.Token, Assert.IsAssignableFrom<OperationCanceledException>(twin.Thrown).CancellationToken);
    }

    // ── 6. Runs a host operation starts ─────────────────────────────────────

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public async Task ANestedRunsFailure_ThatItsHostOperationLetsThrough_EndsTheOuterRunWithTheSameObject(bool nestedOnTwinRoute)
    {
        using var inner = new Host();
        using var outer = new Host();
        var nestedSource = Recursion("if", nestedOnTwinRoute ? "afail" : "fail", depth: 30);
        var operations = HostOperations.Create(
            HostOperation.Create("mark", (a, _) => { Interlocked.Increment(ref outer.MarkCalls); return a[0]; }, "x"),
            HostOperation.CreateAsync("nested", async (_, _) =>
            {
                if (nestedOnTwinRoute)
                    await KatLangEngine.RunAsync(nestedSource, inner.Options(twinRoute: true));
                else
                    KatLangEngine.Run(nestedSource, inner.Options(twinRoute: false));
                return Atom(0);
            }, "x"));

        var thrown = await Assert.ThrowsAsync<HostFailure>(() => Complete(KatLangEngine.RunAsync(
            "F(n) = if(n == 0, nested(1), F(n - 1) + 1)\nF(30) + mark(1)",
            new RunOptions { HostOperations = operations, EvaluationCancellationToken = outer.Token })));

        Assert.Same(inner.Failure, thrown);
        Assert.Equal(1, inner.FailCalls);
        Assert.Equal(0, outer.MarkCalls);
    }

    [Theory]
    [InlineData("fail")]
    [InlineData("afail")]
    [InlineData("cancelnow")]
    [InlineData("acancel")]
    public async Task ANestedRunsTermination_ThatItsHostOperationHandles_LeavesTheOuterRunRunning(string nestedOperation)
    {
        // The nested run has its own budget: its retained exception ends that run only. The outer
        // run's host operation observes it as an exception, returns a value, and the outer run goes
        // on to evaluate, call other operations and succeed.
        using var inner = new Host();
        using var outer = new Host();
        Exception? observed = null;
        var operations = HostOperations.Create(
            HostOperation.Create("mark", (a, _) => { Interlocked.Increment(ref outer.MarkCalls); return a[0]; }, "x"),
            HostOperation.CreateAsync("nested", async (_, _) =>
            {
                try
                {
                    await KatLangEngine.RunAsync(Recursion("if", nestedOperation, depth: 30), inner.Options(twinRoute: true));
                }
                catch (Exception error)
                {
                    observed = error;
                }

                return Atom(40);
            }, "x"));

        var result = await Complete(KatLangEngine.RunAsync(
            "F(n) = if(n == 0, nested(1), F(n - 1) + 1)\nF(2) + mark(100)",
            new RunOptions { HostOperations = operations, EvaluationCancellationToken = outer.Token }));

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal("142", success.ToDisplayString());
        Assert.Equal(1, outer.MarkCalls);
        Assert.False(outer.Token.IsCancellationRequested);
        if (nestedOperation is "fail" or "afail")
            Assert.Same(inner.Failure, observed);
        else
            Assert.Equal(inner.Token, Assert.IsAssignableFrom<OperationCanceledException>(observed).CancellationToken);
    }

    // ── 7. Budget conservation and the closed boundary ──────────────────────

    [Theory]
    [InlineData("fail")]
    [InlineData("afail")]
    [InlineData("cancelnow")]
    [InlineData("acancel")]
    public async Task EveryAdmittedLevelIsReleased_AndTheBoundaryIsClosed_AfterAHostEndedRun(string operation)
    {
        // The pass-through cache records the run's budget at the property access, so the budget
        // stays observable after the run ended with an exception.
        using var host = new Host();
        var operations = host.Operations(twinRoute: true);
        var parsed = Parser.Parse(
            $"Data = {operation}(1)\nG(x) = Data * x\nF(n) = if(n == 0, G(3), F(n - 1) + 1)\nF(40)",
            new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
        var cache = new PassThroughAsyncZeroArgPropertyResultCache();

        var thrown = await Record.ExceptionAsync(async () => await Evaluator.RunCountedObservedAsync(
            new Expr.AlgorithmExpr(parsed.Root), zeroArgPropertyResultCache: cache, hostOperations: operations,
            cancellationToken: host.Token));

        if (operation is "fail" or "afail")
            Assert.Same(host.Failure, thrown);
        else
            Assert.Equal(host.Token, Assert.IsAssignableFrom<OperationCanceledException>(thrown).CancellationToken);
        var budget = cache.ObservedBudget;
        Assert.NotNull(budget);
        Assert.True(budget.IsAsynchronousRun);
        Assert.Equal(0, budget.CurrentDepth);
        Assert.False(budget.CarriesHostTermination);
        Assert.True(budget.RunEnded);
    }

    [Fact]
    public async Task ARunPreparedBelowTheEntryPoints_CarriesNothing_AndThrowsAsBefore()
    {
        // A budget no entry point opened a boundary for: its chokepoints throw, on a run marked
        // asynchronous too. Nothing would rethrow a carried exception there.
        using var cancellation = new CancellationTokenSource();
        var budget = EvaluationBudget.Create(null, cancellationToken: cancellation.Token);
        budget.MarkAsynchronousRun();
        Assert.False(budget.CarriesHostTermination);
        Assert.Null(budget.CheckContinuation());
        var cell = new NeedCell(
            () => throw new InvalidOperationException("the asynchronous demand evaluates"),
            () => new ValueTask<EvalResult<Evaluator.CountedResult>>(
                EvalResult<Evaluator.CountedResult>.Ok(new Evaluator.CountedResult(Atom(1), 1))),
            budget: budget,
            token: cancellation.Token);

        cancellation.Cancel();

        Assert.Equal(cancellation.Token, Assert.Throws<OperationCanceledException>(() => budget.CheckContinuation()).CancellationToken);
        Assert.Equal(cancellation.Token, Assert.Throws<OperationCanceledException>(budget.ObserveCancellation).CancellationToken);
        var thrown = await Assert.ThrowsAsync<OperationCanceledException>(async () => await cell.DemandAsync());
        Assert.Equal(cancellation.Token, thrown.CancellationToken);
        Assert.False(cell.HasCompletedValue);
    }

    // ── 8. The stored state of cells inside the boundary ────────────────────

    private static EvaluationBudget BudgetInsideBoundary(CancellationToken token = default)
    {
        var budget = EvaluationBudget.Create(null, cancellationToken: token);
        budget.MarkAsynchronousRun();
        budget.OpenHostTerminationBoundary();
        return budget;
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task CancellationInsideAHelper_LeavesTheFamilySpineByValue(bool insideAtoms)
    {
        using var host = new Host();
        using var throws = new OutcomeThrows(host);
        var walk = new ValueTraversalObservations { LanguageAtomsCheckpointReached = host.Cancellation.Cancel };
        EvaluationObservations? observation = null;
        var family = new PatternComparisonObservations
        {
            CheckpointReached = _ =>
            {
                if (!insideAtoms && observation!.ClauseFamilyPreparationCount == 1) host.Cancellation.Cancel();
            },
        };
        observation = new EvaluationObservations { StructuralTraversal = walk, FamilyDuplicateIndex = family };
        var leaf = insideAtoms ? "atoms(range(1, 2048))" : "G(0)";
        var source = $"G('{new string('x', 8192)}') = 0\nG(n) = n\nF(0) = {leaf}\nF(n) = F(n - 1) + 1\nF(60)";
        var root = SourceProvenance.ParseValid(source).Root;
        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
            await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(root),
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                observations: observation, cancellationToken: host.Token));
        Assert.Equal(host.Token, thrown.CancellationToken);
        Assert.Equal(1, observation.ClauseFamilyPreparationCount);
        Assert.Equal(insideAtoms ? 1 : 0, walk.LanguageAtomsCancellationCheckpointCount);
        Assert.InRange(throws.Count, 1, MaxOutcomeThrows);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task CancellationPrecedesACellsPreviouslyCompletedLimit(bool projection)
    {
        using var cancellation = new CancellationTokenSource();
        var budget = BudgetInsideBoundary(cancellation.Token);
        var limit = new EvalError.EvaluationDepthExceeded(1);
        var cell = NeedCell.WithRuntimeProjection(
            () => limit, () => new(limit), () => limit, () => new(limit), budget: budget);
        if (projection) Assert.Same(limit, (await cell.ProjectCallableAsync()).Error);
        else Assert.Same(limit, (await cell.DemandAsync()).Error);

        cancellation.Cancel();

        Assert.True(cell.Demand().Error.IsHostTermination);
        Assert.True((await cell.DemandAsync()).Error.IsHostTermination);
        Assert.True(cell.ProjectCallable().Error.IsHostTermination);
        Assert.True((await cell.ProjectCallableAsync()).Error.IsHostTermination);
        budget.CloseHostTerminationBoundary();
        Assert.Equal(cancellation.Token, Assert.Throws<OperationCanceledException>(budget.RethrowHostTermination).CancellationToken);
    }

    [Fact]
    public async Task APlanWaiterReceivesTheRetainedFailureInsideTheBoundary()
    {
        var budget = BudgetInsideBoundary();
        var failure = new HostFailure("spread failed");
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var spread = new NeedCell(() => throw new InvalidOperationException(), async () =>
        {
            entered.SetResult();
            await release.Task;
            return budget.RetainHostTermination(failure);
        }, budget: budget);
        var ctx = (Evaluator.EvalCtx.Empty with { Budget = budget }).WithNeedEnv([("p", spread)]);
        var plan = new Evaluator.InvocationPlan(ctx, []);
        var call = new Expr.Call(new Expr.Resolve("F"), [new Expr.SequenceSpread(new Expr.Param("p"))]);
        _ = new NeedCell(call, plan, budget, runtimeProjection: false, default);
        var view = plan.Reference.ArgumentView;
        var starter = Evaluator.PrepareArgumentViewAsync(view, ctx).AsTask();
        try
        {
            await entered.Task.WaitAsync(HangGuard);
            var waiter = Evaluator.PrepareArgumentViewAsync(view, ctx).AsTask();
            var observer = plan.PrepareSupply(true).AsTask();
            Assert.False(waiter.IsCompleted);
            Assert.False(observer.IsCompleted);
            release.TrySetResult();
            Assert.True((await waiter.WaitAsync(HangGuard)).Error.IsHostTermination);
            Assert.True((await starter.WaitAsync(HangGuard)).Error.IsHostTermination);
            Assert.Same(failure, await Assert.ThrowsAsync<HostFailure>(() => observer.WaitAsync(HangGuard)));
            Assert.True(Evaluator.PrepareArgumentView(view, ctx).Error.IsHostTermination);
            Assert.Same(failure, Assert.IsType<ExceptionDispatchInfo>(plan.Supply).SourceException);
            budget.CloseHostTerminationBoundary();
            Assert.Same(failure, await Assert.ThrowsAsync<HostFailure>(async () => await Evaluator.PrepareArgumentViewAsync(view, ctx)));
        }
        finally
        {
            release.TrySetResult();
        }
    }

    [Fact]
    public async Task ACellEndedByTheMarker_StoresTheRetainedException_PublishesNothing_AndIsNeverRestarted()
    {
        var budget = BudgetInsideBoundary();
        var failure = new HostFailure("carried");
        var computations = 0;
        var cell = new NeedCell(
            () => throw new InvalidOperationException("the asynchronous demand evaluates"),
            () =>
            {
                Interlocked.Increment(ref computations);
                // What a host-operation site returns inside the boundary.
                return new ValueTask<EvalResult<Evaluator.CountedResult>>(budget.RetainHostTermination(failure));
            },
            budget: budget);

        var first = await cell.DemandAsync();

        Assert.True(first.IsError && first.Error.IsHostTermination);
        Assert.True(first.Error.IsTerminalForRun);
        Assert.False(first.Error.IsResourceLimit);
        // The completion a thrown exception leaves: completed, nothing in flight, no edge.
        Assert.True(cell.HasCompletedValue);
        Assert.False(cell.HasValueInFlight);
        Assert.Equal(0, cell.ActiveDependencyCount);
        // Inside the boundary every later observation answers with the run's terminal state.
        Assert.True((await cell.DemandAsync()).Error.IsHostTermination);
        Assert.True(cell.Demand().Error.IsHostTermination);
        Assert.True(cell.ProjectCallable().Error.IsHostTermination);
        Assert.False(cell.HasCallableMemo);
        Assert.True(budget.CheckContinuation()!.IsHostTermination);
        Assert.True(budget.TryChargeStep()!.IsHostTermination);
        Assert.True(budget.TryEnterInvocation()!.IsHostTermination);
        Assert.Equal(0, budget.CurrentDepth);
        Assert.Equal(0, budget.ConsumedSteps);

        // The boundary closes and rethrows the original object; the cell then rethrows it too,
        // exactly as a cell a thrown exception completed does, and never evaluates again.
        budget.CloseHostTerminationBoundary();
        Assert.Same(failure, Assert.Throws<HostFailure>(budget.RethrowHostTermination));
        Assert.Same(failure, await Assert.ThrowsAsync<HostFailure>(async () => await cell.DemandAsync()));
        Assert.Same(failure, Assert.Throws<HostFailure>(() => cell.Demand()));
        Assert.Equal(1, computations);
    }

    [Fact]
    public async Task AJoinerOfACellEndedByTheMarker_ReceivesTheMarkerByValue_AndLeavesNoEdge()
    {
        var budget = BudgetInsideBoundary();
        var failure = new HostFailure("carried to a joiner");
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var cell = new NeedCell(
            () => throw new InvalidOperationException("the asynchronous demand evaluates"),
            async () =>
            {
                entered.TrySetResult();
                await release.Task;
                return budget.RetainHostTermination(failure);
            },
            budget: budget);

        var starter = Task.Run(async () => await cell.DemandAsync());
        await entered.Task.WaitAsync(HangGuard);
        var joiner = Task.Run(async () => await cell.DemandAsync());
        var deadline = DateTime.UtcNow + HangGuard;
        while (!cell.HasJoinedValueFlight)
        {
            Assert.True(DateTime.UtcNow < deadline, "hang guard: the joiner never joined the flight");
            await Task.Delay(1);
        }

        release.TrySetResult();

        Assert.True((await starter.WaitAsync(HangGuard)).Error.IsHostTermination);
        Assert.True((await joiner.WaitAsync(HangGuard)).Error.IsHostTermination);
        Assert.True(cell.HasCompletedValue);
        Assert.False(cell.HasValueInFlight);
        Assert.Equal(0, cell.ActiveDependencyCount);
        budget.CloseHostTerminationBoundary();
        Assert.Same(failure, Assert.Throws<HostFailure>(budget.RethrowHostTermination));
    }

    [Fact]
    public async Task ARuntimeProjectionEndedByTheMarker_StoresTheRetainedException_AndPublishesNoCallable()
    {
        var budget = BudgetInsideBoundary();
        var failure = new HostFailure("carried through a projection");
        var cell = NeedCell.WithRuntimeProjection(
            () => throw new InvalidOperationException("CALLABLE must not demand VALUE"),
            () => throw new InvalidOperationException("CALLABLE must not demand VALUE"),
            () => throw new InvalidOperationException("the asynchronous projection runs"),
            () => new ValueTask<EvalResult<Algorithm?>>(budget.RetainHostTermination(failure)),
            budget: budget);

        var projected = await cell.ProjectCallableAsync();

        Assert.True(projected.IsError && projected.Error.IsHostTermination);
        // A failed projection is marked; a host-ended one is not a projection outcome at all.
        Assert.False(projected.Error.IsProjectionFailure);
        Assert.False(cell.HasCallableMemo);
        Assert.False(cell.HasProjectionInFlight);
        Assert.Equal(1, cell.ProjectionComputations);
        Assert.Equal(0, cell.ProjectionActiveDependencyCount);
        Assert.True((await cell.ProjectCallableAsync()).Error.IsHostTermination);

        budget.CloseHostTerminationBoundary();
        Assert.Same(failure, await Assert.ThrowsAsync<HostFailure>(async () => await cell.ProjectCallableAsync()));
        Assert.Equal(1, cell.ProjectionComputations);
    }

    [Fact]
    public async Task InsideTheBoundary_TheRetainedExceptionThrownAgain_IsCarried_AndAnyOtherExceptionStaysLoud()
    {
        var budget = BudgetInsideBoundary();
        var failure = new HostFailure("retained, then thrown by a caller that cannot return a failure");
        var rethrowing = new NeedCell(
            () => throw new InvalidOperationException("the asynchronous demand evaluates"),
            () =>
            {
                // A value walk's cancellation checkpoint: the run retains its outcome and the
                // checkpoint, which has no failure to return, throws it.
                budget.RetainHostTermination(failure);
                throw failure;
            },
            budget: budget);
        // The cell stores the thrown exception as always, and its starter answers by value: the
        // exception is the run's own retained outcome.
        Assert.True((await rethrowing.DemandAsync()).Error.IsHostTermination);
        Assert.True(rethrowing.HasCompletedValue);
        // A cell first observed after that answers from its observation entry, without evaluating.
        var later = new NeedCell(
            () => throw new InvalidOperationException("the asynchronous demand evaluates"),
            () => throw new InvalidOperationException("an ended run evaluates nothing"),
            budget: budget);
        Assert.True((await later.DemandAsync()).Error.IsHostTermination);
        Assert.False(later.HasCompletedValue);

        var other = BudgetInsideBoundary();
        var unexpected = new InvalidOperationException("an evaluator invariant");
        var failing = new NeedCell(
            () => throw new InvalidOperationException("the asynchronous demand evaluates"),
            () => throw unexpected,
            budget: other);

        // Not a host termination: nothing retained it, so it is thrown, not carried.
        Assert.Same(unexpected, await Assert.ThrowsAsync<InvalidOperationException>(async () => await failing.DemandAsync()));
        Assert.Null(other.CheckContinuation());
        other.CloseHostTerminationBoundary();
        other.RethrowHostTermination();
    }

    [Fact]
    public void TheFirstRetainedException_IsTheRunsOutcome_AndCancellationIsCarriedWithItsToken()
    {
        using var cancellation = new CancellationTokenSource();
        var budget = BudgetInsideBoundary(cancellation.Token);
        Assert.Null(budget.CheckContinuation());
        Assert.Null(budget.ObserveToken(cancellation.Token));

        cancellation.Cancel();

        // Retained and returned, never thrown, and before any counter moves.
        Assert.True(budget.TryEnterInvocation()!.IsHostTermination);
        Assert.True(budget.TryChargeExpressionNodeWork()!.IsHostTermination);
        Assert.True(budget.TryReserveCollection(1)!.IsHostTermination);
        Assert.True(budget.ObserveToken(cancellation.Token)!.IsHostTermination);
        Assert.Equal(0, budget.CurrentDepth);
        Assert.Equal(0, budget.ConsumedSteps);
        Assert.Equal(0, budget.MaterializedItems);
        // A later host failure never replaces the first outcome.
        Assert.True(budget.RetainHostTermination(new HostFailure("later")).IsHostTermination);
        // A caller that cannot return a failure still throws — the run's first exception.
        var fromVoidSite = Assert.Throws<OperationCanceledException>(budget.ObserveCancellation);
        Assert.Equal(cancellation.Token, fromVoidSite.CancellationToken);

        budget.CloseHostTerminationBoundary();
        var rethrown = Assert.Throws<OperationCanceledException>(budget.RethrowHostTermination);
        Assert.Same(fromVoidSite, rethrown);
        Assert.Equal(cancellation.Token, rethrown.CancellationToken);
    }

    [Fact]
    public void TheMarker_IsNotAnErrorCategory_AndClassifyingItFailsLoud()
    {
        var marker = EvalError.HostTermination.Marker;

        Assert.True(marker.IsHostTermination);
        Assert.True(marker.IsTerminalForRun);
        Assert.False(marker.IsResourceLimit);
        Assert.True(new EvalError.WithContext("a frame", marker).IsHostTermination);
        Assert.True(new EvalError.WithContext("a frame", marker).IsTerminalForRun);
        Assert.False(new EvalError.DivByZero().IsHostTermination);
        Assert.False(new EvalError.DivByZero().IsTerminalForRun);
        Assert.True(new EvalError.EvaluationStepLimitExceeded(1).IsTerminalForRun);
        Assert.False(Evaluator.IsLiftableError(marker));
        Assert.False(Evaluator.IsAbsentIdentity(marker));
        Assert.False(Evaluator.IsDeferrableEvaluationFailure(marker));
        Assert.Throws<System.Diagnostics.UnreachableException>(() => marker.Code);
        Assert.Throws<System.Diagnostics.UnreachableException>(() => KatLangError.FromEvalError(marker));
    }
}
