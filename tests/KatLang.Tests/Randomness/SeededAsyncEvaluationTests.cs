using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.Randomness.SeededRun;

namespace KatLang.Tests.Randomness;

/// <summary>
/// A seeded run's stream survives GENUINE suspension: an incomplete host awaitable, a
/// externally held asynchronous property-cache seam, and a deferred module region's
/// on-demand materialization all resume the run with the same stream where it left
/// off — nothing is reseeded, replayed, or duplicated — so the async twin family's
/// values equal the synchronous semantic baseline and the test-side oracle.
/// </summary>
public class SeededAsyncEvaluationTests
{
    private const long Seed = 0xA5A5;

    private const string R = "R = Math.RandomInt(0, 4294967296)\n";

    private static Decimal128[] Draws(int count)
    {
        var words = Words(Seed);
        return Enumerable.Range(0, count).Select(_ => LowWordMod2Pow32(words)).ToArray();
    }

    private static IReadOnlyList<Decimal128> Atoms<T>(EvalResult<T> result, Func<T, Result> value)
    {
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        return value(result.Value).ToHostAtoms();
    }

    // ── Host-operation suspension ─────────────────────────────────────────────

    /// <summary>
    /// The test releases each invocation only after observing the evaluator suspended.
    /// Task.Yield alone is insufficient: its continuation may finish before return.
    /// </summary>
    private sealed class HoldingPause(int count)
    {
        private readonly TaskCompletionSource[] _reached = Enumerable.Range(0, count)
            .Select(_ => new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously)).ToArray();
        private readonly TaskCompletionSource[] _gates = Enumerable.Range(0, count)
            .Select(_ => new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously)).ToArray();

        public int Calls { get; private set; }

        public Task Reached(int index) => _reached[index].Task;
        public void Release(int index) => _gates[index].TrySetResult();

        public void ReleaseAll()
        {
            foreach (var gate in _gates)
                gate.TrySetResult();
        }

        public ValueTask<Result> InvokeAsync(IReadOnlyList<Result> arguments, CancellationToken cancellationToken)
        {
            var index = Calls++;
            var pending = PauseAsync(arguments[0], _gates[index].Task);
            Assert.False(pending.IsCompleted);
            _reached[index].TrySetResult();
            return pending;
        }

        private static async ValueTask<Result> PauseAsync(Result echo, Task gate)
        {
            await Task.Yield();
            await gate;
            return echo;
        }
    }

    private static async Task ReleasePauses(Task pending, HoldingPause pause, int first)
    {
        try
        {
            for (var index = first; index < first + 2; index++)
            {
                await pause.Reached(index).WaitAsync(TimeSpan.FromSeconds(45));
                Assert.False(pending.IsCompleted);
                Assert.Equal(index + 1, pause.Calls);
                pause.Release(index);
            }
        }
        finally
        {
            // Also unblock the run if an assertion fails.
            pause.ReleaseAll();
        }
    }

    [Theory]
    [InlineData("F(a, b, c) = c, b, a\nF(R(), Pause(R()), R()), Pause(R()), R()")]
    [InlineData("F((a, b), c) = c, b, a\nF((R(), Pause(R())), R()), Pause(R()), R()")]
    [InlineData("F(a, b, c) = c, b, a\nR().F(Pause(R()), R()), Pause(R()), R()")]
    public async Task HostOperationSuspension_ResumesTheStream_WithoutReplayOrReseed(string body)
    {
        var program = R + body;
        var pause = new HoldingPause(2);
        var asyncOperations = HostOperations.Create(HostOperation.CreateAsync("Pause", pause.InvokeAsync, "echo"));
        var syncOperations = HostOperations.Create(HostOperation.Create("Pause", static (arguments, _) => arguments[0], "echo"));
        var parsed = Parser.Parse(program, new RunOptions { HostOperations = asyncOperations });
        Assert.False(parsed.HasErrors);
        var ast = new Expr.AlgorithmExpr(parsed.Root);
        var d = Draws(5);
        Decimal128[] expected = [d[2], d[1], d[0], d[3], d[4]];

        // Synchronous semantic baseline (a synchronous Pause, same seed).
        AssertSameAtoms(expected, Atoms(Evaluator.Run(ast, syncOperations, null, Seed, CancellationToken.None), static value => value));

        // The async twin path, suspended twice mid-run.
        var pending = Evaluator.RunAsync(ast, asyncOperations, null, Seed, CancellationToken.None);
        await ReleasePauses(pending, pause, first: 0);
        var suspended = await AsyncEvaluationHarness.Complete(new ValueTask<EvalResult<Result>>(pending));
        Assert.Equal(2, pause.Calls);
        AssertSameAtoms(expected, Atoms(suspended, static value => value));

        // The engine's async surface with RunOptions: same stream.
        var enginePause = new HoldingPause(2);
        var engineOperations = HostOperations.Create(HostOperation.CreateAsync("Pause", enginePause.InvokeAsync, "echo"));
        var enginePending = KatLangEngine.RunAsync(program, new RunOptions { HostOperations = engineOperations, RandomSeed = Seed });
        await ReleasePauses(enginePending, enginePause, first: 0);
        var engine = await AsyncEvaluationHarness.Complete(new ValueTask<RunResult>(enginePending));
        AssertSameAtoms(expected, Assert.IsType<RunResult.Success>(engine).Atoms);
        Assert.Equal(2, enginePause.Calls);
    }

    // ── Async zero-argument property cache seam ───────────────────────────────

    [Theory]
    [InlineData(1)] // miss, after an earlier output draw
    [InlineData(2)] // hit, after the cached property has drawn
    public async Task SuspendingPropertyCache_KeepsTheCacheLawAndTheStream(int holdAtAccess)
    {
        const string program = R + "A = R()\nR(), A, A, A(), R()";
        var d = Draws(4);
        Decimal128[] expected = [d[0], d[1], d[1], d[2], d[3]];
        var ast = Program(program);

        var syncBaseline = Evaluator.RunCounted(ast, new RunScopedZeroArgPropertyResultCache(), randomSeed: Seed);
        AssertSameAtoms(expected, Atoms(syncBaseline, static counted => counted.Value));

        var cache = new HoldingAsyncZeroArgPropertyResultCache(holdAtAccess);
        var pending = Evaluator.RunCountedAsync(ast, cache, randomSeed: Seed);
        try
        {
            await cache.Reached.WaitAsync(TimeSpan.FromSeconds(45));
            Assert.False(pending.IsCompleted);
            Assert.Equal(holdAtAccess, cache.AsyncAccesses);
        }
        finally
        {
            cache.Release();
        }
        var twin = await AsyncEvaluationHarness.Complete(pending);
        Assert.Equal(2, cache.AsyncAccesses);
        AssertSameAtoms(expected, Atoms(twin, static counted => counted.Value));
    }

    // ── Deferred module regions ───────────────────────────────────────────────

    private const string ModuleUrl = "https://katlang.org/seed/deferred.kat";

    private sealed class CountingDownloader(bool hold = false)
    {
        private readonly TaskCompletionSource _reached = new(TaskCreationOptions.RunContinuationsAsynchronously);
        private readonly TaskCompletionSource<string> _gate = new(TaskCreationOptions.RunContinuationsAsynchronously);

        public int Fetches { get; private set; }
        public Task Reached => _reached.Task;
        public void Release() => _gate.TrySetResult("public Base = 1000");

        public ValueTask<string> DownloadAsync(string url, CancellationToken cancellationToken)
        {
            Assert.Equal(ModuleUrl, url);
            Fetches++;
            _reached.TrySetResult();
            return hold ? new(_gate.Task) : ValueTask.FromResult("public Base = 1000");
        }
    }

    [Fact]
    public async Task DeferredModuleRegion_MaterializesWithoutTouchingTheStream_AndMatchesTheEagerRoute()
    {
        // The module dependency is owned by the selected branch body alone, so it is a
        // deferred region materialized DURING evaluation, between the run's draws.
        var deferredSource =
            R +
            $"F(0) = {{ open '{ModuleUrl}'\n    Base + R() }}\n" +
            "F(n) = R() * 0 - 1\n" +
            "R(), F(0), R()";
        var eagerSource =
            $"open '{ModuleUrl}'\n" +
            R +
            "F(0) = Base + R()\n" +
            "F(n) = R() * 0 - 1\n" +
            "R(), F(0), R()";
        var d = Draws(3);
        Decimal128[] expected = [d[0], D(1000) + d[1], d[2]];

        var deferredDownloads = new CountingDownloader(hold: true);
        var deferred = await Parser.ParseAsync(deferredSource, new RunOptions { DownloadCode = deferredDownloads.DownloadAsync });
        Assert.False(deferred.HasErrors, string.Join(Environment.NewLine, deferred.Diagnostics));
        var deferredAst = new Expr.AlgorithmExpr(deferred.Root);
        Assert.True(DeferredModuleRegion.RequiresAsyncEvaluation(deferredAst));
        Assert.Equal(0, deferredDownloads.Fetches);
        // Genuinely deferred: the synchronous family cannot even start it.
        Assert.Throws<InvalidOperationException>(() => Evaluator.Run(deferredAst, null, Seed, CancellationToken.None));

        var deferredPending = Evaluator.RunAsync(deferredAst, null, Seed, CancellationToken.None);
        try
        {
            await deferredDownloads.Reached.WaitAsync(TimeSpan.FromSeconds(45));
            Assert.False(deferredPending.IsCompleted);
            Assert.Equal(1, deferredDownloads.Fetches);
        }
        finally
        {
            deferredDownloads.Release();
        }
        var deferredResult = await AsyncEvaluationHarness.Complete(new ValueTask<EvalResult<Result>>(deferredPending));
        Assert.Equal(1, deferredDownloads.Fetches);
        AssertSameAtoms(expected, Atoms(deferredResult, static value => value));

        var eagerDownloads = new CountingDownloader();
        var eager = await Parser.ParseAsync(eagerSource, new RunOptions { DownloadCode = eagerDownloads.DownloadAsync });
        Assert.False(eager.HasErrors, string.Join(Environment.NewLine, eager.Diagnostics));
        Assert.Equal(1, eagerDownloads.Fetches);
        var eagerAst = new Expr.AlgorithmExpr(eager.Root);
        Assert.False(DeferredModuleRegion.RequiresAsyncEvaluation(eagerAst));
        AssertSameAtoms(expected, Atoms(Evaluator.Run(eagerAst, null, Seed, CancellationToken.None), static value => value));

        // Through the engine, deferred and eager routes agree too, and a second run of
        // the same parse (module already materialized) replays the same stream.
        var engineOptions = new RunOptions { DownloadCode = new CountingDownloader().DownloadAsync, RandomSeed = Seed };
        var engineDeferred = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(deferredSource, engineOptions));
        var engineEager = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(eagerSource, engineOptions));
        AssertSameAtoms(expected, engineDeferred.Atoms);
        AssertSameAtoms(expected, engineEager.Atoms);
        var again = await AsyncEvaluationHarness.Complete(
            new ValueTask<EvalResult<Result>>(Evaluator.RunAsync(deferredAst, null, Seed, CancellationToken.None)));
        Assert.Equal(1, deferredDownloads.Fetches);
        AssertSameAtoms(expected, Atoms(again, static value => value));
    }

    [Fact]
    public async Task UnselectedDeferredBranch_NeitherFetchesNorDraws()
    {
        var source =
            R +
            $"F(0) = {{ open '{ModuleUrl}'\n    Base + R() }}\n" +
            "F(n) = R()\n" +
            "F(1), R()";
        var downloads = new CountingDownloader();
        var parsed = await Parser.ParseAsync(source, new RunOptions { DownloadCode = downloads.DownloadAsync });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
        var d = Draws(2);

        var result = await AsyncEvaluationHarness.Complete(
            new ValueTask<EvalResult<Result>>(Evaluator.RunAsync(new Expr.AlgorithmExpr(parsed.Root), null, Seed, CancellationToken.None)));

        Assert.Equal(0, downloads.Fetches);
        AssertSameAtoms([d[0], d[1]], Atoms(result, static value => value));
    }
}
