using System.Numerics;
using System.Threading.Tasks.Sources;
using KatLang.Evaluation;

namespace KatLang.Tests;

/// <summary>
/// Resource/cancellation boundary audit F2 and F5 (November 2026): evaluation cancellation
/// reaches a deferred materialization that runs INLINE — on a consumer's own stack, because
/// nothing suspended — a second consumer never blocks on the region's run lock, and a host
/// token callback that throws never replaces a consumer's cancellation. The synchronous-
/// completion contract and resumption placement are unchanged.
///
/// <para>Every downloader is deterministic and in-memory; a consumer that blocks inline runs on
/// its own thread (<see cref="Task.Run(Func{Task})"/>), and every wait is bounded by
/// <see cref="HangGuard"/>, a hang guard and never a latency claim. Tests assert outcomes, token
/// identity, and observed state, never elapsed time. Host-only: Lean has no external modules.</para>
/// </summary>
public class DeferredMaterializationCancellationTests
{
    private const string ModuleA = "https://katlang.org/lazy/a.kat";
    private const string ModuleSource = "public V = 7";
    private const string Program = $"F(0) = 0\nF(1) = {{\n    N = load('{ModuleA}')\n    N.V\n}}\nF(1)";

    private static readonly TimeSpan HangGuard = TimeSpan.FromSeconds(30);

    private static DeferredModuleRegion RegionOf(Algorithm root, string family = "F", int branch = 1)
    {
        var conditional = Assert.IsType<Algorithm.Conditional>(root.Properties.Single(property => property.Name == family).Value);
        var region = conditional.Branches[branch].Body.DeferredRegion;
        Assert.NotNull(region);
        return region;
    }

    private static Task<EvalResult<IReadOnlyList<Decimal128>>> RunFlat(Algorithm root, CancellationToken cancellationToken = default)
        => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), limits: null, cancellationToken);

    private static void AssertValue(EvalResult<IReadOnlyList<Decimal128>> result, int expected = 7)
    {
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : "");
        Assert.Equal(new[] { (Decimal128)expected }, result.Value);
    }

    private static async Task WaitUntil(Func<bool> condition, string what)
    {
        var deadline = DateTime.UtcNow + HangGuard;
        while (!condition())
        {
            if (DateTime.UtcNow > deadline)
                Assert.Fail($"hang guard: {what}");
            await Task.Delay(1);
        }
    }

    private static async Task AssertGateFree(DeferredModuleRegion region)
    {
        // The abandoned work may still be unwinding on another thread; the gate turn it held is
        // released exactly once, so acquiring it (bounded) proves it is free.
        await region.Loader.MaterializationGate.WaitAsync().WaitAsync(HangGuard);
        region.Loader.MaterializationGate.Release();
        Assert.Equal(1, region.Loader.MaterializationGate.CurrentCount);
    }

    // ── 1. Inline download, evaluation cancelled ────────────────────────────

    [Fact]
    public async Task InlineDownload_EvaluationCancelled_ReachesTheDownloaderToken_AndARetrySucceeds()
    {
        using var started = new ManualResetEventSlim();
        var calls = 0;
        var sawCancellation = false;
        var options = new RunOptions
        {
            DownloadCode = (_, token) =>
            {
                if (Interlocked.Increment(ref calls) == 1)
                {
                    // Synchronous and token-honouring: the whole run is inline on the consumer's thread.
                    started.Set();
                    sawCancellation = token.WaitHandle.WaitOne(HangGuard);
                    token.ThrowIfCancellationRequested();
                }
                return ValueTask.FromResult(ModuleSource);
            },
        };
        var root = (await SourceProvenance.ParseValidAsync(Program, options)).Root;
        var region = RegionOf(root);
        using var cancellation = new CancellationTokenSource();

        var run = Task.Run(() => RunFlat(root, cancellation.Token));
        Assert.True(started.Wait(HangGuard), "hang guard: download never started");
        cancellation.Cancel();

        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.WaitAsync(HangGuard));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.True(sawCancellation, "the inline downloader's token was never cancelled");
        Assert.False(region.IsMaterialized);
        Assert.Equal(1, region.MaterializationAttempts);
        await AssertGateFree(region);
        Assert.Equal(0, region.Loader.InProgressModuleCount);

        AssertValue(await RunFlat(root).WaitAsync(HangGuard));
        Assert.Equal(2, region.MaterializationAttempts);
        Assert.Equal(2, calls);
    }

    // ── 2. A joiner leaves while the starter runs inline ────────────────────

    [Fact]
    public async Task Joiner_CancelledWhileTheStarterRunsInline_LeavesWithItsOwnToken_AndTheStarterFinishes()
    {
        using var started = new ManualResetEventSlim();
        using var release = new ManualResetEventSlim();
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) =>
            {
                // Ignores its token: only the release ends the inline segment.
                Interlocked.Increment(ref calls);
                started.Set();
                Assert.True(release.Wait(HangGuard));
                return ValueTask.FromResult(ModuleSource);
            },
        };
        var root = (await SourceProvenance.ParseValidAsync(Program, options)).Root;
        var region = RegionOf(root);
        using var joinerCancellation = new CancellationTokenSource();
        Task<EvalResult<IReadOnlyList<Decimal128>>> starter;
        try
        {
            starter = Task.Run(() => RunFlat(root));
            Assert.True(started.Wait(HangGuard), "hang guard: download never started");
            var joiner = Task.Run(() => RunFlat(root, joinerCancellation.Token));
            // The joiner is counted on the starter's run — never blocked on the run lock.
            await WaitUntil(() => region.InFlightConsumers == 2, "the joiner never joined the in-flight run");

            joinerCancellation.Cancel();
            var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => joiner.WaitAsync(HangGuard));
            Assert.Equal(joinerCancellation.Token, error.CancellationToken);
            Assert.False(starter.IsCompleted, "the starter's inline segment was released early");
            Assert.Equal(1, region.InFlightConsumers);
        }
        finally
        {
            release.Set();
        }

        AssertValue(await starter.WaitAsync(HangGuard));
        Assert.True(region.IsMaterialized);
        Assert.Equal(1, region.MaterializationAttempts);
        Assert.Equal(1, calls);
    }

    // ── 3. Inline compile, evaluation cancelled ─────────────────────────────

    // The exposure pass reads an enclosing level's summaries through TryGetValue when a deferred
    // body's property resolves a name declared at that level (`Local = Root + 1` below), which is
    // where this gate holds the compile (the same hook as BranchLazyModuleLoadingTests').
    private sealed class GatedSummaries(
        IReadOnlyDictionary<string, RequirementSet> inner,
        Action onFirstLookup) : IReadOnlyDictionary<string, RequirementSet>
    {
        private Action? _onFirstLookup = onFirstLookup;

        public RequirementSet this[string key] => inner[key];
        public IEnumerable<string> Keys => inner.Keys;
        public IEnumerable<RequirementSet> Values => inner.Values;
        public int Count => inner.Count;
        public bool ContainsKey(string key) => inner.ContainsKey(key);
        public bool TryGetValue(string key, out RequirementSet value)
        {
            Interlocked.Exchange(ref _onFirstLookup, null)?.Invoke();
            return inner.TryGetValue(key, out value!);
        }

        public IEnumerator<KeyValuePair<string, RequirementSet>> GetEnumerator() => inner.GetEnumerator();

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    [Fact]
    public async Task InlineCompile_EvaluationCancelled_PublishesNothing_AndARetrySucceeds()
    {
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) =>
            {
                Interlocked.Increment(ref calls);
                return ValueTask.FromResult("public A = 1");
            },
        };
        var root = (await SourceProvenance.ParseValidAsync(
            $"Root = 1\nF(0) = {{\n    open '{ModuleA}'\n    Local = Root + 1\n    A + Local\n}}\nF(1) = 0\nF(0)", options)).Root;
        var original = RegionOf(root, "F", 0);
        using var entered = new ManualResetEventSlim();
        using var release = new ManualResetEventSlim();
        using var cancellation = new CancellationTokenSource();
        PropertyExposureResolver.SummaryScope GateDeclaringLevel(PropertyExposureResolver.SummaryScope scope)
            => new(scope.Parent is null ? null : GateDeclaringLevel(scope.Parent), scope.PropertyScope,
                scope.PropertyScope.TryLookupOwnProperty("Root") is not null
                    ? new GatedSummaries(scope.Summaries, () =>
                    {
                        entered.Set();
                        Assert.True(release.Wait(HangGuard));
                    })
                    : scope.Summaries,
                scope.Parameters, scope.Algorithm);
        var region = original.WithExposure(new PropertyExposureResolver.DeferredBranchContext(GateDeclaringLevel(original.Exposure!.Scope)));

        // The download completes synchronously, so the compile runs inline on this consumer's thread.
        var pending = Task.Run(() => region.MaterializeAsync(cancellation.Token).AsTask());
        try
        {
            Assert.True(entered.Wait(HangGuard), "hang guard: the compile never reached the gated pass");
            cancellation.Cancel();
        }
        finally
        {
            release.Set();
        }

        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => pending.WaitAsync(HangGuard));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.False(region.IsMaterialized);
        Assert.Equal(1, region.MaterializationAttempts);
        await AssertGateFree(region);

        Assert.False((await region.MaterializeAsync(CancellationToken.None).AsTask().WaitAsync(HangGuard)).IsError);
        Assert.True(region.IsMaterialized);
        Assert.Equal(2, region.MaterializationAttempts);
        Assert.Equal(1, calls);
    }

    // ── 4–5. F5: a throwing downloader callback ─────────────────────────────

    [Fact]
    public async Task ThrowingDownloaderCallback_WhileASuspendedLastConsumerLeaves_KeepsTheConsumersCancellation()
    {
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = async (_, token) =>
            {
                if (Interlocked.Increment(ref calls) > 1)
                    return ModuleSource;
                using var registration = token.Register(() => throw new InvalidOperationException("host callback failed"));
                entered.TrySetResult();
                await Task.Delay(Timeout.Infinite, token);
                return ModuleSource;
            },
        };
        var root = (await SourceProvenance.ParseValidAsync(Program, options)).Root;
        var region = RegionOf(root);
        using var cancellation = new CancellationTokenSource();

        var run = RunFlat(root, cancellation.Token);
        await entered.Task.WaitAsync(HangGuard);
        cancellation.Cancel();

        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.WaitAsync(HangGuard));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.False(region.IsMaterialized);
        await AssertGateFree(region);
        Assert.Equal(0, region.Loader.InProgressModuleCount);
        await WaitUntil(() => region.InFlightConsumers == 0, "the abandoned run never finished");

        AssertValue(await RunFlat(root).WaitAsync(HangGuard));
        Assert.Equal(2, calls);
    }

    [Fact]
    public async Task ThrowingDownloaderCallback_WhenTheInlineStartersCancellationLeaves_HostCancelReturnsNormally()
    {
        using var started = new ManualResetEventSlim();
        using var evaluation = new CancellationTokenSource();
        var sawCancellation = false;
        var options = new RunOptions
        {
            DownloadCode = (_, token) =>
            {
                using var registration = token.Register(() => throw new InvalidOperationException("host callback failed"));
                started.Set();
                sawCancellation = token.WaitHandle.WaitOne(HangGuard);
                token.ThrowIfCancellationRequested();
                return ValueTask.FromResult(ModuleSource);
            },
            EvaluationCancellationToken = evaluation.Token,
        };

        var run = Task.Run(() => KatLangEngine.RunAsync(Program, options));
        Assert.True(started.Wait(HangGuard), "hang guard: download never started");
        // The leave runs inside this Cancel() (the evaluation token's registration); the run's
        // cancellation reaches the downloader's throwing callback, which must stay contained.
        var hostCancel = Record.Exception(evaluation.Cancel);
        Assert.Null(hostCancel);

        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.WaitAsync(HangGuard));
        Assert.Equal(evaluation.Token, error.CancellationToken);
        Assert.True(sawCancellation, "the inline downloader's token was never cancelled");
    }

    // ── 6. Synchronous completion ───────────────────────────────────────────

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task SynchronousDownloaderOrCachedModule_CompletesTheRunSynchronously(bool cached)
    {
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) =>
            {
                Interlocked.Increment(ref calls);
                return ValueTask.FromResult(ModuleSource);
            },
        };
        // Cached: an eager load of the same module fills the loader's cache before selection.
        var source = cached ? $"Eager = load('{ModuleA}')\n" + Program : Program;

        var engine = KatLangEngine.RunAsync(source, options);
        Assert.True(engine.IsCompleted, "KatLangEngine.RunAsync did not complete synchronously");
        var expected = Assert.IsType<RunResult.Success>(KatLangEngine.Run("7"));
        Assert.Equal(expected.Value, Assert.IsType<RunResult.Success>(await engine).Value, Result.ValueComparer);

        var root = (await SourceProvenance.ParseValidAsync(source, options)).Root;
        var callsBeforeSelection = calls;
        var flat = RunFlat(root);
        Assert.True(flat.IsCompleted, "Evaluator.RunFlatAsync did not complete synchronously");
        AssertValue(await flat);
        Assert.Equal(1, RegionOf(root).MaterializationAttempts);
        // A cached module is not fetched again by the selection.
        Assert.Equal(cached ? callsBeforeSelection : callsBeforeSelection + 1, calls);
    }

    // ── 7. Resumption placement ─────────────────────────────────────────────

    /// <summary>
    /// A download that genuinely suspends and reports the moment its awaiter attached, so the
    /// completing thread starts only after the evaluation is suspended on it. Continuations run
    /// inline on the completing thread (no asynchronous-continuation option).
    /// </summary>
    private sealed class SuspendingDownload : IValueTaskSource<string>
    {
        private ManualResetValueTaskSourceCore<string> _core;

        public ManualResetEventSlim Awaited { get; } = new();

        public ValueTask<string> Task => new(this, _core.Version);

        public void Complete(string source) => _core.SetResult(source);

        public string GetResult(short token) => _core.GetResult(token);

        public ValueTaskSourceStatus GetStatus(short token) => _core.GetStatus(token);

        public void OnCompleted(Action<object?> continuation, object? state, short token, ValueTaskSourceOnCompletedFlags flags)
        {
            _core.OnCompleted(continuation, state, token, flags);
            Awaited.Set();
        }
    }

    [Fact]
    public async Task Starter_AfterAGenuineSuspension_ResumesOnTheThreadThatCompletedTheDownload()
    {
        var download = new SuspendingDownload();
        var resumedOn = 0;
        var hosts = HostOperations.Create(HostOperation.Create("Where", (_, _) =>
        {
            resumedOn = Environment.CurrentManagedThreadId;
            return new Result.Atom(1);
        }));
        var source = $"F(0) = 0\nF(1) = {{\n    N = load('{ModuleA}')\n    N.V + Where()\n}}\nF(1)";
        var options = new RunOptions { HostOperations = hosts, DownloadCode = (_, _) => download.Task };
        var root = (await SourceProvenance.ParseValidAsync(source, options)).Root;

        // Started off the test's synchronization context, so placement belongs to the awaitable alone.
        // Return the pending task inside a value so Task.Run does not unwrap it. Once this
        // worker returns, the entire evaluation has attached its awaits, rather than just
        // the downloader's awaiter: completing it earlier can race the starter's unwind.
        var (run, suspended) = await Task.Run(() =>
        {
            var pending = Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), hosts, null, null, CancellationToken.None);
            return (pending, !pending.IsCompleted);
        }).WaitAsync(HangGuard);
        Assert.True(suspended, "the evaluation did not genuinely suspend");
        Assert.True(download.Awaited.Wait(HangGuard), "hang guard: the download never suspended");
        var completingThread = 0;
        var finishedBeforeTheThreadReturned = false;
        var thread = new Thread(() =>
        {
            completingThread = Environment.CurrentManagedThreadId;
            download.Complete(ModuleSource);
            finishedBeforeTheThreadReturned = resumedOn != 0;
        });
        thread.Start();
        Assert.True(thread.Join(HangGuard), "hang guard: the completing thread never returned");

        AssertValue(await run.WaitAsync(HangGuard), 8);
        Assert.Equal(completingThread, resumedOn);
        Assert.True(finishedBeforeTheThreadReturned);
        download.Awaited.Dispose();
    }

    // ── 8. Residual: the inline starter is cancelled while others wait ──────

    [Fact]
    public async Task InlineStarter_CancelledWhileAJoinerWaits_KeepsTheWorkForTheJoiner_AndReturnsWithItsOwnToken()
    {
        using var started = new ManualResetEventSlim();
        using var release = new ManualResetEventSlim();
        CancellationToken downloadToken = default;
        var options = new RunOptions
        {
            DownloadCode = (_, token) =>
            {
                downloadToken = token;
                started.Set();
                Assert.True(release.Wait(HangGuard));
                return ValueTask.FromResult(ModuleSource);
            },
        };
        var root = (await SourceProvenance.ParseValidAsync(Program, options)).Root;
        var region = RegionOf(root);
        using var starterCancellation = new CancellationTokenSource();
        Task<EvalResult<IReadOnlyList<Decimal128>>> starter, joiner;
        try
        {
            starter = Task.Run(() => RunFlat(root, starterCancellation.Token));
            Assert.True(started.Wait(HangGuard), "hang guard: download never started");
            joiner = Task.Run(() => RunFlat(root));
            await WaitUntil(() => region.InFlightConsumers == 2, "the joiner never joined the in-flight run");

            starterCancellation.Cancel();
            // The starter's leave counted at once, but the joiner still needs the work.
            Assert.Equal(1, region.InFlightConsumers);
            Assert.False(downloadToken.IsCancellationRequested, "the work was cancelled while a consumer still waits");
            Assert.False(joiner.IsCompleted);
        }
        finally
        {
            release.Set();
        }

        AssertValue(await joiner.WaitAsync(HangGuard));
        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => starter.WaitAsync(HangGuard));
        Assert.Equal(starterCancellation.Token, error.CancellationToken);
        Assert.True(region.IsMaterialized);
        Assert.Equal(1, region.MaterializationAttempts);
    }

    // ── 9. Same-tree reentrancy from a synchronous downloader ───────────────

    [Fact]
    public async Task SynchronousDownloader_EvaluatingTheSameTree_JoinsItsOwnRun_AndEndsWithItsOwnToken()
    {
        Algorithm? root = null;
        Exception? nested = null;
        CancellationToken nestedToken = default;
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) =>
            {
                Interlocked.Increment(ref calls);
                // Documented as unsupported (RunOptions.DownloadCode): the nested evaluation joins
                // the materialization this downloader serves and ends only through its own token.
                using var limit = new CancellationTokenSource(TimeSpan.FromMilliseconds(50));
                nestedToken = limit.Token;
                nested = Record.Exception(() => RunFlat(root!, limit.Token).GetAwaiter().GetResult());
                return ValueTask.FromResult(ModuleSource);
            },
        };
        root = (await SourceProvenance.ParseValidAsync(Program, options)).Root;
        var region = RegionOf(root);

        AssertValue(await Task.Run(() => RunFlat(root)).WaitAsync(HangGuard));
        var cancelled = Assert.IsAssignableFrom<OperationCanceledException>(nested);
        Assert.Equal(nestedToken, cancelled.CancellationToken);
        Assert.Equal(1, calls);
        Assert.Equal(1, region.MaterializationAttempts);
    }

    // ── 10. Seeded stress ───────────────────────────────────────────────────

    private const string StressCallbackFailure = "deferred-materialization stress callback failure";

    [Fact]
    public async Task SeededStress_CompetingConsumers_EndWithTheValueOrTheirOwnToken_AndLeaveTheRegionClean()
    {
        var unobserved = new List<string>();
        EventHandler<UnobservedTaskExceptionEventArgs> onUnobserved = (_, args) =>
        {
            // Other test classes run in parallel in this process: count only this test's faults.
            var text = args.Exception.ToString();
            if (text.Contains(StressCallbackFailure, StringComparison.Ordinal) || text.Contains(nameof(DeferredModuleRegion), StringComparison.Ordinal))
                lock (unobserved) unobserved.Add(text);
        };
        TaskScheduler.UnobservedTaskException += onUnobserved;
        var violations = new List<string>();
        var outcomes = new Dictionary<string, int>(StringComparer.Ordinal);
        try
        {
            for (var seed = 1; seed <= 300 && violations.Count == 0; seed++)
                await StressTrial(seed, violations, outcomes);

            GC.Collect();
            GC.WaitForPendingFinalizers();
            GC.Collect();
            GC.WaitForPendingFinalizers();
        }
        finally
        {
            TaskScheduler.UnobservedTaskException -= onUnobserved;
        }

        Assert.True(violations.Count == 0, string.Join(Environment.NewLine, violations));
        Assert.True(unobserved.Count == 0, string.Join(Environment.NewLine, unobserved));
        Assert.True(outcomes.GetValueOrDefault("value") > 0, "no consumer ever received the value");
        Assert.True(outcomes.GetValueOrDefault("cancelled") > 0, "no consumer was ever cancelled");
    }

    private static async Task StressTrial(int seed, List<string> violations, Dictionary<string, int> outcomes)
    {
        var random = new Random(seed);
        int Next(int max) { lock (random) return random.Next(max); }
        void Violation(string what) { lock (violations) violations.Add($"seed {seed}: {what}"); }
        void Count(string key) { lock (outcomes) outcomes[key] = outcomes.GetValueOrDefault(key) + 1; }

        // 0: synchronous; 1: synchronous, blocks honouring its token; 2: delays; 3: yields.
        var mode = Next(4);
        var throwing = Next(4) == 0;
        var options = new RunOptions
        {
            DownloadCode = (_, token) =>
            {
                if (mode >= 2)
                    return SuspendingStressDownload(token, mode == 2 ? Next(4) : -1, throwing);
                using var registration = throwing
                    ? token.Register(static () => throw new InvalidOperationException(StressCallbackFailure))
                    : default;
                if (mode == 1)
                {
                    token.WaitHandle.WaitOne(Next(6));
                    token.ThrowIfCancellationRequested();
                }
                return ValueTask.FromResult(ModuleSource);
            },
        };
        var root = (await SourceProvenance.ParseValidAsync(Program, options)).Root;
        var region = RegionOf(root);
        var consumerCount = 2 + Next(3);
        var consumers = new List<Task>();
        var sources = new List<CancellationTokenSource>();
        for (var index = 0; index < consumerCount; index++)
        {
            var cancellation = new CancellationTokenSource();
            sources.Add(cancellation);
            var cancelMode = Next(3);
            var cancelAfter = Next(6);
            consumers.Add(Task.Run(async () =>
            {
                try
                {
                    var result = await RunFlat(root, cancellation.Token);
                    if (result.IsError) Violation("error " + result.Error);
                    else if (result.Value.Count != 1 || result.Value[0] != 7) Violation("wrong value");
                    else Count("value");
                }
                catch (OperationCanceledException error)
                {
                    Count("cancelled");
                    if (error.CancellationToken != cancellation.Token) Violation("foreign cancellation token");
                }
                catch (Exception error)
                {
                    Violation($"escaped {error.GetType().Name}: {error.Message}");
                }
            }));
            if (cancelMode == 1)
                cancellation.CancelAfter(cancelAfter);
            else if (cancelMode == 2)
            {
                consumers.Add(Task.Run(() =>
                {
                    try { cancellation.Cancel(); }
                    catch (Exception error) { Violation($"host Cancel() threw {error.GetType().Name}"); }
                }));
            }
        }

        try
        {
            await Task.WhenAll(consumers).WaitAsync(HangGuard);
        }
        catch (TimeoutException)
        {
            Violation("hang guard: consumers never finished");
            return;
        }

        await AssertGateFree(region);
        if (region.Loader.InProgressModuleCount != 0) Violation("in-progress module leak");
        try
        {
            var final = await RunFlat(root).WaitAsync(HangGuard);
            if (final.IsError || final.Value[0] != 7) Violation("the next selection did not produce the value");
        }
        catch (Exception error)
        {
            Violation($"the next selection threw {error.GetType().Name}");
        }
        if (!region.IsMaterialized) Violation("the next selection did not materialize the region");
        foreach (var cancellation in sources)
            cancellation.Dispose();
    }

    private static async ValueTask<string> SuspendingStressDownload(CancellationToken token, int delay, bool throwing)
    {
        using var registration = throwing
            ? token.Register(static () => throw new InvalidOperationException(StressCallbackFailure))
            : default;
        if (delay < 0)
            await Task.Yield();
        else
            await Task.Delay(delay, token);
        return ModuleSource;
    }
}
