using System.Numerics;
using System.Threading.Tasks.Sources;
using KatLang.Evaluation;

namespace KatLang.Tests;

/// <summary>
/// Resource/cancellation boundary audit F2 and F5 (November 2026): evaluation cancellation
/// reaches a deferred materialization that runs INLINE — on a consumer's own stack, because
/// nothing suspended — a second consumer never blocks on the region's run lock, and a host
/// token callback that throws never replaces a consumer's cancellation. The synchronous-
/// completion contract and resumption placement are unchanged. B15: the region's abandonment
/// record is an exact count plus a bounded failure summary. B16 (host contract): a selection
/// of a not-yet-loaded branch made in the execution context of a load in progress of the same
/// program is refused at once as a possible load cycle, whether or not the downloader waits.
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

    // B15: what the region recorded about abandonment. A run is abandoned only when its LAST
    // consumer leaves before completion; the record is settled once that leave's Cancel()
    // returned, which is inside the test's own Cancel() (the leave is a token registration).
    private static void AssertNoAbandonment(DeferredModuleRegion region)
    {
        Assert.Equal(0, region.AbandonedRuns);
        Assert.Null(region.LastAbandonmentFailure);
    }

    private static void AssertAbandonedCleanly(DeferredModuleRegion region, int runs = 1)
    {
        Assert.Equal(runs, region.AbandonedRuns);
        Assert.Null(region.LastAbandonmentFailure);
    }

    private static void AssertAbandonedWithCallbackFailure(DeferredModuleRegion region, string message)
    {
        Assert.Equal(1, region.AbandonedRuns);
        // CancellationTokenSource.Cancel() aggregates callback failures, once per linked level;
        // the record keeps the flattened count and the first failure's type and message only.
        var failure = Assert.IsType<DeferredModuleRegion.AbandonmentFailureSummary>(region.LastAbandonmentFailure);
        Assert.Equal(typeof(AggregateException).FullName, failure.FailureType);
        Assert.Equal(1, failure.CallbackFailureCount);
        Assert.Equal(typeof(InvalidOperationException).FullName, failure.FirstCallbackFailureType);
        Assert.Equal(message, failure.FirstCallbackFailureMessage);
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
        // The only consumer's leave abandoned the run, and its cancellation completed normally.
        AssertAbandonedCleanly(region);
        await AssertGateFree(region);
        Assert.Equal(0, region.Loader.InProgressModuleCount);

        AssertValue(await RunFlat(root).WaitAsync(HangGuard));
        Assert.Equal(2, region.MaterializationAttempts);
        Assert.Equal(2, calls);
        // A successful retry abandons nothing.
        AssertAbandonedCleanly(region);
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
            // Not the last consumer: nothing was abandoned.
            AssertNoAbandonment(region);
        }
        finally
        {
            release.Set();
        }

        AssertValue(await starter.WaitAsync(HangGuard));
        Assert.True(region.IsMaterialized);
        Assert.Equal(1, region.MaterializationAttempts);
        Assert.Equal(1, calls);
        AssertNoAbandonment(region);
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
        AssertAbandonedCleanly(region);
        await AssertGateFree(region);

        Assert.False((await region.MaterializeAsync(CancellationToken.None).AsTask().WaitAsync(HangGuard)).IsError);
        Assert.True(region.IsMaterialized);
        Assert.Equal(2, region.MaterializationAttempts);
        Assert.Equal(1, calls);
    }

    // ── 4–5. F5: a throwing downloader callback ─────────────────────────────

    /// <summary>
    /// Keeps a downloader's throwing token registration alive until the test ends. A downloader
    /// that disposed it on its own exit could race the cancellation it reacts to:
    /// <see cref="CancellationTokenSource.Cancel()"/> sets the token's wait handle before it runs
    /// any callback, and runs callbacks last-registered first (a <see cref="Task.Delay(int, CancellationToken)"/>
    /// awaited after the registration resumes its awaiter inline), so a downloader woken that
    /// way could unregister the throwing callback before it ever ran — and the test would
    /// silently exercise no callback failure at all.
    /// </summary>
    private sealed class HeldRegistrations : IDisposable
    {
        private readonly List<CancellationTokenRegistration> _held = [];

        public void Hold(CancellationTokenRegistration registration)
        {
            lock (_held) _held.Add(registration);
        }

        public void Dispose()
        {
            lock (_held)
            {
                foreach (var registration in _held)
                    registration.Dispose();
                _held.Clear();
            }
        }
    }

    [Fact]
    public async Task ThrowingDownloaderCallback_WhileASuspendedLastConsumerLeaves_KeepsTheConsumersCancellation()
    {
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        using var callbacks = new HeldRegistrations();
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = async (_, token) =>
            {
                if (Interlocked.Increment(ref calls) > 1)
                    return ModuleSource;
                callbacks.Hold(token.Register(() => throw new InvalidOperationException("host callback failed")));
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
        // The callback's failure belongs to the abandoned run: recorded there, and nowhere else.
        AssertAbandonedWithCallbackFailure(region, "host callback failed");

        AssertValue(await RunFlat(root).WaitAsync(HangGuard));
        Assert.Equal(2, calls);
        // The record stays the last abandoned run's; the successful retry abandons nothing.
        AssertAbandonedWithCallbackFailure(region, "host callback failed");
    }

    [Fact]
    public async Task ThrowingDownloaderCallback_WhenTheInlineStartersCancellationLeaves_HostCancelReturnsNormally()
    {
        using var started = new ManualResetEventSlim();
        using var evaluation = new CancellationTokenSource();
        using var callbacks = new HeldRegistrations();
        var sawCancellation = false;
        var options = new RunOptions
        {
            DownloadCode = (_, token) =>
            {
                callbacks.Hold(token.Register(() => throw new InvalidOperationException("host callback failed")));
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

    [Fact]
    public async Task ThrowingDownloaderCallback_WhenTheInlineStartersCancellationLeaves_RecordsTheFailureOnTheAbandonedRun()
    {
        using var started = new ManualResetEventSlim();
        using var evaluation = new CancellationTokenSource();
        using var callbacks = new HeldRegistrations();
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, token) =>
            {
                if (Interlocked.Increment(ref calls) > 1)
                    return ValueTask.FromResult(ModuleSource);
                callbacks.Hold(token.Register(() => throw new InvalidOperationException("host callback failed")));
                started.Set();
                token.WaitHandle.WaitOne(HangGuard);
                token.ThrowIfCancellationRequested();
                return ValueTask.FromResult(ModuleSource);
            },
        };
        var root = (await SourceProvenance.ParseValidAsync(Program, options)).Root;
        var region = RegionOf(root);

        var run = Task.Run(() => RunFlat(root, evaluation.Token));
        Assert.True(started.Wait(HangGuard), "hang guard: download never started");
        // The starter's leave runs inside this Cancel(), while the work runs inline on the
        // starter's own thread: the failure is recorded before Cancel() returns.
        Assert.Null(Record.Exception(evaluation.Cancel));
        AssertAbandonedWithCallbackFailure(region, "host callback failed");

        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.WaitAsync(HangGuard));
        Assert.Equal(evaluation.Token, error.CancellationToken);
        Assert.False(region.IsMaterialized);
        await AssertGateFree(region);

        AssertValue(await RunFlat(root).WaitAsync(HangGuard));
        Assert.Equal(1, region.AbandonedRuns);
    }

    // ── 4b. B15: the abandonment record is a bounded summary ────────────────

    [Fact]
    public void AbandonmentFailureSummary_FlattensTheAggregate_CountsEveryCallbackFailure_AndBoundsTheMessage()
    {
        var longMessage = new string('x', DeferredModuleRegion.AbandonmentFailureSummary.MaxMessageLength + 50);
        // Flatten() lists an aggregate's direct failures before those of nested aggregates.
        var nested = new AggregateException(
            new InvalidOperationException(longMessage),
            new AggregateException(new ArgumentException("second")));

        var summary = DeferredModuleRegion.AbandonmentFailureSummary.Of(nested);

        Assert.Equal(typeof(AggregateException).FullName, summary.FailureType);
        Assert.Equal(2, summary.CallbackFailureCount);
        Assert.Equal(typeof(InvalidOperationException).FullName, summary.FirstCallbackFailureType);
        Assert.Equal(
            new string('x', DeferredModuleRegion.AbandonmentFailureSummary.MaxMessageLength) + "…",
            summary.FirstCallbackFailureMessage);

        var plain = DeferredModuleRegion.AbandonmentFailureSummary.Of(new TimeoutException("plain"));
        Assert.Equal(1, plain.CallbackFailureCount);
        Assert.Equal(typeof(TimeoutException).FullName, plain.FailureType);
        Assert.Equal("plain", plain.FirstCallbackFailureMessage);
    }

    private sealed class UnreadableMessageException(bool throws) : Exception
    {
        public override string Message => throws ? throw new InvalidOperationException("message getter failed") : null!;
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task AbandonmentFailure_WithAnUnreadableCallbackMessage_DoesNotEscapeHostCancellation(bool throws)
    {
        using var callbacks = new HeldRegistrations();
        using var cancellation = new CancellationTokenSource();
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var calls = 0;
        var root = (await SourceProvenance.ParseValidAsync(Program, new RunOptions
        {
            DownloadCode = async (_, token) =>
            {
                if (Interlocked.Increment(ref calls) > 1)
                    return ModuleSource;
                callbacks.Hold(token.Register(() => throw new UnreadableMessageException(throws)));
                entered.TrySetResult();
                await Task.Delay(Timeout.Infinite, token);
                return ModuleSource;
            },
        })).Root;
        var region = RegionOf(root);
        var run = RunFlat(root, cancellation.Token);
        await entered.Task.WaitAsync(HangGuard);
        var escaped = Record.Exception(cancellation.Cancel);
        // Drain the work even when the diagnostic formatter itself regresses.
        var cancelled = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.WaitAsync(HangGuard));
        await AssertGateFree(region);

        Assert.Null(escaped);
        Assert.Equal(cancellation.Token, cancelled.CancellationToken);
        Assert.Equal(1, region.AbandonedRuns);
        var summary = Assert.IsType<DeferredModuleRegion.AbandonmentFailureSummary>(region.LastAbandonmentFailure);
        Assert.Equal(1, summary.CallbackFailureCount);
        Assert.Equal(typeof(UnreadableMessageException).FullName, summary.FirstCallbackFailureType);
        Assert.Equal("callback exception message unavailable", summary.FirstCallbackFailureMessage);
        AssertValue(await RunFlat(root).WaitAsync(HangGuard));
        Assert.Same(summary, region.LastAbandonmentFailure);
    }

    [Fact]
    public async Task EachAbandonmentStartsAFreshRecord_ACleanAbandonmentAfterAFailedOneRecordsNoFailure()
    {
        using var callbacks = new HeldRegistrations();
        var entered = new[]
        {
            new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously),
            new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously),
        };
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = async (_, token) =>
            {
                var call = Interlocked.Increment(ref calls);
                if (call > 2)
                    return ModuleSource;
                // The first abandoned run's cancellation meets a throwing callback; the second's does not.
                if (call == 1)
                    callbacks.Hold(token.Register(() => throw new InvalidOperationException("host callback failed")));
                entered[call - 1].TrySetResult();
                await Task.Delay(Timeout.Infinite, token);
                return ModuleSource;
            },
        };
        var root = (await SourceProvenance.ParseValidAsync(Program, options)).Root;
        var region = RegionOf(root);

        for (var attempt = 0; attempt < 2; attempt++)
        {
            using var cancellation = new CancellationTokenSource();
            var run = RunFlat(root, cancellation.Token);
            await entered[attempt].Task.WaitAsync(HangGuard);
            cancellation.Cancel();
            var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.WaitAsync(HangGuard));
            Assert.Equal(cancellation.Token, error.CancellationToken);
            await WaitUntil(() => region.InFlightConsumers == 0, "the abandoned run never finished");
            if (attempt == 0)
                AssertAbandonedWithCallbackFailure(region, "host callback failed");
        }

        // The second abandonment is the most recent one, and it completed normally.
        AssertAbandonedCleanly(region, runs: 2);
        AssertValue(await RunFlat(root).WaitAsync(HangGuard));
        AssertAbandonedCleanly(region, runs: 2);
    }

    private sealed class RetainedPayloadException(object payload) : InvalidOperationException("host callback failed")
    {
        public object Payload { get; } = payload;
    }

    [Fact]
    public async Task AbandonmentRecord_DoesNotRetainTheCallbacksExceptionGraph_WhileTheRegionLives()
    {
        using var started = new ManualResetEventSlim();
        using var evaluation = new CancellationTokenSource();
        using var callbacks = new HeldRegistrations();
        // Only the callback creates the payload, and only the weak reference sees it from here.
        var payload = new WeakReference<object>(null!);
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, token) =>
            {
                if (Interlocked.Increment(ref calls) > 1)
                    return ValueTask.FromResult(ModuleSource);
                callbacks.Hold(token.Register(() =>
                {
                    var large = new byte[1 << 20];
                    payload.SetTarget(large);
                    throw new RetainedPayloadException(large);
                }));
                started.Set();
                token.WaitHandle.WaitOne(HangGuard);
                token.ThrowIfCancellationRequested();
                return ValueTask.FromResult(ModuleSource);
            },
        };
        var root = (await SourceProvenance.ParseValidAsync(Program, options)).Root;
        var region = RegionOf(root);

        var run = Task.Run(() => RunFlat(root, evaluation.Token));
        Assert.True(started.Wait(HangGuard), "hang guard: download never started");
        Assert.Null(Record.Exception(evaluation.Cancel));
        await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.WaitAsync(HangGuard));
        await AssertGateFree(region);
        await WaitUntil(() => region.InFlightConsumers == 0, "the abandoned run never finished");

        // The record keeps the diagnostic meaning...
        var failure = Assert.IsType<DeferredModuleRegion.AbandonmentFailureSummary>(region.LastAbandonmentFailure);
        Assert.Equal(typeof(RetainedPayloadException).FullName, failure.FirstCallbackFailureType);
        Assert.Equal("host callback failed", failure.FirstCallbackFailureMessage);
        // ...but not the exception, so nothing the host attached to it stays alive with the
        // region (which lives as long as the tree). The registration is released first: the
        // test's own handle on the callback must not be what keeps anything alive.
        callbacks.Dispose();
        await WaitUntil(() =>
        {
            GC.Collect();
            GC.WaitForPendingFinalizers();
            return !payload.TryGetTarget(out _);
        }, "the abandonment record retained the callback failure's exception graph");
        GC.KeepAlive(region);
        GC.KeepAlive(root);
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
        AssertNoAbandonment(RegionOf(root));
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
        // The starter's leave was not the last: nothing was abandoned.
        AssertNoAbandonment(region);
    }

    // ── 9. Reentrant selection from a module downloader (B16) ───────────────
    //
    // Owner decision (Nov 10 2026): fail fast. A downloader that evaluates the program it is
    // loading for, and selects a branch whose modules are not loaded yet, would wait for the
    // download it is serving — the same region's run (whose completion follows the download) or
    // the loader gate that run holds (another region). That selection fails AT ONCE with an
    // ordinary LoadCycle materialization failure, without any token; the outer run, the gate,
    // the cache, and later selections are unaffected. The downloader's wait for the nested
    // evaluation is bounded by HangGuard only as a watchdog: on a regression it returns anyway,
    // so everything unwinds, and the test fails on NestedCompletedInsideTheDownload. Nothing in
    // these tests is cancelled to make a nested evaluation finish. The library cannot see the
    // downloader's wait, so the same refusal is also the host contract for work that nothing
    // waits for (§ 9b; RunOptions.DownloadCode, Reentrancy).

    private const string TwoRegionProgram =
        $"F(0) = 0\nF(1) = {{\n    N = load('{ModuleA}')\n    N.V\n}}\n" +
        $"G(0) = 0\nG(1) = {{\n    M = load('{ModuleB}')\n    M.W\n}}\n" +
        "P(0) = F(1)\nP(1) = G(1)\nP(2) = 5\nP(Which())";

    private const string ModuleB = "https://katlang.org/lazy/b.kat";

    private sealed class ReentrantDownloader
    {
        private readonly ManualResetEventSlim _entered = new();

        public required Func<CancellationToken, Task<EvalResult<IReadOnlyList<Decimal128>>>> Nested { get; init; }

        public CancellationToken NestedToken { get; init; }

        /// <summary>Runs inside the download, before the nested evaluation starts.</summary>
        public Action? BeforeNested { get; init; }

        /// <summary>Runs inside the download, after the nested evaluation ended (or the watchdog fired).</summary>
        public Action? AfterNested { get; init; }

        public CancellationToken DownloaderToken { get; private set; }

        public bool NestedCompletedInsideTheDownload { get; private set; }

        public EvalResult<IReadOnlyList<Decimal128>>? NestedResult { get; private set; }

        public Exception? NestedException { get; private set; }

        public bool DownloaderTokenCancelledOnReturn { get; private set; }

        public int Calls;

        public ValueTask<string> Download(CancellationToken token, string source)
        {
            if (Interlocked.Increment(ref Calls) > 1)
                return ValueTask.FromResult(source);
            DownloaderToken = token;
            BeforeNested?.Invoke();
            var nested = Nested(NestedToken);
            _entered.Set();
            // Watchdog only: a nested evaluation that waits instead of failing is left behind,
            // and ends once this download has returned.
            NestedCompletedInsideTheDownload = ((IAsyncResult)nested).AsyncWaitHandle.WaitOne(HangGuard);
            if (NestedCompletedInsideTheDownload)
            {
                NestedException = Record.Exception(() => NestedResult = nested.GetAwaiter().GetResult());
            }
            AfterNested?.Invoke();
            DownloaderTokenCancelledOnReturn = token.IsCancellationRequested;
            return ValueTask.FromResult(source);
        }

        public void WaitEntered() => Assert.True(_entered.Wait(HangGuard), "hang guard: the downloader never ran");
    }

    private static void AssertReentrantSelectionRejected(EvalResult<IReadOnlyList<Decimal128>>? nested, Exception? escaped)
    {
        Assert.Null(escaped);
        Assert.True(nested.HasValue, "the reentrant selection produced no result");
        var result = nested.Value;
        Assert.True(result.IsError, "the reentrant selection produced a value");
        // Evaluation frames wrap the failure in context; the innermost error is the region's.
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        var failure = Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(error);
        var diagnostic = Assert.Single(failure.Diagnostics);
        Assert.Equal(DiagnosticCode.LoadCycle, diagnostic.Code);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Equal(DeferredModuleRegion.ReentrantMaterializationMessage, diagnostic.Message);
        // Positioned at the branch's own load directive, like the region's other load failures.
        Assert.NotNull(diagnostic.Span);
        // The public classification is the existing load-cycle code, never a cancellation.
        Assert.Equal(KatLangErrorCode.LoadCycle, KatLangError.FromEvalError(result.Error).Code);
    }

    private static void AssertReentrantSelectionRejected(ReentrantDownloader downloader)
    {
        Assert.True(downloader.NestedCompletedInsideTheDownload, "the nested selection waited instead of failing fast");
        AssertReentrantSelectionRejected(downloader.NestedResult, downloader.NestedException);
    }

    public enum NestedThread
    {
        /// <summary>The nested evaluation runs synchronously on the downloader's own thread.</summary>
        DownloaderThread,

        /// <summary>The downloader blocks on <see cref="Task.Run(Func{Task})"/>: another thread, flowed context.</summary>
        TaskRun,
    }

    private static Func<CancellationToken, Task<EvalResult<IReadOnlyList<Decimal128>>>> Nested(
        NestedThread thread, Func<CancellationToken, Task<EvalResult<IReadOnlyList<Decimal128>>>> evaluate)
        => thread == NestedThread.TaskRun ? token => Task.Run(() => evaluate(token)) : evaluate;

    [Theory]
    [InlineData(NestedThread.DownloaderThread)]
    [InlineData(NestedThread.TaskRun)]
    public async Task SameRegionReentry_WithoutAToken_FailsFastWithALoadCycle_AndTheOuterRunPublishes(NestedThread thread)
    {
        Algorithm? root = null;
        DeferredModuleRegion? region = null;
        var consumersDuringTheDownload = -1;
        var downloader = new ReentrantDownloader
        {
            Nested = Nested(thread, token => RunFlat(root!, token)),
            AfterNested = () => consumersDuringTheDownload = region!.InFlightConsumers,
        };
        var options = new RunOptions { DownloadCode = (_, token) => downloader.Download(token, ModuleSource) };
        root = (await SourceProvenance.ParseValidAsync(Program, options)).Root;
        region = RegionOf(root);

        AssertValue(await Task.Run(() => RunFlat(root)).WaitAsync(HangGuard));

        AssertReentrantSelectionRejected(downloader);
        // The rejected selection was never counted on the run it would have waited for.
        Assert.Equal(1, consumersDuringTheDownload);
        Assert.False(downloader.DownloaderTokenCancelledOnReturn);
        Assert.Equal(1, downloader.Calls);
        Assert.Equal(1, region.MaterializationAttempts);
        Assert.True(region.IsMaterialized);
        AssertNoAbandonment(region);
        await AssertGateFree(region);
        Assert.Equal(0, region.Loader.InProgressModuleCount);

        // Recovery: the region is published once, and every later evaluation is served from it.
        AssertValue(await RunFlat(root).WaitAsync(HangGuard));
        Assert.Equal(1, region.MaterializationAttempts);
    }

    [Theory]
    [InlineData(NestedThread.DownloaderThread)]
    [InlineData(NestedThread.TaskRun)]
    public async Task OtherRegionReentry_WithoutAToken_FailsFastWithALoadCycle_InsteadOfWaitingForTheHeldGate(NestedThread thread)
    {
        var which = 0;
        var hosts = HostOperations.Create(HostOperation.Create("Which", (_, _) => new Result.Atom(Volatile.Read(ref which))));
        Algorithm? root = null;
        DeferredModuleRegion? regionG = null;
        var gConsumersDuringTheDownload = -1;
        var downloader = new ReentrantDownloader
        {
            Nested = Nested(thread, token => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root!), hosts, null, null, token)),
            // The nested evaluation selects the OTHER region of the same tree.
            BeforeNested = () => Volatile.Write(ref which, 1),
            AfterNested = () => gConsumersDuringTheDownload = regionG!.InFlightConsumers,
        };
        var options = new RunOptions
        {
            HostOperations = hosts,
            DownloadCode = (url, token) => url == ModuleA
                ? downloader.Download(token, ModuleSource)
                : ValueTask.FromResult("public W = 8"),
        };
        root = (await SourceProvenance.ParseValidAsync(TwoRegionProgram, options)).Root;
        var regionF = RegionOf(root, "F");
        regionG = RegionOf(root, "G");

        AssertValue(await Task.Run(() => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), hosts, null, null, CancellationToken.None))
            .WaitAsync(HangGuard));

        AssertReentrantSelectionRejected(downloader);
        // G's selection never started a run: no consumer, no attempt, no abandonment.
        Assert.Equal(0, gConsumersDuringTheDownload);
        Assert.Equal(0, regionG.MaterializationAttempts);
        Assert.False(regionG.IsMaterialized);
        AssertNoAbandonment(regionG);
        Assert.True(regionF.IsMaterialized);
        AssertNoAbandonment(regionF);
        await AssertGateFree(regionF);

        // Recovery: G is selected again (Which() is now 1) and materializes normally.
        AssertValue(await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), hosts, null, null, CancellationToken.None)
            .WaitAsync(HangGuard), 8);
        Assert.True(regionG.IsMaterialized);
        Assert.Equal(1, regionG.MaterializationAttempts);
    }

    [Fact]
    public async Task SameRegionReentry_FromAnAsynchronousDownloaderContinuation_FailsFast()
    {
        Algorithm? root = null;
        EvalResult<IReadOnlyList<Decimal128>>? nested = null;
        Exception? escaped = null;
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = async (_, _) =>
            {
                if (Interlocked.Increment(ref calls) > 1)
                    return ModuleSource;
                // A genuine suspension first: the nested evaluation runs on a continuation, on
                // whatever thread resumes it, with the downloader's flowed context — and the
                // download's own completion awaits it, which is the cycle.
                await Task.Yield();
                try { nested = await RunFlat(root!).WaitAsync(HangGuard); }
                catch (Exception error) { escaped = error; }
                return ModuleSource;
            },
        };
        root = (await SourceProvenance.ParseValidAsync(Program, options)).Root;
        var region = RegionOf(root);

        AssertValue(await RunFlat(root).WaitAsync(HangGuard));

        AssertReentrantSelectionRejected(nested, escaped);
        Assert.Equal(1, region.MaterializationAttempts);
        AssertNoAbandonment(region);
        await AssertGateFree(region);
    }

    [Fact]
    public async Task Reentry_ByWorkAnEarlierDownloadStarted_WhileALaterDownloadOfTheSameLoadWaitsForIt_FailsFast()
    {
        // The load is in progress for its whole gate turn, not only while one callback runs. This
        // load makes two downloads. The first starts a child with its flowed context and returns
        // at once; the second releases the child and waits for it. The child's selection would
        // wait for the turn, and the turn waits for the second download: a genuine cycle through
        // a callback that has already returned. A turn frame that ended with its own callback
        // would miss it, so this pins the frame's lifetime.
        var source =
            $"F(0) = 0\nF(1) = {{\n    N = load('{ModuleA}')\n    M = load('{ModuleB}')\n    N.V + M.W\n}}\nF(1)";
        var releaseChild = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        Algorithm? root = null;
        Task<EvalResult<IReadOnlyList<Decimal128>>>? child = null;
        var childCompletedInsideTheLaterDownload = false;
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = (url, _) =>
            {
                // Counted by call, so the test does not depend on which module loads first.
                switch (Interlocked.Increment(ref calls))
                {
                    case 1:
                        child = Task.Run(async () =>
                        {
                            await releaseChild.Task;
                            return await RunFlat(root!);
                        });
                        break;
                    case 2:
                        releaseChild.SetResult();
                        // Watchdog only: a child that waits instead of failing is left behind,
                        // and ends once this download has returned.
                        childCompletedInsideTheLaterDownload = ((IAsyncResult)child!).AsyncWaitHandle.WaitOne(HangGuard);
                        break;
                }

                return ValueTask.FromResult(url == ModuleA ? ModuleSource : "public W = 8");
            },
        };
        root = (await SourceProvenance.ParseValidAsync(source, options)).Root;
        var region = RegionOf(root);

        AssertValue(await Task.Run(() => RunFlat(root)).WaitAsync(HangGuard), 15);

        Assert.True(childCompletedInsideTheLaterDownload, "the selection waited for the load whose later download waits for it");
        EvalResult<IReadOnlyList<Decimal128>>? childResult = null;
        var escaped = await Record.ExceptionAsync(async () => childResult = await child!.WaitAsync(HangGuard));
        AssertReentrantSelectionRejected(childResult, escaped);
        // The refused selection downloaded nothing and counted nothing: one attempt, two downloads.
        Assert.Equal(2, calls);
        Assert.Equal(1, region.MaterializationAttempts);
        Assert.True(region.IsMaterialized);
        AssertNoAbandonment(region);
        await AssertGateFree(region);
    }

    public enum NestedCancellation
    {
        /// <summary>A cancellable token nobody cancels: still the load-cycle failure.</summary>
        Uncancelled,

        /// <summary>The nested evaluation's token is already cancelled: its cancellation wins.</summary>
        NestedPreCancelled,

        /// <summary>The host's source-processing token is cancelled first: it wins, for both evaluations.</summary>
        SourceProcessingCancelled,
    }

    [Theory]
    [InlineData(false, NestedCancellation.Uncancelled)]
    [InlineData(false, NestedCancellation.NestedPreCancelled)]
    [InlineData(false, NestedCancellation.SourceProcessingCancelled)]
    [InlineData(true, NestedCancellation.Uncancelled)]
    [InlineData(true, NestedCancellation.NestedPreCancelled)]
    [InlineData(true, NestedCancellation.SourceProcessingCancelled)]
    public async Task Reentry_GenuineCancellationKeepsItsPrecedence_OverTheLoadCycleVerdict(bool otherRegion, NestedCancellation mode)
    {
        Algorithm? root = null;
        var which = 0;
        var hosts = HostOperations.Create(HostOperation.Create("Which", (_, _) => new Result.Atom(Volatile.Read(ref which))));
        Task<EvalResult<IReadOnlyList<Decimal128>>> Evaluate(CancellationToken cancellationToken = default)
            => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root!), hosts, null, null, cancellationToken);
        using var nestedCancellation = new CancellationTokenSource();
        using var sourceCancellation = new CancellationTokenSource();
        if (mode == NestedCancellation.NestedPreCancelled)
            nestedCancellation.Cancel();
        var downloader = new ReentrantDownloader
        {
            Nested = Evaluate,
            NestedToken = nestedCancellation.Token,
            BeforeNested = () =>
            {
                Volatile.Write(ref which, otherRegion ? 1 : 0);
                if (mode == NestedCancellation.SourceProcessingCancelled)
                    sourceCancellation.Cancel();
            },
        };
        var options = new RunOptions
        {
            HostOperations = hosts,
            DownloadCode = (url, token) => url == ModuleA
                ? downloader.Download(token, ModuleSource)
                : ValueTask.FromResult("public W = 8"),
            SourceProcessingCancellationToken = sourceCancellation.Token,
        };
        root = (await SourceProvenance.ParseValidAsync(TwoRegionProgram, options)).Root;
        var region = RegionOf(root);
        var regionG = RegionOf(root, "G");

        var outer = Task.Run(() => Evaluate());
        if (mode == NestedCancellation.SourceProcessingCancelled)
        {
            var outerError = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => outer.WaitAsync(HangGuard));
            Assert.Equal(sourceCancellation.Token, outerError.CancellationToken);
        }
        else
        {
            AssertValue(await outer.WaitAsync(HangGuard));
        }

        Assert.True(downloader.NestedCompletedInsideTheDownload, "the nested selection waited");
        switch (mode)
        {
            case NestedCancellation.Uncancelled:
                AssertReentrantSelectionRejected(downloader);
                break;
            case NestedCancellation.NestedPreCancelled:
            {
                var cancelled = Assert.IsAssignableFrom<OperationCanceledException>(downloader.NestedException);
                Assert.Equal(nestedCancellation.Token, cancelled.CancellationToken);
                break;
            }
            case NestedCancellation.SourceProcessingCancelled:
            {
                var cancelled = Assert.IsAssignableFrom<OperationCanceledException>(downloader.NestedException);
                Assert.Equal(sourceCancellation.Token, cancelled.CancellationToken);
                Assert.True(downloader.DownloaderTokenCancelledOnReturn);
                Assert.False(region.IsMaterialized);
                break;
            }
        }
        // Whichever way the nested selection ended, it counted nothing and abandoned nothing.
        AssertNoAbandonment(region);
        AssertNoAbandonment(regionG);
        Assert.Equal(1, region.MaterializationAttempts);
        Assert.Equal(0, regionG.MaterializationAttempts);
        Assert.Equal(0, regionG.InFlightConsumers);
        await AssertGateFree(region);
        if (mode != NestedCancellation.SourceProcessingCancelled)
        {
            // Rejection/cancellation of the nested selection cannot poison its later use.
            AssertValue(await Evaluate().WaitAsync(HangGuard), otherRegion ? 8 : 7);
            Assert.Equal(otherRegion ? 1 : 0, regionG.MaterializationAttempts);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task Reentry_AfterTheOuterConsumerLeft_StillFailsAsALoadCycle_AndTheAbandonedRunIsRecordedCleanly(bool otherRegion)
    {
        Algorithm? root = null;
        var which = 0;
        var hosts = HostOperations.Create(HostOperation.Create("Which", (_, _) => new Result.Atom(Volatile.Read(ref which))));
        Task<EvalResult<IReadOnlyList<Decimal128>>> Evaluate(CancellationToken cancellationToken = default)
            => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root!), hosts, null, null, cancellationToken);
        using var outerCancellation = new CancellationTokenSource();
        var downloader = new ReentrantDownloader
        {
            Nested = Evaluate,
            // The outer evaluation is the run's only consumer: its leave abandons the run, which
            // cancels the downloader's token — but the gate turn is still held until this
            // download returns, so the nested selection would still wait for it.
            BeforeNested = () =>
            {
                Volatile.Write(ref which, otherRegion ? 1 : 0);
                outerCancellation.Cancel();
            },
        };
        var options = new RunOptions
        {
            HostOperations = hosts,
            DownloadCode = (url, token) => url == ModuleA
                ? downloader.Download(token, ModuleSource)
                : ValueTask.FromResult("public W = 8"),
        };
        root = (await SourceProvenance.ParseValidAsync(TwoRegionProgram, options)).Root;
        var region = RegionOf(root);
        var regionG = RegionOf(root, "G");

        var outer = Task.Run(() => Evaluate(outerCancellation.Token));
        var outerError = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => outer.WaitAsync(HangGuard));
        Assert.Equal(outerCancellation.Token, outerError.CancellationToken);

        // Cancellation of a DIFFERENT evaluation does not turn the cycle into a cancellation.
        AssertReentrantSelectionRejected(downloader);
        Assert.True(downloader.DownloaderTokenCancelledOnReturn);
        Assert.False(region.IsMaterialized);
        AssertAbandonedCleanly(region);
        AssertNoAbandonment(regionG);
        Assert.Equal(0, regionG.InFlightConsumers);
        Assert.Equal(0, regionG.MaterializationAttempts);
        await AssertGateFree(region);

        Volatile.Write(ref which, 0);
        AssertValue(await Evaluate().WaitAsync(HangGuard));
        Assert.Equal(2, region.MaterializationAttempts);
        AssertAbandonedCleanly(region);
        if (otherRegion)
        {
            Volatile.Write(ref which, 1);
            AssertValue(await Evaluate().WaitAsync(HangGuard), 8);
            Assert.Equal(1, regionG.MaterializationAttempts);
            AssertNoAbandonment(regionG);
        }
    }

    // ── 9b. The host contract for independent consumers (B16) ──────────────
    //
    // Owner decision (Nov 10 2026, Option 1): the conservative rule is the supported
    // RunOptions.DownloadCode contract. The library sees only the selection's wait for the held
    // turn, never whether the downloader waits for the selection, so an evaluation in the
    // downloader's flowed context that selects a not-yet-loaded branch of the same tree is
    // refused during the load EVEN WHEN NOTHING WAITS FOR IT. Those cases are contract pins, not
    // detected cycles. Work started without the downloader's context (another context, flow
    // suppressed, after the load) waits for the load like any concurrent consumer and succeeds.

    [Fact]
    public async Task ConcurrentJoinersFromOtherContexts_AreNeverTakenForReentry_AndShareOneAttempt()
    {
        using var started = new ManualResetEventSlim();
        using var release = new ManualResetEventSlim();
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) =>
            {
                Interlocked.Increment(ref calls);
                started.Set();
                Assert.True(release.Wait(HangGuard));
                return ValueTask.FromResult(ModuleSource);
            },
        };
        var root = (await SourceProvenance.ParseValidAsync(Program, options)).Root;
        var region = RegionOf(root);

        var starter = Task.Run(() => RunFlat(root));
        Assert.True(started.Wait(HangGuard), "hang guard: download never started");
        // Two joiners from the test's own (flowed) context, on other threads, while the starter's
        // work holds the gate turn inline: ordinary joins, never a reentry.
        using var cancellable = new CancellationTokenSource();
        var joiners = new[] { Task.Run(() => RunFlat(root)), Task.Run(() => RunFlat(root, cancellable.Token)) };
        await WaitUntil(() => region.InFlightConsumers == 3, "the joiners never joined the in-flight run");
        release.Set();

        AssertValue(await starter.WaitAsync(HangGuard));
        foreach (var joiner in joiners)
            AssertValue(await joiner.WaitAsync(HangGuard));
        Assert.Equal(1, calls);
        Assert.Equal(1, region.MaterializationAttempts);
        AssertNoAbandonment(region);
    }

    // What one independent-child scenario observed. The downloader of F's module starts a child
    // evaluation with Task.Run and never waits for it; only the test's separate controller
    // completes the download. The two contracts' scenarios differ in nothing but whether the
    // child carries the downloader's execution context.
    private sealed record IndependentChildRun(
        Algorithm Root,
        HostOperations Hosts,
        DeferredModuleRegion RegionF,
        DeferredModuleRegion RegionG,
        bool ChildCompletedAtItsSelection,
        int FConsumersWhileHeld,
        int GConsumersWhileHeld,
        int GAttemptsWhileHeld,
        EvalResult<IReadOnlyList<Decimal128>> Outer,
        EvalResult<IReadOnlyList<Decimal128>>? Child,
        Exception? ChildEscaped);

    private static async Task<IndependentChildRun> RunIndependentChild(bool otherRegion, bool suppressFlow)
    {
        var which = 0;
        var hosts = HostOperations.Create(HostOperation.Create("Which", (_, _) => new Result.Atom(Volatile.Read(ref which))));
        var selected = new TaskCompletionSource<bool>(TaskCreationOptions.RunContinuationsAsynchronously);
        var releaseDownload = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        Algorithm? root = null;
        Task<EvalResult<IReadOnlyList<Decimal128>>>? independent = null;
        var options = new RunOptions
        {
            HostOperations = hosts,
            DownloadCode = async (url, _) =>
            {
                if (url != ModuleA)
                    return "public W = 8";
                Func<Task<EvalResult<IReadOnlyList<Decimal128>>>> child = async () =>
                {
                    Volatile.Write(ref which, otherRegion ? 1 : 0);
                    var pending = Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root!), hosts, null, null, CancellationToken.None);
                    // RunFlatAsync executes its prefix through selection before returning.
                    selected.TrySetResult(pending.IsCompleted);
                    return await pending;
                };
                // The downloader never awaits the child. The ONLY difference between the
                // scenarios: the suppression is disposed on this thread before the await below.
                if (suppressFlow)
                {
                    using (ExecutionContext.SuppressFlow())
                        independent = Task.Run(child);
                }
                else
                {
                    independent = Task.Run(child);
                }
                await releaseDownload.Task;
                return ModuleSource;
            },
        };
        root = (await SourceProvenance.ParseValidAsync(TwoRegionProgram, options)).Root;
        var regionF = RegionOf(root, "F");
        var regionG = RegionOf(root, "G");
        var outer = Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), hosts, null, null, CancellationToken.None);
        bool completedAtSelection;
        int fConsumers, gConsumers, gAttempts;
        try
        {
            completedAtSelection = await selected.Task.WaitAsync(HangGuard);
            // Still inside the held download: the controller has not released it.
            fConsumers = regionF.InFlightConsumers;
            gConsumers = regionG.InFlightConsumers;
            gAttempts = regionG.MaterializationAttempts;
        }
        finally
        {
            // Neither assertion failure nor a watchdog leaves a worker behind.
            releaseDownload.TrySetResult();
            await outer.WaitAsync(HangGuard);
            if (independent is not null)
                await independent.WaitAsync(HangGuard);
        }

        EvalResult<IReadOnlyList<Decimal128>>? childResult = null;
        var escaped = await Record.ExceptionAsync(async () => childResult = await independent!);
        return new IndependentChildRun(root, hosts, regionF, regionG, completedAtSelection, fConsumers, gConsumers, gAttempts,
            await outer, childResult, escaped);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task IndependentEvaluationStartedByDownloader_WithFlowedContext_IsRefusedDuringTheLoad_AlthoughNothingWaitsForIt(bool otherRegion)
    {
        // Contract pin (B16 host contract), formerly a required-success case: nothing waits for
        // this child, and it is refused anyway, because the library cannot see that.
        var run = await RunIndependentChild(otherRegion, suppressFlow: false);

        Assert.True(run.ChildCompletedAtItsSelection, "the flowed child was not refused at its selection");
        AssertReentrantSelectionRejected(run.Child, run.ChildEscaped);
        // The refusal counted no consumer and started nothing.
        Assert.Equal(1, run.FConsumersWhileHeld);
        Assert.Equal(0, run.GConsumersWhileHeld);
        Assert.Equal(0, run.GAttemptsWhileHeld);
        // The load in progress published normally.
        AssertValue(run.Outer);
        Assert.Equal(1, run.RegionF.MaterializationAttempts);
        Assert.Equal(0, run.RegionG.MaterializationAttempts);
        AssertNoAbandonment(run.RegionF);
        AssertNoAbandonment(run.RegionG);
        await AssertGateFree(run.RegionF);

        // The same selection, evaluated again from the test's own context after the load: served.
        AssertValue(await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(run.Root), run.Hosts, null, null, CancellationToken.None)
            .WaitAsync(HangGuard), otherRegion ? 8 : 7);
        Assert.Equal(1, run.RegionF.MaterializationAttempts);
        Assert.Equal(otherRegion ? 1 : 0, run.RegionG.MaterializationAttempts);
        AssertNoAbandonment(run.RegionG);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task IndependentEvaluationStartedByDownloader_WithFlowSuppressed_WaitsForTheLoad_AndSucceeds(bool otherRegion)
    {
        // The supported pattern: the same child, scheduled without the downloader's context, is
        // an ordinary concurrent consumer: it joins F's run, or G's run queues for the gate.
        var run = await RunIndependentChild(otherRegion, suppressFlow: true);

        Assert.False(run.ChildCompletedAtItsSelection, "an independent consumer was refused before the download was released");
        Assert.Equal(otherRegion ? 1 : 2, run.FConsumersWhileHeld);
        Assert.Equal(otherRegion ? 1 : 0, run.GConsumersWhileHeld);
        Assert.Equal(0, run.GAttemptsWhileHeld);
        AssertValue(run.Outer);
        Assert.Null(run.ChildEscaped);
        Assert.True(run.Child.HasValue);
        AssertValue(run.Child.Value, otherRegion ? 8 : 7);
        Assert.Equal(1, run.RegionF.MaterializationAttempts);
        Assert.Equal(otherRegion ? 1 : 0, run.RegionG.MaterializationAttempts);
        AssertNoAbandonment(run.RegionF);
        AssertNoAbandonment(run.RegionG);
        await AssertGateFree(run.RegionF);
    }

    [Fact]
    public async Task IndependentEvaluation_SelectingWhileTheDownloaderIsStillInsideItsSynchronousCall_IsRefusedToo()
    {
        // Contract pin (ported from the Reviewer 2 probe): the downloader starts a flowed child,
        // blocks only until the child's selection has run, then suspends on a separate
        // controller. Neither waits for the other's result, and the child is still refused, so
        // the verdict does not depend on whether the downloader has suspended yet.
        using var selected = new ManualResetEventSlim();
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        Algorithm? root = null;
        Task<EvalResult<IReadOnlyList<Decimal128>>>? child = null;
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = async (_, _) =>
            {
                if (Interlocked.Increment(ref calls) > 1)
                    return ModuleSource;
                child = Task.Run(async () =>
                {
                    var pending = RunFlat(root!);
                    selected.Set();
                    return await pending;
                });
                Assert.True(selected.Wait(HangGuard), "hang guard: the child never selected");
                await release.Task;
                return ModuleSource;
            },
        };
        root = (await SourceProvenance.ParseValidAsync(Program, options)).Root;
        var region = RegionOf(root);
        var outer = RunFlat(root);
        try
        {
            Assert.True(selected.Wait(HangGuard), "hang guard: the child never selected");
        }
        finally
        {
            release.TrySetResult();
            await outer.WaitAsync(HangGuard);
            if (child is not null)
                await child.WaitAsync(HangGuard);
        }

        EvalResult<IReadOnlyList<Decimal128>>? childResult = null;
        var escaped = await Record.ExceptionAsync(async () => childResult = await child!);
        AssertReentrantSelectionRejected(childResult, escaped);
        AssertValue(await outer);
        Assert.Equal(1, calls);
        Assert.Equal(1, region.MaterializationAttempts);
        AssertNoAbandonment(region);
        await AssertGateFree(region);
        AssertValue(await RunFlat(root).WaitAsync(HangGuard));
        Assert.Equal(1, region.MaterializationAttempts);
    }

    public enum SafeNestedSelection
    {
        /// <summary>The nested evaluation selects a region that is already materialized.</summary>
        MaterializedRegion,

        /// <summary>The nested evaluation selects code that loads nothing.</summary>
        NonDeferredCode,
    }

    [Theory]
    [InlineData(SafeNestedSelection.MaterializedRegion, 8)]
    [InlineData(SafeNestedSelection.NonDeferredCode, 5)]
    public async Task NestedEvaluationOfTheSameTree_ThatWaitsForNothing_SucceedsInsideTheDownload(SafeNestedSelection selection, int expected)
    {
        var which = 1;
        var hosts = HostOperations.Create(HostOperation.Create("Which", (_, _) => new Result.Atom(Volatile.Read(ref which))));
        Algorithm? root = null;
        var downloader = new ReentrantDownloader
        {
            Nested = token => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root!), hosts, null, null, token),
            BeforeNested = () => Volatile.Write(ref which, selection == SafeNestedSelection.MaterializedRegion ? 1 : 2),
        };
        var options = new RunOptions
        {
            HostOperations = hosts,
            DownloadCode = (url, token) => url == ModuleA
                ? downloader.Download(token, ModuleSource)
                : ValueTask.FromResult("public W = 8"),
        };
        root = (await SourceProvenance.ParseValidAsync(TwoRegionProgram, options)).Root;
        var regionF = RegionOf(root, "F");
        // G is materialized first, by an ordinary evaluation.
        AssertValue(await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), hosts, null, null, CancellationToken.None)
            .WaitAsync(HangGuard), 8);

        Volatile.Write(ref which, 0);
        AssertValue(await Task.Run(() => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), hosts, null, null, CancellationToken.None))
            .WaitAsync(HangGuard));

        Assert.True(downloader.NestedCompletedInsideTheDownload);
        Assert.Null(downloader.NestedException);
        AssertValue(downloader.NestedResult!.Value, expected);
        Assert.True(regionF.IsMaterialized);
        AssertNoAbandonment(regionF);
    }

    [Fact]
    public async Task NestedEvaluationOfADifferentParsedTree_FromInsideTheDownload_IsIndependent()
    {
        // The nested program is a separate parse: its own loader, gate, and regions.
        var innerOptions = new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult("public V = 9") };
        var inner = (await SourceProvenance.ParseValidAsync(Program, innerOptions)).Root;
        var innerRegion = RegionOf(inner);
        var downloader = new ReentrantDownloader { Nested = token => RunFlat(inner, token) };
        var options = new RunOptions { DownloadCode = (_, token) => downloader.Download(token, ModuleSource) };
        var root = (await SourceProvenance.ParseValidAsync(Program, options)).Root;

        AssertValue(await Task.Run(() => RunFlat(root)).WaitAsync(HangGuard));

        Assert.True(downloader.NestedCompletedInsideTheDownload);
        Assert.Null(downloader.NestedException);
        AssertValue(downloader.NestedResult!.Value, 9);
        Assert.True(innerRegion.IsMaterialized);
    }

    [Fact]
    public async Task OneEvaluationSelectingTwoRegionsInTurn_IsNotAReentry()
    {
        // The starter runs F's work inline; once that work returned, its gate turn is gone from
        // the starter's context, so the same evaluation's later selection of G is ordinary.
        var options = new RunOptions
        {
            DownloadCode = (url, _) => ValueTask.FromResult(url == ModuleA ? ModuleSource : "public W = 8"),
        };
        var source =
            $"F(0) = 0\nF(1) = {{\n    N = load('{ModuleA}')\n    N.V\n}}\n" +
            $"G(0) = 0\nG(1) = {{\n    M = load('{ModuleB}')\n    M.W\n}}\n" +
            "F(1) + G(1)";
        var root = (await SourceProvenance.ParseValidAsync(source, options)).Root;

        AssertValue(await RunFlat(root).WaitAsync(HangGuard), 15);
        Assert.True(RegionOf(root, "F").IsMaterialized);
        Assert.True(RegionOf(root, "G").IsMaterialized);
    }

    public enum LeftBehind
    {
        /// <summary>Started with the download's flowed context, run after the download returned.</summary>
        FlowedContextAfterTheTurn,

        /// <summary>Started with execution-context flow suppressed, run while the download is in progress.</summary>
        SuppressedFlowDuringTheTurn,
    }

    [Theory]
    [InlineData(LeftBehind.FlowedContextAfterTheTurn)]
    [InlineData(LeftBehind.SuppressedFlowDuringTheTurn)]
    public async Task AnEvaluationTheDownloaderStartsButDoesNotAwait_IsNotRejected_OnceItIsOutsideTheTurn(LeftBehind mode)
    {
        var which = 0;
        var hosts = HostOperations.Create(HostOperation.Create("Which", (_, _) => new Result.Atom(Volatile.Read(ref which))));
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        Algorithm? root = null;
        Task<EvalResult<IReadOnlyList<Decimal128>>>? leftBehind = null;
        var options = new RunOptions
        {
            HostOperations = hosts,
            DownloadCode = (url, _) =>
            {
                if (url != ModuleA)
                    return ValueTask.FromResult("public W = 8");
                Func<Task<EvalResult<IReadOnlyList<Decimal128>>>> evaluateG = async () =>
                {
                    if (mode == LeftBehind.FlowedContextAfterTheTurn)
                        await release.Task;
                    Volatile.Write(ref which, 1);
                    return await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root!), hosts, null, null, CancellationToken.None);
                };
                if (mode == LeftBehind.SuppressedFlowDuringTheTurn)
                {
                    using (ExecutionContext.SuppressFlow())
                        leftBehind = Task.Run(evaluateG);
                    // G's run genuinely waits for the gate this download holds — an ordinary
                    // wait that ends when this download returns, not a rejection.
                    var waited = SpinWait.SpinUntil(() => RegionOf(root!, "G").InFlightConsumers == 1, HangGuard);
                    Assert.True(waited, "the left-behind evaluation never started G's run");
                }
                else
                {
                    leftBehind = Task.Run(evaluateG);
                }
                return ValueTask.FromResult(ModuleSource);
            },
        };
        root = (await SourceProvenance.ParseValidAsync(TwoRegionProgram, options)).Root;

        AssertValue(await Task.Run(() => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), hosts, null, null, CancellationToken.None))
            .WaitAsync(HangGuard));
        release.SetResult();

        AssertValue(await leftBehind!.WaitAsync(HangGuard), 8);
        Assert.True(RegionOf(root, "G").IsMaterialized);
        AssertNoAbandonment(RegionOf(root, "G"));
    }

    // ── 9c. Cycles through a second parsed program (B16) ────────────────────
    //
    // Another parsed program has its own loader, turn and regions, so the refusal reaches it only
    // through the execution context: a load's turn frame chains the frames its STARTING context
    // already carried (HeldGateTurn.Enclosing). Program 1's download evaluates program 2, that
    // selection starts program 2's load, and program 2's download evaluates program 1 again. The
    // last selection would wait for program 1's load, which waits for all of the above; it is
    // refused at once, without a token. Nothing else pins the chaining: every other test has one
    // loader, or a second program whose downloader evaluates nothing.
    //
    // A load that ANOTHER execution context started contributes no frame to the evaluations that
    // wait for it. The same two downloaders therefore close a wait-for cycle when two unrelated
    // evaluations start the two loads: neither selection is refused, nothing has a timeout, and
    // the cycle is ended by cancelling a waiting evaluation's own token, not by cancelling the
    // evaluations that started the loads. That is a documented limit of the host contract
    // (RunOptions.DownloadCode, Reentrancy), not a guarantee: those cases pin what a host
    // observes today and how a bounded token recovers, and they are re-specified if the refusal
    // is ever widened. Every wait is bounded: each download's wait for its evaluation by the
    // watchdog, the cycle by a short token armed once it is closed.

    // Outlasts the downloads' own watchdogs, so a chain that waits instead of being refused fails
    // on the refusal assertions and never on the test's wait for the outer evaluation.
    private static readonly TimeSpan ChainGuard = HangGuard + HangGuard;

    // The bound a host would put on an evaluation its downloader waits for.
    private static readonly TimeSpan ShortBound = TimeSpan.FromMilliseconds(100);

    public enum HostForm
    {
        /// <summary>Sync-over-async: the downloader evaluates on its own thread and blocks on the result.</summary>
        BlockingOnTheDownloaderThread,

        /// <summary>Sync-over-async: the downloader blocks on <see cref="Task.Run(Func{Task})"/> (another thread, flowed context).</summary>
        BlockingOnTaskRun,

        /// <summary>An asynchronous downloader awaits the evaluation after a genuine suspension.</summary>
        AwaitingAfterASuspension,
    }

    /// <summary>
    /// The downloader of one cross-program scenario. Its first download of the F module evaluates
    /// another program in the given host form and waits for it, then serves the module like every
    /// later call. The wait is watchdog-bounded: an evaluation that never ends is left behind,
    /// the download returns anyway, and everything unwinds.
    /// </summary>
    private sealed class NestingDownloader(HostForm form)
    {
        private readonly TaskCompletionSource _entered = new(TaskCreationOptions.RunContinuationsAsynchronously);
        private readonly TaskCompletionSource<bool> _selected = new(TaskCreationOptions.RunContinuationsAsynchronously);
        private readonly TaskCompletionSource _returned = new(TaskCreationOptions.RunContinuationsAsynchronously);
        private int _calls;

        /// <summary>The evaluation the first download runs and waits for.</summary>
        public Func<Task<EvalResult<IReadOnlyList<Decimal128>>>>? Nested { get; set; }

        /// <summary>When set, the first download waits for it before it evaluates anything.</summary>
        public Task? Hold { get; set; }

        /// <summary>Runs inside the first download, after its evaluation ended (or the watchdog fired).</summary>
        public Action? AfterNested { get; set; }

        /// <summary>Completes when the first download is running.</summary>
        public Task Entered => _entered.Task;

        /// <summary>
        /// Completes when the evaluation's selection has run, with whether the evaluation had
        /// already ended by then. The async entry point executes its prefix through selection
        /// before it returns, so <c>true</c> is a selection refused at once and <c>false</c> one
        /// that waits.
        /// </summary>
        public Task<bool> Selected => _selected.Task;

        /// <summary>Completes when the first download is about to return its module.</summary>
        public Task Returned => _returned.Task;

        public int Calls => Volatile.Read(ref _calls);

        public CancellationToken Token { get; private set; }

        public bool TokenCancelledOnReturn { get; private set; }

        public bool NestedEndedInsideTheDownload { get; private set; }

        public EvalResult<IReadOnlyList<Decimal128>>? NestedResult { get; private set; }

        public Exception? NestedException { get; private set; }

        public ValueTask<string> Download(string source, CancellationToken token)
        {
            if (Interlocked.Increment(ref _calls) > 1)
                return ValueTask.FromResult(source);
            Token = token;
            return form == HostForm.AwaitingAfterASuspension
                ? new ValueTask<string>(DownloadAwaiting(source, token))
                : ValueTask.FromResult(DownloadBlocking(source, token));
        }

        private Task<EvalResult<IReadOnlyList<Decimal128>>> Evaluate()
        {
            var pending = Nested!();
            _selected.TrySetResult(pending.IsCompleted);
            return pending;
        }

        private string DownloadBlocking(string source, CancellationToken token)
        {
            _entered.TrySetResult();
            // Hang guard only: a hold nobody releases is abandoned, and the test fails on what follows.
            Hold?.Wait(HangGuard);
            var nested = form == HostForm.BlockingOnTaskRun ? Task.Run(() => Evaluate()) : Evaluate();
            // Watchdog only: an evaluation that waits instead of ending is left behind, and ends
            // once this download has returned.
            NestedEndedInsideTheDownload = ((IAsyncResult)nested).AsyncWaitHandle.WaitOne(HangGuard);
            if (NestedEndedInsideTheDownload)
                NestedException = Record.Exception(() => NestedResult = nested.GetAwaiter().GetResult());
            return Return(source, token);
        }

        private async Task<string> DownloadAwaiting(string source, CancellationToken token)
        {
            _entered.TrySetResult();
            // A genuine suspension first: the evaluation runs on a continuation, on whatever
            // thread resumes it, with the download's flowed context.
            await Task.Yield();
            if (Hold is { } hold)
            {
                // Hang guard only, as in the blocking form.
                try { await hold.WaitAsync(HangGuard); }
                catch (TimeoutException) { }
            }

            var nested = Evaluate();
            try
            {
                NestedResult = await nested.WaitAsync(HangGuard);
                NestedEndedInsideTheDownload = true;
            }
            catch (TimeoutException) when (!nested.IsCompleted)
            {
                // Watchdog only, as in the blocking form.
            }
            catch (Exception error)
            {
                NestedException = error;
                NestedEndedInsideTheDownload = true;
            }

            return Return(source, token);
        }

        private string Return(string source, CancellationToken token)
        {
            AfterNested?.Invoke();
            TokenCancelledOnReturn = token.IsCancellationRequested;
            _returned.TrySetResult();
            return source;
        }
    }

    /// <summary>
    /// One separately parsed two-region program of a cross-program scenario: its own loader,
    /// turn, regions, branch selector and downloader, and module values no other program has.
    /// Every program loads the same two URLs, which stay independent: a module cache belongs to
    /// one parse.
    /// </summary>
    private sealed class CrossProgram
    {
        private int _which;
        private int _otherModuleDownloads;

        private CrossProgram(int index, HostForm form)
        {
            F = 7 + 10 * index;
            G = 8 + 10 * index;
            Downloader = new NestingDownloader(form);
            Hosts = HostOperations.Create(HostOperation.Create("Which", (_, _) => new Result.Atom(Volatile.Read(ref _which))));
        }

        /// <summary>The value of the F branch, whose module the nesting downloader serves.</summary>
        public int F { get; }

        /// <summary>The value of the G branch.</summary>
        public int G { get; }

        public NestingDownloader Downloader { get; }

        public HostOperations Hosts { get; }

        public Algorithm Root { get; private set; } = null!;

        public DeferredModuleRegion RegionF { get; private set; } = null!;

        public DeferredModuleRegion RegionG { get; private set; } = null!;

        public ModuleLoader Loader => RegionF.Loader;

        /// <summary>Downloads of the G module, which no scenario nests anything in.</summary>
        public int OtherModuleDownloads => Volatile.Read(ref _otherModuleDownloads);

        /// <summary>Which branch the next evaluation of this program selects.</summary>
        public void Select(bool otherRegion) => Volatile.Write(ref _which, otherRegion ? 1 : 0);

        public Task<EvalResult<IReadOnlyList<Decimal128>>> Evaluate(CancellationToken cancellationToken = default)
            => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(Root), Hosts, null, null, cancellationToken);

        public static async Task<CrossProgram> Parse(int index, HostForm form)
        {
            var program = new CrossProgram(index, form);
            var options = new RunOptions
            {
                HostOperations = program.Hosts,
                DownloadCode = (url, token) =>
                {
                    if (url == ModuleA)
                        return program.Downloader.Download($"public V = {program.F}", token);
                    Interlocked.Increment(ref program._otherModuleDownloads);
                    return ValueTask.FromResult($"public W = {program.G}");
                },
            };
            program.Root = (await SourceProvenance.ParseValidAsync(TwoRegionProgram, options)).Root;
            program.RegionF = RegionOf(program.Root, "F");
            program.RegionG = RegionOf(program.Root, "G");
            Assert.Same(program.RegionF.Loader, program.RegionG.Loader);
            return program;
        }
    }

    private static async Task AssertNothingLeftBehind(CrossProgram program)
    {
        Assert.Equal(0, program.RegionF.InFlightConsumers);
        Assert.Equal(0, program.RegionG.InFlightConsumers);
        await AssertGateFree(program.RegionF);
        Assert.Equal(0, program.Loader.InProgressModuleCount);
    }

    [Theory]
    [InlineData(HostForm.BlockingOnTheDownloaderThread, false)]
    [InlineData(HostForm.BlockingOnTheDownloaderThread, true)]
    [InlineData(HostForm.BlockingOnTaskRun, false)]
    [InlineData(HostForm.BlockingOnTaskRun, true)]
    [InlineData(HostForm.AwaitingAfterASuspension, false)]
    [InlineData(HostForm.AwaitingAfterASuspension, true)]
    public async Task CrossProgramChain_StartedInTheDownloaderContext_SelectingTheFirstProgramAgain_FailsFastWithALoadCycle_WithoutAToken(
        HostForm form, bool otherRegion)
    {
        var first = await CrossProgram.Parse(0, form);
        var second = await CrossProgram.Parse(1, form);
        Assert.NotSame(first.Loader.MaterializationGate, second.Loader.MaterializationGate);
        // Program 1's download evaluates program 2: that selection STARTS program 2's load, in
        // the download's execution context.
        first.Downloader.Nested = () => second.Evaluate();
        // Program 2's download evaluates program 1 again: the branch being loaded (it would join
        // that load's run) or the other one (it would queue for the turn that load holds). No
        // evaluation has a token.
        second.Downloader.Nested = () =>
        {
            first.Select(otherRegion);
            return first.Evaluate();
        };
        int firstFConsumers = -1, firstGConsumers = -1, firstGAttempts = -1, secondFConsumers = -1;
        second.Downloader.AfterNested = () =>
        {
            firstFConsumers = first.RegionF.InFlightConsumers;
            firstGConsumers = first.RegionG.InFlightConsumers;
            firstGAttempts = first.RegionG.MaterializationAttempts;
            secondFConsumers = second.RegionF.InFlightConsumers;
        };

        AssertValue(await Task.Run(() => first.Evaluate()).WaitAsync(ChainGuard), first.F);

        // The innermost selection was refused at once, as a load cycle of program 1.
        Assert.True(await second.Downloader.Selected.WaitAsync(HangGuard),
            "the selection waited for the load whose downloads wait for it instead of being refused at once");
        Assert.True(second.Downloader.NestedEndedInsideTheDownload, "the refused selection did not end inside the download");
        AssertReentrantSelectionRejected(second.Downloader.NestedResult, second.Downloader.NestedException);
        // It counted nothing on either load in progress, and cancelled neither.
        Assert.Equal(1, firstFConsumers);
        Assert.Equal(0, firstGConsumers);
        Assert.Equal(0, firstGAttempts);
        Assert.Equal(1, secondFConsumers);
        Assert.False(first.Downloader.TokenCancelledOnReturn);
        Assert.False(second.Downloader.TokenCancelledOnReturn);
        // Both loads completed normally: program 2 was served to program 1's download, and
        // program 1 published.
        Assert.True(first.Downloader.NestedEndedInsideTheDownload, "program 2's evaluation did not end inside the download");
        Assert.Null(first.Downloader.NestedException);
        AssertValue(first.Downloader.NestedResult!.Value, second.F);
        Assert.Equal(1, first.Downloader.Calls);
        Assert.Equal(1, second.Downloader.Calls);
        Assert.True(first.RegionF.IsMaterialized);
        Assert.True(second.RegionF.IsMaterialized);
        Assert.Equal(1, first.RegionF.MaterializationAttempts);
        Assert.Equal(1, second.RegionF.MaterializationAttempts);
        Assert.False(first.RegionG.IsMaterialized);
        Assert.Equal(0, first.RegionG.MaterializationAttempts);
        AssertNoAbandonment(first.RegionF);
        AssertNoAbandonment(first.RegionG);
        AssertNoAbandonment(second.RegionF);
        await AssertNothingLeftBehind(first);
        await AssertNothingLeftBehind(second);

        // Recovery: independent later evaluations are served, and so is the refused selection
        // itself now that the loads have finished.
        AssertValue(await first.Evaluate().WaitAsync(HangGuard), otherRegion ? first.G : first.F);
        Assert.Equal(otherRegion ? 1 : 0, first.RegionG.MaterializationAttempts);
        first.Select(otherRegion: false);
        AssertValue(await first.Evaluate().WaitAsync(HangGuard), first.F);
        AssertValue(await second.Evaluate().WaitAsync(HangGuard), second.F);
        Assert.Equal(1, first.RegionF.MaterializationAttempts);
        Assert.Equal(1, second.RegionF.MaterializationAttempts);
        Assert.Equal(1, first.Downloader.Calls);
        Assert.Equal(1, second.Downloader.Calls);
        AssertNoAbandonment(first.RegionG);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    public async Task CrossProgramChain_ThroughThreePrograms_RefusesALoadOfEveryProgramTheContextIsLoading(int reloaded)
    {
        var programs = new CrossProgram[3];
        for (var index = 0; index < programs.Length; index++)
            programs[index] = await CrossProgram.Parse(index, HostForm.BlockingOnTheDownloaderThread);
        programs[0].Downloader.Nested = () => programs[1].Evaluate();
        programs[1].Downloader.Nested = () => programs[2].Evaluate();
        // The innermost download selects a branch this context is already loading: two links out
        // (the whole chain of frames is searched), one link out, or its own program's.
        programs[2].Downloader.Nested = () => programs[reloaded].Evaluate();

        AssertValue(await Task.Run(() => programs[0].Evaluate()).WaitAsync(ChainGuard), programs[0].F);

        Assert.True(await programs[2].Downloader.Selected.WaitAsync(HangGuard),
            "the selection waited for a load this context holds instead of being refused at once");
        Assert.True(programs[2].Downloader.NestedEndedInsideTheDownload, "the refused selection did not end inside the download");
        AssertReentrantSelectionRejected(programs[2].Downloader.NestedResult, programs[2].Downloader.NestedException);
        // Every load in progress completed normally, innermost first.
        Assert.Null(programs[1].Downloader.NestedException);
        AssertValue(programs[1].Downloader.NestedResult!.Value, programs[2].F);
        Assert.Null(programs[0].Downloader.NestedException);
        AssertValue(programs[0].Downloader.NestedResult!.Value, programs[1].F);
        foreach (var program in programs)
        {
            Assert.True(program.RegionF.IsMaterialized);
            Assert.Equal(1, program.RegionF.MaterializationAttempts);
            Assert.Equal(1, program.Downloader.Calls);
            Assert.False(program.Downloader.TokenCancelledOnReturn);
            AssertNoAbandonment(program.RegionF);
            await AssertNothingLeftBehind(program);
        }

        // Recovery: the refused selection is served now.
        AssertValue(await programs[reloaded].Evaluate().WaitAsync(HangGuard), programs[reloaded].F);
        Assert.Equal(1, programs[reloaded].RegionF.MaterializationAttempts);
    }

    public enum CrossProgramWait
    {
        /// <summary>The evaluation selects the branch the other context is loading: it joins that load's run.</summary>
        JoinsTheRun,

        /// <summary>It selects the program's other branch: its own run queues for the loader turn that load holds.</summary>
        QueuesForTheTurn,
    }

    /// <summary>
    /// The two-program wait-for cycle through loads that other execution contexts started. Two
    /// unrelated evaluations start the two programs' loads; each download is held until both
    /// loads are in progress, then evaluates the OTHER program and waits for it. Program 1's
    /// download evaluates program 2 under the caller's token, program 2's download evaluates
    /// program 1 with no token.
    /// </summary>
    private sealed class CrossProgramCycle
    {
        private readonly TaskCompletionSource _bothLoading = new(TaskCreationOptions.RunContinuationsAsynchronously);

        public required CrossProgram First { get; init; }

        public required CrossProgram Second { get; init; }

        /// <summary>The evaluation that started program 1's load.</summary>
        public Task<EvalResult<IReadOnlyList<Decimal128>>> FirstStarter { get; private set; } = null!;

        /// <summary>The evaluation that started program 2's load.</summary>
        public Task<EvalResult<IReadOnlyList<Decimal128>>> SecondStarter { get; private set; } = null!;

        public static async Task<CrossProgramCycle> Start(
            HostForm form,
            CrossProgramWait wait,
            CancellationToken waitingToken,
            CancellationToken firstStarterToken = default,
            CancellationToken secondStarterToken = default)
        {
            var cycle = new CrossProgramCycle
            {
                First = await CrossProgram.Parse(0, form),
                Second = await CrossProgram.Parse(1, form),
            };
            var (first, second) = (cycle.First, cycle.Second);
            first.Downloader.Hold = cycle._bothLoading.Task;
            second.Downloader.Hold = cycle._bothLoading.Task;
            first.Downloader.Nested = () =>
            {
                second.Select(otherRegion: wait == CrossProgramWait.QueuesForTheTurn);
                return second.Evaluate(waitingToken);
            };
            second.Downloader.Nested = () => first.Evaluate();
            // Each from the test's own context: neither load's turn is visible to the other's.
            cycle.FirstStarter = Task.Run(() => first.Evaluate(firstStarterToken));
            cycle.SecondStarter = Task.Run(() => second.Evaluate(secondStarterToken));
            return cycle;
        }

        public async Task AssertClosed(CrossProgramWait wait)
        {
            await First.Downloader.Entered.WaitAsync(HangGuard);
            await Second.Downloader.Entered.WaitAsync(HangGuard);
            // Both loads are in progress, each started by its own evaluation, each holding its turn.
            Assert.Equal(1, First.RegionF.InFlightConsumers);
            Assert.Equal(1, Second.RegionF.InFlightConsumers);
            _bothLoading.SetResult();

            // Neither selection is refused: each is an ordinary consumer of a load that another
            // context started, so it waits.
            Assert.False(await First.Downloader.Selected.WaitAsync(HangGuard),
                "the evaluation of program 2 was refused or served at its selection instead of waiting for the load in progress");
            Assert.False(await Second.Downloader.Selected.WaitAsync(HangGuard),
                "the evaluation of program 1 was refused or served at its selection instead of waiting for the load in progress");
            Assert.Equal(2, First.RegionF.InFlightConsumers);
            Assert.Equal(wait == CrossProgramWait.JoinsTheRun ? 2 : 1, Second.RegionF.InFlightConsumers);
            Assert.Equal(wait == CrossProgramWait.JoinsTheRun ? 0 : 1, Second.RegionG.InFlightConsumers);
            Assert.Equal(0, Second.RegionG.MaterializationAttempts);
            // The cycle is closed: each load holds its turn and waits for its download, each
            // download for its evaluation, each evaluation for the other program's load.
            Assert.Equal(0, First.Loader.MaterializationGate.CurrentCount);
            Assert.Equal(0, Second.Loader.MaterializationGate.CurrentCount);
            Assert.False(FirstStarter.IsCompleted);
            Assert.False(SecondStarter.IsCompleted);
            Assert.False(First.Downloader.Returned.IsCompleted);
            Assert.False(Second.Downloader.Returned.IsCompleted);
            Assert.Equal(1, First.RegionF.MaterializationAttempts);
            Assert.Equal(1, Second.RegionF.MaterializationAttempts);
        }

        /// <summary>
        /// Neither an assertion failure nor a watchdog leaves a worker behind: everything is
        /// released, and the downloads' own watchdogs bound whatever still waits.
        /// </summary>
        public async Task Drain(CancellationTokenSource waiting)
        {
            _bothLoading.TrySetResult();
            waiting.Cancel();
            var pending = new List<Task> { FirstStarter, SecondStarter };
            foreach (var downloader in new[] { First.Downloader, Second.Downloader })
            {
                if (downloader.Entered.IsCompleted)
                    pending.Add(downloader.Returned);
            }

            await Record.ExceptionAsync(() => Task.WhenAll(pending).WaitAsync(ChainGuard));
        }
    }

    [Theory]
    [InlineData(HostForm.BlockingOnTheDownloaderThread, CrossProgramWait.JoinsTheRun)]
    [InlineData(HostForm.BlockingOnTheDownloaderThread, CrossProgramWait.QueuesForTheTurn)]
    [InlineData(HostForm.AwaitingAfterASuspension, CrossProgramWait.JoinsTheRun)]
    [InlineData(HostForm.AwaitingAfterASuspension, CrossProgramWait.QueuesForTheTurn)]
    public async Task CrossProgramCycle_ThroughLoadsOtherContextsStarted_IsNotRefused_AndWaitsUntilAWaitingEvaluationsBoundedTokenEndsIt(
        HostForm form, CrossProgramWait wait)
    {
        using var bounded = new CancellationTokenSource();
        var cycle = await CrossProgramCycle.Start(form, wait, bounded.Token);
        var (first, second) = (cycle.First, cycle.Second);
        try
        {
            await cycle.AssertClosed(wait);

            // The bound is armed only now, so the outcome never depends on how long closing the
            // cycle took. If the token did not end the wait, the download's watchdog would, and
            // the next assertions fail.
            bounded.CancelAfter(ShortBound);
            await first.Downloader.Returned.WaitAsync(HangGuard);
            Assert.True(first.Downloader.NestedEndedInsideTheDownload, "the bounded token did not end the waiting evaluation");
            // The waiting evaluation ended as its own cancellation: it could not have ended otherwise.
            Assert.Null(first.Downloader.NestedResult);
            var cancelled = Assert.IsAssignableFrom<OperationCanceledException>(first.Downloader.NestedException);
            Assert.Equal(bounded.Token, cancelled.CancellationToken);

            // One broken edge unwinds the whole cycle: program 1's download returned, its load
            // published and served the tokenless evaluation that waited for it, program 2's
            // download returned in turn, and both starting evaluations completed.
            AssertValue(await cycle.FirstStarter.WaitAsync(HangGuard), first.F);
            AssertValue(await cycle.SecondStarter.WaitAsync(HangGuard), second.F);
            Assert.True(second.Downloader.NestedEndedInsideTheDownload, "the tokenless evaluation did not end inside the download");
            Assert.Null(second.Downloader.NestedException);
            AssertValue(second.Downloader.NestedResult!.Value, first.F);
            // Only that one evaluation was cancelled: no load was, and nothing was downloaded twice.
            Assert.False(first.Downloader.TokenCancelledOnReturn);
            Assert.False(second.Downloader.TokenCancelledOnReturn);
            Assert.Equal(1, first.Downloader.Calls);
            Assert.Equal(1, second.Downloader.Calls);
            Assert.True(first.RegionF.IsMaterialized);
            Assert.True(second.RegionF.IsMaterialized);
            Assert.Equal(1, first.RegionF.MaterializationAttempts);
            Assert.Equal(1, second.RegionF.MaterializationAttempts);
            AssertNoAbandonment(first.RegionF);
            AssertNoAbandonment(first.RegionG);
            AssertNoAbandonment(second.RegionF);
            if (wait == CrossProgramWait.JoinsTheRun)
            {
                // Its leave was not the last on the run it had joined.
                AssertNoAbandonment(second.RegionG);
            }
            else
            {
                // It was the only consumer of the run it had queued for the turn: that run was
                // abandoned there, before it downloaded anything.
                AssertAbandonedCleanly(second.RegionG);
                Assert.False(second.RegionG.IsMaterialized);
                Assert.Equal(0, second.OtherModuleDownloads);
            }

            await AssertNothingLeftBehind(first);
            await AssertNothingLeftBehind(second);

            // Recovery: the cancelled selection itself is served now, from a fresh run where its
            // own was abandoned, and so is every other selection.
            AssertValue(await second.Evaluate().WaitAsync(HangGuard), wait == CrossProgramWait.JoinsTheRun ? second.F : second.G);
            Assert.True(wait == CrossProgramWait.JoinsTheRun || second.RegionG.IsMaterialized);
            Assert.Equal(wait == CrossProgramWait.JoinsTheRun ? 0 : 1, second.OtherModuleDownloads);
            second.Select(otherRegion: false);
            AssertValue(await second.Evaluate().WaitAsync(HangGuard), second.F);
            AssertValue(await first.Evaluate().WaitAsync(HangGuard), first.F);
            Assert.Equal(1, first.RegionF.MaterializationAttempts);
            Assert.Equal(1, second.RegionF.MaterializationAttempts);
            await AssertNothingLeftBehind(first);
            await AssertNothingLeftBehind(second);
        }
        finally
        {
            await cycle.Drain(bounded);
        }
    }

    [Fact]
    public async Task CrossProgramCycle_ThroughLoadsOtherContextsStarted_OutlivesTheEvaluationsThatStartedThoseLoads()
    {
        // Cancelling the evaluations that STARTED the two loads does not end the cycle. Each
        // leaves with its own token, but neither load is abandoned, because the other program's
        // waiting evaluation still counts as its consumer; so no downloader token is cancelled,
        // both turns stay held, and only a waiting evaluation's own token breaks an edge.
        using var firstStarter = new CancellationTokenSource();
        using var secondStarter = new CancellationTokenSource();
        using var bounded = new CancellationTokenSource();
        var cycle = await CrossProgramCycle.Start(HostForm.AwaitingAfterASuspension, CrossProgramWait.JoinsTheRun,
            bounded.Token, firstStarter.Token, secondStarter.Token);
        var (first, second) = (cycle.First, cycle.Second);
        try
        {
            await cycle.AssertClosed(CrossProgramWait.JoinsTheRun);

            firstStarter.Cancel();
            secondStarter.Cancel();
            // No thread is inside a download in this host form, so each starter returns at once.
            var firstError = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => cycle.FirstStarter.WaitAsync(HangGuard));
            Assert.Equal(firstStarter.Token, firstError.CancellationToken);
            var secondError = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => cycle.SecondStarter.WaitAsync(HangGuard));
            Assert.Equal(secondStarter.Token, secondError.CancellationToken);

            // The cycle is still closed: one consumer left on each load, nothing abandoned or
            // cancelled, both turns held, both downloads still waiting.
            Assert.Equal(1, first.RegionF.InFlightConsumers);
            Assert.Equal(1, second.RegionF.InFlightConsumers);
            AssertNoAbandonment(first.RegionF);
            AssertNoAbandonment(second.RegionF);
            Assert.False(first.Downloader.Token.IsCancellationRequested);
            Assert.False(second.Downloader.Token.IsCancellationRequested);
            Assert.Equal(0, first.Loader.MaterializationGate.CurrentCount);
            Assert.Equal(0, second.Loader.MaterializationGate.CurrentCount);
            Assert.False(first.Downloader.Returned.IsCompleted);
            Assert.False(second.Downloader.Returned.IsCompleted);
            Assert.False(first.RegionF.IsMaterialized);
            Assert.False(second.RegionF.IsMaterialized);

            // The waiting evaluation's bounded token ends it.
            bounded.CancelAfter(ShortBound);
            await first.Downloader.Returned.WaitAsync(HangGuard);
            await second.Downloader.Returned.WaitAsync(HangGuard);
            Assert.True(first.Downloader.NestedEndedInsideTheDownload, "the bounded token did not end the waiting evaluation");
            var cancelled = Assert.IsAssignableFrom<OperationCanceledException>(first.Downloader.NestedException);
            Assert.Equal(bounded.Token, cancelled.CancellationToken);
            // Program 1's load still had the tokenless evaluation as a consumer: it published
            // and served it.
            Assert.True(second.Downloader.NestedEndedInsideTheDownload, "the tokenless evaluation did not end inside the download");
            Assert.Null(second.Downloader.NestedException);
            AssertValue(second.Downloader.NestedResult!.Value, first.F);
            Assert.False(first.Downloader.TokenCancelledOnReturn);
            Assert.True(first.RegionF.IsMaterialized);
            Assert.Equal(1, first.RegionF.MaterializationAttempts);
            AssertNoAbandonment(first.RegionF);
            // The cancelled evaluation was the last consumer of program 2's load: its leave
            // abandoned that run, which cancelled its downloader token and published nothing.
            Assert.True(second.Downloader.TokenCancelledOnReturn);
            AssertAbandonedCleanly(second.RegionF);
            await AssertNothingLeftBehind(first);
            await AssertNothingLeftBehind(second);
            Assert.False(second.RegionF.IsMaterialized);
            Assert.Equal(1, second.RegionF.MaterializationAttempts);

            // Recovery: the abandoned load is retried by a fresh run, the published one is served.
            AssertValue(await second.Evaluate().WaitAsync(HangGuard), second.F);
            Assert.Equal(2, second.RegionF.MaterializationAttempts);
            Assert.Equal(2, second.Downloader.Calls);
            AssertAbandonedCleanly(second.RegionF);
            AssertValue(await first.Evaluate().WaitAsync(HangGuard), first.F);
            Assert.Equal(1, first.RegionF.MaterializationAttempts);
            Assert.Equal(1, first.Downloader.Calls);
            await AssertNothingLeftBehind(first);
            await AssertNothingLeftBehind(second);
        }
        finally
        {
            await cycle.Drain(bounded);
        }
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
        // Held until the trial ends (see HeldRegistrations): a downloader that disposed its
        // throwing registration on exit could unregister it before an abandoning Cancel() ran it.
        using var callbacks = new HeldRegistrations();
        var options = new RunOptions
        {
            DownloadCode = (_, token) =>
            {
                if (throwing)
                    callbacks.Hold(token.Register(static () => throw new InvalidOperationException(StressCallbackFailure)));
                if (mode >= 2)
                    return SuspendingStressDownload(token, mode == 2 ? Next(4) : -1);
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
        await WaitUntil(() => region.InFlightConsumers == 0, "an abandoned run never finished");
        // B15: a callback failure is recorded only for a throwing downloader, and as its own.
        if (region.LastAbandonmentFailure is { } failure)
        {
            if (!throwing) Violation("an abandonment failure without a throwing callback");
            else if (failure.FirstCallbackFailureMessage != StressCallbackFailure) Violation("a foreign abandonment failure");
            if (region.AbandonedRuns == 0) Violation("an abandonment failure without an abandoned run");
        }
        if (region.AbandonedRuns > region.MaterializationAttempts + consumerCount) Violation("abandonment over-counted");
        var abandonedBeforeTheNextSelection = region.AbandonedRuns;
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
        if (region.AbandonedRuns != abandonedBeforeTheNextSelection) Violation("a successful selection changed the abandonment count");
        if (throwing && region.AbandonedRuns > 0) Count("abandoned-throwing");
        foreach (var cancellation in sources)
            cancellation.Dispose();
    }

    private static async ValueTask<string> SuspendingStressDownload(CancellationToken token, int delay)
    {
        if (delay < 0)
            await Task.Yield();
        else
            await Task.Delay(delay, token);
        return ModuleSource;
    }
}
