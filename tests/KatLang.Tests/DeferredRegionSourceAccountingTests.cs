using System.Numerics;
using System.Text.RegularExpressions;
using KatLang.Evaluation;

namespace KatLang.Tests;

/// <summary>
/// Batch 3 of the resource/cancellation boundary audit (F3, F4): source accounting across
/// deferred materializations. C#-only host source-processing policy; Lean has no module
/// loading, no deferral and no source budget.
///
/// <para><b>F3.</b> A deferred branch's loads obey <see cref="SourceProcessingLimits.MaxModuleDepth"/>
/// exactly as eager loads do: the region records the live import depth at deferral
/// (<see cref="DeferredModuleRegion.ImportDepth"/>) and the materialization's walk-context scope
/// resumes it, then restores the displaced depth.</para>
///
/// <para><b>F4.</b> An attempt that publishes nothing releases the cache-hit splices its own walk
/// charged, exactly once, whatever the reason it did not publish. Its downloads stay charged,
/// including modules that completed and were cached inside it; the residual over-refusal that
/// leaves under an exactly fitting aggregate is pinned here deliberately.</para>
///
/// <para>Every downloader is deterministic and in memory — no network. The time limits are hang
/// guards, never latency claims.</para>
/// </summary>
public class DeferredRegionSourceAccountingTests
{
    private const string Base = "https://katlang.org/lazy/";
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);

    private static string Url(string name) => Base + name + ".kat";

    // ── Helpers ──────────────────────────────────────────────────────────────

    /// <summary>Every distinct deferred region reachable from <paramref name="root"/>, module content included.</summary>
    private static List<DeferredModuleRegion> Regions(Algorithm root)
    {
        var visited = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>();
        var regions = new List<DeferredModuleRegion>();
        pending.Push(root);
        while (pending.TryPop(out var node))
        {
            if (!visited.Add(node))
                continue;
            if (node is Algorithm { DeferredRegion: { } region } && !regions.Contains(region))
                regions.Add(region);
            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
                pending.Push(child);
        }

        return regions;
    }

    private static DeferredModuleRegion OnlyRegion(Algorithm root) => Assert.Single(Regions(root));

    private static Task<EvalResult<IReadOnlyList<Decimal128>>> RunFlat(Algorithm root, CancellationToken cancellationToken = default)
        => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), limits: null, cancellationToken);

    private static RunOptions Options(IReadOnlyDictionary<string, string> files, SourceProcessingLimits? limits = null)
        => new()
        {
            DownloadCode = (url, _) => ValueTask.FromResult(files[url]),
            SourceProcessingLimits = limits,
        };

    /// <summary>
    /// A verdict that eager and deferred elaboration can share: the error code and, for an
    /// import-depth refusal, the depth the message names. Eager refusals are parse failures and
    /// deferred ones evaluation failures, so the channel is deliberately not part of it.
    /// </summary>
    private static string Verdict(RunResult result) => result switch
    {
        RunResult.Success success => "ok " + success.ToDisplayString().Trim(),
        RunResult.ParseFailure failure => failure.Errors[0].Code + NamedDepth(failure.Errors[0].Message),
        RunResult.EvalFailure failure => failure.Errors[0].Code + NamedDepth(failure.Errors[0].Message),
        _ => throw new InvalidOperationException(result.GetType().Name),
    };

    private static string Verdict(EvalResult<IReadOnlyList<Decimal128>> result)
        => result.IsError
            ? result.Error.Code + NamedDepth(KatLangError.FromEvalError(result.Error).Message)
            : "ok " + string.Join(", ", result.Value);

    private static string NamedDepth(string message)
    {
        var match = Regex.Match(message, @"would reach depth (\d+), over the maximum of (\d+)");
        return match.Success ? $"@{match.Groups[1].Value}/{match.Groups[2].Value}" : "";
    }

    private static async Task WaitForGate(DeferredModuleRegion region)
    {
        // The abandoned attempt releases the materialization gate last; acquiring it proves the
        // walk has unwound. The wait itself is cancelled on timeout so it cannot steal the gate.
        using var timeout = new CancellationTokenSource(WaitLimit);
        await region.Loader.MaterializationGate.WaitAsync(timeout.Token);
        region.Loader.MaterializationGate.Release();
    }

    // A deferred chain main → m0 → [branch] m1 → [branch] m2 …: every module's next load sits in
    // a clause branch; the eager twin loads the next module at its top level.
    private static (Dictionary<string, string> Eager, Dictionary<string, string> Deferred) Chain(int length)
    {
        var eager = new Dictionary<string, string>();
        var deferred = new Dictionary<string, string>();
        for (var i = 0; i < length; i++)
        {
            var next = Url("m" + (i + 1));
            eager[Url("m" + i)] = i == length - 1
                ? "public F(x) = 42"
                : $"public N = load('{next}')\npublic F(x) = N.F(x)";
            deferred[Url("m" + i)] = i == length - 1
                ? "public F(0) = 0\npublic F(1) = 42"
                : $"public F(0) = 0\npublic F(1) = {{\n    N = load('{next}')\n    N.F(1)\n}}";
        }

        return (eager, deferred);
    }

    private static readonly string ChainMain = $"M = load('{Url("m0")}')\nM.F(1)";

    // ── F3: import depth is inherited across deferral ─────────────────────────

    [Fact]
    public async Task DeferredBranchInsideAModule_IsJudgedAtItsModulesImportDepth_AsEagerIs()
    {
        var a = Url("a");
        var b = Url("b");
        var limits = new SourceProcessingLimits { MaxModuleDepth = 1 };
        var main = $"M = load('{a}')\nM.F(1)";
        var eager = await KatLangEngine.RunAsync(main, Options(new Dictionary<string, string>
        {
            [a] = $"public N = load('{b}')\npublic F(x) = N.V",
            [b] = "public V = 7",
        }, limits));
        var deferredFiles = new Dictionary<string, string>
        {
            [a] = $"public F(0) = 0\npublic F(1) = {{\n    N = load('{b}')\n    N.V\n}}",
            [b] = "public V = 7",
        };

        var deferred = await KatLangEngine.RunAsync(main, Options(deferredFiles, limits));

        Assert.Equal("ModuleImportDepthExceeded@2/1", Verdict(eager));
        Assert.IsType<RunResult.EvalFailure>(deferred);
        Assert.Equal(Verdict(eager), Verdict(deferred));
        // The same wording as eager: the refused load and the depth it would reach.
        Assert.Contains($"load: importing '{b}' would reach depth 2, over the maximum of 1 nested module level.",
            ((RunResult.EvalFailure)deferred).Errors[0].Message);

        // Control: one level more and the branch loads.
        var allowed = await KatLangEngine.RunAsync(main, Options(deferredFiles, new SourceProcessingLimits { MaxModuleDepth = 2 }));
        Assert.Equal("ok 7", Verdict(allowed));
    }

    [Fact]
    public async Task EagerAndDeferredChains_ReachTheSameVerdict_AndNameTheSameDepth()
    {
        var refusals = 0;
        foreach (var limit in new[] { 1, 2, 3, 4 })
        foreach (var length in new[] { 1, 2, 3, 4, 5, 6 })
        {
            var (eagerFiles, deferredFiles) = Chain(length);
            var limits = new SourceProcessingLimits { MaxModuleDepth = limit };

            var eager = Verdict(await KatLangEngine.RunAsync(ChainMain, Options(eagerFiles, limits)));
            var deferred = Verdict(await KatLangEngine.RunAsync(ChainMain, Options(deferredFiles, limits)));

            // m_i sits at import depth i + 1, so the chain is refused exactly when it is longer
            // than the limit, at the first level past it.
            var expected = length > limit ? $"ModuleImportDepthExceeded@{limit + 1}/{limit}" : "ok 42";
            Assert.True(expected == eager, $"MaxModuleDepth={limit} chain={length}: eager {eager}, expected {expected}");
            Assert.True(eager == deferred, $"MaxModuleDepth={limit} chain={length}: eager {eager}, deferred {deferred}");
            if (length > limit)
                refusals++;
        }

        Assert.Equal(14, refusals);
    }

    [Fact]
    public async Task DeferralInsideAMaterializedBranch_AccumulatesImportDepth()
    {
        var a = Url("a");
        var b = Url("b");
        var files = new Dictionary<string, string>
        {
            [a] = $"public G(0) = 0\npublic G(1) = {{\n    M = load('{b}')\n    M.V\n}}",
            [b] = "public V = 7",
        };
        var main = $"F(0) = 0\nF(1) = {{\n    N = load('{a}')\n    N.G(1)\n}}\nF(1)";

        // main's branch (depth 0) loads a at depth 1; a's branch is deferred inside that
        // materialization at depth 1, so its load of b would reach depth 2.
        var refused = await SourceProvenance.ParseValidAsync(main, Options(files, new SourceProcessingLimits { MaxModuleDepth = 1 }));
        var outer = OnlyRegion(refused.Root);
        Assert.Equal(0, outer.ImportDepth);
        var refusal = await RunFlat(refused.Root).WaitAsync(WaitLimit);
        Assert.Equal("ModuleImportDepthExceeded@2/1", Verdict(refusal));
        Assert.Equal(0, outer.Loader.SourceBudget.CurrentDepth);
        Assert.Equal(1, outer.Loader.SourceBudget.PeakDepth);

        var allowed = await SourceProvenance.ParseValidAsync(main, Options(files, new SourceProcessingLimits { MaxModuleDepth = 2 }));
        var region = OnlyRegion(allowed.Root);
        Assert.Equal("ok 7", Verdict(await RunFlat(allowed.Root).WaitAsync(WaitLimit)));
        Assert.Equal(0, region.Loader.SourceBudget.CurrentDepth);
        Assert.Equal(2, region.Loader.SourceBudget.PeakDepth);
        // The nested region was deferred inside the materialization, at the resumed depth plus a's frame.
        Assert.True(region.TryGetMaterialized(out var body));
        Assert.Equal(1, OnlyRegion(body).ImportDepth);
    }

    [Fact]
    public async Task LongDeferredChain_UnderDepthOne_StopsAfterOneDownload()
    {
        // Without the inherited depth only the cumulative traversal ceiling stopped such a chain,
        // after 62 downloads. Run on a large dedicated stack so a regression fails by its counts
        // rather than by exhausting the test host's stack.
        var (_, files) = Chain(24);
        var downloads = 0;
        var options = new RunOptions
        {
            SourceProcessingLimits = new SourceProcessingLimits { MaxModuleDepth = 1 },
            DownloadCode = (url, _) =>
            {
                Interlocked.Increment(ref downloads);
                return ValueTask.FromResult(files[url]);
            },
        };

        var result = await OnLargeStack(() => KatLangEngine.RunAsync(ChainMain, options)).WaitAsync(WaitLimit);

        Assert.Equal("ModuleImportDepthExceeded@2/1", Verdict(result));
        Assert.Contains($"'{Url("m1")}'", ((RunResult.EvalFailure)result).Errors[0].Message);
        Assert.Equal(1, downloads);
    }

    private static Task<T> OnLargeStack<T>(Func<Task<T>> run)
    {
        var completion = new TaskCompletionSource<T>(TaskCreationOptions.RunContinuationsAsynchronously);
        var thread = new Thread(() =>
        {
            try { completion.SetResult(run().GetAwaiter().GetResult()); }
            catch (Exception error) { completion.SetException(error); }
        }, 16 * 1024 * 1024);
        thread.Start();
        return completion.Task;
    }

    public enum DepthOutcome { Success, LoadFailure, DepthRefusal, Cancellation }

    [Theory]
    [InlineData(DepthOutcome.Success)]
    [InlineData(DepthOutcome.LoadFailure)]
    [InlineData(DepthOutcome.DepthRefusal)]
    [InlineData(DepthOutcome.Cancellation)]
    public async Task EveryMaterializationOutcome_LeavesTheLiveImportDepthAtZero(DepthOutcome outcome)
    {
        // The region sits inside module a, so it records import depth 1 and the materialization
        // resumes there: a scope that did not restore would leave the run at depth 1.
        var a = Url("a");
        var b = Url("b");
        var started = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        async ValueTask<string> Download(string url, CancellationToken cancellationToken)
        {
            if (url == a)
                return $"public F(0) = 0\npublic F(1) = {{\n    N = load('{b}')\n    N.V\n}}";
            switch (outcome)
            {
                case DepthOutcome.LoadFailure:
                    throw new InvalidOperationException("transport failure");
                case DepthOutcome.Cancellation:
                    started.TrySetResult();
                    await Task.Delay(Timeout.Infinite, cancellationToken);
                    break;
            }

            return "public V = 7";
        }

        var parsed = await SourceProvenance.ParseValidAsync($"M = load('{a}')\nM.F(1)", new RunOptions
        {
            DownloadCode = Download,
            SourceProcessingLimits = new SourceProcessingLimits { MaxModuleDepth = outcome == DepthOutcome.DepthRefusal ? 1 : 2 },
        });
        var region = OnlyRegion(parsed.Root);
        var budget = region.Loader.SourceBudget;
        Assert.Equal(1, region.ImportDepth);
        Assert.Equal(0, budget.CurrentDepth);

        if (outcome == DepthOutcome.Cancellation)
        {
            using var cancellation = new CancellationTokenSource();
            var run = RunFlat(parsed.Root, cancellation.Token);
            await started.Task.WaitAsync(WaitLimit);
            // While the branch's download is in flight the walk is inside b's module frame.
            Assert.Equal(2, budget.CurrentDepth);
            cancellation.Cancel();
            await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.WaitAsync(WaitLimit));
            await WaitForGate(region);
        }
        else
        {
            var result = await RunFlat(parsed.Root).WaitAsync(WaitLimit);
            Assert.Equal(outcome switch
            {
                DepthOutcome.Success => "ok 7",
                DepthOutcome.LoadFailure => nameof(KatLangErrorCode.LoadFetchFailed),
                _ => "ModuleImportDepthExceeded@2/1",
            }, Verdict(result));
        }

        Assert.Equal(0, budget.CurrentDepth);
        Assert.Equal(outcome == DepthOutcome.DepthRefusal ? 1 : 2, budget.PeakDepth);
        Assert.Equal(0, region.Loader.InProgressModuleCount);
    }

    // ── F4: an attempt that publishes nothing releases its own splices ───────

    private const string GoodPadding = "public G = 1\n";
    private static readonly string GoodSource = GoodPadding + new string(' ', 400) + "\n";

    [Fact]
    public async Task TransientFetchFailures_KeepTheAggregateFlat_AndTheRecoveringAttemptSucceeds()
    {
        // The branch splices a cached `good` and loads a `flaky` module whose transport fails
        // four times. The aggregate admits the program plus four splices of `good`: a failed
        // attempt that kept its splice would exhaust it before the transport recovers.
        var good = Url("good");
        var flaky = Url("flaky");
        var main = $"F(0) = 0\nF(1) = {{\n    open '{good}'\n    N = load('{flaky}')\n    G + N.V\n}}\nF(1)";
        var failures = 4;
        var parsed = await SourceProvenance.ParseValidAsync(main, new RunOptions
        {
            DownloadCode = (url, _) =>
            {
                if (url == flaky && Interlocked.Decrement(ref failures) >= 0)
                    throw new InvalidOperationException("transient 503");
                return ValueTask.FromResult(url == good ? GoodSource : "public V = 2");
            },
            SourceProcessingLimits = new SourceProcessingLimits { MaxAggregateSourceLength = main.Length + 4L * GoodSource.Length },
        });
        var region = OnlyRegion(parsed.Root);
        var budget = region.Loader.SourceBudget;
        Assert.Equal(main.Length, budget.AggregateSource);

        for (var attempt = 1; attempt <= 4; attempt++)
        {
            var failed = await RunFlat(parsed.Root).WaitAsync(WaitLimit);
            Assert.Equal(nameof(KatLangErrorCode.LoadFetchFailed), Verdict(failed));
            // `good`'s download in the first attempt stays charged; no splice does.
            Assert.Equal(main.Length + GoodSource.Length, budget.AggregateSource);
            Assert.Equal(1 + attempt, budget.ModuleCount);
        }

        var recovered = await RunFlat(parsed.Root).WaitAsync(WaitLimit);
        Assert.Equal("ok 3", Verdict(recovered));
        Assert.True(region.IsMaterialized);
        // The published attempt keeps its charges: good's splice and flaky's download.
        Assert.Equal(main.Length + 2L * GoodSource.Length + "public V = 2".Length, budget.AggregateSource);
        Assert.Equal(5, region.MaterializationAttempts);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task UnfinishedNestedModules_ReleaseTheirSplicesAndKeepParsedSource(bool cancel)
    {
        var shared = Url("shared");
        var outer = Url("outer");
        var inner = Url("inner");
        var completed = Url("completed");
        var flaky = Url("flaky");
        const string sharedSource = "public G = 1";
        var outerSource = $"N = load('{inner}')\npublic V = N.V";
        var innerSource = $"open '{shared}'\nA = load('{completed}')\nB = load('{flaky}')\npublic V = G + A.V + B.V";
        var completedSource = $"open '{shared}'\npublic V = G";
        const string flakySource = "public V = 2";
        var downloads = 0;
        var started = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var files = new Dictionary<string, string>
        {
            [shared] = sharedSource,
            [outer] = outerSource,
            [inner] = innerSource,
            [completed] = completedSource,
            [flaky] = flakySource,
        };
        async ValueTask<string> Download(string url, CancellationToken cancellationToken)
        {
            if (url == flaky && Interlocked.Increment(ref downloads) == 1)
            {
                if (!cancel)
                    throw new InvalidOperationException("transient transport failure");

                started.SetResult();
                await Task.Delay(Timeout.Infinite, cancellationToken);
            }

            return files[url];
        }

        var main = $"Eager = load('{shared}')\nF(0) = 0\nF(1) = {{\n    N = load('{outer}')\n    N.V\n}}\nF(1)";
        var parsed = await SourceProvenance.ParseValidAsync(main, new RunOptions { DownloadCode = Download });
        var region = OnlyRegion(parsed.Root);
        var budget = region.Loader.SourceBudget;
        var afterParse = main.Length + sharedSource.Length;
        Assert.Equal(afterParse, budget.AggregateSource);

        using var cancellation = new CancellationTokenSource();
        var first = RunFlat(parsed.Root, cancellation.Token);
        if (cancel)
        {
            await started.Task.WaitAsync(WaitLimit);
            cancellation.Cancel();
            var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => first.WaitAsync(WaitLimit));
            Assert.Equal(cancellation.Token, error.CancellationToken);
            await WaitForGate(region);
        }
        else
        {
            Assert.Equal(nameof(KatLangErrorCode.LoadFetchFailed), Verdict(await first.WaitAsync(WaitLimit)));
        }

        var completedWeight = completedSource.Length + sharedSource.Length;
        var afterFailure = afterParse + outerSource.Length + innerSource.Length + completedWeight;
        // The inner walk's direct splice is released. The completed sibling's splice remains
        // part of its cached weight, and the two uncached modules' parsed text stays charged.
        Assert.Equal(afterFailure, budget.AggregateSource);
        Assert.Equal(5, budget.ModuleCount);
        Assert.Equal(2, region.Loader.CachedModuleCount);
        Assert.Equal(0, budget.CurrentDepth);
        Assert.False(region.IsMaterialized);

        Assert.Equal("ok 4", Verdict(await RunFlat(parsed.Root).WaitAsync(WaitLimit)));
        Assert.Equal(afterFailure + outerSource.Length + innerSource.Length + sharedSource.Length + completedWeight + flakySource.Length,
            budget.AggregateSource);
        Assert.Equal(8, budget.ModuleCount);
        Assert.Equal(5, region.Loader.CachedModuleCount);
    }

    [Fact]
    public async Task FrontEndErrorInTheBody_RetriedAttemptsChargeOnlyTheRealDownload()
    {
        var good = Url("good");
        var b = Url("b");
        const string bSource = "public V = 2";
        var main = $"Eager = load('{good}')\nF(0) = 0\nF(1) = {{\n    open '{good}'\n    N = load('{b}')\n    G + N.V + Missing\n}}\nF(1)";
        var parsed = await SourceProvenance.ParseValidAsync(main,
            Options(new Dictionary<string, string> { [good] = GoodSource, [b] = bSource }));
        var region = OnlyRegion(parsed.Root);
        var budget = region.Loader.SourceBudget;
        var afterParse = budget.AggregateSource;
        Assert.Equal(main.Length + GoodSource.Length, afterParse);

        for (var attempt = 1; attempt <= 4; attempt++)
        {
            var failed = await RunFlat(parsed.Root).WaitAsync(WaitLimit);
            Assert.Equal(nameof(KatLangErrorCode.UndeclaredIdentifier), Verdict(failed));
            Assert.False(region.IsMaterialized);
            // Exactly b's download, once; good's splice is released by every attempt.
            Assert.Equal(afterParse + bSource.Length, budget.AggregateSource);
            Assert.Equal(2, budget.ModuleCount);
            Assert.Equal(2, region.Loader.CachedModuleCount);
        }
    }

    // The exposure pass reads the declaring level's summaries through TryGetValue (the program
    // declares `Local = Root + 1`), which is where this gate holds the compile. The same hook as
    // BranchLazyModuleLoadingTests.LastConsumerLeavingDuringFinalization_CannotPublishTheAbandonedBody.
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

        public IEnumerator<KeyValuePair<string, RequirementSet>> GetEnumerator()
            => inner.GetEnumerator();

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    [Fact]
    public async Task AttemptAbandonedDuringTheCompile_ChargesOnlyItsDownload_AndARetrySucceeds()
    {
        var good = Url("good");
        var a = Url("a");
        const string aSource = "public A = 1";
        var aRelease = new TaskCompletionSource<string>(TaskCreationOptions.RunContinuationsAsynchronously);
        var parsed = await SourceProvenance.ParseValidAsync(
            $"Root = 1\nEager = load('{good}')\nF(0) = {{\n    open '{good}', '{a}'\n    Local = Root + 1\n    A + G + Local\n}}\nF(1) = 0\nF(0)",
            new RunOptions
            {
                DownloadCode = (url, _) => url == good ? ValueTask.FromResult(GoodSource) : new ValueTask<string>(aRelease.Task),
            });
        var original = OnlyRegion(parsed.Root);
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        using var release = new ManualResetEventSlim();
        using var cancellation = new CancellationTokenSource();
        PropertyExposureResolver.SummaryScope GateDeclaringLevel(PropertyExposureResolver.SummaryScope scope)
            => new(scope.Parent is null ? null : GateDeclaringLevel(scope.Parent), scope.PropertyScope,
                scope.PropertyScope.TryLookupOwnProperty("Root") is not null
                    ? new GatedSummaries(scope.Summaries, () =>
                    {
                        entered.SetResult();
                        Assert.True(release.Wait(WaitLimit));
                    })
                    : scope.Summaries,
                scope.Parameters, scope.Algorithm);
        var region = original.WithExposure(new PropertyExposureResolver.DeferredBranchContext(GateDeclaringLevel(original.Exposure!.Scope)));
        var budget = region.Loader.SourceBudget;
        var before = budget.AggregateSource;

        var pending = region.MaterializeAsync(cancellation.Token).AsTask();
        aRelease.SetResult(aSource);
        try
        {
            await entered.Task.WaitAsync(WaitLimit);
            cancellation.Cancel();
            await Assert.ThrowsAnyAsync<OperationCanceledException>(() => pending.WaitAsync(WaitLimit));
        }
        finally
        {
            release.Set();
        }

        await WaitForGate(region);
        Assert.False(region.IsMaterialized);
        // a's download stays charged; the attempt's splice of good does not.
        Assert.Equal(before + aSource.Length, budget.AggregateSource);

        Assert.False((await region.MaterializeAsync(CancellationToken.None).AsTask().WaitAsync(WaitLimit)).IsError);
        Assert.True(region.IsMaterialized);
        // The published retry keeps both splices.
        Assert.Equal(before + aSource.Length + GoodSource.Length + aSource.Length, budget.AggregateSource);
    }

    [Fact]
    public async Task CancellationDuringADownload_ReleasesTheAttemptsSplicesExactlyOnce()
    {
        // The attempt splices the cached `shared`, downloads and completes `fresh`, then is
        // cancelled during `slow`'s download. The load releases the attempt's ledger on
        // cancellation and the region releases it again for the unpublished attempt: the second
        // release must find nothing to subtract.
        var shared = Url("shared");
        var fresh = Url("fresh");
        var slow = Url("slow");
        const string sharedSource = "public V = 40";
        const string freshSource = "public U = 0";
        const string slowSource = "public W = 2";
        var slowStarted = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var slowRelease = new TaskCompletionSource<string>(TaskCreationOptions.RunContinuationsAsynchronously);
        async ValueTask<string> Download(string url, CancellationToken cancellationToken)
        {
            if (url == shared)
                return sharedSource;
            if (url == fresh)
                return freshSource;
            slowStarted.TrySetResult();
            return await slowRelease.Task.WaitAsync(cancellationToken);
        }

        var main = $"S = load('{shared}')\nF(0) = 0\nF(1) = {{\n    open '{shared}', '{fresh}', '{slow}'\n    V + U + W\n}}\nF(1)";
        var parsed = await SourceProvenance.ParseValidAsync(main, new RunOptions { DownloadCode = Download });
        var region = OnlyRegion(parsed.Root);
        var budget = region.Loader.SourceBudget;
        var before = budget.AggregateSource;
        Assert.Equal(main.Length + sharedSource.Length, before);

        using (var cancellation = new CancellationTokenSource())
        {
            var run = RunFlat(parsed.Root, cancellation.Token);
            await slowStarted.Task.WaitAsync(WaitLimit);
            // In flight: shared's splice and fresh's download are charged.
            Assert.Equal(before + sharedSource.Length + freshSource.Length, budget.AggregateSource);
            cancellation.Cancel();
            await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.WaitAsync(WaitLimit));
        }

        await WaitForGate(region);
        // Exactly the earlier value plus the download that completed, never below.
        Assert.Equal(before + freshSource.Length, budget.AggregateSource);
        Assert.Equal(3, budget.ModuleCount);

        slowRelease.SetResult(slowSource);
        var retry = await RunFlat(parsed.Root).WaitAsync(WaitLimit);
        Assert.Equal("ok 42", Verdict(retry));
        Assert.Equal(before + freshSource.Length + sharedSource.Length + freshSource.Length + slowSource.Length,
            budget.AggregateSource);
    }

    [Fact]
    public async Task Residual_SiblingCompletedByACancelledAttempt_StaysCharged_AndRetriesDoNotClimb()
    {
        // By design (rejected alternative: a "prepaid" splice): a module an unpublished attempt
        // downloaded and cached stays charged, and its next splice charges again. Under an
        // aggregate that exactly fits the program, the retry is then refused until the tree is
        // parsed again. Over-refusal only, and stable: retries never climb. Pinned so that a
        // change to it is deliberate.
        var a = Url("a");
        var b = Url("b");
        var aSource = "public A = 1\n" + new string(' ', 300) + "\n";
        const string bSource = "public B = 2";
        var main = $"F(0) = 0\nF(1) = {{\n    open '{a}'\n    N = load('{b}')\n    A + N.B\n}}\nF(1)";
        var limit = main.Length + (long)aSource.Length + bSource.Length;
        var downloadsOfB = 0;
        var firstBStarted = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var options = new RunOptions
        {
            DownloadCode = async (url, cancellationToken) =>
            {
                if (url == a)
                    return aSource;
                if (Interlocked.Increment(ref downloadsOfB) == 1)
                {
                    firstBStarted.TrySetResult();
                    await Task.Delay(Timeout.Infinite, cancellationToken);
                }

                return bSource;
            },
            SourceProcessingLimits = new SourceProcessingLimits { MaxAggregateSourceLength = limit },
        };

        // Control: without the cancelled attempt the program fits exactly.
        var control = await SourceProvenance.ParseValidAsync(main, new RunOptions
        {
            DownloadCode = (url, _) => ValueTask.FromResult(url == a ? aSource : bSource),
            SourceProcessingLimits = new SourceProcessingLimits { MaxAggregateSourceLength = limit },
        });
        Assert.Equal("ok 3", Verdict(await RunFlat(control.Root).WaitAsync(WaitLimit)));
        Assert.Equal(limit, OnlyRegion(control.Root).Loader.SourceBudget.AggregateSource);

        var parsed = await SourceProvenance.ParseValidAsync(main, options);
        var region = OnlyRegion(parsed.Root);
        var budget = region.Loader.SourceBudget;
        using (var cancellation = new CancellationTokenSource())
        {
            var run = RunFlat(parsed.Root, cancellation.Token);
            await firstBStarted.Task.WaitAsync(WaitLimit);
            cancellation.Cancel();
            await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.WaitAsync(WaitLimit));
        }

        await WaitForGate(region);
        Assert.Equal(main.Length + aSource.Length, budget.AggregateSource);

        long? settled = null;
        for (var retry = 1; retry <= 3; retry++)
        {
            var refused = await RunFlat(parsed.Root).WaitAsync(WaitLimit);
            Assert.Equal(nameof(KatLangErrorCode.AggregateSourceLengthExceeded), Verdict(refused));
            Assert.Contains($"splicing the already loaded '{a}' again", KatLangError.FromEvalError(refused.Error).Message);
            Assert.False(region.IsMaterialized);
            // The first retry downloads b (kept); from then on nothing climbs.
            settled ??= budget.AggregateSource;
            Assert.Equal(limit, budget.AggregateSource);
            Assert.Equal(settled, budget.AggregateSource);
        }

        Assert.Equal(2, downloadsOfB);
    }
}
