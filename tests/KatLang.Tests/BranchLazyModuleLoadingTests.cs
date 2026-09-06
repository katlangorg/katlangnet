using System.Numerics;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// B2c — branch-lazy module loading, the engine-level acceptance matrix. A module dependency
/// owned exclusively by a conditional branch body is fetched, parsed, elaborated, and
/// budget-charged only after evaluation SELECTS that branch; alternatives that are never
/// selected perform zero module work and cannot fail because of their own dependencies.
/// Shared dependencies (outer loads, family-owned opens) keep their eager timing. Every test
/// uses deterministic in-memory downloaders that count fetches per URL — no network.
/// Host-only by nature: Lean's input model has no external modules and no demand timing.
/// </summary>
public class BranchLazyModuleLoadingTests
{
    private const string ModuleA = "https://katlang.org/lazy/a.kat";
    private const string ModuleB = "https://katlang.org/lazy/b.kat";
    private const string ModuleC = "https://katlang.org/lazy/c.kat";
    private const string ModuleY = "https://katlang.org/lazy/y.kat";
    private const string ModuleZ = "https://katlang.org/lazy/z.kat";
    private const string Missing = "https://katlang.org/lazy/missing.kat";

    private sealed class CountingModules
    {
        private readonly Dictionary<string, string> _files;

        public CountingModules(params (string Url, string Source)[] files)
            => _files = files.ToDictionary(file => file.Url, file => file.Source, StringComparer.Ordinal);

        public Dictionary<string, int> Fetches { get; } = new(StringComparer.Ordinal);

        public int this[string url] => Fetches.GetValueOrDefault(url);

        public ValueTask<string> Download(string url, CancellationToken cancellationToken)
        {
            Fetches[url] = this[url] + 1;
            return _files.TryGetValue(url, out var source)
                ? ValueTask.FromResult(source)
                : throw new Exception($"404: {url}");
        }

        public RunOptions Options => new() { DownloadCode = Download };
    }

    private static CountingModules Modules()
        => new((ModuleA, "public A = 1"), (ModuleB, "public B = 2"), (ModuleC, "public C = 3"));

    private static string Display(RunResult result) => result.ToDisplayString().ReplaceLineEndings("\n");

    private static int LineOf(string source, string fragment)
    {
        var lines = source.Split('\n');
        var index = Array.FindIndex(lines, line => line.Contains(fragment, StringComparison.Ordinal));
        Assert.True(index >= 0, $"fragment '{fragment}' not found");
        return index + 1;
    }

    private static Algorithm.Conditional Family(Algorithm root, string name)
        => Assert.IsType<Algorithm.Conditional>(root.Properties.Single(property => property.Name == name).Value);

    private static DeferredModuleRegion Region(Algorithm root, string family, int branch)
    {
        Assert.True(DeferredModuleRegions.TryGet(Family(root, family).Branches[branch].Body, out var region));
        return region!;
    }

    // ── A. A dead branch may contain an unavailable module ──────────────────

    [Fact]
    public async Task DeadBranchWithMissingModule_IsNeverFetched_AndSelectingItReportsTheOrdinaryLoadFailure()
    {
        var branch = $"F(0) = 42\nF(1) = {{\n    open '{Missing}'\n    X\n}}\n";
        var modules = Modules();

        var dead = await KatLangEngine.RunAsync(branch + "F(0)", modules.Options);

        Assert.Equal("42", Display(Assert.IsType<RunResult.Success>(dead)));
        Assert.Equal(0, modules[Missing]);

        var selected = await KatLangEngine.RunAsync(branch + "F(1)", modules.Options);

        var failure = Assert.IsType<RunResult.EvalFailure>(selected);
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.LoadFetchFailed, error.Code);
        Assert.Contains(Missing, error.Message, StringComparison.Ordinal);
        Assert.Equal(1, modules[Missing]);
        // Provenance: the branch-local `open` site, not the family call or the selection point.
        Assert.Equal(LineOf(branch, "open '"), error.StartLine);
        Assert.Equal(10, error.StartColumn);

        // The very diagnostic the equivalent eager load reports — only its timing differs.
        var eager = Assert.IsType<RunResult.ParseFailure>(
            await KatLangEngine.RunAsync($"open '{Missing}'\nX", Modules().Options));
        var eagerError = Assert.Single(eager.Errors, candidate => candidate.Code == KatLangErrorCode.LoadFetchFailed);
        Assert.Equal(eagerError.Code, error.Code);
        Assert.EndsWith(eagerError.Message, error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task FailedMaterialization_IsNeverCached_AndDoesNotPoisonTheRegion()
    {
        var modules = Modules();
        var source = $"F(0) = 42\nF(1) = {{\n    open '{Missing}'\n    X\n}}\nF(1)";
        var parsed = await Parser.ParseAsync(source, modules.Options);
        Assert.False(parsed.HasErrors);
        var region = Region(parsed.Root, "F", 1);

        var first = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));
        var second = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));

        Assert.True(first.IsError);
        Assert.True(second.IsError);
        Assert.Equal(KatLangErrorCode.LoadFetchFailed, first.Error.Code);
        Assert.Equal(KatLangErrorCode.LoadFetchFailed, second.Error.Code);
        // Like the module cache, a failed attempt is not remembered: the next selection retries.
        Assert.Equal(2, modules[Missing]);
        Assert.Equal(2, region.MaterializationAttempts);
        Assert.False(region.IsMaterialized);
    }

    [Fact]
    public async Task FailedNestedDependency_CannotPoisonTheParentModuleCache()
    {
        var modules = new CountingModules((ModuleA, $"open '{Missing}'\npublic A = 1"));
        var parsed = await Parser.ParseAsync(TwoAlternatives + "F(0)", modules.Options);
        Assert.False(parsed.HasErrors);
        var region = Region(parsed.Root, "F", 0);

        for (var attempt = 1; attempt <= 2; attempt++)
        {
            var result = await RunFlat(parsed.Root);

            Assert.True(result.IsError);
            Assert.Equal(KatLangErrorCode.LoadFetchFailed, result.Error.Code);
            Assert.Equal(attempt, modules[ModuleA]);
            Assert.Equal(attempt, modules[Missing]);
            Assert.False(region.IsMaterialized);
            Assert.Equal(0, region.Loader.CachedModuleCount);
            Assert.Empty(parsed.Diagnostics);
        }
    }

    // ── B. Two alternative modules ──────────────────────────────────────────

    private const string TwoAlternatives =
        $"F(0) = {{\n    open '{ModuleA}'\n    A\n}}\nF(1) = {{\n    open '{ModuleB}'\n    B\n}}\n";

    [Fact]
    public async Task TwoAlternatives_OnlyTheSelectedBranchIsFetched()
    {
        var modules = Modules();

        var result = await KatLangEngine.RunAsync(TwoAlternatives + "F(0)", modules.Options);

        Assert.Equal("1", Display(Assert.IsType<RunResult.Success>(result)));
        Assert.Equal(1, modules[ModuleA]);
        Assert.Equal(0, modules[ModuleB]);
    }

    [Fact]
    public async Task TwoAlternatives_SelectedInOneRun_EachMaterializesOnce()
    {
        var modules = Modules();

        var result = await KatLangEngine.RunAsync(TwoAlternatives + "F(0) + F(1) + F(0) + F(1)", modules.Options);

        Assert.Equal("6", Display(Assert.IsType<RunResult.Success>(result)));
        Assert.Equal(1, modules[ModuleA]);
        Assert.Equal(1, modules[ModuleB]);
    }

    [Fact]
    public async Task DynamicSelection_InsideTheProgram_IsLazyToo()
    {
        // The selected branch is only known at evaluation: materialization happens at the
        // real branch-selection boundary, not by static call analysis.
        var modules = Modules();

        var result = await KatLangEngine.RunAsync(
            TwoAlternatives + "Choose = count([7]) - 1\nF(Choose)", modules.Options);

        Assert.Equal("1", Display(Assert.IsType<RunResult.Success>(result)));
        Assert.Equal(1, modules[ModuleA]);
        Assert.Equal(0, modules[ModuleB]);
    }

    [Fact]
    public async Task SelectionThroughCallbackAndDotCallPositions_IsLazyToo()
    {
        var modules = Modules();

        var callback = await KatLangEngine.RunAsync(TwoAlternatives + "[0, 0].map(F)", modules.Options);
        Assert.Equal("[1, 1]", Display(Assert.IsType<RunResult.Success>(callback)));

        var dotted = await KatLangEngine.RunAsync(
            $"Lib = {{\n    public {TwoAlternatives.Replace("\nF(1)", "\n    public F(1)")}}}\nLib.F(0)",
            modules.Options);
        Assert.Equal("1", Display(Assert.IsType<RunResult.Success>(dotted)));

        Assert.Equal(2, modules[ModuleA]);
        Assert.Equal(0, modules[ModuleB]);
    }

    // ── C. Nested conditional laziness ──────────────────────────────────────

    [Fact]
    public async Task NestedFamilies_MaterializeOnlyTheSelectedPath()
    {
        var modules = Modules();
        var source =
            $"F(0) = {{\n    G(0) = {{\n        open '{ModuleA}'\n        A\n    }}\n    G(1) = {{\n        open '{ModuleB}'\n        B\n    }}\n    G(0)\n}}\n" +
            $"F(1) = {{\n    open '{ModuleC}'\n    C\n}}\nF(0)";

        var result = await KatLangEngine.RunAsync(source, modules.Options);

        Assert.Equal("1", Display(Assert.IsType<RunResult.Success>(result)));
        Assert.Equal(1, modules[ModuleA]);
        Assert.Equal(0, modules[ModuleB]);
        Assert.Equal(0, modules[ModuleC]);
    }

    [Fact]
    public async Task NestedFamilies_InnerAlternativesStayDeferredAfterTheOuterBranchMaterializes()
    {
        var modules = Modules();
        var source =
            $"F(0) = {{\n    G(0) = {{\n        open '{ModuleA}'\n        A\n    }}\n    G(1) = {{\n        open '{ModuleB}'\n        B\n    }}\n    G(0)\n}}\nF(1) = 0\nF(0)";
        var parsed = await Parser.ParseAsync(source, modules.Options);
        Assert.False(parsed.HasErrors);
        var outer = Region(parsed.Root, "F", 0);

        var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));

        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([1m], result.Value);
        Assert.True(outer.TryGetMaterialized(out var materializedOuter));
        var inner = Assert.IsType<Algorithm.Conditional>(
            materializedOuter!.Properties.Single(property => property.Name == "G").Value);
        Assert.True(DeferredModuleRegions.TryGet(inner.Branches[0].Body, out var selectedInner));
        Assert.True(DeferredModuleRegions.TryGet(inner.Branches[1].Body, out var unselectedInner));
        Assert.True(selectedInner!.IsMaterialized);
        Assert.False(unselectedInner!.IsMaterialized);
        Assert.Equal(0, unselectedInner.MaterializationAttempts);
        Assert.Equal(0, modules[ModuleB]);
    }

    // ── D. Repeated selected branch ─────────────────────────────────────────

    [Fact]
    public async Task RepeatedSelection_MaterializesOnce_WithinARunAndAcrossRunsOfOneParse()
    {
        var modules = Modules();
        var source = TwoAlternatives + "F(0) + F(0) + F(0)";
        var parsed = await Parser.ParseAsync(source, modules.Options);
        Assert.False(parsed.HasErrors);
        var region = Region(parsed.Root, "F", 0);

        var first = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));
        var second = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));

        Assert.Equal([3m], first.Value);
        Assert.Equal([3m], second.Value);
        Assert.Equal(1, modules[ModuleA]);
        Assert.Equal(1, region.MaterializationAttempts);
        Assert.Equal(1, region.Loader.CachedModuleCount);
    }

    [Fact]
    public async Task ConcurrentSelections_ShareOneMaterialization()
    {
        var gate = new TaskCompletionSource<string>(TaskCreationOptions.RunContinuationsAsynchronously);
        var fetches = 0;
        var options = new RunOptions
        {
            DownloadCode = (url, _) =>
            {
                Interlocked.Increment(ref fetches);
                return new ValueTask<string>(gate.Task);
            },
        };
        var parsed = await Parser.ParseAsync(TwoAlternatives + "F(0)", options);
        Assert.False(parsed.HasErrors);
        var region = Region(parsed.Root, "F", 0);

        var first = Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));
        var second = Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));
        Assert.False(first.IsCompleted);
        Assert.False(second.IsCompleted);
        Assert.Equal(1, fetches);

        gate.SetResult("public A = 1");

        Assert.Equal([1m], (await first).Value);
        Assert.Equal([1m], (await second).Value);
        Assert.Equal(1, fetches);
        Assert.Equal(1, region.MaterializationAttempts);
    }

    // ── E. Ordinary outer loads keep their timing ───────────────────────────

    [Fact]
    public async Task OuterLoad_KeepsEagerTiming_WhileBranchLoadsStayLazy()
    {
        var modules = Modules();

        var result = await KatLangEngine.RunAsync(
            $"open '{ModuleA}'\nF(0) = A\nF(1) = {{\n    open '{ModuleB}'\n    B\n}}\nF(0)", modules.Options);

        Assert.Equal("1", Display(Assert.IsType<RunResult.Success>(result)));
        Assert.Equal(1, modules[ModuleA]);
        Assert.Equal(0, modules[ModuleB]);

        var failing = await KatLangEngine.RunAsync(
            $"open '{Missing}'\nF(0) = 42\nF(n) = n\nF(0)", modules.Options);

        // An outer failing load is still a front-end (parse-time) failure: nothing is deferred.
        var failure = Assert.IsType<RunResult.ParseFailure>(failing);
        Assert.Equal(KatLangErrorCode.LoadFetchFailed, Assert.Single(failure.Errors).Code);
        Assert.Equal(1, modules[Missing]);
    }

    // ── H. Provenance of a nested branch-local site ─────────────────────────

    [Fact]
    public async Task SelectedBranchFailure_ReportsTheNestedBranchLocalOpenSite()
    {
        var modules = Modules();
        var source = $"F(0) = 42\nF(1) = {{\n    G = {{\n        open '{Missing}'\n        X\n    }}\n    G\n}}\nF(1)";

        var result = await KatLangEngine.RunAsync(source, modules.Options);

        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);
        Assert.Equal(KatLangErrorCode.LoadFetchFailed, error.Code);
        Assert.Equal(LineOf(source, "open '"), error.StartLine);
        Assert.Equal(14, error.StartColumn);
    }

    // ── I. Policy and cycle failures in a dead branch ───────────────────────

    [Fact]
    public async Task PolicyRejectedModule_InDeadBranch_IsUntouched_AndSelectedReportsThePolicyFailure()
    {
        var modules = Modules();
        var branch = "F(0) = 42\nF(1) = {\n    open 'https://evil.example/x.kat'\n    X\n}\n";

        Assert.Equal("42", Display(Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(branch + "F(0)", modules.Options))));

        var selected = await KatLangEngine.RunAsync(branch + "F(1)", modules.Options);

        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(selected).Errors);
        Assert.Equal(KatLangErrorCode.InvalidLoadUrl, error.Code);
        Assert.Contains("evil.example", error.Message, StringComparison.Ordinal);
        // Policy rejects before any download, exactly as the eager load does.
        Assert.Empty(modules.Fetches);
    }

    [Fact]
    public async Task CyclicModuleChain_InDeadBranch_IsUntouched_AndSelectedReportsTheOrdinaryCycle()
    {
        var modules = new CountingModules(
            (ModuleY, $"open '{ModuleZ}'\npublic Y = 1"),
            (ModuleZ, $"open '{ModuleY}'\npublic Z = 2"));
        var branch = $"F(0) = 42\nF(1) = {{\n    open '{ModuleY}'\n    Y\n}}\n";

        Assert.Equal("42", Display(Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(branch + "F(0)", modules.Options))));
        Assert.Empty(modules.Fetches);

        var selected = await KatLangEngine.RunAsync(branch + "F(1)", modules.Options);

        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(selected).Errors);
        Assert.Equal(KatLangErrorCode.LoadCycle, error.Code);
        Assert.Equal(1, modules[ModuleY]);
        Assert.Equal(1, modules[ModuleZ]);
    }

    [Fact]
    public async Task ModuleBudget_IsChargedOnlyBySelectedBranches()
    {
        // Two lazy alternatives under a module-count ceiling of one: the dead branch charges
        // nothing, so the selected one fits; selecting the other afterwards would exceed the
        // ceiling exactly as an eager second load would.
        var modules = Modules();
        var options = new RunOptions
        {
            DownloadCode = modules.Download,
            SourceProcessingLimits = new SourceProcessingLimits { MaxModuleCount = 1 },
        };
        var parsed = await Parser.ParseAsync(TwoAlternatives + "F(0) + F(1)", options);
        Assert.False(parsed.HasErrors);

        var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));

        Assert.True(result.IsError);
        Assert.Equal(KatLangErrorCode.ModuleCountExceeded, result.Error.Code);
        Assert.Equal(1, modules[ModuleA]);
        Assert.Equal(0, modules[ModuleB]);

        var onlyFirst = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(
            (await Parser.ParseAsync(TwoAlternatives + "F(0)", new RunOptions
            {
                DownloadCode = Modules().Download,
                SourceProcessingLimits = new SourceProcessingLimits { MaxModuleCount = 1 },
            })).Root));
        Assert.Equal([1m], onlyFirst.Value);
    }

    /// <summary>
    /// A downloader that suspends INSIDE the request until released and reports what it
    /// observed per URL: whether the request started, the token it was handed, and whether
    /// it exited because that token was cancelled. This is what lets a test prove that
    /// cancellation reached the download itself rather than merely being observed by the
    /// caller while the request kept running.
    /// </summary>
    private sealed class GatedDownloader
    {
        private sealed class Request
        {
            public readonly TaskCompletionSource<string> Release = new(TaskCreationOptions.RunContinuationsAsynchronously);
            public readonly TaskCompletionSource Started = new(TaskCreationOptions.RunContinuationsAsynchronously);
            public readonly TaskCompletionSource Exited = new(TaskCreationOptions.RunContinuationsAsynchronously);
            public int Calls;
            public CancellationToken ObservedToken;
            public bool AbortedByCancellation;
        }

        private readonly object _lock = new();
        private readonly Dictionary<string, Request> _requests = new(StringComparer.Ordinal);

        private Request For(string url)
        {
            lock (_lock)
            {
                if (!_requests.TryGetValue(url, out var request))
                    _requests[url] = request = new Request();
                return request;
            }
        }

        public RunOptions Options => new() { DownloadCode = Download };

        public Task Started(string url) => For(url).Started.Task;

        public Task Exited(string url) => For(url).Exited.Task;

        public int Calls(string url) => For(url).Calls;

        public bool TokenWasCancelled(string url) => For(url).ObservedToken.IsCancellationRequested;

        public bool AbortedByCancellation(string url) => For(url).AbortedByCancellation;

        public void Release(string url, string source) => For(url).Release.TrySetResult(source);

        public async ValueTask<string> Download(string url, CancellationToken cancellationToken)
        {
            var request = For(url);
            Interlocked.Increment(ref request.Calls);
            request.ObservedToken = cancellationToken;
            request.Started.TrySetResult();
            try
            {
                return await request.Release.Task.WaitAsync(cancellationToken);
            }
            catch (OperationCanceledException) when (cancellationToken.IsCancellationRequested)
            {
                request.AbortedByCancellation = true;
                throw;
            }
            finally
            {
                request.Exited.TrySetResult();
            }
        }
    }

    private static Task<EvalResult<IReadOnlyList<Decimal128>>> RunFlat(Algorithm root, CancellationToken cancellationToken = default)
        => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), limits: null, cancellationToken);

    // ── J. Genuine suspension and cancellation ──────────────────────────────

    [Fact]
    public async Task UnselectedBranch_NeverStartsItsDownload_EvenWhenTheDownloaderWouldSuspend()
    {
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = (url, _) =>
            {
                calls++;
                return url == ModuleA
                    ? ValueTask.FromResult("public A = 1")
                    : new ValueTask<string>(new TaskCompletionSource<string>().Task);
            },
        };

        // The alternative's downloader would suspend forever: completing at all proves it was
        // never invoked.
        var result = await KatLangEngine.RunAsync(TwoAlternatives + "F(0)", options);

        Assert.Equal("1", Display(Assert.IsType<RunResult.Success>(result)));
        Assert.Equal(1, calls);
    }

    [Fact]
    public async Task SelectedBranch_AwaitsItsSuspendedDownload_AndResumesOnce()
    {
        var downloader = new GatedDownloader();

        var task = KatLangEngine.RunAsync(TwoAlternatives + "F(0)", downloader.Options);

        // Parsing completed without touching either module; evaluation is suspended inside
        // the selected branch's download.
        await downloader.Started(ModuleA);
        Assert.False(task.IsCompleted);
        Assert.Equal(1, downloader.Calls(ModuleA));

        downloader.Release(ModuleA, "public A = 1");

        Assert.Equal("1", Display(Assert.IsType<RunResult.Success>(await task)));
        Assert.Equal(1, downloader.Calls(ModuleA));
        Assert.Equal(0, downloader.Calls(ModuleB));
    }

    [Fact]
    public async Task EvaluationCancellation_ReachesAnInFlightDeferredDownload_AbortsIt_AndCachesNothing()
    {
        // The materialization exists only because THIS evaluation selected the branch, so the
        // evaluation's token cancels the download itself: the downloader's token is cancelled,
        // the request exits because of it, no body or module is cached, and the evaluation
        // reports cancellation with its own token. A later evaluation retries from scratch.
        var downloader = new GatedDownloader();
        var parsed = await Parser.ParseAsync(TwoAlternatives + "F(0)", downloader.Options);
        Assert.False(parsed.HasErrors);
        var region = Region(parsed.Root, "F", 0);
        using var cancellation = new CancellationTokenSource();

        var run = RunFlat(parsed.Root, cancellation.Token);
        await downloader.Started(ModuleA);
        Assert.False(run.IsCompleted);
        Assert.False(downloader.TokenWasCancelled(ModuleA));

        cancellation.Cancel();
        await downloader.Exited(ModuleA);

        Assert.True(downloader.TokenWasCancelled(ModuleA));
        Assert.True(downloader.AbortedByCancellation(ModuleA));
        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run);
        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.False(region.IsMaterialized);
        Assert.Equal(1, region.MaterializationAttempts);
        Assert.Equal(0, region.Loader.CachedModuleCount);

        // Retry: a fresh evaluation starts a fresh run and succeeds.
        downloader.Release(ModuleA, "public A = 1");
        var retry = await RunFlat(parsed.Root);

        Assert.Equal([1m], retry.Value);
        Assert.True(region.IsMaterialized);
        Assert.Equal(2, region.MaterializationAttempts);
        Assert.Equal(2, downloader.Calls(ModuleA));
        Assert.Equal(1, region.Loader.CachedModuleCount);
    }

    [Fact]
    public async Task EngineEvaluationCancellation_AbortsTheDeferredDownload_WithTheEvaluationToken()
    {
        var downloader = new GatedDownloader();
        using var cancellation = new CancellationTokenSource();
        var options = new RunOptions
        {
            EvaluationCancellationToken = cancellation.Token,
            DownloadCode = downloader.Download,
        };

        var task = KatLangEngine.RunAsync(TwoAlternatives + "F(0)", options);
        await downloader.Started(ModuleA);
        Assert.False(task.IsCompleted);

        cancellation.Cancel();
        await downloader.Exited(ModuleA);

        Assert.True(downloader.AbortedByCancellation(ModuleA));
        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => task);
        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.Equal(0, downloader.Calls(ModuleB));
    }

    [Fact]
    public async Task SourceProcessingCancellation_DuringALazyDownload_AbortsIt_WithTheHostTokenIdentity()
    {
        // The host's source-processing token stays authoritative for module work: it aborts
        // the download too, keeps its identity even though an evaluation token is also
        // configured, and leaves nothing cached.
        var downloader = new GatedDownloader();
        using var sourceCancellation = new CancellationTokenSource();
        using var evaluationCancellation = new CancellationTokenSource();
        var parsed = await Parser.ParseAsync(TwoAlternatives + "F(0)", new RunOptions
        {
            SourceProcessingCancellationToken = sourceCancellation.Token,
            DownloadCode = downloader.Download,
        });
        Assert.False(parsed.HasErrors);
        var region = Region(parsed.Root, "F", 0);

        var run = RunFlat(parsed.Root, evaluationCancellation.Token);
        await downloader.Started(ModuleA);

        sourceCancellation.Cancel();
        await downloader.Exited(ModuleA);

        Assert.True(downloader.AbortedByCancellation(ModuleA));
        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run);
        Assert.Equal(sourceCancellation.Token, exception.CancellationToken);
        Assert.False(evaluationCancellation.IsCancellationRequested);
        Assert.False(region.IsMaterialized);
        Assert.Equal(0, region.Loader.CachedModuleCount);
    }

    [Fact]
    public async Task CancellationWhileWaitingForTheGate_LeavesAnotherRegionsMaterializationUndisturbed()
    {
        // Region F holds the loader's gate inside its download; region G's evaluation is
        // queued behind it. Cancelling G's evaluation releases G at once (no attempt, no
        // download) and touches neither F's download nor its token; F completes normally, and
        // G materializes on its next selection.
        var downloader = new GatedDownloader();
        var source = $"F(0) = {{\n    open '{ModuleA}'\n    A\n}}\nF(1) = 0\nG(0) = {{\n    open '{ModuleB}'\n    B\n}}\nG(1) = 0\nF(0) + G(0)";
        var parsed = await Parser.ParseAsync(source, downloader.Options);
        Assert.False(parsed.HasErrors);
        var regionF = Region(parsed.Root, "F", 0);
        var regionG = Region(parsed.Root, "G", 0);
        using var cancellationF = new CancellationTokenSource();
        using var cancellationG = new CancellationTokenSource();

        var runF = regionF.MaterializeAsync(cancellationF.Token).AsTask();
        await downloader.Started(ModuleA);
        var runG = regionG.MaterializeAsync(cancellationG.Token).AsTask();
        Assert.False(runG.IsCompleted);
        Assert.Equal(0, regionG.MaterializationAttempts);
        Assert.Equal(0, downloader.Calls(ModuleB));

        cancellationG.Cancel();

        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => runG);
        Assert.Equal(cancellationG.Token, exception.CancellationToken);
        Assert.False(runF.IsCompleted);
        Assert.False(downloader.TokenWasCancelled(ModuleA));
        Assert.Equal(0, regionG.MaterializationAttempts);
        Assert.Equal(0, downloader.Calls(ModuleB));

        downloader.Release(ModuleA, "public A = 1");
        Assert.False((await runF).IsError);
        Assert.True(regionF.IsMaterialized);

        downloader.Release(ModuleB, "public B = 2");
        Assert.False((await regionG.MaterializeAsync(CancellationToken.None)).IsError);
        Assert.True(regionG.IsMaterialized);
        Assert.Equal(1, regionG.MaterializationAttempts);
        Assert.Equal(1, downloader.Calls(ModuleA));
        Assert.Equal(1, downloader.Calls(ModuleB));
    }

    [Fact]
    public async Task TwoConsumers_OneCancels_TheOtherStillGetsTheSharedMaterialization()
    {
        var downloader = new GatedDownloader();
        var parsed = await Parser.ParseAsync(TwoAlternatives + "F(0)", downloader.Options);
        Assert.False(parsed.HasErrors);
        var region = Region(parsed.Root, "F", 0);
        using var cancellationA = new CancellationTokenSource();
        using var cancellationB = new CancellationTokenSource();

        var runA = RunFlat(parsed.Root, cancellationA.Token);
        var runB = RunFlat(parsed.Root, cancellationB.Token);
        await downloader.Started(ModuleA);
        Assert.Equal(1, downloader.Calls(ModuleA));

        cancellationA.Cancel();

        // The cancelled consumer leaves with its own token; the shared download keeps running
        // for the consumer that still needs it.
        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => runA);
        Assert.Equal(cancellationA.Token, exception.CancellationToken);
        Assert.False(runB.IsCompleted);
        Assert.False(downloader.TokenWasCancelled(ModuleA));
        Assert.False(downloader.Exited(ModuleA).IsCompleted);

        downloader.Release(ModuleA, "public A = 1");

        Assert.Equal([1m], (await runB).Value);
        Assert.True(region.IsMaterialized);
        Assert.Equal(1, region.MaterializationAttempts);
        Assert.Equal(1, downloader.Calls(ModuleA));

        // The cancelled evaluation's retry is served from the cache.
        Assert.Equal([1m], (await RunFlat(parsed.Root)).Value);
        Assert.Equal(1, downloader.Calls(ModuleA));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task SourceCancellation_WhileWaitingForLoaderGate_IsAuthoritative(bool cancelEvaluation)
    {
        var modules = Modules();
        using var sourceCancellation = new CancellationTokenSource();
        using var evaluationCancellation = new CancellationTokenSource();
        var parsed = await Parser.ParseAsync(TwoAlternatives + "F(0)", new RunOptions
        {
            SourceProcessingCancellationToken = sourceCancellation.Token,
            DownloadCode = modules.Download,
        });
        Assert.False(parsed.HasErrors);
        var region = Region(parsed.Root, "F", 0);
        var gate = region.Loader.MaterializationGate;
        await gate.WaitAsync();
        try
        {
            var pending = region.MaterializeAsync(evaluationCancellation.Token).AsTask();
            Assert.False(pending.IsCompleted);

            sourceCancellation.Cancel();
            if (cancelEvaluation)
                evaluationCancellation.Cancel();

            var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(
                () => pending.WaitAsync(TimeSpan.FromSeconds(5)));
            Assert.Equal(sourceCancellation.Token, error.CancellationToken);
            Assert.Equal(0, region.MaterializationAttempts);
            Assert.False(region.IsMaterialized);
            Assert.Empty(modules.Fetches);
        }
        finally
        {
            evaluationCancellation.Cancel();
            gate.Release();
        }
    }

    [Fact]
    public async Task AllConsumersCancel_StopsTheUnderlyingWork_AndTheNextSelectionRetries()
    {
        var downloader = new GatedDownloader();
        var parsed = await Parser.ParseAsync(TwoAlternatives + "F(0)", downloader.Options);
        Assert.False(parsed.HasErrors);
        var region = Region(parsed.Root, "F", 0);
        using var cancellationA = new CancellationTokenSource();
        using var cancellationB = new CancellationTokenSource();

        var runA = RunFlat(parsed.Root, cancellationA.Token);
        var runB = RunFlat(parsed.Root, cancellationB.Token);
        await downloader.Started(ModuleA);

        cancellationA.Cancel();
        await Assert.ThrowsAnyAsync<OperationCanceledException>(() => runA);
        Assert.False(downloader.TokenWasCancelled(ModuleA));

        cancellationB.Cancel();
        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => runB);
        Assert.Equal(cancellationB.Token, exception.CancellationToken);
        await downloader.Exited(ModuleA);

        // Nobody needs the download any more: it was cancelled, and nothing was cached.
        Assert.True(downloader.TokenWasCancelled(ModuleA));
        Assert.True(downloader.AbortedByCancellation(ModuleA));
        Assert.False(region.IsMaterialized);
        Assert.Equal(1, region.MaterializationAttempts);
        Assert.Equal(0, region.Loader.CachedModuleCount);

        downloader.Release(ModuleA, "public A = 1");
        Assert.Equal([1m], (await RunFlat(parsed.Root)).Value);
        Assert.True(region.IsMaterialized);
        Assert.Equal(2, region.MaterializationAttempts);
        Assert.Equal(2, downloader.Calls(ModuleA));
    }

    [Fact]
    public async Task AlreadyCancelledEvaluationToken_NeverStartsAMaterialization()
    {
        var downloader = new GatedDownloader();
        var parsed = await Parser.ParseAsync(TwoAlternatives + "F(0)", downloader.Options);
        var region = Region(parsed.Root, "F", 0);
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();

        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(
            async () => await region.MaterializeAsync(cancellation.Token));

        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.Equal(0, region.MaterializationAttempts);
        Assert.Equal(0, downloader.Calls(ModuleA));
    }

    private sealed class GatedSummaries(
        IReadOnlyDictionary<string, PropertyExposureResolver.AnalysisSummary> inner,
        Action onEnumeration) : IReadOnlyDictionary<string, PropertyExposureResolver.AnalysisSummary>
    {
        private Action? _onEnumeration = onEnumeration;

        public PropertyExposureResolver.AnalysisSummary this[string key] => inner[key];
        public IEnumerable<string> Keys => inner.Keys;
        public IEnumerable<PropertyExposureResolver.AnalysisSummary> Values => inner.Values;
        public int Count => inner.Count;
        public bool ContainsKey(string key) => inner.ContainsKey(key);
        public bool TryGetValue(string key, out PropertyExposureResolver.AnalysisSummary value)
            => inner.TryGetValue(key, out value!);

        public IEnumerator<KeyValuePair<string, PropertyExposureResolver.AnalysisSummary>> GetEnumerator()
        {
            Interlocked.Exchange(ref _onEnumeration, null)?.Invoke();
            return inner.GetEnumerator();
        }

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    [Fact]
    public async Task LastConsumerLeavingDuringFinalization_CannotPublishTheAbandonedBody()
    {
        var downloader = new GatedDownloader();
        var parsed = await Parser.ParseAsync(
            $"F(0) = {{\n    open '{ModuleA}'\n    Local = 1\n    A + Local\n}}\nF(1) = 0\nF(0)",
            downloader.Options);
        Assert.False(parsed.HasErrors);
        var original = Region(parsed.Root, "F", 0);
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        using var release = new ManualResetEventSlim();
        using var cancellation = new CancellationTokenSource();
        var region = original.WithExposure(new PropertyExposureResolver.DeferredBranchContext(
            new GatedSummaries(original.Exposure!.VisiblePropertySummaries, () =>
            {
                entered.SetResult();
                Assert.True(release.Wait(TimeSpan.FromSeconds(10)));
            })));
        var pending = region.MaterializeAsync(cancellation.Token).AsTask();
        await downloader.Started(ModuleA);
        downloader.Release(ModuleA, "public A = 1");
        try
        {
            await entered.Task.WaitAsync(TimeSpan.FromSeconds(5));
            cancellation.Cancel();
            var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(
                () => pending.WaitAsync(TimeSpan.FromSeconds(5)));
            Assert.Equal(cancellation.Token, error.CancellationToken);
        }
        finally
        {
            release.Set();
        }

        await region.Loader.MaterializationGate.WaitAsync().WaitAsync(TimeSpan.FromSeconds(5));
        region.Loader.MaterializationGate.Release();
        Assert.False(region.IsMaterialized);
        Assert.Equal(1, region.MaterializationAttempts);

        Assert.False((await region.MaterializeAsync(CancellationToken.None)).IsError);
        Assert.True(region.IsMaterialized);
        Assert.Equal(2, region.MaterializationAttempts);
        Assert.Equal(1, downloader.Calls(ModuleA));
    }

    // ── Combined with Follow-up A: branch-local library backed by a lazy module ──

    [Fact]
    public async Task BranchLocalLibraryOverALazyModule_IsOpenableWithinTheBranch_WhileTheAlternativeStaysLazy()
    {
        var modules = Modules();
        var source =
            $"F(0) = {{\n    Lib = {{\n        open '{ModuleA}'\n        public X = A + 10\n    }}\n    G = {{\n        open Lib\n        X\n    }}\n    G\n}}\n" +
            $"F(1) = {{\n    open '{ModuleB}'\n    B\n}}\nF(0)";

        var result = await KatLangEngine.RunAsync(source, modules.Options);

        Assert.Equal("11", Display(Assert.IsType<RunResult.Success>(result)));
        Assert.Equal(1, modules[ModuleA]);
        Assert.Equal(0, modules[ModuleB]);
    }

    [Fact]
    public async Task BranchBinder_IsBoundInTheMaterializedBranch()
    {
        var modules = Modules();

        var result = await KatLangEngine.RunAsync(
            $"F(0) = 0\nF(n) = {{\n    open '{ModuleA}'\n    A + n\n}}\nF(5)", modules.Options);

        Assert.Equal("6", Display(Assert.IsType<RunResult.Success>(result)));
    }

    // ── Diagnostics timing ─────────────────────────────────────────────────

    [Fact]
    public async Task ElaborationDiagnosticsInsideADeferredBranch_AreReportedWhenTheBranchIsSelected()
    {
        // A diagnostic that could depend on the deferred module's members — here an undeclared
        // identifier under the closed branch-pattern rule — is deferred with the branch: a dead
        // branch reports nothing, a selected branch reports it with the ordinary wording and
        // code at its own source site.
        var modules = Modules();
        var branch = $"F(0) = 42\nF(1) = {{\n    open '{ModuleB}'\n    Undeclared + B\n}}\n";

        Assert.Equal("42", Display(Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(branch + "F(0)", modules.Options))));
        Assert.Equal(0, modules[ModuleB]);

        var selected = await KatLangEngine.RunAsync(branch + "F(1)", modules.Options);

        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(selected).Errors);
        Assert.Equal(KatLangErrorCode.UndeclaredIdentifier, error.Code);
        Assert.Contains("Identifier 'Undeclared' is used in conditional branch 'F'", error.Message, StringComparison.Ordinal);
        Assert.Equal(LineOf(branch, "Undeclared + B"), error.StartLine);
        Assert.Equal(1, modules[ModuleB]);
    }

    [Fact]
    public async Task RuntimePositionLoadInsideABranch_IsReportedWhenTheBranchIsSelected()
    {
        var modules = Modules();
        var branch = $"F(0) = 42\nF(1) = 1 + load('{ModuleA}')\n";

        Assert.Equal("42", Display(Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(branch + "F(0)", modules.Options))));

        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(branch + "F(1)", modules.Options)).Errors);
        Assert.Equal(KatLangErrorCode.InvalidLoadDirective, error.Code);
        Assert.Empty(modules.Fetches);
    }

    [Fact]
    public async Task ParseErrorsInsideADeadBranch_StayParseTimeErrors()
    {
        var modules = Modules();

        var result = await KatLangEngine.RunAsync($"F(0) = 42\nF(1) = {{\n    open '{ModuleB}'\n    1 +\n}}\nF(0)", modules.Options);

        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        Assert.NotEmpty(failure.Errors);
        Assert.DoesNotContain(failure.Errors, error => error.Code == KatLangErrorCode.LoadFetchFailed);
        Assert.Equal(0, modules[ModuleB]);
    }

    // ── Entry-point routing ────────────────────────────────────────────────

    [Fact]
    public async Task DeferredRegions_RequireTheAsyncEvaluationFamily()
    {
        var modules = Modules();
        var parsed = await Parser.ParseAsync(TwoAlternatives + "F(0)", modules.Options);
        Assert.False(parsed.HasErrors);
        var program = new Expr.AlgorithmExpr(parsed.Root);

        // A synchronous entry point cannot await a materialization: rejected before
        // evaluating, like an asynchronous host-operation configuration.
        Assert.Throws<InvalidOperationException>(() => Evaluator.Run(program));
        Assert.Throws<InvalidOperationException>(() => Evaluator.RunFlat(program));
        Assert.Equal(0, modules[ModuleA]);

        var result = await Evaluator.RunFlatAsync(program);

        Assert.Equal([1m], result.Value);
        Assert.Equal(1, modules[ModuleA]);
    }

    // ── Editor semantic model over a deferred region ───────────────────────

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task HostComposition_PreservesDeferredAsyncRouting(bool copyRoot)
    {
        var modules = Modules();
        var parsed = await Parser.ParseAsync(TwoAlternatives + "F(0)", modules.Options);
        Assert.False(parsed.HasErrors);
        Expr program = copyRoot
            ? new Expr.AlgorithmExpr(parsed.Root with { })
            : new Expr.Capture(new OutputBundle([new Expr.AlgorithmExpr(parsed.Root)]));

        Assert.Throws<InvalidOperationException>(() => Evaluator.Run(program));
        Assert.Empty(modules.Fetches);

        var result = await Evaluator.RunFlatAsync(program);

        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([1m], result.Value);
        Assert.Equal(1, modules[ModuleA]);
        Assert.Equal(0, modules[ModuleB]);
    }

    [Theory]
    [InlineData("F(1, 2)", false)]
    [InlineData("[(1, 2)].map(F)", false)]
    [InlineData("F()", true)]
    [InlineData("F", true)]
    [InlineData("Box.F", true)]
    public async Task HostFlatBinderFamily_OnlyInvocationDemandsItsDeferredBody(string expression, bool arityError)
    {
        var modules = Modules();
        var syntax = Parser.ParseSyntax(
            $"F(0) = {{\n    open '{ModuleA}'\n    x + y + A\n}}\nF(1) = 0\n" + expression);
        Assert.False(syntax.HasErrors);
        var body = Family(syntax.Root, "F").Branches[0].Body;
        var family = new Algorithm.Conditional(null, [],
            [new CondBranch(new Pattern.SequenceValue([new Pattern.Bind("x"), new Pattern.Bind("y")]), body)]);
        var property = new Property("F", family);
        var root = syntax.Root with
        {
            Properties = [property, new Property("Box", new Algorithm.User(null, [], [], [property], OutputBundle.Empty))],
        };
        var diagnostics = new List<Diagnostic>();
        var loaded = await new ModuleLoader(diagnostics, modules.Download).ElaborateAsync(root);
        var (detected, detectionDiagnostics) = ParameterDetector.Detect(loaded);
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, diagnostics: diagnostics);
        var exposed = PropertyExposureResolver.Resolve(resolved);
        Assert.Empty(diagnostics);
        Assert.Empty(detectionDiagnostics);
        Assert.Empty(modules.Fetches);

        var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(exposed));

        if (arityError)
        {
            Assert.True(result.IsError);
            Assert.Equal(KatLangErrorCode.ArityMismatch, result.Error.Code);
            Assert.Empty(modules.Fetches);
        }
        else
        {
            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
            Assert.Equal([4m], result.Value);
            Assert.Equal(1, modules[ModuleA]);
        }
    }

    [Fact]
    public async Task SemanticModel_DeferredModuleName_IsIndeterminate_NotUnresolved_WithZeroModuleWork()
    {
        // The editor's semantic model is built from the published tree. A deferred region is
        // not an unresolved load the pipeline forgot (the guard skips it), so building neither
        // throws nor fetches anything. Inside a deferred branch, a name that resolves nowhere
        // lexically but sits under a deferred module open is INDETERMINATE — the module may
        // supply it, and only branch selection would load it — never a hard unresolved error;
        // a name the lexical chain resolves without the module stays resolved as before.
        var modules = Modules();
        var source = $"Known = 5\nF(0) = {{\n    open '{ModuleA}'\n    ImportedValue + Known\n}}\nF(1) = 0\nF(0)";
        var parsed = await Parser.ParseAsync(source, modules.Options);
        Assert.False(parsed.HasErrors);

        var model = SemanticModelBuilder.Build(parsed);

        Assert.Empty(modules.Fetches);
        var imported = Assert.Single(model.FindResolutions("ImportedValue"));
        Assert.Equal(IdentifierClassification.DeferredModuleReference, imported.Classification);
        Assert.Null(imported.ResolvedDeclaration);
        Assert.Null(imported.ResolvedProperty);
        var known = Assert.Single(model.FindResolutions("Known"), r => r.Occurrence.Kind == OccurrenceKind.ResolveReference);
        Assert.Equal(IdentifierClassification.PropertyReference, known.Classification);
        Assert.NotNull(known.ResolvedDeclaration);
        Assert.DoesNotContain(model.IdentifierResolutions, r => r.Classification == IdentifierClassification.Unresolved);
    }

    [Fact]
    public async Task SemanticModel_GenuinelyUnresolvedNames_StayUnresolved_BesideADeferredOpen()
    {
        // Names no deferred open could supply keep the ordinary unresolved treatment: a free
        // name in a closed branch WITHOUT a deferred open in its lookup chain (a real typo,
        // reported by the front end), and an open HEAD inside the deferred branch (open heads
        // resolve through direct properties only — never through opens, deferred or not).
        var modules = Modules();
        var source = $"F(0) = {{\n    open '{ModuleA}'\n    Inner = {{\n        open Missing\n        A\n    }}\n    Inner\n}}\nF(1) = Typo\nF(0)";
        var parsed = await Parser.ParseAsync(source, modules.Options);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Contains("'Typo' is used in conditional branch 'F'", diagnostic.Message, StringComparison.Ordinal);

        var model = SemanticModelBuilder.Build(parsed);

        Assert.Empty(modules.Fetches);
        Assert.Equal(IdentifierClassification.DeferredModuleReference, Assert.Single(model.FindResolutions("A")).Classification);
        Assert.Equal(IdentifierClassification.Unresolved, Assert.Single(model.FindResolutions("Typo")).Classification);
        var missingOpen = Assert.Single(model.FindResolutions("Missing"));
        Assert.Equal(OccurrenceKind.OpenTargetReference, missingOpen.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Unresolved, missingOpen.Classification);
    }

    [Fact]
    public async Task SemanticModel_DeferredPlaceholderMembers_AreIndeterminate()
    {
        // `Lib = load('url')` inside a deferred branch keeps its unmaterialized placeholder: a
        // member of it, a name looked up through a nested `open Lib`, a name the branch's own
        // deferred open may supply, and a member of such a name are all indeterminate; `Lib`
        // itself is an ordinary property and a valid open target.
        var modules = Modules();
        var source =
            $"F(0) = {{\n    open '{ModuleB}'\n    Lib = load('{ModuleA}')\n    Inner = {{\n        open Lib\n        Lib.A + Fetched.B + Z\n    }}\n    Inner\n}}\nF(1) = 0\nF(0)";
        var parsed = await Parser.ParseAsync(source, modules.Options);
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics.Select(d => d.Message)));

        var model = SemanticModelBuilder.Build(parsed);

        Assert.Empty(modules.Fetches);
        Assert.Contains(model.FindResolutions("Lib"), r => r.Classification == IdentifierClassification.PropertyReference);
        Assert.Contains(model.FindResolutions("Lib"), r => r.Classification == IdentifierClassification.OpenTarget);
        var memberA = Assert.Single(model.FindResolutions("A"), r => r.Occurrence.Kind == OccurrenceKind.DotMemberReference);
        Assert.Equal(IdentifierClassification.DeferredModuleReference, memberA.Classification);
        Assert.Equal(IdentifierClassification.DeferredModuleReference, Assert.Single(model.FindResolutions("Fetched")).Classification);
        var memberB = Assert.Single(model.FindResolutions("B"), r => r.Occurrence.Kind == OccurrenceKind.DotMemberReference);
        Assert.Equal(IdentifierClassification.DeferredModuleReference, memberB.Classification);
        Assert.Equal(IdentifierClassification.DeferredModuleReference, Assert.Single(model.FindResolutions("Z")).Classification);
        Assert.DoesNotContain(model.IdentifierResolutions, r => r.Classification == IdentifierClassification.Unresolved);
    }

    [Fact]
    public async Task SemanticModel_SharedDeferredSubtree_IsAnalyzedOnce_WithZeroModuleWork()
    {
        // One deferred family referenced from two properties of a host-built root: the same
        // node under the same scope frame is one occurrence (M4), so the builder analyzes the
        // deferred subtree once, classifies its name as deferred, and performs no module I/O.
        var modules = Modules();
        var parsed = await Parser.ParseAsync($"F(0) = {{\n    open '{ModuleA}'\n    A\n}}\nF(1) = 0\nF(0)", modules.Options);
        Assert.False(parsed.HasErrors);
        var family = Family(parsed.Root, "F");
        var hostRoot = new Algorithm.User(
            null, [], [],
            [new Property("F", family), new Property("G", family)],
            new OutputBundle([new Expr.Num(0)]));
        var observations = new FrontEndTraversalObservations();

        var model = SemanticModelBuilder.Build(hostRoot, observations);

        Assert.Empty(modules.Fetches);
        var resolution = Assert.Single(model.FindResolutions("A"));
        Assert.Equal(IdentifierClassification.DeferredModuleReference, resolution.Classification);
        // Root, the family, and its two branch bodies: the shared family is not visited again.
        Assert.Equal(4, observations.SemanticModelAlgorithmVisits);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task SemanticModel_DeferredDottedPaths_PropagateUncertainty(bool openPath)
    {
        var modules = Modules();
        var body = openPath
            ? "Inner = {\n    open Lib.Sub.Nested\n    X\n}\nInner"
            : "Lib.Sub.Nested.X";
        var parsed = await Parser.ParseAsync(
            $"F(0) = {{\n    Lib = load('{ModuleA}')\n    {body}\n}}\nF(1) = 0\nF(0)",
            modules.Options);
        Assert.False(parsed.HasErrors);

        var model = SemanticModelBuilder.Build(parsed);

        Assert.Empty(modules.Fetches);
        foreach (var name in new[] { "Sub", "Nested", "X" })
        {
            var resolution = Assert.Single(model.FindResolutions(name));
            Assert.Equal(IdentifierClassification.DeferredModuleReference, resolution.Classification);
            Assert.Null(resolution.ResolvedDeclaration);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task SemanticModel_DeferredAndKnownOpen_DoNotClaimCertainResolution(bool directlyDeclared)
    {
        var modules = Modules();
        var prefix = directlyDeclared ? "X = 5\n" : "";
        var parsed = await Parser.ParseAsync(
            prefix + $"F(0) = {{\n    open {{ public X = 1 }}, '{ModuleA}'\n    X\n}}\nF(1) = 0\nF(0)",
            modules.Options);
        Assert.False(parsed.HasErrors);

        var model = SemanticModelBuilder.Build(parsed);

        Assert.Empty(modules.Fetches);
        var resolution = Assert.Single(model.FindResolutions("X"),
            candidate => candidate.Occurrence.Kind == OccurrenceKind.ResolveReference);
        Assert.Equal(directlyDeclared
            ? IdentifierClassification.PropertyReference
            : IdentifierClassification.DeferredModuleReference, resolution.Classification);
        Assert.Equal(directlyDeclared, resolution.ResolvedDeclaration is not null);
        var visible = Assert.Single(model.GetVisibleSymbolsAt(
            resolution.Occurrence.Span.StartLineNumber, resolution.Occurrence.Span.StartColumn),
            candidate => candidate.Name == "X");
        Assert.Equal(resolution.Classification, visible.Classification);
        Assert.Equal(directlyDeclared, visible.Declaration is not null);
    }
}
