namespace KatLang.Tests;

/// <summary>
/// Host-cancellation coverage for parsing and compile-time module loading. Cancellation is a
/// source-processing policy and is deliberately not an evaluator cancellation mechanism.
/// </summary>
public class ModuleLoaderCancellationTests
{
    private const string ModuleUrl = "https://katlang.org/cancellation/module.kat";
    private const string NestedUrl = "https://katlang.org/cancellation/nested.kat";
    private const string Source = $"public Module = load('{ModuleUrl}')\nModule.Value";

    [Fact]
    public void ParserParse_PreCancelledToken_PreventsDownloadAndPropagatesCancellation()
    {
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var calls = 0;
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = cancellation.Token,
            DownloadCodeWithCancellation = (_, _) =>
            {
                calls++;
                return "public Value = 1";
            },
        };

        var exception = Assert.Throws<OperationCanceledException>(() => Parser.Parse(Source, options));

        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.Equal(0, calls);
    }

    [Fact]
    public void EngineRun_PreCancelledToken_PreventsDownloadAndPropagatesCancellation()
    {
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var calls = 0;
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = cancellation.Token,
            DownloadCodeWithCancellation = (_, _) =>
            {
                calls++;
                return "public Value = 1";
            },
        };

        var exception = Assert.Throws<OperationCanceledException>(() => KatLangEngine.Run(Source, options));

        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.Equal(0, calls);
    }

    [Fact]
    public void TokenAwareDownloader_ReceivesExactConfiguredToken()
    {
        using var cancellation = new CancellationTokenSource();
        CancellationToken received = default;
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = cancellation.Token,
            DownloadCodeWithCancellation = (_, token) =>
            {
                received = token;
                return "public Value = 7";
            },
        };

        var result = Parser.Parse(Source, options);

        Assert.False(result.HasErrors, JoinDiagnostics(result.Diagnostics));
        Assert.Equal(cancellation.Token, received);
    }

    [Fact]
    public void BothDownloadersConfigured_TokenAwareDownloaderTakesPrecedence()
    {
        var legacyCalls = 0;
        var tokenAwareCalls = 0;
        var options = new RunOptions
        {
            DownloadCode = _ =>
            {
                legacyCalls++;
                throw new InvalidOperationException("legacy downloader must not be selected");
            },
            DownloadCodeWithCancellation = (_, _) =>
            {
                tokenAwareCalls++;
                return "public Value = 7";
            },
        };

        var result = Parser.Parse(Source, options);

        Assert.False(result.HasErrors, JoinDiagnostics(result.Diagnostics));
        Assert.Equal(0, legacyCalls);
        Assert.Equal(1, tokenAwareCalls);
    }

    [Fact]
    public void PublicModuleLoader_LegacyConstructorAndCancellationFactoryBothRemainAvailable()
    {
        var root = ParseSyntaxRoot(Source);
        var legacyDiagnostics = new List<Diagnostic>();
        var legacyLoader = new ModuleLoader(
            legacyDiagnostics,
            _ => "public Value = 3");

        _ = legacyLoader.Elaborate(root);

        using var cancellation = new CancellationTokenSource();
        var tokenAwareDiagnostics = new List<Diagnostic>();
        CancellationToken received = default;
        var tokenAwareLoader = ModuleLoader.CreateWithCancellation(
            tokenAwareDiagnostics,
            cancellation.Token,
            (_, token) =>
            {
                received = token;
                return "public Value = 5";
            });

        _ = tokenAwareLoader.Elaborate(root);

        Assert.Empty(legacyDiagnostics);
        Assert.Empty(tokenAwareDiagnostics);
        Assert.Equal(cancellation.Token, received);
    }

    [Fact]
    public void CancellationRequestedDuringDownload_PropagatesWithoutFetchDiagnosticOrCommit()
    {
        using var cancellation = new CancellationTokenSource();
        var diagnostics = new List<Diagnostic>();
        var budget = new SourceProcessingBudget(SourceProcessingLimits.Default);
        var loader = new ModuleLoader(
            diagnostics,
            downloadCode: null,
            downloadCodeWithCancellation: (_, _) =>
            {
                cancellation.Cancel();
                return "public Value = 7";
            },
            allowedHosts: null,
            budget,
            cancellation.Token);

        var exception = Assert.Throws<OperationCanceledException>(
            () => loader.Elaborate(ParseSyntaxRoot(Source)));

        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.DoesNotContain(diagnostics, IsFetchFailure);
        Assert.Equal(0, loader.CachedModuleCount);
        Assert.Equal(0, loader.InProgressModuleCount);
        Assert.Equal(0, budget.CurrentDepth);
        Assert.Equal(0, budget.ModuleCount);
        Assert.Equal(0, budget.AggregateSource);
    }

    [Fact]
    public void HostCancellationWinsWhenDownloaderThrowsDifferentException()
    {
        using var cancellation = new CancellationTokenSource();
        var diagnostics = new List<Diagnostic>();
        var loader = ModuleLoader.CreateWithCancellation(
            diagnostics,
            cancellation.Token,
            (_, _) =>
            {
                cancellation.Cancel();
                throw new InvalidOperationException("downloader shutdown race");
            });

        var exception = Assert.Throws<OperationCanceledException>(
            () => loader.Elaborate(ParseSyntaxRoot(Source)));

        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.DoesNotContain(diagnostics, IsFetchFailure);
        Assert.Equal(0, loader.CachedModuleCount);
        Assert.Equal(0, loader.InProgressModuleCount);
    }

    [Fact]
    public void RegularTokenAwareDownloaderException_RemainsFetchDiagnostic()
    {
        var options = new RunOptions
        {
            DownloadCodeWithCancellation = (_, _) => throw new InvalidOperationException("network failed"),
        };

        var result = Parser.Parse(Source, options);

        var diagnostic = Assert.Single(result.Diagnostics, IsFetchFailure);
        Assert.Contains("network failed", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DownloaderCancellationWithoutHostCancellation_RemainsFetchDiagnostic(bool taskCanceled)
    {
        using var hostCancellation = new CancellationTokenSource();
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = hostCancellation.Token,
            DownloadCodeWithCancellation = (_, _) =>
            {
                if (taskCanceled)
                    throw new TaskCanceledException("internal timeout");

                throw new OperationCanceledException("internal cancellation");
            },
        };

        var result = Parser.Parse(Source, options);

        Assert.False(hostCancellation.IsCancellationRequested);
        var diagnostic = Assert.Single(result.Diagnostics, IsFetchFailure);
        Assert.Contains(
            taskCanceled ? "internal timeout" : "internal cancellation",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void LegacyDownloaderOperationCanceled_WithoutConfiguredToken_RemainsFetchDiagnostic()
    {
        var options = new RunOptions
        {
            DownloadCode = _ => throw new OperationCanceledException("stray downloader cancellation"),
        };

        var result = Parser.Parse(Source, options);

        var diagnostic = Assert.Single(result.Diagnostics, IsFetchFailure);
        Assert.Contains("stray downloader cancellation", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void NestedModuleCancellation_RestoresDepthInProgressCacheAndReservations()
    {
        using var cancellation = new CancellationTokenSource();
        var diagnostics = new List<Diagnostic>();
        var budget = new SourceProcessingBudget(SourceProcessingLimits.Default);
        var outerSource = $"public Nested = load('{NestedUrl}')";
        var loader = new ModuleLoader(
            diagnostics,
            downloadCode: null,
            downloadCodeWithCancellation: (url, _) =>
            {
                if (url == ModuleUrl)
                    return outerSource;

                Assert.Equal(NestedUrl, url);
                cancellation.Cancel();
                throw new OperationCanceledException("host cancelled nested fetch", cancellation.Token);
            },
            allowedHosts: null,
            budget,
            cancellation.Token);

        var exception = Assert.Throws<OperationCanceledException>(
            () => loader.Elaborate(ParseSyntaxRoot(Source)));

        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.Equal(2, budget.PeakDepth);
        Assert.Equal(0, budget.CurrentDepth);
        Assert.Equal(0, loader.InProgressModuleCount);
        Assert.Equal(0, loader.CachedModuleCount);
        Assert.Equal(0, budget.ModuleCount);
        Assert.Equal(0, budget.AggregateSource);
        Assert.DoesNotContain(diagnostics, IsFetchFailure);
    }

    [Fact]
    public void NestedCancellation_PreservesCompletedSiblingModule_AndSkipsRemainingFetches()
    {
        const string SiblingUrl = "https://katlang.org/cancellation/sibling.kat";
        const string RemainingUrl = "https://katlang.org/cancellation/remaining.kat";
        const string SiblingSource = "public Value = 1";
        var outerSource =
            $"public First = load('{SiblingUrl}')\n" +
            $"public Again = load('{SiblingUrl}')\n" +
            $"public Cancelled = load('{NestedUrl}')\n" +
            $"public Remaining = load('{RemainingUrl}')";

        using var cancellation = new CancellationTokenSource();
        var diagnostics = new List<Diagnostic>();
        var budget = new SourceProcessingBudget(SourceProcessingLimits.Default);
        var siblingFetches = 0;
        var remainingFetches = 0;
        var loader = new ModuleLoader(
            diagnostics,
            downloadCode: null,
            downloadCodeWithCancellation: (url, _) =>
            {
                switch (url)
                {
                    case ModuleUrl:
                        return outerSource;
                    case SiblingUrl:
                        siblingFetches++;
                        return SiblingSource;
                    case NestedUrl:
                        cancellation.Cancel();
                        throw new OperationCanceledException("host cancelled nested fetch", cancellation.Token);
                    default:
                        remainingFetches++;
                        throw new InvalidOperationException($"unexpected fetch of '{url}'");
                }
            },
            allowedHosts: null,
            budget,
            cancellation.Token);

        var exception = Assert.Throws<OperationCanceledException>(
            () => loader.Elaborate(ParseSyntaxRoot(Source)));

        Assert.Equal(cancellation.Token, exception.CancellationToken);
        // The completed sibling module stays cached and charged exactly once (its repeated load
        // was a cache hit), only the aborted outer/nested frames rolled back, and the fetch that
        // would have followed the cancelled one never ran.
        Assert.Equal(1, siblingFetches);
        Assert.Equal(0, remainingFetches);
        Assert.Equal(1, loader.CachedModuleCount);
        Assert.Equal(1, budget.ModuleCount);
        Assert.Equal(SiblingSource.Length, budget.AggregateSource);
        Assert.Equal(0, loader.InProgressModuleCount);
        Assert.Equal(0, budget.CurrentDepth);
        Assert.Equal(2, budget.PeakDepth);
        Assert.DoesNotContain(diagnostics, IsFetchFailure);
    }

    [Fact]
    public void RollbackAfterCancellation_FreesBudgetCapacityForANewLoaderOnTheSameBudget()
    {
        const string OuterUrl = "https://katlang.org/cancellation/reuse-outer.kat";
        const string InnerUrl = "https://katlang.org/cancellation/reuse-inner.kat";
        const string InnerSource = "public Value = 21";
        var outerSource = $"public Inner = load('{InnerUrl}')";
        var root = ParseSyntaxRoot($"public Module = load('{OuterUrl}')");

        // Ceilings sized so both modules exactly fit: a reservation leaked by the cancelled first
        // attempt would push the second attempt over the module-count and aggregate ceilings.
        var budget = new SourceProcessingBudget(new SourceProcessingLimits
        {
            MaxModuleCount = 2,
            MaxAggregateSourceLength = outerSource.Length + InnerSource.Length,
        });

        using var firstCancellation = new CancellationTokenSource();
        var firstDiagnostics = new List<Diagnostic>();
        var firstLoader = new ModuleLoader(
            firstDiagnostics,
            downloadCode: null,
            downloadCodeWithCancellation: (url, _) =>
            {
                if (url == OuterUrl)
                    return outerSource;

                Assert.Equal(InnerUrl, url);
                firstCancellation.Cancel();
                throw new OperationCanceledException("host cancelled inner fetch", firstCancellation.Token);
            },
            allowedHosts: null,
            budget,
            firstCancellation.Token);

        Assert.Throws<OperationCanceledException>(() => firstLoader.Elaborate(root));
        Assert.Equal(0, budget.ModuleCount);
        Assert.Equal(0, budget.AggregateSource);

        using var secondCancellation = new CancellationTokenSource();
        var secondDiagnostics = new List<Diagnostic>();
        var secondLoader = new ModuleLoader(
            secondDiagnostics,
            downloadCode: null,
            downloadCodeWithCancellation: (url, _) => url == OuterUrl ? outerSource : InnerSource,
            allowedHosts: null,
            budget,
            secondCancellation.Token);

        _ = secondLoader.Elaborate(root);

        Assert.Empty(secondDiagnostics);
        Assert.Equal(2, budget.ModuleCount);
        Assert.Equal(outerSource.Length + InnerSource.Length, budget.AggregateSource);
        Assert.Equal(2, secondLoader.CachedModuleCount);
    }

    [Fact]
    public void CancelledLoader_SecondElaborateThrows_WithoutDisturbingCommittedState()
    {
        const string CompletedUrl = "https://katlang.org/cancellation/completed.kat";
        const string CompletedSource = "public Value = 17";
        var root = ParseSyntaxRoot(
            $"public First = load('{CompletedUrl}')\n" +
            $"public Second = load('{ModuleUrl}')");

        using var cancellation = new CancellationTokenSource();
        var diagnostics = new List<Diagnostic>();
        var budget = new SourceProcessingBudget(SourceProcessingLimits.Default);
        var fetches = 0;
        var loader = new ModuleLoader(
            diagnostics,
            downloadCode: null,
            downloadCodeWithCancellation: (url, _) =>
            {
                fetches++;
                if (url == CompletedUrl)
                    return CompletedSource;

                Assert.Equal(ModuleUrl, url);
                cancellation.Cancel();
                throw new OperationCanceledException("host cancelled second fetch", cancellation.Token);
            },
            allowedHosts: null,
            budget,
            cancellation.Token);

        Assert.Throws<OperationCanceledException>(() => loader.Elaborate(root));
        Assert.Equal(2, fetches);
        Assert.Equal(1, loader.CachedModuleCount);
        Assert.Equal(1, budget.ModuleCount);
        Assert.Equal(CompletedSource.Length, budget.AggregateSource);

        // Reuse of the cancelled loader is deterministic: its fixed token is still cancelled, so
        // a second elaboration throws immediately without fetching, double-rolling-back, or
        // touching the committed module state.
        Assert.Throws<OperationCanceledException>(() => loader.Elaborate(root));
        Assert.Equal(2, fetches);
        Assert.Equal(1, loader.CachedModuleCount);
        Assert.Equal(1, budget.ModuleCount);
        Assert.Equal(CompletedSource.Length, budget.AggregateSource);
        Assert.Equal(0, loader.InProgressModuleCount);
        Assert.Equal(0, budget.CurrentDepth);
    }

    [Fact]
    public void SequentialRuns_FreshOptionsAfterCancelledRun_SucceedWithoutCrossRunState()
    {
        var downloads = 0;

        string Download(string url, CancellationToken token)
        {
            downloads++;
            return "public Value = 11";
        }

        using var cancellation = new CancellationTokenSource();
        var cancelledOptions = new RunOptions
        {
            SourceProcessingCancellationToken = cancellation.Token,
            DownloadCodeWithCancellation = (url, token) =>
            {
                cancellation.Cancel();
                return Download(url, token);
            },
        };

        var exception = Assert.Throws<OperationCanceledException>(
            () => KatLangEngine.Run(Source, cancelledOptions));
        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.Equal(1, downloads);

        var freshOptions = new RunOptions { DownloadCodeWithCancellation = Download };

        var result = KatLangEngine.Run(Source, freshOptions);

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal([11m], success.Atoms);
        Assert.Equal(2, downloads);
    }

    [Fact]
    public void LegacyDownloadCode_RemainsSupportedWithSourceProcessingToken()
    {
        using var cancellation = new CancellationTokenSource();
        var calls = 0;
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = cancellation.Token,
            DownloadCode = _ =>
            {
                calls++;
                return "public Value = 11";
            },
        };

        var result = KatLangEngine.Run(Source, options);

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal([11m], success.Atoms);
        Assert.Equal(1, calls);
    }

    [Fact]
    public async Task ConcurrentRuns_SharingRunOptions_KeepCancellationAndLoaderStateRunLocal()
    {
        const int runCount = 4;
        using var cancellation = new CancellationTokenSource();
        using var enteredDownloaders = new CountdownEvent(runCount);
        using var releaseDownloaders = new ManualResetEventSlim(false);
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = cancellation.Token,
            DownloadCodeWithCancellation = (_, token) =>
            {
                Assert.Equal(cancellation.Token, token);
                enteredDownloaders.Signal();
                Assert.True(releaseDownloaders.Wait(TimeSpan.FromSeconds(10)));
                return "public Value = 13";
            },
        };

        var tasks = Enumerable.Range(0, runCount)
            .Select(index => Task.Factory.StartNew(
                () => KatLangEngine.Run(
                    $"public Module = load('https://katlang.org/cancellation/{index}.kat')\nModule.Value",
                    options),
                CancellationToken.None,
                TaskCreationOptions.LongRunning,
                TaskScheduler.Default))
            .ToArray();

        try
        {
            Assert.True(
                enteredDownloaders.Wait(TimeSpan.FromSeconds(10)),
                "Runs did not overlap inside their token-aware downloaders.");
        }
        finally
        {
            releaseDownloaders.Set();
        }

        var results = await Task.WhenAll(tasks);
        Assert.All(results, result => Assert.IsType<RunResult.Success>(result));
        Assert.False(cancellation.IsCancellationRequested);
    }

    private static Algorithm ParseSyntaxRoot(string source)
    {
        var syntax = Parser.ParseSyntax(source);
        Assert.False(syntax.HasErrors, JoinDiagnostics(syntax.Diagnostics));
        return syntax.SyntaxRoot;
    }

    private static bool IsFetchFailure(Diagnostic diagnostic)
        => diagnostic.Message.Contains("failed to fetch", StringComparison.Ordinal);

    private static string JoinDiagnostics(IEnumerable<Diagnostic> diagnostics)
        => string.Join(Environment.NewLine, diagnostics.Select(diagnostic => diagnostic.Message));
}
