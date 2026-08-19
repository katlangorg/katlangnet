namespace KatLang.Tests;

/// <summary>
/// Host-cancellation coverage for parsing and compile-time module loading over the
/// async-only source-loading contract. Cancellation is a source-processing policy and is
/// deliberately not an evaluator cancellation mechanism. Downloaders here complete
/// synchronously unless a test needs a genuine suspension; suspension-focused coverage
/// lives in <see cref="ModuleLoaderAsyncTests"/>.
/// </summary>
public class ModuleLoaderCancellationTests
{
    private const string ModuleUrl = "https://katlang.org/cancellation/module.kat";
    private const string NestedUrl = "https://katlang.org/cancellation/nested.kat";
    private const string Source = $"public Module = load('{ModuleUrl}')\nModule.Value";

    [Fact]
    public async Task ParserParseAsync_PreCancelledToken_PreventsDownloadAndPropagatesCancellation()
    {
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var calls = 0;
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = cancellation.Token,
            DownloadCode = (_, _) =>
            {
                calls++;
                return ValueTask.FromResult("public Value = 1");
            },
        };

        var exception = await Assert.ThrowsAsync<OperationCanceledException>(
            () => Parser.ParseAsync(Source, options));

        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.Equal(0, calls);
    }

    [Fact]
    public async Task EngineRunAsync_PreCancelledToken_PreventsDownloadAndPropagatesCancellation()
    {
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var calls = 0;
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = cancellation.Token,
            DownloadCode = (_, _) =>
            {
                calls++;
                return ValueTask.FromResult("public Value = 1");
            },
        };

        var exception = await Assert.ThrowsAsync<OperationCanceledException>(
            () => KatLangEngine.RunAsync(Source, options));

        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.Equal(0, calls);
    }

    [Fact]
    public async Task Downloader_ReceivesExactConfiguredToken()
    {
        using var cancellation = new CancellationTokenSource();
        CancellationToken received = default;
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = cancellation.Token,
            DownloadCode = (_, token) =>
            {
                received = token;
                return ValueTask.FromResult("public Value = 7");
            },
        };

        var result = await Parser.ParseAsync(Source, options);

        Assert.False(result.HasErrors, JoinDiagnostics(result.Diagnostics));
        Assert.Equal(cancellation.Token, received);
    }

    /// <summary>
    /// Source loading is async-only: every SYNCHRONOUS source-level entry point rejects a
    /// downloader-configured options object before parsing, and the downloader is never
    /// invoked. This replaces the removed synchronous downloader path — there is no
    /// precedence rule and no blocking bridge.
    /// </summary>
    [Fact]
    public void SynchronousEntryPoints_RejectDownloaderConfiguredOptions_WithoutInvokingDownloader()
    {
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) =>
            {
                calls++;
                return ValueTask.FromResult("public Value = 7");
            },
        };

        Assert.Throws<InvalidOperationException>(() => KatLangEngine.Run(Source, options));
        Assert.Throws<InvalidOperationException>(() => KatLangEngine.EvaluateToAtoms(Source, options));
        Assert.Throws<InvalidOperationException>(() => KatLangEngine.EvaluateToString(Source, options));
        Assert.Throws<InvalidOperationException>(() => Parser.Parse(Source, options));

        // The rejection is configuration-driven, so load-free source is rejected too —
        // deterministic fail-fast, mirroring the asynchronous host-operation rule.
        Assert.Throws<InvalidOperationException>(() => KatLangEngine.Run("1 + 1", options));

        Assert.Equal(0, calls);
    }

    [Fact]
    public async Task PublicModuleLoader_ConstructorConfiguresDownloaderAndToken()
    {
        var root = ParseSyntaxRoot(Source);
        var defaultTokenDiagnostics = new List<Diagnostic>();
        var defaultTokenLoader = new ModuleLoader(
            defaultTokenDiagnostics,
            (_, _) => ValueTask.FromResult("public Value = 3"));

        _ = await defaultTokenLoader.ElaborateAsync(root);

        using var cancellation = new CancellationTokenSource();
        var tokenDiagnostics = new List<Diagnostic>();
        CancellationToken received = default;
        var tokenLoader = new ModuleLoader(
            tokenDiagnostics,
            (_, token) =>
            {
                received = token;
                return ValueTask.FromResult("public Value = 5");
            },
            allowedHosts: null,
            cancellation.Token);

        _ = await tokenLoader.ElaborateAsync(root);

        Assert.Empty(defaultTokenDiagnostics);
        Assert.Empty(tokenDiagnostics);
        Assert.Equal(cancellation.Token, received);
    }

    [Fact]
    public async Task CancellationRequestedDuringDownload_PropagatesWithoutFetchDiagnosticOrCommit()
    {
        using var cancellation = new CancellationTokenSource();
        var diagnostics = new List<Diagnostic>();
        var budget = new SourceProcessingBudget(SourceProcessingLimits.Default);
        var loader = new ModuleLoader(
            diagnostics,
            (_, _) =>
            {
                // The module text is returned successfully, but the host cancelled while
                // the download was in flight: the post-fetch observation wins and the
                // fetched module must never be committed.
                cancellation.Cancel();
                return ValueTask.FromResult("public Value = 7");
            },
            allowedHosts: null,
            budget,
            cancellation.Token);

        var exception = await Assert.ThrowsAsync<OperationCanceledException>(
            async () => await loader.ElaborateAsync(ParseSyntaxRoot(Source)));

        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.DoesNotContain(diagnostics, IsFetchFailure);
        Assert.Equal(0, loader.CachedModuleCount);
        Assert.Equal(0, loader.InProgressModuleCount);
        Assert.Equal(0, budget.CurrentDepth);
        Assert.Equal(0, budget.ModuleCount);
        Assert.Equal(0, budget.AggregateSource);
    }

    [Fact]
    public async Task HostCancellationWins_WhenDownloaderThrowsDifferentException()
    {
        using var cancellation = new CancellationTokenSource();
        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(
            diagnostics,
            (_, _) =>
            {
                cancellation.Cancel();
                throw new InvalidOperationException("downloader shutdown race");
            },
            allowedHosts: null,
            cancellation.Token);

        var exception = await Assert.ThrowsAsync<OperationCanceledException>(
            async () => await loader.ElaborateAsync(ParseSyntaxRoot(Source)));

        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.DoesNotContain(diagnostics, IsFetchFailure);
        Assert.Equal(0, loader.CachedModuleCount);
        Assert.Equal(0, loader.InProgressModuleCount);
    }

    [Fact]
    public async Task HostCancellationWins_WhenDownloaderTaskFaultsWithDifferentException()
    {
        using var cancellation = new CancellationTokenSource();
        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(
            diagnostics,
            (_, _) =>
            {
                // A FAULTED awaitable (not a synchronous throw) racing host cancellation:
                // the cancelled host token stays authoritative over the fault.
                cancellation.Cancel();
                return ValueTask.FromException<string>(new InvalidOperationException("socket torn down"));
            },
            allowedHosts: null,
            cancellation.Token);

        var exception = await Assert.ThrowsAsync<OperationCanceledException>(
            async () => await loader.ElaborateAsync(ParseSyntaxRoot(Source)));

        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.DoesNotContain(diagnostics, IsFetchFailure);
        Assert.Equal(0, loader.CachedModuleCount);
        Assert.Equal(0, loader.InProgressModuleCount);
    }

    [Fact]
    public async Task RegularDownloaderException_RemainsFetchDiagnostic()
    {
        var options = new RunOptions
        {
            DownloadCode = (_, _) => throw new InvalidOperationException("network failed"),
        };

        var result = await Parser.ParseAsync(Source, options);

        var diagnostic = Assert.Single(result.Diagnostics, IsFetchFailure);
        Assert.Contains("network failed", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task RegularDownloaderFaultedTask_RemainsFetchDiagnostic()
    {
        var options = new RunOptions
        {
            DownloadCode = (_, _) => ValueTask.FromException<string>(
                new InvalidOperationException("connection reset")),
        };

        var result = await Parser.ParseAsync(Source, options);

        var diagnostic = Assert.Single(result.Diagnostics, IsFetchFailure);
        Assert.Contains("connection reset", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task DownloaderCancellationWithoutHostCancellation_RemainsFetchDiagnostic(bool taskCanceled)
    {
        using var hostCancellation = new CancellationTokenSource();
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = hostCancellation.Token,
            DownloadCode = (_, _) =>
            {
                if (taskCanceled)
                    return ValueTask.FromException<string>(new TaskCanceledException("internal timeout"));

                throw new OperationCanceledException("internal cancellation");
            },
        };

        var result = await Parser.ParseAsync(Source, options);

        Assert.False(hostCancellation.IsCancellationRequested);
        var diagnostic = Assert.Single(result.Diagnostics, IsFetchFailure);
        Assert.Contains(
            taskCanceled ? "internal timeout" : "internal cancellation",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public async Task DownloaderOperationCanceled_WithoutConfiguredToken_RemainsFetchDiagnostic()
    {
        var options = new RunOptions
        {
            DownloadCode = (_, _) => throw new OperationCanceledException("stray downloader cancellation"),
        };

        var result = await Parser.ParseAsync(Source, options);

        var diagnostic = Assert.Single(result.Diagnostics, IsFetchFailure);
        Assert.Contains("stray downloader cancellation", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task NestedModuleCancellation_RestoresDepthInProgressCacheAndReservations()
    {
        using var cancellation = new CancellationTokenSource();
        var diagnostics = new List<Diagnostic>();
        var budget = new SourceProcessingBudget(SourceProcessingLimits.Default);
        var outerSource = $"public Nested = load('{NestedUrl}')";
        var loader = new ModuleLoader(
            diagnostics,
            (url, _) =>
            {
                if (url == ModuleUrl)
                    return ValueTask.FromResult(outerSource);

                Assert.Equal(NestedUrl, url);
                cancellation.Cancel();
                throw new OperationCanceledException("host cancelled nested fetch", cancellation.Token);
            },
            allowedHosts: null,
            budget,
            cancellation.Token);

        var exception = await Assert.ThrowsAsync<OperationCanceledException>(
            async () => await loader.ElaborateAsync(ParseSyntaxRoot(Source)));

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
    public async Task NestedCancellation_PreservesCompletedSiblingModule_AndSkipsRemainingFetches()
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
            (url, _) =>
            {
                switch (url)
                {
                    case ModuleUrl:
                        return ValueTask.FromResult(outerSource);
                    case SiblingUrl:
                        siblingFetches++;
                        return ValueTask.FromResult(SiblingSource);
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

        var exception = await Assert.ThrowsAsync<OperationCanceledException>(
            async () => await loader.ElaborateAsync(ParseSyntaxRoot(Source)));

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
    public async Task RollbackAfterCancellation_FreesBudgetCapacityForANewLoaderOnTheSameBudget()
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
            (url, _) =>
            {
                if (url == OuterUrl)
                    return ValueTask.FromResult(outerSource);

                Assert.Equal(InnerUrl, url);
                firstCancellation.Cancel();
                throw new OperationCanceledException("host cancelled inner fetch", firstCancellation.Token);
            },
            allowedHosts: null,
            budget,
            firstCancellation.Token);

        await Assert.ThrowsAsync<OperationCanceledException>(
            async () => await firstLoader.ElaborateAsync(root));
        Assert.Equal(0, budget.ModuleCount);
        Assert.Equal(0, budget.AggregateSource);

        using var secondCancellation = new CancellationTokenSource();
        var secondDiagnostics = new List<Diagnostic>();
        var secondLoader = new ModuleLoader(
            secondDiagnostics,
            (url, _) => ValueTask.FromResult(url == OuterUrl ? outerSource : InnerSource),
            allowedHosts: null,
            budget,
            secondCancellation.Token);

        _ = await secondLoader.ElaborateAsync(root);

        Assert.Empty(secondDiagnostics);
        Assert.Equal(2, budget.ModuleCount);
        Assert.Equal(outerSource.Length + InnerSource.Length, budget.AggregateSource);
        Assert.Equal(2, secondLoader.CachedModuleCount);
    }

    [Fact]
    public async Task CancelledLoader_SecondElaborateThrows_WithoutDisturbingCommittedState()
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
            (url, _) =>
            {
                fetches++;
                if (url == CompletedUrl)
                    return ValueTask.FromResult(CompletedSource);

                Assert.Equal(ModuleUrl, url);
                cancellation.Cancel();
                throw new OperationCanceledException("host cancelled second fetch", cancellation.Token);
            },
            allowedHosts: null,
            budget,
            cancellation.Token);

        await Assert.ThrowsAsync<OperationCanceledException>(async () => await loader.ElaborateAsync(root));
        Assert.Equal(2, fetches);
        Assert.Equal(1, loader.CachedModuleCount);
        Assert.Equal(1, budget.ModuleCount);
        Assert.Equal(CompletedSource.Length, budget.AggregateSource);

        // Reuse of the cancelled loader is deterministic: its fixed token is still cancelled, so
        // a second elaboration throws immediately without fetching, double-rolling-back, or
        // touching the committed module state.
        await Assert.ThrowsAsync<OperationCanceledException>(async () => await loader.ElaborateAsync(root));
        Assert.Equal(2, fetches);
        Assert.Equal(1, loader.CachedModuleCount);
        Assert.Equal(1, budget.ModuleCount);
        Assert.Equal(CompletedSource.Length, budget.AggregateSource);
        Assert.Equal(0, loader.InProgressModuleCount);
        Assert.Equal(0, budget.CurrentDepth);
    }

    [Fact]
    public async Task SequentialRuns_FreshOptionsAfterCancelledRun_SucceedWithoutCrossRunState()
    {
        var downloads = 0;

        ValueTask<string> Download(string url, CancellationToken token)
        {
            downloads++;
            return ValueTask.FromResult("public Value = 11");
        }

        using var cancellation = new CancellationTokenSource();
        var cancelledOptions = new RunOptions
        {
            SourceProcessingCancellationToken = cancellation.Token,
            DownloadCode = (url, token) =>
            {
                cancellation.Cancel();
                return Download(url, token);
            },
        };

        var exception = await Assert.ThrowsAsync<OperationCanceledException>(
            () => KatLangEngine.RunAsync(Source, cancelledOptions));
        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.Equal(1, downloads);

        var freshOptions = new RunOptions { DownloadCode = Download };

        var result = await KatLangEngine.RunAsync(Source, freshOptions);

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal([11m], success.Atoms);
        Assert.Equal(2, downloads);
    }

    [Fact]
    public async Task ConcurrentRuns_SharingRunOptions_KeepCancellationAndLoaderStateRunLocal()
    {
        const int runCount = 4;
        using var cancellation = new CancellationTokenSource();
        var releaseDownloaders = new TaskCompletionSource(
            TaskCreationOptions.RunContinuationsAsynchronously);
        using var enteredDownloaders = new CountdownEvent(runCount);
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = cancellation.Token,
            DownloadCode = async (_, token) =>
            {
                Assert.Equal(cancellation.Token, token);
                enteredDownloaders.Signal();
                await releaseDownloaders.Task;
                return "public Value = 13";
            },
        };

        var tasks = Enumerable.Range(0, runCount)
            .Select(index => KatLangEngine.RunAsync(
                $"public Module = load('https://katlang.org/cancellation/{index}.kat')\nModule.Value",
                options))
            .ToArray();

        // All four runs are genuinely suspended inside their downloaders at once —
        // run-local loader state and the shared options object never interfere.
        Assert.True(
            enteredDownloaders.Wait(TimeSpan.FromSeconds(10)),
            "Runs did not overlap inside their suspended downloaders.");
        Assert.All(tasks, task => Assert.False(task.IsCompleted));

        releaseDownloaders.SetResult();

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
