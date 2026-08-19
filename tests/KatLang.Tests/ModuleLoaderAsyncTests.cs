namespace KatLang.Tests;

/// <summary>
/// Genuine-suspension coverage for the async-only source-loading contract
/// (<see cref="RunOptions.DownloadCode"/> as
/// <c>Func&lt;string, CancellationToken, ValueTask&lt;string&gt;&gt;</c>): an incomplete
/// download suspends source processing and resumes it at the same logical point, the
/// downloader is never replayed after a suspension, and module loading composes with
/// asynchronous host-operation evaluation inside one run. All gating uses deterministic
/// <see cref="TaskCompletionSource"/> instances — no delays.
/// </summary>
public class ModuleLoaderAsyncTests
{
    private const string ModuleUrl = "https://katlang.org/async/module.kat";
    private const string Source = $"public Module = load('{ModuleUrl}')\nModule.Value";

    private static TaskCompletionSource<string> NewGate()
        => new(TaskCreationOptions.RunContinuationsAsynchronously);

    [Fact]
    public async Task SynchronouslyCompletingDownloader_RunAsyncCompletesSynchronously()
    {
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) =>
            {
                calls++;
                return ValueTask.FromResult("public Value = 42");
            },
        };

        var task = KatLangEngine.RunAsync(Source, options);

        // An in-memory downloader keeps the whole run on the synchronous fast path:
        // the task is already completed when the call returns.
        Assert.True(task.IsCompletedSuccessfully);
        var success = Assert.IsType<RunResult.Success>(await task);
        Assert.Equal([42m], success.Atoms);
        Assert.Equal(1, calls);
    }

    [Fact]
    public async Task RunAsync_WithoutLoadDirectives_NeverInvokesConfiguredDownloader()
    {
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) =>
            {
                calls++;
                return ValueTask.FromResult("public Value = 1");
            },
        };

        var task = KatLangEngine.RunAsync("public X = 3\nX + 4", options);

        Assert.True(task.IsCompletedSuccessfully);
        var success = Assert.IsType<RunResult.Success>(await task);
        Assert.Equal([7m], success.Atoms);
        Assert.Equal(0, calls);
    }

    [Fact]
    public async Task IncompleteDownloader_GenuinelySuspendsAndResumesSourceProcessing()
    {
        var gate = NewGate();
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) =>
            {
                calls++;
                return new ValueTask<string>(gate.Task);
            },
        };

        var task = KatLangEngine.RunAsync(Source, options);

        // Source processing is suspended inside the module fetch: nothing is blocked,
        // nothing has completed, and the downloader ran exactly once.
        Assert.False(task.IsCompleted);
        Assert.Equal(1, calls);

        gate.SetResult("public Value = 5");

        var success = Assert.IsType<RunResult.Success>(await task);
        Assert.Equal([5m], success.Atoms);
        // Resumption continued from the suspension point — the downloader was not replayed.
        Assert.Equal(1, calls);
    }

    [Fact]
    public async Task NestedTransitiveLoads_SuspendPerModule_AndResumeInDependencyOrder()
    {
        const string OuterUrl = "https://katlang.org/async/outer.kat";
        const string InnerUrl = "https://katlang.org/async/inner.kat";
        var outerGate = NewGate();
        var innerGate = NewGate();
        var log = new List<string>();
        var options = new RunOptions
        {
            DownloadCode = (url, _) =>
            {
                lock (log)
                {
                    log.Add(url);
                }

                return url switch
                {
                    OuterUrl => new ValueTask<string>(outerGate.Task),
                    InnerUrl => new ValueTask<string>(innerGate.Task),
                    _ => throw new InvalidOperationException($"unexpected fetch of '{url}'"),
                };
            },
        };

        var task = KatLangEngine.RunAsync($"public Outer = load('{OuterUrl}')\nOuter.Total", options);

        // Only the outer module has been requested; the inner load is not discoverable
        // until the outer source arrives.
        Assert.False(task.IsCompleted);
        Assert.Equal([OuterUrl], log);

        outerGate.SetResult($"public Inner = load('{InnerUrl}')\npublic Total = Inner.Value + 1");

        // The elaboration resumed, discovered the nested load, and suspended again.
        await WaitUntilAsync(() =>
        {
            lock (log)
            {
                return log.Count == 2;
            }
        });
        Assert.False(task.IsCompleted);
        Assert.Equal([OuterUrl, InnerUrl], log);

        innerGate.SetResult("public Value = 9");

        var success = Assert.IsType<RunResult.Success>(await task);
        Assert.Equal([10m], success.Atoms);
        Assert.Equal([OuterUrl, InnerUrl], log);
    }

    [Fact]
    public async Task RepeatedLoadsOfOneUrl_AcrossASuspension_InvokeDownloaderExactlyOnce()
    {
        var gate = NewGate();
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) =>
            {
                calls++;
                return new ValueTask<string>(gate.Task);
            },
        };

        var source =
            $"public First = load('{ModuleUrl}')\n" +
            $"public Second = load('{ModuleUrl}')\n" +
            "First.Value + Second.Value";
        var task = KatLangEngine.RunAsync(source, options);

        Assert.False(task.IsCompleted);
        gate.SetResult("public Value = 6");

        var success = Assert.IsType<RunResult.Success>(await task);
        Assert.Equal([12m], success.Atoms);
        // The second load site was served from the per-run module cache after resumption.
        Assert.Equal(1, calls);
    }

    [Fact]
    public async Task CancellationWhileDownloaderSuspended_PropagatesHostCancellation()
    {
        using var cancellation = new CancellationTokenSource();
        var gate = NewGate();
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = cancellation.Token,
            DownloadCode = (_, _) => new ValueTask<string>(gate.Task),
        };

        var task = KatLangEngine.RunAsync(Source, options);
        Assert.False(task.IsCompleted);

        // The host cancels while the download is suspended; a token-honoring
        // downloader then faults the in-flight download with the host token.
        cancellation.Cancel();
        gate.TrySetCanceled(cancellation.Token);

        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => task);
        Assert.Equal(cancellation.Token, exception.CancellationToken);
    }

    [Fact]
    public async Task CancellationAfterSuspendedModuleReturns_IsObservedBeforeProcessingContinues()
    {
        using var cancellation = new CancellationTokenSource();
        var gate = NewGate();
        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(
            diagnostics,
            (_, _) => new ValueTask<string>(gate.Task),
            allowedHosts: null,
            cancellation.Token);

        var syntax = Parser.ParseSyntax(Source);
        Assert.False(syntax.HasErrors);
        var task = loader.ElaborateAsync(syntax.SyntaxRoot).AsTask();
        Assert.False(task.IsCompleted);

        // The host cancels first, then the download completes successfully: the
        // post-fetch observation wins, and the fetched module is never committed.
        cancellation.Cancel();
        gate.SetResult("public Value = 7");

        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => task);
        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.Equal(0, loader.CachedModuleCount);
        Assert.Equal(0, loader.InProgressModuleCount);
        Assert.DoesNotContain(
            diagnostics,
            d => d.Message.Contains("failed to fetch", StringComparison.Ordinal));
    }

    [Fact]
    public async Task HostCancellationRacingDownloaderCancellation_UsesExactHostToken()
    {
        using var hostCancellation = new CancellationTokenSource();
        using var downloaderCancellation = new CancellationTokenSource();
        var gate = NewGate();
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = hostCancellation.Token,
            DownloadCode = (_, _) => new ValueTask<string>(gate.Task),
        };

        var task = KatLangEngine.RunAsync(Source, options);
        Assert.False(task.IsCompleted);

        // Both parties cancel while the fetch is suspended. The downloader's
        // awaitable carries its own token, but host cancellation is authoritative
        // and must escape with the exact configured source-processing token.
        hostCancellation.Cancel();
        downloaderCancellation.Cancel();
        gate.SetException(new OperationCanceledException(downloaderCancellation.Token));

        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => task);
        Assert.Equal(hostCancellation.Token, exception.CancellationToken);
        Assert.NotEqual(downloaderCancellation.Token, exception.CancellationToken);
    }

    [Fact]
    public async Task DownloaderFaultAfterSuspension_RemainsFetchDiagnostic()
    {
        var gate = NewGate();
        var options = new RunOptions
        {
            DownloadCode = (_, _) => new ValueTask<string>(gate.Task),
        };

        var task = Parser.ParseAsync(Source, options);
        Assert.False(task.IsCompleted);

        gate.SetException(new InvalidOperationException("origin unreachable"));

        var result = await task;
        var diagnostic = Assert.Single(
            result.Diagnostics,
            d => d.Message.Contains("failed to fetch", StringComparison.Ordinal));
        Assert.Contains("origin unreachable", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task ParseFailureInsideSuspendedDownloadedSource_ReportsLoadDiagnostic()
    {
        var gate = NewGate();
        var options = new RunOptions
        {
            DownloadCode = (_, _) => new ValueTask<string>(gate.Task),
        };

        var task = Parser.ParseAsync(Source, options);
        Assert.False(task.IsCompleted);

        gate.SetResult("@@not katlang@@");

        var result = await task;
        Assert.Contains(
            result.Diagnostics,
            d => d.Severity == DiagnosticSeverity.Error
                && d.Message.Contains("not valid KatLang source", StringComparison.Ordinal));
    }

    [Fact]
    public async Task AsyncModuleLoad_ThenAsyncHostOperation_SuspendTwiceInOneRun()
    {
        var downloadGate = NewGate();
        var operationGate = new TaskCompletionSource<Result>(
            TaskCreationOptions.RunContinuationsAsynchronously);
        var operationCalls = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) => new ValueTask<string>(downloadGate.Task),
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync(
                    "Fetch",
                    (_, _) =>
                    {
                        operationCalls++;
                        return new ValueTask<Result>(operationGate.Task);
                    })),
        };

        var task = KatLangEngine.RunAsync(
            $"public Module = load('{ModuleUrl}')\nModule.Value + Fetch", options);

        // First suspension: source processing awaits the module download. The host
        // operation cannot have run yet — evaluation has not started.
        Assert.False(task.IsCompleted);
        Assert.Equal(0, operationCalls);

        downloadGate.SetResult("public Value = 30");

        // Second suspension: evaluation awaits the host operation.
        await WaitUntilAsync(() => operationCalls == 1);
        Assert.False(task.IsCompleted);

        operationGate.SetResult(new Result.Atom(12));

        var success = Assert.IsType<RunResult.Success>(await task);
        Assert.Equal([42m], success.Atoms);
    }

    [Fact]
    public async Task ConcurrentRuns_IndependentDownloadersAndTokens_SeeOnlyTheirOwnState()
    {
        using var firstCancellation = new CancellationTokenSource();
        using var secondCancellation = new CancellationTokenSource();
        var firstGate = NewGate();
        var secondGate = NewGate();
        CancellationToken firstSeen = default;
        CancellationToken secondSeen = default;

        var firstTask = KatLangEngine.RunAsync(Source, new RunOptions
        {
            SourceProcessingCancellationToken = firstCancellation.Token,
            DownloadCode = (_, token) =>
            {
                firstSeen = token;
                return new ValueTask<string>(firstGate.Task);
            },
        });
        var secondTask = KatLangEngine.RunAsync(Source, new RunOptions
        {
            SourceProcessingCancellationToken = secondCancellation.Token,
            DownloadCode = (_, token) =>
            {
                secondSeen = token;
                return new ValueTask<string>(secondGate.Task);
            },
        });

        // Both runs are suspended inside their own downloaders with their own tokens.
        Assert.False(firstTask.IsCompleted);
        Assert.False(secondTask.IsCompleted);
        Assert.Equal(firstCancellation.Token, firstSeen);
        Assert.Equal(secondCancellation.Token, secondSeen);

        // Releasing them in reverse order keeps each run's module content run-local.
        secondGate.SetResult("public Value = 2");
        var secondSuccess = Assert.IsType<RunResult.Success>(await secondTask);
        Assert.Equal([2m], secondSuccess.Atoms);
        Assert.False(firstTask.IsCompleted);

        firstGate.SetResult("public Value = 1");
        var firstSuccess = Assert.IsType<RunResult.Success>(await firstTask);
        Assert.Equal([1m], firstSuccess.Atoms);

        Assert.False(firstCancellation.IsCancellationRequested);
        Assert.False(secondCancellation.IsCancellationRequested);
    }

    /// <summary>
    /// The stack-reserve backstop under the structural gates: on a deliberately tiny
    /// dedicated thread, a host-built load-bearing spine that the structural ceiling
    /// admits cannot be walked safely — the loader reports the structured
    /// stack-exhaustion diagnostic with the placeholder root instead of crashing the
    /// process. The downloader completes synchronously, so the elaboration stays on
    /// that thread throughout.
    /// </summary>
    [Fact]
    public void StackReserveBackstop_OnTinyThread_ReportsStructuredDiagnostic()
    {
        // Each wrap adds TWO counted levels (AlgorithmExpr + Algorithm), so 300 wraps
        // keep the composition safely inside the 640-level structural gate while the
        // load-bearing async spine is far deeper than a tiny thread can hold.
        Expr spine = new Expr.Call(
            new Expr.Resolve("load"),
            [new Expr.StringLiteral(ModuleUrl)]);
        for (var i = 0; i < 300; i++)
        {
            spine = new Expr.AlgorithmExpr(
                new Algorithm.User(null, [], [], [], [spine]));
        }

        var root = new Algorithm.User(null, [], [], [new Property("Deep", new Algorithm.User(null, [], [], [], [spine]))], [new Expr.Num(1)]);

        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(
            diagnostics,
            (_, _) => ValueTask.FromResult("public Value = 1"));

        Algorithm? elaborated = null;
        Exception? failure = null;
        var thread = new Thread(
            () =>
            {
                try
                {
                    var task = loader.ElaborateAsync(root);
                    Assert.True(task.IsCompleted);
                    elaborated = task.GetAwaiter().GetResult();
                }
                catch (Exception ex)
                {
                    failure = ex;
                }
            },
            maxStackSize: 192 * 1024);
        thread.Start();
        thread.Join();

        Assert.Null(failure);
        Assert.NotNull(elaborated);
        Assert.Empty(elaborated!.Output);
        Assert.Contains(
            diagnostics,
            d => d.Message.Contains("remaining stack", StringComparison.Ordinal));
    }

    /// <summary>
    /// Deterministic bounded wait on a condition flipped by a resumed continuation —
    /// the continuation runs on the thread pool, so the observing test polls without
    /// blocking it. Fails loudly instead of hanging the suite.
    /// </summary>
    private static async Task WaitUntilAsync(Func<bool> condition)
    {
        for (var i = 0; i < 1000; i++)
        {
            if (condition())
                return;

            await Task.Delay(10);
        }

        Assert.Fail("Condition was not reached within the bounded wait.");
    }
}
