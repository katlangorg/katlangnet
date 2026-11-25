using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// A downloader failure stays behind the documented fetch boundary even when reading its details
/// fails (finding <c>modules-deferred-downloader-message-getter-escape</c> of the 2026-11-21
/// adversarial investigation, baseline <c>8947d21e</c>). <see cref="Exception.Message"/> is virtual
/// host code, and the loader read it unguarded while building the <c>load: failed to fetch</c>
/// diagnostic, so a getter that threw escaped <see cref="Parser.ParseAsync"/> and, for a branch that
/// loads its modules on demand, the evaluator entry points, as the getter's own exception. The earlier
/// guard of 92abaec0 covered only the abandonment summary of a deferred run's token callbacks.
///
/// <para>Now (see <c>RunOptions.DownloadCode</c> and <c>SourceProcessingCancellationToken</c>): a
/// failure whose message cannot be read is the ordinary <see cref="DiagnosticCode.LoadFetchFailed"/>
/// diagnostic at the load site, naming the exception's type instead of its message, eagerly and at
/// materialization alike; a readable message is quoted exactly as before. Cancellation keeps its
/// established classification: the source-processing token, or a deferred materialization's own
/// cancellation, requested before the details are read or while host code reads them, ends the
/// operation as cancellation carrying the established token, never as a fetch diagnostic and never as
/// the getter's exception; a cancellation exception raised without such a request stays a failed
/// fetch.</para>
///
/// <para>Every downloader is in memory and deterministic, and every wait is bounded by
/// <see cref="HangGuard"/>, a hang guard and never a latency claim. Host-only: Lean has no external
/// modules.</para>
/// </summary>
public class DownloaderFailureDetailTests
{
    private const string ModuleA = "https://katlang.org/detail/a.kat";
    private const string ModuleSource = "public V = 7";
    private const string EagerProgram = $"N = load('{ModuleA}')\nN.V";
    private const string DeferredProgram = $"F(0) = 0\nF(1) = {{\n    N = load('{ModuleA}')\n    N.V\n}}\nF(1)";

    private static readonly TimeSpan HangGuard = TimeSpan.FromSeconds(30);

    private static readonly string UnreadableDetails =
        $"the downloader failed with {typeof(UnreadableMessageException).FullName}, whose message could not be read";

    /// <summary>How the downloader delivers its failure.</summary>
    public enum Delivery
    {
        /// <summary>The delegate throws synchronously.</summary>
        Thrown,

        /// <summary>The delegate returns an already-faulted awaitable.</summary>
        Faulted,

        /// <summary>The delegate genuinely suspends, then faults on resumption.</summary>
        Suspended,
    }

    /// <summary>What the failure's message getter does once it has requested cancellation.</summary>
    public enum Getter
    {
        ReturnsText,
        ThrowsInvalidOperation,
        ThrowsWithTheCancelledToken,
        ThrowsWithAForeignToken,
        ThrowsWithoutAToken,
    }

    /// <summary>A failure whose message getter runs <c>beforeThrow</c> and then throws <c>thrown</c>.</summary>
    private sealed class UnreadableMessageException(Action? beforeThrow = null, Func<Exception>? thrown = null) : Exception
    {
        public int Reads { get; private set; }

        public override string Message
        {
            get
            {
                Reads++;
                beforeThrow?.Invoke();
                throw thrown?.Invoke() ?? new InvalidOperationException("message getter failed");
            }
        }
    }

    /// <summary>
    /// The downloader's own cancellation or timeout (no host token is cancelled) whose message cannot be
    /// read: an ordinary failed fetch, like any downloader-owned cancellation.
    /// </summary>
    private sealed class UnreadableTimeoutException : OperationCanceledException
    {
        public override string Message => throw new InvalidOperationException("message getter failed");
    }

    /// <summary>A failure whose message getter cancels <paramref name="cancellation"/> first, then does what <paramref name="getter"/> says.</summary>
    private sealed class CancellingMessageException(CancellationTokenSource cancellation, Getter getter) : Exception
    {
        public override string Message
        {
            get
            {
                cancellation.Cancel();
                return getter switch
                {
                    Getter.ReturnsText => "read after cancellation",
                    Getter.ThrowsInvalidOperation => throw new InvalidOperationException("message getter failed"),
                    Getter.ThrowsWithTheCancelledToken => throw new OperationCanceledException(cancellation.Token),
                    Getter.ThrowsWithAForeignToken => throw new OperationCanceledException(new CancellationToken(canceled: true)),
                    Getter.ThrowsWithoutAToken => throw new OperationCanceledException(),
                    _ => throw new ArgumentOutOfRangeException(nameof(getter)),
                };
            }
        }
    }

    private static async ValueTask<string> Fail(Delivery delivery, Exception failure)
    {
        switch (delivery)
        {
            case Delivery.Thrown:
                throw failure;
            case Delivery.Faulted:
                return await ValueTask.FromException<string>(failure);
            default:
                await Task.Yield();
                throw failure;
        }
    }

    // The delegate itself: a synchronous throw must leave the delegate, not an async wrapper around it.
    private static Func<string, CancellationToken, ValueTask<string>> Failing(Delivery delivery, Func<Exception> failure)
        => (_, _) => delivery == Delivery.Thrown ? throw failure() : Fail(delivery, failure());

    private static DeferredModuleRegion RegionOf(Algorithm root)
    {
        var family = Assert.IsType<Algorithm.Conditional>(root.Properties.Single(property => property.Name == "F").Value);
        return Assert.IsType<DeferredModuleRegion>(family.Branches[1].Body.DeferredRegion);
    }

    private static Task<EvalResult<IReadOnlyList<Decimal128>>> RunFlat(Algorithm root, CancellationToken cancellationToken = default)
        => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), limits: null, cancellationToken);

    // The materialization failure under the call frames the selection added.
    private static EvalError.ModuleRegionMaterializationFailed MaterializationFailure(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(error);
    }

    private static async Task AssertGateFree(DeferredModuleRegion region)
    {
        await region.Loader.MaterializationGate.WaitAsync().WaitAsync(HangGuard);
        region.Loader.MaterializationGate.Release();
    }

    private static Algorithm ParseSyntaxRoot(string source)
    {
        var syntax = Parser.ParseSyntax(source);
        Assert.False(syntax.HasErrors);
        return syntax.SyntaxRoot;
    }

    // ── 1. An unreadable message is an ordinary failed fetch ──────────────────

    [Theory]
    [InlineData(Delivery.Thrown)]
    [InlineData(Delivery.Faulted)]
    [InlineData(Delivery.Suspended)]
    public async Task EagerLoad_UnreadableMessage_IsTheOrdinaryFetchFailure_AtTheSameSite(Delivery delivery)
    {
        var unreadable = await Parser.ParseAsync(EagerProgram, new RunOptions
        {
            DownloadCode = Failing(delivery, () => new UnreadableMessageException()),
        }).WaitAsync(HangGuard);
        var readable = await Parser.ParseAsync(EagerProgram, new RunOptions
        {
            DownloadCode = Failing(delivery, () => new InvalidOperationException("network down")),
        }).WaitAsync(HangGuard);

        // The readable twin is the established diagnostic, quoted exactly as before.
        var twin = Assert.Single(readable.Diagnostics);
        Assert.Equal(DiagnosticCode.LoadFetchFailed, twin.Code);
        Assert.Equal($"load: failed to fetch '{ModuleA}': network down", twin.Message);

        // Same code, severity and load-site span; only the quoted details name the type instead.
        var failure = Assert.Single(unreadable.Diagnostics);
        Assert.Equal(twin.Code, failure.Code);
        Assert.Equal(twin.Severity, failure.Severity);
        Assert.Equal(twin.Span, failure.Span);
        Assert.Equal(1, Assert.NotNull(failure.Span).Start.Line);
        Assert.Equal($"load: failed to fetch '{ModuleA}': {UnreadableDetails}", failure.Message);

        // The engine's source gate reports it as the parse failure it is.
        var run = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(EagerProgram, new RunOptions
        {
            DownloadCode = Failing(delivery, () => new UnreadableMessageException()),
        }).WaitAsync(HangGuard));
        var error = Assert.Single(run.Errors);
        Assert.Equal(KatLangErrorCode.LoadFetchFailed, error.Code);
        Assert.Equal(failure.Message, error.Message);
    }

    [Theory]
    [InlineData(Delivery.Thrown)]
    [InlineData(Delivery.Faulted)]
    [InlineData(Delivery.Suspended)]
    public async Task DeferredLoad_UnreadableMessage_IsTheOrdinaryMaterializationFailure_AndTheBranchStaysRetryable(Delivery delivery)
    {
        var fail = true;
        var downloads = 0;
        var options = new RunOptions
        {
            DownloadCode = (url, token) =>
            {
                downloads++;
                return Volatile.Read(ref fail)
                    ? Failing(delivery, () => new UnreadableMessageException())(url, token)
                    : ValueTask.FromResult(ModuleSource);
            },
        };
        var readableOptions = new RunOptions { DownloadCode = Failing(delivery, () => new InvalidOperationException("network down")) };

        // Engine: the materialization failure carries the one fetch diagnostic at the branch's load site.
        var twin = Assert.Single(Assert.IsType<RunResult.EvalFailure>(
            await KatLangEngine.RunAsync(DeferredProgram, readableOptions).WaitAsync(HangGuard)).Errors);
        var failure = Assert.Single(Assert.IsType<RunResult.EvalFailure>(
            await KatLangEngine.RunAsync(DeferredProgram, options).WaitAsync(HangGuard)).Errors);
        Assert.Equal(KatLangErrorCode.LoadFetchFailed, twin.Code);
        Assert.Equal(twin.Code, failure.Code);
        Assert.Equal(twin.Span, failure.Span);
        Assert.Equal(3, Assert.NotNull(failure.Span).Start.Line);
        Assert.EndsWith($"load: failed to fetch '{ModuleA}': network down", twin.Message, StringComparison.Ordinal);
        Assert.EndsWith($"load: failed to fetch '{ModuleA}': {UnreadableDetails}", failure.Message, StringComparison.Ordinal);
        Assert.Equal(twin.Message.Replace("network down", UnreadableDetails, StringComparison.Ordinal), failure.Message);

        // Evaluator over a retained tree: a structured failure, never an exception, and never cached.
        var parsed = await SourceProvenance.ParseValidAsync(DeferredProgram, options);
        var region = RegionOf(parsed.Root);
        downloads = 0;
        var result = await RunFlat(parsed.Root).WaitAsync(HangGuard);
        Assert.True(result.IsError);
        Assert.Equal(KatLangErrorCode.LoadFetchFailed, result.Error.Code);
        var materialization = MaterializationFailure(result.Error);
        Assert.Equal(DiagnosticCode.LoadFetchFailed, Assert.Single(materialization.Diagnostics).Code);
        Assert.Equal(1, downloads);
        Assert.False(region.IsMaterialized);
        await AssertGateFree(region);

        Volatile.Write(ref fail, false);
        var retried = await RunFlat(parsed.Root).WaitAsync(HangGuard);
        Assert.False(retried.IsError, retried.IsError ? retried.Error.ToString() : "");
        Assert.Equal([(Decimal128)7], retried.Value);
        Assert.Equal(2, downloads);
        Assert.True(region.IsMaterialized);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task DownloaderOwnedCancellation_WithAnUnreadableMessage_StaysAnOrdinaryFetchFailure(bool deferred)
    {
        // No host token is cancelled: a downloader's own cancellation or timeout is a failed fetch
        // (the established classification), whatever its message getter does.
        using var source = new CancellationTokenSource();
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = source.Token,
            DownloadCode = (_, _) => throw new UnreadableTimeoutException(),
        };
        var details = $"the downloader failed with {typeof(UnreadableTimeoutException).FullName}, whose message could not be read";

        if (!deferred)
        {
            var diagnostic = Assert.Single((await Parser.ParseAsync(EagerProgram, options)).Diagnostics);
            Assert.Equal(DiagnosticCode.LoadFetchFailed, diagnostic.Code);
            Assert.Equal($"load: failed to fetch '{ModuleA}': {details}", diagnostic.Message);
        }
        else
        {
            var parsed = await SourceProvenance.ParseValidAsync(DeferredProgram, options);
            var result = await RunFlat(parsed.Root).WaitAsync(HangGuard);
            Assert.True(result.IsError);
            var materialization = MaterializationFailure(result.Error);
            var diagnostic = Assert.Single(materialization.Diagnostics);
            Assert.Equal(DiagnosticCode.LoadFetchFailed, diagnostic.Code);
            Assert.Equal($"load: failed to fetch '{ModuleA}': {details}", diagnostic.Message);
        }

        Assert.False(source.IsCancellationRequested);
    }

    // ── 2. Cancellation keeps its classification and identity ─────────────────

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task HostCancellationBeforeTheDetailsAreRead_WinsWithoutReadingThem(bool deferred)
    {
        // The downloader raced the host's cancellation and failed with an unreadable message: the token
        // decides first, so the host code behind Message never runs.
        using var source = new CancellationTokenSource();
        var failure = new UnreadableMessageException();
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = source.Token,
            DownloadCode = (_, _) =>
            {
                source.Cancel();
                throw failure;
            },
        };

        Task run;
        if (deferred)
        {
            var root = (await SourceProvenance.ParseValidAsync(DeferredProgram, options)).Root;
            run = RunFlat(root);
        }
        else
        {
            run = Parser.ParseAsync(EagerProgram, options);
        }

        var cancelled = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run.WaitAsync(HangGuard));
        Assert.Equal(source.Token, cancelled.CancellationToken);
        Assert.Equal(0, failure.Reads);
    }

    [Theory]
    [InlineData(Getter.ReturnsText)]
    [InlineData(Getter.ThrowsInvalidOperation)]
    [InlineData(Getter.ThrowsWithTheCancelledToken)]
    [InlineData(Getter.ThrowsWithAForeignToken)]
    [InlineData(Getter.ThrowsWithoutAToken)]
    public async Task EagerLoad_SourceCancelledWhileTheMessageIsRead_IsHostCancellation_WithTheConfiguredToken(Getter getter)
    {
        // The public parse.
        using (var source = new CancellationTokenSource())
        {
            var options = new RunOptions
            {
                SourceProcessingCancellationToken = source.Token,
                DownloadCode = (_, _) => throw new CancellingMessageException(source, getter),
            };
            var cancelled = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Parser.ParseAsync(EagerProgram, options));
            Assert.Equal(source.Token, cancelled.CancellationToken);
        }

        // The loader itself: no fetch diagnostic, nothing committed, the invocation still charged.
        using (var source = new CancellationTokenSource())
        {
            var diagnostics = new DiagnosticBag();
            var budget = new SourceProcessingBudget(SourceProcessingLimits.Default);
            var loader = new ModuleLoader(
                diagnostics,
                (_, _) => throw new CancellingMessageException(source, getter),
                allowedHosts: null,
                budget,
                source.Token);

            var cancelled = await Assert.ThrowsAnyAsync<OperationCanceledException>(
                async () => await loader.ElaborateAsync(ParseSyntaxRoot(EagerProgram)));

            Assert.Equal(source.Token, cancelled.CancellationToken);
            Assert.DoesNotContain(diagnostics, diagnostic => diagnostic.Code == DiagnosticCode.LoadFetchFailed);
            Assert.Equal(0, loader.CachedModuleCount);
            Assert.Equal(0, loader.InProgressModuleCount);
            Assert.Equal(0, budget.CurrentDepth);
            Assert.Equal(1, budget.ModuleCount);
            Assert.Equal(0, budget.AggregateSource);
        }
    }

    [Theory]
    [InlineData(Getter.ReturnsText)]
    [InlineData(Getter.ThrowsInvalidOperation)]
    [InlineData(Getter.ThrowsWithTheCancelledToken)]
    [InlineData(Getter.ThrowsWithAForeignToken)]
    [InlineData(Getter.ThrowsWithoutAToken)]
    public async Task DeferredLoad_SourceCancelledWhileTheMessageIsRead_IsHostCancellation_WithTheSourceToken(Getter getter)
    {
        using var source = new CancellationTokenSource();
        using var evaluation = new CancellationTokenSource();
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = source.Token,
            DownloadCode = (_, _) => throw new CancellingMessageException(source, getter),
        };
        var root = (await SourceProvenance.ParseValidAsync(DeferredProgram, options)).Root;
        var region = RegionOf(root);

        var cancelled = await Assert.ThrowsAnyAsync<OperationCanceledException>(
            () => RunFlat(root, evaluation.Token).WaitAsync(HangGuard));

        Assert.Equal(source.Token, cancelled.CancellationToken);
        Assert.False(evaluation.IsCancellationRequested);
        Assert.False(region.IsMaterialized);
        Assert.Equal(1, region.MaterializationAttempts);
        Assert.Equal(0, region.Loader.CachedModuleCount);
        Assert.Equal(0, region.Loader.InProgressModuleCount);
        await AssertGateFree(region);
    }

    [Theory]
    [InlineData(Getter.ReturnsText)]
    [InlineData(Getter.ThrowsInvalidOperation)]
    [InlineData(Getter.ThrowsWithTheCancelledToken)]
    [InlineData(Getter.ThrowsWithoutAToken)]
    public async Task DeferredLoad_EvaluationCancelledWhileTheMessageIsRead_LeavesWithTheEvaluationToken_AndARetrySucceeds(Getter getter)
    {
        // The materialization's own cancellation (its only consumer leaves) is as authoritative over the
        // fetch diagnostic as the source token, and the region maps it to the evaluation's token.
        using var evaluation = new CancellationTokenSource();
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) => Interlocked.Increment(ref calls) == 1
                ? throw new CancellingMessageException(evaluation, getter)
                : ValueTask.FromResult(ModuleSource),
        };
        var root = (await SourceProvenance.ParseValidAsync(DeferredProgram, options)).Root;
        var region = RegionOf(root);

        var cancelled = await Assert.ThrowsAnyAsync<OperationCanceledException>(
            () => RunFlat(root, evaluation.Token).WaitAsync(HangGuard));

        Assert.Equal(evaluation.Token, cancelled.CancellationToken);
        Assert.False(region.IsMaterialized);
        Assert.Equal(1, region.AbandonedRuns);
        await AssertGateFree(region);

        var retried = await RunFlat(root).WaitAsync(HangGuard);
        Assert.False(retried.IsError, retried.IsError ? retried.Error.ToString() : "");
        Assert.Equal([(Decimal128)7], retried.Value);
        Assert.Equal(2, calls);
        Assert.True(region.IsMaterialized);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task AGetterCancellationException_WithoutRequestedCancellation_IsAnOrdinaryFetchFailure(bool deferred)
    {
        // An OperationCanceledException carrying the configured token is cancellation only when that
        // token was cancelled; raised by a message getter of a still-active run, it is a failed fetch.
        using var source = new CancellationTokenSource();
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = source.Token,
            DownloadCode = (_, _) => throw new UnreadableMessageException(thrown: () => new OperationCanceledException(source.Token)),
        };

        Diagnostic diagnostic;
        if (!deferred)
        {
            diagnostic = Assert.Single((await Parser.ParseAsync(EagerProgram, options)).Diagnostics);
        }
        else
        {
            var parsed = await SourceProvenance.ParseValidAsync(DeferredProgram, options);
            var result = await RunFlat(parsed.Root).WaitAsync(HangGuard);
            Assert.True(result.IsError);
            diagnostic = Assert.Single(MaterializationFailure(result.Error).Diagnostics);
        }

        Assert.Equal(DiagnosticCode.LoadFetchFailed, diagnostic.Code);
        Assert.Equal($"load: failed to fetch '{ModuleA}': {UnreadableDetails}", diagnostic.Message);
        Assert.False(source.IsCancellationRequested);
    }

    // ── 3. The rendering helper ───────────────────────────────────────────────

    [Fact]
    public void EchoDownloaderFailure_QuotesAReadableMessage_AsTheHostMessageEcho_AndNamesTheTypeOtherwise()
    {
        var hostile = "HTTP 404 \u001B[2J" + new string('x', ModuleLoadTarget.MaxEchoedHostMessageLength);
        Assert.Equal(ModuleLoadTarget.EchoHostMessage(hostile), ModuleLoadTarget.EchoDownloaderFailure(new InvalidOperationException(hostile)));
        Assert.Equal(UnreadableDetails, ModuleLoadTarget.EchoDownloaderFailure(new UnreadableMessageException()));

        // A getter that fails while an aggregate renders its inner messages fails the aggregate's getter too.
        var aggregate = new AggregateException(new UnreadableMessageException());
        Assert.Equal(
            $"the downloader failed with {typeof(AggregateException).FullName}, whose message could not be read",
            ModuleLoadTarget.EchoDownloaderFailure(aggregate));
    }
}
