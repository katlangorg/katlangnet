using System.Diagnostics;
using System.Net;
using System.Net.Http.Headers;
using System.Text;

namespace KatLang.CLI.Tests;

/// <summary>
/// The shipped CLI transport's own policies (<see cref="HttpSourceDownloader"/>):
/// the response-body byte ceiling, the whole-download deadline, and how each
/// failure reaches KatLang — a failed fetch for the transport's refusals and
/// timeouts, a cancellation only for the caller's own token. Real loopback
/// sockets cover the transport-level behaviors (stalls, trickles, endless and
/// over-declared bodies); scripted handlers cover byte-exact boundaries,
/// decoding, consumption accounting, and disposal, where a real socket's
/// buffering would blur the numbers.
/// </summary>
public sealed class HttpSourceDownloaderTests
{
    private const int Failure = 1;

    /// <summary>
    /// Outer guard so a transport that never finishes cannot hang the run. It is never
    /// handed to the code under test: a bound that fails to fire shows up as an assertion.
    /// </summary>
    private static readonly TimeSpan Watchdog = TimeSpan.FromSeconds(60);

    /// <summary>A deadline no passing test approaches; deadline tests set their own.</summary>
    private static readonly TimeSpan LongDeadline = TimeSpan.FromSeconds(20);

    private static readonly TimeSpan ShortDeadline = TimeSpan.FromMilliseconds(1500);

    private const string ModuleUrl = "https://katlang.org/demo/cli-transport-lib.kat";
    private const string LoadingSource = $"open '{ModuleUrl}'\nVal\n";

    // ── Production wiring ───────────────────────────────────────────────────

    [Fact]
    public void Shared_InstallsTheDocumentedFiniteBounds()
    {
        Assert.Equal(1_048_576L, HttpSourceDownloader.MaxResponseBodyBytes);
        Assert.NotEqual((long)SourceProcessingLimits.MaxSupportedSourceLength, HttpSourceDownloader.MaxResponseBodyBytes);
        Assert.Equal(TimeSpan.FromSeconds(15), HttpSourceDownloader.DownloadTimeout);

        Assert.Equal(HttpSourceDownloader.MaxResponseBodyBytes, HttpSourceDownloader.Shared.ConfiguredMaxResponseBodyBytes);
        Assert.Equal(HttpSourceDownloader.DownloadTimeout, HttpSourceDownloader.Shared.ConfiguredDownloadTimeout);
    }

    [Fact]
    public async Task AllowLoading_LibraryAcceptableSource_CanExceedTheShippedTransportByteLimit()
    {
        // A legal module with a UTF-8 comment: about 350k UTF-16 units, just over 1 MiB
        // encoded. The control proves that the library accepts this exact module.
        var module = "public Val = 42\n#" + new string('€', 1_048_576 / 3);
        Assert.True(module.Length < SourceProcessingLimits.MaxSupportedSourceLength);
        var control = await Guarded(Cli.InvokeWithDownloaderAsync(
            (_, _) => ValueTask.FromResult(module), "eval", LoadingSource, "--allow-loading"));
        Assert.Equal(0, control.ExitCode);
        Assert.Equal("42", control.Output.Trim());
        Assert.Equal("", control.Error);

        var body = Encoding.UTF8.GetBytes(module);
        Assert.True(body.Length > HttpSourceDownloader.MaxResponseBodyBytes);
        var content = ScriptedContent.Bytes(body, declaredLength: body.Length);
        using var transport = Transport(
            HttpSourceDownloader.MaxResponseBodyBytes,
            HttpSourceDownloader.DownloadTimeout,
            ScriptedHandler.Serving(content));
        var refused = await Guarded(Cli.InvokeWithDownloaderAsync(
            transport.DownloadAsync, "eval", LoadingSource, "--allow-loading"));
        Assert.Equal(Failure, refused.ExitCode);
        Assert.Equal("", refused.Output);
        Assert.Contains("load: failed to fetch", refused.TrimmedError);
        Assert.Contains("1048576-byte limit", refused.TrimmedError);
        Assert.Equal(0, content.SerializeCalls); // refused by transport before source decoding
        Assert.True(content.Disposed);
    }

    [Theory]
    [InlineData(-1L, 1000)]
    [InlineData((long)int.MaxValue + 1, 1000)]
    [InlineData(64L, 0)]
    [InlineData(64L, -1)] // Timeout.InfiniteTimeSpan
    public void Constructor_RejectsUnboundedOrNegativeLimits(long maxResponseBodyBytes, int timeoutMilliseconds)
        => Assert.Throws<ArgumentOutOfRangeException>(
            () => new HttpSourceDownloader(maxResponseBodyBytes, TimeSpan.FromMilliseconds(timeoutMilliseconds)));

    // ── Successful downloads and boundaries ─────────────────────────────────

    [Fact]
    public async Task Download_SmallModule_OverRealTransport_ReturnsItsText()
    {
        await using var server = new LoopbackHttpServer(() => LoopbackHttpServer.Ok("public Value = 42"));
        using var transport = Transport(HttpSourceDownloader.MaxResponseBodyBytes, HttpSourceDownloader.DownloadTimeout);

        var text = await Guarded(transport.DownloadAsync(server.Url("127.0.0.1"), CancellationToken.None).AsTask());

        Assert.Equal("public Value = 42", text);
        Assert.Equal(1, server.RequestCount);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public async Task Download_EmptyBody_ReturnsEmptyText(bool declaredLength)
    {
        var content = ScriptedContent.Bytes([], declaredLength ? 0 : null);
        using var transport = Transport(64, handler: ScriptedHandler.Serving(content));

        Assert.Equal("", await Guarded(transport.DownloadAsync(ModuleUrl, CancellationToken.None).AsTask()));
        Assert.True(content.Disposed);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public async Task Download_BodyExactlyAtTheCeiling_Succeeds(bool declaredLength)
    {
        var body = Encoding.ASCII.GetBytes(new string('x', 64));
        var content = ScriptedContent.Bytes(body, declaredLength ? body.Length : null);
        using var transport = Transport(64, handler: ScriptedHandler.Serving(content));

        var text = await Guarded(transport.DownloadAsync(ModuleUrl, CancellationToken.None).AsTask());

        Assert.Equal(new string('x', 64), text);
        Assert.Equal(64, content.BytesWritten);
        Assert.True(content.Disposed);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public async Task Download_BodyOneByteOverTheCeiling_IsRefused(bool declaredLength)
    {
        var body = Encoding.ASCII.GetBytes(new string('x', 65));
        var content = ScriptedContent.Bytes(body, declaredLength ? body.Length : null, writeSize: 1);
        using var transport = Transport(64, handler: ScriptedHandler.Serving(content));

        var exception = await Assert.ThrowsAsync<HttpRequestException>(
            () => Guarded(transport.DownloadAsync(ModuleUrl, CancellationToken.None).AsTask()));

        Assert.Equal(HttpRequestError.ConfigurationLimitExceeded, exception.HttpRequestError);
        Assert.Contains("64-byte limit", exception.Message);
        if (declaredLength)
        {
            // Refused from the header alone.
            Assert.Contains("Content-Length of 65 bytes", exception.Message);
            Assert.Equal(0, content.SerializeCalls);
        }
        else
        {
            // The 65th byte is the one refused.
            Assert.Equal(64, content.BytesWritten);
        }

        Assert.True(content.Disposed);
    }

    [Fact]
    public async Task Download_NonAsciiModule_IsMeasuredInBytes_NotUtf16CodeUnits()
    {
        // 14 code units, 30 UTF-8 bytes. The ceiling is a byte ceiling: a cap equal to the
        // byte size admits the module, and a cap equal to the code-unit count would not.
        // The fixed CLI policy measures the content bytes the source encoding requires.
        const string module = "V = '€€€€€€€€'";
        var bytes = Encoding.UTF8.GetBytes(module);
        Assert.Equal(14, module.Length);
        Assert.Equal(30, bytes.Length);

        using (var transport = Transport(bytes.Length, handler: ScriptedHandler.Serving(ScriptedContent.Bytes(bytes))))
        {
            Assert.Equal(module, await Guarded(transport.DownloadAsync(ModuleUrl, CancellationToken.None).AsTask()));
        }

        using (var transport = Transport(module.Length, handler: ScriptedHandler.Serving(ScriptedContent.Bytes(bytes))))
        {
            var exception = await Assert.ThrowsAsync<HttpRequestException>(
                () => Guarded(transport.DownloadAsync(ModuleUrl, CancellationToken.None).AsTask()));
            Assert.Equal(HttpRequestError.ConfigurationLimitExceeded, exception.HttpRequestError);
        }
    }

    [Theory]
    [InlineData(1)]
    [InlineData(3)]
    [InlineData(7)]
    public async Task Download_MultiByteSequencesSplitAcrossWrites_DecodeIntact(int writeSize)
    {
        // U+20AC is 3 UTF-8 bytes; U+1F600 is 4 bytes and a surrogate pair; U+00E9 is 2.
        // Every write size here splits some sequence, and decoding happens only after the
        // bounded buffering has assembled the complete body.
        const string module = "Total = '€\U0001F600é'";
        var content = ScriptedContent.Bytes(Encoding.UTF8.GetBytes(module), writeSize: writeSize);
        using var transport = Transport(64, handler: ScriptedHandler.Serving(content));

        Assert.Equal(module, await Guarded(transport.DownloadAsync(ModuleUrl, CancellationToken.None).AsTask()));
    }

    public static TheoryData<string, byte[], string?, string?, string> DecodingCases()
    {
        const string text = "V = 'é€'";
        return new()
        {
            { "utf-8 charset", Encoding.UTF8.GetBytes(text), "text/plain", "utf-8", text },
            { "utf-8 byte-order mark, no charset", [.. Encoding.UTF8.GetPreamble(), .. Encoding.UTF8.GetBytes(text)], "text/plain", null, text },
            { "no Content-Type at all (UTF-8 default)", Encoding.UTF8.GetBytes(text), null, null, text },
            { "utf-16 charset, no byte-order mark", Encoding.Unicode.GetBytes(text), "text/plain", "utf-16", text },
            { "utf-16 little-endian byte-order mark", [.. Encoding.Unicode.GetPreamble(), .. Encoding.Unicode.GetBytes(text)], "text/plain", null, text },
            { "utf-16 big-endian byte-order mark", [.. Encoding.BigEndianUnicode.GetPreamble(), .. Encoding.BigEndianUnicode.GetBytes(text)], "text/plain", null, text },
            { "utf-32 byte-order mark", [.. Encoding.UTF32.GetPreamble(), .. Encoding.UTF32.GetBytes(text)], "text/plain", null, text },
            { "iso-8859-1 charset", Encoding.Latin1.GetBytes("V = 'é'"), "text/plain", "iso-8859-1", "V = 'é'" },
            { "us-ascii charset", Encoding.ASCII.GetBytes("V = 1"), "text/plain", "us-ascii", "V = 1" },
            { "quoted charset and matching BOM", [.. Encoding.Unicode.GetPreamble(), .. Encoding.Unicode.GetBytes(text)], "text/plain", "\"utf-16\"", text },
            { "utf-32 big-endian charset and BOM", [.. new UTF32Encoding(true, true).GetPreamble(), .. new UTF32Encoding(true, true).GetBytes(text)], "text/plain", "utf-32BE", text },
            { "charset overrides a conflicting BOM", [0xEF, 0xBB, 0xBF, 0x78], "text/plain", "iso-8859-1", "ï»¿x" },
            { "truncated UTF-8 replacement", [0xF0, 0x90, 0x80], "text/plain", "utf-8", "\uFFFD" },
            { "unpaired UTF-16 replacement", [0x00, 0xD8], "text/plain", "utf-16", "\uFFFD" },
            { "invalid UTF-32 scalar replacement", [0x00, 0x00, 0x11, 0x00], "text/plain", "utf-32", "\uFFFD" },
            { "empty body bypasses charset lookup", [], "text/plain", "no-such-charset", "" },
        };
    }

    [Theory]
    [MemberData(nameof(DecodingCases))]
    public async Task Download_DecodesTheSupportedCharsetsAndByteOrderMarks_AsBefore(
        string label, byte[] body, string? mediaType, string? charset, string expected)
    {
        // The ceiling is set to the body's exact size, byte-order mark included: the mark
        // counts toward the content limit and is still handled by the unchanged decoding.
        using var oldContent = ScriptedContent.Bytes(body, mediaType: mediaType, charset: charset, writeSize: 3);
        Assert.Equal(expected, await oldContent.ReadAsStringAsync());
        var content = ScriptedContent.Bytes(body, mediaType: mediaType, charset: charset, writeSize: 3);
        using var transport = Transport(body.Length, handler: ScriptedHandler.Serving(content));

        var text = await Guarded(transport.DownloadAsync(ModuleUrl, CancellationToken.None).AsTask());

        Assert.True(expected == text, $"{label}: expected {Show(expected)} but decoded {Show(text)}");
        Assert.Equal(1, content.SerializeCalls); // decoding did not acquire the body a second time
        Assert.True(content.Disposed);
    }

    [Theory]
    [InlineData("windows-1252")]
    [InlineData("no-such-charset")]
    public async Task Download_UnsupportedCharset_FailsExactlyAsTheUnboundedReadDid(string charset)
    {
        // Pre-existing HttpContent.ReadAsStringAsync behavior, pinned so bounded buffering is
        // shown not to change decoding failures; KatLang reports it as a failed fetch.
        var content = ScriptedContent.Bytes(Encoding.ASCII.GetBytes("V = 1"), charset: charset);
        using var transport = Transport(64, handler: ScriptedHandler.Serving(content));

        var exception = await Assert.ThrowsAsync<InvalidOperationException>(
            () => Guarded(transport.DownloadAsync(ModuleUrl, CancellationToken.None).AsTask()));

        Assert.Contains("character set", exception.Message, StringComparison.OrdinalIgnoreCase);
        Assert.True(content.Disposed);
    }

    [Fact]
    public void ShippedEncodingConfiguration_DoesNotEnableUtf7()
        => Assert.Throws<NotSupportedException>(() => Encoding.GetEncoding("utf-7"));

    // ── Oversized responses ─────────────────────────────────────────────────

    [Fact]
    public async Task Download_ExcessiveDeclaredLength_IsRefusedWithoutReadingTheBody()
    {
        const long declared = 1L << 40;
        var content = ScriptedContent.Endless(writeSize: 4096, declaredLength: declared);
        using var transport = Transport(64 * 1024, handler: ScriptedHandler.Serving(content));

        var exception = await Assert.ThrowsAsync<HttpRequestException>(
            () => Guarded(transport.DownloadAsync(ModuleUrl, CancellationToken.None).AsTask()));

        Assert.Equal(HttpRequestError.ConfigurationLimitExceeded, exception.HttpRequestError);
        Assert.Contains($"Content-Length of {declared} bytes", exception.Message);
        Assert.Equal(0, content.SerializeCalls);
        Assert.Equal(0, content.BytesAttempted);
        Assert.True(content.Disposed);
    }

    [Fact]
    public async Task Download_ExcessiveDeclaredLength_OverRealTransport_IsRefusedAtTheHeaders()
    {
        const long declared = 64L * 1024 * 1024;
        var piece = new byte[4096];
        Array.Fill(piece, (byte)'x');
        await using var server = new LoopbackHttpServer(async connection =>
        {
            await connection.WriteAsync(LoopbackHttpServer.OkHead($"Content-Length: {declared}"));
            // Push body until the client goes away — capped, so a transport that kept reading
            // could not make the fixture unbounded.
            for (long sent = 0; sent < 4 * 1024 * 1024 && await connection.TryWriteAsync(piece); sent += piece.Length)
            {
            }

            await connection.WaitForClientToDisconnectAsync();
        });
        using var transport = Transport(64 * 1024);

        var exception = await Assert.ThrowsAsync<HttpRequestException>(
            () => Guarded(transport.DownloadAsync(server.Url("127.0.0.1"), CancellationToken.None).AsTask()));

        Assert.Equal(HttpRequestError.ConfigurationLimitExceeded, exception.HttpRequestError);
        Assert.Contains($"Content-Length of {declared} bytes", exception.Message);
        // The refusal closed the connection instead of taking the declared body.
        await Guarded(server.ClientDisconnected);
    }

    [Fact]
    public async Task Download_UnknownLengthBody_IsStoppedByTheRunningCeiling_WithBoundedReadAhead()
    {
        const int ceiling = 64 * 1024;
        const int writeSize = 4096;
        var content = ScriptedContent.Endless(writeSize);
        using var transport = Transport(ceiling, handler: ScriptedHandler.Serving(content));

        var exception = await Assert.ThrowsAsync<HttpRequestException>(
            () => Guarded(transport.DownloadAsync(ModuleUrl, CancellationToken.None).AsTask()));

        Assert.Equal(HttpRequestError.ConfigurationLimitExceeded, exception.HttpRequestError);
        Assert.Contains($"{ceiling}-byte limit", exception.Message);
        // Everything up to the ceiling was accepted; the write that would cross it was
        // refused, so consumption is the ceiling plus at most one write, never more.
        Assert.Equal(ceiling, content.BytesWritten);
        Assert.True(content.BytesAttempted <= ceiling + writeSize);
        Assert.True(content.Disposed);
    }

    [Fact]
    public async Task Download_SyntheticUnderDeclaredContent_StillHonorsTheRunningLimit()
    {
        // HttpContent can lie about its length; real HTTP framing exposes only Content-Length
        // bytes. This pins the buffer's write limit, not a claim about real HTTP framing.
        var content = ScriptedContent.Endless(writeSize: 8, declaredLength: 1);
        using var transport = Transport(64, handler: ScriptedHandler.Serving(content));
        var error = await Assert.ThrowsAsync<HttpRequestException>(
            () => Guarded(transport.DownloadAsync(ModuleUrl, CancellationToken.None).AsTask()));
        Assert.Equal(HttpRequestError.ConfigurationLimitExceeded, error.HttpRequestError);
        Assert.Equal(64, content.BytesWritten);
        Assert.Equal(72, content.BytesAttempted);
        Assert.True(content.Disposed);
    }

    [Theory]
    [InlineData(false, 64)]
    [InlineData(false, 65)]
    [InlineData(true, 64)]
    [InlineData(true, 65)]
    public async Task Download_RealUnknownLengthFraming_HonorsTheExactContentBoundary(bool chunked, int length)
    {
        var bytes = Encoding.ASCII.GetBytes(new string('x', length));
        await using var server = new LoopbackHttpServer(async connection =>
        {
            await connection.WriteAsync(LoopbackHttpServer.OkHead(chunked ? ["Transfer-Encoding: chunked"] : []));
            // Tiny chunks have more framing bytes than content: those must not count.
            foreach (var value in bytes)
                if (!await connection.TryWriteAsync(chunked ? LoopbackHttpServer.Chunk([value]) : new byte[] { value }))
                    return;
            if (chunked)
                await connection.TryWriteAsync(LoopbackHttpServer.LastChunk);
        });
        using var transport = Transport(64);
        var download = transport.DownloadAsync(server.Url("127.0.0.1"), CancellationToken.None).AsTask();
        if (length == 64)
            Assert.Equal(new string('x', length), await Guarded(download));
        else
            Assert.Equal(HttpRequestError.ConfigurationLimitExceeded,
                (await Assert.ThrowsAsync<HttpRequestException>(() => Guarded(download))).HttpRequestError);
    }

    [Fact]
    public async Task Download_EndlessChunkedBody_OverRealTransport_IsStoppedByTheRunningCeiling()
    {
        const int ceiling = 64 * 1024;
        var data = new byte[4096];
        Array.Fill(data, (byte)'x');
        var chunk = LoopbackHttpServer.Chunk(data);
        await using var server = new LoopbackHttpServer(async connection =>
        {
            await connection.WriteAsync(LoopbackHttpServer.OkHead("Transfer-Encoding: chunked"));
            // Stream chunks until the client goes away — capped and then properly ended, so a
            // transport that kept reading could not make the fixture unbounded.
            for (long sent = 0; sent < 4 * 1024 * 1024 && await connection.TryWriteAsync(chunk); sent += data.Length)
            {
            }

            await connection.TryWriteAsync(LoopbackHttpServer.LastChunk);
            await connection.WaitForClientToDisconnectAsync();
        });
        using var transport = Transport(ceiling);

        var exception = await Assert.ThrowsAsync<HttpRequestException>(
            () => Guarded(transport.DownloadAsync(server.Url("127.0.0.1"), CancellationToken.None).AsTask()));

        Assert.Equal(HttpRequestError.ConfigurationLimitExceeded, exception.HttpRequestError);
        Assert.Contains($"{ceiling}-byte limit", exception.Message);
        await Guarded(server.ClientDisconnected);
    }

    [Fact]
    public async Task AllowLoading_OversizedModule_IsAFailedFetch_BeforeKatLangSeesAnyText()
    {
        // The ceiling acts inside the transport: KatLang receives no string to measure, and
        // the CLI reports the refusal as the ordinary load diagnostic with the failure exit code.
        var content = ScriptedContent.Endless(writeSize: 16);
        using var transport = Transport(64, handler: ScriptedHandler.Serving(content));

        var result = await Guarded(Cli.InvokeWithDownloaderAsync(transport.DownloadAsync, "eval", LoadingSource, "--allow-loading"));

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Contains($"load: failed to fetch '{ModuleUrl}'", result.TrimmedError);
        Assert.Contains("64-byte limit", result.TrimmedError);
        Assert.Equal(64, content.BytesWritten);
    }

    // ── Deadlines ───────────────────────────────────────────────────────────

    [Fact]
    public async Task Download_StalledBody_OverRealTransport_EndsByTheTransportsOwnDeadline()
    {
        await using var server = new LoopbackHttpServer(async connection =>
        {
            await connection.WriteAsync(LoopbackHttpServer.OkHead("Content-Length: 100"));
            await connection.WaitForClientToDisconnectAsync(); // the body never comes
        });
        using var transport = Transport(64 * 1024, ShortDeadline);
        var clock = Stopwatch.StartNew();

        var exception = await Assert.ThrowsAsync<TimeoutException>(
            () => Guarded(transport.DownloadAsync(server.Url("127.0.0.1"), CancellationToken.None).AsTask()));

        Assert.Contains("did not complete within 1.5 seconds", exception.Message);
        Assert.True(clock.Elapsed < Watchdog);
        // The deadline stopped the actual transfer: the server saw its client leave.
        await Guarded(server.ClientDisconnected);
    }

    [Fact]
    public async Task Download_TricklingBody_OverRealTransport_DoesNotRestartTheDeadline()
    {
        // One byte every 20 ms, forever: each read completes well inside the deadline, so a
        // per-read timeout would never fire. Only an absolute deadline ends this.
        var chunk = LoopbackHttpServer.Chunk("x"u8);
        var trickled = 0;
        await using var server = new LoopbackHttpServer(async connection =>
        {
            await connection.WriteAsync(LoopbackHttpServer.OkHead("Transfer-Encoding: chunked"));
            do
            {
                await Task.Delay(20, connection.Shutdown);
            }
            while (await connection.TryWriteAsync(chunk) && Interlocked.Increment(ref trickled) > 0);
        });
        using var transport = Transport(64 * 1024, ShortDeadline);

        await Assert.ThrowsAsync<TimeoutException>(
            () => Guarded(transport.DownloadAsync(server.Url("127.0.0.1"), CancellationToken.None).AsTask()));

        await Guarded(server.ClientDisconnected);
        Assert.True(Volatile.Read(ref trickled) >= 1, "the fixture never got to trickle a byte");
    }

    [Fact]
    public async Task Download_StalledHeaders_OverRealTransport_EndsByTheTransportsOwnDeadline()
    {
        // Accepts the connection and never answers.
        await using var server = new LoopbackHttpServer(connection => connection.WaitForClientToDisconnectAsync());
        using var transport = Transport(64 * 1024, ShortDeadline);

        await Assert.ThrowsAsync<TimeoutException>(
            () => Guarded(transport.DownloadAsync(server.Url("127.0.0.1"), CancellationToken.None).AsTask()));

        await Guarded(server.ClientDisconnected);
        Assert.Equal(1, server.RequestCount);
    }

    [Fact]
    public async Task Download_StalledRequest_IsAlsoBoundedByTheDeadline()
    {
        // The handler never produces a response; the deadline, linked into the request, ends it.
        var requestStarted = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var handler = ScriptedHandler.NeverResponding(requestStarted);
        using var transport = Transport(64, ShortDeadline, handler);

        await Assert.ThrowsAsync<TimeoutException>(
            () => Guarded(transport.DownloadAsync(ModuleUrl, CancellationToken.None).AsTask()));

        Assert.True(requestStarted.Task.IsCompletedSuccessfully);
        Assert.True(handler.ObservedCancellation);
    }

    [Fact]
    public async Task Download_StalledBody_WithAScriptedHandler_TimesOutAndDisposesTheResponse()
    {
        var content = ScriptedContent.Stalled();
        using var transport = Transport(64, ShortDeadline, ScriptedHandler.Serving(content));

        await Assert.ThrowsAsync<TimeoutException>(
            () => Guarded(transport.DownloadAsync(ModuleUrl, CancellationToken.None).AsTask()));

        Assert.True(content.BodyStarted.Task.IsCompletedSuccessfully);
        Assert.True(content.ObservedCancellation); // the deadline reached the body read itself
        Assert.True(content.Disposed);
    }

    // ── Caller cancellation and cleanup ─────────────────────────────────────

    [Fact]
    public async Task Download_CancelledBeforeTheRequest_ThrowsTheCallersToken_AndSendsNothing()
    {
        var handler = ScriptedHandler.Serving(ScriptedContent.Bytes(Encoding.ASCII.GetBytes("V = 1")));
        using var transport = Transport(64, handler: handler);
        using var cancellation = new CancellationTokenSource();
        await cancellation.CancelAsync();

        var exception = await Assert.ThrowsAsync<OperationCanceledException>(
            () => Guarded(transport.DownloadAsync(ModuleUrl, cancellation.Token).AsTask()));

        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.Equal(0, handler.Requests);
    }

    [Fact]
    public async Task Download_CancelledDuringTheBody_ThrowsTheCallersToken_AndStopsTheTransfer()
    {
        var content = ScriptedContent.Stalled();
        using var transport = Transport(64, handler: ScriptedHandler.Serving(content));
        using var cancellation = new CancellationTokenSource();

        var download = transport.DownloadAsync(ModuleUrl, cancellation.Token).AsTask();
        await Guarded(content.BodyStarted.Task);
        await cancellation.CancelAsync();

        var exception = await Assert.ThrowsAsync<OperationCanceledException>(() => Guarded(download));

        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.True(content.ObservedCancellation);
        Assert.True(content.Disposed);
    }

    [Fact]
    public async Task Download_CancelledAfterTheHeaders_OverRealTransport_ClosesTheConnection()
    {
        var headersSent = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        await using var server = new LoopbackHttpServer(async connection =>
        {
            await connection.WriteAsync(LoopbackHttpServer.OkHead("Content-Length: 100"));
            headersSent.SetResult();
            await connection.WaitForClientToDisconnectAsync();
        });
        using var transport = Transport(64 * 1024);
        using var cancellation = new CancellationTokenSource();

        var download = transport.DownloadAsync(server.Url("127.0.0.1"), cancellation.Token).AsTask();
        await Guarded(headersSent.Task);
        await cancellation.CancelAsync();

        var exception = await Assert.ThrowsAsync<OperationCanceledException>(() => Guarded(download));

        Assert.Equal(cancellation.Token, exception.CancellationToken);
        await Guarded(server.ClientDisconnected);
    }

    [Fact]
    public async Task Download_AfterARefusalAndATimeout_TheNextDownloadStillSucceeds()
    {
        // One instance, one client, three servers: a size refusal and a deadline expiry leave
        // nothing behind that a following ordinary download could trip over.
        using var transport = Transport(64, ShortDeadline);

        await using (var oversized = new LoopbackHttpServer(() => LoopbackHttpServer.Ok(new string('x', 65))))
        {
            await Assert.ThrowsAsync<HttpRequestException>(
                () => Guarded(transport.DownloadAsync(oversized.Url("127.0.0.1"), CancellationToken.None).AsTask()));
        }

        await using (var stalled = new LoopbackHttpServer(async connection =>
        {
            await connection.WriteAsync(LoopbackHttpServer.OkHead("Content-Length: 5"));
            await connection.WaitForClientToDisconnectAsync();
        }))
        {
            await Assert.ThrowsAsync<TimeoutException>(
                () => Guarded(transport.DownloadAsync(stalled.Url("127.0.0.1"), CancellationToken.None).AsTask()));
        }

        await using var healthy = new LoopbackHttpServer(() => LoopbackHttpServer.Ok("public Value = 42"));
        Assert.Equal(
            "public Value = 42",
            await Guarded(transport.DownloadAsync(healthy.Url("127.0.0.1"), CancellationToken.None).AsTask()));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task Download_CallerCancellationWins_WhenBothTokensHaveExpired(bool throughLoader)
    {
        var deadlineObserved = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var releaseFailure = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var content = ScriptedContent.Script(async (_, token) =>
        {
            try
            {
                await Task.Delay(Timeout.InfiniteTimeSpan, token);
            }
            catch (OperationCanceledException)
            {
                deadlineObserved.SetResult();
                await releaseFailure.Task;
                throw;
            }
        });
        using var transport = Transport(64, ShortDeadline, ScriptedHandler.Serving(content));
        using var caller = new CancellationTokenSource();
        Task operation = throughLoader
            ? KatLangEngine.RunAsync(LoadingSource, new RunOptions
            {
                DownloadCode = transport.DownloadAsync,
                SourceProcessingCancellationToken = caller.Token,
            })
            : transport.DownloadAsync(ModuleUrl, caller.Token).AsTask();
        try
        {
            // Wait for the actual downloader timer, then cancel the caller BEFORE allowing
            // the failure to reach either exception-classification boundary. No timing race.
            await Guarded(deadlineObserved.Task);
            await caller.CancelAsync();
            releaseFailure.SetResult();
            var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Guarded(operation));
            Assert.Equal(caller.Token, error.CancellationToken);
            Assert.True(content.Disposed);
        }
        finally
        {
            releaseFailure.TrySetResult();
            await caller.CancelAsync();
            await Record.ExceptionAsync(() => operation);
        }
    }

    [Fact]
    public async Task AllowLoading_CancellationAtBodyCompletion_RetainsTheCallerToken()
    {
        using var caller = new CancellationTokenSource();
        var content = ScriptedContent.Script(async (stream, token) =>
        {
            await stream.WriteAsync("public Val = 42"u8.ToArray(), token);
            await caller.CancelAsync(); // final write completed; buffered decoding may still succeed
        });
        using var transport = Transport(64, handler: ScriptedHandler.Serving(content));
        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Guarded(
            KatLangEngine.RunAsync(LoadingSource, new RunOptions
            {
                DownloadCode = transport.DownloadAsync,
                SourceProcessingCancellationToken = caller.Token,
            })));
        Assert.Equal(caller.Token, error.CancellationToken);
        Assert.Equal(1, content.SerializeCalls);
        Assert.True(content.Disposed);
    }

    [Fact]
    public async Task Download_CancellationDoesNotAffectAnOverlappingOrLaterRequest()
    {
        var secondStarted = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var releaseSecond = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var first = ScriptedContent.Stalled();
        var second = ScriptedContent.Script(async (stream, token) =>
        {
            secondStarted.SetResult();
            await releaseSecond.Task.WaitAsync(token);
            await stream.WriteAsync("public Val = 42"u8.ToArray(), token);
        });
        var third = ScriptedContent.Bytes("public Val = 43"u8.ToArray());
        var responses = new Queue<HttpContent>([first, second, third]);
        var handler = ScriptedHandler.Responding((_, _) => Task.FromResult(
            new HttpResponseMessage(HttpStatusCode.OK) { Content = responses.Dequeue() }));
        using var transport = Transport(64, handler: handler);
        using var caller = new CancellationTokenSource();
        var failed = transport.DownloadAsync(ModuleUrl, caller.Token).AsTask();
        var healthy = transport.DownloadAsync(ModuleUrl, CancellationToken.None).AsTask();
        try
        {
            await Guarded(first.BodyStarted.Task);
            await Guarded(secondStarted.Task);
            await caller.CancelAsync();
            var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Guarded(failed));
            Assert.Equal(caller.Token, error.CancellationToken);
            Assert.True(first.Disposed);
            Assert.False(healthy.IsCompleted);
            releaseSecond.SetResult();
            Assert.Equal("public Val = 42", await Guarded(healthy));
            Assert.Equal("public Val = 43", await Guarded(transport.DownloadAsync(ModuleUrl, CancellationToken.None).AsTask()));
            Assert.True(second.Disposed);
            Assert.True(third.Disposed);
        }
        finally
        {
            releaseSecond.TrySetResult();
            await caller.CancelAsync();
            await Record.ExceptionAsync(() => Task.WhenAll(failed, healthy));
        }
    }

    // ── Through the CLI: classification, layering, existing safeguards ──────

    [Fact]
    public async Task AllowLoading_TransportDeadline_IsAFailedFetch_NotACancellation()
    {
        var content = ScriptedContent.Stalled();
        using var transport = Transport(64, ShortDeadline, ScriptedHandler.Serving(content));

        var result = await Guarded(Cli.InvokeWithDownloaderAsync(transport.DownloadAsync, "eval", LoadingSource, "--allow-loading"));

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal("", result.Output);
        Assert.Contains($"load: failed to fetch '{ModuleUrl}'", result.TrimmedError);
        Assert.Contains("did not complete within 1.5 seconds", result.TrimmedError);
        Assert.DoesNotContain("cancelled", result.TrimmedError);
    }

    [Fact]
    public async Task AllowLoading_HostCancellationDuringADownload_IsReportedAsCancelled()
    {
        var content = ScriptedContent.Stalled();
        using var transport = Transport(64, handler: ScriptedHandler.Serving(content));
        using var cancellation = new CancellationTokenSource();
        var output = new StringWriter();
        var error = new StringWriter();

        var run = CliApplication.RunAsync(
            ["eval", LoadingSource, "--allow-loading"], output, error, transport.DownloadAsync, cancellation.Token);
        await Guarded(content.BodyStarted.Task);
        await cancellation.CancelAsync();
        var exitCode = await Guarded(run);

        Assert.Equal(Failure, exitCode);
        Assert.Equal("", output.ToString());
        Assert.Equal("katlang: cancelled.", error.ToString().Trim());
        Assert.True(content.ObservedCancellation);
    }

    [Fact]
    public async Task AllowLoading_KatLangStillEnforcesItsDecodedSourceLengthLimit_OnTextTheTransportAccepted()
    {
        // Layering control with an explicitly larger TEST-ONLY transport allowance:
        // the shipped 1 MiB policy would refuse this body first. Let it through here to
        // verify that the library's independent decoded-length check remains in force.
        var body = new byte[SourceProcessingLimits.MaxSupportedSourceLength + 1];
        Array.Fill(body, (byte)'x');
        var content = ScriptedContent.Bytes(body, declaredLength: body.Length, writeSize: 64 * 1024);
        using var transport = Transport(
            body.Length,
            HttpSourceDownloader.DownloadTimeout,
            ScriptedHandler.Serving(content));

        var result = await Guarded(Cli.InvokeWithDownloaderAsync(transport.DownloadAsync, "eval", LoadingSource, "--allow-loading"));

        Assert.Equal(Failure, result.ExitCode);
        Assert.Equal(body.Length, content.BytesWritten);
        Assert.DoesNotContain("failed to fetch", result.TrimmedError);
        Assert.Contains($"over the maximum of {SourceProcessingLimits.MaxSupportedSourceLength} UTF-16 code units", result.TrimmedError);
    }

    [Fact]
    public async Task Download_RefusesRedirects_OnAnInstanceBuiltThroughTheTestSeam()
    {
        // Omitting the handler uses the same redirect-disabled handler factory as Shared.
        await using var destination = new LoopbackHttpServer(() => LoopbackHttpServer.Ok("public Value = 42"));
        await using var origin = new LoopbackHttpServer(() => LoopbackHttpServer.Redirect(destination.Url("localhost")));
        using var transport = Transport(64 * 1024, ShortDeadline);

        var exception = await Assert.ThrowsAsync<HttpRequestException>(
            () => Guarded(transport.DownloadAsync(origin.Url("127.0.0.1"), CancellationToken.None).AsTask()));

        Assert.Contains("redirects are not allowed", exception.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(1, origin.RequestCount);
        Assert.Equal(0, destination.RequestCount);
    }

    [Theory]
    [InlineData(HttpStatusCode.Found)]
    [InlineData(HttpStatusCode.NotFound)]
    [InlineData(HttpStatusCode.InternalServerError)]
    public async Task Download_UnsuccessfulStatus_DoesNotConsumeTheBody(HttpStatusCode status)
    {
        var content = ScriptedContent.Endless(8, declaredLength: long.MaxValue);
        using var transport = Transport(64, handler: ScriptedHandler.Serving(content, status));
        var error = await Assert.ThrowsAsync<HttpRequestException>(
            () => Guarded(transport.DownloadAsync(ModuleUrl, CancellationToken.None).AsTask()));
        Assert.Equal(status, error.StatusCode);
        Assert.NotEqual(HttpRequestError.ConfigurationLimitExceeded, error.HttpRequestError);
        Assert.Equal(0, content.SerializeCalls);
        Assert.True(content.Disposed);
    }

    [Fact]
    public async Task AllowLoading_NetworkFailure_IsAFailedFetch_AndDisposesTheOwnedHandler()
    {
        var handler = ScriptedHandler.Responding((_, _) => throw new HttpRequestException(
            HttpRequestError.ConnectionError, "scripted connection failure"));
        using (var transport = Transport(64, handler: handler))
        {
            var error = await Assert.ThrowsAsync<HttpRequestException>(
                () => Guarded(transport.DownloadAsync(ModuleUrl, CancellationToken.None).AsTask()));
            Assert.Equal(HttpRequestError.ConnectionError, error.HttpRequestError);
            var result = await Guarded(Cli.InvokeWithDownloaderAsync(transport.DownloadAsync, "eval", LoadingSource, "--allow-loading"));
            Assert.Equal(Failure, result.ExitCode);
            Assert.Equal("", result.Output);
            Assert.Contains("load: failed to fetch", result.TrimmedError);
            Assert.Contains("scripted connection failure", result.TrimmedError);
        }
        Assert.True(handler.Disposed);
    }

    // ── Support ─────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("io")]
    [InlineData("socket")]
    [InlineData("disposed")]
    [InlineData("cancellation")]
    [InlineData("assertion")]
    public async Task LoopbackFixture_PropagatesResponseScriptFailures(string kind)
    {
        Exception expected = kind switch
        {
            "io" => new IOException("response script failed"),
            "socket" => new System.Net.Sockets.SocketException((int)System.Net.Sockets.SocketError.AccessDenied),
            "disposed" => new ObjectDisposedException("response script"),
            "cancellation" => new OperationCanceledException("unrelated script cancellation"),
            _ => new Xunit.Sdk.XunitException("response script assertion failed"),
        };
        var server = new LoopbackHttpServer(async connection =>
        {
            // A partial response prevents HTTP's retry of a connection closed before headers.
            await connection.WriteAsync(LoopbackHttpServer.OkHead("Content-Length: 1"));
            throw expected;
        });
        using var transport = Transport(64);
        try
        {
            await Assert.ThrowsAnyAsync<HttpRequestException>(
                () => Guarded(transport.DownloadAsync(server.Url("127.0.0.1"), CancellationToken.None).AsTask()));
        }
        finally
        {
            var failure = await Record.ExceptionAsync(() => server.DisposeAsync().AsTask());
            Assert.Same(expected, failure);
        }
    }

    private static HttpSourceDownloader Transport(
        long maxResponseBodyBytes,
        TimeSpan? deadline = null,
        HttpMessageHandler? handler = null)
        => new(maxResponseBodyBytes, deadline ?? LongDeadline, handler);

    /// <summary>
    /// Awaits the operation under the watchdog WITHOUT cancelling it: a production bound that
    /// fails to fire shows up as this assertion, never as a watchdog-induced stop.
    /// </summary>
    private static async Task<T> Guarded<T>(Task<T> operation)
    {
        await Guarded((Task)operation);
        return await operation;
    }

    private static async Task Guarded(Task operation)
    {
        var finished = await Task.WhenAny(operation, Task.Delay(Watchdog));
        Assert.True(
            finished == operation,
            $"The operation did not finish within the {Watchdog.TotalSeconds}s test watchdog; the transport's own bound did not stop it.");
        await operation;
    }

    private static string Show(string text)
    {
        var shown = new StringBuilder();
        foreach (var ch in text)
            shown.Append(ch is >= ' ' and <= '~' ? ch.ToString() : $"\\u{(int)ch:X4}");
        return shown.ToString();
    }

    /// <summary>A handler whose response is scripted, with the request count observable.</summary>
    private sealed class ScriptedHandler : HttpMessageHandler
    {
        private Func<HttpRequestMessage, CancellationToken, Task<HttpResponseMessage>> _respond = null!;
        private int _requests;

        public int Requests => Volatile.Read(ref _requests);

        /// <summary>Set when a never-completing request observed its token's cancellation.</summary>
        public bool ObservedCancellation { get; private set; }

        public bool Disposed { get; private set; }

        public static ScriptedHandler Serving(HttpContent content, HttpStatusCode status = HttpStatusCode.OK)
            => new()
            {
                _respond = (_, _) => Task.FromResult(new HttpResponseMessage(status) { Content = content }),
            };

        public static ScriptedHandler Responding(Func<HttpRequestMessage, CancellationToken, Task<HttpResponseMessage>> respond)
            => new() { _respond = respond };

        /// <summary>Accepts the request and never answers it; completes <paramref name="requestStarted"/> first.</summary>
        public static ScriptedHandler NeverResponding(TaskCompletionSource requestStarted)
        {
            var handler = new ScriptedHandler();
            handler._respond = async (_, cancellationToken) =>
            {
                requestStarted.TrySetResult();
                try
                {
                    await Task.Delay(Timeout.InfiniteTimeSpan, cancellationToken);
                }
                catch (OperationCanceledException)
                {
                    handler.ObservedCancellation = true;
                    throw;
                }

                throw new UnreachableException();
            };
            return handler;
        }

        protected override Task<HttpResponseMessage> SendAsync(HttpRequestMessage request, CancellationToken cancellationToken)
        {
            Interlocked.Increment(ref _requests);
            return _respond(request, cancellationToken);
        }

        protected override void Dispose(bool disposing)
        {
            Disposed = true;
            base.Dispose(disposing);
        }
    }

    /// <summary>
    /// A response body served by a script, with what the transport consumed and whether it
    /// disposed the content observable.
    /// </summary>
    private sealed class ScriptedContent : HttpContent
    {
        // A transport that ignored the ceiling still ends, so a pre-fix run fails an
        // assertion instead of exhausting memory.
        private const long EndlessCap = 16L * 1024 * 1024;

        private readonly Func<ScriptedContent, Stream, CancellationToken, Task> _serve;
        private long _bytesWritten;
        private long _bytesAttempted;

        private ScriptedContent(
            Func<ScriptedContent, Stream, CancellationToken, Task> serve,
            long? declaredLength,
            string? mediaType,
            string? charset)
        {
            _serve = serve;
            if (mediaType is not null)
                Headers.ContentType = new MediaTypeHeaderValue(mediaType) { CharSet = charset };
            if (declaredLength is { } length)
                Headers.ContentLength = length;
        }

        public int SerializeCalls { get; private set; }

        /// <summary>Bytes the transport accepted into its buffer.</summary>
        public long BytesWritten => Volatile.Read(ref _bytesWritten);

        /// <summary>Bytes the script offered, including a write the transport refused.</summary>
        public long BytesAttempted => Volatile.Read(ref _bytesAttempted);

        public bool Disposed { get; private set; }

        public bool ObservedCancellation { get; private set; }

        /// <summary>Completes when the transport first asks a stalled body for bytes.</summary>
        public TaskCompletionSource BodyStarted { get; } = new(TaskCreationOptions.RunContinuationsAsynchronously);

        public static ScriptedContent Script(Func<Stream, CancellationToken, Task> serve)
            => new((_, stream, token) => serve(stream, token), null, "text/plain", "utf-8");

        /// <summary>A fixed body, written in <paramref name="writeSize"/>-byte pieces so multi-byte sequences straddle writes.</summary>
        public static ScriptedContent Bytes(
            byte[] body,
            long? declaredLength = null,
            string? mediaType = "text/plain",
            string? charset = "utf-8",
            int writeSize = 7)
            => new(
                async (self, stream, cancellationToken) =>
                {
                    for (var offset = 0; offset < body.Length; offset += writeSize)
                    {
                        var count = Math.Min(writeSize, body.Length - offset);
                        await self.WriteAsync(stream, body.AsMemory(offset, count), cancellationToken);
                    }
                },
                declaredLength,
                mediaType,
                charset);

        /// <summary>A body of 'x' bytes in <paramref name="writeSize"/>-byte writes that only the reader can stop.</summary>
        public static ScriptedContent Endless(int writeSize, long? declaredLength = null)
            => new(
                async (self, stream, cancellationToken) =>
                {
                    var piece = new byte[writeSize];
                    Array.Fill(piece, (byte)'x');
                    for (long sent = 0; sent < EndlessCap; sent += writeSize)
                        await self.WriteAsync(stream, piece, cancellationToken);
                },
                declaredLength,
                "text/plain",
                "utf-8");

        /// <summary>Headers only: the body never arrives. Records whether the reader's token cancelled the wait.</summary>
        public static ScriptedContent Stalled(long? declaredLength = null)
            => new(
                async (self, _, cancellationToken) =>
                {
                    self.BodyStarted.TrySetResult();
                    try
                    {
                        await Task.Delay(Timeout.InfiniteTimeSpan, cancellationToken);
                    }
                    catch (OperationCanceledException)
                    {
                        self.ObservedCancellation = true;
                        throw;
                    }
                },
                declaredLength,
                "text/plain",
                "utf-8");

        private async Task WriteAsync(Stream stream, ReadOnlyMemory<byte> bytes, CancellationToken cancellationToken)
        {
            Interlocked.Add(ref _bytesAttempted, bytes.Length);
            await stream.WriteAsync(bytes, cancellationToken);
            Interlocked.Add(ref _bytesWritten, bytes.Length);
        }

        protected override Task SerializeToStreamAsync(Stream stream, TransportContext? context, CancellationToken cancellationToken)
        {
            SerializeCalls++;
            return _serve(this, stream, cancellationToken);
        }

        protected override Task SerializeToStreamAsync(Stream stream, TransportContext? context)
            => SerializeToStreamAsync(stream, context, CancellationToken.None);

        protected override bool TryComputeLength(out long length)
        {
            length = 0;
            return false;
        }

        protected override void Dispose(bool disposing)
        {
            Disposed = true;
            base.Dispose(disposing);
        }
    }
}
