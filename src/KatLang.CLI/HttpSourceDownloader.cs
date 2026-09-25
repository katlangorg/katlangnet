using System.Globalization;
using System.Net;

namespace KatLang.CLI;

/// <summary>
/// Transport for <see cref="RunOptions.DownloadCode"/> when <c>--allow-loading</c>
/// is supplied. KatLang validates every requested URL (HTTPS only, no user
/// information, an allowed host — the CLI configures no allow-list, so KatLang's
/// default applies: <c>katlang.org</c> and its subdomains) before calling this
/// transport, and hands it the canonical URL; everything after that is the shipped
/// CLI's own host policy — owned here, and imposed on no other KatLang host:
///
/// <list type="bullet">
///   <item>Redirects are refused so the HTTP layer cannot silently fetch a
///   second URL whose host KatLang never validated.</item>
///   <item>Only <c>200 OK</c> is a module. Every other status — a redirect, an error,
///   and every other 2xx such as <c>204 No Content</c> or <c>206 Partial Content</c> —
///   is a failed download, reported with the CLI's own wording (never the server's
///   reason phrase) and without reading the body.</item>
///   <item>No ambient state travels with a request: cookies are disabled (a response
///   cannot plant state that a later module request would carry), no credentials are
///   configured, and no decompression is negotiated. The system proxy settings apply
///   as for any other HTTPS client; TLS certificate validation is the platform's
///   default. Host names are resolved by the platform: the CLI makes no claim about
///   the IP addresses an allowed name resolves to.</item>
///   <item>A response body is buffered only up to <see cref="MaxResponseBodyBytes"/>
///   — content bytes exposed by HttpContent, excluding headers and chunk framing;
///   no decompression is negotiated or performed. A larger declared Content-Length
///   is refused before body buffering, and a chunked or unknown-length body is
///   refused when a buffer write would exceed the same ceiling. Buffered memory is bounded by a small
///   multiple of the ceiling (the runtime buffer's growth policy) rather than by
///   the peer. KatLang's decoded source-length
///   ceiling (<see cref="SourceProcessingLimits.MaxSupportedSourceLength"/> UTF-16
///   code units per module) is a different limit and still applies to the
///   returned text afterwards, unchanged.</item>
///   <item>One absolute per-download deadline, <see cref="DownloadTimeout"/>,
///   covers the request, the headers, and the complete body. It is never
///   restarted by incoming bytes, so a peer that stalls or trickles after its
///   headers is cancelled. Cancellation is cooperative; in particular, the bounded
///   synchronous decoding step is not preemptible. <see cref="HttpClient.Timeout"/> alone
///   cannot do this — under headers-first completion it ends with the headers —
///   so the client's own timeout is disabled and the CLI's 15-second deadline
///   applies end to end.</item>
/// </list>
///
/// A size refusal or an expired deadline surfaces to KatLang as an ordinary
/// failed fetch (<c>load: failed to fetch …</c>); only the caller's own
/// cancellation surfaces as <see cref="OperationCanceledException"/>, carrying
/// the caller's token. Every download disposes its response and releases its body
/// stream; connection closure, bounded draining, or reuse is managed by HttpClient.
/// </summary>
internal sealed class HttpSourceDownloader : IDisposable
{
    /// <summary>
    /// Fixed CLI host policy: at most 1 MiB (1,048,576 content bytes) per downloaded module,
    /// independent of KatLang's decoded source-length limit. This intentionally stricter
    /// transport policy can refuse valid source that would fit the library's limit.
    /// Non-ASCII and non-UTF-8 sources consume the content bytes their encoding requires,
    /// including any BOM; HTTP headers and chunk framing do not count.
    /// </summary>
    public const long MaxResponseBodyBytes = 1_048_576L;

    /// <summary>
    /// Fixed CLI host policy: one absolute 15-second deadline per downloaded module,
    /// starting before the request and remaining active through body acquisition.
    /// </summary>
    public static readonly TimeSpan DownloadTimeout = TimeSpan.FromSeconds(15);

    /// <summary>
    /// The production transport: one instance — one client — for the process lifetime, the
    /// documented HttpClient usage pattern. A short-lived CLI process reclaims it on exit.
    /// </summary>
    public static HttpSourceDownloader Shared { get; } = new(MaxResponseBodyBytes, DownloadTimeout);

    private readonly HttpClient _client;

    /// <param name="handler">
    /// Test seam only: a substitute message handler, which controls its own transport behavior.
    /// Production and loopback tests omit it and use <see cref="CreateHandler"/>.
    /// </param>
    internal HttpSourceDownloader(
        long maxResponseBodyBytes,
        TimeSpan downloadTimeout,
        HttpMessageHandler? handler = null)
    {
        // HttpContent's supported buffering ceiling is int.MaxValue.
        ArgumentOutOfRangeException.ThrowIfNegative(maxResponseBodyBytes);
        ArgumentOutOfRangeException.ThrowIfGreaterThan(maxResponseBodyBytes, (long)int.MaxValue);
        // Finite and positive: Timeout.InfiniteTimeSpan is negative and rejected too.
        ArgumentOutOfRangeException.ThrowIfLessThanOrEqual(downloadTimeout, TimeSpan.Zero);

        ConfiguredMaxResponseBodyBytes = maxResponseBodyBytes;
        ConfiguredDownloadTimeout = downloadTimeout;
        _client = new HttpClient(handler ?? CreateHandler())
        {
            // The per-download deadline in DownloadAsync is the ONE timeout. The client's
            // own would cover only the header phase here, and would race the linked token
            // with a differently classified exception.
            Timeout = Timeout.InfiniteTimeSpan,
        };
    }

    /// <summary>The body ceiling this instance enforces, in bytes.</summary>
    internal long ConfiguredMaxResponseBodyBytes { get; }

    /// <summary>The whole-download deadline this instance enforces.</summary>
    internal TimeSpan ConfiguredDownloadTimeout { get; }

    /// <summary>
    /// Redirects are never followed, so the HTTP layer cannot silently fetch a second URL
    /// whose host KatLang never validated. Cookies are disabled: the handler's default
    /// cookie container would otherwise keep what one response sets and send it with every
    /// later request of this process-wide client, so a module server could plant state that
    /// reaches another module request. No decompression and no credentials; default
    /// certificate validation.
    /// </summary>
    private static SocketsHttpHandler CreateHandler() => new()
    {
        AllowAutoRedirect = false,
        UseCookies = false,
        AutomaticDecompression = DecompressionMethods.None,
    };

    public async ValueTask<string> DownloadAsync(string url, CancellationToken cancellationToken)
    {
        cancellationToken.ThrowIfCancellationRequested();

        // One absolute deadline for the whole download, linked to the caller's token and
        // never restarted: a trickling peer runs out of time exactly like a silent one.
        using var deadline = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
        deadline.CancelAfter(ConfiguredDownloadTimeout);

        try
        {
            using var response = await _client.GetAsync(
                url,
                HttpCompletionOption.ResponseHeadersRead,
                deadline.Token).ConfigureAwait(false);

            if ((int)response.StatusCode is >= 300 and <= 399)
            {
                throw new HttpRequestException(
                    "HTTP redirects are not allowed while loading KatLang algorithms.",
                    inner: null,
                    response.StatusCode);
            }

            // Only 200 OK carries a module. The refusal is worded here, never with the
            // server's reason phrase, and the body is not read.
            if (response.StatusCode != HttpStatusCode.OK)
            {
                throw new HttpRequestException(
                    $"The server responded with HTTP status {(int)response.StatusCode}; only 200 (OK) is accepted for a KatLang module.",
                    inner: null,
                    response.StatusCode);
            }

            // Refuse an excessive declared length before requesting body buffering or
            // allowing the runtime to size a content buffer from that length.
            if (response.Content.Headers.ContentLength is { } declaredLength
                && declaredLength > ConfiguredMaxResponseBodyBytes)
            {
                throw new HttpRequestException(
                    HttpRequestError.ConfigurationLimitExceeded,
                    $"The declared Content-Length of {declaredLength} bytes exceeds the " +
                    $"{ConfiguredMaxResponseBodyBytes}-byte limit for a loaded module.");
            }

            // Bounded buffering. The runtime re-checks the declared length, sizes its buffer
            // from it only once validated, and refuses the first write that would cross
            // the ceiling. Network/copy read-ahead and HttpClient's bounded disposal drain
            // are separate from these accepted content bytes. Real HTTP Content-Length
            // framing ends the exposed body at that length; only synthetic content can
            // write more than its declared length into this buffer.
            try
            {
                await response.Content.LoadIntoBufferAsync(
                    ConfiguredMaxResponseBodyBytes,
                    deadline.Token).ConfigureAwait(false);
            }
            catch (HttpRequestException ex) when (ex.HttpRequestError == HttpRequestError.ConfigurationLimitExceeded)
            {
                throw new HttpRequestException(
                    HttpRequestError.ConfigurationLimitExceeded,
                    $"The response body exceeds the {ConfiguredMaxResponseBodyBytes}-byte limit for a loaded module.",
                    ex);
            }

            // Decoding the buffered bytes is unchanged from the unbounded read this replaces:
            // the Content-Type charset, else a byte-order mark, else UTF-8, with the same
            // failure for an unsupported charset. The decoded string is what KatLang then
            // measures against its own source-length ceiling. Already-buffered content is
            // reused without another read; this synchronous decode does not observe cancellation.
            return await response.Content.ReadAsStringAsync(deadline.Token).ConfigureAwait(false);
        }
        catch (OperationCanceledException ex) when (cancellationToken.IsCancellationRequested)
        {
            // Caller cancellation observed here takes precedence over deadline expiry.
            // Keep that contract, including the token's identity, which
            // the linked source would otherwise replace with its own.
            throw new OperationCanceledException(ex.Message, ex, cancellationToken);
        }
        catch (OperationCanceledException ex) when (deadline.IsCancellationRequested)
        {
            // The downloader's own deadline while the caller is still waiting: an ordinary
            // failed download, not a cancellation.
            var seconds = ConfiguredDownloadTimeout.TotalSeconds.ToString("0.###", CultureInfo.InvariantCulture);
            throw new TimeoutException($"The download did not complete within {seconds} seconds.", ex);
        }
    }

    public void Dispose() => _client.Dispose();
}
