using System.Diagnostics;
using System.Net;
using System.Net.Sockets;

namespace KatLang.CLI;

/// <summary>
/// Test-only relaxations of <see cref="HttpSourceDownloader"/>'s guardrails. Production uses
/// <see cref="Production"/>, which relaxes nothing; no command-line option, environment
/// variable or configuration reaches this type.
/// </summary>
/// <param name="AllowPlainHttp">Admit <c>http://</c> addresses as well as <c>https://</c>.</param>
/// <param name="IsAllowedAddress">The address rule; production's is <see cref="PublicAddress.IsPublic"/>.</param>
/// <param name="ResolveAsync">Host name to addresses; production's is the platform resolver.</param>
/// <remarks>
/// <see cref="OpenAsync"/> is the fourth substitution point: how the connection to one judged
/// address is opened. It relaxes no rule — it is called only for an address that passed
/// <see cref="IsAllowedAddress"/> — and production's is a plain TCP socket.
/// </remarks>
internal sealed record DownloadSeam(
    bool AllowPlainHttp,
    Func<IPAddress, bool> IsAllowedAddress,
    Func<string, CancellationToken, Task<IPAddress[]>> ResolveAsync)
{
    /// <summary>The shipped guardrails: HTTPS only, public addresses only, the platform resolver.</summary>
    public static DownloadSeam Production { get; } = new(
        AllowPlainHttp: false,
        PublicAddress.IsPublic,
        Dns.GetHostAddressesAsync);

    /// <summary>
    /// Lets a loopback HTTP server stand in for a public HTTPS host, so the real socket
    /// transport can be exercised offline: plain <c>http</c> is admitted, and a loopback
    /// address passes beside the public ones. Every other address is still refused.
    /// </summary>
    public static DownloadSeam LoopbackStandsInForPublic { get; } = new(
        AllowPlainHttp: true,
        static address => IPAddress.IsLoopback(address) || PublicAddress.IsPublic(address),
        Dns.GetHostAddressesAsync);

    /// <summary>
    /// Opens the TCP connection to one address that passed <see cref="IsAllowedAddress"/>.
    /// Production's is <see cref="OpenSocketAsync"/>; a test substitutes its own to make an
    /// address stall or to see which addresses were dialed, in what order.
    /// </summary>
    public Func<IPEndPoint, CancellationToken, ValueTask<Stream>> OpenAsync { get; init; } = OpenSocketAsync;

    /// <summary>A TCP connection to <paramref name="target"/>, on a socket of its own address family.</summary>
    public static async ValueTask<Stream> OpenSocketAsync(IPEndPoint target, CancellationToken cancellationToken)
    {
        var socket = new Socket(target.AddressFamily, SocketType.Stream, ProtocolType.Tcp) { NoDelay = true };
        try
        {
            await socket.ConnectAsync(target, cancellationToken).ConfigureAwait(false);
            return new NetworkStream(socket, ownsSocket: true);
        }
        catch
        {
            socket.Dispose();
            throw;
        }
    }
}

/// <summary>
/// The CLI's ONE downloader. It fetches the program a URL operand names
/// (<see cref="DownloadProgramAsync"/>) and, when <c>--allow-loading</c> is supplied, every
/// module (<see cref="DownloadAsync"/>, the transport for <see cref="RunOptions.DownloadCode"/>).
/// Either may name any host, so every download passes the same guardrails, owned here and
/// imposed on no other KatLang host. The CLI runs inside AI agents, where a link can be pasted
/// or injected by someone else; such a link must not reach the user's own machine or network.
///
/// <list type="bullet">
///   <item>HTTPS only. An <c>http://</c> address is refused, never upgraded: code is not
///   fetched unprotected in transit, and plain-HTTP internal services stay out of reach.</item>
///   <item>No user information in the address (<c>user@</c>, <c>user:password@</c>), and no
///   credentials of any other kind: none is configured, and cookies are disabled, so a
///   response cannot plant state that a later request would carry.</item>
///   <item>Public addresses only (<see cref="PublicAddress"/>). The host name is resolved
///   HERE, every address of the answer is judged, and the connection is opened to an address
///   that passed (<see cref="ConnectAsync"/>, the handler's connect callback) — so a name that
///   resolves to a loopback, private, carrier-grade NAT, link-local or other non-public
///   address is refused before any connection, and a later DNS answer cannot swap the address
///   between the check and the connection. An IP literal is judged the same way. Because the
///   address a proxy would connect to cannot be checked, the system proxy settings are NOT
///   used: every connection is direct.</item>
///   <item>Redirects are refused, so the HTTP layer cannot fetch a second address that was
///   never judged.</item>
///   <item>Only <c>200 OK</c> carries source. Every other status — a redirect, an error, and
///   every other 2xx such as <c>204 No Content</c> or <c>206 Partial Content</c> — is a failed
///   download, and its body is not read.</item>
///   <item>A PROGRAM's response must be served as source text: <c>text/plain</c> in any
///   character set, or <c>application/octet-stream</c>, which many servers send for an
///   unknown extension such as <c>.kat</c>. Anything else — <c>text/html</c>,
///   <c>application/json</c>, no <c>Content-Type</c> at all — is refused from the headers,
///   before the body is read and before anything runs. A module's media type is not judged.</item>
///   <item>A response body is buffered only up to <see cref="MaxResponseBodyBytes"/>
///   — content bytes exposed by HttpContent, excluding headers and chunk framing;
///   no decompression is negotiated or performed. A larger declared Content-Length
///   is refused before body buffering, and a chunked or unknown-length body is
///   refused when a buffer write would exceed the same ceiling. Buffered memory is bounded by a small
///   multiple of the ceiling (the runtime buffer's growth policy) rather than by
///   the peer. KatLang's decoded source-length
///   ceiling (<see cref="SourceProcessingLimits.MaxSupportedSourceLength"/> UTF-16
///   code units per source) is a different limit and still applies to the
///   returned text afterwards, unchanged.</item>
///   <item>One absolute per-download deadline, <see cref="DownloadTimeout"/>,
///   covers name resolution, the connection, the request, the headers, and the complete body.
///   It is never restarted by incoming bytes, so a peer that stalls or trickles after its
///   headers is cancelled. Cancellation is cooperative; in particular, the bounded
///   synchronous decoding step is not preemptible. <see cref="HttpClient.Timeout"/> alone
///   cannot do this — under headers-first completion it ends with the headers —
///   so the client's own timeout is disabled and the CLI's 15-second deadline
///   applies end to end.</item>
///   <item>Every request is HTTP/1.1 over a TCP connection this class opened, with the fixed
///   <c>User-Agent</c> <see cref="UserAgent"/>. TLS certificate validation is the platform's
///   default.</item>
/// </list>
///
/// The body is decoded as the response states: its <c>Content-Type</c> character set, else a
/// byte-order mark, else UTF-8, with one leading byte-order mark dropped, as for a file.
///
/// <para>Every refusal and failure is a <see cref="DownloadException"/>, worded once for both
/// kinds of download. For a module KatLang reports it as an ordinary failed fetch
/// (<c>load: failed to fetch …</c>); only the caller's own cancellation surfaces as
/// <see cref="OperationCanceledException"/>, carrying the caller's token. Every download
/// disposes its response and releases its body stream; connection closure, bounded draining,
/// or reuse is managed by HttpClient.</para>
/// </summary>
internal sealed class HttpSourceDownloader : IDisposable
{
    /// <summary>
    /// Fixed CLI host policy: at most 1 MiB (1,048,576 content bytes) per download,
    /// independent of KatLang's decoded source-length limit. This intentionally stricter
    /// transport policy can refuse valid source that would fit the library's limit.
    /// Non-ASCII and non-UTF-8 sources consume the content bytes their encoding requires,
    /// including any BOM; HTTP headers and chunk framing do not count.
    /// </summary>
    public const long MaxResponseBodyBytes = 1_048_576L;

    /// <summary>
    /// Fixed CLI host policy: one absolute 15-second deadline per download,
    /// starting before the request and remaining active through body acquisition.
    /// </summary>
    public static readonly TimeSpan DownloadTimeout = TimeSpan.FromSeconds(15);

    /// <summary>The fixed <c>User-Agent</c> of every request: <c>katlang-cli/&lt;version&gt;</c>.</summary>
    public static string UserAgent { get; } = "katlang-cli/" + HelpText.Version;

    /// <summary>
    /// The production transport: one instance — one client — for the process lifetime, the
    /// documented HttpClient usage pattern. A short-lived CLI process reclaims it on exit.
    /// </summary>
    public static HttpSourceDownloader Shared { get; } = new(MaxResponseBodyBytes, DownloadTimeout);

    private readonly HttpClient _client;
    private readonly DownloadSeam _seam;

    /// <param name="handler">
    /// Test seam only: a substitute message handler, which controls its own transport behavior
    /// (it opens no connection through this class, so only the address checks made before a
    /// request apply). Production and loopback tests omit it and use <see cref="CreateHandler"/>.
    /// </param>
    /// <param name="seam">Test seam only; production omits it (<see cref="DownloadSeam.Production"/>).</param>
    internal HttpSourceDownloader(
        long maxResponseBodyBytes,
        TimeSpan downloadTimeout,
        HttpMessageHandler? handler = null,
        DownloadSeam? seam = null)
    {
        // HttpContent's supported buffering ceiling is int.MaxValue.
        ArgumentOutOfRangeException.ThrowIfNegative(maxResponseBodyBytes);
        ArgumentOutOfRangeException.ThrowIfGreaterThan(maxResponseBodyBytes, (long)int.MaxValue);
        // Finite and positive: Timeout.InfiniteTimeSpan is negative and rejected too.
        ArgumentOutOfRangeException.ThrowIfLessThanOrEqual(downloadTimeout, TimeSpan.Zero);

        ConfiguredMaxResponseBodyBytes = maxResponseBodyBytes;
        ConfiguredDownloadTimeout = downloadTimeout;
        _seam = seam ?? DownloadSeam.Production;
        _client = new HttpClient(handler ?? CreateHandler())
        {
            // The per-download deadline in DownloadAsync is the ONE timeout. The client's
            // own would cover only the header phase here, and would race the linked token
            // with a differently classified exception.
            Timeout = Timeout.InfiniteTimeSpan,

            // HTTP/1.1 over TCP, never upgraded: an HTTP/3 connection would be opened by the
            // QUIC stack, outside the connect callback that enforces the address rule.
            DefaultRequestVersion = HttpVersion.Version11,
            DefaultVersionPolicy = HttpVersionPolicy.RequestVersionOrLower,
        };
        _client.DefaultRequestHeaders.TryAddWithoutValidation("User-Agent", UserAgent);
    }

    /// <summary>The body ceiling this instance enforces, in bytes.</summary>
    internal long ConfiguredMaxResponseBodyBytes { get; }

    /// <summary>The whole-download deadline this instance enforces.</summary>
    internal TimeSpan ConfiguredDownloadTimeout { get; }

    /// <summary>
    /// Redirects are never followed, so the HTTP layer cannot silently fetch a second address
    /// that was never judged. Cookies are disabled: the handler's default
    /// cookie container would otherwise keep what one response sets and send it with every
    /// later request of this process-wide client, so one server could plant state that
    /// reaches another request. No decompression and no credentials; default
    /// certificate validation. No proxy: a proxy resolves the host name itself, so the
    /// address it connects to could not be held to the public-address rule. Every connection
    /// is opened by <see cref="ConnectAsync"/>.
    /// </summary>
    private SocketsHttpHandler CreateHandler() => new()
    {
        AllowAutoRedirect = false,
        UseCookies = false,
        UseProxy = false,
        AutomaticDecompression = DecompressionMethods.None,
        ConnectCallback = ConnectAsync,

        // The handler opens a connection apart from the request that asked for it, so the
        // request's deadline alone would leave a stalled resolution or connection attempt
        // running behind a download that has already failed. This bound ends it; it is longer
        // than the deadline, though its timer can race the download's cancellation callback.
        ConnectTimeout = ConfiguredDownloadTimeout + ConfiguredDownloadTimeout,
    };

    /// <summary>A module, for <see cref="RunOptions.DownloadCode"/>: the text of <paramref name="url"/>.</summary>
    public ValueTask<string> DownloadAsync(string url, CancellationToken cancellationToken)
        => DownloadAsync(url, program: false, cancellationToken);

    /// <summary>
    /// The program a URL operand names: the text of <paramref name="url"/>, which must be
    /// served as KatLang source text (see the class remarks).
    /// </summary>
    public ValueTask<string> DownloadProgramAsync(string url, CancellationToken cancellationToken)
        => DownloadAsync(url, program: true, cancellationToken);

    private async ValueTask<string> DownloadAsync(string url, bool program, CancellationToken cancellationToken)
    {
        cancellationToken.ThrowIfCancellationRequested();

        // Judged before a request exists: the scheme, user information, and an IP-literal host.
        var address = Admit(url);

        // One absolute deadline for the whole download, linked to the caller's token and
        // never restarted: a trickling peer runs out of time exactly like a silent one.
        var started = Stopwatch.GetTimestamp();
        using var deadline = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
        deadline.CancelAfter(ConfiguredDownloadTimeout);

        try
        {
            using var response = await _client.GetAsync(
                address,
                HttpCompletionOption.ResponseHeadersRead,
                deadline.Token).ConfigureAwait(false);

            if ((int)response.StatusCode is >= 300 and <= 399)
                throw DownloadException.Redirect(response.StatusCode);

            // Only 200 OK carries source. The refusal is worded by the CLI, never with the
            // server's reason phrase, and the body is not read.
            if (response.StatusCode != HttpStatusCode.OK)
                throw DownloadException.UnexpectedStatus(response.StatusCode);

            // A program must be served as source text. Decided from the headers, so a page,
            // a document or a picture is refused whatever its size, and nothing of it is read.
            if (program)
                RequireSourceText(response.Content);

            // Refuse an excessive declared length before requesting body buffering or
            // allowing the runtime to size a content buffer from that length.
            if (response.Content.Headers.ContentLength is { } declaredLength
                && declaredLength > ConfiguredMaxResponseBodyBytes)
            {
                throw DownloadException.DeclaredLengthTooLarge(declaredLength, ConfiguredMaxResponseBodyBytes);
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
                throw DownloadException.BodyTooLarge(ConfiguredMaxResponseBodyBytes, ex);
            }

            // Decoding the buffered bytes: the Content-Type charset, else a byte-order mark,
            // else UTF-8, with one leading byte-order mark dropped. The decoded string is what
            // KatLang then measures against its own source-length ceiling. Already-buffered
            // content is reused without another read; this synchronous decode does not
            // observe cancellation.
            try
            {
                return await response.Content.ReadAsStringAsync(deadline.Token).ConfigureAwait(false);
            }
            catch (InvalidOperationException ex)
            {
                // The response names a character set this runtime has no decoder for.
                throw DownloadException.UnsupportedCharacterSet(ex);
            }
        }
        catch (Exception ex) when (cancellationToken.IsCancellationRequested
            && ex is OperationCanceledException or HttpRequestException or DownloadException)
        {
            // Caller cancellation observed here takes precedence over deadline expiry and
            // over whatever the cancelled transfer failed with. Keep that contract, including
            // the token's identity, which the linked source would otherwise replace with its own.
            throw new OperationCanceledException(ex.Message, ex, cancellationToken);
        }
        catch (OperationCanceledException ex) when (deadline.IsCancellationRequested)
        {
            // The downloader's own deadline while the caller is still waiting: an ordinary
            // failed download, not a cancellation.
            throw DownloadException.DeadlineExceeded(ConfiguredDownloadTimeout, ex);
        }
        catch (OperationCanceledException ex) when (ex.InnerException is TimeoutException)
        {
            throw ClassifyConnectTimeout(ConfiguredDownloadTimeout, Stopwatch.GetElapsedTime(started), ex);
        }
        catch (HttpRequestException ex)
        {
            // The handler wraps what the connect callback threw; the refusal itself is inside.
            // A transfer the deadline ended can also surface as a transport failure.
            throw FindDownloadException(ex)
                ?? (deadline.IsCancellationRequested
                    ? DownloadException.DeadlineExceeded(ConfiguredDownloadTimeout, ex)
                    : DownloadException.RequestFailed(ex));
        }
    }

    internal static DownloadException ClassifyConnectTimeout(TimeSpan deadline, TimeSpan elapsed, Exception error)
        => elapsed >= deadline
            ? DownloadException.DeadlineExceeded(deadline, error)
            : DownloadException.ConnectionFailed(error);

    /// <summary>
    /// The address checks that need no network: an absolute URL, HTTPS, no user information,
    /// a host that is a DNS name or an IP literal — and, for a literal, the address rule
    /// itself, so such an address is refused before a request is even built.
    /// </summary>
    private Uri Admit(string url)
    {
        if (!Uri.TryCreate(url, UriKind.Absolute, out var address))
            throw DownloadException.InvalidAddress();

        // Uri reports the scheme in lower case, so HTTPS:// and https:// are one scheme.
        if (address.Scheme != Uri.UriSchemeHttps
            && !(_seam.AllowPlainHttp && address.Scheme == Uri.UriSchemeHttp))
        {
            throw DownloadException.NotHttps();
        }

        // Uri.UserInfo alone cannot distinguish absent from explicitly empty user information.
        if (address.UserInfo.Length != 0
            || address.GetLeftPart(UriPartial.Authority).Contains('@', StringComparison.Ordinal))
        {
            throw DownloadException.UserInformation();
        }

        switch (address.HostNameType)
        {
            case UriHostNameType.Dns:
                // The name is resolved in its ASCII (IDNA) form. A spelling with no such form,
                // or one whose conversion leaves anything but DNS name characters (the
                // conversion is the platform's, and can map a lookalike to a delimiter), names
                // no host.
                if (!HasDnsName(address))
                    throw DownloadException.InvalidAddress();

                return address;

            case UriHostNameType.IPv4:
            case UriHostNameType.IPv6:
                // Uri has already folded every spelling of a literal (127.1, 0x7f.0.0.1,
                // 2130706433) into its canonical text.
                if (!IPAddress.TryParse(address.Host, out var literal))
                    throw DownloadException.InvalidAddress();

                if (!_seam.IsAllowedAddress(literal))
                    throw DownloadException.NonPublicAddress(literal);

                return address;

            default:
                throw DownloadException.InvalidAddress();
        }
    }

    private static bool HasDnsName(Uri address)
    {
        string ascii;
        try
        {
            ascii = address.IdnHost;
        }
        catch (UriFormatException)
        {
            return false;
        }

        if (ascii.Length == 0)
            return false;

        foreach (var ch in ascii)
        {
            if (!char.IsAsciiLetterOrDigit(ch) && ch is not ('-' or '_' or '.'))
                return false;
        }

        return true;
    }

    /// <summary>
    /// A program's response is KatLang source only when its <c>Content-Type</c> says it is
    /// text: <c>text/plain</c> (any character set) or <c>application/octet-stream</c>.
    /// </summary>
    private static void RequireSourceText(HttpContent content)
    {
        if (content.Headers.ContentType?.MediaType is { } mediaType)
        {
            if (mediaType.Equals("text/plain", StringComparison.OrdinalIgnoreCase)
                || mediaType.Equals("application/octet-stream", StringComparison.OrdinalIgnoreCase))
            {
                return;
            }

            throw DownloadException.NotKatLangSource(mediaType.ToLowerInvariant());
        }

        // No parsed media type: the header is absent, or present and not a media type.
        throw DownloadException.NotKatLangSource(
            mediaType: null,
            unreadable: content.Headers.NonValidated.Contains("Content-Type"));
    }

    /// <summary>
    /// Opens the connection of one request: resolves the host, judges every address of the
    /// answer, and connects to the first permitted address that accepts. The address that was
    /// judged IS the address connected to — nothing resolves the name again — and a refused
    /// address is never tried, whatever else the answer holds.
    ///
    /// <para>Permitted addresses are tried one at a time, in the answer's order. One that
    /// refuses is passed over at once. One that does not answer is given up after its share of
    /// <see cref="ConnectFallbackBudget"/>, which all attempts before the last divide equally,
    /// so however many addresses stall, the last still has two thirds of the deadline for its
    /// connection, TLS and the response. An IPv4-mapped address is dialed as the IPv4 address
    /// it carries.</para>
    /// </summary>
    private async ValueTask<Stream> ConnectAsync(SocketsHttpConnectionContext context, CancellationToken cancellationToken)
    {
        var endPoint = context.DnsEndPoint;

        IPAddress[] addresses;
        if (IPAddress.TryParse(endPoint.Host, out var literal))
        {
            addresses = [literal];
        }
        else
        {
            try
            {
                addresses = await _seam.ResolveAsync(endPoint.Host, cancellationToken).ConfigureAwait(false);
            }
            catch (SocketException ex)
            {
                throw DownloadException.NameResolution(ex);
            }
        }

        // Judge the whole answer first: only the addresses that passed are ever dialed.
        var permitted = new List<IPAddress>(addresses.Length);
        IPAddress? refused = null;
        foreach (var address in addresses)
        {
            if (_seam.IsAllowedAddress(address))
                permitted.Add(address);
            else
                refused ??= address;
        }

        if (permitted.Count == 0)
        {
            throw refused is not null
                ? DownloadException.NonPublicAddress(refused)
                : DownloadException.NameResolution();
        }

        // An address that never answers (a host with an unreachable IPv6 address, say) must
        // not use up the download's deadline while another address would answer. Every attempt
        // but the last is bounded, and together they may take no more than ConnectFallbackBudget,
        // however many addresses the answer holds: an equal share each. The last attempt is not
        // bounded here, so it has all the time the download has left.
        var fallbackAttempts = permitted.Count - 1;
        Exception? connectFailure = null;
        for (var index = 0; index < permitted.Count; index++)
        {
            // An IPv4-mapped address (::ffff:a.b.c.d) is the IPv4 address it carries, and only
            // an IPv4 socket reaches it: an IPv6 socket is IPv6-only. It was judged as that
            // IPv4 address (PublicAddress), so the address dialed is the address judged.
            var address = permitted[index];
            var target = new IPEndPoint(address.IsIPv4MappedToIPv6 ? address.MapToIPv4() : address, endPoint.Port);

            using var attempt = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
            if (index < fallbackAttempts)
                attempt.CancelAfter(ConnectFallbackBudget / fallbackAttempts);

            try
            {
                return await _seam.OpenAsync(target, attempt.Token).ConfigureAwait(false);
            }
            catch (Exception ex) when (ex is SocketException
                || (ex is OperationCanceledException && !cancellationToken.IsCancellationRequested))
            {
                // This address refused, or did not answer in its share of the time; the next
                // permitted one may.
                connectFailure = ex;
            }
        }

        throw DownloadException.ConnectionFailed(connectFailure);
    }

    /// <summary>
    /// The most time the connection attempts before the last one may take TOGETHER, when a host
    /// has several permitted addresses: a third of the download's deadline. The rest of the
    /// deadline is left for the last address, TLS, the request and the response.
    /// </summary>
    internal TimeSpan ConnectFallbackBudget => ConfiguredDownloadTimeout / 3;

    private static DownloadException? FindDownloadException(Exception exception)
    {
        for (Exception? current = exception; current is not null; current = current.InnerException)
        {
            if (current is DownloadException found)
                return found;
        }

        return null;
    }

    public void Dispose() => _client.Dispose();
}
