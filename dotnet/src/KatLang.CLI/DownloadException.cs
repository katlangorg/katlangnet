using System.Globalization;
using System.Net;

namespace KatLang.CLI;

/// <summary>Why <see cref="HttpSourceDownloader"/> refused or could not complete a download.</summary>
internal enum DownloadFailure
{
    /// <summary>The address is not an absolute URL with a DNS-name or IP-literal host.</summary>
    InvalidAddress,

    /// <summary>The address is not <c>https</c>. Plain <c>http</c> is refused, never upgraded.</summary>
    NotHttps,

    /// <summary>The address carries user information (<c>user@</c> or <c>user:password@</c>).</summary>
    UserInformation,

    /// <summary>The host is, or resolves only to, an address <see cref="PublicAddress"/> refuses.</summary>
    NonPublicAddress,

    /// <summary>The host name has no address.</summary>
    NameResolution,

    /// <summary>No permitted address accepted a connection.</summary>
    ConnectionFailed,

    /// <summary>TLS could not be established with the host.</summary>
    SecureConnectionFailed,

    /// <summary>The request failed in some other way before a complete response arrived.</summary>
    RequestFailed,

    /// <summary>The server answered with a redirect (3xx), which is never followed.</summary>
    Redirect,

    /// <summary>The server answered with a status other than 200 that is not a redirect.</summary>
    UnexpectedStatus,

    /// <summary>A program's response is not served as KatLang source text.</summary>
    NotKatLangSource,

    /// <summary>The response body is over the byte ceiling.</summary>
    TooLarge,

    /// <summary>The whole-download deadline expired.</summary>
    DeadlineExceeded,

    /// <summary>The response names a character set the runtime cannot decode.</summary>
    UnsupportedCharacterSet,
}

/// <summary>
/// One refused or failed download, worded ONCE here for both kinds of download.
/// <see cref="Exception.Message"/> is the reason as a sentence that reads after a colon — lower
/// case, with its final period — and is fixed CLI text: it never carries the server's reason
/// phrase, a response excerpt, or a platform's socket message, so nothing a remote host
/// controls reaches the terminal through it (the media type of <see cref="Returned"/> is the
/// one remote value, and it is bounded printable ASCII).
///
/// <para>A module download surfaces it through KatLang as
/// <c>load: failed to fetch '&lt;url&gt;': &lt;message&gt;</c>; a program URL through the CLI as
/// <c>katlang: cannot download '&lt;link&gt;': &lt;message&gt;</c>, except for the two cases the CLI
/// words on their own (<c>not found</c> and <c>not KatLang source</c>).</para>
/// </summary>
internal sealed class DownloadException : Exception
{
    /// <summary>The longest media type a <see cref="NotKatLangSource"/> report echoes.</summary>
    internal const int MaxEchoedMediaTypeLength = 100;

    private DownloadException(DownloadFailure failure, string message, Exception? inner = null)
        : base(message, inner)
        => Failure = failure;

    public DownloadFailure Failure { get; }

    /// <summary>The response status, for <see cref="DownloadFailure.Redirect"/> and <see cref="DownloadFailure.UnexpectedStatus"/>.</summary>
    public HttpStatusCode? StatusCode { get; private init; }

    /// <summary>
    /// For <see cref="DownloadFailure.NotKatLangSource"/>, what came back in place of source
    /// text, as it completes the sentence "… returned …": the media type (<c>text/html</c>),
    /// <c>no Content-Type</c>, or <c>a Content-Type that cannot be read</c>.
    /// </summary>
    public string? Returned { get; private init; }

    public static DownloadException InvalidAddress()
        => new(DownloadFailure.InvalidAddress, "it is not a valid address.");

    public static DownloadException NotHttps()
        => new(DownloadFailure.NotHttps, "only HTTPS addresses are downloaded.");

    public static DownloadException UserInformation()
        => new(DownloadFailure.UserInformation, "it contains user information ('user@' or 'user:password@').");

    public static DownloadException NonPublicAddress(IPAddress address)
        => new(DownloadFailure.NonPublicAddress, $"its host is not at a public address ({address}).");

    public static DownloadException NameResolution(Exception? inner = null)
        => new(DownloadFailure.NameResolution, "its host name could not be resolved.", inner);

    public static DownloadException ConnectionFailed(Exception? inner = null)
        => new(DownloadFailure.ConnectionFailed, "the connection failed.", inner);

    /// <summary>A transport failure the HTTP client reported, worded by its category alone.</summary>
    public static DownloadException RequestFailed(HttpRequestException inner) => inner.HttpRequestError switch
    {
        HttpRequestError.NameResolutionError => NameResolution(inner),
        HttpRequestError.ConnectionError => ConnectionFailed(inner),
        HttpRequestError.SecureConnectionError
            => new(DownloadFailure.SecureConnectionFailed, "a secure connection could not be established.", inner),
        _ => new(DownloadFailure.RequestFailed, "the request failed.", inner),
    };

    public static DownloadException Redirect(HttpStatusCode status)
        => new(
            DownloadFailure.Redirect,
            $"the server responded with a redirect (HTTP status {Number((int)status)}), and redirects are not allowed.")
        {
            StatusCode = status,
        };

    public static DownloadException UnexpectedStatus(HttpStatusCode status)
        => new(
            DownloadFailure.UnexpectedStatus,
            $"the server responded with HTTP status {Number((int)status)}; only 200 (OK) is accepted.")
        {
            StatusCode = status,
        };

    /// <param name="mediaType">The response's media type; null when it has no Content-Type.</param>
    /// <param name="unreadable">The response has a Content-Type header that is not a media type.</param>
    public static DownloadException NotKatLangSource(string? mediaType, bool unreadable = false)
    {
        var returned = mediaType is not null
            ? Bounded(mediaType)
            : unreadable ? "a Content-Type that cannot be read" : "no Content-Type";
        return new(DownloadFailure.NotKatLangSource, $"the response is not KatLang source: it returned {returned}.")
        {
            Returned = returned,
        };
    }

    public static DownloadException DeclaredLengthTooLarge(long declaredLength, long limit)
        => new(
            DownloadFailure.TooLarge,
            $"the declared Content-Length of {Number(declaredLength)} bytes exceeds the {Number(limit)}-byte limit.");

    public static DownloadException BodyTooLarge(long limit, Exception? inner = null)
        => new(DownloadFailure.TooLarge, $"the response body exceeds the {Number(limit)}-byte limit.", inner);

    public static DownloadException DeadlineExceeded(TimeSpan deadline, Exception? inner = null)
        => new(
            DownloadFailure.DeadlineExceeded,
            $"the download did not complete within {deadline.TotalSeconds.ToString("0.###", CultureInfo.InvariantCulture)} seconds.",
            inner);

    public static DownloadException UnsupportedCharacterSet(Exception? inner = null)
        => new(DownloadFailure.UnsupportedCharacterSet, "the response names a character set that is not supported.", inner);

    private static string Number(long value) => value.ToString(CultureInfo.InvariantCulture);

    /// <summary>
    /// A media type is two HTTP tokens and a slash, so it is printable ASCII already; only its
    /// length is the server's to choose.
    /// </summary>
    private static string Bounded(string mediaType)
        => mediaType.Length <= MaxEchoedMediaTypeLength ? mediaType : mediaType[..MaxEchoedMediaTypeLength] + "...";
}
