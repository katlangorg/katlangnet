namespace KatLang.CLI;

/// <summary>
/// Transport for <see cref="RunOptions.DownloadCode"/> when <c>--allow-loading</c>
/// is supplied. KatLang validates every requested URL before calling this
/// transport. Redirects are refused so the HTTP layer cannot silently fetch a
/// second URL whose host KatLang never validated.
/// </summary>
internal static class HttpSourceDownloader
{
    // One client for the process lifetime, the documented HttpClient usage
    // pattern. A short-lived CLI process reclaims it on exit.
    private static readonly HttpClient Client = new(new SocketsHttpHandler
    {
        AllowAutoRedirect = false,
    });

    public static async ValueTask<string> DownloadAsync(string url, CancellationToken cancellationToken)
    {
        using var response = await Client.GetAsync(
            url,
            HttpCompletionOption.ResponseHeadersRead,
            cancellationToken).ConfigureAwait(false);

        if ((int)response.StatusCode is >= 300 and <= 399)
        {
            throw new HttpRequestException(
                "HTTP redirects are not allowed while loading KatLang algorithms.",
                inner: null,
                response.StatusCode);
        }

        response.EnsureSuccessStatusCode();
        return await response.Content.ReadAsStringAsync(cancellationToken).ConfigureAwait(false);
    }
}
