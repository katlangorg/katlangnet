using System.Net;
using KatLang;

var source = """
    doNotSin=Math.Sin
    doNotSin(1.23) #Remember Jesus
    """;

// A host downloader owns the transport policy KatLang cannot see: KatLang validates only the
// URL it hands over (RunOptions.AllowedHosts), so this client refuses redirects (a redirect
// would fetch a host KatLang never validated), bounds the body, and sends no cookies.
using var client = new HttpClient(new SocketsHttpHandler { AllowAutoRedirect = false, UseCookies = false })
{
    Timeout = TimeSpan.FromSeconds(10),
    MaxResponseContentBufferSize = 1024 * 1024,
};

switch (await KatLangEngine.RunAsync(source, new RunOptions { DownloadCode = (url, token) => DownloadCode(client, url, token) }))
{
    case RunResult.Success s:
        Console.WriteLine(s.ToDisplayString());
        break;

    case RunResult.NoProgramOutput n:
        Console.WriteLine(n.ToDisplayString());
        break;

    case RunResult.ParseFailure p:
        foreach (var error in p.Errors)
            Console.WriteLine(error);
        break;

    case RunResult.EvalFailure e:
        foreach (var error in e.Errors)
            Console.WriteLine(error);
        break;
}

static async ValueTask<string> DownloadCode(HttpClient client, string url, CancellationToken cancellationToken)
{
    using var response = await client.GetAsync(url, cancellationToken);
    if (response.StatusCode != HttpStatusCode.OK)
        throw new HttpRequestException($"HTTP status {(int)response.StatusCode}.", inner: null, response.StatusCode);

    return await response.Content.ReadAsStringAsync(cancellationToken);
}
