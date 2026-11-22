namespace KatLang.CLI.Tests;

/// <summary>What one CLI invocation produced: exit code, stdout, stderr.</summary>
internal sealed record CliResult(int ExitCode, string Output, string Error)
{
    /// <summary>Stdout with platform newlines normalized and trailing newlines removed.</summary>
    public string TrimmedOutput => Normalize(Output);

    /// <summary>Stderr with platform newlines normalized and trailing newlines removed.</summary>
    public string TrimmedError => Normalize(Error);

    private static string Normalize(string text)
        => text.Replace("\r\n", "\n", StringComparison.Ordinal).TrimEnd('\n');
}

/// <summary>
/// Drives the real CLI boundary — an argument array in, an exit code and the two
/// output streams out — without spawning a process. Everything below
/// <see cref="CliApplication.RunAsync"/> (command-line parsing, source
/// acquisition, KatLang configuration, formatting) is exercised exactly as the
/// executable exercises it; only <c>Program.cs</c>'s console wiring is outside.
/// </summary>
internal static class Cli
{
    public static Task<CliResult> InvokeAsync(params string[] args)
        => InvokeWithDownloaderAsync(null, args);

    /// <param name="downloader">
    /// Substitute for the CLI's HTTP transport: address to text, with no rule of its own. It
    /// serves a program URL operand, and it reaches KatLang only when
    /// <c>--allow-loading</c> is supplied, so a test can also assert that it was
    /// never consulted.
    /// </param>
    public static async Task<CliResult> InvokeWithDownloaderAsync(
        Func<string, CancellationToken, ValueTask<string>>? downloader,
        params string[] args)
    {
        var output = new StringWriter();
        var error = new StringWriter();
        var exitCode = await CliApplication.RunAsync(args, output, error, downloader);
        return new CliResult(exitCode, output.ToString(), error.ToString());
    }

    /// <param name="transport">
    /// The real downloader, as a test built it — usually over a <see cref="StubHttpHandler"/>,
    /// so its rules (the address checks, the status, the content type, the size, the deadline)
    /// run in the test and no connection is ever opened.
    /// </param>
    public static async Task<CliResult> InvokeWithTransportAsync(
        HttpSourceDownloader transport,
        params string[] args)
    {
        var output = new StringWriter();
        var error = new StringWriter();
        var exitCode = await CliApplication.RunAsync(args, output, error, transport);
        return new CliResult(exitCode, output.ToString(), error.ToString());
    }
}

/// <summary>
/// The "network" of a transport under test: every request the real
/// <see cref="HttpSourceDownloader"/> sends is answered here, in memory, and recorded. A
/// request reaches it only after the downloader's own address checks, so an empty
/// <see cref="RequestedUrls"/> shows that a refusal came before any request.
/// </summary>
internal sealed class StubHttpHandler(Func<HttpRequestMessage, HttpResponseMessage> respond) : HttpMessageHandler
{
    private readonly List<string> _requestedUrls = [];

    /// <summary>Serves one fixed response for every address.</summary>
    public StubHttpHandler(Func<HttpResponseMessage> respond)
        : this(_ => respond())
    {
    }

    /// <summary>Serves text per exact address; any other address is a 404.</summary>
    public StubHttpHandler(IReadOnlyDictionary<string, string> pages)
        : this(request => pages.TryGetValue(request.RequestUri!.AbsoluteUri, out var text)
            ? Text(text)
            : Status(System.Net.HttpStatusCode.NotFound))
    {
    }

    /// <summary>The absolute address of every request, in order.</summary>
    public IReadOnlyList<string> RequestedUrls => _requestedUrls;

    /// <summary>A transport with the SHIPPED guardrails and bounds over this handler.</summary>
    public HttpSourceDownloader Transport(TimeSpan? deadline = null)
        => new(HttpSourceDownloader.MaxResponseBodyBytes, deadline ?? HttpSourceDownloader.DownloadTimeout, this);

    /// <summary>A 200 response with <paramref name="body"/> as UTF-8.</summary>
    public static HttpResponseMessage Text(string body, string? contentType = "text/plain; charset=utf-8")
        => Bytes(System.Text.Encoding.UTF8.GetBytes(body), contentType);

    /// <summary>
    /// A 200 response with exactly these body bytes. The Content-Type is set as RAW header
    /// text, as a server sends it, valid or not; null sends none.
    /// </summary>
    public static HttpResponseMessage Bytes(byte[] body, string? contentType)
    {
        var response = new HttpResponseMessage(System.Net.HttpStatusCode.OK) { Content = new ByteArrayContent(body) };
        if (contentType is not null)
            Assert.True(response.Content.Headers.TryAddWithoutValidation("Content-Type", contentType));
        return response;
    }

    /// <summary>A response with <paramref name="status"/> and a small HTML error body.</summary>
    public static HttpResponseMessage Status(System.Net.HttpStatusCode status, string? location = null)
    {
        var response = new HttpResponseMessage(status)
        {
            Content = new StringContent("<html>error page</html>", System.Text.Encoding.UTF8, "text/html"),
        };
        if (location is not null)
            response.Headers.Location = new Uri(location);
        return response;
    }

    protected override Task<HttpResponseMessage> SendAsync(HttpRequestMessage request, CancellationToken cancellationToken)
    {
        cancellationToken.ThrowIfCancellationRequested();
        lock (_requestedUrls)
            _requestedUrls.Add(request.RequestUri!.AbsoluteUri);
        return Task.FromResult(respond(request));
    }
}

/// <summary>
/// An in-memory stand-in for the network that records every URL KatLang asks
/// for, so tests can assert both that loading happened and that it did not.
/// </summary>
internal sealed class RecordingDownloader(IReadOnlyDictionary<string, string> modules)
{
    private readonly List<string> _requestedUrls = [];

    public RecordingDownloader() : this(new Dictionary<string, string>()) { }

    public IReadOnlyList<string> RequestedUrls => _requestedUrls;

    public ValueTask<string> DownloadAsync(string url, CancellationToken cancellationToken)
    {
        _requestedUrls.Add(url);

        return modules.TryGetValue(url, out var source)
            ? ValueTask.FromResult(source)
            : ValueTask.FromException<string>(new HttpRequestException($"no route to '{url}' in this test."));
    }
}

/// <summary>A throwaway <c>.kat</c> file for the file-based commands.</summary>
internal sealed class TempSourceFile : IDisposable
{
    public TempSourceFile(string content)
    {
        Path = System.IO.Path.Combine(
            System.IO.Path.GetTempPath(),
            $"katlang-cli-{Guid.NewGuid():N}.kat");

        File.WriteAllText(Path, content);
    }

    public string Path { get; }

    public void Dispose()
    {
        try
        {
            File.Delete(Path);
        }
        catch (IOException)
        {
            // A leftover temp file is not worth failing a test over.
        }
    }

    /// <summary>A path that is guaranteed not to exist.</summary>
    public static string MissingPath()
        => System.IO.Path.Combine(
            System.IO.Path.GetTempPath(),
            $"katlang-cli-missing-{Guid.NewGuid():N}.kat");
}
