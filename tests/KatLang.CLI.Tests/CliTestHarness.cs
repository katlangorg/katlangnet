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
    /// Substitute for the CLI's HTTP transport. It reaches KatLang only when
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
