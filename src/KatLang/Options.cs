namespace KatLang;

/// <summary>
/// Options for <see cref="Parser.Parse(string, ParseOptions?)"/>.
/// Encapsulates optional module-loading configuration.
/// </summary>
public sealed class ParseOptions
{
    /// <summary>
    /// Injected code fetcher: URL → source text. In WASM, pass a JS interop downloader.
    /// If null, load directives are not elaborated.
    /// </summary>
    public Func<string, string>? DownloadCode { get; init; }

    /// <summary>
    /// Optional set of allowed hostnames for load directives. Defaults to katlang.org only.
    /// </summary>
    public IEnumerable<string>? AllowedHosts { get; init; }
}

/// <summary>
/// Options for <see cref="KatLang.Run(string, RunOptions?)"/> and related façade methods.
/// </summary>
public sealed class RunOptions
{
    /// <summary>
    /// Injected code fetcher: URL → source text. In WASM, pass a JS interop downloader.
    /// If null, load directives are not elaborated.
    /// </summary>
    public Func<string, string>? DownloadCode { get; init; }

    /// <summary>
    /// Optional set of allowed hostnames for load directives. Defaults to katlang.org only.
    /// </summary>
    public IEnumerable<string>? AllowedHosts { get; init; }

    internal ParseOptions? ToParseOptions()
    {
        if (DownloadCode is null && AllowedHosts is null)
            return null;
        return new ParseOptions { DownloadCode = DownloadCode, AllowedHosts = AllowedHosts };
    }
}
