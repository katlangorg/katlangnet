namespace KatLang;

/// <summary>
/// Optional configuration for KatLang parsing and evaluation.
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
}
