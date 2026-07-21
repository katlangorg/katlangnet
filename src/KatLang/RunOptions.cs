namespace KatLang;

/// <summary>
/// Optional configuration for KatLang parsing and evaluation.
/// </summary>
public sealed class RunOptions
{
    /// <summary>
    /// Injected code fetcher: URL → source text. In WASM, pass a JS interop downloader.
    /// If null, this configuration does not provide module elaboration support,
    /// so any source that uses <c>load</c> is rejected by the public parser/run pipeline.
    /// </summary>
    public Func<string, string>? DownloadCode { get; init; }

    /// <summary>
    /// Optional set of allowed hostnames for load directives. Defaults to katlang.org only.
    /// </summary>
    public IEnumerable<string>? AllowedHosts { get; init; }

    /// <summary>
    /// Optional deterministic evaluation resource limits. When null,
    /// <see cref="KatLang.EvaluationLimits.Default"/> applies: the internal depth
    /// ceiling is enforced and there is no step budget.
    /// <para>These are immutable configuration and safe to share across runs — the
    /// mutable counters live in run-scoped evaluation state, so every run starts
    /// fresh.</para>
    /// </summary>
    public EvaluationLimits? EvaluationLimits { get; init; }
}
