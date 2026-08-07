namespace KatLang;

/// <summary>
/// Optional configuration for KatLang parsing and evaluation.
/// </summary>
public sealed class RunOptions
{
    /// <summary>
    /// Injected code fetcher: URL → source text. In WASM, pass a JS interop downloader.
    /// If <see cref="DownloadCodeWithCancellation"/> is also supplied, that token-aware fetcher
    /// takes precedence and this legacy callback is not called.
    /// If this and <see cref="DownloadCodeWithCancellation"/> are both null, this configuration
    /// does not provide module elaboration support, so any source that uses <c>load</c> is rejected
    /// by the public parser/run pipeline.
    /// </summary>
    public Func<string, string>? DownloadCode { get; init; }

    /// <summary>
    /// Injected token-aware code fetcher: URL and the configured
    /// <see cref="SourceProcessingCancellationToken"/> → source text. In WASM, pass a JS
    /// interop downloader that observes the token where the host integration permits it.
    /// If both this property and <see cref="DownloadCode"/> are supplied, this token-aware
    /// fetcher takes precedence deterministically.
    /// <para>If both downloader properties are null, this configuration does not provide module
    /// elaboration support, so any source that uses <c>load</c> is rejected by the public
    /// parser/run pipeline.</para>
    /// </summary>
    public Func<string, CancellationToken, string>? DownloadCodeWithCancellation { get; init; }

    /// <summary>
    /// Host cancellation for parsing, module fetching, and front-end source processing.
    /// The token is passed unchanged to <see cref="DownloadCodeWithCancellation"/>. Cancellation
    /// is checked at front-end phase boundaries and immediately before and after each module
    /// fetch. It does not cancel arbitrary evaluator computation after source processing has
    /// completed; use <see cref="EvaluationLimits"/> to bound evaluator work.
    /// <para>An <see cref="OperationCanceledException"/> is propagated as host cancellation only
    /// when this token has been cancelled. A downloader cancellation or timeout while this token
    /// is not cancelled remains an ordinary <c>load: failed to fetch</c> diagnostic.</para>
    /// </summary>
    public CancellationToken SourceProcessingCancellationToken { get; init; }

    /// <summary>
    /// Optional set of allowed hostnames for load directives. Defaults to katlang.org only.
    /// </summary>
    public IEnumerable<string>? AllowedHosts { get; init; }

    /// <summary>
    /// Optional deterministic evaluation resource limits. When null,
    /// <see cref="KatLang.EvaluationLimits.Default"/> applies: hard depth, per-collection,
    /// per-string, and returned-display ceilings are enforced; step and cumulative
    /// materialization budgets remain optional.
    /// <para>These are immutable configuration and safe to share across runs — the
    /// mutable counters live in run-scoped evaluation state, so every run starts
    /// fresh.</para>
    /// </summary>
    public EvaluationLimits? EvaluationLimits { get; init; }

    /// <summary>
    /// Optional host-runtime limits on the source text and module graph consumed BEFORE
    /// evaluation. When null, <see cref="KatLang.SourceProcessingLimits.Default"/> applies:
    /// always-active per-source length, import depth, aggregate source, and module-count
    /// ceilings are enforced. These bound parsing and module loading, never evaluation
    /// (<see cref="EvaluationLimits"/> owns that), and are immutable configuration safe to
    /// share across concurrent runs — the counters live in run-scoped processing state.
    /// </summary>
    public SourceProcessingLimits? SourceProcessingLimits { get; init; }
}
