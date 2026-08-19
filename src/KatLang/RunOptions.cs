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
    /// completed; use <see cref="EvaluationCancellationToken"/> to cancel evaluation and
    /// <see cref="EvaluationLimits"/> to bound evaluator work.
    /// <para>An <see cref="OperationCanceledException"/> is propagated as host cancellation only
    /// when this token has been cancelled. A downloader cancellation or timeout while this token
    /// is not cancelled remains an ordinary <c>load: failed to fetch</c> diagnostic.</para>
    /// </summary>
    public CancellationToken SourceProcessingCancellationToken { get; init; }

    /// <summary>
    /// Host cancellation for evaluation. Observed once at evaluation entry — an
    /// already-cancelled token prevents evaluation from starting — and then
    /// cooperatively at the evaluator's budget chokepoints: dynamic invocations, loop
    /// iterations (generic and optimized), argument evaluation, expression-work
    /// checkpoints, and collection/string reservations. Observation does not depend on
    /// any opt-in budget being configured, so cancellation also works under default
    /// <see cref="EvaluationLimits"/>. A final observation before completion prevents
    /// cancellation requested by the last evaluator operation from being missed; host
    /// flattening entry points also observe after their bounded atom projection.
    /// <para>Separate from <see cref="SourceProcessingCancellationToken"/>, which
    /// governs parsing and module loading only. A host that wants one stop signal for
    /// the whole pipeline passes the same token to both properties.</para>
    /// <para>Requested cancellation escapes as
    /// <see cref="OperationCanceledException"/> carrying this token — never a KatLang
    /// diagnostic, and never a retained resource-limit value, so a cancelled run does
    /// not continue. An uncancelled token changes no result, no diagnostic, and no
    /// limit verdict.</para>
    /// </summary>
    public CancellationToken EvaluationCancellationToken { get; init; }

    /// <summary>
    /// Optional set of allowed hostnames for load directives. Defaults to katlang.org only.
    /// </summary>
    public IEnumerable<string>? AllowedHosts { get; init; }

    /// <summary>
    /// Optional host operations exposed to the program as ambient callables (resolved
    /// like the built-in <c>Math</c> members; program-defined properties shadow them).
    /// The names resolve during front-end parameter detection too, so referencing an
    /// operation never turns it into an implicit parameter. Each operation receives the
    /// evaluated argument values and <see cref="EvaluationCancellationToken"/>, and its
    /// exceptions propagate to the host unchanged — see <see cref="HostOperation"/> for
    /// the full contract.
    /// <para>A set containing an ASYNCHRONOUS operation requires the asynchronous entry
    /// points (<see cref="KatLangEngine.RunAsync"/> and the async conveniences), where
    /// an incomplete host awaitable genuinely suspends evaluation and resumes it on
    /// completion; synchronous entry points reject such a configuration with
    /// <see cref="InvalidOperationException"/> before evaluating anything. Synchronous
    /// operations work on every entry point and keep <c>RunAsync</c>'s synchronous
    /// fast path.</para>
    /// <para>Like <see cref="EvaluationLimits"/>, this is immutable configuration and
    /// safe to share across concurrent and sequential runs — all run state lives in
    /// run-scoped evaluator structures.</para>
    /// </summary>
    public HostOperations? HostOperations { get; init; }

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
