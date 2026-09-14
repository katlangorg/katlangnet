namespace KatLang;

/// <summary>
/// Optional configuration for KatLang parsing and evaluation.
/// </summary>
public sealed class RunOptions
{
    /// <summary>
    /// Injected asynchronous code fetcher — the ONE source-loading contract: URL and the
    /// active source-processing cancellation token to source text. Eager downloads receive
    /// <see cref="SourceProcessingCancellationToken"/> unchanged; deferred branch downloads
    /// receive a token linked to it and to the shared materialization's active consumers. A host with the
    /// source already in memory returns <c>ValueTask.FromResult(text)</c> and source processing
    /// completes synchronously; a networked host awaits ordinary managed I/O (for example
    /// <c>HttpClient.GetStringAsync(url, token)</c>) and source processing genuinely suspends
    /// until the download completes.
    /// <para>Configuring a downloader selects the ASYNCHRONOUS entry points
    /// (<see cref="KatLangEngine.RunAsync"/>, the async conveniences, and
    /// <see cref="Parser.ParseAsync"/>): the synchronous entry points cannot suspend for a
    /// download and reject a downloader-configured options object with
    /// <see cref="InvalidOperationException"/> before parsing anything. If this property is null,
    /// the configuration does not provide module elaboration support, so any source that uses
    /// <c>load</c> is rejected by the public parser/run pipeline with a diagnostic.</para>
    /// <para>KatLang performs no ambient downloading: the library owns no HTTP transport and
    /// ships no default downloader, so every byte of module source arrives through this
    /// delegate. <see cref="AllowedHosts"/> governs which source-written load targets KatLang
    /// hands to the delegate; transport behavior after that — connections, timeouts, and any
    /// redirect policy — is owned entirely by the host implementation.</para>
    /// </summary>
    public Func<string, CancellationToken, ValueTask<string>>? DownloadCode { get; init; }

    /// <summary>
    /// Host cancellation for parsing, module fetching, and front-end source processing.
    /// The token is passed unchanged to <see cref="DownloadCode"/> for eager loads and linked
    /// with consumer cancellation for deferred branch loads, including their loader-gate wait. Cancellation
    /// is checked at front-end phase boundaries and immediately before and after each module
    /// fetch. It does not cancel arbitrary evaluator computation after source processing has
    /// completed, but remains authoritative for later deferred module materialization;
    /// use <see cref="EvaluationCancellationToken"/> to cancel evaluation and
    /// <see cref="EvaluationLimits"/> to bound evaluator work.
    /// <para>When this token is cancelled, an escaping <see cref="OperationCanceledException"/>
    /// carries this exact token, taking precedence over evaluation cancellation —
    /// including when the downloader's awaitable faults with a different exception or cancellation
    /// token while the host token is cancelled. A downloader cancellation or timeout without
    /// source or materialization cancellation remains an ordinary <c>load: failed to fetch</c> diagnostic.</para>
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
    /// <para>A cancelled evaluation leaves a shared deferred materialization immediately. The
    /// underlying work is cancelled only when its last consumer leaves; it cannot publish an
    /// abandoned body. Source-processing cancellation remains authoritative when both tokens
    /// are cancelled during materialization.</para>
    /// <para>Requested cancellation escapes as
    /// <see cref="OperationCanceledException"/> carrying this token — never a KatLang
    /// diagnostic, and never a retained resource-limit value, so a cancelled run does
    /// not continue. An uncancelled token changes no result, no diagnostic, and no
    /// limit verdict.</para>
    /// </summary>
    public CancellationToken EvaluationCancellationToken { get; init; }

    /// <summary>
    /// Optional set of allowed hostnames for source-written load targets. KatLang validates
    /// the original HTTPS URL against this set before passing it to <see cref="DownloadCode"/>;
    /// it does not observe or recursively validate transport-level redirect destinations.
    /// Redirect handling and every other transport policy belong to the host-supplied downloader.
    /// A URL's host is admitted when it equals an entry or is a subdomain of one (<c>sub.ex.com</c>
    /// under <c>ex.com</c>; <c>ex.com.evil.net</c> is not), entries are trimmed, and a null, empty,
    /// or whitespace-only entry is rejected with <see cref="ArgumentException"/> at the parse/run
    /// entry point before anything is processed. Defaults to katlang.org only.
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
    /// Optional seed for KatLang's random operations — <c>Math.Random</c> / <c>random</c>
    /// and <c>Math.RandomInt</c> / <c>randomInt</c>. <c>null</c> (the default) keeps
    /// evaluation UNSEEDED and nondeterministic: every run draws from fresh entropy.
    /// Any <see cref="long"/> value is a valid seed — <c>0</c>, negative values,
    /// <see cref="long.MinValue"/>, and <see cref="long.MaxValue"/> included — and every
    /// distinct value names a distinct stream (<c>-5</c> and <c>5</c> differ; the seed's
    /// bit pattern is used as-is, never folded, hashed, or truncated).
    /// <para><b>Reproducibility contract.</b> For a given KatLang version: the same program
    /// (loaded module contents and a <c>DisplayDecimals</c> property, which is itself
    /// evaluated, included), the same seed, and the same semantically executed KatLang
    /// path produce the same random values on every supported platform. Both random
    /// operations, in every spelling, consume ONE run-scoped stream in actual evaluation
    /// order, so the values depend on which random calls execute and in what order —
    /// removing an earlier random call generally changes every later value (a call can
    /// consume a variable number of raw words), and the ordinary evaluation rules
    /// (left-to-right arguments, lazy <c>if</c> branches, the zero-argument property cache,
    /// explicit <c>A()</c> re-evaluation) decide which calls execute. Synchronous versus
    /// asynchronous entry points, optimizer strategies, and unrelated
    /// <see cref="EvaluationLimits"/> settings that do not change the program's actual
    /// control flow never alter the stream. Host-operation results are the host's
    /// responsibility and outside this guarantee. The exact stream may change in a future
    /// KatLang version when the generator, a sampling algorithm, or evaluation semantics
    /// deliberately change (release-noted); it is NOT promised across versions, and
    /// KatLang randomness is not cryptographically secure. The internal generator contract
    /// is documented in <c>docs/design/seeded-randomness-2026-09.md</c>.</para>
    /// <para><b>Lifetime.</b> This is immutable configuration, safe to share across
    /// concurrent and sequential runs — no generator state lives here. Each evaluation
    /// creates its own fresh stream from the seed: reusing one options object for
    /// sequential runs replays the stream from its beginning every time, and concurrent
    /// runs sharing one options object get independent stream instances initialized from
    /// the same seed. The direct <see cref="Evaluator.Run(Expr, EvaluationLimits?, long?, CancellationToken)"/>
    /// family accepts the same seed with the same semantics.</para>
    /// <para><see cref="Parser.Parse(string, RunOptions?)"/> and <see cref="Parser.ParseAsync"/>
    /// ignore this property: seeding is evaluation-only configuration with no effect on
    /// parsing, module loading, elaboration, or editor semantics.</para>
    /// </summary>
    public long? RandomSeed { get; init; }

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
