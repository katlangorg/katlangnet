namespace KatLang;

/// <summary>
/// Deterministic, run-scoped HOST-RUNTIME limits on the work and memory KatLang consumes
/// turning source text and imported modules into an elaborated program, BEFORE the evaluator
/// runs. These are host-runtime policy, not language semantics: they bound how much source a
/// caller may submit and how large a module graph a run may pull, so an oversized submission
/// or a pathological import graph fails with a structured diagnostic instead of exhausting the
/// host. They do NOT change the meaning of any in-budget program, and Lean does not model them.
///
/// <para>The evaluator's own budgets live separately in <see cref="EvaluationLimits"/>; this
/// type never overlaps them. The prebuilt-AST evaluator entry points bypass parsing, so they
/// are governed by <see cref="EvaluationLimits"/> alone and are unaffected by these ceilings.</para>
///
/// <list type="bullet">
///   <item><b>Source length</b> (<see cref="MaxSourceLength"/>) bounds ONE source text — the
///   main program and each imported module — in UTF-16 code units, checked before tokenization.
///   The measurement probes show token and ordinary syntax/frontend-node counts scaling linearly
///   with source length, so this ceiling also bounds those counts (diagnostics, up to one per code
///   unit, are bounded further by the diagnostic count below). The formerly
///   quadratic per-construct paths (wide assignment deconstruction and large conditional clause
///   families) are now linear in the number of targets/clauses, so this bound is a resource ceiling
///   rather than the only thing standing between a caller and quadratic parse work.</item>
///   <item><b>Import depth</b> (<see cref="MaxModuleDepth"/>) bounds how deep a transitive
///   <c>load</c> chain may descend. The loader is recursive, so without this an unbounded chain
///   overflows the host stack — an uncatchable process crash — which this converts into a
///   structured diagnostic.</item>
///   <item><b>Aggregate source</b> (<see cref="MaxAggregateSourceLength"/>) bounds the TOTAL
///   source one run ELABORATES: the main program, every module accepted for parsing, and every
///   further SPLICE of a module the run has already loaded. A per-module ceiling alone does not
///   bound a wide graph of many individually-legal modules, and a cached module spliced into
///   many scopes is elaborated once per scope, so a repeated <c>load</c> of a cached URL charges
///   the source that splice adds to the program (the module's own source plus everything its own
///   loads charged) although it downloads nothing.</item>
///   <item><b>Module count</b> (<see cref="MaxModuleCount"/>) bounds the number of module
///   DOWNLOADS one run requests from <see cref="RunOptions.DownloadCode"/>: every downloader
///   invocation consumes one, whatever it returns, while a load of a module the run has already
///   loaded is served from the run's module cache and consumes none. It bounds the transport
///   requests a source can cause as well as the tree many tiny modules could build.</item>
///   <item><b>Diagnostic count</b> (<see cref="MaxDiagnosticCount"/>) bounds how many
///   <see cref="Diagnostic"/>s one diagnostic list keeps. Malformed source costs one diagnostic
///   per offending token, so a large invalid input would otherwise produce a result holding
///   millions of diagnostics; past the limit a list keeps its first diagnostics and ends with
///   one <see cref="DiagnosticCode.DiagnosticCountExceeded"/> diagnostic.</item>
/// </list>
///
/// <para>The source and module ceilings are RUN-scoped and INHERITED: the main program and every
/// module it loads — nested modules, and modules a deferred conditional branch loads when
/// evaluation selects it — draw on the same budget, so a descendant never starts from a fresh
/// one. The diagnostic count bounds each diagnostic LIST KatLang produces: the one list of a
/// parse (the main program, every module it loads, and every nested module share it) and the
/// list of each demand-time materialization of a deferred branch, which belongs to the
/// evaluation that requested it.</para>
///
/// <para>Every ceiling is always active: the supported maximum applies to a run that configures
/// nothing, and a configured value may only request a LOWER limit — there is no "unlimited"
/// representation. Values above the supported maximum are clamped down rather than rejected, so
/// raising a request can never weaken host safety; non-positive values are rejected.</para>
///
/// <para>Limits are immutable configuration and safe to share across concurrent runs: the
/// mutable counters (aggregate source consumed, module downloads requested, current import
/// depth) and every diagnostic list live in run-scoped processing state, never here.</para>
/// </summary>
public sealed record SourceProcessingLimits
{
    /// <summary>
    /// Internal hard ceiling on the length of ONE source text (the main program or a single
    /// imported module), in UTF-16 code units, applied on every parser/front-end entry point
    /// regardless of configuration. <see cref="MaxSourceLength"/> can only request a lower limit.
    ///
    /// <para>Checked before tokenization, so an oversized submission never allocates tokens or
    /// nodes. Calibrated by the process-isolated source probes (<c>fuzz/KatLang.ParserFuzz</c>,
    /// <c>source-probe</c>): measured token and ordinary node counts scale linearly once the
    /// frontend O(P^2) sibling-map passes, the wide-deconstruction elaboration, and the
    /// conditional clause-family duplicate check were made linear. A maximal 2 MiB source of dense
    /// declarations costs roughly 600-900 MB of peak working set. The value matches
    /// the pre-existing per-module download ceiling, so the main program and imported modules
    /// share one consistent bound. Ordinary programs are orders of magnitude smaller (the whole
    /// language-spec and tutorial corpus is a few KB each); WASM or multi-tenant embedders that
    /// want a tighter memory envelope configure a lower value.</para>
    /// </summary>
    public const int MaxSupportedSourceLength = 2 * 1024 * 1024;

    /// <summary>
    /// Internal hard ceiling on transitive <c>load</c> import-chain depth, applied whenever module
    /// elaboration runs. <see cref="MaxModuleDepth"/> can only request a lower limit.
    ///
    /// <para>The module loader resolves a <c>load</c> by recursively fetching, parsing, and
    /// elaborating the target, so a deep chain recurses the host stack. The process-isolated
    /// import-depth probe (<c>module-depth-search</c>) measured the crash boundary at 562 (Release)
    /// and 605 (Debug) transitive levels on a 1 MiB Windows stack — an uncatchable
    /// StackOverflowException, not a structured error. 64 keeps roughly a 9x margin below that on
    /// the measured Windows stack. Smaller-stack hosts such as WASM motivate that conservative
    /// margin, but available WASM stack headroom is runtime-specific and was not measured by this
    /// campaign.</para>
    /// </summary>
    public const int MaxSupportedModuleDepth = 64;

    /// <summary>
    /// Internal hard ceiling on the TOTAL source length one run elaborates — the main program,
    /// every module accepted for parsing, and every further splice of an already-loaded module —
    /// in UTF-16 code units. <see cref="MaxAggregateSourceLength"/> can only request a lower limit.
    ///
    /// <para>A per-module ceiling does not bound a wide graph: one module may reference thousands
    /// of others, and the source probes accepted 67 MB of aggregate module source (64 modules of
    /// 1 MiB each) with no limit. 8 MiB is four times the single-source ceiling — generous for a
    /// genuine multi-module program (real graphs total well under a megabyte) while bounding the
    /// run-wide memory a module graph can pull.</para>
    ///
    /// <para>The total also counts every further SPLICE of an already-loaded module. A module
    /// content's names resolve against the scope it is spliced into, so the front end elaborates
    /// one copy per enclosing scope: a 10 KB module spliced into 373 distinct blocks cost 3.2 GB of
    /// allocation, and the same work grows with the product of the two source sizes, which no
    /// per-source ceiling bounds. A splice served from the module cache therefore charges the
    /// source it adds to the elaborated program — the module's own source plus everything its own
    /// loads charged — so this ceiling bounds the elaborated program, not just the text
    /// downloaded.</para>
    /// </summary>
    public const long MaxSupportedAggregateSourceLength = 8L * 1024 * 1024;

    /// <summary>
    /// Internal hard ceiling on the number of module DOWNLOADS one run may request, applied
    /// whenever module elaboration runs. <see cref="MaxModuleCount"/> can only request a lower
    /// limit.
    ///
    /// <para>Many tiny modules each pass the per-module and aggregate ceilings yet together build
    /// an arbitrarily large syntax tree: the probes accepted 5000 distinct modules (about 283k
    /// nodes) with no limit. 256 bounds that node/time growth while staying far above real usage
    /// (programs import a handful of libraries). A repeated <c>load</c> of an already-loaded URL
    /// is served from the run's module cache and consumes no slot. Every downloader invocation
    /// consumes one whatever it returns — a failed download, a text over the per-source limit,
    /// and a text that does not fit the aggregate still happened — so a program that names
    /// thousands of unreachable or oversized modules cannot re-request them without limit:
    /// this ceiling is also the per-run bound on requests to <see cref="RunOptions.DownloadCode"/>.</para>
    /// </summary>
    public const int MaxSupportedModuleCount = 256;

    /// <summary>
    /// Internal hard ceiling on the number of <see cref="Diagnostic"/>s ONE diagnostic list keeps
    /// before it is truncated, applied to every list KatLang produces regardless of configuration.
    /// <see cref="MaxDiagnosticCount"/> can only request a lower limit.
    ///
    /// <para><b>What one list is.</b> A parse produces one list
    /// (<see cref="ParseResult.Diagnostics"/>, projected by a run into
    /// <see cref="RunResult.ParseFailure.Errors"/>): the main program's lexical, syntax,
    /// module-loading, and elaboration diagnostics and those of every module and nested module it
    /// loads all draw on it. A deferred conditional branch materialized when evaluation selects it
    /// produces its own list, reported by that evaluation's error. The standalone
    /// <see cref="Lexer.Tokenize(string)"/> list is bounded by this supported maximum.</para>
    ///
    /// <para><b>Truncation.</b> Past the limit, a list keeps exactly the first diagnostics an
    /// unbounded list would hold, in the same order, followed by ONE
    /// <see cref="DiagnosticCode.DiagnosticCountExceeded"/> error diagnostic with no position,
    /// which the limit does not count. Later diagnostics are neither stored nor formatted.
    /// Processing continues unchanged — the recovery tree, module loading, and every decision
    /// are the same whether or not the limit was reached — so for a list that stays within the
    /// limit it is unobservable, and a list that holds the marker is known to be incomplete.
    /// Every retained message is itself at most 4096 UTF-16 code units, so one list is bounded
    /// by a constant (about four million code units of message text at the very worst;
    /// ordinary messages are a few hundred code units).</para>
    ///
    /// <para><b>Calibration.</b> Malformed source can produce one diagnostic per UTF-16 code
    /// unit (a bad character, a stray closer, a semicolon), so the process-isolated probes kept
    /// 2.1 million diagnostics — up to 464 MB retained and 400 million characters of message
    /// text — for one 2 MiB source, more than three times what the largest valid program
    /// retains. Ordinary programs report a handful of diagnostics; real non-KatLang files
    /// pasted as source report 30 to 130 per thousand code units (a 26 KB README reports about
    /// 2,300), and everything past the first few hundred is cascade. 1000 keeps every realistic
    /// program's complete list while bounding the result, and anything that renders it, by a
    /// constant.</para>
    /// </summary>
    public const int MaxSupportedDiagnosticCount = 1000;

    private readonly int? _maxSourceLength;
    private readonly int? _maxModuleDepth;
    private readonly long? _maxAggregateSourceLength;
    private readonly int? _maxModuleCount;
    private readonly int? _maxDiagnosticCount;

    /// <summary>
    /// Maximum UTF-16 code units in one source text, or <c>null</c> to use
    /// <see cref="MaxSupportedSourceLength"/>. Values above the supported maximum are clamped
    /// down to it.
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException">The value is zero or negative.</exception>
    public int? MaxSourceLength
    {
        get => _maxSourceLength;
        init
        {
            if (value is <= 0)
            {
                throw new ArgumentOutOfRangeException(
                    nameof(MaxSourceLength), value, "Source length limit must be at least 1.");
            }

            _maxSourceLength = value;
        }
    }

    /// <summary>
    /// Maximum transitive <c>load</c> import-chain depth, or <c>null</c> to use
    /// <see cref="MaxSupportedModuleDepth"/>. Values above the supported maximum are clamped
    /// down to it.
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException">The value is zero or negative.</exception>
    public int? MaxModuleDepth
    {
        get => _maxModuleDepth;
        init
        {
            if (value is <= 0)
            {
                throw new ArgumentOutOfRangeException(
                    nameof(MaxModuleDepth), value, "Module depth limit must be at least 1.");
            }

            _maxModuleDepth = value;
        }
    }

    /// <summary>
    /// Maximum total source length across one run, or <c>null</c> to use
    /// <see cref="MaxSupportedAggregateSourceLength"/>. Values above the supported maximum are
    /// clamped down to it.
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException">The value is zero or negative.</exception>
    public long? MaxAggregateSourceLength
    {
        get => _maxAggregateSourceLength;
        init
        {
            if (value is <= 0)
            {
                throw new ArgumentOutOfRangeException(
                    nameof(MaxAggregateSourceLength), value, "Aggregate source length limit must be at least 1.");
            }

            _maxAggregateSourceLength = value;
        }
    }

    /// <summary>
    /// Maximum number of module downloads one run may request (every downloader invocation
    /// counts; a load served from the run's module cache does not), or <c>null</c> to use
    /// <see cref="MaxSupportedModuleCount"/>. Values above the supported maximum are clamped
    /// down to it.
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException">The value is zero or negative.</exception>
    public int? MaxModuleCount
    {
        get => _maxModuleCount;
        init
        {
            if (value is <= 0)
            {
                throw new ArgumentOutOfRangeException(
                    nameof(MaxModuleCount), value, "Module count limit must be at least 1.");
            }

            _maxModuleCount = value;
        }
    }

    /// <summary>
    /// Maximum number of diagnostics one diagnostic list keeps before it ends with a
    /// <see cref="DiagnosticCode.DiagnosticCountExceeded"/> diagnostic (which is not counted), or
    /// <c>null</c> to use <see cref="MaxSupportedDiagnosticCount"/>. Values above the supported
    /// maximum are clamped down to it.
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException">The value is zero or negative.</exception>
    public int? MaxDiagnosticCount
    {
        get => _maxDiagnosticCount;
        init
        {
            if (value is <= 0)
            {
                throw new ArgumentOutOfRangeException(
                    nameof(MaxDiagnosticCount), value, "Diagnostic count limit must be at least 1.");
            }

            _maxDiagnosticCount = value;
        }
    }

    /// <summary>
    /// Default limits: every supported ceiling applies and nothing is configured lower.
    /// </summary>
    public static SourceProcessingLimits Default { get; } = new();

    /// <summary>The per-source length limit actually enforced: the ceiling, or a lower configured value.</summary>
    internal int EffectiveMaxSourceLength
        => _maxSourceLength is { } length && length < MaxSupportedSourceLength
            ? length
            : MaxSupportedSourceLength;

    /// <summary>The import-depth limit actually enforced.</summary>
    internal int EffectiveMaxModuleDepth
        => _maxModuleDepth is { } depth && depth < MaxSupportedModuleDepth
            ? depth
            : MaxSupportedModuleDepth;

    /// <summary>The aggregate-source limit actually enforced.</summary>
    internal long EffectiveMaxAggregateSourceLength
        => _maxAggregateSourceLength is { } length && length < MaxSupportedAggregateSourceLength
            ? length
            : MaxSupportedAggregateSourceLength;

    /// <summary>The distinct-module-count limit actually enforced.</summary>
    internal int EffectiveMaxModuleCount
        => _maxModuleCount is { } count && count < MaxSupportedModuleCount
            ? count
            : MaxSupportedModuleCount;

    /// <summary>The per-list diagnostic-count limit actually enforced.</summary>
    internal int EffectiveMaxDiagnosticCount
        => _maxDiagnosticCount is { } count && count < MaxSupportedDiagnosticCount
            ? count
            : MaxSupportedDiagnosticCount;
}
