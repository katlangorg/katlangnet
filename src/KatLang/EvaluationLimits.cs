namespace KatLang;

/// <summary>
/// Deterministic, run-scoped resource limits for KatLang evaluation.
///
/// <para>The limits are independent and deliberately not collapsed into one number:</para>
/// <list type="bullet">
///   <item><b>Depth</b> (<see cref="MaxDepth"/>) bounds how many dynamic algorithm
///   invocations may be active at once. Its purpose is host-stack safety.</item>
///   <item><b>Steps</b> (<see cref="MaxSteps"/>) bounds the cumulative amount of
///   semantic work one run may perform. Its purpose is stopping unbounded or
///   excessive computation such as a non-terminating loop.</item>
///   <item><b>Collections</b> (<see cref="MaxCollectionItems"/> and
///   <see cref="MaxMaterializedItems"/>) bound one persistent collection and cumulative
///   item-slot construction.</item>
///   <item><b>Language strings</b> (<see cref="MaxStringLength"/> and
///   <see cref="MaxMaterializedStringChars"/>) bound one string and cumulative UTF-16
///   units constructed.</item>
///   <item><b>Display</b> (<see cref="MaxDisplayLength"/>) strictly bounds every string
///   returned by <see cref="RunResult.ToDisplayString"/> and
///   <see cref="KatLangEngine.EvaluateToString(string, RunOptions)"/>.</item>
/// </list>
///
/// <para>Host cancellation and wall-clock timeouts are a third, different concept.
/// They are host policy rather than deterministic semantic budgets, and are not
/// part of this type.</para>
///
/// <para>Limits are immutable configuration. A single instance may be shared by any
/// number of concurrent runs: the mutable counters live in run-scoped evaluation
/// state, never here.</para>
/// </summary>
public sealed record EvaluationLimits
{
    /// <summary>
    /// Internal hard ceiling on dynamic evaluation depth, applied to every evaluation
    /// on every entry point regardless of configuration. <see cref="MaxDepth"/> can
    /// only request a LOWER limit; it can never raise this ceiling.
    ///
    /// <para>Calibrated by the process-isolated evaluator depth probes
    /// (<c>fuzz/KatLang.ParserFuzz</c>, <c>eval-probe</c>) on the default 1 MiB Windows
    /// stack. Measured host-stack failure boundaries, Debug / Release: plain
    /// clause-family recursion 222 / 333, the same recursion wrapped in ten nested
    /// parentheses per level 222 / 333, dotted recursion 176 / 272, recursion through
    /// the <c>if</c> builtin 91 / 139, and recursion through a collection callback
    /// 67 / 105. No single portable value is therefore simultaneously useful for real
    /// programs and provably safe for the heaviest shape on the smallest stack.</para>
    ///
    /// <para>128 keeps a measured margin of 1.7x (Debug) to 2.6x (Release) below the
    /// cheapest shape's boundary, so this deterministic limit — not the machine — is
    /// what stops ordinary runaway recursion, on both Windows and Linux. For the two
    /// most stack-expensive shapes the stack-headroom backstop described on
    /// <see cref="EvalError.EvaluationStackExhausted"/> takes over and still yields a
    /// structured error instead of terminating the process.</para>
    /// </summary>
    public const int MaxSupportedDepth = 128;

    private readonly int? _maxDepth;
    private readonly long? _maxSteps;

    /// <summary>
    /// Maximum number of simultaneously active dynamic algorithm invocations, or
    /// <c>null</c> to use <see cref="MaxSupportedDepth"/>. Values above
    /// <see cref="MaxSupportedDepth"/> are clamped down to it.
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException">The value is zero or negative.</exception>
    public int? MaxDepth
    {
        get => _maxDepth;
        init
        {
            if (value is <= 0)
            {
                throw new ArgumentOutOfRangeException(
                    nameof(MaxDepth), value, "Evaluation depth limit must be at least 1.");
            }

            _maxDepth = value;
        }
    }

    /// <summary>
    /// Maximum cumulative evaluation steps for one run, or <c>null</c> for no step
    /// budget (the default). One step is charged for each dynamic algorithm
    /// invocation and for each loop iteration.
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException">The value is zero or negative.</exception>
    public long? MaxSteps
    {
        get => _maxSteps;
        init
        {
            if (value is <= 0)
            {
                throw new ArgumentOutOfRangeException(
                    nameof(MaxSteps), value, "Evaluation step limit must be at least 1.");
            }

            _maxSteps = value;
        }
    }

    /// <summary>
    /// Default limits: the always-active hard depth, collection, string, and display
    /// ceilings apply. Step, cumulative collection, and cumulative string budgets are
    /// unconfigured.
    /// </summary>
    public static EvaluationLimits Default { get; } = new();

    /// <summary>
    /// Internal hard ceiling on the number of immediate item slots in ONE collection
    /// materialized by source evaluation, applied to every evaluation on every entry
    /// point regardless of configuration. <see cref="MaxCollectionItems"/> can only
    /// request a LOWER limit.
    ///
    /// <para>Unlike the step budget, this ceiling cannot be opt-in: a single compact
    /// expression such as <c>range(1, 10000000)</c> asks for one enormous allocation
    /// before any step or depth unit is charged, so default entry points need a finite
    /// bound to be process-safe.</para>
    ///
    /// <para>Calibrated by the process-isolated allocation probes (<c>eval-probe</c>,
    /// Windows/Release): a materialized collection costs roughly 190-200 bytes of peak
    /// working set per item, so 100,000 items is about 20 MB, and the worst measured
    /// temporary amplification (nested list construction, ~2.5x peak) still lands near
    /// 50 MB. The value is deliberately far below what this development machine
    /// survives (5,000,000 items = 916 MB): WASM and multi-tenant server embeddings have
    /// much smaller practical budgets. It leaves a 100x margin against the established
    /// <c>range(1, 10000000)</c> reproducer while staying far above the collection sizes
    /// realistic KatLang programs build.</para>
    /// </summary>
    public const int MaxSupportedCollectionItems = 100_000;

    private readonly int? _maxCollectionItems;
    private readonly long? _maxMaterializedItems;

    /// <summary>
    /// Maximum immediate item slots in one materialized sequence or exact list, or
    /// <c>null</c> to use <see cref="MaxSupportedCollectionItems"/>. Values above the
    /// supported maximum are clamped down to it rather than rejected, so raising the
    /// request can never weaken process safety.
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException">The value is zero or negative.</exception>
    public int? MaxCollectionItems
    {
        get => _maxCollectionItems;
        init
        {
            if (value is <= 0)
            {
                throw new ArgumentOutOfRangeException(
                    nameof(MaxCollectionItems), value, "Collection size limit must be at least 1.");
            }

            _maxCollectionItems = value;
        }
    }

    /// <summary>
    /// Maximum cumulative item slots materialized across one whole run, or <c>null</c>
    /// for no cumulative budget (the default). This bounds a program that repeatedly
    /// builds individually legal collections; it counts slots CREATED, and is therefore
    /// deliberately not a live-memory measure — a run that builds and discards many
    /// small collections still pays for each one.
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException">The value is zero or negative.</exception>
    public long? MaxMaterializedItems
    {
        get => _maxMaterializedItems;
        init
        {
            if (value is <= 0)
            {
                throw new ArgumentOutOfRangeException(
                    nameof(MaxMaterializedItems), value, "Materialization limit must be at least 1.");
            }

            _maxMaterializedItems = value;
        }
    }

    /// <summary>
    /// Internal hard ceiling on the length of ONE language string value
    /// (<see cref="Result.Str"/>) created by source evaluation, in UTF-16 code units.
    /// <see cref="MaxStringLength"/> can only request a lower limit.
    ///
    /// <para>KatLang has no string concatenation operator — <c>"a" + "b"</c> is a type
    /// error — so a source program cannot grow a string: the only producers are string
    /// literals (bounded by the source text) and <c>.string</c> on a number (about 30
    /// units). This ceiling therefore exists as defence in depth rather than to close a
    /// known compact-source path, and its practical effect is on hand-built ASTs supplied
    /// through the public <see cref="Evaluator"/> API, where an arbitrarily long
    /// <c>Expr.StringLiteral</c> is reachable. If a concatenating operation is ever added
    /// to the language, this is the ceiling it must charge against.</para>
    /// </summary>
    public const int MaxSupportedStringLength = 1_000_000;

    /// <summary>
    /// Internal hard ceiling on the length of ONE rendered display string, in UTF-16 code
    /// units, applied to every public rendering surface.
    /// <see cref="MaxDisplayLength"/> can only request a lower limit.
    ///
    /// <para>This is the string ceiling that closes a real compact-source path. Display
    /// flattens a value recursively, so a value that is legal under every evaluation limit
    /// can still render enormously: nesting a list inside itself
    /// (<c>B = [A, A]</c>, <c>C = [B, B]</c>, ...) adds two item slots per level while
    /// DOUBLING the rendered length, so a handful of lines can ask for gigabytes of text.
    /// A maximal legal collection renders well inside this ceiling — <c>range(1, 100000)</c>
    /// is about 689,000 units — while 1,000,000 units is roughly 2 MB of UTF-16 storage,
    /// which stays affordable for WASM and multi-tenant server embeddings.</para>
    /// </summary>
    public const int MaxSupportedDisplayLength = 1_000_000;

    private readonly int? _maxStringLength;
    private readonly long? _maxMaterializedStringChars;
    private readonly int? _maxDisplayLength;

    /// <summary>
    /// Maximum UTF-16 code units in one language string value, or <c>null</c> to use
    /// <see cref="MaxSupportedStringLength"/>. Values above the supported maximum are
    /// clamped down to it.
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException">The value is negative.</exception>
    public int? MaxStringLength
    {
        get => _maxStringLength;
        init
        {
            if (value is < 0)
            {
                throw new ArgumentOutOfRangeException(
                    nameof(MaxStringLength), value, "String length limit cannot be negative.");
            }

            _maxStringLength = value;
        }
    }

    /// <summary>
    /// Maximum cumulative UTF-16 code units stored in language string values across one
    /// run, or <c>null</c> for no cumulative budget (the default). Counts units CREATED,
    /// like <see cref="MaxMaterializedItems"/>, so it is not a live-memory measure.
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException">The value is negative.</exception>
    public long? MaxMaterializedStringChars
    {
        get => _maxMaterializedStringChars;
        init
        {
            if (value is < 0)
            {
                throw new ArgumentOutOfRangeException(
                    nameof(MaxMaterializedStringChars), value, "String materialization limit cannot be negative.");
            }

            _maxMaterializedStringChars = value;
        }
    }

    /// <summary>
    /// Maximum UTF-16 code units returned by one call to
    /// <see cref="RunResult.ToDisplayString"/> or
    /// <see cref="KatLangEngine.EvaluateToString(string, RunOptions)"/>, or <c>null</c>
    /// to use <see cref="MaxSupportedDisplayLength"/>. This applies to success, parse
    /// failure, evaluation failure, no-output text, and the overflow replacement itself.
    /// Values above the supported maximum are clamped down to it.
    /// </summary>
    /// <exception cref="ArgumentOutOfRangeException">The value is negative.</exception>
    public int? MaxDisplayLength
    {
        get => _maxDisplayLength;
        init
        {
            if (value is < 0)
            {
                throw new ArgumentOutOfRangeException(
                    nameof(MaxDisplayLength), value, "Display length limit cannot be negative.");
            }

            _maxDisplayLength = value;
        }
    }

    /// <summary>The depth limit actually enforced: the ceiling, or a lower configured value.</summary>
    internal int EffectiveMaxDepth
        => _maxDepth is { } depth && depth < MaxSupportedDepth ? depth : MaxSupportedDepth;

    /// <summary>The step limit actually enforced, or <c>null</c> when unbudgeted.</summary>
    internal long? EffectiveMaxSteps => _maxSteps;

    /// <summary>The single-collection limit actually enforced.</summary>
    internal int EffectiveMaxCollectionItems
        => _maxCollectionItems is { } items && items < MaxSupportedCollectionItems
            ? items
            : MaxSupportedCollectionItems;

    /// <summary>The cumulative materialization limit actually enforced, or <c>null</c>.</summary>
    internal long? EffectiveMaxMaterializedItems => _maxMaterializedItems;

    /// <summary>The single-string length limit actually enforced.</summary>
    internal int EffectiveMaxStringLength
        => _maxStringLength is { } length && length < MaxSupportedStringLength
            ? length
            : MaxSupportedStringLength;

    /// <summary>The cumulative string-materialization limit actually enforced, or <c>null</c>.</summary>
    internal long? EffectiveMaxMaterializedStringChars => _maxMaterializedStringChars;

    /// <summary>The rendered-output limit actually enforced.</summary>
    internal int EffectiveMaxDisplayLength
        => _maxDisplayLength is { } length && length < MaxSupportedDisplayLength
            ? length
            : MaxSupportedDisplayLength;
}
