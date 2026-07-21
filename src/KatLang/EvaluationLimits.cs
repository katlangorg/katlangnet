namespace KatLang;

/// <summary>
/// Deterministic, run-scoped resource limits for KatLang evaluation.
///
/// <para>Two independent limits are modelled, and they are deliberately NOT one number:</para>
/// <list type="bullet">
///   <item><b>Depth</b> (<see cref="MaxDepth"/>) bounds how many dynamic algorithm
///   invocations may be active at once. Its purpose is host-stack safety.</item>
///   <item><b>Steps</b> (<see cref="MaxSteps"/>) bounds the cumulative amount of
///   semantic work one run may perform. Its purpose is stopping unbounded or
///   excessive computation such as a non-terminating loop.</item>
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
    /// Default limits: the internal depth ceiling applies and there is no step budget.
    /// </summary>
    public static EvaluationLimits Default { get; } = new();

    /// <summary>The depth limit actually enforced: the ceiling, or a lower configured value.</summary>
    internal int EffectiveMaxDepth
        => _maxDepth is { } depth && depth < MaxSupportedDepth ? depth : MaxSupportedDepth;

    /// <summary>The step limit actually enforced, or <c>null</c> when unbudgeted.</summary>
    internal long? EffectiveMaxSteps => _maxSteps;
}
