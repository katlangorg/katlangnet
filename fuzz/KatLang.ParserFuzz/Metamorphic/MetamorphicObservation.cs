using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>
/// LANGUAGE-SEMANTIC identity of one run: the class of observation the Lean differential
/// corpus compares, plus the host-policy flag that keeps a resource-limit failure
/// distinguishable from an ordinary language-semantic failure.
/// </summary>
internal sealed record MetamorphicSemanticObservation(
    string Outcome,             // "ok" | "err"
    string? Structure,          // neutral structural value (ok only)
    int? EmittedCount,          // root emitted count (ok only)
    string? ErrorCategory,      // innermost structured error kind (err only)
    string? ErrorPayload,       // stable numeric payload where supported (err only)
    bool IsResourceLimit)       // host resource policy, never a language-semantic fact
{
    public static MetamorphicSemanticObservation Success(string structure, int emittedCount)
        => new("ok", structure, emittedCount, null, null, false);

    public static MetamorphicSemanticObservation Failure(string category, string? payload, bool isResourceLimit)
        => new("err", null, null, category, payload, isResourceLimit);

    public override string ToString() => Outcome == "ok"
        ? $"ok value={Structure} emitted={EmittedCount?.ToString(CultureInfo.InvariantCulture)}"
        : $"err kind={ErrorCategory} payload={ErrorPayload ?? "-"} resourceLimit={(IsResourceLimit ? "yes" : "no")}";
}

/// <summary>
/// OPERATIONAL counters one run charged, read from the run's own
/// <see cref="KatLang.Evaluation.EvaluationBudget"/>. These are C# implementation
/// observations: they may be compared between C# executions and are never compared with
/// Lean, which models an unbounded evaluator with no notion of work.
///
/// <para><see cref="EvaluationSteps"/> and <see cref="PeakDynamicDepth"/> are carried for
/// DIAGNOSTICS only. Phase 1's operational relation does not fail on them, because the
/// repository's established contract for the dotted/ordinary pair asserts materialization
/// equality and does not claim the two forms share one definition of a "step".</para>
/// </summary>
internal sealed record MetamorphicOperationalObservation(
    MetamorphicSemanticObservation Semantic,
    long EvaluationSteps,
    long MaterializedItems,
    long MaterializedStringChars,
    int PeakDynamicDepth,
    string OptimizerPolicy)
{
    public override string ToString() =>
        $"{Semantic} | steps={EvaluationSteps.ToString(CultureInfo.InvariantCulture)} " +
        $"materializedItems={MaterializedItems.ToString(CultureInfo.InvariantCulture)} " +
        $"materializedStringChars={MaterializedStringChars.ToString(CultureInfo.InvariantCulture)} " +
        $"peakDepth={PeakDynamicDepth.ToString(CultureInfo.InvariantCulture)} optimizer={OptimizerPolicy}";
}
