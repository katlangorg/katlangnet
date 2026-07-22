using KatLang;
using KatLang.Evaluation.Caching;

namespace KatLang.ParserFuzz;

/// <summary>
/// Thrown when the harness itself is broken (an observation changed the run it observed, an
/// unregistered family reached execution, ...). Distinct from a metamorphic MISMATCH: this
/// says the measuring apparatus is untrustworthy, not that the language is wrong.
/// </summary>
internal sealed class MetamorphicHarnessException(string message) : Exception(message);

/// <summary>The result of running one case's pair: accepted with both observations, or rejected.</summary>
internal sealed record MetamorphicExecution(
    MetamorphicCase Case,
    bool Accepted,
    string RejectionReason,
    MetamorphicOperationalObservation? Left,
    MetamorphicOperationalObservation? Right);

/// <summary>
/// Executes both members of a metamorphic pair with fully independent run state.
///
/// <para>Isolation is by construction, not by cleanup. Each side re-parses its OWN source, so
/// no front-end state crosses; <c>Evaluator.RunCountedObserved</c> creates that side's
/// <c>EvaluationBudget</c>, so the counters cannot be shared or reset; and each side gets a
/// freshly allocated zero-argument property cache. The one thing the two sides DO share is the
/// immutable <see cref="EvaluationLimits"/> instance — deliberately, because "a reused limits
/// object must not carry counters" is exactly the property this executor should be exercising.
/// There is no static mutable state anywhere in this harness.</para>
///
/// <para>Observation reuses the real run-scoped budget the evaluator charged. It never
/// re-evaluates, never rebuilds a value, and is checked afterwards to have left every counter
/// untouched.</para>
/// </summary>
internal static class MetamorphicExecutor
{
    /// <summary>An unrelated program used to prove one run cannot influence the next.</summary>
    internal const string IsolationProbeSource = "V = range(1, 7)\nOutput = V.count + V.sum + V.count";

    internal static MetamorphicExecution Execute(MetamorphicCase testCase)
    {
        ArgumentNullException.ThrowIfNull(testCase);

        if (!testCase.Precondition.Satisfied)
            return new MetamorphicExecution(testCase, false, testCase.Precondition.Reason, null, null);

        // Left first, then right, each from a clean start.
        if (!TryObserve(testCase.LeftSource, testCase.Limits, testCase.EnableOptimizations, out var left, out var leftReason))
            return new MetamorphicExecution(testCase, false, "left-" + leftReason, null, null);

        if (!TryObserve(testCase.RightSource, testCase.Limits, testCase.EnableOptimizations, out var right, out var rightReason))
            return new MetamorphicExecution(testCase, false, "right-" + rightReason, left, null);

        return new MetamorphicExecution(testCase, true, "ok", left, right);
    }

    /// <summary>
    /// Runs ONE program with fresh state and reports what it produced and what it charged.
    /// Returns <c>false</c> only for a template precondition failure (the trusted template
    /// generated source the front end rejects); every unexpected exception escapes.
    /// </summary>
    internal static bool TryObserve(
        string source,
        EvaluationLimits? limits,
        bool enableOptimizations,
        out MetamorphicOperationalObservation observation,
        out string reason)
    {
        ArgumentNullException.ThrowIfNull(source);

        var parsed = Parser.Parse(source);
        if (parsed.HasErrors)
        {
            observation = null!;
            reason = "parse-error";
            return false;
        }

        var (result, budget) = Evaluator.RunCountedObserved(
            new Expr.Block(parsed.Root),
            limits,
            enableOptimizations,
            new RunScopedZeroArgPropertyResultCache());

        // Snapshot the run's own counters BEFORE encoding anything, so no later read can be
        // mistaken for work the run performed.
        var steps = budget.ConsumedSteps;
        var materializedItems = budget.MaterializedItems;
        var materializedStringChars = budget.MaterializedStringChars;
        var peakDepth = budget.PeakDepth;

        var semantic = result.IsError
            ? MetamorphicSemanticObservation.Failure(
                MetamorphicValue.ErrorCategory(result.Error),
                MetamorphicValue.ErrorPayload(result.Error),
                result.Error.IsResourceLimit)
            : MetamorphicSemanticObservation.Success(
                MetamorphicValue.Neutral(result.Value.Value),
                result.Value.EmittedCount);

        // Purity: encoding the outcome must not have charged the run it describes.
        if (budget.ConsumedSteps != steps
            || budget.MaterializedItems != materializedItems
            || budget.MaterializedStringChars != materializedStringChars
            || budget.PeakDepth != peakDepth)
        {
            throw new MetamorphicHarnessException(
                "Observing a completed run changed its budget counters; the operational observation is not a pure read.");
        }

        observation = new MetamorphicOperationalObservation(
            semantic,
            steps,
            materializedItems,
            materializedStringChars,
            peakDepth,
            enableOptimizations ? "on" : "off");
        reason = "ok";
        return true;
    }

    /// <summary>
    /// A/B/A state-isolation check for the executor: observe <paramref name="source"/>,
    /// observe an unrelated program, observe <paramref name="source"/> again. The two
    /// observations of the same program must be identical, counters included.
    /// </summary>
    internal static void AssertIsolated(string source, EvaluationLimits? limits, bool enableOptimizations)
    {
        if (!TryObserve(source, limits, enableOptimizations, out var first, out var reason)) return;

        _ = TryObserve(IsolationProbeSource, null, enableOptimizations, out _, out _);

        if (!TryObserve(source, limits, enableOptimizations, out var second, out _) || first != second)
        {
            throw new MetamorphicHarnessException(
                "A/B/A isolation failed: an unrelated evaluation changed a later observation of the same program.\n" +
                $"  source: {source.Replace("\n", "\\n", StringComparison.Ordinal)}\n" +
                $"  reason: {reason}\n" +
                $"  first:  {first}\n" +
                $"  second: {second}");
        }
    }
}
