using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>Which declared relation a mismatch violated.</summary>
internal enum MetamorphicMismatchClass
{
    /// <summary>The language-semantic relation (what the program means).</summary>
    Semantic,

    /// <summary>The resource-limit verdict (host policy: did the run stop for a budget?).</summary>
    ResourceBoundary,

    /// <summary>The operational relation (how much work the run charged).</summary>
    Operational,
}

/// <summary>The exact comparison that failed. One kind per compared field, so a diagnostic
/// can name the property rather than dumping two opaque observations.</summary>
internal enum MetamorphicMismatchKind
{
    SemanticOutcome,
    ResourceLimitVerdict,
    SemanticErrorCategory,
    SemanticErrorPayload,
    SemanticStructure,
    EmittedCount,
    MaterializedItems,
    MaterializedStringChars,
    EvaluationSteps,
    PeakDynamicDepth,
}

/// <summary>One failed comparison, with the two values that failed it.</summary>
internal sealed record MetamorphicMismatch(
    MetamorphicMismatchKind Kind,
    MetamorphicMismatchClass Class,
    string ComparedProperty,
    string LeftValue,
    string RightValue)
{
    public string Headline =>
        $"{Class} relation violated on {ComparedProperty}: left={LeftValue} right={RightValue}";
}

/// <summary>
/// Compares one executed pair against the relations its case DECLARED.
///
/// <para>The order is chosen so the reported kind is the most specific true statement about
/// the difference: an ok/err split is an outcome mismatch, two errors that differ only in
/// whether a resource budget stopped them is a resource-boundary mismatch, and only once the
/// semantic halves agree do the operational counters get the blame.</para>
///
/// <para><b>Operational counters are compared only when both executions complete.</b> When
/// either side stops at a structured resource limit, semantic outcome, resource-limit kind, and
/// structured payload remain comparable, but partial work counters are not
/// (<see cref="WorkIsComparable"/>). An ordinary, non-resource semantic failure is not exempt:
/// its counters are compared exactly like a successful run's.</para>
/// </summary>
internal static class MetamorphicComparator
{
    /// <summary>Returns the first violated comparison, or <c>null</c> when every declared relation holds.</summary>
    internal static MetamorphicMismatch? Compare(
        MetamorphicCase testCase,
        MetamorphicOperationalObservation left,
        MetamorphicOperationalObservation right)
    {
        ArgumentNullException.ThrowIfNull(testCase);
        ArgumentNullException.ThrowIfNull(left);
        ArgumentNullException.ThrowIfNull(right);

        var semantic = testCase.SemanticRelation switch
        {
            MetamorphicSemanticRelation.SemanticEqual => CompareSemanticEqual(left.Semantic, right.Semantic),
            _ => throw new MetamorphicHarnessException(
                $"No comparison is implemented for semantic relation {testCase.SemanticRelation}."),
        };

        if (semantic is not null) return semantic;

        // Operational counters are only meaningful for runs that COMPLETED. When a resource
        // limit stops a run, its counters are a PARTIAL PREFIX recorded at the abort point, and
        // two equivalent forms may legitimately have done different preparatory work before
        // reaching the same limit — `reduce(R, contains, [1, 2])` materializes its initial
        // accumulator before forcing R, while `R.reduce(contains, [1, 2])` prepares the receiver
        // first and fails earlier. The semantic relation above has already established that both
        // sides report the same error kind and the same structured payload, which is what a
        // program can actually observe; measured over the whole builtin x receiver x
        // (item budget x string budget) grid, no observable outcome ever differed, and no pair of
        // SUCCESSFUL runs ever differed on counters.
        if (!WorkIsComparable(left, right)) return null;

        return testCase.OperationalRelation switch
        {
            MetamorphicOperationalRelation.ExactMaterializationEqual => CompareExactMaterializationEqual(left, right),
            MetamorphicOperationalRelation.ExactObservedWorkEqual =>
                CompareExactMaterializationEqual(left, right) ?? CompareObservedWork(left, right),
            MetamorphicOperationalRelation.MaterializationNeverIncreases =>
                CompareMaterializationNeverIncreases(left, right),
            _ => throw new MetamorphicHarnessException(
                $"No comparison is implemented for operational relation {testCase.OperationalRelation}."),
        };
    }

    /// <summary>
    /// True when both runs finished under their budgets, so their counters describe the WHOLE
    /// work each form performed rather than the prefix that happened to precede an abort.
    /// </summary>
    internal static bool WorkIsComparable(
        MetamorphicOperationalObservation left, MetamorphicOperationalObservation right)
        => !left.Semantic.IsResourceLimit && !right.Semantic.IsResourceLimit;

    private static MetamorphicMismatch? CompareSemanticEqual(
        MetamorphicSemanticObservation left, MetamorphicSemanticObservation right)
    {
        if (!string.Equals(left.Outcome, right.Outcome, StringComparison.Ordinal))
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.SemanticOutcome, MetamorphicMismatchClass.Semantic,
                "success/failure outcome", left.Outcome, right.Outcome);
        }

        // A resource-limit stop is host policy, not a language-semantic fact, so it is kept
        // distinguishable from an ordinary semantic failure with its own mismatch kind.
        if (left.IsResourceLimit != right.IsResourceLimit)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.ResourceLimitVerdict, MetamorphicMismatchClass.ResourceBoundary,
                "resource-limit verdict", Flag(left.IsResourceLimit), Flag(right.IsResourceLimit));
        }

        if (!string.Equals(left.ErrorCategory, right.ErrorCategory, StringComparison.Ordinal))
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.SemanticErrorCategory,
                left.IsResourceLimit ? MetamorphicMismatchClass.ResourceBoundary : MetamorphicMismatchClass.Semantic,
                "innermost error kind", Text(left.ErrorCategory), Text(right.ErrorCategory));
        }

        if (!string.Equals(left.ErrorPayload, right.ErrorPayload, StringComparison.Ordinal))
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.SemanticErrorPayload,
                left.IsResourceLimit ? MetamorphicMismatchClass.ResourceBoundary : MetamorphicMismatchClass.Semantic,
                "structured error payload", Text(left.ErrorPayload), Text(right.ErrorPayload));
        }

        if (!string.Equals(left.Structure, right.Structure, StringComparison.Ordinal))
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.SemanticStructure, MetamorphicMismatchClass.Semantic,
                "neutral structural value", Text(left.Structure), Text(right.Structure));
        }

        if (left.EmittedCount != right.EmittedCount)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.EmittedCount, MetamorphicMismatchClass.Semantic,
                "emitted count", Number(left.EmittedCount), Number(right.EmittedCount));
        }

        return null;
    }

    /// <summary>
    /// Exact equality of what the two runs MATERIALIZED. Evaluation steps and peak dynamic
    /// depth are deliberately not compared: they are carried on the observation for
    /// diagnostics, but Phase 1 claims only that the two spellings of one call construct the
    /// same collection storage, which is the claim the repository's dotted-receiver contract
    /// actually establishes.
    /// </summary>
    private static MetamorphicMismatch? CompareExactMaterializationEqual(
        MetamorphicOperationalObservation left, MetamorphicOperationalObservation right)
    {
        if (left.MaterializedItems != right.MaterializedItems)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.MaterializedItems, MetamorphicMismatchClass.Operational,
                "materialized collection-item slots", Number(left.MaterializedItems), Number(right.MaterializedItems));
        }

        if (left.MaterializedStringChars != right.MaterializedStringChars)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.MaterializedStringChars, MetamorphicMismatchClass.Operational,
                "materialized string UTF-16 units",
                Number(left.MaterializedStringChars), Number(right.MaterializedStringChars));
        }

        return null;
    }

    /// <summary>
    /// The DIRECTIONAL materialization relation: the right member may charge less (it is the
    /// fusion-eligible spelling) but never more. Doing more work than the equivalent ordinary
    /// form is never a legitimate implementation choice.
    /// </summary>
    private static MetamorphicMismatch? CompareMaterializationNeverIncreases(
        MetamorphicOperationalObservation left, MetamorphicOperationalObservation right)
    {
        if (right.MaterializedItems > left.MaterializedItems)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.MaterializedItems, MetamorphicMismatchClass.Operational,
                "materialized collection-item slots (right must never exceed left)",
                Number(left.MaterializedItems), Number(right.MaterializedItems));
        }

        if (right.MaterializedStringChars > left.MaterializedStringChars)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.MaterializedStringChars, MetamorphicMismatchClass.Operational,
                "materialized string UTF-16 units (right must never exceed left)",
                Number(left.MaterializedStringChars), Number(right.MaterializedStringChars));
        }

        return null;
    }

    /// <summary>
    /// The additional counters an EXACT-WORK family claims. Declared only where the two members
    /// resolve to the same invocations, so a difference here means one form performed work the
    /// other did not — never a legitimate implementation choice.
    /// </summary>
    private static MetamorphicMismatch? CompareObservedWork(
        MetamorphicOperationalObservation left, MetamorphicOperationalObservation right)
    {
        if (left.EvaluationSteps != right.EvaluationSteps)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.EvaluationSteps, MetamorphicMismatchClass.Operational,
                "evaluation steps", Number(left.EvaluationSteps), Number(right.EvaluationSteps));
        }

        if (left.PeakDynamicDepth != right.PeakDynamicDepth)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.PeakDynamicDepth, MetamorphicMismatchClass.Operational,
                "peak dynamic depth", Number(left.PeakDynamicDepth), Number(right.PeakDynamicDepth));
        }

        return null;
    }

    private static string Flag(bool value) => value ? "resource-limit" : "language-semantic";

    private static string Text(string? value) => value ?? "-";

    private static string Number(long value) => value.ToString(CultureInfo.InvariantCulture);

    private static string Number(int value) => value.ToString(CultureInfo.InvariantCulture);

    private static string Number(int? value) => value?.ToString(CultureInfo.InvariantCulture) ?? "-";
}
