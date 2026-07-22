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

        return (testCase.SemanticRelation switch
        {
            MetamorphicSemanticRelation.SemanticEqual => CompareSemanticEqual(left.Semantic, right.Semantic),
            _ => throw new MetamorphicHarnessException(
                $"No comparison is implemented for semantic relation {testCase.SemanticRelation}."),
        })
        ?? testCase.OperationalRelation switch
        {
            MetamorphicOperationalRelation.ExactMaterializationEqual => CompareExactMaterializationEqual(left, right),
            _ => throw new MetamorphicHarnessException(
                $"No comparison is implemented for operational relation {testCase.OperationalRelation}."),
        };
    }

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

    private static string Flag(bool value) => value ? "resource-limit" : "language-semantic";

    private static string Text(string? value) => value ?? "-";

    private static string Number(long value) => value.ToString(CultureInfo.InvariantCulture);

    private static string Number(int? value) => value?.ToString(CultureInfo.InvariantCulture) ?? "-";
}
