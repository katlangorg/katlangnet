namespace KatLang;

/// <summary>
/// Passive, operation-scoped observer of exact pattern-equivalence comparisons. One instance belongs
/// to ONE measured operation — a single parse, or a single indexed clause-family duplicate check — and
/// is passed explicitly to <see cref="Pattern.CreateMatchEquivalenceComparer"/> so the comparer records
/// one comparison per <see cref="Pattern.IsMatchEquivalent"/> call it performs. It is never static and
/// never ambient: a production comparer carries no observer, separate parses never share one, and
/// concurrent parses each own their own, so a count can never leak across operations, runs, or threads.
/// A fresh instance starts at zero by construction, so no reset logic exists or is required.
///
/// <para>Internal and excluded from every public API; the count is a C# implementation observation
/// used only by scaling regressions, with no semantic meaning.</para>
/// </summary>
internal sealed class PatternComparisonObservations
{
    /// <summary>
    /// Number of exact <see cref="Pattern.IsMatchEquivalent"/> equality checks performed through the
    /// comparer(s) this observer owns. Hash computations and dictionary bucket probes do not count;
    /// only a real exact comparison (a hash-bucket collision, or a genuine duplicate) does. For a
    /// family of distinct clauses this stays O(clauses); the former all-pairs scan was O(clauses^2).
    /// </summary>
    public long MatchEquivalenceComparisonCount { get; private set; }

    internal void RecordExactComparison()
        => MatchEquivalenceComparisonCount = checked(MatchEquivalenceComparisonCount + 1);
}
