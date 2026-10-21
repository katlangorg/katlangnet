namespace KatLang;

/// <summary>
/// Passive, operation-scoped observer of clause-family duplicate-detection work. One instance belongs
/// to ONE measured operation — a single parse (every family index it builds), or a single indexed
/// duplicate check — and is passed explicitly to <see cref="PatternMatchEquivalenceIndex"/>, so the
/// index records the work it performs. It is never static and never ambient: a production index
/// carries no observer, separate parses never share one, and concurrent parses each own their own, so
/// a count can never leak across operations, runs, or threads. A fresh instance starts at zero by
/// construction, so no reset logic exists or is required.
///
/// <para>Internal and excluded from every public API; the counts are C# implementation observations
/// used only by scaling, security (SEC-03), and cancellation regressions, with no semantic
/// meaning.</para>
/// </summary>
internal sealed class PatternComparisonObservations
{
    /// <summary>Canonical match-equivalence keys built (one per indexed pattern).</summary>
    public long CanonicalKeyCount { get; private set; }

    /// <summary>Total code units of the canonical keys built (writing work).</summary>
    public long CanonicalKeyUnits { get; private set; }

    /// <summary>Pattern nodes and structural cursors visited by the iterative walk.</summary>
    public long TraversalUnits { get; private set; }

    /// <summary>Code units copied when materializing completed canonical keys.</summary>
    public long KeyCopyUnits { get; private set; }

    /// <summary>Binder-name input units (names are erased from the resulting key).</summary>
    public long BinderNameUnits { get; private set; }

    /// <summary>Ordered binder-map comparisons, independent of any hashing.</summary>
    public long BinderComparisonCount { get; private set; }

    /// <summary>Upper bound of the code units examined by ordered binder-map comparisons.</summary>
    public long BinderComparisonUnits { get; private set; }

    /// <summary>Ordinal key comparisons performed by the ordered index.</summary>
    public long KeyComparisonCount { get; private set; }

    /// <summary>
    /// Upper bound of the code units the key comparisons examined: each comparison is charged the
    /// shorter key's length plus one, which bounds where an ordinal comparison stops.
    /// </summary>
    public long KeyComparisonUnits { get; private set; }

    /// <summary>
    /// Total duplicate-index work, including traversal, writing/copying, binder names and both ordered
    /// indexes. For N clauses, total key size S, binder-name size T and at most B names per head, the
    /// bound is O(S log(N + 1) + T log(B + 1)); literal-only families have T = 0.
    /// </summary>
    public long TotalIndexWork => CanonicalKeyUnits + KeyComparisonUnits + TraversalUnits + KeyCopyUnits
        + BinderNameUnits + BinderComparisonUnits;

    /// <summary>Cancellation observations per insertion and within traversal, copying and comparisons.</summary>
    public long CancellationCheckpointCount { get; private set; }

    /// <summary>
    /// Test-only hook invoked at every cancellation checkpoint, BEFORE the tokens are observed, with the
    /// checkpoint's ordinal (1-based). A cancellation test cancels its own token source here to place a
    /// cancellation deterministically inside duplicate detection; it belongs to this one operation.
    /// </summary>
    public Action<long>? CheckpointReached { get; init; }

    internal void RecordCanonicalKey(int units)
    {
        CanonicalKeyCount = checked(CanonicalKeyCount + 1);
        CanonicalKeyUnits = checked(CanonicalKeyUnits + units);
    }

    internal void RecordKeyComparison(int units)
    {
        KeyComparisonCount = checked(KeyComparisonCount + 1);
        KeyComparisonUnits = checked(KeyComparisonUnits + units);
    }

    internal void RecordTraversal() => TraversalUnits = checked(TraversalUnits + 1);

    internal void RecordKeyCopy(int units) => KeyCopyUnits = checked(KeyCopyUnits + units);

    internal void RecordBinderName(int units) => BinderNameUnits = checked(BinderNameUnits + units);

    internal void RecordBinderComparison(int units)
    {
        BinderComparisonCount = checked(BinderComparisonCount + 1);
        BinderComparisonUnits = checked(BinderComparisonUnits + units);
    }

    internal void RecordCancellationCheckpoint()
    {
        CancellationCheckpointCount = checked(CancellationCheckpointCount + 1);
        CheckpointReached?.Invoke(CancellationCheckpointCount);
    }
}
