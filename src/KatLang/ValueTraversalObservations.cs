namespace KatLang;

/// <summary>
/// Passive, operation-scoped observer of structural <see cref="Result"/> value traversals. One
/// instance belongs to ONE measured sequence of value operations and is passed explicitly to
/// <see cref="Result.CreateObservedValueComparer"/>, so the comparer it produces records the
/// structural work its own equality and hash walks perform. It is never static and never ambient:
/// the production <see cref="Result.ValueComparer"/> carries no observer and records nothing, so a
/// count can never leak across operations, runs, or threads.
///
/// <para>Internal and excluded from every public API; the counts are C# implementation observations
/// with no semantic meaning, used only by the shared-value-graph complexity regressions. A fresh
/// instance starts at zero by construction, so no reset logic exists or is required.</para>
///
/// <para>This is the same operation-scoped observation shape as
/// <see cref="PatternComparisonObservations"/> (parser/clause-family comparisons) and the run-scoped
/// <c>EvaluationObservations</c>: created by the measuring caller, mutated only through
/// <c>Record*</c> methods, and read afterwards.</para>
/// </summary>
internal sealed class ValueTraversalObservations
{
    /// <summary>
    /// Number of collection PAIRS structurally expanded across the equality comparisons this
    /// observer's comparer performed — one increment per pair whose element sequences were actually
    /// walked (the top-level pair of one comparison, plus every nested pair descended into).
    /// The reference fast path, leaf comparisons, count/kind mismatches, empty collections, and
    /// memo hits on an already-expanded pair record nothing, so for ONE top-level comparison this
    /// stays bounded by the number of distinct reachable <c>(leftReference, rightReference)</c>
    /// pairs — never the number of expanded tree paths.
    /// </summary>
    public long EqualityPairExpansionCount { get; private set; }

    internal void RecordEqualityPairExpansion()
        => EqualityPairExpansionCount = checked(EqualityPairExpansionCount + 1);

    /// <summary>
    /// Number of collection NODES structurally expanded across the hash computations this observer's
    /// comparer performed: the top-level collection of each hash, plus every nested NON-EMPTY
    /// collection descended into. Leaves and nested empty collections are hashed in place and record
    /// nothing, and a node reached again through a second shared reference reuses its memoized hash,
    /// so for ONE top-level hash this stays bounded by the number of distinct reachable collection
    /// nodes — never the number of expanded tree paths. The memo lives for exactly one top-level
    /// hash, so hashing the same value twice observes twice the count.
    /// </summary>
    public long HashStructureExpansionCount { get; private set; }

    internal void RecordHashStructureExpansion()
        => HashStructureExpansionCount = checked(HashStructureExpansionCount + 1);
}
