namespace KatLang.Tests;

/// <summary>
/// The summary channel of a tree no exposure run is processing. Every summary is computed in the completed
/// structural context of the tree it summarizes (the summary channel has no contextless mode), so a test that
/// reads a summary graph directly supplies the one a standalone analysis gives:
/// <see cref="AnalyzedStaticStructures.ForBoundAst"/>, a published tree's own context or a fresh analysis of a
/// host-built one. The context is built BEFORE the summary walk, so a test can measure the walk alone.
/// </summary>
internal static class StandaloneSummaries
{
    /// <summary>
    /// The summary graph of <paramref name="root"/> in its own completed context. With no <paramref name="memo"/> the
    /// walk gets the memo an exposure run gives it (<see cref="MemoFor"/>).
    /// </summary>
    internal static PropertyDependencySummaryGraph Build(
        Algorithm root,
        PropertyDependencyGraphBuilder.SummaryMemo? memo = null,
        FrontEndTraversalObservations? observations = null)
        => PropertyDependencyGraphBuilder.BuildSummaries(root, AnalyzedStaticStructures.ForBoundAst(root),
            memo ?? MemoFor(root, observations), observations);

    /// <summary>
    /// The summary memo of one exposure resolution of <paramref name="root"/>: it carries the census of the bodies
    /// the tree reaches through several paths, which is what lets every occurrence of a shared body below one
    /// representative context be summarized once.
    /// </summary>
    internal static PropertyDependencyGraphBuilder.SummaryMemo MemoFor(Algorithm root, FrontEndTraversalObservations? observations = null)
        => new(observations) { SharedBodies = SharedBodyCensus.Of(root) };

    /// <summary>
    /// The sibling equations the summary of property <paramref name="propertyIndex"/> statically reads, in index
    /// order: the sibling edges of its raw rows, and every lexical reference whose head the level declares. These are
    /// the read edges the exposure level solver orders its equations by. A name written inside a nested body escapes
    /// that body anchored at its completed context, so it reaches the level as such a reference, never as a bare edge.
    /// </summary>
    internal static int[] SiblingReads(PropertyDependencySummaryGraph graph, int propertyIndex)
    {
        var node = graph[propertyIndex];
        var reads = new SortedSet<int>(node.SummarySiblingDependencyIndices);
        foreach (var reference in node.PendingReferences)
            if (reference.Selection == PendingSelection.Lexical && graph.TryGetPropertyIndex(reference.Head, out var read)
                && read != propertyIndex)
                reads.Add(read);
        foreach (var name in node.SummaryVisiblePropertyDependencyNames)
            if (graph.TryGetPropertyIndex(name, out var read) && read != propertyIndex)
                reads.Add(read);
        return [.. reads];
    }
}
