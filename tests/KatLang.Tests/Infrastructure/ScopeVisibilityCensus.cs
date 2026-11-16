using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Passive structural census of a model's scope visibility storage: logical memberships versus the
/// distinct physical objects that back them. Test-only (it reads the storage through the friend
/// assembly); the production assembly carries no census.
/// </summary>
internal static class ScopeVisibilityCensus
{
    internal readonly record struct Report(
        int Scopes,
        long Memberships,
        int Wrappers,
        int Views,
        int Roots,
        int Nodes,
        int Symbols,
        int MaxTreeDepth);

    public static Report Measure(IReadOnlyList<ScopeVisibility> scopes)
    {
        long memberships = 0;
        var wrappers = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var views = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var roots = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var nodes = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var symbols = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var heights = new Dictionary<VisibilityNode, int>(ReferenceEqualityComparer.Instance);
        var maxDepth = 0;
        foreach (var scope in scopes)
        {
            memberships += scope.Symbols.Count;
            wrappers.Add(scope.Symbols);
            if (scope.View is not { } view)
            {
                foreach (var symbol in scope.Symbols)
                    symbols.Add(symbol);
                continue;
            }

            views.Add(view);
            if (view.Root is not { } root || !roots.Add(root))
                continue;

            // A shared subtree may occur at different depths in different roots. Memoize
            // its HEIGHT, not the first root-relative depth at which the census saw it.
            var heightWork = new Stack<(VisibilityNode Node, bool ChildrenDone)>();
            heightWork.Push((root, false));
            while (heightWork.TryPop(out var work))
            {
                if (heights.ContainsKey(work.Node))
                    continue;
                if (work.ChildrenDone)
                {
                    heights.Add(work.Node, 1 + Math.Max(
                        work.Node.Left is { } l ? heights[l] : 0,
                        work.Node.Right is { } r ? heights[r] : 0));
                    continue;
                }
                heightWork.Push((work.Node, true));
                if (work.Node.Left is { } leftChild)
                    heightWork.Push((leftChild, false));
                if (work.Node.Right is { } rightChild)
                    heightWork.Push((rightChild, false));
            }
            maxDepth = Math.Max(maxDepth, heights[root]);

            var pending = new Stack<(VisibilityNode Node, int Depth)>();
            pending.Push((root, 1));
            while (pending.TryPop(out var item))
            {
                if (!nodes.Add(item.Node))
                    continue;
                symbols.Add(item.Node.Symbol);
                if (item.Node.DeferredTwin is { } twin)
                    symbols.Add(twin);
                if (item.Node.Left is { } left)
                    pending.Push((left, item.Depth + 1));
                if (item.Node.Right is { } right)
                    pending.Push((right, item.Depth + 1));
            }
        }

        return new Report(scopes.Count, memberships, wrappers.Count, views.Count, roots.Count, nodes.Count, symbols.Count, maxDepth);
    }

    /// <summary>The nodes a name lookup visits in <paramref name="scope"/>'s tree (0 for a host-built scope).</summary>
    public static int LookupProbes(ScopeVisibility scope, string name)
    {
        _ = VisibilityTree.Find(scope.View?.Root, name, out _, out var probes);
        return probes;
    }
}
