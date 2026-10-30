using System.Diagnostics;
using KatLang.Semantics;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// SCOPE-BAL-3 (issue #169): <see cref="VisibilityTreeBuilder.Set"/>, <see cref="VisibilityTreeBuilder.Remove"/>
/// and the join they share are iterative. The differential half replays every operation through
/// <see cref="RecursiveReference"/> — the pre-SCOPE-BAL-3 recursive algorithms, verbatim over the
/// public <see cref="VisibilityTreeBuilder.Make"/> — at safe heights and requires the same trees and
/// the same <see cref="VisibilityTreeBuilder.Make"/> creation/reuse counts (identical counters
/// after every step; in one builder, the iterative result is the very node the reference built and
/// creates nothing). The process half updates 100,000-level trees on a 256 KiB thread stack in a
/// child process, so a regression to depth-proportional recursion kills only the child.
/// </summary>
public class ScopeVisibilityIterativeUpdateTests(ITestOutputHelper output)
{
    private const string ProbeChildEnvironment = "KATLANG_SCOPE_DEEP_PROBE_CHILD";
    private const string ProbeMarkerFileEnvironment = "KATLANG_SCOPE_DEEP_PROBE_MARKER_FILE";
    private const string ProbeLogFileEnvironment = "KATLANG_SCOPE_DEEP_PROBE_LOG_FILE";
    private const string ProbeSuccessMarker = "katlang-scope-deep-update-ok";
    private const int SmallStackBytes = 256 * 1024;
    private const int DeepLevels = 100_000;

    /// <summary>A name above every <see cref="Name"/>: the end of every chain.</summary>
    private const string Extra = "n9999999";

    /// <summary>The recursive Set/Remove/Merge as they were before SCOPE-BAL-3, kept as the bounded-height oracle.</summary>
    private static class RecursiveReference
    {
        public static VisibilityNode Set(VisibilityTreeBuilder trees, VisibilityNode? node, in VisibilityEntry entry)
        {
            if (node is null)
                return trees.Make(entry, null, null);

            var comparison = string.CompareOrdinal(entry.Name, node.Name);
            if (comparison == 0)
            {
                return SameEntry(node, entry)
                    ? node
                    : trees.Make(entry, node.Left, node.Right);
            }

            if (comparison < 0)
            {
                var left = Set(trees, node.Left, entry);
                if (ReferenceEquals(left, node.Left))
                    return node;

                return VisibilityTree.HigherPriority(left.Priority, left.Name, node.Priority, node.Name)
                    ? trees.Make(new VisibilityEntry(left), left.Left, trees.Make(new VisibilityEntry(node), left.Right, node.Right))
                    : trees.Make(new VisibilityEntry(node), left, node.Right);
            }

            var right = Set(trees, node.Right, entry);
            if (ReferenceEquals(right, node.Right))
                return node;

            return VisibilityTree.HigherPriority(right.Priority, right.Name, node.Priority, node.Name)
                ? trees.Make(new VisibilityEntry(right), trees.Make(new VisibilityEntry(node), node.Left, right.Left), right.Right)
                : trees.Make(new VisibilityEntry(node), node.Left, right);
        }

        public static VisibilityNode? Remove(VisibilityTreeBuilder trees, VisibilityNode? node, string? name)
        {
            if (node is null)
                return null;

            var comparison = string.CompareOrdinal(name, node.Name);
            if (comparison == 0)
                return Merge(trees, node.Left, node.Right);

            if (comparison < 0)
            {
                var left = Remove(trees, node.Left, name);
                return ReferenceEquals(left, node.Left) ? node : trees.Make(new VisibilityEntry(node), left, node.Right);
            }

            var right = Remove(trees, node.Right, name);
            return ReferenceEquals(right, node.Right) ? node : trees.Make(new VisibilityEntry(node), node.Left, right);
        }

        private static VisibilityNode? Merge(VisibilityTreeBuilder trees, VisibilityNode? low, VisibilityNode? high)
        {
            if (low is null)
                return high;
            if (high is null)
                return low;

            return VisibilityTree.HigherPriority(low.Priority, low.Name, high.Priority, high.Name)
                ? trees.Make(new VisibilityEntry(low), low.Left, Merge(trees, low.Right, high))
                : trees.Make(new VisibilityEntry(high), Merge(trees, low, high.Left), high.Right);
        }

        private static bool SameEntry(VisibilityNode node, in VisibilityEntry entry)
            => ReferenceEquals(node.Symbol, entry.Symbol)
                && node.Meta == entry.Meta
                && ReferenceEquals(node.DeferredTwin, entry.DeferredTwin);
    }

    /// <summary>One operation of a scripted sequence: a set (symbol, meta, twin) or a removal by name.</summary>
    private readonly record struct Op(string Name, VisibleSymbol? Symbol, int Meta, VisibleSymbol? Twin)
    {
        public bool IsRemoval => Symbol is null;

        public static Op Set(VisibleSymbol symbol, int meta = 0, VisibleSymbol? twin = null) => new(symbol.Name, symbol, meta, twin);

        public static Op Remove(string name) => new(name, null, 0, null);
    }

    private static VisibleSymbol Symbol(string name) => new(name, IdentifierClassification.PropertyReference, null, null);

    private static string Name(int index) => $"n{index:D7}";

    public static IEnumerable<object[]> Scripts()
        => from script in new[] { "ascending", "descending", "random", "reversed-random", "alternating", "replacements", "removals", "cycles", "mixed", "vshape" }
           from priority in new[] { "pseudo-random", "constant", "increasing", "decreasing", "collisions", "vshape" }
           from collide in new[] { false, true }
           select new object[] { script, priority, collide };

    /// <summary>
    /// A deterministic per-name priority (a function of the name, as <see cref="VisibilityTreeBuilder.PriorityOverride"/>
    /// requires). "vshape" makes the middle name the root over a right spine (low names) and a left
    /// spine (high names) whose priorities interleave, so removing the root joins both spines.
    /// </summary>
    private static Func<string?, int> Priority(string mode, int size)
    {
        var middle = size / 2;
        return name =>
        {
            var index = int.Parse(name!.AsSpan(1));
            return mode switch
            {
                "pseudo-random" => (int)(unchecked((uint)index * 2_654_435_761u) >> 1) ^ 0x5bd1e995,
                "constant" => 3,
                "increasing" => index,
                "decreasing" => -index,
                "collisions" => index % 3,
                "vshape" => index == middle ? int.MaxValue
                    : index < middle ? int.MaxValue - 1 - (2 * index)
                    : int.MaxValue - 2 - (2 * (size - 1 - index)),
                _ => throw new ArgumentOutOfRangeException(nameof(mode)),
            };
        };
    }

    private static List<Op> Script(string kind, int size, int seed)
    {
        var random = new Random(seed);
        var symbols = Enumerable.Range(0, size).Select(i => Symbol(Name(i))).ToArray();
        var ops = new List<Op>();
        switch (kind)
        {
            case "ascending":
                ops.AddRange(symbols.Select(s => Op.Set(s)));
                break;
            case "descending":
                ops.AddRange(symbols.Reverse().Select(s => Op.Set(s)));
                break;
            case "random":
            case "reversed-random":
                var shuffled = symbols.OrderBy(_ => random.Next()).Select(s => Op.Set(s)).ToList();
                if (kind == "reversed-random")
                    shuffled.Reverse();
                ops.AddRange(shuffled);
                break;
            case "alternating":
                for (int low = 0, high = size - 1; low <= high; low++, high--)
                {
                    ops.Add(Op.Set(symbols[low]));
                    if (high != low)
                        ops.Add(Op.Set(symbols[high]));
                }
                break;
            case "replacements":
                ops.AddRange(symbols.OrderBy(_ => random.Next()).Select(s => Op.Set(s)));
                for (var i = 0; i < size * 2; i++)
                {
                    var target = symbols[random.Next(size)];
                    ops.Add(random.Next(4) switch
                    {
                        0 => Op.Set(target),                                   // no-op replacement
                        1 => Op.Set(Symbol(target.Name)),                      // a new symbol object
                        2 => Op.Set(target, VisibilityEntry.OpenMeta(random.Next(3))),
                        _ => Op.Set(target, 0, Symbol(target.Name)),           // deferred twin
                    });
                }
                break;
            case "removals":
                ops.AddRange(symbols.OrderBy(_ => random.Next()).Select(s => Op.Set(s)));
                ops.Add(Op.Remove("absent"));
                ops.Add(Op.Remove(Extra));
                ops.AddRange(symbols.OrderBy(_ => random.Next()).Select(s => Op.Remove(s.Name)));
                ops.Add(Op.Remove(symbols[0].Name));
                break;
            case "cycles":
                ops.AddRange(symbols.Select(s => Op.Set(s)));
                for (var i = 0; i < size * 2; i++)
                {
                    var target = symbols[random.Next(size)];
                    ops.Add(Op.Remove(target.Name));
                    ops.Add(Op.Set(target));
                }
                break;
            case "mixed":
                for (var i = 0; i < size * 4; i++)
                {
                    var target = symbols[random.Next(size)];
                    ops.Add(random.Next(5) switch
                    {
                        0 or 1 => Op.Set(target),
                        2 => Op.Set(target, VisibilityEntry.OpenMeta(1), random.Next(2) == 0 ? null : Symbol(target.Name)),
                        3 => Op.Remove(target.Name),
                        _ => Op.Remove("m" + random.Next(size)),
                    });
                }
                break;
            case "vshape":
                // Every name, then remove the current root repeatedly (deep joins under "vshape").
                ops.AddRange(symbols.OrderBy(_ => random.Next()).Select(s => Op.Set(s)));
                ops.Add(Op.Remove(symbols[size / 2].Name));
                for (var i = 0; i < size / 2; i++)
                    ops.Add(Op.Remove(symbols[random.Next(size)].Name));
                break;
            default:
                throw new ArgumentOutOfRangeException(nameof(kind));
        }

        return ops;
    }

    [Theory]
    [MemberData(nameof(Scripts))]
    public void IterativeUpdates_MatchTheRecursiveAlgorithm_NodeForNodeAndMakeForMake(string script, string priorityMode, bool collide)
    {
        const int size = 160;
        var priority = Priority(priorityMode, size);
        var ops = Script(script, size, seed: 0x5CB3 ^ size);

        // Two builders with the same priorities: the reference and the candidate, counted apart.
        var referenceObservations = new FrontEndTraversalObservations();
        var candidateObservations = new FrontEndTraversalObservations();
        var reference = new VisibilityTreeBuilder(referenceObservations, collide) { PriorityOverride = priority };
        var candidate = new VisibilityTreeBuilder(candidateObservations, collide) { PriorityOverride = priority };

        // One builder running both: the candidate must find every node the reference made.
        var sharedObservations = new FrontEndTraversalObservations();
        var shared = new VisibilityTreeBuilder(sharedObservations, collide) { PriorityOverride = priority };

        VisibilityNode? referenceRoot = null, candidateRoot = null, sharedRoot = null;
        var history = new List<(VisibilityNode? Root, List<(VisibleSymbol Symbol, int Meta, VisibleSymbol? Twin)> Content)>();
        var oracle = new SortedDictionary<string, (VisibleSymbol Symbol, int Meta, VisibleSymbol? Twin)>(StringComparer.Ordinal);
        var deepestMergeObserved = 0;
        for (var step = 0; step < ops.Count; step++)
        {
            var op = ops[step];
            VisibilityNode? nextReference, nextCandidate, nextSharedReference, nextShared;
            if (op.IsRemoval)
            {
                nextReference = RecursiveReference.Remove(reference, referenceRoot, op.Name);
                nextCandidate = candidate.Remove(candidateRoot, op.Name);
                nextSharedReference = RecursiveReference.Remove(shared, sharedRoot, op.Name);
                var createdBefore = sharedObservations.ScopeVisibilityNodesCreated;
                nextShared = shared.Remove(sharedRoot, op.Name);
                Assert.Equal(createdBefore, sharedObservations.ScopeVisibilityNodesCreated);
                if (VisibilityTree.Find(candidateRoot, op.Name) is { } removed && removed.Left is not null && removed.Right is not null)
                    deepestMergeObserved = Math.Max(deepestMergeObserved, RightSpine(removed.Left) + LeftSpine(removed.Right));
                oracle.Remove(op.Name);
            }
            else
            {
                nextReference = RecursiveReference.Set(reference, referenceRoot, reference.Entry(op.Symbol!, op.Meta, op.Twin));
                nextCandidate = candidate.Set(candidateRoot, candidate.Entry(op.Symbol!, op.Meta, op.Twin));
                var entry = shared.Entry(op.Symbol!, op.Meta, op.Twin);
                nextSharedReference = RecursiveReference.Set(shared, sharedRoot, entry);
                var createdBefore = sharedObservations.ScopeVisibilityNodesCreated;
                nextShared = shared.Set(sharedRoot, entry);
                Assert.Equal(createdBefore, sharedObservations.ScopeVisibilityNodesCreated);
                oracle[op.Name] = (op.Symbol!, op.Meta, op.Twin);
            }

            var where = $"step {step} ({(op.IsRemoval ? "remove" : "set")} {op.Name}) of {script}/{priorityMode}/collide={collide}";
            Assert.True(ReferenceEquals(nextShared, nextSharedReference), $"different node in one builder at {where}");
            Assert.True(ReferenceEquals(nextReference, referenceRoot) == ReferenceEquals(nextCandidate, candidateRoot), $"no-op disagreement at {where}");
            Assert.True(ReferenceEquals(nextShared, sharedRoot) == ReferenceEquals(nextCandidate, candidateRoot), $"shared no-op disagreement at {where}");
            Assert.True(
                referenceObservations.ScopeVisibilityNodesCreated == candidateObservations.ScopeVisibilityNodesCreated
                    && referenceObservations.ScopeVisibilityNodesReused == candidateObservations.ScopeVisibilityNodesReused,
                $"Make sequence diverged at {where}: reference {referenceObservations.ScopeVisibilityNodesCreated}/{referenceObservations.ScopeVisibilityNodesReused}, "
                    + $"candidate {candidateObservations.ScopeVisibilityNodesCreated}/{candidateObservations.ScopeVisibilityNodesReused} (created/reused)");
            AssertSameShape(nextReference, nextCandidate, where);
            AssertTreap(nextCandidate, where);
            AssertContent(oracle, nextCandidate, where);

            referenceRoot = nextReference;
            candidateRoot = nextCandidate;
            sharedRoot = nextShared;
            history.Add((candidateRoot, Content(candidateRoot)));
        }

        // Every historical version is untouched by the later updates.
        foreach (var (root, content) in history)
        {
            Assert.Equal(content, Content(root));
            AssertTreap(root, "history");
        }

        // The V-shaped script really joins two long spines on its first root removal.
        if (script == "vshape" && priorityMode == "vshape")
            Assert.True(deepestMergeObserved >= size - 2, $"the V-shaped join spanned only {deepestMergeObserved} levels");
    }

    [Fact]
    public void ProductionPriorities_IterativeAndRecursiveUpdatesYieldTheSameNodesInOneBuilder()
    {
        foreach (var script in new[] { "random", "replacements", "removals", "cycles", "mixed" })
        {
            var observations = new FrontEndTraversalObservations();
            var trees = new VisibilityTreeBuilder(observations);
            VisibilityNode? root = null;
            foreach (var op in Script(script, 300, seed: 17))
            {
                VisibilityNode? expected, actual;
                var createdBefore = 0L;
                if (op.IsRemoval)
                {
                    expected = RecursiveReference.Remove(trees, root, op.Name);
                    createdBefore = observations.ScopeVisibilityNodesCreated;
                    actual = trees.Remove(root, op.Name);
                }
                else
                {
                    var entry = trees.Entry(op.Symbol!, op.Meta, op.Twin);
                    expected = RecursiveReference.Set(trees, root, entry);
                    createdBefore = observations.ScopeVisibilityNodesCreated;
                    actual = trees.Set(root, entry);
                }

                Assert.Same(expected, actual);
                Assert.Equal(createdBefore, observations.ScopeVisibilityNodesCreated);
                root = actual;
            }

            // Canonical: the bulk build of the final content is the same root object.
            Assert.Same(root, trees.Build(VisibilityTree.InOrder(root).Select(node => new VisibilityEntry(node)).ToList()));
        }
    }

    [Fact]
    public void NoOpUpdates_ReturnTheRootAndMakeNothing()
    {
        var observations = new FrontEndTraversalObservations();
        var trees = new VisibilityTreeBuilder(observations) { PriorityOverride = _ => 0 };
        var entries = Enumerable.Range(0, 64).Select(i => trees.Entry(Symbol(Name(i)), 0, null)).ToList();
        var root = trees.Build(entries)!;
        var created = observations.ScopeVisibilityNodesCreated;
        var reused = observations.ScopeVisibilityNodesReused;

        Assert.Null(trees.Remove(null, "absent"));
        Assert.Same(root, trees.Remove(root, "absent"));
        Assert.Same(root, trees.Remove(root, Extra));
        Assert.Same(root, trees.Remove(root, ""));
        Assert.Same(root, trees.Remove(root, null));
        Assert.Same(root, trees.Set(root, entries[0]));
        Assert.Same(root, trees.Set(root, entries[63]));
        Assert.Same(root, trees.Set(root, entries[31]));
        Assert.Equal(created, observations.ScopeVisibilityNodesCreated);
        Assert.Equal(reused, observations.ScopeVisibilityNodesReused);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void InternalRemoval_PreservesPendingAncestors_WhenMergeGrowsThePath(bool targetOnLeft)
    {
        const int size = 161;
        var ancestorName = targetOnLeft ? "z" : "a";
        var priority = Priority("vshape", size);
        var observations = new FrontEndTraversalObservations();
        var trees = new VisibilityTreeBuilder(observations)
        {
            PriorityOverride = name => name == ancestorName ? int.MaxValue : priority(name) - 1,
        };
        var entries = Enumerable.Range(0, size).Select(i => trees.Entry(Symbol(Name(i)), 0, null)).ToList();
        var ancestor = trees.Entry(Symbol(ancestorName), 0, null);
        var root = trees.Build(entries.Append(ancestor).OrderBy(entry => entry.Name, StringComparer.Ordinal).ToList())!;
        Assert.Equal(ancestorName, root.Name);
        var target = (targetOnLeft ? root.Left : root.Right)!;
        Assert.Equal(Name(size / 2), target.Name);
        Assert.Equal(size / 2, RightSpine(target.Left!));
        Assert.Equal(size / 2, LeftSpine(target.Right!));

        // Remove has a pending ancestor before Merge grows the shared 32-slot path. Both the
        // old slots and the new array must survive: each side catches a different unwind error.
        var expected = RecursiveReference.Remove(trees, root, target.Name);
        var created = observations.ScopeVisibilityNodesCreated;
        var reused = observations.ScopeVisibilityNodesReused;
        var actual = trees.Remove(root, target.Name);
        Assert.Same(expected, actual);
        Assert.Equal(created, observations.ScopeVisibilityNodesCreated);
        Assert.Equal(size - 1, observations.ScopeVisibilityNodesReused - reused);
        Assert.Equal(size, actual!.Count);
        AssertTreap(actual, "internal V-shaped removal");
        Assert.Same(root, trees.Set(actual, entries[size / 2]));
        Assert.Equal(size + 1, root.Count);
        Assert.Same(target, VisibilityTree.Find(root, target.Name));
    }

    [Fact]
    public async Task DeepTreeUpdates_RunAtConstantStackDepth_InASubprocess()
        => await RunProbeChild(nameof(DeepTreeUpdates_ProbeChild));

    [Fact]
    public void DeepTreeUpdates_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        AstStructuralDepthProcessTests.RunOnThreadWithStack(SmallStackBytes, () =>
        {
            Log($"deep-stack requested={SmallStackBytes} os={ThreadStackSize.OfCurrentThread()?.ToString() ?? "unknown"} (excess is padded away)");
            DeepSetAtTheBottom();
            DeepSetRotatingToTheRoot();
            DeepRemove();
            DeepMerge();
            DeepNoOps();
            DeepFailureRecovery();
        });

        File.WriteAllText(Environment.GetEnvironmentVariable(ProbeMarkerFileEnvironment)!, ProbeSuccessMarker);
    }

    /// <summary>A right-degenerate chain of <paramref name="levels"/> names via the iterative bulk build (equal priorities: the lowest name is the root).</summary>
    private static (VisibilityTreeBuilder Trees, FrontEndTraversalObservations Observations, VisibilityNode Root) Chain(int levels, Func<string?, int>? priority = null)
    {
        var observations = new FrontEndTraversalObservations();
        var trees = new VisibilityTreeBuilder(observations) { PriorityOverride = priority ?? (_ => 0) };
        var root = trees.Build(Enumerable.Range(0, levels).Select(i => trees.Entry(Symbol(Name(i)), 0, null)).ToList())!;
        Assert.Equal(levels, Height(root));
        return (trees, observations, root);
    }

    /// <summary>Appends one progress line to the parent's log file at once, so a crash leaves the last started case.</summary>
    private static void Log(string line)
        => File.AppendAllText(Environment.GetEnvironmentVariable(ProbeLogFileEnvironment)!, line + Environment.NewLine);

    private static void Case(string name, Action body)
    {
        Log($"deep-case {name} start");
        var watch = Stopwatch.StartNew();
        var allocated = GC.GetAllocatedBytesForCurrentThread();
        body();
        Log($"deep-case {name} ok {watch.ElapsedMilliseconds} ms, {(GC.GetAllocatedBytesForCurrentThread() - allocated) / 1024} KiB allocated");
    }

    private static void DeepSetAtTheBottom() => Case($"set-bottom chain={DeepLevels}", () =>
    {
        var (trees, observations, root) = Chain(DeepLevels);
        var created = observations.ScopeVisibilityNodesCreated;
        var grown = trees.Set(root, trees.Entry(Symbol(Extra), 0, null));
        AssertDeepPathReleased(trees);
        Assert.Equal(DeepLevels + 1, grown.Count);
        Assert.Equal(DeepLevels + 1, Height(grown));
        Assert.Equal(DeepLevels + 1, observations.ScopeVisibilityNodesCreated - created);
        Assert.NotNull(VisibilityTree.Find(grown, Extra));
        Assert.Null(VisibilityTree.Find(root, Extra));
        AssertTreap(grown, "set-bottom");
        Assert.Equal(DeepLevels, Height(root));
    });

    private static void DeepSetRotatingToTheRoot() => Case($"set-rotate chain={DeepLevels}", () =>
    {
        // The new highest name outranks every chain node: it rotates through all of them.
        var (trees, observations, root) = Chain(DeepLevels, name => name == Extra ? 1 : 0);
        var created = observations.ScopeVisibilityNodesCreated;
        var grown = trees.Set(root, trees.Entry(Symbol(Extra), 0, null));
        AssertDeepPathReleased(trees);
        Assert.Equal(Extra, grown.Name);
        Assert.Null(grown.Right);
        Assert.Equal(DeepLevels + 1, Height(grown));

        // Each rotation re-makes the chain suffix below the new node, which interning resolves to
        // the existing chain nodes: only the new name's DeepLevels + 1 intermediate nodes are new.
        Assert.Same(root, grown.Left);
        Assert.Equal(DeepLevels + 1, observations.ScopeVisibilityNodesCreated - created);
        Assert.Equal(DeepLevels, observations.ScopeVisibilityNodesReused);
        AssertTreap(grown, "set-rotate");
        Assert.Equal(Enumerable.Range(0, DeepLevels).Select(Name).Append(Extra), VisibilityTree.InOrder(grown).Select(node => node.Name));
    });

    private static void DeepRemove() => Case($"remove-bottom chain={DeepLevels}", () =>
    {
        var (trees, _, root) = Chain(DeepLevels);
        var last = Name(DeepLevels - 1);
        var shrunk = trees.Remove(root, last)!;
        AssertDeepPathReleased(trees);
        Assert.Equal(DeepLevels - 1, shrunk.Count);
        Assert.Null(VisibilityTree.Find(shrunk, last));
        Assert.NotNull(VisibilityTree.Find(shrunk, Name(DeepLevels - 2)));
        Assert.Equal(Enumerable.Range(0, DeepLevels - 1).Select(Name), VisibilityTree.InOrder(shrunk).Select(node => node.Name));
        AssertTreap(shrunk, "remove-bottom");

        // The historical root still holds the name, at its depth.
        Assert.Equal(DeepLevels, root.Count);
        Assert.NotNull(VisibilityTree.Find(root, last, out var index, out var probes));
        Assert.Equal((DeepLevels - 1, DeepLevels), (index, probes));
    });

    private static void DeepMerge() => Case($"merge-vshape spines={DeepLevels}+{DeepLevels}", () =>
    {
        // Root in the middle over a right spine of the low names and a left spine of the high
        // names, priorities interleaved: removing the root joins both spines level by level.
        var size = (2 * DeepLevels) + 1;
        var observations = new FrontEndTraversalObservations();
        var trees = new VisibilityTreeBuilder(observations) { PriorityOverride = Priority("vshape", size) };
        var root = trees.Build(Enumerable.Range(0, size).Select(i => trees.Entry(Symbol(Name(i)), 0, null)).ToList())!;
        Assert.Equal(Name(DeepLevels), root.Name);
        Assert.Equal(DeepLevels, RightSpine(root.Left!));
        Assert.Equal(DeepLevels, LeftSpine(root.Right!));

        var created = observations.ScopeVisibilityNodesCreated;
        var merged = trees.Remove(root, root.Name)!;
        AssertDeepPathReleased(trees);

        // The join rebuilt each node of both spines but the deepest one, which it kept as is.
        Assert.Equal((2 * DeepLevels) - 1, observations.ScopeVisibilityNodesCreated - created);
        Assert.Equal(2 * DeepLevels, merged.Count);
        Assert.Equal(2 * DeepLevels, Height(merged));
        Assert.Equal(Name(0), merged.Name);
        Assert.Null(VisibilityTree.Find(merged, Name(DeepLevels)));
        Assert.Equal(Enumerable.Range(0, size).Where(i => i != DeepLevels).Select(Name), VisibilityTree.InOrder(merged).Select(node => node.Name));
        AssertTreap(merged, "merge-vshape");
        Assert.Equal(size, root.Count);
    });

    private static void DeepNoOps() => Case($"no-ops chain={DeepLevels}", () =>
    {
        var (trees, observations, root) = Chain(DeepLevels);
        var created = observations.ScopeVisibilityNodesCreated;
        var reused = observations.ScopeVisibilityNodesReused;
        var deepest = VisibilityTree.Find(root, Name(DeepLevels - 1))!;
        Assert.Same(root, trees.Set(root, new VisibilityEntry(deepest)));
        AssertDeepPathReleased(trees);
        Assert.Same(root, trees.Remove(root, Extra));
        AssertDeepPathReleased(trees);
        Assert.Same(root, trees.Remove(root, Name(DeepLevels - 1) + "x"));
        AssertDeepPathReleased(trees);
        Assert.Equal(created, observations.ScopeVisibilityNodesCreated);
        Assert.Equal(reused, observations.ScopeVisibilityNodesReused);
    });

    /// <summary>
    /// A DEBUG own-priority refusal at the bottom must release the large temporary path and
    /// leave the builder usable. This depth is unsafe for the old algorithm on small stacks,
    /// so failure recovery belongs in the isolated child alongside the other deep cases.
    /// </summary>
    private static void DeepFailureRecovery() => Case("failed-update chain=3000", () =>
    {
        var (trees, _, root) = Chain(3_000);
#if DEBUG
        var foreign = new VisibilityEntry(Symbol("n9999998"), 0, null, 12345);
        Assert.Throws<InvalidOperationException>(() => trees.Set(root, foreign));
        AssertDeepPathReleased(trees);
#endif
        var extra = trees.Entry(Symbol(Extra), 0, null);
        var grown = trees.Set(root, extra);
        AssertDeepPathReleased(trees);
        Assert.Equal(3_001, grown.Count);
        Assert.Same(root, trees.Remove(grown, extra.Name));
        AssertDeepPathReleased(trees);
        AssertTreap(grown, "after failure");
    });

    private static void AssertDeepPathReleased(VisibilityTreeBuilder trees)
        => Assert.Null(typeof(VisibilityTreeBuilder)
            .GetField("_path", System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic)!
            .GetValue(trees));

    private async Task RunProbeChild(string childTestName)
    {
        var assemblyPath = typeof(ScopeVisibilityIterativeUpdateTests).Assembly.Location;
        var testName = typeof(ScopeVisibilityIterativeUpdateTests).FullName + "." + childTestName;
        var markerFile = Path.Combine(Path.GetTempPath(), $"katlang-scope-deep-probe-{Guid.NewGuid():N}.txt");
        var logFile = Path.ChangeExtension(markerFile, ".log");

        var startInfo = SubprocessProbe.StartInfo(assemblyPath, [testName]);
        startInfo.Environment[ProbeChildEnvironment] = "1";
        startInfo.Environment[ProbeMarkerFileEnvironment] = markerFile;
        startInfo.Environment[ProbeLogFileEnvironment] = logFile;
        startInfo.Environment["DOTNET_NOLOGO"] = "1";

        try
        {
            using var process = new Process { StartInfo = startInfo };
            process.Start();
            var stdoutTask = process.StandardOutput.ReadToEndAsync();
            var stderrTask = process.StandardError.ReadToEndAsync();

            await process.WaitForExitAsync();

            // The progress log first: its last "deep-case ... start" line names the operation that hung or crashed.
            var progress = File.Exists(logFile) ? await File.ReadAllTextAsync(logFile) : "(no progress log)";
            var combined = progress + Environment.NewLine + await stdoutTask + Environment.NewLine + await stderrTask;
            output.WriteLine(combined);

            Assert.DoesNotContain("Stack overflow", combined, StringComparison.OrdinalIgnoreCase);
            Assert.DoesNotContain("StackOverflowException", combined, StringComparison.OrdinalIgnoreCase);
            Assert.True(process.ExitCode == 0, $"Deep-update probe exited with {process.ExitCode}.{Environment.NewLine}{combined}");
            Assert.True(File.Exists(markerFile), "Deep-update probe did not write its success marker." + Environment.NewLine + combined);
            Assert.Equal(ProbeSuccessMarker, (await File.ReadAllTextAsync(markerFile)).Trim());
            Assert.Equal(6, progress.Split('\n').Count(line => line.StartsWith("deep-case ", StringComparison.Ordinal) && line.Contains(" ok ", StringComparison.Ordinal)));
        }
        finally
        {
            foreach (var file in new[] { markerFile, logFile })
            {
                try { File.Delete(file); }
                catch { /* best-effort cleanup */ }
            }
        }
    }

    private static List<(VisibleSymbol Symbol, int Meta, VisibleSymbol? Twin)> Content(VisibilityNode? root)
        => VisibilityTree.InOrder(root).Select(node => (node.Symbol, node.Meta, node.DeferredTwin)).ToList();

    private static void AssertContent(SortedDictionary<string, (VisibleSymbol Symbol, int Meta, VisibleSymbol? Twin)> oracle, VisibilityNode? root, string where)
    {
        var actual = Content(root);
        Assert.True(oracle.Values.SequenceEqual(actual), $"content differs from the dictionary oracle at {where}");
        var index = 0;
        foreach (var (name, expected) in oracle)
        {
            var found = VisibilityTree.Find(root, name, out var position, out _);
            Assert.True(found is not null && ReferenceEquals(found.Symbol, expected.Symbol) && position == index, $"lookup of {name} at {where}");
            Assert.Same(found, VisibilityTree.ElementAt(root!, index));
            index++;
        }

        Assert.Null(VisibilityTree.Find(root, "absent"));
    }

    /// <summary>Exact structural equality of two trees from different builders: every node's entry, priority, count and child shape.</summary>
    private static void AssertSameShape(VisibilityNode? expected, VisibilityNode? actual, string where)
    {
        var pending = new Stack<(VisibilityNode? Expected, VisibilityNode? Actual)>();
        pending.Push((expected, actual));
        while (pending.TryPop(out var pair))
        {
            if (pair.Expected is null || pair.Actual is null)
            {
                Assert.True(pair.Expected is null && pair.Actual is null, $"child presence differs at {where}");
                continue;
            }

            Assert.True(
                ReferenceEquals(pair.Expected.Symbol, pair.Actual.Symbol)
                    && ReferenceEquals(pair.Expected.DeferredTwin, pair.Actual.DeferredTwin)
                    && pair.Expected.Meta == pair.Actual.Meta
                    && pair.Expected.Priority == pair.Actual.Priority
                    && pair.Expected.Count == pair.Actual.Count,
                $"node {pair.Expected.Name} differs from {pair.Actual.Name} at {where}");
            pending.Push((pair.Expected.Right, pair.Actual.Right));
            pending.Push((pair.Expected.Left, pair.Actual.Left));
        }
    }

    /// <summary>Ordinal search order, heap order under <see cref="VisibilityTree.HigherPriority"/>, and exact subtree counts, without recursion.</summary>
    private static void AssertTreap(VisibilityNode? root, string where)
    {
        string? previous = null;
        foreach (var node in VisibilityTree.InOrder(root))
        {
            Assert.True(previous is null || string.CompareOrdinal(previous, node.Name) < 0, $"ordinal order broken at {node.Name} ({where})");
            previous = node.Name;
            Assert.True(node.Count == 1 + (node.Left?.Count ?? 0) + (node.Right?.Count ?? 0), $"count of {node.Name} ({where})");
            foreach (var child in new[] { node.Left, node.Right })
            {
                if (child is not null)
                    Assert.True(VisibilityTree.HigherPriority(node.Priority, node.Name, child.Priority, child.Name), $"heap order broken under {node.Name} ({where})");
            }
        }
    }

    private static int Height(VisibilityNode? root)
    {
        var height = 0;
        var pending = new Stack<(VisibilityNode Node, int Depth)>();
        if (root is not null)
            pending.Push((root, 1));
        while (pending.TryPop(out var item))
        {
            height = Math.Max(height, item.Depth);
            if (item.Node.Left is { } left)
                pending.Push((left, item.Depth + 1));
            if (item.Node.Right is { } right)
                pending.Push((right, item.Depth + 1));
        }

        return height;
    }

    private static int RightSpine(VisibilityNode node)
    {
        var length = 1;
        for (; node.Right is { } right; node = right)
            length++;
        return length;
    }

    private static int LeftSpine(VisibilityNode node)
    {
        var length = 1;
        for (; node.Left is { } left; node = left)
            length++;
        return length;
    }
}
