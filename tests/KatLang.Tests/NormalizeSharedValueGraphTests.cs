using System.Globalization;
using System.Numerics;
using System.Runtime.CompilerServices;

namespace KatLang.Tests;

/// <summary>
/// <see cref="Result.Normalize"/> over SHARED value graphs, the value-PRODUCING sibling of the
/// equality/hash walks pinned by <see cref="SharedValueGraphComplexityTests"/>. A value is a DAG,
/// not a tree — <c>W = [x, x]</c> applied n times reaches n+1 distinct nodes through 2^n
/// root-to-leaf paths — so a normalization whose work is proportional to PATHS is exponential on
/// values an ordinary in-budget loop builds, and no evaluation step budget bounds it: the blow-up
/// happens inside ONE value-level operation.
///
/// <para>Producing a value raises a second requirement the scalar walks do not have: the OUTPUT
/// must stay a DAG. A rebuild that expands paths hands the exponentially larger tree to every
/// later operation, so sharing preservation is pinned here as directly as the work bound.</para>
///
/// <para>Work counts are exact and deterministic, measured through the passive operation-scoped
/// <see cref="ValueTraversalObservations"/>; timing is deliberately not a pass/fail signal.
/// Semantics are checked against <see cref="NaiveNormalize"/>, a test-only recursive replica of the
/// path-expanding rebuild this suite replaced.</para>
/// </summary>
public class NormalizeSharedValueGraphTests
{
    private const int ShallowDepth = 20;

    private const int DeepDepth = 40;

    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result Str(string value) => new Result.Str(value);

    private static Result List(params Result[] items) => Result.ListValue.TakeOwnership(items);

    private static Result Seq(params Result[] items) => Result.SequenceValue.TakeOwnership(items);

    private static ValueTraversalObservations Observations() => new();

    /// <summary>
    /// The doubling DAG: <c>P0 = leaf</c>, <c>Pk = [P(k-1), P(k-1)]</c>. A graph of depth n has
    /// exactly n+1 structure nodes on the spine and 2^n root-to-leaf paths. The default leaf is
    /// already normal, so the whole graph is; pass <see cref="RedundantLeaf"/> to force every level
    /// to rebuild.
    /// </summary>
    private static Result SharedDag(int depth, Result? leaf = null)
    {
        var node = leaf ?? List(Atom(1), Atom(2));
        for (var i = 0; i < depth; i++)
            node = List(node, node);
        return node;
    }

    /// <summary>A leaf carrying ONE redundant singleton sequence, so its normal form differs and
    /// the difference propagates through every enclosing level of a doubling DAG.</summary>
    private static Result RedundantLeaf(decimal a = 1, decimal b = 2) => List(Seq(Atom(a)), Atom(b));

    /// <summary>The normal form of <see cref="RedundantLeaf"/>.</summary>
    private static Result NormalLeaf(decimal a = 1, decimal b = 2) => List(Atom(a), Atom(b));

    /// <summary>
    /// Test-only replica of the pre-fix normalization: a plain recursive post-order rebuild with no
    /// memo, which expands one frame per PATH and allocates fresh structure for every node it
    /// visits. It is the semantic oracle for the memoized implementation, and (with a counter) the
    /// measurement of the work the old walk performed. Only ever applied to small values — on the
    /// doubling DAG it is exponential by construction.
    /// </summary>
    private static Result NaiveNormalize(Result value, StrongBox<long>? expansions = null)
    {
        IReadOnlyList<Result> items;
        bool isSequence;
        switch (value)
        {
            case Result.SequenceValue(var sequenceItems):
                items = sequenceItems;
                isSequence = true;
                break;
            case Result.ListValue(var listItems):
                items = listItems;
                isSequence = false;
                break;
            default:
                return value;
        }

        if (expansions is not null)
            expansions.Value++;

        var normalized = new Result[items.Count];
        for (var i = 0; i < items.Count; i++)
            normalized[i] = NaiveNormalize(items[i], expansions);

        if (isSequence)
            return normalized is [var single] ? single : Result.SequenceValue.TakeOwnership(normalized);
        return Result.ListValue.TakeOwnership(normalized);
    }

    /// <summary>Distinct nodes reachable from <paramref name="value"/> by REFERENCE identity.</summary>
    private static int DistinctNodes(Result value)
    {
        var seen = new HashSet<Result>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<Result>();
        pending.Push(value);
        while (pending.Count > 0)
        {
            var node = pending.Pop();
            if (!seen.Add(node))
                continue;
            foreach (var child in Children(node))
                pending.Push(child);
        }

        return seen.Count;
    }

    private static IReadOnlyList<Result> Children(Result value) => value switch
    {
        Result.SequenceValue(var items) => items,
        Result.ListValue(var items) => items,
        _ => [],
    };

    private static int DistinctStructureNodes(Result value)
    {
        var seen = new HashSet<Result>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<Result>();
        pending.Push(value);
        while (pending.Count > 0)
        {
            var node = pending.Pop();
            if (node is not (Result.SequenceValue or Result.ListValue) || !seen.Add(node))
                continue;
            foreach (var child in Children(node))
                pending.Push(child);
        }

        return seen.Count;
    }

    /// <summary>
    /// A DAG-BOUNDED description of a value. Rendering — including
    /// <see cref="Evaluator.FormatResultForDiagnostic"/> — spells out every PATH and is therefore
    /// exponential on a shared graph, so failures here are described by kind, breadth, and
    /// distinct-node count instead of attempting to materialize that path-sized message.
    /// </summary>
    private static string Describe(Result value)
        => value switch
        {
            Result.SequenceValue(var items) => $"sequence value ({items.Count} items, {DistinctNodes(value)} distinct nodes)",
            Result.ListValue(var items) => $"list value ({items.Count} elements, {DistinctNodes(value)} distinct nodes)",
            Result.Atom(var number) => $"atom {number}",
            Result.Str(var text) => $"string '{text}'",
            _ => "value",
        };

    private static void AssertSemanticallyEqual(Result expected, Result actual)
    {
        if (!Result.ValueComparer.Equals(expected, actual))
            Assert.Fail($"expected {Describe(expected)} but got {Describe(actual)}");
        Assert.Equal(
            Result.ValueComparer.GetHashCode(expected),
            Result.ValueComparer.GetHashCode(actual));
    }

    // ── Unique-node work: each distinct node is normalized at most once per call ─────────────

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public void Normalize_SharedDag_ExpandsEachUniqueNodeAtMostOnce(int depth)
    {
        var observations = Observations();
        var value = SharedDag(depth);

        _ = value.NormalizeObserved(observations);

        // depth+1 distinct structure nodes, each expanded once. The path-expanding rebuild
        // expanded 2^(depth+1) - 1 of them.
        Assert.Equal(depth + 1, observations.NormalizeStructureExpansionCount);
    }

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public void Normalize_SharedDagNeedingRebuild_ExpandsEachUniqueNodeAtMostOnce(int depth)
    {
        var observations = Observations();

        // Every level's normal form now DIFFERS from the written node, so the memo is exercised on
        // the rebuilding path rather than on an unchanged-node shortcut.
        var normalized = SharedDag(depth, RedundantLeaf()).NormalizeObserved(observations);

        // The depth+1 spine nodes plus the one redundant singleton sequence inside the leaf.
        Assert.Equal(depth + 2, observations.NormalizeStructureExpansionCount);
        AssertSemanticallyEqual(SharedDag(depth, NormalLeaf()), normalized);
    }

    [Fact]
    public void Normalize_WorkGrowsLinearlyWithGraphDepth()
    {
        var shallow = Observations();
        var deep = Observations();

        _ = SharedDag(ShallowDepth, RedundantLeaf()).NormalizeObserved(shallow);
        _ = SharedDag(DeepDepth, RedundantLeaf()).NormalizeObserved(deep);

        // Twenty more levels cost twenty more expansions, not 2^20 times as many.
        Assert.Equal(
            DeepDepth - ShallowDepth,
            deep.NormalizeStructureExpansionCount - shallow.NormalizeStructureExpansionCount);
    }

    [Fact]
    public void Normalize_DeterministicDagCorpus_ExpandsEachReachableStructureOnce()
    {
        // Non-chain meshes: each later node reuses several earlier nodes, with different parent
        // kinds, positions and neighbours. Keep them small enough for the path-expanding oracle.
        var leaf = RedundantLeaf(1, 2);
        var peer = List(Seq(Atom(3)), Atom(4));
        var left = List(leaf, peer, leaf);
        var right = Seq(peer, left, Seq(Atom(5)));
        var mesh = List(right, leaf, left, right, peer);

        Result[] corpus =
        [
            mesh,
            Seq(left, mesh, right, left),
            List(Seq(mesh), right, List(left, peer), mesh),
        ];

        foreach (var value in corpus)
        {
            var observations = Observations();
            var normalized = value.NormalizeObserved(observations);

            Assert.Equal(DistinctStructureNodes(value), observations.NormalizeStructureExpansionCount);
            AssertSemanticallyEqual(NaiveNormalize(value), normalized);
        }
    }

    [Fact]
    public void Normalize_NaiveRebuildExpandsOnePathPerFrame()
    {
        // Pins the oracle's own complexity, so the counts above are measured against a known
        // baseline rather than an assumed one: the old walk expanded 2^(depth+1) - 1 nodes.
        foreach (var depth in new[] { 4, 8, 12 })
        {
            var expansions = new StrongBox<long>(0);
            _ = NaiveNormalize(SharedDag(depth, RedundantLeaf()), expansions);

            // 2^(depth+1) - 1 spine expansions plus one redundant sequence per leaf occurrence.
            Assert.Equal(((1L << (depth + 1)) - 1) + (1L << depth), expansions.Value);
        }
    }

    [Fact]
    public void Normalize_LeavesAndEmptyStructuresExpandNothingExtra()
    {
        var observations = Observations();

        _ = Atom(7).NormalizeObserved(observations);
        _ = Str("text").NormalizeObserved(observations);
        Assert.Equal(0, observations.NormalizeStructureExpansionCount);

        // One flat structure of leaves: only the root itself is expanded.
        _ = List(Atom(1), Str("a")).NormalizeObserved(observations);
        Assert.Equal(1, observations.NormalizeStructureExpansionCount);

        // Nested empties are structures and are expanded, but they have no children to walk.
        _ = List(List(), Seq()).NormalizeObserved(observations);
        Assert.Equal(4, observations.NormalizeStructureExpansionCount);
    }

    [Fact]
    public void Normalize_MemoIsScopedToOneTopLevelCall()
    {
        var observations = Observations();
        var value = SharedDag(ShallowDepth, RedundantLeaf());

        var first = value.NormalizeObserved(observations);
        Assert.Equal(ShallowDepth + 2, observations.NormalizeStructureExpansionCount);

        // Nothing is cached on a Result: a second call recomputes the whole graph and must produce
        // the same value. The memo belongs to one operation and is discarded with it.
        var second = value.NormalizeObserved(observations);
        Assert.Equal(2 * (ShallowDepth + 2), observations.NormalizeStructureExpansionCount);
        AssertSemanticallyEqual(first, second);
    }

    [Fact]
    public void Normalize_IndependentEqualNodes_AreDistinctMemoEntries()
    {
        var observations = Observations();

        // Two children that are VALUE-EQUAL but share no reference. A memo keyed by KatLang value
        // equality (or its structural hash) would expand the second one zero times; reference
        // identity expands both.
        var left = RedundantLeaf();
        var right = RedundantLeaf();
        Assert.True(Result.ValueComparer.Equals(left, right));
        Assert.False(ReferenceEquals(left, right));

        var normalized = List(left, right).NormalizeObserved(observations);

        // Root + two independent leaves + their two independent singleton sequences.
        Assert.Equal(5, observations.NormalizeStructureExpansionCount);

        // ...and each keeps its own normalized node, so the equal-but-distinct inputs are not
        // silently unified.
        var items = Assert.IsType<Result.ListValue>(normalized).Items;
        Assert.False(ReferenceEquals(items[0], items[1]));
        AssertSemanticallyEqual(List(NormalLeaf(), NormalLeaf()), normalized);
    }

    [Fact]
    public void Normalize_DefaultEqualRecordClones_AreDistinctMemoEntries()
    {
        // A plain Dictionary<Result, Result> uses generated C# record equality, not KatLang's
        // ValueComparer. Independently constructed containers usually have distinct read-only
        // wrapper fields and do not expose that mutation. A record clone is a distinct Result that
        // shares the wrapper, so it is default-equal and deterministically catches removal of the
        // explicit ReferenceEqualityComparer.
        var left = Assert.IsType<Result.ListValue>(RedundantLeaf());
        var right = left with { };
        Assert.NotSame(left, right);
        Assert.True(left.Equals(right));
        Assert.Same(left.Items, right.Items);

        var observations = Observations();
        var normalized = Assert.IsType<Result.ListValue>(
            List(left, right).NormalizeObserved(observations));

        // Root + both distinct list references + their one shared singleton sequence.
        Assert.Equal(4, observations.NormalizeStructureExpansionCount);
        Assert.NotSame(normalized.Items[0], normalized.Items[1]);
        AssertSemanticallyEqual(List(NormalLeaf(), NormalLeaf()), normalized);
    }

    // ── Sharing preservation in the produced value ──────────────────────────────────────────

    [Fact]
    public void Normalize_AlreadyNormalValue_IsReturnedUnchanged()
    {
        // The strongest form of sharing preservation: when nothing changes, nothing is built, so
        // the input graph IS the output graph and every shared reference in it survives.
        var flatList = List(Atom(1), Str("a"));
        Assert.Same(flatList, flatList.Normalize());

        var flatSequence = Seq(Atom(1), Atom(2));
        Assert.Same(flatSequence, flatSequence.Normalize());

        var emptyList = Result.ListValue.TakeOwnership([]);
        Assert.Same(emptyList, emptyList.Normalize());

        var emptySequence = Result.SequenceValue.TakeOwnership([]);
        Assert.Same(emptySequence, emptySequence.Normalize());

        var dag = SharedDag(DeepDepth);
        Assert.Same(dag, dag.Normalize());
    }

    [Fact]
    public void Normalize_SharedDag_PreservesReferenceSharing()
    {
        var normalized = SharedDag(DeepDepth, RedundantLeaf()).Normalize();

        // The output is a DAG of the same shape: DeepDepth+1 structure nodes and 2 atoms, not the
        // 2^(DeepDepth+1) - 1 nodes the expanded tree spells out.
        Assert.Equal(DeepDepth + 1 + 2, DistinctNodes(normalized));

        var level = normalized;
        for (var i = 0; i < DeepDepth; i++)
        {
            var items = Assert.IsType<Result.ListValue>(level).Items;
            Assert.Same(items[0], items[1]);
            level = items[0];
        }

        AssertSemanticallyEqual(SharedDag(DeepDepth, NormalLeaf()), normalized);
    }

    [Fact]
    public void Normalize_SimpleSharedParent_ReusesOneNormalizedChild()
    {
        var child = RedundantLeaf();
        var normalized = Assert.IsType<Result.ListValue>(List(child, child).Normalize());

        Assert.Same(normalized.Items[0], normalized.Items[1]);
        AssertSemanticallyEqual(List(NormalLeaf(), NormalLeaf()), normalized);
    }

    [Fact]
    public void Normalize_DiamondDag_PreservesSharedNormalizedChild()
    {
        //         root
        //        /    \
        //       A      B
        //      / \    / \
        //     X   Y  X   Z
        var x = RedundantLeaf(1, 2);
        var y = RedundantLeaf(3, 4);
        var z = RedundantLeaf(5, 6);
        var a = List(x, y);
        var b = List(x, z);

        var observations = Observations();
        var normalized = Assert.IsType<Result.ListValue>(
            List(a, b).NormalizeObserved(observations));

        // root + A + B + X + Y + Z + one singleton sequence inside each of X, Y and Z.
        Assert.Equal(9, observations.NormalizeStructureExpansionCount);

        var normalizedA = Assert.IsType<Result.ListValue>(normalized.Items[0]);
        var normalizedB = Assert.IsType<Result.ListValue>(normalized.Items[1]);
        Assert.Same(normalizedA.Items[0], normalizedB.Items[0]);
        Assert.False(ReferenceEquals(normalizedA.Items[1], normalizedB.Items[1]));

        AssertSemanticallyEqual(
            List(
                List(NormalLeaf(1, 2), NormalLeaf(3, 4)),
                List(NormalLeaf(1, 2), NormalLeaf(5, 6))),
            normalized);
    }

    [Fact]
    public void Normalize_MixedSharedAndUnsharedSubgraphs()
    {
        var observations = Observations();
        var shared = SharedDag(3, RedundantLeaf());

        var normalized = List(shared, shared, List(Atom(9))).NormalizeObserved(observations);

        // Root (1) + the four spine nodes of the shared depth-3 graph expanded once for both
        // occurrences (4) + its one redundant sequence (1) + the unshared [9] (1).
        Assert.Equal(7, observations.NormalizeStructureExpansionCount);

        var items = Assert.IsType<Result.ListValue>(normalized).Items;
        Assert.Same(items[0], items[1]);
        AssertSemanticallyEqual(
            List(SharedDag(3, NormalLeaf()), SharedDag(3, NormalLeaf()), List(Atom(9))),
            normalized);
    }

    [Fact]
    public void Normalize_PathCopiesOnlyAncestorsOfTheChangedBranch()
    {
        //         root
        //        /    \
        //       A      B
        //      / \    / \
        //     X   Y  X   Z
        //
        // Only Y changes. A and root must be path-copied; B, X and Z are already normal and must
        // retain identity. This is stronger than checking only semantic equality or shared output.
        var x = Assert.IsType<Result.ListValue>(List(Atom(1), Atom(2)));
        var y = Assert.IsType<Result.SequenceValue>(Seq(Atom(3)));
        var z = Assert.IsType<Result.ListValue>(List(Atom(4), Atom(5)));
        var a = Assert.IsType<Result.ListValue>(List(x, y));
        var b = Assert.IsType<Result.ListValue>(List(x, z));
        var root = Assert.IsType<Result.ListValue>(List(a, b));

        var normalizedRoot = Assert.IsType<Result.ListValue>(root.Normalize());
        var normalizedA = Assert.IsType<Result.ListValue>(normalizedRoot.Items[0]);
        var normalizedB = Assert.IsType<Result.ListValue>(normalizedRoot.Items[1]);

        Assert.NotSame(root, normalizedRoot);
        Assert.NotSame(a, normalizedA);
        Assert.Same(b, normalizedB);
        Assert.Same(x, normalizedA.Items[0]);
        Assert.Same(x, normalizedB.Items[0]);
        Assert.Same(z, normalizedB.Items[1]);
        Assert.Same(y.Items[0], normalizedA.Items[1]);

        // Path copying must not mutate any source edge.
        Assert.Same(a, root.Items[0]);
        Assert.Same(b, root.Items[1]);
        Assert.Same(y, a.Items[1]);
    }

    [Fact]
    public void Normalize_ReconstructionHandlesEveryChangedChildPosition()
    {
        // Exercise the delayed destination-array allocation when the first change is early, in the
        // middle, or last, and when later unchanged/changed children follow it. Distinct atom values
        // make an index/backfill/order bug deterministic rather than merely structurally visible.
        int[][] changedPositionCases =
        [
            [0],
            [2],
            [4],
            [0, 4],
            [1, 2],
            [0, 2, 4],
        ];

        foreach (var changedPositions in changedPositionCases)
        {
            var changed = changedPositions.ToHashSet();
            var originalChildren = new Result[5];
            var expectedChildren = new Result[5];
            for (var i = 0; i < originalChildren.Length; i++)
            {
                var atom = Atom(i + 1);
                expectedChildren[i] = atom;
                originalChildren[i] = changed.Contains(i) ? Seq(atom) : atom;
            }

            var source = Assert.IsType<Result.ListValue>(List(originalChildren));
            var normalized = Assert.IsType<Result.ListValue>(source.Normalize());

            Assert.NotSame(source, normalized);
            Assert.Equal(expectedChildren.Length, normalized.Items.Count);
            for (var i = 0; i < expectedChildren.Length; i++)
            {
                Assert.Same(expectedChildren[i], normalized.Items[i]);
                Assert.Same(originalChildren[i], source.Items[i]);
            }
        }
    }

    // ── Context freedom: a node's normal form does not depend on where it is reached ─────────

    [Fact]
    public void Normalize_SameChildUnderSequenceAndListParents_NormalizesIdentically()
    {
        // The strongest adversary for a reference-only memo: ONE child reference reached from
        // parents of different KINDS, at different POSITIONS, beside different neighbours, and at
        // the root. Normalization reads only the node's own kind and its children's normal forms,
        // so every occurrence must produce the same value.
        var child = RedundantLeaf();
        var direct = child.Normalize();

        var underList = Assert.IsType<Result.ListValue>(List(child, Atom(0)).Normalize());
        var underSequence = Assert.IsType<Result.SequenceValue>(Seq(Atom(0), child).Normalize());
        var underSingletonSequence = Seq(child).Normalize();
        var underNestedMix = Assert.IsType<Result.ListValue>(
            List(Seq(child, Atom(0)), List(Seq(), child)).Normalize());

        AssertSemanticallyEqual(NormalLeaf(), direct);
        AssertSemanticallyEqual(direct, underList.Items[0]);
        AssertSemanticallyEqual(direct, underSequence.Items[1]);
        AssertSemanticallyEqual(direct, underSingletonSequence);

        var mixedLeft = Assert.IsType<Result.SequenceValue>(underNestedMix.Items[0]);
        var mixedRight = Assert.IsType<Result.ListValue>(underNestedMix.Items[1]);
        AssertSemanticallyEqual(direct, mixedLeft.Items[0]);
        AssertSemanticallyEqual(direct, mixedRight.Items[1]);

        // Within ONE call the shared occurrences are literally the same normalized reference.
        Assert.Same(mixedLeft.Items[0], mixedRight.Items[1]);
    }

    [Fact]
    public void Normalize_RootAndNestedOccurrencesAgree()
    {
        // Normalizing a node directly and reading the same node's normalized form out of an
        // enclosing structure must agree. Reference identity is deliberately NOT required across
        // calls: the memo lives for one call.
        foreach (var child in Corpus())
        {
            var direct = child.Normalize();
            var nested = Assert.IsType<Result.ListValue>(List(Atom(0), child).Normalize());
            AssertSemanticallyEqual(direct, nested.Items[1]);
        }
    }

    // ── Semantic equivalence against the naive oracle ────────────────────────────────────────

    /// <summary>Every supported value kind and the nesting/empty/singleton shapes around them.</summary>
    private static IEnumerable<Result> Corpus()
    {
        var shared = List(Seq(Atom(1)), Atom(2));
        var sharedSequence = Seq(Seq(Atom(8)), Atom(9));

        return
        [
            Atom(0),
            Atom(-3.5m),
            Str(string.Empty),
            Str("text"),
            Seq(),
            List(),
            Seq(Seq()),
            List(Seq()),
            Seq(List()),
            List(List()),
            Seq(Atom(1)),
            List(Atom(1)),
            Seq(Seq(Atom(1))),
            Seq(Seq(Seq(Atom(1)))),
            List(Seq(Seq(Atom(1)))),
            Seq(List(Atom(1))),
            List(List(Atom(1))),
            Seq(Atom(1), Atom(2), Atom(3)),
            List(Atom(1), Atom(2), Atom(3)),
            Seq(Atom(1), Str("a"), List(), Seq()),
            Seq(Seq(Atom(1), Atom(2)), Atom(3)),
            List(Seq(Atom(1), Atom(2)), Atom(3)),
            Seq(Seq(Atom(1)), Seq(Atom(2))),
            List(Seq(Atom(1)), Seq(Atom(2))),
            Seq(List(Seq(Atom(1))), Atom(2)),
            List(Seq(List(Seq(Atom(1)))), Str("s")),
            // Repeated references, both kinds of parent.
            List(shared, shared),
            Seq(shared, shared),
            Seq(sharedSequence, sharedSequence),
            List(shared, List(Seq(Atom(1)), Atom(2))),
            // Diamonds and a small doubling DAG.
            List(List(shared, sharedSequence), List(shared, Atom(4))),
            SharedDag(4),
            SharedDag(4, RedundantLeaf()),
            SharedDag(4, Seq(Atom(7))),
            // Deepest-leaf difference under otherwise identical sharing.
            List(SharedDag(3, RedundantLeaf(1, 2)), SharedDag(3, RedundantLeaf(1, 3))),
            // Wide flat and wide nested.
            Result.ListValue.TakeOwnership([.. Enumerable.Range(0, 64).Select(i => Atom(i))]),
            Result.SequenceValue.TakeOwnership([.. Enumerable.Range(0, 64).Select(i => Seq(Atom(i)))]),
        ];
    }

    [Fact]
    public void Normalize_MatchesTheNaiveRebuild_AcrossEveryValueShape()
    {
        foreach (var value in Corpus())
            AssertSemanticallyEqual(NaiveNormalize(value), value.Normalize());
    }

    [Fact]
    public void Normalize_PreservesKindAndItemOrder()
    {
        // Equality alone would not catch a reordering that happens to stay equal, nor a list that
        // normalized into a sequence, so the produced structure is read out directly.
        var normalized = Assert.IsType<Result.SequenceValue>(
            Seq(Seq(Atom(1)), List(Atom(2), Seq(Atom(3))), Seq(Atom(4), Atom(5)), Str("z")).Normalize());

        Assert.Equal(4, normalized.Items.Count);
        Assert.Equal(Atom(1), normalized.Items[0]);

        var list = Assert.IsType<Result.ListValue>(normalized.Items[1]);
        Assert.Equal([Atom(2), Atom(3)], list.Items);

        var inner = Assert.IsType<Result.SequenceValue>(normalized.Items[2]);
        Assert.Equal([Atom(4), Atom(5)], inner.Items);
        Assert.Equal(Str("z"), normalized.Items[3]);
    }

    [Fact]
    public void Normalize_SharedSubgraphsInDifferentPositionsKeepTheirOrder()
    {
        var a = List(Seq(Atom(1)), Atom(2));
        var b = List(Seq(Atom(3)), Atom(4));
        var normalized = Assert.IsType<Result.SequenceValue>(Seq(a, b, a, b, a).Normalize());

        AssertSemanticallyEqual(
            Seq(NormalLeaf(1, 2), NormalLeaf(3, 4), NormalLeaf(1, 2), NormalLeaf(3, 4), NormalLeaf(1, 2)),
            normalized);
        Assert.Same(normalized.Items[0], normalized.Items[2]);
        Assert.Same(normalized.Items[0], normalized.Items[4]);
        Assert.Same(normalized.Items[1], normalized.Items[3]);
        Assert.False(ReferenceEquals(normalized.Items[0], normalized.Items[1]));
    }

    [Fact]
    public void Normalize_ListAndSequenceBoundariesStayDistinct()
    {
        var shared = Seq(Atom(1));

        // A singleton SEQUENCE collapses wherever it appears; a singleton LIST never does, and the
        // two never normalize to the same value even over the same shared child. The enclosing
        // two-element parents are NOT singletons, so they survive as their own kind.
        AssertSemanticallyEqual(Seq(Atom(1), Atom(1)), Seq(shared, shared).Normalize());
        AssertSemanticallyEqual(List(Atom(1), Atom(1)), List(shared, shared).Normalize());
        AssertSemanticallyEqual(Atom(1), Seq(Seq(shared)).Normalize());
        AssertSemanticallyEqual(List(Atom(1)), List(Seq(shared)).Normalize());
        Assert.False(Result.ValueComparer.Equals(
            Seq(List(shared)).Normalize(),
            Seq(Seq(shared)).Normalize()));
        AssertSemanticallyEqual(List(Atom(1)), Seq(List(shared)).Normalize());
        AssertSemanticallyEqual(Atom(1), Seq(Seq(shared)).Normalize());
    }

    [Fact]
    public void Normalize_EmptyBoundariesSurviveSharing()
    {
        var emptySequence = Seq();
        var emptyList = List();

        // The empty sequence is not a singleton, so it never collapses; the empty list is exact.
        Assert.Same(emptySequence, emptySequence.Normalize());
        Assert.Same(emptyList, emptyList.Normalize());

        // A sequence holding one empty sequence IS a singleton and collapses to it.
        AssertSemanticallyEqual(Seq(), Seq(emptySequence).Normalize());
        AssertSemanticallyEqual(Seq(), Seq(Seq(Seq())).Normalize());
        AssertSemanticallyEqual(List(), Seq(emptyList).Normalize());

        // The same shared empty reached beside a shared non-empty keeps both boundaries.
        AssertSemanticallyEqual(
            List(Seq(), List(), Seq(), List()),
            List(emptySequence, emptyList, emptySequence, emptyList).Normalize());
    }

    [Fact]
    public void Normalize_DeepestLeafDifference_IsPreserved()
    {
        // Two graphs sharing everything except the single deepest leaf. A memo that keyed on the
        // structural hash or on the enclosing shape would unify them.
        var left = SharedDag(ShallowDepth, RedundantLeaf(1, 2)).Normalize();
        var right = SharedDag(ShallowDepth, RedundantLeaf(1, 3)).Normalize();

        Assert.False(Result.ValueComparer.Equals(left, right));
        AssertSemanticallyEqual(SharedDag(ShallowDepth, NormalLeaf(1, 2)), left);
        AssertSemanticallyEqual(SharedDag(ShallowDepth, NormalLeaf(1, 3)), right);

        // ...and inside ONE normalization, where the two graphs meet under one root.
        var combined = Assert.IsType<Result.ListValue>(
            List(SharedDag(3, RedundantLeaf(1, 2)), SharedDag(3, RedundantLeaf(1, 3))).Normalize());
        Assert.False(Result.ValueComparer.Equals(combined.Items[0], combined.Items[1]));
    }

    [Fact]
    public void Normalize_SharedAndExpandedEquivalentGraphs_AreSemanticallyEqual()
    {
        // Sharing topology is not part of the value: the DAG and the tree its paths spell out
        // normalize to equal values, and (under the memoized hash contract) to equal hashes.
        const int depth = 6;
        var shared = SharedDag(depth, RedundantLeaf());
        var expanded = ExpandToTree(shared);

        Assert.False(ReferenceEquals(shared, expanded));
        AssertSemanticallyEqual(shared, expanded);
        AssertSemanticallyEqual(shared.Normalize(), expanded.Normalize());
        AssertSemanticallyEqual(NaiveNormalize(expanded), shared.Normalize());

        // The shared input keeps its compact output; the rebuilt tree keeps its expanded one.
        Assert.Equal(depth + 1 + 2, DistinctNodes(shared.Normalize()));
        Assert.Equal((1 << (depth + 1)) - 1 + 2, DistinctNodes(expanded.Normalize()));
    }

    /// <summary>Rebuilds <paramref name="value"/> as a TREE, one fresh node per path.</summary>
    private static Result ExpandToTree(Result value) => value switch
    {
        Result.SequenceValue(var items) =>
            Result.SequenceValue.TakeOwnership([.. items.Select(ExpandToTree)]),
        Result.ListValue(var items) =>
            Result.ListValue.TakeOwnership([.. items.Select(ExpandToTree)]),
        _ => value,
    };

    // ── Scalar views decide from sequence shape ──────────────────────────────────────────────
    //
    // Result.AsNum and Result.AsBool (Lean asInt? / asBool?) are DEFINED by normalization: a value
    // has a number or a truth value exactly when its normal form is that scalar. A sequence's
    // normal form keeps its item count and collapses only at one item, and a list never
    // collapses, so the views peel singleton sequence wrappers and decide at the first value that
    // is not one. They never read past that boundary and never normalize. Full normalization stays
    // the oracle here, and the views' work — ScalarViewSequenceInspectionCount, one per sequence
    // whose count they read — is the unary depth plus at most one deciding boundary.

    private const int DeepUnaryDepth = 100_000;

    private static Decimal128 D(string text) => Decimal128.Parse(text, NumberStyles.Float, CultureInfo.InvariantCulture);

    /// <summary>The 128 bits of a number: its representation (quantum, zero sign), not merely its value.</summary>
    private static UInt128 Bits(Decimal128 value) => Unsafe.BitCast<Decimal128, UInt128>(value);

    /// <summary><paramref name="depth"/> redundant singleton sequence wrappers around <paramref name="terminal"/>.</summary>
    private static Result Spine(int depth, Result terminal)
    {
        var node = terminal;
        for (var i = 0; i < depth; i++)
            node = Seq(node);
        return node;
    }

    /// <summary>What the scalar views must answer, read off a full normal form.</summary>
    private static (Decimal128? Number, bool? Truth) ViewsOfNormalForm(Result normal) => normal switch
    {
        Result.Atom(var number) => (number, null),
        Result.Bool(var truth) => (null, truth),
        _ => (null, null),
    };

    /// <summary>
    /// Both views of <paramref name="value"/> against <paramref name="normal"/>, its full normal
    /// form: the same answer (a number bit for bit), exactly <paramref name="inspections"/>
    /// sequence reads per view, no normalization, and the public observer-free views agreeing.
    /// </summary>
    private static void AssertScalarViews(Result value, Result normal, long inspections)
    {
        var (number, truth) = ViewsOfNormalForm(normal);
        var observations = Observations();

        var observedNumber = value.AsNumObserved(observations);
        Assert.Equal(inspections, observations.ScalarViewSequenceInspectionCount);
        var observedTruth = value.AsBoolObserved(observations);
        Assert.Equal(2 * inspections, observations.ScalarViewSequenceInspectionCount);
        Assert.Equal(0, observations.NormalizeStructureExpansionCount);

        var publicNumber = value.AsNum();
        Assert.Equal(number.HasValue, observedNumber.HasValue);
        Assert.Equal(number.HasValue, publicNumber.HasValue);
        if (number is { } expected)
        {
            Assert.Equal(Bits(expected), Bits(observedNumber!.Value));
            Assert.Equal(Bits(expected), Bits(publicNumber!.Value));
        }

        Assert.Equal(truth, observedTruth);
        Assert.Equal(truth, value.AsBool());
    }

    private static void AssertScalarViews(Result value, long inspections)
        => AssertScalarViews(value, value.Normalize(), inspections);

    /// <summary>
    /// One generated value, with facts derived COMPOSITIONALLY from its construction rather than by
    /// peeling: <see cref="Inspections"/> is the work the scalar views are allowed (a singleton
    /// sequence costs one plus its child's, any other sequence one, a list or a leaf nothing), and
    /// <see cref="TreeSize"/> the path-expanded node count (saturating), which gates the recursive
    /// oracle.
    /// </summary>
    private readonly record struct GeneratedValue(Result Value, long Inspections, long TreeSize);

    /// <summary>
    /// Small acyclic values from a seeded pool: every new node takes its children either from the
    /// pool — SHARED descendants, reachable from several parents and sometimes twice from one — or
    /// as fresh leaves, DISTINCT descendants that may be value-equal to shared ones. Leaves mix
    /// numbers (a negative zero, a quantum-bearing and an exponent-bearing one), Booleans and a
    /// string; half the nodes are redundant singleton wrappers, so unary spines form over every
    /// kind of terminal, including lists holding one scalar and boundaries whose children are
    /// themselves normalizable.
    /// </summary>
    private static List<GeneratedValue> GenerateAcyclicValues(int seed, int count)
    {
        var random = new Random(seed);
        Func<Result>[] leaves =
        [
            () => new Result.Atom(D("5")),
            () => new Result.Atom(D("1.50")),
            () => new Result.Atom(D("-0")),
            () => new Result.Atom(D("1E+3")),
            () => new Result.Bool(true),
            () => new Result.Bool(false),
            () => new Result.Str("x"),
        ];

        var pool = new List<GeneratedValue>();
        foreach (var leaf in leaves)
            pool.Add(new GeneratedValue(leaf(), 0, 1));

        GeneratedValue Child()
            => random.Next(4) == 0
                ? new GeneratedValue(leaves[random.Next(leaves.Length)](), 0, 1)
                : pool[random.Next(pool.Count)];

        GeneratedValue[] Children(int width)
        {
            var children = new GeneratedValue[width];
            for (var i = 0; i < width; i++)
                children[i] = i > 0 && random.Next(4) == 0 ? children[i - 1] : Child();
            return children;
        }

        static long TreeSize(GeneratedValue[] children)
            => Math.Min(1 + children.Sum(child => child.TreeSize), 1L << 40);

        while (pool.Count < count)
        {
            var kind = random.Next(10);
            if (kind < 5)
            {
                var child = Child();
                pool.Add(new GeneratedValue(Seq(child.Value), child.Inspections + 1, TreeSize([child])));
            }
            else if (kind < 7)
            {
                var children = Children(random.Next(3) == 0 ? 0 : 2 + random.Next(3));
                pool.Add(new GeneratedValue(Seq([.. children.Select(c => c.Value)]), 1, TreeSize(children)));
            }
            else
            {
                var children = Children(random.Next(4));
                pool.Add(new GeneratedValue(List([.. children.Select(c => c.Value)]), 0, TreeSize(children)));
            }
        }

        return pool;
    }

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(3)]
    public void ScalarViews_AgreeWithFullNormalization_OnGeneratedAcyclicValues(int seed)
    {
        int numbers = 0, negativeZeros = 0, truths = 0, sequenceRejections = 0, listRejections = 0, recursiveChecks = 0;
        long deepestSpine = 0;

        foreach (var generated in GenerateAcyclicValues(seed, 800))
        {
            var normal = generated.Value.Normalize();
            if (generated.TreeSize <= 2_000)
            {
                // The production normalizer against its path-expanding replica.
                AssertSemanticallyEqual(NaiveNormalize(generated.Value), normal);
                recursiveChecks++;
            }

            AssertScalarViews(generated.Value, normal, generated.Inspections);

            deepestSpine = Math.Max(deepestSpine, generated.Inspections);
            switch (normal)
            {
                case Result.Atom(var number):
                    numbers++;
                    if (number == Decimal128.Zero && Decimal128.IsNegative(number))
                        negativeZeros++;
                    break;
                case Result.Bool:
                    truths++;
                    break;
                case Result.SequenceValue:
                    sequenceRejections++;
                    break;
                case Result.ListValue:
                    listRejections++;
                    break;
            }
        }

        // The generator reaches every deciding shape, so agreement is not vacuous.
        Assert.True(numbers > 20 && negativeZeros > 0 && truths > 20, $"numbers {numbers}, -0 {negativeZeros}, truths {truths}");
        Assert.True(sequenceRejections > 20 && listRejections > 20, $"sequences {sequenceRejections}, lists {listRejections}");
        Assert.True(deepestSpine >= 4, $"deepest unary spine {deepestSpine}");
        Assert.True(recursiveChecks > 200, $"recursive oracle checks {recursiveChecks}");
    }

    [Fact]
    public void ScalarViews_DecideAtTheFirstValueThatIsNotASingletonSequence()
    {
        var one = Atom(1);
        var redundantOne = Seq(Seq(one));

        // A direct scalar or list reads no sequence at all.
        AssertScalarViews(Atom(5), 0);
        AssertScalarViews(new Result.Bool(true), 0);
        AssertScalarViews(Str("5"), 0);
        // A list wrapping one scalar never collapses: no number, no truth value.
        AssertScalarViews(List(Atom(5)), 0);
        AssertScalarViews(List(new Result.Bool(true)), 0);
        Assert.Null(List(Atom(5)).AsNum());
        Assert.Null(List(new Result.Bool(true)).AsBool());

        // A unary spine reads one sequence per wrapper; a spine ending in a list stops there.
        AssertScalarViews(Seq(one), 1);
        AssertScalarViews(Spine(64, new Result.Bool(false)), 64);
        AssertScalarViews(Spine(64, List(Atom(5))), 64);
        AssertScalarViews(Seq(List(Seq(Atom(5)))), 1);

        // Empty and multi-item sequences decide by their count alone: one read, then null.
        AssertScalarViews(Seq(), 1);
        AssertScalarViews(Spine(64, Seq()), 65);
        AssertScalarViews(Seq(Atom(1), Atom(2)), 1);
        // ...even when every child is itself normalizable to a scalar, shared or distinct.
        AssertScalarViews(Seq(redundantOne, redundantOne), 1);
        AssertScalarViews(Seq(redundantOne, Seq(Seq(Atom(1)))), 1);
        AssertScalarViews(Seq(Seq(Seq(new Result.Bool(true)), Seq(new Result.Bool(true)))), 2);
        Assert.Null(Seq(redundantOne, redundantOne).AsNum());

        // Numbers and Booleans stay distinct through any spine.
        Assert.Null(Spine(8, new Result.Bool(true)).AsNum());
        Assert.True(Spine(8, new Result.Bool(true)).AsBool());
        Assert.Null(Spine(8, Atom(1)).AsBool());
        Assert.Null(Spine(8, Atom(0)).AsBool());
        Assert.Equal((Decimal128)1, Spine(8, Atom(1)).AsNum());
    }

    [Fact]
    public void ScalarViews_KeepTheExactDecimal128Payload()
    {
        // The view returns the stored number itself: zero sign, quantum and exponent included.
        foreach (var text in new[] { "-0", "0.00", "-0.0", "1.50", "1.500", "1E+3", "-12.3400" })
        {
            var number = D(text);
            foreach (var depth in new[] { 0, 1, 7 })
            {
                var value = Spine(depth, new Result.Atom(number));
                AssertScalarViews(value, depth);
                Assert.Equal(Bits(number), Bits(value.AsNum()!.Value));
            }
        }

        Assert.True(Decimal128.IsNegative(Spine(3, new Result.Atom(D("-0"))).AsNum()!.Value));
        Assert.NotEqual(Bits(D("1.5")), Bits(Spine(3, new Result.Atom(D("1.50"))).AsNum()!.Value));
    }

    [Fact]
    public void ScalarViews_PeelADeepUnarySpineIteratively_InUnaryDepthWork()
    {
        // Far deeper than any native recursion survives; the work is exactly the unary depth
        // (plus the deciding boundary when it is a sequence), whatever ends the spine.
        var quantum = new Result.Atom(D("1.50"));
        var observations = Observations();

        Assert.Equal(Bits(quantum.Value), Bits(Spine(DeepUnaryDepth, quantum).AsNumObserved(observations)!.Value));
        Assert.Equal(DeepUnaryDepth, observations.ScalarViewSequenceInspectionCount);

        observations = Observations();
        Assert.False(Spine(DeepUnaryDepth, new Result.Bool(false)).AsBoolObserved(observations));
        Assert.Equal(DeepUnaryDepth, observations.ScalarViewSequenceInspectionCount);

        observations = Observations();
        var endsInList = Spine(DeepUnaryDepth, List(Atom(1)));
        Assert.Null(endsInList.AsNumObserved(observations));
        Assert.Null(endsInList.AsBoolObserved(observations));
        Assert.Equal(2L * DeepUnaryDepth, observations.ScalarViewSequenceInspectionCount);

        observations = Observations();
        var endsInPair = Spine(DeepUnaryDepth, Seq(Atom(1), Atom(2)));
        Assert.Null(endsInPair.AsNumObserved(observations));
        Assert.Null(endsInPair.AsBoolObserved(observations));
        Assert.Equal(2L * (DeepUnaryDepth + 1), observations.ScalarViewSequenceInspectionCount);
        Assert.Equal(0, observations.NormalizeStructureExpansionCount);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(2)]
    [InlineData(16)]
    [InlineData(1024)]
    [InlineData(100_000)]
    public void ScalarViews_RejectAtTheDecidingBoundary_IndependentOfItsWidth(int width)
    {
        // Every item normalizes to a scalar — even items share ONE redundant wrapper, odd items are
        // distinct ones — so only the boundary's own count decides. A view that read or normalized
        // the children would scale with the width; this one reads the same sequences at every width.
        var shared = Seq(Seq(Atom(1)));
        var items = new Result[width];
        for (var i = 0; i < width; i++)
            items[i] = i % 2 == 0 ? shared : Seq(Seq(new Result.Bool(i % 4 == 1)));
        var boundary = Result.SequenceValue.TakeOwnership(items);

        foreach (var unaryDepth in new[] { 0, 1, 64 })
        {
            var value = Spine(unaryDepth, boundary);
            var observations = Observations();
            Assert.Null(value.AsNumObserved(observations));
            Assert.Null(value.AsBoolObserved(observations));
            Assert.Equal(2L * (unaryDepth + 1), observations.ScalarViewSequenceInspectionCount);
            Assert.Equal(0, observations.NormalizeStructureExpansionCount);
        }

        // The oracle: full normalization keeps the width-item boundary, so it is never a scalar.
        if (width <= 1024)
        {
            var normal = Assert.IsType<Result.SequenceValue>(Spine(64, boundary).Normalize());
            Assert.Equal(width, normal.Items.Count);
        }
    }

    [Fact]
    public void ScalarViews_AllocateNothingThatGrowsWithWidthOrDepth()
    {
        // The reported shape — one single-number list per item — at the maximum collection width
        // behind a unary prefix, and a deep unary spine ending in a number.
        var wide = Spine(64, Result.SequenceValue.TakeOwnership(
            [.. Enumerable.Range(0, 100_000).Select(i => List(Atom(i)))]));
        var deep = Spine(DeepUnaryDepth, Atom(7));

        for (var i = 0; i < 4; i++)
        {
            _ = wide.AsNum();
            _ = wide.AsBool();
            _ = deep.AsNum();
            _ = deep.AsBool();
        }

        var answered = 0;
        var before = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < 32; i++)
        {
            if (wide.AsNum() is not null)
                answered++;
            if (wide.AsBool() is not null)
                answered++;
            if (deep.AsNum() is not null)
                answered++;
            if (deep.AsBool() is not null)
                answered++;
        }

        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.Equal(32, answered);
        // The views allocate nothing: a Release harness measured 0 bytes for both shapes. The
        // in-process counter can still report up to one ~8 KiB allocation quantum during a
        // background GC (dotnet/runtime#134724), and no ArrayPool buffer is rented, so 16 KiB
        // allows two quanta. The normalizing views allocated about 26.5 MB per AsNum + AsBool pair
        // at width 100,000 and about 37 MB per pair at unary depth 100,000.
        Assert.True(allocated <= 16 * 1024, $"128 scalar-view reads allocated {allocated:N0} bytes");
    }

    // ── Language-level regression ────────────────────────────────────────────────────────────

    /// <summary>
    /// The doubling DAG built by an ordinary in-budget loop, the same recipe
    /// <see cref="SharedValueGraphComplexityTests"/> uses: <c>Wrap</c> stores its ONE bound argument
    /// in both element slots, so each step adds one node reachable through twice as many paths.
    /// </summary>
    private static string DagProgram(string body, int depth = DeepDepth)
        => $"""
            Wrap = [x, x]
            A = Wrap(1).repeat({depth})
            {body}
            """;

    private static Result RunValue(string source)
    {
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

        var plain = Evaluator.Run(expr);
        if (plain.IsError)
            Assert.Fail($"Expected success but got error: {plain.Error}");

        // The fix lives at the Result level, so the counted entry point must agree exactly.
        var counted = Evaluator.RunCounted(expr);
        if (counted.IsError)
            Assert.Fail($"Expected counted success but got error: {counted.Error}");
        Assert.True(Result.ValueComparer.Equals(plain.Value, counted.Value.Value));

        return plain.Value!;
    }

    [Fact]
    public void IndexingSharedValue_DoesNotExpandNormalizeByPath()
    {
        // `A[0]` selects one shared child and projects its content through
        // Result.FromItems -> Result.Normalize. Before the memo this rebuilt the selected
        // sub-DAG path by path: 2^depth nodes, unreachable at depth 40.
        var selected = RunValue(DagProgram("A[0]"));

        // The projected value is A's shared child: DeepDepth-1 list levels over one atom leaf, and
        // still a DAG. The path-expanding rebuild produced 2^(DeepDepth-1) list nodes instead.
        Assert.Equal((DeepDepth - 1) + 1, DistinctNodes(selected));

        var level = selected;
        for (var i = 0; i < DeepDepth - 1; i++)
        {
            var items = Assert.IsType<Result.ListValue>(level).Items;
            Assert.Equal(2, items.Count);
            Assert.Same(items[0], items[1]);
            level = items[0];
        }

        Assert.Equal(new Result.Atom(1), level);
    }

    [Fact]
    public void IndexingSharedValue_KeepsItsScalarProjection()
    {
        // A scalar answer, so no rendering of the graph can confound the measurement.
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(DagProgram("(A[0]).count")).Root);

        var plain = Evaluator.RunFlat(expr);
        if (plain.IsError)
            Assert.Fail($"Expected success but got error: {plain.Error}");
        Assert.Equal([2m], plain.Value);

        var counted = Evaluator.RunCounted(expr);
        if (counted.IsError)
            Assert.Fail($"Expected counted success but got error: {counted.Error}");
        Assert.Equal([2m], counted.Value.Value.ToHostAtoms());
    }

    [Fact]
    public void IteratingSharedValues_DoesNotExpandNormalizeByPath()
    {
        // The other production entry that once normalized selected values: higher-order iteration
        // passed each iterated item through the former projection -> Result.FromItems. Selection is
        // now a value boundary (the item is passed exactly as stored), and this pins that the
        // callback path still never expands the shared graph by traversal path.
        var expr = new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid(DagProgram("Id(q) = q\nmap((A, A), Id).count")).Root);

        var plain = Evaluator.RunFlat(expr);
        if (plain.IsError)
            Assert.Fail($"Expected success but got error: {plain.Error}");
        Assert.Equal([2m], plain.Value);

        var counted = Evaluator.RunCounted(expr);
        if (counted.IsError)
            Assert.Fail($"Expected counted success but got error: {counted.Error}");
        Assert.Equal([2m], counted.Value.Value.ToHostAtoms());
    }

    [Fact]
    public void SequenceValuedIndexSelector_DoesNotNormalizeSharedDagByPath()
    {
        // ExpectInt -> Result.AsNum once normalized sequence-valued operands before rejecting a
        // non-scalar. The selector repeats the same depth-40 DAG twice; before the memo, merely
        // deciding that it was not one number expanded both occurrences into enormous trees. The
        // view now decides from the selector's two-item count alone (the scalar-view section
        // above); this pins the source route and its diagnostic.
        var expr = new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid(DagProgram("[1][(A, A)]")).Root);

        // A structured selector is a value of the wrong KIND (Q-27); its bounded diagnostic
        // rendering must not expand the shared DAG either.
        var plain = Evaluator.Run(expr);
        Assert.True(plain.IsError);
        Assert.IsType<EvalError.TypeMismatch>(plain.Error);

        var counted = Evaluator.RunCounted(expr);
        Assert.True(counted.IsError);
        Assert.IsType<EvalError.TypeMismatch>(counted.Error);
    }

    [Fact]
    public void SelectedSharedValueStaysUsableInLaterOperations()
    {
        // Sharing destroyed by a projection is not merely slow: every later walk over the projected
        // value inherits the expanded tree. These consumers are DAG-bounded only if the projection
        // handed them a DAG.
        var expr = new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid(DagProgram("B = A[0]\nB == A[0], B != A[0], distinct((B, A[0])).count")).Root);

        var plain = Evaluator.Run(expr);
        if (plain.IsError)
            Assert.Fail($"Expected success but got error: {plain.Error}");
        Assert.Equal(
            Result.FromItems([new Result.Bool(true), new Result.Bool(false), new Result.Atom(1)]),
            plain.Value,
            Result.ValueComparer);
    }
}
