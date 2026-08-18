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

    // ── Language-level regression ────────────────────────────────────────────────────────────

    /// <summary>
    /// The doubling DAG built by an ordinary in-budget loop, the same recipe
    /// <see cref="SharedValueGraphComplexityTests"/> uses: <c>Wrap</c> stores its ONE bound argument
    /// in both element slots, so each step adds one node reachable through twice as many paths.
    /// </summary>
    private static string DagProgram(string body, int depth = DeepDepth)
        => $"""
            Wrap = [x, x]
            A = Wrap.repeat({depth}, 1)
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
        // `A:0` selects one shared child and projects its content through
        // Result.FromItems -> Result.Normalize. Before the memo this rebuilt the selected
        // sub-DAG path by path: 2^depth nodes, unreachable at depth 40.
        var selected = RunValue(DagProgram("A:0"));

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
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(DagProgram("(A:0).count")).Root);

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
        // The other production entry into the same projection: higher-order iteration projects each
        // iterated item through Result.ProjectIteratedContent -> Result.FromItems.
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
        // ExpectInt -> Result.AsNum normalizes sequence-valued operands before rejecting a
        // non-scalar. The selector repeats the same depth-40 DAG twice; before the memo, merely
        // deciding that it was not one number expanded both occurrences into enormous trees.
        var expr = new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid(DagProgram("[1]:(A, A)")).Root);

        var plain = Evaluator.Run(expr);
        Assert.True(plain.IsError);
        Assert.IsType<EvalError.BadArity>(plain.Error);

        var counted = Evaluator.RunCounted(expr);
        Assert.True(counted.IsError);
        Assert.IsType<EvalError.BadArity>(counted.Error);
    }

    [Fact]
    public void SelectedSharedValueStaysUsableInLaterOperations()
    {
        // Sharing destroyed by a projection is not merely slow: every later walk over the projected
        // value inherits the expanded tree. These consumers are DAG-bounded only if the projection
        // handed them a DAG.
        var expr = new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid(DagProgram("B = A:0\nB == A:0, B != A:0, distinct((B, A:0)).count")).Root);

        var plain = Evaluator.RunFlat(expr);
        if (plain.IsError)
            Assert.Fail($"Expected success but got error: {plain.Error}");
        Assert.Equal([1m, 0m, 1m], plain.Value);
    }
}
