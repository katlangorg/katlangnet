namespace KatLang.Tests;

/// <summary>
/// A <see cref="Result"/> value is a DAG, not a tree: an immutable child may be shared by many
/// parents, so <c>W = [x, x]</c> applied n times reaches n+1 distinct nodes through 2^n
/// root-to-leaf paths. Structural equality and structural hashing must therefore do work
/// proportional to the distinct nodes (equality: distinct ordered reference PAIRS) they must
/// decide, never to the paths that reach them — a path-expanding walk is exponential in n on
/// values an ordinary in-budget loop builds, and no evaluation step budget bounds it, because the
/// blow-up happens inside ONE value-level operation.
///
/// <para>The work counts here are exact and deterministic, measured through a passive
/// operation-scoped <see cref="ValueTraversalObservations"/> handed to
/// <see cref="Result.CreateObservedValueComparer"/>; the production comparer carries no observer.
/// Timing is deliberately not a pass/fail signal.</para>
/// </summary>
public class SharedValueGraphComplexityTests
{
    /// <summary>Depths chosen so the previous path-expanding walks differ by 2^20 between them.</summary>
    private const int ShallowDepth = 20;

    private const int DeepDepth = 40;

    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result List(params Result[] items) => Result.ListValue.TakeOwnership(items);

    private static Result Seq(params Result[] items) => Result.SequenceValue.TakeOwnership(items);

    /// <summary>
    /// The doubling DAG: <c>P0 = [leafA, leafB]</c>, <c>Pk = [P(k-1), P(k-1)]</c>. Every call builds
    /// FRESH objects, so two graphs from two calls are structurally equal while sharing no
    /// reference — the case the <see cref="object.ReferenceEquals"/> fast path cannot help with.
    /// A graph of depth n has exactly n+1 distinct structure nodes and 2^n root-to-leaf paths.
    /// </summary>
    private static Result SharedDag(int depth, decimal leafA = 1, decimal leafB = 2)
    {
        var node = List(Atom(leafA), Atom(leafB));
        for (var i = 0; i < depth; i++)
            node = List(node, node);
        return node;
    }

    private static (IEqualityComparer<Result> Comparer, ValueTraversalObservations Observations) Observed()
    {
        var observations = new ValueTraversalObservations();
        return (Result.CreateObservedValueComparer(observations), observations);
    }

    // ── Test A: one equality operation expands each reference pair at most once ──────────────

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public void Equality_DagPair_IsVisitedAtMostOnce(int depth)
    {
        var (comparer, observations) = Observed();

        Assert.True(comparer.Equals(SharedDag(depth), SharedDag(depth)));

        // The pairs reachable from the root are exactly {(Pk, Qk) : k = 0..depth}: depth+1 of them.
        // Every one must be expanded at least once to decide equality, so an exact count of
        // depth+1 IS the at-most-once property. The path-expanding walk expanded 2^(depth+1) - 1.
        Assert.Equal(depth + 1, observations.EqualityPairExpansionCount);
    }

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public void Equality_DagPair_DeepestLeafMismatchIsFoundWithoutPathExpansion(int depth)
    {
        var (comparer, observations) = Observed();

        // Identical except for the second atom of the single shared deepest leaf.
        Assert.False(comparer.Equals(SharedDag(depth), SharedDag(depth, leafB: 3)));

        // The walk descends the first branch of each level and reports the mismatch there.
        Assert.Equal(depth + 1, observations.EqualityPairExpansionCount);
    }

    [Fact]
    public void Equality_PairWorkGrowsLinearlyWithGraphDepth()
    {
        var (shallowComparer, shallow) = Observed();
        var (deepComparer, deep) = Observed();

        Assert.True(shallowComparer.Equals(SharedDag(ShallowDepth), SharedDag(ShallowDepth)));
        Assert.True(deepComparer.Equals(SharedDag(DeepDepth), SharedDag(DeepDepth)));

        // Twenty more levels cost twenty more pair expansions, not 2^20 times as many.
        Assert.Equal(
            DeepDepth - ShallowDepth,
            deep.EqualityPairExpansionCount - shallow.EqualityPairExpansionCount);
    }

    // ── Equality correctness across the shapes the memo could break ──────────────────────────

    [Fact]
    public void Equality_ReferenceFastPathDecidesWithoutAnyExpansion()
    {
        var (comparer, observations) = Observed();
        var value = SharedDag(DeepDepth);

        Assert.True(comparer.Equals(value, value));
        Assert.Equal(0, observations.EqualityPairExpansionCount);
    }

    [Fact]
    public void Equality_SharedLeftNodeIsDecidedAgainstEachRightNodeSeparately()
    {
        // The memo key is the ORDERED PAIR of references, never one side alone: the same left node
        // is compared against an equal right node and then against an unequal one. A memo keyed on
        // the left reference (or on value equality) would wrongly report equal here.
        var (comparer, observations) = Observed();
        var shared = List(Atom(1), Atom(2));

        Assert.False(comparer.Equals(
            List(shared, shared),
            List(List(Atom(1), Atom(2)), List(Atom(1), Atom(3)))));

        // Root pair, then (shared, equal) and (shared, different) as two distinct pairs.
        Assert.Equal(3, observations.EqualityPairExpansionCount);
    }

    [Fact]
    public void Equality_RepeatedReferenceOnOneSideOnly()
    {
        var (comparer, observations) = Observed();
        var shared = List(Atom(1), Atom(2));

        // Shared twice on the left, two independent equal copies on the right: two distinct pairs.
        Assert.True(comparer.Equals(
            List(shared, shared),
            List(List(Atom(1), Atom(2)), List(Atom(1), Atom(2)))));
        Assert.Equal(3, observations.EqualityPairExpansionCount);
    }

    [Fact]
    public void Equality_MixedSharedAndUnsharedSubgraphs()
    {
        var (comparer, observations) = Observed();
        var leftShared = SharedDag(3);
        var rightShared = SharedDag(3);

        Assert.True(comparer.Equals(
            List(leftShared, leftShared, List(Atom(9))),
            List(rightShared, rightShared, List(Atom(9)))));

        // Root pair (1) + the four pairs of the shared depth-3 chain, expanded once for the two
        // occurrences (4) + the unshared [9] pair (1).
        Assert.Equal(6, observations.EqualityPairExpansionCount);
    }

    [Fact]
    public void Equality_DifferentLengthsAndKindsStayUnequal()
    {
        var (comparer, observations) = Observed();

        // Length mismatch is decided by the count check, before any expansion.
        Assert.False(comparer.Equals(List(Atom(1), Atom(2)), List(Atom(1))));
        Assert.Equal(0, observations.EqualityPairExpansionCount);

        // A list never equals a sequence value with the same elements, at the root...
        Assert.False(comparer.Equals(List(Atom(1), Atom(2)), Seq(Atom(1), Atom(2))));
        Assert.Equal(0, observations.EqualityPairExpansionCount);

        // ...nor nested, where the kinds are compared after the enclosing pair is expanded.
        Assert.False(comparer.Equals(List(Seq(Atom(1))), List(List(Atom(1)))));
        Assert.Equal(1, observations.EqualityPairExpansionCount);

        // Leaf kinds stay distinct too.
        Assert.False(comparer.Equals(new Result.Str("1"), Atom(1)));
        Assert.False(comparer.Equals(List(new Result.Str("a")), List(new Result.Str("b"))));
    }

    [Fact]
    public void Equality_EmptyStructuresAreDecidedWithoutExpansion()
    {
        var (comparer, observations) = Observed();

        Assert.True(comparer.Equals(List(List(), List()), List(List(), List())));
        Assert.False(comparer.Equals(List(List()), List(Seq())));

        // Only the two root pairs; empty children have nothing to expand.
        Assert.Equal(2, observations.EqualityPairExpansionCount);
    }

    // ── Test B: one hash operation expands each node at most once ────────────────────────────

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public void Hash_DagNode_IsHashedAtMostOncePerTopLevelHash(int depth)
    {
        var (comparer, observations) = Observed();
        var value = SharedDag(depth);

        var first = comparer.GetHashCode(value);

        // depth+1 distinct structure nodes, each folded once; the path-expanding walk visited
        // 2^(depth+1) - 1 of them.
        Assert.Equal(depth + 1, observations.HashStructureExpansionCount);

        // The memo lives for ONE top-level hash: a second call recomputes the graph (no state is
        // cached on the value) and must still produce the same hash.
        var second = comparer.GetHashCode(value);
        Assert.Equal(first, second);
        Assert.Equal(2 * (depth + 1), observations.HashStructureExpansionCount);
    }

    [Fact]
    public void Hash_NodeWorkGrowsLinearlyWithGraphDepth()
    {
        var (shallowComparer, shallow) = Observed();
        var (deepComparer, deep) = Observed();

        _ = shallowComparer.GetHashCode(SharedDag(ShallowDepth));
        _ = deepComparer.GetHashCode(SharedDag(DeepDepth));

        Assert.Equal(
            DeepDepth - ShallowDepth,
            deep.HashStructureExpansionCount - shallow.HashStructureExpansionCount);
    }

    [Fact]
    public void Hash_LeavesAndEmptyStructuresExpandNothing()
    {
        var (comparer, observations) = Observed();

        _ = comparer.GetHashCode(Atom(7));
        _ = comparer.GetHashCode(new Result.Str("text"));
        Assert.Equal(0, observations.HashStructureExpansionCount);

        // One flat structure of leaves and empties: only the root itself is folded.
        _ = comparer.GetHashCode(List(Atom(1), new Result.Str("a"), List(), Seq()));
        Assert.Equal(1, observations.HashStructureExpansionCount);
    }

    // ── The Equals / GetHashCode contract over shared graphs ─────────────────────────────────

    [Fact]
    public void EqualValues_HashEqually_AcrossSharedAndRebuiltGraphs()
    {
        var shared = SharedDag(DeepDepth);
        var rebuilt = SharedDag(DeepDepth);

        Assert.True(Result.ValueComparer.Equals(shared, rebuilt));
        Assert.Equal(Result.ValueComparer.GetHashCode(shared), Result.ValueComparer.GetHashCode(rebuilt));

        // A tree with the same content as a shared graph is the same VALUE, so it hashes the same.
        var unshared = List(
            List(Atom(1), Atom(2)),
            List(Atom(1), Atom(2)));
        Assert.True(Result.ValueComparer.Equals(SharedDag(1), unshared));
        Assert.Equal(
            Result.ValueComparer.GetHashCode(SharedDag(1)),
            Result.ValueComparer.GetHashCode(unshared));
    }

    [Fact]
    public void DeepLeafMutationBreaksEqualityEvenWhenMostOfTheGraphIsShared()
    {
        var value = SharedDag(DeepDepth);
        var mutated = SharedDag(DeepDepth, leafB: 3);

        Assert.False(Result.ValueComparer.Equals(value, mutated));
        Assert.True(Result.ValueComparer.Equals(value, SharedDag(DeepDepth)));

        // Kind distinctions survive sharing as well.
        var sequenceShaped = Seq(Atom(1), Atom(2));
        Assert.False(Result.ValueComparer.Equals(
            List(sequenceShaped, sequenceShaped),
            List(List(Atom(1), Atom(2)), List(Atom(1), Atom(2)))));
    }

    [Fact]
    public void SharedGraphsBehaveAsSetAndDictionaryKeys()
    {
        var set = new HashSet<Result>(Result.ValueComparer)
        {
            SharedDag(DeepDepth),
            SharedDag(DeepDepth),
            SharedDag(DeepDepth, leafB: 3),
        };

        Assert.Equal(2, set.Count);
        Assert.Contains(SharedDag(DeepDepth), set);

        var dictionary = new Dictionary<Result, string>(Result.ValueComparer)
        {
            [SharedDag(ShallowDepth)] = "graph",
        };
        Assert.Equal("graph", dictionary[SharedDag(ShallowDepth)]);
    }

    // ── Totality on an aliased graph that no legal construction can produce ──────────────────

    [Fact]
    public async Task AliasedSelfReferentialGraphTerminatesInsteadOfHangingTheHost()
    {
        // Result values are acyclic by construction: public construction snapshots its input, and
        // TakeOwnership requires storage with no other owner. This probe deliberately VIOLATES that
        // ownership invariant to build a self-referential graph — not a legal value, and not a
        // semantic contract — purely to pin that neither walk can spin forever inside a host if an
        // embedder ever breaks the invariant. Both walks are bounded by their reference memos.
        var storage = new Result[1];
        var cyclic = Result.ListValue.TakeOwnership(storage);
        storage[0] = cyclic;

        var otherStorage = new Result[1];
        var otherCyclic = Result.ListValue.TakeOwnership(otherStorage);
        otherStorage[0] = otherCyclic;

        var walk = Task.Run(() =>
        {
            _ = Result.ValueComparer.Equals(cyclic, otherCyclic);
            _ = Result.ValueComparer.GetHashCode(cyclic);
        });

        var finished = await Task.WhenAny(walk, Task.Delay(TimeSpan.FromSeconds(30)));
        Assert.True(
            ReferenceEquals(finished, walk),
            "structural equality/hashing did not terminate on an aliased self-referential graph");
        await walk;
    }

    // ── Language-level regressions for the consumers of the two walks ────────────────────────

    /// <summary>
    /// The doubling DAG, built by an ordinary in-budget loop: <c>Wrap</c> stores its ONE bound
    /// argument in both element slots, so each step adds one node reachable through twice as many
    /// paths. <c>A</c> and <c>B</c> are independently built and structurally equal but share no
    /// object; <c>C</c> differs only in the single shared deepest leaf.
    /// </summary>
    private static string DagProgram(string body, int depth = DeepDepth)
        => $"""
            Wrap = [x, x]
            A = Wrap.repeat({depth}, 1)
            B = Wrap.repeat({depth}, 1)
            C = Wrap.repeat({depth}, 2)
            {body}
            """;

    /// <summary>
    /// STRICT-SOURCE: requires a clean front end, then runs the PLAIN and the COUNTED evaluator and
    /// requires both to agree — the memoized walks are one shared value-level primitive, so neither
    /// entry point may observe different equality or duplicate detection.
    /// </summary>
    private static void AssertEval(string source, params decimal[] expected)
    {
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

        var plain = Evaluator.RunFlat(expr);
        if (plain.IsError)
            Assert.Fail($"Expected success but got error: {plain.Error}");
        Assert.Equal(expected, plain.Value);

        var counted = Evaluator.RunCounted(expr);
        if (counted.IsError)
            Assert.Fail($"Expected counted success but got error: {counted.Error}");
        Assert.Equal(expected, counted.Value.Value.ToHostAtoms());
    }

    [Fact]
    public void LanguageBuiltDoublingValueIsOneSharedGraph()
    {
        // The premise of every case below: the loop builds a DAG, not a tree. Without sharing the
        // depth-40 values would be 2^40 nodes and could not be built at all.
        var expr = new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid("Wrap = [x, x]\nWrap.repeat(3, 1)").Root);

        var plain = Evaluator.Run(expr);
        if (plain.IsError)
            Assert.Fail($"Expected success but got error: {plain.Error}");
        var list = Assert.IsType<Result.ListValue>(plain.Value);
        Assert.Same(list.Items[0], list.Items[1]);
        var inner = Assert.IsType<Result.ListValue>(list.Items[0]);
        Assert.Same(inner.Items[0], inner.Items[1]);

        var counted = Evaluator.RunCounted(expr);
        if (counted.IsError)
            Assert.Fail($"Expected counted success but got error: {counted.Error}");
        var countedList = Assert.IsType<Result.ListValue>(counted.Value.Value);
        Assert.Same(countedList.Items[0], countedList.Items[1]);
    }

    [Fact]
    public void SharedGraphEqualityOperators()
        => AssertEval(DagProgram("A == B, A == C, A != B, A != C"), 1, 0, 0, 1);

    [Fact]
    public void SharedGraphContains()
    {
        // The searched item is compared against a structurally equal graph, so the scan cannot
        // short-circuit on a shape mismatch — it performs the full deep comparison.
        AssertEval(DagProgram("contains((A, 5), B)"), 1);
        AssertEval(DagProgram("contains((A, 5), C)"), 0);
    }

    [Fact]
    public void SharedGraphDistinct()
        // Forces Result hashing of three deep shared graphs; the result is scalar, so no display
        // rendering of the graphs can confound it.
        => AssertEval(DagProgram("distinct((A, B, C)).count"), 2);

    [Fact]
    public void SharedGraphRepeatedNamePatternBinding()
    {
        // The second argument binds an already-bound pattern name, which compares the incoming
        // value structurally against the bound one.
        AssertEval(DagProgram("Same(v, v) = 1\nSame(A, B)"), 1);

        var mismatched = Evaluator.RunFlat(new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid(DagProgram("Same(v, v) = 1\nSame(A, C)")).Root));
        Assert.True(mismatched.IsError);
    }
}
