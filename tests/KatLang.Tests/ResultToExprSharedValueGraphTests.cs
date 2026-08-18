using System.Runtime.CompilerServices;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// <see cref="Evaluator.ResultToExpr"/> over SHARED value graphs — the reification sibling of the
/// <see cref="Result.Normalize"/> walk pinned by <see cref="NormalizeSharedValueGraphTests"/>. A
/// value is a DAG, not a tree (<c>Wrap = [x, x]</c> applied n times reaches n+1 distinct nodes
/// through 2^n root-to-leaf paths in n in-budget steps), so a reification whose work is
/// proportional to PATHS is exponential on values an ordinary in-budget loop builds, and no
/// evaluation budget bounds it: the blow-up happens inside ONE uncharged conversion, reachable
/// from source through the lazy counted-argument wrapper (<c>CountedArgAlgorithm</c>) whenever an
/// algorithm-only builtin slot receives a pre-evaluated value (a loop step slot, an
/// algorithm-kind suffix slot).
///
/// <para>Reification is a pure function of the <see cref="Result"/> node (Lean:
/// <c>resultToExpr</c>), so the fix is the same discipline as Normalize: a REFERENCE-IDENTITY
/// memo scoped to one conversion operation (one direct call or one complete multi-emission
/// wrapper), one completed <see cref="Expr"/> per unique node, reused at every shared occurrence.
/// The produced expression is then itself a shared (acyclic)
/// <see cref="Expr"/> DAG — an explicitly supported AST shape; evaluation work stays charged per
/// VISIT, so shared expression identity never collapses semantic occurrences (pinned by
/// <see cref="SharedExprOccurrenceSemanticsTests"/>).</para>
///
/// <para>Work counts are exact and deterministic, measured through the passive run-scoped
/// <see cref="EvaluationObservations"/> observer; timing is deliberately not a pass/fail signal.
/// Semantics are checked against <see cref="NaiveResultToExpr"/>, a test-only recursive replica
/// of the path-expanding rebuild this suite replaced.</para>
/// </summary>
public class ResultToExprSharedValueGraphTests
{
    private const int ShallowDepth = 20;

    private const int DeepDepth = 40;

    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result Str(string value) => new Result.Str(value);

    private static Result List(params Result[] items) => Result.ListValue.TakeOwnership(items);

    private static Result Seq(params Result[] items) => Result.SequenceValue.TakeOwnership(items);

    private static EvaluationObservations Observations() => new();

    /// <summary>
    /// The doubling DAG: <c>P0 = leaf</c>, <c>Pk = [P(k-1), P(k-1)]</c>. With the default
    /// two-atom list leaf a graph of depth n has exactly n+1 distinct structure nodes and
    /// 2^(n+1) - 1 structure-node path occurrences.
    /// </summary>
    private static Result SharedDag(int depth, Result? leaf = null)
    {
        var node = leaf ?? List(Atom(1), Atom(2));
        for (var i = 0; i < depth; i++)
            node = List(node, node);
        return node;
    }

    /// <summary>
    /// Test-only replica of the pre-fix reification: a plain recursive post-order rebuild with no
    /// memo, which expands one frame per PATH occurrence and allocates fresh expression structure
    /// for every occurrence it visits. It is the semantic oracle for the memoized implementation,
    /// and (with a counter) the measurement of the work the old walk performed. Only ever applied
    /// to small values — on the doubling DAG it is exponential by construction.
    /// </summary>
    private static Expr NaiveResultToExpr(Result value, StrongBox<long>? expansions = null)
    {
        if (NaiveLeaf(value) is { } leaf)
            return leaf;

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
                return new Expr.EmptySequence(0);
        }

        if (expansions is not null)
            expansions.Value++;

        var converted = new Expr[items.Count];
        for (var i = 0; i < items.Count; i++)
            converted[i] = NaiveResultToExpr(items[i], expansions);

        return isSequence
            ? new Expr.Capture(OutputBundle.TakeOwnership(converted))
            : new Expr.ListLiteral(OutputBundle.TakeOwnership(converted));
    }

    private static Expr? NaiveLeaf(Result value) => value switch
    {
        Result.Atom(var n) => new Expr.Num(n),
        Result.Str(var s) => new Expr.StringLiteral(s),
        Result.SequenceValue when IsEmptySequenceChain(value) => new Expr.EmptySequence(0),
        _ => null,
    };

    private static bool IsEmptySequenceChain(Result value)
    {
        while (true)
        {
            if (value is not Result.SequenceValue(var items))
                return false;
            if (items.Count == 0)
                return true;
            if (items.Count != 1)
                return false;
            value = items[0];
        }
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

    private static IReadOnlyList<Expr> ExprChildren(Expr expr) => expr switch
    {
        Expr.Capture(var body) => body,
        Expr.ListLiteral(var items) => items,
        _ => [],
    };

    /// <summary>Distinct expression objects reachable from <paramref name="root"/> by REFERENCE
    /// identity, walked iteratively so deep and shared graphs are both safe to measure.</summary>
    private static int DistinctExprNodes(Expr root)
    {
        var seen = new HashSet<Expr>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<Expr>();
        pending.Push(root);
        while (pending.Count > 0)
        {
            var node = pending.Pop();
            if (!seen.Add(node))
                continue;
            foreach (var child in ExprChildren(node))
                pending.Push(child);
        }

        return seen.Count;
    }

    /// <summary>Structural equality over the closed reified fragment (Num, StringLiteral,
    /// EmptySequence, Capture, ListLiteral), independent of reference topology.</summary>
    private static bool StructurallyEqual(Expr left, Expr right)
    {
        var pending = new Stack<(Expr Left, Expr Right)>();
        pending.Push((left, right));
        while (pending.Count > 0)
        {
            var (a, b) = pending.Pop();
            switch (a, b)
            {
                case (Expr.Num(var x), Expr.Num(var y)) when x == y:
                    continue;
                case (Expr.StringLiteral(var x), Expr.StringLiteral(var y)) when x == y:
                    continue;
                case (Expr.EmptySequence(var x), Expr.EmptySequence(var y)) when x == y:
                    continue;
                case (Expr.Capture(var xs), Expr.Capture(var ys)) when xs.Count == ys.Count:
                    for (var i = 0; i < xs.Count; i++)
                        pending.Push((xs[i], ys[i]));
                    continue;
                case (Expr.ListLiteral(var ls), Expr.ListLiteral(var rs)) when ls.Count == rs.Count:
                    for (var i = 0; i < ls.Count; i++)
                        pending.Push((ls[i], rs[i]));
                    continue;
                default:
                    return false;
            }
        }

        return true;
    }

    private static void AssertNoSourceSpans(Expr root)
    {
        var pending = new Stack<Expr>();
        var seen = new HashSet<Expr>(ReferenceEqualityComparer.Instance);
        pending.Push(root);
        while (pending.Count > 0)
        {
            var node = pending.Pop();
            if (!seen.Add(node))
                continue;
            Assert.Null(node.Span);
            foreach (var child in ExprChildren(node))
                pending.Push(child);
        }
    }

    private static Result EvalExpr(Expr expr)
    {
        var result = Evaluator.Run(expr);
        if (result.IsError)
            Assert.Fail($"Reified expression failed to evaluate: {result.Error}");
        return result.Value;
    }

    private static void AssertSameEvaluation(Expr expected, Expr actual)
    {
        var expectedPlain = Evaluator.Run(expected);
        var actualPlain = Evaluator.Run(actual);
        Assert.Equal(expectedPlain.IsError, actualPlain.IsError);
        if (!expectedPlain.IsError)
            Assert.Equal(expectedPlain.Value, actualPlain.Value, Result.ValueComparer);

        var expectedCounted = Evaluator.RunCounted(expected);
        var actualCounted = Evaluator.RunCounted(actual);
        Assert.Equal(expectedCounted.IsError, actualCounted.IsError);
        if (!expectedCounted.IsError)
        {
            Assert.Equal(expectedCounted.Value.Value, actualCounted.Value.Value, Result.ValueComparer);
            Assert.Equal(expectedCounted.Value.EmittedCount, actualCounted.Value.EmittedCount);
        }

        var expectedFlat = Evaluator.RunFlat(expected);
        var actualFlat = Evaluator.RunFlat(actual);
        Assert.Equal(expectedFlat.IsError, actualFlat.IsError);
        if (expectedFlat.IsError)
            Assert.Equal(expectedFlat.Error.GetType(), actualFlat.Error.GetType());
        else
            Assert.Equal(expectedFlat.Value, actualFlat.Value);
    }

    // ── Unique-node work: each distinct structure node is converted at most once per call ────

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public void ResultToExpr_SharedDag_ExpandsEachUniqueResultOnce(int depth)
    {
        var observations = Observations();
        var value = SharedDag(depth);

        _ = Evaluator.ResultToExpr(value, observations);

        // depth+1 distinct structure nodes, each expanded once. The path-expanding rebuild
        // expanded 2^(depth+1) - 1 of them.
        Assert.Equal(depth + 1, observations.ResultToExprStructureExpansionCount);
        Assert.Equal(depth + 1, DistinctStructureNodes(value));
    }

    [Fact]
    public void ResultToExpr_WorkGrowsLinearlyWithGraphDepth()
    {
        var shallow = Observations();
        var deep = Observations();

        _ = Evaluator.ResultToExpr(SharedDag(ShallowDepth), shallow);
        _ = Evaluator.ResultToExpr(SharedDag(DeepDepth), deep);

        // Twenty more levels cost twenty more expansions, not 2^20 times as many.
        Assert.Equal(
            DeepDepth - ShallowDepth,
            deep.ResultToExprStructureExpansionCount - shallow.ResultToExprStructureExpansionCount);
    }

    [Fact]
    public void ResultToExpr_NaiveRebuildExpandsOnePathPerFrame()
    {
        // Pins the oracle's own complexity, so the counts above are measured against a known
        // baseline rather than an assumed one: the old walk expanded one frame per structure-node
        // PATH occurrence — 2^(depth+1) - 1 on the doubling DAG.
        foreach (var depth in new[] { 4, 8, 12 })
        {
            var expansions = new StrongBox<long>(0);
            _ = NaiveResultToExpr(SharedDag(depth), expansions);

            Assert.Equal((1L << (depth + 1)) - 1, expansions.Value);
        }
    }

    [Fact]
    public void ResultToExpr_MemoIsScopedToOneTopLevelCall()
    {
        var observations = Observations();
        var value = SharedDag(ShallowDepth);

        var first = Evaluator.ResultToExpr(value, observations);
        Assert.Equal(ShallowDepth + 1, observations.ResultToExprStructureExpansionCount);

        // Nothing is cached on a Result: a second conversion recomputes the whole graph and must
        // produce a structurally identical expression. The memo belongs to one call.
        var second = Evaluator.ResultToExpr(value, observations);
        Assert.Equal(2 * (ShallowDepth + 1), observations.ResultToExprStructureExpansionCount);
        Assert.NotSame(first, second);
        Assert.True(StructurallyEqual(first, second));
    }

    [Fact]
    public void ResultToExpr_LeavesAndEmptyChainsExpandNothing()
    {
        var observations = Observations();

        Assert.IsType<Expr.Num>(Evaluator.ResultToExpr(Atom(7), observations));
        Assert.IsType<Expr.StringLiteral>(Evaluator.ResultToExpr(Str("text"), observations));

        // The empty sequence and redundant chains over it are canonical `()` leaves.
        Assert.Equal(0, Assert.IsType<Expr.EmptySequence>(Evaluator.ResultToExpr(Seq(), observations)).Depth);
        Assert.Equal(0, Assert.IsType<Expr.EmptySequence>(Evaluator.ResultToExpr(Seq(Seq()), observations)).Depth);
        Assert.Equal(0, observations.ResultToExprStructureExpansionCount);

        // One flat structure of leaves: only the root itself is expanded, and the memo path is
        // never needed. The empty LIST is exact and stays a real (empty) list literal.
        var flat = Assert.IsType<Expr.Capture>(Evaluator.ResultToExpr(Seq(Atom(1), Str("a")), observations));
        Assert.Equal(2, flat.Body.Count);
        Assert.Equal(1, observations.ResultToExprStructureExpansionCount);

        var emptyList = Assert.IsType<Expr.ListLiteral>(Evaluator.ResultToExpr(List(), observations));
        Assert.Empty(emptyList.Items);
        Assert.Equal(2, observations.ResultToExprStructureExpansionCount);
    }

    // ── Sharing preservation in the produced expression ─────────────────────────────────────

    [Fact]
    public void ResultToExpr_SharedDag_PreservesReferenceSharing()
    {
        var observations = Observations();
        var reified = Evaluator.ResultToExpr(SharedDag(DeepDepth), observations);

        // The output is an Expr DAG of the same shape: DeepDepth+1 list literals plus the two
        // atom leaves, not the 2^(DeepDepth+1) - 1 nodes the expanded tree spells out.
        Assert.Equal(DeepDepth + 1, observations.ResultToExprStructureExpansionCount);
        Assert.Equal(DeepDepth + 1 + 2, DistinctExprNodes(reified));

        var level = reified;
        for (var i = 0; i < DeepDepth; i++)
        {
            var items = Assert.IsType<Expr.ListLiteral>(level).Items;
            Assert.Equal(2, items.Count);
            Assert.Same(items[0], items[1]);
            level = items[0];
        }

        var leaf = Assert.IsType<Expr.ListLiteral>(level).Items;
        Assert.Equal(2, leaf.Count);
        Assert.Equal(1, Assert.IsType<Expr.Num>(leaf[0]).Value);
        Assert.Equal(2, Assert.IsType<Expr.Num>(leaf[1]).Value);
    }

    [Fact]
    public void ResultToExpr_DiamondDag_ConvertsTheSharedChildOnceAndReusesIt()
    {
        //         root
        //        /    \
        //       A      B
        //      / \    / \
        //     X   Y  X   Z
        var x = List(Atom(1), Atom(2));
        var y = Seq(Atom(3), Atom(4));
        var z = List(Atom(5), Atom(6));
        var a = List(x, y);
        var b = Seq(x, z);
        var root = List(a, b);

        var observations = Observations();
        var reified = Assert.IsType<Expr.ListLiteral>(Evaluator.ResultToExpr(root, observations));

        // root + A + B + X + Y + Z, with X expanded exactly once.
        Assert.Equal(6, observations.ResultToExprStructureExpansionCount);

        var reifiedA = Assert.IsType<Expr.ListLiteral>(reified.Items[0]);
        var reifiedB = Assert.IsType<Expr.Capture>(reified.Items[1]);
        Assert.Same(reifiedA.Items[0], reifiedB.Body[0]);
        Assert.NotSame(reifiedA.Items[1], reifiedB.Body[1]);

        // Chain-only coverage is insufficient: the mesh must also evaluate exactly like the
        // path-expanded tree the old walk produced.
        AssertSameEvaluation(NaiveResultToExpr(root), reified);
    }

    [Fact]
    public void ResultToExpr_MixedSharedAndUnsharedGraph_KeepsExactCountsAndTopology()
    {
        // One heavily shared branch, one unique branch, and two independent value-equal branches.
        var shared = SharedDag(3);
        var unique = List(Atom(9), Seq(Atom(10)));
        var equalLeft = List(Seq(Atom(7)), Atom(8));
        var equalRight = List(Seq(Atom(7)), Atom(8));
        Assert.True(Result.ValueComparer.Equals(equalLeft, equalRight));
        Assert.False(ReferenceEquals(equalLeft, equalRight));

        var root = Seq(shared, shared, unique, equalLeft, equalRight);
        var observations = Observations();
        var reified = Assert.IsType<Expr.Capture>(Evaluator.ResultToExpr(root, observations));

        // Root (1) + the four structure nodes of the shared depth-3 graph expanded once for both
        // occurrences (4) + the unique branch and its inner sequence (2) + each equal-but-distinct
        // branch and its inner sequence (4).
        Assert.Equal(11, observations.ResultToExprStructureExpansionCount);

        Assert.Same(reified.Body[0], reified.Body[1]);
        Assert.NotSame(reified.Body[3], reified.Body[4]);
        Assert.True(StructurallyEqual(reified.Body[3], reified.Body[4]));

        AssertSameEvaluation(NaiveResultToExpr(root), reified);
    }

    // ── Memo keying: reference identity, never KatLang or record equality ───────────────────

    [Fact]
    public void ResultToExpr_IndependentEqualNodes_AreDistinctMemoEntries()
    {
        var observations = Observations();

        // Two children that are VALUE-EQUAL but share no reference. A memo keyed by KatLang value
        // equality (or its structural hash) would expand the second one zero times; reference
        // identity expands both and keeps their reified expressions distinct objects.
        var left = List(Seq(Atom(1)), Atom(2));
        var right = List(Seq(Atom(1)), Atom(2));
        Assert.True(Result.ValueComparer.Equals(left, right));
        Assert.False(ReferenceEquals(left, right));

        var reified = Assert.IsType<Expr.ListLiteral>(
            Evaluator.ResultToExpr(List(left, right), observations));

        // Root + two independent lists + their two independent singleton sequences.
        Assert.Equal(5, observations.ResultToExprStructureExpansionCount);
        Assert.NotSame(reified.Items[0], reified.Items[1]);
        Assert.True(StructurallyEqual(reified.Items[0], reified.Items[1]));
    }

    [Fact]
    public void ResultToExpr_DefaultEqualRecordClones_AreDistinctMemoEntries()
    {
        // A plain Dictionary<Result, Expr> would use generated C# record equality, not reference
        // identity. Independently constructed containers usually have distinct read-only wrapper
        // fields and do not expose that mutation. A record clone is a distinct Result that shares
        // the wrapper, so it is default-equal and deterministically catches removal of the
        // explicit ReferenceEqualityComparer.
        var left = Assert.IsType<Result.ListValue>(List(Seq(Atom(1)), Atom(2)));
        var right = left with { };
        Assert.NotSame(left, right);
        Assert.True(left.Equals(right));
        Assert.Same(left.Items, right.Items);

        var observations = Observations();
        var reified = Assert.IsType<Expr.ListLiteral>(
            Evaluator.ResultToExpr(List(left, right), observations));

        // Root + both distinct list references + their one genuinely shared singleton sequence.
        Assert.Equal(4, observations.ResultToExprStructureExpansionCount);
        Assert.NotSame(reified.Items[0], reified.Items[1]);
        Assert.True(StructurallyEqual(reified.Items[0], reified.Items[1]));
    }

    // ── Context freedom: a node's reified form does not depend on where it is reached ───────

    [Fact]
    public void ResultToExpr_SameChildUnderEveryParentKindAndPosition_ReifiesIdentically()
    {
        // ONE child reference reached from parents of different KINDS, at different POSITIONS,
        // beside different neighbours, and at the root. Reification reads only the node's own
        // kind and its children's reified forms, so every occurrence must produce the same
        // structural expression — and within one call, literally the same reference.
        var child = List(Seq(Atom(1), Atom(2)), Str("s"));
        var direct = Evaluator.ResultToExpr(child);

        var underList = Assert.IsType<Expr.ListLiteral>(Evaluator.ResultToExpr(List(child, Atom(0))));
        var underSequence = Assert.IsType<Expr.Capture>(Evaluator.ResultToExpr(Seq(Atom(0), child)));
        var underNestedMix = Assert.IsType<Expr.ListLiteral>(
            Evaluator.ResultToExpr(List(Seq(child, Atom(0)), List(List(), child))));

        Assert.True(StructurallyEqual(direct, underList.Items[0]));
        Assert.True(StructurallyEqual(direct, underSequence.Body[1]));

        var mixedLeft = Assert.IsType<Expr.Capture>(underNestedMix.Items[0]);
        var mixedRight = Assert.IsType<Expr.ListLiteral>(underNestedMix.Items[1]);
        Assert.True(StructurallyEqual(direct, mixedLeft.Body[0]));
        Assert.True(StructurallyEqual(direct, mixedRight.Items[1]));

        // Within ONE call the shared occurrences are literally the same reified reference.
        Assert.Same(mixedLeft.Body[0], mixedRight.Items[1]);
    }

    [Fact]
    public void ResultToExpr_ReifiedNodesCarryNoSourceSpans()
    {
        // Reified expressions are synthetic: every node is spanless, shared or not, exactly like
        // the path-expanding rebuild's output. Diagnostics that need a location fall back to the
        // consuming call site's span, which sharing cannot change.
        var value = List(SharedDag(4), Seq(Atom(1), Str("x")), SharedDag(4));

        AssertNoSourceSpans(Evaluator.ResultToExpr(value));
        AssertNoSourceSpans(NaiveResultToExpr(value));
    }

    [Fact]
    public void ResultToExpr_ObserverDoesNotAffectReferenceSharingTopology()
    {
        var value = SharedDag(8);
        var observedStats = Observations();
        var observed = Evaluator.ResultToExpr(value, observedStats);
        var unobserved = Evaluator.ResultToExpr(value);

        Assert.Equal(9, observedStats.ResultToExprStructureExpansionCount);
        Assert.True(StructurallyEqual(unobserved, observed));
        Assert.Equal(DistinctExprNodes(unobserved), DistinctExprNodes(observed));

        for (var level = 0; level < 8; level++)
        {
            var observedItems = Assert.IsType<Expr.ListLiteral>(observed).Items;
            var unobservedItems = Assert.IsType<Expr.ListLiteral>(unobserved).Items;
            Assert.Same(observedItems[0], observedItems[1]);
            Assert.Same(unobservedItems[0], unobservedItems[1]);
            observed = observedItems[0];
            unobserved = unobservedItems[0];
        }
    }

    [Fact]
    public void ResultToExpr_WideSharedLeafPreservesEveryExplicitOccurrence()
    {
        const int width = 100_000;
        var leaf = Atom(7);
        var value = Result.ListValue.TakeOwnership(Enumerable.Repeat(leaf, width).ToArray());
        var observations = Observations();

        var reified = Assert.IsType<Expr.ListLiteral>(Evaluator.ResultToExpr(value, observations));

        // Leaves are intentionally fresh per explicit incoming edge. Work and output are O(E):
        // the physical root really stores 100,000 child slots, so none may be collapsed.
        Assert.Equal(1, observations.ResultToExprStructureExpansionCount);
        Assert.Equal(width, reified.Items.Count);
        Assert.Equal(width + 1, DistinctExprNodes(reified));
        Assert.NotSame(reified.Items[0], reified.Items[1]);
        Assert.All(reified.Items, item => Assert.Equal(7, Assert.IsType<Expr.Num>(item).Value));
    }

    [Fact]
    public void ResultToExpr_WideSharedContainerExpandsItsInteriorOnce()
    {
        const int width = 100_000;
        var child = List(Atom(1), Atom(2));
        var value = Result.ListValue.TakeOwnership(Enumerable.Repeat(child, width).ToArray());
        var observations = Observations();

        var reified = Assert.IsType<Expr.ListLiteral>(Evaluator.ResultToExpr(value, observations));

        Assert.Equal(2, observations.ResultToExprStructureExpansionCount);
        Assert.Equal(width, reified.Items.Count);
        Assert.Equal(4, DistinctExprNodes(reified)); // root, child, and the child's two leaves
        Assert.All(reified.Items, item => Assert.Same(reified.Items[0], item));
    }

    // ── Semantic equivalence against the naive path-expanding oracle ────────────────────────

    /// <summary>Every supported value kind and the nesting/empty/singleton/sharing shapes around
    /// them. Kept small enough for the exponential oracle.</summary>
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
            SharedDag(4, Seq(Atom(7))),
            // Deepest-leaf difference under otherwise identical sharing.
            List(SharedDag(3, List(Atom(1), Atom(2))), SharedDag(3, List(Atom(1), Atom(3)))),
            // Wide flat and wide nested.
            Result.ListValue.TakeOwnership([.. Enumerable.Range(0, 64).Select(i => Atom(i))]),
            Result.SequenceValue.TakeOwnership([.. Enumerable.Range(0, 64).Select(i => Seq(Atom(i)))]),
        ];
    }

    [Fact]
    public void ResultToExpr_MatchesTheNaiveRebuild_AcrossEveryValueShape()
    {
        foreach (var value in Corpus())
        {
            var reified = Evaluator.ResultToExpr(value);
            var naive = NaiveResultToExpr(value);

            // The memoized conversion produces the same STRUCTURAL expression as the
            // path-expanding rebuild, and the two evaluate identically through the plain and
            // counted evaluators — value, error, and emitted count.
            Assert.True(StructurallyEqual(naive, reified));
            AssertSameEvaluation(naive, reified);
        }
    }

    [Fact]
    public void ResultToExpr_RoundTripsNormalizedValues()
    {
        // For a normalized value the reified expression evaluates back to that value: reification
        // and evaluation are inverse at the value boundary. (Unnormalized chains canonicalize,
        // which the corpus differential above covers.)
        foreach (var value in Corpus())
        {
            var normalized = value.Normalize();
            Assert.Equal(normalized, EvalExpr(Evaluator.ResultToExpr(normalized)), Result.ValueComparer);
        }
    }

    [Fact]
    public void ResultToExpr_SharedAndExpandedReifications_EvaluateWithIdenticalWork()
    {
        // The §15-style oracle on the actual reified fragment: the shared reification and the
        // naive path-expanded tree describe the same expression, so evaluating them must charge
        // identical work — evaluation is per VISIT, and a shared reference visited twice pays
        // twice on both representations.
        var value = SharedDag(6);
        var shared = Evaluator.ResultToExpr(value);
        var expanded = NaiveResultToExpr(value);

        var (sharedResult, sharedBudget) = Evaluator.RunCountedObserved(shared);
        var (expandedResult, expandedBudget) = Evaluator.RunCountedObserved(expanded);

        Assert.False(sharedResult.IsError);
        Assert.False(expandedResult.IsError);
        Assert.Equal(expandedResult.Value.Value, sharedResult.Value.Value, Result.ValueComparer);
        Assert.Equal(expandedResult.Value.EmittedCount, sharedResult.Value.EmittedCount);
        Assert.Equal(expandedBudget.ConsumedSteps, sharedBudget.ConsumedSteps);
        Assert.Equal(expandedBudget.MaterializedItems, sharedBudget.MaterializedItems);
        Assert.Equal(expandedBudget.MaterializedStringChars, sharedBudget.MaterializedStringChars);
        Assert.Equal(expandedBudget.PeakDepth, sharedBudget.PeakDepth);
    }

    [Fact]
    public void ResultToExpr_ActualSharedChildMaterializesOncePerOccurrence()
    {
        var child = List(Atom(1), Atom(2));
        var twice = Evaluator.ResultToExpr(List(child, child));
        var once = Evaluator.ResultToExpr(List(child));

        var twiceRoot = Assert.IsType<Expr.ListLiteral>(twice);
        Assert.Same(twiceRoot.Items[0], twiceRoot.Items[1]);

        var (twiceResult, twiceBudget) = Evaluator.RunCountedObserved(twice);
        var (onceResult, onceBudget) = Evaluator.RunCountedObserved(once);
        Assert.False(twiceResult.IsError);
        Assert.False(onceResult.IsError);
        Assert.True(twiceBudget.MaterializedItems > onceBudget.MaterializedItems);
    }

    [Fact]
    public void ResultToExpr_SharedAndExpandedDiagnosticsAreIdentical()
    {
        var value = SharedDag(4);
        var sharedCall = new Expr.Call(Evaluator.ResultToExpr(value), OutputBundle.Empty);
        var expandedCall = new Expr.Call(NaiveResultToExpr(value), OutputBundle.Empty);

        var shared = Evaluator.Run(sharedCall);
        var expanded = Evaluator.Run(expandedCall);
        Assert.True(shared.IsError);
        Assert.True(expanded.IsError);
        Assert.Equal(expanded.Error, shared.Error);
        Assert.Equal(expanded.Error.ToString(), shared.Error.ToString());
        Assert.Null(shared.Error.Span);
    }

    [Fact]
    public void ResultToExpr_SharedAndExpandedReifications_CrossResourceBoundariesIdentically()
    {
        // Exact-boundary parity: sweep the cumulative materialization budget across the entire
        // range that matters for this value, so the success/failure boundary — wherever it lies —
        // is included for both representations.
        var value = SharedDag(4);
        var shared = Evaluator.ResultToExpr(value);
        var expanded = NaiveResultToExpr(value);

        var crossed = false;
        for (long budget = 1; budget <= 96; budget++)
        {
            var limits = new EvaluationLimits { MaxMaterializedItems = budget };
            var sharedR = Evaluator.Run(shared, limits);
            var expandedR = Evaluator.Run(expanded, limits);

            Assert.Equal(expandedR.IsError, sharedR.IsError);
            if (sharedR.IsError)
            {
                Assert.Equal(expandedR.Error.GetType(), sharedR.Error.GetType());
            }
            else
            {
                crossed = true;
            }
        }

        Assert.True(crossed, "The sweep never reached the success side of the boundary.");
    }

    // ── Deep linear conversion stays iterative ──────────────────────────────────────────────

    [Fact]
    public void ResultToExpr_VeryDeepUnsharedLinearValue_ConvertsIterativelyWithoutStackGrowth()
    {
        const int depth = 100_000;
        Result node = Atom(1);
        for (var i = 0; i < depth; i++)
            node = List(node);

        var observations = Observations();
        var reified = Evaluator.ResultToExpr(node, observations);

        // One frame per unique level, walked with an explicit stack: a recursive rebuild
        // overflows the CLR stack thousands of levels before this depth.
        Assert.Equal(depth, observations.ResultToExprStructureExpansionCount);
        Assert.Equal(depth + 1, DistinctExprNodes(reified));

        var level = reified;
        for (var i = 0; i < depth; i++)
            level = Assert.Single(Assert.IsType<Expr.ListLiteral>(level).Items);
        Assert.Equal(1, Assert.IsType<Expr.Num>(level).Value);
    }

    // ── Source-level regressions: the production reification channels ───────────────────────

    /// <summary>
    /// The doubling DAG built by an ordinary in-budget loop — the same recipe the F16 Normalize
    /// regressions use: <c>Wrap</c> stores its ONE bound argument in both element slots, so each
    /// step adds one node reachable through twice as many paths.
    /// </summary>
    private static string DagProgram(string body, int depth = DeepDepth)
        => $"""
            Wrap = [x, x]
            A = Wrap.repeat({depth}, 1)
            {body}
            """;

    /// <summary>
    /// Build one depth-<paramref name="dagDepth"/> shared value DAG, then duplicate that SAME
    /// result reference into 2^<paramref name="duplicationDepth"/> emitted slots in only
    /// <paramref name="duplicationDepth"/> loop steps. Grouping <c>B*</c> makes those slots one
    /// sequence-valued collection item; using builtin <c>while</c> as the reducer routes the
    /// item's multi-emission counted value through ONE <c>CountedArgAlgorithm</c> wrapper.
    /// </summary>
    private static string MultiEmissionDagProgram(
        string body,
        int dagDepth = ShallowDepth,
        int duplicationDepth = 5)
        => $"""
            Wrap = [x, x]
            A = Wrap.repeat({dagDepth}, 1)
            Dup(*xs) = xs*, xs*
            B = Dup.repeat({duplicationDepth}, A)
            {body}
            """;

    private sealed record ObservedSourceRun(
        bool IsError,
        EvalError? InnermostError,
        Result? Value,
        int? Emitted,
        long Reifications,
        long Expansions,
        LoopOptimizationDiagnosticsSnapshot LoopStats);

    private static ObservedSourceRun ObserveSource(string source, bool optimize)
    {
        var observations = new EvaluationObservations();
        var loopDiagnostics = new LoopOptimizationDiagnostics();
        var (result, _) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root),
            enableOptimizations: optimize,
            loopDiagnostics: loopDiagnostics,
            observations: observations);

        return new ObservedSourceRun(
            result.IsError,
            result.IsError ? Innermost(result.Error) : null,
            result.IsError ? null : result.Value.Value,
            result.IsError ? null : result.Value.EmittedCount,
            observations.CountedArgumentReificationCount,
            observations.ResultToExprStructureExpansionCount,
            loopDiagnostics.GetSnapshot());
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void LoopStepSlot_ReifiesTheSharedDagOncePerUniqueNode(bool optimize)
    {
        // `A*` spreads the depth-40 list, so `while`'s step slot receives A's shared child (a
        // depth-39 DAG, 39 distinct structure nodes) as a prepared value and must reify it.
        // Before the memo this expanded 2^39 - 1 path occurrences inside one uncharged
        // conversion; now it expands each unique node once. The zero-parameter wrapper then
        // mismatches the two-slot loop state, which is the pre-existing outcome for a value in
        // step position.
        var run = ObserveSource(DagProgram("while(A*, 1)"), optimize);

        Assert.True(run.IsError);
        Assert.IsType<EvalError.ArityMismatch>(run.InnermostError);
        Assert.Equal(1, run.Reifications);
        Assert.Equal(DeepDepth - 1, run.Expansions);
        if (optimize)
        {
            // The configuration difference is non-vacuous: the outer Wrap.repeat is genuinely
            // optimized. The zero-parameter reified while step reaches its ordinary state-binding
            // arity check BEFORE loop-plan construction, so no optimizer can observe its output.
            Assert.True(run.LoopStats.OptimizedLoopHits > 0);
            Assert.All(run.LoopStats.LoopPlans, plan => Assert.Equal("Wrap.repeat", plan.Identity));
        }
        else
        {
            Assert.Equal(0, run.LoopStats.LoopPlanBuilds);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AlgorithmSuffixSlot_ReifiesTheSharedDagOncePerUniqueNode_AndSucceeds(bool optimize)
    {
        // `map` used as the reducer routes each step's pre-evaluated accumulator into its mapper
        // slot, reifying it. Step 1 reifies the depth-40 DAG accumulator (40 distinct structure
        // nodes); mapping the empty collection never applies the wrapper, so the step succeeds
        // and returns []. Step 2 reifies that [] accumulator (one node). The run SUCCEEDS — the
        // reified-wrapper channel is not error-only — after exactly 41 structure expansions where
        // the path-expanding rebuild attempted ~2^41.
        var run = ObserveSource(DagProgram("((), ()).reduce(map, A)"), optimize);

        Assert.False(run.IsError);
        var list = Assert.IsType<Result.ListValue>(run.Value);
        Assert.Empty(list.Items);
        Assert.Equal(1, run.Emitted);
        Assert.Equal(2, run.Reifications);
        Assert.Equal(DeepDepth + 1, run.Expansions);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MultiEmissionWrapper_ReusesOneMemoAcrossEveryRepeatedRoot(bool optimize)
    {
        // F21 review finding: the initial F20 patch gave each emitted root its own top-level
        // ResultToExpr call. B contains 32 references to the SAME depth-20 DAG, so that scope
        // performed 32 * 20 = 640 unbudgeted expansions. One CountedArgAlgorithm construction is
        // one conversion operation: its root set now shares one completed-node memo and expands
        // the deep graph exactly once. The wrapper's old zero-parameter arity error is unchanged.
        var run = ObserveSource(
            MultiEmissionDagProgram("[(B*)].reduce(while, 1)"),
            optimize);

        Assert.True(run.IsError);
        Assert.IsType<EvalError.ArityMismatch>(run.InnermostError);
        Assert.Equal(1, run.Reifications);
        Assert.Equal(ShallowDepth, run.Expansions);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MultiEmissionWrapper_ReusesSharedDescendantAcrossDistinctRoots(bool optimize)
    {
        // The two emitted list roots are reference-distinct, but both contain the exact same A
        // reference. The wrapper scope expands root L, A, then root R: depth + 2 total. Recreating
        // a memo per emitted root would expand A twice and observe 2 * (depth + 1).
        var run = ObserveSource(
            DagProgram("[([A, 1], [A, 2])].reduce(while, 1)", ShallowDepth),
            optimize);

        Assert.True(run.IsError);
        Assert.IsType<EvalError.ArityMismatch>(run.InnermostError);
        Assert.Equal(1, run.Reifications);
        Assert.Equal(ShallowDepth + 2, run.Expansions);
    }

    [Fact]
    public void SourceReification_WorkGrowsLinearlyWithDagDepth()
    {
        var shallow = ObserveSource(DagProgram("((), ()).reduce(map, A)", ShallowDepth), optimize: false);
        var deep = ObserveSource(DagProgram("((), ()).reduce(map, A)", DeepDepth), optimize: false);

        Assert.False(shallow.IsError);
        Assert.False(deep.IsError);
        Assert.Equal(DeepDepth - ShallowDepth, deep.Expansions - shallow.Expansions);
    }

    [Fact]
    public void CountedArgumentMemo_DoesNotCrossSeparateWrapperConstructions()
    {
        // Each successful reduce builds two wrappers (A, then []); repeating the whole expression
        // in the same evaluator run must rebuild both. Even though A comes from the run-scoped
        // property cache as the same Result reference, reification state belongs to one wrapper.
        var run = ObserveSource(
            DagProgram("""
                ((), ()).reduce(map, A)
                ((), ()).reduce(map, A)
                """, ShallowDepth),
            optimize: false);

        Assert.False(run.IsError);
        Assert.Equal(4, run.Reifications);
        Assert.Equal(2 * (ShallowDepth + 1), run.Expansions);
    }

    [Fact]
    public void SourceReification_PlainCountedAndFlatEntryPointsAgree()
    {
        // Entry-point parity for the successful reified-wrapper program: the reified
        // representation must not change what any public entry point observes.
        var source = DagProgram("((), ()).reduce(map, A)");
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

        var plain = Evaluator.Run(expr);
        Assert.False(plain.IsError);
        var plainList = Assert.IsType<Result.ListValue>(plain.Value);
        Assert.Empty(plainList.Items);

        var counted = Evaluator.RunCounted(expr);
        Assert.False(counted.IsError);
        Assert.Equal(plain.Value, counted.Value.Value, Result.ValueComparer);
        Assert.Equal(1, counted.Value.EmittedCount);

        var flat = Evaluator.RunFlat(expr);
        Assert.False(flat.IsError);
        Assert.Empty(flat.Value);
    }

    [Fact]
    public void LoopStepSourceReification_ErrorEntryPointsAgree()
    {
        var source = DagProgram("while(A*, 1)");
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

        var plain = Evaluator.Run(expr);
        var counted = Evaluator.RunCounted(expr);
        var flat = Evaluator.RunFlat(expr);

        Assert.True(plain.IsError);
        Assert.True(counted.IsError);
        Assert.True(flat.IsError);
        Assert.IsType<EvalError.ArityMismatch>(Innermost(plain.Error));
        Assert.IsType<EvalError.ArityMismatch>(Innermost(counted.Error));
        Assert.IsType<EvalError.ArityMismatch>(Innermost(flat.Error));
        Assert.Equal(plain.Error.ToString(), counted.Error.ToString());
        Assert.Equal(plain.Error.ToString(), flat.Error.ToString());
        Assert.Equal(plain.Error.Span, counted.Error.Span);
        Assert.Equal(plain.Error.Span, flat.Error.Span);
    }

    [Fact]
    public void SourceDag_IsActuallyShared_NotATreeThatHappensToBeSmall()
    {
        // The measurement above is meaningful only if the runtime value really is a DAG. Pin the
        // reference topology of the loop-built value directly: every level stores the SAME child
        // reference twice.
        var source = DagProgram("A", depth: 12);
        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        Assert.False(result.IsError);

        var level = result.Value;
        for (var i = 0; i < 12; i++)
        {
            var items = Assert.IsType<Result.ListValue>(level).Items;
            Assert.Equal(2, items.Count);
            Assert.Same(items[0], items[1]);
            level = items[0];
        }

        Assert.Equal(new Result.Atom(1), level);
        Assert.Equal(12, DistinctStructureNodes(result.Value!));
    }

    [Fact]
    public void MultiEmissionSourceGraph_RepeatsTheSameDeepRootReference()
    {
        const int dagDepth = 12;
        const int duplicationDepth = 5;
        var source = MultiEmissionDagProgram("B", dagDepth, duplicationDepth);
        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        Assert.False(result.IsError);

        var emitted = Assert.IsType<Result.SequenceValue>(result.Value).Items;
        Assert.Equal(1 << duplicationDepth, emitted.Count);
        Assert.All(emitted, item => Assert.Same(emitted[0], item));

        // The sequence root plus the depth-12 A chain: width is explicit in the root edges, but
        // the repeated deep structure remains one physical subgraph.
        Assert.Equal(dagDepth + 1, DistinctStructureNodes(result.Value));
    }

    [Fact]
    public void ReificationObservation_RemainsSemanticallyAndOperationallyPassive()
    {
        // The new expansion counter must not influence evaluation: observed and unobserved runs
        // of the reifying programs agree on outcome and on every budget counter.
        foreach (var source in new[]
        {
            DagProgram("while(A*, 1)", depth: 8),
            DagProgram("((), ()).reduce(map, A)", depth: 8),
        })
        {
            var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
            var (observed, observedBudget) = Evaluator.RunCountedObserved(
                expr, observations: new EvaluationObservations());
            var (unobserved, unobservedBudget) = Evaluator.RunCountedObserved(
                expr, observations: null);

            Assert.Equal(unobserved.IsError, observed.IsError);
            if (!observed.IsError)
            {
                Assert.Equal(unobserved.Value.Value, observed.Value.Value, Result.ValueComparer);
                Assert.Equal(unobserved.Value.EmittedCount, observed.Value.EmittedCount);
            }

            Assert.Equal(unobservedBudget.ConsumedSteps, observedBudget.ConsumedSteps);
            Assert.Equal(unobservedBudget.MaterializedItems, observedBudget.MaterializedItems);
            Assert.Equal(unobservedBudget.PeakDepth, observedBudget.PeakDepth);
        }
    }
}
