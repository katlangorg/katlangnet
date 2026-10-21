using System.Numerics;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;
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
            A = Wrap(1).repeat({depth})
            B = Wrap(1).repeat({depth})
            C = Wrap(2).repeat({depth})
            {body}
            """;

    /// <summary>
    /// STRICT-SOURCE: requires a clean front end, then runs the PLAIN and the COUNTED evaluator and
    /// requires both to agree — the memoized walks are one shared value-level primitive, so neither
    /// entry point may observe different equality or duplicate detection.
    /// </summary>
    private static void AssertEval(string source, params Decimal128[] expected)
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
            SourceProvenance.ParseValid("Wrap = [x, x]\nWrap(1).repeat(3)").Root);

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
        => EvaluatorTestSupport.AssertEvalBools(DagProgram("A == B, A == C, A != B, A != C"), true, false, false, true);

    [Fact]
    public void SharedGraphContains()
    {
        // The searched item is compared against a structurally equal graph, so the scan cannot
        // short-circuit on a shape mismatch — it performs the full deep comparison.
        EvaluatorTestSupport.AssertEvalBool(DagProgram("contains((A, 5), B)"), true);
        EvaluatorTestSupport.AssertEvalBool(DagProgram("contains((A, 5), C)"), false);
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
        // value structurally against the bound one. Select the graph VALUES so the
        // test exercises deep equality, independently of A/B's distinct callable
        // identities (equal-valued distinct callables deliberately reject).
        AssertEval(DagProgram("Same(v, v) = 1\nSame([A][0], [B][0])"), 1);

        var mismatched = Evaluator.RunFlat(new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid(DagProgram("Same(v, v) = 1\nSame([A][0], [C][0])")).Root));
        Assert.True(mismatched.IsError);
        var error = mismatched.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        Assert.IsType<EvalError.BadArity>(error);
    }

    // ══ SEC-02: one OPERATION memo per contains/distinct, charged to the run's budget ══════════
    //
    // The memos above live for ONE top-level call, so a bulk operation over many items repeated
    // the same deep walk once per item: contains over N references to a depth-D value expanded
    // N × (D + 1) pairs, distinct hashed it N times, and none of that work observed cancellation
    // or charged a step. An operation comparer (Result.CreateOperationComparer) keeps COMPLETED
    // verdicts and hashes for the whole operation and charges every inspected child slot and completed frame.

    private const int RepeatCount = 50;

    // Exact operation-walk costs on the doubling DAGs. An operation memo retains a pair or node only
    // when it descends into a nested structure (or is wide), so the narrow all-leaf pair at the bottom
    // of a doubling DAG is re-walked at its second occurrence — one extra expansion per FULL walk —
    // and a repeated narrow top-level item costs one root expansion whose children are memo answers.
    // SharedDag(d) has d + 1 distinct structure nodes; the language DAG (Wrap(1).repeat(d)) has d.

    /// <summary>Expansions of one equal (or hashed) walk of <see cref="SharedDag"/> at depth d.</summary>
    private static long FullWalk(int depth) => depth + 2L;

    /// <summary>Expansions of one deepest-leaf mismatch walk of <see cref="SharedDag"/> at depth d.</summary>
    private static long MismatchWalk(int depth) => depth + 1L;

    /// <summary>The same for the language-built DAG of <see cref="DagProgram"/>.</summary>
    private const long LanguageFullWalk = DeepDepth + 1L;

    private const long LanguageMismatchWalk = DeepDepth;

    private static Result.ValueSemanticComparer OperationComparer(
        out ValueTraversalObservations observations,
        EvaluationBudget? budget = null,
        Action<long>? beforeCharge = null)
    {
        observations = new ValueTraversalObservations { BeforeStructuralWorkCharge = beforeCharge };
        return Result.CreateOperationComparer(budget ?? EvaluationBudget.Create(limits: null), observations);
    }

    /// <summary>The pre-SEC-02 contains: a fresh per-call memo for every item.</summary>
    private static (bool Found, long PairExpansions) PerCallContains(IReadOnlyList<Result> items, Result searched)
    {
        var (comparer, observations) = Observed();
        var found = items.Any(item => comparer.Equals(item, searched));
        return (found, observations.EqualityPairExpansionCount);
    }

    /// <summary>The pre-SEC-02 distinct: one shared per-call comparer behind the set.</summary>
    private static (int Kept, long HashExpansions, long PairExpansions) PerCallDistinct(IReadOnlyList<Result> items)
    {
        var (comparer, observations) = Observed();
        var set = new HashSet<Result>(comparer);
        var kept = items.Count(set.Add);
        return (kept, observations.HashStructureExpansionCount, observations.EqualityPairExpansionCount);
    }

    private static Result[] Repeated(Result value, int count, params Result[] tail)
        => [.. Enumerable.Repeat(value, count), .. tail];

    private static bool OperationContains(IReadOnlyList<Result> items, Result searched, out ValueTraversalObservations observations)
    {
        var comparer = OperationComparer(out observations);
        var found = false;
        foreach (var item in items)
        {
            if (comparer.Equals(item, searched))
            {
                found = true;
                break;
            }
        }

        Assert.Null(comparer.CompleteOperation());
        return found;
    }

    // ── T1: repeated deep equality ──────────────────────────────────────────────────────────

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public void Operation_RepeatedDeepReference_IsComparedOnce(int depth)
    {
        var searched = SharedDag(depth, leafB: 3);
        var items = Repeated(SharedDag(depth), RepeatCount);

        // Before: every item re-walks the same (deep, searched) pair from scratch.
        var before = PerCallContains(items, searched);
        Assert.False(before.Found);
        Assert.Equal(RepeatCount * (depth + 1L), before.PairExpansions);

        // After: the first comparison decides the deep pairs UNEQUAL; each later item expands only
        // its narrow root, whose child pair is a memo answer — O(N + D), not O(N × D).
        Assert.False(OperationContains(items, searched, out var observations));
        Assert.Equal(MismatchWalk(depth) + (RepeatCount - 1), observations.EqualityPairExpansionCount);
    }

    [Fact]
    public void Operation_RepeatedEqualReference_IsComparedOnce()
    {
        var comparer = OperationComparer(out var observations);
        var left = SharedDag(DeepDepth);
        var right = SharedDag(DeepDepth);

        for (var i = 0; i < RepeatCount; i++)
            Assert.True(comparer.Equals(left, right));

        Assert.Equal(FullWalk(DeepDepth) + (RepeatCount - 1), observations.EqualityPairExpansionCount);
        Assert.Null(comparer.CompleteOperation());
    }

    [Fact]
    public void Operation_RepeatedWideReference_IsAnsweredWithoutAWalk()
    {
        // A wide top-level pair is retained itself: every repetition is answered from the memo.
        var comparer = OperationComparer(out var observations);
        var left = List([.. Enumerable.Range(0, 1000).Select(i => Atom(i))]);
        var right = List([.. Enumerable.Range(0, 999).Select(i => Atom(i)), Atom(-1)]);

        for (var i = 0; i < RepeatCount; i++)
            Assert.False(comparer.Equals(left, right));

        Assert.Equal(1, observations.EqualityPairExpansionCount);
        Assert.Null(comparer.CompleteOperation());
        Assert.Equal(1001, observations.StructuralWorkUnits);
    }

    [Fact]
    public void Contains_RepeatedDeepReference_ExpandsOnePairWalk_AtLanguageLevel()
    {
        var items = string.Join(", ", Enumerable.Repeat("A", RepeatCount));
        var (result, _, traversal) = RunObserved(DagProgram($"contains(({items}), C)"));

        AssertBool(false, result);
        Assert.Equal(LanguageMismatchWalk + (RepeatCount - 1), traversal.EqualityPairExpansionCount);
    }

    // ── T2: the first match still stops the scan ────────────────────────────────────────────

    [Theory]
    [InlineData(0)]
    [InlineData(3)]
    [InlineData(9)]
    public void Operation_Contains_StopsAtTheFirstMatch(int matchIndex)
    {
        // Every non-matching item is an independent deep value with its OWN deepest-leaf mismatch,
        // so each comparison the scan performs costs exactly one mismatch walk, and the match one
        // full walk: the count shows exactly how many items were compared.
        const int depth = 10;
        var searched = SharedDag(depth);
        var items = Enumerable.Range(0, 10)
            .Select(i => i == matchIndex ? SharedDag(depth) : SharedDag(depth, leafB: 100 + i))
            .ToArray();

        Assert.True(OperationContains(items, searched, out var observations));
        Assert.Equal(matchIndex * MismatchWalk(depth) + FullWalk(depth), observations.EqualityPairExpansionCount);
    }

    [Fact]
    public void Contains_FirstMatchStopsBeforeLaterItems_AtLanguageLevel()
    {
        // B matches A at index 1; the later C (a deep mismatch) is never compared.
        var (early, _, earlyTraversal) = RunObserved(DagProgram("contains((5, B, C, C), A)"));
        AssertBool(true, early);
        Assert.Equal(LanguageFullWalk, earlyTraversal.EqualityPairExpansionCount);

        var (late, _, lateTraversal) = RunObserved(DagProgram("contains((5, C, B), A)"));
        AssertBool(true, late);
        Assert.Equal(LanguageMismatchWalk + LanguageFullWalk, lateTraversal.EqualityPairExpansionCount);
    }

    // ── T3: repeated deep hashing ───────────────────────────────────────────────────────────

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public void Operation_RepeatedDeepReference_IsHashedOnce(int depth)
    {
        var items = Repeated(SharedDag(depth), RepeatCount, SharedDag(depth));

        // Before: N + 1 full hashes, then one full equality for the rebuilt duplicate.
        var before = PerCallDistinct(items);
        Assert.Equal(1, before.Kept);
        Assert.Equal((RepeatCount + 1L) * (depth + 1), before.HashExpansions);
        Assert.Equal(depth + 1L, before.PairExpansions);

        // After: one full hash of each distinct graph; a repeat expands only its narrow root, whose
        // children are replayed from the operation memo.
        var comparer = OperationComparer(out var observations);
        var set = new HashSet<Result>(comparer);
        Assert.Equal(1, items.Count(set.Add));
        Assert.Equal(2 * FullWalk(depth) + (RepeatCount - 1), observations.HashStructureExpansionCount);
        Assert.Equal(FullWalk(depth), observations.EqualityPairExpansionCount);
        Assert.Null(comparer.CompleteOperation());
    }

    [Fact]
    public void Distinct_RepeatedDeepReference_HashesOnce_AtLanguageLevel()
    {
        var items = string.Join(", ", Enumerable.Repeat("A", RepeatCount));
        var (result, _, traversal) = RunObserved(DagProgram($"distinct(({items}, B, C)).count"));

        AssertNumber(2, result);
        // A, B and C are three independent graphs: three hashes and one A-versus-B equality walk
        // (C could add a deep mismatch walk only through a hash collision).
        Assert.Equal(3 * LanguageFullWalk + (RepeatCount - 1), traversal.HashStructureExpansionCount);
        Assert.InRange(traversal.EqualityPairExpansionCount, LanguageFullWalk, LanguageFullWalk + LanguageMismatchWalk);
    }

    // ── T4: shared INTERNAL nodes are reused across distinct top-level values ────────────────

    [Fact]
    public void Operation_SharedInternalNode_IsDecidedOnceAcrossDistinctWrappers()
    {
        var shared = SharedDag(DeepDepth);
        var searched = List(SharedDag(DeepDepth, leafB: 3));
        var items = Enumerable.Range(0, RepeatCount).Select(_ => List(shared)).ToArray();

        var before = PerCallContains(items, searched);
        Assert.Equal(RepeatCount * (DeepDepth + 2L), before.PairExpansions);

        // Each fresh wrapper pair is a new pair (one expansion), but the deep (shared, searched)
        // pair below it is decided UNEQUAL by the first walk and answered from the memo after.
        Assert.False(OperationContains(items, searched, out var observations));
        Assert.Equal(DeepDepth + 2L + (RepeatCount - 1), observations.EqualityPairExpansionCount);
    }

    [Fact]
    public void Operation_SharedInternalNode_IsHashedOnceAcrossDistinctWrappers()
    {
        var shared = SharedDag(DeepDepth);
        var items = Enumerable.Range(0, RepeatCount).Select(i => List(shared, Atom(i))).ToArray();

        var before = PerCallDistinct(items);
        Assert.Equal(RepeatCount, before.Kept);
        Assert.Equal(RepeatCount * (DeepDepth + 2L), before.HashExpansions);

        var comparer = OperationComparer(out var observations);
        var set = new HashSet<Result>(comparer);
        Assert.Equal(RepeatCount, items.Count(set.Add));
        Assert.Equal(1 + FullWalk(DeepDepth) + (RepeatCount - 1), observations.HashStructureExpansionCount);
        Assert.Null(comparer.CompleteOperation());
    }

    [Fact]
    public void SharedInternalNodes_AreReused_AtLanguageLevel()
    {
        // Every [A] is a FRESH wrapper around the one shared A.
        var wrappers = string.Join(", ", Enumerable.Repeat("[A]", RepeatCount));

        var (contains, _, containsTraversal) = RunObserved(DagProgram($"contains(({wrappers}), [C])"));
        AssertBool(false, contains);
        Assert.Equal(1 + LanguageMismatchWalk + (RepeatCount - 1), containsTraversal.EqualityPairExpansionCount);

        var (distinct, _, distinctTraversal) = RunObserved(DagProgram($"distinct(({wrappers})).count"));
        AssertNumber(1, distinct);
        Assert.Equal(1 + LanguageFullWalk + (RepeatCount - 1), distinctTraversal.HashStructureExpansionCount);
        // Each later wrapper equals the first: one wrapper-pair expansion, A against A by reference.
        Assert.Equal(RepeatCount - 1L, distinctTraversal.EqualityPairExpansionCount);
    }

    // ── T5/T6: a reused operation memo never changes a verdict or a hash ─────────────────────

    /// <summary>
    /// Values chosen so that reused verdicts COULD go wrong: shared and rebuilt equal graphs, the
    /// same left node against unequal right nodes, deepest-leaf mismatches, list/sequence kinds,
    /// lengths, empties, and the numeric/string/Boolean value identities.
    /// </summary>
    private static Result[] AdversarialValues()
    {
        var shared = List(Atom(1), Atom(2));
        var nan = new Result.Atom(Decimal128.NaN);
        var negativeZero = new Result.Atom(Decimal128.NegativeZero);
        var quantum = new Result.Atom(Decimal128.Parse("1.50"));
        return
        [
            SharedDag(6),
            SharedDag(6),
            SharedDag(6, leafB: 3),
            SharedDag(6, leafA: 3),
            List(SharedDag(5), SharedDag(5)),
            List(SharedDag(5), SharedDag(5, leafB: 3)),
            List(shared, shared),
            List(List(Atom(1), Atom(2)), List(Atom(1), Atom(2))),
            List(List(Atom(1), Atom(2)), List(Atom(1), Atom(3))),
            List(Seq(Atom(1), Atom(2)), Seq(Atom(1), Atom(2))),
            Seq(shared, shared),
            List(shared),
            List(shared, shared, shared),
            List(List(), Seq()),
            List(Seq(), List()),
            List(),
            Seq(),
            List(Atom(1.5m), quantum),
            List(Atom(1.5m), Atom(1.5m)),
            List(nan, Atom(0)),
            List(new Result.Atom(Decimal128.NaN), Atom(0)),
            List(nan, negativeZero),
            List(new Result.Str("a"), new Result.Bool(true)),
            List(new Result.Str("a"), new Result.Bool(true)),
            List(new Result.Str("A"), new Result.Bool(true)),
            List(Atom(1), new Result.Bool(true)),
            nan,
            negativeZero,
            Atom(0),
            quantum,
            Atom(1.5m),
            new Result.Str("text"),
            new Result.Bool(false),
        ];
    }

    [Fact]
    public void Operation_OneMemoAcrossEveryOrderedPair_MatchesThePublicComparer()
    {
        var values = AdversarialValues();
        var comparer = OperationComparer(out _);

        // Every ordered pair, twice, through ONE operation memo: the second sweep is answered
        // almost entirely from retained verdicts and must not differ anywhere.
        for (var sweep = 0; sweep < 2; sweep++)
        {
            foreach (var left in values)
            {
                foreach (var right in values)
                    Assert.Equal(Result.ValueComparer.Equals(left, right), comparer.Equals(left, right));
            }
        }

        // Hashes are the public recipe exactly, memo replays included, so equal values agree.
        foreach (var value in values.Concat(values.Reverse()))
            Assert.Equal(Result.ValueComparer.GetHashCode(value), comparer.GetHashCode(value));

        Assert.Null(comparer.CompleteOperation());
    }

    [Fact]
    public void Operation_SameLeftAgainstEqualThenUnequalRight_KeepsBothVerdicts()
    {
        var comparer = OperationComparer(out var observations);
        var left = SharedDag(DeepDepth);
        var equal = SharedDag(DeepDepth);
        var unequal = SharedDag(DeepDepth, leafB: 3);

        Assert.True(comparer.Equals(left, equal));
        Assert.False(comparer.Equals(left, unequal));
        Assert.True(comparer.Equals(left, equal));
        Assert.False(comparer.Equals(left, unequal));
        Assert.False(comparer.Equals(unequal, left));
        Assert.True(comparer.Equals(equal, left));

        // (left, equal), (left, unequal), (unequal, left) and (equal, left) are four ordered pair
        // walks; each repeat expands only the narrow root, whose child pair is a memo answer.
        Assert.Equal(
            2 * FullWalk(DeepDepth) + 2 * MismatchWalk(DeepDepth) + 2,
            observations.EqualityPairExpansionCount);
    }

    [Fact]
    public void Operation_PartialMatchBeforeAMismatch_KeepsTheCompletedEqualSubpairs()
    {
        // The first child pair completes EQUAL before the second child mismatches. Only the open
        // path is decided unequal, so later comparisons reusing the first child pair stay correct.
        var comparer = OperationComparer(out var observations);
        var deepLeft = SharedDag(8);
        var deepRight = SharedDag(8);

        Assert.False(comparer.Equals(List(deepLeft, Atom(1)), List(deepRight, Atom(2))));
        var afterFirst = observations.EqualityPairExpansionCount;
        Assert.Equal(1 + FullWalk(8), afterFirst);

        Assert.True(comparer.Equals(List(deepLeft), List(deepRight)));
        Assert.True(comparer.Equals(deepLeft, deepRight));
        Assert.False(comparer.Equals(List(deepLeft, Atom(1)), List(deepRight, Atom(2))));
        // Only the two new wrapper pairs were expanded; (deepLeft, deepRight) was answered EQUAL.
        Assert.Equal(afterFirst + 2, observations.EqualityPairExpansionCount);
    }

    [Fact]
    public void Operation_KindsLengthsAndLeafIdentitiesAreUnchanged()
    {
        var comparer = OperationComparer(out _);
        var nan = new Result.Atom(Decimal128.NaN);
        var negativeZero = new Result.Atom(Decimal128.NegativeZero);

        Assert.False(comparer.Equals(List(Atom(1), Atom(2)), Seq(Atom(1), Atom(2))));
        Assert.False(comparer.Equals(List(Seq(Atom(1))), List(List(Atom(1)))));
        Assert.False(comparer.Equals(List(Atom(1), Atom(2)), List(Atom(1))));
        Assert.True(comparer.Equals(List(nan), List(new Result.Atom(Decimal128.NaN))));
        Assert.True(comparer.Equals(Atom(1.5m), new Result.Atom(Decimal128.Parse("1.50"))));
        Assert.Equal(Result.ValueComparer.Equals(Atom(0), negativeZero), comparer.Equals(Atom(0), negativeZero));
        Assert.Equal(Result.ValueComparer.Equals(List(Atom(0)), List(negativeZero)), comparer.Equals(List(Atom(0)), List(negativeZero)));
        Assert.True(comparer.Equals(List(new Result.Str("a")), List(new Result.Str("a"))));
        Assert.False(comparer.Equals(List(new Result.Str("a")), List(new Result.Str("A"))));
        Assert.False(comparer.Equals(new Result.Bool(true), Atom(1)));
        Assert.False(comparer.Equals(List(new Result.Bool(false)), List(Atom(0))));
        Assert.Equal(
            comparer.GetHashCode(List(Atom(1.5m))),
            comparer.GetHashCode(List(new Result.Atom(Decimal128.Parse("1.50")))));
        Assert.Equal(comparer.GetHashCode(List(nan)), comparer.GetHashCode(List(new Result.Atom(Decimal128.NaN))));
        Assert.Null(comparer.CompleteOperation());
    }

    [Fact]
    public void Operation_DistinctKeepsFirstOccurrenceReferencesAndOrder()
    {
        var first = SharedDag(6);
        var other = SharedDag(6, leafB: 3);
        var sequenceShaped = Seq(Atom(1), Atom(2));
        var listShaped = List(Atom(1), Atom(2));
        Result[] items = [other, first, SharedDag(6), sequenceShaped, listShaped, other, first, List(Atom(1), Atom(2))];

        var comparer = OperationComparer(out _);
        var set = new HashSet<Result>(comparer);
        var kept = items.Where(set.Add).ToArray();

        Assert.Equal(4, kept.Length);
        Assert.Same(other, kept[0]);
        Assert.Same(first, kept[1]);
        Assert.Same(sequenceShaped, kept[2]);
        Assert.Same(listShaped, kept[3]);
        Assert.Null(comparer.CompleteOperation());
    }

    [Fact]
    public void Operation_CallReferencesKeepPlanAndArgumentViewIdentity()
    {
        var plan = new Evaluator.InvocationPlan(Evaluator.EvalCtx.Empty, []);
        var reference = new Result.CallReference(plan);
        var samePlan = new Result.CallReference(plan);
        var otherPlan = new Result.CallReference(new Evaluator.InvocationPlan(Evaluator.EvalCtx.Empty, []));
        Result[] values = [reference, samePlan, reference.ArgumentView, samePlan.ArgumentView, otherPlan, otherPlan.ArgumentView];
        var comparer = OperationComparer(out _);

        foreach (var left in values)
        {
            foreach (var right in values)
            {
                var expected = ReferenceEquals(((Result.CallReference)left).Plan, ((Result.CallReference)right).Plan)
                    && ((Result.CallReference)left).IsArgumentView == ((Result.CallReference)right).IsArgumentView;
                Assert.Equal(expected, comparer.Equals(left, right));
                // Wrap them so the structural walk's leaf cases run as well as the top-level cases.
                Assert.Equal(expected, comparer.Equals(List(left), List(right)));
                if (expected)
                    Assert.Equal(comparer.GetHashCode(List(left)), comparer.GetHashCode(List(right)));
            }

            Assert.Equal(Result.ValueComparer.GetHashCode(left), comparer.GetHashCode(left));
            Assert.Equal(Result.ValueComparer.GetHashCode(List(left)), comparer.GetHashCode(List(left)));
        }

        Assert.Equal(4, values.Distinct(comparer).Count());
        Assert.Null(comparer.CompleteOperation());
    }

    // ── Budget: units, blocks, and the end of the operation ────────────────────────────────

    private static Result WideList(int width, int last)
        => List([.. Enumerable.Range(0, width - 1).Select(i => Atom(i)), Atom(last)]);

    [Fact]
    public void Operation_ChargesNothingForTopLevelLeaves()
    {
        var budget = EvaluationBudget.Create(limits: null);
        var comparer = OperationComparer(out var observations, budget);

        for (var i = 0; i < 1000; i++)
            Assert.False(comparer.Equals(Atom(i), Atom(-1)));
        _ = comparer.GetHashCode(Atom(7));
        _ = comparer.GetHashCode(new Result.Str("text"));
        Assert.Null(comparer.CompleteOperation());

        Assert.Equal(0, observations.StructuralWorkChargeCount);
        Assert.Equal(0, budget.ConsumedStructuralWorkUnits);
        Assert.Equal(0, budget.ConsumedSteps);
    }

    [Fact]
    public void Operation_ChargesChildInspectionsAndStructureCompletions_AndOneStepPerBlock()
    {
        var budget = EvaluationBudget.Create(limits: null);
        var comparer = OperationComparer(out var observations, budget);
        var width = 3 * EvaluationBudget.StructuralWorkUnitsPerStep + 17;

        Assert.True(comparer.Equals(WideList(width, -1), WideList(width, -1)));
        // A memo answer inspects nothing: the repeat costs no unit.
        var left = WideList(width, -1);
        var right = WideList(width, -1);
        Assert.True(comparer.Equals(left, right));
        Assert.True(comparer.Equals(left, right));
        Assert.Null(comparer.CompleteOperation());

        var units = 2L * (width + 1); // Each full comparison also completes its one expanded root.
        Assert.Equal(units, observations.StructuralWorkUnits);
        Assert.Equal(units, budget.ConsumedStructuralWorkUnits);
        Assert.Equal(units / EvaluationBudget.StructuralWorkUnitsPerStep, budget.ConsumedSteps);
        // The expression-work checkpoint counter is a separate batch and is not touched.
        Assert.Equal(0, budget.ConsumedExpressionCheckpoints);
        // Full blocks of UnitsPerCharge, then one remainder charge at completion.
        Assert.Equal(
            (units + Result.ValueSemanticComparer.UnitsPerCharge - 1) / Result.ValueSemanticComparer.UnitsPerCharge,
            observations.StructuralWorkChargeCount);
    }

    [Fact]
    public void Operation_RefusedCharge_ThrowsTheRetainedStepError_AndRetiresTheComparer()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxSteps = 1 });
        var comparer = OperationComparer(out _, budget);
        var width = 2 * EvaluationBudget.StructuralWorkUnitsPerStep + 1;

        var refused = Assert.Throws<StructuralWorkRefusedException>(() => comparer.Equals(WideList(width, 0), WideList(width, 0)));
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(refused.Error);
        Assert.Equal(1, budget.ConsumedSteps);
        // Every block below the refused step boundary was admitted; the refused block was not.
        Assert.Equal(
            2 * EvaluationBudget.StructuralWorkUnitsPerStep - Result.ValueSemanticComparer.UnitsPerCharge,
            budget.ConsumedStructuralWorkUnits);
        Assert.Throws<InvalidOperationException>(() => comparer.Equals(List(Atom(1)), List(Atom(1))));
        Assert.Throws<InvalidOperationException>(() => comparer.CompleteOperation());
    }

    [Fact]
    public async Task Operation_AliasedSelfReferentialGraphTerminates()
    {
        // The same invariant-violating probe as AliasedSelfReferentialGraphTerminatesInsteadOfHangingTheHost,
        // through the operation walks: their first-descent seeding must keep them total too, and
        // repeated calls through one memo must stay total as well.
        var storage = new Result[1];
        var cyclic = Result.ListValue.TakeOwnership(storage);
        storage[0] = cyclic;

        var otherStorage = new Result[1];
        var otherCyclic = Result.ListValue.TakeOwnership(otherStorage);
        otherStorage[0] = otherCyclic;

        var walk = Task.Run(() =>
        {
            var comparer = OperationComparer(out _);
            for (var i = 0; i < 3; i++)
            {
                _ = comparer.Equals(cyclic, otherCyclic);
                _ = comparer.Equals(List(cyclic), List(otherCyclic));
                _ = comparer.GetHashCode(cyclic);
                _ = comparer.GetHashCode(List(cyclic));
            }

            Assert.Null(comparer.CompleteOperation());
        });

        var finished = await Task.WhenAny(walk, Task.Delay(TimeSpan.FromSeconds(30)));
        Assert.True(
            ReferenceEquals(finished, walk),
            "operation equality/hashing did not terminate on an aliased self-referential graph");
        await walk;
    }

    [Fact]
    public void Operation_CompletedComparer_RetainsNoMemoAndRefusesReuse()
    {
        var comparer = OperationComparer(out _);
        Assert.True(comparer.Equals(SharedDag(4), SharedDag(4)));
        Assert.Null(comparer.CompleteOperation());
        Assert.Throws<InvalidOperationException>(() => comparer.Equals(SharedDag(4), SharedDag(4)));
        Assert.Throws<InvalidOperationException>(() => comparer.GetHashCode(SharedDag(4)));
    }

    // ── T7/T8: cancellation is observed INSIDE one long walk ────────────────────────────────

    /// <summary>A nested chain <c>[[[…[leaf]…, 1], 0]</c>, built independently on each call.</summary>
    private static Result Chain(int depth, decimal leaf)
    {
        var node = List(Atom(leaf));
        for (var i = 0; i < depth; i++)
            node = List(node, Atom(i));
        return node;
    }

    [Fact]
    public void Operation_Equality_ObservesCancellationAtADeterministicCheckpoint()
    {
        using var cts = new CancellationTokenSource();
        var budget = EvaluationBudget.Create(limits: null, cancellationToken: cts.Token);
        var comparer = OperationComparer(out var observations, budget, ordinal => { if (ordinal == 3) cts.Cancel(); });

        // About 10,000 units to the deepest-leaf mismatch: far more than three charges' worth.
        var thrown = Assert.ThrowsAny<OperationCanceledException>(() => comparer.Equals(Chain(5_000, 1), Chain(5_000, 2)));
        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.Equal(3, observations.StructuralWorkChargeCount);
        Assert.Equal(3L * Result.ValueSemanticComparer.UnitsPerCharge, observations.StructuralWorkUnits);
        // The interrupted walk left in-progress entries: the comparer refuses every later use.
        Assert.Throws<InvalidOperationException>(() => comparer.Equals(List(Atom(1)), List(Atom(1))));
    }

    [Fact]
    public void Operation_Hash_ObservesCancellationAtADeterministicCheckpoint()
    {
        using var cts = new CancellationTokenSource();
        var budget = EvaluationBudget.Create(limits: null, cancellationToken: cts.Token);
        var comparer = OperationComparer(out var observations, budget, ordinal => { if (ordinal == 2) cts.Cancel(); });

        var thrown = Assert.ThrowsAny<OperationCanceledException>(() => comparer.GetHashCode(Chain(5_000, 1)));
        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.Equal(2, observations.StructuralWorkChargeCount);
        Assert.Throws<InvalidOperationException>(() => comparer.GetHashCode(Chain(2, 1)));
    }

    private static Result SingletonChain(int depth, decimal leaf)
    {
        var value = Atom(leaf);
        for (var i = 0; i < depth; i++)
            value = List(value);
        return value;
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void Operation_Equality_ObservesCancellationWhileCompletingDeepFrames(bool equal)
    {
        const int depth = 4 * Result.ValueSemanticComparer.UnitsPerCharge;
        using var cts = new CancellationTokenSource();
        var budget = EvaluationBudget.Create(limits: null, cancellationToken: cts.Token);
        var comparer = OperationComparer(out var observations, budget, ordinal => { if (ordinal == 5) cts.Cancel(); });

        // All child positions are visited in the first four charges. A singleton chain then has
        // no more children to inspect: cancellation must still interrupt completion/mismatch unwind.
        var thrown = Assert.ThrowsAny<OperationCanceledException>(() =>
            comparer.Equals(SingletonChain(depth, 1), SingletonChain(depth, equal ? 1 : 2)));
        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.Equal(depth, observations.EqualityPairExpansionCount);
        Assert.Equal(5, observations.StructuralWorkChargeCount);
        Assert.Throws<InvalidOperationException>(() => comparer.CompleteOperation());
    }

    [Fact]
    public void Operation_Hash_ObservesCancellationWhileCompletingDeepFrames()
    {
        const int depth = 4 * Result.ValueSemanticComparer.UnitsPerCharge;
        using var cts = new CancellationTokenSource();
        var budget = EvaluationBudget.Create(limits: null, cancellationToken: cts.Token);
        var comparer = OperationComparer(out var observations, budget, ordinal => { if (ordinal == 5) cts.Cancel(); });

        var thrown = Assert.ThrowsAny<OperationCanceledException>(() => comparer.GetHashCode(SingletonChain(depth, 1)));
        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.Equal(depth, observations.HashStructureExpansionCount);
        Assert.Equal(5, observations.StructuralWorkChargeCount);
        Assert.Throws<InvalidOperationException>(() => comparer.CompleteOperation());
    }

    [Theory]
    [InlineData("contains((W, X), Y)")]
    [InlineData("distinct((W, X, Y)).count")]
    public async Task Builtin_ObservesCancellationDuringItsStructuralWalk(string body)
    {
        foreach (var route in AllRoutes)
        {
            using var cts = new CancellationTokenSource();
            var charges = 0L;
            var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => RunObservedOn(
                route,
                WideProgram(body),
                beforeCharge: ordinal =>
                {
                    charges = ordinal;
                    if (ordinal == 2) cts.Cancel();
                },
                token: cts.Token));
            Assert.Equal(cts.Token, thrown.CancellationToken);
            Assert.Equal(2, charges);
        }
    }

    // ── T9: a finite step budget stops the structural work ─────────────────────────────────

    /// <summary>
    /// W and X are independent equal lists of 3,000 numbers; Y differs only in its last number.
    /// Comparing either against Y inspects 3,000 child slots, so two such comparisons cross one
    /// 4096-unit structural step.
    /// </summary>
    private static string WideProgram(string body)
        => $$"""
            W = range(1, 3000)
            X = range(1, 3000).map{n * 1}
            Y = range(1, 3000).map{if(n == 3000, 0, n)}
            {{body}}
            """;

    [Theory]
    [InlineData("contains((W, X), Y)")]
    [InlineData("distinct((W, X, Y)).count")]
    public void FiniteStepBudget_StopsStructuralWork_WithTheStructuredStepError(string body)
    {
        var (unlimited, budget, traversal) = RunObserved(WideProgram(body));
        if (unlimited.IsError)
            Assert.Fail($"Expected success but got error: {unlimited.Error}");

        Assert.True(budget.ConsumedStructuralWorkUnits >= EvaluationBudget.StructuralWorkUnitsPerStep);
        Assert.Equal(budget.ConsumedStructuralWorkUnits, traversal.StructuralWorkUnits);
        var steps = budget.ConsumedSteps;

        var (exact, _, _) = RunObserved(WideProgram(body), new EvaluationLimits { MaxSteps = steps });
        Assert.False(exact.IsError, exact.IsError ? exact.Error.ToString() : null);
        Assert.True(Result.ValueComparer.Equals(unlimited.Value.Value, exact.Value.Value));

        var (refused, refusedBudget, _) = RunObserved(WideProgram(body), new EvaluationLimits { MaxSteps = steps - 1 });
        Assert.True(refused.IsError);
        var error = refused.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(error);
        Assert.Equal(steps - 1, refusedBudget.ConsumedSteps);
    }

    [Fact]
    public void FiniteStepBudget_ReachesTheEngineAsTheStepLimitError()
    {
        var source = WideProgram("contains((W, X), Y)");
        var (_, budget, _) = RunObserved(source);

        var refused = KatLangEngine.Run(source, new RunOptions { EvaluationLimits = new EvaluationLimits { MaxSteps = budget.ConsumedSteps - 1 } });
        var failure = Assert.IsType<RunResult.EvalFailure>(refused);
        Assert.Contains(failure.Errors, error => error.Code == KatLangErrorCode.EvaluationStepLimitExceeded);

        var admitted = KatLangEngine.Run(source, new RunOptions { EvaluationLimits = new EvaluationLimits { MaxSteps = budget.ConsumedSteps } });
        Assert.IsType<RunResult.Success>(admitted);
    }

    // ── T10: every route charges the same structural work ─────────────────────────────────

    private enum Route { Generic, Optimized, ForcedTwin, SuspendingTwin }

    private static readonly Route[] AllRoutes = [Route.Generic, Route.Optimized, Route.ForcedTwin, Route.SuspendingTwin];

    [Theory]
    [InlineData("contains((W, X, W, X), Y)")]
    [InlineData("distinct((W, X, Y, W, X, Y)).count")]
    [InlineData("range(1, 3).map{if(contains((W, X), Y), n, 0 - n)}")]
    [InlineData("[W, X, Y].filter{contains((W, X), n)}.count")]
    [InlineData("Small = range(1, 400).map{[n mod 7, [n mod 3]]}\ndistinct(Small).count")]
    [InlineData("Step(k) = k + if(contains((W, Y), X), 1, 0)\nStep(0).repeat(3)")]
    public async Task Routes_AgreeOnResultStepsAndStructuralWork(string body)
    {
        var source = WideProgram(body);
        var observations = new List<string>();
        foreach (var route in AllRoutes)
        {
            var (result, budget, traversal) = await RunObservedOn(route, source);
            if (result.IsError)
                Assert.Fail($"{route}: {result.Error}");
            observations.Add(string.Join(
                " | ",
                Describe(result.Value.Value),
                result.Value.EmittedCount,
                budget.ConsumedSteps,
                budget.ConsumedStructuralWorkUnits,
                traversal.EqualityPairExpansionCount,
                traversal.HashStructureExpansionCount,
                traversal.StructuralWorkChargeCount));
        }

        Assert.All(observations, observation => Assert.Equal(observations[0], observation));

        // The plain entry point agrees with the counted one.
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var plain = Evaluator.Run(expr);
        Assert.False(plain.IsError);
        var counted = Evaluator.RunCounted(expr);
        Assert.False(counted.IsError);
        Assert.True(Result.ValueComparer.Equals(counted.Value.Value, plain.Value));
    }

    [Theory]
    [InlineData("contains((W, X), Y)")]
    [InlineData("distinct((W, X, Y)).count")]
    public async Task Routes_AgreeAtStructuralStepBudgetBoundaries(string body)
    {
        var source = WideProgram(body);
        var (expected, unlimitedBudget, _) = RunObserved(source, enableOptimizations: false);
        Assert.False(expected.IsError);
        foreach (var route in AllRoutes)
        {
            var (admitted, admittedBudget, _) = await RunObservedOn(
                route, source, limits: new EvaluationLimits { MaxSteps = unlimitedBudget.ConsumedSteps });
            Assert.False(admitted.IsError);
            Assert.True(Result.ValueComparer.Equals(expected.Value.Value, admitted.Value.Value));
            Assert.Equal(unlimitedBudget.ConsumedStructuralWorkUnits, admittedBudget.ConsumedStructuralWorkUnits);
            Assert.Equal(unlimitedBudget.ConsumedSteps, admittedBudget.ConsumedSteps);

            var (refused, refusedBudget, _) = await RunObservedOn(
                route, source, limits: new EvaluationLimits { MaxSteps = unlimitedBudget.ConsumedSteps - 1 });
            Assert.True(refused.IsError);
            var error = refused.Error;
            while (error is EvalError.WithContext context)
                error = context.Inner;
            var stepError = Assert.IsType<EvalError.EvaluationStepLimitExceeded>(error);
            Assert.Equal(unlimitedBudget.ConsumedSteps - 1, refusedBudget.ConsumedSteps);
            // Evaluation may attach the source span by copying the retained error.
            var retained = Assert.IsType<EvalError.EvaluationStepLimitExceeded>(refusedBudget.CheckContinuation());
            Assert.Equal(stepError.Limit, retained.Limit);
            Assert.Same(retained, refusedBudget.CheckContinuation());
        }
    }

    private static string Describe(Result value)
        => value switch
        {
            Result.Atom(var number) => number.ToString(),
            Result.Bool(var flag) => flag ? "true" : "false",
            Result.ListValue(var items) => "[" + string.Join(",", items.Select(Describe)) + "]",
            Result.SequenceValue(var items) => "(" + string.Join(",", items.Select(Describe)) + ")",
            _ => value.GetType().Name,
        };

    // ── T11: isolation across operations, runs, and threads ────────────────────────────────

    [Fact]
    public void TwoOperationsInOneRun_DoNotShareAMemo()
    {
        var (one, _, oneTraversal) = RunObserved(DagProgram("contains((A, A), C)"));
        var (two, _, twoTraversal) = RunObserved(DagProgram("contains((A, A), C), contains((A, A), C)"));

        AssertBool(false, one);
        Assert.False(two.IsError);
        Assert.Equal(LanguageMismatchWalk + 1, oneTraversal.EqualityPairExpansionCount);
        Assert.Equal(2 * (LanguageMismatchWalk + 1), twoTraversal.EqualityPairExpansionCount);
    }

    [Fact]
    public async Task SequentialAndConcurrentRuns_ObserveIdenticalIndependentWork()
    {
        var source = WideProgram("contains((W, X, W, X), Y), distinct((W, X, Y)).count");
        var (_, firstBudget, first) = RunObserved(source);
        var (_, secondBudget, second) = RunObserved(source);
        Assert.Equal(first.StructuralWorkUnits, second.StructuralWorkUnits);
        Assert.Equal(first.EqualityPairExpansionCount, second.EqualityPairExpansionCount);
        Assert.Equal(first.HashStructureExpansionCount, second.HashStructureExpansionCount);
        Assert.Equal(firstBudget.ConsumedSteps, secondBudget.ConsumedSteps);

        using var cancelled = new CancellationTokenSource();
        var runs = Enumerable.Range(0, 8).Select(i => Task.Run(() =>
        {
            if (i == 0)
            {
                Assert.ThrowsAny<OperationCanceledException>(() => RunObserved(
                    source,
                    beforeCharge: ordinal => { if (ordinal == 2) cancelled.Cancel(); },
                    token: cancelled.Token));
                return -1L;
            }

            var (result, budget, traversal) = RunObserved(source);
            Assert.False(result.IsError);
            Assert.Equal(firstBudget.ConsumedSteps, budget.ConsumedSteps);
            return traversal.StructuralWorkUnits;
        })).ToArray();

        var units = await Task.WhenAll(runs);
        Assert.Equal(-1L, units[0]);
        Assert.All(units.Skip(1), observed => Assert.Equal(first.StructuralWorkUnits, observed));
    }

    // ── Language-level run helpers ─────────────────────────────────────────────────────────

    private static (EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget, ValueTraversalObservations Traversal) RunObserved(
        string source,
        EvaluationLimits? limits = null,
        bool enableOptimizations = true,
        Action<long>? beforeCharge = null,
        CancellationToken token = default)
    {
        var traversal = new ValueTraversalObservations { BeforeStructuralWorkCharge = beforeCharge };
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var (result, budget) = Evaluator.RunCountedObserved(
            expr,
            limits,
            enableOptimizations,
            observations: new EvaluationObservations { StructuralTraversal = traversal },
            cancellationToken: token);
        return (result, budget, traversal);
    }

    private static async Task<(EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget, ValueTraversalObservations Traversal)> RunObservedOn(
        Route route,
        string source,
        EvaluationLimits? limits = null,
        Action<long>? beforeCharge = null,
        CancellationToken token = default)
    {
        if (route is not (Route.ForcedTwin or Route.SuspendingTwin))
            return RunObserved(source, limits, enableOptimizations: route is Route.Optimized, beforeCharge: beforeCharge, token: token);

        var traversal = new ValueTraversalObservations { BeforeStructuralWorkCharge = beforeCharge };
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var suspendingCache = route is Route.SuspendingTwin ? new SuspendingAsyncZeroArgPropertyResultCache() : null;
        var (result, budget) = await Evaluator.RunCountedObservedAsync(
            expr,
            limits,
            zeroArgPropertyResultCache: (IZeroArgPropertyResultCache?)suspendingCache ?? new RunScopedAsyncZeroArgPropertyResultCache(),
            observations: new EvaluationObservations { StructuralTraversal = traversal },
            cancellationToken: token);
        if (suspendingCache is not null)
        {
            Assert.True(suspendingCache.AsyncAccesses > 0);
            Assert.Equal(0, suspendingCache.SyncAccesses);
            Assert.NotEmpty(suspendingCache.ThreadHops);
        }
        return (result, budget, traversal);
    }

    private static void AssertBool(bool expected, EvalResult<Evaluator.CountedResult> result)
    {
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal(new Result.Bool(expected), result.Value.Value);
    }

    private static void AssertNumber(decimal expected, EvalResult<Evaluator.CountedResult> result)
    {
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal(new Result.Atom(expected), result.Value.Value);
    }
}
