using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// Truth testing and the bounded atom collectors over SHARED value graphs, the atom-view siblings
/// of the equality/hash walks (<see cref="SharedValueGraphComplexityTests"/>) and the
/// <see cref="Result.Normalize"/> rebuild (<see cref="NormalizeSharedValueGraphTests"/>). A value
/// is a DAG, not a tree — <c>W = (x, x)</c> applied n times reaches n distinct sequence nodes
/// through 2^n root-to-leaf paths — and the atom views flatten one atom per PATH, so any of them
/// whose WORK is per-path is exponential on values an ordinary in-budget loop builds, while no
/// evaluation step budget bounds it: the blow-up happens inside ONE value-level operation.
///
/// <para>Two different fixes are pinned here. <see cref="Result.TruthValue"/> needs only the FIRST
/// flattened atom, so it searches for it and skips sequence nodes already searched through another
/// shared reference: node-bounded outright. <c>Result.TryLanguageAtoms</c> and
/// <c>Result.TryToHostAtoms</c> must keep collecting atoms per path (their contract, bounded by
/// <c>maxItems</c>), so they memoize only structures proven to contribute NO atoms — the nodes
/// whose revisits the atom bound can never stop.</para>
///
/// <para>Work counts are exact and deterministic, measured through the passive operation-scoped
/// <see cref="ValueTraversalObservations"/>; timing is deliberately not a pass/fail signal.
/// Semantics are checked against the unchanged materializing <see cref="Result.ToAtoms"/> view
/// (the pre-fix truth implementation read its first element) and against
/// <see cref="NaiveAtoms"/>, a test-only recursive replica of the path-expanding collection.</para>
/// </summary>
public class AtomViewSharedValueGraphTests
{
    private const int ShallowDepth = 20;

    private const int DeepDepth = 40;

    private const int DeepTraversalDepth = 200_000;

    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result Str(string value) => new Result.Str(value);

    private static Result List(params Result[] items) => Result.ListValue.TakeOwnership(items);

    private static Result Seq(params Result[] items) => Result.SequenceValue.TakeOwnership(items);

    private static ValueTraversalObservations Observations() => new();

    /// <summary>
    /// The sequence doubling DAG: <c>P0 = leaf</c>, <c>Pk = (P(k-1), P(k-1))</c>. A graph of depth
    /// n has n sequence nodes on the spine (plus whatever structure the leaf carries) and 2^n
    /// root-to-leaf paths.
    /// </summary>
    private static Result SharedSeqDag(int depth, Result leaf)
    {
        var node = leaf;
        for (var i = 0; i < depth; i++)
            node = Seq(node, node);
        return node;
    }

    /// <summary>The list doubling DAG: like <see cref="SharedSeqDag"/> with list nodes.</summary>
    private static Result SharedListDag(int depth, Result leaf)
    {
        var node = leaf;
        for (var i = 0; i < depth; i++)
            node = List(node, node);
        return node;
    }

    /// <summary>Doubling DAG alternating sequence and list levels, so both collector arms run.</summary>
    private static Result SharedMixedDag(int depth, Result leaf)
    {
        var node = leaf;
        for (var i = 0; i < depth; i++)
            node = i % 2 == 0 ? Seq(node, node) : List(node, node);
        return node;
    }

    /// <summary>
    /// The pre-fix truth implementation: materialize the whole (per-path) sequence-only
    /// flattening, then read its first element. <see cref="Result.ToAtoms"/> is unchanged, so
    /// this IS the semantic oracle for the first-atom search. Only ever applied to small values.
    /// </summary>
    private static bool? OracleTruth(Result value)
    {
        var atoms = value.ToAtoms();
        return atoms.Count == 0 ? null : atoms[0] != 0;
    }

    /// <summary>
    /// Test-only replica of the path-expanding atom collection: recursive, no memo, one visit per
    /// PATH. <c>languageAtoms</c> and <c>hostAtoms</c> flatten identically (both open sequence and
    /// list boundaries; strings contribute nothing), so one oracle serves both collectors. Only
    /// ever applied to small values — on a doubling DAG it is exponential by construction.
    /// </summary>
    private static List<Decimal128> NaiveAtoms(Result value)
    {
        var collected = new List<Decimal128>();
        Collect(value);
        return collected;

        void Collect(Result node)
        {
            switch (node)
            {
                case Result.Atom(var n):
                    collected.Add(n);
                    break;
                case Result.SequenceValue(var items):
                    foreach (var item in items) Collect(item);
                    break;
                case Result.ListValue(var items):
                    foreach (var item in items) Collect(item);
                    break;
                default:
                    break; // strings contribute no atoms
            }
        }
    }

    /// <summary>Every value kind plus the shared/empty/mixed shapes around them.</summary>
    private static IEnumerable<Result> Corpus()
    {
        var sharedAtomless = Seq(Str("s"), List(Atom(9)));
        var sharedAtomBearing = Seq(Atom(1), List(Atom(2)));
        var sharedListLeaf = List(Str("s"));

        return
        [
            Atom(0),
            Atom(7),
            Atom(-3.5m),
            new Result.Atom(Decimal128.NaN),
            new Result.Atom(Decimal128.NegativeZero),
            new Result.Atom(Decimal128.PositiveInfinity),
            Str(string.Empty),
            Str("text"),
            Seq(),
            List(),
            Seq(Seq()),
            Seq(Seq(), Seq(Seq())),
            List(Seq()),
            Seq(List()),
            Seq(Atom(0), Atom(1)),
            Seq(Atom(1), Atom(0)),
            Seq(Str("x"), Atom(0), Atom(1)),
            Seq(List(Atom(1)), Atom(0)),
            List(Atom(1), Atom(2)),
            List(Seq(Atom(1)), Str("a")),
            Seq(Seq(Seq(Atom(5)))),
            Seq(sharedAtomless, sharedAtomless, Atom(3)),
            Seq(sharedAtomBearing, sharedAtomBearing),
            List(sharedAtomBearing, sharedAtomless, sharedAtomBearing),
            List(sharedListLeaf, sharedListLeaf, Atom(4)),
            SharedSeqDag(4, Atom(1)),
            SharedSeqDag(4, Str("s")),
            SharedListDag(4, List(Atom(1), Atom(2))),
            SharedMixedDag(5, Seq(Atom(0), Atom(1))),
            Seq(SharedSeqDag(3, Str("s")), SharedListDag(3, Str("t")), Atom(0), Atom(1)),
        ];
    }

    // ── Truth search: each distinct sequence node is searched at most once ───────────────────

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public void Truth_SharedAtomDag_FindsTheFirstAtomInDistinctNodeWork(int depth)
    {
        var observations = Observations();

        Assert.Equal(true, SharedSeqDag(depth, Atom(1)).TruthValueObserved(observations));

        // The search descends the leftmost spine only: depth sequence nodes, then the atom.
        // The materializing walk flattened 2^depth atoms first.
        Assert.Equal(depth, observations.TruthSearchStructureExpansionCount);
    }

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public void Truth_AtomlessSharedDag_IsDecidedInDistinctNodeWork(int depth)
    {
        var observations = Observations();

        // No atom anywhere: the whole graph must be searched, but each of the depth distinct
        // sequence nodes only once — the second shared reference of every level is skipped.
        Assert.Null(SharedSeqDag(depth, Str("s")).TruthValueObserved(observations));
        Assert.Equal(depth, observations.TruthSearchStructureExpansionCount);
    }

    [Fact]
    public void Truth_WorkGrowsLinearlyWithGraphDepth()
    {
        var shallow = Observations();
        var deep = Observations();

        Assert.Null(SharedSeqDag(ShallowDepth, Str("s")).TruthValueObserved(shallow));
        Assert.Null(SharedSeqDag(DeepDepth, Str("s")).TruthValueObserved(deep));

        // Twenty more levels cost twenty more searches, not 2^20 times as many.
        Assert.Equal(
            DeepDepth - ShallowDepth,
            deep.TruthSearchStructureExpansionCount - shallow.TruthSearchStructureExpansionCount);
    }

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public void Truth_SharedDag_FirstFlattenedAtomDecides(int depth)
    {
        var observations = Observations();

        // The leaf's first atom is 0 and its second is 1, so the graph's 2^depth later atoms all
        // disagree with the verdict: only the FIRST flattened atom may decide.
        Assert.Equal(false, SharedSeqDag(depth, Seq(Atom(0), Atom(1))).TruthValueObserved(observations));
        Assert.Equal(depth + 1, observations.TruthSearchStructureExpansionCount);
    }

    [Fact]
    public void Truth_SharedAtomlessPrefix_IsSearchedOnceAndSkippedAfter()
    {
        var observations = Observations();
        var atomless = SharedSeqDag(DeepDepth, Str("s"));

        // The deciding atom sits AFTER two references to the atomless graph: the first reference
        // costs one full distinct-node search, the second is skipped outright.
        Assert.Equal(false, Seq(atomless, atomless, Atom(0), Atom(1)).TruthValueObserved(observations));
        Assert.Equal(DeepDepth + 1, observations.TruthSearchStructureExpansionCount);
    }

    // ── Truth search: memo-key discipline ────────────────────────────────────────────────────

    [Fact]
    public void Truth_ValueEqualButDistinctAtomlessNodes_AreSearchedSeparately()
    {
        // Two children that are VALUE-EQUAL but share no reference. A searched-set keyed by
        // KatLang value equality (or its structural hash) would skip the second one; reference
        // identity searches both.
        var left = Seq(Str("s"));
        var right = Seq(Str("s"));
        Assert.True(Result.ValueComparer.Equals(left, right));
        Assert.False(ReferenceEquals(left, right));

        var observations = Observations();
        Assert.Equal(true, Seq(left, right, Atom(1)).TruthValueObserved(observations));
        Assert.Equal(3, observations.TruthSearchStructureExpansionCount);
    }

    [Fact]
    public void Truth_DefaultEqualRecordClones_AreDistinctSearchEntries()
    {
        // A record clone is a distinct Result that shares the read-only wrapper, so it is
        // default-record-equal: a plain HashSet<Result> (generated record equality) would merge
        // the two and skip the clone. Deterministically catches removal of the explicit
        // ReferenceEqualityComparer.
        var left = Assert.IsType<Result.SequenceValue>(Seq(Str("s")));
        var right = left with { };
        Assert.NotSame(left, right);
        Assert.True(left.Equals(right));

        var observations = Observations();
        Assert.Equal(true, Seq(left, right, Atom(1)).TruthValueObserved(observations));
        Assert.Equal(3, observations.TruthSearchStructureExpansionCount);
    }

    [Fact]
    public void Truth_SameReferenceIsSkippedNotResearched()
    {
        var shared = Seq(Str("s"), Seq(Str("t")));

        var observations = Observations();
        Assert.Equal(true, Seq(shared, shared, shared, Atom(1)).TruthValueObserved(observations));

        // Root + the shared node + its inner sequence, once each; the two later references skip.
        Assert.Equal(3, observations.TruthSearchStructureExpansionCount);
    }

    // ── Truth semantics against the materializing oracle ─────────────────────────────────────

    [Fact]
    public void Truth_MatchesTheMaterializingFlattening_AcrossEveryValueShape()
    {
        foreach (var value in Corpus())
            Assert.Equal(OracleTruth(value), value.TruthValue());
    }

    [Fact]
    public void Truth_EmptyAndAtomlessShapes_HaveNoTruthValue()
    {
        Assert.Null(Seq().TruthValue());
        Assert.Null(Seq(Seq(), Seq(Seq())).TruthValue());
        Assert.Null(Str("1").TruthValue());
        Assert.Null(List(Atom(1)).TruthValue());
        Assert.Null(Seq(Str("x"), List(Atom(1))).TruthValue());
        Assert.Null(SharedSeqDag(4, List(Atom(1))).TruthValue());
    }

    [Fact]
    public void Truth_FirstFlattenedAtomDecides_LaterAtomsAreIrrelevant()
    {
        // Empties, strings, and opaque lists before the first atom are passed over in order;
        // the atoms after it never matter.
        var falseFirst = Seq(Seq(), Str("s"), List(Atom(9)), Seq(Seq(Atom(0))), Atom(1));
        Assert.Equal(false, falseFirst.TruthValue());
        Assert.Equal(OracleTruth(falseFirst), falseFirst.TruthValue());

        var trueFirst = Seq(Seq(), Str("s"), List(Atom(9)), Seq(Seq(Atom(1))), Atom(0));
        Assert.Equal(true, trueFirst.TruthValue());
        Assert.Equal(OracleTruth(trueFirst), trueFirst.TruthValue());
    }

    [Fact]
    public void Truth_SpecialAtomValues_FollowTheOrderingOperator()
    {
        // The verdict uses the IEEE ordering operator `!= 0`, exactly like the materializing
        // implementation did: NaN != 0 is true, and negative zero equals zero.
        var nan = new Result.Atom(Decimal128.NaN);
        var negativeZero = new Result.Atom(Decimal128.NegativeZero);

        Assert.Equal(true, nan.TruthValue());
        Assert.Equal(OracleTruth(nan), nan.TruthValue());
        Assert.Equal(false, negativeZero.TruthValue());
        Assert.Equal(OracleTruth(negativeZero), negativeZero.TruthValue());
        Assert.Equal(false, Seq(negativeZero, Atom(1)).TruthValue());
    }

    [Fact]
    public void Truth_DeepAtomlessSequenceChain_RemainsIterative()
    {
        Result value = Str("leaf");
        for (var i = 0; i < DeepTraversalDepth; i++)
            value = Seq(value, Str("tail"));

        var observations = Observations();
        Assert.Null(value.TruthValueObserved(observations));
        Assert.Equal(DeepTraversalDepth, observations.TruthSearchStructureExpansionCount);
    }

    // ── Collectors: atomless shared subgraphs are visited by node, not by path ───────────────

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public void LanguageAtoms_AtomlessSharedDag_VisitsEachNodeAtMostOnce(int depth)
    {
        var observations = Observations();
        var value = SharedListDag(depth, List(Str("s"), Str("t")));

        Assert.True(value.TryLanguageAtomsObserved(long.MaxValue, observations, out var atoms));

        // depth spine nodes plus the leaf list, each descended once; the atom bound never fires
        // on an atomless graph, so before the memo this walk expanded 2^(depth+1) - 1 nodes.
        Assert.Empty(atoms);
        Assert.Equal(depth + 1, observations.LanguageAtomsStructureExpansionCount);
    }

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public void HostAtoms_AtomlessSharedDag_VisitsEachNodeAtMostOnce(int depth)
    {
        var observations = Observations();
        var value = SharedSeqDag(depth, Str("s"));

        Assert.True(value.TryToHostAtomsObserved(long.MaxValue, observations, out var atoms));

        Assert.Empty(atoms);
        Assert.Equal(depth, observations.HostAtomsStructureExpansionCount);
    }

    [Fact]
    public void Collectors_AtomlessMixedKindDag_VisitsEachNodeAtMostOnce()
    {
        var value = SharedMixedDag(DeepDepth, Str("s"));

        var language = Observations();
        Assert.True(value.TryLanguageAtomsObserved(long.MaxValue, language, out var languageAtoms));
        Assert.Empty(languageAtoms);
        Assert.Equal(DeepDepth, language.LanguageAtomsStructureExpansionCount);

        var host = Observations();
        Assert.True(value.TryToHostAtomsObserved(long.MaxValue, host, out var hostAtoms));
        Assert.Empty(hostAtoms);
        Assert.Equal(DeepDepth, host.HostAtomsStructureExpansionCount);
    }

    [Fact]
    public void Collectors_TailChildCompletion_MemoizesTheChildAndItsParent()
    {
        var sharedTail = List(Str("s"), Seq(Str("t")));
        var tailParent = Seq(Str("prefix"), sharedTail);
        var value = List(tailParent, tailParent, sharedTail, Atom(1));

        var language = Observations();
        Assert.True(value.TryLanguageAtomsObserved(long.MaxValue, language, out var languageAtoms));
        Assert.Equal([1m], languageAtoms);
        Assert.Equal(4, language.LanguageAtomsStructureExpansionCount);

        var host = Observations();
        Assert.True(value.TryToHostAtomsObserved(long.MaxValue, host, out var hostAtoms));
        Assert.Equal([1m], hostAtoms);
        Assert.Equal(4, host.HostAtomsStructureExpansionCount);
    }

    [Fact]
    public void Collectors_AtomlessWorkGrowsLinearlyWithGraphDepth()
    {
        var shallowLanguage = Observations();
        var deepLanguage = Observations();
        Assert.True(SharedListDag(ShallowDepth, Str("s")).TryLanguageAtomsObserved(long.MaxValue, shallowLanguage, out _));
        Assert.True(SharedListDag(DeepDepth, Str("s")).TryLanguageAtomsObserved(long.MaxValue, deepLanguage, out _));
        Assert.Equal(
            DeepDepth - ShallowDepth,
            deepLanguage.LanguageAtomsStructureExpansionCount - shallowLanguage.LanguageAtomsStructureExpansionCount);

        var shallowHost = Observations();
        var deepHost = Observations();
        Assert.True(SharedListDag(ShallowDepth, Str("s")).TryToHostAtomsObserved(long.MaxValue, shallowHost, out _));
        Assert.True(SharedListDag(DeepDepth, Str("s")).TryToHostAtomsObserved(long.MaxValue, deepHost, out _));
        Assert.Equal(
            DeepDepth - ShallowDepth,
            deepHost.HostAtomsStructureExpansionCount - shallowHost.HostAtomsStructureExpansionCount);
    }

    // ── Collectors: per-path atom output is preserved; only zero-atom nodes are skipped ──────

    [Fact]
    public void LanguageAtoms_AtomBearingSharedNodes_AreReDescendedPerOccurrence()
    {
        var inner = List(Atom(2));
        var shared = Seq(Atom(1), inner);
        var value = List(shared, shared, Str("x"), Atom(3));

        var observations = Observations();
        Assert.True(value.TryLanguageAtomsObserved(long.MaxValue, observations, out var atoms));

        // Atoms are collected once per PATH — that is the collector's contract — so the shared
        // atom-bearing node contributes twice and is descended twice; the memo may never skip it.
        Assert.Equal([1m, 2m, 1m, 2m, 3m], atoms);
        Assert.Equal(5, observations.LanguageAtomsStructureExpansionCount);
    }

    [Fact]
    public void HostAtoms_AtomBearingSharedNodes_AreReDescendedPerOccurrence()
    {
        var inner = List(Atom(2));
        var shared = Seq(Atom(1), inner);
        var value = List(shared, shared, Str("x"), Atom(3));

        var observations = Observations();
        Assert.True(value.TryToHostAtomsObserved(long.MaxValue, observations, out var atoms));

        Assert.Equal([1m, 2m, 1m, 2m, 3m], atoms);
        Assert.Equal(5, observations.HostAtomsStructureExpansionCount);
    }

    [Fact]
    public void LanguageAtoms_AtomlessSkipDoesNotSuppressAtomsElsewhere()
    {
        var atomlessShared = List(Str("s"), Seq(Str("t")));
        var value = Seq(atomlessShared, List(atomlessShared, Atom(5)), atomlessShared, Atom(6));

        var observations = Observations();
        Assert.True(value.TryLanguageAtomsObserved(long.MaxValue, observations, out var atoms));

        // The atomless node is searched once and skipped twice; the atoms around it survive in
        // flattening order. Root + atomless node + its inner sequence + the middle list.
        Assert.Equal([5m, 6m], atoms);
        Assert.Equal(4, observations.LanguageAtomsStructureExpansionCount);
    }

    [Fact]
    public void Collectors_ValueEqualButDistinctAtomlessNodes_AreDistinctMemoEntries()
    {
        // Value-equal but reference-distinct: both must be descended.
        var left = List(Str("s"));
        var right = List(Str("s"));
        Assert.True(Result.ValueComparer.Equals(left, right));
        Assert.False(ReferenceEquals(left, right));

        var observations = Observations();
        Assert.True(List(left, right, Atom(1)).TryLanguageAtomsObserved(long.MaxValue, observations, out var atoms));
        Assert.Equal([1m], atoms);
        Assert.Equal(3, observations.LanguageAtomsStructureExpansionCount);

        // A default-record-equal clone (shared wrapper) is still a DISTINCT memo entry: a memo
        // using generated record equality would skip it.
        var original = Assert.IsType<Result.ListValue>(List(Str("s")));
        var clone = original with { };
        Assert.NotSame(original, clone);
        Assert.True(original.Equals(clone));

        var cloneObservations = Observations();
        Assert.True(List(original, clone, Atom(1)).TryToHostAtomsObserved(long.MaxValue, cloneObservations, out var cloneAtoms));
        Assert.Equal([1m], cloneAtoms);
        Assert.Equal(3, cloneObservations.HostAtomsStructureExpansionCount);
    }

    // ── Collectors: the atom bound is unchanged, and visits stay bounded beside it ───────────

    [Fact]
    public void LanguageAtoms_AtomBoundStopsCollection_WithTheExactPrefix()
    {
        // 2^4 leaf paths over (1, 2): 32 atoms alternating 1, 2, 1, 2, ...
        var value = SharedListDag(4, List(Atom(1), Atom(2)));

        Assert.False(value.TryLanguageAtoms(3, out var truncated));
        Assert.Equal([1m, 2m, 1m], truncated);

        Assert.False(value.TryLanguageAtoms(31, out _));
        Assert.True(value.TryLanguageAtoms(32, out var full));
        Assert.Equal(32, full.Count);
        Assert.Equal(NaiveAtoms(value), full);

        // The pre-existing edge stays: a zero budget rejects even a lone atom.
        Assert.False(Atom(7).TryLanguageAtoms(0, out var none));
        Assert.Empty(none);
    }

    [Fact]
    public void HostAtoms_AtomBoundStopsCollection_WithTheExactPrefix()
    {
        var value = SharedSeqDag(4, Seq(Atom(1), Atom(2)));

        Assert.False(value.TryToHostAtoms(3, out var truncated));
        Assert.Equal([1m, 2m, 1m], truncated);

        Assert.True(value.TryToHostAtoms(32, out var full));
        Assert.Equal(NaiveAtoms(value), full);
    }

    [Fact]
    public void Collectors_AtomBoundEdges_AreUnchangedAroundSharedAtomlessStructures()
    {
        var atomless = SharedMixedDag(8, Str("s"));
        var value = Seq(Seq(), atomless, List(Seq()), Atom(1), atomless, Atom(2));

        Assert.True(atomless.TryLanguageAtoms(0, out var emptyLanguage));
        Assert.Empty(emptyLanguage);
        Assert.False(value.TryLanguageAtoms(0, out var zeroLanguage));
        Assert.Empty(zeroLanguage);
        Assert.False(value.TryLanguageAtoms(1, out var oneLanguage));
        Assert.Equal([1m], oneLanguage);
        Assert.True(value.TryLanguageAtoms(2, out var exactLanguage));
        Assert.Equal([1m, 2m], exactLanguage);

        Assert.True(atomless.TryToHostAtoms(0, out var emptyHost));
        Assert.Empty(emptyHost);
        Assert.False(value.TryToHostAtoms(0, out var zeroHost));
        Assert.Empty(zeroHost);
        Assert.False(value.TryToHostAtoms(1, out var oneHost));
        Assert.Equal([1m], oneHost);
        Assert.True(value.TryToHostAtoms(2, out var exactHost));
        Assert.Equal([1m, 2m], exactHost);
    }

    [Fact]
    public void Collectors_MatchTheNaiveFlattening_AcrossEveryValueShape()
    {
        foreach (var value in Corpus())
        {
            Assert.True(value.TryLanguageAtoms(long.MaxValue, out var languageAtoms));
            Assert.Equal(NaiveAtoms(value), languageAtoms);

            Assert.True(value.TryToHostAtoms(long.MaxValue, out var hostAtoms));
            Assert.Equal(NaiveAtoms(value), hostAtoms);
        }
    }

    // ── Language-level regressions for the public funnels ────────────────────────────────────

    /// <summary>
    /// The sequence doubling DAG built by an ordinary in-budget loop — the SEQUENCE sibling of
    /// the <c>Wrap = [x, x]</c> recipe the other shared-graph suites use, because truth testing
    /// opens sequence boundaries only: <c>Wrap</c> stores its ONE bound argument in both slots of
    /// one written group, so each step adds one sequence node reachable through twice as many
    /// paths.
    /// </summary>
    private static string SeqDagProgram(string body, string leaf = "1", int depth = DeepDepth)
        => $"""
            Wrap = (x, x)
            D = Wrap.repeat({depth}, {leaf})
            {body}
            """;

    /// <summary>
    /// STRICT-SOURCE: requires a clean front end, then runs the PLAIN and the COUNTED evaluator
    /// and requires both to agree — the fixes live at the Result level, so neither entry point
    /// may observe a different verdict.
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

    private static void AssertEvalError<TError>(string source)
        where TError : EvalError
    {
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

        var plain = Evaluator.Run(expr);
        Assert.True(plain.IsError, "Expected an error from the plain evaluator.");
        Assert.IsType<TError>(Innermost(plain.Error));

        var counted = Evaluator.RunCounted(expr);
        Assert.True(counted.IsError, "Expected an error from the counted evaluator.");
        Assert.IsType<TError>(Innermost(counted.Error));
    }

    private static EvalError Innermost(EvalError error)
        => error is EvalError.WithContext(_, var inner) ? Innermost(inner) : error;

    [Fact]
    public void LanguageBuiltDoublingSequenceIsOneSharedGraph()
    {
        // The premise of every case below: the loop builds a sequence DAG, not a tree. Without
        // sharing the depth-40 values would be 2^40 nodes and could not be built at all.
        var expr = new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid("Wrap = (x, x)\nWrap.repeat(3, 1)").Root);

        var plain = Evaluator.Run(expr);
        if (plain.IsError)
            Assert.Fail($"Expected success but got error: {plain.Error}");
        var sequence = Assert.IsType<Result.SequenceValue>(plain.Value);
        Assert.Same(sequence.Items[0], sequence.Items[1]);
        var inner = Assert.IsType<Result.SequenceValue>(sequence.Items[0]);
        Assert.Same(inner.Items[0], inner.Items[1]);

        var counted = Evaluator.RunCounted(expr);
        if (counted.IsError)
            Assert.Fail($"Expected counted success but got error: {counted.Error}");
        var countedSequence = Assert.IsType<Result.SequenceValue>(counted.Value.Value);
        Assert.Same(countedSequence.Items[0], countedSequence.Items[1]);
    }

    [Fact]
    public void IfOnSharedAtomDag_IsTrue()
        // The H2 repro: before the first-atom search, deciding this condition materialized 2^40
        // atoms inside one uncancellable, unbudgeted value operation.
        => AssertEval(SeqDagProgram("if(D, 1, 0)"), 1);

    [Fact]
    public void IfOnSharedZeroLeafDag_IsFalse()
        => AssertEval(SeqDagProgram("if(D, 1, 0)", leaf: "0"), 0);

    [Fact]
    public void IfOnSharedDag_FirstFlattenedAtomDecides()
        // Every level doubles a (0, 1) leaf, so all 2^40 later atoms disagree with the verdict.
        => AssertEval(SeqDagProgram("if(D, 1, 0)", leaf: "(0, 1)"), 0);

    [Fact]
    public void IfOnAtomlessSharedDag_FailsFastWithBadArity()
        // No atom anywhere: the condition has no truth value, and deciding THAT must also be
        // distinct-node work, not path work.
        => AssertEvalError<EvalError.BadArity>(SeqDagProgram("if(D, 1, 0)", leaf: "'s'"));

    [Fact]
    public async Task IfOnSharedDag_AsyncTwinAgrees()
    {
        var expr = new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid(SeqDagProgram("if(D, 1, 0)")).Root);

        // An async-capable cache is the routing signal for the actual async twin family. The
        // public no-configuration RunFlatAsync overload intentionally takes the synchronous fast
        // path, so using it here would not test the async `if` implementation.
        var result = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedAsync(expr, new PassThroughAsyncZeroArgPropertyResultCache()));
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal([1m], result.Value.Value.ToHostAtoms());
    }

    [Fact]
    public void IfOnSharedDag_OptimizedLoopPlanUsesTheFirstAtomSearch()
    {
        var source = SeqDagProgram("""
            Outer(d) = {
                Step(n) = if(d, n + 1, n)
                Step.repeat(1, 0)
            }
            Outer(D)
            """);
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var diagnostics = new LoopOptimizationDiagnostics();

        var optimized = Evaluator.Run(
            expr,
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true,
            diagnostics);
        if (optimized.IsError)
            Assert.Fail($"Expected optimized success but got error: {optimized.Error}");
        Assert.Equal([1m], optimized.Value.ToHostAtoms());

        var snapshot = diagnostics.GetSnapshot();
        Assert.True(
            snapshot.OptimizedLoopHits == 2,
            $"Unexpected optimizer routing: {snapshot}; reasons={string.Join("; ", snapshot.FallbackReasons)}; " +
            $"plans={string.Join("; ", snapshot.LoopPlans)}");
        // The Wrap loop that builds D deliberately falls back for its capture expression. The
        // Step loop itself is wholly planned; these totals prove it introduced no second fallback.
        Assert.Equal(1, snapshot.PlannedExpressionFallbacks);
        Assert.Equal(1, snapshot.GenericExpressionEvaluationsInsideOptimizedLoops);
        var plan = Assert.Single(snapshot.LoopPlans, candidate => candidate.Identity == "Outer.Step.repeat");
        var output = Assert.Single(
            plan.Expressions,
            expression => expression.Role == "output" && expression.Index == 0);
        Assert.Equal(
            "If(CapturedSlot(d), Add(StateSlot(n), Const(1)), StateSlot(n))",
            output.PlanSummary);

        var generic = Evaluator.Run(
            expr,
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: false);
        if (generic.IsError)
            Assert.Fail($"Expected generic success but got error: {generic.Error}");
        Assert.Equal(generic.Value, optimized.Value, Result.ValueComparer);
    }

    [Fact]
    public void AtomsBuiltinOnAtomlessSharedDag_IsEmptyQuickly()
        // TryLanguageAtoms collects nothing here, so its atom bound never fires: only the
        // atomless-node memo keeps this from re-walking the graph per path.
        => AssertEval(SeqDagProgram("atoms(D).count", leaf: "'s'"), 0);

    [Fact]
    public void AtomsBuiltinOnAtomBearingSharedDag_HitsTheCollectionLimit()
        // 2^40 atoms exceed every collection budget: the pre-existing bounded-traversal abort
        // is preserved, and the walk stays bounded on the way to it.
        => AssertEvalError<EvalError.CollectionSizeLimitExceeded>(SeqDagProgram("atoms(D)"));

    [Fact]
    public void RunFlatOnAtomlessSharedDag_ProjectsNoAtomsQuickly()
    {
        var expr = new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid(SeqDagProgram("D", leaf: "'s'")).Root);

        var flat = Evaluator.RunFlat(expr);
        if (flat.IsError)
            Assert.Fail($"Expected success but got error: {flat.Error}");
        Assert.Empty(flat.Value);

        // The unbounded public host projection over the same value is node-bounded too.
        var counted = Evaluator.RunCounted(expr);
        if (counted.IsError)
            Assert.Fail($"Expected counted success but got error: {counted.Error}");
        Assert.Empty(counted.Value.Value.ToHostAtoms());
    }

    [Fact]
    public void RunFlatOnAtomBearingSharedDag_HitsTheCollectionLimit()
    {
        // Evaluation itself succeeds — the value is a compact DAG — and the bounded host
        // projection reports the same limit error it always did, without path-expanding first.
        var expr = new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid(SeqDagProgram("D")).Root);

        var flat = Evaluator.RunFlat(expr);
        Assert.True(flat.IsError, "Expected the host projection to hit the collection limit.");
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(flat.Error);
    }
}
