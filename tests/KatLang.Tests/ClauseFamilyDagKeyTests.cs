using System.Globalization;
using System.Numerics;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.TestInfrastructure;

namespace KatLang.Tests;

/// <summary>
/// The DAG-LINEAR canonical key of <see cref="PatternMatchEquivalenceIndex"/> (2026-11-10): a head's
/// key is built once per distinct node (reference identity), not once per path, and induces exactly
/// the equality of the former pre-order tree key (<see cref="PatternMatchEquivalenceIndex.TreeCanonicalKey"/>,
/// kept as the oracle) and of <see cref="Pattern.IsMatchEquivalent"/>. The differentials run over
/// the SEC-03 equivalence corpus, generated trees, and generated shared DAGs against their unshared
/// expansions; the depth-n doubling heads (2^n paths) show linear work with the expanded tree's
/// verdict, including repeated-name equivalence under sharing.
/// </summary>
public class ClauseFamilyDagKeyTests
{
    private static Pattern B(string name) => new Pattern.Bind(name);
    private static Pattern I(string text) => new Pattern.LitInt(Decimal128.Parse(text, NumberStyles.Float, CultureInfo.InvariantCulture));
    private static Pattern S(string value) => new Pattern.LitString(value);
    private static Pattern Seq(params Pattern[] items) => new Pattern.SequenceValue(items);
    private static Pattern Lst(params Pattern[] items) => new Pattern.ListValue(items);

    // The unshared tree a head spells out: a fresh node per occurrence.
    private static Pattern Expand(Pattern pattern) => pattern switch
    {
        Pattern.SequenceValue sequence => new Pattern.SequenceValue(sequence.Items.Select(Expand).ToArray()),
        Pattern.ListValue list => new Pattern.ListValue(list.Items.Select(Expand).ToArray()),
        Pattern.Bind bind => new Pattern.Bind(bind.Name),
        Pattern.LitInt literal => new Pattern.LitInt(literal.Value),
        Pattern.LitString literal => new Pattern.LitString(literal.Value),
        Pattern.LitBool literal => new Pattern.LitBool(literal.Value),
        _ => throw new InvalidOperationException(),
    };

    private static string Key(Pattern pattern) => PatternMatchEquivalenceIndex.CanonicalKey(pattern);

    private static string TreeKey(Pattern pattern) => PatternMatchEquivalenceIndex.TreeCanonicalKey(pattern);

    // ── generators ────────────────────────────────────────────────────────────

    private static readonly string[] Names = ["a", "b", "c"];
    private static readonly string[] Numbers = ["0", "-0", "1", "1.0", "2", "NaN"];

    private static Pattern RandomLeaf(Random random) => random.Next(6) switch
    {
        0 or 1 or 2 => B(Names[random.Next(Names.Length)]),
        3 => I(Numbers[random.Next(Numbers.Length)]),
        4 => S(random.Next(2) == 0 ? "x" : "y"),
        _ => new Pattern.LitBool(random.Next(2) == 0),
    };

    private static Pattern RandomTree(Random random, int depth)
    {
        if (depth == 0 || random.Next(3) == 0)
            return RandomLeaf(random);
        var items = new Pattern[random.Next(4)];
        for (var i = 0; i < items.Length; i++)
            items[i] = RandomTree(random, depth - 1);
        return random.Next(3) == 0 ? Lst(items) : Seq(items);
    }

    // A shared DAG: structural nodes pick their items from the pool of earlier nodes, so nodes
    // (including leaves) are referenced along several paths.
    private static Pattern RandomDag(Random random, int nodes)
    {
        var pool = new List<Pattern>();
        for (var i = 0; i < 4; i++)
            pool.Add(RandomLeaf(random));
        for (var i = 0; i < nodes; i++)
        {
            var items = new Pattern[random.Next(4)];
            for (var k = 0; k < items.Length; k++)
                items[k] = random.Next(5) == 0 ? RandomLeaf(random) : pool[pool.Count - 1 - random.Next(Math.Min(pool.Count, 4))];
            pool.Add(random.Next(3) == 0 ? Lst(items) : Seq(items));
        }

        return pool[^1];
    }

    // Level 0 is `bottom`; level k is (level k-1, level k-1) through ONE shared node: n levels
    // spell a tree with 2^n copies of the bottom.
    private static Pattern Doubling(int levels, Pattern bottom)
    {
        var node = bottom;
        // A per-path regression must fail instead of hanging at depth 48/64. Small depths are
        // deliberately expanded by the oracle, so only the intractably large cases need a budget.
        var budget = levels > 12 ? new PatternReadBudget(100_000) : null;
        for (var level = 0; level < levels; level++)
            node = budget is null ? Seq(node, node)
                : new Pattern.SequenceValue(new BudgetedPatternItems<Pattern>(node, node, budget));
        return node;
    }

    private static void AssertKeyLaw(IReadOnlyList<Pattern> patterns)
    {
        var keys = patterns.Select(Key).ToArray();
        var treeKeys = patterns.Select(TreeKey).ToArray();
        for (var i = 0; i < patterns.Count; i++)
        {
            for (var j = 0; j < patterns.Count; j++)
            {
                var dagEqual = string.Equals(keys[i], keys[j], StringComparison.Ordinal);
                var treeEqual = string.Equals(treeKeys[i], treeKeys[j], StringComparison.Ordinal);
                Assert.True(dagEqual == treeEqual, $"{i} vs {j}: DAG key equal={dagEqual}, tree key equal={treeEqual}");
                Assert.True(dagEqual == patterns[i].IsMatchEquivalent(patterns[j]), $"{i} vs {j}: key equality is not match-equivalence");
            }
        }
    }

    // ── 1. differential: trees ────────────────────────────────────────────────

    [Fact]
    public void DagKey_InducesTheTreeKeysEquality_OverTheSec03Corpus()
        => AssertKeyLaw(ClauseFamilyCollisionSecurityTests.EquivalenceCorpus());

    [Fact]
    public void DagKey_InducesTheTreeKeysEquality_OnGeneratedTrees()
    {
        var random = new Random(20261110);
        var patterns = Enumerable.Range(0, 600).Select(_ => RandomTree(random, 3)).ToList();
        AssertKeyLaw(patterns);
        var keys = patterns.Select(Key).ToHashSet(StringComparer.Ordinal);
        Assert.True(keys.Count < patterns.Count - 50, $"only {patterns.Count - keys.Count} equal pairs: the corpus is vacuous");
    }

    [Fact]
    public void TreeHeads_NeverReuseANode()
    {
        var random = new Random(7);
        var observations = new PatternComparisonObservations();
        var index = new PatternMatchEquivalenceIndex(observations);
        for (var i = 0; i < 300; i++)
            index.TryAdd(RandomTree(random, 4));
        Assert.Equal(0, observations.SharedNodeReuseCount);
        Assert.True(observations.CanonicalKeyCount > 0);
    }

    // ── 2. differential: DAGs against their unshared expansions ───────────────

    [Fact]
    public void SharedHeads_HaveExactlyTheKeyOfTheirExpandedTree()
    {
        var random = new Random(11);
        var reused = 0L;
        for (var round = 0; round < 400; round++)
        {
            var dag = RandomDag(random, random.Next(1, 9));
            var tree = Expand(dag);
            Assert.Equal(Key(tree), Key(dag));
            Assert.Equal(TreeKey(tree), TreeKey(dag));

            var observations = new PatternComparisonObservations();
            var index = new PatternMatchEquivalenceIndex(observations);
            index.TryAdd(I("0"));
            index.TryAdd(dag);
            reused += observations.SharedNodeReuseCount;
        }

        Assert.True(reused > 150, $"only {reused} reused nodes: the DAGs barely share");
    }

    [Fact]
    public void SharedFamilies_ReachTheExpandedTreesVerdict_InEveryOrder()
    {
        var random = new Random(5);
        for (var round = 0; round < 60; round++)
        {
            var dags = Enumerable.Range(0, 24).Select(_ => RandomDag(random, random.Next(1, 6))).ToList();
            // Equal-shaped heads under binder renaming and with re-shared subnodes join the family.
            dags.Add(Expand(dags[random.Next(dags.Count)]));
            dags.Add(Seq(dags[random.Next(dags.Count)], dags[random.Next(dags.Count)]));
            var trees = dags.Select(Expand).ToList();
            var dagIndex = new PatternMatchEquivalenceIndex();
            var treeIndex = new PatternMatchEquivalenceIndex();
            for (var k = 0; k < dags.Count; k++)
            {
                var oracle = !trees.Take(k).Any(earlier => earlier.IsMatchEquivalent(trees[k]));
                Assert.Equal(oracle, treeIndex.TryAdd(trees[k]));
                Assert.Equal(oracle, dagIndex.TryAdd(dags[k]));
            }

            var family = new Algorithm.Conditional(Parent: null, Opens: [],
                Branches: dags.Select(head => new CondBranch(head, new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))).ToList());
            var expanded = family with { Branches = family.Branches.Select(branch => branch with { Pattern = Expand(branch.Pattern) }).ToList() };
            Assert.Equal(expanded.HasDuplicateBranchPatterns(), family.HasDuplicateBranchPatterns());
        }
    }

    // ── 3. repeated names under sharing ───────────────────────────────────────

    [Fact]
    public void RepeatedNamesUnderSharing_AreTheExpandedTreesConstraints()
    {
        var shared = Seq(B("x"), B("y"));
        var head = Seq(shared, shared);                                      // (x, y), (x, y)
        Assert.Equal(Key(Seq(Seq(B("p"), B("q")), Seq(B("p"), B("q")))), Key(head));
        Assert.NotEqual(Key(Seq(Seq(B("p"), B("q")), Seq(B("q"), B("p")))), Key(head));
        Assert.NotEqual(Key(Seq(Seq(B("p"), B("q")), Seq(B("r"), B("s")))), Key(head));
        Assert.NotEqual(Key(Seq(Seq(B("p"), B("p")), Seq(B("p"), B("p")))), Key(head));

        // A binder first met inside a shared node keeps that index on every later path.
        var inner = Seq(B("z"), I("1"));
        var mixed = Seq(B("w"), inner, Lst(inner, B("w")));
        Assert.Equal(Key(Expand(mixed)), Key(mixed));
        Assert.Equal(Key(Seq(B("a"), Seq(B("b"), I("1")), Lst(Seq(B("b"), I("1.0")), B("a")))), Key(mixed));
        Assert.NotEqual(Key(Seq(B("a"), Seq(B("b"), I("1")), Lst(Seq(B("a"), I("1")), B("b")))), Key(mixed));
    }

    [Fact]
    public void PrefixAndEmptyBinderNames_KeepTheTreeOraclesBijection()
    {
        string[] names = ["abc", "a", "ab", "", "\0", "\0x", "\uffff", "\uffff\0", new string('p', 20_000)];
        var patterns = new List<Pattern>();
        foreach (var order in new[] { names, names.Reverse().ToArray(), names.Order(StringComparer.Ordinal).ToArray() })
        {
            patterns.Add(Seq(order.Concat(order.Reverse()).Select(B).ToArray()));
            // Same constraints, including a terminal that prefixes a later key and vice versa.
            patterns.Add(Seq(Enumerable.Range(0, order.Length).Concat(Enumerable.Range(0, order.Length).Reverse())
                .Select(i => B($"renamed{i}")).ToArray()));
            patterns.Add(Seq(order.Concat(order).Select(B).ToArray()));
        }
        AssertKeyLaw(patterns);
    }

    [Fact]
    public void ManyDistinctBindersAndDefinitions_HaveLinearKeyConstructionWork()
    {
        static PatternComparisonObservations At(int count)
        {
            var leaves = Enumerable.Range(0, count).Select(i => B(new string('p', 64) + i.ToString("D6", CultureInfo.InvariantCulture))).ToArray();
            var head = Doubling(20, Seq(leaves.Concat(leaves.Reverse()).ToArray()));
            var observations = ObserveFamily(I("0"), head);
            var inputUnits = observations.DefinitionWriteUnits + observations.BinderNameUnits;
            Assert.True(observations.DefinitionComparisonUnits + observations.BinderComparisonUnits < 64 * inputUnits);
            Assert.Equal(20 + count, observations.SharedNodeReuseCount);
            return observations;
        }

        var at512 = At(512);
        var at1024 = At(1024);
        var at2048 = At(2048);
        Assert.True(at1024.TotalIndexWork < 2.3 * at512.TotalIndexWork, $"{at512.TotalIndexWork} -> {at1024.TotalIndexWork}");
        Assert.True(at2048.TotalIndexWork < 2.3 * at1024.TotalIndexWork, $"{at1024.TotalIndexWork} -> {at2048.TotalIndexWork}");
    }

    // ── 4. depth-n shared heads: linear work, the expanded tree's verdict ────

    private static PatternComparisonObservations ObserveFamily(params Pattern[] heads)
    {
        var observations = new PatternComparisonObservations();
        var index = new PatternMatchEquivalenceIndex(observations);
        foreach (var head in heads)
            index.TryAdd(head);
        return observations;
    }

    [Theory]
    [InlineData(1)]
    [InlineData(6)]
    [InlineData(12)]
    public void DoublingHeads_AtSmallDepth_DecideLikeTheirExpandedTrees(int levels)
    {
        Pattern[] Family(Func<Pattern, Pattern> shape) =>
        [
            shape(Doubling(levels, Seq(B("x"), B("y")))),
            shape(Doubling(levels, Seq(B("y"), B("x")))),   // a renaming of the first: duplicate
            shape(Doubling(levels, Seq(B("x"), B("x")))),   // repeated name: distinct
            shape(Doubling(levels, Seq(B("x"), I("1")))),
        ];

        var dags = Family(static head => head);
        var trees = dags.Select(Expand).ToArray();
        for (var i = 0; i < dags.Length; i++)
        {
            Assert.Equal(Key(trees[i]), Key(dags[i]));
            Assert.Equal(TreeKey(trees[i]), TreeKey(dags[i]));
        }

        Assert.Equal(new[] { true, false, true, true }, Verdicts(dags));
        Assert.Equal(new[] { true, false, true, true }, Verdicts(trees));
        // The renamed heads stay one class even when a different object shares the bottom.
        Assert.Equal(Key(dags[0]), Key(Expand(dags[1])));
    }

    private static bool[] Verdicts(IEnumerable<Pattern> heads)
    {
        var index = new PatternMatchEquivalenceIndex();
        return heads.Select(head => index.TryAdd(head)).ToArray();
    }

    [Fact]
    public void DoublingHeads_AtDepth64_AreDecidedWithLinearWork()
    {
        // 2^64 paths per head: any per-path walk would never finish.
        static PatternComparisonObservations At(int levels)
        {
            var observations = ObserveFamily(
                Doubling(levels, Seq(B("x"), B("y"))),
                Doubling(levels, Seq(B("x"), B("x"))),
                Doubling(levels, Seq(B("p"), B("q"))));
            Assert.Equal(3, observations.CanonicalKeyCount);
            return observations;
        }

        var verdicts = new PatternMatchEquivalenceIndex();
        Assert.True(verdicts.TryAdd(Doubling(64, Seq(B("x"), B("y")))));
        Assert.True(verdicts.TryAdd(Doubling(64, Seq(B("x"), B("x")))));
        Assert.False(verdicts.TryAdd(Doubling(64, Seq(B("p"), B("q")))));
        Assert.True(verdicts.TryAdd(Doubling(63, Seq(B("p"), B("q")))));

        var at16 = At(16);
        var at32 = At(32);
        var at64 = At(64);
        // Every level adds one node, one visit to it and one reuse of its shared item, per head.
        Assert.Equal(3 * 64L, at64.SharedNodeReuseCount);
        Assert.Equal(at64.TraversalUnits - at32.TraversalUnits, 2 * (at32.TraversalUnits - at16.TraversalUnits));
        var growth = (double)at64.TotalIndexWork / at32.TotalIndexWork;
        Assert.True(growth < 2.5, $"index work grew {growth:F2}x when the depth doubled ({at32.TotalIndexWork} -> {at64.TotalIndexWork})");
        Assert.True(at64.TotalIndexWork < 64 * 3 * 200, $"{at64.TotalIndexWork} work units for 3 heads of 64 levels");
    }

    [Fact]
    public void WideSharedLiteral_IsCopiedOnce_NotPerPath()
    {
        // One 10,000-unit string under 2^20 paths contributes its text to the key once.
        var literal = S(new string('q', 10_000));
        var head = Doubling(20, Seq(literal, B("x")));
        var observations = ObserveFamily(I("0"), head);
        Assert.InRange(observations.CanonicalKeyUnits, 10_000, 12_000);
        Assert.Equal(Key(Doubling(20, Seq(S(new string('q', 10_000)), B("y")))), Key(head));
    }

    [Fact]
    public void SeparateEqualLeaves_CountTheirWritesBeforeDefinitionsAreRetracted()
    {
        var text = new string('q', 10_000);
        var head = Seq(Enumerable.Range(0, 64).Select(_ => S(text)).ToArray());
        var observations = ObserveFamily(I("0"), head);
        Assert.InRange(observations.CanonicalKeyUnits, text.Length, 2 * text.Length);
        Assert.True(observations.DefinitionWriteUnits >= 64L * text.Length);
        Assert.Equal(observations.CanonicalKeyUnits, observations.KeyCopyUnits);
        Assert.Equal(0, observations.SharedNodeReuseCount);
    }

    [Fact]
    public void PublicGuard_OnDepth48SharedHeads_IsTheExpandedTreesVerdict()
    {
        static CondBranch Branch(Pattern head) => new(head, new Algorithm.User(null, [], [], [], [new Expr.Num(1)]));

        var duplicate = new Algorithm.Conditional(Parent: null, Opens: [], Branches:
            [Branch(Doubling(48, Seq(B("x"), I("1")))), Branch(Doubling(48, Seq(B("y"), I("1.0"))))]);
        Assert.True(duplicate.HasDuplicateBranchPatterns());

        var distinct = new Algorithm.Conditional(Parent: null, Opens: [], Branches:
            [Branch(Doubling(48, Seq(B("x"), I("1")))), Branch(Doubling(47, Seq(B("y"), I("1"))))]);
        Assert.False(distinct.HasDuplicateBranchPatterns());
    }

    [Theory]
    [InlineData("generic")]
    [InlineData("optimized")]
    [InlineData("async")]
    public async Task FirstFamilyCall_OnDepth48SharedDuplicateHeads_IsRejectedWithLinearGuardWork(string route)
    {
        // 2^48 paths per head: the run reaches the duplicate verdict only if the guard (and every
        // consumer before it) is linear in the distinct head nodes.
        static async Task<(EvalError? Error, long Work)> Run(string route, int levels)
        {
            static CondBranch Branch(Pattern head, int value) => new(head, new Algorithm.User(null, [], [], [], [new Expr.Num(value)]));
            var family = new Algorithm.Conditional(Parent: null, Opens: [], Branches:
                [Branch(Doubling(levels, Seq(B("x"), I("1"))), 1), Branch(Doubling(levels, Seq(B("y"), I("1.0"))), 2)]);
            var root = new Algorithm.User(null, [], [], [new Property("F", family, IsPublic: true)],
                [new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Num(1)]))]);
            var index = new PatternComparisonObservations();
            var observations = new EvaluationObservations { FamilyDuplicateIndex = index };
            var expr = new Expr.AlgorithmExpr(root);
            var (result, _) = route == "async"
                ? await Evaluator.RunCountedObservedAsync(expr, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), observations: observations)
                : Evaluator.RunCountedObserved(expr, enableOptimizations: route == "optimized", observations: observations);
            var error = result.IsError ? result.Error : null;
            while (error is EvalError.WithContext context)
                error = context.Inner;
            return (error, index.TotalIndexWork);
        }

        var (at24, work24) = await Run(route, 24);
        var (at48, work48) = await Run(route, 48);
        Assert.IsType<EvalError.DuplicateBranchPattern>(at24);
        Assert.IsType<EvalError.DuplicateBranchPattern>(at48);
        Assert.True(work48 < 2.5 * work24, $"{route}: guard work {work24} -> {work48} when the depth doubled");
    }

    [Fact]
    public void CancellationInsideASharedHead_StopsAtThatCheckpoint()
    {
        using var source = new CancellationTokenSource();
        var observations = new PatternComparisonObservations
        {
            CheckpointReached = count =>
            {
                if (count == 4)
                    source.Cancel();
            },
        };
        var index = new PatternMatchEquivalenceIndex(observations);
        Assert.True(index.TryAdd(I("0"), source.Token));
        // Wide shared items: many visits, so the walk passes several checkpoints.
        var wide = Seq(Enumerable.Range(0, 20_000).Select(i => I(i.ToString(CultureInfo.InvariantCulture))).ToArray());
        var exception = Assert.ThrowsAny<OperationCanceledException>(() => index.TryAdd(Seq(wide, wide), source.Token));
        Assert.Equal(source.Token, exception.CancellationToken);
        Assert.Equal(4, observations.CancellationCheckpointCount);
        Assert.Equal(1, observations.CanonicalKeyCount);
    }

    [Fact]
    public void TextBufferGrowth_IsCountedAndCancellableInBoundedBlocks()
    {
        using var source = new CancellationTokenSource();
        const int interval = PatternMatchEquivalenceIndex.CanonicalizationCheckpointInterval;
        var previousCopyUnits = 0L;
        PatternComparisonObservations observations = null!;
        observations = new PatternComparisonObservations
        {
            CheckpointReached = _ =>
            {
                Assert.InRange(observations.BufferCopyUnits - previousCopyUnits, 0, 2L * interval);
                previousCopyUnits = observations.BufferCopyUnits;
                if (observations.BufferCopyUnits >= 8L * interval)
                    source.Cancel();
            },
        };
        var index = new PatternMatchEquivalenceIndex(observations);
        Assert.True(index.TryAdd(I("0"), source.Token));
        var head = Doubling(20, S(new string('q', 256_000)));
        var exception = Assert.ThrowsAny<OperationCanceledException>(() => index.TryAdd(head, source.Token));
        Assert.Equal(source.Token, exception.CancellationToken);
        Assert.InRange(observations.BufferCopyUnits, 8L * interval, 10L * interval);
        Assert.Equal(1, observations.CanonicalKeyCount);
    }
}
