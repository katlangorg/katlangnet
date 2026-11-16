using System.Numerics;
using KatLang.Evaluation;
using KatLang.TestInfrastructure;
namespace KatLang.Tests;

/// <summary>
/// The host-facing, context-free <see cref="Result.ValueComparer"/> decides structural equality with
/// reference classes too (<see cref="ReferenceClasses"/>, union–find, one per call), like the
/// evaluator's walks (<c>SharedValueGraphComplexityTests.ReferenceClasses.cs</c>). Its exact-pair memo
/// reached about m² pairs per level of the shift-register witness: at m = 512, depth 40 one
/// comparison expanded 8,388,097 pairs and allocated about 630 MB (Release, measured before the
/// change). Every verdict and every hash stays exactly what it was.
///
/// <para>The shared static comparer carries no observer, so the expansion counts below come from
/// <see cref="Result.CreateObservedValueComparer"/>: the same <see cref="Result.ValueSemanticComparer"/>
/// and the same per-call walk, with a passive counter. Verdicts and the allocation bound go through
/// <see cref="Result.ValueComparer"/> itself.</para>
/// </summary>
public partial class SharedValueGraphComplexityTests
{
    /// <summary>Structure nodes of both witness sides together: nodesA + nodesB.</summary>
    private static long WitnessNodes => 2 * RegisterNodes(WitnessWidth, WitnessDepth);

    [Fact]
    public void HostComparer_TheObservedComparer_RunsTheSharedComparersWalk()
    {
        // The counts below are only evidence for Result.ValueComparer if both are the same walk.
        Assert.Same(Result.ValueComparer, Result.CreateObservedValueComparer(observations: null));
        Assert.IsType<Result.ValueSemanticComparer>(Result.ValueComparer);
        Assert.IsType<Result.ValueSemanticComparer>(Result.CreateObservedValueComparer(new ValueTraversalObservations()));
    }

    [Theory]
    [MemberData(nameof(WitnessShapes))]
    public void HostComparer_OneComparison_IsLinearInTheDistinctNodes(string shape)
    {
        var (left, right) = Witness(shape);
        Assert.True(Result.ValueComparer.Equals(left, right));
        Assert.True(Result.ValueComparer.Equals(right, left));

        var (comparer, observations) = Observed();
        Assert.True(comparer.Equals(left, right));
        var expansions = observations.EqualityPairExpansionCount;
        Assert.InRange(expansions, 1, WitnessExpansionBound);
        // Sharper: every expansion below the top level unites two classes, and the nodes recorded are
        // at most both sides' nested structure nodes, so the walk expands at most nodesA + nodesB pairs.
        Assert.InRange(expansions, 1, WitnessNodes);
        if (shape == "isomorphic")
        {
            // Node-to-node correspondence: the root plus one pair per level node, exactly as before.
            Assert.Equal(1L + (long)WitnessWidth * WitnessDepth, expansions);
        }

        // Hashing was already linear (one memoized hash per distinct node) and is unchanged.
        var (hasher, hashing) = Observed();
        Assert.Equal(hasher.GetHashCode(left), hasher.GetHashCode(right));
        Assert.Equal(WitnessNodes, hashing.HashStructureExpansionCount);
        Assert.Equal(Result.ValueComparer.GetHashCode(left), Result.ValueComparer.GetHashCode(right));
    }

    /// <summary>
    /// A faithful model of the context-free walk BEFORE reference classes: the same order, early
    /// mismatches and recording point (a nested non-empty pair when descended into; the top-level pair
    /// never), but skipping only an EXACT expanded ordered reference pair. Returns its verdict and its
    /// expanded pairs.
    /// </summary>
    private static (bool Equal, long Expansions) ExactPairContextFreeWalk(Result left, Result right)
    {
        if (ReferenceEquals(left, right))
            return (true, 0);
        if (!SameKindAndCount(left, right, out var leftItems, out var rightItems))
            return (LeafEquals(left, right), 0);

        var expanded = new HashSet<(Result, Result)>(PairIdentity.Instance);
        var frames = new Stack<(IReadOnlyList<Result> Left, IReadOnlyList<Result> Right, int Next)>();
        var (next, expansions) = (0, 1L);
        while (true)
        {
            if (next >= leftItems.Count)
            {
                if (frames.Count == 0)
                    return (true, expansions);
                (leftItems, rightItems, next) = frames.Pop();
                continue;
            }

            var (childLeft, childRight) = (leftItems[next], rightItems[next]);
            next++;
            if (ReferenceEquals(childLeft, childRight))
                continue;
            if (!SameKindAndCount(childLeft, childRight, out var childLeftItems, out var childRightItems))
            {
                if (!LeafEquals(childLeft, childRight))
                    return (false, expansions);
                continue;
            }

            if (childLeftItems.Count == 0 || !expanded.Add((childLeft, childRight)))
                continue;
            expansions++;
            if (next < leftItems.Count)
                frames.Push((leftItems, rightItems, next));
            (leftItems, rightItems, next) = (childLeftItems, childRightItems, 0);
        }

        static bool SameKindAndCount(Result x, Result y, out IReadOnlyList<Result> xItems, out IReadOnlyList<Result> yItems)
        {
            (xItems, yItems) = (ItemsOf(x), ItemsOf(y));
            return ((x is Result.ListValue && y is Result.ListValue) || (x is Result.SequenceValue && y is Result.SequenceValue))
                && xItems.Count == yItems.Count;
        }

        // Every pair that is not two structures of one kind and count: leaves by value, else unequal.
        static bool LeafEquals(Result x, Result y)
            => x is not (Result.ListValue or Result.SequenceValue) && NaiveEquals(x, y);
    }

    [Fact]
    public void HostComparer_IsomorphicSharing_KeepsTheExactPairWalksCounts()
    {
        // Node to node correspondence: each class is one expanded pair, so the walk is exactly the
        // exact-pair walk, expansion for expansion.
        var (left, right) = Witness("isomorphic");
        var (comparer, observations) = Observed();
        Assert.True(comparer.Equals(left, right));
        var exact = ExactPairContextFreeWalk(left, right);
        Assert.True(exact.Equal);
        Assert.Equal(exact.Expansions, observations.EqualityPairExpansionCount);

        // On the differently shared pair the model is the m² blow-up (checked where it stays cheap).
        var (smallLeft, smallRight) = (Register(64, 12, ShiftRegister), Register(64, 12, Mixing));
        var (smallComparer, small) = Observed();
        Assert.True(smallComparer.Equals(smallLeft, smallRight));
        var smallExact = ExactPairContextFreeWalk(smallLeft, smallRight);
        Assert.True(smallExact.Equal);
        Assert.InRange(small.EqualityPairExpansionCount, 1, 2 * RegisterNodes(64, 12));
        Assert.True(smallExact.Expansions > 4 * small.EqualityPairExpansionCount, $"{smallExact.Expansions} vs {small.EqualityPairExpansionCount}");
    }

    [Theory]
    [MemberData(nameof(WitnessShapes))]
    public void HostComparer_OneDeepLeafMismatch_IsUnequal(string shape)
    {
        // One deepest leaf differs on one side. In the LATE variant only the root's last child reaches
        // the different leaf, through fresh nodes, so the walk meets it after every other level has
        // merged into its classes: no class may answer that pair early.
        var (left, right) = Witness(shape, mismatchAt: WitnessWidth - 1);
        var (_, correct) = Witness(shape);
        var (_, wrong) = Witness(shape, mismatchAt: 0);
        var late = List([.. ItemsOf(correct).Take(WitnessWidth - 1), ItemsOf(wrong)[WitnessWidth - 1]]);
        var budget = EvaluationBudget.Create(limits: null);
        foreach (var (x, y) in new[] { (left, right), (right, left), (left, late), (late, left) })
        {
            Assert.False(Result.ValueComparer.Equals(x, y));
            var (comparer, observations) = Observed();
            Assert.False(comparer.Equals(x, y));
            Assert.InRange(observations.EqualityPairExpansionCount, 1, WitnessExpansionBound);
            // The late root reaches nodes of two fresh sides, so the sharp bound counts them directly.
            Assert.InRange(observations.EqualityPairExpansionCount, 1, DistinctStructureNodes(x, y));
            var evaluator = Result.EvaluatorValueEquals(x, y, budget, observations: null);
            Assert.False(evaluator.IsError);
            Assert.False(evaluator.Value);
        }

        // The control: a fresh root over the correct side's children is equal again.
        Assert.True(Result.ValueComparer.Equals(left, List([.. ItemsOf(correct)])));
    }

    [Fact]
    public void HostComparer_AFalseComparison_LeavesNothingForTheNextCall()
    {
        // (p, q) is united when the walk descends into it, then its last leaf differs. The classes
        // die with the call: a later comparison on the SAME shared comparer must not skip (p, q).
        var shared = List(Atom(1), Atom(2));
        var p0 = List(shared, shared);
        var q0 = List(List(Atom(1), Atom(2)), List(Atom(1), Atom(2)));
        var p = List(p0, Atom(1));
        var q = List(q0, Atom(2));

        Assert.False(Result.ValueComparer.Equals(List(p), List(q)));
        Assert.False(Result.ValueComparer.Equals(List(p, Atom(0)), List(q, Atom(0))));
        Assert.False(Result.ValueComparer.Equals(List(Atom(0), p), List(Atom(0), q)));
        Assert.False(Result.ValueComparer.Equals(p, q));
        Assert.True(Result.ValueComparer.Equals(p0, q0));
        Assert.True(Result.ValueComparer.Equals(q0, p0));

        // Per call: each repetition costs exactly what the first one did (nothing was retained). The
        // root, (p, q), (p0, q0), (shared, q0[0]), then (shared, q0[1]): q0[1] is a fresh reference,
        // so it shares no class with shared yet, and the walk descends before the mismatch at p[1].
        var (comparer, observations) = Observed();
        Assert.False(comparer.Equals(List(p), List(q)));
        Assert.Equal(5, observations.EqualityPairExpansionCount);
        Assert.False(comparer.Equals(List(p), List(q)));
        Assert.Equal(10, observations.EqualityPairExpansionCount);
    }

    [Fact]
    public void HostComparer_ConcurrentComparisons_ShareNoState()
    {
        // The comparer is one static instance: every call owns its classes, so concurrent equal and
        // unequal comparisons of the witness never see each other's unions.
        var (left, right) = Witness("differently-shared");
        var (_, unequal) = Witness("differently-shared", mismatchAt: WitnessWidth - 1);
        var (isoLeft, isoRight) = Witness("isomorphic");
        var verdicts = new bool[32];
        Parallel.For(0, verdicts.Length, new ParallelOptions { MaxDegreeOfParallelism = 8 }, i =>
            verdicts[i] = (i % 4) switch
            {
                0 => Result.ValueComparer.Equals(left, right),
                1 => Result.ValueComparer.Equals(left, unequal),
                2 => Result.ValueComparer.Equals(isoRight, isoLeft),
                _ => Result.ValueComparer.Equals(unequal, right),
            });
        for (var i = 0; i < verdicts.Length; i++)
            Assert.True(verdicts[i] == (i % 4 is 0 or 2), $"comparison {i}");
    }

    // ── Randomized differential: the old walk, the naive definition and the evaluator walk ───────

    /// <summary>The distinct non-empty structure nodes reachable from either value, by reference.</summary>
    private static int DistinctStructureNodes(Result left, Result right)
    {
        var seen = new HashSet<Result>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<Result>([left, right]);
        while (pending.TryPop(out var node))
        {
            var items = ItemsOf(node);
            if (items.Count == 0 || !seen.Add(node))
                continue;
            foreach (var item in items)
                pending.Push(item);
        }

        return seen.Count;
    }

    /// <summary>
    /// A <see cref="Register"/> side over special leaves: every deepest node is a fresh
    /// <c>[NaN, ±0]</c> (the sign of zero drawn at random, so equal nodes differ in their objects and
    /// their zero's sign), and <paramref name="mismatchAt"/> makes that one <c>[NaN, 1]</c> instead.
    /// </summary>
    private static Result SpecialRegister(int width, int depth, int multiplier, int mismatchAt, Random random)
    {
        var level = new Result[width];
        for (var j = 0; j < width; j++)
        {
            var second = j == mismatchAt
                ? Atom(1)
                : new Result.Atom(random.Next(2) == 0 ? Decimal128.Zero : Decimal128.NegativeZero);
            level[j] = List(new Result.Atom(Decimal128.NaN), second);
        }

        for (var k = 1; k < depth; k++)
        {
            var above = new Result[width];
            for (var j = 0; j < width; j++)
                above[j] = List(level[multiplier * j % width], level[(multiplier * j + 1) % width]);
            level = above;
        }

        return List(level);
    }

    [Fact]
    public void HostComparer_RandomizedDifferential_AgreesWithTheOldWalk_TheNaiveComparison_AndTheEvaluatorWalk()
    {
        long comparisons = 0, equalVerdicts = 0, equalDistinctObjects = 0, deepEqual = 0, deepUnequal = 0, fewerExpansions = 0;
        for (var seed = 101; seed <= 140; seed++)
        {
            // Phase 1: small random DAGs with re-sharing and the special atoms (NaN twice, ±0,
            // 1 / 1.0 / 1.00, Booleans, long strings), plus equal copies of the deepest nodes shared
            // differently and near misses (one change, then re-shared).
            var values = new DifferentialValues(seed);
            for (var i = 0; i < 30; i++)
                _ = values.Grow();
            var candidates = new List<Result>(values.Pool);
            foreach (var source in values.Pool.OrderByDescending(DepthOf).Take(6).ToArray())
            {
                for (var copy = 0; copy < 4; copy++)
                    candidates.Add(values.Reshare(source));
                for (var miss = 0; miss < 2; miss++)
                    candidates.Add(values.Reshare(values.Mutate(source)));
            }

            CompareEveryOrderedPair(seed, candidates);
            AssertHashedCollectionsKeepTheNaiveClasses(candidates);

            // Phase 2: one width and depth per seed and every multiplier — each spells the same tree,
            // shared differently — with random deepest-leaf mismatches, and roots spliced from the
            // top levels of several variants: deep pairs whose classes merge across levels.
            var random = new Random(seed * 7919);
            var (width, depth) = (random.Next(3, 17), random.Next(2, 8));
            var registers = new List<Result>();
            foreach (var multiplier in new[] { 1, 2, 3, 5, 7 })
            {
                registers.Add(SpecialRegister(width, depth, multiplier, mismatchAt: -1, random));
                registers.Add(SpecialRegister(width, depth, multiplier, random.Next(width), random));
            }

            for (var splice = 0; splice < 4; splice++)
                registers.Add(List([.. Enumerable.Range(0, width).Select(k => ItemsOf(registers[random.Next(registers.Count)])[k])]));

            CompareEveryOrderedPair(seed, registers);
            AssertHashedCollectionsKeepTheNaiveClasses(registers);
        }

        // Both verdicts substantially, equal distinct objects, deep values both ways, and comparisons
        // whose classes saved expansions the exact-pair walk made (seeds 101–140 reach about 1.6–1.7
        // times each floor).
        Assert.True(equalVerdicts >= comparisons / 20, $"{equalVerdicts} equal of {comparisons}");
        Assert.True(equalVerdicts <= comparisons - comparisons / 20, $"{equalVerdicts} equal of {comparisons}");
        Assert.True(equalDistinctObjects >= comparisons / 50, $"{equalDistinctObjects} of {comparisons}");
        Assert.True(deepEqual >= 2_500, $"deep equal comparisons: {deepEqual}");
        Assert.True(deepUnequal >= 40_000, $"deep unequal comparisons: {deepUnequal}");
        Assert.True(fewerExpansions >= 1_000, $"comparisons with fewer expansions than the exact-pair walk: {fewerExpansions}");

        void CompareEveryOrderedPair(int seed, List<Result> candidates)
        {
            var budget = EvaluationBudget.Create(limits: null);
            var depths = candidates.Select(DepthOf).ToArray();
            var (comparer, observations) = Observed();
            for (var i = 0; i < candidates.Count; i++)
            {
                for (var j = 0; j < candidates.Count; j++)
                {
                    var (left, right) = (candidates[i], candidates[j]);
                    var expected = NaiveEquals(left, right);
                    var old = ExactPairContextFreeWalk(left, right);
                    Assert.True(expected == old.Equal, $"seed {seed}: the model of the old walk decided {old.Equal} for {i} and {j}");

                    var before = observations.EqualityPairExpansionCount;
                    Assert.True(expected == Result.ValueComparer.Equals(left, right), $"seed {seed}: ValueComparer of {i} and {j}");
                    Assert.True(expected == comparer.Equals(left, right), $"seed {seed}: observed comparer of {i} and {j}");
                    var expansions = observations.EqualityPairExpansionCount - before;
                    Assert.InRange(expansions, 0, Math.Max(1, DistinctStructureNodes(left, right)));
                    if (expansions < old.Expansions)
                        fewerExpansions++;

                    var evaluator = Result.EvaluatorValueEquals(left, right, budget, observations: null);
                    Assert.False(evaluator.IsError);
                    Assert.True(expected == evaluator.Value, $"seed {seed}: the evaluator walk of {i} and {j}");
                    if (expected)
                        Assert.Equal(Result.ValueComparer.GetHashCode(left), Result.ValueComparer.GetHashCode(right));

                    comparisons++;
                    if (expected)
                        equalVerdicts++;
                    if (expected && !ReferenceEquals(left, right))
                        equalDistinctObjects++;
                    if (!ReferenceEquals(left, right) && depths[i] >= 3)
                    {
                        if (expected)
                            deepEqual++;
                        else
                            deepUnequal++;
                    }
                }
            }
        }

        // Hashed host collections keyed by the comparer keep exactly the naive classes.
        static void AssertHashedCollectionsKeepTheNaiveClasses(List<Result> candidates)
        {
            var set = new HashSet<Result>(Result.ValueComparer);
            var naiveKept = new List<Result>();
            var firstIndex = new Dictionary<Result, int>(Result.ValueComparer);
            for (var i = 0; i < candidates.Count; i++)
            {
                var item = candidates[i];
                var isNew = !naiveKept.Any(earlier => NaiveEquals(earlier, item));
                if (isNew)
                    naiveKept.Add(item);
                Assert.Equal(isNew, set.Add(item));
                Assert.Equal(isNew, firstIndex.TryAdd(item, i));
                Assert.True(NaiveEquals(candidates[firstIndex[item]], item));
            }

            Assert.Equal(naiveKept.Count, set.Count);
        }
    }

    // ── Memory: one host comparison of the m = 512 differently shared pair ───────────────────────

    [Fact]
    public void HostComparer_OneComparison_OfTheDifferentlySharedPair_AllocatesUnderEightMegabytes_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        // Warm up the walk and the memo types on a small pair of the same shapes.
        Assert.True(Result.ValueComparer.Equals(Register(16, 4, ShiftRegister), Register(16, 4, Mixing)));
        var (left, right) = Witness("differently-shared");

        var before = GC.GetAllocatedBytesForCurrentThread();
        var equal = Result.ValueComparer.Equals(left, right);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.True(equal);
        // The exact-pair memo allocated about 630 MB here (Release, before the change).
        Assert.InRange(allocated, 0, 8L * 1024 * 1024);
        GcIsolatedAllocation.Complete();
    }
}
