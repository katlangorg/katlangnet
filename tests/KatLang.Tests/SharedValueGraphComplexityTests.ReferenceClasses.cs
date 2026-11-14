using System.Numerics;
using KatLang.Evaluation;
using KatLang.TestInfrastructure;
namespace KatLang.Tests;

/// <summary>
/// Reference classes (audit §1.9): the evaluator's equality walks decide by equivalence classes of
/// references (<see cref="ReferenceClasses"/>, union–find), not by exact reference pairs. Two equal
/// values whose sharing does not correspond node to node then cost O(|A| + |B|): the exact-pair memo
/// reached about m² pairs per level of the witness below, so one <c>==</c> at m = 1,024 took
/// 23–35 s and over 1 GB. Every verdict stays exactly the context-free <see cref="Result.ValueComparer"/>'s
/// and a naive unfolded-tree comparison's (the randomized differential below).
/// </summary>
public partial class SharedValueGraphComplexityTests
{
    private const int WitnessWidth = 512;

    private const int WitnessDepth = 40;

    /// <summary>The shift register: node j's children are (2j, 2j + 1) mod m.</summary>
    private const int ShiftRegister = 2;

    /// <summary>The mixing side: node j's children are (3j, 3j + 1) mod m, which mixes the whole path.</summary>
    private const int Mixing = 3;

    /// <summary>
    /// One side of the witness: <paramref name="depth"/> levels of <paramref name="width"/> list nodes
    /// under a root listing the top level. Node j of a level has the children
    /// (multiplier·j, multiplier·j + 1) mod width on the level below, and every deepest node is
    /// <c>[1, 1]</c>, so all nodes of one level are equal values and every multiplier spells the
    /// same tree. <paramref name="mismatchAt"/> makes that one deepest node <c>[1, 2]</c> instead.
    /// Every call builds fresh objects.
    /// </summary>
    private static Result Register(int width, int depth, int multiplier, int mismatchAt = -1)
    {
        var level = new Result[width];
        for (var j = 0; j < width; j++)
            level[j] = List(Atom(1), Atom(j == mismatchAt ? 2 : 1));
        for (var k = 1; k < depth; k++)
        {
            var above = new Result[width];
            for (var j = 0; j < width; j++)
                above[j] = List(level[multiplier * j % width], level[(multiplier * j + 1) % width]);
            level = above;
        }

        return List(level);
    }

    /// <summary>Structure nodes of one <see cref="Register"/> side: the levels and the root.</summary>
    private static long RegisterNodes(int width, int depth) => 1L + (long)width * depth;

    /// <summary>Child slots of one <see cref="Register"/> side: the root's, then two per level node.</summary>
    private static long RegisterSlots(int width, int depth) => width + 2L * width * depth;

    /// <summary>The bound on expanded pairs of one comparison of two sides: 2·(nodesA + nodesB).</summary>
    private static long WitnessExpansionBound => 2 * 2 * RegisterNodes(WitnessWidth, WitnessDepth);

    /// <summary>The bound on structural units of one comparison: 4·(slotsA + slotsB).</summary>
    private static long WitnessUnitBound => 4 * 2 * RegisterSlots(WitnessWidth, WitnessDepth);

    public static TheoryData<string> WitnessShapes => ["differently-shared", "isomorphic"];

    private static (Result Left, Result Right) Witness(string shape, int mismatchAt = -1) => shape switch
    {
        "differently-shared" => (Register(WitnessWidth, WitnessDepth, ShiftRegister),
            Register(WitnessWidth, WitnessDepth, Mixing, mismatchAt)),
        "isomorphic" => (Register(WitnessWidth, WitnessDepth, ShiftRegister),
            Register(WitnessWidth, WitnessDepth, ShiftRegister, mismatchAt)),
        _ => throw new ArgumentOutOfRangeException(nameof(shape)),
    };

    [Theory]
    [MemberData(nameof(WitnessShapes))]
    public void ReferenceClasses_OneComparison_IsLinearInTheDistinctNodes(string shape)
    {
        var (left, right) = Witness(shape);
        // == / != through ApplyComparison's decision (Result.EvaluatorValueEquals: the single walk),
        // and one comparison of an operation comparer (contains/distinct/repeated names).
        var single = ObserveWalk(left, right, single: true);
        var operation = ObserveWalk(left, right, single: false);
        Assert.True(single.Equal);
        Assert.True(operation.Equal);

        // The exact-pair memo expanded about m²·d/2 = 5.2 million pairs on the differently shared pair.
        Assert.InRange(single.Expansions, 1, WitnessExpansionBound);
        Assert.InRange(single.Units, 1, WitnessUnitBound);
        // Both walks make the same class decisions in the same order: the same work and checkpoints.
        Assert.Equal(single.Expansions, operation.Expansions);
        Assert.Equal(single.Units, operation.Units);
        Assert.Equal(single.Boundaries, operation.Boundaries);
    }

    private sealed class PairIdentity : IEqualityComparer<(Result Left, Result Right)>
    {
        public static readonly PairIdentity Instance = new();

        public bool Equals((Result Left, Result Right) x, (Result Left, Result Right) y)
            => ReferenceEquals(x.Left, y.Left) && ReferenceEquals(x.Right, y.Right);

        public int GetHashCode((Result Left, Result Right) pair)
            => HashCode.Combine(
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(pair.Left),
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(pair.Right));
    }

    private static IReadOnlyList<Result> ItemsOf(Result value) => value switch
    {
        Result.ListValue(var items) => items,
        Result.SequenceValue(var items) => items,
        _ => [],
    };

    /// <summary>
    /// A model of the single-comparison walk BEFORE reference classes, for two EQUAL values: the same
    /// recording points (seeded at first descent, entered when at least RetainedWidth wide, top-level
    /// never), but skipping only an EXACT recorded reference pair. Returns its expanded pairs and units
    /// (each expanded pair inspects every child and completes once).
    /// </summary>
    private static (long Expansions, long Units) ExactPairWalkOfEqualValues(Result left, Result right)
    {
        var recorded = new HashSet<(Result, Result)>(PairIdentity.Instance);
        var frames = new Stack<(Result LeftNode, Result RightNode, IReadOnlyList<Result> Left, IReadOnlyList<Result> Right, int Next)>();
        var (leftNode, rightNode, leftItems, rightItems, next, settled) = (left, right, ItemsOf(left), ItemsOf(right), 0, true);
        var (expansions, units) = (1L, ItemsOf(left).Count + 1L);
        while (true)
        {
            if (next >= leftItems.Count)
            {
                if (frames.Count == 0)
                    return (expansions, units);
                (leftNode, rightNode, leftItems, rightItems, next) = frames.Pop();
                settled = true;
                continue;
            }

            var (childLeft, childRight) = (leftItems[next], rightItems[next]);
            next++;
            if (ReferenceEquals(childLeft, childRight) || ItemsOf(childLeft).Count == 0 || recorded.Contains((childLeft, childRight)))
                continue;
            if (!settled)
            {
                recorded.Add((leftNode, rightNode));
                settled = true;
            }

            expansions++;
            units += ItemsOf(childLeft).Count + 1;
            frames.Push((leftNode, rightNode, leftItems, rightItems, next));
            (leftNode, rightNode, leftItems, rightItems, next) = (childLeft, childRight, ItemsOf(childLeft), ItemsOf(childRight), 0);
            settled = leftItems.Count >= Result.ValueSemanticComparer.RetainedWidth;
            if (settled)
                recorded.Add((childLeft, childRight));
        }
    }

    [Fact]
    public void ReferenceClasses_IsomorphicSharing_KeepsTheExactPairWalksCounts()
    {
        // Node to node correspondence: each class is one recorded pair, so the walk is exactly the
        // exact-pair walk, expansion for expansion and unit for unit.
        var (left, right) = Witness("isomorphic");
        var single = ObserveWalk(left, right, single: true);
        Assert.True(single.Equal);
        var exact = ExactPairWalkOfEqualValues(left, right);
        Assert.Equal(exact.Expansions, single.Expansions);
        Assert.Equal(exact.Units, single.Units);

        // The model is faithful where it applies, and on the differently shared pair it is the m²
        // blow-up (checked at a width where that stays cheap).
        var (smallLeft, smallRight) = (Register(64, 12, ShiftRegister), Register(64, 12, Mixing));
        var small = ObserveWalk(smallLeft, smallRight, single: true);
        var smallExact = ExactPairWalkOfEqualValues(smallLeft, smallRight);
        Assert.True(small.Equal);
        Assert.True(smallExact.Expansions > 4 * small.Expansions, $"{smallExact.Expansions} vs {small.Expansions}");
    }

    [Theory]
    [MemberData(nameof(WitnessShapes))]
    public void ReferenceClasses_OneDeepLeafMismatch_IsUnequalOnEveryWalk(string shape)
    {
        // One deepest leaf differs on one side: no route may return an early true. In the LATE
        // variant only the root's last child reaches the different leaf, through fresh nodes, so
        // the walk meets it after every other level has merged into its classes.
        var (left, right) = Witness(shape, mismatchAt: WitnessWidth - 1);
        var (_, correct) = Witness(shape);
        var (_, wrong) = Witness(shape, mismatchAt: 0);
        var late = List([.. ItemsOf(correct).Take(WitnessWidth - 1), ItemsOf(wrong)[WitnessWidth - 1]]);
        foreach (var (x, y) in new[] { (left, right), (right, left), (left, late), (late, left) })
        {
            var single = ObserveWalk(x, y, single: true);
            var operation = ObserveWalk(x, y, single: false);
            Assert.False(single.Equal);
            Assert.False(operation.Equal);
            Assert.InRange(single.Expansions, 1, WitnessExpansionBound);
            Assert.InRange(single.Units, 1, WitnessUnitBound);
            Assert.Equal(single.Units, operation.Units);
            Assert.Equal(single.Expansions, operation.Expansions);
        }
    }

    [Fact]
    public void ReferenceClasses_OneOperation_ReusesClassesAcrossComparisons_AndKeepsEveryVerdict()
    {
        // contains/distinct shapes through ONE operation comparer: a mismatching comparison keeps the
        // knowledge of its completed levels and retains its unequal pairs; equal knowledge is
        // transitive across comparisons (B ~ A and C ~ A answer B against C without a walk).
        var a = Register(WitnessWidth, WitnessDepth, ShiftRegister);
        var b = Register(WitnessWidth, WitnessDepth, Mixing);
        var c = Register(WitnessWidth, WitnessDepth, 5);
        var unequal = Register(WitnessWidth, WitnessDepth, Mixing, mismatchAt: WitnessWidth / 2);
        var comparer = OperationComparer(out var observations);

        Assert.False(comparer.Equals(a, unequal));
        Assert.True(comparer.Equals(a, b));
        Assert.True(comparer.Equals(c, a));
        var expansions = observations.EqualityPairExpansionCount;
        Assert.InRange(expansions, 1, 3 * WitnessExpansionBound);

        // Repetitions and the transitive pairs are answered from the memo: no expansion at all.
        Assert.True(comparer.Equals(b, c));
        Assert.True(comparer.Equals(c, b));
        Assert.True(comparer.Equals(a, b));
        Assert.False(comparer.Equals(a, unequal));
        Assert.Equal(expansions, observations.EqualityPairExpansionCount);

        // New unequal pairs are walked, and still decided exactly.
        Assert.False(comparer.Equals(b, unequal));
        Assert.False(comparer.Equals(unequal, c));
        Assert.InRange(observations.EqualityPairExpansionCount - expansions, 1, 2 * WitnessExpansionBound);
        Assert.Null(comparer.CompleteOperation());
    }

    [Fact]
    public void ReferenceClasses_AFalseComparison_DropsTheUnionsOfItsOpenLevels_AndKeepsItsCompletedOnes()
    {
        // (p, q) is recorded at its first descent, into the equal (p0, q0), then its last leaf
        // differs. The false verdict must drop p ~ q: kept, the second comparison would skip (p, q)
        // as equal and return true. The completed (p0, q0) stays known equal.
        var shared = List(Atom(1), Atom(2));
        var p0 = List(shared, shared);
        var q0 = List(List(Atom(1), Atom(2)), List(Atom(1), Atom(2)));
        var p = List(p0, Atom(1));
        var q = List(q0, Atom(2));
        var comparer = OperationComparer(out var observations);

        Assert.False(comparer.Equals(List(p), List(q)));
        Assert.False(comparer.Equals(List(p, Atom(0)), List(q, Atom(0))));
        Assert.False(comparer.Equals(List(Atom(0), p), List(Atom(0), q)));
        var expansions = observations.EqualityPairExpansionCount;
        Assert.True(comparer.Equals(p0, q0));
        Assert.True(comparer.Equals(q0, p0));
        Assert.Equal(expansions, observations.EqualityPairExpansionCount);
        Assert.Null(comparer.CompleteOperation());
    }

    [Fact]
    public void ReferenceClasses_CompressingCommittedPathsDuringATentativeWalk_PreservesRollback()
    {
        // Every node has the same value but a distinct reference. The oracle is reachability in an
        // undirected graph of retained equations, independent of representatives and parent links.
        var nodes = Enumerable.Range(0, 64).Select(_ => List(Atom(1))).ToArray();
        var classes = new ReferenceClasses();
        var retained = new List<(int Left, int Right)>();
        var pending = new List<(int Left, int Right)>();

        // Eight committed classes with paths of length three. Do not query them yet: querying under
        // the tentative links below must compress only the committed parts of those paths.
        for (var start = 0; start < nodes.Length; start += 8)
        {
            for (var stride = 1; stride < 8; stride *= 2)
            {
                for (var i = start; i < start + 8; i += 2 * stride)
                {
                    Assert.True(classes.Union(nodes[i], nodes[i + stride]));
                    retained.Add((i, i + stride));
                }
            }
        }

        Record(0, 8, completed: false);
        Record(16, 24, completed: true);
        Record(0, 16, completed: false);
        Record(32, 40, completed: true);
        Record(0, 32, completed: false);
        Record(48, 56, completed: true);
        Record(0, 48, completed: true);
        AssertKnowledge(retained.Concat(pending));
        classes.Rollback();
        pending.Clear();
        AssertKnowledge(retained);

        // A second walk must safely undo links over the forest re-built by the first rollback.
        Record(8, 16, completed: false);
        Record(24, 32, completed: false);
        Record(0, 8, completed: false);
        AssertKnowledge(retained.Concat(pending));
        classes.Rollback();
        pending.Clear();
        AssertKnowledge(retained);

        // Successful walks commit every equation, including ones not marked as completed yet.
        Record(8, 16, completed: false);
        Record(24, 32, completed: false);
        Record(0, 8, completed: false);
        classes.Commit();
        retained.AddRange(pending);
        pending.Clear();
        AssertKnowledge(retained);
        Assert.False(classes.Union(nodes[7], nodes[63]));
        classes.Rollback(); // A transaction with no new links leaves committed knowledge alone.
        AssertKnowledge(retained);

        void Record(int left, int right, bool completed)
        {
            var union = classes.UnionTentatively(nodes[left], nodes[right]);
            Assert.NotEqual(ReferenceClasses.NoUnion, union);
            pending.Add((left, right));
            if (completed)
            {
                classes.MarkCompleted(union);
                retained.Add((left, right));
            }
        }

        void AssertKnowledge(IEnumerable<(int Left, int Right)> equations)
        {
            var reachable = new bool[nodes.Length, nodes.Length];
            for (var i = 0; i < nodes.Length; i++)
                reachable[i, i] = true;
            foreach (var (left, right) in equations)
                reachable[left, right] = reachable[right, left] = true;
            for (var via = 0; via < nodes.Length; via++)
                for (var left = 0; left < nodes.Length; left++)
                    for (var right = 0; right < nodes.Length; right++)
                        reachable[left, right] |= reachable[left, via] && reachable[via, right];
            for (var left = 0; left < nodes.Length; left++)
                for (var right = 0; right < nodes.Length; right++)
                    Assert.Equal(reachable[left, right], classes.Same(nodes[left], nodes[right]));
        }
    }

    // ── The evaluator routes, with the witness values supplied by host operations ──────────

    private static (EvalResult<Evaluator.CountedResult> Result, ValueTraversalObservations Traversal) RunWithWitness(
        string body, Result left, Result right)
    {
        var operations = HostOperations.Create(
            HostOperation.Create("LeftValue", (_, _) => left),
            HostOperation.Create("RightValue", (_, _) => right));
        var traversal = new ValueTraversalObservations();
        var (result, _) = Evaluator.RunCountedObserved(
            ParseValidWith(body, operations),
            limits: null,
            enableOptimizations: true,
            observations: new EvaluationObservations { StructuralTraversal = traversal },
            hostOperations: operations);
        return (result, traversal);
    }

    public static TheoryData<string, string> WitnessRoutes()
    {
        var data = new TheoryData<string, string>();
        foreach (var shape in new[] { "differently-shared", "isomorphic" })
        {
            data.Add(shape, "LeftValue == RightValue");
            data.Add(shape, "LeftValue != RightValue");
            data.Add(shape, "contains([LeftValue], RightValue)");
            data.Add(shape, "distinct([LeftValue, RightValue]).count");
            data.Add(shape, "Same(x, x) = 1\nSame([LeftValue][0], [RightValue][0])");
        }

        return data;
    }

    [Theory]
    [MemberData(nameof(WitnessRoutes))]
    public void ReferenceClasses_EveryEvaluatorRoute_IsLinear_AndDecidesTheVerdict(string shape, string body)
    {
        foreach (var equal in new[] { true, false })
        {
            var (left, right) = Witness(shape, mismatchAt: equal ? -1 : WitnessWidth - 1);
            var (result, traversal) = RunWithWitness(body, left, right);
            // The host values' admission walk is charged to the same structural units: take it out.
            var (admitted, admission) = RunWithWitness("[LeftValue, RightValue].count", left, right);
            AssertNumber(2, admitted);

            switch (body)
            {
                case "LeftValue == RightValue":
                case "contains([LeftValue], RightValue)":
                    AssertBool(equal, result);
                    break;
                case "LeftValue != RightValue":
                    AssertBool(!equal, result);
                    break;
                case "distinct([LeftValue, RightValue]).count":
                    AssertNumber(equal ? 1 : 2, result);
                    break;
                default:
                    if (equal)
                    {
                        AssertNumber(1, result);
                    }
                    else
                    {
                        Assert.True(result.IsError);
                        Assert.IsType<EvalError.BadArity>(Innermost(result.Error));
                    }

                    break;
            }

            // (Unequal values usually hash apart in distinct, and are then never compared.)
            Assert.InRange(traversal.EqualityPairExpansionCount, 0, WitnessExpansionBound);
            // distinct also hashes both values once, node by node.
            var hashing = body.StartsWith("distinct", StringComparison.Ordinal) ? 2 * RegisterSlots(WitnessWidth, WitnessDepth) + 4 * RegisterNodes(WitnessWidth, WitnessDepth) : 0;
            Assert.InRange(traversal.StructuralWorkUnits - admission.StructuralWorkUnits, 1, WitnessUnitBound + hashing);
        }
    }

    // ── Randomized differential against a naive unfolded-tree comparison ──────────────────

    /// <summary>The unfolded-tree comparison with no memo at all: the definition, path by path.</summary>
    private static bool NaiveEquals(Result left, Result right) => (left, right) switch
    {
        (Result.Atom(var x), Result.Atom(var y)) => x.Equals(y),
        (Result.Str(var x), Result.Str(var y)) => string.Equals(x, y, StringComparison.Ordinal),
        (Result.Bool(var x), Result.Bool(var y)) => x == y,
        (Result.ListValue(var x), Result.ListValue(var y)) => NaiveItemsEqual(x, y),
        (Result.SequenceValue(var x), Result.SequenceValue(var y)) => NaiveItemsEqual(x, y),
        _ => false,
    };

    private static bool NaiveItemsEqual(IReadOnlyList<Result> left, IReadOnlyList<Result> right)
    {
        if (left.Count != right.Count)
            return false;
        for (var i = 0; i < left.Count; i++)
        {
            if (!NaiveEquals(left[i], right[i]))
                return false;
        }

        return true;
    }

    /// <summary>
    /// Random small DAGs with deliberate re-sharing. Leaves come from equivalence groups whose members
    /// are equal but distinct objects (NaN twice, ±0, 1 / 1.0 / 1.00, Booleans, and strings of 64 or
    /// more code units that are equal or differ in the last one), so value-equal nodes are common and
    /// a copy can share them differently.
    /// </summary>
    private sealed class DifferentialValues(int seed)
    {
        private const int MaxUnfolded = 300;

        private readonly Random random = new(seed);
        private readonly Dictionary<Result, int> groupOf = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<Result, int> unfolded = new(ReferenceEqualityComparer.Instance);
        private readonly List<Result> pool = [];

        private static readonly Func<Result>[][] Groups =
        [
            [() => new Result.Atom(Decimal128.NaN), () => new Result.Atom(Decimal128.NaN)],
            [() => new Result.Atom(Decimal128.Zero), () => new Result.Atom(Decimal128.NegativeZero)],
            [() => new Result.Atom(1), () => new Result.Atom(Decimal128.Parse("1.0")), () => new Result.Atom(Decimal128.Parse("1.00"))],
            [() => new Result.Atom(2)],
            [() => new Result.Bool(true)],
            [() => new Result.Bool(false)],
            [() => new Result.Str(new string('a', 64))],
            [() => new Result.Str(new string('a', 63) + "b")],
            [() => new Result.Str(new string('q', 1_100))],
            [() => new Result.Str(new string('q', 1_099) + "r")],
            [() => new Result.Str("s")],
        ];

        public IReadOnlyList<Result> Pool => pool;

        private Result Leaf(int group)
        {
            var members = Groups[group];
            var leaf = members[random.Next(members.Length)]();
            groupOf[leaf] = group;
            unfolded[leaf] = 1;
            return leaf;
        }

        private Result RandomLeaf() => Leaf(random.Next(Groups.Length));

        private Result Structure(bool list, Result[] items)
        {
            var node = list ? List(items) : Seq(items);
            unfolded[node] = 1 + items.Sum(item => unfolded[item]);
            return node;
        }

        /// <summary>Grows the pool by one node: a leaf, or a structure over earlier pool nodes and leaves.</summary>
        public Result Grow()
        {
            Result node;
            if (pool.Count == 0 || random.NextDouble() < 0.25)
            {
                node = RandomLeaf();
            }
            else
            {
                var items = new Result[random.Next(0, 4)];
                var size = 1;
                for (var i = 0; i < items.Length; i++)
                {
                    var shared = pool[random.Next(pool.Count)];
                    items[i] = random.NextDouble() < 0.75 && size + unfolded[shared] <= MaxUnfolded ? shared : RandomLeaf();
                    size += unfolded[items[i]];
                }

                node = Structure(random.NextDouble() < 0.8, items);
            }

            pool.Add(node);
            return node;
        }

        /// <summary>
        /// An equal copy of <paramref name="value"/> with different sharing: equal leaves are fresh
        /// members of the same group, a node is copied once or several times, and value-equal nodes of
        /// different origins are sometimes merged into one object.
        /// </summary>
        public Result Reshare(Result value)
        {
            var copies = new Dictionary<Result, List<Result>>(ReferenceEqualityComparer.Instance);
            var merged = new Dictionary<Result, Result>(Result.ValueComparer);
            return Copy(value);

            Result Copy(Result node)
            {
                if (groupOf.TryGetValue(node, out var group))
                    return random.NextDouble() < 0.5 ? node : Leaf(group);
                if (copies.TryGetValue(node, out var made) && random.NextDouble() < 0.5)
                    return made[random.Next(made.Count)];
                if (made is null)
                    copies[node] = made = [];

                var (list, items) = node switch
                {
                    Result.ListValue(var listItems) => (true, listItems),
                    Result.SequenceValue(var sequenceItems) => (false, sequenceItems),
                    _ => throw new InvalidOperationException("unexpected value"),
                };
                var copy = Structure(list, [.. items.Select(Copy)]);
                if (random.NextDouble() < 0.4)
                {
                    if (merged.TryGetValue(copy, out var representative))
                        copy = representative;
                    else
                        merged[copy] = copy;
                }

                made.Add(copy);
                return copy;
            }
        }

        /// <summary>A copy of <paramref name="value"/> with one random change: a leaf, a kind, or a count.</summary>
        public Result Mutate(Result value)
        {
            var paths = new List<int[]>();
            Collect(value, []);
            var target = paths[random.Next(paths.Count)];
            return Rebuild(value, target, 0);

            void Collect(Result node, int[] path)
            {
                paths.Add(path);
                IReadOnlyList<Result>? children = node switch
                {
                    Result.ListValue(var listItems) => listItems,
                    Result.SequenceValue(var sequenceItems) => sequenceItems,
                    _ => null,
                };
                for (var i = 0; children is not null && i < children.Count && paths.Count <= 64; i++)
                    Collect(children[i], [.. path, i]);
            }

            Result Rebuild(Result node, int[] path, int depth)
            {
                var (list, items) = node switch
                {
                    Result.ListValue(var listItems) => (true, listItems),
                    Result.SequenceValue(var sequenceItems) => (false, sequenceItems),
                    _ => (false, (IReadOnlyList<Result>)[]),
                };
                if (depth == path.Length)
                {
                    if (groupOf.TryGetValue(node, out var group))
                        return Leaf((group + 1 + random.Next(Groups.Length - 1)) % Groups.Length);
                    return random.Next(3) switch
                    {
                        0 => Structure(!list, [.. items]),
                        1 => Structure(list, [.. items, RandomLeaf()]),
                        _ => items.Count == 0 ? Structure(list, [RandomLeaf()]) : Structure(list, [.. items.Take(items.Count - 1)]),
                    };
                }

                var rebuilt = items.ToArray();
                rebuilt[path[depth]] = Rebuild(items[path[depth]], path, depth + 1);
                return Structure(list, rebuilt);
            }
        }
    }

    [Fact]
    public void ReferenceClasses_RandomizedDifferential_AgreesWithTheNaiveComparison_OnEveryRoute()
    {
        long comparisons = 0, equalVerdicts = 0, equalDistinctObjects = 0, deepEqual = 0, deepUnequal = 0;
        for (var seed = 1; seed <= 60; seed++)
        {
            var values = new DifferentialValues(seed);
            for (var i = 0; i < 30; i++)
                _ = values.Grow();

            // Candidates: the pool, and for each of its six deepest nodes four equal copies shared
            // differently and two near misses (one change, then re-shared): deep equal values with
            // no node-to-node correspondence, and deep unequal ones that agree almost everywhere.
            var random = new Random(seed * 7919);
            var candidates = new List<Result>(values.Pool);
            foreach (var source in values.Pool.OrderByDescending(DepthOf).Take(6).ToArray())
            {
                for (var copy = 0; copy < 4; copy++)
                    candidates.Add(values.Reshare(source));
                for (var miss = 0; miss < 2; miss++)
                    candidates.Add(values.Reshare(values.Mutate(source)));
            }

            // ==: the single walk through the evaluator's decision, and the context-free comparer.
            var budget = EvaluationBudget.Create(limits: null);
            var depths = candidates.Select(DepthOf).ToArray();
            for (var i = 0; i < candidates.Count; i++)
            {
                for (var j = 0; j < candidates.Count; j++)
                {
                    var (left, right) = (candidates[i], candidates[j]);
                    var expected = NaiveEquals(left, right);
                    var decided = Result.EvaluatorValueEquals(left, right, budget, observations: null);
                    Assert.False(decided.IsError);
                    Assert.True(expected == decided.Value, $"seed {seed}: == of {i} and {j} decided {decided.Value}");
                    Assert.Equal(expected, Result.ValueComparer.Equals(left, right));
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

            // ONE operation comparer over every ordered pair, twice: committed classes, unequal pairs,
            // and the rolled-back tentative unions of every false comparison are reused throughout.
            var shared = OperationComparer(out _);
            for (var sweep = 0; sweep < 2; sweep++)
            {
                for (var i = 0; i < candidates.Count; i++)
                {
                    for (var j = 0; j < candidates.Count; j++)
                        Assert.True(NaiveEquals(candidates[i], candidates[j]) == shared.Equals(candidates[i], candidates[j]), $"seed {seed} sweep {sweep}: operation {i} vs {j}");
                }
            }

            Assert.Null(shared.CompleteOperation());

            // contains and distinct, each one operation as the builtins run them.
            for (var round = 0; round < 8; round++)
            {
                var items = Enumerable.Range(0, random.Next(1, 10)).Select(_ => candidates[random.Next(candidates.Count)]).ToArray();
                var needle = candidates[random.Next(candidates.Count)];
                var containsComparer = OperationComparer(out _);
                Assert.Equal(items.Any(item => NaiveEquals(item, needle)), items.Any(item => containsComparer.Equals(item, needle)));
                Assert.Null(containsComparer.CompleteOperation());

                var distinctComparer = OperationComparer(out _);
                var kept = new HashSet<Result>(distinctComparer);
                var naiveKept = new List<Result>();
                foreach (var item in items)
                {
                    if (!naiveKept.Any(earlier => NaiveEquals(earlier, item)))
                        naiveKept.Add(item);
                    _ = kept.Add(item);
                }

                Assert.Equal(naiveKept.Count, kept.Count);
                Assert.Null(distinctComparer.CompleteOperation());
            }
        }

        // The generator must exercise both verdicts substantially, equal distinct objects included,
        // and deep values (at least three levels of structure) both ways.
        Assert.InRange(equalVerdicts, comparisons / 20, comparisons - comparisons / 20);
        Assert.True(equalDistinctObjects >= comparisons / 50, $"{equalDistinctObjects} of {comparisons}");
        Assert.True(deepEqual >= 3_500, $"deep equal comparisons: {deepEqual}");
        Assert.True(deepUnequal >= 2_000, $"deep unequal comparisons: {deepUnequal}");
    }

    /// <summary>Levels of nested structure below a value (0 for a leaf or an empty structure).</summary>
    private static int DepthOf(Result value)
    {
        var items = ItemsOf(value);
        return items.Count == 0 ? 0 : 1 + items.Max(DepthOf);
    }

    // ── Memory: one == on the m = 512 differently shared pair ─────────────────────────────

    [Fact]
    public void ReferenceClasses_OneComparison_OfTheDifferentlySharedPair_AllocatesUnderEightMegabytes_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var budget = EvaluationBudget.Create(limits: null);
        // Warm up the walk and the memo types on a small pair of the same shapes.
        Assert.True(Result.EvaluatorValueEquals(Register(16, 4, ShiftRegister), Register(16, 4, Mixing), budget, observations: null).Value);
        var (left, right) = Witness("differently-shared");

        var before = GC.GetAllocatedBytesForCurrentThread();
        var verdict = Result.EvaluatorValueEquals(left, right, budget, observations: null);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.False(verdict.IsError);
        Assert.True(verdict.Value);
        // The exact-pair memo allocated about 283 MB here.
        Assert.InRange(allocated, 0, 8L * 1024 * 1024);
        GcIsolatedAllocation.Complete();
    }
}
