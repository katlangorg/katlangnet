using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using KatLang.Evaluation;
using KatLang.TestInfrastructure;
namespace KatLang.Tests;

/// <summary>
/// One reference-class entry per union. <see cref="ReferenceClasses"/> used to link by size, so the
/// first union of two fresh nodes stored two 32-byte entries — the child's link and the
/// representative's size — where the exact-pair memo before it stored one 24-byte pair, and the
/// ordinary shapes paid for it: the isomorphic control of <see cref="Witness"/> took 5.24 MB in one
/// host comparison against the exact-pair memo's 1.96 MB, and two equal unshared trees 2.1–2.7 times
/// the bytes. Classes now link by index, which reads nothing stored, so only a node linked below
/// another one has an entry; and the two walks whose memo dies with one comparison use
/// <see cref="CommittedReferenceClasses"/>, whose entry is the parent reference alone (24 bytes).
/// Every verdict, expansion and unit stays exactly what it was: the walks read class membership
/// only, and which node represents a class decides nothing they observe.
/// </summary>
public partial class SharedValueGraphComplexityTests
{
    /// <summary>
    /// The layout this change replaced (<c>ReferenceClasses</c> at 51adb70f), kept as the
    /// differential's reference: union by size, so BOTH representatives of a union get an entry, the
    /// same two layers, and the same path compression and rollback.
    /// </summary>
    private sealed class TwoEntryReferenceClasses
    {
        private readonly Dictionary<Result, Entry> entries = new(ReferenceEqualityComparer.Instance);
        private readonly List<(Result Left, Result Right, Result Child, bool Completed)> tentative = [];
        private int generation = 1;

        private struct Entry
        {
            internal Result? Parent;
            internal int Size;
            internal int Generation;
        }

        public int RecordedReferences => entries.Count;

        public bool Same(Result left, Result right) => ReferenceEquals(Find(left), Find(right));

        public bool Union(Result left, Result right)
        {
            Assert.Empty(tentative);
            return Link(left, right, tentatively: false, out _);
        }

        public int UnionTentatively(Result left, Result right)
        {
            if (!Link(left, right, tentatively: true, out var child))
                return ReferenceClasses.NoUnion;
            tentative.Add((left, right, child, false));
            return tentative.Count - 1;
        }

        public void MarkCompleted(int union) => tentative[union] = tentative[union] with { Completed = true };

        public void Commit()
        {
            if (tentative.Count == 0)
                return;
            tentative.Clear();
            generation++;
        }

        public void Rollback()
        {
            if (tentative.Count == 0)
                return;
            for (var i = tentative.Count - 1; i >= 0; i--)
            {
                ref var child = ref CollectionsMarshal.GetValueRefOrNullRef(entries, tentative[i].Child);
                ref var parent = ref CollectionsMarshal.GetValueRefOrNullRef(entries, child.Parent!);
                parent.Size -= child.Size;
                child.Parent = null;
                child.Generation = 0;
            }

            generation++;
            foreach (var union in tentative)
            {
                if (union.Completed)
                    _ = Link(union.Left, union.Right, tentatively: false, out _);
            }

            tentative.Clear();
        }

        private Result Find(Result node)
        {
            var current = node;
            Result? committedRoot = null;
            var committedLinks = 0;
            while (true)
            {
                ref var entry = ref CollectionsMarshal.GetValueRefOrNullRef(entries, current);
                if (Unsafe.IsNullRef(ref entry) || entry.Parent is null)
                    break;
                if (committedRoot is null)
                {
                    if (entry.Generation == generation)
                        committedRoot = current;
                    else
                        committedLinks++;
                }

                current = entry.Parent;
            }

            committedRoot ??= current;
            if (committedLinks > 1)
            {
                var compressed = node;
                while (!ReferenceEquals(compressed, committedRoot))
                {
                    ref var entry = ref CollectionsMarshal.GetValueRefOrNullRef(entries, compressed);
                    var parent = entry.Parent!;
                    entry.Parent = committedRoot;
                    compressed = parent;
                }
            }

            return current;
        }

        private bool Link(Result left, Result right, bool tentatively, out Result child)
        {
            var leftRoot = Find(left);
            var rightRoot = Find(right);
            if (ReferenceEquals(leftRoot, rightRoot))
            {
                child = leftRoot;
                return false;
            }

            ref var leftEntry = ref CollectionsMarshal.GetValueRefOrAddDefault(entries, leftRoot, out var leftExists);
            if (!leftExists)
                leftEntry.Size = 1;
            ref var rightEntry = ref CollectionsMarshal.GetValueRefOrAddDefault(entries, rightRoot, out var rightExists);
            if (!rightExists)
            {
                rightEntry.Size = 1;
                leftEntry = ref CollectionsMarshal.GetValueRefOrNullRef(entries, leftRoot);
            }

            if (leftEntry.Size < rightEntry.Size)
            {
                leftEntry.Parent = rightRoot;
                leftEntry.Generation = tentatively ? generation : 0;
                rightEntry.Size += leftEntry.Size;
                child = leftRoot;
            }
            else
            {
                rightEntry.Parent = leftRoot;
                rightEntry.Generation = tentatively ? generation : 0;
                leftEntry.Size += rightEntry.Size;
                child = rightRoot;
            }

            return true;
        }
    }

    /// <summary>Equal-valued nodes with distinct references: the classes see identity only.</summary>
    private static Result[] DistinctNodes(int count) => [.. Enumerable.Range(0, count).Select(_ => List(Atom(1)))];

    /// <summary>
    /// The oracle: the connected components of <paramref name="equations"/> over node indices,
    /// independent of representatives, links and layout.
    /// </summary>
    private static int[] Components(int count, IEnumerable<(int Left, int Right)> equations)
    {
        var label = Enumerable.Range(0, count).ToArray();
        foreach (var (left, right) in equations)
        {
            var (from, to) = (label[left], label[right]);
            if (from == to)
                continue;
            for (var i = 0; i < count; i++)
            {
                if (label[i] == from)
                    label[i] = to;
            }
        }

        return label;
    }

    [Fact]
    public void ReferenceClassEntries_AFirstUnion_RecordsOneEntry_AndAnUndoneLinkKeepsItsEntryForReuse()
    {
        var (a, b, c, d) = (List(Atom(1)), List(Atom(1)), List(Atom(1)), List(Atom(1)));
        var classes = new ReferenceClasses();
        var model = new TwoEntryReferenceClasses();

        // Two fresh nodes: one entry, where the layout by size stored both representatives.
        Assert.True(classes.Union(a, b));
        Assert.True(model.Union(a, b));
        Assert.Equal(1, classes.RecordedReferences);
        Assert.Equal(2, model.RecordedReferences);

        // A fresh node joining a class: still one entry per union.
        Assert.True(classes.Union(c, a));
        Assert.True(model.Union(c, a));
        Assert.Equal(2, classes.RecordedReferences);
        Assert.Equal(3, model.RecordedReferences);
        Assert.False(classes.Union(b, c));
        Assert.Equal(2, classes.RecordedReferences);

        // An undone tentative link keeps its entry as a representative's; linking the same two
        // representatives again, in the same order, picks the same child and reuses it.
        Assert.NotEqual(ReferenceClasses.NoUnion, classes.UnionTentatively(d, a));
        Assert.True(classes.Same(d, b));
        Assert.Equal(3, classes.RecordedReferences);
        classes.Rollback();
        Assert.False(classes.Same(d, a));
        Assert.True(classes.Same(a, c));
        Assert.Equal(3, classes.RecordedReferences);
        Assert.True(classes.Union(d, a));
        Assert.True(classes.Same(d, c));
        Assert.Equal(3, classes.RecordedReferences);

        // The committed-only form records exactly one entry per union that merged two classes.
        var committed = new CommittedReferenceClasses();
        Assert.True(committed.Union(a, b));
        Assert.Equal(1, committed.RecordedReferences);
        Assert.False(committed.Union(b, a));
        Assert.True(committed.Union(c, d));
        Assert.True(committed.Union(d, b));
        Assert.False(committed.Same(a, List(Atom(1))));
        Assert.True(committed.Same(c, a));
        Assert.Equal(3, committed.RecordedReferences);
    }

    [Fact]
    public void ReferenceClassEntries_RandomSequences_AgreeWithTheTwoEntryLayout_AndTheEquationOracle()
    {
        long committedUnions = 0, tentativeUnions = 0, noUnions = 0, commits = 0, rollbacks = 0, keptOnRollback = 0, sameClass = 0, queries = 0;
        long layeredEntries = 0, committedEntries = 0, modelEntries = 0;
        for (var seed = 1; seed <= 300; seed++)
        {
            var random = new Random(seed);
            var nodes = DistinctNodes(random.Next(4, 160));
            var classes = new ReferenceClasses();
            var model = new TwoEntryReferenceClasses();
            var committed = new CommittedReferenceClasses();
            var committedModel = new TwoEntryReferenceClasses();
            var retained = new List<(int Left, int Right)>();
            var pending = new List<(int Left, int Right, bool Completed)>();
            var committedEquations = new List<(int Left, int Right)>();
            var merges = 0;

            for (var step = 0; step < 300; step++)
            {
                var (i, j) = (random.Next(nodes.Length), random.Next(nodes.Length));
                switch (random.Next(12))
                {
                    // A committed union is only valid while no tentative link exists.
                    case < 2 when pending.Count == 0:
                    {
                        var merged = classes.Union(nodes[i], nodes[j]);
                        Assert.Equal(model.Union(nodes[i], nodes[j]), merged);
                        retained.Add((i, j));
                        committedUnions++;
                        break;
                    }

                    case < 7:
                    {
                        var union = classes.UnionTentatively(nodes[i], nodes[j]);
                        Assert.Equal(model.UnionTentatively(nodes[i], nodes[j]), union);
                        if (union == ReferenceClasses.NoUnion)
                        {
                            noUnions++;
                            break;
                        }

                        var completed = random.Next(3) == 0;
                        if (completed)
                        {
                            classes.MarkCompleted(union, nodes[i], nodes[j]);
                            model.MarkCompleted(union);
                        }

                        pending.Add((i, j, completed));
                        tentativeUnions++;
                        break;
                    }

                    case 7:
                        classes.Commit();
                        model.Commit();
                        retained.AddRange(pending.Select(union => (union.Left, union.Right)));
                        pending.Clear();
                        commits++;
                        AssertPairs(Components(nodes.Length, retained), every: false);
                        break;

                    case 8:
                        classes.Rollback();
                        model.Rollback();
                        foreach (var union in pending.Where(union => union.Completed))
                        {
                            retained.Add((union.Left, union.Right));
                            keptOnRollback++;
                        }

                        pending.Clear();
                        rollbacks++;
                        AssertPairs(Components(nodes.Length, retained), every: false);
                        break;

                    default:
                    {
                        var merged = committed.Union(nodes[i], nodes[j]);
                        Assert.Equal(committedModel.Union(nodes[i], nodes[j]), merged);
                        committedEquations.Add((i, j));
                        if (merged)
                            merges++;
                        break;
                    }
                }

                // A random query on both forms, and the entry counts: never more than the layout by
                // size, and exactly one per merge in the committed-only form.
                var (x, y) = (nodes[random.Next(nodes.Length)], nodes[random.Next(nodes.Length)]);
                var same = classes.Same(x, y);
                Assert.Equal(model.Same(x, y), same);
                Assert.Equal(committedModel.Same(x, y), committed.Same(x, y));
                queries++;
                if (same && !ReferenceEquals(x, y))
                    sameClass++;
                Assert.True(classes.RecordedReferences <= model.RecordedReferences, $"seed {seed} step {step}");
                Assert.Equal(merges, committed.RecordedReferences);
                Assert.True(committed.RecordedReferences <= committedModel.RecordedReferences, $"seed {seed} step {step}");
            }

            AssertPairs(Components(nodes.Length, retained.Concat(pending.Select(union => (union.Left, union.Right)))), every: true);
            var committedOracle = Components(nodes.Length, committedEquations);
            for (var left = 0; left < nodes.Length; left++)
            {
                for (var right = 0; right < nodes.Length; right++)
                {
                    var expected = committedOracle[left] == committedOracle[right];
                    Assert.True(expected == committed.Same(nodes[left], nodes[right]), $"seed {seed}: committed-only {left} ~ {right}");
                    Assert.True(expected == committedModel.Same(nodes[left], nodes[right]), $"seed {seed}: committed model {left} ~ {right}");
                }
            }

            layeredEntries += classes.RecordedReferences;
            committedEntries += committed.RecordedReferences;
            modelEntries += model.RecordedReferences + committedModel.RecordedReferences;

            // Every pair at the end of a sequence, and 64 random pairs after each commit or rollback.
            void AssertPairs(int[] oracle, bool every)
            {
                var pairs = every
                    ? Enumerable.Range(0, nodes.Length).SelectMany(left => Enumerable.Range(0, nodes.Length).Select(right => (left, right)))
                    : Enumerable.Range(0, 64).Select(_ => (random.Next(nodes.Length), random.Next(nodes.Length)));
                foreach (var (left, right) in pairs)
                {
                    var expected = oracle[left] == oracle[right];
                    Assert.True(expected == classes.Same(nodes[left], nodes[right]), $"seed {seed}: {left} ~ {right}");
                    Assert.True(expected == model.Same(nodes[left], nodes[right]), $"seed {seed}: model {left} ~ {right}");
                }
            }
        }

        // The generator must exercise every operation, both union outcomes, rollbacks that keep
        // completed links, and real sharing; and the layout by size must have paid for its sizes.
        // (Seeds 1–300 reach about twice each floor.)
        Assert.True(committedUnions >= 4_000, $"committed unions: {committedUnions}");
        Assert.True(tentativeUnions >= 15_000, $"tentative unions: {tentativeUnions}");
        Assert.True(noUnions >= 9_000, $"tentative unions of one class: {noUnions}");
        Assert.True(commits >= 4_000 && rollbacks >= 4_000, $"commits {commits}, rollbacks {rollbacks}");
        Assert.True(keptOnRollback >= 2_500, $"completed links kept on rollback: {keptOnRollback}");
        Assert.InRange(sameClass, queries / 5, 4 * queries / 5);
        Assert.True(layeredEntries + committedEntries < modelEntries, $"{layeredEntries} + {committedEntries} entries against {modelEntries}");
    }

    [Fact]
    public void ReferenceClassEntries_LinkingByIndex_KeepsUncompressedPathsLogarithmic()
    {
        // The tentative layer is never compressed, so its paths are the link rule's alone. A rule
        // that reads nothing stored but always puts one side below would turn a star — one shared
        // node united with n fresh ones in turn — into a chain of n links. Linking by index moves
        // the shared node's representative below only when a fresh index beats every index of its
        // class so far: about ln n ≈ 8.3 times here. The bound leaves a wide margin.
        const int count = 4_096;
        var bound = 4 * BitOperations.Log2(count);
        foreach (var sharedOnTheLeft in new[] { true, false })
        {
            var classes = new ReferenceClasses();
            var shared = List(Atom(1));
            var fresh = DistinctNodes(count);
            foreach (var node in fresh)
                Assert.NotEqual(ReferenceClasses.NoUnion, sharedOnTheLeft ? classes.UnionTentatively(shared, node) : classes.UnionTentatively(node, shared));
            Assert.InRange(fresh.Append(shared).Max(classes.PathLength), 1, bound);
            Assert.Equal(count, classes.RecordedReferences);
            Assert.True(classes.Same(fresh[0], fresh[^1]));
            classes.Rollback();
            Assert.Equal(0, fresh.Append(shared).Max(classes.PathLength));
            Assert.False(classes.Same(fresh[0], fresh[^1]));
        }

        // A chain, each node united with the next, and pairwise merges of equal-sized classes.
        var chain = DistinctNodes(count);
        var chained = new ReferenceClasses();
        for (var i = 1; i < count; i++)
            Assert.NotEqual(ReferenceClasses.NoUnion, chained.UnionTentatively(chain[i - 1], chain[i]));
        Assert.InRange(chain.Max(chained.PathLength), 1, bound);

        var merged = new ReferenceClasses();
        var leaves = DistinctNodes(count);
        for (var width = 1; width < count; width *= 2)
        {
            for (var start = 0; start < count; start += 2 * width)
                Assert.NotEqual(ReferenceClasses.NoUnion, merged.UnionTentatively(leaves[start], leaves[start + width]));
        }

        Assert.InRange(leaves.Max(merged.PathLength), 1, bound);
        Assert.True(merged.Same(leaves[0], leaves[^1]));
    }

    // ── Memory: the ordinary shapes, on every walk ─────────────────────────────────────────

    /// <summary>A complete binary tree of fresh list nodes over distinct atoms (no sharing at all).</summary>
    private static Result UnsharedTree(int depth)
    {
        var next = 0;
        return Build(depth);

        Result Build(int level) => level == 0 ? Atom(next++) : List(Build(level - 1), Build(level - 1));
    }

    [Fact]
    public void ReferenceClassEntries_TheIsomorphicControlAndUnsharedTrees_StayUnderTheOneEntryBounds_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var budget = EvaluationBudget.Create(limits: null);
        // Warm up every walk and its memo types on small shapes of the same kinds.
        for (var warm = 0; warm < 3; warm++)
        {
            _ = Measure("single", Register(16, 4, ShiftRegister), Register(16, 4, ShiftRegister));
            _ = Measure("operation", Register(16, 4, ShiftRegister), Register(16, 4, ShiftRegister));
            _ = Measure("host", Register(16, 4, ShiftRegister), Register(16, 4, ShiftRegister));
        }

        // Bytes of one equal comparison (Release harness, before → after this change), and the bound
        // pinned for each: every bound fails the two-entry layout by size, which stored both
        // representatives of a union in 32-byte entries. The host comparer's isomorphic control is
        // back at the 1,963,096 bytes of the exact-pair memo that reference classes replaced.
        //   isomorphic control  single 2,522,952 → 945,232   operation 3,574,752 → 2,265,992   host 5,238,448 → 1,963,096
        //   unshared depth 14   single 1,211,840 → 452,296   operation 1,737,024 → 1,106,288   host 2,520,528 → 942,808
        //   unshared depth 8    single    29,040 → 10,656    operation    37,600 → 22,032      host    62,104 → 22,704
        //   unshared depth 5    single     2,856 → 1,240     operation     3,984 → 2,600       host     6,040 → 2,256
        // The operation walk's tentative log then went from 32 to 16 bytes per union (2026-11-18,
        // SharedValueGraphComplexityTests.TentativeLog.cs), and its bounds fail the 32-byte log:
        //   operation  isomorphic 2,265,992 → 1,741,768   depth 14 1,106,288 → 844,208   depth 8 22,032 → 18,000   depth 5 2,600 → 2,152
        var cases = new (string Shape, Func<(Result Left, Result Right)> Values, long Single, long Operation, long Host)[]
        {
            ("isomorphic", () => Witness("isomorphic"), 1_100_000, 2_000_000, 2_300_000),
            ("unshared depth 14", () => (UnsharedTree(14), UnsharedTree(14)), 540_000, 975_000, 1_100_000),
            ("unshared depth 8", () => (UnsharedTree(8), UnsharedTree(8)), 13_000, 20_000, 27_000),
            ("unshared depth 5", () => (UnsharedTree(5), UnsharedTree(5)), 1_500, 2_400, 2_700),
        };

        foreach (var (shape, values, single, operation, host) in cases)
        {
            var (left, right) = values();
            var measured = (Single: Measure("single", left, right), Operation: Measure("operation", left, right), Host: Measure("host", left, right));
            Assert.True(measured.Single <= single, $"{shape}: the single-comparison walk allocated {measured.Single} bytes");
            Assert.True(measured.Operation <= operation, $"{shape}: the operation walk allocated {measured.Operation} bytes");
            Assert.True(measured.Host <= host, $"{shape}: the host comparer allocated {measured.Host} bytes");
        }

        GcIsolatedAllocation.Complete();

        long Measure(string walk, Result left, Result right)
        {
            bool equal;
            long allocated;
            switch (walk)
            {
                case "single":
                {
                    var before = GC.GetAllocatedBytesForCurrentThread();
                    var verdict = Result.EvaluatorValueEquals(left, right, budget, observations: null);
                    allocated = GC.GetAllocatedBytesForCurrentThread() - before;
                    Assert.False(verdict.IsError);
                    equal = verdict.Value;
                    break;
                }

                case "operation":
                {
                    var before = GC.GetAllocatedBytesForCurrentThread();
                    var comparer = Result.CreateOperationComparer(budget);
                    var verdict = comparer.TryEquals(left, right);
                    var completion = comparer.CompleteOperation();
                    allocated = GC.GetAllocatedBytesForCurrentThread() - before;
                    Assert.False(verdict.IsError);
                    Assert.Null(completion);
                    equal = verdict.Value;
                    break;
                }

                default:
                {
                    var before = GC.GetAllocatedBytesForCurrentThread();
                    equal = Result.ValueComparer.Equals(left, right);
                    allocated = GC.GetAllocatedBytesForCurrentThread() - before;
                    break;
                }
            }

            Assert.True(equal, $"{walk} decided an equal pair unequal");
            return allocated;
        }
    }
}
