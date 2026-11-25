using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
namespace KatLang.Tests;

/// <summary>
/// The 16-byte tentative log of <see cref="ReferenceClasses"/> (2026-11-18, implementation only). The
/// operation walk's log stored the pair, the child and a completion flag of every tentative union,
/// 32 bytes, and was about half of that walk's memo bytes. It now stores two references: an open
/// union's child, which <see cref="ReferenceClasses.MarkCompleted"/> overwrites with the completed
/// pair, and a rollback finds a completed union's child again by the stamp of its link. Linking,
/// compression, undo and re-linking must be EXACTLY the former log's, so the differential below
/// compares the two forests node for node, not only their classes.
/// </summary>
public partial class SharedValueGraphComplexityTests
{
    /// <summary>
    /// The layout this change replaced (<c>ReferenceClasses</c> at 5fee88d9), kept as the
    /// differential's reference: the same link rule and compression, a generation stamp, and a log
    /// of the pair, the child and a completion flag per tentative union.
    /// </summary>
    private sealed class ThirtyTwoByteLogReferenceClasses
    {
        private readonly Dictionary<Result, Entry> entries = new(ReferenceEqualityComparer.Instance);
        private readonly List<(Result Left, Result Right, Result Child, bool Completed)> tentative = [];
        private int generation = 1;

        private struct Entry
        {
            internal Result? Parent;
            internal int Generation;
        }

        public int RecordedReferences => entries.Count;

        /// <summary>The logged tentative unions, oldest first (for the coverage counts).</summary>
        public IReadOnlyList<(Result Left, Result Right, Result Child, bool Completed)> Log => tentative;

        public bool TryGetRecordedParent(Result node, out Result? parent)
        {
            var recorded = entries.TryGetValue(node, out var entry);
            parent = entry.Parent;
            return recorded;
        }

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

            Result parent;
            (child, parent) = ReferenceClasses.LinksBelow(leftRoot, rightRoot) ? (leftRoot, rightRoot) : (rightRoot, leftRoot);
            ref var entry = ref CollectionsMarshal.GetValueRefOrAddDefault(entries, child, out _);
            entry.Parent = parent;
            entry.Generation = tentatively ? generation : 0;
            return true;
        }
    }

    /// <summary>
    /// Random sequences of committed and tentative unions, completions marked LATE and in any order
    /// (not only right after their union, as a walk marks a level that descended), commits, rollbacks
    /// and queries build EXACTLY the former log's forest: after every step the same recorded entries
    /// and the same parent reference for every node, and the same answer to every query, so
    /// every compression in between happened alike. The counts check that rollbacks undid completed
    /// unions whose child is the left node, the right node, and a node deeper on either path, which
    /// are the three cases the stamp search distinguishes.
    /// </summary>
    [Fact]
    public void TentativeLog_RandomSequences_BuildTheFormerLogsForest_NodeForNode()
    {
        long tentativeUnions = 0, lateCompletions = 0, rollbacks = 0, commits = 0;
        long childIsLeft = 0, childIsRight = 0, childDeeper = 0, openUndone = 0;
        for (var seed = 1; seed <= 300; seed++)
        {
            var random = new Random(seed);
            var nodes = DistinctNodes(random.Next(4, 120));
            var classes = new ReferenceClasses();
            var model = new ThirtyTwoByteLogReferenceClasses();
            var open = new List<(int Union, int Left, int Right)>();

            for (var step = 0; step < 300; step++)
            {
                var (i, j) = (random.Next(nodes.Length), random.Next(nodes.Length));
                switch (random.Next(14))
                {
                    case < 2 when model.Log.Count == 0:
                        Assert.Equal(model.Union(nodes[i], nodes[j]), classes.Union(nodes[i], nodes[j]));
                        break;

                    case < 7:
                    {
                        var union = classes.UnionTentatively(nodes[i], nodes[j]);
                        Assert.Equal(model.UnionTentatively(nodes[i], nodes[j]), union);
                        if (union == ReferenceClasses.NoUnion)
                            break;
                        tentativeUnions++;
                        if (random.Next(4) == 0)
                        {
                            // Completed at once, as a level that is entered wide and descends.
                            classes.MarkCompleted(union, nodes[i], nodes[j]);
                            model.MarkCompleted(union);
                        }
                        else
                        {
                            open.Add((union, i, j));
                        }

                        break;
                    }

                    case < 10 when open.Count != 0:
                    {
                        // A later completion of any open union, after other links were made.
                        var at = random.Next(open.Count);
                        var (union, left, right) = open[at];
                        open.RemoveAt(at);
                        classes.MarkCompleted(union, nodes[left], nodes[right]);
                        model.MarkCompleted(union);
                        lateCompletions++;
                        break;
                    }

                    case 10:
                        classes.Commit();
                        model.Commit();
                        open.Clear();
                        commits++;
                        break;

                    case 11:
                        foreach (var union in model.Log)
                        {
                            if (!union.Completed)
                                openUndone++;
                            else if (ReferenceEquals(union.Child, union.Left))
                                childIsLeft++;
                            else if (ReferenceEquals(union.Child, union.Right))
                                childIsRight++;
                            else
                                childDeeper++;
                        }

                        classes.Rollback();
                        model.Rollback();
                        open.Clear();
                        rollbacks++;
                        break;

                    default:
                    {
                        var (x, y) = (nodes[random.Next(nodes.Length)], nodes[random.Next(nodes.Length)]);
                        Assert.Equal(model.Same(x, y), classes.Same(x, y));
                        break;
                    }
                }

                Assert.True(model.RecordedReferences == classes.RecordedReferences, $"seed {seed} step {step}: entries");
                for (var n = 0; n < nodes.Length; n++)
                {
                    var expected = model.TryGetRecordedParent(nodes[n], out var expectedParent);
                    var actual = classes.TryGetRecordedParent(nodes[n], out var actualParent);
                    if (expected != actual || !ReferenceEquals(expectedParent, actualParent))
                        Assert.Fail($"seed {seed} step {step}: recorded parent of node {n}");
                }
            }

            for (var left = 0; left < nodes.Length; left++)
            {
                for (var right = 0; right < nodes.Length; right++)
                    Assert.True(model.Same(nodes[left], nodes[right]) == classes.Same(nodes[left], nodes[right]), $"seed {seed}: {left} ~ {right}");
            }
        }

        // Seeds 1–300 reach about twice each floor (19,007 tentative unions, 5,754 late completions, 6,418
        // commits, 6,383 rollbacks; completed children undone 1,933 left, 1,940 right, 1,067 deeper; 4,156 open).
        Assert.True(tentativeUnions >= 9_000, $"tentative unions: {tentativeUnions}");
        Assert.True(lateCompletions >= 2_800, $"late completions: {lateCompletions}");
        Assert.True(commits >= 3_000 && rollbacks >= 3_000, $"commits {commits}, rollbacks {rollbacks}");
        Assert.True(childIsLeft >= 950 && childIsRight >= 950 && childDeeper >= 500 && openUndone >= 2_000,
            $"completed children undone: left {childIsLeft}, right {childIsRight}, deeper {childDeeper}; open {openUndone}");
    }
}
