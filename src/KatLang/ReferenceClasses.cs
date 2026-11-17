using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace KatLang;

/// <summary>
/// Equivalence classes of <see cref="Result"/> REFERENCES — the union–find memo of every structural
/// equality walk of <see cref="Result.ValueSemanticComparer"/>: the evaluator's single-comparison
/// walk and operation walk, and the per-call walk of the context-free <see cref="Result.ValueComparer"/>.
/// Two references in one class are already known equal,
/// so a walk skips any pair whose references share a class: the Hopcroft–Karp equivalence check.
/// An exact-pair memo cannot do that, and two equal DAGs whose sharing does not correspond node
/// to node reach about |A|·|B| distinct pairs. Classes need at most one entry per distinct node reached,
/// and a node joins a class at most once per merge, so memory is O(distinct nodes reached) and the
/// expansion count stays linear. Find costs depend on the link rule described below. This type
/// keeps both layers below and serves the operation walk; the two walks whose memo dies with one
/// comparison use <see cref="CommittedReferenceClasses"/>, the same classes with the committed layer
/// only.
///
/// <para>Identity is <see cref="ReferenceEqualityComparer"/>: the memo never calls value equality or a
/// structural hash, which would re-enter the walks it bounds. <see cref="Find"/> on a node it has never
/// recorded returns the node itself without allocating. Path compression on the COMMITTED layer.</para>
///
/// <para>ONE ENTRY PER UNION. A union records only the node it links BELOW another one: a
/// representative needs no entry, so a node absent from the table is the representative of its
/// class whatever the class's size, and the first union of two fresh nodes records one entry, not
/// two. That needs a link rule that reads nothing stored about a class: LINKING BY INDEX
/// (<see cref="LinksBelow"/>), where the representative with the lower index goes below the other
/// and a node's index is a fixed avalanche mix of its runtime identity hash. The mix disperses
/// correlated hash bits; it does not make the indices independent or collision-free. Balance is
/// a measured heuristic, not a runtime guarantee. UNDER THE MODEL of a uniformly random node order
/// independent of the union sequence, a node's expected depth in a class of n nodes is at most
/// ln n: when its class S merges with T, its representative goes below the other with probability
/// |T| / (|S| + |T|) ≤ ln(|S ∪ T| / |S|), and the terms telescope. Goel, Khanna, Larkin and Tarjan,
/// SODA 2014, prove the near-constant amortized bound with path compression under that model too.
/// Runtime identity hashes need not satisfy the model: collision-heavy or hash-ordered inputs can
/// produce long paths, especially in the uncompressed tentative layer. The linear bound on expanded
/// pairs and entries is independent of this balance assumption. Union by size gave logarithmic
/// depth deterministically, but it must store every representative's size, so a first union of two
/// fresh nodes cost two entries. Which
/// node represents a class decides nothing a walk observes: <see cref="Same"/> answers class
/// membership only. Identity hashes can collide; equal indices put the right representative below
/// the left one.</para>
///
/// <para>TWO LAYERS. <see cref="Union"/> links COMMITTED classes. <see cref="UnionTentatively"/>
/// links two committed or tentative roots in the TENTATIVE layer of the running walk. Each tentative
/// link is logged and stamped with the current generation. <see cref="Commit"/> keeps every
/// tentative link. <see cref="Rollback"/> undoes them in reverse and then re-links, as committed,
/// exactly the pairs marked COMPLETED (<see cref="MarkCompleted"/>). Path compression never rewrites
/// a tentative link: a node's committed path is compressed only up to its committed root, the first
/// node on its path whose own link is tentative. So the undo restores the committed forest exactly.
/// An undone link leaves its entry behind as a representative's (no parent), so a later link of
/// the same node reuses it.</para>
///
/// <para>Never static, never shared between operations, runs or threads, and never attached to a
/// <see cref="Result"/>. It dies with the walk or operation that owns it.</para>
/// </summary>
internal sealed class ReferenceClasses
{
    /// <summary>No tentative union: the pair was already one class, or the level recorded nothing.</summary>
    internal const int NoUnion = -1;

    private readonly Dictionary<Result, Entry> entries = new(ReferenceEqualityComparer.Instance);
    private List<TentativeUnion>? tentative;

    /// <summary>
    /// The stamp of the running walk's tentative links. Committed links carry 0, and every
    /// <see cref="Commit"/> or <see cref="Rollback"/> advances it, so an older stamp reads as committed.
    /// </summary>
    private int generation = 1;

    private struct Entry
    {
        /// <summary>
        /// The parent reference, or <c>null</c> for a class representative: a node whose link
        /// <see cref="Rollback"/> undid.
        /// </summary>
        internal Result? Parent;

        /// <summary>The generation of the tentative link to <see cref="Parent"/>, or 0 for a committed link.</summary>
        internal int Generation;
    }

    private struct TentativeUnion
    {
        internal Result Left;
        internal Result Right;

        /// <summary>The representative the link attached below another one: the link to undo.</summary>
        internal Result Child;

        internal bool Completed;
    }

    /// <summary>The recorded references: one per node ever linked below another one (for tests).</summary>
    internal int RecordedReferences => entries.Count;

    /// <summary>
    /// The links from <paramref name="node"/> up to its representative, read without compressing
    /// anything (for tests).
    /// </summary>
    internal int PathLength(Result node)
    {
        var length = 0;
        for (var current = node; entries.TryGetValue(current, out var entry) && entry.Parent is { } parent; current = parent)
            length++;
        return length;
    }

    /// <summary>Whether <paramref name="left"/> and <paramref name="right"/> are in one class.</summary>
    internal bool Same(Result left, Result right) => ReferenceEquals(Find(left), Find(right));

    /// <summary>
    /// Merges the committed classes of <paramref name="left"/> and <paramref name="right"/>. Returns
    /// <c>false</c> when they were one class already. Only valid while no tentative link exists.
    /// </summary>
    internal bool Union(Result left, Result right)
    {
        Debug.Assert(tentative is not { Count: not 0 }, "A committed union while tentative links exist.");
        return Link(left, right, tentatively: false, out _);
    }

    /// <summary>
    /// Merges the classes of <paramref name="left"/> and <paramref name="right"/> in the tentative
    /// layer. Returns the union's index for <see cref="MarkCompleted"/>, or <see cref="NoUnion"/> when
    /// they were one class already.
    /// </summary>
    internal int UnionTentatively(Result left, Result right)
    {
        if (!Link(left, right, tentatively: true, out var child))
            return NoUnion;
        (tentative ??= []).Add(new TentativeUnion { Left = left, Right = right, Child = child });
        return tentative.Count - 1;
    }

    /// <summary>Records that the walk COMPLETED the pair of tentative union <paramref name="union"/>.</summary>
    internal void MarkCompleted(int union) => CollectionsMarshal.AsSpan(tentative)[union].Completed = true;

    /// <summary>Keeps every tentative link: the walk that made them decided its pair EQUAL.</summary>
    internal void Commit()
    {
        if (tentative is not { Count: not 0 })
            return;
        tentative.Clear();
        generation++;
    }

    /// <summary>
    /// Undoes every tentative link, newest first, then re-links as committed the pairs whose
    /// levels COMPLETED. The walk that made them decided its pair UNEQUAL, and only its OPEN levels
    /// were assumed equal (see <c>Result.ValueSemanticComparer.EqualsInOperationWalk</c>).
    /// </summary>
    internal void Rollback()
    {
        if (tentative is not { Count: not 0 })
            return;

        var log = CollectionsMarshal.AsSpan(tentative);
        for (var i = log.Length - 1; i >= 0; i--)
        {
            // Undone newest first: later links have been undone, and compression never rewrites a
            // tentative link, so the child's entry still holds exactly this link. Nothing is stored
            // about the parent, so nothing else needs restoring.
            ref var child = ref CollectionsMarshal.GetValueRefOrNullRef(entries, log[i].Child);
            child.Parent = null;
            child.Generation = 0;
        }

        generation++;
        foreach (ref readonly var union in log)
        {
            if (union.Completed)
                _ = Link(union.Left, union.Right, tentatively: false, out _);
        }

        tentative.Clear();
    }

    /// <summary>
    /// The representative of <paramref name="node"/>'s class: <paramref name="node"/> itself when it
    /// was never recorded. Every node on the committed part of its path is relinked to the committed
    /// root.
    /// </summary>
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
            // Path compression of the committed segment only (see the class remarks).
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

        // Linking by index (see the class remarks). The child's link is the one entry the union
        // records; the parent stays as it was, recorded or not.
        Result parent;
        (child, parent) = LinksBelow(leftRoot, rightRoot) ? (leftRoot, rightRoot) : (rightRoot, leftRoot);
        ref var entry = ref CollectionsMarshal.GetValueRefOrAddDefault(entries, child, out _);
        entry.Parent = parent;
        entry.Generation = tentatively ? generation : 0;
        return true;
    }

    /// <summary>
    /// The link rule of both forms of the classes: whether the representative <paramref name="left"/>
    /// goes below the representative <paramref name="right"/> when their classes merge. Linking by
    /// index (see the class remarks); on equal indices the right one goes below.
    /// </summary>
    internal static bool LinksBelow(Result left, Result right) => Index(left) < Index(right);

    /// <summary>
    /// A node's link index: the murmur3 finalizer of its runtime identity hash, the hash every
    /// lookup of the table already computes. A bijection on 32 bits, so it adds no collision.
    /// </summary>
    private static uint Index(Result node)
    {
        var index = (uint)RuntimeHelpers.GetHashCode(node);
        index ^= index >> 16;
        index *= 0x85EBCA6B;
        index ^= index >> 13;
        index *= 0xC2B2AE35;
        index ^= index >> 16;
        return index;
    }
}

/// <summary>
/// <see cref="ReferenceClasses"/> with the COMMITTED layer only, for a walk whose memo dies with ONE
/// comparison and never undoes a union: the evaluator's single-comparison walk
/// (<c>Result.ValueSemanticComparer.EqualsSingleWalk</c>) and the per-call walk of the context-free
/// <see cref="Result.ValueComparer"/>. The same classes, the same link rule
/// (<see cref="ReferenceClasses.LinksBelow"/>) and the same path compression. With no tentative link
/// to stamp, an entry is the parent reference alone, so a union records one 24-byte table entry —
/// what one exact ordered pair cost the exact-pair memo it replaced — instead of the 32 bytes of a
/// stamped link. A representative is never recorded, because no link is ever undone.
///
/// <para>Never static, never shared between comparisons, runs or threads, and never attached to a
/// <see cref="Result"/>. It dies with the comparison that owns it.</para>
/// </summary>
internal sealed class CommittedReferenceClasses
{
    private readonly Dictionary<Result, Result> parents = new(ReferenceEqualityComparer.Instance);

    /// <summary>The recorded references: one per union (for tests).</summary>
    internal int RecordedReferences => parents.Count;

    /// <summary>Whether <paramref name="left"/> and <paramref name="right"/> are in one class.</summary>
    internal bool Same(Result left, Result right) => ReferenceEquals(Find(left), Find(right));

    /// <summary>
    /// Merges the classes of <paramref name="left"/> and <paramref name="right"/>. Returns
    /// <c>false</c> when they were one class already.
    /// </summary>
    internal bool Union(Result left, Result right)
    {
        var leftRoot = Find(left);
        var rightRoot = Find(right);
        if (ReferenceEquals(leftRoot, rightRoot))
            return false;

        // A representative has no entry, so this adds the union's one entry (and throws, rather than
        // silently relinking, were that ever not so).
        if (ReferenceClasses.LinksBelow(leftRoot, rightRoot))
            parents.Add(leftRoot, rightRoot);
        else
            parents.Add(rightRoot, leftRoot);
        return true;
    }

    /// <summary>
    /// The representative of <paramref name="node"/>'s class: <paramref name="node"/> itself when it
    /// was never recorded. Every node on its path is relinked to the representative.
    /// </summary>
    private Result Find(Result node)
    {
        var root = node;
        var links = 0;
        while (parents.TryGetValue(root, out var parent))
        {
            root = parent;
            links++;
        }

        if (links > 1)
        {
            var compressed = node;
            while (!ReferenceEquals(compressed, root))
            {
                ref var link = ref CollectionsMarshal.GetValueRefOrNullRef(parents, compressed);
                var parent = link;
                link = root;
                compressed = parent;
            }
        }

        return root;
    }
}
