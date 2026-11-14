using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace KatLang;

/// <summary>
/// Equivalence classes of <see cref="Result"/> REFERENCES — the union–find memo of the evaluator's
/// structural equality walks (the single-comparison walk and the operation walk of
/// <see cref="Result.ValueSemanticComparer"/>). Two references in one class are already known equal,
/// so a walk skips any pair whose references share a class: the Hopcroft–Karp equivalence check.
/// An exact-pair memo cannot do that, and two equal DAGs whose sharing does not correspond node
/// to node reach about |A|·|B| distinct pairs. Classes need one entry per distinct node reached,
/// and a node joins a class at most once per merge, so memory is O(distinct nodes reached) and the
/// work is near-linear.
///
/// <para>Identity is <see cref="ReferenceEqualityComparer"/>: the memo never calls value equality or a
/// structural hash, which would re-enter the walks it bounds. <see cref="Find"/> on a node it has never
/// recorded returns the node itself without allocating. Union by size; path compression on the
/// COMMITTED layer.</para>
///
/// <para>TWO LAYERS. <see cref="Union"/> links COMMITTED classes. <see cref="UnionTentatively"/>
/// links two committed or tentative roots in the TENTATIVE layer of the running walk. Each tentative
/// link is logged and stamped with the current generation. <see cref="Commit"/> keeps every
/// tentative link. <see cref="Rollback"/> undoes them in reverse and then re-links, as committed,
/// exactly the pairs marked COMPLETED (<see cref="MarkCompleted"/>). Path compression never rewrites
/// a tentative link: a node's committed path is compressed only up to its committed root, the first
/// node on its path whose own link is tentative. So the undo restores the committed forest exactly.
/// The single-comparison walk discards its memo with the comparison and uses the committed layer
/// only.</para>
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
        /// <summary>The parent reference, or <c>null</c> for a class representative.</summary>
        internal Result? Parent;

        /// <summary>The number of recorded references in the class; read only at a representative.</summary>
        internal int Size;

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
            // Undone newest first, so the child is still the parent's direct child and the parent
            // a representative: later links and compressions have been undone or never touched it.
            ref var child = ref CollectionsMarshal.GetValueRefOrNullRef(entries, log[i].Child);
            ref var parent = ref CollectionsMarshal.GetValueRefOrNullRef(entries, child.Parent!);
            parent.Size -= child.Size;
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

        // Both representatives get an entry. Adding the second may resize the table, so the first
        // reference is read again after it.
        ref var leftEntry = ref CollectionsMarshal.GetValueRefOrAddDefault(entries, leftRoot, out var leftExists);
        if (!leftExists)
            leftEntry.Size = 1;
        ref var rightEntry = ref CollectionsMarshal.GetValueRefOrAddDefault(entries, rightRoot, out var rightExists);
        if (!rightExists)
        {
            rightEntry.Size = 1;
            leftEntry = ref CollectionsMarshal.GetValueRefOrNullRef(entries, leftRoot);
        }

        // Union by size: the smaller class goes below the larger one (the right one on a tie).
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
