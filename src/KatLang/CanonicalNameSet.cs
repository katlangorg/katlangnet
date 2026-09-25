using System.Numerics;

namespace KatLang;

/// <summary>
/// A CONTENT-CANONICAL set of names, interned by a <see cref="NameSetInterner"/>: two sets with the
/// same content are the same node and carry the same <see cref="Id"/>, whatever order or grouping
/// their names were added in. Front-end semantic-region keys compare this one integer where they
/// used to sort, join, and hash every name in scope (FE-1), so extending a wide context by a few
/// names costs the names added, never the names already in scope. Identity is exact — structural
/// equality of canonical tries — never a hash of the content. Ids are meaningful only within the
/// interner that built the set. A set is IMMUTABLE once built: its <see cref="Count"/> and
/// <see cref="Names"/> may be read from any thread after the building run has finished.
/// </summary>
internal readonly struct CanonicalNameSet : IEquatable<CanonicalNameSet>
{
    internal CanonicalNameSet(NameSetInterner.Node? root) => Root = root;

    internal NameSetInterner.Node? Root { get; }

    /// <summary>The set's content identity within its interner; 0 for the empty set.</summary>
    public int Id => Root?.Id ?? 0;

    /// <summary>The number of names in the set.</summary>
    public int Count => Root?.Count ?? 0;

    /// <summary>The set's names, in key order (an order the interner chose; callers must not depend on it).</summary>
    public IEnumerable<string> Names => NameSetInterner.EnumerateNames(Root);

    public bool Equals(CanonicalNameSet other) => ReferenceEquals(Root, other.Root);

    public override bool Equals(object? obj) => obj is CanonicalNameSet other && Equals(other);

    public override int GetHashCode() => Id;
}

/// <summary>
/// Run-local interner of <see cref="CanonicalNameSet"/>s (FE-1): each name gets a dense integer key,
/// and every set is the HASH-CONSED big-endian Patricia trie of its keys. A big-endian Patricia trie
/// is unique for its key set (each branch splits on the highest bit its keys differ in), and every
/// node is built through one table keyed by its exact structure, so equal content is always the
/// SAME node — the property that lets a region memo keep exact content-canonical identity while
/// comparing one reference. Adding d names to a set rebuilds only the paths the new keys touch:
/// O(d × 31) nodes, however large the set already is. <see cref="Union(CanonicalNameSet, CanonicalNameSet)"/>
/// and <see cref="Except(CanonicalNameSet, CanonicalNameSet)"/> memoize every branch pair they combine (a pure function of two canonical nodes), so combining a
/// context that differs from an already combined one by a few names re-walks only the paths those
/// names touch. Never static or ambient: one interner serves one pass run, and is garbage afterwards
/// except for the immutable sets a run hands out.
/// </summary>
internal sealed class NameSetInterner(FrontEndTraversalObservations? observations = null)
{
    internal abstract class Node(int id, int count)
    {
        /// <summary>Unique per canonical node of this interner (positive).</summary>
        public int Id { get; } = id;

        /// <summary>The number of names below this node.</summary>
        public int Count { get; } = count;
    }

    private sealed class Leaf(int id, int key, string name) : Node(id, 1)
    {
        public int Key { get; } = key;

        public string Name { get; } = name;
    }

    private sealed class Branch(int id, int prefix, int bit, Node left, Node right) : Node(id, left.Count + right.Count)
    {
        /// <summary>The key bits above <see cref="Bit"/> that every key below this node shares.</summary>
        public int Prefix { get; } = prefix;

        /// <summary>The single bit the two halves differ in: clear on the left, set on the right.</summary>
        public int Bit { get; } = bit;

        public Node Left { get; } = left;

        public Node Right { get; } = right;
    }

    private readonly Dictionary<string, int> _keys = new(StringComparer.Ordinal);
    private readonly List<Leaf> _leaves = [];
    private readonly Dictionary<(int Prefix, int Bit, int Left, int Right), Branch> _branches = [];
    private readonly Dictionary<(int Lower, int Upper), Node> _unions = [];
    private readonly Dictionary<(int First, int Second), Node?> _differences = [];
    private int _lastNodeId;

    /// <summary>The empty set.</summary>
    public static CanonicalNameSet Empty => default;

    /// <summary>
    /// <paramref name="set"/> with <paramref name="names"/> added. Names already present change
    /// nothing, and the result is the canonical node of the combined content.
    /// </summary>
    public CanonicalNameSet With(CanonicalNameSet set, IEnumerable<string> names)
    {
        List<int>? keys = null;
        foreach (var name in names)
        {
            observations?.RecordContextNameCanonicalized();
            (keys ??= []).Add(KeyOf(name));
        }

        if (keys is null)
            return set;

        keys.Sort();
        var distinct = 1;
        for (var index = 1; index < keys.Count; index++)
        {
            if (keys[index] != keys[distinct - 1])
                keys[distinct++] = keys[index];
        }

        return new CanonicalNameSet(Union(set.Root, Build(keys, 0, distinct - 1)));
    }

    /// <summary>The canonical set of the names in <paramref name="first"/> or <paramref name="second"/>.</summary>
    public CanonicalNameSet Union(CanonicalNameSet first, CanonicalNameSet second)
        => new(Union(first.Root, second.Root));

    /// <summary>The canonical set of the names in <paramref name="first"/> but not in <paramref name="second"/>.</summary>
    public CanonicalNameSet Except(CanonicalNameSet first, CanonicalNameSet second)
        => new(Except(first.Root, second.Root));

    /// <summary>Whether <paramref name="name"/> belongs to <paramref name="set"/>.</summary>
    public bool Contains(CanonicalNameSet set, string name)
        => set.Root is not null && _keys.TryGetValue(name, out var key) && ContainsKey(set.Root, key);

    /// <summary>The names below <paramref name="root"/>; reads only immutable nodes.</summary>
    internal static IEnumerable<string> EnumerateNames(Node? root)
    {
        if (root is null)
            yield break;

        var pending = new Stack<Node>();
        pending.Push(root);
        while (pending.TryPop(out var node))
        {
            if (node is Branch branch)
            {
                pending.Push(branch.Right);
                pending.Push(branch.Left);
            }
            else
            {
                yield return ((Leaf)node).Name;
            }
        }
    }

    private int KeyOf(string name)
    {
        if (_keys.TryGetValue(name, out var key))
            return key;

        key = _keys.Count;
        _keys.Add(name, key);
        _leaves.Add(new Leaf(++_lastNodeId, key, name));
        return key;
    }

    // ── Canonical big-endian Patricia trie over non-negative keys ─────────────────

    private static int HighestBit(int value) => 1 << (31 - BitOperations.LeadingZeroCount((uint)value));

    // The key's bits ABOVE `bit` (`bit` and everything below it cleared).
    private static int PrefixAbove(int key, int bit) => key & ~(bit | (bit - 1));

    private static bool MatchesPrefix(int key, int prefix, int bit) => PrefixAbove(key, bit) == prefix;

    private static bool IsClear(int key, int bit) => (key & bit) == 0;

    private static bool ContainsKey(Node node, int key)
    {
        while (node is Branch branch)
        {
            if (!MatchesPrefix(key, branch.Prefix, branch.Bit))
                return false;
            node = IsClear(key, branch.Bit) ? branch.Left : branch.Right;
        }

        return ((Leaf)node).Key == key;
    }

    private Node MakeBranch(int prefix, int bit, Node left, Node right)
    {
        var structure = (prefix, bit, left.Id, right.Id);
        if (!_branches.TryGetValue(structure, out var branch))
        {
            branch = new Branch(++_lastNodeId, prefix, bit, left, right);
            _branches.Add(structure, branch);
        }

        return branch;
    }

    // A branch that lost every key on one side IS the other side: that subtrie is already the
    // canonical trie of the remaining keys, and a branch keeping both sides keeps its split.
    private Node? Collapse(int prefix, int bit, Node? left, Node? right)
    {
        if (left is null)
            return right;
        if (right is null)
            return left;
        return MakeBranch(prefix, bit, left, right);
    }

    // Joins two non-empty tries whose representative keys differ above both tries' own splits.
    private Node Join(int key0, Node node0, int key1, Node node1)
    {
        var bit = HighestBit(key0 ^ key1);
        var prefix = PrefixAbove(key0, bit);
        return IsClear(key0, bit)
            ? MakeBranch(prefix, bit, node0, node1)
            : MakeBranch(prefix, bit, node1, node0);
    }

    private Node Insert(Node node, int key)
    {
        switch (node)
        {
            case Leaf leaf:
                return leaf.Key == key ? leaf : Join(key, _leaves[key], leaf.Key, leaf);

            case Branch branch when MatchesPrefix(key, branch.Prefix, branch.Bit):
                if (IsClear(key, branch.Bit))
                {
                    var left = Insert(branch.Left, key);
                    return ReferenceEquals(left, branch.Left) ? branch : MakeBranch(branch.Prefix, branch.Bit, left, branch.Right);
                }
                else
                {
                    var right = Insert(branch.Right, key);
                    return ReferenceEquals(right, branch.Right) ? branch : MakeBranch(branch.Prefix, branch.Bit, branch.Left, right);
                }

            case Branch branch:
                return Join(key, _leaves[key], branch.Prefix, branch);

            default:
                throw new InvalidOperationException($"Unhandled name-set node {node.GetType().Name}.");
        }
    }

    private Node? Remove(Node node, int key)
    {
        switch (node)
        {
            case Leaf leaf:
                return leaf.Key == key ? null : leaf;

            case Branch branch when MatchesPrefix(key, branch.Prefix, branch.Bit):
                if (IsClear(key, branch.Bit))
                {
                    var left = Remove(branch.Left, key);
                    return ReferenceEquals(left, branch.Left) ? branch : Collapse(branch.Prefix, branch.Bit, left, branch.Right);
                }
                else
                {
                    var right = Remove(branch.Right, key);
                    return ReferenceEquals(right, branch.Right) ? branch : Collapse(branch.Prefix, branch.Bit, branch.Left, right);
                }

            case Branch branch:
                return branch;

            default:
                throw new InvalidOperationException($"Unhandled name-set node {node.GetType().Name}.");
        }
    }

    private Node? Union(Node? first, Node? second)
    {
        if (first is null)
            return second;
        if (second is null || ReferenceEquals(first, second))
            return first;
        if (first is Leaf firstLeaf)
            return Insert(second, firstLeaf.Key);
        if (second is Leaf secondLeaf)
            return Insert(first, secondLeaf.Key);

        var a = (Branch)first;
        var b = (Branch)second;
        var pair = a.Id < b.Id ? (a.Id, b.Id) : (b.Id, a.Id);
        if (_unions.TryGetValue(pair, out var known))
            return known;

        observations?.RecordNameSetOperationStep();
        Node result;
        if (a.Bit == b.Bit && a.Prefix == b.Prefix)
        {
            result = MakeBranch(a.Prefix, a.Bit, Union(a.Left, b.Left)!, Union(a.Right, b.Right)!);
        }
        // A higher branching bit covers a wider key range: the other trie lies wholly on one side.
        else if (a.Bit > b.Bit && MatchesPrefix(b.Prefix, a.Prefix, a.Bit))
        {
            result = IsClear(b.Prefix, a.Bit)
                ? MakeBranch(a.Prefix, a.Bit, Union(a.Left, b)!, a.Right)
                : MakeBranch(a.Prefix, a.Bit, a.Left, Union(a.Right, b)!);
        }
        else if (b.Bit > a.Bit && MatchesPrefix(a.Prefix, b.Prefix, b.Bit))
        {
            result = IsClear(a.Prefix, b.Bit)
                ? MakeBranch(b.Prefix, b.Bit, Union(a, b.Left)!, b.Right)
                : MakeBranch(b.Prefix, b.Bit, b.Left, Union(a, b.Right)!);
        }
        else
        {
            result = Join(a.Prefix, a, b.Prefix, b);
        }

        _unions.Add(pair, result);
        return result;
    }

    private Node? Except(Node? first, Node? second)
    {
        if (first is null || second is null)
            return first;
        if (ReferenceEquals(first, second))
            return null;
        if (first is Leaf firstLeaf)
            return ContainsKey(second, firstLeaf.Key) ? null : first;
        if (second is Leaf secondLeaf)
            return Remove(first, secondLeaf.Key);

        var a = (Branch)first;
        var b = (Branch)second;
        if (_differences.TryGetValue((a.Id, b.Id), out var known))
            return known;

        observations?.RecordNameSetOperationStep();
        Node? result;
        if (a.Bit == b.Bit && a.Prefix == b.Prefix)
        {
            result = Collapse(a.Prefix, a.Bit, Except(a.Left, b.Left), Except(a.Right, b.Right));
        }
        // The removed trie lies wholly on one side of the wider one.
        else if (a.Bit > b.Bit && MatchesPrefix(b.Prefix, a.Prefix, a.Bit))
        {
            result = IsClear(b.Prefix, a.Bit)
                ? Collapse(a.Prefix, a.Bit, Except(a.Left, b), a.Right)
                : Collapse(a.Prefix, a.Bit, a.Left, Except(a.Right, b));
        }
        // Only the side of the removed trie that covers this trie's keys can remove any of them.
        else if (b.Bit > a.Bit && MatchesPrefix(a.Prefix, b.Prefix, b.Bit))
        {
            result = Except(a, IsClear(a.Prefix, b.Bit) ? b.Left : b.Right);
        }
        else
        {
            // Disjoint key ranges: nothing to remove.
            result = a;
        }

        _differences.Add((a.Id, b.Id), result);
        return result;
    }

    // The canonical trie of sorted DISTINCT keys[low..high]: every key between the extremes shares
    // their bits above the highest bit the extremes differ in, which is this node's split.
    private Node Build(List<int> keys, int low, int high)
    {
        if (low == high)
            return _leaves[keys[low]];

        var bit = HighestBit(keys[low] ^ keys[high]);
        var split = low + 1;
        var end = high;
        while (split < end)
        {
            var middle = split + ((end - split) >> 1);
            if (IsClear(keys[middle], bit))
                split = middle + 1;
            else
                end = middle;
        }

        return MakeBranch(PrefixAbove(keys[low], bit), bit, Build(keys, low, split - 1), Build(keys, split, high));
    }
}
