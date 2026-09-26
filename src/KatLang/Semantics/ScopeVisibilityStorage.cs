using System.Collections;
using System.Collections.Immutable;
using System.Runtime.CompilerServices;

namespace KatLang.Semantics;

/// <summary>
/// One visible name of a scope's persistent visibility state (FE-4b): the symbol the scope offers,
/// how it was decided, and its tree priority. <see cref="Meta"/> bit 0 marks an OPEN-provided
/// entry; the remaining bits count the deferred-module-owning levels strictly OUTSIDE the level
/// whose open decided it — a reading scope with more such levels (<see cref="ScopeSymbolView"/>)
/// reads the entry's <see cref="DeferredTwin"/> instead (the B2c indeterminate classification),
/// so an enclosing deferred open never forces a per-scope rewrite of inherited entries.
/// </summary>
internal readonly struct VisibilityEntry
{
    public VisibilityEntry(VisibleSymbol symbol, int meta, VisibleSymbol? deferredTwin, int priority)
    {
        Symbol = symbol;
        Meta = meta;
        DeferredTwin = deferredTwin;
        Priority = priority;
    }

    internal VisibilityEntry(VisibilityNode node)
    {
        Symbol = node.Symbol;
        Meta = node.Meta;
        DeferredTwin = node.DeferredTwin;
        Priority = node.Priority;
    }

    public VisibleSymbol Symbol { get; }

    public string Name => Symbol.Name;

    public int Meta { get; }

    public VisibleSymbol? DeferredTwin { get; }

    public int Priority { get; }

    public static int DirectMeta => 0;

    public static int OpenMeta(int outerDeferredLevels) => (outerDeferredLevels << 1) | 1;
}

/// <summary>One pending change of a visibility layer: set a name's entry, or remove the name (open ambiguity).</summary>
internal readonly struct VisibilityDelta
{
    private VisibilityDelta(string name, VisibilityEntry entry, bool isRemoval)
    {
        Name = name;
        Entry = entry;
        IsRemoval = isRemoval;
    }

    public string Name { get; }

    public VisibilityEntry Entry { get; }

    public bool IsRemoval { get; }

    public static VisibilityDelta Set(VisibilityEntry entry) => new(entry.Name, entry, isRemoval: false);

    public static VisibilityDelta Remove(string name) => new(name, default, isRemoval: true);
}

/// <summary>
/// One immutable node of a scope visibility tree (FE-4b): a treap ordered by ORDINAL name — the
/// public <see cref="ScopeVisibility.Symbols"/> order — and heap-ordered by a name-derived
/// priority, with subtree sizes for positional reads. Nodes are hash-consed per build by
/// (entry, left, right) REFERENCE identity (<see cref="VisibilityTreeBuilder"/>): a treap's shape
/// is a function of its key set, so two scopes whose visible contents are identical — however
/// they were derived — share one root object, and a scope that differs from its parent by a few
/// names shares every untouched subtree. A node references only its entry's public symbols and
/// its children: no builder, frame, AST, or interner state.
/// </summary>
internal sealed class VisibilityNode
{
    internal VisibilityNode(in VisibilityEntry entry, VisibilityNode? left, VisibilityNode? right)
    {
        Symbol = entry.Symbol;
        Meta = entry.Meta;
        DeferredTwin = entry.DeferredTwin;
        Priority = entry.Priority;
        Left = left;
        Right = right;
        Count = 1 + (left?.Count ?? 0) + (right?.Count ?? 0);
    }

    public readonly VisibleSymbol Symbol;
    public readonly VisibleSymbol? DeferredTwin;
    public readonly VisibilityNode? Left;
    public readonly VisibilityNode? Right;
    public readonly int Meta;
    public readonly int Priority;
    public readonly int Count;

    public string Name => Symbol.Name;

    public bool IsOpenProvided => (Meta & 1) != 0;

    public int OuterDeferredLevels => Meta >> 1;
}

/// <summary>Read-only queries over visibility trees: ordinal name order, O(tree depth) per query.</summary>
internal static class VisibilityTree
{
    /// <summary>
    /// The treap priority of a name: the runtime's per-process randomized string hash, so the
    /// expected tree depth is logarithmic for inputs independent of the process's hash seed.
    /// This is not a deterministic worst-case bound: a host observing hashes can select an
    /// unbalanced key set. Tied priorities remain correct through the exact name discriminator.
    /// Ties are broken by ordinal name, making the shape a function of the key set alone.
    /// </summary>
    public static int PriorityOf(string? name) => name is null ? int.MinValue : name.GetHashCode();

    public static bool HigherPriority(int leftPriority, string? leftName, int rightPriority, string? rightName)
        => leftPriority != rightPriority
            ? leftPriority > rightPriority
            : string.CompareOrdinal(leftName, rightName) < 0;

    public static VisibilityNode? Find(VisibilityNode? node, string? name)
    {
        while (node is not null)
        {
            var comparison = string.CompareOrdinal(name, node.Name);
            if (comparison == 0)
                return node;
            node = comparison < 0 ? node.Left : node.Right;
        }

        return null;
    }

    /// <summary>The node for <paramref name="name"/> and its in-order position, counting the nodes visited.</summary>
    public static VisibilityNode? Find(VisibilityNode? node, string? name, out int index, out int probes)
    {
        index = 0;
        probes = 0;
        while (node is not null)
        {
            probes++;
            var comparison = string.CompareOrdinal(name, node.Name);
            if (comparison == 0)
            {
                index += node.Left?.Count ?? 0;
                return node;
            }

            if (comparison < 0)
            {
                node = node.Left;
            }
            else
            {
                index += (node.Left?.Count ?? 0) + 1;
                node = node.Right;
            }
        }

        index = -1;
        return null;
    }

    public static VisibilityNode ElementAt(VisibilityNode root, int index)
    {
        var node = root;
        while (true)
        {
            var leftCount = node.Left?.Count ?? 0;
            if (index < leftCount)
            {
                node = node.Left!;
            }
            else if (index == leftCount)
            {
                return node;
            }
            else
            {
                index -= leftCount + 1;
                node = node.Right!;
            }
        }
    }

    /// <summary>In-order (ordinal name) traversal with an explicit stack; allocation is one stack of tree depth.</summary>
    public static IEnumerable<VisibilityNode> InOrder(VisibilityNode? root)
    {
        var stack = new Stack<VisibilityNode>();
        var node = root;
        while (node is not null || stack.Count > 0)
        {
            while (node is not null)
            {
                stack.Push(node);
                node = node.Left;
            }

            node = stack.Pop();
            yield return node;
            node = node.Right;
        }
    }
}

/// <summary>
/// The per-build constructor of visibility trees (FE-4b). Every node is created through
/// <see cref="Make"/>, which interns it by (symbol, deferred twin, meta, left, right) reference identity —
/// equality compares every component, the hash only selects a bucket, so colliding hashes never
/// merge distinct nodes. Because a treap's shape depends only on its keys, the incremental path
/// (<see cref="Set"/> / <see cref="Remove"/>, O(depth) nodes per change) and the bulk path
/// (<see cref="Build"/> over the merged sorted entries, O(size) time) produce the SAME root object
/// for the same content; <see cref="Apply"/> picks between them by size only. The intern table
/// lives exactly as long as one semantic-model build and is never reachable from a node.
/// </summary>
internal sealed class VisibilityTreeBuilder
{
    /// <summary>A layer of at least this many changes, and at least 1/<see cref="BulkDivisor"/> of the tree, is applied by a bulk rebuild.</summary>
    internal const int BulkMinimumChanges = 8;

    internal const int BulkDivisor = 8;

    private readonly Dictionary<NodeKey, VisibilityNode> _nodes = new();
    private readonly FrontEndTraversalObservations? _observations;
    private readonly bool _collideNodeHashes;

    /// <param name="observations">Passive construction counters, or null.</param>
    /// <param name="collideNodeHashes">Test knob: every intern key hashes alike, so only full component equality separates nodes.</param>
    public VisibilityTreeBuilder(FrontEndTraversalObservations? observations, bool collideNodeHashes = false)
    {
        _observations = observations;
        _collideNodeHashes = collideNodeHashes;
    }

    /// <summary>Test knob: force every layer onto the bulk (true) or incremental (false) path. Content never depends on it.</summary>
    internal bool? ForceBulk { get; init; }

    /// <summary>
    /// Test knob: the priority function (default <see cref="VisibilityTree.PriorityOf"/>). A constant
    /// makes every comparison a name tie-break — a degenerate but valid treap — so content and
    /// order never depend on the hash, only depth does.
    /// </summary>
    internal Func<string?, int>? PriorityOverride { get; init; }

    /// <summary>An entry of this builder's trees, prioritized by its name.</summary>
    public VisibilityEntry Entry(VisibleSymbol symbol, int meta, VisibleSymbol? deferredTwin)
        => new(symbol, meta, deferredTwin, PriorityOverride is { } priority ? priority(symbol.Name) : VisibilityTree.PriorityOf(symbol.Name));

    public static bool UsesBulkPath(int changes, int size)
        => changes >= BulkMinimumChanges && (long)changes * BulkDivisor >= size;

    /// <summary>
    /// Applies one layer's changes (distinct names). Changes that would leave the tree as it is —
    /// the name already holds exactly that entry, or a removed name is absent — are dropped first
    /// (one lookup each, no allocation), so a re-applied layer costs lookups, never a rebuild; the
    /// remaining changes take the incremental or bulk path by size alone. The result is canonical:
    /// independent of path and change order. <paramref name="changes"/> is filtered in place.
    /// </summary>
    public VisibilityNode? Apply(VisibilityNode? root, List<VisibilityDelta> changes)
    {
        changes.RemoveAll(change => IsNoOp(root, change));
        if (changes.Count == 0)
            return root;

        _observations?.RecordScopeVisibilityLayerChanges(changes.Count);
        if (ForceBulk ?? UsesBulkPath(changes.Count, root?.Count ?? 0))
            return Rebuild(root, changes);

        foreach (var change in changes)
            root = change.IsRemoval ? Remove(root, change.Name) : Set(root, change.Entry);
        return root;
    }

    private static bool IsNoOp(VisibilityNode? root, in VisibilityDelta change)
    {
        var existing = VisibilityTree.Find(root, change.Name);
        return change.IsRemoval
            ? existing is null
            : existing is not null && SameEntry(existing, change.Entry);
    }

    private static bool SameEntry(VisibilityNode node, in VisibilityEntry entry)
        => ReferenceEquals(node.Symbol, entry.Symbol)
            && node.Meta == entry.Meta
            && ReferenceEquals(node.DeferredTwin, entry.DeferredTwin);

    public VisibilityNode Make(in VisibilityEntry entry, VisibilityNode? left, VisibilityNode? right)
    {
        var key = new NodeKey(entry.Symbol, entry.Meta, entry.DeferredTwin, left, right, _collideNodeHashes);
        if (_nodes.TryGetValue(key, out var existing))
        {
            _observations?.RecordScopeVisibilityNodeReused();
            return existing;
        }

        var node = new VisibilityNode(entry, left, right);
        _nodes.Add(key, node);
        _observations?.RecordScopeVisibilityNodeCreated();
        return node;
    }

    /// <summary>Sets the entry for its name (insert or replace), returning the SAME root when nothing changes.</summary>
    public VisibilityNode Set(VisibilityNode? node, in VisibilityEntry entry)
    {
        if (node is null)
            return Make(entry, null, null);

        var comparison = string.CompareOrdinal(entry.Name, node.Name);
        if (comparison == 0)
        {
            return SameEntry(node, entry)
                ? node
                : Make(entry, node.Left, node.Right);
        }

        if (comparison < 0)
        {
            var left = Set(node.Left, entry);
            if (ReferenceEquals(left, node.Left))
                return node;

            // Only the new left root can outrank this node: one rotation restores the heap order.
            return VisibilityTree.HigherPriority(left.Priority, left.Name, node.Priority, node.Name)
                ? Make(new VisibilityEntry(left), left.Left, Make(new VisibilityEntry(node), left.Right, node.Right))
                : Make(new VisibilityEntry(node), left, node.Right);
        }

        var right = Set(node.Right, entry);
        if (ReferenceEquals(right, node.Right))
            return node;

        return VisibilityTree.HigherPriority(right.Priority, right.Name, node.Priority, node.Name)
            ? Make(new VisibilityEntry(right), Make(new VisibilityEntry(node), node.Left, right.Left), right.Right)
            : Make(new VisibilityEntry(node), node.Left, right);
    }

    /// <summary>Removes <paramref name="name"/>, returning the SAME root when it is absent.</summary>
    public VisibilityNode? Remove(VisibilityNode? node, string? name)
    {
        if (node is null)
            return null;

        var comparison = string.CompareOrdinal(name, node.Name);
        if (comparison == 0)
            return Merge(node.Left, node.Right);

        if (comparison < 0)
        {
            var left = Remove(node.Left, name);
            return ReferenceEquals(left, node.Left) ? node : Make(new VisibilityEntry(node), left, node.Right);
        }

        var right = Remove(node.Right, name);
        return ReferenceEquals(right, node.Right) ? node : Make(new VisibilityEntry(node), node.Left, right);
    }

    private VisibilityNode? Merge(VisibilityNode? low, VisibilityNode? high)
    {
        if (low is null)
            return high;
        if (high is null)
            return low;

        return VisibilityTree.HigherPriority(low.Priority, low.Name, high.Priority, high.Name)
            ? Make(new VisibilityEntry(low), low.Left, Merge(low.Right, high))
            : Make(new VisibilityEntry(high), Merge(low, high.Left), high.Right);
    }

    private VisibilityNode? Rebuild(VisibilityNode? root, List<VisibilityDelta> changes)
    {
        changes.Sort(static (left, right) => string.CompareOrdinal(left.Name, right.Name));
        var merged = new List<VisibilityEntry>((root?.Count ?? 0) + changes.Count);
        var next = 0;
        foreach (var node in VisibilityTree.InOrder(root))
        {
            while (next < changes.Count && string.CompareOrdinal(changes[next].Name, node.Name) < 0)
            {
                if (!changes[next].IsRemoval)
                    merged.Add(changes[next].Entry);
                next++;
            }

            if (next < changes.Count && string.CompareOrdinal(changes[next].Name, node.Name) == 0)
            {
                if (!changes[next].IsRemoval)
                    merged.Add(changes[next].Entry);
                next++;
                continue;
            }

            merged.Add(new VisibilityEntry(node));
        }

        for (; next < changes.Count; next++)
        {
            if (!changes[next].IsRemoval)
                merged.Add(changes[next].Entry);
        }

        return Build(merged);
    }

    /// <summary>
    /// The canonical treap over entries sorted by strictly increasing ordinal name: the Cartesian
    /// tree of their priorities (a linear stack pass), built bottom-up through <see cref="Make"/>,
    /// so every subtree whose content is unchanged is the node that already exists.
    /// </summary>
    public VisibilityNode? Build(List<VisibilityEntry> sorted)
    {
        var count = sorted.Count;
        if (count == 0)
            return null;

        _observations?.RecordScopeVisibilityBulkBuild(count);
        var left = new int[count];
        var right = new int[count];
        var spine = new int[count];
        var top = -1;
        for (var i = 0; i < count; i++)
        {
            left[i] = -1;
            right[i] = -1;
            var last = -1;
            while (top >= 0 && VisibilityTree.HigherPriority(sorted[i].Priority, sorted[i].Name, sorted[spine[top]].Priority, sorted[spine[top]].Name))
                last = spine[top--];
            left[i] = last;
            if (top >= 0)
                right[spine[top]] = i;
            spine[++top] = i;
        }

        // Post-order construction with an explicit stack: children before their parent.
        var built = new VisibilityNode?[count];
        var pending = new Stack<(int Index, bool ChildrenDone)>();
        pending.Push((spine[0], false));
        while (pending.TryPop(out var item))
        {
            if (item.ChildrenDone)
            {
                built[item.Index] = Make(
                    sorted[item.Index],
                    left[item.Index] < 0 ? null : built[left[item.Index]],
                    right[item.Index] < 0 ? null : built[right[item.Index]]);
                continue;
            }

            pending.Push((item.Index, true));
            if (right[item.Index] >= 0)
                pending.Push((right[item.Index], false));
            if (left[item.Index] >= 0)
                pending.Push((left[item.Index], false));
        }

        return built[spine[0]];
    }

    /// <summary>
    /// A node's intern identity: its entry symbol, deferred twin, meta, and both children, all compared by
    /// reference/value in <see cref="Equals(NodeKey)"/>; the hash only selects a bucket (and the
    /// test knob makes every key hash alike, so equality alone must separate nodes).
    /// </summary>
    private readonly struct NodeKey(VisibleSymbol symbol, int meta, VisibleSymbol? deferredTwin, VisibilityNode? left, VisibilityNode? right, bool collide) : IEquatable<NodeKey>
    {
        private readonly VisibleSymbol _symbol = symbol;
        private readonly VisibleSymbol? _deferredTwin = deferredTwin;
        private readonly VisibilityNode? _left = left;
        private readonly VisibilityNode? _right = right;
        private readonly int _meta = meta;
        private readonly bool _collide = collide;

        public bool Equals(NodeKey other)
            => ReferenceEquals(_symbol, other._symbol)
                && _meta == other._meta
                && ReferenceEquals(_deferredTwin, other._deferredTwin)
                && ReferenceEquals(_left, other._left)
                && ReferenceEquals(_right, other._right);

        public override bool Equals(object? obj) => obj is NodeKey other && Equals(other);

        public override int GetHashCode()
            => _collide
                ? 42
                : HashCode.Combine(
                    RuntimeHelpers.GetHashCode(_symbol),
                    _meta,
                    _deferredTwin is null ? 0 : RuntimeHelpers.GetHashCode(_deferredTwin),
                    _left is null ? 0 : RuntimeHelpers.GetHashCode(_left),
                    _right is null ? 0 : RuntimeHelpers.GetHashCode(_right));
    }
}

/// <summary>
/// The immutable backing of one scope's <see cref="ScopeVisibility.Symbols"/> (FE-4b): a view over
/// a shared visibility tree plus the scope's deferred-module reading context. The public list is a
/// distinct <see cref="System.Collections.ObjectModel.ReadOnlyCollection{T}"/> wrapper per scope
/// over this view, so storage sharing never merges two scopes' public identities or record
/// equality. Reads are O(tree depth); enumeration is in-order (ordinal name) and allocates only
/// its traversal stack; nothing is materialized, cached, or mutated after construction, so
/// concurrent readers need no synchronization.
/// </summary>
internal sealed class ScopeSymbolView : IList<VisibleSymbol>, IReadOnlyList<VisibleSymbol>
{
    private readonly VisibilityNode? _root;
    private readonly int _deferredLevels;
    private readonly ImmutableHashSet<string>? _syntheticNames;

    internal ScopeSymbolView(VisibilityNode? root, int deferredLevels, ImmutableHashSet<string>? syntheticNames)
    {
        _root = root;
        _deferredLevels = deferredLevels;
        _syntheticNames = syntheticNames is { IsEmpty: false } ? syntheticNames : null;
    }

    internal VisibilityNode? Root => _root;

    internal int DeferredLevels => _deferredLevels;

    public int Count => _root?.Count ?? 0;

    public bool IsReadOnly => true;

    public VisibleSymbol this[int index]
    {
        get
        {
            if ((uint)index >= (uint)Count)
                throw new ArgumentOutOfRangeException(nameof(index));
            return Resolve(VisibilityTree.ElementAt(_root!, index));
        }
        set => throw new NotSupportedException("Scope visibility symbols are read-only.");
    }

    /// <summary>
    /// The symbol this scope offers for a node: its own, or — when an enclosing level at or inside
    /// the deciding open's level opens a DEFERRED module, and no synthetic property of this chain
    /// carries the name — the name's indeterminate twin.
    /// </summary>
    internal VisibleSymbol Resolve(VisibilityNode node)
        => node.DeferredTwin is { } twin
            && _deferredLevels > node.OuterDeferredLevels
            && _syntheticNames?.Contains(node.Name) != true
                ? twin
                : node.Symbol;

    /// <summary>The symbol visible under <paramref name="name"/>, or null (O(tree depth)).</summary>
    internal VisibleSymbol? Find(string? name)
        => VisibilityTree.Find(_root, name) is { } node ? Resolve(node) : null;

    public bool Contains(VisibleSymbol item) => IndexOf(item) >= 0;

    public int IndexOf(VisibleSymbol item)
    {
        if (item is null)
            return -1;

        var node = VisibilityTree.Find(_root, item.Name, out var index, out _);
        return node is not null && EqualityComparer<VisibleSymbol>.Default.Equals(Resolve(node), item) ? index : -1;
    }

    public void CopyTo(VisibleSymbol[] array, int arrayIndex)
    {
        ArgumentNullException.ThrowIfNull(array);
        ArgumentOutOfRangeException.ThrowIfNegative(arrayIndex);
        if (array.Length - arrayIndex < Count)
            throw new ArgumentException("Destination array is not long enough to copy all the items in the collection.", nameof(array));

        using var enumerator = new Enumerator(this);
        while (enumerator.MoveNext())
            array[arrayIndex++] = enumerator.Current;
    }

    public IEnumerator<VisibleSymbol> GetEnumerator() => new Enumerator(this);

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    /// <summary>
    /// In-order traversal over the shared tree with one explicit stack (no nested iterators): O(1)
    /// amortized per element, one small allocation per enumeration, safe under concurrent readers.
    /// </summary>
    private sealed class Enumerator : IEnumerator<VisibleSymbol>
    {
        private readonly ScopeSymbolView _view;
        private VisibilityNode?[] _stack;
        private int _depth;
        private VisibilityNode? _next;
        private VisibleSymbol? _current;

        public Enumerator(ScopeSymbolView view)
        {
            _view = view;
            _stack = new VisibilityNode?[InitialStackCapacity(view.Count)];
            _next = view._root;
        }

        private static int InitialStackCapacity(int count)
            => count == 0 ? 1 : 4 + (2 * (32 - System.Numerics.BitOperations.LeadingZeroCount((uint)count)));

        public VisibleSymbol Current => _current ?? throw new InvalidOperationException("Enumeration has not started or has already finished.");

        object IEnumerator.Current => Current;

        public bool MoveNext()
        {
            // Descend the left spine of the pending subtree; popped slots are not cleared (every
            // node stays alive through the shared tree anyway), keeping reference stores minimal.
            var node = _next;
            var depth = _depth;
            if (node is not null)
            {
                var stack = _stack;
                do
                {
                    if (depth == stack.Length)
                    {
                        Array.Resize(ref _stack, stack.Length * 2);
                        stack = _stack;
                    }

                    stack[depth++] = node;
                    node = node.Left;
                }
                while (node is not null);
            }

            if (depth == 0)
            {
                _depth = 0;
                _next = null;
                _current = null;
                return false;
            }

            node = _stack[--depth]!;
            _depth = depth;
            _next = node.Right;
            _current = node.DeferredTwin is null ? node.Symbol : _view.Resolve(node);
            return true;
        }

        public void Reset()
        {
            Array.Clear(_stack);
            _depth = 0;
            _next = _view._root;
            _current = null;
        }

        public void Dispose()
        {
        }
    }

    public void Add(VisibleSymbol item) => throw new NotSupportedException("Scope visibility symbols are read-only.");

    public void Clear() => throw new NotSupportedException("Scope visibility symbols are read-only.");

    public void Insert(int index, VisibleSymbol item) => throw new NotSupportedException("Scope visibility symbols are read-only.");

    public bool Remove(VisibleSymbol item) => throw new NotSupportedException("Scope visibility symbols are read-only.");

    public void RemoveAt(int index) => throw new NotSupportedException("Scope visibility symbols are read-only.");
}

/// <summary>
/// The completion list of <see cref="SemanticModel.GetVisibleSymbolsAt"/> over a builder scope: the
/// scope's symbols followed by the prelude symbols they do not shadow, read through the scope's
/// shared view instead of copying it (one small array of unshadowed prelude symbols per call).
/// </summary>
internal sealed class MergedVisibleSymbolList : IList<VisibleSymbol>, IReadOnlyList<VisibleSymbol>
{
    private readonly ScopeSymbolView _scope;
    private readonly VisibleSymbol[] _prelude;

    internal MergedVisibleSymbolList(ScopeSymbolView scope, VisibleSymbol[] prelude)
    {
        _scope = scope;
        _prelude = prelude;
    }

    public int Count => _scope.Count + _prelude.Length;

    public bool IsReadOnly => true;

    public VisibleSymbol this[int index]
    {
        get
        {
            if ((uint)index >= (uint)Count)
                throw new ArgumentOutOfRangeException(nameof(index));
            var scopeCount = _scope.Count;
            return index < scopeCount ? _scope[index] : _prelude[index - scopeCount];
        }
        set => throw new NotSupportedException("Visible symbols are read-only.");
    }

    public bool Contains(VisibleSymbol item) => IndexOf(item) >= 0;

    public int IndexOf(VisibleSymbol item)
    {
        var index = _scope.IndexOf(item);
        if (index >= 0)
            return index;

        index = Array.IndexOf(_prelude, item);
        return index >= 0 ? _scope.Count + index : -1;
    }

    public void CopyTo(VisibleSymbol[] array, int arrayIndex)
    {
        ArgumentNullException.ThrowIfNull(array);
        ArgumentOutOfRangeException.ThrowIfNegative(arrayIndex);
        if (array.Length - arrayIndex < Count)
            throw new ArgumentException("Destination array is not long enough to copy all the items in the collection.", nameof(array));

        _scope.CopyTo(array, arrayIndex);
        _prelude.CopyTo(array, arrayIndex + _scope.Count);
    }

    public IEnumerator<VisibleSymbol> GetEnumerator() => new Enumerator(_scope, _prelude);

    private sealed class Enumerator(ScopeSymbolView scope, VisibleSymbol[] prelude) : IEnumerator<VisibleSymbol>
    {
        private readonly IEnumerator<VisibleSymbol> _scope = scope.GetEnumerator();
        private int _preludeIndex = -1;
        private bool _readingScope = true;
        private VisibleSymbol? _current;

        public VisibleSymbol Current => _current ?? throw new InvalidOperationException("Enumeration has not started or has already finished.");

        object IEnumerator.Current => Current;

        public bool MoveNext()
        {
            if (_readingScope && _scope.MoveNext())
            {
                _current = _scope.Current;
                return true;
            }

            _readingScope = false;
            if (_preludeIndex + 1 < prelude.Length)
            {
                _current = prelude[++_preludeIndex];
                return true;
            }

            _current = null;
            return false;
        }

        public void Reset()
        {
            _scope.Reset();
            _preludeIndex = -1;
            _readingScope = true;
            _current = null;
        }

        public void Dispose() => _scope.Dispose();
    }

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    public void Add(VisibleSymbol item) => throw new NotSupportedException("Visible symbols are read-only.");

    public void Clear() => throw new NotSupportedException("Visible symbols are read-only.");

    public void Insert(int index, VisibleSymbol item) => throw new NotSupportedException("Visible symbols are read-only.");

    public bool Remove(VisibleSymbol item) => throw new NotSupportedException("Visible symbols are read-only.");

    public void RemoveAt(int index) => throw new NotSupportedException("Visible symbols are read-only.");
}

/// <summary>
/// Passive structural census of a model's scope visibility storage (tests and probes): logical
/// memberships versus the distinct physical objects that back them.
/// </summary>
internal static class ScopeVisibilityCensus
{
    internal readonly record struct Report(
        int Scopes,
        long Memberships,
        int Wrappers,
        int Views,
        int Roots,
        int Nodes,
        int Symbols,
        int MaxTreeDepth);

    public static Report Measure(IReadOnlyList<ScopeVisibility> scopes)
    {
        long memberships = 0;
        var wrappers = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var views = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var roots = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var nodes = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var symbols = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var heights = new Dictionary<VisibilityNode, int>(ReferenceEqualityComparer.Instance);
        var maxDepth = 0;
        foreach (var scope in scopes)
        {
            memberships += scope.Symbols.Count;
            wrappers.Add(scope.Symbols);
            if (scope.View is not { } view)
            {
                foreach (var symbol in scope.Symbols)
                    symbols.Add(symbol);
                continue;
            }

            views.Add(view);
            if (view.Root is not { } root || !roots.Add(root))
                continue;

            // A shared subtree may occur at different depths in different roots. Memoize
            // its HEIGHT, not the first root-relative depth at which the census saw it.
            var heightWork = new Stack<(VisibilityNode Node, bool ChildrenDone)>();
            heightWork.Push((root, false));
            while (heightWork.TryPop(out var work))
            {
                if (heights.ContainsKey(work.Node))
                    continue;
                if (work.ChildrenDone)
                {
                    heights.Add(work.Node, 1 + Math.Max(
                        work.Node.Left is { } l ? heights[l] : 0,
                        work.Node.Right is { } r ? heights[r] : 0));
                    continue;
                }
                heightWork.Push((work.Node, true));
                if (work.Node.Left is { } leftChild)
                    heightWork.Push((leftChild, false));
                if (work.Node.Right is { } rightChild)
                    heightWork.Push((rightChild, false));
            }
            maxDepth = Math.Max(maxDepth, heights[root]);

            var pending = new Stack<(VisibilityNode Node, int Depth)>();
            pending.Push((root, 1));
            while (pending.TryPop(out var item))
            {
                if (!nodes.Add(item.Node))
                    continue;
                symbols.Add(item.Node.Symbol);
                if (item.Node.DeferredTwin is { } twin)
                    symbols.Add(twin);
                if (item.Node.Left is { } left)
                    pending.Push((left, item.Depth + 1));
                if (item.Node.Right is { } right)
                    pending.Push((right, item.Depth + 1));
            }
        }

        return new Report(scopes.Count, memberships, wrappers.Count, views.Count, roots.Count, nodes.Count, symbols.Count, maxDepth);
    }

    public static string Describe(IReadOnlyList<ScopeVisibility> scopes)
    {
        var report = Measure(scopes);
        return $"wrappers={report.Wrappers} views={report.Views} roots={report.Roots} nodes={report.Nodes} symbolObjects={report.Symbols} maxTreeDepth={report.MaxTreeDepth}";
    }

    /// <summary>The nodes a name lookup visits in <paramref name="scope"/>'s tree (0 for a host-built scope).</summary>
    public static int LookupProbes(ScopeVisibility scope, string name)
    {
        _ = VisibilityTree.Find(scope.View?.Root, name, out _, out var probes);
        return probes;
    }
}
