using System.Diagnostics;
using System.Globalization;
using System.Numerics;
using System.Text;

namespace KatLang;

/// <summary>
/// The ONE duplicate-detection index over <see cref="Pattern.IsMatchEquivalent"/> classes, shared by
/// the parser's clause-family builder and the runtime duplicate-branch guard
/// (<see cref="Algorithm.Conditional.HasDuplicateBranchPatterns()"/>, decided once per run per family by the
/// evaluator's run-local family preparation, <c>Evaluator.NeedFamilyPreparationCache</c>). It is a C# host-runtime
/// implementation detail with no semantic content: <see cref="TryAdd"/> answers whether the pattern
/// adds a new match-equivalence class, and the ordered branch list of its owner
/// stays the source of truth for branch order, diagnostics, and spans.
///
/// <para><b>Canonical key (SEC-03).</b> Each pattern is serialized once into a string key that
/// encodes EXACTLY the relation <see cref="Pattern.IsMatchEquivalent"/> decides:
/// <c>CanonicalKey(a) == CanonicalKey(b)</c> (ordinal) if and only if <c>a.IsMatchEquivalent(b)</c>.
/// The relation is defined on the pattern TREE a head spells out, a node per occurrence. The key
/// codes that tree's nodes as:</para>
/// <list type="bullet">
/// <item>a binder as its FIRST-OCCURRENCE index in left-to-right leaf order (spelling, span, and
/// parameter kind are erased; a repeated name repeats its index, so the equality constraints of
/// repeated binders are kept, and two patterns get the same index sequence exactly when a
/// consistent bijection between their binder names exists — the bijection <c>IsMatchEquivalent</c>
/// builds);</item>
/// <item>a numeric literal as the canonical form of its VALUE, so key equality is
/// <see cref="Decimal128"/>.Equals: one NaN token (NaN is reflexively equal), one zero token (the
/// sign of zero is ignored), signed infinities, and for a finite nonzero value its sign, its
/// coefficient with trailing zeros stripped, and the correspondingly adjusted exponent (quantum is
/// ignored: <c>1.5</c> and <c>1.50</c> share a key);</item>
/// <item>a string literal as its length and its exact UTF-16 code units (ordinal equality — no
/// culture, no normalization);</item>
/// <item>a Boolean literal as its own tag per value (never a number);</item>
/// <item>a sequence or list pattern as a KIND-specific tag plus its item count, followed by its
/// items in order (kind, cardinality, order, and nesting all distinguish).</item>
/// </list>
///
/// <para><b>Built once per shared node (the DAG-linear key, 2026-11-10).</b> A host-built head may
/// share a sub-pattern along many paths, so its tree can be exponentially larger than the head. The
/// key is therefore not the tree's pre-order text but the MINIMAL DAG of that tree, serialized
/// canonically: the list of DEFINITIONS — one per distinct canonical subtree, each a self-delimiting
/// leaf token or a structure token (kind tag, item count, and each item's definition number) — in
/// the order their subtrees first COMPLETE in the tree's post-order. One iterative post-order walk
/// writes it; a node met again in the same call (reference identity, a call-local memo) contributes
/// its known number without being walked. That shortcut changes nothing: everything below the node
/// was completed at its first visit, so a second walk would add no definition and no binder. Binder
/// indexes are context-free here — leaves complete in left-to-right order, so a binder's
/// first-occurrence index is fixed when its leaf completes and is the same on every path, which keeps
/// repeated-name equivalence under sharing exactly as in the tree. A definition already written in
/// this call (an equal subtree under a different object) is found in an exact compressed ordinal
/// trie and reused. The key is a function of the tree alone (two trees with the same minimal DAG produce the
/// same definitions in the same order) and the tree is recoverable from it (the root is the last
/// definition), so key equality is tree equality: exactly the equality of the former pre-order key,
/// which tests keep as an oracle (<see cref="TreeCanonicalKey"/>). Nothing is hashed by content and
/// nothing is attached to a pattern.</para>
///
/// <para><b>Worst-case bound, independent of any content hash.</b> The keys live in a balanced ordered
/// set (<see cref="SortedSet{T}"/>, a red-black tree) under ordinal comparison. Per-head definitions
/// and binder names use compressed ordinal tries; the only hash table is the call-local
/// reference-identity memo. For a head of V distinct nodes (reference identity) with E item
/// edges among them, its walk is O(V + E) node visits, and its key and definitions have size
/// D = O(V + E + L) for L literal code units, using CLR indexes (at most ten decimal digits).
/// A trie lookup advances monotonically through its new input; only SINGLE UTF-16 units are ordered
/// in child maps (a fixed alphabet of 65,536 units), so there is no log V or log B factor. All
/// definition writes, including retracted duplicates, and all trie work cost O(V + E + L + T), for
/// T binder-name units of the distinct binder nodes — independent of the number of paths. An
/// insertion performs O(log N) ordinal key comparisons, and each
/// comparison stops at the first differing code unit or at the end of the shorter key, so it costs
/// at most the NEW key's length. A family of N clauses with total key size S therefore costs
/// O(H + S log(N + 1)) time for total graph input size H (nodes, edges, literal and binder-name units)
/// and O(S + H) memory, whatever the literals. On a tree (every parsed head) V is the node count.
/// The formerly collision-driven O(N^2) exact comparisons (the deterministic
/// 32-bit FNV-1a fingerprint let attacker-chosen string literals share one bucket) cannot occur.
/// Each head gets a fresh binder map and definition numbering, and a large memo is dropped rather
/// than cleared, so a large head leaves no bucket array to clear repeatedly for later small
/// heads.</para>
///
/// <para><b>Laziness and small families.</b> Single-clause families are the common case (every
/// ordinary <c>F(x) = ...</c>), so the first added pattern is only remembered; keys and the builder
/// are created when a SECOND pattern arrives. Up to <see cref="SmallIndexCapacity"/> keys are kept
/// in a short list probed by ordinal equality (at most that many comparisons per insertion, each
/// bounded by the new key's length — a constant factor, not a hash), and only a larger family moves
/// them into the ordered tree. The evaluator decides the runtime guard once per run per family
/// branch list (not per call; the public method still decides afresh on each call), and small
/// families stay cheap either way.</para>
///
/// <para><b>Cancellation.</b> <see cref="TryAdd"/> observes the supplied tokens (the authoritative
/// source-processing token first, so a host cancellation always carries that token's identity) once
/// per call and in bounded blocks while traversing, writing, copying and comparing keys, definitions
/// and binder names. Blocks contain at most <see cref="CanonicalizationCheckpointInterval"/> units; a checkpoint
/// follows at most two such blocks, including for a single long literal or common prefix. The index
/// holds no static or ambient state; an instance belongs to one family of one parse or one guard call.
/// The runtime guard passes the run's token (an uncharged, cancellable, AST-bounded preparation).</para>
/// </summary>
internal sealed class PatternMatchEquivalenceIndex(PatternComparisonObservations? observations = null)
{
    /// <summary>Maximum block of traversal, copying or ordinal-comparison work.</summary>
    internal const int CanonicalizationCheckpointInterval = 4096;

    /// <summary>Keys kept in the linearly probed list before the index moves to the ordered tree.</summary>
    internal const int SmallIndexCapacity = 8;

    private Pattern? _pending;
    private readonly PatternComparisonObservations? _observations = observations;
    private KeyBuilder? _builder;
    private List<string>? _smallKeys;
    private SortedSet<string>? _keys;
    private IndexOrdinalComparer? _keyComparer;
    private CancellationToken _sourceProcessingCancellationToken;
    private CancellationToken _activeCancellationToken;
    private int _unitsUntilCheckpoint = CanonicalizationCheckpointInterval;

    /// <summary>
    /// Adds <paramref name="pattern"/>; returns <c>false</c> exactly when an earlier added pattern is
    /// match-equivalent to it (the pattern is then not added again — one representative per class
    /// suffices because match-equivalence is an equivalence relation).
    /// </summary>
    /// <exception cref="OperationCanceledException">A supplied token was cancelled.</exception>
    public bool TryAdd(
        Pattern pattern,
        CancellationToken sourceProcessingCancellationToken = default,
        CancellationToken activeCancellationToken = default)
    {
        ArgumentNullException.ThrowIfNull(pattern);
        _sourceProcessingCancellationToken = sourceProcessingCancellationToken;
        _activeCancellationToken = activeCancellationToken;
        _unitsUntilCheckpoint = CanonicalizationCheckpointInterval;
        ObserveCancellation();

        if (_builder is null)
        {
            if (_pending is null)
            {
                _pending = pattern;
                return true;
            }

            _builder = new KeyBuilder(this);
            _keyComparer = new IndexOrdinalComparer(this);
            _smallKeys = [_builder.Build(_pending)];
            _pending = null;
        }

        var key = _builder.Build(pattern);
        if (_keys is not null)
            return Finish(_keys.Add(key));

        var smallKeys = _smallKeys!;
        foreach (var existing in smallKeys)
        {
            if (_keyComparer!.Compare(existing, key) == 0)
                return Finish(false);
        }

        if (smallKeys.Count < SmallIndexCapacity)
        {
            smallKeys.Add(key);
            return Finish(true);
        }

        // The family outgrew the list: move its distinct keys into the ordered tree once.
        _keys = new SortedSet<string>(_keyComparer);
        foreach (var existing in smallKeys)
            _keys.Add(existing);
        _smallKeys = null;
        return Finish(_keys.Add(key));
    }

    /// <summary>
    /// The canonical match-equivalence key of <paramref name="pattern"/> (see the class remarks):
    /// equal keys ⇔ <see cref="Pattern.IsMatchEquivalent"/>. Test and diagnostic entry; the index
    /// builds keys through one reused builder instead.
    /// </summary>
    internal static string CanonicalKey(Pattern pattern)
    {
        ArgumentNullException.ThrowIfNull(pattern);
        return new KeyBuilder(new PatternMatchEquivalenceIndex()).Build(pattern);
    }

    /// <summary>
    /// The former pre-order TREE key of <paramref name="pattern"/>: one token per occurrence, so its
    /// length grows with the head's paths. Test oracle only: <see cref="CanonicalKey"/> induces exactly
    /// its equality (equal tree keys ⇔ equal DAG keys), on trees and on shared heads alike.
    /// </summary>
    internal static string TreeCanonicalKey(Pattern pattern)
    {
        ArgumentNullException.ThrowIfNull(pattern);
        return new TreeKeyBuilder(new PatternMatchEquivalenceIndex()).Build(pattern);
    }

    private bool Finish(bool added)
    {
        ThrowIfCancellationRequested();
        return added;
    }

    private void ThrowIfCancellationRequested()
    {
        _sourceProcessingCancellationToken.ThrowIfCancellationRequested();
        _activeCancellationToken.ThrowIfCancellationRequested();
    }

    private void ObserveCancellation()
    {
        _observations?.RecordCancellationCheckpoint();
        ThrowIfCancellationRequested();
    }

    private void ConsumeWork(int units)
    {
        _unitsUntilCheckpoint -= units;
        if (_unitsUntilCheckpoint <= 0)
        {
            ObserveCancellation();
            _unitsUntilCheckpoint = CanonicalizationCheckpointInterval;
        }
    }

    // The DAG-LINEAR canonical key (class remarks): the definitions of the head's distinct canonical
    // subtrees in first-completion post-order, each structure naming its items by definition number.
    private sealed class KeyBuilder
    {
        // A completed-node memo larger than this is dropped rather than cleared, so one large head
        // never makes every later small head clear a large bucket array.
        private const int CompletedMemoReuseLimit = 64;

        private readonly PatternMatchEquivalenceIndex _owner;
        private readonly DefinitionInterner _definitions;
        private readonly List<Frame> _frames = [];
        private readonly List<int> _itemIds = [];
        private char[] _text = new char[64];
        private int _length;

        // Created on the first non-root node; a bare literal or binder head never needs it.
        private Dictionary<Pattern, int>? _completed;

        // Created on the first binder; most literal-only heads never need it.
        private BinderInterner? _binderIndexes;

        public KeyBuilder(PatternMatchEquivalenceIndex owner)
        {
            _owner = owner;
            _definitions = new DefinitionInterner(this);
        }

        public string Build(Pattern pattern)
        {
            _length = 0;
            _definitions.Clear();
            _frames.Clear();
            _itemIds.Clear();
            _binderIndexes = null;
            if (_completed is { Count: > CompletedMemoReuseLimit })
                _completed = null;
            else
                _completed?.Clear();

            // Iterative post-order walk: host-built patterns may be arbitrarily deep, so the walk
            // never recurses on the caller's stack. Cursors keep O(depth) state without pushing
            // every item of a wide structure before the next cancellation observation. A node
            // completed earlier in this call (reference identity) contributes its known number:
            // every definition and binder below it already exists, so the definitions written —
            // and hence the key — are exactly those of the expanded tree.
            _ = Enter(pattern, isRoot: true);
            while (_frames.Count > 0)
            {
                var top = _frames.Count - 1;
                var frame = _frames[top];
                if (frame.Next < frame.Count)
                {
                    _frames[top] = frame with { Next = frame.Next + 1 };
                    var itemId = Enter(frame.Items[frame.Next], isRoot: false);
                    if (itemId >= 0)
                        _itemIds.Add(itemId);
                    continue;
                }

                _frames.RemoveAt(top);
                _owner._observations?.RecordTraversal();
                _owner.ConsumeWork(1);
                var id = DefineStructure(frame.Tag, frame.FirstItem);
                if (_frames.Count > 0)
                {
                    Remember(frame.Node, id);
                    _itemIds.Add(id);
                }
            }

            // Copy the text in bounded blocks, observing cancellation between them.
            var key = string.Create(_length, this, static (destination, builder) =>
            {
                for (var offset = 0; offset < destination.Length;)
                {
                    var length = Math.Min(CanonicalizationCheckpointInterval, destination.Length - offset);
                    builder._text.AsSpan(offset, length).CopyTo(destination.Slice(offset, length));
                    builder._owner._observations?.RecordKeyCopy(length);
                    builder._owner.ConsumeWork(length);
                    offset += length;
                }
            });
            _owner.ThrowIfCancellationRequested();
            _owner._observations?.RecordCanonicalKey(key.Length);
            return key;
        }

        // The definition number of a leaf or an empty structure, the known number of a node
        // completed earlier in this call, or -1 after opening a cursor for a nonempty structure.
        private int Enter(Pattern node, bool isRoot)
        {
            _owner._observations?.RecordTraversal();
            _owner.ConsumeWork(1);
            if (_completed is not null && _completed.TryGetValue(node, out var known))
            {
                _owner._observations?.RecordSharedNodeReuse();
                return known;
            }

            int id;
            switch (node)
            {
                case Pattern.SequenceValue sequence:
                    if ((id = Open(node, '(', sequence.Items)) < 0)
                        return id;
                    break;
                case Pattern.ListValue list:
                    if ((id = Open(node, '[', list.Items)) < 0)
                        return id;
                    break;
                default:
                    id = DefineLeaf(node);
                    break;
            }

            if (!isRoot)
                Remember(node, id);
            return id;
        }

        private int Open(Pattern node, char tag, IReadOnlyList<Pattern> items)
        {
            // The count is read once: the cursor and the definition agree on it.
            var count = items.Count;
            if (count == 0)
                return DefineStructure(tag, _itemIds.Count);
            _frames.Add(new Frame(node, items, count, 0, _itemIds.Count, tag));
            return -1;
        }

        private void Remember(Pattern node, int id)
            => (_completed ??= new Dictionary<Pattern, int>(ReferenceEqualityComparer.Instance))[node] = id;

        private int DefineLeaf(Pattern node)
        {
            var start = _length;
            var copiedUnits = 0;
            switch (node)
            {
                case Pattern.Bind bind:
                    _binderIndexes ??= new BinderInterner(_owner);
                    _owner._observations?.RecordBinderName(bind.Name.Length);
                    var index = _binderIndexes.GetOrAdd(bind.Name, out _);
                    Append('b');
                    AppendFormatted(index);
                    Append(';');
                    break;
                case Pattern.LitInt litInt:
                    Append('n');
                    AppendNumber(litInt.Value);
                    break;
                case Pattern.LitString litString:
                    var value = litString.Value;
                    Append('s');
                    AppendFormatted(value.Length);
                    Append(':');
                    for (var offset = 0; offset < value.Length;)
                    {
                        var length = Math.Min(CanonicalizationCheckpointInterval, value.Length - offset);
                        AppendSpan(value.AsSpan(offset, length));
                        _owner.ConsumeWork(length);
                        offset += length;
                    }
                    copiedUnits = value.Length;
                    break;
                case Pattern.LitBool litBool:
                    Append(litBool.Value ? 't' : 'f');
                    break;
                default:
                    throw new UnreachableException($"Unknown pattern node {node.GetType().Name}.");
            }

            _owner.ConsumeWork(_length - start - copiedUnits);
            return Intern(start);
        }

        // A structure definition: kind tag, item count, then each item's definition number. The
        // item numbers are the entries of the item stack from firstItem on, which this pops.
        private int DefineStructure(char tag, int firstItem)
        {
            var start = _length;
            Append(tag);
            AppendFormatted(_itemIds.Count - firstItem);
            Append(';');
            _owner.ConsumeWork(_length - start);
            for (var item = firstItem; item < _itemIds.Count; item++)
            {
                var itemStart = _length;
                AppendFormatted(_itemIds[item]);
                Append(';');
                _owner.ConsumeWork(_length - itemStart);
            }

            _itemIds.RemoveRange(firstItem, _itemIds.Count - firstItem);
            return Intern(start);
        }

        // The number of the definition just written at [start, _length): an equal earlier
        // definition's (the text is then retracted) or the next number.
        private int Intern(int start)
        {
            var segment = new Segment(start, _length - start);
            _owner._observations?.RecordDefinitionWrite(segment.Length);
            var id = _definitions.GetOrAdd(segment, out var added);
            if (!added)
                _length = start;
            return id;
        }

        // The canonical form of a Decimal128 VALUE: two literals share it exactly when
        // Decimal128.Equals holds (NaN reflexive, signed zeros equal, quantum ignored).
        private void AppendNumber(Decimal128 value)
        {
            if (Decimal128.IsNaN(value))
            {
                Append('N');
                return;
            }

            if (Decimal128.IsInfinity(value))
            {
                AppendSpan(Decimal128.IsNegative(value) ? "-I" : "+I");
                return;
            }

            // Equals, not a representation test: every zero (either sign, any quantum) is
            // one value.
            if (value.Equals(Decimal128.Zero))
            {
                Append('0');
                return;
            }

            var coefficient = Decimal128Numerics.CoefficientOf(Decimal128.Abs(value), out var exponent);
            while (coefficient % 10 == 0)
            {
                coefficient /= 10;
                exponent++;
            }

            Append(Decimal128.IsNegative(value) ? '-' : '+');
            AppendFormatted(exponent);
            Append(':');
            AppendFormatted(coefficient);
            Append(';');
        }

        private void EnsureCapacity(int additional)
        {
            if (_text.Length - _length >= additional)
                return;

            var capacity = (int)Math.Min(Array.MaxLength, Math.Max((long)_length + additional, (long)_text.Length * 2));
            var grown = new char[Math.Max(checked(_length + additional), capacity)];
            // Resizing a flat buffer with Array.Resize would copy its entire old capacity without
            // observing cancellation. Copy only live text, in the same bounded blocks as the key.
            for (var offset = 0; offset < _length;)
            {
                var length = Math.Min(CanonicalizationCheckpointInterval, _length - offset);
                _text.AsSpan(offset, length).CopyTo(grown.AsSpan(offset, length));
                _owner._observations?.RecordBufferCopy(length);
                _owner.ConsumeWork(length);
                offset += length;
            }
            _text = grown;
        }

        private void Append(char value)
        {
            EnsureCapacity(1);
            _text[_length++] = value;
        }

        private void AppendSpan(ReadOnlySpan<char> value)
        {
            EnsureCapacity(value.Length);
            value.CopyTo(_text.AsSpan(_length));
            _length += value.Length;
        }

        private void AppendFormatted<T>(T value)
            where T : ISpanFormattable
        {
            for (var room = 16; ; room *= 2)
            {
                EnsureCapacity(room);
                if (value.TryFormat(_text.AsSpan(_length), out var written, default, CultureInfo.InvariantCulture))
                {
                    _length += written;
                    return;
                }
            }
        }

        private readonly record struct Frame(Pattern Node, IReadOnlyList<Pattern> Items, int Count, int Next, int FirstItem, char Tag);

        private sealed class DefinitionInterner(KeyBuilder builder) : OrdinalInterner<Segment>(builder._owner)
        {
            protected override ReadOnlySpan<char> TextOf(Segment segment)
                => builder._text.AsSpan(segment.Start, segment.Length);
        }
    }

    // A definition's place in the key builder's text.
    private readonly record struct Segment(int Start, int Length);

    private sealed class BinderInterner(PatternMatchEquivalenceIndex owner) : OrdinalInterner<string>(owner, binderNames: true)
    {
        protected override ReadOnlySpan<char> TextOf(string text) => text.AsSpan();
    }

    // Exact compressed ordinal trie. An edge stores a representative key and its END offset, so
    // splitting an edge never copies or rescans its prefix. A lookup advances monotonically through
    // the new key. Child maps compare SINGLE UTF-16 units: at most 65,536 children, hence a constant
    // bound on red-black comparisons per consumed unit, independent of the number of definitions
    // or binders. There is no content hash or collision fallback. Nodes/edges occupy O(key count)
    // space, and work is O(total input units). Definition segments always refer to retained text;
    // they are resolved through the builder so a buffer growth cannot leave an old array retained.
    private abstract class OrdinalInterner<T>(PatternMatchEquivalenceIndex owner, bool binderNames = false)
    {
        private readonly CharacterComparer _characters = new(owner, binderNames);
        private readonly Node _root = new(default!, 0);
        private int _count;

        protected abstract ReadOnlySpan<char> TextOf(T key);

        public void Clear()
        {
            _root.Children = null;
            _root.Id = -1;
            _count = 0;
        }

        public int GetOrAdd(T key, out bool added)
        {
            var text = TextOf(key);
            var parent = _root;
            var offset = 0;
            while (true)
            {
                if (offset == text.Length)
                {
                    RecordComparison(1);
                    added = parent.Id < 0;
                    if (added) parent.Id = _count++;
                    return parent.Id;
                }

                parent.Children ??= new SortedDictionary<char, Node>(_characters);
                var first = text[offset];
                if (!parent.Children.TryGetValue(first, out var child))
                {
                    var leaf = new Node(key, text.Length) { Id = _count++ };
                    parent.Children.Add(first, leaf);
                    added = true;
                    return leaf.Id;
                }

                var existing = TextOf(child.Key);
                var end = Math.Min(text.Length, child.End);
                while (offset < end)
                {
                    var length = Math.Min(CanonicalizationCheckpointInterval, end - offset);
                    var matching = 0;
                    while (matching < length && text[offset + matching] == existing[offset + matching])
                        matching++;
                    RecordComparison(Math.Min(length, matching + 1));
                    offset += matching;
                    if (matching != length) break;
                }

                if (offset == child.End)
                {
                    parent = child;
                    continue;
                }

                // A shorter key or the first differing unit splits this edge. The representative
                // of the common prefix is an already-retained key, even when the new one is a
                // temporary definition that its caller will retract after an equal lookup.
                var split = new Node(child.Key, offset)
                {
                    Children = new SortedDictionary<char, Node>(_characters) { [existing[offset]] = child },
                };
                parent.Children[first] = split;
                var id = _count++;
                if (offset == text.Length)
                    split.Id = id;
                else
                    split.Children.Add(text[offset], new Node(key, text.Length) { Id = id });
                added = true;
                return id;
            }
        }

        private void RecordComparison(int units)
        {
            if (binderNames)
                owner._observations?.RecordBinderComparison(units);
            else
                owner._observations?.RecordDefinitionComparison(units);
            owner.ConsumeWork(units);
        }

        private sealed class Node(T key, int end)
        {
            public T Key { get; } = key;
            public int End { get; } = end;
            public int Id { get; set; } = -1;
            public SortedDictionary<char, Node>? Children { get; set; }
        }

        private sealed class CharacterComparer(PatternMatchEquivalenceIndex index, bool names) : IComparer<char>
        {
            public int Compare(char x, char y)
            {
                if (names)
                    index._observations?.RecordBinderComparison(1);
                else
                    index._observations?.RecordDefinitionComparison(1);
                index.ConsumeWork(1);
                return x.CompareTo(y);
            }
        }
    }

    // THE TREE KEY (test oracle; the key before the DAG-linear builder): one iterative pre-order
    // text over every occurrence, binders numbered by first occurrence. Its length grows with the
    // head's paths, so production never builds it; tests check that the DAG key induces exactly
    // its equality on trees and on the unshared expansions of DAGs.
    private sealed class TreeKeyBuilder(PatternMatchEquivalenceIndex owner)
    {
        private readonly StringBuilder _text = new();
        private readonly Stack<(IReadOnlyList<Pattern> Items, int Next)> _pending = new();

        // Created on the first binder; most literal-only heads never need it.
        private SortedDictionary<string, int>? _binderIndexes;
        private IndexOrdinalComparer? _binderComparer;

        public string Build(Pattern pattern)
        {
            _text.Clear();
            _binderIndexes = null;
            _pending.Clear();

            // Iterative pre-order walk: host-built patterns may be arbitrarily deep, so the
            // walk never recurses on the caller's stack. Cursors keep O(depth) state without
            // pushing every child of a wide structure before the next cancellation observation.
            for (var node = pattern; node is not null;)
            {
                owner._observations?.RecordTraversal();
                owner.ConsumeWork(1);
                var startLength = _text.Length;
                var copiedUnits = 0;
                Pattern? next = null;

                switch (node)
                {
                    case Pattern.Bind bind:
                        _binderComparer ??= new IndexOrdinalComparer(owner, binderNames: true);
                        _binderIndexes ??= new SortedDictionary<string, int>(_binderComparer);
                        owner._observations?.RecordBinderName(bind.Name.Length);
                        if (!_binderIndexes.TryGetValue(bind.Name, out var index))
                        {
                            index = _binderIndexes.Count;
                            _binderIndexes.Add(bind.Name, index);
                        }
                        _text.Append('b').Append(CultureInfo.InvariantCulture, $"{index}").Append(';');
                        break;
                    case Pattern.LitInt litInt:
                        _text.Append('n');
                        AppendNumber(litInt.Value);
                        break;
                    case Pattern.LitString litString:
                        _text.Append('s').Append(CultureInfo.InvariantCulture, $"{litString.Value.Length}").Append(':');
                        for (var offset = 0; offset < litString.Value.Length;)
                        {
                            var length = Math.Min(CanonicalizationCheckpointInterval, litString.Value.Length - offset);
                            _text.Append(litString.Value.AsSpan(offset, length));
                            owner.ConsumeWork(length);
                            offset += length;
                        }
                        copiedUnits = litString.Value.Length;
                        break;
                    case Pattern.LitBool litBool:
                        _text.Append(litBool.Value ? 't' : 'f');
                        break;
                    case Pattern.SequenceValue sequence:
                        next = AppendStructure('(', sequence.Items);
                        break;
                    case Pattern.ListValue list:
                        next = AppendStructure('[', list.Items);
                        break;
                }

                owner.ConsumeWork(_text.Length - startLength - copiedUnits);
                node = next ?? TakeNext();
            }

            // Copy each StringBuilder chunk once. Repeated CopyTo(offset, ...) would repeatedly
            // search the chunk chain and itself permit quadratic work for very long keys.
            var key = string.Create(_text.Length, this, static (destination, builder) =>
            {
                var written = 0;
                foreach (var chunk in builder._text.GetChunks())
                {
                    for (var offset = 0; offset < chunk.Length;)
                    {
                        var length = Math.Min(CanonicalizationCheckpointInterval, chunk.Length - offset);
                        chunk.Span.Slice(offset, length).CopyTo(destination.Slice(written, length));
                        builder.RecordCopyWork(length);
                        offset += length;
                        written += length;
                    }
                }
            });
            owner.ThrowIfCancellationRequested();
            owner._observations?.RecordCanonicalKey(key.Length);
            return key;
        }

        private void RecordCopyWork(int length)
        {
            owner._observations?.RecordKeyCopy(length);
            owner.ConsumeWork(length);
        }

        private Pattern? AppendStructure(char kindTag, IReadOnlyList<Pattern> items)
        {
            _text.Append(kindTag).Append(CultureInfo.InvariantCulture, $"{items.Count}").Append(';');
            if (items.Count == 0)
                return null;
            _pending.Push((items, 1));
            return items[0];
        }

        private Pattern? TakeNext()
        {
            while (_pending.TryPop(out var cursor))
            {
                owner._observations?.RecordTraversal();
                owner.ConsumeWork(1);
                if (cursor.Next < cursor.Items.Count)
                {
                    _pending.Push((cursor.Items, cursor.Next + 1));
                    return cursor.Items[cursor.Next];
                }
            }
            return null;
        }

        // The canonical form of a Decimal128 VALUE: two literals share it exactly when
        // Decimal128.Equals holds (NaN reflexive, signed zeros equal, quantum ignored).
        private void AppendNumber(Decimal128 value)
        {
            if (Decimal128.IsNaN(value))
            {
                _text.Append('N');
                return;
            }

            if (Decimal128.IsInfinity(value))
            {
                _text.Append(Decimal128.IsNegative(value) ? "-I" : "+I");
                return;
            }

            // Equals, not a representation test: every zero (either sign, any quantum) is
            // one value.
            if (value.Equals(Decimal128.Zero))
            {
                _text.Append('0');
                return;
            }

            var coefficient = Decimal128Numerics.CoefficientOf(Decimal128.Abs(value), out var exponent);
            while (coefficient % 10 == 0)
            {
                coefficient /= 10;
                exponent++;
            }

            _text.Append(Decimal128.IsNegative(value) ? '-' : '+')
                .Append(CultureInfo.InvariantCulture, $"{exponent}:{coefficient}")
                .Append(';');
        }
    }

    // Ordinal comparison that additionally records an upper bound of its own work: an ordinal
    // comparison stops at the first differing code unit or at the end of the shorter key.
    private sealed class IndexOrdinalComparer(PatternMatchEquivalenceIndex owner, bool binderNames = false) : IComparer<string>
    {
        public int Compare(string? x, string? y)
        {
            var commonLength = Math.Min(x?.Length ?? 0, y?.Length ?? 0);
            if (binderNames)
                owner._observations?.RecordBinderComparison(commonLength + 1);
            else
                owner._observations?.RecordKeyComparison(commonLength + 1);

            if (x is null || y is null
                || (!owner._sourceProcessingCancellationToken.CanBeCanceled
                    && !owner._activeCancellationToken.CanBeCanceled
                    && owner._observations?.CheckpointReached is null))
                return string.CompareOrdinal(x, y);

            for (var offset = 0; offset < commonLength;)
            {
                var length = Math.Min(CanonicalizationCheckpointInterval, commonLength - offset);
                var comparison = string.CompareOrdinal(x, offset, y, offset, length);
                owner.ConsumeWork(length);
                if (comparison != 0)
                    return comparison;
                offset += length;
            }
            return x.Length.CompareTo(y.Length);
        }
    }
}
