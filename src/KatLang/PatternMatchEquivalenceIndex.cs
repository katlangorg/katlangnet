using System.Globalization;
using System.Numerics;
using System.Text;

namespace KatLang;

/// <summary>
/// The ONE duplicate-detection index over <see cref="Pattern.IsMatchEquivalent"/> classes, shared by
/// the parser's clause-family builder and the runtime duplicate-branch guard
/// (<see cref="Algorithm.Conditional.HasDuplicateBranchPatterns"/>). It is a C# host-runtime
/// implementation detail with no semantic content: <see cref="TryAdd"/> answers whether the pattern
/// adds a new match-equivalence class, and the ordered branch list of its owner
/// stays the source of truth for branch order, diagnostics, and spans.
///
/// <para><b>Canonical key (SEC-03).</b> Each pattern is serialized once, in one iterative pre-order
/// walk, into a string key that encodes EXACTLY the relation <see cref="Pattern.IsMatchEquivalent"/>
/// decides: <c>CanonicalKey(a) == CanonicalKey(b)</c> (ordinal) if and only if
/// <c>a.IsMatchEquivalent(b)</c>. Every token is self-delimiting (a tag, then length- or
/// terminator-delimited data) and structural tokens carry their item count, so the key is a
/// uniquely decodable pre-order code of a tree whose nodes are:</para>
/// <list type="bullet">
/// <item>a binder as its FIRST-OCCURRENCE index in pre-order (spelling, span, and parameter kind are
/// erased; a repeated name repeats its index, so the equality constraints of repeated binders are
/// kept, and two patterns get the same index sequence exactly when a consistent bijection between
/// their binder names exists — the bijection <c>IsMatchEquivalent</c> builds);</item>
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
/// <para><b>Worst-case bound, independent of any hash.</b> The keys live in a balanced ordered set
/// (<see cref="SortedSet{T}"/>, a red-black tree) under ordinal comparison; nothing is hashed, so no
/// attacker-chosen input can share a bucket. Walking and writing a key is linear in the pattern's
/// size (nodes plus text; integers render in O(1) digits). Binder names are numbered by an ordered
/// map, adding O(T log(B + 1)) work for T binder-name units and at most B distinct binders per head.
/// An insertion performs O(log N) ordinal comparisons, and each comparison stops at the first
/// differing code unit or at the end of the
/// shorter key, so it costs at most the NEW key's length. A family of N clauses with total key size
/// S therefore costs O(S log(N + 1) + T log(B + 1)) time and O(S + T) memory, whatever the literals.
/// The formerly collision-driven O(N^2) exact comparisons (the deterministic 32-bit FNV-1a fingerprint let
/// attacker-chosen string literals share one bucket) cannot occur. No part of this index relies on
/// randomized hashing. Each head gets a fresh binder map, so a large head leaves no bucket array
/// to clear repeatedly for later small heads.</para>
///
/// <para><b>Laziness and small families.</b> Single-clause families are the common case (every
/// ordinary <c>F(x) = ...</c>), so the first added pattern is only remembered; keys and the builder
/// are created when a SECOND pattern arrives. Up to <see cref="SmallIndexCapacity"/> keys are kept
/// in a short list probed by ordinal equality (at most that many comparisons per insertion, each
/// bounded by the new key's length — a constant factor, not a hash), and only a larger family moves
/// them into the ordered tree. The runtime guard runs per family call, so small families stay
/// cheap.</para>
///
/// <para><b>Cancellation.</b> <see cref="TryAdd"/> observes the supplied tokens (the authoritative
/// source-processing token first, so a host cancellation always carries that token's identity) once
/// per call and in bounded blocks while traversing, writing, copying and comparing keys and binder
/// names. Blocks contain at most <see cref="CanonicalizationCheckpointInterval"/> units; a checkpoint
/// follows at most two such blocks, including for a single long literal or common prefix. The index
/// holds no static or ambient state; an instance belongs to one family of one parse or one guard call.</para>
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

    private sealed class KeyBuilder(PatternMatchEquivalenceIndex owner)
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
