namespace KatLang;

/// <summary>
/// Structured evaluation result.
/// Corresponds to <c>Result</c> in the Lean specification.
/// </summary>
public abstract record Result
{
    private Result() { }

    /// <summary>
    /// KatLang value-semantic comparer for <see cref="Result"/>.
    /// Atoms compare by numeric value, strings by exact string value, and
    /// sequence and list values structurally by ordered child results.
    /// Different value kinds compare unequal (a list never equals a sequence).
    /// </summary>
    public static IEqualityComparer<Result> ValueComparer { get; } = new ValueSemanticComparer();

    /// <summary>A single numeric value.</summary>
    public sealed record Atom(decimal Value) : Result;

    /// <summary>A first-class string value. Lean: Result.str.</summary>
    public sealed record Str(string Value) : Result;

    /// <summary>
    /// A sequence value containing ordered child results.
    ///
    /// Sequence values are OBSERVABLY immutable, following the same model as
    /// <see cref="ListValue"/>: public construction snapshots the supplied
    /// items (mutating the constructor input afterwards cannot change the
    /// value), and <see cref="Items"/> exposes only a read-only view whose
    /// mutation members throw without changing the value. Trusted internal
    /// construction may instead transfer exclusive ownership of freshly built
    /// storage via <see cref="TakeOwnership"/>; internal mutation of sequence
    /// storage is permitted only before the value is published or under proven
    /// exclusive ownership where no previously observable value can change.
    /// Note: C# record equality is not KatLang language equality — KatLang
    /// structural equality uses <see cref="ValueComparer"/>.
    /// </summary>
    public sealed record SequenceValue : Result
    {
        private readonly IReadOnlyList<Result> items;

        /// <summary>
        /// Snapshot construction for host-facing / untrusted input: copies
        /// <paramref name="items"/>, so the caller retains no alias through
        /// which this value could later be mutated.
        /// </summary>
        public SequenceValue(IEnumerable<Result> items)
            : this(items.ToArray())
        {
        }

        private SequenceValue(Result[] exclusivelyOwnedItems)
            => items = Array.AsReadOnly(exclusivelyOwnedItems);

        /// <summary>
        /// Trusted ownership-transfer construction: wraps
        /// <paramref name="exclusivelyOwnedItems"/> without copying.
        /// Invariant: after this call the storage belongs to the sequence
        /// value — the caller must never mutate, reuse, retain a mutable alias
        /// to, or expose the transferred array. Use only for storage that
        /// provably has no other owner (e.g. a freshly materialized array).
        /// </summary>
        internal static SequenceValue TakeOwnership(Result[] exclusivelyOwnedItems)
            => new(exclusivelyOwnedItems);

        /// <summary>
        /// Ordered items as a read-only view. The view never exposes the
        /// backing storage: casting it to a mutable collection interface
        /// yields an object that rejects every mutation operation.
        /// </summary>
        public IReadOnlyList<Result> Items => items;

        public void Deconstruct(out IReadOnlyList<Result> items) => items = this.items;
    }

    /// <summary>
    /// An exact immutable list value <c>[a, b, c]</c>. Unlike sequence values,
    /// list structure is never singleton-normalized: <c>[7]</c> and <c>7</c>
    /// are distinct values, <c>[]</c> is distinct from the empty sequence
    /// value <c>()</c>, and nesting is preserved exactly.
    ///
    /// List values are OBSERVABLY immutable: public construction snapshots the
    /// supplied items (mutating the constructor input afterwards cannot change
    /// the value), and <see cref="Items"/> exposes only a read-only view whose
    /// mutation members throw without changing the value. Trusted internal
    /// construction may instead transfer exclusive ownership of freshly built
    /// storage via <see cref="TakeOwnership"/>; internal mutation of list
    /// storage is permitted only before the value is published or under proven
    /// exclusive ownership where no previously observable value can change.
    /// Lean: <c>Result.listValue</c>.
    /// </summary>
    public sealed record ListValue : Result
    {
        private readonly IReadOnlyList<Result> items;

        /// <summary>
        /// Snapshot construction for host-facing / untrusted input: copies
        /// <paramref name="items"/>, so the caller retains no alias through
        /// which this value could later be mutated.
        /// </summary>
        public ListValue(IEnumerable<Result> items)
            : this(items.ToArray())
        {
        }

        private ListValue(Result[] exclusivelyOwnedItems)
            => items = Array.AsReadOnly(exclusivelyOwnedItems);

        /// <summary>
        /// Trusted ownership-transfer construction: wraps
        /// <paramref name="exclusivelyOwnedItems"/> without copying.
        /// Invariant: after this call the storage belongs to the list value —
        /// the caller must never mutate, reuse, or expose the transferred
        /// array. Use only for storage that provably has no other owner
        /// (e.g. a freshly materialized array).
        /// </summary>
        internal static ListValue TakeOwnership(Result[] exclusivelyOwnedItems)
            => new(exclusivelyOwnedItems);

        /// <summary>
        /// Ordered elements as a read-only view. The view never exposes the
        /// backing storage: casting it to a mutable collection interface
        /// yields an object that rejects every mutation operation.
        /// </summary>
        public IReadOnlyList<Result> Items => items;

        public void Deconstruct(out IReadOnlyList<Result> items) => items = this.items;
    }

    /// <summary>
    /// Normalize: unwrap single-element sequence values recursively. Lists are
    /// exact: their elements normalize (redundant SEQUENCE structure inside a
    /// list still canonicalizes) but the list boundary itself never collapses.
    /// Lean: Result.normalize
    /// </summary>
    public Result Normalize()
    {
        return this switch
        {
            Atom _ => this,
            Str _ => this,
            SequenceValue(var items) =>
                items.Select(r => r.Normalize()).ToArray() switch
                {
                    [var single] => single,
                    var normalized => SequenceValue.TakeOwnership(normalized),
                },
            ListValue(var items) => ListValue.TakeOwnership(items.Select(r => r.Normalize()).ToArray()),
            _ => this,
        };
    }

    /// <summary>
    /// Flatten result to a list of numbers.
    /// Lean: Result.atoms — strings are silently omitted from atom lists, and
    /// list values are opaque to numeric flattening (omitted like strings).
    /// </summary>
    public IReadOnlyList<decimal> ToAtoms()
    {
        return this switch
        {
            Atom(var n) => [n],
            Str _ => [],
            SequenceValue(var items) => items.SelectMany(r => r.ToAtoms()).ToList(),
            ListValue _ => [],
            _ => [],
        };
    }

    /// <summary>
    /// Host-boundary numeric flattening used by <c>Evaluator.RunFlat</c> and
    /// <c>KatLangEngine.EvaluateToAtoms</c>: like <see cref="ToAtoms"/>, but
    /// also opens exact list boundaries so collection-builtin results surface
    /// their numeric contents to embedding hosts. This is a host projection,
    /// not language semantics: the <c>atoms</c> builtin and truth testing keep
    /// lists opaque (<see cref="ToAtoms"/>), and no in-language conversion
    /// between lists and sequences is implied.
    /// Lean: <c>Result.hostAtoms</c>.
    /// </summary>
    public IReadOnlyList<decimal> ToHostAtoms()
    {
        return this switch
        {
            Atom(var n) => [n],
            Str _ => [],
            SequenceValue(var items) => items.SelectMany(r => r.ToHostAtoms()).ToList(),
            ListValue(var items) => items.SelectMany(r => r.ToHostAtoms()).ToList(),
            _ => [],
        };
    }

    /// <summary>
    /// Count emitted top-level values when this result is already in hand.
    /// Empty results emit 0. Any non-empty atomic, string, or sequence value
    /// counts as one value. List values ALWAYS count as one visible value,
    /// including the empty list <c>[]</c> — only the empty SEQUENCE value
    /// <c>()</c> is the invisible-able empty result.
    ///
    /// Lean: <c>Result.valueCount</c>. Used by <c>reduce</c> and <c>map</c>
    /// so sequence-value accumulator / mapped values count as one value.
    /// </summary>
    public int ValueCount()
    {
        return this switch
        {
            SequenceValue(var items) when items.Count == 0 => 0,
            _ => 1,
        };
    }

    /// <summary>
    /// KatLang truth testing used by builtins like <c>if</c>.
    /// Zero is false, any other numeric atom is true.
    /// Returns null when there is no numeric atom to truth-test.
    /// This follows the generic flattened-atoms convention; stricter builtins
    /// such as <c>filter</c> should use <c>SingleAtomicTruthValue()</c>.
    /// Lean: <c>Result.truthValue?</c>.
    /// </summary>
    public bool? TruthValue()
    {
        var atoms = ToAtoms();
        if (atoms.Count == 0)
            return null;
        return atoms[0] != 0;
    }

    /// <summary>
    /// Strict truth testing for <c>filter</c> predicates.
    /// Accepts exactly one atomic numeric value: <c>0</c> is false and any
    /// other atomic number is true. Sequence values, multi-output values, strings, and
    /// empty results are rejected.
    /// Lean: <c>Result.singleAtomicTruthValue?</c>.
    /// </summary>
    public bool? SingleAtomicTruthValue()
    {
        return this switch
        {
            Atom(var n) => n != 0,
            _ => null,
        };
    }

    /// <summary>
    /// Strict numeric extraction for numeric collection builtins such as
    /// <c>min</c>, <c>max</c>, <c>sum</c>, and <c>avg</c>.
    /// Accepts exactly one atomic numeric value and rejects sequence values and strings.
    /// Lean: <c>Result.singleAtomicNumber?</c>.
    /// </summary>
    public decimal? SingleAtomicNumber()
    {
        return this switch
        {
            Atom(var n) => n,
            _ => null,
        };
    }

    /// <summary>
    /// Try to get as a single number.
    /// Returns null if the result is not a single atom (after normalization).
    /// List values never coerce to numbers, not even <c>[5]</c>.
    /// Lean: Result.asInt?
    /// </summary>
    public decimal? AsNum()
    {
        return this switch
        {
            Atom(var n) => n,
            Str _ => null,
            SequenceValue(var items) => Normalize() switch
            {
                Atom(var n) => n,
                _ => null,
            },
            ListValue _ => null,
            _ => null,
        };
    }

    /// <summary>
    /// Extract top-level items from a result.
    /// Atom/string -> singleton list; sequence value -> its items.
    /// A list value stays OPAQUE here: it is one item, so non-spread consumers
    /// (indexing <c>:</c> projection, boundary re-counting) treat a list as a
    /// single exact value. Only postfix spread (<see cref="SpreadItems"/>),
    /// deconstruction binding, and the builtin collection-item view (the
    /// bound collection argument after ordinary fixed binding) open a list
    /// boundary.
    /// Lean: <c>Result.toItems</c>.
    /// </summary>
    public IReadOnlyList<Result> ToItems()
    {
        return this switch
        {
            Atom or Str => [this],
            SequenceValue(var items) => items,
            ListValue _ => [this],
            _ => [],
        };
    }

    /// <summary>
    /// Item view used by postfix spread <c>...</c>: spread opens exactly ONE
    /// structure boundary. Sequence values and exact list values open to
    /// their immediate items; atoms and strings supply themselves as one item.
    /// Lean: <c>Result.spreadItems</c>.
    /// </summary>
    public IReadOnlyList<Result> SpreadItems()
    {
        return this switch
        {
            ListValue(var items) => items,
            _ => ToItems(),
        };
    }

    /// <summary>
    /// Deconstruction-openable structure view shared by the sequence-value
    /// parameter pattern binders: a received sequence value or exact list
    /// value opens to its immediate items; atoms and strings are not openable
    /// (the binders apply their own scalar one-item fallback). Function-call
    /// argument binding never uses this view — a list argument stays one
    /// argument.
    /// Lean: <c>Result.structureItems?</c>.
    /// </summary>
    public IReadOnlyList<Result>? StructureItems()
    {
        return this switch
        {
            SequenceValue(var items) => items,
            ListValue(var items) => items,
            _ => null,
        };
    }

    /// <summary>
    /// Construction preserves structure; selection projects content.
    /// Project one selected value to the top-level content it denotes at the
    /// current boundary, without recursively flattening nested sequence elements.
    /// Lean: <c>Result.projectSelectedContent</c>.
    /// </summary>
    private static (Result Value, int EmittedCount) ProjectSelectedContent(Result selected)
    {
        var items = selected.ToItems();
        return (FromItems(items), items.Count);
    }

    /// <summary>
    /// Construction preserves structure; selection projects content.
    /// <c>:</c> selects one top-level item from the target and projects that
    /// item's content one level: atoms stay atomic, sequence values yield their
    /// immediate members, and nested sequence values remain intact.
    /// Lean: <c>Result.select?</c>.
    /// </summary>
    public (Result Value, int EmittedCount)? SelectProjected(int i)
    {
        var sourceItems = ToItems();
        return i >= 0 && i < sourceItems.Count
            ? ProjectSelectedContent(sourceItems[i])
            : null;
    }

    /// <summary>
    /// Construction preserves structure; selection projects content.
    /// Higher-order sequence iteration uses the same one-level projection rule
    /// for each iterated item as <c>:</c> uses for a selected item.
    /// Lean: callback item projection via <c>Result.projectSelectedContent</c>.
    /// </summary>
    public (Result Value, int EmittedCount) ProjectIteratedContent()
        => ProjectSelectedContent(this);

    /// <summary>
    /// One-level projected selection result for <c>:</c>.
    /// Lean: <c>Result.index?</c>.
    /// </summary>
    public Result? Index(int i)
    {
        return SelectProjected(i)?.Value;
    }

    /// <summary>
    /// Try to get as integer (for indexing).
    /// </summary>
    public int? AsIndex()
    {
        var num = AsNum();
        if (num is null || num < 0 || num != Math.Floor(num.Value))
            return null;
        return (int)num.Value;
    }

    /// <summary>
    /// Create a sequence value from items and normalize.
    /// </summary>
    public static Result FromItems(IEnumerable<Result> items)
    {
        return SequenceValue.TakeOwnership(items.ToArray()).Normalize();
    }

    private sealed class ValueSemanticComparer : IEqualityComparer<Result>
    {
        public bool Equals(Result? x, Result? y)
        {
            if (ReferenceEquals(x, y)) return true;
            if (x is null || y is null) return false;

            return (x, y) switch
            {
                (Atom(var left), Atom(var right)) => left == right,
                (Str(var left), Str(var right)) => StringComparer.Ordinal.Equals(left, right),
                (SequenceValue(var leftItems), SequenceValue(var rightItems)) =>
                    leftItems.Count == rightItems.Count && ItemsEqual(leftItems, rightItems),
                // Lists compare structurally and recursively; a list never
                // equals a sequence value, even with equal elements.
                (ListValue(var leftItems), ListValue(var rightItems)) =>
                    leftItems.Count == rightItems.Count && ItemsEqual(leftItems, rightItems),
                _ => false,
            };
        }

        public int GetHashCode(Result obj)
        {
            var hash = new HashCode();
            AddHashCode(ref hash, obj);
            return hash.ToHashCode();
        }

        private bool ItemsEqual(IReadOnlyList<Result> left, IReadOnlyList<Result> right)
        {
            for (var index = 0; index < left.Count; index++)
            {
                if (!Equals(left[index], right[index]))
                    return false;
            }

            return true;
        }

        private static void AddHashCode(ref HashCode hash, Result result)
        {
            switch (result)
            {
                case Atom(var value):
                    hash.Add(0);
                    hash.Add(value);
                    break;

                case Str(var value):
                    hash.Add(1);
                    hash.Add(value, StringComparer.Ordinal);
                    break;

                case SequenceValue(var items):
                    hash.Add(2);
                    hash.Add(items.Count);
                    foreach (var item in items)
                        AddHashCode(ref hash, item);
                    break;

                case ListValue(var items):
                    hash.Add(3);
                    hash.Add(items.Count);
                    foreach (var item in items)
                        AddHashCode(ref hash, item);
                    break;
            }
        }
    }
}
