using System.Runtime.CompilerServices;

namespace KatLang;

/// <summary>
/// Structured evaluation result.
/// Corresponds to <c>Result</c> in the Lean specification.
///
/// <para>Value NESTING DEPTH is unbounded: evaluation limits bound only
/// per-collection breadth, an in-budget loop builds a depth-n value in n
/// steps, and host-constructed trees are not bounded by the parser at all.
/// Every whole-value traversal over <see cref="Result"/> trees must therefore
/// use an explicit stack instead of native recursion — a recursive walk
/// overflows the host stack on legally built deep values, and
/// <see cref="StackOverflowException"/> terminates the embedding process
/// uncatchably. The traversal stack must hold indexed continuation frames
/// (one frame per open structure level: the collection plus the next child
/// index), NEVER one entry per pending sibling — a legal collection holds up
/// to 100,000 items, so sibling-granular stacks scale with breadth and
/// allocate large-object-heap-sized backing arrays for wide, shallow values.
/// Auxiliary traversal storage is O(nesting depth); storage for a produced
/// value, atom collection, string, or AST is required output, not traversal
/// overhead. Display rendering follows the same no-recursion rule
/// (<c>KatLangEngine.AppendValue</c>).</para>
///
/// <para>A value is also a DAG, not a tree: an immutable child may be shared by
/// many parents (<c>W = [x, x]</c> applied n times reaches n+1 distinct nodes
/// through 2^n root-to-leaf paths), so a walk whose work is proportional to
/// PATHS is exponential on legally built values. The two walks a shared node can
/// blow up — structural equality and structural hashing in
/// <see cref="ValueComparer"/> — therefore memoize by REFERENCE IDENTITY for the
/// duration of ONE top-level operation: equality expands each ordered
/// <c>(left, right)</c> reference pair at most once, hashing computes each
/// node's hash at most once. That memo is the one deliberate exception to the
/// O(nesting depth) rule above: it is O(distinct nodes or pairs actually
/// reached), never O(paths), and it is allocated lazily on the first nested
/// descent so flat values still allocate none. Memo state belongs to one call
/// and is discarded with it; no hash or comparison result is ever cached on a
/// <see cref="Result"/>.</para>
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
    public static IEqualityComparer<Result> ValueComparer { get; } = new ValueSemanticComparer(observations: null);

    /// <summary>
    /// Returns a value comparer bound to <paramref name="observations"/>: the shared observer-less
    /// <see cref="ValueComparer"/> when it is <c>null</c> (every production path), otherwise a fresh
    /// comparer that records the structural work its equality and hash walks perform. The observer
    /// is passive — it changes neither equality, hashing, memoization, nor traversal order — and
    /// belongs to one measured operation, so counts never cross operations, runs, or threads.
    /// </summary>
    internal static IEqualityComparer<Result> CreateObservedValueComparer(ValueTraversalObservations? observations)
        => observations is null ? ValueComparer : new ValueSemanticComparer(observations);

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
    /// Note: C# record equality is not KatLang language equality — KatLang
    /// structural equality uses <see cref="ValueComparer"/>.
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
        if (this is not (SequenceValue or ListValue))
            return this;

        // Post-order rebuild with explicit frames (see the depth note on the
        // class): each frame fills a fresh array of normalized children, and a
        // completed frame hands its value to the parent frame's open slot.
        var frames = new Stack<NormalizeFrame>();
        frames.Push(new NormalizeFrame(this));
        Result? completed = null;

        while (true)
        {
            var frame = frames.Peek();
            if (completed is not null)
            {
                frame.Normalized[frame.Next++] = completed;
                completed = null;
            }

            while (frame.Next < frame.Normalized.Length)
            {
                var child = frame.Source[frame.Next];
                if (child is SequenceValue or ListValue)
                    break;
                frame.Normalized[frame.Next++] = child;
            }

            if (frame.Next < frame.Normalized.Length)
            {
                frames.Push(new NormalizeFrame(frame.Source[frame.Next]));
                continue;
            }

            frames.Pop();
            completed = frame.Complete();
            if (frames.Count == 0)
                return completed;
        }
    }

    /// <summary>One in-progress structure rebuild in the <see cref="Normalize"/> walk.</summary>
    private sealed class NormalizeFrame
    {
        public readonly IReadOnlyList<Result> Source;
        public readonly Result[] Normalized;
        public readonly bool IsSequence;
        public int Next;

        public NormalizeFrame(Result structure)
        {
            switch (structure)
            {
                case SequenceValue(var items):
                    Source = items;
                    IsSequence = true;
                    break;
                case ListValue(var items):
                    Source = items;
                    IsSequence = false;
                    break;
                default:
                    throw new ArgumentException(
                        "Normalize frames require a sequence or list value.", nameof(structure));
            }

            Normalized = new Result[Source.Count];
        }

        public Result Complete()
        {
            if (IsSequence)
                return Normalized is [var single] ? single : SequenceValue.TakeOwnership(Normalized);
            return ListValue.TakeOwnership(Normalized);
        }
    }

    /// <summary>
    /// Truth-testing numeric flattening: the list of numeric atoms reachable
    /// through SEQUENCE boundaries only. Strings are silently omitted, and
    /// list values are opaque (omitted like strings), so lists never gain a
    /// truth value. This view backs <see cref="TruthValue"/> and is NOT the
    /// <c>atoms</c> builtin's collector — that is <see cref="LanguageAtoms"/>,
    /// which also opens list boundaries.
    /// Lean: Result.atoms.
    /// </summary>
    public IReadOnlyList<decimal> ToAtoms()
    {
        if (this is Atom(var single))
            return [single];
        if (this is not SequenceValue(var rootItems))
            return [];

        // Indexed continuation frames (see the depth note on the class): the
        // collected list is the required output; traversal storage is one
        // suspended frame per open sequence level.
        var collected = new List<decimal>();
        var suspended = new Stack<(IReadOnlyList<Result> Items, int Next)>();
        var items = rootItems;
        var next = 0;

        while (true)
        {
            if (next >= items.Count)
            {
                if (suspended.Count == 0) return collected;
                (items, next) = suspended.Pop();
                continue;
            }

            var child = items[next];
            next++;

            switch (child)
            {
                case Atom(var n):
                    collected.Add(n);
                    break;
                case SequenceValue(var childItems):
                    if (childItems.Count > 0)
                    {
                        // Tail descent: a parent with no children left to
                        // visit has no continuation worth suspending.
                        if (next < items.Count)
                            suspended.Push((items, next));
                        (items, next) = (childItems, 0);
                    }

                    break;
                default:
                    break; // strings and opaque list values contribute no atoms
            }
        }
    }

    /// <summary>
    /// Language-level atom collection for the <c>atoms</c> builtin:
    /// recursively collect numeric atoms depth-first, left-to-right, through
    /// BOTH sequence and exact list boundaries. Strings and any other
    /// non-numeric leaves contribute no atoms. The builtin materializes this
    /// collection as ONE exact immutable list value.
    /// Deliberately separate from <see cref="ToAtoms"/> (truth testing stays
    /// list-opaque) and <see cref="ToHostAtoms"/> (host projection returns
    /// host decimals), so none of the three contracts can drift through
    /// shared code.
    /// Lean: <c>Result.languageAtoms</c>.
    /// </summary>
    public IReadOnlyList<decimal> LanguageAtoms()
    {
        _ = TryLanguageAtoms(long.MaxValue, out var collected);
        return collected;
    }

    /// <summary>
    /// Bounded form of <see cref="LanguageAtoms"/>: stops collecting as soon as more than
    /// <paramref name="maxItems"/> atoms have been found and returns <c>false</c>.
    ///
    /// <para>Atom collection is the one collection producer whose output can be far larger
    /// than its input — nesting a value inside itself repeatedly (<c>[A, A]</c>) doubles the
    /// atom count per level while adding only two item slots — so its result cannot be
    /// bounded by counting the input. Stopping the traversal early keeps the intermediate
    /// list bounded too, which a count-first prepass would not.</para>
    /// </summary>
    internal bool TryLanguageAtoms(long maxItems, out IReadOnlyList<decimal> atoms)
    {
        // Indexed continuation frames (see the depth note on the class): the
        // collected list is the required output; traversal storage is one
        // suspended frame per open structure level.
        var collected = new List<decimal>();
        atoms = collected;

        IReadOnlyList<Result> items;
        switch (this)
        {
            case Atom(var single):
                if (collected.Count >= maxItems) return false;
                collected.Add(single);
                return true;
            case SequenceValue(var rootItems):
                items = rootItems;
                break;
            case ListValue(var rootItems):
                items = rootItems;
                break;
            default:
                return true; // strings and any other non-numeric leaves contribute no atoms
        }

        var suspended = new Stack<(IReadOnlyList<Result> Items, int Next)>();
        var next = 0;

        while (true)
        {
            if (next >= items.Count)
            {
                if (suspended.Count == 0) return true;
                (items, next) = suspended.Pop();
                continue;
            }

            var child = items[next];
            next++;

            switch (child)
            {
                case Atom(var n):
                    if (collected.Count >= maxItems) return false;
                    collected.Add(n);
                    break;
                case SequenceValue(var childItems):
                    if (childItems.Count > 0)
                    {
                        // Tail descent: a parent with no children left to
                        // visit has no continuation worth suspending.
                        if (next < items.Count)
                            suspended.Push((items, next));
                        (items, next) = (childItems, 0);
                    }

                    break;
                case ListValue(var childItems):
                    if (childItems.Count > 0)
                    {
                        // Tail descent: a parent with no children left to
                        // visit has no continuation worth suspending.
                        if (next < items.Count)
                            suspended.Push((items, next));
                        (items, next) = (childItems, 0);
                    }

                    break;
                default:
                    break; // strings and any other non-numeric leaves contribute no atoms
            }
        }
    }

    /// <summary>
    /// Host-boundary numeric flattening used by <c>Evaluator.RunFlat</c> and
    /// <c>KatLangEngine.EvaluateToAtoms</c>: like <see cref="ToAtoms"/>, but
    /// also opens exact list boundaries so collection-builtin results surface
    /// their numeric contents to embedding hosts. This is a host projection,
    /// not language semantics: truth testing keeps lists opaque
    /// (<see cref="ToAtoms"/>), the <c>atoms</c> builtin collects through its
    /// own separate collector (<see cref="LanguageAtoms"/>) and returns one
    /// exact list value rather than host decimals, and no in-language
    /// conversion between lists and sequences is implied.
    /// Lean: <c>Result.hostAtoms</c>.
    /// </summary>
    public IReadOnlyList<decimal> ToHostAtoms()
    {
        _ = TryToHostAtoms(long.MaxValue, out var atoms);
        return atoms;
    }

    /// <summary>
    /// Bounded form of <see cref="ToHostAtoms"/>: stops as soon as more than
    /// <paramref name="maxItems"/> host atoms have been produced and returns <c>false</c>.
    ///
    /// <para>The host projection opens BOTH sequence and list boundaries recursively, so
    /// like <see cref="TryLanguageAtoms"/> it can produce far more atoms than the value has
    /// item slots. It is a separate traversal from the language-level collector on purpose:
    /// the two are distinct contracts and must not drift through shared code.</para>
    /// </summary>
    internal bool TryToHostAtoms(long maxItems, out IReadOnlyList<decimal> atoms)
    {
        // Indexed continuation frames (see the depth note on the class): the
        // collected list is the required output; traversal storage is one
        // suspended frame per open structure level.
        var collected = new List<decimal>();
        atoms = collected;

        IReadOnlyList<Result> items;
        switch (this)
        {
            case Atom(var single):
                if (collected.Count >= maxItems) return false;
                collected.Add(single);
                return true;
            case Str:
                return true;
            case SequenceValue(var rootItems):
                items = rootItems;
                break;
            case ListValue(var rootItems):
                items = rootItems;
                break;
            default:
                return true;
        }

        var suspended = new Stack<(IReadOnlyList<Result> Items, int Next)>();
        var next = 0;

        while (true)
        {
            if (next >= items.Count)
            {
                if (suspended.Count == 0) return true;
                (items, next) = suspended.Pop();
                continue;
            }

            var child = items[next];
            next++;

            switch (child)
            {
                case Atom(var n):
                    if (collected.Count >= maxItems) return false;
                    collected.Add(n);
                    break;
                case Str:
                    break;
                case SequenceValue(var childItems):
                    if (childItems.Count > 0)
                    {
                        // Tail descent: a parent with no children left to
                        // visit has no continuation worth suspending.
                        if (next < items.Count)
                            suspended.Push((items, next));
                        (items, next) = (childItems, 0);
                    }

                    break;
                case ListValue(var childItems):
                    if (childItems.Count > 0)
                    {
                        // Tail descent: a parent with no children left to
                        // visit has no continuation worth suspending.
                        if (next < items.Count)
                            suspended.Push((items, next));
                        (items, next) = (childItems, 0);
                    }

                    break;
                default:
                    break;
            }
        }
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
    /// (boundary re-counting, call binding) treat a list as a single exact
    /// value. Only the spread marker (<see cref="SpreadItems"/>), deconstruction
    /// binding, the indexing <c>:</c> projection target view
    /// (<see cref="ProjectionItems"/>), and the builtin collection-item view
    /// (the bound collection argument after ordinary fixed binding) open a
    /// list boundary.
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
    /// Item view used by the spread expression (<c>expr*</c>): spread opens
    /// exactly ONE structure boundary.
    /// Sequence values and exact list values open to their immediate items;
    /// atoms and strings supply themselves as one item.
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
    /// Projection target view for indexing <c>:</c>: a sequence value or exact
    /// list value opens to its immediate elements; every other value follows
    /// <see cref="ToItems"/>. This opens the TARGET boundary only — the
    /// selected element itself is returned exactly as stored, so a nested
    /// list element stays one opaque list.
    /// Lean: <c>Result.projectionItems</c>.
    /// </summary>
    private IReadOnlyList<Result> ProjectionItems()
    {
        return this switch
        {
            ListValue(var items) => items,
            _ => ToItems(),
        };
    }

    /// <summary>
    /// Construction preserves structure; selection projects content.
    /// <c>:</c> selects one top-level item from a sequence or exact list
    /// target and projects that item's content one level: atoms stay atomic,
    /// sequence values yield their immediate members, and nested sequence and
    /// list values remain intact.
    /// Lean: <c>Result.select?</c>.
    /// </summary>
    public (Result Value, int EmittedCount)? SelectProjected(int i)
    {
        var sourceItems = ProjectionItems();
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
    /// Lean: <c>Result.select?</c>.
    /// </summary>
    public Result? Index(int i)
    {
        return SelectProjected(i)?.Value;
    }

    /// <summary>
    /// Try to get as integer (for indexing). A value beyond the host int
    /// range can never be a valid position, so it is not an index.
    /// </summary>
    public int? AsIndex()
    {
        var num = AsNum();
        if (num is null || num < 0 || num > int.MaxValue || num != Math.Floor(num.Value))
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

    /// <summary>
    /// KatLang value semantics over possibly SHARED value graphs. Both walks memoize by REFERENCE
    /// identity for the duration of one top-level operation, because an immutable value is a DAG,
    /// not a tree: <c>W = [x, x]</c> applied n times builds a value with n+1 distinct nodes but
    /// 2^n root-to-leaf paths, and a walk that expands paths instead of nodes is exponential in n.
    /// The memos hold ONLY object references; they never call value equality or the structural hash
    /// on themselves, which would re-enter the very walks they bound.
    /// </summary>
    private sealed class ValueSemanticComparer(ValueTraversalObservations? observations)
        : IEqualityComparer<Result>
    {
        // Value-kind tags mixed into every structural hash, so a list value never hashes like a
        // sequence value over the same elements. These are the tags the previous streaming hash
        // used, kept for continuity of the recipe.
        private const int AtomTag = 0;
        private const int StrTag = 1;
        private const int SequenceTag = 2;
        private const int ListTag = 3;

        /// <summary>
        /// Placeholder stored for a structure node while its own hash is still being folded, and
        /// the contribution of a value that is neither leaf nor structure. KatLang values cannot be
        /// cyclic — every <see cref="Result"/> is immutable and built from children that already
        /// exist, and public construction snapshots its input — so a node can never be
        /// re-encountered while it is still in progress, and this placeholder is never read for any
        /// constructible value. Seeding it anyway costs one dictionary write per node and makes the
        /// walk TOTAL: an invariant-violating aliased graph terminates with an arbitrary but stable
        /// hash instead of looping forever inside the host.
        /// </summary>
        private const int InProgressHash = 0;

        public bool Equals(Result? x, Result? y)
        {
            if (ReferenceEquals(x, y)) return true;
            if (x is null || y is null) return false;

            IReadOnlyList<Result> leftItems;
            IReadOnlyList<Result> rightItems;
            switch (x, y)
            {
                case (Atom(var leftValue), Atom(var rightValue)):
                    return leftValue == rightValue;

                case (Str(var leftValue), Str(var rightValue)):
                    return StringComparer.Ordinal.Equals(leftValue, rightValue);

                case (SequenceValue(var left), SequenceValue(var right)):
                    if (left.Count != right.Count) return false;
                    (leftItems, rightItems) = (left, right);
                    break;

                // Lists compare structurally element by element; a list never
                // equals a sequence value, even with equal elements.
                case (ListValue(var left), ListValue(var right)):
                    if (left.Count != right.Count) return false;
                    (leftItems, rightItems) = (left, right);
                    break;

                default:
                    return false;
            }

            observations?.RecordEqualityPairExpansion();

            // Pairwise structural walk with indexed continuation frames (see
            // the depth note on the class): the registers hold the current
            // collection pair and next child index, and the stack holds one
            // suspended parent frame per open structure level — never one
            // entry per pending sibling. Pairs compare left to right, and the
            // reference fast path applies at every level so shared subtrees
            // short-circuit.
            //
            // EXPANDED-PAIR MEMO (this operation only): a nested pair is expanded at most once per
            // top-level comparison, keyed by the ORDERED pair of object references. The reference
            // fast path above helps only when the SAME object is on both sides; two independently
            // built equal DAGs share no object at all, so without this memo the walk expands paths
            // (2^n for the n-fold [x, x] shape) instead of deciding the n+1 distinct pairs.
            // Recording a pair when it is DESCENDED INTO — before its children are compared — is
            // what makes "already expanded" mean "already decided equal": the walk RETURNS FALSE
            // the instant any mismatch is found anywhere, so a pair can only be re-encountered
            // after its own subtree finished without one. A pair is never re-encountered while it
            // is still in progress, since that needs a value reachable from itself (see
            // InProgressHash) — and were such a graph ever handed in, skipping the repeat is
            // exactly the coinductive answer and still terminates instead of hanging the host.
            var suspended = new Stack<(IReadOnlyList<Result> Left, IReadOnlyList<Result> Right, int Next)>();
            HashSet<ReferencePair>? expandedPairs = null;
            var next = 0;

            while (true)
            {
                if (next >= leftItems.Count)
                {
                    if (suspended.Count == 0) return true;
                    (leftItems, rightItems, next) = suspended.Pop();
                    continue;
                }

                var left = leftItems[next];
                var right = rightItems[next];
                next++;

                if (ReferenceEquals(left, right)) continue;
                if (left is null || right is null) return false;

                IReadOnlyList<Result> childLeft;
                IReadOnlyList<Result> childRight;
                switch (left, right)
                {
                    case (Atom(var leftValue), Atom(var rightValue)):
                        if (leftValue != rightValue) return false;
                        continue;

                    case (Str(var leftValue), Str(var rightValue)):
                        if (!StringComparer.Ordinal.Equals(leftValue, rightValue)) return false;
                        continue;

                    case (SequenceValue(var childLeftItems), SequenceValue(var childRightItems)):
                        if (childLeftItems.Count != childRightItems.Count) return false;
                        (childLeft, childRight) = (childLeftItems, childRightItems);
                        break;

                    case (ListValue(var childLeftItems), ListValue(var childRightItems)):
                        if (childLeftItems.Count != childRightItems.Count) return false;
                        (childLeft, childRight) = (childLeftItems, childRightItems);
                        break;

                    default:
                        return false;
                }

                // Equal empty collections are decided by the count check alone.
                if (childLeft.Count == 0) continue;

                // Allocated on the first nested descent, so a comparison that never leaves the top
                // level (two flat collections of leaves) allocates no memo at all.
                expandedPairs ??= [];
                if (!expandedPairs.Add(new ReferencePair(left, right))) continue;

                observations?.RecordEqualityPairExpansion();

                // Tail descent: a parent with no children left to visit has no
                // continuation worth suspending.
                if (next < leftItems.Count)
                    suspended.Push((leftItems, rightItems, next));
                (leftItems, rightItems, next) = (childLeft, childRight, 0);
            }
        }

        public int GetHashCode(Result obj)
        {
            // Structural hash COMPOSED BOTTOM-UP: every node mixes its kind tag, its child count,
            // and its children's hashes, so one node contributes exactly one int — and that int can
            // be memoized by reference and replayed at every later occurrence of the same shared
            // node. The previous walk streamed each reachable node's tokens into ONE accumulator in
            // pre-order, a shape that admits no memoization at all: a subtree's contribution
            // depends on the accumulator state and queue position it lands in, so it can only be
            // reproduced by re-walking the subtree, once per path reaching it (exponential on a
            // shared DAG). Composition is therefore required here, not a convenience.
            //
            // The equality contract is preserved BY CONSTRUCTION: equal values have the same kind
            // tag and child count and pairwise-equal children, so by induction they fold to the
            // same hash (equal decimals and ordinal-equal strings already hash equal). Hash VALUES
            // are not observable and never were — System.HashCode is seeded per process, so they
            // already differed between runs, and no KatLang result depends on them (distinct keeps
            // input order and uses its set only as a duplicate filter).
            if (TryHashLeaf(obj, out var leafHash))
                return leafHash;
            if (!TryOpenStructure(obj, out var tag, out var items))
                return InProgressHash;

            // Post-order visit with indexed continuation frames (see the depth note on the class):
            // the registers hold the node being folded, its collection, the next child index, and
            // its accumulator; the stack holds one suspended parent frame per open structure level,
            // never one entry per pending sibling. A parent must survive its last child — it still
            // has that child's hash to fold — so this walk keeps the frame the pre-order walk could
            // drop; the memo below already makes storage proportional to distinct nodes.
            //
            // NODE-HASH MEMO (this operation only): each distinct non-empty structure node is
            // expanded at most once per top-level hash, keyed by object reference. It is seeded
            // with InProgressHash at descent and overwritten with the real hash at completion.
            // Lifetime is deliberately ONE call: no hash is cached on a Result, so no per-value
            // state is added and a second GetHashCode recomputes the graph.
            var node = obj;
            var accumulator = new HashCode();
            accumulator.Add(tag);
            accumulator.Add(items.Count);
            var next = 0;

            var suspended = new Stack<(Result Node, IReadOnlyList<Result> Items, int Next, HashCode Accumulator)>();
            Dictionary<Result, int>? structureHashes = null;

            observations?.RecordHashStructureExpansion();

            while (true)
            {
                if (next >= items.Count)
                {
                    var nodeHash = accumulator.ToHashCode();
                    if (structureHashes is not null)
                        structureHashes[node] = nodeHash;
                    if (suspended.Count == 0)
                        return nodeHash;

                    (node, items, next, accumulator) = suspended.Pop();
                    accumulator.Add(nodeHash);
                    continue;
                }

                var child = items[next];
                next++;

                int childTag;
                IReadOnlyList<Result> childItems;
                switch (child)
                {
                    // A leaf streams its own tokens straight into its parent's fold, exactly as the
                    // previous walk did: it opens no path, so it needs neither a node hash of its
                    // own nor a memo entry, and folding it in place keeps flat collections at their
                    // previous cost.
                    case Atom(var number):
                        accumulator.Add(AtomTag);
                        accumulator.Add(number);
                        continue;

                    case Str(var text):
                        accumulator.Add(StrTag);
                        accumulator.Add(text, StringComparer.Ordinal);
                        continue;

                    case SequenceValue(var sequenceItems):
                        (childTag, childItems) = (SequenceTag, sequenceItems);
                        break;

                    case ListValue(var listItems):
                        (childTag, childItems) = (ListTag, listItems);
                        break;

                    default:
                        continue;
                }

                if (childItems.Count == 0)
                {
                    accumulator.Add(EmptyStructureHash(childTag));
                    continue;
                }

                if (structureHashes is not null && structureHashes.TryGetValue(child, out var memoized))
                {
                    accumulator.Add(memoized);
                    continue;
                }

                // Allocated on the first nested descent, so hashing a flat collection of leaves
                // allocates no memo at all.
                structureHashes ??= new Dictionary<Result, int>(ReferenceEqualityComparer.Instance);
                structureHashes[child] = InProgressHash;

                observations?.RecordHashStructureExpansion();

                suspended.Push((node, items, next, accumulator));
                (node, items, next) = (child, childItems, 0);
                accumulator = new HashCode();
                accumulator.Add(childTag);
                accumulator.Add(childItems.Count);
            }
        }

        /// <summary>
        /// Hash of a leaf value, or <c>false</c> when the value is a structure. Leaves contribute in
        /// place: they open no path, so nothing about them can expand exponentially.
        /// </summary>
        private static bool TryHashLeaf(Result value, out int hash)
        {
            var leaf = new HashCode();
            switch (value)
            {
                case Atom(var number):
                    leaf.Add(AtomTag);
                    leaf.Add(number);
                    hash = leaf.ToHashCode();
                    return true;

                case Str(var text):
                    leaf.Add(StrTag);
                    leaf.Add(text, StringComparer.Ordinal);
                    hash = leaf.ToHashCode();
                    return true;

                default:
                    hash = 0;
                    return false;
            }
        }

        /// <summary>Kind tag and ordered children of a structure value, or <c>false</c> for a leaf.</summary>
        private static bool TryOpenStructure(Result value, out int tag, out IReadOnlyList<Result> items)
        {
            switch (value)
            {
                case SequenceValue(var sequenceItems):
                    (tag, items) = (SequenceTag, sequenceItems);
                    return true;

                case ListValue(var listItems):
                    (tag, items) = (ListTag, listItems);
                    return true;

                default:
                    (tag, items) = (0, []);
                    return false;
            }
        }

        /// <summary>Hash of an empty structure: the fold with no children to mix in.</summary>
        private static int EmptyStructureHash(int tag)
        {
            var empty = new HashCode();
            empty.Add(tag);
            empty.Add(0);
            return empty.ToHashCode();
        }

        /// <summary>
        /// One ordered pair of <see cref="Result"/> OBJECT REFERENCES, the equality memo's key.
        /// Identity is deliberately <see cref="object.ReferenceEquals"/> plus
        /// <see cref="RuntimeHelpers.GetHashCode"/> on both sides — the same reference-identity
        /// discipline the AST preflight and the evaluator's caches use. Keying the memo on value
        /// equality or on the structural hash would re-enter the walks the memo exists to bound,
        /// and record equality on <see cref="Result"/> is not KatLang value equality either.
        /// </summary>
        private readonly struct ReferencePair : IEquatable<ReferencePair>
        {
            private readonly Result left;
            private readonly Result right;

            internal ReferencePair(Result left, Result right)
            {
                this.left = left;
                this.right = right;
            }

            public bool Equals(ReferencePair other)
                => ReferenceEquals(left, other.left) && ReferenceEquals(right, other.right);

            public override bool Equals(object? obj)
                => obj is ReferencePair other && Equals(other);

            public override int GetHashCode()
                => HashCode.Combine(RuntimeHelpers.GetHashCode(left), RuntimeHelpers.GetHashCode(right));
        }
    }
}
