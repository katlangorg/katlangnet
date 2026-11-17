using System.Collections;
using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang;

/// <summary>
/// Result helpers: value inspection and construction, and the counted-result / prepared-evaluation record types (the "Result helpers" section).
/// Part of the <see cref="Evaluator"/> partial class; the central state, lookup and open resolution,
/// the built-in prelude, and the run entry points remain in <c>Evaluator.cs</c>.
/// </summary>
public static partial class Evaluator
{
    // ── Result helpers ────────────────────────────────────────────────────────

    /// <summary>
    /// Extract top-level items from a result into a list.
    /// Atom/string -> singleton list; sequence value -> its items. A list
    /// value stays opaque (one item), matching <see cref="Result.ToItems"/>.
    /// Lean: Result.toItems.
    /// </summary>
    private static void ResultItems(List<Result> into, Result r)
    {
        switch (r)
        {
            case Result.Atom:
            case Result.Str:
            case Result.Bool:
            case Result.ListValue:
                into.Add(r);
                break;
            case Result.SequenceValue(var items):
                into.AddRange(items);
                break;
        }
    }

    /// <summary>How many items <see cref="ResultItems"/> appends for <paramref name="r"/>, without appending.</summary>
    private static int ResultItemCount(Result r) => r switch
    {
        Result.Atom or Result.Str or Result.Bool or Result.ListValue => 1,
        Result.SequenceValue(var items) => items.Count,
        _ => 0,
    };

    /// <summary>
    /// Builds the canonical empty sequence value for an <see cref="Expr.EmptySequence"/>.
    /// Repeated ordinary parentheses around <c>()</c> do not create higher-order
    /// empty sequence values.
    /// </summary>
    private static Result BuildEmptySequenceValue(int _)
        => Result.SequenceValue.TakeOwnership([]);

    /// <summary>
    /// Counted evaluation result: the normalized value paired with the number of
    /// top-level values emitted at the current algorithm boundary.
    /// Helpers whose names end in <c>Counted</c> preserve this pair instead of
    /// collapsing it to just <see cref="Result"/>.
    /// Lean: <c>CountedResult</c>.
    /// </summary>
    internal readonly record struct CountedResult(Result Value, int EmittedCount);

    /// <summary>
    /// One algorithm-output evaluation prepared for consumers that need both the ordinary
    /// counted value and the evaluated written output slots. <see cref="OutputSlots"/> holds
    /// the same <see cref="Result"/> instances used to construct <see cref="Counted"/>; it is
    /// not a second semantic sequence and never triggers a second evaluation. The backing
    /// storage is owned by the finished evaluation and must never be mutated (the combined
    /// value snapshots its items, so the slot list never aliases into a
    /// <see cref="Result"/>); the hot algorithm-output path deliberately allocates no
    /// per-evaluation read-only wrapper for it. Lean: <c>PreparedAlgorithmOutput</c>.
    /// </summary>
    private readonly record struct PreparedAlgorithmOutput(
        CountedResult Counted,
        IReadOnlyList<Result> OutputSlots);

    /// <summary>
    /// A root program's counted output plus the values of the root's requested top-level
    /// properties: <see cref="TopLevelProperties"/> has one entry per requested name, in request
    /// order, <c>null</c> exactly where the root declares no such property (and everywhere for a
    /// non-program expression). The list is owned by the finished run and never mutated.
    /// </summary>
    internal readonly record struct CountedRootProgramResult(
        CountedResult Output,
        IReadOnlyList<CountedResult?> TopLevelProperties);

    /// <summary>
    /// Evaluated bounds for the inclusive integer <c>range(start, stop)</c>
    /// builtin. The bounds have already passed range's whole-integer validation and
    /// carry the canonical integer representation
    /// (<see cref="CanonicalizeIntegralRangeBound"/>), so enumeration never sees the
    /// quantum or zero sign a bound was written with.
    /// </summary>
    internal readonly record struct InclusiveRange(Decimal128 Start, Decimal128 Stop);

    /// <summary>
    /// Collected collection input records the bound collection argument's
    /// viewed items (the one-level post-binding collection view) used by the
    /// current builtin.
    /// </summary>
    private readonly record struct CollectedSequenceBuiltinInput(IReadOnlyList<Result> FlattenedItems)
    {
        public int TotalItemCount => FlattenedItems.Count;
    }

    /// <summary>
    /// Prepared input for current sequence builtin handlers.
    /// Numeric builtins carry the numeric projection of the collected top-level
    /// items: a read-only view over the validated items
    /// (<see cref="SingleAtomicNumberItems"/>), never a copied list.
    /// </summary>
    private readonly record struct PreparedSequenceBuiltinInput(
        CollectedSequenceBuiltinInput Collected,
        SingleAtomicNumberItems? NumericItems = null)
    {
        public IReadOnlyList<Result> FlattenedItems => Collected.FlattenedItems;
    }

    /// <summary>
    /// The iteration items of an ordinarily bound collection builtin
    /// (<see cref="BoundSequenceBuiltinArguments.IterationItems"/>): item <c>i</c> is the
    /// bound collection's viewed item <c>i</c> with emitted count 1, read from that view on
    /// demand instead of copied. The viewed items are immutable — a list or sequence value's
    /// own read-only storage, or a fresh one-element view — so each read returns exactly the
    /// item a copy made at binding would hold, and a builtin that never iterates
    /// (<c>count</c>, <c>take</c>, …) pays nothing for them. Implementation-only
    /// (November 2026): the copied <c>List&lt;CountedResult&gt;</c> was a 16-byte slot per
    /// item, so every collection builtin over 100,000 items allocated a 1.6 MB
    /// large-object-heap array, a share of the generic pipelines' Gen2 collections.
    /// </summary>
    private sealed class CollectionIterationItems(IReadOnlyList<Result> viewedItems) : IReadOnlyList<CountedResult>
    {
        public int Count => viewedItems.Count;

        public CountedResult this[int index] => new(viewedItems[index], 1);

        public IEnumerator<CountedResult> GetEnumerator()
        {
            for (var index = 0; index < viewedItems.Count; index++)
                yield return new CountedResult(viewedItems[index], 1);
        }

        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
    }

    /// <summary>
    /// The numeric projection of a numeric collection builtin's items
    /// (<see cref="PreparedSequenceBuiltinInput.NumericItems"/>): number <c>i</c> is the
    /// <see cref="Result.SingleAtomicNumber"/> of viewed item <c>i</c>, read on demand. It is
    /// built only after <see cref="CollectSingleAtomicNumbers"/> has checked every item in
    /// index order, so each read is the number that check accepted, and the viewed items are
    /// immutable (see <see cref="CollectionIterationItems"/>). Implementation-only (November
    /// 2026): the projection was a <c>List&lt;Decimal128&gt;</c>, a 16-byte slot per item, so
    /// <c>sum</c>, <c>avg</c>, <c>min</c>, <c>max</c>, <c>order</c> and <c>orderDesc</c> over
    /// 100,000 items each allocated a 1.6 MB large-object-heap array. The handlers take this
    /// sealed type and read it by index: no interface dispatch per number (an
    /// <c>IReadOnlyList&lt;Decimal128&gt;</c> view measured about 40% slower than the copied
    /// list for <c>min</c> over a fresh 100,000-item range) and no enumerator.
    /// </summary>
    private sealed class SingleAtomicNumberItems(IReadOnlyList<Result> validatedItems)
    {
        public int Count => validatedItems.Count;

        public Decimal128 this[int index] => validatedItems[index].SingleAtomicNumber()!.Value;
    }

    /// <summary>
    /// One prepared suffix argument of a sequence builtin (Lean:
    /// <c>PreparedSequenceBuiltinSuffixArg</c>): a C# <c>closed</c> record whose three sealed
    /// nested records are its only kinds. Its consumers are the per-kind projectors
    /// (<c>ExpectPrepared…SuffixArg</c>), which check the prepared kind against the
    /// builtin's registered metadata kind — a mismatch is an internal metadata error, not
    /// an unknown variant.
    /// </summary>
    private closed record PreparedSequenceBuiltinSuffixArg
    {
        private PreparedSequenceBuiltinSuffixArg() { }

        /// <summary>
        /// An algorithm-kind (CALLBACK) suffix argument of an argument that call-item
        /// assembly never value-evaluated (CALL-03 — supplying a callback evaluates nothing),
        /// so it carries no value, only its callable: the supplied <see cref="Cell"/>,
        /// projected when the builtin invokes it, or — for an argument without a cell (a
        /// hand-built plan) — <see cref="AlgorithmValue"/> (<see cref="ResolvePreparedCallback"/>).
        /// Lean: <c>.needAlgorithm</c> / <c>.algorithm</c>.
        /// </summary>
        public sealed record AlgorithmArg(KatLang.Algorithm? AlgorithmValue) : PreparedSequenceBuiltinSuffixArg
        {
            /// <summary>The supplied cell whose CALLABLE projection an invoking slot applies.</summary>
            internal KatLang.Evaluation.NeedCell? Cell { get; init; }

            // A whole collector has no single original argument span. Keep the current
            // written slot as the fallback, just as a loop's step argument does.
            internal Expr? WrittenSource { get; init; }
        }

        public sealed record ValueArg(Result ResultValue) : PreparedSequenceBuiltinSuffixArg;

        public sealed record WholeNumberArg(Decimal128 WholeNumberValue) : PreparedSequenceBuiltinSuffixArg;
    }
}
