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

    internal readonly record struct CountedRootProgramResult(
        CountedResult Output,
        CountedResult? TopLevelProperty);

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
    /// Numeric builtins cache the flattened numeric projection of the collected
    /// top-level items.
    /// </summary>
    private readonly record struct PreparedSequenceBuiltinInput(
        CollectedSequenceBuiltinInput Collected,
        IReadOnlyList<Decimal128>? NumericItems = null)
    {
        public IReadOnlyList<Result> FlattenedItems => Collected.FlattenedItems;
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
