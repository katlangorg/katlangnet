using System.Collections;
using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using KatLang.Runtime;

namespace KatLang;

/// <summary>
/// Result helpers: value inspection and construction, <see cref="Result"/>-to-<see cref="Expr"/> reification, and the counted-result / prepared-evaluation record types (the "Result helpers" section).
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
            case Result.ListValue:
                into.Add(r);
                break;
            case Result.SequenceValue(var items):
                into.AddRange(items);
                break;
        }
    }

    /// <summary>
    /// Evaluate <c>target:selector</c> through the shared one-level projected
    /// selection semantics.
    /// Construction preserves structure; selection projects content.
    /// This helper is the single owner of index-expression error spans: every
    /// error it returns carries the full <c>target:selector</c> span unless it
    /// already carries a more specific inner one (<see cref="WithSpan"/> only
    /// fills a missing span, so a selector sub-expression such as
    /// <c>1 div 0</c> keeps its own). Callers therefore need no wrapping of
    /// their own, and plain and counted evaluation report identical spans.
    /// </summary>
    /// <summary>
    /// Lean: <c>resultToExpr</c>. Reify a normalized result as an expression that
    /// evaluates back to the same shape.
    /// </summary>
    private static Expr EmptyResultExpr()
        => new Expr.EmptySequence(0);

    /// <summary>
    /// Post-order rebuild with explicit frames and a REFERENCE-IDENTITY memo, the same
    /// discipline as <see cref="Result.Normalize"/>: reification is a pure function of the
    /// node — each kind maps to its expression form using only the node's own kind and its
    /// children's reified forms, with no parent, position, span, or evaluator context — so
    /// one node's expression is built once per conversion scope and REUSED at every shared
    /// occurrence. A value is a DAG, not a tree (<c>Wrap = [x, x]</c> + <c>repeat</c>
    /// reaches n+1 distinct nodes through 2^n root-to-leaf paths in n in-budget steps), so
    /// a rebuild proportional to PATHS is exponential on ordinary in-budget values, and no
    /// evaluation budget bounds it: the blow-up happens inside one uncharged conversion.
    /// Lean: <c>resultToExpr</c> — a pure function on inductive values, where reference
    /// sharing is not expressible; the memo is C#-only implementation machinery.
    ///
    /// <para>The produced expression preserves the input's sharing as a shared (acyclic)
    /// <see cref="Expr"/> subgraph — an explicitly supported AST shape (the structural
    /// preflight and the pre-evaluation walker are reference-memoized for exactly this).
    /// Reified nodes are immutable and spanless, no evaluator cache keys on
    /// <see cref="Expr"/> reference identity, and evaluation work is charged per VISIT,
    /// so a shared subexpression still evaluates once per semantic occurrence: sharing
    /// changes host object topology only. Reified values nest as deep as any runtime
    /// value (unbounded — see the depth note on <see cref="Result"/>), so the walk stays
    /// iterative. A direct call owns one operation-local memo; the multi-output
    /// <see cref="CountedArgAlgorithm"/> path deliberately shares one memo across every
    /// emitted root in the ONE wrapper it is building, because those roots can share a
    /// deep subgraph. Nothing is cached on a <see cref="Result"/> or across wrappers.
    /// The direct-call memo is allocated lazily on the first nested descent, so flat
    /// structures allocate none. Leaves reify fresh per converting edge (bounded by the
    /// unique edge count); only structure nodes are memoized. Termination relies on the
    /// acyclicity every constructible value has.</para>
    ///
    /// <para><paramref name="observations"/> is the passive run-scoped observer: one
    /// <see cref="EvaluationObservations.RecordResultToExprStructureExpansion"/> per
    /// structure node expanded (frame pushed), pinned by the shared-value-graph
    /// regressions to the distinct-structure-node count. Internal for those tests;
    /// production reaches this only through <see cref="CountedArgAlgorithm"/>, which
    /// passes the run's observer.</para>
    /// </summary>
    internal static Expr ResultToExpr(Result result, EvaluationObservations? observations = null)
        => ResultToExpr(result, observations, sharedMemo: null);

    /// <summary>
    /// Core conversion. A non-null <paramref name="sharedMemo"/> extends the conversion scope
    /// across several roots of one output bundle; it never escapes the operation that owns it.
    /// Scalar/string/empty-sequence leaves deliberately bypass the memo and remain one fresh
    /// expression per explicit incoming edge.
    /// </summary>
    private static Expr ResultToExpr(
        Result result,
        EvaluationObservations? observations,
        Dictionary<Result, Expr>? sharedMemo)
    {
        if (ResultToExprLeaf(result) is { } leaf)
            return leaf;

        if (sharedMemo is not null && sharedMemo.TryGetValue(result, out var sharedRoot))
            return sharedRoot;

        var frames = new Stack<ResultToExprFrame>();
        // One completed expression per distinct nested structure node reached, for the
        // duration of THIS conversion scope only. A direct call allocates it on the first
        // nested descent; a multi-root counted-argument conversion supplies its wrapper-local
        // memo so sharing between emitted roots is preserved too.
        var memo = sharedMemo;
        frames.Push(new ResultToExprFrame(result));
        observations?.RecordResultToExprStructureExpansion();

        while (true)
        {
            var frame = frames.Peek();

            while (frame.Next < frame.Converted.Length)
            {
                var child = frame.Source[frame.Next];
                if (ResultToExprLeaf(child) is { } childLeaf)
                    frame.Converted[frame.Next++] = childLeaf;
                else if (memo is not null && memo.TryGetValue(child, out var reified))
                    frame.Converted[frame.Next++] = reified;
                else
                    break;
            }

            if (frame.Next < frame.Converted.Length)
            {
                memo ??= new Dictionary<Result, Expr>(ReferenceEqualityComparer.Instance);
                frames.Push(new ResultToExprFrame(frame.Source[frame.Next]));
                observations?.RecordResultToExprStructureExpansion();
                continue;
            }

            frames.Pop();
            var completed = frame.Complete();
            // Commit only after every child has completed. Storing the root matters for the
            // multi-root wrapper scope: a later emitted root may be this exact node or may reach
            // it as a descendant. For a direct call the operation-local entry dies on return.
            memo?.TryAdd(frame.Node, completed);
            if (frames.Count == 0)
                return completed;

            var parent = frames.Peek();
            parent.Converted[parent.Next++] = completed;
        }
    }

    /// <summary>
    /// Reify all top-level results of ONE counted-argument wrapper with one reference-identity
    /// memo. The roots remain separate output occurrences, but any structure shared by their
    /// value graph is converted once and reused. The returned bundle owns the fresh root array;
    /// the memo is discarded before this method returns.
    /// </summary>
    private static OutputBundle ResultsToExprBundle(
        IReadOnlyList<Result> results,
        EvaluationObservations? observations)
    {
        var converted = new Expr[results.Count];
        var memo = new Dictionary<Result, Expr>(ReferenceEqualityComparer.Instance);
        for (var i = 0; i < results.Count; i++)
            converted[i] = ResultToExpr(results[i], observations, memo);
        return OutputBundle.TakeOwnership(converted);
    }

    /// <summary>
    /// Reifies the values <see cref="ResultToExpr"/> does not descend into;
    /// returns null for the two structure shapes that convert child by child.
    /// </summary>
    private static Expr? ResultToExprLeaf(Result result) => result switch
    {
        Result.Atom(var n) => new Expr.Num(n),
        Result.Str(var s) => new Expr.StringLiteral(s),
        // Repeated ordinary parentheses around the empty sequence are redundant
        // surface structure, so any empty-sequence chain reifies as `()`.
        Result.SequenceValue when IsEmptySequenceChain(result)
            => new Expr.EmptySequence(0),
        Result.SequenceValue => null,
        Result.ListValue => null,
        _ => EmptyResultExpr(),
    };

    /// <summary>One in-progress structure rebuild in the <see cref="ResultToExpr"/> walk.</summary>
    private sealed class ResultToExprFrame
    {
        public readonly Result Node;
        public readonly IReadOnlyList<Result> Source;
        public readonly Expr[] Converted;
        public readonly bool IsSequence;
        public int Next;

        public ResultToExprFrame(Result structure)
        {
            Node = structure;
            switch (structure)
            {
                case Result.SequenceValue(var items):
                    Source = items;
                    IsSequence = true;
                    break;
                case Result.ListValue(var items):
                    Source = items;
                    IsSequence = false;
                    break;
                default:
                    throw new ArgumentException(
                        "Result reification frames require a sequence or list value.", nameof(structure));
            }

            Converted = new Expr[Source.Count];
        }

        public Expr Complete()
            => IsSequence
                // A reified sequence value is a capture of its already-evaluated
                // items — a value boundary, not an algorithm. Converted is this
                // frame's exclusively owned fresh array, so ownership transfers
                // without a snapshot copy.
                ? new Expr.Capture(OutputBundle.TakeOwnership(Converted))
                // Exact list values reify as list literals so they round-trip
                // losslessly (a reified `()` element stays one visible list
                // element).
                : new Expr.ListLiteral(OutputBundle.TakeOwnership(Converted));
    }

    /// <summary>
    /// Builds the canonical empty sequence value for an <see cref="Expr.EmptySequence"/>.
    /// Repeated ordinary parentheses around <c>()</c> do not create higher-order
    /// empty sequence values.
    /// </summary>
    private static Result BuildEmptySequenceValue(int _)
        => Result.SequenceValue.TakeOwnership([]);

    /// <summary>
    /// Returns true when <paramref name="result"/> is the empty sequence value or
    /// a redundant chain of one-item sequences ending in it.
    /// </summary>
    private static bool IsEmptySequenceChain(Result result)
    {
        var current = result;
        while (true)
        {
            if (current is not Result.SequenceValue(var items))
                return false;
            if (items.Count == 0)
                return true;
            if (items.Count != 1)
                return false;
            current = items[0];
        }
    }

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

    private readonly record struct PreparedCallArgumentEvaluation(
        CountedResult Counted,
        IReadOnlyList<Result>? ExplicitSequenceValueItems);

    internal readonly record struct CountedRootProgramResult(
        CountedResult Output,
        CountedResult? TopLevelProperty);

    /// <summary>
    /// Evaluated bounds for the inclusive integer <c>range(start, stop)</c>
    /// builtin. The bounds have already passed range's whole-integer validation.
    /// </summary>
    internal readonly record struct InclusiveRange(Decimal128 Start, Decimal128 Stop);

    /// <summary>
    /// Collected collection input records the bound collection argument's
    /// viewed items plus the prepared outer-item supply used by the current
    /// builtin.
    /// </summary>
    private readonly record struct CollectedSequenceBuiltinInput(
        IReadOnlyList<IReadOnlyList<Result>> PerInputItems,
        IReadOnlyList<Result> FlattenedItems)
    {
        public int TotalItemCount => FlattenedItems.Count;

        public bool AnyInputEmpty => PerInputItems.Any(static items => items.Count == 0);
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

    private abstract record PreparedSequenceBuiltinSuffixArg
    {
        /// <summary>
        /// An algorithm-kind suffix argument. <see cref="PreparedValue"/> carries the
        /// slot's already-computed counted value when call-item assembly evaluated it
        /// eagerly (a value-shaped zero-parameter argument): a value-consuming
        /// position (the reduce initial accumulator) must use THAT result instead of
        /// re-evaluating the algorithm channel — the written slot is evaluated
        /// exactly once. Genuine callbacks have no prepared value.
        /// </summary>
        public sealed record AlgorithmArg(KatLang.Algorithm AlgorithmValue) : PreparedSequenceBuiltinSuffixArg
        {
            public CountedResult? PreparedValue { get; init; }
        }

        public sealed record ValueArg(Result ResultValue) : PreparedSequenceBuiltinSuffixArg;

        public sealed record WholeNumberArg(Decimal128 WholeNumberValue) : PreparedSequenceBuiltinSuffixArg;
    }

    /// <summary>
    /// Validate the output shape required by counted builtins that must emit
    /// exactly one top-level value. Non-empty sequence values are valid; the empty
    /// sequence value <c>()</c> and multiple top-level outputs are rejected. (An
    /// empty-sequence output is a visible slot at the output boundary, but these
    /// builtins require a substantive single element.)
    /// Lean: <c>expectSingleValueWith</c>.
    /// </summary>
    private static EvalResult<Result> ExpectSingleEmittedValue(CountedResult output, string errorMessage)
        => output.EmittedCount == 1 && output.Value is not Result.SequenceValue { Items.Count: 0 }
            ? EvalResult<Result>.Ok(output.Value)
            : new EvalError.WithContext(
                errorMessage,
                new EvalError.BadArity());

    /// <summary>
    /// Validate the output shape required by <c>reduce</c>.
    /// Lean: <c>expectSingleAccumulator</c>.
    /// </summary>
    private static EvalResult<Result> ExpectSingleAccumulator(CountedResult output)
        => ExpectSingleEmittedValue(output, "reduce step must return a single accumulator value");

    /// <summary>
    /// Validate the output shape required by <c>map</c>.
    /// Lean: <c>expectSingleMappedElement</c>.
    /// </summary>
    private static EvalResult<Result> ExpectSingleMappedElement(CountedResult output)
        => ExpectSingleEmittedValue(output, "map transform must return a single element");
}
