using System.Collections;
using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang;

/// <summary>
/// Expression evaluation: the iterative expression-spine machine, the Eval/EvalCounted dispatch, and native/host/Math dispatch including Math.Random sampling (the "Iterative expression-spine evaluation" and "Main eval" sections).
/// Part of the <see cref="Evaluator"/> partial class; the central state, lookup and open resolution,
/// the built-in prelude, and the run entry points remain in <c>Evaluator.cs</c>.
/// </summary>
public static partial class Evaluator
{
    // ── Iterative expression-spine evaluation ───────────────────────────────

    /// <summary>
    /// The pure-expression composite node kinds whose evaluation is driven by the
    /// iterative spine machine (<see cref="EvalExpressionSpineCounted"/>) instead of
    /// CLR recursion: unary and binary operators, comparison chains, postfix selection
    /// (whose receiver and ordinary selector slots are machine children), list literals,
    /// and interpolated strings (STR-02). These are the shapes whose
    /// recursive evaluation frames were measured to exhaust a 1 MiB stack within the
    /// structural depth ceiling (binary/unary spines at ~330-340 nodes, index spines at
    /// ~270-285, list spines at ~290-300 in Debug; a recursive interpolated string costs
    /// ~6.8 KB per level on the async twin, so a ceiling-depth nesting would overflow
    /// with no stack probe on its path), so within-ceiling safety REQUIRES that their
    /// nesting consume no proportional call stack. Algorithm-carrying kinds (blocks, calls, dot-calls) stay on their
    /// recursive paths and are bounded by the structural ceiling instead; the internal
    /// sequence-join kinds already have their own iterative handling
    /// (<see cref="EvalSequenceConstructCounted"/>, <see cref="EvalSequenceSpreadCounted"/>).
    /// <para>It is also the ONE decision of whether a child expression is pushed as a machine
    /// frame (no dispatch head) or delegated through <see cref="Eval"/> (one dispatch head),
    /// which is why the planned loop evaluator reads it too: a planned expression charges the
    /// expression-work checkpoints of exactly the dispatch this predicate selects
    /// (<c>LoopOptimizer.EvalLoopExprPlan</c>).</para>
    /// </summary>
    internal static bool IsExpressionSpineNode(Expr expr)
        => expr is Expr.Unary or Expr.Binary or Expr.Comparison or Expr.Index or Expr.ListLiteral or Expr.InterpolatedString;

    /// <summary>
    /// A ListLiteral frame's element accumulator together with its SEC-01 transient bound
    /// (<see cref="TransientSupply"/>): once it overflows, the remaining elements are evaluated
    /// count-only and the list's own reservation refuses its full size. The bound lives here, not
    /// in <see cref="ExpressionSpineFrame"/>, so the frame — allocated sixteen at a time per spine
    /// run — does not grow.
    /// </summary>
    private sealed class ListSlotAccumulator : List<Result>
    {
        public TransientSupply Supply;
    }

    /// <summary>
    /// A ListLiteral frame's element accumulator. Only a literal with an explicit spread element can
    /// ever expand its supply, so only such a literal carries the bound (<see cref="ListSlotAccumulator"/>);
    /// any other literal's supply is purely written — never expanded, never overflowed, its total
    /// always its count — and accumulates in a plain list, without the bound's per-literal storage
    /// (SEC-01-FU allocation follow-up). The two accumulators admit, retain and refuse identically.
    /// </summary>
    private static List<Result> NewListSlots(IReadOnlyList<Expr> elements)
    {
        for (var i = 0; i < elements.Count; i++)
        {
            if (elements[i] is Expr.SequenceSpread)
                return new ListSlotAccumulator();
        }

        return [];
    }

    /// <summary>One written element's value into a ListLiteral accumulator (<see cref="NewListSlots"/>).</summary>
    private static void AddListSlot(List<Result> slots, Result slot, EvaluationBudget budget)
    {
        if (slots is ListSlotAccumulator bounded)
            AddSlotBounded(bounded, slot, budget, ref bounded.Supply);
        else
            slots.Add(slot);
    }

    /// <summary>One element's slots into a ListLiteral accumulator (<see cref="NewListSlots"/>).</summary>
    private static void AddListSlots(List<Result> slots, IReadOnlyList<Result> values, EvaluationBudget budget, bool expansion)
    {
        if (slots is ListSlotAccumulator bounded)
            AddSlotsBounded(bounded, values, budget, ref bounded.Supply, expansion);
        else
            slots.AddRange(values);
    }

    /// <summary>The ListLiteral supply's full size: an overflowed accumulator's counted total, else its count.</summary>
    private static long ListSlotTotal(List<Result> slots)
        => slots is ListSlotAccumulator bounded ? bounded.Supply.Total : slots.Count;

    /// <summary>One in-progress spine node in <see cref="EvalExpressionSpineCounted"/>.</summary>
    private struct ExpressionSpineFrame(Expr node)
    {
        public readonly Expr Node = node;

        /// <summary>
        /// Unary/Binary: completed child count. Index: 0 while the receiver is in flight,
        /// then 1 + the position of the supplied selector being demanded. ListLiteral: next
        /// element index. Comparison: the index of the operand being evaluated (0 = the first
        /// operand, k = the operand of link k-1). InterpolatedString: the index of the link
        /// whose hole is being evaluated.
        /// </summary>
        public int Phase;

        /// <summary>
        /// Binary left value / Index RECEIVER value (demanded once, read by every selector) /
        /// Comparison PREVIOUS operand value (the left side of the next link — reused, never
        /// re-evaluated), once evaluated.
        /// </summary>
        public Result? FirstValue;

        /// <summary>Comparison: true once any link has compared false (the chain still runs to its end).</summary>
        public bool ComparisonFailed;

        /// <summary>
        /// ListLiteral element accumulator (exact written slots, spread already expanded) /
        /// Index accumulator of the values selected so far (allocated for two or more selectors).
        /// </summary>
        public List<Result>? ListItems;

        /// <summary>
        /// Index: the formed selector supply when a selector slot is an explicit spread
        /// (<see cref="FormSelectionSupply"/>); null when every slot is an ordinary written selector,
        /// whose supply is the slots themselves.
        /// </summary>
        public List<SuppliedSelector>? Selection;

        /// <summary>InterpolatedString text accumulator; created on the frame's first visit.</summary>
        public InterpolatedTextBuilder? Text;
    }

    /// <summary>
    /// Evaluates one maximal pure-expression spine with an explicit frame stack,
    /// replicating the recursive per-kind evaluation EXACTLY — child order, error
    /// decoration, spans, budget reservations, and emitted counts — while consuming
    /// O(1) CLR stack per spine node. Children that are not spine kinds are delegated
    /// to the ordinary recursive paths (one bounded frame layer; the structural
    /// preflight bounds how many such layers a path can alternate through).
    ///
    /// <para>Per-kind semantics preserved here (previously the recursive
    /// <c>Eval</c> cases and the former per-kind counted helpers):</para>
    /// <list type="bullet">
    ///   <item><b>Unary</b>: non-scalar values, including <c>()</c>, are rejected; strings are a
    ///   <see cref="EvalError.TypeMismatch"/> at the unary expression's span; operand
    ///   errors propagate untouched. Lean: <c>eval</c> unary case.</item>
    ///   <item><b>Binary</b>: left then right, each error propagating untouched, then
    ///   <see cref="ApplyBinaryOperator"/> — where the empty sequence value is an
    ///   ORDINARY operand, not an identity (SYN-01). Lean: <c>eval</c> binary
    ///   case.</item>
    ///   <item><b>Comparison</b>: the first operand, then link by link — evaluate the
    ///   link's operand, compare the PREVIOUS operand's value with it through
    ///   <see cref="ApplyComparison"/> (every operand evaluated exactly once; the
    ///   previous VALUE is reused, never its expression), accumulate the verdict, and
    ///   continue: a <c>false</c> link never stops the chain (eager Boolean composition),
    ///   an error does (later operands are not evaluated). Lean:
    ///   <c>evalComparisonCounted</c>.</item>
    ///   <item><b>Index</b> (variadic postfix selection <c>R[s1, …, sn]</c>): (1) the receiver,
    ///   ONCE, as a machine child — a receiver failure gains the selection's span when it has
    ///   none and ends it, even with no selector; (2) the selector supply is formed like a call's
    ///   (<see cref="FormSelectionSupply"/>, only when a slot is an explicit spread: every spread
    ///   runs now, in written order); (3) each supplied selector LEFT TO RIGHT, one machine
    ///   transition each — an ordinary slot demanded as a machine child at its turn (its
    ///   suspended cell's first demand), a spread-formed cell demanded directly — validated and
    ///   selected through the ONE <see cref="SelectPosition"/>, the first failure ending the
    ///   selection (no later selector is demanded; a selector failure is positioned at its
    ///   written slot, else the selection); (4) the selected values captured by ordinary
    ///   normalization of the result grouping (<see cref="MakeCheckedSequenceCapture"/>: zero →
    ///   <c>()</c>, one → the value itself, several → one sequence kept whole) and RE-COUNTED as
    ///   one plain value (selection is a value boundary). Lean: the <c>.index</c> arm of
    ///   <c>evalCounted</c> (<c>selectWith</c>, <c>selectionResult</c>).</item>
    ///   <item><b>ListLiteral</b>: element slots follow the written-parentheses
    ///   expression-list slot rules (<see cref="EvalExplicitSequenceValueExprSlots"/>);
    ///   elements are stored EXACTLY (no singleton erasure, no empty-nesting collapse),
    ///   the collection reservation happens before the persistent list is built, and a
    ///   list literal always emits one value. Lean: <c>evalListLiteralCounted</c>;
    ///   plain <c>Eval</c> is this function's value projection on both sides.</item>
    ///   <item><b>InterpolatedString</b> (VAL-12): the head text, then the holes LEFT TO
    ///   RIGHT, each EXACTLY ONCE, each converted to its structural value text as soon as it
    ///   is available (<see cref="InterpolatedTextBuilder.AppendValue"/>) and followed by its
    ///   link's text; the first failure ends the node — a hole's failure (gaining the hole's
    ///   span, else the node's, when it has none) or a string limit — and no later hole is
    ///   evaluated. A hole is read exactly like any other machine child (a pushed spine frame,
    ///   or one delegated <c>Eval</c>): a parameter demands its supplied cell, a property goes
    ///   through the zero-argument cache, an output-less algorithm is its
    ///   <see cref="EvalError.MissingOutput"/>. The node emits ONE string value. Lean: the
    ///   <c>.interpolatedString</c> arm of <c>evalCounted</c> (<c>interpolateWith</c>).</item>
    /// </list>
    /// </summary>
    private static EvalResult<CountedResult> EvalExpressionSpineCounted(
        Expr root,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var frames = new ExpressionSpineFrame[16];
        var frameCount = 0;
        frames[frameCount++] = new ExpressionSpineFrame(root);

        // The counted result most recently produced for the top frame's pending
        // child. Machine-kind children deliver here when their frame pops; delegated
        // children deliver here directly.
        CountedResult pendingChild = default;
        var hasPendingChild = false;

        while (true)
        {
            // Bulk pathological-work bound (see TryChargeExpressionNodeWork): the
            // machine bypasses ordinary dispatch for spine kinds, so each frame
            // transition contributes to the same cheap bulk-work counter.
            if (ctx.Budget.TryChargeExpressionNodeWork() is { } nodeWorkError)
                return nodeWorkError;

            ref var frame = ref frames[frameCount - 1];
            EvalResult<CountedResult>? completed = null;
            Expr? requestedChild = null;

            switch (frame.Node)
            {
                case Expr.Unary(var unaryOp, var operand):
                {
                    if (!hasPendingChild)
                    {
                        requestedChild = operand;
                        break;
                    }

                    hasPendingChild = false;
                    var unaryR = ApplyUnaryOperator(unaryOp, pendingChild.Value, frame.Node.Span);
                    completed = unaryR.IsError
                        ? unaryR.Error
                        : EvalResult<CountedResult>.Ok(new CountedResult(
                            unaryR.Value, unaryR.Value.ValueCount()));
                    break;
                }

                case Expr.Binary(var op, var left, var right):
                {
                    if (frame.Phase == 0)
                    {
                        if (!hasPendingChild)
                        {
                            requestedChild = left;
                            break;
                        }

                        hasPendingChild = false;
                        frame.FirstValue = pendingChild.Value;
                        frame.Phase = 1;
                        requestedChild = right;
                        break;
                    }

                    hasPendingChild = false;
                    var binaryR = ApplyBinaryOperator(
                        op, left, right, frame.FirstValue!, pendingChild.Value, frame.Node.Span);
                    completed = binaryR.IsError
                        ? binaryR.Error
                        : EvalResult<CountedResult>.Ok(new CountedResult(
                            binaryR.Value, binaryR.Value.ValueCount()));
                    break;
                }

                case Expr.Comparison(var first, var links):
                {
                    if (frame.Phase == 0)
                    {
                        if (!hasPendingChild)
                        {
                            requestedChild = first;
                            break;
                        }

                        hasPendingChild = false;
                        frame.FirstValue = pendingChild.Value;
                        frame.Phase = 1;
                        if (links.Count == 0)
                        {
                            // A host-built chain with no links: its one operand was
                            // evaluated (exactly once, like every operand) and there is
                            // no comparison to fail.
                            completed = EvalResult<CountedResult>.Ok(new CountedResult(new Result.Bool(true), 1));
                            break;
                        }

                        requestedChild = links[0].Operand;
                        break;
                    }

                    // The operand of link (Phase - 1) just arrived: compare the PREVIOUS
                    // operand's value with it. An error ends the chain here (the
                    // remaining operands are never evaluated); a false link is recorded
                    // and the chain continues to its next operand.
                    hasPendingChild = false;
                    var link = links[frame.Phase - 1];
                    var previousOperand = frame.Phase == 1 ? first : links[frame.Phase - 2].Operand;
                    var linkR = ApplyComparison(
                        link.Op, previousOperand, link.Operand, frame.FirstValue!, pendingChild.Value, frame.Node.Span, ctx);
                    if (linkR.IsError)
                    {
                        completed = linkR.Error;
                        break;
                    }

                    if (!linkR.Value)
                        frame.ComparisonFailed = true;
                    frame.FirstValue = pendingChild.Value;
                    frame.Phase++;
                    if (frame.Phase <= links.Count)
                    {
                        requestedChild = links[frame.Phase - 1].Operand;
                        break;
                    }

                    completed = EvalResult<CountedResult>.Ok(new CountedResult(new Result.Bool(!frame.ComparisonFailed), 1));
                    break;
                }

                case Expr.Index selection:
                {
                    if (frame.Phase == 0)
                    {
                        // (1) The receiver, once, through its ordinary value path.
                        if (!hasPendingChild)
                        {
                            requestedChild = selection.Target;
                            break;
                        }

                        hasPendingChild = false;
                        frame.FirstValue = pendingChild.Value;
                        frame.Phase = 1;
                        // (2) Supply formation: every explicit spread slot runs now.
                        if (HasSpreadSelector(selection.Selectors))
                        {
                            var formed = FormSelectionSupplySync(selection, ctx, valEnv);
                            if (formed.IsError)
                            {
                                completed = formed.Error;
                                break;
                            }

                            frame.Selection = formed.Value;
                        }
                    }

                    // (3) + (4): the supplied selectors left to right, then the capture.
                    completed = AdvanceSelection(ref frame, hasPendingChild ? pendingChild.Value : null, ctx, out requestedChild, out var selectorCell, out var viewIndex);
                    hasPendingChild = false;
                    if (selectorCell is not null)
                    {
                        var demanded = selectorCell.Demand();
                        completed = demanded.IsError
                            ? SelectorFailure(demanded.Error, frame)
                            : AdvanceSelection(ref frame, demanded.Value.Value, ctx, out requestedChild, out _, out viewIndex);
                    }

                    // An argument view's validated position: read that ONE cell, demand it (S2).
                    if (viewIndex >= 0)
                        completed = SelectArgumentViewSync(ref frame, viewIndex, ctx);

                    break;
                }

                case Expr.ListLiteral(var elements):
                {
                    frame.ListItems ??= NewListSlots(elements);
                    if (hasPendingChild)
                    {
                        // WRITTEN-SLOT REIFICATION: a machine-kind element is never a
                        // spread, so its counted supply contributes exactly ONE value.
                        hasPendingChild = false;
                        AddListSlot(frame.ListItems, pendingChild.Value, ctx.Budget);
                        frame.Phase++;
                    }

                    while (frame.Phase < elements.Count)
                    {
                        var element = elements[frame.Phase];
                        if (IsExpressionSpineNode(element))
                            break;

                        var slotsR = EvalExplicitSequenceValueExprSlots(element, ctx, valEnv);
                        if (slotsR.IsError)
                        {
                            completed = slotsR.Error;
                            break;
                        }

                        // The written slots' accumulator is transient-bounded BEFORE it grows
                        // (SEC-01): `[A*, A*]` never retains more spread items than the list may.
                        AddListSlots(frame.ListItems, slotsR.Value, ctx.Budget, element is Expr.SequenceSpread);
                        frame.Phase++;
                    }

                    if (completed is not null)
                        break;

                    if (frame.Phase < elements.Count)
                    {
                        requestedChild = elements[frame.Phase];
                        break;
                    }

                    // Cardinality is known once the written slots (including spread
                    // expansion) are evaluated, so the reservation happens before the
                    // persistent list is built.
                    // An overflowed accumulator (SEC-01) reserves its full counted size: the same refusal.
                    if (ReserveCollection(ctx, ListSlotTotal(frame.ListItems), frame.Node.Span) is { } limitError)
                    {
                        completed = limitError;
                        break;
                    }

                    completed = EvalResult<CountedResult>.Ok(new CountedResult(
                        Result.ListValue.TakeOwnership(frame.ListItems.ToArray()), 1));
                    break;
                }

                case Expr.InterpolatedString(var head, var links):
                {
                    if (frame.Text is null)
                    {
                        frame.Text = new InterpolatedTextBuilder(ctx.Budget);
                        if (!frame.Text.Append(head))
                        {
                            completed = frame.Text.LimitError(frame.Node.Span);
                            break;
                        }
                    }
                    else
                    {
                        // The hole of link Phase just arrived: its text, then the link's text.
                        hasPendingChild = false;
                        if (InterpolationHoleRefusal(pendingChild.Value, links[frame.Phase].Hole) is { } refusedHole)
                        {
                            completed = refusedHole;
                            break;
                        }
                        if (!frame.Text.AppendValue(pendingChild.Value) || !frame.Text.Append(links[frame.Phase].Text))
                        {
                            completed = frame.Text.LimitError(frame.Node.Span);
                            break;
                        }

                        frame.Phase++;
                    }

                    if (frame.Phase < links.Count)
                    {
                        requestedChild = links[frame.Phase].Hole;
                        break;
                    }

                    completed = frame.Text.Complete(frame.Node.Span);
                    break;
                }

                default:
                    throw new InvalidOperationException(
                        $"EvalExpressionSpineCounted received the non-spine node kind '{frame.Node.GetType()}'.");
            }

            if (requestedChild is not null)
            {
                if (IsExpressionSpineNode(requestedChild))
                {
                    if (frameCount == frames.Length)
                        Array.Resize(ref frames, frames.Length * 2);
                    frames[frameCount++] = new ExpressionSpineFrame(requestedChild);
                    continue;
                }

                // Delegated child: exactly the call the recursive code made — plain
                // Eval for unary/binary operands and selection receivers/selectors. (List
                // elements never reach here; non-machine elements go through
                // EvalExplicitSequenceValueExprSlots above, exactly as before.)
                var childR = Eval(requestedChild, ctx, valEnv);
                if (childR.IsError)
                {
                    completed = childR.Error;
                }
                else
                {
                    pendingChild = new CountedResult(childR.Value, childR.Value.ValueCount());
                    hasPendingChild = true;
                    continue;
                }
            }

            if (completed is not { } completedResult)
                continue;

            if (completedResult.IsError)
            {
                // Unwind exactly like the recursive returns: the frame whose child
                // failed applies its child-error decoration (an Index attaches its own
                // span; an InterpolatedString the failed hole's span, else its own),
                // then returns the error to ITS parent, which decorates in turn. An error
                // produced by a frame's own apply step starts at that frame's parent.
                var error = completedResult.Error;
                var decorateTopFrame = requestedChild is not null;
                while (frameCount > 0)
                {
                    ref var unwound = ref frames[frameCount - 1];
                    if (decorateTopFrame)
                        error = DecorateSpineChildError(error, unwound);

                    decorateTopFrame = true;
                    frameCount--;
                }

                // The spine forms a value from SUBORDINATE computations: a missing output escaping
                // it is nested (Q-36; Lean: the operator, selection, list and interpolation arms).
                return NestMissingOutput(error);
            }

            frameCount--;
            if (frameCount == 0)
                return completedResult;

            pendingChild = completedResult.Value;
            hasPendingChild = true;
        }
    }

    /// <summary>
    /// The decoration a spine frame applies to the error of its FAILED CHILD, shared by both
    /// machines: an <see cref="Expr.Index"/> attaches its own span to a failed receiver and the
    /// written slot of the selector in flight (else its own span) to a failed selector, an
    /// <see cref="Expr.InterpolatedString"/> the span of the hole in flight (link
    /// <see cref="ExpressionSpineFrame.Phase"/>), else its own — each only when the error has
    /// no location yet. Every other spine kind passes its child's error on untouched.
    /// </summary>
    private static EvalError DecorateSpineChildError(EvalError error, in ExpressionSpineFrame frame)
        => frame.Node switch
        {
            Expr.Index selection => frame.Phase == 0
                ? AtSpanIfMissing(error, selection.Span)
                : SelectorFailure(error, frame),
            Expr.InterpolatedString interpolation
                => AtSpanIfMissing(error, interpolation.Links[frame.Phase].Hole.Span ?? interpolation.Span),
            _ => error,
        };

    // ── Variadic postfix selection (shared by both spine machines) ─────────

    /// <summary>
    /// One supplied selector of a postfix selection: the written <paramref name="Slot"/> it came
    /// from — the location a failure reports — and, for an item an explicit spread slot formed
    /// (a Ready item or a transported collector cell), its <paramref name="Cell"/>. An ORDINARY
    /// slot has no cell: it is demanded as a machine child of the selection frame at its turn.
    /// </summary>
    private readonly record struct SuppliedSelector(Expr Slot, NeedCell? Cell);

    /// <summary>True when some selector slot is an explicit spread, so the supply must be formed first.</summary>
    private static bool HasSpreadSelector(OutputBundle selectors)
    {
        for (var i = 0; i < selectors.Count; i++)
        {
            if (selectors[i] is Expr.SequenceSpread)
                return true;
        }

        return false;
    }

    /// <summary>
    /// The location of the supplied selector in flight (<see cref="ExpressionSpineFrame.Phase"/> - 1):
    /// its written slot, else the whole selection. Read lazily, so no span temporary lives in a
    /// machine frame.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalError SelectorFailure(EvalError error, in ExpressionSpineFrame frame)
    {
        var selection = (Expr.Index)frame.Node;
        var position = frame.Phase - 1;
        var slot = frame.Selection is { } supplied ? supplied[position].Slot : selection.Selectors[position];
        return AtSpanIfMissing(error, slot.Span ?? selection.Span);
    }

    /// <summary>
    /// One step of a postfix selection after its receiver is in hand — the ONE step both spine
    /// machines run. With <paramref name="arrived"/> (the value of the supplied selector in
    /// flight), the selector is validated and its position selected (<see cref="SelectPosition"/>);
    /// a failure ends the selection, and otherwise the next selector waits for the next machine
    /// transition. Without it, the next supplied selector is requested: an ordinary written slot
    /// as a machine child (<paramref name="requestedChild"/>), a spread-formed cell for the caller
    /// to demand (<paramref name="selectorCell"/>; the synchronous machine demands it inline, the
    /// async twin awaits it). After the last selector the selected values are captured
    /// (<see cref="CompleteSelection"/>). Returns the completed result, or null while the selection
    /// continues. Lean: <c>selectWith</c> then <c>selectionResult</c>.
    /// <para>An ARGUMENT VIEW receiver (CallReference S2) has no positional view of its own: the arrived
    /// selector is validated (<see cref="SelectorIndex"/>) BEFORE anything else, and the validated position
    /// is handed back in <paramref name="viewIndex"/> (otherwise -1) for the machine to read that ONE cell
    /// of the view's supply (<see cref="ArgumentViewSelectionCell"/>, then its demand) and accept its VALUE
    /// (<see cref="AcceptArgumentViewSelection"/>). Lean: <c>selectViewWith</c>.</para>
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult>? AdvanceSelection(
        ref ExpressionSpineFrame frame, Result? arrived, EvalCtx ctx, out Expr? requestedChild, out NeedCell? selectorCell,
        out int viewIndex)
    {
        requestedChild = null;
        selectorCell = null;
        viewIndex = -1;
        var selection = (Expr.Index)frame.Node;
        var supplied = frame.Selection;
        var total = supplied?.Count ?? selection.Selectors.Count;
        if (arrived is not null)
        {
            var position = frame.Phase - 1;
            var slot = supplied is null ? selection.Selectors[position] : supplied[position].Slot;
            if (IsArgumentView(frame.FirstValue!))
            {
                var indexR = SelectorIndex(arrived, slot, selection);
                if (indexR.IsError)
                    return indexR.Error;
                viewIndex = indexR.Value;
                return null;
            }

            var selectedR = SelectPosition(frame.FirstValue!, arrived, slot, selection);
            if (selectedR.IsError)
                return selectedR.Error;

            return AcceptSelected(ref frame, selectedR.Value, total, ctx, selection);
        }

        if (frame.Phase - 1 < total)
        {
            var next = supplied is null ? new SuppliedSelector(selection.Selectors[frame.Phase - 1], null) : supplied[frame.Phase - 1];
            if (next.Cell is { } cell)
                selectorCell = cell;
            else
                requestedChild = next.Slot;
            return null;
        }

        return CompleteSelection(frame.ListItems, ctx, selection);
    }

    /// <summary>
    /// Records one selected value: a single selection is the value itself; otherwise it joins the
    /// accumulator and every further selector takes its own machine transition (its own budget
    /// checkpoint), and after the last the selected values are captured.
    /// </summary>
    private static EvalResult<CountedResult>? AcceptSelected(
        ref ExpressionSpineFrame frame, Result selected, int total, EvalCtx ctx, Expr.Index selection)
    {
        frame.Phase++;
        // One selector: the selected value itself, with no accumulator.
        if (total == 1)
            return CountValue(selected);

        (frame.ListItems ??= new List<Result>(Math.Min(total, 16))).Add(selected);
        if (frame.Phase - 1 < total)
            return null;
        return CompleteSelection(frame.ListItems, ctx, selection);
    }

    /// <summary>
    /// The cell an ARGUMENT VIEW selection reads at the validated position <paramref name="index"/>
    /// (CallReference S2), from the view's cells (the plan's one sticky supply,
    /// <see cref="PrepareArgumentView"/>); a failure is positioned at the selector in flight. The cell is
    /// returned undemanded: the machine demands exactly it. Lean: the supply read of <c>selectViewWith</c>.
    /// </summary>
    private static EvalResult<NeedCell> ArgumentViewSelectionCell(
        EvalResult<IReadOnlyList<NeedCell>> cells, int index, in ExpressionSpineFrame frame)
    {
        if (cells.IsError)
            return SelectorFailure(cells.Error, frame);
        var selection = (Expr.Index)frame.Node;
        var position = frame.Phase - 1;
        var slot = frame.Selection is { } supplied ? supplied[position].Slot : selection.Selectors[position];
        return ArgumentViewSelectedCell(cells.Value, index, slot, selection);
    }

    /// <summary>
    /// The synchronous machine's argument-view selection step (CallReference S2): the view's cells, the
    /// ONE cell at the validated position, its demand, then its acceptance. Out of line so the spine
    /// machine's frame keeps its size.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult>? SelectArgumentViewSync(ref ExpressionSpineFrame frame, int index, EvalCtx ctx)
    {
        var view = (Result.CallReference)frame.FirstValue!;
        var cell = ArgumentViewSelectionCell(PrepareArgumentView(view, ctx), index, frame);
        if (cell.IsError)
            return cell.Error;
        return AcceptArgumentViewSelection(ref frame, cell.Value.Demand(), ctx);
    }

    /// <summary>
    /// Accepts the demanded VALUE of an argument-view selection's cell (CallReference S2): the run's
    /// continuation is observed again (a cell demand never absorbs a terminal run), a failure is
    /// positioned at the selector in flight, and the value is selected whole.
    /// </summary>
    private static EvalResult<CountedResult>? AcceptArgumentViewSelection(
        ref ExpressionSpineFrame frame, EvalResult<CountedResult> demanded, EvalCtx ctx)
    {
        if (demanded.IsError)
            return SelectorFailure(demanded.Error, frame);
        if (CheckCallReferenceOwnership((Result.CallReference)frame.FirstValue!, ctx) is { } terminal)
            return terminal;
        var selection = (Expr.Index)frame.Node;
        var total = frame.Selection?.Count ?? selection.Selectors.Count;
        return AcceptSelected(ref frame, demanded.Value.Value, total, ctx, selection);
    }

    /// <summary>
    /// The value of a completed selection: the selected values captured by ordinary sequence
    /// normalization of the RESULT GROUPING only (<see cref="MakeCheckedSequenceCapture"/>, which
    /// reserves only what it stores) — zero selections are <c>()</c>, one is the selected value
    /// itself, several are ONE sequence of the selected values kept whole (a selected <c>()</c> or
    /// <c>[]</c> stays an element; never <see cref="Expr.SequenceConstruct"/>'s join, which drops
    /// <c>()</c> leaves) — re-counted at the value boundary. No record of the selector count
    /// survives. Lean: <c>selectionResult</c>.
    /// </summary>
    private static EvalResult<CountedResult> CompleteSelection(List<Result>? selected, EvalCtx ctx, Expr.Index selection)
        => CountValue(MakeCheckedSequenceCapture(ctx, (IReadOnlyList<Result>?)selected ?? [], selection.Span));

    /// <summary>
    /// THE check of ONE supplied selector against the receiver — the retired colon form's rules,
    /// unchanged: a selector VALUE that is not a number is the kind failure <c>TypeMismatch</c>
    /// (<see cref="ExpectInt"/>); a number naming no position — fractional, negative, NaN or
    /// infinite, beyond any host position, or past the receiver's immediate positional view
    /// (<see cref="Result.Index"/> over <see cref="Result.ProjectionItems"/>, the view
    /// <c>count</c>, <c>first</c> and <c>last</c> read) — is <c>BadIndex</c>. The stored element is
    /// returned whole, never opened. A failure is positioned at <paramref name="slot"/>, else the
    /// <paramref name="selection"/>. Non-evaluating, so it serves both machines. Lean:
    /// <c>selectPosition</c>.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    internal static EvalResult<Result> SelectPosition(Result receiver, Result selector, Expr slot, Expr selection)
    {
        // An argument view's positions are its supply's cells, read by the machine (S2), never here.
        if (IsArgumentView(receiver))
            throw new InvalidOperationException("An argument view receiver is selected through its cells.");
        // ExpectInt reports a TypeMismatch from a Result and so has no span of its own.
        var nR = ExpectInt(selector);
        if (nR.IsError)
            return AtSpanIfMissing(nR.Error, slot.Span ?? selection.Span);

        var n = nR.Value;
        // IsInteger is false for NaN and the infinities, so a non-finite selector is the same
        // out-of-range badIndex as a fractional one. Lean models the selector as an unbounded
        // integer and reports badIndex for any position past the receiver's view; a selector
        // beyond int range can never be in range, so it is the same out-of-range error rather
        // than a host overflow.
        var selected = Decimal128.IsInteger(n) && n >= 0 && n <= int.MaxValue
            ? receiver.Index((int)n)
            : null;
        return selected is null
            ? new EvalError.BadIndex { Span = slot.Span ?? selection.Span }
            : EvalResult<Result>.Ok(selected);
    }

    /// <summary>
    /// The receiver-independent half of <see cref="SelectPosition"/> (CallReference S2), run for an
    /// argument view BEFORE its supply is read: a selector VALUE that is not a number is the kind failure
    /// <c>TypeMismatch</c>, and a number that names no position of ANY receiver — fractional, negative,
    /// NaN or infinite — is <c>BadIndex</c>. A whole number beyond host positions is clamped to
    /// <see cref="int.MaxValue"/>, past every supply, so it is decided by the supply exactly as Lean's
    /// unbounded index is. Lean: <c>selectorIndex</c>.
    /// </summary>
    private static EvalResult<int> SelectorIndex(Result selector, Expr slot, Expr selection)
    {
        var nR = ExpectInt(selector);
        if (nR.IsError)
            return AtSpanIfMissing(nR.Error, slot.Span ?? selection.Span);

        var n = nR.Value;
        if (!Decimal128.IsInteger(n) || n < 0)
            return new EvalError.BadIndex { Span = slot.Span ?? selection.Span };
        return EvalResult<int>.Ok(n <= int.MaxValue ? (int)n : int.MaxValue);
    }

    // ── Main eval ───────────────────────────────────────────────────────────

    /// <summary>
    /// Test seams for exact diagnostic-span contracts on one prebuilt expression.
    /// Each call gets a fresh empty context (own budget); no structural preflight
    /// runs, so callers own the depth of what they build.
    /// </summary>
    internal static EvalResult<Result> EvalExpressionForTesting(Expr expr)
        => Eval(expr, EvalCtx.Empty, []);

    internal static EvalResult<CountedResult> EvalCountedExpressionForTesting(Expr expr)
        => EvalCounted(expr, EvalCtx.Empty, []);

    /// <summary>
    /// Counted parameter-reference evaluation — the CANONICAL Param dispatch
    /// shared by both dispatcher spellings (the plain <see cref="Eval"/> arm
    /// projects its value, so the dual-view rules exist once).
    /// Lookup order (Lean: <c>evalCounted</c> Param(x)):
    /// 0. NeedEnv (Model C): the parameter's supplied cell (<see cref="NeedCell"/>). The
    ///    read DEMANDS it: the first VALUE demand evaluates the supplied computation once,
    ///    and every later read reuses that completed outcome, a failure included.
    ///    AT-MOST-ONCE ARGUMENT VALUE EVALUATION (Q-01, September 2026): the read never
    ///    evaluates the algorithm channel, so a failure cannot heal, the argument's effects
    ///    and random draws never repeat, and every read of the parameter in one activation
    ///    observes the same outcome.
    /// 1. ValEnv (ordinary value meaning)
    /// 2. Otherwise the name is unbound: <see cref="EvalError.UnknownName"/> at the read.
    /// (The legacy counted and algorithm-channel tiers that sat between them had no
    /// production writer and were retired on 2026-10-13 with their Lean counterparts.)
    /// </summary>
    // Frame-size discipline for the two name dispatches of the Eval / EvalCounted spines: the
    // expression's span (a 20-byte value as SourceSpan?) is read in these small non-inlined
    // frames, so a Call-recursion level's EvalCounted frame carries no span copy for arms it
    // did not take (see the parser's leaf-frame helpers for the measured effect).
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalParamCountedOf(Expr expr, string name, EvalCtx ctx, ValEnv valEnv)
        => EvalParamCounted(name, expr.Span, ctx, valEnv);

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalResolveCountedOf(Expr expr, string name, EvalCtx ctx, ValEnv valEnv)
        => EvalResolveCounted(name, expr.Span, ctx, valEnv);

    private static EvalResult<CountedResult> EvalParamCounted(
        string name,
        SourceSpan? span,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        ctx = ParameterContext(name, ctx, ref valEnv);
        if (LookupNeed(ctx.NeedEnv, name) is { } need)
            return DemandParameter(need, need.Demand(), name, span);

        var val = LookupVal(valEnv, name);
        if (val is not null)
            return EvalResult<CountedResult>.Ok(new CountedResult(val, val.ValueCount()));

        return new EvalError.UnknownName(name) { Span = span };
    }

    /// <summary>
    /// The value outcome of a parameter whose supplied computation FAILED its one value
    /// evaluation (its cell's first VALUE demand, <see cref="NeedCell"/>): that failure,
    /// reported the way a value-position read reports a parameter's failure — an
    /// output-less argument is the PARAMETER's failure
    /// (<see cref="WithParameterContextOnMissingOutput"/>), and the read's location is
    /// attached only when the failure carries none. This is never an evaluation
    /// (AT-MOST-ONCE ARGUMENT VALUE EVALUATION).
    /// Lean: the <c>.param</c> arm of <c>evalCounted</c>.
    /// </summary>
    private static EvalError ParameterSlotFailure(string name, SourceSpan? span, EvalError slotFailure)
        => WithParameterContextOnMissingOutput(name, span, EvalResult<Result>.Err(slotFailure)).Error;

    /// <summary>
    /// A parameter whose value is demanded and whose argument supplied no output is
    /// reported as that PARAMETER's failure (the argument the caller supplied has no
    /// output), so the enclosing call context never reads as if the callee itself had
    /// none. Any other outcome keeps the plain span attachment.
    /// </summary>
    private static EvalResult<Result> WithParameterContextOnMissingOutput(string name, SourceSpan? span, EvalResult<Result> result)
    {
        if (!result.IsError) return result;
        var failure = result.Error is EvalError.WithContext { ErrorContext: ArgumentEvaluationContext, Inner: EvalError.MissingOutput missing }
            ? missing : result.Error;
        return failure is EvalError.MissingOutput
            ? EvalResult<Result>.Err(new EvalError.WithContext(new ParameterEvaluationContext(name), failure) { Span = failure.Span ?? span })
            : WithSpan(span, result);
    }

    /// <summary>
    /// Counted lexical property-reference evaluation — the CANONICAL Resolve
    /// dispatch shared by both dispatcher spellings (the plain
    /// <see cref="Eval"/> arm projects its value). Resolution goes through the
    /// canonical binding-carrying <see cref="LookupLexical"/> chain, and
    /// zero-argument access re-counts at the property value boundary.
    /// Lean: <c>evalCounted</c> Resolve(n).
    /// </summary>
    private static EvalResult<CountedResult> EvalResolveCounted(
        string name,
        SourceSpan? span,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (ctx.CallStack.Count == 0)
            return new EvalError.UnknownName(name) { Span = span };

        // OD-E (M4★): an alias binding reads its VALUE terminal — the terminal binding's own entry, or a
        // runtime-target alias's binding cell — never an entry of its own.
        var resolvedR = LookupLexicalForValue(ctx.CallStack[0], name, ctx);
        if (resolvedR.IsError)
            return AtSpanIfMissing(resolvedR.Error, span);

        if (resolvedR.Value.ResolvedAlgorithm is not Algorithm.Alias
            && ZeroArgumentValueDemandRejection(ZeroArgumentDemandShape.Property, name, span, resolvedR.Value.ResolvedAlgorithm) is { } rejection)
            return rejection;

        // The property that lacks output is the TERMINAL binding a reference reads (M4★: a transparent
        // reference is its target), so the report names it — the written name for any other binding.
        // An ordinary binding keeps its direct frame chain on this recursive path (FRAME-SIZE DISCIPLINE: an
        // alias read takes the out-of-line helper, which adds a frame per level).
        var propertyR = WithPropertyContextOnMissingOutput(resolvedR.Value.Binding.Name, span, resolvedR.Value.ResolvedAlgorithm,
            resolvedR.Value is { ResolvedAlgorithm: not Algorithm.Alias, CrossesCarrier: false }
                ? EvalZeroArgPropertyAccessCounted(resolvedR.Value, ctx, valEnv)
                : ReadValueBindingCounted(resolvedR.Value, ctx, valEnv));
        return propertyR.IsError
            ? propertyR.Error
            : EvalResult<CountedResult>.Ok(new CountedResult(
                propertyR.Value.Value,
                propertyR.Value.Value.ValueCount()));
    }

    /// <summary>
    /// Evaluates a proven leaf without charging a dispatch checkpoint. Each caller
    /// has already charged through its Eval/EvalCounted head (sync or async).
    /// String construction still performs its normal resource checks and tracking.
    /// </summary>
    private static EvalResult<Result> EvalLeafUncharged(Expr expr, EvalCtx ctx)
    {
        switch (expr)
        {
            case Expr.Num(var n):
                return EvalResult<Result>.Ok(new Result.Atom(n));

            case Expr.StringLiteral(var s):
                return MakeStringResult(ctx, s, expr.Span);

            case Expr.BoolLiteral(var b):
                return EvalResult<Result>.Ok(new Result.Bool(b));

            case Expr.Grace:
                return new EvalError.IllegalInEval(ExprKind(expr)) { Span = expr.Span };

            default:
                throw new InvalidOperationException($"Uncharged leaf evaluation cannot dispatch '{expr.GetType().Name}'.");
        }
    }

    /// <summary>
    /// Plain expression dispatch. Recursive variants project the counted-canonical
    /// per-variant helpers. Leaves and native dispatch are shared implementations;
    /// counted heads enter those directly after charging, never through this head.
    /// NativeCall can demand argument algorithms and has its own async twin.
    /// Lean: eval is the total value projection of evalCounted.
    /// </summary>
    private static EvalResult<Result> Eval(
        Expr expr,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // Structural nesting charges no dynamic invocation depth; the pre-evaluation
        // structural preflight (AstStructuralPreflight) bounds every accepted tree to
        // EvaluationLimits.MaxSupportedAstDepth before evaluation begins, and the
        // pure-expression composite kinds (unary, binary, index, list literal, and the
        // internal sequence joins) evaluate ITERATIVELY, so recursion here grows only
        // at algorithm boundaries (blocks, calls, dot-calls) — the shapes the ceiling
        // is calibrated against. Deliberately NO TryEnsureSufficientExecutionStack
        // probe here: the CLR probe reserves roughly half of a 1 MiB stack, so a
        // per-node probe rejects deep parser-produced programs that complete fine
        // today (measured: a 288-level bracket nesting). The structural-nesting
        // backstop lives instead at the two per-nesting-level row-loop funnels
        // (EvalOutputRowsPreparedCore, EvalExplicitSequenceValueRowSlots and their
        // async twins), where static nesting multiplied by dynamic recursion
        // would otherwise descend uncharged between two chokepoint probes.
        // Bulk pathological-work bound (see TryChargeExpressionNodeWork).
        if (ctx.Budget.TryChargeExpressionNodeWork() is { } nodeWorkError)
            return nodeWorkError;

        return expr switch
        {
            Expr.Num or Expr.StringLiteral or Expr.BoolLiteral => EvalLeafUncharged(expr, ctx),

            // Value projection of the canonical counted Param dispatch
            // (dual-view lookup order documented on EvalParamCounted).
            Expr.Param(var name) => ProjectCountedValue(EvalParamCountedOf(expr, name, ctx, valEnv)),

            // Unary, binary, comparison-chain, index, list-literal, and interpolated-string
            // spines evaluate iteratively; the machine preserves operand validation, error
            // propagation, and spans through the shared unary, binary, and comparison
            // applications, and owns the index-expression span. ONE arm for every spine
            // kind: in a Debug frame each call site holds its own struct return
            // temporaries, and this frame recurs once per algorithm boundary (frame-size
            // discipline).
            Expr.Unary or Expr.Binary or Expr.Comparison or Expr.Index or Expr.ListLiteral or Expr.InterpolatedString
                => ProjectCountedValue(EvalExpressionSpineCounted(expr, ctx, valEnv)),

            Expr.SequenceConstruct => ProjectCountedValue(EvalSequenceConstructCounted(expr, ctx, valEnv)),

            Expr.EmptySequence(var depth) => EvalResult<Result>.Ok(BuildEmptySequenceValue(depth)),

            Expr.SequenceSpread => ProjectCountedValue(EvalSequenceSpreadCounted(expr, ctx, valEnv)),

            Expr.AlgorithmExpr(var alg) => EvalAlgorithmExprValue(expr, alg, ctx, valEnv),

            Expr.Capture(var captureBody) => WithPreferredSpanOf(
                expr, captureBody, EvalCaptureValue(captureBody, ctx, valEnv)),

            // Value projection of the canonical counted Resolve dispatch.
            Expr.Resolve(var name) => ProjectCountedValue(EvalResolveCountedOf(expr, name, ctx, valEnv)),

            // Lean: eval (.dotMember o n fallback mode argsOpt) => withCtx (CtxMsg.dotCall o n) do evalDotCall
            // (the context — which renders the receiver's name — is built only on error).
            Expr.DotCall dotCallExpr => WithSpanOf(expr, WithDotCallCtx(dotCallExpr, ctx,
                EvalDotCall(dotCallExpr, ctx, valEnv))),

            Expr.Call(var func, var callArgs) => WithSpanOf(expr,
                EvalCallExpr(func, callArgs, ctx, valEnv)),

            Expr.NativeCall(var fnName, var argNames) => EvalNativeCall(fnName, argNames, ctx, valEnv),

            Expr.Grace => EvalLeafUncharged(expr, ctx),
        };
    }

    /// <summary>
    /// A scope-owning algorithm expression in VALUE position, shared by the plain,
    /// counted, and (mirrored) async dispatches: the block is wired to the caller,
    /// a parameterized block is the ordinary zero-argument value-demand rejection,
    /// and otherwise its output is evaluated under the block's span.
    /// </summary>
    private static EvalResult<Result> EvalAlgorithmExprValue(
        Expr expr,
        Algorithm alg,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (alg is Algorithm.Alias)
            return EvalInlineAliasValue(expr, alg, ctx, valEnv);

        var wired = WireToCaller(ctx, alg);
        var blockSpan = PreferExpressionSpan(expr.Span, wired.Output);
        if (ZeroArgumentValueDemandRejection(ZeroArgumentDemandShape.Block, name: null, blockSpan, wired) is { } rejection)
            return rejection;
        return WithSpan(blockSpan, EvalZeroArgumentDemandOutput(wired, ctx, valEnv));
    }

    /// <summary>
    /// Evaluate an expression together with the number of top-level values it
    /// emits at the current algorithm boundary.
    /// Calls, name resolution, and collection builtins are value boundaries: they
    /// emit <c>Result.ValueCount</c> of the result value (one value for a
    /// non-empty result), so a multi-output body/collection is observed as one
    /// sequence value and only caller-site <c>spread</c> re-spreads it.
    /// Block expressions count as one sequence value when non-empty. Spread
    /// emits the immediate spread items of its operand. All other value
    /// expressions emit either zero values (empty result) or one value.
    /// Lean: <c>evalCounted</c>.
    /// </summary>
    internal static EvalResult<CountedResult> EvalCounted(
        Expr expr,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // Bulk pathological-work bound (see TryChargeExpressionNodeWork): free for
        // small ordinary programs, but a reference-shared (DAG-shaped) host tree that
        // re-evaluates 2^n occurrences of 25 nodes now consults the step budget.
        if (ctx.Budget.TryChargeExpressionNodeWork() is { } nodeWorkError)
            return nodeWorkError;

        // Compiler-exhaustive over the closed Expr hierarchy — MIRRORED case for case by
        // EvalCountedAsync. A new variant is a build error here until it is given a
        // counted case (or joins the proven-leaf group at the end), so it can never
        // silently take a plain value with a single-value count and erase multi-item
        // emission.
        return expr switch
        {
            Expr.Param(var name) => EvalParamCountedOf(expr, name, ctx, valEnv),

            Expr.SequenceSpread => EvalSequenceSpreadCounted(expr, ctx, valEnv),

            Expr.SequenceConstruct => EvalSequenceConstructCounted(expr, ctx, valEnv),

            // The spine kinds share ONE arm (one call site in this recursive frame); the
            // spine machine owns the index-expression span and evaluates an interpolated
            // string's holes left to right, each once (VAL-12).
            Expr.Unary or Expr.Binary or Expr.Comparison or Expr.Index or Expr.ListLiteral or Expr.InterpolatedString
                => EvalExpressionSpineCounted(expr, ctx, valEnv),

            Expr.EmptySequence(var depth) => CountValue(BuildEmptySequenceValue(depth)),

            Expr.AlgorithmExpr(var alg) => CountValue(EvalAlgorithmExprValue(expr, alg, ctx, valEnv)),

            // A capture in value position is a value boundary: the body's
            // supply is captured to one canonical value and re-counted as
            // that value's ValueCount.
            Expr.Capture(var captureBody) => CountValue(WithPreferredSpanOf(
                expr, captureBody, EvalCaptureValue(captureBody, ctx, valEnv))),

            Expr.Resolve(var name) => EvalResolveCountedOf(expr, name, ctx, valEnv),

            Expr.DotCall dotCallExpr => WithSpanOf(expr, WithDotCallCtx(dotCallExpr, ctx,
                EvalDotCallCounted(dotCallExpr, ctx, valEnv))),

            Expr.Call(var func, var callArgs) => WithSpanOf(expr,
                EvalCallCountedExpr(func, callArgs, ctx, valEnv)),

            // This head already charged the dispatch checkpoint. Enter the shared
            // implementations directly, never through the charging plain Eval head.
            // NativeCall is recursive: its parameter reads can demand algorithms,
            // so the async counted dispatcher uses EvalNativeCallAsync.
            Expr.NativeCall(var nativeFnName, var nativeArgNames)
                => CountValue(EvalNativeCall(nativeFnName, nativeArgNames, ctx, valEnv)),

            // PROVEN LEAVES — the only kinds the async twin may delegate to the
            // synchronous leaf core: none evaluates a child expression.
            Expr.Num or Expr.StringLiteral or Expr.BoolLiteral or Expr.Grace => CountValue(EvalLeafUncharged(expr, ctx)),
        };
    }

    private static EvalResult<Result> EvalNativeCall(
        string fnName,
        IReadOnlyList<string> argNames,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // Host-operation dispatch precedes the built-in switch. Host wrapper bodies
        // carry the "host:"-prefixed native name (a spelling no built-in native uses,
        // since ':' cannot appear in an identifier), so registered host operations and
        // built-in Math natives can never collide. An unregistered host-prefixed name —
        // a host-built AST evaluated without its configuration — falls through to the
        // ordinary unknown-native-function error below.
        if (ctx.Budget.HostOperations is { } hostOperations
            && fnName.StartsWith(HostOperations.NativeNamePrefix, StringComparison.Ordinal)
            && hostOperations.TryGetByNativeName(fnName, out var hostOperation))
        {
            return InvokeSynchronousHostOperation(hostOperation, argNames, ctx, valEnv);
        }

        var argsR = CollectMathNativeArguments(argNames, ctx, valEnv);
        if (argsR.IsError) return argsR.Error;

        return ApplyMathNative(fnName, argsR.Value, ctx.Budget.RandomSource);
    }

    /// <summary>
    /// Reads one Math native's declared arguments from the wrapper's bound
    /// parameter environments, in declaration order, and coerces each to its
    /// numeric domain. Lookup is the shared native-argument read
    /// (<see cref="LookupNativeArgument"/>), which is the ordinary
    /// <see cref="Expr.Param"/> value read; the numeric constraint applies to
    /// the value that read produced.
    /// </summary>
    private static EvalResult<Decimal128[]> CollectMathNativeArguments(
        IReadOnlyList<string> argNames,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var args = new Decimal128[argNames.Count];
        for (var i = 0; i < argNames.Count; i++)
        {
            var valR = LookupNativeArgument(ctx, valEnv, argNames[i]);
            if (valR.IsError) return valR.Error;
            // The ONE numeric coercion (strings and Booleans are value-kind
            // errors, and so is every other non-numeric shape, Q-27), shared with the twin.
            var numR = ExpectInt(valR.Value);
            if (numR.IsError) return numR.Error;
            args[i] = numR.Value;
        }

        return EvalResult<Decimal128[]>.Ok(args);
    }

    /// <summary>
    /// Applies one Math native to its already-read numeric arguments. It evaluates
    /// nothing and reads no environment; its only non-argument input is the run's
    /// random stream, passed EXPLICITLY (never a static or shared fallback) and
    /// consumed only by the two random members, which draw from it in evaluation
    /// order after validating their bounds. The synchronous dispatch and its async
    /// twin both hand over <c>ctx.Budget.RandomSource</c> and share this ONE
    /// implementation, so neither the member set nor the draw order can drift
    /// between them.
    /// </summary>
    internal static EvalResult<Result> ApplyMathNative(string fnName, Decimal128[] args, RandomSource randomSource)
    {
        // Host-AST arity gate (bug-hunt B5a). `Expr.NativeCall` is publicly
        // host-constructible, and the arms below read FIXED argument positions
        // (args[0], args[1]), so a host-built call whose ArgNames list was shorter
        // than the member's arity escaped as a CLR IndexOutOfRangeException out of
        // every Run* entry point. The registry's descriptor table is the one
        // authority on each member's arity, and the count must match it EXACTLY:
        // a LONGER list is rejected as well (pinned policy, mirroring the
        // host-operation signature rule in ValidateHostOperationNativeSignature),
        // because the registry-built wrappers always carry exactly the declared
        // names and a surplus name is silently ignored binding metadata no host
        // can have meant. The gate sits AFTER argument binding — the caller has
        // already read every named argument — so an unbound name still reports
        // UnknownName first, and a name that is no Math function member still
        // reaches the `default:` arm below. Both dispatch twins share this one
        // implementation, so the verdict cannot drift between them.
        // A malformed host AST can carry a null name. Preserve the switch's
        // unknown-native verdict instead of passing null to the registry map.
        if (fnName is not null
            && BuiltinRegistry.TryGetMathFunctionArity(fnName, out var arity)
            && args.Length != arity)
        {
            return new EvalError.IllegalInEval(
                $"invalid native-call signature for Math.{fnName}: expected {arity} argument name(s), got {args.Length}");
        }

        // Every math member computes Decimal128 end-to-end — no double round-trip
        // in KatLang. Results use Decimal128's 34-digit format; this is not a
        // correct-rounding guarantee. The transcendental members call the
        // platform Decimal128 functions directly (DEC-RC2-1: the .NET 11 RC2
        // accuracy correction superseded KatLang's endpoint and near-1
        // reformulations; see SEMANTIC-ALIGNMENT.md K6-R3). Domain violations
        // follow IEEE: Sqrt(-1) and Ln(-1) are NaN, Ln(0) is -Infinity, and
        // non-finite inputs propagate. Transcendental results are
        // quantum-canonicalized (see CanonicalizeMathResult); the
        // quantum-transparent members (Abs/Ceil/Floor/Round/Sign) keep their
        // argument-derived quanta exactly as System.Decimal did.
        Decimal128 result;
        switch (fnName)
        {
            case "Abs": result = Decimal128.Abs(args[0]); break;
            case "Ceil": result = Decimal128.Ceiling(args[0]); break;
            case "Floor": result = Decimal128.Floor(args[0]); break;
            case "Round":
                if (!Decimal128.IsInteger(args[1]))
                    return new EvalError.IllegalInEval("digits must be an integer");
                if (args[1] < 0)
                    return new EvalError.IllegalInEval("digits must be >= 0");
                // The smallest representable quantum is 1e-6176, so rounding is the
                // identity for any larger digit count — oversized counts clamp there
                // before the host (int) narrowing.
                result = Decimal128.Round(
                    args[0],
                    ClampRoundDigits(args[1]),
                    MidpointRounding.AwayFromZero);
                break;
            case "Sign":
                // Decimal128.Sign throws on NaN; the signum of NaN propagates as NaN.
                result = Decimal128.IsNaN(args[0]) ? Decimal128.NaN : Decimal128.Sign(args[0]);
                break;
            case "Sqrt": result = CanonicalizeMathResult(Decimal128.Sqrt(args[0])); break;
            case "Exp": result = CanonicalizeMathResult(Decimal128.Exp(args[0])); break;
            case "Ln": result = CanonicalizeMathResult(Decimal128.Log(args[0])); break;
            case "Lg": result = CanonicalizeMathResult(Decimal128.Log10(args[0])); break;
            case "Sin": result = CanonicalizeMathResult(Decimal128.Sin(args[0])); break;
            case "Asin": result = CanonicalizeMathResult(Decimal128.Asin(args[0])); break;
            case "Cos": result = CanonicalizeMathResult(Decimal128.Cos(args[0])); break;
            case "Acos": result = CanonicalizeMathResult(Decimal128.Acos(args[0])); break;
            case "Tan": result = CanonicalizeMathResult(Decimal128.Tan(args[0])); break;
            case "Atan": result = CanonicalizeMathResult(Decimal128.Atan(args[0])); break;
            case "Atan2": result = CanonicalizeMathResult(Decimal128.Atan2(args[0], args[1])); break;
            case "Pow":
                // Math.Pow and the `^` operator share one implementation, so the
                // exact integer-exponent path and the zero-base rule cannot drift.
                return EvalPow(span: null, args[0], args[1]);
            case "Log": result = CanonicalizeMathResult(Decimal128.Log(args[0], args[1])); break;
            case "Random":
                // Validation precedes every draw: an invalid call consumes no word of
                // the run's stream, so the next valid draw is exactly what it would
                // have been had the invalid call never appeared.
                if (!Decimal128.IsFinite(args[0]) || !Decimal128.IsFinite(args[1]))
                    return new EvalError.IllegalInEval("Math.Random bounds must be finite numbers");
                if (args[0] >= args[1])
                    return new EvalError.IllegalInEval("Math.Random start must be less than end");
                if (!Decimal128.IsFinite(args[1] - args[0]))
                    return new EvalError.IllegalInEval("Math.Random range is too large");
                result = RandomInHalfOpenRange(args[0], args[1], randomSource);
                break;
            case "RandomInt":
                // Uniform INTEGER-domain generation, never a scaled fraction: flooring a
                // scaled Math.Random draw biases every span that does not divide its
                // 10^34-point lattice. Bounds are confined to the exact consecutive-integer
                // domain (|bound| <= 1e34), where every candidate result is exactly
                // representable and the span is exactly countable — beyond it, uniformity
                // over "the integers in the interval" is not even well-defined in
                // Decimal128, so such bounds are rejected rather than silently biased.
                if (!Decimal128.IsInteger(args[0]) || !Decimal128.IsInteger(args[1]))
                    return new EvalError.IllegalInEval("Math.RandomInt bounds must be whole numbers");
                if (Decimal128.Abs(args[0]) > MaxExactRangeBound || Decimal128.Abs(args[1]) > MaxExactRangeBound)
                    return new EvalError.IllegalInEval("Math.RandomInt bounds must not exceed 1e34 in magnitude");
                if (args[0] >= args[1])
                    return new EvalError.IllegalInEval("Math.RandomInt start must be less than end");
                result = SampleUniformInteger(args[0], args[1], randomSource);
                break;
            default:
                return new EvalError.IllegalInEval($"unknown native function: {fnName}");
        }

        return EvalResult<Result>.Ok(new Result.Atom(result));
    }

    internal static int ClampRoundDigits(Decimal128 digits)
        => (int)Decimal128.Min(digits, 6176);

    /// <summary>
    /// Invokes a SYNCHRONOUS host operation at its wrapper-body evaluation site. Runs
    /// inside the wrapper call's already-charged invocation region, exactly like a Math
    /// native, so no additional budget accounting applies here. Host exceptions
    /// propagate unchanged — host code failing is a host outcome, never a KatLang
    /// diagnostic (the same contract as the zero-argument property cache seam).
    /// </summary>
    private static EvalResult<Result> InvokeSynchronousHostOperation(
        HostOperation hostOperation,
        IReadOnlyList<string> argNames,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // Every entry point routes asynchronous configurations away from the
        // synchronous evaluator; reaching one here means a routing guard was bypassed.
        // Fail loud instead of blocking on the awaitable or silently skipping the call.
        if (hostOperation.SynchronousImplementation is not { } implementation)
        {
            throw new InvalidOperationException(
                $"Asynchronous host operation '{hostOperation.Name}' reached the synchronous evaluator; " +
                "async host configurations must route through the async evaluation path.");
        }

        if (ValidateHostOperationNativeSignature(hostOperation, argNames) is { } signatureError)
            return signatureError;

        if (TryInvokeMetaReceiver(hostOperation, argNames, ctx) is { } metaReceived)
            return metaReceived;

        var argumentsR = CollectHostOperationArguments(argNames, ctx, valEnv);
        if (argumentsR.IsError) return argumentsR.Error;

        var value = implementation(argumentsR.Value, ctx.Budget.CancellationToken);
        return NormalizeHostOperationValue(hostOperation, value, ctx.Budget, ctx.Observations?.StructuralTraversal);
    }

    /// <summary>
    /// The canonical-value boundary for one SUCCESSFUL host-operation return, shared by
    /// the synchronous dispatch (<see cref="InvokeSynchronousHostOperation"/>) and the
    /// async twin's await site (<c>EvalAsynchronousHostOperationCountedAsync</c>) so the
    /// two paths cannot drift. Host code builds values with the public constructors and
    /// may hand back representations ordinary KatLang evaluation would have normalized
    /// during construction — a singleton transparent sequence around an atom, redundant
    /// nested unary sequence structure around the empty sequence — and such raw shapes
    /// diverge from equal program-produced values at representation-sensitive rules
    /// (structural equality, visible-empty counting). <see cref="Result.Normalize"/> is
    /// the ONE existing normalization algorithm and is applied here, at the host
    /// boundary, before the value reaches ANY consumer: the wrapper body's evaluation
    /// result is derived from this normalized value, so the zero-argument property cache
    /// (which stores that evaluation outcome) can only ever store the canonical value —
    /// a cache hit re-serves it without re-normalizing. Normalize is sharing-preserving
    /// and returns an already-canonical value AS ITSELF (same reference), so canonical
    /// host returns are untouched; lists and strings keep their exact opacity. Successful
    /// values only: host exceptions, faulted awaitables, and cancellation propagate
    /// before this helper runs, and a null return remains the fail-loud host contract
    /// violation.
    ///
    /// <para>The same walk ADMITS the value (SEC-01-FU, <see cref="Result.AdmitHostOperationValue"/>):
    /// every distinct nested collection's immediate count and every string's length must fit the
    /// run's effective per-collection and per-string limits, nested structures charge structural
    /// work and observe cancellation, and a refusal is the run's terminal resource error — the
    /// wrapper body fails with it, so no consumer and no cache ever receives the value.</para>
    /// </summary>
    private static EvalResult<Result> NormalizeHostOperationValue(
        HostOperation hostOperation,
        Result? value,
        Evaluation.EvaluationBudget budget,
        ValueTraversalObservations? observations)
        => value is null
            ? throw new InvalidOperationException(
                $"Host operation '{hostOperation.Name}' returned null; host operations must return a KatLang value.")
            // The same DAG-safe walk normalizes, admits, and refuses reference leaves, including
            // nested ones. No preliminary traversal of large host values is needed.
            : value.AdmitHostOperationValue(hostOperation.Name, budget, observations);

    /// <summary>
    /// A host operation may be reached only through the synthetic wrapper built by its
    /// matching <see cref="HostOperations"/> set. <see cref="Expr.NativeCall"/> remains
    /// publicly host-constructible for Math compatibility, so reject forged host calls
    /// whose environment-binding metadata does not exactly match the registered
    /// signature instead of invoking host code with an unexpected argument list.
    /// </summary>
    private static EvalError? ValidateHostOperationNativeSignature(
        HostOperation hostOperation,
        IReadOnlyList<string> argNames)
    {
        // The synthesized runtime wrapper stores the operation's immutable parameter
        // list directly, so every ordinary call takes this allocation-free O(1) path.
        // The element comparison is only for host-constructed ASTs.
        if (ReferenceEquals(argNames, hostOperation.ParameterNames))
            return null;

        if (argNames.Count == hostOperation.ParameterNames.Count)
        {
            var matches = true;
            for (var i = 0; i < argNames.Count; i++)
            {
                if (!string.Equals(argNames[i], hostOperation.ParameterNames[i], StringComparison.Ordinal))
                {
                    matches = false;
                    break;
                }
            }

            if (matches)
                return null;
        }

        return new EvalError.IllegalInEval(
            $"invalid native-call signature for host operation: {hostOperation.Name}");
    }

    /// <summary>
    /// Collects a host operation's evaluated argument values from the wrapper's bound
    /// parameter environments, in declaration order, as the read-only snapshot handed
    /// to host code. Lookup is the shared counted-first native-argument rule
    /// (<see cref="LookupNativeArgument"/>), so a callback invocation hands the
    /// host its callback-bound arguments — never a same-named ambient value. Unlike
    /// Math natives there is no numeric coercion: host operations receive the full
    /// KatLang values.
    /// </summary>
    private static EvalResult<IReadOnlyList<Result>> CollectHostOperationArguments(
        IReadOnlyList<string> argNames,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (argNames.Count == 0)
            return EvalResult<IReadOnlyList<Result>>.Ok([]);

        var arguments = new Result[argNames.Count];
        for (var i = 0; i < argNames.Count; i++)
        {
            var valueR = LookupNativeArgument(ctx, valEnv, argNames[i]);
            if (valueR.IsError) return valueR.Error;
            // A call reference never reaches host code (CallReference S1, J4); the scan is charged
            // structural work because it repeats for every host call (SEC-01-FU).
            if (HostArgumentBoundaryError(valueR.Value, ctx.Budget, ctx.Observations?.StructuralTraversal) is { } refused) return refused;
            arguments[i] = valueR.Value;
        }

        return EvalResult<IReadOnlyList<Result>>.Ok(Array.AsReadOnly(arguments));
    }

    /// <summary>
    /// IEEE 754 <c>reduce</c> for transcendental math-function results: returns the
    /// same VALUE represented by its cohort member with the fewest trailing zeros.
    /// .NET's Decimal128 transcendentals report results at the maximum-precision
    /// quantum, which is informative only while all 34 digits are significant — an
    /// inexact result like <c>Sin(1)</c> passes through unchanged, while a
    /// mathematically exact result like <c>Lg(1000)</c> drops the uninformative
    /// trailing zeros (<c>3</c>, not <c>3.000…000</c>), matching what the previous
    /// runtime displayed. Presentation never re-rounds: this canonicalization is
    /// value-preserving and belongs to the operation, not the formatter. It is
    /// deliberately NOT applied to ordinary arithmetic or the quantum-transparent
    /// math members (Abs/Ceil/Floor/Round/Sign), whose argument-derived quanta are
    /// established KatLang display behavior.
    /// </summary>
    internal static Decimal128 CanonicalizeMathResult(Decimal128 value)
    {
        if (!Decimal128.IsFinite(value))
            return value;
        if (value == Decimal128.Zero)
            return Decimal128.IsNegative(value) ? Decimal128.NegativeZero : Decimal128.Zero;

        while (true)
        {
            var quantumExponent = Decimal128.ILogB(Decimal128.GetQuantum(value));
            var coarser = Decimal128.Quantize(value, Decimal128.ScaleB(Decimal128.One, quantumExponent + 1));
            // Coarsening only proceeds while it is exact: a changed value means a
            // significant digit would be lost, so the previous form is canonical.
            if (coarser != value || Decimal128.HaveSameQuantum(coarser, value))
                return value;

            value = coarser;
        }
    }

    /// <summary>Exact scale factor 1e-34 for composing full-precision random fractions.</summary>
    private static readonly Decimal128 RandomUnitFractionScale = Decimal128.ScaleB(Decimal128.One, -34);

    /// <summary>Exclusive bound of each independent 17-digit component draw.</summary>
    private const long RandomDecimalComponentBound = 100_000_000_000_000_000; // 1e17

    /// <summary>
    /// A uniform random fraction in [0, 1) carrying Decimal128's full 34 significant
    /// digits: two independent 17-digit draws compose one uniform integer in
    /// [0, 1e34), scaled exactly by 1e-34. Every arithmetic step is exact, and the
    /// 1e34 lattice points carry just under 113 bits of entropy —
    /// <c>Random.NextDouble</c> would cap randomness at double's 53 bits.
    /// The HIGH component is always drawn before the LOW one, each through the
    /// source's exact bounded draw (<see cref="RandomSource.NextInt64Below"/>), so
    /// under a seed the fraction is reproducible; the source is a parameter at this
    /// helper boundary so endpoint and composition behavior can be tested
    /// deterministically by scripting the bounded seam, without replacing production
    /// randomness or introducing mutable global test state. Sampling is independent
    /// of where the source's words come from: this composition is unchanged by seeding.
    /// </summary>
    internal static Decimal128 SampleRandomUnitFraction(RandomSource source)
    {
        ArgumentNullException.ThrowIfNull(source);
        var high = source.NextInt64Below(RandomDecimalComponentBound);
        var low = source.NextInt64Below(RandomDecimalComponentBound);
        if ((ulong)high >= (ulong)RandomDecimalComponentBound
            || (ulong)low >= (ulong)RandomDecimalComponentBound)
        {
            throw new InvalidOperationException(
                "The Math.Random component source returned a value outside its requested half-open bound.");
        }

        return (((Decimal128)high * RandomDecimalComponentBound) + low) * RandomUnitFractionScale;
    }

    private static Decimal128 RandomInHalfOpenRange(Decimal128 start, Decimal128 end, RandomSource source)
        => ScaleRandomUnitFractionToHalfOpenRange(start, end, SampleRandomUnitFraction(source));

    internal static Decimal128 ScaleRandomUnitFractionToHalfOpenRange(
        Decimal128 start,
        Decimal128 end,
        Decimal128 unitFraction)
    {
        var result = start + (unitFraction * (end - start));
        return result >= end ? start : result;
    }

    /// <summary>
    /// Uniform integer draw for <c>Math.RandomInt</c> over <c>[start, end)</c>:
    /// exact Int128 span plus modulo-REJECTION sampling over uniform 128-bit
    /// draws, so no span carries modulo bias and every integer in the interval is
    /// reachable with equal probability. Callers validate that both bounds are
    /// integers within ±1e34 (the exact consecutive-integer domain), so the span
    /// (at most 2e34) fits Int128 with room to spare and the chosen integer
    /// converts back to Decimal128 exactly.
    ///
    /// <para>The 128-bit draws come from the run's <see cref="RandomSource.NextUInt128"/>
    /// (two raw words, high half first), so tests can drive the mapping and rejection
    /// logic deterministically by scripting that seam. Draws at or above the largest
    /// multiple of the span below 2^128 are redrawn — the acceptance probability
    /// always exceeds one half, and each draw is independent, so the loop
    /// terminates with probability one and never biases the accepted values. Even a
    /// unit span consumes one 128-bit draw: consumption is part of the seeded-stream
    /// contract, and this sampler is unchanged by seeding.</para>
    /// </summary>
    internal static Decimal128 SampleUniformInteger(Decimal128 start, Decimal128 end, RandomSource source)
    {
        ArgumentNullException.ThrowIfNull(source);
        var startInteger = (Int128)start;
        var span = (UInt128)((Int128)end - startInteger);

        // 2^128 mod span, computed without representing 2^128: the count of
        // rejected top draws. Zero means the span divides 2^128 exactly and no
        // draw is ever rejected.
        var rejectedDrawCount = (UInt128.MaxValue % span) + 1;
        if (rejectedDrawCount == span)
            rejectedDrawCount = 0;

        UInt128 draw;
        do
        {
            draw = source.NextUInt128();
        }
        while (rejectedDrawCount != 0 && draw > UInt128.MaxValue - rejectedDrawCount);

        return (Decimal128)(startInteger + (Int128)(draw % span));
    }
}
