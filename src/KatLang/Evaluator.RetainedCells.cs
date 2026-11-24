using System.Runtime.CompilerServices;
using KatLang.Evaluation;

namespace KatLang;

/// <summary>
/// DETACHED REUSE OF RETAINED RUNTIME-ALIAS CELLS (ledger R-1, November 2026; Lean-first:
/// <c>CellInputs</c>, <c>CellRecords</c>, <c>noteCellInput</c>, <c>servingDetached</c>,
/// <c>reuseRetainedCell</c> in <c>lean/KatLang.lean</c>, laws in
/// <c>KatLangArityLaws/RetainedCellReuse.lean</c>).
/// <para>THE RULE. A retained binding cell of a runtime-target alias (any non-parameter row:
/// <see cref="AliasBindingCell"/>) carries an INPUT RECORD (<see cref="AliasCellInputs"/>): the activation
/// watermark at its establishment and the LEAST activation below it that its computation has read an input
/// through. The row's context is marked with the record (<see cref="EvalCtx.InputRecord"/>, carried on the
/// call-stack node like the watermark), so every input read of the cell's computation records itself on
/// it: a captured parameter read through its owner's activation (<see cref="CapturedParameterActivation"/>),
/// an admitted local-only property read through its key's activation
/// (<see cref="GetOrEvaluateZeroArgPropertyResultCore"/>) and an admitted access of a local-only member
/// on a structural route through its owners' activations (<see cref="AdmitMemberAccess"/>). A local-only alias's row is supplied
/// at the watermark of its declaring level (<see cref="EvalCtx.Reattach"/>), whichever reader reaches it
/// first, so the cell is never tied to the reader that happened to establish it.</para>
/// <para>THE REUSE. A READER's use of the cell's VALUE or CALLABLE (the bare read, the value view's
/// zero-supply invocation, the runtime step of the alias chase) is JUDGED BEFORE THE CHANNEL RUNS
/// (<see cref="RetainedCellAdmission"/>): a reader that DETACHES an input the cell is known to have read is
/// refused with the alias's own <see cref="EvalError.LocalOnlyProperty"/> and nothing of the cell runs — no
/// demand, no effect. Every other reader is ADMITTED and the channel runs SERVING its watermark
/// (<see cref="EvaluationBudget.EnterServing"/>).</para>
/// <para>THE DEMAND DECIDES (owner decision, November 24 2026). The computation can go on after the channel
/// answered: a lazy collection position or a captured call's argument created in it runs later, in the
/// context it was created in, and records its reads then. Such a read is REFUSED, with its own refusal,
/// exactly while a detached evaluation that detaches the activation is being served — an exported
/// evaluation in progress, or a reader whose reuse is running the cell's channel — and the read is an
/// input of a cell that admitted a reader detaching it. A read an ATTACHED reader demands is never
/// refused: after a detached reader counted a lazy list, the list's own row reads every position with its
/// own inputs. On the recorded routes an exported evaluation never takes an enclosing call's input from a retained
/// cell, whichever row came first and whichever channel is cold, while a cell whose computation read no
/// such input — an independent row, or one the exported evaluation owns itself — is shared exactly as
/// before.</para>
/// </summary>
public static partial class Evaluator
{
    /// <summary>
    /// THE INPUT RECORD of one retained runtime-alias binding cell (ledger R-1; Lean <c>CellInputs</c>):
    /// <see cref="Watermark"/> is the run's activation watermark when the cell was established, so an
    /// activation whose serial is below it existed then and a read through a later one is the cell's own
    /// work — the LEAST such serial its computation has read an input through, the deepest watermark of a
    /// reader ADMITTED to reuse the cell, and the records of the cells whose computation reused this one
    /// (its reads are theirs too, while they are inputs of those cells as well). A reader detaches a recorded
    /// read exactly when it detaches the least one (Lean <c>RetainedCellReuse.trace_dependsBelow</c>).
    /// Every operation runs under the run's ONE retained-cell gate
    /// (<see cref="EvaluationBudget.RetainedCellGate"/>): a note checks and writes every record it reaches
    /// as one step, as Lean's does.
    /// <para>Each live reader keeps the dependency information for its inputs. A producer points to its
    /// readers weakly and keeps the greatest reader watermark applicable along any forwarding path.
    /// That fact survives collection of a reader. A live path can outlive an intermediate call
    /// without keeping that call's cell, activation, or cached values alive.</para>
    /// </summary>
    internal sealed class AliasCellInputs(long watermark, EvaluationBudget budget)
    {
        private readonly EvaluationBudget _budget = budget;
        private readonly InputDependencies _inputs = new(watermark);

        internal long Watermark => _inputs.Watermark;

        /// <summary>The retained cell this record belongs to (set once the cell exists).</summary>
        internal NeedCell? Cell { get; set; }

        /// <summary>
        /// Whether the cell's computation is known to have read an input through an activation that a reader
        /// under <paramref name="detachedBefore"/> detaches (Lean <c>CellInputs.dependsBelow</c>).
        /// </summary>
        internal bool DependsBelow(long detachedBefore) => _inputs.DependsBelow(detachedBefore);

        /// <summary>
        /// WHAT A DETACHED REUSE REPORTS (Lean <c>aliasReuseRefusal</c>): the
        /// <see cref="EvalError.LocalOnlyProperty"/> of the alias's own property — the cell is a binding of an
        /// enclosing call — or, for an alias that is no property of its declaring scope, of the name
        /// <c>alias</c>. Built when it is reported, from the alias the cell's row was entered under (the head
        /// of the row's context), so the record keeps no reference of its own to it.
        /// </summary>
        internal EvalError Refusal()
            => Cell?.Suspension?.Caller.Head is Algorithm.Alias alias && AliasOwnProperty(alias, _budget) is { } property
                ? LocalOnlyPropertyError(DetachedReuseDescription, property)
                : new EvalError.LocalOnlyProperty(DetachedReuseDescription, "alias", PropertyExposure.LocalOnlyConditionalAlgorithm);

        /// <summary>
        /// Records an input read through the activation <paramref name="serial"/>; true when it is REFUSED
        /// instead (Lean <c>noteCellInput</c> over <c>CellRecords.lateRefused</c>): a detached evaluation that
        /// detaches the activation is being served, and the read is an input of a cell that admitted a
        /// reader detaching it. The caller then reports the read's own refusal. A read through an activation
        /// the cell's own computation recorded is no input: it is neither recorded nor refused.
        /// </summary>
        internal bool Note(long serial)
        {
            lock (_budget.RetainedCellGate)
                return _inputs.Note(serial, _budget.ServingDetached);
        }

        /// <summary>
        /// THE JUDGMENT of a reuse by a reader whose watermark is <paramref name="detachedBefore"/> and whose own
        /// record (inside a retained cell's computation) is <paramref name="reader"/>, BEFORE the channel runs
        /// (Lean <c>CellRecords.admit</c>): the cell's refusal when it is known to have read an input the
        /// reader detaches; the same refusal when its recorded read, taken into the reader's record, lands
        /// below a reader admitted there while that is served; else the reader is ADMITTED — its watermark
        /// raises its recorded reader watermark, and subsequent reads propagate to the reader. One step under the gate.
        /// </summary>
        internal EvalError? Admit(long detachedBefore, AliasCellInputs? reader)
        {
            lock (_budget.RetainedCellGate)
            {
                if (_inputs.DependsBelow(detachedBefore))
                    return Refusal();
                if (reader is not null && reader._inputs.Note(_inputs.Least, _budget.ServingDetached))
                    return Refusal();
                _inputs.Admit(detachedBefore, reader?._inputs);
                return null;
            }
        }

        // Only scalar access facts and edges belong here. In particular this object has no pointer to
        // its owning AliasCellInputs, which would also keep the intermediate NeedCell and call alive.
        private sealed class InputDependencies(long watermark)
        {
            private long _least = long.MaxValue;
            private long _detachedInputCutoff;
            internal long Watermark { get; } = watermark;
            private HashSet<InputDependencies>? _sources;
            private ConditionalWeakTable<InputDependencies, object>? _readers;

            internal long Least => Volatile.Read(ref _least);
            internal bool DependsBelow(long detachedBefore) => Least < detachedBefore;

            internal void Admit(long detachedBefore, InputDependencies? reader)
            {
                if (reader is not null && !ReferenceEquals(reader, this))
                {
                    // A live reader needs all its inputs. Producers point back weakly so the
                    // completion of a call can release both its cell and its dependency record.
                    if ((reader._sources ??= []).Add(this))
                        (_readers ??= new()).Add(reader, this);
                    detachedBefore = Math.Max(detachedBefore, reader._detachedInputCutoff);
                }

                // Remember the admission on every source while the reader is live. Lean keeps
                // the reader's address for the whole run. A scalar on the source preserves the
                // same decision after the reader and all of its data have been collected.
                if (!RaiseCutoff(detachedBefore) || _sources is null)
                    return;
                var work = new Stack<InputDependencies>();
                work.Push(this);
                while (work.TryPop(out var node))
                {
                    foreach (var source in node._sources!)
                        if (source.RaiseCutoff(node._detachedInputCutoff) && source._sources is not null)
                            work.Push(source);
                }
            }

            // A read must be external at every cell along its path to the detached reader.
            // Each path therefore contributes its smallest watermark, and any path may refuse.
            private bool RaiseCutoff(long cutoff)
            {
                cutoff = Math.Min(cutoff, Watermark);
                if (cutoff <= _detachedInputCutoff)
                    return false;
                _detachedInputCutoff = cutoff;
                return true;
            }

            internal bool Note(long serial, long serving)
            {
                if (serial < serving && serial < _detachedInputCutoff)
                    return true;
                if (!Record(serial) || _readers is null)
                    return false;

                var work = new Stack<InputDependencies>();
                work.Push(this);
                while (work.TryPop(out var node))
                {
                    foreach (var (reader, _) in node._readers!)
                        if (reader.Record(serial) && reader._readers is not null)
                            work.Push(reader);
                }
                return false;
            }

            private bool Record(long serial)
            {
                if (serial >= Watermark || serial >= _least)
                    return false;
                Volatile.Write(ref _least, serial);
                return true;
            }
        }
    }

    // How a refused detached reuse names where the binding lives. Presentation only (Lean `detachedReadDescription`).
    private const string DetachedReuseDescription = "an enclosing call";

    /// <summary>
    /// THE INPUT RECORD of the retained binding cell <paramref name="cell"/>, or null for every other cell
    /// (a parameter row's own cell, an argument's cell): the record its row's context was marked with,
    /// when it belongs to this very cell.
    /// </summary>
    private static AliasCellInputs? RetainedCellRecord(NeedCell cell)
        => cell.Suspension?.Caller.InputRecord is { } record && ReferenceEquals(record.Cell, cell) ? record : null;

    /// <summary>
    /// THE JUDGMENT OF A REUSE of the retained cell <paramref name="cell"/> by the reader <paramref name="ctx"/>,
    /// BEFORE its channel runs (ledger R-1; Lean <c>judgeRetainedCellReuse</c>): the cell's refusal for a
    /// reader that detaches an input the cell is known to have read, or null — then the reader is admitted,
    /// and for a reader inside a retained cell's computation the cell's recorded read becomes that cell's
    /// read too (<see cref="AliasCellInputs.Admit"/>). A reader outside every exported evaluation and every
    /// retained cell's computation is never judged (Lean's judgment changes nothing for it). A run that has
    /// already ended in a terminal failure reports that failure, as every later operation of it does: the
    /// failure that has occurred keeps its precedence.
    /// </summary>
    internal static EvalError? RetainedCellAdmission(NeedCell cell, in EvalCtx ctx)
    {
        if (ctx.CallStack is not AnnotatedReadOnlyList<Algorithm>)
            return null;
        return JudgeRetainedCellReuse(cell, ctx);
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalError? JudgeRetainedCellReuse(NeedCell cell, EvalCtx ctx)
    {
        if (!ctx.Budget.JudgesRetainedCellReuse || RetainedCellRecord(cell) is not { } record)
            return null;
        if (ctx.Budget.CheckContinuation() is { } terminal)
            return terminal;
        return record.Admit(ctx.DetachedBefore, ctx.InputRecord);
    }

    /// <summary>
    /// A retained cell's VALUE read as a REUSE by the reader <paramref name="ctx"/>: a runtime alias's bare
    /// read and a value view's zero-supply invocation (ledger R-1; Lean <c>reuseRetainedCell</c> in
    /// <c>aliasValue</c> and the value view's demand). The reader is judged first; an admitted reader's
    /// demand runs SERVING its watermark, so a read the cell's computation makes now through an activation
    /// the reader detaches is refused where it happens. Out of line, with its asynchronous twin, so that a
    /// caller's asynchronous state machine is the one it had before the judgment existed: the caller awaits
    /// one call whose arguments are evaluated before the await, and nothing is spilled across it.
    /// </summary>
    internal static EvalResult<CountedResult> RetainedCellValue(NeedCell cell, EvalCtx ctx)
        => ctx.CallStack is AnnotatedReadOnlyList<Algorithm> ? JudgedRetainedCellValue(cell, ctx) : cell.Demand();

    /// <summary>MIRROR OF <see cref="RetainedCellValue"/> — keep in lock-step.</summary>
    internal static ValueTask<EvalResult<CountedResult>> RetainedCellValueAsync(NeedCell cell, EvalCtx ctx)
        => ctx.CallStack is AnnotatedReadOnlyList<Algorithm> ? JudgedRetainedCellValueAsync(cell, ctx) : cell.DemandAsync();

    /// <summary>
    /// <see cref="RetainedCellValue"/> for an ANNOTATED reader (inside an exported evaluation or a retained
    /// cell's computation): the judgment, then the demand between the two halves of the serving bracket
    /// (<see cref="EvaluationBudget.EnterServing"/> / <see cref="EvaluationBudget.ExitServing"/>, which keep
    /// the entry watermark on the budget, so nothing is held across the demand).
    /// </summary>
    private static EvalResult<CountedResult> JudgedRetainedCellValue(NeedCell cell, EvalCtx ctx)
    {
        if (JudgeRetainedCellReuse(cell, ctx) is { } refusal)
            return refusal;
        ctx.Budget.EnterServing(ctx.DetachedBefore);
        try { return cell.Demand(); }
        finally { ctx.Budget.ExitServing(); }
    }

    /// <summary>MIRROR OF <see cref="JudgedRetainedCellValue"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> JudgedRetainedCellValueAsync(NeedCell cell, EvalCtx ctx)
    {
        if (JudgeRetainedCellReuse(cell, ctx) is { } refusal)
            return refusal;
        ctx.Budget.EnterServing(ctx.DetachedBefore);
        try { return await cell.DemandAsync().ConfigureAwait(false); }
        finally { ctx.Budget.ExitServing(); }
    }
}
