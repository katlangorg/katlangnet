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
/// watermark at its establishment and the activations below it that its computation has read inputs
/// through. The row's context is marked with the record (<see cref="EvalCtx.InputRecord"/>, carried on the
/// call-stack node like the watermark), so every input read of the cell's computation records itself on
/// it: a captured parameter read through its owner's activation (<see cref="CapturedParameterActivation"/>),
/// an admitted local-only property read through its key's activation
/// (<see cref="GetOrEvaluateZeroArgPropertyResultCore"/>) and an admitted access of a local-only member
/// on a structural route through its owners' activations (<see cref="AliasCellInputs.AdmitMemberAccess"/>). A local-only alias's row is supplied
/// at the watermark of its declaring level (<see cref="EvalCtx.Reattach"/>), whichever reader reaches it
/// first, so the cell is never tied to the reader that happened to establish it.</para>
/// <para>THE REUSE. A READER's use of the cell's VALUE or CALLABLE (the bare read, the value view's
/// zero-supply invocation, the runtime step of the alias chase) is JUDGED BEFORE THE CHANNEL RUNS
/// (<see cref="RetainedCellAdmission"/>): a reader that DETACHES an input the cell is known to have read is
/// refused with the alias's own <see cref="EvalError.LocalOnlyProperty"/> and nothing of the cell runs — no
/// demand, no effect. Every other reader is ADMITTED and the channel runs serving its detached owners
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
    /// work — the serials its computation has read an input through (each once) with the LEAST of them, the
    /// owners detached by readers ADMITTED to reuse the cell, and the records of the cells whose computation
    /// reused this one (its reads are theirs too, while they are inputs of those cells as well). A reuse is
    /// refused exactly to a reader that detaches one of the reads (Lean <c>RetainedCellReuse.trace_dependsFor</c>):
    /// a reader detaches only its enclosing calls, so the read of a returned callable's level is shared.
    /// Every operation runs under the run's ONE retained-cell gate
    /// (<see cref="EvaluationBudget.RetainedCellGate"/>): a note checks and writes every record it reaches
    /// as one step, as Lean's does.
    /// <para>Each live reader keeps the dependency information for its inputs. A producer points to its
    /// readers weakly and keeps the applicable detached activation serials along any forwarding path.
    /// Those serials survive collection of a reader. A live path can outlive an intermediate call
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

        // Accessibility has already checked every requirement. Commit the reads as one operation,
        // so a later owner's refusal cannot leave a prefix on the retained cell.
        internal bool AdmitMemberAccess(List<long>? owners)
        {
            lock (_budget.RetainedCellGate)
                return _inputs.TakeReads(owners, _budget.ServingDetached);
        }

        /// <summary>
        /// THE JUDGMENT of a reuse by a reader whose watermark is <paramref name="detachedBefore"/>, whose detached
        /// owners are <paramref name="owners"/> and whose own record (inside a retained cell's computation) is
        /// <paramref name="reader"/>, BEFORE the channel runs (Lean <c>CellRecords.admit</c>): the cell's refusal
        /// when the reader DETACHES an input the cell is known to have read — one of its recorded reads is an
        /// enclosing call of the reader below the reader's watermark (Lean <c>CellInputs.dependsFor</c>, exact:
        /// RETURNED CALLABLES ACROSS DETACHED READS); the same refusal when one of its recorded reads, taken into
        /// the reader's record, lands among the owners detached by a reader admitted there while that is served (then none is taken);
        /// else every recorded read becomes the reader's record's read and the reader is ADMITTED — its
        /// detached owners join the recorded reader owners, and subsequent reads propagate to the reader. One step
        /// under the gate.
        /// </summary>
        internal EvalError? Admit(long detachedBefore, DetachedOwnerSet? owners, AliasCellInputs? reader)
        {
            lock (_budget.RetainedCellGate)
            {
                if (_inputs.DependsFor(detachedBefore, owners))
                    return Refusal();
                if (reader is not null && !_inputs.ForwardReadsTo(reader._inputs, _budget.ServingDetached))
                    return Refusal();
                _inputs.Admit(DetachedOwnerSet.Union(null, owners, detachedBefore), reader?._inputs);
                return null;
            }
        }

        // Only scalar access facts and edges belong here. In particular this object has no pointer to
        // its owning AliasCellInputs, which would also keep the intermediate NeedCell and call alive.
        private sealed class InputDependencies(long watermark)
        {
            private long _least = long.MaxValue;
            private DetachedOwnerSet? _admittedOwners;
            internal long Watermark { get; } = watermark;
            private HashSet<InputDependencies>? _sources;
            private ConditionalWeakTable<InputDependencies, object>? _readers;

            // Every serial below the watermark the computation has read an input through, each once
            // (membership in Lean `CellInputs.reads`); null while it has read none. Written and read under the gate.
            private HashSet<long>? _reads;

            internal long Least => Volatile.Read(ref _least);
            internal bool DependsBelow(long detachedBefore) => Least < detachedBefore;

            // Lean `CellInputs.dependsFor`: a recorded read below the reader's watermark that is one of its
            // detached owners (its enclosing calls). No owner, or no read below the watermark: never.
            internal bool DependsFor(long detachedBefore, DetachedOwnerSet? owners)
            {
                if (owners is null || Least >= detachedBefore)
                    return false;
                foreach (var serial in _reads!)
                {
                    if (serial < detachedBefore && owners.Contains(serial))
                        return true;
                }
                return false;
            }

            // The catch-up of an admission (Lean: the `reads` fold of `CellRecords.admit`): every recorded read
            // becomes the reader's read, as far as it is an input there; false — and nothing recorded — when one
            // of them would be refused there while `serving` is served.
            internal bool ForwardReadsTo(InputDependencies reader, DetachedOwnerSet? serving)
                => reader.TakeReads(_reads, serving);

            internal bool TakeReads(IReadOnlyCollection<long>? reads, DetachedOwnerSet? serving)
            {
                if (reads is null) return true;
                foreach (var serial in reads)
                {
                    if (Refuses(serial, serving))
                        return false;
                }
                foreach (var serial in reads)
                    _ = Note(serial, serving: null);
                return true;
            }

            private bool Refuses(long serial, DetachedOwnerSet? serving) => serving?.Contains(serial) == true && _admittedOwners?.Contains(serial) == true;

            internal void Admit(DetachedOwnerSet? owners, InputDependencies? reader)
            {
                if (reader is not null && !ReferenceEquals(reader, this))
                {
                    // A live reader needs all its inputs. Producers point back weakly so the
                    // completion of a call can release both its cell and its dependency record.
                    if ((reader._sources ??= []).Add(this))
                        (_readers ??= new()).Add(reader, this);
                    owners = DetachedOwnerSet.Union(owners, reader._admittedOwners, Watermark);
                }

                // Propagate detached serials back to the sources while the reader is live. Each source
                // keeps only reads external at every cell on this path, even after the reader is collected.
                if (!AddOwners(owners) || _sources is null) return;
                var work = new Stack<InputDependencies>();
                work.Push(this);
                while (work.TryPop(out var node))
                {
                    foreach (var source in node._sources!)
                        if (source.AddOwners(node._admittedOwners) && source._sources is not null)
                            work.Push(source);
                }
            }

            private bool AddOwners(DetachedOwnerSet? owners)
            {
                var previous = _admittedOwners;
                _admittedOwners = DetachedOwnerSet.Union(previous, owners, Watermark);
                return !ReferenceEquals(previous, _admittedOwners);
            }

            internal bool Note(long serial, DetachedOwnerSet? serving)
            {
                if (Refuses(serial, serving))
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

            // Records a read below the watermark that is new to the record (Lean `CellInputs.note`): true then, so
            // the read is passed on to the readers; a read the record already has reached them when it was first
            // recorded, and an admission forwards every read the reader has not seen (ForwardReadsTo).
            private bool Record(long serial)
            {
                if (serial >= Watermark)
                    return false;
                var reads = _reads ??= [];
                if (!reads.Add(serial))
                    return false;
                if (serial < _least)
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
        return record.Admit(ctx.DetachedBefore, ctx.DetachedOwners, ctx.InputRecord);
    }

    /// <summary>
    /// A retained cell's VALUE read as a REUSE by the reader <paramref name="ctx"/>: a runtime alias's bare
    /// read and a value view's zero-supply invocation (ledger R-1; Lean <c>reuseRetainedCell</c> in
    /// <c>aliasValue</c> and the value view's demand). The reader is judged first; an admitted reader's
    /// demand runs serving its detached owners, so a read the cell's computation makes now through an activation
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
    /// the previously served owners on the budget, so nothing is held across the demand).
    /// </summary>
    private static EvalResult<CountedResult> JudgedRetainedCellValue(NeedCell cell, EvalCtx ctx)
    {
        if (JudgeRetainedCellReuse(cell, ctx) is { } refusal)
            return refusal;
        ctx.Budget.EnterServing(ctx.ServingOwners);
        try { return cell.Demand(); }
        finally { ctx.Budget.ExitServing(); }
    }

    /// <summary>MIRROR OF <see cref="JudgedRetainedCellValue"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> JudgedRetainedCellValueAsync(NeedCell cell, EvalCtx ctx)
    {
        if (JudgeRetainedCellReuse(cell, ctx) is { } refusal)
            return refusal;
        ctx.Budget.EnterServing(ctx.ServingOwners);
        try { return await cell.DemandAsync().ConfigureAwait(FoldTrampoline.CaptureFoldContext); }
        finally { ctx.Budget.ExitServing(); }
    }
}
