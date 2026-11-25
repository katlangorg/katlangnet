using System.Runtime.CompilerServices;

namespace KatLang;

/// <summary>
/// One note of <see cref="EvalError.OutputSpreadNotes"/> (declaration-level output spreading, diagnostics only):
/// the written call the front end spread (<see cref="CallText"/>), the marked declaration that made it spread and
/// the line of its marker (absent for a module's locationless declaration), and — when the failing call's
/// arguments determine it — how many arguments the spread supplied.
/// </summary>
internal sealed record OutputSpreadNote(string CallText, string DeclarationName, int? DeclarationLine, int? SuppliedCount);

public static partial class Evaluator
{
    /// <summary>
    /// DECLARATION-LEVEL OUTPUT SPREADING's one evaluator-side change, C# wording only. The front end spreads
    /// every eligible call to a declaration written with <c>*</c> (<c>A(x, y)* = x, y</c>) — inserting the
    /// ordinary <see cref="Expr.SequenceSpread"/>, marked with <see cref="Expr.SequenceSpread.InsertedFor"/> —
    /// so <c>count(A(1, 2))</c> supplies two arguments although none was written. When such a call fails with
    /// its OWN cardinality error or META refusal (<see cref="NoteOutputSpreads"/>), the error carries one note per
    /// inserted slot, naming the call and the declaration. Applied where each call's own result returns, BEFORE
    /// its call frame is attached, on the error path only; no value, effect, error kind, payload, code or span
    /// changes, and no evaluation frame is added (like <see cref="WithCallCtx{T}"/>, the check runs after the
    /// call's own evaluation returned, and only its error path does any work).
    /// </summary>
    private static EvalResult<T> WithOutputSpreadNotes<T>(OutputBundle? args, EvalResult<T> result)
        => result.IsError && args is { Count: > 0 } ? NoteOutputSpreads(args, result.Error, otherSuppliedSlots: 0) : result;

    /// <summary>
    /// <see cref="WithOutputSpreadNotes{T}(OutputBundle, EvalResult{T})"/> for a dot edge with an argument list. An extension call
    /// <c>R.F(args)</c> supplies its receiver as the leading argument (DOT-03), a member call <c>R.F(args)</c>
    /// does not, and a runtime receiver decides between them: the count a note states accounts for the receiver
    /// slot only when the edge's static route is known.
    /// </summary>
    private static EvalResult<T> WithOutputSpreadNotes<T>(Expr.DotCall dot, EvalResult<T> result)
        => result.IsError && dot.Args is { Count: > 0 } args
            ? NoteOutputSpreads(args, result.Error, DotReceiverSupplySlots(dot))
            : result;

    private static int? DotReceiverSupplySlots(Expr.DotCall dot)
        => dot.UsesDotMissIntrinsic()
            ? null
            : dot.EffectiveMissSelection() switch
            {
                LexicalFallbackSelection.Always => 1,
                LexicalFallbackSelection.Never => 0,
                _ => null,
            };

    /// <summary>
    /// The notes of <see cref="WithOutputSpreadNotes{T}(OutputBundle, EvalResult{T})"/>. The call's OWN failure is the one its binding raises
    /// before anything it calls can: a bare <see cref="EvalError.ArityMismatch"/> or
    /// <see cref="EvalError.VariadicArityMismatch"/> (a failure from inside the callee arrives inside that inner
    /// call's frame) — every spread slot feeds the count, so each inserted one is named — or the canonical META refusal
    /// inside exactly its binding frame (<see cref="AnnotateMetaBindingRefusal"/>), named only when the refused cell
    /// provably came from the inserted spread: the refusal has no written occurrence (a spread-produced item; a written
    /// argument positions it at that argument, META-DIAG-2) and that spread is the call's ONLY spread slot. The supplied
    /// count is stated when the call has exactly one spread slot (the arguments then determine it: every other slot
    /// supplies one); otherwise the note says the call was spread into separate arguments.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalError NoteOutputSpreads(OutputBundle args, EvalError error, int? otherSuppliedSlots)
    {
        List<Expr.SequenceSpread>? inserted = null;
        var spreadSlots = 0;
        for (var index = 0; index < args.Count; index++)
        {
            if (args[index] is not Expr.SequenceSpread spread)
                continue;
            spreadSlots++;
            if (spread.InsertedFor is not null)
                (inserted ??= []).Add(spread);
        }

        if (inserted is null)
            return error;

        return error switch
        {
            EvalError.ArityMismatch { OutputSpreadNotes: null } arity
                => arity with { OutputSpreadNotes = OutputSpreadNotesOf(inserted, SuppliedBySoleSpread(args.Count, spreadSlots, otherSuppliedSlots, arity.Actual)) },
            EvalError.VariadicArityMismatch { OutputSpreadNotes: null } variadic
                => variadic with { OutputSpreadNotes = OutputSpreadNotesOf(inserted, SuppliedBySoleSpread(args.Count, spreadSlots, otherSuppliedSlots, variadic.Actual)) },
            EvalError.WithContext { Inner: EvalError.NotAnAlgorithm { Description: MetaRefusalDescription, OutputSpreadNotes: null, Span: null } refusal } frame
                when spreadSlots == 1
                => frame.WithInner(refusal with { OutputSpreadNotes = OutputSpreadNotesOf(inserted, suppliedCount: null) }),
            _ => error,
        };
    }

    /// <summary>
    /// <see cref="WithOutputSpreadNotes{T}(OutputBundle, EvalResult{T})"/> for a result whose call frame is already attached
    /// (the <c>.Algorithm</c> callee dispatch, whose every return carries it): the notes go on the error inside that one frame.
    /// </summary>
    private static EvalResult<T> WithOutputSpreadNotesInsideFrame<T>(OutputBundle args, EvalResult<T> result)
    {
        if (!result.IsError || args.Count == 0 || result.Error is not EvalError.WithContext frame)
            return result;
        var noted = NoteOutputSpreads(args, frame.Inner, otherSuppliedSlots: 0);
        return ReferenceEquals(noted, frame.Inner) ? result : frame.WithInner(noted);
    }

    /// <summary>
    /// The count the call's one spread slot supplied: the supply minus the other written slots (one each) and the
    /// slots the call supplies besides its written arguments (a dot receiver); null when that is unknown.
    /// </summary>
    private static int? SuppliedBySoleSpread(int writtenSlots, int spreadSlots, int? otherSuppliedSlots, int supplied)
        => spreadSlots == 1 && otherSuppliedSlots is { } other && supplied - (writtenSlots - 1) - other is var count and >= 0
            ? count
            : null;

    private static IReadOnlyList<OutputSpreadNote> OutputSpreadNotesOf(List<Expr.SequenceSpread> inserted, int? suppliedCount)
    {
        var notes = new OutputSpreadNote[inserted.Count];
        for (var index = 0; index < inserted.Count; index++)
        {
            var spread = inserted[index];
            var marker = spread.InsertedFor!;
            notes[index] = new OutputSpreadNote(
                RenderSpreadCall(spread.Operand),
                marker.DeclarationName,
                marker.Span?.Start.Line,
                suppliedCount);
        }

        return notes;
    }

    /// <summary>
    /// The spread call as the note names it, WITH its argument list (<c>Fib(0, 1)</c>, <c>Lib.Pair(x, y)</c>,
    /// <c>v.F(1)</c>): the diagnostic renderer abbreviates every argument list to <c>(...)</c>, which would hide
    /// the call the note is about. Each argument keeps the renderer's own (bounded) spelling.
    /// </summary>
    private static string RenderSpreadCall(Expr call)
    {
        var (callee, args) = call switch
        {
            Expr.Call(var function, var callArgs) => (function, callArgs),
            Expr.DotCall { Args: { } dotArgs } dot => (dot with { Args = null }, dotArgs),
            _ => ((Expr?)null, (OutputBundle?)null),
        };
        if (callee is null || args is null)
            return ExprNameRenderer.Render(call, ExprNameMode.DiagnosticName);

        var renderedArgs = new string[args.Count];
        for (var index = 0; index < args.Count; index++)
            renderedArgs[index] = ExprNameRenderer.Render(args[index], ExprNameMode.DiagnosticName);
        return $"{ExprNameRenderer.Render(callee, ExprNameMode.DiagnosticName)}({ExprNameRenderer.BoundedJoin(renderedArgs, ", ")})";
    }
}
