namespace KatLang.Evaluation;

/// <summary>
/// INTERNAL TEST SEAM for the MUTATION GUARDS of detached exported evaluation (EXPORTED-DETACHED,
/// November 2026). Under <see cref="DisableDetachment"/> a run whose budget is created while the seam is
/// active evaluates an exported zero-argument property in its READER's context, as the evaluator did
/// before it enforced the exposure classification (<c>Evaluator.DetachedEvaluation</c> returns its input
/// unchanged): the refusal tests run their mis-exposed trees under it to prove that detachment, and nothing
/// else, produces their refusals. It disables detachment only: captured reads stay lexical-only. Under
/// <see cref="DisableRetainedCellJudgment"/> detachment stays on and the OLD REUSE PATH of a retained
/// runtime-alias cell is restored (ledger R-1, <c>Evaluator.RetainedCellAdmission</c>): no reuse is judged
/// — so a detached evaluation takes a cell an attached read established, and, since no reader is then
/// admitted, no later read of the cell's computation is refused either — and a local-only alias's row is
/// supplied in the using context, as before the judgment existed (<c>Evaluator.AliasCellContext</c>), so the
/// R-1 refusal tests can prove that the judgment produces their refusals. Ambient per asynchronous flow (like
/// <see cref="TickCounterTestSeam"/>) and read ONCE, when a budget is created. No production entry point
/// activates it.
/// </summary>
internal sealed class DetachedEvaluationTestSeam
{
    private static readonly AsyncLocal<DetachedEvaluationTestSeam?> Ambient = new();

    private DetachedEvaluationTestSeam(bool disablesDetachment, bool disablesRetainedCellJudgment)
    {
        DisablesDetachment = disablesDetachment;
        DisablesRetainedCellJudgment = disablesRetainedCellJudgment;
    }

    /// <summary>The seam a budget created in the current flow captures, if any.</summary>
    internal static DetachedEvaluationTestSeam? Current => Ambient.Value;

    /// <summary>Whether a run under this seam evaluates exported properties attached.</summary>
    internal bool DisablesDetachment { get; }

    /// <summary>Whether a run under this seam reuses retained alias cells without judging the reader.</summary>
    internal bool DisablesRetainedCellJudgment { get; }

    /// <summary>Makes every run created in this flow evaluate exported properties attached, until disposed.</summary>
    internal static IDisposable DisableDetachment() => Install(new DetachedEvaluationTestSeam(true, false));

    /// <summary>
    /// Makes every run created in this flow reuse retained runtime-alias cells without judging the reader,
    /// and supply a local-only alias's row in the using context (the reuse path before ledger R-1 was
    /// closed), until disposed. Detachment stays on.
    /// </summary>
    internal static IDisposable DisableRetainedCellJudgment() => Install(new DetachedEvaluationTestSeam(false, true));

    private static IDisposable Install(DetachedEvaluationTestSeam seam)
    {
        var previous = Ambient.Value;
        Ambient.Value = seam;
        return new Restore(previous);
    }

    private sealed class Restore(DetachedEvaluationTestSeam? previous) : IDisposable
    {
        public void Dispose() => Ambient.Value = previous;
    }
}
