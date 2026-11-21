namespace KatLang.Evaluation;

/// <summary>
/// INTERNAL TEST SEAM for the MUTATION GUARD of detached exported evaluation (EXPORTED-DETACHED,
/// November 2026): a run whose budget is created while the seam is active evaluates an exported
/// zero-argument property in its READER's context, as the evaluator did before it enforced the
/// exposure classification (<c>Evaluator.DetachedEvaluation</c> returns its input unchanged). The
/// refusal tests run their mis-exposed trees under it to prove that detachment, and nothing else,
/// produces their refusals. It disables detachment only: captured reads stay lexical-only. Ambient
/// per asynchronous flow (like <see cref="TickCounterTestSeam"/>) and read ONCE, when a budget is
/// created. No production entry point activates it.
/// </summary>
internal sealed class DetachedEvaluationTestSeam
{
    private static readonly AsyncLocal<DetachedEvaluationTestSeam?> Ambient = new();

    private DetachedEvaluationTestSeam()
    {
    }

    /// <summary>The seam a budget created in the current flow captures, if any.</summary>
    internal static DetachedEvaluationTestSeam? Current => Ambient.Value;

    /// <summary>Makes every run created in this flow evaluate exported properties attached, until disposed.</summary>
    internal static IDisposable DisableDetachment()
    {
        var previous = Ambient.Value;
        Ambient.Value = new DetachedEvaluationTestSeam();
        return new Restore(previous);
    }

    private sealed class Restore(DetachedEvaluationTestSeam? previous) : IDisposable
    {
        public void Dispose() => Ambient.Value = previous;
    }
}
