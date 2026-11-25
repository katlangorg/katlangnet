namespace KatLang.Evaluation;

/// <summary>
/// INTERNAL TEST SEAM for the <c>tick()</c> counter's exhaustion boundary: a run whose budget is created
/// while a seam is active starts its counter at <see cref="InitialCount"/> instead of zero, so a test can
/// reach <see cref="EvaluationBudget.MaxTickCount"/> without executing 2^63 ticks. It is ambient per
/// asynchronous flow (like <see cref="InvocationPlanTestSeam"/>) and is read ONCE, when a budget is
/// created; the counter itself lives on that budget alone. No production entry point activates it.
/// </summary>
internal sealed class TickCounterTestSeam
{
    private static readonly AsyncLocal<TickCounterTestSeam?> Ambient = new();

    private TickCounterTestSeam(long initialCount) => InitialCount = initialCount;

    /// <summary>The counter value a run created under this seam starts with.</summary>
    internal long InitialCount { get; }

    /// <summary>The seam a budget created in the current flow captures, if any.</summary>
    internal static TickCounterTestSeam? Current => Ambient.Value;

    /// <summary>Starts every run created in this flow at <paramref name="initialCount"/> until disposed.</summary>
    internal static IDisposable Activate(long initialCount)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(initialCount);
        var previous = Ambient.Value;
        Ambient.Value = new TickCounterTestSeam(initialCount);
        return new Restore(previous);
    }

    private sealed class Restore(TickCounterTestSeam? previous) : IDisposable
    {
        public void Dispose() => Ambient.Value = previous;
    }
}
