namespace KatLang.Evaluation;

/// <summary>
/// Internal TEST seam that withholds INLINE resumptions from the synchronous fold pumps started in the activating
/// flow (<see cref="FoldTrampoline.TryRunSynchronously"/>): every suspended step's frames then register posted
/// resumptions through the pump's queue, as every pump did before inline resumptions. Tests use it as the oracle
/// the inline pump is compared with (values, effects and their order, threads, budget counters, allocation);
/// production code never activates it, and a pump reads one unset <see cref="AsyncLocal{T}"/> when it starts.
/// </summary>
internal static class FoldResumeTestSeam
{
    private static readonly AsyncLocal<bool> Ambient = new();

    /// <summary>Whether pumps started in the current flow withhold inline resumptions.</summary>
    internal static bool WithholdsInlineResumes => Ambient.Value;

    /// <summary>Withholds inline resumptions from pumps started in this flow, until disposed.</summary>
    internal static IDisposable Activate()
    {
        var previous = Ambient.Value;
        Ambient.Value = true;
        return new Restore(previous);
    }

    private sealed class Restore(bool previous) : IDisposable
    {
        public void Dispose() => Ambient.Value = previous;
    }
}
