namespace KatLang.Evaluation;

/// <summary>
/// Internal TEST seam that withholds the literal clause-run index (<c>Evaluator.LiteralClauseRun</c>) from the
/// clause-family preparations of runs whose preparation memo is created in the activating flow, so every clause of
/// such a run binds through the ordered route the index replaces. Tests use it as the oracle the indexed route is
/// compared with (values, errors, demands, effects, counters, clause attempts); production code never activates it,
/// and an ordinary run reads one unset <see cref="AsyncLocal{T}"/> when its first family is prepared.
/// </summary>
internal static class OrderedClauseDispatchTestSeam
{
    private static readonly AsyncLocal<bool> Ambient = new();

    /// <summary>Whether preparation memos created in the current flow withhold the literal clause-run index.</summary>
    internal static bool IsActive => Ambient.Value;

    /// <summary>Withholds the index from runs whose preparation memo is created in this flow, until disposed.</summary>
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
