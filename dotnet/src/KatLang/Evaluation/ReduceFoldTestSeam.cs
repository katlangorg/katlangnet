namespace KatLang.Evaluation;

/// <summary>
/// Internal TEST seam that withholds the STREAMED route of a <c>reduce</c> fold
/// (<c>Evaluator.ReduceFold.Stream</c>) from folds evaluated in the activating flow, so a reducer that
/// leads with its accumulator takes the general route, one suspended step per element. Tests use it
/// as the oracle the streamed route is compared with (values, errors, effects and their order, budget
/// counters); production code never activates it, and an ordinary fold reads one unset
/// <see cref="AsyncLocal{T}"/> when it begins.
/// </summary>
internal static class ReduceFoldTestSeam
{
    private static readonly AsyncLocal<bool> Ambient = new();

    /// <summary>Whether folds evaluated in the current flow take the general route only.</summary>
    internal static bool WithholdsStreaming => Ambient.Value;

    /// <summary>Withholds the streamed route from folds evaluated in this flow, until disposed.</summary>
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
