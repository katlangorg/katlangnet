namespace KatLang.Evaluation;

/// <summary>
/// Internal TEST seam that records, weakly, every lazy-collection stage (<c>map</c>, <c>filter</c>,
/// <c>take</c>) built in the activating flow, so a test can count the stages a run still keeps
/// reachable: the reachability guard of the ownership a stage releases once it runs no further step
/// (lazy collections, issue #204). Production code never activates it; building a stage reads one
/// unset <see cref="AsyncLocal{T}"/>.
/// </summary>
internal static class LazyStageTestSeam
{
    private static readonly AsyncLocal<Recorder?> Ambient = new();

    /// <summary>Records a stage just built, when a recorder is active in the current flow.</summary>
    internal static void Note(object stage) => Ambient.Value?.Add(stage);

    /// <summary>Records the stages built in this flow, until disposed.</summary>
    internal static Recorder Activate()
    {
        var recorder = new Recorder(Ambient.Value);
        Ambient.Value = recorder;
        return recorder;
    }

    /// <summary>The stages one activation recorded.</summary>
    internal sealed class Recorder(Recorder? previous) : IDisposable
    {
        private readonly List<WeakReference> _stages = [];

        /// <summary>How many stages were built.</summary>
        internal int Built
        {
            get { lock (_stages) return _stages.Count; }
        }

        /// <summary>How many of them are still reachable (meaningful right after a full collection).</summary>
        internal int Alive()
        {
            lock (_stages) return _stages.Count(static stage => stage.IsAlive);
        }

        internal void Add(object stage)
        {
            lock (_stages) _stages.Add(new WeakReference(stage));
        }

        public void Dispose() => Ambient.Value = previous;
    }
}
