namespace KatLang.Evaluation;

/// <summary>
/// Internal TEST seam that records, weakly, every lazy-collection stage (<c>map</c>, <c>filter</c>,
/// <c>take</c>) built in the activating flow, so a test can count the stages a run still keeps
/// reachable: the reachability guard of the ownership a stage releases once it runs no further step
/// (lazy collections, issue #204). It records the same way the positions of every list literal built
/// with a deferred element and every deferred element's suspension (the literal's environment), which
/// an element's cell releases once its VALUE computation has ended (2026-11-25). Production code never
/// activates it: while no recorder is active in the process, building a stage or a literal pays one
/// static load.
/// </summary>
internal static class LazyStageTestSeam
{
    private static readonly AsyncLocal<Recorder?> Ambient = new();
    // How many recorders are active in the process: while none is, a note pays one static load.
    private static int s_active;

    /// <summary>Records a stage just built, when a recorder is active in the current flow.</summary>
    internal static void Note(object stage)
    {
        if (Volatile.Read(ref s_active) != 0) Ambient.Value?.Add(stage);
    }

    /// <summary>Records the positions of a list literal just built with a deferred element.</summary>
    internal static void NoteLiteral(object positions)
    {
        if (Volatile.Read(ref s_active) != 0) Ambient.Value?.AddLiteral(positions);
    }

    /// <summary>Records a deferred list element's suspension just created.</summary>
    internal static void NoteElementSuspension(object suspension)
    {
        if (Volatile.Read(ref s_active) != 0) Ambient.Value?.AddElementSuspension(suspension);
    }

    /// <summary>Records the stages built in this flow, until disposed.</summary>
    internal static Recorder Activate()
    {
        var recorder = new Recorder(Ambient.Value);
        Interlocked.Increment(ref s_active);
        Ambient.Value = recorder;
        return recorder;
    }

    /// <summary>The stages, literals and element suspensions one activation recorded.</summary>
    internal sealed class Recorder(Recorder? previous) : IDisposable
    {
        private readonly List<WeakReference> _stages = [];
        private readonly List<WeakReference> _literals = [];
        private readonly List<WeakReference> _elementSuspensions = [];
        private int _disposed;

        /// <summary>How many stages were built.</summary>
        internal int Built => Count(_stages);

        /// <summary>How many of them are still reachable (meaningful right after a full collection).</summary>
        internal int Alive() => CountAlive(_stages);

        /// <summary>How many list literals with a deferred element were built.</summary>
        internal int LiteralsBuilt => Count(_literals);

        /// <summary>How many of those literals' positions are still reachable (after a full collection).</summary>
        internal int LiteralsAlive() => CountAlive(_literals);

        /// <summary>How many deferred list elements' suspensions were created.</summary>
        internal int ElementSuspensionsBuilt => Count(_elementSuspensions);

        /// <summary>How many of those suspensions are still reachable (after a full collection).</summary>
        internal int ElementSuspensionsAlive() => CountAlive(_elementSuspensions);

        internal void Add(object stage) => Record(_stages, stage);

        internal void AddLiteral(object positions) => Record(_literals, positions);

        internal void AddElementSuspension(object suspension) => Record(_elementSuspensions, suspension);

        private static void Record(List<WeakReference> list, object target)
        {
            lock (list) list.Add(new WeakReference(target));
        }

        private static int Count(List<WeakReference> list)
        {
            lock (list) return list.Count;
        }

        private static int CountAlive(List<WeakReference> list)
        {
            lock (list) return list.Count(static entry => entry.IsAlive);
        }

        public void Dispose()
        {
            if (Interlocked.Exchange(ref _disposed, 1) != 0) return;
            Ambient.Value = previous;
            Interlocked.Decrement(ref s_active);
        }
    }
}
