using System.Runtime.CompilerServices;

namespace KatLang.Evaluation;

/// <summary>
/// Internal TEST seam that counts the reads of <see cref="EvalError.WithContext.Inner"/> made in the
/// activating flow. Every reader that moves down a chain of context frames — a classification, the Q-36
/// nesting rebuild, the message formatter, record equality and hashing — reads <c>Inner</c> once per
/// frame it passes, so the count is the CONTEXT-CHAIN WORK of what the flow did, kept apart from the
/// frames it constructed (building a frame reads no <c>Inner</c>). Tests bound it deterministically as
/// a deep failure's frames grow (<c>DeepFailureUnwindScalingTests</c>) instead of timing a run.
///
/// <para>Flow-scoped: a recorder counts the reads of its own flow and of every flow that inherits its
/// <see cref="ExecutionContext"/> — the awaits, stack hops and host-operation continuations of a run
/// started inside it — and never those of a concurrent run. Passive: it decides nothing. Production code
/// never activates it; while no recorder is active anywhere in the process, a read pays one static
/// load.</para>
/// </summary>
internal static class ContextChainReadTestSeam
{
    private static int s_active;

    private static readonly AsyncLocal<Recorder?> Ambient = new();

    /// <summary>Whether any recorder is active in the process (the one test a read pays without one).</summary>
    internal static bool IsActive => Volatile.Read(ref s_active) != 0;

    /// <summary>Counts one read for the current flow's recorder, if it has one.</summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    internal static void NoteRead() => Ambient.Value?.Count();

    /// <summary>Counts the reads made in this flow from zero, until disposed.</summary>
    internal static Recorder Activate()
    {
        var recorder = new Recorder(Ambient.Value);
        Interlocked.Increment(ref s_active);
        Ambient.Value = recorder;
        return recorder;
    }

    /// <summary>One activation's count; disposing it restores the enclosing recorder.</summary>
    internal sealed class Recorder(Recorder? previous) : IDisposable
    {
        private long _reads;
        private int _disposed;

        /// <summary>The reads counted so far.</summary>
        internal long Reads => Interlocked.Read(ref _reads);

        internal void Count()
        {
            // A continuation may inherit this recorder and resume after its scope ends.
            if (Volatile.Read(ref _disposed) == 0)
                Interlocked.Increment(ref _reads);
        }

        public void Dispose()
        {
            if (Interlocked.Exchange(ref _disposed, 1) != 0)
                return;
            Ambient.Value = previous;
            Interlocked.Decrement(ref s_active);
        }
    }
}
