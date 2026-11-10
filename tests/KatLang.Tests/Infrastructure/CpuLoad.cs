namespace KatLang.TestInfrastructure;

/// <summary>
/// The stress load of the process-isolated stack sweeps: <see cref="Environment.ProcessorCount"/>
/// background threads spinning until disposed; every other one allocates short-lived arrays so
/// gen-0 collections run during the sweep. JIT tier-up and GC pauses then perturb frame sizes and
/// timing while the sweep runs. Used only inside <see cref="SubprocessProbe"/> children
/// (<c>EvaluatorOpenChainStackProcessTests</c>, <c>DeferredCompileStackProcessTests</c>).
/// </summary>
internal sealed class CpuLoad : IDisposable
{
    private readonly CancellationTokenSource _stop = new();
    private readonly List<Thread> _threads = [];
    private readonly int _collectionsAtStart = GC.CollectionCount(0);

    public int Threads => _threads.Count;

    public int Collections => GC.CollectionCount(0) - _collectionsAtStart;

    public static CpuLoad Start()
    {
        var load = new CpuLoad();
        var token = load._stop.Token;
        for (var i = 0; i < Environment.ProcessorCount; i++)
        {
            var allocate = i % 2 == 1;
            var thread = new Thread(() =>
            {
                var sink = 0L;
                while (!token.IsCancellationRequested)
                {
                    if (allocate)
                        sink += new byte[1024 + (int)(sink & 4095)].Length;
                    else
                        sink = unchecked(sink * 31 + 7);
                }

                GC.KeepAlive(sink);
            }) { IsBackground = true };
            thread.Start();
            load._threads.Add(thread);
        }

        return load;
    }

    public void Dispose()
    {
        _stop.Cancel();
        foreach (var thread in _threads)
            thread.Join();
        _stop.Dispose();
    }
}
