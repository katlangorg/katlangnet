namespace KatLang.Evaluation.Caching;

/// <summary>
/// Evaluator-side origin of a zero-arg property cache request.
/// These categories identify the four Stage 1 wiring points only.
/// </summary>
internal enum ZeroArgPropertyAccessKind
{
    Lexical,
    Structural,
    CountedLexical,
    CountedStructural,
}

/// <summary>
/// Snapshot of one access category's request counters.
/// Requests should always equal hits plus misses.
/// Stores count successful insertions after misses.
/// </summary>
internal readonly record struct ZeroArgPropertyResultCacheAccessSnapshot(
    ZeroArgPropertyAccessKind AccessKind,
    int Requests,
    int Hits,
    int Misses,
    int Stores);

/// <summary>
/// Per-run cache diagnostics snapshot.
/// RepeatedMissRequests counts requests for keys that had already missed earlier
/// in the same run and were still not stored when requested again.
/// </summary>
internal readonly record struct ZeroArgPropertyResultCacheSnapshot(
    int TotalRequests,
    int Hits,
    int Misses,
    int Stores,
    int DistinctKeysCreated,
    int RepeatedMissRequests,
    int MaxCacheSize,
    IReadOnlyList<ZeroArgPropertyResultCacheAccessSnapshot> AccessKinds)
{
    public ZeroArgPropertyResultCacheAccessSnapshot GetAccessKind(ZeroArgPropertyAccessKind accessKind)
        => AccessKinds[(int)accessKind];
}

internal sealed class ZeroArgPropertyResultCacheStatsCollector
{
    private static readonly ZeroArgPropertyAccessKind[] AccessKindValues = Enum.GetValues<ZeroArgPropertyAccessKind>();

    private readonly int[] _requestsByKind = new int[AccessKindValues.Length];
    private readonly int[] _hitsByKind = new int[AccessKindValues.Length];
    private readonly int[] _missesByKind = new int[AccessKindValues.Length];
    private readonly int[] _storesByKind = new int[AccessKindValues.Length];

    public int TotalRequests { get; private set; }

    public int Hits { get; private set; }

    public int Misses { get; private set; }

    public int Stores { get; private set; }

    public void RecordRequest(ZeroArgPropertyAccessKind accessKind)
    {
        TotalRequests++;
        _requestsByKind[(int)accessKind]++;
    }

    public void RecordHit(ZeroArgPropertyAccessKind accessKind)
    {
        Hits++;
        _hitsByKind[(int)accessKind]++;
    }

    public void RecordMiss(ZeroArgPropertyAccessKind accessKind)
    {
        Misses++;
        _missesByKind[(int)accessKind]++;
    }

    public void RecordStore(ZeroArgPropertyAccessKind accessKind)
    {
        Stores++;
        _storesByKind[(int)accessKind]++;
    }

    public ZeroArgPropertyResultCacheSnapshot CreateSnapshot(
        int distinctKeysCreated,
        int repeatedMissRequests,
        int maxCacheSize)
    {
        var accessKinds = new ZeroArgPropertyResultCacheAccessSnapshot[AccessKindValues.Length];
        for (var index = 0; index < AccessKindValues.Length; index++)
        {
            accessKinds[index] = new ZeroArgPropertyResultCacheAccessSnapshot(
                AccessKindValues[index],
                _requestsByKind[index],
                _hitsByKind[index],
                _missesByKind[index],
                _storesByKind[index]);
        }

        return new ZeroArgPropertyResultCacheSnapshot(
            TotalRequests,
            Hits,
            Misses,
            Stores,
            distinctKeysCreated,
            repeatedMissRequests,
            maxCacheSize,
            accessKinds);
    }
}