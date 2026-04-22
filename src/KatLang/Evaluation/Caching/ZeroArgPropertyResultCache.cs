using System.Runtime.CompilerServices;

namespace KatLang.Evaluation.Caching;

internal readonly record struct ZeroArgPropertyExecution(
    Algorithm Owner,
    Property Binding,
    ZeroArgPropertyAccessKind AccessKind,
    object ValueEnvironmentIdentity,
    object AlgorithmEnvironmentIdentity,
    object CountedParamEnvironmentIdentity);

internal readonly record struct ZeroArgPropertyResult(
    Result Value,
    int EmittedCount);

internal enum ZeroArgPropertyCacheAccessShape
{
    Lexical,
    Structural,
}

internal interface IZeroArgPropertyResultCache
{
    EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate);
}

internal readonly record struct ZeroArgPropertyCacheKey(
    ZeroArgPropertyCacheAccessShape AccessShape,
    object OwnerIdentity,
    object BindingIdentity,
    object ValueEnvironmentIdentity,
    object AlgorithmEnvironmentIdentity,
    object CountedParamEnvironmentIdentity)
{
    private static readonly object StructuralOwnerIdentity = new();

    public static ZeroArgPropertyCacheKey FromExecution(ZeroArgPropertyExecution execution)
        => new(
            GetAccessShape(execution.AccessKind),
            GetOwnerIdentity(execution),
            execution.Binding,
            execution.ValueEnvironmentIdentity,
            execution.AlgorithmEnvironmentIdentity,
            execution.CountedParamEnvironmentIdentity);

    private static ZeroArgPropertyCacheAccessShape GetAccessShape(ZeroArgPropertyAccessKind accessKind)
        => accessKind is ZeroArgPropertyAccessKind.Structural or ZeroArgPropertyAccessKind.CountedStructural
            ? ZeroArgPropertyCacheAccessShape.Structural
            : ZeroArgPropertyCacheAccessShape.Lexical;

    private static object GetOwnerIdentity(ZeroArgPropertyExecution execution)
        => GetAccessShape(execution.AccessKind) is ZeroArgPropertyCacheAccessShape.Structural
            ? StructuralOwnerIdentity
            : execution.Owner;
}

internal sealed class ZeroArgPropertyCacheKeyComparer : IEqualityComparer<ZeroArgPropertyCacheKey>
{
    public static ZeroArgPropertyCacheKeyComparer Instance { get; } = new();

    private ZeroArgPropertyCacheKeyComparer()
    {
    }

    public bool Equals(ZeroArgPropertyCacheKey x, ZeroArgPropertyCacheKey y)
        => x.AccessShape == y.AccessShape
            && ReferenceEquals(x.OwnerIdentity, y.OwnerIdentity)
            && ReferenceEquals(x.BindingIdentity, y.BindingIdentity)
            && ReferenceEquals(x.ValueEnvironmentIdentity, y.ValueEnvironmentIdentity)
            && ReferenceEquals(x.AlgorithmEnvironmentIdentity, y.AlgorithmEnvironmentIdentity)
            && ReferenceEquals(x.CountedParamEnvironmentIdentity, y.CountedParamEnvironmentIdentity);

    public int GetHashCode(ZeroArgPropertyCacheKey obj)
    {
        var hash = new HashCode();
        hash.Add(obj.AccessShape);
        hash.Add(RuntimeHelpers.GetHashCode(obj.OwnerIdentity));
        hash.Add(RuntimeHelpers.GetHashCode(obj.BindingIdentity));
        hash.Add(RuntimeHelpers.GetHashCode(obj.ValueEnvironmentIdentity));
        hash.Add(RuntimeHelpers.GetHashCode(obj.AlgorithmEnvironmentIdentity));
        hash.Add(RuntimeHelpers.GetHashCode(obj.CountedParamEnvironmentIdentity));
        return hash.ToHashCode();
    }
}

internal sealed class UncachedZeroArgPropertyResultCache : IZeroArgPropertyResultCache
{
    private readonly HashSet<ZeroArgPropertyCacheKey> _seenKeys = new(ZeroArgPropertyCacheKeyComparer.Instance);
    private readonly ZeroArgPropertyResultCacheStatsCollector _stats = new();
    private int _repeatedMissRequests;

    public static UncachedZeroArgPropertyResultCache Instance { get; } = new();

    internal static UncachedZeroArgPropertyResultCache CreateForRun()
        => new();

    private UncachedZeroArgPropertyResultCache()
    {
    }

    public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate)
    {
        var key = ZeroArgPropertyCacheKey.FromExecution(execution);
        _stats.RecordRequest(execution.AccessKind);
        _stats.RecordMiss(execution.AccessKind);

        if (!_seenKeys.Add(key))
            _repeatedMissRequests++;

        return evaluate();
    }

    public ZeroArgPropertyResultCacheSnapshot GetSnapshot()
        => _stats.CreateSnapshot(
            distinctKeysCreated: _seenKeys.Count,
            repeatedMissRequests: _repeatedMissRequests,
            maxCacheSize: 0);
}

internal sealed class RunScopedZeroArgPropertyResultCache : IZeroArgPropertyResultCache
{
    private readonly Dictionary<ZeroArgPropertyCacheKey, ZeroArgPropertyResult> _results =
        new(ZeroArgPropertyCacheKeyComparer.Instance);
    private readonly HashSet<ZeroArgPropertyCacheKey> _seenKeys = new(ZeroArgPropertyCacheKeyComparer.Instance);
    private readonly HashSet<ZeroArgPropertyCacheKey> _missedKeysWithoutStore = new(ZeroArgPropertyCacheKeyComparer.Instance);
    private readonly ZeroArgPropertyResultCacheStatsCollector _stats = new();
    private int _repeatedMissRequests;
    private int _maxCacheSize;

    public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate)
    {
        var key = ZeroArgPropertyCacheKey.FromExecution(execution);
        _stats.RecordRequest(execution.AccessKind);
        _seenKeys.Add(key);

        if (_results.TryGetValue(key, out var cached))
        {
            _stats.RecordHit(execution.AccessKind);
            return EvalResult<ZeroArgPropertyResult>.Ok(cached);
        }

        _stats.RecordMiss(execution.AccessKind);
        if (!_missedKeysWithoutStore.Add(key))
            _repeatedMissRequests++;

        var result = evaluate();
        if (result.IsError)
            return result.Error;

        _results[key] = result.Value;
        _stats.RecordStore(execution.AccessKind);
        _missedKeysWithoutStore.Remove(key);
        if (_results.Count > _maxCacheSize)
            _maxCacheSize = _results.Count;
        return result;
    }

    public ZeroArgPropertyResultCacheSnapshot GetSnapshot()
        => _stats.CreateSnapshot(
            distinctKeysCreated: _seenKeys.Count,
            repeatedMissRequests: _repeatedMissRequests,
            maxCacheSize: _maxCacheSize);
}