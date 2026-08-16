using System.Runtime.CompilerServices;

namespace KatLang.Evaluation.Caching;

internal readonly record struct ZeroArgPropertyExecution(
    Algorithm Owner,
    Property Binding,
    ZeroArgPropertyAccessKind AccessKind,
    object ValueEnvironmentIdentity,
    object AlgorithmEnvironmentIdentity,
    object CountedParamEnvironmentIdentity,
    object RunIdentity);

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
    object CountedParamEnvironmentIdentity,
    object RunIdentity)
{
    public static ZeroArgPropertyCacheKey FromExecution(ZeroArgPropertyExecution execution)
        => new(
            GetAccessShape(execution.AccessKind),
            GetOwnerIdentity(execution),
            execution.Binding,
            execution.ValueEnvironmentIdentity,
            execution.AlgorithmEnvironmentIdentity,
            execution.CountedParamEnvironmentIdentity,
            execution.RunIdentity);

    private static ZeroArgPropertyCacheAccessShape GetAccessShape(ZeroArgPropertyAccessKind accessKind)
        => accessKind is ZeroArgPropertyAccessKind.Structural or ZeroArgPropertyAccessKind.CountedStructural
            ? ZeroArgPropertyCacheAccessShape.Structural
            : ZeroArgPropertyCacheAccessShape.Lexical;

    private static object GetOwnerIdentity(ZeroArgPropertyExecution execution)
        => GetAccessShape(execution.AccessKind) is ZeroArgPropertyCacheAccessShape.Structural
            ? StructuralOwnerIdentity.FromOwner(execution.Owner)
            : execution.Owner;
}

/// <summary>
/// Owner identity for STRUCTURAL zero-arg property access. The evaluator
/// rebuilds the receiver <see cref="Algorithm"/> record on every structural
/// access (<c>ChildOf</c>/<c>AsScopeCtx</c> mint fresh records and scope
/// contexts), so keying on the owner REFERENCE would defeat structural reuse
/// entirely — but erasing the owner altogether (the previous process-wide
/// sentinel) let one shared <see cref="Property"/> object placed under two
/// different owners alias to a single cache entry and return the other owner's
/// value. The value actually evaluated is the property wired to
/// <c>ScopeCtx(Owner.Parent, Owner.Opens, Owner.Properties)</c>, so this
/// identity captures that scope and its complete parent chain. Non-empty
/// opens/property-list components compare BY REFERENCE; separately allocated
/// empty components compare as resolution-equivalent because they contribute
/// nothing to lookup. Each intermediate <see cref="ScopeCtx"/> can be minted
/// afresh along a nested structural path, so comparing any scope record itself
/// would split equivalent rebuilt paths. Rebuilt owners over the same resolving
/// scope therefore keep hitting at every nesting depth, while owners with
/// resolution-distinct components never collide.
/// </summary>
internal sealed class StructuralOwnerIdentity
{
    private readonly ScopeComponent[] _scopeChain;

    private StructuralOwnerIdentity(ScopeComponent[] scopeChain)
    {
        _scopeChain = scopeChain;
    }

    public static StructuralOwnerIdentity FromOwner(Algorithm owner)
    {
        var scopeChain = new List<ScopeComponent>
        {
            new(owner.Opens, owner.Properties),
        };

        for (var scope = owner.Parent; scope is not null; scope = scope.Parent)
            scopeChain.Add(new ScopeComponent(scope.Opens, scope.Properties));

        return new StructuralOwnerIdentity([.. scopeChain]);
    }

    public override bool Equals(object? obj)
    {
        if (obj is not StructuralOwnerIdentity other
            || _scopeChain.Length != other._scopeChain.Length)
        {
            return false;
        }

        for (var i = 0; i < _scopeChain.Length; i++)
        {
            if (!ComponentEquals(_scopeChain[i].Opens, other._scopeChain[i].Opens)
                || !ComponentEquals(_scopeChain[i].Properties, other._scopeChain[i].Properties))
            {
                return false;
            }
        }

        return true;
    }

    /// <summary>
    /// A scope level participates in name resolution ONLY through its opens and properties, so
    /// two EMPTY lists resolve identically no matter which instance they are. Comparing them by
    /// reference would split otherwise-equivalent chains: the parser gives every elaborated
    /// helper — for example each target of one assignment deconstruction — its own empty
    /// collections, so a per-target wrapper level would make every target look like a different
    /// owner. Non-empty lists still compare by REFERENCE: they are the live declaration lists,
    /// and two distinct lists are two distinct scopes even when their contents look alike.
    /// </summary>
    private static bool ComponentEquals<T>(IReadOnlyList<T> x, IReadOnlyList<T> y)
        => ReferenceEquals(x, y) || (x.Count == 0 && y.Count == 0);

    private static int ComponentHash<T>(IReadOnlyList<T> component)
        => component.Count == 0 ? 0 : RuntimeHelpers.GetHashCode(component);

    public override int GetHashCode()
    {
        var hash = new HashCode();
        hash.Add(_scopeChain.Length);
        foreach (var component in _scopeChain)
        {
            hash.Add(ComponentHash(component.Opens));
            hash.Add(ComponentHash(component.Properties));
        }

        return hash.ToHashCode();
    }

    private readonly record struct ScopeComponent(
        IReadOnlyList<Expr> Opens,
        IReadOnlyList<Property> Properties);
}

internal sealed class ZeroArgPropertyCacheKeyComparer : IEqualityComparer<ZeroArgPropertyCacheKey>
{
    public static ZeroArgPropertyCacheKeyComparer Instance { get; } = new();

    private ZeroArgPropertyCacheKeyComparer()
    {
    }

    public bool Equals(ZeroArgPropertyCacheKey x, ZeroArgPropertyCacheKey y)
        => x.AccessShape == y.AccessShape
            && OwnerIdentityEquals(x.OwnerIdentity, y.OwnerIdentity)
            && ReferenceEquals(x.BindingIdentity, y.BindingIdentity)
            && ReferenceEquals(x.ValueEnvironmentIdentity, y.ValueEnvironmentIdentity)
            && ReferenceEquals(x.AlgorithmEnvironmentIdentity, y.AlgorithmEnvironmentIdentity)
            && ReferenceEquals(x.CountedParamEnvironmentIdentity, y.CountedParamEnvironmentIdentity)
            && ReferenceEquals(x.RunIdentity, y.RunIdentity);

    /// <summary>
    /// Lexical owners are live per-run objects compared by reference; a
    /// structural owner identity is a computed <see cref="StructuralOwnerIdentity"/>
    /// whose equality treats empty scope components as resolution-equivalent and
    /// compares non-empty components by reference.
    /// </summary>
    internal static bool OwnerIdentityEquals(object x, object y)
        => x is StructuralOwnerIdentity structural
            ? structural.Equals(y)
            : ReferenceEquals(x, y);

    public int GetHashCode(ZeroArgPropertyCacheKey obj)
    {
        var hash = new HashCode();
        hash.Add(obj.AccessShape);
        hash.Add(obj.OwnerIdentity is StructuralOwnerIdentity structural
            ? structural.GetHashCode()
            : RuntimeHelpers.GetHashCode(obj.OwnerIdentity));
        hash.Add(RuntimeHelpers.GetHashCode(obj.BindingIdentity));
        hash.Add(RuntimeHelpers.GetHashCode(obj.ValueEnvironmentIdentity));
        hash.Add(RuntimeHelpers.GetHashCode(obj.AlgorithmEnvironmentIdentity));
        hash.Add(RuntimeHelpers.GetHashCode(obj.CountedParamEnvironmentIdentity));
        hash.Add(RuntimeHelpers.GetHashCode(obj.RunIdentity));
        return hash.ToHashCode();
    }
}

internal sealed class UncachedZeroArgPropertyResultCache : IZeroArgPropertyResultCache
{
    private readonly HashSet<ZeroArgPropertyCacheKey>? _seenKeys;
    private readonly ZeroArgPropertyResultCacheStatsCollector? _stats;
    private int _repeatedMissRequests;

    /// <summary>
    /// Shared STATELESS pass-through instance. It records no bookkeeping at all:
    /// this singleton is process-wide, thread safety in evaluation is by
    /// per-run isolation (see <see cref="EvaluationBudget"/>), and the seen-key
    /// tracking holds strong references to the run's algorithms, bindings, and
    /// environments — a shared mutable set was both a concurrency corruption
    /// source and an unbounded process-lifetime retention of every evaluated
    /// AST. Use <see cref="CreateForRun"/> when snapshot statistics are wanted.
    /// </summary>
    public static UncachedZeroArgPropertyResultCache Instance { get; } = new(trackStatistics: false);

    internal static UncachedZeroArgPropertyResultCache CreateForRun()
        => new(trackStatistics: true);

    private UncachedZeroArgPropertyResultCache(bool trackStatistics)
    {
        if (trackStatistics)
        {
            _seenKeys = new(ZeroArgPropertyCacheKeyComparer.Instance);
            _stats = new();
        }
    }

    public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate)
    {
        if (_stats is null || _seenKeys is null)
            return evaluate();

        var key = ZeroArgPropertyCacheKey.FromExecution(execution);
        _stats.RecordRequest(execution.AccessKind);
        _stats.RecordMiss(execution.AccessKind);

        if (!_seenKeys.Add(key))
            _repeatedMissRequests++;

        return evaluate();
    }

    public ZeroArgPropertyResultCacheSnapshot GetSnapshot()
        => (_stats ?? new ZeroArgPropertyResultCacheStatsCollector()).CreateSnapshot(
            distinctKeysCreated: _seenKeys?.Count ?? 0,
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
