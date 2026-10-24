using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// The C# observation of one host-parent case, on the neutral channel shared with the generated
/// Lean artifact plus the zero-argument property cache's PUBLISHED entries per binding name.
/// </summary>
public sealed record HostParentObservation(
    string Neutral,
    SharedErrorPayload? ErrorPayload,
    IReadOnlyDictionary<string, int> PublishedByName,
    int PublishedTotal)
{
    public bool IsSuccess => Neutral.StartsWith("ok ", StringComparison.Ordinal);
    public int Published(string name) => PublishedByName.TryGetValue(name, out var count) ? count : 0;
}

/// <summary>
/// Runs a host-parent case's ONE program graph through every C# evaluator route — the plain
/// evaluator, the counted evaluator, the observed counted run with the generic strategies and with
/// the optimizers enabled, and the genuinely suspending async twin — and requires them to agree
/// exactly on value, emitted count and error category/payload. Sync routes also compare published
/// entries per name; the async route compares the published total and rejects synchronous access.
/// The harness reports one observation only after these checks. A disagreement throws, naming the case: the corpus can never
/// pin one route's behaviour as "the C# observation".
/// </summary>
public static class HostParentDifferentialHarness
{
    public static HostParentObservation Observe(HostParentCase hostCase)
    {
        var id = hostCase.Id;
        var program = hostCase.Program;

        var plain = Evaluator.Run(program);
        var counted = Evaluator.RunCounted(program);

        var genericCache = new PublicationRecorder();
        var (generic, _) = Evaluator.RunCountedObserved(program, enableOptimizations: false, zeroArgPropertyResultCache: genericCache);
        var optimizedCache = new PublicationRecorder();
        var (optimized, _) = Evaluator.RunCountedObserved(program, enableOptimizations: true, zeroArgPropertyResultCache: optimizedCache);
        var asyncCache = new SuspendingCache();
        var (asynchronous, _) = Task.Run(async () =>
            await Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: asyncCache)).GetAwaiter().GetResult();

        Require(id, genericCache.ActiveOwners == 0 && optimizedCache.ActiveOwners == 0 && asyncCache.ActiveOwners == 0,
            "a publication owner was left active");
        Require(id, asyncCache.SyncAccesses == 0, "the async route used the synchronous cache member");

        var routes = new (string Name, EvalResult<Evaluator.CountedResult> Result)[]
        {
            ("counted", counted), ("generic", generic), ("optimized", optimized), ("async", asynchronous),
        };
        foreach (var (name, result) in routes)
        {
            Require(id, result.IsError == plain.IsError, $"plain and {name} routes disagree on success");
            if (plain.IsError)
                DifferentialErrors.RequireAgreement(id, plain.Error, result.Error);
            else
            {
                Require(id, Result.ValueComparer.Equals(plain.Value, result.Value.Value),
                    $"plain value {SemanticExplorerHarness.Neutral(plain.Value)} vs {name} {SemanticExplorerHarness.Neutral(result.Value.Value)}");
                Require(id, result.Value.EmittedCount == counted.Value.EmittedCount, $"{name} emitted count differs");
            }
        }

        Require(id, genericCache.ByName.Count == optimizedCache.ByName.Count
            && genericCache.ByName.All(entry => optimizedCache.ByName.TryGetValue(entry.Key, out var count) && count == entry.Value),
            "generic and optimized routes published different cache entries");
        Require(id, asyncCache.PublishedCount == genericCache.Total, "async and sync routes published a different number of entries");

        if (plain.IsError)
        {
            var observed = DifferentialErrors.Observe(plain.Error);
            return new($"err {observed.Category}", observed.Payload, genericCache.ByName, genericCache.Total);
        }

        return new($"ok raw={SemanticExplorerHarness.Neutral(counted.Value.Value)} n={counted.Value.EmittedCount}",
            null, genericCache.ByName, genericCache.Total);
    }

    private static void Require(string caseId, bool condition, string what)
    {
        if (!condition)
            throw new InvalidOperationException($"Host-parent differential route disagreement for '{caseId}': {what}.");
    }

    /// <summary>
    /// The run-scoped publication law itself (<see cref="ZeroArgPropertyPublications"/>, exactly as
    /// <see cref="RunScopedZeroArgPropertyResultCache"/> applies it), recording the binding name of
    /// every entry a request PUBLISHED. Observation only: it changes no request's outcome.
    /// </summary>
    private sealed class PublicationRecorder : IZeroArgPropertyResultCache
    {
        private readonly ZeroArgPropertyPublications _publications = new();
        internal SortedDictionary<string, int> ByName { get; } = new(StringComparer.Ordinal);
        internal int Total { get; private set; }
        internal int ActiveOwners => _publications.ActiveOwnerCount;

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            var key = ZeroArgPropertyCacheKey.FromExecution(execution);
            if (_publications.TryGetPublished(key, out var cached))
                return EvalResult<ZeroArgPropertyResult>.Ok(cached);
            var result = _publications.EvaluateMiss(key, evaluate, out var published);
            Record(key, published);
            return result;
        }

        public EvalResult<ZeroArgPropertyResult> Invoke(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            var key = ZeroArgPropertyCacheKey.FromExecution(execution);
            var result = _publications.Invoke(key, evaluate, out var published);
            Record(key, published);
            return result;
        }

        private void Record(ZeroArgPropertyCacheKey key, bool published)
        {
            if (!published)
                return;
            var name = key.BindingIdentity is Property property
                ? property.Name
                : throw new InvalidOperationException("A published zero-argument entry must be keyed by its Property binding.");
            ByName[name] = ByName.GetValueOrDefault(name) + 1;
            Total++;
        }
    }

    /// <summary>The async reference cache, genuinely suspending before every access so the run takes the async twins.</summary>
    private sealed class SuspendingCache : IAsyncZeroArgPropertyResultCache
    {
        private readonly RunScopedAsyncZeroArgPropertyResultCache _inner = new();
        internal int SyncAccesses { get; private set; }
        internal int PublishedCount => _inner.PublishedCount;
        internal int ActiveOwners => _inner.ActiveOwnerCount;

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            SyncAccesses++;
            return _inner.GetOrEvaluate(execution, evaluate);
        }

        public EvalResult<ZeroArgPropertyResult> Invoke(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            SyncAccesses++;
            return _inner.Invoke(execution, evaluate);
        }

        public async ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(ZeroArgPropertyExecution execution, Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
        {
            await Task.Yield();
            return await _inner.GetOrEvaluateAsync(execution, evaluateAsync);
        }

        public async ValueTask<EvalResult<ZeroArgPropertyResult>> InvokeAsync(ZeroArgPropertyExecution execution, Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
        {
            await Task.Yield();
            return await _inner.InvokeAsync(execution, evaluateAsync);
        }
    }
}
