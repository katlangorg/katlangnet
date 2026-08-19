namespace KatLang.Evaluation.Caching;

/// <summary>
/// Async-capable variant of the zero-argument property result seam — one of the
/// boundaries through which the ASYNC evaluation path may complete asynchronously.
///
/// <para>This interface is the structural landing point for an asynchronous property
/// cache inside evaluation. A run whose zero-argument property cache implements it is
/// routed through the evaluator's async twin family (<c>Evaluator.RunAsync</c> internals),
/// where every property access awaits <see cref="GetOrEvaluateAsync"/>; a returned
/// <see cref="ValueTask{TResult}"/> that has not completed suspends the whole evaluation
/// spine and resumes it when the cache work finishes — no thread is blocked, and no
/// evaluator thread offloading is involved. Since Phase 3, a public asynchronous host
/// operation is a second routing reason and has its own await site; public entry points
/// pair such configurations with an async-capable cache because the twin family awaits
/// this seam at every property access. A run with only a synchronous cache and no
/// asynchronous host operation executes the ordinary synchronous evaluator inline.</para>
///
/// <para><b>Contract</b> — identical to <see cref="IZeroArgPropertyResultCache.GetOrEvaluate"/>
/// except for asynchrony:</para>
/// <list type="bullet">
///   <item>On a hit, return the stored result without invoking <paramref name="evaluateAsync"/>.</item>
///   <item>On a miss, invoke <paramref name="evaluateAsync"/> at most once and store only
///   successful results (errors are never stored — a deterministic failure recurs
///   identically, and a transient resource-limit failure must be free to recur under the
///   live budget).</item>
///   <item>Never swallow exceptions from the callback: in particular a thrown
///   <see cref="OperationCanceledException"/> is host cancellation and must propagate
///   unchanged (it is never a cacheable outcome).</item>
///   <item>The implementation may complete asynchronously (for example an IO-backed host
///   cache), but must never block the calling thread to simulate synchronous completion.</item>
/// </list>
///
/// <para>Thread-safety note: within one run the evaluator awaits each property access
/// before issuing the next, so accesses are sequential — but after a genuine suspension
/// the CONTINUATION may run on a different thread than the one that started the run.
/// Implementations must therefore not assume thread affinity, exactly like every other
/// run-scoped evaluator structure (see the concurrency notes on
/// <see cref="EvaluationBudget"/>).</para>
/// </summary>
internal interface IAsyncZeroArgPropertyResultCache : IZeroArgPropertyResultCache
{
    /// <summary>
    /// Async twin of <see cref="IZeroArgPropertyResultCache.GetOrEvaluate"/>. Used only by
    /// the evaluator's async twin family; the synchronous evaluator keeps using the
    /// synchronous member.
    /// </summary>
    ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
        ZeroArgPropertyExecution execution,
        Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync);
}

/// <summary>
/// Run-scoped async-capable zero-argument property cache: the reference implementation
/// of <see cref="IAsyncZeroArgPropertyResultCache"/>, with exactly the store semantics of
/// <see cref="RunScopedZeroArgPropertyResultCache"/> (same keys, same comparer, errors
/// never stored) minus that class's snapshot statistics. Supplying one to an async
/// evaluator entry point routes the run through the async twin family; a run uses one of
/// the two members throughout (sync entry points use the synchronous member, the async
/// twin path awaits the asynchronous one), and within the async family each access is
/// awaited before evaluation continues, so the dictionary is never touched concurrently.
/// </summary>
internal sealed class RunScopedAsyncZeroArgPropertyResultCache : IAsyncZeroArgPropertyResultCache
{
    private readonly Dictionary<ZeroArgPropertyCacheKey, ZeroArgPropertyResult> _results =
        new(ZeroArgPropertyCacheKeyComparer.Instance);

    public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate)
    {
        var key = ZeroArgPropertyCacheKey.FromExecution(execution);
        if (_results.TryGetValue(key, out var cached))
            return EvalResult<ZeroArgPropertyResult>.Ok(cached);

        var result = evaluate();
        if (result.IsError)
            return result.Error;

        _results[key] = result.Value;
        return result;
    }

    public async ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
        ZeroArgPropertyExecution execution,
        Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
    {
        var key = ZeroArgPropertyCacheKey.FromExecution(execution);
        if (_results.TryGetValue(key, out var cached))
            return EvalResult<ZeroArgPropertyResult>.Ok(cached);

        var result = await evaluateAsync().ConfigureAwait(false);
        if (result.IsError)
            return result.Error;

        _results[key] = result.Value;
        return result;
    }
}
