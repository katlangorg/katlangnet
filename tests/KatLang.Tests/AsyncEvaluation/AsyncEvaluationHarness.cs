using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// Shared plumbing for the async-evaluation suites.
///
/// <para>The async twin family is reachable only when a run's zero-argument property
/// cache implements <see cref="IAsyncZeroArgPropertyResultCache"/>, so these helpers are
/// the test-side counterpart of the Phase 1 cancellation seam wrappers: composable cache
/// decorators that (a) force the twin path, (b) optionally force GENUINE asynchrony
/// (thread-hopping suspension) at every property access, and (c) inject cancellation or
/// gating at deterministic access ordinals.</para>
/// </summary>
internal static class AsyncEvaluationHarness
{
    public static Expr Ast(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    /// <summary>Neutral outcome encoding shared with the explorer harness corpora.</summary>
    public static string NeutralOf(EvalResult<Evaluator.CountedResult> result)
        => result.IsError
            ? $"err {SemanticExplorerHarness.ErrorCategory(result.Error)}"
            : $"ok raw={SemanticExplorerHarness.Neutral(result.Value.Value)} n={result.Value.EmittedCount}";

    public static string NeutralOf(EvalResult<Result> result)
        => result.IsError
            ? $"err {SemanticExplorerHarness.ErrorCategory(result.Error)}"
            : $"ok raw={SemanticExplorerHarness.Neutral(result.Value)}";

    public static string NeutralOfFlat(EvalResult<IReadOnlyList<Decimal128>> result)
        => result.IsError
            ? $"err {SemanticExplorerHarness.ErrorCategory(result.Error)}"
            : $"ok [{string.Join(", ", result.Value)}]";

    /// <summary>
    /// Awaits the value task with a bounded timeout so a wedged twin path fails a test
    /// instead of hanging the suite.
    /// </summary>
    public static async Task<T> Complete<T>(ValueTask<T> pending)
    {
        var task = pending.AsTask();
        var completed = await Task.WhenAny(task, Task.Delay(TimeSpan.FromSeconds(45)));
        Assert.Same(task, completed);
        return await task;
    }
}

/// <summary>
/// Pass-through async cache: routes evaluation through the async twin family while every
/// seam access COMPLETES SYNCHRONOUSLY (store semantics of the run-scoped reference
/// cache). This isolates the twin family's sequencing from genuine suspension.
/// </summary>
internal sealed class PassThroughAsyncZeroArgPropertyResultCache : IAsyncZeroArgPropertyResultCache
{
    private readonly RunScopedAsyncZeroArgPropertyResultCache _inner = new();

    public int SyncAccesses { get; private set; }

    public int AsyncAccesses { get; private set; }

    public EvaluationBudget? ObservedBudget { get; private set; }

    public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate)
    {
        SyncAccesses++;
        ObservedBudget = (EvaluationBudget)execution.RunIdentity;
        return _inner.GetOrEvaluate(execution, evaluate);
    }

    public ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
        ZeroArgPropertyExecution execution,
        Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
    {
        AsyncAccesses++;
        ObservedBudget = (EvaluationBudget)execution.RunIdentity;
        return _inner.GetOrEvaluateAsync(execution, evaluateAsync);
    }
}

/// <summary>
/// Forces GENUINE asynchrony: every async seam access first yields to the thread pool
/// (host-side scheduling inside the cache — the evaluator itself never yields), so the
/// evaluation spine truly suspends and resumes, usually on a different thread. Records
/// the thread ids observed before and after the yield so tests can assert that at least
/// one real thread hop occurred.
/// </summary>
internal sealed class SuspendingAsyncZeroArgPropertyResultCache : IAsyncZeroArgPropertyResultCache
{
    private readonly RunScopedAsyncZeroArgPropertyResultCache _inner = new();
    private readonly List<(int Before, int After)> _threadHops = [];

    public int SyncAccesses { get; private set; }

    public int AsyncAccesses { get; private set; }

    public IReadOnlyList<(int Before, int After)> ThreadHops => _threadHops;

    public bool ObservedThreadHop => _threadHops.Any(static hop => hop.Before != hop.After);

    public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate)
    {
        // Counted so exhaustiveness suites can assert the twin path never
        // consults the SYNCHRONOUS seam member (a recursive variant silently
        // delegated to sync evaluation would reach it through its children).
        SyncAccesses++;
        return _inner.GetOrEvaluate(execution, evaluate);
    }

    public async ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
        ZeroArgPropertyExecution execution,
        Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
    {
        AsyncAccesses++;
        var before = Environment.CurrentManagedThreadId;
        await Task.Yield();
        _threadHops.Add((before, Environment.CurrentManagedThreadId));
        return await _inner.GetOrEvaluateAsync(execution, evaluateAsync);
    }
}

/// <summary>
/// Suspends inside the cache-miss callback and counts both cache accesses and callback
/// evaluations. This distinguishes an ordinary cache hit from replay or duplicate
/// callback invocation after resumption.
/// </summary>
internal sealed class CountingSuspendingAsyncZeroArgPropertyResultCache : IAsyncZeroArgPropertyResultCache
{
    private readonly RunScopedAsyncZeroArgPropertyResultCache _inner = new();

    public int SyncAccesses { get; private set; }

    public int AsyncAccesses { get; private set; }

    public int AsyncEvaluations { get; private set; }

    public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate)
    {
        SyncAccesses++;
        return _inner.GetOrEvaluate(execution, evaluate);
    }

    public ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
        ZeroArgPropertyExecution execution,
        Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
    {
        AsyncAccesses++;
        return _inner.GetOrEvaluateAsync(
            execution,
            async () =>
            {
                AsyncEvaluations++;
                await Task.Yield();
                return await evaluateAsync();
            });
    }
}

/// <summary>
/// Suspends and then throws one supplied host exception without invoking the evaluator
/// callback. Used to pin exception identity, no replay, sync-seam exclusion, and depth
/// conservation on exceptional unwind.
/// </summary>
internal sealed class ThrowingAsyncZeroArgPropertyResultCache(Exception exception)
    : IAsyncZeroArgPropertyResultCache
{
    public int SyncAccesses { get; private set; }

    public int AsyncAccesses { get; private set; }

    public int AsyncEvaluations { get; private set; }

    public EvaluationBudget? ObservedBudget { get; private set; }

    public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate)
    {
        SyncAccesses++;
        throw exception;
    }

    public async ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
        ZeroArgPropertyExecution execution,
        Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
    {
        _ = evaluateAsync;
        AsyncAccesses++;
        ObservedBudget = (EvaluationBudget)execution.RunIdentity;
        await Task.Yield();
        throw exception;
    }
}

/// <summary>
/// Async counterpart of the Phase 1 <c>CancellingZeroArgPropertyResultCache</c>: requests
/// cancellation at the Nth ASYNC seam access, BEFORE delegating, so the run's own next
/// chokepoint observes it — the cache itself never throws.
/// </summary>
internal sealed class CancellingAsyncZeroArgPropertyResultCache(
    int cancelAtAccess,
    CancellationTokenSource cts) : IAsyncZeroArgPropertyResultCache
{
    private readonly RunScopedAsyncZeroArgPropertyResultCache _inner = new();

    public int AsyncAccesses { get; private set; }

    public EvaluationBudget? ObservedBudget { get; private set; }

    public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        => _inner.GetOrEvaluate(execution, evaluate);

    public ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
        ZeroArgPropertyExecution execution,
        Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
    {
        ObservedBudget = (EvaluationBudget)execution.RunIdentity;
        if (++AsyncAccesses == cancelAtAccess)
            cts.Cancel();

        return _inner.GetOrEvaluateAsync(execution, evaluateAsync);
    }
}

/// <summary>
/// Async counterpart of the Phase 1 <c>CancellingAfterZeroArgPropertyResultCache</c>:
/// requests cancellation AFTER the Nth async access has produced its result, exercising
/// the completion-boundary observation when no later charging chokepoint exists.
/// </summary>
internal sealed class CancellingAfterAsyncZeroArgPropertyResultCache(
    int cancelAfterAccess,
    CancellationTokenSource cts) : IAsyncZeroArgPropertyResultCache
{
    private readonly RunScopedAsyncZeroArgPropertyResultCache _inner = new();

    public int AsyncAccesses { get; private set; }

    public EvaluationBudget? ObservedBudget { get; private set; }

    public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        => _inner.GetOrEvaluate(execution, evaluate);

    public async ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
        ZeroArgPropertyExecution execution,
        Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
    {
        ObservedBudget = (EvaluationBudget)execution.RunIdentity;
        var result = await _inner.GetOrEvaluateAsync(execution, evaluateAsync);
        if (++AsyncAccesses == cancelAfterAccess)
            cts.Cancel();

        return result;
    }
}

/// <summary>
/// Holds the Nth async seam access on an externally completed gate, so a test can
/// deterministically observe a run SUSPENDED mid-evaluation (assert the task is not
/// completed, cancel the token, then release the gate and observe the outcome).
/// </summary>
internal sealed class HoldingAsyncZeroArgPropertyResultCache(int holdAtAccess) : IAsyncZeroArgPropertyResultCache
{
    private readonly RunScopedAsyncZeroArgPropertyResultCache _inner = new();
    private readonly TaskCompletionSource _reached = new(TaskCreationOptions.RunContinuationsAsynchronously);
    private readonly TaskCompletionSource _gate = new(TaskCreationOptions.RunContinuationsAsynchronously);

    public int AsyncAccesses { get; private set; }

    public EvaluationBudget? ObservedBudget { get; private set; }

    /// <summary>Completes when the held access has been entered (the run is suspended).</summary>
    public Task Reached => _reached.Task;

    public void Release() => _gate.TrySetResult();

    public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        => _inner.GetOrEvaluate(execution, evaluate);

    public async ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
        ZeroArgPropertyExecution execution,
        Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
    {
        ObservedBudget = (EvaluationBudget)execution.RunIdentity;
        if (++AsyncAccesses == holdAtAccess)
        {
            _reached.TrySetResult();
            await _gate.Task;
        }

        return await _inner.GetOrEvaluateAsync(execution, evaluateAsync);
    }
}
