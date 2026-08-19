using KatLang.Evaluation;

namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// Phase 1's evaluation-cancellation contract carried onto the async surface, on both
/// execution families:
///
/// <list type="bullet">
///   <item><b>A.</b> An already-cancelled token cancels the returned task before any
///   evaluation, carrying the supplied token.</item>
///   <item><b>B.</b> Mid-run cancellation requested through the async seam is observed
///   at the next shared budget chokepoint; the task is Canceled with the supplied token
///   and the scoped depth protocol is conserved.</item>
///   <item><b>C.</b> Cancellation requested by the FINAL operation is still observed at
///   the completion boundary.</item>
///   <item><b>D.</b> Cancellation during a GENUINE suspension is observed when the
///   suspended run resumes.</item>
///   <item><b>E.</b> Cancellation never becomes an <see cref="EvalError"/> or a retained
///   binding value, and an uncancelled token changes nothing.</item>
/// </list>
/// </summary>
public class AsyncCancellationTests
{
    private const string PropertyProgram = "A = 1\nA";

    private const string TwoPropertyProgram = "A = 1\nB = A + 1\nA + B";

    // ── A. Already-cancelled token ──────────────────────────────────────────

    [Fact]
    public async Task RunAsync_AlreadyCancelledToken_CancelsTaskWithSuppliedToken()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();

        var task = Evaluator.RunAsync(AsyncEvaluationHarness.Ast(PropertyProgram), limits: null, cts.Token);
        Assert.True(task.IsCanceled);

        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => task);
        Assert.Equal(cts.Token, thrown.CancellationToken);
    }

    [Fact]
    public async Task RunFlatAsync_AlreadyCancelledToken_CancelsTaskWithSuppliedToken()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();

        var task = Evaluator.RunFlatAsync(AsyncEvaluationHarness.Ast(PropertyProgram), limits: null, cts.Token);
        Assert.True(task.IsCanceled);

        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => task);
        Assert.Equal(cts.Token, thrown.CancellationToken);
    }

    [Fact]
    public async Task EngineRunAsync_AlreadyCancelledEvaluationToken_CancelsTaskWithSuppliedToken()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();

        var task = KatLangEngine.RunAsync(PropertyProgram, new RunOptions
        {
            EvaluationCancellationToken = cts.Token,
        });
        Assert.True(task.IsCanceled);

        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => task);
        Assert.Equal(cts.Token, thrown.CancellationToken);
    }

    [Fact]
    public async Task EngineRunAsync_AlreadyCancelledSourceToken_CancelsTaskWithSuppliedToken()
    {
        using var sourceCts = new CancellationTokenSource();
        using var evaluationCts = new CancellationTokenSource();
        sourceCts.Cancel();

        var task = KatLangEngine.RunAsync(PropertyProgram, new RunOptions
        {
            SourceProcessingCancellationToken = sourceCts.Token,
            EvaluationCancellationToken = evaluationCts.Token,
        });
        Assert.True(task.IsCanceled);

        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => task);
        Assert.Equal(sourceCts.Token, thrown.CancellationToken);
        Assert.False(evaluationCts.IsCancellationRequested);
    }

    [Fact]
    public async Task RunCountedAsync_TwinPath_AlreadyCancelledToken_EvaluatesNothing()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();

        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
            await Evaluator.RunCountedAsync(
                AsyncEvaluationHarness.Ast(PropertyProgram), cache, limits: null, cancellationToken: cts.Token));

        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.Equal(0, cache.AsyncAccesses);
        Assert.Equal(0, cache.SyncAccesses);
    }

    // ── B. Mid-run cancellation through the async seam ──────────────────────

    [Fact]
    public async Task TwinPath_CancellationRequestedMidRun_IsObservedWithSuppliedToken()
    {
        using var cts = new CancellationTokenSource();
        var cache = new CancellingAsyncZeroArgPropertyResultCache(cancelAtAccess: 1, cts);

        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
            await Evaluator.RunCountedAsync(
                AsyncEvaluationHarness.Ast(TwoPropertyProgram), cache, limits: null, cancellationToken: cts.Token));

        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.True(cache.AsyncAccesses >= 1);
        AssertConservedAfterCancellation(cache.ObservedBudget!);
    }

    [Fact]
    public async Task TwinPath_CancellationDuringGenuineSuspensionWork_IsObservedWithSuppliedToken()
    {
        // Suspension plus mid-run cancellation: every property access hops threads, and
        // the second access requests cancellation, so the observation happens on a
        // resumed continuation rather than the starting thread.
        using var cts = new CancellationTokenSource();
        var cancelling = new CancellingAsyncZeroArgPropertyResultCache(cancelAtAccess: 2, cts);

        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
            await Evaluator.RunCountedAsync(
                AsyncEvaluationHarness.Ast(TwoPropertyProgram), cancelling, limits: null, cancellationToken: cts.Token));

        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.True(cancelling.AsyncAccesses >= 2);
        AssertConservedAfterCancellation(cancelling.ObservedBudget!);
    }

    // ── C. Completion-boundary cancellation ─────────────────────────────────

    [Fact]
    public async Task TwinPath_CancellationRequestedByTheFinalOperation_IsObservedBeforeCompletion()
    {
        // One-slot property output: after the final seam access there is no later
        // charging chokepoint, so only the completion-boundary observation can see the
        // request — exactly the Phase 1 completion-edge shape, on the twin path.
        using var cts = new CancellationTokenSource();
        var cache = new CancellingAfterAsyncZeroArgPropertyResultCache(cancelAfterAccess: 1, cts);

        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
            await Evaluator.RunCountedAsync(
                AsyncEvaluationHarness.Ast(PropertyProgram), cache, limits: null, cancellationToken: cts.Token));

        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.Equal(1, cache.AsyncAccesses);
        AssertConservedAfterCancellation(cache.ObservedBudget!);
    }

    // ── D. Cancellation while suspended ─────────────────────────────────────

    [Fact]
    public async Task TwinPath_CancelledWhileSuspendedAtTheSeam_ObservesOnResumption()
    {
        using var cts = new CancellationTokenSource();
        var cache = new HoldingAsyncZeroArgPropertyResultCache(holdAtAccess: 1);

        var runTask = Evaluator.RunCountedAsync(
            AsyncEvaluationHarness.Ast(TwoPropertyProgram), cache, limits: null, cancellationToken: cts.Token).AsTask();

        // The run reached the held seam access and is genuinely suspended.
        await AsyncEvaluationHarness.Complete(new ValueTask<bool>(WaitReached(cache)));
        Assert.False(runTask.IsCompleted);

        // Cancel while suspended, then let the seam complete successfully: the next
        // shared chokepoint observes the request on the resumed continuation.
        cts.Cancel();
        cache.Release();

        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => runTask);
        Assert.Equal(cts.Token, thrown.CancellationToken);
        AssertConservedAfterCancellation(cache.ObservedBudget!);
    }

    private static async Task<bool> WaitReached(HoldingAsyncZeroArgPropertyResultCache cache)
    {
        await cache.Reached;
        return true;
    }

    // ── E. Never an error value; uncancelled token inert ────────────────────

    [Fact]
    public async Task TwinPath_CancellationIsNeverRetainedAsABindingError()
    {
        // The eager value channel of `Late` fails only through cancellation. If
        // cancellation were modeled as an EvalError, it would be retained on the binding
        // and the run would continue to a successful result; the contract requires the
        // OperationCanceledException to escape instead.
        const string source = "Late = A + 1\nUse(x) = 42\nA = 1\nUse(Late)";
        using var cts = new CancellationTokenSource();
        var cache = new CancellingAsyncZeroArgPropertyResultCache(cancelAtAccess: 1, cts);

        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
            await Evaluator.RunCountedAsync(
                AsyncEvaluationHarness.Ast(source), cache, limits: null, cancellationToken: cts.Token));

        Assert.Equal(cts.Token, thrown.CancellationToken);
    }

    [Fact]
    public async Task TwinPath_UncancelledToken_ChangesNoOutcomeAndNoCounters()
    {
        using var cts = new CancellationTokenSource();

        var withoutToken = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(
                AsyncEvaluationHarness.Ast(TwoPropertyProgram),
                zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache()));
        var withToken = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(
                AsyncEvaluationHarness.Ast(TwoPropertyProgram),
                zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache(),
                cancellationToken: cts.Token));

        Assert.Equal(
            AsyncEvaluationHarness.NeutralOf(withoutToken.Result),
            AsyncEvaluationHarness.NeutralOf(withToken.Result));
        Assert.Equal(withoutToken.Budget.ConsumedSteps, withToken.Budget.ConsumedSteps);
        Assert.Equal(withoutToken.Budget.PeakDepth, withToken.Budget.PeakDepth);
        Assert.Equal(withoutToken.Budget.MaterializedItems, withToken.Budget.MaterializedItems);
        Assert.Equal(withoutToken.Budget.MaterializedStringChars, withToken.Budget.MaterializedStringChars);
    }

    /// <summary>
    /// Same conservation shape as the Phase 1 suite: every admitted depth level has been
    /// released on the cancellation unwind (the budget's own token is cancelled, so a
    /// capacity re-probe would throw — CurrentDepth is the direct observation).
    /// </summary>
    private static void AssertConservedAfterCancellation(EvaluationBudget budget)
    {
        Assert.Equal(0, budget.CurrentDepth);
        Assert.InRange(budget.PeakDepth, 0, budget.MaxDepth);
    }
}
