using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using System.Numerics;

namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// Architecture pins for the SHARED run-entry preparation (M7): every evaluator run
/// entry funnel — the four synchronous families and their four async twin phases —
/// prepares through one synchronous sequence (entry guards, fresh budget, structural
/// preflight, pre-evaluation validation, cache validation, root context), and the
/// run cache is paired with the host-operation configuration by one factory.
///
/// <list type="bullet">
///   <item><b>A.</b> Preflight and validation rejections are identical across all
///   eight funnels, sync and twin path alike.</item>
///   <item><b>B.</b> The per-family entry-guard ordering is a contract: the
///   synchronous family observes the token BEFORE its configuration guard; the twin
///   family raises its cache-pairing ownership guard BEFORE the first token
///   observation.</item>
///   <item><b>C.</b> The cache-pairing factory pairs the async-capable run-scoped
///   cache exactly with asynchronous host-operation configurations, fresh per call.</item>
///   <item><b>D.</b> The observed harness funnels hand back an untouched budget on a
///   rejected preparation, on both families.</item>
///   <item><b>E.</b> Preparation order details stay put: pre-evaluation rejections
///   precede cache argument validation, and the flat entry family shares one bounded
///   host projection.</item>
/// </list>
/// </summary>
public class RunEntryPreparationTests
{
    private static Result Atom(Decimal128 value) => new Result.Atom(value);

    private static HostOperations AsynchronousOperations() =>
        HostOperations.Create(HostOperation.CreateAsync("Data", (_, _) => ValueTask.FromResult(Atom(1))));

    private static EvalError Require<T>(EvalResult<T> result)
    {
        Assert.True(result.IsError, "expected a pre-evaluation rejection");
        return result.Error;
    }

    private static Expr ValidationRejectedProgram()
    {
        // Branch input arities 1 vs 2 — Lean's runResultM rejects before any evaluation.
        var mismatched = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches:
            [
                new CondBranch(new Pattern.LitInt(0), new Algorithm.User(null, [], [], [], [new Expr.Num(1)])),
                new CondBranch(
                    new Pattern.SequenceValue([new Pattern.Bind("x"), new Pattern.Bind("y")]),
                    new Algorithm.User(null, [], [], [], [new Expr.Param("x")])),
            ]);
        return new Expr.AlgorithmExpr(
            new Algorithm.User(null, [], [], [new Property("F", mismatched)], [new Expr.Num(1)]));
    }

    // ── A. Rejection parity across all eight funnels ────────────────────────

    private static async Task<IReadOnlyList<EvalError>> ErrorsFromAllEightFunnels(Expr program)
    {
        var syncCache = new RunScopedZeroArgPropertyResultCache();
        return
        [
            // The four synchronous funnels.
            Require(Evaluator.Run(program)),
            Require(Evaluator.RunCounted(program, syncCache)),
            Require(Evaluator.RunCountedObserved(program).Result),
            Require(Evaluator.RunCountedWithTopLevelProperty(program, "X", syncCache)),

            // The four async twin phases (an async-capable cache forces the twin path).
            Require(await Evaluator.RunAsync(program, new PassThroughAsyncZeroArgPropertyResultCache())),
            Require(await Evaluator.RunCountedAsync(program, new PassThroughAsyncZeroArgPropertyResultCache())),
            Require(await Evaluator.RunCountedWithTopLevelPropertyAsync(
                program, "X", new PassThroughAsyncZeroArgPropertyResultCache())),
            Require((await Evaluator.RunCountedObservedAsync(
                program, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache())).Result),
        ];
    }

    [Fact]
    public async Task StructuralPreflightRejection_IsIdenticalAcrossAllEightRunEntryFunnels()
    {
        var errors = await ErrorsFromAllEightFunnels(AstStructuralDepthTests.UnarySpine(10_000));

        Assert.Equal(8, errors.Count);
        foreach (var error in errors)
        {
            Assert.Equal(
                EvaluationLimits.MaxSupportedAstDepth,
                Assert.IsType<EvalError.AstDepthLimitExceeded>(error).Limit);
        }

        Assert.Single(errors.Distinct());
    }

    [Fact]
    public async Task PreEvaluationValidationRejection_IsIdenticalAcrossAllEightRunEntryFunnels()
    {
        var errors = await ErrorsFromAllEightFunnels(ValidationRejectedProgram());

        Assert.Equal(8, errors.Count);
        foreach (var error in errors)
        {
            var mismatch = Assert.IsType<EvalError.BranchArityMismatch>(error);
            Assert.Equal(1, mismatch.Expected);
            Assert.Equal(2, mismatch.Actual);
        }

        Assert.Single(errors.Distinct());
    }

    // ── B. Entry-guard ordering is a per-family contract ────────────────────

    [Fact]
    public void SynchronousEntry_ObservesCancellation_BeforeTheAsyncConfigurationGuard()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        var program = AsyncEvaluationHarness.Ast("1 + 1");

        // Both rejections apply; the synchronous family's contract is token first.
        var thrown = Assert.Throws<OperationCanceledException>(() =>
            Evaluator.Run(program, AsynchronousOperations(), limits: null, cts.Token));
        Assert.Equal(cts.Token, thrown.CancellationToken);
    }

    [Fact]
    public void SynchronousEntry_RejectsAsynchronousConfigurations_BeforeEvaluatingAnything()
    {
        // The deeper sync-dispatch ownership guard also throws InvalidOperationException,
        // but only once evaluation REACHES the asynchronous operation — by which time an
        // earlier synchronous operation has already run. The entry guard's contract is
        // rejection before anything evaluates, pinned here through the sync operation's
        // invocation counter.
        var invoked = 0;
        var operations = HostOperations.Create(
            HostOperation.Create("Tick", (_, _) => { invoked++; return Atom(1); }),
            HostOperation.CreateAsync("Data", (_, _) => ValueTask.FromResult(Atom(2))));
        var parsed = Parser.Parse("Tick + Data", new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors);
        var program = new Expr.AlgorithmExpr(parsed.Root);

        Assert.Throws<InvalidOperationException>(() =>
            Evaluator.Run(program, operations, limits: null, CancellationToken.None));
        Assert.Equal(0, invoked);
    }

    [Fact]
    public async Task AsyncTwinEntry_RaisesTheCachePairingGuard_BeforeObservingCancellation()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        var program = AsyncEvaluationHarness.Ast("1 + 1");

        // Async operations with a sync-only cache is an internal wiring bug; the twin
        // family's contract is that this ownership guard fails loud even under a
        // cancelled token.
        await Assert.ThrowsAsync<InvalidOperationException>(async () =>
            await Evaluator.RunCountedAsync(
                program,
                new RunScopedZeroArgPropertyResultCache(),
                hostOperations: AsynchronousOperations(),
                cancellationToken: cts.Token));
    }

    // ── C. The one cache-pairing factory ────────────────────────────────────

    [Fact]
    public void CacheFactory_PairsTheAsyncCapableCache_ExactlyWithAsynchronousConfigurations()
    {
        // No host operations and purely synchronous operations keep the ordinary
        // run-scoped cache (and with it the synchronous fast path).
        Assert.IsNotAssignableFrom<IAsyncZeroArgPropertyResultCache>(
            Evaluator.CreateRunScopedZeroArgPropertyResultCache(hostOperations: null));
        Assert.IsNotAssignableFrom<IAsyncZeroArgPropertyResultCache>(
            Evaluator.CreateRunScopedZeroArgPropertyResultCache(
                HostOperations.Create(HostOperation.Create("Data", (_, _) => Atom(1)))));

        // An asynchronous configuration is paired with the async-capable cache.
        Assert.IsAssignableFrom<IAsyncZeroArgPropertyResultCache>(
            Evaluator.CreateRunScopedZeroArgPropertyResultCache(AsynchronousOperations()));
    }

    [Fact]
    public void CacheFactory_ConstructsAFreshRunLocalCache_OnEveryCall()
    {
        var operations = AsynchronousOperations();
        Assert.NotSame(
            Evaluator.CreateRunScopedZeroArgPropertyResultCache(operations),
            Evaluator.CreateRunScopedZeroArgPropertyResultCache(operations));
        Assert.NotSame(
            Evaluator.CreateRunScopedZeroArgPropertyResultCache(hostOperations: null),
            Evaluator.CreateRunScopedZeroArgPropertyResultCache(hostOperations: null));
    }

    [Fact]
    public async Task EngineAdditionalErrorEvaluation_PairsTheCache_ForAsynchronousOperations()
    {
        // A failing module fetch with an evaluable remainder routes through the
        // engine's additional-error evaluation; with an asynchronous host-operation
        // configuration that path must pair an async-capable cache (a mispairing
        // fails loud as InvalidOperationException instead of projecting errors).
        const string source = "open 'https://katlang.org/missing.kat'\nData + (1 / 0)";
        var options = new RunOptions
        {
            DownloadCode = (_, _) => throw new InvalidOperationException("fetch refused by test"),
            HostOperations = AsynchronousOperations(),
        };

        var result = await KatLangEngine.RunAsync(source, options);

        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        Assert.Contains(failure.Errors, e => e.Message.Contains("failed to fetch", StringComparison.Ordinal));
    }

    // ── D. Observed funnels hand back an untouched budget on rejection ──────

    [Fact]
    public async Task ObservedFunnels_HandBackAnUntouchedBudget_OnARejectedPreparation()
    {
        foreach (var rejected in new[]
                 {
                     AstStructuralDepthTests.UnarySpine(10_000),
                     ValidationRejectedProgram(),
                 })
        {
            var (syncResult, syncBudget) = Evaluator.RunCountedObserved(rejected);
            var (twinResult, twinBudget) = await Evaluator.RunCountedObservedAsync(
                rejected, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache());

            foreach (var (result, budget) in new[] { (syncResult, syncBudget), (twinResult, twinBudget) })
            {
                _ = Require(result);
                Assert.Equal(0, budget.ConsumedSteps);
                Assert.Equal(0, budget.PeakDepth);
                Assert.Equal(0, budget.MaterializedItems);
            }
        }
    }

    /// <summary>
    /// Cancels after every synchronous seam access; with a single-property program the
    /// first access IS the final operation, so only the completion-boundary observation
    /// can see the request (the Phase 1 completion-edge shape, per funnel).
    /// </summary>
    private sealed class CancellingAfterAccessCache(CancellationTokenSource cts) : IZeroArgPropertyResultCache
    {
        private readonly RunScopedZeroArgPropertyResultCache _inner = new();

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            var result = _inner.GetOrEvaluate(execution, evaluate);
            cts.Cancel();
            return result;
        }
    }

    [Fact]
    public void CompletionBoundaryObservation_IsPresentOnEverySynchronousFunnel()
    {
        // The observed funnel's completion edge is pinned by the Phase 1 suite; these
        // pin the remaining synchronous funnels. The top-level-property funnel demands
        // a MISSING property so nothing after the output row's final access passes a
        // charging chokepoint on that funnel either.
        var program = AsyncEvaluationHarness.Ast("A = 1\nA");

        using (var cts = new CancellationTokenSource())
        {
            var thrown = Assert.Throws<OperationCanceledException>(() => Evaluator.Run(
                program,
                new CancellingAfterAccessCache(cts),
                enableLoopOptimization: true,
                loopDiagnostics: null,
                enableSequencePipelineOptimization: true,
                sequenceDiagnostics: null,
                cancellationToken: cts.Token));
            Assert.Equal(cts.Token, thrown.CancellationToken);
        }

        using (var cts = new CancellationTokenSource())
        {
            var thrown = Assert.Throws<OperationCanceledException>(() => Evaluator.RunCounted(
                program, new CancellingAfterAccessCache(cts), cancellationToken: cts.Token));
            Assert.Equal(cts.Token, thrown.CancellationToken);
        }

        using (var cts = new CancellationTokenSource())
        {
            var thrown = Assert.Throws<OperationCanceledException>(() => Evaluator.RunCountedWithTopLevelProperty(
                program, "Missing", new CancellingAfterAccessCache(cts), cancellationToken: cts.Token));
            Assert.Equal(cts.Token, thrown.CancellationToken);
        }
    }

    [Fact]
    public async Task CompletionBoundaryObservation_IsPresentOnEveryAsyncTwinFunnel()
    {
        // The counted twin's completion edge is pinned by the async cancellation suite;
        // these pin the remaining twin funnels.
        var program = AsyncEvaluationHarness.Ast("A = 1\nA");

        using (var cts = new CancellationTokenSource())
        {
            var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
                await Evaluator.RunAsync(
                    program,
                    new CancellingAfterAsyncZeroArgPropertyResultCache(cancelAfterAccess: 1, cts),
                    cancellationToken: cts.Token));
            Assert.Equal(cts.Token, thrown.CancellationToken);
        }

        using (var cts = new CancellationTokenSource())
        {
            var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
                await Evaluator.RunCountedWithTopLevelPropertyAsync(
                    program,
                    "Missing",
                    new CancellingAfterAsyncZeroArgPropertyResultCache(cancelAfterAccess: 1, cts),
                    cancellationToken: cts.Token));
            Assert.Equal(cts.Token, thrown.CancellationToken);
        }

        using (var cts = new CancellationTokenSource())
        {
            var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
                await Evaluator.RunCountedObservedAsync(
                    program,
                    zeroArgPropertyResultCache: new CancellingAfterAsyncZeroArgPropertyResultCache(cancelAfterAccess: 1, cts),
                    cancellationToken: cts.Token));
            Assert.Equal(cts.Token, thrown.CancellationToken);
        }
    }

    [Fact]
    public async Task CompletionBoundaryCancellation_PreemptsAnEvaluatorError_OnBothFamilies()
    {
        // The property access has already produced an evaluator error when the seam
        // requests cancellation. The run-level completion observation must still throw
        // OCE rather than returning the error as if cancellation had not happened.
        var program = AsyncEvaluationHarness.Ast("A = 1 / 0\nA");

        using (var cts = new CancellationTokenSource())
        {
            var thrown = Assert.Throws<OperationCanceledException>(() => Evaluator.Run(
                program,
                new CancellingAfterAccessCache(cts),
                enableLoopOptimization: true,
                loopDiagnostics: null,
                enableSequencePipelineOptimization: true,
                sequenceDiagnostics: null,
                cancellationToken: cts.Token));
            Assert.Equal(cts.Token, thrown.CancellationToken);
        }

        using (var cts = new CancellationTokenSource())
        {
            var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
                await Evaluator.RunAsync(
                    program,
                    new CancellingAfterAsyncZeroArgPropertyResultCache(cancelAfterAccess: 1, cts),
                    cancellationToken: cts.Token));
            Assert.Equal(cts.Token, thrown.CancellationToken);
        }
    }

    // ── E. Preparation order details stay put ───────────────────────────────

    [Fact]
    public void PreEvaluationRejections_PrecedeCacheArgumentValidation()
    {
        // The cache argument is validated after the structural preflight and the
        // pre-evaluation validation gate, so a rejected tree reports its rejection
        // rather than throwing ArgumentNullException — while an accepted tree still
        // fails loud on the missing cache.
        var deep = AstStructuralDepthTests.UnarySpine(10_000);
        var rejected = Evaluator.Run(deep, zeroArgPropertyResultCache: null!, enableLoopOptimization: true);
        Assert.IsType<EvalError.AstDepthLimitExceeded>(Require(rejected));

        Assert.Throws<ArgumentNullException>(() => Evaluator.Run(
            AsyncEvaluationHarness.Ast("1 + 1"), zeroArgPropertyResultCache: null!, enableLoopOptimization: true));
    }

    [Fact]
    public async Task TopLevelPropertyNameValidation_KeepsItsHistoricalFamilyOrdering()
    {
        var deep = AstStructuralDepthTests.UnarySpine(10_000);

        // The synchronous funnel validates the AST before the top-level property name.
        var sync = Evaluator.RunCountedWithTopLevelProperty(
            deep, " ", new RunScopedZeroArgPropertyResultCache());
        Assert.IsType<EvalError.AstDepthLimitExceeded>(Require(sync));

        // The async wrapper has always validated the name at method entry, before
        // routing into the twin preparation and therefore before structural preflight.
        await Assert.ThrowsAsync<ArgumentException>(async () =>
            await Evaluator.RunCountedWithTopLevelPropertyAsync(
                deep, " ", new PassThroughAsyncZeroArgPropertyResultCache()));
    }

    [Fact]
    public async Task FlatEntryFamily_SharesTheBoundedHostProjection()
    {
        // Evaluation succeeds (each list stays within the per-collection ceiling),
        // and the flat host projection then rejects the flattening identically on
        // the synchronous and asynchronous flat entry points.
        var program = AsyncEvaluationHarness.Ast("[[1, 2], [3, 4]]");
        var limits = new EvaluationLimits { MaxCollectionItems = 3 };

        Assert.False(Evaluator.Run(program, limits).IsError);

        var sync = Evaluator.RunFlat(program, limits);
        var async = await Evaluator.RunFlatAsync(program, limits, CancellationToken.None);
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(Require(sync));
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(Require(async));
        Assert.Equal(sync.Error, async.Error);

        // The projection itself is unchanged where it fits.
        var fits = new EvaluationLimits { MaxCollectionItems = 4 };
        var syncAtoms = Evaluator.RunFlat(program, fits);
        var asyncAtoms = await Evaluator.RunFlatAsync(program, fits, CancellationToken.None);
        Assert.False(syncAtoms.IsError);
        Assert.False(asyncAtoms.IsError);
        Assert.Equal(syncAtoms.Value, asyncAtoms.Value);
    }
}
