using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// PERF-STATE-1: an evaluation context carries its run's invariant services (caches, optimizer selection,
/// diagnostics, observations) through ONE <see cref="Evaluator.RunServices"/> reference. Every context of a
/// run — nested calls, callbacks, sync or async twin — reaches the SAME services object, which references the
/// very cache and observations the run's entry was given; activation state stays per context, and two runs
/// never share services or budget.
/// </summary>
public sealed class EvalCtxRunServicesTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task EveryContextOfARun_SharesItsOneServices_AndRunsNeverShare(bool asynchronous)
    {
        var first = await Observe(asynchronous);
        var second = await Observe(asynchronous);

        foreach (var run in new[] { first, second })
        {
            // F(1): one grab; G(3): G's own grab and F's; [1, 2].map(F): two.
            Assert.Equal(5, run.Contexts.Count);
            Assert.All(run.Contexts, ctx =>
            {
                Assert.Same(run.Contexts[0].Services, ctx.Services);
                Assert.Same(run.Contexts[0].Budget, ctx.Budget);
            });
            var services = run.Contexts[0].Services;
            Assert.Same(run.Cache, services.ZeroArgPropertyResultCache);
            Assert.Same(run.Cache, run.Contexts[0].ZeroArgPropertyResultCache);
            Assert.Same(run.Observations, services.Observations);
            Assert.Same(run.Observations, run.Contexts[0].Observations);
            Assert.IsType<RunScopedDeconstructionBindingCache>(services.DeconstructionBindingCache);
            // The entry's own optimizer selection: the synchronous observed entry enables both optimizers,
            // the async twin entry (PrepareAsyncTwinRun) disables both.
            Assert.Equal(!asynchronous, services.EnableLoopOptimization);
            Assert.Equal(!asynchronous, services.EnableSequencePipelineOptimization);
            Assert.Equal(!asynchronous, run.Contexts[0].EnableLoopOptimization);
            // Activation state is the context's own: the grabs ran in different callers.
            Assert.True(run.Contexts.Select(ctx => ctx.CallStack).Distinct(ReferenceEqualityComparer.Instance).Count() > 1);
        }

        Assert.NotSame(first.Contexts[0].Services, second.Contexts[0].Services);
        Assert.NotSame(first.Contexts[0].Services.DeconstructionBindingCache, second.Contexts[0].Services.DeconstructionBindingCache);
        Assert.NotSame(first.Contexts[0].Budget, second.Contexts[0].Budget);
    }

    [Fact]
    public void AContextBuiltOutsideARun_UsesTheStatelessUnconfiguredServices_WithAFreshBudget()
    {
        var a = Evaluator.EvalCtx.Empty;
        var b = Evaluator.EvalCtx.Empty;
        Assert.Same(Evaluator.RunServices.Unconfigured, a.Services);
        Assert.Same(a.Services, b.Services);
        Assert.NotSame(a.Budget, b.Budget);
        Assert.Same(UncachedZeroArgPropertyResultCache.Instance, a.ZeroArgPropertyResultCache);
        Assert.Same(UncachedDeconstructionBindingCache.Instance, a.DeconstructionBindingCache);
        Assert.Null(a.Observations);
        Assert.Null(a.LoopDiagnostics);
        Assert.Null(a.SequenceDiagnostics);

        // Deriving a context keeps the services and budget and replaces only activation state.
        var head = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        var pushed = a.Push(head).WithNeedEnv([]);
        Assert.Same(a.Services, pushed.Services);
        Assert.Same(a.Budget, pushed.Budget);
        Assert.Same(head, pushed.Head);
        Assert.Empty(a.CallStack);
    }

    private sealed record Observed(List<Evaluator.EvalCtx> Contexts, IZeroArgPropertyResultCache Cache, EvaluationObservations Observations);

    private static async Task<Observed> Observe(bool asynchronous)
    {
        var contexts = new List<Evaluator.EvalCtx>();
        var operations = HostOperations.Create(
            HostOperation.Create("Grab", (_, _) => throw new InvalidOperationException("the META receiver seam must intercept Grab"), "x"));
        var seam = new InvocationPlanTestSeam(new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>
        {
            ["Grab"] = cells =>
            {
                lock (contexts)
                    contexts.Add(Assert.IsAssignableFrom<Evaluator.ExpressionSuspension>(cells[0]!.Suspension).Caller);
                return new Result.Atom(0);
            },
        });
        var parsed = Parser.Parse("""
            F(x) = Grab(x + 1)
            G(y) = Grab(y - 1) + F(y * 2)
            F(1) + G(3) + [1, 2].map(F).sum
            """, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));
        var root = new Expr.AlgorithmExpr(parsed.Root);
        var observations = new EvaluationObservations();
        IZeroArgPropertyResultCache cache = asynchronous ? new RunScopedAsyncZeroArgPropertyResultCache() : new RunScopedZeroArgPropertyResultCache();
        using var activation = InvocationPlanTestSeam.Activate(seam);
        var (result, _) = asynchronous
            ? await Evaluator.RunCountedObservedAsync(root, zeroArgPropertyResultCache: cache, observations: observations, hostOperations: operations)
            : Evaluator.RunCountedObserved(root, zeroArgPropertyResultCache: cache, observations: observations, hostOperations: operations);
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        Assert.Equal(new Result.Atom(0), result.Value.Value);
        return new Observed(contexts, cache, observations);
    }
}
