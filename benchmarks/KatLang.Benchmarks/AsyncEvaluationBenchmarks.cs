using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Order;
using KatLang.Evaluation.Caching;

namespace KatLang.Benchmarks;

/// <summary>
/// Async-surface evaluation benchmarks over prepared roots (evaluation only, no front
/// end). Four execution modes per scenario:
///
/// <list type="bullet">
///   <item><b>SyncOptimized</b> — the ordinary synchronous evaluator with the default
///   optimizer eligibility (production baseline).</item>
///   <item><b>SyncGeneric</b> — the synchronous evaluator with the generic loop and
///   sequence strategies (the strategy mode the async twin family mirrors; the fair
///   baseline for twin overhead).</item>
///   <item><b>AsyncFastPath</b> — the public <c>Evaluator.RunAsync</c> with the default
///   (synchronous) cache: the async surface delegating to the synchronous pipeline
///   inline. Expected cost over SyncOptimized: one Task allocation per run.</item>
///   <item><b>AsyncTwinPath</b> — the async twin family (async-capable run-scoped
///   cache, every seam access completing synchronously): the state-machine overhead an
///   async-capable run pays while no operation actually suspends. Compare against
///   SyncGeneric.</item>
/// </list>
///
/// All async modes complete synchronously, so <c>GetAwaiter().GetResult()</c> reads an
/// already-completed task and never blocks.
/// </summary>
[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 3, iterationCount: 8)]
[Orderer(SummaryOrderPolicy.FastestToSlowest)]
[RankColumn]
public class AsyncEvaluationBenchmarks
{
    public enum AsyncBenchmarkMode
    {
        SyncOptimized,
        SyncGeneric,
        AsyncFastPath,
        AsyncTwinPath,
    }

    private static readonly BenchmarkScenario ScalarHelperSumCallsScenario = BenchmarkScenarioCatalog.ScalarHelperSumCalls;
    private static readonly BenchmarkScenario NestedPropertyChainsScenario = BenchmarkScenarioCatalog.NestedPropertyChains;
    private static readonly BenchmarkScenario SequenceHeavyBuiltinsScenario = BenchmarkScenarioCatalog.SequenceHeavyBuiltins;
    private static readonly BenchmarkScenario PropertyRichSharedSubcomputationsScenario = BenchmarkScenarioCatalog.PropertyRichSharedSubcomputations;
    private static readonly BenchmarkScenario RepeatManyIterationsScenario = BenchmarkScenarioCatalog.RepeatManyIterations;
    private static readonly BenchmarkScenario SequenceFilterCountEvenRangeScenario = BenchmarkScenarioCatalog.SequenceFilterCountEvenRange;

    [Params(
        AsyncBenchmarkMode.SyncOptimized,
        AsyncBenchmarkMode.SyncGeneric,
        AsyncBenchmarkMode.AsyncFastPath,
        AsyncBenchmarkMode.AsyncTwinPath)]
    public AsyncBenchmarkMode Mode { get; set; }

    [Benchmark(Baseline = true)]
    public IReadOnlyList<decimal> ScalarHelperSumCalls()
        => Execute(ScalarHelperSumCallsScenario);

    [Benchmark]
    public IReadOnlyList<decimal> NestedPropertyChains()
        => Execute(NestedPropertyChainsScenario);

    [Benchmark]
    public IReadOnlyList<decimal> SequenceHeavyBuiltins()
        => Execute(SequenceHeavyBuiltinsScenario);

    [Benchmark]
    public IReadOnlyList<decimal> PropertyRichSharedSubcomputations()
        => Execute(PropertyRichSharedSubcomputationsScenario);

    [Benchmark]
    public IReadOnlyList<decimal> RepeatManyIterations()
        => Execute(RepeatManyIterationsScenario);

    [Benchmark]
    public IReadOnlyList<decimal> SequenceFilterCountEvenRange()
        => Execute(SequenceFilterCountEvenRangeScenario);

    private IReadOnlyList<decimal> Execute(BenchmarkScenario scenario)
    {
        var root = new Expr.AlgorithmExpr(scenario.PreparedRoot);
        switch (Mode)
        {
            case AsyncBenchmarkMode.SyncOptimized:
                return KatLangBenchmarkRunner.RunPrepared(scenario, BenchmarkCacheMode.Stage1);

            case AsyncBenchmarkMode.SyncGeneric:
                return KatLangBenchmarkRunner.RunPrepared(
                    scenario, BenchmarkCacheMode.Stage1, BenchmarkLoopMode.Generic, BenchmarkSequencePipelineMode.Generic);

            case AsyncBenchmarkMode.AsyncFastPath:
                {
                    var result = Evaluator.RunAsync(root).GetAwaiter().GetResult();
                    if (result.IsError)
                        throw new InvalidOperationException($"Async fast-path benchmark '{scenario.Id}' failed: {result.Error}");
                    return result.Value.ToHostAtoms();
                }

            case AsyncBenchmarkMode.AsyncTwinPath:
                {
                    var result = Evaluator.RunCountedAsync(root, new RunScopedAsyncZeroArgPropertyResultCache())
                        .GetAwaiter().GetResult();
                    if (result.IsError)
                        throw new InvalidOperationException($"Async twin-path benchmark '{scenario.Id}' failed: {result.Error}");
                    return result.Value.Value.ToHostAtoms();
                }

            default:
                throw new InvalidOperationException($"Unknown async benchmark mode '{Mode}'.");
        }
    }
}
