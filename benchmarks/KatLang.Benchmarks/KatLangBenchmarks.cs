using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Order;
using KatLang.Evaluation.Caching;

namespace KatLang.Benchmarks;

public enum BenchmarkCacheMode
{
	Uncached,
	Stage1,
}

internal static class KatLangBenchmarkRunner
{
	internal readonly record struct BenchmarkRunWithCacheStats(
		IReadOnlyList<decimal> Atoms,
		ZeroArgPropertyResultCacheSnapshot CacheStats);

	internal static IReadOnlyList<decimal> RunWithFrontEnd(BenchmarkScenario scenario, BenchmarkCacheMode cacheMode)
		=> EvaluateWithFrontEnd(scenario, CreateCache(cacheMode)).ToAtoms();

	internal static BenchmarkRunWithCacheStats RunWithFrontEndWithStats(BenchmarkScenario scenario)
	{
		var cache = new RunScopedZeroArgPropertyResultCache();
		return new BenchmarkRunWithCacheStats(
			EvaluateWithFrontEnd(scenario, cache).ToAtoms(),
			cache.GetSnapshot());
	}

	internal static IReadOnlyList<decimal> RunPrepared(BenchmarkScenario scenario, BenchmarkCacheMode cacheMode)
	{
		return EvaluatePrepared(scenario, CreateCache(cacheMode)).ToAtoms();
	}

	internal static BenchmarkRunWithCacheStats RunPreparedWithStats(BenchmarkScenario scenario)
	{
		var cache = new RunScopedZeroArgPropertyResultCache();
		return new BenchmarkRunWithCacheStats(
			EvaluatePrepared(scenario, cache).ToAtoms(),
			cache.GetSnapshot());
	}

	private static IZeroArgPropertyResultCache CreateCache(BenchmarkCacheMode cacheMode)
		=> cacheMode switch
		{
			BenchmarkCacheMode.Uncached => UncachedZeroArgPropertyResultCache.CreateForRun(),
			BenchmarkCacheMode.Stage1 => new RunScopedZeroArgPropertyResultCache(),
			_ => throw new InvalidOperationException($"Unknown benchmark cache mode '{cacheMode}'."),
		};

	private static Result EvaluateWithFrontEnd(BenchmarkScenario scenario, IZeroArgPropertyResultCache cache)
	{
		var frontEndResult = FrontEndPipeline.Process(scenario.Source);
		var errors = frontEndResult.Diagnostics
			.Where(diagnostic => diagnostic.Severity == DiagnosticSeverity.Error)
			.Select(diagnostic => diagnostic.Message)
			.ToArray();

		if (errors.Length > 0)
		{
			throw new InvalidOperationException(
				$"Benchmark scenario '{scenario.Id}' failed in front-end processing:{Environment.NewLine}{string.Join(Environment.NewLine, errors)}");
		}

		var result = Evaluator.Run(new Expr.Block(frontEndResult.ElaboratedRoot), cache);
		if (result.IsError)
		{
			throw new InvalidOperationException(
				$"Front-end benchmark scenario '{scenario.Id}' failed during evaluation: {result.Error}");
		}

		return result.Value;
	}

	private static Result EvaluatePrepared(BenchmarkScenario scenario, IZeroArgPropertyResultCache cache)
	{
		var result = Evaluator.Run(new Expr.Block(scenario.PreparedRoot), cache);
		if (result.IsError)
		{
			throw new InvalidOperationException(
				$"Prepared benchmark scenario '{scenario.Id}' failed during timed evaluation: {result.Error}");
		}

		return result.Value;
	}
}

[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 3, iterationCount: 8)]
[Orderer(SummaryOrderPolicy.FastestToSlowest)]
[RankColumn]
public class ParseAndEvaluateBenchmarks
{
	private static readonly BenchmarkScenario RepeatedZeroArgPropertyReuseScenario = BenchmarkScenarioCatalog.RepeatedZeroArgPropertyReuse;
	private static readonly BenchmarkScenario NestedPropertyChainsScenario = BenchmarkScenarioCatalog.NestedPropertyChains;
	private static readonly BenchmarkScenario SequenceHeavyBuiltinsScenario = BenchmarkScenarioCatalog.SequenceHeavyBuiltins;
	private static readonly BenchmarkScenario PropertyRichSharedSubcomputationsScenario = BenchmarkScenarioCatalog.PropertyRichSharedSubcomputations;
	private static readonly BenchmarkScenario RealisticWhileCalculationScenario = BenchmarkScenarioCatalog.RealisticWhileCalculation;

	[Params(BenchmarkCacheMode.Uncached, BenchmarkCacheMode.Stage1)]
	public BenchmarkCacheMode CacheMode { get; set; }

	[Benchmark(Baseline = true)]
	public IReadOnlyList<decimal> RepeatedZeroArgPropertyReuse()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(RepeatedZeroArgPropertyReuseScenario, CacheMode);

	[Benchmark]
	public IReadOnlyList<decimal> NestedPropertyChains()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(NestedPropertyChainsScenario, CacheMode);

	[Benchmark]
	public IReadOnlyList<decimal> SequenceHeavyBuiltins()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(SequenceHeavyBuiltinsScenario, CacheMode);

	[Benchmark]
	public IReadOnlyList<decimal> PropertyRichSharedSubcomputations()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(PropertyRichSharedSubcomputationsScenario, CacheMode);

	[Benchmark]
	public IReadOnlyList<decimal> RealisticWhileCalculation()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(RealisticWhileCalculationScenario, CacheMode);
}

[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 3, iterationCount: 8)]
[Orderer(SummaryOrderPolicy.FastestToSlowest)]
[RankColumn]
public class PreparedEvaluationBenchmarks
{
	private static readonly BenchmarkScenario RepeatedZeroArgPropertyReuseScenario = BenchmarkScenarioCatalog.RepeatedZeroArgPropertyReuse;
	private static readonly BenchmarkScenario NestedPropertyChainsScenario = BenchmarkScenarioCatalog.NestedPropertyChains;
	private static readonly BenchmarkScenario SequenceHeavyBuiltinsScenario = BenchmarkScenarioCatalog.SequenceHeavyBuiltins;
	private static readonly BenchmarkScenario PropertyRichSharedSubcomputationsScenario = BenchmarkScenarioCatalog.PropertyRichSharedSubcomputations;
	private static readonly BenchmarkScenario RealisticWhileCalculationScenario = BenchmarkScenarioCatalog.RealisticWhileCalculation;

	[Params(BenchmarkCacheMode.Uncached, BenchmarkCacheMode.Stage1)]
	public BenchmarkCacheMode CacheMode { get; set; }

	[Benchmark(Baseline = true)]
	public IReadOnlyList<decimal> RepeatedZeroArgPropertyReuse()
		=> KatLangBenchmarkRunner.RunPrepared(RepeatedZeroArgPropertyReuseScenario, CacheMode);

	[Benchmark]
	public IReadOnlyList<decimal> NestedPropertyChains()
		=> KatLangBenchmarkRunner.RunPrepared(NestedPropertyChainsScenario, CacheMode);

	[Benchmark]
	public IReadOnlyList<decimal> SequenceHeavyBuiltins()
		=> KatLangBenchmarkRunner.RunPrepared(SequenceHeavyBuiltinsScenario, CacheMode);

	[Benchmark]
	public IReadOnlyList<decimal> PropertyRichSharedSubcomputations()
		=> KatLangBenchmarkRunner.RunPrepared(PropertyRichSharedSubcomputationsScenario, CacheMode);

	[Benchmark]
	public IReadOnlyList<decimal> RealisticWhileCalculation()
		=> KatLangBenchmarkRunner.RunPrepared(RealisticWhileCalculationScenario, CacheMode);
}