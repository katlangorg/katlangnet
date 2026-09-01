using BenchmarkDotNet.Attributes;
using System.Numerics;
using BenchmarkDotNet.Order;
using KatLang.Evaluation.Caching;

namespace KatLang.Benchmarks;

public enum BenchmarkCacheMode
{
	Uncached,
	Stage1,
}

public enum BenchmarkLoopMode
{
	Generic,
	Optimized,
}

public enum BenchmarkSequencePipelineMode
{
	Generic,
	Optimized,
}

internal static class KatLangBenchmarkRunner
{
	internal readonly record struct BenchmarkRunWithCacheStats(
		IReadOnlyList<Decimal128> Atoms,
		ZeroArgPropertyResultCacheSnapshot CacheStats);

	internal static IReadOnlyList<Decimal128> RunWithFrontEnd(BenchmarkScenario scenario, BenchmarkCacheMode cacheMode)
		=> RunWithFrontEnd(scenario, cacheMode, BenchmarkLoopMode.Optimized);

	internal static IReadOnlyList<Decimal128> RunWithFrontEnd(
		BenchmarkScenario scenario,
		BenchmarkCacheMode cacheMode,
		BenchmarkLoopMode loopMode)
		=> RunWithFrontEnd(scenario, cacheMode, loopMode, BenchmarkSequencePipelineMode.Optimized);

	internal static IReadOnlyList<Decimal128> RunWithFrontEnd(
		BenchmarkScenario scenario,
		BenchmarkCacheMode cacheMode,
		BenchmarkLoopMode loopMode,
		BenchmarkSequencePipelineMode sequencePipelineMode)
		=> EvaluateWithFrontEnd(scenario, CreateCache(cacheMode), loopMode, sequencePipelineMode).ToHostAtoms();

	internal static BenchmarkRunWithCacheStats RunWithFrontEndWithStats(BenchmarkScenario scenario)
	{
		var cache = new RunScopedZeroArgPropertyResultCache();
		return new BenchmarkRunWithCacheStats(
			EvaluateWithFrontEnd(scenario, cache, BenchmarkLoopMode.Optimized, BenchmarkSequencePipelineMode.Optimized).ToHostAtoms(),
			cache.GetSnapshot());
	}

	internal static IReadOnlyList<Decimal128> RunPrepared(BenchmarkScenario scenario, BenchmarkCacheMode cacheMode)
		=> RunPrepared(scenario, cacheMode, BenchmarkLoopMode.Optimized);

	internal static IReadOnlyList<Decimal128> RunPrepared(
		BenchmarkScenario scenario,
		BenchmarkCacheMode cacheMode,
		BenchmarkLoopMode loopMode)
		=> RunPrepared(scenario, cacheMode, loopMode, BenchmarkSequencePipelineMode.Optimized);

	internal static IReadOnlyList<Decimal128> RunPrepared(
		BenchmarkScenario scenario,
		BenchmarkCacheMode cacheMode,
		BenchmarkLoopMode loopMode,
		BenchmarkSequencePipelineMode sequencePipelineMode)
	{
		return EvaluatePrepared(scenario, CreateCache(cacheMode), loopMode, sequencePipelineMode).ToHostAtoms();
	}

	internal static BenchmarkRunWithCacheStats RunPreparedWithStats(BenchmarkScenario scenario)
	{
		var cache = new RunScopedZeroArgPropertyResultCache();
		return new BenchmarkRunWithCacheStats(
			EvaluatePrepared(scenario, cache, BenchmarkLoopMode.Optimized, BenchmarkSequencePipelineMode.Optimized).ToHostAtoms(),
			cache.GetSnapshot());
	}

	private static IZeroArgPropertyResultCache CreateCache(BenchmarkCacheMode cacheMode)
		=> cacheMode switch
		{
			BenchmarkCacheMode.Uncached => UncachedZeroArgPropertyResultCache.CreateForRun(),
			BenchmarkCacheMode.Stage1 => new RunScopedZeroArgPropertyResultCache(),
			_ => throw new InvalidOperationException($"Unknown benchmark cache mode '{cacheMode}'."),
		};

	private static bool EnableLoopOptimization(BenchmarkLoopMode loopMode)
		=> loopMode switch
		{
			BenchmarkLoopMode.Generic => false,
			BenchmarkLoopMode.Optimized => true,
			_ => throw new InvalidOperationException($"Unknown benchmark loop mode '{loopMode}'."),
		};

	private static bool EnableSequencePipelineOptimization(BenchmarkSequencePipelineMode sequencePipelineMode)
		=> sequencePipelineMode switch
		{
			BenchmarkSequencePipelineMode.Generic => false,
			BenchmarkSequencePipelineMode.Optimized => true,
			_ => throw new InvalidOperationException($"Unknown benchmark sequence pipeline mode '{sequencePipelineMode}'."),
		};

	private static Result EvaluateWithFrontEnd(
		BenchmarkScenario scenario,
		IZeroArgPropertyResultCache cache,
		BenchmarkLoopMode loopMode,
		BenchmarkSequencePipelineMode sequencePipelineMode)
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

		var result = Evaluator.Run(
			new Expr.AlgorithmExpr(frontEndResult.ElaboratedRoot),
			cache,
			EnableLoopOptimization(loopMode),
			loopDiagnostics: null,
			enableSequencePipelineOptimization: EnableSequencePipelineOptimization(sequencePipelineMode),
			sequenceDiagnostics: null);
		if (result.IsError)
		{
			throw new InvalidOperationException(
				$"Front-end benchmark scenario '{scenario.Id}' failed during evaluation: {result.Error}");
		}

		return result.Value;
	}

	private static Result EvaluatePrepared(
		BenchmarkScenario scenario,
		IZeroArgPropertyResultCache cache,
		BenchmarkLoopMode loopMode,
		BenchmarkSequencePipelineMode sequencePipelineMode)
	{
		var result = Evaluator.Run(
			new Expr.AlgorithmExpr(scenario.PreparedRoot),
			cache,
			EnableLoopOptimization(loopMode),
			loopDiagnostics: null,
			enableSequencePipelineOptimization: EnableSequencePipelineOptimization(sequencePipelineMode),
			sequenceDiagnostics: null);
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
	private static readonly BenchmarkScenario ScalarHelperSumCallsScenario = BenchmarkScenarioCatalog.ScalarHelperSumCalls;
	private static readonly BenchmarkScenario NestedPropertyChainsScenario = BenchmarkScenarioCatalog.NestedPropertyChains;
	private static readonly BenchmarkScenario SequenceHeavyBuiltinsScenario = BenchmarkScenarioCatalog.SequenceHeavyBuiltins;
	private static readonly BenchmarkScenario PropertyRichSharedSubcomputationsScenario = BenchmarkScenarioCatalog.PropertyRichSharedSubcomputations;
	private static readonly BenchmarkScenario RealisticWhileCalculationScenario = BenchmarkScenarioCatalog.RealisticWhileCalculation;
	private static readonly BenchmarkScenario GcdWhileLoopScenario = BenchmarkScenarioCatalog.GcdWhileLoop;
	private static readonly BenchmarkScenario RepeatManyIterationsScenario = BenchmarkScenarioCatalog.RepeatManyIterations;
	private static readonly BenchmarkScenario NestedCapturedParentLoopScenario = BenchmarkScenarioCatalog.NestedCapturedParentLoop;

	[Params(BenchmarkCacheMode.Uncached, BenchmarkCacheMode.Stage1)]
	public BenchmarkCacheMode CacheMode { get; set; }

	[Params(BenchmarkLoopMode.Generic, BenchmarkLoopMode.Optimized)]
	public BenchmarkLoopMode LoopMode { get; set; }

	[Benchmark(Baseline = true)]
	public IReadOnlyList<Decimal128> RepeatedZeroArgPropertyReuse()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(RepeatedZeroArgPropertyReuseScenario, CacheMode, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> ScalarHelperSumCalls()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(ScalarHelperSumCallsScenario, CacheMode, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> NestedPropertyChains()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(NestedPropertyChainsScenario, CacheMode, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> SequenceHeavyBuiltins()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(SequenceHeavyBuiltinsScenario, CacheMode, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> PropertyRichSharedSubcomputations()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(PropertyRichSharedSubcomputationsScenario, CacheMode, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> RealisticWhileCalculation()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(RealisticWhileCalculationScenario, CacheMode, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> GcdWhileLoop()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(GcdWhileLoopScenario, CacheMode, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> RepeatManyIterations()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(RepeatManyIterationsScenario, CacheMode, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> NestedCapturedParentLoop()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(NestedCapturedParentLoopScenario, CacheMode, LoopMode);
}

[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 3, iterationCount: 8)]
[Orderer(SummaryOrderPolicy.FastestToSlowest)]
[RankColumn]
public class PreparedEvaluationBenchmarks
{
	private static readonly BenchmarkScenario RepeatedZeroArgPropertyReuseScenario = BenchmarkScenarioCatalog.RepeatedZeroArgPropertyReuse;
	private static readonly BenchmarkScenario ScalarHelperSumCallsScenario = BenchmarkScenarioCatalog.ScalarHelperSumCalls;
	private static readonly BenchmarkScenario NestedPropertyChainsScenario = BenchmarkScenarioCatalog.NestedPropertyChains;
	private static readonly BenchmarkScenario SequenceHeavyBuiltinsScenario = BenchmarkScenarioCatalog.SequenceHeavyBuiltins;
	private static readonly BenchmarkScenario PropertyRichSharedSubcomputationsScenario = BenchmarkScenarioCatalog.PropertyRichSharedSubcomputations;
	private static readonly BenchmarkScenario RealisticWhileCalculationScenario = BenchmarkScenarioCatalog.RealisticWhileCalculation;
	private static readonly BenchmarkScenario GcdWhileLoopScenario = BenchmarkScenarioCatalog.GcdWhileLoop;
	private static readonly BenchmarkScenario RepeatManyIterationsScenario = BenchmarkScenarioCatalog.RepeatManyIterations;
	private static readonly BenchmarkScenario NestedCapturedParentLoopScenario = BenchmarkScenarioCatalog.NestedCapturedParentLoop;

	[Params(BenchmarkCacheMode.Uncached, BenchmarkCacheMode.Stage1)]
	public BenchmarkCacheMode CacheMode { get; set; }

	[Params(BenchmarkLoopMode.Generic, BenchmarkLoopMode.Optimized)]
	public BenchmarkLoopMode LoopMode { get; set; }

	[Benchmark(Baseline = true)]
	public IReadOnlyList<Decimal128> RepeatedZeroArgPropertyReuse()
		=> KatLangBenchmarkRunner.RunPrepared(RepeatedZeroArgPropertyReuseScenario, CacheMode, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> ScalarHelperSumCalls()
		=> KatLangBenchmarkRunner.RunPrepared(ScalarHelperSumCallsScenario, CacheMode, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> NestedPropertyChains()
		=> KatLangBenchmarkRunner.RunPrepared(NestedPropertyChainsScenario, CacheMode, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> SequenceHeavyBuiltins()
		=> KatLangBenchmarkRunner.RunPrepared(SequenceHeavyBuiltinsScenario, CacheMode, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> PropertyRichSharedSubcomputations()
		=> KatLangBenchmarkRunner.RunPrepared(PropertyRichSharedSubcomputationsScenario, CacheMode, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> RealisticWhileCalculation()
		=> KatLangBenchmarkRunner.RunPrepared(RealisticWhileCalculationScenario, CacheMode, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> GcdWhileLoop()
		=> KatLangBenchmarkRunner.RunPrepared(GcdWhileLoopScenario, CacheMode, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> RepeatManyIterations()
		=> KatLangBenchmarkRunner.RunPrepared(RepeatManyIterationsScenario, CacheMode, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> NestedCapturedParentLoop()
		=> KatLangBenchmarkRunner.RunPrepared(NestedCapturedParentLoopScenario, CacheMode, LoopMode);
}

[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 3, iterationCount: 8)]
[Orderer(SummaryOrderPolicy.FastestToSlowest)]
[RankColumn]
public class LoopStage2Benchmarks
{
	private static readonly BenchmarkScenario MinimalRepeatLoopScenario = BenchmarkScenarioCatalog.MinimalRepeatLoop;
	private static readonly BenchmarkScenario MinimalWhileLoopScenario = BenchmarkScenarioCatalog.MinimalWhileLoop;
	private static readonly BenchmarkScenario ArithmeticWhileLoopScenario = BenchmarkScenarioCatalog.ArithmeticWhileLoop;
	private static readonly BenchmarkScenario CapturedParentLoopScenario = BenchmarkScenarioCatalog.CapturedParentLoop;
	private static readonly BenchmarkScenario NestedRepeatedCallLoopScenario = BenchmarkScenarioCatalog.NestedRepeatedCallLoop;
	private static readonly BenchmarkScenario SquareFreeCountInlineLoopScenario = BenchmarkScenarioCatalog.SquareFreeCountInlineLoop;
	private static readonly BenchmarkScenario SquareFreeCountLocalTempLoopScenario = BenchmarkScenarioCatalog.SquareFreeCountLocalTempLoop;

	[Params(BenchmarkLoopMode.Generic, BenchmarkLoopMode.Optimized)]
	public BenchmarkLoopMode LoopMode { get; set; }

	[Benchmark]
	public IReadOnlyList<Decimal128> MinimalRepeatLoop()
		=> KatLangBenchmarkRunner.RunPrepared(MinimalRepeatLoopScenario, BenchmarkCacheMode.Stage1, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> MinimalWhileLoop()
		=> KatLangBenchmarkRunner.RunPrepared(MinimalWhileLoopScenario, BenchmarkCacheMode.Stage1, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> ArithmeticWhileLoop()
		=> KatLangBenchmarkRunner.RunPrepared(ArithmeticWhileLoopScenario, BenchmarkCacheMode.Stage1, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> CapturedParentLoop()
		=> KatLangBenchmarkRunner.RunPrepared(CapturedParentLoopScenario, BenchmarkCacheMode.Stage1, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> NestedRepeatedCallLoop()
		=> KatLangBenchmarkRunner.RunPrepared(NestedRepeatedCallLoopScenario, BenchmarkCacheMode.Stage1, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> SquareFreeCountInlineLoop()
		=> KatLangBenchmarkRunner.RunPrepared(SquareFreeCountInlineLoopScenario, BenchmarkCacheMode.Stage1, LoopMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> SquareFreeCountLocalTempLoop()
		=> KatLangBenchmarkRunner.RunPrepared(SquareFreeCountLocalTempLoopScenario, BenchmarkCacheMode.Stage1, LoopMode);
}

[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 3, iterationCount: 8)]
[Orderer(SummaryOrderPolicy.FastestToSlowest)]
[RankColumn]
public class SequencePipelineStage2Benchmarks
{
	private static readonly BenchmarkScenario FilterCountEvenRangeScenario = BenchmarkScenarioCatalog.SequenceFilterCountEvenRange;
	private static readonly BenchmarkScenario SquareFreeFilterCount1000Scenario = BenchmarkScenarioCatalog.SequenceSquareFreeFilterCount1000;
	private static readonly BenchmarkScenario SquareFreeFilterCount10000Scenario = BenchmarkScenarioCatalog.SequenceSquareFreeFilterCount10000;
	private static readonly BenchmarkScenario SquareFreeRepeatCount1000Scenario = BenchmarkScenarioCatalog.SquareFreeCountLocalTempLoop1000;
	private static readonly BenchmarkScenario SquareFreeRepeatCount10000Scenario = BenchmarkScenarioCatalog.SquareFreeCountLocalTempLoop;

	[Params(BenchmarkSequencePipelineMode.Generic, BenchmarkSequencePipelineMode.Optimized)]
	public BenchmarkSequencePipelineMode SequencePipelineMode { get; set; }

	[Benchmark]
	public IReadOnlyList<Decimal128> FilterCountEvenRange()
		=> KatLangBenchmarkRunner.RunPrepared(
			FilterCountEvenRangeScenario,
			BenchmarkCacheMode.Stage1,
			BenchmarkLoopMode.Optimized,
			SequencePipelineMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> SquareFreeFilterCount1000()
		=> KatLangBenchmarkRunner.RunPrepared(
			SquareFreeFilterCount1000Scenario,
			BenchmarkCacheMode.Stage1,
			BenchmarkLoopMode.Optimized,
			SequencePipelineMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> SquareFreeFilterCount10000()
		=> KatLangBenchmarkRunner.RunPrepared(
			SquareFreeFilterCount10000Scenario,
			BenchmarkCacheMode.Stage1,
			BenchmarkLoopMode.Optimized,
			SequencePipelineMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> SquareFreeRepeatCount1000()
		=> KatLangBenchmarkRunner.RunPrepared(
			SquareFreeRepeatCount1000Scenario,
			BenchmarkCacheMode.Stage1,
			BenchmarkLoopMode.Optimized,
			BenchmarkSequencePipelineMode.Optimized);

	[Benchmark]
	public IReadOnlyList<Decimal128> SquareFreeRepeatCount10000()
		=> KatLangBenchmarkRunner.RunPrepared(
			SquareFreeRepeatCount10000Scenario,
			BenchmarkCacheMode.Stage1,
			BenchmarkLoopMode.Optimized,
			BenchmarkSequencePipelineMode.Optimized);
}

/// <summary>
/// M15 sequence-pipeline dispatch benchmarks: the per-call cost of the pipeline
/// PROBE on ordinary calls and dot-calls that are never candidates. Both workloads
/// run 100000 iterations of a step whose body is one non-candidate call or
/// dot-call; the generic loop strategy is pinned so every iteration goes through
/// the generic expression dispatch that hosts the probe. <c>Optimized</c> measures
/// the fusion-enabled miss path (recognition runs, nothing else may); <c>Generic</c>
/// measures the fusion-disabled path (the probe must bail before recognition).
/// Allocated bytes/op is the primary metric.
/// </summary>
[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 3, iterationCount: 8)]
[Orderer(SummaryOrderPolicy.FastestToSlowest)]
[RankColumn]
public class SequencePipelineDispatchBenchmarks
{
	private static readonly BenchmarkScenario NonCandidateCallsScenario = BenchmarkScenarioCatalog.DispatchNonCandidateCalls;
	private static readonly BenchmarkScenario NonCandidateDotCallsScenario = BenchmarkScenarioCatalog.DispatchNonCandidateDotCalls;

	[Params(BenchmarkSequencePipelineMode.Generic, BenchmarkSequencePipelineMode.Optimized)]
	public BenchmarkSequencePipelineMode SequencePipelineMode { get; set; }

	[Benchmark]
	public IReadOnlyList<Decimal128> NonCandidateCalls()
		=> KatLangBenchmarkRunner.RunPrepared(
			NonCandidateCallsScenario,
			BenchmarkCacheMode.Stage1,
			BenchmarkLoopMode.Generic,
			SequencePipelineMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> NonCandidateDotCalls()
		=> KatLangBenchmarkRunner.RunPrepared(
			NonCandidateDotCallsScenario,
			BenchmarkCacheMode.Stage1,
			BenchmarkLoopMode.Generic,
			SequencePipelineMode);
}
