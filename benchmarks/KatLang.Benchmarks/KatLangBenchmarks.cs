using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Order;

namespace KatLang.Benchmarks;

internal static class KatLangBenchmarkRunner
{
	internal static IReadOnlyList<decimal> RunWithFrontEnd(BenchmarkScenario scenario)
		=> KatLangEngine.EvaluateToAtoms(scenario.Source);

	internal static IReadOnlyList<decimal> RunPrepared(BenchmarkScenario scenario)
	{
		var result = Evaluator.RunFlat(new Expr.Block(scenario.PreparedRoot));
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

	[Benchmark(Baseline = true)]
	public IReadOnlyList<decimal> RepeatedZeroArgPropertyReuse()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(RepeatedZeroArgPropertyReuseScenario);

	[Benchmark]
	public IReadOnlyList<decimal> NestedPropertyChains()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(NestedPropertyChainsScenario);

	[Benchmark]
	public IReadOnlyList<decimal> SequenceHeavyBuiltins()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(SequenceHeavyBuiltinsScenario);

	[Benchmark]
	public IReadOnlyList<decimal> PropertyRichSharedSubcomputations()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(PropertyRichSharedSubcomputationsScenario);

	[Benchmark]
	public IReadOnlyList<decimal> RealisticWhileCalculation()
		=> KatLangBenchmarkRunner.RunWithFrontEnd(RealisticWhileCalculationScenario);
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

	[Benchmark(Baseline = true)]
	public IReadOnlyList<decimal> RepeatedZeroArgPropertyReuse()
		=> KatLangBenchmarkRunner.RunPrepared(RepeatedZeroArgPropertyReuseScenario);

	[Benchmark]
	public IReadOnlyList<decimal> NestedPropertyChains()
		=> KatLangBenchmarkRunner.RunPrepared(NestedPropertyChainsScenario);

	[Benchmark]
	public IReadOnlyList<decimal> SequenceHeavyBuiltins()
		=> KatLangBenchmarkRunner.RunPrepared(SequenceHeavyBuiltinsScenario);

	[Benchmark]
	public IReadOnlyList<decimal> PropertyRichSharedSubcomputations()
		=> KatLangBenchmarkRunner.RunPrepared(PropertyRichSharedSubcomputationsScenario);

	[Benchmark]
	public IReadOnlyList<decimal> RealisticWhileCalculation()
		=> KatLangBenchmarkRunner.RunPrepared(RealisticWhileCalculationScenario);
}