using System.Collections.Immutable;
using System.Numerics;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Configs;
using BenchmarkDotNet.Order;
using BenchmarkDotNet.Reports;
using BenchmarkDotNet.Running;

namespace KatLang.Benchmarks;

/// <summary>
/// Filter→count fusion ON (<c>Optimized</c>) against OFF (<c>Generic</c>) on ONE pipeline whose generic
/// composition materializes 100,000-item lists: <c>count(filter(range(1, 100000), Pos))</c> with the cheap
/// predicate <c>Pos(n) = n &gt; 0</c>, so the source and the kept list are both at the default ceiling. The
/// generic path's large lists and the survival of their items cost Gen1/Gen2 collections that the fused
/// path does not have, so read the GC columns beside the time. <c>PropertyFilterCount100k</c> (2026-11-18)
/// is the same pipeline over a property source, <c>R.filter(Pos).count</c> with <c>R = range(1, 100000)</c>:
/// it is no written range, so the fused strategy reads its items through the dot-receiver adapter. Prepared
/// evaluation with the loop optimizer on (the production configuration). Filter:
/// <c>--filter *SequencePipelineLargeList*</c>.
/// <para>No <c>[RankColumn]</c>: BenchmarkDotNet 0.14.0's rank column throws while the summary is built
/// under <c>--job dry</c> (benchmarks/README.md, Exit Code), so this class stays runnable with any job.
/// The execution order follows <see cref="SequencePipelineModeOrderConfig"/>.</para>
/// </summary>
[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 3, iterationCount: 20, invocationCount: 16)]
[Config(typeof(SequencePipelineModeOrderConfig))]
public class SequencePipelineLargeListBenchmarks
{
	private static readonly BenchmarkScenario CheapFilterCount100kScenario = BenchmarkScenarioCatalog.SequenceCheapFilterCount100k;
	private static readonly BenchmarkScenario PropertyFilterCount100kScenario = BenchmarkScenarioCatalog.SequencePropertyFilterCount100k;

	[Params(BenchmarkSequencePipelineMode.Generic, BenchmarkSequencePipelineMode.Optimized)]
	public BenchmarkSequencePipelineMode SequencePipelineMode { get; set; }

	[Benchmark]
	public IReadOnlyList<Decimal128> CheapFilterCount100k()
		=> KatLangBenchmarkRunner.RunPrepared(
			CheapFilterCount100kScenario,
			BenchmarkCacheMode.Stage1,
			BenchmarkLoopMode.Optimized,
			SequencePipelineMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> PropertyFilterCount100k()
		=> KatLangBenchmarkRunner.RunPrepared(
			PropertyFilterCount100kScenario,
			BenchmarkCacheMode.Stage1,
			BenchmarkLoopMode.Optimized,
			SequencePipelineMode);
}

/// <summary>
/// Filter→count fusion ON against OFF on runs that repeat a pipeline, one operation per iteration (about
/// one second each): the audit program <c>map(range(1, 20), K).sum</c> with 20 pipelines of 100,000 items
/// (<c>RepeatedFilterCount100k</c>), and 2,000 pipelines of 1,000 items with the same 2,000,000 predicate
/// calls (<c>RepeatedShortFilterCount</c>), where no list is large and the comparison shows the per-pipeline
/// overhead. Filter: <c>--filter *SequencePipelineRepeated*</c>. No <c>[RankColumn]</c>, as in
/// <see cref="SequencePipelineLargeListBenchmarks"/>.
/// </summary>
[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 3, iterationCount: 15, invocationCount: 1)]
[Config(typeof(SequencePipelineModeOrderConfig))]
public class SequencePipelineRepeatedBenchmarks
{
	private static readonly BenchmarkScenario RepeatedFilterCount100kScenario = BenchmarkScenarioCatalog.SequenceRepeatedFilterCount100k;
	private static readonly BenchmarkScenario RepeatedShortFilterCountScenario = BenchmarkScenarioCatalog.SequenceRepeatedShortFilterCount;

	[Params(BenchmarkSequencePipelineMode.Generic, BenchmarkSequencePipelineMode.Optimized)]
	public BenchmarkSequencePipelineMode SequencePipelineMode { get; set; }

	[Benchmark]
	public IReadOnlyList<Decimal128> RepeatedFilterCount100k()
		=> KatLangBenchmarkRunner.RunPrepared(
			RepeatedFilterCount100kScenario,
			BenchmarkCacheMode.Stage1,
			BenchmarkLoopMode.Optimized,
			SequencePipelineMode);

	[Benchmark]
	public IReadOnlyList<Decimal128> RepeatedShortFilterCount()
		=> KatLangBenchmarkRunner.RunPrepared(
			RepeatedShortFilterCountScenario,
			BenchmarkCacheMode.Stage1,
			BenchmarkLoopMode.Optimized,
			SequencePipelineMode);
}

/// <summary>
/// The generic collection builtins that build or reduce a 100,000-item list, one per method: <c>take</c>,
/// <c>skip</c>, <c>distinct</c>, <c>order</c>, <c>orderDesc</c>, <c>sum</c>, <c>avg</c>, <c>min</c> and
/// <c>max</c> over <c>range(…)</c> (the scenario descriptions in <see cref="BenchmarkScenarioCatalog"/> name each program), plus
/// <c>range(1, 100000).map(Inc).sum</c>. None of these shapes is fused, so there is no fusion mode
/// parameter: the production configuration (both optimizers on) is measured. Each run also builds its
/// 100,000-item source range (0.8 MB of list slots and 3.2 MB of numbers), so read the allocation column
/// against <c>RangeCount100k</c>, which only builds and counts that source. Since 2026-11-17 the list
/// builders allocate their exact result array once and hand it over, and the numeric builtins read the
/// numbers through a view instead of a copied <c>List&lt;Decimal128&gt;</c>. <c>Atoms100k</c> and
/// <c>RetainedTake100k</c> (2026-11-18) add <c>atoms</c> over the same source and a 50,000-item
/// <c>take</c> of a retained collector (NEED-07) holding its 100,000 cells. Filter:
/// <c>--filter *SequenceBuiltinLargeList*</c>. No <c>[RankColumn]</c>, as in
/// <see cref="SequencePipelineLargeListBenchmarks"/>.
/// </summary>
[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 3, iterationCount: 20, invocationCount: 16)]
public class SequenceBuiltinLargeListBenchmarks
{
	private static readonly BenchmarkScenario RangeCount100kScenario = BenchmarkScenarioCatalog.SequenceRangeCount100k;
	private static readonly BenchmarkScenario Take100kScenario = BenchmarkScenarioCatalog.SequenceTake100k;
	private static readonly BenchmarkScenario Skip100kScenario = BenchmarkScenarioCatalog.SequenceSkip100k;
	private static readonly BenchmarkScenario Distinct100kScenario = BenchmarkScenarioCatalog.SequenceDistinct100k;
	private static readonly BenchmarkScenario Order100kScenario = BenchmarkScenarioCatalog.SequenceOrder100k;
	private static readonly BenchmarkScenario OrderDesc100kScenario = BenchmarkScenarioCatalog.SequenceOrderDesc100k;
	private static readonly BenchmarkScenario Sum100kScenario = BenchmarkScenarioCatalog.SequenceSum100k;
	private static readonly BenchmarkScenario Avg100kScenario = BenchmarkScenarioCatalog.SequenceAvg100k;
	private static readonly BenchmarkScenario Min100kScenario = BenchmarkScenarioCatalog.SequenceMin100k;
	private static readonly BenchmarkScenario Max100kScenario = BenchmarkScenarioCatalog.SequenceMax100k;
	private static readonly BenchmarkScenario MapSum100kScenario = BenchmarkScenarioCatalog.SequenceMapSum100k;
	private static readonly BenchmarkScenario Atoms100kScenario = BenchmarkScenarioCatalog.SequenceAtoms100k;
	private static readonly BenchmarkScenario RetainedTake100kScenario = BenchmarkScenarioCatalog.SequenceRetainedTake100k;

	[Benchmark]
	public IReadOnlyList<Decimal128> RangeCount100k() => Run(RangeCount100kScenario);

	[Benchmark]
	public IReadOnlyList<Decimal128> Take100k() => Run(Take100kScenario);

	[Benchmark]
	public IReadOnlyList<Decimal128> Skip100k() => Run(Skip100kScenario);

	[Benchmark]
	public IReadOnlyList<Decimal128> Distinct100k() => Run(Distinct100kScenario);

	[Benchmark]
	public IReadOnlyList<Decimal128> Order100k() => Run(Order100kScenario);

	[Benchmark]
	public IReadOnlyList<Decimal128> OrderDesc100k() => Run(OrderDesc100kScenario);

	[Benchmark]
	public IReadOnlyList<Decimal128> Sum100k() => Run(Sum100kScenario);

	[Benchmark]
	public IReadOnlyList<Decimal128> Avg100k() => Run(Avg100kScenario);

	[Benchmark]
	public IReadOnlyList<Decimal128> Min100k() => Run(Min100kScenario);

	[Benchmark]
	public IReadOnlyList<Decimal128> Max100k() => Run(Max100kScenario);

	[Benchmark]
	public IReadOnlyList<Decimal128> MapSum100k() => Run(MapSum100kScenario);

	[Benchmark]
	public IReadOnlyList<Decimal128> Atoms100k() => Run(Atoms100kScenario);

	[Benchmark]
	public IReadOnlyList<Decimal128> RetainedTake100k() => Run(RetainedTake100kScenario);

	private static IReadOnlyList<Decimal128> Run(BenchmarkScenario scenario)
		=> KatLangBenchmarkRunner.RunPrepared(
			scenario,
			BenchmarkCacheMode.Stage1,
			BenchmarkLoopMode.Optimized,
			BenchmarkSequencePipelineMode.Optimized);
}

/// <summary>
/// The execution order of the sequence-pipeline ON/OFF classes: methods in declaration order, and each
/// method's two modes back to back, <c>Generic</c> first — or <c>Optimized</c> first when the environment
/// variable <see cref="OrderVariable"/> is <c>OptimizedFirst</c>. Two runs in opposite orders give an
/// alternating (ABBA) comparison, so a drift in machine state during a run does not favour one mode.
/// Summary order, grouping and highlighting stay BenchmarkDotNet's defaults.
/// </summary>
public sealed class SequencePipelineModeOrderConfig : ManualConfig
{
	/// <summary>The environment variable that puts <c>Optimized</c> first: <c>OptimizedFirst</c>; anything else keeps <c>Generic</c> first.</summary>
	public const string OrderVariable = "KATLANG_BENCH_SEQUENCE_MODE_ORDER";

	public SequencePipelineModeOrderConfig()
		=> Orderer = new ModeOrderer(string.Equals(
			Environment.GetEnvironmentVariable(OrderVariable), "OptimizedFirst", StringComparison.Ordinal));

	private sealed class ModeOrderer(bool optimizedFirst) : IOrderer
	{
		public IEnumerable<BenchmarkCase> GetExecutionOrder(
			ImmutableArray<BenchmarkCase> benchmarksCase,
			IEnumerable<BenchmarkLogicalGroupRule>? order = null)
			=> benchmarksCase
				.OrderBy(benchmarkCase => benchmarkCase.Descriptor.WorkloadMethod.MetadataToken)
				.ThenBy(benchmarkCase => IsOptimized(benchmarkCase) == optimizedFirst ? 0 : 1)
				.ToArray();

		public IEnumerable<BenchmarkCase> GetSummaryOrder(ImmutableArray<BenchmarkCase> benchmarksCases, Summary summary)
			=> DefaultOrderer.Instance.GetSummaryOrder(benchmarksCases, summary);

		public string? GetHighlightGroupKey(BenchmarkCase benchmarkCase)
			=> DefaultOrderer.Instance.GetHighlightGroupKey(benchmarkCase);

		public string GetLogicalGroupKey(ImmutableArray<BenchmarkCase> allBenchmarksCases, BenchmarkCase benchmarkCase)
			=> DefaultOrderer.Instance.GetLogicalGroupKey(allBenchmarksCases, benchmarkCase)!;

		public IEnumerable<IGrouping<string, BenchmarkCase>> GetLogicalGroupOrder(
			IEnumerable<IGrouping<string, BenchmarkCase>> logicalGroups,
			IEnumerable<BenchmarkLogicalGroupRule>? order = null)
			=> DefaultOrderer.Instance.GetLogicalGroupOrder(logicalGroups, order);

		public bool SeparateLogicalGroups => DefaultOrderer.Instance.SeparateLogicalGroups;

		private static bool IsOptimized(BenchmarkCase benchmarkCase)
			=> benchmarkCase.Parameters[nameof(SequencePipelineLargeListBenchmarks.SequencePipelineMode)]
				is BenchmarkSequencePipelineMode.Optimized;
	}
}
