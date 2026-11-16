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
/// path does not have, so read the GC columns beside the time. Prepared evaluation with the loop optimizer
/// on (the production configuration). Filter: <c>--filter *SequencePipelineLargeList*</c>.
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

	[Params(BenchmarkSequencePipelineMode.Generic, BenchmarkSequencePipelineMode.Optimized)]
	public BenchmarkSequencePipelineMode SequencePipelineMode { get; set; }

	[Benchmark]
	public IReadOnlyList<Decimal128> CheapFilterCount100k()
		=> KatLangBenchmarkRunner.RunPrepared(
			CheapFilterCount100kScenario,
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
