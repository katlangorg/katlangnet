using System.Diagnostics;
using System.Globalization;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Sequences;

namespace KatLang.Benchmarks;

internal static class BenchmarkSequenceStatsDiagnosticRunner
{
	private static BenchmarkScenario[] Scenarios =>
	[
		BenchmarkScenarioCatalog.SquareFreeCountLocalTempLoop1000,
		BenchmarkScenarioCatalog.SquareFreeCountLocalTempLoop,
		BenchmarkScenarioCatalog.SequenceFilterCountEvenRange,
		BenchmarkScenarioCatalog.SequenceSquareFreeFilterCount1000,
		BenchmarkScenarioCatalog.SequenceSquareFreeFilterCount10000,
	];

	public static bool TryRun(string[] args)
	{
		if (!args.Contains("--sequence-stats", StringComparer.Ordinal))
		{
			return false;
		}

		WriteComparisonReport();
		return true;
	}

	private static void WriteComparisonReport()
	{
		Console.WriteLine("Sequence pipeline optimization stats comparison");
		Console.WriteLine("Counters: hit/fallback directRangeHit/directRangeFallback predicateCalls avoidedFilteredMaterialization avoidedSourceMaterialization");
		Console.WriteLine();

		var scenarioLabelWidth = Scenarios.Max(scenario => scenario.Id.Length);

		foreach (var scenario in Scenarios)
		{
			WriteScenarioLine(scenario, BenchmarkSequencePipelineMode.Generic, scenarioLabelWidth);
			WriteScenarioLine(scenario, BenchmarkSequencePipelineMode.Optimized, scenarioLabelWidth);
			Console.WriteLine();
		}
	}

	private static void WriteScenarioLine(
		BenchmarkScenario scenario,
		BenchmarkSequencePipelineMode sequenceMode,
		int scenarioLabelWidth)
	{
		var diagnostics = new SequencePipelineDiagnostics();
		var stopwatch = Stopwatch.StartNew();
		var result = Evaluator.Run(
			new Expr.Block(scenario.PreparedRoot),
			new RunScopedZeroArgPropertyResultCache(),
			enableLoopOptimization: true,
			loopDiagnostics: null,
			enableSequencePipelineOptimization: sequenceMode == BenchmarkSequencePipelineMode.Optimized,
			sequenceDiagnostics: diagnostics);
		stopwatch.Stop();

		if (result.IsError)
			throw new InvalidOperationException($"Sequence stats scenario '{scenario.Id}' failed: {result.Error}");

		var atoms = result.Value.ToHostAtoms();
		if (!scenario.ExpectedAtoms.SequenceEqual(atoms))
		{
			throw new InvalidOperationException(
				$"Sequence stats scenario '{scenario.Id}' produced unexpected atoms. Expected [{string.Join(", ", scenario.ExpectedAtoms)}] but got [{string.Join(", ", atoms)}].");
		}

		var stats = diagnostics.GetSnapshot();
		Console.WriteLine(string.Create(
			CultureInfo.InvariantCulture,
			$"{scenario.Id.PadRight(scenarioLabelWidth)} | {sequenceMode,-9} | {stopwatch.Elapsed.TotalMilliseconds,8:0.0} ms | hit={stats.FilterCountFusionHits}/fb={stats.FilterCountFusionFallbacks} directRange={stats.DirectRangeFusionHits}/fb={stats.DirectRangeFusionFallbacks} predicateCalls={stats.FilterCountPredicateCalls} avoidedFiltered={stats.AvoidedFilteredResultMaterializations} avoidedSource={stats.AvoidedSourceMaterializations} reasons={FormatFallbackReasons(stats.FallbackReasons)}"));
		WritePipelineDiagnostics(stats.Pipelines);
	}

	private static string FormatFallbackReasons(IReadOnlyDictionary<string, long> reasons)
		=> reasons.Count == 0
			? "-"
			: string.Join(", ", reasons.Select(entry => $"{entry.Key}:{entry.Value}"));

	private static void WritePipelineDiagnostics(IReadOnlyList<SequencePipelineDiagnosticSnapshot> pipelines)
	{
		foreach (var pipeline in pipelines)
		{
			Console.WriteLine($"  Sequence pipeline: {pipeline.Summary}");
			Console.WriteLine($"    form: {pipeline.Form}");
			Console.WriteLine($"    optimized: {(pipeline.Optimized ? "yes" : $"no ({pipeline.FallbackReason})")}");
			Console.WriteLine($"    fusion: {pipeline.Fusion}");
			Console.WriteLine($"    source kind: {pipeline.SourceKind}");
			Console.WriteLine($"    source: {pipeline.SourceSummary}");
			Console.WriteLine($"    source execution: {pipeline.SourceExecution}");
			if (pipeline.SourceExecutionFallbackReason is { } sourceExecutionReason)
				Console.WriteLine($"    reason: {sourceExecutionReason}");
			Console.WriteLine($"    predicate: {pipeline.PredicateSummary}");
			if (pipeline.ExecutionCount > 0)
			{
				Console.WriteLine($"    source item count: {pipeline.SourceItemCount}");
				Console.WriteLine($"    predicate calls: {pipeline.PredicateCalls}");
				if (pipeline.LastResultCount is { } resultCount)
					Console.WriteLine($"    result count: {resultCount}");
				Console.WriteLine($"    avoided filtered result materialization: {pipeline.AvoidedFilteredResultMaterializationCount}");
				Console.WriteLine($"    avoided source materialization: {pipeline.AvoidedSourceMaterializationCount}");
			}
		}
	}
}
