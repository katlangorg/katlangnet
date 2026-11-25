using System.Globalization;
using KatLang.Evaluation.Caching;

namespace KatLang.Benchmarks;

internal static class BenchmarkCacheStatsDiagnosticRunner
{
	private static readonly (string Label, Func<BenchmarkScenario, KatLangBenchmarkRunner.BenchmarkRunWithCacheStats> Run)[] Modes =
	[
		("Prepared", KatLangBenchmarkRunner.RunPreparedWithStats),
		("Parse+Eval", KatLangBenchmarkRunner.RunWithFrontEndWithStats),
	];

	private static readonly BenchmarkScenario[] Scenarios =
	[
		BenchmarkScenarioCatalog.RepeatedZeroArgPropertyReuse,
		BenchmarkScenarioCatalog.ScalarHelperSumCalls,
		BenchmarkScenarioCatalog.PropertyRichSharedSubcomputations,
		BenchmarkScenarioCatalog.RealisticWhileCalculation,
		BenchmarkScenarioCatalog.NestedPropertyChains,
	];

	public static bool TryRun(string[] args)
	{
		if (!args.Contains("--cache-stats", StringComparer.Ordinal))
		{
			return false;
		}

		WriteComparisonReport();
		return true;
	}

	private static void WriteComparisonReport()
	{
		Console.WriteLine("Stage 1 zero-arg cache stats comparison");
		Console.WriteLine("Access-kind format: req/hit/miss/store");
		Console.WriteLine();

		var scenarioLabelWidth = Scenarios.Max(scenario => scenario.Id.Length);

		foreach (var (label, run) in Modes)
		{
			Console.WriteLine(label);
			foreach (var scenario in Scenarios)
			{
				var snapshot = run(scenario).CacheStats;
				Console.WriteLine(FormatScenarioLine(scenario, snapshot, scenarioLabelWidth));
			}

			Console.WriteLine();
		}
	}

	private static string FormatScenarioLine(
		BenchmarkScenario scenario,
		ZeroArgPropertyResultCacheSnapshot snapshot,
		int scenarioLabelWidth)
	{
		var lexical = snapshot.GetAccessKind(ZeroArgPropertyAccessKind.Lexical);
		var countedLexical = snapshot.GetAccessKind(ZeroArgPropertyAccessKind.CountedLexical);
		var structural = snapshot.GetAccessKind(ZeroArgPropertyAccessKind.Structural);
		var countedStructural = snapshot.GetAccessKind(ZeroArgPropertyAccessKind.CountedStructural);
		var hitRate = snapshot.TotalRequests == 0
			? 0m
			: decimal.Divide(snapshot.Hits, snapshot.TotalRequests) * 100m;

		return string.Create(
			CultureInfo.InvariantCulture,
			$"{scenario.Id.PadRight(scenarioLabelWidth)} | req={snapshot.TotalRequests} hit={snapshot.Hits} miss={snapshot.Misses} store={snapshot.Stores} distinct={snapshot.DistinctKeysCreated} repeatMiss={snapshot.RepeatedMissRequests} max={snapshot.MaxCacheSize} hitRate={hitRate:0.0}% | lex={FormatAccessKind(lexical)} cLex={FormatAccessKind(countedLexical)} struct={FormatAccessKind(structural)} cStruct={FormatAccessKind(countedStructural)}");
	}

	private static string FormatAccessKind(ZeroArgPropertyResultCacheAccessSnapshot snapshot)
		=> string.Create(
			CultureInfo.InvariantCulture,
			$"{snapshot.Requests}/{snapshot.Hits}/{snapshot.Misses}/{snapshot.Stores}");
}