using System.Diagnostics;
using System.Globalization;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Benchmarks;

internal static class BenchmarkLoopStatsDiagnosticRunner
{
	private static readonly BenchmarkScenario[] Scenarios =
	[
		BenchmarkScenarioCatalog.MinimalRepeatLoop,
		BenchmarkScenarioCatalog.MinimalWhileLoop,
		BenchmarkScenarioCatalog.ArithmeticWhileLoop,
		BenchmarkScenarioCatalog.CapturedParentLoop,
		BenchmarkScenarioCatalog.NestedRepeatedCallLoop,
		BenchmarkScenarioCatalog.SquareFreeCountInlineLoop,
		BenchmarkScenarioCatalog.SquareFreeCountLocalTempLoop,
	];

	public static bool TryRun(string[] args)
	{
		if (!args.Contains("--loop-stats", StringComparer.Ordinal))
		{
			return false;
		}

		WriteComparisonReport();
		return true;
	}

	private static void WriteComparisonReport()
	{
		Console.WriteLine("Loop optimization stats comparison");
		Console.WriteLine("Counters: hit/fallback planBuild exec/iter exprHit/exprFallback genericExpr plannedOp countedParam");
		Console.WriteLine();

		var scenarioLabelWidth = Scenarios.Max(scenario => scenario.Id.Length);

		foreach (var scenario in Scenarios)
		{
			WriteScenarioLine(scenario, BenchmarkLoopMode.Generic, scenarioLabelWidth);
			WriteScenarioLine(scenario, BenchmarkLoopMode.Optimized, scenarioLabelWidth);
			Console.WriteLine();
		}
	}

	private static void WriteScenarioLine(
		BenchmarkScenario scenario,
		BenchmarkLoopMode loopMode,
		int scenarioLabelWidth)
	{
		var diagnostics = new LoopOptimizationDiagnostics();
		var stopwatch = Stopwatch.StartNew();
		var result = Evaluator.Run(
			new Expr.Block(scenario.PreparedRoot),
			new RunScopedZeroArgPropertyResultCache(),
			enableLoopOptimization: loopMode == BenchmarkLoopMode.Optimized,
			loopDiagnostics: diagnostics);
		stopwatch.Stop();

		if (result.IsError)
			throw new InvalidOperationException($"Loop stats scenario '{scenario.Id}' failed: {result.Error}");

		var atoms = result.Value.ToHostAtoms();
		if (!scenario.ExpectedAtoms.SequenceEqual(atoms))
		{
			throw new InvalidOperationException(
				$"Loop stats scenario '{scenario.Id}' produced unexpected atoms. Expected [{string.Join(", ", scenario.ExpectedAtoms)}] but got [{string.Join(", ", atoms)}].");
		}

		var stats = diagnostics.GetSnapshot();
		Console.WriteLine(string.Create(
			CultureInfo.InvariantCulture,
			$"{scenario.Id.PadRight(scenarioLabelWidth)} | {loopMode,-9} | {stopwatch.Elapsed.TotalMilliseconds,8:0.0} ms | hit={stats.OptimizedLoopHits}/fb={stats.OptimizedLoopFallbacks} planBuild={stats.LoopPlanBuilds} exec={stats.LoopExecutions}/{stats.LoopIterations} expr={stats.PlannedExpressionHits}/{stats.PlannedExpressionFallbacks} genericExpr={stats.GenericExpressionEvaluationsInsideOptimizedLoops} plannedOp={stats.PlannedBuiltinOperations} countedParam={stats.CountedParameterReferencesPlanned}/{stats.CountedParameterReferencesFallbacks} reasons={FormatFallbackReasons(stats.FallbackReasons)}"));
		WriteLoopPlanDiagnostics(stats.LoopPlans);
	}

	private static string FormatFallbackReasons(IReadOnlyDictionary<string, long> reasons)
		=> reasons.Count == 0
			? "-"
			: string.Join(", ", reasons.Select(entry => $"{entry.Key}:{entry.Value}"));

	private static void WriteLoopPlanDiagnostics(IReadOnlyList<LoopPlanDiagnosticSnapshot> plans)
	{
		foreach (var plan in plans)
		{
			Console.WriteLine($"  Loop plan: {plan.Identity}");
			Console.WriteLine($"    kind: {plan.Kind}");
			Console.WriteLine($"    state arity: {plan.StateArity}");
			Console.WriteLine($"    optimized: {(plan.Optimized ? "yes" : $"no ({plan.FallbackReason})")}");
			Console.WriteLine($"    builds/executions: {plan.BuildCount}/{plan.ExecutionCount}");

			foreach (var temp in plan.Temps)
				Console.WriteLine($"    temp[{temp.Name}]: {FormatTempDiagnostic(temp)}");

			foreach (var expression in plan.Expressions)
				Console.WriteLine($"    {FormatExpressionRole(expression)}: {FormatExpressionDiagnostic(expression)}");
		}
	}

	private static string FormatTempDiagnostic(LoopTempDiagnosticSnapshot temp)
		=> temp.Planned
			? $"planned: {temp.PlanSummary}"
			: $"fallback: {temp.FallbackReason}";

	private static string FormatExpressionRole(LoopExpressionDiagnosticSnapshot expression)
		=> expression.Role == "output" && expression.Index is { } index
			? $"output[{index}]"
			: expression.Role;

	private static string FormatExpressionDiagnostic(LoopExpressionDiagnosticSnapshot expression)
		=> expression.Planned
			? $"planned: {expression.PlanSummary}"
			: $"fallback: {expression.FallbackReason}";
}
