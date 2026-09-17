using System.Text;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Order;
using KatLang.Evaluation.Caching;

namespace KatLang.Benchmarks;

/// <summary>
/// Program shapes whose cost is dominated by the evaluator's declaration / activation /
/// scope-owner bookkeeping (the state the September 2026 invalid-state audit §3.1 moved
/// from process-global <c>ConditionalWeakTable</c>s onto the runtime model): every shape
/// repeats its measured operation in a single root row. Divide per-run measurements by
/// <c>All.UnitsPerRun</c> to compare per-operation costs (201 ordinarily, 804 nested
/// calls, or 41 recursive calls). The sources are
/// deterministic and fixed; the pass/fail question is behavioural equivalence, and the
/// measurement question is per-operation time, allocated bytes, and Gen0 pressure.
/// </summary>
internal static class EvaluatorIdentityStateScenarios
{
	/// <summary>Repetitions of the measured operation in each root row.</summary>
	internal const int Units = 201;

	/// <summary>Recursion depth of the <see cref="Recursion"/> shape (the run's dynamic depth limit is 128).</summary>
	internal const int RecursionDepth = 40;

	/// <summary>One parameterized call: <c>Inc(0)</c>, entering a parameterized body per unit.</summary>
	internal static readonly string ParameterizedCall = "Inc(v) = v + 1\n" + Chain("Inc(0)") + "\n";

	/// <summary>Three nested parameterized calls per unit: <c>Nested(0)</c> = <c>Inc(Inc(Inc(0)))</c>.</summary>
	internal static readonly string NestedCalls =
		"Inc(v) = v + 1\nNested(v) = Inc(Inc(Inc(v)))\n" + Chain("Nested(0)") + "\n";

	/// <summary>Exported zero-argument property value read: the first read evaluates, the rest hit the run cache.</summary>
	internal static readonly string PropertyCacheHit = "A = 1\n" + Chain("A") + "\n";

	/// <summary>
	/// Local-only zero-argument property read inside ONE activation of its owner: <c>Local</c>
	/// captures <c>n</c>, so its cache entry is per binding context; the first read evaluates
	/// and the rest hit that context's entry.
	/// </summary>
	internal static readonly string LocalOnlyPropertyRead =
		"Outer(n) = {\n  Local = n + 1\n  " + Chain("Local") + "\n}\nOuter(1)\n";

	/// <summary>Structural member access <c>M.A</c> of an exported nested block member.</summary>
	internal static readonly string MemberChain = "M = { public A = 1 }\n" + Chain("M.A") + "\n";

	/// <summary>
	/// A nested parameterized call whose body reads an ancestor's parameter: every
	/// <c>Inner(1)</c> creates an activation and resolves <c>n</c> through the owning
	/// activation of <c>Outer</c> (the captured-parameter lookup path).
	/// </summary>
	internal static readonly string CapturedAncestorParameter =
		"Outer(n) = {\n  Inner(k) = n + k\n  " + Chain("Inner(1)") + "\n}\nOuter(5)\n";

	/// <summary>
	/// Direct recursion to <see cref="RecursionDepth"/>: each level is a distinct activation of
	/// ONE declaration, and the accumulated call stack is deepest at the base case.
	/// </summary>
	internal static readonly string Recursion =
		$"Sum(n) = if(n == 0, 0, n + Sum(n - 1))\nSum({RecursionDepth})\n";

	/// <summary>A clause-family call per unit: branch matching wires the selected body under an activated family scope.</summary>
	internal static readonly string ConditionalCall = "F(0) = 100\nF(x) = x + 1\n" + Chain("F(1)") + "\n";

	internal static readonly IReadOnlyList<(string Name, string Source, int UnitsPerRun)> All =
	[
		("ParameterizedCall", ParameterizedCall, Units),
		("NestedCalls", NestedCalls, Units * 4),
		("PropertyCacheHit", PropertyCacheHit, Units),
		("LocalOnlyPropertyRead", LocalOnlyPropertyRead, Units),
		("MemberChain", MemberChain, Units),
		("CapturedAncestorParameter", CapturedAncestorParameter, Units),
		("Recursion", Recursion, RecursionDepth + 1),
		("ConditionalCall", ConditionalCall, Units),
	];

	private static string Chain(string term)
	{
		var builder = new StringBuilder(term);
		for (var i = 1; i < Units; i++)
			builder.Append(" + ").Append(term);
		return builder.ToString();
	}

	/// <summary>Parses and elaborates a scenario once; a failed parse is a benchmark configuration error.</summary>
	internal static Algorithm Prepare(string source)
	{
		var parsed = Parser.Parse(source);
		if (parsed.HasErrors)
			throw new InvalidOperationException($"Benchmark scenario failed to parse: {string.Join("; ", parsed.Diagnostics)}");
		return parsed.Root;
	}

	/// <summary>Evaluates a prepared scenario with a fresh run-scoped cache (the engine's default configuration).</summary>
	internal static Result Evaluate(Algorithm root)
	{
		var result = Evaluator.Run(
			new Expr.AlgorithmExpr(root),
			new RunScopedZeroArgPropertyResultCache(),
			enableLoopOptimization: true,
			loopDiagnostics: null);
		if (result.IsError)
			throw new InvalidOperationException($"Benchmark scenario failed during evaluation: {result.Error}");
		return result.Value;
	}
}

[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 3, iterationCount: 8)]
[Orderer(SummaryOrderPolicy.Declared)]
public class EvaluatorIdentityStateBenchmarks
{
	private static readonly Algorithm ParameterizedCallRoot = EvaluatorIdentityStateScenarios.Prepare(EvaluatorIdentityStateScenarios.ParameterizedCall);
	private static readonly Algorithm NestedCallsRoot = EvaluatorIdentityStateScenarios.Prepare(EvaluatorIdentityStateScenarios.NestedCalls);
	private static readonly Algorithm PropertyCacheHitRoot = EvaluatorIdentityStateScenarios.Prepare(EvaluatorIdentityStateScenarios.PropertyCacheHit);
	private static readonly Algorithm LocalOnlyPropertyReadRoot = EvaluatorIdentityStateScenarios.Prepare(EvaluatorIdentityStateScenarios.LocalOnlyPropertyRead);
	private static readonly Algorithm MemberChainRoot = EvaluatorIdentityStateScenarios.Prepare(EvaluatorIdentityStateScenarios.MemberChain);
	private static readonly Algorithm CapturedAncestorParameterRoot = EvaluatorIdentityStateScenarios.Prepare(EvaluatorIdentityStateScenarios.CapturedAncestorParameter);
	private static readonly Algorithm RecursionRoot = EvaluatorIdentityStateScenarios.Prepare(EvaluatorIdentityStateScenarios.Recursion);
	private static readonly Algorithm ConditionalCallRoot = EvaluatorIdentityStateScenarios.Prepare(EvaluatorIdentityStateScenarios.ConditionalCall);

	[Benchmark(Baseline = true)]
	public Result ParameterizedCall() => EvaluatorIdentityStateScenarios.Evaluate(ParameterizedCallRoot);

	[Benchmark]
	public Result NestedCalls() => EvaluatorIdentityStateScenarios.Evaluate(NestedCallsRoot);

	[Benchmark]
	public Result PropertyCacheHit() => EvaluatorIdentityStateScenarios.Evaluate(PropertyCacheHitRoot);

	[Benchmark]
	public Result LocalOnlyPropertyRead() => EvaluatorIdentityStateScenarios.Evaluate(LocalOnlyPropertyReadRoot);

	[Benchmark]
	public Result MemberChain() => EvaluatorIdentityStateScenarios.Evaluate(MemberChainRoot);

	[Benchmark]
	public Result CapturedAncestorParameter() => EvaluatorIdentityStateScenarios.Evaluate(CapturedAncestorParameterRoot);

	[Benchmark]
	public Result Recursion() => EvaluatorIdentityStateScenarios.Evaluate(RecursionRoot);

	[Benchmark]
	public Result ConditionalCall() => EvaluatorIdentityStateScenarios.Evaluate(ConditionalCallRoot);
}

/// <summary>
/// Signature-width scaling of the activation snapshot itself. Wide captures must remain
/// linear: using a set for ownership but scanning all previously kept names regressed
/// this to quadratic work during the initial explicit-state implementation.
/// </summary>
[MemoryDiagnoser]
public class ParameterActivationCaptureBenchmarks
{
	[Params(8, 128, 2048)]
	public int Width { get; set; }
	private string[] _names = [];
	private IReadOnlyList<(string Name, Result Value)> _values = [];
	private Evaluator.EvalCtx _context;

	[GlobalSetup]
	public void Setup()
	{
		_names = Enumerable.Range(0, Width).Select(i => $"p{i}").ToArray();
		_values = _names.Select(n => (n, (Result)new Result.Atom(1))).ToArray();
		_context = Evaluator.EvalCtx.Empty;
	}

	[Benchmark]
	public object Capture() => ParameterActivation.Capture(_names, _context, _values);
}
