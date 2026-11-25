using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Order;
using KatLang.Evaluation;

namespace KatLang.Benchmarks;

/// <summary>
/// Evaluator-owned structural equality and hashing (SEC-02, SEC-02-FU): the repeated-reference
/// <c>contains</c>/<c>distinct</c> memo, the charged <c>==</c>/<c>!=</c>, repeated-name agreement in
/// ordinary calls and clause families, string payload charging, and the ordinary scalar and short-
/// string comparisons whose cost must stay unchanged. <c>A</c>/<c>B</c> are independently built equal
/// doubling DAGs of depth 40 (41 distinct nodes, 2^40 paths), <c>C</c> differs only in its shared
/// deepest leaf; <c>W</c>/<c>X</c> are independent equal flat lists, <c>Y</c> differs in its last item.
/// <c>text(k)</c> returns one of two distinct 64,000-unit string objects with equal text.
/// The sources are deterministic; compare time and allocated bytes between builds, never across
/// shapes.
/// </summary>
internal static class StructuralComparisonScenarios
{
	private const string Dags = "Wrap = [x, x]\nA = Wrap(1).repeat(40)\nB = Wrap(1).repeat(40)\nC = Wrap(2).repeat(40)\n";

	private const string Flat = "W = range(1, 5000)\nX = range(1, 5000).map{n * 1}\nY = range(1, 5000).map{if(n == 5000, 0, n)}\n";

	private static readonly string LongText = new('k', 64_000);

	// Two distinct objects with equal text: their comparison reads the whole payload.
	private static readonly Result.Str FirstText = new(LongText);
	private static readonly Result.Str SecondText = new(new string('k', 64_000));

	internal static readonly HostOperations Operations = HostOperations.Create(
		HostOperation.Create("text", (args, _) => ((Result.Atom)args[0]).Value == 1 ? FirstText : SecondText, "k"));

	internal static readonly IReadOnlyList<(string Name, string Source)> All =
	[
		("DeepRepeatedContains", Dags + "range(1, 2000).map{if(n > 0, A, A)}.contains(C)"),
		("DeepRepeatedDistinct", Dags + "distinct(range(1, 2000).map{if(n > 0, A, A)}).count"),
		("DeepEqualOperator", Dags + "range(1, 200).filter{if(n > 0, A == B, false)}.count"),
		("DeepMismatchOperator", Dags + "range(1, 200).filter{if(n > 0, A != C, false)}.count"),
		("SharedReferenceOperator", Dags + "range(1, 200).filter{if(n > 0, A == A, false)}.count"),
		("WideEqualOperator", Flat + "range(1, 50).filter{if(n > 0, W == X, false)}.count"),
		("WideMismatchOperator", Flat + "range(1, 50).filter{if(n > 0, W != Y, false)}.count"),
		("RepeatedNameDeep", Dags + "Same(v, v) = 1\nrange(1, 200).map{n * 0 + Same([A][0], [B][0])}.count"),
		("ClauseFamilyDeepMismatch", Dags + "F(v, v) = 1\nF(a, b) = 2\nrange(1, 200).map{n * 0 + F([A][0], [C][0])}.count"),
		("FlatNumericEquality", "range(1, 20000).filter{n == 5000}.count"),
		("FlatBooleanEquality", "range(1, 20000).filter{(n > 5000) == true}.count"),
		("DeepSingletonOperator", "Box = [x]\nP = Box(1).repeat(2000)\nQ = Box(1).repeat(2000)\nrange(1, 50).filter{if(n > 0, P == Q, false)}.count"),
		("ClauseFamilyOrdinaryDispatch", "G(0) = 1\nG(k) = 2\nrange(1, 20000).map{G(n mod 2)}.count"),
		("ShortStringEquality", "range(1, 20000).filter{\"s{n mod 100}\" == \"s7\"}.count"),
		("LongStringEquality", "range(1, 200).filter{text(n mod 1 + 1) == text(2)}.count"),
		("LongStringDistinct", "distinct(range(1, 2000).map{text(n mod 2)}).count"),
		("FlatNumericContains", "range(1, 20000).contains(-1)"),
		("ShallowMixedDistinct", "distinct(range(1, 5000).map{[n mod 7, [n mod 3], \"x{n mod 5}\"]}).count"),
	];

	/// <summary>Parses and elaborates a scenario once; a failed parse is a benchmark configuration error.</summary>
	internal static Expr Prepare(string source)
	{
		var parsed = Parser.Parse(source, new RunOptions { HostOperations = Operations });
		if (parsed.HasErrors)
			throw new InvalidOperationException($"Benchmark scenario failed to parse: {string.Join("; ", parsed.Diagnostics)}");
		return new Expr.AlgorithmExpr(parsed.Root);
	}

	internal static Result Evaluate(Expr program)
	{
		var (result, _) = Evaluator.RunCountedObserved(program, hostOperations: Operations);
		if (result.IsError)
			throw new InvalidOperationException($"Benchmark scenario failed during evaluation: {result.Error}");
		return result.Value.Value;
	}
}

[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 5, iterationCount: 10)]
[Orderer(SummaryOrderPolicy.Declared)]
public class StructuralComparisonBenchmarks
{
	private Expr _program = null!;

	[ParamsSource(nameof(Scenarios))]
	public string Scenario { get; set; } = "";

	public static IEnumerable<string> Scenarios => StructuralComparisonScenarios.All.Select(static scenario => scenario.Name);

	[GlobalSetup]
	public void Setup()
		=> _program = StructuralComparisonScenarios.Prepare(
			StructuralComparisonScenarios.All.Single(scenario => scenario.Name == Scenario).Source);

	[Benchmark]
	public Result Evaluate() => StructuralComparisonScenarios.Evaluate(_program);
}

/// <summary>
/// The per-comparison cost of one evaluator-owned equality (<see cref="Result.EvaluatorValueEquals"/>)
/// against the context-free public comparer it must agree with, for the value shapes an ordinary
/// program compares: scalars and short strings must stay allocation-free and on the O(1) path. The
/// deep shapes (SEC-02-FU2) exercise the single-comparison walk: <c>Singleton</c> and <c>TailChain</c>
/// descend only through last children (no frame), <c>HeadChain</c> keeps one frame per level,
/// <c>Tree</c> is an independent binary tree, <c>Dag</c> two independent doubling DAGs; the
/// <c>Mismatch</c> variants differ only in their deepest (last) leaf.
/// </summary>
[MemoryDiagnoser]
[Orderer(SummaryOrderPolicy.Declared)]
public class EvaluatorValueEqualsBenchmarks
{
	private Result _left = null!;
	private Result _right = null!;
	private EvaluationBudget _budget = null!;

	[Params("Number", "NumberUnequal", "NaN", "Quantum", "Bool", "NumberVsBool", "SameReference", "ShortString",
		"FlatList16", "NestedList", "LongString", "Singleton", "SingletonMismatch", "TailChain", "HeadChain", "Tree", "TreeMismatch", "Dag")]
	public string Shape { get; set; } = "";

	[GlobalSetup]
	public void Setup()
	{
		(_left, _right) = Shape switch
		{
			"Number" => ((Result)new Result.Atom(42), (Result)new Result.Atom(42)),
			"NumberUnequal" => (new Result.Atom(42), new Result.Atom(43)),
			"NaN" => (new Result.Atom(System.Numerics.Decimal128.NaN), new Result.Atom(System.Numerics.Decimal128.NaN)),
			"Quantum" => (new Result.Atom(System.Numerics.Decimal128.Parse("1.5")), new Result.Atom(System.Numerics.Decimal128.Parse("1.50"))),
			"Bool" => (new Result.Bool(true), new Result.Bool(true)),
			"NumberVsBool" => (new Result.Atom(1), new Result.Bool(true)),
			"SameReference" => Twice(Flat(16)),
			"ShortString" => (new Result.Str("short text"), new Result.Str(new string("short text".ToCharArray()))),
			"FlatList16" => (Flat(16), Flat(16)),
			"NestedList" => (Nested(), Nested()),
			"LongString" => (new Result.Str(new string('k', 64_000)), new Result.Str(new string('k', 64_000))),
			"Singleton" => (Singleton(2_000, 1), Singleton(2_000, 1)),
			"SingletonMismatch" => (Singleton(2_000, 1), Singleton(2_000, 2)),
			"TailChain" => (TailChain(2_000), TailChain(2_000)),
			"HeadChain" => (HeadChain(2_000), HeadChain(2_000)),
			"Tree" => (Tree(11, 1), Tree(11, 1)),
			"TreeMismatch" => (Tree(11, 1), Tree(11, 2)),
			"Dag" => (Dag(40), Dag(40)),
			_ => throw new InvalidOperationException(Shape),
		};
		_budget = EvaluationBudget.Create(limits: null);

		static Result Flat(int width)
			=> Result.ListValue.TakeOwnership([.. Enumerable.Range(0, width).Select(static i => (Result)new Result.Atom(i))]);

		static (Result, Result) Twice(Result value) => (value, value);

		static Result List(params Result[] items) => Result.ListValue.TakeOwnership(items);

		static Result Singleton(int depth, int leaf)
		{
			Result node = new Result.Atom(leaf);
			for (var i = 0; i < depth; i++)
				node = List(node);
			return node;
		}

		static Result TailChain(int depth)
		{
			var node = List(new Result.Atom(1));
			for (var i = 0; i < depth; i++)
				node = List(new Result.Atom(i), node);
			return node;
		}

		static Result HeadChain(int depth)
		{
			var node = List(new Result.Atom(1));
			for (var i = 0; i < depth; i++)
				node = List(node, new Result.Atom(i));
			return node;
		}

		static Result Tree(int depth, int lastLeaf)
		{
			var counter = 0;
			return Build(depth, lastLeaf);

			Result Build(int level, int leaf)
				=> level == 0
					? List(new Result.Atom(counter++), new Result.Atom(leaf))
					: List(Build(level - 1, 0), Build(level - 1, leaf));
		}

		static Result Dag(int depth)
		{
			var node = List(new Result.Atom(1), new Result.Atom(2));
			for (var i = 0; i < depth; i++)
				node = List(node, node);
			return node;
		}

		static Result Nested()
			=> Result.ListValue.TakeOwnership([Flat(4), Result.SequenceValue.TakeOwnership([Flat(4), new Result.Str("leaf")])]);
	}

	[Benchmark(Baseline = true)]
	public bool PublicComparer() => Result.ValueComparer.Equals(_left, _right);

	[Benchmark]
	public bool EvaluatorComparison() => Result.EvaluatorValueEquals(_left, _right, _budget, observations: null).Value;
}
