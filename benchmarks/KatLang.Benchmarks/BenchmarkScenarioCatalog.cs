using System.Reflection;
using System.Numerics;

namespace KatLang.Benchmarks;

internal sealed class BenchmarkScenario
{
	public BenchmarkScenario(
		string id,
		string displayName,
		string description,
		string origin,
		string source,
		Decimal128[] expectedAtoms,
		Algorithm preparedRoot)
	{
		Id = id;
		DisplayName = displayName;
		Description = description;
		Origin = origin;
		Source = source;
		ExpectedAtoms = expectedAtoms;
		PreparedRoot = preparedRoot;
	}

	public string Id { get; }

	public string DisplayName { get; }

	public string Description { get; }

	public string Origin { get; }

	public string Source { get; }

	public Decimal128[] ExpectedAtoms { get; }

	public Algorithm PreparedRoot { get; }
}

internal static class BenchmarkScenarioCatalog
{
	private static readonly Lazy<BenchmarkScenario> RepeatedZeroArgPropertyReuseScenario =
		new(() => Load(
			id: "repeated-zero-arg-property-reuse",
			displayName: "Repeated zero-arg property reuse",
			description: "Repeated reuse of a single zero-argument property derived from the existing evaluator regression test.",
			origin: "tests/KatLang.Tests/EvaluatorTests.cs (Eval_RepeatedEligiblePropertyWithinSingleRun)",
			resourceName: "KatLang.Benchmarks.Scenarios.repeated-zero-arg-property-reuse.kat",
			expectedAtoms: [1200m]));

	private static readonly Lazy<BenchmarkScenario> ScalarHelperSumCallsScenario =
		new(() => Load(
			id: "scalar-helper-sum-calls",
			displayName: "Scalar helper sum calls",
			description: "A parameterized helper closes over a shared zero-arg sequence sum and is called with distinct scalar arguments.",
			origin: "User-provided benchmark case for repeated lexical helper calls over a shared sum.",
			resourceName: "KatLang.Benchmarks.Scenarios.scalar-helper-sum-calls.kat",
			expectedAtoms: [10103m]));

	private static readonly Lazy<BenchmarkScenario> NestedPropertyChainsScenario =
		new(() => Load(
			id: "nested-property-chains",
			displayName: "Nested property chains",
			description: "Repeated one-hop nested receiver property lookup across multiple contexts, matching KatLang's current exported dot-access surface.",
			origin: "tests/KatLang.Tests/EvaluatorTests.cs (Eval_Distinguishes_HigherOrderAlgorithmContexts)",
			resourceName: "KatLang.Benchmarks.Scenarios.nested-property-chains.kat",
			expectedAtoms: [69m]));

	private static readonly Lazy<BenchmarkScenario> SequenceHeavyBuiltinsScenario =
		new(() => Load(
			id: "sequence-heavy-builtins",
			displayName: "Sequence-heavy builtins",
			description: "A map/filter/reduce pipeline based on the tutorial's collection builtin examples.",
			origin: "tutorial.md (range, filter, map, reduce examples)",
			resourceName: "KatLang.Benchmarks.Scenarios.sequence-heavy-builtins.kat",
			expectedAtoms: [10746800m]));

	private static readonly Lazy<BenchmarkScenario> PropertyRichSharedSubcomputationsScenario =
		new(() => Load(
			id: "property-rich-shared-subcomputations",
			displayName: "Property-rich shared subcomputations",
			description: "Several dependent properties repeatedly reuse the same intermediate totals and counts.",
			origin: "Derived from the property reuse evaluator tests plus tutorial sequence builtin patterns.",
			resourceName: "KatLang.Benchmarks.Scenarios.property-rich-shared-subcomputations.kat",
			expectedAtoms: [163204m]));

	private static readonly Lazy<BenchmarkScenario> RealisticWhileCalculationScenario =
		new(() => Load(
			id: "realistic-while-calculation",
			displayName: "Realistic while calculation",
			description: "The existing sum-of-multiples loop benchmark exercises while, if, dot-call, and selection together.",
			origin: "tests/KatLang.Tests/EvaluatorTests.cs (Eval_While_DotCall_SumMultiplesOf3Or5)",
			resourceName: "KatLang.Benchmarks.Scenarios.realistic-while-calculation.kat",
			expectedAtoms: [233168m]));

	private static readonly Lazy<BenchmarkScenario> GcdWhileLoopScenario =
		new(() => Load(
			id: "gcd-while-loop",
			displayName: "GCD while loop",
			description: "A compact Euclidean GCD loop that repeatedly threads two state values and a continuation flag.",
			origin: "tests/KatLang.Tests/EvaluatorTests.cs (Eval_While_GcdDotCall_ProjectsFinalState)",
			resourceName: "KatLang.Benchmarks.Scenarios.gcd-while-loop.kat",
			expectedAtoms: [21m]));

	private static readonly Lazy<BenchmarkScenario> RepeatManyIterationsScenario =
		new(() => Load(
			id: "repeat-many-iterations",
			displayName: "Repeat many iterations",
			description: "A minimal repeat loop that isolates repeated state rebinding overhead across many iterations.",
			origin: "Stage 1 loop optimization benchmark case.",
			resourceName: "KatLang.Benchmarks.Scenarios.repeat-many-iterations.kat",
			expectedAtoms: [20000m]));

	private static readonly Lazy<BenchmarkScenario> NestedCapturedParentLoopScenario =
		new(() => Load(
			id: "nested-captured-parent-loop",
			displayName: "Nested captured parent loop",
			description: "A nested while step that mutates one state value while reading parent parameters and a sibling property.",
			origin: "tests/KatLang.Tests/EvaluatorTests.cs (Eval_While_NestedStepUsesMutableStateAndCapturedParentValues)",
			resourceName: "KatLang.Benchmarks.Scenarios.nested-captured-parent-loop.kat",
			expectedAtoms: [2493m]));

	private static readonly Lazy<BenchmarkScenario> MinimalRepeatLoopScenario =
		new(() => Load(
			id: "minimal-repeat-loop",
			displayName: "Minimal repeat loop",
			description: "The exact one-million-iteration repeat loop used to measure Stage 2 slot-bound expression planning.",
			origin: "Stage 2 loop optimization benchmark case.",
			resourceName: "KatLang.Benchmarks.Scenarios.minimal-repeat-loop.kat",
			expectedAtoms: [1000002m]));

	private static readonly Lazy<BenchmarkScenario> MinimalWhileLoopScenario =
		new(() => Load(
			id: "minimal-while-loop",
			displayName: "Minimal while loop",
			description: "The exact one-million-step while loop used to measure Stage 2 slot-bound expression planning.",
			origin: "Stage 2 loop optimization benchmark case.",
			resourceName: "KatLang.Benchmarks.Scenarios.minimal-while-loop.kat",
			expectedAtoms: [1000001m]));

	private static readonly Lazy<BenchmarkScenario> ArithmeticWhileLoopScenario =
		new(() => Load(
			id: "arithmetic-while-loop",
			displayName: "Arithmetic while loop",
			description: "A simple while loop whose continuation multiplies the state value before comparison.",
			origin: "Stage 2 loop optimization benchmark case.",
			resourceName: "KatLang.Benchmarks.Scenarios.arithmetic-while-loop.kat",
			expectedAtoms: [1001m]));

	private static readonly Lazy<BenchmarkScenario> CapturedParentLoopScenario =
		new(() => Load(
			id: "captured-parent-loop",
			displayName: "Captured parent loop",
			description: "A loop whose continuation compares against a captured parent parameter.",
			origin: "Stage 2 loop optimization benchmark case.",
			resourceName: "KatLang.Benchmarks.Scenarios.captured-parent-loop.kat",
			expectedAtoms: [1001m]));

	private static readonly Lazy<BenchmarkScenario> NestedRepeatedCallLoopScenario =
		new(() => Load(
			id: "nested-repeated-call-loop",
			displayName: "Nested repeated call loop",
			description: "An outer repeat loop that calls a small inner while loop on every iteration.",
			origin: "Stage 2 loop optimization benchmark case.",
			resourceName: "KatLang.Benchmarks.Scenarios.nested-repeated-call-loop.kat",
			expectedAtoms: [1010000m]));

	private static readonly Lazy<BenchmarkScenario> SquareFreeCountInlineLoopScenario =
		new(() => Load(
			id: "square-free-count-inline-loop",
			displayName: "Square-free count inline loop",
			description: "Square-free counting with the inner loop expression written inline.",
			origin: "Stage 3A loop optimization benchmark case.",
			resourceName: "KatLang.Benchmarks.Scenarios.square-free-count-inline-loop.kat",
			expectedAtoms: [6083m]));

	private static readonly Lazy<BenchmarkScenario> SquareFreeCountLocalTempLoop1000Scenario =
		new(() => Load(
			id: "square-free-count-local-temp-loop-1000",
			displayName: "Square-free count local temp loop 1000",
			description: "Square-free counting with manual repeat and a local K2 property at N=1000.",
			origin: "Stage S2 sequence pipeline comparison benchmark case.",
			resourceName: "KatLang.Benchmarks.Scenarios.square-free-count-local-temp-loop-1000.kat",
			expectedAtoms: [608m]));

	private static readonly Lazy<BenchmarkScenario> SquareFreeCountLocalTempLoopScenario =
		new(() => Load(
			id: "square-free-count-local-temp-loop",
			displayName: "Square-free count local temp loop",
			description: "Square-free counting with the inner loop using a local K2 property.",
			origin: "Stage 3B loop optimization benchmark case.",
			resourceName: "KatLang.Benchmarks.Scenarios.square-free-count-local-temp-loop.kat",
			expectedAtoms: [6083m]));

	private static readonly Lazy<BenchmarkScenario> SequenceFilterCountEvenRangeScenario =
		new(() => Load(
			id: "sequence-filter-count-even-range",
			displayName: "Sequence filter count over range",
			description: "Stage S2 sequence pipeline benchmark for direct range iteration through range(...).filter(IsEven).count at N=10000.",
			origin: "Stage S2 sequence pipeline optimization benchmark case.",
			resourceName: "KatLang.Benchmarks.Scenarios.sequence-filter-count-even-range.kat",
			expectedAtoms: [5000m]));

	private static readonly Lazy<BenchmarkScenario> SequenceSquareFreeFilterCount1000Scenario =
		new(() => Load(
			id: "sequence-square-free-filter-count-1000",
			displayName: "Sequence square-free filter count 1000",
			description: "Stage S2 sequence pipeline benchmark for direct range iteration through range(...).filter(IsSquareFree).count at N=1000.",
			origin: "Stage S2 sequence pipeline optimization benchmark case.",
			resourceName: "KatLang.Benchmarks.Scenarios.sequence-square-free-filter-count-1000.kat",
			expectedAtoms: [608m]));

	private static readonly Lazy<BenchmarkScenario> SequenceSquareFreeFilterCount10000Scenario =
		new(() => Load(
			id: "sequence-square-free-filter-count-10000",
			displayName: "Sequence square-free filter count 10000",
			description: "Stage S2 sequence pipeline benchmark for direct range iteration through range(...).filter(IsSquareFree).count at N=10000.",
			origin: "Stage S2 sequence pipeline optimization benchmark case.",
			resourceName: "KatLang.Benchmarks.Scenarios.sequence-square-free-filter-count-10000.kat",
			expectedAtoms: [6083m]));

	private static readonly Lazy<BenchmarkScenario> DispatchNonCandidateCallsScenario =
		new(() => Load(
			id: "dispatch-non-candidate-calls",
			displayName: "Dispatch non-candidate calls",
			description: "M15 sequence-pipeline dispatch benchmark: 100000 ordinary plain calls that are never pipeline candidates, so each iteration pays one recognition probe and nothing more.",
			origin: "M15 sequence pipeline dispatch benchmark case.",
			resourceName: "KatLang.Benchmarks.Scenarios.dispatch-non-candidate-calls.kat",
			expectedAtoms: [100000m]));

	private static readonly Lazy<BenchmarkScenario> DispatchNonCandidateDotCallsScenario =
		new(() => Load(
			id: "dispatch-non-candidate-dot-calls",
			displayName: "Dispatch non-candidate dot-calls",
			description: "M15 sequence-pipeline dispatch benchmark: 100000 ordinary dot-calls that are never pipeline candidates, so each iteration pays one recognition probe and nothing more.",
			origin: "M15 sequence pipeline dispatch benchmark case.",
			resourceName: "KatLang.Benchmarks.Scenarios.dispatch-non-candidate-dot-calls.kat",
			expectedAtoms: [100000m]));

	public static BenchmarkScenario RepeatedZeroArgPropertyReuse => RepeatedZeroArgPropertyReuseScenario.Value;

	public static BenchmarkScenario ScalarHelperSumCalls => ScalarHelperSumCallsScenario.Value;

	public static BenchmarkScenario NestedPropertyChains => NestedPropertyChainsScenario.Value;

	public static BenchmarkScenario SequenceHeavyBuiltins => SequenceHeavyBuiltinsScenario.Value;

	public static BenchmarkScenario PropertyRichSharedSubcomputations => PropertyRichSharedSubcomputationsScenario.Value;

	public static BenchmarkScenario RealisticWhileCalculation => RealisticWhileCalculationScenario.Value;

	public static BenchmarkScenario GcdWhileLoop => GcdWhileLoopScenario.Value;

	public static BenchmarkScenario RepeatManyIterations => RepeatManyIterationsScenario.Value;

	public static BenchmarkScenario NestedCapturedParentLoop => NestedCapturedParentLoopScenario.Value;

	public static BenchmarkScenario MinimalRepeatLoop => MinimalRepeatLoopScenario.Value;

	public static BenchmarkScenario MinimalWhileLoop => MinimalWhileLoopScenario.Value;

	public static BenchmarkScenario ArithmeticWhileLoop => ArithmeticWhileLoopScenario.Value;

	public static BenchmarkScenario CapturedParentLoop => CapturedParentLoopScenario.Value;

	public static BenchmarkScenario NestedRepeatedCallLoop => NestedRepeatedCallLoopScenario.Value;

	public static BenchmarkScenario SquareFreeCountInlineLoop => SquareFreeCountInlineLoopScenario.Value;

	public static BenchmarkScenario SquareFreeCountLocalTempLoop1000 => SquareFreeCountLocalTempLoop1000Scenario.Value;

	public static BenchmarkScenario SquareFreeCountLocalTempLoop => SquareFreeCountLocalTempLoopScenario.Value;

	public static BenchmarkScenario SequenceFilterCountEvenRange => SequenceFilterCountEvenRangeScenario.Value;

	public static BenchmarkScenario SequenceSquareFreeFilterCount1000 => SequenceSquareFreeFilterCount1000Scenario.Value;

	public static BenchmarkScenario SequenceSquareFreeFilterCount10000 => SequenceSquareFreeFilterCount10000Scenario.Value;

	public static BenchmarkScenario DispatchNonCandidateCalls => DispatchNonCandidateCallsScenario.Value;

	public static BenchmarkScenario DispatchNonCandidateDotCalls => DispatchNonCandidateDotCallsScenario.Value;

	private static BenchmarkScenario Load(
		string id,
		string displayName,
		string description,
		string origin,
		string resourceName,
		Decimal128[] expectedAtoms)
	{
		var source = ReadResourceText(resourceName);
		var parseResult = Parser.Parse(source);
		var parseErrors = parseResult.Diagnostics
			.Where(diagnostic => diagnostic.Severity == DiagnosticSeverity.Error)
			.Select(diagnostic => diagnostic.Message)
			.ToArray();

		if (parseErrors.Length > 0)
		{
			throw new InvalidOperationException(
				$"Benchmark scenario '{id}' failed to parse:{Environment.NewLine}{string.Join(Environment.NewLine, parseErrors)}");
		}

		IReadOnlyList<Decimal128> fullRunAtoms;
		try
		{
			fullRunAtoms = KatLangEngine.EvaluateToAtoms(source);
		}
		catch (KatLangException ex)
		{
			throw new InvalidOperationException($"Benchmark scenario '{id}' failed in KatLangEngine.", ex);
		}

		AssertExpectedAtoms(id, "parse+eval", expectedAtoms, fullRunAtoms);

		var preparedRun = Evaluator.RunFlat(new Expr.AlgorithmExpr(parseResult.Root));
		if (preparedRun.IsError)
		{
			throw new InvalidOperationException(
				$"Benchmark scenario '{id}' failed in prepared evaluation: {preparedRun.Error}");
		}

		AssertExpectedAtoms(id, "prepared eval", expectedAtoms, preparedRun.Value);

		return new BenchmarkScenario(
			id,
			displayName,
			description,
			origin,
			source,
			expectedAtoms,
			parseResult.Root);
	}

	private static void AssertExpectedAtoms(
		string id,
		string stage,
		IReadOnlyList<Decimal128> expectedAtoms,
		IReadOnlyList<Decimal128> actualAtoms)
	{
		if (expectedAtoms.SequenceEqual(actualAtoms))
		{
			return;
		}

		throw new InvalidOperationException(
			$"Benchmark scenario '{id}' produced unexpected atoms during {stage}. Expected [{string.Join(", ", expectedAtoms)}] but got [{string.Join(", ", actualAtoms)}].");
	}

	private static string ReadResourceText(string resourceName)
	{
		using var stream = Assembly.GetExecutingAssembly().GetManifestResourceStream(resourceName);
		if (stream is null)
		{
			throw new InvalidOperationException($"Embedded benchmark scenario resource '{resourceName}' was not found.");
		}

		using var reader = new StreamReader(stream);
		return reader.ReadToEnd();
	}
}
