using System.Reflection;

namespace KatLang.Benchmarks;

internal sealed class BenchmarkScenario
{
	public BenchmarkScenario(
		string id,
		string displayName,
		string description,
		string origin,
		string source,
		decimal[] expectedAtoms,
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

	public decimal[] ExpectedAtoms { get; }

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

	public static BenchmarkScenario RepeatedZeroArgPropertyReuse => RepeatedZeroArgPropertyReuseScenario.Value;

	public static BenchmarkScenario NestedPropertyChains => NestedPropertyChainsScenario.Value;

	public static BenchmarkScenario SequenceHeavyBuiltins => SequenceHeavyBuiltinsScenario.Value;

	public static BenchmarkScenario PropertyRichSharedSubcomputations => PropertyRichSharedSubcomputationsScenario.Value;

	public static BenchmarkScenario RealisticWhileCalculation => RealisticWhileCalculationScenario.Value;

	private static BenchmarkScenario Load(
		string id,
		string displayName,
		string description,
		string origin,
		string resourceName,
		decimal[] expectedAtoms)
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

		IReadOnlyList<decimal> fullRunAtoms;
		try
		{
			fullRunAtoms = KatLangEngine.EvaluateToAtoms(source);
		}
		catch (KatLangException ex)
		{
			throw new InvalidOperationException($"Benchmark scenario '{id}' failed in KatLangEngine.", ex);
		}

		AssertExpectedAtoms(id, "parse+eval", expectedAtoms, fullRunAtoms);

		var preparedRun = Evaluator.RunFlat(new Expr.Block(parseResult.Root));
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
		IReadOnlyList<decimal> expectedAtoms,
		IReadOnlyList<decimal> actualAtoms)
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