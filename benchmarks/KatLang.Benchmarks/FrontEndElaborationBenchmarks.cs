using System.Text;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Order;

namespace KatLang.Benchmarks;

/// <summary>
/// Shared scenario sources for the front-end elaboration benchmarks (M17 surfaces): the
/// complete public pipeline (<see cref="Parser.Parse(string)"/> — parameter detection,
/// implicit-argument resolution, property-exposure resolution) on parse-only workloads.
/// </summary>
internal static class FrontEndElaborationScenarios
{
	/// <summary>
	/// Depth nested brace algorithms; every level owns a parameter, two simple properties
	/// (one capturing the level parameter, so exposure summaries carry real content), and
	/// the next level as a nested property. Bodies end with an ordinary output row.
	/// Before M17 each level's property-dependency summary was recomputed once per
	/// ancestor level, so this shape amplifies the repeated-summary cost quadratically.
	/// </summary>
	internal static string BuildNestedChainSource(int depth)
	{
		var source = new StringBuilder();
		for (var level = 0; level < depth; level++)
		{
			source.AppendLine($"L{level}(x{level}) = {{");
			source.AppendLine($"A{level} = x{level} + 1");
			source.AppendLine($"B{level} = A{level} + 1");
		}

		source.AppendLine("1");
		for (var level = depth - 1; level >= 0; level--)
		{
			source.AppendLine($"B{level}");
			source.AppendLine("}");
		}

		source.AppendLine("L0(1)");
		return source.ToString();
	}

	/// <summary>
	/// A wide flat scope: count properties, each a small parameterized brace body with one
	/// nested local property, plus one output row referencing the last property. The
	/// implicit-argument resolver never consumes summary data, so before M17 this shape
	/// paid a dead summary walk over every property subtree at every algorithm level.
	/// </summary>
	internal static string BuildWidePropertiesSource(int count)
	{
		var source = new StringBuilder();
		for (var i = 0; i < count; i++)
		{
			source.AppendLine($"W{i}(y{i}) = {{");
			source.AppendLine($"Inner{i} = y{i} * 2");
			source.AppendLine($"Inner{i} + 1");
			source.AppendLine("}");
		}

		source.AppendLine($"W{count - 1}(3)");
		return source.ToString();
	}

	internal const string SmallProgramSource = """
		Base = 10
		Scale(x) = x * Base
		Scale(4) + Scale(5)
		""";

	internal static void AssertParsesCleanly(string source)
	{
		var result = Parser.Parse(source);
		if (result.HasErrors)
		{
			throw new InvalidOperationException(
				"Front-end benchmark scenario failed to parse: "
				+ string.Join("; ", result.Diagnostics.Select(d => d.Message)));
		}
	}

	internal static void AssertNestedChainShape(string source, int depth)
	{
		var result = Parser.Parse(source);
		AssertParsesCleanly(result);
		var owner = AssertUser(result.Root, "root");
		for (var level = 0; level < depth; level++)
		{
			var levelProperty = owner.Properties.Single(property => property.Name == $"L{level}");
			if (levelProperty.Exposure != PropertyExposure.Exported)
				throw new InvalidOperationException($"Nested benchmark L{level} was not exported.");

			owner = AssertUser(levelProperty.Value, $"L{level}");
			foreach (var localName in new[] { $"A{level}", $"B{level}" })
			{
				var local = owner.Properties.Single(property => property.Name == localName);
				if (local.Exposure != PropertyExposure.LocalOnlyCapturedAncestorParameters)
					throw new InvalidOperationException($"Nested benchmark {localName} lost its capture classification.");
			}
		}

		var syntax = Parser.ParseSyntax(source);
		if (syntax.HasErrors)
			throw new InvalidOperationException("Nested benchmark syntax parse unexpectedly failed.");
		var (detected, detectionDiagnostics) = ParameterDetector.DetectPrevalidated(syntax.Root);
		if (detectionDiagnostics.Any(diagnostic => diagnostic.Severity == DiagnosticSeverity.Error))
			throw new InvalidOperationException("Nested benchmark parameter detection unexpectedly failed.");
		var resolverObservations = new FrontEndTraversalObservations();
		var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, resolverObservations);
		if (resolverObservations.DependencySiblingExpansions != 2L * depth
			|| resolverObservations.DependencySeedExpansions != 0
			|| resolverObservations.DependencyAlgorithmSummaryComputations != 0)
		{
			throw new InvalidOperationException("Nested benchmark no longer exercises the expected order-only resolver work.");
		}

		var exposureObservations = new FrontEndTraversalObservations();
		PropertyExposureResolver.Resolve(resolved, exposureObservations);
		if (exposureObservations.DependencySeedExpansions != 2L * depth
			|| exposureObservations.DependencyAlgorithmSummaryComputations != 3L * depth)
		{
			throw new InvalidOperationException("Nested benchmark no longer exercises linear completed-summary work.");
		}
	}

	internal static void AssertWidePropertiesShape(string source, int count)
	{
		var result = Parser.Parse(source);
		AssertParsesCleanly(result);
		var root = AssertUser(result.Root, "root");
		if (root.Properties.Count != count)
			throw new InvalidOperationException($"Wide benchmark expected {count} root properties, found {root.Properties.Count}.");

		foreach (var property in root.Properties)
		{
			if (property.Exposure != PropertyExposure.Exported)
				throw new InvalidOperationException($"Wide benchmark property {property.Name} was not exported.");
			var value = AssertUser(property.Value, property.Name);
			var inner = value.Properties.Single();
			if (inner.Exposure != PropertyExposure.LocalOnlyCapturedAncestorParameters)
				throw new InvalidOperationException($"Wide benchmark property {property.Name} lost its nested capture.");
		}

		var syntax = Parser.ParseSyntax(source);
		if (syntax.HasErrors)
			throw new InvalidOperationException("Wide benchmark syntax parse unexpectedly failed.");
		var (detected, detectionDiagnostics) = ParameterDetector.DetectPrevalidated(syntax.Root);
		if (detectionDiagnostics.Any(diagnostic => diagnostic.Severity == DiagnosticSeverity.Error))
			throw new InvalidOperationException("Wide benchmark parameter detection unexpectedly failed.");
		var observations = new FrontEndTraversalObservations();
		ImplicitArgumentResolver.ResolvePrevalidated(detected, observations);
		if (observations.DependencySiblingExpansions <= 0)
			throw new InvalidOperationException("Wide benchmark no longer exercises dependency-order analysis.");
		if (observations.DependencySeedExpansions != 0 || observations.DependencyAlgorithmSummaryComputations != 0)
			throw new InvalidOperationException("Wide benchmark resolver path unexpectedly executed summary analysis.");
	}

	private static void AssertParsesCleanly(ParseResult result)
	{
		if (result.HasErrors)
		{
			throw new InvalidOperationException(
				"Front-end benchmark scenario failed to parse: "
				+ string.Join("; ", result.Diagnostics.Select(d => d.Message)));
		}
	}

	private static Algorithm.User AssertUser(Algorithm algorithm, string label)
		=> algorithm as Algorithm.User
			?? throw new InvalidOperationException($"Front-end benchmark {label} was not a User algorithm.");
}

/// <summary>
/// Depth scaling of front-end elaboration on the nested-algorithm chain — the workload
/// where repeated descendant-summary computation dominated before M17.
/// </summary>
[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 3, iterationCount: 8)]
[Orderer(SummaryOrderPolicy.FastestToSlowest)]
public class FrontEndNestedElaborationBenchmarks
{
	private string nestedChainSource = string.Empty;

	[Params(8, 16, 32, 64)]
	public int NestedDepth { get; set; }

	[GlobalSetup]
	public void Setup()
	{
		nestedChainSource = FrontEndElaborationScenarios.BuildNestedChainSource(NestedDepth);
		FrontEndElaborationScenarios.AssertNestedChainShape(nestedChainSource, NestedDepth);
	}

	[Benchmark]
	public ParseResult NestedChain() => Parser.Parse(nestedChainSource);
}

/// <summary>
/// Ordinary front-end elaboration workloads: a wide flat scope (resolver-heavy) and a
/// tiny representative program (guards against fixed memo/setup overhead regressions).
/// </summary>
[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 3, iterationCount: 8)]
[Orderer(SummaryOrderPolicy.FastestToSlowest)]
public class FrontEndOrdinaryElaborationBenchmarks
{
	private string widePropertiesSource = string.Empty;

	[GlobalSetup]
	public void Setup()
	{
		widePropertiesSource = FrontEndElaborationScenarios.BuildWidePropertiesSource(400);
		FrontEndElaborationScenarios.AssertWidePropertiesShape(widePropertiesSource, 400);
		FrontEndElaborationScenarios.AssertParsesCleanly(FrontEndElaborationScenarios.SmallProgramSource);
	}

	[Benchmark]
	public ParseResult WideProperties() => Parser.Parse(widePropertiesSource);

	[Benchmark]
	public ParseResult SmallProgram() => Parser.Parse(FrontEndElaborationScenarios.SmallProgramSource);
}
