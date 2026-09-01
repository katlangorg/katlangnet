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

	/// <summary>
	/// A wide flat calculation chain: count root properties, each referencing the
	/// previous one, plus one output row referencing the last. Every reference is
	/// resolved by <c>ElaboratedScopeLookup</c> against the root level, so before
	/// M18 the per-level linear scan made total lookup work quadratic in count.
	/// </summary>
	internal static string BuildWideLookupChainSource(int count)
	{
		var source = new StringBuilder();
		source.AppendLine("V0 = 1");
		for (var i = 1; i < count; i++)
			source.AppendLine($"V{i} = V{i - 1} + 1");
		source.AppendLine($"V{count - 1}");
		return source.ToString();
	}

	/// <summary>
	/// A wide flat scope plus count unresolved output-row references (one fresh
	/// name per row, promoted to root implicit parameters). Every miss walks the
	/// whole chain — root level and prelude — so before M18 each miss scanned
	/// every property list in full, and the near-miss suggestion machinery
	/// re-scanned the chain per gathered candidate name.
	/// </summary>
	internal static string BuildWideLookupMissSource(int count)
	{
		var source = new StringBuilder();
		for (var i = 0; i < count; i++)
			source.AppendLine($"V{i} = {i}");
		for (var i = 0; i < count; i++)
			source.AppendLine($"u{i}");
		return source.ToString();
	}

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

	internal static void AssertWideLookupChainShape(string source, int count)
	{
		var result = Parser.Parse(source);
		AssertParsesCleanly(result);
		var root = AssertUser(result.Root, "root");
		if (root.Properties.Count != count)
			throw new InvalidOperationException($"Lookup-chain benchmark expected {count} root properties, found {root.Properties.Count}.");
		if (root.Parameters.Count != 0)
			throw new InvalidOperationException("Lookup-chain benchmark unexpectedly promoted implicit parameters.");
		if (root.Output is not [Expr.Resolve { Name: var finalName }] || finalName != $"V{count - 1}")
			throw new InvalidOperationException("Lookup-chain benchmark lost its final written reference.");
		for (var i = 1; i < count; i++)
		{
			var value = AssertUser(root.Properties[i].Value, $"V{i}");
			if (value.Output is not [Expr.Binary { Left: Expr.Resolve { Name: var referencedName } }]
				|| referencedName != $"V{i - 1}")
			{
				throw new InvalidOperationException($"Lookup-chain benchmark V{i} no longer references V{i - 1} exactly once.");
			}
		}

		AssertLookupWorkObserved(source, expectedIndexBuilds: 1, expectedLevelVisits: 2L * count - 1);
	}

	internal static void AssertWideLookupMissShape(string source, int count)
	{
		var result = Parser.Parse(source);
		AssertParsesCleanly(result);
		var root = AssertUser(result.Root, "root");
		if (root.Properties.Count != count)
			throw new InvalidOperationException($"Lookup-miss benchmark expected {count} root properties, found {root.Properties.Count}.");
		if (root.Parameters.Count != count
			|| root.Parameters[0].Name != "u0"
			|| root.Parameters[count - 1].Name != $"u{count - 1}")
			throw new InvalidOperationException("Lookup-miss benchmark lost its implicit-parameter promotions.");
		if (root.Output.Count != count
			|| root.Output.OfType<Expr.Param>().Select(static parameter => parameter.Name)
				.Where(static name => name.StartsWith("u", StringComparison.Ordinal)).Distinct(StringComparer.Ordinal).Count() != count)
		{
			throw new InvalidOperationException("Lookup-miss benchmark no longer contains exactly the intended promoted references.");
		}

		AssertLookupWorkObserved(source, expectedIndexBuilds: 2, expectedLevelVisits: null);
	}

	private static void AssertLookupWorkObserved(
		string source,
		long expectedIndexBuilds,
		long? expectedLevelVisits)
	{
		var syntax = Parser.ParseSyntax(source);
		if (syntax.HasErrors)
			throw new InvalidOperationException("Lookup benchmark syntax parse unexpectedly failed.");
		var observations = new FrontEndTraversalObservations();
		var (_, diagnostics) = ParameterDetector.DetectPrevalidated(syntax.Root, null, observations);
		if (diagnostics.Any(diagnostic => diagnostic.Severity == DiagnosticSeverity.Error))
			throw new InvalidOperationException("Lookup benchmark parameter detection unexpectedly failed.");
		if (observations.LookupNameIndexBuilds != expectedIndexBuilds
			|| observations.LookupPropertyComparisons != 0
			|| observations.LookupOpenTargetResolutions != 0
			|| observations.LookupOpenMemberIndexBuilds != 0
			|| observations.LookupRootDiscoveryWalks != 0
			|| (expectedLevelVisits is { } visits
				? observations.LookupLevelVisits != visits
				: observations.LookupLevelVisits <= 0))
		{
			throw new InvalidOperationException(
				"Lookup benchmark no longer exercises the intended indexed substrate: "
				+ $"indexes={observations.LookupNameIndexBuilds}, linearComparisons={observations.LookupPropertyComparisons}, "
				+ $"openResolutions={observations.LookupOpenTargetResolutions}, openMemberIndexes={observations.LookupOpenMemberIndexBuilds}, "
				+ $"rootWalks={observations.LookupRootDiscoveryWalks}, levelVisits={observations.LookupLevelVisits}.");
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
/// Width scaling of front-end elaboration on lookup-heavy flat scopes — the workloads
/// where repeated per-level linear name scans dominated before M18. Chain resolves
/// every reference at the root level; Misses walks the full chain (root and prelude)
/// for every promoted implicit parameter.
/// </summary>
[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 3, iterationCount: 8)]
[Orderer(SummaryOrderPolicy.FastestToSlowest)]
public class FrontEndWideLookupBenchmarks
{
	private string chainSource = string.Empty;
	private string missSource = string.Empty;

	[Params(100, 200, 400, 800)]
	public int Width { get; set; }

	[GlobalSetup]
	public void Setup()
	{
		chainSource = FrontEndElaborationScenarios.BuildWideLookupChainSource(Width);
		FrontEndElaborationScenarios.AssertWideLookupChainShape(chainSource, Width);
		missSource = FrontEndElaborationScenarios.BuildWideLookupMissSource(Width);
		FrontEndElaborationScenarios.AssertWideLookupMissShape(missSource, Width);
	}

	[Benchmark]
	public ParseResult WideLookupChain() => Parser.Parse(chainSource);

	[Benchmark]
	public ParseResult WideLookupMisses() => Parser.Parse(missSource);
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
