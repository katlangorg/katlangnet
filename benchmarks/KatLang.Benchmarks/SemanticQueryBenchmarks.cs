using System.Text;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Order;
using KatLang.Semantics;

namespace KatLang.Benchmarks;

/// <summary>
/// Generated editor documents for the semantic-query benchmarks. One block declares a library with public
/// members, a nested member and a parameterized member, an alias and an alias chain, a body that opens the
/// library, a clause family, an implicit-parameter formula, a three-level nested body and a callback row, so
/// every query kind meets opened, aliased, nested, clause and builtin references. The document repeats the
/// block <see cref="Blocks"/> times (32 lines each), then adds one output row.
/// </summary>
internal static class SemanticQueryScenarios
{
	internal static readonly string[] Sizes = ["small", "medium", "large"];

	internal static int Blocks(string size) => size switch
	{
		"small" => 4,
		"medium" => 40,
		"large" => 400,
		_ => throw new ArgumentOutOfRangeException(nameof(size), size, "Unknown semantic-query document size."),
	};

	internal static string Source(int blocks)
	{
		var source = new StringBuilder();
		for (var i = 0; i < blocks; i++)
		{
			source.Append($"Lib{i} = {{\n");
			source.Append($"    public Size{i} = {i}\n");
			source.Append($"    public Area{i}(w, h) = w * h + Size{i}\n");
			source.Append($"    Helper{i} = Size{i} * 2\n");
			source.Append($"    public Inner{i} = {{\n        public Deep{i} = Helper{i} + 1\n    }}\n");
			source.Append("}\n");
			source.Append($"Alias{i} = Lib{i}\n");
			source.Append($"Chain{i} = Alias{i}\n");
			source.Append($"Use{i} = {{\n");
			source.Append($"    open Lib{i}\n");
			source.Append($"    Local{i} = Area{i}(2, 3) + Size{i}\n");
			source.Append($"    Shadow = Local{i} * 2\n");
			source.Append($"    Local{i} + Chain{i}.Helper{i} + Alias{i}.Inner{i}.Deep{i} + Shadow\n");
			source.Append("}\n");
			source.Append($"Speed{i}(x) = x + Use{i} + Angle{i}\n");
			source.Append($"Angle{i} = Lib{i}.Size{i} * Math.Pi + sin(1)\n");
			source.Append($"Clause{i}(0) = 1\n");
			source.Append($"Clause{i}(n) = n * 2\n");
			source.Append($"Imp{i} = a + b * Speed{i}(1)\n");
			source.Append($"Nest{i} = {{\n    L1 = {{\n        L2 = {{\n            V = Imp{i}(1, 2) + Clause{i}(3)\n            V\n        }}\n        L2 + 1\n    }}\n    L1\n}}\n");
			source.Append($"Rows{i} = range(1, 3).map(Speed{i}).sum + Nest{i}\n");
		}

		return source.Append("Rows0\n").ToString();
	}
}

/// <summary>
/// Editor semantic queries (<see cref="SemanticModel"/>) on generated documents of 129, 1,281 and
/// 12,801 lines (<see cref="SemanticQueryScenarios"/>): <c>Parse</c> (<see cref="Parser.Parse(string)"/>,
/// the whole front end), <c>Build</c> (<see cref="SemanticModelBuilder.Build(ParseResult)"/> of the parsed
/// document), and four query kinds, each a fixed batch so that every size reports per-query time and bytes:
/// <c>Hover</c> (<see cref="SemanticModel.FindPropertyAt"/> and the property's display signature) and
/// <c>Definition</c> (<see cref="SemanticModel.FindResolutionAt"/>) at <see cref="PositionQueries"/>
/// identifier sites spread over the document, <c>Completion</c>
/// (<see cref="SemanticModel.GetVisibleSymbolsAt"/>) at <see cref="CompletionQueries"/> of them, and
/// <c>Names</c> (<see cref="SemanticModel.FindResolutions"/> and <see cref="SemanticModel.FindDeclarations"/>)
/// for <see cref="NameQueries"/> declared names. Hover and definition are binary searches over the sites;
/// completion and the name queries still scan, so their per-query cost grows with the document.
/// </summary>
[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 3, iterationCount: 8)]
[Orderer(SummaryOrderPolicy.Declared)]
public class SemanticQueryBenchmarks
{
	public const int PositionQueries = 4_096;
	public const int CompletionQueries = 256;
	public const int NameQueries = 64;

	private string source = string.Empty;
	private ParseResult parsed = null!;
	private SemanticModel model = null!;
	private SourcePosition[] positions = [];
	private SourcePosition[] completionPositions = [];
	private string[] names = [];

	[ParamsSource(nameof(SizeNames))]
	public string Size { get; set; } = "small";

	public static IEnumerable<string> SizeNames => SemanticQueryScenarios.Sizes;

	[GlobalSetup]
	public void Setup()
	{
		source = SemanticQueryScenarios.Source(SemanticQueryScenarios.Blocks(Size));
		parsed = Parser.Parse(source);
		if (parsed.HasErrors)
		{
			throw new InvalidOperationException(
				"Semantic-query benchmark document failed to parse: "
				+ string.Join("; ", parsed.Diagnostics.Take(5).Select(d => d.Message)));
		}

		model = SemanticModelBuilder.Build(parsed);
		var sites = model.IdentifierResolutions.Select(r => r.Occurrence.Span.Start).ToArray();
		var declared = model.Declarations.Select(d => d.Name).Distinct(StringComparer.Ordinal).ToArray();
		if (sites.Length == 0 || declared.Length == 0)
			throw new InvalidOperationException("Semantic-query benchmark document has no identifier sites or declarations.");

		positions = Spread(sites, PositionQueries);
		completionPositions = Spread(sites, CompletionQueries);
		names = Spread(declared, NameQueries);

		// Every query kind must find something, or it would measure only misses.
		if (Hover() == 0 || Definition() == 0 || Completion() == 0 || Names() == 0)
			throw new InvalidOperationException("A semantic-query benchmark batch found nothing.");
	}

	/// <summary><paramref name="count"/> items evenly spread over <paramref name="items"/>, cycling when there are fewer.</summary>
	private static T[] Spread<T>(T[] items, int count)
	{
		var spread = new T[count];
		for (var i = 0; i < count; i++)
			spread[i] = items[items.Length >= count ? (int)((long)i * items.Length / count) : i % items.Length];
		return spread;
	}

	[Benchmark]
	public ParseResult Parse() => Parser.Parse(source);

	[Benchmark]
	public SemanticModel Build() => SemanticModelBuilder.Build(parsed);

	[Benchmark(OperationsPerInvoke = PositionQueries)]
	public int Hover()
	{
		var found = 0;
		foreach (var position in positions)
		{
			if (model.FindPropertyAt(position) is { } property)
				found += property.DisplaySignature.Length;
		}

		return found;
	}

	[Benchmark(OperationsPerInvoke = PositionQueries)]
	public int Definition()
	{
		var found = 0;
		foreach (var position in positions)
		{
			if (model.FindResolutionAt(position)?.ResolvedDeclaration is { } declaration)
				found += declaration.Name.Length;
		}

		return found;
	}

	[Benchmark(OperationsPerInvoke = CompletionQueries)]
	public int Completion()
	{
		var found = 0;
		foreach (var position in completionPositions)
			found += model.GetVisibleSymbolsAt(position).Count;
		return found;
	}

	[Benchmark(OperationsPerInvoke = NameQueries)]
	public int Names()
	{
		var found = 0;
		foreach (var name in names)
			found += model.FindResolutions(name).Count + model.FindDeclarations(name).Count;
		return found;
	}
}
