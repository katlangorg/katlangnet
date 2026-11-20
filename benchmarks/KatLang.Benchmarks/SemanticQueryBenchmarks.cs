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

	/// <summary>
	/// A document of the same length in which one name is most of the sites: <see cref="Blocks"/> times 32
	/// lines of <c>D{i}(v) = v + v + v + v + v + v</c>, then one output row. The parameter <c>v</c> is 7 of
	/// every 8 identifier sites and half of the declarations.
	/// </summary>
	internal static string DenseSource(int blocks)
	{
		var source = new StringBuilder();
		for (var i = 0; i < blocks * 32; i++)
			source.Append($"D{i}(v) = v + v + v + v + v + v\n");
		return source.Append("D0(1)\n").ToString();
	}
}

/// <summary>
/// Editor semantic queries (<see cref="SemanticModel"/>) on generated documents of 129, 1,281 and
/// 12,801 lines (<see cref="SemanticQueryScenarios"/>): <c>Parse</c> (<see cref="Parser.Parse(string)"/>,
/// the whole front end), <c>Build</c> (<see cref="SemanticModelBuilder.Build(ParseResult)"/> of the parsed
/// document), and the query kinds, each a fixed batch so that every size reports per-query time and bytes:
/// <c>Hover</c> (<see cref="SemanticModel.FindPropertyAt"/> and the property's display signature) and
/// <c>Definition</c> (<see cref="SemanticModel.FindResolutionAt"/>) at <see cref="PositionQueries"/>
/// identifier sites spread over the document, <c>Completion</c>
/// (<see cref="SemanticModel.GetVisibleSymbolsAt"/>) at <see cref="CompletionQueries"/> of them, and
/// <see cref="NameQueries"/> name queries, each <see cref="SemanticModel.FindResolutions"/> plus
/// <see cref="SemanticModel.FindDeclarations"/> of one name: <c>Names</c> for declared names spread over
/// the document, then by result shape <c>NamesEmpty</c> (absent names), <c>NamesSparse</c> (names declared
/// once with at most four sites), <c>NamesDuplicate</c> (the names every block declares again, whose
/// results grow with the document) and <c>NamesDense</c> (the name that is 7 of every 8 sites of
/// <see cref="SemanticQueryScenarios.DenseSource"/>). Hover and definition binary-search the sites, and
/// completion binary-searches the scope regions. The name queries repeat on one model, so they measure its
/// name index after the first call built it. <c>Rewrap</c> puts the model's own parts in a new model, which
/// has no name index, and <c>RewrapAndIndex</c> adds the first name queries, which build both indexes: the
/// difference is the index build, and its allocated bytes are about what the model then keeps.
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
	private SemanticModel denseModel = null!;
	private SourcePosition[] positions = [];
	private SourcePosition[] completionPositions = [];
	private string[] names = [];
	private string[] emptyNames = [];
	private string[] sparseNames = [];
	private string[] duplicateNames = [];
	private string[] denseNames = [];
	private Dictionary<DeclarationOccurrence, PropertyInfo> propertiesByDeclaration = new();

	[ParamsSource(nameof(SizeNames))]
	public string Size { get; set; } = "small";

	public static IEnumerable<string> SizeNames => SemanticQueryScenarios.Sizes;

	[GlobalSetup]
	public void Setup()
	{
		source = SemanticQueryScenarios.Source(SemanticQueryScenarios.Blocks(Size));
		parsed = ParseValid(source);
		model = SemanticModelBuilder.Build(parsed);
		var sites = model.IdentifierResolutions.Select(r => r.Occurrence.Span.Start).ToArray();
		var declared = model.Declarations.Select(d => d.Name).Distinct(StringComparer.Ordinal).ToArray();
		if (sites.Length == 0 || declared.Length == 0)
			throw new InvalidOperationException("Semantic-query benchmark document has no identifier sites or declarations.");

		positions = Spread(sites, PositionQueries);
		completionPositions = Spread(sites, CompletionQueries);
		names = Spread(declared, NameQueries);

		// Name queries by result shape. A name every block declares again is declared Blocks times.
		var siteCounts = model.IdentifierResolutions
			.GroupBy(r => r.Occurrence.Name, StringComparer.Ordinal)
			.ToDictionary(g => g.Key, g => g.Count(), StringComparer.Ordinal);
		var declarationCounts = model.Declarations
			.GroupBy(d => d.Name, StringComparer.Ordinal)
			.ToDictionary(g => g.Key, g => g.Count(), StringComparer.Ordinal);
		string[] Named(Func<string, bool> keep)
			=> declarationCounts.Keys.Where(keep).Order(StringComparer.Ordinal).ToArray();
		emptyNames = Enumerable.Range(0, NameQueries).Select(i => $"Missing{i}").ToArray();
		sparseNames = Spread(Named(name => declarationCounts[name] == 1 && siteCounts[name] <= 4), NameQueries);
		duplicateNames = Spread(Named(name => declarationCounts[name] == SemanticQueryScenarios.Blocks(Size)), NameQueries);
		propertiesByDeclaration = new Dictionary<DeclarationOccurrence, PropertyInfo>(ReferenceEqualityComparer.Instance);
		foreach (var declaration in model.Declarations)
		{
			if (model.FindPropertyByDeclaration(declaration) is { } property)
				propertiesByDeclaration[declaration] = property;
		}

		// Every query kind must find something, or it would measure only misses; NamesEmpty must find nothing.
		if (Hover() == 0 || Definition() == 0 || Completion() == 0 || Names() == 0 || NamesSparse() == 0 || NamesDuplicate() == 0)
			throw new InvalidOperationException("A semantic-query benchmark batch found nothing.");
		if (NamesEmpty() != 0)
			throw new InvalidOperationException("The absent-name batch found something.");
		if (RewrapAndIndex() != 0 || Rewrap().IdentifierResolutions.Count != sites.Length)
			throw new InvalidOperationException("The rewrapped model differs from the built one.");
	}

	[GlobalSetup(Target = nameof(NamesDense))]
	public void DenseSetup()
	{
		denseModel = SemanticModelBuilder.Build(ParseValid(SemanticQueryScenarios.DenseSource(SemanticQueryScenarios.Blocks(Size))));
		denseNames = Enumerable.Repeat("v", NameQueries).ToArray();
		if (NamesDense() < NameQueries * (denseModel.IdentifierResolutions.Count / 2))
			throw new InvalidOperationException("The dense batch found fewer than half of the sites.");
	}

	private static ParseResult ParseValid(string text)
	{
		var result = Parser.Parse(text);
		if (result.HasErrors)
		{
			throw new InvalidOperationException(
				"Semantic-query benchmark document failed to parse: "
				+ string.Join("; ", result.Diagnostics.Take(5).Select(d => d.Message)));
		}

		return result;
	}

	/// <summary><paramref name="count"/> items evenly spread over <paramref name="items"/>, cycling when there are fewer.</summary>
	private static T[] Spread<T>(T[] items, int count)
	{
		if (items.Length == 0)
			throw new InvalidOperationException("A semantic-query benchmark batch has no candidates.");

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
	public int Names() => NameBatch(model, names);

	[Benchmark(OperationsPerInvoke = NameQueries)]
	public int NamesEmpty() => NameBatch(model, emptyNames);

	[Benchmark(OperationsPerInvoke = NameQueries)]
	public int NamesSparse() => NameBatch(model, sparseNames);

	[Benchmark(OperationsPerInvoke = NameQueries)]
	public int NamesDuplicate() => NameBatch(model, duplicateNames);

	[Benchmark(OperationsPerInvoke = NameQueries)]
	public int NamesDense() => NameBatch(denseModel, denseNames);

	private static int NameBatch(SemanticModel queried, string[] batch)
	{
		var found = 0;
		foreach (var name in batch)
			found += queried.FindResolutions(name).Count + queried.FindDeclarations(name).Count;
		return found;
	}

	/// <summary>The built model's parts in a new model, which has no name index yet.</summary>
	[Benchmark]
	public SemanticModel Rewrap()
		=> new(
			model.Root,
			model.IdentifierOccurrences,
			model.Declarations,
			model.IdentifierResolutions,
			model.PropertyInfos,
			propertiesByDeclaration,
			model.ScopeVisibilities)
		{
			PreludeSymbols = model.PreludeSymbols,
		};

	/// <summary><see cref="Rewrap"/> and the new model's first name queries, which build its two name indexes.</summary>
	[Benchmark]
	public int RewrapAndIndex()
	{
		var fresh = Rewrap();
		return fresh.FindResolutions("Missing").Count + fresh.FindDeclarations("Missing").Count;
	}
}
