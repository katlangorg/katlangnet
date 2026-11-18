using System.Text;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Order;
using KatLang.Formatting;

namespace KatLang.Benchmarks;

/// <summary>
/// The evaluated values the output-formatting benchmarks render, each produced once by a real
/// <see cref="KatLangEngine.Run(string)"/> of a KatLang program so the formatters see exactly what a host
/// formats.
/// </summary>
internal static class OutputFormattingScenarios
{
	/// <summary>
	/// The values, by name: a large flat list of integers; a large list of nested lists, three levels deep;
	/// and two lists of numbers whose canonical text is exactly the renderer's atom stack buffer
	/// (<c>1e63</c>, 64 UTF-16 code units, written from the buffer) and one code unit longer (<c>1e64</c>,
	/// 65 code units, the one fixed-point string fallback).
	/// </summary>
	internal static readonly string[] Values = ["FlatList", "NestedLists", "Numbers64", "Numbers65"];

	internal const int FlatItems = 20_000;
	internal const int NestedRows = 4_000;
	internal const int BoundaryItems = 2_000;

	internal static string Source(string value) => value switch
	{
		"FlatList" => $"range(1, {FlatItems})",
		"NestedLists" => $"Row(i) = [i, [i * 2, [i * 3, i + 0.5]]]\nrange(1, {NestedRows}).map(Row)",
		"Numbers64" => RepeatedLiteralList("1e63", BoundaryItems),
		"Numbers65" => RepeatedLiteralList("1e64", BoundaryItems),
		_ => throw new ArgumentOutOfRangeException(nameof(value), value, "Unknown output-formatting value."),
	};

	/// <summary>The canonical text length every number of a boundary value must have.</summary>
	internal static int? BoundaryLength(string value) => value switch
	{
		"Numbers64" => Rendering.ValueTextRenderer.AtomStackBufferLength,
		"Numbers65" => Rendering.ValueTextRenderer.AtomStackBufferLength + 1,
		_ => null,
	};

	private static string RepeatedLiteralList(string literal, int count)
	{
		var source = new StringBuilder("[");
		for (var i = 0; i < count; i++)
		{
			if (i > 0)
				source.Append(i % 20 == 0 ? ",\n" : ", ");
			source.Append(literal);
		}

		return source.Append(']').ToString();
	}

	/// <summary>
	/// Runs <paramref name="value"/>'s program and checks the result is the intended shape: a successful run
	/// whose one output is a list, whose numbers at the boundary have the expected canonical text length, and
	/// whose rendering by every built-in formatter stays inside the display limit.
	/// </summary>
	internal static RunResult.Success Evaluate(string value)
	{
		var source = Source(value);
		var result = KatLangEngine.Run(source) as RunResult.Success
			?? throw new InvalidOperationException($"Output-formatting value '{value}' did not run successfully.");
		if (result.Value is not Result.ListValue list)
			throw new InvalidOperationException($"Output-formatting value '{value}' is not a list.");

		if (BoundaryLength(value) is { } length)
		{
			if (list.Items.Count != BoundaryItems)
				throw new InvalidOperationException($"Output-formatting value '{value}' has {list.Items.Count} items.");
			foreach (var item in list.Items)
			{
				if (item is not Result.Atom(var number)
					|| Rendering.ValueTextRenderer.FormatAtom(number, result.DisplayOptions).Length != length)
				{
					throw new InvalidOperationException(
						$"Output-formatting value '{value}' holds a number whose canonical text is not {length} code units long.");
				}
			}
		}

		foreach (var formatter in OutputFormatters.All)
		{
			var rendering = formatter.RenderDisplay(result);
			if (rendering.LimitExceeded)
				throw new InvalidOperationException($"Output-formatting value '{value}' exceeds the display limit under '{formatter.Id}'.");
		}

		return result;
	}
}

/// <summary>
/// Rendering of large evaluated values by the three built-in output formatters (<c>exact</c>,
/// <c>readable</c>, <c>concise</c>; <see cref="OutputFormatters"/>), with allocated bytes per rendering.
/// The values (<see cref="OutputFormattingScenarios"/>) are a 20,000-integer flat list, 4,000 nested lists
/// three levels deep, and 2,000 numbers on each side of the 64-code-unit atom stack buffer: <c>Numbers64</c>
/// is written from the buffer, <c>Numbers65</c> takes the string fallback, so the pair shows that fallback's
/// cost. Each value is evaluated once in setup; only <see cref="OutputFormatter.Format"/> is measured.
/// </summary>
[MemoryDiagnoser]
[SimpleJob(launchCount: 1, warmupCount: 3, iterationCount: 8)]
[Orderer(SummaryOrderPolicy.Declared)]
public class OutputFormattingBenchmarks
{
	private OutputFormatter formatter = OutputFormatters.Exact;
	private RunResult result = null!;

	[Params("exact", "readable", "concise")]
	public string Formatter { get; set; } = "exact";

	[ParamsSource(nameof(ValueNames))]
	public string Value { get; set; } = "FlatList";

	public static IEnumerable<string> ValueNames => OutputFormattingScenarios.Values;

	[GlobalSetup]
	public void Setup()
	{
		if (!OutputFormatters.TryGet(Formatter, out var selected))
			throw new InvalidOperationException($"Unknown output formatter '{Formatter}'.");
		formatter = selected;
		result = OutputFormattingScenarios.Evaluate(Value);
	}

	[Benchmark]
	public string Format() => formatter.Format(result);
}
