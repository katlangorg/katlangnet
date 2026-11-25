using System.Text.Json;

namespace KatLang.Tests.CodeLinks;

/// <summary>
/// One source and what the format's reference encoder made of it. <see cref="Status"/> is its
/// verdict (<c>ok</c>, <c>empty</c>, <c>sourceTooLong</c> or <c>payloadTooLong</c>), and
/// <see cref="Payload"/> the payload, also for <c>payloadTooLong</c>; it is empty for a
/// program that is never encoded (<c>empty</c> and <c>sourceTooLong</c>). <see cref="Url"/> is
/// the link a vector states, and <c>null</c> for a generated case.
/// </summary>
internal sealed record CodeLinkCase(string Name, string Source, string Status, string Payload, string? Url);

/// <summary>
/// The committed code-link encoder fixtures in <c>dotnet/tests/KatLang.Tests/CodeLinks/Fixtures/</c>
/// (see the README there): <c>code-link-vectors.json</c>, documented programs with their links,
/// and <c>code-link-cases.json</c>, 707 sources with the reference encoder's verdicts. Both were
/// made with the reference implementation of code-link format 1, outside this repository; they
/// are expectations, not observations of this repository's code, and no test regenerates them.
///
/// <para>This file is shared as source: the KatLang tests own it, and the CLI tests link it
/// (<c>KatLang.CLI.Tests.csproj</c>), so both read the same cases.</para>
/// </summary>
internal static class CodeLinkFixtures
{
    private static readonly Lazy<IReadOnlyList<CodeLinkCase>> s_vectors = new(LoadVectors);
    private static readonly Lazy<IReadOnlyList<CodeLinkCase>> s_generatedCases = new(LoadGeneratedCases);

    public static IReadOnlyList<CodeLinkCase> Vectors => s_vectors.Value;

    public static IReadOnlyList<CodeLinkCase> GeneratedCases => s_generatedCases.Value;

    public static CodeLinkCase Vector(string name) => Vectors.Single(vector => vector.Name == name);

    public static CodeLinkCase Generated(string name) => GeneratedCases.Single(@case => @case.Name == name);

    /// <summary>The case names, the theory data: a name is plain ASCII, where a source may not be.</summary>
    public static TheoryData<string> Names(IEnumerable<CodeLinkCase> cases)
    {
        var data = new TheoryData<string>();
        foreach (var @case in cases)
            data.Add(@case.Name);
        return data;
    }

    private static IReadOnlyList<CodeLinkCase> LoadVectors()
    {
        using var document = JsonDocument.Parse(File.ReadAllText(FixturePath("code-link-vectors.json")));
        return document.RootElement.GetProperty("vectors").EnumerateArray()
            .Select(vector => new CodeLinkCase(
                vector.GetProperty("name").GetString()!,
                vector.GetProperty("source").GetString()!,
                "ok",
                vector.GetProperty("payload").GetString()!,
                vector.GetProperty("url").GetString()!))
            .ToList();
    }

    private static IReadOnlyList<CodeLinkCase> LoadGeneratedCases()
    {
        using var document = JsonDocument.Parse(File.ReadAllText(FixturePath("code-link-cases.json")));
        var cases = new List<CodeLinkCase>();
        foreach (var element in document.RootElement.GetProperty("cases").EnumerateArray())
        {
            var name = element.GetProperty("name").GetString()!;
            var source = SourceOf(element);

            // The recorded length guards the reading of the three source forms itself.
            var recordedLength = element.GetProperty("sourceLength").GetInt32();
            if (source.Length != recordedLength)
            {
                throw new InvalidDataException(
                    $"Fixture case '{name}' reads back as {source.Length} code units, not the {recordedLength} it was generated with.");
            }

            cases.Add(new CodeLinkCase(
                name,
                source,
                element.GetProperty("status").GetString()!,
                element.TryGetProperty("payload", out var payload) ? payload.GetString()! : "",
                Url: null));
        }

        return cases;
    }

    /// <summary>
    /// The source a fixture element gives, in one of three forms: <c>source</c>, the text;
    /// <c>codeUnits</c>, its UTF-16 code units (for an unpaired surrogate, which a JSON string
    /// read by System.Text.Json cannot carry); or <c>repeat</c>, a text repeated a number of
    /// times and followed by an optional suffix (for the long sources at the source limit).
    /// </summary>
    internal static string SourceOf(JsonElement element)
    {
        if (element.TryGetProperty("source", out var source))
            return source.GetString()!;

        if (element.TryGetProperty("codeUnits", out var codeUnits))
            return CodeUnitsOf(codeUnits);

        var repeat = element.GetProperty("repeat");
        var text = repeat.GetProperty("text").GetString()!;
        var count = repeat.GetProperty("count").GetInt32();
        var suffix = repeat.TryGetProperty("suffix", out var tail) ? tail.GetString()! : "";
        return string.Concat(Enumerable.Repeat(text, count)) + suffix;
    }

    /// <summary>The string of the UTF-16 code units the JSON array <paramref name="codeUnits"/> lists.</summary>
    internal static string CodeUnitsOf(JsonElement codeUnits)
    {
        var units = new char[codeUnits.GetArrayLength()];
        var index = 0;
        foreach (var unit in codeUnits.EnumerateArray())
            units[index++] = checked((char)unit.GetInt32());
        return new string(units);
    }

    /// <summary>The path of a file in the fixtures directory of the repository this test assembly was built from.</summary>
    public static string FixturePath(string fileName)
        => Path.Combine(RepoRoot.Find(), "dotnet", "tests", "KatLang.Tests", "CodeLinks", "Fixtures", fileName);
}
