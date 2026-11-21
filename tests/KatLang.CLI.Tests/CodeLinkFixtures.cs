using System.Text.Json;

namespace KatLang.CLI.Tests;

/// <summary>
/// One source and what katlang.org's encoder made of it. <see cref="Status"/> is the reference
/// encoder's verdict (<c>ok</c>, <c>empty</c> or <c>tooLong</c>), and <see cref="Payload"/> is
/// <c>LZString.compressToEncodedURIComponent(source)</c> whatever the verdict.
/// <see cref="Url"/> is the link a Playground vector states, and <c>null</c> for a generated case.
/// </summary>
internal sealed record CodeLinkCase(string Name, string Source, string Status, string Payload, string? Url);

/// <summary>
/// The committed code-link fixtures in <c>Fixtures/</c> (see the README there):
/// <c>code-link-vectors.json</c>, a byte-for-byte copy of the vectors katlangweb tests the
/// Playground's codec with (<c>KatLangWeb.Tests/Fixtures/code-link-vectors.json</c>, katlangweb
/// commit <c>9d9bce7</c>), and <c>code-link-cases.json</c>, sources encoded once by katlangweb's
/// reference encoder. Both are read from the repository, as the CLI tests read the README, and
/// both are expectations made outside this repository: no test regenerates them.
/// </summary>
internal static class CodeLinkFixtures
{
    private static readonly Lazy<IReadOnlyList<CodeLinkCase>> s_playgroundVectors = new(LoadPlaygroundVectors);
    private static readonly Lazy<IReadOnlyList<CodeLinkCase>> s_generatedCases = new(LoadGeneratedCases);

    public static IReadOnlyList<CodeLinkCase> PlaygroundVectors => s_playgroundVectors.Value;

    public static IReadOnlyList<CodeLinkCase> GeneratedCases => s_generatedCases.Value;

    public static CodeLinkCase PlaygroundVector(string name) => PlaygroundVectors.Single(vector => vector.Name == name);

    public static CodeLinkCase Generated(string name) => GeneratedCases.Single(@case => @case.Name == name);

    /// <summary>The case names, the theory data: a name is plain ASCII, where a source may not be.</summary>
    public static TheoryData<string> Names(IEnumerable<CodeLinkCase> cases)
    {
        var data = new TheoryData<string>();
        foreach (var @case in cases)
            data.Add(@case.Name);
        return data;
    }

    private static IReadOnlyList<CodeLinkCase> LoadPlaygroundVectors()
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
                element.GetProperty("payload").GetString()!,
                Url: null));
        }

        return cases;
    }

    /// <summary>
    /// The source a generated case gives, in one of three forms: <c>source</c>, the text;
    /// <c>codeUnits</c>, its UTF-16 code units (for an unpaired surrogate, which a JSON string
    /// read by System.Text.Json cannot carry); or <c>repeat</c>, a text repeated a number of
    /// times and followed by an optional suffix (for the long sources at the source limit).
    /// </summary>
    private static string SourceOf(JsonElement element)
    {
        if (element.TryGetProperty("source", out var source))
            return source.GetString()!;

        if (element.TryGetProperty("codeUnits", out var codeUnits))
        {
            var units = new char[codeUnits.GetArrayLength()];
            var index = 0;
            foreach (var unit in codeUnits.EnumerateArray())
                units[index++] = checked((char)unit.GetInt32());
            return new string(units);
        }

        var repeat = element.GetProperty("repeat");
        var text = repeat.GetProperty("text").GetString()!;
        var count = repeat.GetProperty("count").GetInt32();
        var suffix = repeat.TryGetProperty("suffix", out var tail) ? tail.GetString()! : "";
        return string.Concat(Enumerable.Repeat(text, count)) + suffix;
    }

    private static string FixturePath(string fileName)
    {
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory is not null && !File.Exists(Path.Combine(directory.FullName, "KatLang.slnx")))
            directory = directory.Parent;

        if (directory is null)
            throw new DirectoryNotFoundException("The repository root (KatLang.slnx) was not found above the test assembly.");

        return Path.Combine(directory.FullName, "tests", "KatLang.CLI.Tests", "Fixtures", fileName);
    }
}
