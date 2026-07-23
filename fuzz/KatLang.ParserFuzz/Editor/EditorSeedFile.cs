using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>One tracked editor seed: a declared template plus the encoded payload.</summary>
internal sealed record EditorSeed(
    string Origin,
    int LineNumber,
    EditorTemplateKind DeclaredTemplate,
    byte[] Payload,
    string Description)
{
    public string Location => $"{Origin}:{LineNumber.ToString(CultureInfo.InvariantCulture)}";
}

/// <summary>
/// Reader for the tracked editor seed manifest.
///
/// <para>An editor seed is NOT a source file: the payload selects a template plus difficult UTF-16
/// code units, and storing the built source as text would rewrite an isolated surrogate to U+FFFD.
/// The manifest is pure ASCII and carries the PAYLOAD in hex; replay feeds it to the same decoder the
/// campaign uses.</para>
///
/// <code>
/// # comment
/// template=dotted-call bytes=0E 01 04 05 00 00 00 06 00 00 00 00 00 desc=isolated high surrogate at dot member
/// </code>
///
/// <para><c>template</c> is redundant on purpose: it is checked against the decoded template, so a
/// stale or mis-copied seed is reported instead of quietly replaying a different case.</para>
/// </summary>
internal static class EditorSeedFile
{
    private const int MaxPayloadBytes = 64;

    internal static IReadOnlyList<EditorSeed> Load(string path, List<string> problems)
    {
        ArgumentNullException.ThrowIfNull(path);
        ArgumentNullException.ThrowIfNull(problems);

        var seeds = new List<EditorSeed>();
        string[] lines;
        try
        {
            lines = File.ReadAllLines(path);
        }
        catch (Exception exception)
        {
            problems.Add($"{path}: could not read seed file ({exception.GetType().Name}: {exception.Message}).");
            return seeds;
        }

        var origin = Path.GetFileName(path);
        for (var index = 0; index < lines.Length; index++)
        {
            var line = lines[index].Trim();
            if (line.Length == 0 || line.StartsWith('#')) continue;

            if (TryParse(line, origin, index + 1, out var seed, out var problem)) seeds.Add(seed);
            else problems.Add($"{origin}:{(index + 1).ToString(CultureInfo.InvariantCulture)}: {problem}");
        }

        return seeds;
    }

    internal static bool TryParse(string line, string origin, int lineNumber, out EditorSeed seed, out string problem)
    {
        seed = null!;

        var templateText = ReadField(line, "template=", stopAtWhitespace: true);
        if (templateText is null)
        {
            problem = "missing 'template=' field.";
            return false;
        }

        if (!TryParseTemplateId(templateText, out var declaredTemplate))
        {
            problem = $"unknown template id '{templateText}'.";
            return false;
        }

        var bytesText = ReadField(line, "bytes=", stopAtWhitespace: false, stopAtFields: ["desc="]);
        if (bytesText is null)
        {
            problem = "missing 'bytes=' field.";
            return false;
        }

        if (!Utf16SeedFile.TryParseHexBytes(bytesText, out var payload, out var hexProblem))
        {
            problem = hexProblem;
            return false;
        }

        if (payload.Length > MaxPayloadBytes)
        {
            problem = $"'bytes=' exceeds the {MaxPayloadBytes.ToString(CultureInfo.InvariantCulture)}-byte seed payload limit.";
            return false;
        }

        var parameters = EditorDecoder.Decode(payload);
        if (parameters.Template != declaredTemplate)
        {
            problem =
                $"declared template '{EditorTables.TemplateOf(declaredTemplate).Id}' does not match the template the " +
                $"payload decodes to ('{EditorTables.TemplateOf(parameters.Template).Id}').";
            return false;
        }

        var description = ReadField(line, "desc=", stopAtWhitespace: false) ?? "";
        seed = new EditorSeed(origin, lineNumber, declaredTemplate, payload, description);
        problem = "";
        return true;
    }

    internal static bool TryParseTemplateId(string id, out EditorTemplateKind template)
    {
        for (var i = 0; i < EditorTables.Templates.Length; i++)
        {
            if (string.Equals(EditorTables.Templates[i].Id, id, StringComparison.Ordinal))
            {
                template = (EditorTemplateKind)i;
                return true;
            }
        }

        template = default;
        return false;
    }

    private static string? ReadField(string line, string key, bool stopAtWhitespace, string[]? stopAtFields = null)
    {
        var start = line.IndexOf(key, StringComparison.Ordinal);
        if (start < 0) return null;

        var from = start + key.Length;
        var to = line.Length;

        if (stopAtWhitespace)
        {
            var whitespace = line.AsSpan(from).IndexOfAny(' ', '\t');
            if (whitespace >= 0) to = from + whitespace;
        }
        else if (stopAtFields is not null)
        {
            foreach (var stop in stopAtFields)
            {
                var next = line.IndexOf(stop, from, StringComparison.Ordinal);
                if (next >= 0 && next < to) to = next;
            }
        }

        return line[from..to].Trim();
    }
}
