using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>One tracked UTF-16 seed: a declared template plus the encoded payload.</summary>
internal sealed record Utf16Seed(
    string Origin,
    int LineNumber,
    Utf16TemplateKind DeclaredTemplate,
    byte[] Payload,
    string Description)
{
    public string Location => $"{Origin}:{LineNumber.ToString(CultureInfo.InvariantCulture)}";
}

/// <summary>
/// Reader for the tracked UTF-16 seed manifest.
///
/// <para>A UTF-16 seed is NOT a source file. Storing one as text would defeat the whole point:
/// an isolated surrogate has no UTF-8 form, so any encoder in the path — git's, an editor's,
/// <c>File.ReadAllText</c>'s — would rewrite it to U+FFFD and the seed would silently stop testing
/// what it names. The manifest is therefore pure ASCII and carries the PAYLOAD in hex; replay feeds
/// it to the same decoder the campaign uses.</para>
///
/// <code>
/// # comment
/// template=string-literal bytes=06 00 00 03 04 05 00 00 units=004F ... desc=isolated high surrogate
/// </code>
///
/// <para><c>template</c> is redundant on purpose: it is checked against the decoded template, so a
/// stale or mis-copied seed is reported instead of quietly replaying a different case. <c>units</c>
/// is optional and, where present, pins the EXACT code-unit sequence the payload must build — the
/// round-trip guard for the seeds whose whole point is one difficult code unit.</para>
/// </summary>
internal static class Utf16SeedFile
{
    /// <summary>Largest payload a tracked seed may carry.</summary>
    private const int MaxPayloadBytes = 128;

    internal static IReadOnlyList<Utf16Seed> Load(string path, List<string> problems)
    {
        ArgumentNullException.ThrowIfNull(path);
        ArgumentNullException.ThrowIfNull(problems);

        var seeds = new List<Utf16Seed>();
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

    internal static bool TryParse(
        string line, string origin, int lineNumber, out Utf16Seed seed, out string problem)
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

        var bytesText = ReadField(line, "bytes=", stopAtWhitespace: false, stopAtFields: ["units=", "desc="]);
        if (bytesText is null)
        {
            problem = "missing 'bytes=' field.";
            return false;
        }

        if (!TryParseHexBytes(bytesText, out var payload, out var hexProblem))
        {
            problem = hexProblem;
            return false;
        }

        var parameters = Utf16Decoder.Decode(payload);
        if (parameters.Template != declaredTemplate)
        {
            problem =
                $"declared template '{Utf16Tables.TemplateOf(declaredTemplate).Id}' does not match the template the " +
                $"payload decodes to ('{Utf16Tables.TemplateOf(parameters.Template).Id}').";
            return false;
        }

        var unitsText = ReadField(line, "units=", stopAtWhitespace: false, stopAtFields: ["desc="]);
        if (unitsText is not null)
        {
            var built = Utf16SourceBuilder.Build(parameters);
            var expected = unitsText.Replace(" ", "", StringComparison.Ordinal).ToUpperInvariant();
            var actual = built.HexUnits.Replace(" ", "", StringComparison.Ordinal).ToUpperInvariant();
            if (!string.Equals(expected, actual, StringComparison.Ordinal))
            {
                problem =
                    "'units=' does not match the code units the payload builds.\n" +
                    $"       declared: {expected}\n       built:    {actual}";
                return false;
            }
        }

        var description = ReadField(line, "desc=", stopAtWhitespace: false) ?? "";
        seed = new Utf16Seed(origin, lineNumber, declaredTemplate, payload, description);
        problem = "";
        return true;
    }

    internal static bool TryParseTemplateId(string id, out Utf16TemplateKind template)
    {
        for (var i = 0; i < Utf16Tables.Templates.Length; i++)
        {
            if (string.Equals(Utf16Tables.Templates[i].Id, id, StringComparison.Ordinal))
            {
                template = (Utf16TemplateKind)i;
                return true;
            }
        }

        template = default;
        return false;
    }

    private static string? ReadField(
        string line, string key, bool stopAtWhitespace, string[]? stopAtFields = null)
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

    /// <summary>Parses a hex payload (contiguous or whitespace-separated pairs).</summary>
    internal static bool TryParseHexBytes(string text, out byte[] payload, out string problem)
    {
        payload = [];
        var compact = text.Replace(" ", "", StringComparison.Ordinal).Replace("\t", "", StringComparison.Ordinal);

        if (compact.Length == 0)
        {
            problem = "'bytes=' is empty; a seed must carry at least one payload byte.";
            return false;
        }

        if (compact.Length % 2 != 0)
        {
            problem = $"'bytes=' has an odd number of hex digits ({compact.Length.ToString(CultureInfo.InvariantCulture)}).";
            return false;
        }

        if (compact.Length / 2 > MaxPayloadBytes)
        {
            problem = $"'bytes=' exceeds the {MaxPayloadBytes.ToString(CultureInfo.InvariantCulture)}-byte seed payload limit.";
            return false;
        }

        var bytes = new byte[compact.Length / 2];
        for (var i = 0; i < bytes.Length; i++)
        {
            if (!byte.TryParse(compact.AsSpan(i * 2, 2), NumberStyles.HexNumber, CultureInfo.InvariantCulture, out bytes[i]))
            {
                problem = $"'bytes=' contains a non-hex pair at position {(i * 2).ToString(CultureInfo.InvariantCulture)}.";
                return false;
            }
        }

        payload = bytes;
        problem = "";
        return true;
    }
}
