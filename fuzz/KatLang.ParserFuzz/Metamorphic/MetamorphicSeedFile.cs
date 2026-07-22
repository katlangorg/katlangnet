using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>One tracked metamorphic seed: a declared family plus the encoded parameters.</summary>
internal sealed record MetamorphicSeed(
    string Origin,
    int LineNumber,
    MetamorphicFamily DeclaredFamily,
    byte[] Payload,
    string Description)
{
    public string Location => $"{Origin}:{LineNumber.ToString(CultureInfo.InvariantCulture)}";
}

/// <summary>
/// Reader for the tracked metamorphic seed manifest.
///
/// <para>A metamorphic seed is NOT a source file — it is a template payload — so storing it as
/// KatLang text would duplicate two programs that the template regenerates deterministically.
/// The manifest keeps one reviewable line per case:</para>
///
/// <code>
/// # comment
/// family=dotted-collection-call bytes=00 04 01 00 01 00 desc=cumulative budget exactly at the boundary
/// </code>
///
/// <para><c>bytes</c> is the fuzz payload replay feeds to the SAME decoder the campaign uses.
/// <c>family</c> is redundant metadata on purpose: it is checked against the decoded family, so
/// a stale or mis-copied seed is reported instead of silently replaying a different case.</para>
/// </summary>
internal static class MetamorphicSeedFile
{
    /// <summary>Largest payload a tracked seed may carry (a decoded case needs six bytes).</summary>
    private const int MaxPayloadBytes = 256;

    /// <summary>
    /// Reads every seed in <paramref name="path"/>. Malformed lines are reported into
    /// <paramref name="problems"/> with their exact location and are not returned.
    /// </summary>
    internal static IReadOnlyList<MetamorphicSeed> Load(string path, List<string> problems)
    {
        ArgumentNullException.ThrowIfNull(path);
        ArgumentNullException.ThrowIfNull(problems);

        var seeds = new List<MetamorphicSeed>();
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

    /// <summary>Parses one manifest line. Returns false with a specific reason for anything malformed.</summary>
    internal static bool TryParse(
        string line, string origin, int lineNumber, out MetamorphicSeed seed, out string problem)
    {
        seed = null!;

        var familyText = ReadField(line, "family=", stopAtWhitespace: true);
        if (familyText is null)
        {
            problem = "missing 'family=' field.";
            return false;
        }

        if (!MetamorphicCase.TryParseFamilyId(familyText, out var declaredFamily))
        {
            problem = $"unknown relation family '{familyText}'.";
            return false;
        }

        var bytesText = ReadField(line, "bytes=", stopAtWhitespace: false, stopAtField: "desc=");
        if (bytesText is null)
        {
            problem = "missing 'bytes=' field.";
            return false;
        }

        if (!TryParseHex(bytesText, out var payload, out var hexProblem))
        {
            problem = hexProblem;
            return false;
        }

        var decoded = MetamorphicDecoder.Decode(payload);
        if (decoded.Family != declaredFamily)
        {
            problem =
                $"declared family '{MetamorphicCase.FamilyIdOf(declaredFamily)}' does not match the family the " +
                $"payload decodes to ('{MetamorphicCase.FamilyIdOf(decoded.Family)}').";
            return false;
        }

        var description = ReadField(line, "desc=", stopAtWhitespace: false) ?? "";
        seed = new MetamorphicSeed(origin, lineNumber, declaredFamily, payload, description);
        problem = "";
        return true;
    }

    private static string? ReadField(string line, string key, bool stopAtWhitespace, string? stopAtField = null)
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
        else if (stopAtField is not null)
        {
            var next = line.IndexOf(stopAtField, from, StringComparison.Ordinal);
            if (next >= 0) to = next;
        }

        return line[from..to].Trim();
    }

    /// <summary>Parses a hex payload (contiguous or whitespace-separated pairs).</summary>
    internal static bool TryParseHex(string text, out byte[] payload, out string problem)
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
