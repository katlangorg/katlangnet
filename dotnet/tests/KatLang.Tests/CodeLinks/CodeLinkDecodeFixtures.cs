using System.Security.Cryptography;
using System.Text.Json;

namespace KatLang.Tests.CodeLinks;

/// <summary>
/// What the format's reference decoder answered for one input: a refusal
/// (<see cref="Refusal"/>), or a program. The program is <see cref="Source"/>, or, for a long
/// one, its <see cref="SourceLength"/> and <see cref="SourceSha256"/> (the SHA-256, in
/// lowercase hexadecimal, of its UTF-16 code units, little-endian).
/// </summary>
internal sealed record CodeLinkVerdict(CodeLinkRefusal? Refusal, string? Source, int? SourceLength, string? SourceSha256)
{
    /// <summary>Whether <paramref name="source"/> is exactly the program this verdict states.</summary>
    public bool IsProgram(string source)
    {
        if (Refusal is not null)
            return false;

        if (Source is not null)
            return string.Equals(Source, source, StringComparison.Ordinal);

        if (SourceSha256 is null || SourceLength != source.Length)
            return false;

        // Code unit by code unit: an encoding would replace an unpaired surrogate.
        var bytes = new byte[source.Length * 2];
        for (var i = 0; i < source.Length; i++)
        {
            bytes[2 * i] = (byte)source[i];
            bytes[2 * i + 1] = (byte)(source[i] >> 8);
        }

        return string.Equals(Convert.ToHexStringLower(SHA256.HashData(bytes)), SourceSha256, StringComparison.Ordinal);
    }

    /// <summary>Why <paramref name="actual"/> is not this verdict, or <c>null</c> when it is.</summary>
    public string? Mismatch(CodeLinkDecoding actual) => actual switch
    {
        CodeLinkDecoding.Program program when IsProgram(program.Source) => null,
        CodeLinkDecoding.Program program => $"expected {this}, got a program of {program.Source.Length} code units",
        CodeLinkDecoding.Refused refused when refused.Reason == Refusal => null,
        CodeLinkDecoding.Refused refused => $"expected {this}, got the refusal {refused.Reason}",
    };

    public override string ToString() => Refusal is { } refusal
        ? $"the refusal {refusal}"
        : $"a program of {Source?.Length ?? SourceLength} code units";
}

/// <summary>A payload the oracle's edits start from: an encoder case, with its program.</summary>
internal sealed record CodeLinkDecodeBase(string Name, string Payload, string Source);

/// <summary>
/// One input of the decoder oracle: a payload of the format <see cref="Format"/>, or a link
/// (<see cref="IsLink"/>), with the reference's verdict. For a link, <see cref="LinkFormat"/>
/// and <see cref="LinkPayload"/> are what <see cref="CodeLink.TryGetPayload"/> gives, both
/// <c>null</c> when it is <c>false</c>.
/// </summary>
internal sealed record CodeLinkDecodeCase(
    string Name,
    string Kind,
    int Format,
    bool IsLink,
    string Input,
    int? LinkFormat,
    string? LinkPayload,
    CodeLinkVerdict Verdict);

/// <summary>
/// Proper prefixes of a base's payload: <see cref="Verdicts"/> has one letter for each prefix
/// length from 1 (<c>D</c> Damaged, <c>N</c> NotCanonical, <c>S</c> SourceTooLong, <c>K</c>
/// accepted, <c>.</c> not sampled), and <see cref="Accepted"/> the program of each prefix the
/// reference accepts, by prefix length.
/// </summary>
internal sealed record CodeLinkTruncations(CodeLinkDecodeBase Base, string Verdicts, IReadOnlyDictionary<int, CodeLinkVerdict> Accepted);

/// <summary>
/// The character at <see cref="At"/> of a base's payload replaced by the text <see cref="To"/>,
/// or deleted when that is <c>null</c>.
/// </summary>
internal sealed record CodeLinkMutation(int At, string? To, CodeLinkVerdict Verdict)
{
    public string Apply(string payload) => string.Concat(payload.AsSpan(0, At), To, payload.AsSpan(At + 1));
}

/// <summary>The edits of one base's payload.</summary>
internal sealed record CodeLinkMutations(CodeLinkDecodeBase Base, IReadOnlyList<CodeLinkMutation> Edits);

/// <summary>
/// The committed decoder oracle, <c>Fixtures/code-link-decode-cases.json</c> (see the README
/// there): inputs with the verdicts of the format's reference decoder, made once outside this
/// repository. It is an expectation, not an observation of this repository's code: no test
/// regenerates it. Its bases are cases of <c>code-link-cases.json</c>
/// (<see cref="CodeLinkFixtures"/>).
/// </summary>
internal static class CodeLinkDecodeFixtures
{
    private static readonly Lazy<Content> s_content = new(Load);

    public static IReadOnlyList<CodeLinkDecodeCase> Cases => s_content.Value.Cases;

    public static IReadOnlyList<CodeLinkTruncations> Truncations => s_content.Value.Truncations;

    public static IReadOnlyList<CodeLinkMutations> Mutations => s_content.Value.Mutations;

    /// <summary>The fixture's own count of its inputs by kind, with <c>truncations</c>, <c>mutations</c> and <c>total</c>.</summary>
    public static IReadOnlyDictionary<string, int> StatedCounts => s_content.Value.StatedCounts;

    public static CodeLinkDecodeCase Case(string name) => Cases.Single(@case => @case.Name == name);

    public static CodeLinkTruncations TruncationsOf(string baseName) => Truncations.Single(family => family.Base.Name == baseName);

    public static CodeLinkMutations MutationsOf(string baseName) => Mutations.Single(family => family.Base.Name == baseName);

    private sealed record Content(
        IReadOnlyList<CodeLinkDecodeCase> Cases,
        IReadOnlyList<CodeLinkTruncations> Truncations,
        IReadOnlyList<CodeLinkMutations> Mutations,
        IReadOnlyDictionary<string, int> StatedCounts);

    private static Content Load()
    {
        using var document = JsonDocument.Parse(File.ReadAllText(CodeLinkFixtures.FixturePath("code-link-decode-cases.json")));
        var root = document.RootElement;

        var bases = new Dictionary<string, CodeLinkDecodeBase>(StringComparer.Ordinal);
        foreach (var element in root.GetProperty("bases").EnumerateArray())
        {
            var name = element.GetProperty("name").GetString()!;
            var payload = element.GetProperty("payload").GetString()!;
            var @case = CodeLinkFixtures.Generated(name);
            if (!string.Equals(@case.Payload, payload, StringComparison.Ordinal))
                throw new InvalidDataException($"The base '{name}' does not have its encoder case's payload.");
            bases.Add(name, new CodeLinkDecodeBase(name, payload, @case.Source));
        }

        var truncations = root.GetProperty("truncations").EnumerateArray()
            .Select(element =>
            {
                var accepted = new Dictionary<int, CodeLinkVerdict>();
                foreach (var entry in element.GetProperty("accepted").EnumerateObject())
                    accepted.Add(int.Parse(entry.Name, System.Globalization.CultureInfo.InvariantCulture), Verdict(entry.Value));
                return new CodeLinkTruncations(bases[element.GetProperty("base").GetString()!], element.GetProperty("verdicts").GetString()!, accepted);
            })
            .ToList();

        var mutations = root.GetProperty("mutations").EnumerateArray()
            .Select(element => new CodeLinkMutations(
                bases[element.GetProperty("base").GetString()!],
                element.GetProperty("edits").EnumerateArray()
                    .Select(edit => new CodeLinkMutation(
                        edit.GetProperty("at").GetInt32(),
                        edit.GetProperty("to").ValueKind == JsonValueKind.Null ? null : edit.GetProperty("to").GetString()!,
                        Verdict(edit.GetProperty("verdict"))))
                    .ToList()))
            .ToList();

        var cases = root.GetProperty("cases").EnumerateArray()
            .Select(element =>
            {
                var isLink = element.TryGetProperty("isLink", out var link) && link.GetBoolean();
                var input = element.TryGetProperty("inputCodeUnits", out var units)
                    ? CodeLinkFixtures.CodeUnitsOf(units)
                    : element.GetProperty("input").GetString()!;
                int? linkFormat = null;
                string? linkPayload = null;
                if (isLink && element.GetProperty("linkPayload").ValueKind != JsonValueKind.Null)
                {
                    linkFormat = element.GetProperty("linkFormat").GetInt32();
                    linkPayload = element.GetProperty("linkPayload").GetString()!;
                }

                return new CodeLinkDecodeCase(
                    element.GetProperty("name").GetString()!,
                    element.GetProperty("kind").GetString()!,
                    isLink ? 0 : element.GetProperty("format").GetInt32(),
                    isLink,
                    input,
                    linkFormat,
                    linkPayload,
                    Verdict(element.GetProperty("verdict")));
            })
            .ToList();

        var counts = root.GetProperty("counts").EnumerateObject().ToDictionary(entry => entry.Name, entry => entry.Value.GetInt32(), StringComparer.Ordinal);
        return new Content(cases, truncations, mutations, counts);
    }

    private static CodeLinkVerdict Verdict(JsonElement element)
    {
        if (element.TryGetProperty("refused", out var refused))
            return new CodeLinkVerdict(Enum.Parse<CodeLinkRefusal>(refused.GetString()!), null, null, null);
        if (element.TryGetProperty("program", out var program))
            return new CodeLinkVerdict(null, program.GetString()!, null, null);
        if (element.TryGetProperty("programCodeUnits", out var units))
            return new CodeLinkVerdict(null, CodeLinkFixtures.CodeUnitsOf(units), null, null);
        if (element.TryGetProperty("programCase", out var @case))
            return new CodeLinkVerdict(null, CodeLinkFixtures.Generated(@case.GetString()!).Source, null, null);
        return new CodeLinkVerdict(null, null, element.GetProperty("programLength").GetInt32(), element.GetProperty("programSha256").GetString()!);
    }
}
