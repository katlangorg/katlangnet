using System.Collections.Immutable;
using System.Globalization;
using System.Text;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// A stable structural fingerprint of a UTF-16 case and its outcome.
///
/// <para>It carries NO source text, no wall-clock reading, no process or thread id, no object
/// address, and no runtime-randomized hash. Arbitrary source content is summarized through fixed
/// code-unit CLASS buckets, so the same case fingerprints identically in every process — which is
/// what makes the corpus, the campaign distributions and the replay comparison mean anything.</para>
/// </summary>
internal static class Utf16Fingerprint
{
    /// <summary>Named classes a single UTF-16 code unit falls into. Order is the report order.</summary>
    private static readonly ImmutableArray<string> ClassNames =
    [
        "nul", "control", "tab", "lf", "cr", "space",
        "ascii-letter", "ascii-digit", "ascii-punct",
        "latin-ext", "combining", "bmp-letter", "bmp-digit", "bmp-symbol",
        "format", "space-other", "high-surrogate", "low-surrogate", "other",
    ];

    public static string Describe(Utf16Case testCase, Utf16Observation? observation, Utf16RelationOutcome relations)
    {
        ArgumentNullException.ThrowIfNull(testCase);

        var parameters = testCase.Parameters;
        var builder = new StringBuilder(512);

        Append(builder, "template", Utf16Tables.TemplateOf(parameters.Template).Id);
        Append(builder, "placement", parameters.Placement.ToString());
        Append(builder, "lineEndings", parameters.LineEndings.ToString());
        Append(builder, "execution", parameters.ExecutionMode.ToString());
        Append(builder, "insertion", InsertionId(parameters));
        Append(builder, "repeat", Num(parameters.Repeat));
        Append(builder, "surrogates", testCase.SurrogateClass.ToString());
        Append(builder, "classes", ClassSetOf(testCase.CodeUnits));
        Append(builder, "sourceLen", Bucket(testCase.CodeUnits.Length));

        if (observation is null)
        {
            Append(builder, "outcome", "not-executed");
            return builder.ToString();
        }

        Append(builder, "lines", Bucket(observation.LineCount));
        Append(builder, "tokens", Bucket(observation.TokenCount));
        Append(builder, "recovery", RecoveryClass(observation));
        Append(builder, "parse", observation.RawDiagnosticCount == 0 ? "clean" : "diagnostics");
        Append(builder, "diagBucket", Bucket(observation.RawDiagnosticCount));
        Append(builder, "diagFirst", observation.FirstDiagnosticBucket);
        Append(builder, "diagAtOnePos", Bucket(observation.MaxDiagnosticsAtOnePosition));
        Append(builder, "spanShape", SpanShape(observation));
        Append(builder, "frontend", observation.FrontEndRan ? "ran" : "skipped");
        Append(builder, "frontendDiag", observation.FrontEndRan ? Bucket(observation.FrontEndDiagnosticCount) : "-");
        Append(builder, "spanCheck", "ok");                    // a failure throws; it never reaches here
        Append(builder, "determinism", "stable");              // ditto
        Append(builder, "relations", relations.Summary);

        return builder.ToString();
    }

    /// <summary>The insertion's identity: a group member id, or the raw mode's shape.</summary>
    public static string InsertionId(Utf16Parameters parameters)
    {
        ArgumentNullException.ThrowIfNull(parameters);
        if (!Utf16Tables.IsRaw(parameters.Template))
        {
            var group = parameters.Group.ToString().ToLowerInvariant();
            return $"{group}/{Utf16Tables.MembersOf(parameters.Group)[parameters.Member].Id}";
        }

        return $"raw/{Bucket(parameters.RawUnits.Length)}";
    }

    /// <summary>The sorted set of code-unit classes present. Stable, structural, and small.</summary>
    public static string ClassSetOf(ImmutableArray<ushort> units)
    {
        var present = new bool[ClassNames.Length];
        foreach (var unit in units) present[ClassIndexOf(unit)] = true;

        var names = new List<string>(ClassNames.Length);
        for (var i = 0; i < ClassNames.Length; i++)
            if (present[i]) names.Add(ClassNames[i]);

        return names.Count == 0 ? "none" : string.Join('+', names);
    }

    private static int ClassIndexOf(ushort unit)
    {
        var c = (char)unit;

        if (unit == 0x0000) return 0;
        if (unit == 0x0009) return 2;
        if (unit == 0x000A) return 3;
        if (unit == 0x000D) return 4;
        if (unit == 0x0020) return 5;
        if (unit < 0x0020 || unit == 0x007F) return 1;
        if (unit < 0x0080)
            return char.IsAsciiLetter(c) ? 6
                : char.IsAsciiDigit(c) ? 7
                : 8;

        if (char.IsHighSurrogate(c)) return 16;
        if (char.IsLowSurrogate(c)) return 17;

        // GetUnicodeCategory on a lone char is total: it never throws and never inspects
        // neighbours, which is exactly the per-code-unit view the lexer itself uses.
        var category = System.Globalization.CharUnicodeInfo.GetUnicodeCategory(c);
        return category switch
        {
            System.Globalization.UnicodeCategory.NonSpacingMark
                or System.Globalization.UnicodeCategory.SpacingCombiningMark
                or System.Globalization.UnicodeCategory.EnclosingMark => 10,
            System.Globalization.UnicodeCategory.Format => 14,
            System.Globalization.UnicodeCategory.SpaceSeparator
                or System.Globalization.UnicodeCategory.LineSeparator
                or System.Globalization.UnicodeCategory.ParagraphSeparator => 15,
            System.Globalization.UnicodeCategory.DecimalDigitNumber
                or System.Globalization.UnicodeCategory.LetterNumber
                or System.Globalization.UnicodeCategory.OtherNumber => 12,
            _ when unit is >= 0x0100 and <= 0x024F => 9,
            _ when char.IsLetter(c) => 11,
            System.Globalization.UnicodeCategory.MathSymbol
                or System.Globalization.UnicodeCategory.CurrencySymbol
                or System.Globalization.UnicodeCategory.ModifierSymbol
                or System.Globalization.UnicodeCategory.OtherSymbol
                or System.Globalization.UnicodeCategory.DashPunctuation
                or System.Globalization.UnicodeCategory.OtherPunctuation => 13,
            _ => 18,
        };
    }

    /// <summary>
    /// A printable, stable bucket for the FIRST diagnostic. Messages may legitimately contain an
    /// isolated surrogate (the lexer quotes the offending code unit), so every non-ASCII-printable
    /// unit is replaced with '?' — the fingerprint stays well-formed text without ever claiming the
    /// message was well-formed.
    /// </summary>
    public static string DiagnosticBucket(IReadOnlyList<Diagnostic> diagnostics)
    {
        ArgumentNullException.ThrowIfNull(diagnostics);
        if (diagnostics.Count == 0) return "none";

        var first = diagnostics[0];
        var text = first.Message;
        var builder = new StringBuilder(40);
        builder.Append(first.Severity).Append(':');
        for (var i = 0; i < text.Length && builder.Length < 40; i++)
        {
            var c = text[i];
            builder.Append(c is >= ' ' and <= '~' ? c : '?');
        }

        return builder.ToString();
    }

    private static string RecoveryClass(Utf16Observation observation)
        => observation.BadTokenCount == 0 ? "no-bad-tokens"
            : observation.BadTokenCount == 1 ? "one-bad-token"
            : $"bad-tokens-{Bucket(observation.BadTokenCount)}";

    private static string SpanShape(Utf16Observation observation)
    {
        var parts = new List<string>(3);
        parts.Add(observation.MaxSpanEndLine <= 1 ? "single-line-source" : $"lines-{Bucket(observation.MaxSpanEndLine)}");
        if (observation.AnyMultilineSpan) parts.Add("multiline-span");
        if (observation.AnyZeroWidthSpan) parts.Add("zero-width-span");
        return string.Join('+', parts);
    }

    /// <summary>Powers-of-two bucketing keeps the space small while staying monotone in size.</summary>
    public static string Bucket(int value)
    {
        if (value <= 0) return "0";
        if (value == 1) return "1";
        if (value <= 2) return "2";
        if (value <= 4) return "3-4";
        if (value <= 8) return "5-8";
        if (value <= 16) return "9-16";
        if (value <= 32) return "17-32";
        if (value <= 64) return "33-64";
        if (value <= 128) return "65-128";
        if (value <= 256) return "129-256";
        if (value <= 512) return "257-512";
        return "513+";
    }

    private static void Append(StringBuilder builder, string key, string value)
    {
        if (builder.Length > 0) builder.Append('|');
        builder.Append(key).Append('=').Append(value);
    }

    private static string Num(int value) => value.ToString(CultureInfo.InvariantCulture);
}
