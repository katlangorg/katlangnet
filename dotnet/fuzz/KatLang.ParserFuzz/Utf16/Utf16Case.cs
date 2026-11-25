using System.Collections.Immutable;
using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>
/// Where a fuzz-selected run of UTF-16 code units is inserted into a trusted source template.
/// Each value names ONE lexer/parser position; the surrounding text is fixed and reviewable
/// (see <see cref="Utf16Tables.Templates"/>).
/// </summary>
internal enum Utf16TemplateKind
{
    IdentifierStart,
    IdentifierContinue,
    PropertyName,
    FunctionName,
    ParameterName,
    NumberBoundary,
    StringLiteral,
    StringBackslash,
    StringUnterminated,
    LineComment,
    CommentAtEof,
    DelimiterAdjacent,
    DottedCall,
    SpreadOperator,
    ListLiteral,
    SequenceLiteral,
    Deconstruction,
    CollectingBinding,
    CallbackBody,
    ConditionalClause,
    MultilineBody,
    RecoveryPoint,
    EofBoundary,

    /// <summary>Bounded raw mode: payload tail bytes index a fixed alphabet of difficult code units.</summary>
    RawAlphabet,

    /// <summary>Bounded raw mode: payload tail byte PAIRS are literal UTF-16 code units, so an
    /// arbitrary (including unassigned or ill-formed) code unit is reachable.</summary>
    RawLiteralUnits,
}

/// <summary>How the selected code units sit relative to the template's insertion site.</summary>
internal enum Utf16PlacementKind
{
    Alone,
    AfterLetter,
    BeforeLetter,
    Surrounded,
    Doubled,
    Repeated3,
    SplitByNewline,
    SplitByPunctuation,
    AfterDot,
    BeforeSpread,

    /// <summary>Appended after the template's suffix — the end-of-source / EOF-recovery position.</summary>
    AtEndOfSource,
}

/// <summary>
/// How the assembled source's line breaks are physically encoded. The builder writes every
/// break as a single <c>\n</c> and this mode rewrites them; nothing else is normalized, so the
/// produced source keeps the exact code units the mode names.
/// </summary>
internal enum Utf16LineEndingMode
{
    Lf,
    Crlf,
    LoneCr,
    Mixed,
    NoNewline,
    RepeatedBlankLines,
    TrailingNewline,
    NoTrailingNewline,
}

/// <summary>How far the harness processes the generated source.</summary>
internal enum Utf16ExecutionMode
{
    /// <summary>Raw syntax boundary only — <c>Parser.ParseSyntax</c>.</summary>
    ParseSyntax,

    /// <summary>Raw syntax plus the real elaborated front end (no downloader, no network).</summary>
    FrontEnd,

    /// <summary>Front end plus the public <c>Parser.Parse</c> entry point. No evaluation.</summary>
    EngineParse,

    /// <summary>Front end plus, for eligible valid string-literal cases only, a bounded evaluation
    /// that verifies UTF-16 code-unit preservation. Never general evaluator fuzzing.</summary>
    StringBridge,
}

/// <summary>The named code-unit groups a case can draw its insertion from.</summary>
internal enum Utf16CodeUnitGroup
{
    Basic,
    Latvian,
    BmpSymbols,
    Combining,
    Surrogates,
    Whitespace,
}

/// <summary>Surrogate well-formedness of a code-unit sequence, as a stable fingerprint bucket.</summary>
internal enum Utf16SurrogateClass
{
    /// <summary>No surrogate code unit at all.</summary>
    None,

    /// <summary>Every surrogate participates in a well-formed high+low pair.</summary>
    WellFormedPairs,

    /// <summary>At least one isolated high surrogate and no isolated low surrogate.</summary>
    IsolatedHigh,

    /// <summary>At least one isolated low surrogate and no isolated high surrogate.</summary>
    IsolatedLow,

    /// <summary>Isolated surrogates of both kinds (includes reversed low+high order).</summary>
    IsolatedMixed,
}

/// <summary>
/// The decoded, normalized parameters of one UTF-16 case. Two payloads that normalize to equal
/// parameters describe the SAME case, which is what makes the fingerprint and the corpus
/// meaningful. <see cref="RawUnits"/> is empty for every structured template.
/// </summary>
internal sealed record Utf16Parameters(
    Utf16TemplateKind Template,
    Utf16PlacementKind Placement,
    Utf16LineEndingMode LineEndings,
    Utf16ExecutionMode ExecutionMode,
    Utf16CodeUnitGroup Group,
    int Member,
    int Repeat,
    int Filler,
    ImmutableArray<ushort> RawUnits)
{
    public bool Equals(Utf16Parameters? other)
        => other is not null
           && Template == other.Template
           && Placement == other.Placement
           && LineEndings == other.LineEndings
           && ExecutionMode == other.ExecutionMode
           && Group == other.Group
           && Member == other.Member
           && Repeat == other.Repeat
           && Filler == other.Filler
           && RawUnits.AsSpan().SequenceEqual(other.RawUnits.AsSpan());

    public override int GetHashCode()
    {
        var hash = new HashCode();
        hash.Add(Template);
        hash.Add(Placement);
        hash.Add(LineEndings);
        hash.Add(ExecutionMode);
        hash.Add(Group);
        hash.Add(Member);
        hash.Add(Repeat);
        hash.Add(Filler);
        foreach (var unit in RawUnits) hash.Add(unit);
        return hash.ToHashCode();
    }
}

/// <summary>
/// One fully materialized UTF-16 case: the exact source code units plus the parameters that
/// produced them. <see cref="CodeUnits"/> is the authoritative artifact — <see cref="Source"/>
/// is the same units as a .NET <c>string</c>, which may be ill-formed UTF-16 by design.
/// </summary>
internal sealed record Utf16Case(
    Utf16Parameters Parameters,
    ImmutableArray<ushort> CodeUnits,
    string Source,
    string Description)
{
    public Utf16SurrogateClass SurrogateClass => Utf16CodeUnits.ClassifySurrogates(CodeUnits);

    /// <summary>Four-digit hex code units, space separated — the only lossless printable form.</summary>
    public string HexUnits => Utf16CodeUnits.ToHex(CodeUnits);
}

/// <summary>Code-unit helpers shared by the decoder, builder, replay and fingerprint.</summary>
internal static class Utf16CodeUnits
{
    public static ImmutableArray<ushort> FromString(string text)
    {
        ArgumentNullException.ThrowIfNull(text);
        var builder = ImmutableArray.CreateBuilder<ushort>(text.Length);
        foreach (var c in text) builder.Add(c);
        return builder.MoveToImmutable();
    }

    /// <summary>
    /// Builds the .NET string for a code-unit sequence WITHOUT validating or replacing anything:
    /// isolated surrogates survive, because a .NET string is a code-unit sequence.
    /// </summary>
    public static string ToStringExact(ImmutableArray<ushort> units)
    {
        var chars = new char[units.Length];
        for (var i = 0; i < units.Length; i++) chars[i] = (char)units[i];
        return new string(chars);
    }

    public static string ToHex(ImmutableArray<ushort> units)
        => string.Join(' ', units.Select(u => u.ToString("X4", CultureInfo.InvariantCulture)));

    public static Utf16SurrogateClass ClassifySurrogates(ImmutableArray<ushort> units)
    {
        var isolatedHigh = false;
        var isolatedLow = false;
        var pairs = false;

        for (var i = 0; i < units.Length; i++)
        {
            var unit = units[i];
            if (char.IsHighSurrogate((char)unit))
            {
                if (i + 1 < units.Length && char.IsLowSurrogate((char)units[i + 1]))
                {
                    pairs = true;
                    i++;                       // consume the pair
                }
                else isolatedHigh = true;
            }
            else if (char.IsLowSurrogate((char)unit))
            {
                isolatedLow = true;
            }
        }

        return (isolatedHigh, isolatedLow) switch
        {
            (true, true) => Utf16SurrogateClass.IsolatedMixed,
            (true, false) => Utf16SurrogateClass.IsolatedHigh,
            (false, true) => Utf16SurrogateClass.IsolatedLow,
            _ => pairs ? Utf16SurrogateClass.WellFormedPairs : Utf16SurrogateClass.None,
        };
    }
}
