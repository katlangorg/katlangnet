using System.Collections.Immutable;

namespace KatLang.ParserFuzz;

/// <summary>One named code-unit sequence a case can insert.</summary>
internal sealed record Utf16Member(string Id, ImmutableArray<ushort> Units)
{
    public static Utf16Member Of(string id, params ushort[] units)
        => new(id, [.. units]);
}

/// <summary>
/// One trusted source template. <see cref="Prefix"/> and <see cref="Suffix"/> are written with
/// <c>\n</c> for every line break; <see cref="Utf16LineEndingMode"/> decides the physical encoding.
/// </summary>
/// <param name="Id">Stable identifier used in seeds, fingerprints and reports.</param>
/// <param name="Prefix">Source text before the insertion.</param>
/// <param name="Suffix">Source text after the insertion.</param>
/// <param name="ClosedWhenBenign">
/// True when the template is a complete, diagnostic-free program for a benign insertion — the
/// precondition for the trailing-newline neutrality relation.
/// </param>
/// <param name="StringBridge">
/// True when the insertion lands inside a terminated string literal, so a valid case can verify
/// exact code-unit preservation through evaluation.
/// </param>
internal sealed record Utf16Template(
    string Id,
    string Prefix,
    string Suffix,
    bool ClosedWhenBenign,
    bool StringBridge = false);

/// <summary>
/// FROZEN tables for the UTF-16 target. A payload byte selects an entry by index, so reordering
/// or removing an entry changes what every existing seed and corpus unit MEANS. Append only.
/// </summary>
internal static class Utf16Tables
{
    // ── Templates ────────────────────────────────────────────────────────────
    //
    // Every template is a small, reviewable KatLang program with ONE insertion site. The point
    // is to put difficult code units where the lexer and parser make decisions, not to produce
    // valid programs: structured rejection is a perfectly good outcome.

    public static readonly ImmutableArray<Utf16Template> Templates =
    [
        new(Utf16TemplateIds.IdentifierStart, "A = 1\nOutput = ", "A", ClosedWhenBenign: false),
        new(Utf16TemplateIds.IdentifierContinue, "A = 1\nOutput = A", "", ClosedWhenBenign: false),
        new(Utf16TemplateIds.PropertyName, "", " = 1\nOutput = 1", ClosedWhenBenign: false),
        new(Utf16TemplateIds.FunctionName, "", "(x) = x\nOutput = 1", ClosedWhenBenign: false),
        new(Utf16TemplateIds.ParameterName, "F(", ") = 1\nOutput = F(2)", ClosedWhenBenign: false),
        new(Utf16TemplateIds.NumberBoundary, "Output = 12", "34", ClosedWhenBenign: false),
        new(Utf16TemplateIds.StringLiteral, "Output = '", "'", ClosedWhenBenign: true, StringBridge: true),
        new(Utf16TemplateIds.StringBackslash, "Output = 'a\\", "b'", ClosedWhenBenign: true, StringBridge: true),
        new(Utf16TemplateIds.StringUnterminated, "Output = 'a", "\nB = 2", ClosedWhenBenign: false),
        new(Utf16TemplateIds.LineComment, "// ", "\nOutput = 1", ClosedWhenBenign: true),
        new(Utf16TemplateIds.CommentAtEof, "Output = 1\n// ", "", ClosedWhenBenign: false),
        new(Utf16TemplateIds.DelimiterAdjacent, "Output = (1, ", "2)", ClosedWhenBenign: false),
        new(Utf16TemplateIds.DottedCall, "A = (1, 2)\nOutput = A.", "count", ClosedWhenBenign: false),
        new(Utf16TemplateIds.SpreadOperator, "A = (1, 2)\nOutput = A", "*", ClosedWhenBenign: false),
        new(Utf16TemplateIds.ListLiteral, "Output = [1, ", "2]", ClosedWhenBenign: false),
        new(Utf16TemplateIds.SequenceLiteral, "Output = (1, ", "2)", ClosedWhenBenign: false),
        new(Utf16TemplateIds.Deconstruction, "x, ", ", z = (1, 2, 3)\nOutput = x", ClosedWhenBenign: false),
        new(Utf16TemplateIds.CollectingBinding, "F(a, *", "z) = a\nOutput = F(1, 2)", ClosedWhenBenign: false),
        new(Utf16TemplateIds.CallbackBody, "F(x) = x + ", "\nOutput = [1, 2].map(F)", ClosedWhenBenign: false),
        new(Utf16TemplateIds.ConditionalClause, "F(0) = 1\nF(", ") = 2\nOutput = F(0)", ClosedWhenBenign: false),
        new(Utf16TemplateIds.MultilineBody, "A = 1 +\n", "\nOutput = A", ClosedWhenBenign: false),
        new(Utf16TemplateIds.RecoveryPoint, "Output = (1, ", "", ClosedWhenBenign: false),
        new(Utf16TemplateIds.EofBoundary, "Output = 1\n", "", ClosedWhenBenign: false),
        new(Utf16TemplateIds.RawAlphabet, "", "", ClosedWhenBenign: false),
        new(Utf16TemplateIds.RawLiteralUnits, "", "", ClosedWhenBenign: false),
    ];

    /// <summary>The two templates whose insertion is read from the payload tail, not the group table.</summary>
    public static bool IsRaw(Utf16TemplateKind template)
        => template is Utf16TemplateKind.RawAlphabet or Utf16TemplateKind.RawLiteralUnits;

    public static Utf16Template TemplateOf(Utf16TemplateKind kind) => Templates[(int)kind];

    // ── Code-unit groups ─────────────────────────────────────────────────────

    /// <summary>ASCII letters, digits, punctuation, spaces, tabs, NUL and control characters.</summary>
    public static readonly ImmutableArray<Utf16Member> Basic =
    [
        Utf16Member.Of("ascii-upper", 0x0041),
        Utf16Member.Of("ascii-lower", 0x007A),
        Utf16Member.Of("ascii-digit", 0x0037),
        Utf16Member.Of("underscore", 0x005F),
        Utf16Member.Of("bang", 0x0021),
        Utf16Member.Of("backslash", 0x005C),
        Utf16Member.Of("at-sign", 0x0040),
        Utf16Member.Of("space", 0x0020),
        Utf16Member.Of("tab", 0x0009),
        Utf16Member.Of("nul", 0x0000),
        Utf16Member.Of("nul-run", 0x0000, 0x0000, 0x0000),
        Utf16Member.Of("control-bell", 0x0007),
        Utf16Member.Of("control-esc", 0x001B),
        Utf16Member.Of("delete", 0x007F),
        Utf16Member.Of("quote", 0x0027),
        Utf16Member.Of("dot", 0x002E),
        Utf16Member.Of("dot-dot", 0x002E, 0x002E),
        Utf16Member.Of("ellipsis", 0x002E, 0x002E, 0x002E),
        Utf16Member.Of("paren-open", 0x0028),
        Utf16Member.Of("brace-open", 0x007B),
        Utf16Member.Of("bracket-open", 0x005B),
        Utf16Member.Of("semicolon", 0x003B),
    ];

    /// <summary>Latvian letters, the repository's primary non-ASCII natural-language text.</summary>
    public static readonly ImmutableArray<Utf16Member> Latvian =
    [
        Utf16Member.Of("a-macron", 0x0101),          // ā
        Utf16Member.Of("c-caron", 0x010D),           // č
        Utf16Member.Of("e-macron", 0x0113),          // ē
        Utf16Member.Of("g-cedilla", 0x0123),         // ģ
        Utf16Member.Of("i-macron", 0x012B),          // ī
        Utf16Member.Of("k-cedilla", 0x0137),         // ķ
        Utf16Member.Of("l-cedilla", 0x013C),         // ļ
        Utf16Member.Of("n-cedilla", 0x0146),         // ņ
        Utf16Member.Of("s-caron", 0x0161),           // š
        Utf16Member.Of("u-macron", 0x016B),          // ū
        Utf16Member.Of("z-caron", 0x017E),           // ž
        Utf16Member.Of("upper-run", 0x0100, 0x010C, 0x0112, 0x0122),      // ĀČĒĢ
        Utf16Member.Of("upper-rest", 0x012A, 0x0136, 0x013B, 0x0145),     // ĪĶĻŅ
        Utf16Member.Of("upper-tail", 0x0160, 0x016A, 0x017D),             // ŠŪŽ
        Utf16Member.Of("word", 0x0100, 0x0101, 0x0161, 0x016B),           // Āašū
        Utf16Member.Of("vowels", 0x0101, 0x0113, 0x012B, 0x016B),         // āēīū
        Utf16Member.Of("mixed-ascii", 0x0053, 0x0161, 0x0041),            // SšA
    ];

    /// <summary>Non-Latin BMP letters, symbols, and format/space characters.</summary>
    public static readonly ImmutableArray<Utf16Member> BmpSymbols =
    [
        Utf16Member.Of("greek-lower", 0x03B1, 0x03B2),      // αβ
        Utf16Member.Of("greek-upper", 0x03A9),              // Ω
        Utf16Member.Of("cyrillic", 0x0416, 0x0438),         // Жи
        Utf16Member.Of("math-operator", 0x2211),            // ∑
        Utf16Member.Of("math-letterlike", 0x2115),          // ℕ (a LETTER by Unicode category)
        Utf16Member.Of("arrow", 0x2192),                    // →
        Utf16Member.Of("currency-euro", 0x20AC),            // €
        Utf16Member.Of("currency-sign", 0x00A4),            // ¤
        Utf16Member.Of("em-dash", 0x2014),                  // —
        Utf16Member.Of("nbsp", 0x00A0),
        Utf16Member.Of("zero-width-space", 0x200B),         // Cf, NOT .NET whitespace
        Utf16Member.Of("zero-width-joiner", 0x200D),
        Utf16Member.Of("byte-order-mark", 0xFEFF),
        Utf16Member.Of("ideographic", 0x4E2D),              // 中
        Utf16Member.Of("fullwidth-digit", 0xFF10),          // ０ (a DIGIT by Unicode category)
        Utf16Member.Of("arabic-indic-digit", 0x0660),       // ٠ (a DIGIT by Unicode category)
        Utf16Member.Of("noncharacter", 0xFFFE),
        Utf16Member.Of("replacement-char", 0xFFFD),
        Utf16Member.Of("private-use", 0xE000),
        Utf16Member.Of("roman-numeral", 0x2160),            // Ⅰ (Nl)
    ];

    /// <summary>Combining marks, and precomposed versus decomposed forms of the same glyph.</summary>
    public static readonly ImmutableArray<Utf16Member> Combining =
    [
        Utf16Member.Of("base-plus-mark", 0x0065, 0x0301),                       // e + acute
        Utf16Member.Of("base-plus-three", 0x0065, 0x0301, 0x0308, 0x0327),
        Utf16Member.Of("mark-alone", 0x0301),
        Utf16Member.Of("mark-run", 0x0301, 0x0301, 0x0301, 0x0301),
        Utf16Member.Of("precomposed-e-acute", 0x00E9),                          // é as ONE unit
        Utf16Member.Of("decomposed-e-acute", 0x0065, 0x0301),                   // é as TWO units
        Utf16Member.Of("precomposed-a-macron", 0x0101),                         // ā as ONE unit
        Utf16Member.Of("decomposed-a-macron", 0x0061, 0x0304),                  // ā as TWO units
        Utf16Member.Of("mark-after-dot", 0x002E, 0x0301),
        Utf16Member.Of("mark-before-spread", 0x0301, 0x002A),
        Utf16Member.Of("mark-after-space", 0x0020, 0x0301),
        Utf16Member.Of("hangul-jamo", 0x1100, 0x1161),
        Utf16Member.Of("enclosing-mark", 0x0041, 0x20DD),                       // A + enclosing circle
        Utf16Member.Of("variation-selector", 0x0041, 0xFE0F),
    ];

    /// <summary>Well-formed pairs, isolated halves, reversed order, repeats, and split pairs.</summary>
    public static readonly ImmutableArray<Utf16Member> Surrogates =
    [
        Utf16Member.Of("valid-pair", 0xD83D, 0xDE00),                 // U+1F600
        Utf16Member.Of("valid-pair-letter", 0xD835, 0xDC00),          // U+1D400, a LETTER as a scalar
        Utf16Member.Of("pair-min", 0xD800, 0xDC00),                   // U+10000
        Utf16Member.Of("pair-max", 0xDBFF, 0xDFFF),                   // U+10FFFF
        Utf16Member.Of("several-pairs", 0xD83D, 0xDE00, 0xD835, 0xDC00),
        Utf16Member.Of("high-alone", 0xD83D),
        Utf16Member.Of("low-alone", 0xDE00),
        Utf16Member.Of("high-min", 0xD800),
        Utf16Member.Of("high-max", 0xDBFF),
        Utf16Member.Of("low-min", 0xDC00),
        Utf16Member.Of("low-max", 0xDFFF),
        Utf16Member.Of("reversed-pair", 0xDE00, 0xD83D),
        Utf16Member.Of("high-high", 0xD83D, 0xD83D),
        Utf16Member.Of("low-low", 0xDE00, 0xDE00),
        Utf16Member.Of("pair-split-lf", 0xD83D, 0x000A, 0xDE00),
        Utf16Member.Of("pair-split-crlf", 0xD83D, 0x000D, 0x000A, 0xDE00),
        Utf16Member.Of("pair-split-dot", 0xD83D, 0x002E, 0xDE00),
        Utf16Member.Of("pair-split-quote", 0xD83D, 0x0027, 0xDE00),
        Utf16Member.Of("pair-split-space", 0xD83D, 0x0020, 0xDE00),
        Utf16Member.Of("high-then-letter", 0xD83D, 0x0041),
        Utf16Member.Of("letter-then-low", 0x0041, 0xDE00),
        Utf16Member.Of("high-then-nul", 0xD83D, 0x0000),
    ];

    /// <summary>
    /// Whitespace and line-separator candidates. Only <c>\n</c> is a KatLang line break; the rest
    /// are here precisely because the lexer must NOT treat them as one.
    /// </summary>
    public static readonly ImmutableArray<Utf16Member> Whitespace =
    [
        Utf16Member.Of("space", 0x0020),
        Utf16Member.Of("tab", 0x0009),
        Utf16Member.Of("lf", 0x000A),
        Utf16Member.Of("crlf", 0x000D, 0x000A),
        Utf16Member.Of("cr", 0x000D),
        Utf16Member.Of("cr-cr", 0x000D, 0x000D),
        Utf16Member.Of("lf-lf", 0x000A, 0x000A),
        Utf16Member.Of("mixed-endings", 0x000D, 0x000A, 0x000A, 0x000D),
        Utf16Member.Of("cr-lf-reversed", 0x000A, 0x000D),
        Utf16Member.Of("form-feed", 0x000C),
        Utf16Member.Of("vertical-tab", 0x000B),
        Utf16Member.Of("nbsp", 0x00A0),
        Utf16Member.Of("line-separator", 0x2028),
        Utf16Member.Of("paragraph-separator", 0x2029),
        Utf16Member.Of("next-line", 0x0085),
        Utf16Member.Of("ogham-space", 0x1680),
        Utf16Member.Of("en-quad", 0x2000),
        Utf16Member.Of("ideographic-space", 0x3000),
        Utf16Member.Of("narrow-nbsp", 0x202F),
        Utf16Member.Of("medium-mathematical-space", 0x205F),
    ];

    public static ImmutableArray<Utf16Member> MembersOf(Utf16CodeUnitGroup group) => group switch
    {
        Utf16CodeUnitGroup.Basic => Basic,
        Utf16CodeUnitGroup.Latvian => Latvian,
        Utf16CodeUnitGroup.BmpSymbols => BmpSymbols,
        Utf16CodeUnitGroup.Combining => Combining,
        Utf16CodeUnitGroup.Surrogates => Surrogates,
        Utf16CodeUnitGroup.Whitespace => Whitespace,
        _ => throw new ArgumentOutOfRangeException(nameof(group), group, "Unknown code-unit group."),
    };

    /// <summary>
    /// The alphabet <see cref="Utf16TemplateKind.RawAlphabet"/> indexes with one payload byte per
    /// code unit — dense in the units that actually make the lexer decide something.
    /// </summary>
    public static readonly ImmutableArray<ushort> RawAlphabet =
    [
        // Structure and operators
        0x0020, 0x0009, 0x000A, 0x000D, 0x0000, 0x0027, 0x002E, 0x002C, 0x003D, 0x0028,
        0x0029, 0x005B, 0x005D, 0x007B, 0x007D, 0x002B, 0x002D, 0x002A, 0x002F, 0x005E,
        0x003C, 0x003E, 0x0021, 0x003A, 0x003B, 0x007E, 0x005F, 0x005C, 0x0025, 0x0023,
        // ASCII letters and digits
        0x0041, 0x0042, 0x004F, 0x0061, 0x0062, 0x0078, 0x007A, 0x0030, 0x0031, 0x0039,
        0x0065, 0x0045,
        // Latvian
        0x0101, 0x010D, 0x0113, 0x0123, 0x012B, 0x0137, 0x013C, 0x0146, 0x0161, 0x016B,
        0x017E, 0x0100, 0x0160, 0x017D,
        // Other BMP letters and symbols
        0x03B1, 0x03A9, 0x0416, 0x2211, 0x2115, 0x2192, 0x20AC, 0x2014, 0x4E2D, 0x2160,
        // Format, space and problem characters
        0x00A0, 0x200B, 0x200D, 0xFEFF, 0x2028, 0x2029, 0x0085, 0x000B, 0x000C, 0x3000,
        0xFFFD, 0xFFFE, 0xE000, 0x007F, 0x001B,
        // Combining marks
        0x0301, 0x0308, 0x0327, 0x0304, 0x20DD, 0xFE0F,
        // Digits that are digits only by Unicode category
        0xFF10, 0x0660,
        // Surrogate code units, both halves and both extremes
        0xD83D, 0xDE00, 0xD835, 0xDC00, 0xD800, 0xDBFF, 0xDFFF,
    ];

    /// <summary>ASCII letters the placement decorations use, so a decoration never adds a
    /// character the template did not expect.</summary>
    public static readonly ImmutableArray<ushort> FillerLetters = [0x0061, 0x0042, 0x005F, 0x0079];

    public const int MaxRawAlphabetUnits = 48;
    public const int MaxRawLiteralUnits = 24;

    /// <summary>Hard cap on the code units of a generated source. Enforced by construction; the
    /// readiness tests assert the whole stratified space stays well under it.</summary>
    public const int MaxSourceCodeUnits = 2048;
}

/// <summary>Stable template identifiers. Separate from the enum so seeds read as text.</summary>
internal static class Utf16TemplateIds
{
    public const string IdentifierStart = "identifier-start";
    public const string IdentifierContinue = "identifier-continue";
    public const string PropertyName = "property-name";
    public const string FunctionName = "function-name";
    public const string ParameterName = "parameter-name";
    public const string NumberBoundary = "number-boundary";
    public const string StringLiteral = "string-literal";
    public const string StringBackslash = "string-backslash";
    public const string StringUnterminated = "string-unterminated";
    public const string LineComment = "line-comment";
    public const string CommentAtEof = "comment-at-eof";
    public const string DelimiterAdjacent = "delimiter-adjacent";
    public const string DottedCall = "dotted-call";
    public const string SpreadOperator = "spread-operator";
    public const string ListLiteral = "list-literal";
    public const string SequenceLiteral = "sequence-literal";
    public const string Deconstruction = "deconstruction";
    public const string CollectingBinding = "collecting-binding";
    public const string CallbackBody = "callback-body";
    public const string ConditionalClause = "conditional-clause";
    public const string MultilineBody = "multiline-body";
    public const string RecoveryPoint = "recovery-point";
    public const string EofBoundary = "eof-boundary";
    public const string RawAlphabet = "raw-alphabet";
    public const string RawLiteralUnits = "raw-literal-units";
}
