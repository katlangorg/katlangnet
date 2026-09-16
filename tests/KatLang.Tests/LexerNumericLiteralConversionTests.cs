using System.Globalization;
using System.Numerics;
using System.Text;
using System.Text.RegularExpressions;

namespace KatLang.Tests;

/// <summary>
/// The numeric-literal CONVERSION contract. The lexer's scan loop decides which code units
/// form a numeric literal; <c>Decimal128</c> parsing then converts exactly that text, from a
/// span over the source (a separator literal is stripped into a temporary string first).
/// These tests pin the observable contract of that division of labour — token boundaries,
/// values (including quantum), spans, diagnostic codes and wording — against two
/// INDEPENDENT oracles that never touch the production conversion:
/// <list type="bullet">
/// <item>the <c>Number</c> production of <c>KatLang.ebnf</c>, re-stated here as a regex, for
/// where an ASCII literal ends;</item>
/// <item>the pre-optimization conversion (token text → strip <c>_</c> → string-based
/// <c>Decimal128.TryParse</c>) for what the selected text is worth.</item>
/// </list>
/// Nothing here asserts that an input SHOULD lex as it does; it records what the lexer does
/// today so that a deliberate change is a reviewed diff and a drift is a failure.
/// </summary>
public class LexerNumericLiteralConversionTests
{
    private const string TooLargeMessage = "Number literal is too large.";
    private const string InvalidMessage =
        "Number literal is not a valid KatLang number: only the ASCII digits 0-9 are recognized (with an optional fraction and a lowercase 'e' exponent).";

    // ── Oracles ──────────────────────────────────────────────────────────────

    /// <summary>
    /// The <c>Number</c> production of KatLang.ebnf, anchored at the match start: a digit
    /// run with separators only BETWEEN digits, an optional fraction, an optional lowercase
    /// exponent with an optional sign. Backtracking makes the match maximal without ever
    /// admitting a trailing separator, a bare dot, or an exponent marker with no digit.
    /// </summary>
    private static readonly Regex NumberProduction = new(
        @"\G[0-9](_*[0-9])*(\.[0-9](_*[0-9])*)?(e[+-]?[0-9](_*[0-9])*)?",
        RegexOptions.CultureInvariant | RegexOptions.ExplicitCapture);

    private enum Outcome { Value, TooLarge, Invalid }

    /// <summary>
    /// The pre-optimization conversion, reproduced test-side: the token's source text with
    /// every separator removed, parsed by the STRING overload of Decimal128.TryParse.
    /// </summary>
    private static (Outcome Outcome, Decimal128 Value) LegacyConvert(string tokenText)
    {
        var stripped = tokenText.Replace("_", "");
        var parsed = Decimal128.TryParse(stripped, NumberStyles.Float, CultureInfo.InvariantCulture, out var value);
        if (!parsed)
            return (Outcome.Invalid, default);
        return Decimal128.IsFinite(value) ? (Outcome.Value, value) : (Outcome.TooLarge, default);
    }

    private static string Canonical(Decimal128 value) => value.ToString(CultureInfo.InvariantCulture);

    /// <summary>
    /// Asserts value IDENTITY, not mere numeric equality: two Decimal128 values with the
    /// same numeric value but different quantum (1 versus 1.0) render differently, so the
    /// canonical rendering is compared alongside <see cref="Decimal128.Equals(Decimal128)"/>.
    /// </summary>
    private static void AssertSameValue(Decimal128 expected, Decimal128 actual, string context)
    {
        if (!expected.Equals(actual) || Canonical(expected) != Canonical(actual))
            Assert.Fail($"{context}: expected {Canonical(expected)} but lexed {Canonical(actual)}.");
    }

    private static string Slice(string source, Token token) => source.Substring(token.Position, token.Length);

    /// <summary>Names a token for a failure message: its text, offset, and a bounded excerpt
    /// of the source around it (sources here run to hundreds of thousands of code units).</summary>
    private static string Context(string source, Token token)
    {
        var excerptStart = Math.Max(0, token.Position - 16);
        var excerptLength = Math.Min(source.Length - excerptStart, token.Length + 32);
        return $"literal '{Printable(Slice(source, token))}' at {token.Position} in \"{Printable(source.Substring(excerptStart, excerptLength))}\"";
    }

    /// <summary>
    /// Checks one tokenization against both oracles: every number token's extent is the
    /// grammar's maximal match at its position, its value or diagnostic is what the legacy
    /// conversion yields, a failing literal carries exactly one diagnostic spanning the
    /// token (inclusive end column), and diagnostics exist for failing literals only.
    /// </summary>
    private static void AssertAgreesWithOracles(string source)
    {
        var (tokens, diagnostics) = Lexer.Tokenize(source);
        var expectedDiagnostics = new List<(DiagnosticCode Code, string Message, SourceSpan Span)>();

        foreach (var token in tokens.Where(static t => t.Kind == TokenKind.Number))
        {
            var grammar = NumberProduction.Match(source, token.Position);
            if (!grammar.Success || grammar.Length != token.Length)
            {
                Assert.Fail(
                    $"{Context(source, token)}: the lexer selected {token.Length} code units but the EBNF Number production matches {(grammar.Success ? grammar.Length : 0)}.");
            }

            var (outcome, value) = LegacyConvert(Slice(source, token));
            switch (outcome)
            {
                case Outcome.Value:
                    if (!value.Equals(token.NumValue) || Canonical(value) != Canonical(token.NumValue))
                        Assert.Fail($"{Context(source, token)}: expected {Canonical(value)} but lexed {Canonical(token.NumValue)}.");
                    break;
                case Outcome.TooLarge:
                    if (!token.NumValue.Equals(Decimal128.Zero))
                        Assert.Fail($"{Context(source, token)}: an out-of-range literal must lex as the zero placeholder.");
                    expectedDiagnostics.Add((DiagnosticCode.NumberLiteralTooLarge, TooLargeMessage, TokenSpan(token)));
                    break;
                case Outcome.Invalid:
                    if (!token.NumValue.Equals(Decimal128.Zero))
                        Assert.Fail($"{Context(source, token)}: an unparsable literal must lex as the zero placeholder.");
                    expectedDiagnostics.Add((DiagnosticCode.InvalidNumberLiteral, InvalidMessage, TokenSpan(token)));
                    break;
            }
        }

        Assert.Equal(
            expectedDiagnostics.Select(static d => (d.Code, d.Message, Describe(d.Span))).ToArray(),
            diagnostics.Select(static d => (d.Code, d.Message, Describe(d.Span))).ToArray());
    }

    private static SourceSpan TokenSpan(Token token)
        => new(token.Line, token.Column, token.Line, token.Column + token.Length - 1);

    private static string Describe(SourceSpan span)
        => $"{span.StartLineNumber}:{span.StartColumn}-{span.EndLineNumber}:{span.EndColumn}";

    private static string Printable(string text)
        => string.Concat(text.Select(static c =>
            c is >= ' ' and <= '~' ? c.ToString() : $"U+{(int)c:X4}"));

    // ── Differential corpus ──────────────────────────────────────────────────

    private static readonly string[] IntegerParts =
    [
        "0", "1", "7", "42", "007", "123456789",
        "1_000", "1__0", "9_8_7_6",
        "1234567890123456789012345678901234",           // 34 significant digits
        "12345678901234567890123456789012345",          // 35: a rounding tie
        "99999999999999999999999999999999995",          // 35: a tie that carries out
        "1_234_567_890_123_456_789_012_345_678_901_234_5",
    ];

    private static readonly string[] FractionParts =
    [
        "", ".5", ".0", ".000_1", ".14_15",
        ".9999999999999999999999999999999999",
        ".123456789012345678901234567890123456789",
    ];

    private static readonly string[] ExponentParts =
    [
        "", "e0", "e5", "e+5", "e-5", "e1_0", "e-6_1_7_6", "e6144", "e6145", "e-6177", "e99999999999", "e+0_0",
    ];

    /// <summary>Every literal of the grid: integer part × fraction part × exponent part.</summary>
    private static IEnumerable<string> GridLiterals()
        => from integer in IntegerParts
           from fraction in FractionParts
           from exponent in ExponentParts
           select integer + fraction + exponent;

    /// <summary>
    /// Contexts a literal appears in: the whole source (where <c>string.Substring</c> would
    /// return the source instance), an assignment row, a bundle, an operator chain, and a
    /// row ending in a comment.
    /// </summary>
    private static readonly Func<string, string>[] Contexts =
    [
        static literal => literal,
        static literal => $"X = {literal}\n",
        static literal => $"({literal}, {literal})",
        static literal => $"{literal}+{literal}*2",
        static literal => $"A({literal}) # {literal}",
    ];

    [Fact]
    public void GridLiterals_AgreeWithTheGrammarAndTheLegacyConversion_InEveryContext()
    {
        var count = 0;
        foreach (var literal in GridLiterals())
        {
            foreach (var context in Contexts)
            {
                AssertAgreesWithOracles(context(literal));
                count++;
            }
        }

        Assert.Equal(IntegerParts.Length * FractionParts.Length * ExponentParts.Length * Contexts.Length, count);
    }

    [Fact]
    public void GridLiterals_CoverEveryConversionOutcome()
    {
        // The grid is only a differential oracle if it reaches all three outcomes.
        var outcomes = GridLiterals().Select(static literal => LegacyConvert(literal).Outcome).ToHashSet();
        Assert.Contains(Outcome.Value, outcomes);
        Assert.Contains(Outcome.TooLarge, outcomes);
        Assert.DoesNotContain(Outcome.Invalid, outcomes); // ASCII grid: invalid literals are pinned below
    }

    // ── Valid literals: pinned values ────────────────────────────────────────

    /// <summary>
    /// (literal, canonical IEEE rendering of the expected Decimal128). The rendering pins
    /// the quantum too: <c>1.0</c> is not <c>1</c>, and <c>1e2</c> is not <c>100</c>.
    /// </summary>
    public static TheoryData<string, string> ValidLiterals => new()
    {
        { "0", "0" },
        { "00", "0" },
        { "007", "7" },
        { "123", "123" },
        { "123.456", "123.456" },
        { "1.0", "1.0" },
        { "1.00", "1.00" },
        { "0.0", "0.0" },
        { "1e2", "1E+02" },
        { "0e5", "0E+05" },
        { "6.022e23", "6.022E+23" },
        { "1e+5", "1E+05" },
        { "1e-5", "1E-05" },
        { "1.5e+2", "1.5E+02" },
        { "1.5e-2", "0.015" },
        { "0.0001", "0.0001" },
        { "1234567890123456789012345678901234", "1234567890123456789012345678901234" },
        { "12345678901234567890123456789012345", "1.234567890123456789012345678901234E+34" }, // tie -> even (…234)
        { "12345678901234567890123456789012355", "1.234567890123456789012345678901236E+34" }, // tie -> even (…236)
        { "12345678901234567890123456789012346", "1.234567890123456789012345678901235E+34" }, // above the tie
        { "0.99999999999999999999999999999999995", "1.000000000000000000000000000000000" },   // tie carrying out of 34 nines
        { "9999999999999999999999999999999999e6111", "9.999999999999999999999999999999999E+6144" }, // largest finite
        { "1e6144", "1.000000000000000000000000000000000E+6144" },
        { "1e-6176", "1E-6176" },       // smallest subnormal
        { "1e-6143", "1E-6143" },       // smallest normal
        { "1e-6177", "0E-6176" },       // underflows to zero, finite: no diagnostic
        { "0e99999999999", "0E+6111" }, // zero with a huge exponent clamps, finite
        // Separators in every legal position.
        { "1_000", "1000" },
        { "1_000_000", "1000000" },
        { "1__0", "10" },
        { "1_2.3_4", "12.34" },
        { "1.0_1", "1.01" },
        { "3.14_15", "3.1415" },
        { "0.000_1", "0.0001" },
        { "1e1_0", "1E+10" },
        { "1_0e-1_0", "1.0E-09" },
        { "1_2.3_4e+5_6", "1.234E+57" },
        { "7e1_0", "7E+10" },
    };

    [Theory]
    [MemberData(nameof(ValidLiterals))]
    public void ValidLiteral_LexesToTheExpectedValue_WithNoDiagnostic(string literal, string canonical)
    {
        var source = "X = " + literal;
        var (tokens, diagnostics) = Lexer.Tokenize(source);

        Assert.Empty(diagnostics);
        Assert.Equal(
            [TokenKind.Identifier, TokenKind.Equals, TokenKind.Number, TokenKind.EndOfFile],
            tokens.Select(static t => t.Kind).ToArray());

        var token = tokens[2];
        Assert.Equal(4, token.Position);
        Assert.Equal(literal.Length, token.Length);
        Assert.Equal(1, token.Line);
        Assert.Equal(5, token.Column);
        Assert.Equal(canonical, Canonical(token.NumValue));
        AssertSameValue(Decimal128.Parse(canonical, NumberStyles.Float, CultureInfo.InvariantCulture), token.NumValue, literal);

        // The whole-source spelling reaches the same value through the same path.
        var (alone, aloneDiagnostics) = Lexer.Tokenize(literal);
        Assert.Empty(aloneDiagnostics);
        Assert.Equal(canonical, Canonical(alone[0].NumValue));
    }

    // ── Failing literals: pinned diagnostics ─────────────────────────────────

    public static TheoryData<string, DiagnosticCode, string> FailingLiterals => new()
    {
        { "1e6145", DiagnosticCode.NumberLiteralTooLarge, TooLargeMessage },
        { "10e6144", DiagnosticCode.NumberLiteralTooLarge, TooLargeMessage },
        { "9999999999999999999999999999999999e6112", DiagnosticCode.NumberLiteralTooLarge, TooLargeMessage },
        { "1e99999999999", DiagnosticCode.NumberLiteralTooLarge, TooLargeMessage },
        { "1e2147483648", DiagnosticCode.NumberLiteralTooLarge, TooLargeMessage },
        { "1_0e6_144", DiagnosticCode.NumberLiteralTooLarge, TooLargeMessage },
        { "\u0663", DiagnosticCode.InvalidNumberLiteral, InvalidMessage },          // ARABIC-INDIC DIGIT THREE
        { "1\u0663", DiagnosticCode.InvalidNumberLiteral, InvalidMessage },
        { "\u06631", DiagnosticCode.InvalidNumberLiteral, InvalidMessage },
        { "1.\u0663", DiagnosticCode.InvalidNumberLiteral, InvalidMessage },
        { "1e\u0663", DiagnosticCode.InvalidNumberLiteral, InvalidMessage },
        { "1e+\u0663", DiagnosticCode.InvalidNumberLiteral, InvalidMessage },
        { "1_\u0663", DiagnosticCode.InvalidNumberLiteral, InvalidMessage },
        { "\u0663.5", DiagnosticCode.InvalidNumberLiteral, InvalidMessage },
        { "0.\u0663e5", DiagnosticCode.InvalidNumberLiteral, InvalidMessage },
        { "\uFF11\uFF12", DiagnosticCode.InvalidNumberLiteral, InvalidMessage },    // FULLWIDTH DIGITS ONE TWO
        { "1\u0663e6145", DiagnosticCode.InvalidNumberLiteral, InvalidMessage },    // unparsable wins over magnitude
    };

    [Theory]
    [MemberData(nameof(FailingLiterals))]
    public void FailingLiteral_LexesAsOneZeroPlaceholder_WithOnePositionedDiagnostic(string literal, DiagnosticCode code, string message)
    {
        var source = "X = " + literal + "\nY";
        var (tokens, diagnostics) = Lexer.Tokenize(source);

        // One token covers the whole literal; the source after it still lexes normally.
        Assert.Equal(
            [TokenKind.Identifier, TokenKind.Equals, TokenKind.Number, TokenKind.Identifier, TokenKind.EndOfFile],
            tokens.Select(static t => t.Kind).ToArray());
        var token = tokens[2];
        Assert.Equal(4, token.Position);
        Assert.Equal(literal.Length, token.Length);
        Assert.True(token.NumValue.Equals(Decimal128.Zero));
        Assert.Equal(2, tokens[3].Line);

        var diagnostic = Assert.Single(diagnostics);
        Assert.Equal(code, diagnostic.Code);
        Assert.Equal(message, diagnostic.Message);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Equal(1, diagnostic.Span.StartLineNumber);
        Assert.Equal(5, diagnostic.Span.StartColumn);
        Assert.Equal(1, diagnostic.Span.EndLineNumber);
        Assert.Equal(4 + literal.Length, diagnostic.Span.EndColumn); // inclusive end column
    }

    // ── Token boundaries: where the scan stops ───────────────────────────────

    /// <summary>
    /// (source, expected (kind, text) per token before EOF). Every row lexes with NO
    /// diagnostic: the scan simply stops before the code unit it does not admit, and the
    /// remainder is ordinary tokens.
    /// </summary>
    public static TheoryData<string, (TokenKind Kind, string Text)[]> BoundaryShapes => new()
    {
        { "7e", [(TokenKind.Number, "7"), (TokenKind.Identifier, "e")] },
        { "7e+", [(TokenKind.Number, "7"), (TokenKind.Identifier, "e"), (TokenKind.Plus, "+")] },
        { "7e-x", [(TokenKind.Number, "7"), (TokenKind.Identifier, "e"), (TokenKind.Minus, "-"), (TokenKind.Identifier, "x")] },
        { "7e_3", [(TokenKind.Number, "7"), (TokenKind.Identifier, "e_3")] },
        { "7E3", [(TokenKind.Number, "7"), (TokenKind.Identifier, "E3")] },
        { "1.", [(TokenKind.Number, "1"), (TokenKind.Dot, ".")] },
        { "1..2", [(TokenKind.Number, "1"), (TokenKind.Dot, "."), (TokenKind.Dot, "."), (TokenKind.Number, "2")] },
        { ".5", [(TokenKind.Dot, "."), (TokenKind.Number, "5")] },
        { "1.e5", [(TokenKind.Number, "1"), (TokenKind.Dot, "."), (TokenKind.Identifier, "e5")] },
        { "1._5", [(TokenKind.Number, "1"), (TokenKind.Dot, "."), (TokenKind.Identifier, "_5")] },
        { "1_.5", [(TokenKind.Number, "1"), (TokenKind.Identifier, "_"), (TokenKind.Dot, "."), (TokenKind.Number, "5")] },
        { "1.x", [(TokenKind.Number, "1"), (TokenKind.Dot, "."), (TokenKind.Identifier, "x")] },
        { "1.5.5", [(TokenKind.Number, "1.5"), (TokenKind.Dot, "."), (TokenKind.Number, "5")] },
        { "1e5e5", [(TokenKind.Number, "1e5"), (TokenKind.Identifier, "e5")] },
        { "1e5.5", [(TokenKind.Number, "1e5"), (TokenKind.Dot, "."), (TokenKind.Number, "5")] },
        { "1e+5+5", [(TokenKind.Number, "1e+5"), (TokenKind.Plus, "+"), (TokenKind.Number, "5")] },
        { "1e-5-5", [(TokenKind.Number, "1e-5"), (TokenKind.Minus, "-"), (TokenKind.Number, "5")] },
        { "1_", [(TokenKind.Number, "1"), (TokenKind.Identifier, "_")] },
        { "1__", [(TokenKind.Number, "1"), (TokenKind.Identifier, "__")] },
        { "1_000_", [(TokenKind.Number, "1_000"), (TokenKind.Identifier, "_")] },
        { "1_e5", [(TokenKind.Number, "1"), (TokenKind.Identifier, "_e5")] },
        { "1e5_", [(TokenKind.Number, "1e5"), (TokenKind.Identifier, "_")] },
        { "_1", [(TokenKind.Identifier, "_1")] },
        { "1x", [(TokenKind.Number, "1"), (TokenKind.Identifier, "x")] },
        { "1e5x", [(TokenKind.Number, "1e5"), (TokenKind.Identifier, "x")] },
        { "1\u0663x", [(TokenKind.Number, "1\u0663"), (TokenKind.Identifier, "x")] },
        { "-1", [(TokenKind.Minus, "-"), (TokenKind.Number, "1")] },
        { "+1", [(TokenKind.Plus, "+"), (TokenKind.Number, "1")] },
    };

    [Theory]
    [MemberData(nameof(BoundaryShapes))]
    public void ScanStopsExactlyWhereTheGrammarStops(string source, (TokenKind Kind, string Text)[] expected)
    {
        var (tokens, diagnostics) = Lexer.Tokenize(source);

        // The only diagnostic a row may carry is the invalid-literal one for a non-ASCII digit.
        Assert.All(diagnostics, static d => Assert.Equal(DiagnosticCode.InvalidNumberLiteral, d.Code));
        Assert.Equal(TokenKind.EndOfFile, tokens[^1].Kind);
        Assert.Equal(source.Length, tokens[^1].Position);
        Assert.Equal(
            expected,
            tokens.Take(tokens.Count - 1).Select(t => (t.Kind, Slice(source, t))).ToArray());

        // Tokens tile the source contiguously.
        var position = 0;
        foreach (var token in tokens)
        {
            Assert.Equal(position, token.Position);
            position += token.Length;
        }
    }

    /// <summary>
    /// A literal followed by one code unit of every token class the lexer knows: the scan
    /// never consumes into the follower, and the follower lexes as itself.
    /// </summary>
    public static TheoryData<string, TokenKind> Followers => new()
    {
        { "+", TokenKind.Plus }, { "-", TokenKind.Minus }, { "*", TokenKind.Star }, { "/", TokenKind.Slash },
        { "^", TokenKind.Caret }, { "<", TokenKind.LessThan }, { ">", TokenKind.GreaterThan },
        { "<=", TokenKind.LessEqual }, { ">=", TokenKind.GreaterEqual }, { "==", TokenKind.EqualEqual },
        { "!=", TokenKind.BangEqual }, { "=", TokenKind.Equals },
        { "(", TokenKind.LParen }, { ")", TokenKind.RParen }, { "{", TokenKind.LBrace }, { "}", TokenKind.RBrace },
        { "[", TokenKind.LBracket }, { "]", TokenKind.RBracket }, { ",", TokenKind.Comma }, { ";", TokenKind.Semicolon },
        { ":", TokenKind.Colon }, { ".", TokenKind.Dot }, { "~", TokenKind.Tilde },
        { "'s'", TokenKind.StringLiteral }, { "#c", TokenKind.Comment },
        { "x", TokenKind.Identifier }, { "_", TokenKind.Identifier }, { "e", TokenKind.Identifier }, { "E", TokenKind.Identifier },
        { "div", TokenKind.KeywordDiv }, { "and", TokenKind.KeywordAnd }, { "not", TokenKind.KeywordNot },
        { "@", TokenKind.Bad }, { "!", TokenKind.Bad }, { "\u200B", TokenKind.Bad },
        { " ", TokenKind.EndOfFile }, { "\t", TokenKind.EndOfFile }, { "\n", TokenKind.EndOfFile }, { "\r", TokenKind.EndOfFile },
        { "", TokenKind.EndOfFile },
    };

    [Theory]
    [MemberData(nameof(Followers))]
    public void EveryLiteralShape_EndsBeforeEveryFollowerClass(string follower, TokenKind followerKind)
    {
        foreach (var literal in new[] { "1", "12", "1.5", "1e5", "1e+5", "1e-5", "1_0", "1_0.0_1e1_0" })
        {
            var source = literal + follower;
            var (tokens, _) = Lexer.Tokenize(source);

            Assert.Equal(TokenKind.Number, tokens[0].Kind);
            Assert.Equal(literal, Slice(source, tokens[0]));
            Assert.Equal(followerKind, tokens[1].Kind);
            AssertSameValue(LegacyConvert(literal).Value, tokens[0].NumValue, source);
        }
    }

    // ── Hostile sizes ────────────────────────────────────────────────────────

    [Fact]
    public void VeryLongLiterals_LexAsOneToken_WithoutThrowing()
    {
        // 100,001 digits with a finite magnitude: rounds to 34 significant digits (the
        // 35th digit is a 7, so the last kept digit rounds up).
        var digits = "1." + new string('7', 100_000);
        AssertAgreesWithOracles(digits);
        AssertAgreesWithOracles("X = " + digits + "\nY");
        var (tokens, diagnostics) = Lexer.Tokenize(digits);
        Assert.Empty(diagnostics);
        Assert.Equal(digits.Length, tokens[0].Length);
        Assert.Equal("1.777777777777777777777777777777778", Canonical(tokens[0].NumValue));

        // 100,000 integer digits: the magnitude is far past the finite range, so the
        // whole token is one too-large diagnostic.
        var huge = "1" + new string('0', 99_999);
        AssertAgreesWithOracles(huge);
        var (hugeTokens, hugeDiagnostics) = Lexer.Tokenize(huge);
        Assert.Equal(DiagnosticCode.NumberLiteralTooLarge, Assert.Single(hugeDiagnostics).Code);
        Assert.Equal(huge.Length, hugeTokens[0].Length);

        // 100,000 digits past the point: underflows to zero without a diagnostic.
        var tiny = "0." + new string('0', 100_000) + "1";
        AssertAgreesWithOracles(tiny);
        var (tinyTokens, tinyDiagnostics) = Lexer.Tokenize(tiny);
        Assert.Empty(tinyDiagnostics);
        Assert.Equal("0E-6176", Canonical(tinyTokens[0].NumValue));

        // 100,000 separators between two digits: one token, value 11.
        var separated = "1" + new string('_', 100_000) + "1";
        AssertAgreesWithOracles(separated);
        var (separatedTokens, separatedDiagnostics) = Lexer.Tokenize(separated);
        Assert.Empty(separatedDiagnostics);
        Assert.Equal(separated.Length, separatedTokens[0].Length);
        Assert.Equal("11", Canonical(separatedTokens[0].NumValue));

        // An exponent of 100,000 digits: too large, one diagnostic spanning the token.
        var hugeExponent = "1e" + new string('9', 100_000);
        AssertAgreesWithOracles(hugeExponent);
        var (exponentTokens, exponentDiagnostics) = Lexer.Tokenize(hugeExponent);
        Assert.Equal(DiagnosticCode.NumberLiteralTooLarge, Assert.Single(exponentDiagnostics).Code);
        Assert.Equal(hugeExponent.Length, exponentTokens[0].Length);

        // The same exponent on a zero significand is a finite zero.
        AssertAgreesWithOracles("0e" + new string('9', 100_000));

        // 100,000 separator-heavy literals in one source.
        var many = new StringBuilder();
        for (var i = 0; i < 100_000; i++)
            many.Append("1_0_0, ");
        AssertAgreesWithOracles(many.ToString());
    }

    // ── Allocation contract ──────────────────────────────────────────────────

    [Fact]
    public void PlainLiterals_AllocateNoTextOfTheirOwn()
    {
        // A plain literal parses straight from a span over the source, so a number token
        // costs strictly less than an identifier token of the same length, whose text the
        // token must carry. Both sources have the same token count and layout, so the
        // token records and list growth cancel and the difference is the identifier text.
        const int count = 1000;
        var numbers = string.Join('\n', Enumerable.Range(0, count).Select(static i => $"{i % 10}23456789"));
        var identifiers = string.Join('\n', Enumerable.Range(0, count).Select(static i => $"a{(char)('a' + i % 10)}cdefghi"));
        Assert.Equal(numbers.Length, identifiers.Length);

        // Warm up so JIT-time allocations never count.
        _ = Lexer.Tokenize(numbers);
        _ = Lexer.Tokenize(identifiers);

        var numberBytes = MeasureTokenizeAllocation(numbers, count);
        var identifierBytes = MeasureTokenizeAllocation(identifiers, count);

        // The smallest string object is 24 bytes plus its code units; assert only that
        // the identifier text's share is present and the literal's is not.
        Assert.True(
            identifierBytes - numberBytes >= count * 24L,
            $"Number tokens allocated {numberBytes} bytes against {identifierBytes} for identifiers: numeric literals appear to allocate their text again.");
    }

    private static long MeasureTokenizeAllocation(string source, int expectedTokens)
    {
        var before = GC.GetAllocatedBytesForCurrentThread();
        var (tokens, diagnostics) = Lexer.Tokenize(source);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
        Assert.Empty(diagnostics);
        Assert.Equal(expectedTokens + 1, tokens.Count);
        return allocated;
    }
}
