using KatLang.ParserFuzz;

namespace KatLang.Tests;

/// <summary>
/// The UTF-16 source-text contract, pinned.
///
/// <para>Every relation in the UTF-16 fuzz target rests on the answers below, and several of them
/// are answers a reader would GUESS wrong: a lone carriage return is not a line break, U+2028 is
/// whitespace but not a newline, a surrogate pair is two columns and never an identifier character,
/// a zero-width space is not whitespace at all, and a fullwidth digit starts a number token that
/// cannot then be parsed. None of that is written down anywhere else, so a future change that
/// altered it would be invisible — these tests are where it becomes visible.</para>
///
/// <para>Nothing here asserts that a particular input SHOULD be accepted or rejected. They record
/// what the implementation does today so a deliberate change is a reviewed diff.</para>
/// </summary>
public class Utf16LexerContractTests
{
    // ── Coordinate system ────────────────────────────────────────────────────

    [Fact]
    public void LinesAndColumnsAreOneBased_CountUtf16CodeUnits_AndEndColumnsAreInclusive()
    {
        var (tokens, _) = Lexer.Tokenize("ab\ncd");

        var first = tokens[0];
        Assert.Equal(TokenKind.Identifier, first.Kind);
        Assert.Equal(1, first.Line);
        Assert.Equal(1, first.Column);
        Assert.Equal(0, first.Position);
        Assert.Equal(2, first.Length);

        var second = tokens[1];
        Assert.Equal(2, second.Line);
        Assert.Equal(1, second.Column);
        Assert.Equal(3, second.Position);

        // A diagnostic's end column is INCLUSIVE: a one-unit token spans column c..c.
        var syntax = Parser.ParseSyntax("!");
        var span = Assert.Single(syntax.Diagnostics).Span;
        Assert.Equal(1, span.StartColumn);
        Assert.Equal(1, span.EndColumn);
    }

    [Fact]
    public void ColumnsCountCodeUnits_NotScalars_NotGraphemes_NotDisplayWidth()
    {
        // One supplementary-plane character is TWO columns, because the parser indexes code units.
        var (pairTokens, _) = Lexer.Tokenize("\uD83D\uDE00b");
        var identifier = pairTokens.Single(t => t.Kind == TokenKind.Identifier);
        Assert.Equal(3, identifier.Column);

        // A combining mark is its own column: "e" + U+0301 is two columns, not one grapheme.
        var (markTokens, _) = Lexer.Tokenize("e\u0301b");
        Assert.Equal(1, markTokens[0].Column);          // "e"
        Assert.Equal(2, markTokens[1].Column);          // the combining mark, a Bad token
        Assert.Equal(3, markTokens[2].Column);          // "b"

        // A tab is ONE column: columns are not tab-expanded.
        var (tabTokens, _) = Lexer.Tokenize("\ta");
        Assert.Equal(2, tabTokens[0].Column);
    }

    [Fact]
    public void TheEndOfFileTokenSitsOnePastTheLastCodeUnit()
    {
        foreach (var source in new[] { "", "a", "a\n", "a\nb", "a\r\nb", "\uD83D" })
        {
            var (tokens, _) = Lexer.Tokenize(source);
            var eof = tokens[^1];
            Assert.Equal(TokenKind.EndOfFile, eof.Kind);
            Assert.Equal(source.Length, eof.Position);
            Assert.Equal(0, eof.Length);

            var (line, column) = SourceSpanValidator.LineColumnAt(source, source.Length);
            Assert.Equal(line, eof.Line);
            Assert.Equal(column, eof.Column);
        }
    }

    // ── Line endings ─────────────────────────────────────────────────────────

    [Fact]
    public void OnlyLineFeedStartsANewLine_AndCarriageReturnIsTransparent()
    {
        // CRLF: the CR occupies no column, so the next line starts at column 1 exactly as with LF.
        var (crlf, _) = Lexer.Tokenize("a\r\nb");
        Assert.Equal((1, 1), (crlf[0].Line, crlf[0].Column));
        Assert.Equal((2, 1), (crlf[1].Line, crlf[1].Column));

        // A LONE carriage return is NOT a line break: everything stays on line 1, and the CR does
        // not advance the column either, so 'b' lands where it would with no separator at all.
        var (loneCr, _) = Lexer.Tokenize("a\rb");
        Assert.Equal((1, 1), (loneCr[0].Line, loneCr[0].Column));
        Assert.Equal((1, 2), (loneCr[1].Line, loneCr[1].Column));

        // Repeated carriage returns stay transparent however many there are.
        var (manyCr, _) = Lexer.Tokenize("a\r\r\r\rb");
        Assert.Equal((1, 2), (manyCr[1].Line, manyCr[1].Column));
    }

    [Theory]
    [InlineData('\u2028', "LINE SEPARATOR")]
    [InlineData('\u2029', "PARAGRAPH SEPARATOR")]
    [InlineData('\u0085', "NEXT LINE")]
    [InlineData('\u000B', "VERTICAL TAB")]
    [InlineData('\u000C', "FORM FEED")]
    [InlineData('\u00A0', "NO-BREAK SPACE")]
    [InlineData('\u2000', "EN QUAD")]
    [InlineData('\u3000', "IDEOGRAPHIC SPACE")]
    public void UnicodeWhitespaceIsWhitespaceButNeverAKatLangLineBreak(char separator, string name)
    {
        // These are all .NET whitespace, so they SEPARATE tokens — but KatLang's line boundary is
        // '\n' alone, so none of them starts a new line, and each one costs exactly one column.
        var (tokens, diagnostics) = Lexer.Tokenize($"a{separator}b");

        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.Identifier, tokens[0].Kind);
        Assert.Equal(TokenKind.Identifier, tokens[1].Kind);
        Assert.Equal(1, tokens[1].Line);
        Assert.Equal(3, tokens[1].Column);
        Assert.True(char.IsWhiteSpace(separator), name);
    }

    [Theory]
    [InlineData('\u200B', "ZERO WIDTH SPACE")]
    [InlineData('\u200D', "ZERO WIDTH JOINER")]
    [InlineData('\uFEFF', "ZERO WIDTH NO-BREAK SPACE / BOM")]
    public void ZeroWidthFormatCharactersAreNotWhitespaceAndBecomeBadTokens(char format, string name)
    {
        // Category Cf, not whitespace: the lexer has no rule for them, so they take the
        // unexpected-character path. A BOM in the middle of a file is a diagnostic, not trivia.
        var (tokens, diagnostics) = Lexer.Tokenize($"a{format}b");

        Assert.False(char.IsWhiteSpace(format), name);
        Assert.Contains(tokens, t => t.Kind == TokenKind.Bad);
        var diagnostic = Assert.Single(diagnostics);
        Assert.StartsWith("Unexpected character:", diagnostic.Message, StringComparison.Ordinal);
        Assert.Equal(2, diagnostic.Span.StartColumn);
        Assert.Equal(2, diagnostic.Span.EndColumn);
    }

    // ── Identifiers ──────────────────────────────────────────────────────────

    [Theory]
    [InlineData("\u0101")]      // a-macron
    [InlineData("\u010D")]      // c-caron
    [InlineData("\u0113")]      // e-macron
    [InlineData("\u0123")]      // g-cedilla
    [InlineData("\u012B")]      // i-macron
    [InlineData("\u0137")]      // k-cedilla
    [InlineData("\u013C")]      // l-cedilla
    [InlineData("\u0146")]      // n-cedilla
    [InlineData("\u0161")]      // s-caron
    [InlineData("\u016B")]      // u-macron
    [InlineData("\u017E")]      // z-caron
    [InlineData("\u0100\u010C\u0112")]                  // uppercase run
    [InlineData("Sve\u0161\u016Bd\u0101")]              // a mixed Latvian word
    [InlineData("\u03B1\u03B2")]                        // Greek
    [InlineData("\u0416\u0438")]                        // Cyrillic
    [InlineData("\u4E2D")]                              // ideographic
    [InlineData("\u2115")]                              // a LETTER by category, though it looks symbolic
    public void LettersOfAnyScriptAreIdentifierCharacters(string text)
    {
        var (tokens, diagnostics) = Lexer.Tokenize(text);

        Assert.Empty(diagnostics);
        var identifier = Assert.Single(tokens, t => t.Kind == TokenKind.Identifier);
        Assert.Equal(text, identifier.StringValue);
        Assert.Equal(text.Length, identifier.Length);
    }

    [Fact]
    public void SurrogatePairsAreNeverIdentifierCharacters_BecauseTheTestIsPerCodeUnit()
    {
        // U+1D400 MATHEMATICAL BOLD CAPITAL A is an uppercase LETTER as a scalar value, but the
        // lexer classifies one code unit at a time and neither half of a pair is a letter. Both
        // halves therefore become bad tokens. This is a code-unit-level contract, not an oversight
        // to route around: changing it is a language-design decision.
        var (tokens, diagnostics) = Lexer.Tokenize("\uD835\uDC00");

        Assert.Equal(2, diagnostics.Count);
        Assert.Equal(2, tokens.Count(t => t.Kind == TokenKind.Bad));
        Assert.DoesNotContain(tokens, t => t.Kind == TokenKind.Identifier);
        Assert.Equal(1, tokens[0].Column);
        Assert.Equal(2, tokens[1].Column);
    }

    [Fact]
    public void CombiningMarksAreNotIdentifierCharacters()
    {
        // "e" + COMBINING ACUTE lexes as an identifier followed by a bad token, while the
        // PRECOMPOSED form is a single identifier. The two are deliberately NOT equivalent: nothing
        // normalizes source text, so a decomposed name and a precomposed one are different sources.
        var (decomposed, decomposedDiagnostics) = Lexer.Tokenize("e\u0301");
        Assert.Single(decomposedDiagnostics);
        Assert.Equal("e", decomposed[0].StringValue);
        Assert.Equal(TokenKind.Bad, decomposed[1].Kind);

        var (precomposed, precomposedDiagnostics) = Lexer.Tokenize("\u00E9");
        Assert.Empty(precomposedDiagnostics);
        Assert.Equal("\u00E9", precomposed[0].StringValue);
    }

    [Fact]
    public void DigitsAndUnderscoresContinueAnIdentifierButNeverStartOne()
    {
        var (tokens, _) = Lexer.Tokenize("a1_b");
        Assert.Equal("a1_b", Assert.Single(tokens, t => t.Kind == TokenKind.Identifier).StringValue);

        var (leadingUnderscore, underscoreDiagnostics) = Lexer.Tokenize("_ab");
        Assert.Empty(underscoreDiagnostics);
        Assert.Equal("_ab", leadingUnderscore[0].StringValue);

        var (leadingDigit, _) = Lexer.Tokenize("1ab");
        Assert.Equal(TokenKind.Number, leadingDigit[0].Kind);
        Assert.Equal(TokenKind.Identifier, leadingDigit[1].Kind);
    }

    // ── Numbers ──────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("\uFF10")]      // FULLWIDTH DIGIT ZERO
    [InlineData("\u0660")]      // ARABIC-INDIC DIGIT ZERO
    [InlineData("1\u0662")]     // ASCII digit followed by a non-ASCII one
    public void NonAsciiDecimalDigitsStartANumberTokenThatCannotBeParsed(string text)
    {
        // char.IsDigit is true for every Unicode decimal digit, so the lexer takes the number path;
        // decimal.TryParse under the invariant culture only accepts ASCII digits, so it then fails.
        // The result is a deterministic, positioned diagnostic — but one whose WORDING names the
        // wrong cause. Recorded here rather than changed: the acceptance behaviour is the contract,
        // and rewording a public diagnostic is a separate, reviewed decision.
        Assert.True(char.IsDigit(text[^1]));

        var (tokens, diagnostics) = Lexer.Tokenize(text);
        Assert.Equal(TokenKind.Number, tokens[0].Kind);
        Assert.Equal(text.Length, tokens[0].Length);

        var diagnostic = Assert.Single(diagnostics);
        Assert.Equal("Number literal is too large.", diagnostic.Message);
        Assert.Equal(1, diagnostic.Span.StartColumn);
    }

    [Fact]
    public void AGenuinelyTooLargeLiteralGivesTheSameDiagnostic()
    {
        // The same message for a genuinely out-of-range literal, which is why the wording above is
        // indistinguishable from this case rather than merely imprecise.
        var (_, diagnostics) = Lexer.Tokenize(new string('9', 40));
        Assert.Equal("Number literal is too large.", Assert.Single(diagnostics).Message);
    }

    // ── String literals ──────────────────────────────────────────────────────

    [Fact]
    public void StringLiteralsHaveNoEscapeSequences()
    {
        // A backslash inside a literal is an ordinary code unit; there is no escaping at all.
        var (tokens, diagnostics) = Lexer.Tokenize(@"'a\nb'");
        Assert.Empty(diagnostics);
        Assert.Equal("a\\nb", Assert.Single(tokens, t => t.Kind == TokenKind.StringLiteral).StringValue);

        // Outside a literal the same backslash is an unexpected character.
        var (_, outside) = Lexer.Tokenize("\\");
        Assert.Single(outside);
    }

    [Fact]
    public void StringLiteralsEndAtAQuote_ALineFeed_OrACarriageReturn()
    {
        Assert.Equal("ab", ValueOf("'ab'"));
        Assert.Equal("ab", ValueOf("'ab"));            // unterminated at end of file
        Assert.Equal("ab", ValueOf("'ab\ncd'"));       // a line feed ends it
        Assert.Equal("ab", ValueOf("'ab\rcd'"));       // and so does a lone carriage return
        Assert.Equal("", ValueOf("''"));
        Assert.Equal("", ValueOf("'"));

        foreach (var unterminated in new[] { "'ab", "'ab\ncd'", "'ab\rcd'" })
            Assert.Contains(
                Lexer.Tokenize(unterminated).Diagnostics,
                d => string.Equals(d.Message, "Unterminated string literal.", StringComparison.Ordinal));
    }

    [Fact]
    public void StringLiteralsCarryTheirCodeUnitsThroughToTheEvaluatedValue()
    {
        // Isolated surrogates included: nothing on the path validates or replaces a code unit, and
        // the string's Length is its UTF-16 code-unit count.
        Assert.Equal("\uD83D\uDE00", Evaluate("'\uD83D\uDE00'"));
        Assert.Equal("\uD83D", Evaluate("'\uD83D'"));
        Assert.Equal("\uDE00", Evaluate("'\uDE00'"));
        Assert.Equal("\uDE00\uD83D", Evaluate("'\uDE00\uD83D'"));
        Assert.Equal("\u0000", Evaluate("'\u0000'"));   // NUL is ordinary content
        Assert.Equal("\u00A0", Evaluate("'\u00A0'"));       // and so is a no-break space
        Assert.Equal(2, Evaluate("'\uD83D\uDE00'").Length);
        Assert.Equal(1, Evaluate("'\uD83D'").Length);

        // Precomposed and decomposed forms stay distinct all the way to the value.
        Assert.Equal(1, Evaluate("'\u00E9'").Length);
        Assert.Equal(2, Evaluate("'e\u0301'").Length);
        Assert.NotEqual(Evaluate("'\u00E9'"), Evaluate("'e\u0301'"));
    }

    // ── Comments ─────────────────────────────────────────────────────────────

    [Fact]
    public void CommentsRunToALineFeedOrACarriageReturn_AndThereAreNoBlockComments()
    {
        Assert.Equal(" x", CommentOf("// x\n1"));
        Assert.Equal(" x", CommentOf("// x\r\n1"));
        Assert.Equal(" x", CommentOf("// x\rP = 1"));
        Assert.Equal(" x", CommentOf("// x"));                    // running to end of file

        // There is no /* ... */ form: the characters lex individually.
        var (_, diagnostics) = Lexer.Tokenize("/* x */");
        Assert.Empty(diagnostics);                                // '/' and '*' are real operators
        var (tokens, _) = Lexer.Tokenize("/* x */");
        Assert.DoesNotContain(tokens, t => t.Kind == TokenKind.Comment);
    }

    [Fact]
    public void CommentTextIsTheExactSourceSliceAndCannotDisturbTheFollowingToken()
    {
        const string source = "// \uD83D \u0301\n1";
        var (tokens, _) = Lexer.Tokenize(source);

        var comment = Assert.Single(tokens, t => t.Kind == TokenKind.Comment);
        Assert.Equal(" \uD83D \u0301", comment.StringValue);
        Assert.Equal(source[comment.Position..(comment.Position + comment.Length)][2..], comment.StringValue);

        // The token after the comment is exactly where it would be without it.
        var following = Assert.Single(tokens, t => t.Kind == TokenKind.Number);
        Assert.Equal(2, following.Line);
        Assert.Equal(1, following.Column);
    }

    [Fact]
    public void ACommentOnlySourceIsDeterministicAndProducesNoProgram()
    {
        var syntax = Parser.ParseSyntax("// only a comment");
        Assert.Empty(syntax.Diagnostics);

        var again = Parser.ParseSyntax("// only a comment");
        Assert.Equal(
            FrontEndFingerprint.ComputeParseResult(syntax.Root, syntax.Diagnostics),
            FrontEndFingerprint.ComputeParseResult(again.Root, again.Diagnostics));
    }

    // ── Diagnostics ──────────────────────────────────────────────────────────

    [Fact]
    public void AnUnexpectedCharacterDiagnosticQuotesTheOffendingCodeUnitVerbatim()
    {
        // The message embeds the code unit itself, so for an isolated surrogate the message string
        // is ill-formed UTF-16 — faithful in memory, and something any UTF-8 boundary downstream
        // will render as U+FFFD. Pinned because it is a real characteristic of the public
        // diagnostic surface, not because it is necessarily the last word on the subject.
        var (_, diagnostics) = Lexer.Tokenize("\uD83D");
        var message = Assert.Single(diagnostics).Message;

        Assert.Equal("Unexpected character: '\uD83D'.", message);
        Assert.Contains('\uD83D', message);
        Assert.DoesNotContain('\uFFFD', message);
    }

    [Fact]
    public void EveryLexerDiagnosticSpanIsInRangeForItsSource()
    {
        foreach (var source in new[]
                 {
                     "\uD83D", "\uDE00", "\uD83D\uDE00", " ", "\u0301", "\uFEFF",
                     "'\uD83D", "// \uD83D", "a\rb\uD83D", "\uD83D\n\uDE00", "\uFF10", "!",
                 })
        {
            var widths = SourceSpanValidator.LineWidths(source);
            var (_, diagnostics) = Lexer.Tokenize(source);
            foreach (var diagnostic in diagnostics)
                Assert.Null(SourceSpanValidator.Validate(diagnostic.Span, widths));
        }
    }

    // ── Helpers ──────────────────────────────────────────────────────────────

    /// <summary>The FIRST string-literal token: a literal ended by a line break leaves the rest of
    /// the line to be lexed as ordinary source, which usually opens a second literal.</summary>
    private static string? ValueOf(string source)
        => Lexer.Tokenize(source).Tokens.First(t => t.Kind == TokenKind.StringLiteral).StringValue;

    private static string? CommentOf(string source)
        => Lexer.Tokenize(source).Tokens.Single(t => t.Kind == TokenKind.Comment).StringValue;

    private static string Evaluate(string source)
    {
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        return Assert.IsType<Result.Str>(success.Value).Value;
    }
}
