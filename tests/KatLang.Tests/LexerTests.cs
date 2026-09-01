namespace KatLang.Tests;

public class LexerTests
{
    [Fact]
    public void Tokenize_EmptySource_ReturnsOnlyEof()
    {
        var (tokens, diagnostics) = Lexer.Tokenize("");

        Assert.Single(tokens);
        Assert.Equal(TokenKind.EndOfFile, tokens[0].Kind);
        Assert.Empty(diagnostics);
    }

    [Fact]
    public void Tokenize_WhitespaceOnly_ReturnsOnlyEof()
    {
        var (tokens, diagnostics) = Lexer.Tokenize("   \t\n  ");

        Assert.Single(tokens);
        Assert.Equal(TokenKind.EndOfFile, tokens[0].Kind);
        Assert.Empty(diagnostics);
    }

    [Fact]
    public void Tokenize_Integer_ReturnsNumberToken()
    {
        var (tokens, _) = Lexer.Tokenize("42");

        Assert.Equal(2, tokens.Count);
        Assert.Equal(TokenKind.Number, tokens[0].Kind);
        Assert.Equal(42, tokens[0].NumValue);
    }

    [Fact]
    public void Tokenize_LargeInteger_ReturnsCorrectValue()
    {
        var (tokens, _) = Lexer.Tokenize("9876543210");

        Assert.Equal(TokenKind.Number, tokens[0].Kind);
        Assert.Equal(9876543210L, tokens[0].NumValue);
    }

    [Fact]
    public void Tokenize_Identifier_ReturnsIdentifierToken()
    {
        var (tokens, _) = Lexer.Tokenize("foo");

        Assert.Equal(TokenKind.Identifier, tokens[0].Kind);
        Assert.Equal("foo", tokens[0].StringValue);
    }

    [Fact]
    public void Tokenize_IdentifierWithUnderscore_ReturnsIdentifierToken()
    {
        var (tokens, _) = Lexer.Tokenize("foo_bar_123");

        Assert.Equal(TokenKind.Identifier, tokens[0].Kind);
        Assert.Equal("foo_bar_123", tokens[0].StringValue);
    }

    [Fact]
    public void Tokenize_SelfKeyword_NowParsesAsIdentifier()
    {
        var (tokens, _) = Lexer.Tokenize("self");
        Assert.Equal(TokenKind.Identifier, tokens[0].Kind);
        Assert.Equal("self", tokens[0].StringValue);
    }

    [Fact]
    public void Tokenize_Operators_ReturnsCorrectTokens()
    {
        var (tokens, _) = Lexer.Tokenize("+ - * < >");

        Assert.Equal(TokenKind.Plus, tokens[0].Kind);
        Assert.Equal(TokenKind.Minus, tokens[1].Kind);
        Assert.Equal(TokenKind.Star, tokens[2].Kind);
        Assert.Equal(TokenKind.LessThan, tokens[3].Kind);
        Assert.Equal(TokenKind.GreaterThan, tokens[4].Kind);
    }

    [Fact]
    public void Tokenize_Delimiters_ReturnsCorrectTokens()
    {
        var (tokens, _) = Lexer.Tokenize("( ) { } ,");

        Assert.Equal(TokenKind.LParen, tokens[0].Kind);
        Assert.Equal(TokenKind.RParen, tokens[1].Kind);
        Assert.Equal(TokenKind.LBrace, tokens[2].Kind);
        Assert.Equal(TokenKind.RBrace, tokens[3].Kind);
        Assert.Equal(TokenKind.Comma, tokens[4].Kind);
    }

    [Fact]
    public void Tokenize_Brackets_ReturnsBracketTokens()
    {
        var (tokens, diagnostics) = Lexer.Tokenize("[1, 2]");

        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.LBracket, tokens[0].Kind);
        Assert.Equal(TokenKind.Number, tokens[1].Kind);
        Assert.Equal(TokenKind.Comma, tokens[2].Kind);
        Assert.Equal(TokenKind.Number, tokens[3].Kind);
        Assert.Equal(TokenKind.RBracket, tokens[4].Kind);
    }

    [Fact]
    public void Tokenize_TripleDots_AreThreeOrdinaryDotTokens()
    {
        // The language has no ellipsis token: `...` lexes as three Dot tokens
        // and fails through ordinary parser handling.
        var (tokens, diagnostics) = Lexer.Tokenize("A...B");

        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.Identifier, tokens[0].Kind);
        Assert.Equal(TokenKind.Dot, tokens[1].Kind);
        Assert.Equal(TokenKind.Dot, tokens[2].Kind);
        Assert.Equal(TokenKind.Dot, tokens[3].Kind);
        Assert.Equal(TokenKind.Identifier, tokens[4].Kind);
    }

    [Theory]
    [InlineData("*items", 0, 1, 1, 5)]
    [InlineData("* items", 0, 1, 2, 5)]
    [InlineData("*\nitems", 0, 1, 2, 5)]
    public void Tokenize_StarAndIdentifier_RemainDistinctTokensWithExactOffsets(
        string source,
        int markerPosition,
        int markerLength,
        int namePosition,
        int nameLength)
    {
        // The collect marker is a plain Star token; attachment is decided by
        // the parser from exact source offsets (Position/Length), so the
        // lexer must record them precisely for all three spacing shapes.
        var (tokens, diagnostics) = Lexer.Tokenize(source);

        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.Star, tokens[0].Kind);
        Assert.Equal(markerPosition, tokens[0].Position);
        Assert.Equal(markerLength, tokens[0].Length);
        Assert.Equal(TokenKind.Identifier, tokens[1].Kind);
        Assert.Equal(namePosition, tokens[1].Position);
        Assert.Equal(nameLength, tokens[1].Length);
    }

    [Fact]
    public void Tokenize_SpecialTokens_ReturnsCorrectTokens()
    {
        var (tokens, _) = Lexer.Tokenize("= : .");

        Assert.Equal(TokenKind.Equals, tokens[0].Kind);
        Assert.Equal(TokenKind.Colon, tokens[1].Kind);
        Assert.Equal(TokenKind.Dot, tokens[2].Kind);
    }

    [Fact]
    public void Tokenize_Comment_IsEmittedAsCommentToken()
    {
        // Comments are preserved in the token stream so consumers (e.g. colorizers) can use them.
        // The parser skips them via its navigation helpers.
        var source = """
            1 # this is a comment
            2
            """;
        var (tokens, _) = Lexer.Tokenize(source);

        // Number(1), Comment, Number(2), EOF
        Assert.Equal(4, tokens.Count);
        Assert.Equal(TokenKind.Number,  tokens[0].Kind);
        Assert.Equal(1,                 tokens[0].NumValue);
        Assert.Equal(TokenKind.Comment, tokens[1].Kind);
        Assert.Equal(TokenKind.Number,  tokens[2].Kind);
        Assert.Equal(2,                 tokens[2].NumValue);
        Assert.Equal(TokenKind.EndOfFile, tokens[3].Kind);
    }

    [Fact]
    public void Tokenize_Comment_TokenCarriesTextAndPosition()
    {
        var (tokens, _) = Lexer.Tokenize("1 # hello");

        var comment = Assert.Single(tokens, t => t.Kind == TokenKind.Comment);
        Assert.Equal(" hello", comment.StringValue);  // text after #
        Assert.Equal(2, comment.Position);             // starts at offset of '#'
        Assert.Equal(1, comment.Line);
        Assert.Equal(3, comment.Column);
    }

    [Fact]
    public void Tokenize_FloatingPoint_ReturnsNumberToken()
    {
        var (tokens, diagnostics) = Lexer.Tokenize("3.14");

        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.Number, tokens[0].Kind);
        Assert.Equal(3.14m, tokens[0].NumValue);
    }

    [Fact]
    public void Tokenize_UnexpectedCharacter_ReportsError()
    {
        var (tokens, diagnostics) = Lexer.Tokenize("@");

        Assert.Single(diagnostics);
        Assert.Contains("Unexpected character", diagnostics[0].Message);
        Assert.Equal(TokenKind.Bad, tokens[0].Kind);
        Assert.Equal(1, diagnostics[0].Span.StartLineNumber);
        Assert.Equal(1, diagnostics[0].Span.StartColumn);
        Assert.Equal(1, diagnostics[0].Span.EndLineNumber);
        Assert.Equal(1, diagnostics[0].Span.EndColumn);
    }

    [Fact]
    public void Tokenize_ComplexExpression_ReturnsAllTokens()
    {
        var (tokens, _) = Lexer.Tokenize("X = a + 1, b * 2");

        var kinds = tokens.Select(t => t.Kind).ToList();
        Assert.Equal(
            [TokenKind.Identifier, TokenKind.Equals, TokenKind.Identifier, TokenKind.Plus,
             TokenKind.Number, TokenKind.Comma, TokenKind.Identifier, TokenKind.Star,
             TokenKind.Number, TokenKind.EndOfFile],
            kinds);
    }

    [Fact]
    public void Tokenize_TokenPositions_AreCorrect()
    {
        var (tokens, _) = Lexer.Tokenize("ab + cd");

        Assert.Equal(0, tokens[0].Position);
        Assert.Equal(2, tokens[0].Length);
        Assert.Equal(1, tokens[0].Line);
        Assert.Equal(1, tokens[0].Column);

        Assert.Equal(3, tokens[1].Position);
        Assert.Equal(1, tokens[1].Length);
        Assert.Equal(1, tokens[1].Line);
        Assert.Equal(4, tokens[1].Column);

        Assert.Equal(5, tokens[2].Position);
        Assert.Equal(2, tokens[2].Length);
        Assert.Equal(1, tokens[2].Line);
        Assert.Equal(6, tokens[2].Column);
    }

    // ── Grace/Tilde token tests ──────────────────────────────────────────────

    [Fact]
    public void Tokenize_Tilde_ReturnsTildeToken()
    {
        var (tokens, diagnostics) = Lexer.Tokenize("~");

        Assert.Empty(diagnostics);
        Assert.Equal(2, tokens.Count);
        Assert.Equal(TokenKind.Tilde, tokens[0].Kind);
        Assert.Equal(0, tokens[0].Position);
        Assert.Equal(1, tokens[0].Length);
        Assert.Equal(1, tokens[0].Line);
        Assert.Equal(1, tokens[0].Column);
    }

    [Fact]
    public void Tokenize_MultilineSource_TracksLineAndColumn()
    {
        // "ab" is on line 1, col 1; "cd" is on line 2, col 1; "+" is on line 2, col 4
        var (tokens, _) = Lexer.Tokenize("ab\ncd + ef");

        Assert.Equal(1, tokens[0].Line);  // ab
        Assert.Equal(1, tokens[0].Column);
        Assert.Equal(2, tokens[1].Line);  // cd
        Assert.Equal(1, tokens[1].Column);
        Assert.Equal(2, tokens[2].Line);  // +
        Assert.Equal(4, tokens[2].Column);
        Assert.Equal(2, tokens[3].Line);  // ef
        Assert.Equal(6, tokens[3].Column);
    }

    [Fact]
    public void Tokenize_MultilineError_SpanReflectsCorrectLine()
    {
        // "@" is on line 2, col 3
        var (_, diagnostics) = Lexer.Tokenize("ab\n  @");

        Assert.Single(diagnostics);
        Assert.Equal(2, diagnostics[0].Span.StartLineNumber);
        Assert.Equal(3, diagnostics[0].Span.StartColumn);
        Assert.Equal(2, diagnostics[0].Span.EndLineNumber);
        Assert.Equal(3, diagnostics[0].Span.EndColumn);
    }

    [Fact]
    public void Tokenize_TildeBeforeIdentifier_ReturnsTwoTokens()
    {
        var (tokens, _) = Lexer.Tokenize("~x");

        var kinds = tokens.Select(t => t.Kind).ToList();
        Assert.Equal([TokenKind.Tilde, TokenKind.Identifier, TokenKind.EndOfFile], kinds);
    }

    [Fact]
    public void Tokenize_IdentifierThenTilde_ReturnsTwoTokens()
    {
        var (tokens, _) = Lexer.Tokenize("x~");

        var kinds = tokens.Select(t => t.Kind).ToList();
        Assert.Equal([TokenKind.Identifier, TokenKind.Tilde, TokenKind.EndOfFile], kinds);
    }

    [Fact]
    public void Tokenize_MultipleTildes_ReturnsMultipleTildeTokens()
    {
        var (tokens, _) = Lexer.Tokenize("~~x");

        var kinds = tokens.Select(t => t.Kind).ToList();
        Assert.Equal([TokenKind.Tilde, TokenKind.Tilde, TokenKind.Identifier, TokenKind.EndOfFile], kinds);
    }

    [Fact]
    public void Tokenize_OverflowingNumber_ReportsDiagnosticInsteadOfCrashing()
    {
        // 1e6145 parses to an infinity (past Decimal128's finite range); a
        // 30-digit integer like the old probe literal is now representable.
        var (tokens, diagnostics) = Lexer.Tokenize("1e6145");

        Assert.Single(diagnostics);
        Assert.Equal(DiagnosticSeverity.Error, diagnostics[0].Severity);
        Assert.Contains("too large", diagnostics[0].Message);
        // A placeholder token is still emitted so the parser can continue
        Assert.Equal(TokenKind.Number, tokens[0].Kind);
    }

    [Fact]
    public void Tokenize_OverflowingNumber_InExpression_DoesNotCrash()
    {
        var (tokens, diagnostics) = Lexer.Tokenize("2/1e6145");

        Assert.Single(diagnostics);
        Assert.Contains("too large", diagnostics[0].Message);
        // Tokens: Number(2), Slash, Number(0-placeholder), EOF
        Assert.Equal(4, tokens.Count);
    }

    [Fact]
    public void Tokenize_30DigitInteger_IsNowRepresentable()
    {
        // This exact literal was System.Decimal's overflow probe; Decimal128
        // parses it directly and exactly.
        var (tokens, diagnostics) = Lexer.Tokenize("999999999999999999999999999999");

        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.Number, tokens[0].Kind);
        Assert.Equal(
            System.Numerics.Decimal128.Parse("999999999999999999999999999999", System.Globalization.CultureInfo.InvariantCulture),
            tokens[0].NumValue);
    }

    // ── Digit separator (_) tests ────────────────────────────────────────────

    [Theory]
    [InlineData("1_000",        1000)]
    [InlineData("1_000_000",    1000000)]
    [InlineData("1_2_3",        123)]
    [InlineData("1__2",         12)]
    [InlineData("9_8_7_6",      9876)]
    public void Tokenize_IntegerWithUnderscores_ReturnsCorrectValue(string source, decimal expected)
    {
        var (tokens, diagnostics) = Lexer.Tokenize(source);

        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.Number, tokens[0].Kind);
        Assert.Equal(expected, tokens[0].NumValue);
    }

    [Theory]
    [InlineData("3.14_15",   "3.1415")]
    [InlineData("1_2.3_4",   "12.34")]
    [InlineData("0.000_1",   "0.0001")]
    public void Tokenize_DecimalWithUnderscores_ReturnsCorrectValue(string source, string expectedStr)
    {
        var expected = decimal.Parse(expectedStr, System.Globalization.CultureInfo.InvariantCulture);
        var (tokens, diagnostics) = Lexer.Tokenize(source);

        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.Number, tokens[0].Kind);
        Assert.Equal(expected, tokens[0].NumValue);
    }

    [Fact]
    public void Tokenize_TrailingUnderscore_TreatedAsNumberThenIdentifier()
    {
        // "1_" → Number(1) then Identifier("_") — trailing _ is not part of the literal
        var (tokens, diagnostics) = Lexer.Tokenize("1_");

        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.Number, tokens[0].Kind);
        Assert.Equal(1m, tokens[0].NumValue);
        Assert.Equal(TokenKind.Identifier, tokens[1].Kind);
        Assert.Equal("_", tokens[1].StringValue);
    }

    [Fact]
    public void Tokenize_UnderscoreAdjacentToDecimalPoint_TreatedAsNumberThenIdentifier()
    {
        // "1_.2" → Number(1), Identifier("_"), Dot, Number(2) — _ not consumed into literal
        var (tokens, diagnostics) = Lexer.Tokenize("1_.2");

        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.Number, tokens[0].Kind);
        Assert.Equal(1m, tokens[0].NumValue);
        Assert.Equal(TokenKind.Identifier, tokens[1].Kind);
    }

    // ── Scientific notation tests ────────────────────────────────────────────

    [Theory]
    [InlineData("7e3",    7000)]
    [InlineData("7e+3",   7000)]
    [InlineData("1e0",    1)]
    [InlineData("1e1",    10)]
    [InlineData("2e10",   20000000000L)]
    public void Tokenize_ScientificNotation_NonNegativeExponent_ReturnsCorrectValue(string source, decimal expected)
    {
        var (tokens, diagnostics) = Lexer.Tokenize(source);

        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.Number, tokens[0].Kind);
        Assert.Equal(expected, tokens[0].NumValue);
    }

    [Theory]
    [InlineData("7e-3",   "0.007")]
    [InlineData("3e-1",   "0.3")]
    [InlineData("1.5e-2", "0.015")]
    public void Tokenize_ScientificNotation_NegativeExponent_ReturnsCorrectValue(string source, string expectedStr)
    {
        var expected = decimal.Parse(expectedStr, System.Globalization.CultureInfo.InvariantCulture);
        var (tokens, diagnostics) = Lexer.Tokenize(source);

        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.Number, tokens[0].Kind);
        Assert.Equal(expected, tokens[0].NumValue);
    }

    [Theory]
    [InlineData("1.5e2",  150)]
    [InlineData("2.5e1",  25)]
    public void Tokenize_ScientificNotation_WithDecimal_ReturnsCorrectValue(string source, decimal expected)
    {
        var (tokens, diagnostics) = Lexer.Tokenize(source);

        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.Number, tokens[0].Kind);
        Assert.Equal(expected, tokens[0].NumValue);
    }

    [Theory]
    [InlineData("1_0e3",   10000)]
    [InlineData("1_5e-2",  "0.15")]
    [InlineData("7e1_0",   70000000000L)]
    public void Tokenize_ScientificNotation_WithUnderscores_ReturnsCorrectValue(string source, object expectedObj)
    {
        var expected = expectedObj is string s
            ? decimal.Parse(s, System.Globalization.CultureInfo.InvariantCulture)
            : Convert.ToDecimal(expectedObj);
        var (tokens, diagnostics) = Lexer.Tokenize(source);

        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.Number, tokens[0].Kind);
        Assert.Equal(expected, tokens[0].NumValue);
    }

    [Fact]
    public void Tokenize_UppercaseE_NotScientificNotation()
    {
        // Only lowercase 'e' is the scientific notation marker; 'E' starts an identifier
        var (tokens, diagnostics) = Lexer.Tokenize("7E3");

        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.Number,     tokens[0].Kind);
        Assert.Equal(7m,                   tokens[0].NumValue);
        Assert.Equal(TokenKind.Identifier, tokens[1].Kind);
        Assert.Equal("E3",                 tokens[1].StringValue);
    }

    [Fact]
    public void Tokenize_EWithNoDigit_BacktracksToPlainNumber()
    {
        // "7e" → Number(7) + Identifier("e")
        var (tokens, diagnostics) = Lexer.Tokenize("7e");

        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.Number,     tokens[0].Kind);
        Assert.Equal(7m,                   tokens[0].NumValue);
        Assert.Equal(TokenKind.Identifier, tokens[1].Kind);
        Assert.Equal("e",                  tokens[1].StringValue);
    }

    [Fact]
    public void Tokenize_UnderscoreAdjacentToE_NotConsumedIntoLiteral()
    {
        // "7e_3" → e is followed by _ (not a digit) → backtrack; "e_3" becomes identifier
        var (tokens, diagnostics) = Lexer.Tokenize("7e_3");

        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.Number,     tokens[0].Kind);
        Assert.Equal(7m,                   tokens[0].NumValue);
        Assert.Equal(TokenKind.Identifier, tokens[1].Kind);
        Assert.Equal("e_3",                tokens[1].StringValue);
    }

    // ── Identifier contract ──────────────────────────────────────────────────
    // The shipped identifier policy, pinned as a hand-authored table: start =
    // underscore or a UTF-16 code unit char.IsLetter accepts (Lu/Ll/Lt/Lm/Lo);
    // continuation additionally accepts Unicode decimal digits (Nd); the whole
    // word must not be a reserved keyword. Classification is per UTF-16 code
    // unit, so surrogate pairs (supplementary-plane letters, emoji) and
    // combining marks are never identifier characters and nothing normalizes
    // source text. Every row is asserted BOTH against IsValidIdentifier and
    // against real tokenization, so the whole-string helper and the tokenizer
    // scan loop cannot drift apart without a failure here.

    /// <summary>(display, text, valid): hand-authored identifier contract rows.
    /// Tricky code units are composed from explicit code points so the file
    /// stays reviewable; none of the rows is a reserved keyword (keywords are
    /// pinned separately — they tokenize as ONE keyword token, not as an
    /// identifier and not as an error).</summary>
    private static readonly (string Display, string Text, bool Valid)[] IdentifierContractRows =
    [
        // Accepted: ASCII shapes.
        ("ASCII name", "x", true),
        ("ASCII with digits and underscores", "foo_bar_123", true),
        ("lone underscore", "_", true),
        ("leading underscore", "_x", true),
        ("double underscore", "__", true),
        ("underscore then digit", "_1", true),
        ("digit continuation", "x1", true),
        ("trailing underscore", "x_", true),
        // Accepted: letters of any script (per-code-unit char.IsLetter).
        ("Greek pi", "π", true),
        ("Greek with Latin continuation", "Δx", true),
        ("Cyrillic", "Жи", true),
        ("CJK", "中文", true),
        ("precomposed accent", "é", true),
        ("Latvian diacritics", "Vērtība", true),
        ("titlecase letter (Lt)", "ǅx", true),
        ("modifier letter (Lm)", "xʰ", true),
        // Accepted: Unicode decimal digits (Nd) CONTINUE an identifier.
        ("Arabic-Indic digit continuation", "x" + (char)0x0663, true),
        ("fullwidth digit continuation", "x" + (char)0xFF12, true),
        // Rejected: empty, digit-first, punctuation, whitespace.
        ("empty", "", false),
        ("digit first", "3x", false),
        ("Unicode digit first", (char)0x0663 + "x", false),
        ("interior space", "x y", false),
        ("interior hyphen", "x-y", false),
        ("interior dot", "x.y", false),
        ("leading space", " x", false),
        ("trailing space", "x ", false),
        ("trailing bang", "x!", false),
        // Rejected: non-letter Unicode categories.
        ("letter number Nl (Roman numeral)", "Ⅻ", false),
        ("other number No (superscript two)", "x²", false),
        ("currency symbol", "€", false),
        ("decomposed accent (combining mark continuation)", "e" + (char)0x0301, false),
        ("combining mark first", (char)0x0301 + "e", false),
        ("combining mark after underscore", "_" + (char)0x0301, false),
        // Rejected: supplementary-plane code points are surrogate PAIRS and the
        // policy is per code unit — even a Unicode LETTER outside the BMP is
        // not an identifier character. Changing this is a language-design
        // decision, not a bug fix.
        ("supplementary-plane letter (MATHEMATICAL BOLD CAPITAL A)", char.ConvertFromUtf32(0x1D400), false),
        ("supplementary-plane letter continuation", "x" + char.ConvertFromUtf32(0x10400), false),
        ("emoji", char.ConvertFromUtf32(0x1F600), false),
        ("lone high surrogate", ((char)0xD835).ToString(), false),
        ("lone low surrogate", ((char)0xDC00).ToString(), false),
        ("surrogate after underscore", "_" + (char)0xD835, false),
    ];

    [Fact]
    public void IdentifierPredicates_PreserveThePreviousRuleAndTheProgressInvariant_OverTheWholeBmp()
    {
        var failures = new List<string>();
        for (var value = 0; value <= 0xFFFF && failures.Count < 12; value++)
        {
            var c = (char)value;
            var previousStart = char.IsLetter(c) || c == '_';
            var previousPart = char.IsLetterOrDigit(c) || c == '_';
            var factoredPart = Lexer.IsIdentifierStartChar(c) || char.IsDigit(c);

            if (Lexer.IsIdentifierStartChar(c) != previousStart)
                failures.Add($"U+{value:X4}: identifier-start predicate changed from the shipped pre-M14 rule.");
            if (Lexer.IsIdentifierPartChar(c) != previousPart)
                failures.Add($"U+{value:X4}: identifier-part predicate changed from char.IsLetterOrDigit/underscore.");
            if (char.IsLetterOrDigit(c) != (char.IsLetter(c) || char.IsDigit(c)))
                failures.Add($"U+{value:X4}: char.IsLetterOrDigit differs from char.IsLetter || char.IsDigit.");
            if (Lexer.IsIdentifierPartChar(c) != factoredPart)
                failures.Add($"U+{value:X4}: identifier-part is not identifier-start || Unicode decimal digit.");
            if (Lexer.IsIdentifierStartChar(c) && !Lexer.IsIdentifierPartChar(c))
                failures.Add($"U+{value:X4}: identifier start is not a continuation, risking a zero-progress scan.");
        }

        Assert.True(failures.Count == 0, string.Join(Environment.NewLine, failures));
    }

    [Fact]
    public void IsValidIdentifier_MatchesTheHandAuthoredContract()
    {
        var failures = new List<string>();
        foreach (var (display, text, valid) in IdentifierContractRows)
        {
            if (Lexer.IsValidIdentifier(text) != valid)
                failures.Add($"{display}: IsValidIdentifier(\"{Printable(text)}\") expected {valid}.");
        }

        Assert.True(failures.Count == 0, string.Join(Environment.NewLine, failures));
    }

    [Fact]
    public void Tokenization_AgreesWithIsValidIdentifier_OnEveryContractRow()
    {
        // The whole-string helper and the tokenizer scan loop share one
        // character policy; this asserts the OBSERVABLE agreement so that
        // policy cannot silently fork: a text is a valid identifier exactly
        // when it lexes as one clean Identifier token spanning the whole text.
        // For an INVALID row this deliberately proves only that it is not one
        // clean identifier; targeted tests below pin important recovery shapes
        // such as Number+Identifier for a leading digit and Identifier+Bad for
        // an invalid continuation.
        var failures = new List<string>();
        foreach (var (display, text, valid) in IdentifierContractRows)
        {
            if (text.Length == 0)
                continue; // empty source lexes to EOF only; IsValidIdentifier covers the row

            var (tokens, diagnostics) = Lexer.Tokenize(text);
            var lexesAsOneIdentifier =
                diagnostics.Count == 0
                && tokens.Count == 2
                && tokens[0].Kind == TokenKind.Identifier
                && tokens[0].StringValue == text;
            if (lexesAsOneIdentifier != valid)
                failures.Add(
                    $"{display}: tokenizing \"{Printable(text)}\" {(lexesAsOneIdentifier ? "produced" : "did not produce")} " +
                    $"one clean Identifier token, but IsValidIdentifier says {valid}.");
        }

        Assert.True(failures.Count == 0, string.Join(Environment.NewLine, failures));
    }

    [Theory]
    [InlineData("π2x")]
    [InlineData("x٣y")]
    [InlineData("foo_bar123")]
    public void Tokenize_IdentifierUsesMaximalMunch(string source)
    {
        var (tokens, diagnostics) = Lexer.Tokenize(source);
        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.Identifier, tokens[0].Kind);
        Assert.Equal(source, tokens[0].StringValue);
        Assert.Equal(source.Length, tokens[0].Length);
        Assert.Equal(TokenKind.EndOfFile, tokens[1].Kind);
    }

    [Fact]
    public void Tokenize_InvalidIdentifierContinuation_EndsTheIdentifierAndKeepsMakingProgress()
    {
        foreach (var (source, prefix, badCount) in new[]
        {
            ("abc!", "abc", 1),
            ("e" + (char)0x0301, "e", 1),
            ("x" + char.ConvertFromUtf32(0x10400), "x", 2),
            ("_" + (char)0xD835, "_", 1),
        })
        {
            var (tokens, diagnostics) = Lexer.Tokenize(source);
            Assert.Equal(prefix, tokens[0].StringValue);
            Assert.Equal(prefix.Length, tokens[0].Length);
            Assert.Equal(badCount, tokens.Count(static token => token.Kind == TokenKind.Bad));
            Assert.Equal(badCount, diagnostics.Count);
            Assert.Equal(source.Length, tokens[^1].Position);
        }
    }

    [Fact]
    public void ReservedKeywords_AreExactlyTheKnownEight_AndAreNeverIdentifiers()
    {
        // Independent hand-authored keyword list: a keyword added to or removed
        // from the lexer must be reviewed here (and in KatLang.ebnf, whose
        // ReservedWord production EbnfLexicalSyncTests pins against
        // Lexer.KeywordNames).
        string[] expected = ["div", "mod", "and", "or", "xor", "not", "public", "open"];
        Assert.Equal(expected, Lexer.KeywordNames);

        foreach (var keyword in expected)
        {
            Assert.False(Lexer.IsValidIdentifier(keyword), $"'{keyword}' must not be a valid identifier.");

            // A keyword lexes as ONE keyword token — identifier-shaped, but
            // classified out of the identifier space (never Bad, never split).
            var (tokens, diagnostics) = Lexer.Tokenize(keyword);
            Assert.Empty(diagnostics);
            Assert.Equal(2, tokens.Count);
            Assert.NotEqual(TokenKind.Identifier, tokens[0].Kind);
            Assert.StartsWith("Keyword", tokens[0].Kind.ToString(), StringComparison.Ordinal);

            // Reservation is exact and case-sensitive: any cased variant is an
            // ordinary identifier.
            var cased = char.ToUpperInvariant(keyword[0]) + keyword[1..];
            Assert.True(Lexer.IsValidIdentifier(cased), $"'{cased}' (cased variant) must be a valid identifier.");
        }
    }

    // ── Identifier contract, end to end ──────────────────────────────────────
    // A helper is not evidence a program runs: these push representative names
    // through the public engine (lexer → parser → front end → evaluator).

    [Fact]
    public void Run_GreekPropertyName_EvaluatesLikeAnyIdentifier()
    {
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run("π = 3\nπ"));
        Assert.Equal(3, Assert.Single(success.Atoms));
    }

    [Theory]
    [InlineData("Ж")]
    [InlineData("中")]
    [InlineData("é")]
    [InlineData("x٣")]
    [InlineData("_1")]
    public void Run_OtherBmpIdentifierClasses_EvaluateThroughThePublicEngine(string identifier)
    {
        var success = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run($"{identifier} = 3\n{identifier}"));
        Assert.Equal(3, Assert.Single(success.Atoms));
    }

    [Fact]
    public void Run_NonAsciiFunctionAndParameterNames_EvaluateLikeAnyIdentifier()
    {
        var source = "Saskaitīt(α, β) = α + β\nSaskaitīt(1, 2)";
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal(3, Assert.Single(success.Atoms));
    }

    [Fact]
    public void Run_SupplementaryPlaneLetterName_IsRejectedAtTheLexicalBoundary()
    {
        // U+1D400 is a Unicode letter, but the per-code-unit policy sees two
        // surrogate halves: the program fails to parse instead of defining a
        // property.
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(char.ConvertFromUtf32(0x1D400) + " = 1"));
        Assert.NotEmpty(failure.Errors);
    }

    [Fact]
    public void Run_DecomposedAccentName_IsRejected_WhilePrecomposedRuns()
    {
        var precomposed = Assert.IsType<RunResult.Success>(KatLangEngine.Run("é = 1\né"));
        Assert.Equal(1, Assert.Single(precomposed.Atoms));

        var decomposed = KatLangEngine.Run("e" + (char)0x0301 + " = 1");
        Assert.IsType<RunResult.ParseFailure>(decomposed);
    }

    /// <summary>Renders non-ASCII/invisible code units as U+XXXX so a failure
    /// message stays readable in any console.</summary>
    private static string Printable(string text)
        => string.Concat(text.Select(static c =>
            c is >= ' ' and <= '~' ? c.ToString() : $"U+{(int)c:X4}"));
}
