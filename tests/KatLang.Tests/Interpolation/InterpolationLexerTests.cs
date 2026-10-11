namespace KatLang.Tests.Interpolation;

/// <summary>
/// STR-02 lexical contract of double-quoted strings: a hole-free double-quoted string is ONE
/// <see cref="TokenKind.StringLiteral"/> carrying its decoded text (the same token kind as a
/// single-quoted string), an interpolated one is a paired token structure — start, text runs,
/// hole open/close around ordinary tokens, end — on one line, and every escape outside the
/// six admitted ones is a diagnostic. Single-quoted strings are unchanged (no escapes, no holes).
/// </summary>
public class InterpolationLexerTests
{
    private static (IReadOnlyList<Token> Tokens, IReadOnlyList<Diagnostic> Diagnostics) Lex(string source)
    {
        var (tokens, diagnostics) = Lexer.Tokenize(source);
        return (tokens.Where(t => t.Kind != TokenKind.EndOfFile).ToList(), diagnostics);
    }

    private static TokenKind[] KindsOf(string source)
    {
        var (tokens, diagnostics) = Lex(source);
        Assert.Empty(diagnostics);
        return tokens.Select(t => t.Kind).ToArray();
    }

    [Theory]
    [InlineData("\"abc\"", "abc")]
    [InlineData("\"\"", "")]
    [InlineData("\"{{}}\"", "{}")]
    [InlineData("\"{{x}}\"", "{x}")]
    [InlineData("\"it's\"", "it's")]
    [InlineData("\"a\\\"b\"", "a\"b")]
    [InlineData("\"a\\\\b\"", "a\\b")]
    [InlineData("\"a\\nb\"", "a\nb")]
    [InlineData("\"a\\tb\"", "a\tb")]
    [InlineData("\"# not a comment\"", "# not a comment")]
    [InlineData("\"'\"", "'")]
    public void HoleFreeDoubleQuotedString_IsOneStringLiteralToken_WithItsDecodedText(string source, string text)
    {
        var (tokens, diagnostics) = Lex(source);
        Assert.Empty(diagnostics);
        var token = Assert.Single(tokens);
        Assert.Equal(TokenKind.StringLiteral, token.Kind);
        Assert.Equal(text, token.StringValue);
        Assert.Equal((0, source.Length), (token.Position, token.Length));
    }

    [Theory]
    [InlineData("'a\\nb'", "a\\nb")]
    [InlineData("'{x}'", "{x}")]
    [InlineData("'\"'", "\"")]
    [InlineData("'}'", "}")]
    [InlineData("'\\'", "\\")]
    public void SingleQuotedStrings_AreUnchanged_RawAndHoleFree(string source, string text)
    {
        var (tokens, diagnostics) = Lex(source);
        Assert.Empty(diagnostics);
        var token = Assert.Single(tokens);
        Assert.Equal(TokenKind.StringLiteral, token.Kind);
        Assert.Equal(text, token.StringValue);
    }

    [Fact]
    public void InterpolatedString_IsAPairedTokenStructure_WithTextRunsAroundOrdinaryHoleTokens()
    {
        var (tokens, diagnostics) = Lex("\"a{x}b\"");
        Assert.Empty(diagnostics);
        Assert.Equal(
            new[]
            {
                TokenKind.InterpolatedStringStart, TokenKind.InterpolatedStringText, TokenKind.InterpolationHoleOpen,
                TokenKind.Identifier, TokenKind.InterpolationHoleClose, TokenKind.InterpolatedStringText,
                TokenKind.InterpolatedStringEnd,
            },
            tokens.Select(t => t.Kind));
        Assert.Equal("a", tokens[1].StringValue);
        Assert.Equal("b", tokens[5].StringValue);
        Assert.Equal(new[] { 0, 1, 2, 3, 4, 5, 6 }, tokens.Select(t => t.Position));
        Assert.All(tokens, t => Assert.Equal(1, t.Line));
    }

    [Fact]
    public void EmptyTextRuns_ProduceNoTextToken()
        => Assert.Equal(
            new[]
            {
                TokenKind.InterpolatedStringStart, TokenKind.InterpolationHoleOpen, TokenKind.Number,
                TokenKind.InterpolationHoleClose, TokenKind.InterpolationHoleOpen, TokenKind.Number,
                TokenKind.InterpolationHoleClose, TokenKind.InterpolatedStringEnd,
            },
            KindsOf("\"{1}{2}\""));

    [Fact]
    public void TextRuns_DecodeEscapesAndDoubledBraces()
    {
        var (tokens, diagnostics) = Lex("\"{{\\n{x}\\t\\\"}}\"");
        Assert.Empty(diagnostics);
        var texts = tokens.Where(t => t.Kind == TokenKind.InterpolatedStringText).Select(t => t.StringValue).ToArray();
        Assert.Equal(new[] { "{\n", "\t\"}" }, texts);
    }

    [Fact]
    public void BracesInsideAHole_AreOrdinaryBraces_AndTheHoleClosesAtItsOwnBrace()
        => Assert.Equal(
            new[]
            {
                TokenKind.InterpolatedStringStart, TokenKind.InterpolationHoleOpen, TokenKind.LBrace, TokenKind.Number,
                TokenKind.RBrace, TokenKind.InterpolationHoleClose, TokenKind.InterpolatedStringEnd,
            },
            KindsOf("\"{ {1} }\""));

    [Fact]
    public void StringsInsideAHole_AreOrdinaryStringTokens_InEitherQuote()
    {
        var (tokens, diagnostics) = Lex("\"{'}'}{\"q\"}\"");
        Assert.Empty(diagnostics);
        var literals = tokens.Where(t => t.Kind == TokenKind.StringLiteral).Select(t => t.StringValue).ToArray();
        Assert.Equal(new[] { "}", "q" }, literals);
        Assert.Equal(2, tokens.Count(t => t.Kind == TokenKind.InterpolationHoleOpen));
    }

    [Fact]
    public void NestedInterpolatedStrings_PairEveryBoundaryToken()
    {
        var kinds = KindsOf("\"<{\"[{1}]\"}>\"");
        Assert.Equal(2, kinds.Count(k => k == TokenKind.InterpolatedStringStart));
        Assert.Equal(2, kinds.Count(k => k == TokenKind.InterpolatedStringEnd));
        Assert.Equal(2, kinds.Count(k => k == TokenKind.InterpolationHoleOpen));
        Assert.Equal(2, kinds.Count(k => k == TokenKind.InterpolationHoleClose));
        AssertPaired(Lex("\"<{\"[{1}]\"}>\"").Tokens);
    }

    [Theory]
    [InlineData("\"a}b\"", 3)]
    [InlineData("\"}\"", 2)]
    [InlineData("\"{x}}\"", 5)]
    public void ALoneClosingBraceInText_IsUnmatchedBraceInString(string source, int column)
    {
        var (_, diagnostics) = Lex(source);
        var diagnostic = Assert.Single(diagnostics);
        Assert.Equal(DiagnosticCode.UnmatchedBraceInString, diagnostic.Code);
        Assert.Equal(new SourcePosition(1, column), Assert.NotNull(diagnostic.Span).Start);
    }

    [Theory]
    [InlineData("\"\\r\"")]
    [InlineData("\"\\u0041\"")]
    [InlineData("\"\\x41\"")]
    [InlineData("\"\\0\"")]
    [InlineData("\"\\{\"")]
    [InlineData("\"\\}\"")]
    [InlineData("\"\\'\"")]
    [InlineData("\"\\a\"")]
    public void EveryEscapeOutsideTheAdmittedSix_IsInvalidStringEscape(string source)
    {
        var (_, diagnostics) = Lex(source);
        var diagnostic = Assert.Single(diagnostics);
        Assert.Equal(DiagnosticCode.InvalidStringEscape, diagnostic.Code);
        Assert.Equal(new SourceSpan(1, 2, 1, 4), diagnostic.Span);
    }

    [Fact]
    public void ABackslashBeforeTheLineEnd_LeavesTheStringUnterminated()
    {
        var (tokens, diagnostics) = Lex("\"a\\");
        Assert.Equal(TokenKind.StringLiteral, Assert.Single(tokens).Kind);
        Assert.Equal(DiagnosticCode.UnterminatedStringLiteral, Assert.Single(diagnostics).Code);
    }

    [Theory]
    [InlineData("\"{1 # c}\"")]
    [InlineData("\"{#}\"")]
    public void ACommentCannotStartInsideAHole(string source)
    {
        var (_, diagnostics) = Lex(source);
        Assert.Equal(DiagnosticCode.InvalidInterpolationHole, Assert.Single(diagnostics).Code);
    }

    [Fact]
    public void AHashInText_IsText_AndAfterTheString_IsAComment()
    {
        var (tokens, diagnostics) = Lex("\"a # b\" # c");
        Assert.Empty(diagnostics);
        Assert.Equal(TokenKind.StringLiteral, tokens[0].Kind);
        Assert.Equal("a # b", tokens[0].StringValue);
        Assert.Equal(TokenKind.Comment, tokens[1].Kind);
    }

    [Theory]
    [InlineData("\"a{x", DiagnosticCode.UnterminatedInterpolationHole)]
    [InlineData("\"a{x}b", DiagnosticCode.UnterminatedStringLiteral)]
    [InlineData("\"{(1}", DiagnosticCode.UnterminatedStringLiteral)]
    [InlineData("\"{1 +\n2}\"", DiagnosticCode.UnterminatedInterpolationHole)]
    public void AnUnterminatedStringOrHole_IsOneTokenToTheLineEnd_WithOneDiagnosticOnItsLine(string source, DiagnosticCode code)
    {
        var (tokens, diagnostics) = Lex(source);
        var lineEnd = source.IndexOf('\n') is var at and >= 0 ? at : source.Length;
        Assert.Equal(TokenKind.StringLiteral, tokens[0].Kind);
        Assert.Equal((0, lineEnd), (tokens[0].Position, tokens[0].Length));
        var onLine = diagnostics.Where(d => Assert.NotNull(d.Span).Start.Line == 1).ToList();
        Assert.Equal(code, Assert.Single(onLine).Code);
        Assert.DoesNotContain(tokens, t => t.Kind is TokenKind.InterpolatedStringStart or TokenKind.InterpolationHoleOpen);
    }

    [Fact]
    public void TheNextLine_LexesIndependently_AfterAnUnterminatedString()
    {
        var (tokens, _) = Lex("A = \"a{x\nB = 2");
        Assert.Contains(tokens, t => t.Kind == TokenKind.Identifier && t.StringValue == "B" && t.Line == 2);
        Assert.Contains(tokens, t => t.Kind == TokenKind.Number && t.Line == 2);
    }

    [Fact]
    public void LexerInvariants_HoldOnEveryStringOverASmallAlphabet()
    {
        // Exhaustive over all strings of length <= 5 on an alphabet that exercises quotes,
        // braces, escapes, comments and line ends: the lexer never throws, every token stays in
        // range, every diagnostic span is in range, and every interpolated-string boundary token
        // is paired on one line.
        var alphabet = new[] { '"', '\'', '{', '}', '\\', 'x', '#', '\n', ' ' };
        var buffer = new char[5];
        var checkedCount = 0;
        for (var length = 0; length <= 5; length++)
        {
            var indexes = new int[length];
            while (true)
            {
                for (var i = 0; i < length; i++)
                    buffer[i] = alphabet[indexes[i]];
                var source = new string(buffer, 0, length);
                AssertLexerInvariants(source);
                checkedCount++;

                var position = length - 1;
                while (position >= 0 && ++indexes[position] == alphabet.Length)
                    indexes[position--] = 0;
                if (position < 0)
                    break;
            }
        }

        Assert.True(checkedCount > 60_000);
    }

    [Fact]
    public void LexerInvariants_HoldOnSeededRandomSources()
    {
        var random = new Random(20261011);
        var pieces = new[] { "\"", "'", "{", "}", "{{", "}}", "\\", "\\n", "\\\"", "x", "1", "+", ",", ":", "(", ")", "[", "]", "#", "\n", " ", "=", "*", "~" };
        for (var i = 0; i < 4_000; i++)
        {
            var count = random.Next(1, 24);
            var source = string.Concat(Enumerable.Range(0, count).Select(_ => pieces[random.Next(pieces.Length)]));
            AssertLexerInvariants(source);
        }
    }

    internal static void AssertLexerInvariants(string source)
    {
        var (tokens, diagnostics) = Lexer.Tokenize(source);
        foreach (var token in tokens)
        {
            Assert.InRange(token.Position, 0, source.Length);
            Assert.InRange(token.Position + token.Length, token.Position, source.Length);
        }

        foreach (var diagnostic in diagnostics)
            Assert.NotNull(diagnostic.Span);

        AssertPaired(tokens);
    }

    private static void AssertPaired(IReadOnlyList<Token> tokens)
    {
        var open = new Stack<Token>();
        foreach (var token in tokens)
        {
            switch (token.Kind)
            {
                case TokenKind.InterpolatedStringStart or TokenKind.InterpolationHoleOpen:
                    open.Push(token);
                    break;
                case TokenKind.InterpolatedStringEnd or TokenKind.InterpolationHoleClose:
                    var opener = open.Pop();
                    Assert.Equal(
                        opener.Kind == TokenKind.InterpolatedStringStart,
                        token.Kind == TokenKind.InterpolatedStringEnd);
                    Assert.Equal(opener.Line, token.Line);
                    break;
                case TokenKind.InterpolatedStringText:
                    Assert.NotEmpty(open);
                    Assert.Equal(TokenKind.InterpolatedStringStart, open.Peek().Kind);
                    break;
            }
        }

        Assert.Empty(open);
    }
}
