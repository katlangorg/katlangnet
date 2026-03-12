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
        var (tokens, _) = Lexer.Tokenize("( ) { } , ;");

        Assert.Equal(TokenKind.LParen, tokens[0].Kind);
        Assert.Equal(TokenKind.RParen, tokens[1].Kind);
        Assert.Equal(TokenKind.LBrace, tokens[2].Kind);
        Assert.Equal(TokenKind.RBrace, tokens[3].Kind);
        Assert.Equal(TokenKind.Comma, tokens[4].Kind);
        Assert.Equal(TokenKind.Semicolon, tokens[5].Kind);
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
            1 // this is a comment
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
        var (tokens, _) = Lexer.Tokenize("1 // hello");

        var comment = Assert.Single(tokens.Where(t => t.Kind == TokenKind.Comment));
        Assert.Equal(" hello", comment.StringValue);  // text after //
        Assert.Equal(2, comment.Position);             // starts at offset of first /
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
}
