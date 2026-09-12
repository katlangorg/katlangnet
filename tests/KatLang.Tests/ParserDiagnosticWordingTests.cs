namespace KatLang.Tests;

/// <summary>
/// Parser diagnostics are phrased in KatLang terms. The generic unexpected-token
/// family used to interpolate the lexer's internal <see cref="TokenKind"/> enum
/// names ("Expected 'RParen', got 'EndOfFile'."), which mean nothing to a KatLang
/// user; these pins keep the written spelling of the token — or "end of input" —
/// in every message of that family.
/// </summary>
public class ParserDiagnosticWordingTests
{
    [Theory]
    [InlineData("(1, 2", "Expected ')' but found end of input.")]
    [InlineData("{ x = 1", "Expected '}' but found end of input.")]
    [InlineData("F(x) = x\nF({ 1 )", "Expected '}' but found ')'.")]
    [InlineData("[1, 2", "Expected ']' but found end of input.")]
    [InlineData("F() = 1\nF()", "Unexpected ')' in a pattern.")]
    [InlineData("= 1", "Unexpected '='.")]
    [InlineData("1 ]", "Unexpected ']'.")]
    [InlineData("public = 1", "Unexpected 'public'.")]
    [InlineData("1,", "Unexpected end of input.")]
    [InlineData("1 + @", "Unexpected unrecognized character.")]
    public void UnexpectedTokenFamily_NamesTheWrittenTokenOrEndOfInput(string source, string expectedMessage)
    {
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d =>
            d.Code == DiagnosticCode.UnexpectedToken && d.Message == expectedMessage);
    }

    [Fact]
    public void NoParserDiagnostic_LeaksAnInternalTokenKindName()
    {
        string[] sources =
        [
            "(1, 2", "{ x = 1", "[1", "F() = 1", "= 1", "1 ]", "public = 1", "1,", ", 1", "1,, 2",
            "F(x) = x\nF({ 1 )", "open Math Pi", "div = 1", "A = 1 )", "1 ; 2", "~", "x = *", "F(", "1 + @",
        ];
        foreach (var source in sources)
        {
            var result = Parser.ParseSyntax(source);
            Assert.True(result.HasErrors, source);
            foreach (var diagnostic in result.Diagnostics)
            {
                foreach (var kind in Enum.GetValues<TokenKind>())
                {
                    Assert.DoesNotContain($"'{kind}'", diagnostic.Message);
                }
            }
        }
    }

    [Fact]
    public void EveryTokenKind_HasAKatLangFacingDescription()
    {
        foreach (var kind in Enum.GetValues<TokenKind>())
        {
            var description = Parser.DescribeTokenKind(kind);
            Assert.False(string.IsNullOrWhiteSpace(description));
            Assert.DoesNotContain(kind.ToString(), description);
        }
    }

    [Fact]
    public void PunctuationAndKeywords_DescribeTheirExactLexicalSpelling()
    {
        const string spellings = "+ - * / ^ < > <= >= == != div mod and or xor not public open ( ) { } [ ] , ; = : . ~";
        foreach (var spelling in spellings.Split(' '))
        {
            var (tokens, diagnostics) = Lexer.Tokenize(spelling);
            Assert.Empty(diagnostics);
            Assert.Equal($"'{spelling}'", Parser.DescribeTokenKind(tokens[0].Kind));
            Assert.Equal($"'{spelling}'", Parser.DescribeTokenKind(tokens[0].Kind, includeArticle: false));
        }
    }

    [Theory]
    [InlineData(TokenKind.Number, "a number", "number")]
    [InlineData(TokenKind.Identifier, "a name", "name")]
    [InlineData(TokenKind.StringLiteral, "a string", "string")]
    [InlineData(TokenKind.Comment, "a comment", "comment")]
    [InlineData(TokenKind.Bad, "an unrecognized character", "unrecognized character")]
    [InlineData(TokenKind.EndOfFile, "end of input", "end of input")]
    public void TokenCategories_UseArticlesOnlyWhereGrammatical(TokenKind kind, string expected, string unexpected)
    {
        Assert.Equal(expected, Parser.DescribeTokenKind(kind));
        Assert.Equal(unexpected, Parser.DescribeTokenKind(kind, includeArticle: false));
    }

    [Theory]
    [InlineData("(1", "Expected ')' but found end of input.", 3, 3)]
    [InlineData("public = 1", "Unexpected 'public'.", 1, 6)]
    [InlineData("F() = 1", "Unexpected ')' in a pattern.", 3, 3)]
    [InlineData("1 + @", "Unexpected unrecognized character.", 5, 5)]
    public void UnexpectedTokenWording_PreservesCodeAndSpan(string source, string message, int column, int endColumn)
    {
        var diagnostic = Assert.Single(Parser.ParseSyntax(source).Diagnostics,
            d => d.Code == DiagnosticCode.UnexpectedToken && d.Message == message);
        Assert.Equal(new SourceSpan(1, column, 1, endColumn), diagnostic.Span);
    }
}
