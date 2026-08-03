namespace KatLang.Tests;

/// <summary>
/// The `#` line-comment surface: a `#` outside a string literal starts a
/// comment that runs to the next physical newline or the end of the source,
/// regardless of what precedes it (whitespace before `#` is optional). The
/// comment is trivia — it never removes or relaxes the newline boundary it
/// stops at — and the former `//` marker is removed entirely, so `/` is
/// always the division token. Style (one space before and after a trailing
/// `#`) is a documentation recommendation only; the compact form `value=6#7`
/// is fully valid.
/// </summary>
public class CommentSyntaxTests
{
    private static string Display(string source)
    {
        var result = KatLangEngine.Run(source);
        Assert.True(result is RunResult.Success, $"Expected success but got: {result.ToDisplayString()}");
        return result.ToDisplayString().Replace("\r\n", "\n");
    }

    private static IReadOnlyList<Token> TokensOf(string source)
    {
        var (tokens, diagnostics) = Lexer.Tokenize(source);
        Assert.Empty(diagnostics);
        return tokens;
    }

    // ── Full-line and trailing comments ─────────────────────────────────────

    [Fact]
    public void FullLineComment_LeavesFollowingRowsIntact()
    {
        Assert.Equal("6", Display("# comment\nvalue = 6\nvalue"));
    }

    [Fact]
    public void TrailingComment_WithSpaces_IsIgnored()
    {
        Assert.Equal("6", Display("value = 6 # comment\nvalue"));
    }

    [Fact]
    public void TrailingComment_WithoutWhitespace_IsEquivalentToSpacedForm()
    {
        // `value = 6 # 7 is a comment` and `value = 6#7 is a comment` are the
        // same program as `value = 6`.
        Assert.Equal("6", Display("value = 6 # 7 is a comment\nvalue"));
        Assert.Equal("6", Display("value = 6#7 is a comment\nvalue"));
    }

    [Fact]
    public void CompactForm_ValueEqualsSixHashSeven_AssignsSixAndCommentsOutSeven()
    {
        // The exact form `value=6#7`: `value` is assigned 6 and `7` is
        // comment text — proven at the token, AST, and evaluation layers.
        var tokens = TokensOf("value=6#7");
        Assert.Equal(
            new[] { TokenKind.Identifier, TokenKind.Equals, TokenKind.Number, TokenKind.Comment, TokenKind.EndOfFile },
            tokens.Select(t => t.Kind));
        Assert.Equal(6, tokens[2].NumValue);
        Assert.Equal("7", tokens[3].StringValue);

        var parse = Parser.Parse("value=6#7");
        Assert.Empty(parse.Diagnostics);
        var property = Assert.Single(parse.Root.Properties);
        Assert.Equal("value", property.Name);
        var body = Assert.IsType<Expr.Num>(Assert.Single(property.Value.Output));
        Assert.Equal(6, body.Value);

        Assert.Equal("6", Display("value=6#7\nvalue"));
    }

    // ── The marker starts a comment after any preceding token kind ──────────

    [Theory]
    [InlineData("value = 1\nvalue#comment", "1")]           // after an identifier
    [InlineData("6#comment", "6")]                          // after a number
    [InlineData("[1,2]#comment", "[1, 2]")]                 // after a closing bracket
    [InlineData("(1,2)#comment", "(1, 2)")]                 // after a closing paren
    [InlineData("Call(x) = x\nCall(1)#comment", "1")]       // after a call's closing paren
    [InlineData("text = 'a'#comment\ntext", "a")]           // after a string literal
    [InlineData("Pair = 1, 2\nPair:0#comment", "1")]        // after an indexing selector
    public void CommentStartsAfterAnyTokenKind(string source, string expected)
    {
        Assert.Equal(expected, Display(source));
    }

    // ── Comment-only, empty, and end-of-file comments ───────────────────────

    [Fact]
    public void CommentOnlySource_IsAValidEmptyProgram()
    {
        var tokens = TokensOf("# comment");
        Assert.Equal(
            new[] { TokenKind.Comment, TokenKind.EndOfFile },
            tokens.Select(t => t.Kind));

        var parse = Parser.Parse("# comment");
        Assert.Empty(parse.Diagnostics);
        Assert.Empty(parse.Root.Output);

        // The comment is trivia: like the empty program, a comment-only
        // source parses cleanly and simply defines no output.
        Assert.IsType<RunResult.NoProgramOutput>(KatLangEngine.Run("# comment"));
    }

    [Fact]
    public void EmptyComment_IsAValidCommentWithEmptyText()
    {
        var tokens = TokensOf("value = 6#");
        var comment = Assert.Single(tokens, t => t.Kind == TokenKind.Comment);
        Assert.Equal("", comment.StringValue);
        Assert.Equal(1, comment.Length);

        var parse = Parser.Parse("value = 6#");
        Assert.Empty(parse.Diagnostics);
        Assert.Equal("value", Assert.Single(parse.Root.Properties).Name);
    }

    [Fact]
    public void EndOfFileComment_WithoutFinalNewline_TerminatesAtEndOfSource()
    {
        const string source = "value = 6#comment";
        var tokens = TokensOf(source);
        var comment = Assert.Single(tokens, t => t.Kind == TokenKind.Comment);
        Assert.Equal("comment", comment.StringValue);
        Assert.Equal(9, comment.Position);
        Assert.Equal(source.Length - 9, comment.Length);
        Assert.Equal(source.Length, tokens[^1].Position); // EOF sits at source length

        Assert.Equal("6", Display("value = 6#comment\nvalue"));
        Assert.Equal("6", Display("6 # end of file"));
    }

    // ── Newline preservation ────────────────────────────────────────────────

    [Fact]
    public void CommentRemoval_PreservesTheRowSeparatingNewline()
    {
        // The newline the comment stops at keeps its ordinary boundary
        // meaning: two output rows never merge into one.
        Assert.Equal("1\n2", Display("1 # one\n2 # two"));
    }

    [Fact]
    public void CommentRemoval_PreservesBlankLines()
    {
        Assert.Equal("1\n2", Display("1 # one\n\n# comment-only row\n\n2 # two"));
    }

    [Fact]
    public void DefinitionBody_StillEndsAtTheNewlineAfterATrailingComment()
    {
        // A simple one-line property body ends at the physical newline; a
        // trailing comment does not extend the body onto the next line.
        Assert.Equal("2\n1", Display("P = 1 # comment\n2\nP"));
    }

    [Fact]
    public void TrailingOperatorContinuation_StillWorksWithACommentAfterTheOperator()
    {
        // `1 +` continues onto the next line; the comment between the
        // operator and the newline changes nothing.
        Assert.Equal("3", Display("1 + # comment\n2"));
    }

    [Fact]
    public void OperatorLedLine_IsStillRejectedWhenThePreviousLineEndsWithAComment()
    {
        // A comment must never RELAX the newline boundary either: the
        // '+'-led line stays invalid exactly as without the comment.
        var result = Parser.ParseSyntax("1 # comment\n+ 2");
        Assert.True(result.HasErrors);
    }

    // ── Strings ─────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("text = '#'\ntext", "#")]
    [InlineData("text = 'a#b'\ntext", "a#b")]
    [InlineData("text = 'value=6#7'\ntext", "value=6#7")]
    [InlineData("text = 'not # a comment'\ntext", "not # a comment")]
    public void HashInsideStringLiteral_IsOrdinaryContent(string source, string expected)
    {
        Assert.Equal(expected, Display(source));
    }

    [Fact]
    public void HashInsideStringLiteral_ProducesNoCommentToken()
    {
        var tokens = TokensOf("'a#b'");
        Assert.Equal(
            new[] { TokenKind.StringLiteral, TokenKind.EndOfFile },
            tokens.Select(t => t.Kind));
        Assert.Equal("a#b", tokens[0].StringValue);
    }

    [Fact]
    public void BackslashesAndMalformedStrings_DoNotExposeHashToCommentScanning()
    {
        var closed = TokensOf("'a\\#b'");
        var closedString = Assert.Single(closed, token => token.Kind == TokenKind.StringLiteral);
        Assert.Equal("a\\#b", closedString.StringValue);
        Assert.DoesNotContain(closed, token => token.Kind == TokenKind.Comment);

        var (unterminated, diagnostics) = Lexer.Tokenize("'a#b");
        Assert.Single(diagnostics);
        Assert.Equal("a#b", Assert.Single(unterminated, token => token.Kind == TokenKind.StringLiteral).StringValue);
        Assert.DoesNotContain(unterminated, token => token.Kind == TokenKind.Comment);
    }

    [Fact]
    public void CommentAfterAClosedString_StartsNormally()
    {
        var tokens = TokensOf("'a' # note");
        Assert.Equal(
            new[] { TokenKind.StringLiteral, TokenKind.Comment, TokenKind.EndOfFile },
            tokens.Select(t => t.Kind));
        Assert.Equal(" note", tokens[1].StringValue);
    }

    // ── The former `//` marker is removed ───────────────────────────────────

    [Fact]
    public void DoubleSlash_LexesAsTwoDivisionTokens_NeverAsAComment()
    {
        var (tokens, diagnostics) = Lexer.Tokenize("// old comment");
        Assert.Empty(diagnostics);
        Assert.DoesNotContain(tokens, t => t.Kind == TokenKind.Comment);
        Assert.Equal(TokenKind.Slash, tokens[0].Kind);
        Assert.Equal(TokenKind.Slash, tokens[1].Kind);
        Assert.Equal(TokenKind.Identifier, tokens[2].Kind); // `old` is ordinary source text now
    }

    [Theory]
    [InlineData("// old comment")]
    [InlineData("value = 6 // old comment")]
    public void FormerDoubleSlashComment_IsAParseErrorNotTrivia(string source)
    {
        // The second '/' has no operand, so the former comment line is
        // rejected by the ordinary grammar instead of being skipped.
        Assert.True(Parser.ParseSyntax(source).HasErrors);
    }

    [Fact]
    public void SingleSlash_RemainsDivision()
    {
        Assert.Equal("5", Display("10 / 2 # halve it"));
    }

    [Theory]
    [InlineData("a/b", 1)]
    [InlineData("a//b", 2)]
    [InlineData("a///b", 3)]
    [InlineData("a / / b", 2)]
    public void AdjacentSlashes_AlwaysUseOrdinaryDivisionTokenization(string source, int slashCount)
    {
        var tokens = TokensOf(source);
        Assert.Equal(slashCount, tokens.Count(token => token.Kind == TokenKind.Slash));
        Assert.DoesNotContain(tokens, token => token.Kind == TokenKind.Comment);
    }

    // ── Text after `#` is never lexed or parsed ─────────────────────────────

    [Theory]
    [InlineData("value = 6 # ]]] invalid ??? KatLang text")]
    [InlineData("6 # 'unterminated string opener")]
    [InlineData("6 # ((( [[[ ,,, *** ...")]
    [InlineData("6 # // the removed marker is inert inside a comment")]
    public void TextAfterHash_IsNeverLexedOrParsed(string source)
    {
        var (tokens, diagnostics) = Lexer.Tokenize(source);
        Assert.Empty(diagnostics);
        Assert.Single(tokens, t => t.Kind == TokenKind.Comment);

        var parse = Parser.Parse(source);
        Assert.Empty(parse.Diagnostics);
    }

    // ── Source spans and diagnostics ────────────────────────────────────────

    [Fact]
    public void TokensBeforeATrailingComment_RetainExactSpans()
    {
        var tokens = TokensOf("value = 6 # c");

        Assert.Equal(TokenKind.Identifier, tokens[0].Kind);
        Assert.Equal((0, 5, 1, 1), (tokens[0].Position, tokens[0].Length, tokens[0].Line, tokens[0].Column));
        Assert.Equal(TokenKind.Equals, tokens[1].Kind);
        Assert.Equal((6, 1, 1, 7), (tokens[1].Position, tokens[1].Length, tokens[1].Line, tokens[1].Column));
        Assert.Equal(TokenKind.Number, tokens[2].Kind);
        Assert.Equal((8, 1, 1, 9), (tokens[2].Position, tokens[2].Length, tokens[2].Line, tokens[2].Column));
        Assert.Equal(TokenKind.Comment, tokens[3].Kind);
        Assert.Equal((10, 3, 1, 11), (tokens[3].Position, tokens[3].Length, tokens[3].Line, tokens[3].Column));
    }

    [Fact]
    public void LineAfterATrailingComment_StartsAtTheCorrectPosition()
    {
        var tokens = TokensOf("A = 1 # c\nB = 2");
        var b = Assert.Single(tokens, t => t.Kind == TokenKind.Identifier && t.StringValue == "B");
        Assert.Equal(10, b.Position);
        Assert.Equal(2, b.Line);
        Assert.Equal(1, b.Column);
    }

    [Fact]
    public void DiagnosticsAfterCommentLines_ReportCorrectLineAndColumn()
    {
        var (_, diagnostics) = Lexer.Tokenize("# one\n# two\n!");
        var diagnostic = Assert.Single(diagnostics);
        Assert.Contains("Unexpected character: '!'", diagnostic.Message);
        Assert.Equal(new SourceSpan(3, 1, 3, 1), diagnostic.Span);
    }

    [Fact]
    public void ParserRecoveryAfterAComment_PreservesTheFollowingRowsAndDiagnosticLocation()
    {
        var parse = Parser.ParseSyntax("1 # first\n!\n2 # recovered");

        Assert.True(parse.HasErrors);
        Assert.Contains(parse.Diagnostics, diagnostic => diagnostic.Span == new SourceSpan(2, 1, 2, 1));
        Assert.Equal(
            new decimal[] { 1, 2 },
            parse.Root.Output.OfType<Expr.Num>().Select(number => number.Value));
    }

    [Fact]
    public void Utf16CodeUnitsAroundACommentKeepExactOffsetsAndContent()
    {
        const string source = "'\U0001F600'# \uD83D\0\u0301\r\n2";
        var tokens = TokensOf(source);

        var text = Assert.Single(tokens, token => token.Kind == TokenKind.StringLiteral);
        Assert.Equal("\U0001F600", text.StringValue);
        Assert.Equal((0, 4, 1, 1), (text.Position, text.Length, text.Line, text.Column));

        var comment = Assert.Single(tokens, token => token.Kind == TokenKind.Comment);
        Assert.Equal(" \uD83D\0\u0301", comment.StringValue);
        Assert.Equal((4, 5, 1, 5), (comment.Position, comment.Length, comment.Line, comment.Column));

        var following = Assert.Single(tokens, token => token.Kind == TokenKind.Number);
        Assert.Equal((11, 2, 1), (following.Position, following.Line, following.Column));
    }

    [Fact]
    public void CommentAtEndOfFile_ProducesInBoundsSpans()
    {
        const string source = "1 # c";
        var tokens = TokensOf(source);
        var comment = Assert.Single(tokens, t => t.Kind == TokenKind.Comment);
        Assert.Equal(2, comment.Position);
        Assert.Equal(3, comment.Length);
        Assert.True(comment.Position + comment.Length <= source.Length);
        Assert.Equal(source.Length, tokens[^1].Position);
        Assert.Equal(0, tokens[^1].Length);
    }

    // ── LF and CRLF termination ─────────────────────────────────────────────

    [Theory]
    [InlineData("1 # c\n2")]
    [InlineData("1 # c\r\n2")]
    public void CommentTerminates_BeforeLfAndCrLfAlike(string source)
    {
        var tokens = TokensOf(source);
        var comment = Assert.Single(tokens, t => t.Kind == TokenKind.Comment);
        Assert.Equal(" c", comment.StringValue);
        Assert.Equal(3, comment.Length); // stops before '\r' and '\n' alike

        var two = Assert.Single(tokens, t => t.Kind == TokenKind.Number && t.NumValue == 2);
        Assert.Equal(2, two.Line);
        Assert.Equal(1, two.Column);

        Assert.Equal("1\n2", Display(source));
    }

    [Fact]
    public void CommentTerminatesBeforeLoneCarriageReturn_WithoutChangingTheCrCoordinatePolicy()
    {
        // KatLang's established coordinate contract treats a lone CR as
        // transparent rather than as a line break, but it still terminates a
        // string or comment so following source is tokenized normally.
        var tokens = TokensOf("# c\r2");
        Assert.Equal(" c", Assert.Single(tokens, token => token.Kind == TokenKind.Comment).StringValue);

        var following = Assert.Single(tokens, token => token.Kind == TokenKind.Number);
        Assert.Equal((4, 1, 4), (following.Position, following.Line, following.Column));
    }

    [Fact]
    public void CommentAtModuleEof_DoesNotCrossTheSourceModuleBoundary()
    {
        const string url = "https://katlang.org/comment-syntax.kat";
        var result = KatLangEngine.Run(
            $"open '{url}'\nX",
            new RunOptions
            {
                DownloadCode = requested => requested == url
                    ? "public X = 6# ] invalid text ignored at module EOF"
                    : throw new InvalidOperationException($"Unexpected URL: {requested}"),
            });

        Assert.IsType<RunResult.Success>(result);
        Assert.Equal("6", result.ToDisplayString());
    }
}
