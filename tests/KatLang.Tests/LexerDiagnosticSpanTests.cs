namespace KatLang.Tests;

/// <summary>
/// Exact diagnostic-span regressions for the two lexer diagnostics that carry
/// a scanned-run span: oversized number literals and unterminated string
/// literals. The repository convention is inclusive spans — EndColumn is the
/// final offending source column, not the lexer's live cursor column (which
/// points one past the last consumed code unit). Tokenization itself must be
/// unaffected: the placeholder number token and the string token are still
/// produced with their original positions and lengths.
/// </summary>
public class LexerDiagnosticSpanTests
{
    private const string NumberTooLargeMessage = "Number literal is too large.";
    private const string UnterminatedStringMessage = "Unterminated string literal.";

    /// <summary>42 digits — far beyond decimal range, so TryParse fails.</summary>
    private static readonly string OversizedDigits = new('9', 42);

    private static Diagnostic SingleDiagnostic(
        IReadOnlyList<Diagnostic> diagnostics, string expectedMessage)
    {
        var diagnostic = Assert.Single(diagnostics);
        Assert.Equal(expectedMessage, diagnostic.Message);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        return diagnostic;
    }

    private static void AssertSpan(
        string source, SourceSpan span,
        int startLine, int startColumn, int endLine, int endColumn,
        string expectedSlice)
    {
        Assert.Equal(startLine, span.StartLineNumber);
        Assert.Equal(startColumn, span.StartColumn);
        Assert.Equal(endLine, span.EndLineNumber);
        Assert.Equal(endColumn, span.EndColumn);

        Assert.Equal(span.StartLineNumber, span.EndLineNumber);
        var line = source.Split('\n')[span.StartLineNumber - 1].TrimEnd('\r');
        Assert.Equal(
            expectedSlice,
            line.Substring(span.StartColumn - 1, span.EndColumn - span.StartColumn + 1));
    }

    // ── Number literal is too large ─────────────────────────────────────────

    [Fact]
    public void OversizedNumber_AtColumnOne_EndsAtFinalDigitColumn()
    {
        var source = OversizedDigits;
        var (tokens, diagnostics) = Lexer.Tokenize(source);

        var diagnostic = SingleDiagnostic(diagnostics, NumberTooLargeMessage);
        AssertSpan(source, diagnostic.Span, 1, 1, 1, 42, OversizedDigits);

        // Tokenization is preserved: a placeholder zero number token covering
        // the whole literal, then end of file.
        Assert.Equal(2, tokens.Count);
        Assert.Equal(TokenKind.Number, tokens[0].Kind);
        Assert.Equal(0, tokens[0].NumValue);
        Assert.Equal(0, tokens[0].Position);
        Assert.Equal(42, tokens[0].Length);
        Assert.Equal(TokenKind.EndOfFile, tokens[1].Kind);
    }

    [Fact]
    public void OversizedNumber_AfterPrefixOnSameLine_EndsAtFinalDigitColumn()
    {
        var source = "X = " + OversizedDigits;
        var (tokens, diagnostics) = Lexer.Tokenize(source);

        var diagnostic = SingleDiagnostic(diagnostics, NumberTooLargeMessage);
        AssertSpan(source, diagnostic.Span, 1, 5, 1, 46, OversizedDigits);

        Assert.Equal(
            new[] { TokenKind.Identifier, TokenKind.Equals, TokenKind.Number, TokenKind.EndOfFile },
            tokens.Select(t => t.Kind).ToArray());
    }

    // ── Unterminated string literal ─────────────────────────────────────────

    [Fact]
    public void UnterminatedString_MidLine_EndsAtFinalConsumedColumn()
    {
        const string source = "X = 'abc\nY = 2";
        var (tokens, diagnostics) = Lexer.Tokenize(source);

        var diagnostic = SingleDiagnostic(diagnostics, UnterminatedStringMessage);
        // The unterminated token is `'abc`, columns 5..8 on line 1.
        AssertSpan(source, diagnostic.Span, 1, 5, 1, 8, "'abc");

        // Tokenization is preserved: the string token still carries the
        // scanned value and the second line still tokenizes normally.
        var stringToken = Assert.Single(tokens, t => t.Kind == TokenKind.StringLiteral);
        Assert.Equal("abc", stringToken.StringValue);
        Assert.Equal(4, stringToken.Position);
        Assert.Equal(4, stringToken.Length);
        Assert.Equal(
            new[]
            {
                TokenKind.Identifier, TokenKind.Equals, TokenKind.StringLiteral,
                TokenKind.Identifier, TokenKind.Equals, TokenKind.Number,
                TokenKind.EndOfFile,
            },
            tokens.Select(t => t.Kind).ToArray());
    }

    [Fact]
    public void UnterminatedString_LoneQuoteAtEndOfFile_IsOneColumnWide()
    {
        const string source = "'";
        var (tokens, diagnostics) = Lexer.Tokenize(source);

        var diagnostic = SingleDiagnostic(diagnostics, UnterminatedStringMessage);
        // One consumed character: the span must not extend past it (and must
        // not precede the start column either).
        AssertSpan(source, diagnostic.Span, 1, 1, 1, 1, "'");

        Assert.Equal(2, tokens.Count);
        Assert.Equal(TokenKind.StringLiteral, tokens[0].Kind);
        Assert.Equal("", tokens[0].StringValue);
        Assert.Equal(TokenKind.EndOfFile, tokens[1].Kind);
    }
}
