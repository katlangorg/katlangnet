namespace KatLang.Tests;

/// <summary>
/// Exact diagnostic-span regressions for the two lexer diagnostics that carry
/// a scanned-run span: oversized number literals and unterminated string
/// literals. Spans are half-open: the exclusive end column IS the lexer's live
/// cursor column (one past the last consumed code unit), so the span slices
/// exactly the offending text and equals the placeholder token's own span.
/// Tokenization itself must be unaffected: the placeholder number token and the
/// string token are still produced with their original positions and lengths.
/// </summary>
public class LexerDiagnosticSpanTests
{
    private const string NumberTooLargeMessage = "Number literal is too large.";
    private const string UnterminatedStringMessage = "Unterminated string literal.";

    /// <summary>
    /// A 42-character literal whose value exceeds Decimal128's finite range
    /// (~1e6180 parses to an infinity). 42 digits alone are merely rounded now,
    /// so the oversized probe needs an exponent to genuinely overflow; the
    /// length is kept at 42 so the span expectations below stay byte-for-byte.
    /// </summary>
    private static readonly string OversizedDigits = new string('9', 37) + "e6144";

    private static Diagnostic SingleDiagnostic(
        IReadOnlyList<Diagnostic> diagnostics, string expectedMessage)
    {
        var diagnostic = Assert.Single(diagnostics);
        Assert.Equal(expectedMessage, diagnostic.Message);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        return diagnostic;
    }

    private static void AssertSpan(
        string source, SourceSpan? actual,
        int startLine, int startColumn, int endLine, int endColumn,
        string expectedSlice)
    {
        var span = Assert.NotNull(actual);
        Assert.Equal(new SourceSpan(startLine, startColumn, endLine, endColumn), span);

        // Half-open: the slice runs from the start column up to (not including) the end column.
        Assert.Equal(span.Start.Line, span.End.Line);
        var line = source.Split('\n')[span.Start.Line - 1].TrimEnd('\r');
        Assert.Equal(
            expectedSlice,
            line.Substring(span.Start.Column - 1, span.End.Column - span.Start.Column));
    }

    // ── Number literal is too large ─────────────────────────────────────────

    [Fact]
    public void OversizedNumber_AtColumnOne_EndsJustPastTheFinalDigit()
    {
        var source = OversizedDigits;
        var (tokens, diagnostics) = Lexer.Tokenize(source);

        var diagnostic = SingleDiagnostic(diagnostics, NumberTooLargeMessage);
        AssertSpan(source, diagnostic.Span, 1, 1, 1, 43, OversizedDigits);

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
    public void OversizedNumber_AfterPrefixOnSameLine_EndsJustPastTheFinalDigit()
    {
        var source = "X = " + OversizedDigits;
        var (tokens, diagnostics) = Lexer.Tokenize(source);

        var diagnostic = SingleDiagnostic(diagnostics, NumberTooLargeMessage);
        AssertSpan(source, diagnostic.Span, 1, 5, 1, 47, OversizedDigits);

        Assert.Equal(
            new[] { TokenKind.Identifier, TokenKind.Equals, TokenKind.Number, TokenKind.EndOfFile },
            tokens.Select(t => t.Kind).ToArray());
    }

    // ── Unterminated string literal ─────────────────────────────────────────

    [Fact]
    public void UnterminatedString_MidLine_EndsJustPastTheLastConsumedCodeUnit()
    {
        const string source = "X = 'abc\nY = 2";
        var (tokens, diagnostics) = Lexer.Tokenize(source);

        var diagnostic = SingleDiagnostic(diagnostics, UnterminatedStringMessage);
        // The unterminated token is `'abc`, columns 5..8 on line 1, so the half-open
        // span ends at column 9 (the line break is not consumed).
        AssertSpan(source, diagnostic.Span, 1, 5, 1, 9, "'abc");

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
    public void UnterminatedString_LoneQuoteAtEndOfFile_IsOneCodeUnitWide()
    {
        const string source = "'";
        var (tokens, diagnostics) = Lexer.Tokenize(source);

        var diagnostic = SingleDiagnostic(diagnostics, UnterminatedStringMessage);
        // One consumed character: the span must not extend past it (and must
        // not precede the start column either).
        AssertSpan(source, diagnostic.Span, 1, 1, 1, 2, "'");

        Assert.Equal(2, tokens.Count);
        Assert.Equal(TokenKind.StringLiteral, tokens[0].Kind);
        Assert.Equal("", tokens[0].StringValue);
        Assert.Equal(TokenKind.EndOfFile, tokens[1].Kind);
    }
}
