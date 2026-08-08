namespace KatLang.Tests;

/// <summary>
/// Exact diagnostic-span regressions for parser error reporting.
/// The repository convention is inclusive spans: EndColumn is the last
/// offending source column. These tests pin three families:
/// - direct `if` arity diagnostics cover the whole call (identical to the
///   resulting <see cref="Expr.Call"/> node span), never the token after it;
/// - clause-head grace diagnostics cover the offending marker run plus its
///   pattern atom, never the delimiter after the atom;
/// - the at-most-one-collecting-binding deconstruction diagnostic includes
///   the collect marker, not just the binding name.
/// Every test asserts all four span coordinates and the exact source slice.
/// </summary>
public class ParserDiagnosticSpanTests
{
    private const string GraceInClauseHeadMessage = "Grace is not allowed in clause-head patterns.";

    private static Diagnostic SingleDiagnosticContaining(string source, string messageFragment)
    {
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        return Assert.Single(result.Diagnostics, d => d.Message.Contains(messageFragment));
    }

    private static void AssertSpan(
        string source,
        Diagnostic diagnostic,
        int startLine, int startColumn, int endLine, int endColumn,
        string expectedSlice)
    {
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Equal(startLine, diagnostic.Span.StartLineNumber);
        Assert.Equal(startColumn, diagnostic.Span.StartColumn);
        Assert.Equal(endLine, diagnostic.Span.EndLineNumber);
        Assert.Equal(endColumn, diagnostic.Span.EndColumn);
        Assert.Equal(expectedSlice, SourceSlice(source, diagnostic.Span));
    }

    /// <summary>
    /// The source text covered by a single-line span under the inclusive
    /// 1-based line/column convention.
    /// </summary>
    private static string SourceSlice(string source, SourceSpan span)
    {
        Assert.Equal(span.StartLineNumber, span.EndLineNumber);
        var line = source.Split('\n')[span.StartLineNumber - 1].TrimEnd('\r');
        return line.Substring(span.StartColumn - 1, span.EndColumn - span.StartColumn + 1);
    }

    // ── F3: direct `if` arity diagnostics span the whole call ───────────────

    [Fact]
    public void IfArity_CallFollowedByOutputRow_SpansTheCall()
    {
        const string source = "if(1, 2)\nNext";
        var result = Parser.ParseSyntax(source);
        var diagnostic = Assert.Single(
            result.Diagnostics,
            d => d.Message == "Builtin 'if' expects 3 arguments: condition, whenTrue, whenFalse. Got 2.");

        AssertSpan(source, diagnostic, 1, 1, 1, 8, "if(1, 2)");
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(call.Span, diagnostic.Span);
    }

    [Fact]
    public void IfArity_CallFollowedByPropertyDeclaration_SpansTheCall()
    {
        const string source = "X = 1\nif(1, 2)\nLongIdentifierHere = 3\nLongIdentifierHere";
        var result = Parser.ParseSyntax(source);
        var diagnostic = Assert.Single(
            result.Diagnostics,
            d => d.Message == "Builtin 'if' expects 3 arguments: condition, whenTrue, whenFalse. Got 2.");

        AssertSpan(source, diagnostic, 2, 1, 2, 8, "if(1, 2)");
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(call.Span, diagnostic.Span);
    }

    [Fact]
    public void IfArity_CallInsidePropertyValue_SpansTheCall()
    {
        const string source = "P = if(1, 2)\nP";
        var result = Parser.ParseSyntax(source);
        var diagnostic = Assert.Single(
            result.Diagnostics,
            d => d.Message == "Builtin 'if' expects 3 arguments: condition, whenTrue, whenFalse. Got 2.");

        AssertSpan(source, diagnostic, 1, 5, 1, 12, "if(1, 2)");
        var property = Assert.Single(result.Root.Properties, p => p.Name == "P");
        var call = Assert.IsType<Expr.Call>(Assert.Single(property.Value.Output));
        Assert.Equal(call.Span, diagnostic.Span);
    }

    [Fact]
    public void IfArity_CallAtEndOfFile_SpansTheCall()
    {
        const string source = "if(1, 2)";
        var result = Parser.ParseSyntax(source);
        var diagnostic = Assert.Single(
            result.Diagnostics,
            d => d.Message == "Builtin 'if' expects 3 arguments: condition, whenTrue, whenFalse. Got 2.");

        AssertSpan(source, diagnostic, 1, 1, 1, 8, "if(1, 2)");
        var call = Assert.IsType<Expr.Call>(Assert.Single(result.Root.Output));
        Assert.Equal(call.Span, diagnostic.Span);
    }

    [Fact]
    public void IfArity_ZeroArguments_SpansTheCall()
    {
        const string source = "if()\nNext";
        var result = Parser.ParseSyntax(source);
        var diagnostic = Assert.Single(
            result.Diagnostics,
            d => d.Message == "Builtin 'if' expects 3 arguments: condition, whenTrue, whenFalse. Got 0.");

        AssertSpan(source, diagnostic, 1, 1, 1, 4, "if()");
        var call = Assert.IsType<Expr.Call>(result.Root.Output[0]);
        Assert.Equal(call.Span, diagnostic.Span);
    }

    [Fact]
    public void IfArity_TooManyArguments_SpansTheCall()
    {
        const string source = "if(1, 2, 3, 4)";
        var result = Parser.ParseSyntax(source);
        var diagnostic = Assert.Single(
            result.Diagnostics,
            d => d.Message == "Builtin 'if' expects 3 arguments: condition, whenTrue, whenFalse. Got 4.");

        AssertSpan(source, diagnostic, 1, 1, 1, 14, "if(1, 2, 3, 4)");
        var call = Assert.IsType<Expr.Call>(Assert.Single(result.Root.Output));
        Assert.Equal(call.Span, diagnostic.Span);
    }

    // ── F4: clause-head grace diagnostics span the marker + atom ────────────

    [Fact]
    public void ClauseHeadGrace_PrefixMarker_SpansMarkerAndName()
    {
        const string source = "F(~a, b) = a";
        var diagnostic = SingleDiagnosticContaining(source, GraceInClauseHeadMessage);
        Assert.Equal(GraceInClauseHeadMessage, diagnostic.Message);
        AssertSpan(source, diagnostic, 1, 3, 1, 4, "~a");
    }

    [Fact]
    public void ClauseHeadGrace_PostfixMarker_SpansNameAndMarker()
    {
        const string source = "F(a~, b) = a";
        var diagnostic = SingleDiagnosticContaining(source, GraceInClauseHeadMessage);
        Assert.Equal(GraceInClauseHeadMessage, diagnostic.Message);
        AssertSpan(source, diagnostic, 1, 3, 1, 4, "a~");
    }

    [Fact]
    public void ClauseHeadGrace_PrefixMarkerInNestedPattern_SpansMarkerAndName()
    {
        const string source = "F(a, (~b, c)) = a";
        var diagnostic = SingleDiagnosticContaining(source, GraceInClauseHeadMessage);
        AssertSpan(source, diagnostic, 1, 7, 1, 8, "~b");
    }

    [Fact]
    public void ClauseHeadGrace_RepeatedPrefixMarkers_SpanTheWholeRunAndName()
    {
        const string source = "F(~~a, b) = a";
        var diagnostic = SingleDiagnosticContaining(source, GraceInClauseHeadMessage);
        AssertSpan(source, diagnostic, 1, 3, 1, 5, "~~a");
    }

    [Fact]
    public void ClauseHeadGrace_PrefixAndPostfixMarkers_SpanTheWholeRun()
    {
        const string source = "F(~a~, b) = a";
        var diagnostic = SingleDiagnosticContaining(source, GraceInClauseHeadMessage);
        AssertSpan(source, diagnostic, 1, 3, 1, 5, "~a~");
    }

    [Fact]
    public void ClauseHeadGrace_RepeatedPostfixMarkers_SpanNameAndWholeRun()
    {
        const string source = "F(a~~, b) = a";
        var diagnostic = SingleDiagnosticContaining(source, GraceInClauseHeadMessage);
        AssertSpan(source, diagnostic, 1, 3, 1, 5, "a~~");
    }

    [Fact]
    public void ClauseHeadGrace_PrefixMarkerWithoutIdentifier_SpansTheMarker()
    {
        // The prefix marker is followed by a number, not an identifier: the
        // grace diagnostic covers the marker itself, and recovery still
        // parses `2` as an ordinary literal pattern atom.
        const string source = "F(~2, b) = a";
        var diagnostic = SingleDiagnosticContaining(source, GraceInClauseHeadMessage);
        AssertSpan(source, diagnostic, 1, 3, 1, 3, "~");
    }

    [Fact]
    public void ClauseHeadGrace_PrefixMarkerBeforeClosingParen_SpansTheMarker()
    {
        // No atom follows at all; the grace diagnostic still covers the
        // marker (further recovery diagnostics may follow it).
        const string source = "F(~) = 1";
        var diagnostic = SingleDiagnosticContaining(source, GraceInClauseHeadMessage);
        AssertSpan(source, diagnostic, 1, 3, 1, 3, "~");
    }

    // ── F4 (related): collecting-binding diagnostic includes the marker ─────

    [Fact]
    public void DeconstructionMultipleCollectingBindings_SpanIncludesCollectMarker()
    {
        const string source = "*a, *b = (1, 2)";
        var diagnostic = SingleDiagnosticContaining(
            source, "at most one collecting binding (`*name`)");
        Assert.Equal(
            "A deconstruction binding pattern may contain at most one collecting binding (`*name`).",
            diagnostic.Message);
        AssertSpan(source, diagnostic, 1, 1, 1, 2, "*a");
    }
}
