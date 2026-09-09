namespace KatLang.Tests;

/// <summary>
/// Exact diagnostic-span regressions for parser error reporting.
/// The repository convention is inclusive spans: EndColumn is the last
/// offending source column. These tests pin two families:
/// - clause-head grace diagnostics cover the offending marker run plus its
///   pattern atom, never the delimiter after the atom;
/// - the at-most-one-collecting-binding deconstruction diagnostic includes
///   the collect marker, not just the binding name.
/// Every test asserts all four span coordinates and the exact source slice.
///
/// <para>The `if` arity family that used to live here left with SYN-05: the
/// parser no longer counts a call's arguments from its callee SPELLING, so the
/// whole-call span guarantee moved to the authoritative arity boundary and is
/// pinned by <see cref="BuiltinCallableIdentityTests.ArityDiagnostic_SpansTheWholeCall"/>
/// against the RESOLVED signature.</para>
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

    // ── K5-R1: expression-position grace diagnostics span the marker run ────

    private const string GraceLawMessage = "Grace `~` can only be applied to a parameter or name occurrence.";

    [Fact]
    public void LineFinalGraceAfterCall_SpansTheMarker()
    {
        const string source = "K = f(x)~\ny";
        var diagnostic = SingleDiagnosticContaining(source, GraceLawMessage);
        Assert.Equal(GraceLawMessage, diagnostic.Message);
        AssertSpan(source, diagnostic, 1, 9, 1, 9, "~");
    }

    [Fact]
    public void LineFinalGraceRunAfterCall_SpansTheWholeRun()
    {
        const string source = "K = f(x)~~~\ny";
        var diagnostic = SingleDiagnosticContaining(source, GraceLawMessage);
        AssertSpan(source, diagnostic, 1, 9, 1, 11, "~~~");
    }

    [Fact]
    public void SameLineGraceAfterLiteral_SpansTheMarker()
    {
        const string source = "c = 3\n5~ c";
        var diagnostic = SingleDiagnosticContaining(source, GraceLawMessage);
        AssertSpan(source, diagnostic, 2, 2, 2, 2, "~");
    }

    [Fact]
    public void LoneGraceRunLine_SpansOnlyItsOwnLine()
    {
        // The run is physical-line-local: the next line's `~a` is not part
        // of it (and stays valid prefix Grace, so it reports nothing).
        const string source = "a = 1\n~~\n~a";
        var diagnostic = SingleDiagnosticContaining(source, GraceLawMessage);
        AssertSpan(source, diagnostic, 2, 1, 2, 2, "~~");
    }

    [Fact]
    public void PrefixGraceRunBeforeNonName_SpansTheRun()
    {
        // The diagnostic covers the marker run, never the token after it.
        const string source = "~~42";
        var diagnostic = SingleDiagnosticContaining(source, GraceLawMessage);
        AssertSpan(source, diagnostic, 1, 1, 1, 2, "~~");
    }

    [Fact]
    public void PostfixGraceOnCompoundReceiverBeforeDot_SpansTheMarker()
    {
        const string source = "K = (x + y)~.t";
        var diagnostic = SingleDiagnosticContaining(source, GraceLawMessage);
        AssertSpan(source, diagnostic, 1, 12, 1, 12, "~");
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
