using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// The location model (public API cleanup Task 3b): <see cref="SourcePosition"/> is a real
/// 1-based coordinate, <see cref="SourceSpan"/> the half-open range <c>[Start, End)</c> of two of
/// them (zero width allowed), and an ABSENT location is a <see langword="null"/>
/// <c>SourceSpan?</c> — never a sentinel coordinate and never the struct's default value.
/// These tests pin the invariants the types themselves must make obvious.
/// </summary>
public class SourceLocationTests
{
    // ── SourcePosition ───────────────────────────────────────────────────────

    [Theory]
    [InlineData(1, 1)]
    [InlineData(1, 7)]
    [InlineData(40, 1)]
    [InlineData(int.MaxValue, int.MaxValue)]
    public void Position_AcceptsOneBasedCoordinates(int line, int column)
    {
        var position = new SourcePosition(line, column);
        Assert.Equal(line, position.Line);
        Assert.Equal(column, position.Column);
        var (l, c) = position;
        Assert.Equal((line, column), (l, c));
    }

    [Theory]
    [InlineData(0, 1)]
    [InlineData(1, 0)]
    [InlineData(0, 0)]
    [InlineData(-1, 5)]
    [InlineData(5, -1)]
    [InlineData(int.MinValue, 1)]
    public void Position_RejectsZeroAndNegativeCoordinates(int line, int column)
        => Assert.Throws<ArgumentOutOfRangeException>(() => new SourcePosition(line, column));

    [Fact]
    public void Position_IsAValue_EqualByCoordinates()
    {
        var a = new SourcePosition(3, 4);
        var b = new SourcePosition(3, 4);
        Assert.Equal(a, b);
        Assert.True(a == b);
        Assert.False(a != b);
        Assert.Equal(a.GetHashCode(), b.GetHashCode());
        Assert.NotEqual(a, new SourcePosition(3, 5));
        Assert.NotEqual(a, new SourcePosition(4, 4));
        Assert.Equal("3:4", a.ToString());
    }

    [Fact]
    public void Position_OrdersByLineThenColumn()
    {
        var earlierLine = new SourcePosition(1, 99);
        var laterLine = new SourcePosition(2, 1);
        var sameLineLater = new SourcePosition(2, 8);

        Assert.True(earlierLine < laterLine);
        Assert.True(earlierLine <= laterLine);
        Assert.True(laterLine > earlierLine);
        Assert.True(laterLine >= earlierLine);
        Assert.True(laterLine < sameLineLater);
        Assert.True(laterLine <= laterLine);
        Assert.True(laterLine >= laterLine);
        Assert.False(laterLine < laterLine);
        Assert.False(laterLine > laterLine);
        Assert.True(earlierLine.CompareTo(laterLine) < 0);
        Assert.True(sameLineLater.CompareTo(laterLine) > 0);
        Assert.Equal(0, laterLine.CompareTo(new SourcePosition(2, 1)));
        Assert.Equal(earlierLine, SourcePosition.Min(laterLine, earlierLine));
        Assert.Equal(sameLineLater, SourcePosition.Max(laterLine, sameLineLater));

        var sorted = new[] { sameLineLater, earlierLine, laterLine }.Order().ToArray();
        Assert.Equal([earlierLine, laterLine, sameLineLater], sorted);
    }

    [Fact]
    public void Position_DefaultValue_IsNotAPositionAndCannotEnterASpan()
    {
        // The struct's default exists (zero coordinates) but is invalid: it is never
        // "absent", and a span refuses to be built from it.
        var none = default(SourcePosition);
        Assert.Equal((0, 0), (none.Line, none.Column));
        Assert.NotEqual(none, new SourcePosition(1, 1));
        Assert.Throws<ArgumentOutOfRangeException>(() => new SourceSpan(none, new SourcePosition(1, 1)));
        Assert.Throws<ArgumentOutOfRangeException>(() => new SourceSpan(new SourcePosition(1, 1), none));
        Assert.Throws<ArgumentOutOfRangeException>(() => new SourceSpan(none, none));
    }

    // ── SourceSpan ───────────────────────────────────────────────────────────

    [Fact]
    public void Span_IsHalfOpen_AndZeroWidthIsValid()
    {
        var oneCharacter = new SourceSpan(1, 1, 1, 2);
        Assert.Equal(new SourcePosition(1, 1), oneCharacter.Start);
        Assert.Equal(new SourcePosition(1, 2), oneCharacter.End);
        Assert.False(oneCharacter.IsEmpty);

        var insertionPoint = new SourceSpan(4, 15, 4, 15);
        Assert.True(insertionPoint.IsEmpty);
        Assert.Equal(insertionPoint.Start, insertionPoint.End);

        var (start, end) = oneCharacter;
        Assert.Equal((new SourcePosition(1, 1), new SourcePosition(1, 2)), (start, end));
        Assert.Equal(new SourceSpan(new SourcePosition(1, 1), new SourcePosition(1, 2)), oneCharacter);
    }

    [Theory]
    [InlineData(1, 2, 1, 1)]      // end column before start column
    [InlineData(2, 1, 1, 9)]      // end line before start line
    [InlineData(0, 1, 1, 1)]      // zero start line
    [InlineData(1, 0, 1, 1)]      // zero start column
    [InlineData(1, 1, 0, 1)]      // zero end line
    [InlineData(1, 1, 1, 0)]      // zero end column
    [InlineData(-3, 1, 1, 1)]     // negative
    public void Span_RejectsInvertedAndNonPositiveRanges(int startLine, int startColumn, int endLine, int endColumn)
        => Assert.Throws<ArgumentOutOfRangeException>(() => new SourceSpan(startLine, startColumn, endLine, endColumn));

    [Fact]
    public void Span_IsAValue_EqualByCoordinates_NeverByIdentity()
    {
        var a = new SourceSpan(2, 3, 2, 8);
        var b = new SourceSpan(new SourcePosition(2, 3), new SourcePosition(2, 8));
        Assert.Equal(a, b);
        Assert.True(a == b);
        Assert.Equal(a.GetHashCode(), b.GetHashCode());
        Assert.NotEqual(a, new SourceSpan(2, 3, 2, 9));
        Assert.NotEqual(a, new SourceSpan(2, 4, 2, 8));
        Assert.NotEqual(a, new SourceSpan(3, 3, 3, 8));

        // Boxed copies compare by value too, and a nullable wrapper compares through to it.
        object boxed = a;
        Assert.True(boxed.Equals(b));
        SourceSpan? maybe = b;
        Assert.True(maybe == a);
        Assert.Equal(a, maybe);
    }

    [Fact]
    public void Span_Contains_IncludesStart_ExcludesEnd()
    {
        var span = new SourceSpan(1, 3, 1, 6);   // columns 3, 4, 5
        Assert.False(span.Contains(new SourcePosition(1, 2)));
        Assert.True(span.Contains(new SourcePosition(1, 3)));
        Assert.True(span.Contains(new SourcePosition(1, 5)));
        Assert.False(span.Contains(new SourcePosition(1, 6)));
        Assert.False(span.Contains(new SourcePosition(1, 7)));
        Assert.False(span.Contains(new SourcePosition(2, 4)));
    }

    [Fact]
    public void Span_EmptySpanContainsNothing_AdjacentSpansShareNoPosition()
    {
        var empty = new SourceSpan(1, 4, 1, 4);
        Assert.False(empty.Contains(new SourcePosition(1, 4)));
        Assert.False(empty.Contains(new SourcePosition(1, 3)));

        var left = new SourceSpan(1, 1, 1, 4);
        var right = new SourceSpan(1, 4, 1, 7);
        var boundary = new SourcePosition(1, 4);
        Assert.False(left.Contains(boundary));
        Assert.True(right.Contains(boundary));
    }

    [Fact]
    public void Span_Contains_MultilineRange()
    {
        var span = new SourceSpan(2, 5, 4, 3);   // from 2:5 up to (not including) 4:3
        Assert.False(span.Contains(new SourcePosition(2, 4)));
        Assert.True(span.Contains(new SourcePosition(2, 5)));
        Assert.True(span.Contains(new SourcePosition(2, 1000)));
        Assert.True(span.Contains(new SourcePosition(3, 1)));
        Assert.True(span.Contains(new SourcePosition(4, 1)));
        Assert.True(span.Contains(new SourcePosition(4, 2)));
        Assert.False(span.Contains(new SourcePosition(4, 3)));
        Assert.False(span.Contains(new SourcePosition(5, 1)));
        Assert.False(span.Contains(new SourcePosition(1, 9)));
    }

    [Fact]
    public void Span_Union_IsTheHull()
    {
        var a = new SourceSpan(1, 1, 1, 5);
        var overlapping = new SourceSpan(1, 3, 1, 9);
        var adjacent = new SourceSpan(1, 5, 1, 7);
        var disjoint = new SourceSpan(3, 2, 3, 4);
        var empty = new SourceSpan(1, 12, 1, 12);
        var multiline = new SourceSpan(2, 8, 5, 2);

        Assert.Equal(new SourceSpan(1, 1, 1, 9), a.Union(overlapping));
        Assert.Equal(new SourceSpan(1, 1, 1, 7), a.Union(adjacent));
        Assert.Equal(new SourceSpan(1, 1, 3, 4), a.Union(disjoint));
        Assert.Equal(new SourceSpan(1, 1, 1, 12), a.Union(empty));   // the hull reaches the empty span's position
        Assert.Equal(new SourceSpan(1, 1, 5, 2), a.Union(multiline));
        Assert.Equal(new SourceSpan(2, 8, 5, 2), multiline.Union(new SourceSpan(3, 1, 3, 2)));   // contained
        Assert.Equal(a, a.Union(a));
        Assert.Equal(a.Union(disjoint), disjoint.Union(a));   // commutative
        Assert.Equal(empty, empty.Union(empty));
    }

    [Fact]
    public void Span_ToString_RendersTheHalfOpenRange_AndAnEmptySpanAsOnePosition()
    {
        Assert.Equal("[4:15, 4:21)", new SourceSpan(4, 15, 4, 21).ToString());
        Assert.Equal("[1:1, 2:3)", new SourceSpan(1, 1, 2, 3).ToString());
        Assert.Equal("[4:15]", new SourceSpan(4, 15, 4, 15).ToString());
    }

    [Fact]
    public void Span_DefaultValue_IsNotALocation_AndAbsenceIsNull()
    {
        // default(SourceSpan) carries zero coordinates: an invalid value, never "no location".
        var none = default(SourceSpan);
        Assert.Equal(default(SourcePosition), none.Start);
        Assert.NotEqual(none, new SourceSpan(1, 1, 1, 1));

        SourceSpan? absent = null;
        Assert.Null(absent);
        Assert.False(absent.HasValue);
        Assert.NotEqual(absent, (SourceSpan?)none);

        // The nullable wrapper is how every location-bearing surface spells absence.
        var diagnostic = new Diagnostic("unpositioned", DiagnosticSeverity.Error, Span: null);
        Assert.Null(diagnostic.Span);
        var error = new EvalError.DivByZero();
        Assert.Null(error.Span);
    }

    // ── Token spans ──────────────────────────────────────────────────────────

    [Fact]
    public void Token_Span_IsTheTokensExtent_EndOfFileIsEmpty()
    {
        var (tokens, diagnostics) = Lexer.Tokenize("abc = 'xy' # note\n  <= 42");
        Assert.Empty(diagnostics);

        foreach (var token in tokens)
        {
            Assert.Equal(new SourceSpan(token.Line, token.Column, token.Line, token.Column + token.Length), token.Span);
            Assert.Equal(token.Length == 0, token.Span.IsEmpty);
        }

        Assert.Equal(new SourceSpan(1, 1, 1, 4), tokens[0].Span);      // abc
        Assert.Equal(new SourceSpan(1, 5, 1, 6), tokens[1].Span);      // =
        Assert.Equal(new SourceSpan(1, 7, 1, 11), tokens[2].Span);     // 'xy' (quotes included)
        Assert.Equal(new SourceSpan(1, 12, 1, 18), tokens[3].Span);    // # note
        Assert.Equal(new SourceSpan(2, 3, 2, 5), tokens[4].Span);      // <=
        Assert.Equal(new SourceSpan(2, 6, 2, 8), tokens[5].Span);      // 42
        var eof = tokens[^1];
        Assert.Equal(TokenKind.EndOfFile, eof.Kind);
        Assert.Equal(new SourceSpan(2, 8, 2, 8), eof.Span);
        Assert.True(eof.Span.IsEmpty);
    }

    [Fact]
    public void Token_Span_CountsUtf16CodeUnits_SoASurrogatePairIsTwoColumnsWide()
    {
        // A supplementary character is not an identifier character: it lexes as ONE bad token
        // of length 2 whose span is two columns wide, positioned in UTF-16 code units.
        var (tokens, diagnostics) = Lexer.Tokenize("a \U0001F600 b");
        var bad = Assert.Single(tokens, t => t.Kind == TokenKind.Bad);
        Assert.Equal(2, bad.Length);
        Assert.Equal(new SourceSpan(1, 3, 1, 5), bad.Span);
        Assert.Equal(bad.Span, Assert.Single(diagnostics).Span);
        Assert.Equal(new SourceSpan(1, 6, 1, 7), tokens[^2].Span);   // b, after the two-unit pair
        Assert.Equal(new SourceSpan(1, 7, 1, 7), tokens[^1].Span);   // end of file

        // A BMP non-identifier character is one column wide.
        var (bmpTokens, bmpDiagnostics) = Lexer.Tokenize("a § b");
        var bmpBad = Assert.Single(bmpTokens, t => t.Kind == TokenKind.Bad);
        Assert.Equal(new SourceSpan(1, 3, 1, 4), bmpBad.Span);
        Assert.Equal(bmpBad.Span, Assert.Single(bmpDiagnostics).Span);
    }

    // ── Parser spans ─────────────────────────────────────────────────────────

    [Fact]
    public void Parser_EndOfInputDiagnostic_IsAnEmptySpanAtTheEndPosition()
    {
        var result = Parser.ParseSyntax("(1");
        var diagnostic = Assert.Single(result.Diagnostics);
        Assert.Equal("Expected ')' but found end of input.", diagnostic.Message);
        Assert.Equal(new SourceSpan(1, 3, 1, 3), diagnostic.Span);
        Assert.True(Assert.NotNull(diagnostic.Span).IsEmpty);

        // After a final newline the end position is the start of the next (empty) line.
        var afterNewline = Assert.Single(Parser.ParseSyntax("(1\n").Diagnostics);
        Assert.Equal(new SourceSpan(2, 1, 2, 1), afterNewline.Span);
    }

    [Fact]
    public void Parser_MissingTokenAndUnexpectedToken_AreTheOffendingTokensExtent()
    {
        var missing = Assert.Single(Parser.ParseSyntax("F(a b) =\n1").Diagnostics, d => d.Code == DiagnosticCode.UnseparatedSameLineItem);
        Assert.Equal(new SourceSpan(1, 5, 1, 6), missing.Span);   // the one-character `b`

        var unexpected = Assert.Single(Parser.ParseSyntax("1 + )").Diagnostics);
        Assert.Equal(new SourceSpan(1, 5, 1, 6), unexpected.Span);   // the one-character `)`

        var multiCharacter = Assert.Single(Parser.ParseSyntax("public = 1").Diagnostics, d => d.Message == "Unexpected 'public'.");
        Assert.Equal(new SourceSpan(1, 1, 1, 7), multiCharacter.Span);   // the six-character keyword
    }

    [Fact]
    public void Parser_ExpressionSpans_AreHalfOpen_IncludingMultilineConstructs()
    {
        var root = SourceProvenance.ParseValid("Total = 12 + 30\n(1,\n 2)").Root;
        var total = Assert.Single(root.Properties);
        Assert.Equal(new SourceSpan(1, 1, 1, 6), Assert.Single(total.DeclarationSpans));
        var body = Assert.IsType<Expr.Binary>(Assert.Single(Assert.IsType<Algorithm.User>(total.Value).Output));
        Assert.Equal(new SourceSpan(1, 9, 1, 16), body.Span);           // `12 + 30`
        Assert.Equal(new SourceSpan(1, 9, 1, 11), body.Left.Span);      // `12`
        Assert.Equal(new SourceSpan(1, 14, 1, 16), body.Right.Span);    // `30`

        var capture = Assert.IsType<Expr.Capture>(Assert.Single(root.Output));
        Assert.Equal(new SourceSpan(2, 1, 3, 4), capture.Span);         // `(1,` newline ` 2)`
        Assert.Equal(new SourceSpan(2, 2, 2, 3), capture.Body[0].Span);
        Assert.Equal(new SourceSpan(3, 2, 3, 3), capture.Body[1].Span);
        Assert.True(Assert.NotNull(capture.Span).Contains(new SourcePosition(2, 9)));   // past the first line's text, still inside
        Assert.False(Assert.NotNull(capture.Span).Contains(new SourcePosition(3, 4)));  // the exclusive end
    }

    // ── Error conversion ─────────────────────────────────────────────────────

    [Fact]
    public void KatLangError_CarriesTheStructuredSpan_OrNoneAtAll()
    {
        var positioned = KatLangError.FromDiagnostic(
            new Diagnostic("bad", DiagnosticSeverity.Error, new SourceSpan(4, 15, 4, 21)) { Code = DiagnosticCode.UnexpectedToken });
        Assert.Equal(new SourceSpan(4, 15, 4, 21), positioned.Span);
        Assert.Equal("[4:15] bad", positioned.ToString());

        var unpositioned = KatLangError.FromDiagnostic(
            new Diagnostic("limit", DiagnosticSeverity.Error, Span: null) { Code = DiagnosticCode.SourceLengthExceeded });
        Assert.Null(unpositioned.Span);
        Assert.Equal("limit", unpositioned.ToString());

        var spannedError = KatLangError.FromEvalError(new EvalError.DivByZero { Span = new SourceSpan(2, 1, 2, 6) });
        Assert.Equal(new SourceSpan(2, 1, 2, 6), spannedError.Span);
        Assert.StartsWith("[2:1] ", spannedError.ToString(), StringComparison.Ordinal);

        var spanlessError = KatLangError.FromEvalError(new EvalError.DivByZero());
        Assert.Null(spanlessError.Span);
        Assert.Equal(spanlessError.Message, spanlessError.ToString());
    }

    [Fact]
    public void WholeDocumentLimits_AreUnpositionedDiagnostics()
    {
        // A limit on the whole source has no position of its own: null, not line 1 column 1.
        var oversized = new string('1', SourceProcessingLimits.MaxSupportedSourceLength + 1);
        var diagnostic = Assert.Single(Parser.ParseSyntax(oversized).Diagnostics);
        Assert.Equal(DiagnosticCode.SourceLengthExceeded, diagnostic.Code);
        Assert.Null(diagnostic.Span);
        var error = Assert.Single(Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(oversized)).Errors);
        Assert.Null(error.Span);
        Assert.Equal(error.Message, error.ToString());
    }

    [Fact]
    public void HostBuiltSpanlessProgram_ReportsAnUnpositionedError()
    {
        // No node carries a span, so no attach-if-missing step can supply one: the error stays absent.
        var root = new Algorithm.User(null, [], [], [], [new Expr.Binary(BinaryOp.Div, new Expr.Num(1), new Expr.Num(0))]);
        var result = Evaluator.Run(new Expr.AlgorithmExpr(root));
        Assert.True(result.IsError);
        Assert.Null(result.Error.Span);
        Assert.Null(KatLangError.FromEvalError(result.Error).Span);
    }

    // ── Semantic model position queries ─────────────────────────────────────

    [Fact]
    public void SemanticModel_PositionQueries_UseHalfOpenSites()
    {
        var model = SemanticModelBuilder.Build(Parser.Parse("Total = 5\nTotal + 1"));
        var reference = Assert.Single(model.FindResolutions("Total"), r => r.Occurrence.Kind == OccurrenceKind.ResolveReference);
        Assert.Equal(new SourceSpan(2, 1, 2, 6), reference.Occurrence.Span);

        Assert.Same(reference, model.FindResolutionAt(new SourcePosition(2, 1)));   // first column: inside
        Assert.Same(reference, model.FindResolutionAt(new SourcePosition(2, 5)));   // last character: inside
        Assert.Null(model.FindResolutionAt(new SourcePosition(2, 6)));              // the exclusive end: outside
        Assert.Null(model.FindPropertyAt(new SourcePosition(2, 6)));
        Assert.NotNull(model.FindPropertyAt(new SourcePosition(2, 3)));
        Assert.Contains(model.GetVisibleSymbolsAt(new SourcePosition(2, 3)), s => s.Name == "Total");
    }
}
