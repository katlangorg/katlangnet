namespace KatLang.Tests;

/// <summary>
/// The MARKER ATTACHMENT LAW (SYN-07B follow-up), pinned as one table:
/// unary structural/annotation markers must be directly attached to the
/// syntax they modify, while ordinary expression operators may be spaced
/// freely.
///
/// <list type="table">
/// <item><description>collecting parameter — <c>*x</c> (never <c>* x</c>)</description></item>
/// <item><description>postfix spread — <c>x*</c> (never <c>x *</c>)</description></item>
/// <item><description>prefix Grace — <c>~x</c> (never <c>~ x</c>)</description></item>
/// <item><description>postfix Grace — <c>x~</c> (never <c>x ~</c>)</description></item>
/// <item><description>multiplication — <c>x * y</c>, whitespace and line breaks optional</description></item>
/// </list>
///
/// Attachment is decided by ONE helper (<c>Parser.IsDirectlyAttached</c>:
/// exact source-offset adjacency, no whitespace/comment/newline between the
/// tokens), and for the postfix star it is checked only AFTER the SYN-07B
/// classification has established that the star is a spread marker (nothing
/// that could be a right operand follows it). A detached marker never
/// silently keeps the marker's meaning and never silently becomes the other
/// valid operation: it is a parse-phase error, and the recovered tree keeps
/// the plain name/operand (no collecting binding, no spread node, no Grace
/// weight).
/// </summary>
public class MarkerAttachmentTests
{
    private const string SpreadAttachmentFragment =
        "The spread marker `*` must be directly attached to the expression it spreads";

    private const string CollectAttachmentFragment =
        "The collect marker `*` must be directly attached to its binding name";

    private const string GraceAttachmentFragment =
        "The Grace marker `~` must be directly attached to the name it decorates";

    private static string Display(string source)
    {
        var result = KatLangEngine.Run(source);
        Assert.True(result is RunResult.Success, $"Expected success but got: {result.ToDisplayString()}");
        return result.ToDisplayString().Replace("\r\n", "\n");
    }

    /// <summary>
    /// The source must parse CLEANLY (never an evaluator outcome on illegal
    /// source) and display <paramref name="expected"/>.
    /// </summary>
    private static void AssertValid(string source, string expected)
    {
        var parse = Parser.Parse(source);
        Assert.False(parse.HasErrors, $"expected a clean parse for:{Environment.NewLine}{source}{Environment.NewLine}"
            + string.Join(Environment.NewLine, parse.Diagnostics.Select(static d => $"[{d.Code}] {d.Message}")));
        Assert.Equal(expected, Display(source));
    }

    /// <summary>
    /// The source must be rejected by the PARSER (raw syntax phase, before any
    /// elaboration) with exactly one error carrying <paramref name="code"/>
    /// whose message contains <paramref name="fragment"/>, and the engine must
    /// surface it as a parse failure with the same-named public error code.
    /// </summary>
    private static Diagnostic AssertRejected(string source, DiagnosticCode code, string fragment)
    {
        var syntax = Parser.ParseSyntax(source);
        var error = Assert.Single(syntax.Diagnostics);
        Assert.Equal(DiagnosticSeverity.Error, error.Severity);
        Assert.Equal(code, error.Code);
        Assert.Contains(fragment, error.Message, StringComparison.Ordinal);

        var elaborated = Parser.Parse(source);
        Assert.Equal([error.Message], elaborated.Diagnostics.Select(static d => d.Message));

        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        var publicError = Assert.Single(failure.Errors);
        Assert.Equal(Enum.Parse<KatLangErrorCode>(code.ToString()), publicError.Code);
        return error;
    }

    // ── Multiplication: spacing and line breaks never matter ────────────────

    [Theory]
    [InlineData("4*6")]
    [InlineData("4* 6")]
    [InlineData("4 *6")]
    [InlineData("4 * 6")]
    [InlineData("A = 4\nB = 6\nA*\nB")]
    [InlineData("A = 4\nB = 6\nA *\nB")]
    [InlineData("A = 4\nB = 6\nA*B")]
    [InlineData("A = 4\nB = 6\nA* B")]
    [InlineData("A = 4\nB = 6\nA *B")]
    [InlineData("A = 4\nB = 6\nA * B")]
    // Definition bodies: the trailing star continues the line-bounded body
    // across the newline like every trailing binary operator.
    [InlineData("A = 4\nB = 6\nX = A*\nB\nX")]
    [InlineData("A = 4\nB = 6\nX = A *\nB\nX")]
    [InlineData("A = 4\nB = 6\nX = A*B\nX")]
    [InlineData("A = 4\nB = 6\nX = A * B\nX")]
    // Inside an open call-argument list and a brace body.
    [InlineData("F(v) = v\nA = 4\nB = 6\nF(A*\nB)")]
    [InlineData("F(v) = v\nA = 4\nB = 6\nF(A *\nB)")]
    [InlineData("A = 4\nB = 6\n{ A*\nB }")]
    [InlineData("A = 4\nB = 6\n{ A *\nB }")]
    public void Multiplication_IsSpacingAndLineBreakIndependent(string source)
    {
        AssertValid(source, "24");
        var parse = Parser.Parse(source);
        Assert.DoesNotContain(parse.Diagnostics, static d => d.Code == DiagnosticCode.InvalidSpreadMarker);
    }

    [Theory]
    [InlineData("(PRODUCT)", "24")]
    [InlineData("[PRODUCT]", "[24]")]
    [InlineData("Add(x, y) = x + y\n0.Add(PRODUCT)", "24")]
    [InlineData("Id(x) = x\n[Id((PRODUCT))]", "[24]")]
    public void NestedMultiplicationLayouts_HaveTheSameElaboratedStructureAndValue(string context, string expected)
    {
        string? baseline = null;
        foreach (var product in new[] { "A*~~B", "A * ~~B", "A*\n~~B", "A *\r\n# comment\r\n~~B" })
        {
            var source = "A = 4\nB = 6\n" + context.Replace("PRODUCT", product);
            var parsed = SourceProvenance.ParseValid(source);
            // Compare the entire semantic tree, including bundle boundaries
            // and binding identities; source spans alone differ by layout.
            var structure = LeanAstEncoder.EncodeProgram(parsed.Root);
            baseline ??= structure;
            Assert.Equal(baseline, structure);
            Assert.Equal(expected, Display(source));
        }
    }

    [Fact]
    public void Multiplication_NeverDependsOnAttachment_EvenWhenTheOperandIsADeclarationLookalike()
    {
        // `B` beginning an expression lexically does not make the star
        // multiplication when `B = 5` is a declaration head, and attachment
        // plays no part in either verdict: the attached star before the
        // declaration is a spread, the detached one is the attachment error —
        // never the multiplication `A * B`.
        Assert.Equal("1\n2\n5", Display("A = (1, 2)\nA*\nB = 5\nB"));
        var detached = AssertRejected("A = (1, 2)\nA *\nB = 5\nB", DiagnosticCode.InvalidSpreadMarker, SpreadAttachmentFragment);
        Assert.Equal(new SourceSpan(2, 1, 2, 3), detached.Span);
    }

    // ── Postfix spread: attached forms valid, detached forms rejected ───────

    [Theory]
    [InlineData("F(*items) = items\nvalues = (1, 2)\nF(values*)", "[1, 2]")]
    [InlineData("F(*items) = items\nvalues = (1, 2)\nother = 3\nF(values*, other)", "[1, 2, 3]")]
    [InlineData("values = (1, 2)\n(values*)", "(1, 2)")]
    [InlineData("values = (1, 2)\n[values*]", "[1, 2]")]
    [InlineData("values = (1, 2)\n{ values* }", "(1, 2)")]
    [InlineData("values = (1, 2)\nvalues*,\n3", "1\n2\n3")]
    [InlineData("values = (1, 2)\nvalues*", "1\n2")]
    [InlineData("values = (1, 2)\nvalues*\nB = 5\nB", "1\n2\n5")]
    [InlineData("values = (1, 2)\nX = (values*)\nX", "(1, 2)")]
    [InlineData("values = (1, 2)\nvalues**", "1\n2")]
    // Spread stays total: scalars and strings supply themselves as one item.
    [InlineData("F(*items) = items\nF(5*)", "[5]")]
    [InlineData("F(*items) = items\nF('text'*)", "[text]")]
    [InlineData("()*, 7", "7")]
    public void AttachedPostfixSpread_IsValid(string source, string expected)
        => AssertValid(source, expected);

    [Theory]
    [InlineData("F(*items) = items\nvalues = (1, 2)\nF(values *)", 3, 3, 3, 10)]
    [InlineData("F(*items) = items\nvalues = (1, 2)\nother = 3\nF(values *, other)", 4, 3, 4, 10)]
    [InlineData("values = (1, 2)\n(values *)", 2, 2, 2, 9)]
    [InlineData("values = (1, 2)\n[values *]", 2, 2, 2, 9)]
    [InlineData("values = (1, 2)\n{ values * }", 2, 3, 2, 10)]
    [InlineData("values = (1, 2)\nvalues *,\n3", 2, 1, 2, 8)]
    [InlineData("values = (1, 2)\nvalues *", 2, 1, 2, 8)]
    [InlineData("values = (1, 2)\nvalues *\nB = 5\nB", 2, 1, 2, 8)]
    [InlineData("values = (1, 2)\nX = (values *)\nX", 2, 6, 2, 13)]
    [InlineData("values = (1, 2)\nvalues* *", 2, 1, 2, 9)]
    [InlineData("F(*items) = items\nF(5 *)", 2, 3, 2, 5)]
    public void DetachedPostfixSpread_IsRejected(string source, int startLine, int startColumn, int endLine, int endColumn)
    {
        var error = AssertRejected(source, DiagnosticCode.InvalidSpreadMarker, SpreadAttachmentFragment);
        Assert.Equal(new SourceSpan(startLine, startColumn, endLine, endColumn), error.Span);
    }

    [Fact]
    public void DetachedStar_WithARightOperand_IsMultiplication_NotAnAttachmentError()
    {
        // The two stages in order: classification first (a right operand
        // follows, on the next line — multiplication), attachment never asked.
        AssertValid("values = 6\nother = 7\nvalues *\nother", "42");
    }

    // ── Collect marker: attached forms valid, detached forms rejected ───────

    [Theory]
    [InlineData("F(*x) = x\nF(1, 2)", "[1, 2]")]
    [InlineData("F(a, *x, z) = x\nF(1, 2, 3, 4)", "[2, 3]")]
    [InlineData("F((a, *x, z)) = x\nF((1, 2, 3, 4))", "[2, 3]")]
    [InlineData("*items = 1, 2\nitems", "[1, 2]")]
    [InlineData("a, *rest = 1, 2, 3\nrest", "[2, 3]")]
    [InlineData("public F(*x) = x\nF(1)", "[1]")]
    public void AttachedCollectMarker_IsValid(string source, string expected)
        => AssertValid(source, expected);

    [Theory]
    [InlineData("F(* x) = x\nF(1, 2)", 1, 3, 1, 5)]
    [InlineData("F(a, * x, z) = x\nF(1, 2, 3, 4)", 1, 6, 1, 8)]
    [InlineData("F((a, * x, z)) = x\nF((1, 2, 3, 4))", 1, 7, 1, 9)]
    [InlineData("* items = 1, 2\nitems", 1, 1, 1, 7)]
    [InlineData("a, * rest = 1, 2, 3\nrest", 1, 4, 1, 9)]
    [InlineData("public F(* x) = x\nF(1)", 1, 10, 1, 12)]
    public void DetachedCollectMarker_IsRejected_OnEveryBindingSurface(string source, int startLine, int startColumn, int endLine, int endColumn)
    {
        // Explicit parameter lists, mixed prefix/collecting/suffix lists,
        // nested sequence-value patterns, lone and mixed deconstruction, and
        // public clause heads all go through the two collect-marker parsers
        // (pattern atoms and binding-pattern assignment); both use the ONE
        // attachment helper.
        var error = AssertRejected(source, DiagnosticCode.InvalidCollectMarker, CollectAttachmentFragment);
        Assert.Equal(new SourceSpan(startLine, startColumn, endLine, endColumn), error.Span);
    }

    // ── Grace: attached forms keep their ordering semantics, detached rejected ──

    [Theory]
    // `Divide(2, 10)`: without Grace the inferred order is (y, x) → 2 / 10.
    [InlineData("Divide = y / x\nDivide(2, 10)", "0.2")]
    // Prefix `~x` moves x one position earlier → order (x, y) → 10 / 2.
    [InlineData("Divide = y / ~x\nDivide(2, 10)", "5")]
    // Postfix `y~` moves y one position later → order (x, y) → 10 / 2.
    [InlineData("Divide = y~ / x\nDivide(2, 10)", "5")]
    // Repeated attached markers use the ordinary weight arithmetic.
    [InlineData("Divide = y / ~~x\nDivide(2, 10)", "5")]
    // `~x~` nets to weight zero: the plain (y, x) order → 2 / 10.
    [InlineData("Divide = y / ~x~\nDivide(2, 10)", "0.2")]
    // Grace on a callee name and in a brace body.
    [InlineData("K = {\n  a\n  ~b\n}\nK(10, 20)", "(20, 10)")]
    // Grace composed with ordinary dot syntax (the two supported forms).
    [InlineData("K(a, t) = a~.t\nK(7, {a+1})", "8")]
    [InlineData("K(a, t) = a.~t\nK(7, {a+1})", "8")]
    [InlineData("K(a, t) = a~~.t\nK(7, {a+1})", "8")]
    [InlineData("K(a, t) = a~.~t\nK(7, {a+1})", "8")]
    public void AttachedGrace_KeepsItsParameterOrderSemantics(string source, string expected)
        => AssertValid(source, expected);

    [Theory]
    [InlineData("Divide = y / ~ x\nDivide(2, 10)", "x", 1, 14, 1, 16)]
    [InlineData("Divide = y ~ / x\nDivide(2, 10)", "y", 1, 10, 1, 12)]
    [InlineData("Divide = y / ~ ~x\nDivide(2, 10)", "x", 1, 14, 1, 17)]
    [InlineData("Divide = y / ~x ~\nDivide(2, 10)", "x", 1, 14, 1, 17)]
    [InlineData("K = {\n  a\n  ~ b\n}\nK(10, 20)", "b", 3, 3, 3, 5)]
    [InlineData("K(a, t) = a ~ .t\nK(7, {a+1})", "a", 1, 11, 1, 13)]
    [InlineData("K(a, t) = a ~.t\nK(7, {a+1})", "a", 1, 11, 1, 13)]
    [InlineData("K(a, t) = a.~ t\nK(7, {a+1})", "t", 1, 13, 1, 15)]
    public void DetachedGrace_IsRejected(string source, string name, int startLine, int startColumn, int endLine, int endColumn)
    {
        var error = AssertRejected(source, DiagnosticCode.InvalidGraceMarker, GraceAttachmentFragment);
        Assert.Equal(
            $"The Grace marker `~` must be directly attached to the name it decorates: write `~{name}` or `{name}~`.",
            error.Message);
        Assert.Equal(new SourceSpan(startLine, startColumn, endLine, endColumn), error.Span);
    }

    [Fact]
    public void DetachedGrace_RecoversToThePlainName_WithoutAnyWeight()
    {
        // A detached marker decorates nothing: the recovered occurrence is the
        // plain name, so the inferred order is the ungraced (y, x).
        var parse = Parser.Parse("Divide = y / ~ x\nDivide(2, 10)");
        Assert.Single(parse.Diagnostics);
        var divide = Assert.Single(parse.Root.Properties, static p => p.Name == "Divide");
        Assert.Equal(["y", "x"], divide.Value.Params);
        var body = Assert.IsType<Expr.Binary>(Assert.Single(divide.Value.Output));
        Assert.IsType<Expr.Param>(body.Right); // no Grace wrapper survives

        var syntax = Parser.ParseSyntax("Divide = y ~ / x");
        var rawBody = Assert.IsType<Expr.Binary>(Assert.Single(Assert.Single(syntax.Root.Properties).Value.Output));
        Assert.IsType<Expr.Resolve>(rawBody.Left);
    }

    [Theory]
    [InlineData("~~ ~x")]
    [InlineData("x~ ~~")]
    [InlineData("~x~ ~")]
    public void GraceRun_WithAnInteriorGap_DiscardsTheWholeOccurrencesWeight(string occurrence)
    {
        var source = "K = y / " + occurrence;
        AssertRejected(source, DiagnosticCode.InvalidGraceMarker, GraceAttachmentFragment);
        var raw = Parser.ParseSyntax(source);
        var body = Assert.IsType<Expr.Binary>(Assert.Single(Assert.Single(raw.Root.Properties).Value.Output));
        Assert.Equal("x", Assert.IsType<Expr.Resolve>(body.Right).Name);
        var recovered = SourceProvenance.ParseAllowingDiagnostics(source);
        Assert.Equal(["y", "x"], Assert.Single(recovered.Root.Properties).Value.Params);
    }

    [Fact]
    public void GraceEligibilityErrors_KeepTheirOwnDiagnostic()
    {
        // The attachment law never rewords the one-name law: a marker on a
        // compound operand is still the eligibility error, attached or not.
        foreach (var source in new[] { "K = f(x)~", "K = f(x) ~", "K = 5~", "K = (x + y)~" })
        {
            var parse = Parser.ParseSyntax(source);
            var error = Assert.Single(parse.Diagnostics);
            Assert.Equal(DiagnosticCode.InvalidGraceMarker, error.Code);
            Assert.Equal("Grace `~` can only be applied to a parameter or name occurrence.", error.Message);
        }
    }

    // ── The attachment helper is shared: comments and newlines break attachment ──

    [Theory]
    [InlineData("values = (1, 2)\nvalues # note\n*", DiagnosticCode.InvalidCollectMarker)]
    [InlineData("F(*\nx) = x\nF(1)", DiagnosticCode.InvalidCollectMarker)]
    public void MarkerSeparatedByANewline_IsNeverAttached(string source, DiagnosticCode expected)
    {
        // A star on a later line is never a spread continuation (the
        // '*'-led-line rule reaches the collect-marker diagnostics instead),
        // and a collect marker never binds across a newline.
        var parse = Parser.ParseSyntax(source);
        Assert.True(parse.HasErrors);
        Assert.Contains(parse.Diagnostics, d => d.Code == expected);
    }
}
