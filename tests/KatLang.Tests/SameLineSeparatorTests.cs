namespace KatLang.Tests;

/// <summary>
/// SYN-07A — the SAME-LINE SEPARATOR RULE, pinned as one table: whitespace
/// never creates a slot boundary. Once an expression is closed, a second
/// independent expression-list slot on the same physical line needs <c>,</c>;
/// a declaration must begin a new row. A physical newline keeps separating
/// slots wherever the context
/// already allowed it (root output, brace bodies, parenthesized groups,
/// call-argument lists, list literals), a definition body still ends at its
/// newline, and ordinary expression continuation (operators, call
/// delimiters, <c>:</c>, <c>.</c>, attached markers) is never a boundary.
///
/// <para>The rule is decided at ONE ownership point for slots
/// (<c>Parser.StartsNextExpressionListSlot</c>, reached by every expression
/// list through <c>ParseExpressionListOperand</c>) and at the body loop's
/// per-item row check for declarations. Both report the one generic
/// diagnostic <see cref="DiagnosticCode.UnseparatedSameLineItem"/> at the
/// first token of the second item — naming the three repairs without
/// guessing intent — and then RECOVER by admitting the item where it was
/// written: as the next slot of the same list (so <c>P = a b</c> keeps
/// <c>b</c> inside P's body and never leaks it to the enclosing scope) or as
/// the declaration it spells. A boundary that a more specific recovery
/// already diagnosed (a rejected Grace run, a detached marker, a stray
/// closer, a bad token, an open-target leftover) is never reported twice.</para>
///
/// <para>SYN-07B is untouched: star classification, marker attachment,
/// multiplication across a newline, and the spread boundaries keep their
/// meaning — except that a slot before a spread now needs its comma like
/// every other slot (<c>A, B*</c>, never <c>A B*</c>).</para>
/// </summary>
public class SameLineSeparatorTests
{
    private const string Message =
        "Unexpected item after a closed expression on the same line. Add ',' to separate slots, add an operator to continue the expression, or start a declaration on a new line.";

    /// <summary>
    /// The same family's report for a parameter-pattern list (a clause head
    /// or a nested sequence-value pattern): the comma is the only repair
    /// there, so the wording names just that and the construct.
    /// </summary>
    private const string PatternMessage =
        "Unexpected item after a parameter pattern on the same line. Add ',' to separate the patterns of a parameter list.";

    private static string Display(string source)
    {
        var result = KatLangEngine.Run(source);
        Assert.True(result is RunResult.Success, $"Expected success but got: {result.ToDisplayString()}");
        return result.ToDisplayString().Replace("\r\n", "\n");
    }

    /// <summary>The source parses CLEANLY and displays <paramref name="expected"/>.</summary>
    private static void AssertValid(string source, string expected)
    {
        AssertParsesCleanly(source);
        Assert.Equal(expected, Display(source));
    }

    private static void AssertParsesCleanly(string source)
    {
        var parse = Parser.Parse(source);
        Assert.False(parse.HasErrors, $"expected a clean parse for:{Environment.NewLine}{source}{Environment.NewLine}"
            + string.Join(Environment.NewLine, parse.Diagnostics.Select(static d => $"[{d.Code}] {d.Message}")));
    }

    /// <summary>
    /// The raw syntax phase reports EXACTLY the separator diagnostics listed
    /// in <paramref name="itemStarts"/> ("line:column" of the first token of
    /// each unseparated second item, in source order), each with the exact
    /// wording <paramref name="message"/> (the generic expression-list wording
    /// unless the list is a parameter-pattern list) and a one-token primary
    /// span starting there; the elaborated parse keeps them, and the engine
    /// surfaces the family as a parse failure under the same-named public
    /// error code.
    /// </summary>
    private static IReadOnlyList<Diagnostic> AssertRejected(string source, string itemStarts, string message = Message)
    {
        var expectedStarts = itemStarts.Split(';', StringSplitOptions.RemoveEmptyEntries)
            .Select(static s => s.Split(':'))
            .Select(static parts => (Line: int.Parse(parts[0]), Column: int.Parse(parts[1])))
            .ToList();

        var syntax = Parser.ParseSyntax(source);
        Assert.Equal(expectedStarts.Count, syntax.Diagnostics.Count);
        foreach (var (diagnostic, expected) in syntax.Diagnostics.Zip(expectedStarts))
        {
            Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
            Assert.Equal(DiagnosticCode.UnseparatedSameLineItem, diagnostic.Code);
            Assert.Equal(message, diagnostic.Message);
            Assert.Equal(expected.Line, diagnostic.Span.StartLineNumber);
            Assert.Equal(expected.Column, diagnostic.Span.StartColumn);
            Assert.Equal(expected.Line, diagnostic.Span.EndLineNumber);
            var token = Assert.Single(Lexer.Tokenize(source).Tokens,
                t => t.Line == expected.Line && t.Column == expected.Column);
            Assert.Equal(expected.Column + token.Length - 1, diagnostic.Span.EndColumn);
        }

        var elaborated = Parser.Parse(source);
        if (message == PatternMessage)
            Assert.Equal(syntax.Diagnostics, elaborated.Diagnostics);
        Assert.Equal(
            syntax.Diagnostics.Where(static d => d.Code == DiagnosticCode.UnseparatedSameLineItem),
            elaborated.Diagnostics.Where(static d => d.Code == DiagnosticCode.UnseparatedSameLineItem));

        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        Assert.Contains(failure.Errors, static e => e.Code == KatLangErrorCode.UnseparatedSameLineItem);
        Assert.All(failure.Errors.Where(static e => e.Code == KatLangErrorCode.UnseparatedSameLineItem),
            e => Assert.Equal(message, e.Message));
        return syntax.Diagnostics;
    }

    // ── Rejected: two slots on one line without a comma ─────────────────────

    [Theory]
    [InlineData("1 2", "1:3")]
    [InlineData("1 2 3", "1:3;1:5")]
    [InlineData("(1 2)", "1:4")]
    [InlineData("[1 2 3]", "1:4;1:6")]
    [InlineData("{ 1 2 }", "1:5")]
    [InlineData("F(a, b) = a + b\nF(1 2)", "2:5")]
    [InlineData("F(a, b) = a + b\nF(1 -2 3)", "2:8")]
    [InlineData("if(1, 2 3)", "1:9")]
    [InlineData("2(3)", "1:2")]
    [InlineData("2 (3)", "1:3")]
    [InlineData("(1 + 2) (3)", "1:9")]
    [InlineData("[1, 2](3)", "1:7")]
    [InlineData("A = [10, 20]\nA[1]", "2:2")]
    [InlineData("m = 5\n2m", "2:2")]
    [InlineData("2pi", "1:2")]
    [InlineData("F = 2x\nF(3)", "1:6")]
    [InlineData("sqrt 2", "1:6")]
    [InlineData("a = 1\nb = 2\nP = a b\nP", "3:7")]
    [InlineData("Add = a + b 2.Add(6)", "1:13")]
    [InlineData("Values = 1, 2, 3\nValues.sum Values.count", "2:12")]
    [InlineData("F(a, b) = a + b\nF(1, 2) F(3, 4)", "2:9")]
    [InlineData("NetSalary = 5\n('neto' NetSalary)", "2:9")]
    [InlineData("K = A~B\nK(1, 2)", "1:7")]
    [InlineData("'a' 'b'", "1:5")]
    [InlineData("F(x) = x\nF(1)(2)", "2:5")]
    public void SameLineSlots_WithoutComma_AreRejectedAtTheSecondItem(string source, string itemStarts)
        => AssertRejected(source, itemStarts);

    // ── Rejected: a same-line slot before a spread (SYN-07B interaction) ────

    [Theory]
    [InlineData("A = (1, 2)\nB = (3, 4)\nA B*", "3:3")]
    [InlineData("A = (1, 2)\nB = (3, 4)\nC = 5\nA B*, C", "4:3")]
    [InlineData("Use(*v) = v\na = 1\nb = (2, 3)\nUse(a b*)", "4:7")]
    [InlineData("X(*vals) = vals.count\nb = (1, 2)\nX(7 b*)", "3:5")]
    public void SameLineSlotBeforeASpread_NeedsTheCommaLikeEveryOtherSlot(string source, string itemStarts)
        => AssertRejected(source, itemStarts);

    // ── Rejected: a declaration after other content on its line ────────────

    [Theory]
    [InlineData("1 P = 3\nP", "1:3")]
    [InlineData("x = 3 y = 4\nx + y", "1:7")]
    [InlineData("x = 1 y = 2 x + y", "1:7;1:13")]
    [InlineData("V = (1, 2, 3)\nV.map { d = 2 n * d }", "2:15")]
    [InlineData("a = 1\na b, c = 1\nb", "2:3")]
    [InlineData("1 public P = 3\nP", "1:3")]
    [InlineData("{ x = 1 y = 2 }", "1:9")]
    [InlineData("F(0) = 1 F(x) = 2\nF(1)", "1:10")]
    [InlineData("x, *rest = 1, 2, 3 y = 4\nrest", "1:20")]
    public void DeclarationAfterContentOnTheSameLine_IsRejected(string source, string itemStarts)
        => AssertRejected(source, itemStarts);

    [Fact]
    public void OpenAfterContentOnTheSameLine_ReportsTheRowBoundaryAndTheExistingPlacementRule()
    {
        // Two distinct defects, two diagnostics: the row boundary before
        // `open` and the (unchanged) placement rule that an open precedes
        // properties and output.
        var syntax = Parser.ParseSyntax("x = 1 open Math\nx");
        Assert.Equal(
            [DiagnosticCode.UnseparatedSameLineItem, DiagnosticCode.InvalidOpenDeclaration],
            syntax.Diagnostics.Select(static d => d.Code));
        Assert.Equal((1, 7), (syntax.Diagnostics[0].Span.StartLineNumber, syntax.Diagnostics[0].Span.StartColumn));
    }

    // ── Recovery: the item stays where it was written ───────────────────────

    [Fact]
    public void Recovery_DefinitionBody_KeepsTheSecondSlotInsideTheBody()
    {
        // `P = a b`: the diagnostic is at `b`, and `b` is P's SECOND body slot —
        // it never leaks into the root output.
        var root = SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot("a = 1\nb = 2\nP = a b\nP");
        var property = Assert.Single(root.Properties, static p => p.Name == "P");
        var body = Assert.IsType<Algorithm.User>(property.Value);
        Assert.Equal(["a", "b"], body.Output.Select(static e => Assert.IsType<Expr.Resolve>(e).Name));
        Assert.Equal("P", Assert.IsType<Expr.Resolve>(Assert.Single(root.Output)).Name);
    }

    [Fact]
    public void Recovery_SameLineDeclaration_StaysADeclaration()
    {
        // `x = 3 y = 4`: `y = 4` is recovered as a property, never swallowed
        // into x's body and never discarded.
        var root = SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot("x = 3 y = 4\nx + y");
        Assert.Equal(["x", "y"], root.Properties.Select(static p => p.Name));
        Assert.Equal(3m, Assert.IsType<Expr.Num>(Assert.Single(Assert.IsType<Algorithm.User>(root.Properties[0].Value).Output)).Value);
        Assert.Equal(4m, Assert.IsType<Expr.Num>(Assert.Single(Assert.IsType<Algorithm.User>(root.Properties[1].Value).Output)).Value);
        Assert.IsType<Expr.Binary>(Assert.Single(root.Output));
    }

    [Fact]
    public void Recovery_OutputRowThenDeclaration_KeepsBoth()
    {
        var root = SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot("1 P = 3\nP");
        Assert.Equal("P", Assert.Single(root.Properties).Name);
        Assert.Equal(2, root.Output.Count);
        Assert.Equal(1m, Assert.IsType<Expr.Num>(root.Output[0]).Value);
        Assert.Equal("P", Assert.IsType<Expr.Resolve>(root.Output[1]).Name);
    }

    [Fact]
    public void Recovery_ExpressionListContexts_KeepTheSlotShapeOfTheCommaSpelling()
    {
        var call = Assert.IsType<Expr.Call>(Assert.Single(SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot("F(a, b) = a + b\nF(1 2)").Output));
        Assert.Equal(2, call.Args.Count);

        var capture = Assert.IsType<Expr.Capture>(Assert.Single(SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot("(1 2)").Output));
        Assert.Equal([1m, 2m], capture.Body.Select(static e => Assert.IsType<Expr.Num>(e).Value));

        var list = Assert.IsType<Expr.ListLiteral>(Assert.Single(SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot("[1 2 3]").Output));
        Assert.Equal([1m, 2m, 3m], list.Items.Select(static e => Assert.IsType<Expr.Num>(e).Value));

        var block = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot("{ 1 2 }").Output));
        Assert.Equal([1m, 2m], block.Algorithm.Output.Select(static e => Assert.IsType<Expr.Num>(e).Value));

        var rows = SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot("1 2").Output;
        Assert.Equal([1m, 2m], rows.Select(static e => Assert.IsType<Expr.Num>(e).Value));
    }

    [Fact]
    public void Recovery_OneLineBraceBody_KeepsTheExpressionInsideTheDefinition()
    {
        // `{ d = 2 n * d }`: the second item is recovered into d's body (the
        // structure the boundary was found in), so the block has no output
        // row — the program is invalid, and nothing silently re-parents `n * d`.
        var block = Assert.IsType<Expr.AlgorithmExpr>(
            Assert.Single(SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot("{ d = 2 n * d }").Output));
        var d = Assert.Single(block.Algorithm.Properties);
        Assert.Equal("d", d.Name);
        Assert.Equal(2, Assert.IsType<Algorithm.User>(d.Value).Output.Count);
        Assert.Empty(block.Algorithm.Output);
    }

    // ── Preserved: explicit commas, newline rows, continuations ─────────────

    [Theory]
    [InlineData("1, 2", "1\n2")]
    [InlineData("(1, 2)", "(1, 2)")]
    [InlineData("[1, 2, 3]", "[1, 2, 3]")]
    [InlineData("F(a, b) = a + b\nF(1, 2)", "3")]
    [InlineData("F(a, b) = a + b\nF(1, -2)", "-1")]
    [InlineData("NetSalary = 5\n('neto', NetSalary)", "(neto, 5)")]
    [InlineData("A = (1, 2)\nB = (3, 4)\nA, B*", "(1, 2)\n3\n4")]
    [InlineData("Use(*v) = v\na = 1\nb = (2, 3)\nUse(a, b*)", "[1, 2, 3]")]
    [InlineData("X(*vals) = vals.count\nb = (1, 2)\nX(7, b*)", "3")]
    [InlineData("K = A~, B\nK(1, 2)", "(2, 1)")]
    // Newline-separated slots stay valid wherever the context is open.
    [InlineData("1\n2\n3", "1\n2\n3")]
    [InlineData("F(a, b) = a + b\nF(\n    1\n    2\n)", "3")]
    [InlineData("[\n    1\n    2\n]", "[1, 2]")]
    [InlineData("(\n    1\n    2\n)", "(1, 2)")]
    [InlineData("{\n    1, 2\n    3\n}", "(1, 2, 3)")]
    [InlineData("1,\n2", "1\n2")]
    [InlineData("F(a, b) = a + b\nF( 1\n  , 2 )", "3")]
    // Ordinary call/postfix continuations.
    [InlineData("F(a, b) = a + b\nF (1, 2)", "3")]
    [InlineData("A = { public B(x) = x + 1 }\nA.B (1)", "2")]
    [InlineData("A = { public B(x, y) = x + y }\nA.B (1, 2)", "3")]
    [InlineData("V = (1, 2, 3)\nV.map { n * 2 }", "[2, 4, 6]")]
    [InlineData("Pair = (1, 2)\nPair :0", "1")]
    [InlineData("K(a, t) = a~.t\nK(7, {a+1})", "8")]
    [InlineData("K(a, t) = a.~t\nK(7, {a+1})", "8")]
    [InlineData("K(a, t) = a~ .t\nK(7, {a+1})", "8")]
    [InlineData("F(x) = x\n(1, 2).F", "(1, 2)")]
    // Multiline operator continuation versus a new row.
    [InlineData("A = 5\nA -\n1", "4")]
    [InlineData("A = 5\nA -1", "4")]
    [InlineData("A = 5\nA\n-1", "5\n-1")]
    [InlineData("Total = 1 +\n    2\nTotal", "3")]
    [InlineData("(1, 2, 3)\n.map { n * 2 }\n.sum", "12")]
    // Declarations on their own rows.
    [InlineData("x = 3\ny = 4\nx + y", "7")]
    [InlineData("{\n    x = 1\n    x + 1\n}", "2")]
    [InlineData("x = 1\n# comment\ny = 2\nx + y", "3")]
    [InlineData("A = { public X = 1 }\nA.X", "1")]
    [InlineData("x, *rest = 1, 2, 3\nrest", "[2, 3]")]
    // SYN-07B star behavior is untouched.
    [InlineData("A = 2\nB = 3\nA*\nB", "6")]
    [InlineData("A = 2\nB = 3\nA *\nB", "6")]
    [InlineData("A = 2\nB = 3\nA* B", "6")]
    [InlineData("A = 2\nB = 3\nA*, B", "2\n3")]
    [InlineData("A = 2\nB = 3\nA*,\nB", "2\n3")]
    [InlineData("A = (1, 2)\nA*\nB = 5\nB", "1\n2\n5")]
    [InlineData("A = (1, 2)\nB = 3\nX = (A*)\nB\nX", "3\n(1, 2)")]
    [InlineData("A = (1, 2)\nB = 3\nX = { A* }\nB\nX", "3\n(1, 2)")]
    public void ExplicitCommasNewlineRowsAndContinuations_StayValid(string source, string expected)
        => AssertValid(source, expected);

    [Fact]
    public void SignedArgument_StaysOneSubtractionExpression()
    {
        // `F(1 -2)` is the ONE argument `1 - 2` (arity error at evaluation),
        // never two slots and never the separator diagnostic; `F(1, -2)` is
        // the two-argument call.
        const string definition = "F(a, b) = a + b\n";
        AssertParsesCleanly(definition + "F(1 -2)");
        var call = Assert.IsType<Expr.Call>(Assert.Single(SourceProvenance.ParseSyntaxValidRoot(definition + "F(1 -2)").Output));
        var argument = Assert.IsType<Expr.Binary>(Assert.Single(call.Args));
        Assert.Equal(BinaryOp.Sub, argument.Op);
        EvaluatorTestSupport.AssertEvalFailsWithArityMismatch(definition + "F(1 -2)", expected: 2, actual: 1);
        AssertValid(definition + "F(1, -2)", "-1");
    }

    [Fact]
    public void CalculationReport_NewlineRowsNeedNoCommas()
    {
        const string source = """
            InitialSpeed = 30
            Gravity = 9.8

            v(t) = InitialSpeed - Gravity * t
            s(t) = InitialSpeed * t - 0.5 * Gravity * t^2

            t_highest = InitialSpeed / Gravity

            'time, velocity and displacement at highest point'
            t_highest
            v(t_highest)
            s(t_highest)
            """;

        AssertValid(
            source,
            "time, velocity and displacement at highest point\n"
            + "3.061224489795918367346938775510204\n"
            + "0.00000000000000000000000000000000\n"
            + "45.91836734693877551020408163265306");
        Assert.Equal(4, SourceProvenance.ParseValid(source).Root.Output.Count);
    }

    [Fact]
    public void BraceBodyFirstItemMayShareTheOpenerLine()
    {
        AssertParsesCleanly("{ public X = 1 }");
        AssertParsesCleanly("F(v) = v\nF{ x = 1\nx + 1 }");
        AssertValid("F(v) = v\nF{ x = 1\nx + 1 }", "2");
    }

    [Theory]
    [InlineData("(P = 1)")]
    [InlineData("F((P = 1))")]
    [InlineData("F(P = 1)")]
    [InlineData("(public P = 1)")]
    [InlineData("(P(x) = x)")]
    [InlineData("(x, y = 1, 2)")]
    [InlineData("(*items = 1, 2)")]
    [InlineData("(open Math)")]
    public void ParenthesizedFirstItem_StillRejectsDeclarationsIndependently(string source)
    {
        // The row-boundary exemption for a body's first item is not permission
        // to declare in parentheses. Its separate grammar guard remains active.
        var syntax = Parser.ParseSyntax(source);
        Assert.Equal(DiagnosticCode.DeclarationInParentheses, Assert.Single(syntax.Diagnostics).Code);
        Assert.Empty(syntax.Root.Properties);
        Assert.Empty(syntax.Root.Opens);
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        Assert.Contains(failure.Errors, static e => e.Code == KatLangErrorCode.DeclarationInParentheses);
    }

    // ── Cascade suppression: one diagnostic per malformed boundary ──────────

    [Theory]
    [InlineData("F(a, b) = a + b\nc = 3\nF(1)~ c", "InvalidGraceMarker")]
    [InlineData("x = 5\n1 ~~~x", "InvalidGraceMarker")]
    [InlineData("y = 2\nx = 1\nx ~ y", "InvalidGraceMarker")]
    [InlineData("~ 5", "InvalidGraceMarker")]
    [InlineData("Divide = y ~ / x\nDivide(2, 10)", "InvalidGraceMarker")]
    [InlineData("A = 1\nA = 1 ) 2\nA", "DuplicateProperty;UnexpectedToken")]
    [InlineData("x = (1, 2)\nx:-1", "UnexpectedToken")]
    [InlineData("= 1", "UnexpectedToken")]
    [InlineData("1 ; 2", "UnsupportedSemicolon")]
    [InlineData("open Math Physics\n1", "InvalidOpenTargetList")]
    [InlineData("open Math ; Physics\n1", "InvalidOpenTargetList")]
    [InlineData("public open Math\n1", "InvalidOpenDeclaration")]
    [InlineData("A = (1, 2)\nA *", "InvalidSpreadMarker")]
    [InlineData("A = (1, 2)\nA *, 3", "InvalidSpreadMarker")]
    [InlineData("Collect(*items) = items\nA = (1, 2)\nCollect(A *)", "InvalidSpreadMarker")]
    [InlineData("A = (1, 2)\nB = (3, 4)\nA*\nB*", "MisplacedSpread")]
    [InlineData("1 @ 2", "UnexpectedCharacter")]
    public void ARecoveryThatOwnsTheBoundary_ReportsOnlyItsOwnDiagnostic(string source, string expectedCodes)
    {
        var syntax = Parser.ParseSyntax(source);
        Assert.Equal(
            expectedCodes.Split(';').Select(Enum.Parse<DiagnosticCode>),
            syntax.Diagnostics.Select(static d => d.Code));
    }

    [Fact]
    public void ALaterIndependentSameLineItem_IsStillReported()
    {
        // The rejected Grace run owns the boundary before `c`; the boundary
        // before `4` is a separate defect and gets its own report.
        var syntax = Parser.ParseSyntax("F(a, b) = a + b\nc = 3\nF(1)~ c 4");
        Assert.Equal(
            [DiagnosticCode.InvalidGraceMarker, DiagnosticCode.UnseparatedSameLineItem],
            syntax.Diagnostics.Select(static d => d.Code));
        Assert.Equal((3, 9), (syntax.Diagnostics[1].Span.StartLineNumber, syntax.Diagnostics[1].Span.StartColumn));
    }

    [Theory]
    [InlineData("1 ] 2 3", 7)]
    [InlineData("1 = 2 3", 7)]
    [InlineData("1 public 2 3", 12)]
    [InlineData("1 public = 2 3", 14)]
    public void UnexpectedBodyToken_DoesNotAcquireASeparatorDiagnostic(string source, int laterColumn)
    {
        var syntax = Parser.ParseSyntax(source);
        Assert.Equal(
            source.Contains("public =", StringComparison.Ordinal)
                ? [DiagnosticCode.UnexpectedToken, DiagnosticCode.UnexpectedToken, DiagnosticCode.UnseparatedSameLineItem]
                : new[] { DiagnosticCode.UnexpectedToken, DiagnosticCode.UnseparatedSameLineItem },
            syntax.Diagnostics.Select(static d => d.Code));
        Assert.Equal(new SourceSpan(1, laterColumn, 1, laterColumn), syntax.Diagnostics[^1].Span);
    }

    [Theory]
    [InlineData("~ x y", 5)]
    [InlineData("~ x~ y", 6)]
    [InlineData("~~ x y", 6)]
    [InlineData("~ ~x y", 6)]
    [InlineData("F(~ x y)", 7)]
    [InlineData("P = ~ x y", 9)]
    [InlineData("a.~ t y", 7)]
    public void DetachedPrefixGrace_DoesNotOwnTheBoundaryAfterItsName(string source, int laterColumn)
    {
        var syntax = Parser.ParseSyntax(source);
        Assert.Equal(
            [DiagnosticCode.InvalidGraceMarker, DiagnosticCode.UnseparatedSameLineItem],
            syntax.Diagnostics.Select(static d => d.Code));
        Assert.Equal(new SourceSpan(1, laterColumn, 1, laterColumn), syntax.Diagnostics[1].Span);
    }

    [Fact]
    public void DetachedPrefixAndPostfixGrace_OnlyOwnTheBoundaryAfterThePostfixRun()
    {
        var syntax = Parser.ParseSyntax("P = ~ x ~ y z");
        Assert.Equal(
            [DiagnosticCode.InvalidGraceMarker, DiagnosticCode.UnseparatedSameLineItem],
            syntax.Diagnostics.Select(static d => d.Code));
        Assert.Equal(new SourceSpan(1, 13, 1, 13), syntax.Diagnostics[1].Span);
        var body = Assert.IsType<Algorithm.User>(Assert.Single(syntax.Root.Properties).Value);
        Assert.Equal(["x", "y", "z"], body.Output.Select(static e => Assert.IsType<Expr.Resolve>(e).Name));
        Assert.Empty(syntax.Root.Output);
    }

    [Fact]
    public void CollectMarkerWithoutAnOperand_OwnsOnlyItsRecoveryBoundary()
    {
        var syntax = Parser.ParseSyntax("* public P = 1 Q = 2");
        Assert.Equal(
            [DiagnosticCode.InvalidCollectMarker, DiagnosticCode.UnseparatedSameLineItem],
            syntax.Diagnostics.Select(static d => d.Code));
        Assert.Equal(new SourceSpan(1, 16, 1, 16), syntax.Diagnostics[1].Span);
        Assert.Equal(["P", "Q"], syntax.Root.Properties.Select(static p => p.Name));
    }

    // ── Parameter-pattern lists: the same rule, the comma as the one repair ──
    // Clause heads and nested sequence-value patterns are comma-separated
    // lists too. A same-line token that can begin another pattern item without
    // a comma is the same family's diagnostic (pattern-worded, since a pattern
    // has no operator to continue with and no declaration to move), reported
    // ONCE at that item and recovered as the next pattern of the SAME list, so
    // the head's ')' and '=' are found where written and the body stays the
    // head's body — never the generic closing-delimiter cascade that used to
    // recover `= a + b` as unrelated root rows with root implicit parameters.

    [Theory]
    [InlineData("F(a b) = a + b\nF(1, 2)", "1:5")]
    [InlineData("F(x y) = x + y\nF(1, 2)", "1:5")]
    [InlineData("F(1 2) = 3\nF(1, 2)", "1:5")]
    [InlineData("F((a b)) = a\nF((1, 2))", "1:6")]
    [InlineData("F(a, *b c) = a\nF(1, 2, 3)", "1:9")]
    [InlineData("F(a *b) = a\nF(1, 2)", "1:5")]
    [InlineData("F(a (b, c)) = a\nF(1, (2, 3))", "1:5")]
    [InlineData("F((a) b) = a\nF((1), 2)", "1:7")]
    [InlineData("F(1 -2) = 3\nF(1, -2)", "1:5")]
    [InlineData("F(a 'x') = a\nF(1, 'x')", "1:5")]
    [InlineData("F(a b c) = a\nF(1, 2, 3)", "1:5;1:7")]
    [InlineData("F(a b, c d) = a\nF(1, 2, 3, 4)", "1:5;1:10")]
    [InlineData("public F(a b) = a + b\nF(1, 2)", "1:12")]
    [InlineData("F(0, 0) = 0\nF(x y) = x + y\nF(1, 2)", "2:5")]
    [InlineData("M = {\n    public F(a b) = a + b\n}\nM.F(1, 2)", "2:16")]
    [InlineData("F(a bee) = a + bee", "1:5")]
    [InlineData("F(a b) = a + b\r\nF(1, 2)", "1:5")]
    [InlineData("F(\n a, # first\n b c # missing comma\n) = a\nF(1, 2, 3)", "3:4")]
    [InlineData("F(a (b c)) = a\nF(1, (2, 3))", "1:5;1:8")]
    [InlineData("F((a b) c) = a\nF((1, 2), 3)", "1:6;1:9")]
    [InlineData("F(a b) = a + b\nG(x) = x\nG(4)", "1:5")]
    public void ParameterPatternList_WithoutComma_IsRejectedOnceAtTheNextPattern(string source, string itemStarts)
    {
        var diagnostics = AssertRejected(source, itemStarts, PatternMessage);
        // Compare the WHOLE recovered program with the clean comma spelling,
        // including nested patterns, clause families, bodies, and later rows.
        // The existing AST encoder omits source coordinates but retains the
        // language's structural distinctions; never evaluate malformed source.
        var repaired = source;
        var tokens = Lexer.Tokenize(source).Tokens;
        foreach (var diagnostic in diagnostics.Reverse())
        {
            var token = Assert.Single(tokens, t => t.Line == diagnostic.Span.StartLineNumber
                && t.Column == diagnostic.Span.StartColumn);
            repaired = repaired.Insert(token.Position, ",");
        }
        var recovered = SourceProvenance.ParseAllowingDiagnostics(source).Root;
        Assert.Empty(recovered.Parameters);
        Assert.Equal(LeanAstEncoder.EncodeProgram(SourceProvenance.ParseValid(repaired).Root),
            LeanAstEncoder.EncodeProgram(recovered));
    }

    [Fact]
    public void Recovery_ParameterPatternList_KeepsTheItemInTheSameHead()
    {
        // `F(a b) = a + b`: `b` is F's SECOND parameter and `a + b` is F's body.
        // Nothing leaks to the root — no stray rows, no implicit parameters —
        // and the call row stays the only root output.
        var parse = SourceProvenance.ParseAllowingDiagnostics("F(a b) = a + b\nF(1, 2)");
        Assert.Equal([DiagnosticCode.UnseparatedSameLineItem], parse.Diagnostics.Select(static d => d.Code));
        var root = Assert.IsType<Algorithm.User>(parse.Root);
        var f = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties).Value);
        Assert.Equal(["a", "b"], f.Params);
        Assert.IsType<Expr.Binary>(Assert.Single(f.Output));
        Assert.Empty(root.Parameters);
        var call = Assert.IsType<Expr.Call>(Assert.Single(root.Output));
        Assert.Equal(2, call.Args.Count);

        // Literal heads recover as the clause pattern their comma spelling writes.
        var literal = Assert.IsType<Algorithm.Conditional>(
            Assert.Single(SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot("F(1 2) = 3").Properties).Value);
        var pattern = Assert.IsType<Pattern.SequenceValue>(Assert.Single(literal.Branches).Pattern);
        Assert.Equal(2, pattern.Items.Count);
        Assert.Equal(1m, Assert.IsType<Pattern.LitInt>(pattern.Items[0]).Value);
        Assert.Equal(2m, Assert.IsType<Pattern.LitInt>(pattern.Items[1]).Value);

        // A nested pattern recovers inside ITS parentheses.
        var nested = Assert.IsType<Algorithm.User>(
            Assert.Single(SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot("F((a b)) = a").Properties).Value);
        var sequence = Assert.IsType<SequenceValueParameterPattern>(Assert.Single(nested.ExplicitParameterPatterns));
        Assert.Equal(["a", "b"], sequence.Items.Select(static item => Assert.IsType<CaptureParameterPattern>(item).Name));

        // The item after a collecting binding recovers as the fixed suffix parameter.
        var collecting = Assert.IsType<Algorithm.User>(
            Assert.Single(SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot("F(a, *b c) = a").Properties).Value);
        Assert.Equal(
            [("a", ParameterKind.Normal), ("b", ParameterKind.Collecting), ("c", ParameterKind.Normal)],
            collecting.Parameters.Select(static p => (p.Name, p.Kind)));
    }

    [Theory]
    [InlineData("F(a, b) = a + b\nF(1, 2)", "3")]
    [InlineData("F(\n    a,\n    b\n) = a + b\nF(1, 2)", "3")]
    [InlineData("F(a,\n  b) = a + b\nF(1, 2)", "3")]
    [InlineData("F(\n    a\n    , b\n) = a + b\nF(1, 2)", "3")]
    [InlineData("F( a , b ) = a + b\nF(1, 2)", "3")]
    [InlineData("F((a, b)) = a * b\nF((3, 4))", "12")]
    [InlineData("F(a, *b, c) = b\nF(1, 2, 3, 4)", "[2, 3]")]
    [InlineData("F(1, -2) = 'pair'\nF(x, y) = x + y\nF(1, -2)", "pair")]
    [InlineData("F(0) = 1\nF(x) = x\nF(0)", "1")]
    [InlineData("F(\r\n a, # first\r\n b # last\r\n) = a + b\r\nF(1, 2)", "3")]
    [InlineData("F((a, (*b, c))) = b\nF((1, (2, 3, 4)))", "[2, 3]")]
    [InlineData("F(a, b) = a~ + b\nF(1, 2)", "3")]
    public void ParameterPatternLists_WithCommas_StayValid(string source, string expected)
        => AssertValid(source, expected);

    [Theory]
    // A malformed atom that diagnosed the token after it owns that boundary.
    [InlineData("F(-x) = 1\nF(1)", "UnexpectedToken")]
    [InlineData("F(a, ] b) = a\nF(1, 2)", "UnexpectedToken")]
    // A star nothing can follow is the atom's own spread-marker diagnostic.
    [InlineData("F(a *) = a\nF(1)", "InvalidCollectMarker")]
    // A star an operand follows is a next collecting binding missing its comma;
    // the marker grammar then reports the detached or nameless marker itself.
    [InlineData("F(a * b) = a\nF(1, 2)", "UnseparatedSameLineItem;InvalidCollectMarker")]
    [InlineData("F(a *2) = a\nF(1, 2)", "UnseparatedSameLineItem;InvalidCollectMarker")]
    [InlineData("F(a, *b *c) = a\nF(1, 2, 3)", "UnseparatedSameLineItem;InvalidCollectingBinding")]
    // Grace in a clause head is rejected on its own; a missing comma beside it
    // is a separate defect, reported at the item it belongs to.
    [InlineData("F(a ~b) = a\nF(1, 2)", "InvalidGraceMarker;UnseparatedSameLineItem")]
    [InlineData("F(1 ~b) = 1\nF(1, 2)", "UnseparatedSameLineItem;InvalidGraceMarker")]
    public void ParameterPatternRecovery_ReportsEachDefectOnce(string source, string expectedCodes)
    {
        var syntax = Parser.ParseSyntax(source);
        Assert.Equal(
            expectedCodes.Split(';').Select(Enum.Parse<DiagnosticCode>),
            syntax.Diagnostics.Select(static d => d.Code));
    }

    [Theory]
    [InlineData("F(-x) = 1", 4)]
    [InlineData("F((-x)) = 1", 5)]
    public void MalformedNegativePattern_BlamesTheNameOnceInsideItsHead(string source, int column)
    {
        var parse = SourceProvenance.ParseAllowingDiagnostics(source);
        var diagnostic = Assert.Single(parse.Diagnostics);
        Assert.Equal(DiagnosticCode.UnexpectedToken, diagnostic.Code);
        Assert.Equal("Expected number after '-' in pattern.", diagnostic.Message);
        Assert.Equal(new SourceSpan(1, column, 1, column), diagnostic.Span);
        Assert.Equal("F", Assert.Single(parse.Root.Properties).Name);
        Assert.Empty(parse.Root.Output);
        Assert.Empty(parse.Root.Parameters);
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        Assert.Equal(KatLangErrorCode.UnexpectedToken, Assert.Single(failure.Errors).Code);
    }

    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    public void PatternStarOperandLookahead_CrossesCommentsAndNewlines(string newline)
    {
        var source = $"F(a * # marker{newline}b) = a";
        var parse = SourceProvenance.ParseAllowingDiagnostics(source);
        Assert.Collection(parse.Diagnostics,
            separator =>
            {
                Assert.Equal(DiagnosticCode.UnseparatedSameLineItem, separator.Code);
                Assert.Equal(PatternMessage, separator.Message);
                Assert.Equal(new SourceSpan(1, 5, 1, 5), separator.Span);
            },
            marker =>
            {
                Assert.Equal(DiagnosticCode.InvalidCollectMarker, marker.Code);
                Assert.Equal("The collect marker `*` must be directly attached to its binding name: write `*b`.", marker.Message);
                Assert.Equal(new SourceSpan(1, 5, 2, 1), marker.Span);
            });
        var f = Assert.IsType<Algorithm.User>(Assert.Single(parse.Root.Properties).Value);
        Assert.Equal([("a", ParameterKind.Normal), ("b", ParameterKind.Normal)],
            f.Parameters.Select(static p => (p.Name, p.Kind)));
        Assert.Empty(parse.Root.Output);
        Assert.Empty(parse.Root.Parameters);
    }

    [Theory]
    [InlineData("F(a b) =", 5)]
    [InlineData("F((a b)) =", 6)]
    public void RecoveredPatternHead_WithMissingBodyAtEof_KeepsItsDeclaration(string source, int column)
    {
        var parse = SourceProvenance.ParseAllowingDiagnostics(source);
        Assert.Collection(parse.Diagnostics,
            separator =>
            {
                Assert.Equal(DiagnosticCode.UnseparatedSameLineItem, separator.Code);
                Assert.Equal(PatternMessage, separator.Message);
                Assert.Equal(new SourceSpan(1, column, 1, column), separator.Span);
            },
            eof =>
            {
                Assert.Equal(DiagnosticCode.UnexpectedToken, eof.Code);
                Assert.Equal("Unexpected end of input.", eof.Message);
                Assert.Equal(new SourceSpan(1, source.Length + 1, 1, source.Length + 1), eof.Span);
            });
        Assert.Equal("F", Assert.Single(parse.Root.Properties).Name);
        Assert.Empty(parse.Root.Output);
        Assert.Empty(parse.Root.Parameters);
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
    }

    [Theory]
    [InlineData("F(a b")]
    [InlineData("F((a b)")]
    public void UnclosedHeadAtEof_RemainsAnInvalidCallWithoutDeclarationLookahead(string source)
    {
        // Without the closing head and '=', lookahead cannot identify a
        // declaration. Keep expression recovery and reject the incomplete call.
        var syntax = Parser.ParseSyntax(source);
        Assert.Empty(syntax.Root.Properties);
        Assert.Contains(syntax.Diagnostics, d => d.Message == Message);
        Assert.Contains(syntax.Diagnostics, d => d.Code == DiagnosticCode.UnexpectedToken
            && d.Message == "Expected ')' but found end of input.");
        Assert.DoesNotContain(syntax.Diagnostics, d => d.Message == PatternMessage);
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
    }

    [Theory]
    [InlineData("F(1*) = 1\nF(1)", 1, 4, "'*'")]
    [InlineData("F(1 *) = 1\nF(1)", 1, 5, "'*'")]
    [InlineData("F(\n    a\n    b\n) = a + b\nF(1, 2)", 3, 5, "a name")]
    [InlineData("F(a # comment\nb) = a", 2, 1, "a name")]
    [InlineData("F(a # comment\r\nb) = a", 2, 1, "a name")]
    [InlineData("F(a\n*b) = a", 2, 1, "'*'")]
    public void PatternListWithoutANextSameLinePattern_KeepsTheClosingDelimiterDiagnostic(
        string source, int line, int column, string found)
    {
        // A star that no operand can follow is never a next pattern, and a
        // parameter list has no newline separator: both reach the ordinary
        // closing-delimiter check unchanged, and the separator rule stays silent.
        var syntax = Parser.ParseSyntax(source);
        var first = syntax.Diagnostics[0];
        Assert.Equal(DiagnosticCode.UnexpectedToken, first.Code);
        Assert.Equal($"Expected ')' but found {found}.", first.Message);
        Assert.Equal((line, column), (first.Span.StartLineNumber, first.Span.StartColumn));
        Assert.DoesNotContain(syntax.Diagnostics, static d => d.Code == DiagnosticCode.UnseparatedSameLineItem);
    }

    /// <summary>
    /// The pattern-atom starter set behind the boundary decision, pinned for
    /// EVERY token kind: after the literal pattern <c>1</c>, a same-line sample
    /// of a starter kind is the pattern-list report at the sample (and the
    /// first diagnostic); every other kind never produces that report — it
    /// reaches the closing-delimiter check, or never forms a clause head at
    /// all. A new token kind must be classified here deliberately.
    /// </summary>
    [Fact]
    public void PatternAtomStarters_ArePinnedForEveryTokenKind()
    {
        var samples = new Dictionary<TokenKind, (string Sample, bool StartsPattern)>
        {
            [TokenKind.Number] = ("2", true),
            [TokenKind.StringLiteral] = ("'s'", true),
            [TokenKind.Identifier] = ("y", true),
            [TokenKind.Minus] = ("-2", true),
            [TokenKind.Tilde] = ("~y", true),
            [TokenKind.LParen] = ("(y)", true),
            [TokenKind.Star] = ("*y", true),
            [TokenKind.Plus] = ("+", false),
            [TokenKind.Slash] = ("/", false),
            [TokenKind.Caret] = ("^", false),
            [TokenKind.LessThan] = ("<", false),
            [TokenKind.GreaterThan] = (">", false),
            [TokenKind.LessEqual] = ("<=", false),
            [TokenKind.GreaterEqual] = (">=", false),
            [TokenKind.EqualEqual] = ("==", false),
            [TokenKind.BangEqual] = ("!=", false),
            [TokenKind.KeywordDiv] = ("div", false),
            [TokenKind.KeywordMod] = ("mod", false),
            [TokenKind.KeywordAnd] = ("and", false),
            [TokenKind.KeywordOr] = ("or", false),
            [TokenKind.KeywordXor] = ("xor", false),
            [TokenKind.KeywordNot] = ("not", false),
            [TokenKind.KeywordPublic] = ("public", false),
            [TokenKind.KeywordOpen] = ("open", false),
            [TokenKind.RParen] = (")", false),
            [TokenKind.LBrace] = ("{", false),
            [TokenKind.RBrace] = ("}", false),
            [TokenKind.LBracket] = ("[", false),
            [TokenKind.RBracket] = ("]", false),
            [TokenKind.Comma] = (",", false),
            [TokenKind.Semicolon] = (";", false),
            [TokenKind.Equals] = ("=", false),
            [TokenKind.Colon] = (":", false),
            [TokenKind.Dot] = (".", false),
            [TokenKind.Comment] = ("# note", false),
            [TokenKind.Bad] = ("@", false),
            [TokenKind.EndOfFile] = ("", false),
        };
        Assert.Equal(Enum.GetValues<TokenKind>().Order(), samples.Keys.Order());

        // Exercise the actual atom dispatch independently of declaration
        // lookahead and the separator predicate. Otherwise a missing starter
        // (or a sample that never forms a head) can pass vacuously. This pins
        // BOTH directions: an atom arm missing from the classifier, and a
        // classified starter missing its atom arm. No public test seam needed.
        const System.Reflection.BindingFlags instanceFlags =
            System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Instance;
        var constructor = Assert.Single(typeof(Parser).GetConstructors(instanceFlags));
        var parseAtom = typeof(Parser).GetMethod("ParsePatternAtomCore", instanceFlags)!;
        var classify = typeof(Parser).GetMethod("CanStartPatternAtom",
            System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Static)!;

        foreach (var (kind, (sample, startsPattern)) in samples)
        {
            var sampleTokens = Lexer.Tokenize(sample).Tokens;
            Assert.Equal(kind, sampleTokens[0].Kind);
            Assert.Equal(startsPattern, Assert.IsType<bool>(classify.Invoke(null, [kind])));
            var atomDiagnostics = new List<Diagnostic>();
            var parser = constructor.Invoke([sampleTokens, atomDiagnostics, null]);
            Assert.IsAssignableFrom<Pattern>(parseAtom.Invoke(parser, null));
            // Comments are transparent to Current, so a comment-only stream
            // reaches the ordinary EOF recovery arm.
            var currentKind = kind == TokenKind.Comment ? TokenKind.EndOfFile : kind;
            Assert.Equal(!startsPattern, atomDiagnostics.Any(d => d.Message ==
                $"Unexpected {Parser.DescribeTokenKind(currentKind, includeArticle: false)} in a pattern."));

            var source = kind == TokenKind.EndOfFile ? "F(1 " : $"F(1 {sample}) = 1";
            var syntax = Parser.ParseSyntax(source);
            var reports = syntax.Diagnostics.Where(static d => d.Message == PatternMessage).ToList();
            if (!startsPattern)
            {
                Assert.True(reports.Count == 0, $"{kind}: a non-starter must never be a next pattern.");
                continue;
            }

            var report = Assert.Single(reports);
            Assert.Equal(DiagnosticCode.UnseparatedSameLineItem, report.Code);
            Assert.Equal((1, 5), (report.Span.StartLineNumber, report.Span.StartColumn));
            Assert.Equal(report, syntax.Diagnostics[0]);
        }
    }

    // ── The semicolon diagnostic no longer recommends adjacency ────────────

    [Fact]
    public void SemicolonDiagnostic_RecommendsCommaOrNewLine_NeverAdjacency()
    {
        var diagnostic = Assert.Single(Parser.ParseSyntax("1 ; 2").Diagnostics);
        Assert.Equal(DiagnosticCode.UnsupportedSemicolon, diagnostic.Code);
        Assert.Equal(
            "Semicolon is not supported as an expression separator. Use ',' between expressions on one line (a new line separates them where the context allows it), or parentheses for one sequence value.",
            diagnostic.Message);
        Assert.DoesNotContain("adjacen", diagnostic.Message, StringComparison.OrdinalIgnoreCase);
    }

    // ── The public facade carries the family end to end ────────────────────

    [Fact]
    public void PublicErrorCode_MapsTheFamily_ThroughTheEngineAndTheDirectMapping()
    {
        Assert.Equal(KatLangErrorCode.UnseparatedSameLineItem, KatLangError.MapDiagnosticCode(DiagnosticCode.UnseparatedSameLineItem));
        Assert.Equal(41, (int)DiagnosticCode.UnseparatedSameLineItem);
        Assert.Equal(64, (int)KatLangErrorCode.UnseparatedSameLineItem);

        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("1 2"));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.UnseparatedSameLineItem, error.Code);
        Assert.Equal(Message, error.Message);
    }
}
