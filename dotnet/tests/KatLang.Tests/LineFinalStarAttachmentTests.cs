using System.Globalization;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Issue #183 (owner decision 2026-10-14, refining Q-65): ATTACHMENT CLASSIFIES A LINE-FINAL STAR.
/// The independent acceptance matrix of the law, written against observable syntax only — the
/// elaborated tree, the diagnostics, the value and the emitted output rows.
///
/// <para>The canonical newline rule: <i>Newlines separate complete expressions by default. An
/// incomplete expression continues when valid syntax permits it, without consuming a new
/// declaration. Otherwise, an independent expression or declaration begins a new construct.
/// Syntax that cannot stand alone but can legally continue the preceding expression attaches
/// backward. All decisions are syntactic, never based on evaluated values.</i></para>
///
/// <para>The star rule is one syntactic classification that feeds it: when <c>*</c> follows a
/// completed expression and is the final significant token of its physical line (EOF included,
/// across comments and blank lines), an ATTACHED <c>expr*</c> is the postfix spread marker and
/// completes the expression, while a DETACHED <c>expr *</c> is multiplication and leaves it
/// incomplete. A star with a same-line operand multiplies whatever the spacing, and explicitly
/// closed spreads (<c>F(A*)</c>, <c>[A*]</c>, <c>A*, B</c>, <c>A*.F</c>) are unchanged.</para>
///
/// <para>The exhaustive context × layout cross product, modules and deferred branches live in
/// <see cref="LineFinalStarLawTests"/>; this suite is the compact statement of the decision.</para>
/// </summary>
public class LineFinalStarAttachmentTests
{
    // ── Rendering ────────────────────────────────────────────────────────────

    /// <summary>A span-free, precedence-revealing spelling: two different trees never share one.</summary>
    private static string Shape(Expr expr) => expr switch
    {
        Expr.Binary(var op, var left, var right) => $"{ExprNameRenderer.BinaryOpText(op)}({Shape(left)}, {Shape(right)})",
        Expr.Comparison chain => "cmp(" + Shape(chain.First)
            + string.Concat(chain.Links.Select(link => $" {ExprNameRenderer.ComparisonOpText(link.Op)} {Shape(link.Operand)}")) + ")",
        Expr.Unary(UnaryOp.Not, var operand) => $"not({Shape(operand)})",
        Expr.Unary(_, var operand) => $"neg({Shape(operand)})",
        Expr.SequenceSpread(var operand) => $"spread({Shape(operand)})",
        Expr.Capture(var body) => $"capture({Join(body)})",
        Expr.ListLiteral(var items) => $"list({Join(items)})",
        Expr.Index(var target, var selectors) => $"index({Shape(target)}, {Join(selectors)})",
        Expr.Call(var function, var args) => $"call({Shape(function)}; {Join(args)})",
        Expr.DotCall dot => dot.Args is { } args
            ? $"dot({Shape(dot.Target)}.{dot.Name}; {Join(args)})"
            : $"dot({Shape(dot.Target)}.{dot.Name})",
        Expr.AlgorithmExpr(var algorithm) => $"block({Rows(algorithm)})",
        Expr.Resolve(var name) => name,
        Expr.Param(var name) => "$" + name,
        Expr.Num(var value) => value.ToString(CultureInfo.InvariantCulture),
        Expr.BoolLiteral(var value) => value ? "true" : "false",
        _ => $"<{expr.GetType().Name}>",
    };

    private static string Join(IEnumerable<Expr> items) => string.Join(", ", items.Select(Shape));

    private static string Rows(Algorithm algorithm)
        => string.Join(" | ", Assert.IsType<Algorithm.User>(algorithm).Output.Select(Shape));

    private static Algorithm Body(Algorithm owner, string name)
        => Assert.Single(owner.Properties, p => p.Name == name).Value;

    /// <summary>Valid source: no diagnostic of ANY severity, from the raw parse and the elaboration.</summary>
    private static SourceProvenance ParseClean(string source)
    {
        var parsed = SourceProvenance.ParseValid(source);
        Assert.True(parsed.Diagnostics.Count == 0,
            $"expected no diagnostic, got: {string.Join(" | ", parsed.Diagnostics.Select(d => $"{d.Severity} {d.Code}: {d.Message}"))}\nsource:\n{source}");
        Assert.Empty(Parser.ParseSyntax(source).Diagnostics.ToArray());
        return parsed;
    }

    private static async Task<string> ValueOnEveryRoute(string source)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation.Kind == "ok", $"expected success, got {observation}\nsource:\n{source}");
        return observation.Value!;
    }

    /// <summary>The emitted output rows a host presents (RunResult.Success.OutputRows), neutrally rendered.</summary>
    private static string[] OutputRows(string source)
    {
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        return [.. success.OutputRows.Select(SixRouteAgreement.Neutral)];
    }

    private static Diagnostic SingleError(string source)
    {
        var parsed = Parser.ParseSyntax(source);
        Assert.True(parsed.HasErrors, $"expected a front-end error\nsource:\n{source}");
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        return Assert.Single(parsed.Diagnostics);
    }

    // ── The primary acceptance examples ──────────────────────────────────────

    [Fact]
    public async Task StandaloneAttachedSpread_AtTheEndOfTheProgram_ContributesThreeOutputRows()
    {
        const string source = "A = 1, 2, 3\nA*";
        var parsed = ParseClean(source);
        Assert.Equal("spread(A)", Rows(parsed.Root));
        Assert.Equal(["1", "2", "3"], OutputRows(source));
        Assert.Equal("S[1, 2, 3]", await ValueOnEveryRoute(source));
    }

    [Fact]
    public async Task AppendingAnIndependentRow_NeverReinterpretsTheCompletedSpread()
    {
        const string source = "A = 1, 2, 3\nA*\n42";
        var parsed = ParseClean(source);
        Assert.Equal("spread(A) | 42", Rows(parsed.Root));
        Assert.Equal(["1", "2", "3", "42"], OutputRows(source));
        Assert.Equal("S[1, 2, 3, 42]", await ValueOnEveryRoute(source));
    }

    [Fact]
    public async Task DetachedLineFinalStar_IsIncompleteMultiplication_AndTheNextLineIsItsOperand()
    {
        const string source = "A = 2\nB = 3\n\nA *\nB";
        var parsed = ParseClean(source);
        Assert.Equal("*(A, B)", Rows(parsed.Root));
        Assert.Equal(["6"], OutputRows(source));
        Assert.Equal("6", await ValueOnEveryRoute(source));
    }

    // ── The behavior matrix of the decision ──────────────────────────────────

    public static TheoryData<string, string, string, string> ValidMatrix() => new()
    {
        // id, source, root rows, value
        { "A* at EOF", "A = 1, 2, 3\nA*", "spread(A)", "S[1, 2, 3]" },
        { "A* newline B", "A = 1, 2, 3\nB = 4\nA*\nB", "spread(A) | B", "S[1, 2, 3, 4]" },
        { "A * newline B", "A = 2\nB = 3\nA *\nB", "*(A, B)", "6" },
        { "A* newline B = 5", "A = 1, 2, 3\nA*\nB = 5\nB", "spread(A) | B", "S[1, 2, 3, 5]" },
        { "A* newline -2", "A = 1, 2, 3\nA*\n-2", "spread(A) | neg(2)", "S[1, 2, 3, -2]" },
        { "A * newline -2", "A = 2\nA *\n-2", "*(A, neg(2))", "-4" },
        { "A** at EOF", "A = 1, 2, 3\nA**", "spread(spread(A))", "S[1, 2, 3]" },
        { "A*** at EOF", "A = 1, 2, 3\nA***", "spread(spread(spread(A)))", "S[1, 2, 3]" },
        { "A** newline B", "A = 1, 2, 3\nB = 4\nA**\nB", "spread(spread(A)) | B", "S[1, 2, 3, 4]" },
        { "A*B", "A = 2\nB = 3\nA*B", "*(A, B)", "6" },
        { "A* B", "A = 2\nB = 3\nA* B", "*(A, B)", "6" },
        { "A *B", "A = 2\nB = 3\nA *B", "*(A, B)", "6" },
        { "A * B", "A = 2\nB = 3\nA * B", "*(A, B)", "6" },
        { "A newline * B", "A = 2\nB = 3\nA\n* B", "*(A, B)", "6" },
        { "F(A*)", "F(*xs) = xs\nA = 1, 2, 3\nF(A*)", "call(F; spread(A))", "L[1, 2, 3]" },
        { "[A*]", "A = 1, 2, 3\n[A*]", "list(spread(A))", "L[1, 2, 3]" },
        { "A*, B", "A = 1, 2, 3\nB = 4\nA*, B", "spread(A) | B", "S[1, 2, 3, 4]" },
        { "A*.F", "F(*xs) = xs.count\nA = 1, 2, 3\nA*.F", "call(F; spread(A))", "3" },
        // The scalar case is an intentional consequence: spreading a scalar supplies that scalar.
        { "7* at EOF", "7*", "spread(7)", "7" },
    };

    [Theory]
    [MemberData(nameof(ValidMatrix))]
    public async Task Matrix_ValidLayouts_HaveTheirSyntacticMeaning(string id, string source, string rows, string value)
    {
        _ = id;
        var parsed = ParseClean(source);
        Assert.Equal(rows, Rows(parsed.Root));
        Assert.Equal(value, await ValueOnEveryRoute(source));
    }

    [Fact]
    public void Matrix_DetachedStarAtEof_IsAMissingMultiplicationOperand()
    {
        var error = SingleError("A = 2\nA *");
        Assert.Equal(DiagnosticCode.UnexpectedToken, error.Code);
        Assert.Equal(new SourceSpan(2, 3, 2, 4), error.Span);
        Assert.Contains("Expected an expression after '*'", error.Message, StringComparison.Ordinal);
        Assert.Contains("separated from its left operand", error.Message, StringComparison.Ordinal);
        Assert.Contains("`A*`", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Matrix_DetachedStarBeforeADeclaration_IsAMissingOperand_AndTheDeclarationSurvives()
    {
        const string source = "A = 2\nA *\nB = 5\nB";
        var error = SingleError(source);
        Assert.Equal(DiagnosticCode.UnexpectedToken, error.Code);
        Assert.Equal(new SourceSpan(2, 3, 2, 4), error.Span);
        Assert.Contains("declaration", error.Message, StringComparison.Ordinal);

        // Recovery keeps the declaration a declaration and the row `B` a row of its own; the
        // recovered tree is never mistaken for a successful program.
        var recovered = SourceProvenance.ParseAllowingDiagnostics(source).Root;
        Assert.Equal(["A", "B"], recovered.Properties.Select(p => p.Name));
        var rows = recovered.Output;
        Assert.Equal(2, rows.Count);
        var product = Assert.IsType<Expr.Binary>(rows[0]);
        Assert.Equal(BinaryOp.Mul, product.Op);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(product.Left).Name);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(rows[1]).Name);
    }

    [Fact]
    public void Matrix_DetachedSpreadMarkerWithSameLineCloser_StaysTheInvalidMarker()
    {
        var error = SingleError("F(*xs) = xs\nA = 1, 2, 3\nF(A *)");
        Assert.Equal(DiagnosticCode.InvalidSpreadMarker, error.Code);
        Assert.Equal(new SourceSpan(3, 3, 3, 6), error.Span);
    }

    // ── Comments, whitespace and physical lines ──────────────────────────────

    public static TheoryData<string> AttachedLayouts() => new()
    {
        "A*\nB",
        "A*\r\nB",
        "A*   \nB",
        "A*\t\nB",
        "A*\n\tB",
        "A*\n        B",
        "A* # comment\nB",
        "A*\t# comment\r\nB",
        "A*\n\n\nB",
        "A*\n# comment\nB",
        "A*\n# comment\n\nB",
        "A*\r\n\r\n# note\r\n\tB",
    };

    [Theory]
    [MemberData(nameof(AttachedLayouts))]
    public async Task AttachedLineFinalStar_IsASpreadRow_WhateverCommentsOrBlankLinesFollow(string layout)
    {
        var source = "A = 1, 2, 3\nB = 4\n" + layout;
        var parsed = ParseClean(source);
        Assert.Equal("spread(A) | B", Rows(parsed.Root));
        var reference = ParseClean("A = 1, 2, 3\nB = 4\nA*\nB");
        Assert.Equal(LeanAstEncoder.EncodeProgram(reference.Root), LeanAstEncoder.EncodeProgram(parsed.Root));
        Assert.Equal("S[1, 2, 3, 4]", await ValueOnEveryRoute(source));
    }

    public static TheoryData<string> DetachedLayouts() => new()
    {
        "A *\nB",
        "A *\r\nB",
        "A\t*\nB",
        "A  *  \nB",
        "A *\n\tB",
        "A * # comment\nB",
        "A *\t# comment\r\nB",
        "A *\n\n\nB",
        "A *\n# comment\nB",
        "A *\n# comment\n\nB",
        "A *\r\n\r\n# note\r\n\tB",
        // A leading star is detached from its left operand by the newline itself.
        "A\n* B",
        "A\n*B",
        "A\n*\nB",
    };

    [Theory]
    [MemberData(nameof(DetachedLayouts))]
    public async Task DetachedLineFinalStar_IsMultiplication_WhateverCommentsOrBlankLinesFollow(string layout)
    {
        var source = "A = 2\nB = 3\n" + layout;
        var parsed = ParseClean(source);
        Assert.Equal("*(A, B)", Rows(parsed.Root));
        var reference = ParseClean("A = 2\nB = 3\nA * B");
        Assert.Equal(LeanAstEncoder.EncodeProgram(reference.Root), LeanAstEncoder.EncodeProgram(parsed.Root));
        Assert.Equal("6", await ValueOnEveryRoute(source));
    }

    [Theory]
    [InlineData("A = 1, 2, 3\nA*\n")]
    [InlineData("A = 1, 2, 3\nA*\r\n")]
    [InlineData("A = 1, 2, 3\nA* # the end")]
    [InlineData("A = 1, 2, 3\nA* # the end\n\n# nothing follows\n")]
    [InlineData("A = 1, 2, 3\r\nA*\r\n\r\n")]
    public async Task AttachedStar_AtTheEndOfInput_WithOrWithoutAFinalNewline_IsASpread(string source)
    {
        var parsed = ParseClean(source);
        Assert.Equal("spread(A)", Rows(parsed.Root));
        Assert.Equal("S[1, 2, 3]", await ValueOnEveryRoute(source));
    }

    [Theory]
    [InlineData("A = 2\nA *\n")]
    [InlineData("A = 2\nA *\r\n")]
    [InlineData("A = 2\nA * # the end")]
    [InlineData("A = 2\nA * # the end\n\n# nothing follows\n")]
    public void DetachedStar_AtTheEndOfInput_WithOrWithoutAFinalNewline_IsAMissingOperand(string source)
    {
        var error = SingleError(source);
        Assert.Equal(DiagnosticCode.UnexpectedToken, error.Code);
        Assert.Equal(new SourceSpan(2, 3, 2, 4), error.Span);
    }

    [Fact]
    public void LoneCarriageReturn_IsWhitespace_SoTheStarHasASameLineOperand()
    {
        // The established lexical contract: LF alone breaks a physical line; CR is whitespace.
        var parsed = ParseClean("A = 2\nB = 3\nA*\rB");
        Assert.Equal("*(A, B)", Rows(parsed.Root));
    }

    [Fact]
    public void AReportedCharacterBeforeTheStar_NeverManufacturesAttachment()
    {
        // `A@*`: the star is not adjacent to `A` (the reported '@' stands between), so the
        // line-final star is detached multiplication with no operand. The exact source-offset
        // adjacency decides; skipped tokens are not removed before comparing positions.
        var parsed = Parser.ParseSyntax("A = 2\nA@*");
        Assert.True(parsed.HasErrors);
        Assert.DoesNotContain(parsed.Root.Output, e => e is Expr.SequenceSpread);
        Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.UnexpectedToken
            && d.Message.Contains("after '*'", StringComparison.Ordinal));
    }

    [Fact]
    public void AReportedCharacterAfterTheStar_NeverDestroysAttachment()
    {
        // `A*@`: the star is attached to `A` and the reported character after it is invisible to
        // the grammar, so the star is still the final significant token of its line — a spread.
        // The lexer's report is the only diagnostic.
        var parsed = Parser.ParseSyntax("A = 1, 2, 3\nA*@\n42");
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.NotEqual(DiagnosticCode.UnexpectedToken, diagnostic.Code);
        Assert.Equal("spread(A) | 42", Rows(parsed.Root));
    }

    [Theory]
    [InlineData("X = @*\nX")]
    [InlineData("@*")]
    [InlineData("F(*xs) = xs\nF(@*)")]
    [InlineData("X = (@*)\nX")]
    public void AReportedCharacterStandingInAsTheOperand_IsWhatTheStarAttachesTo(string source)
    {
        // A reported character the grammar needs as the operand IS that operand (#9 parser
        // recovery), so a star directly after it is attached by exact offsets: the line-final
        // star is a spread and the lexer's report stays the only diagnostic — wherever the line
        // stands, and with a same-line closer too.
        var parsed = Parser.ParseSyntax(source);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.UnexpectedCharacter, diagnostic.Code);
        var spreads = new List<Expr.SequenceSpread>();
        new SpreadCollector(spreads).VisitAlgorithm(parsed.Root);
        Assert.Single(spreads);
    }

    private sealed class SpreadCollector(List<Expr.SequenceSpread> spreads) : AstWalker
    {
        public override void VisitExpr(Expr expr)
        {
            if (expr is Expr.SequenceSpread spread)
                spreads.Add(spread);
            base.VisitExpr(expr);
        }
    }

    // ── Every expression-list context ────────────────────────────────────────

    /// <summary>
    /// Each context with an ATTACHED line-final spread followed by an independent item, and the
    /// same context with a DETACHED line-final star. Expected cardinalities are independent of
    /// each other: the spread supplies three items, the product one.
    /// </summary>
    public static TheoryData<string, string, string, string> Contexts() => new()
    {
        // id, source, observed structure, value
        { "root rows / spread", "A = 1, 2, 3\nB = 4\nA*\nB",
            "rows: spread(A) | B", "S[1, 2, 3, 4]" },
        { "root rows / product", "A = 2\nB = 3\nA *\nB",
            "rows: *(A, B)", "6" },
        { "simple property / spread", "A = 1, 2, 3\nX = A*\nX\n42",
            "X: spread(A); rows: X | 42", "S[S[1, 2, 3], 42]" },
        { "simple property / product", "A = 2\nB = 3\nX = A *\nB\nX",
            "X: *(A, B); rows: X", "6" },
        { "brace body / spread", "A = 1, 2, 3\nB = 4\n{\n  A*\n  B\n}",
            "rows: block(spread(A) | B)", "S[1, 2, 3, 4]" },
        { "brace body / product", "A = 2\nB = 3\n{\n  A *\n  B\n}",
            "rows: block(*(A, B))", "6" },
        { "parenthesized capture / spread", "A = 1, 2, 3\nB = 4\ncount((\n  A*\n  B\n))",
            "rows: call(count; capture(spread(A), B))", "4" },
        { "parenthesized group / product", "A = 2\nB = 3\n1 + (\n  A *\n  B\n)",
            "rows: +(1, *(A, B))", "7" },
        { "call arguments / spread", "F(*xs) = xs\nA = 1, 2, 3\nB = 4\nF(\n  A*\n  B\n)",
            "rows: call(F; spread(A), B)", "L[1, 2, 3, 4]" },
        { "call arguments / product", "F(*xs) = xs\nA = 2\nB = 3\nF(\n  A *\n  B\n)",
            "rows: call(F; *(A, B))", "L[6]" },
        { "list literal / spread", "A = 1, 2, 3\nB = 4\n[\n  A*\n  B\n]",
            "rows: list(spread(A), B)", "L[1, 2, 3, 4]" },
        { "list literal / product", "A = 2\nB = 3\n[\n  A *\n  B\n]",
            "rows: list(*(A, B))", "L[6]" },
        { "selector list / spread", "L = [10, 20, 30, 40, 50]\nA = 1, 2, 3\nB = 4\nL[\n  A*\n  B\n]",
            "rows: index(L, spread(A), B)", "S[20, 30, 40, 50]" },
        { "selector list / product", "L = [10, 20, 30, 40, 50, 60, 70]\nA = 2\nB = 3\nL[\n  A *\n  B\n]",
            "rows: index(L, *(A, B))", "70" },
        { "nested block in an argument / spread", "F(*xs) = xs\nA = 1, 2, 3\nB = 4\nF({\n  A*\n  B\n})",
            "rows: call(F; block(spread(A) | B))", "L[S[1, 2, 3, 4]]" },
        { "nested expression / product", "A = 2\nB = 3\n(A *\n  B) + 1",
            "rows: +(*(A, B), 1)", "7" },
    };

    [Theory]
    [MemberData(nameof(Contexts))]
    public async Task EveryExpressionListContext_ClassifiesTheLineFinalStarAlike(string id, string source, string structure, string value)
    {
        _ = id;
        var parsed = ParseClean(source);
        var observed = parsed.Root.Properties.Any(p => p.Name == "X")
            ? $"X: {Rows(Body(parsed.Root, "X"))}; rows: {Rows(parsed.Root)}"
            : $"rows: {Rows(parsed.Root)}";
        Assert.Equal(structure, observed);
        Assert.Equal(value, await ValueOnEveryRoute(source));
    }

    [Theory]
    [InlineData("A = 1, 2, 3\n(A*\n)", "capture(spread(A))", "S[1, 2, 3]")]
    [InlineData("A = 1, 2, 3\n[A*\n]", "list(spread(A))", "L[1, 2, 3]")]
    [InlineData("A = 1, 2, 3\n{ A*\n}", "block(spread(A))", "S[1, 2, 3]")]
    [InlineData("F(*xs) = xs\nA = 1, 2, 3\nF(A*\n)", "call(F; spread(A))", "L[1, 2, 3]")]
    [InlineData("L = [10, 20, 30, 40]\nA = 1, 2, 3\nL[A*\n]", "index(L, spread(A))", "S[20, 30, 40]")]
    public async Task ALaterLineCloser_StaysOwnedByItsConstruct_AfterAnAttachedLineFinalSpread(string source, string row, string value)
    {
        var parsed = ParseClean(source);
        Assert.Equal(row, Rows(parsed.Root));
        Assert.Equal(value, await ValueOnEveryRoute(source));
    }

    [Theory]
    [InlineData("A = 2\n(A *\n)")]
    [InlineData("A = 2\n[A *\n]")]
    [InlineData("A = 2\n{ A *\n}")]
    [InlineData("F(x) = x\nA = 2\nF(A *\n)")]
    public void ALaterLineCloser_AfterADetachedLineFinalStar_IsAMissingOperand_AndClosesItsConstruct(string source)
    {
        var error = SingleError(source);
        Assert.Equal(DiagnosticCode.UnexpectedToken, error.Code);
        Assert.Contains("after '*'", error.Message, StringComparison.Ordinal);
    }

    // ── Declarations and scopes ──────────────────────────────────────────────

    public static TheoryData<string, string> FollowingDeclarations() => new()
    {
        // head written on the next line, the row that reads it
        { "Next = 5", "Next" },
        { "public Next = 5", "Next" },
        { "Next(x) = x + 5", "Next(0)" },
        { "x, y = 5, 6", "x" },
        { "*items = 5, 6", "items[0]" },
        { "~Next = 5", "Next" },
    };

    [Theory]
    [MemberData(nameof(FollowingDeclarations))]
    public void AttachedSpread_BeforeADeclaration_CompletesTheRow_AndTheDeclarationStaysADeclaration(string head, string read)
    {
        var source = $"A = 1, 2, 3\nA*\n{head}\n{read}";
        var parsed = Parser.ParseSyntax(source);
        Assert.Equal("spread(A)", Shape(parsed.Root.Output[0]));
        Assert.DoesNotContain(parsed.Diagnostics, d => d.Code == DiagnosticCode.UnexpectedToken);
        Assert.DoesNotContain(parsed.Root.Output, e => e is Expr.Binary);
    }

    [Theory]
    [MemberData(nameof(FollowingDeclarations))]
    public void DetachedStar_BeforeADeclaration_IsTheOneMissingOperand_AndTheDeclarationIsNeverAnOperand(string head, string read)
    {
        _ = read;
        var source = $"A = 2\nA *\n{head}\nLater = 42\nLater";
        var parsed = Parser.ParseSyntax(source);
        Assert.True(parsed.HasErrors);
        var missing = Assert.Single(parsed.Diagnostics, d => d.Code == DiagnosticCode.UnexpectedToken);
        Assert.Equal(new SourceSpan(2, 3, 2, 4), missing.Span);
        var product = Assert.IsType<Expr.Binary>(parsed.Root.Output[0]);
        Assert.Equal(BinaryOp.Mul, product.Op);
        Assert.IsType<Expr.Num>(product.Right); // the recovery stand-in, never the declaration's name
        Assert.Contains(parsed.Root.Properties, p => p.Name == "Later");
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
    }

    [Fact]
    public void OpenDeclaration_AfterAnAttachedSpread_IsOnlyTheMisplacedOpen()
    {
        // `open` is a body's preamble, so after an output row it is misplaced either way. After an
        // attached spread that is the ONE diagnostic: the spread completed its row.
        var attached = Parser.ParseSyntax("A = 1, 2, 3\n{ A*\n  open Math\n  Pi }");
        var only = Assert.Single(attached.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidOpenDeclaration, only.Code);

        // After a detached star the incomplete multiplication is reported too, and `open` is never
        // read as its operand.
        var detached = Parser.ParseSyntax("A = 2\n{ A *\n  open Math\n  Pi }");
        Assert.Contains(detached.Diagnostics, d => d.Code == DiagnosticCode.UnexpectedToken
            && d.Span == new SourceSpan(2, 5, 2, 6));
        Assert.Contains(detached.Diagnostics, d => d.Code == DiagnosticCode.InvalidOpenDeclaration);
    }

    [Fact]
    public void ABraceScope_KeepsItsOwnDeclarations_AfterAnAttachedSpread()
    {
        const string source = "A = 1, 2, 3\n{ A*\n  Y = 5\n  Y }";
        var parsed = ParseClean(source);
        var block = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(parsed.Root.Output));
        Assert.Equal("spread(A) | Y", Rows(block.Algorithm));
        Assert.Equal(["Y"], block.Algorithm.Properties.Select(p => p.Name));
    }

    // ── Backward continuation after a completed spread ───────────────────────

    [Theory]
    [InlineData("F(*xs) = xs.count\nA = 1, 2, 3\nA*\n.F")]
    [InlineData("F(*xs) = xs.count\nA = 1, 2, 3\nA* # receiver\n\n.F")]
    [InlineData("F(*xs) = xs.count\nA = 1, 2, 3\nA*\r\n  .F")]
    [InlineData("F(*xs) = xs.count\nA = 1, 2, 3\nA*.F")]
    public async Task LeadingDot_ContinuesTheSpreadAsAFluentReceiver(string source)
    {
        var parsed = ParseClean(source);
        Assert.Equal("call(F; spread(A))", Rows(parsed.Root));
        Assert.Equal("3", await ValueOnEveryRoute(source));
    }

    [Theory]
    [InlineData("A = 1, 2, 3\nB = 4\nA*\n+ B")]
    [InlineData("A = 1, 2, 3\nB = 4\nA*\n- B")]
    [InlineData("A = 1, 2, 3\nB = 4\nA*\n* B")]
    [InlineData("A = 1, 2, 3\nB = 4\nA*\n^ 2")]
    [InlineData("A = 1, 2, 3\nB = 4\nA*\n== 1")]
    [InlineData("A = 1, 2, 3\nB = 4\nA*\nand true")]
    public void LeadingBinaryOperator_StillAttachesBackward_ButASpreadIsNeverAScalarOperand(string source)
    {
        var error = SingleError(source);
        Assert.Equal(DiagnosticCode.MisplacedSpread, error.Code);
        Assert.Equal(new SourceSpan(3, 1, 3, 3), error.Span); // the spread itself
    }

    [Theory]
    [InlineData("values = (1, 2)\n1 + values*", 2, 5, 2, 12)]
    [InlineData("values = (1, 2)\n2 * values*", 2, 5, 2, 12)]
    [InlineData("values = (1, 2)\n2 ^ values*", 2, 5, 2, 12)]
    [InlineData("values = (1, 2)\n-values*", 2, 2, 2, 9)]
    [InlineData("values = (true, false)\nnot values*", 2, 5, 2, 12)]
    [InlineData("A = 1, 2\nX = 2 * A*\nX", 2, 9, 2, 11)]
    [InlineData("A = 1, 2\nB = 3\nA *\nB*", 4, 1, 4, 3)]
    public void AnAttachedLineFinalSpread_IsNeverAScalarOperand(string source, int line, int column, int endLine, int endColumn)
    {
        // The completed spread may end the line as an operator's right operand or a unary
        // operand: it is still a spread, so it is the one MisplacedSpread at the spread itself —
        // never a missing multiplication operand.
        var error = SingleError(source);
        Assert.Equal(DiagnosticCode.MisplacedSpread, error.Code);
        Assert.Equal(new SourceSpan(line, column, endLine, endColumn), error.Span);
    }

    [Theory]
    [InlineData("A = 1, 2, 3\nA*\n(2)", "spread(A) | 2", "S[1, 2, 3, 2]")]
    [InlineData("A = 1, 2, 3\nA*\n[0]", "spread(A) | list(0)", "S[1, 2, 3, L[0]]")]
    [InlineData("A = 1, 2, 3\nA*\nnot true", "spread(A) | not(true)", "S[1, 2, 3, false]")]
    [InlineData("A = 1, 2, 3\nA*\n{ 9 }", "spread(A) | block(9)", "S[1, 2, 3, 9]")]
    [InlineData("A = 1, 2, 3\nA*\n'text'", "spread(A) | <StringLiteral>", "S[1, 2, 3, 'text']")]
    public async Task IndependentNextLineExpressions_StartTheirOwnRow_AfterACompletedSpread(string source, string rows, string value)
    {
        var parsed = ParseClean(source);
        Assert.Equal(rows, Rows(parsed.Root));
        Assert.Equal(value, await ValueOnEveryRoute(source));
    }

    // ── Same-line classification is unchanged ────────────────────────────────

    [Fact]
    public void SameLineBracket_AfterAStar_IsAMultiplicationOperand_NeverASelectionOfTheSpread()
    {
        Assert.Equal("*(A, list(0))", Rows(ParseClean("A = 2\nA*[0]").Root));
        Assert.Equal("spread(A) | list(0)", Rows(ParseClean("A = 2\nA*\n[0]").Root));
    }

    [Theory]
    [InlineData("A = [1, 2, 3]\nA[0]*", "spread(index(A, 0))", "1")]
    [InlineData("A = 1, 2, 3\n(A*)[0]", "index(capture(spread(A)), 0)", "1")]
    [InlineData("F(*xs) = xs\nA = 1, 2, 3\nF(A*)", "call(F; spread(A))", "L[1, 2, 3]")]
    [InlineData("F(*xs) = xs.count\nA = 1, 2, 3\nA*.F", "call(F; spread(A))", "3")]
    public async Task EstablishedSpreadSpellings_KeepTheirTrees(string source, string rows, string value)
    {
        Assert.Equal(rows, Rows(ParseClean(source).Root));
        Assert.Equal(value, await ValueOnEveryRoute(source));
    }

    [Theory]
    [InlineData("A = 1, 2, 3\nB = 4\nA**B")]
    [InlineData("A = 1, 2, 3\nB = 4\nA** B")]
    [InlineData("A = 1, 2, 3\nB = 4\nA* *\nB")]
    public void ASpreadChainFollowedByMultiplication_KeepsTheMisplacedSpreadRejection(string source)
    {
        var error = SingleError(source);
        Assert.Equal(DiagnosticCode.MisplacedSpread, error.Code);
        Assert.Equal(new SourceSpan(3, 1, 3, 3), error.Span);
    }

    [Theory]
    [InlineData("values = (1, 2)\nvalues **\n42", "values | 42")]
    [InlineData("values = (1, 2)\nvalues **", "values")]
    [InlineData("values = (1, 2)\nvalues ** # note\n\n42", "values | 42")]
    [InlineData("values = (1, 2)\nvalues **\n* 2", "*(values, 2)")]
    public void ADetachedMarkerRun_EndsAtTheAttachedLineFinalStar_WithOneDiagnostic(string source, string rows)
    {
        // `values **`: the first star has a same-line follower (the second star), so it is a
        // spread marker that fails attachment; the second, attached to the first and ending the
        // line, closes the malformed run. One InvalidSpreadMarker over `values **`, the plain
        // operand recovered, and the next line classified on its own.
        var parsed = Parser.ParseSyntax(source);
        var error = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidSpreadMarker, error.Code);
        Assert.Equal(new SourceSpan(2, 1, 2, 10), error.Span);
        Assert.Equal(rows, Rows(parsed.Root));
    }

    [Fact]
    public void AnAttachedLineFinalOpenTarget_IsASpreadTarget_WhileADetachedOneIsIncompleteMultiplication()
    {
        // Attached: the line-final star completes the spread target, which open-form validation
        // rejects exactly like the comma-closed `open A*, B`; the next line stays a declaration.
        var attached = Parser.ParseSyntax("open A*\nA = { public X = 1 }\n0");
        var badForm = Assert.Single(attached.Diagnostics);
        Assert.Equal(DiagnosticCode.BadOpenForm, badForm.Code);
        Assert.Contains("'spread'", badForm.Message, StringComparison.Ordinal);
        Assert.Equal(["A"], attached.Root.Properties.Select(p => p.Name));
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("open A*\nA = { public X = 1 }\n0"));

        // Detached: the open target is an incomplete multiplication, whose missing operand is the
        // one parser error at the star; the declaration is never its operand.
        var detached = Parser.ParseSyntax("open A *\nA = { public X = 1 }\n0");
        Assert.Contains(detached.Diagnostics, d => d.Code == DiagnosticCode.UnexpectedToken
            && d.Span == new SourceSpan(1, 8, 1, 9));
        Assert.Equal(["A"], detached.Root.Properties.Select(p => p.Name));
    }

    [Fact]
    public void ASpreadChain_KeepsOneSpreadLayerPerAttachedStar()
    {
        for (var layers = 1; layers <= 5; layers++)
        {
            var source = "A = 1, 2, 3\n" + "A" + new string('*', layers) + "\n42";
            var root = ParseClean(source).Root;
            var expr = root.Output[0];
            for (var i = 0; i < layers; i++)
                expr = Assert.IsType<Expr.SequenceSpread>(expr).Operand;
            Assert.Equal("A", Assert.IsType<Expr.Resolve>(expr).Name);
            Assert.Equal("42", Shape(root.Output[1]));
        }
    }

    // ── Source spans ─────────────────────────────────────────────────────────

    [Fact]
    public void TheLineFinalSpread_SpansItsOperandThroughTheStar()
    {
        var spread = Assert.IsType<Expr.SequenceSpread>(ParseClean("A = 1, 2, 3\nA*\n42").Root.Output[0]);
        Assert.Equal(new SourceSpan(2, 1, 2, 3), spread.Span);
        var twice = Assert.IsType<Expr.SequenceSpread>(ParseClean("A = 1, 2, 3\nA**").Root.Output[0]);
        Assert.Equal(new SourceSpan(2, 1, 2, 4), twice.Span);
        Assert.Equal(new SourceSpan(2, 1, 2, 3), Assert.IsType<Expr.SequenceSpread>(twice.Operand).Span);
    }

    [Fact]
    public void SemanticModel_ResolvesTheSpreadOperand_AndTheNextRowIndependently()
    {
        const string source = "A = 1, 2, 3\nB = 4\nA*\nB";
        var model = SemanticModelBuilder.Build(Parser.Parse(source));
        var a = model.FindResolutionAt(new SourcePosition(3, 1));
        var b = model.FindResolutionAt(new SourcePosition(4, 1));
        Assert.NotNull(a);
        Assert.NotNull(b);
        Assert.Equal(new SourceSpan(3, 1, 3, 2), a!.Occurrence.Span);
        Assert.Equal(new SourceSpan(1, 1, 1, 2), a.ResolvedDeclaration!.Span);
        Assert.Equal(new SourceSpan(4, 1, 4, 2), b!.Occurrence.Span);
        Assert.Equal(new SourceSpan(2, 1, 2, 2), b.ResolvedDeclaration!.Span);
    }

    // ── Metamorphic properties ───────────────────────────────────────────────

    /// <summary>Representative operands: a literal, a name, a call, a selection and a group.</summary>
    private const string OperandDefinitions = "A = 1, 2\nB = 3\nF(x) = x + 1\nL = [4, 5]\n";

    public static TheoryData<string> SpreadOperands() => new() { "7", "A", "F(1)", "L[0]", "(A)", "(1, 2)", "[1, 2]" };

    public static TheoryData<string> ProductOperands() => new() { "7", "B", "F(1)", "L[0]", "(B)", "(B + 1)" };

    [Theory]
    [MemberData(nameof(SpreadOperands))]
    public void CompletedLineStability_AppendingAnIndependentRow_PreservesTheSpread(string operand)
    {
        var alone = ParseClean(OperandDefinitions + operand + "*").Root;
        var appended = ParseClean(OperandDefinitions + operand + "*\n42").Root;
        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(alone.Output));
        Assert.Equal(2, appended.Output.Count);
        Assert.Equal(LeanAstEncoder.EncodeExpr(spread), LeanAstEncoder.EncodeExpr(appended.Output[0]));
        Assert.Equal("42", Shape(appended.Output[1]));
    }

    [Theory]
    [MemberData(nameof(ProductOperands))]
    public void DetachedMultiplicationContinuation_MatchesTheOneLineProduct(string operand)
    {
        var oneLine = ParseClean(OperandDefinitions + operand + " * " + operand).Root;
        var continued = ParseClean(OperandDefinitions + operand + " *\n" + operand).Root;
        var product = Assert.IsType<Expr.Binary>(Assert.Single(continued.Output));
        Assert.Equal(BinaryOp.Mul, product.Op);
        Assert.Equal(LeanAstEncoder.EncodeProgram(oneLine), LeanAstEncoder.EncodeProgram(continued));
    }

    [Theory]
    [MemberData(nameof(ProductOperands))]
    public void SameLineMultiplication_IsSpacingInvariant(string operand)
    {
        var reference = LeanAstEncoder.EncodeProgram(ParseClean(OperandDefinitions + operand + " * " + operand).Root);
        foreach (var star in new[] { "*", "* ", " *", "\t*\t", "  *" })
        {
            var root = ParseClean(OperandDefinitions + operand + star + operand).Root;
            Assert.Equal(BinaryOp.Mul, Assert.IsType<Expr.Binary>(Assert.Single(root.Output)).Op);
            Assert.Equal(reference, LeanAstEncoder.EncodeProgram(root));
        }
    }

    public static TheoryData<string> LineEndingPrograms() => new()
    {
        "A = 1, 2, 3\nA*",
        "A = 1, 2, 3\nB = 4\nA*\nB",
        "A = 2\nB = 3\nA *\nB",
        "A = 1, 2, 3\nX = A*\nX\n42",
        "A = 1, 2, 3\nA**\n42",
        "F(*xs) = xs\nA = 1, 2, 3\nB = 4\nF(\n  A*\n  B\n)",
        "A = 1, 2, 3\nB = 4\n[\n  A*\n  B\n]",
        "F(*xs) = xs.count\nA = 1, 2, 3\nA* # receiver\n.F",
        "A = 2\nB = 3\nX = A *\n# operand\nB\nX",
    };

    [Theory]
    [MemberData(nameof(LineEndingPrograms))]
    public async Task LfAndCrlf_HaveTheSameTreeAndValue(string source)
    {
        var crlf = source.Replace("\n", "\r\n", StringComparison.Ordinal);
        Assert.Equal(
            LeanAstEncoder.EncodeProgram(ParseClean(source).Root),
            LeanAstEncoder.EncodeProgram(ParseClean(crlf).Root));
        Assert.Equal(await ValueOnEveryRoute(source), await ValueOnEveryRoute(crlf));
    }
}
