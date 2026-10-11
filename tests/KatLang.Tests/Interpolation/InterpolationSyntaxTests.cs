namespace KatLang.Tests.Interpolation;

/// <summary>
/// STR-02 grammar: a hole-free double-quoted string IS a string literal (the very node a
/// single-quoted string parses to), an interpolated string is <see cref="Expr.InterpolatedString"/>
/// whose every hole is ONE ordinary expression of the enclosing owner, the hole restrictions
/// (no empty hole, no hole-level separator, selection, declaration or format specifier) are
/// targeted diagnostics with local recovery, and interpolation is refused where the grammar
/// needs fixed text (clause-head patterns, <c>open</c> targets, <c>load</c> URLs).
/// </summary>
public class InterpolationSyntaxTests
{
    private static Expr OnlyRow(string source)
        => Assert.Single(SourceProvenance.ParseSyntaxValidRoot(source).Output);

    private static IReadOnlyList<Diagnostic> SyntaxDiagnostics(string source)
        => Parser.ParseSyntax(source).Diagnostics;

    // ── Shapes ─────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("\"abc\"", "abc")]
    [InlineData("\"\"", "")]
    [InlineData("\"{{x}}\"", "{x}")]
    [InlineData("\"a\\nb\"", "a\nb")]
    public void AHoleFreeDoubleQuotedString_ParsesToTheStringLiteralNode(string source, string text)
        => Assert.Equal(text, Assert.IsType<Expr.StringLiteral>(OnlyRow(source)).Value);

    [Fact]
    public void AHoleFreeDoubleQuotedString_IsTheSameNodeAsTheSingleQuotedSpelling()
    {
        var doubleQuoted = Assert.IsType<Expr.StringLiteral>(OnlyRow("\"a b\""));
        var singleQuoted = Assert.IsType<Expr.StringLiteral>(OnlyRow("'a b'"));
        Assert.Equal(singleQuoted with { Span = null }, doubleQuoted with { Span = null });
    }

    [Fact]
    public void AnInterpolatedString_HoldsItsHeadText_AndOneLinkPerHole()
    {
        var node = Assert.IsType<Expr.InterpolatedString>(OnlyRow("x = 1\ny = 2\n\"a{x}b{y + 1}c\""));
        Assert.Equal("a", node.Head);
        Assert.Equal(2, node.Links.Count);
        Assert.Equal("x", Assert.IsType<Expr.Resolve>(node.Links[0].Hole).Name);
        Assert.Equal("b", node.Links[0].Text);
        Assert.IsType<Expr.Binary>(node.Links[1].Hole);
        Assert.Equal("c", node.Links[1].Text);
        Assert.Equal(new SourceSpan(3, 1, 3, 16), node.Span);
    }

    [Theory]
    [InlineData("F(x) = x\n\"{F(1)}\"", typeof(Expr.Call))]
    [InlineData("\"{(1, 2).count}\"", typeof(Expr.DotCall))]
    [InlineData("\"{if(true, 1, 2)}\"", typeof(Expr.Call))]
    [InlineData("\"{ { 1 } }\"", typeof(Expr.AlgorithmExpr))]
    [InlineData("\"{[1, 2]}\"", typeof(Expr.ListLiteral))]
    [InlineData("\"{(1, 2)}\"", typeof(Expr.Capture))]
    [InlineData("\"{1 < 2 < 3}\"", typeof(Expr.Comparison))]
    [InlineData("\"{not true}\"", typeof(Expr.Unary))]
    [InlineData("\"{\"in{1}\"}\"", typeof(Expr.InterpolatedString))]
    [InlineData("\"{'raw'}\"", typeof(Expr.StringLiteral))]
    [InlineData("xs = [1]\n\"{(xs:0)}\"", typeof(Expr.Index))]
    [InlineData("\"{((1))}\"", typeof(Expr.Num))]
    public void AHole_IsOneOrdinaryExpression(string source, Type holeType)
    {
        var node = Assert.IsType<Expr.InterpolatedString>(OnlyRow(source));
        Assert.IsType(holeType, Assert.Single(node.Links).Hole);
    }

    [Fact]
    public void AHoleExpression_MayContinueAcrossNoLine_ButUsesEveryOrdinaryOperator()
    {
        var node = Assert.IsType<Expr.InterpolatedString>(OnlyRow("a = 1\n\"{a * 2 + 3 ^ 2 div 1 mod 7 == 10 and true}\""));
        Assert.IsType<Expr.Binary>(Assert.Single(node.Links).Hole);
    }

    // ── Hole restrictions ──────────────────────────────────────────────────

    [Theory]
    [InlineData("\"{}\"", 2)]
    [InlineData("\"{ }\"", 2)]
    [InlineData("a = 1\nb = 2\n\"{a, b}\"", 4)]
    [InlineData("a = [1]\n\"{a:0}\"", 4)]
    [InlineData("a = 1\n\"{a:F2}\"", 4)]
    [InlineData("a = 1\n\"{a = 1}\"", 5)]
    [InlineData("a = 1\n\"{a=}\"", 4)]
    [InlineData("\"{,}\"", 3)]
    [InlineData("\"{:}\"", 3)]
    [InlineData("\"{=}\"", 3)]
    [InlineData("\"{1 2}\"", 5)]
    [InlineData("\"{1)}\"", 4)]
    [InlineData("\"{1]}\"", 4)]
    public void EveryHoleThatIsNotExactlyOneExpression_IsInvalidInterpolationHole_ReportedOnce(string source, int column)
    {
        var diagnostics = SyntaxDiagnostics(source);
        var diagnostic = Assert.Single(diagnostics);
        Assert.Equal(DiagnosticCode.InvalidInterpolationHole, diagnostic.Code);
        Assert.Equal(source.Count(c => c == '\n') + 1, Assert.NotNull(diagnostic.Span).Start.Line);
        Assert.Equal(column, diagnostic.Span.Value.Start.Column);
    }

    [Fact]
    public void AHoleLevelColon_NamesTheParenthesizedSelection_AndTheAbsentFormatSpecifiers()
    {
        var diagnostic = Assert.Single(SyntaxDiagnostics("a = [1]\n\"{a:0}\""));
        Assert.Contains("(xs:0)", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("format specifiers", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AColonInsideADelimiterWithinAHole_IsOrdinarySelection()
    {
        Assert.IsType<Expr.Index>(Assert.Single(Assert.IsType<Expr.InterpolatedString>(OnlyRow("a = [1]\n\"{(a:0)}\"")).Links).Hole);
        Assert.IsType<Expr.ListLiteral>(Assert.Single(Assert.IsType<Expr.InterpolatedString>(OnlyRow("a = [1]\n\"{[a:0]}\"")).Links).Hole);
    }

    [Theory]
    [InlineData("a = [1]\n\"{a*}\"")]
    [InlineData("a = [1]\n\"x{a*}y\"")]
    public void ABareSpreadHole_IsTheMisplacedSpreadError(string source)
        => Assert.Contains(SyntaxDiagnostics(source), d => d.Code == DiagnosticCode.MisplacedSpread);

    [Fact]
    public void ASpreadInsideAGroupInAHole_IsAnOrdinaryCapture()
        => Assert.IsType<Expr.Capture>(Assert.Single(Assert.IsType<Expr.InterpolatedString>(OnlyRow("a = [1]\n\"{(a*)}\"")).Links).Hole);

    [Fact]
    public void AMalformedHole_RecoversLocally_SoTheRestOfTheStringAndTheNextDeclarationSurvive()
    {
        var parsed = Parser.ParseSyntax("A = \"{1,}x{2}\"\nB = 7\nB");
        Assert.Equal(DiagnosticCode.InvalidInterpolationHole, Assert.Single(parsed.Diagnostics).Code);
        var a = Assert.Single(parsed.Root.Properties, p => p.Name == "A");
        var node = Assert.IsType<Expr.InterpolatedString>(Assert.Single(Assert.IsType<Algorithm.User>(a.Value).Output));
        Assert.Equal(2, node.Links.Count);
        Assert.Equal("x", node.Links[0].Text);
        Assert.Contains(parsed.Root.Properties, p => p.Name == "B");
    }

    [Theory]
    [InlineData("F(x) = x\nA = F(\"{ ) }\")\nB = 2")]
    [InlineData("A = [\"{ ] }\"]\nB = 2")]
    [InlineData("A = { \"{ } }\" }\nB = 2")]
    public void AHoleIsAnOwnershipBarrier_ACloserInsideItNeverClosesAnEnclosingConstruct(string source)
    {
        var parsed = Parser.ParseSyntax(source);
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Code == DiagnosticCode.InvalidInterpolationHole);
        Assert.Equal(source.Split('\n').Length - 1, Assert.NotNull(diagnostic.Span).Start.Line);
        Assert.Contains(parsed.Root.Properties, p => p.Name == "B");
    }

    [Fact]
    public void ADeclarationCannotBeWrittenInAHole()
        => Assert.Contains(SyntaxDiagnostics("\"{X = 1}\""), d => d.Code == DiagnosticCode.InvalidInterpolationHole);

    [Fact]
    public void AnInterpolatedStringFollowedOnTheSameLine_IsTheUnseparatedItemError()
    {
        Assert.Contains(SyntaxDiagnostics("\"{1}\" \"{2}\""), d => d.Code == DiagnosticCode.UnseparatedSameLineItem);
        Assert.Contains(SyntaxDiagnostics("\"a\" \"b\""), d => d.Code == DiagnosticCode.UnseparatedSameLineItem);
    }

    [Fact]
    public void ACallCannotFollowAnInterpolatedString()
        => Assert.Contains(SyntaxDiagnostics("\"{1}\"(2)"), d => d.Code == DiagnosticCode.UnseparatedSameLineItem);

    [Fact]
    public void InterpolatedStrings_AreOrdinarySlots()
    {
        var root = SourceProvenance.ParseSyntaxValidRoot("F(a, b) = a\nF(\"{1}\", \"{2}\"), [\"{3}\"], (\"{4}\", 5)");
        Assert.Equal(3, root.Output.Count);
    }

    [Fact]
    public void AMultilineHoleIsNotPossible_TheHoleMustCloseOnItsLine()
    {
        var parsed = Parser.ParseSyntax("A = \"{1 +\n2}\"\nB = 3\nB");
        Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.UnterminatedInterpolationHole);
        Assert.Contains(parsed.Root.Properties, p => p.Name == "B");
    }

    // ── Literal-only positions ─────────────────────────────────────────────

    [Fact]
    public void AHoleFreeDoubleQuotedString_IsALiteralClausePattern()
    {
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run("F(\"a\") = 1\nF(\"{{x}}\") = 3\nF(x) = 2\nF('a'), F(\"b\"), F('{x}')"));
        Assert.Equal("1\n2\n3", success.ToDisplayString().ReplaceLineEndings("\n"));
    }

    [Theory]
    [InlineData("F(\"a{x}\") = 1\nF(y) = 2\nF(1)")]
    [InlineData("F((\"{1}\", y)) = 1\nF(z) = 2\nF(1)")]
    [InlineData("F([\"{1}\"]) = 1\nF(z) = 2\nF(1)")]
    public void AnInterpolatedString_IsNotAClausePattern(string source)
    {
        var diagnostics = SyntaxDiagnostics(source);
        Assert.Contains(diagnostics, d => d.Code == DiagnosticCode.InterpolationNotAllowedHere);
    }

    [Fact]
    public void AnInterpolatedString_IsNotAnOpenTarget()
    {
        var parsed = Parser.ParseSyntax("x = 1\nopen \"https://katlang.org/{x}.kat\"\n2");
        Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.InterpolationNotAllowedHere);
    }

    [Fact]
    public async Task AHoleFreeDoubleQuotedString_IsAnOpenTargetAndALoadUrl()
    {
        var options = new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult("public V = 41") };
        var opened = Assert.IsType<RunResult.Success>(
            await KatLangEngine.RunAsync("open \"https://katlang.org/m.kat\"\nV + 1", options));
        Assert.Equal("42", opened.ToDisplayString());
        var loaded = Assert.IsType<RunResult.Success>(
            await KatLangEngine.RunAsync("M = load(\"https://katlang.org/m.kat\")\nM.V", options));
        Assert.Equal("41", loaded.ToDisplayString());
    }

    [Fact]
    public async Task AnInterpolatedLoadUrl_IsNotALiteral_AndALoadInAHoleIsARuntimeExpression()
    {
        var downloads = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) =>
            {
                downloads++;
                return ValueTask.FromResult("public V = 41");
            },
        };

        var dynamicUrl = await Parser.ParseAsync("x = 'm'\nM = load(\"https://katlang.org/{x}.kat\")\nM.V", options);
        Assert.Contains(dynamicUrl.Diagnostics, d => d.Code == DiagnosticCode.InvalidLoadDirective);

        var inHole = await Parser.ParseAsync("\"{load('https://katlang.org/m.kat')}\"", options);
        Assert.Contains(inHole.Diagnostics, d => d.Code == DiagnosticCode.InvalidLoadDirective);
        Assert.Equal(0, downloads);
    }
}
