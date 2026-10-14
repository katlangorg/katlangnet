using static KatLang.Tests.SixRouteAgreement;

namespace KatLang.Tests;

public class LineFinalStarPriorityTests
{
    [Theory]
    [InlineData("7*8")]
    [InlineData("7 * 8")]
    [InlineData("7*\n8")]
    [InlineData("7 *\n8")]
    [InlineData("7* # c\n\n# c\n8")]
    [InlineData("7*\r\n8")]
    public async Task LineFinalStar_AnnouncesMultiplication(string source)
    {
        var binary = Assert.IsType<Expr.Binary>(Assert.Single(SourceProvenance.ParseSyntaxValidRoot(source).Output));
        Assert.Equal(BinaryOp.Mul, binary.Op);
        var observed = await OnEveryRouteAsync(source);
        Assert.Equal("ok", observed.Kind);
        Assert.Equal("56", observed.Value);
        Assert.Empty(observed.Errors);
    }

    [Theory]
    [InlineData("7*")]
    [InlineData("7 *")]
    [InlineData("7*\n")]
    [InlineData("7* # c\n\n# c")]
    [InlineData("[7*\n]")]
    [InlineData("F(7*\n)")]
    [InlineData("{7*\n}")]
    [InlineData("7*\n, 8")]
    public void NewlineOrEof_NeverClosesASpread(string source)
    {
        var parsed = Parser.ParseSyntax(source);
        Assert.True(parsed.HasErrors);
        Assert.DoesNotContain(parsed.Root.Output, e => e is Expr.SequenceSpread);
        Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.UnexpectedToken);
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
    }

    [Theory]
    [InlineData("X=8", "X")]
    [InlineData("X(a)=a", "X")]
    [InlineData("a,b=7,8", "a")]
    [InlineData("public X=8", "X")]
    [InlineData("~X=8", "X")]
    [InlineData("true=8", "Later")]
    [InlineData("open M", "Later")]
    public void FollowingDeclaration_IsPreservedAfterMissingMultiplication(string head, string name)
    {
        foreach (var gap in new[] { "\n", " # c\n\n# c\n", "\r\n" })
        {
            var parsed = Parser.ParseSyntax("7*" + gap + head + "\nLater=42\nLater");
            Assert.True(parsed.HasErrors);
            Assert.Contains(parsed.Root.Properties, p => p.Name == name);
            var mul = Assert.IsType<Expr.Binary>(parsed.Root.Output[0]);
            Assert.Equal(BinaryOp.Mul, mul.Op);
            Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.UnexpectedToken
                && d.Span?.Start.Line == 1 && d.Message.Contains("after '*'", StringComparison.Ordinal));
        }
    }

    [Theory]
    [InlineData("F(*xs)=xs\nF((1,2)*)", "L[1, 2]")]
    [InlineData("F(*xs)=xs\nF((1,2)*,3)", "L[1, 2, 3]")]
    [InlineData("[(1,2)*]", "L[1, 2]")]
    [InlineData("[10,20][(0,1)*]", "S[10, 20]")]
    [InlineData("(1,2)*,3", "S[1, 2, 3]")]
    [InlineData("(1,2)*,\n3", "S[1, 2, 3]")]
    [InlineData("((1,2)*)", "S[1, 2]")]
    [InlineData("{(1,2)*}", "S[1, 2]")]
    [InlineData("F(*xs)=sum(xs)\n(1,2)*.F", "3")]
    public async Task SameLineSyntax_ExplicitlyClosesSpreadItems(string source, string expected)
    {
        var observed = await OnEveryRouteAsync(source);
        Assert.Equal("ok", observed.Kind);
        Assert.Equal(expected, observed.Value);
        Assert.Empty(observed.Errors);
    }

    [Theory]
    [InlineData("F(A *)")]
    [InlineData("[A *]")]
    [InlineData("A *, B")]
    public void ActualSpread_StillRequiresAttachment(string source)
        => Assert.Contains(Parser.ParseSyntax(source).Diagnostics, d => d.Code == DiagnosticCode.InvalidSpreadMarker);
}
