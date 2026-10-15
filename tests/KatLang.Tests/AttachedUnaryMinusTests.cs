using static KatLang.Tests.SixRouteAgreement;

namespace KatLang.Tests;

public class AttachedUnaryMinusTests
{
    [Theory]
    [InlineData("-2", "-2")]
    [InlineData("x=2\n-x", "-2")]
    [InlineData("-(1+2)", "-3")]
    [InlineData("--2", "2")]
    [InlineData("-(-2)", "2")]
    [InlineData("2 ^ -2", "0.25")]
    [InlineData("-2 ^ 2", "-4")]
    [InlineData("(-2) ^ 2", "4")]
    [InlineData("F(x)=x+1\n-F(2)", "-3")]
    [InlineData("A=[2,3]\n-A[0]", "-2")]
    public async Task AttachedUnaryMinus_KeepsItsExistingPrecedenceAndValue(string source, string expected)
    {
        var observed = await OnEveryRouteAsync(source);
        Assert.Equal("ok", observed.Kind);
        Assert.Equal(expected, observed.Value);
        Assert.Empty(observed.Errors);
    }

    [Theory]
    [InlineData("- 2")]
    [InlineData("-\t2")]
    [InlineData("-\n2")]
    [InlineData("- # comment\n2")]
    [InlineData("- x")]
    [InlineData("- (1+2)")]
    [InlineData("- [1,2]")]
    [InlineData("- -2")]
    [InlineData("2 ^ - 2")]
    [InlineData("- 'text'")]
    public void DetachedMinus_WithoutALeftOperandIsASyntaxError(string source)
    {
        var parsed = Parser.ParseSyntax(source);
        Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.UnexpectedToken
            && d.Message.Contains("Unary '-' must be directly attached", StringComparison.Ordinal));
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
    }

    [Theory]
    [InlineData("10-2", "8")]
    [InlineData("10 - 2", "8")]
    [InlineData("10- 2", "8")]
    [InlineData("10 -2", "8")]
    [InlineData("10 -\n2", "8")]
    [InlineData("10\n- 2", "8")]
    [InlineData("10\n-\n# comment\n2", "8")]
    [InlineData("10\n- -2", "12")]
    [InlineData("10\n-2", "S[10, -2]")]
    [InlineData("10\n* 2", "20")]
    [InlineData("10 *\n2", "20")]
    // Issue #183: an attached line-final star is a completed spread (of the scalar 10).
    [InlineData("10*\n2", "S[10, 2]")]
    public async Task GrammarRolePriority_DeterminesNewlineContinuation(string source, string expected)
    {
        var observed = await OnEveryRouteAsync(source);
        Assert.Equal("ok", observed.Kind);
        Assert.Equal(expected, observed.Value);
        Assert.Empty(observed.Errors);
    }

    [Theory]
    [InlineData("{0}", "10, -2", "10 - 2")]
    [InlineData("A = {0}\nA", "A=10\n-2\nA", "A=10-2\nA")]
    [InlineData("F(x) = {0}\nF(0)", "F(x)=10\n-2\nF(0)", "F(x)=10-2\nF(0)")]
    [InlineData("a,*rest = {0}\na,rest", "a,*rest=10\n-2\na,rest", "a,*rest=10-2\na,rest")]
    [InlineData("{{{0}}}", "{10,-2}", "{10-2}")]
    [InlineData("({0})", "(10,-2)", "(10-2)")]
    [InlineData("F({0})", "F(10,-2)", "F(10-2)")]
    [InlineData("[{0}]", "[10,-2]", "[10-2]")]
    public void CriticalContrast_KeepsEachContextsSlotBoundary(string template, string attached, string detached)
    {
        foreach (var gap in new[] { "\n", "\r\n", "\n\n# c\n" })
        {
            AssertSameAst(attached, string.Format(template, "10" + gap + "-2"));
            AssertSameAst(detached, string.Format(template, "10" + gap + "- 2"));
        }
    }

    [Theory]
    [InlineData("- [1,2]\nLater=42\nLater")]
    [InlineData("-\nGood=41\nGood")]
    [InlineData("1\n-\nGood=41\nGood")]
    public void MalformedUnaryOrBinaryMinus_PreservesLaterDeclarations(string source)
    {
        var parsed = Parser.ParseSyntax(source);
        Assert.True(parsed.HasErrors);
        Assert.Contains(parsed.Root.Properties, p => p.Name is "Later" or "Good");
    }

    [Fact]
    public void AttachedNonNumericOperands_KeepEvaluationTypeErrors()
    {
        SourceProvenance.ParseValid("-'text'");
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("-'text'"));
        Assert.Contains(failure.Errors, e => e.Code == KatLangErrorCode.TypeMismatch);
    }

    [Theory]
    [InlineData("F(- 2)=1\nF(0)=0\nLater=42\nLater")]
    [InlineData("F(-\n2)=1\nF(0)=0\nLater=42\nLater")]
    [InlineData("F(- # c\n2)=1\nF(0)=0\nLater=42\nLater")]
    [InlineData("F([- 2])=1\nLater=42\nLater")]
    public void NegativePatternSigns_AlsoRequireAttachment(string source)
    {
        var parsed = Parser.ParseSyntax(source);
        Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.UnexpectedToken
            && d.Message.Contains("negative pattern", StringComparison.Ordinal));
        Assert.Contains(parsed.Root.Properties, p => p.Name == "Later");
    }

    [Fact]
    public async Task AttachedNegativeLiteralPatterns_KeepMatching()
    {
        var observed = await OnEveryRouteAsync("F(-2)=42\nF(n)=0\nF(-2)");
        Assert.Equal("ok", observed.Kind);
        Assert.Equal("42", observed.Value);
    }

    [Theory]
    [InlineData("-")]
    [InlineData("-\nGood=41\nGood")]
    [InlineData("(-\n)")]
    public void DetachedUnaryRecovery_ReportsItsOwnSyntaxErrorOnce(string source)
    {
        var error = Assert.Single(Parser.ParseSyntax(source).Diagnostics);
        Assert.Equal(DiagnosticCode.UnexpectedToken, error.Code);
        Assert.Contains("Unary '-' must be directly attached", error.Message, StringComparison.Ordinal);
    }

    private static void AssertSameAst(string oneLine, string multiline)
        => Assert.Equal(LeanAstEncoder.EncodeProgram(SourceProvenance.ParseSyntaxValidRoot(oneLine)),
            LeanAstEncoder.EncodeProgram(SourceProvenance.ParseSyntaxValidRoot(multiline)));
}
