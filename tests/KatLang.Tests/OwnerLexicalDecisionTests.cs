namespace KatLang.Tests;

public class OwnerLexicalDecisionTests
{
    [Theory]
    [InlineData("P = 1\n, 2\nP")]
    [InlineData("P = 1\r\n, 2\r\nP")]
    [InlineData("P = 1\n# comment\n, 2\nP")]
    [InlineData("F(x) = x\n, 2\nF(1)")]
    [InlineData("F(0) = 1\n, 2\nF(n) = n, n\nF(0)")]
    [InlineData("a, b = 1, 2\n, 3\na, b")]
    [InlineData("P = 1 +\n2\n, 3\nP")]
    [InlineData("P = (1,\n2)\n, 3\nP")]
    public void LeadingComma_ExplicitlyContinuesACompletedDefinitionBody(string source)
    {
        SourceProvenance.ParseValid(source);
    }

    [Theory]
    [InlineData("P = 1,\n2\nP")]
    [InlineData("P = 1 +\n2\nP")]
    [InlineData("P =\n1, 2\nP")]
    [InlineData("P = (1\n, 2)\nP")]
    [InlineData("P = [1\n, 2]\nP")]
    [InlineData("F(a\n, b) = a + b\nF(1\n, 2)")]
    [InlineData("[10, 20][0\n, 1]")]
    [InlineData("1\n, 2")]
    [InlineData("{1\n, 2}")]
    [InlineData("open M\n, N\nM = {public A = 1}\nN = {public B = 2}\nA, B")]
    public void Commas_ContinueAnIncompleteBodyOrAnAlreadyOpenList(string source)
        => SourceProvenance.ParseValid(source);

    [Fact]
    public void LeadingComma_AddsASecondSlotToThePrecedingProperty()
    {
        var parsed = SourceProvenance.ParseValid("P = 1\n, 2\nP").Parsed;
        var p = Assert.Single(parsed.Root.Properties);
        Assert.Equal("P", p.Name);
        Assert.Equal(2, p.Value.Output.Count);
        Assert.All(p.Value.Output, e => Assert.IsType<Expr.Num>(e));
    }

    [Theory]
    [InlineData("1\\\n2", 2)]
    [InlineData("1 +\\\n2", 1)]
    public void BackslashBeforeLf_IsALexicalErrorAndNeverAContinuation(string source, int outputSlots)
    {
        var parsed = Parser.ParseSyntax(source);
        var error = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.UnexpectedCharacter, error.Code);
        Assert.Equal(1, error.Span?.Start.Line);
        Assert.Equal(source.IndexOf('\\') + 1, error.Span?.Start.Column);
        Assert.Equal(outputSlots, parsed.Root.Output.Count);
    }

    [Fact]
    public void LiteralBackslashesAndDoubleQuotedEscapes_StayDistinctFromPhysicalContinuation()
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot("'a\\nb'");
        Assert.Equal("a\\nb", Assert.IsType<Expr.StringLiteral>(Assert.Single(raw.Output)).Value);
        var escaped = SourceProvenance.ParseSyntaxValidRoot("\"a\\nb\\\\c\"");
        Assert.Equal("a\nb\\c", Assert.IsType<Expr.StringLiteral>(Assert.Single(escaped.Output)).Value);
        var (_, diagnostics) = Lexer.Tokenize("'a\\\nb'");
        Assert.Contains(diagnostics, d => d.Code == DiagnosticCode.UnterminatedStringLiteral);
    }
}
