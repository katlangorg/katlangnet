using KatLang.Semantics;

namespace KatLang.Tests;

public sealed class SourceRecoveryTests
{
    [Theory]
    [InlineData("a,b={open {public Q=7}\nQ,10}\na+b", "17")]
    [InlineData("Result={a,b={open {public Q=7}\nQ,10}\na+b}\nResult", "17")]
    [InlineData("a,b={open {public Q=7}\nQ,10}\nc,d={open {public R=3}\nR,4}\na+b+c+d", "24")]
    [InlineData("a,b={open {Lib={public Q=7}\npublic Alias=Lib}\nAlias.Q,10}\na+b", "17")]
    [InlineData("R={open {public Q=7}\nQ,10}\na,b=R\nc,d=R\na+b+c+d", "34")]
    public async Task InlineOpenDeconstruction_KeepsTheWrittenOwner(string source, string expected)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal(("ok", expected), (observation.Kind, observation.Value));
        var parsed = SourceProvenance.ParseValid(source);
        Assert.NotNull(SemanticModelBuilder.Build(parsed.Parsed));
    }

    [Theory]
    [InlineData("a,b={open Missing\n7,10}\na+b", DiagnosticCode.UnresolvedOpenTarget)]
    [InlineData("a,b={open {public Q=7}\nQ,10}\na+b\n@", DiagnosticCode.UnexpectedCharacter)]
    public void InvalidDeconstruction_ReturnsDiagnosticsAndAUsableEditorTree(string source, DiagnosticCode code)
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        Assert.True(parsed.HasFrontEndErrors);
        Assert.Contains(parsed.Diagnostics, diagnostic => diagnostic.Code == code && diagnostic.Span is not null);
        Assert.NotNull(SemanticModelBuilder.Build(parsed.Parsed));
    }

    [Theory]
    [InlineData("open A\nBox={Algorithm(x)=x}\nA=Box.Algorithm\n0")]
    [InlineData("open A\nBox={Algorithm(x)=x}\nB=Box.Algorithm\nA=B\n0")]
    public void OpenAlias_ReportsTheSelectedDeclaredMembersSignature(string source)
    {
        var errors = SourceProvenance.ExpectFrontEndError(source).Where(d => d.Severity == DiagnosticSeverity.Error).ToArray();
        var error = Assert.Single(errors);
        Assert.Equal(DiagnosticCode.IllegalInOpen, error.Code);
        Assert.Contains("empty effective parameter list (found: x)", error.Message, StringComparison.Ordinal);
        var line = source.Split('\n').Select((text, index) => (text, index)).Single(row => row.text == "open A").index + 1;
        Assert.Equal(new SourceSpan(line, 6, line, 7), error.Span);
    }

    [Theory]
    [InlineData("Use(b)={A=b.G\nA(3)}\nBox={G(x)=x*10}\nUse(Box)", "30")]
    [InlineData("y(v)=v+2\nF(p)={x=p\nA=x.y\nA}\nF(5)", "7")]
    [InlineData("y(v)=v+2\nF(p)={x=p\nA=x.y\nH=A.abs+0\nH}\nF(5)", "7")]
    [InlineData("F(p)={x={y={public foo=9}}\nA=x.y\nA.foo}\nF(1)", "9")]
    public async Task ReceiverClassification_PreservesParameterAliasesAndOrdinaryFallback(string source, string expected)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal(("ok", expected), (observation.Kind, observation.Value));
    }
}
