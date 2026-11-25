using KatLang.Semantics;

namespace KatLang.Tests;

public sealed class ContextIntegrationRecoveryTests
{
    [Theory]
    [InlineData("Data.V", false)]
    [InlineData("A.V", false)]
    [InlineData("B.V", false)]
    [InlineData("Data.Sub.V", true)]
    public void OpenedCapture_KeepsEffectsAndCacheWithinItsActivation(string path, bool nested)
    {
        var seen = new List<string>();
        var host = HostOperations.Create(HostOperation.Create("emit", (arguments, _) =>
        {
            seen.Add(SemanticExplorerHarness.Neutral(arguments[0]));
            return arguments[0];
        }, "value"));
        var source = $$"""
            Outer(k) = {
                open Make
                Make = {
                    public Data = {
                        {{(nested ? "Sub = { V = emit(k) }" : "V = emit(k)")}}
                        k
                    }
                }
                A = Data
                B = A
                P = {{path}}
                P, P, {{path}}
            }
            Outer(10), Outer(55)
            """;
        var options = new RunOptions { HostOperations = host };
        var parsed = Parser.Parse(source, options);
        Assert.False(parsed.HasErrors, string.Join(';', parsed.Diagnostics));
        var outer = parsed.Root.Properties.Single(p => p.Name == "Outer").Value;
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters,
            outer.Properties.Single(p => p.Name == "P").Exposure);
        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, options));
        Assert.Equal("S[S[10, 10, 10], S[55, 55, 55]]", SemanticExplorerHarness.Neutral(result.Value));
        Assert.Equal(new[] { "10", "55" }, seen);
    }

    [Fact]
    public void AnIndependentOpenedMember_StaysExportedAcrossActivations()
    {
        const string source = "Lib={public Data={V=42\n0}}\nOuter(k)={open Lib\nP=Data.V\nP}\nOuter(10),Outer(55)";
        var root = SourceProvenance.ParseValid(source).Root;
        var outer = root.Properties.Single(p => p.Name == "Outer").Value;
        Assert.Equal(PropertyExposure.Exported, outer.Properties.Single(p => p.Name == "P").Exposure);
        Assert.Equal("S[42, 42]", SemanticExplorerHarness.Neutral(Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).Value));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task DeferredKnownNames_KeepTheirKindWithoutLoadingUnselectedBranches(bool malformed)
    {
        var downloads = new List<string>();
        var source = "Lib={public Rate=2\n0}\nF(0)={open 'https://katlang.org/v/later.kat'\nG={open Lib\nRate" +
            (malformed ? " + )" : "") + "\n}\nG}\nF(n)=n\nF(1)";
        var parsed = await Parser.ParseAsync(source, new RunOptions
        {
            AllowedHosts = ["katlang.org"],
            DownloadCode = (url, _) => { downloads.Add(url); return ValueTask.FromResult("public Later=9"); },
        });
        Assert.Equal(malformed, parsed.HasErrors);
        var model = SemanticModelBuilder.Build(parsed);
        Assert.Empty(downloads);
        var position = new SourcePosition(5, 1);
        var visible = Assert.Single(model.GetVisibleSymbolsAt(position), symbol => symbol.Name == "Rate");
        Assert.Equal(IdentifierClassification.DeferredModuleReference, visible.Classification);
        Assert.Null(visible.Declaration);
        Assert.Null(visible.Property);
        var rootSymbols = model.GetVisibleSymbolsAt(new SourcePosition(8, 1));
        Assert.Equal(IdentifierClassification.PropertyReference, Assert.Single(rootSymbols, symbol => symbol.Name == "Lib").Classification);
        Assert.Equal(IdentifierClassification.PropertyReference,
            Assert.Single(SemanticModelBuilder.Build(SourceProvenance.ParseValid("open Lib\nLib={public Rate=2\n0}\nRate").Parsed)
                .GetVisibleSymbolsAt(new SourcePosition(4, 1)), symbol => symbol.Name == "Rate").Classification);
    }

    [Fact]
    public void RawAdmission_ObservesInferredOwnershipWithoutReinterpretingTheAstAsResolved()
    {
        var syntax = Parser.ParseSyntax("F=x+1\nF(1)");
        Assert.False(syntax.HasErrors);
        var body = syntax.Root.Properties.Single().Value;
        var raw = ElaboratedScopeLookup.CreateScope(syntax.Root, sourcePhase: StaticAstPhase.RawSource);
        var rawBody = ElaboratedScopeLookup.CreateScope(body, raw);
        Assert.True(ElaboratedScopeLookup.SelectOwnedDeclaration(rawBody, "x", ElaboratedScopeLookup.OwnParameterBindings.Instance).TryGetParameter(out _));
        var resolved = ElaboratedScopeLookup.CreateScope(syntax.Root, sourcePhase: StaticAstPhase.Resolved);
        var boundBody = ElaboratedScopeLookup.CreateScope(body, resolved);
        Assert.False(ElaboratedScopeLookup.SelectOwnedDeclaration(boundBody, "x", ElaboratedScopeLookup.OwnParameterBindings.Instance).TryGetParameter(out _));
        Assert.Empty(body.Params);
        Assert.IsType<Expr.Resolve>(Assert.IsType<Expr.Binary>(body.Output.Single()).Left);
    }
}
