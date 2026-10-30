using KatLang.Semantics;
using KatLang.TestInfrastructure;
using System.Numerics;

namespace KatLang.Tests;

public sealed class StaticStructureDefaultCutoverTests
{
    [Fact]
    public void StandaloneResolutionCannotReconstructDetectionFromAnArbitraryIntermediateTree()
    {
        var source = SourceProvenance.ParseSyntaxValidRoot("F=x+1\nF(41)");
        Assert.Throws<ArgumentNullException>(() => ImplicitArgumentResolver.ResolvePrevalidated(source));
    }

    [Theory]
    [InlineData("Lib={public K=42\n0}\nA=Lib\nB=A\nB.K")]
    [InlineData("open A\nLib={public K=42\n0}\nA=Lib\nK")]
    [InlineData("A={public K=42\n0}\nB={public C=A\n0}\nB.C.K")]
    [InlineData("A={public K=42\n0}\nB={C=A}.C\nB.K")]
    public async Task PublicSyncAndAsyncCompilationPublishTheSameSelectedStructure(string source)
    {
        var sync = Parser.Parse(source);
        var asyncResult = await Parser.ParseAsync(source);
        foreach (var parsed in new[] { sync, asyncResult })
        {
            Assert.False(parsed.HasErrors, string.Join('\n', parsed.Diagnostics.Select(d => d.Message)));
            Assert.NotNull(parsed.Root.CompletedStructure);
            Assert.NotNull(SemanticModelBuilder.Build(parsed));
            var actual = Evaluator.RunFlat(new Expr.AlgorithmExpr(parsed.Root));
            Assert.False(actual.IsError, actual.IsError ? actual.Error.ToString() : "");
            Assert.Equal(new Decimal128[] { 42 }, actual.Value);
        }
    }

    [Theory]
    [InlineData("A.3.1")]
    [InlineData("A.3.2")]
    [InlineData("A.3.3a")]
    [InlineData("A.3.3b")]
    public void DefaultParserRejectsSelfDependentInferenceAndSupportsEditorRecovery(string witness)
    {
        var parsed = Parser.Parse(StaticStructureWitnessSources.Cases[witness]);
        Assert.True(parsed.HasErrors);
        Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.SelfDependentInferredParameters);
        Assert.NotNull(SemanticModelBuilder.Build(parsed));
    }

    [Fact]
    public void DefaultParserUsesTheUnifiedStrataVerdicts()
    {
        var parsed = Parser.Parse(StaticStructureWitnessSources.Cases["strata0-get"]);
        Assert.False(parsed.HasErrors, string.Join('\n', parsed.Diagnostics.Select(d => d.Message)));
        var actual = Evaluator.RunFlat(new Expr.AlgorithmExpr(parsed.Root));
        Assert.False(actual.IsError, actual.IsError ? actual.Error.ToString() : "");
        Assert.Equal(new Decimal128[] { 42 }, actual.Value);
        Assert.Contains(Parser.Parse(StaticStructureWitnessSources.Cases["strata0-ambiguous"]).Diagnostics,
            d => d.Code == DiagnosticCode.AmbiguousOpen);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task PublicModuleCompilationPublishesEagerAndSelectedDeferredFacts(bool deferred)
    {
        var downloads = 0;
        var options = new RunOptions
        {
            AllowedHosts = ["mods.test"],
            DownloadCode = async (_, _) => { await Task.Yield(); downloads++; return "public K=42\n0"; },
        };
        var source = deferred
            ? "F(0)=0\nF(x)={open load('https://mods.test/m')\nK}\nF(1)"
            : "open load('https://mods.test/m')\nK";
        var parsed = await Parser.ParseAsync(source, options);
        Assert.False(parsed.HasErrors, string.Join('\n', parsed.Diagnostics.Select(d => d.Message)));
        Assert.NotNull(parsed.Root.CompletedStructure);
        Assert.NotNull(SemanticModelBuilder.Build(parsed));
        Assert.Equal(deferred ? 0 : 1, downloads);
        var actual = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));
        Assert.False(actual.IsError, actual.IsError ? actual.Error.ToString() : "");
        Assert.Equal(new Decimal128[] { 42 }, actual.Value);
        Assert.Equal(1, downloads);
    }

    [Fact]
    public void SupersededDetectorAndChaseAuthoritiesArePhysicallyAbsent()
    {
        var root = RepoRoot.Find();
        var detector = File.ReadAllText(Path.Combine(root, "src/KatLang/ParameterDetector.cs"));
        var lookup = File.ReadAllText(Path.Combine(root, "src/KatLang/ElaboratedScopeLookup.cs"));
        var resolver = File.ReadAllText(Path.Combine(root, "src/KatLang/ImplicitArgumentResolver.cs"));
        var pipeline = File.ReadAllText(Path.Combine(root, "src/KatLang/FrontEndPipeline.cs"));
        foreach (var obsolete in new[] { "InferredInputDecisions", "InputOccurrenceIndex", "class UndecidedInput", "InputDecider =" })
            Assert.DoesNotContain(obsolete, detector);
        foreach (var obsolete in new[] { "ChaseStaticStructure(", "SuspendWalk(", "SuspendChase(", "IInferredInputDecider", "TentativeReads" })
            Assert.DoesNotContain(obsolete, lookup);
        foreach (var obsolete in new[] { "InvocationTargets", "StructureKeyComparer", "IsCyclicTargetChase(", "StaticChain(" })
            Assert.DoesNotContain(obsolete, resolver);
        Assert.DoesNotContain("unifiedStructure", pipeline);
        Assert.DoesNotContain("ProcessStaticStructureCandidate", pipeline);
    }
}
