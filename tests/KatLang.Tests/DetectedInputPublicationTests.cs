namespace KatLang.Tests;

public sealed class DetectedInputPublicationTests
{
    [Theory]
    [InlineData("F=x.cos\nF(0.5)","F","x")]
    [InlineData("K=a.t\nK(7,{a+1})","K","a,t")]
    [InlineData("K=a.~t\nK({a+1},7)","K","t,a")]
    [InlineData("P=a.\nb\nb(x)=x+1\nP(5)","P","a")]
    public void DetectionPublishesTheAuthoritativeQ7Signature(string source,string name,string captures)
    {
        var syntax=Parser.ParseSyntax(source);Assert.False(syntax.HasErrors);
        var operation=StaticStructureAdmission.Create(syntax.Root).Operation;
        var property=syntax.Root.Properties.Single(p=>p.Name==name);
        var key=operation.ContextOf(operation.Root,property.Value);
        var names=Assert.IsType<string[]>(operation.Read(StaticQueryKey.Inputs(key)).Data);
        Assert.Equal(captures.Split(','),names);
        var detected=ParameterDetector.DetectPrevalidated(syntax.Root,structuralOperation:operation);
        Assert.Empty(detected.Diagnostics);
        Assert.Equal(names,detected.Root.Properties.Single(p=>p.Name==name).Value.Params);
        var resolved=PropertyExposureResolver.Resolve(ImplicitArgumentResolver.Resolve(detected));
        Assert.False(Evaluator.RunFlat(new Expr.AlgorithmExpr(resolved)).IsError);
    }

    [Fact]
    public void InheritedAndBranchBoundHeadsKeepTheNarrowODBAliasExemption()
    {
        var root=SourceProvenance.ParseValid("Outer(b)={A=b.C\n0}\nF(0)=0\nF(b)={A=b.C\n0}\n0").Root;
        var outer=root.Properties.Single(p=>p.Name=="Outer").Value;
        Assert.Empty(Assert.IsType<Algorithm.Alias>(outer.Properties.Single().Value).Params);
        var family=Assert.IsType<Algorithm.Conditional>(root.Properties.Single(p=>p.Name=="F").Value);
        Assert.Empty(Assert.IsType<Algorithm.Alias>(family.Branches[1].Body.Properties.Single().Value).Params);
    }

    [Theory]
    [InlineData("[[1,2],[3,4]].map({a.sum}).atoms")]
    [InlineData("filter((1,2),{x.string})")]
    public async Task CallbackMemberRowsKeepTheirInferredReceiver(string source)
    {
        var root=SourceProvenance.ParseValid(source).Root;
        var sync=Evaluator.RunFlat(new Expr.AlgorithmExpr(root));
        var asyncResult=await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root));
        if(source.StartsWith("filter"))
        {
            Assert.True(sync.IsError);Assert.True(asyncResult.IsError);
            Assert.Contains("TypeMismatch",sync.Error.ToString());Assert.Contains("TypeMismatch",asyncResult.Error.ToString());
        }
        else { Assert.False(sync.IsError);Assert.False(asyncResult.IsError);Assert.Equal(sync.Value,asyncResult.Value); }
    }

    [Fact]
    public void DetectorHasNoIndependentParameterRootedRowDecider()
        => Assert.DoesNotContain("IsParameterRootedMemberReference(",File.ReadAllText(Path.Combine(RepoRoot.Find(),"src/KatLang/ParameterDetector.cs")));
}
