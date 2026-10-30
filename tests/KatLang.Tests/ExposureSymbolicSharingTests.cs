namespace KatLang.Tests;

public class ExposureSymbolicSharingTests
{
    [Theory]
    [InlineData(false, false, false)]
    [InlineData(false, true, false)]
    [InlineData(true, false, false)]
    [InlineData(true, true, false)]
    [InlineData(false, false, true)]
    [InlineData(false, true, true)]
    [InlineData(true, false, true)]
    [InlineData(true, true, true)]
    public void SharedWrittenMemberRead_KeepsEachSelectedOwnerAndActivation(bool firstCaptures, bool reversed, bool branch)
    {
        var read = Body(new Expr.DotCall(new Expr.Resolve("Lib"), "V", null));
        Algorithm Read() => branch ? new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.LitInt(0), read)]) : read;
        Algorithm.User Owner(bool captures) => new(null,
            captures ? [new CaptureParameterPattern("p")] : [], [],
            [new Property("Lib", new Algorithm.User(null, [], [],
                [new Property("V", Body(captures ? new Expr.Param("p") : new Expr.Num(1)), IsPublic: true)], [])),
                new Property("Read", Read(), IsPublic: true)], [branch ? Call("Read", 0) : new Expr.Resolve("Read")]);
        var first = new Property("A", Owner(firstCaptures));
        var second = new Property("B", Owner(true));
        var root = new Algorithm.User(null, [], [], reversed ? [second, first] : [first, second],
            [firstCaptures ? Call("A", 1) : branch ? new Expr.Resolve("A")
                : new Expr.DotCall(new Expr.Resolve("A"), "Read", null), Call("B", 2), Call("B", 5)]);

        var exposed = PropertyExposureResolver.Resolve(root);
        var a = Member(exposed, "A", "Read");
        var b = Member(exposed, "B", "Read");
        Assert.Equal(firstCaptures ? PropertyExposure.LocalOnlyCapturedAncestorParameters : PropertyExposure.Exported, a.Exposure);
        Assert.Equal(firstCaptures ? [new CapturedParameterRequirement("p", 0)] : [], a.CaptureRequirements);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, b.Exposure);
        Assert.Equal([new CapturedParameterRequirement("p", 0)], b.CaptureRequirements);
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(exposed));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([1m, 2m, 5m], result.Value);
    }

    [Theory]
    [InlineData(3)]
    [InlineData(6)]
    public Task DeferredSmallDiamond_PreservesTheOriginalWorkAndSelectionContract(int depth)
        => new FrontEndDagComplexityTests().Loader_ClauseFamilyDiamondOverLoad_MaterializesOnlyTheSelectedPath(depth);

    [Fact]
    public void SameWrittenBody_UnderDifferentBranchBinders_KeepsItsCapturePosition()
    {
        var shared = new Algorithm.User(null, [], [], [new Property("Captures", Body(new Expr.Param("p")))], [new Expr.Param("p")]);
        Algorithm.Conditional Family(string name) => new(null, [], [new CondBranch(new Pattern.Bind(name), shared)]);
        var root = new Algorithm.User(null, [], [], [new Property("P", Family("p")), new Property("Q", Family("q"))], []);

        var exposed = PropertyExposureResolver.Resolve(root);
        Assert.Equal(PropertyExposure.Exported, Member(exposed, "P").Exposure);
        Assert.Empty(Member(exposed, "P").CaptureRequirements!);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, Member(exposed, "Q").Exposure);
        Assert.Equal([new CapturedParameterRequirement("p", -1)], Member(exposed, "Q").CaptureRequirements);
        var p = ((Algorithm.Conditional)Member(exposed, "P").Value).Branches[0].Body;
        var q = ((Algorithm.Conditional)Member(exposed, "Q").Value).Branches[0].Body;
        Assert.NotSame(p, q);
        Assert.Equal([new CapturedParameterRequirement("p", 1)], Member(p, "Captures").CaptureRequirements);
        Assert.Equal([new CapturedParameterRequirement("p", -1)], Member(q, "Captures").CaptureRequirements);
    }

    [Theory]
    [InlineData(16, 256)]
    [InlineData(256, 16)]
    public void SharedWideSupply_IsSummarizedWithoutAnOwnerWidthProduct(int owners, int width)
    {
        var source = "G = " + string.Join(", ", Enumerable.Range(0, width).Select(i => "v" + i)) + "\n"
            + string.Concat(Enumerable.Range(0, owners).Select(i => $"A{i} = abs(G) + w{i}\n")) + "1";
        var detected = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
        Assert.Empty(detected.Diagnostics);
        var resolved = ImplicitArgumentResolver.Resolve(detected);
        var observations = new FrontEndTraversalObservations();
        var exposed = PropertyExposureResolver.Resolve(resolved, observations);
        Assert.InRange(observations.SummaryResidualNameProbes, 0, 4L * (owners + width) + 64);
        var algorithms = exposed.Properties.Skip(1).Select(property => Assert.IsType<Algorithm.User>(property.Value)).ToArray();
        Assert.Equal(owners, algorithms.Length);
        for (var i = 0; i < owners; i++) Assert.Contains("w" + i, algorithms[i].Params);
        Assert.Equal(owners, algorithms.Select(OpenProviderIdentity.DeclarationOf).Distinct(ReferenceEqualityComparer.Instance).Count());
    }

    private static Algorithm.User Body(Expr row) => new(null, [], [], [], [row]);
    private static Expr.Call Call(string name, int value) => new(new Expr.Resolve(name), [new Expr.Num(value)]);
    private static Property Member(Algorithm algorithm, params string[] path)
    {
        Property? property = null;
        foreach (var name in path)
        {
            property = Assert.Single(algorithm.Properties, candidate => candidate.Name == name);
            algorithm = property.Value;
        }
        return property!;
    }
}
