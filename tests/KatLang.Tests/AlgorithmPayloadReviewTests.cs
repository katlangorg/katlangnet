namespace KatLang.Tests;

public class AlgorithmPayloadReviewTests
{
    [Fact]
    public void WithParameters_NonUserIdentity_DoesNotAllocateDiscardedPatterns()
    {
        Algorithm[] algorithms =
        [
            new Algorithm.Builtin(BuiltinId.count),
            new Algorithm.Conditional(null, [], []),
        ];
        ParameterDeclaration[] parameters = [new("x"), new("y")];
        foreach (var algorithm in algorithms)
            Assert.Same(algorithm, algorithm.WithParameters(parameters));

        var before = GC.GetAllocatedBytesForCurrentThread();
        for (var index = 0; index < 1000; index++)
            foreach (var algorithm in algorithms)
                _ = algorithm.WithParameters(parameters);
        Assert.Equal(0L, GC.GetAllocatedBytesForCurrentThread() - before);
    }

    [Fact]
    public void WithParams_RepeatedCaptureNames_UsesFirstDeclarationLikeLean()
    {
        var first = new ParameterDeclaration("x", new SourceSpan(1, 1, 1, 1), ParameterKind.Collecting);
        var second = new ParameterDeclaration("x", new SourceSpan(2, 1, 2, 1));
        var user = new Algorithm.User(null,
            [new SequenceValueParameterPattern([first.ToPattern(), second.ToPattern()])],
            [], [], [new Expr.Num(1)]);

        // Lean parameterForName? is a first-match search, not a uniqueness assertion.
        var shortened = Assert.IsType<Algorithm.User>(user.WithParams(["x"]));
        Assert.Same(first, Assert.Single(shortened.Parameters));
        Assert.Equal(ParameterKind.Collecting, Assert.Single(shortened.Parameters).Kind);
        Assert.Same(user.Declaration, shortened.Declaration);
        Assert.Empty(Assert.IsType<Algorithm.User>(user.WithParams([])).ParameterPatterns);
        var reordered = Assert.IsType<Algorithm.User>(user.WithParams(["new", "x"]));
        Assert.Equal(["new", "x"], reordered.Params);
        Assert.Same(first, reordered.Parameters[1]);
        Assert.Equal(2, user.ParameterCount);
    }

    [Fact]
    public void ConditionalBranchBody_StillElaboratesItsOwnedOpens()
    {
        var provider = new Algorithm.User(null, [], [],
            [new Property("P", new Algorithm.User(null, [], [], [], [new Expr.Resolve("input")]), IsPublic: true)],
            [new Expr.Num(1)]);
        var nested = new Algorithm.Conditional(null,
            [new Expr.Grace(new Expr.AlgorithmExpr(provider), 1), new Expr.Resolve("x")],
            []);
        var outer = new Algorithm.Conditional(null, [],
            [new CondBranch(new Pattern.Bind("x"), nested)]);

        var (detected, diagnostics) = ParameterDetector.Detect(outer);
        var body = Assert.IsType<Algorithm.Conditional>(
            Assert.Single(Assert.IsType<Algorithm.Conditional>(detected).Branches).Body);
        Assert.Same(nested.Declaration, body.Declaration);
        Assert.Same(nested.Branches, body.Branches);
        var processedProvider = Assert.IsType<Algorithm.User>(
            Assert.IsType<Expr.AlgorithmExpr>(body.Opens[0]).Algorithm);
        Assert.Equal(["input"], Assert.IsType<Algorithm.User>(
            Assert.Single(processedProvider.Properties).Value).Params);
        Assert.Equal("x", Assert.IsType<Expr.Param>(body.Opens[1]).Name);
        Assert.Contains(diagnostics, d => d.Code == DiagnosticCode.OpenTargetIsParameter);
    }

    [Fact]
    public void ExplicitEmptyHostList_RemainsClosed_WhileAbsentListInfers()
    {
        var body = new Algorithm.User(null, [], [], [], [new Expr.Resolve("missing")]);
        var written = Assert.IsType<Algorithm.User>(
            Algorithm.ElaborateClauseDefinition(new Pattern.SequenceValue([]), body));
        Assert.True(written.HasExplicitParameterList);
        Assert.Empty(written.Parameters);
        Assert.False(body.HasExplicitParameterList);
        Assert.NotEqual(body, written);

        var (closed, diagnostics) = ParameterDetector.Detect(written);
        Assert.Empty(Assert.IsType<Algorithm.User>(closed).Parameters);
        Assert.Contains(diagnostics, d => d.Code == DiagnosticCode.UndeclaredIdentifier);
        var (inferred, _) = ParameterDetector.Detect(body);
        Assert.Equal(["missing"], Assert.IsType<Algorithm.User>(inferred).Params);
        Assert.True(CallableSignature.FromUserAlgorithm("F", written).HasExplicitParameterList);
        Assert.False(CallableSignature.FromUserAlgorithm("F", body).HasExplicitParameterList);
        Assert.True(Parser.Parse("F() = 1").HasErrors);
    }
}
