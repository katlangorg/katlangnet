using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

public class LiftedParameterOwnershipTests
{
    public static TheoryData<string, string, string, string> Programs => new()
    {
        // A generated v(x) must revert to the written value reference when v becomes bound.
        { "v = x + 99\nOuter = { Inner = v\nNeed(v) = v\nInner + Need }\nOuter(2, 7)", "x,v", "x", "14" },
        { "v = x + 99\nOuter = { Inner = v\nNeed((v, w)) = v + w\nInner + Need }\nOuter(2, (7, 3))", "x,v,w", "x", "17" },
        { "v = 99\nNeed(*v) = v.count\nOuter = { Inner = v.count\nInner + Need }\nOuter(7, 8)", "v", "", "4" },
        // Written call arguments survive; only the callee binding changes.
        { "v(x) = 99\nNeed(v) = 0\nOuter = { Inner = v(1)\nInner + Need }\nOuter({x + 1})", "v", "", "2" },
        { "v = { Member = 99 }\nMember(x) = x + 1\nNeed(v) = 0\nOuter = { Inner = v.Member\nInner + Need }\nOuter(7)", "v", "", "8" },
        // The completed owner also satisfies an earlier closed branch/explicit body.
        { "Need(v) = v\nOuter = { F(0) = 0\nF(n) = v\nF(1) + Need }\nOuter(7)", "v", "", "14" },
        { "v = x + 1\nNeed(v) = 0\nOuter = { Inner(q) = Math.Abs(v)\nInner(0) + Need }\nOuter(7)", "v", "q", "7" },
        // abs now denotes Apply: its argument is neutral and must remain callable X,
        // rather than the X(x) synthesized for the original strict builtin consumer.
        { "X = x + 1\nNeed(abs) = 0\nApply(f) = f(7)\nOuter = { Inner = abs(X)\nInner + Need }\nOuter(0, Apply)", "x,abs", "x", "8" },
    };

    [Theory]
    [MemberData(nameof(Programs))]
    public async Task CompletedBindings_RebuildForwardingAndDiagnostics_WithSignaturesPreserved(
        string source, string outerParameters, string innerParameters, string expected)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var outer = root.Properties.Single(p => p.Name == "Outer").Value;
        Assert.Equal(outerParameters, string.Join(",", outer.Params));
        if (outerParameters == "x,v,w")
            Assert.IsType<SequenceValueParameterPattern>(outer.ParameterPatterns[1]);
        if (source.Contains("Need(*v)", StringComparison.Ordinal))
            Assert.Equal(ParameterKind.Collecting, Assert.IsType<CaptureParameterPattern>(Assert.Single(outer.ParameterPatterns)).Kind);
        var inner = outer.Properties.SingleOrDefault(p => p.Name == "Inner");
        if (inner is not null)
            Assert.Equal(innerParameters, string.Join(",", inner.Value.Params));

        var ast = new Expr.AlgorithmExpr(root);
        var expectedOutcome = $"ok raw={expected} n=1";
        Assert.Equal(expectedOutcome, AsyncEvaluationHarness.NeutralOf(Evaluator.RunCounted(ast)));
        Assert.Equal(expectedOutcome, AsyncEvaluationHarness.NeutralOf(
            Evaluator.RunCountedObserved(ast, enableOptimizations: false).Item1));
        Assert.Equal(expectedOutcome, AsyncEvaluationHarness.NeutralOf(
            await AsyncEvaluationHarness.Complete(Evaluator.RunCountedAsync(ast, new PassThroughAsyncZeroArgPropertyResultCache()))));

        // Binding shape matters independently of the resulting value.
        if (outerParameters == "x,v")
            Assert.Equal("v", Assert.IsType<Expr.Param>(Assert.Single(inner!.Value.Output)).Name);
        if (outerParameters == "x,abs")
        {
            var call = Assert.IsType<Expr.Call>(Assert.Single(inner!.Value.Output));
            Assert.Equal("abs", Assert.IsType<Expr.Param>(call.Function).Name);
            Assert.Equal("X", Assert.IsType<Expr.Resolve>(Assert.Single(call.Args)).Name);
        }
    }

    [Fact]
    public void Completion_KeepsSharedNodesWithinTheirOwnerRegion()
    {
        var syntax = SourceProvenance.ParseSyntaxValidRoot(
            "v = 99\nOuter = { Left = v\nRight = v\nNeed(v) = 0\nLeft + Right + Need }\nOther = v\nOuter(7), Other");
        var outerProperty = syntax.Properties.Single(p => p.Name == "Outer");
        var shared = outerProperty.Value.Properties.Single(p => p.Name == "Left").Value;
        var outer = outerProperty.Value with
        {
            Properties = outerProperty.Value.Properties.Select(p => p.Name == "Right" ? p.WithValue(shared) : p).ToList(),
        };
        var input = syntax with
        {
            Properties = syntax.Properties.Select(p => p.Name == "Outer" ? p.WithValue(outer)
                : p.Name == "Other" ? p.WithValue(shared) : p).ToList(),
        };
        for (var analysis = 0; analysis < 2; analysis++)
        {
            var detected = ParameterDetector.DetectPrevalidated(input);
            Assert.Empty(detected.Diagnostics);
            var origins = new ImplicitArgumentResolver.ResolutionOrigins();
            var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected.Root, origins: origins);
            Assert.True(origins.HasLiftedParameters);
            var observations = new FrontEndTraversalObservations();
            var completed = ParameterDetector.CompleteOwnership(resolved, origins, observations: observations);
            Assert.True(completed.Changed);
            Assert.Empty(completed.Diagnostics);
            Assert.True(observations.DetectorRewriteExpansions > 0);
            var completedOuter = completed.Root.Properties.Single(p => p.Name == "Outer").Value;
            var left = completedOuter.Properties.Single(p => p.Name == "Left").Value;
            Assert.Same(left, completedOuter.Properties.Single(p => p.Name == "Right").Value);
            Assert.IsType<Expr.Param>(Assert.Single(left.Output));
            Assert.IsType<Expr.Resolve>(Assert.Single(completed.Root.Properties.Single(p => p.Name == "Other").Value.Output));
            var final = ImplicitArgumentResolver.ResolvePrevalidated(completed.Root, preserveSignatures: true);
            Assert.Equal("ok raw=S[14, 99] n=2", AsyncEvaluationHarness.NeutralOf(Evaluator.RunCounted(new Expr.AlgorithmExpr(final))));
        }
        Assert.IsType<Expr.Resolve>(Assert.Single(shared.Output));
    }
}
