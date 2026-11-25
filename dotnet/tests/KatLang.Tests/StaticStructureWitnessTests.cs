namespace KatLang.Tests;

public sealed class StaticStructureWitnessTests
{
    private static StaticScopeKey Child(StaticStructureQueries q, StaticScopeKey scope, string name)
        => q.BodyIn(scope, q.BodyOf(scope).Properties.Single(p => p.Name == name).Value);
    private static StaticStructureQueries Model(string source)
        => new(SourceProvenance.ParseSyntaxValidRoot(source), new(1_000_000, 4, 100_000, 4_000_000));

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ReceiverExpansionReturns_AreBenignCalculations_NotSelfDependentInference(bool mutual)
    {
        var middle = mutual ? "A = B.F\nB = A.F\n" : "A = A.F\n";
        var source = "F(v) = 0\nK(v) = 7\n" + middle + "P = A.x\nP(K)";
        foreach (var reversed in new[] { false, true })
        {
            var raw = SourceProvenance.ParseSyntaxValidRoot(source);
            if (reversed) raw = raw with { Properties = raw.Properties.Reverse().ToArray() };
            var q = new StaticStructureQueries(raw, new(1_000_000, 4, 100_000, 4_000_000));
            var a = Child(q, q.Root, "A");
            var p = Child(q, q.Root, "P");
            var requests = new[] { StaticQueryKey.Inputs(p), StaticQueryKey.TargetWalk(a, StaticCycleCheck.Formation) };
            foreach (var request in reversed ? requests.Reverse() : requests) q.Get(request);
            Assert.Same(a, q.Get(StaticQueryKey.TargetWalk(a, StaticCycleCheck.Formation)).Scope);
            Assert.Equal(new[] { "x" }, Assert.IsType<string[]>(q.Get(StaticQueryKey.Inputs(p)).Data));
            Assert.Equal(StaticFactKind.Yes, q.Get(StaticQueryKey.IsInput(p, "x")).Kind);
            Assert.Equal(StaticFactKind.No, q.Get(StaticQueryKey.Project(StaticQueryKind.TargetWalk, a,
                StaticQueryProjection.TargetCycle, stratum: StaticCycleCheck.None)).Kind);
        }
        var actual = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", actual.Kind);
        Assert.Equal("7", actual.Value);
    }

    [Theory]
    [InlineData("F(v)=0\nA=B.F\nB=A\n0", "B", "A")]
    [InlineData("F(v)=0\nBox={ public C=A.F\n0 }\nA=Box.C\n0", "A", "Box.C")]
    public void ReceiverReturns_PreserveTheIdentityTransportedByBarePrefixes(string source, string path, string target)
    {
        var q = Model(source);
        StaticScopeKey At(string name)
        {
            var scope = q.Root;
            foreach (var part in name.Split('.')) scope = Child(q, scope, part);
            return scope;
        }
        Assert.Same(At(target), q.Get(StaticQueryKey.TargetWalk(At(path), StaticCycleCheck.Formation)).Scope);
    }

    [Fact]
    public void AReceiverReturnAtAnAlgorithmLink_IsRuntime_NotACalculationNamespace()
    {
        var q = Model("A = A.Algorithm\nB = A\n0");
        foreach (var name in new[] { "A", "B" })
        {
            var scope = Child(q, q.Root, name);
            Assert.Equal(StaticFactKind.Runtime, q.Get(StaticQueryKey.TargetWalk(scope, StaticCycleCheck.Formation)).Kind);
            Assert.Equal(StaticFactKind.No, q.Get(StaticQueryKey.Project(StaticQueryKind.TargetWalk, scope,
                StaticQueryProjection.TargetCycle, stratum: StaticCycleCheck.None)).Kind);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void KnownOpenPresencePreventsPromotion_WhileAnotherProviderDependsOnThatDecision(bool ambiguous)
    {
        var source = "X={ public q=1\n0 }\nY={ public q=2\n0 }\nL={ public q=P.R }\nP={\nopen X," + (ambiguous ? "Y," : "")
            + "R\npublic R=C\nC={open L\nq}\nq+0\n}\n0";
        foreach (var reversed in new[] { false, true })
        {
            var q = Model(source);
            var p = Child(q, q.Root, "P");
            var keys = new[] { StaticQueryKey.OpenProviders(p, StaticCycleCheck.Formation), StaticQueryKey.IsInput(p, "q"),
                StaticQueryKey.Binding(p, "q", StaticCycleCheck.Formation) };
            foreach (var key in reversed ? keys.Reverse() : keys) q.Get(key);
            Assert.Equal(StaticFactKind.No, q.Get(keys[1]).Kind);
            Assert.Empty(Assert.IsType<string[]>(q.Get(StaticQueryKey.Inputs(p)).Data));
            Assert.Equal(ambiguous ? StaticFactKind.Ambiguous : StaticFactKind.Declaration, q.Get(keys[2]).Kind);
        }
    }

    [Theory]
    [InlineData("strata0-get")]
    [InlineData("strata0-ambiguous")]
    public void NavigatedBodiesUseTheirOwnInference_InEveryQueryDemandOrder(string name)
    {
        foreach (var reversed in new[] { false, true })
        {
            var q = Model(StaticStructureWitnessSources.Cases[name]);
            var reference = Child(q, q.Root, "Ref");
            var p = Child(q, q.Root, "P");
            var f = Child(q, q.Root, "F");
            var g = Child(q, q.Root, "G");
            var r = Child(q, g, "R");
            var requests = new[] { StaticQueryKey.Inputs(f), StaticQueryKey.TargetWalk(reference, StaticCycleCheck.Formation),
                StaticQueryKey.TargetWalk(r, StaticCycleCheck.Formation), StaticQueryKey.Inputs(p) };
            foreach (var key in reversed ? requests.Reverse() : requests) q.Get(key);
            Assert.Same(p, q.Get(StaticQueryKey.TargetWalk(reference, StaticCycleCheck.Formation)).Scope);
            Assert.Same(r, q.Get(StaticQueryKey.TargetWalk(r, StaticCycleCheck.Formation)).Scope);
            Assert.Equal(new[] { "X" }, Assert.IsType<string[]>(q.Get(StaticQueryKey.Inputs(f)).Data));
            if (name == "strata0-ambiguous")
            {
                var h = Child(q, q.Root, "H");
                Assert.Equal(StaticFactKind.Ambiguous, q.Get(StaticQueryKey.Binding(h, "Q", StaticCycleCheck.Formation)).Kind);
            }
        }
    }

    [Theory]
    [InlineData("A.3.1", "x,y")]
    [InlineData("A.3.2", "m,n")]
    [InlineData("A.3.3a", "a,b,c,y")]
    [InlineData("A.3.3b", "e,p,q")]
    public void ApprovedA1WitnessesRetainUnresolvedClassifications_IndependentOfQueryDemand(string name, string names)
    {
        StaticFactKind[]? expected = null;
        for (var pass = 0; pass < 4; pass++)
        {
            var q = Model(StaticStructureWitnessSources.Cases[name]);
            var p = Child(q, q.Root, "P");
            var candidates = names.Split(',');
            var requests = candidates.Select(n => StaticQueryKey.IsInput(p, n)).Append(StaticQueryKey.Inputs(p)).ToArray();
            foreach (var key in requests.OrderBy(k => (Array.IndexOf(requests, k) + pass) % requests.Length)) q.Get(key);
            var actual = candidates.Select(n => q.Get(StaticQueryKey.IsInput(p, n)).Kind).ToArray();
            Assert.Contains(StaticFactKind.Unknown, actual);
            Assert.Equal(StaticFactKind.Unknown, q.Get(StaticQueryKey.Inputs(p)).Kind);
            if (expected is not null) Assert.Equal(expected, actual);
            expected = actual;
        }
    }
}
