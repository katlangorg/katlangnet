namespace KatLang.Tests;

public sealed class HistoricalContractMigrationTests
{
    [Fact]
    public void Q2_DeduplicatesProviderIdentities_AndReusesTheirCompletedIndex()
    {
        foreach (var reverse in new[] { false, true })
        {
            var syntax = SourceProvenance.ParseSyntaxValidRoot("open " + (reverse ? "Other, B, A" : "A, B, Other")
                + "\nA=Lib\nB=Lib\nLib={public X=7\npublic Shared=1\nPrivate=8\n0}\nOther={public Y=9\npublic Shared=2\n0}\n0");
            var observations = new FrontEndTraversalObservations();
            var queries = new StaticStructureQueries(syntax, StaticQueryLimits.Default) { Observations = observations };
            var lib = queries.BodyIn(queries.Root, syntax.Properties.Single(property => property.Name == "Lib").Value);
            var other = queries.BodyIn(queries.Root, syntax.Properties.Single(property => property.Name == "Other").Value);
            var key = StaticQueryKey.OpenProviders(queries.Root, StaticCycleCheck.Formation);
            var providers = queries.Get(key);
            Assert.Equal(reverse ? new[] { other, lib } : new[] { lib, other }, Assert.IsType<StaticScopeKey[]>(providers.Data));
            Assert.Equal(StaticFactKind.Declaration, queries.Get(StaticQueryKey.Binding(queries.Root, "X", StaticCycleCheck.Formation)).Kind);
            Assert.Equal(StaticFactKind.Ambiguous, queries.Get(StaticQueryKey.Binding(queries.Root, "Shared", StaticCycleCheck.Formation)).Kind);
            Assert.Equal(StaticFactKind.Missing, queries.Get(StaticQueryKey.Binding(queries.Root, "Private", StaticCycleCheck.Formation)).Kind);
            var targets = observations.StaticOpenTargetEvaluations;
            var builds = observations.StaticOpenIndexBuilds;
            var visits = observations.StaticOpenIndexMemberVisits;
            Assert.True(targets > 0);
            Assert.Equal(1, builds);
            Assert.Equal(4, visits);
            for (var i = 0; i < 64; i++)
            {
                Assert.Same(providers, queries.Get(key));
                Assert.Equal(StaticFactKind.Missing, queries.Get(StaticQueryKey.Binding(queries.Root, $"absent{i}", StaticCycleCheck.Formation)).Kind);
            }
            Assert.Equal(targets, observations.StaticOpenTargetEvaluations);
            Assert.Equal(builds, observations.StaticOpenIndexBuilds);
            Assert.Equal(visits, observations.StaticOpenIndexMemberVisits);
        }
    }

    [Fact]
    public void Q3_FinalSharedTargets_DoNotEvaluateAgainForNewReaders()
    {
        var source = string.Join('\n', Enumerable.Range(0, 128).Select(i => $"A{i}=A{i + 1}")) + "\nA128={public V=7\n0}\n0";
        var syntax = SourceProvenance.ParseSyntaxValidRoot(source);
        var queries = new StaticStructureQueries(syntax, StaticQueryLimits.Default);
        var scopes = syntax.Properties.Select(property => queries.BodyIn(queries.Root, property.Value)).ToArray();
        Assert.Same(scopes[^1], queries.Get(StaticQueryKey.TargetWalk(scopes[0], StaticCycleCheck.Formation)).Scope);
        var before = queries.Statistics;
        for (var repeat = 0; repeat < 4; repeat++)
            foreach (var scope in scopes)
                Assert.Same(scopes[^1], queries.Get(StaticQueryKey.TargetWalk(scope, StaticCycleCheck.Formation)).Scope);
        Assert.Equal(before.Computations, queries.Statistics.Computations);
        Assert.Equal(before.Evaluations, queries.Statistics.Evaluations);
    }

    [Fact]
    public void OperationWorkBudget_IsTerminal_AndNeverBecomesAnUnknownAnswer()
    {
        var engine = new StaticQueryEngine<int, int>(new Chain(), limits: new(3, 4, 100, 100));
        Assert.Throws<StaticQueryLimitExceededException>(() => engine.Get(0));
        Assert.Throws<InvalidOperationException>(() => engine.Get(0));
    }

    [Fact]
    public void Cancellation_IsTerminal_AndRetainsTheOriginalToken()
    {
        using var cancellation = new CancellationTokenSource();
        var engine = new StaticQueryEngine<int, int>(new Chain(), limits: StaticQueryLimits.Default, cancellationToken: cancellation.Token);
        cancellation.Cancel();
        var error = Assert.Throws<OperationCanceledException>(() => engine.Get(0));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Throws<InvalidOperationException>(() => engine.Get(0));
    }

    private sealed class Chain : IStaticQueryDefinition<int, int>
    {
        public int Initial(int key) => 0;
        public int PathCycleValue => 2;
        public bool ValueEquals(int left, int right) => left == right;
        public bool IsRefinement(int before, int after) => before == 0 || before == after;
        public StaticQueryStep<int> Compute(int key, StaticQueryReader<int, int> reader)
            => StaticQueryStep.Complete(key < 8 ? reader.Read(key + 1) : 1);
    }
}
