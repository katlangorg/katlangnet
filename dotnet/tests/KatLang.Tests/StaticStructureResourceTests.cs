namespace KatLang.Tests;

public sealed class StaticStructureResourceTests(Xunit.Abstractions.ITestOutputHelper output)
{
    [Theory]
    [InlineData(64)]
    [InlineData(256)]
    [InlineData(1024)]
    [InlineData(4096)]
    public void FlatReferenceChains_ShareAllThreeStrata_WithBoundedWork(int size)
    {
        var source = string.Join('\n', Enumerable.Range(0, size).Select(i => $"A{i} = A{i + 1}")) + $"\nA{size} = 42\n0";
        var root = SourceProvenance.ParseSyntaxValidRoot(source);
        var before = GC.GetAllocatedBytesForCurrentThread();
        var q = new StaticStructureQueries(root, new(1000L * size, 4, 200 * size + 2000, 4000L * size));
        var first = q.BodyIn(q.Root, root.Properties[0].Value);
        var last = q.BodyIn(q.Root, root.Properties[^1].Value);
        Assert.Same(last, q.Get(StaticQueryKey.TargetWalk(first, StaticCycleCheck.Formation)).Scope);
        var statistics = q.Statistics;
        var bytes = GC.GetAllocatedBytesForCurrentThread() - before;
        output.WriteLine($"references {size}: {statistics}; allocated={bytes}");
        Assert.InRange(statistics.Evaluations, 1, 500L * size + 2000);
        Assert.InRange(statistics.Reads, 1, 1000L * size + 2000);
        Assert.InRange(statistics.Entries, 1, 120 * size + 2000);
    }

    [Theory]
    [InlineData(128)]
    [InlineData(512)]
    [InlineData(2048)]
    public void WideBalancedInputBodies_UseSharedDecisionAndActivationAggregates(int size)
    {
        var nodes = Enumerable.Range(0, size).Select(i => (Expr)new Expr.Resolve($"n{i}")).ToList();
        while (nodes.Count > 1)
            nodes = Enumerable.Range(0, (nodes.Count + 1) / 2).Select(i => 2 * i + 1 < nodes.Count
                ? (Expr)new Expr.Binary(BinaryOp.Add, nodes[2 * i], nodes[2 * i + 1]) : nodes[2 * i]).ToList();
        var body = new Algorithm.User(null, [], [], [], nodes);
        var root = new Algorithm.User(null, [], [], [new Property("P", body)], []);
        var before = GC.GetAllocatedBytesForCurrentThread();
        var q = new StaticStructureQueries(root, new(1000L * size, 4, 200 * size + 2000, 4000L * size));
        var scope = q.BodyIn(q.Root, body);
        var signature = Assert.IsType<string[]>(q.Get(StaticQueryKey.Inputs(scope)).Data);
        Assert.Equal(Enumerable.Range(0, size).Select(i => $"n{i}"), signature);
        var statistics = q.Statistics;
        output.WriteLine($"inputs {size}: {statistics}; allocated={GC.GetAllocatedBytesForCurrentThread() - before}");
        Assert.InRange(statistics.Reads, 1, 1000L * size + 2000);
    }

    [Fact]
    public void ASharedGraceDag_PreservesExponentialOccurrenceCounts_WithoutExpandingPaths()
    {
        Expr shared = new Expr.Grace(new Expr.Resolve("a"), 1);
        for (var depth = 0; depth < 1000; depth++) shared = new Expr.Binary(BinaryOp.Add, shared, shared);
        var body = new Algorithm.User(null, [], [], [], [new Expr.Binary(BinaryOp.Add, shared, new Expr.Resolve("b"))]);
        var root = new Algorithm.User(null, [], [], [new Property("P", body)], []);
        var q = new StaticStructureQueries(root, new(2_000_000, 4, 200_000, 4_000_000));
        var scope = q.BodyIn(q.Root, body);
        Assert.Equal(new[] { "b", "a" }, Assert.IsType<string[]>(q.Get(StaticQueryKey.Inputs(scope)).Data));
        Assert.InRange(q.Statistics.Entries, 1, 20_000);
        Assert.InRange(q.Statistics.Reads, 1, 100_000);
    }

    [Fact]
    public void ABodySharedAcrossContexts_SharesItsPureMemberIndex()
    {
        var source = string.Join('\n', Enumerable.Range(0, 2048).Select(i => $"public V{i} = {i}")) + "\n0";
        var shared = SourceProvenance.ParseSyntaxValidRoot(source);
        var root = new Algorithm.User(null, [], [], [], []);
        var q = new StaticStructureQueries(root, new(1_000_000, 4, 100_000, 4_000_000));
        object? members = null;
        for (var i = 0; i < 128; i++)
        {
            var parent = q.BodyIn(q.Root, new Algorithm.User(null, [], [], [], []));
            var body = q.BodyIn(parent, shared);
            var current = q.Get(StaticQueryKey.Members(body)).Data;
            if (members is not null) Assert.Same(members, current);
            members = current;
        }
        Assert.Equal(128, q.Statistics.Entries);
    }

    [Theory]
    [InlineData(64)]
    [InlineData(256)]
    [InlineData(1024)]
    public void WideOpensOverStaggeredSharedReferenceTails_DoNotRescanTheProviderList(int size)
    {
        var source = string.Join('\n', Enumerable.Range(0, size).Select(i => $"R{i}=R{i + 1}"))
            + $"\nR{size}={{public V=42\n0}}\nP={{open "
            + string.Join(',', Enumerable.Range(0, size).Select(i => $"R{i}")) + "\nV+0}\n0";
        var root = SourceProvenance.ParseSyntaxValidRoot(source);
        var before = GC.GetAllocatedBytesForCurrentThread();
        var q = new StaticStructureQueries(root, new(2000L * size, 4, 500 * size + 2000, 4000L * size));
        var p = q.BodyIn(q.Root, root.Properties.Single(p => p.Name == "P").Value);
        var target = q.BodyIn(q.Root, root.Properties.Single(p => p.Name == $"R{size}").Value);
        var providers = Assert.IsType<StaticScopeKey[]>(q.Get(StaticQueryKey.OpenProviders(p, StaticCycleCheck.Formation)).Data);
        Assert.Same(target, Assert.Single(providers));
        output.WriteLine($"opens {size}: {q.Statistics}; allocated={GC.GetAllocatedBytesForCurrentThread() - before}");
        Assert.InRange(q.Statistics.Reads, 1, 1000L * size + 2000);
    }
}
