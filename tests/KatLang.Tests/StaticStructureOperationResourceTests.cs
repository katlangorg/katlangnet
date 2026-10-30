namespace KatLang.Tests;

public sealed class StaticStructureOperationResourceTests(Xunit.Abstractions.ITestOutputHelper output)
{
    private static readonly StaticQueryLimits Limits = new(2_000_000, 4, 400_000, 8_000_000);

    [Fact]
    public void SmallDeferredForksDoNotCopyEveryEagerContextOrPublication()
    {
        // Constant, already closed bodies isolate the operation/fork protocol from the unfinished consumer cutover.
        // No test-side alias/inference algorithm stands in for production behavior.
        MeasureForks(32, 2); // warm up the generic paths outside the measured comparison
        var small = MeasureForks(256, 32);
        var large = MeasureForks(4096, 32);
        output.WriteLine($"forks32 eager256: {small}; eager4096: {large}");
        Assert.True(large.ForkBytes < small.ForkBytes * 2 + 32_000,
            $"Fork allocation grew with all eager contexts: {small.ForkBytes} -> {large.ForkBytes}.");
        Assert.InRange(large.ForkBytes, 1, 2_000_000);
    }

    private (long FreezeBytes, long ForkBytes, long MaxHeapSample) MeasureForks(int size, int forks)
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot(
            string.Join('\n', Enumerable.Range(0, size).Select(i => $"P{i} = {i}")) + "\n0");
        var operation = new StaticStructureOperation(raw, Limits);
        foreach (var property in raw.Properties)
        {
            var key = operation.ContextOf(operation.Root, property.Value);
            operation.Read(StaticQueryKey.Members(key));
            operation.Publish(key, StaticPublicationStage.Detected, property.Value);
            operation.Publish(key, StaticPublicationStage.Resolved, property.Value);
        }
        operation.Publish(operation.Root, StaticPublicationStage.Detected, raw);
        operation.Publish(operation.Root, StaticPublicationStage.Resolved, raw);
        var bytes = GC.GetAllocatedBytesForCurrentThread();
        var continuation = operation.Freeze();
        var freezeBytes = GC.GetAllocatedBytesForCurrentThread() - bytes;
        var maxHeapSample = GC.GetTotalMemory(false);
        var unit = SourceProvenance.ParseSyntaxValidRoot("0");
        var pattern = new Pattern.Bind("x");
        bytes = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < forks; i++)
        {
            var fork = continuation.Materialize(operation.Root, unit, pattern, Limits);
            Assert.Equal(StaticFactKind.Inputs, fork.Read(StaticQueryKey.Inputs(fork.Root)).Kind);
            Assert.InRange(fork.Queries.LocalContextCount, 1, 2);
            Assert.Equal(1, fork.Queries.Statistics.Entries);
            maxHeapSample = Math.Max(maxHeapSample, GC.GetTotalMemory(false));
        }
        return (freezeBytes, GC.GetAllocatedBytesForCurrentThread() - bytes, maxHeapSample);
    }

    [Fact]
    public void RepeatedNestedSnapshotsPreserveExternalFactsWithoutRecopyingTheirGraph()
    {
        var raw = SourceProvenance.ParseSyntaxValidRoot("Lib = { public V = 42\n0 }\n0");
        var operation = new StaticStructureOperation(raw, Limits);
        var lib = operation.ContextOf(operation.Root, raw.Properties[0].Value);
        var fact = operation.Read(StaticQueryKey.Members(lib));
        var unit = SourceProvenance.ParseSyntaxValidRoot("V + 0");
        var pattern = new Pattern.Bind("x");
        for (var i = 0; i < 128; i++)
        {
            var body = operation.SourceOf(operation.Root);
            operation.Publish(operation.Root, StaticPublicationStage.Detected, body);
            operation.Publish(operation.Root, StaticPublicationStage.Resolved, body);
            var next = operation.Freeze().Materialize(operation.Root, unit, pattern, Limits);
            Assert.Same(fact, next.Read(StaticQueryKey.Members(lib)));
            Assert.InRange(next.Queries.LocalContextCount, 1, 2);
            operation = next;
        }
        output.WriteLine($"nested128: {operation.Queries.Statistics}; localContexts={operation.Queries.LocalContextCount}");
    }
}
