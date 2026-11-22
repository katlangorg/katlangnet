using System.Text;

namespace KatLang.Tests;

public sealed class StaticOwnerWalkTests
{
    private static string AliasChain(int depth, int names)
    {
        var source = new StringBuilder();
        for (var i = 0; i < names; i++)
            source.Append($"P{i} = {i}\n");
        for (var i = 0; i < depth; i++)
            source.Append($"B{i} = {{\n");

        // One output row per property keeps the expression depth constant as the width increases.
        for (var i = 0; i < names; i++)
            source.Append($"P{i}\n");
        for (var i = depth - 1; i >= 0; i--)
            source.Append($"}}\nB{i}\n");
        return source.ToString();
    }

    [Theory]
    [InlineData(16, 32, 544)]
    [InlineData(64, 32, 2080)]
    [InlineData(64, 128, 8320)]
    public void OwnerWalk_UsesDistinctContextualKeysAndReusesEachFinalFact(int depth, int names, int expectedKeys)
    {
        var observations = new FrontEndTraversalObservations();
        var root = SourceProvenance.ParseSyntaxValidRoot(AliasChain(depth, names));
        var detected = ParameterDetector.DetectPrevalidated(root, observations: observations);
        Assert.Empty(detected.Diagnostics);
        var operation = detected.Operation!;
        var keys = observations.StaticQueryEvaluations.Keys
            .Where(key => key.Kind == StaticQueryKind.Binding && key.Projection == StaticQueryProjection.OwnedBinding)
            .ToArray();
        Assert.Equal(expectedKeys, keys.Length);

        var deepest = keys.Where(key => key.Name == "P0").MaxBy(key => key.Scope.Depth);
        var first = operation.Read(deepest);
        var before = operation.Queries.Statistics;
        Assert.Same(first, operation.Read(deepest));
        Assert.Equal(before.Entries, operation.Queries.Statistics.Entries);
        Assert.Equal(before.Evaluations, operation.Queries.Statistics.Evaluations);
        Assert.Equal(StaticFactKind.Declaration, first.Kind);
        Assert.Same(operation.Root, first.Scope);
        Assert.Same(root.Properties.Single(property => property.Name == "P0"), first.Property);
    }

    [Fact]
    public void LoweredEnvelope_RefusesTheNestedOwnerWalkAtTheOriginalEntryBound()
    {
        var source = AliasChain(64, 64);
        Assert.Empty(Parser.Parse(source).Diagnostics);

        var options = new RunOptions { SourceProcessingLimits = new() { MaxStaticStructureBytes = 4L * 1024 * 1024 } };
        var parsed = Parser.Parse(source, options);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.StaticStructureLimitExceeded, diagnostic.Code);
        Assert.Null(diagnostic.Span);
        Assert.Equal("Static structure analysis exceeded its resource bound. The static queries exceeded their entry bound (4096). "
            + "The program exceeds the host's static-structure envelope (at most 1 GiB; a host may only lower it).", diagnostic.Message);
        Assert.Null(parsed.Root.CompletedStructure);
    }
}
