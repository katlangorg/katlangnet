using KatLang.ParserFuzz;

namespace KatLang.Tests;

public class FrontEndMemoryProbeTests
{
    private sealed class InlineRoot
    {
        public (object Left, object Right) Payload;
        public object? Collection;
    }

    [Theory]
    [InlineData("--repeat", "0")]
    [InlineData("--sizes", "")]
    [InlineData("--mode", "unknown")]
    public void Parent_RejectsEmptyOrInvalidCampaigns(string option, string value)
        => Assert.Equal(2, FrontEndMemoryProbe.RunParent(["fe-mem", option, value]));

    [Fact]
    public void Census_FollowsInlineDictionaryEntryReferences_WithoutCountingBoxes()
    {
        var first = new string('a', 3);
        var second = new string('b', 3);
        var shared = new object();
        var inlineOnly = new object();
        var dictionary = new Dictionary<string, object> { [first] = shared, [second] = shared };

        var census = FrontEndMemoryProbe.GraphCensus.Of(new InlineRoot
        {
            Payload = (inlineOnly, shared),
            Collection = dictionary,
        });

        Assert.Contains(first, census.Nodes);
        Assert.Contains(second, census.Nodes);
        Assert.Contains(shared, census.Nodes);
        Assert.Contains(inlineOnly, census.Nodes);
        Assert.Equal(1, census.Nodes.Count(node => ReferenceEquals(node, shared)));
        Assert.DoesNotContain(census.Nodes, node => node.GetType().IsValueType);
        Assert.True(census.ArraySlots >= dictionary.Count);
    }

    [Fact]
    public void RequirementOracle_IncludesPropertiesInOutputBlocks()
    {
        var root = SourceProvenance.ParseValid("F(x) = x + {\nP = x\nP\n}\n1").Root;

        var fingerprint = FrontEndMemoryProbe.RequirementFingerprint(root);

        Assert.Contains("property1:P", fingerprint);
        Assert.Contains("req[1:x]", fingerprint);
        Assert.Contains("cap[", fingerprint);
    }

    [Fact]
    public void RequirementOracle_IncludesAliasTargets()
    {
        var first = SourceProvenance.ParseValid("F(x) = x + 1\nG(x) = x + 2\nA = F\n1").Root;
        var second = SourceProvenance.ParseValid("F(x) = x + 1\nG(x) = x + 2\nA = G\n1").Root;
        Assert.IsType<Algorithm.Alias>(first.Properties.Single(property => property.Name == "A").Value);

        Assert.NotEqual(FrontEndMemoryProbe.RequirementFingerprint(first), FrontEndMemoryProbe.RequirementFingerprint(second));
    }

    [Fact]
    public void ValueOracle_DistinguishesRenderedTextCollisionsAndCollectionKinds()
    {
        Result[] values =
        [
            new Result.Str("[1, 2]"),
            new Result.ListValue([new Result.Atom(1), new Result.Atom(2)]),
            new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2)]),
            new Result.ListValue([new Result.Str("a, b"), new Result.Str("c")]),
            new Result.ListValue([new Result.Str("a"), new Result.Str("b, c")]),
            new Result.Str("true"), new Result.Bool(true),
            new Result.Str("1"), new Result.Atom(1),
            new Result.ListValue([]), new Result.SequenceValue([]),
        ];

        Assert.Equal(values.Length, values.Select(FrontEndMemoryProbe.ValueFingerprint).Distinct().Count());
    }

    [Fact]
    public void FaithfulValidShape_RefusesRecoveryDiagnostics_WhileMalformedModeAllowsThem()
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics("@");
        Assert.NotEmpty(parsed.Diagnostics);

        Assert.Throws<InvalidOperationException>(() => FrontEndMemoryProbe.RequireClean(parsed.Diagnostics, required: true));
        FrontEndMemoryProbe.RequireClean(parsed.Diagnostics, required: false);
        FrontEndMemoryProbe.RequireClean(SourceProvenance.ParseValid("1").Diagnostics, required: true);
    }
}
