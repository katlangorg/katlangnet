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
    // ── parse-gaps: pass attribution ─────────────────────────────────────────────

    /// <summary>
    /// A scripted timeline (1 tick = 1 ms): the gap route names the pass each checkpoint interval fell into, an
    /// interval that crosses a boundary by both passes, and each pass's longest stretch between its begin, its
    /// checkpoints and its end. The former fields keep their values.
    /// </summary>
    [Fact]
    public void GapRoute_NamesThePassOfEachInterval_AndEachPassesLongestStretch()
    {
        long now = 0;
        var recorder = new FrontEndMemoryProbe.CheckpointGapRecorder(() => now, 1000, () => 0);
        void At(long t, Action step) { now = t; step(); }

        At(0, recorder.Start);
        At(1, () => recorder.Stage(FrontEndPassStage.Admit, true));
        At(4, () => recorder.Stage(FrontEndPassStage.Admit, false));
        At(5, () => recorder.Stage(FrontEndPassStage.Detect, true));
        At(6, () => recorder.Checkpoint(FrontEndCancellationCheckpoint.DetectorAlgorithm, 1));
        At(8, () => recorder.Checkpoint(FrontEndCancellationCheckpoint.DetectorRow, 1));
        At(9, () => recorder.Stage("completed-publication", true)); // an in-pass stage: ignored
        At(10, () => recorder.Stage(FrontEndPassStage.Detect, false));
        At(11, () => recorder.Stage(FrontEndPassStage.Resolve, true));
        At(20, () => recorder.Checkpoint(FrontEndCancellationCheckpoint.ResolverAlgorithm, 1));
        At(21, () => recorder.Checkpoint(FrontEndCancellationCheckpoint.ResolverRow, 1));
        At(26, () => recorder.Checkpoint(FrontEndCancellationCheckpoint.ResolverRow, 2));
        At(27, () => recorder.Stage(FrontEndPassStage.Resolve, false));
        At(28, () => recorder.Stage(FrontEndPassStage.Exposure, true)); // throws: no end is reported
        At(30, () => recorder.Checkpoint(FrontEndCancellationCheckpoint.ExposureAlgorithm, 1));
        At(33, recorder.End);

        var facts = recorder.Format(checkpoints: 6, diagnostics: 0);

        Assert.StartsWith(
            "checkpoints=6 totalMs=33.0 startToFirstMs=6.0 lastToEndMs=3.0 maxGapMs=12.00 maxAfter=DetectorRow#1 "
            + "DetectorAlgorithm=1/2.00ms#1gen2+0 DetectorRow=1/12.00ms#1gen2+0 ResolverAlgorithm=1/1.00ms#1gen2+0 ResolverRow=2/5.00ms#1gen2+0 ExposureAlgorithm=1/0.00ms#0gen2+0 "
            + "maxGapPass=detect>resolve ",
            facts);
        Assert.Contains(" DetectorAlgorithm.pass=detect DetectorRow.pass=detect>resolve ResolverAlgorithm.pass=resolve ResolverRow.pass=resolve ", facts);
        Assert.Contains(" pass.admit=1x/3.0ms/0cp/max3.00ms@begin ", facts);
        Assert.Contains(" pass.detect=1x/5.0ms/2cp/max2.00ms@DetectorAlgorithm#1 ", facts);
        Assert.Contains(" pass.resolve=1x/16.0ms/3cp/max9.00ms@begin ", facts);
        Assert.Contains(" pass.exposure=1x/5.0ms/1cp/max3.00ms@ExposureAlgorithm#1 ", facts);
        Assert.EndsWith(" diags=0", facts);
    }
    /// <summary>The observed pipeline reports every pass's begin and end, in order; a graph without opens skips the provider rule.</summary>
    [Theory]
    [InlineData("F(x) = x + 1\nF(2)", false)]
    [InlineData("L = { public V = 1 }\nM = { open L\nV }\nM", true)]
    public void ObservedParse_ReportsEachPassBoundary_InPipelineOrder(string source, bool hasOpens)
    {
        var stages = new List<string>();
        var observations = new FrontEndTraversalObservations
        {
            StageObserver = (stage, begin) => { if (FrontEndPassStage.IsPass(stage)) stages.Add((begin ? "+" : "-") + stage["pass:".Length..]); },
        };
        Assert.Empty(Parser.ParseObserved(source, options: null, observations).Diagnostics);

        string[] passes = hasOpens
            ? ["admit", "detect", "resolve", "collisions", "open-providers", "outputs", "exposure"]
            : ["admit", "detect", "resolve", "collisions", "outputs", "exposure"];
        Assert.Equal(passes.SelectMany(static pass => new[] { "+" + pass, "-" + pass }), stages);
    }
}
