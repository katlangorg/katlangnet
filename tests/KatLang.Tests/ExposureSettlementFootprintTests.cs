using System.Text;
using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests;

using BoundOwnerEmptiness = PropertyExposureResolver.BoundOwnerEmptiness;
using Mode = PropertyExposureResolver.SettlementShareMode;
using SettlementShare = PropertyExposureResolver.SettlementShare;
using SummaryScope = PropertyExposureResolver.SummaryScope;

/// <summary>
/// SETTLEMENT FOOTPRINTS (<c>PropertyExposureResolver.SettlementShare</c>, C# implementation only; Lean models no
/// exposure analysis): a completed settlement records every bound-owner membership it read, with the answer, and the
/// share answers a later settlement of the same content and level under OTHER bound owners when they give the same
/// answers. Bound owners a settlement never read cannot take part in any of its decisions, so chains whose links each
/// bind one more owner are settled in linear frames instead of quadratic or exponential ones
/// (<see cref="ExposureSettlementShareTests"/>, <see cref="ExposureSettlementFrameChargeTests"/>).
///
/// <para>The oracles are exact published metadata against the former exact-key share and against no share at all
/// (<see cref="PropertyExposureResolver.SettlementShareModeForTesting"/>), and deterministic work counters, never time.
/// The witnesses of each rule were found by mutation over about 41,600 test-literal and generated programs (November
/// 17 2026): ignoring footprints changes the <c>Outer.Mid.X</c> and <c>ref-in-mid</c> programs; dropping what nested
/// frames read, or subtracting inherited owners as if a child bound them, changes the nested-read programs below;
/// sharing settlements with an off-chain owner lookup under other owners changes the re-entry programs; leaking the
/// unbound open-walks settlement's reads into its reader fails loudly in the C1 programs. The emptiness read of the
/// open-walks route has no witness: C1 makes both of its routes give the same set, and the read only keeps it
/// conservative.</para>
/// </summary>
public sealed class ExposureSettlementFootprintTests
{
    // ── Harness ─────────────────────────────────────────────────────────────

    private static T InMode<T>(Mode mode, Func<T> work)
    {
        var previous = PropertyExposureResolver.SettlementShareModeForTesting.Value;
        PropertyExposureResolver.SettlementShareModeForTesting.Value = mode;
        try { return work(); }
        finally { PropertyExposureResolver.SettlementShareModeForTesting.Value = previous; }
    }

    /// <summary>The eager parse of <paramref name="source"/> in <paramref name="mode"/>: its diagnostics and every property's metadata.</summary>
    private static (string Diagnostics, string Metadata, FrontEndTraversalObservations Observations) Parse(string source, Mode mode)
    {
        var observations = new FrontEndTraversalObservations();
        var parsed = InMode(mode, () => Parser.ParseObserved(source, options: null, observations));
        var diagnostics = string.Join("\n", parsed.Diagnostics.Select(d => $"{d.Code}/{d.Severity}@{d.Span}: {d.Message}"));
        return (diagnostics, ExposureSettlementFrameChargeTests.Metadata(parsed.Root), observations);
    }

    private static void AssertModesAgree(string source, bool includeUnshared = true)
    {
        var footprint = Parse(source, Mode.Footprint);
        Assert.Equal("", footprint.Diagnostics);
        var exact = Parse(source, Mode.ExactBoundOwners);
        Assert.Equal(exact.Diagnostics, footprint.Diagnostics);
        Assert.Equal(exact.Metadata, footprint.Metadata);
        if (!includeUnshared)
            return;
        var unshared = Parse(source, Mode.Unshared);
        Assert.Equal(unshared.Diagnostics, footprint.Diagnostics);
        Assert.Equal(unshared.Metadata, footprint.Metadata);
    }

    /// <summary>The branching chain: each link's member calls the members of the TWO links below.</summary>
    internal static string BranchingLines(int length, string indent = "", string terminal = "x + 1")
    {
        var source = new StringBuilder();
        source.Append(indent).Append($"P0 = {{ public A(x) = {terminal} }}\n");
        source.Append(indent).Append("P1 = { public A(x) = P0.A(1) + 1 }\n");
        for (var i = 2; i <= length; i++)
            source.Append(indent).Append($"P{i} = {{ public A(x) = P{i - 1}.A(1) + P{i - 2}.A(1) }}\n");
        return source.ToString();
    }

    /// <summary>
    /// The branching chain inside <paramref name="owners"/> nested owners <c>O{j}(p{j})</c>, whose parameters the first
    /// link's member reads all: every settlement that reaches it reads one membership per owner. Past
    /// <see cref="SettlementShare.MaxFootprint"/> owners its footprint is unknown and the exact keys serve it.
    /// </summary>
    internal static string NestedOwnerBranchingChain(int owners, int length)
        => NestedOwnerBranchingDeclaration(owners, length) + "O1(1)\n";

    /// <summary>The declaration <c>O1(p1) = { … }</c> of <see cref="NestedOwnerBranchingChain"/>, at <paramref name="indent"/>.</summary>
    internal static string NestedOwnerBranchingDeclaration(int owners, int length, string indent = "")
    {
        var source = new StringBuilder();
        for (var j = 1; j <= owners; j++)
            source.Append(indent).Append(new string(' ', 4 * (j - 1))).Append($"O{j}(p{j}) = {{\n");
        var inner = indent + new string(' ', 4 * owners);
        source.Append(BranchingLines(length, inner, "x" + string.Concat(Enumerable.Range(1, owners).Select(j => $" + p{j}"))));
        source.Append(inner).Append($"P{length}.A(1)\n");
        for (var j = owners; j >= 1; j--)
        {
            source.Append(indent).Append(new string(' ', 4 * (j - 1))).Append("}\n");
            if (j > 1)
                source.Append(indent).Append(new string(' ', 4 * (j - 1))).Append($"O{j}({j})\n");
        }

        return source.ToString();
    }

    // ── The witnesses of a relevant bound owner ─────────────────────────────

    /// <summary>
    /// A member of <c>Mid(n)</c> read back through <c>Outer.Mid</c> from inside <c>Mid</c>. The escaping reference is
    /// bound by <c>Mid</c>, so where <c>Mid</c>'s own summary settles it, <c>X</c>'s requirement <c>n</c> is supplied;
    /// where <c>Read</c>'s level settles the same member, <c>Mid</c> is not bound and the requirement is charged. The
    /// member's settlement read <c>Mid</c> both times, present and then absent: the footprint keeps them apart. In
    /// <c>Outer.Mid.X</c> the read is the reused settlement's own; in the others it is one, two or three frames below.
    /// </summary>
    public static TheoryData<string, string, string[]> RelevantOwnerPrograms() => new()
    {
        { "Outer(n) = {\n Mid(n) = { public X = n\n Read = Outer.Mid.X\n Read }\n Mid(7)\n}\nOuter(5)", "7", ["X", "Read"] },
        { "Outer(n) = {\n    Mid(n) = {\n        public X = n\n        public Y = Outer.Mid.X\n        Read = Outer.Mid.Y\n        Read\n    }\n    Mid(7)\n}\nOuter(5)", "7", ["X", "Y", "Read"] },
        { "Outer(n) = {\n    Mid(n) = {\n        public X = n\n        public Y = Outer.Mid.X + 1\n        public Z = Outer.Mid.Y + 1\n        Read = Outer.Mid.Z\n        Read\n    }\n    Mid(7)\n}\nOuter(5)", "9", ["X", "Y", "Z", "Read"] },
        { "Outer(n) = {\n    Mid(n) = {\n        public X = n\n        public Y(k) = Outer.Mid.X + k\n        Read = Outer.Mid.Y(1)\n        Read\n    }\n    Mid(7)\n}\nOuter(5)", "8", ["X", "Y", "Read"] },
    };

    /// <summary>
    /// Adding the relevant bound owner changes the answer: under <c>Mid</c> the member charges nothing (so <c>Mid</c> is
    /// exported from <c>Outer</c>), without it every reader inside <c>Mid</c> requires <c>Mid</c>'s own <c>n</c>. A
    /// settlement kept under the first is refused under the second by its footprint, and the metadata are exactly
    /// those of the exact-key share and of no share.
    /// </summary>
    [Theory]
    [MemberData(nameof(RelevantOwnerPrograms))]
    public void ARelevantBoundOwner_ChangesTheAnswer_AndItsFootprintKeepsTheTwoApart(string source, string value, string[] readers)
    {
        AssertModesAgree(source);
        var (_, _, observations) = Parse(source, Mode.Footprint);
        var root = Assert.IsType<Algorithm.User>(SourceProvenance.ParseValid(source).Root);
        var outer = ExposureOpenChainComplexityTests.Member(root, "Outer").Value;
        ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(outer, "Mid"));
        foreach (var reader in readers)
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(outer, "Mid", reader), ("n", 0));

        // Some kept settlement was answered under other bound owners, and one was refused by a membership it read.
        Assert.True(observations.SettlementShareCandidateHits > 0);
        Assert.True(observations.SettlementShareCandidateVisits > observations.SettlementShareCandidateHits);
        Assert.Equal(value, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }

    /// <summary>
    /// Two owners with the same parameter spelling around the same nested-read shape, plus a third block that reads
    /// both: every requirement keeps its own owner's identity, whichever footprints the share holds.
    /// </summary>
    [Fact]
    public void SameNamedParametersOfDistinctOwners_KeepDistinctFootprints()
    {
        static string Owner(string name)
            => $"{name}(n) = {{\n    Mid(n) = {{\n        public X = n\n        public Y = {name}.Mid.X\n        Read = {name}.Mid.Y\n        Read\n    }}\n    Mid(7)\n}}\n";
        var source = Owner("O") + Owner("Q") + "O(5) + Q(6)";
        AssertModesAgree(source);
        var root = Assert.IsType<Algorithm.User>(SourceProvenance.ParseValid(source).Root);
        foreach (var name in new[] { "O", "Q" })
        {
            var owner = ExposureOpenChainComplexityTests.Member(root, name).Value;
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, "Mid"));
            foreach (var reader in new[] { "X", "Y", "Read" })
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, "Mid", reader), ("n", 0));
        }

        Assert.Equal("14", Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }

    /// <summary>
    /// A requirement whose owner is on no level of its site's chain charges nothing there (Q1) and raises no landing,
    /// so its settlement is kept for its exact key, from any site, as before footprints. Such a settlement is never
    /// answered under other bound owners: here <c>K.M</c>'s member <c>G</c> is settled from <c>K</c> first and then
    /// reached from <c>F</c>, where the owner <c>F</c> is on the chain. Each program publishes exactly the metadata of
    /// the exact-key share, also where that share's answer is not the unshared one (see the follow-up in the settlement
    /// design notes); the re-entry programs are the witnesses.
    /// </summary>
    [Theory]
    [InlineData("K = { public M(z) = F.G + z }\nF(x) = {\n    public G = x + 1\n    public H = K.M(1)\n    0\n}\nF(5).G")]
    [InlineData("F(x) = {\n    public G = x + 1\n    public H(y) = K.M(1) + y\n    0\n}\nK = { public M(z) = F.G + z }\nF(5).G")]
    [InlineData("F(x) = {\n    public G = x + 1\n    public H(y) = F.G + y\n    public H3(y) = F.G + y\n    0\n}\nK = { public M(z) = F.G + z }\nF(5).H3(1)")]
    [InlineData("F(x) = {\n    public G = x + 1\n    public H(y) = F.G + y\n    public H3(y) = K.M(1) + y\n    0\n}\nK = { public M(z) = F.G + z }\nF(5).H3(1)")]
    [InlineData("F(x) = {\n    public G = x + 1\n    public H(y) = F.G + y\n    0\n}\nK = { public M(z) = F.G + z }\nF(5).H(1)")]
    [InlineData("Outer(n) = {\n    Mid(n) = {\n        public X = n\n        public Y = Hop.V\n        Read = Outer.Mid.Y\n        Read\n    }\n    Hop = { public V = Outer.Mid.X }\n    Mid(7)\n}\nOuter(5)")]
    public void ASettlementWithAnOffChainOwner_IsAnsweredForItsExactBoundOwnersOnly(string source)
        => AssertModesAgree(source, includeUnshared: false);

    // ── Every shape, every mode ─────────────────────────────────────────────

    public static TheoryData<string> Families() =>
    [
        "written-1", "written-x", "written-demanded", "branching", "lifted-root", "lifted-nested",
        "open", "dotted", "mixed", "root", "captured", "same-name-owners", "owners-2", "owners-16", "owners-17",
    ];

    private static string Family(string family, int size) => family switch
    {
        "written-1" => ExposureSettlementShareTests.ExplicitParameterMemberChain(size),
        "written-x" => ExposureSettlementShareTests.ExplicitParameterMemberChain(size, "x"),
        // The chain read at the root: every link's member is demanded by the run.
        "written-demanded" => ExposureSettlementShareTests.ExplicitParameterMemberChain(size, "x").Replace("\n0\n", $"\nP{size}.A(2)\n"),
        "branching" => BranchingLines(size) + "0\n",
        "lifted-root" => ExposureSettlementShareTests.RootChain(size, last: "p"),
        "lifted-nested" => ExposureSettlementShareTests.LiftedOwnerDefinition(size, "O") + "O(1)",
        "open" => ExposureOpenChainComplexityTests.NestedOwnerChain(size),
        "dotted" => ExposureOpenChainComplexityTests.NestedOwnerChain(size, "dotted"),
        "mixed" => ExposureOpenChainComplexityTests.NestedOwnerChain(size, "mixed"),
        "root" => ExposureSettlementShareTests.RootChain(size),
        "captured" => ExposureOpenChainComplexityTests.NestedOwnerChain(size, last: "p"),
        "same-name-owners" => "O(p) = {\n" + LiftedChainBody(size) + "}\nQ(p) = {\n" + LiftedChainBody(size) + "}\nO(1) + Q(20)",
        "owners-2" => NestedOwnerBranchingChain(2, size),
        "owners-16" => NestedOwnerBranchingChain(16, size),
        "owners-17" => NestedOwnerBranchingChain(17, size),
        _ => throw new ArgumentOutOfRangeException(nameof(family)),
    };

    private static string LiftedChainBody(int size)
        => ExposureOpenChainComplexityTests.Chain("open", size, "p", "    ") + ExposureOpenChainComplexityTests.Reader("open", "    ") + "    R\n";

    /// <summary>
    /// Every chain shape — the written chain with literal, forwarded and demanded arguments, the branching chain, the
    /// lifted terminals, the opened, dotted, mixed, root-level and captured-terminal controls, owners with same-named
    /// parameters, the opened-member rings, and the nested-owner witnesses on both sides of the footprint bound — parses
    /// cleanly and publishes the same metadata with footprints, with exact keys, and with no share.
    /// </summary>
    [Theory]
    [MemberData(nameof(Families))]
    public void EveryChainShape_PublishesTheSameMetadata_InEveryShareMode(string family)
    {
        foreach (var size in new[] { 1, 2, 3, 5, 8 })
            AssertModesAgree(Family(family, size));
    }

    [Fact]
    public void ADemandedWrittenChain_ReturnsTheSameValue_InEveryShareMode()
    {
        const int Length = 8;
        var source = Family("written-demanded", Length);
        foreach (var mode in Enum.GetValues<Mode>())
        {
            Assert.Equal("", Parse(source, mode).Diagnostics);
            var result = InMode(mode, () => KatLangEngine.Run(source));
            Assert.Equal((Length + 3).ToString(), Assert.IsType<RunResult.Success>(result).ToDisplayString());
        }
    }

    /// <summary>
    /// The opened-member rings, the witnesses of the cycle-cut rule (<see cref="ExposureSettlementShareTests"/>), with the
    /// owner's input entering at every member in turn: the same metadata in every share mode.
    /// </summary>
    [Theory]
    [InlineData(2)]
    [InlineData(3)]
    [InlineData(5)]
    public void OpenedMemberRings_PublishTheSameMetadata_InEveryShareMode(int size)
    {
        for (var entry = 0; entry < size; entry++)
            AssertModesAgree(ExposureSettlementShareTests.OpenedMemberRing(size, entry));
    }

    /// <summary>
    /// The language-specification and semantic-explorer corpora publish exactly the diagnostics and metadata of the
    /// exact-key share (the former rule), program by program.
    /// </summary>
    [Fact]
    public void TheSpecificationCorpora_PublishTheSameMetadata_AsTheExactKeyShare()
    {
        var sources = LanguageSpecCorpus.AllCases().Select(c => c.Source)
            .Concat(SemanticExplorerCorpus.AllCases().Select(c => c.Source))
            .Distinct(StringComparer.Ordinal)
            .ToArray();
        Assert.True(sources.Length > 1000);
        foreach (var source in sources)
        {
            var footprint = Parse(source, Mode.Footprint);
            var exact = Parse(source, Mode.ExactBoundOwners);
            Assert.True(exact.Diagnostics == footprint.Diagnostics && exact.Metadata == footprint.Metadata, source);
        }
    }

    // ── Linear frames and linear footprint work ─────────────────────────────

    /// <summary>
    /// The work the footprints add stays proportional to the frames: a frame records at most
    /// <see cref="SettlementShare.MaxFootprint"/> memberships and merges at most that many from each nested frame, and a
    /// lookup compares at most <see cref="SettlementShare.MaxCandidates"/> footprints. On the nested-owner witness with
    /// sixteen owners every settlement reads sixteen memberships, and the frames still grow linearly with the chain.
    /// </summary>
    [Fact]
    public void FootprintWork_StaysProportionalToTheFrames()
    {
        var frames = new long[3];
        var sizes = new[] { 16, 32, 64 };
        for (var k = 0; k < sizes.Length; k++)
        {
            var (diagnostics, metadata, observations) = Parse(NestedOwnerBranchingChain(16, sizes[k]), Mode.Footprint);
            Assert.Equal("", diagnostics);
            Assert.Contains($".O1.O2.O3.O4.O5.O6.O7.O8.O9.O10.O11.O12.O13.O14.O15.O16.P0.A|LocalOnlyCapturedAncestorParameters|", metadata);
            frames[k] = observations.RequiredAncestorSettlementFrames;
            Assert.InRange(observations.SettlementFootprintWork, 1, 2L * (SettlementShare.MaxFootprint + 1) * frames[k]);
            Assert.InRange(observations.SettlementShareCandidateVisits, observations.SettlementShareCandidateHits,
                (long)SettlementShare.MaxCandidates * frames[k]);
            Assert.Equal(observations.SettlementShareHits, observations.SettlementShareCandidateHits);
        }

        // Linear: the same number of frames per link at every size, plus a constant.
        Assert.Equal(2 * (frames[1] - frames[0]), frames[2] - frames[1]);
        Assert.InRange(frames[2], 1, 80L * sizes[2]);
    }

    /// <summary>
    /// Past the footprint bound the settlement that reads every owner answers its exact bound owners only, and so does
    /// every settlement that reused it: the branching chain over seventeen owners is the former exponential shape again
    /// (the residual the frame charge bounds, <see cref="ExposureSettlementFrameChargeTests"/>), with unchanged metadata.
    /// </summary>
    [Fact]
    public void AnOverCapFootprint_FallsBackToExactKeys()
    {
        var under = Parse(NestedOwnerBranchingChain(16, 12), Mode.Footprint).Observations.RequiredAncestorSettlementFrames;
        var over = Parse(NestedOwnerBranchingChain(17, 12), Mode.Footprint).Observations.RequiredAncestorSettlementFrames;
        var overExact = Parse(NestedOwnerBranchingChain(17, 12), Mode.ExactBoundOwners).Observations.RequiredAncestorSettlementFrames;
        Assert.True(over > 2 * under, $"{over} frames over the bound against {under} under it");
        Assert.InRange(over, 1, overExact);
        AssertModesAgree(NestedOwnerBranchingChain(17, 12), includeUnshared: false);
    }

    // ── The share's own rules ───────────────────────────────────────────────

    private static readonly IReadOnlyDictionary<string, RequirementSet> NoSummaries = new Dictionary<string, RequirementSet>();

    private static SummaryScope LevelAt(int depth)
    {
        var level = new SummaryScope(parent: null, propertyScope: null!, NoSummaries);
        for (var i = 0; i < depth; i++)
            level = new SummaryScope(level, propertyScope: null!, NoSummaries);
        return level;
    }

    private static Algorithm Owner() => SourceProvenance.ParseValid("1").Root;

    private static BoundOwnerSet? Owners(params Algorithm[] owners) => BoundOwnerSet.With(current: null, owners, observations: null);

    private static SettlementShare.Settled Read(BoundOwnerEmptiness emptiness = BoundOwnerEmptiness.Unread, bool offChain = false,
        params (Algorithm Owner, bool Present)[] footprint)
        => new(default, SummaryScope.NoOwnerLookup, readLive: false, views: [], inconsistentViews: false, footprint, emptiness, offChain);

    /// <summary>
    /// A footprint answers exactly the bound owners that give every read membership its recorded answer — by
    /// reference, so an owner equal by value to a read one is another owner — and, when it read whether there are
    /// none, the same emptiness. Owners it never read are free.
    /// </summary>
    [Fact]
    public void AFootprint_AnswersExactlyTheBoundOwnersThatGiveItsAnswers()
    {
        var a = Owner();
        var b = Owner();
        var c = Owner();
        var twinOfA = a with { };
        Assert.Equal(a, twinOfA);
        var settled = Read(footprint: [(a, true), (b, false)]);
        Assert.True(settled.Satisfies(Owners(a), observations: null));
        Assert.True(settled.Satisfies(Owners(a, c), observations: null));
        Assert.False(settled.Satisfies(Owners(a, b), observations: null));
        Assert.False(settled.Satisfies(Owners(c), observations: null));
        Assert.False(settled.Satisfies(Owners(twinOfA), observations: null));
        Assert.False(settled.Satisfies(null, observations: null));

        Assert.True(Read(footprint: []).Satisfies(null, observations: null));
        Assert.True(Read(footprint: []).Satisfies(Owners(a), observations: null));
        Assert.True(Read(footprint: [(a, false)]).Satisfies(null, observations: null));
        Assert.True(Read(BoundOwnerEmptiness.ReadNone, footprint: []).Satisfies(null, observations: null));
        Assert.False(Read(BoundOwnerEmptiness.ReadNone, footprint: []).Satisfies(Owners(c), observations: null));
        Assert.False(Read(BoundOwnerEmptiness.ReadSome, footprint: []).Satisfies(null, observations: null));
        Assert.True(Read(BoundOwnerEmptiness.ReadSome, footprint: []).Satisfies(Owners(c), observations: null));

        // Through the share: one key's settlement answers another key of its content and level.
        var observations = new FrontEndTraversalObservations();
        var share = new SettlementShare(observations);
        var level = LevelAt(1);
        share.Store(new SettlementShare.Key("reference", level, Owners(a)), settled);
        Assert.True(share.TryGet(new SettlementShare.Key("reference", level, Owners(a, c)), out var kept));
        Assert.Same(settled, kept);
        Assert.False(share.TryGet(new SettlementShare.Key("reference", level, Owners(a, b)), out _));
        Assert.False(share.TryGet(new SettlementShare.Key("reference", LevelAt(1), Owners(a)), out _));
        Assert.False(share.TryGet(new SettlementShare.Key("other", level, Owners(a)), out _));
        Assert.Equal(1, observations.SettlementShareCandidateHits);
        Assert.Equal(2, observations.SettlementShareCandidateVisits);
    }

    /// <summary>
    /// A settlement whose footprint is unknown, or that saw an owner off its site's chain, answers its exact bound
    /// owners only — the former keys, compared exactly.
    /// </summary>
    [Fact]
    public void WithoutAUsableFootprint_ASettlementAnswersItsExactBoundOwnersOnly()
    {
        var a = Owner();
        var b = Owner();
        var level = LevelAt(0);
        foreach (var settled in new[] { Read(footprint: null!), Read(offChain: true, footprint: []) })
        {
            var observations = new FrontEndTraversalObservations();
            var share = new SettlementShare(observations);
            share.Store(new SettlementShare.Key("reference", level, Owners(a)), settled);
            Assert.True(share.TryGet(new SettlementShare.Key("reference", level, Owners(a)), out _));
            Assert.False(share.TryGet(new SettlementShare.Key("reference", level, Owners(a, b)), out _));
            Assert.False(share.TryGet(new SettlementShare.Key("reference", level, Bound: null), out _));
            Assert.Equal(0, observations.SettlementShareCandidateHits);
            Assert.Equal(1, observations.SettlementShareHits);
        }

        Assert.Throws<InvalidOperationException>(() => Read(footprint: null!).Satisfies(null, observations: null));
    }

    /// <summary>
    /// One content and level keep at most <see cref="SettlementShare.MaxCandidates"/> footprints; a further settlement
    /// of them is kept for its exact bound owners, so a lookup compares a bounded number of footprints and the former
    /// exact answer is never lost. A settlement a kept footprint already answers is not kept twice.
    /// </summary>
    [Fact]
    public void TheCandidatesOfOneContent_AreBounded_AndTheRestAreKeptExactly()
    {
        var level = LevelAt(0);
        var observations = new FrontEndTraversalObservations();
        var share = new SettlementShare(observations);
        var owners = Enumerable.Range(0, SettlementShare.MaxCandidates + 2).Select(_ => Owner()).ToArray();
        // Each settlement read its own owner as present: no two answer one bound-owner set of a single owner.
        foreach (var owner in owners)
            share.Store(new SettlementShare.Key("reference", level, Owners(owner)), Read(footprint: [(owner, true)]));
        share.Store(new SettlementShare.Key("reference", level, Owners(owners[0], owners[^1])), Read(footprint: [(owners[0], true)]));
        Assert.Equal(owners.Length, observations.SettlementShareStores);

        var visitsBefore = observations.SettlementShareCandidateVisits;
        foreach (var owner in owners)
            Assert.True(share.TryGet(new SettlementShare.Key("reference", level, Owners(owner)), out _));
        Assert.Equal(SettlementShare.MaxCandidates, observations.SettlementShareCandidateHits);
        Assert.InRange(observations.SettlementShareCandidateVisits - visitsBefore, 1,
            (long)owners.Length * SettlementShare.MaxCandidates);

        // The exactly kept ones answer their own key only.
        Assert.False(share.TryGet(new SettlementShare.Key("reference", level, Owners(owners[^1], Owner())), out _));
    }

    /// <summary>
    /// A candidate weighs its key, its views and every membership of its footprint; a candidate whose view moved on is
    /// dropped at the lookup that meets it, releasing its weight, and is computed again.
    /// </summary>
    [Fact]
    public void ACandidate_WeighsItsFootprint_AndIsDroppedWhenAViewItReadChanges()
    {
        var a = Owner();
        var b = Owner();
        var level = LevelAt(0);
        var key = new SettlementShare.Key("reference", level, Owners(a));
        Assert.Equal(1, key.Weight);

        var narrow = new SettlementShare(observations: null, capacity: 2);
        narrow.Store(key, Read(footprint: [(a, true), (b, false)]));
        Assert.False(narrow.TryGet(key, out _));
        var enough = new SettlementShare(observations: null, capacity: 3);
        enough.Store(key, Read(footprint: [(a, true), (b, false)]));
        Assert.True(enough.TryGet(key with { Bound = Owners(a, Owner()) }, out _));

        var facts = new VersionedFacts();
        var observations = new FrontEndTraversalObservations();
        var share = new SettlementShare(observations, capacity: 2);
        share.Store(key, new SettlementShare.Settled(default, SummaryScope.NoOwnerLookup, readLive: false,
            views: [(facts, facts.ViewVersion)], inconsistentViews: false, footprint: []));
        Assert.True(share.TryGet(key with { Bound = Owners(b) }, out _));
        facts.Version++;
        Assert.False(share.TryGet(key with { Bound = Owners(b) }, out _));
        Assert.Equal(1, observations.SettlementShareStaleViews);
        Assert.False(share.TryGet(key, out _));

        // The dropped candidate released its room.
        share.Store(key, new SettlementShare.Settled(default, SummaryScope.NoOwnerLookup, readLive: false,
            views: [(facts, facts.ViewVersion)], inconsistentViews: false, footprint: []));
        Assert.True(share.TryGet(key, out _));
    }

    /// <summary>
    /// Reclaiming a stale candidate also releases its content key and empty candidate list. Otherwise repeated view
    /// changes leave uncharged groups behind, even when the share has room for only one candidate at a time.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void StaleCandidateGroups_ReleaseTheirKeys_WhenTheirLastEntryIsRemoved(bool replaceDuringStore)
    {
        var level = LevelAt(0);
        var owner = Owner();
        var facts = new VersionedFacts();
        var observations = new FrontEndTraversalObservations();
        var share = new SettlementShare(observations, capacity: 2);
        for (var i = 0; i < 32; i++)
        {
            var key = new SettlementShare.Key($"reference{i}", level, Owners(owner));
            share.Store(key, new SettlementShare.Settled(default, SummaryScope.NoOwnerLookup, readLive: false,
                views: [(facts, facts.ViewVersion)], inconsistentViews: false, footprint: []));
            Assert.True(share.TryGet(key, out _));
            facts.Version++;
            if (replaceDuringStore)
            {
                // This replacement removes the stale entry but cannot fit: key + view + membership = 3 units.
                share.Store(key, new SettlementShare.Settled(default, SummaryScope.NoOwnerLookup, readLive: false,
                    views: [(facts, facts.ViewVersion)], inconsistentViews: false, footprint: [(owner, true)]));
            }
            else
            {
                Assert.False(share.TryGet(key, out _));
            }
        }

        Assert.Equal(32, observations.SettlementShareStores);
        Assert.Equal(32, observations.SettlementShareStaleViews);
        var groups = Assert.IsAssignableFrom<System.Collections.IDictionary>(typeof(SettlementShare)
            .GetField("_candidates", System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic)!
            .GetValue(share));
        Assert.Empty(groups);
    }

    private sealed class VersionedFacts : StaticLookupFacts
    {
        public int Version;
        internal override int ViewVersion => Version;
        internal override StaticScopeKey PreludeKey => throw new NotSupportedException();
        internal override IEnumerable<StaticScopeKey> Scopes => [];
        internal override CompletedStaticStructures.BodyFacts? Facts(StaticScopeKey key) => null;
        internal override StaticScopeKey? Child(StaticScopeKey parent, Algorithm body, Pattern? pattern = null) => null;
        internal override void EnsureUsable() { }
    }
}
