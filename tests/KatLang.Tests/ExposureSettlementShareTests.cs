namespace KatLang.Tests;

using SettlementShare = PropertyExposureResolver.SettlementShare;
using SummaryScope = PropertyExposureResolver.SummaryScope;

/// <summary>
/// The exposure pass's run-scoped settlement share (<c>PropertyExposureResolver.SettlementShare</c>): a
/// completed nested settlement that saw no cycle cut, read no summary of the level in progress and does
/// not depend on its site is kept for the whole resolution, so a chain of N members opened from one
/// another is settled in a constant number of frames per link instead of N(N + 3). Implementation only:
/// every classification is the unshared settlement's (C#-only; Lean models no exposure analysis).
///
/// <para>The oracle is deterministic work (<see cref="FrontEndTraversalObservations"/>) and exact
/// classification, never elapsed time. The opened-member rings are the witness of the cycle-cut rule:
/// no other family reaches a cut-only frame (in the reproducer B family every cycle passes through a
/// level summary, which ends the walk), so a share that kept cut results passes every other test.</para>
/// </summary>
public sealed class ExposureSettlementShareTests
{
    private static string RootChain(int length)
        => ExposureOpenChainComplexityTests.Chain("open", length, "5", "") + ExposureOpenChainComplexityTests.Reader("open", "") + "R";

    private static string Source(string shape, int length) => shape switch
    {
        "open" => ExposureOpenChainComplexityTests.NestedOwnerChain(length),
        "dotted" => ExposureOpenChainComplexityTests.NestedOwnerChain(length, "dotted"),
        "mixed" => ExposureOpenChainComplexityTests.NestedOwnerChain(length, "mixed"),
        "root" => RootChain(length),
        "captured" => ExposureOpenChainComplexityTests.NestedOwnerChain(length, last: "p"),
        _ => throw new ArgumentOutOfRangeException(nameof(shape)),
    };

    // ── The five chain shapes ───────────────────────────────────────────────

    /// <summary>
    /// Each link's level settles its own member's reference by walking the links below it; the walk below
    /// a link is the same from every link above it, so each later level reuses it after one frame. Formerly
    /// N(N + 3) frames: 4,006,000 at 2,000 captured links, now under 16,000.
    /// </summary>
    [Theory]
    [InlineData("open")]
    [InlineData("dotted")]
    [InlineData("mixed")]
    [InlineData("root")]
    [InlineData("captured")]
    public void ChainShapes_SettleInLinearFrames_WithUnchangedClassification(string shape)
    {
        foreach (var length in new[] { 16, 32, 64, 128, 256, 512, 1000, 2000 })
        {
            var observations = new FrontEndTraversalObservations();
            var root = ExposureOpenChainComplexityTests.Exposed(Source(shape, length), observations);
            var level = shape == "root" ? root : ExposureOpenChainComplexityTests.Member(root, "O").Value;
            var captured = shape == "captured";
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(level, "R"),
                captured ? [("p", 0)] : []);
            for (var i = 1; i <= length; i++)
            {
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(level, $"P{i}"));
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(level, $"P{i}", $"A{i}"),
                    captured ? [("p", 1)] : []);
                if (shape == "mixed")
                    ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(level, $"P{i}", $"Local{i}"));
            }

            Assert.InRange(observations.RequiredAncestorSettlementFrames, 1, 16L * length);
            // One reuse per link level below the first walk, and nothing kept that was never complete.
            Assert.InRange(observations.SettlementShareHits, length - 4, length);
            Assert.InRange(observations.SettlementShareStores, 1, observations.RequiredAncestorSettlementFrames);
            Assert.Equal(0, observations.SettlementShareStaleViews);
        }
    }

    // ── Cycle cuts ──────────────────────────────────────────────────────────

    /// <summary>
    /// A ring of k libraries whose public members read one another through <c>open</c>s (no level summary on
    /// the cycle, so every nested settlement reads only final summaries), with the owner's input entering at
    /// one member, read through an open AND dotted from the owner. Inside one settlement the inner members of
    /// the ring see a cycle cut and hold a partial union; a share that kept such a result would hand a later
    /// reader of that member the partial set and classify it exported. Every member and reader requires <c>x</c>.
    /// </summary>
    [Theory]
    [InlineData(2)]
    [InlineData(3)]
    [InlineData(5)]
    public void OpenedMemberRing_CycleCutResultsAreNeverShared(int size)
    {
        for (var entry = 0; entry < size; entry++)
        {
            var source = new System.Text.StringBuilder("O(x) = {\n");
            for (var i = 0; i < size; i++)
                source.Append($"    L{i} = {{\n        open L{(i + 1) % size}\n        public V{i} = V{(i + 1) % size}{(i == entry ? " + x" : "")}\n        1\n    }}\n");
            for (var i = 0; i < size; i++)
                source.Append($"    A{i} = {{\n        open L{i}\n        V{i}\n    }}\n    C{i} = L{i}.V{i}\n");
            source.Append("    1\n}\n1");
            var owner = ExposureOpenChainComplexityTests.Member(ExposureOpenChainComplexityTests.Exposed(source.ToString(), new()), "O").Value;
            for (var i = 0; i < size; i++)
            {
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, $"L{i}", $"V{i}"), ("x", 1));
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, $"A{i}"), ("x", 0));
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, $"C{i}"), ("x", 0));
            }
        }
    }

    // ── Owner identity ──────────────────────────────────────────────────────

    /// <summary>
    /// The same opened chain under two owners whose parameters are both named <c>p</c>: the share keys
    /// settlements by level and bound-owner identity, so each reader still requires its OWN owner's input.
    /// </summary>
    [Fact]
    public void SameNamedParametersOfTwoOwners_StayApart()
    {
        const int Length = 24;
        var chain = ExposureOpenChainComplexityTests.Chain("open", Length, "p", "    ") + ExposureOpenChainComplexityTests.Reader("open", "    ");
        var source = "O(p) = {\n" + chain + "    R\n}\nQ(p) = {\n" + chain + "    R\n}\nO(1) + Q(20)";
        var observations = new FrontEndTraversalObservations();
        var root = ExposureOpenChainComplexityTests.Exposed(source, observations);
        foreach (var owner in new[] { "O", "Q" })
        {
            var level = ExposureOpenChainComplexityTests.Member(root, owner).Value;
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(level, "R"), ("p", 0));
            for (var i = 1; i <= Length; i++)
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(level, $"P{i}", $"A{i}"), ("p", 1));
        }

        Assert.InRange(observations.RequiredAncestorSettlementFrames, 1, 2 * 16L * Length);
        Assert.Equal((1 + Length - 1 + 20 + Length - 1).ToString(System.Globalization.CultureInfo.InvariantCulture),
            Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }

    [Fact]
    public void RetargetedFactView_InvalidatesPreviouslySharedChainSettlements()
    {
        const int Length = 32;
        var source = ExposureOpenChainComplexityTests.NestedOwnerChain(Length, last: "p");
        var detected = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
        Assert.Empty(detected.Diagnostics);
        var diagnostics = new DiagnosticBag();
        var resolved = Assert.IsType<Algorithm.User>(ImplicitArgumentResolver.ResolvePrevalidated(detected, observations: null, diagnostics));
        Assert.Empty(diagnostics);
        var publication = resolved.CompletedStructure!;
        var facts = publication.Facts;
        var entry = publication.Entry!;

        var observations = new FrontEndTraversalObservations();
        observations.RequiredAncestorSettlementObserver = _ =>
        {
            if (observations.SettlementShareHits == 0)
                return;

            // Keep every lookup answer the same while advancing the actual view read by the settlement.
            // Do this after the first reuse so later link levels still encounter entries from the old view.
            var version = facts.ViewVersion;
            facts.Retarget(entry, resolved with { });
            Assert.Equal(version + 1, facts.ViewVersion);
            observations.RequiredAncestorSettlementObserver = null;
        };

        var root = PropertyExposureResolver.Resolve(resolved, observations);
        Assert.True(observations.SettlementShareStaleViews > 0);
        var owner = ExposureOpenChainComplexityTests.Member(root, "O").Value;
        ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, "R"), ("p", 0));
        for (var i = 1; i <= Length; i++)
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, $"P{i}", $"A{i}"), ("p", 1));
    }

    // ── The share itself ────────────────────────────────────────────────────

    /// <summary>A fact view whose version the test moves; the share reads nothing else of a view.</summary>
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

    private static readonly IReadOnlyDictionary<string, RequirementSet> NoSummaries
        = new Dictionary<string, RequirementSet>();

    /// <summary>A level at <paramref name="depth"/>: the share reads a level's identity and depth only.</summary>
    private static SummaryScope LevelAt(int depth)
    {
        var level = new SummaryScope(parent: null, propertyScope: null!, NoSummaries);
        for (var i = 0; i < depth; i++)
            level = new SummaryScope(level, propertyScope: null!, NoSummaries);
        return level;
    }

    private static SettlementShare.Settled Settled(
        int siteDepth = SummaryScope.NoOwnerLookup, bool readLive = false, bool inconsistentViews = false,
        params (StaticLookupFacts Facts, int Version)[] views)
        => new(default, siteDepth, readLive, views, inconsistentViews);

    /// <summary>
    /// A kept settlement answers only while every completed-fact view it consulted is at the version it read:
    /// a changed view drops the entry (it is computed again), and the entry does not return with the version.
    /// Without the check the second lookup would answer from the view's former contents.
    /// </summary>
    [Fact]
    public void KeptSettlement_IsDroppedWhenAViewItConsultedChanges()
    {
        var observations = new FrontEndTraversalObservations();
        var share = new SettlementShare(observations, capacity: 3);
        var level = LevelAt(1);
        var facts = new VersionedFacts();
        var other = new VersionedFacts();
        var key = new SettlementShare.Key("reference", level, "");
        share.Store(key, Settled(views: [(facts, facts.ViewVersion), (other, other.ViewVersion)]));

        Assert.True(share.TryGet(key, out var kept));
        Assert.Equal(2, kept!.Views.Length);

        other.Version++;
        Assert.False(share.TryGet(key, out _));
        other.Version--;
        Assert.False(share.TryGet(key, out _));

        Assert.Equal(1, observations.SettlementShareStores);
        Assert.Equal(1, observations.SettlementShareHits);
        Assert.Equal(1, observations.SettlementShareStaleViews);

        // The dropped entry released its room: the full share keeps the recomputed settlement.
        share.Store(key, Settled(views: [(facts, facts.ViewVersion), (other, other.ViewVersion)]));
        Assert.True(share.TryGet(key, out _));
        Assert.Equal(2, observations.SettlementShareStores);
    }

    /// <summary>
    /// What may be kept: a result that read no live summary, saw every view at one version, and whose site
    /// lookups all landed at or above its level. A landing below the level, or an owner the site's chain does
    /// not hold (<see cref="int.MaxValue"/>), depends on the site and is refused.
    /// </summary>
    [Fact]
    public void OnlyASettlementThatStandsFromEverySite_IsKept()
    {
        var level = LevelAt(2);
        Assert.True(Settled().StandsFromEverySite(level));
        Assert.True(Settled(siteDepth: 0).StandsFromEverySite(level));
        Assert.True(Settled(siteDepth: 2).StandsFromEverySite(level));
        Assert.False(Settled(siteDepth: 3).StandsFromEverySite(level));
        Assert.False(Settled(siteDepth: int.MaxValue).StandsFromEverySite(level));
        Assert.False(Settled(readLive: true).StandsFromEverySite(level));
        Assert.False(Settled(inconsistentViews: true).StandsFromEverySite(level));

        var observations = new FrontEndTraversalObservations();
        var share = new SettlementShare(observations);
        var key = new SettlementShare.Key("reference", level, "");
        Assert.Throws<InvalidOperationException>(() => share.Store(key, Settled(siteDepth: 3)));
        Assert.Throws<InvalidOperationException>(() => share.Store(key, Settled(readLive: true)));
        Assert.False(share.TryGet(key, out _));
        Assert.Equal(0, observations.SettlementShareStores);

        // The key is the settlement's own: another level or another bound-owner set is another entry.
        share.Store(key, Settled(siteDepth: 2));
        Assert.True(share.TryGet(key, out _));
        Assert.False(share.TryGet(key with { Level = LevelAt(2) }, out _));
        Assert.False(share.TryGet(key with { Bound = "7" }, out _));
        Assert.False(share.TryGet(key with { Content = "other" }, out _));
    }

    /// <summary>
    /// The share retains a bounded weight for keys and fact-view records, and
    /// keeps nothing more once it is full, so a program whose settlements never repeat a key cannot make it
    /// grow with the frames. A full share still answers what it holds.
    /// </summary>
    [Fact]
    public void FullShare_KeepsNothingMore_AndStillAnswers()
    {
        var level = LevelAt(0);
        var observations = new FrontEndTraversalObservations();
        var share = new SettlementShare(observations, capacity: 3);
        var keys = Enumerable.Range(0, 5).Select(i => new SettlementShare.Key($"k{i}", level, "")).ToArray();
        foreach (var key in keys)
            share.Store(key, Settled());

        Assert.Equal(3, observations.SettlementShareStores);
        Assert.True(share.TryGet(keys[0], out _));
        Assert.True(share.TryGet(keys[2], out _));
        Assert.False(share.TryGet(keys[3], out _));
        Assert.False(share.TryGet(keys[4], out _));

        // Key text is retained with the entry: 64 characters of content or bound owners weigh one more unit.
        var weighed = new FrontEndTraversalObservations();
        var narrow = new SettlementShare(weighed, capacity: 2);
        narrow.Store(new SettlementShare.Key(new string('c', 64), level, ""), Settled());
        narrow.Store(new SettlementShare.Key("x", level, ""), Settled());
        Assert.Equal(1, weighed.SettlementShareStores);
        Assert.Equal(2, new SettlementShare.Key("c", level, new string('1', 64)).Weight);
        Assert.Equal(1, new SettlementShare.Key("c", level, new string('1', 62)).Weight);

        var withViews = new SettlementShare(observations: null, capacity: 2);
        var facts = new VersionedFacts();
        var other = new VersionedFacts();
        withViews.Store(keys[0], Settled(views: [(facts, facts.ViewVersion), (other, other.ViewVersion)]));
        Assert.False(withViews.TryGet(keys[0], out _));
        withViews.Store(keys[1], Settled(views: [(facts, facts.ViewVersion)]));
        withViews.Store(keys[2], Settled());
        Assert.True(withViews.TryGet(keys[1], out _));
        Assert.False(withViews.TryGet(keys[2], out _));
    }
}
