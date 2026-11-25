using System.Text;
using Xunit.Abstractions;

namespace KatLang.Tests;

using Mode = PropertyExposureResolver.SettlementShareMode;

/// <summary>
/// The exposure residuals of the November 21 2026 adversarial performance audit (baseline <c>8947d21e</c>), measured
/// again after the component settlements (<c>8221e5d1</c>) and the open-walk reuse (<c>9e3ff233</c>) and repaired where
/// the dependency and lifetime invariants hold (C# exposure implementation only; Lean models no exposure analysis):
/// <list type="bullet">
/// <item>LIVE READS (<c>exposure-live-open-walks-maxlivereads</c>): a frame kept at most sixteen names of the live
/// summaries it read, so the unbound open walks of a level that read seventeen or more were settled again by every reader
/// with bound owners (M² + 6M + 1 frames). Names are now canonical sets without that cap, of one interner per level
/// solve that charges every completed operation's new entries and releases its tables on crossing their capacity. After that,
/// the solve's settlements name their live reads as unknown and are reused only inside their Run (2026-11-25).</item>
/// <item>LIVE SETTLEMENTS (that finding's broader shapes): any other whole settlement that read a live summary, a member
/// seed listing the level's properties above all, was reused only inside its Run (K × W frames). It is now kept for the
/// rest of the level's solve while every summary it read stands, under the share's footprint, site and view rules.</item>
/// <item>SEED PARTS (<c>exposure-summary-seed-logical-width</c>): a navigated member's seed was folded and its names
/// canonicalized whole at every settlement, and copied at every parameterless level between its declaration and the
/// reader (K² / 2 elements; depth × K² / 2 copies). A part holding required names only is now resolved once per
/// level through a kept set, and such a seed is carried through those levels unchanged.</item>
/// <item>QUALIFIED SEED PARTS (the seed residual 5d747bb8 recorded): a part holding owner-qualified requirements was folded,
/// qualified name by name while anchored through a level that binds parameters, and read once per requirement when settled
/// (output rows reading K chained library members under their owner: K² / 2 names, 404 MB at K = 2,000). Each part is now
/// qualified once per level and kept, and each settlement looks each owner up once, with the folded walk's record.</item>
/// <item>OFF-CHAIN (<c>exposure-offchain-terminal-disables-footprints</c>): NOT repaired. A settlement with an owner
/// lookup off its site's chain answers its exact key only, because extending it changes the metadata of THE OFF-CHAIN
/// GAP's programs, an owner decision. Its negative controls and the latent <c>LocalOnlyProperty</c> are pinned here.</item>
/// </list>
/// Oracles: exact published metadata against the former walks (<see cref="PropertyExposureResolver.LiveSettlementsPerRunForTesting"/>,
/// <see cref="PropertyExposureResolver.SeedPartsFoldedForTesting"/>, <see cref="PropertyExposureResolver.OpenWalksPerReaderForTesting"/>)
/// and the unshared settlement, independent requirement oracles, run values, and deterministic counters, never time.
/// </summary>
public sealed class ExposureResidualReuseTests(ITestOutputHelper output)
{
    // ── Harness ─────────────────────────────────────────────────────────────

    private static T With<T>(AsyncLocal<bool> seam, Func<T> work)
    {
        var previous = seam.Value;
        seam.Value = true;
        try { return work(); }
        finally { seam.Value = previous; }
    }

    private static T InMode<T>(Mode mode, Func<T> work)
    {
        var previous = PropertyExposureResolver.SettlementShareModeForTesting.Value;
        PropertyExposureResolver.SettlementShareModeForTesting.Value = mode;
        try { return work(); }
        finally { PropertyExposureResolver.SettlementShareModeForTesting.Value = previous; }
    }

    /// <summary>The eager parse of <paramref name="source"/>: its diagnostics, every property's metadata and the counters.</summary>
    private static (string Diagnostics, string Metadata, FrontEndTraversalObservations Observations) Parse(string source,
        FrontEndTraversalObservations? observations = null)
    {
        observations ??= new FrontEndTraversalObservations();
        var parsed = Parser.ParseObserved(source, options: null, observations);
        var diagnostics = string.Join("\n", parsed.Diagnostics.Select(d => $"{d.Code}/{d.Severity}@{d.Span}: {d.Message}"));
        return (diagnostics, ExposureSettlementFrameChargeTests.Metadata(parsed.Root), observations);
    }

    /// <summary>Production, the former walk (the seam) and the unshared settlement publish the same diagnostics and metadata.</summary>
    private static (FrontEndTraversalObservations Production, FrontEndTraversalObservations Former) AssertSameAsFormerWalk(
        string source, AsyncLocal<bool> formerWalk, bool clean = true)
    {
        var production = Parse(source);
        if (clean)
            Assert.Equal("", production.Diagnostics);
        var former = With(formerWalk, () => Parse(source));
        Assert.Equal(former.Diagnostics, production.Diagnostics);
        Assert.Equal(former.Metadata, production.Metadata);
        var unshared = InMode(Mode.Unshared, () => Parse(source));
        Assert.Equal(unshared.Diagnostics, production.Diagnostics);
        Assert.Equal(unshared.Metadata, production.Metadata);
        return (production.Observations, former.Observations);
    }

    private static string Value(string source) => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString();

    private static Algorithm.User Root(string source) => SourceProvenance.ParseValid(source).Root;

    private static void AssertLinear(long[] work, string what)
    {
        Assert.InRange((double)work[1] / work[0], 1.5, 2.5);
        Assert.InRange((double)work[2] / work[1], 1.5, 2.5);
        _ = what;
    }

    // ── Shapes ──────────────────────────────────────────────────────────────

    /// <summary>
    /// The audit's <c>liveb</c> family: <c>F</c> opens <c>M.N</c>, whose block lists <paramref name="caps"/> of
    /// <c>F</c>'s own properties <c>Cap{j} = y</c>, and <paramref name="readers"/> readers <c>A{i}(z)</c> each read one
    /// opened member. The level's open walks read every <c>Cap</c> while <c>F</c> is solved. <c>F</c>'s output reads no
    /// reader: a row reading one would settle the walks once more under <c>F</c> itself as a bound owner, which C1 refuses
    /// by its own rule.
    /// </summary>
    internal static string LiveOpenFamily(int readers, int caps)
    {
        var source = new StringBuilder("F(y) = {\n  open M.N\n  M = {\n    public N = {\n");
        for (var i = 0; i < readers; i++) source.Append($"      public X{i} = 1\n");
        for (var j = 0; j < caps; j++) source.Append($"      Cap{j}\n");
        source.Append("    }\n    0\n  }\n");
        for (var j = 0; j < caps; j++) source.Append($"  Cap{j} = y\n");
        for (var i = 0; i < readers; i++) source.Append($"  A{i}(z) = X{i} + 0\n");
        source.Append("  0\n}\nF(5)\n");
        return source.ToString();
    }

    /// <summary>
    /// The audit's <c>pathl</c> shape inside an owner: a member <c>Lib.V</c> lists <paramref name="width"/> of the level's
    /// properties <c>Cap{j} = y + j</c>, and <paramref name="readers"/> readers <c>A{i}(z)</c> read it through the written
    /// path (no <c>open</c>); with <paramref name="opened"/>, through <c>open M.N</c> (the <c>memberl</c> shape).
    /// </summary>
    internal static string LiveMemberFamily(int readers, int width, bool opened = false)
    {
        var caps = string.Join(", ", Enumerable.Range(0, width).Select(j => $"Cap{j}"));
        var source = new StringBuilder("F(y) = {\n");
        source.Append(opened
            ? $"  open M.N\n  M = {{\n    public N = {{\n      public X0 = [{caps}]\n    }}\n    0\n  }}\n"
            : $"  Lib = {{\n    public V = [{caps}]\n  }}\n");
        for (var j = 0; j < width; j++) source.Append($"  Cap{j} = y + {j}\n");
        var read = opened ? "X0[0]" : "Lib.V[0]";
        for (var i = 0; i < readers; i++) source.Append($"  A{i}(z) = {read} + z\n");
        source.Append("  A0(1)\n}\nF(5)\n");
        return source.ToString();
    }

    /// <summary>
    /// A summary a kept live settlement read changes after a reader took it
    /// (<see cref="AKeptLiveSettlement_IsSettledAgainWhenASummaryItReadChanges"/>): every reader ends up requiring <c>w</c>.
    /// </summary>
    internal const string StaleSummaryWitness = "G(w) = {\n  F(y) = {\n    Lib = {\n      public V = [Cap]\n    }\n"
        + "    Cap = K + 0\n    K = w + A0(1) + A1(1)\n    A0(z) = Lib.V[0] + z\n    A1(z) = Lib.V[0] + z\n    0\n  }\n  F(5)\n}\nG(7)\n";

    /// <summary>
    /// Readers whose live read sets are DISTINCT AND OVERLAPPING: <c>F</c> opens <c>M.N</c>, whose member <c>X{i}</c> lists
    /// the <paramref name="window"/> properties <c>Cap{i}</c> … <c>Cap{i+window-1}</c> (indices modulo
    /// <paramref name="readers"/>) of <c>F</c>, and reader <c>A{i}(z)</c> reads <c>X{i}</c>. Every reader's member settlement
    /// reads a different set of live summaries, which the live-read interner builds path by path.
    /// </summary>
    internal static string OverlappingLiveReads(int readers, int window)
    {
        var source = new StringBuilder("F(y) = {\n  open M.N\n  M = {\n    public N = {\n");
        for (var i = 0; i < readers; i++)
            source.Append($"      public X{i} = [{string.Join(", ", Enumerable.Range(0, window).Select(j => $"Cap{(i + j) % readers}"))}]\n");
        source.Append("    }\n    0\n  }\n");
        for (var j = 0; j < readers; j++) source.Append($"  Cap{j} = y + {j}\n");
        for (var i = 0; i < readers; i++) source.Append($"  A{i}(z) = X{i}[0] + z\n");
        source.Append("  A0(1)\n}\nF(5)\n");
        return source.ToString();
    }

    /// <summary>
    /// The audit's <c>navchain</c> shape: <c>Lib</c>'s member <c>P{i}</c> reads <c>P{i-1}</c> and the parameter
    /// <c>p{i}</c> of <c>F</c>, and reader <c>R{i}</c> reads <c>Lib.P{i}</c>, so <c>R{i}</c> requires <c>p1</c> … <c>p{i}</c>.
    /// With <paramref name="depth"/>, the library is nested in that many parameterless blocks read through one alias
    /// (<c>navalias</c>).
    /// </summary>
    internal static string NavigatedChain(int members, int depth = 0, string? output = null)
    {
        var source = new StringBuilder($"F({string.Join(", ", Enumerable.Range(1, members).Select(i => $"p{i}"))}) = {{\n");
        for (var d = 1; d <= depth; d++) source.Append($"W{d} = {{\n");
        source.Append("Lib = {\npublic P1 = p1\n");
        for (var i = 2; i <= members; i++) source.Append($"public P{i} = P{i - 1} + p{i}\n");
        source.Append("}\n");
        for (var d = 1; d <= depth; d++) source.Append("}\n");
        var head = depth == 0 ? "Lib" : "L";
        if (depth > 0) source.Append($"L = {string.Join(".", Enumerable.Range(1, depth).Select(d => $"W{d}"))}.Lib\n");
        for (var i = 1; i <= members; i++) source.Append($"R{i} = {head}.P{i}\n");
        source.Append($"{output ?? $"R{members}"}\n}}\nF({string.Join(", ", Enumerable.Range(1, members))})\n");
        return source.ToString();
    }

    /// <summary>
    /// The owner-qualified seed-part shapes (QUALIFIED SEED PARTS). The library member <c>P{i}</c> reads <c>P{i-1}</c>
    /// and the parameter <c>p{i}</c>, so its seed holds its predecessor's by reference, and the members are read where
    /// the owner that binds the <c>p{i}</c> lies between their library and the reader:
    /// <list type="bullet">
    /// <item><c>rows</c>, the source report's fixture: <c>F</c>'s output rows <c>Lib.P1</c> … <c>Lib.P{K}</c>, settled
    /// where <c>F</c> is declared with <c>F</c> as a bound owner. Each row's seed is anchored through <c>F</c>'s level,
    /// which binds every <c>p{i}</c>.</item>
    /// <item><c>same-names</c>: those rows inside <c>G(p1, …, p{K})</c>, itself in <c>F(p1, …, p{K})</c>: the names are
    /// <c>G</c>'s, and <c>F</c>'s same-named parameters are never required.</item>
    /// <item><c>one-name</c>: inside <c>G(p2)</c> in <c>F</c>: <c>p2</c> is <c>G</c>'s and every other <c>p{i}</c> is
    /// <c>F</c>'s, so <c>G</c> requires them.</item>
    /// <item><c>outer-name</c>: the first member also reads <c>y</c>, which <c>F</c> does not bind and the enclosing
    /// <c>H(y)</c> does, so <c>F</c> requires <c>H</c>'s <c>y</c>.</item>
    /// <item><c>detached</c>: root properties <c>R{i} = F.Lib.P{i}</c> read the members without calling <c>F</c>: the
    /// owner of their requirements is on no level of the reader's chain (THE OFF-CHAIN GAP), and the root's output is 0.</item>
    /// <item><c>self-path</c>: the chain is <c>F</c>'s own members (qualified with <c>F</c> by its member solve) and
    /// <c>X = F.P{K}</c>, inside <c>F</c>, reads the last one through <c>F</c>'s name: the owner is on the reader's
    /// chain and not bound, so <c>X</c> requires every <c>p{i}</c>.</item>
    /// <item><c>path</c> (NEGATIVE CONTROL): <c>rows</c> whose members also read <c>Q.X{i}</c>, a path in every part.</item>
    /// </list>
    /// </summary>
    internal static string OwnerQualifiedRows(int members, string shape = "rows")
    {
        var parameters = string.Join(", ", Enumerable.Range(1, members).Select(i => $"p{i}"));
        var arguments = string.Join(", ", Enumerable.Range(1, members));
        var path = shape == "path";
        var library = new StringBuilder("Lib = {\n");
        library.Append(shape == "outer-name" ? "public P1 = p1 + y\n" : path ? "public P1 = p1 + Q.X1\n" : "public P1 = p1\n");
        for (var i = 2; i <= members; i++) library.Append(path ? $"public P{i} = P{i - 1} + p{i} + Q.X{i}\n" : $"public P{i} = P{i - 1} + p{i}\n");
        library.Append("}\n");
        var rows = string.Concat(Enumerable.Range(1, members).Select(i => $"Lib.P{i}\n"));
        return shape switch
        {
            "rows" => $"F({parameters}) = {{\n{library}{rows}}}\nF({arguments})\n",
            "same-names" => $"F({parameters}) = {{\nG({parameters}) = {{\n{library}{rows}}}\nG({arguments})\n}}\nF({arguments})\n",
            "one-name" => $"F({parameters}) = {{\nG(p2) = {{\n{library}{rows}}}\nG(100)\n}}\nF({arguments})\n",
            "outer-name" => $"H(y) = {{\nF({parameters}) = {{\n{library}{rows}}}\nF({arguments})\n}}\nH(5)\n",
            "detached" => $"F({parameters}) = {{\n{library}0\n}}\n"
                + string.Concat(Enumerable.Range(1, members).Select(i => $"R{i} = F.Lib.P{i}\n")) + "0\n",
            "self-path" => $"F({parameters}) = {{\nP1 = p1\n"
                + string.Concat(Enumerable.Range(2, members - 1).Select(i => $"P{i} = P{i - 1} + p{i}\n"))
                + $"X = F.P{members}\nX\n}}\nF({arguments})\n",
            "path" => $"F(y, {parameters}) = {{\nQ = {{\n"
                + string.Concat(Enumerable.Range(1, members).Select(i => $"public X{i} = y + {i}\n"))
                + $"}}\n{library}{rows}}}\nF(7, {arguments})\n",
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        };
    }

    // ── Live reads: the unbound open walks past sixteen live summaries ────────

    /// <summary>
    /// Readers with bound owners take the level's ONE unbound open-walk settlement however many summaries of the level in
    /// progress it read: seventeen or more, the former cap, too. Formerly every reader settled it again, M² + 6M + 1 frames
    /// at M readers of M caps (10,601 / 41,201 / 162,401 at 100 / 200 / 400), and 22 frames per reader once the walks read
    /// seventeen. Each reuse compares every summary the walks read (one unit of static work each). The per-reader settlement
    /// (C1 off) and the unshared one publish the same metadata, and every reader requires <c>y</c>.
    /// </summary>
    [Fact]
    public void OpenWalksReadingManyLiveSummaries_AreSettledOnceForEveryReader()
    {
        var frames = new long[3];
        var sizes = new[] { 20, 40, 80 };
        for (var k = 0; k < sizes.Length; k++)
        {
            var source = LiveOpenFamily(sizes[k], sizes[k]);
            var (production, perReader) = AssertSameAsFormerWalk(source, PropertyExposureResolver.OpenWalksPerReaderForTesting);
            Assert.Equal(1, Assert.Single(production.OpenWalksSettlements.Values));
            Assert.Equal(0, production.OpenWalksSettlementsWithBoundOwners);
            Assert.True(production.SettlementLiveReadChecks >= (long)(sizes[k] - 1) * sizes[k]);
            var root = Root(source);
            for (var i = 0; i < sizes[k]; i++)
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", $"A{i}"), ("y", 0));
            frames[k] = production.RequiredAncestorSettlementFrames;
            output.WriteLine($"M = C = {sizes[k]}: {frames[k]} frames, {production.SettlementLiveReadChecks} live checks; per reader {perReader.RequiredAncestorSettlementFrames} frames");
        }

        AssertLinear(frames, "frames");
        Assert.Equal("0", Value(LiveOpenFamily(20, 20)));
    }

    /// <summary>The former cliff at sixteen live reads: one more summary adds a constant number of frames, not 22 per reader.</summary>
    [Fact]
    public void SeventeenLiveSummaries_CostWhatSixteenDo_PlusOneFrame()
    {
        var sixteen = Parse(LiveOpenFamily(64, 16)).Observations;
        var seventeen = Parse(LiveOpenFamily(64, 17)).Observations;
        Assert.InRange(seventeen.RequiredAncestorSettlementFrames - sixteen.RequiredAncestorSettlementFrames, 0, 4);
        Assert.Equal(1, Assert.Single(seventeen.OpenWalksSettlements.Values));
    }

    [Fact]
    public void DeclinedLiveMemberSettlements_DoNotCopySummarySnapshots()
    {
        var source = LiveMemberFamily(20, 20);
        var kept = Parse(source);
        var declined = InMode(Mode.Unshared, () => Parse(source));
        Assert.Empty(kept.Diagnostics);
        Assert.Equal(kept.Diagnostics, declined.Diagnostics);
        Assert.Equal(kept.Metadata, declined.Metadata);
        Assert.True(kept.Observations.SettlementSnapshotNames >= 20);
        Assert.Equal(0, declined.Observations.SettlementSnapshotNames);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(3)]
    public void SaturatedReuseTables_FallBackToTheSameExposure(int capacity)
    {
        var seam = PropertyExposureResolver.ResidualCacheCapacityForTesting;
        foreach (var (source, kind) in new[]
        {
            (LiveOpenFamily(20, 24), "live"), (LiveMemberFamily(20, 24), "live"), (NavigatedChain(48, depth: 2), "names"),
            (OwnerQualifiedRows(48), "qualified"), (OwnerQualifiedRows(48, "one-name"), "qualified"),
            (OwnerQualifiedRows(48, "detached"), "qualified"),
        })
        {
            var normal = Parse(source);
            Assert.Empty(normal.Diagnostics);
            var prior = seam.Value;
            seam.Value = capacity;
            try
            {
                var limited = Parse(source);
                Assert.Equal(normal.Diagnostics, limited.Diagnostics);
                Assert.Equal(normal.Metadata, limited.Metadata);
                if (capacity == 0 && kind == "live")
                {
                    Assert.True(limited.Observations.SettlementSnapshotNames < normal.Observations.SettlementSnapshotNames);
                    Assert.True(limited.Observations.RequiredAncestorSettlementFrames > normal.Observations.RequiredAncestorSettlementFrames);
                }
                if (kind == "names")
                    Assert.True(limited.Observations.RequiredAncestorElementsCanonicalized > normal.Observations.RequiredAncestorElementsCanonicalized);
                if (kind == "qualified")
                {
                    // QUALIFIED SEED PARTS: with no room every seed is expanded and folded as before.
                    Assert.True(normal.Observations.SettlementQualifiedPartOwnerLookups > 0);
                    Assert.True(limited.Observations.SettlementQualifiedPartOwnerLookups < normal.Observations.SettlementQualifiedPartOwnerLookups);
                    if (capacity == 0)
                    {
                        Assert.Equal(0, limited.Observations.SettlementQualifiedPartCopies);
                        Assert.Equal(0, limited.Observations.SettlementQualifiedPartOwnerLookups);
                    }
                }
            }
            finally { seam.Value = prior; }
        }
    }

    // ── Live reads: what the live-read interner holds ─────────────────────────

    /// <summary>
    /// THE INTERNER'S BOUND (2026-11-25). Readers whose members read distinct, overlapping windows of the level's
    /// properties make the live-read interner build a different set for every member, path by path, and memoize the
    /// unions of nested sets, whether or not any settlement is then kept: its entries grow faster than the readers. Every
    /// entry it creates is one unit of static work, counted apart from the names copied into kept snapshots (and charged:
    /// <see cref="ExposureSettlementFrameChargeTests"/>), also with no live settlement admitted (the per-run walk). Under a
    /// capacity it never holds more than that capacity plus the entries of the one operation that crossed it; it then
    /// saturates, the level's later settlements record their live reads as unknown and are reused only inside their Run,
    /// and the metadata is unchanged. Every reader requires <c>y</c>.
    /// </summary>
    [Fact]
    public void OverlappingLiveReadSets_ChargeEveryInternerEntry_AndHoldTheInternerToItsCapacity()
    {
        const int Capacity = 512;
        var sizes = new[] { 24, 48, 96 };
        var peaks = new long[sizes.Length];
        var seam = PropertyExposureResolver.ResidualCacheCapacityForTesting;
        for (var k = 0; k < sizes.Length; k++)
        {
            var source = OverlappingLiveReads(sizes[k], sizes[k] / 2);
            var (production, perRun) = AssertSameAsFormerWalk(source, PropertyExposureResolver.LiveSettlementsPerRunForTesting);
            Assert.Equal(0, production.SettlementLiveNameSaturations);
            Assert.InRange(production.SettlementLiveNamePeakEntries, sizes[k], production.SettlementLiveNameEntries);
            Assert.True(perRun.SettlementLiveNameEntries >= sizes[k]);
            Assert.True(perRun.SettlementSnapshotNames < production.SettlementSnapshotNames);
            peaks[k] = production.SettlementLiveNamePeakEntries;
            var root = Root(source);
            for (var i = 0; i < sizes[k]; i++)
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", $"A{i}"), ("y", 0));

            var uncapped = Parse(source).Metadata;
            var prior = seam.Value;
            seam.Value = Capacity;
            try
            {
                var limited = Parse(source);
                Assert.Equal("", limited.Diagnostics);
                Assert.Equal(uncapped, limited.Metadata);
                // At most the capacity, plus one operation: a name's path, or a union of two sets of at most every name.
                Assert.InRange(limited.Observations.SettlementLiveNamePeakEntries, 1, Capacity + 8L * sizes[k] + 64);
                Assert.Equal(peaks[k] > Capacity ? 1 : 0, limited.Observations.SettlementLiveNameSaturations);
                output.WriteLine($"K = {sizes[k]}, window {sizes[k] / 2}: peak {peaks[k]} entries, {production.SettlementLiveNameEntries} created "
                    + $"({perRun.SettlementLiveNameEntries} with none admitted), {production.SettlementSnapshotNames} snapshot names; "
                    + $"capped at {Capacity}: peak {limited.Observations.SettlementLiveNamePeakEntries}, "
                    + $"{limited.Observations.SettlementLiveNameSaturations} saturated, {limited.Observations.RequiredAncestorSettlementFrames} frames "
                    + $"(uncapped {production.RequiredAncestorSettlementFrames})");
            }
            finally { seam.Value = prior; }
        }

        // The entries grow faster than the readers: doubling them more than doubles the peak.
        Assert.True(peaks[2] > 2 * peaks[1] && peaks[1] > 2 * peaks[0], string.Join(", ", peaks));
    }

    /// <summary>
    /// SATURATION AT ANY POINT. Whatever its capacity, the level solve whose live-read interner fills takes the ordinary
    /// settlement from there on, while a settlement kept before that is still validated against every summary it named:
    /// the metadata is the uncapped one. The witnesses: the live open walks, the live member, distinct overlapping read
    /// sets, and a summary that changes after a reader took a kept settlement (<see cref="StaleSummaryWitness"/>), whose
    /// readers all still require <c>w</c>: the level's record of what its readers read never depends on the interner.
    /// Over the sweep, some capacity keeps a live settlement, saturates later, and finds that settlement stale.
    /// </summary>
    [Fact]
    public void SaturatingTheLiveNameInterner_AtAnyPoint_KeepsTheSameExposure()
    {
        var seam = PropertyExposureResolver.ResidualCacheCapacityForTesting;
        var keptSaturatedAndStale = false;
        foreach (var source in new[] { LiveOpenFamily(20, 24), LiveMemberFamily(20, 24), OverlappingLiveReads(16, 8), StaleSummaryWitness })
        {
            var normal = Parse(source);
            Assert.Empty(normal.Diagnostics);
            Assert.Equal(0, normal.Observations.SettlementLiveNameSaturations);
            var saturated = 0;
            foreach (var capacity in Enumerable.Range(1, 16).Concat(Enumerable.Range(5, 8).Select(static power => 1 << power)))
            {
                var prior = seam.Value;
                seam.Value = capacity;
                try
                {
                    var snapshots = new HashSet<object>(ReferenceEqualityComparer.Instance);
                    var trace = new FrontEndTraversalObservations
                    {
                        LiveSnapshotStoredBeforeSaturation = snapshot => snapshots.Add(snapshot),
                        LiveSnapshotStaleAfterSaturation = snapshot => keptSaturatedAndStale |=
                            source == StaleSummaryWitness && snapshots.Contains(snapshot),
                    };
                    var limited = Parse(source, trace);
                    Assert.Equal(normal.Diagnostics, limited.Diagnostics);
                    Assert.Equal(normal.Metadata, limited.Metadata);
                    var observed = limited.Observations;
                    if (observed.SettlementLiveNameSaturations > 0)
                    {
                        saturated++;
                        Assert.True(observed.SettlementLiveNamePeakEntries > capacity);
                    }
                    else
                    {
                        Assert.InRange(observed.SettlementLiveNamePeakEntries, 0, capacity);
                    }
                }
                finally { seam.Value = prior; }
            }

            Assert.True(saturated > 0);
        }

        Assert.True(keptSaturatedAndStale);
        var root = Root(StaleSummaryWitness);
        var previous = seam.Value;
        seam.Value = 1;
        try
        {
            var limitedRoot = Root(StaleSummaryWitness);
            foreach (var reader in new[] { "A0", "A1", "Cap", "K" })
            {
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "G", "F", reader), ("w", 1));
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(limitedRoot, "G", "F", reader), ("w", 1));
            }
        }
        finally { seam.Value = previous; }
    }

    /// <summary>
    /// CANCELLATION while the live-read interner grows: the first settlement frame after it created entries cancels the
    /// operation, which surfaces with its token and fails the unit, and no entry is created or charged after it. A fresh
    /// parse of the same source then exposes in full with the uncancelled metadata: nothing of the cancelled solve is
    /// left behind.
    /// </summary>
    [Fact]
    public void CancellationWhileLiveNamesGrow_StopsTheSolve_AndAFreshParseExposesInFull()
    {
        var source = OverlappingLiveReads(48, 24);
        var expected = Parse(source);
        using var cancellation = new CancellationTokenSource();
        long entriesAtCancel = -1;
        FrontEndTraversalObservations observations = null!;
        observations = new FrontEndTraversalObservations
        {
            CheckpointReached = (kind, _) =>
            {
                if (kind != FrontEndCancellationCheckpoint.ExposureSettlementFrame || cancellation.IsCancellationRequested
                    || observations.SettlementLiveNameEntries == 0)
                    return;
                entriesAtCancel = observations.SettlementLiveNameEntries;
                cancellation.Cancel();
            },
        };

        var (resolved, ledger, _) = ExposureSettlementFrameChargeTests.Resolved(source);
        var unit = resolved.CompletedStructure!.Facts;
        var error = Assert.ThrowsAny<OperationCanceledException>(
            () => PropertyExposureResolver.Resolve(resolved, observations, cancellationToken: cancellation.Token));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.True(unit.IsFailed);
        Assert.False(unit.IsSealed);
        Assert.True(entriesAtCancel > 0);
        Assert.Equal(entriesAtCancel, observations.SettlementLiveNameEntries);
        Assert.InRange(ledger.WorkCharged, entriesAtCancel, long.MaxValue);

        var again = Parse(source);
        Assert.Equal(expected.Diagnostics, again.Diagnostics);
        Assert.Equal(expected.Metadata, again.Metadata);
        Assert.Equal(expected.Observations.SettlementLiveNameEntries, again.Observations.SettlementLiveNameEntries);
    }

    [Fact]
    public void AUnionOfInterleavedLiveReadSets_ObservesCancellationInsideTheUnion()
    {
        using var cancellation = new CancellationTokenSource();
        var observations = new FrontEndTraversalObservations
        {
            CheckpointReached = (kind, ordinal) =>
            {
                if (kind == FrontEndCancellationCheckpoint.ExposureLiveNameUnion && ordinal == 3)
                    cancellation.Cancel();
            },
        };
        var interner = new PropertyExposureResolver.LiveReadNameInterner(observations, cancellation.Token);
        var even = NameSetInterner.Empty;
        var odd = NameSetInterner.Empty;
        for (var i = 0; i < 128; i++)
        {
            even = interner.WithName(even, $"Even{i}");
            odd = interner.WithName(odd, $"Odd{i}");
        }
        var error = Assert.Throws<OperationCanceledException>(() => interner.Union(even, odd));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal(3, observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.ExposureLiveNameUnion));
    }

    // ── Live settlements: other settlements that read live summaries ─────────

    /// <summary>
    /// A member that lists W of the level's properties, read by K readers with bound owners through a written path or
    /// through an <c>open</c>, is settled once and taken by every other reader while those summaries stand: the frames grow
    /// linearly (formerly K × W: 10,300 / 40,600 / 161,200 at K = W = 100 / 200 / 400 through the path). The former walk
    /// (each reader settles it in its own Run) and the unshared settlement publish the same metadata, every reader requires
    /// <c>y</c>, and the program's value is unchanged.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AMemberReadingManyLiveSummaries_IsSettledOnceForEveryReader(bool opened)
    {
        var frames = new long[3];
        var former = new long[3];
        var sizes = new[] { 20, 40, 80 };
        for (var k = 0; k < sizes.Length; k++)
        {
            var source = LiveMemberFamily(sizes[k], sizes[k], opened);
            var (production, perRun) = AssertSameAsFormerWalk(source, PropertyExposureResolver.LiveSettlementsPerRunForTesting);
            Assert.True(production.SettlementLiveHits >= sizes[k] - 1);
            Assert.Equal(0, perRun.SettlementLiveHits);
            var root = Root(source);
            for (var i = 0; i < sizes[k]; i++)
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", $"A{i}"), ("y", 0));
            frames[k] = production.RequiredAncestorSettlementFrames;
            former[k] = perRun.RequiredAncestorSettlementFrames;
            output.WriteLine($"K = W = {sizes[k]}: {frames[k]} frames ({production.SettlementLiveHits} live hits, {production.SettlementLiveReadChecks} checks); former walk {former[k]}");
        }

        AssertLinear(frames, "frames");
        // The former walk is quadratic: doubling K and W about quadruples it.
        Assert.InRange((double)former[2] / former[1], 3.0, 5.0);
        Assert.Equal("6", Value(LiveMemberFamily(20, 20, opened)));
    }

    /// <summary>
    /// NEGATIVE CONTROL (a summary the kept settlement read changes). <c>K</c> reads both readers, so they are settled first,
    /// while <c>Cap</c>'s summary is still empty: <c>A0</c> settles <c>Lib.V</c> and <c>A1</c> takes it, which records
    /// <c>A1</c>'s read of <c>Cap</c>. <c>Cap</c> then gains <c>w</c> through <c>K</c>, both readers are evaluated again,
    /// and the kept settlement no longer stands: it is dropped and settled again, and only then does each reader require
    /// <c>w</c>. Taken unchecked, or without recording its read, it leaves a reader without <c>w</c>.
    /// </summary>
    [Fact]
    public void AKeptLiveSettlement_IsSettledAgainWhenASummaryItReadChanges()
    {
        const string Source = StaleSummaryWitness;
        var (production, _) = AssertSameAsFormerWalk(Source, PropertyExposureResolver.LiveSettlementsPerRunForTesting);
        Assert.True(production.SettlementLiveHits > 0);
        Assert.True(production.SettlementShareStaleViews > 0);
        var root = Root(Source);
        foreach (var reader in new[] { "A0", "A1", "Cap", "K" })
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "G", "F", reader), ("w", 1));
    }

    /// <summary>
    /// NEGATIVE CONTROL (bound owners). <c>Lib.V</c> lists a live summary and <c>F</c>'s parameter <c>y</c>. The readers
    /// <c>A{i}(z)</c> settle it without <c>F</c> bound, so it charges <c>y</c>; <c>F</c>'s own output row reads it with
    /// <c>F</c> bound, where <c>y</c> is supplied. The kept settlement records that membership with its answer, so neither
    /// answers the other: the metadata is the former walk's and the unshared one's, and every reader requires <c>y</c>.
    /// </summary>
    [Fact]
    public void AKeptLiveSettlement_AnswersOnlyBoundOwnersThatGiveItsMembershipsTheSameAnswers()
    {
        var source = new StringBuilder("F(y) = {\n  Lib = {\n    public V = [Cap, y]\n  }\n  Cap = 2\n");
        for (var i = 0; i < 8; i++) source.Append($"  A{i}(z) = Lib.V[1] + z\n");
        source.Append("  Lib.V[1] + Lib.V[0] + A0(1)\n}\nF(5)\n");
        var text = source.ToString();
        var (production, _) = AssertSameAsFormerWalk(text, PropertyExposureResolver.LiveSettlementsPerRunForTesting);
        Assert.True(production.SettlementLiveHits > 0);
        var root = Root(text);
        for (var i = 0; i < 8; i++)
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", $"A{i}"), ("y", 0));
        Assert.Equal("13", Value(text));
    }

    /// <summary>
    /// NEGATIVE CONTROL (bound owners, a fuzz witness). Program <c>g22_00156</c> of the audit's generator (seed 22), kept
    /// verbatim: it elaborates fully with one <c>UndeclaredIdentifier</c>, and a settlement that read a live summary is kept
    /// and later met under bound owners its footprint refuses. Taken there regardless (the footprint test removed), the
    /// reusing frame records one owner with two answers and the front end throws; in 409 of the 24,000 fuzz programs it
    /// does. With the test, the diagnostics and metadata are the former walk's and the unshared settlement's.
    /// </summary>
    [Fact]
    public void AKeptLiveSettlement_IsNotTakenUnderBoundOwnersItsFootprintRefuses()
    {
        const string Source = "C(0) = B - M\nC(x) = Y.X(x) + Q(X) + C(Y(L(x))) - 0\nL(q) = {\n  C = {\n    Q(p) = Y(M({ N(q) }))\n"
            + "    Q.X * { N } + { N(Q) }\n  }\n  M = Y.N\n  Q - q * 5 - Q.N.C * Y.L\n}\nP = L.C\nN = { C } + L\nQ(z, q) = 3\n5 + P.B.Y\n";
        var (production, _) = AssertSameAsFormerWalk(Source, PropertyExposureResolver.LiveSettlementsPerRunForTesting, clean: false);
        Assert.True(production.SettlementLiveHits > 0);
        Assert.Contains(nameof(DiagnosticCode.UndeclaredIdentifier), Parse(Source).Diagnostics, StringComparison.Ordinal);
    }

    /// <summary>
    /// NEGATIVE CONTROL (an owner lookup off the site's chain). <c>Lib.V</c> lists a live summary and <c>Off.G</c>, whose
    /// requirement's owner <c>Off</c> is on no level of the readers' chain. Such a settlement answers its exact key only
    /// (THE OFF-CHAIN GAP), and so does every one that reaches it, so neither <c>Lib.V</c> nor its seed is ever kept live:
    /// every reader settles them in its own Run, and the frames are exactly the former walk's (kept, they would answer
    /// every later reader in one frame). Only the nested read of <c>Cap</c>, which made no such lookup, is kept and taken.
    /// </summary>
    [Fact]
    public void ALiveSettlementWithAnOffChainLookup_IsNeverKept()
    {
        var source = new StringBuilder("Off(q) = {\n  public G = q + 1\n  0\n}\nF(y) = {\n  Lib = {\n    public V = [Cap, Off.G]\n  }\n  Cap = y\n");
        for (var i = 0; i < 8; i++) source.Append($"  A{i}(z) = Lib.V[0] + z\n");
        source.Append("  A0(1)\n}\nF(5)\n");
        var text = source.ToString();
        var (production, perRun) = AssertSameAsFormerWalk(text, PropertyExposureResolver.LiveSettlementsPerRunForTesting);
        Assert.Equal(perRun.RequiredAncestorSettlementFrames, production.RequiredAncestorSettlementFrames);
        Assert.True(production.SettlementLiveHits > 0);
        Assert.Equal("6", Value(text));
    }

    // ── Seed parts: navigated members whose seeds hold their predecessors ─────

    /// <summary>
    /// Reader <c>R{i}</c> of <c>Lib.P{i}</c> requires exactly <c>p1</c> … <c>p{i}</c> (independent oracle; published in
    /// ordinal order), with SEED PARTS and with every seed folded whole (the former walk), and the unshared settlement
    /// agrees.
    /// </summary>
    [Theory]
    [InlineData(0)]
    [InlineData(3)]
    public void NavigatedChainReaders_RequireExactlyTheirPrefix(int depth)
    {
        const int Members = 12;
        var source = NavigatedChain(Members, depth);
        AssertSameAsFormerWalk(source, PropertyExposureResolver.SeedPartsFoldedForTesting);
        var root = Root(source);
        for (var i = 1; i <= Members; i++)
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", $"R{i}"),
                Enumerable.Range(1, i).Select(p => $"p{p}").Order(StringComparer.Ordinal).Select(name => (name, 0)).ToArray());
        Assert.Equal((Members * (Members + 1) / 2).ToString(), Value(source));
    }

    /// <summary>
    /// The width a navigated member's seed holds by reference is resolved once per part and level: the requirement elements
    /// canonicalized, and the seed-part work, grow linearly with the members (formerly K² / 2 + 3K / 2 elements: 125,750 /
    /// 501,500 / 2,003,000 at 500 / 1,000 / 2,000), while the former walk stays quadratic.
    /// </summary>
    [Fact]
    public void NavigatedChain_CanonicalizesItsRequirementsInLinearWork()
    {
        var canonical = new long[3];
        var parts = new long[3];
        var former = new long[3];
        var sizes = new[] { 100, 200, 400 };
        for (var k = 0; k < sizes.Length; k++)
        {
            var (production, folded) = AssertSameAsFormerWalk(NavigatedChain(sizes[k]), PropertyExposureResolver.SeedPartsFoldedForTesting);
            canonical[k] = production.RequiredAncestorElementsCanonicalized;
            parts[k] = production.SettlementSeedPartWork;
            former[k] = folded.RequiredAncestorElementsCanonicalized;
            Assert.Equal(0, folded.SettlementSeedPartWork);
            output.WriteLine($"K = {sizes[k]}: {canonical[k]} elements canonicalized, {parts[k]} seed-part units; folded {former[k]}");
        }

        AssertLinear(canonical, "elements");
        AssertLinear(parts, "seed parts");
        Assert.InRange((double)former[2] / former[1], 3.0, 5.0);
    }

    /// <summary>
    /// A navigated member's seed holds no name and no path, so every parameterless block between the library and the
    /// reader expands it to the same content: it is carried through unchanged. The summary channel's expansions (one
    /// cancellation checkpoint each) no longer grow with depth × members, and the published metadata is the former walk's.
    /// </summary>
    [Fact]
    public void ANavigatedMemberBelowParameterlessBlocks_IsCarriedThroughUnchanged()
    {
        const int Members = 64;
        var shallow = AssertSameAsFormerWalk(NavigatedChain(Members, depth: 2), PropertyExposureResolver.SeedPartsFoldedForTesting);
        var deep = AssertSameAsFormerWalk(NavigatedChain(Members, depth: 16), PropertyExposureResolver.SeedPartsFoldedForTesting);
        long Expansions(FrontEndTraversalObservations observations) => observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel);
        // Fourteen more levels cost a constant number of expansions per level, not one per member and level.
        Assert.InRange(Expansions(deep.Production) - Expansions(shallow.Production), 0, 14L * 8);
        Assert.True(Expansions(deep.Former) - Expansions(shallow.Former) >= 14L * Members);
    }

    /// <summary>
    /// What a part holds decides its route. Here each member also reads a navigated path (<c>Q.X{i}</c>, a pending
    /// reference in every part: a NEGATIVE CONTROL), or the library binds a parameter of its own (<c>q</c>, an
    /// owner-qualified requirement in every part). Parts with paths are folded and settled whole, as before, and every
    /// reader requires the path's input. Parts with owner-qualified requirements take QUALIFIED SEED PARTS: <c>Lib</c>,
    /// the owner of <c>q</c>, is on no level of the readers' chain, so it is looked up once per settlement, charges
    /// nothing and is noted off-chain exactly as the folded settlement noted it per requirement, and every reader keeps
    /// its own prefix of the <c>p{i}</c>. Taking either part through its names alone would drop those requirements.
    /// </summary>
    [Theory]
    [InlineData("path")]
    [InlineData("library-parameter")]
    public void SeedPartsHoldingPathsOrQualifiedRequirements_SettleAsTheFormerWalk(string shape)
    {
        const int Members = 24;
        var source = new StringBuilder("F(y, " + string.Join(", ", Enumerable.Range(1, Members).Select(i => $"p{i}")) + ") = {\n");
        source.Append("Q = {\n" + string.Concat(Enumerable.Range(1, Members).Select(i => $"public X{i} = y + {i}\n")) + "}\n");
        source.Append(shape == "path" ? "Lib = {\npublic P1 = p1 + Q.X1\n" : "Lib(q) = {\npublic P1 = p1 + q\n");
        for (var i = 2; i <= Members; i++)
            source.Append(shape == "path" ? $"public P{i} = P{i - 1} + p{i} + Q.X{i}\n" : $"public P{i} = P{i - 1} + p{i}\n");
        source.Append("0\n}\n");
        for (var i = 1; i <= Members; i++) source.Append($"R{i} = Lib.P{i}\n");
        source.Append($"0\n}}\nF(7, {string.Join(", ", Enumerable.Range(1, Members))})\n");
        var text = source.ToString();
        var (production, _) = AssertSameAsFormerWalk(text, PropertyExposureResolver.SeedPartsFoldedForTesting);
        var root = Root(text);
        var last = ExposureOpenChainComplexityTests.Member(root, "F", $"R{Members}");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, last.Exposure);
        if (shape == "path")
            Assert.Contains("y", last.RequiredAncestorParameters);
        else
            ExposureOpenChainComplexityTests.AssertRequires(last,
                Enumerable.Range(1, Members).Select(static i => $"p{i}").Order(StringComparer.Ordinal).Select(static name => (name, 0)).ToArray());
        Assert.Contains($"p{Members}", last.RequiredAncestorParameters);
        Assert.Equal(shape != "path", production.SettlementQualifiedPartOwnerLookups > 0);
        Assert.Equal("0", Value(text));
    }

    /// <summary>
    /// NEGATIVE CONTROL (a part that holds paths). <c>P1</c> reads nine navigated paths, so its seed is held BY REFERENCE
    /// by every later member (a completed seed of more than <c>CopiedCompletedEntries</c> entries), and the part each of
    /// them holds carries pending references. Such a part is not taken through its names: the seed is folded and its paths
    /// settled, so every reader requires <c>y</c> through them. Taking the part through its names alone would drop them.
    /// </summary>
    [Fact]
    public void ASeedPartHoldingPaths_IsSettledWhole()
    {
        const int Members = 24;
        var source = new StringBuilder("F(y, " + string.Join(", ", Enumerable.Range(1, Members).Select(i => $"p{i}")) + ") = {\n");
        for (var k = 1; k <= 9; k++) source.Append($"Q{k} = {{ public X = y + {k} }}\n");
        source.Append("Lib = {\npublic P1 = p1 + " + string.Join(" + ", Enumerable.Range(1, 9).Select(k => $"Q{k}.X")) + "\n");
        for (var i = 2; i <= Members; i++) source.Append($"public P{i} = P{i - 1} + p{i}\n");
        source.Append("}\n");
        for (var i = 1; i <= Members; i++) source.Append($"R{i} = Lib.P{i}\n");
        source.Append($"0\n}}\nF(7, {string.Join(", ", Enumerable.Range(1, Members))})\n");
        var text = source.ToString();
        AssertSameAsFormerWalk(text, PropertyExposureResolver.SeedPartsFoldedForTesting);
        var root = Root(text);
        for (var i = 1; i <= Members; i++)
            Assert.Contains("y", ExposureOpenChainComplexityTests.Member(root, "F", $"R{i}").RequiredAncestorParameters);
        Assert.Equal("0", Value(text));
    }

    /// <summary>
    /// NEGATIVE CONTROLS (the levels between the library and the reader). A seed is carried through an intervening level
    /// unchanged only when that level binds no parameter and the seed holds no name or path. Here the outer intervening
    /// block binds <c>p3</c> itself, so the members' <c>p3</c> is qualified at that block (whose activation no reader holds)
    /// instead of reaching <c>F</c>'s; or the members read <c>Q.X</c> and the inner block declares its own <c>Q</c>, which
    /// that level selects instead of <c>F</c>'s. Those seeds are expanded at every level as before: the metadata is the
    /// former walk's, the readers do not require <c>F</c>'s <c>p3</c>, and none requires <c>F</c>'s <c>y</c> through
    /// <c>F</c>'s <c>Q</c>. Carried through, they would.
    /// </summary>
    [Theory]
    [InlineData("parameter")]
    [InlineData("path")]
    public void InterveningLevelsThatBindOrAnchor_ExpandTheSeedAsBefore(string shape)
    {
        const int Members = 16;
        var source = new StringBuilder($"F(y, {string.Join(", ", Enumerable.Range(1, Members).Select(i => $"p{i}"))}) = {{\n");
        source.Append("Q = { public X = y + 1 }\n");
        source.Append(shape == "parameter" ? "W1(p3) = {\n" : "W1 = {\n");
        source.Append("W2 = {\n");
        if (shape == "path")
            source.Append("Q = { public X = 1 }\n");
        source.Append("Lib = {\npublic P1 = p1\n");
        for (var i = 2; i <= Members; i++)
            source.Append(shape == "path" ? $"public P{i} = P{i - 1} + p{i} + Q.X\n" : $"public P{i} = P{i - 1} + p{i}\n");
        source.Append("}\n0\n}\n0\n}\n");
        for (var i = 1; i <= Members; i++) source.Append($"R{i} = W1.W2.Lib.P{i}\n");
        source.Append($"0\n}}\nF(7, {string.Join(", ", Enumerable.Range(1, Members))})\n");
        var text = source.ToString();
        AssertSameAsFormerWalk(text, PropertyExposureResolver.SeedPartsFoldedForTesting);
        var last = ExposureOpenChainComplexityTests.Member(Root(text), "F", $"R{Members}");
        Assert.Contains($"p{Members}", last.RequiredAncestorParameters);
        Assert.DoesNotContain("y", last.RequiredAncestorParameters);
        if (shape == "parameter")
            Assert.DoesNotContain("p3", last.RequiredAncestorParameters);
        Assert.Equal("0", Value(text));
    }

    /// <summary>
    /// NEGATIVE CONTROL (a seed holding paths at an intervening level, a fuzz witness). Program <c>f11_00254</c> of the
    /// audit's generator (seed 11), kept verbatim: it elaborates fully with one <c>DuplicateProperty</c>, and anchoring
    /// passes seeds holding pending references through levels that bind no parameter. Carried through unchanged there
    /// (the path test removed), <c>M</c> and its members would require <c>C</c>, <c>L</c> and <c>X</c> besides
    /// <c>x</c>; in 35 of the 24,000 fuzz programs the metadata changes. With the test, the diagnostics and metadata are
    /// the former walk's and the unshared settlement's.
    /// </summary>
    [Fact]
    public void ASeedHoldingPaths_IsExpandedAtEveryInterveningLevel_FuzzWitness()
    {
        const string Source = "Q = X + L + L + X - C\nM = {\n  A = Q.C\n  A = P(3) - M\n  N = A\n  public P = L.P.Q\n  P = N.Algorithm\n"
            + "  P * x\n}\nN = Y.Q\ny1, x0 = Y(B.Algorithm) - X.M.B - p - B * N.X.C, Y.N.M(A) - X\nL.Y.M - { M } - Q - B(x) * C\n";
        AssertSameAsFormerWalk(Source, PropertyExposureResolver.SeedPartsFoldedForTesting, clean: false);
        var m = Assert.Single(SourceProvenance.ParseAllowingDiagnostics(Source).Root.Properties, property => property.Name == "M");
        Assert.Equal(["x"], m.RequiredAncestorParameters);
    }

    // ── Qualified seed parts: parts that hold owner-qualified requirements ──────

    [Theory]
    [InlineData(19, 1)]
    [InlineData(20, 2)]
    public void AQualifiedCopyReservesItsChildReferences(int capacity, int expectedCopies)
    {
        // The first two completed parts each cost ten units. The second holds eight names,
        // its predecessor reference and its cache entry.
        var source = OwnerQualifiedRows(64);
        var former = With(PropertyExposureResolver.SeedPartsFoldedForTesting, () => Parse(source));
        var seam = PropertyExposureResolver.ResidualCacheCapacityForTesting;
        var prior = seam.Value;
        try
        {
            seam.Value = capacity;
            var actual = Parse(source);
            Assert.Empty(actual.Diagnostics);
            Assert.Equal(former.Metadata, actual.Metadata);
            Assert.Equal(expectedCopies, actual.Observations.SettlementQualifiedPartCopies);
        }
        finally { seam.Value = prior; }
    }

    [Fact]
    public void ADisjointQualificationObservesCancellationInsideTheNameSet()
    {
        using var cancellation = new CancellationTokenSource();
        var probes = 0;
        var watch = false;
        var comparer = EqualityComparer<string>.Create(StringComparer.Ordinal.Equals, name =>
        {
            if (watch && ++probes == 32)
                cancellation.Cancel();
            return StringComparer.Ordinal.GetHashCode(name);
        });
        var parameters = Enumerable.Range(0, 512).Select(i => $"p{i}").ToHashSet(comparer);
        var seed = new PropertyDependencyGraphBuilder.SummarySeed(Enumerable.Range(0, 512).Select(i => $"q{i}"));
        watch = true;
        var error = Assert.ThrowsAny<OperationCanceledException>(() => seed.SharedOwnNames(parameters, null, cancellation.Token));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.InRange(probes, 32, 256);
    }

    [Fact]
    public void AWideQualifiedPartKeepsEveryCaptureAcrossCancellationBatches()
    {
        var names = Enumerable.Range(1, 513).Select(i => $"p{i}").ToArray();
        var all = string.Join(", ", names);
        var chain = string.Join("\n", Enumerable.Range(2, 11).Select(i => $"P{i} = P{i - 1} + p{i}"));
        var source = $"H(y) = {{\nF({all}) = {{\nP1 = p1\n{chain}\nR = [{all}, P12]\nQ = [R, y]\nX = F.Q\n0\n}}\n"
            + $"F({string.Join(", ", Enumerable.Range(1, names.Length))})\n}}\nH(5)\n";
        var (production, _) = AssertSameAsFormerWalk(source, PropertyExposureResolver.SeedPartsFoldedForTesting);
        Assert.True(production.SettlementQualifiedPartOwnerLookups > 0);
        ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(Root(source), "H", "F", "X"),
            names.Order(StringComparer.Ordinal).Select(name => (name, 0)).Append(("y", 1)).ToArray());
    }

    /// <summary>
    /// The witnesses of what a QUALIFIED SEED PARTS settlement records (<see cref="AQualifiedSettlementsRecord_DecidesWhereItIsReused"/>).
    /// Inside <c>H(y)</c>, <c>F(p1, …, p{K})</c>'s own chain <c>P1</c> … <c>P{K}</c> ends in <c>R = p1 + … + p9 + P{K}</c> and
    /// <c>Q = R + y</c>: <c>R</c>'s own sets hold nine names, so <c>Q</c> holds it BY REFERENCE and <c>Q</c>'s own sets hold only
    /// <c>H</c>'s <c>y</c>. <c>F</c>'s requirements are in <c>Q</c>'s parts alone, so only the parts' record notes <c>F</c>, and
    /// two readers read <c>F.Q</c> under one share key (content, level, bound owners) or one footprint:
    /// <list type="bullet">
    /// <item><c>bound-then-found</c>: <c>F</c>'s output row <c>F.Q</c> is settled where <c>F</c> is declared, with <c>F</c>
    /// bound, then <c>X = F.Q</c> inside <c>F</c> reads it with <c>F</c> unbound and on its chain;</item>
    /// <item><c>off-chain-then-found</c>: <c>T = F.Q</c> in <c>H</c> finds <c>F</c> on no level of its chain, then
    /// <c>G(z) = F.Q + z</c> inside <c>F</c> reads it under the bound owner <c>G</c>;</item>
    /// <item><c>found-then-off-chain</c>: <c>X = F.Q</c> inside <c>F</c> lands at <c>F</c>'s level, then <c>Y = F.Q</c> in
    /// <c>S(w)</c>, a sibling of <c>F</c>, reads it off <c>F</c>'s chain.</item>
    /// </list>
    /// </summary>
    internal static string QualifiedRecordWitness(int members, string shape)
    {
        var parameters = string.Join(", ", Enumerable.Range(1, members).Select(i => $"p{i}"));
        var chain = new StringBuilder("P1 = p1\n");
        for (var i = 2; i <= members; i++) chain.Append($"P{i} = P{i - 1} + p{i}\n");
        chain.Append($"R = {string.Join(" + ", Enumerable.Range(1, 9).Select(i => $"p{i}"))} + P{members}\nQ = R + y\n");
        var (inside, beside) = shape switch
        {
            "bound-then-found" => ("X = F.Q\nF.Q\nX\n", ""),
            "off-chain-then-found" => ("G(z) = F.Q + z\nG(1)\n", "T = F.Q\n"),
            "found-then-off-chain" => ("X = F.Q\nX\n", "S(w) = {\nY = F.Q\nY + w\n}\n"),
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        };
        return $"H(y) = {{\nF({parameters}) = {{\n{chain}{inside}}}\n{beside}F({string.Join(", ", Enumerable.Range(1, members))})\n}}\nH(5)\n";
    }

    /// <summary>
    /// THE RECORD OF A QUALIFIED SETTLEMENT decides where it is reused, so it must be the folded settlement's: each owner's
    /// bound-owner membership with its answer, the landing of an owner found on the site's chain, and an owner found on no
    /// level of it (<see cref="QualifiedRecordWitness"/>). Without the membership, the settlement that discharged <c>F</c> as a
    /// bound owner would answer <c>X</c>, and <c>T</c>'s would answer <c>G</c>: both would lose every <c>p{i}</c>. Without the
    /// off-chain note, <c>T</c>'s settlement would be kept by footprint and answer <c>G</c>. Without the landing, <c>X</c>'s
    /// settlement would stand from every site and answer <c>Y</c>, which would require <c>F</c>'s names off its chain. The
    /// readers' requirements are checked against an independent oracle, production agrees with the former walk and the
    /// unshared settlement, the parts were taken owner by owner, and the values are unchanged.
    /// </summary>
    [Theory]
    [InlineData("bound-then-found")]
    [InlineData("off-chain-then-found")]
    [InlineData("found-then-off-chain")]
    public void AQualifiedSettlementsRecord_DecidesWhereItIsReused(string shape)
    {
        const int Members = 12;
        var source = QualifiedRecordWitness(Members, shape);
        var (production, _) = AssertSameAsFormerWalk(source, PropertyExposureResolver.SeedPartsFoldedForTesting);
        Assert.True(production.SettlementQualifiedPartOwnerLookups > 0);
        var root = Root(source);
        var throughF = Enumerable.Range(1, Members).Select(static i => $"p{i}").Order(StringComparer.Ordinal)
            .Select(static name => (name, 0)).Append(("y", 1)).ToArray();
        ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "H", "F"), ("y", 0));
        var q = Members * (Members + 1) / 2 + 45 + 5;
        switch (shape)
        {
            case "bound-then-found":
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "H", "F", "X"), throughF);
                Assert.Equal($"({q}, {q})", Value(source));
                break;
            case "off-chain-then-found":
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "H", "T"), ("y", 0));
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "H", "F", "G"), throughF);
                Assert.Equal($"{q + 1}", Value(source));
                break;
            case "found-then-off-chain":
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "H", "F", "X"), throughF);
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "H", "S"), ("y", 0));
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "H", "S", "Y"), ("y", 1));
                Assert.Equal($"{q}", Value(source));
                break;
        }
    }

    // The value of an owner call whose output rows are members 1 … members: one sequence value.
    private static string Rows(int members, Func<int, int> value)
        => $"({string.Join(", ", Enumerable.Range(1, members).Select(value))})";

    /// <summary>
    /// QUALIFIED SEED PARTS: the source report's <c>rows</c> fixture (<see cref="OwnerQualifiedRows"/>). While a row's
    /// member seed was anchored through <c>F</c>'s level, it was folded and every name qualified with <c>F</c>, and its
    /// settlement then read <c>F</c>'s bound-owner membership once per name: K² / 2 names folded, qualified and read
    /// (2,005,000 footprint reads and 404 MB of exposure allocation at K = 2,000). Now each part is qualified once and kept,
    /// and each settlement looks each owner up once: qualification probes, footprint reads, owner lookups, part copies and
    /// seed-part work grow linearly with the rows, the frames are unchanged, and the former walk
    /// (<see cref="PropertyExposureResolver.SeedPartsFoldedForTesting"/>) stays quadratic. The metadata is the former
    /// walk's and the unshared settlement's.
    /// </summary>
    [Fact]
    public void OwnerQualifiedRows_QualifyAndReadEveryPartOnce_InLinearWork()
    {
        var sizes = new[] { 100, 200, 400 };
        var probes = new long[3];
        var footprint = new long[3];
        var lookups = new long[3];
        var copies = new long[3];
        var parts = new long[3];
        var formerProbes = new long[3];
        var formerFootprint = new long[3];
        for (var k = 0; k < sizes.Length; k++)
        {
            var (production, former) = AssertSameAsFormerWalk(OwnerQualifiedRows(sizes[k]), PropertyExposureResolver.SeedPartsFoldedForTesting);
            Assert.Equal(former.RequiredAncestorSettlementFrames, production.RequiredAncestorSettlementFrames);
            Assert.Equal(0, former.SettlementQualifiedPartOwnerLookups);
            Assert.Equal(0, former.SettlementQualifiedPartCopies);
            probes[k] = production.SummaryQualificationProbes;
            footprint[k] = production.SettlementFootprintWork;
            lookups[k] = production.SettlementQualifiedPartOwnerLookups;
            copies[k] = production.SettlementQualifiedPartCopies;
            parts[k] = production.SettlementSeedPartWork;
            formerProbes[k] = former.SummaryQualificationProbes;
            formerFootprint[k] = former.SettlementFootprintWork;
            output.WriteLine($"K = {sizes[k]}: {production.RequiredAncestorSettlementFrames} frames, {probes[k]} qualification probes, "
                + $"{footprint[k]} footprint reads, {lookups[k]} owner lookups, {copies[k]} part copies, {parts[k]} seed-part units; "
                + $"folded {formerProbes[k]} probes, {formerFootprint[k]} footprint reads");
        }

        AssertLinear(probes, "qualification probes");
        AssertLinear(footprint, "footprint reads");
        AssertLinear(lookups, "owner lookups");
        AssertLinear(copies, "part copies");
        AssertLinear(parts, "seed-part work");
        Assert.InRange((double)formerProbes[2] / formerProbes[1], 3.0, 5.0);
        Assert.InRange((double)formerFootprint[2] / formerFootprint[1], 3.0, 5.0);
        Assert.Equal(Rows(12, i => i * (i + 1) / 2), Value(OwnerQualifiedRows(12)));
    }

    /// <summary>
    /// QUALIFIED SEED PARTS keep each requirement with its exact owner. A part's names are qualified with the innermost
    /// owner the anchoring passes that binds them, discharged where that owner is bound, and the names no passed owner
    /// binds stay required where the rows are settled (<see cref="OwnerQualifiedRows"/>): <c>rows</c> and
    /// <c>same-names</c> — the rows' owner requires nothing although <c>F</c> binds every name too; <c>one-name</c> —
    /// <c>G</c> requires <c>F</c>'s <c>p1</c>, <c>p3</c> … but not <c>p2</c>; <c>outer-name</c> — <c>F</c> requires
    /// <c>H</c>'s <c>y</c>. A name qualified with the wrong owner, or left unqualified, would be required of the wrong
    /// owner. Where the parts' owner is neither bound nor off the reader's chain (<c>self-path</c>, whose parts the member
    /// solve qualified), the requirements are the ones each part keeps for that owner's level: <c>X</c> requires every
    /// <c>p{i}</c>. Production, the former walk and the unshared settlement agree, the parts were taken owner by owner,
    /// and the values are unchanged.
    /// </summary>
    [Theory]
    [InlineData("rows")]
    [InlineData("same-names")]
    [InlineData("one-name")]
    [InlineData("outer-name")]
    [InlineData("self-path")]
    public void OwnerQualifiedParts_KeepEveryRequirementWithItsOwner(string shape)
    {
        const int Members = 24;
        var source = OwnerQualifiedRows(Members, shape);
        var (production, _) = AssertSameAsFormerWalk(source, PropertyExposureResolver.SeedPartsFoldedForTesting);
        Assert.Equal(shape != "self-path", production.SettlementQualifiedPartCopies > 0);
        Assert.True(production.SettlementQualifiedPartOwnerLookups > 0);
        var root = Root(source);
        switch (shape)
        {
            case "rows":
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F"));
                Assert.Equal(Rows(Members, i => i * (i + 1) / 2), Value(source));
                break;
            case "same-names":
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", "G"));
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F"));
                Assert.Equal(Rows(Members, i => i * (i + 1) / 2), Value(source));
                break;
            case "one-name":
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", "G"),
                    Enumerable.Range(1, Members).Where(static i => i != 2).Select(static i => $"p{i}").Order(StringComparer.Ordinal)
                        .Select(static name => (name, 0)).ToArray());
                Assert.Equal(Rows(Members, i => i * (i + 1) / 2 + (i >= 2 ? 98 : 0)), Value(source));
                break;
            case "outer-name":
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "H", "F"), ("y", 0));
                Assert.Equal(Rows(Members, i => i * (i + 1) / 2 + 5), Value(source));
                break;
            case "self-path":
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", "X"),
                    Enumerable.Range(1, Members).Select(static i => $"p{i}").Order(StringComparer.Ordinal).Select(static name => (name, 0)).ToArray());
                Assert.Equal((Members * (Members + 1) / 2).ToString(), Value(source));
                break;
        }
    }

    /// <summary>
    /// QUALIFIED SEED PARTS read without their owner (<c>detached</c>, <see cref="OwnerQualifiedRows"/>): root properties read
    /// <c>F.Lib.P{i}</c> without calling <c>F</c>, so the owner of the parts' requirements is on no level of the reader's
    /// chain. Each settlement notes that lookup once instead of once per requirement, charges nothing for it, and keeps it:
    /// such a result answers its exact key only (THE OFF-CHAIN GAP), so the exact-key share publishes the same metadata. The
    /// read stays a latent check: unused, the program's value is 0, and demanding <c>R{K}</c> fails with
    /// <c>LocalOnlyProperty</c>.
    /// </summary>
    [Fact]
    public void OwnerQualifiedPartsReadWithoutTheirOwner_ChargeNothing_AndKeepTheLatentCheck()
    {
        const int Members = 24;
        var source = OwnerQualifiedRows(Members, "detached");
        var (production, _) = AssertSameAsFormerWalk(source, PropertyExposureResolver.SeedPartsFoldedForTesting);
        Assert.True(production.SettlementQualifiedPartOwnerLookups > 0);
        Assert.Equal(Parse(source).Metadata, InMode(Mode.ExactBoundOwners, () => Parse(source)).Metadata);
        var root = Root(source);
        for (var i = 1; i <= Members; i++)
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, $"R{i}"));
        Assert.Equal("0", Value(source));
        var demanded = KatLangEngine.Run(source[..^"0\n".Length] + $"R{Members}\n");
        var failure = Assert.IsType<RunResult.EvalFailure>(demanded);
        Assert.Equal(KatLangErrorCode.LocalOnlyProperty, Assert.Single(failure.Errors).Code);
    }

    /// <summary>
    /// NEGATIVE CONTROLS (what QUALIFIED SEED PARTS take). Parts that hold a path — every member also reads <c>Q.X{i}</c>, a
    /// pending reference in every part (<c>path</c>) — are neither qualified part by part when anchored nor read owner by
    /// owner when settled: the seed is expanded, folded and its paths settled as before (no part copied, no owner looked up
    /// for parts), and the metadata is the former walk's. Parts that hold required names alone, read by members of the
    /// library's own owner (the navigated chain with output <c>0</c>), keep the name-only SEED PARTS route.
    /// </summary>
    [Fact]
    public void PartsHoldingPathsOrOnlyNames_DoNotTakeTheQualifiedRoute()
    {
        const int Members = 24;
        var pathSource = OwnerQualifiedRows(Members, "path");
        var path = AssertSameAsFormerWalk(pathSource, PropertyExposureResolver.SeedPartsFoldedForTesting).Production;
        Assert.Equal(0, path.SettlementQualifiedPartCopies);
        Assert.Equal(0, path.SettlementQualifiedPartOwnerLookups);
        ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(Root(pathSource), "F"));
        Assert.Equal(Rows(Members, i => i * (i + 1) / 2 + Enumerable.Range(1, i).Sum(j => 7 + j)), Value(pathSource));

        var names = AssertSameAsFormerWalk(NavigatedChain(48, output: "0"), PropertyExposureResolver.SeedPartsFoldedForTesting).Production;
        Assert.True(names.SettlementSeedPartWork > 0);
        Assert.Equal(0, names.SettlementQualifiedPartCopies);
        Assert.Equal(0, names.SettlementQualifiedPartOwnerLookups);
    }

    /// <summary>
    /// An owner only a part's part carries is still looked up. Inside <c>H(y1, …, y10)</c>, <c>F</c>'s chain ends in
    /// <c>R = p1 + … + p9 + P{K}</c> (nine names qualified with <c>F</c>), <c>Q = R + y1 + … + y9</c> and <c>Z = Q + y10</c>:
    /// <c>Z</c> holds <c>Q</c> by reference and <c>Q</c> holds <c>R</c>, so <c>Q</c>'s own sets hold <c>H</c>'s names only and
    /// <c>F</c> is an owner of <c>Q</c> through <c>R</c> alone. <c>X = F.Z</c> inside <c>F</c> finds <c>F</c> on its chain and
    /// requires every <c>p{i}</c> and every <c>y{j}</c>: the owners of a part are its own and those of every part it holds.
    /// </summary>
    [Fact]
    public void AnOwnerOnlyANestedPartCarries_IsStillLookedUp()
    {
        const int Members = 12;
        var source = new StringBuilder($"H({string.Join(", ", Enumerable.Range(1, 10).Select(j => $"y{j}"))}) = {{\n");
        source.Append($"F({string.Join(", ", Enumerable.Range(1, Members).Select(i => $"p{i}"))}) = {{\nP1 = p1\n");
        for (var i = 2; i <= Members; i++) source.Append($"P{i} = P{i - 1} + p{i}\n");
        source.Append($"R = {string.Join(" + ", Enumerable.Range(1, 9).Select(i => $"p{i}"))} + P{Members}\n");
        source.Append($"Q = R + {string.Join(" + ", Enumerable.Range(1, 9).Select(j => $"y{j}"))}\nZ = Q + y10\nX = F.Z\nX\n}}\n");
        source.Append($"F({string.Join(", ", Enumerable.Range(1, Members))})\n}}\nH({string.Join(", ", Enumerable.Range(1, 10))})\n");
        var text = source.ToString();
        var (production, _) = AssertSameAsFormerWalk(text, PropertyExposureResolver.SeedPartsFoldedForTesting);
        Assert.True(production.SettlementQualifiedPartOwnerLookups > 0);
        ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(Root(text), "H", "F", "X"),
            Enumerable.Range(1, Members).Select(static i => ($"p{i}", 0)).Concat(Enumerable.Range(1, 10).Select(static j => ($"y{j}", 1)))
                .OrderBy(static r => r.Item1, StringComparer.Ordinal).ToArray());
        Assert.Equal((Members * (Members + 1) / 2 + 45 + 55).ToString(), Value(text));
    }

    /// <summary>
    /// NEGATIVE CONTROL (a path in a PART, at an owner that binds parameters; the shape of the targeted generator's
    /// <c>q3_00698</c>). <c>D = G.Lib.P{K}</c> in <c>F</c> reads <c>G</c>'s library without calling <c>G</c>, so the member's
    /// seed is anchored through <c>G</c>'s level, which binds every <c>p{i}</c>. <c>P1</c> reads the path <c>Q.X</c>, and the
    /// late members hold it by reference: their own sets hold names only, but a part holds the path. Such a seed is expanded
    /// at <c>G</c>'s level as before, never qualified part by part (a part with a path is no requirement set), and <c>D</c>
    /// requires <c>F</c>'s <c>y</c> through the path while <c>G</c>'s names charge nothing off its chain.
    /// </summary>
    [Theory]
    [InlineData("X")]
    [InlineData("Missing")]
    public void APartHoldingAPath_IsExpandedAtAnOwnerThatBindsParameters(string member)
    {
        const int Members = 12;
        var parameters = string.Join(", ", Enumerable.Range(1, Members).Select(i => $"p{i}"));
        var source = new StringBuilder($"F(y) = {{\nQ = {{ public X = y + 1 }}\nG({parameters}) = {{\nLib = {{\npublic P1 = p1 + Q.{member}\n");
        for (var i = 2; i <= Members; i++) source.Append($"public P{i} = P{i - 1} + p{i}\n");
        source.Append($"}}\n0\n}}\nD = G.Lib.P{Members}\n0\n}}\nF(7)\n");
        var text = source.ToString();
        AssertSameAsFormerWalk(text, PropertyExposureResolver.SeedPartsFoldedForTesting);
        var reader = ExposureOpenChainComplexityTests.Member(Root(text), "F", "D");
        if (member == "X")
            ExposureOpenChainComplexityTests.AssertRequires(reader, ("y", 0));
        else
            ExposureOpenChainComplexityTests.AssertRequires(reader);
        Assert.Equal("0", Value(text));
    }

    /// <summary>
    /// CANCELLATION while parts are qualified: the anchoring of each row's seed observes the summary channel's checkpoint
    /// as the expansion it replaces did, so the first one after a part was copied cancels the operation, which surfaces with
    /// its token and fails the unit, and no part is copied after it. A fresh parse of the same source then exposes in full
    /// with the uncancelled metadata and counters: nothing of the cancelled resolution is kept.
    /// </summary>
    [Fact]
    public void CancellationWhilePartsAreQualified_StopsTheSolve_AndAFreshParseExposesInFull()
    {
        var source = OwnerQualifiedRows(96);
        var expected = Parse(source);
        using var cancellation = new CancellationTokenSource();
        long copiesAtCancel = -1;
        FrontEndTraversalObservations observations = null!;
        observations = new FrontEndTraversalObservations
        {
            CheckpointReached = (kind, _) =>
            {
                if (kind != FrontEndCancellationCheckpoint.SummaryChannel || cancellation.IsCancellationRequested
                    || observations.SettlementQualifiedPartCopies == 0)
                    return;
                copiesAtCancel = observations.SettlementQualifiedPartCopies;
                cancellation.Cancel();
            },
        };

        var (resolved, _, _) = ExposureSettlementFrameChargeTests.Resolved(source);
        var unit = resolved.CompletedStructure!.Facts;
        var error = Assert.ThrowsAny<OperationCanceledException>(
            () => PropertyExposureResolver.Resolve(resolved, observations, cancellationToken: cancellation.Token));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.True(unit.IsFailed);
        Assert.False(unit.IsSealed);
        Assert.True(copiesAtCancel > 0);
        Assert.Equal(copiesAtCancel, observations.SettlementQualifiedPartCopies);
        Assert.True(observations.SettlementQualifiedPartCopies < expected.Observations.SettlementQualifiedPartCopies);

        var again = Parse(source);
        Assert.Equal(expected.Diagnostics, again.Diagnostics);
        Assert.Equal(expected.Metadata, again.Metadata);
        Assert.Equal(expected.Observations.SettlementQualifiedPartCopies, again.Observations.SettlementQualifiedPartCopies);
        Assert.Equal(expected.Observations.SettlementQualifiedPartOwnerLookups, again.Observations.SettlementQualifiedPartOwnerLookups);
    }

    // ── Off-chain: the residual that needs an owner decision ──────────────────

    /// <summary>
    /// The audit's off-chain terminal: <c>P0.A</c> reads <c>F.G</c>, whose requirement's owner <c>F</c> is on no level of
    /// the chain, and every link reaches it. Such settlements answer their exact keys only (THE OFF-CHAIN GAP): the chain
    /// keeps the exact-key share's metadata in every share mode, and it still settles in D² + 3D + 2 frames, the residual
    /// recorded for the owner decision. The read stays a LATENT check: the front end accepts the program and charges
    /// nothing for <c>F</c>, and demanding the read fails with <c>LocalOnlyProperty</c> when the evaluator checks it.
    /// </summary>
    [Fact]
    public void AnOffChainTerminal_KeepsExactKeys_AndItsLatentCheckIsObservable()
    {
        static string Chain(int links, string output)
        {
            var source = new StringBuilder("F(y) = {\npublic G = y + 1\n0\n}\nP0 = { public A(x) = F.G + x }\n");
            for (var i = 1; i <= links; i++) source.Append($"P{i} = {{ public A(x) = P{i - 1}.A(1) + 1 }}\n");
            return source.Append(output).Append('\n').ToString();
        }

        foreach (var links in new[] { 8, 16 })
        {
            var source = Chain(links, "0");
            var footprint = Parse(source);
            Assert.Equal("", footprint.Diagnostics);
            var exact = InMode(Mode.ExactBoundOwners, () => Parse(source));
            Assert.Equal(exact.Metadata, footprint.Metadata);
            Assert.Equal((long)links * links + 3L * links + 2, footprint.Observations.RequiredAncestorSettlementFrames);
            Assert.Equal(0, footprint.Observations.SettlementShareCandidateHits);
            var root = Root(source);
            for (var i = 0; i <= links; i++)
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, $"P{i}", "A"));
        }

        Assert.Equal("0", Value(Chain(8, "0")));
        var demanded = KatLangEngine.Run(Chain(8, "P8.A(1)"));
        var failure = Assert.IsType<RunResult.EvalFailure>(demanded);
        Assert.Equal(KatLangErrorCode.LocalOnlyProperty, Assert.Single(failure.Errors).Code);
    }
}
