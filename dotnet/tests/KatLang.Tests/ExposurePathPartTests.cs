using System.Text;
using Xunit.Abstractions;
using static KatLang.PropertyDependencyGraphBuilder;

namespace KatLang.Tests;

/// <summary>
/// PATH PARTS (November 27 2026; C# exposure implementation only — no classification, requirement, diagnostic kind,
/// value or Lean rule changes). QUALIFIED SEED PARTS (<c>eb978415</c>) left the PATH CONTROL quadratic: library
/// members <c>P{i} = P{i-1} + p{i} + Q.X{i}</c> read by output rows <c>Lib.P1</c> … <c>Lib.P{K}</c> under their owner
/// <c>F</c> (<see cref="ExposureResidualReuseTests.OwnerQualifiedRows"/>, <c>path</c>). The K distinct paths are the
/// unavoidable work; everything else re-read the same predecessor paths as K grew: each member's full expansion copied its
/// predecessor's width (K² entries kept), each row was anchored through <c>F</c> by folding its whole seed, and each row
/// then settled every path of every predecessor again, K² / 2 frames (2,012,999 at K = 2,000). Three changes:
/// <list type="bullet">
/// <item>PATH SHARES (<c>PropertyDependencyGraphBuilder.TryPathShareMemberSeed</c>): a member outside a cycle that carries
/// references and reads ONE nonempty predecessor holds it and a delta of its own anchored references, in the union's
/// write order, under a fold budget.</item>
/// <item>Anchoring (<c>AnchorPublishedSeed</c>): a seed whose parts carry only references every level expansion keeps is
/// carried through a level without parameters and qualified part by part at one with parameters.</item>
/// <item>Settlement (<c>ResolveSeed</c>): such a seed's own sets and references are settled, then each part on its own,
/// each part settlement kept for the resolution under its exact part, level, site and bound owners (or, when it read a
/// summary of the level in progress, in the level's live settlements), with guards for whole results, live reads,
/// fact views, off-chain lookups and bound-owner narrowing.</item>
/// </list>
/// Oracles: the former walk (<see cref="PropertyExposureResolver.PathPartsFoldedForTesting"/> with
/// <see cref="PropertyDependencyGraphBuilder.MemberPathSharesCopiedForTesting"/>) and the unshared settlement, compared by
/// published diagnostics and metadata; the copied union, compared summary by summary in content and reference order; run
/// values; deterministic counters, never time.
/// </summary>
public sealed class ExposurePathPartTests(ITestOutputHelper output)
{
    // ── Harness ─────────────────────────────────────────────────────────────

    private static T Former<T>(Func<T> work)
    {
        var folded = PropertyExposureResolver.PathPartsFoldedForTesting.Value;
        var copied = MemberPathSharesCopiedForTesting.Value;
        PropertyExposureResolver.PathPartsFoldedForTesting.Value = true;
        MemberPathSharesCopiedForTesting.Value = true;
        try { return work(); }
        finally
        {
            PropertyExposureResolver.PathPartsFoldedForTesting.Value = folded;
            MemberPathSharesCopiedForTesting.Value = copied;
        }
    }

    private static T WithoutPathShares<T>(Func<T> work)
    {
        var copied = MemberPathSharesCopiedForTesting.Value;
        MemberPathSharesCopiedForTesting.Value = true;
        try { return work(); }
        finally { MemberPathSharesCopiedForTesting.Value = copied; }
    }

    private static T Unshared<T>(Func<T> work)
    {
        var mode = PropertyExposureResolver.SettlementShareModeForTesting.Value;
        PropertyExposureResolver.SettlementShareModeForTesting.Value = PropertyExposureResolver.SettlementShareMode.Unshared;
        try { return work(); }
        finally { PropertyExposureResolver.SettlementShareModeForTesting.Value = mode; }
    }

    private static T WithCapacity<T>(int capacity, Func<T> work)
    {
        var previous = PropertyExposureResolver.ResidualCacheCapacityForTesting.Value;
        PropertyExposureResolver.ResidualCacheCapacityForTesting.Value = capacity;
        try { return work(); }
        finally { PropertyExposureResolver.ResidualCacheCapacityForTesting.Value = previous; }
    }

    private static (string Diagnostics, string Metadata, FrontEndTraversalObservations Observations) Parse(string source,
        FrontEndTraversalObservations? observations = null)
    {
        observations ??= new FrontEndTraversalObservations();
        var parsed = Parser.ParseObserved(source, options: null, observations);
        var diagnostics = string.Join("\n", parsed.Diagnostics.Select(d => $"{d.Code}/{d.Severity}@{d.Span}: {d.Message}"));
        return (diagnostics, ExposureSettlementFrameChargeTests.Metadata(parsed.Root), observations);
    }

    /// <summary>Production, the former walk and the unshared settlement publish the same diagnostics and metadata.</summary>
    private static (FrontEndTraversalObservations Production, FrontEndTraversalObservations Former) AssertSameAsFormerWalk(
        string source, bool clean = true)
    {
        var production = Parse(source);
        if (clean)
            Assert.Equal("", production.Diagnostics);
        var former = Former(() => Parse(source));
        Assert.Equal(former.Diagnostics, production.Diagnostics);
        Assert.Equal(former.Metadata, production.Metadata);
        var unshared = Unshared(() => Parse(source));
        Assert.Equal(0, unshared.Observations.SettlementPathPartsKept);
        Assert.Equal(0, unshared.Observations.SettlementPathPartReuses);
        Assert.Equal(unshared.Diagnostics, production.Diagnostics);
        Assert.Equal(unshared.Metadata, production.Metadata);
        return (production.Observations, former.Observations);
    }

    private static string Value(string source) => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString();

    private static Algorithm.User Root(string source) => SourceProvenance.ParseValid(source).Root;

    private static void AssertLinear(long[] work)
    {
        Assert.InRange((double)work[1] / work[0], 1.5, 2.5);
        Assert.InRange((double)work[2] / work[1], 1.5, 2.5);
    }

    private static void AssertQuadratic(long[] work) => Assert.InRange((double)work[2] / work[1], 3.0, 5.0);

    private static string Names(string prefix, int from, int to)
        => string.Join(", ", Enumerable.Range(from, to - from + 1).Select(i => $"{prefix}{i}"));

    private static string Arguments(int count) => string.Join(", ", Enumerable.Range(1, count));

    // ── Shapes ──────────────────────────────────────────────────────────────

    /// <summary><c>Q</c>'s <paramref name="width"/> public members <c>X{j} = y + j</c> (or a chain of them: <paramref name="dependent"/>).</summary>
    private static string Provider(int width, bool dependent = false, string name = "Q", string input = "y")
    {
        var source = new StringBuilder($"{name} = {{\n");
        for (var j = 1; j <= width; j++)
            source.Append(dependent && j > 1 ? $"public X{j} = X{j - 1} + 1\n" : $"public X{j} = {input} + {j}\n");
        return source.Append("}\n").ToString();
    }

    /// <summary>The library chain: <c>P1 = p1 + path(1)</c> and <c>P{i} = P{i-1} + p{i} + path(i)</c>.</summary>
    private static string Library(int members, Func<int, string> path, string name = "Lib", Func<int, bool>? shadowed = null)
    {
        var source = new StringBuilder($"{name} = {{\npublic P1 = p1 + {path(1)}\n");
        for (var i = 2; i <= members; i++)
        {
            if (shadowed?.Invoke(i) == true)
                source.Append($"public P{i} = {{\nQ = {{ public X{i} = {i} }}\nP{i - 1} + p{i} + {path(i)}\n}}\n");
            else
                source.Append($"public P{i} = P{i - 1} + p{i} + {path(i)}\n");
        }
        return source.Append("}\n").ToString();
    }

    private static string Rows(int members, string head = "Lib") => string.Concat(Enumerable.Range(1, members).Select(i => $"{head}.P{i}\n"));

    /// <summary>
    /// The controls the brief names, around the path control. Each is <c>F(y, p1, …, p{K})</c> called with
    /// <c>(7, 1, …, K)</c>:
    /// <list type="bullet">
    /// <item><c>dependent</c>: the provider's members read each other (<c>X{j} = X{j-1} + 1</c>).</item>
    /// <item><c>shadowed</c>: every third member is a block that declares its own <c>Q</c>, which its path selects.</item>
    /// <item><c>inner-shadow</c>: the library sits in parameterless blocks, the inner one declaring its own <c>Q</c>.</item>
    /// <item><c>missing</c> (an unavailable path): every member reads <c>Q.Miss</c>, which <c>Q</c> does not declare, so the
    /// dot route falls back to <c>Miss(Q)</c> and reads the provider's VALUE; readers <c>R{i} = Lib.P{i}</c> at <c>F</c>'s level.
    /// The bare callable name that remains is one a level could select, so anchoring keeps such seeds whole.</item>
    /// <item><c>same</c>: every member reads the same path <c>Q.X1</c>.</item>
    /// <item><c>two</c>: two libraries over one provider: distinct parts holding the same paths, every row of both read.</item>
    /// <item><c>repeated</c>: every row read twice, and the last member by K readers: the same parts again.</item>
    /// <item><c>readers</c>: readers <c>R{i} = Lib.P{i}</c> settled at <c>F</c>'s own level (no intervening owner).</item>
    /// <item><c>open</c>: the provider reached through <c>open M</c>.</item>
    /// <item><c>deep</c>: the library under two parameterless blocks; <c>deep-param</c>: the outer one binds <c>p1</c>.</item>
    /// <item><c>inner</c>: the library and its rows inside <c>G(z)</c>, whose provider reads <c>z</c>.</item>
    /// <item><c>detached</c>: root readers <c>R{i} = F.Lib.P{i}</c> (owner off the readers' chain).</item>
    /// <item><c>cycle</c>: the chain closed into a cycle through its head (<c>P1 = P{K} + p1 + Q.X1</c>).</item>
    /// <item><c>bare</c>: every member also reads a bare property <c>w</c> of <c>F</c>, a reference anchoring may replace.</item>
    /// <item><c>names</c> and <c>qualified</c> (no path anywhere): the name-only chain read at <c>F</c>'s level, and the
    /// QUALIFIED SEED PARTS rows.</item>
    /// </list>
    /// </summary>
    internal static string Control(string shape, int members)
    {
        var head = $"F(y, {Names("p", 1, members)}) = {{\n";
        var call = $"F(7, {Arguments(members)})\n";
        string Path(int i) => $"Q.X{i}";
        return shape switch
        {
            "dependent" => head + Provider(members, dependent: true) + Library(members, Path) + Rows(members) + "}\n" + call,
            "shadowed" => head + Provider(members) + Library(members, Path, shadowed: i => i % 3 == 0) + Rows(members) + "}\n" + call,
            "inner-shadow" => head + Provider(members) + "W1 = {\nW2 = {\n" + Provider(members, input: "5") + Library(members, Path)
                + "0\n}\n0\n}\n" + Rows(members, "W1.W2.Lib") + "}\n" + call,
            "missing" => head + "Q = { public Z = y + 1\ny }\nMiss(v) = v + 1\n" + Library(members, _ => "Q.Miss")
                + string.Concat(Enumerable.Range(1, members).Select(i => $"R{i} = Lib.P{i}\n")) + $"R{members}\n}}\n" + call,
            "same" => head + Provider(1) + Library(members, _ => "Q.X1") + Rows(members) + "}\n" + call,
            "two" => head + Provider(members) + Library(members, Path) + Library(members, Path, "Lib2")
                + Rows(members) + Rows(members, "Lib2") + "}\n" + call,
            "repeated" => head + Provider(members) + Library(members, Path)
                + string.Concat(Enumerable.Range(1, members).Select(i => $"R{i} = Lib.P{members}\n"))
                + Rows(members) + Rows(members) + $"R{members}\n}}\n" + call,
            "readers" => head + Provider(members) + Library(members, Path)
                + string.Concat(Enumerable.Range(1, members).Select(i => $"R{i} = Lib.P{i}\n")) + $"R{members}\n}}\n" + call,
            "open" => head + "open M\nM = {\npublic " + Provider(members) + "}\n" + Library(members, Path) + Rows(members) + "}\n" + call,
            "deep" => head + Provider(members) + "W1 = {\nW2 = {\n" + Library(members, Path) + "0\n}\n0\n}\n"
                + Rows(members, "W1.W2.Lib") + "}\n" + call,
            "deep-param" => head + Provider(members) + "W1(p1) = {\nW2 = {\n" + Library(members, Path) + "0\n}\n0\n}\n"
                + "D = W1.W2.Lib.P" + members + "\n0\n}\n" + call,
            "inner" => head + "G(z) = {\n" + Provider(members, input: "z") + Library(members, Path) + Rows(members) + "}\nG(3)\n}\n" + call,
            "detached" => head + Provider(members) + Library(members, Path) + "0\n}\n"
                + string.Concat(Enumerable.Range(1, members).Select(i => $"R{i} = F.Lib.P{i}\n")) + "0\n",
            "cycle" => head + Provider(members) + "Lib = {\n" + $"public P1 = P{members} + p1 + Q.X1\n"
                + string.Concat(Enumerable.Range(2, members - 1).Select(i => $"public P{i} = P{i - 1} + p{i} + Q.X{i}\n"))
                + "}\nLib.P1\n}\n" + call,
            "bare" => head + Provider(members) + "w = y + 7\n" + Library(members, i => $"Q.X{i} + w") + Rows(members) + "}\n" + call,
            "names" => head + Library(members, _ => "0") + string.Concat(Enumerable.Range(1, members).Select(i => $"R{i} = Lib.P{i}\n"))
                + $"R{members}\n}}\n" + call,
            "qualified" => ExposureResidualReuseTests.OwnerQualifiedRows(members),
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        };
    }

    // ── The path control ────────────────────────────────────────────────────

    /// <summary>
    /// THE PATH CONTROL at the production thresholds. Its K distinct paths are settled once each; the predecessor paths no
    /// longer are again per row: settlement frames and the entries the member solve keeps grow linearly, where the former
    /// walk's grow as K² / 2 and K². The published metadata is the former walk's and the unshared settlement's, every row
    /// takes path shares, part-by-part anchoring through <c>F</c> and kept part settlements, and the run value is the
    /// same.
    /// </summary>
    [Fact]
    public void ThePathControl_SettlesEachPathOnce_AndGrowsLinearly()
    {
        var sizes = new[] { 40, 80, 160 };
        var frames = new long[3];
        var formerFrames = new long[3];
        var entries = new long[3];
        var formerEntries = new long[3];
        for (var k = 0; k < sizes.Length; k++)
        {
            var source = ExposureResidualReuseTests.OwnerQualifiedRows(sizes[k], "path");
            var (production, former) = AssertSameAsFormerWalk(source);
            frames[k] = production.RequiredAncestorSettlementFrames;
            formerFrames[k] = former.RequiredAncestorSettlementFrames;
            entries[k] = production.SummaryMemberExpansionEntries;
            formerEntries[k] = former.SummaryMemberExpansionEntries;
            Assert.True(production.SummaryMemberPathShares > sizes[k] / 2);
            Assert.True(production.SettlementPathPartAnchorings > sizes[k] / 2);
            Assert.True(production.SettlementPathPartReuses > sizes[k] / 2);
            // A wide flat predecessor from a full expansion may get a frame. The per-row deltas settle in place.
            Assert.InRange(production.SettlementPathPartFrames, 0, production.SummaryMemberExpansions);
            Assert.Equal(0, former.SummaryMemberPathShares + former.SettlementPathPartAnchorings + former.SettlementPathPartReuses
                + former.SettlementPathPartFrames + former.SettlementPathPartsKept);
            Assert.InRange(frames[k], sizes[k], 16L * sizes[k]);
            output.WriteLine($"K={sizes[k]}: frames {formerFrames[k]} -> {frames[k]}, entries {formerEntries[k]} -> {entries[k]}, "
                + $"part frames {production.SettlementPathPartFrames}, reuses {production.SettlementPathPartReuses}, "
                + $"kept {production.SettlementPathPartsKept}, path shares {production.SummaryMemberPathShares}");
        }

        AssertLinear(frames);
        AssertQuadratic(formerFrames);
        AssertLinear(entries);
        AssertQuadratic(formerEntries);
        const int Members = 40;
        Assert.Equal($"({string.Join(", ", Enumerable.Range(1, Members).Select(i => i * (i + 1) / 2 + Enumerable.Range(1, i).Sum(j => 7 + j)))})",
            Value(ExposureResidualReuseTests.OwnerQualifiedRows(Members, "path")));
    }

    /// <summary>
    /// Sibling readers each hold the same wide flat predecessor and a distinct delta. At the production threshold
    /// the predecessor's K references are settled once and each later reader takes its whole settlement.
    /// </summary>
    [Fact]
    public void SiblingReaders_ReuseThePathsOfTheirWideFlatPredecessor()
    {
        var sizes = new[] { 24, 48, 96 };
        var frames = new long[sizes.Length];
        var formerFrames = new long[sizes.Length];
        for (var k = 0; k < sizes.Length; k++)
        {
            var size = sizes[k];
            var source = new StringBuilder("F(y) = {\n").Append(Provider(size)).Append("Lib = {\npublic Head = ");
            source.AppendJoin(" + ", Enumerable.Range(1, size).Select(i => $"Q.X{i}")).Append('\n');
            for (var i = 1; i <= size; i++)
                source.Append($"public P{i} = Head + Q.X{i}\n");
            source.Append("}\n").Append(Rows(size)).Append("}\nF(1)");

            var (production, former) = AssertSameAsFormerWalk(source.ToString());
            Assert.True(production.SettlementPathPartReuses >= size - 1);
            frames[k] = production.RequiredAncestorSettlementFrames;
            formerFrames[k] = former.RequiredAncestorSettlementFrames;
        }

        AssertLinear(frames);
        AssertQuadratic(formerFrames);
    }

    /// <summary>
    /// THE FOLD BUDGET of path shares. Over a chain of bounded width — 16 cycled parameters and 16 cycled paths, so every
    /// member's logical width is at most 32 — a share that held its predecessor every time would grow a chain of K parts
    /// that every reader folding a member walks whole. The budget folds the chain back into a flat seed whenever it has
    /// grown by about half the width it ends at: full expansions keep coming at a steady rate (13 among these 160
    /// members, against 3 if every share held), and the published metadata is the former walk's.
    /// </summary>
    [Fact]
    public void BoundedPathChains_FoldWithinTheirBudget()
    {
        const int Members = 160;
        var source = new StringBuilder($"F(y, {Names("p", 1, 16)}) = {{\n{Provider(16)}Lib = {{\n");
        source.Append($"public P1 = {string.Join(" + ", Enumerable.Range(1, 16).Select(j => $"p{j}"))} + Q.X1\n");
        for (var i = 2; i <= Members; i++) source.Append($"public P{i} = P{i - 1} + p{1 + (i - 1) % 16} + Q.X{1 + (i - 1) % 16}\n");
        source.Append($"}}\n{Rows(Members)}}}\nF(7, {Arguments(16)})\n");
        var (production, former) = AssertSameAsFormerWalk(source.ToString());
        output.WriteLine($"path shares {production.SummaryMemberPathShares}, full expansions {production.SummaryMemberExpansions} "
            + $"(former {former.SummaryMemberExpansions}), entries {production.SummaryMemberExpansionEntries} (former {former.SummaryMemberExpansionEntries})");
        Assert.True(production.SummaryMemberPathShares > Members / 2);
        Assert.InRange(production.SummaryMemberExpansions, Members / 16, Members / 2);
    }

    /// <summary>
    /// PATH-BEARING READERS of a two-predecessor chain (<see cref="SharedPredecessorExpansionTests.PathReaders"/>:
    /// <c>R{i} = P{i} + Lib.X</c>, and their readers <c>S{i} = R{i} + Lib.Y</c>, over a growing chain and over 16 cycled
    /// parameters): each reader holds the one member it reads instead of a full expansion that copies it, so the member
    /// solve makes fewer full expansions and keeps no more entries than the former walk, with the same metadata.
    /// </summary>
    [Theory]
    [InlineData(0, false)]
    [InlineData(0, true)]
    [InlineData(16, true)]
    public void PathBearingReaders_HoldTheMemberTheyRead(int width, bool secondOrder)
    {
        foreach (var members in new[] { 40, 80 })
        {
            var source = SharedPredecessorExpansionTests.PathReaders(members, width, secondOrder);
            var (production, former) = AssertSameAsFormerWalk(source);
            Assert.True(production.SummaryMemberPathShares > 0);
            Assert.True(production.SummaryMemberExpansions < former.SummaryMemberExpansions);
            Assert.InRange(production.SummaryMemberExpansionEntries, 1, former.SummaryMemberExpansionEntries);
        }
    }

    /// <summary>
    /// ORDER, REQUIREMENTS AND OWNERS of a path share: every summary the member solve computes (output and member seeds) is
    /// the copied union's — the same required names, owner-qualified parameters and visible names, and the same references
    /// in the same order with the same origins — over the controls and the path control at sizes on either side of the
    /// production threshold (a flat predecessor of more than eight entries) and of the fold budget.
    /// </summary>
    [Fact]
    public void PathShares_AreTheUnionsInContentAndReferenceOrder()
    {
        var shapes = new[] { "dependent", "shadowed", "missing", "same", "two", "repeated", "readers", "open", "deep", "inner", "cycle", "bare" };
        var programs = new[] { 3, 9, 14, 33 }.SelectMany(k => shapes.Select(shape => Control(shape, k))
            .Append(ExposureResidualReuseTests.OwnerQualifiedRows(k, "path")))
            .Concat(GeneratedPrograms(120, seed: 5));
        var compared = 0;
        var sharing = 0;
        foreach (var source in programs)
        {
            var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
            if (parsed.Diagnostics.Count != 0)
                continue;
            var root = parsed.Root;
            var context = AnalyzedStaticStructures.ForBoundAst(root);
            var observations = new FrontEndTraversalObservations();
            var shared = StandaloneSummaries.MemoFor(root, observations);
            var copied = StandaloneSummaries.MemoFor(root);
            BuildSummaries(root, context, shared, observations);
            WithoutPathShares(() => BuildSummaries(root, context, copied));
            if (observations.SummaryMemberPathShares > 0)
                sharing++;
            compared += CompareSummaries(shared, copied, source);
        }

        output.WriteLine($"{compared} summaries compared; {sharing} programs made path shares");
        Assert.InRange(sharing, 40, int.MaxValue);
    }

    private static int CompareSummaries(SummaryMemo shared, SummaryMemo copied, string source)
    {
        var compared = 0;
        foreach (var (algorithm, summary) in copied.IndependentAlgorithmSummaries ?? [])
        {
            Assert.True(shared.IndependentAlgorithmSummaries!.TryGetValue(algorithm, out var other), source);
            Assert.Null(SummaryMemo.AdoptedSummaryDifference(other, summary));
            compared++;
        }

        foreach (var (key, summary) in copied.ContextualAlgorithmSummaries ?? [])
        {
            Assert.True(shared.ContextualAlgorithmSummaries!.TryGetValue(key, out var other), source);
            Assert.Null(SummaryMemo.AdoptedSummaryDifference(other, summary));
            compared++;
        }

        Assert.Equal(copied.IndependentAlgorithmSummaries?.Count ?? 0, shared.IndependentAlgorithmSummaries?.Count ?? 0);
        Assert.Equal(copied.ContextualAlgorithmSummaries?.Count ?? 0, shared.ContextualAlgorithmSummaries?.Count ?? 0);
        return compared;
    }

    // ── Controls ────────────────────────────────────────────────────────────

    /// <summary>
    /// THE CONTROLS against the former walk and the unshared settlement, at a size past the production threshold: the
    /// metadata is the same in every one, and each takes the routes its shape allows. Dependent, shadowed and missing
    /// providers, one path read by every member, rows read again and two libraries over one provider take path shares and
    /// kept part settlements and are anchored part by part through <c>F</c>; a provider reached through <c>open</c> and
    /// libraries under blocks (with and without a parameter) or inside an inner owner too. Readers at <c>F</c>'s own level
    /// need no anchoring. A bare name a level could select as its own member keeps a seed out of part-by-part anchoring,
    /// a cycle keeps its members' folded seeds, and the name-only and qualified controls (no path) take neither route.
    /// </summary>
    [Theory]
    [InlineData("dependent", true, true)]
    [InlineData("shadowed", true, true)]
    [InlineData("inner-shadow", true, true)]
    [InlineData("missing", true, false)]
    [InlineData("same", true, true)]
    [InlineData("two", true, true)]
    [InlineData("repeated", true, true)]
    [InlineData("readers", true, true)]
    [InlineData("open", true, true)]
    [InlineData("deep", true, true)]
    [InlineData("deep-param", true, true)]
    [InlineData("inner", true, true)]
    [InlineData("detached", true, true)]
    [InlineData("cycle", false, false)]
    [InlineData("bare", true, false)]
    [InlineData("names", false, false)]
    [InlineData("qualified", false, false)]
    public void TheControls_PublishTheFormerWalksMetadata(string shape, bool shares, bool anchored)
    {
        const int Members = 33;
        var source = Control(shape, Members);
        var (production, former) = AssertSameAsFormerWalk(source);
        output.WriteLine($"{shape}: shares {production.SummaryMemberPathShares}, anchorings {production.SettlementPathPartAnchorings}, "
            + $"part frames {production.SettlementPathPartFrames}, reuses {production.SettlementPathPartReuses}, kept {production.SettlementPathPartsKept}, "
            + $"frames {former.RequiredAncestorSettlementFrames} -> {production.RequiredAncestorSettlementFrames}");
        Assert.Equal(shares, production.SummaryMemberPathShares > 0);
        Assert.Equal(anchored, production.SettlementPathPartAnchorings > 0);
        Assert.Equal(0, former.SummaryMemberPathShares + former.SettlementPathPartAnchorings + former.SettlementPathPartFrames
            + former.SettlementPathPartReuses);
        if (shares && shape is not ("detached" or "deep-param" or "bare"))
            Assert.True(production.SettlementPathPartReuses > 0, shape);
        if (shape == "qualified")
            Assert.True(production.SettlementQualifiedPartOwnerLookups > 0);
        if (shape is not ("detached" or "deep-param" or "cycle"))
            _ = Value(source);
    }

    /// <summary>
    /// REQUIREMENTS through the new routes: a reader at <c>F</c>'s level requires every <c>p{i}</c> it reads and <c>y</c>;
    /// a missing member charges the provider's VALUE, which reads <c>y</c>; the inner owner <c>G</c> requires <c>F</c>'s
    /// <c>p{i}</c> and never its own <c>z</c>, which its provider's paths read; a reader of a library behind a block that
    /// binds <c>p1</c> requires <c>F</c>'s <c>y</c> and every other parameter, never <c>p1</c>; and a member whose block
    /// declares its own <c>Q</c> runs to the former walk's value.
    /// </summary>
    [Fact]
    public void TheRequirementsThroughEachRoute_AreTheFoldedOnes()
    {
        const int Members = 24;
        var readers = Root(Control("readers", Members));
        ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(readers, "F", $"R{Members}"),
            new[] { "y" }.Concat(Enumerable.Range(1, Members).Select(i => $"p{i}")).Order(StringComparer.Ordinal).Select(n => (n, 0)).ToArray());
        Assert.Contains("y", ExposureOpenChainComplexityTests.Member(Root(Control("missing", Members)), "F", $"R{Members}").RequiredAncestorParameters);
        Assert.Equal(Enumerable.Range(1, Members).Select(static i => $"p{i}").Order(StringComparer.Ordinal),
            ExposureOpenChainComplexityTests.Member(Root(Control("inner", Members)), "F", "G").RequiredAncestorParameters);
        var deep = ExposureOpenChainComplexityTests.Member(Root(Control("deep-param", Members)), "F", "D");
        Assert.Contains("y", deep.RequiredAncestorParameters);
        Assert.DoesNotContain("p1", deep.RequiredAncestorParameters);
        Assert.Contains($"p{Members}", deep.RequiredAncestorParameters);
        var shadowed = Value(Control("shadowed", Members));
        Assert.Equal(Former(() => Value(Control("shadowed", Members))), shadowed);
    }

    // ── Guards ──────────────────────────────────────────────────────────────

    [Fact]
    public void AReaderWithReusedParts_StillRequiresItsOwnersActivation()
    {
        var source = Control("readers", 24) + "F.R24\n";
        _ = SourceProvenance.ParseValid(source);
        Assert.True(AssertSameAsFormerWalk(source).Production.SettlementPathPartReuses > 0);
        var actual = Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)).Errors);
        var expected = Assert.Single(Assert.IsType<RunResult.EvalFailure>(Former(() => KatLangEngine.Run(source))).Errors);
        Assert.Equal(KatLangErrorCode.LocalOnlyProperty, actual.Code);
        Assert.Equal((expected.Code, expected.Span, expected.Message), (actual.Code, actual.Span, actual.Message));
    }

    [Fact]
    public void PartEligibility_FollowsNarrowingAndClear()
    {
        var root = Root("1");
        var context = AnalyzedStaticStructures.ForBoundAst(root);
        var bare = new PendingReference("A", [], context);
        var path = new PendingReference("L", ["X"], context);
        var references = new PendingReferenceSet([path.BoundBy(root)]);
        Assert.False(references.BindsNoOwners);
        Assert.True(references.StaysAtEveryExpansion);

        references.Add(bare.BoundBy(root));
        Assert.False(references.StaysAtEveryExpansion);
        references.Add(path);
        Assert.False(references.BindsNoOwners);
        Assert.False(references.StaysAtEveryExpansion);
        references.Add(bare);
        Assert.True(references.BindsNoOwners);
        Assert.False(references.StaysAtEveryExpansion);

        references.Clear();
        references.Add(path);
        Assert.True(references.BindsNoOwners);
        Assert.True(references.StaysAtEveryExpansion);
        references.Add(new SummaryReference("L", ["X"]));
        Assert.False(references.StaysAtEveryExpansion);
    }

    [Fact]
    public void BoundBareNamesInSeparateParts_CanSelectALocalMemberAfterFolding()
    {
        var root = Root("A = 1\n0");
        var context = AnalyzedStaticStructures.ForBoundAst(root);
        var name = new PendingReference("A", [], context);
        var left = new SummarySeed(pendingReferences: [name.BoundBy(root)]);
        var right = new SummarySeed(pendingReferences: [name.BoundBy(root.Properties[0].Value)]);
        var seed = new SummarySeed();
        seed.AbsorbReference(left);
        seed.AbsorbReference(right);

        // Each occurrence is bound alone. Their folded key has no bound owner and reads A's local summary.
        var level = new LevelContext(root, new Dictionary<string, SummarySeed> { ["A"] = new(["witness"]) },
            CreateWalkMemos(new SummaryMemo(), null, context));
        var expanded = ExpandAtLevel(seed, level);
        Assert.Equal("witness", Assert.Single(expanded.RequiredAncestorOwnedParameterNames));
        Assert.Empty(expanded.PendingReferences);
        Assert.False(left.OwnSetsStayAtEveryExpansion);
        Assert.False(right.OwnSetsStayAtEveryExpansion);
    }

    [Fact]
    public void RetainedPathParts_ChargeTheirBoundOwnersAndDistinguishRequestingSites()
    {
        var summaries = new Dictionary<string, RequirementSet>();
        var level = new PropertyExposureResolver.SummaryScope(null, null!, summaries);
        var site = new PropertyExposureResolver.SummaryScope(level, null!, summaries);
        var part = new SummarySeed();
        var root = Root("1");
        var owners = Enumerable.Range(0, 33).Select(_ => (Algorithm)(root with { })).ToArray();
        var bound = BoundOwnerSet.With(null, owners, null);
        var key = new PropertyExposureResolver.SettlementShare.PathPartKey(part, level, site, bound);
        var settled = new PropertyExposureResolver.SettlementShare.Settled(default, 0, false, [], false);

        Assert.NotEqual(key, key with { Site = level });
        Assert.Equal(1, (key with { Bound = null }).RetainedWeight(settled));
        Assert.Equal(2, key.RetainedWeight(settled));
    }

    /// <summary>
    /// LIVE DEPENDENCIES. A share chain whose wide head reads a bare property <c>w</c> of <c>F</c> and two paths is read by
    /// readers at <c>F</c>'s level while <c>F</c> is solved: settling the parts reads <c>w</c>'s live summary. No such part
    /// settlement enters the exact table; each is kept in the level's live settlements and served while <c>w</c>'s summary
    /// stands, so the readers reuse their predecessors' parts. The metadata is the former walk's, the unshared one's, and
    /// that of the walk that reuses live settlements only inside their Run.
    /// </summary>
    [Fact]
    public void PartsReadingALiveSummary_AreKeptOnlyAsLiveSettlements()
    {
        const int Members = 48;
        var source = new StringBuilder($"F(y, {Names("p", 1, Members)}) = {{\nQ = {{ public X1 = y + 1\npublic X2 = y + 2 }}\nw = y + 7\nLib = {{\n");
        source.Append($"public P1 = p1 + w + Q.X1 + Q.X2 + {string.Join(" + ", Enumerable.Range(2, 8).Select(i => $"p{i}"))}\n");
        for (var i = 2; i <= Members; i++) source.Append($"public P{i} = P{i - 1} + p{i}\n");
        source.Append("}\n").Append(string.Concat(Enumerable.Range(1, Members).Select(i => $"R{i} = Lib.P{i}\n")));
        source.Append($"R{Members}\n}}\nF(7, {Arguments(Members)})\n");
        var text = source.ToString();
        var (production, former) = AssertSameAsFormerWalk(text);
        var perRun = With(PropertyExposureResolver.LiveSettlementsPerRunForTesting, () => Parse(text));
        Assert.Equal(perRun.Metadata, Parse(text).Metadata);
        Assert.Equal(0, production.SettlementPathPartsKept);
        Assert.True(production.SettlementPathPartReuses > Members / 2);
        Assert.True(production.SettlementLiveHits > 0);
        Assert.True(production.RequiredAncestorSettlementFrames < former.RequiredAncestorSettlementFrames);
        ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(Root(text), "F", $"R{Members}"),
            new[] { "y" }.Concat(Enumerable.Range(1, Members).Select(i => $"p{i}")).Order(StringComparer.Ordinal).Select(n => (n, 0)).ToArray());
    }

    private static T With<T>(AsyncLocal<bool> seam, Func<T> work)
    {
        var previous = seam.Value;
        seam.Value = true;
        try { return work(); }
        finally { seam.Value = previous; }
    }

    /// <summary>
    /// BOUND-OWNER NARROWING (a guard). Folding narrows a reference written twice with different bound owners to the
    /// owners both carry, which settling the parts one by one would not. <c>P2</c> reads an inline block whose unbound
    /// <c>u</c> becomes the block's parameter, so the block's output carries <c>Q.X1</c> bound by the block, and the
    /// path shares <c>P2</c> and <c>P3</c> hold it in a part. Such seeds are folded and settled whole: no part frame and
    /// no kept part, although the member solve made path shares; the metadata is the former walk's.
    /// </summary>
    [Fact]
    public void APartHoldingABoundReference_IsSettledWhole()
    {
        const string Source = "F(y, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10) = {\nQ = { public X1 = y + 1\npublic X2 = y + 2 }\nLib = {\n"
            + "public P1 = p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8 + p9 + Q.X2\npublic P2 = P1 + p10 + { Q.X1 + u }\n"
            + "public P3 = P2 + p3 + Q.X2\n}\nLib.P1\nLib.P2\nLib.P3\n}\nF(7, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10)\n";
        var (production, _) = AssertSameAsFormerWalk(Source);
        Assert.Equal(2, production.SummaryMemberPathShares);
        Assert.Equal(0, production.SettlementPathPartFrames);
        Assert.Equal(0, production.SettlementPathPartReuses);
        Assert.Equal(0, production.SettlementPathPartsKept);
    }

    /// <summary>
    /// A CYCLE THROUGH THE OWNER (the cycle generator's program 1,502, reduced): members of <c>F</c> read each other
    /// through <c>F.M15</c>, <c>F.M2</c> and <c>F.M1</c>, so a seed can be settled again inside its own settlement, by the
    /// folded walk once the resolution has made an off-chain lookup, which folds it in place and writes its parts'
    /// references into its own set. The part-by-part settlement of that same seed settles a copy of its own references
    /// (it threw "Collection was modified" while it enumerated the set itself); the metadata is the former walk's.
    /// </summary>
    [Fact]
    public void ASeedSettledAgainInsideItsOwnSettlement_KeepsItsOwnReferences()
    {
        const string Source = "F(p1, p2) = {\n  Lib = {\n    public X = p2 + 1\n    public Y = 2\n    public W(a) = a + p1\n"
            + "    public V = X + Y\n    public U = 7\n  }\n  O = {\n  }\n  M1 = M18 + M1 + M9 + M4\n  M2 = M17 + p2 + p1\n"
            + "  M3 = Lib.X + 4 + M2\n  M4 = M5\n  M5 = M4 + M4 + M18 + M4\n  M7 = Lib.V\n  M8 = M2 + M7\n"
            + "  M9 = F.M15 + M8 + p1 + F.M2\n  M11 = M9 + M3 + M13\n  M12 = {\n  }\n  M13 = M8 + p1 + M11 + M11\n  M15 = {\n  }\n"
            + "  M16 = {\n    M6 = 7\n    Lib.W(1) + p1 + M6\n  }\n  M17 = M16 + M19 + F.M1 + Lib.U\n  M18 = M1 + M17 + M12 + p2\n"
            + "  M19 = p1 + Lib.Y + F.M2\n  M21 = {\n  }\n  M11 + M7\n}\n";
        var (production, _) = AssertSameAsFormerWalk(Source);
        Assert.True(production.SettlementPathPartSeeds > 0);
    }

    /// <summary>
    /// PATH RESOLUTION (a guard). The provider's first member reads the library's last one back (<c>X1 = u + Lib.P{K}</c>),
    /// so settling a reader's parts meets the path <c>Q.X1</c> again while its own settlement is in progress and cuts there:
    /// the part settlements between are partial and none is kept, in production and with the per-path settlement that
    /// keeps no partial result for its component (where only the whole-settlement test refuses them). Only <c>X1</c> reads
    /// <c>u</c>, so a kept partial part would leave a later reader without it. Every reader requires every <c>p{i}</c>,
    /// <c>u</c> and <c>y</c>, as the former walk's metadata says in both modes.
    /// </summary>
    [Fact]
    public void PartSettlementsCutByACycle_AreNeverKept()
    {
        const int Members = 24;
        var source = new StringBuilder($"F(y, u, {Names("p", 1, Members)}) = {{\nQ = {{\npublic X1 = u + Lib.P{Members}\n");
        source.Append(string.Concat(Enumerable.Range(2, Members - 1).Select(j => $"public X{j} = y + {j}\n"))).Append("}\n");
        source.Append(Library(Members, i => $"Q.X{i}"));
        source.Append(string.Concat(Enumerable.Range(1, Members).Select(i => $"R{i} = Lib.P{i}\n"))).Append($"R{Members}\n}}\n");
        source.Append($"F(7, 5, {Arguments(Members)})\n");
        var text = source.ToString();
        var (production, _) = AssertSameAsFormerWalk(text);
        Assert.True(production.SettlementPathPartSeeds > 0);
        var perPath = With(PropertyExposureResolver.ComponentSettlementsPerPathForTesting, () => Parse(text));
        output.WriteLine($"production: part seeds {production.SettlementPathPartSeeds}, kept {production.SettlementPathPartsKept}, reuses {production.SettlementPathPartReuses}; "
            + $"per path: part seeds {perPath.Observations.SettlementPathPartSeeds}, kept {perPath.Observations.SettlementPathPartsKept}, reuses {perPath.Observations.SettlementPathPartReuses}");
        Assert.Equal(Former(() => With(PropertyExposureResolver.ComponentSettlementsPerPathForTesting, () => Parse(text))).Metadata, perPath.Metadata);
        Assert.Equal(Parse(text).Metadata, perPath.Metadata);
        Assert.True(perPath.Observations.SettlementPathPartSeeds > 0);
        var expected = new[] { "u", "y" }.Concat(Enumerable.Range(1, Members).Select(i => $"p{i}")).Order(StringComparer.Ordinal).ToArray();
        var root = Root(text);
        for (var i = 1; i <= Members; i++)
            Assert.Equal(expected, ExposureOpenChainComplexityTests.Member(root, "F", $"R{i}").RequiredAncestorParameters);
    }

    /// <summary>
    /// RETENTION BOUND. With the reuse tables' capacity lowered to 64 units, the kept part settlements stop at the bound and
    /// the later seeds are settled from their parts again or folded, with the same metadata; at the production capacity the
    /// same program keeps one settlement per part and site.
    /// </summary>
    [Fact]
    public void KeptPartSettlements_StopAtTheRetentionBound()
    {
        var source = ExposureResidualReuseTests.OwnerQualifiedRows(48, "path");
        var (production, _) = AssertSameAsFormerWalk(source);
        var bounded = WithCapacity(64, () => Parse(source));
        Assert.Equal(Parse(source).Metadata, bounded.Metadata);
        Assert.Equal(Former(() => Parse(source)).Metadata, bounded.Metadata);
        Assert.InRange(bounded.Observations.SettlementPathPartPeakWeight, 1, 64);
        Assert.True(bounded.Observations.RequiredAncestorSettlementFrames > production.RequiredAncestorSettlementFrames);
        output.WriteLine($"kept {production.SettlementPathPartsKept} -> {bounded.Observations.SettlementPathPartsKept}, "
            + $"part frames {production.SettlementPathPartFrames} -> {bounded.Observations.SettlementPathPartFrames}, "
            + $"frames {production.RequiredAncestorSettlementFrames} -> {bounded.Observations.RequiredAncestorSettlementFrames}, "
            + $"reuses {production.SettlementPathPartReuses} -> {bounded.Observations.SettlementPathPartReuses}");
        Assert.True(production.SettlementPathPartsKept > bounded.Observations.SettlementPathPartsKept);
    }

    // ── Production threshold differential ───────────────────────────────────

    /// <summary>
    /// THE PRODUCTION THRESHOLDS (no seam lowers a capacity or the copied-seed width): over generated programs — library
    /// members reading predecessors, parameters and paths, missing members, opened and bare names, shadowed providers, read
    /// through output rows, readers, intervening blocks with and without a parameter, inner owners, detached root readers
    /// and two libraries, with cycles and parameterized members — production publishes the former walk's diagnostics
    /// and metadata, and the unshared settlement's. A substantial share of them takes each new route.
    /// </summary>
    [Fact]
    public void GeneratedPrograms_AtTheProductionThresholds_PublishTheFormerWalksMetadata()
    {
        long shares = 0, anchored = 0, partFrames = 0, reused = 0, programs = 0;
        foreach (var source in GeneratedPrograms(240, seed: 11))
        {
            var production = Parse(source);
            var former = Former(() => Parse(source));
            Assert.Equal(former.Diagnostics, production.Diagnostics);
            Assert.Equal(former.Metadata, production.Metadata);
            var unshared = Unshared(() => Parse(source));
            Assert.Equal(unshared.Diagnostics, production.Diagnostics);
            Assert.Equal(unshared.Metadata, production.Metadata);
            programs++;
            var observations = production.Observations;
            if (observations.SummaryMemberPathShares > 0) shares++;
            if (observations.SettlementPathPartAnchorings > 0) anchored++;
            if (observations.SettlementPathPartFrames > 0) partFrames++;
            if (observations.SettlementPathPartReuses > 0) reused++;
        }

        output.WriteLine($"{programs} programs: path shares {shares}, anchored {anchored}, part frames {partFrames}, reused {reused}");
        Assert.InRange(shares, 30, programs);
        Assert.InRange(anchored, 15, programs);
        Assert.InRange(partFrames, 15, programs);
        Assert.InRange(reused, 10, programs);
    }

    /// <summary>Seeded random path programs (see <see cref="GeneratedPrograms_AtTheProductionThresholds_PublishTheFormerWalksMetadata"/>).</summary>
    internal static IEnumerable<string> GeneratedPrograms(int count, int seed)
    {
        var random = new Random(seed);
        for (var n = 0; n < count; n++)
        {
            var parameters = Enumerable.Range(1, 1 + random.Next(12)).Select(i => $"p{i}").ToArray();
            var members = 2 + random.Next(39);
            var width = 1 + random.Next(8);
            double Pick(params double[] values) => values[random.Next(values.Length)];
            string Name(params string[] values) => values[random.Next(values.Length)];
            var pathRate = Pick(0.9, 0.6, 0.3, 0.1);
            var predecessorRate = Pick(0.95, 0.8, 0.5);
            var twoPredecessors = random.Next(100) < 15;
            var missing = random.Next(5) == 0 ? 0.2 : 0;
            var opened = random.Next(5) == 0 ? 0.25 : 0;
            var bare = random.Next(5) == 0 ? 0.2 : 0;
            var shadows = random.Next(4) == 0 ? 0.25 : 0;
            var cycles = random.Next(100) < 12 ? 0.08 : 0;
            var parameterized = random.Next(100) < 12;
            var wideHead = random.Next(10) < 6;
            var layout = Name("rows", "rows", "readers", "readers2", "detached", "deep", "deepparam", "inner", "two", "self");

            string Path()
            {
                var r = random.NextDouble();
                if (r < missing) return $"Q.Miss{1 + random.Next(3)}";
                if (r < missing + opened) return Name("Z1", "Z2");
                if (r < missing + opened + bare) return "w";
                return $"Q.X{1 + random.Next(width)}";
            }

            string Member(int i)
            {
                var atoms = new List<string>();
                if (i == 1)
                {
                    atoms.Add(Name(parameters));
                    if (wideHead)
                    {
                        for (var a = 4 + random.Next(8); a > 0; a--) atoms.Add(Name(parameters));
                        for (var a = 1 + random.Next(4); a > 0; a--) atoms.Add(Path());
                    }
                }
                else
                {
                    if (random.NextDouble() < predecessorRate) atoms.Add($"P{i - 1}");
                    if (twoPredecessors && i > 2 && random.Next(2) == 0) atoms.Add($"P{i - 2}");
                    if (cycles > 0 && random.NextDouble() < cycles) atoms.Add($"P{1 + random.Next(members)}");
                    if (random.NextDouble() < 0.8) atoms.Add(Name(parameters));
                    if (random.NextDouble() < pathRate) atoms.Add(Path());
                    if (parameterized && random.NextDouble() < 0.2) atoms.Add($"N({Name([.. parameters, "1"])})");
                }
                if (atoms.Count == 0) atoms.Add((random.Next(9) + 1).ToString());
                return string.Join(" + ", atoms);
            }

            string LibraryOf(string name)
            {
                var library = new StringBuilder($"{name} = {{\n");
                if (parameterized) library.Append("N(z) = z + 1\n");
                for (var i = 1; i <= members; i++)
                {
                    var body = Member(i);
                    if (shadows > 0 && random.NextDouble() < shadows && i > 1)
                        library.Append($"public P{i} = {{\nQ = {{ public X1 = {i}\npublic X2 = 2 }}\n{body}\n}}\n");
                    else
                        library.Append($"public P{i} = {body}\n");
                }
                return library.Append("}\n").ToString();
            }

            var provider = "Q = {\n" + string.Concat(Enumerable.Range(1, width).Select(j => $"public X{j} = y + {j}\n")) + "}\n";
            var prefix = (opened > 0 ? "open O\n" : "") + provider + (opened > 0 ? "O = {\npublic Z1 = y\npublic Z2 = 3\n}\n" : "")
                + (bare > 0 ? "w = y + 7\n" : "");
            var signature = "y, " + string.Join(", ", parameters);
            var arguments = "7, " + string.Join(", ", parameters.Select(_ => random.Next(9) + 1));
            var picks = Enumerable.Range(0, layout == "rows" ? members : 1 + random.Next(members)).Select(_ => 1 + random.Next(members)).ToArray();
            string body;
            switch (layout)
            {
                case "rows":
                    body = prefix + LibraryOf("Lib") + string.Concat(picks.Select(i => $"Lib.P{i}\n"));
                    yield return $"F({signature}) = {{\n{body}}}\nF({arguments})\n";
                    break;
                case "two":
                    body = prefix + LibraryOf("Lib") + LibraryOf("Lib2") + string.Concat(picks.Select(i => $"{Name("Lib", "Lib2")}.P{i}\n"));
                    yield return $"F({signature}) = {{\n{body}}}\nF({arguments})\n";
                    break;
                case "self":
                    body = prefix + LibraryOf("Lib") + $"X = F.Lib.P{picks[0]}\nX\n";
                    yield return $"F({signature}) = {{\n{body}}}\nF({arguments})\n";
                    break;
                case "readers":
                case "readers2":
                    body = prefix + LibraryOf("Lib") + string.Concat(picks.Select((i, k) =>
                        $"R{k + 1} = Lib.P{i}" + (layout == "readers2" && random.Next(2) == 0 ? " + Q.X1" : "") + "\n")) + $"R{picks.Length}\n";
                    yield return $"F({signature}) = {{\n{body}}}\nF({arguments})\n";
                    break;
                case "detached":
                    body = prefix + LibraryOf("Lib") + "0\n";
                    yield return $"F({signature}) = {{\n{body}}}\n" + string.Concat(picks.Select((i, k) => $"R{k + 1} = F.Lib.P{i}\n")) + "0\n";
                    break;
                case "deep":
                case "deepparam":
                    var outer = layout == "deepparam" ? $"W1({Name(parameters)}) = {{" : "W1 = {";
                    var inner = random.Next(10) < 3 ? "Q = { public X1 = 1\npublic X2 = 2 }\n" : "";
                    body = prefix + $"{outer}\nW2 = {{\n{inner}" + LibraryOf("Lib") + "0\n}\n0\n}\n" + string.Concat(picks.Select(i => $"W1.W2.Lib.P{i}\n"));
                    yield return $"F({signature}) = {{\n{body}}}\nF({arguments})\n";
                    break;
                default:
                    var innerProvider = "Q = {\n" + string.Concat(Enumerable.Range(1, width).Select(j => $"public X{j} = z + {j}\n")) + "}\n";
                    body = prefix + $"G(z) = {{\n{innerProvider}" + LibraryOf("Lib") + string.Concat(picks.Select(i => $"Lib.P{i}\n")) + "}\nG(3)\n";
                    yield return $"F({signature}) = {{\n{body}}}\nF({arguments})\n";
                    break;
            }
        }
    }

    // ── Deferred providers ──────────────────────────────────────────────────

    private const string ModuleHost = "modules.example";

    private static RunOptions ModuleOptions()
        => new()
        {
            AllowedHosts = [ModuleHost],
            DownloadCode = (_, _) => ValueTask.FromResult("public X1 = 10\npublic X2 = 20\nZ = 1\n0"),
        };

    /// <summary>
    /// DEFERRED PROVIDERS. Inside a branch that loads a module (a deferred unit, compiled when it is selected), the
    /// library's members read the loaded module's members (<c>M.X1</c>, <c>M.X2</c>) and a local provider whose member reads
    /// the branch's own <c>a</c>, with readers wide enough to take path shares. The eager parse leaves the branch
    /// provisional; materializing it settles the readers through path shares, seeds settled part by part and kept part
    /// settlements, and publishes the former walk's metadata; the run value is the former walk's too.
    /// </summary>
    [Fact]
    public async Task ALibraryReadingADeferredProvider_MaterializesAsTheFormerWalk()
    {
        const int Members = 24;
        var library = new StringBuilder("    Lib = {\n    public P1 = a + M.X1 + Q.X1 + " + string.Join(" + ", Enumerable.Range(1, 8).Select(i => $"b{i}")) + "\n");
        for (var i = 2; i <= Members; i++) library.Append($"    public P{i} = P{i - 1} + a + {(i % 2 == 0 ? "M.X2" : "Q.X1")}\n");
        library.Append("    }\n");
        var source = $"G(0, {Names("b", 1, 8)}) = 0\nG(a, {Names("b", 1, 8)}) = {{\n    M = load('https://" + ModuleHost + "/m.kat')\n"
            + "    Q = { public X1 = a + 1 }\n" + library
            + string.Concat(Enumerable.Range(1, Members).Select(i => $"    R{i} = Lib.P{i}\n")) + $"    R{Members}\n}}\nG(1, {Arguments(8)})";

        async Task<(string Metadata, FrontEndTraversalObservations Observations)> Materialize()
        {
            var parsed = await SourceProvenance.ParseValidAsync(source, ModuleOptions());
            Assert.Empty(parsed.Diagnostics);
            var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.Root.Properties, property => property.Name == "G").Value);
            var region = Assert.Single(family.Branches, static branch => branch.Body.DeferredRegion is not null).Body.DeferredRegion!;
            var observations = new FrontEndTraversalObservations();
            region.Loader.TraversalObservations = observations;
            var body = await region.MaterializeAsync(CancellationToken.None);
            Assert.True(body.IsOk, body.IsOk ? "" : body.Error.ToString());
            return (ExposureSettlementFrameChargeTests.Metadata(body.Value), observations);
        }

        var production = await Materialize();
        var former = await Former(Materialize);
        Assert.Equal(former.Metadata, production.Metadata);
        Assert.True(production.Observations.SummaryMemberPathShares > 0);
        Assert.True(production.Observations.SettlementPathPartSeeds > 0);
        Assert.True(production.Observations.SettlementPathPartReuses > 0);
        Assert.Equal(0, former.Observations.SummaryMemberPathShares + former.Observations.SettlementPathPartSeeds);
        var run = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, ModuleOptions()));
        Assert.Equal(Assert.IsType<RunResult.Success>(await Former(() => KatLangEngine.RunAsync(source, ModuleOptions()))).ToDisplayString(),
            run.ToDisplayString());
    }

    // ── Cancellation and static limits ──────────────────────────────────────

    /// <summary>
    /// CANCELLATION inside the part-by-part settlement: the first settlement-frame checkpoint after a seed was settled part
    /// by part cancels the operation, which surfaces with its token and fails the unit; and inside a path share: the summary-channel
    /// checkpoint the share observes in place of the full expansion's cancels it before the share is made. A fresh parse
    /// then exposes in full with the uncancelled metadata and counters.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Cancellation_StopsThePathRoutes_AndAFreshParseExposesInFull(bool inAPathShare)
    {
        var checkpoint = inAPathShare ? FrontEndCancellationCheckpoint.SummaryChannel : FrontEndCancellationCheckpoint.ExposureSettlementFrame;
        var source = ExposureResidualReuseTests.OwnerQualifiedRows(64, "path");
        var expected = Parse(source);
        using var cancellation = new CancellationTokenSource();
        var cancelledAt = -1L;
        FrontEndTraversalObservations observations = null!;
        observations = new FrontEndTraversalObservations
        {
            CheckpointReached = (kind, _) =>
            {
                var progress = checkpoint == FrontEndCancellationCheckpoint.SummaryChannel
                    ? observations.SummaryMemberPathShares : observations.SettlementPathPartSeeds;
                if (kind != checkpoint || cancellation.IsCancellationRequested || progress == 0)
                    return;
                cancelledAt = progress;
                cancellation.Cancel();
            },
        };

        var (resolved, _, _) = ExposureSettlementFrameChargeTests.Resolved(source);
        var unit = resolved.CompletedStructure!.Facts;
        var error = Assert.ThrowsAny<OperationCanceledException>(
            () => PropertyExposureResolver.Resolve(resolved, observations, cancellationToken: cancellation.Token));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.True(unit.IsFailed);
        Assert.True(cancelledAt > 0);
        var progressAfter = checkpoint == FrontEndCancellationCheckpoint.SummaryChannel
            ? observations.SummaryMemberPathShares : observations.SettlementPathPartSeeds;
        Assert.Equal(cancelledAt, progressAfter);

        var again = Parse(source);
        Assert.Equal(expected.Diagnostics, again.Diagnostics);
        Assert.Equal(expected.Metadata, again.Metadata);
        Assert.Equal(expected.Observations.SettlementPathPartSeeds, again.Observations.SettlementPathPartSeeds);
        Assert.Equal(expected.Observations.SettlementPathPartReuses, again.Observations.SettlementPathPartReuses);
        Assert.Equal(expected.Observations.SummaryMemberPathShares, again.Observations.SummaryMemberPathShares);
    }

    /// <summary>
    /// STATIC LIMITS. Every part frame is charged as a settlement frame and every kept part, part classification and copy as
    /// seed-part work, so the operation's work bound applies as before: the path control is admitted at exactly the work it
    /// charges and refused one unit below, with the work-bound refusal. It charges less than the former walk, whose
    /// quadratic frames dominate.
    /// </summary>
    [Fact]
    public void ThePathRoutes_AreChargedAgainstTheWorkBound()
    {
        var source = ExposureResidualReuseTests.OwnerQualifiedRows(200, "path");
        long Run(long? limit)
        {
            var (resolved, ledger, _) = ExposureSettlementFrameChargeTests.Resolved(source,
                limits => limit.HasValue ? limits with { MaxEvaluations = limit.Value } : limits);
            _ = PropertyExposureResolver.Resolve(resolved, observations: null);
            return ledger.WorkCharged;
        }

        var exact = Run(null);
        Assert.Equal(exact, Run(exact));
        var refusal = Assert.Throws<StaticQueryLimitExceededException>(() => Run(exact - 1));
        Assert.Equal(StaticQueryBoundKind.Work, refusal.Bound);
        Assert.True(exact < Former(() => Run(null)));
    }
}
