using System.Text;
using Xunit.Abstractions;
using static KatLang.PropertyDependencyGraphBuilder;

namespace KatLang.Tests;

/// <summary>
/// MEMBERS BY REFERENCE (November 26 2026; C# exposure implementation only — no classification, requirement, diagnostic
/// kind, value or Lean rule changes). A member that reads several predecessors, each holding its own predecessors
/// (<c>P1 = p1</c>, <c>P2 = P1 + p2</c>, <c>P(i) = P(i-1) + P(i-2) + p(i)</c>), was a full level expansion that copied
/// both predecessors' widths and folded them: K² entries over a chain of K members, half of them already present (the
/// second predecessor's width is inside the first's), the other half each member's whole logical width, although the
/// owner's output read only <c>P1</c> (77 MB of 137 MB at K = 2,000 in the source measurement). An expansion now HOLDS
/// the member seeds it reads that carry no name and no reference, and folds them only when its fold budget is spent
/// (<see cref="HeldMemberSeeds.MustFold"/>), which bounds the entry and edge visits of a later fold.
/// Members of a cycle keep the folded seed, and the first member seed that carries a name or a reference ends the holding.
/// Oracles: the copy-and-fold union (<see cref="PropertyDependencyGraphBuilder.MemberSeedsCopiedForTesting"/>), compared
/// summary by summary in content and reference order and by published metadata, run values and deterministic counters,
/// never time.
/// </summary>
public sealed class SharedPredecessorExpansionTests(ITestOutputHelper output)
{
    // ── Harness ─────────────────────────────────────────────────────────────

    private static T Copied<T>(Func<T> work)
    {
        var previous = MemberSeedsCopiedForTesting.Value;
        MemberSeedsCopiedForTesting.Value = true;
        try { return work(); }
        finally { MemberSeedsCopiedForTesting.Value = previous; }
    }

    /// <summary>
    /// The eager parse of <paramref name="source"/> without PATH SHARES (<see cref="MemberPathSharesCopiedForTesting"/>),
    /// on both sides of every comparison here: a member that carries a reference and reads one predecessor would otherwise
    /// hold it in production and not in the copied union, which these counters compare. The path shares have their own
    /// oracle and counters (<c>ExposurePathPartTests</c>, which also reads <see cref="PathReaders"/>).
    /// </summary>
    private static (string Diagnostics, string Metadata, FrontEndTraversalObservations Observations) Parse(string source)
    {
        var previous = MemberPathSharesCopiedForTesting.Value;
        MemberPathSharesCopiedForTesting.Value = true;
        try
        {
            var observations = new FrontEndTraversalObservations();
            var parsed = Parser.ParseObserved(source, options: null, observations);
            var diagnostics = string.Join("\n", parsed.Diagnostics.Select(d => $"{d.Code}/{d.Severity}@{d.Span}: {d.Message}"));
            return (diagnostics, ExposureSettlementFrameChargeTests.Metadata(parsed.Root), observations);
        }
        finally { MemberPathSharesCopiedForTesting.Value = previous; }
    }

    /// <summary>
    /// Production and the copied union publish the same diagnostics and metadata through the same member solve: the same
    /// evaluations and full expansions, the same summary-channel checkpoints, settlement frames and level evaluations.
    /// </summary>
    private static (FrontEndTraversalObservations Held, FrontEndTraversalObservations Copied) AssertSameAsCopied(string source)
    {
        var held = Parse(source);
        var copied = Copied(() => Parse(source));
        Assert.Equal("", held.Diagnostics);
        Assert.Equal(copied.Diagnostics, held.Diagnostics);
        Assert.Equal(copied.Metadata, held.Metadata);
        Assert.Equal(copied.Observations.SummaryMemberEvaluations, held.Observations.SummaryMemberEvaluations);
        Assert.Equal(copied.Observations.SummaryMemberExpansions, held.Observations.SummaryMemberExpansions);
        Assert.Equal(copied.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel),
            held.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel));
        Assert.Equal(copied.Observations.RequiredAncestorSettlementFrames, held.Observations.RequiredAncestorSettlementFrames);
        Assert.Equal(copied.Observations.SettlementSeedPartWork, held.Observations.SettlementSeedPartWork);
        Assert.Equal(copied.Observations.RequiredAncestorLevelEvaluations, held.Observations.RequiredAncestorLevelEvaluations);
        Assert.Equal(0, copied.Observations.SummaryMemberExpansionHeldParts);
        return (held.Observations, copied.Observations);
    }

    private static void AssertLinear(long[] work)
    {
        Assert.InRange((double)work[1] / work[0], 1.5, 2.5);
        Assert.InRange((double)work[2] / work[1], 1.5, 2.5);
    }

    private static void AssertQuadratic(long[] work) => Assert.InRange((double)work[2] / work[1], 3.0, 5.0);

    private static string Value(string source) => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString();

    private static string Names(string prefix, int from, int to)
        => string.Join(", ", Enumerable.Range(from, to - from + 1).Select(i => $"{prefix}{i}"));

    private static string Arguments(int count) => string.Join(", ", Enumerable.Range(1, count));

    // ── Shapes ──────────────────────────────────────────────────────────────

    /// <summary>
    /// The source report's chain: <c>F(p1, …, pK)</c> with <c>P1 = p1</c>, <c>P2 = P1 + p2</c> and
    /// <c>P(i) = P(i-1) + P(i-2) + p(i)</c>; <paramref name="width"/> &gt; 0 cycles that many parameters instead (every
    /// member's width is bounded), and <paramref name="output"/> is <c>F</c>'s output (only <c>P1</c> by default).
    /// </summary>
    internal static string TwoPredecessorChain(int members, string output = "P1", int width = 0, string extra = "")
    {
        var parameters = width == 0 ? members : width;
        string P(int i) => $"p{(width == 0 ? i : 1 + (i - 1) % width)}";
        var source = new StringBuilder($"F({Names("p", 1, parameters)}) = {{\nP1 = p1\n");
        if (members >= 2)
            source.Append($"P2 = P1 + {P(2)}\n");
        for (var i = 3; i <= members; i++)
            source.Append($"P{i} = P{i - 1} + P{i - 2} + {P(i)}\n");
        source.Append(extra).Append(output).Append($"\n}}\nF({Arguments(parameters)})\n");
        return source.ToString();
    }

    /// <summary>The chain in a library <c>Lib</c> of <c>F</c>, read by <c>R(i) = Lib.P(i)</c> (or by output rows <c>Lib.P(i)</c>).</summary>
    private static string LibraryChain(int members, bool readers)
    {
        var source = new StringBuilder($"F({Names("p", 1, members)}) = {{\nLib = {{\npublic P1 = p1\npublic P2 = P1 + p2\n");
        for (var i = 3; i <= members; i++)
            source.Append($"public P{i} = P{i - 1} + P{i - 2} + p{i}\n");
        source.Append("}\n");
        for (var i = 1; i <= members; i++)
            source.Append(readers ? $"R{i} = Lib.P{i}\n" : $"Lib.P{i}\n");
        source.Append(readers ? $"R{members}\n" : "").Append($"}}\nF({Arguments(members)})\n");
        return source.ToString();
    }

    /// <summary>
    /// Readers that carry a path: <c>R(i) = P(i) + Lib.X</c> (no share shape: each is a full expansion holding <c>P(i)</c>),
    /// and with <paramref name="secondOrder"/> <c>S(i) = R(i) + Lib.Y</c>, which reads a seed carrying a reference and so
    /// copies and folds it: its fold walks <c>P(i)</c>'s held parts.
    /// </summary>
    internal static string PathReaders(int members, int width, bool secondOrder)
    {
        var body = TwoPredecessorChain(members, "0", width);
        var readers = new StringBuilder("Lib = {\npublic X = 1\npublic Y = 2\n}\n");
        for (var i = 1; i <= members; i++)
            readers.Append($"R{i} = P{i} + Lib.X\n");
        if (secondOrder)
            for (var i = 1; i <= members; i++)
                readers.Append($"S{i} = R{i} + Lib.Y\n");
        readers.Append(secondOrder ? $"S{members}" : $"R{members}");
        return body.Replace("\n0\n}", "\n" + readers + "\n}");
    }

    /// <summary>A shared dependency: <c>Base</c> reads K inputs, <c>A(i) = Base, a(i)</c>, <c>P(i) = A(i), Base, x(i)</c>.</summary>
    private static string SharedBase(int members)
    {
        var source = new StringBuilder($"F({Names("v", 1, members)}, {Names("a", 1, members)}, {Names("x", 1, members)}) = {{\n");
        source.Append($"Base = {Names("v", 1, members)}\n");
        for (var i = 1; i <= members; i++)
            source.Append($"A{i} = Base, a{i}\n");
        for (var i = 1; i <= members; i++)
            source.Append($"P{i} = A{i}, Base, x{i}\n");
        source.Append($"P1\n}}\nF({Arguments(3 * members)})\n");
        return source.ToString();
    }

    /// <summary>
    /// A shadowed dependency: <c>Q(i) = q(i)</c> and <c>P(i) = P(i-1) + Q(i) + p(i)</c>, where every odd <c>P(i)</c>
    /// declares its own <c>Q(i)</c>, which the sibling <c>Q(i)</c> is not: the odd members read one predecessor.
    /// </summary>
    private static string ShadowedChain(int members)
    {
        var source = new StringBuilder($"F({Names("p", 1, members)}, {Names("q", 1, members)}) = {{\n");
        for (var i = 1; i <= members; i++)
            source.Append($"Q{i} = q{i}\n");
        source.Append("P1 = Q1 + p1\n");
        for (var i = 2; i <= members; i++)
            source.Append(i % 2 == 1 ? $"P{i} = {{\nQ{i} = {i}\nP{i - 1} + Q{i} + p{i}\n}}\n" : $"P{i} = P{i - 1} + Q{i} + p{i}\n");
        source.Append($"P{members}\n}}\nF({Arguments(2 * members)})\n");
        return source.ToString();
    }

    /// <summary>
    /// The chain closed into one cycle through a member that reads a path (<c>P1 = P(K) + p1 + Lib.X</c>), so its members
    /// are evaluated one by one, again and again, while the cycle converges.
    /// </summary>
    private static string CyclicChain(int members)
        => TwoPredecessorChain(members, "Lib.X", extra: "Lib = {\npublic X = 1\n}\n")
            .Replace("P1 = p1\n", $"P1 = P{members} + p1 + Lib.X\n");

    // ── The source report's shape ───────────────────────────────────────────

    /// <summary>
    /// The chain whose output reads only <c>P1</c>: every member keeps its own delta and holds its predecessors, so the
    /// entries the expansions keep grow linearly (the union kept K² / 2), every member still requires exactly its
    /// <c>p1 … p(i)</c>, and the copied union, run through the same member solve, publishes the same metadata.
    /// </summary>
    [Fact]
    public void TwoPredecessorChain_KeepsEachMembersDelta_AndPublishesTheSameRequirements()
    {
        var sizes = new[] { 100, 200, 400 };
        var held = new long[3];
        var copied = new long[3];
        for (var k = 0; k < sizes.Length; k++)
        {
            var (production, union) = AssertSameAsCopied(TwoPredecessorChain(sizes[k]));
            Assert.Equal(sizes[k] - 1, production.SummaryMemberExpansions);
            Assert.InRange(production.SummaryMemberExpansionHeldParts, sizes[k], 2L * sizes[k]);
            Assert.Equal(0, production.SettlementSeedPartWork);
            Assert.Equal(0, production.MemberNavigationFolds);
            Assert.InRange(production.MemberEntriesCopied, 1, 100);
            Assert.InRange(production.MemberBudgetFoldEntries, 1, 16L * sizes[k]);
            held[k] = production.SummaryMemberExpansionEntries;
            copied[k] = union.SummaryMemberExpansionEntries;
            output.WriteLine($"K = {sizes[k]}: held {held[k]} entries, {production.SummaryMemberExpansionHeldParts} parts; union {copied[k]} entries");
        }

        AssertLinear(held);
        Assert.InRange(held[2], 1, 8L * sizes[2]);
        AssertQuadratic(copied);

        var root = SourceProvenance.ParseValid(TwoPredecessorChain(64)).Root;
        foreach (var i in new[] { 1, 2, 3, 17, 40, 64 })
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", $"P{i}"),
                Enumerable.Range(1, i).Select(p => $"p{p}").Order(StringComparer.Ordinal).Select(name => (name, 0)).ToArray());
        Assert.Equal("1", Value(TwoPredecessorChain(20)));
        Assert.Equal("46345", Value(TwoPredecessorChain(20, "P20")));
    }

    /// <summary>
    /// The bounded-width variant (16 parameters cycled, so every member's width stops at 16): the fold budget folds a
    /// member every few links, and the entries the expansions keep stay linear and below the union's.
    /// </summary>
    [Fact]
    public void BoundedWidthChain_FoldsWithinItsBudget_AndKeepsNoMoreThanTheUnion()
    {
        var sizes = new[] { 200, 400, 800 };
        var held = new long[3];
        for (var k = 0; k < sizes.Length; k++)
        {
            var (production, union) = AssertSameAsCopied(TwoPredecessorChain(sizes[k], width: 16));
            held[k] = production.SummaryMemberExpansionEntries;
            Assert.InRange(held[k], 1, union.SummaryMemberExpansionEntries);
            output.WriteLine($"K = {sizes[k]}: held {held[k]} entries; union {union.SummaryMemberExpansionEntries}");
        }

        AssertLinear(held);
    }

    // ── Retained storage and the folds of readers ───────────────────────────

    /// <summary>The member seeds of every summary <paramref name="memo"/> keeps for a level declaring <paramref name="member"/>.</summary>
    private static IReadOnlyDictionary<string, SummarySeed> MemberSeedsOf(SummaryMemo memo, string member)
    {
        var summaries = (memo.IndependentAlgorithmSummaries?.Values ?? Enumerable.Empty<AlgorithmSummary>())
            .Concat(memo.ContextualAlgorithmSummaries?.Values ?? Enumerable.Empty<AlgorithmSummary>());
        return Assert.Single(summaries.Distinct(), summary => summary.MemberSeeds.ContainsKey(member)).MemberSeeds;
    }

    // Every distinct seed reachable from `seed` through the parts it holds, itself included.
    private static List<SummarySeed> Reachable(SummarySeed seed)
    {
        var seen = new HashSet<SummarySeed>(ReferenceEqualityComparer.Instance);
        var order = new List<SummarySeed>();
        var pending = new Stack<SummarySeed>();
        pending.Push(seed);
        while (pending.TryPop(out var part))
        {
            if (!seen.Add(part))
                continue;
            order.Add(part);
            foreach (var child in part.AbsorbedPartsWithoutFolding ?? [])
                pending.Push(child);
        }

        return order;
    }

    // The folded width of a stored seed, taken from a clone: the stored seed is not folded.
    private static int Width(SummarySeed seed)
    {
        var clone = seed.Clone();
        return clone.RequiredAncestorOwnedParameterNames.Count + clone.OwnerQualifiedParameters.Count
            + clone.PendingReferences.Count + clone.VisiblePropertyDependencyNames.Count;
    }

    /// <summary>
    /// RETAINED STORAGE: the completed summaries a resolution keeps hold each member's delta and its predecessors by
    /// reference, so the entries their distinct seeds store grow linearly, while each member's logical width — what a fold
    /// of it yields — is still <c>i</c> (K (K + 1) / 2 in all); the copied union stored every width.
    /// </summary>
    [Fact]
    public void RetainedMemberSeeds_StoreLinearEntries_ForTheirQuadraticLogicalWidth()
    {
        var sizes = new[] { 100, 200, 400 };
        var held = new long[3];
        var copied = new long[3];
        for (var k = 0; k < sizes.Length; k++)
        {
            var root = SourceProvenance.ParseValid(TwoPredecessorChain(sizes[k])).Root;
            long Stored(bool union)
            {
                var memo = StandaloneSummaries.MemoFor(root);
                if (union) Copied(() => StandaloneSummaries.Build(root, memo));
                else StandaloneSummaries.Build(root, memo);
                var members = MemberSeedsOf(memo, "P1");
                Assert.Equal((long)sizes[k] * (sizes[k] + 1) / 2, members.Values.Sum(seed => (long)Width(seed)));
                return members.Values.SelectMany(Reachable).Distinct(ReferenceEqualityComparer.Instance).Cast<SummarySeed>()
                    .Sum(seed => (long)seed.OwnEntryCount);
            }

            held[k] = Stored(union: false);
            copied[k] = Stored(union: true);
            output.WriteLine($"K = {sizes[k]}: held seeds store {held[k]} entries; union {copied[k]}");
        }

        AssertLinear(held);
        AssertQuadratic(copied);
    }

    /// <summary>
    /// A reader that folds a held member seed — a level's output, an expansion that meets a seed carrying a reference, a
    /// navigation through a level with parameters — walks every part the seed holds. The fold budget keeps that walk within
    /// the seed's width plus the two parts a link holds, on chains of growing and of bounded width alike, so a fold never
    /// costs more than a bounded multiple of what the union copied for that member.
    /// </summary>
    [Theory]
    [InlineData("growing", 300)]
    [InlineData("bounded", 300)]
    [InlineData("shared", 120)]
    public void HeldMemberSeeds_HoldNoMorePartsThanTheirWidth(string shape, int members)
    {
        var source = shape switch
        {
            "growing" => TwoPredecessorChain(members),
            "bounded" => TwoPredecessorChain(members, width: 16),
            _ => SharedBase(members),
        };
        var root = SourceProvenance.ParseValid(source).Root;
        var memo = StandaloneSummaries.MemoFor(root);
        StandaloneSummaries.Build(root, memo);
        var memberSeeds = MemberSeedsOf(memo, "P1");
        var holding = 0;
        foreach (var (name, seed) in memberSeeds)
        {
            var parts = Reachable(seed).Count - 1;
            if (parts > 0)
                holding++;
            Assert.True(parts <= Width(seed) + 2, $"{name} holds {parts} parts for width {Width(seed)}");
        }

        Assert.InRange(holding, memberSeeds.Count / 2, memberSeeds.Count);
    }

    // ── Downstream reads: the copies do not move to the readers ─────────────

    [Fact]
    public void BranchingUnionsOverOneWideBase_BoundTheWholeFold()
    {
        const int width = 32, leaves = 128;
        var source = new StringBuilder($"F({Names("p", 1, width)}) = {{\nBase = {Names("p", 1, width)}\n");
        for (var i = 0; i < leaves; i++)
            source.Append($"L{i} = Base, p{1 + i % width}, p{1 + i / width}\n");
        var row = Enumerable.Range(0, leaves).Select(i => $"L{i}").ToArray();
        var id = 0;
        while (row.Length > 1)
        {
            row = row.Chunk(2).Select(pair =>
            {
                var name = $"U{++id}";
                source.Append($"{name} = {pair[0]}, {pair[1]}\n");
                return name;
            }).ToArray();
        }

        source.Append($"L0\n}}\nF({Arguments(width)})\n");
        var root = SourceProvenance.ParseValid(source.ToString()).Root;
        var memo = StandaloneSummaries.MemoFor(root);
        StandaloneSummaries.Build(root, memo);
        var members = MemberSeedsOf(memo, row[0]);
        for (var i = 1; i <= id; i++)
        {
            var seed = members[$"U{i}"];
            var work = Reachable(seed).Sum(part => part.OwnEntryCount + (part.AbsorbedPartsWithoutFolding?.Count ?? 0));
            Assert.InRange(work, width, 4 * width);
        }
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void NavigatingMembers_PreservesTheExactAdmissionBoundary(bool readers)
    {
        var source = LibraryChain(48, readers).Replace("public P2 = P1 + p2",
            "public Tail = P48 + p1\npublic Alias = Tail\npublic P2 = P1 + p2")
            .Replace("Lib.P48\n", "Lib.P48 + Lib.Alias\n");
        long Run(long? limit)
        {
            var (resolved, ledger, _) = ExposureSettlementFrameChargeTests.Resolved(source,
                limits => limit.HasValue ? limits with { MaxEvaluations = limit.Value } : limits);
            _ = PropertyExposureResolver.Resolve(resolved);
            return ledger.WorkCharged;
        }

        var exact = Copied(() => Run(null));
        Assert.Equal(exact, Run(exact));
        Assert.Throws<StaticQueryLimitExceededException>(() => Run(exact - 1));
        Assert.Throws<StaticQueryLimitExceededException>(() => Copied(() => Run(exact - 1)));
    }

    [Fact]
    public void RepeatedNavigationReusesTheFlatViewAndKeepsTheSharedMemberIntact()
    {
        var root = SourceProvenance.ParseValid(TwoPredecessorChain(100)).Root;
        var observations = new FrontEndTraversalObservations();
        var memo = StandaloneSummaries.MemoFor(root, observations);
        StandaloneSummaries.Build(root, memo);
        var member = MemberSeedsOf(memo, "P1").Values.Last(seed => seed.NeedsNavigationView);
        var parts = member.AbsorbedPartsWithoutFolding;
        Assert.NotNull(parts);
        var flat = memo.ForNavigation(member);
        var entriesRead = observations.MemberNavigationEntriesRead;
        Assert.Null(flat.AbsorbedPartsWithoutFolding);
        Assert.Equal(Width(member), Width(flat));
        for (var i = 0; i < 100; i++)
            Assert.Same(flat, memo.ForNavigation(member));
        Assert.Equal(1, observations.MemberNavigationFolds);
        Assert.Equal(entriesRead, observations.MemberNavigationEntriesRead);
        Assert.Same(parts, member.AbsorbedPartsWithoutFolding);

        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var other = new SummaryMemo { CancellationToken = cancellation.Token };
        var error = Assert.Throws<OperationCanceledException>(() => other.ForNavigation(member));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Same(parts, member.AbsorbedPartsWithoutFolding);
    }

    /// <summary>
    /// Substantial downstream reads of the chain: output rows reading every member, readers navigating every member of a
    /// library chain, path-bearing readers and readers of those. The member expansions keep no more entries than the
    /// union's, and linearly many wherever a reader holds what it reads; a reader of a path-bearing reader folds it, which
    /// on a chain of growing width keeps that reader's whole width, exactly as the union copied it. The published lists
    /// store no more entries than the union's, and the metadata, frames and level evaluations are the union's; the
    /// navigated members keep the eager solver's charge and reuse their flat view on subsequent reads.
    /// </summary>
    [Theory]
    [InlineData("rows")]
    [InlineData("library-rows")]
    [InlineData("library-readers")]
    [InlineData("path-readers")]
    [InlineData("second-order-readers")]
    [InlineData("bounded-second-order-readers")]
    public void DownstreamReads_DoNotMoveTheCopiesToTheReaders(string shape)
    {
        var sizes = new[] { 100, 200, 400 };
        var held = new long[3];
        for (var k = 0; k < sizes.Length; k++)
        {
            var source = shape switch
            {
                "rows" => TwoPredecessorChain(sizes[k], string.Join("\n", Enumerable.Range(1, sizes[k]).Select(i => $"P{i}"))),
                "library-rows" => LibraryChain(sizes[k], readers: false),
                "library-readers" => LibraryChain(sizes[k], readers: true),
                "path-readers" => PathReaders(sizes[k], 0, secondOrder: false),
                "second-order-readers" => PathReaders(sizes[k], 0, secondOrder: true),
                _ => PathReaders(sizes[k], 16, secondOrder: true),
            };
            var (production, union) = AssertSameAsCopied(source);
            Assert.InRange(ListEntries(production), 0, ListEntries(union));
            Assert.InRange(production.SummaryMemberExpansionEntries, 1, union.SummaryMemberExpansionEntries);
            held[k] = production.SummaryMemberExpansionEntries;
            if (shape is "library-rows" or "library-readers")
            {
                Assert.InRange(production.MemberNavigationFolds, 1, sizes[k]);
                var logicalEntries = (long)sizes[k] * (sizes[k] + 1) / 2;
                Assert.InRange(production.MemberNavigationEntriesRead, 1, 2 * logicalEntries);
            }
            output.WriteLine($"K = {sizes[k]}: held {held[k]} entries, {production.SettlementSeedPartWork} seed-part units, "
                + $"{ListEntries(production)} list entries; union {union.SummaryMemberExpansionEntries} entries, {ListEntries(union)} list entries");
        }

        if (shape != "second-order-readers")
            AssertLinear(held);

        static long ListEntries(FrontEndTraversalObservations observations)
            => observations.RequiredAncestorListEntriesMaterialized + observations.RequiredAncestorPersistentBaseEntries
                + observations.RequiredAncestorDerivedEntries;
    }

    // ── Controls ────────────────────────────────────────────────────────────

    /// <summary>
    /// Flat members read no member; a narrow chain (<c>P(i) = P(i-1) + p(i)</c>) shares its one predecessor without an
    /// expansion; members reading one member through two aliases share one seed: none of them holds anything new, and each
    /// keeps exactly the union's entries.
    /// </summary>
    [Theory]
    [InlineData("flat")]
    [InlineData("narrow")]
    [InlineData("aliases")]
    public void FlatNarrowAndAliasedControls_AreUnchanged(string shape)
    {
        const int Members = 200;
        var source = shape switch
        {
            "flat" => $"F({Names("p", 1, Members)}) = {{\n" + string.Concat(Enumerable.Range(1, Members).Select(i => $"P{i} = p{i} + {i}\n"))
                + $"P1\n}}\nF({Arguments(Members)})\n",
            "narrow" => $"F({Names("p", 1, Members)}) = {{\nP1 = p1\n" + string.Concat(Enumerable.Range(2, Members - 1).Select(i => $"P{i} = P{i - 1} + p{i}\n"))
                + $"P1\n}}\nF({Arguments(Members)})\n",
            _ => $"F({Names("v", 1, Members)}, {Names("x", 1, Members)}) = {{\nBase = {Names("v", 1, Members)}\nL = Base\nR = Base\n"
                + string.Concat(Enumerable.Range(1, Members).Select(i => $"P{i} = L, R, x{i}\n")) + $"P1\n}}\nF({Arguments(2 * Members)})\n",
        };
        var (production, union) = AssertSameAsCopied(source);
        Assert.Equal(0, production.SummaryMemberExpansionHeldParts);
        Assert.Equal(union.SummaryMemberExpansionEntries, production.SummaryMemberExpansionEntries);
    }

    /// <summary>
    /// A SHARED dependency (two predecessors that hold one wide <c>Base</c>): each member holds both and stores its delta,
    /// where the union copied <c>Base</c>'s width per member. A SHADOWED one (odd members declare their own <c>Q(i)</c>):
    /// exactly the dependencies the members read are held, so the odd members never require the shadowed sibling's input.
    /// </summary>
    [Fact]
    public void SharedAndShadowedDependencies_HoldExactlyWhatIsRead()
    {
        var sizes = new[] { 100, 200, 400 };
        var held = new long[3];
        var copied = new long[3];
        for (var k = 0; k < sizes.Length; k++)
        {
            var (production, union) = AssertSameAsCopied(SharedBase(sizes[k]));
            Assert.InRange(production.SummaryMemberExpansionHeldParts, sizes[k], 3L * sizes[k]);
            held[k] = production.SummaryMemberExpansionEntries;
            copied[k] = union.SummaryMemberExpansionEntries;
        }

        AssertLinear(held);
        AssertQuadratic(copied);

        const int Members = 41;
        var shadowed = ShadowedChain(Members);
        AssertSameAsCopied(shadowed);
        var root = SourceProvenance.ParseValid(shadowed).Root;
        var expected = Enumerable.Range(1, Members).Select(i => $"p{i}")
            .Concat(Enumerable.Range(1, Members).Where(i => i == 1 || i % 2 == 0).Select(i => $"q{i}"))
            .Order(StringComparer.Ordinal).Select(name => (name, 0)).ToArray();
        ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", $"P{Members}"), expected);
    }

    // ── Convergence, cancellation and order ─────────────────────────────────

    /// <summary>
    /// CONVERGENCE: members of a cycle are evaluated again while it converges, and each change detection compares their
    /// seeds whole, so they keep the union's folded seed: the same evaluations, the same entries kept, nothing held.
    /// </summary>
    [Theory]
    [InlineData(20)]
    [InlineData(40)]
    public void CycleMembers_KeepTheFoldedSeed(int members)
    {
        var (production, union) = AssertSameAsCopied(CyclicChain(members));
        Assert.InRange(production.SummaryMemberEvaluations, members + 1, long.MaxValue);
        Assert.Equal(0, production.SummaryMemberExpansionHeldParts);
        Assert.Equal(union.SummaryMemberExpansionEntries, production.SummaryMemberExpansionEntries);

        // A member that reads itself is a cycle of one: it holds neither the wide A nor B, which holds A. Without the
        // cycle, the same member holds both.
        string Level(string reads) => $"F({Names("p", 1, 10)}) = {{\nA = {string.Join(" + ", Enumerable.Range(1, 9).Select(i => $"p{i}"))}\n"
            + $"B = A + p10\nC = {reads}\nB\n}}\nF({Arguments(10)})\n";
        Assert.Equal(0, AssertSameAsCopied(Level("C + A + B")).Held.SummaryMemberExpansionHeldParts);
        Assert.Equal(2, AssertSameAsCopied(Level("A + B + 1")).Held.SummaryMemberExpansionHeldParts);
    }

    /// <summary>
    /// CANCELLATION: a holding expansion observes the summary channel's checkpoint where the union did, and a cancelled one
    /// escapes with the token, records nothing after the cancelling checkpoint, and leaves nothing behind: a fresh parse
    /// publishes the uncancelled metadata.
    /// </summary>
    [Fact]
    public void CancellationInsideAHoldingSolve_EscapesWithTheToken_AndLeavesNothingBehind()
    {
        var source = TwoPredecessorChain(200);
        var uncancelled = Parse(source);
        // The summary-channel checkpoint at which the solve has first held a member seed, plus some: one inside the solve.
        long firstHolding = -1;
        FrontEndTraversalObservations probe = null!;
        probe = new FrontEndTraversalObservations
        {
            CheckpointReached = (kind, ordinal) =>
            {
                if (kind == FrontEndCancellationCheckpoint.SummaryChannel && firstHolding < 0 && probe.SummaryMemberExpansionHeldParts > 0)
                    firstHolding = ordinal;
            },
        };
        Parser.ParseObserved(source, options: null, probe);
        Assert.InRange(firstHolding, 1, long.MaxValue);
        var cancelAt = firstHolding + 25;
        using var cancellation = new CancellationTokenSource();
        long heldAtCancel = -1, entriesAtCancel = -1;
        FrontEndTraversalObservations observations = null!;
        observations = new FrontEndTraversalObservations
        {
            CheckpointReached = (kind, ordinal) =>
            {
                if (kind != FrontEndCancellationCheckpoint.SummaryChannel || ordinal != cancelAt || cancellation.IsCancellationRequested)
                    return;
                heldAtCancel = observations.SummaryMemberExpansionHeldParts;
                entriesAtCancel = observations.SummaryMemberExpansionEntries;
                cancellation.Cancel();
            },
        };

        var error = Assert.Throws<OperationCanceledException>(() => Parser.ParseObserved(
            source, new RunOptions { SourceProcessingCancellationToken = cancellation.Token }, observations));

        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal(cancelAt, observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel));
        Assert.InRange(heldAtCancel, 1, long.MaxValue);
        Assert.Equal(heldAtCancel, observations.SummaryMemberExpansionHeldParts);
        Assert.Equal(entriesAtCancel, observations.SummaryMemberExpansionEntries);
        Assert.Equal(uncancelled.Metadata, Parse(source).Metadata);
    }

    /// <summary>
    /// ORDER, REQUIREMENTS AND OWNERS: over generated levels — members reading several siblings, parameters of the owner
    /// and of a nested owner with the same names, paths, opened names, members shadowed by local declarations, cycles,
    /// parameterized members, wide shared members, and readers navigating members from outside the owner — every summary
    /// the member solve computes (output and member seeds) is the union's: the same required names, owner-qualified
    /// parameters and visible names, and the same references in the same order with the same origins, so the owning
    /// level settles them in the same order. Each program's metadata and diagnostics are the union's too.
    /// </summary>
    [Fact]
    public void GeneratedLevels_HeldSummariesAreTheUnionsInContentAndReferenceOrder()
    {
        var programs = GeneratedLevels(400, seed: 26)
            .Concat(new[] { 3, 9, 17 }.SelectMany(k => new[]
            {
                TwoPredecessorChain(k), TwoPredecessorChain(k, "P" + k, width: 4), LibraryChain(k, readers: true),
                PathReaders(k, 0, secondOrder: true), SharedBase(k), ShadowedChain(k), CyclicChain(k),
            }));
        var compared = 0;
        var holdingPrograms = 0;
        foreach (var source in programs)
        {
            var held = Parse(source);
            var copied = Copied(() => Parse(source));
            Assert.Equal(copied.Diagnostics, held.Diagnostics);
            Assert.Equal(copied.Metadata, held.Metadata);
            Assert.Equal(copied.Observations.SettlementSeedPartWork, held.Observations.SettlementSeedPartWork);
            if (held.Diagnostics.Length != 0)
                continue;
            if (held.Observations.SummaryMemberExpansionHeldParts > 0)
                holdingPrograms++;

            var root = SourceProvenance.ParseValid(source).Root;
            var context = AnalyzedStaticStructures.ForBoundAst(root);
            var heldMemo = StandaloneSummaries.MemoFor(root);
            var copiedMemo = StandaloneSummaries.MemoFor(root);
            PropertyDependencyGraphBuilder.BuildSummaries(root, context, heldMemo);
            Copied(() => PropertyDependencyGraphBuilder.BuildSummaries(root, context, copiedMemo));
            compared += CompareSummaries(heldMemo, copiedMemo, source);
        }

        output.WriteLine($"{compared} summaries compared; {holdingPrograms} programs held member seeds");
        Assert.InRange(holdingPrograms, 60, int.MaxValue);
    }

    private static int CompareSummaries(SummaryMemo held, SummaryMemo copied, string source)
    {
        var compared = 0;
        foreach (var (algorithm, summary) in copied.IndependentAlgorithmSummaries ?? [])
        {
            Assert.True(held.IndependentAlgorithmSummaries!.TryGetValue(algorithm, out var other), source);
            Assert.Null(SummaryMemo.AdoptedSummaryDifference(other, summary));
            compared++;
        }

        foreach (var (key, summary) in copied.ContextualAlgorithmSummaries ?? [])
        {
            Assert.True(held.ContextualAlgorithmSummaries!.TryGetValue(key, out var other), source);
            Assert.Null(SummaryMemo.AdoptedSummaryDifference(other, summary));
            compared++;
        }

        Assert.Equal(copied.IndependentAlgorithmSummaries?.Count ?? 0, held.IndependentAlgorithmSummaries?.Count ?? 0);
        Assert.Equal(copied.ContextualAlgorithmSummaries?.Count ?? 0, held.ContextualAlgorithmSummaries?.Count ?? 0);
        return compared;
    }

    /// <summary>Seeded random levels of members that read siblings (see <see cref="GeneratedLevels_HeldSummariesAreTheUnionsInContentAndReferenceOrder"/>).</summary>
    private static IEnumerable<string> GeneratedLevels(int count, int seed)
    {
        var random = new Random(seed);
        for (var n = 0; n < count; n++)
        {
            // Half the levels carry no path and no opened name and are wider: their members' widths grow past what an
            // expansion copies while they stay holdable.
            var pure = random.Next(2) == 0;
            var parameters = Enumerable.Range(1, pure ? 9 + random.Next(12) : 1 + random.Next(14)).Select(i => $"p{i}").ToArray();
            var members = pure ? 10 + random.Next(21) : 2 + random.Next(24);
            var opened = !pure && random.Next(3) == 0;
            var nested = random.Next(4) == 0;
            var detached = nested && random.Next(2) == 0;
            var cycles = random.Next(10) < (pure ? 1 : 3) ? 0.08 : 0.0;
            var paths = pure ? 0.0 : random.Next(2) == 0 ? 0.15 : 0.03;
            var siblings = pure ? 0.4 : 0.30;
            var reads = pure ? 0.45 : 0.25;
            var shadows = random.Next(10) < 3 ? 0.2 : 0.0;
            var parameterized = random.Next(5) == 0;
            var wide = random.Next(5) == 0;
            string Pick(params string[] items) => items[random.Next(items.Length)];
            string Atom(int i)
            {
                var r = random.NextDouble();
                if (r < siblings && i > 1)
                {
                    var back = random.NextDouble() < 0.7 ? 1 + random.Next(2) : 1 + random.Next(i - 1);
                    return $"M{i - Math.Min(back, i - 1)}";
                }
                if (r < siblings + cycles) return $"M{1 + random.Next(members)}";
                if (r < siblings + reads) return Pick(parameters);
                if (r < siblings + reads + paths) return Pick("Lib.X", "Lib.Y", "Lib.W(1)");
                if (opened && r < 0.75) return Pick("Z", "Z2");
                if (parameterized && r < 0.8 && i > 2) return $"N({Pick([.. parameters, "1"])})";
                if (wide && r < 0.85) return "Base";
                return (random.Next(9) + 1).ToString();
            }

            var lines = new List<string>();
            if (opened) lines.Add("open O");
            lines.AddRange(["Lib = {", $"public X = {Pick(parameters)} + 1", "public Y = 2", $"public W(a) = a + {Pick([.. parameters, "3"])}", "}"]);
            if (opened) lines.AddRange(["O = {", $"public Z = {Pick(parameters)}", "public Z2 = 5", "}"]);
            if (wide) lines.Add("Base = " + string.Join(", ", Enumerable.Range(0, 9).Select(_ => Pick(parameters))));
            if (parameterized) lines.Add($"N(z) = z + {Pick(parameters)}");
            for (var i = 1; i <= members; i++)
            {
                var atoms = Enumerable.Range(0, (pure ? 2 : 1) + random.Next(3)).Select(_ => Atom(i)).ToList();
                var visibility = detached && random.Next(2) == 0 ? "public " : "";
                if (shadows > 0 && random.NextDouble() < shadows && i > 2)
                {
                    var local = $"M{i - 1 - random.Next(i - 1)}";
                    lines.AddRange([$"{visibility}M{i} = {{", $"{local} = {random.Next(9) + 1}", string.Join(" + ", [.. atoms, local]), "}"]);
                }
                else
                    lines.Add($"{visibility}M{i} = {string.Join(" + ", atoms)}");
            }

            lines.Add(string.Join(" + ", Enumerable.Range(0, 1 + random.Next(3)).Select(_ => $"M{1 + random.Next(members)}")));
            var arguments = string.Join(", ", parameters.Select(_ => random.Next(9) + 1));
            var signature = string.Join(", ", parameters);
            var body = string.Join("\n", lines);
            if (!nested)
            {
                yield return $"F({signature}) = {{\n{body}\n}}\nF({arguments})\n";
                continue;
            }

            var inner = random.Next(2) == 0 ? parameters : parameters[..(1 + random.Next(parameters.Length))];
            var innerArguments = string.Join(", ", inner.Select(_ => random.Next(9) + 1));
            var program = new StringBuilder($"F({signature}) = {{\nG({string.Join(", ", inner)}) = {{\n{body}\n}}\nG({innerArguments})\n}}\n");
            if (detached)
                for (var q = 1 + random.Next(3); q > 0; q--)
                    program.Append($"Q{q} = F.G.M{1 + random.Next(members)}\n");
            yield return program.Append($"F({arguments})\n").ToString();
        }
    }
}
