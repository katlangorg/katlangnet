using System.Reflection;
using System.Text;
using Xunit.Abstractions;
using static KatLang.PropertyDependencyGraphBuilder;

namespace KatLang.Tests;

/// <summary>
/// SHARE FOLDS (November 27 2026; C# exposure implementation only — no classification, requirement, diagnostic kind, value
/// or Lean rule changes). A narrow chain <c>P1 = p1</c>, <c>P(i) = P(i-1) + p(i)</c> is a chain of single-predecessor
/// shares (<c>TryShareMemberSeed</c>): each member holds its predecessor, one level deeper every eight members, and the
/// shares never folded. Every member's fold budget therefore ran out after a few dozen members, and from there each reader
/// of a member — a path-bearing reader <c>R(i) = P(i) + Lib.X</c> as much as a full expansion — copied the member's whole
/// width: K² / 2 entries over K readers (255 MB of exposure allocation at K = 2,000). A share outside a cycle whose
/// content carries no name and no reference now takes MEMBERS BY REFERENCE's budget (<see cref="HeldMemberSeeds.MustFold"/>)
/// and folds what it holds once that is spent, so the chain folds at widths that grow geometrically and its readers hold
/// it. Oracle: the former shares (<see cref="PropertyDependencyGraphBuilder.MemberSharesUnfoldedForTesting"/>), compared by
/// published metadata, diagnostics, every summary in content and reference order, run values and deterministic counters,
/// never time.
/// </summary>
public sealed class ShareFoldBudgetTests(ITestOutputHelper output)
{
    // ── Harness ─────────────────────────────────────────────────────────────

    private static T Unfolded<T>(Func<T> work)
    {
        var previous = MemberSharesUnfoldedForTesting.Value;
        MemberSharesUnfoldedForTesting.Value = true;
        try { return work(); }
        finally { MemberSharesUnfoldedForTesting.Value = previous; }
    }

    private static (string Diagnostics, string Metadata, FrontEndTraversalObservations Observations) Parse(string source)
    {
        var observations = new FrontEndTraversalObservations();
        var parsed = Parser.ParseObserved(source, options: null, observations);
        var diagnostics = string.Join("\n", parsed.Diagnostics.Select(d => $"{d.Code}/{d.Severity}@{d.Span}: {d.Message}"));
        return (diagnostics, ExposureSettlementFrameChargeTests.Metadata(parsed.Root), observations);
    }

    /// <summary>
    /// Production and the former shares publish the same diagnostics and metadata through the same member solve: the same
    /// evaluations, summary-channel checkpoints, settlement frames, seed-part work and level evaluations.
    /// </summary>
    private static (FrontEndTraversalObservations Folded, FrontEndTraversalObservations Unfolded) AssertSameAsUnfolded(string source)
    {
        var folded = Parse(source);
        var unfolded = Unfolded(() => Parse(source));
        Assert.Equal("", folded.Diagnostics);
        Assert.Equal(unfolded.Diagnostics, folded.Diagnostics);
        Assert.Equal(unfolded.Metadata, folded.Metadata);
        Assert.Equal(unfolded.Observations.SummaryMemberEvaluations, folded.Observations.SummaryMemberEvaluations);
        Assert.Equal(unfolded.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel),
            folded.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel));
        Assert.Equal(unfolded.Observations.RequiredAncestorSettlementFrames, folded.Observations.RequiredAncestorSettlementFrames);
        Assert.Equal(unfolded.Observations.SettlementSeedPartWork, folded.Observations.SettlementSeedPartWork);
        Assert.Equal(unfolded.Observations.RequiredAncestorLevelEvaluations, folded.Observations.RequiredAncestorLevelEvaluations);
        Assert.Equal(0, unfolded.Observations.SummaryMemberShareFolds);
        return (folded.Observations, unfolded.Observations);
    }

    /// <summary>Every numeric counter of an observer, by name, with every checkpoint kind.</summary>
    private static string Counters(FrontEndTraversalObservations observations)
    {
        var counters = new SortedDictionary<string, long>(StringComparer.Ordinal);
        foreach (var property in typeof(FrontEndTraversalObservations).GetProperties(BindingFlags.Instance | BindingFlags.Public))
        {
            if (property.GetIndexParameters().Length == 0 && (property.PropertyType == typeof(long) || property.PropertyType == typeof(int)))
                counters[property.Name] = Convert.ToInt64(property.GetValue(observations));
        }

        foreach (var kind in Enum.GetValues<FrontEndCancellationCheckpoint>())
            counters["Checkpoints." + kind] = observations.CancellationCheckpointsOf(kind);
        return string.Join(", ", counters.Select(counter => $"{counter.Key}={counter.Value}"));
    }

    private static void AssertLinear(long[] values)
    {
        Assert.InRange((double)values[1] / values[0], 1.5, 2.5);
        Assert.InRange((double)values[2] / values[1], 1.5, 2.5);
    }

    private static void AssertQuadratic(long[] values) => Assert.InRange((double)values[2] / values[1], 3.0, 5.0);

    private static string Value(string source) => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString();

    private static string Names(string prefix, int from, int to)
        => string.Join(", ", Enumerable.Range(from, to - from + 1).Select(i => $"{prefix}{i}"));

    private static string Arguments(int count) => string.Join(", ", Enumerable.Range(1, count));

    // ── Shapes ──────────────────────────────────────────────────────────────

    private const string Library = "Lib = {\npublic X = 1\npublic Y = 2\n}\n";

    /// <summary>The narrow chain <c>P1 = own(1)</c>, <c>P(i) = P(i-1) + own(i)</c> (<c>own(i)</c> is <c>p(i)</c> by default).</summary>
    private static string NarrowChain(int members, Func<int, string>? own = null)
    {
        own ??= i => $"p{i}";
        var source = new StringBuilder($"P1 = {own(1)}\n");
        for (var i = 2; i <= members; i++)
            source.Append($"P{i} = P{i - 1} + {own(i)}\n");
        return source.ToString();
    }

    /// <summary>
    /// The source report's <c>narrow-readers</c>: <c>F(p1, …, pK)</c> with the narrow chain and a path-bearing reader
    /// <c>R(i) = P(i) + Lib.X</c> of every member; <paramref name="width"/> &gt; 0 cycles that many parameters instead.
    /// </summary>
    internal static string NarrowPathReaders(int members, int width = 0)
    {
        var parameters = width == 0 ? members : width;
        var chain = NarrowChain(members, i => $"p{(width == 0 ? i : 1 + (i - 1) % width)}");
        return $"F({Names("p", 1, parameters)}) = {{\n{Library}{chain}"
            + string.Concat(Enumerable.Range(1, members).Select(i => $"R{i} = P{i} + Lib.X\n"))
            + $"R{members}\n}}\nF({Arguments(parameters)})\n";
    }

    /// <summary>Readers of two adjacent members, <c>R(i) = P(i) + P(i-1) + Lib.X</c> (full expansions holding both).</summary>
    private static string AdjacentReaders(int members)
        => $"F({Names("p", 1, members)}) = {{\n{Library}{NarrowChain(members)}R1 = P1 + Lib.X\n"
            + string.Concat(Enumerable.Range(2, members - 1).Select(i => $"R{i} = P{i} + P{i - 1} + Lib.X\n"))
            + $"R{members}\n}}\nF({Arguments(members)})\n";

    /// <summary>One path-bearing reader of the last member, or (<paramref name="reader"/> false) the output reading it by name.</summary>
    private static string SingleReader(int members, bool reader)
        => $"F({Names("p", 1, members)}) = {{\n{Library}{NarrowChain(members)}"
            + (reader ? $"R = P{members} + Lib.X\nR\n" : $"P{members}\n") + $"}}\nF({Arguments(members)})\n";

    /// <summary>
    /// The chain inside <c>G(q1, …, qK)</c> in <c>F(p1, …, pK)</c>, each member reading <c>F</c>'s <c>p(i)</c> and
    /// <c>G</c>'s <c>q(i)</c> (two owners), or with <paramref name="outer"/> <c>F</c>'s <c>p(i)</c> and <c>G(z)</c>'s
    /// <c>z</c>; path-bearing readers of every member.
    /// </summary>
    private static string QualifiedReaders(int members, bool outer)
    {
        var inner = outer ? "G(z)" : $"G({Names("q", 1, members)})";
        var chain = NarrowChain(members, i => outer ? $"p{i} + z" : $"p{i} + q{i}");
        return $"F({Names("p", 1, members)}) = {{\n{inner} = {{\n{Library}{chain}"
            + string.Concat(Enumerable.Range(1, members).Select(i => $"R{i} = P{i} + Lib.X\n"))
            + $"R{members}\n}}\nG({(outer ? "5" : Arguments(members))})\n}}\nF({Arguments(members)})\n";
    }

    /// <summary>Many owners: <paramref name="owners"/> algorithms, each with a 16-member narrow chain and path-bearing readers.</summary>
    private static string ManyOwners(int owners)
    {
        var source = new StringBuilder();
        for (var o = 1; o <= owners; o++)
        {
            source.Append($"G{o}({Names("p", 1, 16)}) = {{\n{Library}{NarrowChain(16)}")
                .Append(string.Concat(Enumerable.Range(1, 16).Select(i => $"R{i} = P{i} + Lib.X\n"))).Append("R16\n}\n");
        }

        for (var o = 1; o <= owners; o++)
            source.Append($"G{o}({Arguments(16)})\n");
        return source.ToString();
    }

    /// <summary>The narrow chain closed into a cycle through a member that reads a path (<c>P1 = P(K) + p1 + Lib.X</c>).</summary>
    private static string SinglePredecessorCycle(int members)
        => $"F({Names("p", 1, members)}) = {{\n{Library}"
            + NarrowChain(members).Replace("P1 = p1\n", $"P1 = P{members} + p1 + Lib.X\n") + $"Lib.X\n}}\nF({Arguments(members)})\n";

    /// <summary>A narrow chain whose first member reads a path: every share holds a seed that carries a reference.</summary>
    private static string PathBearingChain(int members)
        => $"F({Names("p", 1, members)}) = {{\n{Library}"
            + NarrowChain(members).Replace("P1 = p1\n", "P1 = p1 + Lib.X\n")
            + string.Concat(Enumerable.Range(1, members).Select(i => $"R{i} = P{i} + Lib.Y\n"))
            + $"R{members}\n}}\nF({Arguments(members)})\n";

    // ── The source report's shape ───────────────────────────────────────────

    /// <summary>
    /// <c>narrow-readers</c>: every member's path-bearing reader now holds its member (a PATH SHARE) instead of copying
    /// the member's width, so the entries the full expansions keep stay constant (the eight first readers copy their
    /// small members) where the former shares kept K² / 2; the shares fold a handful of times at geometrically growing
    /// widths, and every member and reader still requires exactly its <c>p1 … p(i)</c>.
    /// </summary>
    [Fact]
    public void NarrowPathReaders_HoldTheirMember_InsteadOfCopyingItsWidth()
    {
        var sizes = new[] { 100, 200, 400 };
        var formerEntries = new long[3];
        for (var k = 0; k < sizes.Length; k++)
        {
            var (folded, unfolded) = AssertSameAsUnfolded(NarrowPathReaders(sizes[k]));
            Assert.InRange(folded.SummaryMemberExpansionEntries, 1, 64);
            Assert.InRange(folded.SummaryMemberPathShares, sizes[k] - 16, sizes[k]);
            Assert.InRange(folded.SummaryMemberShareFolds, 1, 8);
            Assert.InRange(folded.SummaryMemberShareFoldEntries, 1, 2L * sizes[k]);
            Assert.InRange(unfolded.SummaryMemberExpansionEntries, (long)sizes[k] * sizes[k] / 4, long.MaxValue);
            formerEntries[k] = unfolded.SummaryMemberExpansionEntries;
            output.WriteLine($"K = {sizes[k]}: {folded.SummaryMemberExpansionEntries} expansion entries, {folded.SummaryMemberPathShares} path shares, "
                + $"{folded.SummaryMemberShareFolds} share folds of {folded.SummaryMemberShareFoldEntries} entries; former {formerEntries[k]} entries");
        }

        AssertQuadratic(formerEntries);

        var root = SourceProvenance.ParseValid(NarrowPathReaders(64)).Root;
        foreach (var i in new[] { 1, 8, 9, 10, 17, 35, 40, 64 })
        {
            var expected = Enumerable.Range(1, i).Select(p => $"p{p}").Order(StringComparer.Ordinal).Select(name => (name, 0)).ToArray();
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", $"P{i}"), expected);
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", $"R{i}"), expected);
        }

        Assert.Equal("821", Value(NarrowPathReaders(40)));
        Assert.Equal("101", Value(NarrowPathReaders(40, width: 4)));
    }

    /// <summary>
    /// Members reading the parameters of two owners (<c>F</c>'s <c>p(i)</c> and <c>G</c>'s own <c>q(i)</c>), or an
    /// ancestor's names only beside <c>G(z)</c>'s <c>z</c>: a folded share keeps each owner-qualified parameter with its
    /// owner and each ancestor-owned name required, so every reader requires its prefix of both at the right depths, and
    /// the entries the expansions keep grow linearly where the former shares' grew quadratically.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void QualifiedAndOuterReaders_KeepEveryRequirementWithItsOwner(bool outer)
    {
        var sizes = new[] { 100, 200, 400 };
        var entries = new long[3];
        var formerEntries = new long[3];
        for (var k = 0; k < sizes.Length; k++)
        {
            var (folded, unfolded) = AssertSameAsUnfolded(QualifiedReaders(sizes[k], outer));
            Assert.InRange(folded.SummaryMemberShareFolds, 1, 8);
            entries[k] = folded.SummaryMemberExpansionEntries;
            formerEntries[k] = unfolded.SummaryMemberExpansionEntries;
        }

        Assert.InRange(entries[2], 1, 2L * sizes[2]);
        AssertQuadratic(formerEntries);

        const int Members = 48;
        var root = SourceProvenance.ParseValid(QualifiedReaders(Members, outer)).Root;
        foreach (var i in new[] { 1, 5, 16, 17, 30, 48 })
        {
            var ancestor = Enumerable.Range(1, i).Select(p => $"p{p}");
            var own = outer ? ["z"] : Enumerable.Range(1, i).Select(q => $"q{q}");
            var expected = ancestor.Select(name => (name, 1)).Concat(own.Select(name => (name, 0)))
                .OrderBy(requirement => requirement.name, StringComparer.Ordinal).ToArray();
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", "G", $"R{i}"), expected);
        }

        Assert.Equal(outer ? "1417" : "2353", Value(QualifiedReaders(Members, outer)));
    }

    // ── Readers of two members: a copied sibling is counted once ───────────

    /// <summary>
    /// A reader of two adjacent members holds both. Seven times in eight the later member COPIED the earlier one (a share
    /// copies a small member's own entries and holds its parts), so the earlier member's whole subtree is inside the
    /// later one's: the reader's work estimate counts it once and the reader holds, where counting it twice made most
    /// readers fold their member's width.
    /// </summary>
    [Fact]
    public void ReadersOfTwoAdjacentMembers_HoldBoth()
    {
        var sizes = new[] { 125, 250, 500 };
        var formerEntries = new long[3];
        for (var k = 0; k < sizes.Length; k++)
        {
            var (folded, unfolded) = AssertSameAsUnfolded(AdjacentReaders(sizes[k]));
            Assert.InRange(folded.SummaryMemberExpansionEntries, 1, 16L * sizes[k]);
            formerEntries[k] = unfolded.SummaryMemberExpansionEntries;
            output.WriteLine($"K = {sizes[k]}: {folded.SummaryMemberExpansionEntries} expansion entries; former {formerEntries[k]}");
        }

        AssertQuadratic(formerEntries);
        Assert.Equal("1601", Value(AdjacentReaders(40)));
    }

    /// <summary>
    /// The fold-work estimate of a seed holding two parts, directly: chains <c>X0</c> (40 flat entries) … <c>X6</c>, each
    /// link holding the previous one beside eight entries of its own. <c>A</c> holds <c>X6</c> beside eight entries and
    /// <c>B</c> holds <c>X6</c> beside seven (A copied B). A reader holding A and B visits A's subtree, then B's own entries
    /// and its one edge: well within four times the width, in either order. A sibling over ANOTHER chain shares no subtree,
    /// and the reader's estimate (two subtrees) exceeds four times the width: it must fold.
    /// </summary>
    [Fact]
    public void TheWorkOfTwoParts_CountsASiblingTheOtherCopied_Once()
    {
        static SummarySeed Chain(string prefix, int links = 6)
        {
            var link = new SummarySeed(Enumerable.Range(1, 40).Select(i => $"{prefix}0_{i}"));
            for (var n = 1; n <= links; n++)
            {
                var next = new SummarySeed(Enumerable.Range(1, 8).Select(i => $"{prefix}{n}_{i}"));
                next.AbsorbReference(link);
                link = next;
            }

            return link;
        }

        static SummarySeed Holder(string prefix, int own, SummarySeed part)
        {
            var seed = new SummarySeed(Enumerable.Range(1, own).Select(i => $"{prefix}{i}"));
            seed.AbsorbReference(part);
            return seed;
        }

        var x6 = Chain("x");
        var a = Holder("a", 8, x6);
        var b = Holder("a", 7, x6);
        var other = Holder("b", 7, Chain("y"));
        var held = new HeldMemberSeeds(observations: null, CancellationToken.None);
        foreach (var seed in new[] { a, b, other })
            Assert.True(held.MayHold(seed));

        var reader = new SummarySeed(["r"]);
        Assert.False(held.MustFold(reader, [a, b]));
        Assert.False(held.MustFold(reader, [b, a]));
        Assert.True(held.MustFold(reader, [a, other]));
        Assert.True(held.MustFold(reader, [other, a]));

        // Over a 12-link chain A's subtree alone is 157 visits of the 160 four widths allow: the shared subtree still
        // counts once, so B's own entries and edge tip the reader into folding (reducing both siblings would not).
        var x12 = Chain("z", links: 12);
        var longA = Holder("a", 8, x12);
        var longB = Holder("a", 7, x12);
        Assert.True(held.MayHold(longA) && held.MayHold(longB));
        Assert.True(held.MustFold(reader, [longA, longB]));
        Assert.True(held.MustFold(reader, [longB, longA]));

        // These distinct siblings share nine direct parts. A share could never have copied that
        // many edges. Their cost stays conservative without scanning the shared list per reader.
        var wideA = new SummarySeed();
        var wideB = new SummarySeed();
        for (var i = 0; i <= SummarySeed.CopiedCompletedEntries; i++)
        {
            var child = new SummarySeed(Enumerable.Range(0, i == 0 ? 50 : 12).Select(j => $"p{i}_{j}"));
            wideA.AbsorbReference(child);
            wideB.AbsorbReference(child);
        }
        Assert.True(held.MayHold(wideA) && held.MayHold(wideB));
        Assert.True(held.MustFold(reader, [wideA, wideB]));
        Assert.True(held.MustFold(reader, [wideB, wideA]));
        Assert.False(held.MustFold(new SummarySeed(), [longA]));
    }

    // ── Controls ────────────────────────────────────────────────────────────

    /// <summary>
    /// A SINGLE reader, and a chain nobody but the output reads: the shares fold only at geometrically growing widths
    /// (linear total entries, including widths just after a fold), and the single reader holds its member where it used to copy K entries. The member
    /// seeds the summaries retain store at most the former entries plus what those folds materialized, and with the
    /// reader at least K fewer than that (the reader's copy of its member is gone).
    /// </summary>
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void ASingleReaderAndAnUnreadChain_FoldOnlyAtGeometricWidths(bool reader)
    {
        foreach (var members in new[] { 200, 400, 500, 800 })
        {
            var source = SingleReader(members, reader);
            var (folded, unfolded) = AssertSameAsUnfolded(source);
            Assert.InRange(folded.SummaryMemberShareFolds, 1, 4);
            Assert.InRange(folded.SummaryMemberShareFoldEntries, 1, 2L * members);
            Assert.InRange(folded.SummaryMemberExpansions, 0, unfolded.SummaryMemberExpansions);
            Assert.InRange(folded.SummaryMemberExpansionEntries, 0, reader ? 1 : unfolded.SummaryMemberExpansionEntries);

            var root = SourceProvenance.ParseValid(source).Root;
            long Stored(bool former)
            {
                var memo = StandaloneSummaries.MemoFor(root);
                if (former) Unfolded(() => StandaloneSummaries.Build(root, memo));
                else StandaloneSummaries.Build(root, memo);
                var summaries = (memo.IndependentAlgorithmSummaries?.Values ?? Enumerable.Empty<AlgorithmSummary>())
                    .Concat(memo.ContextualAlgorithmSummaries?.Values ?? Enumerable.Empty<AlgorithmSummary>());
                var memberSeeds = Assert.Single(summaries.Distinct(), summary => summary.MemberSeeds.ContainsKey("P1")).MemberSeeds;
                return memberSeeds.Values.SelectMany(Reachable).Distinct(ReferenceEqualityComparer.Instance).Cast<SummarySeed>()
                    .Sum(seed => (long)seed.OwnEntryCount);
            }

            // The former reader kept its member's whole width (K entries and its reference) in its own sets; it now holds it.
            var stored = Stored(former: false);
            var formerStored = Stored(former: true);
            Assert.InRange(stored, reader ? 1 : formerStored, formerStored + folded.SummaryMemberShareFoldEntries - (reader ? members : 0));
            output.WriteLine($"K = {members}: {folded.SummaryMemberShareFolds} share folds of {folded.SummaryMemberShareFoldEntries} entries, "
                + $"{folded.SummaryMemberExpansionEntries} expansion entries (former {unfolded.SummaryMemberExpansionEntries}); stored {stored} (former {formerStored})");
        }
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

    /// <summary>
    /// THE CHAIN'S BUDGET: after the solve, every member of a narrow chain holds a chain of parts no deeper than the
    /// widest own set along it, so no reader's fold of it walks more parts than its width. The former shares grew one
    /// level per eight members, far deeper than any own set (the budget long spent).
    /// </summary>
    [Fact]
    public void EveryChainMember_HoldsNoDeeperChainThanItsWidestOwnSet()
    {
        const int Members = 400;
        var root = SourceProvenance.ParseValid(SingleReader(Members, reader: false)).Root;
        (int Deepest, int Violations) Depths(bool former)
        {
            var memo = StandaloneSummaries.MemoFor(root);
            if (former) Unfolded(() => StandaloneSummaries.Build(root, memo));
            else StandaloneSummaries.Build(root, memo);
            var summaries = (memo.IndependentAlgorithmSummaries?.Values ?? Enumerable.Empty<AlgorithmSummary>())
                .Concat(memo.ContextualAlgorithmSummaries?.Values ?? Enumerable.Empty<AlgorithmSummary>());
            var members = Assert.Single(summaries.Distinct(), summary => summary.MemberSeeds.ContainsKey("P1")).MemberSeeds;
            var deepest = 0;
            var violations = 0;
            foreach (var seed in members.Values)
            {
                var reachable = Reachable(seed);
                deepest = Math.Max(deepest, reachable.Count - 1);
                if (reachable.Count - 1 > reachable.Max(part => part.OwnEntryCount))
                    violations++;
            }

            return (deepest, violations);
        }

        var (deepest, violations) = Depths(former: false);
        var (formerDeepest, formerViolations) = Depths(former: true);
        output.WriteLine($"deepest held chain {deepest} (former {formerDeepest}); members deeper than their widest own set {violations} (former {formerViolations})");
        Assert.Equal(0, violations);
        Assert.InRange(formerViolations, Members / 2, Members);
        Assert.InRange(formerDeepest, Members / 10, Members);
    }

    /// <summary>
    /// A bounded-width chain (16 parameters cycled): its shares fold every few links at its bounded width, which costs
    /// fewer entries than the members, and its readers hold their members. MANY OWNERS, each with a 16-member chain: no
    /// share's budget is spent, and every counter is the former one.
    /// </summary>
    [Fact]
    public void BoundedWidthAndManyOwnerControls()
    {
        var sizes = new[] { 100, 200, 400 };
        var folds = new long[3];
        for (var k = 0; k < sizes.Length; k++)
        {
            var (folded, unfolded) = AssertSameAsUnfolded(NarrowPathReaders(sizes[k], width: 16));
            Assert.InRange(folded.SummaryMemberExpansionEntries, 1, 64);
            Assert.InRange(folded.SummaryMemberShareFoldEntries, 1, sizes[k]);
            Assert.InRange(unfolded.SummaryMemberExpansionEntries, folded.SummaryMemberExpansionEntries, long.MaxValue);
            folds[k] = folded.SummaryMemberShareFolds;
        }

        AssertLinear(folds);

        var owners = ManyOwners(24);
        var production = Parse(owners);
        var former = Unfolded(() => Parse(owners));
        Assert.Equal("", production.Diagnostics);
        Assert.Equal(former.Metadata, production.Metadata);
        Assert.Equal(0, production.Observations.SummaryMemberShareFolds);
        Assert.Equal(Counters(former.Observations), Counters(production.Observations));
    }

    /// <summary>
    /// CONVERGENCE AND PATHS: the shares of a cycle's members are compared again on every evaluation and keep the former
    /// representation, and shares that hold a seed carrying a pending reference are PATH PARTS' to settle: neither folds,
    /// and every counter is the former one.
    /// </summary>
    [Theory]
    [InlineData("cycle", 64)]
    [InlineData("cycle", 160)]
    [InlineData("path", 200)]
    public void CycleMembersAndPathBearingChains_KeepTheirShares(string shape, int members)
    {
        var source = shape == "cycle" ? SinglePredecessorCycle(members) : PathBearingChain(members);
        var production = Parse(source);
        var former = Unfolded(() => Parse(source));
        Assert.Equal("", production.Diagnostics);
        Assert.Equal(former.Metadata, production.Metadata);
        Assert.Equal(0, production.Observations.SummaryMemberShareFolds);
        Assert.Equal(Counters(former.Observations), Counters(production.Observations));
    }

    /// <summary>
    /// A share's own requirements are qualified with <c>HashSet.Remove</c>, which can leave its name set empty; the share
    /// then copies a small member into it, or folds what it holds into it. On the .NET 11.0.0 runtime
    /// <c>HashSet.UnionWith</c> into a set that <c>Remove</c> emptied can throw (it keeps a stale free list), and this
    /// generated level (reduced from corpus program 23,078) made <c>Parser.Parse</c> throw
    /// <see cref="IndexOutOfRangeException"/> before November 27 2026. The share now releases an emptied set, so the level
    /// parses, with the same metadata whether its shares fold, its expansions copy, or neither.
    /// </summary>
    [Fact]
    public void AShareNeverUnitesIntoANameSetItsQualificationEmptied()
    {
        const string Source = """
            F(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14) = {
              G(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12) = {
                Lib = {
                }
                M1 = M4 + M4 + M22 + p4
                M2 = M1 + p1 + M1
                M3 = p13 + p5
                M4 = M3 + p5 + M3 + M2
                M5 = M1 + M4 + M3
                M6 = M28 + M5 + p12 + M4
                M7 = p1 + p10 + p9 + 3
                M8 = M6 + p8 + p9
                M9 = 4 + M7
                M12 = 9 + 3 + M6 + p6
                M13 = p10 + M12 + p7
                M14 = M13 + M13 + p10
                M15 = p14 + p8 + M8 + p4
                M17 = 2 + M15
                M20 = p2 + M23 + M20
                M22 = M14 + M22 + p2 + p10
                M23 = p12 + M22
                M24 = M17 + M9
                M25 = p11 + M24
                M26 = M24 + 1
                M28 = M26 + p10
                M12 + M25 + M8
              }
              G(8, 6, 7, 2, 1, 5, 7, 3, 2, 5, 2, 8)
            }
            """;
        var root = SourceProvenance.ParseValid(Source).Root;
        var metadata = ExposureSettlementFrameChargeTests.Metadata(root);
        Assert.Equal(metadata, Unfolded(() => Parse(Source).Metadata));
        var previous = MemberSeedsCopiedForTesting.Value;
        MemberSeedsCopiedForTesting.Value = true;
        try { Assert.Equal(metadata, Parse(Source).Metadata); }
        finally { MemberSeedsCopiedForTesting.Value = previous; }

        ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", "G", "M23"),
            ("p1", 0), ("p10", 0), ("p12", 0), ("p13", 1), ("p14", 1), ("p2", 0), ("p4", 0), ("p5", 0), ("p6", 0), ("p7", 0),
            ("p8", 0), ("p9", 0));
    }

    // ── Cancellation and the ledger ─────────────────────────────────────────

    /// <summary>
    /// CANCELLATION: the budget walk of a share observes the token before it folds anything, so a cancelled share escapes
    /// with the token and keeps the parts it held; a parse cancelled after its first share fold escapes with the token,
    /// folds nothing more, and a fresh parse publishes the uncancelled metadata.
    /// </summary>
    [Fact]
    public void CancellationAroundAShareFold_EscapesWithTheToken_AndLeavesNothingBehind()
    {
        using (var cancelled = new CancellationTokenSource())
        {
            cancelled.Cancel();
            var predecessor = new SummarySeed(Enumerable.Range(1, 12).Select(i => $"p{i}"));
            var middle = new SummarySeed(["q"]);
            middle.AbsorbReference(predecessor);
            var share = new SummarySeed(["r"]);
            share.AbsorbReference(middle);
            var parts = share.AbsorbedPartsWithoutFolding;
            var error = Assert.Throws<OperationCanceledException>(
                () => new HeldMemberSeeds(observations: null, cancelled.Token).FoldShareWhenSpent(share));
            Assert.Equal(cancelled.Token, error.CancellationToken);
            Assert.Same(parts, share.AbsorbedPartsWithoutFolding);
            Assert.Equal(new[] { "r" }, share.OwnRequiredNamesWithoutFolding!);
        }

        var source = NarrowPathReaders(400);
        var uncancelled = Parse(source);
        long firstFold = -1;
        FrontEndTraversalObservations probe = null!;
        probe = new FrontEndTraversalObservations
        {
            CheckpointReached = (kind, ordinal) =>
            {
                if (kind == FrontEndCancellationCheckpoint.SummaryChannel && firstFold < 0 && probe.SummaryMemberShareFolds > 0)
                    firstFold = ordinal;
            },
        };
        Parser.ParseObserved(source, options: null, probe);
        Assert.InRange(firstFold, 1, long.MaxValue);

        using var cancellation = new CancellationTokenSource();
        long foldsAtCancel = -1;
        FrontEndTraversalObservations observations = null!;
        observations = new FrontEndTraversalObservations
        {
            CheckpointReached = (kind, ordinal) =>
            {
                if (kind != FrontEndCancellationCheckpoint.SummaryChannel || ordinal != firstFold || cancellation.IsCancellationRequested)
                    return;
                foldsAtCancel = observations.SummaryMemberShareFolds;
                cancellation.Cancel();
            },
        };

        var escaped = Assert.Throws<OperationCanceledException>(() => Parser.ParseObserved(
            source, new RunOptions { SourceProcessingCancellationToken = cancellation.Token }, observations));
        Assert.Equal(cancellation.Token, escaped.CancellationToken);
        Assert.Equal(firstFold, observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel));
        Assert.InRange(foldsAtCancel, 1, long.MaxValue);
        Assert.Equal(foldsAtCancel, observations.SummaryMemberShareFolds);
        Assert.Equal(uncancelled.Metadata, Parse(source).Metadata);
    }

    /// <summary>
    /// THE LEDGER: output rows navigating a narrow library chain qualify each part of the members they read at the owner
    /// that binds its names (QUALIFIED SEED PARTS). A folded share is one wider part, whose entries the qualification
    /// charges again, so the static work rises by a few units per folded entry; the frames are the former ones. Each
    /// representation is admitted at its own exact charge and refused one unit below it.
    /// </summary>
    [Fact]
    public void NavigatedLibraryRows_ChargeTheFoldedEntries_AtTheExactBoundary()
    {
        var source = ExposureResidualReuseTests.OwnerQualifiedRows(200);
        long Run(long? limit)
        {
            var (resolved, ledger, _) = ExposureSettlementFrameChargeTests.Resolved(source,
                limits => limit.HasValue ? limits with { MaxEvaluations = limit.Value } : limits);
            _ = PropertyExposureResolver.Resolve(resolved);
            return ledger.WorkCharged;
        }

        var exact = Run(null);
        var former = Unfolded(() => Run(null));
        Assert.Equal(exact, Run(exact));
        Assert.Throws<StaticQueryLimitExceededException>(() => Run(exact - 1));
        Assert.Equal(former, Unfolded(() => Run(former)));
        Assert.Throws<StaticQueryLimitExceededException>(() => Unfolded(() => Run(former - 1)));

        var production = Parse(source);
        var unfolded = Unfolded(() => Parse(source));
        Assert.Equal(unfolded.Metadata, production.Metadata);
        Assert.Equal(unfolded.Observations.RequiredAncestorSettlementFrames, production.Observations.RequiredAncestorSettlementFrames);
        var foldedEntries = production.Observations.SummaryMemberShareFoldEntries;
        Assert.InRange(foldedEntries, 1, 200);
        Assert.InRange(exact - former, 1, 4 * foldedEntries);
        output.WriteLine($"work {exact} (former {former}); {production.Observations.SummaryMemberShareFolds} share folds of {foldedEntries} entries");
    }

    // ── Generated levels ────────────────────────────────────────────────────

    /// <summary>
    /// ORDER, REQUIREMENTS AND OWNERS over generated levels built around narrow chains — members adding parameters of their
    /// owner or of an enclosing owner with the same names, sometimes a second sibling, a path or a shadowed local
    /// declaration; readers by path, by name, of two members or inside a block; cycles; output rows; nested owners and
    /// detached readers navigating the members from outside: every summary the member solve computes is the former one in
    /// content and reference order, and each program's metadata and diagnostics are the former ones.
    /// </summary>
    [Fact]
    public void GeneratedNarrowLevels_FoldedSharesKeepEverySummary()
    {
        var compared = 0;
        var foldingPrograms = 0;
        foreach (var source in GeneratedLevels(240, seed: 27))
        {
            var production = Parse(source);
            var former = Unfolded(() => Parse(source));
            Assert.Equal(former.Diagnostics, production.Diagnostics);
            Assert.Equal(former.Metadata, production.Metadata);
            if (production.Diagnostics.Length != 0)
                continue;
            if (production.Observations.SummaryMemberShareFolds > 0)
                foldingPrograms++;

            var root = SourceProvenance.ParseValid(source).Root;
            var context = AnalyzedStaticStructures.ForBoundAst(root);
            var foldedMemo = StandaloneSummaries.MemoFor(root);
            var formerMemo = StandaloneSummaries.MemoFor(root);
            PropertyDependencyGraphBuilder.BuildSummaries(root, context, foldedMemo);
            Unfolded(() => PropertyDependencyGraphBuilder.BuildSummaries(root, context, formerMemo));
            compared += CompareSummaries(foldedMemo, formerMemo, source);
        }

        output.WriteLine($"{compared} summaries compared; {foldingPrograms} programs folded shares");
        Assert.InRange(foldingPrograms, 60, int.MaxValue);
    }

    private static int CompareSummaries(SummaryMemo folded, SummaryMemo former, string source)
    {
        var compared = 0;
        foreach (var (algorithm, summary) in former.IndependentAlgorithmSummaries ?? [])
        {
            Assert.True(folded.IndependentAlgorithmSummaries!.TryGetValue(algorithm, out var other), source);
            Assert.Null(SummaryMemo.AdoptedSummaryDifference(other, summary));
            compared++;
        }

        foreach (var (key, summary) in former.ContextualAlgorithmSummaries ?? [])
        {
            Assert.True(folded.ContextualAlgorithmSummaries!.TryGetValue(key, out var other), source);
            Assert.Null(SummaryMemo.AdoptedSummaryDifference(other, summary));
            compared++;
        }

        Assert.Equal(former.IndependentAlgorithmSummaries?.Count ?? 0, folded.IndependentAlgorithmSummaries?.Count ?? 0);
        Assert.Equal(former.ContextualAlgorithmSummaries?.Count ?? 0, folded.ContextualAlgorithmSummaries?.Count ?? 0);
        return compared;
    }

    /// <summary>Seeded random levels around narrow chains (see <see cref="GeneratedNarrowLevels_FoldedSharesKeepEverySummary"/>).</summary>
    private static IEnumerable<string> GeneratedLevels(int count, int seed)
    {
        var random = new Random(seed);
        for (var n = 0; n < count; n++)
        {
            var parameters = Enumerable.Range(1, 6 + random.Next(30)).Select(i => $"p{i}").ToArray();
            var members = 30 + random.Next(70);
            var second = random.Next(3) == 0 ? 0.06 : 0.0;
            var paths = random.Next(4) == 0 ? 0.04 : 0.0;
            var shadows = random.Next(5) == 0 ? 0.05 : 0.0;
            var cycle = random.Next(8) == 0;
            var nested = random.Next(3) == 0;
            var detached = nested && random.Next(2) == 0;
            var readers = random.Next(5);
            string Pick(params string[] items) => items[random.Next(items.Length)];

            var lines = new List<string> { "Lib = {", $"public X = {Pick(parameters)} + 1", "public Y = 2", "}" };
            for (var i = 1; i <= members; i++)
            {
                var atoms = new List<string>();
                if (i > 1)
                    atoms.Add($"M{i - 1}");
                else if (cycle)
                    atoms.Add($"M{members}");
                atoms.Add(Pick(parameters));
                if (random.NextDouble() < 0.3)
                    atoms.Add(Pick(parameters));
                if (i > 2 && random.NextDouble() < second)
                    atoms.Add($"M{1 + random.Next(i - 2)}");
                if (random.NextDouble() < paths)
                    atoms.Add(Pick("Lib.X", "Lib.Y"));
                var visibility = detached && random.Next(3) == 0 ? "public " : "";
                if (i > 2 && random.NextDouble() < shadows)
                {
                    var local = $"M{i - 1 - random.Next(i - 1)}";
                    lines.AddRange([$"{visibility}M{i} = {{", $"{local} = {random.Next(9) + 1}", string.Join(" + ", [.. atoms, local]), "}"]);
                }
                else
                    lines.Add($"{visibility}M{i} = {string.Join(" + ", atoms)}");
            }

            var rows = new List<string>();
            for (var i = 1; i <= members; i++)
            {
                switch (readers)
                {
                    case 0:
                        lines.Add($"R{i} = M{i} + Lib.X");
                        break;
                    case 1:
                        lines.Add($"R{i} = M{i} + {i}");
                        break;
                    case 2:
                        lines.Add(i > 1 ? $"R{i} = M{i} + M{i - 1} + Lib.Y" : "R1 = M1 + Lib.Y");
                        break;
                    case 3:
                        if (random.Next(4) == 0)
                            rows.Add($"M{i}");
                        continue;
                    default:
                        lines.Add($"R{i} = M{i} + M{1 + random.Next(i)} + Lib.X");
                        break;
                }

                if (random.Next(6) == 0)
                    rows.Add($"R{i}");
            }

            lines.Add(rows.Count == 0 ? $"M{members}" : string.Join("\n", rows));
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
