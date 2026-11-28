using System.Text;
using Xunit.Abstractions;
using static KatLang.PropertyDependencyGraphBuilder;

namespace KatLang.Tests;

/// <summary>
/// MIXED-CYCLE COMPLETE SEEDS (November 28 2026; C# exposure implementation only — no classification, requirement,
/// diagnostic kind, value or Lean rule changes). The members of a mixed cycle — a strongly connected component of a
/// level's members that is solved member by member — kept the folded seed of a full expansion: over the closed chain
/// (<c>P1 = PK + p1 + Lib.X</c>, <c>P(i) = P(i-1) + P(i-2) + p(i)</c>) the two passes copied about 1.5 K² entries. Where
/// the copied expansion (or the share its change test folds) would be a flat seed equal in content and reference order
/// to a flat seed it reads that holds the component's whole BOUND, the member now takes a new seed over that seed's own
/// sets; a member with the share shape holds its reference-free predecessors as outside a cycle; and the change test
/// tells a seed carrying a reference from a reference-free held one without folding. Oracle: the copied seeds
/// (<see cref="PropertyDependencyGraphBuilder.MixedCycleSeedsCopiedForTesting"/>), compared by every member's content with
/// its references IN ORDER, published metadata, diagnostics, the checkpoint sequence, static work, settlement frames and
/// deterministic counters, never time.
/// </summary>
public sealed class MixedCycleCompleteSeedTests(ITestOutputHelper output)
{
    // ── Harness ─────────────────────────────────────────────────────────────

    private static T Copied<T>(Func<T> work)
    {
        var previous = MixedCycleSeedsCopiedForTesting.Value;
        MixedCycleSeedsCopiedForTesting.Value = true;
        try { return work(); }
        finally { MixedCycleSeedsCopiedForTesting.Value = previous; }
    }

    private sealed record Observed(string Diagnostics, string Metadata, FrontEndTraversalObservations Observations, ulong Sequence);

    /// <summary>A parse with its ordered diagnostics, published metadata, counters and the sequence of every checkpoint kind.</summary>
    private static Observed Parse(string source)
    {
        var sequence = 14695981039346656037UL;
        var observations = new FrontEndTraversalObservations
        {
            CheckpointReached = (kind, _) => sequence = (sequence ^ ((ulong)kind + 1)) * 1099511628211UL,
        };
        var parsed = Parser.ParseObserved(source, options: null, observations);
        var diagnostics = string.Join("\n", parsed.Diagnostics.Select(d => $"{d.Code}/{d.Severity}@{d.Span}: {d.Message}"));
        return new(diagnostics, ExposureSettlementFrameChargeTests.Metadata(parsed.Root), observations, sequence);
    }

    /// <summary>The static work the exposure pass charges the operation's ledger.</summary>
    private static long Work(string source)
    {
        var (resolved, ledger, _) = ExposureSettlementFrameChargeTests.Resolved(source);
        var before = ledger.WorkCharged;
        _ = PropertyExposureResolver.Resolve(resolved);
        return ledger.WorkCharged - before;
    }

    /// <summary>The summary memo of a standalone summary build of <paramref name="root"/>.</summary>
    private static SummaryMemo Memo(Algorithm root)
    {
        var memo = StandaloneSummaries.MemoFor(root);
        BuildSummaries(root, AnalyzedStaticStructures.ForBoundAst(root), memo);
        return memo;
    }

    private static IEnumerable<AlgorithmSummary> AllSummaries(SummaryMemo memo)
        => (memo.IndependentAlgorithmSummaries?.Values ?? Enumerable.Empty<AlgorithmSummary>())
            .Concat(memo.ContextualAlgorithmSummaries?.Values ?? Enumerable.Empty<AlgorithmSummary>());

    /// <summary>Every summary of <paramref name="source"/> under production and under the copied seeds, paired.</summary>
    private static List<(string Where, SummarySeed Complete, SummarySeed Copied)> Summaries(string source)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var complete = Memo(root);
        var copied = Copied(() => Memo(root));
        var pairs = new List<(string, SummarySeed, SummarySeed)>();
        void Add(string where, AlgorithmSummary left, AlgorithmSummary right)
        {
            pairs.Add((where + " output", left.OutputSeed, right.OutputSeed));
            Assert.Equal(right.MemberSeeds.Count, left.MemberSeeds.Count);
            foreach (var (name, seed) in right.MemberSeeds)
                pairs.Add((where + " member " + name, left.MemberSeeds[name], seed));
        }

        Assert.Equal(copied.IndependentAlgorithmSummaries?.Count ?? 0, complete.IndependentAlgorithmSummaries?.Count ?? 0);
        Assert.Equal(copied.ContextualAlgorithmSummaries?.Count ?? 0, complete.ContextualAlgorithmSummaries?.Count ?? 0);
        foreach (var (algorithm, summary) in copied.IndependentAlgorithmSummaries ?? [])
            Add("independent", complete.IndependentAlgorithmSummaries![algorithm], summary);
        foreach (var (key, summary) in copied.ContextualAlgorithmSummaries ?? [])
            Add("contextual", complete.ContextualAlgorithmSummaries![key], summary);
        return pairs;
    }

    /// <summary>
    /// Two seeds hold the same content — the same required names, visible names and owner-qualified parameters, and the
    /// same references, each with its origin, path, bound owners and selection, in the SAME order — and the same shape:
    /// flat, or holding as many parts.
    /// </summary>
    private static void AssertSameContentOrderAndShape(SummarySeed complete, SummarySeed copied, string where)
    {
        Assert.True((copied.AbsorbedPartsWithoutFolding?.Count ?? 0) == (complete.AbsorbedPartsWithoutFolding?.Count ?? 0), where);
        complete = complete.Clone();
        copied = copied.Clone();
        Assert.True(copied.RequiredAncestorOwnedParameterNames.SetEquals(complete.RequiredAncestorOwnedParameterNames), where);
        Assert.True(copied.VisiblePropertyDependencyNames.SetEquals(complete.VisiblePropertyDependencyNames), where);
        Assert.True(copied.OwnerQualifiedParameters.SetEquals(complete.OwnerQualifiedParameters), where);
        static (string, object?, object?, bool, PendingSelection?) Identity(SummaryReference reference)
            => reference is PendingReference anchored
                ? (anchored.ContentKey, anchored.Origin.Facts, anchored.Origin.Key, anchored.OpenPath, anchored.Selection)
                : (reference.ContentKey, null, null, false, null);
        Assert.True(copied.PendingReferences.Select(Identity).SequenceEqual(complete.PendingReferences.Select(Identity)), where);
    }

    /// <summary>The member seeds of the summary that declares <paramref name="member"/>.</summary>
    private static IReadOnlyDictionary<string, SummarySeed> MembersDeclaring(SummaryMemo memo, string member)
        => Assert.Single(AllSummaries(memo), summary => summary.MemberSeeds.ContainsKey(member)).MemberSeeds;

    /// <summary>
    /// What the member seeds retain: the distinct seeds they are and hold by reference, and the entries of the distinct own
    /// SETS of those seeds (a seed over another seed's own sets, <see cref="SummarySeed.WithSharedOwnSets"/>, adds none).
    /// </summary>
    private static (int Seeds, long Entries) Retained(IEnumerable<SummarySeed> members)
    {
        var seen = new HashSet<SummarySeed>(ReferenceEqualityComparer.Instance);
        var sets = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<SummarySeed>(members);
        long entries = 0;
        while (pending.TryPop(out var seed))
        {
            if (!seen.Add(seed))
                continue;
            foreach (var (set, count) in seed.OwnSetObjects())
            {
                if (sets.Add(set))
                    entries += count;
            }

            foreach (var part in seed.AbsorbedPartsWithoutFolding ?? [])
                pending.Push(part);
        }

        return (seen.Count, entries);
    }

    /// <summary>Whether two flat seeds are written over the same own sets.</summary>
    private static bool SameSets(SummarySeed left, SummarySeed right)
        => left.AbsorbedPartsWithoutFolding is null && right.AbsorbedPartsWithoutFolding is null && left.SharesOwnSetsWith(right);

    /// <summary>A seed's references in order, written <c>head.member…</c>.</summary>
    private static IEnumerable<string> Paths(SummarySeed seed)
        => seed.Clone().PendingReferences.Select(reference => string.Join(".", [reference.Head, .. reference.Members]));

    private static string Names(string prefix, int from, int to)
        => string.Join(", ", Enumerable.Range(from, to - from + 1).Select(i => $"{prefix}{i}"));

    private static string Arguments(int count) => string.Join(", ", Enumerable.Range(1, count));

    // ── Shapes ──────────────────────────────────────────────────────────────

    /// <summary>
    /// <c>F(p1, …, pK)</c> declaring <c>Lib</c> and the members <c>P(i) = member(i)</c> (in reversed source order with
    /// <paramref name="reversed"/>), then <paramref name="extra"/> and the output row.
    /// </summary>
    private static string Level(int members, Func<int, string> member, string row = "Lib.X", bool reversed = false, string extra = "")
    {
        var source = new StringBuilder($"F({Names("p", 1, members)}) = {{\nLib = {{\npublic X = 1\npublic Y = 2\npublic Z = 3\n}}\n");
        var order = Enumerable.Range(1, members);
        foreach (var i in reversed ? order.Reverse() : order)
            source.Append($"P{i} = {member(i)}\n");
        source.Append(extra).Append(row).Append($"\n}}\nF({Arguments(members)})\n");
        return source.ToString();
    }

    private static string Chain(int i) => i == 2 ? "P1 + p2" : $"P{i - 1} + P{i - 2} + p{i}";

    private static string Closing(int k) => $"P{k} + p1 + Lib.X";

    /// <summary>The sharing-negative control of MIXED-CYCLE SCHEDULE: no member reads two predecessors.</summary>
    private static string SinglePredecessorCycle(int k, bool reversed = false)
        => Level(k, i => i == 1 ? Closing(k) : $"P{i - 1} + p{i}", reversed: reversed);

    private const int OutOfOrder = 15;

    /// <summary>
    /// <c>P(i) = P(i-2) + P(i-1) + p(i)</c> closed by <c>P1 = PK + p1 + Lib.X</c> for an even K, <c>P3</c> also reading
    /// <c>Lib.Y</c>, and the odd member <c>P(OutOfOrder)</c> also reading <c>E</c>, a member outside the cycle that reads
    /// <c>Lib.Z</c>: BEFORE its predecessors with <paramref name="before"/>, after them otherwise. <c>PK</c> reads its even
    /// predecessors first, so the closing member's seed — the first complete seed — holds its references in the order
    /// <c>Lib.Y</c>, <c>Lib.Z</c>, <c>Lib.X</c>, and an expansion that unites <c>E</c> before that seed writes <c>Lib.Z</c> first.
    /// </summary>
    private static string ExternalReadCycle(int k, bool before)
        => Level(k, i => i == 1 ? Closing(k) : i == 2 ? "P1 + p2" : i == 3 ? "P1 + P2 + p3 + Lib.Y"
                : i != OutOfOrder ? $"P{i - 2} + P{i - 1} + p{i}"
                : before ? $"E + P{i - 2} + P{i - 1} + p{i}" : $"P{i - 2} + P{i - 1} + p{i} + E",
            extra: "E = Lib.Z + 1\n");

    /// <summary>The cycle closes through a path (<c>P1</c> reads <c>B.X</c>; <c>B</c>'s row reads <c>PK</c>): <c>P1</c> never receives the chain's content.</summary>
    private static string UnequalCycle(int k)
        => Level(k, i => i == 1 ? "B.X + p1 + Lib.X" : Chain(i), extra: $"B = {{\npublic X = 1\nP{k}\n}}\n");

    private static string ShapeSource(string shape, int k) => shape switch
    {
        "branched" => Level(k, i => (i == 1 ? Closing(k) : Chain(i)) + (i % 8 == 0 && i + 4 <= k ? $" + P{i + 4}" : "")),
        "paths" => Level(k, i => (i == 1 ? Closing(k) : Chain(i)) + (i % 4 == 0 ? $" + Lib.{(char)('X' + i % 3)}" : "")),
        "paths-reversed" => Level(k, i => (i == 1 ? Closing(k) : Chain(i)) + (i % 4 == 0 ? $" + Lib.{(char)('X' + i % 3)}" : ""), reversed: true),
        "self-path" => Level(k, i => i == 1 ? Closing(k) : i == k ? Chain(i) + " + F.P1" : Chain(i)),
        "external-path" => Level(k, i => (i == 1 ? Closing(k) : Chain(i)) + (i % 5 == 0 ? " + E.V" : ""), extra: "E = { public V = 1 }\n"),
        "readers" => Level(k, i => i == 1 ? Closing(k) : Chain(i), row: $"R{k}",
            extra: string.Concat(Enumerable.Range(1, k).Select(i => $"R{i} = P{i} + Lib.Y\n"))),
        "owner" => OwnerCycle(k),
        "navigated" => NavigatedCycle(k),
        "two-cycles" => TwoCycles(k),
        _ => throw new ArgumentOutOfRangeException(nameof(shape)),
    };

    /// <summary>The members also read an enclosing owner's parameter, which their level does not bind.</summary>
    private static string OwnerCycle(int k)
    {
        var source = new StringBuilder($"G({Names("q", 1, k)}) = {{\nF({Names("p", 1, k)}) = {{\nLib = {{\npublic X = 1\n}}\n");
        for (var i = 1; i <= k; i++)
            source.Append($"P{i} = {(i == 1 ? Closing(k) : Chain(i))} + q{i}\n");
        return source.Append($"Lib.X\n}}\nF({Arguments(k)})\n}}\nG({Arguments(k)})\n").ToString();
    }

    /// <summary>The cycle inside a library member, read by navigation from readers at the owner's level.</summary>
    private static string NavigatedCycle(int k)
    {
        var source = new StringBuilder($"F({Names("p", 1, k)}) = {{\nLib = {{\npublic X = 1\npublic Y = 2\n}}\nL = {{\n");
        for (var i = 1; i <= k; i++)
            source.Append($"public P{i} = {(i == 1 ? Closing(k) : Chain(i))}\n");
        source.Append("}\n");
        for (var i = 1; i <= k; i++)
            source.Append($"R{i} = L.P{i} + Lib.Y\n");
        return source.Append($"R{k}\n}}\nF({Arguments(k)})\n").ToString();
    }

    /// <summary>Two closed chains, the second reading the first's tail.</summary>
    private static string TwoCycles(int k)
    {
        var source = new StringBuilder($"F({Names("p", 1, k)}, {Names("q", 1, k)}) = {{\nLib = {{\npublic X = 1\npublic Y = 2\n}}\n");
        source.Append($"A1 = A{k} + p1 + Lib.X\nA2 = A1 + p2\n");
        for (var i = 3; i <= k; i++) source.Append($"A{i} = A{i - 1} + A{i - 2} + p{i}\n");
        source.Append($"B1 = B{k} + A{k} + q1 + Lib.Y\nB2 = B1 + q2\n");
        for (var i = 3; i <= k; i++) source.Append($"B{i} = B{i - 1} + B{i - 2} + q{i}\n");
        return source.Append($"B{k}\n}}\nF({Arguments(2 * k)})\n").ToString();
    }

    /// <summary>
    /// Production and the copied seeds agree on the outcome, the schedule, the checkpoint sequence, the settlement frames
    /// and part work, the static work, and every summary in content, reference order and shape.
    /// </summary>
    private static (Observed Complete, Observed Copied) AssertSameOutcome(string source)
    {
        var complete = Parse(source);
        var copied = Copied(() => Parse(source));
        Assert.Equal("", complete.Diagnostics);
        Assert.Equal(copied.Diagnostics, complete.Diagnostics);
        Assert.Equal(copied.Metadata, complete.Metadata);
        Assert.Equal(copied.Sequence, complete.Sequence);
        Assert.Equal(copied.Observations.SummaryMemberEvaluations, complete.Observations.SummaryMemberEvaluations);
        Assert.Equal(copied.Observations.SummaryMemberReaderNotifications, complete.Observations.SummaryMemberReaderNotifications);
        Assert.Equal(copied.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel),
            complete.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel));
        Assert.Equal(copied.Observations.RequiredAncestorSettlementFrames, complete.Observations.RequiredAncestorSettlementFrames);
        Assert.Equal(copied.Observations.SettlementSeedPartWork, complete.Observations.SettlementSeedPartWork);
        Assert.Equal(copied.Observations.MemberNavigationFolds, complete.Observations.MemberNavigationFolds);
        Assert.Equal(copied.Observations.MemberNavigationEntriesRead, complete.Observations.MemberNavigationEntriesRead);
        Assert.Equal(Copied(() => Work(source)), Work(source));
        foreach (var (where, left, right) in Summaries(source))
            AssertSameContentOrderAndShape(left, right, where);
        return (complete, copied);
    }

    // ── The reviewed shape ──────────────────────────────────────────────────

    /// <summary>
    /// The closed chain in either source order: once the closing member holds the bound, every member evaluated after it
    /// takes a new seed over that seed's own sets, so after the solve the K members are K seeds, as before, over ONE group
    /// of sets: K + 1 entries where the copied seeds kept about K². The evaluations and notifications are MIXED-CYCLE
    /// SCHEDULE's (2K + 4 and 2K − 2), and the published metadata, checkpoint sequence, static work, frames and every
    /// member's content, reference order and shape are the copied seeds'. In source order the first pass holds its
    /// reference-free predecessors and the entries the full expansions keep grow linearly; in reversed order the first
    /// member evaluated carries the reference, so the first pass still copies growing widths (a residual).
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ClosedChain_SharesOneGroupOfSets_InLinearStorage(bool reversed)
    {
        var sizes = new[] { 32, 64, 128 };
        var entries = new long[sizes.Length];
        var copiedEntries = new long[sizes.Length];
        for (var at = 0; at < sizes.Length; at++)
        {
            var k = sizes[at];
            var source = MixedCycleMemberScheduleTests.ClosedChain(k, reversed);
            var (complete, copied) = AssertSameOutcome(source);
            Assert.Equal(2L * k + 4, complete.Observations.SummaryMemberEvaluations);
            Assert.Equal(2L * k - 2, complete.Observations.SummaryMemberReaderNotifications);
            Assert.InRange(complete.Observations.SummaryMemberCompleteSeeds, k - 1, k);
            Assert.Equal(0, copied.Observations.SummaryMemberCompleteSeeds);
            Assert.Equal(1, complete.Observations.SummaryMemberComponentBounds);
            entries[at] = complete.Observations.SummaryMemberExpansionEntries;
            copiedEntries[at] = copied.Observations.SummaryMemberExpansionEntries;

            var root = SourceProvenance.ParseValid(source).Root;
            var members = MembersDeclaring(Memo(root), "P1");
            var copiedMembers = MembersDeclaring(Copied(() => Memo(root)), "P1");
            var cycle = Enumerable.Range(1, k).Select(i => $"P{i}").ToArray();
            foreach (var name in cycle)
                Assert.True(SameSets(members[name], members["P1"]), name);
            var (seeds, retained) = Retained(cycle.Select(name => members[name]));
            var (copiedSeeds, copiedRetained) = Retained(cycle.Select(name => copiedMembers[name]));
            Assert.Equal(k, seeds);
            Assert.Equal(k, copiedSeeds);
            Assert.Equal(k + 1L, retained);
            Assert.Equal(k * (k + 1L), copiedRetained);
            output.WriteLine($"K={k}: expansion entries {copiedEntries[at]} -> {entries[at]}, complete seeds "
                + $"{complete.Observations.SummaryMemberCompleteSeeds}, {seeds} seeds retaining {copiedRetained} -> {retained} entries");

            var expected = Enumerable.Range(1, k).Select(i => $"p{i}").Order(StringComparer.Ordinal).Select(name => (name, 0)).ToArray();
            foreach (var member in new[] { "P1", "P2", $"P{k / 2}", $"P{k}" })
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, "F", member), expected);
        }

        Assert.InRange((double)copiedEntries[2] / copiedEntries[1], 3.0, 5.0);
        if (reversed)
            Assert.InRange(entries[2], 1, copiedEntries[2] / 2);
        else
            Assert.InRange((double)entries[2] / entries[1], 1.5, 2.5);
    }

    /// <summary>
    /// The single-predecessor cycle (every member but the closing one a share): the copied seeds kept K flat members of full
    /// width, each share folded by its change test. Each share whose change test folds it now takes a new seed over the
    /// complete seed's sets, and the level retains one group of sets — two in reversed order, where the last member's
    /// first-pass seed is already complete and stays, as with the copied seeds.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SinglePredecessorCycle_SharesTheCompleteSeedsSets(bool reversed)
    {
        foreach (var k in new[] { 32, 96 })
        {
            var source = SinglePredecessorCycle(k, reversed);
            var (complete, _) = AssertSameOutcome(source);
            Assert.InRange(complete.Observations.SummaryMemberCompleteSeeds, k - 1, k);
            var root = SourceProvenance.ParseValid(source).Root;
            var cycle = Enumerable.Range(1, k).Select(i => $"P{i}").ToArray();
            var members = MembersDeclaring(Memo(root), "P1");
            var copiedMembers = MembersDeclaring(Copied(() => Memo(root)), "P1");
            Assert.Equal((reversed ? 2 : 1) * (k + 1L), Retained(cycle.Select(name => members[name])).Entries);
            Assert.InRange(Retained(cycle.Select(name => copiedMembers[name])).Entries, (long)k * k / 2, long.MaxValue);
        }
    }

    // ── Where sharing is refused ────────────────────────────────────────────

    [Fact]
    public void CompleteSeedStorageBelongsToOneSummaryBuild()
    {
        var root = SourceProvenance.ParseValid(MixedCycleMemberScheduleTests.ClosedChain(16)).Root;
        var first = MembersDeclaring(Memo(root), "P1");
        var second = MembersDeclaring(Memo(root), "P1");
        Assert.True(SameSets(first["P1"], first["P2"]));
        Assert.True(SameSets(second["P1"], second["P2"]));
        var firstSets = first["P1"].OwnSetObjects().Where(entry => entry.Count > 0)
            .Select(entry => entry.Set).ToHashSet(ReferenceEqualityComparer.Instance);
        Assert.False(firstSets.Overlaps(second["P1"].OwnSetObjects().Select(entry => entry.Set)));
        AssertSameContentOrderAndShape(first["P1"], second["P1"], "P1 in two builds of the same AST");
    }

    /// <summary>
    /// REFERENCE ORDER. A member whose copied expansion writes a reference before the complete seed's own sets, out of that
    /// seed's order, keeps its own expansion, with the copied order (<c>Lib.Z</c>, <c>Lib.Y</c>, <c>Lib.X</c>); the odd members
    /// after it, which read it first, take ITS sets (its content is complete too), and the even ones the closing member's.
    /// A reference the complete seed already holds where the expansion writes it does not stop a member taking that seed:
    /// with <c>E</c> read after the predecessors the whole cycle is one group of sets.
    /// </summary>
    [Fact]
    public void AMemberWritingAReferenceOutOfOrder_KeepsItsOwnSeed()
    {
        const int k = 30;
        foreach (var before in new[] { true, false })
        {
            var source = ExternalReadCycle(k, before);
            AssertSameOutcome(source);
            var members = MembersDeclaring(Memo(SourceProvenance.ParseValid(source).Root), "P1");
            Assert.Equal(["Lib.Y", "Lib.Z", "Lib.X"], Paths(members["P1"]));
            if (!before)
            {
                for (var i = 2; i <= k; i++)
                    Assert.True(SameSets(members["P1"], members[$"P{i}"]), $"P{i}");
                continue;
            }

            var refused = members[$"P{OutOfOrder}"];
            Assert.False(SameSets(members[$"P{OutOfOrder - 2}"], refused));
            Assert.False(SameSets(members[$"P{OutOfOrder - 1}"], refused));
            Assert.Equal(["Lib.Z", "Lib.Y", "Lib.X"], Paths(refused));
            for (var i = 2; i <= k; i++)
                Assert.True(SameSets(i >= OutOfOrder && i % 2 == 1 ? refused : members["P1"], members[$"P{i}"]), $"P{i}");
        }
    }

    /// <summary>
    /// UNEQUAL CONTENT. A cycle closed through a path (<c>P1</c> reads <c>B.X</c>, <c>B</c>'s row reads <c>PK</c>) does not carry
    /// the chain's content back to <c>P1</c>: no member holds a seed that is not complete, and every member keeps the copied
    /// seed's content, reference order and shape.
    /// </summary>
    [Fact]
    public void ACycleThatDoesNotCarryItsContentAround_SharesNoIncompleteSeed()
    {
        const int k = 24;
        var source = UnequalCycle(k);
        AssertSameOutcome(source);
        var members = MembersDeclaring(Memo(SourceProvenance.ParseValid(source).Root), "P1");
        Assert.Equal(["B.X", "Lib.X"], Paths(members["P1"]));
        Assert.Single(members["P1"].Clone().OwnerQualifiedParameters);
        Assert.Same(members[$"P{k}"], members["B"]);
        for (var i = 1; i < k; i++)
            Assert.False(SameSets(members[$"P{i}"], members[$"P{k}"]), $"P{i}");
    }

    // ── Paths, readers, owners and navigation ───────────────────────────────

    /// <summary>
    /// Branched cycles, members carrying several library paths (in both source orders), a path back into the owner's own
    /// member, an external path dependency, path-bearing readers, an enclosing owner's parameters, a cycle read by
    /// navigation from the owner's level, and two chained cycles: every member keeps the copied seed's content, reference
    /// order and shape, and the outcome, schedule, checkpoint sequence, frames, part work and static work are the copied
    /// seeds', while the full expansions keep fewer entries.
    /// </summary>
    [Theory]
    [InlineData("branched")]
    [InlineData("paths")]
    [InlineData("paths-reversed")]
    [InlineData("self-path")]
    [InlineData("external-path")]
    [InlineData("readers")]
    [InlineData("owner")]
    [InlineData("navigated")]
    [InlineData("two-cycles")]
    public void MixedCyclesWithPathsReadersOwnersAndNavigation_KeepTheCopiedSeeds(string shape)
    {
        foreach (var k in new[] { 16, 48 })
        {
            var (complete, copied) = AssertSameOutcome(ShapeSource(shape, k));
            Assert.InRange(complete.Observations.SummaryMemberCompleteSeeds, 1, long.MaxValue);
            Assert.InRange(complete.Observations.SummaryMemberExpansionEntries, 0, copied.Observations.SummaryMemberExpansionEntries - 1);
            output.WriteLine($"{shape} K={k}: expansion entries {copied.Observations.SummaryMemberExpansionEntries} -> "
                + $"{complete.Observations.SummaryMemberExpansionEntries}, complete seeds {complete.Observations.SummaryMemberCompleteSeeds}");
        }
    }

    // ── Controls ────────────────────────────────────────────────────────────

    /// <summary>
    /// Levels without a mixed cycle of several members are unchanged: an acyclic level and its readers, a pure-union
    /// component solved as one unit, members that read themselves, a member navigating its own owner, and the
    /// two-predecessor chain. Every counter, the sequence of every cancellation checkpoint, the static work and every
    /// summary — references in order, compared by the adoption check — are the copied seeds'.
    /// </summary>
    [Fact]
    public void LevelsWithoutAMixedCycle_AreUnchanged()
    {
        const int k = 40;
        var sources = new[]
        {
            Level(k, i => i == 1 ? "p1 + Lib.X" : Chain(i)),
            Level(k, i => i == 1 ? $"P{k} + p1" : Chain(i)),
            Level(k, i => i == 1 ? "P1 + p1 + Lib.X" : $"P{i} + P{i - 1} + p{i}", row: $"P{k}"),
            Level(k, i => i == 1 ? "p1" : Chain(i), row: "X", extra: $"X = F.P{k}\n"),
            Level(k, i => i == 1 ? "p1 + Lib.X" : Chain(i), row: $"R{k}",
                extra: string.Concat(Enumerable.Range(1, k).Select(i => $"R{i} = P{i} + Lib.Y\n"))),
            SharedPredecessorExpansionTests.TwoPredecessorChain(k),
        };
        foreach (var source in sources)
        {
            var complete = Parse(source);
            var copied = Copied(() => Parse(source));
            Assert.Equal("", complete.Diagnostics);
            Assert.Equal(copied.Metadata, complete.Metadata);
            Assert.Equal(copied.Sequence, complete.Sequence);
            var (c, d) = (complete.Observations, copied.Observations);
            Assert.Equal(0, c.SummaryMemberCompleteSeeds);
            Assert.Equal(0, c.SummaryMemberComponentBounds);
            Assert.Equal(d.SummaryMemberEvaluations, c.SummaryMemberEvaluations);
            Assert.Equal(d.SummaryMemberReaderNotifications, c.SummaryMemberReaderNotifications);
            Assert.Equal(d.SummaryMemberExpansions, c.SummaryMemberExpansions);
            Assert.Equal(d.SummaryMemberExpansionEntries, c.SummaryMemberExpansionEntries);
            Assert.Equal(d.SummaryMemberExpansionHeldParts, c.SummaryMemberExpansionHeldParts);
            Assert.Equal(d.MemberEntriesCopied, c.MemberEntriesCopied);
            Assert.Equal(d.MemberBudgetFoldEntries, c.MemberBudgetFoldEntries);
            Assert.Equal(d.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel),
                c.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel));
            Assert.Equal(d.RequiredAncestorSettlementFrames, c.RequiredAncestorSettlementFrames);
            Assert.Equal(d.SettlementSeedPartWork, c.SettlementSeedPartWork);
            Assert.Equal(d.RequiredAncestorLevelEvaluations, c.RequiredAncestorLevelEvaluations);
            Assert.Equal(Copied(() => Work(source)), Work(source));
            var root = SourceProvenance.ParseValid(source).Root;
            var completeMemo = Memo(root);
            var copiedMemo = Copied(() => Memo(root));
            foreach (var (key, summary) in copiedMemo.ContextualAlgorithmSummaries ?? [])
                Assert.Null(SummaryMemo.AdoptedSummaryDifference(completeMemo.ContextualAlgorithmSummaries![key], summary));
            foreach (var (algorithm, summary) in copiedMemo.IndependentAlgorithmSummaries ?? [])
                Assert.Null(SummaryMemo.AdoptedSummaryDifference(completeMemo.IndependentAlgorithmSummaries![algorithm], summary));
        }
    }

    // ── Generated levels ────────────────────────────────────────────────────

    /// <summary>
    /// The generated levels of MIXED-CYCLE SCHEDULE, dense in mixed cycles (paths, paths through the owner, opens,
    /// parameterized members, deconstruction, shadowing, nested and detached owners, both declaration orders): every
    /// program's diagnostics, metadata, checkpoint sequence, evaluations, frames and static work are the copied seeds',
    /// and every summary keeps its content, reference order and shape.
    /// </summary>
    [Fact]
    public void GeneratedCyclicLevels_KeepTheCopiedSeeds()
    {
        long compared = 0, programsTaking = 0, completeSeeds = 0;
        foreach (var source in MixedCycleMemberScheduleTests.GeneratedCyclicLevels(300, seed: 41))
        {
            var complete = Parse(source);
            var copied = Copied(() => Parse(source));
            Assert.Equal(copied.Diagnostics, complete.Diagnostics);
            Assert.Equal(copied.Metadata, complete.Metadata);
            Assert.Equal(copied.Sequence, complete.Sequence);
            Assert.Equal(copied.Observations.SummaryMemberEvaluations, complete.Observations.SummaryMemberEvaluations);
            Assert.Equal(copied.Observations.RequiredAncestorSettlementFrames, complete.Observations.RequiredAncestorSettlementFrames);
            if (complete.Observations.SummaryMemberCompleteSeeds > 0)
                programsTaking++;
            completeSeeds += complete.Observations.SummaryMemberCompleteSeeds;
            if (complete.Diagnostics.Length != 0)
                continue;
            Assert.Equal(Copied(() => Work(source)), Work(source));
            foreach (var (where, left, right) in Summaries(source))
            {
                compared++;
                AssertSameContentOrderAndShape(left, right, where + "\n" + source);
            }
        }

        output.WriteLine($"{compared} summaries compared in order; {programsTaking} programs took {completeSeeds} complete seeds");
        Assert.InRange(programsTaking, 30, int.MaxValue);
    }

    // ── Cancellation and admission ──────────────────────────────────────────

    /// <summary>
    /// CANCELLATION: a member that takes a complete seed in place of a full expansion takes that expansion's summary-channel
    /// checkpoints, context uses and read records. A token cancelled at the checkpoint the closing member takes in the
    /// second pass escapes with that token, records nothing after it, and leaves nothing behind: a fresh parse publishes
    /// the uncancelled metadata.
    /// </summary>
    [Fact]
    public void CancellationAtACompleteSeedsCheckpoint_EscapesWithTheToken_AndLeavesNothingBehind()
    {
        const int k = 64;
        var source = MixedCycleMemberScheduleTests.ClosedChain(k);
        var uncancelled = Parse(source);
        long target = -1;
        FrontEndTraversalObservations probe = null!;
        probe = new FrontEndTraversalObservations
        {
            CheckpointReached = (kind, ordinal) =>
            {
                if (kind == FrontEndCancellationCheckpoint.SummaryChannel && target < 0 && probe.SummaryMemberCompleteSeeds == k - 1)
                    target = ordinal;
            },
        };
        Parser.ParseObserved(source, options: null, probe);
        Assert.InRange(target, 1, uncancelled.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel));

        using var cancellation = new CancellationTokenSource();
        long completeSeedsAtCancel = -1;
        FrontEndTraversalObservations observations = null!;
        observations = new FrontEndTraversalObservations
        {
            CheckpointReached = (kind, ordinal) =>
            {
                if (kind != FrontEndCancellationCheckpoint.SummaryChannel || ordinal != target || cancellation.IsCancellationRequested)
                    return;
                completeSeedsAtCancel = observations.SummaryMemberCompleteSeeds;
                cancellation.Cancel();
            },
        };

        var error = Assert.Throws<OperationCanceledException>(() => Parser.ParseObserved(
            source, new RunOptions { SourceProcessingCancellationToken = cancellation.Token }, observations));

        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal(target, observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel));
        Assert.Equal(k - 1, completeSeedsAtCancel);
        Assert.Equal(k - 1, observations.SummaryMemberCompleteSeeds);
        Assert.Equal(uncancelled.Metadata, Parse(source).Metadata);
    }

    /// <summary>
    /// The work bound is resource policy (SETTLEMENT FRAME CHARGE): the closed chain, its path-bearing variant, the
    /// single-predecessor cycle and the navigated cycle are admitted at exactly the copied seeds' charge and refused one
    /// unit below it.
    /// </summary>
    [Theory]
    [InlineData("closed")]
    [InlineData("paths")]
    [InlineData("single-predecessor")]
    [InlineData("navigated")]
    public void TheWorkBound_AdmitsAtTheCopiedCharge_AndRefusesOneUnitBelow(string shape)
    {
        var source = shape switch
        {
            "closed" => MixedCycleMemberScheduleTests.ClosedChain(48),
            "single-predecessor" => SinglePredecessorCycle(48),
            _ => ShapeSource(shape, 48),
        };

        long Run(long? limit)
        {
            var (resolved, ledger, _) = ExposureSettlementFrameChargeTests.Resolved(source,
                limits => limit.HasValue ? limits with { MaxEvaluations = limit.Value } : limits);
            _ = PropertyExposureResolver.Resolve(resolved);
            return ledger.WorkCharged;
        }

        var charge = Copied(() => Run(null));
        Assert.Equal(charge, Run(null));
        Assert.Equal(charge, Run(charge));
        Assert.Throws<StaticQueryLimitExceededException>(() => Run(charge - 1));
    }
}
