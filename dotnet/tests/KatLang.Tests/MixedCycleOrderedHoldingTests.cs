using System.Text;
using Xunit.Abstractions;
using static KatLang.PropertyDependencyGraphBuilder;

namespace KatLang.Tests;

/// <summary>
/// ORDERED HOLDING (November 28 2026; C# exposure implementation only — no classification, requirement, diagnostic kind,
/// value or Lean rule changes). After MIXED-CYCLE COMPLETE SEEDS a mixed cycle whose first evaluated member already carries
/// a reference (the closed chain in reversed source order), or whose members carry paths or escaping names, still copied
/// growing widths in its first pass: every first expansion that read a reference-bearing member seed united it into a new
/// flat seed, K² / 2 entries over a chain of K. The first evaluation of such a member now holds those member seeds by
/// reference with their references copied into its own set in the union's order, and the result, an ORDERED HOLDER, stands
/// for the copied flat seed: every decision that depends on its shape is taken as for that seed or after folding it in
/// place, and a converged component folds every ordered holder its seeds reach. The change test also tells a replaced
/// reference-bearing holder from its wider successor by an upper bound of its requirement counts instead of folding it,
/// and makes that fold at convergence where a seed that stays still holds it. Oracle: the copied seeds
/// (<see cref="PropertyDependencyGraphBuilder.ReferenceBearingSeedsCopiedForTesting"/>), compared by every member's content
/// with its references IN ORDER and its whole part structure, published metadata, diagnostics, the checkpoint sequence,
/// static work, settlement frames and deterministic counters, never time.
/// </summary>
public sealed class MixedCycleOrderedHoldingTests(ITestOutputHelper output)
{
    // ── Harness ─────────────────────────────────────────────────────────────

    private static T Copied<T>(Func<T> work)
    {
        var previous = ReferenceBearingSeedsCopiedForTesting.Value;
        ReferenceBearingSeedsCopiedForTesting.Value = true;
        try { return work(); }
        finally { ReferenceBearingSeedsCopiedForTesting.Value = previous; }
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
    private static SummaryMemo Memo(Algorithm root, FrontEndTraversalObservations? observations = null)
    {
        var memo = StandaloneSummaries.MemoFor(root, observations);
        BuildSummaries(root, AnalyzedStaticStructures.ForBoundAst(root), memo, observations);
        return memo;
    }

    private static IEnumerable<AlgorithmSummary> AllSummaries(SummaryMemo memo)
        => (memo.IndependentAlgorithmSummaries?.Values ?? Enumerable.Empty<AlgorithmSummary>())
            .Concat(memo.ContextualAlgorithmSummaries?.Values ?? Enumerable.Empty<AlgorithmSummary>());

    /// <summary>Every summary of <paramref name="source"/> under production and under the copied seeds, paired.</summary>
    private static List<(string Where, SummarySeed Held, SummarySeed Copied)> Summaries(string source)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var held = Memo(root);
        var copied = Copied(() => Memo(root));
        var pairs = new List<(string, SummarySeed, SummarySeed)>();
        void Add(string where, AlgorithmSummary left, AlgorithmSummary right)
        {
            pairs.Add((where + " output", left.OutputSeed, right.OutputSeed));
            Assert.Equal(right.MemberSeeds.Count, left.MemberSeeds.Count);
            foreach (var (name, seed) in right.MemberSeeds)
                pairs.Add((where + " member " + name, left.MemberSeeds[name], seed));
        }

        Assert.Equal(copied.IndependentAlgorithmSummaries?.Count ?? 0, held.IndependentAlgorithmSummaries?.Count ?? 0);
        Assert.Equal(copied.ContextualAlgorithmSummaries?.Count ?? 0, held.ContextualAlgorithmSummaries?.Count ?? 0);
        foreach (var (algorithm, summary) in copied.IndependentAlgorithmSummaries ?? [])
            Add("independent", held.IndependentAlgorithmSummaries![algorithm], summary);
        foreach (var (key, summary) in copied.ContextualAlgorithmSummaries ?? [])
            Add("contextual", held.ContextualAlgorithmSummaries![key], summary);
        return pairs;
    }

    /// <summary>
    /// A seed's whole part structure: each seed's own entry count and the parts it holds, in order, a seed met again written
    /// as a back reference — what part-by-part settlement and navigation views read of a published seed.
    /// </summary>
    internal static string Structure(SummarySeed seed)
    {
        var ids = new Dictionary<SummarySeed, int>(ReferenceEqualityComparer.Instance);
        var text = new StringBuilder();
        var pending = new Stack<(SummarySeed Seed, bool Close)>();
        pending.Push((seed, false));
        while (pending.TryPop(out var entry))
        {
            if (entry.Close)
            {
                text.Append(')');
                continue;
            }

            if (ids.TryGetValue(entry.Seed, out var id))
            {
                text.Append('@').Append(id).Append(' ');
                continue;
            }

            ids.Add(entry.Seed, ids.Count);
            text.Append(entry.Seed.OwnEntryCount).Append(' ');
            if (entry.Seed.AbsorbedPartsWithoutFolding is not { } parts)
                continue;
            text.Append('(');
            pending.Push((entry.Seed, true));
            for (var i = parts.Count - 1; i >= 0; i--)
                pending.Push((parts[i], false));
        }

        return text.ToString();
    }

    /// <summary>
    /// Two seeds hold the same content — the same required names, visible names and owner-qualified parameters, and the
    /// same references, each with its origin, path, bound owners and selection, in the SAME order — and the same whole
    /// part structure.
    /// </summary>
    private static void AssertSameContentOrderAndShape(SummarySeed held, SummarySeed copied, string where)
    {
        Assert.True(Structure(copied) == Structure(held), $"{where}: {Structure(copied)} -> {Structure(held)}");
        held = held.Clone();
        copied = copied.Clone();
        Assert.True(copied.RequiredAncestorOwnedParameterNames.SetEquals(held.RequiredAncestorOwnedParameterNames), where);
        Assert.True(copied.VisiblePropertyDependencyNames.SetEquals(held.VisiblePropertyDependencyNames), where);
        Assert.True(copied.OwnerQualifiedParameters.SetEquals(held.OwnerQualifiedParameters), where);
        static (string, object?, object?, bool, PendingSelection?) Identity(SummaryReference reference)
            => reference is PendingReference anchored
                ? (anchored.ContentKey, anchored.Origin.Facts, anchored.Origin.Key, anchored.OpenPath, anchored.Selection)
                : (reference.ContentKey, null, null, false, null);
        Assert.True(copied.PendingReferences.Select(Identity).SequenceEqual(held.PendingReferences.Select(Identity)), where);
    }

    /// <summary>
    /// Production and the copied seeds agree on the outcome, the schedule, the checkpoint sequence, the settlement frames,
    /// part work and navigation, the static work, and every summary in content, reference order and part structure; and
    /// no published seed, or seed it holds, is an ordered holder.
    /// </summary>
    private static (Observed Held, Observed Copied) AssertSameOutcome(string source)
    {
        var held = Parse(source);
        var copied = Copied(() => Parse(source));
        Assert.Equal("", held.Diagnostics);
        Assert.Equal(copied.Diagnostics, held.Diagnostics);
        Assert.Equal(copied.Metadata, held.Metadata);
        Assert.Equal(copied.Sequence, held.Sequence);
        var (h, c) = (held.Observations, copied.Observations);
        Assert.Equal(c.SummaryMemberEvaluations, h.SummaryMemberEvaluations);
        Assert.Equal(c.SummaryMemberReaderNotifications, h.SummaryMemberReaderNotifications);
        Assert.Equal(c.SummaryMemberCompleteSeeds, h.SummaryMemberCompleteSeeds);
        Assert.Equal(c.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel),
            h.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel));
        Assert.Equal(c.RequiredAncestorSettlementFrames, h.RequiredAncestorSettlementFrames);
        Assert.Equal(c.SettlementSeedPartWork, h.SettlementSeedPartWork);
        Assert.Equal(c.MemberNavigationFolds, h.MemberNavigationFolds);
        Assert.Equal(c.MemberNavigationEntriesRead, h.MemberNavigationEntriesRead);
        Assert.Equal(0, c.SummaryMemberOrderedHolders);
        Assert.Equal(0, c.SummaryMemberChangeTestsWithoutFold);
        Assert.Equal(Copied(() => Work(source)), Work(source));
        foreach (var (where, left, right) in Summaries(source))
            AssertSameContentOrderAndShape(left, right, where);
        AssertNoOrderedHolderPublished(Memo(SourceProvenance.ParseValid(source).Root));
        return (held, copied);
    }

    /// <summary>No seed a summary publishes, nor any seed it holds, is an ordered holder.</summary>
    private static void AssertNoOrderedHolderPublished(SummaryMemo memo)
    {
        var seen = new HashSet<SummarySeed>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<SummarySeed>();
        foreach (var summary in AllSummaries(memo))
        {
            pending.Push(summary.OutputSeed);
            foreach (var seed in summary.MemberSeeds.Values)
                pending.Push(seed);
        }

        while (pending.TryPop(out var seed))
        {
            if (!seen.Add(seed))
                continue;
            Assert.False(seed.IsOrderedHolder);
            foreach (var part in seed.AbsorbedPartsWithoutFolding ?? [])
                pending.Push(part);
        }
    }

    /// <summary>What member seeds retain: the distinct seeds they are and hold, and the entries of their distinct own sets.</summary>
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

    private static IReadOnlyDictionary<string, SummarySeed> MembersDeclaring(SummaryMemo memo, string member)
        => Assert.Single(AllSummaries(memo), summary => summary.MemberSeeds.ContainsKey(member)).MemberSeeds;

    private static string Names(string prefix, int from, int to)
        => string.Join(", ", Enumerable.Range(from, to - from + 1).Select(i => $"{prefix}{i}"));

    private static string Arguments(int count) => string.Join(", ", Enumerable.Range(1, count));

    // ── Shapes ──────────────────────────────────────────────────────────────

    /// <summary>
    /// <c>F(p1, …, pK)</c> declaring <c>Lib</c> and the members <c>P(i) = member(i)</c> (in reversed source order with
    /// <paramref name="reversed"/>), then <paramref name="extra"/> and the output row.
    /// </summary>
    private static string Level(int members, Func<int, string> member, string row = "Lib.X", bool reversed = false, string extra = "",
        string before = "")
    {
        var source = new StringBuilder(before).Append($"F({Names("p", 1, members)}) = {{\nLib = {{\npublic X = 1\npublic Y = 2\npublic Z = 3\n}}\n");
        var order = Enumerable.Range(1, members);
        foreach (var i in reversed ? order.Reverse() : order)
            source.Append($"P{i} = {member(i)}\n");
        source.Append(extra).Append(row).Append($"\n}}\nF({Arguments(members)})\n");
        return source.ToString();
    }

    private static string Chain(int i) => i == 2 ? "P1 + p2" : $"P{i - 1} + P{i - 2} + p{i}";

    private static string Closing(int k) => $"P{k} + p1 + Lib.X";

    private static string SinglePredecessorCycle(int k, bool reversed = false)
        => Level(k, i => i == 1 ? Closing(k) : $"P{i - 1} + p{i}", reversed: reversed);

    private static string ShapeSource(string shape, int k) => shape switch
    {
        // Every 4th member also reads one of three library paths, in both source orders.
        "paths" => Level(k, i => (i == 1 ? Closing(k) : Chain(i)) + (i % 4 == 0 ? $" + Lib.{(char)('X' + i % 3)}" : "")),
        "paths-reversed" => Level(k, i => (i == 1 ? Closing(k) : Chain(i)) + (i % 4 == 0 ? $" + Lib.{(char)('X' + i % 3)}" : ""), reversed: true),
        // Every third member reads an escaping root property BEFORE its predecessors, or after them.
        "escaping-before" => Level(k, i => (i % 3 == 0 && i > 2 ? "G + " : "") + (i == 1 ? Closing(k) : Chain(i)), before: "G = 5\n"),
        "escaping-after" => Level(k, i => (i == 1 ? Closing(k) : Chain(i)) + (i % 3 == 0 && i > 2 ? " + G" : ""), before: "G = 5\n"),
        // Every 5th member reads a member of a block declared beside the cycle.
        "external-path" => Level(k, i => (i == 1 ? Closing(k) : Chain(i)) + (i % 5 == 0 ? " + E.V" : ""), extra: "E = { public V = 1 }\n"),
        // Chords every 8th member (P(i) also reads P(i+4)) in reversed source order: chord re-evaluations meet ordered holders.
        "branched-reversed" => Level(k, i => (i == 1 ? Closing(k) : Chain(i)) + (i % 8 == 0 && i + 4 <= k ? $" + P{i + 4}" : ""), reversed: true),
        // Path-bearing readers of every member of the reversed chain.
        "readers-reversed" => Level(k, i => i == 1 ? Closing(k) : Chain(i), row: $"R{k}", reversed: true,
            extra: string.Concat(Enumerable.Range(1, k).Select(i => $"R{i} = P{i} + Lib.Y\n"))),
        "owner-reversed" => OwnerCycle(k),
        "navigated-reversed" => NavigatedCycle(k),
        "two-cycles-reversed" => TwoCycles(k),
        _ => throw new ArgumentOutOfRangeException(nameof(shape)),
    };

    /// <summary>The reversed chain whose members also read an enclosing owner's parameter, which their level does not bind.</summary>
    private static string OwnerCycle(int k)
    {
        var source = new StringBuilder($"G({Names("q", 1, k)}) = {{\nF({Names("p", 1, k)}) = {{\nLib = {{\npublic X = 1\n}}\n");
        for (var i = k; i >= 1; i--)
            source.Append($"P{i} = {(i == 1 ? Closing(k) : Chain(i))} + q{i}\n");
        return source.Append($"Lib.X\n}}\nF({Arguments(k)})\n}}\nG({Arguments(k)})\n").ToString();
    }

    /// <summary>The reversed chain inside a library member, read by navigation from readers at the owner's level.</summary>
    private static string NavigatedCycle(int k)
    {
        var source = new StringBuilder($"F({Names("p", 1, k)}) = {{\nLib = {{\npublic X = 1\npublic Y = 2\n}}\nL = {{\n");
        for (var i = k; i >= 1; i--)
            source.Append($"public P{i} = {(i == 1 ? Closing(k) : Chain(i))}\n");
        source.Append("}\n");
        for (var i = 1; i <= k; i++)
            source.Append($"R{i} = L.P{i} + Lib.Y\n");
        return source.Append($"R{k}\n}}\nF({Arguments(k)})\n").ToString();
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DistinctPaths_UseTheOrdinaryUnionWhenReferencesDominate(bool addRequirements)
    {
        const int k = 48;
        var library = "D = {\n" + string.Concat(Enumerable.Range(1, k).Select(i => $"public X{i} = 1\n")) + "}\n";
        var source = Level(k, i => (i == 1 ? $"P{k}" : i == 2 ? "P1" : $"P{i - 1} + P{i - 2}") + $" + D.X{i}"
            + (addRequirements ? $" + p{i}" : ""),
            reversed: true, extra: library);
        var (held, copied) = AssertSameOutcome(source);

        // Only the initial narrow predecessors can take the ordered path. Each of their references was inserted at
        // the hold. Budget folds copy only requirements, one per distinct path in the parameter-bearing fixture.
        var copiedPaths = held.Observations.SummaryMemberOrderedReferencesCopied;
        if (addRequirements)
            Assert.InRange(copiedPaths, 1, 2 * SummarySeed.CopiedCompletedEntries * SummarySeed.CopiedCompletedEntries);
        else
            Assert.Equal(0, copiedPaths);
        Assert.Equal(copiedPaths, held.Observations.MemberBudgetFoldEntries);
        Assert.Equal(copied.Observations.SummaryMemberExpansionEntries, held.Observations.SummaryMemberExpansionEntries);
        Assert.Equal(0, copied.Observations.SummaryMemberOrderedReferencesCopied);
    }

    /// <summary>Two reversed chains, the second reading the first's tail.</summary>
    private static string TwoCycles(int k)
    {
        var source = new StringBuilder($"F({Names("p", 1, k)}, {Names("q", 1, k)}) = {{\nLib = {{\npublic X = 1\npublic Y = 2\n}}\n");
        for (var i = k; i >= 3; i--) source.Append($"A{i} = A{i - 1} + A{i - 2} + p{i}\n");
        source.Append($"A2 = A1 + p2\nA1 = A{k} + p1 + Lib.X\n");
        for (var i = k; i >= 3; i--) source.Append($"B{i} = B{i - 1} + B{i - 2} + q{i}\n");
        source.Append($"B2 = B1 + q2\nB1 = B{k} + A{k} + q1 + Lib.Y\n");
        return source.Append($"B{k}\n}}\nF({Arguments(2 * k)})\n").ToString();
    }

    /// <summary>
    /// A single-predecessor cycle of K members inside a block, navigated by readers at the owner's level. The block binds no
    /// parameter, so the owner's parameters stay required names; <c>M{path}</c> also reads a path, so every share from it
    /// on carries a reference; the parameters repeat with period <paramref name="period"/>, so the first pass already
    /// holds the whole content at member <paramref name="period"/> + <c>path</c> and the second pass stops there, leaving
    /// the first-pass shares of the later members in place.
    /// </summary>
    internal static string EarlyStoppingBlockCycle(int k, int period, int path)
    {
        var source = new StringBuilder($"F({Names("p", 1, period)}) = {{\nQ = {{ public Z = 3 }}\nC = {{\n");
        for (var i = 1; i <= k; i++)
        {
            var read = i == 1 ? $"M{k}" : $"M{i - 1}";
            source.Append($"public M{i} = {read} + p{(i - 1) % period + 1}{(i == path ? " + Q.Z" : "")}\n");
        }

        source.Append("}\n");
        for (var i = 1; i <= k; i++)
            source.Append($"R{i} = C.M{i}\n");
        return source.Append($"R{k}\nR{k - 1}\n}}\nF({Arguments(period)})\n").ToString();
    }

    // ── The reversed chain ──────────────────────────────────────────────────

    /// <summary>
    /// The closed chain in reversed source order: the first member evaluated, <c>P1</c>, carries <c>Lib.X</c>, so every
    /// first-pass expansion read reference-bearing seeds and the copied seeds kept K² / 2 entries. Its first pass now holds
    /// them: the entries the full expansions keep grow linearly, about K − 30 expansions are ordered holders, and one fold
    /// materializes the closing member's seed when its completeness is first asked. The evaluations, notifications,
    /// checkpoint sequence, frames, static work and every member's content, reference order and part structure are the
    /// copied seeds', and the members still retain one group of K + 1 entries.
    /// </summary>
    [Fact]
    public void ReversedClosedChain_FirstPassHoldsInsteadOfCopying()
    {
        var sizes = new[] { 32, 64, 128 };
        var entries = new long[sizes.Length];
        var copiedEntries = new long[sizes.Length];
        for (var at = 0; at < sizes.Length; at++)
        {
            var k = sizes[at];
            var source = MixedCycleMemberScheduleTests.ClosedChain(k, reversed: true);
            var (held, copied) = AssertSameOutcome(source);
            Assert.Equal(2L * k + 4, held.Observations.SummaryMemberEvaluations);
            Assert.InRange(held.Observations.SummaryMemberOrderedHolders, k - 40, k);
            Assert.Equal(1, held.Observations.SummaryMemberOrderedFolds);
            Assert.Equal(k + 1L, held.Observations.SummaryMemberOrderedFoldEntries);
            entries[at] = held.Observations.SummaryMemberExpansionEntries;
            copiedEntries[at] = copied.Observations.SummaryMemberExpansionEntries;

            var root = SourceProvenance.ParseValid(source).Root;
            var members = MembersDeclaring(Memo(root), "P1");
            var (seeds, retained) = Retained(Enumerable.Range(1, k).Select(i => members[$"P{i}"]));
            Assert.Equal(k, seeds);
            Assert.Equal(k + 1L, retained);
            output.WriteLine($"K={k}: expansion entries {copiedEntries[at]} -> {entries[at]}, ordered holders "
                + $"{held.Observations.SummaryMemberOrderedHolders}, ordered folds {held.Observations.SummaryMemberOrderedFoldEntries} entries");
        }

        Assert.InRange((double)copiedEntries[2] / copiedEntries[1], 3.0, 5.0);
        Assert.InRange((double)entries[2] / entries[1], 1.5, 2.5);
    }

    /// <summary>
    /// The closed chain in source order holds its reference-free first pass already (MIXED-CYCLE COMPLETE SEEDS) and makes no
    /// ordered holder: the closing member stands for the copied flat seed but holds nothing that proves it wider than eight
    /// entries, so it folds. Every counter is the copied seeds'.
    /// </summary>
    [Fact]
    public void ClosedChainInSourceOrder_MakesNoOrderedHolder()
    {
        var source = MixedCycleMemberScheduleTests.ClosedChain(96);
        var (held, copied) = AssertSameOutcome(source);
        Assert.Equal(0, held.Observations.SummaryMemberOrderedHolders);
        Assert.Equal(copied.Observations.SummaryMemberExpansionEntries, held.Observations.SummaryMemberExpansionEntries);
        Assert.Equal(copied.Observations.SummaryMemberExpansionHeldParts, held.Observations.SummaryMemberExpansionHeldParts);
    }

    // ── Paths, escaping names, chords, readers, owners and navigation ───────

    /// <summary>
    /// Members carrying library paths in both source orders, escaping root names read before or after the predecessors,
    /// an external path dependency, chords in reversed order, path-bearing readers, an enclosing owner's parameters, a
    /// navigated cycle and two chained cycles: the outcome, schedule, checkpoint sequence, frames, part work and static work
    /// are the copied seeds', every summary keeps its content, reference order and part structure, and the first pass keeps
    /// fewer entries through ordered holders.
    /// </summary>
    [Theory]
    [InlineData("paths")]
    [InlineData("paths-reversed")]
    [InlineData("escaping-before")]
    [InlineData("escaping-after")]
    [InlineData("external-path")]
    [InlineData("branched-reversed")]
    [InlineData("readers-reversed")]
    [InlineData("owner-reversed")]
    [InlineData("navigated-reversed")]
    [InlineData("two-cycles-reversed")]
    public void ReferenceBearingFirstPasses_KeepTheCopiedSeeds(string shape)
    {
        foreach (var k in new[] { 16, 48 })
        {
            var (held, copied) = AssertSameOutcome(ShapeSource(shape, k));
            if (k == 48)
            {
                Assert.InRange(held.Observations.SummaryMemberOrderedHolders, 10, long.MaxValue);
                Assert.InRange(held.Observations.SummaryMemberExpansionEntries, 0, copied.Observations.SummaryMemberExpansionEntries - 1);
            }

            output.WriteLine($"{shape} K={k}: expansion entries {copied.Observations.SummaryMemberExpansionEntries} -> "
                + $"{held.Observations.SummaryMemberExpansionEntries}, ordered holders {held.Observations.SummaryMemberOrderedHolders}, "
                + $"ordered folds {held.Observations.SummaryMemberOrderedFolds} ({held.Observations.SummaryMemberOrderedFoldEntries} entries)");
        }
    }

    // ── The change test ─────────────────────────────────────────────────────

    /// <summary>
    /// The reversed single-predecessor cycle: its first pass makes shares that hold the closing member's reference, and in the
    /// copied seeds the second pass's change test folded each of them, K² / 2 entries. Each replaced share's requirement bound
    /// now proves the change without folding it, and no seed that stays holds one, so none is folded later either. In source
    /// order the shares are reference-free and the reference-free test decides as before.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SinglePredecessorCycle_TellsReplacedSharesWithoutFolding(bool reversed)
    {
        foreach (var k in new[] { 32, 96 })
        {
            var (held, _) = AssertSameOutcome(SinglePredecessorCycle(k, reversed));
            if (reversed)
                Assert.InRange(held.Observations.SummaryMemberChangeTestsWithoutFold, k - 20, k);
            else
                Assert.Equal(0, held.Observations.SummaryMemberChangeTestsWithoutFold);
            Assert.Equal(0, held.Observations.SummaryMemberDeferredChangeTestFolds);
            output.WriteLine($"reversed={reversed} K={k}: change tests without fold {held.Observations.SummaryMemberChangeTestsWithoutFold}");
        }
    }

    /// <summary>
    /// A second pass that stops early leaves the later members' first-pass shares in place, and those hold, through the
    /// copy of a small share's own sets, seeds the change test replaced without folding. The copied change test folded those
    /// seeds, and the readers navigate the later members part by part, so their part structure is observable: the component
    /// folds them when it has converged. Settlement part work, frames, static work and every published part structure are the
    /// copied seeds'.
    /// </summary>
    [Fact]
    public void AnEarlyStoppingSecondPass_FoldsTheReplacedSeedsAStayingSeedHolds()
    {
        var source = EarlyStoppingBlockCycle(k: 24, period: 18, path: 6);
        var (held, _) = AssertSameOutcome(source);
        Assert.InRange(held.Observations.SummaryMemberChangeTestsWithoutFold, 1, long.MaxValue);
        Assert.InRange(held.Observations.SummaryMemberDeferredChangeTestFolds, 1, held.Observations.SummaryMemberChangeTestsWithoutFold);
        output.WriteLine($"change tests without fold {held.Observations.SummaryMemberChangeTestsWithoutFold}, deferred folds "
            + $"{held.Observations.SummaryMemberDeferredChangeTestFolds} ({held.Observations.SummaryMemberDeferredChangeTestFoldEntries} entries)");
    }

    /// <summary>
    /// ALIASING. A share that is the one seed it reads (<c>M26 = M10</c>) makes one seed object the seed of two members. When
    /// one member's change test replaces that seed, it is still the other member's seed, so the change test folds it as the
    /// copied change test does: left unfolded, the alias would publish a held seed where the copied seeds publish a flat
    /// one, with the same frames and static work. Program 6,811 of the cycle-dense levels of MIXED-CYCLE SCHEDULE (nested
    /// owners, shadowing blocks, self paths, detached readers).
    /// </summary>
    [Fact]
    public void AReplacedSeedAnotherMemberAliases_IsFoldedAsTheCopiedChangeTestFoldsIt()
    {
        var (held, _) = AssertSameOutcome(AliasedCycle);
        Assert.InRange(held.Observations.SummaryMemberOrderedHolders, 1, long.MaxValue);
        Assert.Equal(0, held.Observations.SummaryMemberChangeTestsWithoutFold);
    }

    private const string AliasedCycle = """
        F(p1, p2, p3, p4, p5, p6, p7, p8, p9) = {
          G(p1, p2, p3, p4, p5, p6) = {
            Lib = {
              public X = p8 + 1
              public Y = 2
              public W(a) = a + p2
              public V = X + Y
              public U = 7
            }
            N(z) = z + p9
            M1 = M10 + Lib.V
            public M2 = M1 + M1 + p3
            public M3 = M21 + M10 + M24
            M4 = p1 + M1
            public M5 = M3 + Lib.X + p4 + M2
            M6 = {
              M2 = 7
              M26 + p8 + M2
            }
            M7 = p2
            public M8 = {
              M6 = 6
              F.G.M11 + Lib.V + M6 + M6
            }
            public M9 = Lib.Y + M8 + M8 + M3
            public M10 = Lib.W(1) + M9
            public M11 = Lib.V + p7 + p1
            M12 = M21 + M11 + p3
            public M13 = M12 + p3 + Lib.W(1)
            public M14 = M13 + M17 + Lib.X + p4
            public M15 = p2 + M20
            M16 = M1 + M14
            public M17 = M16 + M16 + p9
            M18 = M17 + p2
            M19 = Lib.V + p5
            M20 = p4 + M10 + M19 + M13
            public M21 = F.G.M21 + M20 + Lib.X
            M22 = M9 + M20
            M23 = p9 + p2
            M24 = M22 + F.G.M7
            M25 = M19 + M8
            public M26 = M10
            M14 + M22 + M10
          }
          G(7, 8, 8, 6, 1, 1)
        }
        Q1 = F.G.M4
        Q2 = F.G.M15
        F(5, 1, 3, 7, 5, 1, 1, 5, 4)
        """;

    /// <summary>
    /// A first-pass ordered holder that no later evaluation replaces stays the member's seed when its component converges,
    /// and a navigated reader settles it part by part: the converged component folds it, so the published seeds, part work,
    /// frames and static work are the copied seeds'. The fifth generated single-predecessor cycle of the test below (a
    /// reversed cycle in a block, paths on four members, navigated readers).
    /// </summary>
    [Fact]
    public void AnOrderedHolderThatStays_IsFoldedWhenItsComponentConverges()
    {
        var (held, _) = AssertSameOutcome(NarrowCycles(5, seed: 131).Last());
        Assert.InRange(held.Observations.SummaryMemberOrderedHolders, 1, long.MaxValue);
        Assert.InRange(held.Observations.SummaryMemberOrderedFolds, 1, held.Observations.SummaryMemberOrderedHolders);
    }

    // ── Controls ────────────────────────────────────────────────────────────

    /// <summary>
    /// Levels whose cycles hold no reference-bearing first pass, or that have no mixed cycle, are unchanged: an acyclic
    /// two-predecessor chain with a path and its readers, a pure-union cycle, members that read themselves, a member
    /// navigating its own owner, the chain whose cycle closes through a path, and the branched cycle in source order. Every
    /// counter, the checkpoint sequence, the static work and every summary are the copied seeds'.
    /// </summary>
    [Fact]
    public void LevelsWithoutAReferenceBearingFirstPass_AreUnchanged()
    {
        const int k = 40;
        var sources = new[]
        {
            Level(k, i => i == 1 ? "p1 + Lib.X" : Chain(i)),
            Level(k, i => i == 1 ? "p1 + Lib.X" : Chain(i), row: $"R{k}",
                extra: string.Concat(Enumerable.Range(1, k).Select(i => $"R{i} = P{i} + Lib.Y\n"))),
            Level(k, i => i == 1 ? $"P{k} + p1" : Chain(i)),
            Level(k, i => i == 1 ? "P1 + p1 + Lib.X" : $"P{i} + P{i - 1} + p{i}", row: $"P{k}"),
            Level(k, i => i == 1 ? "p1" : Chain(i), row: "X", extra: $"X = F.P{k}\n"),
            Level(k, i => i == 1 ? "B.X + p1 + Lib.X" : Chain(i), extra: $"B = {{\npublic X = 1\nP{k}\n}}\n"),
            Level(k, i => (i == 1 ? Closing(k) : Chain(i)) + (i % 8 == 0 && i + 4 <= k ? $" + P{i + 4}" : "")),
        };
        foreach (var source in sources)
        {
            var held = Parse(source);
            var copied = Copied(() => Parse(source));
            Assert.Equal("", held.Diagnostics);
            Assert.Equal(copied.Metadata, held.Metadata);
            Assert.Equal(copied.Sequence, held.Sequence);
            var (h, c) = (held.Observations, copied.Observations);
            Assert.Equal(0, h.SummaryMemberOrderedHolders);
            Assert.Equal(0, h.SummaryMemberChangeTestsWithoutFold);
            Assert.Equal(c.SummaryMemberEvaluations, h.SummaryMemberEvaluations);
            Assert.Equal(c.SummaryMemberReaderNotifications, h.SummaryMemberReaderNotifications);
            Assert.Equal(c.SummaryMemberExpansions, h.SummaryMemberExpansions);
            Assert.Equal(c.SummaryMemberExpansionEntries, h.SummaryMemberExpansionEntries);
            Assert.Equal(c.SummaryMemberExpansionHeldParts, h.SummaryMemberExpansionHeldParts);
            Assert.Equal(c.MemberBudgetFoldEntries, h.MemberBudgetFoldEntries);
            Assert.Equal(c.SummaryMemberCompleteSeeds, h.SummaryMemberCompleteSeeds);
            Assert.Equal(c.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel),
                h.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel));
            Assert.Equal(c.RequiredAncestorSettlementFrames, h.RequiredAncestorSettlementFrames);
            Assert.Equal(c.SettlementSeedPartWork, h.SettlementSeedPartWork);
            Assert.Equal(c.RequiredAncestorLevelEvaluations, h.RequiredAncestorLevelEvaluations);
            Assert.Equal(Copied(() => Work(source)), Work(source));
            foreach (var (where, left, right) in Summaries(source))
                AssertSameContentOrderAndShape(left, right, where);
        }
    }

    // ── Generated levels ────────────────────────────────────────────────────

    /// <summary>
    /// Wide levels dense in mixed cycles whose members carry references (two-predecessor chains, chords, third reads,
    /// closing members, library paths, escaping root names before or after the reads, self paths, external block paths,
    /// opened names, shadowing blocks, enclosing owners, readers, all three declaration orders), and single-predecessor
    /// cycles in a block or at the level, navigated or read by path, closed at varying members, with early stops: every
    /// program's diagnostics, metadata, evaluations, frames, part work, summary checkpoints and static work are the copied
    /// seeds', and every summary keeps its content, reference order and part structure.
    /// </summary>
    [Fact]
    public void GeneratedReferenceBearingLevels_KeepTheCopiedSeeds()
    {
        long compared = 0, holding = 0, withoutFold = 0, deferred = 0;
        foreach (var source in WideCyclicLevels(120, seed: 71).Concat(NarrowCycles(120, seed: 131)))
        {
            var held = Parse(source);
            var copied = Copied(() => Parse(source));
            Assert.Equal(copied.Diagnostics, held.Diagnostics);
            Assert.Equal(copied.Metadata, held.Metadata);
            var (h, c) = (held.Observations, copied.Observations);
            Assert.Equal(c.SummaryMemberEvaluations, h.SummaryMemberEvaluations);
            Assert.Equal(c.SummaryMemberReaderNotifications, h.SummaryMemberReaderNotifications);
            Assert.Equal(c.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel),
                h.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel));
            Assert.Equal(c.RequiredAncestorSettlementFrames, h.RequiredAncestorSettlementFrames);
            Assert.Equal(c.SettlementSeedPartWork, h.SettlementSeedPartWork);
            if (h.SummaryMemberOrderedHolders > 0) holding++;
            if (h.SummaryMemberChangeTestsWithoutFold > 0) withoutFold++;
            if (h.SummaryMemberDeferredChangeTestFolds > 0) deferred++;
            if (held.Diagnostics.Length != 0)
                continue;
            Assert.Equal(Copied(() => Work(source)), Work(source));
            foreach (var (where, left, right) in Summaries(source))
            {
                compared++;
                AssertSameContentOrderAndShape(left, right, where + "\n" + source);
            }
        }

        output.WriteLine($"{compared} summaries compared; {holding} programs made ordered holders, {withoutFold} told a replaced "
            + $"seed without folding it, {deferred} folded one at convergence");
        Assert.InRange(holding, 60, int.MaxValue);
        Assert.InRange(withoutFold, 1, int.MaxValue);
    }

    /// <summary>Seeded wide levels dense in mixed cycles whose members carry references (see the test above).</summary>
    internal static IEnumerable<string> WideCyclicLevels(int count, int seed)
    {
        var random = new Random(seed);
        for (var n = 0; n < count; n++)
        {
            var parameterCount = 4 + random.Next(36);
            var parameters = Enumerable.Range(1, parameterCount).Select(i => $"p{i}").ToArray();
            var members = 10 + random.Next(50);
            var order = random.Next(3);
            var pathRate = random.Next(4) == 0 ? 0.0 : random.NextDouble() * 0.35;
            var escapeRate = random.Next(3) == 0 ? 0.0 : random.NextDouble() * 0.25;
            var chordRate = random.Next(3) == 0 ? 0.0 : random.NextDouble() * 0.2;
            var thirdRate = random.Next(3) == 0 ? 0.0 : random.NextDouble() * 0.3;
            var extraParameterRate = random.NextDouble() * 0.4;
            var selfPathRate = random.Next(5) == 0 ? 0.1 : 0.0;
            var externalRate = random.Next(4) == 0 ? 0.15 : 0.0;
            var closing = 1 + random.Next(3);
            var nested = random.Next(4) == 0;
            var readers = random.Next(3) == 0;
            var opened = random.Next(6) == 0;
            var shadow = random.Next(8) == 0;
            var owner = nested ? "F.G" : "F";
            string Pick(params string[] items) => items[random.Next(items.Length)];

            string Member(int i)
            {
                var own = new List<string> { parameters[(i - 1) % parameterCount] };
                if (random.NextDouble() < extraParameterRate) own.Add(Pick(parameters));
                if (nested && random.Next(3) == 0) own.Add($"q{1 + random.Next(4)}");
                var reads = new List<string>();
                if (i > 1) reads.Add($"M{i - 1}");
                if (i > 2 && random.Next(6) != 0) reads.Add($"M{i - 2}");
                if (i > 3 && random.NextDouble() < thirdRate) reads.Add($"M{i - 3 - random.Next(Math.Min(4, i - 3))}");
                if (random.NextDouble() < chordRate) reads.Add($"M{1 + random.Next(members)}");
                if (random.Next(3) == 0) reads.Reverse();
                if (i <= closing) reads.Add($"M{members - random.Next(Math.Min(3, members - 1))}");
                var references = new List<string>();
                if (random.NextDouble() < pathRate) references.Add(Pick("Lib.X", "Lib.Y", "Lib.Z", "Lib.V", "Lib.W(1)"));
                if (random.NextDouble() < escapeRate) references.Add(Pick("G0", "H0"));
                if (random.NextDouble() < selfPathRate) references.Add($"{owner}.M{1 + random.Next(members)}");
                if (random.NextDouble() < externalRate) references.Add("E.V");
                if (opened && random.Next(8) == 0) references.Add(Pick("Z", "Z2"));
                var referencesFirst = references.Count > 0 && random.Next(3) == 0;
                var atoms = new List<string>();
                if (referencesFirst) atoms.AddRange(references);
                if (random.Next(5) != 0) { atoms.AddRange(reads); atoms.AddRange(own); }
                else { atoms.AddRange(own); atoms.AddRange(reads); }
                if (!referencesFirst) atoms.AddRange(references);
                if (shadow && i > 3 && random.Next(10) == 0)
                    return $"M{i} = {{\nM{i - 1} = {random.Next(9) + 1}\n{string.Join(" + ", atoms)} + M{i - 1}\n}}";
                return $"M{i} = {string.Join(" + ", atoms)}";
            }

            var lines = new List<string>();
            if (opened) lines.Add("open O");
            lines.AddRange(["Lib = {", $"public X = {Pick(parameters)} + 1", "public Y = 2", "public Z = 3",
                $"public W(a) = a + {Pick([.. parameters, "3"])}", "public V = X + Y", "}"]);
            if (opened) lines.AddRange(["O = {", $"public Z = {Pick(parameters)}", "public Z2 = 5", "}"]);
            if (externalRate > 0) lines.Add("E = { public V = 1 }");
            var declarations = Enumerable.Range(1, members).Select(Member).ToList();
            if (order == 1) declarations.Reverse();
            else if (order == 2) declarations = [.. declarations.OrderBy(_ => random.Next())];
            lines.AddRange(declarations);
            if (readers)
                for (var i = 1; i <= members; i += 1 + random.Next(3))
                    lines.Add($"R{i} = M{i} + {Pick("Lib.Y", "Lib.X", "G0")}");
            lines.Add(readers ? $"R1 + M{members}" : $"M{1 + random.Next(members)} + Lib.X");
            var arguments = string.Join(", ", parameters.Select(_ => random.Next(9) + 1));
            var body = string.Join("\n", lines);
            var root = "G0 = 5\nH0 = 6\n";
            if (!nested)
            {
                yield return $"{root}F({string.Join(", ", parameters)}) = {{\n{body}\n}}\nF({arguments})\n";
                continue;
            }

            var program = new StringBuilder($"{root}F(q1, q2, q3, q4) = {{\nG({string.Join(", ", parameters)}) = {{\n{body}\n}}\nG({arguments})\n}}\n");
            if (random.Next(2) == 0)
                program.Append($"Q1 = F.G.M{1 + random.Next(members)}\n");
            yield return program.Append("F(1, 2, 3, 4)\n").ToString();
        }
    }

    /// <summary>Seeded single-predecessor mixed cycles in a block or at the level, mostly in reversed order (see above).</summary>
    internal static IEnumerable<string> NarrowCycles(int count, int seed)
    {
        var random = new Random(seed);
        for (var n = 0; n < count; n++)
        {
            var parameterCount = 4 + random.Next(30);
            var parameters = Enumerable.Range(1, parameterCount).Select(i => $"p{i}").ToArray();
            var members = 9 + random.Next(60);
            var inBlock = random.Next(2) == 0;
            var order = random.Next(10) < 7 ? 1 : random.Next(3);
            var pathRate = random.NextDouble() * 0.2;
            var twoRate = random.Next(6) == 0 ? random.NextDouble() * 0.3 : 0.0;
            var extraRate = random.NextDouble() * 0.6;
            var close = 1 + random.Next(members);
            var secondClose = random.Next(4) == 0 ? 2 + random.Next(members - 1) : 0;
            string Pick(params string[] items) => items[random.Next(items.Length)];
            var lines = new List<string> { "Lib = {", $"public X = {Pick(parameters)} + 1", "public Y = 2", "}", "Q = { public Z = 3 }" };
            var declarations = new List<string>();
            var visibility = inBlock ? "public " : "";
            for (var i = 1; i <= members; i++)
            {
                var atoms = new List<string> { i == 1 ? $"M{close}" : $"M{i - 1}" };
                if (i > 2 && random.NextDouble() < twoRate) atoms.Add($"M{i - 2}");
                if (i == secondClose) atoms.Add($"M{members}");
                atoms.Add(Pick(parameters));
                if (random.NextDouble() < extraRate) atoms.Add(Pick(parameters));
                if (random.NextDouble() < pathRate || i == 1 && random.Next(10) < 7) atoms.Add(Pick("Q.Z", "Lib.X", "Lib.Y"));
                if (random.Next(5) == 0) atoms.Reverse();
                declarations.Add($"{visibility}M{i} = {string.Join(" + ", atoms)}");
            }

            if (order == 1) declarations.Reverse();
            else if (order == 2) declarations = [.. declarations.OrderBy(_ => random.Next())];
            var readerLines = new List<string>();
            var readers = new List<string>();
            for (var i = 1; i <= members; i++)
            {
                if (random.Next(3) == 0) continue;
                readers.Add($"R{i}");
                readerLines.Add(inBlock ? $"R{i} = C.M{i}" : $"R{i} = M{i} + {Pick("Lib.Y", "Q.Z", "1")}");
            }

            if (inBlock)
            {
                lines.Add("C = {");
                lines.AddRange(declarations);
                lines.Add("}");
            }
            else
                lines.AddRange(declarations);
            lines.AddRange(readerLines);
            lines.AddRange(readers.Count == 0
                ? [inBlock ? "C.M1" : "M1"]
                : Enumerable.Range(0, 1 + random.Next(4)).Select(_ => readers[random.Next(readers.Count)]).Distinct());
            var arguments = string.Join(", ", parameters.Select(_ => random.Next(9) + 1));
            yield return $"F({string.Join(", ", parameters)}) = {{\n{string.Join("\n", lines)}\n}}\nF({arguments})\n";
        }
    }

    // ── Cancellation and admission ──────────────────────────────────────────

    /// <summary>
    /// CANCELLATION: an expansion that holds instead of copying takes the copied expansion's summary-channel checkpoints and
    /// context uses, and a fold of an ordered holder observes the token. A token cancelled at the checkpoint the first
    /// evaluation after the first ordered holder takes escapes with that token, records nothing after it, and leaves
    /// nothing behind: a fresh parse publishes the uncancelled metadata.
    /// </summary>
    [Fact]
    public void CancellationInAFirstPassThatHolds_EscapesWithTheToken_AndLeavesNothingBehind()
    {
        const int k = 64;
        var source = MixedCycleMemberScheduleTests.ClosedChain(k, reversed: true);
        var uncancelled = Parse(source);
        long target = -1;
        FrontEndTraversalObservations probe = null!;
        probe = new FrontEndTraversalObservations
        {
            CheckpointReached = (kind, ordinal) =>
            {
                if (kind == FrontEndCancellationCheckpoint.SummaryChannel && target < 0 && probe.SummaryMemberOrderedHolders == 1)
                    target = ordinal;
            },
        };
        Parser.ParseObserved(source, options: null, probe);
        Assert.InRange(target, 1, uncancelled.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel));

        using var cancellation = new CancellationTokenSource();
        long holdersAtCancel = -1;
        FrontEndTraversalObservations observations = null!;
        observations = new FrontEndTraversalObservations
        {
            CheckpointReached = (kind, ordinal) =>
            {
                if (kind != FrontEndCancellationCheckpoint.SummaryChannel || ordinal != target || cancellation.IsCancellationRequested)
                    return;
                holdersAtCancel = observations.SummaryMemberOrderedHolders;
                cancellation.Cancel();
            },
        };

        var error = Assert.Throws<OperationCanceledException>(() => Parser.ParseObserved(
            source, new RunOptions { SourceProcessingCancellationToken = cancellation.Token }, observations));

        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal(target, observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel));
        Assert.Equal(1, holdersAtCancel);
        Assert.Equal(1, observations.SummaryMemberOrderedHolders);
        Assert.Equal(uncancelled.Metadata, Parse(source).Metadata);
    }

    /// <summary>
    /// The work bound is resource policy (SETTLEMENT FRAME CHARGE): the reversed closed chain, the reversed path-bearing
    /// cycle, the reversed single-predecessor cycle and the early-stopping block cycle are admitted at exactly the copied
    /// seeds' charge and refused one unit below it.
    /// </summary>
    [Theory]
    [InlineData("reversed")]
    [InlineData("paths-reversed")]
    [InlineData("single-predecessor-reversed")]
    [InlineData("early-stopping")]
    public void TheWorkBound_AdmitsAtTheCopiedCharge_AndRefusesOneUnitBelow(string shape)
    {
        var source = shape switch
        {
            "reversed" => MixedCycleMemberScheduleTests.ClosedChain(48, reversed: true),
            "single-predecessor-reversed" => SinglePredecessorCycle(48, reversed: true),
            "early-stopping" => EarlyStoppingBlockCycle(k: 24, period: 18, path: 6),
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
