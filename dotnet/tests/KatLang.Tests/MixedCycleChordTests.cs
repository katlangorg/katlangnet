using System.Text;
using Xunit.Abstractions;
using static KatLang.PropertyDependencyGraphBuilder;

namespace KatLang.Tests;

/// <summary>
/// CHORDED CYCLES (November 28 2026; C# exposure implementation only — no classification, requirement, diagnostic kind,
/// value or Lean rule changes). A chord <c>P(i) = … + P(i + 4)</c> inside a mixed cycle makes the ranked schedule evaluate
/// <c>P(i)</c> … <c>P(i + 4)</c> again right after the first pass reaches <c>P(i + 4)</c>. Those re-evaluations copied
/// every seed they read into a new flat seed, and their change tests folded each first-pass holder they replaced or kept,
/// so the branched cycle of K = 2,000 allocated 222.5 MB in source order and 259.6 MB reversed. The member solve now
/// <list type="bullet">
/// <item>tells a replaced holder that carries no reference from its successor by its requirement bound, or by collecting its
/// requirements into scratch sets, without folding it; a fold budget that later reads such a holder folds it first, so every
/// budget reads the shape the copied change test gave it;</item>
/// <item>makes a kept holder the flat seed it folds to by taking its equal successor's requirement sets;</item>
/// <item>records what the evaluation equal to a kept seed read, which keeps the requirement bounds of the seeds that hold
/// it tight;</item>
/// <item>gives a re-evaluation whose copied union equals one flat seed it reads (that seed provably contains every other
/// one, and holds the base's own requirements) a new seed over that seed's sets.</item>
/// </list>
/// Oracles: the solve as it was before (<see cref="PropertyDependencyGraphBuilder.KeptAndReplacedHoldersFoldedForTesting"/>)
/// and the copied seeds (<see cref="PropertyDependencyGraphBuilder.ReferenceBearingSeedsCopiedForTesting"/>), compared by
/// every member's content with its references IN ORDER and its whole part structure, published metadata, diagnostics, the
/// checkpoint sequence, static work, settlement frames and deterministic counters, never time.
/// </summary>
public sealed class MixedCycleChordTests(ITestOutputHelper output)
{
    // ── Harness ─────────────────────────────────────────────────────────────

    private enum Oracle
    {
        /// <summary>The member solve before CHORDED CYCLES.</summary>
        AsBefore,

        /// <summary>The copied seeds of ORDERED HOLDING's oracle.</summary>
        Copied,
    }

    private static T With<T>(Oracle oracle, Func<T> work)
    {
        var seam = oracle == Oracle.AsBefore ? KeptAndReplacedHoldersFoldedForTesting : ReferenceBearingSeedsCopiedForTesting;
        var previous = seam.Value;
        seam.Value = true;
        try { return work(); }
        finally { seam.Value = previous; }
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

    /// <summary>Every summary of <paramref name="source"/> in production and under <paramref name="oracle"/>, paired.</summary>
    private static List<(string Where, SummarySeed Production, SummarySeed Oracle)> Summaries(string source, Oracle oracle)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var production = Memo(root);
        var expected = With(oracle, () => Memo(root));
        var pairs = new List<(string, SummarySeed, SummarySeed)>();
        void Add(string where, AlgorithmSummary left, AlgorithmSummary right)
        {
            pairs.Add((where + " output", left.OutputSeed, right.OutputSeed));
            Assert.Equal(right.MemberSeeds.Count, left.MemberSeeds.Count);
            foreach (var (name, seed) in right.MemberSeeds)
                pairs.Add((where + " member " + name, left.MemberSeeds[name], seed));
        }

        Assert.Equal(expected.IndependentAlgorithmSummaries?.Count ?? 0, production.IndependentAlgorithmSummaries?.Count ?? 0);
        Assert.Equal(expected.ContextualAlgorithmSummaries?.Count ?? 0, production.ContextualAlgorithmSummaries?.Count ?? 0);
        foreach (var (algorithm, summary) in expected.IndependentAlgorithmSummaries ?? [])
            Add("independent", production.IndependentAlgorithmSummaries![algorithm], summary);
        foreach (var (key, summary) in expected.ContextualAlgorithmSummaries ?? [])
            Add("contextual", production.ContextualAlgorithmSummaries![key], summary);
        return pairs;
    }

    /// <summary>
    /// Two seeds hold the same content — the same required names, visible names and owner-qualified parameters, and the
    /// same references, each with its origin, path, bound owners and selection, in the SAME order — and the same whole
    /// part structure.
    /// </summary>
    private static void AssertSameContentOrderAndShape(SummarySeed production, SummarySeed expected, string where)
    {
        Assert.True(MixedCycleOrderedHoldingTests.Structure(expected) == MixedCycleOrderedHoldingTests.Structure(production),
            $"{where}: {MixedCycleOrderedHoldingTests.Structure(expected)} -> {MixedCycleOrderedHoldingTests.Structure(production)}");
        production = production.Clone();
        expected = expected.Clone();
        Assert.True(expected.RequiredAncestorOwnedParameterNames.SetEquals(production.RequiredAncestorOwnedParameterNames), where);
        Assert.True(expected.VisiblePropertyDependencyNames.SetEquals(production.VisiblePropertyDependencyNames), where);
        Assert.True(expected.OwnerQualifiedParameters.SetEquals(production.OwnerQualifiedParameters), where);
        static (string, object?, object?, bool, PendingSelection?) Identity(SummaryReference reference)
            => reference is PendingReference anchored
                ? (anchored.ContentKey, anchored.Origin.Facts, anchored.Origin.Key, anchored.OpenPath, anchored.Selection)
                : (reference.ContentKey, null, null, false, null);
        Assert.True(expected.PendingReferences.Select(Identity).SequenceEqual(production.PendingReferences.Select(Identity)), where);
    }

    /// <summary>
    /// Production agrees with both oracles on the outcome, the schedule, the checkpoint sequence, the settlement frames,
    /// part work, level evaluations and navigation, the static work, and every summary in content, reference order and part
    /// structure; with the solve as before it also agrees on what the fold budgets of reference-free expansions keep, the
    /// small members they copy, complete seeds and shares.
    /// </summary>
    private static (Observed Production, Observed AsBefore) AssertSameOutcome(string source)
    {
        var production = Parse(source);
        Assert.Equal("", production.Diagnostics);
        Observed? asBefore = null;
        var work = Work(source);
        foreach (var oracle in new[] { Oracle.AsBefore, Oracle.Copied })
        {
            var expected = With(oracle, () => Parse(source));
            asBefore ??= expected;
            Assert.Equal(expected.Diagnostics, production.Diagnostics);
            Assert.Equal(expected.Metadata, production.Metadata);
            Assert.Equal(expected.Sequence, production.Sequence);
            var (p, e) = (production.Observations, expected.Observations);
            Assert.Equal(e.SummaryMemberEvaluations, p.SummaryMemberEvaluations);
            Assert.Equal(e.SummaryMemberReaderNotifications, p.SummaryMemberReaderNotifications);
            Assert.Equal(e.SummaryMemberCompleteSeeds, p.SummaryMemberCompleteSeeds);
            Assert.Equal(e.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel),
                p.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel));
            Assert.Equal(e.RequiredAncestorSettlementFrames, p.RequiredAncestorSettlementFrames);
            Assert.Equal(e.SettlementSeedPartWork, p.SettlementSeedPartWork);
            Assert.Equal(e.RequiredAncestorLevelEvaluations, p.RequiredAncestorLevelEvaluations);
            Assert.Equal(e.MemberNavigationFolds, p.MemberNavigationFolds);
            Assert.Equal(e.MemberNavigationEntriesRead, p.MemberNavigationEntriesRead);
            Assert.Equal(With(oracle, () => Work(source)), work);
            Assert.Equal(0, e.SummaryMemberDominatingReads);
            Assert.Equal(0, e.SummaryMemberKeptHoldersWithoutFold);
            Assert.Equal(0, e.SummaryMemberDeferredFoldsOnBudgetRead);
            foreach (var (where, left, right) in Summaries(source, oracle))
                AssertSameContentOrderAndShape(left, right, where);
        }

        // The parts that reference-free (MEMBERS BY REFERENCE) expansions keep under their fold budgets, the small members
        // they copy, and the shares: an ordered holder stands for its flat seed and is folded when its component converges,
        // so where its own fold budget folds it (tighter requirement bounds leave more ordered holders unfolded) is no
        // decision the copied seeds see.
        var (h, b) = (production.Observations, asBefore!.Observations);
        Assert.Equal(b.SummaryMemberExpansionHeldParts - b.SummaryMemberOrderedHolderParts,
            h.SummaryMemberExpansionHeldParts - h.SummaryMemberOrderedHolderParts);
        Assert.Equal(b.MemberEntriesCopied, h.MemberEntriesCopied);
        Assert.Equal(b.SummaryMemberShareFolds, h.SummaryMemberShareFolds);
        Assert.Equal(b.SummaryMemberPathShares, h.SummaryMemberPathShares);
        return (production, asBefore);
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

    /// <summary>The closed two-predecessor chain with a chord at every <paramref name="every"/>th member to P(i + reach).</summary>
    private static string Chorded(int k, bool reversed = false, int every = 8, int reach = 4, Func<int, string>? suffix = null)
        => Level(k, i => (i == 1 ? Closing(k) : Chain(i)) + (i % every == 0 && i + reach <= k ? $" + P{i + reach}" : "")
            + (suffix?.Invoke(i) ?? ""), reversed: reversed);

    private static int Chords(int k, int every = 8, int reach = 4)
        => Enumerable.Range(1, k).Count(i => i % every == 0 && i + reach <= k);

    /// <summary>
    /// DISTINCT HOLDERS: <c>P(i)</c> reads <c>P(i − 1)</c> and <c>P(i − 3)</c>, so no seed a chord re-evaluation reads was
    /// produced by an evaluation that read the other, and no read provably contains the others.
    /// </summary>
    private static string ChordedDistinct(int k, bool reversed = false)
        => Level(k, i => (i == 1 ? Closing(k) : i <= 3 ? $"P{i - 1} + p{i}" : $"P{i - 1} + P{i - 3} + p{i}")
            + (i % 8 == 0 && i + 4 <= k ? $" + P{i + 4}" : ""), reversed: reversed);

    // ── Chorded cycles ──────────────────────────────────────────────────────

    /// <summary>
    /// The branched cycle (a chord every 8th member to <c>P(i + 4)</c>) in both source orders. Each chord re-evaluates
    /// five members: the first copies as before; the next four read a flat seed that provably contains every other seed they
    /// read and take seeds over its sets; four replaced holders are told from their successors without folding, and the
    /// fifth member's first-pass holder stays and takes its successor's requirement sets. The outcome, schedule, checkpoint
    /// sequence, frames, part work, static work and every summary are the oracles', and so is every fold-budget decision
    /// of the solve as before; the expansions keep a fifth of the entries, and in reversed order the first pass no longer
    /// folds the ordered holders whose bounds the chords loosened.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ChordedCycle_KeepsTheSeedsAsBefore_WithoutRefoldingTheChordWidths(bool reversed)
    {
        foreach (var k in new[] { 32, 64, 128 })
        {
            var chords = Chords(k);
            var (held, asBefore) = AssertSameOutcome(Chorded(k, reversed));
            var (h, b) = (held.Observations, asBefore.Observations);
            output.WriteLine($"reversed={reversed} K={k} chords={chords}: dominating {h.SummaryMemberDominatingReads}, kept "
                + $"{h.SummaryMemberKeptHoldersWithoutFold}, without fold {h.SummaryMemberChangeTestsWithoutFold}");
            // Four dominating reads per chord; one kept holder per chord (the first chord's in reversed order is flat).
            Assert.Equal(4L * chords, h.SummaryMemberDominatingReads);
            Assert.Equal(reversed ? chords - 1 : chords, h.SummaryMemberKeptHoldersWithoutFold);
            // Replaced first-pass holders: plain ones in source order (Decide; the first two chords replace small flat seeds
            // too); ordered ones in reversed order, which the ordered change test leaves as they are.
            if (!reversed)
                Assert.InRange(h.SummaryMemberChangeTestsWithoutFold, 4L * chords - 5, 4L * chords);
            Assert.Equal(0, h.SummaryMemberDeferredChangeTestFolds);
            if (k == 128)
            {
                Assert.InRange(h.SummaryMemberExpansionEntries, 0, b.SummaryMemberExpansionEntries / 3);
                if (reversed)
                {
                    Assert.InRange(b.SummaryMemberOrderedFolds, 20, long.MaxValue);
                    Assert.Equal(1, h.SummaryMemberOrderedFolds);
                }
            }

            output.WriteLine($"reversed={reversed} K={k}: expansion entries {b.SummaryMemberExpansionEntries} -> {h.SummaryMemberExpansionEntries}, "
                + $"dominating reads {h.SummaryMemberDominatingReads}, kept {h.SummaryMemberKeptHoldersWithoutFold}, "
                + $"replaced without fold {b.SummaryMemberChangeTestsWithoutFold} -> {h.SummaryMemberChangeTestsWithoutFold}, "
                + $"ordered folds {b.SummaryMemberOrderedFolds} -> {h.SummaryMemberOrderedFolds}");
        }
    }

    /// <summary>
    /// Denser and longer chords, chords in a cycle whose members carry paths, and DISTINCT HOLDERS (no read provably contains
    /// the others, so every chord re-evaluation copies as before) in both orders: the oracles' outcomes and summaries.
    /// </summary>
    [Theory]
    [InlineData("dense")]
    [InlineData("long")]
    [InlineData("paths")]
    [InlineData("paths-reversed")]
    [InlineData("distinct")]
    [InlineData("distinct-reversed")]
    public void OtherChordShapes_KeepTheSeedsAsBefore(string shape)
    {
        const int k = 96;
        var source = shape switch
        {
            "dense" => Chorded(k, every: 4, reach: 6),
            "long" => Chorded(k, every: 16, reach: 12),
            "paths" => Chorded(k, suffix: i => i % 4 == 0 ? $" + Lib.{(char)('X' + i % 3)}" : ""),
            "paths-reversed" => Chorded(k, reversed: true, suffix: i => i % 4 == 0 ? $" + Lib.{(char)('X' + i % 3)}" : ""),
            "distinct" => ChordedDistinct(k),
            "distinct-reversed" => ChordedDistinct(k, reversed: true),
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        };
        var (held, asBefore) = AssertSameOutcome(source);
        var (h, b) = (held.Observations, asBefore.Observations);
        Assert.InRange(h.SummaryMemberExpansionEntries, 0, b.SummaryMemberExpansionEntries);
        output.WriteLine($"{shape}: expansion entries {b.SummaryMemberExpansionEntries} -> {h.SummaryMemberExpansionEntries}, "
            + $"dominating reads {h.SummaryMemberDominatingReads}, kept {h.SummaryMemberKeptHoldersWithoutFold}, "
            + $"replaced without fold {b.SummaryMemberChangeTestsWithoutFold} -> {h.SummaryMemberChangeTestsWithoutFold}");
    }

    /// <summary>
    /// A kept holder takes its successor's requirement sets and a dominating read's seed shares the read's sets, so the
    /// members of the chorded cycle keep the same distinct seeds and no more set entries than the solve as before (every
    /// published seed is a complete one there, sharing one group of sets).
    /// </summary>
    [Fact]
    public void ChordedCycle_RetainsNoMoreThanBefore()
    {
        const int k = 96;
        foreach (var reversed in new[] { false, true })
        {
            var root = SourceProvenance.ParseValid(Chorded(k, reversed)).Root;
            IEnumerable<SummarySeed> Members(SummaryMemo memo)
            {
                var members = Assert.Single(AllSummaries(memo), summary => summary.MemberSeeds.ContainsKey("P1")).MemberSeeds;
                return Enumerable.Range(1, k).Select(i => members[$"P{i}"]);
            }

            var production = Retained(Members(Memo(root)));
            var asBefore = Retained(Members(With(Oracle.AsBefore, () => Memo(root))));
            Assert.Equal(asBefore.Seeds, production.Seeds);
            Assert.InRange(production.Entries, 0, asBefore.Entries);
        }
    }

    // ── The change test's fold-budget invariant ─────────────────────────────

    [Fact]
    public void ExactComparisonCountsDuplicateInputsAcrossDistinctParts()
    {
        var qualified = new OwnerQualifiedParameter("p", null);
        var holder = new SummarySeed(["outer"], ownerQualifiedParameters: [qualified]);
        holder.AbsorbReference(new SummarySeed(["outer"], ownerQualifiedParameters: [qualified]));
        HashSet<string> names = new(StringComparer.Ordinal);
        HashSet<OwnerQualifiedParameter> parameters = [];
        Assert.True(holder.CollectRequirements(names, parameters, new(ReferenceEqualityComparer.Instance), new(),
            referencesInOwnSet: false, out var entries, CancellationToken.None));
        Assert.Equal(4L, entries);
        Assert.Equal("outer", Assert.Single(names));
        Assert.Equal(qualified, Assert.Single(parameters));
        Assert.Single(holder.AbsorbedPartsWithoutFolding!);
    }

    /// <summary>
    /// THE FOLD BUDGET OF A REPLACED HOLDER. A fold budget reads the shape of each part it holds: a folded part counts its
    /// width, a holder its parts' budgets. The copied change test folded every replaced holder; left unfolded, a later first
    /// evaluation that holds a seed which holds one would take another budget and fold at other widths. Such a budget folds
    /// the replaced holder first. Program 2,317 of the generated chorded levels (seed 61, chords <c>M1 → M4, M14</c>,
    /// <c>M5 → M8</c>, <c>M13 → M15</c> under an enclosing owner): after its change test replaces a first-pass holder without
    /// folding it, a fold budget reads it. Every held part, budget fold and small-member copy is the solve's as before
    /// (without the fold first, the budget folds visit 119 entries instead of 115).
    /// </summary>
    [Fact]
    public void AFoldBudgetThatReadsAReplacedHolder_FoldsItFirst()
    {
        var (held, asBefore) = AssertSameOutcome(BudgetReadWitness);
        Assert.InRange(held.Observations.SummaryMemberDeferredFoldsOnBudgetRead, 1, long.MaxValue);
        Assert.InRange(held.Observations.SummaryMemberChangeTestsWithoutFold, 1, long.MaxValue);
        Assert.Equal(asBefore.Observations.MemberBudgetFoldEntries, held.Observations.MemberBudgetFoldEntries);
    }

    private const string BudgetReadWitness = """
        G0 = 5
        H0 = 6
        G(q1, q2, q3) = {
        F(p1, p2, p3, p4, p5, p6, p7, p8) = {
        Lib = {
        public X = p3 + 1
        public Y = 2
        public Z = 3
        public V = X + Y
        }
        M1 = p1 + q3 + M4 + M14 + G0
        M2 = M1 + M14 + p2 + q2
        M3 = M2 + M1 + p3 + p1
        M4 = M3 + M2 + p4 + p6 + p5 + p1 + p7 + p2 + p8
        M5 = M8 + M3 + M4 + p5
        M6 = M5 + M4 + M3 + p6 + p2 + p3 + p5 + p4 + p8 + p1 + q1
        M7 = M6 + M5 + M4 + p7
        M8 = p8 + p1 + q1 + M7 + M6 + M5
        M9 = p1 + p7 + p3 + p5 + M6 + M5 + M8
        M10 = M8 + M9 + p2 + q3
        M11 = M9 + M10 + p3 + p1
        M12 = p4 + M11 + M10
        M13 = M12 + M11 + M15 + p5
        M14 = M13 + M12 + p6
        M15 = M14 + M13 + p7
        M16 = M15 + M14 + p8
        M6 + Lib.X
        }
        F(3, 4, 8, 6, 9, 4, 4, 6)
        }
        G(1, 2, 3)
        """;

    /// <summary>
    /// A KEPT ORDERED HOLDER takes its successor's requirement sets but keeps its own references: they are the copied flat
    /// seed's, in the copied order, while the successor's set holds the same references (with the same bound owners) in
    /// the order of its own union. Taking the successor's references too would reorder the published references of later
    /// members. Program 539 of the second generated chorded corpus (seed 62), reduced: <c>M10</c> and <c>M16</c> carry
    /// library paths, <c>M1</c> an escaping name, and the cycle closes through <c>M2 → M28</c> and <c>M11 → M19</c>.
    /// </summary>
    [Fact]
    public void AKeptOrderedHolder_KeepsItsOwnReferenceOrder()
    {
        var (held, _) = AssertSameOutcome(KeptOrderedHolderWitness);
        Assert.InRange(held.Observations.SummaryMemberKeptHoldersWithoutFold, 1, long.MaxValue);
        Assert.InRange(held.Observations.SummaryMemberOrderedHolders, 1, long.MaxValue);
    }

    private const string KeptOrderedHolderWitness = """
        G0 = 5
        H0 = 6
        F(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17) = {
        Lib = {
        public X = p15 + 1
        public Y = 2
        public Z = 3
        public V = X + Y
        }
        M1 = M9 + G0
        M2 = M10 + M28
        M3 = p3 + M2 + M1
        M4 = M12 + M2
        M5 = M4
        M6 = M5
        M8 = M6
        M9 = M8
        M10 = Lib.Z + M8 + p10 + p11
        M11 = p8 + p9 + p15 + M19 + M10
        M12 = M11
        M13 = M12
        M14 = M13
        M15 = M14
        M16 = M15 + Lib.V
        M17 = M16
        M18 = M17 + p6
        M19 = M18
        M20 = M18
        M21 = M20
        M22 = M21
        M24 = M22
        M25 = M24
        M26 = M25
        M27 = M26 + M3
        M28 = M27
        M8 + Lib.X
        }
        F(4, 6, 7, 8, 3, 4, 3, 4, 4, 4, 7, 3, 8, 5, 6, 3, 6)
        """;

    // ── Controls ────────────────────────────────────────────────────────────

    /// <summary>
    /// Shapes without chords — the closed chain in both orders, the single-predecessor cycle in both orders, the cycle that
    /// closes through a path, the acyclic chain with a path, a pure-union cycle, members that read themselves, the
    /// path-bearing cycle, the early-stopping block cycle — are unchanged: every counter, including the expansions' entries
    /// and parts and the change tests without a fold, is the solve's as before, and no new route is taken.
    /// </summary>
    [Fact]
    public void ShapesWithoutChords_AreUnchanged()
    {
        const int k = 48;
        var sources = new[]
        {
            MixedCycleMemberScheduleTests.ClosedChain(k),
            MixedCycleMemberScheduleTests.ClosedChain(k, reversed: true),
            Level(k, i => i == 1 ? Closing(k) : $"P{i - 1} + p{i}"),
            Level(k, i => i == 1 ? Closing(k) : $"P{i - 1} + p{i}", reversed: true),
            Level(k, i => i == 1 ? "B.X + p1 + Lib.X" : Chain(i), extra: $"B = {{\npublic X = 1\nP{k}\n}}\n"),
            Level(k, i => i == 1 ? "p1 + Lib.X" : Chain(i)),
            Level(k, i => i == 1 ? $"P{k} + p1" : Chain(i)),
            Level(k, i => i == 1 ? "P1 + p1 + Lib.X" : $"P{i} + P{i - 1} + p{i}", row: $"P{k}"),
            Level(k, i => (i == 1 ? Closing(k) : Chain(i)) + (i % 4 == 0 ? $" + Lib.{(char)('X' + i % 3)}" : ""), reversed: true),
            MixedCycleOrderedHoldingTests.EarlyStoppingBlockCycle(k: 24, period: 18, path: 6),
        };
        foreach (var source in sources)
        {
            var (held, asBefore) = AssertSameOutcome(source);
            var (h, b) = (held.Observations, asBefore.Observations);
            Assert.Equal(0, h.SummaryMemberDominatingReads);
            Assert.Equal(0, h.SummaryMemberKeptHoldersWithoutFold);
            Assert.Equal(0, h.SummaryMemberDeferredFoldsOnBudgetRead);
            Assert.Equal(b.SummaryMemberExpansions, h.SummaryMemberExpansions);
            Assert.Equal(b.SummaryMemberExpansionEntries, h.SummaryMemberExpansionEntries);
            Assert.Equal(b.MemberBudgetFoldEntries, h.MemberBudgetFoldEntries);
            Assert.Equal(b.SummaryMemberOrderedFolds, h.SummaryMemberOrderedFolds);
            Assert.Equal(b.SummaryMemberOrderedFoldEntries, h.SummaryMemberOrderedFoldEntries);
            Assert.Equal(b.SummaryMemberChangeTestsWithoutFold, h.SummaryMemberChangeTestsWithoutFold);
            Assert.Equal(b.SummaryMemberDeferredChangeTestFolds, h.SummaryMemberDeferredChangeTestFolds);
        }
    }

    // ── Generated levels ────────────────────────────────────────────────────

    /// <summary>
    /// Generated levels dense in chorded mixed cycles — forward chords of varying reach, backward reads, members without
    /// requirements of their own, wide own sets, a few paths and escaping names, closing references or none, enclosing
    /// owners, readers and navigated block cycles, in all three declaration orders: every program keeps the oracles'
    /// outcome, schedule, checkpoints, frames, part work, static work and summaries, and the solve's fold-budget decisions;
    /// the new routes are taken.
    /// </summary>
    [Fact]
    public void GeneratedChordedLevels_KeepTheSeedsAsBefore()
    {
        long dominating = 0, kept = 0, withoutFold = 0, compared = 0;
        foreach (var source in ChordedLevels(150, seed: 61))
        {
            var (held, _) = AssertSameOutcome(source);
            dominating += held.Observations.SummaryMemberDominatingReads;
            kept += held.Observations.SummaryMemberKeptHoldersWithoutFold;
            withoutFold += held.Observations.SummaryMemberChangeTestsWithoutFold;
            compared++;
        }

        output.WriteLine($"{compared} levels: dominating reads {dominating}, kept holders {kept}, replaced without fold {withoutFold}");
        Assert.InRange(dominating, 1, long.MaxValue);
        Assert.InRange(kept, 1, long.MaxValue);
        Assert.InRange(withoutFold, 1, long.MaxValue);
    }

    /// <summary>The generator of the scratch differential (seed 61 there): chorded mixed cycles, see the test above.</summary>
    internal static IEnumerable<string> ChordedLevels(int count, int seed)
    {
        var random = new Random(seed);
        for (var n = 0; n < count; n++)
        {
            var parameterCount = 2 + random.Next(30);
            var parameters = Enumerable.Range(1, parameterCount).Select(i => $"p{i}").ToArray();
            var members = 8 + random.Next(56);
            var order = random.Next(3); // 0 forward, 1 reversed, 2 shuffled
            var chordRate = 0.05 + random.NextDouble() * 0.3;
            var chordReach = 2 + random.Next(10);
            var backRate = random.Next(3) == 0 ? 0.0 : random.NextDouble() * 0.3;
            var bareRate = random.Next(3) == 0 ? 0.0 : random.NextDouble() * 0.35;
            var wideRate = random.Next(3) == 0 ? 0.0 : random.NextDouble() * 0.4;
            var pathRate = random.Next(2) == 0 ? 0.0 : random.NextDouble() * 0.1;
            var escapeRate = random.Next(4) == 0 ? random.NextDouble() * 0.1 : 0.0;
            var closing = random.Next(5); // 0..2 a library path at the closing member, 3 an escaping name, 4 none
            var closeCount = 1 + random.Next(2);
            var readers = random.Next(3) == 0;
            var blockCycle = random.Next(6) == 0;
            var singleRate = random.Next(4) == 0 ? random.NextDouble() * 0.5 : 0.0;
            var ownerRate = random.Next(5) == 0 ? 0.3 : 0.0;
            string Pick(params string[] items) => items[random.Next(items.Length)];

            string Member(int i)
            {
                var own = new List<string>();
                if (random.NextDouble() >= bareRate)
                    own.Add(parameters[(i - 1) % parameterCount]);
                if (random.NextDouble() < wideRate)
                    for (var w = random.Next(12); w > 0; w--) own.Add(Pick(parameters));
                if (ownerRate > 0 && random.NextDouble() < ownerRate) own.Add($"q{1 + random.Next(3)}");
                var reads = new List<string>();
                if (i > 1) reads.Add($"M{i - 1}");
                if (i > 2 && random.NextDouble() >= singleRate) reads.Add($"M{i - 2}");
                if (random.NextDouble() < chordRate && i + chordReach <= members) reads.Add($"M{i + chordReach}");
                if (random.NextDouble() < chordRate / 2) reads.Add($"M{1 + random.Next(members)}");
                if (i > 3 && random.NextDouble() < backRate) reads.Add($"M{1 + random.Next(i - 1)}");
                if (random.Next(4) == 0) reads.Reverse();
                if (i <= closeCount) reads.Add($"M{members - random.Next(Math.Min(3, members - 1))}");
                var refs = new List<string>();
                if (i == 1 && closing <= 2) refs.Add(Pick("Lib.X", "Lib.Y", "Lib.V"));
                if (i == 1 && closing == 3) refs.Add("G0");
                if (random.NextDouble() < pathRate) refs.Add(Pick("Lib.X", "Lib.Y", "Lib.Z", "Lib.V"));
                if (random.NextDouble() < escapeRate) refs.Add(Pick("G0", "H0"));
                var atoms = new List<string>();
                var refsFirst = refs.Count > 0 && random.Next(3) == 0;
                if (refsFirst) atoms.AddRange(refs);
                if (random.Next(4) != 0) { atoms.AddRange(reads); atoms.AddRange(own); }
                else { atoms.AddRange(own); atoms.AddRange(reads); }
                if (!refsFirst) atoms.AddRange(refs);
                if (atoms.Count == 0) atoms.Add("1");
                return $"M{i} = {string.Join(" + ", atoms.Distinct())}";
            }

            var lines = new List<string>
            {
                "Lib = {", $"public X = {Pick(parameters)} + 1", "public Y = 2", "public Z = 3", "public V = X + Y", "}",
            };
            var declarations = Enumerable.Range(1, members).Select(Member).ToList();
            if (order == 1) declarations.Reverse();
            else if (order == 2) declarations = declarations.OrderBy(_ => random.Next()).ToList();
            if (blockCycle)
            {
                lines.Add("L = {");
                lines.AddRange(declarations.Select(d => "public " + d));
                lines.Add("}");
                for (var i = 1; i <= members; i += 1 + random.Next(4))
                    lines.Add($"R{i} = L.M{i} + {Pick("Lib.Y", "Lib.X", "G0")}");
                lines.Add($"R1 + L.M{members}");
            }
            else
            {
                lines.AddRange(declarations);
                if (readers)
                    for (var i = 1; i <= members; i += 1 + random.Next(3))
                        lines.Add($"R{i} = M{i} + {Pick("Lib.Y", "Lib.X", "G0", "M1")}");
                lines.Add(readers ? $"R1 + M{members}" : $"M{1 + random.Next(members)} + Lib.X");
            }

            var arguments = string.Join(", ", parameters.Select(_ => random.Next(9) + 1));
            var signature = string.Join(", ", parameters);
            var body = string.Join("\n", lines);
            var source = new StringBuilder("G0 = 5\nH0 = 6\n");
            if (ownerRate > 0)
                source.Append($"G(q1, q2, q3) = {{\nF({signature}) = {{\n{body}\n}}\nF({arguments})\n}}\nG(1, 2, 3)\n");
            else
                source.Append($"F({signature}) = {{\n{body}\n}}\nF({arguments})\n");
            yield return source.ToString();
        }
    }

    // ── Cancellation and the work bound ─────────────────────────────────────

    /// <summary>
    /// CANCELLATION: a dominating read takes the copied expansion's one summary-channel checkpoint. A token cancelled at
    /// the checkpoint of the first dominating read escapes with that token, records nothing after it, and leaves nothing
    /// behind: a fresh parse publishes the uncancelled metadata.
    /// </summary>
    [Fact]
    public void CancellationAtADominatingRead_EscapesWithTheToken_AndLeavesNothingBehind()
    {
        var source = Chorded(64);
        var uncancelled = Parse(source);
        long target = -1;
        FrontEndTraversalObservations probe = null!;
        probe = new FrontEndTraversalObservations
        {
            CheckpointReached = (kind, ordinal) =>
            {
                if (kind == FrontEndCancellationCheckpoint.SummaryChannel && target < 0 && probe.SummaryMemberDominatingReads == 1)
                    target = ordinal;
            },
        };
        Parser.ParseObserved(source, options: null, probe);
        Assert.InRange(target, 1, uncancelled.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel));

        using var cancellation = new CancellationTokenSource();
        long readsAtCancel = -1;
        FrontEndTraversalObservations observations = null!;
        observations = new FrontEndTraversalObservations
        {
            CheckpointReached = (kind, ordinal) =>
            {
                if (kind != FrontEndCancellationCheckpoint.SummaryChannel || ordinal != target || cancellation.IsCancellationRequested)
                    return;
                readsAtCancel = observations.SummaryMemberDominatingReads;
                cancellation.Cancel();
            },
        };

        var error = Assert.Throws<OperationCanceledException>(() => Parser.ParseObserved(
            source, new RunOptions { SourceProcessingCancellationToken = cancellation.Token }, observations));

        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal(target, observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel));
        Assert.Equal(1, readsAtCancel);
        Assert.Equal(uncancelled.Metadata, Parse(source).Metadata);
    }

    /// <summary>
    /// The work bound is resource policy (SETTLEMENT FRAME CHARGE): the chorded cycle in both orders and the distinct-holder
    /// control are admitted at exactly the charge of the solve as before and refused one unit below it.
    /// </summary>
    [Theory]
    [InlineData("chorded")]
    [InlineData("chorded-reversed")]
    [InlineData("distinct")]
    public void TheWorkBound_AdmitsAtTheChargeAsBefore_AndRefusesOneUnitBelow(string shape)
    {
        var source = shape switch
        {
            "chorded" => Chorded(48),
            "chorded-reversed" => Chorded(48, reversed: true),
            _ => ChordedDistinct(48),
        };

        long Run(long? limit)
        {
            var (resolved, ledger, _) = ExposureSettlementFrameChargeTests.Resolved(source,
                limits => limit.HasValue ? limits with { MaxEvaluations = limit.Value } : limits);
            _ = PropertyExposureResolver.Resolve(resolved);
            return ledger.WorkCharged;
        }

        var charge = With(Oracle.AsBefore, () => Run(null));
        Assert.Equal(charge, Run(null));
        Assert.Equal(charge, Run(charge));
        Assert.Throws<StaticQueryLimitExceededException>(() => Run(charge - 1));
    }
}
