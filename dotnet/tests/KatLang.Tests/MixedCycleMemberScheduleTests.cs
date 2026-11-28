using System.Text;
using Xunit.Abstractions;
using static KatLang.PropertyDependencyGraphBuilder;

namespace KatLang.Tests;

/// <summary>
/// MIXED-CYCLE SCHEDULE (November 27 2026; C# exposure implementation only — no classification, requirement, diagnostic
/// kind, value or Lean rule changes). A strongly connected component of a level's members that is not solved as one unit —
/// a MIXED component, in which some member reads a path or a name the level does not declare — is evaluated member by
/// member. Its members were queued in the order the dependency walk discovered them, which put a chain closed into a cycle
/// (<c>P1 = PK + p1 + Lib.X</c>, <c>P(i) = P(i-1) + P(i-2) + p(i)</c>) before the members each one reads: every pass moved a
/// change about two members, so the cycle took about K² / 2 full-width evaluations (8,448 at K = 128). The solver now ranks a
/// mixed component's members in the walk's postorder and always evaluates the queued unit of least rank. Oracle: the former
/// schedule (<see cref="PropertyDependencyGraphBuilder.MemberSolveInDiscoveryOrderForTesting"/>), compared by every member's
/// content, published metadata, diagnostics, static work and deterministic counters, never time.
/// </summary>
public sealed class MixedCycleMemberScheduleTests(ITestOutputHelper output)
{
    // ── Harness ─────────────────────────────────────────────────────────────

    private static T Discovery<T>(Func<T> work)
    {
        var previous = MemberSolveInDiscoveryOrderForTesting.Value;
        MemberSolveInDiscoveryOrderForTesting.Value = true;
        try { return work(); }
        finally { MemberSolveInDiscoveryOrderForTesting.Value = previous; }
    }

    private static T CopiedSeeds<T>(Func<T> work)
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

    /// <summary>Every summary of a standalone summary build of <paramref name="source"/>, under the production and the former schedule.</summary>
    private static List<(string Where, SummarySeed Ranked, SummarySeed Discovered)> Summaries(string source)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var context = AnalyzedStaticStructures.ForBoundAst(root);
        var ranked = StandaloneSummaries.MemoFor(root);
        var discovered = StandaloneSummaries.MemoFor(root);
        BuildSummaries(root, context, ranked);
        Discovery(() => BuildSummaries(root, context, discovered));
        var pairs = new List<(string, SummarySeed, SummarySeed)>();
        void Add(string where, AlgorithmSummary left, AlgorithmSummary right)
        {
            pairs.Add((where + " output", left.OutputSeed, right.OutputSeed));
            Assert.Equal(right.MemberSeeds.Count, left.MemberSeeds.Count);
            foreach (var (name, seed) in right.MemberSeeds)
                pairs.Add((where + " member " + name, left.MemberSeeds[name], seed));
        }

        Assert.Equal(discovered.IndependentAlgorithmSummaries?.Count ?? 0, ranked.IndependentAlgorithmSummaries?.Count ?? 0);
        Assert.Equal(discovered.ContextualAlgorithmSummaries?.Count ?? 0, ranked.ContextualAlgorithmSummaries?.Count ?? 0);
        foreach (var (algorithm, summary) in discovered.IndependentAlgorithmSummaries ?? [])
            Add("independent", ranked.IndependentAlgorithmSummaries![algorithm], summary);
        foreach (var (key, summary) in discovered.ContextualAlgorithmSummaries ?? [])
            Add("contextual", ranked.ContextualAlgorithmSummaries![key], summary);
        return pairs;
    }

    /// <summary>
    /// Whether two member seeds hold the same content: the same required names, visible names and owner-qualified
    /// parameters, and the same references — each with its origin, path, bound owners and selection — in ANY order.
    /// Returns whether the references also stand in the same order.
    /// </summary>
    private static bool AssertSameContent(SummarySeed ranked, SummarySeed discovered, string where)
    {
        ranked = ranked.Clone();
        discovered = discovered.Clone();
        Assert.True(discovered.RequiredAncestorOwnedParameterNames.SetEquals(ranked.RequiredAncestorOwnedParameterNames), where);
        Assert.True(discovered.VisiblePropertyDependencyNames.SetEquals(ranked.VisiblePropertyDependencyNames), where);
        Assert.True(discovered.OwnerQualifiedParameters.SetEquals(ranked.OwnerQualifiedParameters), where);
        static (string, object?, object?, bool, PendingSelection?) Identity(SummaryReference reference)
            => reference is PendingReference anchored
                ? (anchored.ContentKey, anchored.Origin.Facts, anchored.Origin.Key, anchored.OpenPath, anchored.Selection)
                : (reference.ContentKey, null, null, false, null);
        var left = ranked.PendingReferences.Select(Identity).ToArray();
        var right = discovered.PendingReferences.Select(Identity).ToArray();
        Assert.Equal(right.Length, left.Length);
        Assert.True(right.ToHashSet().SetEquals(left), where);
        return left.SequenceEqual(right);
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

    /// <summary>The reviewed shape: the two-predecessor chain closed into one cycle through <c>P1 = PK + p1 + Lib.X</c>.</summary>
    internal static string ClosedChain(int k, bool reversed = false)
        => Level(k, i => i == 1 ? $"P{k} + p1 + Lib.X" : Chain(i), reversed: reversed);

    /// <summary>Forward chords every 8th member (<c>P(i)</c> also reads <c>P(i+4)</c>): nested cycles inside the component.</summary>
    private static string BranchedCycle(int k, bool reversed = false)
        => Level(k, i => (i == 1 ? $"P{k} + p1 + Lib.X" : Chain(i)) + (i % 8 == 0 && i + 4 <= k ? $" + P{i + 4}" : ""), reversed: reversed);

    /// <summary>Every 4th member also reads one of three library paths, so the members carry several references.</summary>
    private static string PathBearingCycle(int k, bool reversed = false)
        => Level(k, i => (i == 1 ? $"P{k} + p1 + Lib.X" : Chain(i)) + (i % 4 == 0 ? $" + Lib.{(char)('X' + i % 3)}" : ""), reversed: reversed);

    /// <summary>A cycle through a path back into the level's own member (<c>F.P1</c>, genuinely recursive).</summary>
    private static string SelfPathCycle(int k)
        => Level(k, i => i == 1 ? $"P{k} + p1 + Lib.X" : i == k ? Chain(i) + " + F.P1" : Chain(i));

    /// <summary>The sharing-negative control: a single-predecessor mixed cycle (no expansion holds a predecessor).</summary>
    private static string SinglePredecessorCycle(int k, bool reversed = false)
        => Level(k, i => i == 1 ? $"P{k} + p1 + Lib.X" : $"P{i - 1} + p{i}", reversed: reversed);

    /// <summary>Path-bearing readers of every member of the closed chain.</summary>
    private static string ClosedChainWithReaders(int k)
        => Level(k, i => i == 1 ? $"P{k} + p1 + Lib.X" : Chain(i), row: $"R{k}",
            extra: string.Concat(Enumerable.Range(1, k).Select(i => $"R{i} = P{i} + Lib.Y\n")));

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

    // ── The reviewed shape ──────────────────────────────────────────────────

    /// <summary>
    /// The closed chain converges in two passes in either source order: its K members take 2K − 1 evaluations (the
    /// level's <c>Lib</c>, the three members of <c>Lib</c>'s own level and the root take five more) and 2K − 2 reader
    /// notifications, where the discovery order took about K² / 2 evaluations and K² notifications. Every member requires every parameter, the
    /// published metadata and diagnostics are the former schedule's, and so is the static work, which the cycle's one
    /// reference keeps exactly.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ClosedChain_ConvergesInTwoPasses_WhereTheDiscoveryOrderTookQuadraticallyMany(bool reversed)
    {
        var entries = new long[3];
        var discoveredEntries = new long[3];
        var sizes = new[] { 32, 64, 128 };
        for (var at = 0; at < sizes.Length; at++)
        {
            var k = sizes[at];
            var source = ClosedChain(k, reversed);
            var ranked = Parse(source);
            var discovered = Discovery(() => Parse(source));
            Assert.Equal("", ranked.Diagnostics);
            Assert.Equal(discovered.Diagnostics, ranked.Diagnostics);
            Assert.Equal(discovered.Metadata, ranked.Metadata);
            Assert.Equal(2L * k + 4, ranked.Observations.SummaryMemberEvaluations);
            Assert.Equal(2L * k - 2, ranked.Observations.SummaryMemberReaderNotifications);
            Assert.InRange(discovered.Observations.SummaryMemberEvaluations, (long)k * k / 2, (long)k * k);
            Assert.Equal(Discovery(() => Work(source)), Work(source));
            // Measured with copied seeds (MIXED-CYCLE COMPLETE SEEDS keeps the ranked schedule's storage linear,
            // MixedCycleCompleteSeedTests): what each schedule copies when every cycle member keeps a folded seed.
            entries[at] = CopiedSeeds(() => Parse(source)).Observations.SummaryMemberExpansionEntries;
            discoveredEntries[at] = CopiedSeeds(() => Discovery(() => Parse(source))).Observations.SummaryMemberExpansionEntries;
            output.WriteLine($"K={k}: evaluations {discovered.Observations.SummaryMemberEvaluations} -> {ranked.Observations.SummaryMemberEvaluations}, "
                + $"notifications {discovered.Observations.SummaryMemberReaderNotifications} -> {ranked.Observations.SummaryMemberReaderNotifications}, "
                + $"expansion entries {discoveredEntries[at]} -> {entries[at]}");

            var owner = SourceProvenance.ParseValid(source).Root;
            var expected = Enumerable.Range(1, k).Select(i => $"p{i}").Order(StringComparer.Ordinal).Select(name => (name, 0)).ToArray();
            foreach (var member in new[] { "P1", "P2", $"P{k / 2}", $"P{k}" })
                ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, "F", member), expected);
        }

        // With copied seeds each evaluation of a cycle member copies its full width: two passes keep K² entries, the
        // discovery order K³ / 2.
        Assert.InRange((double)entries[2] / entries[1], 3.0, 5.0);
        Assert.InRange((double)discoveredEntries[2] / discoveredEntries[1], 6.0, 10.0);
    }

    /// <summary>
    /// A component converges before any unit that reads it is first evaluated: K path-bearing readers of the closed
    /// chain add exactly K evaluations, where the discovery order evaluated them again after every pass that changed what
    /// they read.
    /// </summary>
    [Fact]
    public void ReadersOfACycle_AreEvaluatedOnce_AfterItConverges()
    {
        const int k = 64;
        var cycle = Parse(ClosedChain(k));
        var source = ClosedChainWithReaders(k);
        var readers = Parse(source);
        var discovered = Discovery(() => Parse(source));
        Assert.Equal("", readers.Diagnostics);
        Assert.Equal(discovered.Metadata, readers.Metadata);
        Assert.Equal(k, readers.Observations.SummaryMemberEvaluations - cycle.Observations.SummaryMemberEvaluations);
        Assert.Equal(cycle.Observations.SummaryMemberReaderNotifications, readers.Observations.SummaryMemberReaderNotifications);
        Assert.InRange(discovered.Observations.SummaryMemberEvaluations, 10L * readers.Observations.SummaryMemberEvaluations, long.MaxValue);
        Assert.Equal(Discovery(() => Work(source)), Work(source));
    }

    // ── Branched, path-bearing, recursive and sharing-negative cycles ───────

    /// <summary>
    /// Branched cycles, cycles whose members carry several library paths, a cycle through the owner's own member, the
    /// single-predecessor cycle and two chained cycles, in both source orders: every member keeps its content — required
    /// names, owner-qualified parameters and the same references with the same origins — and the published metadata,
    /// diagnostics and static work are the former schedule's, in fewer evaluations. The references of a member of a
    /// cycle that carries several of them may stand in another order: the order is the schedule's (a member keeps the
    /// order of its last expansion that changed its content), and the paths here settle to the same frames either way.
    /// </summary>
    [Theory]
    [InlineData("branched", false)]
    [InlineData("branched", true)]
    [InlineData("paths", false)]
    [InlineData("paths", true)]
    [InlineData("self-path", false)]
    [InlineData("single-predecessor", false)]
    [InlineData("single-predecessor", true)]
    [InlineData("two-cycles", false)]
    public void BranchedPathBearingAndRecursiveCycles_KeepEveryMembersContent(string shape, bool reversed)
    {
        foreach (var k in new[] { 16, 48 })
        {
            var source = shape switch
            {
                "branched" => BranchedCycle(k, reversed),
                "paths" => PathBearingCycle(k, reversed),
                "self-path" => SelfPathCycle(k),
                "single-predecessor" => SinglePredecessorCycle(k, reversed),
                _ => TwoCycles(k),
            };
            var ranked = Parse(source);
            var discovered = Discovery(() => Parse(source));
            Assert.Equal("", ranked.Diagnostics);
            Assert.Equal(discovered.Metadata, ranked.Metadata);
            Assert.InRange(ranked.Observations.SummaryMemberEvaluations, 1, discovered.Observations.SummaryMemberEvaluations / 2);
            Assert.InRange(ranked.Observations.SummaryMemberEvaluations, 1, 4L * k + 16);
            Assert.Equal(discovered.Observations.RequiredAncestorSettlementFrames, ranked.Observations.RequiredAncestorSettlementFrames);
            Assert.Equal(Discovery(() => Work(source)), Work(source));
            var reordered = Summaries(source).Count(pair => !AssertSameContent(pair.Ranked, pair.Discovered, pair.Where));
            output.WriteLine($"{shape} K={k}: evaluations {discovered.Observations.SummaryMemberEvaluations} -> "
                + $"{ranked.Observations.SummaryMemberEvaluations}; {reordered} seeds hold their references in another order");
            if (shape is "branched" or "single-predecessor")
                Assert.Equal(0, reordered);
        }
    }

    // ── Controls ────────────────────────────────────────────────────────────

    /// <summary>
    /// Levels without a mixed component are scheduled exactly as before: an acyclic level (nothing is ever queued again,
    /// so the ranked order is the first-evaluation order), a pure-union component solved as one unit, members that read
    /// themselves, a member navigating its own owner, and the two-predecessor chain. Every counter, the sequence of every
    /// cancellation checkpoint, the static work and every summary — references in order — are the former schedule's.
    /// </summary>
    [Fact]
    public void LevelsWithoutAMixedComponent_KeepTheFormerScheduleExactly()
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
            var ranked = Parse(source);
            var discovered = Discovery(() => Parse(source));
            Assert.Equal("", ranked.Diagnostics);
            Assert.Equal(discovered.Metadata, ranked.Metadata);
            Assert.Equal(discovered.Sequence, ranked.Sequence);
            var (r, d) = (ranked.Observations, discovered.Observations);
            Assert.Equal(d.SummaryMemberEvaluations, r.SummaryMemberEvaluations);
            Assert.Equal(d.SummaryMemberReaderNotifications, r.SummaryMemberReaderNotifications);
            Assert.Equal(d.SummaryMemberExpansions, r.SummaryMemberExpansions);
            Assert.Equal(d.SummaryMemberExpansionEntries, r.SummaryMemberExpansionEntries);
            Assert.Equal(d.SummaryMemberExpansionHeldParts, r.SummaryMemberExpansionHeldParts);
            Assert.Equal(d.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel),
                r.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel));
            Assert.Equal(d.RequiredAncestorSettlementFrames, r.RequiredAncestorSettlementFrames);
            Assert.Equal(d.SettlementSeedPartWork, r.SettlementSeedPartWork);
            Assert.Equal(d.RequiredAncestorLevelEvaluations, r.RequiredAncestorLevelEvaluations);
            Assert.Equal(Discovery(() => Work(source)), Work(source));
            var root = SourceProvenance.ParseValid(source).Root;
            var context = AnalyzedStaticStructures.ForBoundAst(root);
            var rankedMemo = StandaloneSummaries.MemoFor(root);
            var discoveredMemo = StandaloneSummaries.MemoFor(root);
            BuildSummaries(root, context, rankedMemo);
            Discovery(() => BuildSummaries(root, context, discoveredMemo));
            foreach (var (key, summary) in discoveredMemo.ContextualAlgorithmSummaries ?? [])
                Assert.Null(SummaryMemo.AdoptedSummaryDifference(rankedMemo.ContextualAlgorithmSummaries![key], summary));
            foreach (var (algorithm, summary) in discoveredMemo.IndependentAlgorithmSummaries ?? [])
                Assert.Null(SummaryMemo.AdoptedSummaryDifference(rankedMemo.IndependentAlgorithmSummaries![algorithm], summary));
        }
    }

    // ── Generated levels ────────────────────────────────────────────────────

    /// <summary>
    /// Generated levels dense in mixed cycles — members reading earlier and later siblings and themselves, library paths,
    /// paths through the owner, opened names, parameterized members, deconstruction sources, local shadowing, nested
    /// owners with the same parameter names, detached readers and reversed declaration order: every program's diagnostics
    /// and published metadata are the former schedule's, and every summary keeps its content (read-dependent requeues,
    /// owner qualification and pending references included). The schedule saves evaluations overall.
    /// </summary>
    [Fact]
    public void GeneratedCyclicLevels_KeepEveryOutcomeAndEveryMembersContent()
    {
        long rankedEvaluations = 0, discoveredEvaluations = 0, compared = 0, reordered = 0, changedPrograms = 0;
        foreach (var source in GeneratedCyclicLevels(300, seed: 27))
        {
            var ranked = Parse(source);
            var discovered = Discovery(() => Parse(source));
            Assert.Equal(discovered.Diagnostics, ranked.Diagnostics);
            Assert.Equal(discovered.Metadata, ranked.Metadata);
            rankedEvaluations += ranked.Observations.SummaryMemberEvaluations;
            discoveredEvaluations += discovered.Observations.SummaryMemberEvaluations;
            if (ranked.Observations.SummaryMemberEvaluations != discovered.Observations.SummaryMemberEvaluations)
                changedPrograms++;
            if (ranked.Diagnostics.Length != 0)
                continue;
            foreach (var (where, left, right) in Summaries(source))
            {
                compared++;
                if (!AssertSameContent(left, right, where + "\n" + source))
                    reordered++;
            }
        }

        output.WriteLine($"{compared} summaries compared, {reordered} with references in another order; {changedPrograms} programs "
            + $"scheduled differently; evaluations {discoveredEvaluations} -> {rankedEvaluations}");
        Assert.InRange(changedPrograms, 60, int.MaxValue);
        Assert.InRange(rankedEvaluations, 1, discoveredEvaluations * 9 / 10);
    }

    /// <summary>Seeded random levels dense in mixed cycles (see <see cref="GeneratedCyclicLevels_KeepEveryOutcomeAndEveryMembersContent"/>).</summary>
    internal static IEnumerable<string> GeneratedCyclicLevels(int count, int seed)
    {
        var random = new Random(seed);
        for (var n = 0; n < count; n++)
        {
            var parameters = Enumerable.Range(1, 1 + random.Next(12)).Select(i => $"p{i}").ToArray();
            var members = 3 + random.Next(26);
            var opened = random.Next(10) < 3;
            var nested = random.Next(10) < 3;
            var detached = nested && random.Next(2) == 0;
            var cycles = 0.08 + random.NextDouble() * 0.3;
            var paths = random.Next(5) == 0 ? 0.0 : 0.05 + random.NextDouble() * 0.2;
            var selfPaths = random.Next(4) == 0;
            var siblings = 0.25 + random.NextDouble() * 0.2;
            var shadows = random.Next(4) == 0 ? 0.2 : 0.0;
            var parameterized = random.Next(5) == 0;
            var deconstruction = random.Next(5) == 0;
            var reversed = random.Next(10) < 4;
            var owner = nested ? "F.G" : "F";
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
                if (r < siblings + cycles + 0.25) return Pick(parameters);
                if (r < siblings + cycles + 0.25 + paths)
                    return selfPaths && random.Next(10) < 3 ? $"{owner}.M{1 + random.Next(members)}" : Pick("Lib.X", "Lib.Y", "Lib.W(1)", "Lib.V");
                if (opened && r < 0.85) return Pick("Z", "Z2");
                if (parameterized && r < 0.9 && i > 2) return $"N({Pick([.. parameters, "1", $"M{1 + random.Next(members)}"])})";
                if (deconstruction && r < 0.93) return Pick("da", "db");
                return (random.Next(9) + 1).ToString();
            }

            var lines = new List<string>();
            if (opened) lines.Add("open O");
            lines.AddRange(["Lib = {", $"public X = {Pick(parameters)} + 1", "public Y = 2", $"public W(a) = a + {Pick([.. parameters, "3"])}", "public V = X + Y", "}"]);
            if (opened) lines.AddRange(["O = {", $"public Z = {Pick(parameters)}", "public Z2 = 5", "}"]);
            if (parameterized) lines.Add($"N(z) = z + {Pick(parameters)}");
            if (deconstruction) lines.Add($"da, db = M{1 + random.Next(members)}, 10");
            var declarations = new List<string[]>();
            for (var i = 1; i <= members; i++)
            {
                var atoms = Enumerable.Range(0, 1 + random.Next(4)).Select(_ => Atom(i)).ToList();
                var visibility = detached && random.Next(2) == 0 ? "public " : "";
                if (shadows > 0 && random.NextDouble() < shadows && i > 2)
                {
                    var local = $"M{i - 1 - random.Next(i - 1)}";
                    declarations.Add([$"{visibility}M{i} = {{", $"{local} = {random.Next(9) + 1}", string.Join(" + ", [.. atoms, local]), "}"]);
                }
                else
                    declarations.Add([$"{visibility}M{i} = {string.Join(" + ", atoms)}"]);
            }

            if (reversed) declarations.Reverse();
            lines.AddRange(declarations.SelectMany(declaration => declaration));
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

    // ── Cancellation and admission ──────────────────────────────────────────

    /// <summary>
    /// CANCELLATION: the ranked schedule takes the summary channel's checkpoints at every expansion as before, only fewer of
    /// them; a token cancelled at a checkpoint inside the cycle's second pass escapes with that token, records nothing after
    /// the cancelling checkpoint, and leaves nothing behind: a fresh parse publishes the uncancelled metadata.
    /// </summary>
    [Fact]
    public void CancellationInsideTheCyclesSecondPass_EscapesWithTheToken_AndLeavesNothingBehind()
    {
        const int k = 64;
        var source = ClosedChain(k);
        var uncancelled = Parse(source);
        // The first summary-channel checkpoint of the cycle's second pass: after Lib's level (three members), the level's Lib and
        // the K members of the first pass.
        long secondPass = -1;
        FrontEndTraversalObservations probe = null!;
        probe = new FrontEndTraversalObservations
        {
            CheckpointReached = (kind, ordinal) =>
            {
                if (kind == FrontEndCancellationCheckpoint.SummaryChannel && secondPass < 0 && probe.SummaryMemberEvaluations > k + 4)
                    secondPass = ordinal;
            },
        };
        Parser.ParseObserved(source, options: null, probe);
        Assert.InRange(secondPass, 1, uncancelled.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel) - 1);
        foreach (var cancelAt in new[] { secondPass, secondPass + k / 2 })
        {
            using var cancellation = new CancellationTokenSource();
            long evaluationsAtCancel = -1;
            FrontEndTraversalObservations observations = null!;
            observations = new FrontEndTraversalObservations
            {
                CheckpointReached = (kind, ordinal) =>
                {
                    if (kind != FrontEndCancellationCheckpoint.SummaryChannel || ordinal != cancelAt || cancellation.IsCancellationRequested)
                        return;
                    evaluationsAtCancel = observations.SummaryMemberEvaluations;
                    cancellation.Cancel();
                },
            };

            var error = Assert.Throws<OperationCanceledException>(() => Parser.ParseObserved(
                source, new RunOptions { SourceProcessingCancellationToken = cancellation.Token }, observations));

            Assert.Equal(cancellation.Token, error.CancellationToken);
            Assert.Equal(cancelAt, observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.SummaryChannel));
            Assert.InRange(evaluationsAtCancel, k + 5, 2L * k + 4);
            Assert.Equal(evaluationsAtCancel, observations.SummaryMemberEvaluations);
            Assert.Equal(uncancelled.Metadata, Parse(source).Metadata);
        }
    }

    /// <summary>
    /// Each schedule admits at its exact operation charge and refuses one unit below. The closed chain keeps its charge.
    /// In the small cycles, reference order changes settlement by two fewer frames or four more.
    /// </summary>
    [Theory]
    [InlineData(0)]
    [InlineData(-2)]
    [InlineData(4)]
    public void EachSchedule_AdmitsAtItsOwnCharge_AndRefusesOneUnitBelow(int frameDelta)
    {
        var source = frameDelta switch
        {
            0 => ClosedChain(48),
            -2 => "F(p) = {\n A = C\n B = p + F.B + A\n C = F.A + B\n B\n}\nF(1)",
            4 => "F(p) = {\n D = C + p\n C = F.B + B\n B = F.D + C + B + F.B\n D\n}\nF(1)",
            _ => throw new ArgumentOutOfRangeException(nameof(frameDelta)),
        };
        var ranked = Parse(source);
        var discovered = Discovery(() => Parse(source));
        Assert.Empty(ranked.Diagnostics);
        Assert.Equal(ranked.Diagnostics, discovered.Diagnostics);
        Assert.Equal(discovered.Metadata, ranked.Metadata);
        Assert.Equal(discovered.Observations.RequiredAncestorSettlementFrames + frameDelta, ranked.Observations.RequiredAncestorSettlementFrames);

        long Run(long? limit)
        {
            var (resolved, ledger, _) = ExposureSettlementFrameChargeTests.Resolved(source,
                limits => limit.HasValue ? limits with { MaxEvaluations = limit.Value } : limits);
            _ = PropertyExposureResolver.Resolve(resolved);
            return ledger.WorkCharged;
        }

        var oldCharge = Discovery(() => Run(null));
        var newCharge = Run(null);
        Assert.Equal(oldCharge + frameDelta * PropertyExposureResolver.SettlementFrameWork, newCharge);
        Assert.Equal(newCharge, Run(newCharge));
        Assert.Throws<StaticQueryLimitExceededException>(() => Run(newCharge - 1));
        Assert.Equal(oldCharge, Discovery(() => Run(oldCharge)));
        Assert.Throws<StaticQueryLimitExceededException>(() => Discovery(() => Run(oldCharge - 1)));
    }

    // ── The walk's postorder ────────────────────────────────────────────────

    /// <summary>
    /// <see cref="DependencyFirstOrder.Components"/> reports each equation's position in its walk's postorder, which is
    /// the order <see cref="DependencyFirstOrder.Of"/> returns; ranked by it, a component's members follow every member
    /// they read except across the edges that close a cycle, which point to a member the walk had entered but not left.
    /// </summary>
    [Fact]
    public void ComponentFinishPositions_AreTheWalksPostorder()
    {
        var random = new Random(5);
        for (var trial = 0; trial < 500; trial++)
        {
            var count = 1 + random.Next(30);
            var edges = Enumerable.Range(0, count)
                .Select(_ => Enumerable.Range(0, random.Next(4)).Select(_ => random.Next(count)).ToArray()).ToArray();
            var skipped = random.Next(4) == 0 ? random.Next(count) : -1;
            bool IsEquation(int index) => index != skipped;
            var components = DependencyFirstOrder.Components(count, IsEquation, index => edges[index], out var finished);
            var order = DependencyFirstOrder.Of(count, IsEquation, index => edges[index]);
            Assert.Equal(order, Enumerable.Range(0, count).Where(IsEquation).OrderBy(index => finished[index]));
            Assert.Equal(order.Order(), components.SelectMany(component => component).Order());
            foreach (var component in components)
            {
                var members = component.ToHashSet();
                foreach (var member in component)
                    foreach (var read in edges[member].Where(members.Contains))
                        if (finished[read] > finished[member])
                            Assert.True(component.IndexOf(read) < component.IndexOf(member), $"trial {trial}: {member} reads {read}");
            }
        }
    }
}
