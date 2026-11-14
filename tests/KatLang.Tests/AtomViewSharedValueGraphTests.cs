using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// The bounded atom collectors over SHARED value graphs, the atom-view siblings of the
/// equality/hash walks (<see cref="SharedValueGraphComplexityTests"/>) and the
/// <see cref="Result.Normalize"/> rebuild (<see cref="NormalizeSharedValueGraphTests"/>). A value
/// is a DAG, not a tree — <c>W = (x, x)</c> applied n times reaches n distinct sequence nodes
/// through 2^n root-to-leaf paths — and the atom views flatten one atom per PATH, so any of them
/// whose WORK is per-path is exponential on values an ordinary in-budget loop builds, while no
/// evaluation step budget bounds it: the blow-up happens inside ONE value-level operation.
///
/// <para><c>Result.TryLanguageAtoms</c> and <c>Result.TryToHostAtoms</c> must keep collecting
/// atoms per path (their contract, bounded by <c>maxItems</c>), but their WORK must not be
/// per path: each memoizes every completed nested structure's run of atoms and REPLAYS it at
/// later shared occurrences (an atomless structure's empty run is skipped), so a walk reads
/// each distinct nested structure's slots once and otherwise only copies output. They observe
/// host cancellation every <see cref="Result.ValueSemanticComparer.UnitsPerCharge"/> units of
/// that work without charging anything. (The former first-atom truth search no longer exists:
/// truth is Boolean-only, decided by <see cref="Result.AsBool"/> without any traversal, so
/// there is nothing left to bound there.)</para>
///
/// <para>Work counts are exact and deterministic, measured through the passive operation-scoped
/// <see cref="ValueTraversalObservations"/>; timing is deliberately not a pass/fail signal.
/// Semantics are checked against <see cref="NaiveAtoms"/>, a test-only recursive replica of the
/// path-expanding collection.</para>
/// </summary>
public class AtomViewSharedValueGraphTests
{
    private const int ShallowDepth = 20;

    private const int DeepDepth = 40;

    private const int DeepTraversalDepth = 200_000;

    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result Str(string value) => new Result.Str(value);

    private static Result List(params Result[] items) => Result.ListValue.TakeOwnership(items);

    private static Result Seq(params Result[] items) => Result.SequenceValue.TakeOwnership(items);

    private static ValueTraversalObservations Observations() => new();

    /// <summary>
    /// The sequence doubling DAG: <c>P0 = leaf</c>, <c>Pk = (P(k-1), P(k-1))</c>. A graph of depth
    /// n has n sequence nodes on the spine (plus whatever structure the leaf carries) and 2^n
    /// root-to-leaf paths.
    /// </summary>
    private static Result SharedSeqDag(int depth, Result leaf)
    {
        var node = leaf;
        for (var i = 0; i < depth; i++)
            node = Seq(node, node);
        return node;
    }

    /// <summary>The list doubling DAG: like <see cref="SharedSeqDag"/> with list nodes.</summary>
    private static Result SharedListDag(int depth, Result leaf)
    {
        var node = leaf;
        for (var i = 0; i < depth; i++)
            node = List(node, node);
        return node;
    }

    /// <summary>Doubling DAG alternating sequence and list levels, so both collector arms run.</summary>
    private static Result SharedMixedDag(int depth, Result leaf)
    {
        var node = leaf;
        for (var i = 0; i < depth; i++)
            node = i % 2 == 0 ? Seq(node, node) : List(node, node);
        return node;
    }

    /// <summary>
    /// Test-only replica of the path-expanding atom collection: recursive, no memo, one visit per
    /// PATH. <c>languageAtoms</c> and <c>hostAtoms</c> flatten identically (both open sequence and
    /// list boundaries; strings contribute nothing), so one oracle serves both collectors. Only
    /// ever applied to small values — on a doubling DAG it is exponential by construction.
    /// </summary>
    private static List<Decimal128> NaiveAtoms(Result value)
    {
        var collected = new List<Decimal128>();
        Collect(value);
        return collected;

        void Collect(Result node)
        {
            switch (node)
            {
                case Result.Atom(var n):
                    collected.Add(n);
                    break;
                case Result.SequenceValue(var items):
                    foreach (var item in items) Collect(item);
                    break;
                case Result.ListValue(var items):
                    foreach (var item in items) Collect(item);
                    break;
                default:
                    break; // strings contribute no atoms
            }
        }
    }

    /// <summary>Every value kind plus the shared/empty/mixed shapes around them.</summary>
    private static IEnumerable<Result> Corpus()
    {
        var sharedAtomless = Seq(Str("s"), List(Atom(9)));
        var sharedAtomBearing = Seq(Atom(1), List(Atom(2)));
        var sharedListLeaf = List(Str("s"));

        return
        [
            Atom(0),
            Atom(7),
            Atom(-3.5m),
            new Result.Atom(Decimal128.NaN),
            new Result.Atom(Decimal128.NegativeZero),
            new Result.Atom(Decimal128.PositiveInfinity),
            Str(string.Empty),
            Str("text"),
            Seq(),
            List(),
            Seq(Seq()),
            Seq(Seq(), Seq(Seq())),
            List(Seq()),
            Seq(List()),
            Seq(Atom(0), Atom(1)),
            Seq(Atom(1), Atom(0)),
            Seq(Str("x"), Atom(0), Atom(1)),
            Seq(List(Atom(1)), Atom(0)),
            List(Atom(1), Atom(2)),
            List(Seq(Atom(1)), Str("a")),
            Seq(Seq(Seq(Atom(5)))),
            Seq(sharedAtomless, sharedAtomless, Atom(3)),
            Seq(sharedAtomBearing, sharedAtomBearing),
            List(sharedAtomBearing, sharedAtomless, sharedAtomBearing),
            List(sharedListLeaf, sharedListLeaf, Atom(4)),
            SharedSeqDag(4, Atom(1)),
            SharedSeqDag(4, Str("s")),
            SharedListDag(4, List(Atom(1), Atom(2))),
            SharedMixedDag(5, Seq(Atom(0), Atom(1))),
            Seq(SharedSeqDag(3, Str("s")), SharedListDag(3, Str("t")), Atom(0), Atom(1)),
        ];
    }

    // ── Collectors: atomless shared subgraphs are visited by node, not by path ───────────────

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public void LanguageAtoms_AtomlessSharedDag_VisitsEachNodeAtMostOnce(int depth)
    {
        var observations = Observations();
        var value = SharedListDag(depth, List(Str("s"), Str("t")));

        Assert.True(value.TryLanguageAtomsObserved(long.MaxValue, observations, out var atoms));

        // depth spine nodes plus the leaf list, each descended once; the atom bound never fires
        // on an atomless graph, so before the memo this walk expanded 2^(depth+1) - 1 nodes.
        Assert.Empty(atoms);
        Assert.Equal(depth + 1, observations.LanguageAtomsStructureExpansionCount);
    }

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public void HostAtoms_AtomlessSharedDag_VisitsEachNodeAtMostOnce(int depth)
    {
        var observations = Observations();
        var value = SharedSeqDag(depth, Str("s"));

        Assert.True(value.TryToHostAtomsObserved(long.MaxValue, observations, out var atoms));

        Assert.Empty(atoms);
        Assert.Equal(depth, observations.HostAtomsStructureExpansionCount);
    }

    [Fact]
    public void Collectors_AtomlessMixedKindDag_VisitsEachNodeAtMostOnce()
    {
        var value = SharedMixedDag(DeepDepth, Str("s"));

        var language = Observations();
        Assert.True(value.TryLanguageAtomsObserved(long.MaxValue, language, out var languageAtoms));
        Assert.Empty(languageAtoms);
        Assert.Equal(DeepDepth, language.LanguageAtomsStructureExpansionCount);

        var host = Observations();
        Assert.True(value.TryToHostAtomsObserved(long.MaxValue, host, out var hostAtoms));
        Assert.Empty(hostAtoms);
        Assert.Equal(DeepDepth, host.HostAtomsStructureExpansionCount);
    }

    [Fact]
    public void Collectors_TailChildCompletion_MemoizesTheChildAndItsParent()
    {
        var sharedTail = List(Str("s"), Seq(Str("t")));
        var tailParent = Seq(Str("prefix"), sharedTail);
        var value = List(tailParent, tailParent, sharedTail, Atom(1));

        var language = Observations();
        Assert.True(value.TryLanguageAtomsObserved(long.MaxValue, language, out var languageAtoms));
        Assert.Equal([1m], languageAtoms);
        Assert.Equal(4, language.LanguageAtomsStructureExpansionCount);

        var host = Observations();
        Assert.True(value.TryToHostAtomsObserved(long.MaxValue, host, out var hostAtoms));
        Assert.Equal([1m], hostAtoms);
        Assert.Equal(4, host.HostAtomsStructureExpansionCount);
    }

    [Fact]
    public void Collectors_AtomlessWorkGrowsLinearlyWithGraphDepth()
    {
        var shallowLanguage = Observations();
        var deepLanguage = Observations();
        Assert.True(SharedListDag(ShallowDepth, Str("s")).TryLanguageAtomsObserved(long.MaxValue, shallowLanguage, out _));
        Assert.True(SharedListDag(DeepDepth, Str("s")).TryLanguageAtomsObserved(long.MaxValue, deepLanguage, out _));
        Assert.Equal(
            DeepDepth - ShallowDepth,
            deepLanguage.LanguageAtomsStructureExpansionCount - shallowLanguage.LanguageAtomsStructureExpansionCount);

        var shallowHost = Observations();
        var deepHost = Observations();
        Assert.True(SharedListDag(ShallowDepth, Str("s")).TryToHostAtomsObserved(long.MaxValue, shallowHost, out _));
        Assert.True(SharedListDag(DeepDepth, Str("s")).TryToHostAtomsObserved(long.MaxValue, deepHost, out _));
        Assert.Equal(
            DeepDepth - ShallowDepth,
            deepHost.HostAtomsStructureExpansionCount - shallowHost.HostAtomsStructureExpansionCount);
    }

    // ── Collectors: per-path atom output is preserved; shared runs are replayed ──────────────

    [Fact]
    public void LanguageAtoms_AtomBearingSharedNodes_AreReplayedNotReDescended()
    {
        var inner = List(Atom(2));
        var shared = Seq(Atom(1), inner);
        var value = List(shared, shared, Str("x"), Atom(3));

        var observations = Observations();
        Assert.True(value.TryLanguageAtomsObserved(long.MaxValue, observations, out var atoms));

        // Atoms are collected once per PATH — that is the collector's contract — so the shared
        // atom-bearing node contributes twice; its second occurrence REPLAYS the run its first
        // descent recorded. Root, shared and inner are descended once each: 4 + 2 + 1 slots.
        Assert.Equal([1m, 2m, 1m, 2m, 3m], atoms);
        Assert.Equal(3, observations.LanguageAtomsStructureExpansionCount);
        Assert.Equal(1, observations.LanguageAtomsRunReplayCount);
        Assert.Equal(7, observations.LanguageAtomsSlotInspectionCount);
        Assert.Equal(0, observations.LanguageAtomsCancellationCheckpointCount);
    }

    [Fact]
    public void HostAtoms_AtomBearingSharedNodes_AreReplayedNotReDescended()
    {
        var inner = List(Atom(2));
        var shared = Seq(Atom(1), inner);
        var value = List(shared, shared, Str("x"), Atom(3));

        var observations = Observations();
        Assert.True(value.TryToHostAtomsObserved(long.MaxValue, observations, out var atoms));

        Assert.Equal([1m, 2m, 1m, 2m, 3m], atoms);
        Assert.Equal(3, observations.HostAtomsStructureExpansionCount);
        Assert.Equal(1, observations.HostAtomsRunReplayCount);
        Assert.Equal(7, observations.HostAtomsSlotInspectionCount);
        Assert.Equal(0, observations.HostAtomsCancellationCheckpointCount);
    }

    /// <summary>
    /// The audit's wide shape, built directly: <c>W = [1, true × (width - 1)]</c> and
    /// <c>D = [W × width]</c>. One atom per occurrence of W, so the output is <c>width</c> ones,
    /// but a per-occurrence walk reads all of W's slots at every occurrence — width² reads.
    /// </summary>
    private static Result WideSharedValue(int width, out Result shared)
    {
        var wideItems = new Result[width];
        wideItems[0] = Atom(1);
        for (var i = 1; i < width; i++)
            wideItems[i] = new Result.Bool(true);
        shared = List(wideItems);

        var outerItems = new Result[width];
        Array.Fill(outerItems, shared);
        return List(outerItems);
    }

    /// <summary>
    /// The audit's chain shape: <c>N0 = [1]</c>, <c>Nk = [N(k-1), true × width]</c> for k up to
    /// <paramref name="height"/>, and <c>D = [N(height) × repeats]</c>. Each chain node is reached
    /// once per occurrence of the top, so a per-occurrence walk re-reads the whole chain each time.
    /// </summary>
    private static Result SharedChainValue(int height, int width, int repeats)
    {
        var node = List(Atom(1));
        for (var level = 1; level <= height; level++)
        {
            var items = new Result[width + 1];
            items[0] = node;
            for (var i = 1; i <= width; i++)
                items[i] = new Result.Bool(true);
            node = List(items);
        }

        var outerItems = new Result[repeats];
        Array.Fill(outerItems, node);
        return List(outerItems);
    }

    /// <summary>
    /// The slots a per-OCCURRENCE walk would read: every slot of every structure on every path,
    /// computed in O(distinct nodes) by a reference-identity DP, never by walking the paths. On
    /// shapes with no atomless nested structure this is exactly the former collectors' work.
    /// </summary>
    private static long PerPathSlotReads(Result value)
    {
        var memo = new Dictionary<Result, long>(ReferenceEqualityComparer.Instance);
        return Reads(value);

        long Reads(Result node)
        {
            IReadOnlyList<Result> items;
            switch (node)
            {
                case Result.SequenceValue(var sequenceItems): items = sequenceItems; break;
                case Result.ListValue(var listItems): items = listItems; break;
                default: return 0;
            }

            if (memo.TryGetValue(node, out var known)) return known;
            long total = items.Count;
            foreach (var item in items)
                total += Reads(item);
            memo[node] = total;
            return total;
        }
    }

    [Fact]
    public void Collectors_WideSharedValue_ReadEachDistinctSlotOnce()
    {
        const int width = 10_000;
        var value = WideSharedValue(width, out _);
        var expected = Enumerable.Repeat((Decimal128)1, width).ToArray();
        // What the per-occurrence walk read before replay: width + width², about 1e8.
        Assert.Equal(width + (long)width * width, PerPathSlotReads(value));

        var language = Observations();
        Assert.True(value.TryLanguageAtomsObserved(long.MaxValue, language, out var languageAtoms));
        Assert.Equal(expected, languageAtoms);
        // D's slots plus W's slots, each read once; the other width - 1 occurrences replay W's
        // one-atom run. The bound the audit asks for is 2 × width + a constant.
        Assert.Equal(2L * width, language.LanguageAtomsSlotInspectionCount);
        Assert.True(language.LanguageAtomsSlotInspectionCount <= 2L * width + 16);
        Assert.Equal(2, language.LanguageAtomsStructureExpansionCount);
        Assert.Equal(width - 1, language.LanguageAtomsRunReplayCount);
        // Slot reads plus replayed atoms, one checkpoint per 256 units.
        Assert.Equal((2L * width + (width - 1)) / Result.ValueSemanticComparer.UnitsPerCharge,
            language.LanguageAtomsCancellationCheckpointCount);

        var host = Observations();
        Assert.True(value.TryToHostAtomsObserved(long.MaxValue, host, out var hostAtoms));
        Assert.Equal(expected, hostAtoms);
        Assert.Equal(2L * width, host.HostAtomsSlotInspectionCount);
        Assert.Equal(2, host.HostAtomsStructureExpansionCount);
        Assert.Equal(width - 1, host.HostAtomsRunReplayCount);
        Assert.Equal((2L * width + (width - 1)) / Result.ValueSemanticComparer.UnitsPerCharge,
            host.HostAtomsCancellationCheckpointCount);
    }

    [Fact]
    public void Collectors_SharedChain_WorkIsLinearInHeightTimesWidthPlusRepeats()
    {
        const int height = 16, width = 1_000, repeats = 1_000;
        var value = SharedChainValue(height, width, repeats);
        var expected = Enumerable.Repeat((Decimal128)1, repeats).ToArray();
        // Each chain level holds its child plus width Booleans; N0 holds one atom.
        long distinctSlots = (long)height * (width + 1) + 1 + repeats;
        // Before replay: every occurrence of the top re-read the whole chain.
        Assert.Equal(repeats + (long)repeats * (distinctSlots - repeats), PerPathSlotReads(value));

        var language = Observations();
        Assert.True(value.TryLanguageAtomsObserved(long.MaxValue, language, out var languageAtoms));
        Assert.Equal(expected, languageAtoms);
        Assert.Equal(distinctSlots, language.LanguageAtomsSlotInspectionCount);
        Assert.True(language.LanguageAtomsSlotInspectionCount <= (long)height * width + repeats + 64);
        Assert.Equal(height + 2, language.LanguageAtomsStructureExpansionCount);
        Assert.Equal(repeats - 1, language.LanguageAtomsRunReplayCount);

        var host = Observations();
        Assert.True(value.TryToHostAtomsObserved(long.MaxValue, host, out var hostAtoms));
        Assert.Equal(expected, hostAtoms);
        Assert.Equal(distinctSlots, host.HostAtomsSlotInspectionCount);
        Assert.True(host.HostAtomsSlotInspectionCount <= (long)height * width + repeats + 64);
        Assert.Equal(height + 2, host.HostAtomsStructureExpansionCount);
        Assert.Equal(repeats - 1, host.HostAtomsRunReplayCount);
    }

    [Fact]
    public void Collectors_ReplayAtTheAtomBound_AppendsExactlyTheRemainingRoom()
    {
        // W = [1, 2, 3] shared three times: 9 atoms. Every budget that ends inside a REPLAYED
        // occurrence must yield exactly the per-path prefix and a refusal.
        var shared = List(Atom(1), Atom(2), Atom(3));
        var value = Seq(shared, Atom(0), shared, shared);
        var naive = NaiveAtoms(value);
        Assert.Equal(10, naive.Count);

        for (long budget = 0; budget <= naive.Count + 1; budget++)
        {
            var fits = naive.Count <= budget;
            var prefix = naive.Take((int)Math.Min(budget, naive.Count)).ToArray();

            var language = Observations();
            Assert.Equal(fits, value.TryLanguageAtomsObserved(budget, language, out var languageAtoms));
            Assert.Equal(prefix, languageAtoms);

            var host = Observations();
            Assert.Equal(fits, value.TryToHostAtomsObserved(budget, host, out var hostAtoms));
            Assert.Equal(prefix, hostAtoms);

            // The shared list is descended at most once; a budget that lets the walk reach its
            // second occurrence (the first four atoms fit) replays it, the last replay possibly
            // truncated to the remaining room.
            Assert.Equal(budget >= 4, language.LanguageAtomsRunReplayCount > 0);
            Assert.Equal(budget >= 4, host.HostAtomsRunReplayCount > 0);
            Assert.True(language.LanguageAtomsStructureExpansionCount <= 2);
            Assert.True(host.HostAtomsStructureExpansionCount <= 2);
        }
    }

    // ── Collectors: seeded differential over random shared DAGs ──────────────────────────────

    /// <summary>
    /// A random shared DAG: a pool of leaves (atoms, strings, Booleans, empty structures) grows
    /// by sequence and list nodes whose children are drawn from the WHOLE pool, so later nodes
    /// share earlier ones at many depths. The last node is the root.
    /// </summary>
    private static Result RandomSharedDag(Random random)
    {
        var pool = new List<Result>
        {
            Atom(random.Next(-3, 10)),
            Atom(random.Next(-3, 10)),
            Str("s"),
            new Result.Bool(random.Next(2) == 0),
            Seq(),
            List(),
        };

        var nodes = random.Next(1, 12);
        for (var i = 0; i < nodes; i++)
        {
            var width = random.Next(0, 5);
            var items = new Result[width];
            for (var j = 0; j < width; j++)
            {
                // Bias towards recent nodes so the DAG gets depth, and towards fresh atoms so
                // runs have distinct contents.
                items[j] = random.Next(4) switch
                {
                    0 => Atom(random.Next(-3, 10)),
                    1 => pool[random.Next(Math.Max(0, pool.Count - 3), pool.Count)],
                    _ => pool[random.Next(pool.Count)],
                };
            }

            pool.Add(random.Next(2) == 0 ? Seq(items) : List(items));
        }

        return pool[^1];
    }

    /// <summary>Total slots of the distinct structures reachable from <paramref name="value"/>.</summary>
    private static long DistinctStructureSlots(Result value, out int distinctStructures)
    {
        var seen = new HashSet<Result>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<Result>();
        pending.Push(value);
        long slots = 0;
        while (pending.Count > 0)
        {
            var node = pending.Pop();
            IReadOnlyList<Result> items;
            switch (node)
            {
                case Result.SequenceValue(var sequenceItems): items = sequenceItems; break;
                case Result.ListValue(var listItems): items = listItems; break;
                default: continue;
            }

            if (!seen.Add(node)) continue;
            slots += items.Count;
            foreach (var item in items)
                pending.Push(item);
        }

        distinctStructures = seen.Count;
        return slots;
    }

    [Fact]
    public void Collectors_RandomSharedDags_MatchTheNaiveFlatteningAtEveryBudget()
    {
        var random = new Random(0x5EED_A70);
        var cases = 0;
        var replayedCases = 0;
        for (var trial = 0; trial < 2_000; trial++)
        {
            var value = RandomSharedDag(random);
            // Only values whose path expansion the naive oracle can afford.
            if (PerPathSlotReads(value) > 20_000) continue;

            var naive = NaiveAtoms(value);
            var total = naive.Count;
            var slots = DistinctStructureSlots(value, out var structures);
            long[] budgets = [0, 1, total - 1, total, total + 1, random.Next(0, total + 2)];
            foreach (var budget in budgets.Where(static b => b >= 0).Distinct())
            {
                cases++;
                var fits = total <= budget;
                var prefix = naive.Take((int)Math.Min(budget, total)).ToArray();

                var language = Observations();
                Assert.Equal(fits, value.TryLanguageAtomsObserved(budget, language, out var languageAtoms));
                Assert.Equal(prefix, languageAtoms);
                Assert.True(language.LanguageAtomsSlotInspectionCount <= slots);
                Assert.True(language.LanguageAtomsStructureExpansionCount <= structures);
                Assert.True(value.TryLanguageAtoms(budget, out var unobservedLanguage) == fits);
                Assert.Equal(prefix, unobservedLanguage);

                var host = Observations();
                Assert.Equal(fits, value.TryToHostAtomsObserved(budget, host, out var hostAtoms));
                Assert.Equal(prefix, hostAtoms);
                Assert.True(host.HostAtomsSlotInspectionCount <= slots);
                Assert.True(host.HostAtomsStructureExpansionCount <= structures);
                Assert.True(value.TryToHostAtoms(budget, out var unobservedHost) == fits);
                Assert.Equal(prefix, unobservedHost);

                if (language.LanguageAtomsRunReplayCount > 0) replayedCases++;
            }
        }

        // The generator must actually exercise sharing and replay, not only trees.
        Assert.True(cases > 2_000, $"only {cases} differential cases");
        Assert.True(replayedCases > 500, $"only {replayedCases} cases replayed a run");
    }

    // ── Collectors: host cancellation is observed DURING the walk, never charged ─────────────

    [Fact]
    public void HostAtoms_PreCancelledToken_ThrowsAtTheFirstCheckpointOfAWideWalk()
    {
        const int width = 10_000;
        var value = WideSharedValue(width, out _);
        using var source = new CancellationTokenSource();
        source.Cancel();

        var observations = Observations();
        var thrown = Assert.ThrowsAny<OperationCanceledException>(
            () => value.TryToHostAtomsObserved(long.MaxValue, observations, out _, source.Token));
        Assert.Equal(source.Token, thrown.CancellationToken);
        // Inside the walk, at its first checkpoint: never after reading every slot.
        Assert.Equal(1, observations.HostAtomsCancellationCheckpointCount);
        Assert.Equal(Result.ValueSemanticComparer.UnitsPerCharge, observations.HostAtomsSlotInspectionCount);
        Assert.True(observations.HostAtomsSlotInspectionCount <= Result.ValueSemanticComparer.UnitsPerCharge + width);
    }

    [Fact]
    public void LanguageAtoms_PreCancelledBudget_ThrowsAtTheFirstCheckpointOfAWideWalk()
    {
        const int width = 10_000;
        var value = WideSharedValue(width, out _);
        using var source = new CancellationTokenSource();
        source.Cancel();
        var budget = KatLang.Evaluation.EvaluationBudget.Create(null, cancellationToken: source.Token);

        var observations = Observations();
        var thrown = Assert.ThrowsAny<OperationCanceledException>(
            () => value.TryLanguageAtomsObserved(long.MaxValue, observations, out _, budget));
        Assert.Equal(source.Token, thrown.CancellationToken);
        Assert.Equal(1, observations.LanguageAtomsCancellationCheckpointCount);
        Assert.Equal(Result.ValueSemanticComparer.UnitsPerCharge, observations.LanguageAtomsSlotInspectionCount);
        Assert.True(observations.LanguageAtomsSlotInspectionCount <= Result.ValueSemanticComparer.UnitsPerCharge + width);

        // Observing charges nothing.
        Assert.Equal(0, budget.ConsumedSteps);
        Assert.Equal(0, budget.ConsumedStructuralWorkUnits);
    }

    [Fact]
    public void Collectors_ReplayedAtomsCountTowardsTheCheckpoint()
    {
        // 3 + 100 slot reads never reach 256 on their own; the two replays of W's 100-atom run
        // do, so the checkpoint falls during the SECOND replay.
        var shared = List(Enumerable.Range(0, 100).Select(static i => Atom(i)).ToArray());
        var value = List(shared, shared, shared);

        var language = Observations();
        Assert.True(value.TryLanguageAtomsObserved(long.MaxValue, language, out var languageAtoms));
        Assert.Equal(300, languageAtoms.Count);
        Assert.Equal(103, language.LanguageAtomsSlotInspectionCount);
        Assert.Equal(1, language.LanguageAtomsCancellationCheckpointCount);

        using var source = new CancellationTokenSource();
        source.Cancel();
        var host = Observations();
        Assert.ThrowsAny<OperationCanceledException>(
            () => value.TryToHostAtomsObserved(long.MaxValue, host, out _, source.Token));
        Assert.Equal(103, host.HostAtomsSlotInspectionCount);
        Assert.Equal(2, host.HostAtomsRunReplayCount);
        Assert.Equal(1, host.HostAtomsCancellationCheckpointCount);

        var budget = KatLang.Evaluation.EvaluationBudget.Create(null, cancellationToken: source.Token);
        var cancelledLanguage = Observations();
        Assert.ThrowsAny<OperationCanceledException>(
            () => value.TryLanguageAtomsObserved(long.MaxValue, cancelledLanguage, out _, budget));
        Assert.Equal(103, cancelledLanguage.LanguageAtomsSlotInspectionCount);
        Assert.Equal(2, cancelledLanguage.LanguageAtomsRunReplayCount);
    }

    [Theory]
    [InlineData(100, 30, int.MaxValue)]
    [InlineData(1_000, 2, int.MaxValue)]
    [InlineData(1_000, 4, int.MaxValue)]
    [InlineData(1_000, 4, 1_500)]
    [InlineData(1_000, 4, 2_000)]
    [InlineData(256, 5, int.MaxValue)]
    public void Collectors_ReplayCancellationCadence_PreservesEvery256UnitBoundary(
        int width, int repeats, int maxItems)
    {
        var shared = List(Enumerable.Range(0, width).Select(static i => Atom(i)).ToArray());
        var value = List(Enumerable.Repeat(shared, repeats).ToArray());
        var naive = NaiveAtoms(value);
        var fits = naive.Count <= maxItems;
        var outputCount = Math.Min(naive.Count, maxItems);
        var prefix = naive.Take(outputCount).ToArray();
        // The first occurrence reads width slots; each later one copies width atoms. A
        // refusal also reads the slot for the occurrence whose next atom would exceed the
        // bound, including when the preceding replay exactly filled the available room.
        var slots = width + (fits ? repeats : maxItems / width + 1L);
        var copiedAtoms = outputCount - width;
        var checkpoints = (slots + copiedAtoms) / Result.ValueSemanticComparer.UnitsPerCharge;

        var language = Observations();
        var budget = KatLang.Evaluation.EvaluationBudget.Create(null);
        Assert.Equal(fits, value.TryLanguageAtomsObserved(maxItems, language, out var languageAtoms, budget));
        Assert.Equal(prefix, languageAtoms);
        Assert.Equal(slots, language.LanguageAtomsSlotInspectionCount);
        Assert.Equal(checkpoints, language.LanguageAtomsCancellationCheckpointCount);
        Assert.Equal(0, budget.ConsumedSteps);
        Assert.Equal(0, budget.ConsumedStructuralWorkUnits);
        Assert.Equal(0, budget.MaterializedItems);

        var host = Observations();
        Assert.Equal(fits, value.TryToHostAtomsObserved(maxItems, host, out var hostAtoms));
        Assert.Equal(prefix, hostAtoms);
        Assert.Equal(slots, host.HostAtomsSlotInspectionCount);
        Assert.Equal(checkpoints, host.HostAtomsCancellationCheckpointCount);
    }

    [Fact]
    public void Collectors_UncancelledTokenAndBudget_AreInert()
    {
        var value = SharedChainValue(4, 300, 50);
        using var source = new CancellationTokenSource();
        var budget = KatLang.Evaluation.EvaluationBudget.Create(null, cancellationToken: source.Token);

        Assert.True(value.TryLanguageAtoms(long.MaxValue, out var plainLanguage));
        Assert.True(value.TryLanguageAtoms(long.MaxValue, out var budgetedLanguage, budget));
        Assert.Equal(plainLanguage, budgetedLanguage);
        Assert.Equal(0, budget.ConsumedSteps);
        Assert.Equal(0, budget.ConsumedStructuralWorkUnits);
        Assert.Equal(0, budget.MaterializedItems);

        Assert.True(value.TryToHostAtoms(long.MaxValue, out var plainHost));
        Assert.True(value.TryToHostAtoms(long.MaxValue, out var tokenHost, source.Token));
        Assert.Equal(plainHost, tokenHost);
        Assert.Equal(NaiveAtoms(value), tokenHost);
    }

    [Fact]
    public void LanguageAtoms_AtomlessSkipDoesNotSuppressAtomsElsewhere()
    {
        var atomlessShared = List(Str("s"), Seq(Str("t")));
        var value = Seq(atomlessShared, List(atomlessShared, Atom(5)), atomlessShared, Atom(6));

        var observations = Observations();
        Assert.True(value.TryLanguageAtomsObserved(long.MaxValue, observations, out var atoms));

        // The atomless node is searched once and skipped twice; the atoms around it survive in
        // flattening order. Root + atomless node + its inner sequence + the middle list.
        Assert.Equal([5m, 6m], atoms);
        Assert.Equal(4, observations.LanguageAtomsStructureExpansionCount);
    }

    [Fact]
    public void Collectors_ValueEqualButDistinctAtomlessNodes_AreDistinctMemoEntries()
    {
        // Value-equal but reference-distinct: both must be descended.
        var left = List(Str("s"));
        var right = List(Str("s"));
        Assert.True(Result.ValueComparer.Equals(left, right));
        Assert.False(ReferenceEquals(left, right));

        var observations = Observations();
        Assert.True(List(left, right, Atom(1)).TryLanguageAtomsObserved(long.MaxValue, observations, out var atoms));
        Assert.Equal([1m], atoms);
        Assert.Equal(3, observations.LanguageAtomsStructureExpansionCount);

        // A default-record-equal clone (shared wrapper) is still a DISTINCT memo entry: a memo
        // using generated record equality would skip it.
        var original = Assert.IsType<Result.ListValue>(List(Str("s")));
        var clone = original with { };
        Assert.NotSame(original, clone);
        Assert.True(original.Equals(clone));

        var cloneObservations = Observations();
        Assert.True(List(original, clone, Atom(1)).TryToHostAtomsObserved(long.MaxValue, cloneObservations, out var cloneAtoms));
        Assert.Equal([1m], cloneAtoms);
        Assert.Equal(3, cloneObservations.HostAtomsStructureExpansionCount);
    }

    // ── Collectors: the atom bound is unchanged, and visits stay bounded beside it ───────────

    [Fact]
    public void LanguageAtoms_AtomBoundStopsCollection_WithTheExactPrefix()
    {
        // 2^4 leaf paths over (1, 2): 32 atoms alternating 1, 2, 1, 2, ...
        var value = SharedListDag(4, List(Atom(1), Atom(2)));

        Assert.False(value.TryLanguageAtoms(3, out var truncated));
        Assert.Equal([1m, 2m, 1m], truncated);

        Assert.False(value.TryLanguageAtoms(31, out _));
        Assert.True(value.TryLanguageAtoms(32, out var full));
        Assert.Equal(32, full.Count);
        Assert.Equal(NaiveAtoms(value), full);

        // The pre-existing edge stays: a zero budget rejects even a lone atom.
        Assert.False(Atom(7).TryLanguageAtoms(0, out var none));
        Assert.Empty(none);
    }

    [Fact]
    public void HostAtoms_AtomBoundStopsCollection_WithTheExactPrefix()
    {
        var value = SharedSeqDag(4, Seq(Atom(1), Atom(2)));

        Assert.False(value.TryToHostAtoms(3, out var truncated));
        Assert.Equal([1m, 2m, 1m], truncated);

        Assert.True(value.TryToHostAtoms(32, out var full));
        Assert.Equal(NaiveAtoms(value), full);
    }

    [Fact]
    public void Collectors_AtomBoundEdges_AreUnchangedAroundSharedAtomlessStructures()
    {
        var atomless = SharedMixedDag(8, Str("s"));
        var value = Seq(Seq(), atomless, List(Seq()), Atom(1), atomless, Atom(2));

        Assert.True(atomless.TryLanguageAtoms(0, out var emptyLanguage));
        Assert.Empty(emptyLanguage);
        Assert.False(value.TryLanguageAtoms(0, out var zeroLanguage));
        Assert.Empty(zeroLanguage);
        Assert.False(value.TryLanguageAtoms(1, out var oneLanguage));
        Assert.Equal([1m], oneLanguage);
        Assert.True(value.TryLanguageAtoms(2, out var exactLanguage));
        Assert.Equal([1m, 2m], exactLanguage);

        Assert.True(atomless.TryToHostAtoms(0, out var emptyHost));
        Assert.Empty(emptyHost);
        Assert.False(value.TryToHostAtoms(0, out var zeroHost));
        Assert.Empty(zeroHost);
        Assert.False(value.TryToHostAtoms(1, out var oneHost));
        Assert.Equal([1m], oneHost);
        Assert.True(value.TryToHostAtoms(2, out var exactHost));
        Assert.Equal([1m, 2m], exactHost);
    }

    [Fact]
    public void Collectors_MatchTheNaiveFlattening_AcrossEveryValueShape()
    {
        foreach (var value in Corpus())
        {
            Assert.True(value.TryLanguageAtoms(long.MaxValue, out var languageAtoms));
            Assert.Equal(NaiveAtoms(value), languageAtoms);

            Assert.True(value.TryToHostAtoms(long.MaxValue, out var hostAtoms));
            Assert.Equal(NaiveAtoms(value), hostAtoms);
        }
    }

    // ── Language-level regressions for the public funnels ────────────────────────────────────

    /// <summary>
    /// The sequence doubling DAG built by an ordinary in-budget loop — the SEQUENCE sibling of
    /// the <c>Wrap = [x, x]</c> recipe the other shared-graph suites use, because the value operations
    /// exercised here open sequence boundaries: <c>Wrap</c> stores its ONE bound argument in both slots of
    /// one written group, so each step adds one sequence node reachable through twice as many
    /// paths.
    /// </summary>
    private static string SeqDagProgram(string body, string leaf = "1", int depth = DeepDepth)
        => $"""
            Wrap = (x, x)
            D = Wrap({leaf}).repeat({depth})
            {body}
            """;

    /// <summary>
    /// STRICT-SOURCE: requires a clean front end, then runs the PLAIN and the COUNTED evaluator
    /// and requires both to agree — the fixes live at the Result level, so neither entry point
    /// may observe a different verdict.
    /// </summary>
    private static void AssertEval(string source, params Decimal128[] expected)
    {
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

        var plain = Evaluator.RunFlat(expr);
        if (plain.IsError)
            Assert.Fail($"Expected success but got error: {plain.Error}");
        Assert.Equal(expected, plain.Value);

        var counted = Evaluator.RunCounted(expr);
        if (counted.IsError)
            Assert.Fail($"Expected counted success but got error: {counted.Error}");
        Assert.Equal(expected, counted.Value.Value.ToHostAtoms());
    }

    private static void AssertEvalError<TError>(string source)
        where TError : EvalError
    {
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

        var plain = Evaluator.Run(expr);
        Assert.True(plain.IsError, "Expected an error from the plain evaluator.");
        Assert.IsType<TError>(Innermost(plain.Error));

        var counted = Evaluator.RunCounted(expr);
        Assert.True(counted.IsError, "Expected an error from the counted evaluator.");
        Assert.IsType<TError>(Innermost(counted.Error));
    }

    private static EvalError Innermost(EvalError error)
        => error is EvalError.WithContext(_, var inner) ? Innermost(inner) : error;

    [Fact]
    public void LanguageBuiltDoublingSequenceIsOneSharedGraph()
    {
        // The premise of every case below: the loop builds a sequence DAG, not a tree. Without
        // sharing the depth-40 values would be 2^40 nodes and could not be built at all.
        var expr = new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid("Wrap = (x, x)\nWrap(1).repeat(3)").Root);

        var plain = Evaluator.Run(expr);
        if (plain.IsError)
            Assert.Fail($"Expected success but got error: {plain.Error}");
        var sequence = Assert.IsType<Result.SequenceValue>(plain.Value);
        Assert.Same(sequence.Items[0], sequence.Items[1]);
        var inner = Assert.IsType<Result.SequenceValue>(sequence.Items[0]);
        Assert.Same(inner.Items[0], inner.Items[1]);

        var counted = Evaluator.RunCounted(expr);
        if (counted.IsError)
            Assert.Fail($"Expected counted success but got error: {counted.Error}");
        var countedSequence = Assert.IsType<Result.SequenceValue>(counted.Value.Value);
        Assert.Same(countedSequence.Items[0], countedSequence.Items[1]);
    }

    [Fact]
    public void IfOnSharedDag_IsRejectedAsNonBooleanWithoutTraversingTheGraph()
        // The H2 repro shape: a 2^40-atom DAG in the condition slot. There is no truth
        // search any more — a sequence value is not a Boolean — so the rejection is decided
        // from the value's kind alone, and the operand description that names the value is
        // produced by the bounded diagnostic renderer, never by a path walk.
        => AssertEvalError<EvalError.TypeMismatch>(SeqDagProgram("if(D, 1, 0)"));

    [Fact]
    public void IfOnAtomlessSharedDag_IsRejectedTheSameWay()
        // No atom anywhere: the kind rule does not care, and deciding it is still
        // distinct-node work, not path work.
        => AssertEvalError<EvalError.TypeMismatch>(SeqDagProgram("if(D, 1, 0)", leaf: "'s'"));

    [Fact]
    public void IfOnSharedDagEquality_IsTrue()
        // A Boolean condition OVER the DAG: structural equality is DAG-bounded, so the
        // condition is decided without materializing the 2^40 atoms.
        => AssertEval(SeqDagProgram("if(D == D, 1, 0)"), 1);

    [Fact]
    public async Task IfOnSharedDag_AsyncTwinAgrees()
    {
        var expr = new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid(SeqDagProgram("if(D == D, 1, 0)")).Root);

        // An async-capable cache is the routing signal for the actual async twin family. The
        // public no-configuration RunFlatAsync overload intentionally takes the synchronous fast
        // path, so using it here would not test the async `if` implementation.
        var result = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedAsync(expr, new PassThroughAsyncZeroArgPropertyResultCache()));
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal([1m], result.Value.Value.ToHostAtoms());
    }

    [Fact]
    public void IfOnSharedDag_OptimizedLoopPlansTheBooleanCondition()
    {
        var source = SeqDagProgram("""
            Outer(d) = {
                Step(n) = if(d == d, n + 1, n)
                Step(0).repeat(1)
            }
            Outer(D)
            """);
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var diagnostics = new LoopOptimizationDiagnostics();

        var optimized = Evaluator.Run(
            expr,
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true,
            diagnostics);
        if (optimized.IsError)
            Assert.Fail($"Expected optimized success but got error: {optimized.Error}");
        Assert.Equal([1m], optimized.Value.ToHostAtoms());

        var snapshot = diagnostics.GetSnapshot();
        Assert.True(
            snapshot.OptimizedLoopHits == 2,
            $"Unexpected optimizer routing: {snapshot}; reasons={string.Join("; ", snapshot.FallbackReasons)}; " +
            $"plans={string.Join("; ", snapshot.LoopPlans)}");
        // The Wrap loop that builds D deliberately falls back for its capture expression. The
        // Step loop itself is wholly planned; these totals prove it introduced no second fallback.
        Assert.Equal(1, snapshot.PlannedExpressionFallbacks);
        Assert.Equal(1, snapshot.GenericExpressionEvaluationsInsideOptimizedLoops);
        var plan = Assert.Single(snapshot.LoopPlans, candidate => candidate.Identity == "Outer.Step.repeat");
        var output = Assert.Single(
            plan.Expressions,
            expression => expression.Role == "output" && expression.Index == 0);
        Assert.Equal(
            "If(Equal(CapturedSlot(d), CapturedSlot(d)), Add(StateSlot(n), Const(1)), StateSlot(n))",
            output.PlanSummary);

        var generic = Evaluator.Run(
            expr,
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: false);
        if (generic.IsError)
            Assert.Fail($"Expected generic success but got error: {generic.Error}");
        Assert.Equal(generic.Value, optimized.Value, Result.ValueComparer);
    }

    [Fact]
    public void AtomsBuiltinOnAtomlessSharedDag_IsEmptyQuickly()
        // TryLanguageAtoms collects nothing here, so its atom bound never fires: only the
        // atomless-node memo keeps this from re-walking the graph per path.
        => AssertEval(SeqDagProgram("atoms(D).count", leaf: "'s'"), 0);

    [Fact]
    public void AtomsBuiltinOnAtomBearingSharedDag_HitsTheCollectionLimit()
        // 2^40 atoms exceed every collection budget: the pre-existing bounded-traversal abort
        // is preserved, and the walk stays bounded on the way to it.
        => AssertEvalError<EvalError.CollectionSizeLimitExceeded>(SeqDagProgram("atoms(D)"));

    [Fact]
    public void RunFlatOnAtomlessSharedDag_ProjectsNoAtomsQuickly()
    {
        var expr = new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid(SeqDagProgram("D", leaf: "'s'")).Root);

        var flat = Evaluator.RunFlat(expr);
        if (flat.IsError)
            Assert.Fail($"Expected success but got error: {flat.Error}");
        Assert.Empty(flat.Value);

        // The unbounded public host projection over the same value is node-bounded too.
        var counted = Evaluator.RunCounted(expr);
        if (counted.IsError)
            Assert.Fail($"Expected counted success but got error: {counted.Error}");
        Assert.Empty(counted.Value.Value.ToHostAtoms());
    }

    /// <summary>
    /// The audit's program: <c>D</c> holds 40,000 references to ONE <c>W</c> of one atom and
    /// 39,999 Booleans. A per-occurrence walk of D reads 1.6e9 slots — about 30 s inside one
    /// <c>atoms</c> step, and again in the engine's eager host projection of a root <c>D</c> —
    /// while every evaluation limit, even a 200,000-step budget, sees a small program.
    /// </summary>
    private const string AuditWideProgram = """
        F(i) = true
        T = map(range(1, 39999), F)
        W = [1, T*]
        K(i) = W
        D = map(range(1, 40000), K)
        """;

    private const int AuditWidth = 40_000;

    private static EvaluationLimits AuditLimits => new() { MaxSteps = 200_000 };

    [Fact]
    public void Engine_AtomsBuiltinOverTheAuditWideValue_ReplaysTheSharedRow()
    {
        var source = AuditWideProgram + "\ncount(atoms(D))";
        var success = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run(source, new RunOptions { EvaluationLimits = AuditLimits }));
        Assert.Equal([(Decimal128)AuditWidth], success.Atoms);

        // The same program through the observed evaluator: the atoms builtin records into the
        // run's structural observer. D's slots and W's slots are read once each; the other
        // occurrences of W replay its one-atom run.
        var traversal = Observations();
        var observed = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root),
            AuditLimits,
            observations: new EvaluationObservations { StructuralTraversal = traversal });
        if (observed.Result.IsError)
            Assert.Fail($"Expected success but got error: {observed.Result.Error}");
        Assert.Equal([(Decimal128)AuditWidth], observed.Result.Value.Value.ToHostAtoms());
        Assert.Equal(2L * AuditWidth, traversal.LanguageAtomsSlotInspectionCount);
        Assert.Equal(2, traversal.LanguageAtomsStructureExpansionCount);
        Assert.Equal(AuditWidth - 1, traversal.LanguageAtomsRunReplayCount);
        Assert.Equal(
            (2L * AuditWidth + (AuditWidth - 1)) / Result.ValueSemanticComparer.UnitsPerCharge,
            traversal.LanguageAtomsCancellationCheckpointCount);
    }

    [Fact]
    public void Engine_HostProjectionOfTheAuditWideValue_ReplaysTheSharedRow()
    {
        var success = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run(AuditWideProgram + "\nD", new RunOptions { EvaluationLimits = AuditLimits }));
        Assert.Equal(Enumerable.Repeat((Decimal128)1, AuditWidth), success.Atoms);

        // The engine's own projection carries no observer; re-project the very value it
        // projected through the observed twin. It is one list of 40,000 references to one W.
        var root = Assert.IsType<Result.ListValue>(success.Value);
        Assert.Equal(AuditWidth, root.Items.Count);
        Assert.All(root.Items, item => Assert.Same(root.Items[0], item));
        Assert.Equal(AuditWidth + (long)AuditWidth * AuditWidth, PerPathSlotReads(success.Value));

        var host = Observations();
        Assert.True(success.Value.TryToHostAtomsObserved(
            EvaluationLimits.Default.EffectiveMaxCollectionItems, host, out var atoms));
        Assert.Equal(success.Atoms, atoms);
        Assert.Equal(2L * AuditWidth, host.HostAtomsSlotInspectionCount);
        Assert.Equal(2, host.HostAtomsStructureExpansionCount);
        Assert.Equal(AuditWidth - 1, host.HostAtomsRunReplayCount);
    }

    [Fact]
    public void RunFlatOnAtomBearingSharedDag_HitsTheCollectionLimit()
    {
        // Evaluation itself succeeds — the value is a compact DAG — and the bounded host
        // projection reports the same limit error it always did, without path-expanding first.
        var expr = new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid(SeqDagProgram("D")).Root);

        var flat = Evaluator.RunFlat(expr);
        Assert.True(flat.IsError, "Expected the host projection to hit the collection limit.");
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>(flat.Error);
    }
}
