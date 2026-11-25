using System.Globalization;
using System.Reflection;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// DECONSTRUCTION-MEMO PROMPT RECLAIM (2026-11-18; C#-only storage, implementation-only, Lean unchanged): the
/// deconstruction shared-bind memo (<see cref="RunScopedDeconstructionBindingCache"/>) and the seen-key statistics of
/// <see cref="UncachedZeroArgPropertyResultCache.CreateForRun"/> keep their binding-context partitions in the
/// PROMPT-RECLAIM form of <see cref="BindingContextPartitionTable"/>, like the property cache since 2026-11-17. That
/// form is sequential and takes no lock: the memo relies on a run being ONE evaluation flow, which an async
/// continuation may move to another thread only after the previous table operation returned.
/// <para>These tests drive that model through <see cref="RunScopedDeconstructionBindingCache.GetOrBindAsync"/>:
/// several independent memos at once, each a sequential flow that reads a partition on two threads and suspends
/// inside owning binds while collections clear dead identities. The flows bind, hit, nest, fail and cancel. Every
/// bind, stored bind and hit is the one the memo's store invariant gives, no bind a live execution can name is lost,
/// dead partitions leave the table, and the table stays far smaller than the identities that passed through it. In
/// DEBUG builds the table also fails loudly if two operations ever overlap.</para>
/// </summary>
public sealed class DeconstructionMemoPromptReclaimTests(ITestOutputHelper output)
{
    private const int Flows = 8;
    private const int Rounds = 4_096;
    private const int KeepEvery = 128;
    private const int CollectEvery = 256;

    [Fact]
    public void TheDeconstructionMemoAndTheUncachedStatistics_UseThePromptReclaimTable()
    {
        // Every partition table is the prompt-reclaim form since 2026-11-20 (the ConditionalWeakTable form, which
        // reported a capacity of 0, was removed); a capacity pins that the store keeps its entries in one.
        Assert.True(new RunScopedDeconstructionBindingCache().PromptTableCapacity > 0);
        Assert.True(UncachedZeroArgPropertyResultCache.CreateForRun().PromptTableCapacity > 0);
        Assert.Equal(0, UncachedZeroArgPropertyResultCache.Instance.PromptTableCapacity); // no statistics, no table

        // The memo a run constructs for itself.
        var observations = new EvaluationObservations();
        var parsed = Parser.Parse("a, b = 1, 2\na + b");
        Assert.False(parsed.HasErrors);
        var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), observations: observations);
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        Assert.True(observations.DeconstructionBindingCache!.PromptTableCapacity > 0);
    }

    [Fact]
    public async Task AsyncMemo_BindsHitsAndDropsPartitions_FromSeveralThreads()
    {
        var reports = await Task.WhenAll(Enumerable.Range(0, Flows).Select(_ => Task.Run(RunFlowAsync)));
        ForceFullCollection();

        foreach (var report in reports)
        {
            var flow = report.Flow;
            var live = flow.Memo.LivePartitionCount();
            output.WriteLine(
                $"flow: {flow.Threads.Count} threads, {flow.Binds} binds, {flow.Memo.Count} stored, "
                + $"table capacity {report.Capacity} after {Rounds} identities, {live} live partitions ({report.Kept.Count} kept)");

            // The sequential flow really moved between threads.
            Assert.True(flow.Threads.Count >= 2, $"one flow ran on {flow.Threads.Count} thread(s)");
            Assert.Equal(flow.ExpectedBinds, flow.Binds);
            Assert.Equal(flow.ExpectedStored, flow.Memo.Count);
            Assert.Equal(0, flow.Memo.RunningExecutionCount);
            // Dead identities were freed in place: the table never held all of them.
            Assert.InRange(report.Capacity, 8, Rounds / 2);
            // Only the kept identities still own partitions (a straggler or two may await its collection).
            Assert.InRange(live, report.Kept.Count, report.Kept.Count + 2);

            // No bind a live execution can name was lost: every kept identity still hits its three stored binds.
            foreach (var kept in report.Kept)
            {
                Assert.Same(kept.Owned, await flow.HitAsync(flow.Owned(kept.Identity)));
                Assert.Same(kept.Nested, await flow.HitAsync(flow.Nested(kept.Identity)));
                Assert.Same(kept.OtherGroup, await flow.HitAsync(flow.OtherGroup(kept.Identity)));
            }

            Assert.Same(flow.ExportedBind, await flow.HitAsync(flow.Exported()));
            GC.KeepAlive(report.Kept);
        }
    }

    /// <summary>
    /// Four independent async runs of a loop whose every step's deconstruction source suspends its run inside the
    /// shared bind. The collection cadence is the PROGRAM's, not the host's: every 1,024 steps each run forces a full
    /// collection and samples its memo — one stored bind per completed step, no owning bind running, a few live
    /// partitions — and a probe after the loop does the same, so the table's capacity follows from the program and the
    /// table's growth rule. Without those collections it followed the host's gen-0 budget: on one Windows machine
    /// (2026-11-23) 256 entries by default, 512 and 1,024 with a 64 and a 256 MiB gen-0 size, and 4,096 under server
    /// GC, against an old bound of half the steps. (The collections are full ones, so they are sparse: forced every 256
    /// steps, they took the test from 3 to 48 seconds.)
    /// </summary>
    [Fact]
    public async Task ConcurrentAsyncRuns_OfALoopWithALocalDeconstructionThatSuspendsEveryStep_DropTheirPartitions()
    {
        const int runs = 4;
        const int steps = 20_000;
        const int collectEvery = 1_024;
        const int survivors = 64;
        var outcomes = await Task.WhenAll(Enumerable.Range(0, runs).Select(_ => Task.Run(async () =>
        {
            var observations = new EvaluationObservations();
            var samples = new List<(int Stored, int Running, int Live)>();
            (int Stored, int Running, int Live)? final = null;
            var hops = 0;
            var operations = HostOperations.Create(
                // Every step's deconstruction source suspends the run inside the shared bind: GetOrBindAsync's
                // continuation, and with it the bind's addition to the table, may resume on another thread.
                HostOperation.CreateAsync("hop", async (_, _) =>
                {
                    hops++;
                    await Task.Yield();
                    return new Result.Atom(0);
                }),
                // Every collectEvery steps, one blocking full collection: it clears every dead identity's handle (no
                // finalizer is involved). A young-generation collection, which the flows above take, does not suffice
                // here: forced every 256 steps under server GC, one left 257 live partitions (2026-11-23).
                HostOperation.CreateAsync("collect", async (_, _) =>
                {
                    await Task.Yield();
                    GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
                    samples.Add(Sample(observations.DeconstructionBindingCache!));
                    return new Result.Atom(0);
                }),
                HostOperation.CreateAsync("probe", async (_, _) =>
                {
                    await Task.Yield();
                    ForceFullCollection();
                    final = Sample(observations.DeconstructionBindingCache!);
                    return new Result.Atom(0);
                }));
            // A collection every collectEvery steps, after the step's bind is stored, and a probe after the loop.
            var source = "Step(x) = { a, b = x + 1 + hop() * 0, x\n"
                + "a + b * 0 + if((x + 1) mod " + collectEvery.ToString(CultureInfo.InvariantCulture) + " == 0, collect(), 0) }\n"
                + "Step(0).repeat(" + steps.ToString(CultureInfo.InvariantCulture) + ") + probe() * 0";
            var parsed = await SourceProvenance.ParseValidAsync(source, new RunOptions { HostOperations = operations });
            var (result, _) = await Evaluator.RunCountedObservedAsync(
                new Expr.AlgorithmExpr(parsed.Root),
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                observations: observations,
                hostOperations: operations);
            var memo = observations.DeconstructionBindingCache!;
            return (Result: result, Stored: memo.Count, FullBinds: observations.DeconstructionFullBindCount,
                Capacity: memo.PromptTableCapacity, Hops: hops, Samples: samples, Final: final);
        })));

        foreach (var outcome in outcomes)
        {
            output.WriteLine($"run: {outcome.Stored} stored binds, {outcome.FullBinds} full binds, {outcome.Hops} suspensions, "
                + $"table capacity {outcome.Capacity}, at most {outcome.Samples.Select(static sample => sample.Live).DefaultIfEmpty(-1).Max()} live partitions "
                + $"in {outcome.Samples.Count} collections, {outcome.Final?.Live} at the probe");
            Assert.True(outcome.Result.IsOk, outcome.Result.IsError ? outcome.Result.Error.ToString() : "");
            Assert.Equal(steps.ToString(CultureInfo.InvariantCulture), SixRouteAgreement.Neutral(outcome.Result.Value.Value));
            // Every step suspended once inside its bind.
            Assert.Equal(steps, outcome.Hops);
            // One stored bind per step, which the step's second target reads instead of binding again.
            Assert.Equal(steps, outcome.Stored);
            Assert.Equal(steps, outcome.FullBinds);
            Assert.Equal(steps / collectEvery, outcome.Samples.Count);
            for (var i = 0; i < outcome.Samples.Count; i++)
            {
                var (stored, running, live) = outcome.Samples[i];
                Assert.Equal((i + 1) * collectEvery, stored);
                Assert.Equal(0, running);
                Assert.InRange(live, 0, survivors);
            }

            Assert.Equal((steps, 0), (outcome.Final!.Value.Stored, outcome.Final.Value.Running));
            Assert.InRange(outcome.Final.Value.Live, 0, survivors);
            // At most collectEvery identities minted since the last collection, plus up to `survivors` that outlived
            // it, are alive when the table fills (1,088). The power-of-two table doubles only if more than half its
            // entries are alive, so it stops at 4,096 whatever the host's GC configuration.
            Assert.InRange(outcome.Capacity, 8, 4_096);
        }
    }

    private static (int Stored, int Running, int Live) Sample(RunScopedDeconstructionBindingCache memo)
        => (memo.Count, memo.RunningExecutionCount, memo.LivePartitionCount());

    // ── One sequential flow: one memo, used from whatever thread its continuations reach ──

    private sealed record Kept(
        object Identity,
        IReadOnlyDictionary<string, NeedCell> Owned,
        IReadOnlyDictionary<string, NeedCell> Nested,
        IReadOnlyDictionary<string, NeedCell> OtherGroup);

    private sealed record FlowReport(Flow Flow, List<Kept> Kept, int Capacity);

    private static async Task<FlowReport> RunFlowAsync()
    {
        var flow = new Flow();
        await flow.BindExportedAsync();
        var kept = new List<Kept>();
        for (var round = 0; round < Rounds; round++)
        {
            // The round's identity lives in the round's own state machine, so it dies when the round ends
            // unless the round returns it to be kept.
            if (await flow.RoundAsync(round, keep: round % KeepEvery == 0) is { } identity)
                kept.Add(identity);
            if (round % CollectEvery == CollectEvery - 1)
                GC.Collect(1, GCCollectionMode.Forced, blocking: true);
        }

        return new FlowReport(flow, kept, flow.Memo.PromptTableCapacity);
    }

    private sealed class Flow
    {
        private readonly object _run = new();
        private readonly object _owner = new();
        // One group's actual pattern list, and its source bindings: the group's own source, and a second source a
        // nested bind of the same group reads — another execution, as a recursive owner's inner activation is.
        private readonly object _group = new();
        private readonly object _pattern = new();
        private readonly object _source = new();
        private readonly object _nestedSource = new();
        // A second group, bound inside the first group's running bind (so it is stored), and a group that fails or
        // is cancelled.
        private readonly object _otherGroup = new();
        private readonly object _otherPattern = new();
        private readonly object _failingGroup = new();
        private readonly object _exportedGroup = new();

        internal RunScopedDeconstructionBindingCache Memo { get; } = new();
        internal HashSet<int> Threads { get; } = [];
        internal IReadOnlyDictionary<string, NeedCell>? ExportedBind { get; private set; }
        internal int Binds { get; private set; }
        internal int ExpectedBinds { get; private set; }
        internal int ExpectedStored { get; private set; }

        internal DeconstructionBindingExecution Owned(object identity) => new(_group, _pattern, Key(_source, identity));

        internal DeconstructionBindingExecution OtherGroup(object identity) => new(_otherGroup, _otherPattern, Key(_source, identity));

        internal DeconstructionBindingExecution Exported()
            => new(_exportedGroup, _pattern, Key(_source, ZeroArgPropertyCacheKey.RunWideEnvironmentIdentity));

        internal DeconstructionBindingExecution Nested(object identity) => new(_group, _pattern, Key(_nestedSource, identity));

        private DeconstructionBindingExecution Failing(object identity) => new(_failingGroup, _pattern, Key(_source, identity));

        private ZeroArgPropertyCacheKey Key(object binding, object identity) => new(_owner, binding, identity, _run);

        internal async Task<IReadOnlyDictionary<string, NeedCell>> HitAsync(DeconstructionBindingExecution execution)
        {
            var hit = await Memo.GetOrBindAsync(execution, MustHit);
            Assert.True(hit.IsOk);
            return hit.Value;
        }

        internal async Task BindExportedAsync()
        {
            ExportedBind = Value(await Memo.GetOrBindAsync(Exported(), () => Bind(-7)));
            ExpectedBinds++;
            ExpectedStored++;
        }

        /// <summary>One loop step's binding context: returns what the step kept, only when it is kept.</summary>
        internal async Task<Kept?> RoundAsync(int round, bool keep)
        {
            var identity = new object();
            Note();

            // An owning bind that suspends and, while it runs, binds ITSELF again (re-entrant: never stored),
            // binds another execution of its group (stored, as a recursive owner's inner activation is) and
            // binds another group (stored).
            IReadOnlyDictionary<string, NeedCell>? nested = null;
            IReadOnlyDictionary<string, NeedCell>? otherGroup = null;
            var owned = Value(await Memo.GetOrBindAsync(Owned(identity), async () =>
            {
                Binds++;
                await Task.Yield();
                Note();
                Assert.Equal(1, Memo.RunningExecutionCount);
                var reentrant = Value(await Memo.GetOrBindAsync(Owned(identity), async () =>
                {
                    Binds++;
                    await Task.Yield();
                    Note();
                    Assert.Equal(1, Memo.RunningExecutionCount); // a re-entrant bind owns nothing
                    return EvalResult<IReadOnlyDictionary<string, NeedCell>>.Ok(Bound(round - 1));
                }));
                Assert.Equal(round - 1, ValueOf(reentrant));
                nested = Value(await Memo.GetOrBindAsync(Nested(identity), async () =>
                {
                    Binds++;
                    await Task.Yield();
                    Note();
                    Assert.Equal(2, Memo.RunningExecutionCount);
                    return EvalResult<IReadOnlyDictionary<string, NeedCell>>.Ok(Bound(round + 1));
                }));
                Assert.Equal(round + 1, ValueOf(nested));
                Assert.Same(nested, await HitAsync(Nested(identity)));
                otherGroup = Value(await Memo.GetOrBindAsync(OtherGroup(identity), () => Bind(-round)));
                Assert.Same(otherGroup, await HitAsync(OtherGroup(identity)));
                Assert.Equal(1, Memo.RunningExecutionCount);
                return EvalResult<IReadOnlyDictionary<string, NeedCell>>.Ok(Bound(round));
            }));
            ExpectedBinds += 4;
            ExpectedStored += 3;
            Assert.Equal(round, ValueOf(owned));
            Note();
            // The owner's bind is the stored one, never the re-entrant bind made while it ran.
            Assert.Same(owned, await HitAsync(Owned(identity)));
            Assert.Same(nested, await HitAsync(Nested(identity)));
            if (round == 0)
            {
                // Read this local partition on a dedicated thread. A yield can resume on the same worker.
                var hit = await Task.Factory.StartNew(() =>
                {
                    Note();
                    return HitAsync(Owned(identity));
                }, CancellationToken.None, TaskCreationOptions.LongRunning, TaskScheduler.Default).Unwrap();
                Assert.Same(owned, hit);
            }
            Assert.Same(ExportedBind, await HitAsync(Exported()));

            if (round % 7 == 2)
            {
                // A failure is never stored: the next request binds again.
                for (var attempt = 0; attempt < 2; attempt++)
                {
                    var failed = await Memo.GetOrBindAsync(Failing(identity), async () =>
                    {
                        Binds++;
                        await Task.Yield();
                        return new EvalError.ArityMismatch(2, 1);
                    });
                    ExpectedBinds++;
                    Assert.True(failed.IsError);
                    Assert.Equal(0, Memo.RunningExecutionCount);
                }
            }

            if (round % 11 == 3)
            {
                // Cancellation propagates, releases the owning-execution guard and stores nothing; a later request binds.
                using var stop = new CancellationTokenSource();
                await stop.CancelAsync();
                var thrown = await Assert.ThrowsAsync<OperationCanceledException>(async () =>
                    await Memo.GetOrBindAsync(Failing(identity), async () =>
                    {
                        Binds++;
                        await Task.Yield();
                        stop.Token.ThrowIfCancellationRequested();
                        return EvalResult<IReadOnlyDictionary<string, NeedCell>>.Ok(Bound(0));
                    }));
                Assert.Equal(stop.Token, thrown.CancellationToken);
                Assert.Equal(0, Memo.RunningExecutionCount);
                var bound = Value(await Memo.GetOrBindAsync(Failing(identity), () => Bind(round + 3)));
                Assert.Same(bound, await HitAsync(Failing(identity)));
                ExpectedBinds += 2;
                ExpectedStored++;
            }

            Note();
            return keep ? new Kept(identity, owned, nested!, otherGroup!) : null;
        }

        private ValueTask<EvalResult<IReadOnlyDictionary<string, NeedCell>>> Bind(int value)
        {
            Binds++;
            return new(EvalResult<IReadOnlyDictionary<string, NeedCell>>.Ok(Bound(value)));
        }

        private void Note() => Threads.Add(Environment.CurrentManagedThreadId);
    }

    private static IReadOnlyDictionary<string, NeedCell> Bound(int value)
        => new Dictionary<string, NeedCell>(StringComparer.Ordinal) { ["x"] = NeedCell.Ready(new(new Result.Atom(value), 1)) };

    private static ValueTask<EvalResult<IReadOnlyDictionary<string, NeedCell>>> MustHit()
        => throw new InvalidOperationException("a stored bind must be served without binding");

    private static IReadOnlyDictionary<string, NeedCell> Value(EvalResult<IReadOnlyDictionary<string, NeedCell>> result)
    {
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        return result.Value;
    }

    private static int ValueOf(IReadOnlyDictionary<string, NeedCell> bound)
    {
        var demanded = bound["x"].Demand();
        Assert.True(demanded.IsOk);
        return int.Parse(SixRouteAgreement.Neutral(demanded.Value.Value), CultureInfo.InvariantCulture);
    }

    private static void ForceFullCollection()
    {
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
        GC.WaitForPendingFinalizers();
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
    }
}

/// <summary>
/// FAILURE ATOMICITY of the prompt-reclaim partition table (2026-11-18): a reclamation allocates only when it doubles the
/// table, and it allocates both doubled arrays before it changes anything. An allocation that fails — injected here
/// through the table's test seam (<see cref="BindingContextPartitionTable.PromptReclaimAllocationTestHook"/>) — leaves
/// every entry, handle and bucket chain as it was: every identity the table held is still found with its very slots,
/// the failed addition added nothing, a DEBUG build's overlap tripwire is released, and the next addition reclaims and
/// succeeds. Before, the table compacted its entries first and doubled after, so a failure there left bucket chains that
/// named moved entries, and a lookup missed identities the table still held. The same holds through the stores
/// (2026-11-20): an addition whose growth fails stores and counts nothing in any store sharing the table, every live
/// key still reads its value, and the next addition reclaims the dead identities' partitions.
/// </summary>
public sealed class PromptReclaimTableFailureAtomicityTests
{
    private const int InitialCapacity = 8;
    private const int Dead = 2;

    [Theory]
    [InlineData(nameof(BindingContextPartitionTable.ReclaimAllocation.Entries))]
    [InlineData(nameof(BindingContextPartitionTable.ReclaimAllocation.Buckets))]
    public void AFailedReclaimAllocation_LeavesTheTableAsItWas_AndTheNextAdditionSucceeds(string failingAllocation)
    {
        var failing = Enum.Parse<BindingContextPartitionTable.ReclaimAllocation>(failingAllocation);
        var table = new BindingContextPartitionTable(storeCount: 1);
        // The first entries' identities die, so a reclamation would move every later entry down.
        AddDeadIdentities(table, Dead);
        var live = Enumerable.Range(0, InitialCapacity - Dead).Select(_ => new object()).ToArray();
        var slots = live.Select(identity => Add(table, identity)).ToArray();
        ForceFullCollection();
        Assert.Equal(InitialCapacity, table.PromptCapacity);
        Assert.Equal(InitialCapacity, Used(table)); // full: the next addition reclaims, and doubles (6 of 8 alive)

        var requested = new List<BindingContextPartitionTable.ReclaimAllocation>();
        var injected = new OutOfMemoryException("injected allocation failure");
        table.PromptReclaimAllocationTestHook = allocation =>
        {
            requested.Add(allocation);
            if (allocation == failing)
                throw injected;
        };

        var extra = new object();
        Assert.Same(injected, Assert.Throws<OutOfMemoryException>(() => table.GetOrCreate(extra)));
        Assert.Equal(failing == BindingContextPartitionTable.ReclaimAllocation.Entries ? 1 : 2, requested.Count);
        Assert.Equal(failing, requested[^1]);

        // Nothing changed: every held identity found with its very slots, nothing added, the same capacity and entries.
        AssertTripwireReleased(table);
        // Check before traversing chains: partial compaction can leave a chain pointing back into itself.
        Assert.Equal(InitialCapacity, table.PromptCapacity);
        Assert.Equal(InitialCapacity, Used(table));
        for (var index = 0; index < live.Length; index++)
            Assert.Same(slots[index], table.Find(live[index]));
        Assert.Null(table.Find(extra));
        Assert.Equal(live.Length, table.LivePartitionCount(0));

        // The next addition reclaims the dead entries, doubles the table and adds.
        table.PromptReclaimAllocationTestHook = null;
        var extraSlots = Add(table, extra);
        Assert.Equal(2 * InitialCapacity, table.PromptCapacity);
        Assert.Equal(live.Length + 1, Used(table));
        for (var index = 0; index < live.Length; index++)
            Assert.Same(slots[index], table.Find(live[index]));
        Assert.Same(extraSlots, table.Find(extra));
        Assert.Equal(live.Length + 1, table.LivePartitionCount(0));
        GC.KeepAlive(live);
        GC.KeepAlive(extra);
    }

    [Fact]
    public void AReclamationThatDoesNotDouble_AllocatesNothing()
    {
        var table = new BindingContextPartitionTable(storeCount: 1);
        // Half or fewer of the entries alive: the reclamation compacts in place.
        AddDeadIdentities(table, InitialCapacity / 2);
        var live = Enumerable.Range(0, InitialCapacity / 2).Select(_ => new object()).ToArray();
        var slots = live.Select(identity => Add(table, identity)).ToArray();
        ForceFullCollection();
        table.PromptReclaimAllocationTestHook = allocation => throw new OutOfMemoryException($"unexpected {allocation} allocation");

        var extra = new object();
        var extraSlots = Add(table, extra);
        Assert.Equal(InitialCapacity, table.PromptCapacity);
        Assert.Equal(live.Length + 1, Used(table));
        for (var index = 0; index < live.Length; index++)
            Assert.Same(slots[index], table.Find(live[index]));
        Assert.Same(extraSlots, table.Find(extra));
        GC.KeepAlive(live);
        GC.KeepAlive(extra);
    }

    /// <summary>
    /// The failure seen through the STORES: a map and a set sharing one table, as the statistics cache's stores do. An
    /// addition whose growth fails — in either store, twice — adds and counts nothing; every live key of both stores
    /// and an exported key still read their values. A dead identity's partition is unreachable at once (its value is
    /// collected while the table still holds its entry), and the next addition reclaims those entries, doubles the table
    /// and stores the keys the failed attempts could not.
    /// </summary>
    [Theory]
    [InlineData(nameof(BindingContextPartitionTable.ReclaimAllocation.Entries))]
    [InlineData(nameof(BindingContextPartitionTable.ReclaimAllocation.Buckets))]
    public void AFailedGrowth_KeepsEveryStoresLiveKeys_AndTheNextAdditionReclaimsTheDeadPartitions(string failingAllocation)
    {
        var failing = Enum.Parse<BindingContextPartitionTable.ReclaimAllocation>(failingAllocation);
        var table = new BindingContextPartitionTable(storeCount: 2);
        var values = new PartitionedMap<ZeroArgPropertyCacheKey, object>(
            ZeroArgPropertyCacheKeyComparer.Instance, BindingContextPartitions.OfPropertyKey, table, store: 0);
        var seen = new PartitionedSet<ZeroArgPropertyCacheKey>(
            ZeroArgPropertyCacheKeyComparer.Instance, BindingContextPartitions.OfPropertyKey, table, store: 1);
        var (owner, binding, run) = (new object(), new object(), new object());
        Func<object, ZeroArgPropertyCacheKey> key = identity => new(owner, binding, identity, run);

        var exported = key(ZeroArgPropertyCacheKey.RunWideEnvironmentIdentity);
        var exportedValue = new object();
        Assert.True(values.TryAdd(exported, exportedValue));
        // The first identities die, so the reclamation would move every later entry down; the rest stay alive.
        var dead = AddUnderDeadIdentities(values, seen, key, Dead);
        var live = Enumerable.Range(0, InitialCapacity - Dead).Select(_ => new object()).ToArray();
        var liveValues = new object[live.Length];
        for (var index = 0; index < live.Length; index++)
        {
            Assert.True(values.TryAdd(key(live[index]), liveValues[index] = new object()));
            Assert.True(seen.Add(key(live[index])));
        }

        ForceFullCollection();
        // Collected while the table still holds their entries: no store keeps a dead identity's partition reachable.
        Assert.All(dead, reference => Assert.False(reference.IsAlive));
        Assert.Equal(InitialCapacity, Used(table)); // full: the next addition reclaims, and doubles (6 of 8 alive)
        var (valuesAdded, seenAdded) = (values.AddedCount, seen.AddedCount);

        var injected = new OutOfMemoryException("injected allocation failure");
        table.PromptReclaimAllocationTestHook = allocation =>
        {
            if (allocation == failing)
                throw injected;
        };
        var extra = new object();
        var extraValue = new object();
        Assert.Same(injected, Assert.Throws<OutOfMemoryException>(() => values.TryAdd(key(extra), extraValue)));
        Assert.Same(injected, Assert.Throws<OutOfMemoryException>(() => seen.Add(key(extra))));

        // Nothing stored or counted, nothing reclaimed, and every live and exported key still read.
        AssertTripwireReleased(table);
        Assert.Equal(InitialCapacity, table.PromptCapacity);
        Assert.Equal(InitialCapacity, Used(table));
        Assert.Equal((valuesAdded, seenAdded), (values.AddedCount, seen.AddedCount));
        Assert.False(values.ContainsKey(key(extra)));
        Assert.False(seen.Contains(key(extra)));
        AssertEveryLiveKeyIsRead();
        Assert.Equal(live.Length, values.LivePartitionCount());
        Assert.Equal(live.Length, seen.LivePartitionCount());

        // The next additions reclaim the dead entries, double the table and store the keys.
        table.PromptReclaimAllocationTestHook = null;
        Assert.True(values.TryAdd(key(extra), extraValue));
        Assert.True(seen.Add(key(extra)));
        Assert.Equal(2 * InitialCapacity, table.PromptCapacity);
        Assert.Equal(live.Length + 1, Used(table)); // the dead identities' entries are gone
        Assert.Equal((valuesAdded + 1, seenAdded + 1), (values.AddedCount, seen.AddedCount));
        AssertEveryLiveKeyIsRead();
        Assert.True(values.TryGetValue(key(extra), out var storedExtra));
        Assert.Same(extraValue, storedExtra);
        Assert.True(seen.Contains(key(extra)));
        Assert.Equal(live.Length + 1, values.LivePartitionCount());
        Assert.Equal(live.Length + 1, seen.LivePartitionCount());
        GC.KeepAlive(live);
        GC.KeepAlive(extra);

        void AssertEveryLiveKeyIsRead()
        {
            for (var index = 0; index < live.Length; index++)
            {
                Assert.True(values.TryGetValue(key(live[index]), out var value));
                Assert.Same(liveValues[index], value);
                Assert.True(seen.Contains(key(live[index])));
            }

            Assert.True(values.TryGetValue(exported, out var exportedStored));
            Assert.Same(exportedValue, exportedStored);
        }
    }

    private static object?[] Add(BindingContextPartitionTable table, object identity)
    {
        var slots = table.GetOrCreate(identity);
        slots[0] = new object(); // store 0's partition, as a PartitionedMap would add it
        return slots;
    }

    // A separate frame, so no dead identity stays reachable from the asserting method's locals. Returns weak references
    // to each dead identity and to the value its partition holds.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static List<WeakReference> AddUnderDeadIdentities(
        PartitionedMap<ZeroArgPropertyCacheKey, object> values,
        PartitionedSet<ZeroArgPropertyCacheKey> seen,
        Func<object, ZeroArgPropertyCacheKey> key,
        int count)
    {
        var references = new List<WeakReference>();
        for (var index = 0; index < count; index++)
        {
            var identity = new object();
            var value = new object();
            Assert.True(values.TryAdd(key(identity), value));
            Assert.True(seen.Add(key(identity)));
            references.Add(new WeakReference(identity));
            references.Add(new WeakReference(value));
        }

        return references;
    }

    // A separate frame, so no dead identity stays reachable from the asserting method's locals.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void AddDeadIdentities(BindingContextPartitionTable table, int count)
    {
        for (var index = 0; index < count; index++)
            Add(table, new object());
    }

    // The table's private state, read by name (pinned here and by the DEBUG tripwire test, so a rename fails them).
    private static object Slots(BindingContextPartitionTable table)
        => typeof(BindingContextPartitionTable).GetField("_prompt", BindingFlags.Instance | BindingFlags.NonPublic)!.GetValue(table)!;

    private static int Used(BindingContextPartitionTable table)
    {
        var slots = Slots(table);
        return (int)slots.GetType().GetField("_used", BindingFlags.Instance | BindingFlags.NonPublic)!.GetValue(slots)!;
    }

    private static void AssertTripwireReleased(BindingContextPartitionTable table)
    {
#if DEBUG
        var slots = Slots(table);
        Assert.Equal(0, (int)slots.GetType().GetField("_operating", BindingFlags.Instance | BindingFlags.NonPublic)!.GetValue(slots)!);
#else
        GC.KeepAlive(table);
#endif
    }

    private static void ForceFullCollection()
    {
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
        GC.WaitForPendingFinalizers();
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
    }
}
