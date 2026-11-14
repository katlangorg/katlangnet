using System.Diagnostics;
using System.Globalization;
using KatLang.Evaluation.Caching;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// IDENTITY-PARTITIONED RUN CACHES (C#-only storage policy, no Lean counterpart): the run-scoped
/// add-only stores of LOCAL-ONLY keys — the published zero-argument property entries
/// (<see cref="ZeroArgPropertyPublications"/>, shared by the sync, async and generic routes), the
/// statistics key sets of <see cref="RunScopedZeroArgPropertyResultCache"/> and of
/// <see cref="UncachedZeroArgPropertyResultCache.CreateForRun"/>, and the deconstruction shared-bind memo
/// (<see cref="RunScopedDeconstructionBindingCache"/>) — keep an entry only while its binding-context
/// identity is reachable (<see cref="PartitionedMap{TKey, TValue}"/>). Before this, every activation's
/// identity, environment and entry lived until the run ended: memory grew about 0.7–2.7 KB per call
/// without limit.
/// <para>A synchronous host operation <c>probe()</c> runs last in each program, forces a full blocking
/// collection and reads the cache's live partition count through the test seam. Live partitions stay
/// bounded while the monotonic counts keep the numbers an unpartitioned store would report. A control
/// shows the seam does count live partitions: activations a run still holds — returned call
/// references kept by a property — keep theirs. The semantic pins show the partition is the identity
/// OBJECT, never an activation, and that nothing is evicted when an activation exits.</para>
/// </summary>
public sealed class LocalOnlyCacheRetentionTests(ITestOutputHelper output)
{
    private const int Calls = 20_000;
    private const int MaxLivePartitions = 64;

    // sum over x = 1..20000 of (x + 1)
    private const string ReduceSum = "200030000";

    private const string ReduceProgram = """
        F(x) = { V = x + 1
         V * 1 }
        Sum(acc, x) = acc + F(x)
        reduce(range(1, 20000), Sum, 0) + probe() * 0
        """;

    private const string DeconstructionReduceProgram = """
        F(x) = { a, b = x + 1, x
         a * 1 }
        Sum(acc, x) = acc + F(x)
        reduce(range(1, 20000), Sum, 0) + probe() * 0
        """;

    private const string RepeatProgram = """
        Step(x) = { V = x + 1
         V * 1 }
        Step(0).repeat(20000) + probe() * 0
        """;

    // ── Retention, one store family at a time ───────────────────────────────────────────

    [Fact]
    public void SyncStatisticsCache_LocalOnlyEntriesOfFinishedCalls_AreNotRetained()
    {
        var cache = new RunScopedZeroArgPropertyResultCache();
        (int Published, int SeenKeys, int MissedWithoutStore) live = default;
        var publishedAtProbe = 0;
        var value = RunSync(ReduceProgram, cache, enableOptimizations: true, () =>
        {
            live = cache.LivePartitionCounts();
            publishedAtProbe = cache.PublishedCount;
        });

        output.WriteLine($"sync statistics: live partitions {live}, published {publishedAtProbe}");
        Assert.Equal(ReduceSum, value);
        Assert.InRange(live.Published, 0, MaxLivePartitions);
        Assert.InRange(live.SeenKeys, 0, MaxLivePartitions);
        Assert.InRange(live.MissedWithoutStore, 0, MaxLivePartitions);
        Assert.True(publishedAtProbe >= Calls, $"published {publishedAtProbe}");

        // The statistics are the numbers an unpartitioned store reports: one key, one miss and one
        // store per call's V, nothing repeated, and every entry counted in the maximum size.
        var snapshot = cache.GetSnapshot();
        Assert.Equal(Calls, snapshot.TotalRequests);
        Assert.Equal(Calls, snapshot.Misses);
        Assert.Equal(0, snapshot.Hits);
        Assert.Equal(Calls, snapshot.Stores);
        Assert.Equal(Calls, snapshot.DistinctKeysCreated);
        Assert.Equal(0, snapshot.RepeatedMissRequests);
        Assert.Equal(Calls, snapshot.MaxCacheSize);
        Assert.Equal(Calls, cache.PublishedCount);
    }

    [Fact]
    public void GenericRoute_LoopStepActivations_AreNotRetained()
    {
        var cache = new RunScopedZeroArgPropertyResultCache();
        (int Published, int SeenKeys, int MissedWithoutStore) live = default;
        var value = RunSync(RepeatProgram, cache, enableOptimizations: false, () => live = cache.LivePartitionCounts());

        output.WriteLine($"generic repeat: live partitions {live}, published {cache.PublishedCount}");
        Assert.Equal("20000", value);
        Assert.InRange(live.Published, 0, MaxLivePartitions);
        Assert.InRange(live.SeenKeys, 0, MaxLivePartitions);
        Assert.InRange(live.MissedWithoutStore, 0, MaxLivePartitions);
        Assert.True(cache.PublishedCount >= Calls, $"published {cache.PublishedCount}");
        Assert.True(cache.GetSnapshot().DistinctKeysCreated >= Calls);
    }

    [Fact]
    public async Task AsyncCache_WithAnAsyncHostOperation_DoesNotRetainFinishedCalls()
    {
        var cache = new RunScopedAsyncZeroArgPropertyResultCache();
        var live = -1;
        var operations = HostOperations.Create(HostOperation.CreateAsync("probe", async (_, _) =>
        {
            // A genuine suspension: the run is on the async twin path.
            await Task.Yield();
            ForceFullCollection();
            live = cache.LivePartitionCount();
            return new Result.Atom(0);
        }));

        var (result, _) = await Evaluator.RunCountedObservedAsync(
            Program(ReduceProgram, operations), zeroArgPropertyResultCache: cache, hostOperations: operations);

        output.WriteLine($"async: live partitions {live}, published {cache.PublishedCount}");
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        Assert.Equal(ReduceSum, SixRouteAgreement.Neutral(result.Value.Value));
        Assert.InRange(live, 0, MaxLivePartitions);
        Assert.True(cache.PublishedCount >= Calls, $"published {cache.PublishedCount}");
    }

    [Fact]
    public void DeconstructionBody_BindsAndEntriesOfFinishedCalls_AreNotRetained()
    {
        var cache = new RunScopedZeroArgPropertyResultCache();
        var observations = new EvaluationObservations();
        (int Published, int SeenKeys, int MissedWithoutStore) live = default;
        var liveBinds = -1;
        var value = RunSync(DeconstructionReduceProgram, cache, enableOptimizations: true, () =>
        {
            live = cache.LivePartitionCounts();
            liveBinds = observations.DeconstructionBindingCache!.LivePartitionCount();
        }, observations);

        output.WriteLine($"deconstruction: live partitions {live}, live bind partitions {liveBinds}, published {cache.PublishedCount}, binds {observations.DeconstructionBindingCache!.Count}");
        Assert.Equal(ReduceSum, value);
        Assert.InRange(live.Published, 0, MaxLivePartitions);
        Assert.InRange(live.SeenKeys, 0, MaxLivePartitions);
        Assert.InRange(live.MissedWithoutStore, 0, MaxLivePartitions);
        Assert.InRange(liveBinds, 0, MaxLivePartitions);
        // Each call stores its own source entry, target entries and one shared bind.
        Assert.True(cache.PublishedCount >= Calls, $"published {cache.PublishedCount}");
        Assert.True(observations.DeconstructionBindingCache!.Count >= Calls, $"binds {observations.DeconstructionBindingCache.Count}");
        Assert.Equal(Calls, observations.DeconstructionFullBindCount);
    }

    [Fact]
    public void UncachedStatisticsCache_SeenKeysOfFinishedCalls_AreNotRetained()
    {
        var cache = UncachedZeroArgPropertyResultCache.CreateForRun();
        var live = -1;
        var value = RunSync(ReduceProgram, cache, enableOptimizations: true, () => live = cache.LivePartitionCount());

        output.WriteLine($"uncached statistics: live partitions {live}, distinct keys {cache.GetSnapshot().DistinctKeysCreated}");
        Assert.Equal(ReduceSum, value);
        Assert.InRange(live, 0, MaxLivePartitions);
        Assert.Equal(Calls, cache.GetSnapshot().DistinctKeysCreated);
    }

    /// <summary>
    /// The control: the seam counts what the run still holds. Every returned call reference is kept by
    /// the exported property <c>Refs</c> (a run-wide entry), so each referenced activation's identity
    /// stays reachable, and the entry its re-entry published stays with it: the second pass of
    /// re-entries reads <c>V</c> again (<c>Get</c> reads it lexically, it is no argument cell) and hits.
    /// </summary>
    [Fact]
    public void Control_ActivationsTheRunStillHolds_KeepTheirPartitions()
    {
        const int held = 100;
        var cache = new RunScopedZeroArgPropertyResultCache();
        (int Published, int SeenKeys, int MissedWithoutStore) live = default;
        var value = RunSync($$"""
            Cap(meta r) = r
            F(x) = { V = x + 1
             Get(u) = V + u
             Cap(Get(0)) }
            Refs = map(range(1, {{held}}), F)
            Refs.map{ n.Invoke() }.sum + Refs.map{ n.Invoke() }.sum + probe() * 0
            """, cache, enableOptimizations: true, () => live = cache.LivePartitionCounts());

        output.WriteLine($"control: live partitions {live}, hits {cache.GetSnapshot().Hits}");
        // sum over x = 1..100 of (x + 1), read twice: the second pass hits every entry.
        Assert.Equal("10300", value);
        Assert.True(live.Published >= held, $"live published partitions {live.Published}");
        Assert.True(live.SeenKeys >= held, $"live seen-key partitions {live.SeenKeys}");
        var snapshot = cache.GetSnapshot();
        Assert.True(snapshot.Hits >= held, $"hits {snapshot.Hits}");
    }

    // ── Semantic pins: one identity, never one activation; no eviction on exit ─────────

    /// <summary>
    /// CACHE-OWNER-D1: B's activation inherits F's binding identity, so B.V, B's own output row and the
    /// second B.V share ONE entry across two activation objects; each F call is its own identity.
    /// </summary>
    [Fact]
    public async Task D1Share_TwoActivationsOfOneIdentity_ShareOneEntry_OnEveryRoute()
    {
        var oracle = await SixRouteAgreement.OnEveryRouteAsync("""
            F(x) = { B = { public V = x + tick()
             V }
             B.V, B, B.V }
            F(0), F(10)
            """);
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal("S[S[1, 1, 1], S[12, 12, 12]]", oracle.Value);
    }

    /// <summary>
    /// A returned activation re-entered through a call reference still reaches what its identity owns:
    /// <c>tick()</c> ran once before the last row. In the first form <c>V</c> is the captured call's
    /// argument cell (memoized by the plan's one supply); in the second the re-executed <c>Get</c> reads
    /// <c>V</c> lexically, so the second <c>Invoke()</c> is a property-cache HIT on the returned
    /// activation's entry — evicting entries when an activation exits would tick again (2, not 1).
    /// </summary>
    [Theory]
    [InlineData("Cap(meta r) = r\nId(v) = v\nF(x) = { V = tick() + x * 0\n Cap(Id(V)) }\nR = F(1)\nR.Invoke(), R.Invoke(), tick()")]
    [InlineData("Cap(meta r) = r\nF(x) = { V = tick() + x * 0\n Get(u) = V + u\n Cap(Get(0)) }\nR = F(1)\nR.Invoke(), R.Invoke(), tick()")]
    public async Task CapRead_AReturnedActivationReenteredByReference_KeepsItsEntry_OnEveryRoute(string source)
    {
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal("S[1, 1, 2]", oracle.Value);
    }

    /// <summary>The second <c>capread</c> form's re-entry hits the returned activation's entry (sync statistics).</summary>
    [Fact]
    public void CapRead_TheSecondReentry_IsACacheHit()
    {
        var cache = new RunScopedZeroArgPropertyResultCache();
        var value = RunSync(
            "Cap(meta r) = r\nF(x) = { V = tick() + x * 0\n Get(u) = V + u\n Cap(Get(0)) }\nR = F(1)\nR.Invoke(), R.Invoke(), tick() + probe() * 0",
            cache,
            enableOptimizations: true,
            static () => { });
        Assert.Equal("S[1, 1, 2]", value);
        var snapshot = cache.GetSnapshot();
        // R and V each miss once (two stores) and hit once.
        Assert.Equal(2, snapshot.Hits);
        Assert.Equal(2, snapshot.Stores);
    }

    // ── Store-level laws ────────────────────────────────────────────────────────────────

    [Fact]
    public void PartitionedMap_DoesNotRootTheLastIdentity_OrTheIdentitiesItReferences()
    {
        var map = new PartitionedMap<ZeroArgPropertyCacheKey, int>(
            ZeroArgPropertyCacheKeyComparer.Instance, BindingContextPartitions.OfPropertyKey);
        const int identities = 256;
        var lastIdentity = AddUnderLinkedIdentities(map, identities);

        ForceFullCollection();

        // A binding environment can retain earlier environments. Keeping even the last identity in
        // a fast-path field would root the entire chain through otherwise weak partitions.
        Assert.False(lastIdentity.IsAlive);
        Assert.Equal(0, map.LivePartitionCount());
        Assert.Equal(identities, map.AddedCount);
        GC.KeepAlive(map);
    }

    [Fact]
    public void PartitionedMap_KeepsAnEntryWhileItsIdentityIsReachable_AndCountsMonotonically()
    {
        var map = new PartitionedMap<ZeroArgPropertyCacheKey, int>(
            ZeroArgPropertyCacheKeyComparer.Instance, BindingContextPartitions.OfPropertyKey);
        var owner = new object();
        var binding = new object();
        var run = new object();
        var identity = new object();
        var exported = Key(owner, binding, ZeroArgPropertyCacheKey.RunWideEnvironmentIdentity, run);
        var local = Key(owner, binding, identity, run);

        Assert.True(map.TryAdd(exported, 1));
        Assert.True(map.TryAdd(local, 2));
        Assert.False(map.TryAdd(Key(owner, binding, identity, run), 3));
        Assert.True(map.TryGetValue(Key(owner, binding, identity, run), out var stored));
        Assert.Equal(2, stored);
        Assert.False(map.ContainsKey(Key(owner, binding, new object(), run)));
        Assert.Equal(2, map.AddedCount);
        Assert.Equal(1, map.LivePartitionCount());

        // A second key under the same identity shares its partition; removal is per key.
        var second = Key(owner, new object(), identity, run);
        Assert.True(map.TryAdd(second, 4));
        Assert.True(map.Remove(local));
        Assert.False(map.ContainsKey(local));
        Assert.True(map.ContainsKey(second));
        Assert.True(map.TryAdd(local, 5));
        Assert.Equal(4, map.AddedCount);
        Assert.Equal(1, map.LivePartitionCount());
        GC.KeepAlive(identity);

        // Partitions of identities nothing references any more are gone; the exported entry stays.
        AddUnderFreshIdentities(map, owner, binding, run, count: 200);
        ForceFullCollection();
        Assert.InRange(map.LivePartitionCount(), 1, 3);
        Assert.Equal(204, map.AddedCount);
        Assert.True(map.TryGetValue(Key(owner, binding, ZeroArgPropertyCacheKey.RunWideEnvironmentIdentity, run), out var kept));
        Assert.Equal(1, kept);
        Assert.True(map.ContainsKey(second));
        GC.KeepAlive(identity);
    }

    [Fact]
    public void PartitionedStores_SharingATable_KeepTheirOwnEntries()
    {
        var table = new BindingContextPartitionTable(storeCount: 2);
        var first = new PartitionedSet<ZeroArgPropertyCacheKey>(
            ZeroArgPropertyCacheKeyComparer.Instance, BindingContextPartitions.OfPropertyKey, table, store: 0);
        var second = new PartitionedSet<ZeroArgPropertyCacheKey>(
            ZeroArgPropertyCacheKeyComparer.Instance, BindingContextPartitions.OfPropertyKey, table, store: 1);
        var identity = new object();
        var key = Key(new object(), new object(), identity, new object());

        Assert.True(first.Add(key));
        Assert.False(second.Contains(key));
        Assert.Equal(1, first.LivePartitionCount());
        Assert.Equal(0, second.LivePartitionCount());
        Assert.True(second.Add(key));
        Assert.True(first.Remove(key));
        Assert.True(second.Contains(key));
        Assert.Equal(1, first.AddedCount);
        Assert.Equal(1, second.AddedCount);
        Assert.Throws<ArgumentOutOfRangeException>(() => new PartitionedSet<ZeroArgPropertyCacheKey>(
            ZeroArgPropertyCacheKeyComparer.Instance, BindingContextPartitions.OfPropertyKey, table, store: 2));
        GC.KeepAlive(identity);
    }

    // ── Helpers ─────────────────────────────────────────────────────────────────────────

    private static ZeroArgPropertyCacheKey Key(object owner, object binding, object identity, object run)
        => new(ZeroArgPropertyCacheAccessShape.Lexical, owner, binding, identity, run);

    // A separate frame, so no fresh identity stays reachable from the asserting method's locals.
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static WeakReference AddUnderLinkedIdentities(PartitionedMap<ZeroArgPropertyCacheKey, int> map, int count)
    {
        var owner = new object();
        var binding = new object();
        var run = new object();
        object? previous = null;
        for (var i = 0; i < count; i++)
        {
            var identity = new object?[] { previous };
            Assert.True(map.TryAdd(Key(owner, binding, identity, run), i));
            previous = identity;
        }

        return new WeakReference(previous);
    }

    // A separate frame, so no fresh identity stays reachable from the asserting method's locals.
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static void AddUnderFreshIdentities(
        PartitionedMap<ZeroArgPropertyCacheKey, int> map, object owner, object binding, object run, int count)
    {
        for (var i = 0; i < count; i++)
            Assert.True(map.TryAdd(Key(owner, binding, new object(), run), i));
    }

    private static string RunSync(
        string source,
        IZeroArgPropertyResultCache cache,
        bool enableOptimizations,
        Action readAtProbe,
        EvaluationObservations? observations = null)
    {
        var operations = HostOperations.Create(HostOperation.Create("probe", (_, _) =>
        {
            ForceFullCollection();
            readAtProbe();
            return new Result.Atom(0);
        }));
        var (result, _) = Evaluator.RunCountedObserved(
            Program(source, operations),
            enableOptimizations: enableOptimizations,
            zeroArgPropertyResultCache: cache,
            observations: observations,
            hostOperations: operations);
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        return SixRouteAgreement.Neutral(result.Value.Value);
    }

    private static Expr Program(string source, HostOperations operations)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    private static void ForceFullCollection()
    {
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
        GC.WaitForPendingFinalizers();
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
    }
}

/// <summary>
/// The peak-memory guard of identity-partitioned run caches: four <c>reduce</c>s over a callback whose
/// body has a local-only property may not take much more peak memory than one. Each program runs in a
/// fresh <see cref="SubprocessProbe"/> child on the default engine (<see cref="KatLangEngine.Run"/>),
/// which reports its peak working set; the parent compares the two. When every finished call's
/// entry stayed until the run ended, the difference was about 280 MB; a partition now dies with its
/// identity.
/// </summary>
public sealed class LocalOnlyCachePeakMemoryProcessTests(ITestOutputHelper output)
{
    private const string Child = "KATLANG_LOCAL_ONLY_PEAK_CHILD";
    private const string Reduces = "KATLANG_LOCAL_ONLY_PEAK_REDUCES";
    private const string Marker = "KATLANG_LOCAL_ONLY_PEAK_MARKER";
    private const long AllowedGrowthBytes = 40L * 1024 * 1024;

    [Fact]
    public async Task FourReduces_PeakWorkingSet_StaysWithinFortyMegabytesOfOne()
    {
        var one = await PeakWorkingSetAsync(reduces: 1);
        var four = await PeakWorkingSetAsync(reduces: 4);
        output.WriteLine($"peak working set: one reduce {one / 1048576.0:F1} MB, four reduces {four / 1048576.0:F1} MB");
        Assert.True(
            four - one < AllowedGrowthBytes,
            $"peak working set: one reduce {one / 1048576.0:F1} MB, four reduces {four / 1048576.0:F1} MB");
    }

    [Fact]
    public void PeakChild()
    {
        if (Environment.GetEnvironmentVariable(Child) != "1")
            return;

        var reduces = int.Parse(Environment.GetEnvironmentVariable(Reduces)!, CultureInfo.InvariantCulture);
        var source = "F(x) = { V = x + 1\n V * 1 }\nSum(acc, x) = acc + F(x)\n"
            + string.Join(" + ", Enumerable.Repeat("reduce(range(1, 100000), Sum, 0)", reduces));
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        // sum over x = 1..100000 of (x + 1), once per reduce
        Assert.Equal((5_000_150_000L * reduces).ToString(CultureInfo.InvariantCulture), success.ToDisplayString());

        using var process = Process.GetCurrentProcess();
        process.Refresh();
        File.WriteAllText(
            Environment.GetEnvironmentVariable(Marker)!,
            process.PeakWorkingSet64.ToString(CultureInfo.InvariantCulture));
    }

    private static async Task<long> PeakWorkingSetAsync(int reduces)
    {
        var marker = Path.Combine(Path.GetTempPath(), $"katlang-local-only-peak-{Guid.NewGuid():N}.txt");
        var start = SubprocessProbe.StartInfo(typeof(LocalOnlyCachePeakMemoryProcessTests), nameof(PeakChild));
        start.Environment[Child] = "1";
        start.Environment[Reduces] = reduces.ToString(CultureInfo.InvariantCulture);
        start.Environment[Marker] = marker;
        try
        {
            using var process = Process.Start(start)!;
            var output = process.StandardOutput.ReadToEndAsync();
            var error = process.StandardError.ReadToEndAsync();
            await process.WaitForExitAsync();
            var text = await output + await error;
            Assert.True(process.ExitCode == 0, text);
            Assert.True(File.Exists(marker), text);
            return long.Parse(await File.ReadAllTextAsync(marker), CultureInfo.InvariantCulture);
        }
        finally
        {
            File.Delete(marker);
        }
    }
}
