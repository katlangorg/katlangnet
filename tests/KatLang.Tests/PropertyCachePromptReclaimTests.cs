using System.Diagnostics;
using System.Globalization;
using System.Reflection;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// PROPERTY-CACHE PROMPT RECLAIM (2026-11-17; C#-only storage, implementation-only, Lean unchanged): the zero-argument
/// property cache's published entries and statistics key sets keep their binding-context partitions in the
/// PROMPT-RECLAIM form of <see cref="BindingContextPartitionTable"/>, which frees a dead identity's entry in place when
/// the table fills instead of waiting for the finalizers of a <see cref="System.Runtime.CompilerServices.ConditionalWeakTable{TKey, TValue}"/>.
/// That form is sequential and takes no lock: the property cache relies on a run being ONE evaluation flow, which an
/// async continuation may move to another thread only after the previous table operation returned.
/// <para>These tests drive that model through the ASYNC cache: several independent runs at once, each a sequential flow
/// that suspends at every miss (through the pool, and periodically onto a new thread, so it provably changes threads)
/// while collections clear dead identities, reading, publishing, failing, cancelling, invoking and dropping partitions.
/// Every hit, miss, published value and count is the one the publication law gives, no entry a live key can name is
/// lost, dead partitions leave the table, and the table stays far smaller than the identities that passed through it.
/// In DEBUG builds the table also fails loudly if two operations ever overlap.</para>
/// </summary>
public sealed class PropertyCachePromptReclaimTests(ITestOutputHelper output)
{
    private const int Flows = 8;
    private const int Rounds = 4_096;
    private const int KeepEvery = 128;
    private const int CollectEvery = 256;
    private const int NewThreadHopEvery = 64;

    [Fact]
    public void EveryRunScopedPropertyCache_UsesThePromptReclaimTable()
    {
        // Every partition table is the prompt-reclaim form since 2026-11-20 (the ConditionalWeakTable form, which
        // reported a capacity of 0, was removed); a capacity pins that the cache keeps its entries in one.
        Assert.True(new RunScopedAsyncZeroArgPropertyResultCache().PromptTableCapacity > 0);
        Assert.True(new RunScopedZeroArgPropertyResultCache(collectStatistics: false).PromptTableCapacity > 0);
        Assert.True(new RunScopedZeroArgPropertyResultCache().PromptTableCapacity > 0);
    }

    [Fact]
    public async Task AsyncCache_ReadsPublishesAndDropsPartitions_FromSeveralThreads()
    {
        var reports = await Task.WhenAll(Enumerable.Range(0, Flows).Select(_ => Task.Run(RunFlowAsync)));
        ForceFullCollection();

        foreach (var report in reports)
        {
            var flow = report.Flow;
            var live = flow.Cache.LivePartitionCount();
            output.WriteLine(
                $"flow: {flow.Threads.Count} threads, {flow.Evaluations} evaluations, {flow.Cache.PublishedCount} published, "
                + $"table capacity {report.Capacity} after {Rounds} identities, {live} live partitions ({report.Kept.Count} kept)");

            // The sequential flow really moved between threads: every new-thread hop resumed it — and the nested
            // lookup and publication that follow the hop — on a thread other than the one that suspended. (A hop
            // through the pool may resume on the very worker that suspended, so the threads seen prove nothing.)
            Assert.Equal(Rounds / NewThreadHopEvery, flow.NewThreadResumptions.Count);
            Assert.All(flow.NewThreadResumptions, AssertOnANewThread);
            Assert.Equal(flow.ExpectedEvaluations, flow.Evaluations);
            Assert.Equal(flow.ExpectedPublished, flow.Cache.PublishedCount);
            Assert.Equal(0, flow.Cache.ActiveOwnerCount);
            // Dead identities were freed in place: the table never held all of them.
            Assert.InRange(report.Capacity, 8, Rounds / 2);
            // Only the kept identities still own partitions (a straggler or two may await its collection).
            Assert.InRange(live, report.Kept.Count, report.Kept.Count + 2);

            // No entry a live key can name was lost: every kept identity still hits both of its entries.
            foreach (var (identity, round) in report.Kept)
            {
                Assert.Equal(round, Value(await flow.Cache.GetOrEvaluateAsync(flow.Read(flow.P, identity), MustHit)));
                Assert.Equal(10 * round + 1, Value(await flow.Cache.GetOrEvaluateAsync(flow.Read(flow.Q, identity), MustHit)));
            }

            Assert.Equal(-7, Value(await flow.Cache.GetOrEvaluateAsync(flow.Read(flow.E, new object()), MustHit)));
            GC.KeepAlive(report.Kept);
        }
    }

    [Fact]
    public async Task ConcurrentAsyncRuns_OfALocalOnlyLoopThatSuspendsEveryStep_DropTheirPartitions()
    {
        const int runs = 4;
        const int steps = 20_000;
        var outcomes = await Task.WhenAll(Enumerable.Range(0, runs).Select(_ => Task.Run(async () =>
        {
            var cache = new RunScopedAsyncZeroArgPropertyResultCache();
            var live = -1;
            var operations = HostOperations.Create(
                HostOperation.CreateAsync("hop", async (_, _) =>
                {
                    await Task.Yield();
                    return new Result.Atom(0);
                }),
                HostOperation.CreateAsync("probe", async (_, _) =>
                {
                    // Read the same table on both threads while the evaluator is waiting for this probe.
                    var beforeCollection = cache.LivePartitionCount();
                    var suspended = Environment.CurrentManagedThreadId;
                    await new Suspension(onANewThread: true);
                    AssertOnANewThread(Resumption.After(suspended));
                    ForceFullCollection();
                    live = cache.LivePartitionCount();
                    Assert.InRange(live, 0, beforeCollection);
                    return new Result.Atom(0);
                }));
            var source = "G(v) = v + 1\nStep(x) = { P = x.G + hop() * 0\nP + 0 }\n"
                + $"Step(0).repeat({steps.ToString(CultureInfo.InvariantCulture)}) + probe() * 0";
            var parsed = await SourceProvenance.ParseValidAsync(source, new RunOptions { HostOperations = operations });
            var (result, _) = await Evaluator.RunCountedObservedAsync(
                new Expr.AlgorithmExpr(parsed.Root), zeroArgPropertyResultCache: cache, hostOperations: operations);
            return (Result: result, cache.PublishedCount, cache.PromptTableCapacity, Live: live);
        })));

        foreach (var outcome in outcomes)
        {
            output.WriteLine($"run: {outcome.PublishedCount} published, "
                + $"table capacity {outcome.PromptTableCapacity}, {outcome.Live} live partitions at the probe");
            Assert.True(outcome.Result.IsOk, outcome.Result.IsError ? outcome.Result.Error.ToString() : "");
            Assert.Equal(steps.ToString(CultureInfo.InvariantCulture), SixRouteAgreement.Neutral(outcome.Result.Value.Value));
            Assert.True(outcome.PublishedCount >= steps, $"published {outcome.PublishedCount}");
            Assert.InRange(outcome.Live, 0, 64);
        }
    }

#if DEBUG
    /// <summary>
    /// The DEBUG tripwire of the sequential premise: an operation that begins while another one is still running
    /// throws instead of racing a reclamation. Simulated by marking the table busy (no schedule can interleave two
    /// operations deterministically); the private names are pinned here, so a rename fails this test.
    /// </summary>
    [Fact]
    public void PromptReclaimTable_RejectsAnOverlappingOperation_InDebugBuilds()
    {
        var table = new BindingContextPartitionTable(storeCount: 1);
        var identity = new object();
        table.GetOrCreate(identity)[0] = new object(); // store 0's partition, as a PartitionedMap would add it
        var slots = typeof(BindingContextPartitionTable).GetField("_prompt", BindingFlags.Instance | BindingFlags.NonPublic)!.GetValue(table)!;
        var operating = slots.GetType().GetField("_operating", BindingFlags.Instance | BindingFlags.NonPublic)!;

        operating.SetValue(slots, 1);
        var overlap = Assert.Throws<InvalidOperationException>(() => table.Find(identity));
        Assert.Contains("serialize access", overlap.Message, StringComparison.Ordinal);
        Assert.Throws<InvalidOperationException>(() => table.GetOrCreate(new object()));
        Assert.Throws<InvalidOperationException>(() => table.LivePartitionCount(0));

        operating.SetValue(slots, 0);
        Assert.NotNull(table.Find(identity));
        Assert.Equal(1, table.LivePartitionCount(0));
        GC.KeepAlive(identity);
    }
#endif

    // ── One sequential flow: one run's cache, read from whatever thread its continuations reach ──

    private sealed record FlowReport(Flow Flow, List<(object Identity, int Round)> Kept, int Capacity);

    private static async Task<FlowReport> RunFlowAsync()
    {
        var flow = new Flow();
        await flow.PublishExportedAsync();
        var kept = new List<(object Identity, int Round)>();
        for (var round = 0; round < Rounds; round++)
        {
            // The round's identity lives in the round's own state machine, so it dies when the round ends
            // unless the round returns it to be kept.
            if (await flow.RoundAsync(round, keep: round % KeepEvery == 0) is { } identity)
                kept.Add((identity, round));
            if (round % CollectEvery == CollectEvery - 1)
                GC.Collect(1, GCCollectionMode.Forced, blocking: true);
        }

        return new FlowReport(flow, kept, flow.Cache.PromptTableCapacity);
    }

    private sealed class Flow
    {
        private readonly Algorithm.User _owner = new(null, [], [], [], [new Expr.Num(0)]);
        private readonly object _run = new();

        internal RunScopedAsyncZeroArgPropertyResultCache Cache { get; } = new();
        internal Property P { get; } = LocalOnly("P");
        internal Property Q { get; } = LocalOnly("Q");
        internal Property E { get; } = new("E", new Algorithm.User(null, [], [], [], [new Expr.Num(0)]));
        private Property Failing { get; } = LocalOnly("F");
        private Property Cancelled { get; } = LocalOnly("C");
        internal HashSet<int> Threads { get; } = [];
        internal List<Resumption> NewThreadResumptions { get; } = [];
        internal int Evaluations { get; private set; }
        internal int ExpectedEvaluations { get; private set; }
        internal int ExpectedPublished { get; private set; }

        internal ZeroArgPropertyExecution Read(Property binding, object identity)
            => new(_owner, binding, ZeroArgPropertyAccessKind.Lexical, identity, _run);

        internal async Task PublishExportedAsync()
        {
            Assert.Equal(-7, Value(await Cache.GetOrEvaluateAsync(Read(E, new object()), () => Evaluate(-7))));
            ExpectedEvaluations++;
            ExpectedPublished++;
        }

        /// <summary>One loop step's binding context: returns the identity only when it is kept.</summary>
        internal async Task<object?> RoundAsync(int round, bool keep)
        {
            var identity = new object();
            Note();

            // A miss that owns P, hops to another thread, and publishes a nested Q before P.
            var owned = await Cache.GetOrEvaluateAsync(Read(P, identity), async () =>
            {
                Evaluations++;
                var suspended = Environment.CurrentManagedThreadId;
                await Hop(round);
                Note();
                if (OnANewThread(round))
                    NewThreadResumptions.Add(Resumption.After(suspended));
                // After a new-thread hop, this lookup and publication run on the new thread.
                var nested = await Cache.GetOrEvaluateAsync(Read(Q, identity), () => Evaluate(10 * round + 1));
                Assert.Equal(10 * round + 1, Value(nested));
                Assert.Equal(10 * round + 1, Value(await Cache.GetOrEvaluateAsync(Read(Q, identity), MustHit)));
                return EvalResult<ZeroArgPropertyResult>.Ok(new(new Result.Atom(round), 1));
            });
            ExpectedEvaluations += 2;
            ExpectedPublished += 2;
            Assert.Equal(round, Value(owned));
            Note();
            Assert.Equal(round, Value(await Cache.GetOrEvaluateAsync(Read(P, identity), MustHit)));
            Assert.Equal(-7, Value(await Cache.GetOrEvaluateAsync(Read(E, identity), MustHit)));

            if (round % 5 == 1)
            {
                // An invocation always executes and never replaces the established entry.
                var invoked = await Cache.InvokeAsync(Read(P, identity), async () =>
                {
                    Evaluations++;
                    await Hop(round);
                    return EvalResult<ZeroArgPropertyResult>.Ok(new(new Result.Atom(-round), 1));
                });
                ExpectedEvaluations++;
                Assert.Equal(-round, Value(invoked));
                Assert.Equal(round, Value(await Cache.GetOrEvaluateAsync(Read(P, identity), MustHit)));
            }

            if (round % 7 == 2)
            {
                // A failure is never published: the next read evaluates again.
                for (var attempt = 0; attempt < 2; attempt++)
                {
                    var failed = await Cache.GetOrEvaluateAsync(Read(Failing, identity), async () =>
                    {
                        Evaluations++;
                        await Hop(round);
                        return new EvalError.UnknownName("missing");
                    });
                    ExpectedEvaluations++;
                    Assert.True(failed.IsError);
                }
            }

            if (round % 11 == 3)
            {
                // Cancellation propagates, clears ownership and publishes nothing; a later read owns the key.
                using var stop = new CancellationTokenSource();
                await stop.CancelAsync();
                var thrown = await Assert.ThrowsAsync<OperationCanceledException>(async () =>
                    await Cache.GetOrEvaluateAsync(Read(Cancelled, identity), async () =>
                    {
                        Evaluations++;
                        await Hop(round);
                        stop.Token.ThrowIfCancellationRequested();
                        return EvalResult<ZeroArgPropertyResult>.Ok(new(new Result.Atom(0), 1));
                    }));
                Assert.Equal(stop.Token, thrown.CancellationToken);
                Assert.Equal(0, Cache.ActiveOwnerCount);
                Assert.Equal(round + 2, Value(await Cache.GetOrEvaluateAsync(Read(Cancelled, identity), () => Evaluate(round + 2))));
                Assert.Equal(round + 2, Value(await Cache.GetOrEvaluateAsync(Read(Cancelled, identity), MustHit)));
                ExpectedEvaluations += 2;
                ExpectedPublished++;
            }

            Note();
            return keep ? identity : null;
        }

        private ValueTask<EvalResult<ZeroArgPropertyResult>> Evaluate(int value)
        {
            Evaluations++;
            return new(EvalResult<ZeroArgPropertyResult>.Ok(new(new Result.Atom(value), 1)));
        }

        private void Note() => Threads.Add(Environment.CurrentManagedThreadId);

        // A genuine suspension: usually back to the pool, and every NewThreadHopEvery rounds onto a new thread.
        private static Suspension Hop(int round) => new(OnANewThread(round));

        private static bool OnANewThread(int round) => round % NewThreadHopEvery == 0;

        private static Property LocalOnly(string name)
            => new(name, new Algorithm.User(null, [], [], [], [new Expr.Num(0)]), Exposure: PropertyExposure.LocalOnlyCapturedAncestorParameters);
    }

    /// <summary>Where a suspended flow resumed: the suspending thread's id, and the resuming thread's id and kind.</summary>
    private readonly record struct Resumption(int Suspended, int Resumed, bool OnAPoolThread)
    {
        internal static Resumption After(int suspended)
            => new(suspended, Environment.CurrentManagedThreadId, Thread.CurrentThread.IsThreadPoolThread);
    }

    // A new-thread hop resumed the flow on a thread of its own: no pool worker, and not the one that suspended.
    private static void AssertOnANewThread(Resumption hop)
    {
        Assert.False(hop.OnAPoolThread, $"a new-thread hop resumed on pool thread {hop.Resumed}");
        Assert.NotEqual(hop.Suspended, hop.Resumed);
    }

    /// <summary>
    /// An awaitable that always suspends: through the thread pool, like <see cref="Task.Yield"/>, which may resume the
    /// awaiting code on the very worker that suspended, or onto a NEW thread, which runs the awaiting code itself. The
    /// suspending thread starts that thread while it is still running, so the two never share a managed thread id: a
    /// new-thread hop moves the flow to another thread on every schedule. (Awaiting a long-running task does not: when the
    /// task has finished before the await, the awaiting code simply continues on its own thread.)
    /// </summary>
    private readonly struct Suspension(bool onANewThread) : ICriticalNotifyCompletion
    {
        private readonly bool _onANewThread = onANewThread;

        public Suspension GetAwaiter() => this;

        public bool IsCompleted => false;

        public void GetResult()
        {
        }

        public void OnCompleted(Action continuation)
        {
            if (_onANewThread)
                new Thread(continuation.Invoke) { IsBackground = true }.Start();
            else
                Task.Yield().GetAwaiter().OnCompleted(continuation);
        }

        // The async method builder restores the awaiting method's execution context itself.
        public void UnsafeOnCompleted(Action continuation)
        {
            if (_onANewThread)
                new Thread(continuation.Invoke) { IsBackground = true }.UnsafeStart();
            else
                Task.Yield().GetAwaiter().UnsafeOnCompleted(continuation);
        }
    }

    private static ValueTask<EvalResult<ZeroArgPropertyResult>> MustHit()
        => throw new InvalidOperationException("an established entry must be served without evaluating");

    private static int Value(EvalResult<ZeroArgPropertyResult> result)
    {
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        return int.Parse(SixRouteAgreement.Neutral(result.Value.Value), CultureInfo.InvariantCulture);
    }

    private static void ForceFullCollection()
    {
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
        GC.WaitForPendingFinalizers();
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
    }
}

/// <summary>
/// The peak-memory guards of a binding context minted per loop step (property-cache prompt reclaim, 2026-11-17;
/// deconstruction-memo prompt reclaim, 2026-11-18): a local-only property per step, a local-only property holding a
/// call reference per step, a local-only runtime alias per step, a local-only deconstruction per step, and that
/// deconstruction under the uncached property cache's statistics. Each program runs in a fresh
/// <see cref="SubprocessProbe"/> child — on the default engine (<see cref="KatLangEngine.Run"/>), except the
/// uncached-statistics loop, which no engine run takes and the child runs on the internal evaluator with
/// <see cref="UncachedZeroArgPropertyResultCache.CreateForRun"/> — and reports its peak working set; the parent
/// compares 10⁵ with 10⁶ rounds. Measured in Release, one process per run, peak working set at 10⁵ / 10⁶ / 3·10⁶
/// rounds (the live heap after a forced collection stayed under 4 MiB in every run): with the property cache's
/// former ConditionalWeakTable the property loop grew 61.5 / 109.0 / 214.3 MiB and the call-reference loop
/// 61.7 / 103.6 / 170.0 MiB; with the prompt-reclaim table they stay at 56.5 / 57.0 / 57.2 and 57.6 / 58.1 / 58.1 MiB.
/// The alias loop, whose cells moved to that table first (ALIAS-CELL-LIFETIME), stays at 57.0 / 57.6 / 57.7 MiB. With
/// the deconstruction memo's former ConditionalWeakTable the deconstruction loop grew 63.6 / 101.3 / 156.3 MiB, and
/// under the uncached cache, whose seen-key set had that table too, 65.0 / 104.7 / 191.9 MiB; with the prompt-reclaim
/// table they stay at 58.7 / 59.7 / 59.2 and 58.8 / 59.1 / 59.1 MiB.
/// </summary>
public sealed class LocalOnlyLoopStepPeakMemoryProcessTests(ITestOutputHelper output)
{
    private const string Child = "KATLANG_LOOP_STEP_PEAK_CHILD";
    private const string Variant = "KATLANG_LOOP_STEP_PEAK_VARIANT";
    private const string Rounds = "KATLANG_LOOP_STEP_PEAK_ROUNDS";
    private const string Marker = "KATLANG_LOOP_STEP_PEAK_MARKER";
    private const string UncachedStatisticsDeconstruction = "uncached-statistics-deconstruction";
    private const int FewRounds = 100_000;
    private const int ManyRounds = 1_000_000;
    // The former tables grew by 38–48 MiB between the two sizes in Release; the flat profile by about 1 MiB.
    // Re-measured on 2026-11-20 before deciding whether to tighten (MiB, one child per run): the uncached-statistics
    // loop grew 0.1–0.6 in Debug and Release on Windows (13 pairs each, before and after the prompt-reclaim table
    // became the only form) and 0.5–0.7 in Debug on Linux (WSL, 5), and
    // 31.5–37.2 with its two stores in the former ConditionalWeakTable. This bound already lies far between the two,
    // so it was left unchanged.
    private const long AllowedGrowthBytes = 16L * 1024 * 1024;

    /// <summary>The loop of <paramref name="variant"/> over <paramref name="rounds"/> rounds; its value is the round count.</summary>
    internal static string Program(string variant, int rounds)
    {
        var step = variant switch
        {
            "local-property" => "G(v) = v + 1\nStep(x) = { P = x.G + 0\nP + 0 }",
            "call-reference-property" => "Cap(meta r) = r\nInc(y) = y + 1\nStep(n) = { R = Cap(Inc(n))\nn + 1 + R.Invoke() * 0 }",
            "runtime-alias" => "G(v) = v + 1\nStep(x) = { A = x.G\nA + 0 }",
            // Both targets read one shared bind of the step's local-only source.
            "local-deconstruction" or UncachedStatisticsDeconstruction => "Step(x) = { a, b = x + 1, x\na + b * 0 }",
            _ => throw new ArgumentOutOfRangeException(nameof(variant), variant, "Unknown loop-step variant."),
        };
        return step + "\nStep(0).repeat(" + rounds.ToString(CultureInfo.InvariantCulture) + ")";
    }

    [Theory]
    [InlineData("local-property")]
    [InlineData("call-reference-property")]
    [InlineData("runtime-alias")]
    [InlineData("local-deconstruction")]
    [InlineData(UncachedStatisticsDeconstruction)]
    [Trait("Tier", "Slow")]
    public async Task PeakWorkingSet_StaysWithinSixteenMiB_FromTenToTheFifthToTenToTheSixthRounds(string variant)
    {
        var few = await PeakWorkingSetAsync(variant, FewRounds);
        var many = await PeakWorkingSetAsync(variant, ManyRounds);
        var summary = $"{variant}: peak working set {few / 1048576.0:F1} MiB at {FewRounds} rounds, "
            + $"{many / 1048576.0:F1} MiB at {ManyRounds} rounds";
        output.WriteLine(summary);
        Assert.True(many - few < AllowedGrowthBytes, summary);
    }

    [Fact]
    public void PeakChild()
    {
        if (Environment.GetEnvironmentVariable(Child) != "1")
            return;

        var rounds = int.Parse(Environment.GetEnvironmentVariable(Rounds)!, CultureInfo.InvariantCulture);
        var variant = Environment.GetEnvironmentVariable(Variant)!;
        var source = Program(variant, rounds);
        if (variant == UncachedStatisticsDeconstruction)
        {
            var parsed = Parser.Parse(source);
            Assert.False(parsed.HasErrors);
            var cache = UncachedZeroArgPropertyResultCache.CreateForRun();
            var result = Evaluator.RunCounted(new Expr.AlgorithmExpr(parsed.Root), cache);
            Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
            Assert.Equal(rounds.ToString(CultureInfo.InvariantCulture), SixRouteAgreement.Neutral(result.Value.Value));
            // Every step's source and two targets are seen keys of the step's own binding context.
            Assert.Equal(3 * rounds, cache.GetSnapshot().DistinctKeysCreated);
        }
        else
        {
            var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
            Assert.Equal(rounds.ToString(CultureInfo.InvariantCulture), success.ToDisplayString());
        }

        using var process = Process.GetCurrentProcess();
        process.Refresh();
        File.WriteAllText(
            Environment.GetEnvironmentVariable(Marker)!,
            process.PeakWorkingSet64.ToString(CultureInfo.InvariantCulture));
    }

    private static async Task<long> PeakWorkingSetAsync(string variant, int rounds)
    {
        var marker = Path.Combine(Path.GetTempPath(), $"katlang-loop-step-peak-{Guid.NewGuid():N}.txt");
        var start = SubprocessProbe.StartInfo(typeof(LocalOnlyLoopStepPeakMemoryProcessTests), nameof(PeakChild));
        start.Environment[Child] = "1";
        start.Environment[Variant] = variant;
        start.Environment[Rounds] = rounds.ToString(CultureInfo.InvariantCulture);
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
