using System.Globalization;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// A STAGE RELEASES WHAT ONLY ITS STEPS READ (lazy collections, issue #204; C#-only host policy, no
/// Lean counterpart: Lean's deferred applications model no memory). A <c>map</c> stage whose
/// positions are all found and all resolved, and a <c>filter</c> scan that has judged every
/// candidate its source will ever have, run no further step, so they let go of their source, the
/// root that found their positions, the callback and the environment of the call that built them;
/// they keep their cells, so every reader still shares each position's one outcome
/// (<c>Evaluator.MappedList.ReleaseIfResolved</c>, <c>Evaluator.FilteredList.Release</c>). Before,
/// a loop that composed a new stage every round and read it kept every earlier round's stage
/// reachable through the newest one: about 266 bytes per resolved mapped position, 19 MiB more
/// live heap after 1,000 rounds of 100 positions than after 250 (measured 2026-11-24).
/// <para>The REACHABILITY GUARD: <see cref="LazyStageTestSeam"/> records every stage the run builds,
/// weakly; a host operation <c>probe()</c> runs after the loop, forces a full blocking collection
/// and counts the stages still reachable. The count depends on reachability only — exactly so on the
/// synchronous route; a twin probe first lets the thread pool drop what it holds only for a moment
/// (<c>RunProbedAsync</c>) — and must not grow with the rounds when every round reads its new stage,
/// while a round that leaves positions unread keeps every stage (their steps are still pending: the
/// controls).
/// Values, effects and their order are pinned on the six routes; the release changes none of
/// them.</para>
/// </summary>
public sealed class LazyStageRetentionTests
{
    // Reads every position of the round's new list, then returns that same list.
    private const string ForceAll = "Force(l) = if(sum(l) >= 0, l, l)\n";

    // Reads only the first position of the round's new list.
    private const string ForceFirst = "Force(l) = if(first(l) >= 0, l, l)\n";

    private static string Rounds(int rounds) => rounds.ToString(CultureInfo.InvariantCulture);

    /// <summary>
    /// A loop of <paramref name="rounds"/> rounds that keeps only the round's result list, then
    /// <paramref name="reader"/> of the last list and the probe.
    /// </summary>
    private static string Loop(string force, string step, int rounds, string reader = "sum")
        => force + "Step(xs) = Force(" + step + ")\nS = repeat(Step([1, 2, 3, 4, 5, 6, 7, 8]), " + Rounds(rounds) + ")\nS." + reader + ", probe()";

    // ── The reachability probe ────────────────────────────────────────────────────────────

    /// <summary>
    /// A probed run: its outcome; the stages it built and how many are reachable at the probe; and the
    /// same for the list literals it built with a deferred element and for their elements' suspensions
    /// (the literals' environments).
    /// </summary>
    private sealed record Probed(
        string Outcome, int Built, int Alive,
        int LiteralsBuilt = 0, int LiteralsAlive = 0, int SuspensionsBuilt = 0, int SuspensionsAlive = 0);

    private static void ForceFullCollection()
    {
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
        GC.WaitForPendingFinalizers();
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
    }

    // How often, and how far apart, a twin probe counts again while it finds more stages than its bound.
    private const int SettleAttempts = 20;
    private const int SettleDelayMilliseconds = 50;

    /// <summary>
    /// Queues a burst of no-op work items on the thread pool's global queue and waits for all of them:
    /// idle workers get other work to run, in place of the last continuation they ran.
    /// </summary>
    private static Task ThreadPoolTurnoverAsync()
    {
        var items = 2 * Math.Max(ThreadPool.ThreadCount, Environment.ProcessorCount);
        var remaining = items;
        var done = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        void Run(int _)
        {
            if (Interlocked.Decrement(ref remaining) == 0) done.SetResult();
        }

        for (var i = 0; i < items; i++) ThreadPool.UnsafeQueueUserWorkItem(Run, 0, preferLocal: false);
        return done.Task;
    }

    /// <summary>
    /// Runs <paramref name="source"/> with the stage recorder active and returns its outcome and the
    /// stages still reachable at <c>probe()</c>. On the twin route every host operation suspends
    /// (<c>pause(x)</c> returns <c>x</c> after yielding), so each step that calls it resumes on
    /// another thread before its stage can be released.
    /// <para>The synchronous count is exact: the run never leaves the test's thread. A twin count is
    /// not: thread-pool work of the last rounds (for example a continuation still in flight, or an
    /// execution context captured while a step's cell was current, <c>NeedCell.Current</c>) can hold
    /// an earlier round's stage for a moment after the run stopped needing it. A probe given
    /// <paramref name="settleTo"/> therefore counts again, after the thread pool has run other work,
    /// while it finds more stages than that, up to <see cref="SettleAttempts"/> times. A collected
    /// stage never comes back, and nothing of the run executes while the probe waits, so a stage the
    /// run itself still holds is counted in every attempt: the bound still catches every retention
    /// the release removed.</para>
    /// <para><paramref name="settleLiteralsTo"/> and <paramref name="settleSuspensionsTo"/> bound, the same way, the
    /// literals and the element suspensions a twin probe may still find reachable.</para>
    /// </summary>
    private static async Task<Probed> RunProbedAsync(
        string source, bool twin, int? settleTo = null, int? settleLiteralsTo = null, int? settleSuspensionsTo = null)
    {
        using var recorder = LazyStageTestSeam.Activate();
        var alive = -1;
        var literalsAlive = -1;
        var suspensionsAlive = -1;
        int Count()
        {
            ForceFullCollection();
            literalsAlive = recorder.LiteralsAlive();
            suspensionsAlive = recorder.ElementSuspensionsAlive();
            return recorder.Alive();
        }

        bool Settled()
            => (settleTo is not { } bound || alive <= bound)
                && (settleLiteralsTo is not { } literalBound || literalsAlive <= literalBound)
                && (settleSuspensionsTo is not { } suspensionBound || suspensionsAlive <= suspensionBound);

        var operations = twin
            ? HostOperations.Create(
                HostOperation.CreateAsync("probe", async (_, _) =>
                {
                    await Task.Yield();
                    alive = Count();
                    for (var attempt = 0; !Settled() && attempt < SettleAttempts; attempt++)
                    {
                        await ThreadPoolTurnoverAsync();
                        await Task.Delay(SettleDelayMilliseconds);
                        alive = Count();
                    }

                    return new Result.Atom(0);
                }),
                HostOperation.CreateAsync("pause", async (args, _) =>
                {
                    await Task.Yield();
                    return args[0];
                }, "x"))
            : HostOperations.Create(
                HostOperation.Create("probe", (_, _) =>
                {
                    alive = Count();
                    return new Result.Atom(0);
                }),
                HostOperation.Create("pause", static (args, _) => args[0], "x"));
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        var program = new Expr.AlgorithmExpr(parsed.Root);
        var result = twin
            ? await Evaluator.RunCountedAsync(program, new RunScopedAsyncZeroArgPropertyResultCache(), hostOperations: operations)
            : Evaluator.RunCountedObserved(program, hostOperations: operations).Result;
        var outcome = result.IsOk ? "ok " + SixRouteAgreement.Neutral(result.Value.Value) : "err " + result.Error.Code;
        return new Probed(outcome, recorder.Built, alive,
            recorder.LiteralsBuilt, literalsAlive, recorder.ElementSuspensionsBuilt, suspensionsAlive);
    }

    // ── 1. A loop that reads every position of its new stage keeps only its last round ────────

    /// <summary>step, stages each round builds, the sum after 60 rounds, the sum after 240 rounds.</summary>
    public static TheoryData<string, int, string, string> EveryRoundReadsItsStage() => new()
    {
        // The issue's loop: a new map stage every round, read whole by the round itself.
        { "xs.map{x + 1}", 1, "516", "1956" },
        // Mixed pipelines: every stage of the round is read through the last one.
        { "xs.map{x + 1}.filter{x > 0}.take(8)", 3, "516", "1956" },
        { "xs.filter{x > 0}.map{x + 1}", 2, "516", "1956" },
        { "xs.filter{x > 0}.take(8)", 2, "36", "36" },
        // A step that suspends: each position resumes on another thread (twin route) before release.
        { "xs.map{pause(x) + 1}", 1, "516", "1956" },
    };

    [Theory]
    [MemberData(nameof(EveryRoundReadsItsStage))]
    public async Task ALoopThatReadsItsNewStageEveryRound_KeepsOnlyTheLastRoundReachable(
        string step, int stagesPerRound, string fewRoundsSum, string manyRoundsSum)
    {
        // At most the last round's stages are reachable, however many rounds ran (every earlier stage
        // was reachable before the release: 60 and 240 rounds' worth). One more is tolerated: on a
        // twin run, a thread-pool continuation can briefly hold the previous round's context (seen
        // only on a process's first twin run). A twin probe settles to that bound before its last
        // count (RunProbedAsync); without settling, CI once counted 3 for the `pause` step.
        var bound = stagesPerRound + 1;
        foreach (var twin in new[] { false, true })
        {
            var few = await RunProbedAsync(Loop(ForceAll, step, 60), twin, settleTo: bound);
            var many = await RunProbedAsync(Loop(ForceAll, step, 240), twin, settleTo: bound);
            Assert.Equal($"ok S[{fewRoundsSum}, 0]", few.Outcome);
            Assert.Equal($"ok S[{manyRoundsSum}, 0]", many.Outcome);
            Assert.Equal(60 * stagesPerRound, few.Built);
            Assert.Equal(240 * stagesPerRound, many.Built);
            Assert.InRange(few.Alive, 1, bound);
            Assert.InRange(many.Alive, 1, bound);
        }
    }

    // ── 2. Controls: a stage with an unread position keeps what its steps read ────────────────

    [Theory]
    [InlineData("xs.map{x + 1}", 1)]
    [InlineData("xs.map{x + 1}.filter{x > 0}.take(8)", 3)]
    [InlineData("xs.filter{x > 0}.map{x + 1}", 2)]
    public async Task ALoopThatLeavesPositionsUnread_KeepsEveryStageUntilItIsReadWhole(string step, int stagesPerRound)
    {
        foreach (var twin in new[] { false, true })
        {
            // Only the first position of each round's list is read, by the rounds and by the reader
            // before the probe: the other positions of every stage are still to be computed through
            // the stages below them.
            var partial = await RunProbedAsync(Loop(ForceFirst, step, 60, reader: "first"), twin);
            Assert.StartsWith("ok S[", partial.Outcome, StringComparison.Ordinal);
            Assert.Equal(60 * stagesPerRound, partial.Built);
            Assert.True(partial.Alive >= 60, $"{partial.Alive} of {partial.Built} stages reachable");

            // The same loop read whole before the probe: every stage is resolved, deepest first,
            // and released.
            var whole = await RunProbedAsync(Loop(ForceFirst, step, 60), twin, settleTo: stagesPerRound + 1);
            Assert.Equal(60 * stagesPerRound, whole.Built);
            Assert.InRange(whole.Alive, 1, stagesPerRound + 1);

            // Nothing is read before the probe (the result is read after it): every stage is still
            // pending. (Counting would read a scan.)
            var unread = await RunProbedAsync("Step(xs) = " + step + "\nS = repeat(Step([1, 2, 3, 4, 5, 6, 7, 8]), 60)\nS, probe()", twin);
            Assert.StartsWith("ok S[L[", unread.Outcome, StringComparison.Ordinal);
            Assert.Equal(60 * stagesPerRound, unread.Built);
            Assert.Equal(unread.Built, unread.Alive);
        }
    }

    [Fact]
    public async Task AStackBuiltUnreadAndThenReadWhole_IsReleasedStageByStage()
    {
        foreach (var twin in new[] { false, true })
        {
            // `sum` reads every position of the top stage, which reads the stages below it deepest
            // first: every stage is then resolved, and only the top one is still reachable.
            var whole = await RunProbedAsync("Step(xs) = xs.map{x + 1}\nS = repeat(Step([1, 2]), 200)\nS.sum, probe()", twin, settleTo: 2);
            Assert.Equal("ok S[403, 0]", whole.Outcome);
            Assert.Equal(200, whole.Built);
            Assert.InRange(whole.Alive, 1, 2);

            // Control: reading one position of each stage leaves the other one pending in all of them.
            var first = await RunProbedAsync("Step(xs) = xs.map{x + 1}\nS = repeat(Step([1, 2]), 200)\nS.first, probe()", twin);
            Assert.Equal("ok S[201, 0]", first.Outcome);
            Assert.Equal(200, first.Alive);
            var last = await RunProbedAsync("Step(xs) = xs.map{x + 1}\nS = repeat(Step([1, 2]), 200)\nS.last, probe()", twin);
            Assert.Equal("ok S[202, 0]", last.Outcome);
            Assert.Equal(200, last.Alive);
        }
    }

    [Fact]
    public async Task AScanStackedUnderATake_IsReleasedOnceItHasJudgedEveryCandidate()
    {
        foreach (var twin in new[] { false, true })
        {
            // Each round's scan reads the previous round's two-position prefix: it judges both
            // candidates while the round's prefix is read, so it lets go of the prefix below it
            // even though nobody asks it for a third position.
            var probed = await RunProbedAsync(ForceAll + "Step(xs) = Force(xs.filter{x > 0}.take(2))\nS = repeat(Step([1, 2]), 100)\nS.sum, probe()", twin, settleTo: 3);
            Assert.Equal("ok S[3, 0]", probed.Outcome);
            Assert.Equal(200, probed.Built);
            Assert.InRange(probed.Alive, 1, 3);
        }
    }

    // ── 3. Sharing, cycles and suspension: the released stages keep every outcome ─────────────

    private static async Task Expect(string source, string expected, string hostCalls = "")
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        var outcome = observation.Kind switch
        {
            "ok" => $"ok {observation.Value}",
            "err" => $"err {observation.Errors[0][..observation.Errors[0].IndexOf(':')]}",
            _ => observation.Kind,
        };
        Assert.Equal(expected, outcome);
        Assert.Equal(hostCalls, string.Join(",", observation.HostCalls));
    }

    public static TheoryData<string, string, string> SharedAndIndependentPipelines() => new()
    {
        // A stage shared by two later stages: the first reads it whole (and it is released); the
        // second reads its cells, so nothing is computed twice and the effects keep their order.
        { "A = [tick(), tick()].map{x * 10}\nB = A.map{x + 1}\nC = A.map{x + 2}\nB.sum, C.sum, A, tick()", "ok S[32, 34, L[10, 20], 3]", "" },
        // Two independent stages over one list share only the list's positions.
        { "L = [tick(), tick()]\nB = L.map{x + 1}\nC = L.map{x + 2}\nC.sum, B.sum, tick()", "ok S[7, 5, 3]", "" },
        // A stack built at run time, read whole by one consumer and then by others.
        { "Step(xs) = xs.map{x + 1}\nS = repeat(Step([tick(), tick()]), 50)\nS.sum, S.map{x * 2}.sum, S, tick()", "ok S[103, 206, L[51, 52], 3]", "" },
        // A scan read by two consumers; the second finds its positions already found.
        { "F = [tick(), tick(), tick()].filter{x != 2}\nF.map{x * 10}.sum, F.count, F, tick()", "ok S[40, 2, L[1, 3], 4]", "" },
        // Steps that suspend on the twin routes: the host calls keep their order.
        { "A = [1, 2].map{x + tock() * 0}\nB = A.map{x * 10}\nB.sum, A.sum, tock()", "ok S[30, 3, 3]", "tock#1,tock#2,tock#3" },
        { "Step(xs) = xs.filter{tock() > 0 and x > 0}.map{x + 1}\nS = repeat(Step([1, 2]), 3)\nS.sum, S, tock()", "ok S[9, L[4, 5], 7]", "tock#1,tock#2,tock#3,tock#4,tock#5,tock#6,tock#7" },
    };

    [Theory]
    [MemberData(nameof(SharedAndIndependentPipelines))]
    public async Task ReleasedStages_KeepEveryOutcomeAndEffectOrder(string source, string expected, string hostCalls)
        => await Expect(source, expected, hostCalls);

    [Theory]
    // A position that reads another position of its own stage: both resolve, then the stage is released.
    [InlineData("M = [1, 2].map{if(x == 1, M[1], 7)}\nM", "ok L[7, 7]")]
    // A position that reads itself is a demand cycle, kept in its cell like any outcome.
    [InlineData("M = [1, 2].map{x + M[1]}\nM", "err DemandCycle")]
    [InlineData("M = [1, 2].map{x + M[1]}\nM.count, M[0]", "err DemandCycle")]
    // A stage over a stack read whole first, then a stage over it that reads itself.
    [InlineData("Step(xs) = xs.map{x + 1}\nS = repeat(Step([1, 2]), 40)\nT = S.map{x + T.count}\nS.sum, T", "ok S[83, L[43, 44]]")]
    [InlineData("Step(xs) = xs.map{x + 1}\nS = repeat(Step([1, 2]), 40)\nT = S.map{x + T[1]}\nS.sum, T.first", "err DemandCycle")]
    public async Task ADemandCycleInAStage_IsKeptAfterTheStageIsReleased(string source, string expected)
        => await Expect(source, expected);

    // ── 4. List literals: a completed element lets go of the literal's environment ────────────

    /// <summary>
    /// A loop of <paramref name="rounds"/> rounds whose step builds a new LIST LITERAL from the previous
    /// round's list, then <paramref name="reader"/> and the probe. A deferred element's suspension is the
    /// literal's environment: the step's activation, whose parameter cell holds the previous round's list.
    /// While a completed element's cell kept it, every earlier round stayed reachable through the newest
    /// list, although the element's value is a number that needs none of it: about 1.2 KB per round,
    /// 0.52 MiB of live heap after 250 rounds of a two-element literal and 1.45 MiB after 1,000 (measured
    /// 2026-11-25; root path cell → suspension → activation → parameter cell → previous list → its cells).
    /// A completed element's cell now keeps only its outcome (<c>NeedCell.ReleaseElementSuspension</c>).
    /// </summary>
    private static string LiteralLoop(string force, string step, string init, int rounds, string reader)
        => force + "Step(xs) = Force(" + step + ")\nS = repeat(Step(" + init + "), " + Rounds(rounds) + ")\n" + reader + ", probe()";

    /// <summary>
    /// force, step, initial list, reader, literals and element suspensions each round builds, those the
    /// initial list builds, the reader's value after 60 rounds and after 240 rounds.
    /// </summary>
    public static TheoryData<string, string, string, string, int, int, int, string, string> EveryRoundReadsItsLiteral() => new()
    {
        // The report's loop: both elements of each round's literal are read by the round itself.
        { ForceAll, "[xs[0] + 1, xs[1] + 1]", "[1, 2]", "S.sum", 1, 2, 0, "123", "483" },
        // Elements that suspend: each resumes on another thread (twin route) before it completes.
        { ForceAll, "[pause(xs[0]) + 1, pause(xs[1]) + 1]", "[1, 2]", "S.sum", 1, 2, 0, "123", "483" },
        // Both expressions can project when supplied as arguments. Here they are fresh literal
        // positions. Their scalar results release the link receiver and the caller that bound xs.
        { ForceAll + "One = 1\nMake(meta op, xs) = [op.Algorithm, xs.first]\n",
            "Make(One(), xs)", "[1, 2]", "S.sum", 1, 2, 0, "2", "2" },
        // A nested literal: the inner list is built when the outer element is read (the initial list's
        // own nested element is one more deferred literal).
        { "Force(l) = if(l[0][0] + l[1] >= 0, l, l)\n", "[[xs[0][0] + 1], xs[1] + 1]", "[[1], 2]", "S[0][0] + S[1]", 2, 3, 1, "123", "483" },
        // A literal shared by two readers each round: the sum and a map stage over it.
        { "Force(l) = if(sum(l) + l.map{x * 2}.sum >= 0, l, l)\n", "[xs[0] + 1, xs[1] + 1]", "[1, 2]", "S.sum", 1, 2, 0, "123", "483" },
        // An explicit spread is formed with its list: the spread literal's element is read then.
        { ForceAll, "[[xs[0] + 1]*, xs[1] + 1]", "[1, 2]", "S.sum", 2, 2, 0, "123", "483" },
    };

    [Theory]
    [MemberData(nameof(EveryRoundReadsItsLiteral))]
    public async Task ALoopThatReadsItsNewLiteralEveryRound_KeepsNoEarlierRoundReachable(
        string force, string step, string init, string reader, int literalsPerRound, int elementsPerRound, int initial,
        string fewRoundsValue, string manyRoundsValue)
    {
        // At most the last round's literals are reachable, and no read element keeps its suspension,
        // however many rounds ran (before, every round's literals and suspensions were). One more
        // literal is tolerated, as for stages: a twin probe settles to that bound (RunProbedAsync).
        var bound = literalsPerRound + 1;
        foreach (var twin in new[] { false, true })
        {
            var few = await RunProbedAsync(LiteralLoop(force, step, init, 60, reader), twin, settleLiteralsTo: bound, settleSuspensionsTo: bound);
            var many = await RunProbedAsync(LiteralLoop(force, step, init, 240, reader), twin, settleLiteralsTo: bound, settleSuspensionsTo: bound);
            Assert.Equal($"ok S[{fewRoundsValue}, 0]", few.Outcome);
            Assert.Equal($"ok S[{manyRoundsValue}, 0]", many.Outcome);
            Assert.Equal(60 * literalsPerRound + initial, few.LiteralsBuilt);
            Assert.Equal(240 * literalsPerRound + initial, many.LiteralsBuilt);
            Assert.Equal(60 * elementsPerRound + initial, few.SuspensionsBuilt);
            Assert.Equal(240 * elementsPerRound + initial, many.SuspensionsBuilt);
            Assert.InRange(few.LiteralsAlive, 1, bound);
            Assert.InRange(many.LiteralsAlive, 1, bound);
            Assert.InRange(few.SuspensionsAlive, 0, twin ? bound : 0);
            Assert.InRange(many.SuspensionsAlive, 0, twin ? bound : 0);
        }
    }

    [Fact]
    public async Task ALoopThatLeavesElementsUnread_KeepsEveryLiteralWithItsEnvironmentUntilItIsRead()
    {
        const string step = "[xs[0] + 1, xs[1] + 1]";
        foreach (var twin in new[] { false, true })
        {
            // Each round reads only the first element of its literal: every round's second element is
            // still to be computed from the previous round's list, so it keeps that environment.
            var partial = await RunProbedAsync(LiteralLoop(ForceFirst, step, "[1, 2]", 60, "S.first"), twin);
            Assert.Equal("ok S[61, 0]", partial.Outcome);
            Assert.Equal(60, partial.LiteralsBuilt);
            Assert.Equal(60, partial.LiteralsAlive);
            Assert.InRange(partial.SuspensionsAlive, 60, 120);

            // The same loop read whole before the probe: every pending element is computed, from the
            // first round's on, and lets go of its environment.
            var whole = await RunProbedAsync(LiteralLoop(ForceFirst, step, "[1, 2]", 60, "S.sum"), twin, settleLiteralsTo: 2, settleSuspensionsTo: 2);
            Assert.Equal("ok S[123, 0]", whole.Outcome);
            Assert.InRange(whole.LiteralsAlive, 1, 2);
            Assert.InRange(whole.SuspensionsAlive, 0, twin ? 2 : 0);

            // Nothing is read before the probe (the result is read after it): every element is pending.
            var unread = await RunProbedAsync("Step(xs) = " + step + "\nS = repeat(Step([1, 2]), 60)\nS, probe()", twin);
            Assert.Equal("ok S[L[61, 62], 0]", unread.Outcome);
            Assert.Equal(60, unread.LiteralsAlive);
            Assert.Equal(120, unread.SuspensionsAlive);
        }
    }

    [Fact]
    public async Task AnElementWhoseValueIsThePreviousList_KeepsEveryListButNoEnvironment()
    {
        // The control whose OUTCOME keeps its input: the second element's value is the previous
        // round's list, so every round's list stays reachable as a nested result, exactly as before.
        // What the elements' suspensions held — every round's activation — is no longer reachable.
        const string force = "Force(l) = if(l[0] + l[1].count >= 0, l, l)\n";
        foreach (var twin in new[] { false, true })
        {
            var kept = await RunProbedAsync(LiteralLoop(force, "[xs[0] + 1, if(true, xs, xs)]", "[1, 2]", 60, "S.count"), twin, settleSuspensionsTo: 2);
            Assert.Equal("ok S[2, 0]", kept.Outcome);
            Assert.Equal(60, kept.LiteralsBuilt);
            Assert.Equal(120, kept.SuspensionsBuilt);
            Assert.Equal(60, kept.LiteralsAlive);
            Assert.InRange(kept.SuspensionsAlive, 0, twin ? 2 : 0);
        }
    }
}
