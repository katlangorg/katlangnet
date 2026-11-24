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
/// and counts the stages still reachable. The count is deterministic — it depends on reachability
/// only — and must not grow with the rounds when every round reads its new stage, while a round
/// that leaves positions unread keeps every stage (their steps are still pending: the controls).
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

    private sealed record Probed(string Outcome, int Built, int Alive);

    private static void ForceFullCollection()
    {
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
        GC.WaitForPendingFinalizers();
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
    }

    /// <summary>
    /// Runs <paramref name="source"/> with the stage recorder active and returns its outcome and the
    /// stages still reachable at <c>probe()</c>. On the twin route every host operation suspends
    /// (<c>pause(x)</c> returns <c>x</c> after yielding), so each step that calls it resumes on
    /// another thread before its stage can be released.
    /// </summary>
    private static async Task<Probed> RunProbedAsync(string source, bool twin)
    {
        using var recorder = LazyStageTestSeam.Activate();
        var alive = -1;
        int Count()
        {
            ForceFullCollection();
            return recorder.Alive();
        }

        var operations = twin
            ? HostOperations.Create(
                HostOperation.CreateAsync("probe", async (_, _) =>
                {
                    await Task.Yield();
                    alive = Count();
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
        return new Probed(outcome, recorder.Built, alive);
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
        foreach (var twin in new[] { false, true })
        {
            var few = await RunProbedAsync(Loop(ForceAll, step, 60), twin);
            var many = await RunProbedAsync(Loop(ForceAll, step, 240), twin);
            Assert.Equal($"ok S[{fewRoundsSum}, 0]", few.Outcome);
            Assert.Equal($"ok S[{manyRoundsSum}, 0]", many.Outcome);
            Assert.Equal(60 * stagesPerRound, few.Built);
            Assert.Equal(240 * stagesPerRound, many.Built);
            // At most the last round's stages are reachable, however many rounds ran (every earlier
            // stage was reachable before the release: 60 and 240 rounds' worth). One more is
            // tolerated: on a twin run, a thread-pool continuation can briefly hold the previous
            // round's context (seen only on a process's first twin run).
            Assert.InRange(few.Alive, 1, stagesPerRound + 1);
            Assert.InRange(many.Alive, 1, stagesPerRound + 1);
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
            var whole = await RunProbedAsync(Loop(ForceFirst, step, 60), twin);
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
            var whole = await RunProbedAsync("Step(xs) = xs.map{x + 1}\nS = repeat(Step([1, 2]), 200)\nS.sum, probe()", twin);
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
            var probed = await RunProbedAsync(ForceAll + "Step(xs) = Force(xs.filter{x > 0}.take(2))\nS = repeat(Step([1, 2]), 100)\nS.sum, probe()", twin);
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
}
