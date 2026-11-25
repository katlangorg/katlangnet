using KatLang.Evaluation;

namespace KatLang.Tests;

/// <summary>
/// THE STREAMED ROUTE OF A <c>reduce</c> FOLD IS ITS NESTED EVALUATION (implementation-only optimization of lazy
/// <c>reduce</c> accumulators, November 2026; no Lean counterpart). A reducer whose first observable act is the
/// read of its accumulator (<c>acc + x</c>, <c>{x + total}</c>) demands every accumulator of its fold, so
/// <c>Evaluator.ReduceFold.Stream</c> performs the sequence the nested evaluation is known to take — every step
/// charged, last step first; the start; every step's body, first step first — without suspending a step. This
/// suite compares it with the general route, which <see cref="ReduceFoldTestSeam"/> forces: the value, every
/// error (code, message, span), the exact host-call log and the final budget counters must agree on every route,
/// and under every step limit of these short folds. It also pins which reducers the streamed route accepts.
///
/// <para><b>Not claimed.</b> The two routes charge the same total, but the streamed one charges a step's expression
/// work before its accumulator read when that step's body runs, the nested one on the way down. A fold long
/// enough for that work to fill an expression-checkpoint batch (4,096 checkpoints) can therefore stop, under a
/// step limit that runs out inside it, after more completed steps on the streamed route. No fold here is that
/// long; every production strategy takes the streamed route for such a reducer, so they agree with each other.</para>
/// </summary>
public sealed class StreamedReduceFoldEquivalenceTests
{
    /// <summary>Reducers that lead with their accumulator.</summary>
    public static readonly string[] LeadingReducers =
    [
        "R(item, acc) = acc + item",
        "R(item, acc) = item + acc",
        "R(item, acc) = acc * 10 + item",
        "R(item, acc) = (acc + item) * 2",
        "R(item, acc) = -acc + item",
        "R(item, acc) = 1 + acc",
        "R(item, acc) = acc + trace(item)",
        "R(item, acc) = acc + tock() * item",
        "R(item, acc) = acc + 10 / (item - 2)",
        "R(item, acc) = acc < item",
        "R(item, acc) = item == acc",
        "R(item, acc) = acc + item, trace(item)",
        "R(item, acc) = acc",
        "R(item, acc) = { Twice = item * 2\n acc + Twice }",
        "R(item, acc) = acc + Free",
    ];

    /// <summary>Reducers the streamed route must leave to the general one.</summary>
    public static readonly string[] OtherReducers =
    [
        "R(item, acc) = item",
        "R(item, acc) = Id(item) + acc",
        "R(item, acc) = item * 2 + acc",
        "R(item, acc) = trace(item) + acc",
        "R(item, acc) = 'x' == acc",
        "R(item, acc) = if(item == 2, 0, item + acc)",
        "R(item, acc) = true and acc",
        "R(item, (a, b)) = a + item",
        "R(item, *acc) = acc",
        "R(item, 0) = item\nR(item, acc) = acc + item",
        "R(acc, acc) = acc",
        "R(item, acc) = [acc, item]",
        "R(item, acc) = acc*",
    ];

    public static readonly string[] Folds =
    [
        "reduce([1, 2, 3], R, 0)",
        "reduce([1], R, 5)",
        "reduce([3, 2, 1], R, trace(100))",
        "reduce([trace(1), trace(2), trace(3)], R, tock())",
        "reduce([1, 2, 3], R, 1 / 0)",
        "reduce([1, 2, 3], R, ())",
        "reduce([1, 2, 3], R, [7])",
        "reduce([1, 2, 3], R, Inc)",
        "reduce([(1, 2), [3]], R, 0)",
        "reduce([1, 2, 3], R, Start)",
        "[1, 2, 3].reduce(R, 0), tock()",
    ];

    private const string Prelude = "Id(x) = x\nInc(x) = x + 1\nFree = 7\nStart = trace(40)\n";

    public static TheoryData<string, string> LeadingPrograms()
    {
        var data = new TheoryData<string, string>();
        foreach (var reducer in LeadingReducers)
            foreach (var fold in Folds)
                data.Add(reducer, fold);
        return data;
    }

    [Theory]
    [MemberData(nameof(LeadingPrograms))]
    public async Task StreamedFold_AgreesWithTheGeneralRoute_OnEveryRoute(string reducer, string fold)
    {
        var source = Prelude + reducer + "\n" + fold;
        var streamed = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(streamed.Kind is "ok" or "err", $"{streamed}\nsource:\n{source}");

        SixRouteAgreement.Observation general;
        using (ReduceFoldTestSeam.Activate())
            general = await SixRouteAgreement.OnEveryRouteAsync(source);

        Assert.True(general.AgreesWith(streamed), $"general {general}\nstreamed {streamed}\nsource:\n{source}");
    }

    [Theory]
    [MemberData(nameof(LeadingPrograms))]
    public void StreamedFold_ChargesWhatTheGeneralRouteCharges(string reducer, string fold)
    {
        // Host operations are not needed to compare charges; programs that name them are covered above.
        if (reducer.Contains("trace", StringComparison.Ordinal) || reducer.Contains("tock", StringComparison.Ordinal)
            || fold.Contains("trace", StringComparison.Ordinal) || fold.Contains("tock", StringComparison.Ordinal)
            || fold.Contains("Start", StringComparison.Ordinal))
        {
            return;
        }

        var source = "Id(x) = x\nInc(x) = x + 1\nFree = 7\n" + reducer + "\n" + fold;
        foreach (var optimized in new[] { false, true })
        {
            var streamed = Counters(source, optimized, general: false);
            var general = Counters(source, optimized, general: true);
            Assert.Equal(general.Outcome, streamed.Outcome);
            Assert.Equal(general.Steps, streamed.Steps);
            Assert.Equal(general.Checkpoints, streamed.Checkpoints);
            Assert.Equal(general.PeakDepth, streamed.PeakDepth);
            Assert.Equal(general.MaterializedItems, streamed.MaterializedItems);
        }
    }

    [Theory]
    [InlineData("R(item, acc) = acc + trace(item)", "reduce([1, 2, 3], R, trace(0))")]
    [InlineData("R(item, acc) = acc + tock() * item", "reduce([1, 2, 3], R, tock())")]
    [InlineData("R(item, acc) = acc + 10 / (item - 2)", "reduce([1, 2, 3], R, trace(0))")]
    [InlineData("R(item, acc) = { Twice = trace(item) * 2\n acc + Twice }", "reduce([1, 2, 3], R, 0), tock()")]
    public async Task StreamedFold_AgreesWithTheGeneralRoute_UnderEveryStepLimit(string reducer, string fold)
    {
        var source = Prelude + reducer + "\n" + fold;
        var unlimited = Counters(Unhosted(source), optimized: true, general: true);
        for (var limit = 1L; limit <= unlimited.Steps + 1; limit++)
        {
            var limits = new EvaluationLimits { MaxSteps = limit };
            var streamed = await SixRouteAgreement.OnEveryRouteAsync(source, limits: limits);
            SixRouteAgreement.Observation general;
            using (ReduceFoldTestSeam.Activate())
                general = await SixRouteAgreement.OnEveryRouteAsync(source, limits: limits);
            Assert.True(general.AgreesWith(streamed), $"limit {limit}: general {general}\nstreamed {streamed}\nsource:\n{source}");
        }
    }

    [Fact]
    public async Task StringConstructionBeforeAccumulator_RefusesBeforeInitialEffect()
    {
        const string source = "R(item, acc) = 'x' == acc\nreduce([1, 2], R, tock())";
        var limits = new EvaluationLimits { MaxMaterializedStringChars = 1 };
        var actual = await SixRouteAgreement.OnEveryRouteAsync(source, limits: limits);
        Assert.Equal("err", actual.Kind);
        Assert.StartsWith("StringMaterializationLimitExceeded:", Assert.Single(actual.Errors));
        Assert.Empty(actual.HostCalls);
    }

    [Fact]
    public void LeadingReducers_AreStreamed_AndHoldNoStepSuspended()
    {
        foreach (var reducer in LeadingReducers)
        {
            if (reducer.Contains("trace", StringComparison.Ordinal) || reducer.Contains("tock", StringComparison.Ordinal))
                continue;

            var source = "Id(x) = x\nInc(x) = x + 1\nFree = 7\n" + reducer + "\nreduce(range(1, 40), R, 0)";
            var (_, streamed) = Run(source, optimized: true, general: false);
            var (_, general) = Run(source, optimized: true, general: true);
            // Streamed: only the start is ever demanded as an accumulator. General: one suspended step each.
            Assert.True(streamed.PeakFoldContinuations <= 1, $"{reducer}: {streamed.PeakFoldContinuations}");
            Assert.Equal(40, general.PeakFoldContinuations);
        }
    }

    [Fact]
    public void OtherReducers_TakeTheGeneralRoute()
    {
        foreach (var reducer in OtherReducers)
        {
            var source = "Id(x) = x\n" + reducer.Replace("trace(item)", "Id(item)", StringComparison.Ordinal) + "\nreduce([1, 2, 3], R, 0)";
            var streamed = Counters(source, optimized: true, general: false);
            var general = Counters(source, optimized: true, general: true);
            // The same route with or without the seam: nothing differs, the fold's own observations included.
            Assert.Equal(general, streamed);
        }
    }

    [Fact]
    public void LongAccumulatorLedFold_StaysOnTheCallingThread_AtTheDepthOfOneStep()
    {
        const int count = 50_000;
        var source = $"Sum(item, acc) = acc + item\nreduce(range(1, {count}), Sum, 0)";
        var (two, twoBudget) = Run("Sum(item, acc) = acc + item\nreduce(range(1, 2), Sum, 0)", optimized: true, general: false);
        Assert.True(two.IsOk);

        var thread = Environment.CurrentManagedThreadId;
        var allocatedBefore = GC.GetAllocatedBytesForCurrentThread();
        var (result, budget) = Run(source, optimized: true, general: false);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - allocatedBefore;

        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
        Assert.Equal(((long)count * (count + 1) / 2).ToString(), SixRouteAgreement.Neutral(result.Value.Value));
        Assert.Equal(thread, Environment.CurrentManagedThreadId);
        Assert.True(budget.PeakFoldContinuations <= 1);
        Assert.Equal(twoBudget.PeakDepth, budget.PeakDepth);
        // Every step's allocations are this thread's: a coarse bound, a few kilobytes a step.
        Assert.InRange(allocated, count * 100L, count * 8_000L);
    }

    // ── Harness ───────────────────────────────────────────────────────────────────────────────────────

    private sealed record FoldCounters(string Outcome, long Steps, long Checkpoints, int PeakDepth, long MaterializedItems, int PeakFoldContinuations);

    private static string Unhosted(string source)
        => source.Replace("trace(", "Id(", StringComparison.Ordinal).Replace("tock()", "tick()", StringComparison.Ordinal);

    private static (EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget) Run(string source, bool optimized, bool general)
    {
        var parsed = SourceProvenance.ParseValid(source);
        using var seam = general ? ReduceFoldTestSeam.Activate() : null;
        return Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), enableOptimizations: optimized);
    }

    private static FoldCounters Counters(string source, bool optimized, bool general)
    {
        var (result, budget) = Run(source, optimized, general);
        var outcome = result.IsError
            ? "err " + KatLangError.FromEvalError(result.Error).Code + ": " + KatLangError.FromEvalError(result.Error).Message
            : "ok " + SixRouteAgreement.Neutral(result.Value.Value) + " n=" + result.Value.EmittedCount;
        return new FoldCounters(outcome, budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth,
            budget.MaterializedItems, budget.PeakFoldContinuations);
    }
}
