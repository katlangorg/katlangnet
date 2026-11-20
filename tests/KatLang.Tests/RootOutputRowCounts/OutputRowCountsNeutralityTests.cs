using System.Collections;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Text;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using KatLang.Tests.RootPropertyObservations;
using Xunit.Abstractions;

namespace KatLang.Tests.RootOutputRowCounts;

/// <summary>
/// THE RECORDER-NEUTRALITY DIFFERENTIAL: attaching the root output-row recorder must change
/// nothing about a run but the presence of the counts. Every program of both differential corpora
/// runs twice per route — recorder off, recorder on — on the optimized and generic synchronous
/// evaluators and the forced async twin, with one random seed, and the two runs must agree on the
/// outcome (value, emitted count, error category), every operational budget counter, the
/// optimizers' diagnostics, the cache's own statistics, the structural-traversal counters, and the
/// position of the run's random stream. Targeted programs pin host-effect logs and seeded draws,
/// also across real suspension. The recorder's claim rule is pinned directly. For the bodies that
/// are not the root's, the same recorder-on against recorder-off comparison is made on allocation:
/// attaching the recorder adds no allocation to them, and the row loop's frame holds no recorder
/// state for them.
/// <para><b>What the comparison is.</b> Every test here runs ONE implementation — this build —
/// with the recorder attached and detached. None of them measures this build against an earlier
/// release, so none is evidence about what the row loop cost before the recorder existed.</para>
/// </summary>
public class OutputRowCountsNeutralityTests(ITestOutputHelper output)
{
    private const long Seed = 11;

    private enum Route { Optimized, Generic, ForcedTwin }

    private sealed record RunTrace(string Outcome, string Operational, string? SlotCounts, long PlannedLoops, long Fusions);

    private static async Task<RunTrace> ExecuteAsync(Algorithm.User root, Route route, bool record, HostOperations? operations = null)
    {
        var recorder = record ? new RootOutputRowRecorder(root.Output) : null;
        var loops = new LoopOptimizationDiagnostics();
        var sequences = new SequencePipelineDiagnostics();
        var traversal = new ValueTraversalObservations();
        var observations = new EvaluationObservations { StructuralTraversal = traversal };
        var program = new Expr.AlgorithmExpr(root);

        EvalResult<Evaluator.CountedResult> result;
        EvaluationBudget budget;
        string cacheStatistics;
        if (route == Route.ForcedTwin)
        {
            (result, budget) = await Evaluator.RunCountedObservedAsync(
                program,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                loopDiagnostics: loops,
                sequenceDiagnostics: sequences,
                observations: observations,
                hostOperations: operations,
                randomSeed: Seed,
                rootOutputRows: recorder);
            cacheStatistics = "async";
        }
        else
        {
            var cache = new RunScopedZeroArgPropertyResultCache();
            (result, budget) = Evaluator.RunCountedObserved(
                program,
                enableOptimizations: route == Route.Optimized,
                zeroArgPropertyResultCache: cache,
                loopDiagnostics: loops,
                sequenceDiagnostics: sequences,
                observations: observations,
                hostOperations: operations,
                randomSeed: Seed,
                rootOutputRows: recorder);
            cacheStatistics = Counters(cache.GetSnapshot()) + " active=" + cache.ActiveOwnerCount;
        }

        // The harness detaches the recorder when the root evaluation returns.
        Assert.Null(budget.RootOutputRows);

        var outcome = result.IsError
            ? "err " + SemanticExplorerHarness.ErrorCategory(result.Error) + " " + result.Error.GetType().Name
            : $"ok {SemanticExplorerHarness.Neutral(result.Value.Value)} n={result.Value.EmittedCount}";
        var operational = string.Join(" | ",
            $"steps={budget.ConsumedSteps} checkpoints={budget.ConsumedExpressionCheckpoints} peakDepth={budget.PeakDepth}"
                + $" items={budget.MaterializedItems} chars={budget.MaterializedStringChars} transient={budget.PeakTransientExpansion}"
                + $" structural={budget.ConsumedStructuralWorkUnits} retries={budget.ResolutionRetries} nextRandom={budget.RandomSource.NextUInt64()}",
            "loops " + Counters(loops),
            "sequences " + Counters(sequences),
            "observations " + Counters(observations),
            "traversal " + Counters(traversal),
            "cache " + cacheStatistics);

        string? slotCounts = null;
        if (recorder is not null && !result.IsError)
            slotCounts = recorder.TakeSlotCounts() is { } counts ? string.Join(",", counts) : "<not recorded>";
        return new RunTrace(outcome, operational, slotCounts, loops.OptimizedLoopHits,
            sequences.FilterCountFusionHits + sequences.DirectRangeFusionHits);
    }

    /// <summary>Every public instance counter of a diagnostics object (numbers and string-keyed dictionaries), in name order.</summary>
    private static string Counters(object diagnostics)
    {
        var text = new StringBuilder();
        foreach (var property in diagnostics.GetType()
                     .GetProperties(BindingFlags.Instance | BindingFlags.Public)
                     .Where(static p => p.GetIndexParameters().Length == 0)
                     .OrderBy(static p => p.Name, StringComparer.Ordinal))
        {
            var value = property.GetValue(diagnostics);
            switch (value)
            {
                case int or long or bool:
                    text.Append(property.Name).Append('=').Append(value).Append(' ');
                    break;
                case IEnumerable<KeyValuePair<string, long>> reasons:
                    text.Append(property.Name).Append("={")
                        .AppendJoin(",", reasons.OrderBy(static r => r.Key, StringComparer.Ordinal).Select(static r => $"{r.Key}:{r.Value}"))
                        .Append("} ");
                    break;
                case IEnumerable sequence and not string:
                    text.Append(property.Name).Append("=[")
                        .AppendJoin(",", sequence.Cast<object?>().Select(static item => item?.ToString()))
                        .Append("] ");
                    break;
            }
        }

        return text.ToString();
    }

    [Fact]
    public async Task Corpora_AttachingTheRecorder_ChangesNothingButTheCounts_OnEveryEvaluatorRoute()
    {
        var mismatches = new List<string>();
        var unrecorded = new List<string>();
        var routeDisagreements = new List<string>();
        var compared = 0;
        var recorded = 0;
        long plannedLoopHits = 0, fusionHits = 0;

        foreach (var (id, source) in OutputRowCountsTestSupport.CorpusSources)
        {
            var parsed = Parser.Parse(source);
            if (parsed.HasErrors)
                continue;
            compared++;

            var traces = new Dictionary<Route, RunTrace>();
            foreach (var route in Enum.GetValues<Route>())
            {
                var off = await ExecuteAsync(parsed.Root, route, record: false);
                var on = await ExecuteAsync(parsed.Root, route, record: true);
                if (off.Outcome != on.Outcome || off.Operational != on.Operational)
                    mismatches.Add($"{id} [{route}]\n  off: {off.Outcome} :: {off.Operational}\n  on:  {on.Outcome} :: {on.Operational}");

                // A root program that succeeded was evaluated once by the row loop, which the
                // recorder claimed; its counts cover every root row.
                if (on.SlotCounts is { } counts)
                {
                    if (counts == "<not recorded>" || CountOf(counts) != parsed.Root.Output.Count)
                        unrecorded.Add($"{id} [{route}]: {counts} for {parsed.Root.Output.Count} root rows");
                    else if (route == Route.Optimized)
                        recorded++;
                }

                traces[route] = on;
                if (route == Route.Optimized)
                {
                    plannedLoopHits += on.PlannedLoops;
                    fusionHits += on.Fusions;
                }
            }

            // Completing routes agree on the counts. Failing routes may legitimately stop at
            // different points (host-stack resource limits).
            if (traces.Values.All(static t => t.Outcome.StartsWith("ok", StringComparison.Ordinal)))
            {
                foreach (var route in new[] { Route.Generic, Route.ForcedTwin })
                {
                    if (traces[route].SlotCounts != traces[Route.Optimized].SlotCounts)
                        routeDisagreements.Add($"{id} [{route}]: {traces[route].SlotCounts} against the optimized {traces[Route.Optimized].SlotCounts}");
                }
            }
        }

        Assert.True(compared > 1000, $"only {compared} corpus programs parsed");
        Assert.True(recorded > 300, $"only {recorded} programs recorded their root rows");
        Assert.True(plannedLoopHits > 0, "no corpus program ran a planned loop with the recorder attached");
        Assert.True(fusionHits > 0, "no corpus program ran a fused sequence pipeline with the recorder attached");
        Assert.True(mismatches.Count == 0, $"{mismatches.Count} of {compared} programs changed when recorded:\n" + string.Join("\n", mismatches.Take(10)));
        Assert.True(unrecorded.Count == 0, $"{unrecorded.Count} successful programs did not record every root row:\n" + string.Join("\n", unrecorded.Take(10)));
        Assert.True(routeDisagreements.Count == 0, $"{routeDisagreements.Count} completing programs disagree across routes:\n" + string.Join("\n", routeDisagreements.Take(10)));

        static int CountOf(string counts) => counts.Length == 0 ? 0 : counts.Split(',').Length;
    }

    public static TheoryData<string> EffectfulSources => new()
    {
        "A = if(tock() < 3, A + 1, 0)\nA, A",
        "A = tock()\nB = trace(A + 10)\nA() + B + A + A()",
        "R = randomInt(0, 1000)\nS = R + random()\nR, S, randomInt(0, 9)",
        "Step(s) = trace(s) + tock()\nX = Step(0).repeat(4)\nX, X",
        "Before = trace(1)\nBoom = trace(2) / 0\nAfter = trace(3)\nBefore + Boom + After",
        "x, y = trace(1), tock()\nZ = x + y\nZ, y, x",
    };

    [Theory]
    [MemberData(nameof(EffectfulSources))]
    public async Task HostEffects_AndSeededDraws_AreIdenticalWithAndWithoutTheRecorder(string source)
    {
        foreach (var route in Enum.GetValues<Route>())
        {
            // The forced twin runs suspending operations, so its rows are recorded across awaits.
            var suspending = route == Route.ForcedTwin;
            var offLog = new PropertyObservationTestSupport.TickLog();
            var onLog = new PropertyObservationTestSupport.TickLog();
            var parsed = Parser.Parse(source, new RunOptions { HostOperations = offLog.Operations(suspending) });
            Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics.Select(static d => d.Message)));

            var off = await ExecuteAsync(parsed.Root, route, record: false, offLog.Operations(suspending));
            var on = await ExecuteAsync(parsed.Root, route, record: true, onLog.Operations(suspending));

            Assert.Equal(off.Outcome, on.Outcome);
            Assert.Equal(off.Operational, on.Operational);
            Assert.Equal(offLog.Calls, onLog.Calls);
        }
    }

    // ── The recorder's claim rule ────────────────────────────────────────────

    private static OutputBundle Rows(int count)
        => OutputBundle.Create(Enumerable.Range(0, count).Select(static n => (Expr)new Expr.Num(n)).ToArray());

    [Fact]
    public void OnlyTheFirstMatchingInvocationCanRecord_EvenWhenNestedRowsAreShared()
    {
        var rows = Rows(4);
        var recorder = new RootOutputRowRecorder(rows);
        var budget = new EvaluationBudget(EvaluationLimits.Default) { RootOutputRows = recorder };

        Assert.Null(RootOutputRowRecorder.Claim(budget, Rows(4)));
        var root = RootOutputRowRecorder.Claim(budget, rows);
        Assert.Same(recorder, root);
        Assert.Null(budget.RootOutputRows);

        root!.RecordRow(0, 0);
        root.RecordRow(1, 2);
        Assert.Null(RootOutputRowRecorder.Claim(budget, rows));
        root.RecordRow(2, 3);
        root.RecordRow(3, 3);

        Assert.Equal(new[] { 0, 2, 1, 0 }, recorder.TakeSlotCounts());
        Assert.Null(recorder.TakeSlotCounts());
    }

    [Fact]
    public void MissingOrPartialRootOutputHasNoCompletedCounts()
    {
        var rows = Rows(3);
        var recorder = new RootOutputRowRecorder(rows);
        Assert.Null(recorder.TakeSlotCounts());

        var budget = new EvaluationBudget(EvaluationLimits.Default) { RootOutputRows = recorder };
        var root = RootOutputRowRecorder.Claim(budget, rows);
        Assert.Same(recorder, root);
        root!.RecordRow(0, 2);
        Assert.Null(recorder.TakeSlotCounts());

        budget.RootOutputRows = new RootOutputRowRecorder(OutputBundle.Empty);
        Assert.Null(RootOutputRowRecorder.Claim(budget, OutputBundle.Empty));
    }

    [Fact]
    public void NonEngineRuns_AttachNoRecorder()
    {
        var parsed = Parser.Parse("A = 1, 2\nV = 5\nA*\nV");
        Assert.False(parsed.HasErrors);

        var (result, budget) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root));

        Assert.True(result.IsOk);
        Assert.Null(budget.RootOutputRows);
    }

    // ── Bodies that are not the root's: recorder attached against detached, this build ──

    [Fact]
    public void NestedRowLoopTwin_CarriesOnlyTheOrdinaryRowSource()
    {
        var twin = typeof(Evaluator).GetMethod("EvalOutputRowsPreparedCoreAsync", BindingFlags.NonPublic | BindingFlags.Static);
        Assert.NotNull(twin);
        var machine = twin.GetCustomAttribute<AsyncStateMachineAttribute>()?.StateMachineType;
        Assert.NotNull(machine);

        // Close the compiler-generated state machine as it runs in a nested body. The one
        // reference inside OrdinaryOutputRows replaces the row-list reference the loop needs.
        var fields = machine.MakeGenericType(typeof(OrdinaryOutputRows))
            .GetFields(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic);
        Assert.Single(fields, static field => field.FieldType == typeof(OrdinaryOutputRows));
        Assert.DoesNotContain(fields, static field => field.FieldType == typeof(RootOutputRowRecorder));
        var sourceFields = typeof(OrdinaryOutputRows).GetFields(BindingFlags.Instance | BindingFlags.NonPublic | BindingFlags.Public);
        Assert.Equal(typeof(IReadOnlyList<Expr>), Assert.Single(sourceFields).FieldType);
    }

    /// <summary>
    /// RECORDER ATTACHED AGAINST DETACHED, ON THIS BUILD: the same program is evaluated by the same
    /// implementation with a root output-row recorder and without one, and the attached run may
    /// allocate at most the recorder's one counts array more. The measured difference is between
    /// those two runs only. It bounds what attaching the recorder costs the nested bodies; it does
    /// not compare this implementation with an earlier release, and so says nothing about whether
    /// the row loop itself allocates as it did before the recorder existed.
    /// </summary>
    [Fact]
    public void AttachingTheRecorder_AddsAtMostItsCountsArray_OverNestedBodies_OnTheSameBuild()
    {
        // 80 root rows, each a sum of 50 ordinary calls: 4,000 evaluations of F's body, every one
        // of them through the shared row loop (an ordinary call evaluates its bound body there),
        // none of them the root's. Both runs evaluate all of them; only the recorder differs.
        const int rootRows = 80;
        const int callsPerRow = 50;
        var source = new StringBuilder("F(x) = x + 1\n");
        for (var row = 0; row < rootRows; row++)
            source.AppendJoin(" + ", Enumerable.Range(0, callsPerRow).Select(call => $"F({row + call})")).Append('\n');
        var parsed = Parser.Parse(source.ToString());
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics.Select(static d => d.Message)));
        Assert.Equal(rootRows, parsed.Root.Output.Count);
        var program = new Expr.AlgorithmExpr(parsed.Root);

        long Measure(bool record)
        {
            // The recorder itself is made outside the window; its one array is made inside.
            var recorder = record ? new RootOutputRowRecorder(parsed.Root.Output) : null;
            var before = GC.GetAllocatedBytesForCurrentThread();
            var (result, _) = Evaluator.RunCountedObserved(program, enableOptimizations: false, rootOutputRows: recorder);
            var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
            Assert.True(result.IsOk);
            if (record)
                Assert.Equal(Enumerable.Repeat(1, rootRows), recorder!.TakeSlotCounts());
            return allocated;
        }

        // Warm both paths, then keep the smallest of several windows of each.
        Measure(record: false);
        Measure(record: true);
        long detached = long.MaxValue, attached = long.MaxValue;
        for (var i = 0; i < 7; i++)
        {
            detached = Math.Min(detached, Measure(record: false));
            attached = Math.Min(attached, Measure(record: true));
        }

        // The attached run may allocate its one counts array: an int[80] is 24 + 4 * 80 = 344
        // bytes. The in-process counter can add one allocation quantum (about 8 KB). A recorder
        // that cost any nested body even one smallest object (24 bytes) would add 4,000 * 24 =
        // 96,000 bytes to the attached run, far above the bound.
        const long countsArray = 24 + 4 * rootRows;
        const long counterQuantum = 8 * 1024;
        const long bound = countsArray + counterQuantum;
        var difference = attached - detached;
        var measured =
            $"recorder detached {detached} bytes, attached {attached} bytes, difference {difference} bytes "
            + $"(bound {bound}) over {rootRows * callsPerRow} nested bodies, both runs on this build";
        output.WriteLine(measured);
        Assert.True(difference <= bound,
            "attaching the root output-row recorder allocated more than its counts array allows: " + measured);
    }
}
