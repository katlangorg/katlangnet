using System.Collections;
using System.Reflection;
using System.Text;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using KatLang.Tests.LanguageSpec;
using static KatLang.Tests.RootPropertyObservations.PropertyObservationTestSupport;

namespace KatLang.Tests.RootPropertyObservations;

/// <summary>
/// THE OBSERVER-NEUTRALITY DIFFERENTIAL (IV-1, RUN-01/RUN-02): attaching the root-property
/// observation sink must change nothing about a run but the presence of the snapshot. Every
/// program of both differential corpora (the canonical language spec with its probes and the
/// semantic-explorer corpus) runs twice per route — sink off, sink on — on the optimized and
/// generic synchronous evaluators and the forced async twin, with one random seed, and the two
/// runs must agree on the outcome (value, emitted count, error category), every operational
/// budget counter, the optimizers' diagnostics (which path ran and why it fell back), the cache's
/// own statistics, the structural-traversal counters, and the position of the run's random stream.
/// The engine routes are compared the same way on outcome, and targeted programs pin host-effect
/// logs and seeded draws on the sync, async, and genuinely suspending engine routes. The
/// completed snapshots must agree across completing routes, and no root binding may publish twice.
/// </summary>
public class PropertyObservationNeutralityTests
{
    private const long Seed = 11;

    private static readonly IReadOnlyList<(string Id, string Source)> CorpusSources = BuildCorpusSources();

    private static IReadOnlyList<(string, string)> BuildCorpusSources()
    {
        var sources = new List<(string, string)>();
        foreach (var specCase in LanguageSpecCorpus.AllCases())
        {
            sources.Add(("spec:" + specCase.Id, specCase.Source));
            for (var i = 0; i < specCase.Probes.Count; i++)
                sources.Add(($"spec:{specCase.Id}#probe{i}", specCase.Probes[i].Probe));
        }

        foreach (var explorerCase in SemanticExplorerCorpus.AllCases())
            sources.Add(("explorer:" + explorerCase.Id, explorerCase.Source));
        return sources;
    }

    private enum Route { Optimized, Generic, ForcedTwin }

    private sealed record RunTrace(string Outcome, string Operational, string? Snapshot, int Duplicates);

    private static RunTrace Execute(Algorithm.User root, Route route, bool observe)
    {
        var sink = observe ? new RootPropertyObservationSink(root) : null;
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
            (result, budget) = Evaluator.RunCountedObservedAsync(
                program,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(sink),
                loopDiagnostics: loops,
                sequenceDiagnostics: sequences,
                observations: observations,
                randomSeed: Seed).AsTask().GetAwaiter().GetResult();
            cacheStatistics = "async";
        }
        else
        {
            var cache = new RunScopedZeroArgPropertyResultCache(sink);
            (result, budget) = Evaluator.RunCountedObserved(
                program,
                enableOptimizations: route == Route.Optimized,
                zeroArgPropertyResultCache: cache,
                loopDiagnostics: loops,
                sequenceDiagnostics: sequences,
                observations: observations,
                randomSeed: Seed);
            cacheStatistics = Counters(cache.GetSnapshot()) + " active=" + cache.ActiveOwnerCount;
        }

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

        return new RunTrace(outcome, operational, sink is null ? null : DescribeSnapshot(sink.Complete()), sink?.DuplicateBindingPublications ?? 0);
    }

    private static string DescribeSnapshot(PropertyObservations snapshot)
        => string.Join("; ", snapshot.Select(o => o.Status == PropertyValueStatus.Available
            ? $"{o.Name}@{o.DeclarationSpan}={SemanticExplorerHarness.Neutral(o.Value!)}#{o.EmittedCount}"
            : $"{o.Name}@{o.DeclarationSpan}=<withheld>#{o.EmittedCount}"));

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
    public void Corpora_AttachingTheSink_ChangesNothingButTheSnapshot_OnEveryEvaluatorRoute()
    {
        var mismatches = new List<string>();
        var routeDisagreements = new List<string>();
        var duplicates = new List<string>();
        var compared = 0;
        var nonEmptySnapshots = 0;
        long plannedLoopHits = 0, fusionHits = 0;

        foreach (var (id, source) in CorpusSources)
        {
            var parsed = Parser.Parse(source);
            if (parsed.HasErrors)
                continue;
            compared++;

            var snapshots = new Dictionary<Route, RunTrace>();
            foreach (var route in Enum.GetValues<Route>())
            {
                var off = Execute(parsed.Root, route, observe: false);
                var on = Execute(parsed.Root, route, observe: true);
                if (off.Outcome != on.Outcome || off.Operational != on.Operational)
                    mismatches.Add($"{id} [{route}]\n  off: {off.Outcome} :: {off.Operational}\n  on:  {on.Outcome} :: {on.Operational}");
                if (on.Duplicates != 0)
                    duplicates.Add($"{id} [{route}] {on.Duplicates}: {on.Snapshot}");
                snapshots[route] = on;
                if (route == Route.Optimized)
                {
                    plannedLoopHits += on.Operational.Contains("OptimizedLoopHits=0 ", StringComparison.Ordinal) ? 0 : 1;
                    fusionHits += on.Operational.Contains("FilterCountFusionHits=0 ", StringComparison.Ordinal)
                        && on.Operational.Contains("DirectRangeFusionHits=0 ", StringComparison.Ordinal) ? 0 : 1;
                }
            }

            if (!string.IsNullOrEmpty(snapshots[Route.Optimized].Snapshot))
                nonEmptySnapshots++;

            // Equivalent completing executions agree on the snapshot. Failing routes may
            // legitimately stop at different points (host-stack resource limits, RUN-01).
            if (snapshots.Values.All(static t => t.Outcome.StartsWith("ok", StringComparison.Ordinal)))
            {
                foreach (var route in new[] { Route.Generic, Route.ForcedTwin })
                {
                    if (snapshots[route].Snapshot != snapshots[Route.Optimized].Snapshot)
                        routeDisagreements.Add($"{id} [{route}]\n  optimized: {snapshots[Route.Optimized].Snapshot}\n  {route}: {snapshots[route].Snapshot}");
                }
            }
        }

        Assert.True(compared > 1000, $"only {compared} corpus programs parsed");
        Assert.True(nonEmptySnapshots > 200, $"only {nonEmptySnapshots} programs published a root property");
        Assert.True(plannedLoopHits > 0, "no corpus program ran a planned loop with the sink attached");
        Assert.True(fusionHits > 0, "no corpus program ran a fused sequence pipeline with the sink attached");
        Assert.True(mismatches.Count == 0, $"{mismatches.Count} of {compared} programs changed when observed:\n" + string.Join("\n", mismatches.Take(10)));
        Assert.True(duplicates.Count == 0, $"{duplicates.Count} programs published one root binding twice:\n" + string.Join("\n", duplicates.Take(10)));
        Assert.True(routeDisagreements.Count == 0, $"{routeDisagreements.Count} completing programs disagree across routes:\n" + string.Join("\n", routeDisagreements.Take(10)));
    }

    [Fact]
    public async Task Corpora_EngineOutcomes_AreIdenticalWithAndWithoutObservation()
    {
        var mismatches = new List<string>();
        foreach (var (id, source) in CorpusSources)
        {
            var off = KatLangEngine.Run(source, new RunOptions { RandomSeed = Seed });
            var on = KatLangEngine.Run(source, new RunOptions { RandomSeed = Seed, ObservePropertyValues = true });
            var onAsync = await KatLangEngine.RunAsync(source, new RunOptions { RandomSeed = Seed, ObservePropertyValues = true });

            if (Outcome(off) != Outcome(on) || Outcome(off) != Outcome(onAsync))
                mismatches.Add($"{id}: off {Outcome(off)} / on {Outcome(on)} / async {Outcome(onAsync)}");
            if (off.PropertyObservations is not null)
                mismatches.Add($"{id}: unobserved run carries a snapshot");
            if ((on.PropertyObservations is null) != on is RunResult.ParseFailure
                || (onAsync.PropertyObservations is null) != onAsync is RunResult.ParseFailure)
            {
                mismatches.Add($"{id}: null/empty contract broken for {on.GetType().Name}");
            }
        }

        Assert.True(mismatches.Count == 0, $"{mismatches.Count} programs differ:\n" + string.Join("\n", mismatches.Take(10)));
    }

    public static TheoryData<string> EffectfulSources => new()
    {
        "A = if(tick() < 3, A + 1, 0)\nA, A",
        "A = tick()\nB = trace(A + 10)\nA() + B + A + A()",
        "R = randomInt(0, 1000)\nS = R + random()\nR, S, randomInt(0, 9)",
        "Step(s) = trace(s) + tick()\nX = Step(0).repeat(4)\nX, X",
        "L = range(1, 20).map{trace(n)}.filter{n mod 2 == 0}\nC = L.count\nC + L.count",
        "Before = trace(1)\nBoom = trace(2) / 0\nAfter = trace(3)\nBefore + Boom + After",
        "x, y = trace(1), tick()\nZ = x + y\nZ, y, x",
    };

    [Theory]
    [MemberData(nameof(EffectfulSources))]
    public async Task HostEffects_AndSeededDraws_AreIdenticalWithAndWithoutObservation(string source)
    {
        foreach (var engine in new[] { "sync", "async", "suspending" })
        {
            var offLog = new TickLog();
            var onLog = new TickLog();
            AssertLegal(source, offLog.Operations());
            var off = await RunOn(engine, source, Options(observe: false, offLog.Operations(engine == "suspending"), Seed));
            var on = await RunOn(engine, source, Options(observe: true, onLog.Operations(engine == "suspending"), Seed));

            Assert.Equal(Outcome(off), Outcome(on));
            Assert.Equal(offLog.Calls, onLog.Calls);
            Assert.Null(off.PropertyObservations);
            Assert.NotNull(on.PropertyObservations);
        }

        static Task<RunResult> RunOn(string engine, string source, RunOptions options)
            => engine == "sync" ? Task.FromResult(KatLangEngine.Run(source, options)) : KatLangEngine.RunAsync(source, options);
    }
}
