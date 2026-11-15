using System.Collections;
using System.Reflection;
using System.Text;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using KatLang.TestInfrastructure;
using KatLang.Tests.AsyncEvaluation;
using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests;

/// <summary>
/// STATISTICS OPT-OUT of the synchronous run-scoped zero-argument property cache (implementation-only,
/// no Lean counterpart). <see cref="RunScopedZeroArgPropertyResultCache"/> keeps its snapshot statistics
/// only when constructed with them (the default, for the tests and harnesses that read them); every
/// cache the library constructs passes <c>collectStatistics: false</c>, because nothing a run computes
/// reads a snapshot. The flag must decide only that bookkeeping: the same keys hit, the same misses run,
/// the same entries are published and every value, charge, diagnostic and limit verdict is unchanged.
/// </summary>
public sealed class ZeroArgPropertyCacheStatisticsOptOutTests
{
    private const long Seed = 11;

    // ── The flag ────────────────────────────────────────────────────────────────────────

    [Fact]
    public void WithoutStatistics_TheCacheServesHitsMissesReentryAndInvocationsExactlyAsWithThem()
    {
        var environment = new object();
        var with = Exercise(new RunScopedZeroArgPropertyResultCache(), environment);
        var without = Exercise(new RunScopedZeroArgPropertyResultCache(collectStatistics: false), environment);

        Assert.Equal(with, without);
        // 10 reads (4 hits, 6 misses including the re-entrant one) and 3 invocations: 9 bodies ran.
        Assert.Equal(
            "1 1 err err 2 [r3- 4 4] 5 5 6 1 7 published=4 active=0 obtains=True,True evaluations=9",
            with);
        GC.KeepAlive(environment);
    }

    [Fact]
    public void WithoutStatistics_TheCacheRefusesASnapshot_AndHoldsNoStatisticsPartitions()
    {
        // The local-only key's binding-context identity stays reachable, so its partitions stay live.
        var environment = new object();
        var cache = new RunScopedZeroArgPropertyResultCache(collectStatistics: false);
        Assert.False(cache.CollectsStatistics);
        Exercise(cache, environment);

        var refusal = Assert.Throws<InvalidOperationException>(() => cache.GetSnapshot());
        Assert.Contains("collectStatistics: false", refusal.Message, StringComparison.Ordinal);
        Assert.Equal((1, 0, 0), cache.LivePartitionCounts());

        // The default keeps the statistics the existing suites read, counted as before.
        var withStatistics = new RunScopedZeroArgPropertyResultCache();
        Assert.True(withStatistics.CollectsStatistics);
        Exercise(withStatistics, environment);
        var snapshot = withStatistics.GetSnapshot();
        Assert.Equal(10, snapshot.TotalRequests);
        Assert.Equal(4, snapshot.Hits);
        Assert.Equal(6, snapshot.Misses);
        Assert.Equal(4, snapshot.Stores);
        Assert.Equal(5, snapshot.DistinctKeysCreated);
        // The second failing read, and the re-entrant read while its owner was missing.
        Assert.Equal(2, snapshot.RepeatedMissRequests);
        Assert.Equal(4, snapshot.MaxCacheSize);
        Assert.Equal(1, snapshot.GetAccessKind(ZeroArgPropertyAccessKind.Invocation).Stores);
        Assert.Equal(1, withStatistics.LivePartitionCounts().Published);
        GC.KeepAlive(environment);
    }

    /// <summary>
    /// One fixed script over the cache's contract, rendered as text: a local-only key (partitioned by
    /// <paramref name="environment"/>) and exported keys; a miss that publishes and its hit; a failing
    /// key, missed twice and never stored; a re-entrant read inside its owner (evaluated, never
    /// published, and no published value while the owner runs) followed by a hit of the owner's entry;
    /// an invocation that establishes an empty entry, a read that hits it and invocations that run
    /// past established entries; and the publication-provenance answers afterwards.
    /// </summary>
    private static string Exercise(RunScopedZeroArgPropertyResultCache cache, object environment)
    {
        var run = new object();
        var text = new StringBuilder();
        var evaluations = 0;

        var local = Execution(NewProperty("Local", PropertyExposure.LocalOnlyCapturedAncestorParameters), environment, run);
        var exported = Execution(NewProperty("Exported", PropertyExposure.Exported), new object(), run);
        var failing = Execution(NewProperty("Failing", PropertyExposure.Exported), new object(), run);
        var reentrant = Execution(NewProperty("Reentrant", PropertyExposure.Exported), new object(), run);
        var invoked = Execution(NewProperty("Invoked", PropertyExposure.Exported), new object(), run);

        Append(cache.GetOrEvaluate(local, () => Value(1)));
        Append(cache.GetOrEvaluate(local, () => Value(99)));
        Append(cache.GetOrEvaluate(failing, Failure));
        Append(cache.GetOrEvaluate(failing, Failure));
        Append(cache.GetOrEvaluate(exported, () => Value(2)));
        text.Append('[');
        Append(cache.GetOrEvaluate(reentrant, () =>
        {
            evaluations++;
            var obtainedWhileRunning = cache.ReadObtainsPublishedValue(ZeroArgPropertyCacheKey.FromExecution(reentrant));
            // Re-entry: evaluated and returned, never published (Q-37).
            var inner = cache.GetOrEvaluate(reentrant, () => Value(3));
            text.Append('r').Append(Render(inner)).Append(obtainedWhileRunning ? '+' : '-').Append(' ');
            return EvalResult<ZeroArgPropertyResult>.Ok(new ZeroArgPropertyResult(new Result.Atom(4m), 1));
        }));
        Append(cache.GetOrEvaluate(reentrant, () => Value(98)));
        text.Length--;
        text.Append("] ");
        // An invocation on an empty entry runs and publishes it, a read then hits that entry, and a
        // later invocation runs past it without replacing it.
        Append(cache.Invoke(invoked, () => Value(5)));
        Append(cache.GetOrEvaluate(invoked, () => Value(97)));
        Append(cache.Invoke(invoked, () => Value(6)));
        Append(cache.GetOrEvaluate(local, () => Value(96)));
        Append(cache.Invoke(local, () => Value(7)));

        text.Append("published=").Append(cache.PublishedCount)
            .Append(" active=").Append(cache.ActiveOwnerCount)
            .Append(" obtains=").Append(cache.ReadObtainsPublishedValue(ZeroArgPropertyCacheKey.FromExecution(local)))
            .Append(',').Append(cache.ReadObtainsPublishedValue(ZeroArgPropertyCacheKey.FromExecution(failing)))
            .Append(" evaluations=").Append(evaluations);
        return text.ToString();

        EvalResult<ZeroArgPropertyResult> Value(int value)
        {
            evaluations++;
            return EvalResult<ZeroArgPropertyResult>.Ok(new ZeroArgPropertyResult(new Result.Atom(value), 1));
        }

        EvalResult<ZeroArgPropertyResult> Failure()
        {
            evaluations++;
            return new EvalError.UnknownName("missing");
        }

        void Append(EvalResult<ZeroArgPropertyResult> result) => text.Append(Render(result)).Append(' ');
    }

    private static string Render(EvalResult<ZeroArgPropertyResult> result)
        => result.IsError ? "err" : SemanticExplorerHarness.Neutral(result.Value.Value);

    private static ZeroArgPropertyExecution Execution(Property binding, object environment, object run)
        => new(NewAlgorithm() with { Properties = [binding] }, binding, ZeroArgPropertyAccessKind.CountedLexical, environment, run);

    private static Algorithm.User NewAlgorithm()
        => new(Parent: null, ParameterPatterns: [], Opens: [], Properties: [], Output: [new Expr.Num(0)]);

    private static Property NewProperty(string name, PropertyExposure exposure)
        => new(name, NewAlgorithm(), IsPublic: true, Exposure: exposure);

    // ── Corpus differential ─────────────────────────────────────────────────────────────

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

    /// <summary>
    /// Every program of the language-spec (with its probes) and semantic-explorer corpora runs on the
    /// optimized and the generic synchronous evaluator twice, through a cache with statistics and one
    /// without, each behind a counting wrapper. The two runs must agree on the outcome, every
    /// operational budget counter, the optimizers' and observations' counters, the cache's reads,
    /// executed misses, invocations, publication-provenance answers and published entries; the
    /// statistics of the first run must count exactly the reads and misses the wrapper saw.
    /// </summary>
    [Fact]
    public void Corpora_StatisticsOff_ChangesNoValueChargeHitMissOrPublication_OnEitherSynchronousRoute()
    {
        var mismatches = new List<string>();
        var statisticsDisagreements = new List<string>();
        var compared = 0;
        long hits = 0, invocations = 0, provenanceQueries = 0;

        foreach (var (id, source) in CorpusSources)
        {
            var parsed = Parser.Parse(source);
            if (parsed.HasErrors)
                continue;
            compared++;

            foreach (var optimized in new[] { true, false })
            {
                var with = Execute(parsed.Root, optimized, collectStatistics: true);
                var without = Execute(parsed.Root, optimized, collectStatistics: false);
                if (with.Trace != without.Trace)
                    mismatches.Add($"{id} [{(optimized ? "optimized" : "generic")}]\n  with:    {with.Trace}\n  without: {without.Trace}");

                var snapshot = with.Cache.Inner.GetSnapshot();
                if (snapshot.TotalRequests != with.Cache.Reads || snapshot.Misses != with.Cache.ReadEvaluations
                    || snapshot.Hits != with.Cache.Reads - with.Cache.ReadEvaluations)
                {
                    statisticsDisagreements.Add(
                        $"{id}: statistics requests={snapshot.TotalRequests} hits={snapshot.Hits} misses={snapshot.Misses}"
                        + $" / wrapper reads={with.Cache.Reads} evaluations={with.Cache.ReadEvaluations}");
                }

                if (optimized)
                {
                    hits += with.Cache.Reads - with.Cache.ReadEvaluations;
                    invocations += with.Cache.Invocations;
                    provenanceQueries += with.Cache.ProvenanceQueries;
                }
            }
        }

        Assert.True(compared > 1000, $"only {compared} corpus programs parsed");
        Assert.True(hits > 100, $"only {hits} cache hits across the corpora");
        Assert.True(invocations > 0, "no corpus program made a qualifying explicit zero-supply invocation");
        Assert.True(provenanceQueries > 0, "no corpus program asked for publication provenance (deconstruction sharing)");
        Assert.True(mismatches.Count == 0, $"{mismatches.Count} of {compared} programs changed without statistics:\n" + string.Join("\n", mismatches.Take(10)));
        Assert.True(statisticsDisagreements.Count == 0, string.Join("\n", statisticsDisagreements.Take(10)));
    }

    private sealed record RunTrace(string Trace, CountingCache Cache);

    private static RunTrace Execute(Algorithm.User root, bool optimized, bool collectStatistics)
    {
        var cache = new CountingCache(new RunScopedZeroArgPropertyResultCache(collectStatistics: collectStatistics));
        var loops = new LoopOptimizationDiagnostics();
        var sequences = new SequencePipelineDiagnostics();
        var observations = new EvaluationObservations { StructuralTraversal = new ValueTraversalObservations() };
        var (result, budget) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(root),
            enableOptimizations: optimized,
            zeroArgPropertyResultCache: cache,
            loopDiagnostics: loops,
            sequenceDiagnostics: sequences,
            observations: observations,
            randomSeed: Seed);

        var outcome = result.IsError
            ? "err " + SemanticExplorerHarness.ErrorCategory(result.Error) + " " + result.Error.GetType().Name
            : $"ok {SemanticExplorerHarness.Neutral(result.Value.Value)} n={result.Value.EmittedCount}";
        var trace = string.Join(" | ",
            outcome,
            $"steps={budget.ConsumedSteps} checkpoints={budget.ConsumedExpressionCheckpoints} peakDepth={budget.PeakDepth}"
                + $" items={budget.MaterializedItems} chars={budget.MaterializedStringChars} transient={budget.PeakTransientExpansion}"
                + $" structural={budget.ConsumedStructuralWorkUnits} retries={budget.ResolutionRetries} nextRandom={budget.RandomSource.NextUInt64()}",
            "loops " + Counters(loops),
            "sequences " + Counters(sequences),
            "observations " + Counters(observations),
            "traversal " + Counters(observations.StructuralTraversal!),
            $"cache reads={cache.Reads} evaluations={cache.ReadEvaluations} invocations={cache.Invocations}"
                + $" invocationEvaluations={cache.InvocationEvaluations} provenance={cache.ProvenanceQueries}/{cache.ProvenanceObtained}"
                + $" published={cache.Inner.PublishedCount} active={cache.Inner.ActiveOwnerCount}");
        return new RunTrace(trace, cache);
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

    /// <summary>
    /// Forwards every member to a run-scoped cache and counts what the evaluator asked of it: reads, the
    /// read misses whose body actually ran, invocations and their executions, and publication-provenance
    /// queries with their positive answers.
    /// </summary>
    private sealed class CountingCache(RunScopedZeroArgPropertyResultCache inner) : IZeroArgPropertyResultCache
    {
        internal RunScopedZeroArgPropertyResultCache Inner => inner;

        internal long Reads { get; private set; }

        internal long ReadEvaluations { get; private set; }

        internal long Invocations { get; private set; }

        internal long InvocationEvaluations { get; private set; }

        internal long ProvenanceQueries { get; private set; }

        internal long ProvenanceObtained { get; private set; }

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            Reads++;
            return inner.GetOrEvaluate(execution, () =>
            {
                ReadEvaluations++;
                return evaluate();
            });
        }

        public EvalResult<ZeroArgPropertyResult> Invoke(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            Invocations++;
            return inner.Invoke(execution, () =>
            {
                InvocationEvaluations++;
                return evaluate();
            });
        }

        public bool ReadObtainsPublishedValue(ZeroArgPropertyCacheKey key)
        {
            ProvenanceQueries++;
            var obtained = inner.ReadObtainsPublishedValue(key);
            if (obtained)
                ProvenanceObtained++;
            return obtained;
        }
    }

    // ── Production entries ──────────────────────────────────────────────────────────────

    public static TheoryData<string> HostOperationEntries => new()
    {
        "KatLangEngine.Run",
        "KatLangEngine.RunAsync",
        "Evaluator.Run",
        "Evaluator.RunAsync",
    };

    /// <summary>
    /// The public entries that accept synchronous host operations run with a statistics-free cache: an
    /// internal META receiver (<see cref="InvocationPlanTestSeam"/>) reads the cache of the context that
    /// calls it. The value shows the property read was cached as usual.
    /// </summary>
    [Theory]
    [MemberData(nameof(HostOperationEntries))]
    public async Task PublicEntries_RunWithAStatisticsFreeRunScopedCache(string entry)
    {
        const string source = "V = Grab(1)\nV + V";
        var caches = new List<IZeroArgPropertyResultCache>();
        var operations = HostOperations.Create(
            HostOperation.Create("Grab", (_, _) => throw new InvalidOperationException("the META receiver seam must intercept Grab"), "x"));
        var seam = new InvocationPlanTestSeam(new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>
        {
            ["Grab"] = cells =>
            {
                caches.Add(Assert.IsAssignableFrom<Evaluator.ExpressionSuspension>(cells[0]!.Suspension).Caller.ZeroArgPropertyResultCache);
                return new Result.Atom(7);
            },
        });
        var options = new RunOptions { HostOperations = operations };
        var parsed = Parser.Parse(source, options);
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));
        var program = new Expr.AlgorithmExpr(parsed.Root);

        string value;
        using (InvocationPlanTestSeam.Activate(seam))
        {
            value = entry switch
            {
                "KatLangEngine.Run" => NeutralOf(KatLangEngine.Run(source, options)),
                "KatLangEngine.RunAsync" => NeutralOf(await KatLangEngine.RunAsync(source, options)),
                "Evaluator.Run" => AsyncEvaluationHarness.NeutralOf(
                    Evaluator.Run(program, operations, limits: null, randomSeed: null, CancellationToken.None)),
                "Evaluator.RunAsync" => AsyncEvaluationHarness.NeutralOf(
                    await Evaluator.RunAsync(program, operations, limits: null, randomSeed: null, CancellationToken.None)),
                _ => throw new ArgumentOutOfRangeException(nameof(entry)),
            };
        }

        Assert.Equal("ok raw=" + SemanticExplorerHarness.Neutral(new Result.Atom(14)), value);
        var cache = Assert.IsType<RunScopedZeroArgPropertyResultCache>(Assert.Single(caches));
        Assert.False(cache.CollectsStatistics);
        Assert.True(cache.PublishedCount >= 1, $"published {cache.PublishedCount}");

        static string NeutralOf(RunResult run)
            => "ok raw=" + SemanticExplorerHarness.Neutral(Assert.IsType<RunResult.Success>(run).Value);
    }

    [Fact]
    public void TheCachePairingFactory_BuildsAStatisticsFreeSynchronousCache()
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid("V = 1\nV + V").Root);
        var cache = Assert.IsType<RunScopedZeroArgPropertyResultCache>(
            Evaluator.CreateRunScopedZeroArgPropertyResultCache(program, hostOperations: null));
        Assert.False(cache.CollectsStatistics);
    }

    /// <summary>
    /// SOURCE GUARD: every <see cref="RunScopedZeroArgPropertyResultCache"/> the library constructs passes
    /// <c>collectStatistics: false</c> — the public evaluator entries, the engine, the internal harness
    /// entries and the cache-pairing factory. A cache a test or harness constructs to read statistics
    /// keeps the default; the library never reads a snapshot.
    /// </summary>
    [Fact]
    public void EveryCacheTheLibraryConstructs_DisablesStatistics()
    {
        const string construction = "new RunScopedZeroArgPropertyResultCache(";
        var libraryRoot = Path.Combine(RepoRoot.Find(), "src", "KatLang");
        var sites = new List<string>();
        var offenders = new List<string>();
        foreach (var file in Directory.EnumerateFiles(libraryRoot, "*.cs", SearchOption.AllDirectories))
        {
            var relative = Path.GetRelativePath(libraryRoot, file).Replace('\\', '/');
            if (relative.StartsWith("bin/", StringComparison.Ordinal) || relative.StartsWith("obj/", StringComparison.Ordinal))
                continue;

            var text = File.ReadAllText(file);
            for (var index = text.IndexOf(construction, StringComparison.Ordinal);
                 index >= 0;
                 index = text.IndexOf(construction, index + construction.Length, StringComparison.Ordinal))
            {
                var arguments = ArgumentList(text, index + construction.Length);
                var line = 1 + text.AsSpan(0, index).Count('\n');
                var site = $"{relative}:{line} ({arguments})";
                sites.Add(site);
                if (!arguments.Contains("collectStatistics: false", StringComparison.Ordinal))
                    offenders.Add(site);
            }
        }

        foreach (var owner in new[] { "Evaluator.cs:", "Evaluator.Async.cs:", "KatLangEngine.cs:" })
            Assert.Contains(sites, site => site.StartsWith(owner, StringComparison.Ordinal));
        Assert.True(offenders.Count == 0, "library caches constructed with statistics:\n" + string.Join("\n", offenders));
    }

    /// <summary>The text of a call's argument list from just after its opening parenthesis to the matching close.</summary>
    private static string ArgumentList(string text, int start)
    {
        var depth = 1;
        for (var index = start; index < text.Length; index++)
        {
            depth += text[index] switch { '(' => 1, ')' => -1, _ => 0 };
            if (depth == 0)
                return text[start..index];
        }

        throw new InvalidOperationException("unbalanced construction at offset " + start);
    }
}
