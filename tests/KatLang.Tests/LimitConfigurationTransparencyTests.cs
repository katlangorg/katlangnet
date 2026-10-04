using KatLang.Evaluation;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.StrategyNeutralBudgetParityTests;

namespace KatLang.Tests;

/// <summary>
/// LIMITS OBSERVE A RUN; THEY NEVER CHOOSE HOW IT RUNS (Q-09b, decided 2026-10-04; PV-07).
/// Configuring, raising, or removing a limit that a run does not reach changes nothing about
/// that run — not its value, effects, random draws, budget accounting, the evaluation strategy
/// that runs, or whether it completes — and an explicitly written default is the same as no
/// configuration.
///
/// <para><b>The PV-07 defect this pins.</b> <c>Evaluator.CreateRootCtx</c> used to disable loop
/// planning whenever <see cref="EvaluationLimits.MaxSteps"/> was CONFIGURED (any value, even
/// <see cref="long.MaxValue"/>), and sequence fusion whenever <c>MaxSteps</c>,
/// <see cref="EvaluationLimits.MaxMaterializedItems"/>, <see cref="EvaluationLimits.MaxStringLength"/>
/// (even at its own default) or <see cref="EvaluationLimits.MaxMaterializedStringChars"/> was
/// written. The generic strategies need more host stack for loop-step and pipeline shapes, so on
/// one public entry point, one thread, one program, a non-binding limit turned success into
/// <see cref="EvalError.EvaluationStackExhausted"/>
/// (<c>R(n) = if(n &gt; 0, range(n, n).filter({ R(x - 1) &gt;= 0 }).count, 0)</c> / <c>R(35)</c>,
/// Release, 1.5 MiB). Every strategy now charges every budget identically
/// (<see cref="StrategyNeutralBudgetParityTests"/>), so no limit selects a strategy.</para>
///
/// <para>The comparisons here hold the route, the program, the seed and the host operations
/// fixed and vary ONLY the limit configuration. They do not compare routes or host conditions:
/// host-stack headroom is host policy (Q-09a) and may differ between the synchronous evaluator and
/// the async twin, builds, runtimes and JIT states.</para>
/// </summary>
public class LimitConfigurationTransparencyTests
{
    /// <summary>
    /// Every configuration that is non-binding for the corpus below: the empty object, each
    /// formerly strategy-selecting limit at a huge value, at <see cref="long.MaxValue"/> and at its
    /// written default, every always-active ceiling written at its own default, and all of them
    /// together. Index 0 is the unconfigured run.
    /// </summary>
    public static readonly IReadOnlyList<(string Name, EvaluationLimits? Limits)> NonBindingConfigurations =
    [
        ("default", null),
        ("empty", new EvaluationLimits()),
        ("steps-max", new EvaluationLimits { MaxSteps = long.MaxValue }),
        ("steps-1e12", new EvaluationLimits { MaxSteps = 1_000_000_000_000 }),
        ("steps-1e7", new EvaluationLimits { MaxSteps = 10_000_000 }),
        ("items-max", new EvaluationLimits { MaxMaterializedItems = long.MaxValue }),
        ("items-1e12", new EvaluationLimits { MaxMaterializedItems = 1_000_000_000_000 }),
        ("string-length-default", new EvaluationLimits { MaxStringLength = EvaluationLimits.MaxSupportedStringLength }),
        ("string-chars-max", new EvaluationLimits { MaxMaterializedStringChars = long.MaxValue }),
        ("string-chars-1e9", new EvaluationLimits { MaxMaterializedStringChars = 1_000_000_000 }),
        ("depth-ceiling", new EvaluationLimits { MaxDepth = EvaluationLimits.MaxSupportedDepth }),
        ("collection-ceiling", new EvaluationLimits { MaxCollectionItems = EvaluationLimits.MaxSupportedCollectionItems }),
        ("ast-ceiling", new EvaluationLimits { MaxAstDepth = EvaluationLimits.MaxSupportedAstDepth }),
        ("display-ceiling", new EvaluationLimits { MaxDisplayLength = EvaluationLimits.MaxSupportedDisplayLength }),
        ("all-four-selectors", new EvaluationLimits
        {
            MaxSteps = long.MaxValue,
            MaxMaterializedItems = long.MaxValue,
            MaxStringLength = EvaluationLimits.MaxSupportedStringLength,
            MaxMaterializedStringChars = long.MaxValue,
        }),
        ("every-limit-written", new EvaluationLimits
        {
            MaxSteps = 1_000_000_000_000,
            MaxMaterializedItems = 1_000_000_000_000,
            MaxStringLength = EvaluationLimits.MaxSupportedStringLength,
            MaxMaterializedStringChars = 1_000_000_000_000,
            MaxDepth = EvaluationLimits.MaxSupportedDepth,
            MaxCollectionItems = EvaluationLimits.MaxSupportedCollectionItems,
            MaxAstDepth = EvaluationLimits.MaxSupportedAstDepth,
            MaxDisplayLength = EvaluationLimits.MaxSupportedDisplayLength,
        }),
    ];

    public static TheoryData<string, string> CorpusTimesConfigurations()
    {
        var data = new TheoryData<string, string>();
        foreach (var (id, _, _) in Corpus)
        {
            foreach (var (name, _) in NonBindingConfigurations.Skip(1))
                data.Add(id, name);
        }

        return data;
    }

    private static EvaluationLimits? Configuration(string name)
        => NonBindingConfigurations.Single(entry => entry.Name == name).Limits;

    /// <summary>
    /// The strategy-identity and full-observation law on the optimizing route: a non-binding
    /// configuration yields the default run's outcome, error tree, every counter, host trace —
    /// AND the same strategy markers (planned-loop and fusion hits). The strategy markers are
    /// what kill a restored limit-to-strategy switch even where values agree.
    /// </summary>
    [Theory]
    [MemberData(nameof(CorpusTimesConfigurations))]
    public void NonBindingConfiguration_ChangesNothing_OnTheSameRoute(string caseId, string configuration)
    {
        var source = Corpus.Single(entry => entry.Id == caseId).Source;
        var unlimited = Observe(source, optimize: true, seed: 7);
        var configured = Observe(source, optimize: true, limits: Configuration(configuration), seed: 7);

        Assert.Equal(unlimited.Accounting, configured.Accounting);
        Assert.Equal(unlimited.LoopHits, configured.LoopHits);
        Assert.Equal(unlimited.FusionHits, configured.FusionHits);
    }

    /// <summary>
    /// The same law on the public engine entry point, with the result rendered as a host sees it.
    /// </summary>
    [Theory]
    [MemberData(nameof(CorpusTimesConfigurations))]
    public void NonBindingConfiguration_ChangesNothing_OnThePublicEngine(string caseId, string configuration)
    {
        var source = Corpus.Single(entry => entry.Id == caseId).Source;
        Assert.Equal(EngineOutcome(source, null), EngineOutcome(source, Configuration(configuration)));
    }

    internal static string EngineOutcome(string source, EvaluationLimits? limits, long? seed = 7)
    {
        var log = new HostLog();
        var operations = source.Contains("tick(", StringComparison.Ordinal) || source.Contains("trace(", StringComparison.Ordinal)
            ? Operations(log)
            : null;
        var result = KatLangEngine.Run(source, new RunOptions { EvaluationLimits = limits, HostOperations = operations, RandomSeed = seed });
        return $"{result.GetType().Name}: {result.ToDisplayString()} | host={string.Join(",", log.Calls)}";
    }

    /// <summary>
    /// The strategy decision itself, observed directly: under every non-binding configuration the
    /// optimizing route plans the loop AND fuses the pipeline of one program that offers both.
    /// Formerly <c>MaxSteps</c> disabled both, and the materialization and string limits disabled
    /// fusion.
    /// </summary>
    [Fact]
    public void EveryNonBindingConfiguration_KeepsLoopPlanningAndFusionEnabled()
    {
        const string source = "Step(s) = s + 1\nP(x) = x > 2\nrepeat(Step, 3, 0) + range(1, 5).filter(P).count";
        foreach (var (name, limits) in NonBindingConfigurations)
        {
            var observed = Observe(source, optimize: true, limits: limits);
            Assert.True(observed.LoopHits == 1, $"{name}: loop planning disabled");
            Assert.True(observed.FusionHits == 1, $"{name}: sequence fusion disabled");
            Assert.Equal("ok 6 n=1", observed.Outcome);
        }
    }

    /// <summary>
    /// Equivalent EFFECTIVE configurations are the same configuration: writing a limit's default
    /// (<see cref="long.MaxValue"/> for an unbudgeted cumulative limit, the ceiling for an
    /// always-active one) or an empty limits object is indistinguishable from configuring nothing —
    /// including for a run that FAILS on another limit and for the steps it charged on the way.
    /// </summary>
    [Theory]
    [InlineData("Step(s) = s + 1\nrepeat(Step, 5000, 0)")]
    [InlineData("range(1, 2000).filter({ x mod 7 == 0 }).count")]
    [InlineData("R(n) = if(n > 0, range(n, n).filter({ R(x - 1) >= 0 }).count, 0)\nR(20)")]
    [InlineData("Step(s, t) = s + 1, 10 / (s - 40)\nrepeat(Step, 80, 0, 0)")]
    public void ExplicitDefaults_AreTheUnconfiguredBudget(string source)
    {
        var equivalents = new (EvaluationLimits? Left, EvaluationLimits? Right)[]
        {
            (null, new EvaluationLimits()),
            (null, new EvaluationLimits { MaxSteps = long.MaxValue }),
            (null, new EvaluationLimits { MaxMaterializedItems = long.MaxValue }),
            (null, new EvaluationLimits { MaxStringLength = EvaluationLimits.MaxSupportedStringLength }),
            (null, new EvaluationLimits { MaxStringLength = int.MaxValue }),
            (null, new EvaluationLimits { MaxMaterializedStringChars = long.MaxValue }),
            (new EvaluationLimits { MaxDepth = 40 }, new EvaluationLimits { MaxDepth = 40, MaxSteps = long.MaxValue, MaxMaterializedItems = long.MaxValue }),
        };

        foreach (var (left, right) in equivalents)
        {
            foreach (var optimize in new[] { true, false })
            {
                var a = Observe(source, optimize, left);
                var b = Observe(source, optimize, right);
                Assert.Equal(a.Accounting, b.Accounting);
                Assert.Equal(a.LoopHits, b.LoopHits);
                Assert.Equal(a.FusionHits, b.FusionHits);
            }
        }
    }

    /// <summary>
    /// LIMIT INDEPENDENCE: when exactly one limit binds, the presence of other, non-binding limits
    /// does not move its failure point — same error tree, same counters at the failure, same
    /// effects — on either strategy.
    /// </summary>
    [Theory]
    [InlineData("Step(s) = s + 1\nG(a, b) = a + b\nG(trace(1) + repeat(Step, 400, 0), trace(2))", "steps", 120L)]
    [InlineData("range(1, 300).filter({ trace(x) mod 50 == 0 }).count", "steps", 100L)]
    [InlineData("A = range(1, 400).filter({ x > 3 }).count\nB = range(1, 400).filter({ x > 7 }).count\nA + B", "items", 1000L)]
    [InlineData("Step(s, t) = s + 1, if(s > 2, 'abcdef', 'xy')\nrepeat(Step, 40, 0, 'z')", "string-chars", 60L)]
    public void OneBindingLimit_IsUnaffectedByOtherNonBindingLimits(string source, string binding, long value)
    {
        EvaluationLimits Bind(EvaluationLimits limits) => binding switch
        {
            "steps" => limits with { MaxSteps = value },
            "items" => limits with { MaxMaterializedItems = value },
            "string-chars" => limits with { MaxMaterializedStringChars = value },
            _ => throw new ArgumentOutOfRangeException(nameof(binding)),
        };

        var others = new[]
        {
            new EvaluationLimits(),
            new EvaluationLimits { MaxSteps = long.MaxValue },
            new EvaluationLimits { MaxMaterializedItems = 1_000_000_000 },
            new EvaluationLimits { MaxStringLength = EvaluationLimits.MaxSupportedStringLength },
            new EvaluationLimits { MaxMaterializedStringChars = 1_000_000_000 },
            new EvaluationLimits
            {
                MaxSteps = long.MaxValue,
                MaxMaterializedItems = 1_000_000_000,
                MaxStringLength = EvaluationLimits.MaxSupportedStringLength,
                MaxMaterializedStringChars = 1_000_000_000,
            },
        };

        foreach (var optimize in new[] { true, false })
        {
            var alone = Observe(source, optimize, Bind(new EvaluationLimits()));
            Assert.StartsWith("err ", alone.Outcome);
            foreach (var other in others)
            {
                var combined = Observe(source, optimize, Bind(other));
                Assert.Equal(alone.Accounting, combined.Accounting);
                Assert.Equal(alone.LoopHits, combined.LoopHits);
                Assert.Equal(alone.FusionHits, combined.FusionHits);
            }
        }
    }

    /// <summary>
    /// A representative production host configuration (the shape an embedding validation service
    /// configures for untrusted source: a step budget, a cumulative item budget and both string
    /// budgets) keeps the normal optimized strategy for programs it does not stop — so it pays
    /// neither the generic strategy's speed and allocation nor its host-stack cost — while every
    /// configured limit still stops a program that reaches it.
    /// </summary>
    [Fact]
    public void RepresentativeHostConfiguration_KeepsTheOptimizedStrategy_AndEnforcesEveryLimit()
    {
        var host = new EvaluationLimits
        {
            MaxSteps = 200_000,
            MaxMaterializedItems = 200_000,
            MaxStringLength = 10_000,
            MaxMaterializedStringChars = 200_000,
        };

        foreach (var (id, source, exercises) in Corpus)
        {
            var unlimited = Observe(source, optimize: true, seed: 7);
            var hosted = Observe(source, optimize: true, limits: host, seed: 7);
            Assert.True(unlimited.Accounting == hosted.Accounting, $"{id}: the host configuration changed the run");
            Assert.Equal(unlimited.LoopHits, hosted.LoopHits);
            Assert.Equal(unlimited.FusionHits, hosted.FusionHits);
            if (exercises.HasFlag(Exercises.PlannedLoop))
                Assert.True(hosted.LoopHits > 0, $"{id}: planned loop not taken under the host configuration");
            if (exercises.HasFlag(Exercises.Fusion))
                Assert.True(hosted.FusionHits > 0, $"{id}: fusion not taken under the host configuration");
        }

        // Each configured limit still binds, on the optimized strategy.
        var runaway = Observe("Step(s) = s + 1, true\nwhile(Step, 0)", optimize: true, limits: host);
        Assert.Equal("err EvaluationStepLimitExceeded", runaway.Outcome);
        Assert.Equal(1, runaway.LoopHits);
        Assert.Equal(200_000, runaway.Steps);

        var items = Observe("A = range(1, 90000).filter({ x > 0 }).count\nB = range(1, 90000).filter({ x > 0 }).count\nA + B", optimize: true, limits: host);
        Assert.Equal("err MaterializationLimitExceeded", items.Outcome);
        Assert.True(items.FusionHits > 0);

        var longString = Observe($"Step(s, t) = s + 1, '{new string('a', 9_000)}'\nrepeat(Step, 30, 0, 'z')", optimize: true, limits: host);
        Assert.Equal("err StringMaterializationLimitExceeded", longString.Outcome);
        Assert.Equal(1, longString.LoopHits);

        var oversizedString = Observe($"'{new string('b', 10_001)}'", optimize: true, limits: host);
        Assert.Equal("err StringSizeLimitExceeded", oversizedString.Outcome);
    }

    /// <summary>
    /// Model C under limits: a configured limit never DEMANDS a computation the language leaves
    /// undemanded — an unused deep, random, or host-effect argument stays unevaluated whatever
    /// limits are configured, on both strategies, and the transported cell of a forwarded
    /// parameter is demanded exactly as often as without limits.
    /// </summary>
    [Theory]
    [InlineData("Deep(n) = if(n > 0, Deep(n - 1) + 1, 0)\nG(x, y) = y\nG(Deep(60), 5)")]
    [InlineData("G(x, y) = y\nG(randomInt(0, 999), randomInt(0, 999))")]
    [InlineData("G(x, y) = y\nG(trace(1) + repeat({ z + 1 }, 50, 0), trace(2))")]
    [InlineData("F(k) = repeat({ x + 1 }, 20, 0)\nF(trace(9))")]
    [InlineData("F(k) = repeat({ if(x > 30, k, x + 1) }, 25, 0)\nF(trace(4))")]
    [InlineData("C(v) = range(1, 10).filter({ x > 20 }).count + 0 * 0\nH(v) = C(v)\nH(trace(3))")]
    public void Limits_NeverDemandAnUndemandedComputation(string source)
    {
        foreach (var optimize in new[] { true, false })
        {
            var unlimited = Observe(source, optimize, seed: 11);
            foreach (var (name, limits) in NonBindingConfigurations)
            {
                var configured = Observe(source, optimize, limits, seed: 11);
                Assert.True(unlimited.Accounting == configured.Accounting, $"{name} (optimize={optimize}) changed the run:\n{unlimited.Accounting}\n---\n{configured.Accounting}");
            }
        }
    }

    /// <summary>
    /// The budget accounting is ROUTE-independent too: at every tight step budget the synchronous
    /// optimized and generic strategies and the forced async twin (which always runs the generic
    /// strategies) report the same verdict, the same error tree and the same counters at the
    /// failure point. Host-stack headroom may differ between the routes (Q-09a); these programs
    /// stay far inside every route's headroom, so only the accounting is compared.
    /// </summary>
    [Theory]
    [InlineData("Step(s) = s + 1\nrepeat(Step, 60, 0)")]
    [InlineData("Step(s) = {\n  T = s * 2\n  if(T > 30, s - 1, T() - s + 1)\n}\nrepeat(Step, 25, 1)")]
    [InlineData("range(1, 40).filter({ x mod 3 == 0 }).count")]
    [InlineData("R(n) = if(n > 0, range(n, n).filter({ R(x - 1) >= 0 }).count, 0)\nR(8)")]
    public async Task TightStepBudgets_GiveTheSameVerdictOnEveryRoute(string source)
    {
        var program = Program(source, operations: null);
        var (_, unlimited) = Evaluator.RunCountedObserved(program, enableOptimizations: false);
        for (var budget = 1L; budget <= unlimited.ConsumedSteps + 1; budget++)
        {
            var limits = new EvaluationLimits { MaxSteps = budget };
            var (optimized, optimizedBudget) = Evaluator.RunCountedObserved(program, limits, enableOptimizations: true);
            var (generic, genericBudget) = Evaluator.RunCountedObserved(program, limits, enableOptimizations: false);
            var (twin, twinBudget) = await AsyncEvaluation.AsyncEvaluationHarness.Complete(
                Evaluator.RunCountedObservedAsync(program, limits, zeroArgPropertyResultCache: new AsyncEvaluation.PassThroughAsyncZeroArgPropertyResultCache()));

            string Describe(EvalResult<Evaluator.CountedResult> result, EvaluationBudget observed)
                => (result.IsError ? LoopDiagnosticParityAssertions.DescribeErrorTree(result.Error) : SemanticExplorerHarness.Neutral(result.Value.Value))
                    + $" steps={observed.ConsumedSteps} checkpoints={observed.ConsumedExpressionCheckpoints} items={observed.MaterializedItems}";

            var expected = Describe(generic, genericBudget);
            Assert.Equal(expected, Describe(optimized, optimizedBudget));
            Assert.Equal(expected, Describe(twin, twinBudget));
        }
    }

    /// <summary>
    /// The ROUTE is not a limit's to choose either (Q-09b). With nothing that can suspend — a
    /// synchronous cache, no asynchronous host operation, no deferred module — every asynchronous
    /// entry point runs the synchronous pipeline inline, optimizations included, under every
    /// non-binding configuration exactly as unconfigured. A limit that sent such a run to the async
    /// twin (which always runs the generic strategies, on its own host-stack profile) would show here
    /// as a lost planned loop and fused pipeline, and on the public overloads as the twin refusing
    /// the synchronous property cache.
    /// </summary>
    [Fact]
    public async Task AsyncEntryPoints_KeepTheInlineSynchronousRoute_UnderEveryNonBindingConfiguration()
    {
        const string source = "A = 4\nStep(s) = s + 1\nP(x) = x > 2\nrepeat(Step, 3, 0) + range(1, 5).filter(P).count + A";
        var program = Program(source, operations: null);
        var expectedFlat = Evaluator.RunFlat(program).Value;
        foreach (var (name, limits) in NonBindingConfigurations)
        {
            var loops = new LoopOptimizationDiagnostics();
            var sequences = new SequencePipelineDiagnostics();
            var routed = await Evaluator.RunAsync(
                program, new KatLang.Evaluation.Caching.RunScopedZeroArgPropertyResultCache(), limits, loops, sequences);
            Assert.False(routed.IsError, $"{name}: {(routed.IsError ? routed.Error : null)}");
            Assert.Equal("10", SemanticExplorerHarness.Neutral(routed.Value));
            Assert.True(loops.OptimizedLoopHits == 1, $"{name}: the run left the inline synchronous route (no planned loop)");
            Assert.True(sequences.FilterCountFusionHits == 1, $"{name}: the run left the inline synchronous route (no fused pipeline)");

            var counted = await Evaluator.RunCountedAsync(
                program, new KatLang.Evaluation.Caching.RunScopedZeroArgPropertyResultCache(), limits);
            Assert.False(counted.IsError, $"{name}: {(counted.IsError ? counted.Error : null)}");
            Assert.Equal("10", SemanticExplorerHarness.Neutral(counted.Value.Value));

            var publicRun = await Evaluator.RunAsync(program, limits);
            Assert.False(publicRun.IsError, $"{name}: {(publicRun.IsError ? publicRun.Error : null)}");
            Assert.Equal("10", SemanticExplorerHarness.Neutral(publicRun.Value));
            Assert.Equal(expectedFlat, (await Evaluator.RunFlatAsync(program, limits)).Value);
            Assert.Equal("10", (await KatLangEngine.RunAsync(source, new RunOptions { EvaluationLimits = limits })).ToDisplayString());
        }
    }

    /// <summary>
    /// Q-09a and Q-09b together, on a run that GENUINELY suspends before every recursive descent
    /// (an asynchronous host operation that yields). The suspending twin resumes on fresh stacks,
    /// so it may complete a recursion the synchronous evaluator stops on the same thread size with
    /// <see cref="EvalError.EvaluationStackExhausted"/> — route and host variability, which the
    /// language permits and never calls a mismatch. What the configuration may NOT do is change
    /// anything: every non-binding limit configuration leaves the suspending run's outcome and host
    /// trace exactly as the unconfigured run has them.
    /// </summary>
    [Fact]
    public async Task GenuinelySuspendingRun_IsUnchangedByNonBindingLimits_AndMayOutrunTheSynchronousRoute()
    {
        const string source = "F(x) = if(x < 100, pause() + F(x + 1), x)\nF(0)";

        async Task<string> RunSuspending(EvaluationLimits? limits)
        {
            var log = new List<string>();
            var operations = HostOperations.Create(HostOperation.CreateAsync("pause", async (_, _) =>
            {
                await Task.Yield();
                lock (log) log.Add("pause");
                return new Result.Atom(0);
            }));
            var result = await KatLangEngine.RunAsync(source, new RunOptions { HostOperations = operations, EvaluationLimits = limits });
            return $"{result.GetType().Name}: {result.ToDisplayString()} | pauses={log.Count}";
        }

        var unconfigured = await RunSuspending(null);
        Assert.Equal("Success: 100 | pauses=100", unconfigured);
        foreach (var (name, limits) in NonBindingConfigurations)
            Assert.True(unconfigured == await RunSuspending(limits), $"{name} changed the suspending run");

        // The synchronous route on a 1 MiB thread (the documented minimum) either completes with
        // the same value or stops with the structured host-stack backstop — permitted host/route
        // variability (Q-09a), never a different success and never a crash.
        string? synchronous = null;
        AstStructuralDepthProcessTests.RunOnThreadWithStack(1_048_576, () =>
        {
            var operations = HostOperations.Create(HostOperation.Create("pause", (_, _) => new Result.Atom(0)));
            var result = KatLangEngine.Run(source, new RunOptions { HostOperations = operations });
            synchronous = result is RunResult.EvalFailure failure
                ? "err " + Assert.Single(failure.Errors).Code
                : result.ToDisplayString();
        });
        Assert.Contains(synchronous, new[] { "100", "err EvaluationStackExhausted" });
    }

    /// <summary>
    /// Host cancellation is unchanged by the strategy-neutral accounting and by configured limits:
    /// no token and a live token are the same run; an already-cancelled token throws before any
    /// evaluation on every configuration; a token cancelled during an unbounded planned loop stops
    /// it with the host's <see cref="OperationCanceledException"/>, never a limit error.
    /// </summary>
    [Fact]
    public void Cancellation_IsUnchanged_UnderLimitsAndPlannedAccounting()
    {
        const string source = "Step(s) = s + 1\nrepeat(Step, 3000, 0) + range(1, 100).filter({ x > 50 }).count";
        var program = Program(source, operations: null);
        foreach (var (name, limits) in NonBindingConfigurations)
        {
            var (plain, plainBudget) = Evaluator.RunCountedObserved(program, limits);
            using var live = new CancellationTokenSource();
            var (tokened, tokenedBudget) = Evaluator.RunCountedObserved(program, limits, cancellationToken: live.Token);
            Assert.False(plain.IsError, name);
            Assert.Equal(plain.Value, tokened.Value);
            Assert.Equal(plainBudget.ConsumedSteps, tokenedBudget.ConsumedSteps);
            Assert.Equal(plainBudget.ConsumedExpressionCheckpoints, tokenedBudget.ConsumedExpressionCheckpoints);

            using var cancelled = new CancellationTokenSource();
            cancelled.Cancel();
            var thrown = Assert.ThrowsAny<OperationCanceledException>(
                () => Evaluator.RunCountedObserved(program, limits, cancellationToken: cancelled.Token));
            Assert.Equal(cancelled.Token, thrown.CancellationToken);
        }

        // An UNBOUNDED planned loop under a configured, non-binding step budget: cancellation
        // requested while it runs stops it with the host exception (the planned iterations
        // observe the token through their step charge).
        var runaway = Program("Step(s) = s + 1, true\nwhile(Step, 0)", operations: null);
        foreach (var limits in new EvaluationLimits?[] { null, new EvaluationLimits { MaxSteps = long.MaxValue } })
        {
            using var during = new CancellationTokenSource(TimeSpan.FromMilliseconds(200));
            var diagnostics = new LoopOptimizationDiagnostics();
            var stopped = Assert.ThrowsAny<OperationCanceledException>(
                () => Evaluator.RunCountedObserved(runaway, limits, loopDiagnostics: diagnostics, cancellationToken: during.Token));
            Assert.Equal(during.Token, stopped.CancellationToken);
            Assert.Equal(1, diagnostics.OptimizedLoopHits);
        }
    }
}
