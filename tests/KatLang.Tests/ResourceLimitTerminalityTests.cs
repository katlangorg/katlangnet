using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Sequences;
using KatLang.Rendering;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// RESOURCE LIMITS ARE TERMINAL FOR THE RUN (Q-02 / PV-06, September 2026).
///
/// <para>A resource-limit failure is a property of the run, not a latent argument value.
/// Once any evaluation that actually occurs reaches a resource limit, the run terminates
/// with that failure: an unused parameter, a retained algorithm channel, deferred value
/// demand, call forwarding, a builtin's arity verdict or callback fall-through, or a
/// consumer's choice cannot absorb it, and nothing evaluates after it — no later argument,
/// callee body, random draw, or host operation. A resource limit may stop a run; it never
/// redefines the value of a run that succeeds. Laziness is untouched: an argument the
/// language does not evaluate (an unselected <c>if</c> branch, an invoking callback slot)
/// reaches no limit. The decision is <c>Evaluator.IsDeferrableEvaluationFailure</c>,
/// consulted by user-call argument assembly, the builtin argument adapter, and the fused
/// filter-count pipeline, in the synchronous evaluator and its async twin alike.</para>
///
/// <para>Before the rule, an algorithm-channel argument slot whose evaluation reached a
/// limit RETAINED the failure beside its algorithm binding and surfaced it only on demand,
/// so a callee that ignored the parameter let the run SUCCEED after partial evaluation:
/// <c>G(x, y) = y</c> called as <c>G({Deep(100) + randomInt(0, 1000)}, randomInt(0, 1000))</c>
/// returned the FIRST seeded draw (209) because the limit struck before the first argument's
/// draw, while the unlimited meaning is the SECOND draw (711); a lower <c>MaxDepth</c> turned
/// one success into another, and the host stack, the route, and suspension decided which.
/// Ordinary failures keep their CALL-06 / CALL-03 semantics (deferred until demanded,
/// evaluated at most once), and Q-01's at-most-once law is unchanged. Lean has no resource
/// model; the unlimited Lean meaning is the reference every successful limited run must
/// equal.</para>
/// </summary>
public class ResourceLimitTerminalityTests
{
    // ── Execution routes (the ArgumentValueOutcomeTests route set) ─────────────────────

    public enum Route
    {
        /// <summary>The oracle: <see cref="KatLangEngine.Run"/>.</summary>
        EngineSync,

        /// <summary><see cref="KatLangEngine.RunAsync"/> with synchronous host operations.</summary>
        EngineAsync,

        /// <summary><see cref="KatLangEngine.RunAsync"/> with genuinely suspending host operations: the async twin.</summary>
        EngineAsyncTwin,

        /// <summary>The generic evaluator (optimizations disabled).</summary>
        Generic,

        /// <summary>The optimized evaluator (loop planning and sequence fusion enabled).</summary>
        Optimized,

        /// <summary>The async twin forced by an async-capable property cache, with suspending host operations.</summary>
        ForcedTwin,
    }

    private static readonly Route[] Routes = Enum.GetValues<Route>();

    private sealed class HostLog
    {
        private int _ticks;

        public List<string> Calls { get; } = [];

        public Result Tick()
        {
            var tick = Interlocked.Increment(ref _ticks);
            lock (Calls)
                Calls.Add($"tick#{tick}");
            return new Result.Atom((Decimal128)tick);
        }

        public Result Trace(Result value)
        {
            lock (Calls)
                Calls.Add($"trace({Neutral(value)})");
            return value;
        }

        public Result Pause()
        {
            lock (Calls)
                Calls.Add("pause");
            return new Result.Atom((Decimal128)0);
        }
    }

    /// <summary>
    /// <c>tick()</c> counts its invocations, <c>trace(x)</c> logs and returns its argument,
    /// and <c>pause()</c> logs and returns 0. On the twin routes every operation genuinely
    /// suspends (<c>Task.Yield</c>) before acting, so terminality is exercised across real
    /// suspension points; on the other routes they are synchronous.
    /// </summary>
    private static HostOperations OperationsFor(HostLog log, bool suspending)
        => suspending
            ? HostOperations.Create(
                HostOperation.CreateAsync("tick", async (_, _) => { await Task.Yield(); return log.Tick(); }),
                HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return log.Trace(args[0]); }, "x"),
                HostOperation.CreateAsync("pause", async (_, _) => { await Task.Yield(); return log.Pause(); }))
            : HostOperations.Create(
                HostOperation.Create("tick", (_, _) => log.Tick()),
                HostOperation.Create("trace", (args, _) => log.Trace(args[0]), "x"),
                HostOperation.Create("pause", (_, _) => log.Pause()));

    private sealed record Observation(string Kind, string? Value, IReadOnlyList<string> Codes, IReadOnlyList<string> HostCalls)
    {
        public bool IsResourceLimit { get; init; }

        public IReadOnlyList<string> ErrorDetails { get; init; } = [];

        public override string ToString()
            => $"{Kind} {Value} codes=[{string.Join(",", Codes)}] resource={IsResourceLimit} host=[{string.Join(",", HostCalls)}] details=[{string.Join(";", ErrorDetails)}]";
    }

    private static async Task<Observation> ObserveAsync(Route route, string source, long? seed, EvaluationLimits? limits)
    {
        var log = new HostLog();
        var options = new RunOptions
        {
            RandomSeed = seed,
            EvaluationLimits = limits,
            HostOperations = OperationsFor(log, route is Route.EngineAsyncTwin or Route.ForcedTwin),
        };

        switch (route)
        {
            case Route.EngineSync:
                return FromRunResult(KatLangEngine.Run(source, options), log);
            case Route.EngineAsync:
            case Route.EngineAsyncTwin:
                return FromRunResult(await KatLangEngine.RunAsync(source, options), log);
        }

        var parsed = Parser.Parse(source, options);
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
        var program = new Expr.AlgorithmExpr(parsed.Root);
        var (result, _) = route switch
        {
            Route.Generic => Evaluator.RunCountedObserved(
                program, limits: limits, enableOptimizations: false, hostOperations: options.HostOperations, randomSeed: seed),
            Route.Optimized => Evaluator.RunCountedObserved(
                program, limits: limits, enableOptimizations: true, hostOperations: options.HostOperations, randomSeed: seed),
            Route.ForcedTwin => await Evaluator.RunCountedObservedAsync(
                program,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                limits: limits,
                hostOperations: options.HostOperations,
                randomSeed: seed),
            _ => throw new ArgumentOutOfRangeException(nameof(route), route, null),
        };

        return FromEvalResult(result, log);
    }

    private static Observation FromEvalResult(EvalResult<Evaluator.CountedResult> result, HostLog log)
        => result.IsError
            ? new Observation("err", null, [KatLangError.FromEvalError(result.Error).Code.ToString()], [.. log.Calls])
            {
                IsResourceLimit = result.Error.IsResourceLimit,
                ErrorDetails = [DescribeError(KatLangError.FromEvalError(result.Error))],
            }
            : new Observation("ok", Neutral(result.Value.Value), [], [.. log.Calls]);

    private static Observation FromRunResult(RunResult result, HostLog log) => result switch
    {
        RunResult.Success success => new("ok", Neutral(success.Value), [], [.. log.Calls]),
        RunResult.EvalFailure failure => new("err", null, [.. failure.Errors.Select(static error => error.Code.ToString())], [.. log.Calls])
        {
            IsResourceLimit = failure.Errors.All(static error => error.IsResourceLimit),
            ErrorDetails = [.. failure.Errors.Select(DescribeError)],
        },
        RunResult.ParseFailure failure => new("parse", null, [.. failure.Errors.Select(static error => error.Code.ToString())], [.. log.Calls]),
        RunResult.NoProgramOutput none => new("none", null, [none.Diagnostic.Code.ToString()], [.. log.Calls]),
    };

    private static string DescribeError(KatLangError error) => $"{error.Message} @ {error.Span}";

    private static string Neutral(Result value) => value switch
    {
        Result.Atom atom => ValueTextRenderer.FormatNumberInvariant(atom.Value),
        Result.Str text => "'" + text.Value + "'",
        Result.Bool boolean => boolean.Value ? "true" : "false",
        Result.SequenceValue sequence => "S[" + string.Join(", ", sequence.Items.Select(Neutral)) + "]",
        Result.ListValue list => "L[" + string.Join(", ", list.Items.Select(Neutral)) + "]",
    };

    /// <summary>
    /// Runs <paramref name="source"/> on every route and requires each to agree with the
    /// synchronous engine — outcome kind, value, error codes, and the exact host-call log (so
    /// the exact effects performed before a terminal failure). Returns the oracle. With
    /// <paramref name="twinMayReachHostStackFirst"/>, a twin route may instead stop at the
    /// host-stack backstop (<see cref="IsTwinHostStackBackstop"/>).
    /// </summary>
    private static async Task<Observation> OnEveryRouteAsync(
        string source, long? seed = null, EvaluationLimits? limits = null, bool twinMayReachHostStackFirst = false)
    {
        var oracle = await ObserveAsync(Route.EngineSync, source, seed, limits);
        foreach (var route in Routes.Skip(1))
        {
            var observation = await ObserveAsync(route, source, seed, limits);
            if (twinMayReachHostStackFirst && IsTwinHostStackBackstop(route, oracle, observation))
                continue;

            Assert.True(
                oracle.Kind == observation.Kind
                    && oracle.Value == observation.Value
                    && oracle.Codes.SequenceEqual(observation.Codes)
                    && oracle.IsResourceLimit == observation.IsResourceLimit
                    && oracle.ErrorDetails.SequenceEqual(observation.ErrorDetails)
                    && oracle.HostCalls.SequenceEqual(observation.HostCalls),
                $"{route}: expected {oracle}, got {observation}\nsource:\n{source}");
        }

        return oracle;
    }

    /// <summary>
    /// Whether a twin route stopped at the host-stack backstop where the oracle stopped at a
    /// configured depth or step budget, and is otherwise the same terminal outcome. This
    /// exception is enabled only for the recursive depth/step probes; shallow collection and
    /// string probes keep exact verdict equality. The async twin's frames
    /// are larger than the calibrated synchronous frames, and a suspended twin resumes on a
    /// thread-pool stack, so a deep recursion on a twin route can exhaust the host stack BEFORE
    /// the budget does. Measured on a Windows Debug build (September 2026): a <c>Deep</c> level
    /// costs about 54 KB of stack on the twin against 29 KB synchronously, so the resumed twin's
    /// 1.5 MB thread-pool stack is spent after 25 to 30 steps of <c>Deep(100)</c>, while the
    /// oracle reaches its 40-step budget. WHERE a limit fires is not part of the law: it promises
    /// that the run stops after exactly the effects that preceded the limit, and never a
    /// different success (evaluator-and-hosting.md § Resource limits are terminal for the run;
    /// PV-07). So on a twin route that backstop is accepted in place of the oracle's verdict
    /// when it is equally terminal and performed exactly the oracle's effects; any other
    /// difference, on any route, still fails.
    /// </summary>
    private static bool IsTwinHostStackBackstop(Route route, Observation oracle, Observation observation)
        => route is Route.EngineAsyncTwin or Route.ForcedTwin
            && oracle is { Kind: "err", Value: null, IsResourceLimit: true,
                Codes: [nameof(KatLangErrorCode.EvaluationDepthExceeded) or nameof(KatLangErrorCode.EvaluationStepLimitExceeded)] }
            && observation is { Kind: "err", Value: null, IsResourceLimit: true, Codes: [nameof(KatLangErrorCode.EvaluationStackExhausted)] }
            && observation.HostCalls.SequenceEqual(oracle.HostCalls);

    [Fact]
    public void TwinHostStackException_OnlyAdmitsDepthOrStepOracleOnTwinRoutes()
    {
        // A stack verdict must not hide a regression in a shallow collection/string probe.
        // Exercise every error code and route, including ordinary errors and preflight limits.
        var stack = new Observation("err", null, [nameof(KatLangErrorCode.EvaluationStackExhausted)], ["trace(1)"])
        {
            IsResourceLimit = true,
        };
        foreach (var route in Routes)
        foreach (var code in Enum.GetValues<KatLangErrorCode>())
        {
            var oracle = new Observation("err", null, [code.ToString()], ["trace(1)"]) { IsResourceLimit = true };
            var expected = (route == Route.EngineAsyncTwin || route == Route.ForcedTwin)
                && (code == KatLangErrorCode.EvaluationDepthExceeded || code == KatLangErrorCode.EvaluationStepLimitExceeded);
            Assert.True(expected == IsTwinHostStackBackstop(route, oracle, stack), $"{route}, {code}");
        }
    }

    [Fact]
    public void TwinHostStackException_RejectsDifferentEffectsAndNonterminalObservations()
    {
        var oracle = new Observation("err", null, [nameof(KatLangErrorCode.EvaluationStepLimitExceeded)], ["trace(1)", "trace(2)"])
        {
            IsResourceLimit = true,
        };
        var stack = oracle with { Codes = [nameof(KatLangErrorCode.EvaluationStackExhausted)] };
        Assert.True(IsTwinHostStackBackstop(Route.ForcedTwin, oracle, stack));
        foreach (var changed in new[]
        {
            stack with { HostCalls = ["trace(1)"] },
            stack with { HostCalls = ["trace(2)", "trace(1)"] },
            stack with { HostCalls = ["trace(1)", "trace(2)", "trace(9)"] },
            stack with { Kind = "ok" },
            stack with { Value = "7" },
            stack with { IsResourceLimit = false },
            stack with { Codes = [] },
            stack with { Codes = [nameof(KatLangErrorCode.EvaluationStackExhausted), nameof(KatLangErrorCode.DivisionByZero)] },
        })
            Assert.False(IsTwinHostStackBackstop(Route.ForcedTwin, oracle, changed), changed.ToString());
        Assert.False(IsTwinHostStackBackstop(Route.ForcedTwin, oracle with { Kind = "ok" }, stack));
        Assert.False(IsTwinHostStackBackstop(Route.ForcedTwin, oracle with { IsResourceLimit = false }, stack));
    }

    private static void AssertTerminal(Observation observation, KatLangErrorCode code, params string[] hostCalls)
    {
        Assert.True(observation.Kind == "err" && observation.IsResourceLimit, $"expected a terminal resource-limit failure, got {observation}");
        Assert.Equal([code.ToString()], observation.Codes);
        Assert.Equal(hostCalls, observation.HostCalls);
    }

    private static void AssertFails(Observation observation, KatLangErrorCode code, params string[] hostCalls)
    {
        Assert.True(observation.Kind == "err", $"expected an evaluation failure, got {observation}");
        Assert.Equal([code.ToString()], observation.Codes);
        Assert.Equal(hostCalls, observation.HostCalls);
    }

    private static void AssertOk(Observation observation, string neutral, params string[] hostCalls)
    {
        Assert.True(observation.Kind == "ok", $"expected success, got {observation}");
        Assert.Equal(neutral, observation.Value);
        Assert.Equal(hostCalls, observation.HostCalls);
    }

    /// <summary>The display rows of a seeded, unlimited engine run (the reference random stream).</summary>
    private static string[] Rows(string source, long seed)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, new RunOptions { RandomSeed = seed }))
            .ToDisplayString()
            .Split('\n')
            .Select(static row => row.Trim())
            .ToArray();

    /// <summary>Recursion through builtin <c>if</c>: two depth units per level.</summary>
    private const string DeepDefinition = "Deep(n) = if(n == 0, 0, 1 + Deep(n - 1))\n";

    /// <summary>A depth limit far below <c>Deep(100)</c>'s need and far above every other shape here.</summary>
    private static readonly EvaluationLimits Shallow = new() { MaxDepth = 24 };

    /// <summary>
    /// Prefixes <paramref name="program"/> with <c>Deep</c> and the traced zero-parameter
    /// property <c>DeepP = trace(1) + Deep(100)</c>, whose evaluation logs <c>trace(1)</c> and
    /// then reaches the limit. An <c>open</c> declaration must precede its algorithm's other
    /// declarations, so an opening program keeps its first line first.
    /// </summary>
    private static string WithDeepPrelude(string program)
    {
        const string prelude = DeepDefinition + "DeepP = trace(1) + Deep(100)\n";
        if (!program.StartsWith("open ", StringComparison.Ordinal))
            return prelude + program;

        var firstLineEnd = program.IndexOf('\n') + 1;
        return program[..firstLineEnd] + prelude + program[firstLineEnd..];
    }

    // ── 1. The canonical PV-06 reproducer ─────────────────────────────────────────────

    /// <summary>
    /// With seed 3 the stream begins 209, 711. With sufficient resources the first argument
    /// consumes 209 and the second 711, so the unlimited meaning is 711. Before the rule, the
    /// depth limit struck inside <c>Deep(100)</c> before the first draw, the callee ignored
    /// <c>x</c>, the retained failure was dropped, and the second argument drew 209: the run
    /// SUCCEEDED with a value that exists only because the limit was absorbed. Now the limit
    /// ends the run, on every route, before either draw.
    /// </summary>
    [Fact]
    public async Task CanonicalReproducer_ALimitReachedInAnIgnoredArgument_EndsTheRun()
    {
        Assert.Equal(["209", "711"], Rows("randomInt(0, 1000), randomInt(0, 1000)", 3));

        const string canonical = DeepDefinition
            + "G(x, y) = y\nG({Deep(100) + randomInt(0, 1000)}, randomInt(0, 1000))";
        AssertTerminal(await OnEveryRouteAsync(canonical, seed: 3, limits: Shallow), KatLangErrorCode.EvaluationDepthExceeded);

        // The default depth ceiling cannot hold Deep(100) either: a resource-limit failure,
        // never the seeded 209 (the host stack may legitimately win the race on some routes,
        // PV-07, so only the classification is pinned here).
        var unconfigured = KatLangEngine.Run(canonical, new RunOptions { RandomSeed = 3 });
        var failure = Assert.IsType<RunResult.EvalFailure>(unconfigured);
        Assert.True(Assert.Single(failure.Errors).IsResourceLimit, failure.Errors[0].Message);

        // Traced draws: the limit strikes before the first draw, and the second argument never runs.
        AssertTerminal(
            await OnEveryRouteAsync(
                DeepDefinition + "G(x, y) = y\nG({Deep(100) + trace(randomInt(0, 1000))}, trace(randomInt(0, 1000)))",
                seed: 3,
                limits: Shallow),
            KatLangErrorCode.EvaluationDepthExceeded);

        // A draw that happens BEFORE the limit is the only one: the stream stops where the run stops.
        AssertTerminal(
            await OnEveryRouteAsync(
                DeepDefinition + "G(x, y) = y\nG({trace(randomInt(0, 1000)) + Deep(100)}, trace(randomInt(0, 1000)))",
                seed: 3,
                limits: Shallow),
            KatLangErrorCode.EvaluationDepthExceeded,
            "trace(209)");
    }

    /// <summary>
    /// The sufficient-resource half of the canonical example: when the depth fits, the first
    /// argument completes, consumes 209, and the ignored parameter changes nothing — the run
    /// returns the unlimited meaning 711 on every route.
    /// </summary>
    [Fact]
    public async Task CanonicalReproducer_WithSufficientDepth_ReturnsTheUnlimitedMeaning()
        => AssertOk(
            await OnEveryRouteAsync(
                DeepDefinition + "G(x, y) = y\nG({Deep(20) + trace(randomInt(0, 1000))}, trace(randomInt(0, 1000)))",
                seed: 3,
                limits: new EvaluationLimits { MaxDepth = 64 }),
            "711",
            "trace(209)",
            "trace(711)");

    /// <summary>
    /// The explicit <c>MaxDepth</c> sweep of the PV-06 record. Before the rule MaxDepth 10..40
    /// gave ok 209 and 50..128 gave ok 711. Now every limit either stops the run with a
    /// resource-limit failure or returns 711, and the successes form one contiguous upper
    /// range: raising the limit may turn a failure into the success, never one success into
    /// another.
    /// </summary>
    [Fact]
    public void ExplicitDepthSweep_EveryOutcomeIsTheLimitFailureOrTheUnlimitedMeaning()
    {
        const string source = DeepDefinition + "G(x, y) = y\nG({Deep(20) + randomInt(0, 1000)}, randomInt(0, 1000))";
        var outcomes = new List<(int MaxDepth, string Outcome)>();
        for (var maxDepth = 1; maxDepth <= EvaluationLimits.MaxSupportedDepth; maxDepth++)
        {
            var result = KatLangEngine.Run(source, new RunOptions
            {
                RandomSeed = 3,
                EvaluationLimits = new EvaluationLimits { MaxDepth = maxDepth },
            });
            outcomes.Add((maxDepth, result switch
            {
                RunResult.Success success => "ok " + success.ToDisplayString(),
                RunResult.EvalFailure failure when failure.Errors.Single().IsResourceLimit => "limit",
                _ => "unexpected " + result,
            }));
        }

        Assert.All(outcomes, entry => Assert.Contains(entry.Outcome, new[] { "limit", "ok 711" }));
        var firstSuccess = outcomes.FindIndex(static entry => entry.Outcome != "limit");
        Assert.True(firstSuccess > 0, "the sweep must cross from failure to success");
        Assert.All(outcomes.Skip(firstSuccess), static entry => Assert.Equal("ok 711", entry.Outcome));
    }

    // ── 2. Terminality: nothing runs after the limit ───────────────────────────────────

    /// <summary>
    /// Terminal means the run STOPS where the limit strikes: the first argument's effects that
    /// already happened stay happened, but its own later work, every later argument, and the
    /// callee body never run — on every route, the genuinely suspending twins included.
    /// </summary>
    [Fact]
    public async Task NothingEvaluatesAfterTheLimit_LaterEffectsNeverRun()
    {
        AssertTerminal(
            await OnEveryRouteAsync(
                DeepDefinition + "G(x, y) = trace(9)\nG({trace(1) + Deep(100) + trace(2)}, trace(3))",
                limits: Shallow),
            KatLangErrorCode.EvaluationDepthExceeded,
            "trace(1)");

        // Suspension before and after the argument that fails changes nothing.
        AssertTerminal(
            await OnEveryRouteAsync(
                DeepDefinition + "G(x, y, z) = trace(9)\nG(pause(), {pause() + trace(1) + Deep(100)}, pause())",
                limits: Shallow),
            KatLangErrorCode.EvaluationDepthExceeded,
            "pause",
            "pause",
            "trace(1)");

        // A later root row never runs either (the run has no output).
        AssertTerminal(
            await OnEveryRouteAsync(
                DeepDefinition + "G(x) = 0\ntrace(1)\nG({Deep(100)})\ntrace(2)",
                limits: Shallow),
            KatLangErrorCode.EvaluationDepthExceeded,
            "trace(1)");
    }

    /// <summary>
    /// The consumer cannot decide whether an encountered limit is terminal: a callee that
    /// uses the parameter, one that ignores it, one that reads it twice, and one that only
    /// forwards it all fail identically, after identical effects.
    /// </summary>
    [Theory]
    [InlineData("Use(x) = x")]
    [InlineData("Use(x) = 0")]
    [InlineData("Use(x) = x, x")]
    [InlineData("Keep(w) = 5\nUse(x) = Keep(x)")]
    [InlineData("Use(x) = x.string")]
    [InlineData("Use(x) = sum([x])")]
    [InlineData("Use(x) = if(false, x, 0)")]
    public async Task EveryConsumerFailsAlike(string callee)
        => AssertTerminal(
            await OnEveryRouteAsync(
                DeepDefinition + callee + "\nUse({trace(1) + Deep(100)}), trace(2)",
                limits: Shallow),
            KatLangErrorCode.EvaluationDepthExceeded,
            "trace(1)");

    // ── 3. Every binding shape, every consumer, every spelling ─────────────────────────

    /// <summary>
    /// The hostile-review matrix: every way an argument can reach a callee that does not
    /// demand its value — fixed, collecting, nested-pattern, clause-family, forwarding,
    /// alias, opened, structural, higher-order, native wrapper, and dotted spellings, and
    /// builtin versus user-defined consumers — terminates on the limit the argument reached.
    /// </summary>
    [Theory]
    [InlineData("F(x, y) = y\nF(DeepP, 7)")]
    [InlineData("F(x, y) = y\nF({DeepP}, 7)")]
    [InlineData("F(x, y) = y\nF({ {DeepP} }, 7)")]
    [InlineData("Q(x, x) = x\nQ(DeepP, 7)")]
    [InlineData("Only(*xs) = DeepP\nIgnore(f) = 7\nIgnore(Only)")]
    [InlineData("Outer(v) = map([1, 2], {x + 0})\nOuter(DeepP)")]
    [InlineData("a, *rest = DeepP, 1, 2\nIgnore(v) = 7\nIgnore(rest)")]
    [InlineData("5.string(DeepP)")]
    [InlineData("Ignore(v) = false\nStep(s) = s + 1, Ignore({DeepP})\nwhile(Step, 0)")]
    [InlineData("Coll(*xs) = 7\nColl(DeepP)")]
    [InlineData("Coll(*xs) = 7\nColl(1, DeepP, 2)")]
    [InlineData("P((a, b)) = 7\nP(DeepP)")]
    [InlineData("F(0) = 7\nF(n) = 8\nF(DeepP)")]
    [InlineData("Keep(w) = 7\nF(v) = Keep(v)\nF(DeepP)")]
    [InlineData("Keep(w) = 7\nAlias = Keep\nAlias(DeepP)")]
    [InlineData("open Box\nBox = {\n    public V = DeepP\n}\nIgnore(v) = 7\nIgnore(V)")]
    [InlineData("Box = {\n    public V = DeepP\n}\nIgnore(v) = 7\nIgnore(Box.V)")]
    [InlineData("Use(f, x) = x\nUse(DeepP, 7)")]
    [InlineData("Ignore(v) = 7\nIgnore(abs(DeepP))")]
    [InlineData("Ignore(v) = 7\nIgnore(Math.Abs(DeepP))")]
    [InlineData("Ignore(v, w) = 7\nDeepP.Ignore(1)")]
    [InlineData("Ignore(v) = 7\nIgnore({DeepP}.string)")]
    [InlineData("x, y = DeepP, 1\nIgnore(v) = 7\nIgnore(x)")]
    [InlineData("MyFilter(xs, p) = []\nMyFilter([], {DeepP})")]
    [InlineData("filter([], {DeepP})")]
    [InlineData("map([], {DeepP})")]
    [InlineData("reduce([], {x + y}, {DeepP})")]
    [InlineData("count([DeepP])")]
    [InlineData("count({DeepP}, 2)")]
    [InlineData("take([1, 2], {DeepP})")]
    [InlineData("F(v) = 7\nrange(1, 3).filter({x > F({DeepP})}).count")]
    [InlineData("Step(s) = s + 1\nrepeat(Step, 2, {DeepP})")]
    [InlineData("Ignore(v) = 0\nStep(s) = s + Ignore({DeepP})\nrepeat(Step, 2, 0)")]
    public async Task EveryBindingShape_TerminatesOnTheLimit(string program)
        => AssertTerminal(
            await OnEveryRouteAsync(WithDeepPrelude(program) + ", trace(2)", limits: Shallow),
            KatLangErrorCode.EvaluationDepthExceeded,
            "trace(1)");

    /// <summary>
    /// A builtin consumer and its user-defined equivalent agree: before the rule the builtin
    /// adapter already treated the limit as the call's verdict (surfacing it only after later
    /// slots had run), while the user-defined twin let the run succeed.
    /// </summary>
    [Theory]
    [InlineData("filter([], {DeepP})", "MyFilter(xs, p) = []\nMyFilter([], {DeepP})")]
    [InlineData("map([], {DeepP})", "MyMap(xs, f) = []\nMyMap([], {DeepP})")]
    [InlineData("take([1], {DeepP})", "MyTake(xs, n) = xs\nMyTake([1], {DeepP})")]
    public async Task BuiltinAndUserDefinedConsumers_Agree(string builtin, string userDefined)
    {
        var viaBuiltin = await OnEveryRouteAsync(WithDeepPrelude(builtin) + ", trace(2)", limits: Shallow);
        var viaUser = await OnEveryRouteAsync(WithDeepPrelude(userDefined) + ", trace(2)", limits: Shallow);
        AssertTerminal(viaBuiltin, KatLangErrorCode.EvaluationDepthExceeded, "trace(1)");
        AssertTerminal(viaUser, KatLangErrorCode.EvaluationDepthExceeded, "trace(1)");
        Assert.Equal(viaBuiltin.ToString(), viaUser.ToString());
    }

    /// <summary>
    /// The builtin adapter no longer evaluates a later slot after an earlier slot's limit, and
    /// neither its arity verdict nor an earlier slot's retained ORDINARY failure replaces the
    /// limit: the limit was the first failure RAISED in evaluation order.
    /// </summary>
    [Fact]
    public async Task BuiltinAdapter_LimitBeatsArityVerdictAndEarlierOrdinaryFailures()
    {
        const string prefix = DeepDefinition + "DeepP = Deep(100)\nBad = trace(0) / 0\n";
        // Arity: `count` takes one argument; the limit in the first is raised before the verdict.
        AssertTerminal(await OnEveryRouteAsync(prefix + "count({DeepP}, trace(2))", limits: Shallow),
            KatLangErrorCode.EvaluationDepthExceeded);
        // An earlier ordinary failure is deferred (CALL-03); the later limit is raised.
        AssertTerminal(await OnEveryRouteAsync(prefix + "take(Bad, {DeepP})", limits: Shallow),
            KatLangErrorCode.EvaluationDepthExceeded,
            "trace(0)");
        // A callable-shaped item in a VALUE slot is demanded during assembly (a collecting-only
        // callable accepts the zero-argument demand); a limit that demand reaches ends the call
        // before the next slot, instead of being recorded on the item and replaced by the verdict.
        AssertTerminal(await OnEveryRouteAsync(prefix + "Only(*xs) = trace(1) + Deep(100)\ncount(Only, trace(2))", limits: Shallow),
            KatLangErrorCode.EvaluationDepthExceeded,
            "trace(1)");
        // Controls: ordinary failures keep the adapter's own precedence.
        AssertFails(await OnEveryRouteAsync(prefix + "count(Bad, trace(2))"),
            KatLangErrorCode.ArityMismatch,
            "trace(0)",
            "trace(2)");
        AssertFails(await OnEveryRouteAsync(prefix + "take(Bad, {1 / 0})"),
            KatLangErrorCode.DivisionByZero,
            "trace(0)");
    }

    /// <summary>
    /// The fused filter-count pipeline keeps exact parity with the generic adapter it
    /// replaces (the Optimized route fuses; the others do not): a source that reaches a limit
    /// ends the call before the predicate is attempted, and a predicate attempt that reaches
    /// a limit beats the source's deferred ordinary failure — in the direct-range and the
    /// dotted-receiver forms alike.
    /// </summary>
    [Theory]
    [InlineData("count(filter(range(1, DeepP), (trace(5))))", "count(filter(range(1, 3), (trace(5))))")]
    [InlineData("range(1, DeepP).filter((trace(5))).count", "range(1, 3).filter((trace(5))).count")]
    [InlineData("R = range(1, DeepP)\nR.filter((trace(5))).count", "R = range(1, 3)\nR.filter((trace(5))).count")]
    public async Task FusedPipeline_SourceLimitEndsTheCallBeforeThePredicate(string pipeline, string fusableTwin)
    {
        AssertCommitsToFusion(pipeline, fusableTwin);
        AssertTerminal(
            await OnEveryRouteAsync(WithDeepPrelude(pipeline), limits: Shallow),
            KatLangErrorCode.EvaluationDepthExceeded,
            "trace(1)");
    }

    [Theory]
    [InlineData("count(filter(range(1, trace(2) / 0), (DeepP)))", "count(filter(range(1, 3), (1)))")]
    [InlineData("range(1, trace(2) / 0).filter((DeepP)).count", "range(1, 3).filter((1)).count")]
    [InlineData("range(1, trace(2) / 0).filter({DeepP}).count", "range(1, 3).filter({1}).count")]
    public async Task FusedPipeline_PredicateLimitBeatsTheDeferredSourceFailure(string pipeline, string fusableTwin)
    {
        AssertCommitsToFusion(pipeline, fusableTwin);
        AssertTerminal(
            await OnEveryRouteAsync(WithDeepPrelude(pipeline), limits: Shallow),
            KatLangErrorCode.EvaluationDepthExceeded,
            "trace(2)",
            "trace(1)");
    }

    /// <summary>
    /// Proves the Optimized route takes the COMMITTED fused region for <paramref name="pipeline"/>:
    /// the same shape with a harmless source and predicate records a fusion hit, and the
    /// failing pipeline records no fallback (recognition never evaluates anything, so a
    /// recognized shape either commits or falls back before its first evaluation; a committed
    /// region that ends in an error records no hit).
    /// </summary>
    private static void AssertCommitsToFusion(string pipeline, string fusableTwin)
    {
        Assert.Equal(1, Diagnostics(fusableTwin).FilterCountFusionHits);
        var failing = Diagnostics(pipeline);
        Assert.Equal(0, failing.FilterCountFusionFallbacks);
        Assert.Equal(0, failing.FilterCountFusionHits);

        static SequencePipelineDiagnosticsSnapshot Diagnostics(string pipeline)
        {
            var diagnostics = new SequencePipelineDiagnostics();
            var operations = OperationsFor(new HostLog(), suspending: false);
            var parsed = Parser.Parse(WithDeepPrelude(pipeline), new RunOptions { HostOperations = operations });
            Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
            _ = Evaluator.RunCountedObserved(
                new Expr.AlgorithmExpr(parsed.Root),
                limits: Shallow,
                enableOptimizations: true,
                hostOperations: operations,
                sequenceDiagnostics: diagnostics);
            return diagnostics.GetSnapshot();
        }
    }

    // ── 4. Every practical resource-limit kind ────────────────────────────────────────

    private static (string Failing, EvaluationLimits Limits, KatLangErrorCode Code) LimitKind(string kind) => kind switch
    {
        "depth" => ("trace(1) + Deep(100)", new EvaluationLimits { MaxDepth = 24 }, KatLangErrorCode.EvaluationDepthExceeded),
        "steps" => ("trace(1) + Deep(100)", new EvaluationLimits { MaxSteps = 40 }, KatLangErrorCode.EvaluationStepLimitExceeded),
        "collection" => ("trace(1) + range(1, 50).count", new EvaluationLimits { MaxCollectionItems = 10 }, KatLangErrorCode.CollectionSizeLimitExceeded),
        "materialized" => ("trace(1) + range(1, 50).count", new EvaluationLimits { MaxMaterializedItems = 10 }, KatLangErrorCode.MaterializationLimitExceeded),
        "string" => ("trace(1), 123456789012.string", new EvaluationLimits { MaxStringLength = 8 }, KatLangErrorCode.StringSizeLimitExceeded),
        "string-units" => ("trace(1), 123456789012.string", new EvaluationLimits { MaxMaterializedStringChars = 8 }, KatLangErrorCode.StringMaterializationLimitExceeded),
        _ => throw new ArgumentOutOfRangeException(nameof(kind), kind, null),
    };

    /// <summary>
    /// Every resource limit an argument's evaluation can deterministically reach under an
    /// explicit budget is terminal: the ignoring and the using callee fail alike, and the
    /// second argument's effect never happens. (The two remaining classifications cannot be
    /// reached inside an argument: <c>AstDepthLimitExceeded</c> is the pre-evaluation
    /// structural preflight, and <c>DisplayLengthLimitExceeded</c> is rendering state after a
    /// successful run. The host-stack backstop is pinned separately on a controlled stack.)
    /// The synchronous oracle pins each budget's own kind. On the async twin routes the
    /// <c>Deep(100)</c> recursion may exhaust the host stack before the budget (for <c>steps</c>
    /// on a Windows Debug build it does); that stop is equally terminal, so it is accepted
    /// there when it performed exactly the oracle's effects (<see cref="IsTwinHostStackBackstop"/>).
    /// </summary>
    [Theory]
    [InlineData("depth")]
    [InlineData("steps")]
    [InlineData("collection")]
    [InlineData("materialized")]
    [InlineData("string")]
    [InlineData("string-units")]
    public async Task EveryPracticalLimitKind_IsTerminal(string kind)
    {
        var (failing, limits, code) = LimitKind(kind);
        foreach (var callee in new[] { "G(x, y) = y", "G(x, y) = x + y" })
        {
            AssertTerminal(
                await OnEveryRouteAsync(
                    $"{DeepDefinition}{callee}\nG({{{failing}}}, trace(2))", limits: limits,
                    twinMayReachHostStackFirst: kind is "depth" or "steps"),
                code,
                "trace(1)");
        }

        // Unlimited, the same argument completes and the second argument runs.
        var unlimited = await OnEveryRouteAsync($"{DeepDefinition}G(x, y) = y\nG({{{failing.Replace("Deep(100)", "Deep(5)")}}}, trace(2))");
        Assert.True(unlimited.Kind == "ok", unlimited.ToString());
        Assert.Equal(["trace(1)", "trace(2)"], unlimited.HostCalls);
    }

    /// <summary>
    /// The machine-dependent host-stack backstop is a resource limit like any other: once it
    /// fires inside an argument the run fails, and nothing after it runs. WHERE it fires is a
    /// property of the thread, build, and route (PV-07) — so the probe sweeps several small
    /// stacks and pins only terminality, plus that the backstop genuinely fired somewhere. The
    /// host operations are synchronous so the whole evaluation stays on the controlled stack.
    /// </summary>
    [Fact]
    public void HostStackBackstop_IsTerminalWhereverItFires()
    {
        const string source = DeepDefinition + "G(x, y) = trace(9)\nG({trace(1) + Deep(100)}, trace(3))";
        var sawStackExhaustion = false;
        foreach (var stackBytes in new[] { 256 * 1024, 384 * 1024, 512 * 1024, 1024 * 1024 })
        {
            foreach (var twin in new[] { false, true })
            {
                var log = new HostLog();
                var operations = OperationsFor(log, suspending: false);
                var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
                Assert.False(parsed.HasErrors);
                var program = new Expr.AlgorithmExpr(parsed.Root);
                EvalResult<Evaluator.CountedResult>? outcome = null;
                AstStructuralDepthProcessTests.RunOnThreadWithStack(stackBytes, () =>
                {
                    if (!twin)
                    {
                        outcome = Evaluator.RunCountedObserved(program, hostOperations: operations).Result;
                        return;
                    }

                    var pending = Evaluator.RunCountedObservedAsync(
                        program,
                        zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache(),
                        hostOperations: operations);
                    Assert.True(pending.IsCompleted, "a non-suspending twin run completes on the controlled stack");
                    outcome = pending.GetAwaiter().GetResult().Result;
                });

                var result = outcome!.Value;
                Assert.True(result.IsError && result.Error.IsResourceLimit, $"{stackBytes} twin={twin}: {result}");
                Assert.Equal(["trace(1)"], log.Calls);
                sawStackExhaustion |= KatLangError.FromEvalError(result.Error).Code == KatLangErrorCode.EvaluationStackExhausted;
            }
        }

        Assert.True(sawStackExhaustion, "the sweep must reach the host-stack backstop at least once");
    }

    // ── 5. Ordinary failures keep their semantics (the controls) ──────────────────────

    /// <summary>
    /// The same shapes with an ORDINARY failure are unchanged: the failure is retained beside
    /// the algorithm channel (CALL-06), later arguments and the callee still run, an ignoring
    /// callee succeeds, and a demanding one reports the one retained failure.
    /// </summary>
    [Fact]
    public async Task OrdinaryFailures_StayLatent_UntilDemanded()
    {
        AssertOk(
            await OnEveryRouteAsync("G(x, y) = trace(9)\nG({trace(1) + 1 / 0 + trace(2)}, trace(3))"),
            "9",
            "trace(1)",
            "trace(3)",
            "trace(9)");
        AssertFails(
            await OnEveryRouteAsync("G(x, y) = x\nG({trace(1) + 1 / 0}, trace(3))"),
            KatLangErrorCode.DivisionByZero,
            "trace(1)",
            "trace(3)");
        AssertOk(
            await OnEveryRouteAsync("G(x, y) = y\nG({1 / 0 + randomInt(0, 1000)}, randomInt(0, 1000))", seed: 3),
            "209");
        // A collector demands its items at binding, so it surfaces the retained failure (CALL-06).
        AssertFails(await OnEveryRouteAsync("Coll(*xs) = 7\nColl({trace(1) / 0}), trace(2)"), KatLangErrorCode.DivisionByZero, "trace(1)");
        AssertOk(await OnEveryRouteAsync("Keep(w) = 5\nF(v) = Keep(v)\nF({trace(1) / 0})"), "5", "trace(1)");
    }

    /// <summary>
    /// Laziness is preserved: an argument the language never evaluates reaches no limit, so a
    /// deep computation in an unselected branch, an invoking slot that is never invoked, an
    /// undemanded property, or an undemanded deconstruction costs nothing and fails nothing.
    /// </summary>
    [Fact]
    public async Task Laziness_AnUnevaluatedArgumentReachesNoLimit()
    {
        AssertOk(await OnEveryRouteAsync(WithDeepPrelude("if(true, 7, DeepP)"), limits: Shallow), "7");
        AssertOk(await OnEveryRouteAsync(WithDeepPrelude("map([], {x + DeepP})"), limits: Shallow), "L[]");
        AssertOk(await OnEveryRouteAsync(WithDeepPrelude("Step(s) = DeepP + s\nIgnore(f) = 7\nIgnore(Step)"), limits: Shallow), "7");
        AssertOk(await OnEveryRouteAsync(WithDeepPrelude("Step(s) = DeepP + s\nrepeat(Step, 0, 7)"), limits: Shallow), "7");
        AssertOk(await OnEveryRouteAsync(WithDeepPrelude("x, y = DeepP, 1\n7"), limits: Shallow), "7");
        AssertOk(await OnEveryRouteAsync(WithDeepPrelude("Unused = DeepP\n7"), limits: Shallow), "7");
    }

    // ── 6. Q-01 interaction ───────────────────────────────────────────────────────────

    /// <summary>
    /// AT-MOST-ONCE ARGUMENT VALUE EVALUATION is intact beside the new rule: an ordinary
    /// failure is retained once and every read reports it, a successful value is evaluated
    /// once and read many times, an explicit invocation stays fresh, and a limit reached by
    /// a slot is terminal at once — never retained for a later read.
    /// </summary>
    [Fact]
    public async Task AtMostOnceArgumentValueEvaluation_IsIntact()
    {
        AssertFails(await OnEveryRouteAsync("Bad = trace(1) / 0\nPair(x) = x, x\nPair(Bad)"),
            KatLangErrorCode.DivisionByZero, "trace(1)");
        AssertOk(await OnEveryRouteAsync("A = trace(tick())\nPair(x) = x, x\nPair(A), A"),
            "S[S[1, 1], 1]", "tick#1", "trace(1)");
        AssertOk(await OnEveryRouteAsync("P = tick()\nTwice0(f) = f(), f(), f\nTwice0(P)"),
            "S[2, 3, 1]", "tick#1", "tick#2", "tick#3");
        // An ordinary failure beside a later limit: the first slot is evaluated once and
        // retained, the second slot's limit ends the call.
        AssertTerminal(
            await OnEveryRouteAsync(DeepDefinition + "Bad = trace(1) / 0\nG(x, y) = 0\nG(Bad, {trace(2) + Deep(100)})", limits: Shallow),
            KatLangErrorCode.EvaluationDepthExceeded,
            "trace(1)",
            "trace(2)");
    }

    // ── 7. The limit law: limits may stop a run, never redefine it ────────────────────

    /// <summary><c>Deep</c> plus <c>DeepP = Deep(12) + randomInt(0, 1000)</c>: fits a generous limit, fails a tight one.</summary>
    private const string DrawingPrelude = DeepDefinition + "DeepP = Deep(12) + randomInt(0, 1000)\n";

    public static TheoryData<string, string> AbsorptionShapedPrograms => new()
    {
        { "fixed", DrawingPrelude + "G(x, y) = y\nG(DeepP, randomInt(0, 1000))" },
        { "block", DrawingPrelude + "G(x, y) = y\nG({ {DeepP} }, randomInt(0, 1000))" },
        { "repeated-name", DrawingPrelude + "Q(x, x) = x\nQ(DeepP, 7), randomInt(0, 1000)" },
        { "collecting-only-argument", DeepDefinition + "Only(*xs) = Deep(12) + randomInt(0, 1000)\nIgnore(f) = 7\nIgnore(Only), randomInt(0, 1000)" },
        { "collector", DrawingPrelude + "Coll(*xs) = 0\nColl({DeepP}) + randomInt(0, 1000)" },
        { "callback-capture", DrawingPrelude + "Outer(v) = map([1, 2], {x + 0})\nOuter(DeepP), randomInt(0, 1000)" },
        { "loop-step", DrawingPrelude + "Ignore(v) = 0\nStep(s) = s + Ignore({DeepP})\nrepeat(Step, 3, 0), randomInt(0, 1000)" },
        { "while-step", DrawingPrelude + "Ignore(v) = false\nStep(s) = s + 1, Ignore({DeepP})\nwhile(Step, 0), randomInt(0, 1000)" },
        { "collecting-deconstruction", DrawingPrelude + "a, *rest = DeepP, 1, 2\nIgnore(v) = 7\nIgnore(rest), randomInt(0, 1000)" },
        { "forwarded", DrawingPrelude + "Keep(w) = randomInt(0, 1000)\nF(v) = Keep(v)\nF(DeepP)" },
        { "dot-receiver", DrawingPrelude + "Ignore(v, w) = w\nDeepP.Ignore(randomInt(0, 1000))" },
        { "filter-predicate", DrawingPrelude + "F(v) = 7\nrange(1, 3).filter({x > F({DeepP})}).count, randomInt(0, 1000)" },
        { "clause-family", DrawingPrelude + "F(0) = 1\nF(n) = randomInt(0, 1000)\nG(x, y) = y\nG(DeepP, F(1))" },
        { "builtin", DeepDefinition + "take([randomInt(0, 1000)], {Deep(12) + randomInt(0, 1000) * 0 + 1}), randomInt(0, 1000)" },
        { "collection", "G(x, y) = y\nG({range(1, 20).count + randomInt(0, 1000)}, randomInt(0, 1000))" },
        { "string", "G(x, y) = y\nG({(123456789012.string, randomInt(0, 1000))}, randomInt(0, 1000))" },
        { "self-reference", "G(x, y) = y\nA = G({A}, randomInt(0, 1000000))\nA" },
    };

    /// <summary>
    /// THE LIMIT LAW as a metamorphic relation: for a fixed program, seed, and entry point,
    /// varying ONE limit at a time may only move the outcome between a resource-limit failure
    /// and the run the program performs without that limit. Every run that COMPLETES under a
    /// limit — with a success value or with an ordinary failure — is exactly the unconfigured
    /// run (so a limit never changes one success into another, and never turns a failure into
    /// a success), and once the program fits, every larger limit completes the same way. The
    /// programs are shaped so that absorbing a limit would shift a later random draw: against
    /// the evaluator before the rule, 14 of these shapes completed under some limit with a
    /// success DIFFERENT from the unconfigured run's (the self-reference shape with a different
    /// one for almost every depth), and the repeated-name shape turned its ordinary failure into
    /// a success; only the builtin and collector controls, which already surfaced the limit, held.
    /// </summary>
    [Theory]
    [MemberData(nameof(AbsorptionShapedPrograms))]
    public void TheLimitLaw_ALimitMayStopARunButNeverChangeItsValue(string shape, string source)
    {
        _ = shape;
        var sweeps = new (string Name, int From, int To, Func<int, EvaluationLimits> Make)[]
        {
            ("MaxDepth", 1, EvaluationLimits.MaxSupportedDepth, static n => new EvaluationLimits { MaxDepth = n }),
            ("MaxSteps", 1, 120, static n => new EvaluationLimits { MaxSteps = n }),
            ("MaxCollectionItems", 1, 40, static n => new EvaluationLimits { MaxCollectionItems = n }),
            ("MaxMaterializedItems", 1, 80, static n => new EvaluationLimits { MaxMaterializedItems = n }),
            ("MaxStringLength", 1, 60, static n => new EvaluationLimits { MaxStringLength = n }),
            ("MaxMaterializedStringChars", 1, 120, static n => new EvaluationLimits { MaxMaterializedStringChars = n }),
        };

        foreach (var seed in new long[] { 3, 7 })
        {
            var reference = Outcome(source, seed, limits: null);
            foreach (var (name, from, to, make) in sweeps)
            {
                string? completed = null;
                for (var n = from; n <= to; n++)
                {
                    var outcome = Outcome(source, seed, make(n));
                    if (outcome == "limit")
                    {
                        Assert.True(completed is null, $"{name}={n} seed {seed}: a larger limit stopped a run a smaller one completed as {completed}\n{source}");
                        continue;
                    }

                    Assert.True(reference == outcome, $"{name}={n} seed {seed}: completed as {outcome}, but the unconfigured run is {reference}\n{source}");
                    completed = outcome;
                }
            }
        }
    }

    private static string Outcome(string source, long seed, EvaluationLimits? limits)
        => KatLangEngine.Run(source, new RunOptions { RandomSeed = seed, EvaluationLimits = limits }) switch
        {
            RunResult.Success success => "ok " + success.ToDisplayString().ReplaceLineEndings("|"),
            RunResult.EvalFailure failure when failure.Errors.Count == 1 && failure.Errors[0].IsResourceLimit => "limit",
            RunResult.EvalFailure failure => "err " + string.Join("+", failure.Errors.Select(static error => error.Code)),
            var other => "unexpected " + other,
        };
}
