using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Rendering;
using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

/// <summary>
/// AT-MOST-ONCE ARGUMENT VALUE EVALUATION (Q-01 / PV-04, September 2026).
///
/// <para>Within one call, a written argument slot is evaluated at most once for its value.
/// If that evaluation succeeds, that is its value; if it fails, that is its failure.
/// Reading the bound parameter never causes the argument expression to execute again:
/// argument evaluation uses the proper semantic route once (a named property through its
/// ordinary property access), and every parameter read — a value position, a builtin
/// value slot, the <c>.string</c> receiver, a native wrapper's argument, a forwarding
/// call — reuses that outcome. The algorithm channel a slot may also carry stays available
/// for invocation (<c>f(x)</c>, an invoking builtin slot), structural member access, and
/// forwarding; it is never a second route to the parameter's value.</para>
///
/// <para>Before the rule, a slot whose value evaluation failed kept only its algorithm
/// channel, and every value read re-ran the raw argument algorithm outside the property
/// cache: a failing argument ran twice (<c>trace(1)</c> logged twice), a seeded failure
/// healed into a value, and one parameter yielded two different values in one activation
/// (<c>Pair(B)</c> gave <c>(3, 5)</c>). The evidence here is deterministic host
/// instrumentation (<c>tick</c> counts its invocations, <c>trace</c> logs its argument)
/// and seeded random streams, on every execution route: the public sync and async
/// engines, the async twin (an async host operation present), the generic and optimized
/// evaluators, and the forced async twin. Lean: <c>AlgBinding.valueFailure?</c>,
/// <c>slotAlgorithmBinding</c>, <c>CoreTests/ArgumentValueOutcome.lean</c>, and the laws
/// <c>failed_slot_binds_its_failure_beside_the_algorithm_channel</c> /
/// <c>valued_slot_binds_its_value_and_no_failure</c>.</para>
/// </summary>
public class ArgumentValueOutcomeTests
{
    // ── Execution routes ─────────────────────────────────────────────────────────────

    public enum Route
    {
        /// <summary>The oracle: <see cref="KatLangEngine.Run"/>.</summary>
        EngineSync,

        /// <summary><see cref="KatLangEngine.RunAsync"/> with synchronous host operations.</summary>
        EngineAsync,

        /// <summary><see cref="KatLangEngine.RunAsync"/> with an async host operation present: the async twin.</summary>
        EngineAsyncTwin,

        /// <summary>The generic evaluator (optimizations disabled).</summary>
        Generic,

        /// <summary>The optimized evaluator.</summary>
        Optimized,

        /// <summary>The async twin forced by an async-capable property cache.</summary>
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
    }

    private static HostOperations OperationsFor(HostLog log, bool withAsyncOperation)
    {
        var tick = withAsyncOperation
            ? HostOperation.CreateAsync("tick", async (_, _) => { await Task.Yield(); return log.Tick(); })
            : HostOperation.Create("tick", (_, _) => log.Tick());
        var trace = withAsyncOperation
            ? HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return log.Trace(args[0]); }, "x")
            : HostOperation.Create("trace", (args, _) => log.Trace(args[0]), "x");
        return withAsyncOperation
            ? HostOperations.Create(tick, trace, HostOperation.CreateAsync("pause", async (_, _) =>
            {
                await Task.Yield();
                return new Result.Atom((Decimal128)0);
            }))
            : HostOperations.Create(tick, trace);
    }

    private sealed record Observation(string Kind, string? Value, IReadOnlyList<string> Codes, IReadOnlyList<string> HostCalls)
    {
        public IReadOnlyList<string> ErrorDetails { get; init; } = [];
        public override string ToString()
            => $"{Kind} {Value} codes=[{string.Join(",", Codes)}] host=[{string.Join(",", HostCalls)}] details=[{string.Join(";", ErrorDetails)}]";
    }

    private static async Task<Observation> ObserveAsync(Route route, string source, long? seed, EvaluationLimits? limits = null)
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

        return result.IsError
            ? new Observation("err", null, [KatLangError.FromEvalError(result.Error).Code.ToString()], [.. log.Calls])
                { ErrorDetails = [DescribeError(KatLangError.FromEvalError(result.Error))] }
            : new Observation("ok", Neutral(result.Value.Value), [], [.. log.Calls]);
    }

    private static Observation FromRunResult(RunResult result, HostLog log) => result switch
    {
        RunResult.Success success => new("ok", Neutral(success.Value), [], [.. log.Calls]),
        RunResult.EvalFailure failure => new("err", null, [.. failure.Errors.Select(static error => error.Code.ToString())], [.. log.Calls])
            { ErrorDetails = [.. failure.Errors.Select(DescribeError)] },
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
    /// synchronous engine — value, error codes, and the exact host-call log (hence the
    /// exact number of argument evaluations). Returns the oracle.
    /// </summary>
    private static async Task<Observation> OnEveryRouteAsync(string source, long? seed = null, EvaluationLimits? limits = null)
    {
        // Completed async runs can resume inline at the bottom of the previous
        // evaluator's completion chain. Each route starts on a fresh task stack so
        // native stack headroom, rather than a harness continuation, is compared.
        var oracle = await Task.Run(() => ObserveAsync(Route.EngineSync, source, seed, limits));
        foreach (var route in Routes.Skip(1))
        {
            var observation = await Task.Run(() => ObserveAsync(route, source, seed, limits));
            Assert.True(
                oracle.Kind == observation.Kind
                    && oracle.Value == observation.Value
                    && oracle.Codes.SequenceEqual(observation.Codes)
                    && oracle.ErrorDetails.SequenceEqual(observation.ErrorDetails)
                    && oracle.HostCalls.SequenceEqual(observation.HostCalls),
                $"{route}: expected {oracle}, got {observation}\nsource:\n{source}");
        }

        return oracle;
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

    /// <summary>The display rows of a seeded engine run (the reference random stream).</summary>
    private static string[] Rows(string source, long seed)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, new RunOptions { RandomSeed = seed }))
            .ToDisplayString()
            .Split('\n')
            .Select(static row => row.Trim())
            .ToArray();

    private const string Draw = "randomInt(1, 1000000)";

    // ── 1. The canonical examples ────────────────────────────────────────────────────

    /// <summary>
    /// Example 1: the one permitted evaluation of <c>F</c>'s argument slot raises the
    /// division by zero; reading <c>v</c> reuses that failure and never runs <c>Bad</c> again.
    /// </summary>
    [Fact]
    public async Task FailingArgument_IsEvaluatedOnce_ItsFailureIsTheParameterValue()
        => AssertFails(
            await OnEveryRouteAsync("Bad = trace(1) / 0\nF(v) = v\nF(Bad)"),
            KatLangErrorCode.DivisionByZero,
            "trace(1)");

    /// <summary>Several reads of the failed parameter still mean one evaluation.</summary>
    [Fact]
    public async Task RepeatedReadsOfAFailedParameter_ReuseTheOneFailure()
    {
        AssertFails(
            await OnEveryRouteAsync("Bad = trace(1) / 0\nPair(x) = x, x\nPair(Bad)"),
            KatLangErrorCode.DivisionByZero,
            "trace(1)");
        AssertFails(
            await OnEveryRouteAsync("Bad = trace(1) / 0\nThree(x) = x + x + x\nThree(Bad)"),
            KatLangErrorCode.DivisionByZero,
            "trace(1)");
    }

    /// <summary>
    /// Example 2: one parameter never acquires several values. The slot's first evaluation of
    /// <c>B</c> fails (<c>tick#1</c>), so every read of <c>x</c> in that activation is that
    /// failure: the former <c>(3, 5)</c> — two retries producing two different successes — is
    /// impossible, and the call fails after ONE host call.
    /// </summary>
    [Fact]
    public async Task StatefulFailure_IsRetained_OneParameterNeverHasTwoValues()
        => AssertFails(
            await OnEveryRouteAsync("B = if(tick() < 2, 1 / 0, tick())\nPair(x) = x, x\nPair(B), B"),
            KatLangErrorCode.DivisionByZero,
            "tick#1");

    /// <summary>
    /// Reading the PROPERTY <c>B</c> inside the callee is a separate, ordinary property
    /// demand: a failure is never cached, so that read evaluates <c>B</c> afresh (and caches
    /// its first success). The PARAMETER <c>x</c> still reports its own slot's failure.
    /// </summary>
    [Fact]
    public async Task PropertyReadBesideTheParameter_FollowsPropertySemantics_TheParameterKeepsItsFailure()
        => AssertFails(
            await OnEveryRouteAsync("B = if(tick() < 2, 1 / 0, tick())\nPair(x) = B, x, B, x\nPair(B), B"),
            KatLangErrorCode.DivisionByZero,
            "tick#1");

    /// <summary>
    /// Example 3: a failure cannot heal. Seed 4's stream starts <c>2, 0</c>: the first
    /// selection is out of range and the next would select <c>10</c>. The argument slot draws
    /// ONCE and fails with <c>BadIndex</c>; reading <c>v</c> reports that failure and never
    /// consumes the second draw.
    /// </summary>
    [Fact]
    public async Task SeededFailure_CannotHeal_TheSelectorIsDrawnOnce()
    {
        Assert.Equal(["2", "0"], Rows("randomInt(0, 3), randomInt(0, 3)", seed: 4));

        const string pick = "Pick = [10, 20]:(trace(randomInt(0, 3)))";
        AssertFails(await OnEveryRouteAsync($"{pick}\nF(v) = v\nF(Pick)", seed: 4), KatLangErrorCode.BadIndex, "trace(2)");
        AssertFails(await OnEveryRouteAsync($"{pick}\nPair(v) = v, v\nPair(Pick)", seed: 4), KatLangErrorCode.BadIndex, "trace(2)");
        // The property alone agrees: one draw, the same failure.
        AssertFails(await OnEveryRouteAsync($"{pick}\nPick", seed: 4), KatLangErrorCode.BadIndex, "trace(2)");
        // A written block argument (also carrying an algorithm channel) behaves the same.
        AssertFails(
            await OnEveryRouteAsync("F(v) = v\nF({ [10, 20]:(trace(randomInt(0, 3))) })", seed: 4),
            KatLangErrorCode.BadIndex,
            "trace(2)");
    }

    /// <summary>
    /// Example 4: a successful argument value is equally stable. Every read of <c>x</c> sees the
    /// one draw, and a trailing independent draw proves the exact stream position: no read drew
    /// a hidden second value.
    /// </summary>
    [Theory]
    [InlineData(0L)]
    [InlineData(4L)]
    [InlineData(7L)]
    [InlineData(20260928L)]
    public async Task SuccessfulStatefulArgument_IsEvaluatedOnce_EveryReadSeesTheSameValue(long seed)
    {
        var r = Rows($"{Draw}, {Draw}", seed);

        AssertOk(
            await OnEveryRouteAsync($"A = trace({Draw})\nPair(x) = x, x\nPair(A), {Draw}", seed),
            $"S[S[{r[0]}, {r[0]}], {r[1]}]",
            $"trace({r[0]})");
        // A written block and a plain call argument: one draw each way.
        AssertOk(
            await OnEveryRouteAsync($"Pair(x) = x, x\nPair({{ trace({Draw}) }}), {Draw}", seed),
            $"S[S[{r[0]}, {r[0]}], {r[1]}]",
            $"trace({r[0]})");
        AssertOk(
            await OnEveryRouteAsync($"Pair(x) = x, x\nPair(trace({Draw})), {Draw}", seed),
            $"S[S[{r[0]}, {r[0]}], {r[1]}]",
            $"trace({r[0]})");
    }

    // ── 2. Named property arguments ──────────────────────────────────────────────────

    /// <summary>
    /// The one permitted evaluation of a named property argument is the ordinary property
    /// access: the slot reads the entry the root's read stored (one trace for four uses), and
    /// the parameter never re-runs the property's raw algorithm.
    /// </summary>
    [Theory]
    [InlineData(1L)]
    [InlineData(42L)]
    public async Task NamedPropertyArgument_IsReadThroughTheOrdinaryPropertyAccess(long seed)
    {
        var r = Rows(Draw, seed);
        AssertOk(
            await OnEveryRouteAsync($"P = trace({Draw})\nPair(x) = x, x\nP, Pair(P), P", seed),
            $"S[{r[0]}, S[{r[0]}, {r[0]}], {r[0]}]",
            $"trace({r[0]})");
        // The argument slot stores the entry the later root read reuses.
        AssertOk(
            await OnEveryRouteAsync($"P = trace({Draw})\nPair(x) = x, x\nPair(P), P", seed),
            $"S[S[{r[0]}, {r[0]}], {r[0]}]",
            $"trace({r[0]})");
    }

    /// <summary>
    /// The sticky failure belongs to the argument SLOT of one call activation, never to the
    /// property: a failed evaluation is not cached (PROP-09), so a later, separate demand of
    /// <c>B</c> — the root row, or another slot — is an ordinary property demand that
    /// evaluates afresh and caches its first success.
    /// </summary>
    [Fact]
    public async Task UndemandedPropertySlots_DoNotPrimeOrFailThePropertyCache()
    {
        const string flaky = "B = if(tick() < 2, 1 / 0, tick())";
        AssertFails(await OnEveryRouteAsync($"{flaky}\nIgnore(x) = 0\nIgnore(B), B, B"), KatLangErrorCode.DivisionByZero, "tick#1");
        AssertFails(await OnEveryRouteAsync($"{flaky}\nSecond(x, y) = y\nSecond(B, B)"), KatLangErrorCode.DivisionByZero, "tick#1");
        AssertFails(await OnEveryRouteAsync($"{flaky}\nBoth(x, y) = y, x\nBoth(B, B)"), KatLangErrorCode.DivisionByZero, "tick#1");
    }

    /// <summary>
    /// A local-only property (its value reads its owner's parameter) keeps one entry per
    /// owner activation: each activation's slot reads it once, and a failed slot of one
    /// activation never poisons the property's later demands.
    /// </summary>
    [Fact]
    public async Task OwnerDependentProperty_SlotOutcomeIsPerActivation()
    {
        AssertOk(
            await OnEveryRouteAsync("Pair(x) = x, x\nOuter(n) = {\n    L = trace(n * 10)\n    Pair(L), L\n}\nOuter(1), Outer(2)"),
            "S[S[S[10, 10], 10], S[S[20, 20], 20]]",
            "trace(10)", "trace(20)");
        AssertFails(await OnEveryRouteAsync(
            "Pair(x) = x, x\nIgnore(x) = 0\nOuter(n) = {\n    L = if(tick() < 2, 1 / 0, n * 10)\n    Ignore(L), L, Pair(L)\n}\nOuter(1)"),
            KatLangErrorCode.DivisionByZero, "tick#1");
    }

    /// <summary>
    /// Spelling independence: a structurally navigated member (<c>Box.V</c>), the same member
    /// through <c>open</c> (<c>V</c>), and an alias all establish the same slot outcome with
    /// one evaluation — before the rule, the dotted spelling read the cache while the opened
    /// one re-ran the body.
    /// </summary>
    [Fact]
    public async Task EverySpellingOfOneProperty_EstablishesTheSameSlotOutcome()
    {
        const string box = "Box = {\n    public V = if(tick() < 2, 1 / 0, tick())\n}\nPair(x) = x, x";
        AssertFails(await OnEveryRouteAsync($"{box}\nPair(Box.V), Box.V"), KatLangErrorCode.DivisionByZero, "tick#1");
        AssertFails(await OnEveryRouteAsync($"open Box\n{box}\nPair(V), V"), KatLangErrorCode.DivisionByZero, "tick#1");
        AssertFails(await OnEveryRouteAsync($"{box}\nAlias = Box.V\nPair(Alias), Alias"), KatLangErrorCode.DivisionByZero, "tick#1");
    }

    // ── 3. Explicit calls stay fresh; the algorithm channel stays usable ─────────────

    /// <summary>
    /// <c>P</c> and <c>P()</c> keep their distinction: an explicit invocation of the
    /// forwarded callable runs the body afresh and never reads or replaces the entry, while a
    /// VALUE read of the parameter is P's ordinary cached property read (NEED-10) — passing P
    /// itself performs no access.
    /// </summary>
    [Fact]
    public async Task ExplicitInvocationOfTheParameter_StaysAFreshCall()
    {
        AssertOk(
            await OnEveryRouteAsync("P = tick()\nCall0(f) = f()\nP, Call0(P), P"),
            "S[1, 2, 1]",
            "tick#1", "tick#2");
        AssertOk(
            await OnEveryRouteAsync("P = tick()\nTwice0(f) = f(), f(), f\nTwice0(P)"),
            "S[1, 2, 3]",
            "tick#1", "tick#2", "tick#3");
    }

    /// <summary>
    /// INVOKING the callable is not demanding the slot's VALUE (NEED-06): <c>Call0(B)</c> never
    /// reads B through the slot; its explicit call runs B's body afresh, here at its first tick,
    /// which fails. A later VALUE read of the same parameter demands the cell once and reports
    /// that outcome; an invocation never reads, repairs or replaces it.
    /// </summary>
    [Fact]
    public async Task CallableInvocation_DoesNotPredemandItsCellValue()
    {
        const string flaky = "B = if(tick() < 2, 1 / 0, tick())";
        AssertFails(await OnEveryRouteAsync($"{flaky}\nCall0(f) = f()\nCall0(B)"), KatLangErrorCode.DivisionByZero, "tick#1");
        AssertFails(await OnEveryRouteAsync($"{flaky}\nThenRead(f) = f(), f\nThenRead(B)"), KatLangErrorCode.DivisionByZero, "tick#1");
    }

    public static TheoryData<string, string> HigherOrderPrograms() => new()
    {
        { "Inc(y) = y + 1\nApply(f, x) = f(x)\nApply(Inc, 5)", "6" },
        { "Inc(y) = y + 1\nApply(f, x) = f(x)\nFwd(g, x) = Apply(g, x)\nFwd(Inc, 5)", "6" },
        { "Inc(y) = y + 1\nMapWith(f, xs) = map(xs, f)\nMapWith(Inc, [1, 2])", "L[2, 3]" },
        { "Big(y) = y > 1\nKeepWith(f, xs) = filter(xs, f)\nKeepWith(Big, [1, 2, 3])", "L[2, 3]" },
        { "Add(e, a) = e + a\nFold(f, xs) = reduce(xs, f, 0)\nFold(Add, [1, 2, 3])", "6" },
        { "Step(s) = s + 1\nLoop(f) = repeat(f, 3, 0)\nLoop(Step)", "3" },
        { "Box = { public X = 5 }\nMember(o) = o.X\nMember(Box)", "5" },
        { "Twice = f(f(x))\nSquare = n * n\nTwice(Square, 3)", "81" },
        { "Apply(f, x) = f(x)\nApply({n + 1}, 4)", "5" },
        { "Twice(x, f) = f(f(x))\n5.Twice{n * 2}", "20" },
        { "Apply(f, x) = f(x)\nApply(sqrt, 16)", "4" },
        { "Only(*xs) = xs.count\nApply(f, xs) = map(xs, f)\nApply(Only, [10, 20])", "L[1, 1]" },
    };

    /// <summary>Callable arguments keep working through the algorithm channel.</summary>
    [Theory]
    [MemberData(nameof(HigherOrderPrograms))]
    public async Task CallableArguments_KeepTheirAlgorithmChannel(string source, string expected)
        => AssertOk(await OnEveryRouteAsync(source), expected);

    /// <summary>
    /// Reading a callable parameter for its VALUE reports the failure its slot established —
    /// the zero-argument demand of the written argument — rather than re-judging the
    /// algorithm channel: a parameterized property is its arity error, and a written brace
    /// algorithm with an unsupplied parameter is <c>UnresolvedImplicitParams</c>, exactly as the
    /// argument expression alone reports.
    /// </summary>
    [Fact]
    public async Task ValueReadOfACallableParameter_ReportsTheSlotsOwnFailure()
    {
        AssertFails(
            await OnEveryRouteAsync("Inc(y) = y + 1\nPlus(f, x) = f + x\nPlus(Inc, 5)"),
            KatLangErrorCode.ArityMismatch);
        AssertFails(
            await OnEveryRouteAsync("Plus(f, x) = f + x\nPlus({x + 1}, 5)"),
            KatLangErrorCode.UnresolvedImplicitParams);
        // The same failure when the parameter is the whole body.
        AssertFails(
            await OnEveryRouteAsync("Only(g) = g\nOnly({x + 1})"),
            KatLangErrorCode.UnresolvedImplicitParams);

        // A clause family cannot be read as a value: the slot's failure names the family the
        // caller wrote, never the parameter it was read through (Lean
        // `conditionalHigherOrderThunkReferenceFails`).
        const string family = "F(0) = 1\nF(n) = n\nApply(f) = f\nApply(F)";
        AssertFails(await OnEveryRouteAsync(family), KatLangErrorCode.NoMatchingBranch);
        var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(family).Root));
        Assert.True(result.IsError);
        var innermost = result.Error;
        while (innermost is EvalError.WithContext context)
            innermost = context.Inner;
        Assert.Equal("F", Assert.IsType<EvalError.NoMatchingBranch>(innermost).AlgorithmName);
    }

    // ── 4. Every binding shape and consumer: one evaluation of the failed slot ───────

    public static TheoryData<string> FailedSlotConsumers() => new()
    {
        // Fixed parameters, direct and repeated.
        "F(v) = v\nF(Bad)",
        "F(v) = v + 1, v * 2\nF(Bad)",
        // Forwarded through further calls, through a native wrapper, and dotted.
        "One(x) = x\nFwd(w) = One(w), One(w)\nFwd(Bad)",
        "G(v) = abs(v) + sqrt(v)\nG(Bad)",
        "G(v) = Math.Abs(v) + Math.Sqrt(v)\nG(Bad)",
        "F(v) = v, v\nBad.F",
        "F(v) = v, v\nAlias = F\nAlias(Bad)",
        // Builtin value slots and the `.string` receiver reading the parameter.
        "G(v) = sum(v), sum(v)\nG(Bad)",
        "G(v) = if(true, v, 0), v\nG(Bad)",
        "G(v) = v.string, v\nG(Bad)",
        "Add(e, a) = e + a\nG(v) = reduce([1], Add, v)\nG(Bad)",
        "Keep(s) = s\nG(v) = repeat(Keep, 1, v)\nG(Bad)",
        "G(v) = range(v, 3)\nG(Bad)",
        "G(v) = v.filter({x > 0}).count\nG(Bad)",
        "G(v) = [v, v]\nG(Bad)",
        "G(v) = v:0\nG(Bad)",
        "G(v) = (v), (v)\nG(Bad)",
        "G(v) = v < v\nG(Bad)",
        "Coll(*xs) = xs\nG(v) = Coll(v*)\nG(Bad)",
        // A captured parameter read by a nested property, and a loop body.
        "G(v) = {\n    Inner = v + 1\n    Inner, Inner\n}\nG(Bad)",
        "G(v) = repeat({s + v}, 3, 0)\nG(Bad)",
        // Collecting, mixed, nested-pattern, and clause-family callees surface the failure
        // at binding — still one evaluation.
        "Coll(*xs) = xs, xs\nColl(Bad)",
        "M(a, *rest, z) = a, a\nM(Bad, 1, 2)",
        "P((a, b)) = a + b\nP(Bad)",
        "Fam(0) = 0\nFam(n) = n + n\nFam(Bad)",
    };

    [Theory]
    [MemberData(nameof(FailedSlotConsumers))]
    public async Task EveryConsumerOfAFailedSlot_ObservesItsOneFailure(string program)
        => AssertFails(
            await OnEveryRouteAsync("Bad = trace(1) / 0\n" + program),
            KatLangErrorCode.DivisionByZero,
            "trace(1)");

    // The established failure need not agree with rechecking the algorithm's signature.
    // A brace argument records UnresolvedImplicitParams; reclassifying its callable at a
    // builtin boundary incorrectly changes that outcome to ArityMismatch or BadArity.
    [Theory]
    [InlineData("v")]
    [InlineData("sum(v)")]
    [InlineData("abs(v)")]
    [InlineData("Math.Abs(v)")]
    [InlineData("trace(v)")]
    [InlineData("count(v)")]
    [InlineData("first(v)")]
    [InlineData("last(v)")]
    [InlineData("take([1], v)")]
    [InlineData("range(v, 3)")]
    [InlineData("if(true, v, 0)")]
    [InlineData("repeat({s + 1}, v, 0)")]
    [InlineData("repeat({s + 1}, 1, v)")]
    [InlineData("while({false}, {s + 1}, v)")]
    [InlineData("while({s + 1, false}, v)")]
    [InlineData("reduce([1], {e + a}, v)")]
    [InlineData("v.string")]
    [InlineData("v.filter({x > 0}).count")]
    public async Task FailedCallableSlot_KeepsItsOriginalErrorAtEveryValueBoundary(string consumer)
        => AssertFails(
            await OnEveryRouteAsync($"G(v) = {consumer}\nG({{x + 1}})"),
            consumer == "while({false}, {s + 1}, v)" ? KatLangErrorCode.ArityMismatch : KatLangErrorCode.UnresolvedImplicitParams);

    [Fact]
    public async Task DeepForwarding_AndManyReads_KeepOneOutcome()
    {
        var chain = string.Join('\n', Enumerable.Range(0, 32).Select(i => $"F{i}(v) = F{i + 1}(v)"));
        var reads = string.Join(", ", Enumerable.Repeat("v", 64));
        var definitions = $"{chain}\nF32(v) = {reads}";
        // The success control also establishes sufficient stack headroom for this depth.
        AssertOk(await OnEveryRouteAsync($"{definitions}\nF0(tick())"),
            "S[" + string.Join(", ", Enumerable.Repeat("1", 64)) + "]", "tick#1");
        AssertFails(await OnEveryRouteAsync($"{definitions}\nB = if(tick() < 2, 1 / 0, tick())\nF0(B)"),
            KatLangErrorCode.DivisionByZero, "tick#1");
    }

    [Fact]
    public async Task ExplicitCallSlot_AndForwardedInvocation_DoNotReplaceTheValueOutcome()
    {
        AssertOk(await OnEveryRouteAsync("P = tick()\nFour(v) = v, v, v, v\nP, Four(P()), P, P()"),
            "S[1, S[2, 2, 2, 2], 1, 3]", "tick#1", "tick#2", "tick#3");
        AssertOk(await OnEveryRouteAsync("P = tick()\nUse(f) = f, f(), f, f()\nFwd(g) = Use(g)\nFwd(P)"),
            "S[1, 2, 1, 3]", "tick#1", "tick#2", "tick#3");
        AssertFails(await OnEveryRouteAsync("B = if(tick() < 2, 1 / 0, tick())\nUse(f) = f, f()\nFwd(g) = Use(g)\nFwd(B)"),
            KatLangErrorCode.DivisionByZero, "tick#1");
        AssertFails(await OnEveryRouteAsync("B = if(tick() < 2, 1 / 0, tick())\nUse(f) = f(), f\nFwd(g) = Use(g)\nFwd(B)"),
            KatLangErrorCode.DivisionByZero, "tick#1");
    }

    [Fact]
    public async Task CallbackInvocations_LeaveTheCapturedFailureIntact()
    {
        const string definitions = "Step(*xs) = if(xs.count == 0, trace(0) / 0, trace(xs.sum))\n";
        AssertOk(await OnEveryRouteAsync(definitions + "Use(f) = map([1, 2], f)\nUse(Step)"),
            "L[1, 2]", "trace(1)", "trace(2)");
        AssertFails(await OnEveryRouteAsync(definitions + "Use(f) = map([1, 2], f), f\nUse(Step)"),
            KatLangErrorCode.DivisionByZero, "trace(1)", "trace(2)", "trace(0)");
    }

    [Fact]
    public async Task OpenedStructuralAndAliasArguments_ShareTheSuccessfulPropertyEntry()
        => AssertOk(await OnEveryRouteAsync(
            "open Box\nBox = {public V = tick()}\nAlias = Box.V\nPair(x) = x, x\nPair(Box.V), Pair(V), Pair(Alias), Box.V"),
            "S[S[1, 1], S[1, 1], S[1, 1], 1]", "tick#1");

    [Theory]
    [InlineData("sum(v)")]
    [InlineData("if(true, v, 0)")]
    [InlineData("reduce([1], {e + a}, v)")]
    [InlineData("v.string")]
    public async Task BuiltinParameterFailure_KeepsTheOriginalFamilyPayload(string consumer)
    {
        var observed = await OnEveryRouteAsync($"Fam(0) = 1\nFam(n) = n\nG(v) = {consumer}\nG(Fam)");
        AssertFails(observed, KatLangErrorCode.NoMatchingBranch);
        Assert.Contains("Fam", Assert.Single(observed.ErrorDetails));
    }

    [Theory]
    [InlineData("sum(v)")]
    [InlineData("count(v)")]
    [InlineData("if(true, v, 0)")]
    [InlineData("v.string")]
    [InlineData("trace(v)")]
    public async Task ResourceFailure_IsNotReplayedAfterTheBudgetUnwinds(string consumer)
        => AssertFails(await OnEveryRouteAsync(
            $"Deep = Deep\nBad = {{trace(1)\nDeep}}\nG(v) = {consumer}\nG(Bad)",
            limits: new EvaluationLimits { MaxDepth = 8 }),
            KatLangErrorCode.EvaluationDepthExceeded, "trace(1)");

    [Fact]
    public async Task UndemandedBuiltinAndAlgorithmOnlySlots_StayLazy()
    {
        AssertOk(await OnEveryRouteAsync("if(false, trace(1), 7)"), "7");
        AssertOk(await OnEveryRouteAsync("Step(s) = trace(s + 1)\nrepeat(Step, 0, 7)"), "7");
        AssertOk(await OnEveryRouteAsync("Step(s) = trace(s + 1)\nFwd(f) = repeat(f, 0, 7)\nFwd(Step)"), "7");
        AssertOk(await OnEveryRouteAsync("Step(s) = trace(s + 1)\nIgnore(f) = 7\nIgnore(Step)"), "7");
    }

    [Fact]
    public async Task FusedPredicateCapture_ReadsTheSlotFailure_WithoutReplayingIt()
    {
        const string source = "Bad = trace(1) / 0\nG(v) = range(1, 3).filter({x > v}).count\nG(Bad)";
        AssertFails(await OnEveryRouteAsync(source), KatLangErrorCode.DivisionByZero, "trace(1)");
        var log = new HostLog();
        var operations = OperationsFor(log, withAsyncOperation: false);
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
        var diagnostics = new SequencePipelineDiagnostics();
        var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root),
            hostOperations: operations, sequenceDiagnostics: diagnostics);
        Assert.True(result.IsError);
        Assert.Equal(KatLangErrorCode.DivisionByZero, KatLangError.FromEvalError(result.Error).Code);
        Assert.Equal(["trace(1)"], log.Calls);
        Assert.Equal(1, diagnostics.GetSnapshot().FilterCountFusionHits);
        Assert.Equal(1, diagnostics.GetSnapshot().FilterCountPredicateCalls);
    }

    /// <summary>
    /// A repeated name never keeps a value another contribution supplies in place of a failed
    /// one (REPEATED NAMES ARE CONSTRAINTS, NOT MERGES, Q-05): every occurrence needs its own
    /// value, so the failed slot's recorded failure propagates — after exactly one evaluation,
    /// never a second one to re-check it — in either argument order. (Before Q-05 the other
    /// occurrence's value stood in: <c>Q(Bad, 7)</c> was <c>7</c>.) The full matrix is
    /// <see cref="RepeatedNameConstraintTests"/>.
    /// </summary>
    [Fact]
    public async Task RepeatedNameBesideAFailedSlot_PropagatesItsFailure_EvaluatedOnce()
    {
        AssertFails(
            await OnEveryRouteAsync("Bad = trace(1) / 0\nQ(x, x) = x\nQ(Bad, 7)"),
            KatLangErrorCode.DivisionByZero,
            "trace(1)");
        AssertFails(
            await OnEveryRouteAsync("Bad = trace(1) / 0\nQ(x, x) = x, x.string\nQ(7, Bad)"),
            KatLangErrorCode.DivisionByZero,
            "trace(1)");
    }

    /// <summary>
    /// Laziness is preserved: an argument whose value is never demanded is not an error, and
    /// it is never evaluated (Model C, NEED-01).
    /// </summary>
    [Fact]
    public async Task UndemandedFailedSlot_IsNotEvaluated()
    {
        AssertOk(await OnEveryRouteAsync("Bad = trace(1) / 0\nFirst(x, y) = x\nFirst(1, Bad)"), "1");
        AssertOk(await OnEveryRouteAsync("Bad = trace(1) / 0\nIgnore(f) = 0\nIgnore(Bad), Ignore(Bad)"), "S[0, 0]");
    }

    /// <summary>
    /// A resource-limit failure of a slot is terminal for the run at the slot's first VALUE
    /// demand (RESOURCE LIMITS ARE TERMINAL, Q-02 / PV-06; NEED-09): the demanded cell keeps the
    /// limit as its terminal completion, so a callee that reads the parameter and one that
    /// forwards it to a reader fail alike, while an argument nothing demands never runs. Only
    /// ORDINARY failures are the latent, once-established outcomes of this suite.
    /// (The synchronous routes agree on the depth verdict; the async twin's host-stack
    /// headroom is a separate, documented difference, PV-07.)
    /// </summary>
    [Fact]
    public void ResourceLimitFailureOfASlot_IsTerminalAtItsFirstValueDemand()
    {
        foreach (var source in new[]
        {
            "Deep = Deep\nPair(x) = x, x\nPair(Deep)",
            "Deep = Deep\nS(v) = sum(v), v\nS(Deep)",
            // Forwarded, then demanded by G. (Model C changed this row from the unused
            // `G(w) = 5`, which now never runs Deep; before Q-02 that unused form retained and
            // dropped the limit and SUCCEEDED with 5.)
            "Deep = Deep\nG(w) = w + 5\nF(v) = G(v)\nF(Deep)",
        })
        {
            var result = KatLangEngine.Run(source);
            var failure = Assert.IsType<RunResult.EvalFailure>(result);
            Assert.Equal(KatLangErrorCode.EvaluationDepthExceeded, Assert.Single(failure.Errors).Code);
        }

        // The ORDINARY-failure control: an unused one still is not an error.
        Assert.Equal("5", Assert.IsType<RunResult.Success>(KatLangEngine.Run("Bad = 1 / 0\nG(w) = 5\nF(v) = G(v)\nF(Bad)")).ToDisplayString());
    }

    // ── 5. The laws, as metamorphic relations over argument expressions and readers ──

    /// <summary>Argument expressions: failing, failing-then-healing, random, and host-backed, in every written shape.</summary>
    private static readonly string[] ArgumentExpressions =
    [
        "Bad",
        "{ trace(1) / 0 }",
        "Flaky",
        "Box.V",
        "Pick",
        "Roll",
        "Box.R",
        $"{{ trace({Draw}) }}",
        $"trace({Draw})",
        "Tock",
    ];

    private const string LawDefinitions = """
        Bad = trace(1) / 0
        Flaky = if(tick() < 2, 1 / 0, tick())
        Pick = [10, 20]:(trace(randomInt(0, 3)))
        Roll = trace(randomInt(1, 1000000))
        Tock = tick() * 100
        Box = {
            public V = if(tick() < 2, 1 / 0, tick())
            public R = trace(randomInt(1, 1000000))
        }
        One(x) = x
        Two(x) = x, x
        Three(x) = x, x, x
        Sum2(x) = x + x
        Via(x) = One(x), One(x)
        Str(x) = x.string, x.string
        Builtin(x) = sum(x) + sum(x)
        Cond(x) = if(true, x, 0), x
        Local(x) = {
            L = x
            L, x
        }
        Coll2(*xs) = xs, xs
        Eq(x) = x == x
        """;

    /// <summary>Readers that read their parameter more than once, each with its expected success shape.</summary>
    private static readonly (string Reader, Func<string, string> Expected)[] Readers =
    [
        ("Two", v => $"S[{v}, {v}]"),
        ("Three", v => $"S[{v}, {v}, {v}]"),
        ("Via", v => $"S[{v}, {v}]"),
        ("Str", v => $"S['{v}', '{v}']"),
        ("Cond", v => $"S[{v}, {v}]"),
        ("Local", v => $"S[{v}, {v}]"),
        ("Coll2", v => $"S[L[{v}], L[{v}]]"),
        ("Eq", _ => "true"),
    ];

    public static TheoryData<string, long> LawCases()
    {
        var data = new TheoryData<string, long>();
        foreach (var argument in ArgumentExpressions)
        {
            foreach (var seed in new[] { 4L, 5L, 7L })
                data.Add(argument, seed);
        }

        return data;
    }

    /// <summary>
    /// For every argument expression <c>E</c> and every reader that reads its parameter
    /// several times:
    /// <list type="bullet">
    /// <item>LAW D (source replay count ≤ 1) and LAW A (duplication is observationally inert):
    /// the host log of <c>R(E)</c> equals that of <c>One(E)</c>, which equals that of
    /// evaluating <c>E</c> once on its own — reading the parameter again never re-runs
    /// the argument;</item>
    /// <item>LAW B (failure never becomes success): if <c>One(E)</c> fails, every <c>R(E)</c>
    /// fails with the same error;</item>
    /// <item>LAW C (a value never changes between reads): if <c>One(E)</c> succeeds with
    /// <c>v</c>, every read in <c>R(E)</c> sees <c>v</c>, and <c>x == x</c> holds;</item>
    /// </list>
    /// on every execution route.
    /// </summary>
    [Theory]
    [MemberData(nameof(LawCases))]
    public async Task ParameterReads_AreObservationallyInert(string argument, long seed)
    {
        var alone = await OnEveryRouteAsync($"{LawDefinitions}\n{argument}", seed);
        var one = await OnEveryRouteAsync($"{LawDefinitions}\nOne({argument})", seed);

        // The one permitted evaluation IS the argument's evaluation.
        Assert.Equal(alone.Kind, one.Kind);
        Assert.Equal(alone.Codes, one.Codes);
        Assert.Equal(alone.HostCalls, one.HostCalls);
        if (alone.Kind == "ok")
            Assert.Equal(alone.Value, one.Value);

        foreach (var (reader, expected) in Readers)
        {
            var many = await OnEveryRouteAsync($"{LawDefinitions}\n{reader}({argument})", seed);
            Assert.Equal(one.HostCalls, many.HostCalls);
            Assert.Equal(one.Kind, many.Kind);
            if (one.Kind == "err")
                Assert.Equal(one.Codes, many.Codes);
            else
                Assert.Equal(expected(one.Value!), many.Value);
        }

        // Arithmetic readers double the one value: `x + x` and `sum(x) + sum(x)` are 2v.
        foreach (var reader in new[] { "Sum2", "Builtin" })
        {
            var doubled = await OnEveryRouteAsync($"{LawDefinitions}\n{reader}({argument})", seed);
            Assert.Equal(one.HostCalls, doubled.HostCalls);
            Assert.Equal(one.Kind, doubled.Kind);
            if (one.Kind == "err")
            {
                Assert.Equal(one.Codes, doubled.Codes);
            }
            else
            {
                var twice = (decimal.Parse(one.Value!, System.Globalization.CultureInfo.InvariantCulture) * 2)
                    .ToString(System.Globalization.CultureInfo.InvariantCulture);
                Assert.Equal(twice, doubled.Value);
            }
        }
    }
}
