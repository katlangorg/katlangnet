using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Rendering;

namespace KatLang.Tests;

/// <summary>
/// IMPLICIT LIFTING FOLLOWS ZERO-ARGUMENT ACCEPTANCE (Q-03 / PV-03, decided September 28 2026).
///
/// <para>The rule, as the tutorial states it: if a callable works with no arguments, using its
/// name alone reads its cached value, even if it declares optional or collecting parameters; use
/// <c>A()</c> to evaluate it again and get a fresh value. Formally: when an ordinary call that
/// supplies ZERO arguments can bind a callable, a bare reference to it in value context is a
/// property-style value demand. The front end never rewrites it into a fresh forwarding call
/// merely because its signature declares parameters, so the demand follows the ordinary
/// zero-argument property cache in EVERY position. An explicit call — <c>A()</c> or
/// <c>A(args)</c> — stays fresh and never reads, replaces or populates the entry, and implicit
/// lifting and forwarding stay exactly as they were for a callable that REQUIRES supplied
/// arguments.</para>
///
/// <para>Before the decision the two halves disagreed. Implicit lifting asked "does the callable
/// declare any parameter?" while the zero-argument demand law and the cache asked "can a
/// zero-argument call bind it?". So a collecting-only callable was a cached value in neutral
/// positions but became the fresh call <c>Only(xs*)</c> in lifting positions — operator and
/// comparison operands, list elements, index targets, spread operands, strict Math arguments,
/// alias rows and block bodies — with <c>xs</c> lifted into the enclosing owner, which could only
/// forward an empty supply at the root. <c>Roll == Roll</c> was <c>false</c>,
/// <c>first(Pair)</c> and <c>Pair:0</c> read different draws, and a formula chain re-ran its base
/// 2^k times. Both halves now read ONE rule, <c>ParameterPattern.AcceptsZeroSuppliedSlots</c>
/// (<c>ImplicitArgumentResolver.RequiresSuppliedArguments</c> is its complement).</para>
///
/// <para>The evidence is deterministic host instrumentation (<c>tick</c> counts body executions)
/// and seeded random streams, on six execution routes: the public sync and async engines, the
/// async twin (an async host operation present), the generic and optimized evaluators, and the
/// forced async twin. Lean: <c>liftsBareValueReference</c>, the law
/// <c>bare_reference_lifts_iff_not_cacheable</c> (<c>KatLangArityLaws.lean</c>), and the guards in
/// <c>CoreTests/ValueDemand.lean</c>.</para>
/// </summary>
public class ZeroArgumentReferenceLiftingTests
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
    }

    private static HostOperations OperationsFor(HostLog log, bool withAsyncOperation)
        => withAsyncOperation
            ? HostOperations.Create(
                HostOperation.CreateAsync("tick", async (_, _) => { await Task.Yield(); return log.Tick(); }),
                HostOperation.CreateAsync("pause", async (_, _) =>
                {
                    await Task.Yield();
                    return new Result.Atom((Decimal128)0);
                }))
            : HostOperations.Create(HostOperation.Create("tick", (_, _) => log.Tick()));

    private sealed record Observation(string Kind, string? Value, IReadOnlyList<string> Codes, IReadOnlyList<string> HostCalls)
    {
        public override string ToString()
            => $"{Kind} {Value} codes=[{string.Join(",", Codes)}] host=[{string.Join(",", HostCalls)}]";
    }

    private static async Task<Observation> ObserveAsync(Route route, string source, long? seed)
    {
        var log = new HostLog();
        var options = new RunOptions
        {
            RandomSeed = seed,
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
                program, enableOptimizations: false, hostOperations: options.HostOperations, randomSeed: seed),
            Route.Optimized => Evaluator.RunCountedObserved(
                program, enableOptimizations: true, hostOperations: options.HostOperations, randomSeed: seed),
            Route.ForcedTwin => await Evaluator.RunCountedObservedAsync(
                program,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                hostOperations: options.HostOperations,
                randomSeed: seed),
            _ => throw new ArgumentOutOfRangeException(nameof(route), route, null),
        };

        return result.IsError
            ? new Observation("err", null, [KatLangError.FromEvalError(result.Error).Code.ToString()], [.. log.Calls])
            : new Observation("ok", Neutral(result.Value.Value), [], [.. log.Calls]);
    }

    private static Observation FromRunResult(RunResult result, HostLog log) => result switch
    {
        RunResult.Success success => new("ok", Neutral(success.Value), [], [.. log.Calls]),
        RunResult.EvalFailure failure => new("err", null, [.. failure.Errors.Select(static error => error.Code.ToString())], [.. log.Calls]),
        RunResult.ParseFailure failure => new("parse", null, [.. failure.Errors.Select(static error => error.Code.ToString())], [.. log.Calls]),
        RunResult.NoProgramOutput none => new("none", null, [none.Diagnostic.Code.ToString()], [.. log.Calls]),
    };

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
    /// synchronous engine — value, error codes, and the exact host-call log (hence the exact
    /// number of body executions). Returns the oracle.
    /// </summary>
    private static async Task<Observation> OnEveryRouteAsync(string source, long? seed = null)
    {
        var oracle = await ObserveAsync(Route.EngineSync, source, seed);
        foreach (var route in Routes.Skip(1))
        {
            var observation = await ObserveAsync(route, source, seed);
            Assert.True(
                oracle.Kind == observation.Kind
                    && oracle.Value == observation.Value
                    && oracle.Codes.SequenceEqual(observation.Codes)
                    && oracle.HostCalls.SequenceEqual(observation.HostCalls),
                $"{route}: expected {oracle}, got {observation}\nsource:\n{source}");
        }

        return oracle;
    }

    private static void AssertOk(Observation observation, string neutral, params string[] hostCalls)
    {
        Assert.True(observation.Kind == "ok", $"expected success, got {observation}");
        Assert.Equal(neutral, observation.Value);
        Assert.Equal(hostCalls, observation.HostCalls);
    }

    private static void AssertFails(Observation observation, KatLangErrorCode code)
    {
        Assert.True(observation.Kind == "err", $"expected an evaluation failure, got {observation}");
        Assert.Equal([code.ToString()], observation.Codes);
    }

    /// <summary>The display rows of a seeded engine run (the reference random stream).</summary>
    private static string[] Rows(string source, long seed)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, new RunOptions { RandomSeed = seed }))
            .ToDisplayString()
            .Split('\n')
            .Select(static row => row.Trim())
            .ToArray();

    /// <summary>A collecting-only callable whose every body execution is one host call.</summary>
    private const string Only = "Only(*xs) = tick()";

    // ── 1. The rule's own examples ───────────────────────────────────────────────────

    /// <summary>Two bare reads of a collecting-only callable share ONE evaluation.</summary>
    [Fact]
    public async Task BareReads_ShareOneEvaluation()
        => AssertOk(await OnEveryRouteAsync($"{Only}\nOnly, Only"), "S[1, 1]", "tick#1");

    /// <summary>
    /// Both operands of an operator read the SAME cached evaluation. Before Q-03 each operand
    /// was lifted to the fresh call <c>Only(xs*)</c>: two ticks and the value <c>3</c>.
    /// </summary>
    [Fact]
    public async Task OperatorOperands_ReadTheSameCachedEvaluation()
    {
        AssertOk(await OnEveryRouteAsync($"{Only}\nOnly + Only"), "2", "tick#1");
        AssertOk(await OnEveryRouteAsync($"{Only}\nOnly == Only"), "true", "tick#1");
        AssertOk(await OnEveryRouteAsync($"{Only}\nOnly <= Only < Only + 1"), "true", "tick#1");
        AssertOk(await OnEveryRouteAsync($"{Only}\nOnly * 10 + Only, -Only"), "S[11, -1]", "tick#1");
    }

    /// <summary>
    /// <c>A</c> versus <c>A()</c>: the bare reads share the entry, while an explicit call is a
    /// fresh evaluation that neither reads, replaces nor populates it — with or without
    /// arguments, and in a lifting position as much as anywhere else.
    /// </summary>
    [Fact]
    public async Task ExplicitCalls_StayFresh_AndNeverTouchTheEntry()
    {
        AssertOk(await OnEveryRouteAsync($"{Only}\nOnly, Only(), Only"), "S[1, 2, 1]", "tick#1", "tick#2");
        // The first explicit call does not populate the entry: the first bare read evaluates.
        AssertOk(
            await OnEveryRouteAsync($"{Only}\nOnly(), Only, Only(), Only"),
            "S[1, 2, 3, 2]",
            "tick#1", "tick#2", "tick#3");
        // A call WITH arguments is equally fresh and equally separate from the entry.
        AssertOk(
            await OnEveryRouteAsync($"{Only}\nOnly(1, 2), Only, Only(3), Only"),
            "S[1, 2, 3, 2]",
            "tick#1", "tick#2", "tick#3");
        // In a lifting position the explicit call is still the only fresh evaluation.
        AssertOk(
            await OnEveryRouteAsync($"{Only}\nOnly + Only() + Only"),
            "4",
            "tick#1", "tick#2");
    }

    /// <summary>
    /// The constitutional example: a random-backed collecting-only callable is one value per run,
    /// in every position — each read is the stream's FIRST draw, and a trailing independent
    /// draw proves that no read consumed a hidden second one.
    /// </summary>
    [Theory]
    [InlineData(1L)]
    [InlineData(7L)]
    [InlineData(42L)]
    [InlineData(20260928L)]
    public async Task RandomBackedCallable_RollEqualsRoll(long seed)
    {
        const string draw = "randomInt(1, 1000000)";
        var r = Rows($"{draw}, {draw}", seed);

        AssertOk(await OnEveryRouteAsync($"Roll(*xs) = {draw}\nRoll == Roll", seed), "true");
        AssertOk(
            await OnEveryRouteAsync(
                $"Roll(*xs) = {draw}\nRoll, Roll + 0, sum(Roll), abs(Roll), [Roll]:0, Roll:0, {draw}",
                seed),
            $"S[{r[0]}, {r[0]}, {r[0]}, {r[0]}, {r[0]}, {r[0]}, {r[1]}]");
        // An explicit call draws afresh: it consumes the SECOND draw and leaves the entry alone.
        AssertOk(
            await OnEveryRouteAsync($"Roll(*xs) = {draw}\nRoll, Roll(), Roll", seed),
            $"S[{r[0]}, {r[1]}, {r[0]}]");
    }

    // ── 2. Every consumer position reads the one cached evaluation ───────────────────

    /// <summary>
    /// Formerly lifting positions and neutral positions alike. Each program reads <c>Only</c>
    /// once as a plain row and again through the consumer; <c>Defs</c> declares any helper the
    /// consumer needs.
    /// </summary>
    public static TheoryData<string, string> ConsumerPositions() => new()
    {
        { "", "Only + 0" },
        { "", "0 - Only" },
        { "", "-Only" },
        { "", "Only * Only" },
        { "", "Only == 1" },
        { "", "1 <= Only <= 1" },
        { "", "not (Only == 1)" },
        { "", "[Only, Only]" },
        { "", "[Only]:0" },
        { "", "Only:0" },
        { "", "[Only*]" },
        { "", "(Only*, 0)" },
        { "", "abs(Only)" },
        { "", "Math.Abs(Only)" },
        { "", "pow(Only, 2)" },
        { "", "Only.abs" },
        { "", "(Only + 0).abs" },
        { "", "sum(Only)" },
        { "", "Only.string" },
        { "", "if(Only == 1, Only, 0)" },
        { "", "(Only, Only)" },
        { "", "{ Only + Only }" },
        { "Formula = Only + 0", "Formula + Formula" },
        { "Nested = { Inner = Only * 2 \n Inner + Only }", "Nested" },
        { "Twice(v) = v + v", "Twice(Only)" },
        { "Twice(v) = v + v", "Only.Twice" },
        { "", "map([1, 2], {x + Only})" },
        { "", "repeat({s + Only}, 3, 0)" },
        { "Step = s + Only", "repeat(Step, 3, 0)" },
        { "", "while({s + Only, s + Only < 3}, 0)" },
        { "a, b = Only + 0, Only * 10", "a + b" },
    };

    /// <summary>
    /// THE CONSUMER LAW. A collecting-only callable behaves in every consumer position exactly
    /// like the zero-parameter property it abbreviates — the same value and the same host log —
    /// and in every position the body runs ONCE for the whole program: the consumer never
    /// decides whether the body runs again.
    /// </summary>
    [Theory]
    [MemberData(nameof(ConsumerPositions))]
    public async Task EveryConsumerPosition_ReadsTheOneCachedEvaluation(string defs, string consumer)
    {
        var prelude = defs.Length == 0 ? "" : defs + "\n";
        var collecting = await OnEveryRouteAsync($"{Only}\n{prelude}Only, {consumer}");
        var zeroParameter = await OnEveryRouteAsync($"Only = tick()\n{prelude}Only, {consumer}");

        Assert.Equal(zeroParameter.ToString(), collecting.ToString());
        Assert.Equal(["tick#1"], collecting.HostCalls);
    }

    /// <summary>
    /// The front end leaves every such reference BARE: the program's root gains no parameter,
    /// and no synthesized call to the callable exists anywhere in the elaborated tree. (Before
    /// Q-03 each of these rows lifted a collecting <c>xs</c> into the root and rewrote the
    /// reference into <c>Only(xs*)</c>.)
    /// </summary>
    [Theory]
    [InlineData("Only + 1")]
    [InlineData("Only == Only")]
    [InlineData("[Only]")]
    [InlineData("Only:0")]
    [InlineData("[Only*]")]
    [InlineData("abs(Only)")]
    [InlineData("Math.Abs(Only)")]
    [InlineData("Only.abs")]
    [InlineData("map([1], {x + Only})")]
    public void TheFrontEnd_NeverRewritesAZeroArgumentAcceptingReference(string row)
    {
        var root = SourceProvenance.ParseValid($"Only(*xs) = xs.count\n{row}").Root;

        Assert.Empty(root.Parameters);
        Assert.Empty(CallsOf("Only", root));
    }

    /// <summary>
    /// An alias row is not a value position (FWD-02, superseding Q-03's alias clause): the lone
    /// bare row names the callable itself, and Only DECLARES a (collecting) parameter, so the row is
    /// a CALLABLE ALIAS of Only — never a value read, although Only also accepts zero arguments. The
    /// root that reads the alias BARE gains nothing: the alias's callable accepts zero arguments, so
    /// its name there is the alias's own cached zero-argument value.
    /// </summary>
    [Fact]
    public void TheFrontEnd_MakesAZeroArgumentCallableWithParametersACallableAlias()
    {
        var root = SourceProvenance.ParseValid("Only(*xs) = xs.count\nAlias = Only\nAlias + 1").Root;
        var alias = Assert.IsType<Algorithm.Alias>(Assert.Single(root.Properties, static p => p.Name == "Alias").Value);

        Assert.Equal("Only", Assert.IsType<Expr.Resolve>(alias.Target).Name);
        Assert.Equal(["*xs"], alias.ResolvedTarget!.Signature.Signature!.ParameterPatterns.Select(static pattern => pattern.DisplayName));
        Assert.Empty(root.Parameters);
        Assert.Empty(CallsOf("Alias", root));
    }

    // ── 3. Selection and formula chains ──────────────────────────────────────────────

    /// <summary>
    /// <c>first(Pair)</c> and <c>Pair:0</c> choose from ONE evaluation of <c>Pair</c>. Before
    /// Q-03 the index target was lifted, so <c>Pair:0</c> read a fresh evaluation while the
    /// neutral builtin argument read the cached one.
    /// </summary>
    [Fact]
    public async Task Selection_FirstAndIndex_ObserveTheSameEvaluation()
        => AssertOk(
            await OnEveryRouteAsync("Pair(*xs) = tick(), tick()\nfirst(Pair), Pair:0, last(Pair), Pair:1, Pair"),
            "S[1, 1, 2, 2, S[1, 2]]",
            "tick#1", "tick#2");

    [Theory]
    [InlineData(5L)]
    [InlineData(7L)]
    [InlineData(99L)]
    public async Task Selection_RandomBackedPair_FirstEqualsIndexZero(long seed)
        => AssertOk(
            await OnEveryRouteAsync(
                "Pair(*xs) = randomInt(0, 1000000), randomInt(0, 1000000)\n"
                + "first(Pair) == Pair:0, last(Pair) == Pair:1, Pair:0 == Pair:0",
                seed),
            "S[true, true, true]");

    /// <summary>
    /// A formula chain doubles its references at every level; each level's value is still ONE
    /// read of <c>Only</c>. Before Q-03 the base ran 2^k times (4096 host calls here).
    /// </summary>
    [Fact]
    public async Task FormulaChain_EvaluatesTheBaseOnce()
    {
        var chain = new System.Text.StringBuilder("Only(*xs) = tick() * 0 + 1\nA1 = Only + Only\n");
        for (var level = 2; level <= 12; level++)
            chain.Append($"A{level} = A{level - 1} + A{level - 1}\n");
        chain.Append("A12");

        AssertOk(await OnEveryRouteAsync(chain.ToString()), "4096", "tick#1");

        // The same through strict Math arguments and list elements.
        AssertOk(
            await OnEveryRouteAsync(
                "Only(*xs) = tick() * 0 + 1\nB1 = abs(Only) + [Only]:0\nB2 = abs(B1) + [B1]:0\nB3 = abs(B2) + [B2]:0\nB3"),
            "8",
            "tick#1");
    }

    // ── 4. Lifting is untouched where arguments are REQUIRED ─────────────────────────

    /// <summary>
    /// A callable that requires a supplied argument still lifts and forwards: its parameters join
    /// the referencing formula's signature (a lone row is a callable alias, which is the callee), and
    /// each lifted reference is a CALL — fresh, like every call. The rule never disables lifting; it only stops treating "declares a parameter"
    /// as "requires an argument".
    /// </summary>
    [Fact]
    public async Task RequiredParameters_StillLiftAndForward()
    {
        AssertOk(await OnEveryRouteAsync("Inc(x) = x + 1\nK = Inc * 2\nK(4)"), "10");
        AssertOk(await OnEveryRouteAsync("Add(a, b) = a + b\nPlus = Add\nPlus(2, 3)"), "5");
        // A fixed prefix beside a collector: one supplied value is required, so it lifts.
        AssertOk(await OnEveryRouteAsync("Head(x, *rest) = x + rest.count\nH = Head + 0\nH(5, 6, 7)"), "7");
        // A group holding a collector is ONE required slot: it lifts, and a caller's single
        // collecting stream still forwards into it by shape.
        AssertOk(await OnEveryRouteAsync("G((*xs)) = xs.count\nW = G + 0\nW((1, 2, 3))"), "3");
        AssertOk(await OnEveryRouteAsync("G((*xs)) = xs.count\nUse(*items) = G + 0\nUse(1, 2)"), "2");
        // Each lifted reference is a fresh call of a callable that requires its argument.
        AssertOk(
            await OnEveryRouteAsync("Twice(x) = x + tick()\nK = Twice + Twice\nK(10)"),
            "23",
            "tick#1", "tick#2");

        var root = SourceProvenance.ParseValid("Inc(x) = x + 1\nK = Inc * 2\nK(4)").Root;
        var k = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, static p => p.Name == "K").Value);
        Assert.Equal(["x"], k.Params);
        Assert.Single(CallsOf("Inc", k));

        var headRoot = SourceProvenance.ParseValid("Head(x, *rest) = x\nH = Head + 0\nH(5)").Root;
        var h = Assert.IsType<Algorithm.User>(Assert.Single(headRoot.Properties, static p => p.Name == "H").Value);
        Assert.Equal(["x", "rest"], h.Params);
        Assert.Equal(ParameterKind.Collecting, h.Parameters[1].Kind);
    }

    /// <summary>
    /// A required callable left bare at the root keeps its arity rejection (the root row is
    /// preserved), and in a lifting position the root still reports the unresolved input it
    /// cannot supply — both unchanged.
    /// </summary>
    [Fact]
    public async Task RequiredCallable_AtTheRoot_KeepsItsRejections()
    {
        AssertFails(await OnEveryRouteAsync("Inc(x) = x + 1\nInc"), KatLangErrorCode.ArityMismatch);
        AssertFails(await OnEveryRouteAsync("Inc(x) = x + 1\nInc + 0"), KatLangErrorCode.UnresolvedImplicitParams);
        AssertFails(await OnEveryRouteAsync("Head(x, *rest) = x\nHead + 0"), KatLangErrorCode.UnresolvedImplicitParams);
    }

    // ── 5. Zero-parameter properties are unchanged ───────────────────────────────────

    [Fact]
    public async Task ZeroParameterProperty_AVersusACall_IsUnchanged()
    {
        AssertOk(
            await OnEveryRouteAsync("A = tick()\nA, A(), A, A + A, [A]"),
            "S[1, 2, 1, 2, L[1]]",
            "tick#1", "tick#2");
        AssertOk(await OnEveryRouteAsync("A = tick()\nA(), A"), "S[1, 2]", "tick#1", "tick#2");
    }

    // ── 6. Aliases ───────────────────────────────────────────────────────────────────

    /// <summary>
    /// An alias of a callable that accepts zero supplied arguments is a CALLABLE ALIAS (FWD-02,
    /// decided September 29 2026 and binding indirection since October 1 2026, superseding Q-03's
    /// "an alias is a value demand" clause, which in turn had superseded "aliases of collecting
    /// callables are collecting"): it IS <c>Cnt</c>'s callable, collecting signature included, so it
    /// takes arguments directly and as a callback exactly like <c>Cnt</c> and like the written
    /// forwarding alias. Read BARE it is still a cached zero-argument value (Q-03 applies to the
    /// alias as to any callable that works with no arguments) — of its OWN binding: cache identity
    /// follows binding identity, so the target's zero-argument demand is evaluated once for the
    /// alias's entry and the callee's bare reads keep theirs.
    /// </summary>
    [Fact]
    public async Task AliasOfAZeroArgumentCallable_KeepsItsSignature_AndIsReadWhenBare()
    {
        AssertOk(await OnEveryRouteAsync("Cnt(*xs) = xs.count\nAlias = Cnt\nAlias, Alias(), Alias + 1"), "S[0, 0, 1]");
        AssertOk(await OnEveryRouteAsync("Cnt(*xs) = xs.count\nAlias = Cnt\nAlias(1, 2)"), "2");
        AssertOk(await OnEveryRouteAsync("Cnt(*xs) = xs.count\nAlias = Cnt\nmap([1, 2], Alias)"), "L[1, 1]");

        foreach (var alias in new[] { "Alias = Cnt", "Alias(*xs) = Cnt(xs*)" })
        {
            AssertOk(
                await OnEveryRouteAsync(
                    $"Cnt(*xs) = xs.count\n{alias}\nApply(f, xs) = map(xs, f)\n"
                    + "Alias(1, 2, 3), map([1, 2], Alias), Apply(Alias, [(10, 7), 20])"),
                "S[3, L[1, 1], L[1, 1]]");
        }

        // One evaluation per BINDING: the alias's entry, then Only's own entry.
        AssertOk(
            await OnEveryRouteAsync($"{Only}\nAlias = Only\nAlias, Alias + Alias, Only"),
            "S[1, 2, 2]",
            "tick#1",
            "tick#2");
        // A FORMULA over Only is a value read of Only's entry: one evaluation in all.
        AssertOk(
            await OnEveryRouteAsync($"{Only}\nFormula = Only + 0\nFormula, Formula + Formula, Only"),
            "S[1, 2, 1]",
            "tick#1");
    }

    // ── 7. Closed lists, scopes, opens, dot calls, loops ─────────────────────────────

    /// <summary>
    /// A closed explicit parameter list never forwards into a callable that accepts zero
    /// supplied arguments, even when it declares a same-named parameter: the reference is the
    /// cached value. And a strict Math position no longer rejects such a reference statically
    /// (formerly PV-27: "'Cnt' is required as a value here, but producing that value needs the
    /// implicit parameter 'ys'").
    /// </summary>
    [Fact]
    public async Task ClosedLists_ReadTheCachedValue_AndAreNeverRejectedForIt()
    {
        AssertOk(await OnEveryRouteAsync($"{Only}\nF(xs) = Only + 1\nF(10), F(20)"), "S[2, 2]", "tick#1");
        AssertOk(await OnEveryRouteAsync("Cnt(*ys) = ys.count\nH(k) = abs(Cnt) + k\nH(5)"), "5");
        AssertOk(await OnEveryRouteAsync("Cnt(*ys) = ys.count\nH(k) = Math.Abs(Cnt) + Cnt.abs + k\nH(5)"), "5");
    }

    /// <summary>
    /// Nested scopes follow the ordinary cache scope: a self-contained nested callable is one
    /// value per run, one that reads an enclosing owner's input one value per activation — and
    /// every read inside one activation shares it, whether the reference is a root row or a
    /// nested formula.
    /// </summary>
    [Fact]
    public async Task NestedScopes_FollowTheOrdinaryCacheScope()
    {
        AssertOk(
            await OnEveryRouteAsync("F(v) = {\n  Inner(*xs) = tick()\n  Inner + Inner + v\n}\nF(0), F(10)"),
            "S[2, 12]",
            "tick#1");
        AssertOk(
            await OnEveryRouteAsync("F(v) = {\n  Inner(*xs) = tick() + v\n  Inner + Inner\n}\nF(0), F(10)"),
            "S[2, 24]",
            "tick#1", "tick#2");
        AssertOk(
            await OnEveryRouteAsync($"{Only}\nNested = Only + Only\nNested, Only + Only, Nested"),
            "S[2, 2, 2]",
            "tick#1");
    }

    /// <summary>Lexical, opened and structural spellings of one binding share its one entry.</summary>
    [Fact]
    public async Task LexicalOpenedAndStructuralReads_ShareOneEntry()
        => AssertOk(
            await OnEveryRouteAsync(
                "open Lib\nLib = {\n  public Only(*xs) = tick()\n}\nOnly + Only, Lib.Only + 0, Lib.Only:0, abs(Lib.Only)"),
            "S[2, 1, 1, 1]",
            "tick#1");

    /// <summary>
    /// Dot-call paths agree with their plain spellings: the must-selected Math fallback
    /// <c>Only.abs</c> is <c>abs(Only)</c>, the extension call <c>Only.Twice</c> is
    /// <c>Twice(Only)</c>, and both read the one cached evaluation.
    /// </summary>
    [Fact]
    public async Task DotCallPaths_ReadTheCachedValue()
        => AssertOk(
            await OnEveryRouteAsync($"{Only}\nTwice(v) = v + v\nOnly.Twice, Twice(Only), Only.abs, abs(Only), (Only + 0).abs"),
            "S[2, 2, 1, 1, 1]",
            "tick#1");

    /// <summary>
    /// A loop step that reads the callable reads the cached value on every iteration, on the
    /// generic and the planned strategy alike (formerly one fresh evaluation per iteration).
    /// </summary>
    [Fact]
    public async Task LoopSteps_ReadTheCachedValue()
    {
        AssertOk(await OnEveryRouteAsync($"{Only}\nrepeat({{s + Only}}, 3, 0)"), "3", "tick#1");
        AssertOk(await OnEveryRouteAsync($"{Only}\nStep = s + Only\nrepeat(Step, 3, 0)"), "3", "tick#1");
        AssertOk(await OnEveryRouteAsync($"{Only}\nwhile({{s + Only, s + Only < 3}}, 0)"), "2", "tick#1");
    }

    // ── 8. Collectors: a failed read is that read's failure ──────────────────────────

    /// <summary>
    /// Reading a collected list demands every element's VALUE, and a callable that accepts
    /// zero supplied arguments has one (found by the Q-03 hostile review): when its evaluation
    /// fails, the read surfaces that genuine failure exactly as it does for a zero-parameter
    /// property. Formerly it reported "collects values, but a supplied argument is a
    /// callable", because the check asked whether the argument DECLARES parameters; that
    /// collector diagnostic no longer exists at all (VAR-03 as reconciled 2026-10-09: a
    /// collector preserves the supplied cells — <see cref="CollectingCallableForwardingLawTests"/>).
    /// </summary>
    [Theory]
    [InlineData("Coll(Bad)")]
    [InlineData("Bad.Coll")]
    [InlineData("Coll(1, Bad)")]
    [InlineData("Mid(0, Bad, 9)")]
    public async Task Collectors_SurfaceTheGenuineFailureOfAZeroArgumentCallable(string use)
    {
        const string support = "Coll(*ys) = ys\nMid(a, *m, z) = m\n";
        var collecting = await OnEveryRouteAsync($"Bad(*xs) = tick() / 0\n{support}{use}");
        var zeroParameter = await OnEveryRouteAsync($"Bad = tick() / 0\n{support}{use}");

        AssertFails(collecting, KatLangErrorCode.DivisionByZero);
        Assert.Equal(zeroParameter.Codes, collecting.Codes);
        Assert.Equal(zeroParameter.HostCalls, collecting.HostCalls);
    }

    /// <summary>
    /// A callable that REQUIRES a supplied argument, and a builtin, have no zero-argument value:
    /// demanding the collected list demands each element, so the callable's own zero-supply
    /// rejection surfaces (collecting them alone demands nothing, and re-spreading keeps them
    /// callable).
    /// </summary>
    [Fact]
    public async Task Collectors_DemandTheCallablesOwnZeroArgumentRejection()
    {
        AssertFails(await OnEveryRouteAsync("Coll(*ys) = ys\nInc(x) = x + 1\nColl(Inc)"), KatLangErrorCode.ArityMismatch);
        AssertFails(await OnEveryRouteAsync("Coll(*ys) = ys\nHead(x, *rest) = x\nColl(1, Head)"), KatLangErrorCode.ArityMismatch);
        AssertFails(await OnEveryRouteAsync("Coll(*ys) = ys\nColl(sum)"), KatLangErrorCode.ArityMismatch);
    }

    [Fact]
    public async Task CollectorForwarding_PreservesWholeValuesAndTheBareReadEntry()
        => AssertOk(
            await OnEveryRouteAsync(
                "Pair(*xs) = tick(), tick()\nColl(*ys) = ys\nForward(*ys) = Coll(ys*)\n"
                + "Coll(Pair), Forward(Pair), Pair.Coll, Coll(Pair()), Coll(Pair)"),
            "S[L[S[1, 2]], L[S[1, 2]], L[S[1, 2]], L[S[3, 4]], L[S[1, 2]]]",
            "tick#1", "tick#2", "tick#3", "tick#4");

    [Theory]
    [InlineData("Coll(Bad)")]
    [InlineData("Coll(Bad())")]
    [InlineData("Forward(Bad)")]
    [InlineData("Relay(Bad)")]
    [InlineData("Bad.Coll")]
    public async Task CollectorFailures_KeepOneAttemptThroughNestedForwarding(string use)
    {
        var result = await OnEveryRouteAsync(
            "Bad(*xs) = tick() / 0\nColl(*ys) = ys\nForward(f) = Coll(f)\nRelay(g) = Forward(g)\n" + use);
        AssertFails(result, KatLangErrorCode.DivisionByZero);
        Assert.Equal(["tick#1"], result.HostCalls);
    }

    [Fact]
    public async Task ShadowedCollectingBindings_HaveSeparateEntries()
        => AssertOk(
            await OnEveryRouteAsync(
                $"{Only}\nBlock = {{ Only(*xs) = tick()\nOnly + Only, Only(), Only }}\nOnly, Block, Only"),
            "S[1, S[4, 3, 2], 1]",
            "tick#1", "tick#2", "tick#3");

    [Fact]
    public async Task ClauseBodies_ReadOneValue_WhileInvokingSlotsStillCall()
    {
        AssertOk(
            await OnEveryRouteAsync($"{Only}\nF(0) = Only + Only\nF(n) = n + Only\nF(0), F(10), Only"),
            "S[2, 11, 1]", "tick#1");
        AssertOk(
            await OnEveryRouteAsync($"{Only}\nOnly, map([7, 8], Only), Only"),
            "S[1, L[2, 3], 1]", "tick#1", "tick#2", "tick#3");
    }

    [Fact]
    public async Task ExplicitStructuralCall_BypassesTheSharedOpenedEntry()
        => AssertOk(
            await OnEveryRouteAsync(
                "open Lib\nLib = { public Only(*xs) = tick() }\nOnly, Lib.Only(), Only, Lib.Only"),
            "S[1, 2, 1, 1]", "tick#1", "tick#2");

    // ── Helpers ──────────────────────────────────────────────────────────────────────

    /// <summary>Every call in <paramref name="algorithm"/> whose callee is the bare name <paramref name="callee"/>.</summary>
    private static IReadOnlyList<Expr.Call> CallsOf(string callee, Algorithm algorithm)
    {
        var collector = new CallCollector(callee);
        collector.VisitAlgorithm(algorithm);
        return collector.Calls;
    }

    private sealed class CallCollector(string callee) : AstWalker
    {
        public List<Expr.Call> Calls { get; } = [];

        public override void VisitExpr(Expr expr)
        {
            if (expr is Expr.Call { Function: Expr.Resolve(var name) } call && name == callee)
                Calls.Add(call);
            base.VisitExpr(expr);
        }
    }
}
