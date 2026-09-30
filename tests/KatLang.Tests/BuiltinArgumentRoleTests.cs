using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Sequences;
using KatLang.Rendering;

namespace KatLang.Tests;

/// <summary>
/// BUILTIN CALL ASSEMBLY RESPECTS ARGUMENT ROLES (PV-05 / PV-19 / PV-20, September 2026).
///
/// <para>A collection builtin's argument adapter handles every written slot by the ROLE its
/// position has in the builtin's metadata (<c>SequenceBuiltinMetadata.SlotRole</c>):</para>
/// <list type="bullet">
///   <item>a VALUE slot — the collection, a value or whole-number control, and <c>reduce</c>'s
///   <c>initial</c> — is demanded ONCE; its value or its failure is final for the call and is
///   never retried (PV-05: a failed <c>initial</c> used to be evaluated again, so a seeded
///   failure could heal into a success and nested initials cost 2^n evaluations);</item>
///   <item>a CALLBACK slot — the <c>filter</c> predicate, the <c>map</c> mapper, the
///   <c>reduce</c> reducer — carries its algorithm and is INVOKED by the builtin; supplying it
///   evaluates nothing (PV-19: a zero-parameter callback used to be value-evaluated during
///   assembly, so an unused callback ran its effects, consumed random draws, and could
///   recurse forever);</item>
///   <item>a SPREAD slot is supply assembly: it supplies exactly its items, or its failure is
///   the call's failure, raised before the arity check and before any later slot (PV-20: a
///   failed spread used to be kept as ONE phantom item, so <c>take(Bad*)</c> was an arity error
///   and <c>map([], Bad*)</c> swallowed the failure).</item>
/// </list>
/// <para>Every case runs on six routes — the sync and async engines, the genuinely suspending
/// async twin, the generic and optimized evaluators, and the forced twin — which must agree on
/// the outcome, the error codes and messages, and the exact host-call log. Lean pins the same
/// structure in <c>CoreTests/BuiltinArgumentRoles.lean</c> (binding-context counts stand in for
/// effects there) and the slot-role laws in <c>KatLangArityLaws.lean</c>.</para>
/// </summary>
public class BuiltinArgumentRoleTests
{
    // ── Execution routes (the ResourceLimitTerminalityTests route set) ──────────────────

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
    }

    /// <summary>
    /// <c>tick()</c> counts its invocations and <c>trace(x)</c> logs and returns its argument.
    /// On the twin routes both genuinely suspend (<c>Task.Yield</c>) before acting.
    /// </summary>
    private static HostOperations OperationsFor(HostLog log, bool suspending)
        => suspending
            ? HostOperations.Create(
                HostOperation.CreateAsync("tick", async (_, _) => { await Task.Yield(); return log.Tick(); }),
                HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return log.Trace(args[0]); }, "x"))
            : HostOperations.Create(
                HostOperation.Create("tick", (_, _) => log.Tick()),
                HostOperation.Create("trace", (args, _) => log.Trace(args[0]), "x"));

    private sealed record Observation(string Kind, string? Value, IReadOnlyList<string> Codes, IReadOnlyList<string> HostCalls)
    {
        public IReadOnlyList<string> ErrorDetails { get; init; } = [];

        public override string ToString()
            => $"{Kind} {Value} codes=[{string.Join(",", Codes)}] host=[{string.Join(",", HostCalls)}] details=[{string.Join(";", ErrorDetails)}]";
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

        return result.IsError
            ? new Observation("err", null, [KatLangError.FromEvalError(result.Error).Code.ToString()], [.. log.Calls])
            {
                ErrorDetails = [DescribeError(KatLangError.FromEvalError(result.Error))],
            }
            : new Observation("ok", Neutral(result.Value.Value), [], [.. log.Calls]);
    }

    private static Observation FromRunResult(RunResult result, HostLog log) => result switch
    {
        RunResult.Success success => new("ok", Neutral(success.Value), [], [.. log.Calls]),
        RunResult.EvalFailure failure => new("err", null, [.. failure.Errors.Select(static error => error.Code.ToString())], [.. log.Calls])
        {
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
    /// synchronous engine — outcome kind, value, error codes and messages, and the exact
    /// host-call log. Returns the oracle.
    /// </summary>
    private static async Task<Observation> OnEveryRouteAsync(string source, long? seed = null, EvaluationLimits? limits = null)
    {
        var oracle = await ObserveAsync(Route.EngineSync, source, seed, limits);
        Assert.True(oracle.Kind is "ok" or "err", $"the probe must evaluate: {oracle}\nsource:\n{source}");
        foreach (var route in Routes.Skip(1))
        {
            var observation = await ObserveAsync(route, source, seed, limits);
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

    private static void AssertOk(Observation observation, string neutral, params string[] hostCalls)
    {
        Assert.True(observation.Kind == "ok", $"expected success, got {observation}");
        Assert.Equal(neutral, observation.Value);
        Assert.Equal(hostCalls, observation.HostCalls);
    }

    private static void AssertFails(Observation observation, KatLangErrorCode code, params string[] hostCalls)
    {
        Assert.True(observation.Kind == "err", $"expected an evaluation failure, got {observation}");
        Assert.Equal([code.ToString()], observation.Codes);
        Assert.Equal(hostCalls, observation.HostCalls);
    }

    /// <summary>The single error message (without its location) of a failed observation.</summary>
    private static string Message(Observation observation)
    {
        var detail = Assert.Single(observation.ErrorDetails);
        return detail[..detail.LastIndexOf(" @ ", StringComparison.Ordinal)];
    }

    private const string Add = "Add(a, b) = a + b\n";

    // ── 1. The roles are the builtin's metadata ─────────────────────────────────────────

    [Fact]
    public void SlotRoles_AreDecidedByTheMetadata_ReduceInitialIsAValueSlot()
    {
        SequenceBuiltinSlotRole RoleOf(BuiltinId builtin, int slot)
            => BuiltinRegistry.GetBuiltin(builtin).SequenceMetadata!.Value.SlotRole(slot);

        Assert.Equal(SequenceBuiltinSlotRole.Value, RoleOf(BuiltinId.@reduce, 0));
        Assert.Equal(SequenceBuiltinSlotRole.Callback, RoleOf(BuiltinId.@reduce, 1));
        Assert.Equal(SequenceBuiltinSlotRole.Value, RoleOf(BuiltinId.@reduce, 2));
        Assert.Equal(SequenceBuiltinSlotRole.Surplus, RoleOf(BuiltinId.@reduce, 3));
        Assert.Equal(SequenceBuiltinSlotRole.Callback, RoleOf(BuiltinId.@map, 1));
        Assert.Equal(SequenceBuiltinSlotRole.Callback, RoleOf(BuiltinId.@filter, 1));
        Assert.Equal(SequenceBuiltinSlotRole.Value, RoleOf(BuiltinId.@contains, 1));
        Assert.Equal(SequenceBuiltinSlotRole.Value, RoleOf(BuiltinId.@take, 1));
        Assert.Equal(SequenceBuiltinSlotRole.Surplus, RoleOf(BuiltinId.@count, 1));

        // Every collection builtin: position 0 is the value slot `collection`, a callback is
        // exactly an algorithm control, and every position past the signature is surplus.
        foreach (var builtin in Enum.GetValues<BuiltinId>())
        {
            if (BuiltinRegistry.GetBuiltin(builtin).SequenceMetadata is not { } metadata)
                continue;
            Assert.Equal(SequenceBuiltinSlotRole.Value, metadata.SlotRole(0));
            for (var index = 0; index < metadata.SuffixArgs.Count; index++)
            {
                Assert.Equal(
                    metadata.SuffixArgs[index].Kind == SequenceBuiltinSuffixArgKind.Algorithm
                        ? SequenceBuiltinSlotRole.Callback
                        : SequenceBuiltinSlotRole.Value,
                    metadata.SlotRole(index + 1));
            }

            Assert.Equal(SequenceBuiltinSlotRole.Surplus, metadata.SlotRole(metadata.SuffixArgs.Count + 1));
        }
    }

    // ── 2. PV-05 — reduce's initial is a value slot, demanded once, never retried ──────

    [Theory]
    [InlineData("reduce([], {x + y}, 10 / randomInt(0, 2))")]
    [InlineData(Add + "reduce([], Add, 10 / randomInt(0, 2))")]
    [InlineData(Add + "reduce([1, 2], Add, 10 / randomInt(0, 2))")]
    [InlineData(Add + "[].reduce(Add, 10 / randomInt(0, 2))")]
    [InlineData(Add + "Init = 10 / randomInt(0, 2)\nreduce([], Add, Init)")]
    [InlineData(Add + "reduce([], Add, {10 / randomInt(0, 2)})")]
    public async Task SeededFailingInitial_StaysAFailure_ItIsNeverRetried(string program)
    {
        // Seed 5 draws 0 then 1: the first evaluation divides by zero. A retry used to draw
        // again, divide by 1 and return 10 (or 13) — a seeded failure healed into a success.
        var observation = await OnEveryRouteAsync(program, seed: 5);
        AssertFails(observation, KatLangErrorCode.DivisionByZero);
        Assert.Equal(
            ["0", "1"],
            Assert.IsType<RunResult.Success>(KatLangEngine.Run("randomInt(0, 2), randomInt(0, 2)", new RunOptions { RandomSeed = 5 }))
                .ToDisplayString().Split('\n').Select(static row => row.Trim()).ToArray());
    }

    [Theory]
    [InlineData("reduce([], {x + y}, trace(1) / 0)")]
    [InlineData(Add + "reduce([1, 2], Add, trace(1) / 0)")]
    [InlineData(Add + "Bad = trace(1) / 0\nreduce([], Add, Bad)")]
    [InlineData(Add + "reduce([], Add, {trace(1) / 0})")]
    [InlineData(Add + "[].reduce(Add, trace(1) / 0)")]
    [InlineData(Add + "F(i) = reduce([], Add, i)\nF(trace(1) / 0)")]
    [InlineData(Add + "Bad = trace(1) / 0\nF(i) = reduce([], Add, i)\nF(Bad)")]
    [InlineData(Add + "Bad = trace(1) / 0\nF(i) = i.reduce(Add, 0)\nreduce([], Add, Bad)")]
    public async Task FailingInitial_IsEvaluatedExactlyOnce(string program)
        => AssertFails(await OnEveryRouteAsync(program), KatLangErrorCode.DivisionByZero, "trace(1)");

    [Theory]
    [InlineData(1)]
    [InlineData(3)]
    [InlineData(5)]
    [InlineData(8)]
    public async Task NestedFailingInitials_EvaluateTheFailureOnce_NotExponentially(int depth)
    {
        // Formerly every level retried its failed initial, so the innermost failure ran
        // 2^depth times (32 traces at depth 5).
        var initial = "trace(1) / 0";
        for (var level = 0; level < depth; level++)
            initial = $"reduce([], F, {initial})";
        AssertFails(await OnEveryRouteAsync("F(e, a) = a\n" + initial), KatLangErrorCode.DivisionByZero, "trace(1)");
    }

    [Fact]
    public async Task InitialFailure_IsTheFirstRaisedFailure_NotTheRetrysKind()
    {
        // The first evaluation raises DivisionByZero (tick#1 < 2); a retry used to take the
        // other branch and report ITS kind (a TypeMismatch after tick#2).
        AssertFails(
            await OnEveryRouteAsync(Add + "reduce([1], Add, if(tick() < 2, 1 / 0, [5] + 1))"),
            KatLangErrorCode.DivisionByZero,
            "tick#1");
    }

    [Fact]
    public async Task SuccessfulInitial_IsReadOnce_AndTheStreamIsNotShifted()
    {
        // A successful initial always read once; the value slot keeps that, with the random
        // stream in written order: the initial draws first, the root row second.
        var reference = Assert.IsType<RunResult.Success>(
                KatLangEngine.Run("randomInt(0, 1000), randomInt(0, 1000)", new RunOptions { RandomSeed = 5 }))
            .ToDisplayString().Split('\n').Select(static row => row.Trim()).ToArray();
        var first = int.Parse(reference[0], System.Globalization.CultureInfo.InvariantCulture);
        AssertOk(
            await OnEveryRouteAsync(Add + "reduce([1, 2], Add, randomInt(0, 1000)), randomInt(0, 1000)", seed: 5),
            $"S[{first + 3}, {reference[1]}]");
        AssertOk(await OnEveryRouteAsync(Add + "reduce([1, 2], Add, trace(10))"), "13", "trace(10)");
        // A named property initial is its ordinary cached read: one tick for three reads.
        AssertOk(await OnEveryRouteAsync(Add + "A = tick()\nreduce([1, 2], Add, A), A, reduce([], Add, A)"), "S[4, 1, 1]", "tick#1");
        // A multi-output initial is ONE accumulator value.
        AssertOk(await OnEveryRouteAsync(Add + "P = 1, 2\nreduce([], Add, P)"), "S[1, 2]");
    }

    [Fact]
    public async Task InitialRejections_KeepTheirReports()
    {
        // A parameterized callable is the reducer written where the accumulator belongs:
        // reduce's dedicated hint, decided from the signature without entering the body. The
        // initial accumulator is a VALUE slot an inferring root would lift the callable into
        // (the unified formula-lifting law), so the bare demand is pinned under a closed list.
        var inc = await OnEveryRouteAsync(Add + "Inc(x) = trace(x) + 1\nProbe(u) = reduce([1, 2], Add, Inc)\nProbe(0)");
        AssertFails(inc, KatLangErrorCode.ArityMismatch);
        Assert.Contains("the last argument must be an initial accumulator value", Message(inc));
        Assert.Contains("still needs 'x'", Message(inc));
        // A clause family keeps the law's report; a collecting-only callable is demanded as
        // the value it denotes (its own body, one evaluation) — it accepts zero arguments, so
        // it never lifts, root or not.
        AssertFails(await OnEveryRouteAsync(Add + "Fam(0) = 0\nFam(n) = n\nProbe(u) = reduce([1, 2], Add, Fam)\nProbe(0)"), KatLangErrorCode.NoMatchingBranch);
        AssertOk(await OnEveryRouteAsync("Keep(e, a) = a\nOnly(*xs) = trace(xs)\nreduce([1, 2], Keep, Only)"), "L[]", "trace(L[])");
    }

    // ── 3. PV-19 — a callback slot is never value-evaluated merely because it was supplied

    [Theory]
    [InlineData("A = tick()\nmap([], A)", "L[]")]
    [InlineData("A = tick()\nfilter([], A)", "L[]")]
    [InlineData("A = tick()\nreduce([], A, 0)", "0")]
    [InlineData("A = tick()\n[].map(A)", "L[]")]
    [InlineData("A = tick()\n[].filter(A).count", "0")]
    [InlineData("A = tick()\nB = A\nmap([], B)", "L[]")]
    [InlineData("map([], {tick()})", "L[]")]
    [InlineData("map([], (tick()))", "L[]")]
    [InlineData("map([], tick() + 1)", "L[]")]
    [InlineData("Box = {\n    public V = tick()\n}\nmap([], Box.V)", "L[]")]
    [InlineData("open Lib\nLib = {\n    public V = tick()\n}\nmap([], V)", "L[]")]
    [InlineData("A = tick()\nOuter = { map([], A) }\nOuter", "L[]")]
    public async Task UnusedCallback_RunsNoEffect(string program, string value)
        => AssertOk(await OnEveryRouteAsync(program), value);

    [Fact]
    public async Task UnusedCallback_BehavesLikeAZeroIterationLoopStep()
    {
        // The same algorithm-channel rule the loop builtins always had.
        AssertOk(await OnEveryRouteAsync("A = tick()\nrepeat(A, 0, 5)"), "5");
        AssertOk(await OnEveryRouteAsync("A = tick()\nmap([], A)"), "L[]");
    }

    [Theory]
    [InlineData("map([], R)", "L[]")]
    [InlineData("filter([], R)", "L[]")]
    [InlineData("reduce([], R, 7)", "7")]
    [InlineData("[].filter(R).count", "0")]
    [InlineData("repeat(R, 0, 5)", "5")]
    public async Task UnusedCallback_ConsumesNoRandomDraw(string row, string value)
    {
        // The root's own draw is the stream's FIRST value: formerly the unused callback took
        // it (the second value was printed instead).
        var first = Assert.IsType<RunResult.Success>(KatLangEngine.Run("randomInt(0, 1000)", new RunOptions { RandomSeed = 7 }))
            .ToDisplayString().Trim();
        AssertOk(await OnEveryRouteAsync($"R = randomInt(0, 1000)\n{row}, randomInt(0, 1000)", seed: 7), $"S[{value}, {first}]");
    }

    [Theory]
    [InlineData("L = L + 1\nmap([], L)", "L[]")]
    [InlineData("L = L + 1\nfilter([], L)", "L[]")]
    [InlineData("L = L + 1\nreduce([], L, 3)", "3")]
    [InlineData("E = ()\nD = E.filter(D)\nD.count", "0")]
    [InlineData("E = ()\nD = count(filter(E, D))\nD", "0")]
    public async Task UnusedCallback_CannotRecurse(string program, string value)
        // Formerly the eager attempt read the self-referential callback until the stack
        // backstop (EvaluationStackExhausted).
        => AssertOk(await OnEveryRouteAsync(program), value);

    [Theory]
    [InlineData("map([], 1 / 0)", "L[]")]
    [InlineData("filter([], 1 / 0)", "L[]")]
    [InlineData("reduce([], 1 / 0, 7)", "7")]
    [InlineData("Bad = trace(1) / 0\nmap([], Bad)", "L[]")]
    [InlineData("Bad = [1]:5\n[].filter(Bad).count", "0")]
    public async Task UnusedCallback_CannotFail(string program, string value)
        => AssertOk(await OnEveryRouteAsync(program), value);

    [Fact]
    public async Task InvokedCallback_IsAnOrdinaryCallPerElement()
    {
        AssertOk(await OnEveryRouteAsync("map([1, 2], {x + tick()})"), "L[2, 4]", "tick#1", "tick#2");
        AssertOk(await OnEveryRouteAsync("Keep(x) = trace(x) > 1\nfilter([1, 2], Keep)"), "L[2]", "trace(1)", "trace(2)");
        AssertOk(await OnEveryRouteAsync(Add + "reduce([1, 2, 3], Add, 0)"), "6");
        // A zero-parameter callable invoked with an element is rejected by the binder before
        // its body runs (formerly the eager attempt had already run it once).
        AssertFails(await OnEveryRouteAsync("A = tick()\nmap([1], A)"), KatLangErrorCode.ArityMismatch);
        AssertFails(await OnEveryRouteAsync("map([1, 2], 1 / 0)"), KatLangErrorCode.ArityMismatch);
        AssertFails(await OnEveryRouteAsync("map([1, 2], 5)"), KatLangErrorCode.ArityMismatch);
    }

    [Fact]
    public async Task UnusedCallback_LeavesThePropertyCacheToTheValueReads()
    {
        // The callback slot reads nothing; the root reads evaluate `A` once and share it.
        AssertOk(await OnEveryRouteAsync("A = tick()\nmap([], A), A, A"), "S[L[], 1, 1]", "tick#1");
        // An explicit forwarding CALL still evaluates its written argument (CALL-02: a user
        // call assembles every slot eagerly) — the builtin slot then adds no evaluation.
        AssertOk(await OnEveryRouteAsync("A = tick()\nApply(f, xs) = map(xs, f)\nApply(A, [])"), "L[]", "tick#1");
    }

    [Fact]
    public async Task FusedFilterCount_NeverEvaluatesThePredicate_OnEitherStrategy()
    {
        foreach (var pipeline in new[] { "[].filter(A).count", "count([].filter(A))", "E.filter(A).count", "count(filter(range(1, 3), A))" })
        {
            var source = $"A = tick()\nE = ()\n{pipeline}";
            var observation = await OnEveryRouteAsync(source);
            Assert.Empty(observation.HostCalls);
        }

        // The optimized route genuinely takes the fused region for these shapes.
        var diagnostics = new SequencePipelineDiagnostics();
        var parsed = SourceProvenance.ParseValid("A = 7\nE = ()\nE.filter(A).count");
        _ = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), sequenceDiagnostics: diagnostics);
        Assert.Equal(1, diagnostics.GetSnapshot().FilterCountFusionHits);
    }

    // ── 4. PV-20 — a failed spread is the call's failure, never a phantom argument ─────

    [Theory]
    [InlineData("take(Bad*)", KatLangErrorCode.DivisionByZero)]
    [InlineData("map([], Bad*)", KatLangErrorCode.DivisionByZero)]
    [InlineData("filter([], Bad*)", KatLangErrorCode.DivisionByZero)]
    [InlineData("reduce([], Bad*, 0)", KatLangErrorCode.DivisionByZero)]
    [InlineData("count(Bad*)", KatLangErrorCode.DivisionByZero)]
    [InlineData("take([1, 2], 1, Bad*)", KatLangErrorCode.DivisionByZero)]
    [InlineData("Bad*.take(1)", KatLangErrorCode.DivisionByZero)]
    [InlineData("take(BadT*)", KatLangErrorCode.TypeMismatch)]
    [InlineData("map([], BadI*)", KatLangErrorCode.BadIndex)]
    [InlineData("count(1, {}*)", KatLangErrorCode.SpreadMissingOutput)]
    [InlineData("map([], {}*)", KatLangErrorCode.SpreadMissingOutput)]
    [InlineData("map([], H*)", KatLangErrorCode.SpreadMissingOutput)]
    public async Task FailedSpread_PropagatesItsOwnFailure(string row, KatLangErrorCode code)
    {
        var observation = await OnEveryRouteAsync(
            "Bad = 1 / 0\nBadT = 1 + 'a'\nBadI = [1]:5\nG = {\n    public X = 1\n}\nH = G + 1\n" + row);
        AssertFails(observation, code);
        Assert.DoesNotContain("but was called with", Message(observation));
    }

    [Fact]
    public async Task FailedSpread_OfACallable_IsItsOwnZeroArgumentRejection_NotAPhantomArity()
    {
        // `take(Inc*)` fails with ArityMismatch either way, so the MESSAGE decides: the spread's
        // own demand of `Inc`, never `take`'s "called with 1 argument". A spread operand is a
        // value position an inferring root would lift `Inc` into, so it sits under a closed list.
        var observation = await OnEveryRouteAsync("Inc(x) = x + 1\nProbe(u) = take(Inc*)\nProbe(0)");
        AssertFails(observation, KatLangErrorCode.ArityMismatch);
        Assert.Contains("Property 'Inc' expects 1 parameter", Message(observation));
        Assert.DoesNotContain("take(collection, count)", Message(observation));
    }

    [Fact]
    public async Task FailedSpread_StopsAssembly_BeforeLaterSlotsAndBeforeArity()
    {
        // Written order: trace(2) ran, the spread failed, trace(3) never ran, and no arity
        // verdict replaced the failure (formerly all three ran and the verdict was arity).
        AssertFails(
            await OnEveryRouteAsync("Bad = trace(1) / 0\ntake(trace(2), Bad*, trace(3))"),
            KatLangErrorCode.DivisionByZero,
            "trace(2)",
            "trace(1)");
        // A failed spread that would have made the count wrong reports its own failure.
        AssertFails(await OnEveryRouteAsync("Bad = 1 / 0\ncount(1, 2, Bad*)"), KatLangErrorCode.DivisionByZero);
    }

    [Fact]
    public async Task FailedSpread_IsTheFirstRaisedFailure_AfterAnEarlierRetainedOne()
    {
        // An earlier VALUE slot's ORDINARY failure is retained, not raised (CALL-03 defers it to
        // binding); the later spread's failure is raised at assembly, so it is the call's.
        AssertFails(
            await OnEveryRouteAsync("Bad = trace(1) / 0\nBadT = 1 + 'a'\ntake(Bad, BadT*)"),
            KatLangErrorCode.TypeMismatch,
            "trace(1)");
    }

    [Theory]
    [InlineData("take(Bad*)", "T(a, b) = take(a, b)\nT(Bad*)")]
    [InlineData("map([], Bad*)", "M(xs, f) = map(xs, f)\nM([], Bad*)")]
    [InlineData("reduce([], Bad*, 0)", "R(xs, f, i) = reduce(xs, f, i)\nR([], Bad*, 0)")]
    [InlineData("count(1, {}*)", "C(xs) = count(xs)\nC(1, {}*)")]
    public async Task FailedSpread_BuiltinAndUserCallAgree(string builtin, string userCall)
    {
        const string prelude = "Bad = trace(1) / 0\n";
        var viaBuiltin = await OnEveryRouteAsync(prelude + builtin);
        var viaUser = await OnEveryRouteAsync(prelude + userCall);
        Assert.Equal("err", viaBuiltin.Kind);
        Assert.Equal(viaBuiltin.Codes, viaUser.Codes);
        Assert.Equal(viaBuiltin.HostCalls, viaUser.HostCalls);
    }

    [Fact]
    public async Task FailedSpread_CannotShiftTheRandomStream()
    {
        // The failing spread draws once and fails; formerly the swallowed failure let the run
        // continue and print a later draw.
        AssertFails(
            await OnEveryRouteAsync("R = [1, 2]:(randomInt(2, 3))\nmap([], R*), randomInt(0, 1000)", seed: 5),
            KatLangErrorCode.BadIndex);
    }

    [Fact]
    public async Task SuccessfulSpread_StillSuppliesExactlyItsItems()
    {
        AssertOk(await OnEveryRouteAsync("P = [1, 2, 3], 2\ntake(P*)"), "L[1, 2]");
        AssertOk(await OnEveryRouteAsync("P = [1, 2, 3], 2\nT(a, b) = take(a, b)\nT(P*)"), "L[1, 2]");
        AssertFails(await OnEveryRouteAsync("count(()*)"), KatLangErrorCode.ArityMismatch);
        // A spread item is an established VALUE in whatever position it lands on.
        AssertOk(await OnEveryRouteAsync("Q = [[4, 5]]\ncount(Q*)"), "2");
    }

    [Fact]
    public async Task SlotRoles_FollowSuppliedPositions_AfterEmptyAndMultiItemSpreads()
    {
        // Written argument indices differ from supplied positions. The next callback must
        // stay inert, and the next initial must be demanded, after either kind of spread.
        AssertOk(await OnEveryRouteAsync("E = ()\nA = tick()\nmap(E*, [], A)"), "L[]");
        AssertOk(await OnEveryRouteAsync("P = [[]]\nA = tick()\nmap(P*, A)"), "L[]");
        AssertOk(
            await OnEveryRouteAsync("P = trace([]), trace(17)\nreduce(P*, trace(9))"),
            "9", "trace(L[])", "trace(17)", "trace(9)");
        AssertFails(
            await OnEveryRouteAsync(Add + "E = ()\nBad = trace(1) / 0\nreduce([], Add, E*, Bad)"),
            KatLangErrorCode.DivisionByZero, "trace(1)");
    }

    [Fact]
    public async Task LaterFailedSpread_PreservesEarlierEffects_AndNeverSuppliesAnItem()
    {
        AssertFails(
            await OnEveryRouteAsync("First = [trace(1)]\nBad = trace(2) / 0\nAlias = Bad\ntake(First*, Alias*, trace(3))"),
            KatLangErrorCode.DivisionByZero, "trace(1)", "trace(2)");
        AssertFails(
            await OnEveryRouteAsync("Fail(x) = trace(x) + 'a'\nmap([[]]*, Fail(2)*, trace(3))"),
            KatLangErrorCode.TypeMismatch, "trace(2)");
        // CALL-03 retains an ordinary value failure until binding. A later spread raises
        // its own failure during assembly; this also holds for an unnamed first slot.
        AssertFails(
            await OnEveryRouteAsync("BadT = trace(2) + 'a'\ntake(trace(1) / 0, BadT*)"),
            KatLangErrorCode.TypeMismatch, "trace(1)", "trace(2)");
    }

    [Theory]
    [InlineData("Box = { public Initial = trace(1) / 0 }\nreduce([], Add, Box.Initial)")]
    [InlineData("Bad = trace(1) / 0\nAlias = Bad\nreduce([], Add, Alias)")]
    [InlineData("Bad(*xs) = trace(1) / 0\nreduce([], Add, Bad)")]
    [InlineData("Bad = trace(1) / 0\nF(i) = G(i)\nG(j) = reduce([], Add, j)\nF(Bad)")]
    public async Task InitialValue_ThroughIdentityAndForwardingRoutes_KeepsOneFailure(string program)
        => AssertFails(await OnEveryRouteAsync(Add + program), KatLangErrorCode.DivisionByZero, "trace(1)");

    [Fact]
    public async Task UnusedDotFallbackCallback_DoesNotEvaluateItsReceiverOrBody()
        => AssertOk(await OnEveryRouteAsync("Callback(x) = trace(x)\nmap([], tick().Callback)"), "L[]");

    // ── 5. Laziness is preserved ────────────────────────────────────────────────────────

    [Fact]
    public async Task Laziness_UndemandedComputationsStayUndemanded()
    {
        // Only callback slots changed: an unselected `if` branch, a zero-iteration loop step,
        // and a user call's ignored parameter keep their own rules.
        AssertOk(await OnEveryRouteAsync("if(true, 7, tick())"), "7");
        AssertOk(await OnEveryRouteAsync("repeat({tick()}, 0, 5)"), "5");
        AssertOk(await OnEveryRouteAsync("Ignore(f) = 0\nIgnore({1 / 0})"), "0");
        // A value slot is still demanded in written order, before binding reports arity
        // (CALL-03): both value items ran, the surplus item too, then the verdict.
        AssertFails(await OnEveryRouteAsync("count(trace(1), trace(2))"), KatLangErrorCode.ArityMismatch, "trace(1)", "trace(2)");
        AssertFails(await OnEveryRouteAsync("count(1 / 0, 2)"), KatLangErrorCode.ArityMismatch);
        // A callback item between value items is skipped, not evaluated.
        AssertFails(
            await OnEveryRouteAsync("map(trace(1), trace(2), trace(3))"),
            KatLangErrorCode.ArityMismatch,
            "trace(1)",
            "trace(3)");
    }

    // ── 6. Metamorphic equivalences ─────────────────────────────────────────────────────

    public static IEnumerable<object[]> ValueSlotExpressions()
    {
        foreach (var expression in new[] { "trace(1) / 0", "trace(4) + 1", "if(trace(true), 1 / 0, 2)", "[trace(1)]:3", "trace(9)" })
            yield return [expression];
    }

    /// <summary>
    /// The initial accumulator is an ordinary value slot: whatever the expression, reading it
    /// through <c>reduce([], Add, V)</c> establishes exactly the outcome and effects of the
    /// ordinary value read <c>V</c> — and of the value slot of <c>contains</c>.
    /// </summary>
    [Theory]
    [MemberData(nameof(ValueSlotExpressions))]
    public async Task InitialSlot_EstablishesTheSameOutcome_AsAnOrdinaryValueRead(string expression)
    {
        var viaReduce = await OnEveryRouteAsync($"{Add}V = {expression}\nreduce([], Add, V)");
        var viaRead = await OnEveryRouteAsync($"V = {expression}\nV");
        Assert.Equal(viaRead.Kind, viaReduce.Kind);
        Assert.Equal(viaRead.Codes, viaReduce.Codes);
        Assert.Equal(viaRead.HostCalls, viaReduce.HostCalls);
        if (viaRead.Kind == "ok")
            Assert.Equal(viaRead.Value, viaReduce.Value);

        var viaWrittenInitial = await OnEveryRouteAsync($"{Add}reduce([], Add, {expression})");
        var viaContains = await OnEveryRouteAsync($"contains([], {expression})");
        Assert.Equal(viaRead.Codes, viaWrittenInitial.Codes);
        Assert.Equal(viaRead.HostCalls, viaWrittenInitial.HostCalls);
        Assert.Equal(viaContains.Codes.Count == 0 ? viaRead.Codes : viaContains.Codes, viaWrittenInitial.Codes);
        Assert.Equal(viaContains.HostCalls, viaWrittenInitial.HostCalls);
    }

    public static IEnumerable<object[]> CallbackExpressions()
    {
        foreach (var callback in new[] { "A", "{tick()}", "(tick())", "tick() + 1", "Box.V", "L", "1 / 0", "{x + tick()}" })
        foreach (var builtin in new[] { "map([], C)", "filter([], C)", "reduce([], C, 7)", "[].filter(C).count" })
            yield return [callback, builtin];
    }

    /// <summary>
    /// Supplying a callback that is never invoked has exactly the effects of a loop step that
    /// is never invoked: none. Only the builtin's ordinary empty result differs.
    /// </summary>
    [Theory]
    [MemberData(nameof(CallbackExpressions))]
    public async Task UnusedCallback_HasTheEffectsOfAZeroIterationLoopStep(string callback, string builtin)
    {
        const string prelude = "A = tick()\nBox = {\n    public V = tick()\n}\nL = L + 1\n";
        var viaBuiltin = await OnEveryRouteAsync(prelude + builtin.Replace("C", callback, StringComparison.Ordinal));
        var viaLoop = await OnEveryRouteAsync(prelude + $"repeat({callback}, 0, 5)");
        Assert.Equal("ok", viaBuiltin.Kind);
        Assert.Equal("ok", viaLoop.Kind);
        Assert.Equal(viaLoop.HostCalls, viaBuiltin.HostCalls);
        Assert.Empty(viaBuiltin.HostCalls);
    }

    public static IEnumerable<object[]> SpreadOperands()
    {
        foreach (var operand in new[] { "Bad", "BadT", "BadI", "{}", "H", "Inc", "(1, 2)", "[3]", "()" })
            yield return [operand];
    }

    /// <summary>
    /// For any builtin <c>B</c> and operand <c>X</c>, <c>B(X*)</c> first obeys the spread law of
    /// a user call <c>F(X*)</c>: the operand's failure is the call's failure (identical code
    /// and effects), or its items are supplied exactly — only then does builtin-specific
    /// binding start.
    /// </summary>
    [Theory]
    [MemberData(nameof(SpreadOperands))]
    public async Task BuiltinSpread_ObeysTheUserCallSpreadLaw(string operand)
    {
        const string prelude = "Bad = trace(1) / 0\nBadT = 1 + 'a'\nBadI = [1]:5\nG = {\n    public X = 1\n}\nH = G + 1\nInc(x) = x + 1\nColl(*xs) = xs\n";
        var viaUser = await OnEveryRouteAsync(prelude + $"Coll({operand}*)");

        // Two builtin shapes where a phantom item would matter: the spread alone decides
        // `take`'s argument count, and the spread lands in `map`'s never-invoked callback slot.
        // Each succeeds exactly when the supplied items complete the fixed signature.
        foreach (var (builtin, completingItems) in new[] { ($"take({operand}*)", 2), ($"map([], {operand}*)", 1) })
        {
            var viaBuiltin = await OnEveryRouteAsync(prelude + builtin);
            if (viaUser.Kind == "err")
            {
                // The operand failed: the builtin reports the very same failure, never an
                // arity verdict derived from a phantom item and never a swallowed failure.
                Assert.Equal("err", viaBuiltin.Kind);
                Assert.Equal(viaUser.Codes, viaBuiltin.Codes);
                Assert.Equal(viaUser.HostCalls, viaBuiltin.HostCalls);
                Assert.DoesNotContain("take(collection, count)", Message(viaBuiltin));
                Assert.DoesNotContain("map(collection, mapper)", Message(viaBuiltin));
            }
            else
            {
                // The operand succeeded: the builtin bound exactly the supplied items.
                var itemCount = viaUser.Value == "L[]" ? 0 : viaUser.Value!.Count(static ch => ch == ',') + 1;
                Assert.Equal(itemCount == completingItems ? "ok" : "err", viaBuiltin.Kind);
            }
        }
    }
}
