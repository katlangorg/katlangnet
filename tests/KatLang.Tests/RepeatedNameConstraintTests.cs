using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Rendering;

namespace KatLang.Tests;

/// <summary>
/// REPEATED NAMES ARE CONSTRAINTS, NOT MERGES (Q-05, decided September 29 2026).
///
/// <para>A repeated parameter name is a compatibility constraint over INDEPENDENTLY supplied
/// arguments. Every occurrence must supply its OWN value; the values must be equal; if a
/// required value's evaluation failed, that failure propagates (another occurrence never
/// supplies a value in its place, and no unrelated pattern or type error replaces it); a
/// callable-only argument cannot satisfy the constraint (its value demand is its own arity
/// rejection); when several occurrences also carry algorithm channels, their callable
/// identities must agree; and channels from different occurrences are never spliced together.
/// Repeated-name matching may RESTRICT a binding; it never manufactures a binding that no
/// individual argument supplied.</para>
///
/// <para>Before the decision the verdict ignored a valueless contribution unless TWO of them met:
/// <c>P(x, x) = x, x(5)</c> with <c>P(Inc, 1)</c> bound <c>x</c> to the value <c>1</c> AND the
/// algorithm <c>Inc</c> (the chimera <c>(1, 6)</c>), <c>Q(Bad, 7)</c> with <c>Bad = 1 / 0</c>
/// returned <c>7</c>, and <c>Q(Bad, Bad)</c> reported a type mismatch instead of the division by
/// zero. The mechanism: a top-level capture whose name repeats at its pattern level needs its
/// slot's own value when it binds (C# <c>BindParameterPattern</c> / <c>RepeatsAtLevel</c>, Lean
/// <c>bindParameterPattern</c> / <c>ParameterPattern.repeatsAtLevel</c>), exactly as a nested
/// sequence-value pattern needs the value it opens; the former "algorithm-only" verdict is
/// deleted because it can no longer arise.</para>
///
/// <para>Evidence: six execution routes (the public sync and async engines, the async twin with an
/// async host operation present, the generic and optimized evaluators, and the forced async
/// twin), which must agree on the outcome, the error message and location, and the exact
/// host-call log (so the number of argument evaluations); plus a generated metamorphic family
/// asserting that every successful binding is observationally the binding of ONE individual
/// argument. Lean: <c>CoreTests/RepeatedNameConstraints.lean</c> and the
/// <c>repeated_capture_*</c> laws in <c>KatLangArityLaws.lean</c>.</para>
/// </summary>
public class RepeatedNameConstraintTests
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

    /// <summary>
    /// One route's observation: <see cref="Outcome"/> (<c>ok &lt;value&gt;</c> or
    /// <c>err &lt;code&gt;: &lt;message&gt;</c>) is what the tests pin; the location and the host-call
    /// log must additionally agree across routes.
    /// </summary>
    internal sealed record Observation(string Outcome, string Location, IReadOnlyList<string> HostCalls)
    {
        public override string ToString()
            => $"{Outcome} @ {Location} host=[{string.Join(",", HostCalls)}]";
    }

    private static async Task<Observation> ObserveAsync(Route route, string source, long? seed)
    {
        var log = new HostLog();
        var options = new RunOptions { HostOperations = OperationsFor(log, route is Route.EngineAsyncTwin or Route.ForcedTwin), RandomSeed = seed };

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
            Route.Generic => Evaluator.RunCountedObserved(program, enableOptimizations: false, hostOperations: options.HostOperations, randomSeed: seed),
            Route.Optimized => Evaluator.RunCountedObserved(program, enableOptimizations: true, hostOperations: options.HostOperations, randomSeed: seed),
            Route.ForcedTwin => await Evaluator.RunCountedObservedAsync(
                program,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                hostOperations: options.HostOperations,
                randomSeed: seed),
            _ => throw new ArgumentOutOfRangeException(nameof(route), route, null),
        };

        return result.IsError
            ? FromError(KatLangError.FromEvalError(result.Error), log)
            : new Observation($"ok {Neutral(result.Value.Value)}", "", [.. log.Calls]);
    }

    private static Observation FromRunResult(RunResult result, HostLog log) => result switch
    {
        RunResult.Success success => new($"ok {Neutral(success.Value)}", "", [.. log.Calls]),
        RunResult.EvalFailure failure => FromError(Assert.Single(failure.Errors), log),
        RunResult.ParseFailure failure => new($"parse {string.Join(",", failure.Errors.Select(static error => error.Code))}", "", [.. log.Calls]),
        RunResult.NoProgramOutput none => new($"none {none.Diagnostic.Code}", "", [.. log.Calls]),
    };

    private static Observation FromError(KatLangError error, HostLog log)
        => new($"err {error.Code}: {error.Message}", error.Span?.ToString() ?? "-", [.. log.Calls]);

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
    /// synchronous engine — outcome, error location, and the exact host-call log (hence the exact
    /// number of argument evaluations). Returns the oracle.
    /// </summary>
    internal static async Task<Observation> OnEveryRouteAsync(string source, long? seed = null)
    {
        var oracle = await ObserveAsync(Route.EngineSync, source, seed);
        Assert.False(oracle.Outcome.StartsWith("parse", StringComparison.Ordinal), $"{oracle}\nsource:\n{source}");
        foreach (var route in Routes.Skip(1))
        {
            var observation = await ObserveAsync(route, source, seed);
            Assert.True(
                oracle.Outcome == observation.Outcome
                    && oracle.Location == observation.Location
                    && oracle.HostCalls.SequenceEqual(observation.HostCalls),
                $"{route}: expected {oracle}, got {observation}\nsource:\n{source}");
        }

        return oracle;
    }

    internal static string Rendered(Observation observation)
        => observation.HostCalls.Count == 0
            ? observation.Outcome
            : $"{observation.Outcome} [{string.Join(",", observation.HostCalls)}]";

    private static void AssertOutcome(string id, string expected, string actual)
        => Assert.True(expected == actual, $"{id}\nexpected: {expected}\nactual:   {actual}");

    // ── Shared outcome spellings ─────────────────────────────────────────────────────

    /// <summary>The evaluation frame of a call to <paramref name="callee"/>.</summary>
    private static string Call(string callee) => $"while evaluating call to {callee}: ";

    /// <summary>The evaluation frame of the dot-call <c>receiver.member(...)</c>.</summary>
    private static string Dot(string receiver, string member) => $"while evaluating dotCall .{member} of {receiver}: ";

    /// <summary>The ordinary unequal-values failure, inside <paramref name="frames"/>.</summary>
    private static string Unequal(string frames = "") => $"err ArityMismatch: {frames}Bad arity";

    /// <summary><c>Inc</c> passed bare: its OWN value demand, the arity rejection of <c>Inc(y)</c>.</summary>
    private static string IncValueDemand(string frames = "")
        => $"err ArityMismatch: {frames}Property 'Inc' expects 1 parameter, but was called with 0 arguments.";

    private static string DivisionByZero(string frames = "") => $"err DivisionByZero: {frames}Division by zero";

    private static string Identity(string frames = "")
        => $"err TypeMismatch: {frames}Type mismatch: Repeated bind equality requires the same callable identity";

    private const string Inc = "Inc(y) = y + 1\n";

    private const string Bad = "Bad = trace(1) / 0\n";

    private const string BadTraced = " [trace(1)]";

    // ── 1. The regression matrix on every route ──────────────────────────────────────

    /// <summary>
    /// (id, source, outcome with host calls, on every route). The error rows pin the complete
    /// user-visible message, call frame included: a repeated-name failure is reported at the
    /// call whose binding needed the value. Rows marked "formerly" changed with the decision.
    /// </summary>
    public static TheoryData<string, string, string> Programs => new()
    {
        // 1. Ordinary equal values match.
        { "equal-values", "P(x, x) = x\nP(7, 7)", "ok 7" },
        { "equal-values-traced", "P(x, x) = x\nP(trace(7), trace(7))", "ok 7 [trace(7),trace(7)]" },

        // 2. Unequal values do not match (the language's normal repeated-name failure).
        { "unequal-values", "P(x, x) = x\nP(7, 8)", Unequal(Call("P")) },
        { "unequal-ticks", "P(x, x) = x\nP(tick(), tick())", Unequal(Call("P")) + " [tick#1,tick#2]" },

        // 3. A callable-only argument beside a value: never a dual-channel binding, both orders.
        // Formerly `ok S[1, 6]`: x read the value 1 and x(5) invoked Inc.
        { "callable-then-value", Inc + "P(x, x) = x, x(5)\nP(Inc, 1)", IncValueDemand(Call("P")) },
        { "value-then-callable", Inc + "P(x, x) = x, x(5)\nP(1, Inc)", IncValueDemand(Call("P")) },
        // Formerly `ok 0` and `ok 2`: the binding itself succeeded.
        { "callable-body-ignores-x", Inc + "P(x, x) = 0\nP(Inc, 1)", IncValueDemand(Call("P")) },
        { "value-then-callable-invoked", Inc + "P(x, x) = x(1)\nP(1, Inc)", IncValueDemand(Call("P")) },
        // Formerly the "algorithm-only arguments" type mismatch, which named no argument.
        { "callable-twice", Inc + "P(x, x) = 0\nP(Inc, Inc)", IncValueDemand(Call("P")) },

        // 4. A failed value beside a successful one: the failure propagates, in evaluation order,
        // after exactly ONE evaluation of the failed argument. Formerly `ok 7`.
        { "failed-then-value", Bad + "Q(x, x) = x\nQ(Bad, 7)", DivisionByZero(Call("Q")) + BadTraced },
        { "value-then-failed", Bad + "Q(x, x) = x\nQ(7, Bad)", DivisionByZero(Call("Q")) + BadTraced },
        { "failed-then-value-read-twice", Bad + "Q(x, x) = x, x.string\nQ(Bad, 7)", DivisionByZero(Call("Q")) + BadTraced },
        { "failed-block-then-value", "Q(x, x) = x\nQ({trace(1) / 0}, 7)", DivisionByZero(Call("Q")) + BadTraced },
        { "value-then-failed-block", "Q(x, x) = x\nQ(7, {trace(1) / 0})", DivisionByZero(Call("Q")) + BadTraced },

        // 5. Two failed values: the FIRST-raised failure (arguments evaluate left to right, once
        // each), never an unrelated repeated-name diagnostic. Formerly the "algorithm-only" type
        // mismatch masked both.
        { "two-failures", Bad + "Missing = [trace(2)]:5\nQ(x, x) = x\nQ(Bad, Missing)", DivisionByZero(Call("Q")) + " [trace(1),trace(2)]" },
        { "two-failures-reversed", Bad + "Missing = [trace(2)]:5\nQ(x, x) = x\nQ(Missing, Bad)", $"err BadIndex: {Call("Q")}Bad index [trace(2),trace(1)]" },
        { "same-failure-twice", Bad + "Q(x, x) = 0\nQ(Bad, Bad)", DivisionByZero(Call("Q")) + " [trace(1),trace(1)]" },

        // 6. Arguments that each carry BOTH channels: equal values and one callable identity bind
        // (and invoke that callable); equal values with two identities reject. One algorithm
        // channel may accompany an equal value its OWN argument supplied, in both orders.
        { "same-identity", "A = 5\nP(f, f) = f, f()\nP(A, A)", "ok S[5, 5]" },
        { "different-identity", "A = 5\nB = 5\nP(f, f) = f\nP(A, B)", Identity(Call("P")) },
        { "different-identity-invoked", "A(*xs) = 5\nB(*xs) = 5 + xs.count\nP(f, f) = f(1)\nP(B, A)", Identity(Call("P")) },
        { "one-channel-then-value", "A = 5\nP(f, f) = f, f()\nP(A, 5)", "ok S[5, 5]" },
        { "value-then-one-channel", "A = 5\nP(f, f) = f, f()\nP(5, A)", "ok S[5, 5]" },
        // The matching adds no evaluation: Tr's cached value is read once for both slots, and only
        // the EXPLICIT invocation f(1) runs Tr again.
        { "matching-adds-no-evaluation", "Tr(*xs) = trace(5)\nP(f, f) = f, f(1)\nP(Tr, Tr)", "ok S[5, 5] [trace(5),trace(5)]" },
        { "matching-adds-no-evaluation-mixed", "Tr(*xs) = trace(5)\nP(f, f) = f, f(1)\nP(5, Tr)", "ok S[5, 5] [trace(5),trace(5)]" },

        // 7. Nested patterns: an occurrence inside a group never completes a top-level one.
        // Formerly `ok 9` and `ok 8`.
        { "nested-equal", "N(x, (x, y)) = y\nN(7, (7, 8))", "ok 8" },
        { "nested-unequal", "N(x, (x, y)) = y\nN(6, (7, 8))", Unequal(Call("N")) },
        { "nested-callable", Inc + "N(x, (x, y)) = x(y)\nN(Inc, (7, 8))", IncValueDemand(Call("N")) },
        { "nested-failed", Bad + "N(x, (x, y)) = y\nN(Bad, (7, 8))", DivisionByZero(Call("N")) + BadTraced },
        { "nested-inside-one-group", "M((x, x)) = x\nM((7, 7))", "ok 7" },
        { "nested-inside-one-group-unequal", "M((x, x)) = x\nM((7, 8))", Unequal(Call("M")) },

        // 8. Clause families: every argument's value is required before a clause is tried, so a
        // failed or callable-only argument is its own failure, never a fall-through. Family
        // binders are values only (PAT-07): distinct callables with equal values match (PV-43).
        { "family-equal", "E(x, x) = true\nE(x, y) = false\nE(7, 7)", "ok true" },
        { "family-unequal", "E(x, x) = true\nE(x, y) = false\nE(7, 8)", "ok false" },
        { "family-failed-first", Bad + "E(x, x) = true\nE(x, y) = false\nE(Bad, 7)", DivisionByZero(Call("E")) + BadTraced },
        { "family-failed-second", Bad + "E(x, x) = true\nE(x, y) = false\nE(7, Bad)", DivisionByZero(Call("E")) + BadTraced },
        { "family-callable", Inc + "E(x, x) = true\nE(x, y) = false\nE(Inc, 1)", IncValueDemand(Call("E")) },
        { "family-distinct-callables", "A = 5\nB = 5\nE(x, x) = true\nE(x, y) = false\nE(A, B)", "ok true" },

        // 9. Lists and sequences: the ONE structural, kind-sensitive value equality.
        { "list-equal", "P(x, x) = x\nP([1], [1])", "ok L[1]" },
        { "list-vs-scalar", "P(x, x) = x\nP([1], 1)", Unequal(Call("P")) },
        { "sequence-equal", "P(x, x) = x\nP((1, 2), (1, 2))", "ok S[1, 2]" },
        { "list-vs-sequence", "P(x, x) = x\nP([1, 2], (1, 2))", Unequal(Call("P")) },
        { "empty-list-vs-empty-sequence", "P(x, x) = 0\nP([], ())", Unequal(Call("P")) },
        { "family-list-vs-scalar", "E(x, x) = true\nE(x, y) = false\nE([1], 1)", "ok false" },

        // 10. Collected parameters: the name repeats across the collector.
        { "collector-equal", "C(x, *r, x) = x, r\nC(7, 9, 7)", "ok S[7, L[9]]" },
        { "collector-callable", Inc + "C(x, *r, x) = x\nC(Inc, 9, 1)", IncValueDemand(Call("C")) },
        { "collector-failed", Bad + "C(x, *r, x) = x\nC(1, 9, Bad)", DivisionByZero(Call("C")) + BadTraced },

        // 11. Three occurrences: every one needs its own value, wherever the callable stands.
        { "three-callable-last", "A = 5\n" + Inc + "T(x, x, x) = x\nT(A, 5, Inc)", IncValueDemand(Call("T")) },
        { "three-callable-first", "A = 5\n" + Inc + "T(x, x, x) = x\nT(Inc, A, 5)", IncValueDemand(Call("T")) },
        { "three-compatible", "A = 5\nT(x, x, x) = x\nT(5, A, A)", "ok 5" },

        // 12. A valueless occurrence is a BINDING failure: it precedes the level's verdicts
        // wherever the unequal name stands.
        { "binding-failure-before-verdict", Bad + "Q2(x, x, y, y) = 0\nQ2(Bad, 7, 1, 2)", DivisionByZero(Call("Q2")) + BadTraced },
        { "binding-failure-before-verdict-late", Bad + "Q2(x, x, y, y) = 0\nQ2(1, 2, Bad, 7)", DivisionByZero(Call("Q2")) + BadTraced },
    };

    [Theory]
    [MemberData(nameof(Programs))]
    public async Task RepeatedNameLaw_HoldsOnEveryRoute(string id, string source, string expected)
        => AssertOutcome(id, expected, Rendered(await OnEveryRouteAsync(source)));

    // ── 2. Equivalent routes cannot reconstruct the old splice ──────────────────────

    /// <summary>
    /// Every equivalent spelling of the chimera and of the repaired failure: argument order,
    /// aliases, dot-call versus lexical call, forwarding (once and twice into one parameter),
    /// a nested property, opened and member-resolved callables, and explicit calls versus bare
    /// references.
    /// </summary>
    public static TheoryData<string, string, string> EquivalentRoutes => new()
    {
        // Dot-call is the ordinary call with the receiver as the leading argument.
        { "dot-callable-receiver", Inc + "P(x, x) = x, x(5)\nInc.P(1)", IncValueDemand(Dot("Inc", "P")) },
        { "dot-callable-argument", Inc + "P(x, x) = x, x(5)\n1.P(Inc)", IncValueDemand(Dot("1", "P")) },
        { "dot-failed-receiver", Bad + "Q(x, x) = x\nBad.Q(7)", DivisionByZero(Dot("Bad", "Q")) + BadTraced },
        { "dot-failed-argument", Bad + "Q(x, x) = x\n7.Q(Bad)", DivisionByZero(Dot("7", "Q")) + BadTraced },

        // An alias of a callable that requires arguments is that callable (it lifts), and an
        // alias of a failing value is that failing value.
        { "alias-callable", Inc + "J = Inc\nP(x, x) = x, x(5)\nP(J, 1)",
            $"err ArityMismatch: {Call("P")}Property 'J' expects 1 parameter, but was called with 0 arguments." },
        { "alias-failed", Bad + "AliasBad = Bad\nQ(x, x) = x\nQ(AliasBad, 7)", DivisionByZero(Call("Q")) + BadTraced },

        // Forwarding carries each parameter's established outcome; the failed argument is
        // evaluated once, at the outer call.
        { "forward-callable-first", Inc + "P(x, x) = x, x(5)\nFwd(a, b) = P(a, b)\nFwd(Inc, 1)", IncValueDemand(Call("Fwd") + Call("P")) },
        { "forward-callable-second", Inc + "P(x, x) = x, x(5)\nFwd(a, b) = P(a, b)\nFwd(1, Inc)", IncValueDemand(Call("Fwd") + Call("P")) },
        { "forward-failed", Bad + "Q(x, x) = x\nFwd(a, b) = Q(a, b)\nFwd(Bad, 7)", DivisionByZero(Call("Fwd") + Call("Q")) + BadTraced },
        { "forward-one-parameter-twice-callable", Inc + "P(x, x) = x\nPass(g) = P(g, g)\nPass(Inc)", IncValueDemand(Call("Pass") + Call("P")) },
        { "forward-one-parameter-twice-failed", Bad + "Q(x, x) = x\nPass(g) = Q(g, g)\nPass(Bad)", DivisionByZero(Call("Pass") + Call("Q")) + BadTraced },
        { "forward-one-parameter-twice-valued", "A = 5\nP(f, f) = f, f()\nPass(g) = P(g, g)\nPass(A)", "ok S[5, 5]" },

        // A nested property, and callables resolved through `open` or a structural member.
        { "nested-property", Inc + "Outer = {\n    P(x, x) = x, x(5)\n    P(Inc, 1)\n}\nOuter", IncValueDemand(Call("P")) },
        { "opened-callable", "open Lib\nLib = {\n    public Inc(y) = y + 1\n}\nP(x, x) = x, x(5)\nP(Inc, 1)", IncValueDemand(Call("P")) },
        { "member-callable", "Lib = {\n    public Inc(y) = y + 1\n}\nP(x, x) = x, x(5)\nP(Lib.Inc, 1)",
            $"err ArityMismatch: {Call("P")}Property 'Inc' on `Lib` expects 1 parameter, but was called with 0 arguments." },
        { "member-failed", "Lib = {\n    public Bad = trace(1) / 0\n}\nQ(x, x) = x\nQ(Lib.Bad, 7)", DivisionByZero(Call("Q") + Dot("Lib", "Bad")) + BadTraced },

        // An explicit call supplies a value; the bare reference does not.
        { "explicit-call-is-a-value", Inc + "P(x, x) = x\nP(Inc(1), 2)", "ok 2" },
        // A callable that works with no arguments IS a value, and its channel accompanies it.
        { "zero-argument-callable-is-a-value", "Only(*xs) = 5 + xs.count\nP(f, f) = f, f(1)\nP(Only, 5)", "ok S[5, 6]" },
        { "zero-argument-callable-is-a-value-reversed", "Only(*xs) = 5 + xs.count\nP(f, f) = f, f(1)\nP(5, Only)", "ok S[5, 6]" },
    };

    [Theory]
    [MemberData(nameof(EquivalentRoutes))]
    public async Task EquivalentRoutes_CannotReconstructASplicedBinding(string id, string source, string expected)
        => AssertOutcome(id, expected, Rendered(await OnEveryRouteAsync(source)));

    /// <summary>
    /// The hostile review of the law: every further way a repeated-name callee can be reached
    /// with a valueless argument — higher-order invocation, a loop step (the optimized route
    /// plans loops), a fused filter-count predicate and a map callback (the sequence-pipeline
    /// optimizer), an opened or structurally selected callee — and the latency boundary: a
    /// failed argument whose value no pattern requires stays latent, so the first REQUIRED
    /// value decides. Every row agrees on six routes; before Q-05 each spliced row succeeded.
    /// </summary>
    public static TheoryData<string, string, string> HostileReviewRoutes => new()
    {
        // Formerly `ok S[1, 6]` through the higher-order parameter.
        { "higher-order-invocation", Inc + "P(x, x) = x, x(5)\nApply(f, a, b) = f(a, b)\nApply(P, Inc, 1)",
            IncValueDemand(Call("Apply") + Call("f")) },
        // Formerly `ok 2`: each step added the spliced value 1.
        { "loop-step-body", Inc + "P(x, x) = x\nStep(s) = s + P(1, Inc)\nrepeat(Step, 2, 0)",
            IncValueDemand(Call("repeat") + Call("P")) },
        // Formerly `ok 2` (fused filter -> count) and `ok L[1, 2]`.
        { "fused-filter-count-predicate", Inc + "P(x, x) = x\n[1, 2].filter({P(x, Inc) == x}).count",
            IncValueDemand(Dot("[1, 2].filter(...)", "count") + Dot("[1, 2]", "filter")
                + "while evaluating filter predicate for item 0: 1 (filter passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact): "
                + Call("P")) },
        { "map-callback", Inc + "P(x, x) = x\nmap([1, 2], {P(x, Inc)})",
            IncValueDemand(Call("map")
                + "while evaluating map transform (map passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact): "
                + Call("P")) },
        // The callee itself resolved through `open` or as a structural member.
        { "opened-callee", "open Lib\nLib = {\n    public P(x, x) = x, x(5)\n}\n" + Inc + "P(Inc, 1)", IncValueDemand(Call("P")) },
        { "member-callee", "Lib = {\n    public P(x, x) = x, x(5)\n}\n" + Inc + "Lib.P(Inc, 1)", IncValueDemand(Dot("Lib", "P")) },
        // A failed argument no pattern requires stays latent (CALL-06): the first REQUIRED
        // value decides, although `Bad` was evaluated (and failed) first.
        { "latent-failure-is-not-required", Bad + Inc + "P(y, x, x) = x\nP(Bad, Inc, 1)", IncValueDemand(Call("P")) + BadTraced },
        { "latent-failure-read-later", Bad + "P(y, x, x) = x, y\nP(Bad, 7, 7)", DivisionByZero(Call("P")) + BadTraced },
        // A callable that works with no arguments IS value-shaped: its own failed read propagates.
        { "value-shaped-callable-failure", "Only(*xs) = 1 / 0\nP(x, x) = x\nP(Only, 1)", DivisionByZero(Call("P")) },
        // A written block needing an input has no value: its own failure, never a match.
        { "block-with-implicit-input", "P(x, x) = x\nP({y + 1}, 1)",
            $"err UnresolvedImplicitParams: {Call("P")}Identifier 'y' does not resolve to a property or other visible name here, so KatLang interprets it as an implicit parameter. Its value is provided by the caller. No argument was provided, so the program cannot be executed (expected 1 argument, got 0)." },
        { "string-receiver-read", Bad + "P(x, x) = x.string\nP(Bad, 7)", DivisionByZero(Call("P")) + BadTraced },
    };

    [Theory]
    [MemberData(nameof(HostileReviewRoutes))]
    public async Task HostileReview_NoRouteReconstructsASplicedBinding(string id, string source, string expected)
        => AssertOutcome(id, expected, Rendered(await OnEveryRouteAsync(source)));

    /// <summary>
    /// Builtin and Math callables passed bare are callable-only arguments too: each reports its
    /// own value demand, never a binding paired with the other occurrence's value.
    /// </summary>
    [Theory]
    [InlineData("count")]
    [InlineData("abs")]
    [InlineData("Math.Abs")]
    public async Task BuiltinCallables_AreNotValuesForARepeatedName(string callable)
    {
        foreach (var call in new[] { $"P({callable}, 1)", $"P(1, {callable})" })
        {
            var repeated = await OnEveryRouteAsync($"P(x, x) = x, x(-5)\n{call}");
            var alone = await OnEveryRouteAsync($"V(x) = x + 0\nV({callable})");
            Assert.StartsWith("err ", repeated.Outcome, StringComparison.Ordinal);
            Assert.Equal(Innermost(alone.Outcome), Innermost(repeated.Outcome));
        }
    }

    // ── 3. The generated no-manufactured-binding family ──────────────────────────────

    /// <summary>
    /// The contributions: plain values (<c>5</c>, <c>6</c>), zero-parameter properties that carry
    /// both channels (<c>A</c>, and <c>B</c> — the same value from a different callable), a
    /// callable that works with no arguments (<c>Only</c>), a callable-only argument
    /// (<c>Inc</c>), a failing value (<c>Bad</c>), and a written block (<c>{5}</c>, a fresh callable
    /// at every occurrence).
    /// </summary>
    private static readonly string[] Contributions = ["5", "6", "A", "B", "Only", "Inc", "Bad", "{5}"];

    private const string Vocabulary =
        "A = 5\nB = 2 + 3\nOnly(*xs) = 5 + xs.count\nInc(y) = y + 1\nBad = trace(1) / 0\n";

    /// <summary>The three reads of a binding: its value, a zero-argument and a one-argument invocation.</summary>
    private static readonly string[] Reads = ["f", "f()", "f(1)"];

    public static TheoryData<string, string> ContributionPairs()
    {
        var data = new TheoryData<string, string>();
        foreach (var first in Contributions)
        foreach (var second in Contributions)
            data.Add(first, second);
        return data;
    }

    /// <summary>
    /// THE LAW as a metamorphic relation. For every ordered pair (a, b), every read R of the
    /// repeated name, and three spellings (the direct call, the dot-call, and forwarding through
    /// a flat helper), <c>P(a, b)</c> with <c>P(f, f) = R</c>:
    /// <list type="bullet">
    /// <item>fails with a's own value failure when a supplies no value, else with b's;</item>
    /// <item>else fails with the ordinary unequal-values error when their values differ;</item>
    /// <item>else fails with the callable-identity error when both carry DIFFERENT callables;</item>
    /// <item>else reads exactly what ONE individual argument supplies — <c>S(x)</c> with
    /// <c>S(f) = R</c>, for the argument x that carries an algorithm channel (either, when both
    /// carry the same one; a, when neither does).</item>
    /// </list>
    /// So a successful binding is always one some argument supplied: never one argument's value
    /// with another's algorithm, and never a failure repaired by another occurrence.
    /// </summary>
    [Theory]
    [MemberData(nameof(ContributionPairs))]
    public async Task EverySuccessfulBinding_IsTheBindingOfOneArgument(string a, string b)
    {
        var valueOfA = await ValueFailureOf(a);
        var valueOfB = await ValueFailureOf(b);
        foreach (var read in Reads)
        {
            string expected;
            if (valueOfA is not null)
                expected = valueOfA;
            else if (valueOfB is not null)
                expected = valueOfB;
            else if ((await OnEveryRouteAsync($"{Vocabulary}Eq(x, y) = x == y\nEq({a}, {b})")).Outcome != "ok true")
                expected = Unequal();
            else if (CarriesCallable(a) && CarriesCallable(b) && !(a == b && a != "{5}"))
                expected = Identity();
            else
                expected = Innermost((await OnEveryRouteAsync(
                    $"{Vocabulary}S(f) = {read}\nS({(CarriesCallable(a) || !CarriesCallable(b) ? a : b)})")).Outcome);

            var spellings = new[]
            {
                $"{Vocabulary}P(f, f) = {read}\nP({a}, {b})",
                $"{Vocabulary}P(f, f) = {read}\n{a}.P({b})",
                $"{Vocabulary}P(f, f) = {read}\nFwd(u, v) = P(u, v)\nFwd({a}, {b})",
            };
            foreach (var spelling in spellings)
            {
                var actual = Innermost((await OnEveryRouteAsync(spelling)).Outcome);
                Assert.True(expected == actual, $"expected: {expected}\nactual:   {actual}\nsource:\n{spelling}");
            }
        }
    }

    /// <summary>The argument's own value failure (<c>V(x) = x</c> reads it), or <c>null</c> when it has a value.</summary>
    private static async Task<string?> ValueFailureOf(string argument)
    {
        var outcome = Innermost((await OnEveryRouteAsync($"{Vocabulary}V(x) = x\nV({argument})")).Outcome);
        return outcome.StartsWith("ok ", StringComparison.Ordinal) ? null : outcome;
    }

    /// <summary>
    /// An outcome without its evaluation frames (<c>while evaluating call to P: </c>): the value,
    /// or the error code with the innermost message — what differs between <c>P(a, b)</c> and the
    /// single-argument references is only the callee frame around it.
    /// </summary>
    private static string Innermost(string outcome)
    {
        if (!outcome.StartsWith("err ", StringComparison.Ordinal))
            return outcome;

        var separator = outcome.IndexOf(": ", StringComparison.Ordinal);
        var message = outcome[(separator + 2)..];
        while (message.StartsWith("while evaluating ", StringComparison.Ordinal)
            && message.IndexOf(": ", StringComparison.Ordinal) is var end and > 0)
            message = message[(end + 2)..];
        return $"{outcome[..separator]}: {message}";
    }

    /// <summary>Whether the written argument also binds an algorithm channel.</summary>
    private static bool CarriesCallable(string argument) => argument is not ("5" or "6");
}
