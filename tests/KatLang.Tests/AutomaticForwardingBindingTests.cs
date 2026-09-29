using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Rendering;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// AUTOMATIC PARAMETER FORWARDING MUST NOT CHANGE WHAT AN EXISTING NAME REFERS TO (Q-04, decided
/// September 28 2026; formerly PV-01).
///
/// <para>When a formula uses another formula that still needs an input <c>n</c>, KatLang hands
/// that input on automatically (implicit lifting). The decided law has two halves:</para>
/// <list type="number">
/// <item><b>Forwarding reuses parameter bindings only.</b> The input is supplied by the binding a
/// WRITTEN parameter reference of <c>n</c> would already denote at the referencing body: that
/// body's own written or inferred parameter, or an accessible captured parameter of an enclosing
/// owner, a clause-branch binder included. Properties, opened names, module members and prelude
/// builtins are never forwarded as parameters. Only when no such binding exists does the body
/// receive a NEW (forwarded) parameter — an inferring body; a closed parameter list refuses.</item>
/// <item><b>A forwarded parameter never changes a written name.</b> It is an ordinary parameter
/// for every caller, but it is never what a written name refers to: name resolution decides every
/// written name first, and forwarding never re-selects a binding afterwards.</item>
/// </list>
///
/// <para>Before the decision, referencing <c>A = y + 1</c> inside <c>G</c> gave <c>G</c> its own
/// parameter <c>y</c> even though <c>G</c> already read the enclosing <c>F</c>'s <c>y</c>, and the
/// former ownership-completion pass then made every same-named reference denote the new parameter:
/// <c>F(3)</c> gave <c>100101</c> where the inlined helper gives <c>3004</c>. The same pass rebound
/// references to properties, opened members and builtins whenever forwarding added a same-named
/// parameter to an enclosing body. Both are gone.</para>
///
/// <para>Evidence: six execution routes (the public sync and async engines, the async twin with an
/// async host operation present, the generic and optimized evaluators, and the forced async twin),
/// host-call counts, the elaborated tree, the editor model's resolution of every written name, and
/// generated metamorphic families. Lean: <c>forwardingSource</c>, the laws beside it, and
/// <c>CoreTests/ForwardingBindings.lean</c>; the Lean programs of the <c>forwarding-*</c> spec cases
/// are derived from these elaborations.</para>
/// </summary>
public class AutomaticForwardingBindingTests
{
    // ── Execution routes ─────────────────────────────────────────────────────────────

    public enum Route
    {
        EngineSync,
        EngineAsync,
        EngineAsyncTwin,
        Generic,
        Optimized,
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

    private static async Task<string> ObserveAsync(Route route, string source)
    {
        var log = new HostLog();
        var options = new RunOptions { HostOperations = OperationsFor(log, route is Route.EngineAsyncTwin or Route.ForcedTwin) };

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
            Route.Generic => Evaluator.RunCountedObserved(program, enableOptimizations: false, hostOperations: options.HostOperations),
            Route.Optimized => Evaluator.RunCountedObserved(program, enableOptimizations: true, hostOperations: options.HostOperations),
            Route.ForcedTwin => await Evaluator.RunCountedObservedAsync(
                program,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                hostOperations: options.HostOperations),
            _ => throw new ArgumentOutOfRangeException(nameof(route), route, null),
        };

        return result.IsError
            ? $"err {KatLangError.FromEvalError(result.Error).Code}{Host(log)}"
            : $"ok {Neutral(result.Value.Value)}{Host(log)}";
    }

    private static string FromRunResult(RunResult result, HostLog log) => result switch
    {
        RunResult.Success success => $"ok {Neutral(success.Value)}{Host(log)}",
        RunResult.EvalFailure failure => $"err {string.Join(",", failure.Errors.Select(static error => error.Code))}{Host(log)}",
        RunResult.ParseFailure failure => $"parse {string.Join(",", failure.Errors.Select(static error => error.Code))}",
        RunResult.NoProgramOutput none => $"none {none.Diagnostic.Code}",
    };

    private static string Host(HostLog log) => log.Calls.Count == 0 ? "" : " [" + string.Join(",", log.Calls) + "]";

    private static string Neutral(Result value) => value switch
    {
        Result.Atom atom => ValueTextRenderer.FormatNumberInvariant(atom.Value),
        Result.Str text => "'" + text.Value + "'",
        Result.Bool boolean => boolean.Value ? "true" : "false",
        Result.SequenceValue sequence => "S[" + string.Join(", ", sequence.Items.Select(Neutral)) + "]",
        Result.ListValue list => "L[" + string.Join(", ", list.Items.Select(Neutral)) + "]",
    };

    /// <summary>
    /// Runs <paramref name="source"/> on every route and requires each to agree with the synchronous
    /// engine, value and host-call log alike; a front-end rejection is observed once. Returns the oracle.
    /// </summary>
    private static async Task<string> OnEveryRouteAsync(string source)
    {
        var oracle = await ObserveAsync(Route.EngineSync, source);
        if (oracle.StartsWith("parse", StringComparison.Ordinal))
            return oracle;

        foreach (var route in Routes.Skip(1))
            Assert.Equal(oracle, await ObserveAsync(route, source));
        return oracle;
    }

    // ── 1. The law on every route ────────────────────────────────────────────────────

    /// <summary>(id, source, outcome on every route). Rows marked "formerly" changed with the decision.</summary>
    public static TheoryData<string, string, string> Programs => new()
    {
        // A. A captured ANCESTOR parameter is reused: the written `y` in G keeps denoting F's `y`.
        // Formerly 100101 — G acquired its own `y`, the written one followed it, and H(100) fed it.
        { "pv01-captured-ancestor-parameter", "A = y + 1\nF(y) = {\n    G = y * 1000 + A\n    H(y) = G\n    H(100)\n}\nF(3)", "ok 3004" },
        { "pv01-inlined-control", "F(y) = {\n    G = y * 1000 + (y + 1)\n    H(y) = G\n    H(100)\n}\nF(3)", "ok 3004" },
        { "pv01-without-the-helper", "F(y) = {\n    G = y * 1000\n    H(y) = G\n    H(100)\n}\nF(3)", "ok 3000" },
        // Formerly ArityMismatch: the helper took a parameter, so a neutral `if` argument could not read it.
        { "local-helper-read-as-a-value", "Area = width * height\nReport(width, height) = {\n    Doubled = Area * 2\n    if(width > 1, Doubled, 0)\n}\nReport(3, 4)", "ok 24" },
        { "reused-helper-in-a-neutral-argument", "A = y + 1\nF(y) = {\n    G = A * 10\n    if(y > 0, G, 0)\n}\nF(3)", "ok 40" },
        { "reused-helper-in-a-lifting-row", "A = y + 1\nF(y) = {\n    G = A * 10\n    G\n}\nF(3)", "ok 40" },
        // The inferred ancestor parameter is reused the same way (formerly 100104).
        { "captured-inferred-ancestor-parameter", "A = y + 1\nB = { G = y * 1000 + A\n  H(y) = G\n  H(100) + y }\nB(3)", "ok 3007" },

        // B/C. The body's OWN parameter — written or inferred — is reused as always.
        { "own-explicit-parameter", "A = y + 1\nF(y) = A * 10\nF(3)", "ok 40" },
        { "own-inferred-parameter", "A = y + 1\nG = y * 100 + A\nG(3)", "ok 304" },

        // D. Several nested levels: the original binding survives every forwarding layer.
        { "nested-levels", "A = y + 1\nOuter(y) = {\n    Mid = {\n        Inner = y * 1000 + A\n        Inner\n    }\n    Mid\n}\nOuter(3)", "ok 3004" },
        { "transitive-helper-chain", "A = y + 1\nB = A * 2\nF(y) = {\n    G = B + y\n    if(true, G, 0)\n}\nF(3)", "ok 11" },
        { "inferred-intermediate-owner", "A = y + 1\nOuter = {\n    Mid = {\n        G = A * 2\n        G\n    }\n    Mid + y\n}\nOuter(3)", "ok 11" },
        // Inner reads Outer's `y`; H's own written `y` is unrelated to it (formerly 51).
        { "deeper-owner-does-not-leak-its-parameter", "A = y + 1\nOuter(y) = {\n    Mid = {\n        Inner = A\n        H(y) = Inner\n        H(50)\n    }\n    Mid\n}\nOuter(3)", "ok 4" },

        // E. A clause-branch binder is a parameter binding like any other (formerly ArityMismatch / 990).
        { "branch-binder-reused", "A = n * 10\nF(0) = 0\nF(n) = {\n    G = A + 1\n    if(n > 0, G, 0)\n}\nF(2)", "ok 21" },
        { "branch-binder-not-rebound", "A = n * 10\nF(0) = 0\nF(n) = {\n    G = n * 100 + A\n    H(n) = G\n    H(9)\n}\nF(2)", "ok 220" },
        { "pv01-in-a-branch-body", "A = y + 1\nF(0) = 0\nF(y) = {\n    G = y * 1000 + A\n    H(y) = G\n    H(100)\n}\nF(3)", "ok 3004" },

        // F. A genuinely unbound dependency still becomes a (forwarded) parameter.
        { "genuine-dependency-at-the-root-level", "A = y + 1\nG = A * 2\nG(5)", "ok 12" },
        { "genuine-dependency-in-a-block", "A = y + 1\nF = {\n    G = A * 2\n    G\n}\nF(5)", "ok 12" },

        // G. Explicit shadowing stays intentional.
        { "explicit-shadowing", "Outer(y) = {\n    Inner(y) = y * 2\n    Inner(10) + y\n}\nOuter(3)", "ok 23" },
        { "explicit-shadowing-forwards-the-inner-parameter", "A = y + 1\nOuter(y) = {\n    Inner(y) = A * 2\n    Inner(10) + y\n}\nOuter(3)", "ok 25" },

        // H. A same-named PROPERTY is never forwarded, and a reference to it is never rebound.
        { "root-property-is-not-forwarded", "v = 99\nNeed(v) = v\nOuter = Need + 1\nOuter(7)", "ok 8" },
        // Formerly 14: Inner's written `v` was rebound to Outer's forwarded `v`.
        { "property-reference-is-not-rebound", "v = 99\nNeed(v) = v\nOuter = { Inner = v\n  Inner + Need }\nOuter(7)", "ok 106" },
        { "property-reference-keeps-its-own-forwarding", "v = x + 99\nOuter = { Inner = v\nNeed(v) = v\nInner + Need }\nOuter(2, 7)", "ok 108" },
        // The former ownership-completion pins, each rebinding a written reference (formerly 17, 4, 2, 8):
        { "grouped-forwarding-leaves-the-property-reference", "v = x + 99\nOuter = { Inner = v\nNeed((v, w)) = v + w\nInner + Need }\nOuter(2, (7, 3))", "ok 111" },
        { "collecting-forwarding-leaves-the-property-reference", "v = 99\nNeed(q, *v) = v.count\nOuter = { Inner = v.count\nInner + Need }\nOuter(0, 7, 8)", "ok 3" },
        { "called-property-reference-is-not-rebound", "v(x) = 99\nNeed(v) = 0\nOuter = { Inner = v(1)\nInner + Need }\nOuter({x + 1})", "ok 99" },
        { "dot-receiver-reference-is-not-rebound", "v = { Member = 99 }\nMember(x) = x + 1\nNeed(v) = 0\nOuter = { Inner = v.Member\nInner + Need }\nOuter(7)", "ok 99" },
        // The written `v` stays the root property `v = x + 1`, whose `x` the closed list cannot forward.
        { "strict-property-reference-stays-blocked", "v = x + 1\nNeed(v) = 0\nOuter = { Inner(q) = Math.Abs(v)\nInner(0) + Need }\nOuter(7)", "parse UndeclaredIdentifier" },
        { "same-owner-property-collides", "A = y + 1\nF = { y = 3\n  A }\nF", "parse ParameterPropertyCollision" },

        // I. An OPENED member is never forwarded, and a reference to it is never rebound (formerly 14).
        { "opened-member-is-not-forwarded", "Lib = { public v = 99 }\nNeed(v) = v\nOuter = {\n    open Lib\n    Need + 1\n}\nOuter(7)", "ok 8" },
        { "nested-opened-reference-is-not-rebound", "Lib = { public v = 99 }\nOuter = {\n    Inner = { open Lib\n        v\n    }\n    Need = v\n    Inner + Need\n}\nOuter(7)", "ok 106" },
        { "opened-reference-is-not-rebound", "Lib = { public v = 99 }\nNeed(v) = v\nOuter = {\n    open Lib\n    v + Need\n}\nOuter(7)", "ok 106" },

        // J. A PRELUDE builtin is never forwarded, and a reference to it is never rebound.
        { "builtin-names-remain-parameters", "Clamp(x, min, max) = if(x < min, min, if(x > max, max, x))\nSafe = Clamp + 0\nSafe(15, 0, 10)", "ok 10" },
        // Formerly NotAnAlgorithm: the written `min(...)` called Safe's forwarded parameter.
        { "builtin-callee-is-not-rebound", "NeedMin(min) = min + 1\nSafe = NeedMin + min((3, 4))\nSafe(10)", "ok 14" },
        { "count-callee-is-not-rebound", "Need(count) = count * 2\nF = Need + count((1, 2, 3))\nF(5)", "ok 13" },
        // Formerly 8: Inner's `abs` called Outer's forwarded parameter.
        { "math-alias-is-not-rebound", "X = x + 1\nNeed(abs) = 0\nApply(f) = f(7)\nOuter = { Inner = abs(X)\nInner + Need }\nOuter(0, Apply)", "ok 1" },

        // A closed parameter list forwards an accessible captured ancestor parameter too
        // (formerly a front-end refusal / ArityMismatch); with none there, it still refuses.
        { "closed-list-strict-position-reuses-ancestor", "A = y + 1\nG = {\n  F(x) = Math.Abs(A)\n  F(1) + y\n}\nG(3)", "ok 7" },
        { "closed-list-reuses-ancestor", "A = y + 1\nG = {\n  F(x) = A\n  F(1) + y\n}\nG(3)", "ok 7" },
        { "closed-list-without-an-ancestor-still-refuses", "Speed = distance / time\nKE(m, d, t) = m * Speed ^ 2 / 2\nKE(2, 10, 5)", "err ArityMismatch" },

        // A reused binding keeps its KIND: a collecting ancestor re-spreads, an ordinary one does not.
        { "collecting-ancestor-respreads", "Target(tag, *items) = items\nOuter(tag, *items) = {\n    G = Target\n    G\n}\nOuter(0, 1, 2)", "ok L[1, 2]" },
        { "ordinary-ancestor-stays-one-argument", "Target(tag, *items) = items\nOuter(tag, items) = {\n    G = Target\n    G\n}\nOuter(0, [1, 2])", "ok L[L[1, 2]]" },

        // Blocks, callbacks, aliases, and deconstruction right-hand sides reuse the same bindings.
        { "callback-block-reuses-ancestor", "A = y + 1\nG(y) = map([1, 2], { A + n })\nG(10)", "ok L[12, 13]" },
        { "alias-reuses-ancestor", "Inc(x) = x + 1\nF(x) = {\n    Alias = Inc\n    Alias\n}\nF(4)", "ok 5" },
        { "partial-alias-reuses-ancestor", "Head(x, *rest) = x + rest.count\nF(x) = {\n    H = Head\n    H(10, 20)\n}\nF(4)", "ok 6" },
        { "deconstruction-source-reuses-ancestor", "A = y + 1\nF(y) = {\n    G = {\n        a, b = A, 1\n        a + b\n    }\n    if(true, G, 0)\n}\nF(3)", "ok 5" },

        // A helper that now reads an enclosing parameter is an ordinary zero-parameter property:
        // one evaluation per activation of its owner (formerly one fresh call per reference).
        { "reused-helper-is-read-once-per-activation", "A = y + 1\nF(y) = {\n    G = A * 10 + tick() * 0\n    G + G\n}\nF(3)", "ok 80 [tick#1]" },
        { "reused-helper-is-per-activation", "A = y + 1\nF(y) = {\n    G = A * 10 + tick() * 0\n    G + G\n}\nF(3), F(4)", "ok S[80, 100] [tick#1,tick#2]" },

        // A forwarded parameter never gives a meaning to a name nothing declares either: the
        // closed body's `v` stays undeclared (formerly 14 / 22.0, bound to the forwarded one).
        { "forwarded-parameter-names-nothing-in-a-branch", "Need(v) = v\nOuter = { F(0) = 0\nF(n) = v\nF(1) + Need }\nOuter(7)", "parse UndeclaredIdentifier" },
        { "forwarded-parameter-names-nothing-in-a-closed-list", "Tax = price * rate\nInvoice = {\n    Line(qty) = qty * price\n    Line(2) + Tax\n}\nInvoice(10, 0.2)", "parse UndeclaredIdentifier" },

        // The never-called root still reports an unresolved input.
        { "root-input-stays-unresolved", "A = y + 1\nG = A * 2\ny + G", "err UnresolvedImplicitParams" },

        // Hostile audit: adding a forwarded dependency never changes an existing binding.
        // An opened name written in the forwarding body keeps its value (formerly 7: rebound to 3).
        { "opened-name-in-the-forwarding-body", "Lib = { public y = 50 }\nA = y + 1\nF = {\n    open Lib\n    G = y + A\n    G\n}\nF(3)", "ok 54" },
        // A nearer explicit owner decides: Inner reuses Mid's `y`, not Outer's.
        { "nearest-enclosing-parameter-is-reused", "A = y + 1\nOuter(y) = {\n    Mid(y) = {\n        Inner = A\n        Inner\n    }\n    Mid(10) + y\n}\nOuter(3)", "ok 14" },
        { "alias-chain-reuses-ancestor", "A = y + 1\nF(y) = {\n    G = A\n    H = G\n    K = H\n    if(true, K, 0)\n}\nF(3)", "ok 4" },
        // Callback and loop-step blocks reuse the enclosing parameter (formerly ArityMismatch:
        // the block took the lifted `y` as a second callback parameter).
        { "reduce-callback-reuses-ancestor", "A = y + 1\nF(y) = reduce([1, 2], { e + acc + A }, 0)\nF(3)", "ok 11" },
        { "filter-callback-reuses-ancestor", "A = y + 1\nF(y) = filter([1, 5, 9], { e > A })\nF(3)", "ok L[5, 9]" },
        { "map-callback-reuses-ancestor", "A = n + 1\nF(n) = map([1, 2], { A + e })\nF(10)", "ok L[12, 13]" },
        { "loop-step-reuses-ancestor", "A = y + 1\nF(y) = repeat({ s + A }, 2, 0)\nF(3)", "ok 8" },
        // Only the unbound half is forwarded; H's closed list then supplies it (formerly ArityMismatch).
        { "partial-reuse-forwards-only-the-unbound-name", "A = y + z\nF(y) = {\n    G = A * 10\n    H(z) = G\n    H(100)\n}\nF(3)", "ok 1030" },
        { "partial-reuse-inside-a-branch", "A = y + 1\nF(0) = 0\nF(y) = {\n    G(q) = A + q\n    G(1)\n}\nF(3)", "ok 5" },
        // A grouped callee pattern keeps its reused capture: G forwards only `b`, as a one-item group.
        { "grouped-callee-reuses-one-capture", "P((a, b)) = a + b\nF(a) = {\n    G = P + 0\n    G(5)\n}\nF(10)", "ok 15" },
        { "grouped-callee-no-longer-takes-the-reused-capture", "P((a, b)) = a + b\nF(a) = {\n    G = P + 0\n    G((1, 2))\n}\nF(10)", "err ArityMismatch" },
        // A Math alias forwards like any callee: pow's `x` is F's (formerly ArityMismatch).
        { "math-alias-reuses-ancestor", "F(x) = {\n    G = pow + 0\n    G(2)\n}\nF(3)", "ok 9" },
        { "collector-through-several-owners", "Target(tag, *items) = items\nF(tag, *items) = {\n G = { H = { I = Target\n I }\n H }\n G\n}\nF(0, (1, 2), [3], ())", "ok L[S[1, 2], L[3], S[]]" },
        { "closed-child-reuses-collector", "Target(tag, *items) = items\nF(tag, *items) = { G(q) = Target\n G(99) }\nF(0, (1, 2), [3], ())", "ok L[S[1, 2], L[3], S[]]" },
        { "partial-reuse-of-collector", "Target(tag, *items) = items\nF(*items) = { G = Target\n G(0) }\nF((1, 2), [3], ())", "ok L[S[1, 2], L[3], S[]]" },
        { "collector-to-fixed-keeps-one-value", "Target(items) = items\nF(*items) = { G = Target\n G }\nF((1, 2), [3], ())", "ok L[S[1, 2], L[3], S[]]" },
        { "nearer-fixed-over-outer-collector", "Target(tag, *items) = items\nF(tag, *items) = { M(items) = { G = Target\n G }\n M([7, 8]) }\nF(0, 1, 2)", "ok L[L[7, 8]]" },
        { "nearer-collector-over-outer-fixed", "Target(tag, *items) = items\nF(tag, items) = { M(*items) = { G = Target\n G }\n M(7, 8) }\nF(0, [1, 2])", "ok L[7, 8]" },
        { "branch-nested-closed-list-reuses-ancestor", "Target(tag, *items) = items\nF(tag, *items) = { M(0) = 0\n M(n) = { G(q) = Target\n G(n) }\n M(1) }\nF(0, (1, 2), [3], ())", "ok L[S[1, 2], L[3], S[]]" },
    };

    [Theory]
    [MemberData(nameof(Programs))]
    public async Task Forwarding_ReusesParameterBindingsOnly_AndNeverRebindsAWrittenName(string id, string source, string expected)
    {
        _ = id;
        Assert.Equal(expected, await OnEveryRouteAsync(source));
    }

    // ── 2. The elaborated tree ───────────────────────────────────────────────────────

    private static Algorithm Property(Algorithm owner, params string[] path)
    {
        foreach (var name in path)
            owner = owner.Properties.Single(property => property.Name == name).Value;
        return owner;
    }

    [Fact]
    public void CapturedAncestorParameter_IsForwarded_NotLifted()
    {
        var root = SourceProvenance.ParseValid("A = y + 1\nF(y) = {\n    G = y * 1000 + A\n    H(y) = G\n    H(100)\n}\nF(3)").Root;
        var g = Assert.IsType<Algorithm.User>(Property(root, "F", "G"));

        // G acquires no parameter: forwarding reuses F's binding.
        Assert.Empty(g.Params);
        Assert.Null(g.ForwardingParameterStart);
        var sum = Assert.IsType<Expr.Binary>(Assert.Single(g.Output));
        // The written `y` is F's captured parameter, and the synthesized call hands A that same binding.
        Assert.Equal("y", Assert.IsType<Expr.Param>(Assert.IsType<Expr.Binary>(sum.Left).Left).Name);
        var call = Assert.IsType<Expr.Call>(sum.Right);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(call.Function).Name);
        Assert.Equal("y", Assert.IsType<Expr.Param>(Assert.Single(call.Args)).Name);
        // G reads an enclosing parameter, so it is local to F's activation.
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Property(root, "F").Properties.Single(property => property.Name == "G").Exposure);
    }

    [Fact]
    public void ForwardedParameter_IsMarked_AndNeverOwnsAWrittenName()
    {
        var root = SourceProvenance.ParseValid("v = 99\nNeed(v) = v\nOuter = { Inner = v\n  Inner + Need }\nOuter(7)").Root;
        var outer = Assert.IsType<Algorithm.User>(Property(root, "Outer"));

        // Outer receives a forwarded `v` for Need: an ordinary parameter for its callers ...
        Assert.Equal(["v"], outer.Params);
        Assert.Equal(0, outer.ForwardingParameterStart);
        Assert.Empty(outer.NameResolutionParameterPatterns);
        // ... that the written `v` in Inner does not denote: it stays the root property.
        Assert.Equal("v", Assert.IsType<Expr.Resolve>(Assert.Single(Property(root, "Outer", "Inner").Output)).Name);
    }

    [Fact]
    public void ReusedEnclosingBinding_IsNeverAppendedToTheSignature()
    {
        // Head's `x` is F's; only the collector it cannot supply is forwarded into H.
        var root = SourceProvenance.ParseValid("Head(x, *rest) = x + rest.count\nF(x) = {\n    H = Head\n    H(10, 20)\n}\nF(4)").Root;
        var h = Assert.IsType<Algorithm.User>(Property(root, "F", "H"));
        Assert.Equal(["rest"], h.Params);
        Assert.Equal(ParameterKind.Collecting, Assert.IsType<CaptureParameterPattern>(Assert.Single(h.ParameterPatterns)).Kind);
        Assert.Equal(0, h.ForwardingParameterStart);
    }

    // ── 3. The editor model sees what a written name denotes ─────────────────────────

    private static IdentifierResolution ResolutionOf(SemanticModel model, string source, string needle, int occurrence = 0)
    {
        var index = -1;
        for (var i = 0; i <= occurrence; i++)
            index = source.IndexOf(needle, index + 1, StringComparison.Ordinal);
        Assert.True(index >= 0, $"'{needle}' #{occurrence} not found");
        var line = source[..index].Count(static c => c == '\n') + 1;
        var lineStart = index == 0 ? 0 : source.LastIndexOf('\n', index - 1) + 1;
        return Assert.IsType<IdentifierResolution>(model.FindResolutionAt(new SourcePosition(line, index - lineStart + 1)));
    }

    [Fact]
    public void EditorModel_ResolvesTheReusedAncestorReference_ToTheAncestorDeclaration()
    {
        const string source = "A = y + 1\nF(y) = {\n    G = y * 1000 + A\n    H(y) = G\n    H(100)\n}\nF(3)";
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Root);
        var written = ResolutionOf(model, source, "y * 1000");
        Assert.Equal(IdentifierClassification.ExplicitParameterReference, written.Classification);
        Assert.NotNull(written.ResolvedDeclaration);
        Assert.Equal(new SourcePosition(2, 3), written.ResolvedDeclaration.Span.Start);
    }

    [Fact]
    public void EditorModel_NeitherResolvesToNorOffersAForwardedParameter()
    {
        const string source = "v = 99\nNeed(v) = v\nOuter = { Inner = v\n  Inner + Need }\nOuter(7)";
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Root);
        var written = ResolutionOf(model, source, "v\n  Inner");
        Assert.Equal(IdentifierClassification.PropertyReference, written.Classification);
        Assert.NotNull(written.ResolvedDeclaration);
        Assert.Equal(new SourcePosition(1, 1), written.ResolvedDeclaration.Span.Start);

        var visible = Assert.Single(model.GetVisibleSymbolsAt(written.Occurrence.Span.Start), symbol => symbol.Name == "v");
        Assert.Equal(IdentifierClassification.PropertyReference, visible.Classification);
        Assert.Equal(written.ResolvedDeclaration.Span, visible.Declaration?.Span);
    }

    // ── 4. Metamorphic: adding a forwarded dependency never changes an existing binding ──

    /// <summary>
    /// One base program per way the name <c>n</c> can be bound where it is written, plus a marked
    /// row (<c>/*USE*/</c> is where the dependency is added) and whether the enclosing call keeps
    /// its arity when the dependency is added (then the value must not change either).
    /// </summary>
    public static TheoryData<string, string, bool> BindingShapes => new()
    {
        { "explicit-ancestor", "F(n) = {\n    G = n * 10/*USE*/\n    if(true, G, 0)\n}\nF(3)", true },
        { "inferred-ancestor", "F = {\n    G = n * 10/*USE*/\n    if(true, G, 0) + n\n}\nF(3)", true },
        { "branch-binder", "F(0) = 0\nF(n) = {\n    G = n * 10/*USE*/\n    if(true, G, 0)\n}\nF(3)", true },
        { "nested-explicit-ancestor", "F(n) = {\n    M = {\n        G = n * 10/*USE*/\n        G\n    }\n    if(true, M, 0)\n}\nF(3)", true },
        { "closed-list-with-ancestor", "F(n) = {\n    G(x) = x + n/*USE*/\n    G(1)\n}\nF(3)", true },
        { "callback-block", "F(n) = map([1, 2], { e + n/*USE*/ })\nF(3)", true },
        { "own-explicit", "G(n) = n * 10/*USE*/\nG(3)", true },
        { "own-inferred", "G = n * 10/*USE*/\nG(3)", true },
        { "shadowing-explicit", "F(n) = {\n    G(n) = n * 10/*USE*/\n    G(7) + n\n}\nF(3)", true },
        { "root-property", "n = 5\nF = {\n    G = n * 10/*USE*/\n    G\n}\nF", false },
        { "enclosing-property", "F = {\n    n = 5\n    G = n * 10/*USE*/\n    G\n}\nF", false },
        { "opened-member", "Lib = { public n = 5 }\nF = {\n    open Lib\n    G = n * 10/*USE*/\n    G\n}\nF", false },
        { "nested-opened-member", "Lib = { public n = 5 }\nF = {\n    G = {\n        open Lib\n        n * 10/*USE*/\n    }\n    G\n}\nF", false },
        { "prelude-constant", "F = {\n    G = pi * 10/*USE*/\n    G\n}\nF", false },
    };

    /// <summary>The same program with a forwarded dependency on the bound name added at the marker.</summary>
    private static string WithDependency(string source, string name)
        => source.Replace("/*USE*/", " + 0 * Dep", StringComparison.Ordinal) + $"\nDep({name}) = {name}";

    [Theory]
    [MemberData(nameof(BindingShapes))]
    public void AddingAForwardedDependency_KeepsEveryWrittenBinding(string id, string template, bool valueStable)
    {
        var name = id == "prelude-constant" ? "pi" : "n";
        var before = template.Replace("/*USE*/", "", StringComparison.Ordinal);
        var after = WithDependency(template, name);

        var beforeParse = SourceProvenance.ParseValid(before);
        var afterParse = SourceProvenance.ParseAllowingDiagnostics(after);
        var beforeBindings = WrittenBindings(beforeParse.Root, before);
        var afterBindings = WrittenBindings(afterParse.Root, after);

        // Every identifier written in the base program denotes exactly what it denoted before:
        // the same classification, the same declaration, and — for a parameter — the same owner.
        Assert.NotEmpty(beforeBindings);
        foreach (var (position, binding) in beforeBindings)
            Assert.True(afterBindings.TryGetValue(position, out var now) && now == binding,
                $"{id}: the written name at {position} denoted {binding} and now denotes {(now ?? "nothing")}\n{after}");

        if (valueStable)
        {
            Assert.Empty(afterParse.Diagnostics);
            Assert.Equal(
                KatLangEngine.Run(before).ToDisplayString(),
                KatLangEngine.Run(after).ToDisplayString());
        }
    }

    /// <summary>
    /// Every source-backed identifier of <paramref name="source"/>'s own lines, keyed by position:
    /// the editor's classification and declaration, plus — for a parameter reference — the elaborated
    /// owner that binds it at run time (the nearest enclosing body that owns the name).
    /// </summary>
    private static Dictionary<SourcePosition, string> WrittenBindings(Algorithm.User root, string source)
    {
        var model = SemanticModelBuilder.Build(root);
        var owners = ParameterOwners(root);
        var bindings = new Dictionary<SourcePosition, string>();
        foreach (var resolution in model.IdentifierResolutions)
        {
            var position = resolution.Occurrence.Span.Start;
            if (resolution.Occurrence.Name == "Dep")
                continue;
            owners.TryGetValue(position, out var owner);
            bindings[position] = $"{resolution.Occurrence.Name}:{resolution.Classification}:{resolution.ResolvedDeclaration?.Span.Start.ToString() ?? "-"}:{owner ?? "-"}";
        }

        return bindings;
    }

    /// <summary>The owning body path of every source-backed parameter reference in the elaborated tree.</summary>
    private static Dictionary<SourcePosition, string> ParameterOwners(Algorithm root)
    {
        var owners = new Dictionary<SourcePosition, string>();
        VisitAlgorithm(root, "root", ImmutableOwnerChain.Empty);
        return owners;

        void VisitAlgorithm(Algorithm algorithm, string path, ImmutableOwnerChain chain)
        {
            switch (algorithm)
            {
                case Algorithm.User user:
                {
                    var inner = chain.Push(path, user.Params);
                    foreach (var property in user.Properties)
                        VisitAlgorithm(property.Value, path + "/" + property.Name, inner);
                    foreach (var row in user.Output)
                        VisitExpr(row, inner, path);
                    break;
                }

                case Algorithm.Conditional family:
                    for (var index = 0; index < family.Branches.Count; index++)
                    {
                        var branch = family.Branches[index];
                        VisitAlgorithm(branch.Body, path + "/@" + index, chain.Push(path + "/@" + index + ":binders", branch.Pattern.BoundNames()));
                    }

                    break;
            }
        }

        void VisitExpr(Expr expr, ImmutableOwnerChain chain, string path)
        {
            switch (expr)
            {
                case Expr.Param parameter when parameter.Span is { } span:
                    owners[span.Start] = chain.OwnerOf(parameter.Name) ?? "?";
                    break;
                case Expr.Call call:
                    VisitExpr(call.Function, chain, path);
                    foreach (var arg in call.Args)
                        VisitExpr(arg, chain, path);
                    break;
                case Expr.Binary binary:
                    VisitExpr(binary.Left, chain, path);
                    VisitExpr(binary.Right, chain, path);
                    break;
                case Expr.Comparison comparison:
                    VisitExpr(comparison.First, chain, path);
                    foreach (var link in comparison.Links)
                        VisitExpr(link.Operand, chain, path);
                    break;
                case Expr.Unary unary:
                    VisitExpr(unary.Operand, chain, path);
                    break;
                case Expr.Index index:
                    VisitExpr(index.Target, chain, path);
                    VisitExpr(index.Selector, chain, path);
                    break;
                case Expr.SequenceSpread spread:
                    VisitExpr(spread.Operand, chain, path);
                    break;
                case Expr.ListLiteral list:
                    foreach (var item in list.Items)
                        VisitExpr(item, chain, path);
                    break;
                case Expr.Capture capture:
                    foreach (var row in capture.Body)
                        VisitExpr(row, chain, path);
                    break;
                case Expr.DotCall dotCall:
                    VisitExpr(dotCall.Target, chain, path);
                    if (dotCall.Args is { } args)
                    {
                        foreach (var arg in args)
                            VisitExpr(arg, chain, path);
                    }

                    break;
                case Expr.AlgorithmExpr block:
                    VisitAlgorithm(block.Algorithm, path + "/{}", chain);
                    break;
            }
        }
    }

    /// <summary>An innermost-first chain of (owner path, parameter names) levels.</summary>
    private sealed record ImmutableOwnerChain(string Path, IReadOnlyCollection<string> Names, ImmutableOwnerChain? Parent)
    {
        public static readonly ImmutableOwnerChain Empty = new("", [], null);

        public ImmutableOwnerChain Push(string path, IEnumerable<string> names) => new(path, names.ToArray(), this);

        public string? OwnerOf(string name)
        {
            for (var level = this; level is not null; level = level.Parent)
            {
                if (level.Names.Contains(name))
                    return level.Path;
            }

            return null;
        }
    }

    // ── 4b. One shared node, two forwarding contexts ─────────────────────────────────

    [Fact]
    public void SharedBody_UnderOwnersWithDifferentParameters_IsForwardedPerContext()
    {
        // One host-built property value `G = A * 10`, shared by F(y) and K (whose rows infer z).
        // Under F, A's `y` is F's parameter, so G reuses it and takes no parameter; under K nothing
        // binds `y`, so G receives a forwarded `y` that K then forwards too. The resolver's region
        // memo keys a nested body on the enclosing parameter bindings it may reuse, so the shared
        // node is rewritten once per distinct context and each owner gets its own rewrite.
        var syntax = SourceProvenance.ParseSyntaxValidRoot(
            "A = y + 1\nF(y) = {\n    G = A * 10\n    G\n}\nK = {\n    G = A * 10\n    G + z\n}\nF(3), K(1, 5)");
        var (detected, diagnostics) = ParameterDetector.DetectPrevalidated(syntax);
        Assert.Empty(diagnostics);

        // Share ONE detected G (the same elaborated node under both owners) before resolution.
        var detectedRoot = Assert.IsType<Algorithm.User>(detected);
        var f = Assert.IsType<Algorithm.User>(detectedRoot.Properties.Single(p => p.Name == "F").Value);
        var k = Assert.IsType<Algorithm.User>(detectedRoot.Properties.Single(p => p.Name == "K").Value);
        var shared = f.Properties.Single(p => p.Name == "G").Value;
        var hostK = k with { Properties = [k.Properties.Single(p => p.Name == "G").WithValue(shared)] };
        var root = detectedRoot with
        {
            Properties = [.. detectedRoot.Properties.Select(p => p.Name == "K" ? p.WithValue(hostK) : p)],
        };

        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(root);
        var exposed = PropertyExposureResolver.Resolve(resolved);

        var gUnderF = Property(exposed, "F", "G");
        var gUnderK = Property(exposed, "K", "G");
        Assert.NotSame(gUnderF, gUnderK);
        Assert.Empty(gUnderF.Params);
        Assert.Equal(["y"], gUnderK.Params);
        Assert.Equal(["z", "y"], Property(exposed, "K").Params);
        var result = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(exposed), enableOptimizations: false).Result;
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : "");
        Assert.Equal("S[40, 61]", Neutral(result.Value.Value));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SharedBody_UnderTheSameParameterNamesWithDifferentKinds_KeepsItsSupply(bool collectingFirst)
    {
        const string source = "Target(tag, *items) = items\nF(tag, *items) = { G = Target\n G }\nK(tag, items) = { G = Target\n G }\n[F(0, (1, 2), [3], ()), K(0, [(1, 2), [3], ()])]";
        var (detected, diagnostics) = ParameterDetector.DetectPrevalidated(SourceProvenance.ParseSyntaxValidRoot(source));
        Assert.Empty(diagnostics);
        var root = Assert.IsType<Algorithm.User>(detected);
        var f = Assert.IsType<Algorithm.User>(Property(root, "F"));
        var k = Assert.IsType<Algorithm.User>(Property(root, "K"));
        var shared = Property(root, "F", "G");
        k = k with { Properties = [k.Properties.Single().WithValue(shared)] };
        var fProperty = root.Properties.Single(p => p.Name == "F").WithValue(f);
        var kProperty = root.Properties.Single(p => p.Name == "K").WithValue(k);
        root = root with
        {
            Properties = [root.Properties.Single(p => p.Name == "Target"),
                collectingFirst ? fProperty : kProperty, collectingFirst ? kProperty : fProperty],
        };

        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(root);
        var collected = Property(resolved, "F", "G");
        var fixedValue = Property(resolved, "K", "G");
        Assert.NotSame(collected, fixedValue);
        Assert.Empty(collected.Params);
        Assert.Empty(fixedValue.Params);
        var collectingCall = Assert.IsType<Expr.Call>(Assert.Single(collected.Output));
        var fixedCall = Assert.IsType<Expr.Call>(Assert.Single(fixedValue.Output));
        Assert.Equal("items", Assert.IsType<Expr.Param>(Assert.IsType<Expr.SequenceSpread>(collectingCall.Args[1]).Operand).Name);
        Assert.Equal("items", Assert.IsType<Expr.Param>(fixedCall.Args[1]).Name);
        Assert.NotSame(collectingCall.Args, fixedCall.Args);

        var exposed = PropertyExposureResolver.Resolve(resolved);
        var result = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(exposed), enableOptimizations: false).Result;
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : "");
        Assert.Equal("L[L[S[1, 2], L[3], S[]], L[L[S[1, 2], L[3], S[]]]]", Neutral(result.Value.Value));
    }

    // ── 5. Metamorphic: extracting a sub-expression into a property keeps every binding ──

    /// <summary>
    /// (context, inlined body, extracted helper, extracted body): the written names of the inlined
    /// form are bound by an enclosing owner; the extracted helper names them as its own free names,
    /// which forwarding must supply from that same binding.
    /// </summary>
    public static TheoryData<string, string, string, string> ExtractionContexts => new()
    {
        { "explicit-owner", "F(y) = {\n    G = y * 1000 + (y + 1)\n    H(y) = G\n    H(100)\n}\nF(3)", "A = y + 1", "F(y) = {\n    G = y * 1000 + A\n    H(y) = G\n    H(100)\n}\nF(3)" },
        { "inferred-owner", "B = {\n    G = y * 1000 + (y + 1)\n    H(y) = G\n    H(100) + y\n}\nB(3)", "A = y + 1", "B = {\n    G = y * 1000 + A\n    H(y) = G\n    H(100) + y\n}\nB(3)" },
        { "branch-binder", "F(0) = 0\nF(y) = {\n    G = y * 1000 + (y + 1)\n    H(y) = G\n    H(100)\n}\nF(3)", "A = y + 1", "F(0) = 0\nF(y) = {\n    G = y * 1000 + A\n    H(y) = G\n    H(100)\n}\nF(3)" },
        { "nested-levels", "F(y) = {\n    M = {\n        G = y * 1000 + (y + 1)\n        G\n    }\n    if(true, M, 0)\n}\nF(3)", "A = y + 1", "F(y) = {\n    M = {\n        G = y * 1000 + A\n        G\n    }\n    if(true, M, 0)\n}\nF(3)" },
        { "neutral-argument", "F(y) = {\n    G = (y + 1) * 2\n    if(true, G, 0)\n}\nF(3)", "A = y + 1", "F(y) = {\n    G = A * 2\n    if(true, G, 0)\n}\nF(3)" },
        { "closed-list", "F(y) = {\n    G(x) = x + (y + 1)\n    G(10)\n}\nF(3)", "A = y + 1", "F(y) = {\n    G(x) = x + A\n    G(10)\n}\nF(3)" },
        { "callback-block", "F(y) = map([1, 2], { e + (y + 1) })\nF(3)", "A = y + 1", "F(y) = map([1, 2], { e + A })\nF(3)" },
        { "two-level-helper", "F(y) = {\n    G = (y + 1) * 2 + y\n    if(true, G, 0)\n}\nF(3)", "A = y + 1\nB = A * 2", "F(y) = {\n    G = B + y\n    if(true, G, 0)\n}\nF(3)" },
        { "alias", "F(y) = {\n    G = y + 1\n    if(true, G, 0)\n}\nF(3)", "A = y + 1", "F(y) = {\n    G = A\n    if(true, G, 0)\n}\nF(3)" },
        { "clause-family-owner", "F(0) = 0\nF(y) = {\n    G = (y + 1) * 10\n    G\n}\nF(3)", "A = y + 1", "F(0) = 0\nF(y) = {\n    G = A * 10\n    G\n}\nF(3)" },
    };

    [Theory]
    [MemberData(nameof(ExtractionContexts))]
    public async Task ExtractingIntoAProperty_KeepsTheExistingBindings(string id, string inlined, string helper, string extracted)
    {
        _ = id;
        var inlinedOutcome = await OnEveryRouteAsync(inlined);
        Assert.StartsWith("ok ", inlinedOutcome);
        Assert.Equal(inlinedOutcome, await OnEveryRouteAsync(helper + "\n" + extracted));
    }
}
