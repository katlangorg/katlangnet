using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// VAR-03 (owner decision 2026-10-09, adopting the Model-C NEED-07/08 collector and forwarding laws): A
/// COLLECTING PARAMETER PRESERVES THE SUPPLIED DEMANDABLE ARGUMENT CELLS. Three different operations:
/// <list type="bullet">
/// <item><b>Collecting.</b> <c>*xs</c> binds an exact slice of the supplied cells; collecting demands none
/// of their values.</item>
/// <item><b>Re-spreading a known slice.</b> <c>xs*</c> transfers those very cells into another supply with
/// whatever VALUE/CALLABLE capabilities they already have, without forcing VALUE: <c>Fwd(*fs) = Apply(fs*)</c>
/// / <c>Fwd(Inc)</c> is <c>10</c>. The collector invents no capability: a scalar, a capture or a computed
/// value stays value-only.</item>
/// <item><b>Reading the collector as a value.</b> Ordinary <c>xs</c> materializes ONE exact list, demanding
/// every element by its own VALUE contract; a callable element reports its OWN zero-argument demand failure
/// (exactly as through a fixed parameter), never a collector-specific type mismatch. The unspread collector
/// is one collection-valued computation with no CALLABLE identity.</item>
/// </list>
/// An arbitrary spread <c>E*</c> (a list literal, a call result, a fixed parameter holding a list) is still
/// evaluated during supply formation, independently required static checks still apply, bare forwarding
/// still selects by binding name, and re-spread items are never reopened. This supersedes the pre-Model-C
/// VAR-03 text ("collects values, never callables"; a callable-shaped item was a binding-time
/// <c>TypeMismatch</c>; an unused collected failure was reported at the call).
/// <para>Every expectation is written from the law, not from observation. Every source runs on the six
/// routes, which must agree with the synchronous engine on value, emitted count, every error (code,
/// message, span) and the host-call log; the three evaluator routes must also charge identical budgets.
/// Lean: <c>CoreTests/CollectingCallableForwarding.lean</c>; spec case
/// <c>collected-callable-survives-explicit-respread</c>.</para>
/// </summary>
public sealed class CollectingCallableForwardingLawTests
{
    private const string Inc = "Inc(x) = x + 1\n";
    private const string Apply = "Apply(f) = f(9)\n";
    private const string Fwd = "Fwd(*fs) = Apply(fs*)\n";
    private const string NotCallable =
        "Parameter 'f' is not callable here: it is bound to a value, not to an algorithm. Pass an algorithm for 'f', or read it as a value.";
    private const string IncDemand = "Property 'Inc' expects 1 parameter, but was called with 0 arguments.";
    private const string ApplyChain = "while evaluating call to Fwd: while evaluating call to Apply: while evaluating call to f";

    // ── 1. The canonical witnesses ─────────────────────────────────────────────────────────────────

    public static TheoryData<string, string, string> CanonicalWitnesses() => new()
    {
        // V1: the collected callable is invoked after the known slice is re-spread.
        { "V1", Inc + Apply + Fwd + "Fwd(Inc)", "ok 10 n=1" },
        // V2: the re-spread cell keeps its algorithm channel in a builtin callback slot.
        { "V2", Inc + "ApplyFirst(*fs) = map([1, 2], fs*)\nApplyFirst(Inc)", "ok L[2, 3] n=1" },
        // V3: collecting alone makes no zero-argument demand of Inc.
        { "V3", Inc + "Ignore(*xs) = 1\nIgnore(Inc)", "ok 1 n=1" },
        // V4: an unused collected failure is not demanded.
        { "V4", "Bad = 1 / 0\nIgnore(*xs) = 1\nIgnore(Bad)", "ok 1 n=1" },
        // V5: reading the collected list demands Inc's VALUE: Inc's own zero-argument rejection, blamed at
        // the written argument.
        { "V5", Inc + "Collect(*xs) = xs\nCollect(Inc)", $"err ArityMismatch: while evaluating call to Collect: {IncDemand} @ [3:9, 3:12)" },
    };

    [Theory]
    [MemberData(nameof(CanonicalWitnesses))]
    public async Task CanonicalWitness_HasTheAdoptedMeaning(string id, string source, string expected)
    {
        var observation = await AllRoutesAsync(source);
        Assert.True(expected == observation.Outcome, $"{id}: expected {expected}, got {observation}");
        Assert.Empty(observation.HostCalls);
    }

    [Fact]
    public void ReadingACollectedCallable_IsItsOwnArityRejection_NeverACollectorTypeMismatch()
    {
        var error = GenericError(Inc + "Collect(*xs) = xs\nCollect(Inc)");
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal((1, 0), (arity.Expected, arity.Actual));
        Assert.DoesNotContain("collects values", KatLangError.FromEvalError(error).Message, StringComparison.Ordinal);
    }

    // ── 2. A known slice versus the collector's VALUE versus arbitrary spreads ──────────────────────

    public static TheoryData<string, string, string> SliceVersusValue() => new()
    {
        { "a known slice re-spread transfers the original cell", Inc + Apply + Fwd + "Fwd(Inc)", "ok 10 n=1" },
        { "the fluent spelling of the same re-spread (R*.F is F(R*))", Inc + Apply + "Fwd(*fs) = fs*.Apply\nFwd(Inc)", "ok 10 n=1" },
        {
            "the unspread collector is one collection-valued computation with no identity",
            Inc + Apply + "Fwd(*fs) = Apply(fs)\nFwd(Inc)",
            $"err NotAnAlgorithm: {ApplyChain}: {NotCallable} @ [2:12, 2:13)"
        },
        {
            "the fluent unspread receiver (R.F is F(R))",
            Inc + Apply + "Fwd(*fs) = fs.Apply\nFwd(Inc)",
            $"err NotAnAlgorithm: while evaluating call to Fwd: while evaluating dotCall .Apply of fs: while evaluating call to f: {NotCallable} @ [2:12, 2:13)"
        },
        {
            "a selection of the collector is a computed value",
            Inc + Apply + "Fwd(*fs) = Apply(fs:0)\nFwd(Inc)",
            $"err NotAnAlgorithm: {ApplyChain}: {NotCallable} @ [2:12, 2:13)"
        },
        {
            "a capture of the spread is one sequence value",
            Inc + Apply + "Fwd(*fs) = Apply((fs*))\nFwd(Inc)",
            $"err NotAnAlgorithm: {ApplyChain}: {NotCallable} @ [2:12, 2:13)"
        },
        {
            "an ordinary materialized list, then a spread: building the list demands Inc",
            Inc + Apply + "Fwd(*fs) = Apply([fs*]*)\nFwd(Inc)",
            $"err ArityMismatch: while evaluating call to Fwd: while evaluating call to Apply: {IncDemand} @ [4:5, 4:8)"
        },
        {
            "an arbitrary computed spread operand is evaluated during supply formation",
            Inc + Apply + "Hold(v) = v\nFwd(*fs) = Apply(Hold(fs)*)\nFwd(Inc)",
            $"err ArityMismatch: while evaluating call to Fwd: while evaluating call to Apply: while evaluating call to Hold: {IncDemand} @ [5:5, 5:8)"
        },
        {
            "a FIXED parameter holding a list is not a collector slice",
            Inc + Apply + "Fix(xs) = Apply(xs*)\nWrap(f) = Fix([f])\nWrap(Inc)",
            $"err ArityMismatch: while evaluating call to Wrap: while evaluating call to Fix: while evaluating call to Apply: {IncDemand} @ [5:6, 5:9)"
        },
        {
            "spreading a FIXED parameter bound to a callable is an arbitrary spread",
            Inc + "Coll(*xs) = 1\nPass(f) = Coll(f*)\nPass(Inc)",
            $"err ArityMismatch: while evaluating call to Pass: while evaluating call to Coll: {IncDemand} @ [4:6, 4:9)"
        },
        {
            "reading a mixed list's collector demands a family element: its own NoMatchingBranch",
            "Fam(0) = 0\nFam(n) = n\nHead(x, *rest) = rest\nHead(1, Fam)",
            "err NoMatchingBranch: while evaluating call to Head: No matching branch for 'Fam' @ [4:9, 4:12)"
        },
        {
            "reading collected zero-argument callables demands each by its own VALUE contract",
            "Coll(*xs) = xs\nOnly(*ys) = ys\nK = 5\nColl(K), Coll(Only), Coll({ 3 })", "ok S[L[5], L[L[]], L[3]] n=3"
        },
        { "a slice of values re-spreads as ordinary items", "Add(a, b) = a + b\nFwd(*xs) = Add(xs*)\nFwd(1, 2)", "ok 3 n=1" },
        { "a materialized list of values re-spreads as ordinary items", "Add(a, b) = a + b\nFix(xs) = Add(xs*)\nFix([1, 2])", "ok 3 n=1" },
        { "re-spread items are never reopened", "Use(*ys) = ys\nFwd(*xs) = Use(xs*)\nFwd((1, 2), [3])", "ok L[S[1, 2], L[3]] n=1" },
    };

    [Theory]
    [MemberData(nameof(SliceVersusValue))]
    public async Task SliceRespread_DiffersFromTheCollectorsValueAndFromArbitrarySpreads(string label, string source, string expected)
    {
        var observation = await AllRoutesAsync(source);
        Assert.True(expected == observation.Outcome, $"{label}: expected {expected}, got {observation}");
        Assert.Empty(observation.HostCalls);
    }

    // ── 3. Transport is lazy; the demanding operation runs the original computation ─────────────────

    public static TheoryData<string, string, string, string[]> TransportIsLazy() => new()
    {
        { "an unused collected argument runs nothing", "Ignore(*xs) = 1\nIgnore(trace(5))", "ok 1 n=1", [] },
        { "re-spreading runs nothing", "Ignore(*xs) = 1\nFwd(*xs) = Ignore(xs*)\nFwd(trace(5))", "ok 1 n=1", [] },
        { "the demanding read runs the original computation", "Use(*ys) = ys\nFwd(*xs) = Use(xs*)\nFwd(trace(5))", "ok L[5] n=1", ["trace(5)"] },
        {
            "two transports of one cell share its one completion",
            "Use(*ys) = ys\nTwice(*xs) = Use(xs*), Use(xs*)\nTwice(trace(5))", "ok S[L[5], L[5]] n=1", ["trace(5)"]
        },
        {
            "the same cell forwarded across three wrappers is evaluated once",
            "Use(*ys) = ys\nF1(*a) = Use(a*), Use(a*)\nF2(*b) = F1(b*)\nF3(*c) = F2(c*)\nF3(trace(5))", "ok S[L[5], L[5]] n=1", ["trace(5)"]
        },
        { "an unused transported failure stays suspended", "Ignore(*xs) = 1\nFwd(*xs) = Ignore(xs*)\nFwd(1 / 0)", "ok 1 n=1", [] },
        {
            "the demanding read reports the transported failure at the written argument",
            "Use(*ys) = ys\nFwd(*xs) = Use(xs*)\nFwd(1 / 0)",
            "err DivisionByZero: while evaluating call to Fwd: while evaluating call to Use: Division by zero @ [3:5, 3:10)", []
        },
        {
            "materialization demands left to right and stops at the first failure",
            "Use(*ys) = ys\nFwd(*xs) = Use(xs*)\nFwd(trace(1), 1 / 0, trace(3))",
            "err DivisionByZero: while evaluating call to Fwd: while evaluating call to Use: Division by zero @ [3:15, 3:20)", ["trace(1)"]
        },
        {
            "every invocation through the transported CALLABLE channel is fresh",
            "T(x) = trace(x) + 1\n" + Apply + "Twice(*fs) = Apply(fs*) + Apply(fs*)\nTwice(T)", "ok 20 n=1", ["trace(9)", "trace(9)"]
        },
        {
            "VALUE and CALLABLE survive one transport independently",
            "Z = trace(7)\nApply0(f) = f()\nUse(*ys) = ys\nBoth(*zs) = Apply0(zs*), Use(zs*)\nBoth(Z)", "ok S[7, L[7]] n=1", ["trace(7)", "trace(7)"]
        },
        {
            "a later VALUE read observes the completed cell while an invocation is fresh",
            "Z = trace(7)\nApply0(f) = f()\nUse(*ys) = ys\nBoth(*zs) = Use(zs*), Apply0(zs*), Use(zs*)\nBoth(Z)",
            "ok S[L[7], 7, L[7]] n=1", ["trace(7)", "trace(7)"]
        },
        {
            "a computed argument is never evaluated in order to be called",
            "T(x) = trace(x)\n" + Apply + Fwd + "Fwd(T(1))", $"err NotAnAlgorithm: {ApplyChain}: {NotCallable} @ [2:12, 2:13)", []
        },
        { "a collector and a fixed parameter treat an unused failure alike", "Bad = 1 / 0\nFix(x) = 1\nIgnore(*xs) = 1\nFix(Bad), Ignore(Bad)", "ok S[1, 1] n=2", [] },
        { "an output-less written block is not demanded by collecting it", "Coll(*xs) = 1\nColl({ X = 1 })", "ok 1 n=1", [] },
        {
            "reading the collected list demands the output-less block",
            "Coll(*xs) = xs\nColl({ X = 1 })",
            "err MissingOutput: while evaluating call to Coll: The argument `{...}` has no defined output.\nAdd an output expression to that argument, or use `()` if the empty sequence value was intended. @ [2:6, 2:15)", []
        },
    };

    [Theory]
    [MemberData(nameof(TransportIsLazy))]
    public async Task TransportingACellNeverForcesIt_TheDemandingOperationDoes(string label, string source, string expected, string[] hostCalls)
    {
        var observation = await AllRoutesAsync(source);
        Assert.True(expected == observation.Outcome, $"{label}: expected {expected}, got {observation}");
        Assert.Equal(hostCalls, observation.HostCalls);
    }

    // ── 4. Every forwarding route and callable kind keeps the CALLABLE channel ─────────────────────

    public static TheoryData<string, string, string> EveryRouteKeepsTheCallable() => new()
    {
        { "three wrappers", Inc + Apply + Fwd + "Fwd2(*gs) = Fwd(gs*)\nFwd3(*hs) = Fwd2(hs*)\nFwd3(Inc)", "ok 10 n=1" },
        { "a callable alias", Inc + Apply + Fwd + "A = Inc\nFwd(A)", "ok 10 n=1" },
        { "a clause family", Apply + "Fam(0) = 100\nFam(n) = n + 1\n" + Fwd + "Fwd(Fam)", "ok 10 n=1" },
        { "a recursive user callable", Apply + "Sum(n) = if(n == 0, 0, n + Sum(n - 1))\n" + Fwd + "Fwd(Sum)", "ok 45 n=1" },
        { "a recursive clause family", Apply + "Fact(0) = 1\nFact(n) = n * Fact(n - 1)\n" + Fwd + "Fwd(Fact)", "ok 362880 n=1" },
        { "a builtin", Apply + Fwd + "Fwd(count)", "ok 1 n=1" },
        { "a Math member", Apply + Fwd + "Fwd(Math.Abs)", "ok 9 n=1" },
        { "an anonymous brace block", Apply + Fwd + "Fwd({ x * 2 })", "ok 18 n=1" },
        { "a structural dot path to a member", "Lib = { Inc(x) = x + 1 }\n" + Apply + Fwd + "Fwd(Lib.Inc)", "ok 10 n=1" },
        { "a fixed parameter's cell transported into the collector", Inc + Apply + Fwd + "Pass(f) = Fwd(f)\nPass(Inc)", "ok 10 n=1" },
        { "a mixed prefix/collector/suffix list", Inc + Apply + "Mid(a, *fs, z) = Apply(fs*)\nMid(1, Inc, 2)", "ok 10 n=1" },
        { "bare forwarding of a collecting source into a collecting destination", Inc + Apply + "Use(*fs) = Apply(fs*)\nRelay(*fs) = Use\nRelay(Inc)", "ok 10 n=1" },
        { "a fixed source into a collecting destination", Inc + Apply + "Use(*fs) = Apply(fs*)\nRelay(fs) = Use\nRelay(Inc)", "ok 10 n=1" },
        { "a two-cell slice into two fixed callable parameters", Inc + "Apply2(f, g) = f(g(1))\nBoth(*fs) = Apply2(fs*)\nBoth(Inc, Inc)", "ok 3 n=1" },
        { "a callback slot reached through two wrappers", Inc + "Use(*fs) = map([1, 2], fs*)\nRelay(*gs) = Use(gs*)\nRelay(Inc)", "ok L[2, 3] n=1" },
        { "an enclosing body's collector re-spread in a nested block", Inc + Apply + "Fwd(*fs) = {\n  Inner = Apply(fs*)\n  Inner\n}\nFwd(Inc)", "ok 10 n=1" },
        { "a clause family re-spread, and an ignored one", "Fam(0) = 100\nFam(n) = n + 1\n" + Apply + Fwd + "Ignore(*xs) = 1\nFwd(Fam), Ignore(Fam)", "ok S[10, 1] n=2" },
    };

    /// <summary>The reconciled VAR-03 Normal example of the Constitution, with its stated result.</summary>
    [Fact]
    public async Task TheConstitutionsNormalExample_HasItsStatedResult()
    {
        var observation = await AllRoutesAsync(
            Inc + Apply + Fwd + "ApplyFirst(*fs) = map([1, 2], fs*)\nIgnore(*xs) = 1\nBad = 1 / 0\n"
            + "Fwd(Inc), ApplyFirst(Inc), Ignore(Inc), Ignore(Bad)");
        Assert.Equal("ok S[10, L[2, 3], 1, 1] n=4", observation.Outcome);
        Assert.Empty(observation.HostCalls);
    }

    [Theory]
    [MemberData(nameof(EveryRouteKeepsTheCallable))]
    public async Task CollectedCallable_SurvivesEveryForwardingRoute(string label, string source, string expected)
    {
        var observation = await AllRoutesAsync(source);
        Assert.True(expected == observation.Outcome, $"{label}: expected {expected}, got {observation}");
    }

    /// <summary>
    /// Metamorphic: forwarding through a collector and re-spreading is transparent for the supplied cell —
    /// <c>Fwd(X)</c> means what <c>Apply(X)</c> means, for callables and for value-only arguments alike
    /// (each error's code and innermost kind; the forwarding frame is the only difference).
    /// </summary>
    [Theory]
    [InlineData(Inc, "Inc")]
    [InlineData(Inc + "A = Inc\n", "A")]
    [InlineData("Fam(0) = 100\nFam(n) = n + 1\n", "Fam")]
    [InlineData("", "count")]
    [InlineData("", "{ x * 2 }")]
    [InlineData("", "5")]
    [InlineData(Inc, "Inc(1)")]
    [InlineData(Inc, "[Inc(1)]")]
    [InlineData("", "1 / 0")]
    public async Task ForwardingThroughACollector_IsTransparentForTheCell(string definitions, string argument)
    {
        var direct = await AllRoutesAsync(definitions + Apply + $"Apply({argument})");
        var forwarded = await AllRoutesAsync(definitions + Apply + Fwd + $"Fwd({argument})");
        Assert.Equal(direct.Semantic, forwarded.Semantic);
    }

    // ── 5. No capability is invented; cardinality precedes any demand ───────────────────────────────

    public static TheoryData<string, string, string> NoCapabilityIsInvented() => new()
    {
        { "a scalar", Apply + Fwd + "Fwd(5)", $"err NotAnAlgorithm: {ApplyChain}: {NotCallable} @ [1:12, 1:13)" },
        { "a string", Apply + Fwd + "Fwd('Inc')", $"err NotAnAlgorithm: {ApplyChain}: {NotCallable} @ [1:12, 1:13)" },
        { "a list value", Apply + Fwd + "Fwd([1])", $"err NotAnAlgorithm: {ApplyChain}: {NotCallable} @ [1:12, 1:13)" },
        {
            "a capture",
            Inc + Apply + Fwd + "Pair(f) = Fwd((f, f))\nPair(Inc)",
            $"err NotAnAlgorithm: while evaluating call to Pair: {ApplyChain}: {NotCallable} @ [2:12, 2:13)"
        },
        {
            "two cells for one parameter",
            Inc + Apply + Fwd + "Fwd(Inc, Inc)",
            "err ArityMismatch: while evaluating call to Fwd: Callable `Apply(f)` expects 1 argument, but was called with 2 arguments. @ [3:12, 3:22)"
        },
        {
            "no cell",
            Inc + Apply + Fwd + "Fwd()",
            "err ArityMismatch: while evaluating call to Fwd: Callable `Apply(f)` expects 1 argument, but was called with 0 arguments. @ [3:12, 3:22)"
        },
        {
            "a nested structural collector holds ready values only",
            Inc + Apply + "Nest((*fs)) = Apply(fs*)\nPair(f) = Nest((f, f))\nPair(Inc)",
            $"err ArityMismatch: while evaluating call to Pair: while evaluating call to Nest: {IncDemand} @ [5:6, 5:9)"
        },
        {
            "bare forwarding never renames a binding: gs supplies nothing to fs",
            Inc + Apply + "Use(*fs) = Apply(fs*)\nRelay(*gs) = Use\nRelay(Inc)",
            "err ArityMismatch: while evaluating call to Relay: Callable `Apply(f)` expects 1 argument, but was called with 0 arguments. @ [3:12, 3:22)"
        },
    };

    [Theory]
    [MemberData(nameof(NoCapabilityIsInvented))]
    public async Task ACollectorInventsNoCapability_AndCardinalityComesFirst(string label, string source, string expected)
    {
        var observation = await AllRoutesAsync(source);
        Assert.True(expected == observation.Outcome, $"{label}: expected {expected}, got {observation}");
        Assert.Empty(observation.HostCalls);
    }

    // ── 6. Reading the collected list reports the ORIGINAL callable's own error ─────────────────────
    //       (oracle: the same callable value-demanded through a FIXED parameter, `Id(x) = x`)

    [Theory]
    [InlineData(Inc, "Inc", "ArityMismatch")]
    [InlineData("Head(x, *rest) = x\n", "Head", "ArityMismatch")]
    [InlineData("", "sum", "ArityMismatch")]
    [InlineData("Fam(0) = 0\nFam(n) = n\n", "Fam", "NoMatchingBranch")]
    [InlineData("Lib = { Inc(x) = x + 1 }\n", "Lib.Inc", "ArityMismatch")]
    [InlineData("Bad = 1 / 0\n", "Bad", "DivisionByZero")]
    [InlineData("Bad(*xs) = 1 / 0\n", "Bad", "DivisionByZero")]
    public async Task ReadingTheCollectedList_ReportsTheCallablesOwnValueDemand(string definitions, string argument, string code)
    {
        var collectedSource = definitions + $"Coll(*xs) = xs\nColl({argument})";
        var fixedSource = definitions + $"Id(x) = x\nId({argument})";
        var collected = await AllRoutesAsync(collectedSource);
        var fixedRead = await AllRoutesAsync(fixedSource);

        Assert.Equal("err", collected.Kind);
        Assert.StartsWith(code + ":", collected.Errors.Single(), StringComparison.Ordinal);
        Assert.Equal(fixedRead.Causes, collected.Causes);
        Assert.Equal(Innermost(GenericError(fixedSource)) with { Span = null }, Innermost(GenericError(collectedSource)) with { Span = null });
        Assert.DoesNotContain("collects values", collected.Errors.Single(), StringComparison.Ordinal);

        // Collecting the same argument without reading it demands nothing.
        var ignored = await AllRoutesAsync(definitions + $"Ignore(*xs) = 1\nIgnore({argument})");
        Assert.Equal("ok 1 n=1", ignored.Outcome);
    }

    // ── 7. Independently required static and supply-formation checks are not excused ──────────────

    [Fact]
    public async Task AStaticCheck_IsNotExcusedByAnUnusedCollectedArgument()
    {
        var observation = await AllRoutesAsync("Ignore(*xs) = 1\nRun(z) = Ignore(q)\nRun(0)", requireCleanParse: false);
        Assert.Equal("parse", observation.Kind);
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith("UndeclaredIdentifier: Identifier 'q' is used in an explicitly parameterized algorithm", error, StringComparison.Ordinal);
        Assert.EndsWith(" @ [2:17, 2:18)", error, StringComparison.Ordinal);
    }

    [Fact]
    public async Task AnArbitrarySpread_IsEvaluatedToFormTheSupply_EvenForAnIgnoringCollector()
    {
        var observation = await AllRoutesAsync("Ignore(*xs) = 1\nIgnore((1 / 0)*)");
        Assert.Equal("err DivisionByZero: while evaluating call to Ignore: Division by zero @ [2:8, 2:15)", observation.Outcome);
        var known = await AllRoutesAsync("Ignore(*xs) = 1\nFwd(*xs) = Ignore(xs*)\nFwd(1 / 0)");
        Assert.Equal("ok 1 n=1", known.Outcome);
    }

    // ── 8. Cancellation is reached only through a demand or an invocation ──────────────────────────

    public static TheoryData<string, string, string, string[]> CancellationCases() => new()
    {
        { "a transported cell nothing demands never runs", "Ignore(*xs) = 1\nFwd(*xs) = Ignore(xs*)\nFwd(cancel(1)), 5", "ok S[1, 5] n=2", [] },
        { "the demanding read runs it, and the run observes the cancellation", "Use(*ys) = ys\nFwd(*xs) = Use(xs*)\nFwd(cancel(1)), 5", "cancelled", ["cancel(1)"] },
        { "a transported callable nothing invokes never runs", "K(x) = cancel(x) + 1\nIgnore(*fs) = 1\nFwd(*fs) = Ignore(fs*)\nFwd(K), 5", "ok S[1, 5] n=2", [] },
        { "the invocation through the transported channel runs it", "K(x) = cancel(x) + 1\n" + Apply + Fwd + "Fwd(K), 5", "cancelled", ["cancel(9)"] },
    };

    [Theory]
    [MemberData(nameof(CancellationCases))]
    public async Task Cancellation_IsReachedOnlyThroughADemandOrAnInvocation(string label, string source, string expected, string[] hostCalls)
    {
        var observation = await AllRoutesAsync(source);
        Assert.True(expected == observation.Outcome, $"{label}: expected {expected}, got {observation}");
        Assert.Equal(hostCalls, observation.HostCalls);
    }

    // Known slices belong to the transported cell, not the receiving binder's declared kind.
    // A fixed parameter can retain an unmaterialized collector cell (NEED-01/08).
    [Theory]
    [InlineData("Pass(v) = Apply(v*)\nOuter(*fs) = Pass(fs)\nOuter(Inc)")]
    [InlineData("Pass(v) = { Inner = Apply(v*)\nInner }\nOuter(*fs) = Pass(fs)\nOuter(Inc)")]
    [InlineData("Use(fs) = Apply(fs*)\nOuter(*fs) = Use\nOuter(Inc)")]
    public async Task FixedBindingOfACollectorCell_PreservesItsKnownSlice(string body)
    {
        var observation = await AllRoutesAsync(Inc + Apply + body);
        Assert.Equal("ok 10 n=1", observation.Outcome);
        Assert.Empty(observation.HostCalls);
    }

    public static TheoryData<string, string, string[]> IndependentDemandIntersections() => new()
    {
        { "Ignore(*ys) = 7\nPass(v) = Ignore(v*)\nOuter(*xs) = Pass(xs)\nOuter(trace(4))", "ok 7 n=1", [] },
        { "Use(a, b) = a + b\nOuter(*xs) = Use(xs*, xs*)\nOuter(tick())", "ok 2 n=1", ["tick#1"] },
        { "Z = trace(7)\nCall(f) = f()\nOuter(*xs) = xs, Call(xs*), xs\nOuter(Z)", "ok S[L[7], 7, L[7]] n=1", ["trace(7)", "trace(7)"] },
        { "Choose([], x) = 0\nChoose(tag, x) = tag + x\nOuter(*xs) = Choose(xs*)\nOuter(trace(2), trace(3))", "ok 5 n=1", ["trace(2)", "trace(3)"] },
        { "Outer(*xs) = xs.count\nOuter(trace(1), trace(2), trace(3))", "ok 3 n=1", ["trace(1)", "trace(2)", "trace(3)"] },
    };

    [Theory]
    [MemberData(nameof(IndependentDemandIntersections))]
    public async Task KnownSliceTransport_AndItsConsumersKeepTheirDemandContracts(string source, string expected, string[] effects)
    {
        var observation = await AllRoutesAsync(source);
        Assert.Equal(expected, observation.Outcome);
        Assert.Equal(effects, observation.HostCalls);
    }

    [Fact]
    public async Task FixedBindingDoesNotMakeTheCollectorCallable()
    {
        var observation = await AllRoutesAsync(Inc + Apply + "Pass(v) = Apply(v)\nOuter(*fs) = Pass(fs)\nOuter(Inc)");
        Assert.Equal("err", observation.Kind);
        Assert.Equal("NotAnAlgorithm/NotAnAlgorithm", Assert.Single(observation.Causes));
        Assert.Empty(observation.HostCalls);
    }

    [Fact]
    public async Task FirstOfACollector_MaterializesTheTailBeforeSelecting()
    {
        const string source = "Outer(*xs) = xs.first\nOuter(trace(1), 2 / 0, trace(3))";
        var observation = await AllRoutesAsync(source);
        Assert.Equal("err", observation.Kind);
        Assert.Equal("DivisionByZero/DivByZero", Assert.Single(observation.Causes));
        Assert.EndsWith(" @ [2:17, 2:22)", Assert.Single(observation.Errors), StringComparison.Ordinal);
        Assert.Equal(["trace(1)"], observation.HostCalls);
    }

    [Theory]
    [InlineData("F(x) = x + 1\nF(Fam)")]
    [InlineData("Apply(f) = f\nApply(Fam)")]
    [InlineData("P((x, y)) = x\nP(Fam)")]
    public async Task FixedAndStructuralDemand_KeepTheOriginalFamilyName(string body)
    {
        var source = "Fam(0) = 0\nFam(n) = n\n" + body;
        var observation = await AllRoutesAsync(source);
        Assert.Equal("err", observation.Kind);
        Assert.Equal("NoMatchingBranch/NoMatchingBranch", Assert.Single(observation.Causes));
        Assert.Equal(new EvalError.NoMatchingBranch("Fam"), Innermost(GenericError(source)) with { Span = null });
    }

    // ── Helpers ──────────────────────────────────────────────────────────────────────────────────────

    private sealed record Budget(long Steps, long Checkpoints, int PeakDepth, long MaterializedItems, long MaterializedStringChars);

    /// <summary>
    /// One route's outcome: kind (<c>ok</c>, <c>err</c>, <c>parse</c>, <c>none</c>, <c>cancelled</c>), the neutral
    /// value with the program's emitted count, every error as <c>Code: message @ span</c>, every error's cause
    /// (<c>Code/innermost kind</c>), and the host-call log.
    /// </summary>
    private sealed record Observation(string Kind, string? Value, int? Count, IReadOnlyList<string> Errors, IReadOnlyList<string> Causes, IReadOnlyList<string> HostCalls)
    {
        public bool Equals(Observation? other)
            => other is not null && Kind == other.Kind && Value == other.Value && Count == other.Count
                && Errors.SequenceEqual(other.Errors) && Causes.SequenceEqual(other.Causes) && HostCalls.SequenceEqual(other.HostCalls);

        public override int GetHashCode() => HashCode.Combine(Kind, Value, Count);

        /// <summary>The one-line outcome the expectations are written in.</summary>
        public string Outcome => Kind switch
        {
            "ok" => $"ok {Value} n={Count}",
            "cancelled" => "cancelled",
            _ => $"{Kind} {string.Join(" | ", Errors)}",
        };

        /// <summary>The layer two DIFFERENT programs are compared at: the value, or each error's cause, and the host log.</summary>
        public string Semantic
            => (Kind == "ok" ? $"ok {Value}" : $"{Kind} [{string.Join(", ", Causes)}]") + $" host=[{string.Join(",", HostCalls)}]";

        public override string ToString()
            => $"{Kind} {Value} n={Count} errors=[{string.Join(" | ", Errors)}] host=[{string.Join(",", HostCalls)}]";
    }

    private sealed class HostLog
    {
        private int _ticks;
        public List<string> Calls { get; } = [];
        public CancellationTokenSource Cancellation { get; } = new();

        private Result Log(string call, Result value)
        {
            lock (Calls)
                Calls.Add(call);
            return value;
        }

        public Result Tick() => Log($"tick#{Interlocked.Increment(ref _ticks)}", new Result.Atom(_ticks));

        public Result Trace(Result value) => Log($"trace({SixRouteAgreement.Neutral(value)})", value);

        public Result Cancel(Result value)
        {
            Log($"cancel({SixRouteAgreement.Neutral(value)})", value);
            Cancellation.Cancel();
            return value;
        }
    }

    private static HostOperations Operations(HostLog log, bool suspending)
        => suspending
            ? HostOperations.Create(
                HostOperation.CreateAsync("tick", async (_, _) => { await Task.Yield(); return log.Tick(); }),
                HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return log.Trace(args[0]); }, "x"),
                HostOperation.CreateAsync("cancel", async (args, _) => { await Task.Yield(); return log.Cancel(args[0]); }, "x"))
            : HostOperations.Create(
                HostOperation.Create("tick", (_, _) => log.Tick()),
                HostOperation.Create("trace", (args, _) => log.Trace(args[0]), "x"),
                HostOperation.Create("cancel", (args, _) => log.Cancel(args[0]), "x"));

    private static async Task<(Observation Observation, Budget? Budget)> ObserveAsync(SixRouteAgreement.Route route, string source)
    {
        var log = new HostLog();
        var operations = Operations(log, route is SixRouteAgreement.Route.EngineAsyncTwin or SixRouteAgreement.Route.ForcedTwin);
        var options = new RunOptions { HostOperations = operations, EvaluationCancellationToken = log.Cancellation.Token };
        try
        {
            switch (route)
            {
                case SixRouteAgreement.Route.EngineSync:
                    return (FromRunResult(KatLangEngine.Run(source, options), log), null);
                case SixRouteAgreement.Route.EngineAsync:
                case SixRouteAgreement.Route.EngineAsyncTwin:
                    return (FromRunResult(await KatLangEngine.RunAsync(source, options), log), null);
            }

            var parsed = Parser.Parse(source, options);
            if (parsed.HasErrors)
            {
                var errors = parsed.Diagnostics.Where(static d => d.Severity == DiagnosticSeverity.Error).Select(KatLangError.FromDiagnostic).ToArray();
                return (new Observation("parse", null, null, [.. errors.Select(Describe)], [.. errors.Select(Cause)], [.. log.Calls]), null);
            }

            var program = new Expr.AlgorithmExpr(parsed.Root);
            var (result, budget) = route switch
            {
                SixRouteAgreement.Route.Generic => Evaluator.RunCountedObserved(program, enableOptimizations: false,
                    hostOperations: operations, cancellationToken: log.Cancellation.Token),
                SixRouteAgreement.Route.Optimized => Evaluator.RunCountedObserved(program, enableOptimizations: true,
                    hostOperations: operations, cancellationToken: log.Cancellation.Token),
                SixRouteAgreement.Route.ForcedTwin => await Evaluator.RunCountedObservedAsync(program,
                    zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                    hostOperations: operations, cancellationToken: log.Cancellation.Token),
                _ => throw new ArgumentOutOfRangeException(nameof(route), route, null),
            };
            var counters = new Budget(budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth,
                budget.MaterializedItems, budget.MaterializedStringChars);
            return result.IsError
                ? (FromError(KatLangError.FromEvalError(result.Error), log), counters)
                : (new Observation("ok", SixRouteAgreement.Neutral(result.Value.Value), result.Value.EmittedCount, [], [], [.. log.Calls]), counters);
        }
        catch (OperationCanceledException)
        {
            return (new Observation("cancelled", null, null, [], [], [.. log.Calls]), null);
        }
    }

    /// <summary>
    /// Runs <paramref name="source"/> on every route; requires every route to agree with the synchronous engine and
    /// the three evaluator routes to charge identical budgets. Returns the oracle. Unless
    /// <paramref name="requireCleanParse"/> is false, the source must be valid KatLang with output.
    /// </summary>
    private static async Task<Observation> AllRoutesAsync(string source, bool requireCleanParse = true)
    {
        var (oracle, _) = await ObserveAsync(SixRouteAgreement.Route.EngineSync, source);
        if (requireCleanParse)
            Assert.True(oracle.Kind is not ("parse" or "none"), $"source must parse cleanly and have output: {oracle}\nsource:\n{source}");
        Budget? counters = null;
        foreach (var route in SixRouteAgreement.Routes.Skip(1))
        {
            var (observation, budget) = await ObserveAsync(route, source);
            Assert.True(oracle.Equals(observation), $"{route}: expected {oracle}, got {observation}\nsource:\n{source}");
            if (budget is null)
                continue;
            if (counters is null)
                counters = budget;
            else
                Assert.True(counters == budget, $"{route}: budget {budget} differs from {counters}\nsource:\n{source}");
        }

        return oracle;
    }

    private static Observation FromRunResult(RunResult result, HostLog log) => result switch
    {
        RunResult.Success success => new("ok", SixRouteAgreement.Neutral(success.Value), success.EmittedCount, [], [], [.. log.Calls]),
        RunResult.EvalFailure failure => new("err", null, null, [.. failure.Errors.Select(Describe)], [.. failure.Errors.Select(Cause)], [.. log.Calls]),
        RunResult.ParseFailure failure => new("parse", null, null, [.. failure.Errors.Select(Describe)], [.. failure.Errors.Select(Cause)], [.. log.Calls]),
        RunResult.NoProgramOutput none => new("none", null, null, [none.Diagnostic.Code.ToString()], [], [.. log.Calls]),
    };

    private static Observation FromError(KatLangError error, HostLog log)
        => new("err", null, null, [Describe(error)], [Cause(error)], [.. log.Calls]);

    private static string Describe(KatLangError error) => $"{error.Code}: {error.Message} @ {error.Span}";

    private static string Cause(KatLangError error)
        => $"{error.Code}/{(error.Source is EvalError evalError ? Innermost(evalError).GetType().Name : "front-end")}";

    private static EvalError GenericError(string source)
    {
        var log = new HostLog();
        var operations = Operations(log, suspending: false);
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), enableOptimizations: false, hostOperations: operations);
        Assert.True(result.IsError, source);
        return result.Error;
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }
}
