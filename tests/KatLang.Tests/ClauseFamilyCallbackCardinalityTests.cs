using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

/// <summary>
/// D1 (constitution-implementation audit, 2026-10-09): A CLAUSE-FAMILY CALLBACK IS JUDGED BY ITS OWN EMITTED
/// COUNT. HO-03: a <c>map</c> transform and a <c>reduce</c> step must each EMIT exactly one top-level value that
/// is not <c>()</c>, judged by the callback's own emitted count and never re-counted at the call's value
/// boundary; a <c>filter</c> predicate's value must be a Boolean. PAT-11: a clause family is an ordinary
/// callable, so its callback result is judged exactly like a user algorithm's, while its ORDINARY call keeps
/// the value boundary (one value). C# had evaluated family callbacks through the ordinary call's re-count and
/// accepted a two-row family transform (<c>F(0) = 1, 2</c> / <c>map([0], F)</c> gave <c>[(1, 2)]</c>); the
/// callback receiver now selects <c>recount: false</c> for a family exactly as it does for a user algorithm
/// (<c>EvalNeedCallbackBody</c>), like Lean's <c>evalConditionalCallbackCallCounted</c>. The source observer
/// matrix runs on the six established routes, requiring the same value, emitted count, errors
/// (code, message, span) and host-call log and identical budget counters on the three evaluator routes.
/// The optimizer instrumentation facts compare generic/optimized execution. The boundary companion covers
/// deferred sources on four async configurations and host-built trees on three evaluator configurations;
/// those shapes cannot use the six source routes. Expectations follow the law (host totality is explicitly
/// labeled). Lean: <c>CoreTests/FamilyCallbackCardinality.lean</c>; spec cases
/// <c>clause-family-multirow-callback-rejected</c>, <c>clause-family-multirow-reduce-step-rejected</c>,
/// <c>clause-family-callback-single-value-accepted</c>.
/// </summary>
public sealed partial class ClauseFamilyCallbackCardinalityTests
{
    private const string Fam = "F(0) = 1, 2\nF(n) = n, n\n";
    private const string OneBranch = "F(0) = 1, 2\n";
    private const string Red = "R(e, 0) = e, 0\nR(e, acc) = e, acc\n";
    private const string Pair = "P(0) = (1, 2)\nP(n) = (n, n)\n";
    private const string MapContract = "map transform must return a single element";
    private const string ReduceContract = "reduce step must return a single accumulator value";

    // ── 1. The canonical witnesses (D1-A … D1-F), pinned exactly ────────────────────────────────

    public static TheoryData<string, string, string> CanonicalWitnesses() => new()
    {
        // D1-A: a two-row multi-branch family transform.
        { "D1-A", Fam + "map([0, 3], F)", $"ArityMismatch: while evaluating call to map: {MapContract}: Bad arity @ [3:1, 3:15)" },
        // D1-B: a lone literal clause is a one-branch family.
        { "D1-B", OneBranch + "map([0], F)", $"ArityMismatch: while evaluating call to map: {MapContract}: Bad arity @ [2:1, 2:12)" },
        // D1-C: a two-row family reduce step.
        { "D1-C", Red + "reduce([1], R, 0)", $"ArityMismatch: while evaluating call to reduce: {ReduceContract}: Bad arity @ [3:1, 3:18)" },
        // D1-D, D1-E: the ordinary user-algorithm controls.
        { "D1-D", "D(x) = x, x\nmap([1, 3], D)", $"ArityMismatch: while evaluating call to map: {MapContract}: Bad arity @ [2:1, 2:15)" },
        { "D1-E", "R(e, acc) = e, acc\nreduce([1], R, 0)", $"ArityMismatch: while evaluating call to reduce: {ReduceContract}: Bad arity @ [2:1, 2:18)" },
        // D1-F: a family transform emitting one `()`.
        { "D1-F", "F(0) = ()\nF(n) = n\nmap([0], F)", $"ArityMismatch: while evaluating call to map: {MapContract}: Bad arity @ [3:1, 3:12)" },
    };

    [Theory]
    [MemberData(nameof(CanonicalWitnesses))]
    public async Task CanonicalWitness_IsRejectedByTheCallbackContract(string id, string source, string expected)
    {
        var (observation, _) = await AllRoutesAsync(source);
        Assert.True(observation.Kind == "err", $"{id}: {observation}");
        Assert.Equal(expected, Assert.Single(observation.Errors));
        Assert.Empty(observation.HostCalls);

        // The structured error: the contract's context around the innermost bad-arity verdict.
        var error = GenericError(source);
        Assert.IsType<EvalError.BadArity>(Innermost(error));
        Assert.Contains(expected.Contains(MapContract, StringComparison.Ordinal) ? MapContract : ReduceContract, Frames(error));
    }

    // ── 2. Multi-row family callbacks are rejected, whatever route reaches the family ──────────────

    /// <summary>label, source, and the operation whose callback contract rejects the result.</summary>
    public static TheoryData<string, string, string> MultiRowFamilyCallbacks() => new()
    {
        { "binder clause selected", Fam + "map([3], F)", "map" },
        { "literal clause selected", Fam + "map([0], F)", "map" },
        { "a later item's clause emits two items", "F(0) = [0]*\nF(n) = [n, n]*\nZ = 0\nmap([0, 3], F)", "map" },
        { "the literal clause emits two items after a valid item", "F(0) = [1, 2]*\nF(n) = [n]*\nZ = 0\nmap([3, 0], F)", "map" },
        { "three rows", "F(0) = 1, 2, 3\nF(n) = n, n, n\nmap([0], F)", "map" },
        { "structural clauses", "F((a, 0)) = a, 0\nF((a, b)) = a, b\nmap([(1, 2)], F)", "map" },
        { "list-pattern clauses", "F([0]) = 0, 0\nF([x]) = x, x\nmap([[1]], F)", "map" },
        { "Boolean literal clauses", "F(true) = 1, 1\nF(false) = 0, 0\nmap([true], F)", "map" },
        { "a () row beside a value row", "F(0) = (), 1\nF(n) = n, n\nmap([0], F)", "map" },
        { "a spread row emitting two items", "F(0) = [5, 6]*\nF(n) = n\nmap([0], F)", "map" },
        { "a spread of a bound sequence element", "F((0, 0)) = (0, 0)*\nF(p) = p*\nZ = 0\nmap([5, (1, 2)], F)", "map" },
        { "the two-row base clause of a recursive family", "F(0) = [1, 2]*\nF(n) = [F(n - 1)]*\nZ = 0\nmap([0], F)", "map" },
        { "callable alias", Fam + "G = F\nmap([0], G)", "map" },
        { "alias chain", Fam + "G = F\nH = G\nmap([0], H)", "map" },
        { "forwarded through a parameter", Fam + "Apply(f, xs) = map(xs, f)\nApply(F, [0])", "map" },
        { "lifted formula", Fam + "K = map(xs, F)\nK([0])", "map" },
        { "qualified member", "Lib = {\n  public F(0) = 1, 2\n  public F(n) = n, n\n}\nmap([0], Lib.F)", "map" },
        { "opened member", "open Lib\nLib = {\n  public F(0) = 1, 2\n  public F(n) = n, n\n}\nmap([0], F)", "map" },
        { "dot call", Fam + "[0, 3].map(F)", "map" },
        { "spread dot receiver", Fam + "[[0]]*.map(F)", "map" },
        { "nested map", Fam + "map([[0]], { map(x, F) })", "map" },
        { "after filter", Fam + "map(filter([0, 3], { x > 0 }), F)", "map" },
        { "inside a loop step", Fam + "Step(xs) = map(xs, F)\nrepeat(Step, 1, [0])", "map" },
        { "reduce, binder clause selected", Red + "reduce([1], R, 5)", "reduce" },
        { "reduce, one-branch family", "R(e, 0) = e, 0\nreduce([1], R, 0)", "reduce" },
        { "reduce, the second step", "R(e, 0) = [e + 1]*\nR(e, acc) = [e, acc]*\nZ = 0\nreduce([1, 2], R, 0)", "reduce" },
        { "reduce, forwarded", Red + "Fold(r, xs) = reduce(xs, r, 0)\nFold(R, [1])", "reduce" },
        { "reduce, dot call", Red + "[1].reduce(R, 0)", "reduce" },
        { "reduce, forwarded dot call", Red + "Fold(r, xs) = xs.reduce(r, 0)\nFold(R, [1])", "reduce" },
    };

    [Theory]
    [MemberData(nameof(MultiRowFamilyCallbacks))]
    public async Task MultiRowFamilyCallback_IsRejected(string label, string source, string operation)
    {
        var (observation, _) = await AllRoutesAsync(source);
        Assert.True(observation.Kind == "err", $"{label}: {observation}");
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith("ArityMismatch: ", error, StringComparison.Ordinal);
        Assert.Contains($"{(operation == "map" ? MapContract : ReduceContract)}: Bad arity @ ", error, StringComparison.Ordinal);
        Assert.IsType<EvalError.BadArity>(Innermost(GenericError(source)));
    }

    /// <summary>The frames and positions of the rejection are those of the ordinary user-callback rejection.</summary>
    public static TheoryData<string, string> RejectionFrames() => new()
    {
        { Fam + "[0, 3].map(F)", $"ArityMismatch: while evaluating dotCall .map of [0, 3]: {MapContract}: Bad arity @ [3:1, 3:14)" },
        { Fam + "Apply(f, xs) = map(xs, f)\nApply(F, [0])",
            $"ArityMismatch: while evaluating call to Apply: while evaluating call to map: {MapContract}: Bad arity @ [3:16, 3:26)" },
        { Red + "Fold(r, xs) = xs.reduce(r, 0)\nFold(R, [1])",
            $"ArityMismatch: while evaluating call to Fold: while evaluating dotCall .reduce of xs: {ReduceContract}: Bad arity @ [3:15, 3:30)" },
        { Fam + "map([[0]], { map(x, F) })",
            "ArityMismatch: while evaluating call to map: while evaluating map transform (map passes each iterated collection item as collected; "
            + "a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact): "
            + $"while evaluating call to map: {MapContract}: Bad arity @ [3:14, 3:23)" },
    };

    [Theory]
    [MemberData(nameof(RejectionFrames))]
    public async Task Rejection_IsReportedUnderTheCallFramesOfTheWrittenCallbackUse(string source, string expected)
    {
        var (observation, _) = await AllRoutesAsync(source);
        Assert.Equal(expected, Assert.Single(observation.Errors));
    }

    // ── 3. One emitted value is one callback result, however many elements it holds ───────────────

    public static TheoryData<string, string, string> SingleValueFamilyCallbacks() => new()
    {
        { "one number", "F(0) = 1\nF(n) = n * 10\nmap([0, 3], F)", "L[1, 30]" },
        { "one sequence value", Pair + "map([0, 3], P)", "L[S[1, 2], S[3, 3]]" },
        { "one sequence value, one-branch family", "P(0) = (1, 2)\nmap([0], P)", "L[S[1, 2]]" },
        { "one list", "F(0) = [1, 2]\nF(n) = [n]\nmap([0, 3], F)", "L[L[1, 2], L[3]]" },
        { "one empty list", "F(0) = []\nF(n) = [n]\nmap([0, 3], F)", "L[L[], L[3]]" },
        { "one empty list, one-branch family", "F(0) = []\nmap([0], F)", "L[L[]]" },
        { "one string", "F(0) = 'zero'\nF(n) = n.string\nmap([0, 3], F)", "L['zero', '3']" },
        { "an inner call's one value", "D(x) = x, x\nF(0) = D(0)\nF(n) = D(n)\nmap([0, 3], F)", "L[S[0, 0], S[3, 3]]" },
        { "a recursive clause's inner call", "F(0) = [1, 2]*\nF(n) = [F(n - 1)]*\nZ = 0\nmap([1], F)", "L[S[1, 2]]" },
        { "a completed loop", "Fib(x, y) = y, x + y\nF(0) = repeat(Fib, 2, 0, 1)\nF(n) = repeat(Fib, 2, n, 1)\nmap([0, 1], F)", "L[S[1, 2], S[2, 3]]" },
        { "a spread of one item", "F(0) = [5]*\nF(n) = n\nmap([0, 3], F)", "L[5, 3]" },
        { "a spread of a bound scalar", "F((0, 0)) = (0, 0)*\nF(p) = p*\nZ = 0\nmap([5, 7], F)", "L[5, 7]" },
        { "η-expanded block", Fam + "map([0, 3], { F(x) })", "L[S[1, 2], S[3, 3]]" },
        { "η-expanded dot call", Fam + "map([0, 3], { x.F })", "L[S[1, 2], S[3, 3]]" },
        { "structural clauses", "Swap((a, 0)) = (0, a)\nSwap((a, b)) = (b, a)\nmap([(1, 2), (3, 0)], Swap)", "L[S[2, 1], S[0, 3]]" },
        { "PAT-11's example", "Fact(0) = 1\nFact(n) = n * Fact(n - 1)\nIsZero(0) = true\nIsZero(n) = false\n"
            + "map([0, 3, 5], Fact), filter([0, 1, 0], IsZero), 5.Fact", "S[L[1, 6, 120], L[0, 0], 120]" },
        { "HO-02's family example", "F(0) = 'z'\nF((a, b)) = a + b\nF(n) = n * 10\nmap([0, (1, 2), 3], F), F(0), F((1, 2)), F(3)",
            "S[L['z', 3, 30], 'z', 3, 30]" },
        { "qualified member", "Lib = {\n  public F(0) = 1\n  public F(n) = n * 2\n}\nmap([0, 3], Lib.F)", "L[1, 6]" },
        { "callable alias", Pair + "G = P\nmap([0], G)", "L[S[1, 2]]" },
        { "inside a loop step", Pair + "Step(xs) = map(xs, P)\nrepeat(Step, 1, [0, 3])", "L[S[1, 2], S[3, 3]]" },
        { "reduce, one value", "Add(e, 0) = e\nAdd(e, acc) = e + acc\nreduce([1, 2, 3], Add, 0)", "6" },
        { "reduce, one sequence accumulator", "R(e, 0) = (e, 0)\nR(e, acc) = (e, acc)\nreduce([1], R, 0)", "S[1, 0]" },
        { "reduce, η-expanded block", Red + "reduce([1], { R(e, a) }, 0)", "S[1, 0]" },
        { "reduce, alias, forwarding and dot call", "Add(e, 0) = e\nAdd(e, acc) = e + acc\nG = Add\nFold(r, xs) = reduce(xs, r, 0)\n"
            + "Fold(G, [1, 2, 3]), [1, 2, 3].reduce(Add, 0)", "S[6, 6]" },
        { "filter, one Boolean", "IsZero(0) = true\nIsZero(n) = false\nfilter([0, 1, 0], IsZero)", "L[0, 0]" },
        { "filter, one-branch family", "P(0) = true\nfilter([0], P)", "L[0]" },
    };

    [Theory]
    [MemberData(nameof(SingleValueFamilyCallbacks))]
    public async Task SingleValueFamilyCallback_IsAccepted(string label, string source, string expected)
    {
        var (observation, _) = await AllRoutesAsync(source);
        Assert.True(observation.Kind == "ok", $"{label}: {observation}");
        Assert.Equal(expected, observation.Value);
    }

    [Fact]
    public async Task OneEmittedSequence_IsNotSeveralRows()
    {
        // As ordinary calls, a two-row clause and a one-row clause holding the pair are the same value ...
        var (direct, _) = await AllRoutesAsync("F(0) = 1, 2\nP(0) = (1, 2)\nF(0) == P(0), F(0), P(0)");
        Assert.Equal("S[true, S[1, 2], S[1, 2]]", direct.Value);

        // ... but only the one-row clause is ONE callback result: the contract counts emitted rows, not elements.
        var (pair, _) = await AllRoutesAsync("P(0) = (1, 2)\nmap([0], P), reduce([1], { (e, a) }, 0)");
        Assert.Equal("S[L[S[1, 2]], S[1, 0]]", pair.Value);
        var (rows, _) = await AllRoutesAsync("F(0) = 1, 2\nmap([0], F)");
        Assert.Contains(MapContract, Assert.Single(rows.Errors), StringComparison.Ordinal);
    }

    // ── 4. Empty callback results ──────────────────────────────────────────────────────────────────

    /// <summary>label, source, and the expected outcome: the contract (<c>map</c>/<c>reduce</c>) that
    /// rejects the result, or <c>ok VALUE</c>.</summary>
    public static TheoryData<string, string, string> EmptyCallbackResults() => new()
    {
        { "one () row (D1-F)", "F(0) = ()\nF(n) = n\nmap([0], F)", "map" },
        { "one () row in every clause", "F(0) = ()\nF(n) = ()\nmap([0, 3], F)", "map" },
        { "zero rows: a spread of []", "F(0) = []*\nF(n) = n\nmap([0], F)", "map" },
        { "zero rows: a spread of ()", "F(0) = ()*\nF(n) = n\nmap([0], F)", "map" },
        { "reduce, one () row", "R(e, 0) = ()\nR(e, acc) = acc\nreduce([1], R, 0)", "reduce" },
        { "reduce, zero rows", "R(e, 0) = []*\nR(e, acc) = acc\nreduce([1], R, 0)", "reduce" },
        { "user identity of a () element (control)", "Id(x) = x\nmap([(), 1], Id)", "map" },
        { "one [] is one value", "F(0) = []\nmap([0], F)", "ok L[L[]]" },
        { "map over [] never invokes", Fam + "map([], F)", "ok L[]" },
        { "reduce over [] returns the initial value", Red + "reduce([], R, 7)", "ok 7" },
    };

    [Theory]
    [MemberData(nameof(EmptyCallbackResults))]
    public async Task EmptyCallbackResult_FollowsTheContract(string label, string source, string expected)
    {
        var (observation, _) = await AllRoutesAsync(source);
        if (expected.StartsWith("ok ", StringComparison.Ordinal))
        {
            Assert.True(observation.Kind == "ok", $"{label}: {observation}");
            Assert.Equal(expected[3..], observation.Value);
            return;
        }

        Assert.True(observation.Kind == "err", $"{label}: {observation}");
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith("ArityMismatch: ", error, StringComparison.Ordinal);
        Assert.Contains($"{(expected == "map" ? MapContract : ReduceContract)}: Bad arity @ ", error, StringComparison.Ordinal);
    }

    // ── 5. The ordinary call keeps its value boundary ──────────────────────────────────────────────

    [Theory]
    [InlineData(Fam, "0", "S[1, 2]")]
    [InlineData(Fam, "3", "S[3, 3]")]
    [InlineData(OneBranch, "0", "S[1, 2]")]
    public async Task OrdinaryCall_IsOneValue_WhileTheSameClauseIsRejectedAsACallback(string definitions, string argument, string value)
    {
        // The ordinary call crosses the value boundary: one sequence value, emitted count 1 ...
        var (direct, _) = await AllRoutesAsync(definitions + $"F({argument})");
        Assert.Equal(("ok", value, 1), (direct.Kind, direct.Value, direct.Count));

        // ... one list element, one collected argument, a value of two elements ...
        var (consumers, _) = await AllRoutesAsync(definitions + $"Coll(*xs) = xs\n[F({argument})], Coll(F({argument})), F({argument}).count");
        Assert.Equal($"S[L[{value}], L[{value}], 2]", consumers.Value);

        // ... while the very same clause as a map transform emits two rows, as does the η-block that
        // spreads the call's one value back into two rows; the η-block of the plain call is one value.
        var (mapped, _) = await AllRoutesAsync(definitions + $"map([{argument}], F)");
        Assert.Contains($"{MapContract}: Bad arity", Assert.Single(mapped.Errors), StringComparison.Ordinal);
        var (spread, _) = await AllRoutesAsync(definitions + $"map([{argument}], {{ F(x)* }})");
        Assert.Contains($"{MapContract}: Bad arity", Assert.Single(spread.Errors), StringComparison.Ordinal);
        var (eta, _) = await AllRoutesAsync(definitions + $"map([{argument}], {{ F(x) }})");
        Assert.Equal($"L[{value}]", eta.Value);
    }

    [Fact]
    public async Task OrdinaryReduceStepCall_IsOneValue_WhileTheReduceCallbackIsRejected()
    {
        var (direct, _) = await AllRoutesAsync(Red + "R(1, 0), R(2, 5)");
        Assert.Equal(("ok", "S[S[1, 0], S[2, 5]]", 2), (direct.Kind, direct.Value, direct.Count));
        var (reduced, _) = await AllRoutesAsync(Red + "reduce([1], R, 0)");
        Assert.Contains($"{ReduceContract}: Bad arity", Assert.Single(reduced.Errors), StringComparison.Ordinal);
    }

    /// <summary>Every ordinary consumer of a family call reads ONE value (VAL-06), unchanged by D1.</summary>
    public static TheoryData<string, string, string> OrdinaryFamilyCalls() => new()
    {
        { "list of calls", Fam + "[F(0), F(3)]", "L[S[1, 2], S[3, 3]]" },
        { "collectors, count and spread", Fam + "Coll(*xs) = xs\nCnt(*xs) = xs.count\nColl(F(0)), Cnt(F(3)), F(0).count, (F(0))*.Coll",
            "S[L[S[1, 2]], 1, 2, L[1, 2]]" },
        { "selection", Fam + "F(0):1, first(F(3)), F(0).count", "S[2, 3, 2]" },
        { "if branches", Fam + "if(true, F(0), 0), [if(false, 0, F(3))]", "S[S[1, 2], L[S[3, 3]]]" },
        { "a higher-order parameter's ordinary call", Fam + "Apply(f, x) = f(x)\nApply(F, 0), map([0], { Apply(F, x) })",
            "S[S[1, 2], L[S[1, 2]]]" },
        { "dot calls", Fam + "0.F, 3.F", "S[S[1, 2], S[3, 3]]" },
        { "a () clause", "F(0) = ()\nF(n) = n\n[F(0), F(3)]", "L[S[], 3]" },
        { "single-branch", OneBranch + "F(0), [F(0)]", "S[S[1, 2], L[S[1, 2]]]" },
    };

    [Theory]
    [MemberData(nameof(OrdinaryFamilyCalls))]
    public async Task OrdinaryFamilyCall_IsOneValue(string label, string source, string expected)
    {
        var (observation, _) = await AllRoutesAsync(source);
        Assert.True(observation.Kind == "ok", $"{label}: {observation}");
        Assert.Equal(expected, observation.Value);
    }

    // ── 6. filter keeps its own contract: the predicate's VALUE must be a Boolean ──────────────────

    [Theory]
    [InlineData("P(0) = true, true\nP(n) = false, false\nfilter([0, 3], P)")]
    [InlineData("P(0) = true, true\nfilter([0], P)")]
    [InlineData("Q(x) = true, true\nfilter([0], Q)")]
    [InlineData("P(0) = true, true\nP(n) = false, false\ncount(filter(range(0, 3), P))")]
    [InlineData("P(0) = true, true\nP(n) = false, false\nfilter([0, 3], P).count")]
    public async Task FilterPredicate_WithTwoRows_IsTheBooleanRequiredTypeError(string source)
    {
        var (observation, _) = await AllRoutesAsync(source);
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith("TypeMismatch: ", error, StringComparison.Ordinal);
        Assert.Contains("filter predicate result must be a Boolean value (true or false), but was a sequence value with 2 sequence elements: (true, true)",
            error, StringComparison.Ordinal);
    }

    [Fact]
    public void FusedFilterCount_InvokesAFamilyPredicateUnderTheSameContract()
    {
        var fused = Observe("P(0) = true\nP(n) = n mod 2 == 0\ncount(filter(range(0, 6), P))", optimize: true);
        Assert.Equal("4", fused.Value);
        Assert.Equal(1, fused.Sequences.FilterCountFusionHits);
        Assert.Equal(7, fused.Sequences.FilterCountPredicateCalls);

        // The fused pipeline stops at the first predicate result that is not a Boolean, charging exactly
        // what the generic composition charges.
        var rejected = Observe("P(0) = true, true\nP(n) = false, false\ncount(filter(range(0, 3), P))", optimize: true);
        Assert.Equal("err TypeMismatch", rejected.Value);
        Assert.Equal(1, rejected.Sequences.FilterCountFusionHits);
        Assert.Equal(1, rejected.Sequences.FilterCountPredicateCalls);
        Assert.Equal(Observe("P(0) = true, true\nP(n) = false, false\ncount(filter(range(0, 3), P))", optimize: false).Budget, rejected.Budget);
    }

    // ── 7. Loop steps are not callbacks (Q-23, LOOP-03): their rows are the next state ─────────────

    public static TheoryData<string, string, string> FamilyLoopSteps() => new()
    {
        { "two rows are two state slots", "S(0) = 1, 2\nS(n) = n, n\nrepeat(S, 1, 0)", "ok S[1, 2]" },
        { "dot spelling", "S(0) = 1, 2\nS(n) = n, n\nS.repeat(1, 0)", "ok S[1, 2]" },
        { "the next iteration binds the two slots", "S(0) = 1, 2\nS(n) = n, n\nrepeat(S, 2, 0)", "err ArityMismatch" },
        { "a two-parameter family", "T(a, 0) = a, 1\nT(a, b) = a + b, b + 1\nrepeat(T, 3, 0, 0)", "ok S[3, 3]" },
        { "the while flag row", "Step(0) = 0, false\nStep(n) = n - 1, true\nwhile(Step, 3)", "ok 0" },
    };

    [Theory]
    [MemberData(nameof(FamilyLoopSteps))]
    public async Task FamilyLoopStep_KeepsTheStateProtocol(string label, string source, string expected)
    {
        var (observation, _) = await AllRoutesAsync(source);
        if (expected.StartsWith("ok ", StringComparison.Ordinal))
        {
            Assert.True(observation.Kind == "ok", $"{label}: {observation}");
            Assert.Equal(expected[3..], observation.Value);
            return;
        }

        var error = Assert.Single(observation.Errors);
        Assert.StartsWith(expected[4..] + ": ", error, StringComparison.Ordinal);
        Assert.DoesNotContain(MapContract, error, StringComparison.Ordinal);
        Assert.DoesNotContain(ReduceContract, error, StringComparison.Ordinal);
    }

    [Fact]
    public void PlannedLoop_RunsAFamilyMapCallbackUnderTheSameContract()
    {
        var rejected = Observe(Fam + "Step(xs) = map(xs, F)\nrepeat(Step, 1, [0])", optimize: true);
        Assert.Equal("err ArityMismatch", rejected.Value);
        Assert.True(rejected.Loops.OptimizedLoopHits > 0, "the optimized route must plan the loop");

        var accepted = Observe(Pair + "Step(xs) = map(xs, P)\nrepeat(Step, 1, [0, 3])", optimize: true);
        Assert.Equal("L[S[1, 2], S[3, 3]]", accepted.Value);
        Assert.True(accepted.Loops.OptimizedLoopHits > 0, "the optimized route must plan the loop");
        Assert.Equal(Observe(Pair + "Step(xs) = map(xs, P)\nrepeat(Step, 1, [0, 3])", optimize: false).Budget, accepted.Budget);
    }

    // ── 8. Demand, order and effects ───────────────────────────────────────────────────────────────

    [Fact]
    public async Task UninvokedCallbacks_HaveNoEffect()
    {
        var (observation, _) = await AllRoutesAsync(
            "F(0) = trace(1), 2\nF(n) = trace(n), n\nR(e, 0) = trace(e), 0\nR(e, acc) = trace(e), acc\nK(f) = 7\n"
            + "map([], F), reduce([], R, trace(7)), K(F)");
        Assert.Equal(("ok", "S[L[], 7, 7]"), (observation.Kind, observation.Value));
        Assert.Equal(["trace(7)"], observation.HostCalls);
    }

    [Fact]
    public async Task Map_InvokesItemsInOrder_AndStopsAtTheRejectedResult()
    {
        var (observation, _) = await AllRoutesAsync("F(0) = [trace(0)]*\nF(n) = [trace(n), n]*\nZ = 0\nmap([0, 1, 2], F)");
        Assert.Equal($"ArityMismatch: while evaluating call to map: {MapContract}: Bad arity @ [4:1, 4:18)", Assert.Single(observation.Errors));
        Assert.Equal(["trace(0)", "trace(1)"], observation.HostCalls);
    }

    [Fact]
    public async Task Reduce_StopsAtTheRejectedStep()
    {
        var (observation, _) = await AllRoutesAsync("R(e, 0) = [trace(e)]*\nR(e, acc) = [trace(e), acc]*\nZ = 0\nreduce([1, 2, 3], R, 0)");
        Assert.Equal($"ArityMismatch: while evaluating call to reduce: {ReduceContract}: Bad arity @ [4:1, 4:24)", Assert.Single(observation.Errors));
        Assert.Equal(["trace(1)", "trace(2)"], observation.HostCalls);
    }

    [Fact]
    public async Task RejectedCallback_RanItsWholeBodyExactlyOnce()
    {
        // The contract judges the result: every row of the selected clause ran first, once.
        var (observation, _) = await AllRoutesAsync("F(0) = tick(), tick()\nF(n) = n, n\nmap([0], F)");
        Assert.Contains(MapContract, Assert.Single(observation.Errors), StringComparison.Ordinal);
        Assert.Equal(["tick#1", "tick#2"], observation.HostCalls);
    }

    [Fact]
    public async Task AcceptedFamilyCallbacks_InvokeOncePerItem()
    {
        var (observation, _) = await AllRoutesAsync("F(0) = tick()\nF(n) = (tick(), n)\nmap([0, 5], F), tick()");
        Assert.Equal(("ok", "S[L[1, S[2, 5]], 3]"), (observation.Kind, observation.Value));
        Assert.Equal(["tick#1", "tick#2", "tick#3"], observation.HostCalls);
    }

    [Theory]
    [InlineData(3L)]
    [InlineData(42L)]
    public async Task AcceptedFamilyCallbacks_DrawExactlyTheDirectStream(long seed)
    {
        var (mapped, _) = await AllRoutesAsync("G(0) = random(0, 1)\nG(n) = random(0, 1)\nmap([0, 1], G), random(0, 1)", seed);
        var (direct, _) = await AllRoutesAsync("[random(0, 1), random(0, 1)], random(0, 1)", seed);
        Assert.Equal("ok", mapped.Kind);
        Assert.Equal(direct.Value, mapped.Value);
    }

    [Theory]
    [InlineData("F(0) = cancel(0), 1\nF(n) = n, n\nmap([0], F)", "U(x) = cancel(x), 1\nmap([0], U)")]
    [InlineData("R(e, 0) = cancel(e), 0\nR(e, acc) = e, acc\nreduce([1], R, 0)", "U(e, acc) = cancel(e), 0\nreduce([1], U, 0)")]
    [InlineData(Pair + "C(0) = cancel(0)\nC(n) = n\nmap([0], C), map([0], P)", Pair + "U(x) = cancel(x)\nmap([0], U), map([0], P)")]
    public async Task Cancellation_InAFamilyCallback_IsObservedAsInAUserCallback(string family, string user)
    {
        var (fam, _) = await AllRoutesAsync(family);
        var (usr, _) = await AllRoutesAsync(user);
        Assert.Equal("cancelled", fam.Kind);
        Assert.Equal(usr.Semantic, fam.Semantic);
    }

    // ── 9. The law: a family callback is judged exactly like its selected clause as a user callback ──
    //       (Lean `fcFamilyCallbackEqualsItsSelectedClause`)

    private const string LawDefinitions =
        Fam + Red + Pair
        + "One(0) = 1, 2\nE(0) = ()\nE(n) = n\nBoth(0) = true, true\nBoth(n) = false, false\n"
        + "U0(x) = 1, 2\nD(x) = x, x\nUp0(x) = (1, 2)\nUp(n) = (n, n)\nUe(x) = ()\nRu(e, acc) = e, acc\nQ(x) = true, true\n";

    public static TheoryData<string, string> SelectedClauseLawCases() => new()
    {
        { "map([0], F)", "map([0], U0)" },
        { "map([3], F)", "map([3], D)" },
        { "map([0], One)", "map([0], U0)" },
        { "map([0], P)", "map([0], Up0)" },
        { "map([3], P)", "map([3], Up)" },
        { "map([0], E)", "map([0], Ue)" },
        { "reduce([1], R, 0)", "reduce([1], Ru, 0)" },
        { "reduce([1], R, 5)", "reduce([1], Ru, 5)" },
        { "filter([0], Both)", "filter([0], Q)" },
    };

    [Theory]
    [MemberData(nameof(SelectedClauseLawCases))]
    public async Task FamilyCallback_IsJudgedLikeItsSelectedClauseAsAUserCallback(string family, string user)
    {
        var (fam, _) = await AllRoutesAsync(LawDefinitions + family);
        var (usr, _) = await AllRoutesAsync(LawDefinitions + user);
        Assert.Equal(usr.Semantic, fam.Semantic);
        Assert.Equal(usr.Errors.Select(WithoutSpan), fam.Errors.Select(WithoutSpan));
        if (usr.Kind == "err")
        {
            Assert.Equal(Innermost(GenericError(LawDefinitions + user)) with { Span = null },
                Innermost(GenericError(LawDefinitions + family)) with { Span = null });
        }
    }

    // ── Helpers ──────────────────────────────────────────────────────────────────────────────────

    internal sealed record Budget(long Steps, long Checkpoints, int PeakDepth, long MaterializedItems, long MaterializedStringChars);

    /// <summary>
    /// One route's outcome: kind (<c>ok</c>, <c>err</c>, <c>parse</c>, <c>none</c>, <c>cancelled</c>), the
    /// neutral value with the program's emitted count, every error as <c>Code: message @ span</c>, every
    /// error's cause (<c>Code/innermost kind</c>), and the host-call log.
    /// </summary>
    internal sealed record Observation(string Kind, string? Value, int? Count, IReadOnlyList<string> Errors, IReadOnlyList<string> Causes, IReadOnlyList<string> HostCalls)
    {
        public bool Equals(Observation? other)
            => other is not null && Kind == other.Kind && Value == other.Value && Count == other.Count
                && Errors.SequenceEqual(other.Errors) && Causes.SequenceEqual(other.Causes) && HostCalls.SequenceEqual(other.HostCalls);

        public override int GetHashCode() => HashCode.Combine(Kind, Value, Count);

        /// <summary>The layer two DIFFERENT programs are compared at: the value, or each error's code and
        /// innermost kind, and the host log.</summary>
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

    private static async Task<(Observation Observation, Budget? Budget)> ObserveAsync(SixRouteAgreement.Route route, string source, long? seed)
    {
        var log = new HostLog();
        var operations = Operations(log, route is SixRouteAgreement.Route.EngineAsyncTwin or SixRouteAgreement.Route.ForcedTwin);
        var options = new RunOptions
        {
            HostOperations = operations,
            RandomSeed = seed,
            EvaluationCancellationToken = log.Cancellation.Token,
        };
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
                return (new Observation("parse", null, null, [.. parsed.Diagnostics.Select(static d => d.Message)], [], [.. log.Calls]), null);

            var program = new Expr.AlgorithmExpr(parsed.Root);
            var (result, budget) = route switch
            {
                SixRouteAgreement.Route.Generic => Evaluator.RunCountedObserved(program, enableOptimizations: false,
                    hostOperations: operations, randomSeed: seed, cancellationToken: log.Cancellation.Token),
                SixRouteAgreement.Route.Optimized => Evaluator.RunCountedObserved(program, enableOptimizations: true,
                    hostOperations: operations, randomSeed: seed, cancellationToken: log.Cancellation.Token),
                SixRouteAgreement.Route.ForcedTwin => await Evaluator.RunCountedObservedAsync(program,
                    zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                    hostOperations: operations, randomSeed: seed, cancellationToken: log.Cancellation.Token),
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
    /// Runs <paramref name="source"/> on every route; requires every route to agree with the synchronous engine
    /// and the three evaluator routes to report identical budget counters. Returns the oracle and the counters.
    /// </summary>
    private static async Task<(Observation Observation, Budget Budget)> AllRoutesAsync(string source, long? seed = null)
    {
        var (oracle, _) = await ObserveAsync(SixRouteAgreement.Route.EngineSync, source, seed);
        Assert.True(oracle.Kind is not ("parse" or "none"), $"source must parse cleanly and have output: {oracle}\nsource:\n{source}");
        Budget? counters = null;
        foreach (var route in SixRouteAgreement.Routes.Skip(1))
        {
            var (observation, budget) = await ObserveAsync(route, source, seed);
            Assert.True(oracle.Equals(observation), $"{route}: expected {oracle}, got {observation}\nsource:\n{source}");
            if (budget is null)
                continue;
            if (counters is null)
                counters = budget;
            else
                Assert.True(counters == budget, $"{route}: budget {budget} differs from {counters}\nsource:\n{source}");
        }

        return (oracle, counters ?? new Budget(0, 0, 0, 0, 0));
    }

    private sealed record Run(string Value, Budget Budget, LoopOptimizationDiagnosticsSnapshot Loops, SequencePipelineDiagnosticsSnapshot Sequences);

    /// <summary>The generic or optimized evaluator alone, with its optimizer diagnostics.</summary>
    private static Run Observe(string source, bool optimize)
    {
        var log = new HostLog();
        var operations = Operations(log, suspending: false);
        var program = new Expr.AlgorithmExpr(ParseValid(source, operations));
        var loops = new LoopOptimizationDiagnostics();
        var sequences = new SequencePipelineDiagnostics();
        var (result, budget) = Evaluator.RunCountedObserved(program, enableOptimizations: optimize, loopDiagnostics: loops,
            sequenceDiagnostics: sequences, hostOperations: operations);
        return new Run(result.IsOk ? SixRouteAgreement.Neutral(result.Value.Value) : "err " + result.Error.Code,
            new Budget(budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth, budget.MaterializedItems, budget.MaterializedStringChars),
            loops.GetSnapshot(), sequences.GetSnapshot());
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

    private static string WithoutSpan(string described)
        => described[..described.LastIndexOf(" @ ", StringComparison.Ordinal)];

    private static string Cause(KatLangError error)
        => $"{error.Code}/{(error.Source is EvalError evalError ? Innermost(evalError).GetType().Name : "front-end")}";

    private static EvalError GenericError(string source)
    {
        var log = new HostLog();
        var operations = Operations(log, suspending: false);
        var program = new Expr.AlgorithmExpr(ParseValid(source, operations));
        var (result, _) = Evaluator.RunCountedObserved(program, enableOptimizations: false, hostOperations: operations);
        Assert.True(result.IsError, source);
        return result.Error;
    }

    /// <summary>A source the front end accepts, parsed with the host operations its names resolve to.</summary>
    private static Algorithm.User ParseValid(string source, HostOperations operations)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return parsed.Root;
    }

    private static string[] Frames(EvalError error)
    {
        var frames = new List<string>();
        while (error is EvalError.WithContext context)
        {
            frames.Add(context.ErrorContext.ToString() ?? "");
            error = context.Inner;
        }

        return [.. frames];
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }
}
