using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

/// <summary>
/// D1 (2026-10-09) and Q-25 (resolved October 2026, Option B): A CLAUSE-FAMILY CALLBACK RETURNS ITS ORDINARY
/// CALL RESULT, EXACTLY LIKE A USER ALGORITHM. HO-03: a <c>map</c> transform and a <c>reduce</c> step return the
/// result of an ordinary call — the ONE value the call boundary delivers (VAL-06): several written rows arrive as
/// one sequence value, <c>()</c> and <c>[]</c> are ordinary values, and nothing is spread; <c>map</c> stores it as
/// one element and <c>reduce</c> passes it whole as the next accumulator. A <c>filter</c> predicate's value must
/// be a Boolean. PAT-11: a clause family is an ordinary callable, so its callback result is its ordinary call
/// result, exactly like a user algorithm's (D1 first aligned the C# family callback path with the user path;
/// since Q-25 both use the ordinary call boundary in <c>EvalNeedCallbackBody</c>, like Lean's
/// <c>evalConditionalCallbackCallCounted</c>). The source observer matrix runs on the six established routes,
/// requiring the same value, emitted count, errors (code, message, span) and host-call log and identical budget
/// counters on the three evaluator routes. The optimizer instrumentation facts compare generic/optimized
/// execution. The boundary companion covers deferred sources on four async configurations and host-built trees
/// on three evaluator configurations; those shapes cannot use the six source routes. Lean:
/// <c>CoreTests/FamilyCallbackCardinality.lean</c>, <c>CoreTests/CallbackResultBoundary.lean</c>; spec cases
/// <c>clause-family-multirow-callback-is-one-value</c>, <c>clause-family-multirow-reduce-step-is-one-value</c>,
/// <c>clause-family-callback-single-value-accepted</c>.
/// </summary>
public sealed partial class ClauseFamilyCallbackCardinalityTests
{
    private const string Fam = "F(0) = 1, 2\nF(n) = n, n\n";
    private const string OneBranch = "F(0) = 1, 2\n";
    private const string Red = "R(e, 0) = e, 0\nR(e, acc) = e, acc\n";
    private const string Pair = "P(0) = (1, 2)\nP(n) = (n, n)\n";
    private const string MapTransformFrame =
        "while evaluating map transform (map passes each iterated collection item as collected; a collecting parameter "
        + "collects supplied values as one exact list and nested sequence and list values stay intact)";
    private const string ReduceStepFrame =
        "while evaluating reduce step (reduce passes each iterated collection item as collected and the accumulator as one "
        + "value; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)";

    // ── 1. The canonical witnesses (D1-A … D1-F): the ordinary call result, equal to the explicit calls ──

    /// <summary>id, the callback program, its value, and the explicit ordinary calls it equals.</summary>
    public static TheoryData<string, string, string, string> CanonicalWitnesses() => new()
    {
        // D1-A: a two-row multi-branch family transform.
        { "D1-A", Fam + "map([0, 3], F)", "L[S[1, 2], S[3, 3]]", Fam + "[F(0), F(3)]" },
        // D1-B: a lone literal clause is a one-branch family.
        { "D1-B", OneBranch + "map([0], F)", "L[S[1, 2]]", OneBranch + "[F(0)]" },
        // D1-C: a two-row family reduce step.
        { "D1-C", Red + "reduce([1], R, 0)", "S[1, 0]", Red + "R(1, 0)" },
        // D1-D, D1-E: the ordinary user-algorithm controls.
        { "D1-D", "D(x) = x, x\nmap([1, 3], D)", "L[S[1, 1], S[3, 3]]", "D(x) = x, x\n[D(1), D(3)]" },
        { "D1-E", "R(e, acc) = e, acc\nreduce([1], R, 0)", "S[1, 0]", "R(e, acc) = e, acc\nR(1, 0)" },
        // D1-F: a family transform returning one `()`.
        { "D1-F", "F(0) = ()\nF(n) = n\nmap([0], F)", "L[S[]]", "F(0) = ()\nF(n) = n\n[F(0)]" },
    };

    [Theory]
    [MemberData(nameof(CanonicalWitnesses))]
    public async Task CanonicalWitness_ReturnsTheOrdinaryCallResult(string id, string source, string value, string explicitCalls)
    {
        var (observation, _) = await AllRoutesAsync(source);
        Assert.True(observation.Kind == "ok", $"{id}: {observation}");
        Assert.Equal((value, 1), (observation.Value, observation.Count));
        Assert.Empty(observation.HostCalls);

        // map(L, F) is [F(L:0), …] and reduce([a], R, i) is R(a, i): the explicit ordinary calls give the same value.
        var (direct, _) = await AllRoutesAsync(explicitCalls);
        Assert.Equal(value, direct.Value);
    }

    // ── 2. Multi-row family callbacks are ONE sequence value, whatever route reaches the family ──────

    /// <summary>label, source, and the value: every route to the family is the family, and the selected
    /// clause's rows arrive as one value at the call boundary.</summary>
    public static TheoryData<string, string, string> MultiRowFamilyCallbacks() => new()
    {
        { "binder clause selected", Fam + "map([3], F)", "L[S[3, 3]]" },
        { "literal clause selected", Fam + "map([0], F)", "L[S[1, 2]]" },
        { "a later item's clause emits two items", "F(0) = [0]*\nF(n) = [n, n]*\nZ = 0\nmap([0, 3], F)", "L[0, S[3, 3]]" },
        { "the literal clause emits two items after a one-item result", "F(0) = [1, 2]*\nF(n) = [n]*\nZ = 0\nmap([3, 0], F)", "L[3, S[1, 2]]" },
        { "three rows", "F(0) = 1, 2, 3\nF(n) = n, n, n\nmap([0], F)", "L[S[1, 2, 3]]" },
        { "structural clauses", "F((a, 0)) = a, 0\nF((a, b)) = a, b\nmap([(1, 2)], F)", "L[S[1, 2]]" },
        { "list-pattern clauses", "F([0]) = 0, 0\nF([x]) = x, x\nmap([[1]], F)", "L[S[1, 1]]" },
        { "Boolean literal clauses", "F(true) = 1, 1\nF(false) = 0, 0\nmap([true], F)", "L[S[1, 1]]" },
        { "a () row beside a value row", "F(0) = (), 1\nF(n) = n, n\nmap([0], F)", "L[S[S[], 1]]" },
        { "a spread row emitting two items", "F(0) = [5, 6]*\nF(n) = n\nmap([0], F)", "L[S[5, 6]]" },
        { "a spread of a bound sequence element", "F((0, 0)) = (0, 0)*\nF(p) = p*\nZ = 0\nmap([5, (1, 2)], F)", "L[5, S[1, 2]]" },
        { "the two-row base clause of a recursive family", "F(0) = [1, 2]*\nF(n) = [F(n - 1)]*\nZ = 0\nmap([0], F)", "L[S[1, 2]]" },
        { "callable alias", Fam + "G = F\nmap([0], G)", "L[S[1, 2]]" },
        { "alias chain", Fam + "G = F\nH = G\nmap([0], H)", "L[S[1, 2]]" },
        { "forwarded through a parameter", Fam + "Apply(f, xs) = map(xs, f)\nApply(F, [0])", "L[S[1, 2]]" },
        { "lifted formula", Fam + "K = map(xs, F)\nK([0])", "L[S[1, 2]]" },
        { "qualified member", "Lib = {\n  public F(0) = 1, 2\n  public F(n) = n, n\n}\nmap([0], Lib.F)", "L[S[1, 2]]" },
        { "opened member", "open Lib\nLib = {\n  public F(0) = 1, 2\n  public F(n) = n, n\n}\nmap([0], F)", "L[S[1, 2]]" },
        { "dot call", Fam + "[0, 3].map(F)", "L[S[1, 2], S[3, 3]]" },
        { "spread dot receiver", Fam + "[[0]]*.map(F)", "L[S[1, 2]]" },
        { "nested map", Fam + "map([[0]], { map(x, F) })", "L[L[S[1, 2]]]" },
        { "after filter", Fam + "map(filter([0, 3], { x > 0 }), F)", "L[S[3, 3]]" },
        { "inside a loop step", Fam + "Step(xs) = map(xs, F)\nrepeat(Step, 1, [0])", "L[S[1, 2]]" },
        { "reduce, binder clause selected", Red + "reduce([1], R, 5)", "S[1, 5]" },
        { "reduce, one-branch family", "R(e, 0) = e, 0\nreduce([1], R, 0)", "S[1, 0]" },
        { "reduce, the second step", "R(e, 0) = [e + 1]*\nR(e, acc) = [e, acc]*\nZ = 0\nreduce([1, 2], R, 0)", "S[2, 2]" },
        { "reduce, forwarded", Red + "Fold(r, xs) = reduce(xs, r, 0)\nFold(R, [1])", "S[1, 0]" },
        { "reduce, dot call", Red + "[1].reduce(R, 0)", "S[1, 0]" },
        { "reduce, forwarded dot call", Red + "Fold(r, xs) = xs.reduce(r, 0)\nFold(R, [1])", "S[1, 0]" },
    };

    [Theory]
    [MemberData(nameof(MultiRowFamilyCallbacks))]
    public async Task MultiRowFamilyCallback_IsOneSequenceValue(string label, string source, string expected)
    {
        var (observation, _) = await AllRoutesAsync(source);
        Assert.True(observation.Kind == "ok", $"{label}: {observation}");
        Assert.Equal((expected, 1), (observation.Value, observation.Count));
    }

    /// <summary>
    /// An error raised INSIDE a multi-row callback is the ordinary call's error, reported under the call frames of
    /// the written callback use and the callback operation's own frame (the frames the former rejection used), and
    /// the family reports it exactly as its user twin does: family source, user twin, and the family's message.
    /// </summary>
    public static TheoryData<string, string, string> FailureFrames() => new()
    {
        { "F(0) = 1, 1 / 0\nF(n) = n, n\n[0, 3].map(F)", "U(x) = 1, 1 / 0\n[0, 3].map(U)",
            $"DivisionByZero: while evaluating dotCall .map of [0, 3]: {MapTransformFrame}: Division by zero @ [1:11, 1:16)" },
        { "F(0) = 1, 1 / 0\nF(n) = n, n\nApply(f, xs) = map(xs, f)\nApply(F, [0])", "U(x) = 1, 1 / 0\nApply(f, xs) = map(xs, f)\nApply(U, [0])",
            $"DivisionByZero: while evaluating call to Apply: while evaluating call to map: {MapTransformFrame}: Division by zero @ [1:11, 1:16)" },
        { "R(e, 0) = e, e / 0\nR(e, acc) = e, acc\nFold(r, xs) = xs.reduce(r, 0)\nFold(R, [1])", "Ru(e, acc) = e, e / 0\nFold(r, xs) = xs.reduce(r, 0)\nFold(Ru, [1])",
            $"DivisionByZero: while evaluating call to Fold: while evaluating dotCall .reduce of xs: {ReduceStepFrame}: Division by zero @ [1:14, 1:19)" },
        { "F(0) = 1, 1 / 0\nF(n) = n, n\nmap([[0]], { map(x, F) })", "U(x) = 1, 1 / 0\nmap([[0]], { map(x, U) })",
            $"DivisionByZero: while evaluating call to map: {MapTransformFrame}: while evaluating call to map: {MapTransformFrame}: Division by zero @ [1:11, 1:16)" },
    };

    [Theory]
    [MemberData(nameof(FailureFrames))]
    public async Task FailureInsideAMultiRowCallback_IsTheOrdinaryCallsError(string family, string user, string expected)
    {
        var (fam, _) = await AllRoutesAsync(family);
        Assert.Equal(expected, Assert.Single(fam.Errors));
        Assert.Empty(fam.HostCalls);
        var (usr, _) = await AllRoutesAsync(user);
        Assert.Equal(WithoutSpan(expected), WithoutSpan(Assert.Single(usr.Errors)));
        Assert.IsType<EvalError.DivByZero>(Innermost(GenericError(family)));
    }

    // ── 3. One value is one callback result, however many elements it holds ───────────────────────

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
    public async Task SeveralRows_AndOneSequence_AreTheSameCallbackResult()
    {
        // As ordinary calls, a two-row clause and a one-row clause holding the pair are the same value ...
        var (direct, _) = await AllRoutesAsync("F(0) = 1, 2\nP(0) = (1, 2)\nF(0) == P(0), F(0), P(0)");
        Assert.Equal("S[true, S[1, 2], S[1, 2]]", direct.Value);

        // ... and as callbacks too: the callback result is the ordinary call result, never the written row count.
        var (pair, _) = await AllRoutesAsync("P(0) = (1, 2)\nmap([0], P), reduce([1], { (e, a) }, 0)");
        Assert.Equal("S[L[S[1, 2]], S[1, 0]]", pair.Value);
        var (rows, _) = await AllRoutesAsync("F(0) = 1, 2\nmap([0], F), reduce([1], { e, a }, 0)");
        Assert.Equal(pair.Value, rows.Value);
    }

    // ── 4. Empty callback results are ordinary values ──────────────────────────────────────────────

    /// <summary>label, source, and the value. A reduce whose result is <c>()</c> is shown inside a list literal,
    /// so the observed value names the empty element explicitly.</summary>
    public static TheoryData<string, string, string> EmptyCallbackResults() => new()
    {
        { "one () row (D1-F)", "F(0) = ()\nF(n) = n\nmap([0], F)", "L[S[]]" },
        { "one () row in every clause", "F(0) = ()\nF(n) = ()\nmap([0, 3], F)", "L[S[], S[]]" },
        { "zero rows: a spread of []", "F(0) = []*\nF(n) = n\nmap([0], F)", "L[S[]]" },
        { "zero rows: a spread of ()", "F(0) = ()*\nF(n) = n\nmap([0], F)", "L[S[]]" },
        { "reduce, one () row", "R(e, 0) = ()\nR(e, acc) = acc\n[reduce([1], R, 0)]", "L[S[]]" },
        { "reduce, zero rows", "R(e, 0) = []*\nR(e, acc) = acc\n[reduce([1], R, 0)]", "L[S[]]" },
        { "reduce, () is the next accumulator", "R(e, 0) = ()\nR(e, acc) = e\nreduce([1, 2], R, 0)", "2" },
        { "user identity of a () element", "Id(x) = x\nmap([(), 1], Id)", "L[S[], 1]" },
        { "one [] is one value", "F(0) = []\nmap([0], F)", "L[L[]]" },
        { "map over [] never invokes", Fam + "map([], F)", "L[]" },
        { "reduce over [] returns the initial value", Red + "reduce([], R, 7)", "7" },
    };

    [Theory]
    [MemberData(nameof(EmptyCallbackResults))]
    public async Task EmptyCallbackResult_IsAnOrdinaryValue(string label, string source, string expected)
    {
        var (observation, _) = await AllRoutesAsync(source);
        Assert.True(observation.Kind == "ok", $"{label}: {observation}");
        Assert.Equal((expected, 1), (observation.Value, observation.Count));
    }

    // ── 5. The ordinary call and the callback return the same one value ─────────────────────────────

    [Theory]
    [InlineData(Fam, "0", "S[1, 2]")]
    [InlineData(Fam, "3", "S[3, 3]")]
    [InlineData(OneBranch, "0", "S[1, 2]")]
    public async Task OrdinaryCall_AndCallback_ReturnTheSameOneValue(string definitions, string argument, string value)
    {
        // The ordinary call crosses the value boundary: one sequence value, emitted count 1 ...
        var (direct, _) = await AllRoutesAsync(definitions + $"F({argument})");
        Assert.Equal(("ok", value, 1), (direct.Kind, direct.Value, direct.Count));

        // ... one list element, one collected argument, a value of two elements ...
        var (consumers, _) = await AllRoutesAsync(definitions + $"Coll(*xs) = xs\n[F({argument})], Coll(F({argument})), F({argument}).count");
        Assert.Equal($"S[L[{value}], L[{value}], 2]", consumers.Value);

        // ... and the same one value as a map transform, as the η-block of the call, and as the η-block that spreads
        // the call's value into two rows, which the call boundary captures again (HO-03).
        foreach (var callback in new[] { "F", "{ F(x) }", "{ F(x)* }" })
        {
            var (mapped, _) = await AllRoutesAsync(definitions + $"map([{argument}], {callback})");
            Assert.Equal(("ok", $"L[{value}]", 1), (mapped.Kind, mapped.Value, mapped.Count));
        }
    }

    [Fact]
    public async Task OrdinaryReduceStepCall_AndReduceStep_ReturnTheSameOneValue()
    {
        var (direct, _) = await AllRoutesAsync(Red + "R(1, 0), R(2, 5)");
        Assert.Equal(("ok", "S[S[1, 0], S[2, 5]]", 2), (direct.Kind, direct.Value, direct.Count));
        var (reduced, _) = await AllRoutesAsync(Red + "reduce([1], R, 0), reduce([1, 2], R, 0) == R(2, R(1, 0))");
        Assert.Equal(("ok", "S[S[1, 0], true]", 2), (reduced.Kind, reduced.Value, reduced.Count));
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

        // The state protocol's own cardinality: the step's two rows were two state slots.
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith(expected[4..] + ": ", error, StringComparison.Ordinal);
    }

    [Fact]
    public void PlannedLoop_RunsAFamilyMapCallbackAsTheOrdinaryCall()
    {
        foreach (var (source, value) in new[]
        {
            (Fam + "Step(xs) = map(xs, F)\nrepeat(Step, 1, [0])", "L[S[1, 2]]"),
            (Pair + "Step(xs) = map(xs, P)\nrepeat(Step, 1, [0, 3])", "L[S[1, 2], S[3, 3]]"),
        })
        {
            var optimized = Observe(source, optimize: true);
            Assert.Equal(value, optimized.Value);
            Assert.True(optimized.Loops.OptimizedLoopHits > 0, "the optimized route must plan the loop");
            Assert.Equal(Observe(source, optimize: false).Budget, optimized.Budget);
        }
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
    public async Task Map_InvokesItemsInOrder_StoringEachResultAsOneElement()
    {
        var (observation, _) = await AllRoutesAsync("F(0) = [trace(0)]*\nF(n) = [trace(n), n]*\nZ = 0\nmap([0, 1, 2], F)");
        Assert.Equal(("ok", "L[0, S[1, 1], S[2, 2]]"), (observation.Kind, observation.Value));
        Assert.Equal(["trace(0)", "trace(1)", "trace(2)"], observation.HostCalls);
    }

    [Fact]
    public async Task Reduce_ThreadsEachStepResultWhole()
    {
        // Step 2's two rows are the one accumulator (2, 1); step 3 receives it whole, fails the literal clause, and
        // its own rows nest it: (3, (2, 1)).
        var (observation, _) = await AllRoutesAsync("R(e, 0) = [trace(e)]*\nR(e, acc) = [trace(e), acc]*\nZ = 0\nreduce([1, 2, 3], R, 0)");
        Assert.Equal(("ok", "S[3, S[2, 1]]"), (observation.Kind, observation.Value));
        Assert.Equal(["trace(1)", "trace(2)", "trace(3)"], observation.HostCalls);
    }

    [Fact]
    public async Task MultiRowCallback_RunsItsWholeBodyExactlyOnce()
    {
        // The callback result is the ordinary call's: every row of the selected clause runs once, in order.
        var (observation, _) = await AllRoutesAsync("F(0) = tick(), tick()\nF(n) = n, n\nmap([0], F)");
        Assert.Equal(("ok", "L[S[1, 2]]"), (observation.Kind, observation.Value));
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

        // A multi-row clause draws its rows in order, exactly as the explicit calls do.
        var (rows, _) = await AllRoutesAsync("G(0) = random(0, 1), random(0, 1)\nG(n) = n, n\nmap([0], G), random(0, 1)", seed);
        var (calls, _) = await AllRoutesAsync("G(0) = random(0, 1), random(0, 1)\nG(n) = n, n\n[G(0)], random(0, 1)", seed);
        Assert.Equal("ok", rows.Kind);
        Assert.Equal(calls.Value, rows.Value);
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

    // ── 9. The law: a family callback returns exactly what its selected clause returns as a user callback ──
    //       (Lean `fcFamilyCallbackEqualsItsSelectedClause`)

    private const string LawDefinitions =
        Fam + Red + Pair
        + "One(0) = 1, 2\nE(0) = ()\nE(n) = n\nZ0(0) = []*\nZ0(n) = n\nBoth(0) = true, true\nBoth(n) = false, false\n"
        + "U0(x) = 1, 2\nD(x) = x, x\nUp0(x) = (1, 2)\nUp(n) = (n, n)\nUe(x) = ()\nUz(x) = { []* }\nRu(e, acc) = e, acc\nQ(x) = true, true\n";

    public static TheoryData<string, string> SelectedClauseLawCases() => new()
    {
        { "map([0], F)", "map([0], U0)" },
        { "map([3], F)", "map([3], D)" },
        { "map([0], One)", "map([0], U0)" },
        { "map([0], P)", "map([0], Up0)" },
        { "map([3], P)", "map([3], Up)" },
        { "map([0], E)", "map([0], Ue)" },
        { "map([0], Z0)", "map([0], Uz)" },
        { "reduce([1], R, 0)", "reduce([1], Ru, 0)" },
        { "reduce([1], R, 5)", "reduce([1], Ru, 5)" },
        { "reduce([1, 2], R, 0)", "reduce([1, 2], Ru, 0)" },
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
