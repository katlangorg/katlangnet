using KatLang.Evaluation.Caching;
using KatLang.Evaluation;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// HO-03 — Q-25 RESOLVED BY OWNER DECISION (October 2026, Option B): A <c>map</c> TRANSFORM OR <c>reduce</c> STEP
/// RETURNS THE ORDINARY RESULT OF CALLING ITS CALLBACK. Each successful invocation delivers the ONE value the
/// ordinary call-result boundary defines (VAL-06): several written rows arrive as one sequence value, <c>()</c>
/// and <c>[]</c> are ordinary values, <c>map</c> stores the result whole as ONE list element and <c>reduce</c>
/// passes it whole as the next accumulator; nothing is spread, and no cardinality or non-empty restriction is
/// added. For pure, deterministic, total computations, <c>map(L, F)</c> is <c>[F(L:0), F(L:1), …]</c> and
/// <c>reduce([a, b], R, i)</c> is <c>R(b, R(a, i))</c> in result value. Map demands its collection; sequential reduction demands its initial
/// value and every step; nested Model-C calls retain their ordinary demand order. Failures of the invocation
/// propagate unchanged (an output-less algorithm is still
/// <c>MissingOutput</c>, VAL-05); <c>filter</c> keeps its Boolean contract and loop steps their row protocol.
/// <para>Every program runs on the six established routes (synchronous engine, asynchronous engine, asynchronous
/// engine with genuinely suspending host operations, the generic and optimized evaluators, and the forced async
/// twin), which must agree on the value, emitted count, errors (code, message, span) and host-call log; the three
/// evaluator routes must report identical budget counters. Section 1 is the Q-25 investigation's frozen 92-program
/// matrix (<c>artifacts/validation/q25-callback-result-investigation/</c>, Option B predictions); the other
/// sections state the laws themselves. Lean: <c>CoreTests/CallbackResultBoundary.lean</c>; spec cases
/// <c>callback-result-is-the-ordinary-call-result</c>, <c>map-identity-preserves-empty-elements</c>,
/// <c>reduce-accumulator-may-be-empty</c>.</para>
/// </summary>
public sealed class CallbackResultBoundaryTests
{
    // ── 1. The investigation's frozen matrix (68 programs + 24 adversarial probes), Option B ───────────────

    /// <summary>id, source, expected outcome (<c>ok VALUE</c> or <c>err CODE</c>), expected host-call log.</summary>
    public static TheoryData<string, string, string, string> InvestigationMatrix() => new()
    {
        { "E1-direct-rows", "D(x) = x, x\nmap([1], D)", "ok L[S[1, 1]]", "" },
        { "E1-call-wrapper", "D(x) = x, x\nG(x) = D(x)\nmap([1], G)", "ok L[S[1, 1]]", "" },
        { "E1-capture-row", "H(x) = (x, x)\nmap([1], H)", "ok L[S[1, 1]]", "" },
        { "E1-direct-call-equality", "D(x) = x, x\nG(x) = D(x)\nH(x) = (x, x)\n[D(1) == G(1), G(1) == H(1)]", "ok L[true, true]", "" },
        { "E1-map-unfolding-law", "D(x) = x, x\nmap([1, 2], D) == [D(1), D(2)]", "ok true", "" },
        { "E1-spread-wrapper", "D(x) = x, x\nS(x) = { D(x)* }\nmap([1], S)", "ok L[S[1, 1]]", "" },
        { "E1-no-implicit-spread-count", "D(x) = x, x\nmap([1, 2, 3], D).count", "ok 3", "" },
        { "E1-brace-two-rows", "map([1, 2], {x, x * 10})", "ok L[S[1, 10], S[2, 20]]", "" },
        { "E1-brace-list-row", "map([1, 2], {[x, x]})", "ok L[L[1, 1], L[2, 2]]", "" },
        { "E2-identity-with-empties", "Id(x) = x\nmap([(), 1, [], 2], Id)", "ok L[S[], 1, L[], 2]", "" },
        { "E2-identity-no-empty-seq", "Id(x) = x\nmap([1, [], 2], Id)", "ok L[1, L[], 2]", "" },
        { "E2-filter-keeps-empty", "K(x) = true\nfilter([(), 1], K)", "ok L[S[], 1]", "" },
        { "E2-map-after-filter", "K(x) = true\nId(x) = x\nmap(filter([(), 1], K), Id)", "ok L[S[], 1]", "" },
        { "E2-identity-law", "Id(x) = x\nL = [(), [], 1]\nmap(L, Id) == L", "ok true", "" },
        { "E3-direct-empty-seq", "E(x) = ()\nmap([1], E)", "ok L[S[]]", "" },
        { "E3-direct-empty-list", "E(x) = []\nmap([1], E)", "ok L[L[]]", "" },
        { "E3-empty-through-call", "E(x) = ()\nG(x) = E(x)\nmap([1], G)", "ok L[S[]]", "" },
        { "E3-sequence-of-empties", "E(x) = ((), ())\nmap([1], E)", "ok L[S[S[], S[]]]", "" },
        { "E3-missing-output", "Lib = { public V = 1 }\nF(x) = Lib\nmap([1], F)", "err MissingOutput", "" },
        { "E3-conditional-empty", "F(x) = if(x > 1, x, ())\nmap([1, 2], F)", "ok L[S[], 2]", "" },
        { "E3-zero-rows-empty-spread", "Z(x) = { ()* }\nmap([1], Z)", "ok L[S[]]", "" },
        { "E3-zero-rows-empty-list-spread", "Z(x) = { []* }\nmap([1], Z)", "ok L[S[]]", "" },
        { "E3-one-row-spread", "O(x) = { [x]* }\nmap([1, 2], O)", "ok L[1, 2]", "" },
        { "E3-two-row-spread", "T(x) = { [x, x]* }\nmap([1], T)", "ok L[S[1, 1]]", "" },
        { "E4-two-row-reducer", "R(x, acc) = x, acc\nreduce([1, 2], R, 0)", "ok S[2, S[1, 0]]", "" },
        { "E4-reduce-unfolding-law", "R(x, acc) = x, acc\nreduce([1, 2], R, 0) == R(2, R(1, 0))", "ok true", "" },
        { "E4-flat-accumulation-rows", "R(x, acc) = acc*, x\nreduce([1, 2, 3], R, ())", "ok S[1, 2, 3]", "" },
        { "E4-flat-accumulation-capture", "R(x, acc) = (acc*, x)\nreduce([1, 2, 3], R, ())", "ok S[1, 2, 3]", "" },
        { "E5-step-returns-empty-seq", "R(x, acc) = ()\n[reduce([1, 2], R, 0)]", "ok L[S[]]", "" },
        { "E5-step-returns-empty-list", "R(x, acc) = []\nreduce([1], R, 0)", "ok L[]", "" },
        { "E5-step-returns-sequence-capture", "R(x, acc) = (x, acc)\nreduce([1, 2], R, 0)", "ok S[2, S[1, 0]]", "" },
        { "E5-step-returns-nested-list", "R(x, acc) = [x, acc]\nreduce([1, 2], R, [])", "ok L[2, L[1, L[]]]", "" },
        { "E5-identity-reducer-empty-initial", "R(x, acc) = acc\n[reduce([1], R, ())]", "ok L[S[]]", "" },
        { "E5-identity-reducer-empty-collection", "R(x, acc) = acc\n[reduce([], R, ())]", "ok L[S[]]", "" },
        { "E5-callable-accumulator", "Inc(q) = q + 1\nR(x, acc) = (Inc, x)\nreduce([1], R, 0)", "err ArityMismatch", "" },
        { "E5-empty-initial-flows-in", "R(x, acc) = (acc, x)\nreduce([1], R, ())", "ok S[S[], 1]", "" },
        { "E5-transient-empty-accumulator", "R(x, acc) = if(x == 1, (), x)\nreduce([1, 2], R, 0)", "ok 2", "" },
        { "E6-family-scalar", "F(0) = 10\nF(n) = n\nmap([0, 2], F)", "ok L[10, 2]", "" },
        { "E6-family-list", "F(0) = []\nF(n) = [n]\nmap([0, 2], F)", "ok L[L[], L[2]]", "" },
        { "E6-family-empty-seq", "F(0) = ()\nF(n) = n\nmap([0, 2], F)", "ok L[S[], 2]", "" },
        { "E6-user-empty-seq", "U(n) = if(n == 0, (), n)\nmap([0, 2], U)", "ok L[S[], 2]", "" },
        { "E6-family-two-rows", "F(0) = 0, 0\nF(n) = n, n\nmap([0, 2], F)", "ok L[S[0, 0], S[2, 2]]", "" },
        { "E6-user-two-rows", "U(n) = n, n\nmap([0, 2], U)", "ok L[S[0, 0], S[2, 2]]", "" },
        { "E6-family-one-sequence", "F(0) = (0, 0)\nF(n) = (n, n)\nmap([0, 2], F)", "ok L[S[0, 0], S[2, 2]]", "" },
        { "E6-family-reducer-two-rows", "R(e, 0) = e, 0\nR(e, acc) = e, acc\nreduce([1], R, 0)", "ok S[1, 0]", "" },
        { "E6-family-zero-rows", "F(0) = []*\nF(n) = n\nmap([0, 2], F)", "ok L[S[], 2]", "" },
        { "E7-first-error-order", "F(x) = x, 10 / (x - 2)\nmap([1, 2], F)", "err DivisionByZero", "" },
        { "E7-host-effects-two-rows", "F(x) = trace(x), trace(x * 10)\nmap([1, 2], F)", "ok L[S[1, 10], S[2, 20]]", "trace(1) | trace(10) | trace(2) | trace(20)" },
        { "E7-host-effects-spread", "F(x) = { [trace(x), x]* }\nmap([1, 2], F)", "ok L[S[1, 1], S[2, 2]]", "trace(1) | trace(2)" },
        { "E7-unused-callback-empty-collection", "D(x) = x, x\nmap([], D)", "ok L[]", "" },
        { "E7-fresh-effect-order", "F(x) = tick(), x\nmap([5, 6], F)", "ok L[S[1, 5], S[2, 6]]", "tick#1 | tick#2" },
        { "P8-alias", "D(x) = x, x\nA = D\nmap([1], A)", "ok L[S[1, 1]]", "" },
        { "P8-parameter-forwarded", "D(x) = x, x\nApply(f, L) = map(L, f)\nApply(D, [1])", "ok L[S[1, 1]]", "" },
        { "P8-collector-forwarded", "D(x) = x, x\nFwd(L, *fs) = map(L, fs*)\nFwd([1], D)", "ok L[S[1, 1]]", "" },
        { "P8-builtin-returns-empty-seq", "map([[()], [1]], first)", "ok L[S[], 1]", "" },
        { "P8-math-callback", "map([-1, 2], abs)", "ok L[1, 2]", "" },
        { "P8-host-callback-empty-seq", "map([()], trace)", "ok L[S[]]", "trace(S[])" },
        { "LOOP-two-row-step", "Step(x) = x, x\nrepeat(Step, 1, 5)", "ok S[5, 5]", "" },
        { "LOOP-empty-seq-step", "Step(x) = ()\n[repeat(Step, 1, 5)]", "ok L[S[]]", "" },
        { "FILTER-two-row-predicate", "P(x) = x > 1, x < 5\nfilter([2], P)", "err TypeMismatch", "" },
        { "REAL-accidental-row-map", "Net(x) = {\n  x * 2\n  - 1\n}\nmap([1, 2], Net)", "ok L[S[2, -1], S[4, -1]]", "" },
        { "REAL-accidental-row-sum", "Net(x) = {\n  x * 2\n  - 1\n}\nsum(map([1, 2], Net))", "err TypeMismatch", "" },
        { "REAL-accidental-row-direct", "Net(x) = {\n  x * 2\n  - 1\n}\nNet(3) + 1", "err TypeMismatch", "" },
        { "REAL-running-pair-reduce", "Acc(x, (s, n)) = s + x, n + 1\nreduce([4, 6], Acc, (0, 0))", "ok S[10, 2]", "" },
        { "REAL-optional-results-map", "Recip(x) = if(x == 0, (), 1 / x)\nmap([0, 2], Recip)", "ok L[S[], 0.5]", "" },
        { "REAL-optional-results-filter", "Recip(x) = if(x == 0, (), 1 / x)\nNotEmpty(v) = v != ()\nfilter(map([0, 2, 4], Recip), NotEmpty)", "ok L[0.5, 0.25]", "" },
        { "REAL-tutorial-rectangle-map", "Rect((w, h)) = w * h, 2 * (w + h)\nSizes = [(3, 4), (5, 6)]\nSizes.map(Rect)", "ok L[S[12, 14], S[30, 22]]", "" },
        { "REAL-tutorial-rectangle-calls", "Rect((w, h)) = w * h, 2 * (w + h)\n[Rect((3, 4)), Rect((5, 6))]", "ok L[S[12, 14], S[30, 22]]", "" },
        { "ADV-defend-A-AD1-continuation-row-silent-wrong", "Net(q) = {\n  q * 10\n  - 4\n}\nM = map([1, 2, 3], Net)\n[contains(M, 26), avg(atoms(M))]", "ok L[false, 8]", "" },
        { "ADV-defend-A-AD2-brace-wrapper-bypasses-guard", "Net(q) = {\n  q * 10\n  - 4\n}\nM = map([1, 2, 3], {Net(n)})\n[contains(M, 26), avg(atoms(M))]", "ok L[false, 8]", "" },
        { "ADV-defend-A-AD3-empty-as-skip-count", "Valid(x) = if(x >= 0, x, ())\ncount(map([3, -1, 4], Valid))", "ok 3", "" },
        { "ADV-defend-A-AD4-running-max-forgot-else", "MaxStep(x, acc) = if(x > acc, x, ())\nBest = reduce([3, 1], MaxStep, 0)\n[Best, Best == 3]", "ok L[S[], false]", "" },
        { "ADV-defend-A-AD5-append-forgot-spread-nests", "Append(x, acc) = acc, x\nR = reduce([1, 2, 3], Append, ())\n[count(R), R]", "ok L[2, S[S[S[S[], 1], 2], 3]]", "" },
        { "ADV-defend-A-AD6-reduce-leftover-row-displaced-error", "Fold(d, acc) = {\n  acc * 10\n  acc * 10 - d\n}\nreduce([1, 2], Fold, 0)", "err TypeMismatch", "" },
        { "ADV-defend-A-AD7-map-equals-one-iteration-repeat", "D(x) = x, x\nE(x) = ()\nZ(x) = { ()* }\n[map([5], D):0 == repeat(D, 1, 5), map([5], E):0 == repeat(E, 1, 5), map([5], Z):0 == repeat(Z, 1, 5)]", "ok L[true, true, true]", "" },
        { "ADV-defend-A-AD8-compat-positive-control-special-routes", "H(x) = (x, x * 10)\nP = [1, 2].map(H)\nStep(n) = n + count(map([n, n], H))\nColl(*xs) = xs\nR(x, acc) = [acc*, x * 2]\n[P:1, repeat(Step, 3, 0), Coll(P*), count(filter(range(1, 4), {last(first(map([k], H))) > 15})), last(P:0).string, reduce([1, 2], R, [])]", "ok L[S[2, 20], 6, L[S[1, 10], S[2, 20]], 3, '10', L[2, 4]]", "" },
        { "ADV-attack-B-ADV-B1-reduce-empty-skip-discards-state", "Keep(x, acc) = if(x < 0, (), (acc*, x))\nreduce([1, 2, -1, 3], Keep, ())", "ok 3", "" },
        { "ADV-attack-B-ADV-B2-accidental-row-never-detected", "Net(x) = {\n  x * 2\n  - 2\n}\n[1, 2, 3].map(Net).filter({v != 0}).count", "ok 3", "" },
        { "ADV-attack-B-ADV-B3-lookup-shape-depends-on-match-count", "Data = [10, 20, 20]\nFind(k) = { filter(Data, {v == k})* }\nmap([10, 20, 30], Find)", "ok L[10, S[20, 20], S[]]", "" },
        { "ADV-attack-B-ADV-B4-reduce-debug-row-displaced-blame", "Total(x, acc) = trace(x), acc + x\nreduce([1, 2, 3], Total, 0)", "err TypeMismatch", "trace(1) | trace(2)" },
        { "ADV-attack-B-ADV-B5-structured-fold-empty-skip-same-code-new-site", "Acc(x, (s, n)) = if(x < 0, (), (s + x, n + 1))\nreduce([4, -1, 6], Acc, (0, 0))", "err ArityMismatch", "" },
        { "ADV-attack-B-ADV-B6-empty-element-fails-in-another-callback", "Opt(x) = if(x > 1, trace(x), ())\nfilter(map([1, 2, 3], Opt), {v > 1})", "err TypeMismatch", "trace(2) | trace(3)" },
        { "ADV-attack-B-ADV-B7-family-empty-branch-then-container", "Lib = { public V = 1 }\nF(0) = { []* }\nF(n) = Lib\nmap([0, 1], F)", "err MissingOutput", "" },
        { "ADV-attack-B-ADV-B8-loop-step-row-is-reduce-returning-empty", "Z(x, acc) = ()\nStep(s) = reduce([s], Z, 0)\n[repeat(Step, 1, 5)]", "ok L[S[]]", "" },
        { "ADV-attack-C-C-split-spread", "map([[1, 2], []], {x*})", "ok L[S[1, 2], S[]]", "" },
        { "ADV-attack-C-C-reduce-concat-order", "Cat(x, acc) = { acc*, x* }\n[reduce([[1, 2], []], Cat, ()), reduce([[], [1, 2]], Cat, ())]", "ok L[S[1, 2], S[1, 2]]", "" },
        { "ADV-attack-C-C-count-empty-seq", "count(map([1, 2, 3], {if(x == 2, (), x)}))", "ok 3", "" },
        { "ADV-attack-C-C-count-empty-list", "count(map([1, 2, 3], {if(x == 2, [], x)}))", "ok 3", "" },
        { "ADV-attack-C-C-sum-empty-seq", "sum(map([5, 0], {if(x == 0, (), x)}))", "err TypeMismatch", "" },
        { "ADV-attack-C-C-sum-empty-list", "sum(map([5, 0], {if(x == 0, [], x)}))", "err TypeMismatch", "" },
        { "ADV-attack-C-C-keep-fold", "Keep(x, acc) = if(x > 0, (acc*, x), acc)\nreduce([-1, 2, 3], Keep, ())", "ok S[2, 3]", "" },
        { "ADV-attack-C-C-map-via-reduce", "E(x) = if(x == 2, (), x)\nSnoc(x, acc) = [acc*, E(x)]\nreduce([1, 2, 3], Snoc, []) == map([1, 2, 3], E)", "ok true", "" },
    };

    [Theory]
    [MemberData(nameof(InvestigationMatrix))]
    public async Task InvestigationMatrix_FollowsTheOrdinaryCallResultLaw(string id, string source, string expected, string hostCalls)
    {
        var (observation, _) = await AllRoutesAsync(source);
        Assert.True(expected == observation.Outcome, $"{id}: expected {expected}, observed {observation}");
        if (observation.Kind == "ok")
            Assert.Equal(1, observation.Count);
        Assert.Equal(hostCalls.Length == 0 ? [] : hostCalls.Split(" | "), observation.HostCalls);
    }

    // 2. Pure deterministic input matrix: map(L, F) matches the result values of the ordinary calls.

    private const string Callees =
        "D(x) = x, x\nG(x) = D(x)\nH(x) = (x, x)\nS(x) = { D(x)* }\nE(x) = ()\nZ(x) = { []* }\nW(x) = [x]\nId(x) = x\n"
        + "F(0) = 1, 2\nF(n) = n, n\nFe(0) = ()\nFe(n) = n\nA = D\n";

    public static TheoryData<string, string> MapCells()
    {
        var data = new TheoryData<string, string>();
        foreach (var callee in new[] { "D", "G", "H", "S", "E", "Z", "W", "Id", "F", "Fe", "A", "count", "first" })
            foreach (var elements in new[] { "1 | 2", "() | 1", "[] | (1, 2)", "[1, 2] | ((), 3)" })
                data.Add(callee, elements);
        return data;
    }

    [Theory]
    [MemberData(nameof(MapCells))]
    public async Task Map_IsTheListOfTheOrdinaryCalls(string callee, string elements)
    {
        var items = elements.Split(" | ");
        var (mapped, _) = await AllRoutesAsync(Callees + $"map([{string.Join(", ", items)}], {callee})");
        var (direct, _) = await AllRoutesAsync(Callees + "[" + string.Join(", ", items.Select(item => $"{callee}({item})")) + "]");
        Assert.Equal(direct.Outcome, mapped.Outcome);
    }

    // 3. Pure, deterministic, total computations: reduce and nested calls have the same result value.

    private const string Reducers =
        "Pair2(x, acc) = x, acc\nSnoc(x, acc) = acc, x\nCap(x, acc) = (acc, x)\nFlat(x, acc) = acc*, x\nKeep(x, acc) = acc\n"
        + "Empty(x, acc) = ()\nLst(x, acc) = [acc, x]\nR(e, 0) = e, 0\nR(e, acc) = e, acc\n";

    public static TheoryData<string, string, string> ReduceCells()
    {
        var data = new TheoryData<string, string, string>();
        foreach (var reducer in new[] { "Pair2", "Snoc", "Cap", "Flat", "Keep", "Empty", "Lst", "R" })
            foreach (var initial in new[] { "0", "()", "[]", "(1, 2)" })
                foreach (var items in new[] { "1 | 2", "() | 3" })
                    data.Add(reducer, initial, items);
        return data;
    }

    [Theory]
    [MemberData(nameof(ReduceCells))]
    public async Task Reduce_IsTheNestedOrdinaryCalls(string reducer, string initial, string items)
    {
        var (first, second) = (items.Split(" | ")[0], items.Split(" | ")[1]);
        // Both sides are wrapped in a list literal, so every outcome is compared as one list element.
        var (reduced, _) = await AllRoutesAsync(Reducers + $"[reduce([{first}, {second}], {reducer}, {initial})]");
        var (direct, _) = await AllRoutesAsync(Reducers + $"[{reducer}({second}, {reducer}({first}, {initial}))]");
        Assert.Equal(direct.Outcome, reduced.Outcome);
    }

    // ── 4. The identity map reproduces every list; every value is a legitimate accumulator ───────────────

    [Theory]
    [InlineData("[]")]
    [InlineData("[()]")]
    [InlineData("[[]]")]
    [InlineData("[(), (), ()]")]
    [InlineData("[1, 'a', true, (), []]")]
    [InlineData("[(1, ()), [(), []], ((), ((), ()))]")]
    [InlineData("[range(1, 3), take([1, 2], 1), first([()])]")]
    [InlineData("filter([(), 1, []], { x == x })")]
    public async Task IdentityMap_ReproducesTheList(string list)
    {
        var (observation, _) = await AllRoutesAsync($"Id(x) = x\nL = {list}\n[map(L, Id) == L, count(map(L, Id)) == count(L), map(L, Id)]");
        var (expected, _) = await AllRoutesAsync($"L = {list}\n[true, true, L]");
        Assert.Equal(expected.Outcome, observation.Outcome);
    }

    [Theory]
    [InlineData("()")]
    [InlineData("[]")]
    [InlineData("0")]
    [InlineData("'s'")]
    [InlineData("false")]
    [InlineData("(1, ())")]
    [InlineData("[(), [1]]")]
    public async Task EveryValue_IsALegitimateAccumulator_AtEveryStep(string value)
    {
        // The value may start the fold, be produced by every step, and end it; the empty fold returns it too.
        var (observation, _) = await AllRoutesAsync(
            $"V = {value}\nStep(x, acc) = V\nKeep(x, acc) = acc\n[reduce([1, 2], Step, 0) == V, reduce([1, 2], Keep, V) == V, reduce([], Keep, V) == V]");
        Assert.Equal("ok L[true, true, true]", observation.Outcome);
    }

    // ── 5. Wrapper, alias and forwarding invariance: every spelling of the same callable maps alike ─────────

    [Theory]
    [InlineData("D(x) = x, x\nmap([1, 2], D)")]
    [InlineData("D(x) = x, x\nG(x) = D(x)\nmap([1, 2], G)")]
    [InlineData("H(x) = (x, x)\nmap([1, 2], H)")]
    [InlineData("D(x) = x, x\nS(x) = { D(x)* }\nmap([1, 2], S)")]
    [InlineData("D(x) = x, x\nA = D\nB = A\nmap([1, 2], B)")]
    [InlineData("map([1, 2], {x, x})")]
    [InlineData("map([1, 2], { (x, x) })")]
    [InlineData("map([1, 2], { [x, x]* })")]
    [InlineData("D(x) = x, x\nmap([1, 2], { D(x) })")]
    [InlineData("D(x) = x, x\nApply(f, xs) = map(xs, f)\nApply(D, [1, 2])")]
    [InlineData("D(x) = x, x\nFwd(xs, *fs) = map(xs, fs*)\nFwd([1, 2], D)")]
    [InlineData("D(x) = x, x\n[1, 2].map(D)")]
    [InlineData("D(x) = x, x\n[[1, 2]]*.map(D)")]
    [InlineData("D(x) = x, x\nLib = { public M(xs) = map(xs, D) }\nLib.M([1, 2])")]
    [InlineData("F(1) = 1, 1\nF(n) = n, n\nmap([1, 2], F)")]
    [InlineData("D(x) = x, x\nStep(xs) = map(xs, D)\nrepeat(Step, 1, [1, 2])")]
    public async Task EverySpellingOfTheSamePairCallable_MapsToTheSamePairs(string source)
    {
        var (observation, _) = await AllRoutesAsync(source);
        Assert.Equal("ok L[S[1, 1], S[2, 2]]", observation.Outcome);
    }

    /// <summary>A clause-family callback returns exactly what its selected clause returns as a user callback.</summary>
    [Theory]
    [InlineData("F(0) = 1, 2\nF(n) = n, n\nmap([0, 3], F)", "F0(x) = 1, 2\nF1(x) = x, x\n[map([0], F0):0, map([3], F1):0]")]
    [InlineData("F(0) = ()\nF(n) = n\nmap([0, 3], F)", "E(x) = ()\nI(x) = x\n[map([0], E):0, map([3], I):0]")]
    [InlineData("F(0) = []*\nF(n) = [n, n]*\nK = 0\nmap([0, 3], F)", "Z(x) = { []* }\nT(x) = { [x, x]* }\n[map([0], Z):0, map([3], T):0]")]
    [InlineData("R(e, 0) = ()\nR(e, acc) = [e, acc]*\nK = 0\n[reduce([1, 2], R, 0)]", "E(e, acc) = ()\nP(e, acc) = e, acc\n[P(2, E(1, 0))]")]
    public async Task FamilyCallback_EqualsItsSelectedClausesAsUserCallbacks(string family, string user)
    {
        var (fam, _) = await AllRoutesAsync(family);
        var (usr, _) = await AllRoutesAsync(user);
        Assert.Equal(usr.Outcome, fam.Outcome);
    }

    // ── 6. No implicit spread; an explicit spread opens exactly one level ───────────────────────────────

    [Theory]
    [InlineData("D(x) = x, x\nmap([1, 2], D).count", "ok 2")]
    [InlineData("D(x) = x, x\n(map([1, 2], D)*)", "ok S[S[1, 1], S[2, 2]]")]
    [InlineData("D(x) = x, x\n[map([1, 2], D):0*]", "ok L[1, 1]")]
    [InlineData("D(x) = x, x\natoms(map([1, 2], D))", "ok L[1, 1, 2, 2]")]
    [InlineData("D(x) = x, x\nColl(*xs) = xs\nColl(map([1], D))", "ok L[L[S[1, 1]]]")]
    [InlineData("D(x) = x, x\nColl(*xs) = xs\nColl(map([1], D)*)", "ok L[S[1, 1]]")]
    [InlineData("R(x, acc) = x, acc\nreduce([1, 2], R, 0).count", "ok 2")]
    [InlineData("R(x, acc) = acc*, x\nreduce([1, 2, 3], R, ())", "ok S[1, 2, 3]")]
    public async Task CallbackResults_AreNeverSpreadImplicitly(string source, string expected)
    {
        var (observation, _) = await AllRoutesAsync(source);
        Assert.Equal(expected, observation.Outcome);
    }

    // ── 7. A reduce result crosses the value boundary: its emitted count is that of its value ────────────────

    [Theory]
    [InlineData("R(x, acc) = acc", "[1]", "()", "S[]", 0)]
    [InlineData("R(x, acc) = ()", "[1, 2]", "0", "S[]", 0)]
    [InlineData("R(x, acc) = acc", "[]", "()", "S[]", 0)]
    [InlineData("R(x, acc) = x, acc", "[1, 2]", "0", "S[2, S[1, 0]]", 1)]
    [InlineData("R(x, acc) = []", "[1]", "0", "L[]", 1)]
    public async Task ReduceResult_IsCountedByItsValue(string step, string items, string initial, string value, int count)
    {
        // A root program re-counts its rows, so the reduce call itself is evaluated as a host-built top-level
        // expression, its step an inline algorithm: the count is the builtin RESULT's own, Result.ValueCount of its
        // value (VAL-06) — 0 exactly for (), whether the fold ran steps or returned its initial value.
        var parsed = Parser.Parse(step + "\nreduce(" + items + ", R, " + initial + ")");
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        var call = Assert.IsType<Expr.Call>(Assert.Single(parsed.Root.Output));
        var arguments = call.Args.ToArray();
        var hostCall = call with { Args = [arguments[0], new Expr.AlgorithmExpr(parsed.Root.Properties.Single().Value), arguments[2]] };
        foreach (var optimize in new[] { false, true })
        {
            var (result, _) = Evaluator.RunCountedObserved(hostCall, enableOptimizations: optimize);
            Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
            Assert.Equal((value, count), (SixRouteAgreement.Neutral(result.Value.Value), result.Value.EmittedCount));
        }

        var (twin, _) = await Evaluator.RunCountedObservedAsync(hostCall, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache());
        Assert.True(twin.IsOk, twin.IsError ? twin.Error.ToString() : "");
        Assert.Equal((value, count), (SixRouteAgreement.Neutral(twin.Value.Value), twin.Value.EmittedCount));
    }

    // ── 8. Failures propagate as the ordinary call's failures ─────────────────────────────────────────────

    [Fact]
    public async Task OutputLessAlgorithm_IsStillMissingOutput_NeverTheEmptyValue()
    {
        // VAL-05: rows that supply zero items have the output (); a container has no output at all.
        var (container, _) = await AllRoutesAsync("Lib = { public V = 1 }\nF(x) = Lib\nmap([1], F)");
        Assert.Equal("err MissingOutput", container.Outcome);
        var (zeroItems, _) = await AllRoutesAsync("Z(x) = { []* }\nmap([1], Z)");
        Assert.Equal("ok L[S[]]", zeroItems.Outcome);
    }

    [Fact]
    public async Task ALaterItemsFailure_IsReportedAfterTheEarlierMultiRowResult()
    {
        // Item 1's two rows are its result; item 2 then divides by zero inside its own second row.
        var (observation, _) = await AllRoutesAsync("F(x) = trace(x), 10 / (x - 2)\nmap([1, 2], F)");
        Assert.Equal(
            "DivisionByZero: while evaluating call to map: while evaluating map transform (map passes each iterated collection item as "
            + "collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay "
            + "intact): Division by zero @ [1:18, 1:30)",
            Assert.Single(observation.Errors));
        Assert.Equal(["trace(1)", "trace(2)"], observation.HostCalls);
    }

    [Fact]
    public async Task AnEmptyAccumulator_FailsOnlyWhereAnOperatorRejectsIt()
    {
        // () is an ordinary accumulator; the operator that receives it reports its own value-kind error (SYN-01).
        var (observation, _) = await AllRoutesAsync("Skip(x, acc) = if(x < 0, (), acc + x)\nreduce([1, -1, 2], Skip, 0)");
        Assert.Equal("err TypeMismatch", observation.Outcome);
        Assert.Contains("+", Assert.Single(observation.Errors), StringComparison.Ordinal);
    }

    [Fact]
    public async Task CallbackArityFailure_KeepsThePlainShape_WhileTheDirectCallIsVariadic()
    {
        // Q-25 changed results only: a callback's arity diagnostic keeps the plain ArityMismatch shape named by its
        // role, while the direct call of the same collecting callee reports the variadic shape (same public code).
        var callback = GenericError("C(a, b, *rest) = a\nmap([1], C)");
        Assert.IsType<EvalError.ArityMismatch>(Innermost(callback));
        var direct = GenericError("C(a, b, *rest) = a\nC(1)");
        Assert.IsType<EvalError.VariadicArityMismatch>(Innermost(direct));
        Assert.Equal(KatLangErrorCode.ArityMismatch, callback.Code);
        Assert.Equal(KatLangErrorCode.ArityMismatch, direct.Code);
    }

    // ── 9. Model-C demand, effects, randomness and limits are unchanged ──────────────────────────────────

    [Fact]
    public async Task Demand_IsUnchanged_UnusedCallbacksRunNothing_InitialIsDemandedOnce()
    {
        var (observation, _) = await AllRoutesAsync(
            "F(x) = trace(x), x\nR(x, acc) = trace(x), acc\n[map([], F), reduce([], R, trace(7)), reduce([1], R, trace(8))]");
        Assert.Equal("ok L[L[], 7, S[1, 8]]", observation.Outcome);
        Assert.Equal(["trace(7)", "trace(8)", "trace(1)"], observation.HostCalls);
    }

    [Fact]
    public async Task EveryRowRunsOnce_InWrittenOrder_ItemByItem()
    {
        var (observation, _) = await AllRoutesAsync("F(x) = tick(), x, tick()\nmap([5, 6], F), tick()");
        Assert.Equal("ok S[L[S[1, 5, 2], S[3, 6, 4]], 5]", observation.Outcome);
        Assert.Equal(["tick#1", "tick#2", "tick#3", "tick#4", "tick#5"], observation.HostCalls);
    }

    [Theory]
    [InlineData(5L)]
    [InlineData(77L)]
    public async Task MultiRowCallbacks_DrawExactlyTheDirectStream(long seed)
    {
        var (mapped, _) = await AllRoutesAsync("G(x) = random(0, 1), random(0, 1)\nmap([1, 2], G), random(0, 1)", seed);
        var (direct, _) = await AllRoutesAsync("G(x) = random(0, 1), random(0, 1)\n[G(1), G(2)], random(0, 1)", seed);
        Assert.Equal("ok", mapped.Kind);
        Assert.Equal(direct.Value, mapped.Value);
    }

    [Fact]
    public async Task ANewlyAcceptedMultiRowCallback_ObservesTheOrdinaryStepBudget()
    {
        const string source = "D(x) = x, x\nmap([1, 2, 3], D)";
        var (unlimited, budget) = await AllRoutesAsync(source);
        Assert.Equal("ok L[S[1, 1], S[2, 2], S[3, 3]]", unlimited.Outcome);

        // A limit never redefines a run that completes: exactly the steps it needs give the same result ...
        var (exact, exactBudget) = await AllRoutesAsync(source, limits: new EvaluationLimits { MaxSteps = budget.Steps });
        Assert.Equal(unlimited.Outcome, exact.Outcome);
        Assert.Equal(budget, exactBudget);

        // ... one step fewer is the terminal step-limit failure, never a partial list.
        var (under, _) = await AllRoutesAsync(source, limits: new EvaluationLimits { MaxSteps = budget.Steps - 1 });
        Assert.Equal("err EvaluationStepLimitExceeded", under.Outcome);
    }

    // Independent Q-25 review: interactions outside the frozen investigation matrix.

    [Theory]
    [InlineData("Z(x, acc) = ()\nStep(s) = reduce([s], Z, 0)\nrepeat(Step, 3, 5)", "ok S[]")]
    [InlineData("Z(x, acc) = ()\nStep(a, b) = trace(a), reduce([b], Z, 0)\nrepeat(Step, 3, 5, 5)", "ok S[5, S[]]")]
    [InlineData("E(x) = ()\nR(x, acc) = map([x], E), acc\nreduce([1, 2], R, ())", "ok S[L[S[]], S[L[S[]], S[]]]")]
    [InlineData("R(x, acc) = ()\nP(x, x) = x\n[P(reduce([1], R, 0), ()), P((), reduce([1], R, 0))]", "ok L[S[], S[]]")]
    [InlineData("R(x, acc) = ()\nC(*xs) = xs\n[C(reduce([1], R, 0)), C(reduce([1], R, 0)*)]", "ok L[L[S[]], L[]]")]
    [InlineData("R(x, acc) = ()\n[reduce([1], R, 0), reduce([1], R, 0).string]", "err TypeMismatch")]
    [InlineData("R(x, acc) = ()\n[reduce([1], R, 0), tick(), reduce([2], R, ()), tick()]", "ok L[S[], 1, S[], 2]")]
    [InlineData("D(0) = (), []\nD(n) = n, []\nKeep(x) = true\ncount(filter(map([0, 1], D), Keep))", "ok 2")]
    [InlineData("D(x) = repeat({s, s + 1}, 1, x)\nmap([1, 2], D)", "ok L[S[1, 2], S[2, 3]]")]
    [InlineData("D(x) = x, x\nApply(f, *xs) = map(xs, f)\nApply(D, (), [])", "ok L[S[S[], S[]], S[L[], L[]]]")]
    public async Task Independent_ComposedConsumers_PreserveTheCompleteResult(string source, string expected)
    {
        var (observation, _) = await AllRoutesAsync(source);
        Assert.Equal(expected, observation.Outcome);
    }

    [Fact]
    public async Task Independent_EmptyReduceResult_PreservesPlannedLoopHandover()
    {
        const string source = "Z(x, acc) = ()\nStep(s) = reduce([s], Z, 0)\nrepeat(Step, 3, 5)";
        var (observation, _) = await AllRoutesAsync(source);
        Assert.Equal("ok S[]", observation.Outcome);
        var diagnostics = new LoopOptimizationDiagnostics();
        var observations = new EvaluationObservations();
        var parsed = SourceProvenance.ParseValid(source);
        var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), loopDiagnostics: diagnostics, observations: observations);
        Assert.True(result.IsOk);
        Assert.True(diagnostics.OptimizedLoopHits > 0);
        Assert.True(diagnostics.FallbackReasons.TryGetValue("loop expression did not emit exactly one state value", out var handovers));
        Assert.Equal(1, handovers);
        Assert.Equal(1, observations.OptimizedLoopHandoverMaterializationCount);
    }

    [Fact]
    public async Task Independent_ReduceDemandsItsInitial_WhileNestedOrdinaryCallsMayIgnoreIt()
    {
        const string reducer = "R(x, acc) = x\n";
        var (fold, _) = await AllRoutesAsync(reducer + "reduce([1, 2], R, 1 / 0)");
        var (nested, _) = await AllRoutesAsync(reducer + "R(2, R(1, 1 / 0))");
        Assert.Equal("err DivisionByZero", fold.Outcome);
        Assert.Equal("ok 2", nested.Outcome);
    }

    [Fact]
    public async Task Independent_ReduceRunsEarlierSteps_WhileNestedOrdinaryCallsMaySkipThem()
    {
        const string reducer = "R(x, acc) = if(x == 1, 1 / 0, x)\n";
        var (fold, _) = await AllRoutesAsync(reducer + "reduce([1, 2], R, 0)");
        var (nested, _) = await AllRoutesAsync(reducer + "R(2, R(1, 0))");
        Assert.Equal("err DivisionByZero", fold.Outcome);
        Assert.Equal("ok 2", nested.Outcome);
    }

    [Fact]
    public async Task Independent_ReduceAndNestedOrdinaryCalls_HaveTheirOwnDemandOrder()
    {
        const string reducer = "R(x, acc) = trace(x), acc\n";
        var (fold, _) = await AllRoutesAsync(reducer + "reduce([1, 2], R, 0)");
        var (nested, _) = await AllRoutesAsync(reducer + "R(2, R(1, 0))");
        Assert.Equal(fold.Outcome, nested.Outcome);
        Assert.Equal(new[] { "trace(1)", "trace(2)" }, fold.HostCalls);
        Assert.Equal(new[] { "trace(2)", "trace(1)" }, nested.HostCalls);
    }

    [Fact]
    public async Task Independent_ReduceAndNestedOrdinaryCalls_CanDifferOnSuccessfulEffectfulValues()
    {
        const string reducer = "R(x, acc) = tick() * x + acc\n";
        var (fold, _) = await AllRoutesAsync(reducer + "reduce([1, 2], R, 0)");
        var (nested, _) = await AllRoutesAsync(reducer + "R(2, R(1, 0))");
        Assert.Equal("ok 5", fold.Outcome);
        Assert.Equal("ok 4", nested.Outcome);
        Assert.Equal(new[] { "tick#1", "tick#2" }, fold.HostCalls);
        Assert.Equal(fold.HostCalls, nested.HostCalls);
    }

    [Fact]
    public async Task Independent_MapDemandsItsCollection_WhileOrdinaryCallsMaySkipIndexedArguments()
    {
        const string definitions = "L = [1 / 0, 2]\nF(x) = 0\n";
        var (mapped, _) = await AllRoutesAsync(definitions + "map(L, F)");
        var (calls, _) = await AllRoutesAsync(definitions + "[F(L:0), F(L:1)]");
        Assert.Equal("err DivisionByZero", mapped.Outcome);
        Assert.Equal("ok L[0, 0]", calls.Outcome);
    }

    [Fact]
    public async Task Independent_MapAndOrdinaryCalls_CanDifferOnSuccessfulEffectfulValues()
    {
        const string definitions = "L = [tick(), tick()]\nF(x) = tick()\n";
        var (mapped, _) = await AllRoutesAsync(definitions + "map(L, F)");
        var (calls, _) = await AllRoutesAsync(definitions + "[F(L:0), F(L:1)]");
        Assert.Equal("ok L[3, 4]", mapped.Outcome);
        Assert.Equal("ok L[1, 2]", calls.Outcome);
        Assert.Equal(new[] { "tick#1", "tick#2", "tick#3", "tick#4" }, mapped.HostCalls);
        Assert.Equal(new[] { "tick#1", "tick#2" }, calls.HostCalls);
    }

    [Theory]
    [InlineData("F(x) = pause(x), ()\nmap([1, 2], F)")]
    [InlineData("R(x, acc) = pause(x), ()\nreduce([1, 2], R, 0)")]
    public async Task Independent_CancellationDuringSuspendingCallback_DoesNotBuildAPartialResult(string source)
    {
        using var cancellation = new CancellationTokenSource();
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var calls = 0;
        var operations = HostOperations.Create(HostOperation.CreateAsync("pause", async (args, _) =>
        {
            Interlocked.Increment(ref calls);
            reached.SetResult();
            await release.Task;
            return args[0];
        }, "x"));
        var task = KatLangEngine.RunAsync(source, new RunOptions { HostOperations = operations, EvaluationCancellationToken = cancellation.Token });
        try
        {
            await reached.Task.WaitAsync(TimeSpan.FromSeconds(10));
            Assert.False(task.IsCompleted);
            cancellation.Cancel();
        }
        finally
        {
            release.TrySetResult();
        }
        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await task);
        Assert.Equal(cancellation.Token, thrown.CancellationToken);
        Assert.Equal(1, calls);
    }

    // ── Harness ───────────────────────────────────────────────────────────────────────────────────────

    internal sealed record Budget(long Steps, long Checkpoints, int PeakDepth, long MaterializedItems, long MaterializedStringChars);

    /// <summary>One route's outcome: kind, neutral value with the program's emitted count, every error as
    /// <c>Code: message @ span</c>, and the host-call log.</summary>
    internal sealed record Observation(string Kind, string? Value, int? Count, IReadOnlyList<string> Errors, IReadOnlyList<string> HostCalls)
    {
        /// <summary><c>ok VALUE</c>, <c>err CODE</c> (the first error), or the kind.</summary>
        public string Outcome => Kind switch
        {
            "ok" => $"ok {Value}",
            "err" => $"err {Errors[0][..Errors[0].IndexOf(':')]}",
            _ => Kind,
        };

        public bool Equals(Observation? other)
            => other is not null && Kind == other.Kind && Value == other.Value && Count == other.Count
                && Errors.SequenceEqual(other.Errors) && HostCalls.SequenceEqual(other.HostCalls);

        public override int GetHashCode() => HashCode.Combine(Kind, Value, Count);

        public override string ToString()
            => $"{Kind} {Value} n={Count} errors=[{string.Join(" | ", Errors)}] host=[{string.Join(",", HostCalls)}]";
    }

    private sealed class HostLog
    {
        private int _ticks;
        public List<string> Calls { get; } = [];

        private Result Log(string call, Result value)
        {
            lock (Calls)
                Calls.Add(call);
            return value;
        }

        public Result Tick()
        {
            var tick = Interlocked.Increment(ref _ticks);
            return Log($"tick#{tick}", new Result.Atom(tick));
        }

        public Result Trace(Result value) => Log($"trace({SixRouteAgreement.Neutral(value)})", value);
    }

    private static HostOperations Operations(HostLog log, bool suspending)
        => suspending
            ? HostOperations.Create(
                HostOperation.CreateAsync("tick", async (_, _) => { await Task.Yield(); return log.Tick(); }),
                HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return log.Trace(args[0]); }, "x"))
            : HostOperations.Create(
                HostOperation.Create("tick", (_, _) => log.Tick()),
                HostOperation.Create("trace", (args, _) => log.Trace(args[0]), "x"));

    private static async Task<(Observation Observation, Budget? Budget)> ObserveAsync(
        SixRouteAgreement.Route route, string source, long? seed, EvaluationLimits? limits)
    {
        var log = new HostLog();
        var operations = Operations(log, route is SixRouteAgreement.Route.EngineAsyncTwin or SixRouteAgreement.Route.ForcedTwin);
        var options = new RunOptions { HostOperations = operations, RandomSeed = seed, EvaluationLimits = limits };
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
            return (new Observation("parse", null, null, [.. parsed.Diagnostics.Select(static d => d.Message)], [.. log.Calls]), null);

        var program = new Expr.AlgorithmExpr(parsed.Root);
        var (result, budget) = route switch
        {
            SixRouteAgreement.Route.Generic => Evaluator.RunCountedObserved(program, limits, enableOptimizations: false,
                hostOperations: operations, randomSeed: seed),
            SixRouteAgreement.Route.Optimized => Evaluator.RunCountedObserved(program, limits, enableOptimizations: true,
                hostOperations: operations, randomSeed: seed),
            SixRouteAgreement.Route.ForcedTwin => await Evaluator.RunCountedObservedAsync(program, limits,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), hostOperations: operations, randomSeed: seed),
            _ => throw new ArgumentOutOfRangeException(nameof(route), route, null),
        };
        var counters = new Budget(budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth,
            budget.MaterializedItems, budget.MaterializedStringChars);
        return result.IsError
            ? (new Observation("err", null, null, [Describe(KatLangError.FromEvalError(result.Error))], [.. log.Calls]), counters)
            : (new Observation("ok", SixRouteAgreement.Neutral(result.Value.Value), result.Value.EmittedCount, [], [.. log.Calls]), counters);
    }

    /// <summary>
    /// Runs <paramref name="source"/> on every route; requires every route to agree with the synchronous engine and
    /// the three evaluator routes to report identical budget counters. Returns the oracle and the counters.
    /// </summary>
    private static async Task<(Observation Observation, Budget Budget)> AllRoutesAsync(
        string source, long? seed = null, EvaluationLimits? limits = null)
    {
        var (oracle, _) = await ObserveAsync(SixRouteAgreement.Route.EngineSync, source, seed, limits);
        Assert.True(oracle.Kind is not ("parse" or "none"), $"source must parse cleanly and have output: {oracle}\nsource:\n{source}");
        Budget? counters = null;
        foreach (var route in SixRouteAgreement.Routes.Skip(1))
        {
            var (observation, budget) = await ObserveAsync(route, source, seed, limits);
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

    private static Observation FromRunResult(RunResult result, HostLog log) => result switch
    {
        RunResult.Success success => new("ok", SixRouteAgreement.Neutral(success.Value), success.EmittedCount, [], [.. log.Calls]),
        RunResult.EvalFailure failure => new("err", null, null, [.. failure.Errors.Select(Describe)], [.. log.Calls]),
        RunResult.ParseFailure failure => new("parse", null, null, [.. failure.Errors.Select(Describe)], [.. log.Calls]),
        RunResult.NoProgramOutput none => new("none", null, null, [none.Diagnostic.Code.ToString()], [.. log.Calls]),
    };

    private static string Describe(KatLangError error) => $"{error.Code}: {error.Message} @ {error.Span}";

    private static EvalError GenericError(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), enableOptimizations: false);
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
