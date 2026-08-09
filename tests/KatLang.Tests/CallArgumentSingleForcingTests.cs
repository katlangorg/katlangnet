namespace KatLang.Tests;

/// <summary>
/// Deterministic exactly-once regression coverage for call-argument
/// preparation, across every call family: a WRITTEN argument expression is
/// semantically forced exactly once per call-preparation/binding event.
///
/// <para><b>Mechanism</b>: the run-scoped <c>EvaluationBudget</c> counters
/// exposed by <c>Evaluator.RunCountedObserved</c> — the same deterministic
/// observation infrastructure <see cref="PatternedCallSingleEvaluationTests"/>
/// uses. <c>ConsumedSteps</c> increments once per charged dynamic invocation
/// (every user/conditional call boundary), and <c>MaterializedItems</c> once
/// per persistent collection slot built. Each probe argument is an explicit
/// user call <c>Make()</c> whose body materializes a 4-item <c>range</c>
/// list, so ONE semantic forcing of the written argument costs exactly
/// 1 step + 4 items. A duplicate forcing during one preparation event would
/// raise the run's step count by 1 and its item count by 4 — these exact-count
/// pins fail hard on any duplicate, unlike a value-equality check (two
/// forcings of a pure expression produce equal values).</para>
///
/// <para><b>Boundary rule</b>: exactly-once means once per INTENTIONAL call
/// boundary. Each expected step count below is the number of user-call
/// invocations the program intentionally performs (outer call + one forcing
/// of each written <c>Make()</c> argument); it does not forbid a separate
/// user-level call from evaluating again.</para>
///
/// <para><b>Algorithm probing is non-forcing</b>: the higher-order case pins
/// that AlgEnv probing of a callable argument adds no step; the poison-block
/// test <c>PatternedCallSingleEvaluationTests.MultiParameterBlock_RemainsLazyOnTheAlgorithmOnlyChannel</c>
/// additionally proves a probed-but-never-consumed argument is never value-forced
/// at all (its body divides by zero).</para>
/// </summary>
public class CallArgumentSingleForcingTests
{
    private static Expr ParseProgram(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.False(
            parsed.HasErrors,
            string.Join(Environment.NewLine, parsed.Diagnostics.Select(static diagnostic => diagnostic.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    /// <summary>
    /// One deterministic case per call family. Columns: the number of charged
    /// call boundaries (outer call + each argument forcing), the number of
    /// materialized collection slots, and the expected value. A second
    /// semantic forcing of any written <c>Make()</c>/<c>MakePair()</c>
    /// argument would add +1 step (and +4/+2 items) and fail the pin.
    /// </summary>
    public static TheoryData<string, string, decimal, long, long> Families => new()
    {
        // Flat fixed call F(Make()): steps = F + Make = 2; items = Make's
        // 4-item range list.
        {
            "flat",
            "Make = range(1, 4)\nF(x) = x.count\nF(Make())",
            4m, 2, 4
        },
        // Patterned call Pair((Make(), 6)): steps = Pair + Make = 2; items =
        // range list (4) + the written two-slot group capture (2). The
        // captured value AND its written-slot projection come from the same
        // prepared pass — the numbers match PatternedCallSingleEvaluationTests.
        {
            "patterned",
            "Make = range(1, 4)\nPair((items, marker)) = items.count + marker\nPair((Make(), 6))",
            10m, 2, 6
        },
        // Collecting call V(Make()): steps = V + Make = 2; items = range list
        // (4) + the one-slot collected exact list (1). The collector receives
        // ONE written argument (the range list stays one collected slot,
        // hence count = 1) — collection is not re-forcing.
        {
            "collecting",
            "Make = range(1, 4)\nV(*items) = items.count\nV(Make())",
            1m, 2, 5
        },
        // Clause-family call C(Make()): argument preparation happens ONCE
        // before clause selection; trying the literal clause first must not
        // re-force the argument. steps = C (one invocation for the whole
        // family) + Make = 2; items = 4.
        {
            "clause-family",
            "Make = range(1, 4)\nC(0) = 0\nC(x) = x.count\nC(Make())",
            4m, 2, 4
        },
        // Spread call F2(MakePair()*): the SPREAD SOURCE expression is forced
        // once — steps = F2 + MakePair = 2; items = the captured pair (2)
        // plus the spread supply's combined counted value (2), both built
        // once per forcing. Its 2 resulting supplied items then bind the two
        // fixed parameters WITHOUT re-forcing the source — the bound values
        // prove both items arrived (7*100 + 9), and a second forcing would
        // observe 3 steps / 8 items.
        {
            "spread",
            "MakePair = (7, 9)\nF2(a, b) = a * 100 + b\nF2(MakePair()*)",
            709m, 2, 4
        },
        // Structural dot call Obj.M(Make()): resolving the receiver Obj is
        // structural lookup, not semantic evaluation (no step); the explicit
        // argument is forced once. steps = M + Make = 2; items = 4.
        {
            "structural-dot",
            "Make = range(1, 4)\nObj = {public M(x) = x.count}\nObj.M(Make())",
            4m, 2, 4
        },
        // Lexical dot fallback Make().F2(6): the receiver expression joins the
        // fresh argument bundle as the injected leading slot and is forced
        // exactly once, like every other slot. steps = F2 + Make = 2;
        // items = 4.
        {
            "lexical-dot",
            "Make = range(1, 4)\nF2(a, b) = a.count + b\nMake().F2(6)",
            10m, 2, 4
        },
        // Higher-order dual view Apply(Increment): AlgEnv probing of the
        // callable argument is NON-FORCING — the only invocations are Apply
        // and the callee's own intentional f(9) call boundary. steps = 2;
        // items = 0.
        {
            "higher-order-probe",
            "Apply = f(9)\nIncrement = x + 1\nApply(Increment)",
            10m, 2, 0
        },
        // Zero-parameter inline block Call0({42}): the block's algorithm
        // identity crosses the higher-order boundary WITHOUT value-forcing
        // the block during probing; the only invocations are Call0 and the
        // callee's intentional f() call of the block. steps = 2; items = 0.
        // A duplicate forcing (probe-time evaluation) would add a step.
        {
            "zero-param-block",
            "Call0 = f()\nCall0({42})",
            42m, 2, 0
        },
    };

    [Theory]
    [MemberData(nameof(Families))]
    public void WrittenArgumentExpressions_AreForcedExactlyOnce(
        string family, string source, decimal expectedValue, long expectedSteps, long expectedItems)
    {
        foreach (var optimize in new[] { false, true })
        {
            var (result, budget) = Evaluator.RunCountedObserved(
                ParseProgram(source),
                enableOptimizations: optimize);

            Assert.True(result.IsOk, $"{family} (optimize: {optimize}) failed: {(result.IsError ? result.Error.ToString() : "?")}");
            Assert.Equal(expectedValue, Assert.IsType<Result.Atom>(result.Value.Value).Value);
            Assert.True(
                expectedSteps == budget.ConsumedSteps,
                $"{family} (optimize: {optimize}): expected {expectedSteps} charged call boundaries, observed {budget.ConsumedSteps}");
            Assert.True(
                expectedItems == budget.MaterializedItems,
                $"{family} (optimize: {optimize}): expected {expectedItems} materialized items, observed {budget.MaterializedItems}");
        }
    }
}
