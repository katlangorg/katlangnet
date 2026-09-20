using System.Numerics;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

/// <summary>
/// Comparison-chain EVALUATION semantics (September 2026), pinned end to end: adjacent-pair
/// links, every operand evaluated exactly once, incremental left-to-right evaluation, eager
/// continuation after <c>false</c>, termination at the first error, link-precise diagnostics
/// and spans, and strategy/twin parity (generic, planned loop, async twin). Lean twin:
/// <c>lean/CoreTests/ComparisonChains.lean</c>; the corpus cases
/// <c>comparison-chains-compare-adjacent-pairs</c> / <c>comparison-chain-is-eager-after-false</c>
/// pin the same chains against the Lean evaluator.
/// </summary>
public class ComparisonChainEvaluationTests
{
    private static KatLangError EngineFailure(string source, RunOptions? options = null)
        => Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source, options)).Errors);

    private static Result Atom(Decimal128 value) => new Result.Atom(value);

    /// <summary>A zero-parameter host operation that counts its invocations and returns <paramref name="value"/>.</summary>
    private static HostOperation Counted(string name, Decimal128 value, Hosting.HostOperationApiTests.Counter counter)
        => HostOperation.Create(name, (_, _) =>
        {
            counter.Increment();
            return Atom(value);
        });

    private static HostOperation CountedAsync(string name, Decimal128 value, Hosting.HostOperationApiTests.Counter counter)
        => HostOperation.CreateAsync(name, async (_, _) =>
        {
            await Task.Yield();
            counter.Increment();
            return Atom(value);
        });

    // ── The compatibility examples: one tier, adjacent pairs ─────────────────

    [Theory]
    [InlineData("1 == 1 == 1", true)]
    [InlineData("1 != 1 != 1", false)]
    [InlineData("1 < 2 < 3", true)]
    [InlineData("1 == 1 < 2", true)]
    [InlineData("1 == 1 < 1", false)]
    [InlineData("1 == (1 < 2)", false)]
    public void TheBreakingChangeExamples_EvaluateAsChains(string source, bool expected)
        => AssertEvalBool(source, expected);

    [Fact]
    public void TheOldNestedReading_IsStillAvailableThroughParentheses()
        => AssertEvalFailsWithTypeMismatch("(1 == 1) < 2", "operator `<` expects numeric scalar operands, but the left operand was a Boolean value: true");

    // ── Adjacent-pair semantics over every operator class ───────────────────

    [Theory]
    // all true
    [InlineData("1 < 2 < 3", true)]
    [InlineData("1 <= 1 <= 2", true)]
    [InlineData("3 > 2 >= 2", true)]
    [InlineData("1 == 1 == 1", true)]
    [InlineData("1 != 2 != 3", true)]
    // first / middle / last link false
    [InlineData("2 < 1 < 3", false)]
    [InlineData("1 < 3 < 2 < 4", false)]
    [InlineData("1 < 2 < 2", false)]
    // equality-only, inequality-only, ordering-only
    [InlineData("2 == 2 == 2 == 2", true)]
    [InlineData("2 == 2 == 3", false)]
    [InlineData("1 != 2 != 1", true)]
    [InlineData("1 != 1 != 2", false)]
    [InlineData("1 != 2 != 3 != 1", true)]
    [InlineData("1 < 2 <= 2 < 3", true)]
    [InlineData("3 >= 3 > 2 >= 2", true)]
    // mixed chains
    [InlineData("1 < 2 == 2", true)]
    [InlineData("1 == 1 < 2", true)]
    [InlineData("1 != 2 <= 2", true)]
    [InlineData("1 < 2 <= 2 == 2 != 3", true)]
    [InlineData("1 < 2 <= 2 == 2 != 2", false)]
    // numeric equality versus ordering on the same operands
    [InlineData("1 < 1 == 1", false)]
    [InlineData("1 <= 1 == 1", true)]
    // Boolean equality inside a mixed chain: `2 == true` is false (a number is never a Boolean)
    [InlineData("1 < 2 == true", false)]
    [InlineData("true == true != false", true)]
    [InlineData("(1 < 2) == true", true)]
    // structural equality on strings, sequences, and lists
    [InlineData("'a' == 'a' == 'a'", true)]
    [InlineData("'a' != 'b' != 'a'", true)]
    [InlineData("(1, 2) == (1, 2) == (1, 2)", true)]
    [InlineData("[1] == [1] != (1)", true)]
    // two operands
    [InlineData("2 < 3", true)]
    [InlineData("2 != 2", false)]
    // longer chains
    [InlineData("1 < 2 < 3 < 4 < 5 < 6 < 7", true)]
    [InlineData("1 < 2 < 3 < 4 < 5 < 6 < 6", false)]
    // arithmetic operands bind tighter than the chain
    [InlineData("1 + 1 < 3 * 1 <= 4 - 1", true)]
    [InlineData("-2 ^ 2 < -3 < 0", true)]
    public void Chains_CompareAdjacentPairs(string source, bool expected)
        => AssertEvalBool(source, expected);

    [Fact]
    public void ALongFlatChain_Evaluates()
    {
        var source = string.Join(" < ", Enumerable.Range(1, 301));
        AssertEvalBool(source, true);
        AssertEvalBool(source.Replace("301", "300"), false);
    }

    [Theory]
    [InlineData("N = Math.Sqrt(-1)\nN == N == N", true)]
    [InlineData("N = Math.Sqrt(-1)\nN != N", false)]
    [InlineData("N = Math.Sqrt(-1)\n1 < N < 2", false)]
    [InlineData("N = Math.Sqrt(-1)\nN <= N", false)]
    [InlineData("N = Math.Sqrt(-1)\n1 < 2 < N", false)]
    public void NaN_KeepsStructuralEqualityAndIeeeOrdering_InsideChains(string source, bool expected)
        // Existing semantics, unchanged by chaining: `==` is structural (NaN equals NaN),
        // the ordering comparisons are IEEE (every comparison with NaN is false).
        => AssertEvalBool(source, expected);

    // ── Parentheses ─────────────────────────────────────────────────────────

    [Theory]
    [InlineData("(1 < 2) == true", true)]
    [InlineData("(1 < 2) == (3 < 4)", true)]
    [InlineData("(1 < 2) == (3 > 4)", false)]
    [InlineData("(1 < 2 < 3) == true", true)]
    [InlineData("1 == (2 < 3 < 4)", false)]
    [InlineData("true == (2 < 3 < 4)", true)]
    [InlineData("(1 == 1) == (1 < 2)", true)]
    public void ParenthesizedChains_AreOrdinaryBooleanOperands(string source, bool expected)
        => AssertEvalBool(source, expected);

    [Theory]
    [InlineData("1 < (2 == 2)", "1 < (2 == 2)", "operator `<` expects numeric scalar operands, but the right operand was a Boolean value: true")]
    [InlineData("(1 < 2) < 3", "(1 < 2) < 3", "operator `<` expects numeric scalar operands, but the left operand was a Boolean value: true")]
    [InlineData("(1 < 2) < (3 < 4)", "(1 < 2) < (3 < 4)", "operator `<` expects numeric scalar operands, but the left operand was a Boolean value: true")]
    public void ParenthesizedChains_UnderOrdering_AreTheBooleanOrderingRejection_NamingTheGrouping(string source, string context, string message)
    {
        var error = EngineFailure(source);
        Assert.Equal(KatLangErrorCode.TypeMismatch, error.Code);
        Assert.Contains($"while evaluating `{context}`", error.Message, StringComparison.Ordinal);
        Assert.Contains(message, error.Message, StringComparison.Ordinal);
    }

    // ── Composition with the surrounding operators ──────────────────────────

    [Theory]
    [InlineData("not 1 < 2 < 3", false)]
    [InlineData("not 3 < 2 < 1", true)]
    [InlineData("1 < 2 < 3 and 4 < 5", true)]
    [InlineData("1 < 2 < 3 and 5 < 4", false)]
    [InlineData("3 < 2 or 1 < 2 < 3", true)]
    [InlineData("1 < 2 < 3 xor 1 < 2", false)]
    [InlineData("not 1 < 2 and 2 < 3", false)]
    [InlineData("if(1 <= 2 <= 3, 7, 9) == 7", true)]
    [InlineData("range(1, 5).filter{1 < x < 5}.count == 3", true)]
    public void Chains_ComposeWithNotTheLogicalOperatorsAndPredicates(string source, bool expected)
        => AssertEvalBool(source, expected);

    // ── Exactly-once operand evaluation ─────────────────────────────────────

    [Fact]
    public void EveryOperand_IsEvaluatedExactlyOnce_ThroughHostOperationCounters()
    {
        var a = new Hosting.HostOperationApiTests.Counter();
        var b = new Hosting.HostOperationApiTests.Counter();
        var c = new Hosting.HostOperationApiTests.Counter();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(Counted("A", 1, a), Counted("B", 2, b), Counted("C", 3, c)),
        };

        // A() < B() < C(): the middle operand is compared twice but evaluated once.
        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run("A() < B() < C()", options));
        Assert.Equal("true", result.ToDisplayString());
        Assert.Equal(1, a.Count);
        Assert.Equal(1, b.Count);
        Assert.Equal(1, c.Count);
    }

    [Fact]
    public void EveryOperand_IsEvaluatedExactlyOnce_InALongerMixedChain_AndAfterAFalseLink()
    {
        var counters = Enumerable.Range(0, 5).Select(_ => new Hosting.HostOperationApiTests.Counter()).ToArray();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                Counted("A", 1, counters[0]), Counted("B", 2, counters[1]), Counted("C", 2, counters[2]),
                Counted("D", 9, counters[3]), Counted("E", 3, counters[4])),
        };

        // A < B <= C == D != E: C == D is false (2 == 9), yet every later operand still
        // runs exactly once and the chain is false.
        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run("A() < B() <= C() == D() != E()", options));
        Assert.Equal("false", result.ToDisplayString());
        Assert.All(counters, counter => Assert.Equal(1, counter.Count));
    }

    [Fact]
    public void OperandReads_KeepTheOrdinaryPropertyVersusCallRule()
    {
        // A chain operand is an ordinary value read: a property-style read `B` goes
        // through the zero-argument property cache (one invocation per run whatever the
        // chain does with it), while every WRITTEN call `B()` runs — once each, so two
        // written calls are two invocations and never more.
        var read = new Hosting.HostOperationApiTests.Counter();
        var reads = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            "1 < B < 3, B == B == 2", new RunOptions { HostOperations = HostOperations.Create(Counted("B", 2, read)) }));
        Assert.Equal("true\ntrue", reads.ToDisplayString().ReplaceLineEndings("\n"));
        Assert.Equal(1, read.Count);

        // 1 < 2 < 3 > 2 > 1: two written calls, each run once.
        var called = new Hosting.HostOperationApiTests.Counter();
        Assert.Equal("true", Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            "1 < B() < 3 > B() > 1", new RunOptions { HostOperations = HostOperations.Create(Counted("B", 2, called)) })).ToDisplayString());
        Assert.Equal(2, called.Count);
    }

    [Fact]
    public async Task EveryOperand_IsEvaluatedExactlyOnce_OnTheAsyncTwinPath()
    {
        var a = new Hosting.HostOperationApiTests.Counter();
        var b = new Hosting.HostOperationApiTests.Counter();
        var c = new Hosting.HostOperationApiTests.Counter();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(CountedAsync("A", 1, a), CountedAsync("B", 2, b), CountedAsync("C", 3, c)),
        };

        var result = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync("A() < B() < C()\nC() > B() == B() > A()", options));
        Assert.Equal("true\ntrue", result.ToDisplayString().ReplaceLineEndings("\n"));
        // Row 1 runs each once; row 2 runs C once, B twice (written twice), A once.
        Assert.Equal(2, a.Count);
        Assert.Equal(3, b.Count);
        Assert.Equal(2, c.Count);
    }

    [Fact]
    public void RandomOperands_DrawOnceEach_InWrittenOrder()
    {
        // Seeded randomness observes evaluation order and count: the stream of
        // `randomInt(1, 1000000)` draws for `R() < R() < R()` is the SAME three draws a
        // three-row program takes, so no operand was drawn twice or out of order.
        var rows = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            "R = randomInt(1, 1000000)\nR(), R(), R()", new RunOptions { RandomSeed = 42 })).Atoms;
        Assert.Equal(3, rows.Count);
        var expected = rows[0] < rows[1] && rows[1] < rows[2];

        var chain = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            "R = randomInt(1, 1000000)\nR() < R() < R(), R()", new RunOptions { RandomSeed = 42 }));
        var display = chain.ToDisplayString().ReplaceLineEndings("\n").Split('\n');
        Assert.Equal(expected ? "true" : "false", display[0]);
        // The FOURTH draw of the same stream follows the chain's three draws.
        var fourth = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            "R = randomInt(1, 1000000)\nR(), R(), R(), R()", new RunOptions { RandomSeed = 42 })).Atoms[3];
        Assert.Equal(fourth.ToString(), display[1]);
    }

    // ── Eager after false ───────────────────────────────────────────────────

    [Fact]
    public void AFalseLink_NeverStopsTheChain_ALaterInvalidComparisonIsStillReported()
    {
        // 3 < 2 is false, and 2 < true is STILL compared — the ordering rejection names
        // exactly that adjacent comparison, never `(3 < 2) < true`.
        var error = EngineFailure("3 < 2 < true");
        Assert.Equal(KatLangErrorCode.TypeMismatch, error.Code);
        Assert.Contains("while evaluating `2 < true`", error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("(3 < 2)", error.Message, StringComparison.Ordinal);
        Assert.Contains("operator `<` expects numeric scalar operands, but the right operand was a Boolean value: true", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AFalseLink_NeverStopsTheChain_LaterOperandsStillRun()
    {
        var later = new Hosting.HostOperationApiTests.Counter();
        var options = new RunOptions { HostOperations = HostOperations.Create(Counted("Later", 10, later)) };

        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run("3 < 2 < Later() < 20", options));
        Assert.Equal("false", result.ToDisplayString());
        Assert.Equal(1, later.Count);

        // ...and a later operand's own error surfaces after an earlier false link.
        Assert.IsType<EvalError.DivByZero>(Innermost(FailureOf("3 < 2 < 1 / 0")));
        Assert.IsType<EvalError.DivByZero>(Innermost(FailureOf("1 == 2 == 1 / 0")));
    }

    // ── Errors terminate ────────────────────────────────────────────────────

    [Fact]
    public void AnEarlierOperandError_StopsTheChain_BeforeLaterOperands()
    {
        var b = new Hosting.HostOperationApiTests.Counter();
        var c = new Hosting.HostOperationApiTests.Counter();
        var options = new RunOptions { HostOperations = HostOperations.Create(Counted("B", 2, b), Counted("C", 3, c)) };

        var error = EngineFailure("1 / 0 < B() < C()", options);
        Assert.Equal(KatLangErrorCode.DivisionByZero, error.Code);
        Assert.Equal(0, b.Count);
        Assert.Equal(0, c.Count);
    }

    [Fact]
    public void AnEarlierLinkError_StopsTheChain_BeforeLaterOperands()
    {
        var a = new Hosting.HostOperationApiTests.Counter();
        var c = new Hosting.HostOperationApiTests.Counter();
        var options = new RunOptions { HostOperations = HostOperations.Create(Counted("A", 1, a), Counted("C", 3, c)) };

        // A() < true fails at the FIRST link: A ran once, C never.
        var error = EngineFailure("A() < true < C()", options);
        Assert.Equal(KatLangErrorCode.TypeMismatch, error.Code);
        Assert.Contains("while evaluating `A(...) < true`", error.Message, StringComparison.Ordinal);
        Assert.Equal(1, a.Count);
        Assert.Equal(0, c.Count);

        // The earlier failure wins over a later one that would also fail.
        Assert.Contains("while evaluating `1 < true`", EngineFailure("1 < true < 'x'").Message, StringComparison.Ordinal);
        Assert.Contains("Strings only support == and != operators", EngineFailure("'a' < 'b' < true").Message, StringComparison.Ordinal);
    }

    [Fact]
    public void OperandsEvaluateLeftToRight_Incrementally()
    {
        // The first operand's error precedes the second operand's evaluation, and the
        // first link is applied before the third operand is evaluated.
        Assert.IsType<EvalError.DivByZero>(Innermost(FailureOf("1 / 0 < 2 / 0")));
        var error = EngineFailure("1 < true < 1 / 0");
        Assert.Equal(KatLangErrorCode.TypeMismatch, error.Code);
        Assert.Contains("while evaluating `1 < true`", error.Message, StringComparison.Ordinal);
    }

    // ── Diagnostics: the failing LINK, with its own span ────────────────────

    [Fact]
    public void ALinkFailure_IsLocatedAtTheTwoAdjacentOperands()
    {
        // `1 < 2 < true`: the failing link `2 < true` occupies columns 5..13.
        var error = EngineFailure("1 < 2 < true");
        Assert.Equal(new SourceSpan(1, 5, 1, 13), error.Span);

        // The first link of a chain is located at its own two operands too.
        Assert.Equal(new SourceSpan(1, 1, 1, 9), EngineFailure("1 < true < 2").Span);

        // A parenthesized operand contributes its full group extent (F6).
        Assert.Equal(new SourceSpan(1, 1, 1, 12), EngineFailure("(1 < 2) < 3").Span);

        // Across lines, the hull of the two operands.
        Assert.Equal(new SourceSpan(1, 5, 2, 7), EngineFailure("1 < 2 <\n  true").Span);
    }

    [Theory]
    [InlineData("1 < 2 < true", "2 < true")]
    [InlineData("1 < 2 <= 3 > false", "3 > false")]
    [InlineData("1 + 1 < 2 * 2 < true", "2 * 2 < true")]
    [InlineData("(1 < 2) == 3 < true", "3 < true")]
    [InlineData("1 < (2 == 2)", "1 < (2 == 2)")]
    [InlineData("true < 1", "true < 1")]
    public void ALinkFailure_NamesExactlyTheFailingAdjacentComparison(string source, string context)
    {
        var error = EngineFailure(source);
        Assert.Contains($"while evaluating `{context}`", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void StringOperands_KeepTheirEstablishedRejections_PerLink()
    {
        AssertEvalFailsWithTypeMismatch("'a' < 'b'", "Strings only support == and != operators");
        AssertEvalFailsWithTypeMismatch("'a' == 'a' < 'b'", "Strings only support == and != operators");
        AssertEvalFailsWithTypeMismatch("1 == 1 < 'b'", "Cannot apply operator to string and non-string operands");
        AssertEvalFailsWithTypeMismatch("1 < () < 3", "operator `<` expects numeric scalar operands, but the right operand was a sequence value with 0 sequence elements: ()");
        AssertEvalFailsWithTypeMismatch("1 < [2] < 3", "operator `<` expects numeric scalar operands, but the right operand was a list value with 1 element: [2]");
    }

    // ── Host-built chains ───────────────────────────────────────────────────

    [Fact]
    public void AHostBuiltChainWithNoLinks_EvaluatesItsOperandAndIsTrue()
    {
        var result = Evaluator.Run(new Expr.Comparison(new Expr.Num(7), []));
        Assert.False(result.IsError);
        Assert.Equal(new Result.Bool(true), result.Value, Result.ValueComparer);

        // ...and its one operand IS evaluated (an error there is the chain's outcome).
        var failing = Evaluator.Run(new Expr.Comparison(new Expr.Binary(BinaryOp.Div, new Expr.Num(1), new Expr.Num(0)), []));
        Assert.IsType<EvalError.DivByZero>(Innermost(failing.Error));
    }

    [Fact]
    public void AHostBuiltChain_UsesTheChainSpan_WhenAnOperandIsUnpositioned()
    {
        var chainSpan = new SourceSpan(3, 1, 3, 20);
        var chain = Chain(new Expr.Num(1), ComparisonOp.Lt, new Expr.Num(2), ComparisonOp.Lt, new Expr.BoolLiteral(true)) with { Span = chainSpan };
        var result = Evaluator.Run(chain);
        Assert.True(result.IsError);
        Assert.Equal(chainSpan, result.Error.Span);
    }

    [Fact]
    public void AChain_IsNotAnAlgorithm_InAlgorithmPosition()
    {
        // Surface syntax never puts a chain in callee position (`(1 < 2)(3)` is the
        // same-line separator error), so the algorithm-position rejection is pinned from
        // a host-built call whose callee is a chain: the ordinary not-an-algorithm
        // rejection, described by the chain's own kind (Lean: `resolveAlg`).
        var callee = Chain(new Expr.Num(1), ComparisonOp.Lt, new Expr.Num(2)) with { Span = new SourceSpan(1, 1, 1, 6) };
        var result = Evaluator.Run(new Expr.Call(callee, new OutputBundle([new Expr.Num(3)])));
        Assert.True(result.IsError);
        var error = Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(result.Error));
        Assert.Equal("comparison expression", error.Description);
        Assert.Equal(new SourceSpan(1, 1, 1, 6), error.Span);
    }

    // ── Strategy and twin parity ────────────────────────────────────────────

    [Fact]
    public void Chains_AgreeAcrossLoopStrategies()
    {
        AssertEvalLoopModes("Step = x + 1, 0 <= x < 5\nStep.while(0)", 5);
        // 0 → 1 → 11 → 12 … → 20; the proposed 21 is never committed (20 < 20 is false).
        AssertEvalLoopModes("Step = x + if(1 <= x <= 3, 10, 1), x < 20\nStep.while(0)", 20);
        // (0, 1) → (1, 3) → (2, 5) → (3, 7) → (4, 9) → (5, 11); then 5 < 11 <= 10 is false.
        AssertEvalResultLoopModes("Step(a, b) = a + 1, b + 2, a < b <= 10\nStep.while(0, 1)", Result.FromItems([new Result.Atom(5), new Result.Atom(11)]));
        AssertEvalResultLoopModes("Step(x) = x + 1, not 1 < x < 3\nStep.while(0)", new Result.Atom(2));
        AssertEvalResultLoopModes("Step(x) = x + 1, x == x == x and x < 2\nStep.while(0)", new Result.Atom(2));
    }

    [Theory]
    [InlineData("Step = x + 1, 0 <= x < true\nStep.while(0)")]
    [InlineData("Step = x + 1, 3 < 2 < 'x'\nStep.while(0)")]
    public void ChainRejections_AgreeAcrossLoopStrategies(string source)
    {
        var generic = EvalFull(source, enableLoopOptimization: false);
        var optimized = EvalFull(source, enableLoopOptimization: true);
        Assert.True(generic.IsError);
        Assert.True(optimized.IsError);
        Assert.Equal(generic.Error.ToString(), optimized.Error.ToString());
    }

    [Fact]
    public void ThePlannedLoop_PlansAChainAsOneNode_AndEvaluatesTheMiddleOperandOnce()
    {
        // `T()` is a planned temp CALL that materializes a ten-unit string on every
        // call (a call bypasses the property cache), so the string-unit budget observes
        // how often the middle operand ran: the chain form materializes 30 units per
        // iteration (the two literals and ONE call) on BOTH strategies, the
        // `and`-rewrite 40 (the two literals and TWO calls).
        const string chain = "Step = {\n    T = 'xxxxxxxxxx'\n    n + if('xxxxxxxxxx' == T() != 'yyyyyyyyyy', 1, 0)\n}\nStep.repeat(200, 0)";
        const string rewritten = "Step = {\n    T = 'xxxxxxxxxx'\n    n + if('xxxxxxxxxx' == T() and T() != 'yyyyyyyyyy', 1, 0)\n}\nStep.repeat(200, 0)";

        var diagnostics = new LoopOptimizationDiagnostics();
        var (planned, plannedBudget) = Evaluator.RunCountedObserved(
            Program(chain), enableOptimizations: true, loopDiagnostics: diagnostics);
        var (generic, genericBudget) = Evaluator.RunCountedObserved(Program(chain), enableOptimizations: false);
        var (twoCalls, twoCallsBudget) = Evaluator.RunCountedObserved(Program(rewritten), enableOptimizations: false);

        Assert.Equal("ok raw=200 n=1", AsyncEvaluationHarness.NeutralOf(planned));
        Assert.Equal("ok raw=200 n=1", AsyncEvaluationHarness.NeutralOf(generic));
        Assert.Equal("ok raw=200 n=1", AsyncEvaluationHarness.NeutralOf(twoCalls));
        Assert.Equal(200 * 30, genericBudget.MaterializedStringChars);
        Assert.Equal(200 * 30, plannedBudget.MaterializedStringChars);
        Assert.Equal(200 * 40, twoCallsBudget.MaterializedStringChars);

        var snapshot = diagnostics.GetSnapshot();
        Assert.Equal(1, snapshot.OptimizedLoopHits);
        Assert.Equal(0, snapshot.PlannedExpressionFallbacks);
        var plan = Assert.Single(snapshot.LoopPlans);
        var output = Assert.Single(plan.Expressions, e => e.Role == "output" && e.Index == 0);
        Assert.Equal(
            "Add(StateSlot(n), If(Compare(StringConst(length=10) Equal TempCall(T) NotEqual StringConst(length=10)), Const(1), Const(0)))",
            output.PlanSummary);
    }

    private static Expr Program(string source) => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    [Theory]
    [InlineData("1 < 2 < 3")]
    [InlineData("1 < 2 <= 2 == 2 != 3")]
    [InlineData("3 < 2 < true")]
    [InlineData("P = 5\n1 < P < 10, P == P == 5")]
    [InlineData("P = 5\n1 / 0 < P")]
    [InlineData("P = (1, 2)\nP == P != (2, 1)")]
    public async Task Chains_AgreeBetweenTheSyncEvaluatorAndTheAsyncTwin(string source)
    {
        var ast = AsyncEvaluationHarness.Ast(source);
        var (sync, syncBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var (twin, twinBudget) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache()));

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(twin));
        Assert.Equal(syncBudget.ConsumedSteps, twinBudget.ConsumedSteps);
        if (sync.IsError)
            Assert.Equal(sync.Error.ToString(), twin.Error.ToString());
    }

    private static EvalError FailureOf(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"`{source}` unexpectedly succeeded with {result.Value}");
        return result.Error;
    }
}
