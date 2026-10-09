using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// Deterministic evaluator resource limits: dynamic invocation depth (host-stack
/// safety) and the optional step budget (unbounded-work safety).
///
/// <para>Boundary assertions always configure an explicit small limit rather than
/// relying on <see cref="EvaluationLimits.MaxSupportedDepth"/>, so every assertion is
/// exact and identical on every platform and build configuration. Nothing here measures
/// elapsed time.</para>
/// </summary>
public class EvaluationLimitsTests
{
    // `f(k)` needs k + 1 nested invocations: f(k), f(k-1), ... f(0).
    private const string CountDown = "f(0) = 0\nf(n) = f(n - 1)\n";

    private static EvalResult<Result> Eval(string source, EvaluationLimits? limits = null)
        => Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), limits);

    private static EvalError ErrorOf(string source, EvaluationLimits? limits = null)
    {
        var result = Eval(source, limits);
        if (!result.IsError)
            Assert.Fail($"expected a structured error, got {result.Value}");
        return result.Error;
    }

    private static EvaluationLimits Depth(int maxDepth) => new() { MaxDepth = maxDepth };

    private static EvaluationLimits Steps(long maxSteps) => new() { MaxSteps = maxSteps };

    private static RunResult Run(string source, EvaluationLimits limits)
        => KatLangEngine.Run(source, new RunOptions { EvaluationLimits = limits });

    // ── Configuration and validation ─────────────────────────────────────────

    [Theory]
    [InlineData(0)]
    [InlineData(-1)]
    [InlineData(int.MinValue)]
    public void MaxDepth_ZeroOrNegative_Throws(int value)
        => Assert.Throws<ArgumentOutOfRangeException>(() => new EvaluationLimits { MaxDepth = value });

    [Theory]
    [InlineData(0L)]
    [InlineData(-1L)]
    [InlineData(long.MinValue)]
    public void MaxSteps_ZeroOrNegative_Throws(long value)
        => Assert.Throws<ArgumentOutOfRangeException>(() => new EvaluationLimits { MaxSteps = value });

    [Fact]
    public void MaxDepth_AboveCeiling_IsClampedToCeiling()
    {
        Assert.Equal(EvaluationLimits.MaxSupportedDepth, new EvaluationLimits { MaxDepth = int.MaxValue }.EffectiveMaxDepth);
        Assert.Equal(EvaluationLimits.MaxSupportedDepth, EvaluationLimits.Default.EffectiveMaxDepth);
        Assert.Equal(4, new EvaluationLimits { MaxDepth = 4 }.EffectiveMaxDepth);
    }

    [Fact]
    public void Defaults_AreDepthCeilingAndNoStepBudget()
    {
        Assert.Null(EvaluationLimits.Default.MaxDepth);
        Assert.Null(EvaluationLimits.Default.MaxSteps);
        // The default enforces NO step budget (Q-09b: the budget holds only effective
        // thresholds; there is no "configured" fact a strategy could be chosen from).
        Assert.Null(EvaluationLimits.Default.EffectiveMaxSteps);
        Assert.Equal(EvaluationLimits.MaxSupportedDepth, EvaluationBudget.Create(null).MaxDepth);
    }

    // ── Depth: direct recursion ──────────────────────────────────────────────

    [Fact]
    public void DirectRecursion_BelowLimit_Succeeds()
        => Assert.False(Eval($"{CountDown}f(5)", Depth(16)).IsError);

    [Fact]
    public void DirectRecursion_ExactlyAtLimit_Succeeds()
    {
        // Depth 16 admits exactly 16 nested invocations, so f(15) is the deepest call
        // that fits: f(15) .. f(0).
        Assert.False(Eval($"{CountDown}f(15)", Depth(16)).IsError);
    }

    [Fact]
    public void DirectRecursion_OneBeyondLimit_ReturnsDepthError()
    {
        var error = ErrorOf($"{CountDown}f(16)", Depth(16));
        Assert.Equal(16, Assert.IsType<EvalError.EvaluationDepthExceeded>(error).Limit);
    }

    [Fact]
    public void UnboundedDirectRecursion_ReturnsDepthError()
        => Assert.IsType<EvalError.EvaluationDepthExceeded>(ErrorOf("f(x) = f(x)\nf(1)", Depth(24)));

    [Fact]
    public void DefaultLimits_UnboundedRecursion_ReturnsResourceErrorWithoutCrashing()
    {
        // No configured limits: the internal ceiling must still apply on the public
        // engine path. The exact kind may be the deterministic depth limit or the
        // machine-dependent stack backstop, but it is always structured.
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("f(x) = f(x)\nf(1)"));
        Assert.Single(failure.Errors);
    }

    // ── Depth: mutual recursion ──────────────────────────────────────────────

    [Fact]
    public void MutualRecursion_TwoFunctions_ReturnsDepthError()
        => Assert.IsType<EvalError.EvaluationDepthExceeded>(
            ErrorOf("f(x) = g(x)\ng(x) = f(x)\nf(1)", Depth(20)));

    [Fact]
    public void MutualRecursion_ThreeFunctionCycle_ReturnsDepthError()
        => Assert.IsType<EvalError.EvaluationDepthExceeded>(
            ErrorOf("f(x) = g(x)\ng(x) = h(x)\nh(x) = f(x)\nf(1)", Depth(20)));

    // ── Depth: property recursion ────────────────────────────────────────────

    [Fact]
    public void PropertyRecursion_SelfReference_ReturnsDepthError()
        => Assert.IsType<EvalError.EvaluationDepthExceeded>(ErrorOf("A = A\nA", Depth(12)));

    [Fact]
    public void PropertyRecursion_MutuallyDependent_ReturnsDepthError()
        => Assert.IsType<EvalError.EvaluationDepthExceeded>(ErrorOf("A = B\nB = A\nA", Depth(12)));

    [Fact]
    public void PropertyRecursion_ExplicitCallForm_ReturnsDepthError()
        => Assert.IsType<EvalError.EvaluationDepthExceeded>(ErrorOf("A = A()\nA()", Depth(12)));

    [Fact]
    public void PropertyStyleAccess_RepeatedReads_StayWellWithinDepth()
    {
        // Depth is about ACTIVE invocations, so repeated (cached) property reads never
        // accumulate depth however many times the property is named.
        Assert.False(Eval("A = 1\nA + A + A + A + A + A + A + A", Depth(4)).IsError);
    }

    // ── Depth: conditional recursion ─────────────────────────────────────────

    [Fact]
    public void ConditionalRecursion_WithBaseCase_TerminatesWithinLimit()
        => Assert.False(Eval($"{CountDown}f(3)", Depth(8)).IsError);

    [Fact]
    public void ConditionalRecursion_WithoutBaseCase_ReturnsDepthError()
        => Assert.IsType<EvalError.EvaluationDepthExceeded>(
            ErrorOf("f(0) = f(0)\nf(n) = f(n)\nf(0)", Depth(16)));

    [Fact]
    public void IfBuiltinRecursion_ReturnsDepthError()
        => Assert.IsType<EvalError.EvaluationDepthExceeded>(
            ErrorOf("f(n) = if(n > 0, f(n - 1), 0)\nf(1000)", Depth(16)));

    // ── Depth: callback and higher-order recursion ───────────────────────────

    [Fact]
    public void CollectionCallbackRecursion_ReturnsDepthError()
        => Assert.IsType<EvalError.EvaluationDepthExceeded>(
            ErrorOf("F(x) = [x].map(F)\nF(1)", Depth(16)));

    [Fact]
    public void HigherOrderArgumentRecursion_ReturnsDepthError()
        => Assert.IsType<EvalError.EvaluationDepthExceeded>(
            ErrorOf("Apply(g, x) = g(x)\nF(x) = Apply(F, x)\nF(1)", Depth(16)));

    // ── Depth: recursion through builtin arguments ───────────────────────────
    //
    // A zero-parameter property that reaches itself through a builtin ARGUMENT or
    // RECEIVER re-enters its body outside every call chokepoint. Before the
    // depth-charged argument-evaluation chokepoint
    // (EvaluationBudget.TryEnterArgumentEvaluation), the plain-call spellings below
    // terminated the whole process with an uncatchable StackOverflowException — the
    // one failure mode no in-process assertion can observe, which is why
    // EvaluationLimitsProcessTests re-proves the worst spellings in a subprocess.

    [Theory]
    [InlineData("A = count(A)\nA")]
    [InlineData("A = A.count\nA")]
    [InlineData("A = range(1, A)\nA.count")]
    [InlineData("A = if(true, A, 0)\nA")]
    [InlineData("A = if(A, 1, 0)\nA")]
    [InlineData("A = take([1, 2, 3], A)\nA")]
    [InlineData("A = [1, 2].take(A)\nA")]
    [InlineData("A = sum([A])\nA")]
    [InlineData("Add(a, b) = a + b\nA = [1, 2].reduce(Add, A)\nA")]
    [InlineData("Step = x, false\nA = Step.while(A)\nA")]
    [InlineData("Inc = x + 1\nA = Inc.repeat(A, 0)\nA")]
    [InlineData("A = B.count\nB = A.count\nA")]
    public void BuiltinArgumentRecursion_ReturnsAStructuredResourceError(string source)
    {
        // The deterministic depth limit is the primary guard; the machine-dependent
        // stack backstop remains acceptable for the spellings whose per-level frame
        // cost trips the probe first. Any other outcome — a wrong value, a
        // non-resource error, or a crash — is the regression.
        foreach (var error in new[]
        {
            Eval(source).Error,
            Evaluator.RunCounted(
                new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root),
                UncachedZeroArgPropertyResultCache.Instance,
                limits: null).Error,
        })
        {
            Assert.True(
                error is EvalError.EvaluationDepthExceeded or EvalError.EvaluationStackExhausted,
                $"expected a structured resource error for `{source.Replace("\n", " ; ")}`, got {error}");
        }

        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        Assert.Single(failure.Errors);
    }

    // ── Failing recursion stays linear in depth ──────────────────────────────

    [Theory]
    [InlineData("f(x) = f(x)\nf(1)")]
    [InlineData("f(x) = f(x) + f(x)\nf(1)")]
    [InlineData("f(x) = f(f(x))\nf(1)")]
    public void FailingRecursion_ConsumesWorkLinearInDepth(string source)
    {
        // Every failing shape charges exactly MaxDepth + 1 steps: one per entered
        // level plus the rejected attempt. The budget of 3x MaxDepth therefore
        // leaves the DEPTH error as the observed kind; a mutation that swallows a
        // limit error and retries the child on a second channel squares the work,
        // trips the step budget first, and flips the asserted kind.
        var error = ErrorOf(source, new EvaluationLimits { MaxDepth = 24, MaxSteps = 72 });
        Assert.IsType<EvalError.EvaluationDepthExceeded>(error);
    }

    [Fact]
    public void FailingBuiltinArgumentRecursion_ConsumesWorkLinearInDepth()
    {
        // The builtin-argument twin, indirected through a charged user call so the
        // step budget observes each level. The reduce initial accumulator once
        // retried a depth-failed eager argument evaluation through the algorithm
        // channel (2^depth work); the resource-limit error then became sticky
        // (PrepareSequenceBuiltinSuffixArg), was made terminal at the eager attempt
        // itself (BuildCallableCallItems, RESOURCE LIMITS ARE TERMINAL, Q-02), and
        // `initial` is now an ordinary VALUE slot demanded once, whatever its failure
        // (PV-05), so the run stays linear and the depth kind wins under a linear step
        // budget.
        var error = ErrorOf(
            "Add(a, b) = a + b\nG(x) = A\nA = [1, 2].reduce(Add, G(1))\nA",
            new EvaluationLimits { MaxDepth = 24, MaxSteps = 96 });
        Assert.IsType<EvalError.EvaluationDepthExceeded>(error);
    }

    [Theory]
    [InlineData("F(v) = v\nx = F(x)\nx")]
    [InlineData("F(v) = v*\nx = F(x)\nx")]
    public void AlgEnvThunkRecursion_IsDepthBoundedAndConsumesLinearWork(string source)
    {
        // The ordinary F body reaches EvalCounted(Param); the spread body reaches the
        // plain Eval(Param) twin while evaluating the spread operand. x's argument slot
        // is x itself, so every level re-enters it until MaxDepth; the refusal is
        // terminal at the innermost slot's assembly (RESOURCE LIMITS ARE TERMINAL, Q-02 —
        // it was once retained for an algorithm-channel fallback, which is why every
        // zero-parameter AlgEnv re-entry must consume depth: the retries grew
        // exponentially), so the work stays linear.
        const int maxDepth = 24;
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var (result, budget) = Evaluator.RunCountedObserved(
            expr,
            new EvaluationLimits { MaxDepth = maxDepth });

        Assert.True(result.IsError);
        Assert.Equal(
            maxDepth,
            Assert.IsType<EvalError.EvaluationDepthExceeded>(result.Error).Limit);
        Assert.Equal(maxDepth, budget.PeakDepth);
        Assert.True(
            budget.ConsumedSteps <= 2L * maxDepth,
            $"expected work linear in MaxDepth, observed {budget.ConsumedSteps} steps at depth {maxDepth}");
    }

    [Fact]
    public void UnusedSelfReferentialArgument_ReachesNoLimit()
    {
        var expression = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(
            "F(v) = 0\nx = F(x)\nx").Root);
        var (result, budget) = Evaluator.RunCountedObserved(expression,
            new EvaluationLimits { MaxDepth = 24 });
        Assert.False(result.IsError);
        Assert.Equal([0m], result.Value.Value.ToAtoms());
        Assert.Equal(2, budget.PeakDepth);
        Assert.Equal(2, budget.ConsumedSteps);
    }

    [Theory]
    [InlineData("F(v) = v.string\nx = F(x)\nx")]
    [InlineData("F(v) = v.string*\nx = F(x)\nx")]
    public void DotStringAlgEnvRecursion_IsDepthBoundedAndConsumesLinearWork(string source)
    {
        // The ordinary-dot `string` intrinsic evaluates an algorithm-resolving
        // receiver for its value, so an AlgEnv-bound Param receiver is the same
        // demand funnel as a bare `v`: a resource-limit error must never be retried
        // through the receiver (a depth charge alone leaves the retry tree exponential)
        // — it is terminal at the slot that reached it (RESOURCE LIMITS ARE TERMINAL,
        // Q-02). The plain body reaches the counted dot-call twin; the spread body
        // reaches the plain twin through the spread operand.
        const int maxDepth = 24;
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var (result, budget) = Evaluator.RunCountedObserved(
            expr,
            new EvaluationLimits { MaxDepth = maxDepth });

        Assert.True(result.IsError);
        Assert.Equal(
            maxDepth,
            Assert.IsType<EvalError.EvaluationDepthExceeded>(result.Error).Limit);
        Assert.Equal(maxDepth, budget.PeakDepth);
        Assert.True(
            budget.ConsumedSteps <= 2L * maxDepth,
            $"expected work linear in MaxDepth, observed {budget.ConsumedSteps} steps at depth {maxDepth}");
    }

    [Theory]
    [InlineData("A = A.string\nA")]
    [InlineData("A = { A.string* }\nA")]
    public void DotStringLexicalSelfRecursion_TerminatesWithStructuredDepthError(string source)
    {
        // A name-resolved `.string` receiver re-enters the named algorithm's body
        // with no dynamic-invocation chokepoint on the path, so the receiver
        // evaluation must consume depth: uncharged, these shapes recursed outside
        // every budget and terminated the process with an uncatchable
        // StackOverflowException. The zero-parameter receiver forms exercise the
        // funnel (a parameterized receiver never reaches it — see
        // DotStringParameterizedLexicalReceiver_IsRejectedBeforeReentry); the
        // spread body reaches the plain twin.
        const int maxDepth = 24;
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var (result, budget) = Evaluator.RunCountedObserved(
            expr,
            new EvaluationLimits { MaxDepth = maxDepth });

        Assert.True(result.IsError);
        Assert.Equal(
            maxDepth,
            Assert.IsType<EvalError.EvaluationDepthExceeded>(result.Error).Limit);
        Assert.Equal(maxDepth, budget.PeakDepth);
        Assert.True(
            budget.ConsumedSteps <= 2L * maxDepth,
            $"expected work linear in MaxDepth, observed {budget.ConsumedSteps} steps at depth {maxDepth}");
    }

    [Fact]
    public void DotStringParameterizedLexicalReceiver_IsRejectedBeforeReentry()
    {
        // A `.string` receiver that is a zero-argument value demand of a PARAMETERIZED
        // algorithm nothing forwards to (A's closed list has no `n` for B) is rejected by
        // the ONE zero-argument demand law at the demand boundary: the ordinary property
        // arity error, no re-entry, and the only depth consumed is the invocation of A(1).
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid("B(n) = n\nA(m) = B.string\nA(1)").Root);
        var (result, budget) = Evaluator.RunCountedObserved(
            expr,
            new EvaluationLimits { MaxDepth = 24 });

        Assert.True(result.IsError);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
        Assert.Equal(1, arity.Expected);
        Assert.Equal(0, arity.Actual);
        Assert.Equal(1, budget.PeakDepth);
    }

    [Fact]
    public void DotStringParameterizedSelfReceiver_IsTheChargedRecursiveCall()
    {
        // `.string` converts its receiver's VALUE, so under the unified formula-lifting law a
        // parameterized receiver lifts like an operand: `A(n) = A.string` is
        // `A(n) = A(n).string`, the same unbounded recursion as `A(n) = A + 1`. Every level is
        // an ordinary charged invocation, so it stops at the depth limit with the structured
        // error and work linear in the limit.
        const int maxDepth = 24;
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid("A(n) = A.string\nA(1)").Root);
        var (result, budget) = Evaluator.RunCountedObserved(
            expr,
            new EvaluationLimits { MaxDepth = maxDepth });

        Assert.True(result.IsError);
        Assert.Equal(maxDepth, Assert.IsType<EvalError.EvaluationDepthExceeded>(result.Error).Limit);
        Assert.Equal(maxDepth, budget.PeakDepth);
        Assert.True(
            budget.ConsumedSteps <= 2L * maxDepth,
            $"expected work linear in MaxDepth, observed {budget.ConsumedSteps} steps at depth {maxDepth}");
    }

    [Theory]
    [InlineData("F(v) = v.string\nF({1 / 0})")]
    [InlineData("F(v) = { v.string* }\nF({1 / 0})")]
    public void DotStringFailedParamDemand_ReusesTheSlotFailure_WithoutReentry(string source)
    {
        // AT-MOST-ONCE ARGUMENT VALUE EVALUATION (Q-01): the brace argument has an algorithm
        // channel, and its one value evaluation fails with a NON-resource semantic error at
        // assembly. That failure is the parameter's value outcome, so the Param receiver's
        // `.string` demand reports it WITHOUT re-entering the brace body: the only depth is
        // F's own invocation, and even MaxDepth = 1 still reports the division error. (Before
        // Q-01 the demand re-entered the body through a depth-only funnel: PeakDepth 2, and
        // MaxDepth = 1 reported the depth limit.) The spread spelling reaches the plain
        // dot-call twin; the other spelling reaches the counted twin.
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

        var (demanded, budget) = Evaluator.RunCountedObserved(
            expr,
            new EvaluationLimits { MaxDepth = 1 });
        Assert.True(demanded.IsError);
        Assert.IsType<EvalError.DivByZero>(Innermost(demanded.Error));
        Assert.Equal(1, budget.PeakDepth);
        Assert.Equal(1, budget.ConsumedSteps);
    }

    [Theory]
    [InlineData("Bad = 1 / 0\nG(w) = w\nF(v) = G(v)\nF(Bad)")]
    [InlineData("Bad = 1 / 0\nG(w) = w*\nF(v) = G(v)\nF(Bad)")]
    public void FailedArgumentForwardedThroughAParameter_IsNeverReentered(string source)
    {
        // The failing property argument is evaluated ONCE, as F's slot (the property access
        // at depth 2). Forwarding `v` into G's slot and reading `w` reuse that recorded
        // failure — neither re-enters Bad's body — so the profile is F's invocation (depth 1),
        // the one property access and G's invocation (both at depth 2): exactly three steps
        // and no deeper entry. (Before Q-01 the forwarded demand re-evaluated the thunk at
        // depth 3.)
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

        var (demanded, budget) = Evaluator.RunCountedObserved(
            expr,
            new EvaluationLimits { MaxDepth = 3 });
        Assert.True(demanded.IsError);
        Assert.IsType<EvalError.DivByZero>(Innermost(demanded.Error));
        Assert.Equal(3, budget.PeakDepth);
        Assert.Equal(3, budget.ConsumedSteps);
    }

    [Fact]
    public void FailedArgumentForwardedToSeveralRows_IsNeverReentered()
    {
        // Each of the three G(v) rows forwards the parameter whose slot failed; each reads the
        // recorded failure (G ignores it), so no row re-enters Bad's body: the depth stays at
        // the one-call profile and the steps are F, the one property access, and three G calls.
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(
            "Bad = 1 / 0\nG(w) = 0\nF(v) = G(v), G(v), G(v)\nF(Bad)").Root);
        var (result, budget) = Evaluator.RunCountedObserved(
            expr,
            new EvaluationLimits { MaxDepth = 24 });

        Assert.False(result.IsError);
        Assert.Equal(2, budget.PeakDepth);
        Assert.Equal(4, budget.ConsumedSteps);
    }

    [Theory]
    [InlineData("Double(n) = n * 2\nApply(f, x) = f(x)\nApply(Double, 3)", "6")]
    [InlineData("Bad = 1 / 0\nUse(f, x) = x\nUse(Bad, 3)", "3")]
    [InlineData("Bad = 1 / 0\nG(w) = 5\nF(v) = G(v)\nF(Bad)", "5")]
    public void DualChannelFallback_PreservedUnderDemandDepthAccounting(string source, string expected)
    {
        // Higher-order dispatch, an unused argument whose ORDINARY failure is retained beside
        // its algorithm channel, and that failure forwarded through an intermediate callee
        // keep their pre-accounting results.
        var result = Evaluator.RunFlat(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        Assert.False(result.IsError);
        Assert.Equal([decimal.Parse(expected, System.Globalization.CultureInfo.InvariantCulture)], result.Value);
    }

    [Theory]
    [InlineData("Big = range(1, 200000)\nUse(f, x) = x\nUse(Big, 3)", typeof(EvalError.CollectionSizeLimitExceeded))]
    [InlineData("Deep = Deep\nUse(f, x) = x\nUse(Deep, 3)", typeof(EvalError.EvaluationDepthExceeded))]
    [InlineData("Deep = Deep\nG(w) = 5\nF(v) = G(v)\nF(Deep)", typeof(EvalError.EvaluationDepthExceeded))]
    public void UnusedResourceFailingArgument_NeverReachesTheLimit(string source, Type expected)
    {
        // RESOURCE LIMITS ARE TERMINAL (Q-02 / PV-06): these arguments ARE evaluated at
        // assembly (CALL-02) and reach the per-collection ceiling or the depth limit. The
        // limit used to be retained beside the unused parameter's algorithm channel — and
        // forwarded "stickily" through an intermediate callee — so the run succeeded with 3
        // and 5 after partial evaluation. It now ends the run, whether or not anything reads
        // the parameter.
        var result = Evaluator.RunFlat(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        Assert.False(result.IsError);
        Assert.Equal([source.Contains("G(w)", StringComparison.Ordinal) ? 5m : 3m], result.Value);
        Assert.True(typeof(EvalError).IsAssignableFrom(expected));
    }

    private static EvalError Innermost(EvalError error)
        => error is EvalError.WithContext(_, var inner) ? Innermost(inner) : error;

    [Fact]
    public void UnusedResolveArgument_WithAnOrdinaryFailure_StaysLatentAndCheap()
    {
        // F never demands its parameter, so its supplied computation `Bad` is never
        // evaluated and the call succeeds (Model C, NEED-01/03; CALL-02, CALL-06). (Until
        // Model C the argument WAS evaluated, once, at assembly, and only its failure stayed
        // latent, retained beside its algorithm channel.)
        var result = Evaluator.RunFlat(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid("Bad = 1 / 0\nF(v) = 0\nF(Bad)").Root),
            new EvaluationLimits { MaxDepth = 24, MaxSteps = 72 });
        Assert.False(result.IsError);
        Assert.Equal([0m], result.Value);
    }

    [Fact]
    public void UnusedSelfReferentialResolveArgument_DoesNotRecurse()
    {
        // The same shape whose argument would recurse into itself: F never demands it, so
        // the supplied computation `A` is never evaluated, nothing recurses, no limit is
        // reached, and the run returns 0 (Model C, NEED-01/03). (Before Model C each level's
        // slot evaluated A again at assembly until MaxDepth refused it — first absorbed, and
        // from the Q-02 decision of 2026-09-28 terminal; this comment described that until
        // 2026-10-09.)
        var result = Evaluator.RunFlat(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid("F(v) = 0\nA = F(A)\nA").Root),
            new EvaluationLimits { MaxDepth = 24, MaxSteps = 72 });
        Assert.False(result.IsError);
        Assert.Equal([0m], result.Value);
    }

    // ── Budget unit invariants ───────────────────────────────────────────────

    [Fact]
    public void TryEnterInvocation_RejectedAttempt_LeavesDepthUnchanged()
    {
        // The doc contract: a failed enter is never counted as entered. Entering
        // twice at MaxDepth = 2 fills the budget, the third attempt fails, and one
        // exit must make room for exactly one more successful enter.
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 2 });
        Assert.Null(budget.TryEnterInvocation());
        Assert.Null(budget.TryEnterInvocation());
        Assert.IsType<EvalError.EvaluationDepthExceeded>(budget.TryEnterInvocation());
        budget.ExitInvocation();
        Assert.IsType<EvalError.EvaluationDepthExceeded>(budget.TryEnterInvocation());
        Assert.Equal(2, budget.PeakDepth);
    }

    [Fact]
    public void TryEnterArgumentEvaluation_SharesTheDepthBudget_AndChargesNoStep()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 2, MaxSteps = 5 });
        Assert.Null(budget.TryEnterArgumentEvaluation());
        Assert.Null(budget.TryEnterInvocation());
        Assert.IsType<EvalError.EvaluationDepthExceeded>(budget.TryEnterArgumentEvaluation());
        budget.ExitInvocation();
        Assert.IsType<EvalError.EvaluationDepthExceeded>(budget.TryEnterArgumentEvaluation());
        Assert.Equal(2, budget.PeakDepth);

        // Exactly one step was charged across all of the above — by the one
        // successful TryEnterInvocation; argument-evaluation entries are step-free.
        Assert.Equal(1L, budget.ConsumedSteps);
    }

    // ── Error shape: span, context, display ──────────────────────────────────

    [Fact]
    public void DepthError_CarriesSourceSpan()
        => Assert.NotNull(ErrorOf($"{CountDown}f(50)", Depth(8)).Span);

    [Fact]
    public void DepthError_IsNotBuriedUnderOneContextFramePerActiveCall()
    {
        // A depth failure is a property of the RUN, not of any one call on the chain:
        // accumulating one "while evaluating call to f" frame per active invocation
        // would produce hundreds of identical lines that say nothing extra.
        var error = ErrorOf($"{CountDown}f(50)", Depth(8));
        Assert.IsType<EvalError.EvaluationDepthExceeded>(error);
    }

    [Fact]
    public void DepthError_PublicDisplayIsStableAndSingleLine()
    {
        var display = KatLangEngine.Run($"{CountDown}f(50)", new RunOptions { EvaluationLimits = Depth(8) })
            .ToDisplayString();
        Assert.Equal("[2:10] Evaluation recursion limit of 8 was exceeded", display);
    }

    [Fact]
    public void StepLimitError_PublicDisplayIsStable()
    {
        var display = Run("Step = x, true\nStep.while(0)", Steps(25)).ToDisplayString();
        Assert.Contains("Evaluation step limit of 25 was exceeded", display);
    }

    // ── Engine surface consistency ───────────────────────────────────────────

    [Fact]
    public void EngineRun_AppliesConfiguredDepthLimit()
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(Run($"{CountDown}f(40)", Depth(8)));
        Assert.Contains("recursion limit of 8", failure.Errors[0].Message);
    }

    [Fact]
    public void EvaluateToAtoms_AppliesConfiguredDepthLimit()
    {
        var ex = Assert.Throws<KatLangException>(
            () => KatLangEngine.EvaluateToAtoms($"{CountDown}f(40)", new RunOptions { EvaluationLimits = Depth(8) }));
        Assert.Contains("recursion limit of 8", ex.Errors[0].Message);
    }

    [Fact]
    public void PlainAndCountedEvaluators_AgreeOnLimitOutcome()
    {
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid($"{CountDown}f(40)").Root);
        var plain = Evaluator.Run(expr, Depth(8));
        var counted = Evaluator.RunCounted(expr, UncachedZeroArgPropertyResultCache.Instance, Depth(8));
        Assert.IsType<EvalError.EvaluationDepthExceeded>(plain.Error);
        Assert.IsType<EvalError.EvaluationDepthExceeded>(counted.Error);
    }

    [Fact]
    public void RunFlat_AppliesConfiguredDepthLimit()
        => Assert.IsType<EvalError.EvaluationDepthExceeded>(
            Evaluator.RunFlat(new Expr.AlgorithmExpr(SourceProvenance.ParseValid($"{CountDown}f(40)").Root), Depth(8)).Error);

    [Fact]
    public void LowLevelEvaluatorDefaults_AreBoundedNotUnlimited()
    {
        // The parameterless public overloads must not be an unguarded back door.
        Assert.True(Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid("f(x) = f(x)\nf(1)").Root)).IsError);
        Assert.True(Evaluator.RunFlat(new Expr.AlgorithmExpr(SourceProvenance.ParseValid("f(x) = f(x)\nf(1)").Root)).IsError);
    }

    // ── Entry-point x configuration depth matrix ─────────────────────────────
    //
    // The SAME recursive family must reach the SAME verdict through every public and
    // internal evaluator entry point, for every way of expressing the same effective
    // limit. `f(k)` needs k + 1 nested invocations, so an effective depth of d admits
    // exactly f(d - 1) and rejects f(d). Default limits, an explicit limit equal to the
    // ceiling, and any limit above the ceiling must all behave identically.

    /// <summary>Every entry point, reduced to "did this program complete?".</summary>
    private static IReadOnlyList<(string Entry, bool Completed)> AllEntryPoints(string source, EvaluationLimits? limits)
    {
        var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var options = new RunOptions { EvaluationLimits = limits };

        bool atomsCompleted;
        try
        {
            _ = KatLangEngine.EvaluateToAtoms(source, options);
            atomsCompleted = true;
        }
        catch (KatLangException)
        {
            atomsCompleted = false;
        }

        return
        [
            ("Evaluator.Run", !Evaluator.Run(expr, limits).IsError),
            ("Evaluator.RunCounted", !Evaluator.RunCounted(expr, UncachedZeroArgPropertyResultCache.Instance, limits).IsError),
            ("Evaluator.RunCountedWithTopLevelProperty",
                !Evaluator.RunCountedWithTopLevelProperty(expr, "DisplayDecimals", UncachedZeroArgPropertyResultCache.Instance, limits).IsError),
            ("KatLangEngine.Run", KatLangEngine.Run(source, options) is RunResult.Success),
            ("KatLangEngine.EvaluateToAtoms", atomsCompleted),
        ];
    }

    private static void AssertAllEntryPoints(string source, EvaluationLimits? limits, bool expectCompleted)
    {
        foreach (var (entry, completed) in AllEntryPoints(source, limits))
        {
            Assert.True(
                completed == expectCompleted,
                $"{entry}: expected completed={expectCompleted} but got {completed} for `{source.Replace("\n", " ; ")}`.");
        }
    }

    public static TheoryData<int?> EquivalentCeilingConfigurations => new()
    {
        null,                                        // default limits
        EvaluationLimits.MaxSupportedDepth,          // explicitly at the ceiling
        int.MaxValue,                                // above the ceiling: clamped down
    };

    [Theory]
    [MemberData(nameof(EquivalentCeilingConfigurations))]
    public void CeilingEquivalentConfigurations_AdmitExactlyOneLessThanTheCeiling(int? maxDepth)
    {
        var limits = maxDepth is { } d ? new EvaluationLimits { MaxDepth = d } : null;
        AssertAllEntryPoints($"{CountDown}f({EvaluationLimits.MaxSupportedDepth - 1})", limits, expectCompleted: true);
        AssertAllEntryPoints($"{CountDown}f({EvaluationLimits.MaxSupportedDepth})", limits, expectCompleted: false);
    }

    [Theory]
    [MemberData(nameof(EquivalentCeilingConfigurations))]
    public void OriginalReproducer_IsRejectedByEveryDefaultPath(int? maxDepth)
    {
        // f(223) was the Phase-4 process-termination reproducer. Under the calibrated
        // ceiling of 128 it needs 224 nested invocations, so it is REJECTED — it does not
        // succeed on any default path. (The Phase-5 report's "f(223) succeeds" line was
        // stale text from the earlier 256 calibration and is corrected here.)
        var limits = maxDepth is { } d ? new EvaluationLimits { MaxDepth = d } : null;
        AssertAllEntryPoints($"{CountDown}f(223)", limits, expectCompleted: false);
    }

    [Fact]
    public void ConfiguredLowerLimit_AdmitsExactlyOneLessThanItself()
    {
        AssertAllEntryPoints($"{CountDown}f(63)", Depth(64), expectCompleted: true);
        AssertAllEntryPoints($"{CountDown}f(64)", Depth(64), expectCompleted: false);
    }

    [Fact]
    public void ConfiguredLimitCannotRaiseTheCeiling()
    {
        // A request above MaxSupportedDepth is clamped, never honoured.
        AssertAllEntryPoints($"{CountDown}f(200)", new EvaluationLimits { MaxDepth = 100_000 }, expectCompleted: false);
    }

    // ── Run-scoped state isolation ───────────────────────────────────────────

    [Fact]
    public void RepeatedRuns_SharingOneOptionsInstance_EachStartFresh()
    {
        var options = new RunOptions { EvaluationLimits = Steps(200) };
        var first = KatLangEngine.Run($"{CountDown}f(20)", options).ToDisplayString();
        for (var i = 0; i < 5; i++)
            Assert.Equal(first, KatLangEngine.Run($"{CountDown}f(20)", options).ToDisplayString());
    }

    [Fact]
    public void FailedRun_DoesNotAffectTheNextRun_AbaDeterminism()
    {
        var options = new RunOptions { EvaluationLimits = Steps(60) };
        var a1 = KatLangEngine.Run($"{CountDown}f(10)", options).ToDisplayString();
        var b = KatLangEngine.Run($"{CountDown}f(10000)", options).ToDisplayString();
        var a2 = KatLangEngine.Run($"{CountDown}f(10)", options).ToDisplayString();

        Assert.Equal("0", a1);
        Assert.Equal(a1, a2);
        Assert.Contains("step limit", b);
    }

    [Fact]
    public void ConcurrentRuns_SharingOneOptionsInstance_DoNotShareCounters()
    {
        var options = new RunOptions { EvaluationLimits = Steps(200) };
        var results = new string[32];
        Parallel.For(0, results.Length, i => results[i] = KatLangEngine.Run($"{CountDown}f(20)", options).ToDisplayString());
        Assert.All(results, r => Assert.Equal("0", r));
    }

    // ── Step budget ──────────────────────────────────────────────────────────

    [Fact]
    public void StepBudget_ExactBoundary_Succeeds()
    {
        // f(3) charges one step per invocation: f(3), f(2), f(1), f(0).
        Assert.False(Eval($"{CountDown}f(3)", Steps(4)).IsError);
    }

    [Fact]
    public void StepBudget_OneStepShort_ReturnsStepLimitError()
    {
        var error = ErrorOf($"{CountDown}f(3)", Steps(3));
        Assert.Equal(3L, Assert.IsType<EvalError.EvaluationStepLimitExceeded>(error).Limit);
    }

    [Fact]
    public void StepBudget_OfOne_FailsDeterministically()
        => Assert.IsType<EvalError.EvaluationStepLimitExceeded>(ErrorOf($"{CountDown}f(3)", Steps(1)));

    [Fact]
    public void StepBudget_ProgramWithNoInvocations_NeedsNoSteps()
        => Assert.False(Eval("1 + 2 * 3", Steps(1)).IsError);

    [Fact]
    public void InfiniteWhile_TerminatesWithStepLimitError()
        => Assert.IsType<EvalError.EvaluationStepLimitExceeded>(
            ErrorOf("Step = x, true\nStep.while(0)", Steps(500)));

    [Fact]
    public void FiniteWhile_WithSufficientBudget_Succeeds()
    {
        var result = Eval("Step = x - 1, x > 1\nStep.while(200)", Steps(10_000));
        Assert.False(result.IsError);
    }

    [Fact]
    public void Repeat_ChargesOneStepPerIteration()
    {
        // 100 iterations plus the `Inc` step invocations must not fit in 100 steps,
        // and comfortably fit in 10_000.
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(ErrorOf("Inc = x + 1\nInc.repeat(100, 0)", Steps(50)));
        Assert.False(Eval("Inc = x + 1\nInc.repeat(100, 0)", Steps(10_000)).IsError);
    }

    [Fact]
    public void LoopWithCallback_IsCharged()
        => Assert.IsType<EvalError.EvaluationStepLimitExceeded>(
            ErrorOf("G(y) = y + 1\nInc = G(x)\nInc.repeat(1000, 0)", Steps(200)));

    [Fact]
    public void CollectionCallbackPipeline_IsCharged()
        => Assert.IsType<EvalError.EvaluationStepLimitExceeded>(
            ErrorOf("F(x) = x + 1\nrange(1, 1000).map(F).count", Steps(100)));

    [Fact]
    public void ReduceCallback_IsCharged()
        => Assert.IsType<EvalError.EvaluationStepLimitExceeded>(
            ErrorOf("Add(a, b) = a + b\nrange(1, 1000).reduce(Add, 0)", Steps(100)));

    [Fact]
    public void CachedProperty_ChargesTheAccessButNotTheCachedComputation()
    {
        // `Slow` is evaluated once and then served from the zero-argument property
        // cache: eight reads cost eight access steps plus one evaluation, not eight
        // evaluations. A budget that only fits the cached shape proves the difference.
        const string source = "Slow = 1 + 1\nSlow + Slow + Slow + Slow + Slow + Slow + Slow + Slow";
        Assert.False(Eval(source, Steps(16)).IsError);
    }

    [Fact]
    public void PropertyEvaluationThatReachesTheBudget_IsNotCachedAsSuccess()
    {
        var error = ErrorOf("A = A\nA", Steps(6));
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(error);
    }

    [Fact]
    public void NoStepBudgetByDefault_LongLoopStillRuns()
    {
        // The documented default is depth-bounded but work-unbounded, so existing
        // long-running programs keep working with no options supplied.
        var result = KatLangEngine.Run("Inc = x + 1\nInc.repeat(50000, 0)");
        Assert.Equal("50000", Assert.IsType<RunResult.Success>(result).ToDisplayString());
    }

    // ── Bulk expression-node work is bounded by the step budget ──────────────

    /// <summary>16 levels of `e = e + e` over ONE shared reference: 17 node objects, 2^17 node evaluations.</summary>
    private static Expr SharedBinaryDag(int levels)
    {
        Expr e = new Expr.Num(1);
        for (var i = 0; i < levels; i++)
            e = new Expr.Binary(BinaryOp.Add, e, e);
        return e;
    }

    [Fact]
    public void SharedExpressionDag_IsBoundedByAConfiguredStepBudget()
    {
        // The preflight accepts reference-shared acyclic subtrees (visited once, so
        // the CHECK is linear), but evaluation re-walks every occurrence: 17 shared
        // Binary nodes demand 2^17 node evaluations while charging no invocation,
        // depth, or materialization. Expression-node work is now charged in bulk
        // (one step per 4096 evaluator work checkpoints), so the ONE budget documented to stop excessive
        // computation actually stops it — previously this exact run succeeded after
        // millions of operations with MaxSteps = 1 configured.
        var bounded = Evaluator.Run(SharedBinaryDag(16), new EvaluationLimits { MaxDepth = 1, MaxSteps = 1 });
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(bounded.Error);
    }

    [Fact]
    public void SharedExpressionDag_WithinAGenerousStepBudget_StillEvaluates()
    {
        // 2^17 node evaluations plus the spine-machine transitions cost far fewer
        // than 10_000 bulk steps, and the value is exact.
        var result = Evaluator.RunFlat(SharedBinaryDag(16), new EvaluationLimits { MaxSteps = 10_000 });
        Assert.False(result.IsError);
        Assert.Equal([65536m], result.Value);

        // Without a configured step budget the run stays in the documented
        // unbudgeted-compute class and completes.
        var unbudgeted = Evaluator.RunFlat(SharedBinaryDag(16));
        Assert.False(unbudgeted.IsError);
        Assert.Equal([65536m], unbudgeted.Value);
    }

    [Fact]
    public void OrdinaryPrograms_ChargeNoBulkExpressionSteps()
    {
        // The 4096-checkpoint granularity exists so small ordinary programs keep
        // their exact step accounting, including this no-invocation control.
        Assert.False(Eval("1 + 2 * 3 - 4", Steps(1)).IsError);
    }

    // ── Optimizer independence ───────────────────────────────────────────────

    [Fact]
    public void StepBudget_KeepsOptimizedPaths_AndChargingIsOptimizerIndependent()
    {
        // Limits observe a run; they never choose how it runs (Q-09b): a budgeted run keeps
        // the planned loop, which charges exactly the generic loop's steps, so the charged
        // count cannot depend on whether an optimization applied to this shape. (Until
        // 2026-10-04 a configured step budget forced the generic paths instead — PV-07.)
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid("Inc = x + 1\nInc.repeat(500, 0)").Root);
        var loops = new LoopOptimizationDiagnostics();
        var (budgeted, budgetedBudget) = Evaluator.RunCountedObserved(program, Steps(100_000), loopDiagnostics: loops);
        var (generic, genericBudget) = Evaluator.RunCountedObserved(program, enableOptimizations: false);

        Assert.False(budgeted.IsError);
        Assert.False(generic.IsError);
        Assert.Equal(1, loops.OptimizedLoopHits);
        Assert.Equal(generic.Value.Value, budgeted.Value.Value, Result.ValueComparer);
        Assert.Equal(genericBudget.ConsumedSteps, budgetedBudget.ConsumedSteps);
        Assert.Equal(genericBudget.ConsumedExpressionCheckpoints, budgetedBudget.ConsumedExpressionCheckpoints);
    }

    [Theory]
    [InlineData("Inc = x + 1\nInc.repeat(200, 0)")]
    [InlineData("Step = x - 1, x > 1\nStep.while(200)")]
    [InlineData("F(x) = x * 2\nrange(1, 50).map(F).sum")]
    [InlineData("range(1, 50).filter(IsBig).count\nIsBig(x) = x > 10")]
    public void BudgetedAndUnbudgetedRuns_ProduceTheSameValue(string source)
    {
        var unbudgeted = Eval(source);
        var budgeted = Eval(source, Steps(1_000_000));

        Assert.False(unbudgeted.IsError);
        Assert.False(budgeted.IsError);
        Assert.Equal(unbudgeted.Value, budgeted.Value, Result.ValueComparer);
    }

    // ── In-budget programs are untouched ─────────────────────────────────────

    [Theory]
    [InlineData("1 + 2", "3")]
    [InlineData("f(0) = 1\nf(n) = n * f(n - 1)\nf(10)", "3628800")]
    [InlineData("range(1, 10).sum", "55")]
    [InlineData("A = 7\nA + A", "14")]
    public void InBudgetPrograms_AreUnaffectedByLimits(string source, string expected)
    {
        Assert.Equal(expected, KatLangEngine.Run(source).ToDisplayString());
        Assert.Equal(expected, Run(source, Depth(64)).ToDisplayString());
        Assert.Equal(expected, Run(source, Steps(100_000)).ToDisplayString());
    }
}
