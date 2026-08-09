using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

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
        Assert.False(EvaluationBudget.Create(null).HasStepLimit);
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
        var display = Run("Step = x, 1\nStep.while(0)", Steps(25)).ToDisplayString();
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
    public void EvaluateToString_AppliesConfiguredDepthLimit()
        => Assert.Contains(
            "recursion limit of 8",
            KatLangEngine.EvaluateToString($"{CountDown}f(40)", new RunOptions { EvaluationLimits = Depth(8) }));

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
            ("KatLangEngine.EvaluateToString", !KatLangEngine.EvaluateToString(source, options).Contains("limit")),
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
            ErrorOf("Step = x, 1\nStep.while(0)", Steps(500)));

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

    // ── Optimizer independence ───────────────────────────────────────────────

    [Fact]
    public void StepBudget_DisablesOptimizedPaths_SoChargingIsOptimizerIndependent()
    {
        // A budgeted run always takes the generic loop/pipeline paths, so the charged
        // count cannot depend on whether an optimization applied to this shape.
        var budgeted = Eval("Inc = x + 1\nInc.repeat(500, 0)", Steps(100_000));
        var generic = Evaluator.Run(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid("Inc = x + 1\nInc.repeat(500, 0)").Root),
            UncachedZeroArgPropertyResultCache.Instance,
            enableLoopOptimization: false);

        Assert.False(budgeted.IsError);
        Assert.False(generic.IsError);
        Assert.Equal(generic.Value, budgeted.Value, Result.ValueComparer);
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
