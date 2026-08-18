using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

/// <summary>
/// Conservation of the evaluator's SCOPED resource protocol under every exit path.
///
/// <para>Dynamic depth is the evaluator's only balanced (enter/leave) budget:
/// <see cref="EvaluationBudget.TryEnterInvocation"/> and
/// <see cref="EvaluationBudget.TryEnterArgumentEvaluation"/> admit one level, and
/// <see cref="EvaluationBudget.ExitInvocation"/> releases it. Everything else the budget
/// tracks — steps, materialized item slots, materialized string units — is CUMULATIVE:
/// work already performed stays charged within its run and is never refunded, so those
/// counters are checked here only for the things a balanced protocol must still promise
/// (a rejected enter reserves nothing, and no counter crosses into a later run).</para>
///
/// <para>Two invariants are pinned for every admitted level:</para>
/// <list type="number">
/// <item>A REJECTED enter is non-mutating — no depth, no peak, no reservation.</item>
/// <item>An ADMITTED level is released exactly once on every exit path: success,
/// structured <see cref="EvalError"/>, a nested budget failure, an exceptional unwind,
/// and <see cref="OperationCanceledException"/>.</item>
/// </list>
///
/// <para><b>How faults get inside a charged region.</b> Evaluation takes no host callback,
/// so ordinary source cannot make the CLR throw inside an entered region. The injection
/// seam is <see cref="IZeroArgPropertyResultCache"/>, which the evaluator consults from
/// <c>GetOrEvaluateZeroArgPropertyResultCore</c> — i.e. inside the <c>try</c> of a
/// SUCCESSFUL <see cref="EvaluationBudget.TryEnterInvocation"/>, and once per nesting level
/// of a property chain. A cache that throws at the k-th access therefore faults inside k
/// live charged regions, unwinding through the real production <c>finally</c> blocks. The
/// same seam hands the test the run's live <see cref="EvaluationBudget"/> (the cache key's
/// run identity IS the budget), which is how conservation is asserted after an exception
/// escapes the run entry point and the ordinary budget return value is lost.</para>
///
/// <para>Conservation is asserted two independent ways: directly through
/// <see cref="EvaluationBudget.CurrentDepth"/>, and behaviourally through
/// <see cref="RemainingDepthCapacity"/>, which counts how many levels the budget will still
/// admit. The capacity probe catches a double release as well as a leak, and it is what a
/// test could use even with no observation accessor at all.</para>
/// </summary>
public class BudgetConservationTests
{
    // `f(k)` needs k + 1 nested invocations: f(k), f(k-1), ... f(0).
    private const string CountDown = "f(0) = 0\nf(n) = f(n - 1)\n";

    private static Expr Ast(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    /// <summary>
    /// Levels this budget will still admit, leaving it exactly as it was found. A leaked
    /// level shows up as one fewer; a double release as one more (or as the fail-loud
    /// underflow in <see cref="EvaluationBudget.ExitInvocation"/>, whichever comes first).
    /// </summary>
    private static int RemainingDepthCapacity(EvaluationBudget budget)
    {
        var entered = 0;
        while (budget.TryEnterArgumentEvaluation() is null)
        {
            entered++;
            if (entered > budget.MaxDepth + 8)
                Assert.Fail("depth capacity probe did not terminate; the budget is not enforcing MaxDepth");
        }

        for (var i = 0; i < entered; i++)
            budget.ExitInvocation();

        return entered;
    }

    /// <summary>Every scoped level is released and the peak never exceeded the ceiling.</summary>
    private static void AssertConserved(EvaluationBudget budget, string what)
    {
        Assert.True(budget.CurrentDepth == 0, $"{what}: leaked {budget.CurrentDepth} depth level(s)");
        Assert.True(budget.PeakDepth >= 0, $"{what}: negative peak depth {budget.PeakDepth}");
        Assert.True(
            budget.PeakDepth <= budget.MaxDepth,
            $"{what}: PeakDepth {budget.PeakDepth} exceeded MaxDepth {budget.MaxDepth}");
        Assert.Equal(budget.MaxDepth, RemainingDepthCapacity(budget));
    }

    // ── Fault injection ──────────────────────────────────────────────────────

    /// <summary>Where the injected fault is thrown relative to the production cache.</summary>
    private enum FaultSite
    {
        /// <summary>Before the production cache is consulted at all.</summary>
        BeforeCacheLookup,

        /// <summary>From inside the callback the production cache invokes on a miss.</summary>
        InsideCachedEvaluation,
    }

    /// <summary>
    /// Wraps a real cache and throws a chosen exception at the k-th zero-argument property
    /// access. Access k happens inside k live charged invocation regions for a property
    /// chain, so the fault unwinds through the production <c>finally</c> blocks. It also
    /// captures the run's live budget from the execution's run identity.
    /// </summary>
    private sealed class FaultingZeroArgPropertyResultCache(
        IZeroArgPropertyResultCache inner,
        int faultAtAccess,
        Func<Exception> fault,
        FaultSite site) : IZeroArgPropertyResultCache
    {
        private int _accesses;

        public EvaluationBudget? ObservedBudget { get; private set; }

        public int Accesses => _accesses;

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            ObservedBudget = (EvaluationBudget)execution.RunIdentity;
            var access = ++_accesses;

            if (site == FaultSite.BeforeCacheLookup && access == faultAtAccess)
                throw fault();

            return inner.GetOrEvaluate(
                execution,
                () => site == FaultSite.InsideCachedEvaluation && access == faultAtAccess
                    ? throw fault()
                    : evaluate());
        }
    }

    /// <summary>Counts zero-argument property accesses without changing any of them.</summary>
    private sealed class CountingZeroArgPropertyResultCache(IZeroArgPropertyResultCache inner)
        : IZeroArgPropertyResultCache
    {
        public int Accesses { get; private set; }

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            Accesses++;
            return inner.GetOrEvaluate(execution, evaluate);
        }
    }

    /// <summary>
    /// Runs <paramref name="source"/> with a fault injected at the k-th property access and
    /// returns the escaped exception together with the run's budget. Fails the test if the
    /// fault never fired or never escaped.
    /// </summary>
    private static (TException Thrown, EvaluationBudget Budget) RunFaulting<TException>(
        string source,
        int faultAtAccess,
        Func<Exception> fault,
        FaultSite site = FaultSite.InsideCachedEvaluation,
        EvaluationLimits? limits = null,
        bool enableOptimizations = true)
        where TException : Exception
    {
        var cache = new FaultingZeroArgPropertyResultCache(
            new RunScopedZeroArgPropertyResultCache(), faultAtAccess, fault, site);

        var thrown = Assert.Throws<TException>(() =>
            Evaluator.RunCountedObserved(
                Ast(source),
                limits,
                enableOptimizations,
                cache));

        Assert.NotNull(cache.ObservedBudget);
        Assert.True(
            cache.Accesses >= faultAtAccess,
            $"fault was configured for access {faultAtAccess} but only {cache.Accesses} occurred");
        return (thrown, cache.ObservedBudget!);
    }

    // ── A. A rejected enter is non-mutating ──────────────────────────────────

    [Fact]
    public void FailedArgumentDepthEnter_IsNonMutating()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 3, MaxSteps = 10 });
        for (var i = 0; i < 3; i++)
            Assert.Null(budget.TryEnterArgumentEvaluation());

        var depthBefore = budget.CurrentDepth;
        var peakBefore = budget.PeakDepth;
        var stepsBefore = budget.ConsumedSteps;
        var itemsBefore = budget.MaterializedItems;
        var charsBefore = budget.MaterializedStringChars;

        // Repeated rejection must stay non-mutating, not merely the first one.
        for (var attempt = 0; attempt < 5; attempt++)
        {
            Assert.IsType<EvalError.EvaluationDepthExceeded>(budget.TryEnterArgumentEvaluation());
            Assert.Equal(depthBefore, budget.CurrentDepth);
            Assert.Equal(peakBefore, budget.PeakDepth);
            Assert.Equal(stepsBefore, budget.ConsumedSteps);
            Assert.Equal(itemsBefore, budget.MaterializedItems);
            Assert.Equal(charsBefore, budget.MaterializedStringChars);
        }

        // The peak is ADMITTED depth, never attempted depth.
        Assert.Equal(budget.MaxDepth, budget.PeakDepth);

        for (var i = 0; i < 3; i++)
            budget.ExitInvocation();
        Assert.Equal(0, budget.CurrentDepth);
    }

    [Fact]
    public void FailedInvocationDepthEnter_IsNonMutating()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 3 });
        for (var i = 0; i < 3; i++)
            Assert.Null(budget.TryEnterInvocation());

        var depthBefore = budget.CurrentDepth;
        var peakBefore = budget.PeakDepth;
        var itemsBefore = budget.MaterializedItems;
        var charsBefore = budget.MaterializedStringChars;

        for (var attempt = 0; attempt < 5; attempt++)
        {
            Assert.IsType<EvalError.EvaluationDepthExceeded>(budget.TryEnterInvocation());
            Assert.Equal(depthBefore, budget.CurrentDepth);
            Assert.Equal(peakBefore, budget.PeakDepth);
            Assert.Equal(itemsBefore, budget.MaterializedItems);
            Assert.Equal(charsBefore, budget.MaterializedStringChars);
        }

        Assert.Equal(budget.MaxDepth, budget.PeakDepth);

        for (var i = 0; i < 3; i++)
            budget.ExitInvocation();
        Assert.Equal(0, budget.CurrentDepth);
    }

    /// <summary>
    /// A depth-rejected invocation charges NO step. The step is the invocation's own unit
    /// of semantic work, so an invocation that never entered must not consume it: a
    /// rejected enter is non-mutating in every counter, not only in depth. Without this
    /// the two always-active budgets cross-talk — a lower <c>MaxDepth</c> would consume
    /// more steps and could flip an unrelated <c>MaxSteps</c> verdict, exactly the
    /// dependency <see cref="BudgetCrossTalkMatrixTests"/> exists to forbid.
    /// </summary>
    [Fact]
    public void FailedInvocationDepthEnter_ChargesNoStep()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 2, MaxSteps = 100 });
        Assert.Null(budget.TryEnterInvocation());
        Assert.Null(budget.TryEnterInvocation());
        Assert.Equal(2L, budget.ConsumedSteps);

        for (var attempt = 0; attempt < 5; attempt++)
        {
            Assert.IsType<EvalError.EvaluationDepthExceeded>(budget.TryEnterInvocation());
            Assert.Equal(2L, budget.ConsumedSteps);
        }

        budget.ExitInvocation();
        budget.ExitInvocation();
    }

    /// <summary>
    /// Named regression for the defect this suite found. <c>TryEnterInvocation</c> charged
    /// its step BEFORE testing the depth ceiling, so a depth-REJECTED invocation still
    /// consumed a step. That is normally invisible because the limit error ends the run —
    /// but a resource-limit failure of a parameter's eager value evaluation is RETAINED on
    /// the algorithm binding instead of raised, so a program that binds such a parameter
    /// without demanding its value succeeds while having absorbed the refusal.
    ///
    /// <para>Here <c>G(A)</c> binds <c>A</c> whose value channel recurses until
    /// <c>MaxDepth</c> refuses it, <c>G</c> never demands the value, and the run returns
    /// 10 after exactly four dynamic invocations: <c>G(A)</c>, <c>A</c>, <c>A</c>,
    /// <c>H()</c>. It was charged five steps, so <c>MaxSteps = 4</c> rejected a run that
    /// performed four invocations — a <c>MaxDepth</c> value deciding a <c>MaxSteps</c>
    /// verdict, the cross-talk <see cref="BudgetCrossTalkMatrixTests"/> forbids.</para>
    /// </summary>
    [Fact]
    public void AbsorbedDepthRejection_DoesNotConsumeAStep()
    {
        var ast = Ast("G(f) = 1\nA = A\nH = 9\nG(A) + H()");
        var limits = new EvaluationLimits { MaxDepth = 3 };

        var (result, budget) = Evaluator.RunCountedObserved(ast, limits);
        Assert.False(result.IsError);
        Assert.Equal(3, budget.PeakDepth);

        // Four dynamic invocations were performed; the refused fifth is not one of them.
        Assert.Equal(4L, budget.ConsumedSteps);
        AssertConserved(budget, "run that absorbed a depth rejection");

        // ... and the step budget that exactly covers the performed work must admit it.
        Assert.False(Evaluator.Run(ast, limits with { MaxSteps = 4 }).IsError);
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(
            Innermost(Evaluator.Run(ast, limits with { MaxSteps = 3 }).Error));
    }

    /// <summary>
    /// The same retained-error path with two independently refused eager values. Each
    /// refusal is non-mutating, so only the six admitted invocations are charged.
    /// </summary>
    [Fact]
    public void MultipleAbsorbedDepthRejections_ChargeNoPhantomSteps()
    {
        var ast = Ast("G(f, g) = 1\nA = A\nB = B\nH = 9\nG(A, B) + H()");
        var limits = new EvaluationLimits { MaxDepth = 3 };

        var (result, budget) = Evaluator.RunCountedObserved(ast, limits);
        Assert.False(result.IsError);
        Assert.Equal(3, budget.PeakDepth);
        Assert.Equal(6L, budget.ConsumedSteps);
        AssertConserved(budget, "run that absorbed two independent depth rejections");

        Assert.False(Evaluator.Run(ast, limits with { MaxSteps = 6 }).IsError);
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(
            Innermost(Evaluator.Run(ast, limits with { MaxSteps = 5 }).Error));
    }

    /// <summary>
    /// The step ceiling still takes precedence over the depth ceiling when BOTH are
    /// exhausted, and a step-rejected enter is equally non-mutating.
    /// </summary>
    [Fact]
    public void StepExhaustedInvocationEnter_ReportsStepLimit_AndIsNonMutating()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 4, MaxSteps = 2 });
        Assert.Null(budget.TryEnterInvocation());
        Assert.Null(budget.TryEnterInvocation());
        Assert.Equal(2L, budget.ConsumedSteps);
        Assert.Equal(2, budget.CurrentDepth);

        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(budget.TryEnterInvocation());
        Assert.Equal(2L, budget.ConsumedSteps);
        Assert.Equal(2, budget.CurrentDepth);
        Assert.Equal(2, budget.PeakDepth);

        budget.ExitInvocation();
        budget.ExitInvocation();
    }

    [Fact]
    public void SimultaneouslyExhaustedInvocationEnter_PreservesStepFirstPrecedence()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 2, MaxSteps = 2 });
        Assert.Null(budget.TryEnterInvocation());
        Assert.Null(budget.TryEnterInvocation());

        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(budget.TryEnterInvocation());
        Assert.Equal(2L, budget.ConsumedSteps);
        Assert.Equal(2, budget.CurrentDepth);
        Assert.Equal(2, budget.PeakDepth);

        budget.ExitInvocation();
        budget.ExitInvocation();
    }

    /// <summary>
    /// A bulk expression-work step is committed only when the whole 4096-checkpoint
    /// batch is admitted. If the step ceiling rejects the batch boundary, retrying that
    /// same boundary must reject again; advancing into a fresh batch would let retained
    /// or otherwise absorbed errors execute more expression work past the ceiling.
    /// </summary>
    [Fact]
    public void FailedExpressionWorkCharge_DoesNotAdvanceTheCheckpointBatch()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxSteps = 1 });

        for (var i = 0; i < 4096; i++)
            Assert.Null(budget.TryChargeExpressionNodeWork());
        Assert.Equal(1L, budget.ConsumedSteps);

        for (var i = 0; i < 4095; i++)
            Assert.Null(budget.TryChargeExpressionNodeWork());

        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(budget.TryChargeExpressionNodeWork());
        Assert.Equal(1L, budget.ConsumedSteps);

        // The rejected checkpoint was not performed and therefore did not enter a new batch.
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(budget.TryChargeExpressionNodeWork());
        Assert.Equal(1L, budget.ConsumedSteps);
    }

    /// <summary>
    /// A rejected enter must not evaluate what the region would have evaluated. Source
    /// level: <c>count(A)</c> reaches <c>A</c> only through the depth-charged builtin
    /// argument funnel, so at one level below the boundary the property is never accessed.
    /// </summary>
    [Fact]
    public void RejectedArgumentDepthEnter_DoesNotEvaluateTheArgumentBody()
    {
        var ast = Ast("A = B\nB = 7\ncount(A)");

        var admitted = new CountingZeroArgPropertyResultCache(new RunScopedZeroArgPropertyResultCache());
        var (okResult, okBudget) = Evaluator.RunCountedObserved(
            ast, new EvaluationLimits { MaxDepth = 2 }, zeroArgPropertyResultCache: admitted);
        Assert.False(okResult.IsError);
        Assert.Equal(1, admitted.Accesses);
        AssertConserved(okBudget, "admitted builtin argument funnel");

        var rejected = new CountingZeroArgPropertyResultCache(new RunScopedZeroArgPropertyResultCache());
        var (failResult, failBudget) = Evaluator.RunCountedObserved(
            ast, new EvaluationLimits { MaxDepth = 1 }, zeroArgPropertyResultCache: rejected);
        Assert.True(failResult.IsError);
        Assert.IsType<EvalError.EvaluationDepthExceeded>(failResult.Error);
        Assert.Equal(0, rejected.Accesses);
        AssertConserved(failBudget, "rejected builtin argument funnel");
    }

    // ── B. Balanced exactly once: structured failure ─────────────────────────

    public static TheoryData<string, EvaluationLimits?> ConservationCorpus()
    {
        var data = new TheoryData<string, EvaluationLimits?>();

        // (program, limits). Each program is run at several ceilings so that the same
        // shape exits normally, through a structured error, and through a budget failure.
        string[] programs =
        [
            "1 + 1",                                              // trivial success
            $"{CountDown}f(6)",                                    // deep recursion
            "A = A\nA",                                            // self-referential property
            "A = count(A)\nA",                                     // recursion through a builtin argument
            "A = A.string\nA",                                     // recursion through the demand funnel
            "F(v) = v.string\nx = F(x)\nx",                        // dual-channel demand retry
            "range(1, 6).filter(P).count\nP(x) = x > 2",           // fused pipeline
            "count(filter(range(1, 6), P))\nP(x) = x > 2",         // plain fused pipeline
            "(1, 2, 3).map(F).sum\nF(x) = x * 2",                  // callback pipeline
            "[1, 2, 3].reduce(F, 0)\nF(a, b) = a + b",             // reducer callback
            "1 / 0",                                               // structured non-limit error
            "Missing",                                             // unknown name
            "count(1, 2)",                                         // arity error
            "while(S, 4)\nS(n) = n + 1, n < 3",                    // loop
            "repeat(S, 4, 0)\nS(n) = n + 1",                       // repeat loop
            "'abc'.string",                                        // string materialization
        ];

        EvaluationLimits?[] configurations =
        [
            null,
            new EvaluationLimits { MaxDepth = 1 },
            new EvaluationLimits { MaxDepth = 2 },
            new EvaluationLimits { MaxDepth = 3 },
            new EvaluationLimits { MaxDepth = 5 },
            new EvaluationLimits { MaxSteps = 1 },
            new EvaluationLimits { MaxSteps = 4 },
            new EvaluationLimits { MaxCollectionItems = 1 },
            new EvaluationLimits { MaxMaterializedItems = 2 },
            new EvaluationLimits { MaxStringLength = 1 },
            new EvaluationLimits { MaxMaterializedStringChars = 2 },
        ];

        foreach (var program in programs)
        {
            foreach (var configuration in configurations)
                data.Add(program, configuration);
        }

        return data;
    }

    /// <summary>
    /// The broad sweep: whatever a run does — succeed, fail with an ordinary error, or hit
    /// any budget, with optimizers on and off — it must end holding no depth level.
    /// </summary>
    [Theory]
    [MemberData(nameof(ConservationCorpus))]
    public void EveryRunOutcome_ReleasesAllScopedDepth(string program, EvaluationLimits? limits)
    {
        foreach (var optimizations in new[] { false, true })
        {
            var (_, budget) = Evaluator.RunCountedObserved(
                Ast(program), limits, enableOptimizations: optimizations);
            AssertConserved(budget, $"{program} @ {(limits is null ? "default" : limits.ToString())}");
        }
    }

    [Fact]
    public void InvocationDepth_IsReleasedOnStructuredFailure()
    {
        // The innermost call fails with an ordinary (non-limit) error while six
        // invocation levels are live; all six must unwind.
        var (result, budget) = Evaluator.RunCountedObserved(
            Ast("f(0) = 1 / 0\nf(n) = f(n - 1)\nf(5)"),
            new EvaluationLimits { MaxDepth = 16 });

        Assert.True(result.IsError);
        Assert.IsType<EvalError.DivByZero>(Innermost(result.Error));
        Assert.Equal(6, budget.PeakDepth);
        AssertConserved(budget, "structured failure under six live invocations");
    }

    [Fact]
    public void ArgumentEvaluationDepth_IsReleasedOnStructuredFailure()
    {
        // `count(...)` charges the builtin ARGUMENT funnel (depth, no step) around a body
        // that then fails with an ordinary error.
        var (result, budget) = Evaluator.RunCountedObserved(
            Ast("A = 1 / 0\ncount(A)"),
            new EvaluationLimits { MaxDepth = 8 });

        Assert.True(result.IsError);
        Assert.IsType<EvalError.DivByZero>(Innermost(result.Error));
        AssertConserved(budget, "structured failure inside a builtin argument funnel");
    }

    [Fact]
    public void NestedScopedRegions_UnwindTogetherOnInnerDepthFailure()
    {
        // argument funnel -> invocation -> argument funnel -> ... until the ceiling
        // rejects the innermost enter. Every admitted level above it must still unwind.
        var (result, budget) = Evaluator.RunCountedObserved(
            Ast("A = count(B)\nB = f(3)\nf(0) = count(A)\nf(n) = f(n - 1)\nA"),
            new EvaluationLimits { MaxDepth = 6 });

        Assert.True(result.IsError);
        Assert.IsType<EvalError.EvaluationDepthExceeded>(Innermost(result.Error));
        Assert.Equal(6, budget.PeakDepth);
        AssertConserved(budget, "nested mixed regions after an inner depth failure");
    }

    // ── C. Balanced exactly once: exceptional unwind ─────────────────────────

    [Fact]
    public void InvocationDepth_IsReleasedOnException()
    {
        // Fault at the third nested property access: three charged invocation regions are
        // live when the CLR exception is thrown.
        var (thrown, budget) = RunFaulting<InvalidOperationException>(
            "A = B\nB = C\nC = 1\nA",
            faultAtAccess: 3,
            () => new InvalidOperationException("fault-injection"),
            limits: new EvaluationLimits { MaxDepth = 12 });

        Assert.Equal("fault-injection", thrown.Message);
        Assert.Equal(3, budget.PeakDepth);
        AssertConserved(budget, "exception under three live invocations");
    }

    [Fact]
    public void ArgumentEvaluationDepth_IsReleasedOnException()
    {
        // `A = count(B)` stacks invocation(A) -> builtin ARGUMENT funnel(B) -> invocation(C),
        // so the unwind crosses both protocols. `B` itself is an argument ALGORITHM, not a
        // zero-argument property access, so the second cache access is `C`.
        var (_, budget) = RunFaulting<InvalidOperationException>(
            "A = count(B)\nB = C\nC = 1\nA",
            faultAtAccess: 2,
            () => new InvalidOperationException("fault-injection"),
            limits: new EvaluationLimits { MaxDepth = 12 });

        Assert.Equal(3, budget.PeakDepth);
        AssertConserved(budget, "exception across mixed invocation and argument levels");
    }

    /// <summary>
    /// The fault fires BEFORE the production cache is consulted, so it unwinds from the
    /// charged region without the run-scoped cache having recorded a miss for that access.
    /// </summary>
    [Fact]
    public void InvocationDepth_IsReleasedOnExceptionBeforeCacheLookup()
    {
        var (_, budget) = RunFaulting<InvalidOperationException>(
            "A = B\nB = C\nC = 1\nA",
            faultAtAccess: 3,
            () => new InvalidOperationException("fault-injection"),
            FaultSite.BeforeCacheLookup,
            new EvaluationLimits { MaxDepth = 12 });

        AssertConserved(budget, "exception before cache lookup");
    }

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(3)]
    [InlineData(4)]
    public void ScopedDepth_IsReleasedOnExceptionAtEveryNestingLevel(int faultAtAccess)
    {
        var (_, budget) = RunFaulting<InvalidOperationException>(
            "A = B\nB = C\nC = D\nD = 1\nA",
            faultAtAccess,
            () => new InvalidOperationException("fault-injection"),
            limits: new EvaluationLimits { MaxDepth = 12 });

        Assert.Equal(faultAtAccess, budget.PeakDepth);
        AssertConserved(budget, $"exception at nesting level {faultAtAccess}");
    }

    // ── D. Balanced exactly once: cancellation ───────────────────────────────

    /// <summary>
    /// <see cref="OperationCanceledException"/> is not special-cased anywhere in the
    /// evaluator: it must escape unchanged (never be translated into a language
    /// <see cref="EvalError"/>) and must leave the scoped protocol conserved.
    /// </summary>
    [Fact]
    public void InvocationDepth_IsReleasedOnCancellation()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();

        var (thrown, budget) = RunFaulting<OperationCanceledException>(
            "A = B\nB = C\nC = 1\nA",
            faultAtAccess: 3,
            () => new OperationCanceledException(cts.Token),
            limits: new EvaluationLimits { MaxDepth = 12 });

        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.Equal(3, budget.PeakDepth);
        AssertConserved(budget, "cancellation under three live invocations");
    }

    [Fact]
    public void ArgumentEvaluationDepth_IsReleasedOnCancellation()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();

        var (_, budget) = RunFaulting<OperationCanceledException>(
            "A = count(B)\nB = C\nC = 1\nA",
            faultAtAccess: 2,
            () => new OperationCanceledException(cts.Token),
            limits: new EvaluationLimits { MaxDepth = 12 });

        Assert.Equal(3, budget.PeakDepth);
        AssertConserved(budget, "cancellation across mixed invocation and argument levels");
    }

    [Fact]
    public void CancellationInsideAFusedPipelinePredicate_ReleasesEveryScopedLevel()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();

        // The predicate body reads a zero-argument property, so the fault fires inside the
        // filter callback, inside the committed fused region's collection-argument level.
        var (_, budget) = RunFaulting<OperationCanceledException>(
            "K = 2\nP(x) = x > K\nrange(1, 6).filter(P).count",
            faultAtAccess: 1,
            () => new OperationCanceledException(cts.Token),
            limits: new EvaluationLimits { MaxDepth = 12 });

        AssertConserved(budget, "cancellation inside a fused pipeline predicate");
    }

    [Fact]
    public void ExceptionInsideAFusedPipelinePredicate_ReleasesEveryScopedLevel()
    {
        var (_, budget) = RunFaulting<InvalidOperationException>(
            "K = 2\nP(x) = x > K\nrange(1, 6).filter(P).count",
            faultAtAccess: 1,
            () => new InvalidOperationException("fault-injection"),
            limits: new EvaluationLimits { MaxDepth = 12 });

        AssertConserved(budget, "exception inside a fused pipeline predicate");
    }

    // ── E. Fused pipeline and range optimizer regions ────────────────────────

    /// <summary>
    /// The direct-range optimizer charges a NESTED argument-evaluation level while it
    /// evaluates the range bounds, inside the committed fused region's own level. A fault
    /// in a bound must release both.
    ///
    /// <para>The bound is written <c>N</c> with <c>N = M</c>: a bound is an argument
    /// ALGORITHM, so the fault has to be planted one level further in, in the body the
    /// bound's own argument funnel evaluates.</para>
    /// </summary>
    private const string FusedRangeBoundProgram =
        "N = M\nM = 6\nP(x) = x > 2\nrange(1, N).filter(P).count";

    /// <summary>Proves the program under test really does fuse through the DIRECT RANGE source.</summary>
    private static void AssertFusesThroughTheDirectRangeSource(string program)
    {
        var diagnostics = new SequencePipelineDiagnostics();
        var (result, _) = Evaluator.RunCountedObserved(
            Ast(program), new EvaluationLimits { MaxDepth = 12 }, sequenceDiagnostics: diagnostics);
        Assert.False(result.IsError);
        Assert.Equal(1, diagnostics.FilterCountFusionHits);
        Assert.Equal(0, diagnostics.FilterCountFusionFallbacks);
        Assert.Equal(0, diagnostics.DirectRangeFusionFallbacks);
    }

    [Fact]
    public void RangeOptimizerDepth_IsReleasedOnBoundFault()
    {
        AssertFusesThroughTheDirectRangeSource(FusedRangeBoundProgram);

        var (_, budget) = RunFaulting<InvalidOperationException>(
            FusedRangeBoundProgram,
            faultAtAccess: 1,
            () => new InvalidOperationException("fault-injection"),
            limits: new EvaluationLimits { MaxDepth = 12 });

        AssertConserved(budget, "exception inside a fused range bound");
    }

    [Fact]
    public void RangeOptimizerDepth_IsReleasedOnBoundCancellation()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();

        var (_, budget) = RunFaulting<OperationCanceledException>(
            FusedRangeBoundProgram,
            faultAtAccess: 1,
            () => new OperationCanceledException(cts.Token),
            limits: new EvaluationLimits { MaxDepth = 12 });

        AssertConserved(budget, "cancellation inside a fused range bound");
    }

    [Fact]
    public void RangeOptimizerDepth_IsReleasedOnStructuredBoundFailure()
    {
        var (result, budget) = Evaluator.RunCountedObserved(
            Ast("N = 1 / 0\nP(x) = x > 2\nrange(1, N).filter(P).count"),
            new EvaluationLimits { MaxDepth = 12 });

        Assert.True(result.IsError);
        Assert.IsType<EvalError.DivByZero>(Innermost(result.Error));
        AssertConserved(budget, "structured failure inside a fused range bound");
    }

    /// <summary>
    /// The nested range-bound level is charged on TOP of the committed fused level, so a
    /// depth ceiling that admits the outer level but not the bound's own must reject
    /// cleanly and leave nothing held.
    /// </summary>
    [Fact]
    public void RangeOptimizerNestedDepth_IsReleasedOnItsOwnDepthRejection()
    {
        var (unlimited, unlimitedBudget) = Evaluator.RunCountedObserved(
            Ast(FusedRangeBoundProgram), new EvaluationLimits { MaxDepth = 12 });
        Assert.False(unlimited.IsError);
        var boundary = unlimitedBudget.PeakDepth;

        for (var maxDepth = 1; maxDepth < boundary; maxDepth++)
        {
            var (result, budget) = Evaluator.RunCountedObserved(
                Ast(FusedRangeBoundProgram), new EvaluationLimits { MaxDepth = maxDepth });
            Assert.True(result.IsError, $"MaxDepth={maxDepth} must reject below the boundary {boundary}");
            Assert.IsType<EvalError.EvaluationDepthExceeded>(Innermost(result.Error));
            AssertConserved(budget, $"fused range pipeline rejected at MaxDepth={maxDepth}");
        }

        var (atBoundary, atBoundaryBudget) = Evaluator.RunCountedObserved(
            Ast(FusedRangeBoundProgram), new EvaluationLimits { MaxDepth = boundary });
        Assert.False(atBoundary.IsError);
        AssertConserved(atBoundaryBudget, "fused range pipeline at its exact depth boundary");
    }

    /// <summary>
    /// The committed fused region must release its outer collection-argument level when an
    /// EXCEPTION escapes it, not only when a structured error is returned
    /// (<c>BudgetCrossTalkMatrixTests.CommittedSourceFailure_ReleasesOptimizerDepthExactlyOnce</c>
    /// pins the structured case). Driven through the optimizer's own service seam so the
    /// fault lands exactly in the committed region.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void FusedPipelineOuterDepth_IsReleasedWhenAnExceptionEscapesTheCommittedRegion(bool cancellation)
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        Func<Exception> fault = cancellation
            ? () => new OperationCanceledException(cts.Token)
            : () => new InvalidOperationException("fault-injection");

        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 4 });
        var ctx = Evaluator.EvalCtx.Empty with { Budget = budget };

        var thrown = Assert.Throws(
            cancellation ? typeof(OperationCanceledException) : typeof(InvalidOperationException),
            () => SequencePipelineOptimizer.TryExecute(
                FusedRangeCountInvocation(),
                FaultingRangeServices(fault),
                ctx,
                [],
                diagnostics: null,
                out _));

        Assert.NotNull(thrown);
        Assert.Equal(1, budget.PeakDepth);
        AssertConserved(budget, "exception escaping the committed fused region");
    }

    /// <summary>
    /// The same for the GENERIC (non-range) fused source, whose committed region evaluates
    /// the dot receiver instead of range bounds.
    /// </summary>
    [Fact]
    public void FusedPipelineOuterDepth_IsReleasedWhenTheGenericSourceThrows()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 4 });
        var ctx = Evaluator.EvalCtx.Empty with { Budget = budget };
        var source = new Expr.Resolve("Values");
        var filter = new Expr.DotCall(
            source, "filter", OutputBundle.From([new Expr.Resolve("Predicate")]));
        var invocation = SequencePipelineInvocation.DotCall(new Expr.DotCall(filter, "count"));
        var predicate = new Algorithm.User(null, [new ParameterDeclaration("x")], [], [], [new Expr.Num(1)]);

        var services = new SequencePipelineEvaluationServices(
            GetDotCallLexicalBuiltinFallbackReason: (_, _) => null,
            EvaluateDotReceiverIterationItems: _ => throw new InvalidOperationException("fault-injection"),
            EvaluateSequenceIterationItems: _ => throw new Xunit.Sdk.XunitException("plain source must not run"),
            ResolveArgumentAlgorithms: _ => EvalResult<IReadOnlyList<Algorithm>>.Ok([predicate]),
            ResolveAlgorithm: _ => EvalResult<Algorithm>.Ok(new Algorithm.User(null, [], [], [], [])),
            EvaluateRangeCallArguments: (_, _, _) =>
                throw new Xunit.Sdk.XunitException("range evaluation must not run"));

        Assert.Throws<InvalidOperationException>(() => SequencePipelineOptimizer.TryExecute(
            invocation, services, ctx, [], diagnostics: null, out _));

        Assert.Equal(1, budget.PeakDepth);
        AssertConserved(budget, "exception escaping the committed generic fused region");
    }

    /// <summary>
    /// No level is released when none was committed: an optimizer that never reaches the
    /// commit point must leave the budget untouched, so a later exact-boundary region still
    /// gets its full capacity.
    /// </summary>
    [Fact]
    public void UncommittedOptimizerFallback_ReleasesNothing()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 3 });
        var ctx = Evaluator.EvalCtx.Empty with
        {
            Budget = budget,
            EnableSequencePipelineOptimization = false,
        };

        var handled = SequencePipelineOptimizer.TryExecute(
            FusedRangeCountInvocation(),
            FaultingRangeServices(() => new Xunit.Sdk.XunitException("committed region must not run")),
            ctx,
            [],
            diagnostics: null,
            out _);

        Assert.False(handled);
        Assert.Equal(0, budget.PeakDepth);
        AssertConserved(budget, "uncommitted optimizer fallback");
    }

    private static SequencePipelineInvocation FusedRangeCountInvocation()
    {
        var range = new Expr.Call(
            new Expr.Resolve("range"),
            OutputBundle.From([new Expr.Num(1), new Expr.Num(3)]));
        var filter = new Expr.DotCall(
            range, "filter", OutputBundle.From([new Expr.Resolve("Predicate")]));
        return SequencePipelineInvocation.DotCall(new Expr.DotCall(filter, "count"));
    }

    private static SequencePipelineEvaluationServices FaultingRangeServices(Func<Exception> fault)
    {
        var predicate = new Algorithm.User(null, [new ParameterDeclaration("x")], [], [], [new Expr.Num(1)]);
        return new SequencePipelineEvaluationServices(
            GetDotCallLexicalBuiltinFallbackReason: (_, _) => null,
            EvaluateDotReceiverIterationItems: _ =>
                throw new Xunit.Sdk.XunitException("generic source must not run for a direct range"),
            EvaluateSequenceIterationItems: _ => throw new Xunit.Sdk.XunitException("plain source must not run"),
            ResolveArgumentAlgorithms: _ => EvalResult<IReadOnlyList<Algorithm>>.Ok([predicate]),
            ResolveAlgorithm: _ => EvalResult<Algorithm>.Ok(new Algorithm.Builtin(BuiltinId.@range)),
            EvaluateRangeCallArguments: (_, _, _) => throw fault());
    }

    // ── E2. Callback regions ─────────────────────────────────────────────────

    /// <summary>
    /// Every callback dispatch is its own charged invocation. A callback that fails —
    /// structurally, or by exhausting the depth budget itself — must release its own level
    /// and every level the pipeline holds above it.
    /// </summary>
    [Theory]
    [InlineData("[1, 2, 3].map(F)\nF(x) = x / 0")]
    [InlineData("[1, 2, 3].filter(F)\nF(x) = x / 0")]
    [InlineData("[1, 2, 3].reduce(F, 0)\nF(a, b) = a / 0")]
    [InlineData("range(1, 4).filter(F).count\nF(x) = x / 0")]
    [InlineData("[1, 2, 3].map(F)\nF(x) = R\nR = R")]
    [InlineData("[1, 2, 3].reduce(F, 0)\nF(a, b) = R\nR = R")]
    public void CallbackDepth_IsReleasedOnCallbackFailure(string program)
    {
        foreach (var optimizations in new[] { false, true })
        {
            var (result, budget) = Evaluator.RunCountedObserved(
                Ast(program), new EvaluationLimits { MaxDepth = 8 }, enableOptimizations: optimizations);
            Assert.True(result.IsError);
            AssertConserved(budget, $"{program} (optimizations={optimizations})");
        }
    }

    /// <summary>
    /// The composite shape: a fused outer collection-argument level, a predicate invocation
    /// inside it, and a nested pipeline inside that which fails. Everything unwinds.
    /// </summary>
    [Fact]
    public void NestedPipelineInsideAFusedPredicate_UnwindsEveryLevel()
    {
        const string Program =
            "Inner(k) = range(1, k).filter(Q).count\n" +
            "Q(y) = y / 0\n" +
            "P(x) = Inner(x) > 0\n" +
            "range(1, 3).filter(P).count";

        foreach (var optimizations in new[] { false, true })
        {
            var (result, budget) = Evaluator.RunCountedObserved(
                Ast(Program), new EvaluationLimits { MaxDepth = 16 }, enableOptimizations: optimizations);
            Assert.True(result.IsError);
            Assert.IsType<EvalError.DivByZero>(Innermost(result.Error));
            AssertConserved(budget, $"nested fused pipeline failure (optimizations={optimizations})");
        }
    }

    /// <summary>
    /// Cumulative budgets are NOT rolled back by a failure: work performed before the
    /// failure stays charged inside its own run. Only the SCOPED depth protocol unwinds.
    /// </summary>
    [Fact]
    public void CumulativeWorkBeforeAFailure_StaysChargedWithinItsRun()
    {
        var (result, budget) = Evaluator.RunCountedObserved(
            Ast("f(0) = 1 / 0\nf(n) = f(n - 1)\nf(5)"),
            new EvaluationLimits { MaxDepth = 16 });

        Assert.True(result.IsError);
        Assert.Equal(6L, budget.ConsumedSteps);
        Assert.Equal(0, budget.CurrentDepth);
    }

    // ── F. No underflow / no double release ──────────────────────────────────

    /// <summary>
    /// A double release is fail-loud. It is as damaging as a leak — it makes every later
    /// nested region look shallower than it is — and silent clamping would hide exactly the
    /// ownership bug this suite exists to catch.
    /// </summary>
    [Fact]
    public void ExitingALevelThatWasNeverEntered_FailsLoudly()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxDepth = 2 });
        Assert.Throws<InvalidOperationException>(budget.ExitInvocation);

        Assert.Null(budget.TryEnterArgumentEvaluation());
        budget.ExitInvocation();
        Assert.Throws<InvalidOperationException>(budget.ExitInvocation);
        Assert.Equal(0, budget.CurrentDepth);
        Assert.Equal(budget.MaxDepth, RemainingDepthCapacity(budget));
    }

    // ── G. Exact-boundary conservation ───────────────────────────────────────

    /// <summary>
    /// Off-by-one leaks hide behind generous ceilings. At the exact boundary D, a run that
    /// faulted earlier must still admit D levels — and D - 1 must still be rejected.
    /// </summary>
    [Fact]
    public void FaultedRun_LeavesTheExactDepthBoundaryIntact()
    {
        var program = $"{CountDown}f(6)";
        var (_, unlimited) = Evaluator.RunCountedObserved(Ast(program));
        var boundary = unlimited.PeakDepth;

        Assert.False(Evaluator.Run(Ast(program), new EvaluationLimits { MaxDepth = boundary }).IsError);
        Assert.True(Evaluator.Run(Ast(program), new EvaluationLimits { MaxDepth = boundary - 1 }).IsError);

        // Now fault a run at that exact ceiling and re-probe its budget: the fault consumed
        // levels while unwinding, and every one of them must be back.
        var (_, faultedBudget) = RunFaulting<InvalidOperationException>(
            "A = B\nB = C\nC = 1\nA",
            faultAtAccess: 3,
            () => new InvalidOperationException("fault-injection"),
            limits: new EvaluationLimits { MaxDepth = boundary });
        Assert.Equal(boundary, RemainingDepthCapacity(faultedBudget));
    }

    // ── H. Run isolation ─────────────────────────────────────────────────────

    /// <summary>
    /// A faulted run must not change the verdict of the next run. The budget is per-run, so
    /// this also pins that no state escapes through the shared, immutable
    /// <see cref="EvaluationLimits"/> instance the runs have in common.
    /// </summary>
    [Fact]
    public void FailedRun_DoesNotChangeSubsequentDepthVerdict()
    {
        var boundaryProgram = $"{CountDown}f(6)";
        var boundary = Evaluator.RunCountedObserved(Ast(boundaryProgram)).Budget.PeakDepth;
        var atBoundary = new EvaluationLimits { MaxDepth = boundary, MaxSteps = 5_000 };

        var fresh = Evaluator.Run(Ast(boundaryProgram), atBoundary);
        Assert.False(fresh.IsError);

        // Exhaust depth, exhaust steps, and fail with an ordinary error, all under the very
        // same limits instance the boundary run uses.
        foreach (var failing in new[] { "A = A\nA", $"{CountDown}f(400)", "1 / 0", "Missing" })
            Assert.True(Evaluator.Run(Ast(failing), atBoundary).IsError);

        var after = Evaluator.Run(Ast(boundaryProgram), atBoundary);
        Assert.False(after.IsError);
        Assert.Equal(fresh.Value, after.Value);

        // And the boundary is still exactly where it was.
        Assert.True(Evaluator.Run(
            Ast(boundaryProgram), atBoundary with { MaxDepth = boundary - 1 }).IsError);
    }

    [Fact]
    public void FaultedRun_DoesNotChangeSubsequentDepthVerdict()
    {
        var boundaryProgram = $"{CountDown}f(6)";
        var boundary = Evaluator.RunCountedObserved(Ast(boundaryProgram)).Budget.PeakDepth;
        var atBoundary = new EvaluationLimits { MaxDepth = boundary, MaxSteps = 5_000 };
        var expected = Evaluator.Run(Ast(boundaryProgram), atBoundary);
        Assert.False(expected.IsError);

        using var cts = new CancellationTokenSource();
        cts.Cancel();

        RunFaulting<InvalidOperationException>(
            "A = B\nB = C\nC = 1\nA", 3,
            () => new InvalidOperationException("fault-injection"), limits: atBoundary);
        RunFaulting<OperationCanceledException>(
            "A = B\nB = C\nC = 1\nA", 3,
            () => new OperationCanceledException(cts.Token), limits: atBoundary);

        var after = Evaluator.Run(Ast(boundaryProgram), atBoundary);
        Assert.False(after.IsError);
        Assert.Equal(expected.Value, after.Value);
        Assert.True(Evaluator.Run(
            Ast(boundaryProgram), atBoundary with { MaxDepth = boundary - 1 }).IsError);
    }

    /// <summary>
    /// Cumulative counters are per-RUN. A run that spent most of a cumulative budget must
    /// not leave the next run short: the second run's counters must match a fresh run's,
    /// even though the two share one immutable limits instance.
    /// </summary>
    [Fact]
    public void CumulativeBudgets_DoNotCrossIntoALaterRun()
    {
        var limits = new EvaluationLimits
        {
            MaxSteps = 400,
            MaxMaterializedItems = 40,
            MaxMaterializedStringChars = 40,
        };
        var probe = Ast("(1, 2, 3).map(F).sum\nF(x) = x * 2");

        var (freshResult, freshBudget) = Evaluator.RunCountedObserved(probe, limits);
        Assert.False(freshResult.IsError);

        // Spend most of every cumulative budget, then fail.
        var (spentResult, spentBudget) = Evaluator.RunCountedObserved(
            Ast("range(1, 30).map(G).sum\nG(x) = x * 2"), limits);
        Assert.True(spentResult.IsError);
        Assert.True(spentBudget.ConsumedSteps > 0);

        var (afterResult, afterBudget) = Evaluator.RunCountedObserved(probe, limits);
        Assert.False(afterResult.IsError);
        Assert.Equal(freshResult.Value.Value, afterResult.Value.Value);
        Assert.Equal(freshBudget.ConsumedSteps, afterBudget.ConsumedSteps);
        Assert.Equal(freshBudget.MaterializedItems, afterBudget.MaterializedItems);
        Assert.Equal(freshBudget.MaterializedStringChars, afterBudget.MaterializedStringChars);
        Assert.Equal(freshBudget.PeakDepth, afterBudget.PeakDepth);
    }

    /// <summary>
    /// The same at the PUBLIC façade, where a host actually reuses configuration:
    /// <see cref="KatLangEngine"/> is static and builds fresh run state per call, and one
    /// <see cref="RunOptions"/> object drives every run here — including the extra
    /// <c>DisplayDecimals</c> evaluation, which charges the same run budget.
    /// </summary>
    [Fact]
    public void PublicEngine_FailedRuns_DoNotChangeALaterRunsVerdict()
    {
        var boundaryProgram = $"{CountDown}f(6)";
        var boundary = Evaluator.RunCountedObserved(Ast(boundaryProgram)).Budget.PeakDepth;
        var options = new RunOptions
        {
            EvaluationLimits = new EvaluationLimits { MaxDepth = boundary, MaxSteps = 5_000 },
        };

        var expected = KatLangEngine.Run(boundaryProgram, options);
        Assert.True(expected.IsSuccess);

        foreach (var failing in new[] { "A = A\nA", $"{CountDown}f(400)", "1 / 0", "Missing" })
            Assert.True(KatLangEngine.Run(failing, options).IsFailure);

        var after = KatLangEngine.Run(boundaryProgram, options);
        Assert.True(after.IsSuccess);
        Assert.Equal(expected.ToDisplayString(), after.ToDisplayString());

        // A program with a DisplayDecimals property charges the same budget twice over;
        // neither charge may escape into the next run.
        var withDisplay = $"DisplayDecimals = 2\n{boundaryProgram}";
        var displayExpected = KatLangEngine.Run(withDisplay, options);
        Assert.True(KatLangEngine.Run("A = A\nA", options).IsFailure);
        Assert.Equal(displayExpected.ToDisplayString(), KatLangEngine.Run(withDisplay, options).ToDisplayString());
    }

    // ── I. Reusable-cache isolation ──────────────────────────────────────────

    /// <summary>
    /// The zero-argument property cache is the one evaluator object a host may legitimately
    /// carry across runs. A run that faulted while a cache entry was in flight must leave it
    /// usable: the next run through that same cache must agree with a fresh one, in value
    /// and in accounting.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void FaultedRun_DoesNotContaminateAReusableCache(bool cancellation)
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        Func<Exception> fault = cancellation
            ? () => new OperationCanceledException(cts.Token)
            : () => new InvalidOperationException("fault-injection");

        const string Probe = "A = B\nB = C\nC = 41\nA + 1";
        var limits = new EvaluationLimits { MaxDepth = 16 };

        var (freshResult, freshBudget) = Evaluator.RunCountedObserved(
            Ast(Probe), limits, zeroArgPropertyResultCache: new RunScopedZeroArgPropertyResultCache());
        Assert.False(freshResult.IsError);

        // Same cache instance: first a run faulted mid-computation, then the probe.
        var shared = new RunScopedZeroArgPropertyResultCache();
        var faulting = new FaultingZeroArgPropertyResultCache(
            shared, 3, fault, FaultSite.InsideCachedEvaluation);
        Assert.Throws(
            cancellation ? typeof(OperationCanceledException) : typeof(InvalidOperationException),
            () => Evaluator.RunCountedObserved(Ast(Probe), limits, zeroArgPropertyResultCache: faulting));
        AssertConserved(faulting.ObservedBudget!, "faulted run through a shared cache");

        var (reusedResult, reusedBudget) = Evaluator.RunCountedObserved(
            Ast(Probe), limits, zeroArgPropertyResultCache: shared);
        Assert.False(reusedResult.IsError);
        Assert.Equal(freshResult.Value.Value, reusedResult.Value.Value);
        Assert.Equal(freshBudget.ConsumedSteps, reusedBudget.ConsumedSteps);
        Assert.Equal(freshBudget.PeakDepth, reusedBudget.PeakDepth);
        AssertConserved(reusedBudget, "run reusing a cache a faulted run touched");
    }

    /// <summary>
    /// The reverse order, which would expose a cache that keeps a completed entry keyed
    /// without run identity: success first, then a faulted run, then the probe again.
    /// </summary>
    [Fact]
    public void SuccessThenFaultThenSuccess_AgreesWithAFreshCache()
    {
        const string Probe = "A = B\nB = C\nC = 41\nA + 1";
        var limits = new EvaluationLimits { MaxDepth = 16 };
        var shared = new RunScopedZeroArgPropertyResultCache();

        var (firstResult, firstBudget) = Evaluator.RunCountedObserved(
            Ast(Probe), limits, zeroArgPropertyResultCache: shared);
        Assert.False(firstResult.IsError);

        var faulting = new FaultingZeroArgPropertyResultCache(
            shared, 2, () => new InvalidOperationException("fault-injection"),
            FaultSite.InsideCachedEvaluation);
        Assert.Throws<InvalidOperationException>(
            () => Evaluator.RunCountedObserved(Ast(Probe), limits, zeroArgPropertyResultCache: faulting));

        var (lastResult, lastBudget) = Evaluator.RunCountedObserved(
            Ast(Probe), limits, zeroArgPropertyResultCache: shared);
        Assert.False(lastResult.IsError);
        Assert.Equal(firstResult.Value.Value, lastResult.Value.Value);
        Assert.Equal(firstBudget.ConsumedSteps, lastBudget.ConsumedSteps);
        Assert.Equal(firstBudget.PeakDepth, lastBudget.PeakDepth);
    }

    // ── J. Concurrency isolation ─────────────────────────────────────────────

    /// <summary>
    /// Scoped accounting lives in per-run objects, never in ambient or thread-local state.
    /// A run failing deep on one thread cannot change an exact-boundary run on another.
    /// </summary>
    [Fact]
    public void ConcurrentFailingRuns_DoNotChangeAnExactBoundaryRun()
    {
        var boundaryProgram = $"{CountDown}f(6)";
        var boundary = Evaluator.RunCountedObserved(Ast(boundaryProgram)).Budget.PeakDepth;
        var shared = new EvaluationLimits { MaxDepth = boundary, MaxSteps = 5_000 };
        var boundaryAst = Ast(boundaryProgram);
        var failingAst = Ast("A = A\nA");
        var expected = Evaluator.Run(boundaryAst, shared);
        Assert.False(expected.IsError);

        Parallel.For(0, 64, i =>
        {
            if (i % 2 == 0)
            {
                Assert.True(Evaluator.Run(failingAst, shared).IsError);
                return;
            }

            var actual = Evaluator.Run(boundaryAst, shared);
            Assert.False(actual.IsError);
            Assert.Equal(expected.Value, actual.Value);
        });
    }

    private static EvalError Innermost(EvalError error)
        => error is EvalError.WithContext(_, var inner) ? Innermost(inner) : error;
}
