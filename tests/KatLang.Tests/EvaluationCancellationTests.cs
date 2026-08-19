using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// Cooperative host cancellation of EVALUATION via
/// <see cref="RunOptions.EvaluationCancellationToken"/> and the evaluator entry-point
/// token overloads. The token lives on the run-scoped <see cref="EvaluationBudget"/> and
/// is observed at the existing budget chokepoints plus the optimized loop executor's
/// per-iteration observation and the evaluator entry points' completion boundary, so
/// these tests pin four contracts:
///
/// <list type="number">
/// <item>An already-cancelled token prevents evaluation from starting, at every entry
/// point, and cancellation escapes as <see cref="OperationCanceledException"/> carrying
/// the supplied token — never a structured <see cref="EvalError"/>, never a
/// <see cref="KatLangException"/>, and never a retained binding error.</item>
/// <item>Cancellation requested MID-RUN is observed at the next chokepoint or before
/// completion — through recursion, generic and optimized loops, eager argument
/// evaluation, and with no opt-in limits configured — and the scoped depth protocol
/// stays conserved on the unwind.</item>
/// <item>An UNCANCELLED token is inert: identical results, error kinds, and budget
/// counters/verdicts as a run with no token at all.</item>
/// <item>Concurrent cancelled and uncancelled runs sharing one AST and one limits
/// instance stay isolated.</item>
/// </list>
///
/// <para><b>Determinism.</b> Mid-run cancellation is triggered from INSIDE the run via
/// the <see cref="IZeroArgPropertyResultCache"/> seam: the wrapper CANCELS the token
/// source at the k-th property access and then proceeds normally, so the
/// <see cref="OperationCanceledException"/> these tests observe is thrown by the
/// EVALUATOR's own token observation, not by the injected fault — the complement of
/// <see cref="BudgetConservationTests"/> section D, where the cache throws the exception
/// itself. A second wrapper cancels after a final property result has been produced to
/// pin the completion observation. No test depends on wall-clock timing, and every test
/// fails in bounded time if observation regresses (finite loops / finite recursion).</para>
/// </summary>
public class EvaluationCancellationTests
{
    private static Expr Ast(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    /// <summary>
    /// Wraps a real cache; CANCELS <paramref name="cts"/> at the k-th zero-argument
    /// property access and then delegates unchanged, so evaluation continues until the
    /// evaluator's own next chokepoint observes the token. Captures the run's live
    /// budget from the execution's run identity, like the conservation suite.
    /// </summary>
    private sealed class CancellingZeroArgPropertyResultCache(
        IZeroArgPropertyResultCache inner,
        int cancelAtAccess,
        CancellationTokenSource cts) : IZeroArgPropertyResultCache
    {
        private int _accesses;

        public EvaluationBudget? ObservedBudget { get; private set; }

        public int Accesses => _accesses;

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            ObservedBudget = (EvaluationBudget)execution.RunIdentity;
            if (++_accesses == cancelAtAccess)
                cts.Cancel();

            return inner.GetOrEvaluate(execution, evaluate);
        }
    }

    /// <summary>
    /// Cancels only AFTER the selected property access has produced its result. This
    /// creates a deterministic cancellation at the completion edge of an evaluator
    /// operation, with no injected exception and no guarantee of a later charging
    /// checkpoint inside the expression being evaluated.
    /// </summary>
    private sealed class CancellingAfterZeroArgPropertyResultCache(
        IZeroArgPropertyResultCache inner,
        int cancelAfterAccess,
        CancellationTokenSource cts) : IZeroArgPropertyResultCache
    {
        public int Accesses { get; private set; }

        public EvaluationBudget? ObservedBudget { get; private set; }

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            ObservedBudget = (EvaluationBudget)execution.RunIdentity;
            var result = inner.GetOrEvaluate(execution, evaluate);
            if (++Accesses == cancelAfterAccess)
                cts.Cancel();

            return result;
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
    /// Runs <paramref name="source"/> with the budget carrying <paramref name="cts"/>'s
    /// token and the cache cancelling that source at the k-th property access. Asserts
    /// the run escapes with an <see cref="OperationCanceledException"/> carrying exactly
    /// the supplied token, and returns the run's live budget for conservation asserts.
    /// </summary>
    private static EvaluationBudget RunCancelling(
        string source,
        int cancelAtAccess,
        CancellationTokenSource cts,
        EvaluationLimits? limits = null,
        bool enableOptimizations = true)
    {
        var cache = new CancellingZeroArgPropertyResultCache(
            new RunScopedZeroArgPropertyResultCache(), cancelAtAccess, cts);

        var thrown = Assert.Throws<OperationCanceledException>(() =>
            Evaluator.RunCountedObserved(
                Ast(source),
                limits,
                enableOptimizations,
                cache,
                cancellationToken: cts.Token));

        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.True(
            cache.Accesses >= cancelAtAccess,
            $"cancellation was configured for access {cancelAtAccess} but only {cache.Accesses} occurred");
        Assert.NotNull(cache.ObservedBudget);
        return cache.ObservedBudget!;
    }

    /// <summary>
    /// The scoped depth protocol is conserved after a cancellation unwind. The
    /// conservation suite's capacity re-probe is deliberately NOT used here: this
    /// budget's own token is cancelled, so every further enter would itself throw. A
    /// leak still shows as <c>CurrentDepth != 0</c>, and a double release cannot hide —
    /// <see cref="EvaluationBudget.ExitInvocation"/> is fail-loud on underflow, so it
    /// would surface as an <see cref="InvalidOperationException"/> and fail the
    /// exact-type <see cref="OperationCanceledException"/> assertion first.
    /// </summary>
    private static void AssertConservedAfterCancellation(EvaluationBudget budget, string what)
    {
        Assert.True(budget.CurrentDepth == 0, $"{what}: leaked {budget.CurrentDepth} depth level(s)");
        Assert.True(
            budget.PeakDepth <= budget.MaxDepth,
            $"{what}: PeakDepth {budget.PeakDepth} exceeded MaxDepth {budget.MaxDepth}");
    }

    // ── A. Already-cancelled token prevents evaluation from starting ─────────

    [Fact]
    public void AlreadyCancelledToken_PreventsEvaluation_AtTheEvaluatorEntryPoints()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        var ast = Ast("A = 1\nA + 1");

        var fromRun = Assert.Throws<OperationCanceledException>(
            () => Evaluator.Run(ast, limits: null, cts.Token));
        Assert.Equal(cts.Token, fromRun.CancellationToken);

        var fromRunFlat = Assert.Throws<OperationCanceledException>(
            () => Evaluator.RunFlat(ast, limits: null, cts.Token));
        Assert.Equal(cts.Token, fromRunFlat.CancellationToken);

        var fromCounted = Assert.Throws<OperationCanceledException>(() =>
            Evaluator.RunCounted(
                ast,
                new RunScopedZeroArgPropertyResultCache(),
                limits: null,
                cts.Token));
        Assert.Equal(cts.Token, fromCounted.CancellationToken);

        var fromCountedWithTopLevelProperty = Assert.Throws<OperationCanceledException>(() =>
            Evaluator.RunCountedWithTopLevelProperty(
                ast,
                "A",
                new RunScopedZeroArgPropertyResultCache(),
                limits: null,
                cts.Token));
        Assert.Equal(cts.Token, fromCountedWithTopLevelProperty.CancellationToken);
    }

    /// <summary>
    /// "Prevents starting" means NOTHING ran: no property access happened and no budget
    /// counter moved, not merely that the run eventually failed.
    /// </summary>
    [Fact]
    public void AlreadyCancelledToken_EvaluatesNothing()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        var counting = new CountingZeroArgPropertyResultCache(new RunScopedZeroArgPropertyResultCache());

        Assert.Throws<OperationCanceledException>(() =>
            Evaluator.RunCountedObserved(
                Ast("A = 1\nA + 1"),
                zeroArgPropertyResultCache: counting,
                cancellationToken: cts.Token));

        Assert.Equal(0, counting.Accesses);
    }

    [Fact]
    public void AlreadyCancelledEvaluationToken_ThrowsFromEveryEngineEntryPoint()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        var options = new RunOptions { EvaluationCancellationToken = cts.Token };

        var fromRun = Assert.Throws<OperationCanceledException>(() => KatLangEngine.Run("1 + 1", options));
        Assert.Equal(cts.Token, fromRun.CancellationToken);

        // Cancellation must escape, never become a KatLangException or an error string.
        var fromAtoms = Assert.Throws<OperationCanceledException>(
            () => KatLangEngine.EvaluateToAtoms("1 + 1", options));
        Assert.Equal(cts.Token, fromAtoms.CancellationToken);

        var fromString = Assert.Throws<OperationCanceledException>(
            () => KatLangEngine.EvaluateToString("1 + 1", options));
        Assert.Equal(cts.Token, fromString.CancellationToken);
    }

    [Fact]
    public void SourceProcessingAndEvaluationTokens_RemainIndependent()
    {
        using var sourceCts = new CancellationTokenSource();
        using var evaluationCts = new CancellationTokenSource();
        sourceCts.Cancel();

        var thrown = Assert.Throws<OperationCanceledException>(() =>
            KatLangEngine.Run(
                "1 + 1",
                new RunOptions
                {
                    SourceProcessingCancellationToken = sourceCts.Token,
                    EvaluationCancellationToken = evaluationCts.Token,
                }));

        Assert.Equal(sourceCts.Token, thrown.CancellationToken);
        Assert.False(evaluationCts.IsCancellationRequested);
    }

    /// <summary>
    /// The two tokens stay separate: the evaluation token governs evaluation only, so a
    /// program that never reaches evaluation returns its parse failure normally, and an
    /// unconfigured source-processing token is untouched by the evaluation one.
    /// </summary>
    [Fact]
    public void CancelledEvaluationToken_DoesNotAffectFrontEndOutcomes()
    {
        using var cts = new CancellationTokenSource();
        cts.Cancel();
        var options = new RunOptions { EvaluationCancellationToken = cts.Token };

        var result = KatLangEngine.Run("1 +", options);
        Assert.IsType<RunResult.ParseFailure>(result);
    }

    // ── B. Cancellation observed mid-run ─────────────────────────────────────

    /// <summary>
    /// Cancellation lands at the bottom of a 41-level recursion (the trigger property is
    /// read by <c>f(0)</c>), with DEFAULT limits — no opt-in budget configured — and the
    /// second <c>f(40)</c> never runs. Covers: long-running evaluation, nested-call
    /// unwind conservation, and cancellation with evaluation limits disabled.
    /// </summary>
    [Fact]
    public void CancellationDeepInRecursion_UnderDefaultLimits_EscapesAndConserves()
    {
        using var cts = new CancellationTokenSource();

        var budget = RunCancelling(
            "f(0) = Trigger\nTrigger = 1\nf(n) = f(n - 1)\nf(40) + f(40)",
            cancelAtAccess: 1,
            cts);

        Assert.True(budget.PeakDepth >= 41, $"expected the recursion to be live, peak was {budget.PeakDepth}");
        AssertConservedAfterCancellation(budget, "cancellation under a 41-level recursion");
    }

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(3)]
    public void CancellationAtEveryPropertyNestingLevel_EscapesAndConserves(int cancelAtAccess)
    {
        using var cts = new CancellationTokenSource();

        var budget = RunCancelling(
            "A = B\nB = C\nC = 1\nA",
            cancelAtAccess,
            cts,
            new EvaluationLimits { MaxDepth = 12 });

        AssertConservedAfterCancellation(budget, $"cancellation at property nesting level {cancelAtAccess}");
    }

    /// <summary>
    /// Regression for a missing final observation: the sole output row is a one-slot
    /// property value, so after the cache returns there is no collection reservation or
    /// other charging chokepoint. Cancellation requested by that final operation must
    /// still preempt successful completion.
    /// </summary>
    [Fact]
    public void CancellationRequestedByTheFinalOperation_IsObservedBeforeCompletion()
    {
        using var cts = new CancellationTokenSource();
        var cache = new CancellingAfterZeroArgPropertyResultCache(
            new RunScopedZeroArgPropertyResultCache(),
            cancelAfterAccess: 1,
            cts);

        var thrown = Assert.Throws<OperationCanceledException>(() =>
            Evaluator.RunCountedObserved(
                Ast("A = 1\nA"),
                zeroArgPropertyResultCache: cache,
                cancellationToken: cts.Token));

        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.Equal(1, cache.Accesses);
        Assert.NotNull(cache.ObservedBudget);
        AssertConservedAfterCancellation(
            cache.ObservedBudget!,
            "cancellation requested by the final property operation");
    }

    /// <summary>
    /// A generic `while` observes a token cancelled at the 50th iteration (the step body
    /// reads a property each iteration). The loop is finite, so a broken observation
    /// fails the test in bounded time instead of hanging.
    /// </summary>
    [Fact]
    public void CancellationDuringGenericWhileLoop_EscapesAndConserves()
    {
        using var cts = new CancellationTokenSource();

        var budget = RunCancelling(
            "K = 1\nS(n) = n + K, n < 50000\nwhile(S, 0)",
            cancelAtAccess: 50,
            cts,
            enableOptimizations: false);

        AssertConservedAfterCancellation(budget, "cancellation inside a generic while loop");
    }

    [Fact]
    public void CancellationDuringGenericRepeatLoop_EscapesAndConserves()
    {
        using var cts = new CancellationTokenSource();

        var budget = RunCancelling(
            "K = 1\nS(n) = n + K\nrepeat(S, 50000, 0)",
            cancelAtAccess: 50,
            cts,
            enableOptimizations: false);

        AssertConservedAfterCancellation(budget, "cancellation inside a generic repeat loop");
    }

    /// <summary>
    /// End-to-end: a large OPTIMIZED repeat under default limits is cancellable. The
    /// trigger property is its own output row evaluated BEFORE the loop row (a builtin
    /// call ARGUMENT would bypass the zero-argument property cache and never fire the
    /// trigger), so the multi-million-iteration fully-planned loop must stop at a
    /// cancellation observation rather than running to completion. If observation
    /// regressed everywhere, the loop finishes in bounded time and the missing
    /// exception fails the test.
    /// </summary>
    [Fact]
    public void CancellationBeforeALargeOptimizedRepeat_StopsTheLoop()
    {
        using var cts = new CancellationTokenSource();

        RunCancelling(
            "S(n) = n + 1\nTrigger = 0\nTrigger\nrepeat(S, 5000000, 0)",
            cancelAtAccess: 1,
            cts,
            enableOptimizations: true);
    }

    /// <summary>
    /// Pins the observation point the end-to-end test cannot isolate: the OPTIMIZED loop
    /// executor observes the token at each iteration head. Fully-planned iterations
    /// touch no charging chokepoint (and this path never runs under a step budget), so
    /// without this observation a fused <c>repeat(S, huge, 0)</c> would be
    /// un-cancellable exactly when no limits are configured.
    /// </summary>
    [Fact]
    public void OptimizedRepeatExecutor_ObservesTheTokenPerIteration()
    {
        var step = SourceProvenance.ParseValid("S(n) = n + 1\nS(0)")
            .Root.Properties.Single(p => p.Name == "S").Value;

        using var cancelled = new CancellationTokenSource();
        cancelled.Cancel();
        var cancelledCtx = Evaluator.EvalCtx.Empty with
        {
            Budget = EvaluationBudget.Create(null, cancelled.Token),
        };

        var thrown = Assert.Throws<OperationCanceledException>(() =>
            LoopOptimizer.TryEvaluateRepeat(
                step,
                count: 10,
                [new Result.Atom(0)],
                cancelledCtx,
                [],
                (_, _) => throw new Xunit.Sdk.XunitException("generic continuation must not run"),
                out _));
        Assert.Equal(cancelled.Token, thrown.CancellationToken);

        // Control: the same direct call with an uncancelled token completes normally,
        // proving the throw above came from token observation, not from the harness.
        using var live = new CancellationTokenSource();
        var liveCtx = Evaluator.EvalCtx.Empty with
        {
            Budget = EvaluationBudget.Create(null, live.Token),
        };
        var handled = LoopOptimizer.TryEvaluateRepeat(
            step,
            count: 10,
            [new Result.Atom(0)],
            liveCtx,
            [],
            (_, _) => throw new Xunit.Sdk.XunitException("generic continuation must not run"),
            out var result);
        Assert.True(handled);
        Assert.False(result.IsError);
        Assert.Equal(new Result.Atom(10), result.Value.Value);
    }

    [Fact]
    public void OptimizedWhileExecutor_ObservesTheTokenPerIteration()
    {
        var step = SourceProvenance.ParseValid("S(n) = n + 1, n < 3\nS(0)")
            .Root.Properties.Single(p => p.Name == "S").Value;

        using var cancelled = new CancellationTokenSource();
        cancelled.Cancel();
        var ctx = Evaluator.EvalCtx.Empty with
        {
            Budget = EvaluationBudget.Create(null, cancelled.Token),
        };

        var thrown = Assert.Throws<OperationCanceledException>(() =>
            LoopOptimizer.TryEvaluateWhile(
                step,
                [new Result.Atom(0)],
                ctx,
                [],
                _ => throw new Xunit.Sdk.XunitException("generic continuation must not run"),
                out _));
        Assert.Equal(cancelled.Token, thrown.CancellationToken);
    }

    // ── C. Cancellation is never retained as a binding error ─────────────────

    /// <summary>
    /// THE retention trap. In this shape a RESOURCE-LIMIT failure of the eager argument
    /// evaluation is retained on the binding and the run SUCCEEDS with 10
    /// (<see cref="BudgetConservationTests.AbsorbedDepthRejection_DoesNotConsumeAStep"/>);
    /// a cancellation observed during the same eager evaluation must instead escape as
    /// <see cref="OperationCanceledException"/> — a cancelled run does not continue.
    /// </summary>
    [Fact]
    public void CancellationDuringEagerArgumentEvaluation_EscapesInsteadOfBeingRetained()
    {
        const string Program = "G(f) = 1\nA = A\nH = 9\nG(A) + H()";
        var limits = new EvaluationLimits { MaxDepth = 3 };

        // Control: the depth-limit refusal of A's eager value IS retained; the run
        // completes with 10. This is the exact behavior cancellation must not share.
        var retained = Evaluator.Run(Ast(Program), limits);
        Assert.False(retained.IsError);

        // Same program, same limits, but the token is cancelled while A's eager value
        // evaluation recurses (A = A reaches itself through the property cache).
        using var cts = new CancellationTokenSource();
        var budget = RunCancelling(Program, cancelAtAccess: 2, cts, limits);
        AssertConservedAfterCancellation(budget, "cancellation during eager argument evaluation");
    }

    [Fact]
    public void CancellationEscapesFromEngineAdditionalErrorEvaluation()
    {
        const string Source = """
            A = load('https://katlang.org/cancellation/not-katlang.kat')
            Use(z) = A.X
            Use(0)
            """;

        using var cts = new CancellationTokenSource();
        cts.Cancel();
        var options = new RunOptions
        {
            EvaluationCancellationToken = cts.Token,
            DownloadCode = _ => "<!doctype html><html><body>Not found</body></html>",
        };

        var thrown = Assert.Throws<OperationCanceledException>(() =>
            KatLangEngine.Run(Source, options));

        Assert.Equal(cts.Token, thrown.CancellationToken);
    }

    // ── D. An uncancelled token is inert ─────────────────────────────────────

    public static TheoryData<string, EvaluationLimits?> InertTokenCorpus()
    {
        var data = new TheoryData<string, EvaluationLimits?>();

        string[] programs =
        [
            "1 + 1",
            "f(0) = 0\nf(n) = f(n - 1)\nf(6)",
            "A = count(A)\nA",
            "range(1, 6).filter(P).count\nP(x) = x > 2",
            "(1, 2, 3).map(F).sum\nF(x) = x * 2",
            "1 / 0",
            "Missing",
            "while(S, 4)\nS(n) = n + 1, n < 3",
            "repeat(S, 4, 0)\nS(n) = n + 1",
            "'abc'.string",
        ];

        EvaluationLimits?[] configurations =
        [
            null,
            new EvaluationLimits { MaxDepth = 3 },
            new EvaluationLimits { MaxSteps = 4 },
            new EvaluationLimits { MaxCollectionItems = 1 },
            new EvaluationLimits { MaxStringLength = 1 },
        ];

        foreach (var program in programs)
        {
            foreach (var configuration in configurations)
                data.Add(program, configuration);
        }

        return data;
    }

    /// <summary>
    /// A present-but-never-cancelled token changes NOTHING: same success/error outcome,
    /// same error kind, same value, and the same operational counters — so no budget
    /// verdict can depend on whether a token was supplied (the cross-talk rule the
    /// budget suite pins for the opt-in limits, extended to the token).
    /// </summary>
    [Theory]
    [MemberData(nameof(InertTokenCorpus))]
    public void UncancelledToken_ProducesIdenticalResultsAndBudgetVerdicts(
        string program, EvaluationLimits? limits)
    {
        using var cts = new CancellationTokenSource();

        foreach (var optimizations in new[] { false, true })
        {
            var (bare, bareBudget) = Evaluator.RunCountedObserved(
                Ast(program), limits, enableOptimizations: optimizations);
            var (tokened, tokenedBudget) = Evaluator.RunCountedObserved(
                Ast(program), limits, enableOptimizations: optimizations, cancellationToken: cts.Token);

            Assert.Equal(bare.IsError, tokened.IsError);
            if (bare.IsError)
            {
                // Record equality is unusable for errors carrying list payloads
                // (reference-compared members), so compare the error SHAPE — outer and
                // innermost kinds — plus the fully rendered message, which spells out
                // every payload.
                Assert.Equal(bare.Error.GetType(), tokened.Error.GetType());
                Assert.Equal(Innermost(bare.Error).GetType(), Innermost(tokened.Error).GetType());
                Assert.Equal(
                    KatLangError.FromEvalError(bare.Error).Message,
                    KatLangError.FromEvalError(tokened.Error).Message);
            }
            else
            {
                Assert.Equal(bare.Value, tokened.Value);
            }

            Assert.Equal(bareBudget.ConsumedSteps, tokenedBudget.ConsumedSteps);
            Assert.Equal(bareBudget.PeakDepth, tokenedBudget.PeakDepth);
            Assert.Equal(bareBudget.MaterializedItems, tokenedBudget.MaterializedItems);
            Assert.Equal(bareBudget.MaterializedStringChars, tokenedBudget.MaterializedStringChars);
        }
    }

    [Fact]
    public void UncancelledToken_IsInertAtThePublicEngine()
    {
        using var cts = new CancellationTokenSource();
        const string Program = "DisplayDecimals = 2\nf(0) = 0\nf(n) = f(n - 1)\n1 / 3, f(6)";

        var bare = KatLangEngine.Run(Program);
        var tokened = KatLangEngine.Run(
            Program, new RunOptions { EvaluationCancellationToken = cts.Token });

        Assert.Equal(bare.ToDisplayString(), tokened.ToDisplayString());
    }

    // ── E. Concurrent cancelled and uncancelled runs stay isolated ───────────

    /// <summary>
    /// One shared AST and one shared limits instance across overlapping runs: cancelled
    /// runs throw their own token, uncancelled runs produce the untouched result, and
    /// mid-run cancellations conserve their own budget — nothing leaks across runs.
    /// </summary>
    [Fact]
    public void OverlappingCancelledAndUncancelledRuns_StayIsolated()
    {
        const string Program = "A = B\nB = C\nC = 41\nA + 1";
        var sharedAst = Ast(Program);
        var sharedLimits = new EvaluationLimits { MaxDepth = 16 };

        var expected = Evaluator.Run(sharedAst, sharedLimits);
        Assert.False(expected.IsError);

        Parallel.For(0, 48, i =>
        {
            switch (i % 3)
            {
                case 0:
                    // Pre-cancelled run: throws its own token, evaluates nothing.
                    using (var cts = new CancellationTokenSource())
                    {
                        cts.Cancel();
                        var thrown = Assert.Throws<OperationCanceledException>(
                            () => Evaluator.Run(sharedAst, sharedLimits, cts.Token));
                        Assert.Equal(cts.Token, thrown.CancellationToken);
                    }

                    break;
                case 1:
                    // Mid-run cancellation with its own run-scoped budget and cache.
                    using (var cts = new CancellationTokenSource())
                    {
                        var budget = RunCancelling(Program, cancelAtAccess: 2, cts, sharedLimits);
                        AssertConservedAfterCancellation(budget, "concurrent mid-run cancellation");
                    }

                    break;
                default:
                    // Untouched run: no token, full result.
                    var actual = Evaluator.Run(sharedAst, sharedLimits);
                    Assert.False(actual.IsError);
                    Assert.Equal(expected.Value, actual.Value);
                    break;
            }
        });
    }

    private static EvalError Innermost(EvalError error)
        => error is EvalError.WithContext(_, var inner) ? Innermost(inner) : error;
}
