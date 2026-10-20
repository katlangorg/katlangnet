using KatLang.Evaluation;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// F7-D6: the planned loop's step-shape gate (<c>Evaluator.IsOptimizedLoopShapeEligible</c>) fails
/// CLOSED. A user step is planned only when its binding plan is BUILT and shows flat fixed captures
/// with distinct names. A plan that cannot be built is no evidence of eligibility, so the loop runs
/// the generic route and records <see cref="PlanUnavailable"/>.
///
/// <para>Until the repair a failed plan counted as ELIGIBLE. The helper caught the plan
/// constructor's <see cref="InvalidOperationException"/> and returned <c>null</c>, the same value it
/// returned for a step that is not a user algorithm, and the gate read <c>null</c> as "eligible". The
/// planner compares only the flattened capture count with the state arity, so it planned the step
/// and bound every capture by position as a plain value.</para>
///
/// <para>The plan constructor refuses a pattern level with two collecting captures. The
/// pre-evaluation gate refuses that head on every algorithm it validates (X-02), so no written
/// program reaches the refusal. A host-built AST did, by two routes (<see cref="Trigger"/>):
/// <list type="bullet">
/// <item>A host operation rewrites a caller-owned pattern list after the gate. This breaks the host
/// contract for ASTs, and it still reaches the planner.</item>
/// <item>A step is stored in a host-built parent scope. The gate did not examine such scopes until
/// they were brought under the pre-evaluation rules (owner decision, 2026-10-12), so this route is
/// now refused before evaluation (section 6).</item>
/// </list>
/// The failure-path tests use the first route. They pin robustness, not a language rule. The oracle
/// is the GENERIC route of the same program. With the plan unavailable, the optimizing run must be exactly the run with
/// optimization disabled: the same value or error, the same host calls, and every budget counter
/// equal. Of the failure-path tests, the synchronous comparisons, the stale-facts test and the
/// nested-head cancellation rows fail on the pre-repair code. The async-twin rows and the
/// top-level-head cancellation rows are parity checks: they pass before and after the repair.</para>
///
/// <para>The controls pin what must NOT change:
/// <list type="bullet">
/// <item>Valid flat fixed steps stay planned, including steps whose signature is a shared lifted
/// template.</item>
/// <item>The valid collecting, structural and repeated-name steps keep their "variadic loop step"
/// fallback.</item>
/// <item>Every other callable shape still reaches the planner, which refuses it (Q-23).</item>
/// <item>A zero-iteration <c>repeat</c> never decides eligibility at all (LOOP-05).</item>
/// </list></para>
/// </summary>
public class LoopPlanEligibilityFailClosedTests
{
    private const string PlanUnavailable = "loop step binding plan unavailable";
    private const string VariadicStep = "variadic loop step";
    private const string UnsupportedShape = "loop plan unsupported step shape";
    private const string OptimizationDisabled = "loop optimization disabled";

    internal sealed record Budget(long Steps, long Checkpoints, int PeakDepth, long MaterializedItems, long MaterializedStringChars)
    {
        public static Budget Of(EvaluationBudget budget)
            => new(budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth,
                budget.MaterializedItems, budget.MaterializedStringChars);
    }

    private sealed record Run(
        string Outcome,
        string Error,
        Budget Budget,
        LoopOptimizationDiagnosticsSnapshot Loops,
        long GenericPreparations,
        IReadOnlyList<string> HostCalls);

    // ── 1. The failure path: a plan that cannot be built is never planned ──────────────────────

    /// <summary>
    /// How a host-built AST brought an invalid head to the loop although the pre-evaluation gate
    /// refuses it. Only <see cref="HostMutation"/> still reaches the loop.
    /// </summary>
    public enum Trigger
    {
        /// <summary>A host operation rewrites the step's caller-owned head after the gate read it.</summary>
        HostMutation,

        /// <summary>
        /// The step is stored in a host-built <see cref="ScopeCtx"/>, the parent of an
        /// <c>open { … }</c> block. The pre-evaluation walker validates such scopes since
        /// 2026-10-12, so this program is refused before evaluation and never reaches a loop
        /// (section 6; <see cref="HostBuiltParentScopeValidationTests"/>).
        /// </summary>
        HostScope,
    }

    /// <summary>The invalid heads. Each is refused by the plan constructor and by X-02.</summary>
    public enum InvalidHead
    {
        /// <summary><c>Step(*a, *b)</c>: two collecting captures at the top level.</summary>
        TwoTopLevelCollectors,

        /// <summary><c>Step((*a, *b))</c>: two collecting captures in one sequence pattern.</summary>
        TwoNestedCollectors,
    }

    private static ParameterPattern[] Head(InvalidHead head)
    {
        var a = new CaptureParameterPattern("a", Kind: ParameterKind.Collecting);
        var b = new CaptureParameterPattern("b", Kind: ParameterKind.Collecting);
        return head switch
        {
            InvalidHead.TwoTopLevelCollectors => [a, b],
            InvalidHead.TwoNestedCollectors => [new SequenceValueParameterPattern([a, b])],
            _ => throw new ArgumentOutOfRangeException(nameof(head), head, null),
        };
    }

    /// <summary>
    /// The plan constructor itself refuses both heads, so a gate that reaches it really takes the
    /// failure branch, and the pre-evaluation validator refuses them too. A wrong head here would make
    /// every failure-path test vacuous.
    /// </summary>
    [Theory]
    [InlineData(InvalidHead.TwoTopLevelCollectors)]
    [InlineData(InvalidHead.TwoNestedCollectors)]
    public void InvalidHead_CannotBuildALoopStepBindingPlan(InvalidHead head)
    {
        var step = new Algorithm.User(Parent: null, ParameterPatterns: Head(head), Opens: [], Properties: [],
            Output: [new Expr.Param("a"), new Expr.Param("b")]);

        Assert.Throws<InvalidOperationException>(
            () => CallableBindingPlan.FromSignature(CallableSignature.FromUserAlgorithm("loop step", step)));
        Assert.NotNull(ParameterPattern.FindSignatureViolation(step.ParameterPatterns));
    }

    /// <summary>
    /// The generic route's own outcomes, written by hand from the binder's allocation rule. A level
    /// with two collecting captures gives the FIRST collector the slice the other pattern leaves, and
    /// the later collector one cell (<c>Evaluator.NeedSourceRange</c>), so <c>Step(*a, *b)</c> over
    /// <c>10, 20</c> binds <c>a = [10]</c>, <c>b = 20</c>. One sequence pattern is one supplied slot,
    /// so <c>Step((*a, *b))</c> refuses two state values with the loop-state arity error. The
    /// fail-open planner bound <c>a = 10</c>, <c>b = 20</c> in every case: a different value, or a
    /// success where the generic route reports an error.
    /// </summary>
    public static TheoryData<string, InvalidHead, string> FailurePathCases => new()
    {
        { "repeat", InvalidHead.TwoTopLevelCollectors, "ok S[L[10], 20]" },
        { "while", InvalidHead.TwoTopLevelCollectors, "ok S[L[10], 20]" },
        { "repeat", InvalidHead.TwoNestedCollectors, "err ArityMismatch" },
        { "while", InvalidHead.TwoNestedCollectors, "err ArityMismatch" },
    };

    [Theory]
    [MemberData(nameof(FailurePathCases))]
    public void UnbuildablePlan_RunsTheGenericRoute_ExactlyAsWithOptimizationDisabled(
        string loop, InvalidHead head, string expected)
    {
        var generic = RunScenario(loop, head, optimize: false);
        var optimizing = RunScenario(loop, head, optimize: true);

        Assert.Equal(expected, generic.Outcome);
        Assert.Equal(generic.Outcome, optimizing.Outcome);
        Assert.Equal(generic.Error, optimizing.Error);
        Assert.Equal(generic.HostCalls, optimizing.HostCalls);
        Assert.Equal(generic.Budget, optimizing.Budget);

        // The failure branch was taken, and it is the only thing that happened: the planner was never
        // consulted, nothing was planned, and the generic step binding was prepared once.
        Assert.Equal(0, optimizing.Loops.OptimizedLoopHits);
        Assert.Equal(0, optimizing.Loops.LoopPlanBuilds);
        Assert.Empty(optimizing.Loops.LoopPlans);
        Assert.Equal(1, optimizing.Loops.OptimizedLoopFallbacks);
        AssertOnlyReason(optimizing.Loops.FallbackReasons, PlanUnavailable);
        Assert.Equal(1, optimizing.GenericPreparations);
        Assert.Equal(1, generic.GenericPreparations);

        // The reshaping host operation ran exactly once per run: the fallback re-evaluates nothing.
        Assert.Equal(1, optimizing.HostCalls.Count(static call => call == "reshape"));
    }

    /// <summary>
    /// A DIFFERENT refusal of the plan constructor: signature facts that disagree with the patterns.
    /// No program produces it. A host can reach it only through a pattern list whose own reads
    /// disagree, such as an enumerator that disagrees with the indexer, or a concurrent writer. This
    /// test forces it instead through a shared signature template whose cached facts no longer
    /// describe its content: it writes into the array the template took ownership of
    /// (<c>ImplicitSignatureTemplate.Flat</c> does not copy it), after the facts were computed.
    /// <para>The facts were computed from <c>(a, b)</c>, so the cached top-level collector count is
    /// zero. The content is now the valid <c>(a, *b)</c>. The template's parameters are derived lazily
    /// from the live array, while its collector count was fixed when the facts were built. The
    /// constructor's arity-facts agreement check therefore refuses the step, so the gate fails
    /// closed.</para>
    /// <para>The generic route snapshots the actual patterns and binds <c>a = 10</c>,
    /// <c>b = [20]</c>. The fail-open planner admitted the step by its capture count and bound the
    /// collecting <c>b</c> by position as the plain value <c>20</c>. If the template ever copies its
    /// array or recomputes its facts, the refusal assertion below fails: update this test on purpose
    /// then.</para>
    /// </summary>
    [Fact]
    public void InconsistentSignatureMetadata_IsAnotherUnbuildablePlan_AndRunsGenerically()
    {
        static (Expr Program, Algorithm.User Step) Build()
        {
            ParameterPattern[] items = [new CaptureParameterPattern("a"), new CaptureParameterPattern("b")];
            var template = ImplicitSignatureTemplate.Flat(items);
            Assert.Equal(2, template.Facts.CaptureCount);
            items[1] = new CaptureParameterPattern("b", Kind: ParameterKind.Collecting);
            var step = new Algorithm.User(Parent: null, ParameterPatterns: template, Opens: [], Properties: [],
                Output: [new Expr.Param("a"), new Expr.Param("b")]);
            return (new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("S", step)],
                [new Expr.Call(new Expr.Resolve("repeat"),
                    [new Expr.Call(new Expr.Resolve("S"), [new Expr.Num(10), new Expr.Num(20)]), new Expr.Num(1)])])), step);
        }

        var refusal = Assert.Throws<InvalidOperationException>(
            () => CallableBindingPlan.FromSignature(CallableSignature.FromUserAlgorithm("loop step", Build().Step)));
        Assert.Contains("arity facts do not match", refusal.Message, StringComparison.Ordinal);

        var generic = RunProgram(Build().Program, optimize: false);
        var optimizing = RunProgram(Build().Program, optimize: true);

        Assert.Equal("ok S[10, L[20]]", generic.Outcome);
        Assert.Equal(generic.Outcome, optimizing.Outcome);
        Assert.Equal(generic.Budget, optimizing.Budget);
        Assert.Equal(0, optimizing.Loops.OptimizedLoopHits);
        Assert.Equal(0, optimizing.Loops.LoopPlanBuilds);
        AssertOnlyReason(optimizing.Loops.FallbackReasons, PlanUnavailable);
        Assert.Equal(1, optimizing.GenericPreparations);
    }

    /// <summary>
    /// A PARITY check, not a regression detector. The async route never plans, so these rows pass
    /// before and after the repair. They pin that a refused plan, whose construction still runs on
    /// this route before the route test, throws nothing there and changes nothing. With genuinely
    /// suspending host operations, the run still produces the synchronous generic outcome, host calls
    /// and budgets.
    /// </summary>
    [Theory]
    [MemberData(nameof(FailurePathCases))]
    public async Task UnbuildablePlan_OnTheSuspendingAsyncTwin_MatchesTheSynchronousGenericRoute(
        string loop, InvalidHead head, string expected)
    {
        var generic = RunScenario(loop, head, optimize: false);
        var scenario = new UnbuildableStepLoop(Trigger.HostMutation, loop, head, suspending: true);
        var loops = new LoopOptimizationDiagnostics();
        var observations = new EvaluationObservations();
        var cache = new SuspendingAsyncZeroArgPropertyResultCache();

        var (result, budget) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            scenario.Program,
            zeroArgPropertyResultCache: cache,
            loopDiagnostics: loops,
            observations: observations,
            hostOperations: scenario.Operations));

        Assert.Equal(expected, Outcome(result));
        Assert.Equal(generic.Error, ErrorText(result));
        Assert.Equal(generic.HostCalls, scenario.HostCalls);
        Assert.Equal(generic.Budget, Budget.Of(budget));
        Assert.Equal(0, cache.SyncAccesses);

        // The async route never plans; it records its own reason, exactly as before the repair.
        var snapshot = loops.GetSnapshot();
        Assert.Equal(0, snapshot.OptimizedLoopHits);
        Assert.Equal(0, snapshot.LoopPlanBuilds);
        AssertOnlyReason(snapshot.FallbackReasons, OptimizationDisabled);
        Assert.Equal(1, observations.GenericLoopStepBindingPreparationCount);
    }

    /// <summary>
    /// <c>flag</c> cancels the run on its first call. The two head shapes behave differently.
    /// <list type="bullet">
    /// <item>Top-level head: both routes call <c>flag</c> once, then throw
    /// <see cref="OperationCanceledException"/> with the run's token at the next iteration's step
    /// charge. These rows are parity checks. The optimizing run must still show the failure branch,
    /// whose reason is recorded before the first step charge.</item>
    /// <item>Nested head: the generic route refuses the state before the cancelling row runs. The
    /// pre-repair planner ran that row and was cancelled instead.</item>
    /// </list>
    /// </summary>
    [Theory]
    [InlineData(InvalidHead.TwoTopLevelCollectors)]
    [InlineData(InvalidHead.TwoNestedCollectors)]
    public void UnbuildablePlan_ObservesCancellationExactlyLikeTheGenericRoute(InvalidHead head)
    {
        if (head == InvalidHead.TwoNestedCollectors)
        {
            var generic = RunScenario("while", head, optimize: false, cancelOnFlag: true);
            var optimizing = RunScenario("while", head, optimize: true, cancelOnFlag: true);
            string[] refusedCalls = ["reshape"];
            Assert.Equal("err ArityMismatch", generic.Outcome);
            Assert.Equal(generic.Outcome, optimizing.Outcome);
            Assert.Equal(generic.Error, optimizing.Error);
            Assert.Equal(refusedCalls, generic.HostCalls);
            Assert.Equal(refusedCalls, optimizing.HostCalls);
            AssertOnlyReason(optimizing.Loops.FallbackReasons, PlanUnavailable);
            return;
        }

        string[] cancelledCalls = ["reshape", "flag"];
        var (genericCalls, _) = Cancelled(head, optimize: false);
        var (optimizingCalls, loops) = Cancelled(head, optimize: true);
        Assert.Equal(cancelledCalls, genericCalls);
        Assert.Equal(cancelledCalls, optimizingCalls);
        Assert.Equal(0, loops.OptimizedLoopHits);
        Assert.Equal(0, loops.LoopPlanBuilds);
        AssertOnlyReason(loops.FallbackReasons, PlanUnavailable);

        static (IReadOnlyList<string> HostCalls, LoopOptimizationDiagnosticsSnapshot Loops) Cancelled(
            InvalidHead head, bool optimize)
        {
            var scenario = new UnbuildableStepLoop(Trigger.HostMutation, "while", head, suspending: false, cancelOnFlag: true);
            var loops = new LoopOptimizationDiagnostics();
            var exception = Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(
                scenario.Program,
                enableOptimizations: optimize,
                loopDiagnostics: loops,
                hostOperations: scenario.Operations,
                cancellationToken: scenario.Cancellation.Token));
            Assert.Equal(scenario.Cancellation.Token, exception.CancellationToken);
            return (scenario.HostCalls, loops.GetSnapshot());
        }
    }

    // ── 2. Controls: valid flat fixed steps stay planned ─────────────────────────────────────

    public static TheoryData<string, string> PlannedSteps => new()
    {
        { "S(k) = k + 1\nS(0).repeat(5)", "5" },
        { "Fib(a, b) = b, a + b\nFib(0, 1).repeat(10)", "S[55, 89]" },
        { "T(a, b, c) = b, c, a + b + c\nT(1, 1, 1).repeat(4)", "S[5, 9, 17]" },
        { "Step = k + 1\nStep(0).repeat(5)", "5" },
        { "W(k) = k + 1, k < 9\nW(0).while", "9" },
        { "W(a, b) = b, a + b, b < 50\nW(0, 1).while", "S[34, 55]" },
        { "S(k) = k + 1\nA = S\nA(0).repeat(3)", "3" },
        { "Use(f) = f(0).repeat(3)\nS(k) = k + 1\nUse(S)", "3" },
        // A step calling a recursive helper.
        { "F(n) = if(n == 0, 0, F(n - 1) + 2)\nS(k) = F(k)\nS(3).repeat(2)", "12" },
        { "Inner(y) = y + 1\nOuter(x) = Inner(x).repeat(2)\nOuter(0).repeat(3)", "6" },
        // A Math member is user-shaped (a native wrapper with one flat parameter), so it is planned.
        { "repeat(abs(-3), 2)", "3" },
    };

    [Theory]
    [MemberData(nameof(PlannedSteps))]
    public void FlatFixedSteps_StayPlanned_WithTheGenericOutcomeAndBudget(string source, string expected)
    {
        var generic = RunSource(source, optimize: false);
        var planned = RunSource(source, optimize: true);

        Assert.Equal("ok " + expected, generic.Outcome);
        Assert.Equal(generic.Outcome, planned.Outcome);
        Assert.Equal(generic.Budget, planned.Budget);

        Assert.True(planned.Loops.OptimizedLoopHits > 0, $"expected a planned loop: {Describe(planned.Loops)}");
        Assert.NotEmpty(planned.Loops.LoopPlans);
        Assert.All(planned.Loops.LoopPlans, static plan => Assert.True(plan.Optimized, plan.ToString()));
        Assert.DoesNotContain(PlanUnavailable, planned.Loops.FallbackReasons.Keys);
        Assert.DoesNotContain(VariadicStep, planned.Loops.FallbackReasons.Keys);
        Assert.Equal(0, planned.GenericPreparations);
    }

    [Theory]
    [MemberData(nameof(PlannedSteps))]
    public async Task FlatFixedSteps_OnTheAsyncTwin_MatchThePlannedOutcome(string source, string expected)
    {
        var loops = new LoopOptimizationDiagnostics();
        var (result, _) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            Program(source),
            zeroArgPropertyResultCache: new SuspendingAsyncZeroArgPropertyResultCache(),
            loopDiagnostics: loops));

        Assert.Equal("ok " + expected, Outcome(result));
        Assert.Equal(0, loops.OptimizedLoopHits);
        Assert.DoesNotContain(PlanUnavailable, loops.FallbackReasons.Keys);
    }

    /// <summary>
    /// A step whose signature is a shared lifted template is where a false refusal would now
    /// silently de-optimize. Plan construction compares the template's cached facts with its
    /// content only for such signatures. <c>Step</c> lifts <c>A</c>'s parameter <c>k</c>. In the
    /// first row that lift is its whole signature, the flat shared tail. In the second it follows
    /// <c>Step</c>'s own <c>s</c>, a composed template.
    /// </summary>
    [Theory]
    [InlineData("A = k + 1\nStep = A + 0\nStep(0).repeat(5)", false, "5")]
    [InlineData("A = k + 1\nStep = s + 1, A + 0\nStep(0, 0).repeat(3)", true, "S[3, 3]")]
    public void LiftedTemplateSteps_StayPlanned(string source, bool composed, string expected)
    {
        var step = Assert.IsType<Algorithm.User>(
            SourceProvenance.ParseValid(source).Root.Properties.Single(static property => property.Name == "Step").Value);
        var template = Assert.IsType<ImplicitSignatureTemplate>(step.ParameterPatterns);
        Assert.Equal(composed, template.IsComposed);

        var generic = RunSource(source, optimize: false);
        var planned = RunSource(source, optimize: true);

        Assert.Equal("ok " + expected, generic.Outcome);
        Assert.Equal(generic.Outcome, planned.Outcome);
        Assert.Equal(generic.Budget, planned.Budget);
        Assert.True(planned.Loops.OptimizedLoopHits > 0, $"expected a planned loop: {Describe(planned.Loops)}");
        Assert.All(planned.Loops.LoopPlans, static plan => Assert.True(plan.Optimized, plan.ToString()));
        Assert.DoesNotContain(PlanUnavailable, planned.Loops.FallbackReasons.Keys);
        Assert.Equal(0, planned.GenericPreparations);
    }

    // ── 3. Controls: valid steps the planned frame cannot represent keep their fallback ──────

    public static TheoryData<string, string> VariadicSteps => new()
    {
        // A collecting step binds a list; a planned frame would bind the plain value instead.
        { "C(*xs) = xs\nC(5).repeat(1)", "L[5]" },
        { "C(h, *t) = h, t\nC(1, 2).repeat(1)", "S[1, L[2]]" },
        { "P((a, b)) = (b, a + b)\nP((0, 1)).repeat(3)", "S[2, 3]" },
        { "D(x, x) = x, x\nD(3, 3).repeat(1)", "S[3, 3]" },
    };

    [Theory]
    [MemberData(nameof(VariadicSteps))]
    public void CollectingStructuralAndRepeatedNameSteps_KeepTheVariadicFallback(string source, string expected)
    {
        var generic = RunSource(source, optimize: false);
        var optimizing = RunSource(source, optimize: true);

        Assert.Equal("ok " + expected, generic.Outcome);
        Assert.Equal(generic.Outcome, optimizing.Outcome);
        Assert.Equal(generic.Budget, optimizing.Budget);
        Assert.Equal(0, optimizing.Loops.OptimizedLoopHits);
        Assert.Equal(0, optimizing.Loops.LoopPlanBuilds);
        AssertOnlyReason(optimizing.Loops.FallbackReasons, VariadicStep);
        Assert.Equal(1, optimizing.GenericPreparations);
    }

    // ── 4. Controls: every other callable shape still reaches the planner, which refuses it ──

    public static TheoryData<string, string> NonUserSteps => new()
    {
        { "repeat(order([3, 1, 2]), 1)", "L[1, 2, 3]" },
        { "F(0) = 0\nF(n) = n - 1\nrepeat(F(5), 2)", "3" },
        { "A = order\nrepeat(A([3, 1, 2]), 1)", "L[1, 2, 3]" },
    };

    [Theory]
    [MemberData(nameof(NonUserSteps))]
    public void NonUserSteps_StillReachThePlanner_WhichRefusesThem(string source, string expected)
    {
        var generic = RunSource(source, optimize: false);
        var optimizing = RunSource(source, optimize: true);

        Assert.Equal("ok " + expected, generic.Outcome);
        Assert.Equal(generic.Outcome, optimizing.Outcome);
        Assert.Equal(generic.Budget, optimizing.Budget);

        // A step with no binding plan passes the shape gate unchanged; the planner is consulted once
        // and refuses the shape itself. Only a USER step is ever refused by the gate (an unbuildable
        // or a variadic plan); a non-user step always reaches the planner.
        Assert.Equal(0, optimizing.Loops.OptimizedLoopHits);
        Assert.Equal(1, optimizing.Loops.LoopPlanBuilds);
        var plan = Assert.Single(optimizing.Loops.LoopPlans);
        Assert.False(plan.Optimized);
        Assert.Equal(UnsupportedShape, plan.FallbackReason);
        Assert.DoesNotContain(PlanUnavailable, optimizing.Loops.FallbackReasons.Keys);
    }

    // ── 5. Control: a zero-iteration repeat never decides eligibility (LOOP-05) ──────────────

    [Fact]
    public void ZeroIterationRepeat_NeverProjectsTheStep_SoNoEligibilityIsDecided()
    {
        var optimizing = RunSource("S(k) = k + 1\nS(7).repeat(0)", optimize: true);

        Assert.Equal("ok 7", optimizing.Outcome);
        Assert.Equal(1, optimizing.Loops.LoopExecutions);
        Assert.Equal(0, optimizing.Loops.LoopPlanBuilds);
        Assert.Equal(0, optimizing.Loops.OptimizedLoopFallbacks);
        Assert.Empty(optimizing.Loops.FallbackReasons);
        Assert.Equal(0, optimizing.GenericPreparations);
    }

    // ── 6. The former host-scope route is refused before evaluation ──────────────────────────

    /// <summary>
    /// The <see cref="Trigger.HostScope"/> program used to reach the planner, because the
    /// pre-evaluation walker never entered a host-built parent scope. Since such scopes are held to
    /// the pre-evaluation rules (owner decision, 2026-10-12), it is refused before evaluation with
    /// the head's own X-02 violation: the error the same step gets as an ordinary property of the
    /// root. Nothing runs. No loop executes, no host operation is called and no budget is charged,
    /// with or without optimization and on the suspending async twin.
    /// </summary>
    [Theory]
    [InlineData("repeat", InvalidHead.TwoTopLevelCollectors)]
    [InlineData("while", InvalidHead.TwoTopLevelCollectors)]
    [InlineData("repeat", InvalidHead.TwoNestedCollectors)]
    [InlineData("while", InvalidHead.TwoNestedCollectors)]
    public async Task HostScopeStep_IsRefusedBeforeEvaluation(string loop, InvalidHead head)
    {
        var step = new Algorithm.User(Parent: null, ParameterPatterns: Head(head), Opens: [], Properties: [],
            Output: [new Expr.Param("a"), new Expr.Param("b")]);
        var control = Evaluator.RunCounted(new Expr.AlgorithmExpr(new Algorithm.User(Parent: null, ParameterPatterns: [],
            Opens: [], Properties: [new Property("Step", step)], Output: [new Expr.Num(1)])));
        var illegal = Assert.IsType<EvalError.IllegalInEval>(control.Error);
        Assert.Equal(Parser.MultipleCollectingBindingsPerLevelDiagnostic, illegal.Reason);
        var nothingCharged = new Budget(0, 0, 0, 0, 0);

        foreach (var optimize in new[] { false, true })
        {
            var scenario = new UnbuildableStepLoop(Trigger.HostScope, loop, head, suspending: false);
            var loops = new LoopOptimizationDiagnostics();
            var (result, budget) = Evaluator.RunCountedObserved(
                scenario.Program,
                enableOptimizations: optimize,
                loopDiagnostics: loops,
                hostOperations: scenario.Operations);

            Assert.Equal(ErrorText(control), ErrorText(result));
            Assert.Equal(nothingCharged, Budget.Of(budget));
            Assert.Equal(0, loops.LoopExecutions);
            Assert.Empty(scenario.HostCalls);
        }

        var suspending = new UnbuildableStepLoop(Trigger.HostScope, loop, head, suspending: true);
        var asyncLoops = new LoopOptimizationDiagnostics();
        var (asyncResult, asyncBudget) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            suspending.Program,
            zeroArgPropertyResultCache: new SuspendingAsyncZeroArgPropertyResultCache(),
            loopDiagnostics: asyncLoops,
            hostOperations: suspending.Operations));

        Assert.Equal(ErrorText(control), ErrorText(asyncResult));
        Assert.Equal(nothingCharged, Budget.Of(asyncBudget));
        Assert.Equal(0, asyncLoops.LoopExecutions);
        Assert.Empty(suspending.HostCalls);
    }

    // ── Helpers ──────────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// A loop over the user step <c>Step = a, b</c> (a <c>while</c> adds the row <c>flag()</c>)
    /// whose head is <paramref name="head"/> by the time the loop's first iteration projects it.
    /// <c>flag</c> returns <c>true</c> once, then <c>false</c>, so a <c>while</c> result is the state
    /// its first iteration produced.
    /// <list type="bullet">
    /// <item><see cref="Trigger.HostMutation"/>: the caller-owned head is the valid <c>(a, b)</c>
    /// when the pre-evaluation gate reads it. The initial state is the explicit spread
    /// <c>reshape()*</c>, which runs while the loop's supply is formed, before the first iteration;
    /// <c>reshape</c> replaces the head and returns the state <c>(10, 20)</c>.</item>
    /// <item><see cref="Trigger.HostScope"/>: the head is invalid from the start. The step is the
    /// property <c>Step</c> of a host-built scope, the parent of the block an <c>open</c> target
    /// names; the block's public <c>Run</c> loops over <c>Step</c> from the state <c>10, 20</c>, and
    /// the root's one row is <c>Run</c>. That chain never reaches the prelude, so <c>Run</c> calls
    /// the loop builtin through its algorithm rather than by name. The pre-evaluation walker now
    /// refuses this program (section 6).</item>
    /// </list>
    /// </summary>
    private sealed class UnbuildableStepLoop
    {
        private int _flags;

        public UnbuildableStepLoop(Trigger trigger, string loop, InvalidHead head, bool suspending, bool cancelOnFlag = false)
        {
            var validHead = new List<ParameterPattern> { new CaptureParameterPattern("a"), new CaptureParameterPattern("b") };

            Result Reshape()
            {
                Log("reshape");
                validHead.Clear();
                validHead.AddRange(LoopPlanEligibilityFailClosedTests.Head(head));
                return new Result.SequenceValue([new Result.Atom(10), new Result.Atom(20)]);
            }

            Result Flag()
            {
                Log("flag");
                if (cancelOnFlag)
                    Cancellation.Cancel();
                return new Result.Bool(Interlocked.Increment(ref _flags) == 1);
            }

            var reshape = suspending
                ? HostOperation.CreateAsync("reshape", async (_, _) => { await Task.Yield(); return Reshape(); })
                : HostOperation.Create("reshape", (_, _) => Reshape());
            var flag = suspending
                ? HostOperation.CreateAsync("flag", async (_, _) => { await Task.Yield(); return Flag(); })
                : HostOperation.Create("flag", (_, _) => Flag());
            Operations = HostOperations.Create(reshape, flag);

            Head = trigger == Trigger.HostMutation
                ? validHead
                : LoopPlanEligibilityFailClosedTests.Head(head);
            Expr[] rows = loop == "while"
                ? [new Expr.Param("a"), new Expr.Param("b"), new Expr.NativeCall(flag.NativeName, [])]
                : [new Expr.Param("a"), new Expr.Param("b")];
            var step = new Algorithm.User(Parent: null, ParameterPatterns: Head, Opens: [], Properties: [], Output: rows);
            Expr[] count = loop == "repeat" ? [new Expr.Num(1)] : [];

            if (trigger == Trigger.HostMutation)
            {
                Expr state = new Expr.SequenceSpread(new Expr.NativeCall(reshape.NativeName, []));
                Program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("S", step)],
                    [new Expr.Call(new Expr.Resolve(loop), [new Expr.Call(new Expr.Resolve("S"), [state]), .. count])]));
                return;
            }

            var builtin = new Algorithm.Builtin(loop == "repeat" ? BuiltinId.@repeat : BuiltinId.@while);
            var run = new Algorithm.User(Parent: null, ParameterPatterns: [], Opens: [], Properties: [],
                Output: [new Expr.Call(new Expr.AlgorithmExpr(builtin),
                    [new Expr.Call(new Expr.Resolve("Step"), [new Expr.Num(10), new Expr.Num(20)]), .. count])]);
            var hostScope = new ScopeCtx(null, [], [new Property("Step", step)]);
            var block = new Algorithm.User(Parent: hostScope, ParameterPatterns: [], Opens: [],
                Properties: [new Property("Run", run, IsPublic: true)], Output: []);
            Program = new Expr.AlgorithmExpr(new Algorithm.User(Parent: null, ParameterPatterns: [],
                Opens: [new Expr.AlgorithmExpr(block)], Properties: [], Output: [new Expr.Resolve("Run")]));
        }

        public Expr Program { get; }

        public HostOperations Operations { get; }

        /// <summary>The step's caller-owned head, read after the run to prove the trigger happened.</summary>
        public IReadOnlyList<ParameterPattern> Head { get; }

        public List<string> HostCalls { get; } = [];

        public CancellationTokenSource Cancellation { get; } = new();

        private void Log(string call)
        {
            lock (HostCalls)
                HostCalls.Add(call);
        }
    }

    private static Run RunScenario(string loop, InvalidHead head, bool optimize, bool cancelOnFlag = false)
    {
        var scenario = new UnbuildableStepLoop(Trigger.HostMutation, loop, head, suspending: false, cancelOnFlag);
        var loops = new LoopOptimizationDiagnostics();
        var observations = new EvaluationObservations();
        var (result, budget) = Evaluator.RunCountedObserved(
            scenario.Program,
            enableOptimizations: optimize,
            loopDiagnostics: loops,
            observations: observations,
            hostOperations: scenario.Operations,
            cancellationToken: scenario.Cancellation.Token);

        // The pre-evaluation gate let the run start, so the loop executed, and the caller-owned head
        // really became the invalid one, during the run. That `reshape` ran before the shape gate is
        // proven by the optimizing run's plan-unavailable reason, which the callers assert.
        Assert.Equal(1, loops.LoopExecutions);
        Assert.Contains("reshape", scenario.HostCalls);
        Assert.Equal(Head(head).Select(static pattern => pattern.DisplayName), scenario.Head.Select(static pattern => pattern.DisplayName));

        return new Run(Outcome(result), ErrorText(result), Budget.Of(budget), loops.GetSnapshot(),
            observations.GenericLoopStepBindingPreparationCount, [.. scenario.HostCalls]);
    }

    private static Run RunSource(string source, bool optimize) => RunProgram(Program(source), optimize);

    private static Run RunProgram(Expr program, bool optimize)
    {
        var loops = new LoopOptimizationDiagnostics();
        var observations = new EvaluationObservations();
        var (result, budget) = Evaluator.RunCountedObserved(
            program,
            enableOptimizations: optimize,
            loopDiagnostics: loops,
            observations: observations);
        return new Run(Outcome(result), ErrorText(result), Budget.Of(budget), loops.GetSnapshot(),
            observations.GenericLoopStepBindingPreparationCount, []);
    }

    private static Expr Program(string source) => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private static string Outcome(EvalResult<Evaluator.CountedResult> result)
        => result.IsError
            ? "err " + LoopDiagnosticParityAssertions.Innermost(result.Error).GetType().Name
            : "ok " + SixRouteAgreement.Neutral(result.Value.Value);

    /// <summary>
    /// The whole reported error: public code, message and span, then every context frame from the
    /// outermost inward. Compared as text because a context record may hold lists, which record
    /// equality compares by reference.
    /// </summary>
    private static string ErrorText(EvalResult<Evaluator.CountedResult> result)
    {
        if (!result.IsError)
            return "";
        var error = KatLangError.FromEvalError(result.Error);
        return $"{error.Code}: {error.Message} @ {error.Span} | {string.Join(" / ", LoopDiagnosticParityAssertions.ContextChain(result.Error))}";
    }

    private static void AssertOnlyReason(IReadOnlyDictionary<string, long> reasons, string reason)
    {
        var only = Assert.Single(reasons);
        Assert.Equal(reason, only.Key);
        Assert.Equal(1, only.Value);
    }

    private static string Describe(LoopOptimizationDiagnosticsSnapshot loops)
        => $"hits={loops.OptimizedLoopHits} builds={loops.LoopPlanBuilds} reasons=[{string.Join(", ", loops.FallbackReasons.Select(static pair => $"{pair.Key}:{pair.Value}"))}]";
}
