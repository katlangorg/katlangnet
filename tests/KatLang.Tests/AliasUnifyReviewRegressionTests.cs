using KatLang.Evaluation;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// ALIAS-UNIFY-1 (M4★) independent-review regressions: every defect the review confirmed, pinned on
/// every route (<see cref="SixRouteAgreement"/>: the sync, optimized and asynchronous engines must agree
/// on the outcome, every diagnostic and the host-call log). Front end: the static reference chases
/// resolve a followed row in ITS OWN scope, terminate on cycles through member steps, honor parameter
/// bindings before resolution, treat a reference-shaped body whose head names nothing as its own
/// structure, and give a block-headed reference the processed block. Evaluator: an alias step's route
/// decision cannot re-enter itself, an alias receiver of <c>.string</c> reads its terminal's cached entry
/// and names the terminal on a missing output, and the loop planner keeps a carrier's own declarations.
/// Lean: the ALIAS-UNIFY-1 review guards of <c>CoreTests/AliasForwarding.lean</c> and
/// <c>CoreTests/PropertyCacheConsumers.lean</c>.
/// </summary>
public sealed class AliasUnifyReviewRegressionTests
{
    // ── Evaluator: an alias step's route decision ──

    [Theory]
    [InlineData("A = A.Algorithm\nA")]
    [InlineData("A = B.Algorithm\nB = A\nB(1)")]
    [InlineData("A = B.Algorithm\nB = A\nA")]
    public async Task AnAlgorithmLinkWhoseReceiverLeadsBackIntoItsChase_IsADemandCycle_NeverAHostOverflow(string source)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", outcome.Kind);
        Assert.StartsWith("DemandCycle:", outcome.Errors[0], StringComparison.Ordinal);
    }

    // ── Evaluator: an alias receiver of `.string` reads its VALUE terminal ──

    [Theory]
    [InlineData("F = tick()\nF, { F }.string")]
    [InlineData("F = tick()\nC = { F }\nF, C.string")]
    [InlineData("F = tick()\nA = F\nF, A.string")]
    [InlineData("F = tick()\nF, F.string")]
    public async Task AnAliasReceiverOfString_ReadsItsTerminalsCachedEntry(string source)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal("S[1, '1']", outcome.Value);
        Assert.Equal(["tick#1"], outcome.HostCalls);
    }

    [Theory]
    [InlineData("A = P\nA.string", "MissingOutput: while evaluating dotCall .string of A: Property 'P' has no defined output.")]
    [InlineData("C = { P }\nC.string", "MissingOutput: while evaluating dotCall .string of C: Property 'P' has no defined output.")]
    [InlineData("P.string", "MissingOutput: Property 'P' has no defined output.")]
    public async Task AStringReceiverReachedThroughAnAlias_NamesTheTerminalBinding_AsItsFormerRowReadDid(string rows, string expected)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync("P = {\n    Q = 1\n}\n" + rows);
        Assert.Equal("err", outcome.Kind);
        Assert.StartsWith(expected, outcome.Errors[0], StringComparison.Ordinal);
    }

    // ── Evaluator: the loop planner and a carrier's own declarations ──

    [Theory]
    [InlineData("Step(x) = {\n    U = x + 1\n    T = U\n    T + 0\n}\nStep(0).repeat(2)")]
    [InlineData("Step(x) = {\n    U = x + 1\n    T = { U }\n    T + 0\n}\nStep(0).repeat(2)")]
    public async Task APlannedLoopTemp_ReadsAnAliasTargetInTheAliasesOwnScope(string source)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal("2", outcome.Value);

        // A reference, or a carrier that declares and opens nothing of its own, is planned as its target's
        // temp: the whole loop runs on the planner, charging exactly the generic evaluator's steps and depth.
        var generic = ObserveLoop(source, optimized: false);
        var optimized = ObserveLoop(source, optimized: true);
        Assert.Equal(1, optimized.Loops.OptimizedLoopHits);
        Assert.Equal(0, optimized.Loops.PlannedExpressionFallbacks);
        Assert.Equal(0, optimized.Loops.GenericExpressionEvaluationsInsideOptimizedLoops);
        var plan = Assert.Single(optimized.Loops.LoopPlans);
        Assert.True(plan.Optimized, plan.FallbackReason);
        Assert.Equal("2", SixRouteAgreement.Neutral(optimized.Result.Value.Value));
        Assert.Equal(generic.Budget.ConsumedSteps, optimized.Budget.ConsumedSteps);
        Assert.Equal(generic.Budget.PeakDepth, optimized.Budget.PeakDepth);

        // Adjacent limits: the exact budgets admit both strategies, one step less stops both (a loop step
        // charges no depth, so these loops peak at depth 1, which has no lower legal setting).
        Assert.True(generic.Budget.ConsumedSteps > 1, "the step limit must have a lower legal setting");
        foreach (var strategy in new[] { false, true })
        {
            Assert.False(ObserveLoop(source, strategy, new EvaluationLimits { MaxSteps = generic.Budget.ConsumedSteps }).Result.IsError);
            Assert.IsType<EvalError.EvaluationStepLimitExceeded>(
                ObserveLoop(source, strategy, new EvaluationLimits { MaxSteps = generic.Budget.ConsumedSteps - 1 }).Result.Error);
            Assert.False(ObserveLoop(source, strategy, new EvaluationLimits { MaxDepth = generic.Budget.PeakDepth }).Result.IsError);
            if (generic.Budget.PeakDepth > 1)
            {
                Assert.IsType<EvalError.EvaluationDepthExceeded>(
                    ObserveLoop(source, strategy, new EvaluationLimits { MaxDepth = generic.Budget.PeakDepth - 1 }).Result.Error);
            }
        }
    }

    [Fact]
    public async Task ALoopTempCarrierWithItsOwnDeclarations_FallsBackToTheGenericEvaluator()
    {
        const string source = "Step(x) = {\n    U = x + 1\n    T = {\n        U = 99\n        U\n    }\n    T + 0\n}\nStep(0).repeat(2)";
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal("99", outcome.Value);

        // The carrier T declares its own U, so the planner refuses it as a temp (planning it as U's would
        // lose that declaration): its reading row is evaluated generically inside the optimized loop, which
        // reads T's own U.
        var optimized = ObserveLoop(source, optimized: true);
        Assert.Equal(1, optimized.Loops.OptimizedLoopHits);
        Assert.True(optimized.Loops.PlannedExpressionFallbacks > 0);
        Assert.True(optimized.Loops.GenericExpressionEvaluationsInsideOptimizedLoops > 0);
        Assert.Equal("99", SixRouteAgreement.Neutral(optimized.Result.Value.Value));
        Assert.Equal(ObserveLoop(source, optimized: false).Budget.ConsumedSteps, optimized.Budget.ConsumedSteps);
    }

    private static (EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget, LoopOptimizationDiagnosticsSnapshot Loops) ObserveLoop(
        string source, bool optimized, EvaluationLimits? limits = null)
    {
        var loops = new LoopOptimizationDiagnostics();
        var (result, budget) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), limits, enableOptimizations: optimized, loopDiagnostics: loops);
        return (result, budget, loops.GetSnapshot());
    }

    // ── Front end: the resolver's open-provider chase ──

    [Theory]
    [InlineData("R1 = R2.count\nR2 = R1\nLib = { public Q = 7 }\nF = {\n    open R1, Lib\n    Q\n}\nF", "7")]
    // R1 provides nothing of its own, so Q is F's inferred input.
    [InlineData("R1 = R2.count\nR2 = R1\nF = {\n    open R1\n    Q\n}\nF(5)", "5")]
    public async Task AReferenceCycleThroughAMemberStep_IsItsOwnNamespace_NeverAHostOverflow(string source, string value)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal(value, outcome.Value);
    }

    [Fact]
    public async Task AClosedBodyOpeningACyclicReference_ReportsItsUndeclaredName()
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(
            "R1 = R2.count\nR2 = R1\nF(p) = {\n    open R1\n    Q\n}\nF(1)");
        Assert.Equal("parse", outcome.Kind);
        Assert.StartsWith("UndeclaredIdentifier:", outcome.Errors[0], StringComparison.Ordinal);
    }

    [Theory]
    // The opener declares a nearer same-named Lib: the reference's head is still the root Lib.
    [InlineData("Lib = { public Inc(x) = x + 1 }\nA = Lib\nF = {\n    open A\n    Lib = { public Dec(x) = x - 1 }\n    G = Inc\n    G(5)\n}\nF")]
    // The reference is reached through a member step: its head is visible only from its own scope.
    [InlineData("Box = {\n    Lib2 = { public Inc(x) = x + 1 }\n    public A = Lib2\n}\nF = {\n    open Box.A\n    G = Inc\n    G(5)\n}\nF")]
    // An outer same-named Lib2 with ANOTHER signature is not the provider.
    [InlineData("Lib2 = { public Inc = 100 }\nBox = {\n    Lib2 = { public Inc(x) = x + 1 }\n    public A = Lib2\n}\nF = {\n    open Box.A\n    G = Inc\n    G(5)\n}\nF")]
    public async Task AnOpenedReference_ResolvesItsHeadInItsOwnScope(string source)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal("6", outcome.Value);
    }

    // ── Front end: receivers are read through their structure, in their own scope ──

    [Theory]
    [InlineData("open Lib\nLib = {\n    Defaults = { public Rate = 0.2 }\n    public Cfg = Defaults\n}\nTax = Cfg.Rate * 100\nTax")]
    [InlineData("Lib = {\n    Defaults = { public Rate = 0.2 }\n    public Cfg = Defaults\n}\nTax = Lib.Cfg.Rate * 100\nTax")]
    [InlineData("Outer = {\n    Lib = {\n        Defaults = { public Rate = 0.2 }\n        public Cfg = Defaults\n    }\n    T = {\n        open Lib\n        Cfg.Rate * 100\n    }\n    T\n}\nOuter")]
    [InlineData("Defaults = { public Rate = 0.5 }\nOuter = {\n    Inner = { public Rate = 0.2 }\n    Lib = {\n        public Cfg = Inner\n    }\n    T = {\n        open Lib\n        Cfg.Rate * 100\n    }\n    T\n}\nOuter")]
    public async Task AReferenceReceiver_IsItsTargetsStructure_HoweverItIsReached(string source)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal("20.0", outcome.Value);
    }

    [Fact]
    public async Task AParameterHeadedReference_IsItsOwnNamespace_SoAClosedBodyReportsWhatItCannotProvide()
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync("B = { public X = 1 }\nF(B) = {\n    open A\n    A = B\n    X\n}\nF(5)");
        Assert.Equal("parse", outcome.Kind);
        Assert.StartsWith("UndeclaredIdentifier: Identifier 'X'", outcome.Errors[0], StringComparison.Ordinal);
    }

    [Fact]
    public async Task AReferenceShapedBodyWhoseHeadNamesNothing_IsItsOwnStructure_SoACertainMissIsChecked()
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync("A = x\nG(p) = A.foo\nG(1)");
        Assert.Equal("parse", outcome.Kind);
        Assert.StartsWith("UndeclaredIdentifier: Property 'foo' was not found on `A`", outcome.Errors[0], StringComparison.Ordinal);
    }

    // ── Front end: OD-D and block-headed references ──

    [Fact]
    public void ACompletedOuterAlias_DoesNotHideAnInnerReferenceCycle()
    {
        var parsed = SourceProvenance.ParseValid(
            "Tail = 7\nGood = Tail\nOuter = {\n    Tail = Good\n    Good = Tail\n    1\n}\n1");
        Assert.IsType<Algorithm.Alias>(Assert.Single(parsed.Root.Properties, static p => p.Name == "Good").Value);
        var outer = Assert.IsType<Algorithm.User>(
            Assert.Single(parsed.Root.Properties, static p => p.Name == "Outer").Value);
        Assert.All(outer.Properties, static property => Assert.IsType<Algorithm.User>(property.Value));
    }

    [Theory]
    [InlineData("V = A\nA = {\n    V = { public W = 7 }\n    K = V\n}.K\nA.W")]
    [InlineData("A = {\n    V = { public W = 7 }\n    K = V\n}.K\nA.W")]
    [InlineData("A = B.K\nB = {\n    V = { public W = 7 }\n    K = V\n    U = A\n}\nV = A\nA.W")]
    [InlineData("B = {\n    V = { public W = 7 }\n    K = V\n    U = A\n}\nA = B.K\nV = A\nA.W")]
    public async Task AReferenceChase_FollowsEachRowInItsOwnScope_InEveryDeclarationOrder(string source)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal("7", outcome.Value);
    }

    [Theory]
    [InlineData("A, A(), A", "S[1, 2, 1]", 2)]
    [InlineData("A == A()", "false", 2)]
    public async Task ABlockHeadedReference_NavigatesTheProcessedBlock(string rows, string expected, int ticks)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync("A = {\n    Z = tick() + 0\n    K = Z\n}.K\n" + rows);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal(expected, outcome.Value);
        Assert.Equal(ticks, outcome.HostCalls.Count);
    }
}
