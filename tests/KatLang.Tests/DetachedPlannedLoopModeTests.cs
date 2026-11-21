using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// EXPORTED-DETACHED and the planned loop (November 2026): the evidence for keeping the planned
/// iteration head WITHOUT a context-binding marker (the audit's SPECS §D part 4, made conditional
/// by the owner's follow-up decision).
/// <para>A planned loop runs its rounds in one of two modes, decided once when its plan is built
/// (<c>LoopPlanTemplate.RequiresPerIterationCacheIdentity</c>):</para>
/// <list type="bullet">
///   <item>FULLY PLANNED — every output row and every temp is a plan. The step is pushed once,
///   without an activation; no generic expression evaluation runs under that head, so no captured
///   parameter read is ever looked up through it: state is read from the frame's slots, an
///   enclosing parameter through the cell the planner found when it built the plan.</item>
///   <item>PARTIALLY PLANNED — at least one row is a generic fallback. Every round enters the step's
///   body with a REAL activation (<c>LoopRunFrame.BeginIteration</c>), so a nested captured read is
///   an ordinary lexical read of the current round.</item>
/// </list>
/// <para>Each test below PROVES its mode from the planner's own observations
/// (<see cref="LoopOptimizationDiagnostics"/>: the loop was entered as a planned loop, and how many
/// rows ran as plans or as generic fallbacks), then checks, in that mode: an ordinary read gets the
/// CURRENT iteration's input; an EXECUTED detached read is refused with the structured outcome the
/// generic strategy gives; and the planner selected the intended plan or fallback. Values, effects
/// (the run's tick count) and raw checkpoints (steps, peak depth, materialized items) are compared
/// with the generic route, and the forced async twin's outcome is compared too. A refusal obtained
/// by running the WHOLE loop generically would prove nothing about the planned head: every refusal
/// here is asserted from a run whose loop was entered planned.</para>
/// <para>The second half pins the planner's exported-temp dependency walk
/// (<c>LoopOptimizer.ExportedTempReadsLoopOrEnclosingInput</c>): each distinct plan node is expanded
/// once, by reference identity, however many paths share it.</para>
/// </summary>
public class DetachedPlannedLoopModeTests
{
    // ── Fully planned rounds ───────────────────────────────────────────────────────────────────

    [Fact]
    public async Task FullyPlanned_OrdinaryStateRead_GetsTheCurrentIterationInput()
    {
        var program = Parsed("Step(a, n) = { a * 2, n + 1 }\nStep(1, 0).repeat(3)\n");

        var planned = RunPlanned(program);

        Assert.Equal("ok raw=S[8, 3] n=1", AsyncEvaluationHarness.NeutralOf(planned.Result));
        AssertFullyPlanned(planned.Diagnostics, iterations: 3, rowsPerIteration: 2);
        await AssertAgreesWithGenericAndAsync(program, planned);
    }

    [Fact]
    public async Task FullyPlanned_EnclosingParameterRead_GetsTheCallThatBuiltThePlan()
    {
        // The step reads `y`, an input of the call around the loop, through the cell the planner
        // found on F's activation. Each call of F builds its own plan over its own cell.
        var program = Parsed("""
            F(y) = {
              Step(a, n) = { a * y, n + 1 }
              Step(1, 0).repeat(3)
            }
            F(2), F(3)
            """);

        var planned = RunPlanned(program);

        Assert.Equal("ok raw=S[S[8, 3], S[27, 3]] n=2", AsyncEvaluationHarness.NeutralOf(planned.Result));
        Assert.Equal(2, planned.Diagnostics.OptimizedLoopHits);
        Assert.Equal(0, planned.Diagnostics.OptimizedLoopFallbacks);
        Assert.Equal(0, planned.Diagnostics.PlannedExpressionFallbacks);
        Assert.Equal(0, planned.Diagnostics.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.Equal(12, planned.Diagnostics.PlannedExpressionHits);
        await AssertAgreesWithGenericAndAsync(program, planned);
    }

    [Fact]
    public async Task FullyPlanned_CorrectlyExportedTemp_IsPlannedInEveryRound()
    {
        var program = Parsed("""
            Step(s) = {
              T = 5
              s + T
            }
            Step(0).repeat(3)
            """);

        var planned = RunPlanned(program);

        Assert.Equal("ok raw=15 n=1", AsyncEvaluationHarness.NeutralOf(planned.Result));
        AssertFullyPlanned(planned.Diagnostics, iterations: 3, rowsPerIteration: 1);
        var temp = Assert.Single(Assert.Single(planned.Diagnostics.GetSnapshot().LoopPlans).Temps);
        Assert.True(temp.Planned);
        Assert.False(planned.Diagnostics.FallbackReasons.ContainsKey(LoopOptimizer.ExportedTempInputFallbackReason));
        await AssertAgreesWithGenericAndAsync(program, planned);
    }

    /// <summary>
    /// A detached read EXECUTED inside a fully planned round. <c>P</c> is falsely exported, so its
    /// loop runs in the detached context; the loop's initial state <c>y + 0</c> is a suspended
    /// computation of that context, demanded by the first planned state read. The plan stays fully
    /// planned — no row falls back, the loop is entered planned — and the read is the refusal the
    /// generic strategy gives where its step demands the same cell.
    /// </summary>
    [Fact]
    public async Task FullyPlanned_ExecutedDetachedRead_IsRefused_LikeGeneric()
    {
        const string source = """
            F(y) = {
              Step(a, n) = { a * 2, n + 1 }
              P = Step(y + 0, 0).repeat(3)
              P
            }
            F(1)
            """;

        // The correctly classified program first: fully planned, and the ordinary value.
        var declared = RunPlanned(Parsed(source));
        Assert.Equal("ok raw=S[8, 3] n=1", AsyncEvaluationHarness.NeutralOf(declared.Result));
        AssertFullyPlanned(declared.Diagnostics, iterations: 3, rowsPerIteration: 2);

        var program = MisExposed(source, "F.P");
        var planned = RunPlanned(program);

        var unknown = Assert.IsType<EvalError.UnknownName>(EvaluatorTestSupport.Innermost(planned.Result.Error));
        Assert.Equal("y", unknown.Name);
        Assert.Contains(Contexts(planned.Result.Error), context
            => context is TextErrorContext text && text.Message == Evaluator.DetachedParameterMessage("y"));
        // The loop was entered PLANNED and no row ran generically: the refusal is the planned round's.
        Assert.Equal(1, planned.Diagnostics.OptimizedLoopHits);
        Assert.Equal(0, planned.Diagnostics.OptimizedLoopFallbacks);
        Assert.Equal(0, planned.Diagnostics.PlannedExpressionFallbacks);
        Assert.Equal(0, planned.Diagnostics.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.Empty(planned.Diagnostics.FallbackReasons);
        var plan = Assert.Single(planned.Diagnostics.GetSnapshot().LoopPlans);
        Assert.True(plan.Optimized);
        Assert.All(plan.Expressions, expression => Assert.True(expression.Planned));
        await AssertAgreesWithGenericAndAsync(program, planned);
    }

    // ── Partially planned rounds ───────────────────────────────────────────────────────────────

    [Fact]
    public async Task PartiallyPlanned_NestedCapturedRead_GetsTheCurrentIterationInput()
    {
        // The audit's l1: the inline block is a generic fallback row, and its captured read of the
        // step's `a` is a lexical read of the round's own activation — 1, 2, 4 across the rounds.
        var program = Parsed("Step(a, n) = { { a * 2 }, n + 1 }\nStep(1, 0).repeat(3)\n");

        var planned = RunPlanned(program);

        Assert.Equal("ok raw=S[8, 3] n=1", AsyncEvaluationHarness.NeutralOf(planned.Result));
        AssertPartiallyPlanned(planned.Diagnostics, iterations: 3, fallbackRowsPerIteration: 1, plannedRowsPerIteration: 1);
        // Recorded when the plan was built and once per round the fallback row ran.
        Assert.Equal(4, planned.Diagnostics.FallbackReasons["unsupported block expression"]);
        await AssertAgreesWithGenericAndAsync(program, planned);
    }

    [Fact]
    public async Task PartiallyPlanned_NestedRead_GetsTheCurrentIterationInput_AndTheEnclosingCallsInput()
    {
        var program = Parsed("""
            F(y) = {
              Step(a, n) = { { a * y }, n + 1 }
              Step(1, 0).repeat(3)
            }
            F(2), F(3)
            """);

        var planned = RunPlanned(program);

        Assert.Equal("ok raw=S[S[8, 3], S[27, 3]] n=2", AsyncEvaluationHarness.NeutralOf(planned.Result));
        Assert.Equal(2, planned.Diagnostics.OptimizedLoopHits);
        Assert.Equal(0, planned.Diagnostics.OptimizedLoopFallbacks);
        Assert.Equal(6, planned.Diagnostics.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.Equal(6, planned.Diagnostics.PlannedExpressionHits);
        await AssertAgreesWithGenericAndAsync(program, planned);
    }

    /// <summary>
    /// A detached read EXECUTED inside a partially planned round. The falsely exported temp
    /// <c>T = s + 1</c> reads the loop state, so the planner does not plan it (the recorded reason)
    /// and the row reading it is a generic fallback INSIDE the planned loop: the round's activation
    /// is real, the property is evaluated detached, and the read is refused exactly as the generic
    /// strategy refuses it.
    /// </summary>
    [Fact]
    public async Task PartiallyPlanned_ExecutedDetachedRead_IsRefused_LikeGeneric()
    {
        const string source = """
            Step(s) = {
              T = s + 1
              T
            }
            Step(0).repeat(3)
            """;

        // Correctly classified, the local-only temp is planned and the loop is fully planned.
        var declared = RunPlanned(Parsed(source));
        Assert.Equal("ok raw=3 n=1", AsyncEvaluationHarness.NeutralOf(declared.Result));
        AssertFullyPlanned(declared.Diagnostics, iterations: 3, rowsPerIteration: 1);

        var program = MisExposed(source, "Step.T");
        var planned = RunPlanned(program);

        var unknown = Assert.IsType<EvalError.UnknownName>(EvaluatorTestSupport.Innermost(planned.Result.Error));
        Assert.Equal("s", unknown.Name);
        Assert.Contains(Contexts(planned.Result.Error), context
            => context is TextErrorContext text && text.Message == Evaluator.DetachedParameterMessage("s"));
        // The intended fallback: the temp is left unplanned for the stated reason, the loop is STILL
        // entered planned, and the refusing row is the one generic evaluation inside it.
        Assert.Equal(1, planned.Diagnostics.FallbackReasons[LoopOptimizer.ExportedTempInputFallbackReason]);
        Assert.Equal(1, planned.Diagnostics.OptimizedLoopHits);
        Assert.Equal(0, planned.Diagnostics.OptimizedLoopFallbacks);
        Assert.Equal(1, planned.Diagnostics.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.Equal(1, planned.Diagnostics.PlannedExpressionFallbacks);
        var plan = Assert.Single(planned.Diagnostics.GetSnapshot().LoopPlans);
        Assert.True(plan.Optimized);
        Assert.False(Assert.Single(plan.Temps).Planned);
        Assert.False(Assert.Single(plan.Expressions).Planned);
        await AssertAgreesWithGenericAndAsync(program, planned);
    }

    /// <summary>
    /// The same refusal when the falsely exported member is read through a NESTED block of the row:
    /// the block is the fallback, and the member it reads is evaluated detached.
    /// </summary>
    [Fact]
    public async Task PartiallyPlanned_ExecutedDetachedRead_ThroughANestedBlock_IsRefused_LikeGeneric()
    {
        const string source = """
            Step(s, n) = {
              T = s + 1
              { T * 2 }, n + 1
            }
            Step(0, 0).repeat(3)
            """;

        var declared = RunPlanned(Parsed(source));
        Assert.Equal("ok raw=S[14, 3] n=1", AsyncEvaluationHarness.NeutralOf(declared.Result));
        Assert.Equal(1, declared.Diagnostics.OptimizedLoopHits);
        Assert.Equal(3, declared.Diagnostics.GenericExpressionEvaluationsInsideOptimizedLoops);

        var program = MisExposed(source, "Step.T");
        var planned = RunPlanned(program);

        var unknown = Assert.IsType<EvalError.UnknownName>(EvaluatorTestSupport.Innermost(planned.Result.Error));
        Assert.Equal("s", unknown.Name);
        Assert.Equal(1, planned.Diagnostics.OptimizedLoopHits);
        Assert.Equal(0, planned.Diagnostics.OptimizedLoopFallbacks);
        Assert.Equal(1, planned.Diagnostics.GenericExpressionEvaluationsInsideOptimizedLoops);
        await AssertAgreesWithGenericAndAsync(program, planned);
    }

    // ── The exported-temp dependency walk: each distinct plan node once ────────────────────────

    /// <summary>
    /// A plan DAG of <paramref name="depth"/> binary nodes over one leaf, every node used TWICE by the
    /// node above it: depth + 1 distinct nodes and 2^depth paths from the root to the leaf.
    /// </summary>
    private static LoopExprPlan SharedPlan(LoopExprPlan leaf, int depth)
    {
        var node = leaf;
        for (var level = 0; level < depth; level++)
            node = new LoopExprPlan.Binary(new Expr.Num(level), BinaryOp.Add, node, node);
        return node;
    }

    private static Property ExportedTemp(string name)
        => new(name, new Algorithm.User(null, [], [], [], new OutputBundle([new Expr.Num(0)])), IsPublic: false);

    [Theory]
    [InlineData(1)]
    [InlineData(8)]
    [InlineData(64)]
    [InlineData(4096)]
    public void DependencyWalk_OverAnInputFreeSharedGraph_ExpandsEachDistinctNodeOnce(int depth)
    {
        var leaf = new LoopExprPlan.Constant(new Expr.Num(1), PlannedLoopValue.FromNumeric(1));

        var readsInput = LoopOptimizer.ExportedTempReadsLoopOrEnclosingInput(
            ExportedTemp("T"), SharedPlan(leaf, depth), [], out var visited);

        // 2^depth paths (far beyond any budget at depth 64), depth + 1 nodes.
        Assert.False(readsInput);
        Assert.Equal(depth + 1, visited);
    }

    [Theory]
    [InlineData(1)]
    [InlineData(8)]
    [InlineData(64)]
    [InlineData(4096)]
    public void DependencyWalk_DetectsASharedInputDependency_WithinTheDistinctNodes(int depth)
    {
        var state = new LoopExprPlan.StateSlot(new Expr.Param("s"), 0, "s");

        var readsInput = LoopOptimizer.ExportedTempReadsLoopOrEnclosingInput(
            ExportedTemp("T"), SharedPlan(state, depth), [], out var visited);

        Assert.True(readsInput);
        Assert.InRange(visited, 1, depth + 1);
    }

    /// <summary>
    /// A shared graph with the input on ONE side only: the input-free side is shared at every level, so
    /// an unshared walk would expand it once per path before reaching the input on the other side.
    /// </summary>
    [Theory]
    [InlineData(8)]
    [InlineData(64)]
    [InlineData(4096)]
    public void DependencyWalk_FindsAnInputBesideALargeSharedInputFreeGraph(int depth)
    {
        var free = SharedPlan(new LoopExprPlan.Constant(new Expr.Num(1), PlannedLoopValue.FromNumeric(1)), depth);
        var state = new LoopExprPlan.StateSlot(new Expr.Param("s"), 0, "s");
        // The walk pops the right operand first: the whole input-free graph, then the input.
        var plan = new LoopExprPlan.Binary(new Expr.Num(-1), BinaryOp.Add, state, free);

        var readsInput = LoopOptimizer.ExportedTempReadsLoopOrEnclosingInput(ExportedTemp("T"), plan, [], out var visited);

        Assert.True(readsInput);
        Assert.Equal(depth + 3, visited);
    }

    [Fact]
    public void DependencyWalk_JudgesOnlyExportedParameterlessTemps()
    {
        var state = new LoopExprPlan.StateSlot(new Expr.Param("s"), 0, "s");
        var localOnly = ExportedTemp("T") with
        {
            Exposure = PropertyExposure.LocalOnlyCapturedAncestorParameters,
            RequiredAncestorParameters = ["s"],
        };

        Assert.False(LoopOptimizer.ExportedTempReadsLoopOrEnclosingInput(localOnly, state, [], out var visited));
        Assert.Equal(0, visited);
    }

    /// <summary>
    /// The same bound through the real planner, for a temp NOTHING reads. A host tree may share one
    /// expression object between both operands of every level; the planner gives it one plan node, and
    /// preparing the step's temps walks that plan whether or not a row ever reads the temp.
    /// </summary>
    [Theory]
    [InlineData(40, false)]
    [InlineData(40, true)]
    public async Task PreparingAnUndemandedExportedTemp_WalksItsSharedBody_OncePerDistinctNode(int depth, bool readsState)
    {
        Expr body = readsState ? new Expr.Param("s") : new Expr.Num(1);
        for (var level = 0; level < depth; level++)
            body = new Expr.Binary(BinaryOp.Add, body, body);

        // Step(s) = { T = <shared body> ⏎ s + 1 }: no row reads T.
        var temp = new Property("T", new Algorithm.User(null, [], [], [], new OutputBundle([body])), IsPublic: false);
        var step = new Property("Step", new Algorithm.User(null, [new CaptureParameterPattern("s")], [], [temp],
            new OutputBundle([new Expr.Binary(BinaryOp.Add, new Expr.Param("s"), new Expr.Num(1))])), IsPublic: true);
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [step],
            new OutputBundle([new Expr.DotCall(
                new Expr.Call(new Expr.Resolve("Step"), new OutputBundle([new Expr.Num(0)])),
                "repeat", new OutputBundle([new Expr.Num(3)]))])));

        var planned = RunPlanned(program);

        Assert.Equal("ok raw=3 n=1", AsyncEvaluationHarness.NeutralOf(planned.Result));
        Assert.Equal(1, planned.Diagnostics.OptimizedLoopHits);
        // 2^40 paths; the walk expanded at most the distinct nodes of the one judged temp.
        Assert.InRange(planned.Diagnostics.ExportedTempDependencyVisits, 1, depth + 1);
        if (readsState)
        {
            // The mis-exposed temp is left unplanned for the stated reason; nothing reads it, so the
            // loop's value is unaffected on every route.
            Assert.Equal(1, planned.Diagnostics.FallbackReasons[LoopOptimizer.ExportedTempInputFallbackReason]);
        }
        else
        {
            Assert.Equal(depth + 1, planned.Diagnostics.ExportedTempDependencyVisits);
            Assert.False(planned.Diagnostics.FallbackReasons.ContainsKey(LoopOptimizer.ExportedTempInputFallbackReason));
        }

        var generic = Evaluator.RunCountedObserved(program, enableOptimizations: false).Result;
        Assert.Equal("ok raw=3 n=1", AsyncEvaluationHarness.NeutralOf(generic));
        var asynchronous = (await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache()))).Result;
        Assert.Equal("ok raw=3 n=1", AsyncEvaluationHarness.NeutralOf(asynchronous));
    }

    // ── Harness ────────────────────────────────────────────────────────────────────────────────

    private sealed record PlannedRun(
        EvalResult<Evaluator.CountedResult> Result,
        EvaluationBudget Budget,
        LoopOptimizationDiagnostics Diagnostics);

    private static PlannedRun RunPlanned(Expr program)
    {
        var diagnostics = new LoopOptimizationDiagnostics();
        var (result, budget) = Evaluator.RunCountedObserved(program, loopDiagnostics: diagnostics);
        return new PlannedRun(result, budget, diagnostics);
    }

    /// <summary>Every row of every round ran as a plan, and the loop was entered planned.</summary>
    private static void AssertFullyPlanned(LoopOptimizationDiagnostics diagnostics, int iterations, int rowsPerIteration)
    {
        Assert.Equal(1, diagnostics.OptimizedLoopHits);
        Assert.Equal(0, diagnostics.OptimizedLoopFallbacks);
        Assert.Equal(iterations, diagnostics.LoopIterations);
        Assert.Equal((long)iterations * rowsPerIteration, diagnostics.PlannedExpressionHits);
        Assert.Equal(0, diagnostics.PlannedExpressionFallbacks);
        Assert.Equal(0, diagnostics.GenericExpressionEvaluationsInsideOptimizedLoops);
        var plan = Assert.Single(diagnostics.GetSnapshot().LoopPlans);
        Assert.True(plan.Optimized);
        Assert.All(plan.Expressions, expression => Assert.True(expression.Planned));
        Assert.All(plan.Temps, temp => Assert.True(temp.Planned));
    }

    /// <summary>The loop was entered planned, and some rows of every round ran as generic fallbacks.</summary>
    private static void AssertPartiallyPlanned(
        LoopOptimizationDiagnostics diagnostics, int iterations, int fallbackRowsPerIteration, int plannedRowsPerIteration)
    {
        Assert.Equal(1, diagnostics.OptimizedLoopHits);
        Assert.Equal(0, diagnostics.OptimizedLoopFallbacks);
        Assert.Equal(iterations, diagnostics.LoopIterations);
        Assert.Equal((long)iterations * fallbackRowsPerIteration, diagnostics.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.Equal((long)iterations * fallbackRowsPerIteration, diagnostics.PlannedExpressionFallbacks);
        Assert.Equal((long)iterations * plannedRowsPerIteration, diagnostics.PlannedExpressionHits);
        var plan = Assert.Single(diagnostics.GetSnapshot().LoopPlans);
        Assert.True(plan.Optimized);
        Assert.Contains(plan.Expressions, expression => !expression.Planned);
    }

    /// <summary>
    /// The planned run against the generic strategy — the same value or the same structured error, the
    /// same effects (tick count) and the same raw checkpoints — and against the forced async twin.
    /// </summary>
    private static async Task AssertAgreesWithGenericAndAsync(Expr program, PlannedRun planned)
    {
        var (generic, genericBudget) = Evaluator.RunCountedObserved(program, enableOptimizations: false);

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(planned.Result));
        if (generic.IsError)
            DifferentialErrors.RequireAgreement("planned-loop-mode", planned.Result.Error, generic.Error);
        Assert.Equal(genericBudget.TickCount, planned.Budget.TickCount);
        Assert.Equal(genericBudget.ConsumedExpressionCheckpoints, planned.Budget.ConsumedExpressionCheckpoints);
        Assert.Equal(genericBudget.ConsumedSteps, planned.Budget.ConsumedSteps);
        Assert.Equal(genericBudget.PeakDepth, planned.Budget.PeakDepth);
        Assert.Equal(genericBudget.MaterializedItems, planned.Budget.MaterializedItems);

        var asynchronous = (await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache()))).Result;
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(asynchronous));
        if (generic.IsError)
            DifferentialErrors.RequireAgreement("planned-loop-mode-async", asynchronous.Error, generic.Error);
    }

    private static Expr Parsed(string source) => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    /// <summary>
    /// Parses <paramref name="source"/> cleanly and forces the property named by a dotted declaration
    /// path to <see cref="PropertyExposure.Exported"/>; the front end's own verdict on it must be
    /// local-only (the test breaks a correct classification, it does not rely on a wrong one).
    /// </summary>
    private static Expr MisExposed(string source, string path)
        => new Expr.AlgorithmExpr(Export(SourceProvenance.ParseValid(source).Root, path.Split('.'), 0));

    private static Algorithm Export(Algorithm algorithm, string[] path, int depth)
    {
        var owner = Assert.IsType<Algorithm.User>(algorithm);
        var properties = owner.Properties.ToList();
        var index = properties.FindIndex(property => property.Name == path[depth]);
        Assert.True(index >= 0, $"No property '{path[depth]}' on the path {string.Join('.', path)}.");

        var selected = properties[index];
        if (depth < path.Length - 1)
        {
            properties[index] = selected with { Value = Export(selected.Value, path, depth + 1) };
        }
        else
        {
            Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, selected.Exposure);
            properties[index] = selected with
            {
                Exposure = PropertyExposure.Exported,
                RequiredAncestorParameters = [],
                CaptureRequirements = null,
            };
        }

        return owner with { Properties = properties };
    }

    private static IEnumerable<ErrorContext> Contexts(EvalError error)
    {
        for (var current = error; current is EvalError.WithContext wrapped; current = wrapped.Inner)
            yield return wrapped.ErrorContext;
    }
}
