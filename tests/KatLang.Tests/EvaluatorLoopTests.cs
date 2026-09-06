using KatLang.Evaluation;
using System.Numerics;
using System.Reflection;
using System.Runtime.CompilerServices;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorLoopTests
{
    private static (EvalError Generic, EvalError Optimized) AssertEvalFailsInBothLoopModes(string source)
    {
        var generic = EvalFull(source, enableLoopOptimization: false);
        if (generic.IsOk)
            Assert.Fail($"Expected generic evaluation failure but got: {generic.Value}");

        var optimized = EvalFull(source, enableLoopOptimization: true);
        if (optimized.IsOk)
            Assert.Fail($"Expected optimized evaluation failure but got: {optimized.Value}");

        Assert.Equal(
            KatLangError.FromEvalError(generic.Error).Message,
            KatLangError.FromEvalError(optimized.Error).Message);

        return (generic.Error, optimized.Error);
    }

    private static (EvalResult<Result> Result, LoopOptimizationDiagnosticsSnapshot Stats) EvalFullWithLoopDiagnostics(
        string source,
        bool enableLoopOptimization = true)
    {
        var ast = ParseValidRoot(source);
        var diagnostics = new LoopOptimizationDiagnostics();
        var result = Evaluator.Run(
            new Expr.AlgorithmExpr(ast),
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization,
            diagnostics);
        return (result, diagnostics.GetSnapshot());
    }

    private static (
        EvalResult<Result> Result,
        LoopOptimizationDiagnosticsSnapshot LoopStats,
        SequencePipelineDiagnosticsSnapshot SequenceStats) EvalFullWithOptimizationDiagnostics(
            string source,
            bool enableLoopOptimization = true,
            bool enableSequencePipelineOptimization = true)
    {
        var ast = ParseValidRoot(source);
        var loopDiagnostics = new LoopOptimizationDiagnostics();
        var sequenceDiagnostics = new SequencePipelineDiagnostics();
        var result = Evaluator.Run(
            new Expr.AlgorithmExpr(ast),
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization,
            loopDiagnostics,
            enableSequencePipelineOptimization,
            sequenceDiagnostics);
        return (result, loopDiagnostics.GetSnapshot(), sequenceDiagnostics.GetSnapshot());
    }

    private static LoopPlanDiagnosticSnapshot AssertSingleLoopPlan(
        LoopOptimizationDiagnosticsSnapshot stats,
        string identity)
    {
        var plan = Assert.Single(stats.LoopPlans, plan => plan.Identity == identity);
        Assert.True(plan.Optimized, $"Expected optimized loop plan for {identity}, got fallback: {plan.FallbackReason}");
        return plan;
    }

    private static LoopExpressionDiagnosticSnapshot AssertLoopExpression(
        LoopPlanDiagnosticSnapshot plan,
        string role,
        int? index)
        => Assert.Single(
            plan.Expressions,
            expression => expression.Role == role && expression.Index == index);

    private static LoopTempDiagnosticSnapshot AssertLoopTemp(
        LoopPlanDiagnosticSnapshot plan,
        string name)
        => Assert.Single(
            plan.Temps,
            temp => temp.Name == name);

    // â”€â”€ Repeat builtin â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Repeat_SingleParam()
        => AssertEval("repeat({x + 1}, (3), (0))", 3);

    [Fact]
    public void Eval_Repeat_ZeroIterations()
        => AssertEval("repeat({x + 1}, (0), (5))", 5);

    [Fact]
    public void Eval_Repeat_MultipleParams()
        => AssertEval("repeat({a + 1, b + a}, 3, 0, 0)", 3, 3);

    [Fact]
    public void Eval_Repeat_NegativeCount_Fails()
        => AssertEvalFails("repeat({x}, (-1), (0))");

    [Fact]
    public void Eval_Repeat_Factorial()
        => AssertEval("repeat({n + 1, acc * n}, 5, 1, 1):1", 120);

    [Fact]
    public void Eval_Repeat_SimultaneousUpdate_UsesOldStateForAllOutputs()
    {
        var source = """
            Step = b, ~a
            Step.repeat(1, 1, 2)
            """;
        AssertEvalLoopModes(source, 2, 1);
    }

    [Fact]
    public void Eval_LoopStage2_PlannedCases_MatchGenericMode()
    {
        var cases = new (string Source, Decimal128[] Expected)[]
        {
            ("""
                Step = k + 1
                Step.repeat(5, 2):0
                """, [7m]),
            ("""
                Step = k + 1, k <= 10
                Step.while(2):0
                """, [11m]),
            ("""
                Step = k + 1, k * k <= 100
                Step.while(2):0
                """, [11m]),
            ("""
                Outer(num) = {
                    Step = k + 1, k * k <= num
                    Step.while(2):0
                }
                Outer(100)
                """, [11m]),
            ("""
                Test = {
                    Step = k + 1, k <= 10
                    Step.while(2):0
                }

                Run(n) = {
                    Step = value + 1, total + Test()
                    Step.repeat(n, 1, 0):1
                }

                Run(5)
                """, [55m]),
        };

        foreach (var (source, expected) in cases)
            AssertEvalLoopModes(source, expected);
    }

    [Fact]
    public void Eval_LoopStage2_MinimalRepeat_UsesPlannedExpressionDiagnostics()
    {
        var source = """
            Step = k + 1
            Step.repeat(5, 2):0
            """;

        var (result, stats) = EvalFullWithLoopDiagnostics(source);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal([7m], result.Value.ToAtoms());
        Assert.Equal(1, stats.OptimizedLoopHits);
        Assert.Equal(1, stats.LoopPlanBuilds);
        Assert.Equal(5, stats.LoopIterations);
        Assert.Equal(5, stats.PlannedExpressionHits);
        Assert.Equal(0, stats.PlannedExpressionFallbacks);
        Assert.Equal(0, stats.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.Equal(5, stats.PlannedBuiltinOperations);

        var plan = AssertSingleLoopPlan(stats, "Step.repeat");
        Assert.Equal("repeat", plan.Kind);
        Assert.Equal(1, plan.StateArity);
        Assert.Equal(1, plan.BuildCount);
        Assert.Equal(1, plan.ExecutionCount);
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal("Add(StateSlot(k), Const(1))", output.PlanSummary);
        Assert.Null(output.FallbackReason);
    }

    [Fact]
    public void Eval_LoopStage2_MinimalWhile_ReportsOutputAndContinuationPlans()
    {
        var source = """
            Step = k + 1, k <= 100
            Step.while(2):0
            """;

        var (result, stats) = EvalFullWithLoopDiagnostics(source);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal([101m], result.Value.ToAtoms());

        var plan = AssertSingleLoopPlan(stats, "Step.while");
        Assert.Equal("while", plan.Kind);
        Assert.Equal(1, plan.StateArity);

        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal("Add(StateSlot(k), Const(1))", output.PlanSummary);

        var continuation = AssertLoopExpression(plan, "continuation", null);
        Assert.True(continuation.Planned);
        Assert.Equal("LessOrEqual(StateSlot(k), Const(100))", continuation.PlanSummary);
    }

    [Fact]
    public void Eval_OptimizedLoop_VariadicStep_RejectedAtEligibilityGate()
    {
        var source = """
            Step(*values) = values, 0
            Step.while(1, 2, 3)
            """;

        AssertEvalLoopModes(source, 1, 2, 3);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([1m, 2m, 3m], result.Value.ToAtoms());
        Assert.Equal(0, stats.OptimizedLoopHits);
        Assert.Equal(1, stats.FallbackReasons["variadic loop step"]);
    }

    [Fact]
    public void Eval_OptimizedLoop_SequenceValuePatternStep_RejectedAtEligibilityGate()
    {
        var source = """
            Step((x, y)) = x + 1, y + 1, 0
            Step.while((1, 2))
            """;

        AssertEvalLoopModes(source, 1, 2);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([1m, 2m], result.Value.ToAtoms());
        Assert.Equal(0, stats.OptimizedLoopHits);
        Assert.Equal(1, stats.FallbackReasons["variadic loop step"]);
    }

    [Fact]
    public void Eval_OptimizedLoop_FlatFixedScalarStep_RemainsOptimized()
    {
        var source = """
            Step(x) = x + 1, x < 3
            Step.while(1)
            """;

        AssertEvalLoopModes(source, 3);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([3m], result.Value.ToAtoms());
        Assert.Equal(1, stats.OptimizedLoopHits);
        Assert.Equal(0, stats.PlannedExpressionFallbacks);
        Assert.Equal(0, stats.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.DoesNotContain("variadic loop step", stats.FallbackReasons.Keys);
    }

    [Fact]
    public void Eval_LoopStage3A_RepeatOutput_PlansIf()
    {
        var source = """
            Step = x + if(x == 2, 10, 1)
            Step.repeat(3, 1):0
            """;

        AssertEvalLoopModes(source, 13);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(stats, "Step.repeat");
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal(
            "Add(StateSlot(x), If(Equal(StateSlot(x), Const(2)), Const(10), Const(1)))",
            output.PlanSummary);
    }

    [Fact]
    public void Eval_LoopStage3A_RepeatOutput_PlansIfWithCapturedSlot()
    {
        var source = """
            Outer(n) = {
                Step = x + if(x <= n, 1, 0)
                Step.repeat(5, 0):0
            }
            Outer(3)
            """;

        AssertEvalLoopModes(source, 4);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(stats, "Outer.Step.repeat");
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal(
            "Add(StateSlot(x), If(LessOrEqual(StateSlot(x), CapturedSlot(n)), Const(1), Const(0)))",
            output.PlanSummary);
    }

    [Fact]
    public void Eval_LoopStage3A_PlannedIf_PreservesLazyBranchEvaluation()
    {
        var source = """
            Step = x + if(x == 1, 1, 1 / 0)
            Step.repeat(1, 1):0
            """;

        AssertEvalLoopModes(source, 2);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(stats, "Step.repeat");
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Contains("If(", output.PlanSummary, StringComparison.Ordinal);
        Assert.Contains("Divide(Const(1), Const(0))", output.PlanSummary, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_LoopStage3A_IfPlanning_RespectsLexicalShadowing()
    {
        var source = """
            if(a, b, c) = b + c
            Step = if(x, 10, 1)
            Step.repeat(1, 0):0
            """;

        AssertEvalLoopModes(source, 11);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(stats, "Step.repeat");
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.False(output.Planned);
        Assert.Equal("unsupported call: if", output.FallbackReason);
    }

    [Fact]
    public void Eval_LoopStage3B_LocalTempOutput_IsPlanned()
    {
        var source = """
            Step = {
                A = x + 1
                A
            }
            Step.repeat(3, 0):0
            """;

        AssertEvalLoopModes(source, 3);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(stats, "Step.repeat");
        var temp = AssertLoopTemp(plan, "A");
        Assert.True(temp.Planned, temp.FallbackReason);
        Assert.Equal("Add(StateSlot(x), Const(1))", temp.PlanSummary);

        // `A` reads `x`, which the step does not bind itself, so the front end gives `A`
        // the implicit parameter `x` and rewrites the reference to the forwarding call
        // `A(x)` — a user call, evaluated fresh on every call by both strategies
        // (TempCall), never the memoized zero-argument read (TempSlot).
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal("TempCall(A)", output.PlanSummary);
    }

    [Fact]
    public void Eval_LoopStage3B_LocalTemp_RecomputesEachIteration()
    {
        var source = """
            Step = {
                A = x
                A + 1
            }
            Step.repeat(3, 0):0
            """;

        AssertEvalLoopModes(source, 3);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(stats, "Step.repeat");
        var temp = AssertLoopTemp(plan, "A");
        Assert.True(temp.Planned, temp.FallbackReason);
        Assert.Equal("StateSlot(x)", temp.PlanSummary);

        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal("Add(TempCall(A), Const(1))", output.PlanSummary);
    }

    [Fact]
    public void Eval_LoopStage3B_UnusedLocalTemp_IsNotEvaluated()
    {
        var source = """
            Step = {
                A = 1 / 0
                x + 1
            }
            Step.repeat(1, 0):0
            """;

        AssertEvalLoopModes(source, 1);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(stats, "Step.repeat");
        var temp = AssertLoopTemp(plan, "A");
        Assert.True(temp.Planned, temp.FallbackReason);
        Assert.Equal("Divide(Const(1), Const(0))", temp.PlanSummary);

        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal("Add(StateSlot(x), Const(1))", output.PlanSummary);
    }

    [Fact]
    public void Eval_LoopStage3B_LocalTemp_UsedByContinuation()
    {
        var source = """
            Step = {
                A = x + 1
                A, A <= 5
            }
            Step.while(0):0
            """;

        AssertEvalLoopModes(source, 5);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal([5m], result.Value.ToAtoms());
        Assert.Equal(1, stats.OptimizedLoopHits);

        var plan = AssertSingleLoopPlan(stats, "Step.while");
        var temp = AssertLoopTemp(plan, "A");
        Assert.True(temp.Planned, temp.FallbackReason);
        Assert.Equal("Add(StateSlot(x), Const(1))", temp.PlanSummary);

        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal("TempCall(A)", output.PlanSummary);

        var continuation = AssertLoopExpression(plan, "continuation", null);
        Assert.True(continuation.Planned);
        Assert.Equal("LessOrEqual(TempCall(A), Const(5))", continuation.PlanSummary);
    }

    [Theory]
    [InlineData("RepeatLoopGenericCounted")]
    [InlineData("RepeatLoopGenericCountedAsync")]
    public void RepeatLoopGenericCounter_IsLongAtBothMirrorSites(string methodName)
    {
        var method = typeof(Evaluator).GetMethod(methodName, BindingFlags.NonPublic | BindingFlags.Static)!;
        Assert.Equal(typeof(long), Assert.Single(method.GetParameters(), parameter => parameter.Name == "count").ParameterType);
        var stateMachine = method.GetCustomAttribute<AsyncStateMachineAttribute>()?.StateMachineType;
        var numericLocals = stateMachine is null
            ? method.GetMethodBody()!.LocalVariables.Select(local => local.LocalType)
            : stateMachine.GetFields(BindingFlags.Instance | BindingFlags.NonPublic | BindingFlags.Public)
                .Where(field => field.Name != "<>1__state"
                    && !method.GetParameters().Any(parameter => parameter.Name == field.Name))
                .Select(field => field.FieldType);

        Assert.Equal(typeof(long), Assert.Single(numericLocals, type => type == typeof(int) || type == typeof(long)));
    }

    [Fact]
    public void Eval_LoopStage3B_SquareFreeLocalTemp_PlansInnerLoop()
    {
        var source = """
            IsSquareFree(num) = {
                Step = {
                    K2 = k * k
                    k + 1, s + if(num mod K2 == 0, 1, 0), K2 <= num and s <= 0
                }
                Step.while(2, 0):1 == 0
            }
            IsSquareFree(100)
            """;

        AssertEvalLoopModes(source, 0);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(stats, "IsSquareFree.Step.while");
        var temp = AssertLoopTemp(plan, "K2");
        Assert.True(temp.Planned, temp.FallbackReason);
        Assert.Equal("Multiply(StateSlot(k), StateSlot(k))", temp.PlanSummary);

        var output0 = AssertLoopExpression(plan, "output", 0);
        Assert.True(output0.Planned);
        Assert.Equal("Add(StateSlot(k), Const(1))", output0.PlanSummary);

        var output1 = AssertLoopExpression(plan, "output", 1);
        Assert.True(output1.Planned);
        Assert.Contains("TempSlot(K2)", output1.PlanSummary, StringComparison.Ordinal);
        Assert.Contains("If(", output1.PlanSummary, StringComparison.Ordinal);

        var continuation = AssertLoopExpression(plan, "continuation", null);
        Assert.True(continuation.Planned);
        Assert.Contains("LessOrEqual(TempSlot(K2), CapturedSlot(num))", continuation.PlanSummary, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_LoopStage3B_UnsupportedParameterizedLocalTemp_FallsBackClearly()
    {
        var source = """
            Step = {
                A(x) = x + 1
                A(k), k <= 10
            }
            Step.while(0):0
            """;

        AssertEvalLoopModes(source, 11);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(stats, "Step.while");
        var temp = AssertLoopTemp(plan, "A");
        Assert.False(temp.Planned);
        Assert.Equal("unsupported local property with explicit parameters: A", temp.FallbackReason);

        var output = AssertLoopExpression(plan, "output", 0);
        Assert.False(output.Planned);
        Assert.Equal("unsupported call: A", output.FallbackReason);

        var continuation = AssertLoopExpression(plan, "continuation", null);
        Assert.True(continuation.Planned);
        Assert.Equal("LessOrEqual(StateSlot(k), Const(10))", continuation.PlanSummary);
    }

    [Fact]
    public void Eval_LoopStage3A_SquareFreeStyleLoop_PlansInnerIfOutput()
    {
        var source = """
            IsSquareFree(num) = {
                Step = k + 1, s + if(num mod (k * k) == 0, 1, 0), k * k <= num and s <= 0
                Step.while(2, 0):1 == 0
            }
            IsSquareFree(100)
            """;

        var (result, stats) = EvalFullWithLoopDiagnostics(source);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal([0m], result.Value.ToAtoms());

        var plan = AssertSingleLoopPlan(stats, "IsSquareFree.Step.while");
        Assert.Equal("while", plan.Kind);
        Assert.Equal(2, plan.StateArity);

        var output0 = AssertLoopExpression(plan, "output", 0);
        Assert.True(output0.Planned);
        Assert.Equal("Add(StateSlot(k), Const(1))", output0.PlanSummary);

        var output1 = AssertLoopExpression(plan, "output", 1);
        Assert.True(output1.Planned);
        Assert.Contains("If(", output1.PlanSummary, StringComparison.Ordinal);
        Assert.Contains("Mod(CapturedSlot(num), Multiply(StateSlot(k), StateSlot(k)))", output1.PlanSummary, StringComparison.Ordinal);

        var continuation = AssertLoopExpression(plan, "continuation", null);
        Assert.True(continuation.Planned);
        Assert.Contains("And(", continuation.PlanSummary, StringComparison.Ordinal);
        Assert.Contains("CapturedSlot(num)", continuation.PlanSummary, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_LoopStage3A_SquareFreeCountOuterRepeat_ReportsUserCallFallbackInsideIfCondition()
    {
        var source = """
            IsSquareFree(num) = {
                Step = k + 1, s + if(num mod (k * k) == 0, 1, 0), k * k <= num and s <= 0
                Step.while(2, 0):1 == 0
            }

            SquareFreeCount(n) = {
                Step = value + 1, total + if(IsSquareFree(value), 1, 0)
                Step.repeat(n, 1, 0):1
            }

            SquareFreeCount(20)
            """;

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var outerPlan = AssertSingleLoopPlan(stats, "SquareFreeCount.Step.repeat");
        var outerOutput = AssertLoopExpression(outerPlan, "output", 1);
        Assert.False(outerOutput.Planned);
        Assert.Equal("unsupported if condition: unsupported call: IsSquareFree", outerOutput.FallbackReason);

        var innerPlan = AssertSingleLoopPlan(stats, "IsSquareFree.Step.while");
        var innerOutput = AssertLoopExpression(innerPlan, "output", 1);
        Assert.True(innerOutput.Planned);
        Assert.Contains("If(", innerOutput.PlanSummary, StringComparison.Ordinal);
    }

    // â”€â”€ While builtin â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_While_CountDown()
        => AssertEval("while({x - 1, x - 1}, (3))", 1);

    [Fact]
    public void Eval_While_SingleOutputStep_UsesGenericSingletonSemantics()
        => AssertEvalLoopModes("while({x - 1}, 3)", 1);

    [Fact]
    public void Eval_While_GcdDotCall_ProjectsFinalState()
    {
        var source = """
            GcdStep = b, ~a mod b, a mod b != 0
            GcdStep.while(12, 30):1
            """;
        AssertEvalLoopModes(source, 6);
    }

    [Fact]
    public void Eval_While_TerminatingNextStateIsNotCommitted()
    {
        var source = """
            Step = x + 10, x < 3
            Step.while(0)
            """;
        AssertEvalLoopModes(source, 10);
    }

    [Fact]
    public void Eval_While_LocalPropertyRecomputesPerIteration()
    {
        var source = """
            Step = {
                A = x
                A + 1, x < 3
            }
            Step.while(0)
            """;
        AssertEvalLoopModes(source, 3);
    }

    [Fact]
    public void Eval_While_NestedStepCapturesParentParameter()
    {
        var source = """
            Outer(n) = {
                Step = x + n, x < 10
                Step.while(0)
            }
            Outer(2)
            """;
        AssertEvalLoopModes(source, 10);
    }

    [Fact]
    public void Eval_While_NestedStepUsesMutableStateAndCapturedParentValues()
    {
        var source = """
            Outer(limit, offset) = {
                Reached = candidate + offset >= limit
                Step = candidate + 1, not Reached
                Step.while(0)
            }
            Outer(6, 2)
            """;
        AssertEvalLoopModes(source, 4);
    }

    [Fact]
    public void Eval_While_BadContinuationValue_KeepsTypeMismatchMeaning()
    {
        var (_, optimizedError) = AssertEvalFailsInBothLoopModes("while({x + 1, 'keep'}, 0)");
        var error = Innermost(optimizedError);
        var typeMismatch = Assert.IsType<EvalError.TypeMismatch>(error);
        Assert.Contains("Expected a number", typeMismatch.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_Repeat_BadStateArity_KeepsLoopBindingContext()
    {
        var (_, optimizedError) = AssertEvalFailsInBothLoopModes("repeat({x + 1}, 2, 0, 1)");
        var formatted = KatLangError.FromEvalError(optimizedError).Message;
        Assert.Contains("`repeat` step expects 1 state value", formatted, StringComparison.Ordinal);
        Assert.Contains("current loop state has 2 state values", formatted, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_While_EvenFibonacciSum()
    {
        // Sums even Fibonacci numbers <= 100: 2 + 8 + 34 = 44.
        // Grace (~a) reorders detected params [b, a, total] -> [a, b, total].
        // Initial state arguments 1, 2, 0 bind a=1, b=2, total=0.
        // The step with b=144 (first even Fibonacci > 100) triggers cont=0;
        // pre-check semantics return the prior state (total=44), not the updated one.
        var source = """
            Algo = b, ~a + b, total + if(b mod 2 == 0, b, 0), b <= 100
            Sum = Algo.while(1, 2, 0) : 2
            Sum
            """;
        AssertEval(source, 44);
    }

    [Fact]
    public void Eval_While_ImmediateExit()
        => AssertEval("while({x, 0}, (5))", 5);

    [Fact]
    public void Eval_While_DotCall_SumMultiplesOf3Or5()
    {
        var source = """
            Algo = n - 1, result + if(n mod 3==0 or n mod 5==0, n, 0), n > 2
            Sum = Algo.while(x, 0) : 1
            Sum(999)
            """;
        AssertEval(source, 233168);
    }

    // ── While/repeat multi-item init boundaries ──────────────────────────────────

    [Fact]
    public void Eval_While_DotCall_BareComma_Works()
    {
        // Algo.while(x, 0) with bare comma starts with two explicit state slots.
        var source = """
            Algo = n - 1, result + if(n mod 3==0 or n mod 5==0, n, 0), n > 2
            Sum = Algo.while(x, 0) : 1
            Sum(999)
            """;
        AssertEval(source, 233168);
    }

    [Fact]
    public void Eval_While_DotCall_ParenSequenceValueInit_IsOneSlot()
    {
        var source = """
            Algo = n - 1, result + if(n mod 3==0 or n mod 5==0, n, 0), n > 2
            Sum = Algo.while((x, 0)) : 1
            Sum(999)
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_While_DotCall_ExistingInit_ExplicitSelectionsWork()
    {
        var source = """
            Algo = n - 1, result + if(n mod 3==0 or n mod 5==0, n, 0), n > 2
            Init = x, 0
            Sum = Algo.while(Init(x):0, Init(x):1) : 1
            Sum(999)
            """;
        AssertEval(source, 233168);
    }

    [Fact]
    public void Eval_While_DotCall_BareComma_NoParams()
    {
        var source = """
            Algo = n - 1, result + if(n mod 3==0 or n mod 5==0, n, 0), n > 2
            Sum = Algo.while(x, 0) : 1
            Sum(999)
            """;
        AssertEval(source, 233168);
    }

    // â”€â”€ Atoms builtin â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_While_DirectCall_MultiInit()
    {
        // while(Step, s1, s2, ...) starts with one state slot per explicit init arg.
        var source = """
            Step = n - 1, acc + n, n > 1
            while(Step, 5, 0) : 1
            """;
        // 5+4+3+2 = 14 (stops when n=1, cont=0, returns prior state)
        AssertEval(source, 14);
    }

    [Fact]
    public void Eval_Repeat_DirectCall_MultiInit()
    {
        // repeat(Step, n, s1, s2) starts with two explicit state slots.
        var source = """
            Step = a + 1, b + a
            repeat(Step, 3, 0, 0)
            """;
        AssertEval(source, 3, 3);
    }

    [Fact]
    public void Eval_Repeat_DotCall_MultiInit()
    {
        // Step.repeat(n, s1, s2) lexical fallback preserves the explicit state slots.
        var source = """
            Step = a + 1, b + a
            Step.repeat(3, 0, 0)
            """;
        AssertEval(source, 3, 3);
    }

    [Fact]
    public void Eval_While_DotCall_SingleInit_StillWorks()
    {
        var source = """
            Step = x - 1, x - 1
            Step.while(3)
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Repeat_DotCall_SingleInit_StillWorks()
    {
        var source = """
            Step = x + 1
            Step.repeat(3, 0)
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_While_DirectCall_SingleInit_StillWorks()
        => AssertEval("while({x - 1, x - 1}, 3)", 1);

    [Fact]
    public void Eval_Repeat_DirectCall_SingleInit_StillWorks()
        => AssertEval("repeat({x + 1}, 3, 0)", 3);

    [Fact]
    public void Eval_DotCall_TrailingBrace_StillWorks()
    {
        var source = """
            F = x + 1
            F{3}
            """;
        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_DotCall_PropertyPrecedence_WhileShadow()
    {
        // If algorithm A has a real property named while, dotCall must
        // resolve as property call, not lexical builtin fallback packaging
        var source = """
            A = {
                while = x + 1
            }
            A.while(10)
            """;
        AssertEval(source, 11);
    }

    [Fact]
    public void Eval_DotCall_PropertyPrecedence_RepeatShadow()
    {
        var source = """
            A = {
                repeat = x * 2
            }
            A.repeat(5)
            """;
        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_While_DotCall_NoArgs_Fails()
    {
        var source = """
            Step = x - 1, x > 0
            Step.while()
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_Repeat_DotCall_NoArgs_Fails()
    {
        var source = """
            Step = x + 1
            Step.repeat()
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_Repeat_DotCall_OneArg_Fails()
    {
        var source = """
            Step = x + 1
            Step.repeat(3)
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_LoopPlanner_CountedCallbackParameterFullyPlansSquareFreeInnerLoop()
    {
        var source = """
            IsSquareFree(num) = {
                Step = {
                    Square = k * k
                    k + 1, s + if(num mod Square == 0, 1, 0), Square <= num and s <= 0
                }
                Step.while(2, 0):1 == 0
            }

            SquareFreeCount = range(1,N).filter(IsSquareFree).count

            SquareFreeCount(100)
            """;

        var generic = EvalFull(
            source,
            enableLoopOptimization: false,
            enableSequencePipelineOptimization: false);
        if (generic.IsError)
            Assert.Fail($"Expected generic success but got error: {generic.Error}");

        var (result, loopStats, sequenceStats) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected optimized success but got error: {result.Error}");

        Assert.Equal(generic.Value.ToAtoms(), result.Value.ToAtoms());
        Assert.Equal(1, sequenceStats.FilterCountFusionHits);
        Assert.Equal(1, sequenceStats.DirectRangeFusionHits);
        Assert.Equal(100, sequenceStats.FilterCountPredicateCalls);
        Assert.Equal(100, sequenceStats.AvoidedSourceMaterializations);
        Assert.Equal(0, loopStats.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.True(loopStats.CountedParameterReferencesPlanned > 0);
        Assert.Equal(0, loopStats.CountedParameterReferencesFallbacks);

        var sequencePipeline = Assert.Single(sequenceStats.Pipelines, pipeline => pipeline.Optimized);
        Assert.Equal("dot-filter-dot-count", sequencePipeline.Form);
        Assert.Equal("direct range iteration", sequencePipeline.SourceExecution);

        var loopPlan = AssertSingleLoopPlan(loopStats, "IsSquareFree.Step.while");
        var squareTemp = AssertLoopTemp(loopPlan, "Square");
        Assert.True(squareTemp.Planned);
        Assert.Equal("Multiply(StateSlot(k), StateSlot(k))", squareTemp.PlanSummary);

        var output0 = AssertLoopExpression(loopPlan, "output", 0);
        var output1 = AssertLoopExpression(loopPlan, "output", 1);
        var continuation = AssertLoopExpression(loopPlan, "continuation", null);

        Assert.True(output0.Planned);
        Assert.Equal("Add(StateSlot(k), Const(1))", output0.PlanSummary);
        Assert.True(output1.Planned);
        Assert.Contains("CountedParamSlot(num)", output1.PlanSummary, StringComparison.Ordinal);
        Assert.True(continuation.Planned);
        Assert.Contains("CountedParamSlot(num)", continuation.PlanSummary, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_LoopPlanner_CountedCallbackParameterPlansMinimalNestedLoop()
    {
        var source = """
            Pred(num) = {
                Step = k + 1, k <= num
                Step.while(1):0 > 0
            }

            range(1,10).filter(Pred).count
            """;

        AssertEvalLoopModes(source, 10);

        var (result, loopStats, sequenceStats) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([10m], result.Value.ToAtoms());
        Assert.Equal(1, sequenceStats.FilterCountFusionHits);
        Assert.Equal(1, sequenceStats.DirectRangeFusionHits);
        Assert.Equal(0, loopStats.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.True(loopStats.CountedParameterReferencesPlanned > 0);
        Assert.Equal(0, loopStats.CountedParameterReferencesFallbacks);

        var plan = AssertSingleLoopPlan(loopStats, "Pred.Step.while");
        var continuation = AssertLoopExpression(plan, "continuation", null);
        Assert.True(continuation.Planned);
        Assert.Equal("LessOrEqual(StateSlot(k), CountedParamSlot(num))", continuation.PlanSummary);
    }

    [Fact]
    public void Eval_LoopPlanner_LoopStateShadowsOuterCountedCallbackParameterInWhile()
    {
        var source = """
            Inner = {
                Step = n + 1, n < limit
                Step.while(limit - limit):0
            }

            UsesInner = Inner(n)

            (2,3).map(UsesInner)
            """;

        AssertEvalLoopModes(source, 2, 3);

        var (result, loopStats, _) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([2m, 3m], result.Value.ToHostAtoms());
        Assert.Equal(0, loopStats.CountedParameterReferencesPlanned);

        var plan = AssertSingleLoopPlan(loopStats, "Inner.Step.while");
        var output = AssertLoopExpression(plan, "output", 0);
        var continuation = AssertLoopExpression(plan, "continuation", null);

        Assert.True(output.Planned);
        Assert.Equal("Add(StateSlot(n), Const(1))", output.PlanSummary);
        Assert.DoesNotContain("CountedParamSlot(n)", output.PlanSummary, StringComparison.Ordinal);

        Assert.True(continuation.Planned);
        Assert.Equal("LessThan(StateSlot(n), CapturedSlot(limit))", continuation.PlanSummary);
        Assert.DoesNotContain("CountedParamSlot(n)", continuation.PlanSummary, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_LoopPlanner_LoopStateShadowsOuterCountedCallbackParameterInRepeat()
    {
        var source = """
            Inner = {
                Step = n + 1
                Step.repeat(limit, 0):0
            }

            UsesInner = Inner(n)

            (2,3).map(UsesInner)
            """;

        AssertEvalLoopModes(source, 2, 3);

        var (result, loopStats, _) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([2m, 3m], result.Value.ToHostAtoms());
        Assert.Equal(0, loopStats.CountedParameterReferencesPlanned);

        var plan = AssertSingleLoopPlan(loopStats, "Inner.Step.repeat");
        var output = AssertLoopExpression(plan, "output", 0);

        Assert.True(output.Planned);
        Assert.Equal("Add(StateSlot(n), Const(1))", output.PlanSummary);
        Assert.DoesNotContain("CountedParamSlot(n)", output.PlanSummary, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_LoopPlanner_LoopStateShadowsOuterCountedCallbackParameterInFilter()
    {
        var source = """
            Inner = {
                Step = n + 1, n < limit
                Step.while(limit - limit):0
            }

            Keep = Inner(n) == n

            (2,3).filter(Keep)
            """;

        AssertEvalLoopModes(source, 2, 3);
    }

    [Fact]
    public void Eval_LoopPlanner_LoopStateShadowsOuterCountedCallbackParameterInReduce()
    {
        var source = """
            Inner = {
                Step = n + 1
                Step.repeat(limit, 0):0
            }

            AddInner(n, acc) = acc + Inner(n)

            (2,3).reduce(AddInner, 0)
            """;

        AssertEvalLoopModes(source, 5);
    }

    [Fact]
    public void Eval_LoopPlanner_OriginalEmirpFilterCallbackNameDoesNotLeakIntoReverseStep()
    {
        var source = """
            IsPrime = {
                Step = {
                    k+1, s + if(n mod k == 0, 1, 0), k <= n div 2 and s <= 0
                }
                n > 1 and Step.while(2,0):1 == 0
            }

            Reverse = {
                Step = Math.Floor(n / 10), rev * 10 + n mod 10, n > 0
                Step.while(x, 0):1
            }

            IsEmirp = n > 11 and IsPrime(n) and IsPrime(Reverse(n))

            (11,12,13,14,15,16,17).filter(IsEmirp)
            """;

        AssertEvalLoopModes(source, 13, 17);

        var (result, loopStats, _) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([13m, 17m], result.Value.ToHostAtoms());

        var reversePlan = AssertSingleLoopPlan(loopStats, "Reverse.Step.while");
        var revOutput = AssertLoopExpression(reversePlan, "output", 1);
        var continuation = AssertLoopExpression(reversePlan, "continuation", null);

        Assert.True(revOutput.Planned);
        Assert.Contains("Mod(StateSlot(n), Const(10))", revOutput.PlanSummary, StringComparison.Ordinal);
        Assert.DoesNotContain("CountedParamSlot(n)", revOutput.PlanSummary, StringComparison.Ordinal);

        Assert.True(continuation.Planned);
        Assert.Equal("GreaterThan(StateSlot(n), Const(0))", continuation.PlanSummary);
    }

    [Fact]
    public void Eval_LoopPlanner_DifferentOuterNameKeepsInnerStateBinding()
    {
        var source = """
            Inner = {
                Step = n + 1, n < limit
                Step.while(limit - limit):0
            }

            UsesInner = Inner(m)

            (2,3).map(UsesInner)
            """;

        AssertEvalLoopModes(source, 2, 3);

        var (result, loopStats, _) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(loopStats, "Inner.Step.while");
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal("Add(StateSlot(n), Const(1))", output.PlanSummary);
    }

    [Fact]
    public void Eval_LoopPlanner_RenamedInnerStateAvoidsCallbackNameCollision()
    {
        var source = """
            Inner = {
                Step = s + 1, s < limit
                Step.while(limit - limit):0
            }

            UsesInner = Inner(n)

            (2,3).map(UsesInner)
            """;

        AssertEvalLoopModes(source, 2, 3);

        var (result, loopStats, _) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(loopStats, "Inner.Step.while");
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal("Add(StateSlot(s), Const(1))", output.PlanSummary);
    }

    [Fact]
    public void Eval_LoopPlanner_UnshadowedOuterCountedCallbackParameterRemainsVisible()
    {
        var source = """
            UsesLimit = {
                Step = s + 1, s < limit
                Step.while(limit - limit):0
            }

            (2,3).map(UsesLimit)
            """;

        AssertEvalLoopModes(source, 2, 3);

        var (result, loopStats, _) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([2m, 3m], result.Value.ToHostAtoms());
        Assert.True(loopStats.CountedParameterReferencesPlanned > 0);

        var plan = AssertSingleLoopPlan(loopStats, "UsesLimit.Step.while");
        var continuation = AssertLoopExpression(plan, "continuation", null);
        Assert.True(continuation.Planned);
        Assert.Equal("LessThan(StateSlot(s), CountedParamSlot(limit))", continuation.PlanSummary);
    }

    [Fact]
    public void Eval_LoopPlanner_DirectCallCapturedSlotPlanningRemainsUnchanged()
    {
        var source = """
            Pred(num) = {
                Step = k + 1, k <= num
                Step.while(1):0
            }

            Pred(10)
            """;

        AssertEvalLoopModes(source, 11);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([11m], result.Value.ToAtoms());
        Assert.Equal(0, stats.CountedParameterReferencesPlanned);
        Assert.Equal(0, stats.CountedParameterReferencesFallbacks);

        var plan = AssertSingleLoopPlan(stats, "Pred.Step.while");
        var continuation = AssertLoopExpression(plan, "continuation", null);
        Assert.True(continuation.Planned);
        Assert.Equal("LessOrEqual(StateSlot(k), CapturedSlot(num))", continuation.PlanSummary);
        Assert.DoesNotContain("CountedParamSlot", continuation.PlanSummary, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_LoopPlanner_CountedCallbackParameterNonNumericShapeFallsBack()
    {
        var source = """
            Pred(text) = {
                Step = if(text == 'a', k + 1, k + 1), k <= 1
                Step.while(0):0 > 0
            }

            ('a').filter(Pred).count
            """;

        AssertEvalLoopModes(source, 1);

        var (result, loopStats, sequenceStats) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([1m], result.Value.ToAtoms());
        Assert.Equal(1, sequenceStats.FilterCountFusionHits);
        Assert.Equal(1, loopStats.CountedParameterReferencesFallbacks);
        Assert.Contains(
            loopStats.FallbackReasons,
            reason => reason.Key == "unsupported counted parameter value shape: text (counted parameter is non-numeric: 'a')");

        var plan = AssertSingleLoopPlan(loopStats, "Pred.Step.while");
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.False(output.Planned);
        Assert.Equal(
            "unsupported if condition: unsupported counted parameter value shape: text (counted parameter is non-numeric: 'a')",
            output.FallbackReason);
    }

    [Fact]
    public void Eval_LoopPlanner_CountedCallbackParameterSequenceValueMultiEmitShapeFallsBack()
    {
        var source = """
            Pred(item) = {
                Step = if(1, k + 1, item), k <= 1
                Step.while(0):0 > 0
            }

            (((1, 2), (3, 4))).filter(Pred).count
            """;

        AssertEvalLoopModes(source, 2);

        var (result, loopStats, sequenceStats) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([2m], result.Value.ToAtoms());
        Assert.Equal(1, sequenceStats.FilterCountFusionHits);
        Assert.Equal(0, loopStats.CountedParameterReferencesPlanned);
        Assert.Equal(2, loopStats.CountedParameterReferencesFallbacks);
        Assert.Contains(
            loopStats.FallbackReasons,
            reason => reason.Key == "unsupported counted parameter value shape: item (counted parameter emitted multiple values (2))");

        var plan = AssertSingleLoopPlan(loopStats, "Pred.Step.while");
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.False(output.Planned);
        Assert.Equal(
            "unsupported if false branch: unsupported counted parameter value shape: item (counted parameter emitted multiple values (2))",
            output.FallbackReason);

        var continuation = AssertLoopExpression(plan, "continuation", null);
        Assert.True(continuation.Planned);
        Assert.Equal("LessOrEqual(StateSlot(k), Const(1))", continuation.PlanSummary);
    }

    [Fact]
    public void Eval_LoopOptimizer_ListValuedStateSlot_MatchesGenericMode()
    {
        // A step expression may produce an exact list state value via a
        // collection builtin; optimized and generic loop modes must carry the
        // same list value through repeat and while state slots.
        AssertEvalResultLoopModes(
            """
            Step(a, b) = take(a, 1), count(a)
            Step.repeat(2, 1, 0)
            """,
            Result.FromItems([ListValue(Atom(1)), Atom(1)]));

        AssertEvalResultLoopModes(
            """
            Step(a, b) = take(a, 1), b + 1, b < 2
            Step.while(5, 0)
            """,
            Result.FromItems([ListValue(Atom(5)), Atom(2)]));
    }

    [Fact]
    public void Eval_LoopOptimizer_CanonicalizesNestedEmptyStateSlot_MatchesGenericMode()
        // A loop whose next-state slot becomes `(())` now carries the canonical
        // empty sequence value, matching the generic loop.
        => AssertEvalLoopModes(
            """
            Step(a, b) = if(a == 1, (()), a.take(1)), count(a)
            Step.repeat(2, 1, 0)
            """,
            0);

    // Optimized-loop parity: a captured sequence value compared with `==` inside an
    // optimized repeat loop must use the same structural equality as normal
    // evaluation. The Equal node is planned (not a generic fallback) and runs entirely
    // inside the optimized loop harness, pinning that ApplyPlannedBinary delegates
    // equality to Evaluator.ApplyBinaryOperator and never reintroduces a numeric-only
    // fast path (which would throw a numeric-scalar type mismatch on the sequence
    // operands). `pair == pair` is 1, so x increments to 5 over 5 iterations.
    [Fact]
    public void Eval_OptimizedLoop_CapturedSequenceValueEquality_UsesStructuralEquality()
    {
        var source = """
            Outer(pair) = {
                Step = x + (pair == pair)
                Step.repeat(5, 0)
            }
            Outer((1, 2))
            """;

        // Generic and optimized modes must agree and both return 5.
        AssertEvalLoopModes(source, 5);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal([5m], result.Value.ToAtoms());

        // The optimized loop harness ran the equality every iteration with no fallback
        // to generic evaluation, so ApplyPlannedBinary handled the sequence-value Eq.
        Assert.Equal(1, stats.OptimizedLoopHits);
        Assert.Equal(5, stats.PlannedExpressionHits);
        Assert.Equal(0, stats.PlannedExpressionFallbacks);
        Assert.Equal(0, stats.GenericExpressionEvaluationsInsideOptimizedLoops);

        var plan = AssertSingleLoopPlan(stats, "Outer.Step.repeat");
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal(
            "Add(StateSlot(x), Equal(CapturedSlot(pair), CapturedSlot(pair)))",
            output.PlanSummary);
        Assert.Null(output.FallbackReason);
    }

    [Fact]
    public void Eval_FlatFixedLoopStep_ExplicitUserStep_PreservesGenericBindingBehavior()
    {
        AssertEvalLoopModes(
            """
            Step(a, b) = b, a + b, a + b < 10
            Step.while(1, 1)
            """,
            5, 8);
    }

    [Fact]
    public void Eval_PatternedLoopStep_WrongTopLevelShapeUsesLoopArityDiagnostic()
    {
        var (generic, optimized) = AssertEvalFailsInBothLoopModes(
            """
            Step((x, y)) = x + y
            Step.repeat(1, 1, 2)
            """);

        foreach (var error in new[] { generic, optimized })
        {
            // The step has ONE top-level state slot (the pattern `(x, y)`), so the
            // binder-computed expected count is 1 — never the flattened capture
            // count 2, which used to produce the contradictory 2-vs-2 payload.
            var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
            Assert.Equal(1, arity.Expected);
            Assert.Equal(2, arity.Actual);

            var formatted = KatLangError.FromEvalError(error).Message;
            Assert.Contains("`repeat` step expects 1 state value for 1 parameter '(x, y)'", formatted, StringComparison.Ordinal);
            Assert.Contains("current loop state has 2 state values", formatted, StringComparison.Ordinal);
            Assert.DoesNotContain("Callable `Step((x, y))`", formatted, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void Eval_SequenceValueVariadicLoopStep_YellowstoneHistoryNeedsNoCleanup()
    {
        AssertEvalLoopModes(
            """
            GcdStep = b, ~a mod b, a mod b != 0
            Gcd = GcdStep.while(a, b):1

            FindNext(*history, pre1, pre2) = {
                IsYSCandidate(candidate) = not history.contains(candidate) and
                    Gcd(candidate, pre1) == 1 and
                    Gcd(candidate, pre2) != 1

                FindStep = candidate + 1, not IsYSCandidate(candidate)
                FindStep.while(1):0
            }

            YSStep((*history), pre2, pre1) = {
                Next = FindNext(history*, pre1, pre2)
                (history*, Next), pre1, Next
            }

            YSStep.repeat(27, (1, 2, 3), 2, 3):0
            """,
            1, 2, 3, 4, 9, 8, 15, 14, 5, 6,
            25, 12, 35, 16, 7, 10, 21, 20, 27, 22,
            39, 11, 13, 33, 26, 45, 28, 51, 32, 17);
    }

    [Fact]
    public void Eval_VariadicLoopStep_RepeatOneIterationCapturesStateItems()
    {
        AssertEvalResultLoopModes(
            """
            AppendNext(*history) = history*, history.atoms.last + 1
            AppendNext.repeat(1, 1, 2, 4)
            """,
            ResultFromAtoms(1, 2, 4, 5));
    }

    [Fact]
    public void Eval_VariadicLoopStep_RepeatTwoIterationsKeepsExpandedState()
    {
        AssertEvalResultLoopModes(
            """
            AppendNext(*history) = history*, history.atoms.last + 1
            AppendNext.repeat(2, 1, 2, 4)
            """,
            ResultFromAtoms(1, 2, 4, 5, 6));
    }

    [Fact]
    public void Eval_VariadicLoopStep_DirectCallBaselineMatchesRepeatSteps()
    {
        AssertEvalSequenceModes(
            """
            AppendNext(*history) = history*, history.atoms.last + 1
            AppendNext((1, 2, 4))*, AppendNext((1, 2, 4, 5))
            """,
            1, 2, 4, 5, 1, 2, 4, 5, 6);
    }

    [Fact]
    public void Eval_VariadicLoopStep_ImplicitOrdinaryRepeatStillFails()
    {
        var (generic, optimized) = AssertEvalFailsInBothLoopModes(
            """
            AppendNext = history*, history.atoms.last + 1
            AppendNext.repeat(1, 1, 2, 4)
            """);

        foreach (var error in new[] { generic, optimized })
        {
            var formatted = KatLangError.FromEvalError(error).Message;
            Assert.Contains("`repeat` step expects 1 state value", formatted, StringComparison.Ordinal);
            Assert.Contains("current loop state has 3 state values", formatted, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void Eval_VariadicLoopStep_WithPrefix_CapturesRemainingStateItemsAsOneListSlot()
    {
        // The step returns the collected list unspread, so the collected list
        // [2, 3] stays one state slot beside the spread first item.
        AssertEvalResultLoopModes(
            """
            Step(first, *rest) = first*, rest
            Step.repeat(1, 1, 2, 3)
            """,
            Result.FromItems([Atom(1), ListValue(Atom(2), Atom(3))]));
    }

    [Fact]
    public void Eval_VariadicLoopStep_WithSuffix_CapturesLeadingStateItems()
    {
        AssertEvalResultLoopModes(
            """
            Step(*values, last) = values*, last
            Step.repeat(1, 1, 2, 3)
            """,
            ResultFromAtoms(1, 2, 3));
    }

    [Fact]
    public void Eval_VariadicLoopStep_WithPrefixAndSuffix_CapturesMiddleStateItems()
    {
        AssertEvalResultLoopModes(
            """
            Step(first, *middle, last) = first*, middle*, last
            Step.repeat(1, 1, 2, 3, 4)
            """,
            ResultFromAtoms(1, 2, 3, 4));
    }

    [Fact]
    public void Eval_VariadicLoopStep_ExtraMiddleStateSlots_RepeatTwoIterations()
    {
        // Four state slots bind first=0, middle=[5, 5] (the collected exact list),
        // last=10; the body re-spreads middle with `middle*` so the extra middle slots
        // survive across iterations. Mirrors the Lean guard
        // variadicLoopStepExtraMiddleRepeatsTwice.
        AssertEvalLoopModes(
            """
            Step(first, *middle, last) = first + 1, middle*, last + 1
            Step.repeat(2, 0, 5, 5, 10)
            """,
            2, 5, 5, 12);
    }

    [Fact]
    public void Eval_VariadicLoopStep_WithPrefixMiddleSuffix_PreservesDeclarationOrderBindings()
    {
        AssertEvalLoopModes(
            """
            Step(first, *middle, last) = first, middle.count, last
            Step.repeat(1, 10, 20, 30, 40)
            """,
            10, 2, 40);
    }

    [Fact]
    public void Eval_VariadicLoopStep_ReportsMinimumStateArityWhenFixedParametersCannotBind()
    {
        // The minimum for Step(first, *rest, last) is the FIXED parameter
        // count (2), so a single state slot cannot bind first + last. The collecting
        // parameter itself may collect zero slots (see Eval_VariadicLoopStep_TwoStateSlots_*).
        var (generic, optimized) = AssertEvalFailsInBothLoopModes(
            """
            Step(first, *rest, last) = first*, rest*, last
            Step.repeat(1, 1)
            """);

        foreach (var error in new[] { generic, optimized })
        {
            var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
            Assert.Equal(2, arity.Expected);
            Assert.Equal(1, arity.Actual);

            var formatted = KatLangError.FromEvalError(error).Message;
            Assert.Contains("`repeat` variadic step expects at least 2 state values", formatted, StringComparison.Ordinal);
            Assert.Contains("for fixed parameter(s) 'first' and 'last'", formatted, StringComparison.Ordinal);
            Assert.Contains("current loop state has 1 state value", formatted, StringComparison.Ordinal);
            Assert.DoesNotContain("Callable `Step(first, *rest, last)`", formatted, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void Eval_VariadicLoopStep_TwoStateSlots_BindEmptyCollectedList()
    {
        // The empty loop-state segment follows the SAME rule as every other collecting
        // receiver: Step(first, *middle, last) with exactly two state slots
        // binds first/last from the ends and middle collects ZERO slots as the
        // exact empty list `[]` (count 0). Pins the parity boundary: 1 slot
        // fails (Eval_VariadicLoopStep_ReportsMinimumStateArity*), 2 bind an
        // empty segment, 3 a singleton, 4+ a multi-item segment. Mirrors the Lean
        // guard variadicLoopStepEmptyMiddleBindsEmptyList.
        AssertEvalLoopModes(
            """
            Step(first, *middle, last) = first, (middle == []), middle.count, last
            Step.repeat(1, 10, 20)
            """,
            10, 1, 0, 20);
    }

    [Fact]
    public void Eval_OptimizedLoop_MultiEmittingStateExpression_MatchesGenericPath()
    {
        // A state expression whose counted supply emits more than one value
        // (an index projection here) grows the generic state-slot vector; the
        // optimizer must observe the identical value shape (it finishes the
        // current iteration once, then hands its assembled state slots to the
        // generic evaluator when an expression does not emit exactly one value).
        AssertEvalLoopModes(
            """
            S = (1, 2), (3, 4)
            repeat({S:0, a + b}, 1, 0, 0)
            """,
            1, 2, 0);

        AssertEvalResultLoopModes(
            """
            S = (1, 2), (3, 4)
            repeat({S:0, a + b}, 1, 0, 0)
            """,
            ResultFromAtoms(1, 2, 0));

        // The first iteration stays on the scalar fast path; only the second
        // projection grows from one emitted item to two. This pins handoff
        // from the already-advanced state rather than from the initial state.
        AssertEvalResultLoopModes(
            """
            S = 1, (2, 3)
            repeat({a + 1, S:(a + b - b)}, 2, 0, 9)
            """,
            ResultFromAtoms(2, 2, 3));
    }

    [Fact]
    public void Eval_OptimizedLoop_MultiEmittingContinuation_MatchesGenericPath()
    {
        // A while continuation expression emitting more than one value changes
        // which generic slot is the continuation flag; the optimizer must
        // defer to generic semantics (state (1, 0) means the last item, 0,
        // stops the loop and the pre-iteration state is returned).
        AssertEvalLoopModes(
            """
            S = (1, 0), (2, 2)
            while({a + 1, S:0}, 9)
            """,
            9);
    }

    [Fact]
    public void Eval_OptimizedLoop_ZeroEmittingStateAndContinuation_MatchGenericPath()
    {
        // A spread empty value contributes no generic state slot. The
        // optimizer must complete that iteration once and hand off the
        // shrunken slot vector without replaying it.
        AssertEvalResultLoopModes(
            "repeat({if(a == 0, (), ())*, b}, 1, 0, 9)",
            ResultFromAtoms(9));

        // A spread-empty continuation leaves the preceding numeric output as
        // the generic continuation slot; zero stops and returns the old state.
        AssertEvalResultLoopModes(
            "while({a + 1, if(a == -1, (), ())*}, -1)",
            ResultFromAtoms(-1));

        // Non-spread `()` is a visible output slot, so it is an invalid
        // continuation value in both modes rather than disappearing.
        var (generic, optimized) = AssertEvalFailsInBothLoopModes("while({a + 1, ()}, 0)");
        Assert.IsType<EvalError.BadArity>(Innermost(generic));
        Assert.IsType<EvalError.BadArity>(Innermost(optimized));
        Assert.Equal(
            KatLangError.FromEvalError(generic).Message,
            KatLangError.FromEvalError(optimized).Message);
    }

    [Fact]
    public void Eval_OptimizedLoop_MultiEmittingStateExpression_ErrorMatchesGenericPath()
    {
        // Error identity parity: a spread state expression makes the next
        // state three slots against a two-parameter step; both modes must
        // report the same loop-state arity mismatch at the same program point.
        var (generic, optimized) = AssertEvalFailsInBothLoopModes(
            "repeat({(a + 1, a + 2)*, b}, 2, 0, 9)");

        var genericArity = Assert.IsType<EvalError.ArityMismatch>(Innermost(generic));
        var optimizedArity = Assert.IsType<EvalError.ArityMismatch>(Innermost(optimized));
        Assert.Equal(genericArity.Expected, optimizedArity.Expected);
        Assert.Equal(genericArity.Actual, optimizedArity.Actual);
        Assert.Equal(
            KatLangError.FromEvalError(generic).Message,
            KatLangError.FromEvalError(optimized).Message);

        // One scalar iteration succeeds before the second iteration grows the
        // state from two slots to three; the next bind then fails identically.
        var (laterGeneric, laterOptimized) = AssertEvalFailsInBothLoopModes(
            """
            S = 1, (2, 3)
            repeat({a + 1, S:(a + b - b)}, 3, 0, 9)
            """);
        var laterGenericArity = Assert.IsType<EvalError.ArityMismatch>(Innermost(laterGeneric));
        var laterOptimizedArity = Assert.IsType<EvalError.ArityMismatch>(Innermost(laterOptimized));
        Assert.Equal((2, 3), (laterGenericArity.Expected, laterGenericArity.Actual));
        Assert.Equal(
            KatLangError.FromEvalError(laterGeneric).Message,
            KatLangError.FromEvalError(laterOptimized).Message);
    }

    [Fact]
    public void Eval_OptimizedLoop_ListAndSequenceValuedState_MatchesGenericPath()
    {
        // Structural state slots (exact lists, growing via spread) are bound
        // and rebuilt identically in both loop modes.
        AssertEvalResultLoopModes(
            "repeat({[a*, 1]}, 3, [])",
            ListValue(ResultFromAtoms(1), ResultFromAtoms(1), ResultFromAtoms(1)));

        AssertEvalResultLoopModes(
            """
            Step(acc, *x) = acc + x.count, 0
            repeat(Step, 1, 5)
            """,
            SequenceValue(ResultFromAtoms(5), ResultFromAtoms(0)));
    }

    [Fact]
    public void Eval_PatternedAndFlatLoopSteps_ShareTheEmptySegmentRule()
    {
        // The flat variadic loop path and the patterned loop path both allow a
        // collecting parameter that collects zero state slots (the exact empty list `[]`) —
        // the same rule as every other collecting binding.
        AssertEvalResultLoopModes(
            """
            Step(a, *rest, a) = rest, 0
            repeat(Step, 1, 7, 7)
            """,
            SequenceValue(ListValue(), ResultFromAtoms(0)));
    }

    [Fact]
    public void Eval_SingleVariadicLoopStep_MayShrinkStateToZeroSlots()
    {
        // Deliberate consequence of the uniform empty-segment rule: a single-variadic
        // step has zero fixed parameters, so the state vector may shrink all
        // the way to zero slots, and the loop result is then the visible
        // empty sequence value `()`.
        AssertEvalResultLoopModes(
            """
            Step(*x) = x.skip(1)*
            repeat(Step, 3, 7, 8)
            """,
            SequenceValue());

        AssertEvalResultLoopModes(
            """
            Step(*x) = x.skip(1)*
            repeat(Step, 1, 7, 8)
            """,
            ResultFromAtoms(8));
    }

    [Fact]
    public void Eval_VariadicLoopStep_WhileUsesExpandedState()
    {
        AssertEvalResultLoopModes(
            """
            AppendWhile(*history) = (history*, history.atoms.last + 1), if(history.atoms.last + 1 < 6, 1, 0)
            AppendWhile.while(1, 2, 4)
            """,
            ResultFromAtoms(1, 2, 4, 5));
    }

    [Fact]
    public void Eval_LoopInitial_ManyExplicitArgsCreateManySlots()
    {
        AssertEvalLoopModes(
            """
            Step = a + 1, b + a
            Step.repeat(3, 0, 0)
            """,
            3, 3);
    }

    [Fact]
    public void Eval_LoopInitial_SequenceValuePropertyArgIsOneSlot()
    {
        AssertEvalLoopModes(
            """
            Pair = (1, 2)
            Step = pair:0 + pair:1
            Step.repeat(1, Pair)
            """,
            3);
    }

    [Fact]
    public void Eval_LoopInitial_SequenceValueArgDoesNotSatisfyTwoOrdinaryParams()
    {
        var (generic, optimized) = AssertEvalFailsInBothLoopModes(
            """
            Pair = (1, 2)
            Step = a + b
            Step.repeat(1, Pair)
            """);

        foreach (var error in new[] { generic, optimized })
        {
            var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
            Assert.Equal(2, arity.Expected);
            Assert.Equal(1, arity.Actual);
        }
    }

    [Fact]
    public void Eval_LoopInitial_ExplicitSelectionsSplitSequenceValueArg()
    {
        AssertEvalLoopModes(
            """
            Pair = (1, 2)
            Step = a + b
            Step.repeat(1, Pair:0, Pair:1)
            """,
            3);
    }

    [Fact]
    public void Eval_LoopInitial_SequenceValueHistorySlotCanBePreservedAcrossRepeat()
    {
        AssertEvalLoopModes(
            """
            History = (1, 2, 4)
            Step = (history, history.atoms.last + 1)
            Step.repeat(2, History)
            """,
            1, 2, 4, 5, 6);
    }

    [Fact]
    public void Eval_LoopInitial_SequenceValueStepOutputBecomesOneStateSlot()
        => AssertEvalResultLoopModes(
            """
            History = (1, 2, 4)
            Step = (history*, history.atoms.last + 1)
            Step.repeat(2, History)
            """,
            ResultFromAtoms(1, 2, 4, 5, 6));

    [Fact]
    public void Eval_LoopStep_SequenceSpreadSlotRequiresACommaBeforeTheNextItem()
    {
        // A loop-step sequence value keeps two slots only with the comma:
        // `(history*, FindNext(history*))` spreads the state and then supplies
        // the next candidate. Dropping the comma does NOT re-create the old
        // adjacency reading — `history* FindNext(...)` is the multiplication
        // `history * FindNext(...)` under the star rule, so the same step body
        // fails as a numeric type error instead of silently building one slot.
        const string definitions = """
            FindNext(*history) = {
                Tail = history:(history.atoms.count-1)
                IsCandidate(candidate) = not history.contains(candidate)
                FindStep = x + 1, not IsCandidate(x)
                FindStep.while(Tail+1):0
            }
            LIST = 1, 2, 4
            """;

        AssertEvalResultLoopModes(
            definitions + "\nTestStep = (history*, FindNext(history*))\nTestStep.repeat(1, LIST)",
            ResultFromAtoms(1, 2, 4, 5));

        var adjacent = EvalFull(
            definitions + "\nTestStep = (history* FindNext(history*))\nTestStep.repeat(1, LIST)");
        Assert.True(adjacent.IsError, "adjacency after a spread must multiply, not supply a second slot");
        Assert.Contains("*", adjacent.Error!.ToString());
    }

    [Fact]
    public void Eval_LoopStep_SequenceValueSequenceSpreadCarriesOneSequenceStateSlot()
        => AssertEvalResultLoopModes(
            """
            FindNext(*history) = {
                Tail = history:(history.atoms.count-1)
                IsCandidate(candidate) = not history.contains(candidate)
                FindStep = x + 1, not IsCandidate(x)
                FindStep.while(Tail+1):0
            }
            TestStep = (history*, FindNext(history*))
            LIST = 1, 2, 4
            TestStep.repeat(2, LIST)
            """,
            ResultFromAtoms(1, 2, 4, 5, 6));

    [Fact]
    public void Eval_LoopStep_ExplicitVariadicStillAcceptsExpandedState()
    {
        AssertEvalResultLoopModes(
            """
            FindNext(*history) = {
                Tail = history:(history.atoms.count-1)
                IsCandidate(candidate) = not history.contains(candidate)
                FindStep = x + 1, not IsCandidate(x)
                FindStep.while(Tail+1):0
            }
            TestStep(*history) = history*, FindNext(history*)
            TestStep.repeat(2, 1, 2, 4)
            """,
            ResultFromAtoms(1, 2, 4, 5, 6));
    }

    [Fact]
    public void Eval_LoopStep_SequenceValueCommaHistorySlotUsesExplicitSpreadAcrossRepeat()
    {
        const string source = """
            Step((*history), previous) = (history*, previous + 1), previous + 1
            Step.repeat(2, (1, 2), 2):0
            """;

        AssertEvalResultLoopModes(source, ResultFromAtoms(1, 2, 3, 4));

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        AssertSequenceValueAtoms(result.Value, 1, 2, 3, 4);
    }

    [Fact]
    public void Eval_LoopInitial_MultiOutputPropertyArgIsOneSlot()
    {
        AssertEvalLoopModes(
            """
            Pair = 1, 2
            Step = pair:0 + pair:1
            Step.repeat(1, Pair)
            """,
            3);
    }

    [Fact]
    public void Eval_LoopInitial_ExplicitSelectionsSplitMultiOutputProperty()
    {
        AssertEvalLoopModes(
            """
            Pair = 1, 2
            Step = a + b
            Step.repeat(1, Pair:0, Pair:1)
            """,
            3);
    }
}
