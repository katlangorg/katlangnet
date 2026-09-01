using System.Numerics;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// Structural regressions for the M16 loop-strategy work-timing contract, using the
/// passive run-scoped <see cref="EvaluationObservations"/> counters as the oracle
/// (never CLR allocation totals, so the pins are deterministic under JIT/runtime
/// noise):
///
/// <list type="bullet">
///   <item><b>Generic strategy</b>: the loop-invariant step binding (callable
///   signature, binding plan/shape, shadowed counted environment, spread-boundary
///   policy) is prepared exactly ONCE per loop invocation that runs at least one
///   iteration — <see cref="EvaluationObservations.GenericLoopStepBindingPreparationCount"/>
///   — never once per iteration, never zero, never process-cached across invocations,
///   and never at all for a zero-iteration loop. The async generic twins share the
///   same non-evaluating preparation helper and must observe identical counts.</item>
///   <item><b>Optimized strategy</b>: the generic handover output-slot representation
///   is materialized ONLY inside an actual handover branch —
///   <see cref="EvaluationObservations.OptimizedLoopHandoverMaterializationCount"/> —
///   so a loop that never hands over materializes zero times regardless of iteration
///   count, and each real handover (either branch: an output that did not emit exactly
///   one value, or a committed next state whose arity grew) materializes exactly once
///   at the handover point. Handover keeps outcome and cumulative materialization
///   charging identical to the forced-generic run.</item>
/// </list>
/// </summary>
public class LoopStrategyPreparationTests
{
    private sealed class RecordingZeroArgPropertyResultCache : IZeroArgPropertyResultCache
    {
        private readonly RunScopedZeroArgPropertyResultCache inner = new();

        public List<ZeroArgPropertyExecution> Requests { get; } = [];

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            Requests.Add(execution);
            return inner.GetOrEvaluate(execution, evaluate);
        }
    }

    private static Expr Program(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private static (EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget) RunGeneric(
        string source,
        EvaluationObservations observations)
        => Evaluator.RunCountedObserved(
            Program(source),
            enableOptimizations: false,
            observations: observations);

    private static (EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget, LoopOptimizationDiagnostics Diagnostics) RunOptimized(
        string source,
        EvaluationObservations observations)
    {
        var diagnostics = new LoopOptimizationDiagnostics();
        var (result, budget) = Evaluator.RunCountedObserved(
            Program(source),
            loopDiagnostics: diagnostics,
            observations: observations);
        return (result, budget, diagnostics);
    }

    // ── Generic strategy: binding preparation is once per loop invocation ──────

    [Theory]
    [InlineData(1, 1)]
    [InlineData(2, 2)]
    [InlineData(1000, 1000)]
    public void GenericRepeat_PreparesStepBindingOncePerLoopInvocation(int count, decimal expected)
    {
        var observations = new EvaluationObservations();
        var (result, _) = RunGeneric($"Step = k + 1\nStep.repeat({count}, 0)", observations);

        Assert.False(result.IsError, $"generic repeat failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal([expected], result.Value.Value.ToAtoms());
        Assert.Equal(1, observations.GenericLoopStepBindingPreparationCount);
        Assert.Equal(0, observations.OptimizedLoopHandoverMaterializationCount);
    }

    [Fact]
    public void GenericWhile_PreparesStepBindingOncePerLoopInvocation()
    {
        var observations = new EvaluationObservations();
        var (result, _) = RunGeneric("Step = k + 1, k < 100\nStep.while(0)", observations);

        Assert.False(result.IsError, $"generic while failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal([100m], result.Value.Value.ToAtoms());
        Assert.Equal(1, observations.GenericLoopStepBindingPreparationCount);
    }

    [Fact]
    public void TwoSeparateGenericLoopInvocations_PrepareTwice()
    {
        // Preparation is per-loop-invocation state: a second invocation of the SAME
        // step algorithm prepares again (no static or cross-loop cache may exist).
        var observations = new EvaluationObservations();
        var (result, _) = RunGeneric(
            "Step = k + 1\nA = Step.repeat(10, 0)\nB = Step.repeat(10, 5)\nA + B",
            observations);

        Assert.False(result.IsError, $"two-loop program failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal([25m], result.Value.Value.ToAtoms());
        Assert.Equal(2, observations.GenericLoopStepBindingPreparationCount);
    }

    [Fact]
    public void SameStepInstanceAcrossTwoLoopInvocations_PreparesTwice()
    {
        // A higher-order step bound to a parameter is the SAME Algorithm instance
        // for both loop invocations (property resolution rewires a fresh instance,
        // parameter reads do not) — so this shape specifically kills any
        // reference-keyed cross-invocation preparation cache.
        var observations = new EvaluationObservations();
        var (result, _) = RunGeneric(
            "Use(f) = f.repeat(2, 0) + f.repeat(3, 10)\nStep = k + 1\nUse(Step)",
            observations);

        Assert.False(result.IsError, $"higher-order two-loop program failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal([15m], result.Value.Value.ToAtoms());
        Assert.Equal(2, observations.GenericLoopStepBindingPreparationCount);
    }

    [Fact]
    public void NestedGenericLoops_PrepareOncePerInvocationEach()
    {
        // The outer loop prepares once; each outer iteration re-invokes the inner
        // loop, and each inner INVOCATION prepares once on its own stack frame.
        var observations = new EvaluationObservations();
        var (result, _) = RunGeneric(
            "Inner = y + 1\nOuter = Inner.repeat(2, x)\nOuter.repeat(3, 0)",
            observations);

        Assert.False(result.IsError, $"nested-loop program failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal([6m], result.Value.Value.ToAtoms());
        Assert.Equal(4, observations.GenericLoopStepBindingPreparationCount);
    }

    [Fact]
    public void ZeroIterationRepeat_PreparesNothing()
    {
        // A zero-iteration repeat never binds its step, so it must not gain step
        // preparation either — in generic mode and in default (optimized) mode alike.
        var genericObservations = new EvaluationObservations();
        var (genericResult, _) = RunGeneric("Step = k + 1\nStep.repeat(0, 7)", genericObservations);

        Assert.False(genericResult.IsError);
        Assert.Equal([7m], genericResult.Value.Value.ToAtoms());
        Assert.Equal(0, genericObservations.GenericLoopStepBindingPreparationCount);

        var defaultObservations = new EvaluationObservations();
        var (defaultResult, _, _) = RunOptimized("Step = k + 1\nStep.repeat(0, 7)", defaultObservations);

        Assert.False(defaultResult.IsError);
        Assert.Equal([7m], defaultResult.Value.Value.ToAtoms());
        Assert.Equal(0, defaultObservations.GenericLoopStepBindingPreparationCount);
        Assert.Equal(0, defaultObservations.OptimizedLoopHandoverMaterializationCount);
    }

    [Fact]
    public void GenericLoop_FirstIterationBindingError_StillPreparesExactlyOnce()
    {
        // Invalid loop-state arity surfaces on the first generic iteration, inside
        // per-iteration binding — preparation happened once and the structured error
        // is unchanged (LoopStateArityDiagnosticTests pins the cross-mode message).
        var observations = new EvaluationObservations();
        var (result, _) = RunGeneric("Step(a, b) = a + b, 1\nStep.while(5)", observations);

        Assert.True(result.IsError, "arity-mismatched while step must fail");
        Assert.Equal(1, observations.GenericLoopStepBindingPreparationCount);
    }

    [Fact]
    public void GenericRepeat_PreparationAddsNoStepCharge()
    {
        const string source = "Step = k + 1\nStep.repeat(3, 0)";
        var observations = new EvaluationObservations();
        var (unbounded, unboundedBudget) = RunGeneric(source, observations);

        Assert.False(unbounded.IsError);
        Assert.Equal(3L, unboundedBudget.ConsumedSteps);

        var exactObservations = new EvaluationObservations();
        var (exact, exactBudget) = Evaluator.RunCountedObserved(
            Program(source),
            limits: new EvaluationLimits { MaxSteps = 3 },
            enableOptimizations: false,
            observations: exactObservations);
        Assert.False(exact.IsError);
        Assert.Equal(3L, exactBudget.ConsumedSteps);
        Assert.Equal(1, exactObservations.GenericLoopStepBindingPreparationCount);

        var shortObservations = new EvaluationObservations();
        var (shortRun, shortBudget) = Evaluator.RunCountedObserved(
            Program(source),
            limits: new EvaluationLimits { MaxSteps = 2 },
            enableOptimizations: false,
            observations: shortObservations);
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(shortRun.Error);
        Assert.Equal(2L, shortBudget.ConsumedSteps);
        Assert.Equal(1, shortObservations.GenericLoopStepBindingPreparationCount);
    }

    [Fact]
    public void GenericRepeat_StateDependentConditionalDispatch_RemainsPerIteration()
    {
        // The prepared object describes only Step's callable binding. The nested
        // conditional family must still select and bind a clause from the CURRENT
        // state on every evaluation: iteration 1 takes the literal clause and
        // iteration 2 takes the binder clause.
        var observations = new EvaluationObservations();
        var (result, _) = RunGeneric(
            "Advance(0) = 1\nAdvance(x) = x + 1\nStep = Advance(k)\nStep.repeat(2, 0)",
            observations);

        Assert.False(result.IsError, $"conditional loop failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal([2m], result.Value.Value.ToAtoms());
        Assert.Equal(1, observations.GenericLoopStepBindingPreparationCount);
    }

    [Fact]
    public void GenericRepeat_FreshCountedEnvironmentIdentitySurvivesPreparedBaseReuse()
    {
        // The shadowed BASE environment is invariant, but the combined environment
        // remains a fresh list per bind. Besides being part of the zero-arg cache key,
        // that reference identity is an explicit environment-lifetime contract.
        var cache = new RecordingZeroArgPropertyResultCache();
        var observations = new EvaluationObservations();
        var (result, _) = Evaluator.RunCountedObserved(
            Program("Step(x) = { Val = x + 1\nVal }\nStep.repeat(3, 0)"),
            enableOptimizations: false,
            zeroArgPropertyResultCache: cache,
            observations: observations);

        Assert.False(result.IsError, $"counted-environment loop failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal([3m], result.Value.Value.ToAtoms());
        var requests = cache.Requests.Where(static request => request.Binding.Name == "Val").ToList();
        Assert.Equal(3, requests.Count);
        Assert.Equal(3, requests.Select(static request => request.CountedParamEnvironmentIdentity).Distinct().Count());
        Assert.Equal(1, observations.GenericLoopStepBindingPreparationCount);
    }

    [Fact]
    public void HostOwnedCallableMetadata_IsSnapshottedBeforeCallbackCanMutateItsSourceLists()
    {
        // Algorithm is a public host-AST boundary. Retaining the constructor lists lets
        // this callback change Step from flat-one-parameter to patterned-two-capture
        // between iterations. The loop-invocation snapshot prevents M16 from mixing the
        // old prepared classification with the newly mutated Params list; the public AST
        // keeps its established caller-owned collection behavior outside that invocation.
        var parameters = new List<ParameterDeclaration> { new("state") };
        var patterns = new List<ParameterPattern> { new CaptureParameterPattern("state") };
        var calls = 0;
        var operation = HostOperation.Create("ChangeShape", (_, _) =>
        {
            calls++;
            if (calls == 1)
            {
                parameters.Clear();
                parameters.Add(new ParameterDeclaration("left"));
                parameters.Add(new ParameterDeclaration("right"));
                patterns.Clear();
                patterns.Add(new SequenceValueParameterPattern(
                    [new CaptureParameterPattern("left"), new CaptureParameterPattern("right")]));
                return new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2)]);
            }

            return new Result.Atom(9);
        });
        var step = new Algorithm.User(
            Parent: null,
            Parameters: parameters,
            Opens: [],
            Properties: [],
            Output: [new Expr.NativeCall(operation.NativeName, [])])
        {
            ParameterPatterns = patterns,
        };
        var expression = new Expr.Call(
            new Expr.Resolve("repeat"),
            [new Expr.AlgorithmExpr(step), new Expr.Num(2), new Expr.Num(0)]);
        var observations = new EvaluationObservations();

        var (result, _) = Evaluator.RunCountedObserved(
            expression,
            enableOptimizations: false,
            observations: observations,
            hostOperations: HostOperations.Create(operation));

        Assert.False(result.IsError, $"host-mutation loop failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal([9m], result.Value.Value.ToAtoms());
        Assert.Equal(2, calls);
        Assert.Equal(["left", "right"], step.Params);
        Assert.IsType<SequenceValueParameterPattern>(Assert.Single(step.ParameterPatterns));
        Assert.Equal(1, observations.GenericLoopStepBindingPreparationCount);
    }

    [Fact]
    public void NestedPatternMembership_IsSnapshottedForOneLoopInvocation()
    {
        var nestedItems = new List<ParameterPattern>
        {
            new CaptureParameterPattern("state"),
        };
        var pattern = new SequenceValueParameterPattern(nestedItems);
        var calls = 0;
        var operation = HostOperation.Create("ChangeNestedShape", (_, _) =>
        {
            calls++;
            if (calls == 1)
            {
                nestedItems.Clear();
                nestedItems.Add(new CaptureParameterPattern("left"));
                nestedItems.Add(new CaptureParameterPattern("right"));
                return new Result.SequenceValue([new Result.Atom(1)]);
            }

            return new Result.Atom(9);
        });
        var step = new Algorithm.User(
            Parent: null,
            Parameters: [new ParameterDeclaration("state")],
            Opens: [],
            Properties: [],
            Output: [new Expr.NativeCall(operation.NativeName, [])])
        {
            ParameterPatterns = [pattern],
        };
        var expression = new Expr.Call(
            new Expr.Resolve("repeat"),
            [new Expr.AlgorithmExpr(step), new Expr.Num(2), new Expr.Capture([new Expr.Num(0)])]);
        var observations = new EvaluationObservations();

        var (result, _) = Evaluator.RunCountedObserved(
            expression,
            enableOptimizations: false,
            observations: observations,
            hostOperations: HostOperations.Create(operation));

        Assert.False(result.IsError, $"nested host-mutation loop failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal([9m], result.Value.Value.ToAtoms());
        Assert.Equal(2, calls);
        Assert.Equal(2, pattern.Items.Count);
        Assert.Equal(1, observations.GenericLoopStepBindingPreparationCount);
    }

    // ── Async generic twins: identical preparation policy, shared helper ───────

    [Fact]
    public async Task AsyncTwinGenericRepeat_PreparesStepBindingOncePerLoopInvocation()
    {
        var observations = new EvaluationObservations();
        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var (result, _) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(
                Program("Step = k + 1\nStep.repeat(10, 0)"),
                zeroArgPropertyResultCache: cache,
                observations: observations));

        Assert.False(result.IsError, $"async twin repeat failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal([10m], result.Value.Value.ToAtoms());
        Assert.Equal(1, observations.GenericLoopStepBindingPreparationCount);
        Assert.Equal(0, cache.SyncAccesses);
    }

    [Fact]
    public async Task AsyncTwinGenericWhile_PreparesStepBindingOncePerLoopInvocation()
    {
        var observations = new EvaluationObservations();
        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var (result, _) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(
                Program("Step = k + 1, k < 100\nStep.while(0)"),
                zeroArgPropertyResultCache: cache,
                observations: observations));

        Assert.False(result.IsError, $"async twin while failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal([100m], result.Value.Value.ToAtoms());
        Assert.Equal(1, observations.GenericLoopStepBindingPreparationCount);
        Assert.Equal(0, cache.SyncAccesses);
    }

    [Fact]
    public async Task AsyncTwinZeroIterationRepeat_PreparesNothing()
    {
        var observations = new EvaluationObservations();
        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var (result, _) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(
                Program("Step = k + 1\nStep.repeat(0, 7)"),
                zeroArgPropertyResultCache: cache,
                observations: observations));

        Assert.False(result.IsError);
        Assert.Equal([7m], result.Value.Value.ToAtoms());
        Assert.Equal(0, observations.GenericLoopStepBindingPreparationCount);
        Assert.Equal(0, cache.SyncAccesses);
    }

    [Fact]
    public async Task AsyncTwinNegativeRepeatCount_IsRejectedBeforePreparation()
    {
        var observations = new EvaluationObservations();
        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var (result, _) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(
                Program("Step = k + 1\nStep.repeat(-1, 7)"),
                zeroArgPropertyResultCache: cache,
                observations: observations));

        Assert.True(result.IsError);
        Assert.Equal(0, observations.GenericLoopStepBindingPreparationCount);
        Assert.Equal(0, cache.SyncAccesses);
    }

    // ── Optimized strategy: no handover, no generic materialization ────────────

    [Fact]
    public void OptimizedRepeat_NoHandover_NeverMaterializesGenericSlots()
    {
        var observations = new EvaluationObservations();
        var (result, _, diagnostics) = RunOptimized("Step = k + 1\nStep.repeat(1000, 0)", observations);

        Assert.False(result.IsError, $"optimized repeat failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal([1000m], result.Value.Value.ToAtoms());
        Assert.Equal(0, observations.OptimizedLoopHandoverMaterializationCount);
        // The optimized strategy never touches generic step preparation either.
        Assert.Equal(0, observations.GenericLoopStepBindingPreparationCount);
        Assert.Equal(1, diagnostics.OptimizedLoopHits);
        Assert.Equal(1000, diagnostics.LoopIterations);
        Assert.Equal(0, diagnostics.OptimizedLoopFallbacks);
    }

    [Fact]
    public void OptimizedWhile_NoHandover_NeverMaterializesGenericSlots()
    {
        var observations = new EvaluationObservations();
        var (result, _, diagnostics) = RunOptimized("Step = k + 1, k < 100\nStep.while(0)", observations);

        Assert.False(result.IsError, $"optimized while failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal([100m], result.Value.Value.ToAtoms());
        Assert.Equal(0, observations.OptimizedLoopHandoverMaterializationCount);
        Assert.Equal(0, observations.GenericLoopStepBindingPreparationCount);
        Assert.Equal(1, diagnostics.OptimizedLoopHits);
        Assert.Equal(101, diagnostics.LoopIterations);
        Assert.Equal(0, diagnostics.OptimizedLoopFallbacks);
    }

    // ── Optimized strategy: handover branch 1 (output emission shape) ──────────

    [Fact]
    public void OptimizedRepeat_EmissionShapeHandover_MaterializesExactlyOnceThenContinuesGenerically()
    {
        // At v == 3 the state output evaluates to the empty sequence value (zero
        // emission), which the optimized frame cannot pack: the iteration finishes,
        // hands its assembled slots over ONCE, and the generic loop runs the
        // remaining iterations (preparing its own binding once).
        const string source = "Empty = ()\nStep = if(v == 3, Empty, v + 1)\nStep.repeat(10, 0)";

        var observations = new EvaluationObservations();
        var (result, budget, diagnostics) = RunOptimized(source, observations);

        var genericObservations = new EvaluationObservations();
        var (genericResult, genericBudget) = RunGeneric(source, genericObservations);

        Assert.False(result.IsError, $"handover repeat failed: {(result.IsError ? result.Error : null)}");
        Assert.False(genericResult.IsError);
        Assert.Equal(genericResult.Value.Value.ToAtoms(), result.Value.Value.ToAtoms());
        Assert.Equal([2m], result.Value.Value.ToAtoms());
        Assert.Equal(genericResult.Value.EmittedCount, result.Value.EmittedCount);

        Assert.Equal(1, observations.OptimizedLoopHandoverMaterializationCount);
        Assert.Equal(1, observations.GenericLoopStepBindingPreparationCount);
        Assert.Equal(4, diagnostics.LoopIterations);
        Assert.Equal(1, diagnostics.FallbackReasons["loop expression did not emit exactly one state value"]);

        // Handover leaves cumulative materialization charging identical to the
        // forced-generic strategy (only final persistent state is charged).
        Assert.Equal(genericBudget.MaterializedItems, budget.MaterializedItems);
    }

    [Fact]
    public void OptimizedWhile_StateEmissionHandover_ReturnsCurrentStateWhenContinuationStops()
    {
        // The handover iteration's continuation is 0, so the handover branch itself
        // resolves the loop from the current state — still exactly one
        // materialization, and no generic continuation is ever entered.
        const string source = "Empty = ()\nStep = if(k == 3, Empty, k + 1), k < 3\nStep.while(0)";

        var observations = new EvaluationObservations();
        var (result, budget, diagnostics) = RunOptimized(source, observations);

        var genericObservations = new EvaluationObservations();
        var (genericResult, genericBudget) = RunGeneric(source, genericObservations);

        Assert.False(result.IsError, $"handover while failed: {(result.IsError ? result.Error : null)}");
        Assert.False(genericResult.IsError);
        Assert.Equal(genericResult.Value.Value.ToAtoms(), result.Value.Value.ToAtoms());
        Assert.Equal([3m], result.Value.Value.ToAtoms());

        Assert.Equal(1, observations.OptimizedLoopHandoverMaterializationCount);
        Assert.Equal(0, observations.GenericLoopStepBindingPreparationCount);
        Assert.Equal(4, diagnostics.LoopIterations);
        Assert.Equal(1, diagnostics.FallbackReasons["loop expression did not emit exactly one state value"]);
        Assert.Equal(genericBudget.MaterializedItems, budget.MaterializedItems);
    }

    [Fact]
    public void OptimizedWhile_ContinuationEmissionHandover_MatchesGenericError()
    {
        // The CONTINUATION emits zero values at k == 3; the handover branch assembles
        // the same slots the generic evaluator would have produced, and the shared
        // continuation split reports the identical structured error.
        const string source = "Empty = ()\nStep = k + 1, if(k < 3, 1, Empty)\nStep.while(0)";

        var observations = new EvaluationObservations();
        var (result, _, diagnostics) = RunOptimized(source, observations);

        var genericObservations = new EvaluationObservations();
        var (genericResult, _) = RunGeneric(source, genericObservations);

        Assert.True(result.IsError, "continuation-emission handover must surface the generic split error");
        Assert.True(genericResult.IsError);
        Assert.Equal(genericResult.Error.ToString(), result.Error.ToString());

        Assert.Equal(1, observations.OptimizedLoopHandoverMaterializationCount);
        Assert.Equal(1, diagnostics.FallbackReasons["loop continuation did not emit exactly one value"]);
    }

    [Fact]
    public void OptimizedRepeat_MultiSlotEmissionHandover_PreservesSlotOrder()
    {
        // Two state slots; the SECOND output stops emitting exactly one value while
        // the first stays scalar. The materialized handover slots must keep the
        // written output order (state slot 0 first), or the generic continuation
        // binds the wrong values.
        const string source = "Empty = ()\nStepTwo = a + 1, if(a == 1, Empty, b * 2)\nStepTwo.repeat(3, 0, 5)";

        var observations = new EvaluationObservations();
        var (result, budget, diagnostics) = RunOptimized(source, observations);

        var genericObservations = new EvaluationObservations();
        var (genericResult, genericBudget) = RunGeneric(source, genericObservations);

        Assert.False(result.IsError, $"multi-slot handover failed: {(result.IsError ? result.Error : null)}");
        Assert.False(genericResult.IsError);
        Assert.Equal(genericResult.Value.Value.ToAtoms(), result.Value.Value.ToAtoms());
        Assert.Equal([3m, 2m], result.Value.Value.ToAtoms());

        Assert.Equal(1, observations.OptimizedLoopHandoverMaterializationCount);
        Assert.Equal(1, observations.GenericLoopStepBindingPreparationCount);
        Assert.Equal(1, diagnostics.FallbackReasons["loop expression did not emit exactly one state value"]);
        // Two retained state slots make an accidental handover-only collection
        // reservation visible (singleton capture would charge nothing).
        Assert.Equal(genericBudget.MaterializedItems, budget.MaterializedItems);
    }

    [Fact]
    public void OptimizedRepeat_OutputError_ReturnsImmediatelyWithoutHandoverMaterialization()
    {
        const string source = "Step(a, b) = a + 1, 1 / 0\nStep.repeat(3, 0, 5)";
        var observations = new EvaluationObservations();
        var (result, _, diagnostics) = RunOptimized(source, observations);
        var genericObservations = new EvaluationObservations();
        var (generic, _) = RunGeneric(source, genericObservations);

        Assert.True(result.IsError);
        Assert.True(generic.IsError);
        Assert.Equal(generic.Error.ToString(), result.Error.ToString());
        Assert.Equal(0, observations.OptimizedLoopHandoverMaterializationCount);
        Assert.Equal(1, diagnostics.LoopIterations);
    }

    [Fact]
    public void OptimizedRepeat_HandoverOnFinalIteration_MaterializesOnceWithoutGenericPreparation()
    {
        // The handover branch fires on the LAST iteration: zero remaining
        // iterations, so the branch completes the loop directly from the
        // materialized slots and no generic loop invocation ever begins.
        const string source = "Empty = ()\nStep = if(v == 3, Empty, v + 1)\nStep.repeat(4, 0)";

        var observations = new EvaluationObservations();
        var (result, budget, _) = RunOptimized(source, observations);

        var genericObservations = new EvaluationObservations();
        var (genericResult, genericBudget) = RunGeneric(source, genericObservations);

        Assert.False(result.IsError, $"final-iteration handover failed: {(result.IsError ? result.Error : null)}");
        Assert.False(genericResult.IsError);
        Assert.Equal(genericResult.Value.Value.ToAtoms(), result.Value.Value.ToAtoms());
        Assert.Equal(genericResult.Value.EmittedCount, result.Value.EmittedCount);

        Assert.Equal(1, observations.OptimizedLoopHandoverMaterializationCount);
        Assert.Equal(0, observations.GenericLoopStepBindingPreparationCount);
        Assert.Equal(genericBudget.MaterializedItems, budget.MaterializedItems);
    }

    // ── Optimized strategy: handover branch 2 (next-state arity growth) ────────

    [Fact]
    public void OptimizedRepeat_StateArityGrowthHandover_MaterializesExactlyOnce()
    {
        // Every output emits exactly one value, but the committed single next-state
        // value packs two top-level items — the scratch commit refuses and the loop
        // hands the state-only slots over once.
        const string source = "Pair = 1, 2\nStep = if(v == 0, Pair, count(v) + 10)\nStep.repeat(3, 0)";

        var observations = new EvaluationObservations();
        var (result, budget, diagnostics) = RunOptimized(source, observations);

        var genericObservations = new EvaluationObservations();
        var (genericResult, genericBudget) = RunGeneric(source, genericObservations);

        Assert.False(result.IsError, $"arity-growth repeat handover failed: {(result.IsError ? result.Error : null)}");
        Assert.False(genericResult.IsError);
        Assert.Equal(genericResult.Value.Value.ToAtoms(), result.Value.Value.ToAtoms());
        Assert.Equal([11m], result.Value.Value.ToAtoms());

        Assert.Equal(1, observations.OptimizedLoopHandoverMaterializationCount);
        Assert.Equal(1, observations.GenericLoopStepBindingPreparationCount);
        Assert.Equal(1, diagnostics.LoopIterations);
        Assert.Equal(1, diagnostics.FallbackReasons["loop next-state arity changed"]);
        Assert.Equal(genericBudget.MaterializedItems, budget.MaterializedItems);
    }

    [Fact]
    public void OptimizedWhile_StateArityGrowthHandover_MaterializesExactlyOnce()
    {
        const string source = "Pair = 1, 2\nStep = if(k == 0, Pair, count(k) + 10), k == 0\nStep.while(0)";

        var observations = new EvaluationObservations();
        var (result, budget, diagnostics) = RunOptimized(source, observations);

        var genericObservations = new EvaluationObservations();
        var (genericResult, genericBudget) = RunGeneric(source, genericObservations);

        Assert.False(result.IsError, $"arity-growth while handover failed: {(result.IsError ? result.Error : null)}");
        Assert.False(genericResult.IsError);
        Assert.Equal(genericResult.Value.Value.ToAtoms(), result.Value.Value.ToAtoms());
        Assert.Equal([1m, 2m], result.Value.Value.ToAtoms());

        Assert.Equal(1, observations.OptimizedLoopHandoverMaterializationCount);
        Assert.Equal(1, observations.GenericLoopStepBindingPreparationCount);
        Assert.Equal(1, diagnostics.FallbackReasons["loop next-state arity changed"]);
        Assert.Equal(genericBudget.MaterializedItems, budget.MaterializedItems);
    }

    [Fact]
    public void OptimizedRepeat_H1FinalHandover_PreservesExistingSharedSequenceReference()
    {
        var leaf = new Result.Atom(7);
        var sharedChild = new Result.SequenceValue([leaf, leaf]);
        var sharedDag = new Result.SequenceValue([sharedChild, sharedChild]);
        var operation = HostOperation.Create("SharedState", (_, _) => sharedDag);
        var step = new Algorithm.User(
            Parent: null,
            Parameters: [new ParameterDeclaration("left"), new ParameterDeclaration("right")],
            Opens: [],
            Properties: [],
            Output:
            [
                new Expr.NativeCall(operation.NativeName, []),
                new Expr.SequenceSpread(new Expr.EmptySequence(0)),
            ]);
        var expression = new Expr.Call(
            new Expr.Resolve("repeat"),
            [new Expr.AlgorithmExpr(step), new Expr.Num(1), new Expr.Num(0), new Expr.Num(0)]);
        var observations = new EvaluationObservations();
        var diagnostics = new LoopOptimizationDiagnostics();

        var (result, _) = Evaluator.RunCountedObserved(
            expression,
            loopDiagnostics: diagnostics,
            observations: observations,
            hostOperations: HostOperations.Create(operation));

        Assert.False(result.IsError, $"H1 sharing handover failed: {(result.IsError ? result.Error : null)}");
        Assert.Same(sharedDag, result.Value.Value);
        var outerItems = Assert.IsType<Result.SequenceValue>(result.Value.Value).Items;
        Assert.Same(sharedChild, outerItems[0]);
        Assert.Same(outerItems[0], outerItems[1]);
        Assert.Equal(1, observations.OptimizedLoopHandoverMaterializationCount);
        Assert.Equal(1, diagnostics.GetSnapshot().OptimizedLoopHits);
    }

    [Fact]
    public void OptimizedRepeat_H2Handover_PreservesReferenceAndDoesNotReevaluateOutput()
    {
        var shared = new Result.SequenceValue([new Result.Str("left"), new Result.ListValue([])]);
        Result? secondInput = null;
        var calls = 0;
        var operation = HostOperation.Create(
            "CarryState",
            (args, _) =>
            {
                calls++;
                if (calls == 1)
                    return shared;

                secondInput = args[0];
                return new Result.Atom(9);
            },
            "state");
        var step = new Algorithm.User(
            Parent: null,
            Parameters: [new ParameterDeclaration("state")],
            Opens: [],
            Properties: [],
            Output: [new Expr.NativeCall(operation.NativeName, ["state"])]);
        var expression = new Expr.Call(
            new Expr.Resolve("repeat"),
            [new Expr.AlgorithmExpr(step), new Expr.Num(2), new Expr.Num(0)]);
        var observations = new EvaluationObservations();
        var diagnostics = new LoopOptimizationDiagnostics();

        var (result, _) = Evaluator.RunCountedObserved(
            expression,
            loopDiagnostics: diagnostics,
            observations: observations,
            hostOperations: HostOperations.Create(operation));

        Assert.False(result.IsError, $"H2 sharing handover failed: {(result.IsError ? result.Error : null)}");
        Assert.Equal([9m], result.Value.Value.ToAtoms());
        Assert.Equal(2, calls);
        Assert.Same(shared, secondInput);
        Assert.Equal(1, observations.OptimizedLoopHandoverMaterializationCount);
        Assert.Equal(1, observations.GenericLoopStepBindingPreparationCount);
        Assert.Equal(1, diagnostics.FallbackReasons["loop next-state arity changed"]);
    }

    [Theory]
    [InlineData("-0")]
    [InlineData("1.50")]
    [InlineData("9e6144 * 10")]
    [InlineData("Math.Sqrt(-1)")]
    public void RepeatedPlannedNumericState_PreservesDecimal128RepresentationParity(string initial)
    {
        var source = $"Step(x) = x + 0.00\nStep.repeat(5, {initial})";
        var genericObservations = new EvaluationObservations();
        var (generic, _) = RunGeneric(source, genericObservations);
        var optimizedObservations = new EvaluationObservations();
        var (optimized, _, diagnostics) = RunOptimized(source, optimizedObservations);

        Assert.False(generic.IsError, $"generic numeric loop failed: {(generic.IsError ? generic.Error : null)}");
        Assert.False(optimized.IsError, $"optimized numeric loop failed: {(optimized.IsError ? optimized.Error : null)}");
        var genericNumber = Assert.IsType<Result.Atom>(generic.Value.Value).Value;
        var optimizedNumber = Assert.IsType<Result.Atom>(optimized.Value.Value).Value;
        Assert.Equal(genericNumber, optimizedNumber);
        Assert.Equal(Decimal128.IsNegative(genericNumber), Decimal128.IsNegative(optimizedNumber));
        Assert.Equal(Decimal128.IsNaN(genericNumber), Decimal128.IsNaN(optimizedNumber));
        Assert.Equal(Decimal128.IsInfinity(genericNumber), Decimal128.IsInfinity(optimizedNumber));
        Assert.Equal(Decimal128.GetQuantum(genericNumber), Decimal128.GetQuantum(optimizedNumber));
        Assert.Equal(1, diagnostics.OptimizedLoopHits);
        Assert.Equal(0, optimizedObservations.OptimizedLoopHandoverMaterializationCount);
    }
}
