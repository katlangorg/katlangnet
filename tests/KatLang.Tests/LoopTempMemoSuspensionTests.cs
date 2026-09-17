using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// A planned temp CALL (<c>LoopExprPlan.TempCall</c>) suspends the loop frame's
/// per-iteration temp memo for the call's duration and reinstates it afterwards
/// (<c>LoopRunFrame.SuspendTempMemo</c>): the suspension is now an owned disposable
/// scope (<c>LoopRunFrame.TempMemoSuspension</c>) instead of a suspend/restore pair the
/// caller had to balance by hand. These tests pin the observable memo contract that a
/// misplaced, swapped, or forgotten restore would break. The planned strategy exposes
/// how often a temp's body ran through its planned-operation count (a temp body is one
/// planned multiplication here, so every extra memo miss is one extra operation); the
/// generic strategy is the oracle for the value and, through the zero-argument property
/// cache seam, for the number of evaluations (a local-only property is evaluated once per
/// binding context — once per activation, and a call is a fresh activation).
/// </summary>
public class LoopTempMemoSuspensionTests
{
    private static LoopRunFrame Frame()
    {
        var step = new Algorithm.User(null, [], [], [], []);
        var plan = new LoopPlanTemplate(LoopKind.Repeat, step, 0,
            [new LoopTempPlan("A", 0, [], new LoopExprPlan.Constant(new Expr.Num(0), PlannedLoopValue.FromNumeric(0)), null, new Property("A", step))],
            [], null, false, Evaluator.EvalCtx.Empty, null);
        return new LoopRunFrame(plan, [], []);
    }

    [Fact]
    public void SuspensionAndDisposal_DoNotAllocate()
    {
        var frame = Frame();
        for (var i = 0; i < 16; i++)
        {
            using var warmup = frame.SuspendTempMemo();
        }
        var before = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < 1024; i++)
        {
            using var outer = frame.SuspendTempMemo();
            using var inner = frame.SuspendTempMemo();
        }
        Assert.Equal(0, GC.GetAllocatedBytesForCurrentThread() - before);
    }

    [Fact]
    public void Suspension_RejectsCopiedOrOutOfOrderDispose_BeforeChangingTheMemo()
    {
        var frame = Frame();
        var root = PlannedLoopValue.FromNumeric(10);
        var first = PlannedLoopValue.FromNumeric(20);
        var second = PlannedLoopValue.FromNumeric(30);
        frame.SetTempSlot(0, root);
        var outer = frame.SuspendTempMemo();
        var copy = outer;
        frame.SetTempSlot(0, first);
        var inner = frame.SuspendTempMemo();
        frame.SetTempSlot(0, second);

        Assert.Throws<InvalidOperationException>(() => copy.Dispose());
        Assert.True(frame.TryGetTempSlot(0, out var current));
        Assert.Equal(second, current);
        inner.Dispose();
        Assert.True(frame.TryGetTempSlot(0, out current));
        Assert.Equal(first, current);
        outer.Dispose();
        using (frame.SuspendTempMemo())
        {
            frame.SetTempSlot(0, second);
            Assert.Throws<InvalidOperationException>(() => copy.Dispose());
            Assert.True(frame.TryGetTempSlot(0, out current));
            Assert.Equal(second, current);
        }
        Assert.True(frame.TryGetTempSlot(0, out current));
        Assert.Equal(root, current);
        default(LoopRunFrame.TempMemoSuspension).Dispose();
    }

    [Fact]
    public void ExceptionalNestedSuspension_RestoresEachMemo_AndLeavesNoCallMemoInTheNextIteration()
    {
        var frame = Frame();
        frame.SetTempSlot(0, PlannedLoopValue.FromNumeric(10));
        using (frame.SuspendTempMemo())
        {
            frame.SetTempSlot(0, PlannedLoopValue.FromNumeric(20));
            Assert.Throws<OperationCanceledException>((Action)(() =>
            {
                using var inner = frame.SuspendTempMemo();
                frame.SetTempSlot(0, PlannedLoopValue.FromNumeric(30));
                throw new OperationCanceledException();
            }));
            Assert.True(frame.TryGetTempSlot(0, out var current));
            Assert.Equal(20, current.AsNum());
        }
        Assert.True(frame.TryGetTempSlot(0, out var restored));
        Assert.Equal(10, restored.AsNum());
        frame.BeginIteration();
        Assert.False(frame.TryGetTempSlot(0, out _));
    }

    private sealed class CountingCache : IZeroArgPropertyResultCache
    {
        private readonly RunScopedZeroArgPropertyResultCache _inner = new();

        public Dictionary<string, int> Evaluations { get; } = new(StringComparer.Ordinal);

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
            => _inner.GetOrEvaluate(execution, () =>
            {
                Evaluations[execution.Binding.Name] = Evaluations.GetValueOrDefault(execution.Binding.Name) + 1;
                return evaluate();
            });
    }

    private static Decimal128 Atom(EvalResult<Evaluator.CountedResult> result)
    {
        Assert.False(result.IsError, $"expected success but got: {(result.IsError ? result.Error : null)}");
        return Assert.IsType<Result.Atom>(result.Value.Value).Value;
    }

    private static (Decimal128 Value, CountingCache Cache, LoopOptimizationDiagnosticsSnapshot Loop) Observe(string source, bool optimized)
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var cache = new CountingCache();
        var diagnostics = new LoopOptimizationDiagnostics();
        var (result, _) = Evaluator.RunCountedObserved(
            program,
            enableOptimizations: optimized,
            zeroArgPropertyResultCache: cache,
            loopDiagnostics: diagnostics);
        return (Atom(result), cache, diagnostics.GetSnapshot());
    }

    /// <summary>The optimized run took the wholly planned path; returns its output plan.</summary>
    private static string OutputSummary(LoopOptimizationDiagnosticsSnapshot loop)
    {
        Assert.Equal(1, loop.OptimizedLoopHits);
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);
        var plan = Assert.Single(loop.LoopPlans);
        Assert.True(plan.Optimized, plan.FallbackReason);
        return Assert.Single(plan.Expressions, e => e.Role == "output" && e.Index == 0).PlanSummary!;
    }

    [Fact]
    public void TempCall_SuspendsTheCallerMemoForTheCall_AndReinstatesItAfterwards()
    {
        // Per iteration: the first bare `A` fills the iteration memo (one multiplication);
        // inside `B()` the memo is suspended, so B's bare `A` misses and runs again (one
        // multiplication) before B's own addition; after the call the memo is reinstated, so
        // the third `A` hits; plus the output row's two additions — five planned operations
        // per iteration. A memo left suspended after the call would cost a sixth (the final
        // `A` would miss); a call that did not suspend would cost only four.
        // Values: iteration 1 (n = 0) is 0 + 1 + 0 = 1, iteration 2 (n = 1) is 10 + 11 + 10 = 31.
        const string source = "Step(n) = {\n    A = n * 10\n    B = A + 1\n    A + B() + A\n}\nStep.repeat(2, 0)";

        var generic = Observe(source, optimized: false);
        var planned = Observe(source, optimized: true);

        Assert.Equal(31m, generic.Value);
        Assert.Equal(31m, planned.Value);
        // Generic oracle: A is evaluated once per activation — Step's and B's, per iteration.
        Assert.Equal(4, generic.Cache.Evaluations["A"]);
        Assert.Equal("Add(Add(TempSlot(A), TempCall(B)), TempSlot(A))", OutputSummary(planned.Loop));
        Assert.Equal(10, planned.Loop.PlannedBuiltinOperations);
    }

    [Fact]
    public void NestedTempCalls_ReinstateEachSuspendedMemoInReverseOrder()
    {
        // `B()` suspends the iteration memo; inside it `C()` suspends B's call memo. Per
        // iteration: the iteration's `A` (1 multiplication); in B, `A` misses (1), `C()` runs
        // C's body — a bare `A` that misses under C's own fresh memo (1) — then B's two
        // additions (2) with B's second `A` served by B's REINSTATED memo; back in the
        // iteration, the two output additions (2) with the final `A` served by the reinstated
        // iteration memo — seven planned operations. Reinstating the wrong memo after `C()`
        // (B's second `A` misses) or none after `B()` (the final `A` misses) costs an extra
        // multiplication each.
        // Values: iteration 1 (n = 1) is 10 + 30 + 10 = 50, iteration 2 (n = 50) is
        // 500 + 1500 + 500 = 2500.
        // (A temp is planned against the temps declared BEFORE it, so C precedes B.)
        const string source = "Step(n) = {\n    A = n * 10\n    C = A\n    B = A + C() + A\n    A + B() + A\n}\nStep.repeat(2, 1)";

        var generic = Observe(source, optimized: false);
        var planned = Observe(source, optimized: true);

        Assert.Equal(2500m, generic.Value);
        Assert.Equal(2500m, planned.Value);
        // Generic oracle: A is evaluated once per activation — Step's, B's, and C's, per iteration.
        Assert.Equal(6, generic.Cache.Evaluations["A"]);
        Assert.Equal("Add(Add(TempSlot(A), TempCall(B)), TempSlot(A))", OutputSummary(planned.Loop));
        Assert.Equal(14, planned.Loop.PlannedBuiltinOperations);
    }
}
