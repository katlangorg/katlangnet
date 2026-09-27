using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// Explicit temp calls evaluate their own body fresh, while sibling property reads
/// still belong to the step's activation and share its per-iteration memo.
/// </summary>
public class LoopTempMemoSuspensionTests
{
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
    public void TempCall_KeepsTheDeclaringStepMemoForSiblingReads()
    {
        // A evaluates once per iteration; B() reads that same A and adds one.
        const string source = "Step(n) = {\n    A = n * 10\n    B = A + 1\n    A + B() + A\n}\nStep.repeat(2, 0)";

        var generic = Observe(source, optimized: false);
        var planned = Observe(source, optimized: true);

        Assert.Equal(31m, generic.Value);
        Assert.Equal(31m, planned.Value);
        // A belongs to Step, even while B() is executing.
        Assert.Equal(2, generic.Cache.Evaluations["A"]);
        Assert.Equal("Add(Add(TempSlot(A), TempCall(B)), TempSlot(A))", OutputSummary(planned.Loop));
        Assert.Equal(8, planned.Loop.PlannedBuiltinOperations);
    }

    [Fact]
    public void NestedTempCalls_KeepTheDeclaringStepMemo()
    {
        // B() and C() read the same sibling A; only their own bodies run fresh.
        const string source = "Step(n) = {\n    A = n * 10\n    C = A\n    B = A + C() + A\n    A + B() + A\n}\nStep.repeat(2, 1)";

        var generic = Observe(source, optimized: false);
        var planned = Observe(source, optimized: true);

        Assert.Equal(2500m, generic.Value);
        Assert.Equal(2500m, planned.Value);
        // One A evaluation in each of the two Step activations.
        Assert.Equal(2, generic.Cache.Evaluations["A"]);
        Assert.Equal("Add(Add(TempSlot(A), TempCall(B)), TempSlot(A))", OutputSummary(planned.Loop));
        Assert.Equal(10, planned.Loop.PlannedBuiltinOperations);
    }
}
