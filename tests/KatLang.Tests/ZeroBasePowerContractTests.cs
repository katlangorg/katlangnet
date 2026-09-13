using System.Numerics;
using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

public class ZeroBasePowerContractTests
{
    private const string Reason = "zero cannot be raised to a negative exponent";

    [Theory]
    [InlineData("Z ^ -0.5")]
    [InlineData("Math.Pow(Z, -0.5)")]
    [InlineData("pow(Z, -2.5)")]
    public async Task NegativeFractionalPower_PreservesErrorAndSpanAfterSuspension(string expression)
    {
        // The preceding output catches an erroneous fallback to the root's first
        // row. Reading Z forces the async cache seam before the power executes.
        var source = $"Z = -0.0\n7\n{expression}";
        var ast = Program(source);
        var plain = Evaluator.Run(ast);
        var counted = Evaluator.RunCountedObserved(ast, enableOptimizations: false).Result;
        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var suspended = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedAsync(ast, cache));

        Assert.True(plain.IsError);
        Assert.True(counted.IsError);
        Assert.True(suspended.IsError);
        foreach (var error in new[] { plain.Error, counted.Error, suspended.Error })
        {
            Assert.Equal(Reason, Assert.IsType<EvalError.IllegalInEval>(Innermost(error)).Reason);
            Assert.Equal(KatLangErrorCode.IllegalInEval, error.Code);
            var diagnostic = KatLangError.FromEvalError(error);
            Assert.Equal(((int?)3, (int?)1, (int?)3, (int?)expression.Length),
                (diagnostic.StartLine, diagnostic.StartColumn, diagnostic.EndLine, diagnostic.EndColumn));
            Assert.Equal(DescribeErrorTree(plain.Error), DescribeErrorTree(error));
        }
        Assert.True(cache.AsyncAccesses > 0);
        Assert.NotEmpty(cache.ThreadHops);
        Assert.Equal(0, cache.SyncAccesses);

        var engine = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        var publicError = Assert.Single(engine.Errors);
        Assert.Equal(KatLangErrorCode.IllegalInEval, publicError.Code);
        Assert.Equal(KatLangError.FromEvalError(plain.Error).Message, publicError.Message);
        Assert.Equal(((int?)3, (int?)1, (int?)3, (int?)expression.Length),
            (publicError.StartLine, publicError.StartColumn, publicError.EndLine, publicError.EndColumn));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void NegativeFractionalPower_ActuallyExecutesThePlannedNumericArm(bool useWhile)
    {
        var source = useWhile
            ? "S(x) = x ^ -0.5, 0\nwhile(S, -0.0)"
            : "S(x) = x ^ -0.5\nrepeat(S, 1, -0.0)";
        var (generic, _) = RunCountedObserved(source, enableLoopOptimization: false);
        var (planned, loop) = RunCountedObserved(source, enableLoopOptimization: true);
        Assert.True(generic.IsError);
        Assert.True(planned.IsError);
        Assert.Equal(Reason, Assert.IsType<EvalError.IllegalInEval>(Innermost(planned.Error)).Reason);
        Assert.Equal(new SourceSpan(1, 8, 1, 15), Innermost(planned.Error).Span);
        Assert.Equal(DescribeErrorTree(generic.Error), DescribeErrorTree(planned.Error));

        // Outcome equality alone could pass if both executions became generic.
        Assert.Equal(1, loop.OptimizedLoopHits);
        var plan = Assert.Single(loop.LoopPlans);
        Assert.True(plan.Optimized);
        var power = Assert.Single(plan.Expressions, item => item.Role == "output" && item.Index == 0);
        Assert.True(power.Planned);
        Assert.StartsWith("Power(StateSlot(x),", power.PlanSummary);
        Assert.Equal(1, loop.LoopIterations);
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);
    }

    [Fact]
    public void NonzeroSubnormalBase_IsNotMistakenForZero()
    {
        var value = SourceProvenance.ParseValid("1e-6176 ^ -0.5").Evaluate();
        Assert.False(value.IsError);
        var number = Assert.IsType<Result.Atom>(value.Value).Value;
        Assert.True(Decimal128.IsFinite(number));
        Assert.True(number > Decimal128.One);
    }
}
