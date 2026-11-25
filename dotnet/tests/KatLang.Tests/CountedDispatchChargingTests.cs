using KatLang.Evaluation;

namespace KatLang.Tests;

public class CountedDispatchChargingTests
{
    public static TheoryData<Expr, Type?> DispatchCases() => new()
    {
        { new Expr.Num(7), null },
        { new Expr.StringLiteral("abc"), null },
        { new Expr.EmptySequence(1), null },
        { new Expr.Param("x"), null },
        { new Expr.NativeCall("Abs", ["x"]), null },
        { new Expr.NativeCall("MissingNative", []), typeof(EvalError.IllegalInEval) },
        { new Expr.Grace(new Expr.Num(1), 1), typeof(EvalError.IllegalInEval) },
    };

    // Direct dispatch isolates the sync NativeCall defect: there is no async leaf
    // charge available to cancel it, and no loop planner or argument adapter involved.
    [Theory]
    [MemberData(nameof(DispatchCases))]
    public void CountedDispatch_ChargesOneCheckpointPerEntry(Expr expression, Type? expectedError)
    {
        var ctx = Evaluator.EvalCtx.Empty with { Budget = EvaluationBudget.Create(new EvaluationLimits { MaxSteps = 1 }) };
        for (var entry = 1; entry <= 8192; entry++)
        {
            var result = Evaluator.EvalCounted(expression, ctx, [("x", new Result.Atom(-7))]);
            if (entry == 8192)
                Assert.IsType<EvalError.EvaluationStepLimitExceeded>(result.Error);
            else if (expectedError is not null)
                Assert.IsType(expectedError, result.Error);
            else
                Assert.False(result.IsError);
            Assert.Equal(entry < 4096 ? 0 : 1, ctx.Budget.ConsumedSteps);
        }
    }
}
