using System.Reflection;

namespace KatLang.Tests;

public class NeedCellStackHeadroomTests
{
    // The forty-link UnifiedFormulaLiftingTests case is the end-to-end stack pin.
    // This structural pin also catches the regression in configurations where a
    // different JIT state happens to leave enough headroom for that computation.
    [Fact]
    public void SuspendedValueCompletion_KeepsLargeContextsOutOfTheRecursiveFrame()
    {
        var finish = typeof(Evaluator).GetMethod("FinishSuppliedValue", BindingFlags.NonPublic | BindingFlags.Static)!;
        Assert.DoesNotContain(finish.GetParameters(), parameter => parameter.ParameterType == typeof(Evaluator.EvalCtx));
        Assert.True((finish.MethodImplementationFlags & MethodImplAttributes.NoInlining) != 0);

        // Positive control: ordinary expression evaluation still takes the context
        // by value. The constraint is the completion boundary, not EvalCtx itself.
        var evaluate = typeof(Evaluator).GetMethod("EvalCounted", BindingFlags.NonPublic | BindingFlags.Static)!;
        Assert.Contains(evaluate.GetParameters(), parameter => parameter.ParameterType == typeof(Evaluator.EvalCtx));
    }
}
