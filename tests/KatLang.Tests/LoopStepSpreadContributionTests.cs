using System.Numerics;
namespace KatLang.Tests;

/// <summary>
/// Loop step-output rows keep the spread contribution floor: a spread row
/// contributes exactly the items its operand supplies — ZERO slots for an empty
/// supply — never a materialized empty-value slot. The receiver here (the loop
/// state binder) distinguishes zero-item supply from an empty value: one phantom
/// slot per iteration turns a well-typed loop into a
/// <c>LoopStateArityMismatch</c>, so these pins hold the
/// <c>EvalAlgOutputSlots</c> spread branch in place independently of the
/// generated arity-differential corpus.
/// </summary>
public class LoopStepSpreadContributionTests
{
    private static IReadOnlyList<Decimal128> FlatValues(string source)
    {
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        if (result.IsError)
            Assert.Fail($"expected a value for `{source.Replace("\n", " ; ")}`, got {result.Error}");
        return result.Value;
    }

    [Fact]
    public void RepeatStep_ZeroEmittingSpreadRow_ContributesNoStateSlot()
    {
        // The step's output rows are: E* (an EMPTY supply — zero slots), x + 1,
        // y + 1. Next state must be exactly two slots across BOTH iterations; a
        // phantom empty slot from the spread row would make three state slots for
        // the two-parameter step and fail the second bind.
        Assert.Equal(
            [12m, 22m],
            FlatValues("E = ()\nStep(x, y) = E*, x + 1, y + 1\nStep.repeat(2, 10, 20)"));
    }

    [Fact]
    public void RepeatStep_MultiEmittingSpreadRow_ContributesEachSuppliedItemAsOneSlot()
    {
        // The complementary direction: ONE spread row supplies BOTH next-state
        // slots, so dropping the spread branch (treating the row as one written
        // value slot) would under-supply the state instead.
        Assert.Equal(
            [12m, 22m],
            FlatValues("Step(x, y) = (x + 1, y + 1)*\nStep.repeat(2, 10, 20)"));
    }

    [Fact]
    public void WhileStep_ZeroEmittingSpreadRow_ContributesNoStateSlot()
    {
        // The while twin adds the continuation flag as the final row; the spread
        // row must still contribute nothing, keeping state-slot count and flag
        // position stable across iterations.
        Assert.Equal(
            [12m, 22m],
            FlatValues("E = ()\nStep(x, y) = E*, x + 1, y + 1, x < 12\nStep.while(10, 20)"));
    }

    [Fact]
    public void PlainAndCountedEvaluators_AgreeOnSpreadStateContributions()
    {
        foreach (var source in new[]
        {
            "E = ()\nStep(x, y) = E*, x + 1, y + 1\nStep.repeat(2, 10, 20)",
            "Step(x, y) = (x + 1, y + 1)*\nStep.repeat(2, 10, 20)",
            "E = ()\nStep(x, y) = E*, x + 1, y + 1, x < 12\nStep.while(10, 20)",
        })
        {
            var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
            var plain = Evaluator.Run(expr);
            var counted = Evaluator.RunCounted(expr);
            Assert.False(plain.IsError, source);
            Assert.False(counted.IsError, source);
            Assert.Equal(plain.Value, counted.Value.Value, Result.ValueComparer);
        }
    }
}
