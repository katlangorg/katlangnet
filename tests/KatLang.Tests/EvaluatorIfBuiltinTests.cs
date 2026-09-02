using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorIfBuiltinTests
{
    // â”€â”€ If builtin â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_If_TrueCondition_ReturnsThenBranch()
        => AssertEval("if(1, (10), (20))", 10);

    [Fact]
    public void Eval_If_FalseCondition_ReturnsElseBranch()
        => AssertEval("if(0, (10), (20))", 20);

    [Fact]
    public void Eval_If_NonZeroCondition_ReturnsThenBranch()
        => AssertEval("if(5, (10), (20))", 10);

    [Fact]
    public void Eval_If_NegativeCondition_ReturnsThenBranch()
        => AssertEval("if(-1, (10), (20))", 10);

    [Fact]
    public void Eval_If_WithExpressions()
        => AssertEval("if(3 > 2, (100), (200))", 100);

    [Fact]
    public void Eval_If_MultipleOutputs()
        => AssertEval("if(1, (1, 2), (3, 4))", 1, 2);

    // Issue #130: a selected branch that is a multi-output property such as
    // `X = 1, 2, 3` is observed as one grouped sequence value (emitted count 1),
    // exactly like value-position property access — not three separate outputs.
    [Theory]
    [InlineData("X = 1, 2, 3\nif(1, X, X)")]
    [InlineData("X = 1, 2, 3\nif(0, X, X)")]
    public void Eval_If_MultiOutputBranchProperty_CollapsesToOneSequenceValue(string source)
        => AssertEvalCounted(source, 1, ResultFromAtoms(1, 2, 3));

    [Fact]
    public void Eval_If_DistinctMultiOutputBranches_TrueSelectsThenAsOneValue()
        => AssertEvalCounted("X = 1, 2, 3\nY = 10, 20, 30\nif(1, X, Y)", 1, ResultFromAtoms(1, 2, 3));

    [Fact]
    public void Eval_If_DistinctMultiOutputBranches_FalseSelectsElseAsOneValue()
        => AssertEvalCounted("X = 1, 2, 3\nY = 10, 20, 30\nif(0, X, Y)", 1, ResultFromAtoms(10, 20, 30));

    [Fact]
    public void Eval_If_ParenthesizedBranchProperty_StaysOneSequenceValue()
        => AssertEvalCounted("X = (1, 2, 3)\nif(1, X, X)", 1, ResultFromAtoms(1, 2, 3));

    [Fact]
    public void Eval_If_SpreadResult_OpensSelectedBranchIntoItems()
        => AssertEvalCounted("X = 1, 2, 3\nif(1, X, X)*", 3, ResultFromAtoms(1, 2, 3));

    // Issue #131: an explicit spread argument opens its value into the three `if`
    // call-argument slots, so `if(X*)` with `X = 1, 2, 3` is equivalent to
    // `if(1, 2, 3)` and selects the `whenTrue` branch (2) as one value.
    [Theory]
    [InlineData("TrueResult = 1, 2, 3\nif(TrueResult*)")]
    [InlineData("TrueResult = (1, 2, 3)\nif(TrueResult*)")]
    [InlineData("Pair = 2, 3\nif(1, Pair*)")]
    public void Eval_If_SpreadArgument_OpensIntoThreeArguments(string source)
        => AssertEvalCounted(source, 1, Atom(2));

    // A direct builtin `if(X*)` matches the user-wrapper `MyIF(X*)` path.
    [Fact]
    public void Eval_If_SpreadArgument_MatchesUserWrapper()
    {
        var direct = EvalFull("TrueResult = 1, 2, 3\nif(TrueResult*)");
        var wrapped = EvalFull("TrueResult = 1, 2, 3\nMyIF(a, b, c) = if(a, b, c)\nMyIF(TrueResult*)");
        Assert.False(direct.IsError);
        Assert.False(wrapped.IsError);
        Assert.True(Result.ValueComparer.Equals(direct.Value, wrapped.Value));
        Assert.True(Result.ValueComparer.Equals(direct.Value, Atom(2)));
    }

    // A spread whose expanded count is not 3 now reaches evaluation and fails with
    // the normal builtin arity mismatch (expected 3), not a parser arity error.
    [Fact]
    public void Eval_If_SpreadArgument_WrongExpandedArity_FailsAtEvaluation()
        => AssertEvalFailsWithArityMismatch("Two = 1, 2\nif(Two*)", expected: 3, actual: 2);

    // The fix changes counted/display provenance only; the selected branch value
    // is unchanged, so operations that consume the value still open it as before.
    [Theory]
    [InlineData("X = 1, 2, 3\ncount(if(1, X, X))", 3)]
    [InlineData("X = 1, 2, 3\nsum(if(1, X, X))", 6)]
    [InlineData("X = 1, 2, 3\nfirst(if(1, X, X))", 1)]
    public void Eval_If_MultiOutputBranchProperty_ValueIsInvariant(string source, int expected)
        => AssertEval(source, expected);

    [Fact]
    public void Eval_If_ParenSubExpr_FirstArg_Works()
        => AssertEval("if((1 + 2) mod 2 == 0, 1, 0)", 0);

    // ── if builtin ───────────────────────────────────────────────────────────────

    [Fact]
    public void Eval_If3_TrueCondition_ReturnsThenBranch()
        => AssertEval("if(1 == 1, 5, 6)", 5);

    [Fact]
    public void Eval_If3_FalseCondition_ReturnsElseBranch()
        => AssertEval("if(1 == 2, 5, 6)", 6);

    [Fact]
    public void Eval_If3_TrueInAddition()
        => AssertEval("10 + if(1 == 1, 5, 0)", 15);

    [Fact]
    public void Eval_If3_FalseInAddition()
        => AssertEval("10 + if(1 == 2, 5, 0)", 10);

    [Fact]
    public void Eval_If3_CompatibleWithEarlierCoverage_True()
        => AssertEval("if(1 == 1, 5, 6)", 5);

    [Fact]
    public void Eval_If3_CompatibleWithEarlierCoverage_False()
        => AssertEval("if(1 == 2, 5, 6)", 6);

    [Fact]
    public void Eval_If2_RuntimeBuiltinCall_FailsWithSignatureArityMessage()
    {
        var expr = new Expr.Call(
            new Expr.Resolve("if"),
            [new Expr.Num(1), new Expr.Num(5)]);

        var result = Evaluator.Run(expr);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Equal(
            "Callable `if(condition, whenTrue, whenFalse)` expects 3 arguments, but was called with 2 arguments.",
            formatted);
    }

    [Fact]
    public void Eval_If2_RuntimeBuiltinCallInBinary_FailsInsteadOfPropagatingEmptyResult()
    {
        var expr = new Expr.Binary(
            BinaryOp.Mul,
            new Expr.Num(10),
            new Expr.Call(
                new Expr.Resolve("if"),
                [
                    new Expr.Binary(BinaryOp.Lt, new Expr.Num(7), new Expr.Num(6)),
                    new Expr.Num(1),
                ]));

        var result = Evaluator.Run(expr);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Equal(
            "Callable `if(condition, whenTrue, whenFalse)` expects 3 arguments, but was called with 2 arguments.",
            formatted);
    }
}
