namespace KatLang.Tests;

/// <summary>
/// The numeric fields of an <c>if</c> builtin arity failure are NORMATIVE:
/// <c>if</c> requires exactly three arguments, so every reachable <c>if</c>
/// arity failure carries <c>Expected = 3</c> (never the generic-builtin
/// placeholder 0) with <c>Actual</c> = the assembled argument count.
///
/// C# populates the payload in <c>WrongBuiltinArity</c> (the one construction
/// point for builtin arity errors, which special-cases <c>if</c>); these tests
/// pin the C# side of the cross-implementation contract. Lean twins: the
/// CoreTests guards <c>ifDotCallUnderArityCarriesExpectedThree</c> /
/// <c>ifDotCallOverArityCarriesExpectedThree</c> against the same dot-call
/// reproducers (direct malformed <c>if(...)</c> forms are parser-gated by
/// <c>ValidateIfArity</c>, so the dot-call surface is the one that reaches the
/// evaluator's arity payload).
/// </summary>
public class IfBuiltinArityPayloadTests
{
    private static Expr Program(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, "dot-call reproducers must not be parser-gated");
        return new Expr.Block(parsed.Root);
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        return error;
    }

    /// <summary>Ordered outermost-to-innermost legacy context spellings.</summary>
    private static IReadOnlyList<string> ContextChain(EvalError error)
    {
        var chain = new List<string>();
        while (error is EvalError.WithContext context)
        {
            chain.Add(context.ErrorContext.ToLegacyString());
            error = context.Inner;
        }

        return chain;
    }

    private static EvalError.ArityMismatch AssertIfArityPayload(string source, int expectedActual)
    {
        var result = Evaluator.Run(Program(source));

        Assert.True(result.IsError, "expected an if arity rejection");
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
        Assert.Equal(3, arity.Expected);
        Assert.Equal(expectedActual, arity.Actual);
        Assert.Equal("if", arity.Signature?.Name);
        Assert.Contains("while evaluating dotCall .if of A", ContextChain(result.Error));
        return arity;
    }

    [Fact]
    public void DotCallUnderArity_CarriesExpectedThreeActualTwo()
    {
        // `A.if(2)` assembles the receiver plus one written argument: actual 2.
        AssertIfArityPayload("A = 1\nA.if(2)", expectedActual: 2);
    }

    [Fact]
    public void DotCallOverArity_CarriesExpectedThreeActualFour()
    {
        // `A.if(2, 3, 4)` assembles the receiver plus three written arguments: actual 4.
        AssertIfArityPayload("A = 1\nA.if(2, 3, 4)", expectedActual: 4);
    }

    [Fact]
    public void DotCallExactArity_StillDispatchesAndKeepsBranchLaziness()
    {
        // `A.if(20, 30)` is `if(A, 20, 30)` = `if(1, 20, 30)` → 20.
        var dispatched = Evaluator.RunFlat(Program("A = 1\nA.if(20, 30)"));
        Assert.False(dispatched.IsError);
        Assert.Equal([20m], dispatched.Value);

        // The unselected branch stays lazy: `1 / 0` in the else slot never runs.
        var lazyElse = Evaluator.RunFlat(Program("A = 1\nA.if(20, 1 / 0)"));
        Assert.False(lazyElse.IsError);
        Assert.Equal([20m], lazyElse.Value);
    }
}
