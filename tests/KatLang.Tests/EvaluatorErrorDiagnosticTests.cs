using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorErrorDiagnosticTests
{
    // â”€â”€ Edge cases â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_EmptySource_HasNoDefinedOutput()
        => AssertMissingOutputMessage(
            "",
            RunResult.NoProgramOutput.DefaultMessage);

    [Fact]
    public void Eval_UndefinedProperty_Fails()
        => AssertEvalFails("X");

    [Fact]
    public void Eval_UnknownIdentifier_ReturnsUnresolvedImplicitParams()
    {
        // "Sum" is detected as a parameter by ParameterDetector, so the root
        // block has params=["Sum"].  Block value-position semantics:
        // 1+ params => UnresolvedImplicitParams.
        var err = GetEvalError("Sum");
        Assert.NotNull(err);
        while (err is EvalError.WithContext wc)
            err = wc.Inner;
        var uip = Assert.IsType<EvalError.UnresolvedImplicitParams>(err);
        Assert.Equal(["Sum"], uip.ParamNames);
    }

    [Fact]
    public void Eval_UnknownIdentifier_CarriesStructuredImplicitParameterContext()
    {
        var error = GetEvalError("Sum");
        Assert.NotNull(error);

        var contextual = Assert.IsType<EvalError.WithContext>(error);
        var implicitContext = Assert.IsType<ImplicitParameterContext>(contextual.ErrorContext);
        Assert.Equal(["Sum"], implicitContext.ParamNames);
        Assert.Equal(0, implicitContext.ProvidedArgumentCount);

        var unresolved = Assert.IsType<EvalError.UnresolvedImplicitParams>(contextual.Inner);
        Assert.Equal(["Sum"], unresolved.ParamNames);

        var formatted = KatLangError.FromEvalError(error).Message;
        Assert.Contains("KatLang interprets it as an implicit parameter", formatted);
        Assert.Contains("expected 1 argument, got 0", formatted);
        Assert.DoesNotContain("while evaluating", formatted);
    }

    [Fact]
    public void Eval_UnknownIdentifier_ReturnsUnresolvedImplicitParamsType()
    {
        // "Sum" becomes a parameter → block has 1 param → UnresolvedImplicitParams in value position.
        var err = GetEvalError("Sum");
        Assert.NotNull(err);
        while (err is EvalError.WithContext wc)
            err = wc.Inner;
        Assert.IsType<EvalError.UnresolvedImplicitParams>(err);
    }

    [Fact]
    public void Eval_DivByZero_HasCorrectSpan()
    {
        var err = GetEvalError("5 / 0");
        Assert.NotNull(err);
        Assert.NotNull(err.Span);
        // Binary expression "5 / 0" spans full expression
        Assert.Equal(1, err.Span.StartLineNumber);
        Assert.Equal(1, err.Span.StartColumn);
        Assert.Equal(1, err.Span.EndLineNumber);
        Assert.Equal(5, err.Span.EndColumn);
    }

    [Fact]
    public void Eval_UnknownIdentifier_MultiLine_ReturnsUnresolvedImplicitParams()
    {
        // Y is detected as a parameter → block has 1 param → UnresolvedImplicitParams.
        var source = """
            X = 5
            Y
            """;
        var err = GetEvalError(source);
        Assert.NotNull(err);
        while (err is EvalError.WithContext wc)
            err = wc.Inner;
        Assert.IsType<EvalError.UnresolvedImplicitParams>(err);
    }

    [Fact]
    public void Eval_WrongParamCount_Fails()
    {
        var source = """
            F = a + b
            F(1)
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_ArityMismatch_TooManyArguments_UsesUserFacingMessage()
    {
        AssertArityMismatchMessage(
            """
                A = x
                A(1, 2)
                """,
            "Callable `A(x)` expects 1 argument, but was called with 2 arguments.");
    }

    [Fact]
    public void Eval_ArityMismatch_TooFewArguments_UsesUserFacingMessage()
    {
        AssertArityMismatchMessage(
            """
                Add = a + b
                Add(1)
                """,
            "Callable `Add(a, b)` expects 2 arguments, but was called with 1 argument.");
    }

    [Fact]
    public void Eval_ArityMismatch_DirectCall_CarriesStructuredCallContext()
    {
        var source = """
                Add = a + b
                Add(1)
                """;

        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var contextual = Assert.IsType<EvalError.WithContext>(result.Error);
        var callContext = Assert.IsType<CallContext>(contextual.ErrorContext);
        Assert.Equal("Add", callContext.CalleeDescription);

        var arity = Assert.IsType<EvalError.ArityMismatch>(contextual.Inner);
        Assert.Equal(2, arity.Expected);
        Assert.Equal(1, arity.Actual);
        Assert.NotNull(arity.Signature);
        Assert.Equal("Add(a, b)", arity.Signature.DisplayText);

        Assert.Equal(
            "Callable `Add(a, b)` expects 2 arguments, but was called with 1 argument.",
            KatLangError.FromEvalError(result.Error).Message);
    }

    [Fact]
    public void Eval_ArityMismatch_CountedFlatFixedDirectCall_UsesSignatureDisplay()
    {
        var source = """
                Add(a, b) = a + b
                Add(1).count
                """;

        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
        Assert.Equal(2, arity.Expected);
        Assert.Equal(1, arity.Actual);
        Assert.NotNull(arity.Signature);
        Assert.Equal("Add(a, b)", arity.Signature.DisplayText);

        Assert.Contains(
            "Callable `Add(a, b)` expects 2 arguments, but was called with 1 argument.",
            KatLangError.FromEvalError(result.Error).Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_ArityMismatch_NoArgumentsProvided_UsesUserFacingMessage()
    {
        var source = """
                A = x
                A
                """;

        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var contextual = Assert.IsType<EvalError.WithContext>(result.Error);
        var propertyContext = Assert.IsType<PropertyEvaluationContext>(contextual.ErrorContext);
        Assert.Equal("A", propertyContext.PropertyName);
        var arity = Assert.IsType<EvalError.ArityMismatch>(contextual.Inner);
        Assert.Equal(1, arity.Expected);
        Assert.Equal(0, arity.Actual);

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Equal(
            "Property 'A' expects 1 parameter, but was called with 0 arguments.\n"
            + "An implicit parameter 'x' was inferred at [1:5].",
            formatted);
    }

    [Fact]
    public void Eval_ArityMismatch_ZeroParameterPropertyCalledWithArguments_UsesUserFacingMessage()
    {
        AssertArityMismatchMessage(
            """
                A = 1
                A(1)
                """,
            "Callable `A` expects 0 arguments, but was called with 1 argument.");
    }
    [Fact]
    public void Eval_ArityMismatch_InnerCall_SpanPointsToInnerCall()
    {
        // Inner has 0 params; calling Inner(param) inside Outer should produce
        // an error whose span points to Inner(param), not the outer Outer(50000).
        var source = """
                Inner = 5
                Outer = param - Inner(param)
                Outer(50000)
                """;
        var err = GetEvalError(source);
        Assert.NotNull(err);
        Assert.NotNull(err.Span);
        // Span should point to "Inner(param)" on line 2, NOT "Outer(50000)" on line 3.
        Assert.Equal(2, err.Span.StartLineNumber);
    }

    // ── Top-level unresolved implicit parameters ──

    [Fact]
    public void Eval_TopLevel_SingleImplicitParam_ErrorMessage()
    {
        var result = EvalFull("a + 1");
        if (result.IsOk)
            Assert.Fail($"Expected error but got: {result.Value}");
        var error = result.Error;
        var contextual = Assert.IsType<EvalError.WithContext>(error);
        var implicitContext = Assert.IsType<ImplicitParameterContext>(contextual.ErrorContext);
        Assert.Equal(["a"], implicitContext.ParamNames);
        Assert.Equal(0, implicitContext.ProvidedArgumentCount);

        var uip = Assert.IsType<EvalError.UnresolvedImplicitParams>(contextual.Inner);
        Assert.Equal(["a"], uip.ParamNames);
        var formatted = KatLangError.FromEvalError(error).Message;
        Assert.Contains("Identifier 'a' does not resolve to a property or other visible name here", formatted);
        Assert.Contains("KatLang interprets it as an implicit parameter", formatted);
        Assert.Contains("Its value is provided by the caller", formatted);
        Assert.Contains("No argument was provided", formatted);
        Assert.Contains("expected 1 argument, got 0", formatted);
        Assert.DoesNotContain("not defined in the current scope", formatted);
    }

    [Fact]
    public void Eval_TopLevel_MultipleImplicitParams_ErrorMessage()
    {
        var result = EvalFull("a + b");
        if (result.IsOk)
            Assert.Fail($"Expected error but got: {result.Value}");
        var error = result.Error;
        var contextual = Assert.IsType<EvalError.WithContext>(error);
        var implicitContext = Assert.IsType<ImplicitParameterContext>(contextual.ErrorContext);
        Assert.Equal(["a", "b"], implicitContext.ParamNames);
        Assert.Equal(0, implicitContext.ProvidedArgumentCount);

        var uip = Assert.IsType<EvalError.UnresolvedImplicitParams>(contextual.Inner);
        Assert.Equal(2, uip.ParamNames.Count);
        var formatted = KatLangError.FromEvalError(error).Message;
        Assert.Contains("Identifiers 'a' and 'b' do not resolve to properties or other visible names here", formatted);
        Assert.Contains("KatLang interprets them as implicit parameters", formatted);
        Assert.Contains("Their values are provided by the caller", formatted);
        Assert.Contains("No arguments were provided", formatted);
        Assert.Contains("expected 2 arguments, got 0", formatted);
        Assert.DoesNotContain("not defined in the current scope", formatted);
    }

    [Fact]
    public void Eval_InnerCall_ArityMismatch_StillGeneric()
    {
        // A normal arity mismatch inside a call (too many args) should NOT be UnresolvedImplicitParams
        var source = """
            G(x) = x + 1
            G(1, 2)
            """;
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected error but got: {result.Value}");
        var error = result.Error;
        while (error is EvalError.WithContext wc)
            error = wc.Inner;
        Assert.IsNotType<EvalError.UnresolvedImplicitParams>(error);
    }
}
