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
        // Binary expression "5 / 0" spans the full expression: [1:1, 1:6).
        Assert.Equal(new SourceSpan(1, 1, 1, 6), err.Span);
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

    // ── MissingOutput blames the ARGUMENT, never the callee ──────────────────

    /// <summary>
    /// Final audit (September 2026): a call whose ARGUMENT had no output used to render
    /// as the CALLEE's failure — `F(NoOut)` with `F(a) = a + 1` said "Cannot call 'F'
    /// because it has no defined output", and `sum(NoOut)` blamed `sum`. The value demand
    /// on a parameter bound to an output-less algorithm is that PARAMETER's failure
    /// (<see cref="ParameterEvaluationContext"/>), and a named argument demanded by a
    /// builtin value slot is that PROPERTY's failure, both still enclosed by the call's
    /// own context. The structured error kind and payload are unchanged (innermost
    /// <see cref="EvalError.MissingOutput"/>), so Lean is untouched.
    /// </summary>
    [Fact]
    public void Eval_MissingOutput_OfAnArgumentReadThroughAParameter_BlamesTheParameter()
    {
        var result = EvalFull("NoOut = { X = 1 }\nF(a) = a + 1\nF(NoOut)");
        Assert.True(result.IsError);
        AssertInnermostMissingOutput(result.Error);

        var call = Assert.IsType<EvalError.WithContext>(result.Error);
        Assert.Equal("F", Assert.IsType<CallContext>(call.ErrorContext).CalleeDescription);
        var parameter = Assert.IsType<EvalError.WithContext>(call.Inner);
        Assert.Equal("a", Assert.IsType<ParameterEvaluationContext>(parameter.ErrorContext).ParameterName);

        var message = KatLangError.FromEvalError(result.Error).Message;
        Assert.StartsWith("while evaluating call to F: Parameter 'a' has no defined output", message, StringComparison.Ordinal);
        Assert.DoesNotContain("Cannot call 'F'", message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("NoOut = { X = 1 }\nsum(NoOut)", "sum")]
    [InlineData("NoOut = { X = 1 }\nif(1, NoOut, 2)", "if")]
    [InlineData("NoOut = { X = 1 }\ncount(NoOut)", "count")]
    public void Eval_MissingOutput_OfANamedArgumentDemandedByABuiltinValueSlot_BlamesTheProperty(string source, string callee)
    {
        var result = EvalFull(source);
        Assert.True(result.IsError);
        AssertInnermostMissingOutput(result.Error);

        var call = Assert.IsType<EvalError.WithContext>(result.Error);
        Assert.Equal(callee, Assert.IsType<CallContext>(call.ErrorContext).CalleeDescription);
        var property = Assert.IsType<EvalError.WithContext>(call.Inner);
        Assert.Equal("NoOut", Assert.IsType<PropertyEvaluationContext>(property.ErrorContext).PropertyName);

        var message = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("Property 'NoOut' has no defined output", message, StringComparison.Ordinal);
        Assert.DoesNotContain($"Cannot call '{callee}'", message, StringComparison.Ordinal);
    }

    /// <summary>
    /// Final hostile pass (September 2026): the same blame when the demanded argument is read
    /// through a PARAMETER — a builtin value slot (`F(a) = sum(a)`), the reduce initial
    /// accumulator, and the `.string` receiver — reports the parameter, never the builtin and
    /// never "Property 'a' has no defined output".
    /// </summary>
    [Theory]
    [InlineData("NoOut = { X = 1 }\nF(a) = sum(a)\nF(NoOut)")]
    [InlineData("NoOut = { X = 1 }\nF(a) = count(a)\nF(NoOut)")]
    [InlineData("NoOut = { X = 1 }\nF(a) = if(1, a, 0)\nF(NoOut)")]
    [InlineData("NoOut = { X = 1 }\nStep(acc, x) = acc + x\nF(a) = reduce((1, 2), Step, a)\nF(NoOut)")]
    [InlineData("NoOut = { X = 1 }\nF(a) = a.string\nF(NoOut)")]
    [InlineData("NoOut = { X = 1 }\nF(a) = a.string()\nF(NoOut)")]
    public void Eval_MissingOutput_OfAnArgumentReadThroughAParameterInAValueSlot_BlamesTheParameter(string source)
    {
        var result = EvalFull(source);
        Assert.True(result.IsError);
        AssertInnermostMissingOutput(result.Error);

        var contexts = new List<ErrorContext>();
        for (var error = result.Error; error is EvalError.WithContext context; error = context.Inner)
            contexts.Add(context.ErrorContext);
        Assert.Contains(contexts, c => c is ParameterEvaluationContext { ParameterName: "a" });
        Assert.DoesNotContain(contexts, c => c is PropertyEvaluationContext);

        var message = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("Parameter 'a' has no defined output", message, StringComparison.Ordinal);
        Assert.DoesNotContain("Cannot call 'sum'", message, StringComparison.Ordinal);
        Assert.DoesNotContain("Cannot call 'count'", message, StringComparison.Ordinal);
        Assert.DoesNotContain("Cannot call 'reduce'", message, StringComparison.Ordinal);
        Assert.DoesNotContain("Property 'a'", message, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_MissingOutput_OfANamedReduceInitialAccumulator_BlamesTheProperty()
    {
        var result = EvalFull("NoOut = { X = 1 }\nStep(acc, x) = acc + x\nreduce((1, 2), Step, NoOut)");
        Assert.True(result.IsError);
        AssertInnermostMissingOutput(result.Error);
        var message = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("Property 'NoOut' has no defined output", message, StringComparison.Ordinal);
        Assert.DoesNotContain("Cannot call 'reduce'", message, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_MissingOutput_OfTheCalleeItself_StillBlamesTheCallee()
    {
        // The inverse: a callee with no output rows is the callee's own failure.
        AssertMissingOutputMessage(
            "NoOut = { X = 1 }\nNoOut()",
            "Cannot call 'NoOut' because it has no defined output.\nAdd an output expression, or use `()` if the empty sequence value was intended. To call one of its properties, use property access instead.");
    }

    /// <summary>
    /// Final audit (September 2026): the two structured not-callable descriptions shared
    /// with Lean (`param(name)`, `num(value)`) are rendered in KatLang terms; the payload
    /// (<see cref="EvalError.NotAnAlgorithm.Description"/>) is unchanged.
    /// </summary>
    [Fact]
    public void Eval_NotCallableParameterAndNumber_RenderInKatLangTerms()
    {
        var parameter = EvalFull("Apply(f, x) = f(x)\nApply(1, 2)");
        Assert.True(parameter.IsError);
        var notCallable = Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(parameter.Error));
        Assert.Equal("param(f)", notCallable.Description);
        Assert.Contains("Parameter 'f' is not callable here", KatLangError.FromEvalError(parameter.Error).Message, StringComparison.Ordinal);

        // The `num(value)` shape has no ordinary source reaching it (a number in a callable
        // slot binds a zero-parameter wrapper and fails by arity), so its rendering is pinned
        // from the structured error directly.
        Assert.Equal(
            "The number 5 is not callable.",
            KatLangError.FromEvalError(new EvalError.NotAnAlgorithm("num(5)")).Message);
    }

    /// <summary>
    /// Final hostile pass (September 2026): a builtin value demand inside a CALL context
    /// (`F(v) = v + sum`) carries the Lean-aligned placeholder Expected = 0 beside its real
    /// signature; the call arm used to render the raw pair ("Expected 0 parameters, but was
    /// called with 0 arguments"). The signature is rendered first wherever it is carried.
    /// </summary>
    [Theory]
    [InlineData("F(v) = v + sum\nF(1)")]
    [InlineData("F(v) = sum\nF(1)")]
    [InlineData("F(v) = { v + count }\nF(1)")]
    public void Eval_BuiltinValueDemandInsideACall_RendersTheSignature(string source)
    {
        var result = EvalFull(source);
        Assert.True(result.IsError);
        var message = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("(collection)` expects 1 argument, but was called with 0 arguments", message, StringComparison.Ordinal);
        Assert.DoesNotContain("Expected 0 parameters", message, StringComparison.Ordinal);
    }

    /// <summary>
    /// Final hostile pass (September 2026): the Lean-modeled payload of a flat fixed user
    /// call with too few slots is the VALUE-tier view (a slot bound only on the algorithm
    /// channel — an output-less argument — is left out of both numbers), so the MESSAGE
    /// derives the written count from the signature: `R(Obj)` for `R(a, b)` is "called with
    /// 1 argument", never 0. The structured payload is unchanged.
    /// </summary>
    [Theory]
    [InlineData("Obj = {\n    K = 9\n}\nR(a, b) = b\nR(Obj)", 1, 0, "R(a, b)", 2, 1)]
    [InlineData("Obj = {\n    K = 9\n}\nR(a, b, c) = c\nR(Obj, 1)", 2, 1, "R(a, b, c)", 3, 2)]
    [InlineData("Obj = {\n    K = 9\n}\nR(a, b) = b\nR(Obj, 1, 2)", 2, 3, "R(a, b)", 2, 3)]
    [InlineData("R(a, b) = b\nR(1)", 2, 1, "R(a, b)", 2, 1)]
    public void Eval_ArityMismatch_MessageCountsWrittenSlots_EvenWhenASlotIsAlgorithmOnly(
        string source, int expected, int actual, string signature, int parameters, int written)
    {
        var arity = AssertEvalFailsWithArityMismatch(source, expected, actual);
        var message = KatLangError.FromEvalError(arity).Message;
        Assert.Contains($"Callable `{signature}` expects {parameters} arguments, but was called with {written} argument", message, StringComparison.Ordinal);
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
        Assert.Equal(2, Assert.NotNull(err.Span).Start.Line);
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
