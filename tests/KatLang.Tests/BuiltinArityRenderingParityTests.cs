namespace KatLang.Tests;

/// <summary>
/// Builtin arity failures render SIGNATURE-FIRST in every call spelling: the
/// non-<c>if</c> builtins deliberately carry the Lean-aligned placeholder
/// <c>Expected = 0</c> beside their real <see cref="CallableSignature"/>, so
/// the dot-call formatter must never leak the sentinel as
/// "expects 0 parameters". The structured leaf payload is unchanged
/// (rendering-only fix; <see cref="IfBuiltinArityPayloadTests"/> pins the
/// <c>if</c> exception with <c>Expected = 3</c>); signatureless structural
/// user-property errors keep their receiver-specific wording.
/// </summary>
public class BuiltinArityRenderingParityTests
{
    private static Expr Program(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private static EvalError Fail(string source)
    {
        var result = Evaluator.Run(Program(source));
        Assert.True(result.IsError, $"expected an arity failure for: {source}");
        return result.Error;
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        return error;
    }

    [Theory]
    [InlineData(
        "1.range(2, 3)",
        "range(1, 2, 3)",
        "range",
        3,
        "Callable `range(start, stop)` expects 2 arguments, but was called with 3 arguments.")]
    [InlineData(
        "9.atoms(1)",
        "atoms(9, 1)",
        "atoms",
        2,
        "Callable `atoms(value)` expects 1 argument, but was called with 2 arguments.")]
    [InlineData(
        "9.while",
        "while(9)",
        "while",
        1,
        "Callable `while(step, initialState)` expects 2 arguments, but was called with 1 argument.")]
    [InlineData(
        "9.repeat(1)",
        "repeat(9, 1)",
        "repeat",
        2,
        "Callable `repeat(step, count, initialState)` expects 3 arguments, but was called with 2 arguments.")]
    public void DotAndPlainSpellings_RenderTheSameSignatureFirstMessage(
        string dotSource,
        string plainSource,
        string builtinName,
        int actualArgumentCount,
        string expectedMessage)
    {
        foreach (var source in new[] { dotSource, plainSource })
        {
            var error = Fail(source);
            var message = KatLangError.FromEvalError(error).Message;
            Assert.Equal(expectedMessage, message);
            Assert.DoesNotContain("expects 0 parameter", message, StringComparison.Ordinal);

            // The structured leaf keeps the Lean-aligned placeholder payload:
            // Expected = 0 plus the real signature, identically in both spellings.
            var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
            Assert.Equal(0, arity.Expected);
            Assert.Equal(actualArgumentCount, arity.Actual);
            Assert.Equal(builtinName, arity.Signature?.Name);
        }
    }

    [Fact]
    public void SignaturelessStructuralProperty_KeepsReceiverSpecificWording()
    {
        // Positive control: a structural user-property arity failure carries no
        // signature, so the receiver-specific fallback wording must survive
        // signature-first rendering.
        var error = Fail(
            """
            Obj = {
              Inc(x) = x + 1
            }
            Obj.Inc
            """);

        Assert.Equal(
            "Property 'Inc' on `Obj` expects 1 parameter, but was called with 0 arguments.",
            KatLangError.FromEvalError(error).Message);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Null(arity.Signature);
    }

    [Fact]
    public void LegacyDotCallTextContext_WithSignature_UsesSignatureFirstRendering()
    {
        // Directly pin the compatibility branch: source evaluation emits the
        // structured DotCallContext above, while hosts may still construct the
        // legacy text-context form through EvalError.WithContext(string, ...).
        var structured = Fail("1.range(2, 3)");
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(structured));
        var legacy = new EvalError.WithContext(
            "while evaluating dotCall .range of 1",
            arity);

        Assert.Equal(
            "Callable `range(start, stop)` expects 2 arguments, but was called with 3 arguments.",
            KatLangError.FromEvalError(legacy).Message);
        Assert.Equal(0, arity.Expected);
    }
}
