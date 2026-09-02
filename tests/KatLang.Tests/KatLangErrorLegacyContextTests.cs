namespace KatLang.Tests;

/// <summary>
/// Batch 3 / L8 — legacy host prose contexts render through the SAME per-shape
/// message builders as structured contexts.
///
/// <para>Source evaluation always emits structured <see cref="ErrorContext"/>s. Hosts,
/// however, may still construct <see cref="EvalError.WithContext"/> with the historical
/// prose (<c>"while evaluating property P"</c>, <c>"while evaluating call to F"</c>,
/// <c>"while evaluating dotCall .M of R"</c>), and <see cref="KatLangError.FromEvalError"/>
/// recognizes exactly those three prefixes for the unknown-name, missing-output, and
/// arity-mismatch shapes. Recognition yields only the shape's payload; the message
/// comes from the one builder that shape has, so the structured and the legacy
/// construction can never drift. Structured classification (<see cref="KatLangError.Code"/>,
/// <see cref="KatLangError.Source"/>) is untouched by the text form.</para>
///
/// <para>The former <c>"Builtin '..."</c> arm, which echoed such a context verbatim,
/// had no producer (builtin arity is a parser diagnostic, never an evaluation
/// context) and no contract, and is gone: that prose is ordinary host context now.</para>
/// </summary>
public class KatLangErrorLegacyContextTests
{
    private static string Render(EvalError error) => KatLangError.FromEvalError(error).Message;

    private static SourceSpan AnySpan()
        => SourceProvenance.ParseValid("1 + 2").Root.Output[0].Span
            ?? throw new InvalidOperationException("Parsed expressions carry spans.");

    private static EvalError.ArityMismatch SignatureBearingArity()
    {
        // A builtin arity failure carries the callable signature (and the
        // Lean-aligned placeholder Expected = 0), so signature-first rendering
        // must win over the raw counts in both construction paths.
        var arity = SourceProvenance.ParseValid("1.range(2, 3)").ExpectEvaluationError<EvalError.ArityMismatch>();
        Assert.NotNull(arity.Signature);
        return arity;
    }

    // ── Exact supported messages for host-constructed legacy contexts ───────

    [Fact]
    public void DotCallUnknownName_LegacyContext_RendersTheDotCallMessage()
    {
        const string expected = "Property 'Foo' was not found on `Obj`, and no visible algorithm or property named 'Foo' can be used with `Obj` as the first argument.";
        Assert.Equal(
            expected,
            Render(new EvalError.WithContext(new DotCallContext("Obj", "Foo"), new EvalError.UnknownName("Foo"))));
        Assert.Equal(
            expected,
            Render(new EvalError.WithContext("while evaluating dotCall .Foo of Obj", new EvalError.UnknownName("Foo"))));

        // A receiver description may itself contain " of ": the FIRST delimiter
        // after the prefix splits the member from the receiver.
        Assert.Equal(
            "Property 'Foo' was not found on `Obj of Things`, and no visible algorithm or property named 'Foo' can be used with `Obj of Things` as the first argument.",
            Render(new EvalError.WithContext("while evaluating dotCall .Foo of Obj of Things", new EvalError.UnknownName("Foo"))));

        // The missing name must be the member: otherwise the unknown name is an
        // ordinary inner failure under an ordinary context.
        Assert.Equal(
            "while evaluating dotCall .Foo of Obj: Unknown name: Bar",
            Render(new EvalError.WithContext("while evaluating dotCall .Foo of Obj", new EvalError.UnknownName("Bar"))));
    }

    [Fact]
    public void MissingOutput_LegacyContexts_RenderTheMissingOutputMessages()
    {
        Assert.Equal(
            "Property 'P' has no defined output.\nAdd an output expression to 'P', or use `()` if the empty sequence value was intended. To use one of its properties, write `P.X`.",
            Render(new EvalError.WithContext("while evaluating property P", new EvalError.MissingOutput())));
        Assert.Equal(
            "Cannot call 'F' because it has no defined output.\nAdd an output expression, or use `()` if the empty sequence value was intended. To call one of its properties, use property access instead.",
            Render(new EvalError.WithContext("while evaluating call to F", new EvalError.MissingOutput())));
        Assert.Equal(
            "The value `Obj.M` has no defined output.\nAdd an output expression, or use `()` if the empty sequence value was intended. To use one of its properties, access it explicitly.",
            Render(new EvalError.WithContext("while evaluating dotCall .M of Obj", new EvalError.MissingOutput())));

        // The dot-only `string` intrinsic renders receiver-only.
        Assert.Equal(
            "Property 'x' has no defined output.\nAdd an output expression to 'x', or use `()` if the empty sequence value was intended. To use one of its properties, write `x.X`.",
            Render(new EvalError.WithContext("while evaluating dotCall .string of x", new EvalError.MissingOutput())));
    }

    [Fact]
    public void ArityMismatch_LegacyContexts_RenderTheArityMessages()
    {
        Assert.Equal(
            "Property 'P' expects 2 parameters, but was called with 1 argument.",
            Render(new EvalError.WithContext("while evaluating property P", new EvalError.ArityMismatch(2, 1))));

        // Call context: a bare-name callee reads as a property, a rendered
        // expression as an algorithm, and a spanned mismatch as the generic form.
        Assert.Equal(
            "Property 'F' expects 2 parameters, but was called with 1 argument.",
            Render(new EvalError.WithContext("while evaluating call to F", new EvalError.ArityMismatch(2, 1))));
        Assert.Equal(
            "Algorithm `a.b` expects 2 parameters, but was called with 1 argument.",
            Render(new EvalError.WithContext("while evaluating call to a.b", new EvalError.ArityMismatch(2, 1))));
        Assert.Equal(
            "Expected 2 parameters, but was called with 1 argument.",
            Render(new EvalError.WithContext("while evaluating call to F", new EvalError.ArityMismatch(2, 1) { Span = AnySpan() })));

        // Dot-call context: signature first, then the receiver-specific
        // signatureless form, then the generic spanned form.
        Assert.Equal(
            "Callable `range(start, stop)` expects 2 arguments, but was called with 3 arguments.",
            Render(new EvalError.WithContext("while evaluating dotCall .range of 1", SignatureBearingArity())));
        Assert.Equal(
            "Property 'M' on `Obj` expects 1 parameter, but was called with 0 arguments.",
            Render(new EvalError.WithContext("while evaluating dotCall .M of Obj", new EvalError.ArityMismatch(1, 0))));
        Assert.Equal(
            "Expected 1 parameter, but was called with 0 arguments.",
            Render(new EvalError.WithContext("while evaluating dotCall .M of Obj", new EvalError.ArityMismatch(1, 0) { Span = AnySpan() })));
    }

    [Theory]
    [InlineData(0, 0, "0 parameters", "0 arguments")]
    [InlineData(1, 1, "1 parameter", "1 argument")]
    [InlineData(2, 2, "2 parameters", "2 arguments")]
    public void ArityMismatch_CountBoundaries_AgreeForStructuredAndLegacyContexts(
        int expected,
        int actual,
        string expectedCount,
        string actualCount)
    {
        var expectedMessage = $"Property 'P' expects {expectedCount}, but was called with {actualCount}.";
        Assert.Equal(
            expectedMessage,
            Render(new EvalError.WithContext(new PropertyEvaluationContext("P"), new EvalError.ArityMismatch(expected, actual))));
        Assert.Equal(
            expectedMessage,
            Render(new EvalError.WithContext("while evaluating property P", new EvalError.ArityMismatch(expected, actual))));
    }

    // ── One builder per shape: structured and legacy agree byte-for-byte ────

    public static IEnumerable<object[]> ShapePairs()
    {
        var span = AnySpan();
        var signatureArity = SignatureBearingArity();

        yield return Pair(
            "dot-call unknown name",
            new EvalError.WithContext(new DotCallContext("Obj", "Foo"), new EvalError.UnknownName("Foo")),
            new EvalError.WithContext("while evaluating dotCall .Foo of Obj", new EvalError.UnknownName("Foo")));
        yield return Pair(
            "property missing output",
            new EvalError.WithContext(new PropertyEvaluationContext("P"), new EvalError.MissingOutput()),
            new EvalError.WithContext("while evaluating property P", new EvalError.MissingOutput()));
        yield return Pair(
            "call missing output",
            new EvalError.WithContext(new CallContext("F"), new EvalError.MissingOutput()),
            new EvalError.WithContext("while evaluating call to F", new EvalError.MissingOutput()));
        yield return Pair(
            "dot-call missing output",
            new EvalError.WithContext(new DotCallContext("Obj", "M"), new EvalError.MissingOutput()),
            new EvalError.WithContext("while evaluating dotCall .M of Obj", new EvalError.MissingOutput()));
        yield return Pair(
            "dot-call string intrinsic missing output",
            new EvalError.WithContext(new DotCallContext("x", "string"), new EvalError.MissingOutput()),
            new EvalError.WithContext("while evaluating dotCall .string of x", new EvalError.MissingOutput()));
        yield return Pair(
            "property arity",
            new EvalError.WithContext(new PropertyEvaluationContext("P"), new EvalError.ArityMismatch(2, 1)),
            new EvalError.WithContext("while evaluating property P", new EvalError.ArityMismatch(2, 1)));
        yield return Pair(
            "call arity (bare name)",
            new EvalError.WithContext(new CallContext("F"), new EvalError.ArityMismatch(2, 1)),
            new EvalError.WithContext("while evaluating call to F", new EvalError.ArityMismatch(2, 1)));
        yield return Pair(
            "call arity (rendered expression)",
            new EvalError.WithContext(new CallContext("a.b"), new EvalError.ArityMismatch(2, 1)),
            new EvalError.WithContext("while evaluating call to a.b", new EvalError.ArityMismatch(2, 1)));
        yield return Pair(
            "call arity (spanned)",
            new EvalError.WithContext(new CallContext("F"), new EvalError.ArityMismatch(2, 1) { Span = span }),
            new EvalError.WithContext("while evaluating call to F", new EvalError.ArityMismatch(2, 1) { Span = span }));
        yield return Pair(
            "dot-call arity (signatureless)",
            new EvalError.WithContext(new DotCallContext("Obj", "M"), new EvalError.ArityMismatch(1, 0)),
            new EvalError.WithContext("while evaluating dotCall .M of Obj", new EvalError.ArityMismatch(1, 0)));
        yield return Pair(
            "dot-call arity (spanned)",
            new EvalError.WithContext(new DotCallContext("Obj", "M"), new EvalError.ArityMismatch(1, 0) { Span = span }),
            new EvalError.WithContext("while evaluating dotCall .M of Obj", new EvalError.ArityMismatch(1, 0) { Span = span }));
        yield return Pair(
            "dot-call arity (signature-bearing)",
            new EvalError.WithContext(new DotCallContext("1", "range"), signatureArity),
            new EvalError.WithContext("while evaluating dotCall .range of 1", signatureArity));

        static object[] Pair(string shape, EvalError structured, EvalError legacy) => [shape, structured, legacy];
    }

    [Theory]
    [MemberData(nameof(ShapePairs))]
    public void StructuredAndLegacyConstruction_RenderIdenticalMessages(string shape, EvalError structured, EvalError legacy)
    {
        Assert.Equal(Render(structured), Render(legacy));

        // The text form changes rendering only, never classification.
        var structuredFacade = KatLangError.FromEvalError(structured);
        var legacyFacade = KatLangError.FromEvalError(legacy);
        Assert.Equal(structuredFacade.Code, legacyFacade.Code);
        Assert.Same(legacy, legacyFacade.Source);
        Assert.NotEqual(KatLangErrorCode.Unspecified, legacyFacade.Code);
        Assert.NotEmpty(shape);
    }

    // ── The compatibility parser does not broaden ────────────────────────────

    [Theory]
    [InlineData("While evaluating property P")]
    [InlineData(" while evaluating property P")]
    [InlineData("while evaluating properties P")]
    [InlineData("while evaluating property")]
    [InlineData("while evaluating propert")]
    [InlineData("while evaluating call toF")]
    [InlineData("while evaluating call to")]
    [InlineData("while evaluating dotCall .M")]
    [InlineData("while evaluating dotCall .M of")]
    [InlineData("while evaluating dotCall M of Obj")]
    [InlineData("evaluating property P")]
    [InlineData("while evaluating property P and more")]
    [InlineData("Builtin 'if' expects 3 arguments: condition, whenTrue, whenFalse. Got 2.")]
    [InlineData("please retry")]
    public void UnrecognizedProse_StaysOrdinaryHostContext(string context)
    {
        // Near-miss prefixes, truncated prefixes, and unrelated prose are ordinary
        // host contexts: the inner error renders generically after the context.
        // (The "property P and more" row is genuinely a property context whose
        // NAME is the rest of the text — the parser takes the remainder verbatim —
        // so it is asserted separately below.)
        if (context.StartsWith("while evaluating property ", StringComparison.Ordinal))
        {
            Assert.Equal(
                "Property 'P and more' expects 2 parameters, but was called with 1 argument.",
                Render(new EvalError.WithContext(context, new EvalError.ArityMismatch(2, 1))));
            return;
        }

        Assert.Equal(
            $"{context}: Algorithm has no defined output.\nAdd an output expression, or use `()` if the empty sequence value was intended.",
            Render(new EvalError.WithContext(context, new EvalError.MissingOutput())));
        Assert.Equal(
            $"{context}: Expected 2 parameters, but was called with 1 argument.",
            Render(new EvalError.WithContext(context, new EvalError.ArityMismatch(2, 1))));
        Assert.Equal(
            $"{context}: Unknown name: M",
            Render(new EvalError.WithContext(context, new EvalError.UnknownName("M"))));
    }

    [Fact]
    public void RecognizedContexts_ApplyOnlyToTheirShapes()
    {
        // A recognized prefix with an inner error of another family stays generic:
        // recognition is per (prefix, shape), not per prefix.
        Assert.Equal(
            "while evaluating property P: Division by zero",
            Render(new EvalError.WithContext("while evaluating property P", new EvalError.DivByZero())));
        Assert.Equal(
            "while evaluating call to F: Unknown name: G",
            Render(new EvalError.WithContext("while evaluating call to F", new EvalError.UnknownName("G"))));
        Assert.Equal(
            "while evaluating dotCall .M of Obj: Type mismatch: msg",
            Render(new EvalError.WithContext("while evaluating dotCall .M of Obj", new EvalError.TypeMismatch("msg"))));
        Assert.Equal(
            "while evaluating property P: Evaluation step limit of 7 was exceeded",
            Render(new EvalError.WithContext("while evaluating property P", new EvalError.EvaluationStepLimitExceeded(7))));
    }
}
