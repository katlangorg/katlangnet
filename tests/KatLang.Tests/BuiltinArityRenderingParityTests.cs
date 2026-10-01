namespace KatLang.Tests;

/// <summary>
/// Builtin arity failures render SIGNATURE-FIRST in every call spelling: the
/// non-<c>if</c> builtins deliberately carry the Lean-aligned placeholder
/// <c>Expected = 0</c> beside their real <see cref="CallableSignature"/>, so
/// the dot-call formatter must never leak the sentinel as
/// "expects 0 parameters". The structured leaf payload is unchanged
/// (rendering-only fix; <see cref="IfBuiltinArityPayloadTests"/> pins the
/// <c>if</c> exception with <c>Expected = 3</c>); signatureless structural
/// user-property errors keep their receiver-specific wording. The expected count
/// is the builtin's arity CONTRACT (<see cref="BuiltinDescriptor.ArityFacts"/>, Lean
/// <c>builtinAcceptsArity</c> / <c>builtinArityDesc</c>): exact for a fixed-arity
/// builtin, a MINIMUM for the variadic-state loops — <c>repeat</c> accepts at least
/// 3 arguments and <c>while</c> at least 2, any further one being more initial
/// state — which the loops' runtime signature alone rendered as an exact count
/// (X-09, October 2026).
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
        "Callable `while(step, initialState)` expects at least 2 arguments, but was called with 1 argument.")]
    [InlineData(
        "9.repeat(1)",
        "repeat(9, 1)",
        "repeat",
        2,
        "Callable `repeat(step, count, initialState)` expects at least 3 arguments, but was called with 2 arguments.")]
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

    // ── X-09: the loops' minimum arity ─────────────────────────────────────────────────

    /// <summary>
    /// The registry's contract, checked against the INDEPENDENT oracle of Lean's
    /// <c>builtinAcceptsArity</c> / <c>builtinArityDesc</c> (written out here): the loops accept a
    /// minimum and describe it as one; every other builtin is exact, and its description, its
    /// acceptance and its rendered expectation agree.
    /// </summary>
    [Fact]
    public void TheArityContract_IsAMinimumForTheLoops_AndExactForEveryOtherBuiltin()
    {
        var repeat = BuiltinRegistry.GetBuiltin(BuiltinId.@repeat);
        var @while = BuiltinRegistry.GetBuiltin(BuiltinId.@while);
        Assert.Equal((3, (int?)null), (repeat.ArityFacts.MinTopLevelArgumentCount, repeat.ArityFacts.MaxTopLevelArgumentCount));
        Assert.Equal((2, (int?)null), (@while.ArityFacts.MinTopLevelArgumentCount, @while.ArityFacts.MaxTopLevelArgumentCount));
        Assert.Equal("at least 3", repeat.DescribeArity());
        Assert.Equal("at least 2", @while.DescribeArity());
        Assert.Null(repeat.FixedArity);
        Assert.Null(@while.FixedArity);
        foreach (var count in Enumerable.Range(0, 12))
        {
            Assert.Equal(count >= 3, repeat.AcceptsArity(count));
            Assert.Equal(count >= 2, @while.AcceptsArity(count));
        }

        foreach (var builtin in BuiltinRegistry.AllBuiltins.Where(static builtin => builtin.Id is not (BuiltinId.@repeat or BuiltinId.@while)))
        {
            var exact = Assert.IsType<int>(builtin.FixedArity);
            Assert.Equal((exact, (int?)exact), (builtin.ArityFacts.MinTopLevelArgumentCount, builtin.ArityFacts.MaxTopLevelArgumentCount));
            Assert.Equal(exact, builtin.PlainSignature.TopLevelParameterCount);
            foreach (var count in Enumerable.Range(0, 8))
                Assert.Equal(count == exact, builtin.AcceptsArity(count));
        }
    }

    /// <summary>
    /// Too few arguments for a loop name its MINIMUM — never an exact count — in every spelling and
    /// on every route, with the structured payload unchanged (<c>Expected = 0</c>, the written
    /// count, the runtime signature) and nothing evaluated: neither the step nor any written argument
    /// runs before the arity failure.
    /// </summary>
    [Theory]
    [InlineData("Step(s) = trace(s) + 1\nrepeat(Step, trace(3))", "repeat(step, count, initialState)", 3, 2)]
    [InlineData("Step(s) = trace(s) + 1\nrepeat(Step)", "repeat(step, count, initialState)", 3, 1)]
    [InlineData("repeat()", "repeat(step, count, initialState)", 3, 0)]
    [InlineData("repeat", "repeat(step, count, initialState)", 3, 0)]
    [InlineData("Step = { trace(9)\n  s + 1 }\nrepeat(Step, 3)", "repeat(step, count, initialState)", 3, 2)]
    [InlineData("Step(s) = trace(s) + 1\nStep.repeat(3)", "repeat(step, count, initialState)", 3, 2)]
    [InlineData("Step(s) = trace(s) + 1, false\nwhile(Step)", "while(step, initialState)", 2, 1)]
    [InlineData("while()", "while(step, initialState)", 2, 0)]
    [InlineData("Step(s) = trace(s) + 1, false\nStep.while", "while(step, initialState)", 2, 1)]
    public async Task TooFewLoopArguments_RenderTheMinimum_OnEveryRoute(string source, string signature, int minimum, int actual)
    {
        var expected = $"Callable `{signature}` expects at least {minimum} arguments, but was called with {actual} argument{(actual == 1 ? "" : "s")}.";

        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", observation.Kind);
        Assert.Empty(observation.HostCalls);
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith("ArityMismatch: ", error, StringComparison.Ordinal);
        Assert.Contains(expected, error, StringComparison.Ordinal);

        var operations = HostOperations.Create(HostOperation.Create("trace", static (args, _) => args[0], "x"));
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
        var result = Evaluator.Run(new Expr.AlgorithmExpr(parsed.Root), operations, limits: null, randomSeed: null, CancellationToken.None);
        Assert.True(result.IsError);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
        Assert.Equal(0, arity.Expected);
        Assert.Equal(actual, arity.Actual);
        Assert.Equal(signature, arity.Signature?.DisplayText);
    }

    /// <summary>The minimum and any longer initial state stay accepted, with their ordinary meaning.</summary>
    [Theory]
    [InlineData("Step(s) = trace(s) + 1\nrepeat(Step, 2, 0)", "2", new[] { "trace(0)", "trace(1)" })]
    [InlineData("Step(a, b) = a + 1, b * 2\nrepeat(Step, 3, 0, 1)", "S[3, 8]", new string[0])]
    [InlineData("Step(a, b, c) = a + 1, b * 2, c - 1\nrepeat(Step, 2, 0, 1, 10)", "S[2, 4, 8]", new string[0])]
    [InlineData("Step(s) = s + 1, s < 3\nwhile(Step, 0)", "3", new string[0])]
    [InlineData("Step(a, b) = a + 1, b * 2, a < 3\nwhile(Step, 0, 1)", "S[3, 8]", new string[0])]
    public async Task TheMinimumAndLongerInitialStates_StayAccepted(string source, string value, string[] hostCalls)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", observation.Kind);
        Assert.Equal(value, observation.Value);
        Assert.Equal(hostCalls, observation.HostCalls);
    }
}
