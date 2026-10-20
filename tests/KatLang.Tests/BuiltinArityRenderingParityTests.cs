namespace KatLang.Tests;

/// <summary>
/// Builtin arity failures render SIGNATURE-FIRST in every call spelling, and the
/// structured leaf carries the builtin's REAL arity contract beside its
/// <see cref="CallableSignature"/>: <c>Expected</c> is the fixed arity (Q-27 payload hygiene,
/// 2026-10-05: formerly a Lean-aligned placeholder 0 for every builtin but <c>if</c>, which
/// <see cref="IfBuiltinArityPayloadTests"/> pins), so no formatter can render "expects 0
/// parameters"; signatureless structural user-property errors keep their receiver-specific
/// wording. The expected count is the builtin's arity CONTRACT
/// (<see cref="BuiltinDescriptor.ArityFacts"/>, Lean <c>builtinAcceptsArity</c> /
/// <c>builtinArityDesc</c>), read from its one registry signature: every builtin is
/// fixed-arity, the loops <c>while(meta step)</c> (1) and <c>repeat(meta step, count)</c> (2)
/// included since META-S3-3 (the retired variadic-state minimum of X-09 is gone).
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

    /// <summary>The arity contract written out independently (Lean <c>builtinAcceptsArity</c>).</summary>
    private static readonly Dictionary<string, int> ContractMinimum = new()
    {
        ["range"] = 2,
        ["atoms"] = 1,
        ["while"] = 1,
        ["repeat"] = 2,
    };

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
        "9.while(1)",
        "while(9, 1)",
        "while",
        2,
        "Callable `while(meta step)` expects 1 argument, but was called with 2 arguments.")]
    [InlineData(
        "9.repeat(1, 2)",
        "repeat(9, 1, 2)",
        "repeat",
        3,
        "Callable `repeat(meta step, count)` expects 2 arguments, but was called with 3 arguments.")]
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

            // The structured leaf carries the real arity contract (Lean
            // `builtinMinimumArity`) plus the real signature, identically in both spellings.
            var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
            Assert.Equal(ContractMinimum[builtinName], arity.Expected);
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
        Assert.Equal(2, arity.Expected);
    }

    // ── META-S3-3: the loops are ordinary fixed-arity META builtins ─────────────────────

    /// <summary>
    /// The registry's contract, checked against the INDEPENDENT oracle of Lean's
    /// <c>builtinAcceptsArity</c> / <c>builtinArityDesc</c> (written out here): every builtin is exact
    /// — the loops <c>while(meta step)</c> and <c>repeat(meta step, count)</c> too — and its
    /// description, its acceptance, its signature and its rendered expectation agree.
    /// </summary>
    [Fact]
    public void TheArityContract_IsExactForEveryBuiltin_TheMetaLoopsIncluded()
    {
        var repeat = BuiltinRegistry.GetBuiltin(BuiltinId.@repeat);
        var @while = BuiltinRegistry.GetBuiltin(BuiltinId.@while);
        Assert.Equal("repeat(meta step, count)", repeat.PlainSignature.DisplayText);
        Assert.Equal("while(meta step)", @while.PlainSignature.DisplayText);
        Assert.Equal(("2", "1"), (repeat.DescribeArity(), @while.DescribeArity()));
        Assert.True(repeat.DeclaresMetaParameter && @while.DeclaresMetaParameter);
        foreach (var builtin in BuiltinRegistry.AllBuiltins)
        {
            var exact = builtin.FixedArity;
            Assert.Equal((exact, (int?)exact), (builtin.ArityFacts.MinTopLevelArgumentCount, builtin.ArityFacts.MaxTopLevelArgumentCount));
            Assert.Equal(exact, builtin.PlainSignature.TopLevelParameterCount);
            Assert.Equal(builtin.Id is BuiltinId.@while or BuiltinId.@repeat, builtin.DeclaresMetaParameter);
            foreach (var count in Enumerable.Range(0, 12))
                Assert.Equal(count == exact, builtin.AcceptsArity(count));
        }
    }

    /// <summary>
    /// A wrong number of loop arguments names the EXACT arity in every spelling and on every route,
    /// with the structured payload (<c>Expected</c> = that arity, the written count, the registry
    /// signature) and nothing evaluated: the arity gate precedes META capture, so neither the captured
    /// call, its arguments nor any other written argument runs. The retired spellings
    /// (<c>while(Step, 0)</c>, <c>Step.repeat(3, 0)</c>) are such failures.
    /// </summary>
    [Theory]
    [InlineData("Step(s) = trace(s) + 1\nrepeat(Step(trace(0)))", "repeat(meta step, count)", 2, 1)]
    [InlineData("Step(s) = trace(s) + 1\nrepeat(Step(trace(0)), trace(3), trace(4))", "repeat(meta step, count)", 2, 3)]
    [InlineData("repeat()", "repeat(meta step, count)", 2, 0)]
    [InlineData("repeat", "repeat(meta step, count)", 2, 0)]
    [InlineData("Step(s) = trace(s) + 1\nrepeat(Step, trace(3), 0)", "repeat(meta step, count)", 2, 3)]
    [InlineData("Step(s) = trace(s) + 1\nStep(trace(0)).repeat(3, trace(4))", "repeat(meta step, count)", 2, 3)]
    [InlineData("Step(s) = trace(s) + 1\nStep.repeat(3, 0)", "repeat(meta step, count)", 2, 3)]
    [InlineData("Step(s) = trace(s) + 1, false\nwhile(Step(trace(0)), trace(1))", "while(meta step)", 1, 2)]
    [InlineData("while()", "while(meta step)", 1, 0)]
    [InlineData("Step(s) = trace(s) + 1, false\nStep(trace(0)).while(trace(1))", "while(meta step)", 1, 2)]
    [InlineData("Step(s) = trace(s) + 1, false\nwhile(Step, 0)", "while(meta step)", 1, 2)]
    public async Task WrongLoopArgumentCounts_RenderTheExactArity_OnEveryRoute(string source, string signature, int minimum, int actual)
    {
        var expected = $"Callable `{signature}` expects {minimum} argument{(minimum == 1 ? "" : "s")}, but was called with {actual} argument{(actual == 1 ? "" : "s")}.";

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
        Assert.Equal(minimum, arity.Expected);
        Assert.Equal(actual, arity.Actual);
        Assert.Equal(signature, arity.Signature?.DisplayText);
    }

    /// <summary>The captured call's own arguments are the initial state, one or several slots.</summary>
    [Theory]
    [InlineData("Step(s) = trace(s) + 1\nrepeat(Step(0), 2)", "2", new[] { "trace(0)", "trace(1)" })]
    [InlineData("Step(a, b) = a + 1, b * 2\nrepeat(Step(0, 1), 3)", "S[3, 8]", new string[0])]
    [InlineData("Step(a, b, c) = a + 1, b * 2, c - 1\nrepeat(Step(0, 1, 10), 2)", "S[2, 4, 8]", new string[0])]
    [InlineData("Step(s) = s + 1, s < 3\nwhile(Step(0))", "3", new string[0])]
    [InlineData("Step(a, b) = a + 1, b * 2, a < 3\nwhile(Step(0, 1))", "S[3, 8]", new string[0])]
    public async Task TheCapturedCallsArguments_AreTheInitialState(string source, string value, string[] hostCalls)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", observation.Kind);
        Assert.Equal(value, observation.Value);
        Assert.Equal(hostCalls, observation.HostCalls);
    }
}
