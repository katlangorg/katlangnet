using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// X-23: the loop-state <see cref="EvalError.ArityMismatch"/> must tell the truth. When the loop's
/// state binding finds NO parameter of the step to bind a state value to, the structured error is
/// <c>WithContext(LoopStateBindingContext(loop, [], n), ArityMismatch(0, n))</c>. The message once
/// explained that shape as "because the step has no parameters"; it now states only the binding fact —
/// the loop found no step parameter to bind the state to — and never what the step is.
/// <para>Q-23 (decided October 2026): a clause family, a builtin, and an alias or forwarded parameter of
/// either are ORDINARY callables invoked over the state supply (LOOP-08), so they no longer reach this
/// shape at all — their former rows here are the positive cases of
/// <see cref="LoopStepCallableDispatchTests"/>. Only a genuinely zero-parameter callable supplied a
/// non-empty state still reaches it (its ordinary arity, through the user binder).</para>
/// <para>Q-06 (decided 2026-10-05): a value with no CALLABLE identity (NEED-06) is not a step at all —
/// it no longer shares the zero-parameter shape: the iteration that needs it reports
/// <see cref="EvalError.NotAnAlgorithm"/> ("The repeat step is not callable"), positioned at the step
/// argument, by CALLABLE projection alone. Rendered-message-only coverage: no Lean counterpart (the
/// structured kind and its payload are what Lean models).</para>
/// </summary>
public class LoopStepUnboundStateMessageTests
{
    private const string FalseClaim = "has no parameters";

    /// <summary>
    /// Every step category the loop's state binding finds no parameter of — a callable whose
    /// parameter interface accepts no supplied state value — the loop, the number of state values,
    /// and the evaluation frames that enclose the loop-state frame (outermost first).
    /// </summary>
    public static TheoryData<string, string, string, int, string[]> NoBindableStepParameter() => new()
    {
        // zero-parameter user algorithms
        { "zero-parameter property", "Z = 5\nrepeat(Z, 1, 1)", "repeat", 1, ["while evaluating call to repeat"] },
        { "zero-parameter block", "repeat({ 1 }, 1, 1)", "repeat", 1, ["while evaluating call to repeat"] },
        { "zero-parameter property, while", "Z = true\nwhile(Z, 1)", "while", 1, ["while evaluating call to while"] },
        { "nested step whose names were captured", "Outer(x) = {\n  Step = x + 1\n  repeat(Step, 2, x)\n}\nOuter(1)", "repeat", 1, ["while evaluating call to Outer", "while evaluating call to repeat"] },
        // (Q-23: clause families, builtins, and aliases or forwarded parameters of either are ordinary
        // callables and never reach this shape — see FormerlyUnboundStepCategories below.)
        // zero-parameter prelude members
        { "zero-parameter Math member", "repeat(pi, 1, 1)", "repeat", 1, ["while evaluating call to repeat"] },
        { "zero-parameter host operation", "repeat(tick, 1, 1)", "repeat", 1, ["while evaluating call to repeat"] },
        // (Q-06: a value with no CALLABLE identity is not a step at all — see NoCallableIdentityStep.)
    };

    /// <summary>
    /// Every step argument with no CALLABLE identity (NEED-06), the loop, the 1-based column of the
    /// step argument on the last source line, and the evaluation frames that enclose the verdict.
    /// </summary>
    public static TheoryData<string, string, string, int, string[]> NoCallableIdentityStep() => new()
    {
        { "number", "repeat(5, 1, 1)", "repeat", 8, ["while evaluating call to repeat"] },
        { "number, while", "while(5, 1)", "while", 7, ["while evaluating call to while"] },
        { "string", "repeat('a', 1, 1)", "repeat", 8, ["while evaluating call to repeat"] },
        { "Boolean", "repeat(true, 1, 1)", "repeat", 8, ["while evaluating call to repeat"] },
        { "list", "repeat([1, 2], 1, 1)", "repeat", 8, ["while evaluating call to repeat"] },
        { "sequence", "repeat((1, 2), 1, 1)", "repeat", 8, ["while evaluating call to repeat"] },
        { "empty sequence", "repeat((), 1, 1)", "repeat", 8, ["while evaluating call to repeat"] },
        { "operator result", "repeat(2 + 3, 1, 1)", "repeat", 8, ["while evaluating call to repeat"] },
        { "call result", "Inc(x) = x + 1\nrepeat(Inc(1), 1, 1)", "repeat", 8, ["while evaluating call to repeat"] },
        { "selection", "A = 1, 2\nrepeat(A:0, 1, 1)", "repeat", 8, ["while evaluating call to repeat"] },
        { "dot-call value", "A = 3\nrepeat(A.abs, 1, 1)", "repeat", 8, ["while evaluating call to repeat"] },
        { "value forwarded through a parameter", "Run(s) = repeat(s, 1, 1)\nRun(5)", "repeat", 5, ["while evaluating call to Run", "while evaluating call to repeat"] },
    };

    private static string NotCallableSentence(string loop)
        => $"The {loop} step is not callable: the argument supplied for it is a value, not an algorithm. "
            + "Pass an algorithm: a named algorithm, a builtin, or a block { ... }.";

    [Theory]
    [MemberData(nameof(NoCallableIdentityStep))]
    public async Task NoCallableIdentityStep_IsNotAnAlgorithm_OnEveryRoute(string category, string source, string loop, int column, string[] frames)
    {
        _ = column;
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);

        Assert.Equal("err", observation.Kind);
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith($"{KatLangErrorCode.NotAnAlgorithm}: {string.Join(": ", frames)}: {NotCallableSentence(loop)}", error, StringComparison.Ordinal);

        // Never the loop-state binding shape a callable reaches, and never a value demand.
        Assert.DoesNotContain("found no step parameter", error, StringComparison.Ordinal);
        Assert.DoesNotContain("binding", error, StringComparison.Ordinal);
        Assert.Empty(observation.HostCalls);
        Assert.False(string.IsNullOrEmpty(category));
    }

    [Theory]
    [MemberData(nameof(NoCallableIdentityStep))]
    public async Task NoCallableIdentityStep_IsPositionedAtTheStepArgument(string category, string source, string loop, int column, string[] frames)
    {
        _ = (category, frames);
        var lastLine = source.Split('\n').Length;
        foreach (var (route, error) in await ErrorsOnEveryRouteAsync(source))
        {
            Assert.Equal(KatLangErrorCode.NotAnAlgorithm, error.Code);
            var inner = Assert.IsAssignableFrom<EvalError>(error.Source);
            while (inner is EvalError.WithContext withContext)
                inner = withContext.Inner;
            var notAnAlgorithm = Assert.IsType<EvalError.NotAnAlgorithm>(inner);
            Assert.Equal($"{loop} step", notAnAlgorithm.Description);
            Assert.True(new SourcePosition(lastLine, column) == error.Span?.Start, $"{route}: {error.Span}");
        }
    }

    private static string ExpectedSentence(string loop, int stateValues)
        => $"`{loop}` cannot bind the current loop state to its step: the current loop state has "
            + (stateValues == 1 ? "1 state value" : $"{stateValues} state values")
            + $", but the loop found no step parameter to bind {(stateValues == 1 ? "it" : "them")} to.";

    [Theory]
    [MemberData(nameof(NoBindableStepParameter))]
    public async Task NoBindableStepParameter_IsReportedTruthfully_OnEveryRoute(string category, string source, string loop, int stateValues, string[] frames)
    {
        _ = frames;
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);

        Assert.Equal("err", observation.Kind);
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith($"{KatLangErrorCode.ArityMismatch}: ", error, StringComparison.Ordinal);
        Assert.Contains(ExpectedSentence(loop, stateValues), error, StringComparison.Ordinal);

        // Never the false claim, never a count the step is said to "expect", and never a
        // description of the step as a zero-parameter callable — whatever the category.
        Assert.DoesNotContain(FalseClaim, error, StringComparison.Ordinal);
        Assert.DoesNotContain("step expects 0", error, StringComparison.Ordinal);
        Assert.DoesNotContain("zero-parameter", error, StringComparison.Ordinal);
        Assert.False(string.IsNullOrEmpty(category));
    }

    /// <summary>The structured error of every route, unwrapped from the engine facade where needed.</summary>
    private static async Task<IReadOnlyList<(string Route, KatLangError Error)>> ErrorsOnEveryRouteAsync(string source)
    {
        static HostOperations Operations(bool suspending)
            => suspending
                ? HostOperations.Create(
                    HostOperation.CreateAsync("tick", async (_, _) => { await Task.Yield(); return new Result.Atom(1); }),
                    HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return args[0]; }, "x"))
                : HostOperations.Create(
                    HostOperation.Create("tick", (_, _) => new Result.Atom(1)),
                    HostOperation.Create("trace", (args, _) => args[0], "x"));

        static KatLangError Failure(RunResult result)
            => Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);

        var errors = new List<(string, KatLangError)>
        {
            ("EngineSync", Failure(KatLangEngine.Run(source, new RunOptions { HostOperations = Operations(false) }))),
            ("EngineAsync", Failure(await KatLangEngine.RunAsync(source, new RunOptions { HostOperations = Operations(false) }))),
            ("EngineAsyncTwin", Failure(await KatLangEngine.RunAsync(source, new RunOptions { HostOperations = Operations(true) }))),
        };

        // The evaluator routes parse with the same host operations the engines see.
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = Operations(false) });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
        var program = new Expr.AlgorithmExpr(parsed.Root);
        foreach (var (route, optimize) in new[] { ("Generic", false), ("Optimized", true) })
        {
            var (result, _) = Evaluator.RunCountedObserved(program, enableOptimizations: optimize, hostOperations: Operations(false));
            Assert.True(result.IsError, route);
            errors.Add((route, KatLangError.FromEvalError(result.Error)));
        }

        var (twin, _) = await Evaluator.RunCountedObservedAsync(
            program,
            zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
            hostOperations: Operations(true));
        Assert.True(twin.IsError);
        errors.Add(("ForcedTwin", KatLangError.FromEvalError(twin.Error)));
        return errors;
    }

    [Theory]
    [MemberData(nameof(NoBindableStepParameter))]
    public async Task NoBindableStepParameter_KeepsTheStructuredErrorUnchanged(string category, string source, string loop, int stateValues, string[] frames)
    {
        _ = category;
        foreach (var (route, error) in await ErrorsOnEveryRouteAsync(source))
        {
            Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
            Assert.NotNull(error.Span);

            // The frames, outermost first, end in the loop-state frame around the binder's
            // ArityMismatch(0, n): the payload this rendering change leaves untouched.
            var contexts = new List<ErrorContext>();
            var current = Assert.IsAssignableFrom<EvalError>(error.Source);
            while (current is EvalError.WithContext withContext)
            {
                contexts.Add(withContext.ErrorContext);
                current = withContext.Inner;
            }

            Assert.Equal([.. frames, $"while binding {loop} step state"], contexts.Select(static context => context.ToString()));
            var state = Assert.IsType<LoopStateBindingContext>(contexts[^1]);
            Assert.Equal(loop, state.LoopName);
            Assert.Empty(state.StepParameterNames);
            Assert.Equal(stateValues, state.ActualStateValueCount);

            var arity = Assert.IsType<EvalError.ArityMismatch>(current);
            Assert.Equal((0, stateValues), (arity.Expected, arity.Actual));
            Assert.Null(arity.Signature);
            Assert.Null(arity.AcceptedArity);
            Assert.True(arity.InferredImplicitParameters is null or { Count: 0 }, route);
        }
    }

    [Fact]
    public void Message_ForAZeroParameterStep_IsPinnedVerbatim()
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("Z = 5\nrepeat(Z, 2, 1)"));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
        Assert.Equal(new SourceSpan(2, 1, 2, 16), error.Span);
        Assert.Equal(
            "while evaluating call to repeat: `repeat` cannot bind the current loop state to its step: the current loop state "
            + "has 1 state value, but the loop found no step parameter to bind it to. Loop state values are bound positionally to "
            + "the step's parameters. If this is a nested step with inferred parameters, remember that names already bound by an enclosing algorithm are "
            + "captured, not added as step parameters; use a distinct state-slot name such as `candidate` when threading an outer "
            + "value through the loop state.",
            error.Message);
    }

    [Fact]
    public void Message_ForANonCallableValueStep_IsPinnedVerbatim()
    {
        // Q-06: the call result `F(1)` has no CALLABLE identity — it is not a step, whatever it
        // would evaluate to; nothing evaluates it to find that out.
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("F(0) = 5\nF(n) = n * 10\nrepeat(F(1), 2, 1)"));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.NotAnAlgorithm, error.Code);
        Assert.Equal(new SourceSpan(3, 8, 3, 12), error.Span);
        Assert.Equal(
            "while evaluating call to repeat: The repeat step is not callable: the argument supplied for it is a value, "
            + "not an algorithm. Pass an algorithm: a named algorithm, a builtin, or a block { ... }.",
            error.Message);
    }

    [Theory]
    [InlineData("repeat", 1, "it")]
    [InlineData("while", 2, "them")]
    [InlineData("repeat", 3, "them")]
    public void Renderer_DescribesTheUnlabelledShapeByTheBindingFactOnly(string loop, int stateValues, string pronoun)
    {
        // The renderer alone, over a host-constructed payload: it reads nothing but the payload, so
        // the same text serves every step category and every future loop-step contract (Q-23).
        var message = KatLangError.FromEvalError(new EvalError.WithContext(
            new LoopStateBindingContext(loop, [], stateValues),
            new EvalError.ArityMismatch(0, stateValues))).Message;

        Assert.StartsWith(ExpectedSentence(loop, stateValues), message, StringComparison.Ordinal);
        Assert.Contains($"to bind {pronoun} to.", message, StringComparison.Ordinal);
        Assert.Contains("Loop state values are bound positionally to the step's parameters.", message, StringComparison.Ordinal);
        Assert.DoesNotContain(FalseClaim, message, StringComparison.Ordinal);
    }

    // ── Labelled shapes describe their binding facts, without guessing declaration syntax ───

    [Theory]
    [InlineData("Step(x) = x + 1\nrepeat(Step, 2, 1, 2)",
        "`repeat` step expects 1 state value for 1 parameter 'x', but the current loop state has 2 state values. Loop state values are bound positionally to the step's parameters.")]
    [InlineData("Step(x) = x + 1\nA = Step\nrepeat(A, 2, 1, 2)",
        "`repeat` step expects 1 state value for 1 parameter 'x', but the current loop state has 2 state values. Loop state values are bound positionally to the step's parameters.")]
    [InlineData("Step(a, b) = a + b, b\nrepeat(Step, 2, 1)",
        "`repeat` step expects 2 state values for 2 parameters 'a' and 'b', but the current loop state has 1 state value. Loop state values are bound positionally to the step's parameters.")]
    [InlineData("Step((x, y)) = (y, x + y)\nrepeat(Step, 3, 1, 1)",
        "`repeat` step expects 1 state value for 1 parameter '(x, y)', but the current loop state has 2 state values. Loop state values are bound positionally to the step's parameters.")]
    [InlineData("Head2(x, y, *rest) = x, y\nrepeat(Head2, 1, 1)",
        "`repeat` variadic step expects at least 2 state values for fixed parameter(s) 'x' and 'y', but the current loop state has 1 state value.")]
    public async Task LabelledShapes_DescribeTheirParameterCounts(string source, string expected)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith($"{KatLangErrorCode.ArityMismatch}: while evaluating call to repeat: {expected}", error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("Step(x) = x + 1\nrepeat(Step, 1, 1, 2)")]
    [InlineData("Step = x + 1\nrepeat(Step, 1, 1, 2)")]
    [InlineData("Step((x, y)) = x + y\nrepeat(Step, 1, 1, 2)")]
    [InlineData("Step(x, y, *rest) = x\nrepeat(Step, 1, 1)")]
    [InlineData("Outer(x) = {\n  Step(x) = x + 1\n  repeat(Step, 1, x, x)\n}\nOuter(3)")]
    public async Task BindingExplanation_DoesNotClaimTheParametersWereInferred(string source)
    {
        // Written and inferred step heads share the state-binding renderer. An explicit nested
        // Step(x) shadows Outer(x); only an inferred step captures that existing binding.
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", observation.Kind);
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith($"{KatLangErrorCode.ArityMismatch}:", error, StringComparison.Ordinal);
        Assert.DoesNotContain("implicit parameters", error, StringComparison.Ordinal);
        if (!error.Contains("variadic step", StringComparison.Ordinal))
            Assert.Contains("If this is a nested step with inferred parameters, remember", error, StringComparison.Ordinal);
    }

    // ── Q-23: the formerly unbound step categories are ordinary callables ───────────────────────

    /// <summary>
    /// The rows this suite pinned as unbound until Q-23 was decided: each is now the ordinary invocation
    /// of a callable — a value, or the callee's own ordinary failure — and never the unbound-step
    /// message. The full category matrix is <see cref="LoopStepCallableDispatchTests"/>.
    /// </summary>
    [Theory]
    [InlineData("clause family", "F(0) = 5\nF(n) = n * 10\nrepeat(F, 2, 1)", "ok 100")]
    [InlineData("clause family, while", "S(0) = 1, false\nS(n) = n + 1, n < 3\nwhile(S, 0)", "ok 0")]
    [InlineData("unnameable clause family", "G(0) = 0\nG(1) = 1\nrepeat(G, 1, 0)", "ok 0")]
    [InlineData("clause family with two parameters", "T(0, b) = b\nT(a, b) = a + b\nrepeat(T, 1, 1, 2)", "ok 3")]
    [InlineData("clause family with different clause kinds", "H(0) = 1\nH([x]) = x\nrepeat(H, 1, 0)", "ok 1")]
    [InlineData("fluent clause family step", "F(0) = 5\nF(n) = n * 10\nF.repeat(2, 1)", "ok 100")]
    [InlineData("clause family forwarded through a parameter", "F(0) = 5\nF(n) = n * 10\nRun(s) = repeat(s, 2, 1)\nRun(F)", "ok 100")]
    [InlineData("alias of a clause family", "F(0) = 5\nF(n) = n * 10\nW = F\nrepeat(W, 2, 1)", "ok 100")]
    [InlineData("alias chain to a clause family", "F(0) = 5\nF(n) = n * 10\nW = F\nV = W\nrepeat(V, 2, 1)", "ok 100")]
    [InlineData("alias of a builtin", "C = count\nrepeat(C, 1, [1, 2])", "ok 2")]
    [InlineData("alias chain to a builtin", "C = count\nD = C\nrepeat(D, 1, [1, 2])", "ok 2")]
    [InlineData("builtin", "repeat(count, 1, [1, 2])", "ok 2")]
    [InlineData("builtin, while", "while(count, [1, 2])", "err TypeMismatch")]
    [InlineData("callback-taking builtin", "repeat(map, 1, [1, 2], [3])", "err NotAnAlgorithm")]
    [InlineData("if", "repeat(if, 1, true, 1, 2)", "ok 1")]
    [InlineData("a loop builtin", "repeat(while, 1, 1, 2)", "err NotAnAlgorithm")]
    [InlineData("fluent builtin step", "sum.repeat(1, [1, 2])", "ok 3")]
    [InlineData("builtin forwarded through a parameter", "Run(s) = repeat(s, 1, [1, 2])\nRun(count)", "ok 2")]
    public async Task FormerlyUnboundStepCategories_AreOrdinaryCallables(string category, string source, string expected)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        if (expected.StartsWith("ok ", StringComparison.Ordinal))
        {
            Assert.True(observation.Kind == "ok", $"{category}: {observation}");
            Assert.Equal(expected[3..], observation.Value);
            return;
        }

        // An ordinary failure of the invoked callable: `while(count, …)`'s numeric result is the flag;
        // `map`'s callback slot holds a list and the inner `while` gets a value as ITS step — neither
        // has CALLABLE identity, so each is the invoked builtin's own NotAnAlgorithm (Q-06).
        Assert.Equal("err", observation.Kind);
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith(expected[4..] + ": ", error, StringComparison.Ordinal);
        Assert.DoesNotContain("found no step parameter", error, StringComparison.Ordinal);
    }

    // ── Steps that bound before Q-23 are unchanged ──────────────────────────────────────────────

    [Theory]
    [InlineData("F(0) = 5\nF(n) = n * 10\nWrap(n) = F(n)\nrepeat(Wrap, 2, 1)", "100")]
    [InlineData("repeat(abs, 2, -3)", "3")]
    [InlineData("repeat(Math.Abs, 1, -2)", "2")]
    [InlineData("A = abs\nrepeat(A, 1, -2)", "2")]
    [InlineData("Lib = { public Step(x) = x + 1 }\nrepeat(Lib.Step, 2, 0)", "2")]
    [InlineData("Coll(*xs) = xs.count\nrepeat(Coll, 1, 1, 2)", "2")]
    [InlineData("Step = x + 1\nrepeat(Step, 3, 0)", "3")]
    public async Task AcceptedSteps_AreUnchanged(string source, string expected)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal(("ok", expected), (observation.Kind, observation.Value));
    }
}
