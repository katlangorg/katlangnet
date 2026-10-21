using KatLang.Evaluation;
using KatLang.Tests.InvocationRoute;

namespace KatLang.Tests;

/// <summary>
/// META-DIAG-1: when a META binder refuses an argument because it is not a supplied invocation, the
/// refusal keeps its category (<see cref="KatLangErrorCode.NotAnAlgorithm"/>), its canonical
/// description (<see cref="Evaluator.MetaRefusalDescription"/>) and its position (the offending
/// argument), and gains ONE frame naming the META parameter being bound — for a user algorithm and a
/// builtin (<c>while(meta step)</c>, <c>repeat(meta step, count)</c>) alike. A direct reification and
/// a later invocation-route refusal (D-1A) have no binding site and carry no name. Lean:
/// <c>NeedPlan.bindingRefusal</c>, <c>NeedBinder.captureMeta</c>; laws in
/// <c>KatLangArityLaws/CallReference.lean</c>, guards in <c>InvocationRouteGuards.lean</c>.
/// </summary>
public sealed class MetaBindingRefusalDiagnosticTests
{
    private const string Step = "Step(x) = x + 1, x < 3\n";

    private static string Named(string name) => $"while binding meta parameter '{name}': {KatLangError.MetaRefusalMessage}";

    /// <summary>
    /// Runs <paramref name="source"/> on every route (code, message, span and host log agree) and
    /// requires the named refusal of <paramref name="name"/>. Returns the oracle's rendered error.
    /// </summary>
    private static async Task<string> AssertRefusedOnEveryRoute(string source, string name, params string[] hostCalls)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation.Kind == "err", observation.ToString());
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith($"{KatLangErrorCode.NotAnAlgorithm}: ", error, StringComparison.Ordinal);
        Assert.Contains(Named(name), error, StringComparison.Ordinal);
        Assert.Equal(hostCalls, observation.HostCalls);
        return error;
    }

    /// <summary>
    /// The structured refusal on the synchronous and asynchronous engines: the innermost error is the
    /// canonical refusal, framed directly — and only once — by the binding frame of
    /// <paramref name="name"/>, and the public error is positioned at the supplied argument.
    /// </summary>
    private static async Task<KatLangError> AssertStructuredRefusal(string source, string name, int line, int column)
    {
        var sync = Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)).Errors);
        var asynchronous = Assert.Single(Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(source)).Errors);
        Assert.Equal(sync.Message, asynchronous.Message);
        Assert.Equal(sync.Span, asynchronous.Span);
        foreach (var error in new[] { sync, asynchronous })
        {
            Assert.Equal(KatLangErrorCode.NotAnAlgorithm, error.Code);
            Assert.False(error.IsResourceLimit);
            Assert.Equal(new SourcePosition(line, column), error.Span?.Start);

            var frames = new List<EvalError.WithContext>();
            var inner = Assert.IsAssignableFrom<EvalError>(error.Source);
            while (inner is EvalError.WithContext withContext)
            {
                frames.Add(withContext);
                inner = withContext.Inner;
            }

            var refusal = Assert.IsType<EvalError.NotAnAlgorithm>(inner);
            Assert.Equal(Evaluator.MetaRefusalDescription, refusal.Description);
            var binding = Assert.Single(frames, static frame => frame.Context.StartsWith("while binding meta parameter", StringComparison.Ordinal));
            Assert.Same(binding, frames[^1]);
            Assert.Equal(new TextErrorContext($"while binding meta parameter '{name}'"), binding.ErrorContext);
            Assert.Equal(refusal.Span, binding.Span);

            // The public projection of the same structured error renders the same message.
            Assert.Equal(error.Message, KatLangError.FromEvalError(error.Source!).Message);
        }

        return sync;
    }

    // ── A/B: a user-defined META parameter is named by its declaration ────────────────────────

    [Fact]
    public async Task UserMetaParameter_IsNamed_AtTheOffendingArgument()
    {
        const string source = "Capture(meta operation) = operation\n\nCapture(5)";
        var error = await AssertStructuredRefusal(source, "operation", 3, 9);
        Assert.Equal($"while evaluating call to Capture: {Named("operation")}", error.Message);
        await AssertRefusedOnEveryRoute(source, "operation");
    }

    [Fact]
    public async Task TheName_IsTheBoundDeclarations()
    {
        const string source = "Store(meta item) = item\n\nStore(42)";
        var error = await AssertStructuredRefusal(source, "item", 3, 7);
        Assert.Equal($"while evaluating call to Store: {Named("item")}", error.Message);
        await AssertRefusedOnEveryRoute(source, "item");
    }

    [Fact]
    public async Task ARefusedComputedArgument_IsNeverEvaluated()
        => await AssertRefusedOnEveryRoute("Capture(meta operation) = operation\nCapture(trace(5) + tick())", "operation");

    // ── C: several META parameters — the first failing pattern in written order ───────────────

    [Theory]
    [InlineData("Use(Id(1), 5)", "second", 12)]
    [InlineData("Use(5, Id(1))", "first", 5)]
    [InlineData("Use(5, 6)", "first", 5)]
    public async Task SeveralMetaParameters_NameTheFirstFailingOne(string call, string name, int column)
    {
        var source = "Id(x) = x\n\nUse(meta first, meta second) = 0\n\n" + call;
        await AssertStructuredRefusal(source, name, 5, column);
        await AssertRefusedOnEveryRoute(source, name);
    }

    [Fact]
    public async Task SeveralMetaParameters_BindWhenEveryArgumentIsAnInvocation()
        => Assert.Equal("0", (await SixRouteAgreement.OnEveryRouteAsync("Id(x) = x\nUse(meta first, meta second) = 0\nUse(Id(1), Id(2))")).Value);

    // ── D: a builtin's META parameter is named by its declared `step` ─────────────────────────

    [Theory]
    [InlineData("while(5)", "while", 1, 7)]
    [InlineData("repeat(5, 2)", "repeat", 1, 8)]
    public async Task BuiltinMetaParameter_IsNamedStep(string source, string loop, int line, int column)
    {
        var error = await AssertStructuredRefusal(source, "step", line, column);
        Assert.Equal($"while evaluating call to {loop}: {Named("step")}", error.Message);
        await AssertRefusedOnEveryRoute(source, "step");
    }

    [Fact]
    public async Task ADotLoopOverAPropertyRead_NamesStep()
        => await AssertRefusedOnEveryRoute(Step + "Start = Step(0)\nStart.while", "step");

    [Theory]
    [InlineData("while(Step(0), 1)")]
    [InlineData("repeat(5)")]
    public async Task LoopArityValidation_IsUnchanged_AndNamesNoParameter(string call)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(Step + call);
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith($"{KatLangErrorCode.ArityMismatch}: ", error, StringComparison.Ordinal);
        Assert.DoesNotContain("while binding meta parameter", error, StringComparison.Ordinal);
    }

    // ── E: forwarding — the failing INNER binding is named, never the outer capture ──────────

    [Fact]
    public async Task ForwardedMetaParameter_NamesTheFailingInnerBinding()
    {
        const string source = Step + "W(meta s) = while(s)\nW(Step(0))";
        // The transported parameter read has no span of its own: the inner `while(s)` call positions
        // the refusal, exactly as before the name was added.
        var error = await AssertStructuredRefusal(source, "step", 2, 13);
        Assert.Equal($"while evaluating call to W: while evaluating call to while: {Named("step")}", error.Message);
        Assert.DoesNotContain("parameter 's'", error.Message, StringComparison.Ordinal);
        await AssertRefusedOnEveryRoute(source, "step");
    }

    // ── F: a direct reification has no binding site ────────────────────────────────────────

    [Fact]
    public void DirectReification_KeepsTheUnframedRefusal()
    {
        foreach (var cell in new[] { NeedCell.Ready(new Evaluator.CountedResult(new Result.Atom(5), 1)), null })
        {
            var refused = Evaluator.ReifyMeta(cell);
            Assert.True(refused.IsError);
            var error = Assert.IsType<EvalError.NotAnAlgorithm>(refused.Error);
            Assert.Equal(Evaluator.MetaRefusalDescription, error.Description);
            Assert.Equal(KatLangError.MetaRefusalMessage, KatLangError.FromEvalError(error).Message);
        }
    }

    [Fact]
    public void OnlyTheCanonicalCaptureRefusal_IsFramed()
    {
        var span = new SourceSpan(new SourcePosition(2, 9), new SourcePosition(2, 10));
        var refusal = new EvalError.NotAnAlgorithm(Evaluator.MetaRefusalDescription) { Span = span };
        var framed = Assert.IsType<EvalError.WithContext>(Evaluator.AnnotateMetaBindingRefusal("op", refusal));
        Assert.Same(refusal, framed.Inner);
        Assert.Equal(new TextErrorContext("while binding meta parameter 'op'"), framed.ErrorContext);
        Assert.Equal(span, framed.Span);
        Assert.Equal(KatLangErrorCode.NotAnAlgorithm, framed.Code);

        EvalError[] unchanged =
        [
            new EvalError.NotAnAlgorithm(Evaluator.InvocationRefusalDescription),
            new EvalError.NotAnAlgorithm("param(op)"),
            new EvalError.EvaluationStepLimitExceeded(10),
            new EvalError.WithContext("while evaluating call to F", refusal),
        ];
        foreach (var error in unchanged)
            Assert.Same(error, Evaluator.AnnotateMetaBindingRefusal("op", error));
    }

    // ── G: D-1A — capture is inert; a later invocation-route refusal is not a binding failure ──

    [Fact]
    public async Task AnIntrinsicShapedInvocation_IsStillCaptured()
        => Assert.Equal("42", (await SixRouteAgreement.OnEveryRouteAsync("Ignore(meta op) = 42\nIgnore(5.string())")).Value);

    [Theory]
    [InlineData("R.Invoke()")]
    [InlineData("R.Algorithm(1)")]
    public async Task ALaterInvocationRouteRefusal_NamesNoParameter(string use)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync("Capture(meta op) = op\nR = Capture(5.string())\n" + use);
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith($"{KatLangErrorCode.NotAnAlgorithm}: ", error, StringComparison.Ordinal);
        Assert.Contains(KatLangError.InvocationRefusalMessage, error, StringComparison.Ordinal);
        Assert.DoesNotContain("while binding meta parameter", error, StringComparison.Ordinal);
    }

    // ── H: evaluation order ──────────────────────────────────────────────────────────────

    [Fact]
    public async Task AnEarlierInspectingPattern_StillRuns_BeforeTheRefusal()
        => await AssertRefusedOnEveryRoute("Mix([x], meta op) = x\nMix(trace([1]), 5)", "op", "trace(L[1])");

    [Fact]
    public async Task AnEarlierInspectingFailure_WinsOverTheLaterMetaRefusal()
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync("Mix([x], meta op) = x\nMix(trace(5), tick() + 1)");
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith($"{KatLangErrorCode.TypeMismatch}: ", error, StringComparison.Ordinal);
        Assert.DoesNotContain("while binding meta parameter", error, StringComparison.Ordinal);
        Assert.Equal(["trace(5)"], observation.HostCalls);
    }

    [Fact]
    public async Task ALaterInspectingPattern_NeverRuns_AfterTheRefusal()
        => await AssertRefusedOnEveryRoute("Mix(meta op, [x]) = x\nMix(5, trace([1]))", "op");

    [Fact]
    public async Task AnExplicitSpread_IsFormedFirst_ThenItsItemsAreRefused()
        => await AssertRefusedOnEveryRoute("P = tick(), tick()\nUse(meta first, meta second) = 0\nUse(P*)", "first", "tick#1", "tick#2");

    [Fact]
    public async Task Cardinality_PrecedesTheNamedRefusal()
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync("P = 1, 2\nCapture(meta op) = op\nCapture(P*)");
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith($"{KatLangErrorCode.ArityMismatch}: ", error, StringComparison.Ordinal);
        Assert.DoesNotContain("while binding meta parameter", error, StringComparison.Ordinal);
    }

    [Fact]
    public async Task AReachedResourceLimit_IsNeverFramed()
    {
        const string source = "Id(x) = x\nMix([x], meta op) = x\nMix([Id(Id(Id(1)))], 5)";
        var limits = new EvaluationLimits { MaxSteps = 3 };
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source, limits: limits);
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith($"{KatLangErrorCode.EvaluationStepLimitExceeded}: ", error, StringComparison.Ordinal);
        Assert.DoesNotContain("while binding meta parameter", error, StringComparison.Ordinal);
        await AssertRefusedOnEveryRoute(source, "op");
    }

    [Fact]
    public async Task ResourceCounters_Agree_WhenTheRefusalFollowsASuspendingInspection()
    {
        var program = new InvocationRouteCorpus.Case("meta-diag-1-counters", """
            CheckBefore([x], meta operation) = 0
            CheckBefore([aflag()], trace(5) + tick())
            """);
        var generic = await InvocationRouteCorpus.Observe(program, 0);
        Assert.StartsWith("err NotAnAlgorithm | ", generic.Outcome, StringComparison.Ordinal);
        Assert.Contains(Named("operation"), generic.Outcome, StringComparison.Ordinal);
        Assert.Empty(generic.Trace);
        Assert.True(generic.Steps > 0);
        Assert.True(generic.Checkpoints > 0);
        foreach (var mode in new[] { 1, 2 })
        {
            var observed = await InvocationRouteCorpus.Observe(program, mode);
            // Semantic includes code, message, span, count, effects, steps, checkpoints and
            // item/string materialization. Also compare plan retention and supply formation.
            Assert.Equal(generic.Semantic, observed.Semantic);
            Assert.Equal(generic.Plans, observed.Plans);
            Assert.Equal(generic.Formations, observed.Formations);
            Assert.Equal(mode == 2 ? 1 : 0, observed.Suspensions);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task CancellationDuringAnEarlierInspection_IsNotARefusal(bool asynchronous)
    {
        using var cancel = new CancellationTokenSource();
        var log = new List<string>();
        Result Stop() { lock (log) log.Add("stop"); cancel.Cancel(); return new Result.ListValue([new Result.Atom(1)]); }
        var operations = asynchronous
            ? HostOperations.Create(HostOperation.CreateAsync("stop", async (_, _) => { await Task.Yield(); return Stop(); }))
            : HostOperations.Create(HostOperation.Create("stop", (_, _) => Stop()));
        var options = new RunOptions { HostOperations = operations, EvaluationCancellationToken = cancel.Token };
        const string source = "Mix([x], meta op) = x\nMix(stop(), 5)";
        await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
        {
            if (asynchronous) await KatLangEngine.RunAsync(source, options);
            else KatLangEngine.Run(source, options);
        });
        Assert.Equal(["stop"], log);
    }

    // ── Regression: successful META binding is unchanged ─────────────────────────────────

    [Theory]
    [InlineData(Step + "Step(0).while", "3")]
    [InlineData("Math.Abs(-3).repeat(2)", "3")]
    [InlineData(Step + "Loop(meta op) = op.Algorithm(op.Arguments*).while\nStep(0).Loop", "3")]
    [InlineData("Capture(meta op) = op\nSquare(x) = x * x\nCapture(Square(5)).Invoke()", "25")]
    public async Task SuccessfulMetaBinding_IsUnchanged(string source, string expected)
        => Assert.Equal(expected, (await SixRouteAgreement.OnEveryRouteAsync(source)).Value);
}
