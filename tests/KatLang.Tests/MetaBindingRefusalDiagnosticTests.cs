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
        // META-DIAG-2: the refusal is positioned at the argument as written at the refusing binding — the
        // read `s` inside `while(s)` — never at the whole call, the declaration, or `Step(0)`.
        var error = await AssertStructuredRefusal(source, "step", 2, 19);
        Assert.Equal(new SourceSpan(new SourcePosition(2, 19), new SourcePosition(2, 20)), error.Span);
        Assert.Equal($"while evaluating call to W: while evaluating call to while: {Named("step")}", error.Message);
        Assert.DoesNotContain("parameter 's'", error.Message, StringComparison.Ordinal);
        var routed = await AssertRefusedOnEveryRoute(source, "step");
        Assert.EndsWith("@ [2:19, 2:20)", routed, StringComparison.Ordinal);
    }

    // ── META-DIAG-2: a forwarded parameter read is positioned at its own occurrence ─────────

    private static async Task AssertRefusedAt(string source, string name, int line, int column)
    {
        var error = await AssertStructuredRefusal(source, name, line, column);
        Assert.Equal(new SourceSpan(new SourcePosition(line, column), new SourcePosition(line, column + 1)), error.Span);
        var routed = await AssertRefusedOnEveryRoute(source, name);
        Assert.EndsWith($"@ [{line}:{column}, {line}:{column + 1})", routed, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("F(x) = while(x)\nF(42)", "step", 1, 14)]
    [InlineData("F(x) = repeat(x, 2)\nF(42)", "step", 1, 15)]
    [InlineData("F(x) = x.while\nF(42)", "step", 1, 8)]
    [InlineData("F(x) = x.repeat(2)\nF(42)", "step", 1, 8)]
    [InlineData(Step + "F(x) = while(x)\nF(1 / 0)", "step", 2, 14)]
    [InlineData("Capture(meta op) = op\nF(x) = Capture(x)\nF(42)", "op", 2, 16)]
    [InlineData("Capture(meta op) = op\nF(x) = Capture((x))\nF(42)", "op", 2, 17)]
    [InlineData("Capture(meta op) = op\nG(y) = F(y)\nF(x) = Capture(x)\nG(42)", "op", 3, 16)]
    public async Task AForwardedOrdinaryParameter_IsPositionedAtItsRead(string source, string name, int line, int column)
        // Not at the argument originally written for the transported cell (`42`, `1 / 0`).
        => await AssertRefusedAt(source, name, line, column);

    [Theory]
    // One cell read twice in one call: the META slot's read, not the first (value) read.
    [InlineData("Pick(a, meta op) = op\nF(x) = Pick(x, x)\nF(42)", "op", 2, 16)]
    // The cell's VALUE was demanded at an earlier read; the refusal is still the later read's.
    [InlineData("F(x) = x + while(x)\nF(1)", "step", 1, 18)]
    // An earlier inspecting pattern binds a different argument; the META slot's read is blamed.
    [InlineData("Mix([v], meta op) = v\nF(x) = Mix([1], x)\nF(7)", "op", 2, 17)]
    public async Task OneCellReadAtSeveralOccurrences_BlamesTheRefusedRead(string source, string name, int line, int column)
        => await AssertRefusedAt(source, name, line, column);

    [Fact]
    public async Task TheSameCell_RefusedAtTwoBindingSites_IsPositionedAtEachRead()
    {
        // One original cell (`42`) forwarded to two independent refusing sites: no position leaks between them.
        const string head = "Capture(meta op) = op\nA(x) = Capture(x)\nB(x) = while(x)\n";
        await AssertRefusedAt(head + "A(42)", "op", 2, 16);
        await AssertRefusedAt(head + "B(42)", "step", 3, 14);
        await AssertRefusedAt(head + "F(y) = A(y), B(y)\nF(42)", "op", 2, 16);
        await AssertRefusedAt(head + "F(y) = B(y), A(y)\nF(42)", "step", 3, 14);
    }

    [Theory]
    // A planned call (a supplied invocation demanded for its VALUE) and a captured call run by Invoke.
    [InlineData("Capture(meta op) = op\nG(y) = y\nF(x) = G(Capture(x))\nF(42)")]
    [InlineData("Capture(meta op) = op\nO(meta r) = r.Invoke()\nF(x) = O(Capture(x))\nF(42)")]
    public async Task APlannedBinding_IsPositionedAtTheForwardedRead(string source)
        => await AssertRefusedAt(source, "op", 3, 18);

    [Theory]
    [InlineData("Capture(meta op) = op\nF(x) = Capture([]*, x)\nF(42)", 2, 21)]
    [InlineData("Capture(meta op) = op\nG(y) = y\nF(x) = G(Capture([]*, x))\nF(42)", 3, 23)]
    [InlineData("Capture(meta op) = op\nO(meta r) = r.Invoke()\nF(x) = O(Capture([]*, x))\nF(42)", 3, 23)]
    [InlineData("Capture(a, meta op) = op\nO(meta r) = r.Invoke()\nF(x) = O(Capture([1]*, x))\nF(42)", 3, 24)]
    [InlineData("Capture(meta op, a) = op\nO(meta r) = r.Invoke()\nF(x) = O(Capture(x, [1]*))\nF(42)", 3, 18)]
    [InlineData("Capture(meta op) = op\nO(meta r) = r.Arguments.count + r.Invoke()\nF(x) = O(Capture([]*, x))\nF(42)", 3, 23)]
    public async Task ASpreadSibling_DoesNotEraseTheForwardedOccurrence(string source, int line, int column)
        => await AssertRefusedAt(source, "op", line, column);

    [Fact]
    public async Task ASuspendingSpread_PreservesTheForwardedOccurrence()
    {
        const string source = "Capture(a, meta op) = op\nO(meta r) = r.Invoke()\nF(x) = O(Capture(trace([1])*, x))\nF(42)";
        var error = await AssertRefusedOnEveryRoute(source, "op", "trace(L[1])");
        Assert.EndsWith("@ [3:31, 3:32)", error, StringComparison.Ordinal);
    }

    [Fact]
    public async Task AnOpenedSpreadItem_KeepsItsCellsOwnSource()
    {
        // An opened spread's item has no written slot of its own: it keeps the argument written for it.
        const string source = "F(*xs) = while(xs*)\nF(42)";
        await AssertStructuredRefusal(source, "step", 2, 3);
        await AssertRefusedOnEveryRoute(source, "step");
    }

    [Fact]
    public async Task OtherFailuresOfAForwardedRead_KeepTheirPositions()
    {
        // Inspecting failures keep their binding position; a failure inside a transported computation
        // keeps its inner origin instead of being repositioned at the forwarding read.
        var inspected = await SixRouteAgreement.OnEveryRouteAsync("Mix([v], meta op) = v\nF(x) = Mix(x, 5)\nF(7)");
        Assert.StartsWith($"{KatLangErrorCode.TypeMismatch}: ", Assert.Single(inspected.Errors), StringComparison.Ordinal);
        Assert.Contains("@ [2:8,", inspected.Errors[0], StringComparison.Ordinal);
        var computation = await SixRouteAgreement.OnEveryRouteAsync("Mix([v], meta op) = v\nBad = 1 / 0\nF(x) = Mix(x, 5)\nF(Bad)");
        Assert.StartsWith($"{KatLangErrorCode.DivisionByZero}: ", Assert.Single(computation.Errors), StringComparison.Ordinal);
        Assert.EndsWith("@ [2:7, 2:12)", computation.Errors[0], StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("F(x) = map([1, 2], x)\nF(42)", 20)]
    [InlineData("F(x) = filter([1], x)\nF(42)", 20)]
    [InlineData("F(x) = reduce([1], x, 0)\nF(42)", 20)]
    [InlineData("F(x) = count(filter(range(1, 3), x))\nF(42)", 34)]
    [InlineData("F(x) = [1].map(x)\nF(42)", 16)]
    [InlineData("F(x) = map([1], (x))\nF(42)", 18)]
    [InlineData("F(x) = map([], x), map([1], x)\nF(42)", 29)]
    public async Task ANonMetaCapabilityRefusal_BlamesTheCurrentOccurrence(string source, int column)
    {
        var result = await SixRouteAgreement.OnEveryRouteAsync(source);
        var error = Assert.Single(result.Errors);
        Assert.StartsWith($"{KatLangErrorCode.NotAnAlgorithm}: ", error, StringComparison.Ordinal);
        Assert.DoesNotContain("meta parameter", error, StringComparison.Ordinal);
        Assert.EndsWith($"@ [1:{column}, 1:{column + 1})", error, StringComparison.Ordinal);
        Assert.Empty(result.HostCalls);
    }

    [Fact]
    public async Task AForwardedProjectionFailure_KeepsItsInnerOrigin()
    {
        var result = await SixRouteAgreement.OnEveryRouteAsync("F(x) = map([1], x)\nF((1 / 0).Algorithm)");
        var error = Assert.Single(result.Errors);
        Assert.StartsWith($"{KatLangErrorCode.DivisionByZero}: ", error, StringComparison.Ordinal);
        Assert.EndsWith("@ [2:3, 2:10)", error, StringComparison.Ordinal);
    }

    [Fact]
    public async Task AModuleWrittenRead_NeverExposesModuleCoordinates()
    {
        // A loaded module's import view is locationless: its `s` has no span in this document, so the
        // refusal keeps the attach-if-missing law and is positioned at the local call `W(Step(0))`.
        var options = new RunOptions
        {
            DownloadCode = static (_, _) => ValueTask.FromResult("public W(meta s) = while(s)"),
        };
        const string source = "open Lib\nLib = load('https://katlang.org/demo/meta-diag-2.kat')\n" + Step + "W(Step(0))";
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(source, options)).Errors);
        Assert.Equal(KatLangErrorCode.NotAnAlgorithm, error.Code);
        Assert.Contains(Named("step"), error.Message, StringComparison.Ordinal);
        Assert.Equal(new SourcePosition(4, 1), error.Span?.Start);
    }

    [Theory]
    [InlineData(Step + "F(x) = while(x)\nF(Step(0))", "3")]
    [InlineData(Step + "F(x) = while(x)\nG(y) = F(y)\nG(Step(0))", "3")]
    [InlineData(Step + "T = Step\nF(x) = while(x)\nF(T(0))", "3")]
    [InlineData(Step + "F(x) = x.while\nF(Step(0))", "3")]
    [InlineData("Capture(meta op) = op\nSquare(v) = v * v\nF(x) = Capture(x).Invoke()\nF(Square(5))", "25")]
    [InlineData("Capture(meta op) = op\nSquare(v) = v * v\nF(x) = Capture(x)\nG(y) = F(y).Invoke()\nG(Square(4))", "16")]
    public async Task SuccessfulForwarding_IsUnchanged(string source, string expected)
        => Assert.Equal(expected, (await SixRouteAgreement.OnEveryRouteAsync(source)).Value);

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
