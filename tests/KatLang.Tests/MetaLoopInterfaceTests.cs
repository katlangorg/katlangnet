using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// META-S3-3 (October 2026): the loops <c>while(meta step)</c> and <c>repeat(meta step, count)</c> are
/// ordinary fixed-arity builtins whose step is a genuine META parameter, bound through THE ONE binder
/// (<c>Evaluator.ApplyMetaBuiltinCounted</c>; Lean <c>applyBuiltinCounted</c>'s
/// <c>builtinDeclaresMeta</c> branch). The captured call is never dispatched: its plan's canonical callee
/// cell is the step (CR-13) and its ONE sticky supply the initial state (CR-9). Owner decisions pinned here:
/// D1 (genuine META signatures), D2 (the retired interface is gone), D6 (no implicit provenance), D7 (plain
/// and dot forms under ordinary lookup), OD-1 (zero-state loops), RP-1 (the captured supply before the
/// count), CR-2 unchanged. Every semantic case runs on the six established routes
/// (<see cref="SixRouteAgreement"/>: sync and async engines, the genuinely suspending async twin, the
/// generic and the optimized evaluator, the forced async twin), which must agree on outcome, value,
/// every diagnostic with its span, and the exact host-call log. Lean: <c>KatLangArityLaws/MetaLoop.lean</c>,
/// <c>MetaLoopGuards.lean</c>.
/// </summary>
public class MetaLoopInterfaceTests
{
    private const string Step = "Step(x) = x + 1, x < 3\n";
    private const string Inc = "Inc(x) = x + 1\n";
    private const string Fib = "Fib(a, b) = b, a + b\n";

    private static async Task AssertOk(string source, string value, params string[] hostCalls)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation.Kind == "ok", observation.ToString());
        Assert.Equal(value, observation.Value);
        Assert.Equal(hostCalls, observation.HostCalls);
    }

    private static async Task<string> AssertFails(string source, string code, params string[] hostCalls)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation.Kind == "err", observation.ToString());
        var error = Assert.Single(observation.Errors);
        Assert.StartsWith(code + ": ", error, StringComparison.Ordinal);
        Assert.Equal(hostCalls, observation.HostCalls);
        return error;
    }

    // ── D1/D7: the public syntax ───────────────────────────────────────────────────────────

    [Theory]
    [InlineData(Step + "Step(0).while", "3")]
    [InlineData(Step + "while(Step(0))", "3")]
    [InlineData(Step + "Step(0).while()", "3")]
    [InlineData(Step + "(Step(0)).while", "3")]
    [InlineData(Inc + "Inc(0).repeat(5)", "5")]
    [InlineData(Inc + "repeat(Inc(0), 5)", "5")]
    [InlineData(Fib + "Fib(0, 1).repeat(10)", "S[55, 89]")]
    [InlineData(Fib + "Fib(0, 1).repeat(10)[0]", "55")]
    [InlineData(Step + Inc + "Step(0).while.Inc", "4")]
    [InlineData(Step + Inc + "Inc(Step(0).while).repeat(2)", "5")]
    [InlineData(Step + Inc + "while(Step(0)), Step(0).while, repeat(Inc(0), 5), Inc(0).repeat(5)", "S[3, 3, 5, 5]")]
    public Task PlainAndDotSpellings_LoopTheCapturedCall(string source, string expected) => AssertOk(source, expected);

    // ── D2: the retired interface is an ordinary exact-arity failure ───────────────────────

    [Theory]
    [InlineData(Step + "while(Step, 0)", "Callable `while(meta step)` expects 1 argument, but was called with 2 arguments.")]
    [InlineData(Step + "Step.while(0)", "Callable `while(meta step)` expects 1 argument, but was called with 2 arguments.")]
    [InlineData(Inc + "repeat(Inc, 5, 0)", "Callable `repeat(meta step, count)` expects 2 arguments, but was called with 3 arguments.")]
    [InlineData(Inc + "Inc.repeat(5, 0)", "Callable `repeat(meta step, count)` expects 2 arguments, but was called with 3 arguments.")]
    [InlineData(Fib + "Fib.repeat(10, 0, 1)", "Callable `repeat(meta step, count)` expects 2 arguments, but was called with 4 arguments.")]
    [InlineData(Inc + "Inc(0).repeat()", "Callable `repeat(meta step, count)` expects 2 arguments, but was called with 1 argument.")]
    public async Task TheRetiredSpellings_AreExactArityFailures_WithNothingEvaluated(string source, string message)
        => Assert.Contains(message, await AssertFails(source, "ArityMismatch"), StringComparison.Ordinal);

    [Fact]
    public async Task TheArityGate_PrecedesCaptureAndEveryDemand()
        => await AssertFails(Inc + "repeat(Inc(trace(1)), trace(2), trace(3))", "ArityMismatch");

    // ── META binding: one inert capture, the original cells, the canonical callee ──────────

    [Fact]
    public Task TheCapturedCall_IsNeverDispatched_AndItsArgumentCellIsTheState()
        // `trace(5)` is the captured call's ORIGINAL argument cell: demanded once, by the first iteration.
        => AssertOk(Inc + "Inc(trace(5)).repeat(3)", "8", "trace(5)");

    [Fact]
    public Task TheStepIsInvokedOnlyByIterations()
        // Three accepted rounds; the stopping round reads its flag `x < 3` FIRST (LOOP-CF1) and never
        // forms `trace(x) + 1`. The captured `Step(trace(0))` itself never runs as a call: its argument
        // is the first state slot, traced once when the first round demands it.
        => AssertOk("Step(x) = trace(x) + 1, x < 3\nStep(trace(0)).while", "3", "trace(0)", "trace(0)", "trace(1)", "trace(2)");

    [Fact]
    public Task AnExplicitSpreadInsideTheCapturedCall_RunsOnce_AndSuppliesItsItems()
        => AssertOk(Fib + "P = trace(0), trace(1)\nFib(P*).repeat(10)", "S[55, 89]", "trace(0)", "trace(1)");

    [Fact]
    public Task ANonSpreadArgument_IsOneStateSlot()
        => AssertOk("Id(x) = x\nP = 0, 1\nId(P).repeat(2), Id([1, 2]).repeat(1)", "S[S[0, 1], L[1, 2]]");

    [Fact]
    public Task TheCapturedCall_ArgumentViewAndInvoke_ShareTheOriginalCells()
        => AssertOk(
            "Capture(meta op) = op\n" + Step +
            "Use(op) = {\n R = Capture(op)\n op, while(op), R.Arguments[0], R.Invoke(), op\n}\nUse(Step(trace(0)))",
            "S[S[1, true], 3, 0, S[1, true], S[1, true]]", "trace(0)");

    [Fact]
    public Task AViewPreparedBeforeTheLoop_IsTheSameSupply_AsLaterValueAndInvoke()
        => AssertOk(
            "Capture(meta op) = op\n" + Step +
            "Use(op) = {\n R = Capture(op)\n R.Arguments[0], while(op), R.Invoke(), op\n}\nUse(Step(trace(0)))",
            "S[0, 3, S[1, true], S[1, true]]", "trace(0)");

    [Theory]
    [InlineData("F(x, x, meta op) = 0\nF(trace(1), 1, 5)")]
    [InlineData("E(x) = if(trace(x) == x, (), ())\nwhile(5, E(1)*)")]
    public async Task AMetaRefusal_DoesNotClaimEarlierDemandsNeverRan(string source)
    {
        var error = await AssertFails(source, "NotAnAlgorithm", "trace(1)");
        Assert.DoesNotContain("nothing was evaluated", error, StringComparison.Ordinal);
    }

    [Fact]
    public Task ParameterForwarding_TransportsTheOriginalCall()
        => AssertOk(Step + "W(step) = while(step)\nTwice(s) = W(s)\nW(Step(0)), Twice(Step(1)), Step(0).W", "S[3, 3, 3]");

    [Fact]
    public async Task MetaForwarding_HandsOnAReference_WhichTheLoopRefuses()
        => Assert.Contains(KatLangError.MetaRefusalMessage, await AssertFails(Step + "W(meta step) = while(step)\nW(Step(0))", "NotAnAlgorithm"), StringComparison.Ordinal);

    [Fact]
    public Task ARuntimeAliasOfTheCapturedAlgorithm_IsANamedCallee()
        => AssertOk("Capture(meta op) = op\n" + Step + "R = Capture(Step(0))\nRA = R.Algorithm\nRA(R.Arguments*).while, RA(1).while", "S[3, 3]");

    [Fact]
    public Task ALoopStepRuntimeProjection_CycleKeepsItsKind()
        => AssertFails("Keep(meta op) = op\nHold(g) = Keep(g(0))\nR = Hold(R.Algorithm)\nA = R.Algorithm\nA(0).while", "DemandCycle");

    [Theory]
    [InlineData("Inc(boom()*).repeat(1)")]
    [InlineData("Inc(0).repeat(boom())")]
    [InlineData("Step(x) = boom() + x\nStep(0).repeat(1)")]
    public async Task AHostException_InLoopSetupOrStep_PreservesTheOriginalException(string expression)
    {
        var original = new InvalidOperationException("META loop host exception");
        var operations = HostOperations.Create(HostOperation.CreateAsync("boom", async (_, _) =>
        {
            await Task.Yield();
            throw original;
        }));
        var failure = await Assert.ThrowsAsync<InvalidOperationException>(
            () => KatLangEngine.RunAsync(Inc + expression, new RunOptions { HostOperations = operations }));
        Assert.Same(original, failure);
    }

    // ── D6: no implicit provenance ──────────────────────────────────────────────────────────

    [Theory]
    [InlineData(Step + "Start = Step(0)\nStart.while")]
    [InlineData(Step + "Start = Step(0)\nwhile(Start)")]
    [InlineData(Step + "Start = Step(trace(0))\nwhile(Start), Start")]
    [InlineData("Capture(meta op) = op\n" + Step + "R = Capture(Step(0))\nR.while")]
    [InlineData(Step + "while(Step)")]
    [InlineData("while(5)")]
    [InlineData("repeat([1], 1)")]
    [InlineData(Inc + "repeat(Inc(0) + 1, 2)")]
    public async Task AnythingButASuppliedCall_IsTheOrdinaryMetaRefusal_WithNothingEvaluated(string source)
        => Assert.Contains(KatLangError.MetaRefusalMessage, await AssertFails(source, "NotAnAlgorithm"), StringComparison.Ordinal);

    [Fact]
    public async Task AnExplicitPropertyCall_IsAFreshCall_WhoseStepIsTheProperty()
        // `Start()` captures the zero-argument call of `Start` itself: zero state, and `Start`'s one row
        // `(1, true)` is not a Boolean flag.
        => Assert.Contains("must be a Boolean", await AssertFails(Step + "Start = Step(0)\nStart().while", "TypeMismatch"), StringComparison.Ordinal);

    // ── D7: ordinary lookup selects which `while`/`repeat` a call means ─────────────────────

    [Theory]
    [InlineData(Step + "while(meta s) = 100\nwhile(Step(0)), Step(0).while", "S[100, 100]")]
    [InlineData(Step + "Obj = { while = 7 }\nObj.while, Step(0).while", "S[7, 3]")]
    [InlineData("F(x) = count(x) * 10\n" + Step + "Use(while) = Step(1).while\nUse(F)", "20")]
    [InlineData(Step + "W = while\nW(Step(0))", "3")]
    [InlineData(Step + "Run(loop, s) = loop(s(0))\nRun(while, Step)", "3")]
    [InlineData("Capture(meta op) = op\n" + Step + "R = Capture(while(Step(5)))\nL = R.Algorithm\nL(Step(0))", "3")]
    [InlineData("open Lib\nLib = { public Step(x) = x + 1, x < 3 }\nStep(0).while", "3")]
    [InlineData("Outer(limit) = {\n  Step(k) = k + 1, k < limit\n  Step(0).while\n}\nOuter(5)", "5")]
    [InlineData("Countdown(0) = 0, false\nCountdown(n) = n - 1, true\nCountdown(3).while, while(Countdown(2))", "S[0, 0]")]
    public Task OrdinaryLookup_SelectsTheCallable(string source, string expected) => AssertOk(source, expected);

    // ── CR-2 is unchanged: a dot callee needs a name ─────────────────────────────────────────

    [Theory]
    [InlineData("Box = { S(x) = x + 1, x < 3 }\nBox.S(0).while")]
    [InlineData("Math.Abs(-3).repeat(2)")]
    [InlineData("Lib = { public Inc(x) = x + 1 }\nrepeat(Lib.Inc(0), 2)")]
    public async Task AQualifiedCallee_IsRefused(string source)
        => Assert.Contains(KatLangError.MetaRefusalMessage, await AssertFails(source, "NotAnAlgorithm"), StringComparison.Ordinal);

    [Theory]
    [InlineData("Box = { S(x) = x + 1, x < 3 }\nS = Box.S\nS(0).while", "3")]
    [InlineData("A = Math.Abs\nA(-3).repeat(2)", "3")]
    [InlineData("Add = { x + 10 }\nAdd(0).repeat(3)", "30")]
    [InlineData("Lib = { public Inc(x) = x + 1 }\nI = Lib.Inc\nrepeat(I(0), 2)", "2")]
    public Task TheNamedAliasWorkaround_Works(string source, string expected) => AssertOk(source, expected);

    // ── RP-1: the captured supply before the count ───────────────────────────────────────────

    [Fact]
    public Task ACapturedSpreadsFailure_PrecedesAnInvalidCount()
        => AssertFails(Inc + "Inc([1][5]*).repeat(1 / 0)", "BadIndex");

    [Fact]
    public Task ACapturedSpreadsEffect_PrecedesTheCountsEffect()
        => AssertOk(Inc + "P = trace(1)\nInc(P*).repeat(trace(2))", "3", "trace(1)", "trace(2)");

    [Fact]
    public Task AFailingCapturedSpread_NeverDemandsAnEffectfulCount()
        => AssertFails(Inc + "Inc([1][5]*).repeat(trace(2))", "BadIndex");

    [Fact]
    public Task AnInvalidCount_FollowsAnEffectfulSpread()
        => AssertFails(Inc + "P = trace(1)\nInc(P*).repeat(-1)", "IllegalInEval", "trace(1)");

    [Fact]
    public Task ANonSpreadInitialCell_StaysLazy_BeforeTheCount()
        => AssertFails(Inc + "Inc(trace(1) / 0).repeat(-1)", "IllegalInEval");

    [Fact]
    public Task CountZero_StillMaterializesTheInitialState()
        => AssertFails(Inc + "Inc(1 / 0).repeat(0)", "DivisionByZero");

    [Fact]
    public Task CountZero_NeverProjectsTheStep()
        // `N` (a non-callable value when called with a state) and a value callee supplied through a
        // parameter are never projected by zero iterations; the initial state is still materialized.
        => AssertOk("N = 5\nRun(f) = repeat(f(2), 0)\nN(trace(1)).repeat(0), Run(5)", "S[1, 2]", "trace(1)");

    [Theory]
    [InlineData(Inc + "Inc(0).repeat(-1)", "IllegalInEval", "Repeat count must be >= 0")]
    [InlineData(Inc + "Inc(0).repeat(1.5)", "IllegalInEval", "Repeat count must be an integer")]
    [InlineData(Inc + "Inc(0).repeat('x')", "TypeMismatch", "")]
    [InlineData(Inc + "Inc(0).repeat(true)", "TypeMismatch", "")]
    [InlineData(Inc + "Inc(0).repeat([1])", "TypeMismatch", "")]
    public async Task TheCount_IsAnOrdinaryValidatedValue(string source, string code, string message)
        => Assert.Contains(message, await AssertFails(source, code), StringComparison.Ordinal);

    // ── OD-1: zero effective initial state ───────────────────────────────────────────────────

    [Theory]
    [InlineData("Z = false\nZ().while", "S[]")]
    [InlineData("Z = false\nZ().repeat(0)", "S[]")]
    [InlineData("Z = false\nE = ()\nZ(E*).while", "S[]")]
    [InlineData("C(*xs) = xs*\nC().repeat(0), C().repeat(1), C().repeat(3)", "S[S[], S[], S[]]")]
    [InlineData("Z = false\nZ().while, 7", "S[S[], 7]")]
    [InlineData("Once = trace(9) > 8, false\nOnce().while", "S[]")]
    public Task AZeroSlotState_IsTheOrdinaryEmptyState(string source, string expected) => AssertOk(source, expected);

    [Theory]
    [InlineData(Inc + "Inc().repeat(1)")]
    [InlineData(Step + "Step().while")]
    public Task AStepThatNeedsAState_FailsThroughItsOwnBinding(string source) => AssertFails(source, "ArityMismatch");

    [Fact]
    public Task AZeroParameterStep_WithAZeroRepeatCount_NeverBindsIt()
        => AssertOk(Inc + "Inc().repeat(0)", "S[]");

    [Fact]
    public Task AZeroStateStepThatRowsOneTrue_FeedsThatItemBack_AsTheNextState()
        // One effective item is both the flag and the next state (LOOP-06): the second round supplies
        // one slot to the zero-parameter step, which is its own arity failure.
        => AssertFails("T = true\nT().while", "ArityMismatch");

    // A collecting zero-state step accepts the one-item `true` it feeds back, so the loop never ends.
    private const string Endless = "T(*xs) = true\nT().while";

    [Fact]
    public void AnEndlessZeroStateWhile_IsBoundedByMaxSteps_OnEveryEvaluatorRoute()
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(Endless).Root);
        var limits = new EvaluationLimits { MaxSteps = 500 };
        foreach (var optimize in new[] { false, true })
        {
            var (result, _) = Evaluator.RunCountedObserved(program, limits: limits, enableOptimizations: optimize);
            Assert.True(result.IsError);
            Assert.Equal(KatLangErrorCode.EvaluationStepLimitExceeded, KatLangError.FromEvalError(result.Error).Code);
        }

        var engine = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(Endless, new RunOptions { EvaluationLimits = limits }));
        Assert.Equal(KatLangErrorCode.EvaluationStepLimitExceeded, Assert.Single(engine.Errors).Code);
    }

    [Fact]
    public async Task AnEndlessZeroStateWhile_IsCancelled_WithTheHostsToken()
    {
        using var cancel = new CancellationTokenSource(TimeSpan.FromMilliseconds(200));
        var options = new RunOptions { EvaluationCancellationToken = cancel.Token };
        await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Task.Run(() => KatLangEngine.Run(Endless, options)));
    }

    // ── Cancellation at the RP-1 seams ───────────────────────────────────────────────────────

    private static (RunOptions Options, List<string> Log, CancellationTokenSource Cancel) Cancelling(bool asynchronous)
    {
        var cancel = new CancellationTokenSource();
        var log = new List<string>();
        Result Stop(IReadOnlyList<Result> _) { lock (log) log.Add("stop"); cancel.Cancel(); return new Result.Atom(1); }
        Result Trace(IReadOnlyList<Result> args) { lock (log) log.Add("trace"); return args[0]; }
        var operations = asynchronous
            ? HostOperations.Create(
                HostOperation.CreateAsync("stop", async (args, _) => { await Task.Yield(); return Stop(args); }),
                HostOperation.CreateAsync("trace", async (args, _) => { await Task.Yield(); return Trace(args); }, "x"))
            : HostOperations.Create(
                HostOperation.Create("stop", (args, _) => Stop(args)),
                HostOperation.Create("trace", (args, _) => Trace(args), "x"));
        return (new RunOptions { HostOperations = operations, EvaluationCancellationToken = cancel.Token }, log, cancel);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task CancellationDuringTheCapturedSpread_NeverDemandsTheCount(bool asynchronous)
    {
        var (options, log, cancel) = Cancelling(asynchronous);
        using (cancel)
        {
            const string source = Inc + "P = stop()\nInc(P*).repeat(trace(2))";
            await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
            {
                if (asynchronous) await KatLangEngine.RunAsync(source, options);
                else KatLangEngine.Run(source, options);
            });
            Assert.Equal(["stop"], log);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task CancellationDuringTheCount_RunsNoIteration(bool asynchronous)
    {
        var (options, log, cancel) = Cancelling(asynchronous);
        using (cancel)
        {
            const string source = "Step(x) = trace(x) + 1\nStep(0).repeat(stop())";
            await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
            {
                if (asynchronous) await KatLangEngine.RunAsync(source, options);
                else KatLangEngine.Run(source, options);
            });
            Assert.Equal(["stop"], log);
        }
    }

    // ── Invocation routes of a META builtin ──────────────────────────────────────────────────

    [Theory]
    [InlineData("Capture(meta op) = op\n" + Step + "R = Capture(while(Step(0)))\nR.Invoke()", "3")]
    [InlineData("Capture(meta op) = op\n" + Inc + "R = Capture(repeat(Inc(0), 4))\nR.Invoke(), R.Invoke()", "S[4, 4]")]
    [InlineData(Step + "Apply(f, x) = f(x)\nApply(while, Step(0))", "3")]
    // The captured `trace(7)` is never dispatched: the two iterations are the two host calls.
    [InlineData("abs(-3).repeat(2), count([1, 2]).repeat(1), trace(7).repeat(2)", "S[3, 2, 7]", "trace(7)", "trace(7)")]
    [InlineData(Inc + "Twice(x) = repeat(Inc(x), 2)\nmap([1, 2], Twice)", "L[3, 4]")]
    [InlineData(Step + "Inner(x) = while(Step(x))\nOuter(x) = Inner(x) + 10\nOuter(0).repeat(1)", "13")]
    public Task EveryRouteToTheBuiltin_BindsThroughTheOneBinder(string source, string expected, params string[] hostCalls)
        => AssertOk(source, expected, hostCalls);

    [Theory]
    [InlineData("map([1], while)")]
    [InlineData(Inc + "reduce([1, 2], repeat, Inc(0))")]
    public async Task ACallbackInvocation_SuppliesReadyCells_WhichMetaRefuses(string source)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", observation.Kind);
        Assert.StartsWith("NotAnAlgorithm: ", Assert.Single(observation.Errors), StringComparison.Ordinal);
    }

    // ── The optimizer still serves the loops ─────────────────────────────────────────────────

    [Theory]
    [InlineData(Step + "Step(0).while", "3")]
    [InlineData(Fib + "Fib(0, 1).repeat(10)", "S[55, 89]")]
    [InlineData(Inc + "repeat(Inc(0), 1000)", "1000")]
    [InlineData("Countdown(0) = 0, false\nCountdown(n) = n - 1, true\nCountdown(3).while", "0")]
    public void TheOptimizedLoop_PlansTheCapturedStep_WithTheGenericOutcome(string source, string expected)
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var loops = new LoopOptimizationDiagnostics();
        var (optimized, optimizedBudget) = Evaluator.RunCountedObserved(program, enableOptimizations: true, loopDiagnostics: loops);
        var (generic, genericBudget) = Evaluator.RunCountedObserved(program, enableOptimizations: false);
        Assert.False(optimized.IsError);
        Assert.Equal(expected, SixRouteAgreement.Neutral(optimized.Value.Value));
        Assert.Equal(SixRouteAgreement.Neutral(generic.Value.Value), SixRouteAgreement.Neutral(optimized.Value.Value));
        Assert.Equal(genericBudget.ConsumedSteps, optimizedBudget.ConsumedSteps);
        if (!source.Contains("Countdown", StringComparison.Ordinal))
            Assert.True(loops.GetSnapshot().OptimizedLoopHits > 0);
    }

    // ── J7: a program that may reach a META builtin retains invocation plans ────────────────

    [Theory]
    [InlineData(Step + "Step(0).while", true)]
    [InlineData(Inc + "repeat(Inc(0), 2)", true)]
    [InlineData("W = while\n0", true)]
    [InlineData("Lib = { public L = repeat }\n0", true)]
    [InlineData("F(x) = x + 1\nF(2)", false)]
    [InlineData("map([1, 2], { x + 1 })", false)]
    public void TheProgramGate_RecognizesEveryMetaBuiltinRoute(string source, bool retains)
        => Assert.Equal(retains, Evaluator.ProgramMayCaptureCalls(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root)));

    [Fact]
    public void TheProgramGate_RecognizesAHostBuiltBuiltinNode()
    {
        var call = new Expr.Call(new Expr.AlgorithmExpr(new Algorithm.Builtin(BuiltinId.@while)), [new Expr.Num(0)]);
        Assert.True(Evaluator.ProgramMayCaptureCalls(call));
        Assert.False(Evaluator.ProgramMayCaptureCalls(new Expr.Call(new Expr.AlgorithmExpr(new Algorithm.Builtin(BuiltinId.@count)), [new Expr.Num(0)])));
    }

    [Theory]
    [InlineData(BuiltinId.@while)]
    [InlineData(BuiltinId.@repeat)]
    public async Task AHostBuiltBuiltinCall_RunsWithoutAnyPreludeLoopSpelling(BuiltinId builtin)
    {
        Expr next = new Expr.Binary(BinaryOp.Add, new Expr.Param("x"), new Expr.Num(1));
        var output = builtin == BuiltinId.@repeat ? new[] { next }
            : new[] { next, new Expr.Comparison(new Expr.Param("x"), [new ComparisonLink(ComparisonOp.Lt, new Expr.Num(2))]) };
        var step = new Algorithm.User(null, [new CaptureParameterPattern("x")], [], [], output);
        Expr captured = new Expr.Call(new Expr.Resolve("S"), [new Expr.Num(0)]);
        var arguments = builtin == BuiltinId.@repeat ? new[] { captured, new Expr.Num(2) } : new[] { captured };
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("S", step)],
            [new Expr.Call(new Expr.AlgorithmExpr(new Algorithm.Builtin(builtin)), new OutputBundle(arguments))]));
        foreach (var optimize in new[] { false, true })
        {
            var (result, _) = Evaluator.RunCountedObserved(program, enableOptimizations: optimize);
            Assert.False(result.IsError);
            Assert.Equal(new Result.Atom(2), result.Value.Value);
        }
        var asynchronous = await Evaluator.RunCountedAsync(program,
            zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache());
        Assert.False(asynchronous.IsError);
        Assert.Equal(new Result.Atom(2), asynchronous.Value.Value);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AForeignOrEndedCapturedCall_IsRefusedBeforeSupplyOrCalleeWork(bool ended)
    {
        static Evaluator.EvalCtx Context()
        {
            var budget = EvaluationBudget.Create(null);
            budget.DecideInvocationPlanRetention(programMayCapture: true);
            return Evaluator.EvalCtx.Empty with { Budget = budget };
        }
        var owner = Context();
        var call = Evaluator.SupplyCell(new Expr.Call(new Expr.Resolve("Never"), [new Expr.Num(5)]), owner, []);
        var plan = Assert.IsType<Evaluator.InvocationPlan>(call.Suspension);
        var consumer = ended ? owner : Context();
        if (ended) owner.Budget.EndRun();
        var expression = new Expr.Call(new Expr.AlgorithmExpr(new Algorithm.Builtin(BuiltinId.@repeat)),
            [new Expr.Param("op"), new Expr.Num(0)]);
        var result = Evaluator.EvalCounted(expression, consumer.WithNeedEnv([("op", call)]), []);
        Assert.True(result.IsError);
        var error = result.Error;
        while (error is EvalError.WithContext context) error = context.Inner;
        Assert.Equal(ended ? Evaluator.EndedCallReferenceMessage : Evaluator.ForeignCallReferenceMessage,
            Assert.IsType<EvalError.IllegalInEval>(error).Reason);
        Assert.Null(plan.Supply);
        Assert.False(plan.HasCalleeCell);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ADeferredModule_CanSupplyTheLoopAlias_OrRetainItsAcquisitionFailure(bool fail)
    {
        var downloads = 0;
        var result = await KatLangEngine.RunAsync(
            "F(0) = 0\nF(n) = { open 'https://modules.example/loops.kat'\n Loop(Step(n), 2) }\nF(3)",
            new RunOptions
            {
                AllowedHosts = ["modules.example"],
                DownloadCode = async (_, token) =>
                {
                    Interlocked.Increment(ref downloads);
                    await Task.Yield();
                    token.ThrowIfCancellationRequested();
                    if (fail) throw new IOException("META loop acquisition failure");
                    return "public Loop = repeat\npublic Step(x) = x + 1";
                },
            });
        Assert.Equal(1, downloads);
        if (fail)
            Assert.Contains(Assert.IsType<RunResult.EvalFailure>(result).Errors,
                static error => error.Code == KatLangErrorCode.LoadFetchFailed);
        else
            Assert.Equal(new Result.Atom(5), Assert.IsType<RunResult.Success>(result).Value);
    }

    // ── The registry and the semantic model expose the genuine META signature ───────────────

    [Fact]
    public void TheRegistrySignature_IsTheOneSignature()
    {
        var @while = BuiltinRegistry.GetBuiltin(BuiltinId.@while);
        var repeat = BuiltinRegistry.GetBuiltin(BuiltinId.@repeat);
        Assert.Equal("while(meta step)", @while.PlainSignature.DisplayText);
        Assert.Equal("repeat(meta step, count)", repeat.PlainSignature.DisplayText);
        Assert.Equal(["while", "repeat"], BuiltinRegistry.AllBuiltins.Where(static b => b.DeclaresMetaParameter).Select(static b => b.Name));
        Assert.True(@while.IsMetaPosition(0));
        Assert.True(repeat.IsMetaPosition(0));
        Assert.False(repeat.IsMetaPosition(1));
        Assert.Equal(["repeat", "while"], BuiltinRegistry.MetaBuiltinNames.Order(StringComparer.Ordinal));
    }

    [Fact]
    public void UserAndBuiltinMetaParameters_AreReportedAlike()
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics("Keep(meta op, n) = op\nKeep(Inc(0), 1)\nInc(x) = x + 1");
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        var keep = model.FindPropertyAt(new SourcePosition(1, 1))!;
        var parameters = keep.GetParameters(PropertyCallStyle.Plain);
        Assert.Equal([true, false], parameters.Select(static parameter => parameter.IsMeta));
        Assert.Equal(["meta op", "n"], parameters.Select(static parameter => parameter.DisplayName));
        Assert.Equal("Keep(meta op, n)", keep.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal("op.Keep(n)", keep.GetDisplaySignature(PropertyCallStyle.Dot));

        var builtin = Assert.Single(PreludeCatalog.Symbols, static symbol => symbol.Name == "repeat").Property!;
        Assert.Equal(["meta step", "count"], builtin.GetParameters(PropertyCallStyle.Plain).Select(static parameter => parameter.DisplayName));
    }
}
