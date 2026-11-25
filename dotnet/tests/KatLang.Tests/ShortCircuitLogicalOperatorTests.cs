using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

/// <summary>
/// SHORT-CIRCUIT <c>and</c> / <c>or</c> (issue #202), pinned on every C# route that chooses
/// which operand of a binary expression to evaluate: the generic expression-spine machine, its
/// async twin (completing synchronously and genuinely suspending), and the planned loop
/// evaluator.
///
/// <para>The rule. The left operand is evaluated once and must be a Boolean. When it decides
/// the operator — <c>false and _</c>, <c>true or _</c> — the result is that Boolean and the
/// right operand is not evaluated: it has no effect (<c>tick()</c>, a host call), no failure,
/// no suspension and no charge, and its value kind is never checked. Otherwise the right
/// operand is evaluated once, must be a Boolean, and is the result. A left operand's failure
/// or value-kind rejection is the outcome before any right operand work. <c>xor</c> needs both
/// operands and stays eager; <c>not</c> and comparison chains are unchanged.</para>
///
/// <para>Lean twins: <c>evalBinaryCounted</c> / <c>BinaryOp.leftOperandDecides</c>, the
/// <c>shortCircuit*</c> guards of <c>lean/CoreTests/Numerics.lean</c>, and
/// <c>EvaluatorInstallation.logical_arm</c> / <c>logical_arm_decided</c>. C# owner:
/// <c>Evaluator.DecideLogicalAfterLeftOperand</c>, the one post-left decision the three
/// routes share.</para>
/// </summary>
public class ShortCircuitLogicalOperatorTests
{
    // ── Routes ──────────────────────────────────────────────────────────────

    /// <summary>
    /// The routes of a program without host operations: the synchronous machine with the
    /// optimizer off and on, and the async twin over a cache whose accesses complete
    /// synchronously and over one whose every property read GENUINELY suspends.
    /// </summary>
    public static readonly string[] Routes =
        ["sync-generic", "sync-optimized", "async-twin", "async-twin-suspending"];

    private static async Task<EvalResult<Evaluator.CountedResult>> RunOn(string route, string source)
    {
        var ast = Program(source);
        switch (route)
        {
            case "sync-generic":
                return Evaluator.RunCountedObserved(ast, enableOptimizations: false).Result;

            case "sync-optimized":
                return Evaluator.RunCountedObserved(ast, enableOptimizations: true).Result;

            case "async-twin":
            {
                var cache = new PassThroughAsyncZeroArgPropertyResultCache();
                var result = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedAsync(ast, cache));
                Assert.Equal(0, cache.SyncAccesses);
                return result;
            }

            case "async-twin-suspending":
            {
                var cache = new SuspendingAsyncZeroArgPropertyResultCache();
                var result = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedAsync(ast, cache));
                Assert.Equal(0, cache.SyncAccesses);
                return result;
            }

            default:
                throw new ArgumentOutOfRangeException(nameof(route), route, "unknown route");
        }
    }

    /// <summary>The corpora's neutral outcome encoding: <c>ok raw=… n=…</c> or <c>err category</c>.</summary>
    private static string Outcome(EvalResult<Evaluator.CountedResult> result)
        => AsyncEvaluationHarness.NeutralOf(result);

    // ── The outcome matrix ──────────────────────────────────────────────────

    /// <summary>
    /// Each program with its expected outcome. An operand <c>tick() == n</c> is effectful and
    /// computed at run time: it is <c>true</c> iff it ran as the run's n-th tick, and the
    /// program's last row <c>tick()</c> therefore reports one more than the number of operands
    /// that ran.
    /// </summary>
    public static readonly (string Id, string Source, string Expected)[] Matrix =
    [
        // The four examples of issue #202.
        ("issue-false-and", "false and 1 / 0 > 0", "ok raw=false n=1"),
        ("issue-true-or", "true or 1 / 0 > 0", "ok raw=true n=1"),
        ("issue-true-and", "true and 1 / 0 > 0", "err div0"),
        ("issue-false-or", "false or 1 / 0 > 0", "err div0"),

        // Literal left operand: a skipped right operand runs zero times, an evaluated one once.
        ("literal-and-skips", "false and tick() == 1, tick()", "ok raw=S[false, 1] n=2"),
        ("literal-or-skips", "true or tick() == 1, tick()", "ok raw=S[true, 1] n=2"),
        ("literal-and-evaluates-true", "true and tick() == 1, tick()", "ok raw=S[true, 2] n=2"),
        ("literal-and-evaluates-false", "true and tick() == 2, tick()", "ok raw=S[false, 2] n=2"),
        ("literal-or-evaluates-true", "false or tick() == 1, tick()", "ok raw=S[true, 2] n=2"),
        ("literal-or-evaluates-false", "false or tick() == 2, tick()", "ok raw=S[false, 2] n=2"),

        // Left operand computed at run time: it takes tick 1, and the right operand takes
        // tick 2 only when the left one did not decide.
        ("runtime-and-evaluates", "tick() == 1 and tick() == 2, tick()", "ok raw=S[true, 3] n=2"),
        ("runtime-and-skips", "tick() == 2 and tick() == 2, tick()", "ok raw=S[false, 2] n=2"),
        ("runtime-or-skips", "tick() == 1 or tick() == 2, tick()", "ok raw=S[true, 2] n=2"),
        ("runtime-or-evaluates", "tick() == 2 or tick() == 2, tick()", "ok raw=S[true, 3] n=2"),
        ("runtime-or-evaluates-false", "tick() == 2 or tick() == 1, tick()", "ok raw=S[false, 3] n=2"),

        // Nesting, precedence (`and` binds tighter than `or`) and left associativity.
        ("nested-skips-a-whole-tree", "false and (tick() == 1 or tick() == 2), tick()", "ok raw=S[false, 1] n=2"),
        ("nested-inner-skip-outer-evaluates", "(false and tick() == 1) or tick() == 1, tick()", "ok raw=S[true, 2] n=2"),
        ("precedence-or-skips-the-and", "true or tick() == 1 and tick() == 2, tick()", "ok raw=S[true, 1] n=2"),
        ("precedence-and-then-or", "false and tick() == 1 or tick() == 1, tick()", "ok raw=S[true, 2] n=2"),
        ("chain-and-all-true", "tick() == 1 and tick() == 2 and tick() == 3, tick()", "ok raw=S[true, 4] n=2"),
        ("chain-and-stops-at-first-false", "tick() == 1 and tick() == 9 and tick() == 3, tick()", "ok raw=S[false, 3] n=2"),
        ("chain-or-stops-at-first-true", "tick() == 9 or tick() == 2 or tick() == 3, tick()", "ok raw=S[true, 3] n=2"),
        ("not-of-a-skipping-and", "not (false and tick() == 1), tick()", "ok raw=S[true, 1] n=2"),

        // Operands read through properties: the suspending route suspends at each DEMANDED
        // operand, and a skipped operand's property is never demanded.
        ("property-and-skips", "L = false\nR = tick() == 1\nL and R, tick()", "ok raw=S[false, 1] n=2"),
        ("property-and-evaluates", "L = tick() == 1\nR = tick() == 2\nL and R, tick()", "ok raw=S[true, 3] n=2"),
        ("property-or-skips", "L = true\nR = tick() == 1\nL or R, tick()", "ok raw=S[true, 1] n=2"),
        ("property-or-evaluates", "L = tick() == 2\nR = tick() == 2\nL or R, tick()", "ok raw=S[true, 3] n=2"),
        ("property-skipped-failure", "Boom = 1 / 0 > 0\nfalse and Boom", "ok raw=false n=1"),
        ("property-evaluated-failure", "Boom = 1 / 0 > 0\ntrue and Boom", "err div0"),

        // A practical guard with a zero denominator; the left operand is a parameter comparison.
        ("guard-and", "Safe(n, d) = d != 0 and n / d > 1\nSafe(10, 0), Safe(10, 2), Safe(2, 4)", "ok raw=S[false, true, false] n=3"),
        ("guard-or", "Skip(n, d) = d == 0 or n / d > 1\nSkip(10, 0), Skip(10, 2), Skip(2, 4)", "ok raw=S[true, true, false] n=3"),
        ("guard-in-if", "Ratio(n, d) = if(d != 0 and n / d > 1, n / d, 0)\nRatio(10, 0), Ratio(10, 2)", "ok raw=S[0, 5] n=2"),
        ("guard-in-filter", "Ds = [0, 2, 5, 20]\nDs.filter({ d != 0 and 10 / d > 1 })", "ok raw=L[2, 5] n=1"),

        // A skipped right operand is never checked for a Boolean; an evaluated one is.
        ("right-kind-skipped-and", "false and 1", "ok raw=false n=1"),
        ("right-kind-skipped-or", "true or 'x'", "ok raw=true n=1"),
        ("right-kind-skipped-empty", "false and ()", "ok raw=false n=1"),
        ("right-kind-evaluated-and", "true and 1", "err type"),
        ("right-kind-evaluated-or", "false or 'x'", "err type"),

        // The left operand is judged first: its rejection or failure is the outcome.
        ("left-kind-rejected", "1 and tick() == 1", "err type"),
        ("left-failure", "1 / 0 > 0 and tick() == 1", "err div0"),

        // A parameter read only by the skipped operand is never demanded (call by need).
        ("skipped-parameter-is-not-demanded", "F(a, b) = a and b\nF(false, 1 / 0 > 0)", "ok raw=false n=1"),
        ("evaluated-parameter-is-demanded", "F(a, b) = a and b\nF(true, 1 / 0 > 0)", "err div0"),

        // Control: `xor` is eager.
        ("xor-evaluates-right-after-true", "true xor tick() == 1, tick()", "ok raw=S[false, 2] n=2"),
        ("xor-evaluates-right-after-false", "false xor tick() == 1, tick()", "ok raw=S[true, 2] n=2"),
        ("xor-right-failure", "false xor 1 / 0 > 0", "err div0"),
        ("xor-right-kind", "true xor 1", "err type"),
    ];

    public static TheoryData<string, string> MatrixOnEveryRoute()
    {
        var data = new TheoryData<string, string>();
        foreach (var (id, _, _) in Matrix)
        foreach (var route in Routes)
            data.Add(id, route);
        return data;
    }

    private static (string Source, string Expected) Case(string id)
    {
        var found = Assert.Single(Matrix, entry => entry.Id == id);
        return (found.Source, found.Expected);
    }

    [Theory]
    [MemberData(nameof(MatrixOnEveryRoute))]
    public async Task Outcome_IsTheShortCircuitOutcome_OnEveryRoute(string id, string route)
    {
        var (source, expected) = Case(id);
        Assert.Equal(expected, Outcome(await RunOn(route, source)));
    }

    [Fact]
    public void MatrixIds_AreUnique()
        => Assert.Equal(Matrix.Length, Matrix.Select(static entry => entry.Id).Distinct(StringComparer.Ordinal).Count());

    [Theory]
    [InlineData("false and 1 / 0 > 0", "false")]
    [InlineData("true or 1 / 0 > 0", "true")]
    [InlineData("Safe(n, d) = d != 0 and n / d > 1\nSafe(10, 0)\nSafe(10, 2)", "false\ntrue")]
    public void PublicEngine_ReturnsTheShortCircuitValue(string source, string display)
        => Assert.Equal(
            display,
            Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString().ReplaceLineEndings("\n"));

    [Theory]
    [InlineData("false and")]
    [InlineData("true or")]
    public void SkippedOperand_StillParticipatesInInferenceAndNameResolution(string leftAndOperator)
    {
        var expression = $"{leftAndOperator} missing";
        var root = SourceProvenance.ParseValid($"F = {expression}\nF(1 / 0)").Root;
        Assert.Equal(["missing"], Assert.Single(root.Properties).Value.Params);

        var diagnostics = SourceProvenance.ExpectFrontEndError($"F(x) = {expression}\nF(1)");
        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, Assert.Single(diagnostics).Code);
    }

    [Theory]
    [InlineData("false and", 0)]
    [InlineData("true or", 0)]
    [InlineData("true and", 1)]
    [InlineData("false or", 1)]
    public void RightOperand_ConsumesOneRandomDrawOnlyWhenEvaluated(string leftAndOperator, int drawsConsumed)
    {
        const string draw = "randomInt(1, 1000000)";
        var options = new RunOptions { RandomSeed = 42 };
        var draws = Assert.IsType<RunResult.Success>(KatLangEngine.Run($"{draw}, {draw}", options)).OutputRows;
        Assert.NotEqual(draws[0], draws[1]);

        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            $"{leftAndOperator} {draw} > 0, {draw}", options));
        Assert.Equal(draws[drawsConsumed], result.OutputRows[1]);
    }

    // ── Genuine suspension: only demanded operands suspend ──────────────────

    [Theory]
    [InlineData("L = false\nR = true\nL and R", 1, "ok raw=false n=1")]
    [InlineData("L = true\nR = true\nL and R", 2, "ok raw=true n=1")]
    [InlineData("L = true\nR = false\nL or R", 1, "ok raw=true n=1")]
    [InlineData("L = false\nR = false\nL or R", 2, "ok raw=false n=1")]
    [InlineData("L = true\nR = true\nL xor R", 2, "ok raw=false n=1")]
    [InlineData("L = false\nR = true\nL xor R", 2, "ok raw=true n=1")]
    public async Task SuspendingRoute_SuspendsOncePerDemandedOperand(string source, int demandedOperands, string expected)
    {
        // Every property read on this route yields and resumes; the operand properties are the
        // program's only property reads, so the access count IS the number of demanded operands.
        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var result = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedAsync(Program(source), cache));

        Assert.Equal(expected, Outcome(result));
        Assert.Equal(demandedOperands, cache.AsyncAccesses);
        Assert.Equal(demandedOperands, cache.ThreadHops.Count);
        Assert.Equal(0, cache.SyncAccesses);
    }

    // ── Instrumented host operations: order, multiplicity, and failed runs ──

    /// <summary>The executions of the instrumented operation, in order.</summary>
    private sealed class HostTrace
    {
        private readonly List<string> _calls = [];

        public string Calls
        {
            get
            {
                lock (_calls)
                    return string.Join(",", _calls);
            }
        }

        public Result See(IReadOnlyList<Result> args)
        {
            lock (_calls)
                _calls.Add(Assert.IsType<Result.Str>(args[0]).Value);
            return args[1];
        }
    }

    /// <summary><c>see(label, value)</c> records <c>label</c> and returns <c>value</c>.</summary>
    private static HostOperations SynchronousSee(HostTrace trace)
        => HostOperations.Create(HostOperation.Create("see", (args, _) => trace.See(args), "label", "value"));

    /// <summary>The same operation, GENUINELY suspending before it records and returns.</summary>
    private static HostOperations SuspendingSee(HostTrace trace)
        => HostOperations.Create(HostOperation.CreateAsync(
            "see",
            async (args, _) =>
            {
                await Task.Yield();
                return trace.See(args);
            },
            "label",
            "value"));

    /// <summary><c>ok display</c>, or <c>err Code</c> with the single evaluation error's code.</summary>
    private static string Outcome(RunResult result)
        => result switch
        {
            RunResult.Success success => $"ok {success.ToDisplayString().ReplaceLineEndings("\n")}",
            RunResult.EvalFailure failure => $"err {Assert.Single(failure.Errors).Code}",
            _ => $"unexpected {result.GetType().Name}",
        };

    public static TheoryData<string, string, string> HostEffectCases()
        => new()
        {
            // Left before right, one execution per evaluated operand, none for a skipped one.
            { "see('L', false) and see('R', true)", "ok false", "L" },
            { "see('L', true) and see('R', false)", "ok false", "L,R" },
            { "see('L', true) and see('R', true)", "ok true", "L,R" },
            { "see('L', true) or see('R', false)", "ok true", "L" },
            { "see('L', false) or see('R', true)", "ok true", "L,R" },
            { "see('L', false) or see('R', false)", "ok false", "L,R" },
            { "see('A', true) and see('B', false) and see('C', true)", "ok false", "A,B" },
            { "see('A', false) or see('B', true) or see('C', true)", "ok true", "A,B" },
            { "see('A', false) and see('B', true) or see('C', true)", "ok true", "A,C" },
            // A non-Boolean left operand is rejected before the effectful right operand runs.
            { "see('L', 1) and see('R', true)", "err TypeMismatch", "L" },
            { "see('L', 'x') or see('R', true)", "err TypeMismatch", "L" },
            // A failing left operand is the outcome; the right operand never runs.
            { "see('L', 1) / 0 > 0 and see('R', true)", "err DivisionByZero", "L" },
            { "see('L', 1) / 0 > 0 or see('R', true)", "err DivisionByZero", "L" },
            // A non-Boolean right operand: rejected when evaluated, never executed when skipped.
            { "see('L', true) and see('R', 1)", "err TypeMismatch", "L,R" },
            { "see('L', false) or see('R', 1)", "err TypeMismatch", "L,R" },
            { "see('L', false) and see('R', 1)", "ok false", "L" },
            { "see('L', true) or see('R', 1)", "ok true", "L" },
            // Control: `xor` runs both operands, left then right, before it judges either.
            { "see('L', true) xor see('R', true)", "ok false", "L,R" },
            { "see('L', false) xor see('R', true)", "ok true", "L,R" },
            { "see('L', 1) xor see('R', true)", "err TypeMismatch", "L,R" },
            { "see('L', true) xor see('R', 1)", "err TypeMismatch", "L,R" },
        };

    [Theory]
    [MemberData(nameof(HostEffectCases))]
    public void HostEffects_SynchronousRoute_RunOnlyTheEvaluatedOperands(string source, string outcome, string calls)
    {
        var trace = new HostTrace();
        var result = KatLangEngine.Run(source, new RunOptions { HostOperations = SynchronousSee(trace) });

        Assert.Equal(outcome, Outcome(result));
        Assert.Equal(calls, trace.Calls);
    }

    [Theory]
    [MemberData(nameof(HostEffectCases))]
    public async Task HostEffects_SuspendingAsyncRoute_RunOnlyTheEvaluatedOperands(string source, string outcome, string calls)
    {
        var trace = new HostTrace();
        var result = await AsyncEvaluationHarness.Complete(new ValueTask<RunResult>(
            KatLangEngine.RunAsync(source, new RunOptions { HostOperations = SuspendingSee(trace) })));

        Assert.Equal(outcome, Outcome(result));
        Assert.Equal(calls, trace.Calls);
    }

    /// <summary>
    /// A deterministically gated asynchronous operand: it reports when evaluation reached it
    /// (and is therefore suspended awaiting the gate) and completes only when released.
    /// </summary>
    private sealed class HeldOperand
    {
        private readonly TaskCompletionSource<Result> _gate = new(TaskCreationOptions.RunContinuationsAsynchronously);
        private readonly TaskCompletionSource _reached = new(TaskCreationOptions.RunContinuationsAsynchronously);
        private int _invocations;

        public int Invocations => Volatile.Read(ref _invocations);

        public Task Reached => _reached.Task;

        public void Release(bool value) => _gate.TrySetResult(new Result.Bool(value));

        public async ValueTask<Result> InvokeAsync(IReadOnlyList<Result> args, CancellationToken cancellationToken)
        {
            Interlocked.Increment(ref _invocations);
            _reached.TrySetResult();
            return await _gate.Task.ConfigureAwait(false);
        }
    }

    private static readonly TimeSpan GateTimeout = TimeSpan.FromSeconds(45);

    private static async Task AssertReached(Task reached)
        => Assert.Same(reached, await Task.WhenAny(reached, Task.Delay(GateTimeout)));

    private static async Task<RunResult> AssertCompletes(Task<RunResult> run)
    {
        Assert.Same(run, await Task.WhenAny(run, Task.Delay(GateTimeout)));
        return await run;
    }

    [Theory]
    [InlineData("Left() and Right()", false, "false")]
    [InlineData("Left() or Right()", true, "true")]
    public async Task HeldLeftOperand_ThatDecides_CompletesWithoutEverReachingTheRightOperand(
        string source, bool leftValue, string display)
    {
        var left = new HeldOperand();
        var right = new HeldOperand();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Left", left.InvokeAsync),
                HostOperation.CreateAsync("Right", right.InvokeAsync)),
        };

        var run = KatLangEngine.RunAsync(source, options);

        // The run is genuinely suspended at the left operand, and the right one has not started.
        await AssertReached(left.Reached);
        Assert.False(run.IsCompleted);
        Assert.Equal(0, right.Invocations);

        left.Release(leftValue);
        var result = Assert.IsType<RunResult.Success>(await AssertCompletes(run));

        Assert.Equal(display, result.ToDisplayString());
        Assert.Equal(1, left.Invocations);
        Assert.Equal(0, right.Invocations);
        Assert.False(right.Reached.IsCompleted);
    }

    [Theory]
    [InlineData("Left() and Right()", true, false, "false")]
    [InlineData("Left() and Right()", true, true, "true")]
    [InlineData("Left() or Right()", false, true, "true")]
    [InlineData("Left() or Right()", false, false, "false")]
    [InlineData("Left() xor Right()", true, true, "false")]
    [InlineData("Left() xor Right()", false, true, "true")]
    public async Task HeldLeftOperand_ThatDoesNotDecide_ThenSuspendsAtTheRightOperandOnce(
        string source, bool leftValue, bool rightValue, string display)
    {
        var left = new HeldOperand();
        var right = new HeldOperand();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Left", left.InvokeAsync),
                HostOperation.CreateAsync("Right", right.InvokeAsync)),
        };

        var run = KatLangEngine.RunAsync(source, options);

        await AssertReached(left.Reached);
        Assert.False(run.IsCompleted);
        Assert.Equal(0, right.Invocations);

        // Left before right: the right operand starts only after the left one has a value.
        left.Release(leftValue);
        await AssertReached(right.Reached);
        Assert.False(run.IsCompleted);

        right.Release(rightValue);
        var result = Assert.IsType<RunResult.Success>(await AssertCompletes(run));

        Assert.Equal(display, result.ToDisplayString());
        Assert.Equal(1, left.Invocations);
        Assert.Equal(1, right.Invocations);
    }

    // ── Diagnostics: error kinds, blame, and spans ──────────────────────────

    private static async Task<EvalError> FailureOn(string route, string source)
    {
        var result = await RunOn(route, source);
        Assert.True(result.IsError, $"`{source}` unexpectedly succeeded on {route}");
        return result.Error;
    }

    public static TheoryData<string> RouteNames()
    {
        var data = new TheoryData<string>();
        foreach (var route in Routes)
            data.Add(route);
        return data;
    }

    [Theory]
    [MemberData(nameof(RouteNames))]
    public async Task NonBooleanLeftOperand_IsRejectedAtTheWholeExpression_BeforeTheRightOperand(string route)
    {
        // The right operand would fail if it ran: the left operand's rejection is the outcome.
        const string source = "1 and 1 / 0 > 0";
        var error = await FailureOn(route, source);

        var mismatch = Assert.IsType<EvalError.TypeMismatch>(Innermost(error));
        Assert.Equal("operator `and` expects Boolean operands, but the left operand was numeric value 1", mismatch.Message);
        Assert.Equal(["while evaluating `1 and 1 / 0 > 0`"], ContextChain(error));
        Assert.Equal(KatLangErrorCode.TypeMismatch, KatLangError.FromEvalError(error).Code);
        Assert.Equal(new SourceSpan(1, 1, 1, source.Length + 1), Span(error));
    }

    [Theory]
    [MemberData(nameof(RouteNames))]
    public async Task NonBooleanRightOperand_WhenEvaluated_IsTheOrdinaryRightOperandRejection(string route)
    {
        foreach (var (source, op, blame) in new[]
        {
            ("true and 1", "and", "numeric value 1"),
            ("false or 'x'", "or", "a string: 'x'"),
            ("true and ()", "and", "a sequence value with 0 sequence elements: ()"),
            ("false or [true]", "or", "a list value with 1 element: [true]"),
        })
        {
            var error = await FailureOn(route, source);

            var mismatch = Assert.IsType<EvalError.TypeMismatch>(Innermost(error));
            Assert.Equal($"operator `{op}` expects Boolean operands, but the right operand was {blame}", mismatch.Message);
            Assert.Equal([$"while evaluating `{source}`"], ContextChain(error));
            Assert.Equal(KatLangErrorCode.TypeMismatch, KatLangError.FromEvalError(error).Code);
            Assert.Equal(new SourceSpan(1, 1, 1, source.Length + 1), Span(error));
        }
    }

    [Theory]
    [MemberData(nameof(RouteNames))]
    public async Task FailingOperand_KeepsItsOwnErrorKindAndSpan(string route)
    {
        // An evaluated right operand's failure is located at that operand's failing division.
        foreach (var (source, column) in new[]
        {
            ("true and 1 / 0 > 0", 10),
            ("false or 1 / 0 > 0", 10),
            ("false xor 1 / 0 > 0", 11),
            // The left operand's failure, at the left operand; the right one never runs.
            ("1 / 0 > 0 and 2 / 0 > 0", 1),
            ("1 / 0 > 0 or 2 / 0 > 0", 1),
        })
        {
            var error = await FailureOn(route, source);

            Assert.IsType<EvalError.DivByZero>(Innermost(error));
            Assert.Empty(ContextChain(error));
            Assert.Equal(KatLangErrorCode.DivisionByZero, KatLangError.FromEvalError(error).Code);
            Assert.Equal(new SourceSpan(1, column, 1, column + "1 / 0".Length), Span(error));
        }
    }

    [Theory]
    [InlineData("1 and 1 / 0 > 0")]
    [InlineData("true and 1")]
    [InlineData("false or 'x'")]
    [InlineData("true and 1 / 0 > 0")]
    [InlineData("1 / 0 > 0 or true")]
    [InlineData("L = 1\nR = true\nL and R")]
    [InlineData("L = true\nR = 1\nL and R")]
    [InlineData("F(a, b) = a or b\nF(false, 1 / 0 > 0)")]
    public async Task ErrorTree_IsIdenticalOnEveryRoute(string source)
    {
        var expected = DescribeErrorTree(await FailureOn("sync-generic", source));
        foreach (var route in Routes)
            Assert.Equal(expected, DescribeErrorTree(await FailureOn(route, source)));
    }

    // ── The shared decision ─────────────────────────────────────────────────

    [Fact]
    public void LeftOperandDecides_IsFalseForAnd_TrueForOr_AndNeverForTheOtherOperators()
    {
        Assert.True(Evaluator.LeftOperandDecides(BinaryOp.And, left: false));
        Assert.False(Evaluator.LeftOperandDecides(BinaryOp.And, left: true));
        Assert.True(Evaluator.LeftOperandDecides(BinaryOp.Or, left: true));
        Assert.False(Evaluator.LeftOperandDecides(BinaryOp.Or, left: false));
        foreach (var op in Enum.GetValues<BinaryOp>().Where(static op => op is not (BinaryOp.And or BinaryOp.Or)))
        {
            Assert.False(Evaluator.LeftOperandDecides(op, left: true));
            Assert.False(Evaluator.LeftOperandDecides(op, left: false));
        }
    }

    [Fact]
    public void PostLeftDecision_AnswersForAndOrOnly_AndAgreesWithApplication()
    {
        var left = new Expr.BoolLiteral(true);
        var right = new Expr.Num(1);
        Result yes = new Result.Bool(true), no = new Result.Bool(false), number = new Result.Atom(1);

        // Decided: the result is the left Boolean.
        Assert.Equal(no, Evaluator.DecideLogicalAfterLeftOperand(BinaryOp.And, left, right, no, span: null)!.Value.Value, Result.ValueComparer);
        Assert.Equal(yes, Evaluator.DecideLogicalAfterLeftOperand(BinaryOp.Or, left, right, yes, span: null)!.Value.Value, Result.ValueComparer);
        // Not decided: the right operand is needed.
        Assert.Null(Evaluator.DecideLogicalAfterLeftOperand(BinaryOp.And, left, right, yes, span: null));
        Assert.Null(Evaluator.DecideLogicalAfterLeftOperand(BinaryOp.Or, left, right, no, span: null));
        // A non-Boolean left operand of `and` / `or` is rejected here, before the right operand.
        Assert.IsType<EvalError.TypeMismatch>(
            Innermost(Evaluator.DecideLogicalAfterLeftOperand(BinaryOp.And, left, right, number, span: null)!.Value.Error));
        Assert.IsType<EvalError.TypeMismatch>(
            Innermost(Evaluator.DecideLogicalAfterLeftOperand(BinaryOp.Or, left, right, number, span: null)!.Value.Error));
        // `xor` and the arithmetic operators have no post-left decision, whatever the left value.
        foreach (var op in Enum.GetValues<BinaryOp>().Where(static op => op is not (BinaryOp.And or BinaryOp.Or)))
        foreach (var value in new[] { yes, no, number })
            Assert.Null(Evaluator.DecideLogicalAfterLeftOperand(op, left, right, value, span: null));

        // Application judges the left operand by the same rule: a deciding left operand is the
        // result whatever the right value is, so scheduling and application cannot disagree.
        Assert.Equal(no, Evaluator.ApplyBinaryOperator(BinaryOp.And, left, right, no, number, span: null).Value, Result.ValueComparer);
        Assert.Equal(yes, Evaluator.ApplyBinaryOperator(BinaryOp.Or, left, right, yes, number, span: null).Value, Result.ValueComparer);
        Assert.True(Evaluator.ApplyBinaryOperator(BinaryOp.And, left, right, yes, number, span: null).IsError);
        Assert.True(Evaluator.ApplyBinaryOperator(BinaryOp.Xor, left, right, yes, number, span: null).IsError);
    }

    // ── Planned loops ───────────────────────────────────────────────────────

    /// <summary>
    /// Proves the optimized run evaluated the expression through the loop PLAN: the loop is
    /// optimized, the slot is planned with the expected plan summary, and nothing in the loop
    /// fell back to the generic evaluator.
    /// </summary>
    private static void AssertPlannedSlot(
        LoopOptimizationDiagnosticsSnapshot loop,
        string planIdentity,
        string role,
        int? index,
        string planSummary)
    {
        Assert.Equal(1, loop.OptimizedLoopHits);
        Assert.Equal(0, loop.OptimizedLoopFallbacks);
        var plan = Assert.Single(loop.LoopPlans, candidate => candidate.Identity == planIdentity);
        Assert.True(plan.Optimized, $"Expected an optimized plan, got fallback: {plan.FallbackReason}");
        var slot = Assert.Single(plan.Expressions, expression => expression.Role == role && expression.Index == index);
        Assert.True(slot.Planned, $"Expected a planned slot, got fallback: {slot.FallbackReason}");
        Assert.Equal(planSummary, slot.PlanSummary);
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);
    }

    /// <summary>
    /// <c>Use(d)</c> runs ONE round of a step whose only row is the guard
    /// <c>d != 0 and 12 / d > x</c> over the captured parameter <c>d</c> and the state
    /// <c>x</c> (initially 2).
    /// </summary>
    private static string GuardLoop(string denominator)
        => $$"""
            Use(d) = {
                S(x) = d != 0 and 12 / d > x
                repeat(S(2), 1)
            }
            Use({{denominator}})
            """;

    private const string GuardPlan =
        "And(NotEqual(CapturedSlot(d), Const(0)), GreaterThan(Divide(Const(12), CapturedSlot(d)), StateSlot(x)))";

    [Theory]
    // d = 0: the guard's left operand is false, so the division never runs. Planned operations:
    // the `!=` link and the `and`.
    [InlineData("0", false, 2)]
    // d = 4 and d = 12: the right operand runs — `!=`, `/`, `>` and the `and`.
    [InlineData("4", true, 4)]
    [InlineData("12", false, 4)]
    public void PlannedLoop_GuardWithZeroDenominator_SkipsTheRightOperandPlan(string denominator, bool expected, int plannedOperations)
    {
        var source = GuardLoop(denominator);

        var (generic, genericLoop) = RunCountedObserved(source, enableLoopOptimization: false);
        var (optimized, loop) = RunCountedObserved(source, enableLoopOptimization: true);

        Assert.False(generic.IsError, $"Expected generic success but got: {(generic.IsError ? generic.Error : null)}");
        Assert.False(optimized.IsError, $"Expected optimized success but got: {(optimized.IsError ? optimized.Error : null)}");
        Assert.Equal(new Result.Bool(expected), generic.Value.Value, Result.ValueComparer);
        Assert.Equal(new Result.Bool(expected), optimized.Value.Value, Result.ValueComparer);
        Assert.Equal(generic.Value.EmittedCount, optimized.Value.EmittedCount);

        // The generic run used no plan; the optimized run evaluated the guard through its plan,
        // and the planned operation count shows the right operand's plan was not entered.
        Assert.Equal(0, genericLoop.OptimizedLoopHits);
        AssertPlannedSlot(loop, "Use.S.repeat", "output", 0, GuardPlan);
        Assert.Equal(1, loop.LoopIterations);
        Assert.Equal(plannedOperations, loop.PlannedBuiltinOperations);
    }

    public static TheoryData<string, string, string> PlannedLoopPrograms()
        => new()
        {
            // A `while` continuation guard: at s = 5 the left operand is false and `60 / 0` is skipped.
            { "while-continuation-guard", "Step(s) = s + 1, s < 5 and 60 / (5 - s) > 0\nwhile(Step(0))", "ok raw=5 n=1" },
            // `or` in a next-state row: at s = 3 the left operand is true and `6 / 0` is skipped.
            { "repeat-or-guard", "Step(s, b) = s + 1, s == 3 or 6 / (3 - s) > 0\nrepeat(Step(0, true), 6)", "ok raw=S[6, false] n=1" },
            // A local property read only by the skipped operand is never evaluated.
            { "skipped-temp", "Use(d) = {\n    S(x) = {\n        Risky = 12 / d\n        d != 0 and Risky > x\n    }\n    repeat(S(2), 1)\n}\nUse(0)", "ok raw=false n=1" },
            // A parameter read only by the skipped operand is never demanded.
            { "skipped-parameter", "F(k) = {\n    S(x) = x > 100 and k > 0\n    S(0).repeat(1)\n}\nF(1 / 0)", "ok raw=false n=1" },
            // Nested logical operators in a planned `if` condition: s = 2 skips `12 / 0`; the
            // condition holds at s = 0 (the `or`), and at s = 3, 4, 5 (12, 6 and 4 exceed 3).
            { "if-condition", "Step(s, t) = s + 1, if(s > 2 and 12 / (s - 2) > 3 or s == 0, t + 1, t)\nrepeat(Step(0, 0), 8)", "ok raw=S[8, 4] n=1" },
            // An evaluated right operand still fails, identically on both strategies.
            { "evaluated-right-fails", "Step(s) = s + 1, s < 5 and 60 / (4 - s) > 0\nwhile(Step(0))", "err div0" },
            // A non-Boolean left operand is rejected before the right operand's failure.
            { "left-kind-before-right-failure", "Step(s, b) = s + 1, s and 1 / 0 > 0\nrepeat(Step(0, true), 2)", "err type" },
            // Control: `xor` is eager in a planned loop too.
            { "xor-control", "Step(s, b) = s + 1, b xor 6 / (3 - s) > 0\nrepeat(Step(0, true), 6)", "err div0" },
        };

    [Theory]
    [MemberData(nameof(PlannedLoopPrograms))]
    public void PlannedLoop_AgreesWithTheGenericRoute_InOutcomeAndAccounting(string id, string source, string expected)
    {
        var (generic, genericLoop) = RunCountedObserved(source, enableLoopOptimization: false);
        var (optimized, optimizedLoop) = RunCountedObserved(source, enableLoopOptimization: true);

        Assert.Equal(expected, Outcome(generic));
        Assert.Equal(expected, Outcome(optimized));
        if (generic.IsError)
            Assert.Equal(DescribeErrorTree(generic.Error), DescribeErrorTree(optimized.Error));

        // The planned strategy was taken — and nothing of the step fell back to the generic
        // evaluator — so the optimized outcome above is the loop plan's.
        Assert.Equal(0, genericLoop.OptimizedLoopHits);
        Assert.True(optimizedLoop.OptimizedLoopHits > 0, $"{id}: the planned loop strategy was not taken");
        Assert.Equal(0, optimizedLoop.PlannedExpressionFallbacks);
        Assert.Equal(0, optimizedLoop.GenericExpressionEvaluationsInsideOptimizedLoops);

        // It charged exactly the generic steps and expression checkpoints: a skipped operand
        // charges nothing on either strategy.
        var genericAccounting = StrategyNeutralBudgetParityTests.Observe(source, optimize: false);
        var optimizedAccounting = StrategyNeutralBudgetParityTests.Observe(source, optimize: true);
        Assert.True(optimizedAccounting.LoopHits > 0);
        Assert.Equal(genericAccounting.Accounting, optimizedAccounting.Accounting);
    }

    [Theory]
    [MemberData(nameof(PlannedLoopPrograms))]
    public void PlannedLoop_StepBudgetSweep_FailsAtTheSamePointAsTheGenericRoute(string id, string source, string expected)
    {
        Assert.False(string.IsNullOrEmpty(expected));
        var unlimited = StrategyNeutralBudgetParityTests.Observe(source, optimize: false);
        foreach (var budget in StrategyNeutralBudgetParityTests.StepBudgets(unlimited.Steps))
        {
            var limits = new EvaluationLimits { MaxSteps = budget };
            var generic = StrategyNeutralBudgetParityTests.Observe(source, optimize: false, limits);
            var optimized = StrategyNeutralBudgetParityTests.Observe(source, optimize: true, limits);
            Assert.True(
                generic.Accounting == optimized.Accounting,
                $"{id} MaxSteps={budget}:\n--- generic\n{generic.Accounting}\n--- optimized\n{optimized.Accounting}");
        }
    }

    [Fact]
    public void PlannedLoop_SkippedOperand_ChargesFewerCheckpointsThanAnEvaluatedOne()
    {
        // The same step with a left operand that decides (d = 0) and one that does not (d = 4):
        // the deciding run is the cheaper one, on both strategies, by the same amount.
        var skippedGeneric = StrategyNeutralBudgetParityTests.Observe(GuardLoop("0"), optimize: false);
        var skippedPlanned = StrategyNeutralBudgetParityTests.Observe(GuardLoop("0"), optimize: true);
        var evaluatedGeneric = StrategyNeutralBudgetParityTests.Observe(GuardLoop("4"), optimize: false);
        var evaluatedPlanned = StrategyNeutralBudgetParityTests.Observe(GuardLoop("4"), optimize: true);

        Assert.True(skippedPlanned.LoopHits > 0);
        Assert.True(evaluatedPlanned.LoopHits > 0);
        Assert.Equal(skippedGeneric.Checkpoints, skippedPlanned.Checkpoints);
        Assert.Equal(evaluatedGeneric.Checkpoints, evaluatedPlanned.Checkpoints);
        Assert.True(
            skippedGeneric.Checkpoints < evaluatedGeneric.Checkpoints,
            $"skipped {skippedGeneric.Checkpoints} must be below evaluated {evaluatedGeneric.Checkpoints}");
    }

    [Fact]
    public void PlannedLoop_NonBooleanLeftOperand_ReportsTheGenericDiagnosticThroughThePlan()
    {
        const string source = """
            Use(value) = {
                S(x) = value and 1 / 0 > x
                repeat(S(0), 1)
            }
            Use(7)
            """;

        var error = AssertOptimizerTransparentFailure(source);

        var mismatch = Assert.IsType<EvalError.TypeMismatch>(Innermost(error));
        Assert.Equal("operator `and` expects Boolean operands, but the left operand was numeric value 7", mismatch.Message);
        Assert.Equal("while evaluating `value and 1 / 0 > x`", ContextChain(error)[^1]);

        var (_, loop) = RunCountedObserved(source, enableLoopOptimization: true);
        AssertPlannedSlot(
            loop,
            "Use.S.repeat",
            "output",
            0,
            "And(CapturedSlot(value), GreaterThan(Divide(Const(1), Const(0)), StateSlot(x)))");
        // The one planned operation is the `and` that rejected its left operand: the right
        // operand's division and comparison never ran.
        Assert.Equal(1, loop.PlannedBuiltinOperations);
    }

    [Fact]
    public void PlannedLoop_HostEffectInASkippedOperand_NeverRuns_OnEitherStrategy()
    {
        // `trace` is a host operation, so its row is a generic fallback inside the optimized
        // loop: the generic machine short-circuits there exactly as it does outside a loop.
        const string source = "Step(s, t) = s + 1, s > 2 and trace(s) > 3\nrepeat(Step(0, true), 6)";

        var generic = StrategyNeutralBudgetParityTests.Observe(source, optimize: false);
        var optimized = StrategyNeutralBudgetParityTests.Observe(source, optimize: true);

        // s = 0, 1, 2: skipped. s = 3, 4, 5: evaluated once each, in order.
        Assert.Equal("trace(3),trace(4),trace(5)", generic.HostTrace);
        Assert.Equal("ok S[6, true] n=1", generic.Outcome);
        Assert.True(optimized.LoopHits > 0);
        Assert.Equal(generic.Accounting, optimized.Accounting);
    }
}
