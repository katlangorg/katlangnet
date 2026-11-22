using System.Diagnostics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// Process-isolated regressions proving that evaluator re-entry recursion is bounded by
/// the budget chokepoints. Before the depth-charged argument-evaluation chokepoint
/// (<c>EvaluationBudget.TryEnterArgumentEvaluation</c>), a zero-parameter property
/// reaching itself through a builtin argument (<c>A = count(A)</c>,
/// <c>A = range(1, A)</c>, <c>A = if(true, A, 0)</c>, a loop's initial state or count)
/// terminated the whole process with an uncatchable
/// <see cref="StackOverflowException"/>. An in-process test cannot observe that
/// failure mode safely, so a child process runs the worst spellings, asserts the
/// structured resource error, writes a success marker, and exits normally.
/// Follows the subprocess convention of <see cref="AstStructuralDepthProcessTests"/>.
/// </summary>
public class EvaluationLimitsProcessTests
{
    private const string ProbeChildEnvironment = "KATLANG_EVALUATION_LIMITS_PROBE_CHILD";
    private const string ProbeMarkerFileEnvironment = "KATLANG_EVALUATION_LIMITS_PROBE_MARKER_FILE";
    private const string ProbeSuccessMarker = "katlang-evaluation-limits-recursion-ok";

    [Fact]
    public async Task BuiltinArgumentRecursion_IsStructurallyBounded_InSubprocess()
        => await RunProbeChild("BuiltinArgumentRecursion_ProbeChild");

    [Fact]
    public async Task ResolvedValueDemandRecursion_IsStructurallyBounded_InSubprocess()
        => await RunProbeChild("ResolvedValueDemandRecursion_ProbeChild");

    [Fact]
    public async Task PlannedLoopUnderRecursion_IsStructurallyBounded_InSubprocess()
        => await RunProbeChild("PlannedLoopUnderRecursion_ProbeChild");

    [Fact]
    public async Task DeepErrorContextCode_IsStackSafe_InSubprocess()
        => await RunProbeChild(nameof(DeepErrorContextCode_ProbeChild));

    /// <summary>
    /// PV-07 / Q-09b, the host-stack half: a limit the run does not reach must not change
    /// whether the host-stack backstop stops it ON THE SAME HOST. Runs in a child process with
    /// tiered compilation OFF, so frame sizes are fixed for the whole probe (in a tiering
    /// process the same run on the same thread can flip from failure to success as its code is
    /// recompiled — which is host variability, Q-09a, not a configuration effect).
    /// </summary>
    [Fact]
    public async Task NonBindingLimits_KeepTheHostStackOutcome_InSubprocess()
        => await RunProbeChild(
            nameof(NonBindingLimits_KeepTheHostStackOutcome_ProbeChild),
            new Dictionary<string, string> { ["DOTNET_TieredCompilation"] = "0" });

    /// <summary>
    /// For each PV-07 witness the probe FINDS — never hard-codes — the least stack headroom
    /// (64 KiB granularity) with which the UNCONFIGURED run completes, then requires every
    /// non-binding limit configuration (<see cref="LimitConfigurationTransparencyTests.NonBindingConfigurations"/>)
    /// to complete with exactly that headroom with the same value, and to stop exactly like the
    /// unconfigured run one granule below it. Before Q-09b a configured <c>MaxSteps</c>,
    /// <c>MaxMaterializedItems</c>, <c>MaxStringLength</c> (even at its default) or
    /// <c>MaxMaterializedStringChars</c> switched loop planning and/or sequence fusion off, and the
    /// generic strategies need MORE stack for a fused-pipeline recursion (W1) and a loop at the
    /// bottom of a recursion, LESS for recursion routed through a loop step — so the first check
    /// failed for the first two witnesses and the second for the third.
    /// <para>"The same host" is ONE probe thread: every run executes on it, below a padding frame
    /// that consumes all but the given headroom of its fixed stack, so equal headroom means the
    /// same stack pointer against the same stack limit. Threads that merely REQUEST the same stack
    /// size are not the same host (Q-09a): glibc can give a new thread a cached stack up to four
    /// times the requested size, and a new thread's first frame lands at a varying depth. A former
    /// thread-per-run search failed on Linux CI that way: a reused larger stack satisfied its
    /// "minimum", and the re-run, on a stack of exactly that size, stopped.</para>
    /// </summary>
    [Fact]
    public void NonBindingLimits_KeepTheHostStackOutcome_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        const int granuleKiB = 64;
        // The probe thread's stack; a run's headroom is what its padding leaves of it.
        const int stackGranules = 16 * 1024 / granuleKiB;
        // The search never goes below this floor: these witnesses have shallow SOURCE (every
        // recursion level crosses a probing chokepoint), and the floor stays clear of the
        // sub-minimum headroom where deeply nested source was once seen to overflow between probes.
        const int floorGranules = 6;
        var step10 = "Step(s) = {\n" + string.Concat(Enumerable.Range(1, 10).Select(i => $"  T{i} = {(i == 1 ? "s" : $"T{i - 1}")} + 1\n")) + "  T10\n}\n";
        var witnesses = new[]
        {
            // W1: recursion through a fused filter predicate.
            "R(n) = if(n > 0, range(n, n).filter({ R(x - 1) >= 0 }).count, 0)\nR(30)",
            // rc_10_50: a planned ten-temp loop at the bottom of a recursion.
            step10 + "R(n) = if(n > 0, R(n - 1), repeat(Step(0), 2))\nR(50)",
            // looprec: recursion routed through a loop step (the generic loop used LESS stack).
            "S(s) = R(s - 1)\nR(n) = if(n > 0, repeat(S(n), 1), 0)\nR(25)",
        };

        // The run with `headroomGranules` of the probe thread's stack left to it: this frame's
        // padding consumes the rest. With tiering off, the outcome is a function of the headroom.
        [MethodImpl(MethodImplOptions.NoInlining)]
        static string Outcome(string source, EvaluationLimits? limits, int headroomGranules)
        {
            Span<byte> padding = stackalloc byte[(stackGranules - headroomGranules) * granuleKiB * 1024 + 1];
            padding[0] = 1;
            var result = KatLangEngine.Run(source, new RunOptions { EvaluationLimits = limits });
            var outcome = result switch
            {
                RunResult.Success => "ok " + result.ToDisplayString(),
                RunResult.EvalFailure failure => "err " + Assert.Single(failure.Errors).Code,
                _ => result.GetType().Name,
            };
            // Read after the run, so the padding stays allocated across it.
            Assert.Equal(1, padding[0]);
            return outcome;
        }

        AstStructuralDepthProcessTests.RunOnThreadWithStack(stackGranules * granuleKiB * 1024, () =>
        {
            foreach (var witness in witnesses)
            {
                // The least headroom with which the unconfigured run completes (outcomes are
                // monotone in the headroom: more never stops a run that completed).
                int low = floorGranules, high = stackGranules;
                Assert.StartsWith("ok ", Outcome(witness, null, high));
                while (low < high)
                {
                    var middle = (low + high) / 2;
                    if (Outcome(witness, null, middle).StartsWith("ok ", StringComparison.Ordinal))
                        high = middle;
                    else
                        low = middle + 1;
                }

                var minimumKiB = high * granuleKiB;
                var completed = Outcome(witness, null, high);
                Assert.StartsWith("ok ", completed);
                foreach (var (name, limits) in LimitConfigurationTransparencyTests.NonBindingConfigurations)
                {
                    Assert.True(
                        completed == Outcome(witness, limits, high),
                        $"{name} changed the outcome with the {minimumKiB} KiB of headroom the unconfigured run completes with:\n{witness}");
                }

                // The symmetric half: one granule below, where the unconfigured run stops, no
                // configuration may complete instead. (Skipped only if a build's frames are so small
                // that the witness completes at the search floor.)
                if (high == floorGranules)
                    continue;
                var stopped = Outcome(witness, null, high - 1);
                Assert.Equal("err EvaluationStackExhausted", stopped);
                foreach (var (name, limits) in LimitConfigurationTransparencyTests.NonBindingConfigurations)
                {
                    Assert.True(
                        stopped == Outcome(witness, limits, high - 1),
                        $"{name} changed the outcome with the {minimumKiB - granuleKiB} KiB of headroom the unconfigured run stops with:\n{witness}");
                }
            }
        });

        WriteProbeMarker();
    }

    [Fact]
    public async Task HostStackStops_ChargeTheGenericPrefix_OnEveryRoute_InSubprocess()
        => await RunProbeChild(nameof(HostStackStops_ChargeTheGenericPrefix_OnEveryRoute_ProbeChild));

    /// <summary>
    /// Q-09a and Q-09b at the host-stack backstop itself (S3/L9). Unbounded recursions stop at a
    /// route-dependent depth — the forced async twin's frames are larger, so on the same stack it
    /// stops at roughly half the synchronous depth (the historical LOOP-CF1 x5 witness: 122
    /// synchronous steps against 59 on the twin). Those different <c>ConsumedSteps</c> are
    /// permitted variability: the runs stopped at different points. What must NOT differ is the
    /// charge for the same logical prefix, so wherever a route stops, its counters must lie on
    /// the generic strategy's accounting trajectory: with <c>s</c> steps consumed, its expression
    /// checkpoints fall between those of the generic run refused at invocation <c>s</c> and at
    /// invocation <c>s + 1</c> (a step budget of <c>s - 1</c> and <c>s</c>), measured on a roomy
    /// stack. No stopping depth is asserted. A budget that binds before every route's stop gives
    /// every route the identical verdict and counters, the depth scopes are balanced, and the
    /// failure is terminal: the row after the recursion never runs.
    /// </summary>
    [Fact]
    public void HostStackStops_ChargeTheGenericPrefix_OnEveryRoute_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        string[] witnesses =
        [
            "P = P + 1\nP",
            "F(n) = F(n + 1) + 1\nF(0)",
            "G(a) = a\nF(n) = G(F(n + 1))\nF(0)",
            "F(n) = sum(map([n + 1], F))\nF(0)",
            "S(x) = {\nP = P + 1\nP, x < 1\n}\nS(0).while",
            "P = P + 1\nmark(1), P, mark(2)",
        ];
        string[] routes = ["generic", "planned", "twin"];

        (EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget, string Effects) Run(
            string source, string route, EvaluationLimits? limits)
        {
            var effects = new List<string>();
            var operations = HostOperations.Create(HostOperation.Create("mark", (args, _) =>
            {
                effects.Add(SemanticExplorerHarness.Neutral(args[0]));
                return args[0];
            }, "value"));
            var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
            Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
            var program = new Expr.AlgorithmExpr(parsed.Root);
            var (result, budget) = route == "twin"
                ? Evaluator.RunCountedObservedAsync(
                    program,
                    limits,
                    zeroArgPropertyResultCache: new AsyncEvaluation.PassThroughAsyncZeroArgPropertyResultCache(),
                    hostOperations: operations).AsTask().GetAwaiter().GetResult()
                : Evaluator.RunCountedObserved(program, limits, enableOptimizations: route == "planned", hostOperations: operations);
            return (result, budget, string.Join(",", effects));
        }

        static string Describe(EvalResult<Evaluator.CountedResult> result, EvaluationBudget budget)
            => (result.IsError ? LoopDiagnosticParityAssertions.DescribeErrorTree(result.Error) : SemanticExplorerHarness.Neutral(result.Value.Value))
                + $" steps={budget.ConsumedSteps} checkpoints={budget.ConsumedExpressionCheckpoints} peak={budget.PeakDepth}";

        foreach (var witness in witnesses)
        {
            // Each route's unconfigured stop, on the documented minimum 1 MiB stack.
            var stops = new Dictionary<string, (long Steps, long Checkpoints)>();
            AstStructuralDepthProcessTests.RunOnThreadWithStack(1_048_576, () =>
            {
                foreach (var route in routes)
                {
                    var (result, budget, effects) = Run(witness, route, limits: null);
                    Assert.True(result.IsError, $"{route} completed an unbounded recursion:\n{witness}");
                    var leaf = result.Error;
                    while (leaf is EvalError.WithContext(_, var inner))
                        leaf = inner;
                    Assert.True(
                        leaf is EvalError.EvaluationStackExhausted or EvalError.EvaluationDepthExceeded,
                        $"{route} stopped with {leaf.GetType().Name}:\n{witness}");
                    Assert.Equal(0, budget.CurrentDepth);
                    if (witness.Contains("mark", StringComparison.Ordinal))
                        Assert.Equal("1", effects);
                    stops[route] = (budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints);
                }
            });

            // The generic accounting trajectory, on a stack roomy enough that only the step
            // budget binds (the deterministic depth ceiling exceeds every step budget used here).
            AstStructuralDepthProcessTests.RunOnThreadWithStack(16 * 1_048_576, () =>
            {
                long CheckpointsRefusedAt(long invocation)
                {
                    var (result, budget, _) = Run(witness, "generic", new EvaluationLimits { MaxSteps = invocation - 1 });
                    var leaf = result.Error;
                    while (leaf is EvalError.WithContext(_, var inner))
                        leaf = inner;
                    Assert.IsType<EvalError.EvaluationStepLimitExceeded>(leaf);
                    Assert.Equal(invocation - 1, budget.ConsumedSteps);
                    return budget.ConsumedExpressionCheckpoints;
                }

                foreach (var (route, (steps, checkpoints)) in stops)
                {
                    var low = CheckpointsRefusedAt(steps);
                    var high = CheckpointsRefusedAt(steps + 1);
                    Assert.True(
                        low <= checkpoints && checkpoints <= high,
                        $"{route} stopped after {steps} steps with {checkpoints} checkpoints, off the generic "
                        + $"trajectory [{low}, {high}]:\n{witness}");
                }

                // A budget binding before every route's stop: identical verdicts and counters.
                var binding = Math.Max(1, stops.Values.Min(stop => stop.Steps) / 2);
                var limits = new EvaluationLimits { MaxSteps = binding };
                var (genericResult, genericBudget, _) = Run(witness, "generic", limits);
                var expected = Describe(genericResult, genericBudget);
                Assert.Contains("EvaluationStepLimitExceeded", expected, StringComparison.Ordinal);
                foreach (var route in routes)
                {
                    var (result, budget, _) = Run(witness, route, limits);
                    Assert.Equal(expected, Describe(result, budget));
                }
            });
        }

        WriteProbeMarker();
    }

    /// <summary>
    /// Recursion routed through PLANNED loop steps stops at the host-stack backstop on large threads instead of
    /// killing the process (corpus input #11176, 2026-11-20). Each level of <c>F(n) = repeat(F(n), 1)</c> runs the
    /// step's body in a new planned frame over the previous frame's value environment, and loop steps charge no
    /// depth, so <see cref="EvaluationLimits"/> documents the structured
    /// <see cref="EvalError.EvaluationStackExhausted"/> as this recursion's bound. The frames' environments used to
    /// wrap one another (<see cref="LoopValueEnvironment"/>). Every frame enumerated the whole chain in frames that
    /// no probe guards, and that recursion grows with the level while the backstop's reserve stays fixed. So a
    /// large thread overflowed first. In Debug every planned route below overflowed at 16 MiB, with and without
    /// tiered compilation. In Release the public engine did at 16 MiB, and the low-level planned route at 64 MiB, or
    /// at 16 MiB once its code was optimized (tiering off, or warm in the corpus run). A 1 MiB thread stopped in
    /// time, and the generic route never overflowed. The child runs each route on 1, 16 and 64 MiB threads, once
    /// with tiering (Tier-0 frames first) and once without. The routes are the public engine, both synchronously
    /// and through <see cref="KatLangEngine.RunAsync"/> (a synchronous configuration runs inline on the calling
    /// thread), and the planned evaluator under the corpus's step budget, which the recursion never reaches. The
    /// generic evaluator runs as the control. The evaluator probes check balanced depth and verify nested plan
    /// execution at each stack size. Q-09a leaves the point where the backstop fires to the host.
    /// </summary>
    [Theory]
    [InlineData("1")]
    [InlineData("0")]
    public async Task RecursionThroughPlannedLoopSteps_StopsAtTheBackstop_OnLargeThreads_InSubprocess(string tieredCompilation)
        => await RunProbeChild(
            nameof(RecursionThroughPlannedLoopSteps_ProbeChild),
            new Dictionary<string, string> { ["DOTNET_TieredCompilation"] = tieredCompilation });

    [Fact]
    public void RecursionThroughPlannedLoopSteps_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        const string source = "F(n)=repeat(F(n), 1)\nF(0)";
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var corpusLimits = new EvaluationLimits { MaxSteps = 200_000 };

        static void AssertBackstop(EvalResult<Evaluator.CountedResult> result, EvaluationBudget budget, string route)
        {
            Assert.True(result.IsError, $"{route} completed an unbounded recursion");
            var leaf = result.Error;
            while (leaf is EvalError.WithContext(_, var inner))
                leaf = inner;
            Assert.True(leaf is EvalError.EvaluationStackExhausted, $"{route} stopped with {leaf.GetType().Name}");
            Assert.Equal(0, budget.CurrentDepth);
        }

        static void AssertEngineBackstop(RunResult result, string route)
        {
            var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);
            Assert.True(error.Code == KatLangErrorCode.EvaluationStackExhausted, $"{route} stopped with {error.Code}: {error.Message}");
        }

        foreach (var stackMiB in new[] { 1, 16, 64 })
        {
            AstStructuralDepthProcessTests.RunOnThreadWithStack(stackMiB * 1024 * 1024, () =>
            {
                AssertEngineBackstop(KatLangEngine.Run(source), $"KatLangEngine.Run on {stackMiB} MiB");
                AssertEngineBackstop(KatLangEngine.RunAsync(source).GetAwaiter().GetResult(), $"KatLangEngine.RunAsync on {stackMiB} MiB");

                var diagnostics = new LoopOptimizationDiagnostics();
                var planned = Evaluator.RunCountedObserved(program, corpusLimits, loopDiagnostics: diagnostics);
                AssertBackstop(planned.Result, planned.Budget, $"planned on {stackMiB} MiB");
                Assert.True(diagnostics.OptimizedLoopHits > 1, $"only {diagnostics.OptimizedLoopHits} planned loop(s) on {stackMiB} MiB");

                var generic = Evaluator.RunCountedObserved(program, corpusLimits, enableOptimizations: false);
                AssertBackstop(generic.Result, generic.Budget, $"generic on {stackMiB} MiB");
            });
        }

        WriteProbeMarker();
    }

    // ── Recursion routed through loop steps: the loop-entry backstop (audit finding 1, 2026-11-21) ──

    private const string WhileOverItself = "W = while(W())\nmark(1), W(), mark(2)";
    private const string DotWhileInStep = "Countdown(x) = x - 1, Countdown(x).while > 1\nmark(1), Countdown(5).while, mark(2)";
    private const string RepeatWithForwardedCount = "F(c) = repeat(F(c), c)\nmark(1), F(1), mark(2)";
    private const string RepeatWithFreshCount = "F(n) = repeat(F(n), 1)\nmark(1), F(0), mark(2)";

    /// <summary>
    /// Unbounded recursions in which every level ENTERS A LOOP and no invocation: the step's body starts a loop
    /// over the step itself. A loop-step invocation charges a step and never depth, so nothing but the host-stack
    /// backstop bounds them on the synchronous routes. Before the loop entry probed, the first four and the
    /// family step killed the process on every route (the round kernel charges its step without a stack probe,
    /// and the loop-step row readers bypass the row funnels' probe); the fresh-count <c>repeat</c> stopped only
    /// because its literal count is a fresh need cell, whose VALUE computation happens to probe. The forwarded
    /// count and the fresh count are a matched pair: one differs from the other by that incidental probe alone.
    /// </summary>
    private static readonly (string Name, string Source)[] UnboundedLoopStepRecursions =
    [
        ("while over itself", WhileOverItself),
        ("while over a parameter", "F(n) = while(F(n))\nmark(1), F(0), mark(2)"),
        ("dot while in its own step", DotWhileInStep),
        ("repeat with a forwarded count", RepeatWithForwardedCount),
        ("repeat with a fresh count", RepeatWithFreshCount),
        ("family step", "F(0) = 0\nF(n) = repeat(F(n), n)\nmark(1), F(1), mark(2)"),
    ];

    /// <summary>
    /// A TERMINATING recursion through loop steps: each <c>while</c> round reads its flag row first, so the
    /// recursion is <paramref name="levels"/> loops deep when the run-wide <c>tick()</c> counter reaches the bound
    /// and every loop ends. Its value is <c>(0, false)</c> at every depth.
    /// </summary>
    private static string TerminatingLoopStepRecursion(int levels, string counter = "tick()")
        => $"F(n) = while(F(n)), {counter} < {levels}\nF(0)";

    private const string TerminatingLoopStepRecursionValue = "(0, false)";

    /// <summary>The same value in the evaluator routes' neutral rendering (<see cref="SemanticExplorerHarness.Neutral"/>).</summary>
    private const string TerminatingLoopStepRecursionNeutral = "S[0, false]";

    private sealed class LoopStepRecursionRun
    {
        private readonly List<string> _marks = [];
        private int _calledOnThePool;

        public LoopStepRecursionRun(string source, bool asynchronousOperation = false)
        {
            Source = source;
            var here = HostOperation.Create("here", (args, _) =>
            {
                if (Thread.CurrentThread.IsThreadPoolThread)
                    Volatile.Write(ref _calledOnThePool, 1);
                return args[0];
            }, "value");
            var mark = HostOperation.Create("mark", (args, _) =>
            {
                lock (_marks)
                    _marks.Add(SemanticExplorerHarness.Neutral(args[0]));
                return args[0];
            }, "value");
            // An asynchronous operation that is configured and never called routes the public engine through the
            // twin family (the route is chosen by capability); `yield` genuinely suspends where a program calls it.
            Operations = asynchronousOperation
                ? HostOperations.Create(mark, here, HostOperation.CreateAsync("yield", async (args, _) =>
                {
                    await Task.Yield();
                    return args[0];
                }, "value"))
                : HostOperations.Create(mark, here);
            var parsed = Parser.Parse(source, new RunOptions { HostOperations = Operations });
            Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
            Program = new Expr.AlgorithmExpr(parsed.Root);
        }

        public string Source { get; }

        public HostOperations Operations { get; }

        public Expr Program { get; }

        public string Marks
        {
            get
            {
                lock (_marks)
                    return string.Join(",", _marks);
            }
        }

        public bool CalledAnOperationOnThePool => Volatile.Read(ref _calledOnThePool) == 1;

        /// <summary>The generic or planned synchronous evaluator, or the forced twin awaited on this thread.</summary>
        public (EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget) Evaluate(
            string route, EvaluationLimits? limits = null, LoopOptimizationDiagnostics? loopDiagnostics = null)
            => route == "twin"
                ? Evaluator.RunCountedObservedAsync(
                    Program,
                    limits,
                    zeroArgPropertyResultCache: new AsyncEvaluation.PassThroughAsyncZeroArgPropertyResultCache(),
                    hostOperations: Operations).AsTask().GetAwaiter().GetResult()
                : Evaluator.RunCountedObserved(Program, limits, enableOptimizations: route == "planned",
                    loopDiagnostics: loopDiagnostics, hostOperations: Operations);

        public RunResult Engine(EvaluationLimits? limits = null)
            => KatLangEngine.Run(Source, new RunOptions { HostOperations = Operations, EvaluationLimits = limits });

        public RunResult EngineAsync(EvaluationLimits? limits = null)
            => KatLangEngine.RunAsync(Source, new RunOptions { HostOperations = Operations, EvaluationLimits = limits })
                .GetAwaiter().GetResult();
    }

    private static EvalError ContextTerminal(EvalError error)
    {
        while (error is EvalError.WithContext(_, var inner))
            error = inner;
        return error;
    }

    private static int ContextFrameCount(EvalError error)
    {
        var frames = 0;
        for (; error is EvalError.WithContext(_, var inner); error = inner)
            frames++;
        return frames;
    }

    /// <summary>
    /// One line per context frame and one for the terminal, without recursion: a deep run's chain has thousands
    /// of frames, which the indented recursive description of <see cref="LoopDiagnosticParityAssertions"/> cannot hold.
    /// </summary>
    private static string DescribeErrorChain(EvalError error)
    {
        var text = new System.Text.StringBuilder();
        for (; error is EvalError.WithContext frame; error = frame.Inner)
            text.Append(frame.ErrorContext).Append(" @").Append(frame.Span).Append('\n');
        return text.Append(error.GetType().Name).Append(" @").Append(error.Span).ToString();
    }

    private static string DescribeLoopStepRun(EvalResult<Evaluator.CountedResult> result, EvaluationBudget budget)
        => (result.IsError ? DescribeErrorChain(result.Error) : SemanticExplorerHarness.Neutral(result.Value.Value))
            + $" steps={budget.ConsumedSteps} checkpoints={budget.ConsumedExpressionCheckpoints} peak={budget.PeakDepth}"
            + $" depth={budget.CurrentDepth} items={budget.MaterializedItems}";

    /// <summary>
    /// Recursion routed through loop steps is bounded by the host-stack backstop on the synchronous routes, as
    /// <see cref="EvaluationLimits"/> documents: the structured, terminal
    /// <see cref="EvalError.EvaluationStackExhausted"/>, never a process overflow (audit finding 1 of 2026-11-21).
    /// The child runs every unbounded shape through the public engine and the planned and generic evaluators on
    /// 1, 16 and 64 MiB threads, once with tiering (Tier-0 frames first) and once without. Each stop is terminal
    /// (the row after the recursion never runs) and leaves no depth level open. On the 1 MiB thread each
    /// evaluator stop is also checked against the generic accounting (Q-09b: a route may stop anywhere, Q-09a,
    /// but it charged exactly the generic prefix), and a step budget that binds before every route's stop gives
    /// the generic, planned and twin routes one verdict with identical counters. The terminating recursion
    /// returns its value wherever it fits and on every thread of at least 16 MiB.
    /// <para>This is a different boundary from the two earlier repairs in this class: the argument-evaluation
    /// chokepoint (<see cref="BuiltinArgumentRecursion_ProbeChild"/>: a loop's initial STATE or COUNT reaching
    /// itself) and the nested <see cref="LoopValueEnvironment"/> views of
    /// <see cref="RecursionThroughPlannedLoopSteps_ProbeChild"/>, whose one shape (the fresh count) had a probe
    /// in its cycle all along.</para>
    /// </summary>
    [Theory]
    [InlineData("1")]
    [InlineData("0")]
    public async Task RecursionThroughLoopSteps_StopsAtTheLoopEntryBackstop_InSubprocess(string tieredCompilation)
        => await RunProbeChild(
            nameof(RecursionThroughLoopSteps_ProbeChild),
            new Dictionary<string, string> { ["DOTNET_TieredCompilation"] = tieredCompilation });

    [Fact]
    public void RecursionThroughLoopSteps_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        const int oneMiB = 1024 * 1024;
        string[] evaluators = ["generic", "planned"];

        foreach (var (name, source) in UnboundedLoopStepRecursions)
        {
            var stops = new Dictionary<string, (long Steps, long Checkpoints)>();
            foreach (var stackMiB in new[] { 1, 16, 64 })
            {
                AstStructuralDepthProcessTests.RunOnThreadWithStack(stackMiB * oneMiB, () =>
                {
                    var where = $"{name} on {stackMiB} MiB";
                    var engine = new LoopStepRecursionRun(source);
                    // The same high step ceiling as the planned-frame regression above bounds each case
                    // independently of the stack probe. The probe must fire first on these stacks.
                    var limits = new EvaluationLimits { MaxSteps = 200_000 };
                    var failure = Assert.Single(Assert.IsType<RunResult.EvalFailure>(engine.Engine(limits)).Errors);
                    Assert.True(failure.Code == KatLangErrorCode.EvaluationStackExhausted,
                        $"KatLangEngine.Run, {where}: {failure.Code}: {failure.Message}");
                    Assert.True(failure.IsResourceLimit);
                    Assert.Equal("1", engine.Marks);

                    foreach (var route in evaluators)
                    {
                        var run = new LoopStepRecursionRun(source);
                        var diagnostics = new LoopOptimizationDiagnostics();
                        var (result, budget) = run.Evaluate(route, limits, diagnostics);
                        Assert.True(result.IsError, $"{route}, {where}: completed an unbounded recursion");
                        var terminal = ContextTerminal(result.Error);
                        Assert.True(terminal is EvalError.EvaluationStackExhausted, $"{route}, {where}: {terminal.GetType().Name}");
                        Assert.True(result.Error.IsResourceLimit);
                        // A resource limit takes no context frame on the way out.
                        Assert.Equal(0, ContextFrameCount(result.Error));
                        Assert.Equal(0, budget.CurrentDepth);
                        // Loop steps charge no depth: only the one root call and its argument levels are ever open.
                        Assert.InRange(budget.PeakDepth, 1, 4);
                        // Nothing follows a resource limit: the row after the recursion never ran.
                        Assert.Equal("1", run.Marks);
                        // The recursion really nested loops (each level executes one). No depth is promised
                        // (Q-09a): this only rules out a stop before any nesting.
                        Assert.True(diagnostics.LoopExecutions > 2, $"{route}, {where}: only {diagnostics.LoopExecutions} loop(s) ran");
                        if (route == "planned" && source is DotWhileInStep or RepeatWithForwardedCount)
                            Assert.True(diagnostics.OptimizedLoopHits > 1, $"{where}: expected nesting through planned rounds");
                        if (stackMiB == 1)
                            stops[route] = (budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints);
                    }
                });
            }

            // The generic accounting on a stack where only the step budget binds: where a route stopped on the
            // 1 MiB thread, its counters lie between those of the generic run refused at that step and the next.
            AstStructuralDepthProcessTests.RunOnThreadWithStack(64 * oneMiB, () =>
            {
                long CheckpointsRefusedAt(long step)
                {
                    var (result, budget) = new LoopStepRecursionRun(source)
                        .Evaluate("generic", new EvaluationLimits { MaxSteps = step - 1 });
                    Assert.IsType<EvalError.EvaluationStepLimitExceeded>(ContextTerminal(result.Error));
                    Assert.Equal(step - 1, budget.ConsumedSteps);
                    return budget.ConsumedExpressionCheckpoints;
                }

                foreach (var (route, (steps, checkpoints)) in stops)
                {
                    var low = CheckpointsRefusedAt(steps);
                    var high = CheckpointsRefusedAt(steps + 1);
                    Assert.True(low <= checkpoints && checkpoints <= high,
                        $"{name}: {route} stopped after {steps} steps with {checkpoints} checkpoints, off the generic "
                        + $"trajectory [{low}, {high}]");
                }

                // A budget binding before every route's stop: one verdict, identical counters and effects.
                var limits = new EvaluationLimits { MaxSteps = Math.Max(2, stops.Values.Min(static stop => stop.Steps) / 2) };
                var expected = new LoopStepRecursionRun(source);
                var (genericResult, genericBudget) = expected.Evaluate("generic", limits);
                Assert.IsType<EvalError.EvaluationStepLimitExceeded>(ContextTerminal(genericResult.Error));
                Assert.Equal(limits.MaxSteps, genericBudget.ConsumedSteps);
                foreach (var route in new[] { "planned", "twin" })
                {
                    var run = new LoopStepRecursionRun(source);
                    var (result, budget) = run.Evaluate(route, limits);
                    Assert.Equal(DescribeLoopStepRun(genericResult, genericBudget), DescribeLoopStepRun(result, budget));
                    Assert.Equal(expected.Marks, run.Marks);
                }
            });
        }

        // The terminating recursion: its value wherever it fits, the backstop otherwise, and never a crash.
        var terminating = TerminatingLoopStepRecursion(100);
        foreach (var stackMiB in new[] { 1, 16, 64 })
        {
            AstStructuralDepthProcessTests.RunOnThreadWithStack(stackMiB * oneMiB, () =>
            {
                var roomy = stackMiB >= 16;
                var engine = new LoopStepRecursionRun(terminating).Engine();
                if (roomy || engine is RunResult.Success)
                    Assert.Equal(TerminatingLoopStepRecursionValue, Assert.IsType<RunResult.Success>(engine).ToDisplayString());
                else
                    Assert.Equal(KatLangErrorCode.EvaluationStackExhausted,
                        Assert.Single(Assert.IsType<RunResult.EvalFailure>(engine).Errors).Code);

                string? completed = null;
                foreach (var route in evaluators)
                {
                    var (result, budget) = new LoopStepRecursionRun(terminating).Evaluate(route);
                    Assert.Equal(0, budget.CurrentDepth);
                    if (result.IsError)
                    {
                        Assert.False(roomy, $"{route} on {stackMiB} MiB stopped a recursion of 100 loops: {DescribeErrorChain(result.Error)}");
                        Assert.IsType<EvalError.EvaluationStackExhausted>(ContextTerminal(result.Error));
                        continue;
                    }

                    // Every route that completes agrees on the value and on every counter.
                    var described = DescribeLoopStepRun(result, budget);
                    Assert.StartsWith(TerminatingLoopStepRecursionNeutral + " ", described, StringComparison.Ordinal);
                    Assert.Equal(completed ??= described, described);
                }
            });
        }

        WriteProbeMarker();
    }

    /// <summary>
    /// The async twin route's side of the loop-entry backstop: a twin about to enter a loop on a low host stack
    /// first hops (<see cref="StackHop"/>) and continues on a fresh thread-pool stack, like every other twin site
    /// that shares a synchronous probe, so recursion routed through loop steps does not end at the first thread's
    /// stack. Before the loop entry hopped and probed, the shapes with no other hop site in their cycle
    /// overflowed the process on this route too. Every case here is BOUNDED, by a step budget or by its own
    /// termination: on this route nothing else bounds loop-step recursion (no depth is charged, and each hop
    /// supplies a fresh stack), so an unbounded one runs until the host cancels it or memory runs out. That
    /// remaining gap is the separately tracked owner decision on a deterministic loop-nesting limit.
    /// <para>The child checks, on a 1 MiB thread: a step budget far deeper than one stack holds is reached
    /// exactly, with the generic counters of the same budget where a synchronous stack can hold it; a
    /// terminating recursion four times deeper than the stack completes with the synchronous value and
    /// counters; a genuinely suspending one does too; and a failure at the bottom of a deep recursion unwinds
    /// to its structured error, with the frame count and step count that shallow synchronous runs predict.
    /// The last one is the Q-36 walkers' regression at depth: nesting a failure once per level used to recurse
    /// over the whole context chain on whatever stack the completing twin had left.</para>
    /// </summary>
    [Theory]
    [InlineData("1")]
    [InlineData("0")]
    public async Task RecursionThroughLoopSteps_OnTheTwinRoute_ContinuesOnFreshStacks_InSubprocess(string tieredCompilation)
        => await RunProbeChild(
            nameof(RecursionThroughLoopStepsOnTheTwinRoute_ProbeChild),
            new Dictionary<string, string> { ["DOTNET_TieredCompilation"] = tieredCompilation });

    [Fact]
    public void RecursionThroughLoopStepsOnTheTwinRoute_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        const int oneMiB = 1024 * 1024;

        // 1. Unbounded shapes under a step budget: the budget is reached, on fresh stacks.
        foreach (var (name, source) in UnboundedLoopStepRecursions)
        {
            // Shallow enough for a synchronous 64 MiB stack: the three routes agree on everything.
            var shallow = new EvaluationLimits { MaxSteps = 150 };
            var expected = AstStructuralDepthProcessTests.RunOnThreadWithStack(64 * oneMiB, () =>
            {
                var (result, budget) = new LoopStepRecursionRun(source).Evaluate("generic", shallow);
                Assert.IsType<EvalError.EvaluationStepLimitExceeded>(ContextTerminal(result.Error));
                return DescribeLoopStepRun(result, budget);
            });

            AstStructuralDepthProcessTests.RunOnThreadWithStack(oneMiB, () =>
            {
                var twin = new LoopStepRecursionRun(source);
                var (result, budget) = twin.Evaluate("twin", shallow);
                Assert.Equal(expected, DescribeLoopStepRun(result, budget));
                Assert.Equal("1", twin.Marks);

                // Far deeper than any one stack: only fresh stacks reach this budget.
                var deep = new EvaluationLimits { MaxSteps = 4_000 };
                var deepTwin = new LoopStepRecursionRun(source);
                var (deepResult, deepBudget) = deepTwin.Evaluate("twin", deep);
                Assert.True(deepResult.IsError, $"{name}: the twin completed an unbounded recursion");
                var terminal = ContextTerminal(deepResult.Error);
                Assert.True(terminal is EvalError.EvaluationStepLimitExceeded, $"{name}: the twin stopped with {terminal.GetType().Name}");
                Assert.Equal(deep.MaxSteps, deepBudget.ConsumedSteps);
                Assert.Equal(0, deepBudget.CurrentDepth);
                Assert.InRange(deepBudget.PeakDepth, 1, 4);
                Assert.Equal("1", deepTwin.Marks);

                // The public engine takes the twin route once an asynchronous operation is configured.
                var engine = new LoopStepRecursionRun(source, asynchronousOperation: true);
                var failure = Assert.Single(Assert.IsType<RunResult.EvalFailure>(engine.EngineAsync(deep)).Errors);
                Assert.True(failure.Code == KatLangErrorCode.EvaluationStepLimitExceeded, $"{name}: KatLangEngine.RunAsync: {failure.Code}: {failure.Message}");
                Assert.Equal("1", engine.Marks);
            });
        }

        // 2. A terminating recursion deeper than the 1 MiB stack holds: the twin completes it on fresh stacks
        //    (its `here` operation runs on the thread pool once the run has hopped) with the value and counters
        //    of the synchronous routes on a stack that holds it.
        var terminating = TerminatingLoopStepRecursion(400, "here(tick())");
        var synchronous = AstStructuralDepthProcessTests.RunOnThreadWithStack(64 * oneMiB, () =>
        {
            var (generic, genericBudget) = new LoopStepRecursionRun(terminating).Evaluate("generic");
            var (planned, plannedBudget) = new LoopStepRecursionRun(terminating).Evaluate("planned");
            var described = DescribeLoopStepRun(generic, genericBudget);
            Assert.StartsWith(TerminatingLoopStepRecursionNeutral + " ", described, StringComparison.Ordinal);
            Assert.Equal(described, DescribeLoopStepRun(planned, plannedBudget));
            return described;
        });
        AstStructuralDepthProcessTests.RunOnThreadWithStack(oneMiB, () =>
        {
            var stopped = new LoopStepRecursionRun(terminating).Evaluate("generic");
            Assert.IsType<EvalError.EvaluationStackExhausted>(ContextTerminal(stopped.Result.Error));

            var twin = new LoopStepRecursionRun(terminating);
            var (result, budget) = twin.Evaluate("twin");
            Assert.Equal(synchronous, DescribeLoopStepRun(result, budget));
            Assert.True(twin.CalledAnOperationOnThePool, "the twin never left the 1 MiB thread, so no hop was exercised");

            var engine = new LoopStepRecursionRun(terminating, asynchronousOperation: true);
            Assert.Equal(TerminatingLoopStepRecursionValue, Assert.IsType<RunResult.Success>(engine.EngineAsync()).ToDisplayString());
            Assert.True(engine.CalledAnOperationOnThePool);

            // A genuinely suspending recursion: every level awaits a real asynchronous operation first.
            var suspending = new LoopStepRecursionRun(TerminatingLoopStepRecursion(400, "yield(tick())"), asynchronousOperation: true);
            Assert.Equal(TerminatingLoopStepRecursionValue, Assert.IsType<RunResult.Success>(suspending.EngineAsync()).ToDisplayString());
        });

        // 3. A failure at the bottom of a deep recursion. Each level adds the same context frames and charges the
        //    same steps, so two shallow synchronous runs predict the deep twin run's chain length and step count.
        foreach (var (bottom, kind) in new[] { ("1 / 0", typeof(EvalError.DivByZero)), ("G", typeof(EvalError.MissingOutput)) })
        {
            string Failing(int levels) => $"G = {{\n    public X = 1\n}}\nR(n) = if(n == 0, {bottom}, R(n - 1).repeat(1))\nR({levels})";

            var (ten, twenty, chain20) = AstStructuralDepthProcessTests.RunOnThreadWithStack(64 * oneMiB, () =>
            {
                static (int Frames, long Steps, long Checkpoints) Measure(EvalResult<Evaluator.CountedResult> result, EvaluationBudget budget)
                {
                    // Below the first bulk block, so every step is a call or a loop round.
                    Assert.InRange(budget.ConsumedExpressionCheckpoints, 1, EvaluationBudget.ExpressionCheckpointsPerStep - 1);
                    return (ContextFrameCount(result.Error), budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints);
                }

                var (tenResult, tenBudget) = new LoopStepRecursionRun(Failing(10)).Evaluate("generic");
                var (twentyResult, twentyBudget) = new LoopStepRecursionRun(Failing(20)).Evaluate("generic");
                var (planned, plannedBudget) = new LoopStepRecursionRun(Failing(20)).Evaluate("planned");
                Assert.Equal(DescribeLoopStepRun(twentyResult, twentyBudget), DescribeLoopStepRun(planned, plannedBudget));
                return (Measure(tenResult, tenBudget), Measure(twentyResult, twentyBudget), DescribeLoopStepRun(twentyResult, twentyBudget));
            });
            Assert.True(twenty.Frames > ten.Frames, $"a level of `{bottom}` adds no context frame");

            AstStructuralDepthProcessTests.RunOnThreadWithStack(oneMiB, () =>
            {
                var (shallow, shallowBudget) = new LoopStepRecursionRun(Failing(20)).Evaluate("twin");
                Assert.Equal(chain20, DescribeLoopStepRun(shallow, shallowBudget));

                const int levels = 3_000;
                // Keep the deep failure bounded even if a regression stops the recursion from reaching its base.
                var limits = new EvaluationLimits { MaxSteps = 200_000 };
                var (result, budget) = new LoopStepRecursionRun(Failing(levels)).Evaluate("twin", limits);
                Assert.True(result.IsError);
                var terminal = ContextTerminal(result.Error);
                Assert.True(terminal.GetType() == kind, $"`{bottom}` at the bottom of {levels} levels: {terminal.GetType().Name}");
                // The failure stays positioned through every level it left.
                Assert.NotNull(result.Error.Span);
                // Per level: the same frames, calls, rounds and expression checkpoints; every completed block of
                // checkpoints charges one more step (the bulk expression-work unit).
                static long At(long ten, long twenty, int levels) => ten + (twenty - ten) * (levels - 10) / 10;
                var checkpoints = At(ten.Checkpoints, twenty.Checkpoints, levels);
                Assert.Equal(At(ten.Frames, twenty.Frames, levels), ContextFrameCount(result.Error));
                Assert.Equal(checkpoints, budget.ConsumedExpressionCheckpoints);
                Assert.Equal(At(ten.Steps, twenty.Steps, levels) + checkpoints / EvaluationBudget.ExpressionCheckpointsPerStep, budget.ConsumedSteps);
                Assert.Equal(0, budget.CurrentDepth);
                // A missing output that left the bottom is someone else's at every consumer above it (Q-36).
                if (terminal is EvalError.MissingOutput missing)
                    Assert.True(missing.IsNested);

                var failure = Assert.Single(Assert.IsType<RunResult.EvalFailure>(
                    new LoopStepRecursionRun(Failing(levels), asynchronousOperation: true).EngineAsync(limits)).Errors);
                Assert.Equal(terminal.Code, failure.Code);
            });
        }

        WriteProbeMarker();
    }

    [Fact]
    public async Task DeepContextChainReaders_AreStackSafe_InSubprocess()
        => await RunProbeChild(nameof(DeepContextChainReaders_ProbeChild));

    /// <summary>
    /// The Q-36 context-chain readers on a SYNTHETIC chain far deeper than any stack, with no stack pressure of
    /// their own: 100,000 host-built frames on an ordinary thread. They are loops, like
    /// <see cref="EvalError.Code"/> (<see cref="DeepErrorContextCode_ProbeChild"/>): one native frame per context
    /// frame overflowed the process here. The outcomes are the recursive definitions': an own missing output is
    /// nested under copies of every frame (each keeps its context, span and slots; the original chain is
    /// untouched), a nested one and every other failure pass through as the same object, a spread turns the own
    /// one into its own failure kind under the same frames, and the lifting test reads the terminal's kind and the
    /// projection mark at any depth.
    /// </summary>
    [Fact]
    public void DeepContextChainReaders_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        const int depth = 100_000;
        var operand = new Expr.Param("x") { Span = new SourceSpan(9, 2, 9, 3) };

        static EvalError Wrap(EvalError terminal, int frames, int markedFrame = -1)
        {
            var wrapped = terminal;
            for (var i = frames - 1; i >= 0; i--)
            {
                // Frame i is the i-th from the outside: a distinct context and span per frame.
                var frame = new EvalError.WithContext(new CallContext("F" + i), wrapped) { Span = new SourceSpan(i + 1, 1, i + 1, 2) };
                wrapped = i == markedFrame ? frame with { IsProjectionFailure = true } : frame;
            }

            return wrapped;
        }

        static void AssertSameFramesAround(EvalError original, EvalError rebuilt, int frames)
        {
            for (var i = 0; i < frames; i++)
            {
                var before = Assert.IsType<EvalError.WithContext>(original);
                var after = Assert.IsType<EvalError.WithContext>(rebuilt);
                if (!ReferenceEquals(before.ErrorContext, after.ErrorContext) || !Equals(before.Span, after.Span)
                    || before.IsProjectionFailure != after.IsProjectionFailure || ReferenceEquals(before, after))
                    Assert.Fail($"frame {i} was not copied with its context, span and slots");
                (original, rebuilt) = (before.Inner, after.Inner);
            }

            Assert.IsNotType<EvalError.WithContext>(original);
            Assert.IsNotType<EvalError.WithContext>(rebuilt);
        }

        // An own missing output: nested under copies of every frame, the original untouched.
        var origin = new SourceSpan(3, 4, 3, 5);
        var ownTerminal = new EvalError.MissingOutput { Span = origin, IsSelectedMemberOutput = true };
        var own = Wrap(ownTerminal, depth, markedFrame: depth / 2);
        Assert.True(Evaluator.IsOwnMissingOutputError(own));
        var nested = Evaluator.NestMissingOutput(own);
        AssertSameFramesAround(own, nested, depth);
        var nestedTerminal = Assert.IsType<EvalError.MissingOutput>(ContextTerminal(nested));
        Assert.True(nestedTerminal.IsNested);
        Assert.True(nestedTerminal.KeepsOwnBlame);
        Assert.True(nestedTerminal.IsSelectedMemberOutput);
        Assert.Equal(origin, nestedTerminal.Span);
        Assert.Same(ownTerminal, ContextTerminal(own));
        Assert.False(ownTerminal.IsNested);
        Assert.False(ownTerminal.KeepsOwnBlame);
        Assert.Equal(KatLangErrorCode.MissingOutput, nested.Code);

        // Nesting is idempotent, and every other failure is the same object afterwards.
        Assert.False(Evaluator.IsOwnMissingOutputError(nested));
        Assert.Same(nested, Evaluator.NestMissingOutput(nested));
        var other = Wrap(new EvalError.DivByZero { Span = origin }, depth);
        Assert.False(Evaluator.IsOwnMissingOutputError(other));
        Assert.Same(other, Evaluator.NestMissingOutput(other));

        // The spread's decision over the same chains.
        var converted = Evaluator.SpreadOperandFailure(operand, operand.Span, own);
        AssertSameFramesAround(own, converted, depth);
        Assert.Equal(operand.Span, Assert.IsType<EvalError.SpreadMissingOutput>(ContextTerminal(converted)).Span);
        var preserved = Assert.IsType<EvalError.WithContext>(Evaluator.SpreadOperandFailure(operand, operand.Span, nested));
        Assert.IsType<SpreadOperandContext>(preserved.ErrorContext);
        Assert.Same(nested, preserved.Inner);
        Assert.Equal(nested.Span, preserved.Span);
        Assert.Same(other, Evaluator.SpreadOperandFailure(operand, operand.Span, other));

        // The lifting test: the terminal's kind, unless the projection mark sits anywhere on the chain.
        Assert.True(Evaluator.IsLiftableError(Wrap(new EvalError.NotAnAlgorithm("x"), depth)));
        Assert.True(Evaluator.IsLiftableError(Wrap(new EvalError.IllegalInEval("x"), depth)));
        Assert.False(Evaluator.IsLiftableError(other));
        Assert.False(Evaluator.IsLiftableError(Wrap(new EvalError.NotAnAlgorithm("x"), depth, markedFrame: depth - 1)));
        Assert.False(Evaluator.IsLiftableError(Wrap(new EvalError.NotAnAlgorithm("x") { IsProjectionFailure = true }, depth)));
        Assert.True(Evaluator.IsProjectionFailure(Wrap(new EvalError.NotAnAlgorithm("x"), depth, markedFrame: depth - 1)));

        WriteProbeMarker();
    }

    [Fact]
    public async Task StructuralAndDynamicDepthComposition_IsSafe_InSubprocess()
        => await RunProbeChild(nameof(StructuralAndDynamicDepthComposition_ProbeChild));

    [Fact]
    public void StructuralAndDynamicDepthComposition_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        // Host-built bodies avoid the parser's separate nesting ceiling. The last admitted
        // body of each kind exercises the evaluation gate itself, alongside moderate nesting
        // repeated by dynamic calls. The September row-funnel probes must protect both.
        var root = SourceProvenance.ParseValid("F(n) = F(n + 1) + 1\nF(0)").Root;
        var property = Assert.Single(root.Properties);
        var function = Assert.IsType<Algorithm.User>(property.Value);
        Expr[] Wrap(Expr inner) =>
        [
            new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [inner])),
            new Expr.Capture([inner, new Expr.Num(0)]),
            new Expr.Call(new Expr.Resolve("if"), [new Expr.BoolLiteral(true), inner, new Expr.Num(0)]),
        ];

        for (var kind = 0; kind < 3; kind++)
        {
            var cases = new List<Expr>();
            Expr body = Assert.Single(function.Output);
            Expr? lastAdmitted = null;
            for (var nesting = 1; nesting <= EvaluationLimits.MaxSupportedAstDepth; nesting++)
            {
                body = Wrap(body)[kind];
                var program = new Expr.AlgorithmExpr(root with
                {
                    Properties = [property with { Value = function with { Output = [body] } }],
                });
                if (AstStructuralPreflight.Check(program, EvaluationLimits.MaxSupportedAstDepth,
                        AstConsumerProfile.EvaluatorIterativeJoinSpines) is not null)
                    break;
                lastAdmitted = program;
                if (nesting is 8 or 32)
                    cases.Add(program);
            }

            Assert.NotNull(lastAdmitted);
            cases.Add(lastAdmitted);
            AstStructuralDepthProcessTests.RunOnThreadWithStack(1_048_576, () =>
            {
                foreach (var program in cases)
                foreach (var route in new[] { "generic", "planned", "twin" })
                {
                    var limits = new EvaluationLimits { MaxDepth = 32 };
                    var (result, budget) = route == "twin"
                        ? Evaluator.RunCountedObservedAsync(program, limits,
                            zeroArgPropertyResultCache: new AsyncEvaluation.PassThroughAsyncZeroArgPropertyResultCache())
                            .AsTask().GetAwaiter().GetResult()
                        : Evaluator.RunCountedObserved(program, limits, enableOptimizations: route == "planned");
                    Assert.True(result.IsError, $"kind={kind}, route={route} completed unbounded recursion");
                    var leaf = result.Error;
                    while (leaf is EvalError.WithContext(_, var inner))
                        leaf = inner;
                    Assert.True(leaf is EvalError.EvaluationStackExhausted or EvalError.EvaluationDepthExceeded,
                        $"kind={kind}, route={route}: {leaf.GetType().Name}");
                    Assert.InRange(budget.PeakDepth, 1, 32);
                    Assert.Equal(0, budget.CurrentDepth);
                }
            });
        }

        WriteProbeMarker();
    }

    [Fact]
    public async Task GenuineSuspension_RecursiveLimitsAndCancellation_ArePreserved_InSubprocess()
        => await RunProbeChild(nameof(GenuineSuspension_RecursiveLimitsAndCancellation_ProbeChild));

    [Fact]
    public void GenuineSuspension_RecursiveLimitsAndCancellation_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        // yield MUST be demanded before descending. F(yield(n) + 1) alone never demands
        // n under call-by-need, so an async operation there would not prove suspension.
        const string source = "F(n) = if(yield(n) >= 0, F(n + 1) + 1, 0)\nF(0), mark(2)";
        (string Error, long Steps, long Checkpoints, int Peak, long Items, long Strings, int Calls) Run(
            bool forceTwin, EvaluationLimits limits, bool cancel)
        {
            using var cancellation = new CancellationTokenSource();
            var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
            var calls = 0;
            var laterRows = 0;
            var operations = HostOperations.Create(
                HostOperation.CreateAsync("yield", async (args, token) =>
                {
                    if (++calls == 1)
                        await release.Task.ConfigureAwait(false);
                    else
                        await Task.Yield();
                    if (cancel && calls == 3)
                        cancellation.Cancel();
                    token.ThrowIfCancellationRequested();
                    return args[0];
                }, "value"),
                HostOperation.Create("mark", (args, _) => { laterRows++; return args[0]; }, "value"));
            var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
            Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(d => d.Message)));
            var pending = Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root), limits,
                zeroArgPropertyResultCache: forceTwin ? new AsyncEvaluation.PassThroughAsyncZeroArgPropertyResultCache() : null,
                hostOperations: operations, cancellationToken: cancellation.Token);

            // The first host call cannot complete until this assertion has observed the
            // suspended run. Later continuations use host-owned stacks, as Q-09a permits.
            Assert.Equal(1, calls);
            Assert.False(pending.IsCompleted);
            release.SetResult();
            if (cancel)
            {
                var error = Assert.ThrowsAny<OperationCanceledException>(() => pending.AsTask().GetAwaiter().GetResult());
                Assert.Equal(cancellation.Token, error.CancellationToken);
                Assert.Equal(3, calls);
                Assert.Equal(0, laterRows);
                return default;
            }

            var (result, budget) = pending.AsTask().GetAwaiter().GetResult();
            Assert.True(result.IsError);
            Assert.True(calls > 1);
            Assert.Equal(0, budget.CurrentDepth);
            Assert.Equal(0, laterRows);
            return (LoopDiagnosticParityAssertions.DescribeErrorTree(result.Error), budget.ConsumedSteps,
                budget.ConsumedExpressionCheckpoints, budget.PeakDepth, budget.MaterializedItems,
                budget.MaterializedStringChars, calls);
        }

        AstStructuralDepthProcessTests.RunOnThreadWithStack(1_048_576, () =>
        {
            // Low semantic limits isolate equivalent work from host-stack headroom.
            var depth = new EvaluationLimits { MaxDepth = 12 };
            var baseline = Run(false, depth, cancel: false);
            Assert.Contains("EvaluationDepthExceeded", baseline.Error, StringComparison.Ordinal);
            foreach (var forceTwin in new[] { false, true })
            {
                Assert.Equal(baseline, Run(forceTwin, depth, cancel: false));
                Assert.Equal(baseline, Run(forceTwin, depth with
                {
                    MaxSteps = 1_000_000, MaxCollectionItems = 50_000, MaxMaterializedItems = 1_000_000,
                    MaxStringLength = 500_000, MaxMaterializedStringChars = 1_000_000,
                }, cancel: false));
                var steps = Run(forceTwin, new EvaluationLimits { MaxSteps = 10 }, cancel: false);
                Assert.Contains("EvaluationStepLimitExceeded", steps.Error, StringComparison.Ordinal);
                Assert.Equal(10, steps.Steps);
                Assert.Equal(Run(false, new EvaluationLimits { MaxSteps = 10 }, cancel: false), steps);
                Run(forceTwin, depth, cancel: true);
            }
        });

        WriteProbeMarker();
    }

    [Fact]
    public void DeepErrorContextCode_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        // Code is public and host-built wrappers have no AST-depth ceiling.
        // Its exhaustive terminal dispatch must not replace iterative unwrapping
        // with one native stack frame per context. Isolate a regression's process
        // termination; do not format the error (a separate, recursive operation).
        foreach (var terminal in new EvalError[]
        {
            new EvalError.DivByZero(),
            new EvalError.EvaluationStepLimitExceeded(1),
            EvalError.ModuleRegionMaterializationFailed.From(
                [new Diagnostic("fetch failed", DiagnosticSeverity.Error, new SourceSpan(1, 1, 1, 3))
                    { Code = DiagnosticCode.LoadFetchFailed }]),
        })
        {
            var expected = terminal.Code;
            EvalError wrapped = terminal;
            var context = new CallContext("F");
            for (var i = 0; i < 100_000; i++)
                wrapped = new EvalError.WithContext(context, wrapped);

            Assert.Equal(expected, wrapped.Code);
        }

        WriteProbeMarker();
    }

    /// <summary>
    /// Final audit (September 2026): the loop planner (<c>LoopOptimizer.TryBuildLoopExprPlan</c>)
    /// and the planned expression evaluator recurse once per AST level of the step body between
    /// two budget chokepoints, and a plan is built at loop-INVOCATION time — after the dynamic
    /// recursion has already consumed most of the host stack. A parser- and preflight-accepted
    /// step (an 80-operator chain, or 126 nested <c>if</c>s) invoked at a modest recursion depth
    /// therefore terminated the whole process with an uncatchable stack overflow inside the
    /// planner, where the generic strategy completes or reports the structured stack error.
    /// Both walks now probe the host stack per level: an unplannable step falls back to the
    /// generic strategy, and a planned spine that runs out of headroom degrades to the
    /// structured <see cref="EvalError.EvaluationStackExhausted"/>. The generic strategy is the
    /// oracle for the value where the run completes.
    /// </summary>
    [Fact]
    public void PlannedLoopUnderRecursion_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        var chain80 = "Step(x) = x" + string.Concat(Enumerable.Repeat(" + 1", 80));
        var chain200 = "Step(x) = x" + string.Concat(Enumerable.Repeat(" + 1", 200));
        var nestedIfs = "Step(x) = " + string.Concat(Enumerable.Repeat("if(x + 1 > 0, ", 126)) + "x + 1"
            + string.Concat(Enumerable.Repeat(", 0)", 126));

        // A guard that simply refuses every plan must not satisfy the safety test.
        // At shallow depth, these accepted spines must execute planned operations,
        // produce the hand-computed result, and preserve the generic budget relations.
        foreach (var (step, expected) in new[] { (chain80, 160), (chain200, 400) })
        {
            var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(step + "\nStep(0).repeat(2)").Root);
            var diagnostics = new LoopOptimizationDiagnostics();
            var planned = Evaluator.RunCountedObserved(program, loopDiagnostics: diagnostics);
            var generic = Evaluator.RunCountedObserved(program, enableOptimizations: false);
            Assert.False(planned.Result.IsError);
            Assert.False(generic.Result.IsError);
            Assert.Equal(new Result.Atom(expected), planned.Result.Value.Value);
            Assert.Equal(generic.Result.Value, planned.Result.Value);
            Assert.True(diagnostics.PlannedBuiltinOperations > 0);
            Assert.Equal(0, diagnostics.GenericExpressionEvaluationsInsideOptimizedLoops);
            // Every strategy charges every budget identically (Q-09b): steps, the raw
            // expression-work checkpoints, depth, and persistent materialization agree even
            // on this wholly planned path. (Planned steps used to be allowed to fall short.)
            Assert.Equal(generic.Budget.ConsumedSteps, planned.Budget.ConsumedSteps);
            Assert.Equal(generic.Budget.ConsumedExpressionCheckpoints, planned.Budget.ConsumedExpressionCheckpoints);
            Assert.Equal(generic.Budget.PeakDepth, planned.Budget.PeakDepth);
            Assert.Equal(generic.Budget.MaterializedItems, planned.Budget.MaterializedItems);
            Assert.Equal(generic.Budget.MaterializedStringChars, planned.Budget.MaterializedStringChars);
            Assert.Equal(0, planned.Budget.CurrentDepth);
            Assert.Equal(0, generic.Budget.CurrentDepth);
        }

        foreach (var (recursion, step) in new[] { (55, chain80), (60, chain80), (40, chain200), (50, nestedIfs), (30, nestedIfs) })
        {
            var source = $"Rec(n) = if(n == 0, Step(0).repeat(2), Rec(n - 1))\n{step}\nRec({recursion})";
            var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

            // Public engine path under DEFAULT limits — the configuration an embedding host runs with.
            var result = KatLangEngine.Run(source);
            switch (result)
            {
                case RunResult.Success:
                    // The optimized run completed (planned, or generic after the planner's
                    // fallback): a completed generic run has the same value. Native stack capacity
                    // can differ between strategies; both must reject safely before overflow.
                    var generic = Evaluator.RunCountedObserved(program, enableOptimizations: false).Result;
                    if (generic.IsError)
                        Assert.IsType<EvalError.EvaluationStackExhausted>(generic.Error);
                    else
                        Assert.Equal(generic.Value.Value, Assert.IsType<RunResult.Success>(result).Value);
                    break;
                case RunResult.EvalFailure failure:
                    var error = Assert.Single(failure.Errors);
                    Assert.True(
                        error.Source is EvalError.EvaluationStackExhausted or EvalError.EvaluationDepthExceeded,
                        $"expected success or a structured resource error for recursion {recursion}, got: {error.Message}");
                    break;
                default:
                    Assert.Fail($"unexpected outcome {result.GetType().Name} for recursion {recursion}");
                    break;
            }
        }

        WriteProbeMarker();
    }

    [Fact]
    public void BuiltinArgumentRecursion_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        // The spellings that previously killed the process, through the public
        // engine path under DEFAULT limits — exactly the configuration an
        // embedding host runs with.
        foreach (var source in new[]
        {
            "A = count(A)\nA",
            "A = range(1, A)\nA.count",
            "A = if(true, A, 0)\nA",
            "A = take([1, 2, 3], A)\nA",
            "A = [1, 2].take(A)\nA",
            "Add(a, b) = a + b\nA = [1, 2].reduce(Add, A)\nA",
            "Step = x, false\nA = Step(A).while\nA",
            "Inc = x + 1\nA = Inc(0).repeat(A)\nA",
        })
        {
            var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
            Assert.Single(failure.Errors);

            var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
            Assert.True(
                result.Error is EvalError.EvaluationDepthExceeded or EvalError.EvaluationStackExhausted,
                $"expected a structured resource error for `{source.Replace("\n", " ; ")}`, got {result.Error}");
        }

        WriteProbeMarker();
    }

    [Fact]
    public void ResolvedValueDemandRecursion_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        // These are the original parameter re-entry reproducer, its ordinary-dot `string`
        // counterpart, and the lexical `string` receiver that formerly reached
        // an uncatchable CLR stack overflow. A small explicit limit pins the
        // deterministic error; the default public path separately proves that
        // the process returns normally under the production ceiling.
        foreach (var source in new[]
        {
            "F(v) = v\nx = F(x)\nx",
            "F(v) = v.string\nx = F(x)\nx",
            "A = A.string\nA",
        })
        {
            var expr = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
            var bounded = Evaluator.Run(expr, new EvaluationLimits { MaxDepth = 24 });
            Assert.True(bounded.IsError);
            Assert.Equal(
                24,
                Assert.IsType<EvalError.EvaluationDepthExceeded>(bounded.Error).Limit);

            var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
            Assert.Single(failure.Errors);
        }

        WriteProbeMarker();
    }

    private static async Task RunProbeChild(string childTestName, IReadOnlyDictionary<string, string>? extraEnvironment = null)
    {
        var assemblyPath = typeof(EvaluationLimitsProcessTests).Assembly.Location;
        var testName = typeof(EvaluationLimitsProcessTests).FullName + "." + childTestName;
        var markerFile = Path.Combine(
            Path.GetTempPath(),
            $"katlang-eval-limits-probe-{Guid.NewGuid():N}.txt");

        var startInfo = SubprocessProbe.StartInfo(assemblyPath, [testName]);
        startInfo.Environment[ProbeChildEnvironment] = "1";
        startInfo.Environment[ProbeMarkerFileEnvironment] = markerFile;
        startInfo.Environment["DOTNET_NOLOGO"] = "1";
        foreach (var (name, value) in extraEnvironment ?? new Dictionary<string, string>())
            startInfo.Environment[name] = value;

        try
        {
            using var process = new Process { StartInfo = startInfo };
            process.Start();
            var stdoutTask = process.StandardOutput.ReadToEndAsync();
            var stderrTask = process.StandardError.ReadToEndAsync();

            await process.WaitForExitAsync();

            var stdout = await stdoutTask;
            var stderr = await stderrTask;
            var combined = stdout + Environment.NewLine + stderr;

            Assert.DoesNotContain("Stack overflow", combined, StringComparison.OrdinalIgnoreCase);
            Assert.DoesNotContain("StackOverflowException", combined, StringComparison.OrdinalIgnoreCase);
            Assert.True(
                process.ExitCode == 0,
                $"Probe subprocess '{childTestName}' exited with {process.ExitCode}.{Environment.NewLine}{combined}");
            Assert.True(
                File.Exists(markerFile),
                $"Probe child '{childTestName}' did not write its success marker.{Environment.NewLine}{combined}");
            Assert.Equal(ProbeSuccessMarker, (await File.ReadAllTextAsync(markerFile)).Trim());
        }
        finally
        {
            try { File.Delete(markerFile); }
            catch { /* best-effort cleanup */ }
        }
    }

    private static void WriteProbeMarker()
    {
        var markerFile = Environment.GetEnvironmentVariable(ProbeMarkerFileEnvironment);
        Assert.False(string.IsNullOrWhiteSpace(markerFile));
        File.WriteAllText(markerFile!, ProbeSuccessMarker);
    }
}
