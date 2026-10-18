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
            step10 + "R(n) = if(n > 0, R(n - 1), repeat(Step, 2, 0))\nR(50)",
            // looprec: recursion routed through a loop step (the generic loop used LESS stack).
            "S(s) = R(s - 1)\nR(n) = if(n > 0, repeat(S, 1, n), 0)\nR(25)",
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
            "S(x) = {\nP = P + 1\nP, x < 1\n}\nS.while(0)",
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
            var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(step + "\nStep.repeat(2, 0)").Root);
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
            var source = $"Rec(n) = if(n == 0, Step.repeat(2, 0), Rec(n - 1))\n{step}\nRec({recursion})";
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
            "Step = x, false\nA = Step.while(A)\nA",
            "Inc = x + 1\nA = Inc.repeat(A, 0)\nA",
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

        var startInfo = new ProcessStartInfo("dotnet")
        {
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
            CreateNoWindow = true,
        };
        startInfo.ArgumentList.Add("vstest");
        startInfo.ArgumentList.Add(assemblyPath);
        startInfo.ArgumentList.Add("--Tests:" + testName);
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

            var exited = true;
            using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(90));
            try
            {
                await process.WaitForExitAsync(timeout.Token);
            }
            catch (OperationCanceledException)
            {
                exited = false;
                try { process.Kill(entireProcessTree: true); }
                catch { /* process already exited */ }
                await process.WaitForExitAsync();
            }

            var stdout = await stdoutTask;
            var stderr = await stderrTask;
            var combined = stdout + Environment.NewLine + stderr;

            Assert.True(exited, $"Probe subprocess '{childTestName}' did not exit within 90 seconds."
                + Environment.NewLine + combined);
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
