using System.Numerics;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using KatLang.Semantics;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// The native <c>tick()</c> builtin: a zero-argument diagnostic primitive whose every actual execution
/// advances the RUN's own counter (zero when the run starts) and returns the new value. Behavioral cases
/// run on all six execution routes (<see cref="SixRouteAgreement"/>: sync and async engines, the genuinely
/// suspending async twin, the generic and optimized evaluators, the forced twin), which must agree on value,
/// error and host-call log; counter observations read the run's <see cref="EvaluationBudget.TickCount"/>.
/// The Lean counterpart is <c>runTick</c> / the <c>.tickBuiltin</c> arm (<c>KatLangArityLaws/TickGuards.lean</c>,
/// <c>KatLangArityLaws/Tick.lean</c>) and the <c>tick-*</c> language-spec cases.
/// </summary>
public class TickBuiltinTests
{
    private static async Task<string> OkAsync(string source)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(outcome.Kind == "ok", $"{outcome}\nsource:\n{source}");
        return outcome.Value!;
    }

    private static async Task<SixRouteAgreement.Observation> ErrAsync(string source)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(outcome.Kind == "err", $"{outcome}\nsource:\n{source}");
        return outcome;
    }

    /// <summary>A clean source evaluated on the generic or optimized evaluator, returning the run's budget.</summary>
    private static (EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget) Observe(
        string source, bool optimized = false, EvaluationLimits? limits = null, HostOperations? hostOperations = null,
        LoopOptimizationDiagnostics? loops = null, SequencePipelineDiagnostics? sequences = null, long? randomSeed = null)
    {
        // `trace(x)` is available exactly as on the six-route harness, so the same sources parse cleanly.
        hostOperations ??= HostOperations.Create(HostOperation.Create("trace", static (args, _) => args[0], "x"));
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = hostOperations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(parsed.Root), limits, enableOptimizations: optimized,
            loopDiagnostics: loops, sequenceDiagnostics: sequences, hostOperations: hostOperations, randomSeed: randomSeed);
    }

    private const string InvocationRequired =
        "`tick` is a builtin operation that runs only when it is invoked: write `tick()`.";

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    // ── The requested behavior matrix ──

    [Theory]
    // Direct calls: each execution returns the incremented counter.
    [InlineData("tick(), tick(), tick()", "S[1, 2, 3]")]
    // A user property is cached: declaring it ticks nothing, the bare reads share ONE execution.
    [InlineData("A = tick()\nA + A", "2")]
    // Explicit calls are fresh.
    [InlineData("A = tick()\nA() + A()", "3")]
    [InlineData("B = { tick() }\nB() + B()", "3")]
    // A qualifying explicit call establishes the empty entry; later calls stay fresh and never replace it.
    [InlineData("A = tick()\nA(), A, A(), A", "S[1, 1, 2, 1]")]
    [InlineData("A = tick()\nA, A(), A", "S[1, 2, 1]")]
    // An unused argument is never demanded.
    [InlineData("Ignore(x) = 7\nIgnore(tick()), tick()", "S[7, 1]")]
    // ONE supplied computation demanded twice runs once; the independent call is the second tick.
    [InlineData("Twice(x) = x + x\nTwice(tick()), tick()", "S[2, 2]")]
    // Alias creation and callable transport tick nothing; each invocation ticks once.
    [InlineData("T = tick\nApply(f) = f()\nT(), Apply(tick), tick()", "S[1, 2, 3]")]
    // The unselected branch is never demanded.
    [InlineData("if(false, tick(), 0), tick()", "S[0, 1]")]
    [InlineData("if(true, tick(), tick()), tick()", "S[1, 2]")]
    // META: capture is inert; each explicit replay is a fresh execution of the captured call.
    [InlineData("Replay(meta op) = op.Invoke() + op.Invoke()\nReplay(tick()), tick()", "S[3, 3]")]
    public async Task TheRequestedContract_HoldsOnEveryRoute(string source, string expected)
        => Assert.Equal(expected, await OkAsync(source));

    [Theory]
    // Evaluation ORDER is observable through the counter: operands left to right, rows in order.
    [InlineData("tick() * 10 + tick()", "12")]
    [InlineData("tick() - tick()", "-1")]
    [InlineData("[tick(), tick()], (tick(), tick())", "S[L[1, 2], S[3, 4]]")]
    [InlineData("A = tick()\nB = tick()\nB, A, B", "S[1, 2, 1]")]
    // A string hole is one ordinary value read.
    [InlineData("\"{tick()}-{tick()}\"", "'1-2'")]
    // Each `map` callback invocation is a fresh call of the transform.
    [InlineData("map([10, 20, 30], { x + tick() })", "L[11, 22, 33]")]
    // `reduce` demands its initial value first, then each step.
    [InlineData("reduce([1, 2], { e * 10 + a }, tick()), tick()", "S[31, 2]")]
    public async Task TheCounterObservesTheExistingDemandOrder(string source, string expected)
        => Assert.Equal(expected, await OkAsync(source));

    // ── Bare references ──

    [Theory]
    [InlineData("tick")]
    [InlineData("tick + 1")]
    [InlineData("A = tick\nA")]
    [InlineData("A = tick\nA + 1")]
    [InlineData("F(x) = x + 1\nF(tick)")]
    [InlineData("count([tick])")]
    [InlineData("if(true, tick, 0)")]
    [InlineData("\"{tick}\"")]
    public async Task ABareValueDemand_RequiresTheExplicitInvocation_AndTicksNothing(string source)
    {
        var outcome = await ErrAsync(source);
        Assert.StartsWith("IllegalInEval: ", outcome.Errors[0], StringComparison.Ordinal);
        Assert.Contains(InvocationRequired, outcome.Errors[0], StringComparison.Ordinal);
        foreach (var optimized in new[] { false, true })
        {
            var (result, budget) = Observe(source, optimized);
            Assert.Equal(InvocationRequired, Assert.IsType<EvalError.IllegalInEval>(Innermost(result.Error)).Reason);
            Assert.Equal(0, budget.TickCount);
        }
    }

    [Fact]
    public async Task TheInvocationRequiredDiagnostic_IsStructured_NeverAZeroZeroArityReport()
    {
        var result = KatLangEngine.Run("tick");
        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.IllegalInEval, error.Code);
        Assert.Contains("write `tick()`", error.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("expected 0", error.Message, StringComparison.Ordinal);
        // Unrelated builtins keep their own empty-call arity report.
        Assert.StartsWith("ArityMismatch: ", (await ErrAsync("sum")).Errors[0], StringComparison.Ordinal);
    }

    [Theory]
    // Callable identity is obtained, transported and inspected without executing anything.
    [InlineData("T = tick\nIgnore(f) = 7\nIgnore(tick), Ignore(T)", "S[7, 7]")]
    [InlineData("A = tick()\nB = 5\nB", "5")]
    [InlineData("A = tick()\nF(x) = 0\nF(A)", "0")]
    [InlineData("Same(f, f) = 1\nT = tick\nSame(tick, T)", "1")]
    public async Task UnusedComputationsAndCallableTransport_TickNothing(string source, string expected)
    {
        Assert.Equal(expected, await OkAsync(source));
        foreach (var optimized in new[] { false, true })
            Assert.Equal(0, Observe(source, optimized).Budget.TickCount);
    }

    // ── Arity ──

    [Theory]
    // An ordinary surplus argument is never demanded: arity precedes every VALUE demand.
    [InlineData("tick(1 / 0)", 1)]
    [InlineData("tick(trace(1))", 1)]
    [InlineData("tick(1, 2)", 2)]
    // An extension call supplies its receiver: never a silent zero-argument call.
    [InlineData("5.tick", 1)]
    [InlineData("5.tick()", 1)]
    [InlineData("T = tick\nT(1)", 1)]
    public async Task ASuppliedArgument_IsTheOrdinaryArityRejection_WithoutDemandOrTick(string source, int actual)
    {
        var outcome = await ErrAsync(source);
        Assert.StartsWith("ArityMismatch: ", outcome.Errors[0], StringComparison.Ordinal);
        Assert.Contains("`tick` expects 0", outcome.Errors[0], StringComparison.Ordinal);
        Assert.Empty(outcome.HostCalls);
        var (result, budget) = Observe(source);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
        Assert.Equal((0, actual), (arity.Expected, arity.Actual));
        Assert.Equal(0, budget.TickCount);
    }

    [Fact]
    public async Task AnExplicitSpread_IsFormedBeforeTheArityCheck()
    {
        // Supply formation evaluates an explicit spread before cardinality, exactly as for every callee.
        var outcome = await ErrAsync("tick(trace(5)*)");
        Assert.StartsWith("ArityMismatch: ", outcome.Errors[0], StringComparison.Ordinal);
        Assert.Equal(["trace(5)"], outcome.HostCalls);
        Assert.StartsWith("DivisionByZero: ", (await ErrAsync("tick((1 / 0)*)")).Errors[0], StringComparison.Ordinal);
        // An empty spread supplies nothing: the call is the accepted zero-argument call.
        Assert.Equal("1", await OkAsync("tick(()*)"));
    }

    // ── Transparent references, carriers, shadowing ──

    [Theory]
    // A transparent reference reads its target's cache and invokes its target freshly (OD-E).
    [InlineData("A = tick()\nB = A\nB, A, B(), A, B", "S[1, 1, 2, 1, 1]")]
    // A forwarding carrier forwards every explicit call freshly to its target; its bare read is the
    // target's bare view.
    [InlineData("A = tick()\nC = {\n    public M = 0\n    A\n}\nC, A, C(), A", "S[1, 1, 2, 1]")]
    // An alias of tick itself owns no entry: every call is a fresh tick.
    [InlineData("T = tick\nU = T\nT(), U(), T()", "S[1, 2, 3]")]
    public async Task ReferencesAndCarriers_KeepTheirExistingPublicationBehavior(string source, string expected)
        => Assert.Equal(expected, await OkAsync(source));

    [Theory]
    // A user binding named `tick` shadows the prelude completely: no dispatch by spelling.
    [InlineData("tick = 5\ntick + 1", "6")]
    [InlineData("tick(x) = x + 100\ntick(1)", "101")]
    [InlineData("F(tick) = tick * 2\nF(4)", "8")]
    [InlineData("Box = {\n    public tick = 40\n}\nBox.tick + 2", "42")]
    public async Task AUserBindingNamedTick_IsAnOrdinaryBinding(string source, string expected)
    {
        Assert.Equal(expected, await OkAsync(source));
        Assert.Equal(0, Observe(source).Budget.TickCount);
    }

    // ── Run lifetime ──

    [Fact]
    public void RepeatedRuns_OfOneParsedProgram_EachStartAtZero()
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid("tick(), tick()").Root);
        var options = new RunOptions();
        for (var run = 0; run < 3; run++)
        {
            var (result, budget) = Evaluator.RunCountedObserved(program);
            Assert.Equal("S[1, 2]", SixRouteAgreement.Neutral(result.Value.Value));
            Assert.Equal(2, budget.TickCount);
            var engine = Assert.IsType<RunResult.Success>(KatLangEngine.Run("tick(), tick()", options));
            Assert.Equal("S[1, 2]", SixRouteAgreement.Neutral(engine.Value));
        }
    }

    [Fact]
    public async Task ConcurrentIndependentRuns_NeverShareACounter()
    {
        var results = await Task.WhenAll(Enumerable.Range(0, 16).Select(_ => Task.Run(() =>
            KatLangEngine.Run("Step(n) = n + tick()\nStep(0).repeat(50), tick()"))));
        // Each run: 1 + 2 + … + 50 = 1275, then the 51st tick.
        Assert.All(results, result => Assert.Equal("S[1275, 51]",
            SixRouteAgreement.Neutral(Assert.IsType<RunResult.Success>(result).Value)));
    }

    [Fact]
    public void ASeparateRunStartedByHostCode_HasItsOwnCounter()
    {
        var operations = HostOperations.Create(HostOperation.Create(
            "inner",
            (_, _) => Assert.IsType<RunResult.Success>(KatLangEngine.Run("tick(), tick()")).Value));
        var result = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run("tick(), inner(), tick()", new RunOptions { HostOperations = operations }));
        Assert.Equal("S[1, S[1, 2], 2]", SixRouteAgreement.Neutral(result.Value));
    }

    // ── Strategies, async, limits, cancellation ──

    [Theory]
    [InlineData("Step(n) = n + tick()\nStep(0).repeat(3), tick()", "S[6, 4]")]
    // Condition first (LOOP-CF1): the flag row ticks before the state row in every round.
    [InlineData("Step(n) = { n + tick(), tick() < 6 }\nStep(0).while, tick()", "S[12, 8]")]
    // `M` reads no parameter of the step, so it is ONE exported entry for the run, not one per iteration.
    [InlineData("Step(n) = { M = tick()\n    n + M + M }\nStep(0).repeat(2)", "4")]
    // A local helper that reads the step parameter is per activation: it ticks once per iteration.
    [InlineData("Step(n) = { M = n + tick()\n    M + M }\nStep(0).repeat(2)", "8")]
    public async Task PlannedLoops_AgreeWithTheGenericEvaluator(string source, string expected)
    {
        Assert.Equal(expected, await OkAsync(source));
        var loops = new LoopOptimizationDiagnostics();
        var optimized = Observe(source, optimized: true, loops: loops);
        var generic = Observe(source, optimized: false);
        Assert.True(loops.GetSnapshot().OptimizedLoopHits > 0, "the optimized route planned no loop");
        Assert.Equal(generic.Budget.TickCount, optimized.Budget.TickCount);
        Assert.Equal(generic.Budget.ConsumedSteps, optimized.Budget.ConsumedSteps);
    }

    [Fact]
    public async Task TheFusedFilterCountPipeline_AgreesWithTheGenericEvaluator()
    {
        // The predicate ticks once per element, left to right: 1+1, 2+2 fail; 3+3, 4+4 pass.
        const string source = "P(x) = tick() + x > 4\n[1, 2, 3, 4].filter(P).count, tick()";
        Assert.Equal("S[2, 5]", await OkAsync(source));
        var sequences = new SequencePipelineDiagnostics();
        var optimized = Observe(source, optimized: true, sequences: sequences);
        Assert.True(sequences.FilterCountFusionHits > 0, "the optimized route did not fuse the pipeline");
        Assert.Equal(5, optimized.Budget.TickCount);
        Assert.Equal(Observe(source).Budget.ConsumedSteps, optimized.Budget.ConsumedSteps);
    }

    [Fact]
    public async Task GenuineAsyncSuspension_SharesTheRunCounter()
    {
        // `trace` suspends on the twin routes: ticks before and after each suspension continue one counter.
        Assert.Equal("S[1, 2, 3, 4]", await OkAsync("tick(), trace(tick()), tick(), trace(tick())"));
        var (result, budget) = await Evaluator.RunCountedObservedAsync(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid("A = tick()\nA, A(), A").Root),
            zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache());
        Assert.Equal("S[1, 2, 1]", SixRouteAgreement.Neutral(result.Value.Value));
        Assert.Equal(2, budget.TickCount);
    }

    [Fact]
    public void SharedDemands_ExecuteOnce()
    {
        // One cell demanded by several consumers and through forwarding is ONE execution (single flight).
        const string source = "F(x) = G(x, x) + x\nG(a, b) = a * b\nF(tick()), tick()";
        var (result, budget) = Observe(source);
        Assert.Equal("S[2, 2]", SixRouteAgreement.Neutral(result.Value.Value));
        Assert.Equal(2, budget.TickCount);
    }

    [Fact]
    public async Task OverlappingDemands_ShareOneTickAcrossSuspensionAndMemoReads()
    {
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var operations = HostOperations.Create(HostOperation.CreateAsync("pause", async (_, _) =>
        {
            entered.TrySetResult();
            await release.Task;
            return new Result.Atom(0);
        }));
        var parsed = Parser.Parse("tick() + pause()", new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
        var budget = EvaluationBudget.Create(null, hostOperations: operations);
        budget.MarkAsynchronousRun();
        // Match the production async entry: its twin requires the generic strategies.
        var services = Evaluator.RunServices.Unconfigured with
        {
            EnableLoopOptimization = false,
            EnableSequencePipelineOptimization = false,
        };
        var ctx = (Evaluator.EvalCtx.Empty with { Budget = budget, Services = services })
            .Push(operations.RuntimePreludeAlgorithm);
        var cell = Evaluator.SupplyCell(new Expr.AlgorithmExpr(parsed.Root), ctx, []);
        var demands = Enumerable.Range(0, 32).Select(_ => cell.DemandAsync().AsTask()).ToArray();
        try
        {
            var startup = await Task.WhenAny(entered.Task, demands[0]).WaitAsync(TimeSpan.FromSeconds(30));
            if (startup == demands[0])
            {
                var early = await demands[0];
                Assert.Fail($"The computation completed before suspension: {early}");
            }
            Assert.All(demands, demand => Assert.False(demand.IsCompleted));
            Assert.Equal(1, budget.TickCount);
        }
        finally
        {
            release.TrySetResult();
        }

        var outcomes = await Task.WhenAll(demands).WaitAsync(TimeSpan.FromSeconds(30));
        Assert.All(outcomes, outcome =>
        {
            Assert.True(outcome.IsOk, outcome.IsError ? outcome.Error.ToString() : "");
            Assert.Equal("1", SixRouteAgreement.Neutral(outcome.Value.Value));
        });
        Assert.Same(outcomes[0].Value.Value, cell.Demand().Value.Value);
        Assert.Same(outcomes[0].Value.Value, (await cell.DemandAsync()).Value.Value);
        Assert.Equal(1, budget.TickCount);
    }

    [Fact]
    public async Task AsyncCallableResolution_RetriesNeverRepeatTheReceiverTick()
    {
        // The runtime projection must await the reference-producing receiver. `trace` genuinely
        // suspends on the twin routes; resolver retries must reuse that receiver's completed VALUE.
        const string source = "Capture(meta op) = if(trace(tick()) > 0, op, op)\n"
            + "R = Capture(tick())\nApply(f) = f() + f()\nApply(R.Algorithm), tick()";
        Assert.Equal("S[5, 4]", await OkAsync(source));
        Assert.Equal(4, Observe(source).Budget.TickCount);
    }

    [Fact]
    public void AStepLimit_StopsTheRunBeforeLaterTicks_OnEveryStrategy()
    {
        const string source = "tick(), tick(), tick(), tick()";
        var full = Observe(source).Budget.ConsumedSteps;
        var previous = 0L;
        for (var maxSteps = 1L; maxSteps <= full; maxSteps++)
        {
            var limits = new EvaluationLimits { MaxSteps = maxSteps };
            var generic = Observe(source, optimized: false, limits: limits);
            var optimized = Observe(source, optimized: true, limits: limits);
            Assert.Equal(generic.Budget.TickCount, optimized.Budget.TickCount);
            Assert.True(generic.Budget.TickCount >= previous, "raising the limit lost a tick");
            if (generic.Result.IsError)
            {
                Assert.True(generic.Result.Error.IsResourceLimit, generic.Result.Error.ToString());
                Assert.True(generic.Budget.TickCount < 4);
            }
            else
            {
                Assert.Equal(4, generic.Budget.TickCount);
            }

            previous = generic.Budget.TickCount;
        }
    }

    [Fact]
    public async Task Cancellation_StopsTheRunBeforeALaterTick()
    {
        using var cancellation = new CancellationTokenSource();
        var operations = HostOperations.Create(HostOperation.Create("stop", (_, _) =>
        {
            cancellation.Cancel();
            return new Result.Atom(0);
        }));
        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var parsed = Parser.Parse("P = tick() + stop()\nP, tick()", new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
        var program = new Expr.AlgorithmExpr(parsed.Root);
        await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await Evaluator.RunCountedObservedAsync(
            program, zeroArgPropertyResultCache: cache, hostOperations: operations, cancellationToken: cancellation.Token));
        Assert.Equal(1, cache.ObservedBudget!.TickCount);
    }

    [Fact]
    public void TheCounter_IsIndependentOfTheRandomStream()
    {
        const string withTicks = "tick(), random(0, 1), tick(), randomInt(0, 1000000), tick()";
        const string withoutTicks = "random(0, 1), randomInt(0, 1000000)";
        var ticked = Observe(withTicks, randomSeed: 42).Result.Value.Value;
        var plain = Observe(withoutTicks, randomSeed: 42).Result.Value.Value;
        var items = Assert.IsType<Result.SequenceValue>(ticked).Items;
        Assert.Equal(["1", "2", "3"], new[] { items[0], items[2], items[4] }.Select(SixRouteAgreement.Neutral));
        var draws = Assert.IsType<Result.SequenceValue>(plain).Items;
        Assert.Equal(draws[0], items[1]);
        Assert.Equal(draws[1], items[3]);
    }

    // ── The checked boundary ──

    [Fact]
    public async Task TheCounterBoundary_IsExact_AndExhaustionIsADeterministicDomainFailure()
    {
        using (TickCounterTestSeam.Activate(EvaluationBudget.MaxTickCount - 2))
        {
            var (result, budget) = Observe("tick(), tick()");
            Assert.Equal("S[9223372036854775806, 9223372036854775807]", SixRouteAgreement.Neutral(result.Value.Value));
            Assert.Equal(EvaluationBudget.MaxTickCount, budget.TickCount);
            var last = Assert.IsType<Result.Atom>(Assert.IsType<Result.SequenceValue>(result.Value.Value).Items[1]);
            Assert.Equal((Decimal128)long.MaxValue, last.Value);
        }

        using (TickCounterTestSeam.Activate(EvaluationBudget.MaxTickCount))
        {
            foreach (var optimized in new[] { false, true })
            {
                var (result, budget) = Observe("A = 1\nA, tick(), A", optimized);
                Assert.False(result.Error.IsResourceLimit);
                var error = Assert.IsType<EvalError.IllegalInEval>(Innermost(result.Error));
                Assert.Equal(Evaluator.TickExhaustedMessage, error.Reason);
                // The counter neither wraps nor saturates into a duplicate: it stays where it was.
                Assert.Equal(EvaluationBudget.MaxTickCount, budget.TickCount);
            }

            var engine = Assert.IsType<RunResult.EvalFailure>(
                await KatLangEngine.RunAsync("tick()", new RunOptions()));
            Assert.Equal(KatLangErrorCode.IllegalInEval, Assert.Single(engine.Errors).Code);
        }

        // Outside the seam every run starts at zero again.
        Assert.Equal(1, Observe("tick()").Budget.TickCount);
    }

    // ── Hosting and tooling ──

    [Fact]
    public void TheBuiltinName_IsReservedForHostOperations()
    {
        var error = Assert.Throws<ArgumentException>(() => HostOperation.Create("tick", (_, _) => new Result.Atom(0)));
        Assert.Contains("reserved", error.Message, StringComparison.Ordinal);
        Assert.Throws<ArgumentException>(() => HostOperation.CreateAsync("tick", (_, _) => ValueTask.FromResult<Result>(new Result.Atom(0))));
        // An unreserved name stays available, so the suite's host counter is `tock`.
        Assert.NotNull(HostOperation.Create("tock", (_, _) => new Result.Atom(0)));
    }

    [Fact]
    public void TheRegistry_DeclaresAZeroArityBuiltinWithNoDotParameters()
    {
        var descriptor = BuiltinRegistry.GetBuiltin(BuiltinId.@tick);
        Assert.Equal("tick", descriptor.Name);
        Assert.Equal(0, descriptor.FixedArity);
        Assert.Empty(descriptor.PlainParameters);
        Assert.Empty(descriptor.DotParameters);
        Assert.Null(descriptor.SequenceMetadata);
        Assert.False(descriptor.DeclaresMetaParameter);
        Assert.Equal("tick", descriptor.PlainSignature.DisplayText);
        Assert.True(descriptor.AcceptsArity(0));
        Assert.False(descriptor.AcceptsArity(1));
    }

    [Fact]
    public void AnalysisAndElaboration_ExecuteNothing()
    {
        // The front end and the semantic model never evaluate; a bare reference is no lifted call.
        var parsed = SourceProvenance.ParseValid("T = tick\nA = tick()\nT(), A");
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        Assert.NotNull(model);
        var alias = Assert.Single(parsed.Root.Properties, static property => property.Name == "T");
        Assert.IsType<Algorithm.Alias>(alias.Value);
        var (result, budget) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root));
        Assert.Equal("S[1, 2]", SixRouteAgreement.Neutral(result.Value.Value));
        Assert.Equal(2, budget.TickCount);
    }
}
