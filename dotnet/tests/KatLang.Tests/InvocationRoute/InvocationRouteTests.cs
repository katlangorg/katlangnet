using KatLang.Evaluation;

namespace KatLang.Tests.InvocationRoute;

/// <summary>
/// META-S3-4: focused assertions for generalized invocation capture — the mandatory programs, the settled
/// decisions D-1A (inert syntactic capture, delayed intrinsic refusal), D-2A (explicit invocation syntax),
/// D-3 (one retained receiver per plan), D-4 (route resolution before supply access) and D-5 (the extension
/// receiver is supplied), original-cell transport through a rebuilt invocation, real concurrent observers
/// through a genuinely suspended runtime receiver, run ownership, and the receiver-checkpoint and
/// async-preparation corrections of the independent research review (§ O).
/// </summary>
public class InvocationRouteTests
{
    private static readonly TimeSpan Wait = TimeSpan.FromSeconds(30);

    private static string Run(string source)
    {
        var result = KatLangEngine.Run(source);
        return result is RunResult.Success success ? InvocationRouteCorpus.Value(success.Value) : "FAIL " + result.ToDisplayString();
    }

    private static async Task<string> RunAsync(string source)
    {
        var result = await KatLangEngine.RunAsync(source);
        return result is RunResult.Success success ? InvocationRouteCorpus.Value(success.Value) : "FAIL " + result.ToDisplayString();
    }

    // ── The mandatory programs ───────────────────────────────────────────────────────────────────────────

    public static TheoryData<string, string> MandatoryPrograms => new()
    {
        { "Step(x) = x + 1, x < 3\n\nLoop(meta op) = op.Algorithm(op.Arguments*).while\n\nStep(0).Loop", "3" },
        { "Step(x) = x + 1, x < 3\nLoop(meta op) = while(op.Algorithm(op.Arguments*))\nStep(0).Loop", "3" },
        { "Step(x) = x + 1, x < 3\nLoop(meta op) = (op.Algorithm)(op.Arguments*).while\nStep(0).Loop", "3" },
        // `Box = { Step }` is a callable ALIAS of `Step` (FWD-02), not a member declaration, under the
        // current rules; the member must be declared inside the block.
        { "Box = {\n    Step(x) = x + 1, x < 3\n}\n\nBox.Step(0).while", "3" },
        { "Math.Abs(-3).repeat(2)", "3" },
        { "Inc(x) = x + 1\n\nRepeat(meta op, count) =\n    op.Algorithm(op.Arguments*).repeat(count)\n\nInc(0).Repeat(5)", "5" },
        { "Inspect(meta operation) = operation.Arguments.count\n\nInspect(Math.Abs(-3))", "1" },
    };

    [Theory]
    [MemberData(nameof(MandatoryPrograms))]
    public async Task MandatoryPrograms_ReturnTheirValue_OnEveryEngine(string source, string expected)
    {
        Assert.Equal(expected, Run(source));
        Assert.Equal(expected, await RunAsync(source));
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors);
        foreach (var optimized in new[] { false, true })
        {
            var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), enableOptimizations: optimized);
            Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
            Assert.Equal(expected, InvocationRouteCorpus.Value(result.Value.Value));
        }
    }

    [Fact]
    public void TheMotivatingWrapper_UsesTheNativeOptimizedLoop()
    {
        var parsed = SourceProvenance.ParseValid("Step(x) = x + 1, x < 3\nLoop(meta op) = op.Algorithm(op.Arguments*).while\nStep(0).Loop");
        var loops = new KatLang.Optimizations.Loops.LoopOptimizationDiagnostics();
        var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), enableOptimizations: true, loopDiagnostics: loops);
        Assert.Equal("3", InvocationRouteCorpus.Value(result.Value.Value));
        Assert.Equal(1, loops.OptimizedLoopHits);
        Assert.Equal(0, loops.OptimizedLoopFallbacks);
    }

    [Fact]
    public async Task TheMandatoryPrograms_ReturnTheirValues_AfterAGenuineSuspension()
    {
        foreach (var row in MandatoryPrograms)
        {
            var source = Assert.IsType<string>(row[0]);
            var expected = Assert.IsType<string>(row[1]);
            var finalRow = source.LastIndexOf('\n') + 1;
            var gated = source[..finalRow] + "if(aflag(), " + source[finalRow..] + ", 0)";
            var suspensions = 0;
            var operations = HostOperations.Create(HostOperation.CreateAsync("aflag", async (_, _) =>
            {
                await Task.Yield();
                suspensions++;
                return new Result.Bool(true);
            }));
            var result = await KatLangEngine.RunAsync(gated, new RunOptions { HostOperations = operations });
            var success = Assert.IsType<RunResult.Success>(result);
            Assert.Equal(expected, InvocationRouteCorpus.Value(success.Value));
            Assert.Equal(1, suspensions);
        }
    }

    [Fact]
    public async Task AHostException_KeepsItsIdentity_AfterAGenuineSuspension_ThroughACapturedMemberInvocation()
    {
        var boom = new InvalidOperationException("boom after suspension");
        var suspended = 0;
        var operations = HostOperations.Create(
            HostOperation.CreateAsync("aflag", async (_, _) => { await Task.Yield(); Interlocked.Increment(ref suspended); return new Result.Bool(true); }),
            HostOperation.Create("boom", (_, _) => throw boom));
        var parsed = Parser.Parse("""
            Capture(meta op) = op
            Box = { G(x) = x * 10 }
            R = Capture(Box.G(boom()))
            if(aflag(), R.Invoke(), 0)
            """, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors);
        var thrown = await Assert.ThrowsAsync<InvalidOperationException>(async () =>
            await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root), hostOperations: operations));
        Assert.Same(boom, thrown);
        Assert.Equal(1, suspended);
    }

    // ── D-1A: inert syntactic capture; refusal at the first route-dependent operation ────────────────────

    [Fact]
    public void IntrinsicShapedCapture_IsInert_AndItsReferenceIdentityNeedsNoRoute()
    {
        Assert.Equal("(0, 0, true)", Run("""
            Ignore(meta op) = 0
            Capture(meta operation) = operation
            R = Capture(5.string())
            Ignore(5.string()), Ignore(5.Invoke()), R == R
            """));
        // Obtaining and comparing the argument view, and an empty selection, need no supply.
        Assert.Equal("(true, false)", Run("""
            Capture(meta operation) = operation
            R = Capture(5.string())
            V = R.Arguments
            V == R.Arguments, V == Capture(5.string()).Arguments
            """));
    }

    [Fact]
    public async Task IntrinsicCapture_IdentityAndEmptySelection_DoNotDemandAnEffectfulReceiver()
    {
        const string source = """
            Ignore(meta op) = 0
            R = Capture(trace(5).string())
            Ignore(trace(1).string()), Ignore(trace(2).Invoke()), Ignore(trace(3).Arguments(boom())),
            R == R, R.Arguments == R.Arguments, R.Arguments[].count
            """;
        foreach (var mode in new[] { 0, 1, 2 })
        {
            var observed = await InvocationRouteCorpus.Observe(new("inert-intrinsic-receiver", source), mode);
            Assert.Equal("ok (0, 0, 0, true, true, 0)", observed.Outcome);
            Assert.Equal("", observed.Trace);
            Assert.Equal(0, observed.Formations);
        }
    }

    public static TheoryData<string> RouteDependentOperations => new()
    {
        "R.Invoke()",
        "R.Algorithm",
        "R.Algorithm(1)",
        "R.Arguments.count",
        "R.Arguments[0]",
        "R.Arguments.first",
        "Id(R.Arguments*)",
        "while(R.Invoke())",
    };

    [Theory]
    [MemberData(nameof(RouteDependentOperations))]
    public void RouteDependentOperations_RefuseAnIntrinsicRoute_WithTheDedicatedDiagnostic(string operation)
    {
        foreach (var captured in new[] { "5.string()", "Capture(Inc(1)).Invoke()", "Capture(Inc(1)).Arguments(1)" })
        {
            var result = KatLangEngine.Run($"Capture(meta operation) = operation\nInc(x) = x + 1\nId(x) = x\nR = Capture({captured})\n{operation}");
            var failure = Assert.IsType<RunResult.EvalFailure>(result);
            var error = Assert.Single(failure.Errors);
            Assert.Equal(KatLangErrorCode.NotAnAlgorithm, error.Code);
            Assert.Contains("is not a callable invocation", error.Message, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void CapturedIntrinsics_KeepTheirOrdinaryValue()
    {
        const string Library = "Capture(meta operation) = operation\nId(x) = x\nInc(x) = x + 1\n";
        Assert.Equal("'5'", Run(Library + "Id(5.string())"));
        Assert.Equal("2", Run(Library + "Id(Capture(Inc(1)).Invoke())"));
        // The original VALUE of an invalid `.Arguments(...)` keeps its ordinary refusal.
        var ordinary = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(Library + "Capture(Inc(1)).Arguments(1)"));
        var planned = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(Library + "Id(Capture(Inc(1)).Arguments(1))"));
        var ordinaryError = Assert.Single(ordinary.Errors);
        var plannedError = Assert.Single(planned.Errors);
        Assert.Equal(KatLangErrorCode.IllegalInEval, ordinaryError.Code);
        Assert.Equal(KatLangErrorCode.IllegalInEval, plannedError.Code);
        Assert.EndsWith(ordinaryError.Message, plannedError.Message, StringComparison.Ordinal);
    }

    // ── D-2A: an explicit argument list makes the invocation ────────────────────────────────────────────

    [Fact]
    public void ArgumentlessMemberAndPropertyReads_StayOutsideTheDomain()
    {
        const string Library = "Inspect(meta operation) = operation.Arguments.count\nInc(x) = x + 1\nBox = { V = 7\n G(x) = x * 10 }\n";
        Assert.Equal("1", Run(Library + "Inspect(5.Inc())"));
        Assert.Equal("0", Run(Library + "Inspect(Box.V())"));
        foreach (var notAnInvocation in new[] { "5.Inc", "Box.G", "Box.V", "Inc", "Box.G(1).Inc" })
        {
            var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(Library + $"Inspect({notAnInvocation})"));
            Assert.Contains("A meta parameter needs a supplied call computation", Assert.Single(failure.Errors).Message, StringComparison.Ordinal);
        }
        // Member projection and callable forwarding are unchanged.
        Assert.Equal("(70, [10, 20])", Run(Library + "Apply(f, x) = f(x)\nApply(Box.G, 7), [1, 2].map(Box.G)"));
    }

    [Fact]
    public void NoImplicitProvenance_AnEvaluatedPropertyIsNotItsCall()
    {
        foreach (var source in new[] { "Step(x) = x + 1, x < 3\nStart = Step(0)\nStart.while", "Step(x) = x + 1, x < 3\nStart = Step(0)\nwhile(Start)" })
        {
            var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
            Assert.Contains("A meta parameter needs a supplied call computation", Assert.Single(failure.Errors).Message, StringComparison.Ordinal);
        }
    }

    // ── D-4 / D-5: route resolution and the extension supply ────────────────────────────────────────────

    [Fact]
    public void AnExtensionCapture_SuppliesItsReceiverFirst_AndProjectsTheFallback()
    {
        const string Library = "Capture(meta operation) = operation\nAdd(a, b) = a + b\nApply(f, x) = f(x)\nBox = { G(x) = x * 10 }\n";
        Assert.Equal("(2, 5, 1, 6, 30)", Run(Library + "R = Capture(5.Add(1))\nR.Arguments.count, R.Arguments[0], R.Arguments[1], R.Invoke(), R.Algorithm(10, 20)"));
        Assert.Equal("(1, 2, 20, 30)", Run(Library + "R = Capture(Box.G(2))\nR.Arguments.count, R.Arguments[0], R.Invoke(), R.Algorithm(3)"));
        var arity = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(Library + "R = Capture(5.Add(2))\nApply(R.Algorithm, 7)"));
        Assert.Equal(KatLangErrorCode.ArityMismatch, Assert.Single(arity.Errors).Code);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task Repeat_ResolvesARuntimeRoute_BeforeCount_AndMaterializesStateAfterCount(bool countThrows)
    {
        const string source = """
            Capture(meta op) = op
            MkBox(k) = {
              G(x) = body(x)
              k
            }
            R = if(route(), Capture(MkBox(1)), 0)
            Use(b) = b.G(argument()).repeat(iterations())
            Use(R.Algorithm)
            """;
        foreach (var mode in new[] { 0, 1, 2 })
        {
            var effects = new List<string>();
            var boom = new InvalidOperationException("count failure");
            var suspended = 0;
            var operations = HostOperations.Create(
                mode == 2
                    ? HostOperation.CreateAsync("route", async (_, _) =>
                    {
                        await Task.Yield();
                        suspended++;
                        effects.Add("route");
                        return new Result.Bool(true);
                    })
                    : HostOperation.Create("route", (_, _) => { effects.Add("route"); return new Result.Bool(true); }),
                HostOperation.Create("iterations", (_, _) =>
                {
                    effects.Add("count");
                    if (countThrows) throw boom;
                    return new Result.Atom(0);
                }),
                HostOperation.Create("argument", (_, _) => { effects.Add("argument"); return new Result.Atom(2); }),
                HostOperation.Create("body", (args, _) => { effects.Add("body"); return args[0]; }, "x"));
            var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
            Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));
            async Task Evaluate()
            {
                var result = mode == 2
                    ? (await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root), hostOperations: operations)).Result
                    : Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), enableOptimizations: mode == 1, hostOperations: operations).Result;
                Assert.True(result.IsOk);
                Assert.Equal("2", InvocationRouteCorpus.Value(result.Value.Value));
            }
            if (countThrows)
                Assert.Same(boom, await Assert.ThrowsAsync<InvalidOperationException>(Evaluate));
            else
                await Evaluate();
            Assert.Equal(countThrows ? ["route", "count"] : ["route", "count", "argument"], effects);
            Assert.Equal(mode == 2 ? 1 : 0, suspended);
        }
    }

    [Fact]
    public void ADeclaredMemberWins_WhateverItsSpelling()
    {
        Assert.Equal("(1, 200, 200)", Run("""
            Inspect(meta operation) = operation.Arguments.count
            Capture(meta operation) = operation
            Box4 = { Algorithm(x) = x * 100 }
            Inspect(Box4.Algorithm(2)), Capture(Box4.Algorithm(2)).Invoke(), Box4.Algorithm(2).repeat(1)
            """));
        Assert.Equal("(10, 10)", Run("""
            Capture(meta operation) = operation
            Box = { G(x) = x * 10 }
            G(x) = x + 1000
            Capture(Box.G(1)).Invoke(), Box.G(1).repeat(1)
            """));
    }

    // ── Plan identity, shared cells, D-3 ─────────────────────────────────────────────────────────────────

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void RebuiltPlan_TransportsTheOriginalCells_AndEndedRunsRefuse(bool optimized)
    {
        Result.CallReference? rebuilt = null;
        var traces = 0;
        var operations = HostOperations.Create(
            HostOperation.Create("trace", (args, _) => { traces++; return args[0]; }, "x"),
            HostOperation.Create("Meta", (_, _) => throw new InvalidOperationException("ordinary Meta reached"), "original", "rebuilt"));
        var seam = new InvocationPlanTestSeam(new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>
        {
            ["Meta"] = cells =>
            {
                var firstValue = cells[0]!.Demand();
                Assert.True(firstValue.IsOk);
                var original = Assert.IsType<Result.CallReference>(firstValue.Value.Value);
                var reified = Evaluator.ReifyMeta(cells[1]);
                Assert.True(reified.IsOk);
                rebuilt = reified.Value;
                // Two distinct plans; nothing prepared, demanded or executed by capture.
                Assert.NotSame(original.Plan, rebuilt.Plan);
                Assert.Same(cells[1], rebuilt.Plan.Owner);
                Assert.Equal(0, original.Plan.SupplyFormations);
                Assert.Equal(0, rebuilt.Plan.SupplyFormations);
                Assert.Null(rebuilt.Plan.RouteState);
                Assert.Equal(0, traces);
                Assert.Equal(0, original.Plan.Caller.Budget.TickCount);
                Assert.Equal("8", InvocationRouteCorpus.Value(rebuilt.Invoke().Value.Value));
                // The receiver is the transported META adapter cell itself, even though an ordinary
                // invocation preserves the written parameter read's checkpoint and error protocol.
                var linkCell = rebuilt.Plan.CalleeCell;
                var link = Assert.IsType<Evaluator.LinkSuspension>(linkCell.Suspension);
                Assert.Same(cells[0], link.Receiver(Assert.IsType<Expr.DotCall>(linkCell.Source)));
                // The rebuilt plan's argument IS the original plan's argument cell (not a copy).
                Assert.Same(Assert.Single(original.Plan.PreparedCells!), Assert.Single(rebuilt.Plan.PreparedCells!));
                Assert.Equal("9", InvocationRouteCorpus.Value(original.Invoke().Value.Value));
                Assert.Equal("10", InvocationRouteCorpus.Value(rebuilt.Plan.Owner.Demand().Value.Value));
                Assert.Equal("10", InvocationRouteCorpus.Value(rebuilt.Plan.Owner.Demand().Value.Value));
                Assert.Same(Assert.Single(original.Plan.PreparedCells!), Assert.Single(rebuilt.Plan.PreparedCells!));
                Assert.Equal(1, original.Plan.SupplyFormations);
                Assert.Equal(1, rebuilt.Plan.SupplyFormations);
                // The rebuilt `op.Algorithm(...)` plan retained its `.Algorithm` route (a shared singleton).
                Assert.Same(Evaluator.PlanRoute.AlgorithmIntrinsic, rebuilt.Plan.RouteState);
                return new Result.Atom(0);
            },
        });
        var parsed = Parser.Parse("""
            Capture(meta op) = op
            Op(meta op) = Meta(op, op.Algorithm(op.Arguments*))
            Box = { G(x) = x + tick() }
            Op(Box.G(trace(7)))
            """, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));
        using var activation = InvocationPlanTestSeam.Activate(seam);
        var (result, budget) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), enableOptimizations: optimized, hostOperations: operations,
            observations: new EvaluationObservations());
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        Assert.Equal(1, traces);
        Assert.Equal(3, budget.TickCount);
        Assert.True(rebuilt!.Plan.Caller.Budget.RunEnded);
        var ended = Evaluator.InvokeCallReferenceValue(rebuilt, rebuilt.Plan.Caller);
        Assert.Equal(Evaluator.EndedCallReferenceMessage, Assert.IsType<EvalError.IllegalInEval>(ended.Error).Reason);
    }

    [Fact]
    public async Task ConcurrentObservers_ThroughASuspendedRuntimeReceiver_ShareOneRouteCalleeAndSupply()
    {
        var captured = new TaskCompletionSource<Result.CallReference>(TaskCreationOptions.RunContinuationsAsynchronously);
        var alive = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var gateEntered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var receiverRelease = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var runRelease = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        int receivers = 0, traces = 0, bodies = 0;
        Result.CallReference? reference = null;
        var operations = HostOperations.Create(
            HostOperation.Create("Meta", (_, _) => throw new InvalidOperationException("ordinary Meta reached"), "op"),
            HostOperation.Create("Foreign", (_, _) => throw new InvalidOperationException("ordinary Foreign reached"), "x"),
            HostOperation.Create("trace", (args, _) => { Interlocked.Increment(ref traces); return args[0]; }, "x"),
            HostOperation.CreateAsync("gate", async (_, _) =>
            {
                Interlocked.Increment(ref receivers);
                gateEntered.TrySetResult();
                await receiverRelease.Task;
                return new Result.Bool(true);
            }),
            HostOperation.CreateAsync("body", async (args, _) => { Interlocked.Increment(ref bodies); await Task.Yield(); return args[0]; }, "x"),
            HostOperation.CreateAsync("hold", async (_, _) => { alive.TrySetResult(); await runRelease.Task; return new Result.Atom(0); }));
        var seam = new InvocationPlanTestSeam(new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>
        {
            ["Meta"] = cells =>
            {
                var reified = Evaluator.ReifyMeta(cells[0]);
                Assert.True(reified.IsOk);
                reference = reified.Value;
                captured.TrySetResult(reference);
                return new Result.Atom(0);
            },
            ["Foreign"] = cells =>
            {
                var ctx = Assert.IsAssignableFrom<Evaluator.ExpressionSuspension>(cells[0]!.Suspension).Caller;
                var rejected = Evaluator.InvokeCallReferenceValue(reference!, ctx);
                Assert.Equal(Evaluator.ForeignCallReferenceMessage, Assert.IsType<EvalError.IllegalInEval>(rejected.Error).Reason);
                return new Result.Atom(0);
            },
        });
        var options = new RunOptions { HostOperations = operations };
        // `b.G(...)`'s route needs `b`'s CALLABLE, a runtime projection whose receiver suspends in `gate()`.
        var parsed = Parser.Parse("""
            Capture(meta op) = op
            MkBox(k) = {
              G(x) = body(x)
              k
            }
            R = if(gate(), Capture(MkBox(1)), 0)
            Use(b) = Meta(b.G(trace(2)))
            Use(R.Algorithm), hold()
            """, options);
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));
        using var activation = InvocationPlanTestSeam.Activate(seam);
        var running = Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root), hostOperations: operations,
            observations: new EvaluationObservations()).AsTask();
        try
        {
            reference = await captured.Task.WaitAsync(Wait);
            await alive.Task.WaitAsync(Wait);
            // Capture was inert: no receiver, argument or body work.
            Assert.Equal(0, receivers);
            Assert.Equal(0, traces);
            Assert.Equal(0, bodies);
            Assert.Null(reference.Plan.RouteState);
            // Asynchronous supply preparation must await the route through the async adapter (§ O.2),
            // overlapping two thread-pool route/callee observers while the receiver is suspended.
            var preparing = reference.Plan.PrepareSupply(asynchronous: true).AsTask();
            var first = Task.Run(async () => await Evaluator.PlanCalleeCellAsync(reference.Plan));
            var second = Task.Run(async () => await Evaluator.PlanCalleeCellAsync(reference.Plan));
            await gateEntered.Task.WaitAsync(Wait);
            Assert.Equal(1, receivers);
            Assert.False(preparing.IsCompleted);
            receiverRelease.TrySetResult();
            Assert.True((await preparing.WaitAsync(Wait)).IsOk);
            var cells = await Task.WhenAll(first, second).WaitAsync(Wait);
            Assert.All(cells, c => Assert.True(c.IsOk));
            Assert.Same(cells[0].Value, cells[1].Value);
            Assert.IsType<Evaluator.PlanRoute>(reference.Plan.RouteState);
            Assert.Equal(1, receivers);
            Assert.Equal(0, traces);
            Assert.Equal(0, bodies);
            // VALUE and Invoke(): two target executions over ONE argument demand and ONE supply. They run one
            // after the other: a target execution is evaluator work charged to the run's budget, and a run's
            // evaluation is one logical flow (EvaluationBudget, NeedCell concurrency contract) — two at once
            // race the budget's unsynchronized depth counter (~4% of runs underflowed it). Overlapping
            // observers of ONE flight stay covered above.
            var demands = new[]
            {
                await Task.Run(async () => await reference.Plan.Owner.DemandAsync()).WaitAsync(Wait),
                await Task.Run(async () => await reference.InvokeAsync()).WaitAsync(Wait),
            };
            Assert.All(demands, d => { Assert.True(d.IsOk); Assert.Equal("2", InvocationRouteCorpus.Value(d.Value.Value)); });
            Assert.Equal(1, receivers);
            Assert.Equal(1, traces);
            Assert.Equal(2, bodies);
            Assert.Equal(1, reference.Plan.SupplyFormations);
            // A foreign run is refused without executing more target work.
            var foreign = Parser.Parse("Foreign(0)", options);
            Assert.False(foreign.HasErrors);
            var foreignResult = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(foreign.Root), hostOperations: operations);
            Assert.True(foreignResult.Result.IsOk);
            Assert.Equal(2, bodies);
            runRelease.TrySetResult();
            var complete = await running.WaitAsync(Wait);
            Assert.True(complete.Result.IsOk);
            Assert.True(reference.Plan.Caller.Budget.RunEnded);
            var ended = await Evaluator.InvokeCallReferenceValueAsync(reference, reference.Plan.Caller);
            Assert.Equal(Evaluator.EndedCallReferenceMessage, Assert.IsType<EvalError.IllegalInEval>(ended.Error).Reason);
            Assert.Equal(2, bodies);
        }
        finally
        {
            receiverRelease.TrySetResult();
            runRelease.TrySetResult();
            await running.WaitAsync(Wait);
        }
    }

    [Fact]
    public async Task DeferredArguments_AreNotDownloadedByViewCount_AndInvocationKeepsTheOrdinaryFailure()
    {
        const string sourcePrefix = """
            Capture(meta op) = op
            Box = { G(x) = x * 10 }
            F(0) = 0
            F(n) = {
              open 'https://modules.example/bad.kat'
              n
            }
            R = Capture(Box.G(F(1)))

            """;
        foreach (var invalidSource in new[] { false, true })
        {
            int downloads = 0;
            var options = new RunOptions
            {
                AllowedHosts = ["modules.example"],
                DownloadCode = async (_, ct) =>
                {
                    Interlocked.Increment(ref downloads);
                    await Task.Yield();
                    ct.ThrowIfCancellationRequested();
                    if (!invalidSource) throw new HttpRequestException("module admission failure");
                    return "public Broken(x) = ]";
                },
            };
            var inert = await KatLangEngine.RunAsync(sourcePrefix + "R.Arguments.count", options);
            Assert.True(inert.IsSuccess, inert.ToDisplayString());
            Assert.Equal("1", InvocationRouteCorpus.Value(Assert.IsType<RunResult.Success>(inert).Value));
            Assert.Equal(0, downloads);
            var failure = await KatLangEngine.RunAsync(sourcePrefix + "R.Invoke()", options);
            Assert.True(failure.IsFailure, failure.ToString());
            Assert.Equal(1, downloads);
            var ordinary = await KatLangEngine.RunAsync(sourcePrefix + "Box.G(F(1))", options);
            Assert.True(ordinary.IsFailure, ordinary.ToString());
            Assert.Equal(2, downloads);
            Assert.Equal(failure.GetType(), ordinary.GetType());
            var failureCodes = failure is RunResult.ParseFailure pf ? pf.Errors.Select(e => e.Code).ToArray()
                : Assert.IsType<RunResult.EvalFailure>(failure).Errors.Select(e => e.Code).ToArray();
            var ordinaryCodes = ordinary is RunResult.ParseFailure opf ? opf.Errors.Select(e => e.Code).ToArray()
                : Assert.IsType<RunResult.EvalFailure>(ordinary).Errors.Select(e => e.Code).ToArray();
            Assert.Equal(failureCodes, ordinaryCodes);
        }
    }

    // ── Receiver-checkpoint parity (research review § O.1) ───────────────────────────────────────────────

    [Theory]
    [InlineData("Use(p) = Id(p.Algorithm(trace(1)))\nUse(5)", "err TypeMismatch", 6, 1)]
    [InlineData("Use(p) = Id((p.Algorithm)(trace(1)))\nUse(5)", "err TypeMismatch", 6, 1)]
    [InlineData("Use(p) = Id(p.Algorithm(trace(1)))\nUse(min([]))", "err IllegalInEval", 8, 2)]
    [InlineData("Use(p) = Id(p.Algorithm(trace(1)))\nUse({ min([]) })", "err IllegalInEval", 8, 1)]
    [InlineData("Use(p) = Id(p.Algorithm(trace(1)))\nUse(if(aflag(), 5, 0))", "err TypeMismatch", 0, 3)]
    public async Task AParameterReceiver_KeepsItsOrdinaryRead_ThroughAPlannedInvocation(string source, string outcome, long checkpoints, long plannedPlans)
    {
        // Id's supplied p.Algorithm(...) forms one plan; the receiver fails before trace(1) is supplied.
        // Use(min([])) adds the supplied min call, while a brace argument adds none.
        // Use(if(...)) adds the supplied if call and its supplied aflag() call.
        foreach (var mode in new[] { 0, 1, 2 })
        {
            var ordinary = await InvocationRouteCorpus.Observe(new("parameter-receiver-ordinary", source, Plain: true), mode);
            var planned = await InvocationRouteCorpus.Observe(new("parameter-receiver-planned", source), mode);
            Assert.Equal(InvocationRouteExpectations.PlainVariantPlans(plannedPlans), ordinary.Plans);
            Assert.Equal(plannedPlans, planned.Plans);
            Assert.StartsWith(outcome, ordinary.Outcome, StringComparison.Ordinal);
            Assert.Equal("", ordinary.Trace);
            if (checkpoints > 0) Assert.Equal(checkpoints, ordinary.Checkpoints);
            Assert.Equal(ordinary.Semantic, planned.Semantic);
            if (mode == 2 && source.Contains("aflag()", StringComparison.Ordinal))
            {
                Assert.True(ordinary.Suspensions > 0);
                Assert.True(planned.Suspensions > 0);
            }
        }
    }

    [Theory]
    [InlineData("EQ23", 6)]
    [InlineData("EQ25", 4)]
    public async Task APlannedAlgorithmRoute_ChargesTheOrdinaryReceiverCheckpoints(string pair, long checkpoints)
    {
        foreach (var mode in new[] { 0, 1, 2 })
        {
            var ordinary = await InvocationRouteCorpus.Observe(InvocationRouteCorpus.ById(pair + "p"), mode);
            var planned = await InvocationRouteCorpus.Observe(InvocationRouteCorpus.ById(pair + "m"), mode);
            Assert.Equal(InvocationRouteExpectations.RetentionOf(InvocationRouteCorpus.ById(pair + "p")).Plans, ordinary.Plans);
            Assert.Equal(InvocationRouteExpectations.Retention[pair + "m"].Plans, planned.Plans);
            Assert.Equal(checkpoints, ordinary.Checkpoints);
            Assert.Equal(ordinary.Semantic, planned.Semantic);
        }
    }

    // ── Production refinements: no route object for named plans ─────────────────────────────────────────

    [Fact]
    public void NameParameterAndPathCalls_TakeTheCallRouteFromTheirSource_WithoutARouteObject()
    {
        var plans = new List<Evaluator.InvocationPlan>();
        var operations = HostOperations.Create(
            HostOperation.Create("Meta", (_, _) => throw new InvalidOperationException("ordinary Meta reached"), "a", "b", "c", "d"));
        var seam = new InvocationPlanTestSeam(new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>
        {
            ["Meta"] = cells =>
            {
                foreach (var cell in cells)
                {
                    var plan = Assert.IsType<Evaluator.InvocationPlan>(cell!.Suspension);
                    Assert.True(cell.Demand().IsOk);
                    Assert.True(plan.Reference.Invoke().IsOk);
                    plans.Add(plan);
                }
                return new Result.Atom(0);
            },
        });
        var parsed = Parser.Parse("""
            Inc(x) = x + 1
            Box = { G(x) = x * 10 }
            Use(f) = Meta(Inc(1), f(2), (Box.G)(3), Box.G(4))
            Use(Inc)
            """, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors);
        using var activation = InvocationPlanTestSeam.Activate(seam);
        var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), hostOperations: operations);
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        Assert.Equal(4, plans.Count);
        // `Inc(1)`, `f(2)` and `(Box.G)(3)` need no route state at all; the member edge `Box.G(4)` retains one.
        Assert.All(plans.Take(3), plan => { Assert.False(plan.NeedsRoute); Assert.Null(plan.RouteState); });
        var member = Assert.IsType<Evaluator.PlanRoute>(plans[3].RouteState);
        Assert.Equal(Evaluator.PlanRouteKind.Member, member.Kind);
    }
}
