using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// THE RUN-RESULT EXPORT (SEC-01-FU2, October 2026): the final call-reference scan of a run's output and
/// named top-level property (<c>Evaluator.ExportRunValue</c>). A reference is built only from an invocation
/// plan, and only a run that RETAINS plans (the J7 gate or a test seam) allocates one, so a run that retains
/// none exports its result with no traversal; every retaining run keeps the full scan. The scan charges no
/// step or structural work (it runs once, after evaluation) and observes cancellation every block of
/// inspected slots. Pinned here: the skip and its conservative fallback, deep/view/property refusals, test
/// seams, deferred regions, deterministic cancellation, shared DAGs, depth-sized continuation storage, the
/// unchanged accounting, sync/async/strategy/public-entry parity, and the bounded shallow probe (SEC-01-FU3). The scan counters are passive
/// <see cref="ValueTraversalObservations"/>; production runs carry none.
/// </summary>
public class CallReferenceRunExportTests
{
    private const string Prelude = """
        Square(x) = x * x
        Capture(meta operation) = operation
        Add(a, b) = a + b
        Wrap(x) = [x]
        """;

    private static Expr Program(string source, HostOperations? operations = null)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    private static string Describe(EvalResult<Evaluator.CountedResult> result)
    {
        if (result.IsOk)
            return "ok " + SemanticExplorerHarness.Neutral(result.Value.Value);
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error is EvalError.TypeMismatch mismatch ? "err TypeMismatch: " + mismatch.Message : "err " + error.GetType().Name;
    }

    private sealed record Observation(string Outcome, EvaluationBudget Budget, ValueTraversalObservations Scan);

    private static Observation Sync(string source, bool optimized, EvaluationLimits? limits = null)
    {
        var scan = new ValueTraversalObservations();
        var (result, budget) = Evaluator.RunCountedObserved(Program(source), limits, enableOptimizations: optimized,
            observations: new EvaluationObservations { StructuralTraversal = scan });
        return new Observation(Describe(result), budget, scan);
    }

    private static Observation AsyncTwin(string source)
    {
        var scan = new ValueTraversalObservations();
        var (result, budget) = Evaluator.RunCountedObservedAsync(Program(source),
            zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
            observations: new EvaluationObservations { StructuralTraversal = scan }).AsTask().GetAwaiter().GetResult();
        return new Observation(Describe(result), budget, scan);
    }

    /// <summary>
    /// The outcome of <paramref name="source"/> on the generic and optimized synchronous routes and the
    /// forced async twin, which must agree in outcome and in every export-scan counter; returns the
    /// optimized observation.
    /// </summary>
    private static Observation Observe(string source)
    {
        var optimized = Sync(source, optimized: true);
        foreach (var (route, other) in new[]
        {
            ("generic", Sync(source, optimized: false)),
            ("async twin", AsyncTwin(source)),
        })
        {
            Assert.True(optimized.Outcome == other.Outcome, $"{route}: {other.Outcome} vs optimized {optimized.Outcome}");
            Assert.Equal(optimized.Scan.RunExportScanCount, other.Scan.RunExportScanCount);
            Assert.Equal(optimized.Scan.RunExportScanSkippedCount, other.Scan.RunExportScanSkippedCount);
            Assert.Equal(optimized.Scan.RunExportScanSlots, other.Scan.RunExportScanSlots);
            Assert.Equal(optimized.Scan.RunExportScanPeakPendingFrames, other.Scan.RunExportScanPeakPendingFrames);
            Assert.Equal(optimized.Scan.RunExportScanMemoRegistrations, other.Scan.RunExportScanMemoRegistrations);
            Assert.Equal(optimized.Scan.RunExportScanProbedStructures, other.Scan.RunExportScanProbedStructures);
        }

        return optimized;
    }

    private static readonly string Escapes = "err TypeMismatch: " + Evaluator.CallReferenceLeavesRunMessage;

    /// <summary>A retaining export context over a fresh budget (the run boundary as the run root calls it).</summary>
    private static Evaluator.EvalCtx ExportCtx(
        ValueTraversalObservations scan,
        CancellationToken cancellationToken = default)
    {
        var budget = EvaluationBudget.Create(null, hostOperations: null, randomSeed: null, cancellationToken);
        budget.DecideInvocationPlanRetention(programMayCapture: true);
        return Evaluator.EvalCtx.Empty with
        {
            Budget = budget,
            Services = Evaluator.RunServices.Unconfigured with { Observations = new EvaluationObservations { StructuralTraversal = scan } },
        };
    }

    private static Result Num(int value) => new Result.Atom(value);

    /// <summary>A real run's reference, captured through the internal META receiver seam.</summary>
    private static Result.CallReference CaptureFromRun()
    {
        Result.CallReference? captured = null;
        var operations = HostOperations.Create(
            HostOperation.Create("Grab", (_, _) => throw new InvalidOperationException("receiver missing"), "operation"));
        var seam = new InvocationPlanTestSeam(new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>
        {
            ["Grab"] = cells =>
            {
                captured = Evaluator.ReifyMeta(cells[0]).Value;
                return Num(0);
            },
        });
        using (InvocationPlanTestSeam.Activate(seam))
        {
            var (result, _) = Evaluator.RunCountedObserved(Program("Sq(x) = x * x\nGrab(Sq(5))", operations),
                hostOperations: operations);
            Assert.True(result.IsOk);
        }

        return Assert.IsType<Result.CallReference>(captured);
    }

    // ── T1: a run that retains no plans skips the scan ──────────────────────

    [Fact]
    public void AReferenceFreeRun_SkipsTheExportScan()
    {
        var observed = Observe("F(x) = [x, x + 1]\nG = range(1, 5000)\nF(1), count(G), G");

        Assert.Equal("ok S[L[1, 2], 5000, L[" + string.Join(", ", Enumerable.Range(1, 5000)) + "]]", observed.Outcome);
        Assert.Equal(ForcedInvocationPlansHook.Forced, observed.Budget.RetainsInvocationPlans);
        if (ForcedInvocationPlansHook.Forced)
            return; // the forced whole-suite plan mode retains plans, so the scan (correctly) runs
        Assert.Equal(0, observed.Scan.RunExportScanCount);
        Assert.Equal(1, observed.Scan.RunExportScanSkippedCount);
        Assert.Equal(0, observed.Scan.RunExportScanSlots);
    }

    [Fact]
    public void AReferenceFreeRun_ExportsTheSameValueObject()
    {
        var value = new Result.ListValue([Num(1), new Result.ListValue([Num(2)])]);
        var budget = EvaluationBudget.Create(null);
        budget.DecideInvocationPlanRetention(programMayCapture: false);
        var scan = new ValueTraversalObservations();
        var ctx = Evaluator.EvalCtx.Empty with { Budget = budget, Services = Evaluator.RunServices.Unconfigured with { Observations = new EvaluationObservations { StructuralTraversal = scan } } };

        var exported = Evaluator.ExportRunValue(EvalResult<Result>.Ok(value), ctx);

        Assert.Same(value, exported.Value);
        Assert.Equal(budget.RetainsInvocationPlans ? 1 : 0, scan.RunExportScanCount);
    }

    // ── T2: META-capable programs keep the scan ─────────────────────────────

    [Fact]
    public void AMetaCapableRun_ScansAnOrdinaryResult_AndPassesIt()
    {
        var observed = Observe(Prelude + "\nR = Capture(Square(5))\nR.Invoke(), [1, [2, 3]]");

        Assert.Equal("ok S[25, L[1, L[2, 3]]]", observed.Outcome);
        Assert.True(observed.Budget.RetainsInvocationPlans);
        Assert.Equal(1, observed.Scan.RunExportScanCount);
        Assert.Equal(0, observed.Scan.RunExportScanSkippedCount);
        // 2 root rows, 2 list slots, 2 nested slots, and the probe's stopping structural read.
        Assert.Equal(7, observed.Scan.RunExportScanSlots);
    }

    [Fact]
    public void AMetaCapableRun_RefusesAnEscapingReference()
    {
        var observed = Observe(Prelude + "\nR = Capture(Square(5))\n[1, R]");

        Assert.Equal(Escapes, observed.Outcome);
        Assert.Equal(1, observed.Scan.RunExportScanCount);
    }

    [Fact]
    public void AMetaBuiltinOnlyRun_IsMetaCapable_AndScans()
    {
        var observed = Observe("Inc(x) = x + 1\nInc(0).repeat(3)");

        Assert.Equal("ok 3", observed.Outcome);
        Assert.True(observed.Budget.RetainsInvocationPlans);
        Assert.Equal(1, observed.Scan.RunExportScanCount);
    }

    // ── T3: a deeply nested reference ───────────────────────────────────────

    [Fact]
    public void ADeeplyNestedReference_IsRefused_WithDepthSizedStorage()
    {
        var observed = Observe(Prelude + "\nR = Capture(Square(5))\nWrap(R).repeat(300)");

        Assert.Equal(Escapes, observed.Outcome);
        // The innermost [R] is probed in place (SEC-01-FU3), so 298 enclosing lists stay suspended.
        Assert.Equal(298, observed.Scan.RunExportScanPeakPendingFrames);
        Assert.Equal(300 + 298, observed.Scan.RunExportScanSlots); // plus each failed probe's structural read
    }

    [Fact]
    public void ADeepReferenceFreeResult_OfAMetaCapableRun_Passes()
    {
        var observed = Observe(Prelude + "\nWrap(7).repeat(300)");

        Assert.StartsWith("ok L[L[L[", observed.Outcome, StringComparison.Ordinal);
        Assert.Equal(298, observed.Scan.RunExportScanPeakPendingFrames); // the innermost [7] is probed
    }

    [Theory]
    [InlineData("1, [2, [3, (4, [R])]]")]
    [InlineData("[[[[[[[[[[R]]]]]]]]]]")]
    [InlineData("[1, 2, 3], [[4], [5, [R, 6]]]")]
    public void AReferenceAfterOrdinaryItems_IsStillRefused(string rows)
        => Assert.Equal(Escapes, Observe(Prelude + "\nR = Capture(Square(5))\n" + rows).Outcome);

    // ── T4: argument views ──────────────────────────────────────────────────

    [Theory]
    [InlineData("R.Arguments")]
    [InlineData("1, [[R.Arguments]]")]
    [InlineData("[R.Arguments, 2]")]
    public void AnArgumentView_NeverEscapes(string rows)
        => Assert.Equal(Escapes, Observe(Prelude + "\nR = Capture(Add(1, 2))\n" + rows).Outcome);

    [Fact]
    public void AValueReadFromAnArgumentView_IsExported()
        => Assert.Equal("ok S[2, 1, 2]", Observe(Prelude + "\nR = Capture(Add(1, 2))\ncount(R.Arguments), R.Arguments[0], R.Arguments[1]").Outcome);

    // ── T5: the named top-level property is a second export ────────────────

    [Theory]
    [InlineData("P = [R]\nR.Invoke()", false)]
    [InlineData("P = R.Invoke()\n[1, R]", false)]
    [InlineData("P = [[R.Arguments]]\n1", false)]
    [InlineData("P = R.Invoke()\nR.Invoke() + 1", true)]
    public async Task TheOutputAndTheNamedProperty_AreBothProtected(string rows, bool succeeds)
    {
        var source = Prelude + "\nR = Capture(Square(5))\n" + rows;
        var sync = Evaluator.RunCountedWithTopLevelProperty(Program(source), "P", new RunScopedZeroArgPropertyResultCache());
        var asynchronous = await Evaluator.RunCountedWithTopLevelPropertyAsync(Program(source), "P", new RunScopedAsyncZeroArgPropertyResultCache());

        foreach (var result in new[] { sync, asynchronous })
        {
            Assert.Equal(succeeds, result.IsOk);
            if (succeeds)
            {
                Assert.Equal(Num(26), result.Value.Output.Value);
                Assert.Equal(Num(25), result.Value.TopLevelProperty!.Value.Value);
            }
            else
            {
                var error = result.Error;
                while (error is EvalError.WithContext context)
                    error = context.Inner;
                Assert.Equal(Evaluator.CallReferenceLeavesRunMessage, Assert.IsType<EvalError.TypeMismatch>(error).Message);
            }
        }
    }

    [Fact]
    public void APublicRun_RefusesAReferenceInTheDisplayDecimalsProperty()
    {
        var run = KatLangEngine.Run(Prelude + "\nR = Capture(Square(5))\nDisplayDecimals = [R]\n1");
        var failure = Assert.IsType<RunResult.EvalFailure>(run);
        Assert.Equal(KatLangErrorCode.TypeMismatch, failure.Errors[0].Code);
    }

    [Fact]
    public void AReferenceFreeRun_SkipsBothExports()
    {
        var scan = new ValueTraversalObservations();
        var budget = EvaluationBudget.Create(null);
        budget.DecideInvocationPlanRetention(programMayCapture: false);
        var ctx = Evaluator.EvalCtx.Empty with { Budget = budget, Services = Evaluator.RunServices.Unconfigured with { Observations = new EvaluationObservations { StructuralTraversal = scan } } };
        var value = new Evaluator.CountedResult(new Result.ListValue([Num(1)]), 1);

        var exported = Evaluator.ExportRunValue(
            EvalResult<Evaluator.CountedRootProgramResult>.Ok(new Evaluator.CountedRootProgramResult(value, value)), ctx);

        Assert.True(exported.IsOk);
        if (budget.RetainsInvocationPlans)
            return; // forced whole-suite plan mode
        Assert.Equal(2, scan.RunExportScanSkippedCount);
        Assert.Equal(0, scan.RunExportScanCount);
    }

    [Fact]
    public void ARetainingRun_ScansBothExports_AndRefusesAPropertyReference()
    {
        var reference = CaptureFromRun();
        var scan = new ValueTraversalObservations();
        var ctx = ExportCtx(scan);
        var output = new Evaluator.CountedResult(Num(1), 1);
        var property = new Evaluator.CountedResult(new Result.ListValue([Num(2), new Result.ListValue([reference])]), 1);

        var exported = Evaluator.ExportRunValue(
            EvalResult<Evaluator.CountedRootProgramResult>.Ok(new Evaluator.CountedRootProgramResult(output, property)), ctx);

        Assert.Equal(Evaluator.CallReferenceLeavesRunMessage, Assert.IsType<EvalError.TypeMismatch>(exported.Error).Message);
        Assert.Equal(2, scan.RunExportScanCount);
    }

    // ── T6: a test seam always retains, so it always scans ──────────────────

    [Fact]
    public void ATestSeamRun_OfAMetaFreeProgram_StillScans()
    {
        using (InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam()))
        {
            var scan = new ValueTraversalObservations();
            var (result, budget) = Evaluator.RunCountedObserved(Program("F(x) = [x]\nF(F(1))"),
                observations: new EvaluationObservations { StructuralTraversal = scan });

            Assert.Equal("ok L[L[1]]", Describe(result));
            Assert.True(budget.RetainsInvocationPlans);
            Assert.Equal(1, scan.RunExportScanCount);
            Assert.Equal(0, scan.RunExportScanSkippedCount);
        }
    }

    // ── T7: a deferred module region keeps the scan ─────────────────────────

    [Fact]
    public async Task ADeferredModulesReference_IsRefusedAtTheRunBoundary()
    {
        var options = new RunOptions
        {
            DownloadCode = (_, _) => ValueTask.FromResult("public Capture(meta op) = op"),
        };
        const string source = """
            Sq(x) = x * x
            F(0) = 0
            F(v) = {
                open 'https://katlang.org/fu2/deferred-capture.kat'
                [1, Capture(v)]
            }
            F(Sq(5))
            """;

        var run = await KatLangEngine.RunAsync(source, options);
        var failure = Assert.IsType<RunResult.EvalFailure>(run);
        Assert.Equal(KatLangErrorCode.TypeMismatch, failure.Errors[0].Code);

        var parsed = await Parser.ParseAsync(source, options);
        Assert.False(parsed.HasErrors);
        var scan = new ValueTraversalObservations();
        var (result, budget) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root),
            observations: new EvaluationObservations { StructuralTraversal = scan });
        Assert.Equal(Escapes, Describe(result));
        Assert.True(budget.RetainsInvocationPlans);
        Assert.Equal(1, scan.RunExportScanCount);
    }

    // ── T8: deterministic cancellation inside a large export scan ──────────

    [Fact]
    public void Cancellation_DuringALargeExportScan_ThrowsTheRunToken()
    {
        using var cts = new CancellationTokenSource();
        var scan = new ValueTraversalObservations
        {
            BeforeRunExportCancellationCheckpoint = ordinal => { if (ordinal == 3) cts.Cancel(); },
        };
        var ctx = ExportCtx(scan, cts.Token);
        var rows = Enumerable.Range(0, 100).Select(_ => (Result)new Result.ListValue(Enumerable.Range(1, 100).Select(Num))).ToArray();
        var value = new Result.ListValue(rows);

        var thrown = Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.ExportRunValue(EvalResult<Result>.Ok(value), ctx));

        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.Equal(3, scan.RunExportScanCancellationCheckpoints);
        Assert.True(scan.RunExportScanSlots < 100 * 101, "the scan stopped at the checkpoint, not at the end");
        Assert.Equal(0, ctx.Budget.ConsumedStructuralWorkUnits);
    }

    [Fact]
    public void Cancellation_DuringARunsExportScan_IsNeverALanguageError()
    {
        using var cts = new CancellationTokenSource();
        var scan = new ValueTraversalObservations
        {
            BeforeRunExportCancellationCheckpoint = ordinal => { if (ordinal == 1) cts.Cancel(); },
        };

        var thrown = Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(
            Program("Inc(x) = x + 1\nInc(0).repeat(1), range(1, 3000)"),
            observations: new EvaluationObservations { StructuralTraversal = scan },
            cancellationToken: cts.Token));

        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.Equal(1, scan.RunExportScanCancellationCheckpoints);
    }

    [Fact]
    public void AnUncancelledLargeExportScan_ReachesItsCheckpoints_AndCompletes()
    {
        var scan = new ValueTraversalObservations();
        var ctx = ExportCtx(scan);
        var value = new Result.ListValue(Enumerable.Range(0, 100).Select(_ => (Result)new Result.ListValue(Enumerable.Range(1, 100).Select(Num))));

        Assert.True(Evaluator.ExportRunValue(EvalResult<Result>.Ok(value), ctx).IsOk);
        Assert.Equal(100 + 100 * 100, scan.RunExportScanSlots);
        // A checkpoint follows every scan segment that completes a block of 256 slots (a segment adds ≤ 101).
        Assert.InRange(scan.RunExportScanCancellationCheckpoints, 100 * 101 / (256 + 101), 100 * 101 / 256);
    }

    // ── T9 / T10: shared DAGs, wide and deep structures ─────────────────────

    [Fact]
    public void ASharedDag_IsScannedOncePerDistinctNode()
    {
        var node = new Result.ListValue([Num(1), Num(1)]);
        for (var i = 0; i < 40; i++)
            node = new Result.ListValue([node, node]); // 41 nodes, 2^41 leaf paths
        var scan = new ValueTraversalObservations();

        Assert.True(Evaluator.ExportRunValue(EvalResult<Result>.Ok(node), ExportCtx(scan)).IsOk);
        // 40 memoized nodes of 2 slots each; the shallow leaf-only base [1, 1] is probed in place
        // (SEC-01-FU3) at each of its 2 references. Every incoming edge to the other 39 nested nodes
        // also probes their first structural slot before either a frame resumes there or the memo hits.
        Assert.Equal(2 * 40 + 2 * 2 + 2 * 39, scan.RunExportScanSlots);
        Assert.Equal(39, scan.RunExportScanMemoRegistrations);
        Assert.Equal(2, scan.RunExportScanProbedStructures);
        Assert.Equal(39, scan.RunExportScanPeakPendingFrames);
    }

    [Fact]
    public void AWideStructure_KeepsOneContinuationFrame()
    {
        // Each child holds a structure, so it is memoized and entered as a frame (its inner [i] is probed).
        var value = new Result.ListValue(Enumerable.Range(0, 10_000).Select(i => (Result)new Result.ListValue([Num(i), new Result.ListValue([Num(i)])])));
        var scan = new ValueTraversalObservations();

        Assert.True(Evaluator.ExportRunValue(EvalResult<Result>.Ok(value), ExportCtx(scan)).IsOk);
        Assert.Equal(1, scan.RunExportScanPeakPendingFrames);
        Assert.Equal(50_000, scan.RunExportScanSlots); // includes the 10,000 stopping structural reads
        Assert.Equal(10_000, scan.RunExportScanMemoRegistrations);
    }

    [Fact]
    public void ADeepStructure_IsStackSafe_AndKeepsDepthFrames()
    {
        const int depth = 15_000;
        var reference = CaptureFromRun();
        Result value = reference;
        for (var i = 0; i < depth; i++)
            value = new Result.SequenceValue([Num(i), value]);
        var scan = new ValueTraversalObservations();

        var exported = Evaluator.ExportRunValue(EvalResult<Result>.Ok(value), ExportCtx(scan));

        Assert.Equal(Evaluator.CallReferenceLeavesRunMessage, Assert.IsType<EvalError.TypeMismatch>(exported.Error).Message);
        // The innermost (i, R) is probed in place (SEC-01-FU3); every enclosing level is a frame.
        Assert.Equal(depth - 2, scan.RunExportScanPeakPendingFrames);
    }

    [Fact]
    public void AnEarlyReference_StopsTheScan_BeforeTheSuffix()
    {
        var reference = CaptureFromRun();
        var suffix = Enumerable.Range(0, 5000).Select(i => (Result)new Result.ListValue([Num(i)]));
        var value = new Result.ListValue(new Result[] { Num(0), reference }.Concat(suffix));
        var scan = new ValueTraversalObservations();

        var exported = Evaluator.ExportRunValue(EvalResult<Result>.Ok(value), ExportCtx(scan));

        Assert.True(exported.IsError);
        Assert.Equal(2, scan.RunExportScanSlots);
        Assert.Equal(0, scan.RunExportScanPeakPendingFrames);
    }

    // ── T11: the export charges nothing ─────────────────────────────────────

    [Fact]
    public void TheExportScan_ChargesNoStepOrStructuralWork()
    {
        var scan = new ValueTraversalObservations();
        var ctx = ExportCtx(scan);
        var value = new Result.ListValue(Enumerable.Range(0, 300).Select(i => (Result)new Result.ListValue([Num(i), Num(i)])));

        Assert.True(Evaluator.ExportRunValue(EvalResult<Result>.Ok(value), ctx).IsOk);
        Assert.Equal(0, ctx.Budget.ConsumedSteps);
        Assert.Equal(0, ctx.Budget.ConsumedStructuralWorkUnits);
        Assert.Equal(0, scan.StructuralWorkChargeCount);
        Assert.Equal(900, scan.RunExportScanSlots);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void AMetaCapableRun_SucceedsAtExactlyItsEvaluationSteps(bool metaCapable)
    {
        var source = (metaCapable ? Prelude + "\nR = Capture(Square(5))\nR.Invoke(), " : "Inc(x) = x + 1\nInc(Inc(1)), ")
            + "range(1, 2000), [[1, 2], [3]]";
        var baseline = Sync(source, optimized: true);
        Assert.StartsWith("ok ", baseline.Outcome, StringComparison.Ordinal);
        Assert.True(baseline.Budget.ConsumedSteps > 0);
        Assert.Equal(0, baseline.Budget.ConsumedStructuralWorkUnits);

        var exact = Sync(source, optimized: true, new EvaluationLimits { MaxSteps = baseline.Budget.ConsumedSteps });

        Assert.Equal(baseline.Outcome, exact.Outcome);
        Assert.Equal(baseline.Budget.ConsumedSteps, exact.Budget.ConsumedSteps);
        Assert.Equal(0, exact.Budget.ConsumedStructuralWorkUnits);
        Assert.Equal(metaCapable || ForcedInvocationPlansHook.Forced ? 1 : 0, exact.Scan.RunExportScanCount);
    }

    // ── T12: genuine asynchronous host suspension and the public entries ───

    [Theory]
    [InlineData("[Later(1), R]", false)]
    [InlineData("[Later(1), [R.Arguments]]", false)]
    [InlineData("[Later(1), [2, R]]", false)]
    [InlineData("[Later(1), (2, R.Arguments)]", false)]
    [InlineData("[Later(1), R.Invoke()]", true)]
    public async Task AGenuinelySuspendingRun_KeepsTheBoundary(string rows, bool succeeds)
    {
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.CreateAsync("Later", async (args, token) =>
            {
                entered.TrySetResult();
                await release.Task.WaitAsync(token);
                return args[0];
            }, "x")),
        };
        var pending = KatLangEngine.RunAsync(Prelude + "\nR = Capture(Square(5))\n" + rows, options);
        try
        {
            await entered.Task.WaitAsync(TimeSpan.FromSeconds(10));
            Assert.False(pending.IsCompleted);
        }
        finally
        {
            release.TrySetResult();
        }
        var run = await pending;

        if (succeeds)
            Assert.Equal("L[1, 25]", SemanticExplorerHarness.Neutral(Assert.IsType<RunResult.Success>(run).Value));
        else
            Assert.Equal(KatLangErrorCode.TypeMismatch, Assert.IsType<RunResult.EvalFailure>(run).Errors[0].Code);
    }

    [Fact]
    public async Task PublicEvaluatorEntries_ExportReferenceFreeAndRefuseEscapingResults()
    {
        var operations = HostOperations.Create(HostOperation.Create("Id", (args, _) => args[0], "x"));
        var free = Program("F(x) = [x, Id(x)]\nF(2)", operations);
        var escaping = Program(Prelude + "\nR = Capture(Square(5))\n[Id(1), [R]]", operations);

        Assert.Equal("L[2, 2]", SemanticExplorerHarness.Neutral(Evaluator.Run(free, operations, null, null, CancellationToken.None).Value));
        Assert.Equal("L[2, 2]", SemanticExplorerHarness.Neutral((await Evaluator.RunAsync(free, operations, null, null, CancellationToken.None)).Value));
        Assert.IsType<EvalError.TypeMismatch>(Evaluator.Run(escaping, operations, null, null, CancellationToken.None).Error);
        Assert.IsType<EvalError.TypeMismatch>(Evaluator.RunFlat(escaping, operations, null, null, CancellationToken.None).Error);
        Assert.IsType<EvalError.TypeMismatch>((await Evaluator.RunAsync(escaping, operations, null, null, CancellationToken.None)).Error);
        Assert.IsType<RunResult.Success>(KatLangEngine.Run("F(x) = [x, x]\nF(2)"));
    }

    // ── T13: the bounded shallow probe (SEC-01-FU3) ─────────────────────────

    private const int K = Evaluator.ShallowProbeMaxItems;

    private static Result.ListValue Pairs(int count, int offset = 0)
        => new(Enumerable.Range(offset, count).Select(i => (Result)new Result.ListValue([Num(i), Num(i + 1)])));

    private static Result Leaves(int width, int start = 0)
        => new Result.ListValue(Enumerable.Range(start, width).Select(Num));

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DistinctShallowPairs_AreProbedInPlace_WithNoMemoOrFrames(bool sequences)
    {
        var value = new Result.ListValue(Enumerable.Range(0, 5000).Select(i => sequences
            ? (Result)new Result.SequenceValue([Num(i), Num(i + 1)])
            : new Result.ListValue([Num(i), Num(i + 1)])));
        var scan = new ValueTraversalObservations();

        Assert.True(Evaluator.ExportRunValue(EvalResult<Result>.Ok(value), ExportCtx(scan)).IsOk);
        Assert.Equal(5000 * 3, scan.RunExportScanSlots);
        Assert.Equal(5000, scan.RunExportScanProbedStructures);
        Assert.Equal(0, scan.RunExportScanMemoRegistrations);
        Assert.Equal(0, scan.RunExportScanPeakPendingFrames);
        Assert.False(Evaluator.ContainsCallReference(value));
    }

    [Theory]
    [InlineData(2)]
    [InlineData(K - 1)]
    [InlineData(K)]
    [InlineData(K + 1)]
    [InlineData(100)]
    public void RepeatedLeafOnlyStructures_CostAFixedBoundPerReference_OrStayMemoized(int width)
    {
        const int references = 1000;
        var shared = Leaves(width);
        var value = new Result.ListValue(Enumerable.Repeat(shared, references));
        var scan = new ValueTraversalObservations();

        Assert.True(Evaluator.ExportRunValue(EvalResult<Result>.Ok(value), ExportCtx(scan)).IsOk);
        if (width <= K)
        {
            // Never memoized: each reference re-inspects at most K slots.
            Assert.Equal(references + references * width, scan.RunExportScanSlots);
            Assert.Equal(references, scan.RunExportScanProbedStructures);
            Assert.Equal(0, scan.RunExportScanMemoRegistrations);
        }
        else
        {
            // A wider leaf-only structure is expanded once and memoized for every later reference.
            Assert.Equal(references + width, scan.RunExportScanSlots);
            Assert.Equal(0, scan.RunExportScanProbedStructures);
            Assert.Equal(1, scan.RunExportScanMemoRegistrations);
        }
    }

    public static TheoryData<int, int, string> BoundaryCases()
    {
        var cases = new TheoryData<int, int, string>();
        foreach (var width in new[] { K - 1, K, K + 1 })
        {
            foreach (var position in new[] { 0, width / 2, width - 1 })
            {
                foreach (var kind in new[] { "reference", "view", "nested", "clean-nested" })
                    cases.Add(width, position, kind);
            }
        }

        return cases;
    }

    [Theory]
    [MemberData(nameof(BoundaryCases))]
    public void TheProbeBoundary_KeepsDepthFirstOrder_AndStopsBeforeTheSuffix(int width, int position, string kind)
    {
        var reference = CaptureFromRun();
        var items = Enumerable.Range(0, width).Select(Num).ToArray();
        items[position] = kind switch
        {
            "reference" => reference,
            "view" => reference.ArgumentView,
            "nested" => new Result.SequenceValue([Num(-1), reference]),
            _ => new Result.SequenceValue([Num(-1)]),
        };
        Result nested = width % 2 == 0 ? new Result.ListValue(items) : new Result.SequenceValue(items);
        var value = new Result.ListValue(new[] { nested }.Concat(Pairs(1000).Items));
        var scan = new ValueTraversalObservations();

        var exported = Evaluator.ExportRunValue(EvalResult<Result>.Ok(value), ExportCtx(scan));

        var clean = kind == "clean-nested";
        Assert.Equal(clean, exported.IsOk);
        Assert.Equal(!clean, Evaluator.ContainsCallReference(value));
        switch (kind)
        {
            case "reference" or "view":
                // The root slot, then the nested prefix through the leaf reference; never the suffix.
                Assert.Equal(1 + position + 1, scan.RunExportScanSlots);
                Assert.Equal(width <= K ? 0 : 1, scan.RunExportScanMemoRegistrations);
                Assert.Equal(width <= K ? 0 : 1, scan.RunExportScanPeakPendingFrames);
                break;
            case "nested":
                // The probe stops at the structural item; the frame resumes THERE (the leaf prefix is
                // inspected once), then the inner (-1, R) is probed: -1 and R. A shallow outer probe
                // also inspected the structural slot before the resumed frame reads it again.
                Assert.Equal(1 + position + 1 + 2 + (width <= K ? 1 : 0), scan.RunExportScanSlots);
                Assert.Equal(1, scan.RunExportScanMemoRegistrations);
                Assert.Equal(1, scan.RunExportScanPeakPendingFrames);
                break;
            default:
                // The nested slots, its inner (-1), every pair, and the shallow outer probe's stopping read.
                Assert.Equal(1 + width + 1 + 1000 * 3 + (width <= K ? 1 : 0), scan.RunExportScanSlots);
                Assert.Equal(1, scan.RunExportScanMemoRegistrations);
                Assert.Equal(1000 + 1, scan.RunExportScanProbedStructures);
                break;
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AMixedSharedDag_StaysMemoized_WithDepthFrames(bool referenceAtTheBase)
    {
        const int depth = 20; // 2^20 paths: an unmemoized walk would be observed, not hang
        Result node = new Result.ListValue([Num(1), referenceAtTheBase ? CaptureFromRun() : Num(2)]);
        for (var i = 0; i < depth; i++)
            node = i % 2 == 0 ? new Result.SequenceValue([node, node]) : new Result.ListValue([node, node]);
        var scan = new ValueTraversalObservations();

        var exported = Evaluator.ExportRunValue(EvalResult<Result>.Ok(node), ExportCtx(scan));

        Assert.Equal(!referenceAtTheBase, exported.IsOk);
        Assert.Equal(depth - 1, scan.RunExportScanMemoRegistrations);
        Assert.Equal(depth - 1, scan.RunExportScanPeakPendingFrames);
        // Clean: every memoized node's 2 slots, plus the base probed at both of its references.
        // Found: the first slot of each memoized level, the root's, and the base probe through R.
        // Include each failed probe's structural read, once per incoming edge actually visited.
        Assert.Equal(referenceAtTheBase ? depth + 2 + depth - 1 : 2 * depth + 2 * 2 + 2 * (depth - 1), scan.RunExportScanSlots);
    }

    [Fact]
    public void ProbedShallowChildren_ReachCancellationCheckpoints_InsideTheirFrame()
    {
        var scan = new ValueTraversalObservations();

        Assert.True(Evaluator.ExportRunValue(EvalResult<Result>.Ok(Pairs(1000)), ExportCtx(scan)).IsOk);
        // One frame of 1000 probed pairs, 3 slots each: a checkpoint after every 86 pairs (258 slots),
        // not one unchecked 3000-slot segment.
        Assert.Equal(3000, scan.RunExportScanSlots);
        Assert.Equal(1000 / 86, scan.RunExportScanCancellationCheckpoints);
        Assert.Equal(0, scan.RunExportScanPeakPendingFrames);
    }

    [Fact]
    public void AProbe_CountsTheStructuralSlotItReadsBeforeResumingTheFrame()
    {
        var child = new Result.SequenceValue([Num(3)]);
        var value = new Result.ListValue([new Result.ListValue([Num(1), Num(2), child])]);
        var scan = new ValueTraversalObservations();

        Assert.True(Evaluator.ExportRunValue(EvalResult<Result>.Ok(value), ExportCtx(scan)).IsOk);

        // Root slot; three probe reads through child; child read again by the resumed frame;
        // then its one leaf. The stopping structural inspection is real work too.
        Assert.Equal(6, scan.RunExportScanSlots);
        Assert.Equal(1, scan.RunExportScanMemoRegistrations);
        Assert.Equal(1, scan.RunExportScanProbedStructures);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void RepeatedProbesThatFallBackToMemoHits_CheckCancellationInsideTheFrame(bool sequences)
    {
        var child = new Result.ListValue([Num(1)]);
        var slots = Enumerable.Range(0, K - 1).Select(Num).Append(child);
        Result shared = sequences ? new Result.SequenceValue(slots) : new Result.ListValue(slots);
        var repeated = Enumerable.Repeat(shared, 1000);
        Result value = sequences ? new Result.ListValue(repeated) : new Result.SequenceValue(repeated);
        using var cts = new CancellationTokenSource();
        var scan = new ValueTraversalObservations
        {
            BeforeRunExportCancellationCheckpoint = _ => cts.Cancel(),
        };
        var ctx = ExportCtx(scan, cts.Token);

        var thrown = Assert.ThrowsAny<OperationCanceledException>(
            () => Evaluator.ExportRunValue(EvalResult<Result>.Ok(value), ctx));

        Assert.Equal(cts.Token, thrown.CancellationToken);
        // A failed shallow probe still inspects its whole K-slot prefix before the memo hit.
        // Cancellation must be observed after a block, not after all 1000 repeated probes.
        Assert.InRange(scan.RunExportScanSlots,
            Result.ValueSemanticComparer.UnitsPerCharge,
            Result.ValueSemanticComparer.UnitsPerCharge + K);
        Assert.Equal(1, scan.RunExportScanCancellationCheckpoints);
        Assert.Equal(1, scan.RunExportScanMemoRegistrations);
        Assert.Equal(0, ctx.Budget.ConsumedSteps);
        Assert.Equal(0, ctx.Budget.ConsumedStructuralWorkUnits);
    }

    [Fact]
    public void Cancellation_AmongProbedShallowChildren_ThrowsTheRunToken()
    {
        using var cts = new CancellationTokenSource();
        var scan = new ValueTraversalObservations
        {
            BeforeRunExportCancellationCheckpoint = ordinal => { if (ordinal == 2) cts.Cancel(); },
        };
        var ctx = ExportCtx(scan, cts.Token);

        var thrown = Assert.ThrowsAny<OperationCanceledException>(
            () => Evaluator.ExportRunValue(EvalResult<Result>.Ok(Pairs(1000)), ctx));

        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.Equal(2 * 258, scan.RunExportScanSlots);
        Assert.Equal(0, ctx.Budget.ConsumedStructuralWorkUnits);
    }

    [Fact]
    public void TheChargedHostArgumentScan_KeepsItsMemo_AndItsUnits()
    {
        var pair = new Result.ListValue([Num(1), Num(2)]);
        var shared = new Result.ListValue(Enumerable.Repeat<Result>(pair, 5000));
        var sharedBudget = EvaluationBudget.Create(null);
        var sharedScan = new ValueTraversalObservations();
        var distinctBudget = EvaluationBudget.Create(null);

        Assert.Null(Evaluator.HostArgumentBoundaryError(shared, sharedBudget, sharedScan));
        Assert.Null(Evaluator.HostArgumentBoundaryError(Pairs(5000), distinctBudget, observations: null));

        // The shared pair is charged once (2 slots + its completion); every later reference is free.
        Assert.Equal(3, sharedBudget.ConsumedStructuralWorkUnits);
        Assert.Equal(1, sharedScan.CallReferenceScanPeakPendingFrames);
        Assert.Equal(5000 * 3, distinctBudget.ConsumedStructuralWorkUnits);
        Assert.Equal(0, sharedScan.RunExportScanProbedStructures);
    }

    [Fact]
    public void ARetainingRun_ProbesItsShallowRows_OnEveryRoute()
    {
        const string pair = "\nPair(x) = [x, x + 1]\n";
        var observed = Observe(Prelude + pair + "R = Capture(Square(5))\nR.Invoke(), range(1, 300).map(Pair)");

        Assert.StartsWith("ok S[25, L[L[1, 2], L[2, 3], ", observed.Outcome, StringComparison.Ordinal);
        Assert.Equal(2 + 300 + 300 * 2, observed.Scan.RunExportScanSlots);
        Assert.Equal(1, observed.Scan.RunExportScanMemoRegistrations);
        Assert.Equal(300, observed.Scan.RunExportScanProbedStructures);
        Assert.Equal(1, observed.Scan.RunExportScanPeakPendingFrames);

        Assert.Equal(Escapes, Observe(Prelude + pair + "R = Capture(Square(5))\nrange(1, 300).map(Pair), [1, [2, R]]").Outcome);
        Assert.Equal(Escapes, Observe(Prelude + pair + "R = Capture(Add(1, 2))\nrange(1, 300).map(Pair), (1, R.Arguments)").Outcome);
    }

    [Fact]
    public void ExportingDistinctShallowPairs_AllocatesNoMemo()
    {
        // Allocation only (the counts above pin the mechanism): unobserved production path, warmed.
        var budget = EvaluationBudget.Create(null);
        budget.DecideInvocationPlanRetention(programMayCapture: true);
        var ctx = Evaluator.EvalCtx.Empty with { Budget = budget };
        var pairs = EvalResult<Result>.Ok(Pairs(5000));
        var flat = EvalResult<Result>.Ok(Leaves(15_000));

        long Allocated(EvalResult<Result> value)
        {
            for (var i = 0; i < 3; i++)
                Assert.True(Evaluator.ExportRunValue(value, ctx).IsOk);
            var before = GC.GetAllocatedBytesForCurrentThread();
            var exported = Evaluator.ExportRunValue(value, ctx);
            var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
            Assert.True(exported.IsOk);
            return allocated;
        }

        // The memoized walk allocated ~320 KB here; a generous margin over a flat walk of as many slots.
        Assert.InRange(Allocated(pairs), 0, Allocated(flat) + 16 * 1024);
    }
}
