using KatLang.Evaluation.Caching;

namespace KatLang.Tests.ConcurrencyReentrancy;

/// <summary>
/// Concurrency differential suite: independent KatLang evaluations must
/// produce their sequential observations regardless of concurrent execution.
///
/// <para><b>Contract under test</b> (verified at source during the audit):
/// every public/internal evaluator entry point builds a fresh root context
/// per call — fresh <c>EvaluationBudget</c> (also the cache-key run
/// identity), fresh <c>RunScopedZeroArgPropertyResultCache</c> and
/// <c>RunScopedDeconstructionBindingCache</c> (<c>Evaluator.CreateRootCtx</c>) —
/// and the only process-global mutable object in the runtime is
/// <c>Evaluator.ScopeOwnerAlgorithms</c> (a <see cref="System.Runtime.CompilerServices.ConditionalWeakTable{TKey,TValue}"/>
/// whose keys are freshly minted per wiring and published before they
/// escape). Everything else static is immutable (prelude/Math ASTs consumed
/// via <c>with</c>-copies, builtin registry, formatter tables, default
/// options).</para>
///
/// <para><b>Method.</b> Each pair case computes per-lane sequential baselines
/// (recomputed every round — sequential repeat-stability is itself an oracle
/// that kills cross-run counter/cache accumulation deterministically, before
/// any scheduling is involved), then runs both lanes on barrier-released
/// dedicated threads and requires every concurrent observation to equal its
/// own baseline. Deterministic MID-EVALUATION overlap is forced by the gated
/// facts: one run provably suspended inside a charged invocation region (the
/// <see cref="IZeroArgPropertyResultCache"/> seam) or inside a module fetch
/// (the <c>DownloadCode</c> seam) while other runs execute to completion.</para>
/// </summary>
public class ConcurrencyDifferentialTests
{
    private static readonly IReadOnlyList<ConcurrencyPairCase> Matrix = ConcurrencyCorpus.PairCases;

    private static readonly IReadOnlyDictionary<string, ConcurrencyPairCase> ById =
        Matrix.ToDictionary(c => c.Id, StringComparer.Ordinal);

    public static TheoryData<string> PairCaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var pairCase in Matrix)
            data.Add(pairCase.Id);
        return data;
    }

    public static TheoryData<string> SameAstIds()
    {
        var data = new TheoryData<string>();
        foreach (var (id, _) in ConcurrencyCorpus.SameAstPrograms)
            data.Add(id);
        return data;
    }

    // ── The pair differential ────────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(PairCaseIds))]
    public void ConcurrentLanes_EachObserveTheirSequentialBaseline(string caseId)
    {
        var pairCase = ById[caseId];

        var firstBaselineA = ObserveLane(pairCase, laneA: true);
        var firstBaselineB = ObserveLane(pairCase, laneA: false);
        AssertExpectedClass(pairCase, firstBaselineA, firstBaselineB);

        // ConcurrentFailure rounds are followed by a clean sequential sentinel:
        // concurrency + failure must leave no process-global evaluator state behind.
        var sentinelBaseline = pairCase.Scenario == ConcurrencyScenario.ConcurrentFailure
            ? ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.CleanupSentinel)
            : null;

        for (var round = 1; round <= pairCase.Rounds; round++)
        {
            // Recomputed sequential baselines double as repeat-stability: any
            // state accumulating across runs shifts these BEFORE scheduling is
            // involved, so such a defect fails deterministically.
            var baselineA = ObserveLane(pairCase, laneA: true);
            var baselineB = ObserveLane(pairCase, laneA: false);
            AssertRepeatStable(pairCase, "A", firstBaselineA, baselineA, round);
            AssertRepeatStable(pairCase, "B", firstBaselineB, baselineB, round);

            var observed = ConcurrencyHarness.RunConcurrently(
                ("A", () => ObserveLane(pairCase, laneA: true)),
                ("B", () => ObserveLane(pairCase, laneA: false)));

            if (observed[0] != baselineA || observed[1] != baselineB)
            {
                Assert.Fail(
                    $"[{pairCase.Id}] round {round}: a concurrent lane diverged from its sequential baseline.\n"
                    + ConcurrencyHarness.PairReport(
                        pairCase.Invariant,
                        "barrier-released dedicated threads, simultaneous start",
                        ("A", pairCase.ProgramA, pairCase.EntryA.ToString(), baselineA, observed[0]),
                        ("B", pairCase.ProgramB, pairCase.EntryB.ToString(), baselineB, observed[1])));
            }

            if (sentinelBaseline is not null)
            {
                var sentinel = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.CleanupSentinel);
                Assert.True(
                    sentinel == sentinelBaseline,
                    $"[{pairCase.Id}] round {round}: the clean sentinel run AFTER a concurrent-failure round "
                    + $"diverged — process-global evaluator state was polluted.\n  baseline: {sentinelBaseline}\n  observed: {sentinel}");
            }
        }
    }

    private static string ObserveLane(ConcurrencyPairCase pairCase, bool laneA)
        => laneA
            ? ConcurrencyHarness.Observe(pairCase.EntryA, pairCase.ProgramA, pairCase.LimitsA)
            : ConcurrencyHarness.Observe(pairCase.EntryB, pairCase.ProgramB, pairCase.LimitsB);

    private static void AssertExpectedClass(ConcurrencyPairCase pairCase, string baselineA, string baselineB)
    {
        if (pairCase.ExpectedClassA is { } classA)
        {
            Assert.True(
                baselineA.StartsWith(classA, StringComparison.Ordinal),
                $"[{pairCase.Id}] POWER check: lane A's baseline no longer starts with '{classA}' — the case lost its meaning.\n  baseline: {baselineA}");
        }

        if (pairCase.ExpectedClassB is { } classB)
        {
            Assert.True(
                baselineB.StartsWith(classB, StringComparison.Ordinal),
                $"[{pairCase.Id}] POWER check: lane B's baseline no longer starts with '{classB}' — the case lost its meaning.\n  baseline: {baselineB}");
        }
    }

    private static void AssertRepeatStable(
        ConcurrencyPairCase pairCase, string lane, string first, string current, int round)
        => Assert.True(
            current == first,
            $"[{pairCase.Id}] round {round}: lane {lane}'s SEQUENTIAL baseline drifted between rounds — "
            + $"state is accumulating across independent runs.\n  first:   {first}\n  current: {current}");

    // ── Absolute power anchors ───────────────────────────────────────────────

    /// <summary>
    /// A pure differential cannot see a defect that skews baseline and
    /// concurrent observation identically. These hand-derived anchors pin the
    /// sentinels' absolute counted meaning (counted-matrix rules): MultiOut
    /// emits 2+1+1+1 = 5 rows, ZeroOut emits 0, the failure sentinels fail,
    /// and the heavy loop is legal without a step budget but exceeds TinySteps.
    /// </summary>
    [Fact]
    public void PowerAnchors_SentinelBaselinesKeepTheirHandDerivedMeaning()
    {
        Assert.Contains(" n=5 ", ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.MultiOut), StringComparison.Ordinal);
        Assert.Contains(" n=0 ", ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.ZeroOut), StringComparison.Ordinal);
        Assert.StartsWith("err", ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.FailingIndex), StringComparison.Ordinal);
        Assert.StartsWith("err", ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.RecursionRunaway), StringComparison.Ordinal);
        Assert.StartsWith("err", ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.HeavyLoop, ConcurrencyCorpus.TinySteps), StringComparison.Ordinal);
        Assert.StartsWith("ok", ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.HeavyLoop), StringComparison.Ordinal);
    }

    // ── Same AST object, concurrent lanes ───────────────────────────────────

    /// <summary>
    /// The exact same parsed <see cref="Expr"/> instance evaluated by two
    /// concurrent lanes (and across two entry points) observes its baseline:
    /// evaluation wires derived structures (<c>WithParent</c>/<c>ChildOf</c>
    /// mint fresh records and scope contexts) and never mutates the input
    /// tree, so prepared-AST reuse is legal under concurrency. The tree is
    /// also re-observed sequentially AFTERWARDS — hidden mutation during the
    /// concurrent rounds would surface there even if both lanes agreed.
    /// </summary>
    [Theory]
    [MemberData(nameof(SameAstIds))]
    public void SameAstObject_EvaluatedConcurrently_ObservesItsBaseline(string id)
    {
        var program = ConcurrencyCorpus.SameAstPrograms.Single(p => p.Id == id).Program;
        var root = ConcurrencyHarness.ParseRoot(program);

        var baselineCounted = ConcurrencyHarness.ObservePrepared(EvalEntryPoint.RunCounted, root);
        var baselinePlain = ConcurrencyHarness.ObservePrepared(EvalEntryPoint.RunPlain, root);

        for (var round = 1; round <= 4; round++)
        {
            var counted = ConcurrencyHarness.RunConcurrently(
                ("A-counted", () => ConcurrencyHarness.ObservePrepared(EvalEntryPoint.RunCounted, root)),
                ("B-counted", () => ConcurrencyHarness.ObservePrepared(EvalEntryPoint.RunCounted, root)));
            Assert.True(
                counted[0] == baselineCounted && counted[1] == baselineCounted,
                $"[{id}] round {round}: concurrent RunCounted lanes over the SAME AST object diverged.\n"
                + $"  baseline: {baselineCounted}\n  lane A:   {counted[0]}\n  lane B:   {counted[1]}");

            var mixed = ConcurrencyHarness.RunConcurrently(
                ("A-plain", () => ConcurrencyHarness.ObservePrepared(EvalEntryPoint.RunPlain, root)),
                ("B-counted", () => ConcurrencyHarness.ObservePrepared(EvalEntryPoint.RunCounted, root)));
            Assert.True(
                mixed[0] == baselinePlain && mixed[1] == baselineCounted,
                $"[{id}] round {round}: cross-entry-point lanes over the SAME AST object diverged.\n"
                + $"  plain baseline:   {baselinePlain}\n  plain observed:   {mixed[0]}\n"
                + $"  counted baseline: {baselineCounted}\n  counted observed: {mixed[1]}");
        }

        Assert.Equal(baselineCounted, ConcurrencyHarness.ObservePrepared(EvalEntryPoint.RunCounted, root));
    }

    // ── Deterministic gated overlap ──────────────────────────────────────────

    /// <summary>
    /// One run provably SUSPENDED inside evaluation (inside the charged
    /// invocation region of its first zero-argument property access) while
    /// same-named/same-shaped runs execute to completion through several
    /// entry points; the suspended run then resumes to exactly its baseline.
    /// This is the deterministic form of the cache/scope isolation pairs: the
    /// interleaving is forced, not hoped for.
    /// </summary>
    [Fact]
    public void GatedRun_SuspendedInsideEvaluation_OthersCompleteAndItResumesToBaseline()
    {
        var baselineA = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.CachedPropA);
        var baselineB = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.CachedPropB);
        var baselineStructural = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.StructuralPropB);
        var baselineEngine = ConcurrencyHarness.ObserveEngine(ConcurrencyCorpus.CachedPropB);

        var rootA = ConcurrencyHarness.ParseRoot(ConcurrencyCorpus.CachedPropA);
        var gate = new EvaluationGate();
        var gatedCache = new GatedZeroArgPropertyResultCache(gate, gateAtAccess: 1);

        string? gatedObservation = null;
        Exception? gatedFailure = null;
        var gatedThread = new Thread(() =>
        {
            try
            {
                gatedObservation = ConcurrencyHarness.EncodeCounted(Evaluator.RunCounted(rootA, gatedCache));
            }
            catch (Exception ex)
            {
                gatedFailure = ex;
            }
        })
        {
            IsBackground = true,
            Name = "katlang-gated-A",
        };

        gatedThread.Start();
        try
        {
            gate.WaitUntilInside();

            // While A is suspended mid-evaluation with live run-scoped state:
            // same-named property runs, a same-shaped structural run, and a
            // full engine run all complete and observe their own baselines.
            Assert.Equal(baselineB, ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.CachedPropB));
            Assert.Equal(baselineStructural, ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.StructuralPropB));
            Assert.Equal(baselineEngine, ConcurrencyHarness.ObserveEngine(ConcurrencyCorpus.CachedPropB));
        }
        finally
        {
            gate.Release();
        }

        Assert.True(gatedThread.Join(ConcurrencyHarness.WaitBudget), "the gated run never finished after release");
        Assert.Null(gatedFailure);
        Assert.True(
            gatedObservation == baselineA,
            "The gated run resumed to a DIFFERENT observation than its sequential baseline — "
            + $"runs that completed during its suspension leaked into its run-scoped state.\n"
            + $"  baseline: {baselineA}\n  observed: {gatedObservation}");
    }

    /// <summary>
    /// BOTH runs suspended inside evaluation at the same time (each at its
    /// first same-named property access), then released together: maximal
    /// overlap of live run-scoped state, resumed concurrently.
    /// </summary>
    [Fact]
    public void BothRuns_SuspendedInsideEvaluationSimultaneously_ResumeToTheirBaselines()
    {
        var baselineA = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.CachedPropA);
        var baselineB = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.CachedPropB);

        var rootA = ConcurrencyHarness.ParseRoot(ConcurrencyCorpus.CachedPropA);
        var rootB = ConcurrencyHarness.ParseRoot(ConcurrencyCorpus.CachedPropB);
        var gateA = new EvaluationGate();
        var gateB = new EvaluationGate();

        var observations = new string?[2];
        var failures = new Exception?[2];
        var threadA = GatedLane(rootA, gateA, 0, observations, failures, "A");
        var threadB = GatedLane(rootB, gateB, 1, observations, failures, "B");

        threadA.Start();
        threadB.Start();
        try
        {
            gateA.WaitUntilInside();
            gateB.WaitUntilInside();
        }
        finally
        {
            gateA.Release();
            gateB.Release();
        }

        Assert.True(threadA.Join(ConcurrencyHarness.WaitBudget) && threadB.Join(ConcurrencyHarness.WaitBudget));
        Assert.Null(failures[0]);
        Assert.Null(failures[1]);
        Assert.True(
            observations[0] == baselineA && observations[1] == baselineB,
            "Two runs suspended mid-evaluation simultaneously resumed to different observations "
            + $"than their sequential baselines.\n  A baseline: {baselineA}\n  A observed: {observations[0]}\n"
            + $"  B baseline: {baselineB}\n  B observed: {observations[1]}");
    }

    private static Thread GatedLane(
        Expr root, EvaluationGate gate, int index, string?[] observations, Exception?[] failures, string label)
        => new(() =>
        {
            try
            {
                observations[index] = ConcurrencyHarness.EncodeCounted(
                    Evaluator.RunCounted(root, new GatedZeroArgPropertyResultCache(gate)));
            }
            catch (Exception ex)
            {
                failures[index] = ex;
            }
        })
        {
            IsBackground = true,
            Name = $"katlang-gated-{label}",
        };

    /// <summary>
    /// Budget isolation, deterministically interleaved: a run with a
    /// configured step budget is suspended mid-loop while another run EXHAUSTS
    /// its own step budget and a third succeeds; the suspended run then
    /// resumes and completes within its budget exactly as its baseline did.
    /// </summary>
    [Fact]
    public void GatedRunWithStepBudget_OtherRunExhaustsItsOwnBudget_GatedStillCompletesWithinBudget()
    {
        const string gatedProgram = "P = 3\nstep(s) = s + P\nrepeat(step, 2000, 0)";
        var gatedLimits = new EvaluationLimits { MaxSteps = 50_000 };

        var baselineGated = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, gatedProgram, gatedLimits);
        Assert.StartsWith("ok", baselineGated, StringComparison.Ordinal);
        var baselineExhausted = ConcurrencyHarness.Observe(
            EvalEntryPoint.RunCounted, ConcurrencyCorpus.HeavyLoop, ConcurrencyCorpus.TinySteps);
        Assert.StartsWith("err", baselineExhausted, StringComparison.Ordinal);
        var baselineSmall = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.Scalar);

        var gatedRoot = ConcurrencyHarness.ParseRoot(gatedProgram);
        var gate = new EvaluationGate();
        var gatedCache = new GatedZeroArgPropertyResultCache(gate, gateAtAccess: 1);

        string? gatedObservation = null;
        Exception? gatedFailure = null;
        var gatedThread = new Thread(() =>
        {
            try
            {
                gatedObservation = ConcurrencyHarness.EncodeCounted(
                    Evaluator.RunCounted(gatedRoot, gatedCache, gatedLimits));
            }
            catch (Exception ex)
            {
                gatedFailure = ex;
            }
        })
        {
            IsBackground = true,
            Name = "katlang-gated-budget",
        };

        gatedThread.Start();
        try
        {
            gate.WaitUntilInside();

            // While the budgeted run is suspended: another run exhausts ITS
            // OWN budget (baseline failure) and a small unlimited run succeeds.
            Assert.Equal(
                baselineExhausted,
                ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.HeavyLoop, ConcurrencyCorpus.TinySteps));
            Assert.Equal(baselineSmall, ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.Scalar));
        }
        finally
        {
            gate.Release();
        }

        Assert.True(gatedThread.Join(ConcurrencyHarness.WaitBudget), "the gated budgeted run never finished after release");
        Assert.Null(gatedFailure);
        Assert.True(
            gatedObservation == baselineGated,
            "A step-budgeted run suspended mid-evaluation changed its verdict after another run exhausted "
            + $"ITS budget — budgets are not isolated.\n  baseline: {baselineGated}\n  observed: {gatedObservation}");
    }

    // ── Budget counter isolation (operational counters) ─────────────────────

    /// <summary>
    /// ONE shared <see cref="EvaluationLimits"/> instance, calibrated so a
    /// single run fits but two runs' combined work would not: both concurrent
    /// lanes must still succeed, because counters live in each run's own
    /// <c>EvaluationBudget</c>, never in the shared options object. The
    /// calibration is measured from this build's actual consumption, so the
    /// case cannot rot as accounting evolves.
    /// </summary>
    [Fact]
    public void SharedLimitsInstance_CalibratedSoTwoRunsCombinedWouldNotFit_BothConcurrentRunsSucceed()
    {
        var root = ConcurrencyHarness.ParseRoot(ConcurrencyCorpus.HeavyLoop);

        var probe = Evaluator.RunCountedObserved(root, new EvaluationLimits { MaxSteps = 1_000_000 });
        Assert.False(probe.Result.IsError);
        var singleRunSteps = probe.Budget.ConsumedSteps;
        Assert.True(singleRunSteps > 100, $"calibration probe consumed only {singleRunSteps} steps — program too small to calibrate");

        // Fits one run (with headroom), cannot fit two runs' combined charge.
        var sharedLimits = new EvaluationLimits { MaxSteps = singleRunSteps + singleRunSteps / 2 };
        var baseline = ConcurrencyHarness.ObservePrepared(EvalEntryPoint.RunCounted, root, sharedLimits);
        Assert.StartsWith("ok", baseline, StringComparison.Ordinal);

        for (var round = 1; round <= 4; round++)
        {
            var observed = ConcurrencyHarness.RunConcurrently(
                ("A", () => ConcurrencyHarness.ObservePrepared(EvalEntryPoint.RunCounted, root, sharedLimits)),
                ("B", () => ConcurrencyHarness.ObservePrepared(EvalEntryPoint.RunCounted, root, sharedLimits)));
            Assert.True(
                observed[0] == baseline && observed[1] == baseline,
                $"round {round}: two concurrent runs sharing ONE EvaluationLimits instance did not each get "
                + $"their full budget (single run: {singleRunSteps} steps; shared limit: {sharedLimits.MaxSteps}).\n"
                + $"  baseline: {baseline}\n  lane A:   {observed[0]}\n  lane B:   {observed[1]}");
        }
    }

    /// <summary>
    /// Exact operational-counter isolation: a small run's consumed steps are
    /// IDENTICAL whether a heavy run executes concurrently or not. (C#
    /// implementation observation via <c>RunCountedObserved</c>, compared
    /// between C# executions only — the BudgetConservation convention.)
    /// </summary>
    [Fact]
    public void ConcurrentHeavyRun_DoesNotChangeASmallRunsConsumedSteps()
    {
        var smallRoot = ConcurrencyHarness.ParseRoot(ConcurrencyCorpus.UserCallHeavy);
        var heavyRoot = ConcurrencyHarness.ParseRoot(ConcurrencyCorpus.HeavyLoop);
        var limits = new EvaluationLimits { MaxSteps = 1_000_000 };

        var sequential = Evaluator.RunCountedObserved(smallRoot, limits);
        Assert.False(sequential.Result.IsError);
        var sequentialSteps = sequential.Budget.ConsumedSteps;

        for (var round = 1; round <= 3; round++)
        {
            long concurrentSteps = -1;
            ConcurrencyHarness.RunConcurrently(
                ("heavy", () => ConcurrencyHarness.ObservePrepared(EvalEntryPoint.RunCounted, heavyRoot, limits)),
                ("small-observed", () =>
                {
                    var run = Evaluator.RunCountedObserved(smallRoot, limits);
                    Assert.False(run.Result.IsError);
                    concurrentSteps = run.Budget.ConsumedSteps;
                    return ConcurrencyHarness.EncodeCounted(run.Result);
                }));

            Assert.True(
                concurrentSteps == sequentialSteps,
                $"round {round}: the small run consumed {concurrentSteps} steps under concurrency but "
                + $"{sequentialSteps} sequentially — a concurrent run's work leaked into its counters.");
        }
    }

    // ── Engine/module concurrency ────────────────────────────────────────────

    private const string ModuleProgram = ConcurrencyCorpus.ModuleProgram;
    private const string ModuleContentA = ConcurrencyCorpus.ModuleContentA;
    private const string ModuleContentB = ConcurrencyCorpus.ModuleContentB;

    private static RunOptions ProviderFor(string content)
        => new() { DownloadCode = (_, _) => ValueTask.FromResult(content) };

    /// <summary>
    /// Two concurrent engine runs importing the SAME module URL from their own
    /// providers with DIFFERENT content: each observes its own module graph.
    /// Module identity is per-elaboration-scope (fresh ModuleLoader per
    /// <c>FrontEndPipeline.Process</c>), so equal URLs across concurrent runs
    /// share nothing. Absolute anchors pin the counted power (n=3 vs n=4).
    /// </summary>
    [Fact]
    public void ConcurrentEngineRuns_SameModuleUrlDifferentProviders_EachObserveTheirOwnContent()
    {
        var baselineA = ConcurrencyHarness.ObserveEngine(ModuleProgram, options: ProviderFor(ModuleContentA));
        var baselineB = ConcurrencyHarness.ObserveEngine(ModuleProgram, options: ProviderFor(ModuleContentB));
        Assert.StartsWith("engine ok n=3 ", baselineA, StringComparison.Ordinal);
        Assert.StartsWith("engine ok n=4 ", baselineB, StringComparison.Ordinal);

        for (var round = 1; round <= 4; round++)
        {
            var observed = ConcurrencyHarness.RunConcurrently(
                ("A", () => ConcurrencyHarness.ObserveEngine(ModuleProgram, options: ProviderFor(ModuleContentA))),
                ("B", () => ConcurrencyHarness.ObserveEngine(ModuleProgram, options: ProviderFor(ModuleContentB))));
            Assert.True(
                observed[0] == baselineA && observed[1] == baselineB,
                $"round {round}: concurrent engine runs importing the same URL from different providers "
                + $"cross-contaminated.\n  A baseline: {baselineA}\n  A observed: {observed[0]}\n"
                + $"  B baseline: {baselineB}\n  B observed: {observed[1]}");
        }
    }

    /// <summary>
    /// One engine run provably suspended INSIDE its module fetch (gated
    /// <c>DownloadCode</c>) while another engine run imports the SAME URL with
    /// different content to completion; the suspended run then resumes to its
    /// own baseline. Deterministic front-end overlap.
    /// </summary>
    [Fact]
    public void GatedEngineModuleFetch_OtherEngineRunUsesSameUrl_GatedResumesToItsOwnContent()
    {
        var baselineA = ConcurrencyHarness.ObserveEngine(ModuleProgram, options: ProviderFor(ModuleContentA));
        var baselineB = ConcurrencyHarness.ObserveEngine(ModuleProgram, options: ProviderFor(ModuleContentB));

        var gate = new EvaluationGate();
        var gatedOptions = new RunOptions
        {
            DownloadCode = (_, _) =>
            {
                gate.Pass();
                return ValueTask.FromResult(ModuleContentA);
            },
        };

        string? gatedObservation = null;
        Exception? gatedFailure = null;
        var gatedThread = new Thread(() =>
        {
            try
            {
                gatedObservation = ConcurrencyHarness.ObserveEngine(ModuleProgram, options: gatedOptions);
            }
            catch (Exception ex)
            {
                gatedFailure = ex;
            }
        })
        {
            IsBackground = true,
            Name = "katlang-gated-module",
        };

        gatedThread.Start();
        try
        {
            gate.WaitUntilInside();
            Assert.Equal(baselineB, ConcurrencyHarness.ObserveEngine(ModuleProgram, options: ProviderFor(ModuleContentB)));
        }
        finally
        {
            gate.Release();
        }

        Assert.True(gatedThread.Join(ConcurrencyHarness.WaitBudget), "the gated engine run never finished after release");
        Assert.Null(gatedFailure);
        Assert.True(
            gatedObservation == baselineA,
            "An engine run suspended inside its module fetch resumed to different content after another run "
            + $"imported the same URL — module identity leaked across elaboration scopes.\n"
            + $"  baseline: {baselineA}\n  observed: {gatedObservation}");
    }

    // ── Meta-tests ───────────────────────────────────────────────────────────

    [Fact]
    public void CaseIds_AreUnique()
        => Assert.Equal(Matrix.Count, Matrix.Select(c => c.Id).Distinct(StringComparer.Ordinal).Count());

    [Fact]
    public void EveryScenario_HasPairCases()
    {
        foreach (var scenario in Enum.GetValues<ConcurrencyScenario>())
        {
            Assert.True(
                Matrix.Any(c => c.Scenario == scenario),
                $"Scenario {scenario} has no pair cases — the campaign quietly shrank.");
        }
    }

    [Fact]
    public void EveryCase_IsWellFormed()
    {
        foreach (var pairCase in Matrix)
        {
            Assert.False(string.IsNullOrWhiteSpace(pairCase.ProgramA), $"{pairCase.Id}: empty program A");
            Assert.False(string.IsNullOrWhiteSpace(pairCase.ProgramB), $"{pairCase.Id}: empty program B");
            Assert.False(string.IsNullOrWhiteSpace(pairCase.Invariant), $"{pairCase.Id}: missing invariant");
            Assert.True(pairCase.Rounds >= 1, $"{pairCase.Id}: rounds must be >= 1");

            if (pairCase.Scenario == ConcurrencyScenario.CrossEntryPoint)
            {
                Assert.True(
                    pairCase.EntryA != pairCase.EntryB,
                    $"{pairCase.Id}: a CrossEntryPoint case must use two different entry points.");
            }

            if (pairCase.Scenario == ConcurrencyScenario.SameProgram)
            {
                Assert.True(
                    pairCase.ProgramA == pairCase.ProgramB,
                    $"{pairCase.Id}: a SameProgram case must run the same source in both lanes.");
            }
        }
    }
}
