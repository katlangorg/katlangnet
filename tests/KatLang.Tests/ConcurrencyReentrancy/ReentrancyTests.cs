using KatLang.Evaluation.Caching;

namespace KatLang.Tests.ConcurrencyReentrancy;

/// <summary>
/// Reentrancy: nested KatLang evaluation started from host code that runs
/// WHILE an outer evaluation is in progress must observe exactly the same
/// semantics as an equivalent non-reentrant execution, and must leave the
/// outer run's observation unchanged.
///
/// <para><b>The two real host-code-inside-a-run seams</b> (the audit found no
/// others): the internal <see cref="IZeroArgPropertyResultCache"/>, consulted
/// inside a charged invocation region on every zero-argument property access
/// (the same seam <c>BudgetConservationTests</c> uses for fault injection —
/// ordinary evaluation takes no host callback), and the public
/// <see cref="RunOptions.DownloadCode"/> provider, invoked mid-front-end
/// during a <see cref="KatLangEngine.Run"/>. Both are exercised here with
/// full nested evaluator and engine runs, including nested failures that the
/// host contains, nested failures the host propagates (outer unwinds through
/// the production <c>finally</c> chain), multiple and recursive bounded
/// nesting, and nesting at sensitive outer phases (user calls, loop steps,
/// map callbacks).</para>
///
/// <para><b>Instance-reuse contracts.</b> <see cref="KatLangEngine"/> and
/// <see cref="Evaluator"/> are static facades — there is no engine/evaluator
/// instance to reuse, so "same instance reentrancy" reduces to the run-scoped
/// objects. The one host-shareable run object is a zero-argument property
/// cache instance passed to the internal overloads: entries are keyed by RUN
/// IDENTITY (the run's own <c>EvaluationBudget</c> reference —
/// <c>Evaluator.GetOrEvaluateZeroArgPropertyResultCore</c>), so sharing one
/// instance across sequential or nested runs never serves one run's entries
/// to another. Pinned here both sequentially and reentrantly with a
/// budget-verdict oracle. (CONCURRENT use of one cache instance is not part
/// of the contract: the backing dictionary is unsynchronized by design;
/// thread safety is by per-run isolation.)</para>
/// </summary>
public class ReentrancyTests
{
    /// <summary>Outer sentinel with two property accesses: the host action
    /// fires at the FIRST (inside its charged region); the second stays an
    /// ordinary cache hit after resumption.</summary>
    private const string OuterProgram = ConcurrencyCorpus.CachedPropA;

    private sealed class HostEscapeException : Exception
    {
        public HostEscapeException(string message) : base(message)
        {
        }
    }

    /// <summary>Runs the outer sentinel through the counted entry point with a
    /// host action injected at the k-th zero-argument property access, and
    /// returns the outer observation. Fails if the action never fired.</summary>
    private static string RunOuterWithHostAction(string outerProgram, Action hostAction, int actAtAccess = 1)
    {
        var root = ConcurrencyHarness.ParseRoot(outerProgram);
        var cache = new HostActionZeroArgPropertyResultCache(
            new RunScopedZeroArgPropertyResultCache(), actAtAccess, hostAction);
        var outer = ConcurrencyHarness.EncodeCounted(Evaluator.RunCounted(root, cache));
        Assert.True(cache.ActionRan, "the outer program never performed the instrumented property access");
        return outer;
    }

    // ── Nested runs inside outer property evaluation ─────────────────────────

    /// <summary>
    /// Full nested runs (counted evaluator AND engine) launched from inside
    /// the outer run's property evaluation: every nested observation equals
    /// its non-reentrant baseline (multi-output, zero-output, and a contained
    /// nested failure), and the outer run is byte-for-byte undisturbed —
    /// nested counted state cannot alter outer counted state.
    /// </summary>
    [Theory]
    [InlineData(ConcurrencyCorpus.MultiOut)]
    [InlineData(ConcurrencyCorpus.ZeroOut)]
    [InlineData(ConcurrencyCorpus.FailingIndex)]
    public void NestedRuns_InsideOuterPropertyEvaluation_ObserveBaselines_AndOuterIsUndisturbed(string nestedProgram)
    {
        var outerBaseline = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, OuterProgram);
        var nestedCountedBaseline = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, nestedProgram);
        var nestedEngineBaseline = ConcurrencyHarness.ObserveEngine(nestedProgram);

        string? nestedCounted = null;
        string? nestedEngine = null;
        var outer = RunOuterWithHostAction(OuterProgram, () =>
        {
            nestedCounted = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, nestedProgram);
            nestedEngine = ConcurrencyHarness.ObserveEngine(nestedProgram);
        });

        Assert.Equal(nestedCountedBaseline, nestedCounted);
        Assert.Equal(nestedEngineBaseline, nestedEngine);
        Assert.True(
            outer == outerBaseline,
            "A nested evaluation inside the outer run's property evaluation disturbed the outer observation.\n"
            + $"  nested program:\n{nestedProgram}\n  outer baseline: {outerBaseline}\n  outer observed: {outer}");
    }

    /// <summary>Nested runs through the remaining PUBLIC entry points
    /// (<c>Evaluator.Run</c>, <c>Evaluator.RunFlat</c>) from inside an outer
    /// evaluation.</summary>
    [Fact]
    public void NestedPublicRunAndRunFlat_InsideOuterEvaluation_ObserveBaselines()
    {
        var outerBaseline = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, OuterProgram);
        var nestedPlainBaseline = ConcurrencyHarness.Observe(EvalEntryPoint.RunPlain, ConcurrencyCorpus.CaptureSpread);
        var nestedFlatBaseline = ConcurrencyHarness.Observe(EvalEntryPoint.RunFlat, ConcurrencyCorpus.Loop);

        string? nestedPlain = null;
        string? nestedFlat = null;
        var outer = RunOuterWithHostAction(OuterProgram, () =>
        {
            nestedPlain = ConcurrencyHarness.Observe(EvalEntryPoint.RunPlain, ConcurrencyCorpus.CaptureSpread);
            nestedFlat = ConcurrencyHarness.Observe(EvalEntryPoint.RunFlat, ConcurrencyCorpus.Loop);
        });

        Assert.Equal(nestedPlainBaseline, nestedPlain);
        Assert.Equal(nestedFlatBaseline, nestedFlat);
        Assert.Equal(outerBaseline, outer);
    }

    /// <summary>
    /// Reentrancy at sensitive outer phases: the nested run launches while the
    /// outer run is inside a user-function call, a loop step, or a
    /// map-callback invocation (chosen by where the outer program's first
    /// property access sits). Catches any hidden "one active evaluator/current
    /// algorithm" process state — none exists, and this keeps it that way.
    /// </summary>
    [Theory]
    [InlineData(ConcurrencyCorpus.SensitiveUserCall)]
    [InlineData(ConcurrencyCorpus.SensitiveLoopStep)]
    [InlineData(ConcurrencyCorpus.SensitiveMapCallback)]
    [InlineData(ConcurrencyCorpus.CachedPropA)]
    public void NestedRun_AtSensitiveOuterPhases_OuterAndNestedObserveBaselines(string outerProgram)
    {
        var outerBaseline = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, outerProgram);
        var nestedBaseline = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.MultiOut);

        string? nested = null;
        var outer = RunOuterWithHostAction(outerProgram, () =>
        {
            nested = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.MultiOut);
        });

        Assert.Equal(nestedBaseline, nested);
        Assert.True(
            outer == outerBaseline,
            $"Outer program disturbed by a nested run at a sensitive phase.\n  outer:\n{outerProgram}\n"
            + $"  baseline: {outerBaseline}\n  observed: {outer}");
    }

    /// <summary>Two nested runs (B then C) inside one host action.</summary>
    [Fact]
    public void MultipleNestedRuns_InsideOneHostAction_AllObserveBaselines()
    {
        var outerBaseline = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, OuterProgram);
        var baselineB = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.ClauseFamily);
        var baselineC = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.Collecting);

        string? nestedB = null;
        string? nestedC = null;
        var outer = RunOuterWithHostAction(OuterProgram, () =>
        {
            nestedB = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.ClauseFamily);
            nestedC = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.Collecting);
        });

        Assert.Equal(baselineB, nestedB);
        Assert.Equal(baselineC, nestedC);
        Assert.Equal(outerBaseline, outer);
    }

    /// <summary>
    /// Bounded recursive reentrancy: each nesting level runs the same-shaped
    /// program (its own freshly parsed AST) and nests one more level until
    /// depth 3. Every level observes the baseline.
    /// </summary>
    [Fact]
    public void RecursiveReentrancy_BoundedToThreeLevels_EveryLevelObservesTheBaseline()
    {
        var baseline = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, OuterProgram);
        var innerObservations = new List<string>();

        string RunLevel(int depth)
        {
            var root = ConcurrencyHarness.ParseRoot(OuterProgram);
            var cache = new HostActionZeroArgPropertyResultCache(
                new RunScopedZeroArgPropertyResultCache(),
                actAtAccess: 1,
                () =>
                {
                    if (depth < 3)
                        innerObservations.Add(RunLevel(depth + 1));
                });
            return ConcurrencyHarness.EncodeCounted(Evaluator.RunCounted(root, cache));
        }

        var top = RunLevel(1);

        Assert.Equal(baseline, top);
        Assert.Equal(2, innerObservations.Count);
        Assert.All(innerObservations, observation => Assert.Equal(baseline, observation));
    }

    // ── Nested failure propagation and cleanup ───────────────────────────────

    /// <summary>
    /// The host CONTAINS a nested failure (the nested run returns a structured
    /// error result; nothing is thrown) and the outer run resumes undisturbed.
    /// </summary>
    [Fact]
    public void NestedFailure_ContainedByHost_OuterResumesToBaseline()
    {
        var outerBaseline = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, OuterProgram);
        var nestedBaseline = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.RecursionRunaway);
        Assert.StartsWith("err", nestedBaseline, StringComparison.Ordinal);

        string? nested = null;
        var outer = RunOuterWithHostAction(OuterProgram, () =>
        {
            nested = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.RecursionRunaway);
        });

        Assert.Equal(nestedBaseline, nested);
        Assert.Equal(outerBaseline, outer);
    }

    /// <summary>
    /// The host PROPAGATES after a nested failure: the exception unwinds the
    /// outer run through the production <c>finally</c> chain and surfaces to
    /// the outer caller as-is (same instance). A clean sentinel afterwards
    /// matches its baseline — the abandoned outer run left no process-global
    /// state behind. (Balanced budget release on this exact unwind path is
    /// separately pinned by <c>BudgetConservationTests</c>.)
    /// </summary>
    [Fact]
    public void NestedFailure_PropagatedByHost_UnwindsOuterRun_AndLeavesNoGlobalStateBehind()
    {
        var sentinelBaseline = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.CleanupSentinel);
        var escape = new HostEscapeException("nested evaluation failed; host escalates");

        var thrown = Assert.Throws<HostEscapeException>(() =>
            RunOuterWithHostAction(OuterProgram, () =>
            {
                var nested = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.FailingIndex);
                Assert.StartsWith("err", nested, StringComparison.Ordinal);
                throw escape;
            }));

        Assert.Same(escape, thrown);
        Assert.Equal(sentinelBaseline, ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.CleanupSentinel));
    }

    // ── Shared cache instance: run isolation by run identity ────────────────

    /// <summary>
    /// SEQUENTIAL cross-run sharing of one cache instance (the documented-safe
    /// host reuse): a second run of the SAME AST through the SAME cache with a
    /// tiny step budget must re-evaluate and FAIL on its own budget — a stale
    /// hit from the first run would make it succeed. This pins the run-identity
    /// key component (the run's own <c>EvaluationBudget</c>) with a
    /// budget-VERDICT oracle: structural owner identity and every environment
    /// identity are equal across the two runs by construction, so run identity
    /// is the only thing separating the entries.
    /// </summary>
    [Fact]
    public void SharedCacheInstance_SequentialRuns_NeverServeEntriesAcrossRuns()
    {
        const string program = "Box = {P = {step(s) = s + 1\nrepeat(step, 500, 0)}\nQ = 1}\nBox.P, Box.Q";
        var root = ConcurrencyHarness.ParseRoot(program);
        var tiny = new EvaluationLimits { MaxSteps = 50 };

        var baselineFull = ConcurrencyHarness.EncodeCounted(
            Evaluator.RunCounted(root, new RunScopedZeroArgPropertyResultCache()));
        Assert.StartsWith("ok", baselineFull, StringComparison.Ordinal);
        var baselineTiny = ConcurrencyHarness.EncodeCounted(
            Evaluator.RunCounted(root, new RunScopedZeroArgPropertyResultCache(), tiny));
        Assert.StartsWith("err", baselineTiny, StringComparison.Ordinal);

        var shared = new RunScopedZeroArgPropertyResultCache();
        var first = ConcurrencyHarness.EncodeCounted(Evaluator.RunCounted(root, shared));
        Assert.Equal(baselineFull, first);

        var second = ConcurrencyHarness.EncodeCounted(Evaluator.RunCounted(root, shared, tiny));
        Assert.True(
            second == baselineTiny,
            "A second run through a HOST-SHARED cache instance did not match the fresh-cache baseline — "
            + "an entry stored by the first run was served across the run boundary (run identity ignored).\n"
            + $"  fresh-cache baseline: {baselineTiny}\n  shared-cache observed: {second}");
    }

    /// <summary>
    /// REENTRANT variant: the nested run shares the outer run's live cache
    /// instance while the outer run is mid-evaluation and has ALREADY stored
    /// the expensive property's entry. The nested run (own tiny budget) must
    /// still re-evaluate and fail on its own budget; the outer run resumes to
    /// its baseline.
    /// </summary>
    [Fact]
    public void SharedCacheInstance_NestedRunInsideOuter_IsStillRunIsolated()
    {
        const string program = "Box = {P = {step(s) = s + 1\nrepeat(step, 500, 0)}\nQ = 1}\nBox.P, Box.Q";
        var root = ConcurrencyHarness.ParseRoot(program);
        var tiny = new EvaluationLimits { MaxSteps = 50 };

        var baselineFull = ConcurrencyHarness.EncodeCounted(
            Evaluator.RunCounted(root, new RunScopedZeroArgPropertyResultCache()));
        var baselineTiny = ConcurrencyHarness.EncodeCounted(
            Evaluator.RunCounted(root, new RunScopedZeroArgPropertyResultCache(), tiny));
        Assert.StartsWith("err", baselineTiny, StringComparison.Ordinal);

        // Probe: total zero-arg accesses in one outer run, so the host action
        // can fire at the LAST access — by then the first row's expensive
        // entry (Box.P) is guaranteed stored in the shared instance.
        var probeCache = new HostActionZeroArgPropertyResultCache(
            new RunScopedZeroArgPropertyResultCache(), actAtAccess: int.MaxValue, hostAction: static () => { });
        Assert.False(Evaluator.RunCounted(root, probeCache).IsError);
        Assert.True(probeCache.Accesses >= 2, "expected at least the Box.P and Box.Q accesses");

        var shared = new RunScopedZeroArgPropertyResultCache();
        string? nested = null;
        var outerCache = new HostActionZeroArgPropertyResultCache(
            shared,
            actAtAccess: probeCache.Accesses,
            () =>
            {
                nested = ConcurrencyHarness.EncodeCounted(Evaluator.RunCounted(root, shared, tiny));
            });

        var outer = ConcurrencyHarness.EncodeCounted(Evaluator.RunCounted(root, outerCache));
        Assert.True(outerCache.ActionRan, "the outer run never reached the final instrumented access");

        Assert.True(
            nested == baselineTiny,
            "A NESTED run sharing the outer run's live cache instance was served the outer run's entry "
            + $"instead of re-evaluating under its own budget.\n  fresh-cache baseline: {baselineTiny}\n  nested observed: {nested}");
        Assert.Equal(baselineFull, outer);
    }

    // ── Engine-level reentrancy (public DownloadCode seam) ───────────────────

    /// <summary>
    /// Nested engine and evaluator runs launched from inside an outer engine
    /// run's module fetch: outer and both nested observations equal their
    /// baselines. The nested engine run creates its own front end (fresh
    /// ModuleLoader per <c>FrontEndPipeline.Process</c>), so nesting cannot
    /// disturb the outer elaboration scope.
    /// </summary>
    [Fact]
    public void EngineReentrancy_NestedRunsInsideModuleFetch_AllObserveBaselines()
    {
        var outerBaseline = ConcurrencyHarness.ObserveEngine(
            ConcurrencyCorpus.ModuleProgram,
            options: new RunOptions { DownloadCode = _ => ConcurrencyCorpus.ModuleContentA });
        Assert.StartsWith("engine ok n=3 ", outerBaseline, StringComparison.Ordinal);
        var nestedEngineBaseline = ConcurrencyHarness.ObserveEngine(ConcurrencyCorpus.MultiOut);
        var nestedEvalBaseline = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.ClauseFamily);

        string? nestedEngine = null;
        string? nestedEval = null;
        var gatedOptions = new RunOptions
        {
            DownloadCode = _ =>
            {
                nestedEngine = ConcurrencyHarness.ObserveEngine(ConcurrencyCorpus.MultiOut);
                nestedEval = ConcurrencyHarness.Observe(EvalEntryPoint.RunCounted, ConcurrencyCorpus.ClauseFamily);
                return ConcurrencyCorpus.ModuleContentA;
            },
        };

        var outer = ConcurrencyHarness.ObserveEngine(ConcurrencyCorpus.ModuleProgram, options: gatedOptions);

        Assert.Equal(nestedEngineBaseline, nestedEngine);
        Assert.Equal(nestedEvalBaseline, nestedEval);
        Assert.Equal(outerBaseline, outer);
    }

    /// <summary>
    /// A nested MODULE-BACKED engine run inside another engine run's module
    /// fetch, importing the SAME URL with DIFFERENT content through its own
    /// provider: the outer elaboration keeps its own content (n=3), the nested
    /// one its own (n=4) — module identity is per elaboration scope even under
    /// reentrancy.
    /// </summary>
    [Fact]
    public void EngineReentrancy_NestedModuleImportOfSameUrl_KeepsBothElaborationScopesSeparate()
    {
        var outerBaseline = ConcurrencyHarness.ObserveEngine(
            ConcurrencyCorpus.ModuleProgram,
            options: new RunOptions { DownloadCode = _ => ConcurrencyCorpus.ModuleContentA });
        var nestedBaseline = ConcurrencyHarness.ObserveEngine(
            ConcurrencyCorpus.ModuleProgram,
            options: new RunOptions { DownloadCode = _ => ConcurrencyCorpus.ModuleContentB });
        Assert.StartsWith("engine ok n=3 ", outerBaseline, StringComparison.Ordinal);
        Assert.StartsWith("engine ok n=4 ", nestedBaseline, StringComparison.Ordinal);

        string? nested = null;
        var outerOptions = new RunOptions
        {
            DownloadCode = _ =>
            {
                nested = ConcurrencyHarness.ObserveEngine(
                    ConcurrencyCorpus.ModuleProgram,
                    options: new RunOptions { DownloadCode = _ => ConcurrencyCorpus.ModuleContentB });
                return ConcurrencyCorpus.ModuleContentA;
            },
        };

        var outer = ConcurrencyHarness.ObserveEngine(ConcurrencyCorpus.ModuleProgram, options: outerOptions);

        Assert.Equal(nestedBaseline, nested);
        Assert.Equal(outerBaseline, outer);
    }
}
