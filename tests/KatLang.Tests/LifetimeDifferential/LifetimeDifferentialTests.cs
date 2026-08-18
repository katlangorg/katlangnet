using System.Text;

namespace KatLang.Tests.LifetimeDifferential;

/// <summary>
/// Runner for the lifetime differential corpus plus the fact-based audits
/// that do not fit the fresh-vs-polluted table shape: AST/source identity
/// reuse and the <see cref="ModuleLoader"/>-INSTANCE ownership contract
/// (whose module cache and budget are DOCUMENTED per-instance persistent
/// state — asserted here as intended behavior, not treated as leaks).
/// </summary>
public class LifetimeDifferentialTests
{
    private static readonly IReadOnlyList<LifetimeCase> Matrix = LifetimeDifferentialCorpus.Cases();

    private static readonly IReadOnlyDictionary<string, LifetimeCase> ById =
        Matrix.ToDictionary(c => c.Id, StringComparer.Ordinal);

    public static TheoryData<string> CaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var lifetimeCase in Matrix)
            data.Add(lifetimeCase.Id);
        return data;
    }

    [Theory]
    [MemberData(nameof(CaseIds))]
    public void History_DoesNotChangeTheTargetObservation(string caseId)
    {
        var lifetimeCase = ById[caseId];
        var usesHost = lifetimeCase.TargetModules is not null || lifetimeCase.HistoryModules is not null;

        // Baseline: a completely fresh host seeing only the FINAL module content.
        var freshHost = usesHost ? new LifetimeModuleHost(lifetimeCase.TargetModules ?? []) : null;
        var fresh = LifetimeHarness.Observe(lifetimeCase.Target, freshHost);
        if (fresh.Outcome != lifetimeCase.ExpectedFreshOutcome)
        {
            Assert.Fail(Report(lifetimeCase, fresh, polluted: null,
                $"the FRESH baseline no longer has the outcome class this case needs: expected "
                + $"'{lifetimeCase.ExpectedFreshOutcome}' but observed '{fresh.Outcome}' — the case has lost its "
                + "discriminating power; fix the target program or the case annotation"));
        }

        if (lifetimeCase.ExpectedFreshEmitted is { } expectedEmitted && fresh.Emitted != expectedEmitted)
        {
            Assert.Fail(Report(lifetimeCase, fresh, polluted: null,
                $"the FRESH baseline's absolute count anchor failed: expected n={expectedEmitted} but observed "
                + $"n={fresh.Emitted} — either stale module state reached a supposedly fresh host, or the case "
                + "annotation is out of date"));
        }

        // Fetch evidence: the production architecture gives every elaboration a
        // fresh ModuleLoader, so a module-loading target MUST fetch through the
        // caller's delegate on every run. A zero-fetch "fresh" run means some
        // other module source satisfied the load — exactly the cross-run cache
        // this campaign exists to detect. (An intentional future cross-run cache
        // would need to revisit this assertion together with its invalidation
        // story.)
        var targetLoadsModules = lifetimeCase.Target.Contains("load('", StringComparison.Ordinal);
        if (targetLoadsModules && freshHost is not null && fresh.Outcome == "ok"
            && freshHost.DownloadLog.Count == 0)
        {
            Assert.Fail(Report(lifetimeCase, fresh, polluted: null,
                "the fresh baseline loaded modules without a single fetch through its own provider — "
                + "module content came from outside this run's lifetime boundary"));
        }

        // Polluted: one reused host instance carries the whole history, then the
        // module map is switched to the target content and the target runs.
        var pollutedHost = usesHost
            ? new LifetimeModuleHost(lifetimeCase.HistoryModules ?? lifetimeCase.TargetModules ?? [])
            : null;
        for (var i = 0; i < lifetimeCase.History.Length; i++)
        {
            var historyObservation = LifetimeHarness.Observe(lifetimeCase.History[i], pollutedHost);
            var expectedHistoryOutcome = lifetimeCase.ExpectedHistoryOutcomes![i];
            if (historyObservation.Outcome != expectedHistoryOutcome)
            {
                Assert.Fail(Report(lifetimeCase, fresh, polluted: null,
                    $"history step {i} no longer has the outcome class this scenario needs: expected "
                    + $"'{expectedHistoryOutcome}' but observed '{historyObservation.Outcome}' "
                    + $"({historyObservation.Comparable.ReplaceLineEndings(" | ")}) — a poisoning history that "
                    + "stopped failing (or a success history that stopped succeeding) tests nothing"));
            }
        }

        pollutedHost?.SetFiles(lifetimeCase.TargetModules ?? []);
        var fetchesBeforeTarget = pollutedHost?.DownloadLog.Count ?? 0;
        var polluted = LifetimeHarness.Observe(lifetimeCase.Target, pollutedHost);

        if (fresh.Comparable != polluted.Comparable)
        {
            Assert.Fail(Report(lifetimeCase, fresh, polluted,
                "the polluted observation differs from the fresh baseline — prior activity leaked into this run"));
        }

        // Same fetch evidence on the polluted side: the target run after history
        // must still fetch its modules itself rather than inherit them.
        if (targetLoadsModules && pollutedHost is not null && polluted.Outcome == "ok"
            && pollutedHost.DownloadLog.Count == fetchesBeforeTarget)
        {
            Assert.Fail(Report(lifetimeCase, fresh, polluted,
                "the polluted target run loaded modules without fetching — module content crossed the "
                + "run lifetime boundary from the history phase"));
        }
    }

    private static string Report(
        LifetimeCase lifetimeCase,
        LifetimeObservation fresh,
        LifetimeObservation? polluted,
        string difference)
    {
        var report = new StringBuilder();
        report.AppendLine($"LIFETIME DIFFERENTIAL VIOLATION: {lifetimeCase.Id}");
        report.AppendLine($"  scenario={lifetimeCase.Scenario}");
        report.AppendLine($"  invariant: {lifetimeCase.Invariant}");
        report.AppendLine("  target:");
        foreach (var line in lifetimeCase.Target.Split('\n'))
            report.AppendLine($"    | {line}");
        report.AppendLine($"  history ({lifetimeCase.History.Length} step(s)):");
        foreach (var step in lifetimeCase.History)
            report.AppendLine($"    - {step.ReplaceLineEndings(" \\n ")}");
        if (lifetimeCase.HistoryModules is { } historyModules)
            report.AppendLine($"  history modules: {string.Join(", ", historyModules.Select(m => m.Url))}");
        if (lifetimeCase.TargetModules is { } targetModules)
            report.AppendLine($"  target modules:  {string.Join(", ", targetModules.Select(m => m.Url))}");
        report.AppendLine($"  fresh:    {fresh.Comparable.ReplaceLineEndings(" | ")}");
        if (polluted is not null)
            report.AppendLine($"  polluted: {polluted.Comparable.ReplaceLineEndings(" | ")}");
        report.AppendLine($"  difference: {difference}");
        return report.ToString();
    }

    // ── AST / source identity reuse ──────────────────────────────────────────

    /// <summary>
    /// The parsed AST is immutable and reusable: evaluating the SAME elaborated
    /// root twice (both evaluators) observes identically — correctness never
    /// depends on node identity, first-evaluation mutation, or metadata stuck
    /// to previously evaluated syntax.
    /// </summary>
    [Fact]
    public void SameParsedRoot_EvaluatedTwice_ObservesIdentically()
    {
        var root = new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid(LifetimeDifferentialCorpus.TargetCounted).Root);

        var first = Evaluator.RunCounted(root);
        var second = Evaluator.RunCounted(root);
        Assert.True(first.IsOk && second.IsOk, "both runs of the same AST must succeed");
        Assert.True(
            Result.ValueComparer.Equals(first.Value.Value, second.Value.Value)
            && first.Value.EmittedCount == second.Value.EmittedCount,
            $"same-AST re-evaluation diverged: {SemanticExplorerHarness.Neutral(first.Value.Value)} n={first.Value.EmittedCount} "
            + $"vs {SemanticExplorerHarness.Neutral(second.Value.Value)} n={second.Value.EmittedCount}");

        var plainAfterCounted = Evaluator.Run(root);
        Assert.True(plainAfterCounted.IsOk
            && Result.ValueComparer.Equals(plainAfterCounted.Value, first.Value.Value),
            "the plain evaluator on the already-evaluated AST must agree");
    }

    /// <summary>
    /// Structurally identical but reference-distinct ASTs (the same text parsed
    /// twice) observe identically — nothing is keyed by AST object identity.
    /// </summary>
    [Fact]
    public void SameSource_ParsedTwice_IndependentAstsObserveIdentically()
    {
        var first = new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid(LifetimeDifferentialCorpus.TargetScopes).Root);
        var second = new Expr.AlgorithmExpr(
            SourceProvenance.ParseValid(LifetimeDifferentialCorpus.TargetScopes).Root);
        Assert.NotSame(first.Algorithm, second.Algorithm);

        var firstRun = Evaluator.RunCounted(first);
        var secondRun = Evaluator.RunCounted(second);
        Assert.True(firstRun.IsOk && secondRun.IsOk);
        Assert.True(
            Result.ValueComparer.Equals(firstRun.Value.Value, secondRun.Value.Value)
            && firstRun.Value.EmittedCount == secondRun.Value.EmittedCount,
            "independently parsed ASTs of the same source diverged");
    }

    /// <summary>
    /// Two syntactically different but semantically equivalent programs stay
    /// equivalent after mixed history (the equivalence itself is the language's;
    /// the lifetime claim is that history cannot split them).
    /// </summary>
    [Fact]
    public void DiamondLoadOrderVariants_ObserveIdentically()
    {
        var hostB = new LifetimeModuleHost(
            (LifetimeDifferentialCorpus.UrlDb, LifetimeDifferentialCorpus.ModuleDb),
            (LifetimeDifferentialCorpus.UrlDc, LifetimeDifferentialCorpus.ModuleDc),
            (LifetimeDifferentialCorpus.UrlDd, LifetimeDifferentialCorpus.ModuleDd));
        var hostC = new LifetimeModuleHost(
            (LifetimeDifferentialCorpus.UrlDb, LifetimeDifferentialCorpus.ModuleDb),
            (LifetimeDifferentialCorpus.UrlDc, LifetimeDifferentialCorpus.ModuleDc),
            (LifetimeDifferentialCorpus.UrlDd, LifetimeDifferentialCorpus.ModuleDd));

        var bFirst = LifetimeHarness.Observe(LifetimeDifferentialCorpus.TargetDiamondBFirst, hostB);
        var cFirst = LifetimeHarness.Observe(LifetimeDifferentialCorpus.TargetDiamondCFirst, hostC);

        Assert.True(bFirst.Outcome == "ok" && cFirst.Outcome == "ok");
        Assert.Equal(bFirst.Comparable, cFirst.Comparable);
    }

    // ── ModuleLoader instance ownership contract ─────────────────────────────
    // One loader instance is ONE module-elaboration scope (see the constructor
    // remarks in ModuleLoader): its url-keyed cache and its budget persist
    // across Elaborate calls on that instance BY DESIGN. These facts pin the
    // intended lifetime — commit-on-success, no negative caching, cleanup on
    // failure, per-scope content pinning — using the loader's own public API
    // plus the internal counters exposed for exactly this kind of test.

    private static (Algorithm Elaborated, IReadOnlyList<Diagnostic> CallDiagnostics) ElaborateWith(
        ModuleLoader loader, List<Diagnostic> diagnostics, string source)
    {
        var syntax = Parser.ParseSyntax(source);
        Assert.False(syntax.HasErrors,
            "loader-contract source must parse cleanly: "
            + string.Join("; ", syntax.Diagnostics.Select(d => d.Message.Split('\n')[0])));

        var before = diagnostics.Count;
        var elaborated = loader.Elaborate(syntax.SyntaxRoot);
        return (elaborated, diagnostics.Skip(before).ToList());
    }

    /// <summary>
    /// Finishes the front end on a load-elaborated root in production order
    /// (mirrors <c>FrontEndPipeline.FinalizeElaboration</c>: parameter
    /// detection, implicit-argument resolution, property exposure) and returns
    /// the counted neutral observation.
    /// </summary>
    private static string FinishPipelineNeutral(Algorithm loadElaborated)
    {
        var (detected, detectionDiagnostics) = ParameterDetector.Detect(loadElaborated);
        Assert.DoesNotContain(detectionDiagnostics, d => d.Severity == DiagnosticSeverity.Error);
        var resolved = ImplicitArgumentResolver.Resolve(detected);
        var exposed = PropertyExposureResolver.Resolve(resolved);
        var counted = Evaluator.RunCounted(new Expr.AlgorithmExpr(exposed));
        return counted.IsOk
            ? $"ok raw={SemanticExplorerHarness.Neutral(counted.Value.Value)} n={counted.Value.EmittedCount}"
            : $"err {SemanticExplorerHarness.ErrorCategory(counted.Error)}";
    }

    /// <summary>
    /// A module whose content failed to parse is NOT negatively cached: on the
    /// SAME loader instance, correcting the content under the same identity
    /// re-fetches and succeeds exactly like a loader that only ever saw the
    /// corrected content (commit-on-success in FetchAndSplice).
    /// </summary>
    [Fact]
    public void LoaderInstance_FailedModuleIsNotCached_CorrectedSameIdentitySucceeds()
    {
        var host = new LifetimeModuleHost((LifetimeDifferentialCorpus.UrlM, LifetimeDifferentialCorpus.ModuleMBroken));
        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(diagnostics, host.Downloader);

        var (_, firstDiagnostics) = ElaborateWith(loader, diagnostics, LifetimeDifferentialCorpus.TargetModule);
        Assert.Contains(firstDiagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(0, loader.CachedModuleCount);
        Assert.Equal(0, loader.InProgressModuleCount);

        host.SetFiles((LifetimeDifferentialCorpus.UrlM, LifetimeDifferentialCorpus.ModuleMv1));
        var (corrected, secondDiagnostics) = ElaborateWith(loader, diagnostics, LifetimeDifferentialCorpus.TargetModule);
        Assert.DoesNotContain(secondDiagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(1, loader.CachedModuleCount);
        Assert.Equal(2, host.DownloadLog.Count);

        var freshHost = new LifetimeModuleHost((LifetimeDifferentialCorpus.UrlM, LifetimeDifferentialCorpus.ModuleMv1));
        var freshDiagnostics = new List<Diagnostic>();
        var freshLoader = new ModuleLoader(freshDiagnostics, freshHost.Downloader);
        var (fresh, freshCallDiagnostics) = ElaborateWith(freshLoader, freshDiagnostics, LifetimeDifferentialCorpus.TargetModule);
        Assert.DoesNotContain(freshCallDiagnostics, d => d.Severity == DiagnosticSeverity.Error);

        Assert.Equal(FinishPipelineNeutral(fresh), FinishPipelineNeutral(corrected));
    }

    /// <summary>
    /// INTENDED persistent state: within one loader instance, a successfully
    /// loaded identity pins its content — a later Elaborate on the same
    /// instance reuses the cached module without re-fetching, even after the
    /// provider's content changed. Cross-run visibility of new content is the
    /// fresh-loader-per-run boundary (pinned by identity/v1-then-v2 in the
    /// corpus), not cache invalidation inside a scope.
    /// </summary>
    [Fact]
    public void LoaderInstance_CachePinsContentPerScope_ByDesign()
    {
        var host = new LifetimeModuleHost((LifetimeDifferentialCorpus.UrlM, LifetimeDifferentialCorpus.ModuleMv1));
        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(diagnostics, host.Downloader);

        var (first, firstDiagnostics) = ElaborateWith(loader, diagnostics, LifetimeDifferentialCorpus.TargetModule);
        Assert.DoesNotContain(firstDiagnostics, d => d.Severity == DiagnosticSeverity.Error);

        host.SetFiles((LifetimeDifferentialCorpus.UrlM, LifetimeDifferentialCorpus.ModuleMv2));
        var (second, secondDiagnostics) = ElaborateWith(loader, diagnostics, LifetimeDifferentialCorpus.TargetModule);
        Assert.DoesNotContain(secondDiagnostics, d => d.Severity == DiagnosticSeverity.Error);

        // One download total: the second call was a cache hit on the same scope.
        Assert.Equal(1, host.DownloadLog.Count);
        Assert.Equal(FinishPipelineNeutral(first), FinishPipelineNeutral(second));

        // A FRESH loader (the per-run production boundary) sees the new content.
        var freshDiagnostics = new List<Diagnostic>();
        var freshLoader = new ModuleLoader(freshDiagnostics, host.Downloader);
        var (fresh, _) = ElaborateWith(freshLoader, freshDiagnostics, LifetimeDifferentialCorpus.TargetModule);
        Assert.NotEqual(FinishPipelineNeutral(first), FinishPipelineNeutral(fresh));
    }

    /// <summary>Diamond dependency: the shared leaf is fetched once per scope.</summary>
    [Fact]
    public void LoaderInstance_DiamondSharedDependency_FetchedOncePerScope()
    {
        var host = new LifetimeModuleHost(
            (LifetimeDifferentialCorpus.UrlDb, LifetimeDifferentialCorpus.ModuleDb),
            (LifetimeDifferentialCorpus.UrlDc, LifetimeDifferentialCorpus.ModuleDc),
            (LifetimeDifferentialCorpus.UrlDd, LifetimeDifferentialCorpus.ModuleDd));
        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(diagnostics, host.Downloader);

        var (_, callDiagnostics) = ElaborateWith(loader, diagnostics, LifetimeDifferentialCorpus.TargetDiamondBFirst);
        Assert.DoesNotContain(callDiagnostics, d => d.Severity == DiagnosticSeverity.Error);

        Assert.Equal(3, host.DownloadLog.Count);
        Assert.Equal(3, host.DownloadLog.Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(3, loader.CachedModuleCount);
        Assert.Equal(0, loader.InProgressModuleCount);
    }

    /// <summary>Repeated import of one url inside one program: one fetch.</summary>
    [Fact]
    public void LoaderInstance_RepeatedImportInOneProgram_SingleFetch()
    {
        var host = new LifetimeModuleHost((LifetimeDifferentialCorpus.UrlM, LifetimeDifferentialCorpus.ModuleMv1));
        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(diagnostics, host.Downloader);

        var (_, callDiagnostics) = ElaborateWith(loader, diagnostics, LifetimeDifferentialCorpus.TargetRepeatedImport);
        Assert.DoesNotContain(callDiagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(1, host.DownloadLog.Count);
    }

    /// <summary>
    /// Module identity is the NORMALIZED url (Uri.AbsoluteUri): dot-segment and
    /// host-case spellings are one identity (one fetch); path case makes two.
    /// </summary>
    [Fact]
    public void LoaderInstance_UrlNormalization_DefinesModuleIdentity()
    {
        var aliasHost = new LifetimeModuleHost(
            (LifetimeDifferentialCorpus.UrlI1, LifetimeDifferentialCorpus.ModuleI));
        var aliasDiagnostics = new List<Diagnostic>();
        var aliasLoader = new ModuleLoader(aliasDiagnostics, aliasHost.Downloader);
        var (_, aliasCallDiagnostics) = ElaborateWith(
            aliasLoader, aliasDiagnostics, LifetimeDifferentialCorpus.TargetDotSegmentAlias);
        Assert.DoesNotContain(aliasCallDiagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(1, aliasHost.DownloadLog.Count);
        Assert.Equal(LifetimeDifferentialCorpus.UrlI1, aliasHost.DownloadLog[0]);

        var hostCaseHost = new LifetimeModuleHost(
            (LifetimeDifferentialCorpus.UrlI1, LifetimeDifferentialCorpus.ModuleI));
        var hostCaseDiagnostics = new List<Diagnostic>();
        var hostCaseLoader = new ModuleLoader(hostCaseDiagnostics, hostCaseHost.Downloader);
        var (_, hostCaseCallDiagnostics) = ElaborateWith(
            hostCaseLoader, hostCaseDiagnostics, LifetimeDifferentialCorpus.TargetHostCaseAlias);
        Assert.DoesNotContain(hostCaseCallDiagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(1, hostCaseHost.DownloadLog.Count);

        var pathCaseHost = new LifetimeModuleHost(
            (LifetimeDifferentialCorpus.UrlI3Upper, LifetimeDifferentialCorpus.ModuleI3Upper),
            (LifetimeDifferentialCorpus.UrlI3Lower, LifetimeDifferentialCorpus.ModuleI3Lower));
        var pathCaseDiagnostics = new List<Diagnostic>();
        var pathCaseLoader = new ModuleLoader(pathCaseDiagnostics, pathCaseHost.Downloader);
        var (_, pathCaseCallDiagnostics) = ElaborateWith(
            pathCaseLoader, pathCaseDiagnostics, LifetimeDifferentialCorpus.TargetPathCaseDistinct);
        Assert.DoesNotContain(pathCaseCallDiagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(2, pathCaseHost.DownloadLog.Count);
    }

    /// <summary>
    /// A cycle rejection unwinds completely: the in-progress set is empty and
    /// the same loader instance elaborates an unrelated good program exactly
    /// like a fresh one.
    /// </summary>
    [Fact]
    public void LoaderInstance_CycleFailure_LeavesTheInstanceReusable()
    {
        var host = new LifetimeModuleHost(
            (LifetimeDifferentialCorpus.UrlC1, LifetimeDifferentialCorpus.ModuleC1),
            (LifetimeDifferentialCorpus.UrlC2, LifetimeDifferentialCorpus.ModuleC2),
            (LifetimeDifferentialCorpus.UrlM, LifetimeDifferentialCorpus.ModuleMv1));
        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(diagnostics, host.Downloader);

        var (_, cycleDiagnostics) = ElaborateWith(loader, diagnostics, LifetimeDifferentialCorpus.HistLoadCycle);
        Assert.Contains(cycleDiagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Equal(0, loader.InProgressModuleCount);

        var (afterCycle, goodDiagnostics) = ElaborateWith(loader, diagnostics, LifetimeDifferentialCorpus.TargetModule);
        Assert.DoesNotContain(goodDiagnostics, d => d.Severity == DiagnosticSeverity.Error);

        var freshHost = new LifetimeModuleHost((LifetimeDifferentialCorpus.UrlM, LifetimeDifferentialCorpus.ModuleMv1));
        var freshDiagnostics = new List<Diagnostic>();
        var freshLoader = new ModuleLoader(freshDiagnostics, freshHost.Downloader);
        var (fresh, _) = ElaborateWith(freshLoader, freshDiagnostics, LifetimeDifferentialCorpus.TargetModule);

        Assert.Equal(FinishPipelineNeutral(fresh), FinishPipelineNeutral(afterCycle));
    }

    // ── Corpus integrity and coverage ────────────────────────────────────────

    [Fact]
    public void CaseIds_AreUnique()
    {
        var duplicates = Matrix
            .GroupBy(c => c.Id, StringComparer.Ordinal)
            .Where(g => g.Count() > 1)
            .Select(g => g.Key)
            .ToList();
        Assert.True(duplicates.Count == 0, "Duplicate case ids: " + string.Join(", ", duplicates));
    }

    /// <summary>
    /// Every scenario in <see cref="LifetimeScenario"/> must keep at least one
    /// row — adding a required scenario without cases fails here, so the
    /// campaign cannot quietly shrink.
    /// </summary>
    [Fact]
    public void EveryScenario_HasCases()
    {
        var missing = Enum.GetValues<LifetimeScenario>()
            .Where(scenario => !Matrix.Any(c => c.Scenario == scenario))
            .Select(scenario => scenario.ToString())
            .ToList();
        Assert.True(missing.Count == 0,
            "Scenarios without lifetime cases (add rows to LifetimeDifferentialCorpus): "
            + string.Join(", ", missing));
    }

    [Fact]
    public void EveryCase_IsWellFormed()
    {
        var malformed = new List<string>();
        foreach (var lifetimeCase in Matrix)
        {
            if (lifetimeCase.History.Length == 0)
                malformed.Add($"{lifetimeCase.Id}: a lifetime case needs at least one history step");
            if (lifetimeCase.ExpectedHistoryOutcomes is null
                || lifetimeCase.ExpectedHistoryOutcomes.Length != lifetimeCase.History.Length)
                malformed.Add($"{lifetimeCase.Id}: every history step needs an expected outcome class");
            if (lifetimeCase.HistoryModules is not null && lifetimeCase.TargetModules is null)
                malformed.Add($"{lifetimeCase.Id}: HistoryModules requires TargetModules (the fresh baseline's map)");
            if (lifetimeCase.ExpectedFreshOutcome is not ("ok" or "err" or "parseError"))
                malformed.Add($"{lifetimeCase.Id}: unknown fresh outcome class '{lifetimeCase.ExpectedFreshOutcome}'");
        }

        Assert.True(malformed.Count == 0, string.Join(Environment.NewLine, malformed));
    }
}
