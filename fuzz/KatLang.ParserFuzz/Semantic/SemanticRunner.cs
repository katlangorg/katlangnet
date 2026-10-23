using System.Collections.Immutable;
using System.Globalization;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>How one case ended. Failure classes are deliberately distinct (SEM-2B).</summary>
internal enum SemanticVerdict
{
    /// <summary>Every anchor, parity relation and transformation held.</summary>
    Passed,

    /// <summary>An observation disagreed with the construction-derived expectation, a declared parity, or a relation.</summary>
    Mismatch,

    /// <summary>A VALID case's source was rejected by the front end (generator, adapter or engine defect — never discarded).</summary>
    FrontEndUnexpected,

    /// <summary>An INVALID case was accepted, or rejected with the wrong diagnostic or phase.</summary>
    FrontEndExpectation,

    /// <summary>A run stopped at a resource limit the case never expected.</summary>
    ResourceTermination,

    /// <summary>Required observation data was absent: two absent fields are never evidence of equality.</summary>
    MissingObservation,

    /// <summary>The apparatus itself failed (an observer contradiction, an in-process async watchdog).</summary>
    HarnessFailure,

    /// <summary>Supervised only: the external deadline expired; the worker tree was terminated.</summary>
    Timeout,

    /// <summary>The supervisor was cancelled externally and terminated its worker.</summary>
    SupervisorCancellation,

    /// <summary>Supervised only: the worker exited abnormally without a result.</summary>
    Crash,

    /// <summary>Supervised only: the worker's result could not be parsed.</summary>
    MalformedOutput,

    /// <summary>A replay descriptor no longer reconstructs to its recorded source.</summary>
    RecipeDrift,
}

/// <summary>One profile execution of one member, reduced to durable facts (no live evaluator state).</summary>
internal sealed record SemanticProfileRun(
    string Profile,
    string Member,
    bool Ran,
    string Reason,
    MetamorphicOperationalObservation? Observation,
    ImmutableArray<string> Events,
    int WaitCalls,
    int Suspensions,
    bool FirstSuspensionReturnedControl,
    bool Cancelled,
    string? HarnessProblem)
{
    public string OutcomeText => HarnessProblem is not null
        ? "harness"
        : Cancelled ? "cancelled" : !Ran ? "not-run:" + Reason : Observation?.Semantic.Outcome ?? "missing-observation";
}

/// <summary>The complete, durable result of one case.</summary>
internal sealed record SemanticCaseResult(
    string CaseId,
    SemanticVerdict Verdict,
    ImmutableArray<string> Findings,
    ImmutableArray<SemanticProfileRun> Runs,
    SemanticPath PathsExercised,
    ImmutableArray<string> PathRejections,
    ImmutableArray<string> RelationsChecked)
{
    public bool Passed => Verdict == SemanticVerdict.Passed;

    public string Headline => Verdict == SemanticVerdict.Passed
        ? $"{CaseId}: passed"
        : $"{CaseId}: {Verdict}: {(Findings.IsEmpty ? "-" : Findings[0])}";
}

/// <summary>
/// Executes one SEM-2B case through the SHARED profile adapters (<see cref="MetamorphicSurfaces"/>)
/// and judges it with the SHARED SEM-2A observer and comparator. This is the one pipeline used by
/// the deterministic tests, direct replay, and the supervised worker.
/// </summary>
internal static class SemanticRunner
{
    /// <summary>
    /// Runs a case. <paramref name="observationFilter"/> is an inert test seam: when supplied it may
    /// replace a profile run AFTER execution and BEFORE judgement, so apparatus tests can prove a
    /// wrong or incomplete observation is rejected. Production callers never pass it.
    /// </summary>
    internal static SemanticCaseResult Run(
        SemanticCase semanticCase, Func<SemanticProfileRun, SemanticProfileRun>? observationFilter = null)
    {
        ArgumentNullException.ThrowIfNull(semanticCase);
        var findings = new List<(SemanticVerdict Verdict, string Text)>();
        var runs = new List<SemanticProfileRun>();
        var relations = new List<string>();
        var rejections = new List<string>();
        var exercised = SemanticPath.None;
        var expected = semanticCase.Expected;

        if (semanticCase.Profiles.IsEmpty || semanticCase.Members.IsEmpty
            || (semanticCase.Members.Length > 1 && !semanticCase.Profiles.Contains(SemanticProfiles.SyncOptimized)))
            return new SemanticCaseResult(semanticCase.CaseId, SemanticVerdict.HarnessFailure,
                ["a case needs members and execution profiles, including sync-optimized for transformations; nothing verified"], [], SemanticPath.None, [], []);

        // 1. Front end, for every member, BEFORE any evaluator assertion.
        foreach (var member in semanticCase.Members)
            CheckFrontEnd(semanticCase, member, findings);

        // 2. The base member through every selected profile.
        var baseRuns = new Dictionary<string, SemanticProfileRun>(StringComparer.Ordinal);
        foreach (var profileId in semanticCase.Profiles)
        {
            var profile = SemanticProfiles.Get(profileId);
            var run = Execute(semanticCase.Source, profile, SemanticMember.BaseRole);
            if (observationFilter is not null) run = observationFilter(run);
            runs.Add(run);
            baseRuns[profileId] = run;
            CheckAnchors(semanticCase, profile, run, findings);
        }

        // 3. Intended paths: evidence participates in admission, anchors establish the rest.
        if (semanticCase.Kind != SemanticCaseKind.InvalidFrontEnd)
        {
            exercised = JudgePaths(semanticCase, baseRuns, rejections);
            foreach (var rejection in rejections)
                findings.Add((SemanticVerdict.MissingObservation, "required path not admitted: " + rejection));
        }

        // 4. Declared profile parity over one source.
        foreach (var pair in SemanticProfiles.Pairs)
        {
            if (!baseRuns.TryGetValue(pair.Left, out var left) || !baseRuns.TryGetValue(pair.Right, out var right)) continue;
            if (left.Observation is null || right.Observation is null) continue;
            relations.Add(pair.Id);
            try
            {
                if (MetamorphicComparator.Compare(pair.SemanticRelation, pair.OperationalRelation,
                        MetamorphicErrorPolicy.StrictSameSource, left.Observation, right.Observation) is { } mismatch)
                    findings.Add((SemanticVerdict.Mismatch, $"{pair.Id}: {mismatch.Headline}"));
            }
            catch (MetamorphicHarnessException exception)
            {
                findings.Add((SemanticVerdict.MissingObservation, $"{pair.Id}: {exception.Message}"));
            }

            if (!left.Events.SequenceEqual(right.Events))
                findings.Add((SemanticVerdict.Mismatch, $"{pair.Id}: host events differ [{string.Join(",", left.Events)}] vs [{string.Join(",", right.Events)}]"));
        }

        if (baseRuns.TryGetValue(SemanticProfiles.AsyncTwinCancel, out var cancelTwin)
            && baseRuns.TryGetValue(SemanticProfiles.EngineRunAsyncCancel, out var cancelEngine))
        {
            relations.Add("parity:" + SemanticProfiles.AsyncTwinCancel + "~" + SemanticProfiles.EngineRunAsyncCancel);
            if (cancelTwin.Cancelled != cancelEngine.Cancelled || !cancelTwin.Events.SequenceEqual(cancelEngine.Events))
                findings.Add((SemanticVerdict.Mismatch, "cancellation parity: twin and public async runs ended differently"));
        }

        // 5. Well-founded transformations: same anchors, and equal to the base under one profile.
        if (baseRuns.TryGetValue(SemanticProfiles.SyncOptimized, out var baseOptimized) && baseOptimized.Observation is { } baseObservation)
        {
            var profile = SemanticProfiles.Get(SemanticProfiles.SyncOptimized);
            foreach (var member in semanticCase.Members.Skip(1))
            {
                var run = Execute(member.Source, profile, member.Role);
                if (observationFilter is not null) run = observationFilter(run);
                runs.Add(run);
                CheckAnchors(semanticCase, profile, run, findings);
                relations.Add("relation:" + member.Role);
                if (run.Observation is not { } observation) continue;
                try
                {
                    if (MetamorphicComparator.Compare(MetamorphicSemanticRelation.SemanticEqual, MetamorphicOperationalRelation.NotCompared,
                            MetamorphicErrorPolicy.Normalized, baseObservation, observation) is { } mismatch)
                        findings.Add((SemanticVerdict.Mismatch, $"relation:{member.Role}: {mismatch.Headline}"));
                }
                catch (MetamorphicHarnessException exception)
                {
                    findings.Add((SemanticVerdict.MissingObservation, $"relation:{member.Role}: {exception.Message}"));
                }
            }
        }

        var verdict = findings.Count == 0 ? SemanticVerdict.Passed : findings.Select(f => f.Verdict).Aggregate(Severity);
        return new SemanticCaseResult(
            semanticCase.CaseId,
            verdict,
            [.. findings.Select(f => f.Text)],
            [.. runs],
            verdict == SemanticVerdict.Passed ? exercised : SemanticPath.None,
            [.. rejections],
            [.. relations]);
    }

    /// <summary>The most specific verdict wins: front-end and harness problems before mismatches.</summary>
    private static SemanticVerdict Severity(SemanticVerdict a, SemanticVerdict b) => Rank(a) <= Rank(b) ? a : b;

    private static int Rank(SemanticVerdict verdict) => verdict switch
    {
        SemanticVerdict.HarnessFailure => 0,
        SemanticVerdict.FrontEndUnexpected => 1,
        SemanticVerdict.FrontEndExpectation => 2,
        SemanticVerdict.MissingObservation => 3,
        SemanticVerdict.ResourceTermination => 4,
        _ => 5,
    };

    // ── Front end ───────────────────────────────────────────────────────────

    private static void CheckFrontEnd(SemanticCase semanticCase, SemanticMember member, List<(SemanticVerdict, string)> findings)
    {
        var syntax = Parser.ParseSyntax(member.Source);
        var parsed = Parser.Parse(member.Source, new RunOptions { HostOperations = MetamorphicHostFixture.Synchronous().Operations });
        var expected = semanticCase.Expected;

        if (semanticCase.Kind != SemanticCaseKind.InvalidFrontEnd)
        {
            if (parsed.HasErrors)
            {
                var first = parsed.Diagnostics.First(d => d.Severity == DiagnosticSeverity.Error);
                findings.Add((SemanticVerdict.FrontEndUnexpected,
                    $"{member.Role}: valid source rejected by the front end ({first.Code}: {Preview(first.Message)})"));
            }

            return;
        }

        var syntaxCodes = syntax.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error).Select(d => d.Code).ToList();
        var allCodes = parsed.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error).Select(d => d.Code).ToList();
        var phase = syntaxCodes.Count > 0 ? SemanticExpectation.SyntaxPhase : SemanticExpectation.ElaborationPhase;
        var codes = phase == SemanticExpectation.SyntaxPhase ? syntaxCodes : allCodes;
        if (allCodes.Count == 0)
            findings.Add((SemanticVerdict.FrontEndExpectation, $"{member.Role}: invalid source accepted (expected {expected.Diagnostic} in {expected.DiagnosticPhase})"));
        else if (!string.Equals(phase, expected.DiagnosticPhase, StringComparison.Ordinal))
            findings.Add((SemanticVerdict.FrontEndExpectation, $"{member.Role}: rejected in phase {phase}, expected {expected.DiagnosticPhase}"));
        else if (!codes.Contains(expected.Diagnostic!.Value))
            findings.Add((SemanticVerdict.FrontEndExpectation,
                $"{member.Role}: expected diagnostic {expected.Diagnostic} in {phase}, got [{string.Join(",", codes)}]"));
    }

    // ── Execution ───────────────────────────────────────────────────────────

    /// <summary>One run of one source through one profile, with a fresh host fixture.</summary>
    internal static SemanticProfileRun Execute(string source, SemanticProfile profile, string member)
    {
        var executionProfile = profile.ExecutionProfile;
        var options = MetamorphicExecutor.OptionsFor(executionProfile);
        if (profile.AfterInterleavedRun)
        {
            // An unrelated run through the SAME immutable configuration first.
            _ = MetamorphicSurfaces.TryObserve(MetamorphicExecutor.IsolationProbeSource, executionProfile, options, true, out _, out _);
        }

        var fixture = profile.NewFixture();
        MetamorphicOperationalObservation? observation = null;
        var ran = false;
        var reason = "ok";
        var cancelled = false;
        string? harness = null;
        try
        {
            ran = MetamorphicSurfaces.TryObserve(source, executionProfile, options, collectEvidence: true, fixture, out var observed, out reason);
            observation = ran ? observed : null;
        }
        catch (OperationCanceledException)
        {
            // Only a fixture-scheduled cancellation is a language-level cancellation outcome.
            cancelled = true;
            if (!fixture.CancellationRequested) harness = "unscheduled cancellation";
        }
        catch (MetamorphicWatchdogException exception)
        {
            harness = "watchdog: " + exception.Message;
        }
        catch (MetamorphicHarnessException exception)
        {
            harness = exception.Message;
        }

        return new SemanticProfileRun(
            profile.Id, member, ran, reason, observation, [.. fixture.Events], fixture.WaitCalls,
            fixture.SuspensionsWitnessed, fixture.FirstSuspensionReturnedControl, cancelled, harness);
    }

    // ── Anchors ─────────────────────────────────────────────────────────────

    private static void CheckAnchors(
        SemanticCase semanticCase, SemanticProfile profile, SemanticProfileRun run, List<(SemanticVerdict, string)> findings)
    {
        var where = $"{run.Member}@{profile.Id}";
        var expected = semanticCase.Expected;
        if (run.HarnessProblem is { } problem)
        {
            findings.Add((SemanticVerdict.HarnessFailure, $"{where}: {problem}"));
            return;
        }

        var definition = profile.Definition;
        if (run.Ran && run.Observation is null)
        {
            findings.Add((SemanticVerdict.MissingObservation, $"{where}: the surface returned no observation"));
            return;
        }

        if (run.Observation is { } declared
            && (declared.Facets != definition.Facets || declared.Surface != definition.Id))
        {
            findings.Add((SemanticVerdict.MissingObservation,
                $"{where}: observation does not carry the declared surface and required facets ({definition.Id}: {definition.Facets})"));
            return;
        }

        if (semanticCase.Kind == SemanticCaseKind.InvalidFrontEnd)
        {
            if (definition.RequiresParsableSource)
            {
                if (run.Ran || run.Reason != "parse-error")
                    findings.Add((SemanticVerdict.FrontEndExpectation, $"{where}: an invalid source reached the evaluator ({run.OutcomeText})"));
            }
            else if (run.Observation is not { } rejected
                     || rejected.Semantic.Outcome != "err"
                     || rejected.FailureStage != MetamorphicOperationalObservation.FrontEndFailureStage)
            {
                findings.Add((SemanticVerdict.FrontEndExpectation, $"{where}: expected a front-end failure, observed {run.OutcomeText} stage={run.Observation?.FailureStage ?? "-"}"));
            }

            if (!run.Events.IsEmpty)
                findings.Add((SemanticVerdict.Mismatch, $"{where}: host effects ran for a front-end-rejected program"));
            return;
        }

        if (profile.IsCancellation)
        {
            if (!run.Cancelled)
                findings.Add((SemanticVerdict.Mismatch, $"{where}: expected a scheduled cancellation, observed {run.OutcomeText}"));
            if (!run.Events.SequenceEqual(expected.CancelledEventsPrefix))
                findings.Add((SemanticVerdict.Mismatch, $"{where}: events [{string.Join(",", run.Events)}], expected exactly [{string.Join(",", expected.CancelledEventsPrefix)}] before cancellation"));
            return;
        }

        if (run.Cancelled)
        {
            findings.Add((SemanticVerdict.Mismatch, $"{where}: an unscheduled cancellation"));
            return;
        }

        if (!run.Ran)
        {
            findings.Add((SemanticVerdict.FrontEndUnexpected, $"{where}: the surface refused the valid source ({run.Reason})"));
            return;
        }

        var observation = run.Observation!;
        var semantic = observation.Semantic;
        var facets = observation.Facets;
        if (semantic.IsResourceLimit)
        {
            findings.Add((SemanticVerdict.ResourceTermination, $"{where}: stopped at a resource limit ({semantic.ErrorCategory})"));
            return;
        }

        if (semanticCase.Kind == SemanticCaseKind.ValidSuccess)
        {
            if (semantic.Outcome != "ok")
            {
                findings.Add((SemanticVerdict.Mismatch,
                    $"{where}: expected success, observed {semantic} stage={observation.FailureStage ?? "-"}"));
            }
            else
            {
                if (facets.HasFlag(MetamorphicFacets.Structure))
                {
                    if (semantic.Value is null && semantic.StructuralIdentity is null)
                    {
                        findings.Add((SemanticVerdict.MissingObservation, $"{where}: the structure facet carries no value"));
                    }
                    else
                    {
                        var anchor = MetamorphicSemanticObservation.OfValue(expected.Value!, expected.EmittedCount);
                        if (!MetamorphicComparator.StructurallyEqual(anchor, semantic))
                        {
                            findings.Add((SemanticVerdict.Mismatch,
                                $"{where}: value {MetamorphicStructuralIdentity.Preview(semantic.StructuralIdentity)} != constructed {MetamorphicStructuralIdentity.Preview(expected.ValueIdentity)}"));
                        }
                    }
                }

                if (facets.HasFlag(MetamorphicFacets.EmittedCount))
                {
                    if (semantic.EmittedCount is not { } count)
                        findings.Add((SemanticVerdict.MissingObservation, $"{where}: the emitted-count facet is empty"));
                    else if (count != expected.EmittedCount)
                        findings.Add((SemanticVerdict.Mismatch, $"{where}: emitted count {count} != constructed {expected.EmittedCount}"));
                }
            }
        }
        else
        {
            if (semantic.Outcome != "err")
            {
                findings.Add((SemanticVerdict.Mismatch, $"{where}: expected runtime failure {expected.ErrorCategory}, observed {semantic}"));
            }
            else
            {
                if (facets.HasFlag(MetamorphicFacets.StructuredError))
                {
                    if (semantic.ErrorCategory is null || semantic.ErrorDetail is null)
                        findings.Add((SemanticVerdict.MissingObservation, $"{where}: the structured-error facet is empty"));
                    else if (semantic.ErrorCategory != expected.ErrorCategory)
                        findings.Add((SemanticVerdict.Mismatch, $"{where}: error {semantic.ErrorCategory} != constructed {expected.ErrorCategory}"));
                }

                if (definition.UsesFrontEndPipeline && observation.FailureStage != MetamorphicOperationalObservation.EvaluationFailureStage)
                    findings.Add((SemanticVerdict.Mismatch, $"{where}: failure stage {observation.FailureStage ?? "-"}, expected evaluation"));
            }
        }

        if (!run.Events.SequenceEqual(expected.Events))
        {
            findings.Add((SemanticVerdict.Mismatch,
                $"{where}: host events [{string.Join(",", run.Events)}] != constructed [{string.Join(",", expected.Events)}]"));
        }
    }

    // ── Paths ───────────────────────────────────────────────────────────────

    private static readonly MetamorphicSideEvidence OptimizedLoopEvidence = new(
        RequiredPaths: MetamorphicOptimizerPath.OptimizedLoopSelected | MetamorphicOptimizerPath.PlannedExpressionExecuted,
        ForbiddenPaths: MetamorphicOptimizerPath.LoopFallbackExecuted);

    private static readonly MetamorphicSideEvidence GenericLoopEvidence = new(
        RequiredPaths: MetamorphicOptimizerPath.GenericLoopExecuted,
        ForbiddenPaths: MetamorphicOptimizerPath.OptimizedLoopSelected);

    private static readonly MetamorphicSideEvidence ShortCircuitEvidence = new(
        RequiredPaths: MetamorphicOptimizerPath.LoopShortCircuited,
        ForbiddenPaths: MetamorphicOptimizerPath.OptimizedLoopSelected | MetamorphicOptimizerPath.LoopFallbackExecuted);

    private static readonly MetamorphicSideEvidence FallbackEvidence = new(
        RequiredPaths: MetamorphicOptimizerPath.LoopFallbackExecuted | MetamorphicOptimizerPath.GenericLoopExecuted,
        ForbiddenPaths: MetamorphicOptimizerPath.OptimizedLoopSelected);

    private static readonly MetamorphicSideEvidence GenericInsideEvidence = new(
        RequiredPaths: MetamorphicOptimizerPath.OptimizedLoopSelected | MetamorphicOptimizerPath.GenericExpressionInsideOptimizedLoop);

    private static SemanticPath JudgePaths(
        SemanticCase semanticCase, IReadOnlyDictionary<string, SemanticProfileRun> runs, List<string> rejections)
    {
        var claimed = semanticCase.Paths;
        var exercised = SemanticPath.None;

        bool Evidence(SemanticPath path, string profile, MetamorphicSideEvidence evidence)
        {
            if (!runs.TryGetValue(profile, out var run) || run.Observation is not { } observation)
            {
                rejections.Add($"{path}: {profile} not observed");
                return false;
            }

            if (evidence.Unsatisfied(observation, profile) is { } reason)
            {
                rejections.Add($"{path}: {reason} ({observation.OptimizerEvidence?.Feature ?? "no-evidence"}, cache {observation.CacheEvidence?.Feature ?? "-"})");
                return false;
            }

            return true;
        }

        void Claim(SemanticPath path, params (string Profile, MetamorphicSideEvidence Evidence)[] requirements)
        {
            if (!claimed.HasFlag(path)) return;
            var ok = true;
            foreach (var (profile, evidence) in requirements) ok &= Evidence(path, profile, evidence);
            if (ok) exercised |= path;
        }

        Claim(SemanticPath.OptimizedLoop,
            (SemanticProfiles.SyncOptimized, OptimizedLoopEvidence), (SemanticProfiles.SyncGeneric, GenericLoopEvidence));
        Claim(SemanticPath.LoopShortCircuit,
            (SemanticProfiles.SyncOptimized, ShortCircuitEvidence), (SemanticProfiles.SyncGeneric, ShortCircuitEvidence));
        Claim(SemanticPath.LoopFallback,
            (SemanticProfiles.SyncOptimized, FallbackEvidence), (SemanticProfiles.SyncGeneric, GenericLoopEvidence));
        Claim(SemanticPath.GenericInsideOptimizedLoop, (SemanticProfiles.SyncOptimized, GenericInsideEvidence));

        if (semanticCase.MinimumCacheHits > 0)
        {
            var cache = new MetamorphicSideEvidence(MinimumCacheHits: semanticCase.MinimumCacheHits);
            Claim(SemanticPath.CacheHit, (SemanticProfiles.SyncOptimized, cache), (SemanticProfiles.SyncGeneric, cache));
        }

        if (claimed.HasFlag(SemanticPath.AsyncSuspension))
        {
            var expectedWaits = semanticCase.ExpectedWaitCalls;
            var gatedRuns = runs.Values.Where(r => SemanticProfiles.Get(r.Profile) is { GatedHost: true, IsCancellation: false }).ToList();
            var ok = expectedWaits > 0 && gatedRuns.Count > 0;
            if (!ok) rejections.Add("AsyncSuspension: no demanded wait or non-cancellation asynchronous profile");
            foreach (var run in gatedRuns)
            {
                if (run.WaitCalls != expectedWaits || run.Suspensions != expectedWaits || !run.FirstSuspensionReturnedControl)
                {
                    rejections.Add($"AsyncSuspension: {run.Profile} witnessed {run.Suspensions}/{run.WaitCalls} suspensions of {expectedWaits} waits (first returned control: {run.FirstSuspensionReturnedControl})");
                    ok = false;
                }
            }

            if (ok) exercised |= SemanticPath.AsyncSuspension;
        }

        if (claimed.HasFlag(SemanticPath.Cancellation))
        {
            var cancelRuns = runs.Values.Where(r => SemanticProfiles.Get(r.Profile).IsCancellation).ToList();
            if (cancelRuns.Count > 0 && cancelRuns.All(r => r.Cancelled && r.Suspensions >= 1))
                exercised |= SemanticPath.Cancellation;
            else
                rejections.Add("Cancellation: no cancellation profile reached its scheduled suspension");
        }

        // Anchor-backed paths are exercised exactly when the exact anchors hold (judged by the caller).
        exercised |= claimed & ~SemanticPath.EvidenceBacked;
        return exercised;
    }

    private static string Preview(string text)
    {
        var line = text.Split('\n')[0];
        return line.Length <= 160 ? line : line[..160] + "…";
    }

    internal static string Describe(SemanticProfileRun run)
    {
        var o = run.Observation;
        return string.Create(CultureInfo.InvariantCulture,
            $"{run.Member}@{run.Profile}: {run.OutcomeText} {(o is null ? "" : o.Semantic.ToString())} events=[{string.Join(",", run.Events)}] waits={run.WaitCalls} suspensions={run.Suspensions} optimizer={o?.OptimizerEvidence?.Feature ?? "-"} cache={o?.CacheEvidence?.Feature ?? "-"}");
    }
}
