using KatLang.ParserFuzz;

namespace KatLang.Tests.SemanticTesting;

/// <summary>
/// SEM-2B apparatus checks: the harness must REJECT wrong, uniformly wrong, incomplete or
/// unproven observations, keep its verdict classes apart, and give every execution fresh state.
/// Synthetic observations enter only through <see cref="SemanticRunner.Run"/>'s inert test seam,
/// AFTER a real execution and BEFORE judgement. This is a focused apparatus check, not a mutation
/// campaign.
/// </summary>
public class SemanticHarnessApparatusTests
{
    private static SemanticCase Find(Func<SemanticCase, bool> predicate, string what)
        => SemanticGrammarCorpusTests.Cases.FirstOrDefault(predicate)
            ?? throw new InvalidOperationException("the fixed corpus has no case with " + what);

    private static SemanticCase SuccessWithEffects => Find(
        c => c.Kind == SemanticCaseKind.ValidSuccess && c.Profiles.Contains(SemanticProfiles.EngineRun) && !c.Expected.Events.IsEmpty,
        "a successful engine-profiled case with host events");

    private static SemanticCase RuntimeFailure => Find(c => c.Kind == SemanticCaseKind.ValidRuntimeFailure, "a runtime failure");

    private static SemanticCase WithPath(SemanticPath path) => Find(c => c.Paths.HasFlag(path) && c.Kind != SemanticCaseKind.InvalidFrontEnd, path.ToString());

    private static Func<SemanticProfileRun, SemanticProfileRun> WithSemantic(Func<SemanticProfileRun, bool> when, Func<MetamorphicSemanticObservation, MetamorphicSemanticObservation> change)
        => run => when(run) && run.Observation is { } o ? run with { Observation = o with { Semantic = change(o.Semantic) } } : run;

    [Fact]
    public void Baseline_TheChosenCasesPassUnfiltered()
    {
        Assert.True(SemanticRunner.Run(SuccessWithEffects).Passed);
        Assert.True(SemanticRunner.Run(RuntimeFailure).Passed);
    }

    [Fact]
    public void WrongValueOnOneProfile_IsAnAnchorAndParityMismatch()
    {
        var semanticCase = SuccessWithEffects;
        var result = SemanticRunner.Run(semanticCase, WithSemantic(
            r => r.Profile == SemanticProfiles.SyncOptimized && r.Member == SemanticMember.BaseRole,
            s => MetamorphicSemanticObservation.OfValue(new Result.Atom(123456), s.EmittedCount)));

        Assert.Equal(SemanticVerdict.Mismatch, result.Verdict);
        Assert.Contains(result.Findings, f => f.StartsWith("base@sync-optimized: value", StringComparison.Ordinal));
        Assert.Contains(result.Findings, f => f.StartsWith("parity:sync-generic~sync-optimized", StringComparison.Ordinal));
        Assert.Equal(SemanticPath.None, result.PathsExercised);
    }

    /// <summary>
    /// Every profile and member agreeing on the SAME wrong result passes every parity and relation —
    /// and is still caught, on every structure-projecting run, by the constructed anchor.
    /// </summary>
    [Fact]
    public void UniformlyWrongImplementation_IsCaughtByTheIndependentAnchor()
    {
        var semanticCase = SuccessWithEffects;
        var result = SemanticRunner.Run(semanticCase, WithSemantic(_ => true,
            s => MetamorphicSemanticObservation.OfValue(new Result.Atom(424242), s.EmittedCount)));

        Assert.Equal(SemanticVerdict.Mismatch, result.Verdict);
        Assert.DoesNotContain(result.Findings, f => f.StartsWith("parity:", StringComparison.Ordinal) || f.StartsWith("relation:", StringComparison.Ordinal));
        var flagged = result.Findings.Count(f => f.Contains(": value ", StringComparison.Ordinal));
        var structural = result.Runs.Count(r => r.Observation?.Facets.HasFlag(MetamorphicFacets.Structure) == true);
        Assert.Equal(structural, flagged);
    }

    /// <summary>An effect the construction says never happens (eager evaluation of a lazily transported cell) fails.</summary>
    [Fact]
    public void AnUnexpectedOrMissingHostEvent_IsAMismatch()
    {
        var lazy = WithPath(SemanticPath.LazyTransport);
        var eager = SemanticRunner.Run(lazy, r => r.Profile == SemanticProfiles.SyncGeneric ? r with { Events = [.. r.Events, "trace:99"] } : r);
        Assert.Equal(SemanticVerdict.Mismatch, eager.Verdict);
        Assert.Contains(eager.Findings, f => f.Contains("host events", StringComparison.Ordinal));
        Assert.False(eager.PathsExercised.HasFlag(SemanticPath.LazyTransport));

        var dead = WithPath(SemanticPath.DeadComputationUntouched);
        var touched = SemanticRunner.Run(dead, r => r.Profile == SemanticProfiles.AsyncTwin ? r with { Events = [.. r.Events, "trace:666"] } : r);
        Assert.Equal(SemanticVerdict.Mismatch, touched.Verdict);

        var stops = WithPath(SemanticPath.FirstFailureStops);
        var missing = SemanticRunner.Run(stops, r => r.Profile == SemanticProfiles.SyncOptimized && r.Member == SemanticMember.BaseRole ? r with { Events = [] } : r);
        Assert.Equal(SemanticVerdict.Mismatch, missing.Verdict);
    }

    /// <summary>Two absent fields are never evidence of equality.</summary>
    [Fact]
    public void AbsentStructureOrErrorDetail_IsAMissingObservation()
    {
        var noValue = SemanticRunner.Run(SuccessWithEffects, WithSemantic(_ => true,
            s => new MetamorphicSemanticObservation("ok", null, s.EmittedCount, null, null, false)));
        Assert.Equal(SemanticVerdict.MissingObservation, noValue.Verdict);
        Assert.Contains(noValue.Findings, f => f.Contains("carries no value", StringComparison.Ordinal));

        var noCount = SemanticRunner.Run(SuccessWithEffects, WithSemantic(r => r.Profile == SemanticProfiles.SyncGeneric,
            s => s with { EmittedCount = null }));
        Assert.Equal(SemanticVerdict.MissingObservation, noCount.Verdict);

        var failure = RuntimeFailure;
        var noDetail = SemanticRunner.Run(failure, WithSemantic(_ => true,
            s => MetamorphicSemanticObservation.Failure(s.ErrorCategory ?? "x", null, false)));
        Assert.Equal(SemanticVerdict.MissingObservation, noDetail.Verdict);
    }

    [Fact]
    public void MissingFacetFlagsSurfaceOrObservation_CannotEraseTheDeclaredContract()
    {
        foreach (var defect in new[] { "facets", "surface", "observation" })
        {
            var result = SemanticRunner.Run(SuccessWithEffects, run => run.Observation is { } o
                ? run with { Observation = defect switch
                {
                    "facets" => o with { Facets = MetamorphicFacets.Outcome },
                    "surface" => o with { Surface = "wrong-surface" },
                    _ => null,
                } }
                : run);
            Assert.Equal(SemanticVerdict.MissingObservation, result.Verdict);
            Assert.False(result.Passed);
        }
        Assert.Equal(SemanticVerdict.HarnessFailure,
            SemanticRunner.Run(SuccessWithEffects with { Profiles = [] }).Verdict);
    }

    [Fact]
    public void WrongErrorKindOrFailureStage_IsAMismatch()
    {
        var failure = RuntimeFailure;
        var wrongKind = SemanticRunner.Run(failure, WithSemantic(r => r.Profile == SemanticProfiles.AsyncTwin,
            s => s with { ErrorCategory = "NotTheConstructedKind" }));
        Assert.Equal(SemanticVerdict.Mismatch, wrongKind.Verdict);
        Assert.Contains(wrongKind.Findings, f => f.Contains("!= constructed", StringComparison.Ordinal));

        // An engine run of a VALID source that fails in the front end is not a runtime failure.
        var engineFailure = Find(c => c.Kind == SemanticCaseKind.ValidRuntimeFailure && c.Profiles.Contains(SemanticProfiles.EngineRun), "an engine-profiled runtime failure");
        var wrongStage = SemanticRunner.Run(engineFailure, r => r.Profile == SemanticProfiles.EngineRun && r.Observation is { } o
            ? r with { Observation = o with { FailureStage = MetamorphicOperationalObservation.FrontEndFailureStage } }
            : r);
        Assert.Equal(SemanticVerdict.Mismatch, wrongStage.Verdict);
        Assert.Contains(wrongStage.Findings, f => f.Contains("expected evaluation", StringComparison.Ordinal));
    }

    [Fact]
    public void FrontEndProblems_AreTheirOwnVerdicts()
    {
        var valid = SuccessWithEffects;
        var broken = valid with { Members = [new SemanticMember(SemanticMember.BaseRole, "v1 = (\n997")] };
        Assert.Equal(SemanticVerdict.FrontEndUnexpected, SemanticRunner.Run(broken).Verdict);

        var invalid = Find(c => c.Kind == SemanticCaseKind.InvalidFrontEnd && c.Expected.DiagnosticPhase == SemanticExpectation.SyntaxPhase, "a syntax-phase invalid case");
        Assert.True(SemanticRunner.Run(invalid).Passed);
        var wrongCode = invalid with { Expected = invalid.Expected with { Diagnostic = DiagnosticCode.LoadCycle } };
        Assert.Equal(SemanticVerdict.FrontEndExpectation, SemanticRunner.Run(wrongCode).Verdict);
        var wrongPhase = invalid with { Expected = invalid.Expected with { DiagnosticPhase = SemanticExpectation.ElaborationPhase } };
        Assert.Equal(SemanticVerdict.FrontEndExpectation, SemanticRunner.Run(wrongPhase).Verdict);
        var accepted = invalid with { Members = [new SemanticMember(SemanticMember.BaseRole, "1\n997")] };
        Assert.Equal(SemanticVerdict.FrontEndExpectation, SemanticRunner.Run(accepted).Verdict);
    }

    /// <summary>Missing or contradicting evidence makes the path claim REJECTED — never exercised.</summary>
    [Fact]
    public void MissingOrWrongPathEvidence_IsARejectedClaim_NeverAPass()
    {
        var loop = WithPath(SemanticPath.OptimizedLoop);
        Assert.True(SemanticRunner.Run(loop).PathsExercised.HasFlag(SemanticPath.OptimizedLoop));

        var unavailable = SemanticRunner.Run(loop, r => r.Profile == SemanticProfiles.SyncOptimized && r.Observation is { } o
            ? r with { Observation = o with { OptimizerEvidence = null } }
            : r);
        Assert.False(unavailable.PathsExercised.HasFlag(SemanticPath.OptimizedLoop));
        Assert.Equal(SemanticVerdict.MissingObservation, unavailable.Verdict);
        Assert.Contains(unavailable.PathRejections, p => p.Contains("optimizer-evidence-unavailable", StringComparison.Ordinal));

        var generic = SemanticRunner.Run(loop, r => r.Profile == SemanticProfiles.SyncOptimized && r.Observation is { } o
            ? r with { Observation = o with { OptimizerEvidence = MetamorphicOptimizerEvidence.Unobserved } }
            : r);
        Assert.False(generic.PathsExercised.HasFlag(SemanticPath.OptimizedLoop));
        Assert.Contains(generic.PathRejections, p => p.Contains("path-not-exercised", StringComparison.Ordinal));

        var cached = WithPath(SemanticPath.CacheHit);
        var noHits = SemanticRunner.Run(cached, r => r.Observation is { CacheEvidence: { } c } o
            ? r with { Observation = o with { CacheEvidence = c with { Hits = 0 } } }
            : r);
        Assert.False(noHits.PathsExercised.HasFlag(SemanticPath.CacheHit));
        Assert.Contains(noHits.PathRejections, p => p.Contains("cache-reuse-not-observed", StringComparison.Ordinal));

        var waits = WithPath(SemanticPath.AsyncSuspension);
        var noSuspension = SemanticRunner.Run(waits, r => r with { Suspensions = 0 });
        Assert.False(noSuspension.PathsExercised.HasFlag(SemanticPath.AsyncSuspension));
        Assert.Contains(noSuspension.PathRejections, p => p.StartsWith("AsyncSuspension", StringComparison.Ordinal));

        var noWait = Find(c => c.Kind == SemanticCaseKind.ValidSuccess && c.ExpectedWaitCalls == 0, "no demanded waits");
        var vacuous = SemanticRunner.Run(noWait with
        {
            Paths = SemanticPath.AsyncSuspension,
        });
        Assert.False(vacuous.PathsExercised.HasFlag(SemanticPath.AsyncSuspension));
        Assert.Equal(SemanticVerdict.MissingObservation, vacuous.Verdict);
    }

    [Fact]
    public void WhileConditionFirst_HasIndependentTransitionAndFailureAnchors()
    {
        var guards = SemanticGrammarCorpusTests.Cases.Where(c => c.Features.Contains("condition-first")).ToList();
        Assert.Equal(3, guards.Count);
        foreach (var guard in guards)
        {
            var result = SemanticRunner.Run(guard);
            Assert.True(result.Passed, SemanticGrammarCorpusTests.Report(guard, result));
        }
        Assert.Contains(guards, c => c.Kind == SemanticCaseKind.ValidRuntimeFailure && c.Expected.ErrorCategory == "TypeMismatch" && c.Expected.Events.IsEmpty);
        Assert.Contains(guards, c => c.Expected.Events.SequenceEqual(["wait:1", "wait:2"]));
    }

    [Fact]
    public void NestedPatterns_ExerciseBothKindsCollectorsAndRequiredInnerFailure()
    {
        var cases = SemanticGrammarCorpusTests.Cases.Where(c => c.Features.Contains("nested-pattern")).ToList();
        Assert.Equal(11, cases.Count);
        Assert.Contains(cases, c => c.Kind == SemanticCaseKind.ValidRuntimeFailure && c.Expected.ErrorCategory == "TypeMismatch");
        Assert.Contains(cases, c => c.CaseId.Contains("seed-nested/", StringComparison.Ordinal));
        foreach (var semanticCase in cases)
        {
            var result = SemanticRunner.Run(semanticCase);
            Assert.True(result.Passed, SemanticGrammarCorpusTests.Report(semanticCase, result));
        }
    }

    /// <summary>
    /// Optimized loop, generic loop, consulted-and-declined fallback, zero-iteration short circuit,
    /// generic expression inside an optimized loop, an actual cache hit and repeated equal output are
    /// distinct evidence — read from real runs.
    /// </summary>
    [Fact]
    public void OptimizerFallbackShortCircuitAndCacheEvidence_AreNotConflated()
    {
        MetamorphicOptimizerPath Paths(SemanticCase c, string profile)
            => SemanticRunner.Execute(c.Source, SemanticProfiles.Get(profile), SemanticMember.BaseRole).Observation!.OptimizerEvidence!.Paths;

        var optimized = Find(c => c.Paths == SemanticPath.OptimizedLoop && c.Features.Contains("repeat"), "a planned repeat");
        var o = Paths(optimized, SemanticProfiles.SyncOptimized);
        Assert.True(o.HasFlag(MetamorphicOptimizerPath.OptimizedLoopSelected) && o.HasFlag(MetamorphicOptimizerPath.PlannedExpressionExecuted));
        Assert.False(o.HasFlag(MetamorphicOptimizerPath.LoopShortCircuited) || o.HasFlag(MetamorphicOptimizerPath.GenericLoopExecuted));
        var g = Paths(optimized, SemanticProfiles.SyncGeneric);
        Assert.True(g.HasFlag(MetamorphicOptimizerPath.GenericLoopExecuted));
        Assert.False(g.HasFlag(MetamorphicOptimizerPath.OptimizedLoopSelected));

        var zero = Find(c => c.Paths.HasFlag(SemanticPath.LoopShortCircuit), "a zero-iteration repeat");
        var z = Paths(zero, SemanticProfiles.SyncOptimized);
        Assert.True(z.HasFlag(MetamorphicOptimizerPath.LoopShortCircuited));
        Assert.False(z.HasFlag(MetamorphicOptimizerPath.OptimizedLoopSelected) || z.HasFlag(MetamorphicOptimizerPath.LoopFallbackExecuted)
            || z.HasFlag(MetamorphicOptimizerPath.GenericLoopExecuted));

        var declined = Find(c => c.Paths.HasFlag(SemanticPath.LoopFallback), "a declined step");
        var d = Paths(declined, SemanticProfiles.SyncOptimized);
        Assert.True(d.HasFlag(MetamorphicOptimizerPath.LoopFallbackExecuted) && d.HasFlag(MetamorphicOptimizerPath.GenericLoopExecuted));
        Assert.False(d.HasFlag(MetamorphicOptimizerPath.OptimizedLoopSelected));

        var inside = Find(c => c.Paths.HasFlag(SemanticPath.GenericInsideOptimizedLoop), "a host call inside a planned loop");
        var i = Paths(inside, SemanticProfiles.SyncOptimized);
        Assert.True(i.HasFlag(MetamorphicOptimizerPath.OptimizedLoopSelected) && i.HasFlag(MetamorphicOptimizerPath.GenericExpressionInsideOptimizedLoop));

        // A real hit against repeated equal output: [a, a] both times, different evidence and effects.
        static bool Alone(SemanticCase c, params string[] orders)
            => c.Families.SequenceEqual(["cache"]) && c.Kind == SemanticCaseKind.ValidSuccess
                && !c.Features.Any(f => f.StartsWith("ctx-", StringComparison.Ordinal)) && orders.Any(c.Features.Contains);
        var hit = Find(c => Alone(c, "cache-order-0", "cache-order-3"), "a lone cached read pair");
        var fresh = Find(c => Alone(c, "cache-order-1", "cache-order-2"), "a lone fresh-invocation pair");
        var hitRun = SemanticRunner.Execute(hit.Source, SemanticProfiles.Get(SemanticProfiles.SyncOptimized), SemanticMember.BaseRole);
        var freshRun = SemanticRunner.Execute(fresh.Source, SemanticProfiles.Get(SemanticProfiles.SyncOptimized), SemanticMember.BaseRole);
        Assert.True(hitRun.Observation!.CacheEvidence!.Hits >= 1);
        Assert.Single(hitRun.Events);
        Assert.Equal(0, freshRun.Observation!.CacheEvidence!.Hits);
        Assert.Equal(2, freshRun.Events.Length);
        Assert.False(fresh.Paths.HasFlag(SemanticPath.CacheHit));
    }

    /// <summary>
    /// The async profile is witnessed suspension, not an async API call: the same source through the
    /// same asynchronous surface with a SYNCHRONOUS host completes without a single witness.
    /// </summary>
    [Fact]
    public void GenuineSuspensionIsWitnessed_AndAnAsyncCallThatCompletesSynchronouslyIsNot()
    {
        var waits = WithPath(SemanticPath.AsyncSuspension);
        var gated = SemanticRunner.Execute(waits.Source, SemanticProfiles.Get(SemanticProfiles.AsyncTwin), SemanticMember.BaseRole);
        Assert.True(gated.WaitCalls >= 1);
        Assert.Equal(gated.WaitCalls, gated.Suspensions);
        Assert.True(gated.FirstSuspensionReturnedControl);
        Assert.Equal("evaluator-run-counted-observed-async", gated.Observation!.Surface);
        Assert.Equal("twin", gated.Observation.OptimizerPolicy);

        var profile = SemanticProfiles.Get(SemanticProfiles.AsyncTwin).ExecutionProfile;
        var synchronousHost = MetamorphicHostFixture.Synchronous();
        Assert.True(MetamorphicSurfaces.TryObserve(waits.Source, profile, MetamorphicExecutor.OptionsFor(profile), true, synchronousHost, out var observation, out _));
        Assert.Equal(0, synchronousHost.SuspensionsWitnessed);
        Assert.Equal(gated.Events.ToArray(), synchronousHost.Events.ToArray());
        Assert.Equal(gated.Observation.Semantic, observation.Semantic);

        // A gated host on a synchronous surface is refused, never silently run synchronously.
        var sync = SemanticProfiles.Get(SemanticProfiles.SyncOptimized).ExecutionProfile;
        Assert.Throws<MetamorphicHarnessException>(() => MetamorphicSurfaces.TryObserve(
            waits.Source, sync, MetamorphicExecutor.OptionsFor(sync), true, MetamorphicHostFixture.Gated(), out _, out _));
    }

    [Fact]
    public void EveryProfileAdapter_RoutesToItsDeclaredSurface()
    {
        var semanticCase = SuccessWithEffects;
        foreach (var profile in SemanticProfiles.All.Where(p => !p.IsCancellation))
        {
            var run = SemanticRunner.Execute(semanticCase.Source, profile, SemanticMember.BaseRole);
            Assert.True(run.Ran, profile.Id);
            var observation = run.Observation!;
            Assert.Equal(profile.Definition.Id, observation.Surface);
            Assert.Equal(profile.Definition.Facets, observation.Facets);
            Assert.Equal(semanticCase.Expected.Events.ToArray(), run.Events.ToArray());
            if (profile.Definition.SupportsOptimizerPolicy)
                Assert.Equal(profile.EnableOptimizations ? "on" : "off", observation.OptimizerPolicy);
            if (profile.Definition.UsesFrontEndPipeline)
                Assert.Null(observation.FailureStage);
            Assert.Equal(profile.GatedHost && semanticCase.ExpectedWaitCalls > 0, run.Suspensions > 0);
        }
    }

    /// <summary>
    /// Fresh execution: a cancelled run leaves nothing behind for the next run of the same source,
    /// a run's property cache and host events are its own, and repeated runs observe identically.
    /// </summary>
    [Fact]
    public void FreshExecution_InheritsNoEffectsCachesOrCancellation()
    {
        var cancel = WithPath(SemanticPath.Cancellation);
        var cancelled = SemanticRunner.Execute(cancel.Source, SemanticProfiles.Get(SemanticProfiles.AsyncTwinCancel), SemanticMember.BaseRole);
        Assert.True(cancelled.Cancelled);
        Assert.Equal(cancel.Expected.CancelledEventsPrefix.ToArray(), cancelled.Events.ToArray());
        var after = SemanticRunner.Execute(cancel.Source, SemanticProfiles.Get(SemanticProfiles.AsyncTwin), SemanticMember.BaseRole);
        Assert.False(after.Cancelled);
        Assert.Equal(cancel.Expected.Events.ToArray(), after.Events.ToArray());

        var cached = WithPath(SemanticPath.CacheHit);
        var profile = SemanticProfiles.Get(SemanticProfiles.SyncOptimized);
        var first = SemanticRunner.Execute(cached.Source, profile, SemanticMember.BaseRole);
        var second = SemanticRunner.Execute(cached.Source, profile, SemanticMember.BaseRole);
        Assert.Equal(first.Observation, second.Observation); // counters, cache evidence and value included
        Assert.Equal(first.Events.ToArray(), second.Events.ToArray());
        Assert.True(first.Observation!.CacheEvidence!.Misses >= 1); // the second run started cold
    }

    /// <summary>A watchdog expiry is a harness bound, never a semantic outcome; it is not a timing trigger.</summary>
    [Fact]
    public void AsyncWatchdog_IsAHarnessBound()
    {
        var fixture = MetamorphicHostFixture.Gated();
        Assert.Throws<MetamorphicWatchdogException>(() =>
            fixture.Drive(_ => new TaskCompletionSource<int>().Task, TimeSpan.FromMilliseconds(300)));
        Assert.Throws<MetamorphicHarnessException>(() =>
            MetamorphicHostFixture.Synchronous().Drive(_ => Task.FromResult(1), TimeSpan.FromSeconds(1)));
    }
}
