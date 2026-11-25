using System.Globalization;
using System.Text;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using static KatLang.Tests.PlannedLoopTempFamily;

namespace KatLang.Tests;

/// <summary>
/// The planned-loop temporary generator family (<see cref="PlannedLoopTempFamily"/>; KL-06 F01
/// follow-up, owner decision Option A of November 21 2026): 36 generated <c>repeat</c> and
/// <c>while</c> steps, each with a planned local-only temp, a <c>tick()</c> fallback temp, an exported
/// self-contained temp and an undemanded temp, checked against expectations the generator constructs
/// from the approved rule.
///
/// <para><b>What the approved route policy compares</b> (every case):</para>
/// <list type="bullet">
/// <item>the neutral observation (value and root emitted count) against the constructed one on the
/// generic, optimized and genuinely suspending async cache-recording routes, ordinary and with
/// retained invocation plans (<see cref="InvocationPlanTestSeam"/>), and the value on the six
/// established routes of <see cref="SixRouteAgreement"/> (both engines, the engine's async twin,
/// generic, optimized and the forced twin), whose host-call log stays empty. A second run on those
/// six routes appends a final <c>tick()</c> to expose the tick count through the result;</item>
/// <item>the publications per binding name of the generic and the optimized route, with each other
/// (the observer's requirement) and with the constructed count of all four temps (a name at zero is
/// watched), and the async route's total;</item>
/// <item>the <c>tick()</c> count (the run budget's) on the generic, optimized and async routes, with
/// the constructed count;</item>
/// <item>Lean on the whole family, which is all inside the shared domain (the counter is language
/// state, the cache is modeled): the neutral observation, the publications per name and in total,
/// and the tick count, each guarded at the constructed value
/// (<c>lean/CoreTests/PlannedLoopTempFamily.lean</c>).</item>
/// </list>
/// <para><b>Route-specific observations</b>, never compared with Lean: which storage established an
/// entry (frame slots on the optimized route, constructed: the planned path's <c>T</c> and <c>K</c>,
/// nothing on the fallback path) and the run cache's own store count; the planner's path (its
/// per-temp and per-row plans, read from the optimized run's own diagnostics); the publication ORDER
/// and the operational counters (steps, checkpoints, peak depth, materialized items), compared
/// between generic and optimized and between the ordinary and the plan-retaining pass, never with a
/// constructed value. The async route keeps no per-name or order observation. The public engines
/// expose the final tick through the extra output row and have no cache observer.</para>
/// </summary>
public class PlannedLoopTempFamilyTests
{
    private const string ArtifactPath = "lean/CoreTests/PlannedLoopTempFamily.lean";
    private const string Corpus = "Planned-loop temp family";

    /// <summary>The planner's refusal of the tick temp.</summary>
    private const string TickTempRefusal = "unsupported local property body F: unsupported call: tick";

    /// <summary>The planner's withdrawal of every temp plan once a row runs generically.</summary>
    private const string PartialPlanRefusal = "local properties require the shared generic cache in a partially planned loop";

    public static TheoryData<string> CaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var loopCase in Cases)
            data.Add(loopCase.Id);
        return data;
    }

    private static PlannedLoopTempCase CaseById(string id) => Cases.Single(loopCase => loopCase.Id == id);

    private static Algorithm.User Root(PlannedLoopTempCase loopCase) => SourceProvenance.ParseValid(loopCase.Source).Root;

    /// <summary>
    /// The family's shape: the L9 array once for each loop kind and path, distinct ids and Lean
    /// names, and the four temps declared by every step.
    /// </summary>
    [Fact]
    public void Family_IsTheOrthogonalArrayForEachLoopKindAndPath()
    {
        Assert.Equal(36, Cases.Count);
        Assert.Equal(Cases.Count, Cases.Select(loopCase => loopCase.Id).Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(Cases.Count, Cases.Select(loopCase => loopCase.LeanName).Distinct(StringComparer.Ordinal).Count());

        foreach (var group in Cases.GroupBy(loopCase => (loopCase.Loop, loopCase.Path)))
        {
            Assert.Equal(Grid.Count, group.Count());
            var pairs = new[]
            {
                group.Select(c => (c.Depth, c.Rounds)), group.Select(c => (c.Depth, c.Reuse)), group.Select(c => (c.Rounds, c.Reuse)),
            };
            // Every pair of levels of two factors occurs exactly once: 3 × 3 distinct pairs.
            Assert.All(pairs, pair => Assert.Equal(9, pair.Distinct().Count()));
        }

        // The step is the one property of every enclosing owner: Outer, then Run, then Step.
        Assert.All(Cases, loopCase =>
        {
            var step = Root(loopCase).Properties.Single().Value;
            for (var depth = 0; depth < loopCase.Depth; depth++)
                step = Assert.Single(((Algorithm.User)step).Properties).Value;
            var temps = ((Algorithm.User)step).Properties;
            Assert.Equal(TempNames, temps.Select(property => property.Name));
            Assert.All(temps, temp => Assert.Equal(temp.Name == "K" ? PropertyExposure.Exported
                : PropertyExposure.LocalOnlyCapturedAncestorParameters, temp.Exposure));
        });
    }

    // ── C# routes ──────────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// The constructed result, effects and publications on every applicable C# route, ordinary and
    /// with retained invocation plans; the route-specific storage split, order and counters.
    /// </summary>
    [Theory]
    [MemberData(nameof(CaseIds))]
    public async Task EveryCSharpRoute_MeetsTheConstructedResultEffectsAndPublications(string id)
    {
        var loopCase = CaseById(id);
        var expected = loopCase.Expected;
        var root = Root(loopCase);

        var ordinary = ObserveRoutes(loopCase, root, retainPlans: false);
        var retained = ObserveRoutes(loopCase, root, retainPlans: true);
        foreach (var (pass, routes) in new[] { ("ordinary", ordinary), ("plan-retaining", retained) })
        {
            Assert.True(expected.Publications.Matches(routes.Publications),
                $"'{id}' ({pass}) published [{CachePublicationExpectation.Describe(routes.Publications)}], expected [{expected.Publications}]");
            Assert.True(SameEntries(loopCase.ExpectedFrameSlots, routes.OptimizedFrameSlots),
                $"'{id}' ({pass}) established [{CachePublicationExpectation.Describe(routes.OptimizedFrameSlots)}] in frame slots, expected [{loopCase.ExpectedFrameSlots}]");

            // The effect: one tick per establishment of F, on every cache-recording route.
            Assert.Equal(expected.Ticks, routes.Budgets.Generic.TickCount);
            Assert.Equal(expected.Ticks, routes.Budgets.Optimized.TickCount);
            Assert.Equal(expected.Ticks, routes.AsynchronousBudget.TickCount);

            // Route-specific: the optimized route keeps the generic order and charges.
            Assert.Equal(routes.GenericOrder, routes.OptimizedOrder);
            Assert.Equal(Counters(routes.Budgets.Generic), Counters(routes.Budgets.Optimized));
        }

        // Retaining invocation plans changes no observation.
        Assert.Equal(ordinary.GenericOrder, retained.GenericOrder);
        Assert.Equal(Counters(ordinary.Budgets.Generic), Counters(retained.Budgets.Generic));
        Assert.Equal(Counters(ordinary.Budgets.Optimized), Counters(retained.Budgets.Optimized));
        Assert.Equal(Counters(ordinary.AsynchronousBudget), Counters(retained.AsynchronousBudget));

        // The six established routes: the constructed value, and no host call.
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(loopCase.Source);
        Assert.Equal("ok", oracle.Kind);
        Assert.Equal(RawOf(expected.Neutral), oracle.Value);
        Assert.Empty(oracle.HostCalls);

        // The engines expose no budget. One extra root row reads out the final tick on every route,
        // including a spurious tick after the last state was formed or in an undemanded property.
        var readout = await SixRouteAgreement.OnEveryRouteAsync(loopCase.Source + "\ntick()",
            value => SixRouteAgreement.Neutral(Assert.IsType<Result.SequenceValue>(value).Items[^1]));
        Assert.Equal("ok", readout.Kind);
        Assert.Equal((expected.Ticks + 1).ToString(CultureInfo.InvariantCulture), readout.Value);
        Assert.Empty(readout.HostCalls);

        // Route-specific: the run's own cache stores every publication on the generic route and, on
        // the optimized route, only what the frame slots did not hold.
        var program = new Expr.AlgorithmExpr(root);
        var genericCache = new RunScopedZeroArgPropertyResultCache();
        Evaluator.RunCountedObserved(program, enableOptimizations: false, zeroArgPropertyResultCache: genericCache);
        var optimizedCache = new RunScopedZeroArgPropertyResultCache();
        Evaluator.RunCountedObserved(program, enableOptimizations: true, zeroArgPropertyResultCache: optimizedCache);
        Assert.Equal(expected.Publications.Total, genericCache.PublishedCount);
        Assert.Equal(expected.Publications.Total - loopCase.ExpectedFrameSlots.Total, optimizedCache.PublishedCount);
    }

    /// <summary>
    /// WHICH path the optimized route took, from the planner's diagnostics of the very run whose
    /// publications are observed, ordinary and with retained invocation plans: one plan per loop
    /// activation, never a refused loop; on the planned path every row reads <c>T</c> and <c>K</c>
    /// through planned temp slots; on the fallback path the tick temp's refusal withdraws every temp
    /// plan and the reading rows run generically inside the optimized loop.
    /// </summary>
    [Theory]
    [MemberData(nameof(CaseIds))]
    public void OptimizedRoute_TakesTheIntendedPlannedOrFallbackPath(string id)
    {
        var loopCase = CaseById(id);
        var root = Root(loopCase);
        foreach (var retainPlans in new[] { false, true })
        {
            var diagnostics = new LoopOptimizationDiagnostics();
            ObserveRoutes(loopCase, root, retainPlans, diagnostics);
            AssertIntendedPath(loopCase, diagnostics.GetSnapshot());
        }
    }

    private static void AssertIntendedPath(PlannedLoopTempCase loopCase, LoopOptimizationDiagnosticsSnapshot snapshot)
    {
        var activations = ActivationBases.Count;
        var planned = loopCase.Path == TempPath.Planned;
        var isWhile = loopCase.Loop == StepLoop.While;

        Assert.Equal(activations, snapshot.OptimizedLoopHits);
        Assert.Equal(0, snapshot.OptimizedLoopFallbacks);
        Assert.Equal(activations * loopCase.RoundsPerActivation, snapshot.LoopIterations);

        var plan = Assert.Single(snapshot.LoopPlans);
        var owners = new[] { "Outer", "Run" }[(2 - loopCase.Depth)..];
        Assert.Equal(string.Join(".", owners.Append("Step").Append(isWhile ? "while" : "repeat")), plan.Identity);
        Assert.True(plan.Optimized);
        Assert.Null(plan.FallbackReason);
        Assert.Equal(activations, plan.BuildCount);
        Assert.Equal(activations, plan.ExecutionCount);

        // The temps, in declaration order: (planned, plan summary, refusal).
        (string, bool, string?, string?)[] plannedTemps =
        [
            ("T", true, "Multiply(StateSlot(n), Const(2))", null),
            ("F", false, null, TickTempRefusal),
            ("K", true, "Const(7)", null),
            ("U", true, "Add(StateSlot(n), Const(100))", null),
        ];
        (string, bool, string?, string?)[] withdrawnTemps =
        [
            ("T", false, null, PartialPlanRefusal),
            ("F", false, null, TickTempRefusal),
            ("K", false, null, PartialPlanRefusal),
            ("U", false, null, PartialPlanRefusal),
        ];
        Assert.Equal(planned ? plannedTemps : withdrawnTemps,
            plan.Temps.Select(temp => (temp.Name, temp.Planned, temp.PlanSummary, temp.FallbackReason)));

        // The rows: (role, index, planned, plan summary, refusal).
        var accumulator = "StateSlot(acc)";
        for (var group = 0; group < loopCase.Reuse; group++)
            accumulator = $"Add(Add({accumulator}, TempSlot(T)), TempSlot(K))";
        var rows = new List<(string, int?, bool, string?, string?)>
        {
            ("output", 0, true, "Add(StateSlot(n), Const(1))", null),
            planned
                ? ("output", 1, true, accumulator, null)
                : ("output", 1, false, null, "unsupported local property reference: T"),
        };
        if (isWhile)
        {
            rows.Add(planned
                ? ("continuation", null, true, FormattableString.Invariant($"LessOrEqual(Add(StateSlot(n), TempSlot(K)), Const({loopCase.Rounds + 7}))"), null)
                : ("continuation", null, false, null, "unsupported local property reference: K"));
        }

        Assert.Equal(rows, plan.Expressions.Select(row => (row.Role, row.Index, row.Planned, row.PlanSummary, row.FallbackReason)));

        // Generic row evaluations inside the optimized loop: none on the planned path; on the
        // fallback path the accumulator row of every state-forming round and the continuation row of
        // every round.
        var generic = planned ? 0 : activations * (loopCase.Rounds + (isWhile ? loopCase.RoundsPerActivation : 0));
        Assert.Equal(generic, snapshot.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.Equal(generic, snapshot.PlannedExpressionFallbacks);
    }

    // ── The dimensions ─────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// The varied dimensions tell every rejected reading from the approved per-round memo, and each
    /// is told EXACTLY where the rule says a dimension reaches it — so dropping a level of a
    /// dimension would leave a reading undistinguished. Also pinned: which observation sees each
    /// reading (a run cache entry of the exported temp, a missed publication and per-read evaluation
    /// of the pure temps change no value: only the publication observation tells them).
    /// </summary>
    [Fact]
    public void Readings_AreToldApartExactlyWhereTheVariedDimensionsReachThem()
    {
        static bool Rounds2OrWhile(PlannedLoopTempCase c) => c.Rounds >= 2 || c.Loop == StepLoop.While;
        var told = new Dictionary<Reading, Func<PlannedLoopTempCase, bool>>
        {
            // Two activations: one run-scoped entry can never publish as often as the rounds do.
            [Reading.ExportedRunEntry] = _ => true,
            // A one-round repeat has one round per activation: the loop's memo is the round's.
            [Reading.LoopExecutionEntry] = Rounds2OrWhile,
            // At depth 0 the round is the outermost invoked owner.
            [Reading.OutermostInvocationEntry] = c => c.Depth >= 1 && Rounds2OrWhile(c),
            // A temp read once per round is evaluated once per round either way.
            [Reading.PerRead] = c => c.Reuse >= 2 || c.Loop == StepLoop.While,
            [Reading.NoPublication] = _ => true,
        };
        Assert.Equal(Enum.GetValues<Reading>().Where(reading => reading != Reading.Approved), told.Keys);

        foreach (var (reading, predicate) in told)
        {
            var distinguished = Cases.Where(c => !Predict(c, reading).SameAs(c.Expected)).Select(c => c.Id).ToList();
            Assert.NotEmpty(distinguished);
            Assert.Equal(Cases.Where(predicate).Select(c => c.Id), distinguished);
        }

        // Only the publication observation sees these readings: the value and the effect are the approved ones.
        foreach (var reading in new[] { Reading.ExportedRunEntry, Reading.NoPublication })
        {
            Assert.All(Cases, c => Assert.Equal((c.Expected.Neutral, c.Expected.Ticks), (Predict(c, reading).Neutral, Predict(c, reading).Ticks)));
        }

        Assert.All(Cases.Where(c => c.Path == TempPath.Planned), c =>
            Assert.Equal((c.Expected.Neutral, c.Expected.Ticks), (Predict(c, Reading.PerRead).Neutral, Predict(c, Reading.PerRead).Ticks)));

        // Where each reading changes the VALUE. A memo that survives the rounds does so exactly where a
        // later state-forming round reads the stale local-only T (R ≥ 2; a one-round while step tells it
        // by K's count alone), and the outermost-owner key only below an invoked owner. Per-read
        // evaluation does so only where F ticks twice in a round.
        static IEnumerable<string> ValueChanged(Reading reading)
            => Cases.Where(c => Predict(c, reading).Neutral != c.Expected.Neutral).Select(c => c.Id);
        Assert.Equal(Cases.Where(c => c.Rounds >= 2).Select(c => c.Id), ValueChanged(Reading.LoopExecutionEntry));
        Assert.Equal(Cases.Where(c => c.Depth >= 1 && c.Rounds >= 2).Select(c => c.Id), ValueChanged(Reading.OutermostInvocationEntry));
        Assert.Equal(Cases.Where(c => c.Path == TempPath.Fallback && c.Reuse >= 2).Select(c => c.Id), ValueChanged(Reading.PerRead));
    }

    // ── Negative controls ──────────────────────────────────────────────────────────────────────

    /// <summary>
    /// A perturbed recorder on the two synchronous cache-recording routes (the async route keeps the
    /// reference cache), with the cases each check must reject, written from the rule, never
    /// observed. <see cref="PolicyVerdict"/> names, per case, the requirement of the approved route
    /// policy that rejects it (null: accepted); <see cref="ConstructedRejects"/> says where the
    /// constructed expectations alone, with no route compared with another, reject it.
    /// </summary>
    private sealed record Perturbation(
        Func<ZeroArgPublicationObserver.PublicationRecorder> Recorder,
        Func<PlannedLoopTempCase, string?> PolicyVerdict,
        Func<PlannedLoopTempCase, bool> ConstructedRejects);

    /// <summary>Which requirement rejects a case: generic and optimized differ per binding name.</summary>
    private const string ByName = "generic and optimized differ per name";

    /// <summary>Which requirement rejects a case: the async reference route's total differs.</summary>
    private const string ByAsyncTotal = "the async total differs";

    /// <summary>Which requirement rejects a case: the optimized route publishes in another order.</summary>
    private const string ByOrder = "another publication order";

    public static TheoryData<string> Perturbations()
        => new(["drop-planned-slot-reports", "run-wide-key", "swap-planned-slot-names", "evaluate-every-read", "count-every-read"]);

    private static bool Planned(PlannedLoopTempCase c) => c.Path == TempPath.Planned;

    private static bool ReadTwiceInARound(PlannedLoopTempCase c) => c.Reuse >= 2 || c.Loop == StepLoop.While;

    private static Perturbation PerturbationNamed(string name)
        => name switch
        {
            // FAILURE TO DEMAND, as an observer misses it: the report of a planned slot is dropped (the
            // observer before F01). Only the planned path has slots: there the optimized route reports
            // no T and no K.
            "drop-planned-slot-reports" => new(() => new DroppingSlotReports(),
                c => Planned(c) ? ByName : null,
                Planned),
            // A PERTURBED KEY, one entry per binding and run (a run cache entry): the local-only T goes
            // stale and every temp publishes once. On the fallback path both synchronous routes share
            // the perturbation, so only the async reference route tells it.
            "run-wide-key" => new(() => new RunWideKey(),
                c => Planned(c) ? ByName : ByAsyncTotal,
                _ => true),
            // A WRONG BINDING: T's slot is reported as K and K's as T. The counts tell it only where they
            // differ (a while step reads K once more per round); the order tells it in every planned case.
            "swap-planned-slot-names" => new(() => new SwappingSlotNames(),
                c => !Planned(c) ? null : c.Loop == StepLoop.While ? ByName : ByOrder,
                c => Planned(c) && c.Loop == StepLoop.While),
            // A WRONG EVALUATION COUNT, as evaluation (every read misses and evaluates afresh, so F ticks
            // per read) and as observation (a reuse counted as a publication): told wherever a temp is
            // read twice in a round.
            "evaluate-every-read" => new(() => new EvaluatingEveryRead(),
                c => !ReadTwiceInARound(c) ? null : Planned(c) ? ByName : ByAsyncTotal,
                ReadTwiceInARound),
            "count-every-read" => new(() => new CountingEveryRead(),
                c => !ReadTwiceInARound(c) ? null : Planned(c) ? ByName : ByAsyncTotal,
                ReadTwiceInARound),
            _ => throw new ArgumentOutOfRangeException(nameof(name), name, null),
        };

    /// <summary>
    /// Each perturbation is rejected by the approved route policy exactly where the family can tell
    /// it, by the requirement the rule predicts, and — independently of every route comparison — by
    /// the constructed expectations wherever it changes a value, a count or the storage split.
    /// </summary>
    [Theory]
    [MemberData(nameof(Perturbations))]
    public void PerturbedRecorder_IsRejectedExactlyWhereTheFamilyCanTellIt(string name)
    {
        var perturbation = PerturbationNamed(name);

        var verdicts = Cases.Select(c => (c.Id, Verdict: PolicyVerdict(c, perturbation.Recorder))).Where(v => v.Verdict is not null).ToList();
        Assert.NotEmpty(verdicts);
        Assert.Equal(Cases.Where(c => perturbation.PolicyVerdict(c) is not null).Select(c => (c.Id, perturbation.PolicyVerdict(c))), verdicts);

        var constructed = Cases.Where(c => ConstructedExpectationRejects(c, perturbation.Recorder)).Select(c => c.Id).ToList();
        Assert.NotEmpty(constructed);
        Assert.Equal(Cases.Where(perturbation.ConstructedRejects).Select(c => c.Id), constructed);
    }

    /// <summary>The control of the controls: the unperturbed recorder is rejected nowhere, by either check.</summary>
    [Fact]
    public void ApprovedRecorder_IsRejectedNowhere()
    {
        static ZeroArgPublicationObserver.PublicationRecorder Approved() => new();
        Assert.All(Cases, loopCase =>
        {
            Assert.Null(PolicyVerdict(loopCase, Approved));
            Assert.False(ConstructedExpectationRejects(loopCase, Approved));
        });
    }

    /// <summary>
    /// The approved route policy over the cache-recording routes, with <paramref name="recorder"/> on
    /// the two synchronous ones: the observer's route requirements (neutral observation on each
    /// route, owners released, generic and optimized per binding name, the async total), then the
    /// constructed publications and frame-slot split, then the generic publication order on the
    /// optimized route. Which requirement rejected the case, or null; an unexpected reason is
    /// returned whole.
    /// </summary>
    private static string? PolicyVerdict(PlannedLoopTempCase loopCase, Func<ZeroArgPublicationObserver.PublicationRecorder> recorder)
    {
        ZeroArgPublicationObserver.Routes routes;
        try
        {
            routes = ZeroArgPublicationObserver.ObserveSourceRoutes(Corpus, loopCase.Id, Root(loopCase), loopCase.Expected.Neutral, recorders: recorder);
        }
        catch (InvalidOperationException ex) when (ex.Message.StartsWith($"{Corpus} route disagreement for '{loopCase.Id}'", StringComparison.Ordinal))
        {
            return ex.Message.Contains("generic and optimized routes published different cache entries", StringComparison.Ordinal) ? ByName
                : ex.Message.Contains("async and sync routes published a different number of entries", StringComparison.Ordinal) ? ByAsyncTotal
                : ex.Message;
        }

        if (!loopCase.Expected.Publications.Matches(routes.Publications))
            return $"published [{CachePublicationExpectation.Describe(routes.Publications)}]";
        if (!SameEntries(loopCase.ExpectedFrameSlots, routes.OptimizedFrameSlots))
            return $"established [{CachePublicationExpectation.Describe(routes.OptimizedFrameSlots)}] in frame slots";
        return routes.GenericOrder.SequenceEqual(routes.OptimizedOrder) ? null : ByOrder;
    }

    /// <summary>
    /// The constructed expectations alone: whether the generic or the optimized route, each run with
    /// a fresh <paramref name="recorder"/> and compared with nothing but the constructed neutral
    /// observation, publications and (optimized) frame-slot split, misses one of them.
    /// </summary>
    private static bool ConstructedExpectationRejects(PlannedLoopTempCase loopCase, Func<ZeroArgPublicationObserver.PublicationRecorder> recorder)
    {
        var program = new Expr.AlgorithmExpr(Root(loopCase));
        foreach (var optimized in new[] { false, true })
        {
            var cache = recorder();
            var (result, _) = Evaluator.RunCountedObserved(program, enableOptimizations: optimized, zeroArgPropertyResultCache: cache);
            if (Neutral(result) != loopCase.Expected.Neutral
                || !loopCase.Expected.Publications.Matches(new CachePublications(cache.ByName, cache.Total))
                || optimized && !SameEntries(loopCase.ExpectedFrameSlots, new CachePublications(cache.FrameSlotsByName, cache.FrameSlotTotal)))
            {
                return true;
            }
        }

        return false;
    }

    private sealed class DroppingSlotReports : ZeroArgPublicationObserver.PublicationRecorder
    {
        public override void PlannedLoopSlotPublished(Property binding)
        {
        }
    }

    private sealed class RunWideKey : ZeroArgPublicationObserver.PublicationRecorder
    {
        protected override ZeroArgPropertyCacheKey KeyOf(ZeroArgPropertyExecution execution)
            => base.KeyOf(execution) with { ValueEnvironmentIdentity = ZeroArgPropertyCacheKey.RunWideEnvironmentIdentity };
    }

    private sealed class SwappingSlotNames : ZeroArgPublicationObserver.PublicationRecorder
    {
        public override void PlannedLoopSlotPublished(Property binding)
            => RecordFrameSlot(binding.Name switch { "T" => "K", "K" => "T", var other => other });
    }

    private sealed class EvaluatingEveryRead : ZeroArgPublicationObserver.PublicationRecorder
    {
        // A fresh environment per request: no request ever finds another's entry.
        protected override ZeroArgPropertyCacheKey KeyOf(ZeroArgPropertyExecution execution)
            => base.KeyOf(execution) with { ValueEnvironmentIdentity = new object() };
    }

    private sealed class CountingEveryRead : ZeroArgPublicationObserver.PublicationRecorder
    {
        protected override bool CountsReuse => true;
    }

    // ── Lean ───────────────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// Lean's tick observation, beside the shared cache observation: the final
    /// <c>EvalState.tickCounter</c> of a finished run, read with <c>publicationsOf</c>'s completion
    /// rule, and its hand-written states.
    /// </summary>
    internal const string TickObservationDefinitions = """
        /-- The `tick()` executions of ONE finished run, read like `publicationsOf` from its outcome and
            final state: `EvalState.tickCounter` (C#: `EvaluationBudget.TickCount`), which only a
            successful execution advances and nothing rolls back, so a failed run keeps its earlier
            ticks; `none` exactly where `publicationsOf` has no observation. -/
        def ticksOf (outcome : Except Error Result) (state : EvalState) : Option Nat :=
          if outcome.isIncomplete || !state.activeZeroArgProperties.isEmpty then none
          else some state.tickCounter

        /-- The `tick()` executions of ONE plain run; each guard on it runs its program once. -/
        def tickTotal (e : Expr) : Option Nat :=
          match (runResultM e).runState EvalState.empty with
          | (outcome, state) => ticksOf outcome state

        -- Tick observation states (hand-written states, not evaluator programs).
        #guard (ticksOf (.error .fuelExhausted) EvalState.empty).isNone
        #guard (ticksOf (.ok (.atom 0)) { EvalState.empty with activeZeroArgProperties := [observedEntryProbe] }).isNone
        #guard ticksOf (.ok (.atom 0)) { EvalState.empty with tickCounter := 2 } == some 2
        #guard ticksOf (.error .divByZero) { EvalState.empty with tickCounter := 1 } == some 1

        """;

    /// <summary>
    /// The generated Lean module holds, for every case, the encoding of the SAME elaborated program
    /// the C# routes ran, with its neutral, per-name, total and tick guards written from the
    /// constructed expectation — the numbers C# is checked against above, never an observation.
    /// </summary>
    [Fact]
    public void GeneratedLeanModule_HoldsEveryCaseWithItsConstructedGuards()
    {
        var expected = GenerateLeanModule();
        var path = Path.Combine(RepoRoot.Find(), ArtifactPath);
        ArtifactRegeneration.VerifyOrRegenerate(RegenerationFlags.PlannedLoopTempFamily, ArtifactPath,
            regenerate: () => expected,
            verify: () =>
            {
                var actual = File.ReadAllText(path).ReplaceLineEndings("\n");
                Assert.True(expected == actual, SemanticExplorerLeanArtifactTests.DescribeFirstDifference(expected, actual));
            },
            afterRegenerating: "build CoreTests to check the Lean side");
    }

    /// <summary>
    /// The module's guards: the shared observation-state and tick-state guards, seven per case, and
    /// the count guard; no case is guarded at <c>none</c>.
    /// </summary>
    [Fact]
    public void GeneratedLeanModule_GuardsEveryCaseOnTheSharedObservations()
    {
        var module = GenerateLeanModule();
        static int Guards(string text) => text.Split('\n').Count(line => line.StartsWith("#guard ", StringComparison.Ordinal));
        const int TickStateGuards = 4;
        Assert.Equal(TickStateGuards, Guards(TickObservationDefinitions.ReplaceLineEndings("\n")));
        Assert.Equal(LeanObsTemplate.CacheObservationContractGuards + TickStateGuards + 7 * Cases.Count + 1, Guards(module));
        Assert.Contains(LeanObsTemplate.SharedDefinitions.ReplaceLineEndings("\n"), module, StringComparison.Ordinal);
        Assert.Contains(LeanObsTemplate.CacheObservationDefinitions.ReplaceLineEndings("\n"), module, StringComparison.Ordinal);
        Assert.All(Cases, loopCase =>
        {
            Assert.Contains($"#guard obs {loopCase.LeanName} == {LeanAstEncoder.QuoteString(loopCase.Expected.Neutral)}\n", module, StringComparison.Ordinal);
            Assert.Contains($"#guard tickTotal {loopCase.LeanName} == some {loopCase.Expected.Ticks.ToString(CultureInfo.InvariantCulture)}\n", module, StringComparison.Ordinal);
        });
        Assert.DoesNotContain("== none", module[module.IndexOf("-- plt/", StringComparison.Ordinal)..], StringComparison.Ordinal);
    }

    private static string GenerateLeanModule()
    {
        var builder = new StringBuilder();
        builder.Append("""
            import KatLang

            /-!
            GENERATED by PlannedLoopTempFamilyTests from PlannedLoopTempFamily (KL-06 F01 follow-up): never edit
            by hand. Regenerate with KATLANG_REGENERATE_PLANNED_LOOP_TEMP_FAMILY=1 and the filter
            PlannedLoopTempFamilyTests.GeneratedLeanModule, then build CoreTests.

            Thirty-six `repeat` and `while` steps, each declaring a planned local-only temp (`T = n * 2`), a
            fallback temp (`F = n * 10 + tick()`), an exported self-contained temp (`K = 7`) and an undemanded
            temp (`U = n + 100`), with activation depth, round count and reuse varied over an L9 array. Every
            guard is written from the expectation the generator constructs from the approved rule (a round is
            an actual call of the step and publishes each temp it demands once), which C# meets on its
            generic, optimized and async routes. The optimizer's path, the frame-slot storage, the order and
            the operational counters are C#-only. See docs/design/differential-observations.md,
            "Planned-loop temp family".
            -/

            namespace PlannedLoopTempFamily
            open KatLang


            """.ReplaceLineEndings("\n"));
        builder.Append(LeanObsTemplate.SharedDefinitions.ReplaceLineEndings("\n"));
        builder.Append("\n\n");
        builder.Append(LeanObsTemplate.CacheObservationDefinitions.ReplaceLineEndings("\n"));
        builder.Append("\n\n");
        LeanObsTemplate.AppendCacheObservationContracts(builder);
        builder.Append('\n');
        builder.Append(TickObservationDefinitions.ReplaceLineEndings("\n"));
        builder.Append('\n');

        foreach (var loopCase in Cases)
        {
            var expected = loopCase.Expected;
            builder.Append($"-- {loopCase.Id}\n");
            foreach (var line in loopCase.Source.Split('\n'))
                builder.Append("--   ").Append(line).Append('\n');
            builder.Append($"def {loopCase.LeanName} : Expr :=\n  {LeanAstEncoder.EncodeProgram(Root(loopCase))}\n");
            builder.Append($"#guard obs {loopCase.LeanName} == {LeanAstEncoder.QuoteString(expected.Neutral)}\n");
            ZeroArgPublicationObserver.AppendCacheGuards(builder, loopCase.LeanName, expected.Publications);
            builder.Append($"#guard tickTotal {loopCase.LeanName} == some {expected.Ticks.ToString(CultureInfo.InvariantCulture)}\n\n");
        }

        SemanticExplorerLeanArtifactTests.AppendCountGuard(builder, "familyCaseIds", [.. Cases.Select(c => c.Id)], 36,
            "The generated cases: two loop kinds, two paths and the nine cells of the L9 array.");
        builder.Append("end PlannedLoopTempFamily\n");
        return builder.ToString();
    }

    // ── Helpers ────────────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// The three cache-recording routes, ordinary or with retained invocation plans, each run proven
    /// to have captured (or not) the plan seam.
    /// </summary>
    private static ZeroArgPublicationObserver.Routes ObserveRoutes(
        PlannedLoopTempCase loopCase, Algorithm root, bool retainPlans, LoopOptimizationDiagnostics? diagnostics = null)
    {
        using var activation = retainPlans ? InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam()) : null;
        var routes = ZeroArgPublicationObserver.ObserveSourceRoutes(Corpus, loopCase.Id, root, loopCase.Expected.Neutral, diagnostics);
        var seam = retainPlans || ForcedInvocationPlansHook.Forced;
        Assert.Equal(seam, routes.Budgets.Generic.PlanTestSeam is not null);
        Assert.Equal(seam, routes.Budgets.Optimized.PlanTestSeam is not null);
        Assert.Equal(seam, routes.AsynchronousBudget.PlanTestSeam is not null);
        return routes;
    }

    private static (long Steps, long Checkpoints, long Depth, long Items, long Ticks) Counters(EvaluationBudget budget)
        => (budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth, budget.MaterializedItems, budget.TickCount);

    private static bool SameEntries(CachePublicationExpectation expected, CachePublications observed)
        => expected.Total == observed.Total && expected.Entries.All(entry => observed.Published(entry.Name) == entry.Count)
            && observed.ByName.All(entry => entry.Value == 0 || expected.Entries.Any(listed => listed.Name == entry.Key));

    /// <summary>The neutral observation of one run, as the observer and the Lean guards spell it.</summary>
    private static string Neutral(EvalResult<Evaluator.CountedResult> result)
        => result.IsError
            ? $"err {DifferentialErrors.Observe(result.Error).Category}"
            : $"ok raw={SemanticExplorerHarness.Neutral(result.Value.Value)} n={result.Value.EmittedCount}";

    /// <summary>The raw value of a neutral success observation (<c>ok raw=… n=…</c>).</summary>
    private static string RawOf(string neutral)
    {
        const string prefix = "ok raw=";
        Assert.StartsWith(prefix, neutral, StringComparison.Ordinal);
        return neutral[prefix.Length..neutral.LastIndexOf(" n=", StringComparison.Ordinal)];
    }
}
