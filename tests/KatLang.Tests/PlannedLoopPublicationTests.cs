using System.Text;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// KL-06 F01 (owner decision Option A, November 21 2026): the zero-argument property publications
/// of a PLANNED loop. A publication is counted when a zero-argument property first establishes a
/// reusable value in its owning invocation, and a loop round is a fresh invocation of the step. The
/// generic strategy and Lean store that value in the property cache. The planned loop keeps it in
/// the round's frame slot (<c>LoopRunFrame.EstablishTempSlot</c>) and reports the store to the run's
/// publication observer (<see cref="IPlannedLoopPublicationObserver"/>), so the three C# routes and
/// Lean count the same entries under the same binding names. Before the decision the optimized route
/// reported none of them: the local-only step property of the first witness below was published
/// three times by the generic route and by Lean and never by the optimized one, with the same result
/// <c>S[3, 6]</c>.
///
/// <para>The cross-engine table (<see cref="Cases"/>) is pinned on both sides with the same
/// programs and the same expectations. <c>lean/CoreTests/PlannedLoopPublications.lean</c> holds, for
/// every case, the <see cref="LeanAstEncoder"/> encoding of the source's elaborated AST, the neutral
/// guard and the cache guards written from the reviewed expectation, and
/// <see cref="LeanTable_HoldsTheSameProgramsAndExpectations"/> checks that it does. The
/// expectations are hand-written from the rule; no number here is copied from a run.</para>
///
/// <para>Every case PROVES its route from the planner's own observations of the very run whose
/// publications are compared: the loop was entered planned, every row and every step property is a
/// plan, and the entries the reviewed expectation names came from frame slots. The existing
/// requirements of the observer stay in force on every case: generic and optimized agree per binding
/// name, the suspending async route agrees in total and never uses the synchronous member, and every
/// publication owner is released.</para>
/// </summary>
public class PlannedLoopPublicationTests
{
    private const string LeanTablePath = "lean/CoreTests/PlannedLoopPublications.lean";
    private const string Corpus = "Planned-loop publication";
    private const string TableStart = "-- BEGIN PLANNED-LOOP PUBLICATION TABLE (checked by PlannedLoopPublicationTests)";
    private const string TableEnd = "-- END PLANNED-LOOP PUBLICATION TABLE";

    /// <summary>
    /// One case: the source, its neutral observation, the reviewed publications of the whole run
    /// (<c>name=count</c>; a name at zero is watched and unpublished), the part of them the planned
    /// rounds established in frame slots, the number of rounds the optimized route started as planned
    /// rounds, and the reason of the one handover to the generic strategy (none when every round is
    /// planned).
    /// </summary>
    private sealed record LoopCase(
        string Id, string Source, string Neutral, string Publications, string FrameSlots, int PlannedRounds, string? Handover = null)
    {
        /// <summary>The Lean fixture's name: <c>plp</c> plus the id in PascalCase.</summary>
        public string LeanName
            => "plp" + string.Concat(Id.Split('-').Select(static word => char.ToUpperInvariant(word[0]) + word[1..]));

        public Algorithm.User Root() => SourceProvenance.ParseValid(Source).Root;

        public CachePublicationExpectation Expectation => CachePublicationExpectation.Parse(Publications);
    }

    /// <summary>A case whose every round is planned: all its publications are frame-slot stores.</summary>
    private static LoopCase Planned(string id, string source, string neutral, string publications, int rounds)
        => new(id, source, neutral, publications, publications, rounds);

    private static readonly LoopCase[] Cases =
    [
        // The F01 witness: a LOCAL-ONLY step property read twice in each of three rounds. Six reads,
        // three owning invocations, three publications.
        Planned("local-only-temp-read-twice",
            "Step(n, total) = {\n    Next = n + 1\n    Next, total + Next\n}\nStep(0, 0).repeat(3)",
            "ok raw=S[3, 6] n=1", "Next=3", rounds: 3),
        // An EXPORTED, constant step property: one entry reused across the rounds would give the
        // same 15, so only the publication count tells a round's own binding from a shared one.
        Planned("exported-constant-temp",
            "Step(s) = {\n    T = 5\n    s + T\n}\nStep(0).repeat(3)",
            "ok raw=15 n=1", "T=3", rounds: 3),
        // B's calculation reads A: A is established first, then B, once each per round.
        Planned("two-temps-one-reads-the-other",
            "Step(n) = {\n    A = n + 1\n    B = A * 2\n    B + A\n}\nStep(0).repeat(3)",
            "ok raw=39 n=1", "A=3 B=3", rounds: 3),
        // CACHE-PUB-1: a qualifying zero-supply call that finds the slot empty establishes it; the
        // read after it reuses the slot.
        Planned("call-establishes-then-read",
            "Step(n) = {\n    A = n * 10 + 1\n    n + A() + A\n}\nStep(0).repeat(3)",
            "ok raw=926 n=1", "A=3", rounds: 3),
        // The read establishes the slot; the later call executes fresh and publishes nothing.
        Planned("read-establishes-then-call",
            "Step(n) = {\n    A = n * 10 + 1\n    n + A + A()\n}\nStep(0).repeat(3)",
            "ok raw=926 n=1", "A=3", rounds: 3),
        // Two calls: the first establishes the empty slot, the second executes fresh and adds nothing.
        Planned("call-twice",
            "Step(n) = {\n    A = n * 10 + 1\n    n + A() + A()\n}\nStep(0).repeat(3)",
            "ok raw=926 n=1", "A=3", rounds: 3),
        // The same for an exported step property.
        Planned("exported-temp-call-then-read",
            "Step(n) = {\n    E = 6 * 7\n    n + E() + E\n}\nStep(0).repeat(3)",
            "ok raw=252 n=1", "E=3", rounds: 3),
        // An alias step property owns no entry: its read publishes its TARGET's binding (OD-E).
        Planned("alias-temp-publishes-its-target",
            "Step(n) = {\n    A = n + 1\n    B = A\n    B + B\n}\nStep(0).repeat(3)",
            "ok raw=14 n=1", "A=3 B=0", rounds: 3),
        // A `while` round reads its condition row first: that row establishes the slot, the state
        // row reuses it, and the round whose verdict is false has published too.
        Planned("while-condition-row-establishes",
            "Step(n) = {\n    Next = n + 1\n    Next, Next < 3\n}\nStep(0).while",
            "ok raw=2 n=1", "Next=3", rounds: 3),
        // An undemanded step property does no work and publishes nothing: an observed EMPTY cache.
        Planned("unused-temp",
            "Step(n) = {\n    Unused = n + 1\n    n + 2\n}\nStep(0).repeat(3)",
            "ok raw=6 n=1", "Unused=0", rounds: 3),
        // A calculation that fails before it establishes its value publishes nothing.
        Planned("temp-fails-before-establishing",
            "Step(n) = {\n    Bad = 1 / n\n    n + Bad\n}\nStep(0).repeat(3)",
            "err div0", "Bad=0", rounds: 1),
        // The first round publishes; the second round's calculation fails. The run keeps the entry.
        Planned("temp-fails-in-a-later-round",
            "Step(n) = {\n    T = 1 / (1 - n)\n    n + T\n}\nStep(0).repeat(3)",
            "err div0", "T=1", rounds: 2),
        // A failure in the round AFTER its publication: both rounds' entries stay.
        Planned("failure-after-publication-in-the-round",
            "Step(n) = {\n    T = n + 1\n    T + 0 / (2 - T)\n}\nStep(0).repeat(3)",
            "err div0", "T=2", rounds: 2),
        // A failure of the run after the loop completed keeps all three entries.
        Planned("failure-after-the-loop",
            "Step(s) = {\n    T = 5\n    s + T\n}\nStep(0).repeat(3)\n1 / 0",
            "err div0", "T=3", rounds: 3),
        // HANDOVER: the first round is planned and its state row emits no value, so the loop
        // continues on the generic strategy. One entry is a frame-slot store and two are cache
        // stores; the round that handed over is never evaluated again, so nothing is counted twice.
        new("handover-continues-generically",
            "Step(a, n) = {\n    T = n + 1\n    a, T\n}\nStep((), 0).repeat(3)",
            "ok raw=S[S[], 3] n=1", "T=3", FrameSlots: "T=1", PlannedRounds: 1,
            Handover: "loop expression did not emit exactly one state value"),
    ];

    public static TheoryData<string> CaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var loopCase in Cases)
            data.Add(loopCase.Id);
        return data;
    }

    private static LoopCase CaseById(string id) => Cases.Single(loopCase => loopCase.Id == id);

    /// <summary>
    /// The reviewed publications on the three C# routes, from a run whose loop was PLANNED: the
    /// expected entries per binding name, the storage that established them, the publication order,
    /// and the operational counters of the generic and the optimized route.
    /// </summary>
    [Theory]
    [MemberData(nameof(CaseIds))]
    public void EveryRoute_PublishesTheReviewedEntries_AndTheOptimizedRouteIsPlanned(string id)
    {
        var loopCase = CaseById(id);
        var diagnostics = new LoopOptimizationDiagnostics();

        // Generic and optimized per binding name, the suspending async route in total, every owner
        // released, and the case's neutral observation on each route (the observer's requirements).
        var routes = ZeroArgPublicationObserver.ObserveSourceRoutes(Corpus, id, loopCase.Root(), loopCase.Neutral, diagnostics);

        Assert.True(loopCase.Expectation.Matches(routes.Publications),
            $"'{id}' published [{CachePublicationExpectation.Describe(routes.Publications)}], expected [{loopCase.Expectation}]");

        // The optimized route really planned the loop and its step properties.
        Assert.Equal(1, diagnostics.OptimizedLoopHits);
        Assert.Equal(loopCase.PlannedRounds, diagnostics.LoopIterations);
        Assert.Equal(0, diagnostics.PlannedExpressionFallbacks);
        Assert.Equal(0, diagnostics.GenericExpressionEvaluationsInsideOptimizedLoops);
        var plan = Assert.Single(diagnostics.GetSnapshot().LoopPlans);
        Assert.True(plan.Optimized);
        Assert.Equal(1, plan.ExecutionCount);
        Assert.All(plan.Expressions, expression => Assert.True(expression.Planned, $"row {expression.Role} {expression.Index} is not planned"));
        Assert.All(plan.Temps, temp => Assert.True(temp.Planned, $"step property {temp.Name} is not planned: {temp.FallbackReason}"));
        Assert.All(loopCase.Expectation.Entries, entry => Assert.Contains(plan.Temps, temp => temp.Name == entry.Name));
        if (loopCase.Handover is null)
        {
            Assert.Equal(0, diagnostics.OptimizedLoopFallbacks);
            Assert.Empty(diagnostics.FallbackReasons);
        }
        else
        {
            Assert.Equal(1, diagnostics.OptimizedLoopFallbacks);
            Assert.Equal(1, Assert.Single(diagnostics.FallbackReasons, reason => reason.Key == loopCase.Handover).Value);
        }

        // WHICH storage established the entries: the planned rounds' frame slots, and after a
        // handover the cache for the rounds the generic strategy ran.
        var frameSlots = CachePublicationExpectation.Parse(loopCase.FrameSlots);
        Assert.True(frameSlots.Total == routes.OptimizedFrameSlots.Total
            && frameSlots.Entries.All(entry => routes.OptimizedFrameSlots.Published(entry.Name) == entry.Count),
            $"'{id}' established [{CachePublicationExpectation.Describe(routes.OptimizedFrameSlots)}] in frame slots, expected [{frameSlots}]");

        // Evaluation order and charges are the generic ones.
        Assert.Equal(routes.GenericOrder, routes.OptimizedOrder);
        var (generic, optimized) = routes.Budgets;
        Assert.Equal(generic.ConsumedSteps, optimized.ConsumedSteps);
        Assert.Equal(generic.ConsumedExpressionCheckpoints, optimized.ConsumedExpressionCheckpoints);
        Assert.Equal(generic.PeakDepth, optimized.PeakDepth);
        Assert.Equal(generic.MaterializedItems, optimized.MaterializedItems);
        Assert.Equal(generic.TickCount, optimized.TickCount);
    }

    /// <summary>
    /// WHICH optimized path ran for the two witnesses of the owner decision, from the planner's own
    /// description of the plan it executed: the step property is a planned temp, and every row reads
    /// it through a planned temp slot (never a generic fallback, which would use the cache).
    /// </summary>
    [Theory]
    [InlineData("local-only-temp-read-twice", "Step.repeat", "Next", "Add(StateSlot(n), Const(1))",
        "TempSlot(Next)|Add(StateSlot(total), TempSlot(Next))")]
    [InlineData("exported-constant-temp", "Step.repeat", "T", "Const(5)", "Add(StateSlot(s), TempSlot(T))")]
    public void Witness_IsExecutedAsAPlannedTempSlot(string id, string planIdentity, string temp, string tempPlan, string rowPlans)
    {
        var loopCase = CaseById(id);
        var diagnostics = new LoopOptimizationDiagnostics();
        var routes = ZeroArgPublicationObserver.ObserveSourceRoutes(Corpus, id, loopCase.Root(), loopCase.Neutral, diagnostics);

        var plan = Assert.Single(diagnostics.GetSnapshot().LoopPlans);
        Assert.Equal(planIdentity, plan.Identity);
        Assert.True(plan.Optimized);
        Assert.Equal(1, plan.BuildCount);
        Assert.Equal(1, plan.ExecutionCount);
        var planned = Assert.Single(plan.Temps);
        Assert.Equal((temp, true, tempPlan), (planned.Name, planned.Planned, planned.PlanSummary));
        Assert.Equal(rowPlans.Split('|'), plan.Expressions.Select(expression => expression.PlanSummary));

        // Three rounds, one frame-slot store each, and no cache store on the optimized route.
        Assert.Equal(3, diagnostics.LoopIterations);
        Assert.Equal(3, routes.OptimizedFrameSlots.Published(temp));
        Assert.Equal(3, routes.Publications.Published(temp));
        Assert.Equal([temp, temp, temp], routes.OptimizedOrder);
    }

    /// <summary>
    /// Observation only. The planned loop KEEPS its frame storage: on the optimized route the run's
    /// own cache holds no entry for a planned step property, while the generic route stores one per
    /// round. An unobserved optimized run gives the observed run's result and charges exactly its
    /// counters, so reporting a store changes nothing a run computes.
    /// </summary>
    [Theory]
    [MemberData(nameof(CaseIds))]
    public void OptimizedRoute_KeepsItsFrameStorage_AndObservingItChangesNoResultOrCharge(string id)
    {
        var loopCase = CaseById(id);
        var program = new Expr.AlgorithmExpr(loopCase.Root());
        var routes = ZeroArgPublicationObserver.ObserveSourceRoutes(Corpus, id, loopCase.Root(), loopCase.Neutral);

        var genericCache = new RunScopedZeroArgPropertyResultCache();
        Evaluator.RunCountedObserved(program, enableOptimizations: false, zeroArgPropertyResultCache: genericCache);
        var optimizedCache = new RunScopedZeroArgPropertyResultCache();
        var (unobserved, unobservedBudget) = Evaluator.RunCountedObserved(program, enableOptimizations: true, zeroArgPropertyResultCache: optimizedCache);

        // The cache's own store: every publication on the generic route, and on the optimized
        // route only what the frame slots did not hold.
        Assert.Equal(routes.Publications.Total, genericCache.PublishedCount);
        Assert.Equal(routes.Publications.Total - routes.OptimizedFrameSlots.Total, optimizedCache.PublishedCount);

        Assert.Equal(loopCase.Neutral, Neutral(unobserved));
        var observedBudget = routes.Budgets.Optimized;
        Assert.Equal(observedBudget.ConsumedSteps, unobservedBudget.ConsumedSteps);
        Assert.Equal(observedBudget.ConsumedExpressionCheckpoints, unobservedBudget.ConsumedExpressionCheckpoints);
        Assert.Equal(observedBudget.PeakDepth, unobservedBudget.PeakDepth);
        Assert.Equal(observedBudget.MaterializedItems, unobservedBudget.MaterializedItems);
    }

    /// <summary>
    /// C#-side sensitivity: the observer refuses a wrong reviewed expectation for every case — an
    /// entry under a name the run never published, one entry too many, one too few, a publication
    /// moved to another name with the total kept, and an empty cache for a run that published.
    /// </summary>
    [Theory]
    [MemberData(nameof(CaseIds))]
    public void Observer_RefusesAWrongReviewedExpectation(string id)
    {
        var loopCase = CaseById(id);
        var root = loopCase.Root();
        var reviewed = loopCase.Expectation;
        var entries = reviewed.Entries.ToArray();

        var observed = ZeroArgPublicationObserver.ObservePilotCase(Corpus, id, root, loopCase.Neutral, reviewed);
        Assert.Equal(reviewed.Total, observed.Total);

        var wrong = new List<CachePublicationExpectation>
        {
            CachePublicationExpectation.Of([.. entries, ("NeverPublished", 1)]),
            CachePublicationExpectation.Of([(entries[0].Name, entries[0].Count + 1), .. entries.Skip(1)]),
        };
        if (reviewed.Total > 0)
        {
            var published = Array.FindIndex(entries, entry => entry.Count > 0);
            var oneFewer = entries.ToArray();
            oneFewer[published] = (entries[published].Name, entries[published].Count - 1);
            wrong.Add(CachePublicationExpectation.Of(oneFewer));

            // The total is kept; a total-only comparison would accept this.
            var renamed = entries.ToArray();
            renamed[published] = ("NeverPublished", entries[published].Count);
            wrong.Add(CachePublicationExpectation.Of(renamed));

            wrong.Add(CachePublicationExpectation.Nothing);
        }

        foreach (var expectation in wrong)
        {
            var ex = Assert.Throws<InvalidOperationException>(()
                => ZeroArgPublicationObserver.ObservePilotCase(Corpus, id, root, loopCase.Neutral, expectation));
            Assert.Contains($"{Corpus} route disagreement for '{id}'", ex.Message, StringComparison.Ordinal);
            Assert.Contains("not the reviewed cache expectation", ex.Message, StringComparison.Ordinal);
        }
    }

    /// <summary>
    /// The three publication states stay three observations in the table: completed runs with
    /// entries, completed runs with an EMPTY cache on success and on failure, and failures that keep
    /// entries. No case is written as a missing observation.
    /// </summary>
    [Fact]
    public void Table_CoversSuccessAndFailure_WithEntriesAndWithAnEmptyCache()
    {
        var classes = Cases
            .Select(loopCase => (Success: loopCase.Neutral.StartsWith("ok ", StringComparison.Ordinal), loopCase.Expectation.State))
            .ToHashSet();

        Assert.Contains((true, CachePublicationState.CompletedNonEmpty), classes);
        Assert.Contains((true, CachePublicationState.CompletedEmpty), classes);
        Assert.Contains((false, CachePublicationState.CompletedNonEmpty), classes);
        Assert.Contains((false, CachePublicationState.CompletedEmpty), classes);
        Assert.Equal(Cases.Length, Cases.Select(loopCase => loopCase.Id).Distinct(StringComparer.Ordinal).Count());
        Assert.Contains(Cases, loopCase => loopCase.Handover is not null);
    }

    // ── The Lean half ──────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// One case as the Lean module holds it: the source as a comment, the encoding of the SAME
    /// elaborated program the C# routes ran, the neutral guard and the cache guards written from the
    /// reviewed expectation by the emitter the pilot artifacts use.
    /// </summary>
    private static string Fixture(LoopCase loopCase)
    {
        var builder = new StringBuilder();
        builder.Append($"-- {loopCase.Id}: {loopCase.Source.Replace("\n", " \\n ")}\n");
        builder.Append($"def {loopCase.LeanName} : Expr :=\n  {LeanAstEncoder.EncodeProgram(loopCase.Root())}\n");
        builder.Append($"#guard obs {loopCase.LeanName} == {LeanAstEncoder.QuoteString(loopCase.Neutral)}\n");
        ZeroArgPublicationObserver.AppendCacheGuards(builder, loopCase.LeanName, loopCase.Expectation);
        return builder.ToString();
    }

    private static string ExpectedTable()
        => string.Join("\n", Cases.Select(Fixture));

    [Fact]
    public void LeanTable_HoldsTheSameProgramsAndExpectations()
    {
        var leanText = File.ReadAllText(Path.Combine(RepoRoot.Find(), LeanTablePath)).ReplaceLineEndings("\n");
        var start = leanText.IndexOf(TableStart + "\n", StringComparison.Ordinal);
        var end = leanText.IndexOf(TableEnd + "\n", StringComparison.Ordinal);
        Assert.True(start >= 0 && end > start, $"{LeanTablePath} must hold the table between its two marker lines.");

        var table = leanText[(start + TableStart.Length + 1)..end];
        var expected = ExpectedTable();
        Assert.True(table == expected, $"{LeanTablePath} must hold, between its marker lines, exactly:\n{expected}");
    }

    /// <summary>
    /// The module observes with the definitions the four generated artifacts share, verbatim, and
    /// keeps the observation-state guards beside them: a missing observation is <c>none</c>, never
    /// <c>some 0</c>. Every other guard of the module is a table guard, so no unpinned guard exists.
    /// </summary>
    [Fact]
    public void LeanModule_UsesTheSharedObservationDefinitions_AndHoldsNoGuardOutsideTheTable()
    {
        var leanText = File.ReadAllText(Path.Combine(RepoRoot.Find(), LeanTablePath)).ReplaceLineEndings("\n");
        var contracts = new StringBuilder();
        LeanObsTemplate.AppendCacheObservationContracts(contracts);

        var definitions = leanText[..leanText.IndexOf(TableStart, StringComparison.Ordinal)];
        Assert.Contains(LeanObsTemplate.SharedDefinitions.ReplaceLineEndings("\n"), definitions, StringComparison.Ordinal);
        Assert.Contains(LeanObsTemplate.CacheObservationDefinitions.ReplaceLineEndings("\n"), definitions, StringComparison.Ordinal);
        Assert.Contains(contracts.ToString(), definitions, StringComparison.Ordinal);

        static int Guards(string text) => text.Split('\n').Count(line => line.StartsWith("#guard ", StringComparison.Ordinal));
        Assert.Equal(LeanObsTemplate.CacheObservationContractGuards, Guards(definitions));
        Assert.Equal(LeanObsTemplate.CacheObservationContractGuards + Guards(ExpectedTable()), Guards(leanText));
        Assert.DoesNotContain("== none", ExpectedTable(), StringComparison.Ordinal);
    }

    private static string Neutral(EvalResult<Evaluator.CountedResult> result)
        => result.IsError
            ? $"err {DifferentialErrors.Observe(result.Error).Category}"
            : $"ok raw={SemanticExplorerHarness.Neutral(result.Value.Value)} n={result.Value.EmittedCount}";
}
