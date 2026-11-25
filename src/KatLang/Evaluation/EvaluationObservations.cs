namespace KatLang;

/// <summary>
/// Passive, run-scoped evaluator observations for tests and fuzz harnesses. One instance is created
/// per observed evaluator run and carried by reference through <see cref="Evaluator.EvalCtx"/>, so
/// every nested context of that run records into the SAME object while separate runs — including
/// concurrent runs on different threads — never share one. It is never created for an ordinary run;
/// the evaluator records through a null-conditional call, so supplying it (or not) cannot influence
/// any evaluation decision, order, or result. It is internal and excluded from every public API,
/// <see cref="RunResult"/>, and language-semantic contract; the counters are C# implementation
/// observations only, comparable between C# executions and never against Lean.
///
/// <para>This is the same run-scoped observation shape as the optimizer diagnostics
/// (<c>LoopOptimizationDiagnostics</c>) and the run's <c>EvaluationBudget</c>: created once per run,
/// mutated only through <c>Record*</c> methods, and read after the run. A fresh instance starts at
/// zero by construction, so no reset logic exists or is required.</para>
/// </summary>
internal sealed class EvaluationObservations
{
    /// <summary>
    /// Optional observer handed to every operation comparer the run's <c>contains</c> and
    /// <c>distinct</c> evaluations create (SEC-02), so a language-level test can read the
    /// structural pair/hash expansions and budget charges of those walks across the whole run.
    /// The run's <c>atoms</c> collections record their slot reads, run replays and cancellation
    /// checkpoints into it too (<c>Result.TryLanguageAtomsObserved</c>).
    /// Supplied by the measuring test; <c>null</c> records nothing.
    /// </summary>
    public ValueTraversalObservations? StructuralTraversal { get; init; }

    /// <summary>
    /// Optional record of the run's conditional-clause attempts (SEC-02-FU2): which clauses each
    /// family dispatch actually began binding, in order, and how each attempt ended. Supplied by the
    /// measuring test; <c>null</c> records nothing.
    /// </summary>
    public ClauseAttemptObservations? ClauseAttempts { get; init; }

    /// <summary>
    /// Optional observer of the run's two admission passes, handed to the structural preflight and the
    /// pre-evaluation validation walk exactly as their standalone observation overloads take one: the
    /// preflight's edges and table capacity hint, the walk's base-walker counters, the tables it took over
    /// from earlier passes and the alias-reach tables it built
    /// (<see cref="FrontEndTraversalObservations.StructuralPreflightCapacityHints"/>,
    /// <see cref="FrontEndTraversalObservations.PreEvaluationHandedOverTables"/>,
    /// <see cref="FrontEndTraversalObservations.PreEvaluationAliasReachTables"/>). Supplied by the measuring
    /// test; <c>null</c> records nothing.
    /// </summary>
    public FrontEndTraversalObservations? PreEvaluationTraversal { get; init; }

    /// <summary>
    /// Optional observer of the run's deferred-body admissions during evaluation (<c>DeferredBodyAdmission</c>): the
    /// edges of each body check and of its rejection replay (<see cref="FrontEndTraversalObservations.StructuralPreflightEdges"/>),
    /// the edges of the prefix accounting (<see cref="FrontEndTraversalObservations.DeferredRegionPrefixEdges"/>), and each
    /// cancellation checkpoint they reach (<see cref="FrontEndCancellationCheckpoint.EvaluatorDeferredAdmission"/>), whose
    /// <see cref="FrontEndTraversalObservations.CheckpointReached"/> hook a test uses to cancel at a known block. Admissions
    /// are serialized by their run's gate, so one observer is never written concurrently. Supplied by the measuring test;
    /// <c>null</c> records nothing.
    /// </summary>
    public FrontEndTraversalObservations? DeferredAdmissionTraversal { get; init; }

    /// <summary>
    /// Number of COMPLETE assignment-deconstruction binding computations begun during this run. A
    /// deconstruction group binds its shared N-capture pattern once per shared-bind execution (group,
    /// actual pattern list and source entry — <c>DeconstructionBindingExecution</c>; since OD-1 no reader
    /// or caller scope): the first demanded target performs the full bind and increments this once
    /// (whether the bind then succeeds OR fails); later targets with the same execution — from any
    /// consumer: a callback, a helper, an explicit <c>a()</c>, the owner body — reuse the shared bind and
    /// each target's projection does not increment. A target whose bind may not be shared (its source
    /// read would be a re-entrant intermediate, the run's property cache publishes nothing, or a bind of
    /// its group is already running) increments it on every such read. Demanding no target performs no
    /// bind. Two independent groups, or one source in two distinct owning invocations
    /// (two calls, two loop rounds), perform two.
    /// A fresh run starts at zero, so demanding every target of one group any number
    /// of times within one activation observes exactly one.
    /// </summary>
    public long DeconstructionFullBindCount { get; private set; }

    internal void RecordDeconstructionFullBind()
        => DeconstructionFullBindCount = checked(DeconstructionFullBindCount + 1);

    /// <summary>
    /// The run's own deconstruction shared-bind memo, recorded once when the run's root context is
    /// created, so a storage test can read how the memo holds its binds
    /// (<c>LocalOnlyCacheRetentionTests</c>). Evaluation never reads it back.
    /// </summary>
    internal Evaluation.Caching.RunScopedDeconstructionBindingCache? DeconstructionBindingCache { get; private set; }

    internal void RecordDeconstructionBindingCache(Evaluation.Caching.RunScopedDeconstructionBindingCache cache)
        => DeconstructionBindingCache = cache;

    /// <summary>
    /// Optional observer handed to every runtime duplicate-head index the run's clause-family
    /// preparations build, so a test can read that work across the whole run or cancel at a known
    /// checkpoint through <see cref="PatternComparisonObservations.CheckpointReached"/>. Supplied by
    /// the measuring test; <c>null</c> records nothing.
    /// </summary>
    public PatternComparisonObservations? FamilyDuplicateIndex { get; init; }

    /// <summary>
    /// Number of clause-family preparations COMPLETED during this run: one per distinct branch-list
    /// reference whose duplicate-head verdict (and, when duplicate-free, translated heads) the run
    /// decided. Wired copies of one family share their list and so one preparation, however many
    /// calls reach them; a <c>with { Branches = … }</c> copy is prepared separately. A cancelled
    /// preparation completes nothing and is not counted.
    /// </summary>
    public long ClauseFamilyPreparationCount => Interlocked.Read(ref _clauseFamilyPreparationCount);

    private long _clauseFamilyPreparationCount;

    internal void RecordClauseFamilyPreparation() => Interlocked.Increment(ref _clauseFamilyPreparationCount);

    /// <summary>
    /// Number of literal clause runs (<c>Evaluator.LiteralClauseRun</c>) the run's completed clause-family
    /// preparations indexed: maximal runs of at least <c>Evaluator.MinimumLiteralClauseRunLength</c> consecutive
    /// literal-only clauses of one arity, counted once per preparation, however many calls select through them.
    /// </summary>
    public long LiteralClauseRunCount => Interlocked.Read(ref _literalClauseRunCount);

    private long _literalClauseRunCount;

    internal void RecordLiteralClauseRuns(int runs) => Interlocked.Add(ref _literalClauseRunCount, runs);

    /// <summary>
    /// Number of selections through a literal clause run's index during this run
    /// (<c>Evaluator.SelectLiteralRunClause</c>): one per family dispatch that reached a run's first clause with a
    /// supply its heads accept and whose first cell covers every position's demand checks. A run whose index the test seam
    /// <c>OrderedClauseDispatchTestSeam</c> withheld records none.
    /// </summary>
    public long LiteralClauseRunSelectionCount => Interlocked.Read(ref _literalClauseRunSelectionCount);

    private long _literalClauseRunSelectionCount;

    internal void RecordLiteralClauseRunSelection() => Interlocked.Increment(ref _literalClauseRunSelectionCount);

    /// <summary>
    /// Number of compound expression names rendered for call or dot-call diagnostics during this
    /// run. Successful calls and resource-limit errors observe zero; an ordinary error increments
    /// once for each diagnostic/context frame that actually needs the compound name. Simple
    /// identifier names reuse their existing string and do not increment.
    /// </summary>
    public long CallDiagnosticNameRenderCount { get; private set; }

    internal void RecordCallDiagnosticNameRender()
        => CallDiagnosticNameRenderCount = checked(CallDiagnosticNameRenderCount + 1);

    /// <summary>
    /// Number of open levels whose resolved providers were deduplicated during this run (Q-19 D-I,
    /// <c>Evaluator.ResolveAllOpens</c>): one per resolution of a nonempty <c>open</c> list whose every
    /// remaining written target resolved. A level is resolved once per level state
    /// (<c>Evaluator.ResolvedOpenLevel</c>: an activation, a static head entry, an alias step's head level
    /// or a static wiring of the level) and every later read of that state reuses it
    /// (<see cref="OpenLevelReuseCount"/>); a host-constructed level, which has no such state, is resolved
    /// again on every read. A level whose resolution fails indexes nothing and is never memoized.
    /// </summary>
    public long OpenProviderLevelCount { get; private set; }

    /// <summary>
    /// Number of times a lexical lookup consulted a nonempty open level during this run — the head's own
    /// level or an enclosing one: one per read per consulted level, resolved, reused or failed. With
    /// <see cref="OpenProviderLevelCount"/> and <see cref="OpenLevelReuseCount"/> it separates READS of a
    /// level from RESOLUTIONS of it.
    /// </summary>
    public long OpenLevelConsultationCount { get; private set; }

    /// <summary>
    /// The part of <see cref="OpenLevelConsultationCount"/> served by the level state's memoized providers
    /// (<c>Evaluator.ResolvedOpenLevel</c>) without resolving any target: <c>R</c> reads of one level
    /// state resolve it once and reuse it <c>R − 1</c> times.
    /// </summary>
    public long OpenLevelReuseCount { get; private set; }

    internal void RecordOpenLevelConsultation(bool reused)
    {
        OpenLevelConsultationCount = checked(OpenLevelConsultationCount + 1);
        if (reused)
            OpenLevelReuseCount = checked(OpenLevelReuseCount + 1);
    }

    /// <summary>
    /// Number of member indexes of WIDE open levels built during this run (<c>Evaluator.OpenLevelMemberIndexCache</c>):
    /// a memoized level of more than <c>Evaluator.OpenProviderLinearIndexLimit</c> providers takes the run's index
    /// of its providers' member lists on its second read, and the run builds one per distinct sequence of lists,
    /// however many level states — calls, entries, rounds, member calls — read through it.
    /// </summary>
    public long OpenLevelMemberIndexBuildCount { get; private set; }

    /// <summary>
    /// The members — public or not — that <see cref="OpenLevelMemberIndexBuildCount"/>'s builds visited: each build
    /// visits every member of every provider's list once.
    /// </summary>
    public long OpenLevelMemberIndexMemberCount { get; private set; }

    /// <summary>
    /// Number of wide level states that took a member index an earlier state of this run had built, so visited no
    /// member: with <see cref="OpenLevelMemberIndexBuildCount"/>, the level states read at least twice.
    /// </summary>
    public long OpenLevelMemberIndexShareCount { get; private set; }

    internal void RecordOpenLevelMemberIndex(bool built, long members)
    {
        if (built)
        {
            OpenLevelMemberIndexBuildCount = checked(OpenLevelMemberIndexBuildCount + 1);
            OpenLevelMemberIndexMemberCount = checked(OpenLevelMemberIndexMemberCount + members);
        }
        else
        {
            OpenLevelMemberIndexShareCount = checked(OpenLevelMemberIndexShareCount + 1);
        }
    }

    /// <summary>
    /// Number of resolved open targets presented to provider deduplication during this run: the
    /// written targets left after the written-key skip, each indexed once per level resolution, so a
    /// level with <c>K</c> such targets adds exactly <c>K</c>.
    /// </summary>
    public long OpenProviderIndexEntryCount { get; private set; }

    /// <summary>
    /// Number of declaration-key reference comparisons made by provider deduplication's small path
    /// during this run: a level with at most <c>Evaluator.OpenProviderLinearIndexLimit</c> targets
    /// compares each incoming provider's declaration with the earlier accepted ones' (allocation-free,
    /// at most 28 per level); a wider level hashes the key instead and adds nothing here.
    /// </summary>
    public long OpenProviderDeclarationKeyComparisonCount { get; private set; }

    /// <summary>
    /// Number of exact provider-identity comparisons (<c>Evaluator.SameRepeatedCallableIdentity</c>)
    /// made by provider deduplication during this run. Only providers of the SAME declaration are
    /// compared, so <c>K</c> distinct declarations at a level add zero.
    /// </summary>
    public long OpenProviderIdentityComparisonCount { get; private set; }

    /// <summary>
    /// The part of <see cref="OpenProviderIdentityComparisonCount"/> whose two providers have
    /// DIFFERENT declarations. Such a pair is never one provider, so the declaration index never makes
    /// one and this stays zero; the former pairwise scan made <c>K(K−1)/2</c> per level of <c>K</c>
    /// distinct declarations.
    /// </summary>
    public long OpenProviderCrossDeclarationIdentityComparisonCount { get; private set; }

    internal void RecordOpenProviderIndexing(int entries, int keyComparisons, int identityComparisons, int crossDeclarationIdentityComparisons)
    {
        OpenProviderLevelCount = checked(OpenProviderLevelCount + 1);
        OpenProviderIndexEntryCount = checked(OpenProviderIndexEntryCount + entries);
        OpenProviderDeclarationKeyComparisonCount = checked(OpenProviderDeclarationKeyComparisonCount + keyComparisons);
        OpenProviderIdentityComparisonCount = checked(OpenProviderIdentityComparisonCount + identityComparisons);
        OpenProviderCrossDeclarationIdentityComparisonCount = checked(OpenProviderCrossDeclarationIdentityComparisonCount + crossDeclarationIdentityComparisons);
    }

    /// <summary>
    /// Number of per-item <c>filter</c> diagnostic contexts constructed during this run.
    /// Passing predicates and resource-limit failures observe zero; an ordinary predicate
    /// failure increments exactly once for the failing item whose context is attached.
    /// This pins the error-path-only ownership of item rendering in both generic and fused
    /// filter execution without relying on allocation or timing thresholds.
    /// </summary>
    public long FilterItemDiagnosticContextCount { get; private set; }

    internal void RecordFilterItemDiagnosticContext()
        => FilterItemDiagnosticContextCount = checked(FilterItemDiagnosticContextCount + 1);

    /// <summary>
    /// Number of <c>SequencePipelineEvaluationServices</c> bundles constructed during this run.
    /// The bundle's captured delegates are the sequence-pipeline probe's only allocations, and the
    /// closure-bearing helper is entered only AFTER the production allocation-free syntactic recognition gate
    /// (<c>SequencePipelineOptimizer.TryRecognize</c>) accepted the invocation on a fusion-enabled
    /// run. Ordinary non-candidate calls and dot-calls therefore observe zero — however many are
    /// evaluated — as does every fusion-disabled run; a recognized filter-count pipeline observes
    /// exactly one construction per evaluation of the pipeline expression (whether fusion then
    /// executes or the lookup stage falls back to the generic path). This pins the
    /// recognition-before-services dispatch ordering without relying on CLR allocation totals;
    /// the separate helper boundary additionally prevents compiler-hoisted closure allocation on
    /// a miss even when the counter remains zero. An explicitly attached internal diagnostics
    /// collector may independently allocate its own diagnostic records.
    /// </summary>
    public long SequencePipelineServiceConstructionCount { get; private set; }

    internal void RecordSequencePipelineServiceConstruction()
        => SequencePipelineServiceConstructionCount = checked(SequencePipelineServiceConstructionCount + 1);

    /// <summary>
    /// Number of GENERIC loop-step binding preparations performed during this run: each increment is
    /// one <c>Evaluator.PrepareGenericLoopStep</c> call — the loop-invariant snapshot of the step's
    /// binding contract and its need-pattern view (each iteration then binds the state and shadows
    /// the inherited environments itself). The generic loop strategy prepares exactly ONCE per loop
    /// invocation that runs at least one iteration (sync and async twins alike), never once per
    /// iteration, and a zero-iteration loop (<c>repeat</c> with count 0, whose entry returns before
    /// the generic loop body) prepares zero times. Handover from the optimized strategy re-enters the generic loop as
    /// a fresh invocation and therefore prepares once more; nested or recursive loops prepare once
    /// per invocation each. Optimized-strategy iterations never touch this counter.
    /// </summary>
    public long GenericLoopStepBindingPreparationCount { get; private set; }

    internal void RecordGenericLoopStepBindingPreparation()
        => GenericLoopStepBindingPreparationCount = checked(GenericLoopStepBindingPreparationCount + 1);

    /// <summary>
    /// Number of generic handover output-slot materializations performed by the OPTIMIZED loop
    /// strategy during this run: each increment is one
    /// <c>LoopOptimizer.MaterializeGenericHandoverSlots</c> call, which rebuilds the generic
    /// evaluator's output-slot list from the iteration's retained planned values. Materialization
    /// happens only inside an actual handover branch — an iteration output that did not emit exactly
    /// one value, or a committed next state whose arity grew — so an optimized loop that runs to
    /// completion without handover observes zero regardless of iteration count, and a loop that hands
    /// over observes exactly one materialization at the handover point. Generic-strategy iterations
    /// never touch this counter.
    /// </summary>
    public long OptimizedLoopHandoverMaterializationCount { get; private set; }

    internal void RecordOptimizedLoopHandoverMaterialization()
        => OptimizedLoopHandoverMaterializationCount = checked(OptimizedLoopHandoverMaterializationCount + 1);

    /// <summary>
    /// Number of invocation plans created during this run: one per call-shaped supplied
    /// cell allocated while the run retains invocation plans (<c>Evaluator.SupplyCell</c>).
    /// A transported parameter cell is the original cell and creates none; a non-retaining run observes zero.
    /// </summary>
    public long InvocationPlanCount { get; private set; }

    internal void RecordInvocationPlan()
        => InvocationPlanCount = checked(InvocationPlanCount + 1);

    /// <summary>
    /// Number of invocation-plan supply preparations performed during this run: one per
    /// plan whose supply was ever formed, whatever its outcome, however many executions (VALUE and
    /// invocations) ran over it.
    /// </summary>
    public long PlanSupplyFormationCount { get; private set; }

    // PERF-STATE-1: the exact per-plan formation witness, keyed by plan identity. It lives here rather
    // than on every plan so an unobserved plan carries no test-only counter. A plan records into the
    // observations of the run that created it (its caller context's), from its first formation on.
    // STORAGE FOLLOWS LIFETIME (identity-store retention audit, 2026-11-16): each plan is the partition of
    // its own witness, held weakly and reclaimed promptly, so a witness dies with its plan. Only a holder of
    // the plan can read it (PlanSupplyFormations), so a dead plan's witness could never be read again; a
    // strong dictionary kept every plan of an observed run — its caller context, values and supply — alive
    // until the run ended (about 1.4 KB per round of a META loop). The count above is unaffected.
    private readonly Evaluation.Caching.PartitionedMap<Evaluator.InvocationPlan, System.Runtime.CompilerServices.StrongBox<int>> _planSupplyFormations =
        new(ReferenceEqualityComparer.Instance, static plan => plan);

    // Called by the plan's ONE supply publication (Evaluator.PublishPlanSupply) before the outcome is
    // published, so a reader that sees the outcome also sees the count. A run is ONE sequential flow
    // (EvaluationBudget: a continuation may resume it on another thread, but no two operations of one
    // run execute at once), so a run never contends for this lock. It stays for the internal test
    // seams that wait on, and read, one plan's preparation from other threads while the run is
    // suspended (CallPlanRetentionTests): the count and its per-plan entry move together for them.
    internal void RecordPlanSupplyFormation(Evaluator.InvocationPlan plan)
    {
        lock (_planSupplyFormations)
        {
            if (!_planSupplyFormations.TryGetValue(plan, out var formations))
                _planSupplyFormations.TryAdd(plan, formations = new());
            formations.Value = checked(formations.Value + 1);
            PlanSupplyFormationCount = checked(PlanSupplyFormationCount + 1);
        }
    }

    /// <summary>How many times <paramref name="plan"/> formed its supply in this run (at most once).</summary>
    internal int PlanSupplyFormations(Evaluator.InvocationPlan plan)
    {
        lock (_planSupplyFormations)
            return _planSupplyFormations.TryGetValue(plan, out var formations) ? formations.Value : 0;
    }

    /// <summary>
    /// TEST SEAM: the number of formation witnesses whose plan is still reachable (a dead plan's witness is
    /// never counted). Retention tests read it after a forced full collection.
    /// </summary>
    internal int LivePlanSupplyWitnessCount()
    {
        lock (_planSupplyFormations)
            return _planSupplyFormations.LivePartitionCount();
    }
}
