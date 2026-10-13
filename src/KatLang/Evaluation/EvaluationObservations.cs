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
    /// Number of COMPLETE assignment-deconstruction binding computations begun during this run. A
    /// deconstruction group binds its shared N-capture pattern once per (group, binding context): the
    /// first demanded target of a group performs the full bind and increments this once (whether the
    /// bind then succeeds OR fails); later targets of the same group reuse the shared bind and each
    /// target's slot projection does not increment. Demanding no target performs no bind (zero); two
    /// independent groups, or one group in two distinct call contexts, perform two. A fresh run starts
    /// at zero, so demanding every target of one group any number of times observes exactly one.
    /// </summary>
    public long DeconstructionFullBindCount { get; private set; }

    internal void RecordDeconstructionFullBind()
        => DeconstructionFullBindCount = checked(DeconstructionFullBindCount + 1);

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
}
