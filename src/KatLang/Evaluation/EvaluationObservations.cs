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
    /// Number of counted-argument reifications performed during this run: each increment is one
    /// construction of the legacy zero-parameter expression-tree wrapper around an already-evaluated
    /// argument's counted value (<c>Evaluator.CountedArgAlgorithm</c> → <c>ResultToExpr</c>, an
    /// O(value size) rebuild). The wrapper is built lazily, only when an algorithm-only consumer
    /// requests a prepared argument's algorithm channel; value-channel consumption reads
    /// <c>PreparedValue</c> directly and never reifies. An ordinary sequence-builtin dot call
    /// (<c>A.count</c>, <c>A.take(2)</c>, <c>A.map(F)</c>) therefore observes zero, while a run that
    /// routes a pre-evaluated value into an algorithm-only builtin position (for example a builtin
    /// used as a callback, whose prepared arguments reach <c>while</c>'s step slot) observes exactly
    /// one reification per requested channel.
    /// </summary>
    public long CountedArgumentReificationCount { get; private set; }

    internal void RecordCountedArgumentReification()
        => CountedArgumentReificationCount = checked(CountedArgumentReificationCount + 1);

    /// <summary>
    /// Number of structure NODES expanded across the <c>Evaluator.ResultToExpr</c> reifications of
    /// this run: the top-level structure of each conversion, plus every nested sequence or list
    /// value descended into. Leaves reify in place and record nothing, and a node reached again
    /// through a second shared reference reuses its memoized expression, so ONE top-level
    /// conversion stays bounded by the number of distinct reachable structure nodes — never the
    /// number of expanded tree paths (a shared doubling DAG of depth 40 expands ~40 nodes, not
    /// 2^40 path occurrences). One direct <c>ResultToExpr</c> call is one conversion scope. A
    /// multi-emission <c>CountedArgAlgorithm</c> wrapper is likewise ONE conversion scope across
    /// all of its emitted roots, so a deep node shared by several roots expands once for the
    /// whole wrapper. Nothing is shared between separate wrapper constructions or direct calls.
    /// </summary>
    public long ResultToExprStructureExpansionCount { get; private set; }

    internal void RecordResultToExprStructureExpansion()
        => ResultToExprStructureExpansionCount = checked(ResultToExprStructureExpansionCount + 1);

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
}
