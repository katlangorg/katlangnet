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
}
