namespace KatLang.Optimizations.Loops;

/// <summary>
/// Invocation-local planning facts, never runtime values. Several call sites can share one
/// forwarding bundle (FE-2), including across output rows whose expression memos are separate.
/// Matching also depends on the selected temp's ordered parameter names, so both keys use
/// reference identity. Each temp plan owns the parameter-name snapshot built for this invocation.
/// This memo dies when plan construction returns; no memo is stored on the syntax or the plan.
/// </summary>
internal sealed class LoopTempCallArgumentMemo
{
    private readonly Dictionary<LoopTempPlan, Dictionary<OutputBundle, (bool Matches, SourceSpan? LimitSpan)>> _facts
        = new(ReferenceEqualityComparer.Instance);

    public (bool Matches, SourceSpan? LimitSpan) Get(
        OutputBundle arguments, LoopTempPlan temp, LoopOptimizationDiagnostics? diagnostics)
    {
        if (!_facts.TryGetValue(temp, out var bundles))
            _facts.Add(temp, bundles = new(ReferenceEqualityComparer.Instance));
        if (bundles.TryGetValue(arguments, out var known))
            return known;

        var matches = arguments.Count == temp.ParameterNames.Count;
        for (var index = 0; matches && index < arguments.Count; index++)
        {
            diagnostics?.RecordTempCallArgumentSlotExamined();
            matches = arguments[index] is Expr.Param(var name) && name == temp.ParameterNames[index];
        }

        // The generic span policy scans for the first positioned slot. Spanless synthesized
        // bundles must not repeat that L-wide scan for each call either. The call/callee and
        // enclosing diagnostic boundary remain per reference.
        var result = (matches, matches ? Evaluator.UserCallLimitSpan(arguments) : null);
        bundles.Add(arguments, result);
        return result;
    }
}
