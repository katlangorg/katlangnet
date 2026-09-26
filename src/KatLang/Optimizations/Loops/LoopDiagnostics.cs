namespace KatLang.Optimizations.Loops;

internal sealed class LoopOptimizationDiagnostics
{
    /// <summary>Forwarding slots actually inspected during plan construction (FE-2).</summary>
    public long TempCallArgumentSlotsExamined { get; private set; }

    internal void RecordTempCallArgumentSlotExamined() => TempCallArgumentSlotsExamined++;

    private readonly Dictionary<string, long> _fallbackReasons = new(StringComparer.Ordinal);
    private readonly Dictionary<string, LoopPlanDiagnosticBuilder> _loopPlans = new(StringComparer.Ordinal);

    public long OptimizedLoopHits { get; private set; }

    public long OptimizedLoopFallbacks { get; private set; }

    public long LoopPlanBuilds { get; private set; }

    public long LoopExecutions { get; private set; }

    public long LoopIterations { get; private set; }

    public long PlannedExpressionHits { get; private set; }

    public long PlannedExpressionFallbacks { get; private set; }

    public long GenericExpressionEvaluationsInsideOptimizedLoops { get; private set; }

    public long PlannedBuiltinOperations { get; private set; }

    public long CountedParameterReferencesPlanned { get; private set; }

    public long CountedParameterReferencesFallbacks { get; private set; }

    public IReadOnlyDictionary<string, long> FallbackReasons => _fallbackReasons;

    internal void RecordOptimizedLoopHit()
        => OptimizedLoopHits++;

    internal void RecordOptimizedLoopFallback(string reason)
    {
        OptimizedLoopFallbacks++;
        RecordFallbackReason(reason);
    }

    internal void RecordLoopPlanBuild()
        => LoopPlanBuilds++;

    internal void RecordLoopExecution()
        => LoopExecutions++;

    internal void RecordLoopIteration()
        => LoopIterations++;

    internal void RecordPlannedExpressionHit()
        => PlannedExpressionHits++;

    internal void RecordPlannedExpressionFallback(string reason)
    {
        PlannedExpressionFallbacks++;
        RecordFallbackReason(reason);
    }

    internal void RecordGenericExpressionEvaluationInsideOptimizedLoop()
        => GenericExpressionEvaluationsInsideOptimizedLoops++;

    internal void RecordPlannedBuiltinOperation()
        => PlannedBuiltinOperations++;

    internal void RecordCountedParameterReferencePlanned()
        => CountedParameterReferencesPlanned++;

    internal void RecordCountedParameterReferenceFallback(string reason)
    {
        CountedParameterReferencesFallbacks++;
        RecordFallbackReason(reason);
    }

    internal void RecordFallbackReason(string reason)
    {
        _fallbackReasons.TryGetValue(reason, out var count);
        _fallbackReasons[reason] = count + 1;
    }

    internal string RecordLoopPlanDiagnostic(
        string identity,
        string kind,
        int stateArity,
        bool optimized,
        string? fallbackReason,
        IReadOnlyList<LoopTempDiagnosticSnapshot> temps,
        IReadOnlyList<LoopExpressionDiagnosticSnapshot> expressions)
    {
        var key = LoopPlanDiagnosticKey(identity, kind, stateArity, optimized, fallbackReason, temps, expressions);
        if (!_loopPlans.TryGetValue(key, out var builder))
        {
            builder = new LoopPlanDiagnosticBuilder(
                identity,
                kind,
                stateArity,
                optimized,
                fallbackReason,
                temps,
                expressions);
            _loopPlans.Add(key, builder);
        }

        builder.BuildCount++;
        return key;
    }

    internal void RecordLoopPlanExecution(string? key)
    {
        if (key is not null && _loopPlans.TryGetValue(key, out var builder))
            builder.ExecutionCount++;
    }

    public LoopOptimizationDiagnosticsSnapshot GetSnapshot()
        => new(
            OptimizedLoopHits,
            OptimizedLoopFallbacks,
            LoopPlanBuilds,
            LoopExecutions,
            LoopIterations,
            PlannedExpressionHits,
            PlannedExpressionFallbacks,
            GenericExpressionEvaluationsInsideOptimizedLoops,
            PlannedBuiltinOperations,
            CountedParameterReferencesPlanned,
            CountedParameterReferencesFallbacks,
            new Dictionary<string, long>(_fallbackReasons, StringComparer.Ordinal),
            _loopPlans.Values
                .Select(builder => builder.ToSnapshot())
                .OrderBy(plan => plan.Identity, StringComparer.Ordinal)
                .ThenBy(plan => plan.Kind, StringComparer.Ordinal)
                .ThenBy(plan => plan.StateArity)
                .ToList());

    private static string LoopPlanDiagnosticKey(
        string identity,
        string kind,
        int stateArity,
        bool optimized,
        string? fallbackReason,
        IReadOnlyList<LoopTempDiagnosticSnapshot> temps,
        IReadOnlyList<LoopExpressionDiagnosticSnapshot> expressions)
    {
        var tempKey = string.Join(
            "|",
            temps.Select(temp =>
                $"{temp.Name}:{temp.Planned}:{temp.PlanSummary}:{temp.FallbackReason}"));
        var expressionKey = string.Join(
            "|",
            expressions.Select(expression =>
                $"{expression.Role}:{expression.Index?.ToString(System.Globalization.CultureInfo.InvariantCulture) ?? "-"}:{expression.Planned}:{expression.PlanSummary}:{expression.FallbackReason}"));
        return $"{identity}|{kind}|{stateArity}|{optimized}|{fallbackReason}|{tempKey}|{expressionKey}";
    }

    private sealed class LoopPlanDiagnosticBuilder(
        string identity,
        string kind,
        int stateArity,
        bool optimized,
        string? fallbackReason,
        IReadOnlyList<LoopTempDiagnosticSnapshot> temps,
        IReadOnlyList<LoopExpressionDiagnosticSnapshot> expressions)
    {
        public long BuildCount { get; set; }

        public long ExecutionCount { get; set; }

        public LoopPlanDiagnosticSnapshot ToSnapshot()
            => new(
                identity,
                kind,
                stateArity,
                optimized,
                BuildCount,
                ExecutionCount,
                fallbackReason,
                temps,
                expressions);
    }
}

internal sealed record LoopOptimizationDiagnosticsSnapshot(
    long OptimizedLoopHits,
    long OptimizedLoopFallbacks,
    long LoopPlanBuilds,
    long LoopExecutions,
    long LoopIterations,
    long PlannedExpressionHits,
    long PlannedExpressionFallbacks,
    long GenericExpressionEvaluationsInsideOptimizedLoops,
    long PlannedBuiltinOperations,
    long CountedParameterReferencesPlanned,
    long CountedParameterReferencesFallbacks,
    IReadOnlyDictionary<string, long> FallbackReasons,
    IReadOnlyList<LoopPlanDiagnosticSnapshot> LoopPlans);

internal sealed record LoopPlanDiagnosticSnapshot(
    string Identity,
    string Kind,
    int StateArity,
    bool Optimized,
    long BuildCount,
    long ExecutionCount,
    string? FallbackReason,
    IReadOnlyList<LoopTempDiagnosticSnapshot> Temps,
    IReadOnlyList<LoopExpressionDiagnosticSnapshot> Expressions);

internal sealed record LoopTempDiagnosticSnapshot(
    string Name,
    bool Planned,
    string? PlanSummary,
    string? FallbackReason);

internal sealed record LoopExpressionDiagnosticSnapshot(
    string Role,
    int? Index,
    bool Planned,
    string? PlanSummary,
    string? FallbackReason);
