namespace KatLang.Optimizations.Sequences;

internal sealed class SequencePipelineDiagnostics
{
    private readonly Dictionary<string, long> _fallbackReasons = new(StringComparer.Ordinal);
    private readonly Dictionary<string, SequencePipelineDiagnosticBuilder> _pipelines = new(StringComparer.Ordinal);

    public long FilterCountFusionHits { get; private set; }

    public long FilterCountFusionFallbacks { get; private set; }

    public long DirectRangeFusionHits { get; private set; }

    public long DirectRangeFusionFallbacks { get; private set; }

    public long FilterCountPredicateCalls { get; private set; }

    public long AvoidedFilteredResultMaterializations { get; private set; }

    public long AvoidedSourceMaterializations { get; private set; }

    public IReadOnlyDictionary<string, long> FallbackReasons => _fallbackReasons;

    internal void RecordFilterCountFusionHit()
        => FilterCountFusionHits++;

    internal void RecordFilterCountFusionFallback(string reason)
    {
        FilterCountFusionFallbacks++;
        RecordFallbackReason(reason);
    }

    internal void RecordDirectRangeFusionHit()
        => DirectRangeFusionHits++;

    internal void RecordDirectRangeFusionFallback(string reason)
    {
        DirectRangeFusionFallbacks++;
        RecordFallbackReason(reason);
    }

    internal void RecordFilterCountPredicateCalls(long count)
        => FilterCountPredicateCalls += count;

    internal void RecordAvoidedFilteredResultMaterialization(long itemCount)
        => AvoidedFilteredResultMaterializations += itemCount;

    internal void RecordAvoidedSourceMaterialization(long itemCount)
        => AvoidedSourceMaterializations += itemCount;

    internal void RecordFallbackReason(string reason)
    {
        _fallbackReasons.TryGetValue(reason, out var count);
        _fallbackReasons[reason] = count + 1;
    }

    internal string RecordPipelineDiagnostic(
        SequencePipelinePlan plan,
        bool optimized,
        string? fallbackReason,
        string sourceExecution,
        string? sourceExecutionFallbackReason)
    {
        var key = PipelineDiagnosticKey(plan, optimized, fallbackReason, sourceExecution, sourceExecutionFallbackReason);
        if (!_pipelines.TryGetValue(key, out var builder))
        {
            builder = new SequencePipelineDiagnosticBuilder(plan, optimized, fallbackReason, sourceExecution, sourceExecutionFallbackReason);
            _pipelines.Add(key, builder);
        }

        builder.BuildCount++;
        return key;
    }

    internal void RecordPipelineExecution(
        string? key,
        long sourceItemCount,
        long predicateCalls,
        long? resultCount,
        long avoidedFilteredResultMaterializationCount,
        long avoidedSourceMaterializationCount)
    {
        if (key is null || !_pipelines.TryGetValue(key, out var builder))
            return;

        builder.ExecutionCount++;
        builder.SourceItemCount += sourceItemCount;
        builder.PredicateCalls += predicateCalls;
        builder.ResultCount += resultCount ?? 0;
        builder.AvoidedFilteredResultMaterializationCount += avoidedFilteredResultMaterializationCount;
        builder.AvoidedSourceMaterializationCount += avoidedSourceMaterializationCount;
        builder.LastResultCount = resultCount;
    }

    public SequencePipelineDiagnosticsSnapshot GetSnapshot()
        => new(
            FilterCountFusionHits,
            FilterCountFusionFallbacks,
            DirectRangeFusionHits,
            DirectRangeFusionFallbacks,
            FilterCountPredicateCalls,
            AvoidedFilteredResultMaterializations,
            AvoidedSourceMaterializations,
            new Dictionary<string, long>(_fallbackReasons, StringComparer.Ordinal),
            _pipelines.Values
                .Select(builder => builder.ToSnapshot())
                .OrderBy(pipeline => pipeline.Identity, StringComparer.Ordinal)
                .ThenBy(pipeline => pipeline.Fusion, StringComparer.Ordinal)
                .ToList());

    private static string PipelineDiagnosticKey(
        SequencePipelinePlan plan,
        bool optimized,
        string? fallbackReason,
        string sourceExecution,
        string? sourceExecutionFallbackReason)
        => $"{plan.Identity}|{plan.Form}|{plan.Fusion}|{plan.SourceKind}|{plan.SourceSummary}|{plan.PredicateSummary}|{optimized}|{fallbackReason}|{sourceExecution}|{sourceExecutionFallbackReason}";

    private sealed class SequencePipelineDiagnosticBuilder(
        SequencePipelinePlan plan,
        bool optimized,
        string? fallbackReason,
        string sourceExecution,
        string? sourceExecutionFallbackReason)
    {
        public long BuildCount { get; set; }

        public long ExecutionCount { get; set; }

        public long SourceItemCount { get; set; }

        public long PredicateCalls { get; set; }

        public long ResultCount { get; set; }

        public long? LastResultCount { get; set; }

        public long AvoidedFilteredResultMaterializationCount { get; set; }

        public long AvoidedSourceMaterializationCount { get; set; }

        public SequencePipelineDiagnosticSnapshot ToSnapshot()
            => new(
                plan.Identity,
                plan.Summary,
                plan.Form,
                plan.Fusion,
                plan.SourceKind,
                plan.SourceSummary,
                plan.PredicateSummary,
                optimized,
                BuildCount,
                ExecutionCount,
                fallbackReason,
                sourceExecution,
                sourceExecutionFallbackReason,
                SourceItemCount,
                PredicateCalls,
                ResultCount,
                LastResultCount,
                AvoidedFilteredResultMaterializationCount,
                AvoidedSourceMaterializationCount);
    }
}

internal sealed record SequencePipelineDiagnosticsSnapshot(
    long FilterCountFusionHits,
    long FilterCountFusionFallbacks,
    long DirectRangeFusionHits,
    long DirectRangeFusionFallbacks,
    long FilterCountPredicateCalls,
    long AvoidedFilteredResultMaterializations,
    long AvoidedSourceMaterializations,
    IReadOnlyDictionary<string, long> FallbackReasons,
    IReadOnlyList<SequencePipelineDiagnosticSnapshot> Pipelines);

internal sealed record SequencePipelineDiagnosticSnapshot(
    string Identity,
    string Summary,
    string Form,
    string Fusion,
    string SourceKind,
    string SourceSummary,
    string PredicateSummary,
    bool Optimized,
    long BuildCount,
    long ExecutionCount,
    string? FallbackReason,
    string SourceExecution,
    string? SourceExecutionFallbackReason,
    long SourceItemCount,
    long PredicateCalls,
    long ResultCount,
    long? LastResultCount,
    long AvoidedFilteredResultMaterializationCount,
    long AvoidedSourceMaterializationCount);
