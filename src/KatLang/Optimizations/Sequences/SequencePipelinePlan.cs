namespace KatLang.Optimizations.Sequences;

internal enum FilterCountPipelineForm
{
    DotFilterDotCount,
    PlainCountDotFilter,
    PlainCountPlainFilter,
}

internal enum SequencePipelineInvocationKind
{
    DotCall,
    PlainCall,
}

internal readonly record struct SequencePipelineInvocation(
    SequencePipelineInvocationKind Kind,
    Expr.DotCall? Dot,
    Expr? PlainFunction,
    OutputBundle? PlainArgs,
    Algorithm? PlainCallee)
{
    // The dot invocation carries its ORIGINAL node so recognizers and
    // legality probes consume the elaborated dot-edge facts (member name,
    // lexical fallback) instead of loose pieces.
    public Expr? DotTarget => Dot?.Target;

    public string? DotName => Dot?.Name;

    public OutputBundle? DotArgs => Dot?.Args;

    internal static SequencePipelineInvocation DotCall(Expr.DotCall dotCall)
        => new(
            SequencePipelineInvocationKind.DotCall,
            Dot: dotCall,
            PlainFunction: null,
            PlainArgs: null,
            PlainCallee: null);

    internal static SequencePipelineInvocation PlainCall(
        Expr function,
        OutputBundle args,
        Algorithm callee)
        => new(
            SequencePipelineInvocationKind.PlainCall,
            Dot: null,
            PlainFunction: function,
            PlainArgs: args,
            PlainCallee: callee);
}

internal readonly record struct SequencePipelineEvaluationServices(
    Func<Expr.DotCall, BuiltinId, string?> GetDotCallLexicalBuiltinFallbackReason,
    Func<Expr, EvalResult<IReadOnlyList<Evaluator.CountedResult>>> EvaluateDotReceiverIterationItems,
    Func<IReadOnlyList<Algorithm>, EvalResult<IReadOnlyList<Evaluator.CountedResult>>> EvaluateSequenceIterationItems,
    Func<OutputBundle, EvalResult<IReadOnlyList<Algorithm>>> ResolveArgumentAlgorithms,
    Func<Expr, EvalResult<Algorithm>> ResolveAlgorithm,
    Func<Expr, OutputBundle, SourceSpan?, EvalResult<Evaluator.InclusiveRange>> EvaluateRangeCallArguments);

internal readonly record struct SequencePipelineRangeSourceEvaluation(
    bool IsDirectRange,
    Evaluator.InclusiveRange Range,
    string FallbackReason)
{
    internal static SequencePipelineRangeSourceEvaluation Direct(Evaluator.InclusiveRange range)
        => new(true, range, "");

    internal static SequencePipelineRangeSourceEvaluation Fallback(string reason)
        => new(false, default, reason);
}

internal abstract record FilterCountSourcePlan
{
    public sealed record Generic(
        IReadOnlyList<Evaluator.CountedResult> SourceItems,
        string DirectRangeFallbackReason) : FilterCountSourcePlan;

    public sealed record DirectRange(Evaluator.InclusiveRange Range) : FilterCountSourcePlan;
}

/// <summary>
/// The recognized surface syntax of a filter-count pipeline.
/// <para><paramref name="FilterExpression"/> is the ORIGINAL <c>filter(...)</c> /
/// <c>....filter(...)</c> expression node that fusion elides. The generic evaluator
/// dispatches that node through <c>WithSpan(filterExpr.Span, ...)</c>, so the fused
/// pipeline must carry it to reproduce the same span attribution; without it a
/// span-less stage error is stamped with the ENCLOSING <c>count(...)</c> span.</para>
/// </summary>
internal readonly record struct FilterCountPipelineSyntax(
    FilterCountPipelineForm Form,
    Expr Source,
    Expr FilterExpression,
    OutputBundle? DotFilterArgs,
    Expr? PlainFilterFunction,
    OutputBundle? PlainFilterArgs);

internal sealed record FilterCountPipelinePlan(
    Expr Source,
    FilterCountSourcePlan SourcePlan,
    Algorithm Predicate,
    FilterCountPipelineForm FormForDiagnostics,
    Expr? PredicateExpression,
    FilterCountPipelineSyntax EvaluationSyntax,
    SequencePipelinePlan? Diagnostics);

internal sealed record SequencePipelinePlan(
    string Identity,
    string Summary,
    string Form,
    string Fusion,
    string SourceKind,
    string SourceSummary,
    string PredicateSummary);
