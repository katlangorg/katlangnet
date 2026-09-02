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

/// <summary>
/// The evaluator services a recognized pipeline consumes: exactly the members the
/// optimizer reads, one delegate each. A generic (non-range) source is evaluated
/// ONLY through <see cref="EvaluateDotReceiverIterationItems"/> — the plain
/// <c>count(filter(src, pred))</c> form fuses direct builtin-range sources alone
/// and falls back before touching any other source, so it needs no plain-source
/// evaluation service; a member no pipeline reads must not be added here, because
/// every member costs one captured delegate per recognized pipeline.
/// </summary>
internal readonly record struct SequencePipelineEvaluationServices(
    Func<Expr.DotCall, BuiltinId, string?> GetDotCallLexicalBuiltinFallbackReason,
    Func<Expr, EvalResult<IReadOnlyList<Evaluator.CountedResult>>> EvaluateDotReceiverIterationItems,
    Func<OutputBundle, EvalResult<IReadOnlyList<Algorithm>>> ResolveArgumentAlgorithms,
    Func<Expr, EvalResult<Algorithm>> ResolveAlgorithm,
    Func<Expr, OutputBundle, SourceSpan?, EvalResult<Evaluator.InclusiveRange>> EvaluateRangeCallArguments);

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
