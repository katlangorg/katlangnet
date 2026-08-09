using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

/// <summary>
/// Optimizer-transparency regressions for the fused <c>filter -&gt; count</c>
/// pipeline's DIAGNOSTIC SPAN.
///
/// <para>Fusion elides the <c>filter(...)</c> expression node, so the generic
/// evaluator's span attribution for that node — <c>WithSpan(filterExpr.Span, ...)</c>
/// at its dispatch site — never ran. A stage error that arrives WITHOUT a span (a
/// callback <c>BadArity</c>, for example) therefore floated up to the enclosing
/// <c>count(...)</c> expression and was stamped with the <em>count</em> span:
/// <c>count(filter(range(1, 3), F))</c> with <c>F(x) = x, x + 1</c> reported
/// <c>[2,1]-[2,29]</c> optimized versus <c>[2,7]-[2,28]</c> generic.</para>
///
/// <para>The sequence pipeline optimizer is a C#-only execution strategy (see
/// <c>src/KatLang/SEMANTIC-ALIGNMENT.md</c>), so its contract is pinned here as
/// exact optimized-vs-generic diagnostic equivalence across all three recognized
/// syntax forms and both source-plan kinds — never by disabling fusion.</para>
/// </summary>
public class FilterCountFusionSpanParityTests
{
    private static Expr Program(string source) => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private static (EvalResult<Result> Result, SequencePipelineDiagnosticsSnapshot Stats) Run(
        string source,
        bool enableSequencePipelineOptimization)
    {
        var diagnostics = new SequencePipelineDiagnostics();
        var result = Evaluator.Run(
            Program(source),
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: enableSequencePipelineOptimization,
            sequenceDiagnostics: diagnostics);
        return (result, diagnostics.GetSnapshot());
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        return error;
    }

    private static IReadOnlyList<string> ContextChain(EvalError error)
    {
        var chain = new List<string>();
        while (error is EvalError.WithContext context)
        {
            chain.Add(context.ErrorContext.ToLegacyString());
            error = context.Inner;
        }

        return chain;
    }

    private sealed record Diagnostic(
        string Kind,
        string Message,
        IReadOnlyList<string> ContextChain,
        int? StartLine,
        int? StartColumn,
        int? EndLine,
        int? EndColumn);

    private static Diagnostic Describe(EvalError error)
    {
        var rendered = KatLangError.FromEvalError(error);
        return new Diagnostic(
            Innermost(error).GetType().Name,
            rendered.Message,
            ContextChain(error),
            rendered.StartLine,
            rendered.StartColumn,
            rendered.EndLine,
            rendered.EndColumn);
    }

    private static void AssertSameDiagnostic(Diagnostic generic, Diagnostic optimized)
    {
        Assert.Equal(generic.Kind, optimized.Kind);
        Assert.Equal(generic.ContextChain, optimized.ContextChain);
        Assert.Equal(generic.Message, optimized.Message);
        Assert.Equal(
            (generic.StartLine, generic.StartColumn, generic.EndLine, generic.EndColumn),
            (optimized.StartLine, optimized.StartColumn, optimized.EndLine, optimized.EndColumn));
    }

    /// <summary>
    /// Runs a failing program with fusion off and on and asserts the complete
    /// observable diagnostic is identical. <paramref name="expectFusion"/> demands the
    /// optimized run actually fused (so the assertion is not vacuous) and that the
    /// generic run did not.
    /// </summary>
    private static Diagnostic AssertFusionTransparentFailure(string source, bool expectFusion = true)
    {
        var (generic, genericStats) = Run(source, enableSequencePipelineOptimization: false);
        Assert.True(generic.IsError, $"Expected generic failure but got: {(generic.IsError ? null : generic.Value)}");
        Assert.Equal(0, genericStats.FilterCountFusionHits);

        var (optimized, optimizedStats) = Run(source, enableSequencePipelineOptimization: true);
        Assert.True(optimized.IsError, $"Expected optimized failure but got: {(optimized.IsError ? null : optimized.Value)}");
        Assert.Equal(expectFusion ? 1 : 0, optimizedStats.FilterCountFusionHits);

        var describedGeneric = Describe(generic.Error);
        var describedOptimized = Describe(optimized.Error);
        AssertSameDiagnostic(describedGeneric, describedOptimized);
        return describedOptimized;
    }

    // ── The reported reproducer, with its absolute expected span ─────────────

    [Fact]
    public void FusedFilterCount_SpanlessPredicateFailure_ReportsTheFilterSpanNotTheCountSpan()
    {
        // `count(filter(range(1, 3), F))` on line 2: the enclosing `count(...)`
        // expression is columns 1..29 and the elided `filter(...)` expression is
        // columns 7..28. The reported span must be the filter expression's.
        var source = """
            F(x) = x, x + 1
            count(filter(range(1, 3), F))
            """;

        var diagnostic = AssertFusionTransparentFailure(source);

        Assert.Equal(nameof(EvalError.BadArity), diagnostic.Kind);
        Assert.Equal(2, diagnostic.StartLine);
        Assert.Equal(7, diagnostic.StartColumn);
        Assert.Equal(2, diagnostic.EndLine);
        Assert.Equal(28, diagnostic.EndColumn);
    }

    // ── All three recognized syntax forms x both error classes ──────────────

    /// <summary>
    /// Each case is (form label, source). Both source-plan kinds are exercised: a
    /// direct <c>range(...)</c> plan and a generic collection plan (a property).
    /// </summary>
    public static TheoryData<string, string, string> SpanlessPredicateFailures()
    {
        var data = new TheoryData<string, string, string>();

        // A predicate emitting two values is a span-less callback BadArity.
        const string badPredicate = "F(x) = x, x + 1";

        data.Add("dot-filter-dot-count", "direct range", $"{badPredicate}\nrange(1, 3).filter(F).count");
        data.Add("plain-count-dot-filter", "direct range", $"{badPredicate}\ncount(range(1, 3).filter(F))");
        data.Add("plain-count-plain-filter", "direct range", $"{badPredicate}\ncount(filter(range(1, 3), F))");

        data.Add("dot-filter-dot-count", "generic source", $"{badPredicate}\nData = 1, 2, 3\nData.filter(F).count");
        data.Add("plain-count-dot-filter", "generic source", $"{badPredicate}\nData = 1, 2, 3\ncount(Data.filter(F))");

        return data;
    }

    [Theory]
    [MemberData(nameof(SpanlessPredicateFailures))]
    public void FusedFilterCount_SpanlessFailure_MatchesGenericSpanExactly(string form, string sourceKind, string source)
    {
        Assert.False(string.IsNullOrEmpty(form));
        Assert.False(string.IsNullOrEmpty(sourceKind));

        var diagnostic = AssertFusionTransparentFailure(source);

        Assert.Equal(nameof(EvalError.BadArity), diagnostic.Kind);

        // The failure is attributed to the LAST line's filter expression, and never
        // starts at the enclosing `count(` for a `count(...)`-outermost form.
        var lines = source.Split('\n');
        Assert.Equal(lines.Length, diagnostic.StartLine);
        Assert.NotNull(diagnostic.StartColumn);
        var lastLine = lines[^1];
        var filterStart = lastLine.StartsWith("count(", StringComparison.Ordinal) ? 7 : 1;
        Assert.Equal(filterStart, diagnostic.StartColumn);
    }

    /// <summary>
    /// The <c>count(filter(SOURCE, pred))</c> form only fuses a direct builtin-range
    /// source; a generic source is deferred to the generic evaluator. Pinned so the
    /// theory above is not silently claiming coverage it does not have, and so the
    /// deferred path stays diagnostically identical.
    /// </summary>
    [Fact]
    public void PlainFilterCount_GenericSource_IsNotFusedAndStillAgrees()
    {
        var source = """
            F(x) = x, x + 1
            Data = 1, 2, 3
            count(filter(Data, F))
            """;

        var diagnostic = AssertFusionTransparentFailure(source, expectFusion: false);

        Assert.Equal(nameof(EvalError.BadArity), diagnostic.Kind);
        Assert.Equal(3, diagnostic.StartLine);
        Assert.Equal(7, diagnostic.StartColumn);
    }

    public static TheoryData<string, string, string> SpannedPredicateFailures()
    {
        var data = new TheoryData<string, string, string>();

        // A predicate dividing by zero fails with the `x / 0` operand's OWN span.
        const string failingPredicate = "F(x) = x / 0";

        data.Add("dot-filter-dot-count", "direct range", $"{failingPredicate}\nrange(1, 3).filter(F).count");
        data.Add("plain-count-dot-filter", "direct range", $"{failingPredicate}\ncount(range(1, 3).filter(F))");
        data.Add("plain-count-plain-filter", "direct range", $"{failingPredicate}\ncount(filter(range(1, 3), F))");

        data.Add("dot-filter-dot-count", "generic source", $"{failingPredicate}\nData = 1, 2, 3\nData.filter(F).count");
        data.Add("plain-count-dot-filter", "generic source", $"{failingPredicate}\nData = 1, 2, 3\ncount(Data.filter(F))");

        return data;
    }

    [Theory]
    [MemberData(nameof(SpannedPredicateFailures))]
    public void FusedFilterCount_AlreadySpannedFailure_KeepsTheInnerSpan(string form, string sourceKind, string source)
    {
        Assert.False(string.IsNullOrEmpty(form));
        Assert.False(string.IsNullOrEmpty(sourceKind));

        var diagnostic = AssertFusionTransparentFailure(source);

        Assert.Equal(nameof(EvalError.DivByZero), diagnostic.Kind);

        // The inner `x / 0` operand is on line 1 (`F(x) = x / 0`, columns 8..12), so
        // neither the filter span nor the count span may replace it.
        Assert.Equal(1, diagnostic.StartLine);
        Assert.Equal(8, diagnostic.StartColumn);
        Assert.Equal(1, diagnostic.EndLine);
    }

    // ── A later outer evaluator layer must not re-span the failure ───────────

    [Fact]
    public void FusedFilterCount_InsideAnEnclosingExpression_KeepsTheFilterSpan()
    {
        // The fused pipeline is an operand of a binary expression inside a property,
        // so several outer evaluator layers run after it fails. None may re-span the
        // error onto the enclosing expression, the property, or the report row.
        var source = """
            F(x) = x, x + 1
            Total = count(filter(range(1, 3), F)) + 100
            Total
            """;

        var diagnostic = AssertFusionTransparentFailure(source);

        Assert.Equal(nameof(EvalError.BadArity), diagnostic.Kind);

        // `Total = count(filter(range(1, 3), F)) + 100`: `count(` starts at column 9,
        // so the elided `filter(...)` starts at column 15 and ends at column 36.
        Assert.Equal(2, diagnostic.StartLine);
        Assert.Equal(15, diagnostic.StartColumn);
        Assert.Equal(2, diagnostic.EndLine);
        Assert.Equal(36, diagnostic.EndColumn);
    }

    // ── Preserved behavior: values, callback calls, fusion eligibility ───────

    [Fact]
    public void FusedFilterCount_SuccessfulRuns_AreUnchangedAndStillFuse()
    {
        var sources = new[]
        {
            "IsEven = x mod 2 == 0\nrange(1, 10).filter(IsEven).count",
            "IsEven = x mod 2 == 0\ncount(range(1, 10).filter(IsEven))",
            "IsEven = x mod 2 == 0\ncount(filter(range(1, 10), IsEven))",
        };

        foreach (var source in sources)
        {
            var (generic, genericStats) = Run(source, enableSequencePipelineOptimization: false);
            Assert.False(generic.IsError, $"Expected generic success for `{source}` but got: {(generic.IsError ? generic.Error : null)}");
            Assert.Equal([5m], generic.Value.ToAtoms());
            Assert.Equal(0, genericStats.FilterCountFusionHits);

            var (optimized, optimizedStats) = Run(source, enableSequencePipelineOptimization: true);
            Assert.False(optimized.IsError, $"Expected optimized success for `{source}` but got: {(optimized.IsError ? optimized.Error : null)}");
            Assert.Equal([5m], optimized.Value.ToAtoms());
            Assert.Equal(1, optimizedStats.FilterCountFusionHits);
        }
    }

    [Fact]
    public void FusedFilterCount_FailingRun_KeepsItsPredicateCallCountAndPlanShape()
    {
        // Pins the operational shape of the fused failing run so correcting the span
        // cannot change how much work the pipeline does or when it stops: the very
        // first source item fails the predicate, so exactly one predicate call runs
        // and nothing is materialized.
        var source = """
            F(x) = x, x + 1
            count(filter(range(1, 3), F))
            """;

        var (result, stats) = Run(source, enableSequencePipelineOptimization: true);

        Assert.True(result.IsError);
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(1, stats.DirectRangeFusionHits);
        Assert.Equal(0, stats.FilterCountFusionFallbacks);
        Assert.Equal(1, stats.FilterCountPredicateCalls);

        var pipeline = Assert.Single(stats.Pipelines);
        Assert.True(pipeline.Optimized, $"Expected a fused pipeline, got fallback: {pipeline.FallbackReason}");
        Assert.Equal("plain-count-plain-filter", pipeline.Form);
        Assert.Equal(SequencePipelineOptimizer.FilterCountFusion, pipeline.Fusion);
        Assert.Equal("builtin range", pipeline.SourceKind);
        Assert.Equal(1, pipeline.PredicateCalls);
    }
}
