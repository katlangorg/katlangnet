using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorSequencePipelineTests
{
    private static (EvalResult<Result> Result, SequencePipelineDiagnosticsSnapshot Stats) EvalFullWithSequenceDiagnostics(
        string source,
        bool enableSequencePipelineOptimization = true)
    {
        var ast = ParseValidRoot(source);
        var diagnostics = new SequencePipelineDiagnostics();
        var result = Evaluator.Run(
            new Expr.AlgorithmExpr(ast),
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: enableSequencePipelineOptimization,
            sequenceDiagnostics: diagnostics);
        return (result, diagnostics.GetSnapshot());
    }

    // A root evaluation context whose call stack is the runtime prelude, so
    // builtin names (count, filter, range, ...) resolve to builtins — matching
    // the context Evaluator.Run installs. White-box optimizer tests that call
    // SequencePipelineOptimizer.TryExecute directly for a DOT pipeline need this
    // because the dot-form CountResolvesToBuiltin check resolves `count` by name
    // (unlike the plain form, which carries an explicit builtin callee).
    private static Evaluator.EvalCtx PreludeEvalCtx()
        => new(
            [BuiltinRegistry.CreateRuntimePreludeAlgorithm()],
            [],
            [],
            UncachedZeroArgPropertyResultCache.Instance,
            UncachedDeconstructionBindingCache.Instance,
            EnableLoopOptimization: true,
            LoopDiagnostics: null,
            EnableSequencePipelineOptimization: true,
            SequenceDiagnostics: null,
            Observations: null,
            Budget: EvaluationBudget.Create(null));

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_FusesDotFilterDotCount()
    {
        var source = """
            IsEven = x mod 2 == 0
            CountEven(N) = range(1, N).filter(IsEven).count
            CountEven(10)
            """;

        AssertEvalSequenceModes(source, 5);

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([5m], result.Value.ToAtoms());
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(0, stats.FilterCountFusionFallbacks);
        Assert.Equal(1, stats.DirectRangeFusionHits);
        Assert.Equal(0, stats.DirectRangeFusionFallbacks);
        Assert.Equal(10, stats.FilterCountPredicateCalls);
        Assert.Equal(5, stats.AvoidedFilteredResultMaterializations);
        Assert.Equal(10, stats.AvoidedSourceMaterializations);

        var pipeline = Assert.Single(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.Equal("dot-filter-dot-count", pipeline.Form);
        Assert.Equal("filter.count -> countWhere", pipeline.Fusion);
        Assert.Equal("builtin range", pipeline.SourceKind);
        Assert.Equal("range(...)", pipeline.SourceSummary);
        Assert.Equal("direct range iteration", pipeline.SourceExecution);
        Assert.Null(pipeline.SourceExecutionFallbackReason);
        Assert.Equal("IsEven", pipeline.PredicateSummary);
        Assert.Equal(10, pipeline.SourceItemCount);
        Assert.Equal(10, pipeline.PredicateCalls);
        Assert.Equal(5, pipeline.ResultCount);
        Assert.Equal(10, pipeline.AvoidedSourceMaterializationCount);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_SingleKeptSequenceItem_CountsKeptItem()
    {
        // filter keeps exactly one sequence-valued item. The filter result is the
        // exact list [(1, 2)], and `count` opens the lone list boundary: the count
        // is the kept-item count 1, in both the generic composition and the fused
        // filter.count path.
        var source = """
            KeepFirstPair(pair) = pair:0 == 1
            (((1, 2), (3, 4))).filter(KeepFirstPair).count
            """;

        AssertEvalSequenceModes(source, 1);

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([1m], result.Value.ToAtoms());
        Assert.Equal(1, stats.FilterCountFusionHits);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_SingleKeptEmptyItem_CountsOneKeptItem()
    {
        // A lone kept `()` stays an exact list element ([()]), so the count is
        // the kept-item count 1 in both the generic composition and the fused
        // filter.count path.
        var source = """
            KeepEmpty(x) = x.count == 0
            Values = (), 1
            Values.filter(KeepEmpty).count
            """;

        AssertEvalSequenceModes(source, 1);

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([1m], result.Value.ToAtoms());
        Assert.Equal(1, stats.FilterCountFusionHits);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_FusesPlainCountDotFilter()
    {
        // Under fixed collection-object arity the BARE one-argument form
        // count(src.filter(pred)) is the valid plain composition, and it is
        // the form the filter->count fusion recognizes.
        var source = """
            IsEven = x mod 2 == 0
            CountEven(N) = count(range(1, N).filter(IsEven))
            CountEven(10)
            """;

        AssertEvalSequenceModes(source, 5);

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([5m], result.Value.ToAtoms());
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(0, stats.FilterCountFusionFallbacks);
        Assert.Equal(1, stats.DirectRangeFusionHits);
        Assert.Equal(0, stats.DirectRangeFusionFallbacks);
        Assert.Equal(10, stats.FilterCountPredicateCalls);
        Assert.Equal(5, stats.AvoidedFilteredResultMaterializations);
        Assert.Equal(10, stats.AvoidedSourceMaterializations);

        var pipeline = Assert.Single(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.Equal("plain-count-dot-filter", pipeline.Form);
        Assert.Equal("filter.count -> countWhere", pipeline.Fusion);
        Assert.Equal("builtin range", pipeline.SourceKind);
        Assert.Equal("direct range iteration", pipeline.SourceExecution);
        Assert.Equal("IsEven", pipeline.PredicateSummary);
        Assert.Equal(10, pipeline.PredicateCalls);
        Assert.Equal(5, pipeline.ResultCount);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_FusesPlainCountPlainFilter()
    {
        // The BARE nested plain form count(filter(src, pred)) — filter's exact
        // list result is count's one collection argument — also fuses.
        var source = """
            IsEven = x mod 2 == 0
            CountEven(N) = count(filter(range(1, N), IsEven))
            CountEven(10)
            """;

        AssertEvalSequenceModes(source, 5);

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([5m], result.Value.ToAtoms());
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(0, stats.FilterCountFusionFallbacks);
        Assert.Equal(1, stats.DirectRangeFusionHits);
        Assert.Equal(0, stats.DirectRangeFusionFallbacks);
        Assert.Equal(10, stats.FilterCountPredicateCalls);
        Assert.Equal(5, stats.AvoidedFilteredResultMaterializations);
        Assert.Equal(10, stats.AvoidedSourceMaterializations);

        var pipeline = Assert.Single(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.Equal("plain-count-plain-filter", pipeline.Form);
        Assert.Equal("filter.count -> countWhere", pipeline.Fusion);
        Assert.Equal("builtin range", pipeline.SourceKind);
        Assert.Equal("direct range iteration", pipeline.SourceExecution);
        Assert.Equal("IsEven", pipeline.PredicateSummary);
        Assert.Equal(10, pipeline.PredicateCalls);
        Assert.Equal(5, pipeline.ResultCount);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_DotAndPlainCountFormsAgree()
    {
        var source = """
            IsEven = x mod 2 == 0
            A = range(1, 10).filter(IsEven).count
            B = count(range(1, 10).filter(IsEven))
            A, B
            """;

        AssertEvalSequenceModes(source, 5, 5);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_NoMatches()
    {
        var source = """
            Never(x) = 0
            range(1, 10).filter(Never).count
            """;

        AssertEvalSequenceModes(source, 0);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_AllMatches()
    {
        var source = """
            Always(x) = 1
            range(1, 10).filter(Always).count
            """;

        AssertEvalSequenceModes(source, 10);
    }

    [Fact]
    public void Eval_SequencePipelineS2_FilterCount_DirectRangeDescendingMatchesGeneric()
    {
        var source = """
            IsEven = x mod 2 == 0
            range(10, 1).filter(IsEven).count
            """;

        AssertEvalSequenceModes(source, 5);

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([5m], result.Value.ToAtoms());
        Assert.Equal(1, stats.DirectRangeFusionHits);
        var pipeline = Assert.Single(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.Equal("direct range iteration", pipeline.SourceExecution);
        Assert.Equal(10, pipeline.SourceItemCount);
    }

    [Fact]
    public void Eval_SequencePipelineS2_FilterCount_DirectRangeSingletonMatchesGeneric()
    {
        var source = """
            IsFive = x == 5
            range(5, 5).filter(IsFive).count
            """;

        AssertEvalSequenceModes(source, 1);

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([1m], result.Value.ToAtoms());
        Assert.Equal(1, stats.DirectRangeFusionHits);
        Assert.Equal(1, stats.AvoidedSourceMaterializations);
        var pipeline = Assert.Single(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.Equal(1, pipeline.SourceItemCount);
        Assert.Equal(1, pipeline.AvoidedSourceMaterializationCount);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_SequenceValueItems()
    {
        var source = """
            KeepPair = pair:0 mod 2 == 0
            Data = (1, 10), (2, 20), (3, 30), (4, 40)
            Data.filter(KeepPair).count
            """;

        AssertEvalSequenceModes(source, 2);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_ErrorOrderMatchesGeneric()
    {
        var source = """
            BadOnFive(x) = if(x == 5, 1 / 0, x mod 2 == 0)
            range(1, 10).filter(BadOnFive).count
            """;

        var generic = EvalFull(
            source,
            enableLoopOptimization: true,
            enableSequencePipelineOptimization: false);
        var optimized = EvalFull(
            source,
            enableLoopOptimization: true,
            enableSequencePipelineOptimization: true);

        if (generic.IsOk)
            Assert.Fail($"Expected generic sequence evaluation failure but got: {generic.Value}");
        if (optimized.IsOk)
            Assert.Fail($"Expected optimized sequence evaluation failure but got: {optimized.Value}");

        Assert.IsType<EvalError.DivByZero>(Innermost(generic.Error));
        Assert.IsType<EvalError.DivByZero>(Innermost(optimized.Error));

        var genericMessage = KatLangError.FromEvalError(generic.Error).Message;
        var optimizedMessage = KatLangError.FromEvalError(optimized.Error).Message;
        Assert.Contains("while evaluating filter predicate for item 4: 5", genericMessage);
        Assert.Contains("while evaluating filter predicate for item 4: 5", optimizedMessage);
    }

    [Fact]
    public void Eval_SequencePipelineS2_FilterCount_RangeArgumentErrorOrderMatchesGeneric()
    {
        var source = """
            BadPredicate(x) = 1 / 0
            range(1 / 0, 10).filter(BadPredicate).count
            """;

        var generic = EvalFull(
            source,
            enableLoopOptimization: true,
            enableSequencePipelineOptimization: false);
        var optimized = EvalFull(
            source,
            enableLoopOptimization: true,
            enableSequencePipelineOptimization: true);

        if (generic.IsOk)
            Assert.Fail($"Expected generic sequence evaluation failure but got: {generic.Value}");
        if (optimized.IsOk)
            Assert.Fail($"Expected optimized sequence evaluation failure but got: {optimized.Value}");

        Assert.IsType<EvalError.DivByZero>(Innermost(generic.Error));
        Assert.IsType<EvalError.DivByZero>(Innermost(optimized.Error));
    }

    [Fact]
    public void Eval_SequencePipeline_UnarySpreadReceiver_FusesAndMatchesGeneric()
    {
        // A parenthesized postfix-spread dot receiver `(range(1, 10)*)` feeds a
        // dot filter/count pipeline. It fuses through the GENERIC dot-receiver
        // source plan (the receiver is iterated by EvaluateDotReceiverIterationItems)
        // — NOT via UnwrapSpread (which only serves the plain-count path)
        // and NOT via direct-range fusion (the receiver is a parenthesized group,
        // not a bare `range(...)` call). The fused result equals the generic one.
        var source = """
            IsEven = x mod 2 == 0
            (range(1, 10)*).filter(IsEven).count
            """;

        var generic = EvalFull(source, enableLoopOptimization: true, enableSequencePipelineOptimization: false);
        var optimized = EvalFull(source, enableLoopOptimization: true, enableSequencePipelineOptimization: true);
        if (generic.IsError)
            Assert.Fail($"Expected generic success but got error: {generic.Error}");
        if (optimized.IsError)
            Assert.Fail($"Expected optimized success but got error: {optimized.Error}");
        Assert.Equal(generic.Value.ToAtoms(), optimized.Value.ToAtoms());

        var (_, stats) = EvalFullWithSequenceDiagnostics(source);
        Assert.Contains(stats.Pipelines, pipeline => pipeline.Optimized);
        // Exactly one filter-count pipeline runs here, fused via the generic
        // dot-receiver source plan — not direct-range fusion.
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(0, stats.DirectRangeFusionHits);
    }

    [Fact]
    public void Eval_CountFilter_PlainCallCountsFilteredItems_OptimizedMatchesGeneric()
    {
        // Plain count of a filter result: filter returns one exact list value
        // and count opens that lone collection boundary.
        AssertEvalSequenceModes(
            "IsEven = x mod 2 == 0\ncount(filter(range(1, 10), IsEven))",
            5m);

        AssertEvalSequenceModes(
            "IsEven = x mod 2 == 0\nData = range(1, 10)\ncount(filter(Data, IsEven))",
            5m);

        AssertEvalSequenceModes(
            "IsEven = x mod 2 == 0\ncount(range(1, 10).filter(IsEven))",
            5m);

        AssertEvalSequenceModes(
            "IsEven = x mod 2 == 0\nData = range(1, 10)\ncount(Data.filter(IsEven))",
            5m);
    }

    [Fact]
    public void Eval_CountFilter_FilteredItemCountForms_OptimizedMatchesGeneric()
    {
        // The forms whose generic meaning IS the filtered-item count (5). Here the
        // fusion legitimately applies and optimized must equal generic.

        AssertEvalSequenceModes(
            "IsEven = x mod 2 == 0\ncount(filter(range(1, 10), IsEven))",
            5m);

        AssertEvalSequenceModes(
            "IsEven = x mod 2 == 0\nData = range(1, 10)\ncount(filter(Data, IsEven))",
            5m);

        // Dot-call count iterates the receiver = filtered-item count.
        AssertEvalSequenceModes(
            "IsEven = x mod 2 == 0\nrange(1, 10).filter(IsEven).count",
            5m);

        // Dot-filter dot-count over a named source.
        AssertEvalSequenceModes(
            "IsEven = x mod 2 == 0\nData = range(1, 10)\nData.filter(IsEven).count",
            5m);

        AssertEvalSequenceModes(
            "IsEven = x mod 2 == 0\nData = range(1, 10)\ncount(Data.filter(IsEven))",
            5m);
    }

    [Fact]
    public void Eval_SequencePipeline_DirectRangeSource_StillFusesViaDirectRange()
    {
        // The bare plain composition over a direct `range(...)` source fuses
        // via direct-range iteration and matches the generic result.
        var source = """
            IsEven = x mod 2 == 0
            count(filter(range(1, 10), IsEven))
            """;

        var generic = EvalFull(source, enableLoopOptimization: true, enableSequencePipelineOptimization: false);
        var optimized = EvalFull(source, enableLoopOptimization: true, enableSequencePipelineOptimization: true);
        if (generic.IsError)
            Assert.Fail($"Expected generic success but got error: {generic.Error}");
        if (optimized.IsError)
            Assert.Fail($"Expected optimized success but got error: {optimized.Error}");
        Assert.Equal(generic.Value.ToAtoms(), optimized.Value.ToAtoms());
        Assert.Equal([5m], optimized.Value.ToAtoms());

        var (_, stats) = EvalFullWithSequenceDiagnostics(source);
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(1, stats.DirectRangeFusionHits);
    }

    [Fact]
    public void Eval_SequencePipeline_NestedSpreadReceiver_FusesAndMatchesGeneric()
    {
        // A doubly-nested postfix-spread dot receiver `(range(1, 10)**)`.
        // Like the single-spread case it fuses through the GENERIC dot-receiver
        // source plan (the receiver is iterated by EvaluateDotReceiverIterationItems,
        // which evaluates the nested unary spread to the same items) — NOT via
        // UnwrapSpread and NOT via direct-range fusion. The fused result
        // equals the generic one.
        var source = """
            IsEven = x mod 2 == 0
            (range(1, 10)**).filter(IsEven).count
            """;

        var generic = EvalFull(source, enableLoopOptimization: true, enableSequencePipelineOptimization: false);
        var optimized = EvalFull(source, enableLoopOptimization: true, enableSequencePipelineOptimization: true);
        if (generic.IsError)
            Assert.Fail($"Expected generic success but got error: {generic.Error}");
        if (optimized.IsError)
            Assert.Fail($"Expected optimized success but got error: {optimized.Error}");
        Assert.Equal(generic.Value.ToAtoms(), optimized.Value.ToAtoms());

        var (_, stats) = EvalFullWithSequenceDiagnostics(source);
        Assert.Contains(stats.Pipelines, pipeline => pipeline.Optimized);
        // Exactly one filter-count pipeline runs here, fused via the generic
        // dot-receiver source plan — not direct-range fusion.
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(0, stats.DirectRangeFusionHits);
    }

    [Fact]
    public void Eval_SequencePipeline_PlainFilterCountFallback_DoesNotEvaluateNonRangeSource()
    {
        // White-box regression for the plain filter-count fallback path: when the
        // filter source is NOT a direct builtin range, the optimizer must defer to
        // the generic evaluator WITHOUT evaluating the source first (otherwise a
        // non-range source would be evaluated once during the failed fusion probe
        // and again during generic fallback — double evaluation).
        //
        // Models `count(filter(Data, IsEven))` with `Data` a non-range
        // (named) source. Keeping both call boundaries unspread is essential:
        // an outer or inner spread is rejected by an earlier syntax gate and
        // would never exercise the non-range-source fallback under test. The
        // services bundle deliberately carries NO
        // plain-source evaluation service (the plain form fuses direct
        // builtin-range sources only), so the only two evaluation services —
        // the dot-receiver source and the range arguments — both throw: the
        // fallback must be reached without either running.

        OutputBundle filterArgs =
        [
            new Expr.Resolve("Data"),
            new Expr.Resolve("IsEven"),
        ];
        OutputBundle countArgs =
        [
            new Expr.Call(new Expr.Resolve("filter"), filterArgs),
        ];
        var invocation = SequencePipelineInvocation.PlainCall(
            new Expr.Resolve("count"),
            countArgs,
            new Algorithm.Builtin(BuiltinId.@count));

        var services = new SequencePipelineEvaluationServices(
            GetDotCallLexicalBuiltinFallbackReason: (_, _) => null,
            EvaluateDotReceiverIterationItems: _ =>
                throw new Xunit.Sdk.XunitException("dot-receiver evaluation must not run for a plain call"),
            ResolveArgumentAlgorithms: _ => EvalResult<IReadOnlyList<Algorithm>>.Ok(
                [new Algorithm.User(null, [], [], [], []), new Algorithm.User(null, [], [], [], [])]),
            ResolveAlgorithm: _ => EvalResult<Algorithm>.Ok(new Algorithm.Builtin(BuiltinId.@filter)),
            EvaluateRangeCallArguments: (_, _, _) =>
                throw new Xunit.Sdk.XunitException("range-argument evaluation must not run for a non-range source"));

        var diagnostics = new SequencePipelineDiagnostics();
        var handled = SequencePipelineOptimizer.TryExecute(
            invocation,
            services,
            Evaluator.EvalCtx.Empty,
            [],
            diagnostics,
            out _);

        // The optimizer deferred to generic (did not fuse) WITHOUT evaluating the
        // non-range source even once (neither throwing evaluation service ran).
        Assert.False(handled);
        var stats = diagnostics.GetSnapshot();
        Assert.Equal(0, stats.FilterCountFusionHits);
        Assert.Equal(1, stats.FallbackReasons["source is not builtin range"]);
        Assert.Equal(1, stats.FallbackReasons["non-range source for plain filter-count"]);
        var pipeline = Assert.Single(stats.Pipelines);
        Assert.Equal("non-range source for plain filter-count", pipeline.FallbackReason);
        Assert.All(stats.Pipelines, pipeline => Assert.Equal("not executed", pipeline.SourceExecution));
    }

    [Fact]
    public void Eval_SequencePipeline_DotFilterCountFallback_GenericReceiverNotEvaluatedOnPredicateResolutionFailure()
    {
        // White-box regression for the dot-filter/count recognition path: when the
        // filter predicate fails to resolve, the optimizer must fall back to the
        // generic evaluator WITHOUT having evaluated the dot receiver (source).
        //
        // Before the fix the dot path evaluated the source FIRST and only then
        // resolved the predicate, so a predicate-resolution failure (1) caused the
        // generic fallback to re-evaluate the source (double evaluation) and (2)
        // recorded a misleading "not executed" fallback diagnostic for a path that
        // HAD executed the source. The fix resolves the predicate before touching
        // the source, so the source is evaluated exactly once — by the generic
        // re-run — and the "not executed" diagnostic is honest.
        //
        // Models `Data.filter(BadPred).count` with `Data` a non-range (generic)
        // receiver. The counting EvaluateDotReceiverIterationItems delegate must be
        // invoked exactly zero times.
        var dotReceiverEvalCount = 0;

        OutputBundle filterArgs = [new Expr.Resolve("BadPred")];
        var target = new Expr.DotCall(new Expr.Resolve("Data"), "filter", filterArgs);
        var invocation = SequencePipelineInvocation.DotCall(new Expr.DotCall(target, "count"));

        var services = new SequencePipelineEvaluationServices(
            GetDotCallLexicalBuiltinFallbackReason: (_, _) => null,
            EvaluateDotReceiverIterationItems: _ =>
            {
                dotReceiverEvalCount++;
                return EvalResult<IReadOnlyList<Evaluator.CountedResult>>.Ok(
                    new List<Evaluator.CountedResult>());
            },
            ResolveArgumentAlgorithms: _ =>
                EvalResult<IReadOnlyList<Algorithm>>.Err(new EvalError.UnknownName("BadPred")),
            ResolveAlgorithm: _ => EvalResult<Algorithm>.Ok(new Algorithm.Builtin(BuiltinId.@filter)),
            EvaluateRangeCallArguments: (_, _, _) =>
                throw new Xunit.Sdk.XunitException("range-argument evaluation must not run for a non-range source"));

        var diagnostics = new SequencePipelineDiagnostics();
        var handled = SequencePipelineOptimizer.TryExecute(
            invocation,
            services,
            PreludeEvalCtx(),
            [],
            diagnostics,
            out _);

        // Predicate resolution failed BEFORE any source evaluation, so the
        // optimizer declined (handled == false → generic fallback) without touching
        // the source.
        Assert.False(handled);
        Assert.Equal(0, dotReceiverEvalCount);

        // No optimized pipeline executed, and the recorded fallback honestly
        // reports the source as not executed (because it genuinely was not).
        var stats = diagnostics.GetSnapshot();
        Assert.Equal(0, stats.FilterCountFusionHits);
        Assert.Equal(1, stats.FilterCountFusionFallbacks);
        Assert.Equal(1, stats.FallbackReasons["filter argument resolution failed"]);
        Assert.DoesNotContain(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.All(stats.Pipelines, pipeline => Assert.Equal("not executed", pipeline.SourceExecution));
    }

    [Fact]
    public void Eval_SequencePipeline_DotFilterCountFallback_DirectRangeNotEvaluatedOnPredicateResolutionFailure()
    {
        // White-box regression for the direct-range dot-filter/count path: a range
        // source's bounds must NOT be evaluated by the recognition probe when the
        // filter predicate fails to resolve. With the predicate resolved before the
        // source, the optimizer falls back without evaluating the range arguments,
        // so the generic re-run evaluates them exactly once (no double evaluation).
        //
        // Models `range(1, 10).filter(BadPred).count`. The counting
        // EvaluateRangeCallArguments delegate must be invoked exactly zero times.
        var rangeEvalCount = 0;

        var rangeSource = new Expr.Call(
            new Expr.Resolve("range"),
            [new Expr.Num(1m), new Expr.Num(10m)]);
        OutputBundle filterArgs = [new Expr.Resolve("BadPred")];
        var target = new Expr.DotCall(rangeSource, "filter", filterArgs);
        var invocation = SequencePipelineInvocation.DotCall(new Expr.DotCall(target, "count"));

        var services = new SequencePipelineEvaluationServices(
            GetDotCallLexicalBuiltinFallbackReason: (_, _) => null,
            EvaluateDotReceiverIterationItems: _ =>
                throw new Xunit.Sdk.XunitException("generic dot-receiver iteration must not run for a direct range"),
            ResolveArgumentAlgorithms: _ =>
                EvalResult<IReadOnlyList<Algorithm>>.Err(new EvalError.UnknownName("BadPred")),
            ResolveAlgorithm: _ => EvalResult<Algorithm>.Ok(new Algorithm.Builtin(BuiltinId.@range)),
            EvaluateRangeCallArguments: (_, _, _) =>
            {
                rangeEvalCount++;
                return EvalResult<Evaluator.InclusiveRange>.Ok(new Evaluator.InclusiveRange(1, 10));
            });

        var diagnostics = new SequencePipelineDiagnostics();
        var handled = SequencePipelineOptimizer.TryExecute(
            invocation,
            services,
            PreludeEvalCtx(),
            [],
            diagnostics,
            out _);

        // The range arguments were not evaluated by the probe (so the generic
        // fallback evaluates them exactly once), and the optimizer declined.
        Assert.False(handled);
        Assert.Equal(0, rangeEvalCount);

        var stats = diagnostics.GetSnapshot();
        Assert.Equal(0, stats.FilterCountFusionHits);
        Assert.Equal(0, stats.DirectRangeFusionHits);
        Assert.Equal(1, stats.FilterCountFusionFallbacks);
        Assert.Equal(1, stats.FallbackReasons["filter argument resolution failed"]);
        Assert.DoesNotContain(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.All(stats.Pipelines, pipeline => Assert.Equal("not executed", pipeline.SourceExecution));
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_RespectsBuiltinShadowing()
    {
        var filterShadow = """
            filter(*source, predicate) = 123
            IsEven = x mod 2 == 0
            range(1, 10).filter(IsEven).count
            """;

        var (filterResult, filterStats) = EvalFullWithSequenceDiagnostics(filterShadow);
        if (filterResult.IsError)
            Assert.Fail($"Expected success but got error: {filterResult.Error}");

        Assert.Equal([1m], filterResult.Value.ToAtoms());
        Assert.Equal(0, filterStats.FilterCountFusionHits);
        Assert.Equal(1, filterStats.FilterCountFusionFallbacks);
        Assert.Equal(1, filterStats.FallbackReasons["filter does not resolve to builtin"]);

        var structuralFilterShadow = """
            Source = { public filter(predicate) = 42 }
            IsEven = x mod 2 == 0
            Source.filter(IsEven).count
            """;

        var (structuralFilterResult, structuralFilterStats) = EvalFullWithSequenceDiagnostics(structuralFilterShadow);
        if (structuralFilterResult.IsError)
            Assert.Fail($"Expected success but got error: {structuralFilterResult.Error}");

        Assert.Equal([1m], structuralFilterResult.Value.ToAtoms());
        Assert.Equal(0, structuralFilterStats.FilterCountFusionHits);
        Assert.Equal(1, structuralFilterStats.FilterCountFusionFallbacks);
        Assert.Equal(1, structuralFilterStats.FallbackReasons["filter is shadowed by a structural property"]);

        var countShadow = """
            count(value) = 999
            IsEven = x mod 2 == 0
            range(1, 10).filter(IsEven).count
            """;

        var (countResult, countStats) = EvalFullWithSequenceDiagnostics(countShadow);
        if (countResult.IsError)
            Assert.Fail($"Expected success but got error: {countResult.Error}");

        Assert.Equal([999m], countResult.Value.ToAtoms());
        Assert.Equal(0, countStats.FilterCountFusionHits);
        Assert.Equal(1, countStats.FilterCountFusionFallbacks);
        Assert.Equal(1, countStats.FallbackReasons["count does not resolve to builtin"]);

        var plainFilterShadow = """
            filter(*source, predicate) = 123
            IsEven = x mod 2 == 0
            count(filter(range(1, 10), IsEven))
            """;

        var (plainFilterResult, plainFilterStats) = EvalFullWithSequenceDiagnostics(plainFilterShadow);
        if (plainFilterResult.IsError)
            Assert.Fail($"Expected success but got error: {plainFilterResult.Error}");

        Assert.Equal([1m], plainFilterResult.Value.ToAtoms());
        Assert.Equal(0, plainFilterStats.FilterCountFusionHits);
        Assert.Equal(1, plainFilterStats.FilterCountFusionFallbacks);
        Assert.Equal(1, plainFilterStats.FallbackReasons["filter does not resolve to builtin"]);

        // User count shadowing keeps the pipeline from using the builtin count
        // fusion and the shadowed count sees the filter result as one argument.
        var plainCountShadow = """
            count(value) = 999
            IsEven = x mod 2 == 0
            count(range(1, 10).filter(IsEven))
            """;

        var (plainCountResult, plainCountStats) = EvalFullWithSequenceDiagnostics(plainCountShadow);
        if (plainCountResult.IsError)
            Assert.Fail($"Expected success but got error: {plainCountResult.Error}");

        Assert.Equal([999m], plainCountResult.Value.ToAtoms());
        Assert.Equal(0, plainCountStats.FilterCountFusionHits);
        Assert.Equal(1, plainCountStats.FilterCountFusionFallbacks);
        Assert.Equal(1, plainCountStats.FallbackReasons["count does not resolve to builtin"]);
    }

    [Fact]
    public void Eval_SequencePipelineS2_FilterCount_RespectsRangeBuiltinShadowing()
    {
        var source = """
            range(start, stop) = 42
            IsEven = x mod 2 == 0
            range(1, 10).filter(IsEven).count
            """;

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([1m], result.Value.ToAtoms());
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(0, stats.DirectRangeFusionHits);
        Assert.Equal(1, stats.DirectRangeFusionFallbacks);
        Assert.Equal(1, stats.FallbackReasons["source is not builtin range"]);

        var pipeline = Assert.Single(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.Equal("generic source", pipeline.SourceKind);
        Assert.Equal("eager source collection", pipeline.SourceExecution);
        Assert.Equal("source is not builtin range", pipeline.SourceExecutionFallbackReason);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_ExtraCountArgument_IsArityErrorInBothModes()
    {
        // count(collection) is fixed one-argument: an extra argument beside the
        // filter pipeline is an ordinary arity error, and the optimizer must
        // not recognize the over-supplied call in either mode.
        var source = """
            IsEven = x mod 2 == 0
            count(range(1, 10).filter(IsEven), 0)
            """;

        foreach (var enableSequencePipelineOptimization in new[] { false, true })
        {
            var result = EvalFull(
                source,
                enableLoopOptimization: true,
                enableSequencePipelineOptimization: enableSequencePipelineOptimization);
            if (result.IsOk)
                Assert.Fail($"Expected arity failure but got: {result.Value}");

            var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
            Assert.Equal(1, arity.Expected);
            Assert.Equal(2, arity.Actual);
        }
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterExtraArgument_IsArityErrorInBothModes()
    {
        // filter(collection, predicate) is fixed two-argument: the extra `0`
        // over-supplies the call, an ordinary arity error in both the generic
        // and the sequence-pipeline-optimized evaluator.
        var source = """
            IsEven = x mod 2 == 0
            count(filter(range(1, 10), 0, IsEven))
            """;

        foreach (var enableSequencePipelineOptimization in new[] { false, true })
        {
            var result = EvalFull(
                source,
                enableLoopOptimization: true,
                enableSequencePipelineOptimization: enableSequencePipelineOptimization);
            if (result.IsOk)
                Assert.Fail($"Expected arity failure but got: {result.Value}");

            var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
            Assert.Equal(2, arity.Expected);
            Assert.Equal(3, arity.Actual);
        }
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_SquareFreeCount()
    {
        var source = """
            IsSquareFree(num) = {
                Step = {
                    Square = k * k
                    k + 1, s + if(num mod Square == 0, 1, 0), Square <= num and s <= 0
                }
                Step.while(2, 0):1 == 0
            }

            SquareFreeCount(N) = range(1, N).filter(IsSquareFree).count

            SquareFreeCount(1000)
            """;

        AssertEvalSequenceModes(source, 608);

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([608m], result.Value.ToAtoms());
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(1, stats.DirectRangeFusionHits);
        Assert.Equal(1000, stats.FilterCountPredicateCalls);
        Assert.Equal(1000, stats.AvoidedSourceMaterializations);
        var pipeline = Assert.Single(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.Equal("direct range iteration", pipeline.SourceExecution);
        Assert.Equal(1000, pipeline.SourceItemCount);
        Assert.Equal(608, pipeline.ResultCount);
        Assert.Equal(1000, pipeline.AvoidedSourceMaterializationCount);
    }

    [Fact]
    public void Eval_SequencePipelineS2_FilterCount_ImplicitPropertySquareFreeUsesDirectRange()
    {
        var source = """
            IsSquareFree(num) = {
                Step = {
                    Square = k * k
                    k + 1, s + if(num mod Square == 0, 1, 0), Square <= num and s <= 0
                }
                Step.while(2, 0):1 == 0
            }

            SquareFreeCount = range(1,N).filter(IsSquareFree).count

            SquareFreeCount(1000)
            """;

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([608m], result.Value.ToAtoms());
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(1, stats.DirectRangeFusionHits);
        Assert.Equal(1000, stats.FilterCountPredicateCalls);
        Assert.Equal(1000, stats.AvoidedSourceMaterializations);

        var pipeline = Assert.Single(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.Equal("dot-filter-dot-count", pipeline.Form);
        Assert.Equal("builtin range", pipeline.SourceKind);
        Assert.Equal("direct range iteration", pipeline.SourceExecution);
        Assert.Equal(1000, pipeline.SourceItemCount);
    }
}
