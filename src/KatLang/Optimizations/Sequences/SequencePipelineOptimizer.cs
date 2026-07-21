namespace KatLang.Optimizations.Sequences;

internal static class SequencePipelineOptimizer
{
    public const string FilterCountFusion = "filter.count -> countWhere";
    private const string GenericSourceKind = "generic source";
    private const string BuiltinRangeSourceKind = "builtin range";
    private const string SourceExecutionNotExecuted = "not executed";
    private const string SourceExecutionEagerCollection = "eager source collection";
    private const string SourceExecutionDirectRange = "direct range iteration";

    private enum FilterCountRecognitionStatus
    {
        NotRecognized,
        Fallback,
        Error,
        Recognized,
    }

    internal static bool TryExecute(
        SequencePipelineInvocation invocation,
        SequencePipelineEvaluationServices services,
        Evaluator.EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        SequencePipelineDiagnostics? diagnostics,
        out EvalResult<Evaluator.CountedResult> result)
    {
        var status = TryRecognizeFilterCountPipeline(
            invocation,
            services,
            ctx,
            diagnostics,
            out var plan,
            out result);

        if (status is FilterCountRecognitionStatus.NotRecognized or FilterCountRecognitionStatus.Fallback)
        {
            result = default;
            return false;
        }

        if (status == FilterCountRecognitionStatus.Error)
            return true;

        result = WithContext(
            plan!.EvaluationContext,
            ExecuteFilterCount(plan, ctx, valEnv, diagnostics));
        return true;
    }

    private static string FormName(FilterCountPipelineForm form)
        => form switch
        {
            FilterCountPipelineForm.DotFilterDotCount => "dot-filter-dot-count",
            FilterCountPipelineForm.PlainCountDotFilter => "plain-count-dot-filter",
            FilterCountPipelineForm.PlainCountPlainFilter => "plain-count-plain-filter",
            _ => form.ToString(),
        };

    private static FilterCountRecognitionStatus TryRecognizeFilterCountPipeline(
        SequencePipelineInvocation invocation,
        SequencePipelineEvaluationServices services,
        Evaluator.EvalCtx ctx,
        SequencePipelineDiagnostics? diagnostics,
        out FilterCountPipelinePlan? plan,
        out EvalResult<Evaluator.CountedResult> result)
    {
        plan = null;
        result = default;

        if (!TryRecognizeFilterCountSyntax(invocation, out var syntax, out var fallbackReason))
        {
            if (fallbackReason is not null)
            {
                RecordFilterCountFallback(
                    diagnostics,
                    CreateDiagnosticPlan(syntax.Form, syntax.Source, predicateExpr: null, predicateAlg: null),
                    fallbackReason);
                return FilterCountRecognitionStatus.Fallback;
            }

            return FilterCountRecognitionStatus.NotRecognized;
        }

        var predicateExpr = TryGetPredicateExpression(syntax);
        var diagnosticPlan = CreateDiagnosticPlan(syntax.Form, syntax.Source, predicateExpr, predicateAlg: null);

        if (!ctx.EnableSequencePipelineOptimization)
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "sequence pipeline optimization disabled");
            return FilterCountRecognitionStatus.Fallback;
        }

        if (!CountResolvesToBuiltin(invocation, ctx))
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "count does not resolve to builtin");
            return FilterCountRecognitionStatus.Fallback;
        }

        return syntax.Form switch
        {
            FilterCountPipelineForm.DotFilterDotCount or FilterCountPipelineForm.PlainCountDotFilter =>
                TryNormalizeDotFilterCount(syntax, services, diagnostics, predicateExpr, diagnosticPlan, out plan, out result),
            FilterCountPipelineForm.PlainCountPlainFilter =>
                TryNormalizePlainFilterCount(syntax, services, diagnostics, predicateExpr, diagnosticPlan, out plan, out result),
            _ => throw new InvalidOperationException($"Unsupported filter-count pipeline form '{syntax.Form}'."),
        };
    }

    private static bool TryRecognizeFilterCountSyntax(
        SequencePipelineInvocation invocation,
        out FilterCountPipelineSyntax syntax,
        out string? fallbackReason)
    {
        syntax = default;
        fallbackReason = null;

        return invocation.Kind switch
        {
            SequencePipelineInvocationKind.DotCall => TryRecognizeDotFilterDotCount(
                invocation.DotTarget!,
                invocation.DotName!,
                invocation.DotArgs,
                out syntax),
            SequencePipelineInvocationKind.PlainCall => TryRecognizePlainCountFilter(
                invocation.PlainFunction!,
                invocation.PlainArgs!,
                out syntax,
                out fallbackReason),
            _ => false,
        };
    }

    private static bool TryRecognizeDotFilterDotCount(
        Expr target,
        string name,
        Algorithm? argsOpt,
        out FilterCountPipelineSyntax syntax)
    {
        if (name == BuiltinId.@count.ToString()
            && argsOpt is null
            && target is Expr.DotCall(var source, var filterName, var filterArgs)
            && filterName == BuiltinId.@filter.ToString())
        {
            syntax = new FilterCountPipelineSyntax(
                FilterCountPipelineForm.DotFilterDotCount,
                source,
                filterArgs,
                PlainFilterFunction: null,
                PlainFilterArgs: null);
            return true;
        }

        syntax = default;
        return false;
    }

    private static bool TryRecognizePlainCountFilter(
        Expr function,
        Algorithm args,
        out FilterCountPipelineSyntax syntax,
        out string? fallbackReason)
    {
        syntax = default;
        fallbackReason = null;

        if (function is not Expr.Resolve(var countName) || countName != BuiltinId.@count.ToString())
            return false;

        if (args.Output.Count != 1)
        {
            if (TryFindFilterCountSourceCandidate(args.Output, out syntax))
                fallbackReason = "unsupported count argument shape";

            return false;
        }

        // Under fixed collection-object arity the valid plain composition is
        // the BARE one-argument form — `count(filter(src, pred))` or
        // `count(src.filter(pred))` — where the filter result is count's one
        // collection argument. A spread form such as `count(filter(...)...)`
        // supplies the opened items as separate arguments and is an ordinary
        // arity error, so it must NOT be recognized: it falls back to the
        // generic evaluator, which reports the arity mismatch.
        var countSource = args.Output[0];
        if (countSource is Expr.SequenceSpread)
            return false;

        if (countSource is Expr.DotCall(var dotSource, var filterName, var dotFilterArgs)
            && filterName == BuiltinId.@filter.ToString())
        {
            syntax = new FilterCountPipelineSyntax(
                FilterCountPipelineForm.PlainCountDotFilter,
                dotSource,
                dotFilterArgs,
                PlainFilterFunction: null,
                PlainFilterArgs: null);
            return true;
        }

        if (countSource is Expr.Call(var filterFunction, var plainFilterArgs)
            && IsFilterFunctionCandidate(filterFunction))
        {
            var plainSource = plainFilterArgs.Output.Count > 0
                ? plainFilterArgs.Output[0]
                : countSource;
            syntax = new FilterCountPipelineSyntax(
                FilterCountPipelineForm.PlainCountPlainFilter,
                plainSource,
                DotFilterArgs: null,
                filterFunction,
                plainFilterArgs);
            return true;
        }

        return false;
    }

    private static bool TryFindFilterCountSourceCandidate(
        IReadOnlyList<Expr> expressions,
        out FilterCountPipelineSyntax syntax)
    {
        foreach (var expression in expressions)
        {
            var candidate = UnwrapSpread(expression);

            if (candidate is Expr.DotCall(var dotSource, var filterName, var dotFilterArgs)
                && filterName == BuiltinId.@filter.ToString())
            {
                syntax = new FilterCountPipelineSyntax(
                    FilterCountPipelineForm.PlainCountDotFilter,
                    dotSource,
                    dotFilterArgs,
                    PlainFilterFunction: null,
                    PlainFilterArgs: null);
                return true;
            }

            if (candidate is Expr.Call(var filterFunction, var plainFilterArgs)
                && IsFilterFunctionCandidate(filterFunction))
            {
                var plainSource = plainFilterArgs.Output.Count > 0
                    ? UnwrapSpread(plainFilterArgs.Output[0])
                    : candidate;
                syntax = new FilterCountPipelineSyntax(
                    FilterCountPipelineForm.PlainCountPlainFilter,
                    plainSource,
                    DotFilterArgs: null,
                    filterFunction,
                    plainFilterArgs);
                return true;
            }
        }

        syntax = default;
        return false;
    }

    private static bool IsFilterFunctionCandidate(Expr function)
        => function is Expr.Resolve(var name) && name == BuiltinId.@filter.ToString();

    // Returns the innermost operand of a (possibly nested) unary spread,
    // or the expression unchanged when it is not a spread. Nested spread such as
    // `A......` (`sequenceSpread (sequenceSpread A)`) is value-equivalent to a
    // single spread of `A` — every layer spreads the same items — so peeling all
    // layers is semantics-preserving and lets nested-spread sources still reach
    // direct-range fusion instead of falling back.
    private static Expr UnwrapSpread(Expr expression)
    {
        while (expression is Expr.SequenceSpread(var supplied))
            expression = supplied;
        return expression;
    }

    private static bool TryGetSpreadOperand(Expr expression, out Expr supplied)
    {
        supplied = UnwrapSpread(expression);
        return !ReferenceEquals(supplied, expression);
    }

    private static FilterCountRecognitionStatus TryNormalizeDotFilterCount(
        FilterCountPipelineSyntax syntax,
        SequencePipelineEvaluationServices services,
        SequencePipelineDiagnostics? diagnostics,
        Expr? predicateExpr,
        SequencePipelinePlan diagnosticPlan,
        out FilterCountPipelinePlan? plan,
        out EvalResult<Evaluator.CountedResult> result)
    {
        plan = null;
        result = default;

        if (syntax.DotFilterArgs is null || syntax.DotFilterArgs.Output.Count == 0)
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "unsupported filter argument shape");
            return FilterCountRecognitionStatus.Fallback;
        }

        if (syntax.DotFilterArgs.Output.Count != 1)
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "unsupported extra arguments");
            return FilterCountRecognitionStatus.Fallback;
        }

        if (syntax.DotFilterArgs.Output[0] is Expr.SequenceSpread)
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "unsupported explicit spread argument");
            return FilterCountRecognitionStatus.Fallback;
        }

        var filterLookupFallbackReason = services.GetDotCallLexicalBuiltinFallbackReason(
            syntax.Source,
            BuiltinId.@filter.ToString(),
            BuiltinId.@filter);
        if (filterLookupFallbackReason is not null)
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, filterLookupFallbackReason);
            return FilterCountRecognitionStatus.Fallback;
        }

        // Resolve the filter predicate BEFORE evaluating the source. Predicate
        // resolution is a non-observing eligibility check: it resolves the
        // predicate argument to an algorithm (lazy wrap / name lookup) and NEVER
        // iterates `syntax.Source`. Doing it here — before any source evaluation —
        // is what enforces the no-double-evaluation invariant: every fallback
        // (unsupported shape, predicate resolution failure) happens while the
        // source is still untouched, so the generic evaluator re-runs the source
        // exactly once. Generic dot evaluation also evaluates the dot receiver
        // (source) before resolving the filter predicate, so a predicate-resolution
        // fallback here preserves the generic receiver-first error ordering: if the
        // source would also fail, the generic re-run reports the source error first.
        var predicateArgsR = services.ResolveArgumentAlgorithms(syntax.DotFilterArgs);
        if (predicateArgsR.IsError)
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "filter argument resolution failed");
            return FilterCountRecognitionStatus.Fallback;
        }

        if (predicateArgsR.Value.Count != 1)
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "unsupported filter argument shape");
            return FilterCountRecognitionStatus.Fallback;
        }

        var predicateAlg = predicateArgsR.Value[0];

        // Source evaluation is the COMMIT point. After TryCreateSourcePlan returns
        // Recognized the source has been observed (a generic receiver iterated, or
        // a direct range's bounds evaluated), and there is NO further fallback: the
        // predicate is already resolved, so the only remaining step is fused
        // execution. A source-evaluation failure is propagated as a committed
        // optimized-path error (Error status), never a fallback that would
        // re-evaluate the source.
        var evaluationContext = EvaluationContext(syntax);
        var sourcePlanStatus = TryCreateSourcePlan(
            syntax.Source,
            services,
            diagnostics,
            evaluationContext,
            () => services.EvaluateDotReceiverIterationItems(syntax.Source),
            out var sourcePlan,
            out result);
        if (sourcePlanStatus == FilterCountRecognitionStatus.Error)
            return FilterCountRecognitionStatus.Error;
        if (sourcePlanStatus != FilterCountRecognitionStatus.Recognized)
            throw new InvalidOperationException($"Unexpected source-plan status '{sourcePlanStatus}'.");

        var sourceKind = SourceKind(sourcePlan!);
        plan = new FilterCountPipelinePlan(
            syntax.Source,
            sourcePlan!,
            predicateAlg,
            syntax.Form,
            predicateExpr,
            evaluationContext,
            CreateDiagnosticPlan(syntax.Form, syntax.Source, predicateExpr, predicateAlg, sourceKind));
        return FilterCountRecognitionStatus.Recognized;
    }

    private static FilterCountRecognitionStatus TryNormalizePlainFilterCount(
        FilterCountPipelineSyntax syntax,
        SequencePipelineEvaluationServices services,
        SequencePipelineDiagnostics? diagnostics,
        Expr? predicateExpr,
        SequencePipelinePlan diagnosticPlan,
        out FilterCountPipelinePlan? plan,
        out EvalResult<Evaluator.CountedResult> result)
    {
        plan = null;
        result = default;

        var filterFunction = syntax.PlainFilterFunction!;
        var filterArgs = syntax.PlainFilterArgs!;

        // Fixed collection-object arity: `filter(collection, predicate)` is
        // exactly two arguments, and a spread argument would change the
        // supplied argument count — such a program is an ordinary arity error
        // and must fall back so the generic evaluator reports it.
        if (filterArgs.Output.Count != 2)
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "unsupported filter argument shape");
            return FilterCountRecognitionStatus.Fallback;
        }

        if (filterArgs.Output.Any(static expr => expr is Expr.SequenceSpread))
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "spread argument follows ordinary fixed arity");
            return FilterCountRecognitionStatus.Fallback;
        }

        var filterCalleeR = services.ResolveAlgorithm(filterFunction);
        if (filterCalleeR.IsError || !IsBuiltin(filterCalleeR.Value, BuiltinId.@filter))
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "filter does not resolve to builtin");
            return FilterCountRecognitionStatus.Fallback;
        }

        var filterArgAlgsR = services.ResolveArgumentAlgorithms(filterArgs);
        if (filterArgAlgsR.IsError)
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "filter argument resolution failed");
            return FilterCountRecognitionStatus.Fallback;
        }

        if (filterArgAlgsR.Value.Count != 2)
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "unsupported filter argument shape");
            return FilterCountRecognitionStatus.Fallback;
        }

        var evaluationContext = EvaluationContext(syntax);
        // Plain `count(filter(SOURCE, pred))` only fuses a direct builtin-range
        // source. Use a range-ONLY probe that never evaluates a
        // generic/non-range source: evaluating a generic source here only to
        // reject the plan would double-evaluate it once the path falls back to
        // the generic evaluator. Non-range sources are deferred WITHOUT being
        // evaluated here, so the generic evaluator runs them exactly once.
        var sourcePlanStatus = TryCreateDirectRangeSourcePlan(
            syntax.Source,
            services,
            diagnostics,
            evaluationContext,
            out var sourcePlan,
            out result);
        if (sourcePlanStatus == FilterCountRecognitionStatus.Error)
            return FilterCountRecognitionStatus.Error;
        if (sourcePlanStatus != FilterCountRecognitionStatus.Recognized)
        {
            result = default;
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "non-range source for plain filter-count");
            return FilterCountRecognitionStatus.Fallback;
        }

        var sourceKind = SourceKind(sourcePlan!);
        var predicateAlg = filterArgAlgsR.Value[1];
        plan = new FilterCountPipelinePlan(
            syntax.Source,
            sourcePlan!,
            predicateAlg,
            syntax.Form,
            predicateExpr,
            evaluationContext,
            CreateDiagnosticPlan(syntax.Form, syntax.Source, predicateExpr, predicateAlg, sourceKind));
        return FilterCountRecognitionStatus.Recognized;
    }

    // Range-only source probe for the plain filter-count path. Unlike
    // TryCreateSourcePlan it NEVER evaluates a generic/non-range source: it only
    // commits to fusion for a direct builtin-range source (whose bounds it must
    // evaluate to fuse). A non-range source is deferred to the generic evaluator
    // WITHOUT being touched here, so falling back never double-evaluates it.
    private static FilterCountRecognitionStatus TryCreateDirectRangeSourcePlan(
        Expr source,
        SequencePipelineEvaluationServices services,
        SequencePipelineDiagnostics? diagnostics,
        ErrorContext evaluationContext,
        out FilterCountSourcePlan? sourcePlan,
        out EvalResult<Evaluator.CountedResult> result)
    {
        sourcePlan = null;
        result = default;

        var rangeSourceR = WithContext(evaluationContext, TryEvaluateBuiltinRangeSource(source, services));
        if (rangeSourceR.IsError)
        {
            // The direct builtin-range bounds themselves failed to evaluate.
            // Surface that error; no non-range source was evaluated here, so there
            // is no double evaluation.
            result = rangeSourceR.Error;
            return FilterCountRecognitionStatus.Error;
        }

        if (rangeSourceR.Value.IsDirectRange)
        {
            sourcePlan = new FilterCountSourcePlan.DirectRange(rangeSourceR.Value.Range);
            return FilterCountRecognitionStatus.Recognized;
        }

        // Non-range source: defer to the generic evaluator without evaluating it.
        diagnostics?.RecordDirectRangeFusionFallback(rangeSourceR.Value.FallbackReason);
        return FilterCountRecognitionStatus.Fallback;
    }

    private static FilterCountRecognitionStatus TryCreateSourcePlan(
        Expr source,
        SequencePipelineEvaluationServices services,
        SequencePipelineDiagnostics? diagnostics,
        ErrorContext evaluationContext,
        Func<EvalResult<IReadOnlyList<Evaluator.CountedResult>>> evaluateGenericSource,
        out FilterCountSourcePlan? sourcePlan,
        out EvalResult<Evaluator.CountedResult> result)
    {
        sourcePlan = null;
        result = default;

        var rangeSourceR = WithContext(evaluationContext, TryEvaluateBuiltinRangeSource(source, services));
        if (rangeSourceR.IsError)
        {
            result = rangeSourceR.Error;
            return FilterCountRecognitionStatus.Error;
        }

        if (rangeSourceR.Value.IsDirectRange)
        {
            sourcePlan = new FilterCountSourcePlan.DirectRange(rangeSourceR.Value.Range);
            return FilterCountRecognitionStatus.Recognized;
        }

        diagnostics?.RecordDirectRangeFusionFallback(rangeSourceR.Value.FallbackReason);

        var sourceItemsR = WithContext(evaluationContext, evaluateGenericSource());
        if (sourceItemsR.IsError)
        {
            result = sourceItemsR.Error;
            return FilterCountRecognitionStatus.Error;
        }

        sourcePlan = new FilterCountSourcePlan.Generic(
            sourceItemsR.Value,
            rangeSourceR.Value.FallbackReason);
        return FilterCountRecognitionStatus.Recognized;
    }

    private static EvalResult<SequencePipelineRangeSourceEvaluation> TryEvaluateBuiltinRangeSource(
        Expr source,
        SequencePipelineEvaluationServices services)
    {
        // Recognized plain sources are bare expressions (a spread filter
        // argument is an ordinary arity error and never reaches this probe).
        // A DOT receiver can still be a spread expression; spreading a range
        // list into the receiver value re-groups the same items, so fusing on
        // the peeled call stays value-equivalent there.
        source = UnwrapSpread(source);

        if (source is not Expr.Call(var function, var argsAlg))
            return EvalResult<SequencePipelineRangeSourceEvaluation>.Ok(
                SequencePipelineRangeSourceEvaluation.Fallback("source is not builtin range"));

        var calleeR = services.ResolveAlgorithm(function);
        if (calleeR.IsError || !IsBuiltin(calleeR.Value, BuiltinId.@range))
        {
            return EvalResult<SequencePipelineRangeSourceEvaluation>.Ok(
                SequencePipelineRangeSourceEvaluation.Fallback("source is not builtin range"));
        }

        if (argsAlg.Output.Count != 2)
        {
            return EvalResult<SequencePipelineRangeSourceEvaluation>.Ok(
                SequencePipelineRangeSourceEvaluation.Fallback("range argument shape unsupported"));
        }

        var rangeR = services.EvaluateRangeCallArguments(function, argsAlg, source.Span);
        return rangeR.IsError
            ? rangeR.Error
            : EvalResult<SequencePipelineRangeSourceEvaluation>.Ok(
                SequencePipelineRangeSourceEvaluation.Direct(rangeR.Value));
    }

    private static EvalResult<Evaluator.CountedResult> ExecuteFilterCount(
        FilterCountPipelinePlan plan,
        Evaluator.EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        SequencePipelineDiagnostics? diagnostics)
    {
        diagnostics?.RecordFilterCountFusionHit();

        return plan.SourcePlan switch
        {
            FilterCountSourcePlan.DirectRange directRange =>
                ExecuteRangeFilterCount(plan, directRange.Range, ctx, valEnv, diagnostics),
            FilterCountSourcePlan.Generic generic =>
                ExecuteGenericFilterCount(plan, generic, ctx, valEnv, diagnostics),
            _ => throw new InvalidOperationException($"Unsupported filter-count source plan '{plan.SourcePlan.GetType().Name}'."),
        };
    }

    private static EvalResult<Evaluator.CountedResult> ExecuteGenericFilterCount(
        FilterCountPipelinePlan plan,
        FilterCountSourcePlan.Generic sourcePlan,
        Evaluator.EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        SequencePipelineDiagnostics? diagnostics)
    {
        var diagnosticKey = diagnostics?.RecordPipelineDiagnostic(
            plan.Diagnostics,
            optimized: true,
            fallbackReason: null,
            sourceExecution: SourceExecutionEagerCollection,
            sourceExecutionFallbackReason: sourcePlan.DirectRangeFallbackReason);

        long predicateCalls = 0;
        long keptCount = 0;

        for (var index = 0; index < sourcePlan.SourceItems.Count; index++)
        {
            var predicateR = Evaluator.EvalFilterPredicateTruth(plan.Predicate, sourcePlan.SourceItems[index], index, ctx, valEnv);
            predicateCalls++;

            if (predicateR.IsError)
            {
                diagnostics?.RecordFilterCountPredicateCalls(predicateCalls);
                diagnostics?.RecordPipelineExecution(
                    diagnosticKey,
                    sourcePlan.SourceItems.Count,
                    predicateCalls,
                    resultCount: null,
                    avoidedFilteredResultMaterializationCount: keptCount,
                    avoidedSourceMaterializationCount: 0);
                diagnostics?.RecordAvoidedFilteredResultMaterialization(keptCount);
                return predicateR.Error;
            }

            if (predicateR.Value)
                keptCount++;
        }

        // Match the generic composition: filter materializes its kept items as
        // ONE exact immutable list value, and `count` opens exactly that one
        // list boundary through the shared builtin collection-item view, so the
        // fused count is always the kept-item count — a lone kept sequence
        // value (or list value) stays one exact element and counts as one.
        diagnostics?.RecordFilterCountPredicateCalls(predicateCalls);
        diagnostics?.RecordPipelineExecution(
            diagnosticKey,
            sourcePlan.SourceItems.Count,
            predicateCalls,
            keptCount,
            avoidedFilteredResultMaterializationCount: keptCount,
            avoidedSourceMaterializationCount: 0);
        diagnostics?.RecordAvoidedFilteredResultMaterialization(keptCount);

        return EvalResult<Evaluator.CountedResult>.Ok(
            new Evaluator.CountedResult(new Result.Atom(keptCount), 1));
    }

    private static EvalResult<Evaluator.CountedResult> ExecuteRangeFilterCount(
        FilterCountPipelinePlan plan,
        Evaluator.InclusiveRange range,
        Evaluator.EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        SequencePipelineDiagnostics? diagnostics)
    {
        diagnostics?.RecordDirectRangeFusionHit();

        var sourceCount = Evaluator.CountInclusiveRangeValues(range);
        var diagnosticKey = diagnostics?.RecordPipelineDiagnostic(
            plan.Diagnostics,
            optimized: true,
            fallbackReason: null,
            sourceExecution: SourceExecutionDirectRange,
            sourceExecutionFallbackReason: null);

        long predicateCalls = 0;
        long keptCount = 0;
        long sourceItemsSeen = 0;

        foreach (var value in Evaluator.EnumerateInclusiveRangeValues(range))
        {
            var item = new Evaluator.CountedResult(new Result.Atom(value), 1);
            var predicateIndex = predicateCalls <= int.MaxValue ? (int)predicateCalls : int.MaxValue;
            var predicateR = Evaluator.EvalFilterPredicateTruth(plan.Predicate, item, predicateIndex, ctx, valEnv);
            predicateCalls++;
            sourceItemsSeen++;

            if (predicateR.IsError)
            {
                diagnostics?.RecordFilterCountPredicateCalls(predicateCalls);
                diagnostics?.RecordPipelineExecution(
                    diagnosticKey,
                    sourceItemsSeen,
                    predicateCalls,
                    resultCount: null,
                    avoidedFilteredResultMaterializationCount: keptCount,
                    avoidedSourceMaterializationCount: sourceCount);
                diagnostics?.RecordAvoidedFilteredResultMaterialization(keptCount);
                diagnostics?.RecordAvoidedSourceMaterialization(sourceCount);
                return predicateR.Error;
            }

            if (predicateR.Value)
                keptCount++;
        }

        diagnostics?.RecordFilterCountPredicateCalls(predicateCalls);
        diagnostics?.RecordPipelineExecution(
            diagnosticKey,
            sourceItemsSeen,
            predicateCalls,
            keptCount,
            avoidedFilteredResultMaterializationCount: keptCount,
            avoidedSourceMaterializationCount: sourceCount);
        diagnostics?.RecordAvoidedFilteredResultMaterialization(keptCount);
        diagnostics?.RecordAvoidedSourceMaterialization(sourceCount);

        return EvalResult<Evaluator.CountedResult>.Ok(
            new Evaluator.CountedResult(new Result.Atom(keptCount), 1));
    }

    private static bool CountResolvesToBuiltin(
        SequencePipelineInvocation invocation,
        Evaluator.EvalCtx ctx)
        => invocation.Kind switch
        {
            SequencePipelineInvocationKind.DotCall => Evaluator.ResolvesToBuiltinAlgorithm(
                BuiltinId.@count.ToString(),
                BuiltinId.@count,
                ctx),
            SequencePipelineInvocationKind.PlainCall => invocation.PlainCallee is { } callee
                && IsBuiltin(callee, BuiltinId.@count),
            _ => false,
        };

    private static bool IsBuiltin(Algorithm algorithm, BuiltinId expectedBuiltin)
        => algorithm is Algorithm.Builtin(var builtin) && builtin == expectedBuiltin;

    private static Expr? TryGetPredicateExpression(FilterCountPipelineSyntax syntax)
        => syntax.Form switch
        {
            FilterCountPipelineForm.DotFilterDotCount or FilterCountPipelineForm.PlainCountDotFilter =>
                syntax.DotFilterArgs is { Output.Count: 1 } ? syntax.DotFilterArgs.Output[0] : null,
            FilterCountPipelineForm.PlainCountPlainFilter =>
                syntax.PlainFilterArgs is { Output.Count: 2 } ? syntax.PlainFilterArgs.Output[1] : null,
            _ => null,
        };

    private static ErrorContext EvaluationContext(FilterCountPipelineSyntax syntax)
        => syntax.Form switch
        {
            FilterCountPipelineForm.DotFilterDotCount or FilterCountPipelineForm.PlainCountDotFilter =>
                new DotCallContext(Evaluator.OpenExprName(syntax.Source), BuiltinId.@filter.ToString()),
            FilterCountPipelineForm.PlainCountPlainFilter =>
                new CallContext(Evaluator.OpenExprName(syntax.PlainFilterFunction!)),
            _ => throw new InvalidOperationException($"Unsupported filter-count pipeline form '{syntax.Form}'."),
        };

    private static EvalResult<T> WithContext<T>(ErrorContext context, EvalResult<T> result)
        // Resource-limit errors never get extra context, matching the evaluator: the limit
        // belongs to the run, not to the pipeline stage that happened to reach it.
        => result.IsError && !result.Error.IsResourceLimit
            ? new EvalError.WithContext(context, result.Error) { Span = result.Error.Span }
            : result;

    private static void RecordFilterCountFallback(
        SequencePipelineDiagnostics? diagnostics,
        SequencePipelinePlan plan,
        string reason)
    {
        diagnostics?.RecordFilterCountFusionFallback(reason);
        diagnostics?.RecordPipelineDiagnostic(
            plan,
            optimized: false,
            fallbackReason: reason,
            sourceExecution: SourceExecutionNotExecuted,
            sourceExecutionFallbackReason: null);
    }

    private static SequencePipelinePlan CreateDiagnosticPlan(
        FilterCountPipelineForm form,
        Expr source,
        Expr? predicateExpr,
        Algorithm? predicateAlg,
        string sourceKind = GenericSourceKind)
    {
        var sourceSummary = SequencePipelineSourceSummary(source);
        var predicateSummary = SequencePipelinePredicateSummary(predicateExpr, predicateAlg);
        var formSummary = FormName(form);
        return new SequencePipelinePlan(
            Identity: $"filter-count:{formSummary}:{sourceSummary}:{predicateSummary}",
            Summary: "filter-count",
            Form: formSummary,
            Fusion: FilterCountFusion,
            SourceKind: sourceKind,
            SourceSummary: sourceSummary,
            PredicateSummary: predicateSummary);
    }

    private static string SourceKind(FilterCountSourcePlan sourcePlan)
        => sourcePlan switch
        {
            FilterCountSourcePlan.DirectRange => BuiltinRangeSourceKind,
            FilterCountSourcePlan.Generic => GenericSourceKind,
            _ => GenericSourceKind,
        };

    private static string SequencePipelineSourceSummary(Expr source)
        => source is Expr.Call(Expr.Resolve(var name), _)
            ? $"{name}(...)"
            : Evaluator.OpenExprName(source);

    private static string SequencePipelinePredicateSummary(
        Expr? predicateExpr,
        Algorithm? predicateAlg)
    {
        if (predicateAlg is not null && Evaluator.TryGetAlgorithmPath(predicateAlg) is { } path)
            return path;

        if (predicateExpr is not null)
            return Evaluator.OpenExprName(predicateExpr);

        return "(unknown)";
    }
}
