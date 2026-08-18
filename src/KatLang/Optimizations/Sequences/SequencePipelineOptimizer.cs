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

    private readonly record struct BuiltinRangeSourceSyntax(
        Expr Function,
        OutputBundle Arguments,
        SourceSpan? Span);

    private readonly record struct FilterCountPipelinePreparation(
        FilterCountPipelineSyntax Syntax,
        Algorithm Predicate,
        Expr? PredicateExpression,
        BuiltinRangeSourceSyntax? DirectRangeSource,
        string DirectRangeFallbackReason);

    internal static bool TryExecute(
        SequencePipelineInvocation invocation,
        SequencePipelineEvaluationServices services,
        Evaluator.EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        SequencePipelineDiagnostics? diagnostics,
        out EvalResult<Evaluator.CountedResult> result)
    {
        result = default;

        // Purely syntactic shape recognition: no lookup, no evaluation, no budget
        // charge. An expression that is not a filter-count pipeline therefore reaches
        // the generic evaluator having consumed nothing here.
        if (!TryRecognizeFilterCountSyntax(invocation, out var syntax, out var syntaxFallbackReason))
        {
            if (syntaxFallbackReason is not null)
            {
                RecordFilterCountFallback(
                    diagnostics,
                    diagnostics is null
                        ? null
                        : CreateDiagnosticPlan(
                            syntax.Form,
                            syntax.Source,
                            predicateExpr: null,
                            predicateAlg: null),
                    syntaxFallbackReason);
            }

            return false;
        }

        // Finish every PURE eligibility check before committing to fusion. In
        // particular, an optimizer-disabled run and a lookup/shape fallback must not
        // charge PeakDepth merely because the tree looked like a candidate. That would
        // make the forced-generic oracle pass through the same accounting under review.
        var preparationStatus = TryPrepareFilterCountPipeline(
            syntax,
            invocation,
            services,
            ctx,
            diagnostics,
            out var preparation);
        if (preparationStatus is FilterCountRecognitionStatus.NotRecognized or FilterCountRecognitionStatus.Fallback)
            return false;
        if (preparationStatus != FilterCountRecognitionStatus.Recognized)
            throw new InvalidOperationException($"Unexpected filter-count preparation status '{preparationStatus}'.");

        // Dynamic depth is an ALWAYS-ACTIVE budget, so it cannot be made
        // strategy-independent the way the opt-in step and cumulative budgets are —
        // `Evaluator.CreateRootCtx` protects those by forcing the generic strategy
        // once they are configured, which presupposes an unconfigured state where the
        // budget has no verdict. Depth always has one, so it has to be EQUALIZED here
        // instead, exactly as the always-active per-collection ceiling already is
        // (`EvaluationBudget.CheckCollectionSize`).
        //
        // The generic spelling evaluates this pipeline's collection argument through
        // one depth-only argument-evaluation level and runs the filter callbacks
        // INSIDE it (`Evaluator.EvalSequenceBuiltinDotReceiverCounted`, or the
        // plain-call argument funnel). A fused pipeline that elided that level would
        // let the same program survive a depth limit the generic strategy rejects,
        // and which strategy runs depends on which UNRELATED budgets the caller
        // configured — so an unrelated, non-binding `MaxStringLength` would decide a
        // `MaxDepth` verdict.
        //
        // This is the COMMIT point: all remaining paths either evaluate the source and
        // execute fusion or return a committed source-evaluation error. When the level
        // is unavailable the generic path charges the same funnel and reports the same
        // limit error, so fallback cannot mask or double-charge a limit.
        if (ctx.Budget.TryEnterArgumentEvaluation() is not null)
            return false;

        try
        {
            var status = TryCreateFilterCountPlan(
                preparation,
                services,
                ctx,
                diagnostics,
                out var plan,
                out result);

            if (status == FilterCountRecognitionStatus.Error)
                return true;
            if (status != FilterCountRecognitionStatus.Recognized)
                throw new InvalidOperationException($"Unexpected committed filter-count status '{status}'.");

            result = WithContext(
                plan!.EvaluationSyntax,
                ctx,
                ExecuteFilterCount(plan, ctx, valEnv, diagnostics));
            return true;
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    private static string FormName(FilterCountPipelineForm form)
        => form switch
        {
            FilterCountPipelineForm.DotFilterDotCount => "dot-filter-dot-count",
            FilterCountPipelineForm.PlainCountDotFilter => "plain-count-dot-filter",
            FilterCountPipelineForm.PlainCountPlainFilter => "plain-count-plain-filter",
            _ => form.ToString(),
        };

    /// <summary>
    /// Everything after the purely syntactic shape match that can still reject fusion
    /// without evaluating source or callback code. No budget is charged here; the
    /// caller enters the collection-argument depth level only after this method returns
    /// <see cref="FilterCountRecognitionStatus.Recognized"/>.
    /// </summary>
    private static FilterCountRecognitionStatus TryPrepareFilterCountPipeline(
        FilterCountPipelineSyntax syntax,
        SequencePipelineInvocation invocation,
        SequencePipelineEvaluationServices services,
        Evaluator.EvalCtx ctx,
        SequencePipelineDiagnostics? diagnostics,
        out FilterCountPipelinePreparation preparation)
    {
        preparation = default;

        var predicateExpr = TryGetPredicateExpression(syntax);
        var diagnosticPlan = diagnostics is null
            ? null
            : CreateDiagnosticPlan(syntax.Form, syntax.Source, predicateExpr, predicateAlg: null);

        if (!ctx.EnableSequencePipelineOptimization)
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "sequence pipeline optimization disabled");
            return FilterCountRecognitionStatus.Fallback;
        }

        if (!CountResolvesToBuiltin(invocation, services))
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "count does not resolve to builtin");
            return FilterCountRecognitionStatus.Fallback;
        }

        return syntax.Form switch
        {
            FilterCountPipelineForm.DotFilterDotCount or FilterCountPipelineForm.PlainCountDotFilter =>
                TryPrepareDotFilterCount(
                    syntax, services, diagnostics, predicateExpr, diagnosticPlan, out preparation),
            FilterCountPipelineForm.PlainCountPlainFilter =>
                TryPreparePlainFilterCount(
                    syntax, services, diagnostics, predicateExpr, diagnosticPlan, out preparation),
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
        OutputBundle? argsOpt,
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
                FilterExpression: target,
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
        OutputBundle args,
        out FilterCountPipelineSyntax syntax,
        out string? fallbackReason)
    {
        syntax = default;
        fallbackReason = null;

        if (function is not Expr.Resolve(var countName) || countName != BuiltinId.@count.ToString())
            return false;

        if (args.Count != 1)
        {
            if (TryFindFilterCountSourceCandidate(args, out syntax))
                fallbackReason = "unsupported count argument shape";

            return false;
        }

        // Under fixed collection-object arity the valid plain composition is
        // the BARE one-argument form — `count(filter(src, pred))` or
        // `count(src.filter(pred))` — where the filter result is count's one
        // collection argument. A spread form such as `count(filter(...)*)`
        // supplies the spread items as separate arguments and is an ordinary
        // arity error, so it must NOT be recognized: it falls back to the
        // generic evaluator, which reports the arity mismatch.
        var countSource = args[0];
        if (countSource is Expr.SequenceSpread)
            return false;

        if (countSource is Expr.DotCall(var dotSource, var filterName, var dotFilterArgs)
            && filterName == BuiltinId.@filter.ToString())
        {
            syntax = new FilterCountPipelineSyntax(
                FilterCountPipelineForm.PlainCountDotFilter,
                dotSource,
                FilterExpression: countSource,
                dotFilterArgs,
                PlainFilterFunction: null,
                PlainFilterArgs: null);
            return true;
        }

        if (countSource is Expr.Call(var filterFunction, var plainFilterArgs)
            && IsFilterFunctionCandidate(filterFunction))
        {
            var plainSource = plainFilterArgs.Count > 0
                ? plainFilterArgs[0]
                : countSource;
            syntax = new FilterCountPipelineSyntax(
                FilterCountPipelineForm.PlainCountPlainFilter,
                plainSource,
                FilterExpression: countSource,
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
                    FilterExpression: candidate,
                    dotFilterArgs,
                    PlainFilterFunction: null,
                    PlainFilterArgs: null);
                return true;
            }

            if (candidate is Expr.Call(var filterFunction, var plainFilterArgs)
                && IsFilterFunctionCandidate(filterFunction))
            {
                var plainSource = plainFilterArgs.Count > 0
                    ? UnwrapSpread(plainFilterArgs[0])
                    : candidate;
                syntax = new FilterCountPipelineSyntax(
                    FilterCountPipelineForm.PlainCountPlainFilter,
                    plainSource,
                    FilterExpression: candidate,
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

    // Returns the innermost operand of a (possibly nested) unary spread, or the
    // expression unchanged when it is not a spread. This is a recognition
    // helper, not a general semantic rewrite: chained spread can open more than
    // one list boundary (`[[7]]**` differs from one layer).
    // Callers either use the peeled form only to identify an unsupported
    // filter/count candidate, or to identify a builtin range source whose flat
    // scalar result is unchanged by additional spread layers.
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

    private static FilterCountRecognitionStatus TryPrepareDotFilterCount(
        FilterCountPipelineSyntax syntax,
        SequencePipelineEvaluationServices services,
        SequencePipelineDiagnostics? diagnostics,
        Expr? predicateExpr,
        SequencePipelinePlan? diagnosticPlan,
        out FilterCountPipelinePreparation preparation)
    {
        preparation = default;

        if (syntax.DotFilterArgs is null || syntax.DotFilterArgs.Count == 0)
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "unsupported filter argument shape");
            return FilterCountRecognitionStatus.Fallback;
        }

        if (syntax.DotFilterArgs.Count != 1)
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "unsupported extra arguments");
            return FilterCountRecognitionStatus.Fallback;
        }

        if (syntax.DotFilterArgs[0] is Expr.SequenceSpread)
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "unsupported explicit spread argument");
            return FilterCountRecognitionStatus.Fallback;
        }

        // The probe consumes the ORIGINAL filter dot-edge node, so the
        // elaborated fact (the lexical-fallback identity) gates
        // fusion exactly as they gate generic dispatch.
        var filterLookupFallbackReason = services.GetDotCallLexicalBuiltinFallbackReason(
            (Expr.DotCall)syntax.FilterExpression,
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

        var isDirectRange = TryRecognizeBuiltinRangeSource(
            syntax.Source,
            services,
            out var directRangeSource,
            out var directRangeFallbackReason);
        preparation = new FilterCountPipelinePreparation(
            syntax,
            predicateAlg,
            predicateExpr,
            isDirectRange ? directRangeSource : null,
            directRangeFallbackReason);
        return FilterCountRecognitionStatus.Recognized;
    }

    private static FilterCountRecognitionStatus TryPreparePlainFilterCount(
        FilterCountPipelineSyntax syntax,
        SequencePipelineEvaluationServices services,
        SequencePipelineDiagnostics? diagnostics,
        Expr? predicateExpr,
        SequencePipelinePlan? diagnosticPlan,
        out FilterCountPipelinePreparation preparation)
    {
        preparation = default;

        var filterFunction = syntax.PlainFilterFunction!;
        var filterArgs = syntax.PlainFilterArgs!;

        // Fixed collection-object arity: `filter(collection, predicate)` is
        // exactly two arguments, and a spread argument would change the
        // supplied argument count — such a program is an ordinary arity error
        // and must fall back so the generic evaluator reports it.
        if (filterArgs.Count != 2)
        {
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "unsupported filter argument shape");
            return FilterCountRecognitionStatus.Fallback;
        }

        if (filterArgs.Any(static expr => expr is Expr.SequenceSpread))
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

        // Plain `count(filter(SOURCE, pred))` only fuses a direct builtin-range
        // source. Recognition is lookup-only and never evaluates range bounds or a
        // generic/non-range source, so a fallback remains budget- and side-effect-free.
        if (!TryRecognizeBuiltinRangeSource(
            syntax.Source,
            services,
            out var directRangeSource,
            out var directRangeFallbackReason))
        {
            diagnostics?.RecordDirectRangeFusionFallback(directRangeFallbackReason);
            RecordFilterCountFallback(diagnostics, diagnosticPlan, "non-range source for plain filter-count");
            return FilterCountRecognitionStatus.Fallback;
        }

        var predicateAlg = filterArgAlgsR.Value[1];
        preparation = new FilterCountPipelinePreparation(
            syntax,
            predicateAlg,
            predicateExpr,
            directRangeSource,
            DirectRangeFallbackReason: "");
        return FilterCountRecognitionStatus.Recognized;
    }

    /// <summary>
    /// Lookup-only direct-range recognition. This method never evaluates a bound or a
    /// generic source, which lets the caller establish the exact depth-charge commit
    /// point after every possible optimizer fallback.
    /// </summary>
    private static bool TryRecognizeBuiltinRangeSource(
        Expr source,
        SequencePipelineEvaluationServices services,
        out BuiltinRangeSourceSyntax rangeSource,
        out string fallbackReason)
    {
        // Recognized plain sources are bare expressions (a spread filter
        // argument is an ordinary arity error and never reaches this probe).
        // A DOT receiver can still be a spread expression; spreading a range
        // list into the receiver value re-groups the same items, so fusing on
        // the peeled call stays value-equivalent there.
        source = UnwrapSpread(source);

        if (source is not Expr.Call(var function, var callArgs))
        {
            rangeSource = default;
            fallbackReason = "source is not builtin range";
            return false;
        }

        var calleeR = services.ResolveAlgorithm(function);
        if (calleeR.IsError || !IsBuiltin(calleeR.Value, BuiltinId.@range))
        {
            rangeSource = default;
            fallbackReason = "source is not builtin range";
            return false;
        }

        if (callArgs.Count != 2)
        {
            rangeSource = default;
            fallbackReason = "range argument shape unsupported";
            return false;
        }

        rangeSource = new BuiltinRangeSourceSyntax(function, callArgs, source.Span);
        fallbackReason = "";
        return true;
    }

    /// <summary>
    /// The committed fused region. The caller holds the outer collection-argument
    /// depth level across source evaluation and the later callbacks. No fallback is
    /// possible from here: source failures are returned as optimized-path errors.
    /// </summary>
    private static FilterCountRecognitionStatus TryCreateFilterCountPlan(
        FilterCountPipelinePreparation preparation,
        SequencePipelineEvaluationServices services,
        Evaluator.EvalCtx ctx,
        SequencePipelineDiagnostics? diagnostics,
        out FilterCountPipelinePlan? plan,
        out EvalResult<Evaluator.CountedResult> result)
    {
        plan = null;
        result = default;

        FilterCountSourcePlan sourcePlan;
        if (preparation.DirectRangeSource is { } directRangeSource)
        {
            var rangeR = WithContext(
                preparation.Syntax,
                ctx,
                services.EvaluateRangeCallArguments(
                    directRangeSource.Function,
                    directRangeSource.Arguments,
                    directRangeSource.Span));
            if (rangeR.IsError)
            {
                result = rangeR.Error;
                return FilterCountRecognitionStatus.Error;
            }

            sourcePlan = new FilterCountSourcePlan.DirectRange(rangeR.Value);
        }
        else
        {
            if (preparation.Syntax.Form == FilterCountPipelineForm.PlainCountPlainFilter)
                throw new InvalidOperationException("A committed plain filter-count pipeline must have a direct range source.");

            diagnostics?.RecordDirectRangeFusionFallback(preparation.DirectRangeFallbackReason);
            var sourceItemsR = WithContext(
                preparation.Syntax,
                ctx,
                services.EvaluateDotReceiverIterationItems(preparation.Syntax.Source));
            if (sourceItemsR.IsError)
            {
                result = sourceItemsR.Error;
                return FilterCountRecognitionStatus.Error;
            }

            sourcePlan = new FilterCountSourcePlan.Generic(
                sourceItemsR.Value,
                preparation.DirectRangeFallbackReason);
        }

        var sourceKind = SourceKind(sourcePlan);
        plan = new FilterCountPipelinePlan(
            preparation.Syntax.Source,
            sourcePlan,
            preparation.Predicate,
            preparation.Syntax.Form,
            preparation.PredicateExpression,
            preparation.Syntax,
            diagnostics is null
                ? null
                : CreateDiagnosticPlan(
                    preparation.Syntax.Form,
                    preparation.Syntax.Source,
                    preparation.PredicateExpression,
                    preparation.Predicate,
                    sourceKind));
        return FilterCountRecognitionStatus.Recognized;
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
            plan.Diagnostics!,
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
            plan.Diagnostics!,
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
        SequencePipelineEvaluationServices services)
        => invocation.Kind switch
        {
            // The dot form probes through the shared evaluator legality check
            // on the ORIGINAL count dot-edge node, so fusion observes exactly
            // the generic dispatch: a parameter-bound member falls back to the
            // generic path, which resolves the stored fallback identity
            // instead of the builtin.
            SequencePipelineInvocationKind.DotCall => services.GetDotCallLexicalBuiltinFallbackReason(
                invocation.Dot!,
                BuiltinId.@count) is null,
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
                syntax.DotFilterArgs is { Count: 1 } ? syntax.DotFilterArgs[0] : null,
            FilterCountPipelineForm.PlainCountPlainFilter =>
                syntax.PlainFilterArgs is { Count: 2 } ? syntax.PlainFilterArgs[1] : null,
            _ => null,
        };

    private static ErrorContext EvaluationContext(
        FilterCountPipelineSyntax syntax,
        Evaluator.EvalCtx ctx)
        => syntax.Form switch
        {
            FilterCountPipelineForm.DotFilterDotCount or FilterCountPipelineForm.PlainCountDotFilter =>
                new DotCallContext(
                    Evaluator.CallDiagnosticExprName(syntax.Source, ctx),
                    BuiltinId.@filter.ToString()),
            FilterCountPipelineForm.PlainCountPlainFilter =>
                new CallContext(Evaluator.CallDiagnosticExprName(syntax.PlainFilterFunction!, ctx)),
            _ => throw new InvalidOperationException($"Unsupported filter-count pipeline form '{syntax.Form}'."),
        };

    /// <summary>
    /// Reproduces the DIAGNOSTIC BOUNDARY of the <c>filter</c> expression that fusion
    /// elided. The generic evaluator dispatches that expression as
    /// <c>WithSpan(filterExpr.Span, WithCallCtx/WithDotCallCtx(...))</c>; the fused
    /// pipeline never evaluates the node, so both halves have to be applied here.
    /// <para>Without the span half, a stage error that arrives with NO span (a callback
    /// <see cref="EvalError.BadArity"/>, for example) floated up to the enclosing
    /// <c>count(...)</c> expression and was stamped with the count span. It is
    /// <c>AtSpanIfMissing</c> semantics, so an error that already carries a more
    /// specific inner span (a division by zero inside the predicate) keeps it.</para>
    /// <para>Resource-limit errors never get extra CONTEXT, matching the evaluator: the
    /// limit belongs to the run, not to the pipeline stage that happened to reach it.
    /// Span attribution is unconditional, exactly as in <c>Evaluator.WithSpan</c>.</para>
    /// </summary>
    private static EvalResult<T> WithContext<T>(
        FilterCountPipelineSyntax syntax,
        Evaluator.EvalCtx ctx,
        EvalResult<T> result)
        => Evaluator.WithSpan(
            syntax.FilterExpression.Span,
            result.IsError && !result.Error.IsResourceLimit
                ? new EvalError.WithContext(EvaluationContext(syntax, ctx), result.Error) { Span = result.Error.Span }
                : result);

    private static void RecordFilterCountFallback(
        SequencePipelineDiagnostics? diagnostics,
        SequencePipelinePlan? plan,
        string reason)
    {
        if (diagnostics is null)
            return;

        diagnostics.RecordFilterCountFusionFallback(reason);
        diagnostics.RecordPipelineDiagnostic(
            plan!,
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
