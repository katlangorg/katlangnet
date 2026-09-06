using System.Numerics;

namespace KatLang.Optimizations.Loops;

internal static partial class LoopOptimizer
{
    internal static bool TryEvaluateWhile(
        Algorithm step,
        IReadOnlyList<Result> stateValues,
        Evaluator.EvalCtx ctx,
        IReadOnlyList<(string Name, Result Value)> valEnv,
        Func<IReadOnlyList<Result>, EvalResult<Evaluator.CountedResult>> genericContinuation,
        out EvalResult<Evaluator.CountedResult> result)
    {
        var plan = TryBuildLoopPlanTemplate(LoopKind.While, step, stateValues.Count, ctx, valEnv);
        if (plan is null)
        {
            result = default;
            return false;
        }

        ctx.LoopDiagnostics?.RecordOptimizedLoopHit();
        var frame = new LoopRunFrame(plan, valEnv, stateValues);
        while (true)
        {
            // A fully-planned iteration touches a charging budget chokepoint only where
            // the generic path charges one — a planned `if` argument level, a temp read,
            // a temp call — and an iteration of bare planned arithmetic touches none (this
            // path never runs under a step budget), so this is the one guaranteed
            // per-iteration host-cancellation observation. It must stay observation-only:
            // charging any counter here would break the pinned optimized-vs-generic
            // accounting parity.
            ctx.Budget.ObserveCancellation();
            ctx.LoopDiagnostics?.RecordLoopIteration();
            frame.BeginIteration();
            var requiresGenericContinuation = false;

            for (var i = 0; i < plan.NextStateOutputs.Count; i++)
            {
                var outputR = EvalTopLevelLoopExprPlan(plan.NextStateOutputs[i], frame);
                if (outputR.IsError)
                {
                    result = outputR.Error;
                    return true;
                }

                // Normal iterations RETAIN the evaluated output (a struct copy into the
                // frame's reusable buffer); the generic output-slot representation is
                // deliberately NOT built here — it is materialized only inside an
                // actual handover branch below (M16).
                frame.SetIterationOutput(i, outputR.Value);

                // The optimized frame packs one value per state slot, so it can
                // only represent step expressions that emit EXACTLY one value.
                // A zero- or multi-emitting expression grows/shrinks the generic
                // state-slot vector. Finish THIS iteration once, using the same
                // already-evaluated slots, then continue generically from the
                // resulting next state. Never restart the iteration: doing so
                // would duplicate property evaluation, random draws, or errors.
                if (outputR.Value.EmittedCount != 1)
                {
                    ctx.LoopDiagnostics?.RecordOptimizedLoopFallback("loop expression did not emit exactly one state value");
                    requiresGenericContinuation = true;
                }
                else if (!requiresGenericContinuation)
                {
                    frame.SetScratchSlot(i, outputR.Value.ToResult());
                }
            }

            var continuationR = EvalTopLevelLoopExprPlan(plan.ContinuationOutput!, frame);
            if (continuationR.IsError)
            {
                result = continuationR.Error;
                return true;
            }

            frame.SetIterationOutput(plan.NextStateOutputs.Count, continuationR.Value);

            // A continuation expression emitting other than one value changes
            // which generic slot is the continuation flag; generic semantics
            // must decide from the already-evaluated iteration slots.
            if (continuationR.Value.EmittedCount != 1)
            {
                ctx.LoopDiagnostics?.RecordOptimizedLoopFallback("loop continuation did not emit exactly one value");
                requiresGenericContinuation = true;
            }

            if (requiresGenericContinuation)
            {
                var outputSlots = MaterializeGenericHandoverSlots(frame, includeContinuation: true);
                var splitR = Evaluator.SplitContSlots(outputSlots);
                if (splitR.IsError)
                {
                    result = splitR.Error;
                    return true;
                }

                var (nextStateSlots, continueValue) = splitR.Value;
                result = continueValue == 0
                    ? frame.CurrentStateResult()
                    : genericContinuation(nextStateSlots);
                return true;
            }

            var contR = continuationR.Value.AsNum() is { } cont
                ? EvalResult<Decimal128>.Ok(cont)
                : Evaluator.ExpectInt(continuationR.Value.ToResult());
            if (contR.IsError)
            {
                result = contR.Error;
                return true;
            }

            if (contR.Value == 0)
            {
                result = frame.CurrentStateResult();
                return true;
            }

            if (!frame.TryCommitScratchFast())
            {
                ctx.LoopDiagnostics?.RecordOptimizedLoopFallback("loop next-state arity changed");
                // Every output emitted exactly one value on this branch, so the
                // state-only materialization equals the historical full list minus its
                // final continuation slot.
                result = genericContinuation(MaterializeGenericHandoverSlots(frame, includeContinuation: false));
                return true;
            }
        }
    }

    internal static bool TryEvaluateRepeat(
        Algorithm step,
        long count,
        IReadOnlyList<Result> stateValues,
        Evaluator.EvalCtx ctx,
        IReadOnlyList<(string Name, Result Value)> valEnv,
        Func<long, IReadOnlyList<Result>, EvalResult<Evaluator.CountedResult>> genericContinuation,
        out EvalResult<Evaluator.CountedResult> result)
    {
        var plan = TryBuildLoopPlanTemplate(LoopKind.Repeat, step, stateValues.Count, ctx, valEnv);
        if (plan is null)
        {
            result = default;
            return false;
        }

        ctx.LoopDiagnostics?.RecordOptimizedLoopHit();
        var frame = new LoopRunFrame(plan, valEnv, stateValues);
        for (var iteration = 0L; iteration < count; iteration++)
        {
            // Same rule as the optimized while path: an iteration of bare planned
            // arithmetic touches no charging chokepoint, so observe host cancellation
            // here, observation-only.
            ctx.Budget.ObserveCancellation();
            ctx.LoopDiagnostics?.RecordLoopIteration();
            frame.BeginIteration();
            var requiresGenericContinuation = false;

            for (var i = 0; i < plan.NextStateOutputs.Count; i++)
            {
                var outputR = EvalTopLevelLoopExprPlan(plan.NextStateOutputs[i], frame);
                if (outputR.IsError)
                {
                    result = outputR.Error;
                    return true;
                }

                // Retained, not materialized — see the while path (M16).
                frame.SetIterationOutput(i, outputR.Value);

                // Same exactly-one-value rule as the while path: the optimized
                // frame cannot represent a changed state-slot vector. Complete
                // the current iteration exactly once, then hand its assembled
                // next state to the generic evaluator for remaining iterations.
                if (outputR.Value.EmittedCount != 1)
                {
                    ctx.LoopDiagnostics?.RecordOptimizedLoopFallback("loop expression did not emit exactly one state value");
                    requiresGenericContinuation = true;
                }
                else if (!requiresGenericContinuation)
                {
                    frame.SetScratchSlot(i, outputR.Value.ToResult());
                }
            }

            if (requiresGenericContinuation)
            {
                var outputSlots = MaterializeGenericHandoverSlots(frame, includeContinuation: false);
                var remainingCount = count - iteration - 1;
                result = remainingCount == 0
                    ? Evaluator.MakeCheckedLoopStateResult(ctx, outputSlots)
                    : genericContinuation(remainingCount, outputSlots);
                return true;
            }

            if (iteration == count - 1)
            {
                result = frame.ScratchStateResult();
                return true;
            }

            if (!frame.TryCommitScratchFast())
            {
                ctx.LoopDiagnostics?.RecordOptimizedLoopFallback("loop next-state arity changed");
                var outputSlots = MaterializeGenericHandoverSlots(frame, includeContinuation: false);
                var remainingCount = count - iteration - 1;
                result = remainingCount == 0
                    ? Evaluator.MakeCheckedLoopStateResult(ctx, outputSlots)
                    : genericContinuation(remainingCount, outputSlots);
                return true;
            }
        }

        result = frame.CurrentStateResult();
        return true;
    }

    /// <summary>
    /// Builds the generic evaluator's output-slot list for the CURRENT iteration from
    /// the frame's retained planned outputs — state outputs in order, then (when
    /// requested) the while continuation. This runs ONLY inside an actual handover
    /// branch, exactly once per handover (M16): normal optimized iterations retain
    /// their outputs as structs and never construct this representation. Pure
    /// representation work — it charges no budget, observes no cancellation, and
    /// evaluates nothing; every value was already evaluated exactly once by the
    /// iteration itself, so materializing here can neither replay a callback nor
    /// reorder an effect.
    /// </summary>
    private static List<Result> MaterializeGenericHandoverSlots(
        LoopRunFrame frame,
        bool includeContinuation)
    {
        frame.IterationCtx.Observations?.RecordOptimizedLoopHandoverMaterialization();
        var template = frame.Template;
        var outputSlots = new List<Result>();
        for (var i = 0; i < template.NextStateOutputs.Count; i++)
            AppendGenericLoopOutputSlots(outputSlots, template.NextStateOutputs[i].Source, frame.GetIterationOutput(i));

        if (includeContinuation)
        {
            AppendGenericLoopOutputSlots(
                outputSlots,
                template.ContinuationOutput!.Source,
                frame.GetIterationOutput(template.NextStateOutputs.Count));
        }

        return outputSlots;
    }

    /// <summary>
    /// Assemble one already-evaluated loop output expression exactly as the
    /// generic <c>EvalAlgOutputSlots</c> path does for flat loop steps. A
    /// non-spread zero-emission expression remains one visible state slot;
    /// spread contributes its emitted items only; and multi-emission results
    /// reopen their top-level sequence supply.
    /// </summary>
    private static void AppendGenericLoopOutputSlots(
        List<Result> slots,
        Expr source,
        PlannedLoopValue output)
    {
        if (output.EmittedCount == 0)
        {
            if (source is not Expr.SequenceSpread)
                slots.Add(output.ToResult());
            return;
        }

        if (output.EmittedCount == 1)
        {
            slots.Add(output.ToResult());
            return;
        }

        slots.AddRange(output.ToResult().ToItems());
    }

    private static LoopPlanTemplate? TryBuildLoopPlanTemplate(
        LoopKind kind,
        Algorithm step,
        int stateArity,
        Evaluator.EvalCtx ctx,
        IReadOnlyList<(string Name, Result Value)> parentValEnv)
    {
        ctx.LoopDiagnostics?.RecordLoopPlanBuild();

        if (stateArity <= 0 || step is not Algorithm.User userStep)
        {
            RecordLoopPlanFallbackDiagnostic(kind, step, stateArity, ctx, "loop plan unsupported step shape");
            return null;
        }

        if (userStep.FindDuplicatePropName() is not null || userStep.Params.Count != stateArity)
        {
            RecordLoopPlanFallbackDiagnostic(kind, step, stateArity, ctx, "loop plan parameter/property shape mismatch");
            return null;
        }

        var expectedOutputCount = kind == LoopKind.While ? stateArity + 1 : stateArity;
        if (userStep.Output.Count != expectedOutputCount)
        {
            RecordLoopPlanFallbackDiagnostic(kind, step, stateArity, ctx, "loop plan output arity mismatch");
            return null;
        }

        var loopCtx = ShadowLoopStepCountedParamEnv(ctx, userStep);
        var iterationCtx = loopCtx.Push(userStep);
        var tempPlanBuild = BuildLoopTempPlans(
            userStep,
            userStep.Params,
            iterationCtx,
            parentValEnv,
            includeDiagnostics: ctx.LoopDiagnostics is not null);
        var tempPlans = tempPlanBuild.Plans;

        var nextStateOutputs = new List<LoopExprPlan>(stateArity);
        var requiresPerIterationCacheIdentity = false;
        for (var i = 0; i < stateArity; i++)
        {
            var plan = BuildLoopExprPlan(userStep.Output[i], userStep.Params, iterationCtx, parentValEnv, tempPlans);
            if (!plan.IsFullyPlanned)
                requiresPerIterationCacheIdentity = true;
            nextStateOutputs.Add(plan.Plan);
        }

        LoopExprPlan? continuationOutput = null;
        if (kind == LoopKind.While)
        {
            var plan = BuildLoopExprPlan(userStep.Output[stateArity], userStep.Params, iterationCtx, parentValEnv, tempPlans);
            if (!plan.IsFullyPlanned)
                requiresPerIterationCacheIdentity = true;
            continuationOutput = plan.Plan;
        }

        if (requiresPerIterationCacheIdentity && tempPlans.Count != 0)
        {
            const string reason = "local properties require the shared generic cache in a partially planned loop";
            tempPlans = [];
            nextStateOutputs.Clear();
            for (var index = 0; index < stateArity; index++)
            {
                nextStateOutputs.Add(BuildLoopExprPlan(
                    userStep.Output[index], userStep.Params, iterationCtx, parentValEnv, tempPlans).Plan);
            }

            if (kind == LoopKind.While)
            {
                continuationOutput = BuildLoopExprPlan(
                    userStep.Output[stateArity], userStep.Params, iterationCtx, parentValEnv, tempPlans).Plan;
            }

            tempPlanBuild = new LoopTempPlanBuild(tempPlans, tempPlanBuild.Diagnostics.Select(temp => temp.Planned
                ? temp with { Planned = false, PlanSummary = null, FallbackReason = reason }
                : temp).ToArray());
        }

        string? diagnosticKey = null;
        if (ctx.LoopDiagnostics is { } diagnostics)
        {
            var expressionDiagnostics = BuildLoopExpressionDiagnostics(nextStateOutputs, continuationOutput);
            diagnosticKey = diagnostics.RecordLoopPlanDiagnostic(
                LoopPlanIdentity(kind, step),
                LoopKindName(kind),
                stateArity,
                optimized: true,
                fallbackReason: null,
                temps: tempPlanBuild.Diagnostics,
                expressions: expressionDiagnostics);
        }

        return new LoopPlanTemplate(
            kind,
            userStep,
            stateArity,
            tempPlans,
            nextStateOutputs,
            continuationOutput,
            requiresPerIterationCacheIdentity,
            loopCtx,
            diagnosticKey);
    }

    private static Evaluator.EvalCtx ShadowLoopStepCountedParamEnv(
        Evaluator.EvalCtx ctx,
        Algorithm.User userStep)
        => ctx.WithCountedParamEnv(Evaluator.ShadowCountedParamEnv(ctx.CountedParamEnv, userStep.Params));

    private static void RecordLoopPlanFallbackDiagnostic(
        LoopKind kind,
        Algorithm step,
        int stateArity,
        Evaluator.EvalCtx ctx,
        string reason)
    {
        ctx.LoopDiagnostics?.RecordOptimizedLoopFallback(reason);
        var diagnosticKey = ctx.LoopDiagnostics?.RecordLoopPlanDiagnostic(
            LoopPlanIdentity(kind, step),
            LoopKindName(kind),
            stateArity,
            optimized: false,
            fallbackReason: reason,
            temps: [],
            expressions: []);
        ctx.LoopDiagnostics?.RecordLoopPlanExecution(diagnosticKey);
    }

    private static string LoopKindName(LoopKind kind)
        => kind switch
        {
            LoopKind.While => "while",
            LoopKind.Repeat => "repeat",
            _ => kind.ToString(),
        };

    private static string LoopPlanIdentity(LoopKind kind, Algorithm step)
    {
        var stepPath = Evaluator.TryGetAlgorithmPath(step) ?? "(anonymous)";
        return $"{stepPath}.{LoopKindName(kind)}";
    }
}
