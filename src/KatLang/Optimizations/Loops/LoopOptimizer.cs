using KatLang.Evaluation;
using System.Numerics;

namespace KatLang.Optimizations.Loops;

internal static partial class LoopOptimizer
{
    internal static bool TryEvaluateWhile(
        Algorithm step,
        IReadOnlyList<Result> stateValues,
        Evaluator.EvalCtx ctx,
        ValEnv valEnv,
        Func<IReadOnlyList<ParameterPattern>, IReadOnlyList<Result>, EvalResult<Evaluator.CountedResult>> genericContinuation,
        out EvalResult<Evaluator.CountedResult> result)
        => TryEvaluateWhile(step, stateValues.Select(value => NeedCell.Ready(new(value, value.ValueCount()))).ToArray(), ctx, valEnv, genericContinuation, out result);

    /// <summary>
    /// The planned <c>while</c>. A handover continues generically through
    /// <paramref name="genericContinuation"/>, which receives the step's ADMITTED head
    /// (<see cref="LoopPlanTemplate.AdmittedHead"/>) with the next state, so it binds the head these
    /// planned iterations bound, never a fresh read of the step's live head.
    /// </summary>
    internal static bool TryEvaluateWhile(
        Algorithm step,
        IReadOnlyList<NeedCell> stateValues,
        Evaluator.EvalCtx ctx,
        ValEnv valEnv,
        Func<IReadOnlyList<ParameterPattern>, IReadOnlyList<Result>, EvalResult<Evaluator.CountedResult>> genericContinuation,
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
            // ONE step per iteration, charged first — exactly where the generic loop charges
            // its iteration step (Evaluator.EvalNeedLoop / RunReadyNeedStepSlots), before
            // anything of the iteration is evaluated. It is what bounds a runaway planned loop
            // under a finite MaxSteps, and (with the planned expressions' checkpoints) what
            // makes a planned run's step count identical to the generic one (Q-09b). It also
            // observes host cancellation once per iteration, before any counter moves.
            if (ctx.Budget.TryChargeStep() is { } iterationLimit)
            {
                result = iterationLimit;
                return true;
            }

            ctx.LoopDiagnostics?.RecordLoopIteration();
            frame.BeginIteration();

            // The continuation row FIRST (LOOP-06, condition first): the planner admits only a
            // NON-spread continuation row (TryBuildLoopPlanTemplate), which always supplies at
            // least one item, so it is the whole of flag discovery. A false verdict returns the
            // round's state without forming any next-state row.
            var continuationR = EvalTopLevelLoopExprPlan(plan.ContinuationOutput!, frame);
            if (continuationR.IsError)
            {
                result = continuationR.Error;
                return true;
            }

            var continuation = continuationR.Value;
            frame.SetIterationOutput(plan.NextStateOutputs.Count, continuation);
            // One emitted value is the flag itself, read without allocation. A zero-emission row
            // is its one `()` slot; a multi-emission row supplies its items, the last being the
            // flag — read exactly as the generic row rule reads them. No public tree reaches that
            // arm (a non-spread row is a value boundary and a spread continuation row is never
            // planned); it keeps the planned round total over the row rule.
            var cont = continuation.EmittedCount == 1 ? continuation.AsBool() : null;
            if (cont is null)
            {
                var flagRow = plan.ContinuationOutput!.Source;
                var flagR = Evaluator.ContinuationFlagOfRow(flagRow, continuation.EmittedCount <= 1
                    ? continuation.ToResult()
                    : FlagRowLastItem(flagRow, continuation));
                if (flagR.IsError)
                {
                    result = flagR.Error;
                    return true;
                }

                cont = flagR.Value;
            }

            if (!cont.Value)
            {
                result = frame.CurrentStateResult();
                return true;
            }

            // A continuation row supplying other than one item changes the next state's slots
            // (its items before the flag join it); generic semantics continue from the
            // already-evaluated outputs.
            var requiresGenericContinuation = continuation.EmittedCount > 1;
            if (requiresGenericContinuation)
                ctx.LoopDiagnostics?.RecordOptimizedLoopFallback("loop continuation did not emit exactly one value");

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
                    // One iteration hands over once, even when several rows cannot fit the
                    // frame. Retain every cause without counting that handover again.
                    if (ctx.LoopDiagnostics is { } diagnostics)
                    {
                        if (requiresGenericContinuation)
                            diagnostics.RecordFallbackReason("loop expression did not emit exactly one state value");
                        else
                            diagnostics.RecordOptimizedLoopFallback("loop expression did not emit exactly one state value");
                    }
                    requiresGenericContinuation = true;
                }
                else if (!requiresGenericContinuation)
                {
                    frame.SetScratchSlot(i, outputR.Value.ToResult());
                }
            }

            if (requiresGenericContinuation)
            {
                // The verdict is already true: the round's complete supply in written order (the
                // flag row's items last) splits into the next state, never re-evaluating a row.
                var splitR = Evaluator.SplitContSlots(MaterializeGenericHandoverSlots(frame, includeContinuation: true));
                if (splitR.IsError)
                {
                    result = splitR.Error;
                    return true;
                }

                result = genericContinuation(plan.AdmittedHead, splitR.Value.NextStateSlots);
                return true;
            }

            if (!frame.TryCommitScratchFast())
            {
                ctx.LoopDiagnostics?.RecordOptimizedLoopFallback("loop next-state arity changed");
                // Every output emitted exactly one value on this branch, so the
                // state-only materialization equals the historical full list minus its
                // final continuation slot.
                result = genericContinuation(plan.AdmittedHead, MaterializeGenericHandoverSlots(frame, includeContinuation: false));
                return true;
            }
        }
    }

    /// <summary>
    /// The last item a multi-emission continuation row supplies (the generic row rule,
    /// <see cref="AppendGenericLoopOutputSlots"/>): the flag of a round whose continuation row
    /// supplied several items. Evaluates nothing.
    /// </summary>
    private static Result FlagRowLastItem(Expr source, PlannedLoopValue output)
    {
        var items = new List<Result>();
        AppendGenericLoopOutputSlots(items, source, output);
        return items[^1];
    }

    internal static bool TryEvaluateRepeat(
        Algorithm step,
        long count,
        IReadOnlyList<Result> stateValues,
        Evaluator.EvalCtx ctx,
        ValEnv valEnv,
        Func<IReadOnlyList<ParameterPattern>, long, IReadOnlyList<Result>, EvalResult<Evaluator.CountedResult>> genericContinuation,
        out EvalResult<Evaluator.CountedResult> result)
        => TryEvaluateRepeat(step, count, stateValues.Select(value => NeedCell.Ready(new(value, value.ValueCount()))).ToArray(), ctx, valEnv, genericContinuation, out result);

    /// <summary>
    /// The planned <c>repeat</c>. A handover continues generically through
    /// <paramref name="genericContinuation"/>, which receives the step's ADMITTED head
    /// (<see cref="LoopPlanTemplate.AdmittedHead"/>) with the remaining count and the next state,
    /// so it binds the head these planned iterations bound, never a fresh read of the step's live
    /// head.
    /// </summary>
    internal static bool TryEvaluateRepeat(
        Algorithm step,
        long count,
        IReadOnlyList<NeedCell> stateValues,
        Evaluator.EvalCtx ctx,
        ValEnv valEnv,
        Func<IReadOnlyList<ParameterPattern>, long, IReadOnlyList<Result>, EvalResult<Evaluator.CountedResult>> genericContinuation,
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
            // Same rule as the optimized while path: one step per iteration, charged where
            // the generic repeat charges it, observing host cancellation first.
            if (ctx.Budget.TryChargeStep() is { } iterationLimit)
            {
                result = iterationLimit;
                return true;
            }

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
                    // As in while, count this handover once and retain every row's reason.
                    if (ctx.LoopDiagnostics is { } diagnostics)
                    {
                        if (requiresGenericContinuation)
                            diagnostics.RecordFallbackReason("loop expression did not emit exactly one state value");
                        else
                            diagnostics.RecordOptimizedLoopFallback("loop expression did not emit exactly one state value");
                    }
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
                    : genericContinuation(plan.AdmittedHead, remainingCount, outputSlots);
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
                    : genericContinuation(plan.AdmittedHead, remainingCount, outputSlots);
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
        ValEnv parentValEnv)
    {
        ctx.LoopDiagnostics?.RecordLoopPlanBuild();

        if (stateArity <= 0 || step is not Algorithm.User userStep)
        {
            RecordLoopPlanFallbackDiagnostic(kind, step, stateArity, ctx, "loop plan unsupported step shape");
            return null;
        }

        // The step's ADMITTED head (LoopPlanTemplate.AdmittedHead): ONE snapshot of its caller-owned
        // top-level patterns, read here and nowhere else in the planned run. The planned frame binds
        // one plain fixed capture per state slot by position. The shape gate admitted the head as
        // exactly that (Evaluator.IsOptimizedLoopShapeEligible); a snapshot that is not exactly that is
        // refused here too, so the planner never binds a head it cannot represent.
        var admittedHead = userStep.ParameterPatterns.ToArray();
        if (userStep.FindDuplicatePropName() is not null || AdmittedStateNames(admittedHead, stateArity) is not { } stateNames)
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

        // A `while` round discovers its flag from the LAST row backwards (LOOP-06). A spread
        // continuation row may supply no item, and discovery would then need earlier rows, so
        // such a step runs through the generic condition-first reader (fail closed).
        if (kind == LoopKind.While && userStep.Output[stateArity] is Expr.SequenceSpread)
        {
            RecordLoopPlanFallbackDiagnostic(kind, step, stateArity, ctx, "loop plan spread continuation row");
            return null;
        }

        // One immutable state-name list (the admitted head's) and bundle-facts memo for this
        // construction. Output rows keep separate expression memos (including stack-sensitive
        // fallbacks).
        var loopCtx = ShadowLoopStepParameterEnvironments(ctx, stateNames);
        var iterationCtx = loopCtx.Push(userStep);
        var argumentMemo = new LoopTempCallArgumentMemo();
        var tempPlanBuild = BuildLoopTempPlans(
            userStep,
            stateNames,
            iterationCtx,
            parentValEnv,
            includeDiagnostics: ctx.LoopDiagnostics is not null,
            argumentMemo);
        var tempPlans = tempPlanBuild.Plans;

        var nextStateOutputs = new List<LoopExprPlan>(stateArity);
        var requiresPerIterationCacheIdentity = false;
        for (var i = 0; i < stateArity; i++)
        {
            var plan = BuildLoopExprPlan(userStep.Output[i], stateNames, iterationCtx, parentValEnv, tempPlans, argumentMemo);
            if (!plan.IsFullyPlanned)
                requiresPerIterationCacheIdentity = true;
            nextStateOutputs.Add(plan.Plan);
        }

        LoopExprPlan? continuationOutput = null;
        if (kind == LoopKind.While)
        {
            var plan = BuildLoopExprPlan(userStep.Output[stateArity], stateNames, iterationCtx, parentValEnv, tempPlans, argumentMemo);
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
                    userStep.Output[index], stateNames, iterationCtx, parentValEnv, tempPlans, argumentMemo).Plan);
            }

            if (kind == LoopKind.While)
            {
                continuationOutput = BuildLoopExprPlan(
                    userStep.Output[stateArity], stateNames, iterationCtx, parentValEnv, tempPlans, argumentMemo).Plan;
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
            admittedHead,
            stateNames,
            stateArity,
            tempPlans,
            nextStateOutputs,
            continuationOutput,
            requiresPerIterationCacheIdentity,
            loopCtx,
            diagnosticKey);
    }

    /// <summary>
    /// The state names of an admitted head, in slot order: one plain fixed capture per state slot,
    /// with distinct names. Null for any other head. A small head is scanned for a repeated name and
    /// a large one hashed, so the check stays linear.
    /// </summary>
    private static string[]? AdmittedStateNames(ParameterPattern[] head, int stateArity)
    {
        if (head.Length != stateArity)
            return null;

        const int ScannedHeadLength = 8;
        var names = new string[head.Length];
        var seen = head.Length > ScannedHeadLength ? new HashSet<string>(StringComparer.Ordinal) : null;
        for (var index = 0; index < head.Length; index++)
        {
            if (head[index] is not CaptureParameterPattern { Kind: ParameterKind.Normal } capture)
                return null;

            var name = capture.Name;
            if (seen is null ? Array.IndexOf(names, name, 0, index) >= 0 : !seen.Add(name))
                return null;
            names[index] = name;
        }

        return names;
    }

    /// <summary>
    /// The planned loop's step context shadows the step's parameter names out of
    /// BOTH inherited tiers through the evaluator's shared callee-context helper —
    /// the same construction the generic step binding performs — so a partially
    /// planned row that falls back to generic evaluation inside the planned loop
    /// resolves a call on a state parameter exactly as the generic strategy does.
    /// </summary>
    private static Evaluator.EvalCtx ShadowLoopStepParameterEnvironments(
        Evaluator.EvalCtx ctx,
        IReadOnlyList<string> stateNames)
        => Evaluator.ShadowInheritedParameterEnvironments(ctx, stateNames);

    /// <summary>
    /// Records a planner refusal: the ONE <see cref="LoopOptimizationDiagnostics.OptimizedLoopFallbacks"/>
    /// count of the refused loop entry, under the planner's specific reason, plus its plan
    /// diagnostic. Every <c>null</c> return of <see cref="TryBuildLoopPlanTemplate"/> records here, so
    /// a <c>false</c> from <c>TryEvaluateWhile</c> or <c>TryEvaluateRepeat</c> is an
    /// already-recorded fallback, which the loop entry does not record again (OPT-FB-1).
    /// </summary>
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
