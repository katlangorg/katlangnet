namespace KatLang.Optimizations.Loops;

/// <summary>
/// One planned local property of a loop step. <paramref name="DeclarationSpan"/> is the
/// property's first declared-name span — the span the generic zero-argument property
/// access stamps on a rejected depth enter — retained so a planned bare read
/// (<see cref="LoopExprPlan.TempSlot"/>) reports the same limit-error span.
/// </summary>
internal sealed record LoopTempPlan(
    string Name,
    int Index,
    IReadOnlyList<string> ParameterNames,
    LoopExprPlan Plan,
    SourceSpan? DeclarationSpan);

internal sealed record LoopTempPlanBuild(
    IReadOnlyList<LoopTempPlan> Plans,
    IReadOnlyList<LoopTempDiagnosticSnapshot> Diagnostics);

internal static partial class LoopOptimizer
{
    private static LoopTempPlanBuild BuildLoopTempPlans(
        Algorithm.User userStep,
        IReadOnlyList<string> stateNames,
        Evaluator.EvalCtx ctx,
        IReadOnlyList<(string Name, Result Value)> parentValEnv,
        bool includeDiagnostics)
    {
        var plans = new List<LoopTempPlan>(userStep.Properties.Count);
        List<LoopTempDiagnosticSnapshot>? diagnostics = includeDiagnostics
            ? new List<LoopTempDiagnosticSnapshot>(userStep.Properties.Count)
            : null;

        foreach (var property in userStep.Properties)
        {
            var tempIndex = plans.Count;
            var tempR = TryBuildLoopTempPlan(property, plans, stateNames, ctx, parentValEnv);
            if (tempR.Plan is not null)
            {
                var parameterNames = property.Value is Algorithm.User userProperty
                    ? userProperty.Params
                    : [];
                var plan = new LoopTempPlan(
                    property.Name,
                    tempIndex,
                    parameterNames,
                    tempR.Plan,
                    property.DeclarationSpans.FirstOrDefault());
                plans.Add(plan);
                diagnostics?.Add(new LoopTempDiagnosticSnapshot(
                    property.Name,
                    Planned: true,
                    PlanSummary: DescribeLoopExprPlan(plan.Plan),
                    FallbackReason: null));
                continue;
            }

            var reason = tempR.FallbackReason ?? $"unsupported local property: {property.Name}";
            ctx.LoopDiagnostics?.RecordFallbackReason(reason);
            diagnostics?.Add(new LoopTempDiagnosticSnapshot(
                property.Name,
                Planned: false,
                PlanSummary: null,
                FallbackReason: reason));
        }

        return new LoopTempPlanBuild(plans, diagnostics ?? []);
    }

    private readonly record struct LoopTempPlanTryBuildResult(LoopExprPlan? Plan, string? FallbackReason);

    private static LoopTempPlanTryBuildResult TryBuildLoopTempPlan(
        Property property,
        IReadOnlyList<LoopTempPlan> earlierTempPlans,
        IReadOnlyList<string> stateNames,
        Evaluator.EvalCtx ctx,
        IReadOnlyList<(string Name, Result Value)> parentValEnv)
    {
        if (property.Value is not Algorithm.User userProperty)
            return new LoopTempPlanTryBuildResult(null, $"unsupported local property kind: {property.Name}");

        if (userProperty.ExplicitParameters.Count != 0)
            return new LoopTempPlanTryBuildResult(null, $"unsupported local property with explicit parameters: {property.Name}");

        foreach (var parameterName in userProperty.Params)
        {
            if (!IsLoopPlanVisibleParameter(parameterName, stateNames, parentValEnv, ctx, out var fallbackReason))
            {
                return new LoopTempPlanTryBuildResult(
                    null,
                    fallbackReason ?? $"unsupported local property implicit parameter: {property.Name}.{parameterName}");
            }
        }

        if (userProperty.Opens.Count != 0 || userProperty.Properties.Count != 0)
            return new LoopTempPlanTryBuildResult(null, $"unsupported local property shape: {property.Name}");

        if (userProperty.Output.Count != 1)
            return new LoopTempPlanTryBuildResult(null, $"unsupported local property output arity: {property.Name}");

        var bodyPlan = TryBuildLoopExprPlan(userProperty.Output[0], stateNames, ctx, parentValEnv, earlierTempPlans);
        if (bodyPlan.Plan is null)
            return new LoopTempPlanTryBuildResult(null, $"unsupported local property body {property.Name}: {bodyPlan.FallbackReason}");

        return new LoopTempPlanTryBuildResult(bodyPlan.Plan, null);
    }

    private static bool IsLoopPlanVisibleParameter(
        string name,
        IReadOnlyList<string> stateNames,
        IReadOnlyList<(string Name, Result Value)> parentValEnv,
        Evaluator.EvalCtx ctx,
        out string? fallbackReason)
    {
        for (var i = 0; i < stateNames.Count; i++)
        {
            if (stateNames[i] == name)
            {
                fallbackReason = null;
                return true;
            }
        }

        if (TryFindCountedParam(ctx, name, out _, out var countedParam))
        {
            if (IsSafeCountedParamSlot(countedParam, out var countedParamFallbackReason))
            {
                fallbackReason = null;
                return true;
            }

            fallbackReason = $"unsupported counted parameter value shape: {name} ({countedParamFallbackReason})";
            ctx.LoopDiagnostics?.RecordCountedParameterReferenceFallback(fallbackReason);
            return false;
        }

        for (var i = 0; i < parentValEnv.Count; i++)
        {
            if (parentValEnv[i].Name == name)
            {
                fallbackReason = null;
                return true;
            }
        }

        fallbackReason = null;
        return false;
    }
}
