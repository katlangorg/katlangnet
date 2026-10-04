namespace KatLang.Optimizations.Loops;

/// <summary>
/// One planned local property of a loop step. <paramref name="DeclarationSpan"/> is the
/// property's first declared-name span — the span the generic zero-argument property
/// access stamps on a rejected depth enter — retained so a planned bare read
/// (<see cref="LoopExprPlan.TempSlot"/>) reports the same limit-error span.
/// <see cref="Binding"/> is the declared
/// <see cref="Property"/> itself: a bare read of an EXPORTED temp goes through the
/// run's zero-argument property cache under that binding (the same entry the
/// generic evaluator uses), while a local-only temp is memoized per iteration.
/// <see cref="ForwardsTransportedArguments"/> records whether a forwarding call of this temp
/// can be planned at all (see <see cref="LoopOptimizer.TransportsForwardedArguments"/>).
/// </summary>
internal sealed record LoopTempPlan(
    string Name,
    int Index,
    IReadOnlyList<string> ParameterNames,
    LoopExprPlan Plan,
    SourceSpan? DeclarationSpan,
    Property Binding,
    bool ForwardsTransportedArguments);

internal sealed record LoopTempPlanBuild(
    IReadOnlyList<LoopTempPlan> Plans,
    IReadOnlyList<LoopTempDiagnosticSnapshot> Diagnostics);

internal static partial class LoopOptimizer
{
    private static LoopTempPlanBuild BuildLoopTempPlans(
        Algorithm.User userStep,
        IReadOnlyList<string> stateNames,
        Evaluator.EvalCtx ctx,
        ValEnv parentValEnv,
        bool includeDiagnostics,
        LoopTempCallArgumentMemo argumentMemo)
    {
        var plans = new List<LoopTempPlan>(userStep.Properties.Count);
        List<LoopTempDiagnosticSnapshot>? diagnostics = includeDiagnostics
            ? new List<LoopTempDiagnosticSnapshot>(userStep.Properties.Count)
            : null;

        foreach (var property in userStep.Properties)
        {
            var tempIndex = plans.Count;
            var tempR = TryBuildLoopTempPlan(property, plans, stateNames, ctx, parentValEnv, argumentMemo);
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
                    property.FirstDeclarationSpan,
                    property,
                    TransportsForwardedArguments(property, stateNames, ctx));
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
        ValEnv parentValEnv,
        LoopTempCallArgumentMemo argumentMemo)
    {
        if (property.Value is not Algorithm.User userProperty)
            return new LoopTempPlanTryBuildResult(null, $"unsupported local property kind: {property.Name}");

        if (userProperty.HasExplicitParameterList)
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

        var bodyPlan = TryBuildLoopExprPlan(userProperty.Output[0], stateNames, ctx, parentValEnv, earlierTempPlans, argumentMemo);
        if (bodyPlan.Plan is null)
            return new LoopTempPlanTryBuildResult(null, $"unsupported local property body {property.Name}: {bodyPlan.FallbackReason}");

        return new LoopTempPlanTryBuildResult(bodyPlan.Plan, null);
    }

    /// <summary>
    /// Whether the forwarding call <c>T(p1, …, pn)</c> of a planned temp — its arguments are
    /// exactly its own parameter names — can be planned: a planned call evaluates the temp's
    /// body straight against the step's own bindings, which is the generic call EXACTLY only
    /// when that call would TRANSPORT every argument's existing binding into the callee
    /// (<c>Evaluator.SupplyCell</c> reuses a parameter's own cell): each parameter is a plain,
    /// non-collecting capture with a distinct name, and each name is a step state parameter or
    /// a parameter whose need cell the step context already holds. A repeated name would make
    /// the generic binder demand both arguments at binding time, and an argument the step
    /// holds only as a value would be a NEW cell whose first demand records its own dispatch
    /// checkpoint — either would put budget charges or VALUE demand somewhere the planned call
    /// does not, so such a call stays generic. (The front end never produces either: a temp
    /// only acquires a parameter for a name no enclosing binding supplies, which the step then
    /// forwards as one of its own state parameters.)
    /// </summary>
    internal static bool TransportsForwardedArguments(
        Property property,
        IReadOnlyList<string> stateNames,
        Evaluator.EvalCtx ctx)
    {
        if (property.Value is not Algorithm.User userProperty)
            return false;

        var patterns = userProperty.ParameterPatterns;
        for (var i = 0; i < patterns.Count; i++)
        {
            if (patterns[i] is not CaptureParameterPattern { Kind: ParameterKind.Normal } capture)
                return false;

            for (var j = 0; j < i; j++)
            {
                if (patterns[j] is CaptureParameterPattern earlier && earlier.Name == capture.Name)
                    return false;
            }

            if (!ContainsStateName(stateNames, capture.Name) && Evaluator.ParameterNeedCell(capture.Name, ctx) is null)
                return false;
        }

        return true;
    }

    private static bool ContainsStateName(IReadOnlyList<string> stateNames, string name)
    {
        for (var i = 0; i < stateNames.Count; i++)
        {
            if (stateNames[i] == name)
                return true;
        }

        return false;
    }

    private static bool IsLoopPlanVisibleParameter(
        string name,
        IReadOnlyList<string> stateNames,
        ValEnv parentValEnv,
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

        if (Evaluator.ParameterNeedCell(name, ctx) is not null)
        {
            fallbackReason = null;
            return true;
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
