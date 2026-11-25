namespace KatLang.Optimizations.Loops;

/// <summary>
/// One planned local property of a loop step. <paramref name="DeclarationSpan"/> is the
/// property's first declared-name span — the span the generic zero-argument property
/// access stamps on a rejected depth enter — retained so a planned bare read
/// (<see cref="LoopExprPlan.TempSlot"/>) reports the same limit-error span.
/// <see cref="Binding"/> is the declared
/// <see cref="Property"/> itself. Every temp is memoized per iteration: a round is an actual
/// call of the step, which owns its inner bindings whatever their exposure (INNER-PROPERTY
/// LIFETIME, November 2026); the binding's exposure still decides whether the temp may be
/// planned at all (an exported temp that reads an input is left to the generic refusal).
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
            // OD-E (M4★): an alias temp — a reference `T = U` or a carrier `T = { U }` of an earlier
            // planned temp — owns no slot and no cache entry: every read and call of it is its target's,
            // so it is planned as its target's own plan (the same slot, binding and declaration span),
            // exactly as the generic evaluator reads its VALUE terminal and invokes its target. Only an
            // alias that declares and opens nothing of its own: its target name then resolves exactly as
            // at the step level, while a carrier's own declarations or opens decide its name first
            // (`T = { U = 99 ⏎ U }` is its own U) — such a temp keeps the generic path.
            if (property.Value is Algorithm.Alias { Target: Expr.Resolve(var targetName), Properties.Count: 0, Opens.Count: 0 }
                && TryFindLoopTempPlan(plans, targetName, out var targetPlan))
            {
                plans.Add(targetPlan with { Name = property.Name });
                diagnostics?.Add(new LoopTempDiagnosticSnapshot(
                    property.Name,
                    Planned: true,
                    PlanSummary: $"Alias({targetPlan.Name})",
                    FallbackReason: null));
                continue;
            }

            var tempIndex = plans.Count;
            var tempR = TryBuildLoopTempPlan(property, plans, stateNames, ctx, parentValEnv, argumentMemo);
            // EXPORTED MEANS DETACHED: a planned temp is evaluated straight from the frame's slots,
            // so an exported one whose plan reads the loop's state or an enclosing input is not
            // planned. The generic route then evaluates it detached and refuses that read.
            if (tempR.Plan is not null)
            {
                var readsInput = ExportedTempReadsLoopOrEnclosingInput(property, tempR.Plan, plans, out var visited);
                ctx.LoopDiagnostics?.RecordExportedTempDependencyVisits(visited);
                if (readsInput)
                    tempR = new LoopTempPlanTryBuildResult(null, ExportedTempInputFallbackReason);
            }
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

    /// <summary>The fallback reason of an exported temp whose plan reads an input (see <see cref="ExportedTempReadsLoopOrEnclosingInput"/>).</summary>
    internal const string ExportedTempInputFallbackReason = "exported temp reads loop or enclosing input";

    /// <summary>
    /// Whether the plan of a ZERO-parameter <see cref="PropertyExposure.Exported"/> temp reads an input of
    /// the loop or of an enclosing call (EXPORTED-DETACHED, November 2026): a state slot, a captured
    /// slot, an enclosing parameter's cell, or — transitively — a temp that is not itself such an
    /// exported temp (a local-only temp, or a forwarding call, whose arguments are state names). The
    /// planned strategy would evaluate that plan from the frame and read the input, where the
    /// generic strategy evaluates the property DETACHED and refuses the read; so the temp is left
    /// to the generic strategy, and the two agree. A correctly
    /// exported temp reads none of these (it is self-contained by classification), so this never
    /// changes how a correctly classified step is planned. A temp with parameters is no
    /// zero-argument entry and is not judged here. Iterative: a plan is as deep as its expression.
    /// <para>EACH DISTINCT NODE IS EXPANDED ONCE. The planner shares one plan node between every
    /// occurrence of one expression OBJECT (<c>TryBuildLoopExprPlan</c> memoizes by reference, and a
    /// host tree may share acyclic subtrees), so a plan is a DAG whose paths can outnumber its nodes
    /// exponentially. The walk therefore remembers the nodes it has expanded by REFERENCE identity
    /// (a plan node is a record: its value equality would compare whole subtrees) and never expands
    /// one twice: its work is bounded by the distinct nodes plus the edges leaving them, whether or
    /// not the temp is ever read. The verdict is the one an unshared walk gives — a node's
    /// dependencies do not depend on the path that reached it. <paramref name="visited"/> is the
    /// number of distinct nodes expanded (zero for a temp that is not judged), reported for tests
    /// and diagnostics (<see cref="LoopOptimizationDiagnostics.ExportedTempDependencyVisits"/>).</para>
    /// </summary>
    internal static bool ExportedTempReadsLoopOrEnclosingInput(
        Property property,
        LoopExprPlan plan,
        IReadOnlyList<LoopTempPlan> earlierTempPlans,
        out int visited)
    {
        visited = 0;
        if (property.Exposure != PropertyExposure.Exported
            || property.Value is not Algorithm.User { Params.Count: 0 })
            return false;

        var expanded = new HashSet<LoopExprPlan>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<LoopExprPlan>();
        pending.Push(plan);
        while (pending.TryPop(out var node))
        {
            // A shared node reached again by another path: already expanded, nothing new below it.
            if (!expanded.Add(node))
                continue;
            visited++;

            switch (node)
            {
                case LoopExprPlan.Constant or LoopExprPlan.StringConstant:
                    break;

                case LoopExprPlan.StateSlot or LoopExprPlan.CapturedSlot or LoopExprPlan.NeedParameter
                    or LoopExprPlan.Fallback:
                    return true;

                case LoopExprPlan.TempSlot(_, var index, _):
                    if (!IsSelfContainedExportedTemp(earlierTempPlans[index]))
                        return true;
                    break;

                case LoopExprPlan.TempCall(_, _, _, var index, _):
                    if (!IsSelfContainedExportedTemp(earlierTempPlans[index]))
                        return true;
                    break;

                case LoopExprPlan.Unary(_, _, var operand):
                    pending.Push(operand);
                    break;

                case LoopExprPlan.Binary(_, _, var left, var right):
                    pending.Push(left);
                    pending.Push(right);
                    break;

                case LoopExprPlan.Comparison(_, var first, var links):
                    pending.Push(first);
                    foreach (var link in links)
                        pending.Push(link.Operand);
                    break;

                case LoopExprPlan.If(_, _, var condition, var trueBranch, var falseBranch):
                    pending.Push(condition);
                    pending.Push(trueBranch);
                    pending.Push(falseBranch);
                    break;
            }
        }

        return false;
    }

    // A planned temp that passed the check above: exported, parameterless, and therefore input-free.
    private static bool IsSelfContainedExportedTemp(LoopTempPlan temp)
        => temp.Binding.Exposure == PropertyExposure.Exported && temp.ParameterNames.Count == 0;

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
