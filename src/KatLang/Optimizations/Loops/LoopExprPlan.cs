using System.Numerics;

namespace KatLang.Optimizations.Loops;

internal abstract record LoopExprPlan(Expr Source)
{
    public sealed record Constant(Expr Source, PlannedLoopValue Value) : LoopExprPlan(Source);

    public sealed record StringConstant(Expr Source, string Value) : LoopExprPlan(Source);

    public sealed record StateSlot(Expr Source, int Index, string Name) : LoopExprPlan(Source);

    public sealed record CapturedSlot(Expr Source, int Index, string Name) : LoopExprPlan(Source);

    public sealed record CountedParamSlot(Expr Source, int Index, string Name) : LoopExprPlan(Source);

    /// <summary>
    /// A bare value-position read of a ZERO-parameter local property of the loop step
    /// (<c>T</c>). Mirrors the generic zero-argument property access: charged as one
    /// dynamic invocation on EVERY read and memoized per iteration exactly like the run's
    /// zero-argument property cache, whose entries are keyed by the iteration's
    /// environment identities. Passed DIRECTLY as a planned <c>if</c> argument it is
    /// instead the property's own algorithm on the argument's algorithm channel — see
    /// <c>LoopOptimizer.EvalLoopIfArgument</c>.
    /// </summary>
    public sealed record TempSlot(Expr Source, int Index, string Name) : LoopExprPlan(Source);

    /// <summary>
    /// A CALL of a local property of the loop step: the explicit <c>T()</c>, or the
    /// forwarding call <c>A(x)</c> the front end synthesizes for a reference to a
    /// parameterized local property (its arguments are exactly the property's own
    /// parameters, so the planned body reads the same slots). Mirrors the generic user
    /// call — <c>A</c> versus <c>A()</c> is core KatLang semantics, a call bypasses the
    /// property cache — so the body is evaluated FRESH on every call under the user-call
    /// chokepoint, with the caller's temp memo suspended for the call's duration
    /// (<see cref="LoopRunFrame.SuspendTempMemo"/>), inside the generic call-expression
    /// diagnostic boundary. <paramref name="Callee"/> is the ORIGINAL callee expression
    /// and <paramref name="LimitSpan"/> the span a rejected enter is stamped with
    /// (<see cref="Evaluator.UserCallLimitSpan"/>), both retained so attribution cannot
    /// drift from the generic evaluator's.
    /// </summary>
    public sealed record TempCall(Expr Source, Expr Callee, SourceSpan? LimitSpan, int Index, string Name) : LoopExprPlan(Source);

    public sealed record Unary(Expr Source, UnaryOp Op, LoopExprPlan Operand) : LoopExprPlan(Source);

    public sealed record Binary(Expr Source, BinaryOp Op, LoopExprPlan Left, LoopExprPlan Right) : LoopExprPlan(Source);

    /// <summary>
    /// A planned <c>if</c> call. <paramref name="Callee"/> is the ORIGINAL callee
    /// expression of <paramref name="Source"/>, retained so the planned evaluation can
    /// reproduce the generic call boundary's diagnostic context and span attribution
    /// (<see cref="Evaluator.WithPlannedCallBoundary{T}"/>) instead of reconstructing
    /// them.
    /// </summary>
    public sealed record If(Expr Source, Expr Callee, LoopExprPlan Condition, LoopExprPlan TrueBranch, LoopExprPlan FalseBranch) : LoopExprPlan(Source);

    public sealed record Fallback(Expr Source, string Reason) : LoopExprPlan(Source);
}

internal static partial class LoopOptimizer
{
    private readonly record struct LoopExprPlanBuild(LoopExprPlan Plan, bool IsFullyPlanned);

    private readonly record struct LoopExprPlanTryBuildResult(LoopExprPlan? Plan, string? FallbackReason);

    private static LoopExprPlanBuild BuildLoopExprPlan(
        Expr expr,
        IReadOnlyList<string> stateNames,
        Evaluator.EvalCtx ctx,
        IReadOnlyList<(string Name, Result Value)> parentValEnv,
        IReadOnlyList<LoopTempPlan> tempPlans)
    {
        var result = TryBuildLoopExprPlan(expr, stateNames, ctx, parentValEnv, tempPlans);
        if (result.Plan is not null)
            return new LoopExprPlanBuild(result.Plan, true);

        var reason = result.FallbackReason ?? $"unsupported expression: {Evaluator.ExprKind(expr)}";
        ctx.LoopDiagnostics?.RecordFallbackReason(reason);
        return new LoopExprPlanBuild(new LoopExprPlan.Fallback(expr, reason), false);
    }

    private static LoopExprPlanTryBuildResult TryBuildLoopExprPlan(
        Expr expr,
        IReadOnlyList<string> stateNames,
        Evaluator.EvalCtx ctx,
        IReadOnlyList<(string Name, Result Value)> parentValEnv,
        IReadOnlyList<LoopTempPlan> tempPlans,
        Dictionary<Expr, LoopExprPlanTryBuildResult>? memo = null)
    {
        memo ??= new(ReferenceEqualityComparer.Instance);
        if (memo.TryGetValue(expr, out var existing))
            return existing;

        var result = TryBuildLoopExprPlanCore(expr, stateNames, ctx, parentValEnv, tempPlans, memo);
        memo.Add(expr, result);
        return result;
    }

    private static LoopExprPlanTryBuildResult TryBuildLoopExprPlanCore(
        Expr expr,
        IReadOnlyList<string> stateNames,
        Evaluator.EvalCtx ctx,
        IReadOnlyList<(string Name, Result Value)> parentValEnv,
        IReadOnlyList<LoopTempPlan> tempPlans,
        Dictionary<Expr, LoopExprPlanTryBuildResult> memo)
    {
        switch (expr)
        {
            case Expr.Num(var value):
                return new LoopExprPlanTryBuildResult(
                    new LoopExprPlan.Constant(expr, PlannedLoopValue.FromResult(new Result.Atom(value))),
                    null);

            case Expr.StringLiteral(var value):
                return new LoopExprPlanTryBuildResult(
                    new LoopExprPlan.StringConstant(expr, value),
                    null);

            case Expr.Param(var name):
            {
                for (var i = 0; i < stateNames.Count; i++)
                {
                    if (stateNames[i] == name)
                        return new LoopExprPlanTryBuildResult(new LoopExprPlan.StateSlot(expr, i, name), null);
                }

                if (TryFindCountedParam(ctx, name, out var countedParamIndex, out var countedParam))
                {
                    if (!IsSafeCountedParamSlot(countedParam, out var fallbackReason))
                    {
                        var reason = $"unsupported counted parameter value shape: {name} ({fallbackReason})";
                        ctx.LoopDiagnostics?.RecordCountedParameterReferenceFallback(reason);
                        return new LoopExprPlanTryBuildResult(null, reason);
                    }

                    ctx.LoopDiagnostics?.RecordCountedParameterReferencePlanned();
                    return new LoopExprPlanTryBuildResult(
                        new LoopExprPlan.CountedParamSlot(expr, countedParamIndex, name),
                        null);
                }

                for (var i = 0; i < parentValEnv.Count; i++)
                {
                    if (parentValEnv[i].Name == name)
                        return new LoopExprPlanTryBuildResult(new LoopExprPlan.CapturedSlot(expr, i, name), null);
                }

                return new LoopExprPlanTryBuildResult(null, $"unresolved parameter reference: {name}");
            }

            case Expr.Unary(var op, var operand):
            {
                var operandPlan = TryBuildLoopExprPlan(operand, stateNames, ctx, parentValEnv, tempPlans, memo);
                if (operandPlan.Plan is null)
                    return new LoopExprPlanTryBuildResult(null, operandPlan.FallbackReason);

                return new LoopExprPlanTryBuildResult(
                    new LoopExprPlan.Unary(expr, op, operandPlan.Plan),
                    null);
            }

            case Expr.Binary(var op, var left, var right):
            {
                var leftPlan = TryBuildLoopExprPlan(left, stateNames, ctx, parentValEnv, tempPlans, memo);
                if (leftPlan.Plan is null)
                    return new LoopExprPlanTryBuildResult(null, leftPlan.FallbackReason);

                var rightPlan = TryBuildLoopExprPlan(right, stateNames, ctx, parentValEnv, tempPlans, memo);
                if (rightPlan.Plan is null)
                    return new LoopExprPlanTryBuildResult(null, rightPlan.FallbackReason);

                return new LoopExprPlanTryBuildResult(
                    new LoopExprPlan.Binary(expr, op, leftPlan.Plan, rightPlan.Plan),
                    null);
            }

            case Expr.Resolve(var name):
                if (TryFindLoopTempPlan(tempPlans, name, out var tempPlan) && tempPlan.ParameterNames.Count == 0)
                    return new LoopExprPlanTryBuildResult(new LoopExprPlan.TempSlot(expr, tempPlan.Index, name), null);

                return new LoopExprPlanTryBuildResult(null, $"unsupported local property reference: {name}");

            case Expr.Call(var func, var callArgs):
                if (func is Expr.Resolve { Name: "if" }
                    && Evaluator.ResolvesToBuiltinAlgorithm("if", BuiltinId.@if, ctx))
                {
                    return TryBuildLoopIfExprPlan(expr, func, callArgs, stateNames, ctx, parentValEnv, tempPlans, memo);
                }

                if (func is Expr.Resolve(var tempName) && TryFindLoopTempPlan(tempPlans, tempName, out var calledTempPlan))
                {
                    if (IsLoopTempCallShape(callArgs, calledTempPlan))
                    {
                        return new LoopExprPlanTryBuildResult(
                            new LoopExprPlan.TempCall(
                                expr,
                                func,
                                Evaluator.UserCallLimitSpan(callArgs),
                                calledTempPlan.Index,
                                tempName),
                            null);
                    }

                    return new LoopExprPlanTryBuildResult(null, $"unsupported local property call shape: {tempName}");
                }

                return new LoopExprPlanTryBuildResult(null, $"unsupported call: {Evaluator.OpenExprName(func)}");

            case Expr.DotCall(var target, var name, _):
                return new LoopExprPlanTryBuildResult(null, $"unsupported dot-call: {Evaluator.OpenExprName(target)}.{name}");

            case Expr.AlgorithmExpr:
                return new LoopExprPlanTryBuildResult(null, "unsupported block expression");

            case Expr.Capture:
                return new LoopExprPlanTryBuildResult(null, "unsupported capture expression");

            case Expr.Index:
                return new LoopExprPlanTryBuildResult(null, "unsupported index expression");

            case Expr.SequenceSpread:
                return new LoopExprPlanTryBuildResult(null, "unsupported spread expression");

            case Expr.SequenceConstruct:
                return new LoopExprPlanTryBuildResult(null, "unsupported sequence construction expression");

            case Expr.Grace:
                return new LoopExprPlanTryBuildResult(null, "unsupported grace annotation");

            case Expr.NativeCall(var fnName, _):
                return new LoopExprPlanTryBuildResult(null, $"unsupported native call: {fnName}");

            default:
                return new LoopExprPlanTryBuildResult(null, $"unsupported expression kind: {Evaluator.ExprKind(expr)}");
        }
    }

    private static bool TryFindCountedParam(
        Evaluator.EvalCtx ctx,
        string name,
        out int index,
        out Evaluator.CountedResult value)
    {
        for (var i = 0; i < ctx.CountedParamEnv.Count; i++)
        {
            var (paramName, countedValue) = ctx.CountedParamEnv[i];
            if (paramName == name)
            {
                index = i;
                value = countedValue;
                return true;
            }
        }

        index = -1;
        value = default;
        return false;
    }

    private static bool IsSafeCountedParamSlot(
        Evaluator.CountedResult value,
        out string fallbackReason)
    {
        if (value.EmittedCount == 0)
        {
            fallbackReason = "counted parameter emitted no values";
            return false;
        }

        if (value.EmittedCount != 1)
        {
            fallbackReason = $"counted parameter emitted multiple values ({value.EmittedCount})";
            return false;
        }

        if (value.Value is Result.SequenceValue)
        {
            fallbackReason = $"counted parameter is a sequence value: {Evaluator.FormatResultForDiagnostic(value.Value)}";
            return false;
        }

        if (value.Value is not Result.Atom)
        {
            fallbackReason = $"counted parameter is non-numeric: {Evaluator.FormatResultForDiagnostic(value.Value)}";
            return false;
        }

        fallbackReason = "";
        return true;
    }

    private static bool TryFindLoopTempPlan(
        IReadOnlyList<LoopTempPlan> tempPlans,
        string name,
        out LoopTempPlan tempPlan)
    {
        for (var i = 0; i < tempPlans.Count; i++)
        {
            if (tempPlans[i].Name == name)
            {
                tempPlan = tempPlans[i];
                return true;
            }
        }

        tempPlan = null!;
        return false;
    }

    private static bool IsLoopTempCallShape(OutputBundle args, LoopTempPlan tempPlan)
    {
        if (args.Count != tempPlan.ParameterNames.Count)
            return false;

        for (var i = 0; i < args.Count; i++)
        {
            if (args[i] is not Expr.Param(var name) || name != tempPlan.ParameterNames[i])
                return false;
        }

        return true;
    }

    private static LoopExprPlanTryBuildResult TryBuildLoopIfExprPlan(
        Expr source,
        Expr callee,
        OutputBundle callArgs,
        IReadOnlyList<string> stateNames,
        Evaluator.EvalCtx ctx,
        IReadOnlyList<(string Name, Result Value)> parentValEnv,
        IReadOnlyList<LoopTempPlan> tempPlans,
        Dictionary<Expr, LoopExprPlanTryBuildResult> memo)
    {
        if (callArgs.Count != 3)
            return new LoopExprPlanTryBuildResult(null, $"unsupported if arity: {callArgs.Count}");

        var conditionPlan = TryBuildLoopExprPlan(callArgs[0], stateNames, ctx, parentValEnv, tempPlans, memo);
        if (conditionPlan.Plan is null)
            return new LoopExprPlanTryBuildResult(null, $"unsupported if condition: {conditionPlan.FallbackReason}");

        var truePlan = TryBuildLoopExprPlan(callArgs[1], stateNames, ctx, parentValEnv, tempPlans, memo);
        if (truePlan.Plan is null)
            return new LoopExprPlanTryBuildResult(null, $"unsupported if true branch: {truePlan.FallbackReason}");

        var falsePlan = TryBuildLoopExprPlan(callArgs[2], stateNames, ctx, parentValEnv, tempPlans, memo);
        if (falsePlan.Plan is null)
            return new LoopExprPlanTryBuildResult(null, $"unsupported if false branch: {falsePlan.FallbackReason}");

        return new LoopExprPlanTryBuildResult(
            new LoopExprPlan.If(source, callee, conditionPlan.Plan, truePlan.Plan, falsePlan.Plan),
            null);
    }

    private static EvalResult<PlannedLoopValue> EvalTopLevelLoopExprPlan(
        LoopExprPlan plan,
        LoopRunFrame frame)
    {
        if (plan is LoopExprPlan.Fallback fallback)
        {
            frame.Diagnostics?.RecordPlannedExpressionFallback(fallback.Reason);
            frame.Diagnostics?.RecordGenericExpressionEvaluationInsideOptimizedLoop();
        }
        else
        {
            frame.Diagnostics?.RecordPlannedExpressionHit();
        }

        return EvalLoopExprPlan(plan, frame);
    }

    /// <summary>
    /// A bare zero-parameter temp read. MIRROR of the generic zero-argument property
    /// access (<c>Evaluator.GetOrEvaluateZeroArgPropertyResult</c>): the dynamic
    /// invocation is charged through the SAME helper, BEFORE the memo is consulted, so a
    /// memo hit and a miss charge the identical access (one step, one depth level, the
    /// property's declaration span on a rejected enter) and only a miss additionally
    /// charges what the temp's body evaluates. The memo is the per-iteration counterpart
    /// of the run's property cache: its entries live exactly as long as the iteration's
    /// environment identities the cache keys on.
    /// </summary>
    private static EvalResult<PlannedLoopValue> EvalLoopTempSlot(
        LoopRunFrame frame,
        int index)
    {
        if (Evaluator.TryEnterDynamicInvocation(
                frame.IterationCtx,
                frame.Template.TempPlans[index].DeclarationSpan,
                out var level) is { } limitError)
        {
            return limitError;
        }

        using (level)
        {
            return EvalMemoizedLoopTemp(frame, index);
        }
    }

    private static EvalResult<PlannedLoopValue> EvalMemoizedLoopTemp(
        LoopRunFrame frame,
        int index)
    {
        if (frame.TryGetTempSlot(index, out var value))
            return EvalResult<PlannedLoopValue>.Ok(value);

        var tempR = EvalLoopExprPlan(frame.Template.TempPlans[index].Plan, frame);
        if (tempR.IsError) return tempR.Error;
        frame.SetTempSlot(index, tempR.Value);
        return tempR;
    }

    /// <summary>
    /// A temp CALL. MIRROR of the generic user call (<c>Evaluator.EvalUserCallCounted</c>
    /// inside the call-expression boundary of <c>EvalCallCountedExpr</c>): the dynamic
    /// invocation is charged through the SAME helper with the same limit-span rule, the
    /// body is evaluated FRESH on every call (a call bypasses the property cache — the
    /// <c>A</c> versus <c>A()</c> rule), and the caller's temp memo is suspended for the
    /// call's duration because the generic callee runs in fresh environments that share
    /// no cache entries with its caller (<see cref="LoopRunFrame.SuspendTempMemo"/>).
    /// Only the RETURNED result is decorated by the boundary, exactly like the planned
    /// <c>if</c>.
    /// </summary>
    private static EvalResult<PlannedLoopValue> EvalLoopTempCall(
        LoopExprPlan.TempCall tempCall,
        LoopRunFrame frame)
        => Evaluator.WithPlannedCallBoundary(
            tempCall.Source,
            tempCall.Callee,
            frame.IterationCtx,
            EvalLoopTempCallInvocation(tempCall, frame));

    private static EvalResult<PlannedLoopValue> EvalLoopTempCallInvocation(
        LoopExprPlan.TempCall tempCall,
        LoopRunFrame frame)
    {
        if (Evaluator.TryEnterDynamicInvocation(frame.IterationCtx, tempCall.LimitSpan, out var level) is { } limitError)
            return limitError;

        using (level)
        {
            return EvalFreshLoopTemp(frame, tempCall.Index);
        }
    }

    private static EvalResult<PlannedLoopValue> EvalFreshLoopTemp(
        LoopRunFrame frame,
        int index)
    {
        var suspended = frame.SuspendTempMemo();
        try
        {
            return EvalLoopExprPlan(frame.Template.TempPlans[index].Plan, frame);
        }
        finally
        {
            frame.RestoreTempMemo(suspended);
        }
    }

    private static EvalResult<PlannedLoopValue> EvalLoopExprPlan(
        LoopExprPlan plan,
        LoopRunFrame frame)
    {
        switch (plan)
        {
            case LoopExprPlan.Constant constant:
                return EvalResult<PlannedLoopValue>.Ok(constant.Value);

            case LoopExprPlan.StringConstant constant:
            {
                var valueR = Evaluator.MakeStringResult(
                    frame.IterationCtx,
                    constant.Value,
                    constant.Source.Span);
                return valueR.IsError
                    ? valueR.Error
                    : EvalResult<PlannedLoopValue>.Ok(PlannedLoopValue.FromResult(valueR.Value));
            }

            case LoopExprPlan.StateSlot stateSlot:
                return EvalResult<PlannedLoopValue>.Ok(PlannedLoopValue.FromResult(frame.GetStateSlot(stateSlot.Index)));

            case LoopExprPlan.CapturedSlot capturedSlot:
                return EvalResult<PlannedLoopValue>.Ok(PlannedLoopValue.FromResult(frame.GetCapturedSlot(capturedSlot.Index)));

            case LoopExprPlan.CountedParamSlot countedParamSlot:
            {
                var countedParam = frame.GetCountedParamSlot(countedParamSlot.Index);
                return EvalResult<PlannedLoopValue>.Ok(
                    PlannedLoopValue.FromResult(countedParam.Value, countedParam.EmittedCount));
            }

            case LoopExprPlan.TempSlot tempSlot:
                // MIRROR of the generic value-position read (Evaluator.EvalResolveCounted):
                // the reference's own span is attached to an error that carries none.
                return Evaluator.WithSpan(tempSlot.Source.Span, EvalLoopTempSlot(frame, tempSlot.Index));

            case LoopExprPlan.TempCall tempCall:
                return EvalLoopTempCall(tempCall, frame);

            case LoopExprPlan.Unary unary:
            {
                var operandR = EvalLoopExprPlan(unary.Operand, frame);
                if (operandR.IsError) return operandR.Error;
                frame.Diagnostics?.RecordPlannedBuiltinOperation();
                return ApplyPlannedUnary(unary.Op, operandR.Value, unary.Source.Span);
            }

            case LoopExprPlan.Binary binary:
            {
                var leftR = EvalLoopExprPlan(binary.Left, frame);
                if (leftR.IsError) return leftR.Error;
                var rightR = EvalLoopExprPlan(binary.Right, frame);
                if (rightR.IsError) return rightR.Error;
                frame.Diagnostics?.RecordPlannedBuiltinOperation();
                return ApplyPlannedBinary(binary.Op, binary.Left.Source, binary.Right.Source, leftR.Value, rightR.Value, binary.Source.Span);
            }

            case LoopExprPlan.If ifPlan:
                // A planned `if` REPLACES an ordinary `if` call expression, so its
                // failures must carry the same diagnostic boundary the generic call
                // dispatch attaches (`EvalCallExpr`/`EvalCallCountedExpr` inside
                // `WithSpan`) — for a failing condition, for the selected branch, and
                // for the `if`'s own truth-value rejection alike. Only the RETURNED
                // result is decorated, so branch laziness, planned-operation counts,
                // budget charges, and cache state are untouched, and a nested planned
                // `if` nests its own frame exactly like the generic composition.
                return Evaluator.WithPlannedCallBoundary(
                    ifPlan.Source,
                    ifPlan.Callee,
                    frame.IterationCtx,
                    EvalLoopIfExprPlanBody(ifPlan, frame));

            case LoopExprPlan.Fallback fallback:
            {
                var fallbackR = Evaluator.EvalCounted(fallback.Source, frame.IterationCtx, frame.ValueEnvironment);
                if (fallbackR.IsError) return fallbackR.Error;
                return EvalResult<PlannedLoopValue>.Ok(
                    PlannedLoopValue.FromResult(fallbackR.Value.Value, fallbackR.Value.EmittedCount));
            }

            default:
                throw new InvalidOperationException($"Unhandled loop expression plan: {plan.GetType().Name}");
        }
    }

    /// <summary>
    /// The complete logical evaluation of a planned <c>if</c>, WITHOUT the call
    /// boundary. Kept separate so the boundary in <see cref="EvalLoopExprPlan"/>
    /// covers every failure of this evaluation rather than one branch.
    /// </summary>
    private static EvalResult<PlannedLoopValue> EvalLoopIfExprPlanBody(
        LoopExprPlan.If ifPlan,
        LoopRunFrame frame)
    {
        var conditionR = EvalLoopIfArgument(ifPlan.Condition, frame);
        if (conditionR.IsError) return conditionR.Error;
        frame.Diagnostics?.RecordPlannedBuiltinOperation();

        var truth = PlannedTruthValue(conditionR.Value);
        if (truth is null)
        {
            // UNSPANNED, exactly like the generic `if` builtin's truth-value
            // rejection: the surrounding call boundary stamps only the context
            // wrappers (AtSpanIfMissing), and the innermost error's span is public
            // structured state, so pre-stamping it here would be an observable
            // divergence from the generic error tree.
            return new EvalError.BadArity();
        }

        return EvalLoopIfArgument(truth.Value ? ifPlan.TrueBranch : ifPlan.FalseBranch, frame);
    }

    /// <summary>
    /// One planned <c>if</c> argument — the condition, or the selected branch. MIRROR of
    /// the generic builtin argument funnel (<c>Evaluator.EvalResolvedArgumentCounted</c>
    /// over <c>EvalArgumentAlgOutputCounted</c>): EVERY argument the generic <c>if</c>
    /// evaluates is one algorithm re-entered under one depth-only argument-evaluation
    /// level — a literal, a parameter, or an expression is wrapped in a value thunk, and
    /// a bare reference to a zero-parameter local property resolves to that property's
    /// OWN algorithm on the argument's algorithm channel. The level is charged through
    /// the SAME helper as the generic funnel, so nested planned <c>if</c>s stack levels
    /// exactly like the generic composition. The algorithm-channel case is the one place
    /// a temp is evaluated without the zero-argument property access: the generic
    /// evaluator runs the property's body directly (fresh, no cache, no invocation
    /// charge), so a <see cref="LoopExprPlan.TempSlot"/> passed DIRECTLY as an argument
    /// evaluates its body plan here rather than reading the memoized slot. An unselected
    /// branch is never evaluated and charges nothing, on either strategy.
    /// </summary>
    private static EvalResult<PlannedLoopValue> EvalLoopIfArgument(
        LoopExprPlan argument,
        LoopRunFrame frame)
    {
        if (Evaluator.TryEnterArgumentEvaluationLevel(frame.IterationCtx, out var level) is { } limitError)
            return limitError;

        using (level)
        {
            return argument is LoopExprPlan.TempSlot tempSlot
                ? EvalLoopExprPlan(frame.Template.TempPlans[tempSlot.Index].Plan, frame)
                : EvalLoopExprPlan(argument, frame);
        }
    }

    private static bool? PlannedTruthValue(PlannedLoopValue value)
        => value.HasNumericValue
            ? value.NumericValue != 0
            : value.ToResult().TruthValue();

    private static EvalResult<PlannedLoopValue> ApplyPlannedUnary(
        UnaryOp op,
        PlannedLoopValue operand,
        SourceSpan? span)
    {
        // MIRROR of Evaluator.ApplyUnaryOperator's numeric arm: a numeric operand
        // stays in the unboxed planned representation. Every other operand kind —
        // empty transparency, the span-stamped string rejection, and the UNSPANNED
        // numeric-conversion failure — delegates to the shared operator application
        // so the planned strategy cannot drift from the generic error/span policy.
        if (operand.AsNum() is { } value)
        {
            var unaryResult = op switch
            {
                UnaryOp.Minus => -value,
                UnaryOp.Not => value == 0 ? Decimal128.One : Decimal128.Zero,
                _ => Decimal128.Zero,
            };
            return EvalResult<PlannedLoopValue>.Ok(PlannedLoopValue.FromNumeric(unaryResult));
        }

        var resultR = Evaluator.ApplyUnaryOperator(op, operand.ToResult(), span);
        if (resultR.IsError) return resultR.Error;
        return EvalResult<PlannedLoopValue>.Ok(PlannedLoopValue.FromResult(resultR.Value));
    }

    private static EvalResult<PlannedLoopValue> ApplyPlannedBinary(
        BinaryOp op,
        Expr leftExpr,
        Expr rightExpr,
        PlannedLoopValue left,
        PlannedLoopValue right,
        SourceSpan? span)
    {
        // `==` and `!=` always delegate to the evaluator's structural equality so the
        // optimized loop path can never drift back to numeric-only equality. Numeric
        // atoms still compare by value through that path (ApplyBinaryOperator reduces
        // Atom == Atom to a numeric comparison), and non-numeric operands already fell
        // through here. The numeric fast path below is for arithmetic/ordering only.
        if (op is not (BinaryOp.Eq or BinaryOp.Ne)
            && left.AsNum() is { } x && right.AsNum() is { } y)
            return ApplyPlannedNumericBinary(op, x, y, span);

        var resultR = Evaluator.ApplyBinaryOperator(op, leftExpr, rightExpr, left.ToResult(), right.ToResult(), span);
        if (resultR.IsError) return resultR.Error;
        return EvalResult<PlannedLoopValue>.Ok(PlannedLoopValue.FromResult(resultR.Value));
    }

    private static EvalResult<PlannedLoopValue> ApplyPlannedNumericBinary(
        BinaryOp op,
        Decimal128 x,
        Decimal128 y,
        SourceSpan? span)
    {
        // MIRROR of Evaluator.ApplyBinaryOperator's numeric arm: divide/modulo by a
        // zero-valued divisor (the evaluated value, signed zeros included) stays the
        // specified DivByZero error; everything else follows Decimal128's IEEE
        // semantics (overflow saturates to an infinity, NaN propagates, comparisons
        // with NaN are false).
        if ((op is BinaryOp.Div or BinaryOp.IDiv or BinaryOp.Mod) && y == 0)
            return new EvalError.DivByZero() { Span = span };

        if (op == BinaryOp.Pow)
        {
            var powR = Evaluator.EvalPow(span, x, y);
            if (powR.IsError) return powR.Error;
            return EvalResult<PlannedLoopValue>.Ok(PlannedLoopValue.FromResult(powR.Value));
        }

        Decimal128 result = op switch
        {
            BinaryOp.Add => x + y,
            BinaryOp.Sub => x - y,
            BinaryOp.Mul => x * y,
            BinaryOp.Div => x / y,
            BinaryOp.IDiv => Decimal128.Truncate(x / y),
            BinaryOp.Mod => x % y,
            BinaryOp.Lt => x < y ? 1 : 0,
            BinaryOp.Gt => x > y ? 1 : 0,
            BinaryOp.Le => x <= y ? 1 : 0,
            BinaryOp.Ge => x >= y ? 1 : 0,
            // Eq/Ne are intentionally absent: equality is handled structurally by
            // ApplyBinaryOperator in ApplyPlannedBinary and never reaches this path.
            BinaryOp.And => x != 0 && y != 0 ? 1 : 0,
            BinaryOp.Or => x != 0 || y != 0 ? 1 : 0,
            BinaryOp.Xor => (x != 0) != (y != 0) ? 1 : 0,
            _ => 0,
        };

        return EvalResult<PlannedLoopValue>.Ok(PlannedLoopValue.FromNumeric(result));
    }

    private static IReadOnlyList<LoopExpressionDiagnosticSnapshot> BuildLoopExpressionDiagnostics(
        IReadOnlyList<LoopExprPlan> nextStateOutputs,
        LoopExprPlan? continuationOutput)
    {
        var diagnostics = new List<LoopExpressionDiagnosticSnapshot>(
            nextStateOutputs.Count + (continuationOutput is null ? 0 : 1));
        for (var i = 0; i < nextStateOutputs.Count; i++)
            diagnostics.Add(BuildLoopExpressionDiagnostic("output", i, nextStateOutputs[i]));

        if (continuationOutput is not null)
            diagnostics.Add(BuildLoopExpressionDiagnostic("continuation", null, continuationOutput));

        return diagnostics;
    }

    private static LoopExpressionDiagnosticSnapshot BuildLoopExpressionDiagnostic(
        string role,
        int? index,
        LoopExprPlan plan)
        => plan is LoopExprPlan.Fallback fallback
            ? new LoopExpressionDiagnosticSnapshot(role, index, false, null, fallback.Reason)
            : new LoopExpressionDiagnosticSnapshot(role, index, true, DescribeLoopExprPlan(plan), null);

    private static string DescribeLoopExprPlan(LoopExprPlan plan)
    {
        const int maxLength = 2048;
        var text = new System.Text.StringBuilder();
        var pending = new Stack<object>();
        pending.Push(plan);
        while (pending.Count != 0 && text.Length < maxLength)
        {
            var current = pending.Pop();
            switch (current)
            {
                case LoopExprPlan.Unary unary:
                    pending.Push(")");
                    pending.Push(unary.Operand);
                    pending.Push($"{LoopUnaryPlanName(unary.Op)}(");
                    continue;
                case LoopExprPlan.Binary binary:
                    pending.Push(")");
                    pending.Push(binary.Right);
                    pending.Push(", ");
                    pending.Push(binary.Left);
                    pending.Push($"{LoopBinaryPlanName(binary.Op)}(");
                    continue;
                case LoopExprPlan.If ifPlan:
                    pending.Push(")");
                    pending.Push(ifPlan.FalseBranch);
                    pending.Push(", ");
                    pending.Push(ifPlan.TrueBranch);
                    pending.Push(", ");
                    pending.Push(ifPlan.Condition);
                    pending.Push("If(");
                    continue;
            }

            var part = current switch
            {
                string literal => literal,
                LoopExprPlan.Constant constant => $"Const({Evaluator.FormatResultForDiagnostic(constant.Value.ToResult())})",
                LoopExprPlan.StringConstant constant => $"StringConst(length={constant.Value.Length})",
                LoopExprPlan.StateSlot stateSlot => $"StateSlot({stateSlot.Name})",
                LoopExprPlan.CapturedSlot capturedSlot => $"CapturedSlot({capturedSlot.Name})",
                LoopExprPlan.CountedParamSlot countedParamSlot => $"CountedParamSlot({countedParamSlot.Name})",
                LoopExprPlan.TempSlot tempSlot => $"TempSlot({tempSlot.Name})",
                LoopExprPlan.TempCall tempCall => $"TempCall({tempCall.Name})",
                LoopExprPlan.Fallback fallback => $"Fallback({fallback.Reason})",
                _ => throw new InvalidOperationException($"Unhandled loop expression plan: {current.GetType().Name}"),
            };
            var available = maxLength - text.Length;
            text.Append(part.AsSpan(0, Math.Min(part.Length, available)));
            if (part.Length > available || pending.Count != 0 && text.Length == maxLength)
                return text.Append("...").ToString();
        }

        return text.ToString();
    }

    private static string LoopUnaryPlanName(UnaryOp op)
        => op switch
        {
            UnaryOp.Minus => "Negate",
            UnaryOp.Not => "Not",
            _ => op.ToString(),
        };

    private static string LoopBinaryPlanName(BinaryOp op)
        => op switch
        {
            BinaryOp.Add => "Add",
            BinaryOp.Sub => "Subtract",
            BinaryOp.Mul => "Multiply",
            BinaryOp.Div => "Divide",
            BinaryOp.IDiv => "IntegerDivide",
            BinaryOp.Mod => "Mod",
            BinaryOp.Pow => "Power",
            BinaryOp.Lt => "LessThan",
            BinaryOp.Gt => "GreaterThan",
            BinaryOp.Le => "LessOrEqual",
            BinaryOp.Ge => "GreaterOrEqual",
            BinaryOp.Eq => "Equal",
            BinaryOp.Ne => "NotEqual",
            BinaryOp.And => "And",
            BinaryOp.Or => "Or",
            BinaryOp.Xor => "Xor",
            _ => op.ToString(),
        };
}
