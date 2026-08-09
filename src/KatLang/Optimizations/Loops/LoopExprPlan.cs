namespace KatLang.Optimizations.Loops;

internal abstract record LoopExprPlan(Expr Source)
{
    public sealed record Constant(Expr Source, PlannedLoopValue Value) : LoopExprPlan(Source);

    public sealed record StringConstant(Expr Source, string Value) : LoopExprPlan(Source);

    public sealed record StateSlot(Expr Source, int Index, string Name) : LoopExprPlan(Source);

    public sealed record CapturedSlot(Expr Source, int Index, string Name) : LoopExprPlan(Source);

    public sealed record CountedParamSlot(Expr Source, int Index, string Name) : LoopExprPlan(Source);

    public sealed record TempSlot(Expr Source, int Index, string Name) : LoopExprPlan(Source);

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
        IReadOnlyList<LoopTempPlan> tempPlans)
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
                var operandPlan = TryBuildLoopExprPlan(operand, stateNames, ctx, parentValEnv, tempPlans);
                if (operandPlan.Plan is null)
                    return new LoopExprPlanTryBuildResult(null, operandPlan.FallbackReason);

                return new LoopExprPlanTryBuildResult(
                    new LoopExprPlan.Unary(expr, op, operandPlan.Plan),
                    null);
            }

            case Expr.Binary(var op, var left, var right):
            {
                var leftPlan = TryBuildLoopExprPlan(left, stateNames, ctx, parentValEnv, tempPlans);
                if (leftPlan.Plan is null)
                    return new LoopExprPlanTryBuildResult(null, leftPlan.FallbackReason);

                var rightPlan = TryBuildLoopExprPlan(right, stateNames, ctx, parentValEnv, tempPlans);
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
                    return TryBuildLoopIfExprPlan(expr, func, callArgs, stateNames, ctx, parentValEnv, tempPlans);
                }

                if (func is Expr.Resolve(var tempName) && TryFindLoopTempPlan(tempPlans, tempName, out var calledTempPlan))
                {
                    if (IsLoopTempCallShape(callArgs, calledTempPlan))
                        return new LoopExprPlanTryBuildResult(new LoopExprPlan.TempSlot(expr, calledTempPlan.Index, tempName), null);

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
        IReadOnlyList<LoopTempPlan> tempPlans)
    {
        if (callArgs.Count != 3)
            return new LoopExprPlanTryBuildResult(null, $"unsupported if arity: {callArgs.Count}");

        var conditionPlan = TryBuildLoopExprPlan(callArgs[0], stateNames, ctx, parentValEnv, tempPlans);
        if (conditionPlan.Plan is null)
            return new LoopExprPlanTryBuildResult(null, $"unsupported if condition: {conditionPlan.FallbackReason}");

        var truePlan = TryBuildLoopExprPlan(callArgs[1], stateNames, ctx, parentValEnv, tempPlans);
        if (truePlan.Plan is null)
            return new LoopExprPlanTryBuildResult(null, $"unsupported if true branch: {truePlan.FallbackReason}");

        var falsePlan = TryBuildLoopExprPlan(callArgs[2], stateNames, ctx, parentValEnv, tempPlans);
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

    private static EvalResult<PlannedLoopValue> EvalLoopTempSlot(
        LoopRunFrame frame,
        int index)
    {
        if (frame.TryGetTempSlot(index, out var value))
            return EvalResult<PlannedLoopValue>.Ok(value);

        var tempPlan = frame.Template.TempPlans[index];
        var tempR = EvalLoopExprPlan(tempPlan.Plan, frame);
        if (tempR.IsError) return tempR.Error;
        frame.SetTempSlot(index, tempR.Value);
        return tempR;
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
                return EvalLoopTempSlot(frame, tempSlot.Index);

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
        var conditionR = EvalLoopExprPlan(ifPlan.Condition, frame);
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

        return EvalLoopExprPlan(truth.Value ? ifPlan.TrueBranch : ifPlan.FalseBranch, frame);
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
        if (operand.EmittedCount == 0)
            return EvalResult<PlannedLoopValue>.Ok(PlannedLoopValue.FromResult(Result.SequenceValue.TakeOwnership([]), 0));

        if (operand.AsNum() is { } value)
        {
            var unaryResult = op switch
            {
                UnaryOp.Minus => -value,
                UnaryOp.Not => value == 0 ? 1m : 0m,
                _ => 0m,
            };
            return EvalResult<PlannedLoopValue>.Ok(PlannedLoopValue.FromNumeric(unaryResult));
        }

        var result = operand.ToResult();
        if (result is Result.Str)
            return new EvalError.TypeMismatch("Unary operator is not supported for strings") { Span = span };

        var valueR = Evaluator.ExpectInt(result);
        if (valueR.IsError) return valueR.Error with { Span = valueR.Error.Span ?? span };

        var genericUnaryResult = op switch
        {
            UnaryOp.Minus => -valueR.Value,
            UnaryOp.Not => valueR.Value == 0 ? 1m : 0m,
            _ => 0m,
        };
        return EvalResult<PlannedLoopValue>.Ok(PlannedLoopValue.FromNumeric(genericUnaryResult));
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
        decimal x,
        decimal y,
        SourceSpan? span)
    {
        if ((op is BinaryOp.Div or BinaryOp.IDiv or BinaryOp.Mod) && y == 0)
            return new EvalError.DivByZero() { Span = span };

        if (op == BinaryOp.Pow)
        {
            var powR = Evaluator.EvalPow(span, x, y);
            if (powR.IsError) return powR.Error;
            return EvalResult<PlannedLoopValue>.Ok(PlannedLoopValue.FromResult(powR.Value));
        }

        decimal result;
        try
        {
            result = op switch
            {
                BinaryOp.Add => x + y,
                BinaryOp.Sub => x - y,
                BinaryOp.Mul => x * y,
                BinaryOp.Div => x / y,
                BinaryOp.IDiv => Math.Truncate(x / y),
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
        }
        catch (OverflowException)
        {
            return new EvalError.NumericOverflow() { Span = span };
        }

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
        => plan switch
        {
            LoopExprPlan.Constant constant => $"Const({Evaluator.FormatResultForDiagnostic(constant.Value.ToResult())})",
            LoopExprPlan.StringConstant constant => $"StringConst(length={constant.Value.Length})",
            LoopExprPlan.StateSlot stateSlot => $"StateSlot({stateSlot.Name})",
            LoopExprPlan.CapturedSlot capturedSlot => $"CapturedSlot({capturedSlot.Name})",
            LoopExprPlan.CountedParamSlot countedParamSlot => $"CountedParamSlot({countedParamSlot.Name})",
            LoopExprPlan.TempSlot tempSlot => $"TempSlot({tempSlot.Name})",
            LoopExprPlan.Unary unary => $"{LoopUnaryPlanName(unary.Op)}({DescribeLoopExprPlan(unary.Operand)})",
            LoopExprPlan.Binary binary => $"{LoopBinaryPlanName(binary.Op)}({DescribeLoopExprPlan(binary.Left)}, {DescribeLoopExprPlan(binary.Right)})",
            LoopExprPlan.If ifPlan => $"If({DescribeLoopExprPlan(ifPlan.Condition)}, {DescribeLoopExprPlan(ifPlan.TrueBranch)}, {DescribeLoopExprPlan(ifPlan.FalseBranch)})",
            LoopExprPlan.Fallback fallback => $"Fallback({fallback.Reason})",
            _ => plan.GetType().Name,
        };

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
