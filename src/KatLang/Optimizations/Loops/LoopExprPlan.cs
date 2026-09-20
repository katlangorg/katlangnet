using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation.Caching;

namespace KatLang.Optimizations.Loops;

/// <summary>
/// One planned node of a loop step expression: a C# <c>closed</c> record whose direct
/// descendants are exactly the sealed nested records below, so
/// <see cref="LoopOptimizer.EvalLoopExprPlan"/> and the diagnostic renderer are switch
/// expressions that name every kind with no catch-all arm — a new plan kind is a build
/// error at each of them until it is given an evaluation and a rendering.
/// </summary>
internal closed record LoopExprPlan(Expr Source)
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
    /// A planned comparison chain: the first operand's plan and one
    /// <see cref="LoopComparisonLink"/> per written link. Evaluated exactly like the
    /// generic chain (<c>Evaluator.EvalExpressionSpineCounted</c>'s Comparison case):
    /// operands once each, left to right, each link compared as soon as its operand is
    /// available, eager past <c>false</c>, stopped by an error.
    /// </summary>
    public sealed record Comparison(Expr Source, LoopExprPlan First, IReadOnlyList<LoopComparisonLink> Links) : LoopExprPlan(Source);

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

/// <summary>One link of a planned comparison chain: the operator and the plan of its operand (not a plan node itself).</summary>
internal sealed record LoopComparisonLink(ComparisonOp Op, LoopExprPlan Operand);

internal static partial class LoopOptimizer
{
    /// <summary>
    /// The written spelling of the <c>if</c> builtin, taken from the builtin registry
    /// rather than a literal, so the planner's lookup key cannot drift from the
    /// callable it plans.
    /// </summary>
    private static readonly string IfBuiltinName = Evaluator.BuiltinDisplayName(BuiltinId.@if);

    private readonly record struct LoopExprPlanBuild(LoopExprPlan Plan, bool IsFullyPlanned);

    private readonly record struct LoopExprPlanTryBuildResult(LoopExprPlan? Plan, string? FallbackReason);

    private static LoopExprPlanBuild BuildLoopExprPlan(
        Expr expr,
        IReadOnlyList<string> stateNames,
        Evaluator.EvalCtx ctx,
        ValEnv parentValEnv,
        IReadOnlyList<LoopTempPlan> tempPlans)
    {
        var result = TryBuildLoopExprPlan(expr, stateNames, ctx, parentValEnv, tempPlans);
        if (result.Plan is not null)
            return new LoopExprPlanBuild(result.Plan, true);

        var reason = result.FallbackReason ?? $"unsupported expression: {Evaluator.ExprKind(expr)}";
        ctx.LoopDiagnostics?.RecordFallbackReason(reason);
        return new LoopExprPlanBuild(new LoopExprPlan.Fallback(expr, reason), false);
    }

    /// <summary>
    /// The fallback reason recorded when the host stack cannot hold the planner's walk of a
    /// step expression (see <see cref="TryBuildLoopExprPlan"/>).
    /// </summary>
    internal const string InsufficientStackFallbackReason = "insufficient host stack headroom to plan the expression";

    private static LoopExprPlanTryBuildResult TryBuildLoopExprPlan(
        Expr expr,
        IReadOnlyList<string> stateNames,
        Evaluator.EvalCtx ctx,
        ValEnv parentValEnv,
        IReadOnlyList<LoopTempPlan> tempPlans,
        Dictionary<Expr, LoopExprPlanTryBuildResult>? memo = null)
    {
        // A plan is built at loop-INVOCATION time, after the dynamic recursion has already
        // consumed its share of the host stack, and this walk recurses once per AST level of
        // the step (two frames per level, three through a planned `if`) between two budget
        // chokepoints. Probe the host stack per level exactly like the chokepoints do: a step
        // that no longer fits is simply not plannable HERE and takes the generic strategy,
        // whose expression spines are iterative and whose invocations probe. A stack-position
        // verdict is never memoized — the same node may fit on a later, shallower visit.
        if (!RuntimeHelpers.TryEnsureSufficientExecutionStack())
            return new LoopExprPlanTryBuildResult(null, InsufficientStackFallbackReason);

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
        ValEnv parentValEnv,
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

            case Expr.BoolLiteral(var value):
                return new LoopExprPlanTryBuildResult(
                    new LoopExprPlan.Constant(expr, PlannedLoopValue.FromResult(new Result.Bool(value))),
                    null);

            case Expr.Param(var name):
            {
                for (var i = 0; i < stateNames.Count; i++)
                {
                    if (stateNames[i] == name)
                        return new LoopExprPlanTryBuildResult(new LoopExprPlan.StateSlot(expr, i, name), null);
                }

                if (Evaluator.CapturedParameterNeedsOwnerLookup(name, ctx, parentValEnv))
                    return new LoopExprPlanTryBuildResult(null, $"captured parameter requires its lexical activation: {name}");

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

            case Expr.Comparison(var first, var links):
            {
                var firstPlan = TryBuildLoopExprPlan(first, stateNames, ctx, parentValEnv, tempPlans, memo);
                if (firstPlan.Plan is null)
                    return new LoopExprPlanTryBuildResult(null, firstPlan.FallbackReason);

                var linkPlans = new List<LoopComparisonLink>(links.Count);
                foreach (var link in links)
                {
                    var operandPlan = TryBuildLoopExprPlan(link.Operand, stateNames, ctx, parentValEnv, tempPlans, memo);
                    if (operandPlan.Plan is null)
                        return new LoopExprPlanTryBuildResult(null, operandPlan.FallbackReason);

                    linkPlans.Add(new LoopComparisonLink(link.Op, operandPlan.Plan));
                }

                return new LoopExprPlanTryBuildResult(
                    new LoopExprPlan.Comparison(expr, firstPlan.Plan, linkPlans),
                    null);
            }

            case Expr.Resolve(var name):
                if (TryFindLoopTempPlan(tempPlans, name, out var tempPlan) && tempPlan.ParameterNames.Count == 0)
                    return new LoopExprPlanTryBuildResult(new LoopExprPlan.TempSlot(expr, tempPlan.Index, name), null);

                return new LoopExprPlanTryBuildResult(null, $"unsupported local property reference: {name}");

            case Expr.Call(var func, var callArgs):
                // The spelling is only a lookup KEY; the RESOLVED identity decides.
                // `if` is an ordinary prelude binding that a nearer property or
                // parameter may shadow, so a step body calling a user-defined `if`
                // must plan as an ordinary call — never as the intrinsic conditional.
                if (func is Expr.Resolve resolvedCallee
                    && resolvedCallee.Name == IfBuiltinName
                    && Evaluator.ResolvesToBuiltinAlgorithm(IfBuiltinName, BuiltinId.@if, ctx))
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
        ValEnv parentValEnv,
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
    /// invocation is charged through the SAME helper, BEFORE any cache or memo is
    /// consulted, so a hit and a miss charge the identical access (one step, one depth
    /// level, the property's declaration span on a rejected enter) and only a miss
    /// additionally charges what the temp's body evaluates. Reuse follows the run
    /// cache's law (<c>ZeroArgPropertyCacheKey</c>): an EXPORTED temp is served from the
    /// run's cache itself — one entry per run per declaring scope, shared with the
    /// generic evaluator across iterations, temp calls, and loop invocations — while a
    /// local-only temp (its value reads the step's state or a captured input) is
    /// memoized per iteration, the counterpart of the per-iteration environment
    /// identities the generic path keys such a property on.
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
        var temp = frame.Template.TempPlans[index];
        if (temp.Binding.Exposure == PropertyExposure.Exported)
            return EvalRunCachedLoopTemp(frame, temp);

        if (frame.TryGetTempSlot(index, out var value))
            return EvalResult<PlannedLoopValue>.Ok(value);

        var tempR = EvalLoopExprPlan(temp.Plan, frame);
        if (tempR.IsError) return tempR.Error;
        frame.SetTempSlot(index, tempR.Value);
        return tempR;
    }

    /// <summary>
    /// An exported temp read served from the run's zero-argument property cache under
    /// the SAME execution the generic evaluator presents for the property (the step
    /// algorithm as owner, the declared binding, the counted lexical access shape):
    /// the key of an exported binding does not depend on the environment identities,
    /// so the planned and generic strategies share one entry and one evaluation of
    /// the temp's body per run, keeping their evaluation counts, budget charges, and
    /// string materialization identical.
    /// </summary>
    private static EvalResult<PlannedLoopValue> EvalRunCachedLoopTemp(
        LoopRunFrame frame,
        LoopTempPlan temp)
    {
        var ctx = frame.IterationCtx;
        var cachedR = ctx.ZeroArgPropertyResultCache.GetOrEvaluate(
            new ZeroArgPropertyExecution(
                frame.Template.Step,
                temp.Binding,
                ZeroArgPropertyAccessKind.CountedLexical,
                Evaluator.ValueEnvironmentCacheIdentity(frame.ValueEnvironment),
                ctx.AlgEnv,
                ctx.CountedParamEnv,
                ctx.Budget),
            () =>
            {
                var tempR = EvalLoopExprPlan(temp.Plan, frame);
                if (tempR.IsError) return tempR.Error;
                return EvalResult<ZeroArgPropertyResult>.Ok(
                    new ZeroArgPropertyResult(tempR.Value.ToResult(), tempR.Value.EmittedCount));
            });
        if (cachedR.IsError) return cachedR.Error;

        return EvalResult<PlannedLoopValue>.Ok(
            PlannedLoopValue.FromResult(cachedR.Value.Value, cachedR.Value.EmittedCount));
    }

    /// <summary>
    /// A temp CALL. MIRROR of the generic user call (<c>Evaluator.EvalUserCallCounted</c>
    /// inside the call-expression boundary of <c>EvalCallCountedExpr</c>): the dynamic
    /// invocation is charged through the SAME helper with the same limit-span rule, the
    /// body is evaluated FRESH on every call (a call bypasses the property cache — the
    /// <c>A</c> versus <c>A()</c> rule), and the caller's per-iteration temp memo is
    /// suspended for the call's duration because the generic callee runs in fresh
    /// environments, whose identities key every LOCAL-ONLY property entry
    /// (<see cref="LoopRunFrame.SuspendTempMemo"/>); an EXPORTED temp read inside the
    /// call keeps hitting the run cache exactly like the generic callee's read. Only the
    /// RETURNED result is decorated by the boundary, exactly like the planned <c>if</c>.
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
        using (frame.SuspendTempMemo())
        {
            return EvalLoopExprPlan(frame.Template.TempPlans[index].Plan, frame);
        }
    }

    /// <summary>
    /// Evaluates one planned node. Compiler-exhaustive over the closed
    /// <see cref="LoopExprPlan"/> hierarchy: every kind is named, there is no catch-all
    /// arm, and a new kind fails the build here until it is given an evaluation.
    /// </summary>
    private static EvalResult<PlannedLoopValue> EvalLoopExprPlan(
        LoopExprPlan plan,
        LoopRunFrame frame)
        => plan switch
        {
            LoopExprPlan.Constant constant => EvalResult<PlannedLoopValue>.Ok(constant.Value),

            LoopExprPlan.StringConstant constant => EvalLoopStringConstant(constant, frame),

            LoopExprPlan.StateSlot stateSlot =>
                EvalResult<PlannedLoopValue>.Ok(PlannedLoopValue.FromResult(frame.GetStateSlot(stateSlot.Index))),

            LoopExprPlan.CapturedSlot capturedSlot =>
                EvalResult<PlannedLoopValue>.Ok(PlannedLoopValue.FromResult(frame.GetCapturedSlot(capturedSlot.Index))),

            LoopExprPlan.CountedParamSlot countedParamSlot => EvalLoopCountedParamSlot(countedParamSlot, frame),

            // MIRROR of the generic value-position read (Evaluator.EvalResolveCounted):
            // the reference's own span is attached to an error that carries none.
            LoopExprPlan.TempSlot tempSlot =>
                Evaluator.WithSpan(tempSlot.Source.Span, EvalLoopTempSlot(frame, tempSlot.Index)),

            LoopExprPlan.TempCall tempCall => EvalLoopTempCall(tempCall, frame),

            LoopExprPlan.Unary unary => EvalLoopUnaryPlan(unary, frame),

            LoopExprPlan.Binary binary => EvalLoopBinaryPlan(binary, frame),

            LoopExprPlan.Comparison comparison => EvalLoopComparisonPlan(comparison, frame),

            // A planned `if` REPLACES an ordinary `if` call expression, so its
            // failures must carry the same diagnostic boundary the generic call
            // dispatch attaches (`EvalCallExpr`/`EvalCallCountedExpr` inside
            // `WithSpan`) — for a failing condition, for the selected branch, and
            // for the `if`'s own truth-value rejection alike. Only the RETURNED
            // result is decorated, so branch laziness, planned-operation counts,
            // budget charges, and cache state are untouched, and a nested planned
            // `if` nests its own frame exactly like the generic composition.
            LoopExprPlan.If ifPlan => Evaluator.WithPlannedCallBoundary(
                ifPlan.Source,
                ifPlan.Callee,
                frame.IterationCtx,
                EvalLoopIfExprPlanBody(ifPlan, frame)),

            LoopExprPlan.Fallback fallback => EvalLoopFallbackPlan(fallback, frame),
        };

    private static EvalResult<PlannedLoopValue> EvalLoopStringConstant(
        LoopExprPlan.StringConstant constant,
        LoopRunFrame frame)
    {
        var valueR = Evaluator.MakeStringResult(
            frame.IterationCtx,
            constant.Value,
            constant.Source.Span);
        return valueR.IsError
            ? valueR.Error
            : EvalResult<PlannedLoopValue>.Ok(PlannedLoopValue.FromResult(valueR.Value));
    }

    private static EvalResult<PlannedLoopValue> EvalLoopCountedParamSlot(
        LoopExprPlan.CountedParamSlot countedParamSlot,
        LoopRunFrame frame)
    {
        var countedParam = frame.GetCountedParamSlot(countedParamSlot.Index);
        return EvalResult<PlannedLoopValue>.Ok(
            PlannedLoopValue.FromResult(countedParam.Value, countedParam.EmittedCount));
    }

    private static EvalResult<PlannedLoopValue> EvalLoopUnaryPlan(
        LoopExprPlan.Unary unary,
        LoopRunFrame frame)
    {
        // The planned spine recurses per plan level (the generic spine is iterative).
        // Probe again before descending: planning and evaluation have different frame
        // sizes, including this per-kind helper. Exhaustion is a structured rejection.
        if (!RuntimeHelpers.TryEnsureSufficientExecutionStack())
            return new EvalError.EvaluationStackExhausted();

        var operandR = EvalLoopExprPlan(unary.Operand, frame);
        if (operandR.IsError) return operandR.Error;
        frame.Diagnostics?.RecordPlannedBuiltinOperation();
        return ApplyPlannedUnary(unary.Op, operandR.Value, unary.Source.Span);
    }

    private static EvalResult<PlannedLoopValue> EvalLoopBinaryPlan(
        LoopExprPlan.Binary binary,
        LoopRunFrame frame)
    {
        if (!RuntimeHelpers.TryEnsureSufficientExecutionStack())
            return new EvalError.EvaluationStackExhausted();

        var leftR = EvalLoopExprPlan(binary.Left, frame);
        if (leftR.IsError) return leftR.Error;
        var rightR = EvalLoopExprPlan(binary.Right, frame);
        if (rightR.IsError) return rightR.Error;
        frame.Diagnostics?.RecordPlannedBuiltinOperation();
        return ApplyPlannedBinary(binary.Op, binary.Left.Source, binary.Right.Source, leftR.Value, rightR.Value, binary.Source.Span);
    }

    /// <summary>
    /// MIRROR of the generic comparison-chain evaluation (the Comparison case of
    /// <c>Evaluator.EvalExpressionSpineCounted</c>): the first operand, then link by
    /// link — evaluate the operand, compare the PREVIOUS operand's value with it (every
    /// operand evaluated exactly once, one planned operation per link), keep going past a
    /// false link, stop at the first error before any later operand is evaluated.
    /// </summary>
    private static EvalResult<PlannedLoopValue> EvalLoopComparisonPlan(
        LoopExprPlan.Comparison comparison,
        LoopRunFrame frame)
    {
        if (!RuntimeHelpers.TryEnsureSufficientExecutionStack())
            return new EvalError.EvaluationStackExhausted();

        var previousR = EvalLoopExprPlan(comparison.First, frame);
        if (previousR.IsError) return previousR.Error;
        var previous = previousR.Value;
        var previousSource = comparison.First.Source;
        var holds = true;
        var links = comparison.Links;
        // Indexed, not enumerated: the planned path runs once per iteration and must not
        // allocate an enumerator per chain (the temp-call allocation pins are tight).
        for (var index = 0; index < links.Count; index++)
        {
            var link = links[index];
            var nextR = EvalLoopExprPlan(link.Operand, frame);
            if (nextR.IsError) return nextR.Error;
            frame.Diagnostics?.RecordPlannedBuiltinOperation();
            var linkR = ApplyPlannedComparison(
                link.Op, previousSource, link.Operand.Source, previous, nextR.Value, comparison.Source.Span);
            if (linkR.IsError) return linkR.Error;
            holds &= linkR.Value;
            previous = nextR.Value;
            previousSource = link.Operand.Source;
        }

        return EvalResult<PlannedLoopValue>.Ok(PlannedLoopValue.FromResult(new Result.Bool(holds)));
    }

    private static EvalResult<PlannedLoopValue> EvalLoopFallbackPlan(
        LoopExprPlan.Fallback fallback,
        LoopRunFrame frame)
    {
        var fallbackR = Evaluator.EvalCounted(fallback.Source, frame.IterationCtx, frame.ValueEnvironment);
        if (fallbackR.IsError) return fallbackR.Error;
        return EvalResult<PlannedLoopValue>.Ok(
            PlannedLoopValue.FromResult(fallbackR.Value.Value, fallbackR.Value.EmittedCount));
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

        var truth = conditionR.Value.AsBool();
        if (truth is null)
        {
            // UNSPANNED, exactly like the generic `if` builtin's Boolean-requirement
            // rejection (same message): the surrounding call boundary stamps only the
            // context wrappers (AtSpanIfMissing), and the innermost error's span is
            // public structured state, so pre-stamping it here would be an observable
            // divergence from the generic error tree.
            return new EvalError.TypeMismatch(
                Evaluator.BooleanRequiredMessage("if condition", conditionR.Value.ToResult()));
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

    private static EvalResult<PlannedLoopValue> ApplyPlannedUnary(
        UnaryOp op,
        PlannedLoopValue operand,
        SourceSpan? span)
    {
        // MIRROR of Evaluator.ApplyUnaryOperator's numeric negation arm: a numeric
        // operand of `-` stays in the unboxed planned representation. Every other
        // case — `not` (Boolean-only), the string and Boolean rejections, and the
        // numeric-conversion failure, all stamped with the unary expression's span —
        // delegates to the shared operator application so the planned strategy
        // cannot drift from the generic error/span policy.
        if (op == UnaryOp.Minus && operand.AsNum() is { } value)
            return EvalResult<PlannedLoopValue>.Ok(PlannedLoopValue.FromNumeric(-value));

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
        // The logical operators delegate to the shared operator application (they are
        // Boolean-only: a numeric operand is the shared value-kind rejection, never a
        // nonzero truth test). The numeric fast path below is for arithmetic only.
        if (op is not (BinaryOp.And or BinaryOp.Or or BinaryOp.Xor)
            && left.AsNum() is { } x && right.AsNum() is { } y)
            return ApplyPlannedNumericBinary(op, x, y, span);

        var resultR = Evaluator.ApplyBinaryOperator(op, leftExpr, rightExpr, left.ToResult(), right.ToResult(), span);
        if (resultR.IsError) return resultR.Error;
        return EvalResult<PlannedLoopValue>.Ok(PlannedLoopValue.FromResult(resultR.Value));
    }

    /// <summary>
    /// One link of a planned comparison chain. `==` and `!=` always delegate to the
    /// evaluator's structural equality so the optimized loop path can never drift back
    /// to numeric-only equality; an ORDERING link with two numeric operands takes the
    /// unboxed fast path through the ONE shared comparison
    /// (<see cref="Evaluator.TryCompareNumeric"/>), and every other case — string and
    /// value-kind rejections included, with the link's context and span — delegates to
    /// the shared <see cref="Evaluator.ApplyComparison"/>.
    /// </summary>
    private static EvalResult<bool> ApplyPlannedComparison(
        ComparisonOp op,
        Expr leftExpr,
        Expr rightExpr,
        PlannedLoopValue left,
        PlannedLoopValue right,
        SourceSpan? chainSpan)
    {
        if (op is not (ComparisonOp.Eq or ComparisonOp.Ne)
            && left.AsNum() is { } x && right.AsNum() is { } y)
            return EvalResult<bool>.Ok(Evaluator.TryCompareNumeric(op, x, y)!.Value);

        return Evaluator.ApplyComparison(op, leftExpr, rightExpr, left.ToResult(), right.ToResult(), chainSpan);
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
        // with NaN are false). `div` and `^` are the two arms with non-trivial
        // numeric semantics, and both delegate to the ONE shared implementation
        // (Decimal128Numerics.IntegerDivide, Evaluator.EvalPow) so the planned and
        // generic strategies cannot drift.
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
            BinaryOp.IDiv => Decimal128Numerics.IntegerDivide(x, y),
            BinaryOp.Mod => x % y,
            // And/Or/Xor are intentionally absent: the logical operators are
            // Boolean-only and handled by ApplyBinaryOperator in ApplyPlannedBinary,
            // so they never reach this path (comparisons are chain links, planned
            // by ApplyPlannedComparison).
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
        // The work stack holds plan nodes still to render and the literal fragments
        // (an opening head, a separator, a closer) already decided for them.
        var pending = new Stack<object>();
        pending.Push(plan);
        while (pending.Count != 0 && text.Length < maxLength)
        {
            var current = pending.Pop();
            string part;
            if (current is ComparisonDiagnosticCursor cursor)
            {
                if (cursor.Index == cursor.Links.Count)
                    continue;
                var link = cursor.Links[cursor.Index++];
                pending.Push(cursor);
                pending.Push(link.Operand);
                part = $" {LoopComparisonPlanName(link.Op)} ";
            }
            else
            {
                part = current is string literal
                    ? literal
                    : DescribeLoopExprPlanNode((LoopExprPlan)current, pending);
            }
            var available = maxLength - text.Length;
            text.Append(part.AsSpan(0, Math.Min(part.Length, available)));
            if (part.Length > available || pending.Count != 0 && text.Length == maxLength)
                return text.Append("...").ToString();
        }

        return text.ToString();
    }

    // A chain can be arbitrarily wide. Schedule one link at a time so the
    // output bound also bounds pending storage and reads of the operand list.
    private sealed class ComparisonDiagnosticCursor(IReadOnlyList<LoopComparisonLink> links)
    {
        public readonly IReadOnlyList<LoopComparisonLink> Links = links;
        public int Index;
    }

    /// <summary>
    /// The text emitted for one plan node when it is reached: a leaf's whole rendering, or
    /// a composite's opening head after its operands and closer have been queued on
    /// <paramref name="pending"/>. Compiler-exhaustive over the closed hierarchy.
    /// </summary>
    private static string DescribeLoopExprPlanNode(LoopExprPlan plan, Stack<object> pending)
        => plan switch
        {
            LoopExprPlan.Unary unary => QueueOperands(pending, $"{LoopUnaryPlanName(unary.Op)}(", unary.Operand),
            LoopExprPlan.Binary binary => QueueOperands(pending, $"{LoopBinaryPlanName(binary.Op)}(", binary.Left, binary.Right),
            LoopExprPlan.Comparison comparison => QueueComparisonOperands(pending, comparison),
            LoopExprPlan.If ifPlan => QueueOperands(pending, "If(", ifPlan.Condition, ifPlan.TrueBranch, ifPlan.FalseBranch),
            LoopExprPlan.Constant constant => $"Const({Evaluator.FormatResultForDiagnostic(constant.Value.ToResult())})",
            LoopExprPlan.StringConstant constant => $"StringConst(length={constant.Value.Length})",
            LoopExprPlan.StateSlot stateSlot => $"StateSlot({stateSlot.Name})",
            LoopExprPlan.CapturedSlot capturedSlot => $"CapturedSlot({capturedSlot.Name})",
            LoopExprPlan.CountedParamSlot countedParamSlot => $"CountedParamSlot({countedParamSlot.Name})",
            LoopExprPlan.TempSlot tempSlot => $"TempSlot({tempSlot.Name})",
            LoopExprPlan.TempCall tempCall => $"TempCall({tempCall.Name})",
            LoopExprPlan.Fallback fallback => $"Fallback({fallback.Reason})",
        };

    /// <summary>
    /// Queues a composite's closer and its comma-separated operands (last operand first,
    /// so they pop in written order) and returns the head to emit now.
    /// </summary>
    private static string QueueOperands(Stack<object> pending, string head, params ReadOnlySpan<LoopExprPlan> operands)
    {
        pending.Push(")");
        for (var index = operands.Length - 1; index >= 0; index--)
        {
            pending.Push(operands[index]);
            if (index != 0)
                pending.Push(", ");
        }

        return head;
    }

    /// <summary>
    /// Queues a comparison chain. A ONE-link chain — the ordinary comparison — keeps the
    /// established descriptor spelling of one operation over two operand plans
    /// (<c>LessThan(a, b)</c>); a longer chain is described as
    /// <c>Compare(first LessThan x Equal y …)</c>, the chain's operands interleaved with
    /// its link operator names, so the description shows the flat chain structure that
    /// is evaluated (never nested comparisons).
    /// </summary>
    private static string QueueComparisonOperands(Stack<object> pending, LoopExprPlan.Comparison comparison)
    {
        if (comparison.Links.Count == 1)
            return QueueOperands(pending, $"{LoopComparisonPlanName(comparison.Links[0].Op)}(", comparison.First, comparison.Links[0].Operand);

        pending.Push(")");
        pending.Push(new ComparisonDiagnosticCursor(comparison.Links));
        pending.Push(comparison.First);
        return "Compare(";
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
            BinaryOp.And => "And",
            BinaryOp.Or => "Or",
            BinaryOp.Xor => "Xor",
            _ => op.ToString(),
        };

    private static string LoopComparisonPlanName(ComparisonOp op)
        => op switch
        {
            ComparisonOp.Lt => "LessThan",
            ComparisonOp.Gt => "GreaterThan",
            ComparisonOp.Le => "LessOrEqual",
            ComparisonOp.Ge => "GreaterOrEqual",
            ComparisonOp.Eq => "Equal",
            ComparisonOp.Ne => "NotEqual",
            _ => op.ToString(),
        };
}
