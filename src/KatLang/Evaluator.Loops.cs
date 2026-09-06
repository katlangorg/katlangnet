using System.Collections;
using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using KatLang.Runtime;

namespace KatLang;

/// <summary>
/// Loops: algorithm-output slot evaluation, loop-state binding, the while/repeat builtins, and the shared unary/binary operator appliers (the "Algorithm output evaluation" and "Builtins" sections).
/// Part of the <see cref="Evaluator"/> partial class; the central state, lookup and open resolution,
/// the built-in prelude, and the run entry points remain in <c>Evaluator.cs</c>.
/// </summary>
public static partial class Evaluator
{
    // ── Algorithm output evaluation ─────────────────────────────────────────

    /// <summary>
    /// Evaluate an algorithm's output expressions and collect into a single Result
    /// (the value projection of <see cref="EvalAlgOutputCountedCore"/>). Output slots
    /// are combined with the structure-preserving <see cref="CombineOutputSlots"/>, not a
    /// general normalize: each non-spread output is one visible slot even when it is the
    /// empty sequence value <c>()</c>, and only an explicit spread contributes its expanded
    /// items. Redundant empty-sequence nesting has already canonicalized to <c>()</c>.
    /// User-defined algorithms may exist structurally without output, but forcing
    /// them in value position raises <see cref="EvalError.MissingOutput"/>.
    /// Lean: evalAlgOutput → EvalM Result.
    /// </summary>
    private static EvalResult<Result> EvalAlgOutputCore(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => ProjectCountedValue(EvalAlgOutputCountedCore(alg, ctx, valEnv));

    private static EvalResult<Result> EvalAlgOutput(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => EvalAlgOutputCore(alg, ctx, valEnv);

    private static EvalResult<Result> EvalProgramOutput(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => EvalAlgOutputCore(alg, ctx, valEnv);

    private static EvalResult<IReadOnlyList<Result>> EvalInitialLoopStateSlots(
        IReadOnlyList<ResolvedArgumentAlgorithm> initArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // Initial loop state preserves explicit argument boundaries: repeat(Step, 3, a, b)
        // starts with two slots, while repeat(Step, 3, Pair) starts with one slot even
        // when Pair evaluates to multiple values. Step outputs define later state slots;
        // capture a step result as a sequence value to keep one structured slot across iterations.
        var stateSlots = new List<Result>(initArgs.Count);
        foreach (var init in initArgs)
        {
            var slotR = EvalResolvedArgument(init, ctx, valEnv);
            if (slotR.IsError) return slotR.Error;
            stateSlots.Add(slotR.Value);
        }

        return EvalResult<IReadOnlyList<Result>>.Ok(stateSlots);
    }

    private static EvalResult<IReadOnlyList<Result>> EvalAlgOutputSlots(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        bool preserveSequenceSpreadExpressionBoundaries = false)
    {
        if (alg is Algorithm.Builtin(var builtin))
        {
            var countedR = EvalBuiltinValueCounted(builtin);
            return countedR.IsError
                ? countedR.Error
                : EvalResult<IReadOnlyList<Result>>.Ok(CountedTopLevelValues(countedR.Value));
        }

        if (alg.FindDuplicatePropName() is { } duplicateName)
            return new EvalError.DuplicateProperty(duplicateName);

        if (ConditionalValueAccessError("conditional", alg) is { } conditionalError)
            return conditionalError;

        if (alg is Algorithm.User { Output.Count: 0 })
            return new EvalError.MissingOutput();

        var slots = new List<Result>();
        var pushedCtx = ctx.Push(alg);
        foreach (var expr in alg.Output)
        {
            var countedR = EvalCounted(expr, pushedCtx, valEnv);
            if (countedR.IsError) return countedR.Error;

            if (preserveSequenceSpreadExpressionBoundaries && expr is Expr.SequenceSpread)
            {
                if (countedR.Value.EmittedCount != 0)
                    slots.Add(countedR.Value.Value);
                continue;
            }

            if (expr is Expr.SequenceSpread || countedR.Value.EmittedCount != 0)
                slots.AddRange(CountedTopLevelValues(countedR.Value));
            else
                slots.Add(countedR.Value.Value);
        }

        return EvalResult<IReadOnlyList<Result>>.Ok(slots);
    }

    private static EvalError LoopStateArityMismatch(
        Algorithm step,
        int expectedStateValueCount,
        int actualStateValueCount,
        string loopName)
        => LoopStateArityMismatch(
            step.ParameterPatterns,
            step.Parameters,
            expectedStateValueCount,
            actualStateValueCount,
            loopName);

    private static EvalError LoopStateArityMismatch(
        GenericLoopStepBindingContract bindingContract,
        int expectedStateValueCount,
        int actualStateValueCount,
        string loopName)
        => LoopStateArityMismatch(
            bindingContract.ParameterPatterns,
            bindingContract.Parameters,
            expectedStateValueCount,
            actualStateValueCount,
            loopName);

    private static EvalError LoopStateArityMismatch(
        IReadOnlyList<ParameterPattern> parameterPatterns,
        IReadOnlyList<ParameterDeclaration> parameters,
        int expectedStateValueCount,
        int actualStateValueCount,
        string loopName)
        // Expected is the binder-computed top-level state-slot count, NOT the
        // flattened capture count: a patterned step `Step((x, y))` has ONE
        // state slot but two flattened captures. The context's parameter names
        // are the matching top-level display labels ("(x, y)" is one entry).
        => new EvalError.WithContext(
            new LoopStateBindingContext(
                loopName,
                parameterPatterns.Select(static pattern => pattern.DisplayName).ToList(),
                actualStateValueCount),
            new EvalError.ArityMismatch(expectedStateValueCount, actualStateValueCount)
            {
                InferredImplicitParameters = ImplicitParameterProvenance.CollectFrom(parameters),
            });

    private static EvalError VariadicLoopStateArityMismatch(
        Algorithm step,
        int expectedMinimumStateValueCount,
        int actualStateValueCount,
        string loopName)
        => VariadicLoopStateArityMismatch(
            step.Parameters,
            expectedMinimumStateValueCount,
            actualStateValueCount,
            loopName);

    private static EvalError VariadicLoopStateArityMismatch(
        GenericLoopStepBindingContract bindingContract,
        int expectedMinimumStateValueCount,
        int actualStateValueCount,
        string loopName)
        => VariadicLoopStateArityMismatch(
            bindingContract.Parameters,
            expectedMinimumStateValueCount,
            actualStateValueCount,
            loopName);

    private static EvalError VariadicLoopStateArityMismatch(
        IReadOnlyList<ParameterDeclaration> parameters,
        int expectedMinimumStateValueCount,
        int actualStateValueCount,
        string loopName)
        => new EvalError.WithContext(
            new VariadicLoopStateBindingContext(
                loopName,
                parameters
                    .Where(static parameter => parameter.Kind != ParameterKind.Collecting)
                    .Select(static parameter => parameter.DisplayName)
                    .ToList(),
                expectedMinimumStateValueCount,
                actualStateValueCount),
            new EvalError.ArityMismatch(expectedMinimumStateValueCount, actualStateValueCount)
            {
                InferredImplicitParameters = ImplicitParameterProvenance.CollectFrom(parameters),
            });

    private static EvalResult<IReadOnlyList<(string Name, Result Value)>> BindEvaluatedSlotValueBindings(
        FlatCollectingBindingLayout layout,
        IReadOnlyList<(string ParameterName, BindingInputSlot Item)> normalBindings,
        CollectingCapture collectingCapture)
    {
        var valueBindings = new List<(string Name, Result Value)>(layout.Signature.Parameters.Count);
        var normalBindingIndex = 0;

        foreach (var parameter in layout.Signature.Parameters)
        {
            if (parameter.Kind == ParameterKind.Collecting)
            {
                valueBindings.Add((collectingCapture.Name, collectingCapture.Value));
                continue;
            }

            if (normalBindingIndex >= normalBindings.Count)
                return new EvalError.BadArity();

            var binding = normalBindings[normalBindingIndex++];
            if (binding.Item.Value is null)
                return new EvalError.BadArity();

            valueBindings.Add((binding.ParameterName, binding.Item.Value));
        }

        if (normalBindingIndex != normalBindings.Count)
            return new EvalError.BadArity();

        return EvalResult<IReadOnlyList<(string Name, Result Value)>>.Ok(valueBindings);
    }

    private static EvalResult<EvaluatedSlotBindings> BindEvaluatedSlotsToParameters(
        GenericLoopStepBindingContract bindingContract,
        IReadOnlyList<Result> evaluatedSlots,
        EvalCtx ctx,
        string callableName,
        GenericLoopStepBindingSelection bindingSelection,
        Func<int, int, EvalError> fixedArityMismatch,
        Func<int, int, EvalError> variadicArityMismatch)
    {
        // Evaluated slots are already Result values. This helper only applies
        // parameter layout; it does not evaluate argument expressions, unpack a
        // final sequence-value argument, or apply dot-call receiver boundary rules.
        EvalResult<EvaluatedSlotBindings> BindPatternedSlots()
        {
            var inputs = evaluatedSlots
                .Select(static slot => new ParameterPatternInput(slot, Algorithm: null, ValueError: null, ExplicitSequenceValueItems: null))
                .ToList();
            var bindingsR = BindParameterPatternList(
                bindingContract.ParameterPatterns,
                inputs,
                ctx,
                allowAlgorithmBindings: false,
                fixedArityMismatch);
            if (bindingsR.IsError) return bindingsR.Error;

            return EvalResult<EvaluatedSlotBindings>.Ok(new EvaluatedSlotBindings(
                bindingsR.Value.ValueBindings,
                bindingsR.Value.CountedBindings));
        }

        EvalResult<EvaluatedSlotBindings> BindFlatFixedSlots()
        {
            if (bindingContract.ParameterNames.Count != evaluatedSlots.Count)
                return fixedArityMismatch(bindingContract.ParameterNames.Count, evaluatedSlots.Count);

            var boundR = BindParams(bindingContract.ParameterNames, evaluatedSlots);
            if (boundR.IsError) return boundR.Error;

            return EvalResult<EvaluatedSlotBindings>.Ok(new EvaluatedSlotBindings(boundR.Value, []));
        }

        EvalResult<EvaluatedSlotBindings> BindFlatCollectingSlots(FlatCollectingBindingLayout layout)
        {
            var inputSlots = evaluatedSlots
                .Select(BindingInputSlot.FromEvaluatedValue)
                .ToArray();

            var boundItemsR = BindItemsToFlatCollectingLayout(
                layout,
                inputSlots,
                variadicArityMismatch);
            if (boundItemsR.IsError) return boundItemsR.Error;

            var boundItems = boundItemsR.Value;
            var capturedValues = new List<Result>(boundItems.CollectingItems.Count);
            foreach (var item in boundItems.CollectingItems)
            {
                if (item.Value is null)
                    return new EvalError.BadArity();

                capturedValues.Add(item.Value);
            }

            var collectingName = boundItems.CollectingParameterName
                ?? layout.CollectingName;
            if (collectingName is null)
                return new EvalError.BadArity();

            var collectingCaptureR = CreateCollectingCapture(ctx, collectingName, capturedValues);
            if (collectingCaptureR.IsError) return collectingCaptureR.Error;
            var collectingCapture = collectingCaptureR.Value;

            var valueBindingsR = BindEvaluatedSlotValueBindings(
                layout,
                boundItems.NormalBindings,
                collectingCapture);
            if (valueBindingsR.IsError) return valueBindingsR.Error;

            return EvalResult<EvaluatedSlotBindings>.Ok(new EvaluatedSlotBindings(
                valueBindingsR.Value,
                [(collectingCapture.Name, collectingCapture.CountedValue)]));
        }

        EvalResult<EvaluatedSlotBindings> BindLegacyShape()
        {
            if (UsesPatternBinding(bindingContract.ParameterPatterns))
                return BindPatternedSlots();

            return TryGetLegacyFlatCollectingBindingLayout(bindingContract.Parameters, callableName, out var legacyLayout)
                ? BindFlatCollectingSlots(legacyLayout)
                : BindFlatFixedSlots();
        }

        EvalResult<EvaluatedSlotBindings> BindSelectedFlatCollectingShape()
        {
            return bindingSelection.FlatCollectingLayout is { } layout
                ? BindFlatCollectingSlots(layout)
                : BindLegacyShape();
        }

        return bindingSelection.Shape switch
        {
            GenericLoopStepBindingShape.Patterned => BindPatternedSlots(),
            GenericLoopStepBindingShape.FlatFixed => BindFlatFixedSlots(),
            GenericLoopStepBindingShape.FlatCollecting => BindSelectedFlatCollectingShape(),
            _ => BindLegacyShape(),
        };
    }

    private static EvalResult<EvaluatedSlotBindings> BindLoopStepState(
        GenericLoopStepBindingContract bindingContract,
        IReadOnlyList<Result> stateSlots,
        EvalCtx ctx,
        string loopName,
        GenericLoopStepBindingSelection bindingSelection)
    {
        // Loop state slots are produced by initial loop arguments or previous
        // step output. They are already evaluated and must not use ordinary
        // call-site behavior such as spread slot expansion.
        return BindEvaluatedSlotsToParameters(
            bindingContract,
            stateSlots,
            ctx,
            "loop step",
            bindingSelection,
            (required, actual) => LoopStateArityMismatch(bindingContract, required, actual, loopName),
            (required, actual) => VariadicLoopStateArityMismatch(bindingContract, required, actual, loopName));
    }

    /// <summary>
    /// Applies a unary operator to one evaluated operand value. This is the SINGLE
    /// unary application semantics and error/span policy, shared by the generic
    /// expression-spine machine, its async twin, and the planned loop evaluator's
    /// non-numeric arm, so evaluation strategies cannot drift: the empty sequence
    /// value propagates through unchanged, the string rejection is stamped with the
    /// unary expression's span, and the numeric-conversion failure
    /// (<see cref="ExpectInt"/>) is returned UNSPANNED — the innermost error's span
    /// is public structured state, so only the surrounding evaluation boundaries may
    /// attach one (<see cref="AtSpanIfMissing"/>). Lean: the <c>.unary</c> arm of
    /// <c>eval</c>.
    /// </summary>
    internal static EvalResult<Result> ApplyUnaryOperator(UnaryOp op, Result operandValue, SourceSpan? span)
    {
        // Empty result propagation through unary operators.
        if (operandValue is Result.SequenceValue(var items) && items.Count == 0)
            return EvalResult<Result>.Ok(Result.SequenceValue.TakeOwnership([]));

        if (operandValue is Result.Str)
            return new EvalError.TypeMismatch("Unary operator is not supported for strings") { Span = span };

        var vR = ExpectInt(operandValue);
        if (vR.IsError) return vR.Error;

        var value = op switch
        {
            UnaryOp.Minus => -vR.Value,
            UnaryOp.Not => vR.Value == 0 ? Decimal128.One : Decimal128.Zero,
            _ => Decimal128.Zero,
        };
        return EvalResult<Result>.Ok(new Result.Atom(value));
    }

    internal static EvalResult<Result> ApplyBinaryOperator(
        BinaryOp op,
        Expr left,
        Expr right,
        Result leftValue,
        Result rightValue,
        SourceSpan? span)
    {
        // `==` and `!=` compare KatLang values structurally across all value kinds
        // (numbers, strings, and sequence values, recursively). Different value
        // kinds compare unequal rather than raising a type mismatch. This dedicated
        // path is deliberately separate from the numeric-scalar-only validation used
        // by arithmetic and ordering operators below.
        if (op == BinaryOp.Eq)
            return EvalResult<Result>.Ok(new Result.Atom(ValueEquals(leftValue, rightValue) ? 1 : 0));
        if (op == BinaryOp.Ne)
            return EvalResult<Result>.Ok(new Result.Atom(ValueEquals(leftValue, rightValue) ? 0 : 1));

        var leftEmpty = leftValue is Result.SequenceValue(var leftItems) && leftItems.Count == 0;
        var rightEmpty = rightValue is Result.SequenceValue(var rightItems) && rightItems.Count == 0;
        if (leftEmpty || rightEmpty)
        {
            // Empty results stay transparent for the non-comparison operators.
            if (leftEmpty && rightEmpty) return EvalResult<Result>.Ok(Result.SequenceValue.TakeOwnership([]));
            if (leftEmpty) return EvalResult<Result>.Ok(rightValue);
            return EvalResult<Result>.Ok(leftValue);
        }

        if (leftValue is Result.Str && rightValue is Result.Str)
            return new EvalError.TypeMismatch("Strings only support == and != operators") { Span = span };

        if (leftValue is Result.Str || rightValue is Result.Str)
            return new EvalError.TypeMismatch("Cannot apply operator to string and non-string operands") { Span = span };

        // The operand-shape context renders the WHOLE operand trees, which is
        // quadratic over an operator chain — build it only on the error paths that
        // actually attach it (the rendered text is identical either way).
        var xR = RequireNumericScalarOperand(op, "left", leftValue);
        if (xR.IsError)
            return new EvalError.WithContext(BinaryOperandContext(op, left, right), xR.Error) { Span = span };
        var yR = RequireNumericScalarOperand(op, "right", rightValue);
        if (yR.IsError)
            return new EvalError.WithContext(BinaryOperandContext(op, left, right), yR.Error) { Span = span };
        Decimal128 x = xR.Value, y = yR.Value;
        // Division and modulo by a ZERO-VALUED divisor stay the specified KatLang
        // error (Lean: Error.divByZero) — the check is on the evaluated value, so
        // `1 / (1 - 1)`, `1 / -0`, and an underflowed-to-zero divisor all reject,
        // and the IEEE infinity/NaN outcome is deliberately NOT adopted for any of
        // them. All other arithmetic follows
        // Decimal128's IEEE semantics: overflow saturates to an infinity, and
        // non-finite operands propagate (so Infinity/Infinity is NaN, not an
        // error). The ordering comparisons are IEEE too: every comparison with a
        // NaN operand is false, and -0 equals 0.
        if ((op is BinaryOp.Div or BinaryOp.IDiv or BinaryOp.Mod) && y == 0)
            return new EvalError.DivByZero() { Span = span };

        if (op == BinaryOp.Pow)
            return EvalPow(span, x, y);

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
            BinaryOp.Eq => x == y ? 1 : 0,
            BinaryOp.Ne => x != y ? 1 : 0,
            BinaryOp.And => x != 0 && y != 0 ? 1 : 0,
            BinaryOp.Or => x != 0 || y != 0 ? 1 : 0,
            BinaryOp.Xor => (x != 0) != (y != 0) ? 1 : 0,
            _ => 0,
        };

        return EvalResult<Result>.Ok(new Result.Atom(result));
    }

    /// <summary>Evaluate an expression and coerce to a number.
    /// Lean: expectInt over eval (the model has no dedicated wrapper).</summary>
    private static EvalResult<Decimal128> EvalInt(
        Expr expr, EvalCtx ctx, IReadOnlyList<(string, Result)> valEnv)
    {
        var r = Eval(expr, ctx, valEnv);
        if (r.IsError) return r.Error;
        return ExpectInt(r.Value);
    }

    private static EvalResult<IReadOnlyList<Result>> RunStepSlots(
        Algorithm step,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        IReadOnlyList<Result> stateSlots,
        string loopName,
        PreparedGenericLoopStep prepared)
    {
        // One loop ITERATION is one charged work unit. Loops repeat work without growing
        // the host stack, so they charge work only — never depth. This is the single
        // per-iteration chokepoint shared by generic `while` and `repeat`; the optimized
        // loop paths never run under a step budget (see CreateRootCtx), so the charged
        // count is exactly the generic one.
        if (ctx.Budget.TryChargeStep() is { } limitError)
            return limitError;

        var boundR = BindLoopStepState(
            prepared.BindingContract,
            stateSlots,
            ctx,
            loopName,
            prepared.BindingSelection);
        if (boundR.IsError) return boundR.Error;

        // The concatenation must build a FRESH list per iteration: the counted
        // environment's reference identity is a zero-arg property cache key component,
        // so reusing one instance across iterations would create cross-iteration cache
        // hits the generic strategy never had.
        var stepCtx = ctx
            .WithCountedParamEnv(Concat(boundR.Value.CountedBindings, prepared.ShadowedCountedParamEnv));
        return EvalAlgOutputSlots(
            step,
            stepCtx,
            Concat(boundR.Value.ValueBindings, valEnv),
            preserveSequenceSpreadExpressionBoundaries: prepared.PreserveSequenceSpreadExpressionBoundaries);
    }

    internal static EvalResult<(IReadOnlyList<Result> NextStateSlots, Decimal128 Continue)> SplitContSlots(
        IReadOnlyList<Result> outputSlots)
    {
        if (outputSlots.Count == 0)
            return new EvalError.BadArity();

        if (outputSlots.Count == 1)
        {
            if (outputSlots[0] is Result.Atom(var number))
                return EvalResult<(IReadOnlyList<Result>, Decimal128)>.Ok((outputSlots, number));

            return new EvalError.BadArity();
        }

        var contR = ExpectInt(outputSlots[^1]);
        if (contR.IsError) return contR.Error;
        return EvalResult<(IReadOnlyList<Result>, Decimal128)>.Ok((outputSlots.Take(outputSlots.Count - 1).ToList(), contR.Value));
    }

    // ── Builtins ─────────────────────────────────────────────────────────────
    // There is deliberately NO plain builtin dispatch function:
    // ApplyBuiltinCountedResolved is the ONE builtin dispatch switch
    // (sequence-builtin metadata routing plus the if/while/repeat/atoms/range
    // arms), and every plain spelling reaches it through the counted call
    // family plus the value projection. (Lean keeps the named projection
    // `applyBuiltinResolved` because CoreTests guards address it directly;
    // the C# equivalent would have no caller at all.)

    private static EvalResult<CountedResult> WhileLoopCounted(
        Algorithm step,
        IReadOnlyList<Result> initialStateSlots,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        ctx.LoopDiagnostics?.RecordLoopExecution();

        if (!ctx.EnableLoopOptimization)
        {
            ctx.LoopDiagnostics?.RecordOptimizedLoopFallback("loop optimization disabled");
            return WhileLoopGenericCounted(step, initialStateSlots, ctx, valEnv);
        }

        if (!IsOptimizedLoopShapeEligible(step, out var fallbackReason))
        {
            ctx.LoopDiagnostics?.RecordOptimizedLoopFallback(fallbackReason!);
            return WhileLoopGenericCounted(step, initialStateSlots, ctx, valEnv);
        }

        if (initialStateSlots.Any(static slot => slot is not Result.Atom))
        {
            ctx.LoopDiagnostics?.RecordOptimizedLoopFallback("non-scalar loop state slot");
            return WhileLoopGenericCounted(step, initialStateSlots, ctx, valEnv);
        }

        if (step.Params.Count != initialStateSlots.Count)
            return LoopStateArityMismatch(step, step.Params.Count, initialStateSlots.Count, "while");

        return LoopOptimizer.TryEvaluateWhile(
            step,
            initialStateSlots,
            ctx,
            valEnv,
            fallbackStateSlots => WhileLoopGenericCounted(step, fallbackStateSlots, ctx, valEnv),
            out var optimizedResult)
            ? optimizedResult
            : WhileLoopGenericCounted(step, initialStateSlots, ctx, valEnv);
    }

    private static EvalResult<CountedResult> WhileLoopGenericCounted(
        Algorithm step,
        IReadOnlyList<Result> initialStateSlots,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // `while` always runs its step at least once, so the loop-invariant step
        // binding is prepared unconditionally — once per loop invocation, not per
        // iteration.
        var prepared = PrepareGenericLoopStep(step, ctx);
        var stateSlots = initialStateSlots.ToList();
        while (true)
        {
            var outputSlotsR = RunStepSlots(step, ctx, valEnv, stateSlots, "while", prepared);
            if (outputSlotsR.IsError) return outputSlotsR.Error;
            var splitR = SplitContSlots(outputSlotsR.Value);
            if (splitR.IsError) return splitR.Error;
            var (nextStateSlots, cont) = splitR.Value;
            if (cont == 0) return MakeCheckedLoopStateResult(ctx, stateSlots);
            stateSlots = nextStateSlots.ToList();
        }
    }

    private static EvalResult<CountedResult> RepeatLoopCounted(
        Algorithm step,
        long count,
        IReadOnlyList<Result> initialStateSlots,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        ctx.LoopDiagnostics?.RecordLoopExecution();

        if (count == 0)
            return MakeCheckedLoopStateResult(ctx, initialStateSlots);

        if (!ctx.EnableLoopOptimization)
        {
            ctx.LoopDiagnostics?.RecordOptimizedLoopFallback("loop optimization disabled");
            return RepeatLoopGenericCounted(step, count, initialStateSlots, ctx, valEnv);
        }

        if (!IsOptimizedLoopShapeEligible(step, out var fallbackReason))
        {
            ctx.LoopDiagnostics?.RecordOptimizedLoopFallback(fallbackReason!);
            return RepeatLoopGenericCounted(step, count, initialStateSlots, ctx, valEnv);
        }

        if (initialStateSlots.Any(static slot => slot is not Result.Atom))
        {
            ctx.LoopDiagnostics?.RecordOptimizedLoopFallback("non-scalar loop state slot");
            return RepeatLoopGenericCounted(step, count, initialStateSlots, ctx, valEnv);
        }

        if (step.Params.Count != initialStateSlots.Count)
            return LoopStateArityMismatch(step, step.Params.Count, initialStateSlots.Count, "repeat");

        return LoopOptimizer.TryEvaluateRepeat(
            step,
            count,
            initialStateSlots,
            ctx,
            valEnv,
            (remainingCount, fallbackStateSlots) => RepeatLoopGenericCounted(step, remainingCount, fallbackStateSlots, ctx, valEnv),
            out var optimizedResult)
            ? optimizedResult
            : RepeatLoopGenericCounted(step, count, initialStateSlots, ctx, valEnv);
    }

    private static EvalResult<CountedResult> RepeatLoopGenericCounted(
        Algorithm step,
        long count,
        IReadOnlyList<Result> initialStateSlots,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var stateSlots = initialStateSlots.ToList();
        // A zero-iteration repeat never binds its step, so it must not gain step
        // preparation either (every current caller already short-circuits count 0
        // before reaching this loop; the guard keeps that contract local).
        if (count <= 0)
            return MakeCheckedLoopStateResult(ctx, stateSlots);

        var prepared = PrepareGenericLoopStep(step, ctx);
        // The counter is a LONG like `count` itself. An `int` counter silently wraps past
        // int.MaxValue and never satisfies `k < count` again, so a repeat count above
        // 2^31 - 1 (legal: the count is narrowed from Decimal128 to long) would spin
        // forever instead of finishing. Pinned structurally at both mirror sites by
        // EvaluatorLoopTests.RepeatLoopGenericCounter_IsLongAtBothMirrorSites.
        for (var k = 0L; k < count; k++)
        {
            var outputSlotsR = RunStepSlots(step, ctx, valEnv, stateSlots, "repeat", prepared);
            if (outputSlotsR.IsError) return outputSlotsR.Error;
            stateSlots = outputSlotsR.Value.ToList();
        }
        return MakeCheckedLoopStateResult(ctx, stateSlots);
    }
}
