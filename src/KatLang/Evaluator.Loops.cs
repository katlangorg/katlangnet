using System.Collections;
using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

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
    /// items. Redundant empty-sequence nesting has already normalized to <c>()</c>.
    /// User-defined algorithms may exist structurally without output, but forcing
    /// them in value position raises <see cref="EvalError.MissingOutput"/>.
    /// Lean: evalAlgOutput → EvalM Result.
    /// </summary>
    private static EvalResult<Result> EvalAlgOutputCore(
        Algorithm alg,
        EvalCtx ctx,
        ValEnv valEnv)
        => ProjectCountedValue(EvalAlgOutputCountedCore(alg, ctx, valEnv));

    /// <summary>
    /// Evaluate a root program algorithm when a result is requested. The root is demanded
    /// for its value with NOTHING supplied, so it goes through the ONE zero-argument
    /// demand funnel (<see cref="EvalZeroArgumentDemandOutput"/>): a root declaring no
    /// parameter pattern is its output exactly as before, and a root whose parameter list
    /// accepts an EMPTY supply (a collecting-only host-built root) binds that supply
    /// first. Lean: <c>evalProgramOutput</c>.
    /// </summary>
    private static EvalResult<Result> EvalProgramOutput(
        Algorithm alg,
        EvalCtx ctx,
        ValEnv valEnv)
        => EvalZeroArgumentDemandOutput(alg, ctx, valEnv);

    /// <summary>
    /// The ROW SUPPLY of an algorithm's output — what a loop step's rows make the next
    /// state (LOOP-03, VAL-07 applied to a step). Every output row is evaluated once, left
    /// to right; a NON-spread row supplies exactly one item (its value, <c>()</c> included —
    /// a surface row's emitted count is at most one, since every result, a completed
    /// <c>while</c>/<c>repeat</c> included, is a value boundary: Q-26), and a spread row
    /// <c>e*</c> supplies its spread items, possibly none. The supply depends on the rows
    /// alone: no parameter-pattern category is consulted (Q-24 retired the former
    /// pattern-triggered packing of a spread row), so <c>(a, b)</c> is one item and
    /// <c>(a, b)*</c> two in every step. Lean: <c>evalAlgOutputSlots</c>.
    /// <para>A builtin has no written rows, so its value is ONE row (LOOP-03, Q-23) — never a
    /// re-counted top-level supply, which would read a <c>()</c> result as zero slots. A builtin
    /// loop step never reaches this arm (<see cref="InvokeLoopStepSupply"/> invokes it over the
    /// state supply); only a host-built clause body that IS a builtin does, read with nothing
    /// supplied exactly as the ordinary family call reads it.</para>
    /// </summary>
    private static EvalResult<IReadOnlyList<Result>> EvalAlgOutputSlots(
        Algorithm alg,
        EvalCtx ctx,
        ValEnv valEnv,
        IReadOnlyList<string>? parameterNames = null)
    {
        if (alg is Algorithm.Builtin(var builtin))
        {
            var countedR = EvalBuiltinValueCounted(builtin);
            return countedR.IsError
                ? countedR.Error
                : EvalResult<IReadOnlyList<Result>>.Ok([countedR.Value.Value]);
        }

        if (alg.FindDuplicatePropName() is { } duplicateName)
            return new EvalError.DuplicateProperty(duplicateName);

        if (ConditionalValueAccessError("conditional", alg) is { } conditionalError)
            return conditionalError;

        if (alg is Algorithm.User { Output.Count: 0 })
            return new EvalError.MissingOutput();

        var slots = new List<Result>();
        var pushedCtx = EnterAlgorithmBody(alg, ctx, valEnv, parameterNames);
        foreach (var expr in alg.Output)
        {
            var countedR = EvalCounted(expr, pushedCtx, valEnv);
            if (countedR.IsError) return countedR.Error;

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
            parameterPatterns.Any(static pattern => pattern is CaptureParameterPattern { Kind: ParameterKind.Collecting })
                ? new VariadicLoopStateBindingContext(loopName,
                    parameterPatterns.Where(static pattern => pattern is not CaptureParameterPattern { Kind: ParameterKind.Collecting }).Select(static pattern => pattern.DisplayName).ToList(),
                    expectedStateValueCount, actualStateValueCount)
                : new LoopStateBindingContext(loopName,
                    parameterPatterns.Select(static pattern => pattern.DisplayName).ToList(), actualStateValueCount),
            new EvalError.ArityMismatch(expectedStateValueCount, actualStateValueCount)
            {
                InferredImplicitParameters = ImplicitParameterProvenance.CollectFrom(parameters),
            });

    /// <summary>
    /// Applies a unary operator to one evaluated operand value. This is the SINGLE
    /// unary application semantics and error/span policy, shared by the generic
    /// expression-spine machine, its async twin, and the planned loop evaluator's
    /// non-numeric arm, so evaluation strategies cannot drift: the empty sequence value
    /// follows ordinary numeric-conversion validation (SYN-01), and BOTH operand
    /// rejections — the string rejection and the numeric-conversion failure of
    /// <see cref="ExpectInt"/> (a multi-item or empty sequence value, or a list value:
    /// <see cref="EvalError.BadArity"/>) — carry the unary expression's span, exactly as
    /// the binary operators attach their expression span to an operand rejection. The
    /// innermost error's span is public structured state, so it is attached HERE, at the
    /// one unary application site, and the surrounding evaluation boundaries never
    /// overwrite it (<see cref="AtSpanIfMissing"/>). Lean: <c>evalUnaryCounted</c>
    /// (spans are C#-only diagnostic metadata; the error kind is unchanged).
    /// </summary>
    internal static EvalResult<Result> ApplyUnaryOperator(UnaryOp op, Result operandValue, SourceSpan? span)
    {
        // `not` is the Boolean negation and REQUIRES a Boolean operand: a number has no
        // truth value, so every non-Boolean operand kind is the one value-kind error
        // naming the operand. Lean: evalUnaryCounted's `.not` arm.
        if (op == UnaryOp.Not)
        {
            var flag = operandValue.AsBool();
            return flag is not null
                ? EvalResult<Result>.Ok(new Result.Bool(!flag.Value))
                : new EvalError.TypeMismatch(
                    $"operator `not` expects a Boolean operand, but the operand was {DescribeOperand(operandValue)}")
                { Span = span };
        }

        if (operandValue is Result.Str)
            return new EvalError.TypeMismatch("Unary operator is not supported for strings") { Span = span };

        // `-` is numeric negation: a Boolean operand is a value-kind error, every other
        // non-numeric operand keeps the numeric-conversion failure of ExpectInt.
        if (operandValue is Result.Bool)
        {
            return new EvalError.TypeMismatch(
                $"operator `-` expects a numeric scalar operand, but the operand was {DescribeOperand(operandValue)}")
            { Span = span };
        }

        var vR = ExpectInt(operandValue);
        if (vR.IsError) return AtSpanIfMissing(vR.Error, span);

        return EvalResult<Result>.Ok(new Result.Atom(-vR.Value));
    }

    /// <summary>
    /// Applies ONE binary (arithmetic or logical) operator to two evaluated operand
    /// values: the SINGLE binary application semantics and error/span policy shared by
    /// the generic expression-spine machine, its async twin, and the planned loop
    /// evaluator. Comparisons are NOT binary operators — every comparison is a link of a
    /// comparison chain and applies through <see cref="ApplyComparison"/>.
    /// Lean: <c>evalBinaryCounted</c>.
    /// </summary>
    internal static EvalResult<Result> ApplyBinaryOperator(
        BinaryOp op,
        Expr left,
        Expr right,
        Result leftValue,
        Result rightValue,
        SourceSpan? span)
    {
        // The logical operators are Boolean-only: both operands were evaluated left to
        // right before this point (the established evaluation order — no short circuit),
        // and each must be a Boolean value; there is no numeric truthiness, so `1 and 2`
        // is a value-kind error. Lean: evalBinaryCounted's `.and | .or | .xor` arm.
        if (op is BinaryOp.And or BinaryOp.Or or BinaryOp.Xor)
        {
            var leftFlagR = RequireBooleanOperand(op, "left", leftValue);
            if (leftFlagR.IsError)
                return new EvalError.WithContext(BinaryOperandContext(op, left, right), leftFlagR.Error) { Span = span };
            var rightFlagR = RequireBooleanOperand(op, "right", rightValue);
            if (rightFlagR.IsError)
                return new EvalError.WithContext(BinaryOperandContext(op, left, right), rightFlagR.Error) { Span = span };
            bool a = leftFlagR.Value, b = rightFlagR.Value;
            var flag = op switch
            {
                BinaryOp.And => a && b,
                BinaryOp.Or => a || b,
                _ => a != b,
            };
            return EvalResult<Result>.Ok(new Result.Bool(flag));
        }

        // SYN-01: the empty sequence value is NOT an identity for scalar operators.
        // `()` is an ordinary operand here — it carries no numeric scalar value, so
        // it reaches the string contract and the numeric-scalar validation below
        // exactly like `(1, 2)` or `[]`, and `10 / ()`, `() > 10`, `() and 7`, and
        // `() + 'text'` are operand errors rather than a passthrough of the other
        // operand. Empty NEUTRALITY is a property of the arity algebra's SUPPLY
        // operations (capture/collect/spread), never of scalar operators.
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
        // NaN operand is false, and -0 equals 0. `div` is the ONE shared
        // Decimal128Numerics.IntegerDivide (G-3): the exact quotient rounded toward
        // zero to a Decimal128 integer — never `Truncate(x / y)`, whose quotient is
        // rounded to 34 digits BEFORE truncation and can land on the wrong neighbor
        // — so the planned loop arm (LoopExprPlan.ApplyPlannedNumericBinary), the
        // async twin (which reaches this method), and this arm cannot drift.
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
            BinaryOp.IDiv => Decimal128Numerics.IntegerDivide(x, y),
            BinaryOp.Mod => x % y,
            // The logical operators are handled above and `^` by EvalPow.
            _ => 0,
        };

        return EvalResult<Result>.Ok(new Result.Atom(result));
    }

    /// <summary>
    /// Applies ONE LINK of a comparison chain — <c>leftValue op rightValue</c>, the two
    /// ADJACENT operands the link compares — the SINGLE comparison semantics and
    /// error/span policy shared by the generic expression-spine machine, its async twin,
    /// and the planned loop evaluator, so evaluation strategies cannot drift. <c>==</c>
    /// and <c>!=</c> compare KatLang values structurally across all value kinds
    /// (numbers, Booleans, strings, sequence values, and lists, recursively): different
    /// kinds compare unequal rather than raising a type mismatch (<c>true == 1</c> is
    /// false), so equality is total and never fails. The ordering operators reject
    /// strings and then require numeric scalar operands (a Boolean operand is rejected —
    /// Booleans are not ordered), each rejection carrying the operand-shape context of
    /// THIS link (<c>while evaluating `2 &lt; true`</c>, never a nested binary spelling of
    /// the chain) and the link's span: the hull of its two operands' spans, or the
    /// chain's own span when an operand is unpositioned. Lean: <c>applyComparison</c>.
    /// </summary>
    internal static EvalResult<bool> ApplyComparison(
        ComparisonOp op,
        Expr left,
        Expr right,
        Result leftValue,
        Result rightValue,
        SourceSpan? chainSpan)
    {
        if (op == ComparisonOp.Eq)
            return EvalResult<bool>.Ok(ValueEquals(leftValue, rightValue));
        if (op == ComparisonOp.Ne)
            return EvalResult<bool>.Ok(!ValueEquals(leftValue, rightValue));

        // SYN-01: `()` is an ordinary non-scalar operand here too — it reaches the
        // string contract and the numeric-scalar validation exactly like `(1, 2)`.
        if (leftValue is Result.Str && rightValue is Result.Str)
            return new EvalError.TypeMismatch("Strings only support == and != operators") { Span = ComparisonLinkSpan(left, right, chainSpan) };

        if (leftValue is Result.Str || rightValue is Result.Str)
            return new EvalError.TypeMismatch("Cannot apply operator to string and non-string operands") { Span = ComparisonLinkSpan(left, right, chainSpan) };

        // The operand-shape context renders the two operand trees — built only on the
        // error paths that attach it, like the binary operators.
        var xR = RequireNumericScalarOperand(op, "left", leftValue);
        if (xR.IsError)
            return new EvalError.WithContext(ComparisonLinkContext(op, left, right), xR.Error) { Span = ComparisonLinkSpan(left, right, chainSpan) };
        var yR = RequireNumericScalarOperand(op, "right", rightValue);
        if (yR.IsError)
            return new EvalError.WithContext(ComparisonLinkContext(op, left, right), yR.Error) { Span = ComparisonLinkSpan(left, right, chainSpan) };

        // The ordering comparisons take numeric scalar operands only and are IEEE:
        // every comparison with a NaN operand is false, -0 equals 0.
        return EvalResult<bool>.Ok(TryCompareNumeric(op, xR.Value, yR.Value)!.Value);
    }

    /// <summary>
    /// The span of one comparison link: the hull of its two operands' spans — the
    /// failing link of <c>1 &lt; 2 &lt; true</c> is located at <c>2 &lt; true</c> — falling
    /// back to the chain's own span when an operand is unpositioned (host trees).
    /// </summary>
    internal static SourceSpan? ComparisonLinkSpan(Expr left, Expr right, SourceSpan? chainSpan)
        => left.Span is { } leftSpan && right.Span is { } rightSpan
            ? leftSpan.Union(rightSpan)
            : chainSpan;

    /// <summary>
    /// The ONE numeric ordering comparison (IEEE: every comparison with a NaN operand is
    /// false, -0 equals 0), shared by the generic comparison and the planned loop arm so
    /// the two cannot drift; <c>null</c> for <c>==</c>/<c>!=</c>, which are structural
    /// equality (<see cref="ValueEquals"/>), never a numeric comparison.
    /// </summary>
    internal static bool? TryCompareNumeric(ComparisonOp op, Decimal128 x, Decimal128 y) => op switch
    {
        ComparisonOp.Lt => x < y,
        ComparisonOp.Gt => x > y,
        ComparisonOp.Le => x <= y,
        ComparisonOp.Ge => x >= y,
        _ => null,
    };

    private static EvalResult<IReadOnlyList<Result>> RunStepSlots(
        Algorithm step,
        EvalCtx ctx,
        ValEnv valEnv,
        IReadOnlyList<Result> stateSlots,
        string loopName,
        CallDiagnosticName stepName,
        PreparedGenericLoopStep prepared)
        => RunReadyNeedStepSlots(step, stateSlots, ctx, valEnv, loopName, stepName, prepared, asynchronous: false).GetAwaiter().GetResult();

    /// <summary>
    /// Split a loop step output into next state slots and the continuation flag. The
    /// step's LAST output is the flag and must be a Boolean value (<c>true</c> continues,
    /// <c>false</c> stops); a number, string, sequence, or list there is a value-kind
    /// error, never a truth test. A single-output step keeps the established shape — its
    /// one slot is both the next state and the flag — so it must be Boolean too.
    /// Lean: <c>splitContSlots</c>.
    /// </summary>
    internal static EvalResult<(IReadOnlyList<Result> NextStateSlots, bool Continue)> SplitContSlots(
        IReadOnlyList<Result> outputSlots)
    {
        if (outputSlots.Count == 0)
            return new EvalError.BadArity();

        if (outputSlots.Count == 1)
        {
            var flag = outputSlots[0].AsBool();
            return flag is not null
                ? EvalResult<(IReadOnlyList<Result>, bool)>.Ok((outputSlots, flag.Value))
                : new EvalError.TypeMismatch(BooleanRequiredMessage(WhileContinuationFlagRole, outputSlots[0]));
        }

        var last = outputSlots[^1];
        var cont = last.AsBool();
        if (cont is null)
            return new EvalError.TypeMismatch(BooleanRequiredMessage(WhileContinuationFlagRole, last));
        return EvalResult<(IReadOnlyList<Result>, bool)>.Ok((outputSlots.Take(outputSlots.Count - 1).ToList(), cont.Value));
    }

    // ── Builtins ─────────────────────────────────────────────────────────────
    // There is deliberately NO plain builtin dispatch function:
    // ApplyBuiltinCountedResolved is the ONE builtin dispatch switch
    // (sequence-builtin metadata routing plus the if/while/repeat/atoms/range
    // arms), and every plain spelling reaches it through the counted call
    // family plus the value projection. (Lean keeps the named projection
    // `applyBuiltinResolved` because CoreTests guards address it directly;
    // the C# equivalent would have no caller at all.)

    private static EvalResult<CountedResult> WhileLoopGenericCounted(
        Algorithm step,
        IReadOnlyList<Result> initialStateSlots,
        EvalCtx ctx,
        ValEnv valEnv,
        CallDiagnosticName stepName)
    {
        // `while` always runs its step at least once, so the loop-invariant step
        // binding is prepared unconditionally — once per loop invocation, not per
        // iteration.
        var prepared = PrepareUserLoopStep(step, ctx);
        var stateSlots = initialStateSlots.ToList();
        while (true)
        {
            var outputSlotsR = RunStepSlots(step, ctx, valEnv, stateSlots, "while", stepName, prepared);
            if (outputSlotsR.IsError) return outputSlotsR.Error;
            var splitR = SplitContSlots(outputSlotsR.Value);
            if (splitR.IsError) return splitR.Error;
            var (nextStateSlots, cont) = splitR.Value;
            if (!cont) return MakeCheckedLoopStateResult(ctx, stateSlots);
            stateSlots = nextStateSlots.ToList();
        }
    }

    private static EvalResult<CountedResult> RepeatLoopGenericCounted(
        Algorithm step,
        long count,
        IReadOnlyList<Result> initialStateSlots,
        EvalCtx ctx,
        ValEnv valEnv,
        CallDiagnosticName stepName)
    {
        var stateSlots = initialStateSlots.ToList();
        // A zero-iteration repeat never binds its step, so it must not gain step
        // preparation either (every current caller already short-circuits count 0
        // before reaching this loop; the guard keeps that contract local).
        if (count <= 0)
            return MakeCheckedLoopStateResult(ctx, stateSlots);

        var prepared = PrepareUserLoopStep(step, ctx);
        // The counter is a LONG like `count` itself. An `int` counter silently wraps past
        // int.MaxValue and never satisfies `k < count` again, so a repeat count above
        // 2^31 - 1 (legal: the count is narrowed from Decimal128 to long) would spin
        // forever instead of finishing. Pinned structurally at both mirror sites by
        // EvaluatorLoopTests.RepeatLoopGenericCounter_IsLongAtBothMirrorSites.
        for (var k = 0L; k < count; k++)
        {
            var outputSlotsR = RunStepSlots(step, ctx, valEnv, stateSlots, "repeat", stepName, prepared);
            if (outputSlotsR.IsError) return outputSlotsR.Error;
            stateSlots = outputSlotsR.Value.ToList();
        }
        return MakeCheckedLoopStateResult(ctx, stateSlots);
    }
}
