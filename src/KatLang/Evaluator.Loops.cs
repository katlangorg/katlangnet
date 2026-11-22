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
    /// The ROW SUPPLY of an algorithm's output — what a loop step's rows make the next
    /// state (LOOP-03, VAL-07 applied to a step). Every output row is formed once, left
    /// to right (<see cref="AddOutputRowItems"/>, the one row rule): a NON-spread row supplies
    /// exactly one item (its value, <c>()</c> included — a surface row's emitted count is at
    /// most one, since every result, a completed <c>while</c>/<c>repeat</c> included, is a
    /// value boundary: Q-26), and a spread row <c>e*</c> supplies its spread items, possibly
    /// none. The supply depends on the rows alone: no parameter-pattern category is consulted
    /// (Q-24 retired the former pattern-triggered packing of a spread row), so <c>(a, b)</c> is
    /// one item and <c>(a, b)*</c> two in every step. This is the <c>repeat</c> receiver's
    /// reading; a <c>while</c> round reads the same rows in its own order
    /// (<see cref="EvalWhileVerdictSlots"/>, LOOP-06). Lean: <c>evalAlgOutputSlots</c>.
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

        if (OutputRowsAccessError(alg, ctx) is { } accessError)
            return accessError;

        var slots = new List<Result>();
        TransientSupply bound = default;
        SourceSpan? overflowAt = null;
        // A loop round is an actual call of the step (the one caller is the step invocation): its
        // activation owns the round's inner bindings.
        var pushedCtx = EnterAlgorithmBody(alg, ctx, valEnv, parameterNames, invoked: true);
        foreach (var expr in alg.Output)
        {
            var countedR = EvalCounted(expr, pushedCtx, valEnv);
            if (countedR.IsError) return countedR.Error;
            AddOutputRowItems(slots, expr, countedR.Value, ctx.Budget, ref bound, ref overflowAt);
        }

        return bound.Overflowed
            ? RefuseTransientSupply(ctx.Budget, bound, overflowAt)
            : EvalResult<IReadOnlyList<Result>>.Ok(slots);
    }

    /// <summary>
    /// ONE <c>while</c> round's reading of a step body's rows (LOOP-06, condition first —
    /// LOOP-CF1, October 2026). FLAG DISCOVERY forms the rows from the LAST row backwards, each
    /// row one complete ordinary formation (<see cref="AddOutputRowItems"/>, the row rule the
    /// supply reader uses), until a row supplies at least one item; that row's LAST item is the
    /// continuation flag (<see cref="ContinuationFlag"/>). A <c>false</c> flag ends the loop
    /// (<c>null</c>): the remaining earlier rows are never formed. A <c>true</c> flag forms the
    /// remaining rows LEFT TO RIGHT, and the next state is the whole supply in written order
    /// without its last item — a one-item supply is both the state and the flag. Each row is
    /// formed at most once, in the one activation (<see cref="EnterAlgorithmBody"/>), so the
    /// flag row and the transition rows share parameter cells and local-property caches; a
    /// call or spread inside a row stays one ordinary value (row granularity). No row supplies
    /// an item: the missing-flag <c>BadArity</c>. Lean: <c>whileVerdictSlots</c>.
    /// </summary>
    private static EvalResult<IReadOnlyList<Result>?> EvalWhileVerdictSlots(
        Algorithm alg,
        EvalCtx ctx,
        ValEnv valEnv,
        IReadOnlyList<string>? parameterNames = null)
    {
        if (alg is Algorithm.Builtin(var builtin))
        {
            var countedR = EvalBuiltinValueCounted(builtin);
            return countedR.IsError ? countedR.Error : WhileVerdictOfSupply([countedR.Value.Value]);
        }

        if (OutputRowsAccessError(alg, ctx) is { } accessError)
            return accessError;

        var rows = alg.Output;
        var slots = new List<Result>(rows.Count);
        var pushedCtx = EnterAlgorithmBody(alg, ctx, valEnv, parameterNames, invoked: true);
        // Discovery: every row right of the flag row supplied nothing, so `slots` holds exactly
        // the flag row's items once one is found.
        var flagRow = rows.Count - 1;
        CountedResult flagRowValue = default;
        TransientSupply discovery = default;
        SourceSpan? overflowAt = null;
        for (; flagRow >= 0; flagRow--)
        {
            var countedR = EvalCounted(rows[flagRow], pushedCtx, valEnv);
            if (countedR.IsError) return countedR.Error;
            AddOutputRowItems(slots, rows[flagRow], countedR.Value, ctx.Budget, ref discovery, ref overflowAt);
            // A flag row whose items alone pass the ceiling cannot be read (SEC-01).
            if (discovery.Overflowed)
                return RefuseTransientSupply(ctx.Budget, discovery, overflowAt);
            if (slots.Count != 0)
            {
                flagRowValue = countedR.Value;
                break;
            }
        }

        if (flagRow < 0)
            return new EvalError.WithContext(WhileStepWithoutFlagContext, new EvalError.BadArity());
        var flag = ContinuationFlagOfRow(rows[flagRow], slots[^1]);
        if (flag.IsError) return flag.Error;
        if (!flag.Value) return EvalResult<IReadOnlyList<Result>?>.Ok(null);

        if (flagRow > 0)
        {
            slots.Clear();
            TransientSupply bound = default;
            for (var i = 0; i < flagRow; i++)
            {
                var countedR = EvalCounted(rows[i], pushedCtx, valEnv);
                if (countedR.IsError) return countedR.Error;
                AddOutputRowItems(slots, rows[i], countedR.Value, ctx.Budget, ref bound, ref overflowAt);
            }
            // The flag row's already formed value, re-read (never re-formed) in written order.
            AddOutputRowItems(slots, rows[flagRow], flagRowValue, ctx.Budget, ref bound, ref overflowAt);
            if (bound.Overflowed)
                return RefuseTransientSupply(ctx.Budget, bound, overflowAt);
        }

        return EvalResult<IReadOnlyList<Result>?>.Ok(WhileNextStateSlots(slots));
    }

    /// <summary>
    /// The access failures of an algorithm read as output rows (both row readers and their
    /// async mirrors): a duplicate property, a conditional read without call arguments, and a
    /// user algorithm without written output. The context is passed by reference, so the body-entry frames
    /// that ask (recursion spines) hold no copy of its budget.
    /// </summary>
    private static EvalError? OutputRowsAccessError(Algorithm alg, in EvalCtx ctx)
    {
        if (DuplicatePropertyName(alg, ctx.Budget) is { } duplicateName)
            return new EvalError.DuplicateProperty(duplicateName);
        if (ConditionalValueAccessError("conditional", alg) is { } conditionalError)
            return conditionalError;
        return alg is Algorithm.User { Output.Count: 0 } ? new EvalError.MissingOutput() : null;
    }

    /// <summary>
    /// The runtime duplicate-property check of a body evaluation (Lean <c>Algorithm.findDuplicatePropName</c>,
    /// total: <c>none</c> for a builtin or a family, whose property list is empty): host-API defense, since the
    /// front end rejects a duplicate property before evaluation. Every evaluator site that enters a body asks
    /// it here. A short list keeps the allocation-free pairwise scan
    /// (<see cref="AlgorithmAccessors.FirstDuplicatePropertyName"/>); a wide one is decided once per run per
    /// list (<see cref="PropertyBindingIndexCache.FirstDuplicateName"/>), so repeated evaluation of a wide body
    /// builds no name set per evaluation. Out of line, so the body-entry frames that ask it keep no scan state.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    internal static string? DuplicatePropertyName(Algorithm alg, EvaluationBudget budget)
    {
        var properties = alg.Properties;
        return properties.Count <= AlgorithmAccessors.LinearDuplicatePropertyScanLimit
            ? AlgorithmAccessors.FirstDuplicatePropertyName(properties)
            : budget.PropertyBindings.FirstDuplicateName(properties);
    }

    /// <summary>
    /// What ONE formed output row contributes to its algorithm's row supply (LOOP-03): a spread
    /// row its spread items, possibly none; a non-spread row exactly one item, its value
    /// (<c>()</c> included). The one row rule of both row readers
    /// (<see cref="EvalAlgOutputSlots"/>, <see cref="EvalWhileVerdictSlots"/> and their async
    /// mirrors). Lean: <c>OutputRows.items</c>.
    /// <para>The row supply is transient-bounded (SEC-01, <see cref="TransientSupply"/>): the row's
    /// items are admitted into <paramref name="supply"/> before they are appended — a spread or
    /// multi-item row subjects the whole supply, including plain rows, to the ceiling — and the
    /// row that overflows the supply is recorded in
    /// <paramref name="overflowAt"/>; the readers refuse an overflowed supply once its rows are
    /// formed (<see cref="RefuseTransientSupply"/>). The planned loop's handover applies the same
    /// rule to the same rows (<c>LoopOptimizer.MaterializeGenericHandoverSlots</c>).</para>
    /// </summary>
    private static void AddOutputRowItems(
        List<Result> into, Expr row, CountedResult formed, EvaluationBudget budget, ref TransientSupply supply, ref SourceSpan? overflowAt)
    {
        var overflowed = supply.Overflowed;
        if (row is Expr.SequenceSpread || formed.EmittedCount != 0)
            AddCountedTopLevelValuesBounded(into, formed, budget, ref supply, expansion: row is Expr.SequenceSpread || formed.EmittedCount > 1);
        else
            AddSlotBounded(into, formed.Value, budget, ref supply);
        if (supply.Overflowed && !overflowed)
            overflowAt = row.Span;
    }

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
        // Each failure publishes its OWN name list, as the list built here always was: a context
        // record compares its list by reference, so two independently produced failures stay
        // unequal and a `with` copy stays equal. `OverList` is that distinct read-only view even
        // for no names (a zero-parameter step); `Over` would hand every such failure the one
        // shared empty view and make their records equal.
        => new EvalError.WithContext(
            parameterPatterns.Any(static pattern => pattern is CaptureParameterPattern { Kind: ParameterKind.Collecting })
                ? new VariadicLoopStateBindingContext(loopName,
                    SafeReadOnlyCollection.OverList(parameterPatterns.Where(static pattern => pattern is not CaptureParameterPattern { Kind: ParameterKind.Collecting }).Select(static pattern => pattern.DisplayName).ToArray()),
                    expectedStateValueCount, actualStateValueCount)
                : new LoopStateBindingContext(loopName,
                    SafeReadOnlyCollection.OverList(parameterPatterns.Select(static pattern => pattern.DisplayName).ToArray()), actualStateValueCount),
            new EvalError.ArityMismatch(expectedStateValueCount, actualStateValueCount)
            {
                InferredImplicitParameters = ImplicitParameterProvenance.CollectFrom(parameters),
            });

    /// <summary>
    /// Applies a unary operator to one evaluated operand value. This is the SINGLE
    /// unary application semantics and error/span policy, shared by the generic
    /// expression-spine machine, its async twin, and the planned loop evaluator's
    /// non-numeric arm, so evaluation strategies cannot drift: the empty sequence value
    /// is an ordinary non-numeric operand (SYN-01), and EVERY operand rejection — the ONE
    /// value-kind failure of every non-numeric operand of `-` (a string, a Boolean, a
    /// multi-item or empty sequence value, or a list value: one
    /// <see cref="EvalError.TypeMismatch"/> naming the operator and the operand, Q-27) and
    /// the non-Boolean operand of `not` — carries the unary expression's span, exactly as
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

        // `-` is numeric negation: every non-numeric operand — a string, a Boolean, a sequence
        // (`()` included) or a list — is the one value-kind error naming the operand (Q-27).
        if (operandValue.AsNum() is not { } number)
        {
            return new EvalError.TypeMismatch(
                $"operator `-` expects a numeric scalar operand, but the operand was {DescribeOperand(operandValue)}")
            { Span = span };
        }

        return EvalResult<Result>.Ok(new Result.Atom(-number));
    }

    /// <summary>
    /// THE SHORT-CIRCUIT DECISION of <c>and</c> / <c>or</c>: whether the LEFT operand's Boolean
    /// alone decides the operator — <c>false and _</c> is <c>false</c> and <c>true or _</c> is
    /// <c>true</c> — so that the right operand is NOT evaluated. <c>xor</c> needs both operands
    /// whatever the left one is, and so does every arithmetic operator.
    /// Lean: <c>BinaryOp.leftOperandDecides</c>.
    /// </summary>
    internal static bool LeftOperandDecides(BinaryOp op, bool left)
        => op switch
        {
            BinaryOp.And => !left,
            BinaryOp.Or => left,
            _ => false,
        };

    /// <summary>
    /// THE POST-LEFT DECISION of a binary operator: what the expression is once its LEFT operand
    /// has a value, made BEFORE the right operand is scheduled. It is the single short-circuit
    /// rule of <c>and</c> / <c>or</c>, shared by every route that chooses which operand to
    /// evaluate — the generic expression-spine machine, its async twin, and the planned loop
    /// evaluator — so the strategies cannot drift:
    /// <list type="bullet">
    ///   <item><c>null</c>: the right operand is needed. Always the answer for <c>xor</c> and the
    ///   arithmetic operators, and for <c>and</c> / <c>or</c> when the left operand is a Boolean
    ///   that does not decide (<see cref="LeftOperandDecides"/>). The route then evaluates the
    ///   right operand once and applies <see cref="ApplyBinaryOperator"/>.</item>
    ///   <item>a value: the left operand decided <c>and</c> / <c>or</c>. The route completes
    ///   with it and never evaluates the right operand, which therefore has no effect, failure,
    ///   suspension or charge, and whose value kind is never checked.</item>
    ///   <item>an error: the left operand of <c>and</c> / <c>or</c> is not a Boolean — the
    ///   ordinary operand rejection (<see cref="RequireLogicalOperand"/>), reported before any
    ///   right operand work.</item>
    /// </list>
    /// Lean: the <c>.and | .or</c> arm of <c>evalBinaryCounted</c>.
    /// </summary>
    internal static EvalResult<Result>? DecideLogicalAfterLeftOperand(
        BinaryOp op,
        Expr left,
        Expr right,
        Result leftValue,
        SourceSpan? span)
    {
        if (op is not (BinaryOp.And or BinaryOp.Or))
            return null;

        var leftFlagR = RequireLogicalOperand(op, "left", left, right, leftValue, span);
        if (leftFlagR.IsError)
            return leftFlagR.Error;

        // Written as two returns: in a conditional expression the `null` arm would convert
        // through the EvalError conversion and yield a non-null error result.
        if (!LeftOperandDecides(op, leftFlagR.Value))
            return null;

        return EvalResult<Result>.Ok(new Result.Bool(leftFlagR.Value));
    }

    /// <summary>
    /// The Boolean requirement of ONE operand of a logical operator with its diagnostics: the
    /// value-kind rejection naming the operator, the side and the operand
    /// (<see cref="RequireBooleanOperand"/>) inside the binary operand-shape context, at the
    /// binary expression's span. The one place the logical operators' operand error is built,
    /// for the left operand judged before the right one is scheduled and for the operands
    /// judged at application alike.
    /// </summary>
    private static EvalResult<bool> RequireLogicalOperand(
        BinaryOp op,
        string side,
        Expr left,
        Expr right,
        Result value,
        SourceSpan? span)
    {
        var flagR = RequireBooleanOperand(op, side, value);
        return flagR.IsError
            ? new EvalError.WithContext(BinaryOperandContext(op, left, right), flagR.Error) { Span = span }
            : flagR;
    }

    /// <summary>
    /// Applies ONE binary (arithmetic or logical) operator to two evaluated operand
    /// values: the SINGLE binary application semantics and error/span policy shared by
    /// the generic expression-spine machine, its async twin, and the planned loop
    /// evaluator. Comparisons are NOT binary operators — every comparison is a link of a
    /// comparison chain and applies through <see cref="ApplyComparison"/>.
    /// <para>For <c>and</c> / <c>or</c> the routes reach this only after
    /// <see cref="DecideLogicalAfterLeftOperand"/> answered that the right operand is needed, so
    /// <paramref name="rightValue"/> is the value of an operand that was evaluated. The left
    /// operand is judged by the same rule here, so a deciding left operand is the result
    /// whatever the right value is: application and scheduling cannot disagree.</para>
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
        // The logical operators are Boolean-only: there is no numeric truthiness, so
        // `1 and 2` is a value-kind error, and the left operand is judged first. A left
        // operand that decides `and` / `or` is the result (the same rule the routes asked
        // before scheduling the right operand: DecideLogicalAfterLeftOperand); otherwise
        // the right operand must be a Boolean, and it is the result of `and` / `or`, while
        // `xor` — which needs both operands, evaluated left to right before this point —
        // is their inequality. Lean: evalBinaryCounted's `.and | .or` and `.xor` arms.
        if (op is BinaryOp.And or BinaryOp.Or or BinaryOp.Xor)
        {
            var leftFlagR = RequireLogicalOperand(op, "left", left, right, leftValue, span);
            if (leftFlagR.IsError)
                return leftFlagR.Error;
            if (LeftOperandDecides(op, leftFlagR.Value))
                return EvalResult<Result>.Ok(new Result.Bool(leftFlagR.Value));

            var rightFlagR = RequireLogicalOperand(op, "right", left, right, rightValue, span);
            if (rightFlagR.IsError)
                return rightFlagR.Error;
            bool a = leftFlagR.Value, b = rightFlagR.Value;
            return EvalResult<Result>.Ok(new Result.Bool(op == BinaryOp.Xor ? a != b : b));
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
    ///
    /// <para>Equality's structural work is charged to <paramref name="ctx"/>'s budget
    /// (SEC-02-FU, <see cref="ValueEquals"/>); its refusal is the only error <c>==</c>/<c>!=</c>
    /// can return, and it ends the chain like any link error — never a false link.</para>
    /// </summary>
    internal static EvalResult<bool> ApplyComparison(
        ComparisonOp op,
        Expr left,
        Expr right,
        Result leftValue,
        Result rightValue,
        SourceSpan? chainSpan,
        EvalCtx ctx)
    {
        if (op is ComparisonOp.Eq or ComparisonOp.Ne)
        {
            var equalR = ValueEquals(leftValue, rightValue, ctx);
            if (equalR.IsError) return equalR.Error;
            return EvalResult<bool>.Ok(equalR.Value == (op == ComparisonOp.Eq));
        }

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

    /// <summary>
    /// Split a COMPLETE loop step supply into next state slots and the continuation flag
    /// (<see cref="ContinuationFlag"/>): the supply's LAST item is the flag, and a
    /// single-item supply keeps the established shape — its one slot is both the next state
    /// and the flag (<see cref="WhileNextStateSlots"/>). The <c>while</c> round reads a step
    /// body's rows condition first (<see cref="EvalWhileVerdictSlots"/>); this split remains
    /// for a supply that is ONE atomic row (a builtin step, <see cref="WhileVerdictOfSupply"/>)
    /// and for a planned round's handover after its <c>true</c> verdict. Lean:
    /// <c>splitContSlots</c>.
    /// </summary>
    internal static EvalResult<(IReadOnlyList<Result> NextStateSlots, bool Continue)> SplitContSlots(
        IReadOnlyList<Result> outputSlots)
    {
        if (outputSlots.Count == 0)
            return new EvalError.WithContext(WhileStepWithoutFlagContext, new EvalError.BadArity());

        var flag = ContinuationFlag(outputSlots[^1]);
        if (flag.IsError) return flag.Error;
        return EvalResult<(IReadOnlyList<Result>, bool)>.Ok((
            outputSlots.Count == 1 ? outputSlots : outputSlots.Take(outputSlots.Count - 1).ToList(), flag.Value));
    }

    /// <summary>
    /// The <c>while</c> continuation flag rule (LOOP-06): the flag must be a Boolean value
    /// (<c>true</c> continues, <c>false</c> stops); a number, string, sequence, or list there is a
    /// value-kind error, never a truth test. Shared by the generic readers and the planned loop.
    /// </summary>
    internal static EvalResult<bool> ContinuationFlag(Result flag)
        => flag.AsBool() is { } value
            ? EvalResult<bool>.Ok(value)
            : new EvalError.TypeMismatch(BooleanRequiredMessage(WhileContinuationFlagRole, flag));

    /// <summary>
    /// <see cref="ContinuationFlag"/> for a flag supplied by a WRITTEN output row (both row
    /// readers and the planned loop): a rejected flag is positioned at <paramref name="flagRow"/>,
    /// the row whose last item it is — the narrowest truthful location, since a call or spread
    /// row's items carry no provenance of their own. The span is read only on error, and a row
    /// without one (a host-built tree) leaves the error unpositioned. An atomic supply (a builtin
    /// step) has no row and keeps the bare rule.
    /// </summary>
    internal static EvalResult<bool> ContinuationFlagOfRow(Expr flagRow, Result flag)
        => WithSpanOf(flagRow, ContinuationFlag(flag));

    /// <summary>
    /// The next state of an accepted <c>while</c> round from its complete supply (in place): the
    /// supply without its last item, the flag — except that a one-item supply is both the next
    /// state and the flag.
    /// </summary>
    private static List<Result> WhileNextStateSlots(List<Result> supply)
    {
        if (supply.Count > 1)
            supply.RemoveAt(supply.Count - 1);
        return supply;
    }

    /// <summary>
    /// A <c>while</c> round over a supply that is ONE atomic row (a builtin step, a builtin
    /// clause body): there are no earlier rows to skip, so the round is the ordinary split —
    /// <c>null</c> for a <c>false</c> flag, the next state otherwise.
    /// </summary>
    private static EvalResult<IReadOnlyList<Result>?> WhileVerdictOfSupply(IReadOnlyList<Result> supply)
    {
        var split = SplitContSlots(supply);
        if (split.IsError) return split.Error;
        return EvalResult<IReadOnlyList<Result>?>.Ok(split.Value.Continue ? split.Value.NextStateSlots : null);
    }

    // ── Builtins ─────────────────────────────────────────────────────────────
    // There is deliberately NO plain builtin dispatch function:
    // ApplyBuiltinCountedResolved is the ONE builtin dispatch switch
    // (sequence-builtin metadata routing plus the if/while/repeat/atoms/range
    // arms), and every plain spelling reaches it through the counted call
    // family plus the value projection. (Lean keeps the named projection
    // `applyBuiltin` because CoreTests guards address it directly; the C#
    // equivalent would have no caller at all.)
    //
    // There is likewise NO generic loop of its own for a planned loop's handover: its generic
    // continuation runs in the one round kernel (RunGenericLoopRounds, Evaluator.Needs.cs),
    // prepared from the head the planner admitted (PrepareAdmittedLoopStep).
}
