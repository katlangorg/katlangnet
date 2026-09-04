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
/// Expression evaluation: the iterative expression-spine machine, the Eval/EvalCounted dispatch, and native/host/Math dispatch including Math.Random sampling (the "Iterative expression-spine evaluation" and "Main eval" sections).
/// Part of the <see cref="Evaluator"/> partial class; the central state, lookup and open resolution,
/// the built-in prelude, and the run entry points remain in <c>Evaluator.cs</c>.
/// </summary>
public static partial class Evaluator
{
    // ── Iterative expression-spine evaluation ───────────────────────────────

    /// <summary>
    /// The pure-expression composite node kinds whose evaluation is driven by the
    /// iterative spine machine (<see cref="EvalExpressionSpineCounted"/>) instead of
    /// CLR recursion: unary and binary operators, index selection, and list literals.
    /// These are the shapes whose recursive evaluation frames were measured to
    /// exhaust a 1 MiB stack within the structural depth ceiling (binary/unary spines
    /// at ~330-340 nodes, index spines at ~270-285, list spines at ~290-300 in Debug),
    /// so within-ceiling safety REQUIRES that their nesting consume no proportional
    /// call stack. Algorithm-carrying kinds (blocks, calls, dot-calls) stay on their
    /// recursive paths and are bounded by the structural ceiling instead; the internal
    /// sequence-join kinds already have their own iterative handling
    /// (<see cref="EvalSequenceConstructCounted"/>, <see cref="EvalSequenceSpreadCounted"/>).
    /// </summary>
    private static bool IsExpressionSpineNode(Expr expr)
        => expr is Expr.Unary or Expr.Binary or Expr.Index or Expr.ListLiteral;

    /// <summary>One in-progress spine node in <see cref="EvalExpressionSpineCounted"/>.</summary>
    private struct ExpressionSpineFrame(Expr node)
    {
        public readonly Expr Node = node;

        /// <summary>Unary/Binary/Index: completed child count. ListLiteral: next element index.</summary>
        public int Phase;

        /// <summary>Binary left value / Index target value, once evaluated.</summary>
        public Result? FirstValue;

        /// <summary>ListLiteral element accumulator (exact written slots, spread already expanded).</summary>
        public List<Result>? ListItems;
    }

    /// <summary>
    /// Evaluates one maximal pure-expression spine with an explicit frame stack,
    /// replicating the recursive per-kind evaluation EXACTLY — child order, error
    /// decoration, spans, budget reservations, and emitted counts — while consuming
    /// O(1) CLR stack per spine node. Children that are not spine kinds are delegated
    /// to the ordinary recursive paths (one bounded frame layer; the structural
    /// preflight bounds how many such layers a path can alternate through).
    ///
    /// <para>Per-kind semantics preserved here (previously the recursive
    /// <c>Eval</c> cases and the <c>EvalIndexSelectionCounted</c> /
    /// <c>EvalListLiteralCounted</c> helpers):</para>
    /// <list type="bullet">
    ///   <item><b>Unary</b>: empty sequence propagates; strings are a
    ///   <see cref="EvalError.TypeMismatch"/> at the unary expression's span; operand
    ///   errors propagate untouched. Lean: <c>eval</c> unary case.</item>
    ///   <item><b>Binary</b>: left then right, each error propagating untouched, then
    ///   <see cref="ApplyBinaryOperator"/>. Lean: <c>eval</c> binary case.</item>
    ///   <item><b>Index</b>: target then selector; every child or coercion error gains
    ///   the index expression's span when it has none; the selected item re-emits its
    ///   PROJECTED count (<c>S:0</c> re-emits, never re-counts). Lean:
    ///   <c>evalIndexSelectionCounted</c>.</item>
    ///   <item><b>ListLiteral</b>: element slots follow the written-parentheses
    ///   expression-list slot rules (<see cref="EvalExplicitSequenceValueExprSlots"/>);
    ///   elements are stored EXACTLY (no singleton erasure, no empty canonicalization),
    ///   the collection reservation happens before the persistent list is built, and a
    ///   list literal always emits one value. Lean: <c>evalListLiteralCounted</c>;
    ///   plain <c>Eval</c> is this function's value projection on both sides.</item>
    /// </list>
    /// </summary>
    private static EvalResult<CountedResult> EvalExpressionSpineCounted(
        Expr root,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var frames = new ExpressionSpineFrame[16];
        var frameCount = 0;
        frames[frameCount++] = new ExpressionSpineFrame(root);

        // The counted result most recently produced for the top frame's pending
        // child. Machine-kind children deliver here when their frame pops; delegated
        // children deliver here directly.
        CountedResult pendingChild = default;
        var hasPendingChild = false;

        while (true)
        {
            // Bulk pathological-work bound (see TryChargeExpressionNodeWork): the
            // machine bypasses ordinary dispatch for spine kinds, so each frame
            // transition contributes to the same cheap bulk-work counter.
            if (ctx.Budget.TryChargeExpressionNodeWork() is { } nodeWorkError)
                return nodeWorkError;

            ref var frame = ref frames[frameCount - 1];
            EvalResult<CountedResult>? completed = null;
            Expr? requestedChild = null;

            switch (frame.Node)
            {
                case Expr.Unary(var unaryOp, var operand):
                {
                    if (!hasPendingChild)
                    {
                        requestedChild = operand;
                        break;
                    }

                    hasPendingChild = false;
                    var unaryR = ApplyUnaryOperator(unaryOp, pendingChild.Value, frame.Node.Span);
                    completed = unaryR.IsError
                        ? unaryR.Error
                        : EvalResult<CountedResult>.Ok(new CountedResult(
                            unaryR.Value, unaryR.Value.ValueCount()));
                    break;
                }

                case Expr.Binary(var op, var left, var right):
                {
                    if (frame.Phase == 0)
                    {
                        if (!hasPendingChild)
                        {
                            requestedChild = left;
                            break;
                        }

                        hasPendingChild = false;
                        frame.FirstValue = pendingChild.Value;
                        frame.Phase = 1;
                        requestedChild = right;
                        break;
                    }

                    hasPendingChild = false;
                    var binaryR = ApplyBinaryOperator(
                        op, left, right, frame.FirstValue!, pendingChild.Value, frame.Node.Span);
                    completed = binaryR.IsError
                        ? binaryR.Error
                        : EvalResult<CountedResult>.Ok(new CountedResult(
                            binaryR.Value, binaryR.Value.ValueCount()));
                    break;
                }

                case Expr.Index(var target, var selector):
                {
                    if (frame.Phase == 0)
                    {
                        if (!hasPendingChild)
                        {
                            requestedChild = target;
                            break;
                        }

                        hasPendingChild = false;
                        frame.FirstValue = pendingChild.Value;
                        frame.Phase = 1;
                        requestedChild = selector;
                        break;
                    }

                    hasPendingChild = false;

                    // ExpectInt reports TypeMismatch/BadArity from a Result and so has no
                    // span of its own; the index expression is the nearest source location.
                    var nR = ExpectInt(pendingChild.Value);
                    if (nR.IsError)
                    {
                        completed = AtSpanIfMissing(nR.Error, frame.Node.Span);
                        break;
                    }

                    var n = nR.Value;
                    // IsInteger is false for NaN and the infinities, so a non-finite
                    // selector is the same out-of-range badIndex as a fractional one.
                    if (!Decimal128.IsInteger(n) || n < 0)
                    {
                        completed = new EvalError.BadIndex() { Span = frame.Node.Span };
                        break;
                    }

                    // Lean models the selector as an unbounded integer and reports
                    // badIndex for any position past the target's items; a selector
                    // beyond int range can never be in range, so it is the same
                    // out-of-range error rather than a host overflow.
                    if (n > int.MaxValue)
                    {
                        completed = new EvalError.BadIndex() { Span = frame.Node.Span };
                        break;
                    }

                    var selected = frame.FirstValue!.SelectProjected((int)n);
                    completed = selected is null
                        ? new EvalError.BadIndex() { Span = frame.Node.Span }
                        : EvalResult<CountedResult>.Ok(new CountedResult(
                            selected.Value.Value, selected.Value.EmittedCount));
                    break;
                }

                case Expr.ListLiteral(var elements):
                {
                    frame.ListItems ??= [];
                    if (hasPendingChild)
                    {
                        // WRITTEN-SLOT REIFICATION: a machine-kind element is never a
                        // spread, so its counted supply contributes exactly ONE value.
                        hasPendingChild = false;
                        frame.ListItems.Add(pendingChild.Value);
                        frame.Phase++;
                    }

                    while (frame.Phase < elements.Count)
                    {
                        var element = elements[frame.Phase];
                        if (IsExpressionSpineNode(element))
                            break;

                        var slotsR = EvalExplicitSequenceValueExprSlots(element, ctx, valEnv);
                        if (slotsR.IsError)
                        {
                            completed = slotsR.Error;
                            break;
                        }

                        frame.ListItems.AddRange(slotsR.Value);
                        frame.Phase++;
                    }

                    if (completed is not null)
                        break;

                    if (frame.Phase < elements.Count)
                    {
                        requestedChild = elements[frame.Phase];
                        break;
                    }

                    // Cardinality is known once the written slots (including spread
                    // expansion) are evaluated, so the reservation happens before the
                    // persistent list is built.
                    if (ReserveCollection(ctx, frame.ListItems.Count, frame.Node.Span) is { } limitError)
                    {
                        completed = limitError;
                        break;
                    }

                    completed = EvalResult<CountedResult>.Ok(new CountedResult(
                        Result.ListValue.TakeOwnership(frame.ListItems.ToArray()), 1));
                    break;
                }

                default:
                    throw new InvalidOperationException(
                        $"EvalExpressionSpineCounted received the non-spine node kind '{frame.Node.GetType()}'.");
            }

            if (requestedChild is not null)
            {
                if (IsExpressionSpineNode(requestedChild))
                {
                    if (frameCount == frames.Length)
                        Array.Resize(ref frames, frames.Length * 2);
                    frames[frameCount++] = new ExpressionSpineFrame(requestedChild);
                    continue;
                }

                // Delegated child: exactly the call the recursive code made — plain
                // Eval for unary/binary operands and index targets/selectors. (List
                // elements never reach here; non-machine elements go through
                // EvalExplicitSequenceValueExprSlots above, exactly as before.)
                var childR = Eval(requestedChild, ctx, valEnv);
                if (childR.IsError)
                {
                    completed = childR.Error;
                }
                else
                {
                    pendingChild = new CountedResult(childR.Value, childR.Value.ValueCount());
                    hasPendingChild = true;
                    continue;
                }
            }

            if (completed is not { } completedResult)
                continue;

            if (completedResult.IsError)
            {
                // Unwind exactly like the recursive returns: the frame whose child
                // failed applies its child-error decoration (only Index attaches its
                // span), then returns the error to ITS parent, which decorates in
                // turn. An error produced by a frame's own apply step starts at that
                // frame's parent.
                var error = completedResult.Error;
                var decorateTopFrame = requestedChild is not null;
                while (frameCount > 0)
                {
                    ref var unwound = ref frames[frameCount - 1];
                    if (decorateTopFrame && unwound.Node is Expr.Index)
                        error = AtSpanIfMissing(error, unwound.Node.Span);

                    decorateTopFrame = true;
                    frameCount--;
                }

                return error;
            }

            frameCount--;
            if (frameCount == 0)
                return completedResult;

            pendingChild = completedResult.Value;
            hasPendingChild = true;
        }
    }

    // ── Main eval ───────────────────────────────────────────────────────────

    /// <summary>
    /// Test seams for exact diagnostic-span contracts on one prebuilt expression.
    /// Each call gets a fresh empty context (own budget); no structural preflight
    /// runs, so callers own the depth of what they build.
    /// </summary>
    internal static EvalResult<Result> EvalExpressionForTesting(Expr expr)
        => Eval(expr, EvalCtx.Empty, []);

    internal static EvalResult<CountedResult> EvalCountedExpressionForTesting(Expr expr)
        => EvalCounted(expr, EvalCtx.Empty, []);

    /// <summary>
    /// Counted parameter-reference evaluation — the CANONICAL Param dispatch
    /// shared by both dispatcher spellings (the plain <see cref="Eval"/> arm
    /// projects its value, so the dual-view rules exist once).
    /// Dual-view lookup order (Lean: <c>evalCounted</c> Param(x)):
    /// 1. Counted callback-param env (projected higher-order item meaning)
    /// 2. ValEnv (ordinary value meaning)
    /// 3. AlgEnv fallback (algorithm meaning):
    ///    - 0-param algorithm → auto-evaluate (thunk semantics)
    ///    - multi-param algorithm → arityMismatch (needs explicit call)
    /// </summary>
    private static EvalResult<CountedResult> EvalParamCounted(
        string name,
        SourceSpan? span,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var counted = LookupCountedParam(ctx.CountedParamEnv, name);
        if (counted is not null)
            return EvalResult<CountedResult>.Ok(counted.Value);

        var val = LookupVal(valEnv, name);
        if (val is not null)
            return EvalResult<CountedResult>.Ok(new CountedResult(val, val.ValueCount()));

        var algBinding = LookupAlgBinding(ctx.AlgEnv, name);
        if (algBinding is { } bound)
        {
            if (bound.ValueError is { } stickyLimit)
                return AtSpanIfMissing(stickyLimit, span);
            var algBound = bound.Algorithm;
            if (ConditionalValueAccessError(name, algBound) is { } conditionalError)
                return conditionalError with { Span = span };
            if (algBound.Params.Count == 0)
            {
                var valueR = WithSpan(span, EvalResolvedAlgOutputForValueDemand(algBound, ctx, valEnv));
                return valueR.IsError
                    ? valueR.Error
                    : EvalResult<CountedResult>.Ok(new CountedResult(valueR.Value, valueR.Value.ValueCount()));
            }
            return ZeroArgumentDemandArityMismatch(algBound) with { Span = span };
        }

        return new EvalError.UnknownName(name) { Span = span };
    }

    /// <summary>
    /// Counted lexical property-reference evaluation — the CANONICAL Resolve
    /// dispatch shared by both dispatcher spellings (the plain
    /// <see cref="Eval"/> arm projects its value). Resolution goes through the
    /// canonical binding-carrying <see cref="LookupLexical"/> chain, and
    /// zero-argument access re-counts at the property value boundary.
    /// Lean: <c>evalCounted</c> Resolve(n).
    /// </summary>
    private static EvalResult<CountedResult> EvalResolveCounted(
        string name,
        SourceSpan? span,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (ctx.CallStack.Count == 0)
            return new EvalError.UnknownName(name) { Span = span };

        var resolvedR = LookupLexical(ctx.CallStack[0], name, ctx);
        if (resolvedR.IsError)
            return AtSpanIfMissing(resolvedR.Error, span);

        if (ConditionalValueAccessError(name, resolvedR.Value.ResolvedAlgorithm) is { } conditionalError)
            return conditionalError with { Span = span };

        if (resolvedR.Value.ResolvedAlgorithm.Params.Count != 0)
        {
            return WithSpan<CountedResult>(
                span,
                new EvalError.WithContext(
                    CtxProperty(name),
                    ZeroArgumentDemandArityMismatch(resolvedR.Value.ResolvedAlgorithm)));
        }

        var propertyR = WithPropertyContextOnMissingOutput(name, span,
            EvalZeroArgPropertyAccessCounted(resolvedR.Value, ctx, valEnv));
        return propertyR.IsError
            ? propertyR.Error
            : EvalResult<CountedResult>.Ok(new CountedResult(
                propertyR.Value.Value,
                propertyR.Value.Value.ValueCount()));
    }

    /// <summary>
    /// Plain expression dispatch. Every RECURSIVE variant is the value
    /// projection of its counted-canonical implementation (the same per-variant
    /// helpers <see cref="EvalCounted"/> dispatches to), so plain and counted
    /// semantics exist once; only the true leaves (Num, StringLiteral,
    /// NativeCall, and the Grace/unknown catch-all) are plain-owned, because
    /// the counted dispatchers' leaf-delegation group — pinned by the M10
    /// async-dispatch exhaustiveness tests — delegates exactly those to this
    /// method. Lean: eval (the total value projection of evalCounted; Lean has
    /// no leaf exception because it has no async twin family).
    /// </summary>
    private static EvalResult<Result> Eval(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // Structural nesting charges no dynamic invocation depth; the pre-evaluation
        // structural preflight (AstStructuralPreflight) bounds every accepted tree to
        // EvaluationLimits.MaxSupportedAstDepth before evaluation begins, and the
        // pure-expression composite kinds (unary, binary, index, list literal, and the
        // internal sequence joins) evaluate ITERATIVELY, so recursion here grows only
        // at algorithm boundaries (blocks, calls, dot-calls) — the shapes the ceiling
        // is calibrated against. Deliberately NO TryEnsureSufficientExecutionStack
        // probe here: the CLR probe reserves roughly half of a 1 MiB stack, so a
        // per-node probe rejects deep parser-produced programs that complete fine
        // today (measured: a 288-level bracket nesting). The structural-nesting
        // backstop lives instead at the two per-nesting-level row-loop funnels
        // (EvalOutputRowsPreparedCore, EvalExplicitSequenceValueRowSlots and their
        // async twins), where static nesting multiplied by dynamic recursion
        // would otherwise descend uncharged between two chokepoint probes.
        // Bulk pathological-work bound (see TryChargeExpressionNodeWork).
        if (ctx.Budget.TryChargeExpressionNodeWork() is { } nodeWorkError)
            return nodeWorkError;

        switch (expr)
        {
            case Expr.Num(var n):
                return EvalResult<Result>.Ok(new Result.Atom(n));

            case Expr.StringLiteral(var s):
                return MakeStringResult(ctx, s, expr.Span);

            case Expr.Param(var name):
                // Value projection of the canonical counted Param dispatch
                // (dual-view lookup order documented on EvalParamCounted).
                return ProjectCountedValue(EvalParamCounted(name, expr.Span, ctx, valEnv));

            case Expr.Unary or Expr.Binary:
                // Unary and binary spines evaluate iteratively; the machine
                // preserves the recursive semantics exactly (empty-result
                // propagation, string rejection, ApplyBinaryOperator).
                return ProjectCountedValue(EvalExpressionSpineCounted(expr, ctx, valEnv));

            case Expr.SequenceConstruct:
                return ProjectCountedValue(EvalSequenceConstructCounted(expr, ctx, valEnv));

            case Expr.EmptySequence(var depth):
                return EvalResult<Result>.Ok(BuildEmptySequenceValue(depth));

            case Expr.SequenceSpread:
                return ProjectCountedValue(EvalSequenceSpreadCounted(expr, ctx, valEnv));

            case Expr.ListLiteral:
                return ProjectCountedValue(EvalExpressionSpineCounted(expr, ctx, valEnv));

            case Expr.AlgorithmExpr(var alg):
                {
                    var wired = WireToCaller(ctx, alg);
                    if (wired.Params.Count == 0)
                        return WithSpan(PreferExpressionSpan(expr.Span, wired.Output), EvalAlgOutput(wired, ctx, valEnv));
                    var blockSpan = PreferExpressionSpan(expr.Span, wired.Output);
                    return MissingImplicitArguments<Result>(wired, blockSpan);
                }

            case Expr.Capture(var captureBody):
                return WithSpan(PreferExpressionSpan(expr.Span, captureBody), EvalCaptureValue(captureBody, ctx, valEnv));

            case Expr.Resolve(var name):
                // Value projection of the canonical counted Resolve dispatch.
                return ProjectCountedValue(EvalResolveCounted(name, expr.Span, ctx, valEnv));

            case Expr.DotCall dotCallExpr:
                // Lean: eval (.dotMember o n fallback mode argsOpt) => withCtx (CtxMsg.dotCall o n) do evalDotCall
                // (the context — which renders the receiver's name — is built only on error).
                return WithSpan(expr.Span, WithDotCallCtx(dotCallExpr, ctx,
                    EvalDotCall(dotCallExpr, ctx, valEnv)));

            case Expr.Call(var func, var callArgs):
                return WithSpan(expr.Span,
                    EvalCallExpr(func, callArgs, ctx, valEnv));

            case Expr.Index:
                // The spine machine owns the index-expression span.
                return ProjectCountedValue(EvalExpressionSpineCounted(expr, ctx, valEnv));

            case Expr.NativeCall(var fnName, var argNames):
                return EvalNativeCall(fnName, argNames, ctx, valEnv);

            // Catch-all: uses Expr.kind for clear diagnostics
            default:
                return new EvalError.IllegalInEval(ExprKind(expr)) { Span = expr.Span };
        }
    }

    /// <summary>
    /// Evaluate an expression together with the number of top-level values it
    /// emits at the current algorithm boundary.
    /// Calls, name resolution, and collection builtins are value boundaries: they
    /// emit <c>Result.ValueCount</c> of the result value (one value for a
    /// non-empty result), so a multi-output body/collection is observed as one
    /// sequence value and only caller-site <c>spread</c> re-spreads it.
    /// Block expressions count as one sequence value when non-empty. Spread
    /// emits the immediate spread items of its operand. All other value
    /// expressions emit either zero values (empty result) or one value.
    /// Lean: <c>evalCounted</c>.
    /// </summary>
    internal static EvalResult<CountedResult> EvalCounted(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // Bulk pathological-work bound (see TryChargeExpressionNodeWork): free for
        // small ordinary programs, but a reference-shared (DAG-shaped) host tree that
        // re-evaluates 2^n occurrences of 25 nodes now consults the step budget.
        if (ctx.Budget.TryChargeExpressionNodeWork() is { } nodeWorkError)
            return nodeWorkError;

        switch (expr)
        {
            case Expr.Param(var name):
                return EvalParamCounted(name, expr.Span, ctx, valEnv);

            case Expr.SequenceSpread:
                return EvalSequenceSpreadCounted(expr, ctx, valEnv);

            case Expr.SequenceConstruct:
                return EvalSequenceConstructCounted(expr, ctx, valEnv);

            case Expr.Unary or Expr.Binary or Expr.ListLiteral:
                return EvalExpressionSpineCounted(expr, ctx, valEnv);

            case Expr.EmptySequence(var depth):
                {
                    var emptyValue = BuildEmptySequenceValue(depth);
                    return EvalResult<CountedResult>.Ok(new CountedResult(emptyValue, emptyValue.ValueCount()));
                }

            case Expr.AlgorithmExpr(var alg):
                {
                    var wired = WireToCaller(ctx, alg);
                    if (wired.Params.Count == 0)
                    {
                        var blockR = WithSpan(PreferExpressionSpan(expr.Span, wired.Output), EvalAlgOutput(wired, ctx, valEnv));
                        if (blockR.IsError) return blockR.Error;
                        return EvalResult<CountedResult>.Ok(new CountedResult(blockR.Value, blockR.Value.ValueCount()));
                    }

                    var blockSpan = PreferExpressionSpan(expr.Span, wired.Output);
                    return MissingImplicitArguments<CountedResult>(wired, blockSpan);
                }

            case Expr.Capture(var captureBody):
                {
                    // A capture in value position is a value boundary: the body's
                    // supply is captured to one canonical value and re-counted as
                    // that value's ValueCount.
                    var captureR = WithSpan(PreferExpressionSpan(expr.Span, captureBody), EvalCaptureValue(captureBody, ctx, valEnv));
                    if (captureR.IsError) return captureR.Error;
                    return EvalResult<CountedResult>.Ok(new CountedResult(captureR.Value, captureR.Value.ValueCount()));
                }

            case Expr.Resolve(var name):
                return EvalResolveCounted(name, expr.Span, ctx, valEnv);

            case Expr.DotCall dotCallExpr:
                return WithSpan(expr.Span, WithDotCallCtx(dotCallExpr, ctx,
                    EvalDotCallCounted(dotCallExpr, ctx, valEnv)));

            case Expr.Call(var func, var callArgs):
                return WithSpan(expr.Span,
                    EvalCallCountedExpr(func, callArgs, ctx, valEnv));

            case Expr.Index:
                // The spine machine owns the index-expression span.
                return EvalExpressionSpineCounted(expr, ctx, valEnv);

            // PLAIN-DELEGATING cases of the counted dispatch: each produces
            // exactly one value, so delegating to the plain evaluator and
            // projecting a single-value count is total. Grace is the
            // deliberate illegal-in-eval catch-all (elaboration strips every
            // written one; a host-built survivor reports
            // EvalError.IllegalInEval through the plain dispatch). Num,
            // StringLiteral and Grace are also LEAVES — they evaluate no child
            // expression — and are the sync-delegable group EvalCountedAsync
            // may run through the synchronous evaluator. NativeCall is NOT a
            // leaf: its declared-argument reads are ordinary Expr.Param value
            // reads, so a demanded algorithm-channel binding re-enters an
            // algorithm body; the async twin therefore gives it its own case
            // (EvalNativeCallAsync). Keep this classification in lock-step
            // with EvalCountedAsync.
            case Expr.Num:
            case Expr.StringLiteral:
            case Expr.NativeCall:
            case Expr.Grace:
                {
                    var resultR = Eval(expr, ctx, valEnv);
                    if (resultR.IsError) return resultR.Error;
                    return EvalResult<CountedResult>.Ok(new CountedResult(resultR.Value, resultR.Value.ValueCount()));
                }

            // Exhaustiveness guard, matching AstWalker.VisitExpr: a new Expr
            // variant must be classified above — an explicit counted case, or
            // a proven leaf added to the delegation group — rather than
            // silently taking the plain evaluator's value with a single-value
            // count (which would silently erase multi-item emission).
            default:
                throw new InvalidOperationException(
                    $"Unhandled Expr variant in {nameof(Evaluator)}.{nameof(EvalCounted)}: {expr.GetType().Name}. " +
                    "Add an explicit counted case (or classify it as a proven leaf) here and in EvalCountedAsync.");
        }
    }

    private static EvalResult<Result> EvalNativeCall(
        string fnName,
        IReadOnlyList<string> argNames,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // Host-operation dispatch precedes the built-in switch. Host wrapper bodies
        // carry the "host:"-prefixed native name (a spelling no built-in native uses,
        // since ':' cannot appear in an identifier), so registered host operations and
        // built-in Math natives can never collide. An unregistered host-prefixed name —
        // a host-built AST evaluated without its configuration — falls through to the
        // ordinary unknown-native-function error below.
        if (ctx.Budget.HostOperations is { } hostOperations
            && fnName.StartsWith(HostOperations.NativeNamePrefix, StringComparison.Ordinal)
            && hostOperations.TryGetByNativeName(fnName, out var hostOperation))
        {
            return InvokeSynchronousHostOperation(hostOperation, argNames, ctx, valEnv);
        }

        var argsR = CollectMathNativeArguments(argNames, ctx, valEnv);
        if (argsR.IsError) return argsR.Error;

        return ApplyMathNative(fnName, argsR.Value);
    }

    /// <summary>
    /// Reads one Math native's declared arguments from the wrapper's bound
    /// parameter environments, in declaration order, and coerces each to its
    /// numeric domain. Lookup is the shared native-argument read
    /// (<see cref="LookupNativeArgument"/>), which is the ordinary
    /// <see cref="Expr.Param"/> value read; the numeric constraint applies to
    /// the value that read produced.
    /// </summary>
    private static EvalResult<Decimal128[]> CollectMathNativeArguments(
        IReadOnlyList<string> argNames,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var args = new Decimal128[argNames.Count];
        for (var i = 0; i < argNames.Count; i++)
        {
            var valR = LookupNativeArgument(ctx, valEnv, argNames[i]);
            if (valR.IsError) return valR.Error;
            var val = valR.Value;
            var num = val.AsNum();
            if (num is null)
                return val is Result.Str
                    ? new EvalError.TypeMismatch("Expected a number, got a string")
                    : new EvalError.BadArity();
            args[i] = num.Value;
        }

        return EvalResult<Decimal128[]>.Ok(args);
    }

    /// <summary>
    /// Applies one Math native to its already-read numeric arguments. Pure
    /// computation over the argument snapshot — it evaluates nothing and reads
    /// no environment — so the synchronous dispatch and its async twin share
    /// this ONE implementation and the member set cannot drift between them.
    /// </summary>
    private static EvalResult<Result> ApplyMathNative(string fnName, Decimal128[] args)
    {
        // Every math member computes Decimal128 end-to-end — no double round-trip
        // anywhere, so transcendental results carry Decimal128's full 34-digit
        // precision. Domain violations follow IEEE: Sqrt(-1) and Ln(-1) are NaN,
        // Ln(0) is -Infinity, and non-finite inputs propagate. Transcendental
        // results are quantum-canonicalized (see CanonicalizeMathResult); the
        // quantum-transparent members (Abs/Ceil/Floor/Round/Sign) keep their
        // argument-derived quanta exactly as System.Decimal did.
        Decimal128 result;
        switch (fnName)
        {
            case "Abs": result = Decimal128.Abs(args[0]); break;
            case "Ceil": result = Decimal128.Ceiling(args[0]); break;
            case "Floor": result = Decimal128.Floor(args[0]); break;
            case "Round":
                if (!Decimal128.IsInteger(args[1]))
                    return new EvalError.IllegalInEval("digits must be an integer");
                if (args[1] < 0)
                    return new EvalError.IllegalInEval("digits must be >= 0");
                // The smallest representable quantum is 1e-6176, so rounding is the
                // identity for any larger digit count — oversized counts clamp there
                // before the host (int) narrowing.
                result = Decimal128.Round(
                    args[0],
                    ClampRoundDigits(args[1]),
                    MidpointRounding.AwayFromZero);
                break;
            case "Sign":
                // Decimal128.Sign throws on NaN; the signum of NaN propagates as NaN.
                result = Decimal128.IsNaN(args[0]) ? Decimal128.NaN : Decimal128.Sign(args[0]);
                break;
            case "Sqrt": result = CanonicalizeMathResult(Decimal128.Sqrt(args[0])); break;
            case "Exp": result = CanonicalizeMathResult(Decimal128.Exp(args[0])); break;
            case "Ln": result = CanonicalizeMathResult(Decimal128.Log(args[0])); break;
            case "Lg": result = CanonicalizeMathResult(Decimal128.Log10(args[0])); break;
            case "Sin": result = CanonicalizeMathResult(Decimal128.Sin(args[0])); break;
            case "Asin": result = CanonicalizeMathResult(Decimal128.Asin(args[0])); break;
            case "Cos": result = CanonicalizeMathResult(Decimal128.Cos(args[0])); break;
            case "Acos": result = CanonicalizeMathResult(Decimal128.Acos(args[0])); break;
            case "Tan": result = CanonicalizeMathResult(Decimal128.Tan(args[0])); break;
            case "Atan": result = CanonicalizeMathResult(Decimal128.Atan(args[0])); break;
            case "Atan2": result = CanonicalizeMathResult(Decimal128.Atan2(args[0], args[1])); break;
            case "Pow":
                // Math.Pow and the `^` operator share one implementation, so the
                // exact integer-exponent path and the zero-base rule cannot drift.
                return EvalPow(span: null, args[0], args[1]);
            case "Log": result = CanonicalizeMathResult(Decimal128.Log(args[0], args[1])); break;
            case "Random":
                if (!Decimal128.IsFinite(args[0]) || !Decimal128.IsFinite(args[1]))
                    return new EvalError.IllegalInEval("Math.Random bounds must be finite numbers");
                if (args[0] >= args[1])
                    return new EvalError.IllegalInEval("Math.Random start must be less than end");
                if (!Decimal128.IsFinite(args[1] - args[0]))
                    return new EvalError.IllegalInEval("Math.Random range is too large");
                result = RandomInHalfOpenRange(args[0], args[1]);
                break;
            case "RandomInt":
                // Uniform INTEGER-domain generation, never a scaled fraction: flooring a
                // scaled Math.Random draw biases every span that does not divide its
                // 10^34-point lattice. Bounds are confined to the exact consecutive-integer
                // domain (|bound| <= 1e34), where every candidate result is exactly
                // representable and the span is exactly countable — beyond it, uniformity
                // over "the integers in the interval" is not even well-defined in
                // Decimal128, so such bounds are rejected rather than silently biased.
                if (!Decimal128.IsInteger(args[0]) || !Decimal128.IsInteger(args[1]))
                    return new EvalError.IllegalInEval("Math.RandomInt bounds must be whole numbers");
                if (Decimal128.Abs(args[0]) > MaxExactRangeBound || Decimal128.Abs(args[1]) > MaxExactRangeBound)
                    return new EvalError.IllegalInEval("Math.RandomInt bounds must not exceed 1e34 in magnitude");
                if (args[0] >= args[1])
                    return new EvalError.IllegalInEval("Math.RandomInt start must be less than end");
                result = SampleUniformInteger(args[0], args[1], SharedRandomUInt128Source);
                break;
            default:
                return new EvalError.IllegalInEval($"unknown native function: {fnName}");
        }

        return EvalResult<Result>.Ok(new Result.Atom(result));
    }

    internal static int ClampRoundDigits(Decimal128 digits)
        => (int)Decimal128.Min(digits, 6176);

    /// <summary>
    /// Invokes a SYNCHRONOUS host operation at its wrapper-body evaluation site. Runs
    /// inside the wrapper call's already-charged invocation region, exactly like a Math
    /// native, so no additional budget accounting applies here. Host exceptions
    /// propagate unchanged — host code failing is a host outcome, never a KatLang
    /// diagnostic (the same contract as the zero-argument property cache seam).
    /// </summary>
    private static EvalResult<Result> InvokeSynchronousHostOperation(
        HostOperation hostOperation,
        IReadOnlyList<string> argNames,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // Every entry point routes asynchronous configurations away from the
        // synchronous evaluator; reaching one here means a routing guard was bypassed.
        // Fail loud instead of blocking on the awaitable or silently skipping the call.
        if (hostOperation.SynchronousImplementation is not { } implementation)
        {
            throw new InvalidOperationException(
                $"Asynchronous host operation '{hostOperation.Name}' reached the synchronous evaluator; " +
                "async host configurations must route through the async evaluation path.");
        }

        if (ValidateHostOperationNativeSignature(hostOperation, argNames) is { } signatureError)
            return signatureError;

        var argumentsR = CollectHostOperationArguments(argNames, ctx, valEnv);
        if (argumentsR.IsError) return argumentsR.Error;

        var value = implementation(argumentsR.Value, ctx.Budget.CancellationToken);
        return EvalResult<Result>.Ok(NormalizeHostOperationValue(hostOperation, value));
    }

    /// <summary>
    /// The canonical-value boundary for one SUCCESSFUL host-operation return, shared by
    /// the synchronous dispatch (<see cref="InvokeSynchronousHostOperation"/>) and the
    /// async twin's await site (<c>EvalAsynchronousHostOperationCountedAsync</c>) so the
    /// two paths cannot drift. Host code builds values with the public constructors and
    /// may hand back representations ordinary KatLang evaluation would have canonicalized
    /// during construction — a singleton transparent sequence around an atom, redundant
    /// nested unary sequence structure around the empty sequence — and such raw shapes
    /// diverge from equal program-produced values at representation-sensitive rules
    /// (structural equality, visible-empty counting). <see cref="Result.Normalize"/> is
    /// the ONE existing canonicalization algorithm and is applied here, at the host
    /// boundary, before the value reaches ANY consumer: the wrapper body's evaluation
    /// result is derived from this normalized value, so the zero-argument property cache
    /// (which stores that evaluation outcome) can only ever store the canonical value —
    /// a cache hit re-serves it without re-normalizing. Normalize is sharing-preserving
    /// and returns an already-canonical value AS ITSELF (same reference), so canonical
    /// host returns are untouched; lists and strings keep their exact opacity. Successful
    /// values only: host exceptions, faulted awaitables, and cancellation propagate
    /// before this helper runs, and a null return remains the fail-loud host contract
    /// violation.
    /// </summary>
    private static Result NormalizeHostOperationValue(HostOperation hostOperation, Result? value)
        => value is null
            ? throw new InvalidOperationException(
                $"Host operation '{hostOperation.Name}' returned null; host operations must return a KatLang value.")
            : value.Normalize();

    /// <summary>
    /// A host operation may be reached only through the synthetic wrapper built by its
    /// matching <see cref="HostOperations"/> set. <see cref="Expr.NativeCall"/> remains
    /// publicly host-constructible for Math compatibility, so reject forged host calls
    /// whose environment-binding metadata does not exactly match the registered
    /// signature instead of invoking host code with an unexpected argument list.
    /// </summary>
    private static EvalError? ValidateHostOperationNativeSignature(
        HostOperation hostOperation,
        IReadOnlyList<string> argNames)
    {
        // The synthesized runtime wrapper stores the operation's immutable parameter
        // list directly, so every ordinary call takes this allocation-free O(1) path.
        // The element comparison is only for host-constructed ASTs.
        if (ReferenceEquals(argNames, hostOperation.ParameterNames))
            return null;

        if (argNames.Count == hostOperation.ParameterNames.Count)
        {
            var matches = true;
            for (var i = 0; i < argNames.Count; i++)
            {
                if (!string.Equals(argNames[i], hostOperation.ParameterNames[i], StringComparison.Ordinal))
                {
                    matches = false;
                    break;
                }
            }

            if (matches)
                return null;
        }

        return new EvalError.IllegalInEval(
            $"invalid native-call signature for host operation: {hostOperation.Name}");
    }

    /// <summary>
    /// Collects a host operation's evaluated argument values from the wrapper's bound
    /// parameter environments, in declaration order, as the read-only snapshot handed
    /// to host code. Lookup is the shared counted-first native-argument rule
    /// (<see cref="LookupNativeArgument"/>), so a flat-callback invocation hands the
    /// host its callback-bound arguments — never a same-named ambient value. Unlike
    /// Math natives there is no numeric coercion: host operations receive the full
    /// KatLang values.
    /// </summary>
    private static EvalResult<IReadOnlyList<Result>> CollectHostOperationArguments(
        IReadOnlyList<string> argNames,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (argNames.Count == 0)
            return EvalResult<IReadOnlyList<Result>>.Ok([]);

        var arguments = new Result[argNames.Count];
        for (var i = 0; i < argNames.Count; i++)
        {
            var valueR = LookupNativeArgument(ctx, valEnv, argNames[i]);
            if (valueR.IsError) return valueR.Error;
            arguments[i] = valueR.Value;
        }

        return EvalResult<IReadOnlyList<Result>>.Ok(Array.AsReadOnly(arguments));
    }

    /// <summary>
    /// IEEE 754 <c>reduce</c> for transcendental math-function results: returns the
    /// same VALUE represented by its cohort member with the fewest trailing zeros.
    /// .NET's Decimal128 transcendentals report results at the maximum-precision
    /// quantum, which is informative only while all 34 digits are significant — an
    /// inexact result like <c>Sin(1)</c> passes through unchanged, while a
    /// mathematically exact result like <c>Lg(1000)</c> drops the uninformative
    /// trailing zeros (<c>3</c>, not <c>3.000…000</c>), matching what the previous
    /// runtime displayed. Presentation never re-rounds: this canonicalization is
    /// value-preserving and belongs to the operation, not the formatter. It is
    /// deliberately NOT applied to ordinary arithmetic or the quantum-transparent
    /// math members (Abs/Ceil/Floor/Round/Sign), whose argument-derived quanta are
    /// established KatLang display behavior.
    /// </summary>
    internal static Decimal128 CanonicalizeMathResult(Decimal128 value)
    {
        if (!Decimal128.IsFinite(value))
            return value;
        if (value == Decimal128.Zero)
            return Decimal128.IsNegative(value) ? Decimal128.NegativeZero : Decimal128.Zero;

        while (true)
        {
            var quantumExponent = Decimal128.ILogB(Decimal128.GetQuantum(value));
            var coarser = Decimal128.Quantize(value, Decimal128.ScaleB(Decimal128.One, quantumExponent + 1));
            // Coarsening only proceeds while it is exact: a changed value means a
            // significant digit would be lost, so the previous form is canonical.
            if (coarser != value || Decimal128.HaveSameQuantum(coarser, value))
                return value;

            value = coarser;
        }
    }

    /// <summary>Exact scale factor 1e-34 for composing full-precision random fractions.</summary>
    private static readonly Decimal128 RandomUnitFractionScale = Decimal128.ScaleB(Decimal128.One, -34);

    /// <summary>Exclusive bound of each independent 17-digit component draw.</summary>
    private const long RandomDecimalComponentBound = 100_000_000_000_000_000; // 1e17

    /// <summary>
    /// Production component source. <see cref="Random.Shared"/> is the runtime's
    /// thread-safe shared generator; <see cref="Random.NextInt64(long)"/> returns
    /// a value in <c>[0, maxExclusive)</c> without the modulo-scaling bias that a
    /// hand-rolled bounded conversion could introduce.
    /// </summary>
    private static readonly Func<long, long> SharedRandomInt64Source =
        static maxExclusive => Random.Shared.NextInt64(maxExclusive);

    /// <summary>
    /// A uniform random fraction in [0, 1) carrying Decimal128's full 34 significant
    /// digits: two independent 17-digit draws compose one uniform integer in
    /// [0, 1e34), scaled exactly by 1e-34. Every arithmetic step is exact, and the
    /// 1e34 lattice points carry just under 113 bits of entropy —
    /// <c>Random.NextDouble</c> would cap randomness at double's 53 bits.
    /// The bounded source is injected at this helper boundary so endpoint and
    /// composition behavior can be tested deterministically without replacing
    /// production randomness or introducing mutable global test state.
    /// </summary>
    internal static Decimal128 SampleRandomUnitFraction(Func<long, long> nextInt64Exclusive)
    {
        ArgumentNullException.ThrowIfNull(nextInt64Exclusive);
        var high = nextInt64Exclusive(RandomDecimalComponentBound);
        var low = nextInt64Exclusive(RandomDecimalComponentBound);
        if ((ulong)high >= (ulong)RandomDecimalComponentBound
            || (ulong)low >= (ulong)RandomDecimalComponentBound)
        {
            throw new InvalidOperationException(
                "The Math.Random component source returned a value outside its requested half-open bound.");
        }

        return (((Decimal128)high * RandomDecimalComponentBound) + low) * RandomUnitFractionScale;
    }

    private static Decimal128 NextRandomUnitFraction()
        => SampleRandomUnitFraction(SharedRandomInt64Source);

    private static Decimal128 RandomInHalfOpenRange(Decimal128 start, Decimal128 end)
        => ScaleRandomUnitFractionToHalfOpenRange(start, end, NextRandomUnitFraction());

    internal static Decimal128 ScaleRandomUnitFractionToHalfOpenRange(
        Decimal128 start,
        Decimal128 end,
        Decimal128 unitFraction)
    {
        var result = start + (unitFraction * (end - start));
        return result >= end ? start : result;
    }

    /// <summary>Production 128-bit draw source for <see cref="SampleUniformInteger"/>.</summary>
    private static readonly Func<UInt128> SharedRandomUInt128Source = NextRandomUInt128;

    internal static UInt128 NextRandomUInt128()
    {
        Span<byte> bytes = stackalloc byte[16];
        Random.Shared.NextBytes(bytes);
        return System.Buffers.Binary.BinaryPrimitives.ReadUInt128LittleEndian(bytes);
    }

    /// <summary>
    /// Uniform integer draw for <c>Math.RandomInt</c> over <c>[start, end)</c>:
    /// exact Int128 span plus modulo-REJECTION sampling over uniform 128-bit
    /// draws, so no span carries modulo bias and every integer in the interval is
    /// reachable with equal probability. Callers validate that both bounds are
    /// integers within ±1e34 (the exact consecutive-integer domain), so the span
    /// (at most 2e34) fits Int128 with room to spare and the chosen integer
    /// converts back to Decimal128 exactly.
    ///
    /// <para>The draw source is injected so tests can drive the mapping and
    /// rejection logic deterministically; production supplies
    /// <see cref="SharedRandomUInt128Source"/>. Draws at or above the largest
    /// multiple of the span below 2^128 are redrawn — the acceptance probability
    /// always exceeds one half, and each draw is independent, so the loop
    /// terminates with probability one and never biases the accepted values.</para>
    /// </summary>
    internal static Decimal128 SampleUniformInteger(Decimal128 start, Decimal128 end, Func<UInt128> nextUInt128)
    {
        var startInteger = (Int128)start;
        var span = (UInt128)((Int128)end - startInteger);

        // 2^128 mod span, computed without representing 2^128: the count of
        // rejected top draws. Zero means the span divides 2^128 exactly and no
        // draw is ever rejected.
        var rejectedDrawCount = (UInt128.MaxValue % span) + 1;
        if (rejectedDrawCount == span)
            rejectedDrawCount = 0;

        UInt128 draw;
        do
        {
            draw = nextUInt128();
        }
        while (rejectedDrawCount != 0 && draw > UInt128.MaxValue - rejectedDrawCount);

        return (Decimal128)(startInteger + (Int128)(draw % span));
    }
}
