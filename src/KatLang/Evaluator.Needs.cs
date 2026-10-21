using KatLang.Optimizations.Loops;
using KatLang.Evaluation;

namespace KatLang;

public static partial class Evaluator
{
    // Indexed, not `foreach`: enumerating the interface boxes an enumerator on every lookup unless
    // the JIT happens to devirtualize and stack-allocate it (PERF-ORD-1). Every environment list has
    // an O(1) indexer; the scan order and first-match rule are unchanged.
    private static NeedCell? LookupNeed(NeedEnv env, string name)
    {
        for (var i = 0; i < env.Count; i++)
        {
            var binding = env[i];
            if (binding.Name == name) return binding.Cell;
        }
        return null;
    }

    internal static NeedCell? ParameterNeedCell(string name, EvalCtx ctx)
        => LookupNeed(CapturedParameterActivation(name, ctx)?.Needs ?? ctx.NeedEnv, name);

    internal static EvalResult<CountedResult> DemandPlannedParameter(NeedCell cell, string name, SourceSpan? span)
        => DemandParameter(cell, cell.Demand(), name, span);

    private static EvalResult<Algorithm> ResolveNeedParameterAlgorithm(string name, SourceSpan? span, EvalCtx ctx)
    {
        var activation = CapturedParameterActivation(name, ctx);
        if (LookupNeed(activation?.Needs ?? ctx.NeedEnv, name) is { } cell)
        {
            var projected = cell.ProjectCallable();
            if (projected.IsError) return projected.Error;
            return projected.Value is { } callable
                ? EvalResult<Algorithm>.Ok(callable)
                : new EvalError.NotAnAlgorithm($"param({name})") { Span = span };
        }
        // No supplied cell: nothing binds the name on any channel. Lean: `resolveAlg (.param x)`.
        return new EvalError.NotAnAlgorithm($"param({name})") { Span = span };
    }

    private static EvalResult<CountedResult> DemandParameter(NeedCell cell, EvalResult<CountedResult> result, string name, SourceSpan? span)
        => result.IsError && cell.Slice is null && cell.Source is Expr.AlgorithmExpr
            ? ParameterSlotFailure(name, span, result.Error) : result;

    /// <summary>
    /// The supplied cell of one written argument slot (Lean <c>supplyNeed</c>): a bound parameter
    /// transports its existing cell; every other expression becomes a suspended cell whose
    /// suspension (<see cref="ExpressionSuspension"/>: the caller context and value environment)
    /// is kept as data. In a run that retains invocation plans (J7, <see cref="EvaluationBudget.RetainsInvocationPlans"/>),
    /// a WRITTEN INVOCATION (<see cref="IsPlannableCall"/>, META-S3-4: a call through a name, parameter or
    /// argumentless path, or an argument-bearing dot edge) IS an invocation plan
    /// (<see cref="InvocationPlan"/>): its VALUE executes through the plan's route and one supply
    /// (<see cref="EvalPlannedCallCounted"/>). An argumentless dot edge whose CALLABLE may be a
    /// RUNTIME projection (<see cref="IsRuntimeProjectionSource"/>, META-S3-1) gets its projection
    /// node — an edge spelled <c>Algorithm</c> whose intrinsic route is not statically excluded as a
    /// link (<see cref="LinkSuspension"/>, CR-15); a statically selected member stays identity-only.
    /// <paramref name="retained"/> marks a cell an owner establishes once and retains (a link's
    /// receiver, a plan's callee cell), which is retry-stable and therefore exempt from Guard B.
    /// </summary>
    internal static NeedCell SupplyCell(Expr expression, EvalCtx caller, ValEnv values, bool retained = false)
    {
        if (expression is Expr.Param(var name))
        {
            var parameterCtx = ParameterContext(name, caller, ref values);
            if (LookupNeed(parameterCtx.NeedEnv, name) is { } existing) return existing;
        }
        ExpressionSuspension suspension;
        var runtimeProjection = false;
        if (caller.Budget.RetainsInvocationPlans && IsPlannableCall(expression))
        {
            caller.Observations?.RecordInvocationPlan();
            suspension = new InvocationPlan(caller, values);
        }
        else if (expression is Expr.DotCall { Args: null } edge && IsRuntimeProjectionSource(edge, caller.Budget))
        {
            if (!retained) NeedCell.ThrowIfAllocatingRuntimeProjectionWhileObserving();
            runtimeProjection = true;
            suspension = edge.UsesDotAlgorithmIntrinsic() ? new LinkSuspension(caller, values) : new ExpressionSuspension(caller, values);
        }
        else if (caller.Budget.MayReachRuntimeAliases && MayResolveThroughAlias(expression)
            && (caller.Budget.HasDeferredModuleRegions || ReferenceReachesRuntimeAlias(expression, caller)))
        {
            // META-S3-2: resolving this reference's identity reaches a runtime-target alias's runtime
            // projection, so the reference cell is a runtime projection from its formation — never
            // runtime work under an identity-only cell lock, and never a second wrapper cell.
            if (!retained) NeedCell.ThrowIfAllocatingRuntimeProjectionWhileObserving();
            runtimeProjection = true;
            suspension = new ExpressionSuspension(caller, values);
        }
        else suspension = new ExpressionSuspension(caller, values);
        return new NeedCell(expression, suspension, caller.Budget, runtimeProjection, caller.Budget.CancellationToken);
    }

    /// <summary>
    /// The written REFERENCE shapes whose identity resolution normalizes a callable alias (FWD-02): a
    /// name, an argumentless dot path, and an inline alias block. Every other written expression is a
    /// value with no identity, or a parameter, whose own cell is transported.
    /// </summary>
    private static bool MayResolveThroughAlias(Expr expression)
        => expression is Expr.Resolve or Expr.DotCall { Args: null } or Expr.AlgorithmExpr { Algorithm: Algorithm.Alias };

    /// <summary>
    /// Whether the identity resolution of a written REFERENCE reaches a runtime-target alias (META-S3-2):
    /// its binding — a name by the ownership-first lookup, a dot path by structural navigation, an inline
    /// alias block itself — is an alias whose STATIC chain (the VALUE chase, <see cref="ResolveAliasTarget"/>)
    /// ends at a runtime-target alias. Static identity work only, exactly the steps the reference's own
    /// projection takes first. A static resolution failure is no reach: the reference keeps the static
    /// rule (absence lifted, any other failure propagated), as Lean's <c>projectNeedWritten</c>.
    /// A parameter-rooted path and an <c>.Algorithm</c> link are classified by <see cref="IsRuntimeProjectionSource"/> before this.
    /// </summary>
    private static bool ReferenceReachesRuntimeAlias(Expr expression, EvalCtx caller)
    {
        switch (expression)
        {
            case Expr.Resolve(var name):
            {
                if (caller.CallStack.Count == 0)
                    return false;
                var binding = LookupLexicalRaw(caller.CallStack[0], name, caller);
                return binding.IsOk
                    && binding.Value.ResolvedAlgorithm is Algorithm.Alias alias
                    && ChainReachesRuntimeAlias(alias, caller, binding.Value.Binding);
            }

            case Expr.DotCall edge:
            {
                var member = ResolveDotReceiver(edge, caller, out var isStructuralMember);
                return member.IsOk
                    && isStructuralMember && member.Value is Algorithm.Alias alias && ChainReachesRuntimeAlias(alias, caller, null);
            }

            case Expr.AlgorithmExpr { Algorithm: Algorithm.Alias inline }:
                return ChainReachesRuntimeAlias((Algorithm.Alias)WireToCaller(caller, inline), caller, null);

            default:
                return false;
        }

        static bool ChainReachesRuntimeAlias(Algorithm.Alias alias, EvalCtx ctx, Property? binding)
        {
            var end = ResolveAliasTarget(alias, ctx, binding, callable: false);
            return end.IsOk && end.Value is Algorithm.Alias;
        }
    }

    /// <summary>
    /// The VALUE of a written argument's cell, run inside the cell's single flight: the expression
    /// in its caller context — or, for an invocation plan, the plan's execution — finished at the
    /// argument's value boundary with any failure blamed on its written slot.
    /// </summary>
    internal static EvalResult<CountedResult> EvalSuspendedValue(NeedCell cell, ExpressionSuspension suspension)
    {
        var source = cell.Source!;
        // META-S3-4 (D-3): a planned `.Algorithm` invocation's retained receiver is read by the ordinary
        // invocation receiver evaluator.
        if (suspension is InvocationReceiverSuspension receiver)
            return EvalInvocationReceiver(receiver);
        if (suspension is LinkSuspension link && TryEvalLinkValue((Expr.DotCall)source, link) is { } linked)
            return FinishSuppliedLinkValue(source, suspension, linked);
        return FinishSuppliedValue(source, suspension, suspension is InvocationPlan plan
            ? EvalPlannedCallCounted(plan, byInvocation: false)
            : EvalCounted(source, suspension.Caller, suspension.Values));
    }

    /// <summary>MIRROR OF <see cref="EvalSuspendedValue"/> — keep in lock-step.</summary>
    internal static async ValueTask<EvalResult<CountedResult>> EvalSuspendedValueAsync(NeedCell cell, ExpressionSuspension suspension)
    {
        var source = cell.Source!;
        if (suspension is InvocationReceiverSuspension receiver)
            return await EvalInvocationReceiverAsync(receiver).ConfigureAwait(false);
        if (suspension is LinkSuspension link
            && await TryEvalLinkValueAsync((Expr.DotCall)source, link).ConfigureAwait(false) is { } linked)
            return FinishSuppliedLinkValue(source, suspension, linked);
        return FinishSuppliedValue(source, suspension, suspension is InvocationPlan plan
            ? await EvalPlannedCallCountedAsync(plan, byInvocation: false).ConfigureAwait(false)
            : await EvalCountedAsync(source, suspension.Caller, suspension.Values).ConfigureAwait(false));
    }

    /// <summary>
    /// The value boundary of a supplied cell: a written argument's failure is blamed on its slot and
    /// its value re-counted at the argument boundary. A cell supplied under an ALIAS head — a
    /// runtime-target alias's binding cell and the cells it establishes (FWD-02, META-S3-2) — is that
    /// alias's PROPERTY BODY: its outcome is the body's own, with property-style provenance and no
    /// argument slot.
    /// </summary>
    // Keep finishing out of the recursive VALUE frame. Passing EvalCtx by value here made
    // Debug reserve its copies while the child was still evaluating (+704 B per level).
    // The suspension already owns that context; read it only after the child returns.
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> FinishSuppliedValue(Expr source, ExpressionSuspension suspension, EvalResult<CountedResult> result)
        => suspension.Caller.Head is Algorithm.Alias ? result
            : result.IsError ? BlameWrittenArgumentSlot(source, result.Error) : ReCountValueBoundary(result);

    // A link's VALUE under an alias head is the property body's row `X.Algorithm`: its failure carries
    // the row's dot-call context and position, exactly as evaluating the row reports it.
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> FinishSuppliedLinkValue(Expr source, ExpressionSuspension suspension, EvalResult<CountedResult> linked)
        => FinishSuppliedValue(source, suspension, suspension.Caller.Head is Algorithm.Alias
            ? WithSpanOf(source, WithDotCallCtx((Expr.DotCall)source, suspension.Caller, linked)) : linked);

    /// <summary>
    /// The CALLABLE projection of a written argument's cell: identity-only resolution in the
    /// caller context, which evaluates nothing and demands no VALUE — except a supplied
    /// <c>X.Algorithm</c> link, whose projection demands its receiver cell's VALUE and projects
    /// the decoded callee cell (<see cref="ProjectLinkCallable"/>, CR-15), and a parameter-rooted
    /// path, which projects its head parameter's cell; both run as the cell's runtime projection.
    /// </summary>
    internal static EvalResult<Algorithm?> ProjectSuspendedCallable(NeedCell cell, Expr expression, ExpressionSuspension suspension)
    {
        var caller = suspension.Caller;
        // A dot expression carries the ONE identity its projection gives it in every
        // algorithm-capable position, the callee included (DOT-09).
        if (expression is Expr.DotCall edge)
            return suspension is LinkSuspension link ? ProjectLinkCallable(edge, link) : ProjectDotPathCallable(edge, caller);
        if (ShouldWrapArgExprAsValue(expression)) return EvalResult<Algorithm?>.Ok(null);
        var resolved = ResolveAlg(expression, caller);
        return resolved.IsOk ? EvalResult<Algorithm?>.Ok(resolved.Value)
            : IsLiftableError(resolved.Error) ? EvalResult<Algorithm?>.Ok(null) : resolved.Error;
    }

    // Sync formation has no suspending operation. Both engines execute this one ordered
    // supply algorithm; only the evaluation of an arbitrary spread has an async twin.
    private static async ValueTask<EvalResult<IReadOnlyList<NeedCell>>> FormNeedSupply(
        OutputBundle arguments, EvalCtx caller, ValEnv values, bool asynchronous, List<Expr?>? sources = null)
    {
        var supply = new List<NeedCell>(arguments.Count);
        // SEC-01: the supply is transient-bounded (TransientSupply); an overflowed supply forms
        // count-only to its end, then is refused at the slot that overflowed it.
        TransientSupply bound = default;
        SourceSpan? overflowAt = null;
        foreach (var argument in arguments)
        {
            if (argument is not Expr.SequenceSpread spread)
            {
                var overflowed = bound.Overflowed;
                if (AdmitTransient(caller.Budget, ref bound, 1, expansion: false))
                {
                    supply.Add(SupplyCell(argument, caller, values));
                    sources?.Add(argument);
                }
                if (bound.Overflowed && !overflowed)
                    overflowAt = argument.Span;
                continue;
            }
            var formed = await FormSpreadSupplySlot(spread, caller, values, asynchronous, supply, sources, bound).ConfigureAwait(false);
            if (formed.Failure is { } failure)
                return failure;
            if (formed.Supply.Overflowed && !bound.Overflowed)
                overflowAt = spread.Span;
            bound = formed.Supply;
        }
        return bound.Overflowed
            ? RefuseTransientSupply(caller.Budget, bound, overflowAt)
            : EvalResult<IReadOnlyList<NeedCell>>.Ok(supply);
    }

    /// <summary>
    /// The ONE formation of an explicit spread slot, shared by every supply a written expression
    /// list forms — a call's arguments (<see cref="FormNeedSupply"/>) and a postfix selection's
    /// selectors (<see cref="FormSelectionSupply"/>): a collecting parameter's known slice is
    /// transported unforced; any other spread operand is evaluated NOW, during formation, and
    /// opened one boundary into Ready items — except that when the value its LAST star opens is an
    /// ARGUMENT VIEW (CallReference S2), the slot transports that view's ORIGINAL cells (the plan's
    /// one sticky supply, <see cref="PrepareArgumentView"/>), each with its own written source, and
    /// demands none of them: no copy, no Ready wrapper, no second preparation. Appends the slot's cells
    /// to <paramref name="supply"/> (and their written sources to <paramref name="sources"/>) and
    /// returns the formation failure, if any. Lean: <c>NeedSupply.slot</c>, whose known-slice test is
    /// <c>spreadCollectorSlice?</c> and whose computed spread is <c>evalSupplySpread</c>.
    /// <para>The supply is TRANSIENT-BOUNDED (SEC-01, <see cref="AdmitTransient"/>): the slot's
    /// cardinality — a known slice's or view's cell count, a computed spread's opened item count — is
    /// admitted into <paramref name="bound"/> BEFORE any cell is appended or created; an overflowed
    /// supply only counts the slot (the computed spread is still evaluated, exactly as without the
    /// bound). Returns the updated bound with the formation failure.</para>
    /// </summary>
    private static async ValueTask<SpreadSlotFormation> FormSpreadSupplySlot(
        Expr.SequenceSpread argument, EvalCtx caller, ValEnv values, bool asynchronous,
        List<NeedCell> supply, List<Expr?>? sources, TransientSupply bound)
    {
        // A collecting parameter's known slice, found exactly as SupplyCell finds a parameter's
        // cell — without allocating a cell for any other operand.
        if (argument.Operand is Expr.Param(var name) && ParameterNeedCell(name, caller) is { Slice: { } known })
        {
            if (AdmitTransient(caller.Budget, ref bound, known.Count, expansion: true))
            {
                supply.AddRange(known);
                if (sources is not null) sources.AddRange(known.Select(static cell => cell.Source));
            }
            return new(null, bound);
        }
        // The spread node's dispatch checkpoint, which EvalCounted charges before its spread arm; the
        // operand is then evaluated ONCE and opened exactly as EvalSequenceSpreadCounted opens it
        // (it owns output-less spread diagnostics), with the last star's view left to transport.
        if (caller.Budget.TryChargeExpressionNodeWork() is { } nodeWorkError)
            return new(nodeWorkError, bound);
        var operand = PeelSpreadLayers(argument, out var layers);
        var operandR = asynchronous
            ? await EvalSequenceSpreadOperandValueAsync(operand, caller, values).ConfigureAwait(false)
            : EvalSequenceSpreadOperandValue(operand, caller, values);
        if (operandR.IsError) return new(operandR.Error, bound);
        var opened = OpenSpreadLayers(operandR.Value, layers, argument, caller, transportView: true, out var view);
        if (view is not null)
        {
            var cells = asynchronous
                ? await PrepareArgumentViewAsync(view, caller).ConfigureAwait(false)
                : PrepareArgumentView(view, caller);
            if (cells.IsError) return new(AtSpanIfMissing(cells.Error, argument.Span), bound);
            if (AdmitTransient(caller.Budget, ref bound, cells.Value.Count, expansion: true))
            {
                supply.AddRange(cells.Value);
                if (sources is not null)
                    foreach (var cell in cells.Value)
                        sources.Add(cell.Source);
            }
            return new(null, bound);
        }
        if (opened.IsError) return new(opened.Error, bound);
        if (AdmitTransient(caller.Budget, ref bound, CountedTopLevelValueCount(opened.Value), expansion: true))
        {
            foreach (var item in CountedTopLevelValues(opened.Value))
            {
                supply.Add(NeedCell.Ready(new(item, item.ValueCount())));
                sources?.Add(null);
            }
        }
        return new(null, bound);
    }

    /// <summary>One spread slot's formation (<see cref="FormSpreadSupplySlot"/>): its failure, if any, and the supply's updated SEC-01 bound.</summary>
    private readonly record struct SpreadSlotFormation(EvalError? Failure, TransientSupply Supply);

    /// <summary>
    /// Forms the SELECTOR SUPPLY of a postfix selection <c>R[s1, …, sn]</c> exactly as a call forms
    /// its arguments (Lean: <c>formNeedSupply</c>): every explicit spread slot runs now, in written
    /// order, through the ONE spread formation (<see cref="FormSpreadSupplySlot"/>), and the first
    /// spread failure stops formation; every ORDINARY slot stays an unevaluated written expression,
    /// demanded later — left to right, after formation — as a machine child of the selection frame.
    /// Evaluating that private slot at its turn is observably its suspended cell's first demand:
    /// nothing else can reach the cell, a parameter slot reads its own transported cell through the
    /// ordinary parameter read, and the value is the same. Called only when a spread slot exists;
    /// a selection without one forms nothing. A formation failure is positioned at its spread slot.
    /// </summary>
    private static async ValueTask<EvalResult<List<SuppliedSelector>>> FormSelectionSupply(
        Expr.Index selection, EvalCtx ctx, ValEnv valEnv, bool asynchronous)
    {
        var supplied = new List<SuppliedSelector>(selection.Selectors.Count);
        List<NeedCell>? cells = null;
        // SEC-01: the selector supply is transient-bounded like a call's (FormNeedSupply).
        TransientSupply bound = default;
        SourceSpan? overflowAt = null;
        foreach (var slot in selection.Selectors)
        {
            if (slot is not Expr.SequenceSpread spread)
            {
                var overflowed = bound.Overflowed;
                if (AdmitTransient(ctx.Budget, ref bound, 1, expansion: false))
                    supplied.Add(new SuppliedSelector(slot, null));
                if (bound.Overflowed && !overflowed)
                    overflowAt = slot.Span ?? selection.Span;
                continue;
            }
            cells ??= [];
            cells.Clear();
            var formed = await FormSpreadSupplySlot(spread, ctx, valEnv, asynchronous, cells, sources: null, bound).ConfigureAwait(false);
            if (formed.Failure is { } failure)
                return AtSpanIfMissing(failure, slot.Span ?? selection.Span);
            if (formed.Supply.Overflowed && !bound.Overflowed)
                overflowAt = slot.Span ?? selection.Span;
            bound = formed.Supply;
            foreach (var cell in cells)
                supplied.Add(new SuppliedSelector(slot, cell));
        }
        return bound.Overflowed
            ? RefuseTransientSupply(ctx.Budget, bound, overflowAt)
            : EvalResult<List<SuppliedSelector>>.Ok(supplied);
    }

    /// <summary>The synchronous engine's call of <see cref="FormSelectionSupply"/>, kept out of the spine machine's frame.</summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<List<SuppliedSelector>> FormSelectionSupplySync(Expr.Index selection, EvalCtx ctx, ValEnv valEnv)
        => FormSelectionSupply(selection, ctx, valEnv, asynchronous: false).GetAwaiter().GetResult();

    private static ValueTask<EvalResult<CountedResult>> DemandCell(NeedCell cell, bool asynchronous)
        => asynchronous ? cell.DemandAsync() : new(cell.Demand());

    private static EvalResult<Algorithm> ProjectInvokedCell(NeedCell cell)
    {
        var projected = cell.ProjectCallable();
        return projected.IsError ? projected.Error : projected.Value is { } algorithm
            ? EvalResult<Algorithm>.Ok(algorithm)
            : new EvalError.NotAnAlgorithm("argument") { Span = cell.Span };
    }

    private static async ValueTask<EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>>> ResolveNeedSupply(
        OutputBundle args, EvalCtx ctx, ValEnv values, bool asynchronous)
    {
        var sources = new List<Expr?>(args.Count);
        var formed = await FormNeedSupply(args, ctx, values, asynchronous, sources).ConfigureAwait(false);
        return formed.IsError ? formed.Error : EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>>.Ok(
            formed.Value.Select((cell, index) => new ResolvedArgumentAlgorithm(null) { Cell = cell, Source = sources[index] }).ToArray());
    }

    private static NeedCell CollectorCell(IReadOnlyList<NeedCell> slice, EvalCtx ctx)
    {
        async ValueTask<EvalResult<CountedResult>> Materialize(bool asynchronous)
        {
            var items = new List<Result>(slice.Count);
            foreach (var cell in slice)
            {
                var value = await DemandCell(cell, asynchronous).ConfigureAwait(false);
                if (value.IsError) return value.Error;
                items.Add(value.Value.Value);
            }
            return MakeCollectionListResult(ctx, items);
        }
        return new NeedCell(() => Materialize(false).GetAwaiter().GetResult(), () => Materialize(true),
            token: ctx.Budget.CancellationToken, slice: slice, budget: ctx.Budget);
    }

    // `Meta` (CallReference S1) marks a META capture: its name binds a Ready adapter holding the
    // supplied call's reference (ReferenceAdapterCell), reified when written traversal reaches it.
    // Lean: NeedPattern.metaRef.
    private sealed record NeedPattern(
        string? Name = null, bool Collecting = false,
        IReadOnlyList<NeedPattern>? Children = null, bool List = false, Pattern? Literal = null, bool Unpacking = false, ParameterPattern? Original = null,
        bool Meta = false);

    // Translation preserves reference sharing and uses explicit post-order frames. The
    // structural preflight has already rejected cyclic patterns before evaluation begins.
    private static IReadOnlyList<NeedPattern> TranslateNeedPatterns<T>(IReadOnlyList<T> source,
        Func<T, IReadOnlyList<T>?> children, Func<T, IReadOnlyList<NeedPattern>?, NeedPattern> create) where T : class
    {
        if (source.Count == 0) return [];
        // A flat level translates each pattern on its own. Only a structural host-DAG node needs
        // the sharing memo below; a repeated capture node translated twice binds the same way.
        var structural = false;
        for (var i = 0; i < source.Count && !structural; i++) structural = children(source[i]) is not null;
        if (!structural)
        {
            var level = new NeedPattern[source.Count];
            for (var i = 0; i < level.Length; i++) level[i] = create(source[i], null);
            return level;
        }
        var memo = new Dictionary<T, NeedPattern>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<(T Pattern, bool Expanded)>();
        foreach (var root in source)
        {
            pending.Push((root, false));
            while (pending.TryPop(out var frame))
            {
                if (memo.ContainsKey(frame.Pattern)) continue;
                var nested = children(frame.Pattern);
                if (nested is null) { memo[frame.Pattern] = create(frame.Pattern, null); continue; }
                if (!frame.Expanded)
                {
                    pending.Push((frame.Pattern, true));
                    for (var i = nested.Count - 1; i >= 0; i--)
                        if (!memo.ContainsKey(nested[i])) pending.Push((nested[i], false));
                    continue;
                }
                memo[frame.Pattern] = create(frame.Pattern, nested.Select(child => memo[child]).ToArray());
            }
        }
        return source.Select(root => memo[root]).ToArray();
    }

    private static IReadOnlyList<NeedPattern> NeedParameterPatterns(IReadOnlyList<ParameterPattern> patterns)
        => TranslateNeedPatterns(patterns, ParameterPattern.StructuralItems,
            static (pattern, nested) => pattern switch
            {
                CaptureParameterPattern capture => new(capture.Name, capture.Kind == ParameterKind.Collecting, Original: pattern,
                    Meta: capture.Kind == ParameterKind.Meta),
                SequenceValueParameterPattern => new(Children: nested, Original: pattern),
                ListValueParameterPattern => new(Children: nested, List: true, Original: pattern),
                UnpackingParameterPattern => new(Children: nested, Unpacking: true, Original: pattern),
            });

    private static IReadOnlyList<NeedPattern> NeedClausePatterns(IReadOnlyList<Pattern> patterns)
        => TranslateNeedPatterns(patterns,
            static pattern => pattern switch { Pattern.SequenceValue group => group.Items, Pattern.ListValue group => group.Items, _ => null },
            static (pattern, nested) => pattern switch
            {
                Pattern.Bind binder => new(binder.Name, binder.ParameterKind == ParameterKind.Collecting),
                Pattern.SequenceValue => new(Children: nested),
                Pattern.ListValue => new(Children: nested, List: true),
                Pattern.LitInt or Pattern.LitString or Pattern.LitBool => new(Literal: pattern),
            });

    private static IReadOnlyList<NeedPattern> NeedClauseHead(Pattern pattern)
        => NeedClausePatterns(pattern is Pattern.SequenceValue group ? group.Items : [pattern]);

    // The binder reads the language's ONE supplied-slot rule (PatternLevelArity) over a
    // translated level. Lean keeps a binder-level twin, needMinimumSuppliedSlots /
    // needAcceptsCardinality, equal to it on every level the X-02 gate admits.
    private static PatternLevelArity NeedLevelArity(IReadOnlyList<NeedPattern> level)
    {
        for (var i = 0; i < level.Count; i++)
            if (level[i].Collecting) return new(level.Count, HasCollectingCapture: true);
        return new(level.Count, HasCollectingCapture: false);
    }

    private static int NeedMinimumSuppliedSlots(IReadOnlyList<NeedPattern> patterns)
        => NeedLevelArity(patterns).Minimum;

    private static bool NeedAcceptsCardinality(IReadOnlyList<NeedPattern> patterns, int supplied)
        => NeedLevelArity(patterns).Accepts(supplied);

    /// <summary>
    /// ALLOCATION of one ACCEPTED pattern level (VAR-02): the supplied cells the pattern at
    /// <paramref name="index"/> binds. That is ONE cell at <c>Start</c> (<c>Length</c> 1), or,
    /// for the level's first collecting capture <paramref name="collector"/> (-1 when none), the
    /// exact slice the fixed prefix and suffix leave over. This is pure index arithmetic. For every
    /// supply count <see cref="PatternLevelArity.Accepts"/> admits, every range lies inside the
    /// supply and each supplied cell falls in exactly one range, in written order. That holds
    /// whatever the level holds: a later collecting capture, which X-02 refuses before
    /// evaluation, takes one cell. Lean: <c>needSourceAt</c> / <c>needLevelSources</c>.
    /// </summary>
    internal static (int Start, int Length) NeedSourceRange(int patternCount, int collector, int supplied, int index)
    {
        var collected = supplied - patternCount + 1;
        return index == collector ? (index, collected)
            : (collector >= 0 && index > collector ? index + collected - 1 : index, 1);
    }

    /// <summary>
    /// THE ONE INSPECTING BINDER (NEED-04, PAT-10) behind its top-level CARDINALITY GATE. An
    /// unaccepted supply count is a clause family's non-match, and otherwise the binder's own
    /// <c>ArityMismatch</c> (the level's minimum against the complete supply count), decided before
    /// any demand. Lean: <c>bindNeedPatterns</c>, whose level runs <c>needCardinalityGate</c> first.
    /// The zero-supply binding uses it. Every other caller makes that one decision itself and then
    /// binds through <see cref="BindAcceptedNeedPatterns"/>. These are an ordinary call
    /// (<see cref="NeedCallArityError"/>), a user loop step (<c>LoopStateArityMismatch</c>) and a
    /// deconstruction (<see cref="BindNeedDeconstruction"/>), each reporting the rejection in its
    /// own shape. The family drivers decide per clause too, so no gate frame stays on the stack
    /// while a pattern demands a recursive argument.
    /// </summary>
    private static ValueTask<EvalResult<NeedEnv?>> BindNeedPatterns(
        IReadOnlyList<NeedPattern> patterns, IReadOnlyList<NeedCell> supply,
        EvalCtx ctx, bool asynchronous, bool family)
    {
        var arity = NeedLevelArity(patterns);
        return arity.Accepts(supply.Count)
            ? BindAcceptedNeedPatterns(patterns, supply, ctx, asynchronous, family)
            : new(family ? EvalResult<NeedEnv?>.Ok(null) : new EvalError.ArityMismatch(arity.Minimum, supply.Count));
    }

    /// <summary>
    /// The inspecting binder over a supply whose count its top-level patterns ACCEPT. The caller's
    /// cardinality gate has already decided that count, either <see cref="BindNeedPatterns"/> or a
    /// caller's own shaped report, so allocation here never re-checks it. Each structural level's
    /// own gate stays here, exactly once per level. Patterns traverse in written order, depth
    /// first: a unique plain name transports its cell, a repeated name, a literal or a structural
    /// pattern demands its cell when reached, and a collecting capture binds a lazy exact slice.
    /// </summary>
    private static async ValueTask<EvalResult<NeedEnv?>> BindAcceptedNeedPatterns(
        IReadOnlyList<NeedPattern> patterns, IReadOnlyList<NeedCell> supply,
        EvalCtx ctx, bool asynchronous, bool family)
    {
        // Empty and single-name heads need no traversal metadata. These are the same
        // non-inspecting binding rules as the general work-stack path.
        if (patterns.Count == 0) return EvalResult<NeedEnv?>.Ok([]);
        if (patterns.Count == 1 && patterns[0].Name is { } onlyName)
        {
            if (patterns[0].Meta)
            {
                var adapter = CaptureMeta(onlyName, supply[0], ctx);
                return adapter.IsError ? adapter.Error : EvalResult<NeedEnv?>.Ok([(onlyName, adapter.Value)]);
            }
            return EvalResult<NeedEnv?>.Ok([(onlyName, patterns[0].Collecting ? CollectorCell(supply.ToArray(), ctx) : supply[0])]);
        }

        // Multiplicity is only zero/one/many. Visit a shared pattern node at most twice,
        // so a host DAG cannot expand into exponentially many paths before binding.
        var names = new Dictionary<string, int>(StringComparer.Ordinal);
        var visits = new Dictionary<NeedPattern, int>(ReferenceEqualityComparer.Instance);
        var counting = new Stack<NeedPattern>(patterns);
        while (counting.TryPop(out var pattern))
        {
            var seen = visits.GetValueOrDefault(pattern);
            if (seen == 2) continue;
            visits[pattern] = seen + 1;
            if (pattern.Name is { } name) names[name] = Math.Min(2, names.GetValueOrDefault(name) + 1);
            else if (pattern.Children is { } children)
                foreach (var child in children) counting.Push(child);
        }
        var bound = new Dictionary<string, NeedCell>(StringComparer.Ordinal);
        var pending = new Stack<(NeedPattern Pattern, NeedCell Cell)>();
        // ONE charged comparison session per binder activation, created by the first repeated-name
        // comparison with structural work (SEC-02-FU): this head's agreements share its verdicts.
        Result.ValueSemanticComparer? repeatedValues = null;
        EvalResult<NeedEnv?> Mismatch(EvalError error)
            => family ? EvalResult<NeedEnv?>.Ok(null) : error;

        // Allocation of an ACCEPTED level (NeedSourceRange), pushed last-first so the pop
        // order is the written left-to-right order.
        void PushLevel(IReadOnlyList<NeedPattern> level, IReadOnlyList<NeedCell> cells)
        {
            var collector = -1;
            for (var i = 0; i < level.Count; i++) if (level[i].Collecting) { collector = i; break; }
            for (var i = level.Count - 1; i >= 0; i--)
            {
                var (start, length) = NeedSourceRange(level.Count, collector, cells.Count, i);
                NeedCell cell;
                if (i == collector)
                {
                    var slice = new NeedCell[length];
                    for (var j = 0; j < length; j++) slice[j] = cells[start + j];
                    cell = CollectorCell(slice, ctx);
                }
                else cell = cells[start];
                pending.Push((level[i], cell));
            }
        }

        PushLevel(patterns, supply);
        while (pending.TryPop(out var item))
        {
            var (pattern, cell) = item;
            // A META capture (CallReference S1) is reached in WRITTEN order like every pattern
            // (NEED-04): it reifies its supplied cell into a fresh Ready adapter — demanding
            // nothing, a non-plan cell refusing (named by the parameter, META-DIAG-1) — and binds
            // the name to that adapter.
            if (pattern.Meta)
            {
                var adapter = CaptureMeta(pattern.Name!, cell, ctx);
                if (adapter.IsError) return adapter.Error;
                cell = adapter.Value;
            }
            if (pattern.Name is { } name)
            {
                if (names[name] > 1)
                {
                    var value = asynchronous ? await cell.DemandAsync().ConfigureAwait(false) : cell.Demand();
                    if (value.IsError) return value.Error;
                    if (bound.TryGetValue(name, out var previous))
                    {
                        var before = asynchronous ? await previous.DemandAsync().ConfigureAwait(false) : previous.Demand();
                        if (before.IsError) return before.Error;
                        // NEED-04 (frozen): unequal VALUE contributions are the binder's BadArity;
                        // the context names the violated agreement. The comparison is charged
                        // (SEC-02-FU): its refusal is the run's terminal error, returned as is —
                        // never routed through Mismatch, so no later clause is ever tried.
                        if (before.Value.EmittedCount != value.Value.EmittedCount)
                            return Mismatch(new EvalError.WithContext(RepeatedParameterContext(name), new EvalError.BadArity()));
                        var agreed = RepeatedValueEquals(ref repeatedValues, before.Value.Value, value.Value.Value, ctx);
                        if (agreed.IsError) return agreed.Error;
                        if (!agreed.Value)
                            return Mismatch(new EvalError.WithContext(RepeatedParameterContext(name), new EvalError.BadArity()));
                        // META-S3-0b: the async binder awaits and consumes both outcomes directly.
                        var first = asynchronous ? await previous.ProjectCallableAsync().ConfigureAwait(false) : previous.ProjectCallable();
                        if (first.IsError) return first.Error;
                        var second = asynchronous ? await cell.ProjectCallableAsync().ConfigureAwait(false) : cell.ProjectCallable();
                        if (second.IsError) return second.Error;
                        if (first.Value is { } a && second.Value is { } b && !SameRepeatedCallableIdentity(a, b))
                            return Mismatch(new EvalError.TypeMismatch("Repeated bind equality requires the same callable identity"));
                        if (first.Value is not null || second.Value is null) continue;
                    }
                }
                bound[name] = cell;
                continue;
            }
            var outcome = asynchronous ? await cell.DemandAsync().ConfigureAwait(false) : cell.Demand();
            if (outcome.IsError) return outcome.Error;
            var inspected = outcome.Value.Value;
            if (pattern.Literal is { } literal)
            {
                var matched = MatchLiteralPattern(literal, inspected, ctx);
                if (matched.IsError) return matched.Error;
                if (!matched.Value)
                    return EvalResult<NeedEnv?>.Ok(null);
                continue;
            }
            var items = pattern.Unpacking ? inspected.SpreadItems() : pattern.List ? inspected.ListPatternItems() : inspected.SequencePatternItems();
            if (items is null)
                return family ? EvalResult<NeedEnv?>.Ok(null) : StructuralPatternKindMismatch(pattern.Original!, inspected);
            // The nested level's ONE cardinality gate (Lean: needCardinalityGate in bindNeedOne).
            // The unpacking receiver's mismatch stays the plain ArityMismatch its deconstruction
            // reports; a written structural pattern's mismatch names that pattern.
            var arity = NeedLevelArity(pattern.Children!);
            if (!arity.Accepts(items.Count))
                return family ? EvalResult<NeedEnv?>.Ok(null) : pattern.Unpacking
                    ? new EvalError.ArityMismatch(arity.Minimum, items.Count)
                    : StructuralPatternArityMismatch(pattern.Original!, arity.Minimum, items.Count);
            PushLevel(pattern.Children!, items.Select(value => NeedCell.Ready(new(value, value.ValueCount()))).ToArray());
        }
        // The dictionary's own (struct) enumeration order, as before, without a LINQ iterator and a
        // boxed enumerator per binding (PERF-ORD-1).
        var env = new (string Name, NeedCell Cell)[bound.Count];
        var next = 0;
        foreach (var (boundName, boundCell) in bound) env[next++] = (boundName, boundCell);
        return EvalResult<NeedEnv?>.Ok(env);
    }

    private static async ValueTask<EvalResult<IReadOnlyList<NeedCell>>> BindNeedDeconstruction(
        Algorithm.User helper, OutputBundle arguments, EvalCtx ctx, ValEnv values, bool asynchronous)
    {
        ctx.Observations?.RecordDeconstructionFullBind();
        var supply = await FormNeedSupply(arguments, ctx, values, asynchronous).ConfigureAwait(false);
        if (supply.IsError) return supply.Error;
        // The helper's cardinality comes first, before any demand (NEED-05). A parser helper takes
        // its one right-hand side, so only a host-modified helper can be refused here.
        var patterns = NeedParameterPatterns(helper.ParameterPatterns);
        var arity = NeedLevelArity(patterns);
        if (!arity.Accepts(supply.Value.Count))
            return DeconstructionArityMismatch(helper, new EvalError.ArityMismatch(arity.Minimum, supply.Value.Count));
        // The right-hand side's OWN failure belongs to the written right-hand side, never to the
        // assignment pattern. Demanding the one supplied cell before the binder raises that
        // failure unwrapped (pinned by DeconstructionBindingTests). For a parser helper, every
        // ArityMismatch the binder returns afterwards is then its own unpacking-level mismatch:
        // its demand of the cell is a memo hit, and the targets are names.
        if (supply.Value.Count == 1)
        {
            var inspected = await DemandCell(supply.Value[0], asynchronous).ConfigureAwait(false);
            if (inspected.IsError) return inspected.Error;
        }
        var bindings = await BindAcceptedNeedPatterns(patterns, supply.Value, ctx, asynchronous, family: false).ConfigureAwait(false);
        if (bindings.IsError)
            return bindings.Error is EvalError.ArityMismatch shape ? DeconstructionArityMismatch(helper, shape) : bindings.Error;
        var index = bindings.Value!.ToDictionary(binding => binding.Name, binding => binding.Cell, StringComparer.Ordinal);
        return EvalResult<IReadOnlyList<NeedCell>>.Ok(helper.Parameters.Select(parameter => index[parameter.Name]).ToArray());
    }

    // A deconstruction's OWN cardinality failure, named by its assignment pattern.
    private static EvalError DeconstructionArityMismatch(Algorithm.User helper, EvalError.ArityMismatch shape)
        => new EvalError.WithContext(new DeconstructionBindingContext(helper.Parameters.Select(parameter => parameter.DisplayName).ToList(),
            helper.Parameters.Any(parameter => parameter.Kind == ParameterKind.Collecting)), shape);

    internal static EvalCtx LoopNeedBindingContext(EvalCtx ctx, IReadOnlyList<string> names, IReadOnlyList<NeedCell> cells)
        => WithNeedBindings(ctx, names.Select((name, index) => (name, cells[index])).ToArray(), names);

    /// <summary>
    /// One iteration of the generic continuation a planned loop hands over to (and of nothing else):
    /// the iteration's step charge, then the ONE loop-step invocation over the established state slots
    /// (<see cref="InvokeLoopStepSupply"/>), exactly as <see cref="EvalNeedLoop"/> performs it.
    /// </summary>
    private static async ValueTask<EvalResult<IReadOnlyList<Result>?>> RunReadyNeedStepSlots(
        Algorithm step, IReadOnlyList<Result> state, EvalCtx ctx, ValEnv values, string loopName,
        CallDiagnosticName stepName, PreparedGenericLoopStep prepared, bool conditionFirst, bool asynchronous)
    {
        if (ctx.Budget.TryChargeStep() is { } limit) return limit;
        var cells = state.Select(value => NeedCell.Ready(new(value, value.ValueCount()))).ToArray();
        return await InvokeLoopStepSupply(step, prepared, cells, ctx, values, loopName, stepName, conditionFirst, asynchronous).ConfigureAwait(false);
    }

    /// <summary>
    /// A LOOP STEP IS AN ORDINARY CALLABLE INVOKED OVER THE CURRENT STATE SUPPLY (LOOP-08, Q-23 decided
    /// October 2026). The state slots are already a formed supply — Model-C cells, never re-opened,
    /// re-counted or demanded here — and the step is invoked on them by the callable's OWN ordinary
    /// machinery; the loop specializes only the RECEIVER: it reads the invocation as a ROW SUPPLY (the
    /// next state, LOOP-03) instead of as the call's one value. The receiver also fixes the ORDER in
    /// which a step body's rows are formed: <c>repeat</c> forms them left to right
    /// (<see cref="EvalAlgOutputSlots"/>); a <c>while</c> round (<paramref name="conditionFirst"/>)
    /// discovers its continuation flag first and forms the remaining rows only after a <c>true</c>
    /// verdict (<see cref="EvalWhileVerdictSlots"/>, LOOP-06), returning <c>null</c> for a
    /// <c>false</c> verdict and the next state otherwise. A <c>repeat</c> round never returns
    /// <c>null</c>.
    /// <list type="bullet">
    /// <item>A user algorithm (also a block, a Math member and a host operation, which are user-shaped)
    /// keeps its prepared loop binding: cardinality as the loop-state <see cref="LoopStateBindingContext"/>
    /// failure, the ONE inspecting binder, then its written rows (<see cref="EvalAlgOutputSlots"/>).</item>
    /// <item>A clause family is dispatched by the ordinary family dispatcher
    /// (<see cref="BindNeedFamilySupply"/>: cardinality, clause order, inspecting patterns where a
    /// successful mismatch tries the next clause and a runtime failure aborts, <c>NoMatchingBranch</c>,
    /// selected-branch materialization and activation); the selected clause's rows are the supply.</item>
    /// <item>A builtin runs through its ordinary argument roles (<see cref="ApplyBuiltinCountedResolved"/>,
    /// the callback arm's own route); it has no written rows, so its ONE result value is ONE non-spread
    /// row — <c>()</c> and collections included — never re-counted into zero or several slots; for
    /// <c>while</c> that one row is both the flag and the candidate state (<see cref="WhileVerdictOfSupply"/>).</item>
    /// </list>
    /// A family's or builtin's failure is its ordinary invocation failure under the step's own call
    /// frame; the loop adds only its outer frame. Nothing here charges a step or enters an invocation
    /// level: the caller charges one step per iteration, and a loop-step invocation stays outside the
    /// depth protocol for every callable shape, as it always was for user steps. Lean:
    /// <c>runNeedStepSlots</c>.
    /// </summary>
    private static async ValueTask<EvalResult<IReadOnlyList<Result>?>> InvokeLoopStepSupply(
        Algorithm step, PreparedGenericLoopStep prepared, IReadOnlyList<NeedCell> state, EvalCtx ctx, ValEnv values,
        string loopName, CallDiagnosticName stepName, bool conditionFirst, bool asynchronous)
    {
        switch (step)
        {
            case Algorithm.User:
            {
                var patterns = prepared.NeedPatterns;
                var arity = NeedLevelArity(patterns);
                if (!arity.Accepts(state.Count))
                    return LoopStateArityMismatch(prepared.BindingContract, arity.Minimum, state.Count, loopName);
                var bindings = await BindAcceptedNeedPatterns(patterns, state, ctx, asynchronous, family: false).ConfigureAwait(false);
                if (bindings.IsError) return bindings.Error;
                var names = prepared.BindingContract.ParameterNames;
                var stepCtx = WithNeedBindings(ctx, bindings.Value!, names);
                var stepValues = ShadowValEnv(values, names);
                return await ReadLoopStepRows(step, stepCtx, stepValues, names, conditionFirst, asynchronous).ConfigureAwait(false);
            }
            case Algorithm.Conditional:
            {
                var matched = asynchronous
                    ? await BindNeedFamilySupply(step, state, ctx, values, stepName, asynchronous: true).ConfigureAwait(false)
                    : BindNeedFamilySupplyCounted(step, state, ctx, values, stepName);
                if (matched.IsError) return WithCallCtx<IReadOnlyList<Result>?>(stepName, ctx, matched.Error);
                var activation = matched.Value;
                return WithCallCtx(stepName, ctx,
                    await ReadLoopStepRows(activation.Body, activation.Context, activation.Values, null, conditionFirst, asynchronous).ConfigureAwait(false));
            }
            case Algorithm.Builtin(var builtin):
            {
                var supplied = state.Select(static cell => new ResolvedArgumentAlgorithm(null) { Cell = cell }).ToArray();
                var result = asynchronous
                    ? await ApplyBuiltinCountedResolvedAsync(builtin, supplied, ctx, values).ConfigureAwait(false)
                    : ApplyBuiltinCountedResolved(builtin, supplied, ctx, values);
                if (result.IsError) return WithCallCtx<IReadOnlyList<Result>?>(stepName, ctx, result.Error);
                return conditionFirst
                    ? WhileVerdictOfSupply([result.Value.Value])
                    : EvalResult<IReadOnlyList<Result>?>.Ok([result.Value.Value]);
            }
            case Algorithm.Alias alias:
            {
                // A safety net out of line, as in every ordinary dispatcher: projection already normalizes
                // an alias to its target, which is invoked exactly as when written directly (FWD-02).
                var target = ResolveAliasTarget(alias, ctx);
                if (target.IsError) return target.Error;
                return await InvokeLoopStepSupply(target.Value, PrepareUserLoopStep(target.Value, ctx), state, ctx, values,
                    loopName, stepName, conditionFirst, asynchronous).ConfigureAwait(false);
            }
        }

        // A statement-form dispatch over the closed Algorithm hierarchy: the compiler cannot prove it
        // exhaustive, so an unhandled variant fails loudly rather than becoming a silent non-step.
        throw new InvalidOperationException($"Unhandled loop-step callable shape '{step.GetType().Name}'.");
    }

    /// <summary>
    /// The receiver's reading of an activated step body's rows: the <c>while</c> verdict reader or the
    /// <c>repeat</c> supply reader, each with its async mirror.
    /// </summary>
    private static async ValueTask<EvalResult<IReadOnlyList<Result>?>> ReadLoopStepRows(
        Algorithm body, EvalCtx ctx, ValEnv values, IReadOnlyList<string>? parameterNames, bool conditionFirst, bool asynchronous)
    {
        if (conditionFirst)
        {
            return asynchronous
                ? await EvalWhileVerdictSlotsAsync(body, ctx, values, parameterNames).ConfigureAwait(false)
                : EvalWhileVerdictSlots(body, ctx, values, parameterNames);
        }

        var supply = asynchronous
            ? await EvalAlgOutputSlotsAsync(body, ctx, values, parameterNames).ConfigureAwait(false)
            : EvalAlgOutputSlots(body, ctx, values, parameterNames);
        return supply.IsError ? supply.Error : EvalResult<IReadOnlyList<Result>?>.Ok(supply.Value);
    }

    /// <summary>
    /// The prepared loop binding of a USER-shaped step (<see cref="PrepareGenericLoopStep"/>); every other
    /// callable shape binds through its own ordinary dispatcher, so nothing is prepared for it.
    /// </summary>
    private static PreparedGenericLoopStep PrepareUserLoopStep(Algorithm step, EvalCtx ctx)
        => step is Algorithm.User ? PrepareGenericLoopStep(step, ctx) : default;

    /// <summary>
    /// The prepared loop binding of a planned loop's generic continuation after a handover: the
    /// ordinary preparation (<see cref="PrepareGenericLoopStep"/>) of the head the planner ADMITTED
    /// (<c>LoopPlanTemplate.AdmittedHead</c>), never of the step's caller-owned head as it is now.
    /// The view only derives the binding; the step itself is still what the iterations evaluate.
    /// Only a user step is ever planned.
    /// </summary>
    private static PreparedGenericLoopStep PrepareAdmittedLoopStep(
        Algorithm step, IReadOnlyList<ParameterPattern> admittedHead, EvalCtx ctx)
        => step is Algorithm.User user ? PrepareGenericLoopStep(user with { ParameterPatterns = admittedHead }, ctx) : default;

    /// <summary>
    /// The name of a loop step's own call frame (and of a family step's <c>NoMatchingBranch</c>): the written
    /// expression its SUPPLY CELL retains — the step argument as written or, for a cell transported through a
    /// parameter, the argument originally written for it (<see cref="SupplyCell"/>) — named as the ordinary call
    /// names its callee; a cell with no written source (a spread item) is the loop's step. Lean: <c>loopStepName</c>.
    /// </summary>
    private static CallDiagnosticName StepDiagnosticName(ResolvedArgumentAlgorithm step, string loopName)
        => (step.Cell is { } cell ? cell.Source : step.Source) is { } source
            ? CallDiagnosticName.FromExpression(source)
            : CallDiagnosticName.FromKnown(loopName + " step");

    private static EvalCtx WithNeedBindings(EvalCtx ctx, NeedEnv bindings, IReadOnlyList<string> names)
    {
        var inherited = ShadowInheritedParameterEnvironments(ctx, names);
        return inherited.WithNeedEnv(Concat(bindings, inherited.NeedEnv));
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalNeedUserBodyCounted(
        Algorithm callee, OutputBundle arguments, EvalCtx ctx, ValEnv values, CallDiagnosticName name)
    {
        var supply = FormNeedSupply(arguments, ctx, values, asynchronous: false).GetAwaiter().GetResult();
        if (supply.IsError) return supply.Error;
        return EvalNeedUserSupplyCounted(callee, supply.Value, ctx, values, name, variadicArityStyle: true);
    }

    private static EvalError NeedCallArityError(Algorithm callee, IReadOnlyList<NeedPattern> patterns, int supplied, CallDiagnosticName name, EvalCtx ctx, bool variadicStyle)
    {
        var renderedName = name.Render(ctx);
        var arity = NeedLevelArity(patterns);
        return variadicStyle && arity.HasCollectingCapture && patterns.All(pattern => pattern.Name is not null)
            ? new EvalError.VariadicArityMismatch(renderedName, arity.Minimum, supplied) { Signature = CallableSignature.FromAlgorithm(renderedName, callee) }
            : new EvalError.ArityMismatch(arity.Minimum, supplied) { Signature = CallableSignature.FromAlgorithm(renderedName, callee), InferredImplicitParameters = ImplicitParameterProvenance.CollectFrom(callee.Parameters) };
    }

    // A call result crosses the call's value boundary (VAL-06: ONE value, counted by ValueCount),
    // for an ordinary call and a map/filter/reduce callback invocation alike (HO-03, Q-25 resolved
    // October 2026). `variadicArityStyle` only shapes the CARDINALITY diagnostic: an ordinary call
    // reports a collecting callee's arity failure as VariadicArityMismatch, while a callback
    // invocation keeps the plain ArityMismatch shape named by its role. It never changes a result.
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalNeedUserSupplyCounted(
        Algorithm callee, IReadOnlyList<NeedCell> supply, EvalCtx ctx, ValEnv values, CallDiagnosticName name, bool variadicArityStyle)
    {
        // The call's ONE top-level cardinality decision, reported in the call's own shape.
        var patterns = NeedParameterPatterns(callee.ParameterPatterns);
        if (!NeedAcceptsCardinality(patterns, supply.Count)) return NeedCallArityError(callee, patterns, supply.Count, name, ctx, variadicArityStyle);
        var bindings = BindAcceptedNeedPatterns(patterns, supply, ctx, asynchronous: false, family: false).GetAwaiter().GetResult();
        if (bindings.IsError) return bindings.Error;
        if (callee.Output.Count == 0) return new EvalError.MissingOutput();
        var names = callee.Params;
        if (ctx.Budget.MayReachRuntimeAliases && TakeTerminalAliasInvocation(callee, ctx) is { } terminalCell)
            return ReCountValueBoundary(terminalCell.Demand());
        return ReCountValueBoundary(EvalAlgOutputCounted(callee, WithNeedBindings(ctx, bindings.Value!, names), ShadowValEnv(values, names)));
    }

    private static async ValueTask<EvalResult<CountedResult>> EvalNeedUserBody(
        Algorithm callee, OutputBundle arguments, EvalCtx ctx, ValEnv values,
        CallDiagnosticName name, bool asynchronous)
    {
        var supply = await FormNeedSupply(arguments, ctx, values, asynchronous).ConfigureAwait(false);
        if (supply.IsError) return supply.Error;
        return await EvalNeedUserSupply(callee, supply.Value, ctx, values, name, asynchronous, variadicArityStyle: true).ConfigureAwait(false);
    }

    private static async ValueTask<EvalResult<CountedResult>> EvalNeedUserSupply(
        Algorithm callee, IReadOnlyList<NeedCell> supply, EvalCtx ctx, ValEnv values,
        CallDiagnosticName name, bool asynchronous, bool variadicArityStyle)
    {
        var patterns = NeedParameterPatterns(callee.ParameterPatterns);
        if (!NeedAcceptsCardinality(patterns, supply.Count)) return NeedCallArityError(callee, patterns, supply.Count, name, ctx, variadicArityStyle);
        var bindings = await BindAcceptedNeedPatterns(patterns, supply, ctx, asynchronous, family: false).ConfigureAwait(false);
        if (bindings.IsError) return bindings.Error;
        if (callee.Output.Count == 0) return new EvalError.MissingOutput();
        var names = callee.Params;
        var boundCtx = WithNeedBindings(ctx, bindings.Value!, names);
        var boundValues = ShadowValEnv(values, names);
        if (TakeTerminalAliasInvocation(callee, ctx) is { } terminalCell)
            return ReCountValueBoundary(await DemandCell(terminalCell, asynchronous).ConfigureAwait(false));
        return ReCountValueBoundary(asynchronous
            ? await EvalAlgOutputCountedCoreAsync(callee, boundCtx, boundValues).ConfigureAwait(false)
            : EvalAlgOutputCounted(callee, boundCtx, boundValues));
    }

    /// <summary>
    /// One callback invocation of a higher-order builtin (the map transform, the filter predicate,
    /// the reduce step) over already-evaluated values, each ONE Ready cell bound by the callee's own
    /// ordinary machinery (HO-02). The invocation IS the ordinary call (HO-03, Q-25 resolved October
    /// 2026): a user algorithm and a clause family alike (PAT-11: a family is an ordinary callable)
    /// return their ordinary call result — the ONE value the call boundary delivers, several rows
    /// arriving as one sequence value — and a builtin's one result is already a value. The receiving
    /// builtin uses that value whole: map stores it as one element, reduce passes it as the next
    /// accumulator, filter reads its Boolean. A callback's arity failure keeps the plain
    /// <c>ArityMismatch</c> shape (<c>variadicArityStyle: false</c>), its only difference from an
    /// ordinary call. Lean: <c>evalUserCallbackCallCounted</c> / <c>evalConditionalCallbackCallCounted</c>.
    /// </summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalNeedCallbackBody(
        Algorithm callee, IReadOnlyList<CountedResult> arguments, EvalCtx ctx, ValEnv values,
        string name, bool asynchronous)
    {
        var supply = arguments.Select(argument => NeedCell.Ready(argument)).ToArray();
        if (callee is Algorithm.Builtin builtin)
        {
            var resolved = supply.Select(cell => new ResolvedArgumentAlgorithm(null) { Cell = cell }).ToArray();
            return asynchronous ? await ApplyBuiltinCountedResolvedAsync(builtin.Id, resolved, ctx, values).ConfigureAwait(false)
                : ApplyBuiltinCountedResolved(builtin.Id, resolved, ctx, values);
        }
        return callee is Algorithm.Conditional
            ? await EvalNeedFamilySupply(callee, supply, ctx, values, CallDiagnosticName.FromKnown(name), asynchronous).ConfigureAwait(false)
            : await EvalNeedUserSupply(callee, supply, ctx, values, CallDiagnosticName.FromKnown(name), asynchronous, variadicArityStyle: false).ConfigureAwait(false);
    }

    private static async ValueTask<EvalResult<CountedResult>> EvalNeedFamilyBody(
        Algorithm callee, OutputBundle arguments, EvalCtx ctx, ValEnv values,
        CallDiagnosticName name, bool asynchronous)
    {
        var supply = await FormNeedSupply(arguments, ctx, values, asynchronous).ConfigureAwait(false);
        if (supply.IsError) return supply.Error;
        return await EvalNeedFamilySupply(callee, supply.Value, ctx, values, name, asynchronous).ConfigureAwait(false);
    }

    private readonly record struct NeedFamilyActivation(Algorithm Body, EvalCtx Context, ValEnv Values);

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalNeedFamilyBodyCounted(
        Algorithm callee, OutputBundle arguments, EvalCtx ctx, ValEnv values, CallDiagnosticName name)
    {
        var supply = FormNeedSupply(arguments, ctx, values, asynchronous: false).GetAwaiter().GetResult();
        if (supply.IsError) return supply.Error;
        return EvalNeedFamilySupplyCounted(callee, supply.Value, ctx, values, name);
    }

    // The family twins of the user drivers above: ONE dispatch (BindNeedFamilySupply*), then the
    // selected body's counted output at the call's value boundary — for an ordinary call and a
    // callback invocation alike (HO-03, PAT-11). Lean: evalNeedFamilySupply.
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalNeedFamilySupplyCounted(
        Algorithm callee, IReadOnlyList<NeedCell> supply, EvalCtx ctx, ValEnv values, CallDiagnosticName name)
    {
        var matched = BindNeedFamilySupplyCounted(callee, supply, ctx, values, name);
        if (matched.IsError) return matched.Error;
        return ReCountValueBoundary(EvalAlgOutputCounted(matched.Value.Body, matched.Value.Context, matched.Value.Values));
    }

    private static async ValueTask<EvalResult<CountedResult>> EvalNeedFamilySupply(
        Algorithm callee, IReadOnlyList<NeedCell> supply, EvalCtx ctx, ValEnv values,
        CallDiagnosticName name, bool asynchronous)
    {
        var matched = await BindNeedFamilySupply(callee, supply, ctx, values, name, asynchronous).ConfigureAwait(false);
        if (matched.IsError) return matched.Error;
        return ReCountValueBoundary(asynchronous
            ? await EvalAlgOutputCountedCoreAsync(matched.Value.Body, matched.Value.Context, matched.Value.Values).ConfigureAwait(false)
            : EvalAlgOutputCounted(matched.Value.Body, matched.Value.Context, matched.Value.Values));
    }

    // The FAMILY-level decision before any clause (Lean: selectNeedFamilyBranch). First come the
    // duplicate heads. Then, if no clause's head accepts the supply count, the call is an
    // ArityMismatch with the first clause's minimum (0 when there is no clause). Which clause binds
    // is each clause's own gate afterwards, in written order: the driver's per-clause check, where a
    // refused count is that clause's non-match, then BindAcceptedNeedPatterns in family mode.
    private static EvalResult<IReadOnlyList<IReadOnlyList<NeedPattern>>> PrepareNeedFamilyHeads(
        Algorithm callee, int supplied)
    {
        if (callee.HasDuplicateBranchPatterns()) return new EvalError.DuplicateBranchPattern();
        var branches = callee.Branches;
        var heads = new IReadOnlyList<NeedPattern>[branches.Count];
        var accepted = false;
        for (var i = 0; i < heads.Length; i++)
        {
            heads[i] = NeedClauseHead(branches[i].Pattern);
            accepted = accepted || NeedAcceptsCardinality(heads[i], supplied);
        }
        return accepted
            ? EvalResult<IReadOnlyList<IReadOnlyList<NeedPattern>>>.Ok(heads)
            : new EvalError.ArityMismatch(heads.Length == 0 ? 0 : NeedMinimumSuppliedSlots(heads[0]), supplied);
    }

    // The clause-attempt observation both family drivers share (SEC-02-FU2, ClauseAttemptObservations):
    // an attempt is recorded just before the clause's binder, which may demand its supplied values,
    // and its outcome from the binder's own result. Passive — a null observer records nothing, and
    // no call demands, checkpoints, or decides anything. The opt-in collector owns dispatch/attempt
    // bookkeeping: no observation locals or extra frames survive across a recursive binder demand.
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    private static void ObserveFamilyStart(Algorithm callee, in EvalCtx ctx)
        => ctx.Observations?.ClauseAttempts?.BeginDispatch(callee);

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    private static void ObserveClauseAttempt(int clause, in EvalCtx ctx)
        => ctx.Observations?.ClauseAttempts?.RecordAttempt(clause);

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    private static void ObserveClauseOutcome(in EvalResult<NeedEnv?> bindings, in EvalCtx ctx)
    {
        if (ctx.Observations?.ClauseAttempts is not { } observer) return;
        observer.RecordOutcome(bindings.IsError ? ClauseAttemptOutcome.Error
            : bindings.Value is null ? ClauseAttemptOutcome.NonMatch : ClauseAttemptOutcome.Matched);
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    private static void ObserveFamilyUnmatched(in EvalCtx ctx)
        => ctx.Observations?.ClauseAttempts?.EndUnmatchedDispatch();

    private static NeedFamilyActivation ActivateNeedFamilyBranch(
        Algorithm callee, Algorithm selected, NeedEnv matched, EvalCtx ctx, ValEnv values)
    {
        var names = matched.Select(binding => binding.Name).ToArray();
        var boundCtx = WithNeedBindings(ctx.Push(callee), matched, names);
        var boundValues = ShadowValEnv(values, names);
        return new(ChildOfConditionalCall(callee, selected, names, boundCtx, boundValues), boundCtx, boundValues);
    }

    // The synchronous driver avoids retaining an async continuation frame while a literal
    // pattern demands a recursive argument. Both drivers use the same supply, binder and
    // activation operations; only deferred branch materialization may actually suspend.
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<NeedFamilyActivation> BindNeedFamilySupplyCounted(
        Algorithm callee, IReadOnlyList<NeedCell> supply, EvalCtx ctx, ValEnv values, CallDiagnosticName name)
    {
        var prepared = PrepareNeedFamilyHeads(callee, supply.Count);
        if (prepared.IsError) return prepared.Error;
        var heads = prepared.Value;
        ObserveFamilyStart(callee, ctx);
        for (var i = 0; i < heads.Count; i++)
        {
            // The clause's ONE cardinality gate, in family mode: a refused count is its non-match.
            // Decided here rather than in a gated binder frame, so a literal or structural pattern
            // that demands a recursive argument holds no extra frame (stack headroom per level).
            if (!NeedAcceptsCardinality(heads[i], supply.Count)) continue;
            ObserveClauseAttempt(i, ctx);
            var bindings = BindAcceptedNeedPatterns(heads[i], supply, ctx, asynchronous: false, family: true).GetAwaiter().GetResult();
            ObserveClauseOutcome(bindings, ctx);
            if (bindings.IsError) return bindings.Error;
            if (bindings.Value is not { } matched) continue;
            return EvalResult<NeedFamilyActivation>.Ok(ActivateNeedFamilyBranch(callee, SelectedBranchBody(callee.Branches[i]), matched, ctx, values));
        }
        ObserveFamilyUnmatched(ctx);
        return new EvalError.NoMatchingBranch(name.Render(ctx));
    }

    /// <summary>MIRROR OF the synchronous family driver; shared operations own every binding rule.</summary>
    private static async ValueTask<EvalResult<NeedFamilyActivation>> BindNeedFamilySupply(
        Algorithm callee, IReadOnlyList<NeedCell> supply, EvalCtx ctx, ValEnv values,
        CallDiagnosticName name, bool asynchronous)
    {
        var prepared = PrepareNeedFamilyHeads(callee, supply.Count);
        if (prepared.IsError) return prepared.Error;
        var heads = prepared.Value;
        ObserveFamilyStart(callee, ctx);
        for (var i = 0; i < heads.Count; i++)
        {
            if (!NeedAcceptsCardinality(heads[i], supply.Count)) continue;
            ObserveClauseAttempt(i, ctx);
            var bindings = await BindAcceptedNeedPatterns(heads[i], supply, ctx, asynchronous, family: true).ConfigureAwait(false);
            ObserveClauseOutcome(bindings, ctx);
            if (bindings.IsError) return bindings.Error;
            if (bindings.Value is not { } matched) continue;
            var selected = asynchronous
                ? await SelectedBranchBodyAsync(callee.Branches[i], ctx).ConfigureAwait(false)
                : EvalResult<Algorithm>.Ok(SelectedBranchBody(callee.Branches[i]));
            if (selected.IsError) return selected.Error;
            return EvalResult<NeedFamilyActivation>.Ok(ActivateNeedFamilyBranch(callee, selected.Value, matched, ctx, values));
        }
        ObserveFamilyUnmatched(ctx);
        return new EvalError.NoMatchingBranch(name.Render(ctx));
    }

    private static NeedCell ExistingArgumentCell(ResolvedArgumentAlgorithm argument, EvalCtx ctx, ValEnv values)
        => argument.Cell ?? new NeedCell(() => EvalResolvedArgumentCounted(argument, ctx, values),
            () => EvalResolvedArgumentCountedAsync(argument, ctx, values),
            () => EvalResult<Algorithm?>.Ok(argument.Algorithm),
            argument.Source?.Span, source: argument.Source, budget: ctx.Budget, token: ctx.Budget.CancellationToken);

    /// <summary>
    /// THE NATIVE LOOP KERNEL of <c>while</c>/<c>repeat</c> over its logical components (META-S3-3): the
    /// step argument (the captured plan's canonical callee cell), the remaining iteration count of a
    /// <c>repeat</c> (already demanded and validated, RP-1; ignored by <c>while</c>), and the initial
    /// state cells (the captured plan's ONE sticky supply, possibly empty, OD-1). The step's CALLABLE is
    /// projected only when an iteration needs it; <c>while</c> rounds read their flag condition first
    /// (LOOP-CF1); the optimizer (<see cref="LoopOptimizer"/>) is tried once the step is projected; the
    /// final state is materialized at the one result site (<see cref="MakeCheckedLoopStateResult"/>).
    /// Lean: the loop arms of <c>applyBuiltinCounted</c> after <c>metaLoopCapture</c>.
    /// </summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalNeedLoop(
        BuiltinId builtin, ResolvedArgumentAlgorithm stepArgument, long remaining,
        IReadOnlyList<NeedCell> state, EvalCtx ctx, ValEnv values, bool asynchronous)
    {
        var repeat = builtin == BuiltinId.@repeat;
        ctx.LoopDiagnostics?.RecordLoopExecution();

        Algorithm? step = null;
        PreparedGenericLoopStep prepared = default;
        var loopName = repeat ? "repeat" : "while";
        // The step's written spelling names its own call frame (LOOP-08): a family's or builtin's
        // ordinary failure is reported under it, exactly as the ordinary call reports it.
        var stepName = StepDiagnosticName(stepArgument, loopName);
        while (!repeat || remaining > 0)
        {
            if (step is null)
            {
                // CALLABLE projection only now, when an iteration needs the step: a zero-iteration
                // `repeat` never projects or validates it (LOOP-05), and a step argument with no
                // CALLABLE identity is NotAnAlgorithm (Q-06, LOOP-08), never a VALUE demand.
                // META-S3-0b: the async loop consumes the awaited projection outcome through the
                // async resolution adapter (same slot, same point, same diagnostics).
                var projection = asynchronous
                    ? await ProjectLoopStepAsync(stepArgument, builtin, ctx).ConfigureAwait(false)
                    : ProjectLoopStep(stepArgument, builtin);
                if (projection.IsError) return projection.Error;
                step = projection.Value;
                var eligible = IsOptimizedLoopShapeEligible(step, out var shapeFallback);
                if (!asynchronous && ctx.EnableLoopOptimization && eligible)
                {
                    EvalResult<CountedResult> optimized;
                    var taken = repeat
                        ? LoopOptimizer.TryEvaluateRepeat(step, remaining, state, ctx, values,
                            (admittedHead, count, slots) => RepeatLoopGenericCounted(step, admittedHead, count, slots, ctx, values, stepName), out optimized)
                        : LoopOptimizer.TryEvaluateWhile(step, state, ctx, values,
                            (admittedHead, slots) => WhileLoopGenericCounted(step, admittedHead, slots, ctx, values, stepName), out optimized);
                    if (taken) return optimized;
                    // The planner refused the step and already recorded that ONE fallback under
                    // its own reason (OPT-FB-1); it is not recorded again here.
                }
                else
                {
                    // No plan was attempted: this loop entry owns the fallback.
                    ctx.LoopDiagnostics?.RecordOptimizedLoopFallback(asynchronous || !ctx.EnableLoopOptimization ? "loop optimization disabled" : shapeFallback ?? "loop plan unsupported step shape");
                }
                prepared = PrepareUserLoopStep(step, ctx);
            }
            if (ctx.Budget.TryChargeStep() is { } limit) return limit;
            // A `while` round reads its step condition first (LOOP-06): `null` is a false verdict,
            // and the state that entered the round is the loop's final state.
            var output = await InvokeLoopStepSupply(step, prepared, state, ctx, values, loopName, stepName,
                conditionFirst: !repeat, asynchronous).ConfigureAwait(false);
            if (output.IsError) return output.Error;
            if (output.Value is not { } next) break;
            state = next.Select(item => NeedCell.Ready(new(item, item.ValueCount()))).ToArray();
            if (repeat) remaining--;
        }
        var materialized = new List<Result>(state.Count);
        foreach (var cell in state)
        {
            var value = await DemandCell(cell, asynchronous).ConfigureAwait(false);
            if (value.IsError) return value.Error;
            materialized.Add(value.Value.Value);
        }
        return MakeCheckedLoopStateResult(ctx, materialized);
    }
}
