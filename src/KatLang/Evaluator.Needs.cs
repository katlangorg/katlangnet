using KatLang.Optimizations.Loops;
using KatLang.Evaluation;

namespace KatLang;

public static partial class Evaluator
{
    private static NeedCell? LookupNeed(NeedEnv env, string name)
    {
        foreach (var binding in env)
            if (binding.Name == name) return binding.Cell;
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
        return LookupAlg(activation?.Algorithms ?? ctx.AlgEnv, name) is { } algorithm
            ? EvalResult<Algorithm>.Ok(algorithm)
            : new EvalError.NotAnAlgorithm($"param({name})") { Span = span };
    }

    private static EvalResult<CountedResult> DemandParameter(NeedCell cell, EvalResult<CountedResult> result, string name, SourceSpan? span)
        => result.IsError && cell.Slice is null && cell.Source is Expr.AlgorithmExpr
            ? ParameterSlotFailure(name, span, result.Error) : result;

    internal static NeedCell SupplyCell(Expr expression, EvalCtx caller, ValEnv values)
    {
        if (expression is Expr.Param(var name))
        {
            var parameterCtx = ParameterContext(name, caller, ref values);
            if (LookupNeed(parameterCtx.NeedEnv, name) is { } existing) return existing;
        }
        var retainedValues = values;
        EvalResult<Algorithm?> Project()
        {
            if (expression is Expr.DotCall edge)
            {
                if (edge.Args is not null || edge.UsesOrdinaryDotStringIntrinsic()) return EvalResult<Algorithm?>.Ok(null);
                var member = ResolveDotReceiver(edge, caller, out var structural);
                if (member.IsError) return IsLiftableError(member.Error) ? EvalResult<Algorithm?>.Ok(null) : member.Error;
                if (!structural) return EvalResult<Algorithm?>.Ok(null);
                var target = member.Value is Algorithm.Alias alias ? ResolveAliasTarget(alias, caller) : EvalResult<Algorithm>.Ok(member.Value);
                return target.IsError ? target.Error : EvalResult<Algorithm?>.Ok(target.Value);
            }
            if (ShouldWrapArgExprAsValue(expression)) return EvalResult<Algorithm?>.Ok(null);
            var resolved = ResolveAlg(expression, caller);
            return resolved.IsOk ? EvalResult<Algorithm?>.Ok(resolved.Value)
                : IsLiftableError(resolved.Error) ? EvalResult<Algorithm?>.Ok(null) : resolved.Error;
        }
        EvalResult<CountedResult> Finish(EvalResult<CountedResult> result)
            => result.IsError ? BlameWrittenArgumentSlot(expression, result.Error) : ReCountValueBoundary(result);
        return new NeedCell(
            () => Finish(EvalCounted(expression, caller, retainedValues)),
            async () => Finish(await EvalCountedAsync(expression, caller, retainedValues).ConfigureAwait(false)),
            Project, expression.Span, source: expression, budget: caller.Budget, token: caller.Budget.CancellationToken);
    }

    // Sync formation has no suspending operation. Both engines execute this one ordered
    // supply algorithm; only the evaluation of an arbitrary spread has an async twin.
    private static async ValueTask<EvalResult<IReadOnlyList<NeedCell>>> FormNeedSupply(
        OutputBundle arguments, EvalCtx caller, ValEnv values, bool asynchronous, List<Expr?>? sources = null)
    {
        var supply = new List<NeedCell>(arguments.Count);
        foreach (var argument in arguments)
        {
            if (argument is not Expr.SequenceSpread(var operand))
            {
                supply.Add(SupplyCell(argument, caller, values));
                sources?.Add(argument);
                continue;
            }
            var cell = SupplyCell(operand, caller, values);
            if (cell.Slice is { } known)
            {
                supply.AddRange(known);
                if (sources is not null) sources.AddRange(known.Select(static cell => cell.Source));
                continue;
            }
            // EvalSequenceSpreadCounted owns output-less spread diagnostics and opening.
            var opened = asynchronous
                ? await EvalCountedAsync(argument, caller, values).ConfigureAwait(false)
                : EvalCounted(argument, caller, values);
            if (opened.IsError) return opened.Error;
            foreach (var item in CountedTopLevelValues(opened.Value))
            {
                supply.Add(NeedCell.Ready(new(item, item.ValueCount())));
                sources?.Add(null);
            }
        }
        return EvalResult<IReadOnlyList<NeedCell>>.Ok(supply);
    }

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
            formed.Value.Select((cell, index) => new ResolvedArgumentAlgorithm(null, false) { Cell = cell, Source = sources[index] }).ToArray());
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

    private sealed record NeedPattern(
        string? Name = null, bool Collecting = false,
        IReadOnlyList<NeedPattern>? Children = null, bool List = false, Pattern? Literal = null, bool Unpacking = false, ParameterPattern? Original = null);

    // Translation preserves reference sharing and uses explicit post-order frames. The
    // structural preflight has already rejected cyclic patterns before evaluation begins.
    private static IReadOnlyList<NeedPattern> TranslateNeedPatterns<T>(IReadOnlyList<T> source,
        Func<T, IReadOnlyList<T>?> children, Func<T, IReadOnlyList<NeedPattern>?, NeedPattern> create) where T : class
    {
        if (source.Count == 0) return [];
        if (source.Count == 1 && children(source[0]) is null) return [create(source[0], null)];
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
                CaptureParameterPattern capture => new(capture.Name, capture.Kind == ParameterKind.Collecting, Original: pattern),
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

    private static int NeedMinimumSuppliedSlots(IReadOnlyList<NeedPattern> patterns)
        => patterns.Count - patterns.Count(pattern => pattern.Collecting);

    private static bool NeedAcceptsCardinality(IReadOnlyList<NeedPattern> patterns, int supplied)
        => supplied >= NeedMinimumSuppliedSlots(patterns)
            && (patterns.Any(pattern => pattern.Collecting) || supplied == patterns.Count);

    private static async ValueTask<EvalResult<NeedEnv?>> BindNeedPatterns(
        IReadOnlyList<NeedPattern> patterns, IReadOnlyList<NeedCell> supply,
        EvalCtx ctx, bool asynchronous, bool family)
    {
        // Empty and single-name heads need no traversal metadata. These are the same
        // cardinality and non-inspecting binding rules as the general work-stack path.
        if (!NeedAcceptsCardinality(patterns, supply.Count))
            return family ? EvalResult<NeedEnv?>.Ok(null) : new EvalError.ArityMismatch(NeedMinimumSuppliedSlots(patterns), supply.Count);
        if (patterns.Count == 0) return EvalResult<NeedEnv?>.Ok([]);
        if (patterns.Count == 1 && patterns[0].Name is { } onlyName)
            return EvalResult<NeedEnv?>.Ok([(onlyName, patterns[0].Collecting ? CollectorCell(supply.ToArray(), ctx) : supply[0])]);

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
        EvalResult<NeedEnv?> Mismatch(EvalError error)
            => family ? EvalResult<NeedEnv?>.Ok(null) : error;

        EvalError? PushLevel(IReadOnlyList<NeedPattern> level, IReadOnlyList<NeedCell> cells)
        {
            if (!NeedAcceptsCardinality(level, cells.Count))
                return new EvalError.ArityMismatch(NeedMinimumSuppliedSlots(level), cells.Count);
            var collector = -1;
            for (var i = 0; i < level.Count; i++) if (level[i].Collecting) { collector = i; break; }
            var extra = cells.Count - level.Count + 1;
            for (var i = level.Count - 1; i >= 0; i--)
            {
                var cell = i == collector
                    ? CollectorCell(cells.Skip(i).Take(extra).ToArray(), ctx)
                    : cells[collector >= 0 && i > collector ? i + extra - 1 : i];
                pending.Push((level[i], cell));
            }
            return null;
        }

        if (PushLevel(patterns, supply) is { } cardinality) return Mismatch(cardinality);
        while (pending.TryPop(out var item))
        {
            var (pattern, cell) = item;
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
                        // the context names the violated agreement.
                        if (before.Value.EmittedCount != value.Value.EmittedCount || !Result.ValueComparer.Equals(before.Value.Value, value.Value.Value))
                            return Mismatch(new EvalError.WithContext(RepeatedParameterContext(name), new EvalError.BadArity()));
                        var first = previous.ProjectCallable();
                        if (first.IsError) return first.Error;
                        var second = cell.ProjectCallable();
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
                if (!MatchPattern(literal, inspected, new List<(string Name, Result Value)>()))
                    return EvalResult<NeedEnv?>.Ok(null);
                continue;
            }
            var items = pattern.Unpacking ? inspected.SpreadItems() : pattern.List ? inspected.ListPatternItems() : inspected.SequencePatternItems();
            if (items is null)
                return family ? EvalResult<NeedEnv?>.Ok(null) : StructuralPatternKindMismatch(pattern.Original!, inspected);
            if (!NeedAcceptsCardinality(pattern.Children!, items.Count))
            {
                var minimum = NeedMinimumSuppliedSlots(pattern.Children!);
                return family ? EvalResult<NeedEnv?>.Ok(null) : pattern.Unpacking
                    ? new EvalError.ArityMismatch(minimum, items.Count)
                    : StructuralPatternArityMismatch(pattern.Original!, minimum, items.Count);
            }
            var ready = items.Select(value => NeedCell.Ready(new(value, value.ValueCount()))).ToArray();
            if (PushLevel(pattern.Children!, ready) is { } nestedCardinality) return Mismatch(nestedCardinality);
        }
        return EvalResult<NeedEnv?>.Ok(bound.Select(pair => (pair.Key, pair.Value)).ToArray());
    }

    private static async ValueTask<EvalResult<IReadOnlyList<NeedCell>>> BindNeedDeconstruction(
        Algorithm.User helper, OutputBundle arguments, EvalCtx ctx, ValEnv values, bool asynchronous)
    {
        ctx.Observations?.RecordDeconstructionFullBind();
        var supply = await FormNeedSupply(arguments, ctx, values, asynchronous).ConfigureAwait(false);
        if (supply.IsError) return supply.Error;
        if (supply.Value.Count == 1)
        {
            var inspected = await DemandCell(supply.Value[0], asynchronous).ConfigureAwait(false);
            if (inspected.IsError) return inspected.Error;
        }
        var bindings = await BindNeedPatterns(NeedParameterPatterns(helper.ParameterPatterns), supply.Value, ctx, asynchronous, family: false).ConfigureAwait(false);
        if (bindings.IsError)
        {
            if (bindings.Error is EvalError.ArityMismatch shape)
                return new EvalError.WithContext(new DeconstructionBindingContext(helper.Parameters.Select(parameter => parameter.DisplayName).ToList(),
                    helper.Parameters.Any(parameter => parameter.Kind == ParameterKind.Collecting)), shape);
            return bindings.Error;
        }
        var index = bindings.Value!.ToDictionary(binding => binding.Name, binding => binding.Cell, StringComparer.Ordinal);
        return EvalResult<IReadOnlyList<NeedCell>>.Ok(helper.Parameters.Select(parameter => index[parameter.Name]).ToArray());
    }

    internal static EvalCtx LoopNeedBindingContext(EvalCtx ctx, IReadOnlyList<string> names, IReadOnlyList<NeedCell> cells)
        => WithNeedBindings(ctx, names.Select((name, index) => (name, cells[index])).ToArray(), names);

    /// <summary>
    /// One iteration of the generic continuation a planned loop hands over to (and of nothing else):
    /// the iteration's step charge, then the ONE loop-step invocation over the established state slots
    /// (<see cref="InvokeLoopStepSupply"/>), exactly as <see cref="EvalNeedLoop"/> performs it.
    /// </summary>
    private static async ValueTask<EvalResult<IReadOnlyList<Result>>> RunReadyNeedStepSlots(
        Algorithm step, IReadOnlyList<Result> state, EvalCtx ctx, ValEnv values, string loopName,
        CallDiagnosticName stepName, PreparedGenericLoopStep prepared, bool asynchronous)
    {
        if (ctx.Budget.TryChargeStep() is { } limit) return limit;
        var cells = state.Select(value => NeedCell.Ready(new(value, value.ValueCount()))).ToArray();
        return await InvokeLoopStepSupply(step, prepared, cells, ctx, values, loopName, stepName, asynchronous).ConfigureAwait(false);
    }

    /// <summary>
    /// A LOOP STEP IS AN ORDINARY CALLABLE INVOKED OVER THE CURRENT STATE SUPPLY (LOOP-08, Q-23 decided
    /// October 2026). The state slots are already a formed supply — Model-C cells, never re-opened,
    /// re-counted or demanded here — and the step is invoked on them by the callable's OWN ordinary
    /// machinery; the loop specializes only the RECEIVER: it reads the invocation as a ROW SUPPLY (the
    /// next state, LOOP-03) instead of as the call's one value.
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
    /// row — <c>()</c> and collections included — never re-counted into zero or several slots.</item>
    /// </list>
    /// A family's or builtin's failure is its ordinary invocation failure under the step's own call
    /// frame; the loop adds only its outer frame. Nothing here charges a step or enters an invocation
    /// level: the caller charges one step per iteration, and a loop-step invocation stays outside the
    /// depth protocol for every callable shape, as it always was for user steps. Lean:
    /// <c>runNeedStepSlots</c>.
    /// </summary>
    private static async ValueTask<EvalResult<IReadOnlyList<Result>>> InvokeLoopStepSupply(
        Algorithm step, PreparedGenericLoopStep prepared, IReadOnlyList<NeedCell> state, EvalCtx ctx, ValEnv values,
        string loopName, CallDiagnosticName stepName, bool asynchronous)
    {
        switch (step)
        {
            case Algorithm.User:
            {
                var patterns = prepared.NeedPatterns;
                if (!NeedAcceptsCardinality(patterns, state.Count))
                    return LoopStateArityMismatch(prepared.BindingContract, patterns.Count - patterns.Count(pattern => pattern.Collecting), state.Count, loopName);
                var bindings = await BindNeedPatterns(patterns, state, ctx, asynchronous, family: false).ConfigureAwait(false);
                if (bindings.IsError) return bindings.Error;
                var names = prepared.BindingContract.ParameterNames;
                var stepCtx = WithNeedBindings(ctx, bindings.Value!, names);
                var stepValues = ShadowValEnv(values, names);
                return asynchronous
                    ? await EvalAlgOutputSlotsAsync(step, stepCtx, stepValues, names).ConfigureAwait(false)
                    : EvalAlgOutputSlots(step, stepCtx, stepValues, names);
            }
            case Algorithm.Conditional:
            {
                var matched = asynchronous
                    ? await BindNeedFamilySupply(step, state, ctx, values, stepName, asynchronous: true).ConfigureAwait(false)
                    : BindNeedFamilySupplyCounted(step, state, ctx, values, stepName);
                if (matched.IsError) return WithCallCtx<IReadOnlyList<Result>>(stepName, ctx, matched.Error);
                var activation = matched.Value;
                return WithCallCtx(stepName, ctx, asynchronous
                    ? await EvalAlgOutputSlotsAsync(activation.Body, activation.Context, activation.Values).ConfigureAwait(false)
                    : EvalAlgOutputSlots(activation.Body, activation.Context, activation.Values));
            }
            case Algorithm.Builtin(var builtin):
            {
                var supplied = state.Select(static cell => new ResolvedArgumentAlgorithm(null, false) { Cell = cell }).ToArray();
                var result = asynchronous
                    ? await ApplyBuiltinCountedResolvedAsync(builtin, supplied, ctx, values).ConfigureAwait(false)
                    : ApplyBuiltinCountedResolved(builtin, supplied, ctx, values);
                return result.IsError
                    ? WithCallCtx<IReadOnlyList<Result>>(stepName, ctx, result.Error)
                    : EvalResult<IReadOnlyList<Result>>.Ok([result.Value.Value]);
            }
            case Algorithm.Alias alias:
            {
                // A safety net out of line, as in every ordinary dispatcher: projection already normalizes
                // an alias to its target, which is invoked exactly as when written directly (FWD-02).
                var target = ResolveAliasTarget(alias, ctx);
                if (target.IsError) return target.Error;
                return await InvokeLoopStepSupply(target.Value, PrepareUserLoopStep(target.Value, ctx), state, ctx, values,
                    loopName, stepName, asynchronous).ConfigureAwait(false);
            }
        }

        // A statement-form dispatch over the closed Algorithm hierarchy: the compiler cannot prove it
        // exhaustive, so an unhandled variant fails loudly rather than becoming a silent non-step.
        throw new InvalidOperationException($"Unhandled loop-step callable shape '{step.GetType().Name}'.");
    }

    /// <summary>
    /// The prepared loop binding of a USER-shaped step (<see cref="PrepareGenericLoopStep"/>); every other
    /// callable shape binds through its own ordinary dispatcher, so nothing is prepared for it.
    /// </summary>
    private static PreparedGenericLoopStep PrepareUserLoopStep(Algorithm step, EvalCtx ctx)
        => step is Algorithm.User ? PrepareGenericLoopStep(step, ctx) : default;

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
        return EvalNeedUserSupplyCounted(callee, supply.Value, ctx, values, name, recount: true);
    }

    private static EvalError NeedCallArityError(Algorithm callee, IReadOnlyList<NeedPattern> patterns, int supplied, CallDiagnosticName name, EvalCtx ctx, bool variadicStyle)
    {
        var renderedName = name.Render(ctx);
        var minimum = NeedMinimumSuppliedSlots(patterns);
        return variadicStyle && patterns.Any(pattern => pattern.Collecting) && patterns.All(pattern => pattern.Name is not null)
            ? new EvalError.VariadicArityMismatch(renderedName, minimum, supplied) { Signature = CallableSignature.FromAlgorithm(renderedName, callee) }
            : new EvalError.ArityMismatch(minimum, supplied) { Signature = CallableSignature.FromAlgorithm(renderedName, callee), InferredImplicitParameters = ImplicitParameterProvenance.CollectFrom(callee.Parameters) };
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalNeedUserSupplyCounted(
        Algorithm callee, IReadOnlyList<NeedCell> supply, EvalCtx ctx, ValEnv values, CallDiagnosticName name, bool recount)
    {
        var patterns = NeedParameterPatterns(callee.ParameterPatterns);
        if (!NeedAcceptsCardinality(patterns, supply.Count)) return NeedCallArityError(callee, patterns, supply.Count, name, ctx, recount);
        var bindings = BindNeedPatterns(patterns, supply, ctx, asynchronous: false, family: false).GetAwaiter().GetResult();
        if (bindings.IsError) return bindings.Error;
        if (callee.Output.Count == 0) return new EvalError.MissingOutput();
        var result = EvalAlgOutputCounted(callee, WithNeedBindings(ctx, bindings.Value!, callee.Params), ShadowValEnv(values, callee.Params));
        return recount ? ReCountValueBoundary(result) : result;
    }

    private static async ValueTask<EvalResult<CountedResult>> EvalNeedUserBody(
        Algorithm callee, OutputBundle arguments, EvalCtx ctx, ValEnv values,
        CallDiagnosticName name, bool asynchronous)
    {
        var supply = await FormNeedSupply(arguments, ctx, values, asynchronous).ConfigureAwait(false);
        if (supply.IsError) return supply.Error;
        return await EvalNeedUserSupply(callee, supply.Value, ctx, values, name, asynchronous, recount: true).ConfigureAwait(false);
    }

    private static async ValueTask<EvalResult<CountedResult>> EvalNeedUserSupply(
        Algorithm callee, IReadOnlyList<NeedCell> supply, EvalCtx ctx, ValEnv values,
        CallDiagnosticName name, bool asynchronous, bool recount)
    {
        var patterns = NeedParameterPatterns(callee.ParameterPatterns);
        if (!NeedAcceptsCardinality(patterns, supply.Count)) return NeedCallArityError(callee, patterns, supply.Count, name, ctx, recount);
        var bindings = await BindNeedPatterns(patterns, supply, ctx, asynchronous, family: false).ConfigureAwait(false);
        if (bindings.IsError) return bindings.Error;
        if (callee.Output.Count == 0) return new EvalError.MissingOutput();
        var boundCtx = WithNeedBindings(ctx, bindings.Value!, callee.Params);
        var boundValues = ShadowValEnv(values, callee.Params);
        var result = asynchronous
            ? await EvalAlgOutputCountedCoreAsync(callee, boundCtx, boundValues).ConfigureAwait(false)
            : EvalAlgOutputCounted(callee, boundCtx, boundValues);
        return recount ? ReCountValueBoundary(result) : result;
    }

    private static async ValueTask<EvalResult<CountedResult>> EvalNeedCallbackBody(
        Algorithm callee, IReadOnlyList<CountedResult> arguments, EvalCtx ctx, ValEnv values,
        string name, bool asynchronous)
    {
        var supply = arguments.Select(argument => NeedCell.Ready(argument)).ToArray();
        if (callee is Algorithm.Builtin builtin)
        {
            var resolved = supply.Select(cell => new ResolvedArgumentAlgorithm(null, false) { Cell = cell }).ToArray();
            return asynchronous ? await ApplyBuiltinCountedResolvedAsync(builtin.Id, resolved, ctx, values).ConfigureAwait(false)
                : ApplyBuiltinCountedResolved(builtin.Id, resolved, ctx, values);
        }
        return callee is Algorithm.Conditional
            ? await EvalNeedFamilySupply(callee, supply, ctx, values, CallDiagnosticName.FromKnown(name), asynchronous).ConfigureAwait(false)
            : await EvalNeedUserSupply(callee, supply, ctx, values, CallDiagnosticName.FromKnown(name), asynchronous, recount: false).ConfigureAwait(false);
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

    private static EvalResult<IReadOnlyList<IReadOnlyList<NeedPattern>>> PrepareNeedFamilyHeads(
        Algorithm callee, int supplied)
    {
        if (callee.HasDuplicateBranchPatterns()) return new EvalError.DuplicateBranchPattern();
        var heads = callee.Branches.Select(branch => NeedClauseHead(branch.Pattern)).ToArray();
        return heads.Any(head => NeedAcceptsCardinality(head, supplied))
            ? EvalResult<IReadOnlyList<IReadOnlyList<NeedPattern>>>.Ok(heads)
            : new EvalError.ArityMismatch(heads.Length == 0 ? 0 : NeedMinimumSuppliedSlots(heads[0]), supplied);
    }

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
        for (var i = 0; i < heads.Count; i++)
        {
            if (!NeedAcceptsCardinality(heads[i], supply.Count)) continue;
            var bindings = BindNeedPatterns(heads[i], supply, ctx, asynchronous: false, family: true).GetAwaiter().GetResult();
            if (bindings.IsError) return bindings.Error;
            if (bindings.Value is not { } matched) continue;
            return EvalResult<NeedFamilyActivation>.Ok(ActivateNeedFamilyBranch(callee, SelectedBranchBody(callee.Branches[i]), matched, ctx, values));
        }
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
        for (var i = 0; i < heads.Count; i++)
        {
            if (!NeedAcceptsCardinality(heads[i], supply.Count)) continue;
            var bindings = await BindNeedPatterns(heads[i], supply, ctx, asynchronous, family: true).ConfigureAwait(false);
            if (bindings.IsError) return bindings.Error;
            if (bindings.Value is not { } matched) continue;
            var selected = asynchronous
                ? await SelectedBranchBodyAsync(callee.Branches[i], ctx).ConfigureAwait(false)
                : EvalResult<Algorithm>.Ok(SelectedBranchBody(callee.Branches[i]));
            if (selected.IsError) return selected.Error;
            return EvalResult<NeedFamilyActivation>.Ok(ActivateNeedFamilyBranch(callee, selected.Value, matched, ctx, values));
        }
        return new EvalError.NoMatchingBranch(name.Render(ctx));
    }

    private static NeedCell ExistingArgumentCell(ResolvedArgumentAlgorithm argument, EvalCtx ctx, ValEnv values)
        => argument.Cell ?? (argument.PreparedValue is { } ready
            ? NeedCell.Ready(ready)
            : new NeedCell(() => EvalResolvedArgumentCounted(argument, ctx, values),
                () => EvalResolvedArgumentCountedAsync(argument, ctx, values),
                () => EvalResult<Algorithm?>.Ok(argument.InvokedAlgorithm),
                argument.Source?.Span, source: argument.Source, budget: ctx.Budget, token: ctx.Budget.CancellationToken));

    private static async ValueTask<EvalResult<CountedResult>> EvalNeedLoop(
        BuiltinId builtin, IReadOnlyList<ResolvedArgumentAlgorithm> arguments,
        EvalCtx ctx, ValEnv values, bool asynchronous)
    {
        var repeat = builtin == BuiltinId.@repeat;
        long remaining = long.MaxValue;
        if (repeat)
        {
            var count = await DemandCell(ExistingArgumentCell(arguments[1], ctx, values), asynchronous).ConfigureAwait(false);
            if (count.IsError) return count.Error;
            var integer = ExpectWholeInt(count.Value.Value, "Repeat count");
            if (integer.IsError) return integer.Error;
            if (integer.Value < 0) return new EvalError.IllegalInEval("Repeat count must be >= 0");
            remaining = integer.Value >= long.MaxValue ? long.MaxValue : (long)integer.Value;
        }
        IReadOnlyList<NeedCell> state = arguments.Skip(repeat ? 2 : 1)
            .Select(argument => ExistingArgumentCell(argument, ctx, values)).ToArray();
        ctx.LoopDiagnostics?.RecordLoopExecution();

        Algorithm? step = null;
        PreparedGenericLoopStep prepared = default;
        var loopName = repeat ? "repeat" : "while";
        // The step's written spelling names its own call frame (LOOP-08): a family's or builtin's
        // ordinary failure is reported under it, exactly as the ordinary call reports it.
        var stepName = StepDiagnosticName(arguments[0], loopName);
        while (!repeat || remaining > 0)
        {
            if (step is null)
            {
                // CALLABLE projection only now, when an iteration needs the step: a zero-iteration
                // `repeat` never projects or validates it (LOOP-05), and a step argument with no
                // CALLABLE identity is NotAnAlgorithm (Q-06, LOOP-08), never a VALUE demand.
                var projection = ProjectLoopStep(arguments[0], builtin);
                if (projection.IsError) return projection.Error;
                step = projection.Value;
                var eligible = IsOptimizedLoopShapeEligible(step, out var shapeFallback);
                if (!asynchronous && ctx.EnableLoopOptimization && eligible)
                {
                    EvalResult<CountedResult> optimized;
                    var taken = repeat
                        ? LoopOptimizer.TryEvaluateRepeat(step, remaining, state, ctx, values,
                            (count, slots) => RepeatLoopGenericCounted(step, count, slots, ctx, values, stepName), out optimized)
                        : LoopOptimizer.TryEvaluateWhile(step, state, ctx, values,
                            slots => WhileLoopGenericCounted(step, slots, ctx, values, stepName), out optimized);
                    if (taken) return optimized;
                }
                ctx.LoopDiagnostics?.RecordOptimizedLoopFallback(asynchronous || !ctx.EnableLoopOptimization ? "loop optimization disabled" : shapeFallback ?? "loop plan unsupported step shape");
                prepared = PrepareUserLoopStep(step, ctx);
            }
            if (ctx.Budget.TryChargeStep() is { } limit) return limit;
            var output = await InvokeLoopStepSupply(step, prepared, state, ctx, values, loopName, stepName, asynchronous).ConfigureAwait(false);
            if (output.IsError) return output.Error;
            IReadOnlyList<Result> next = output.Value;
            if (!repeat)
            {
                var split = SplitContSlots(next);
                if (split.IsError) return split.Error;
                if (!split.Value.Continue) break;
                next = split.Value.NextStateSlots;
            }
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
