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
/// Calls: lazy argument-to-algorithm resolution, call-expression evaluation, conditional-algorithm calls, and user-defined calls (the "Resolve argument expressions to algorithms (lazy)", "Call evaluation", "Conditional algorithm call", and "User-defined call" sections).
/// Part of the <see cref="Evaluator"/> partial class; the central state, lookup and open resolution,
/// the built-in prelude, and the run entry points remain in <c>Evaluator.cs</c>.
/// </summary>
public static partial class Evaluator
{
    // ── Resolve argument expressions to algorithms (lazy) ───────────────────

    /// <summary>
    /// Resolve each output expression of args to sub-algorithms.
    /// Lean: resolveArgAlgExpr per argument (the list form is
    /// resolveArgAlgsWithSequenceSpread, which also tags spread
    /// arguments) — wraps only liftable errors (notAnAlgorithm,
    /// illegalInEval) in trivial algorithms for lazy evaluation via evalAlgOutput.
    /// All other errors (unknownName, unknownProperty, ambiguousOpen, etc.)
    /// are propagated immediately to preserve precise diagnostics.
    /// </summary>
    /// <summary>
    /// True when an argument expression supplies ONLY a value in argument
    /// position. A capture is a value boundary: it suppresses the algorithm
    /// identity of anything inside it, so higher-order probing never sees the
    /// enclosed content as callable. <see cref="Expr.AlgorithmExpr"/> is
    /// deliberately NOT value-only: an algorithm block explicitly exposes its
    /// contained Algorithm on the algorithm channel regardless of
    /// parameter/declaration/output count — <c>{42}</c> is as much an
    /// Algorithm as <c>{a + 1}</c> — while the value channel reifies the
    /// written slot independently.
    /// </summary>
    private static bool ShouldWrapArgExprAsValue(Expr expr) => expr is Expr.Capture;

    /// <summary>
    /// Builtin argument adapters reify each written slot as one value-producing
    /// adapter. A zero-declaration algorithm block slot keeps its one-slot
    /// value boundary here (written-slot reification: <c>repeat(step, n, {1, 2})</c>
    /// supplies ONE initial state slot), exactly as before the block's
    /// algorithm identity became visible to user-call higher-order binding.
    /// Blocks with parameters, properties, or opens still resolve as
    /// algorithms for algorithm-consuming builtin arguments (callbacks).
    /// </summary>
    private static bool IsZeroDeclarationBlockValueSlot(Expr expr) => expr is
        Expr.AlgorithmExpr(var algorithm)
            && algorithm.Params.Count == 0
            && algorithm.Opens.Count == 0
            && algorithm.Properties.Count == 0;

    private static Algorithm WrapArgExprAsValue(Expr expr, EvalCtx ctx)
        => WireToCaller(
            ctx,
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: [expr]));

    private static bool ShouldWrapBuiltinArgExprAsValue(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => ShouldWrapArgExprAsValue(expr)
            || IsZeroDeclarationBlockValueSlot(expr)
            || expr is Expr.Param(var name)
                && (LookupCountedParam(ctx.CountedParamEnv, name) is not null
                    || LookupVal(valEnv, name) is not null);

    private static EvalResult<IReadOnlyList<Algorithm>> ResolveArgAlgs(
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var resolvedR = ResolveArgAlgsWithSequenceSpread(args, ctx, valEnv);
        if (resolvedR.IsError) return resolvedR.Error;

        var algorithms = new List<Algorithm>(resolvedR.Value.Count);
        foreach (var arg in resolvedR.Value)
        {
            if (arg.Algorithm is null)
                return new EvalError.BadArity();
            algorithms.Add(arg.Algorithm);
        }

        return EvalResult<IReadOnlyList<Algorithm>>.Ok(algorithms);
    }

    private static EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>> ResolveArgAlgsWithSequenceSpread(
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var result = new List<ResolvedArgumentAlgorithm>(args.Count);
        foreach (var argExpr in args)
        {
            var spreadsSequence = argExpr is Expr.SequenceSpread;
            if (ShouldWrapBuiltinArgExprAsValue(argExpr, ctx, valEnv))
            {
                result.Add(new ResolvedArgumentAlgorithm(WrapArgExprAsValue(argExpr, ctx), spreadsSequence));
                continue;
            }

            var r = ResolveAlg(argExpr, ctx);
            if (r.IsOk)
            {
                result.Add(new ResolvedArgumentAlgorithm(r.Value, spreadsSequence));
            }
            else if (IsLiftableError(r.Error))
            {
                // Wrap liftable non-resolvable expressions in a trivial algorithm.
                // evalAlgOutput will evaluate the expression lazily when needed.
                var wrapper = new Algorithm.User(
                    Parent: null, Parameters: [], Opens: [],
                    Properties: [], Output: [argExpr]);
                result.Add(new ResolvedArgumentAlgorithm(WireToCaller(ctx, wrapper), spreadsSequence));
            }
            else
            {
                // Propagate genuine lookup/semantic failures immediately.
                return r.Error;
            }
        }
        return EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>>.Ok(result);
    }

    /// <summary>
    /// Errors that indicate an expression simply isn't an algorithm form and can
    /// safely be deferred to lazy evaluation (wrapping in Algorithm.ofExpr).
    /// </summary>
    private static bool IsLiftableError(EvalError error) => error switch
    {
        EvalError.NotAnAlgorithm => true,
        EvalError.IllegalInEval => true,
        EvalError.WithContext(_, var inner) => IsLiftableError(inner),
        _ => false,
    };

    /// <summary>
    /// Try to resolve each argument expression to an algorithm.
    /// Returns Some(alg) for expressions that resolve, null for those that don't.
    /// A capture slot never yields a candidate (a capture is a value boundary
    /// and suppresses enclosed identity); an algorithm block always yields its
    /// contained Algorithm, regardless of parameter/declaration/output count —
    /// <c>Call0({42})</c> binds the brace algorithm exactly like
    /// <c>Call0(Const)</c> binds a named zero-parameter property.
    /// Lean: tryResolveArgAlgs.
    /// </summary>
    private static EvalResult<IReadOnlyList<Algorithm?>> TryResolveArgAlgs(
        OutputBundle args, EvalCtx ctx)
    {
        var result = new List<Algorithm?>(args.Count);
        foreach (var argExpr in args)
        {
            if (ShouldWrapArgExprAsValue(argExpr))
            {
                result.Add(null);
                continue;
            }

            var r = ResolveAlg(argExpr, ctx);
            if (r.IsOk)
            {
                result.Add(r.Value);
            }
            else if (IsLiftableError(r.Error))
            {
                result.Add(null);
            }
            else
            {
                return r.Error;
            }
        }
        return EvalResult<IReadOnlyList<Algorithm?>>.Ok(result);
    }

    // ── Call evaluation ─────────────────────────────────────────────────────

    /// <summary>
    /// Lean: evalCallExpr → EvalM Result (Lean also attaches the call-context wrapper there).
    /// 1. Resolve callee.
    /// 2. If builtin: resolve args lazily as algorithms, dispatch to applyBuiltin.
    /// 3. If user-defined: delegate to EvalUserCall (dual-view argument binding).
    /// </summary>
    /// <summary>
    /// Context-aware call evaluation for expression position with plain
    /// Result output. This is the value projection of
    /// <see cref="EvalCallCountedExpr"/>: the counted twin owns callee
    /// resolution, the sequence-pipeline hook, dispatch, and the call
    /// error-context attachment, so contexts and spans cannot drift between
    /// the plain and counted spellings.
    /// Lean: evalCallExpr (the projection of evalCallCountedExpr).
    /// </summary>
    private static EvalResult<Result> EvalCallExpr(
        Expr func,
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => ProjectCountedValue(EvalCallCountedExpr(func, args, ctx, valEnv));

    /// <summary>
    /// Counted expression-position call evaluation — the CANONICAL
    /// expression-position call dispatch (<see cref="EvalCallExpr"/> is its
    /// value projection).
    /// Lean: evalCallCountedExpr.
    /// </summary>
    private static EvalResult<CountedResult> EvalCallCountedExpr(
        Expr func,
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var diagnosticName = CallDiagnosticName.FromExpression(func);
        var calleeR = ResolveAlg(func, ctx);
        if (calleeR.IsError)
            return new EvalError.WithContext(CtxCall(diagnosticName, ctx), calleeR.Error) { Span = calleeR.Error.Span };

        if (TryEvaluateSequencePipeline(
            SequencePipelineInvocation.PlainCall(func, args, calleeR.Value),
            ctx,
            valEnv,
            out var sequencePipelineR))
            return WithCallCtx(diagnosticName, ctx, sequencePipelineR);

        return WithCallCtx(
            diagnosticName,
            ctx,
            EvalResolvedCallCounted(calleeR.Value, args, ctx, valEnv, diagnosticName));
    }

    // ── [HOST] B2c: deferred module regions at the branch-selection boundary ──

    /// <summary>
    /// The body a SELECTED conditional branch evaluates. An ordinary branch evaluates its
    /// written body; a branch whose body is a deferred module region
    /// (<see cref="DeferredModuleRegions"/>) evaluates its MATERIALIZED body — the one
    /// eager elaboration would have produced, so the core rules from here on are unchanged.
    /// The synchronous family can only use a materialization that already exists: producing
    /// one awaits the module downloader, which the async family does through
    /// <see cref="SelectedBranchBodyAsync"/>. Every synchronous entry point rejects a root
    /// carrying deferred regions before evaluating, so reaching an unmaterialized region here
    /// means a deferred-region tree was evaluated through a synchronous path — a host
    /// configuration error, reported fail-loud exactly like the async-only host-operation
    /// rejections, never as a KatLang diagnostic.
    /// </summary>
    private static Algorithm SelectedBranchBody(CondBranch branch)
    {
        if (!DeferredModuleRegions.TryGet(branch.Body, out var region))
            return branch.Body;

        if (region.TryGetMaterialized(out var materialized))
            return materialized;

        throw DeferredModuleRegions.SynchronousSelectionNotSupported();
    }

    /// <summary>
    /// MIRROR OF <see cref="SelectedBranchBody"/> for the async twin family: materializes
    /// the selected branch's deferred module region on first selection (awaiting its module
    /// loads through the owning loader), reuses the cached materialization afterwards, and
    /// surfaces a failed materialization as the structured
    /// <see cref="EvalError.ModuleRegionMaterializationFailed"/> carrying the module
    /// diagnostics with their branch-local provenance.
    /// </summary>
    private static async ValueTask<EvalResult<Algorithm>> SelectedBranchBodyAsync(CondBranch branch, EvalCtx ctx)
    {
        if (!DeferredModuleRegions.TryGet(branch.Body, out var region))
            return EvalResult<Algorithm>.Ok(branch.Body);

        if (region.TryGetMaterialized(out var materialized))
            return EvalResult<Algorithm>.Ok(materialized);

        return await region.MaterializeAsync(ctx.Budget.CancellationToken).ConfigureAwait(false);
    }

    // ── Conditional algorithm call (Lean: evalConditionalCallCounted) ───────

    /// <summary>
    /// Assemble the evaluated argument values for a conditional (multi-clause)
    /// call through the shared call argument pipeline
    /// (<see cref="BuildCallArgumentInputs"/>): non-spread slots reify as one
    /// value each and explicit spread expands by one value boundary, exactly
    /// as for every other callable shape. Clause matching needs plain values,
    /// so an algorithm-only argument surfaces its value-evaluation error.
    /// </summary>
    private static EvalResult<IReadOnlyList<Result>> EvalConditionalCallArguments(
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallArgumentAssembly argumentAssembly)
    {
        var inputsR = BuildCallArgumentInputs(args, ctx, valEnv, argumentAssembly);
        if (inputsR.IsError) return inputsR.Error;

        var argResults = new List<Result>(inputsR.Value.Count);
        foreach (var input in inputsR.Value)
        {
            if (input.Value is null)
                return input.ValueError ?? new EvalError.BadArity();

            argResults.Add(input.Value);
        }

        return EvalResult<IReadOnlyList<Result>>.Ok(argResults);
    }

    /// <summary>
    /// Counted conditional call evaluation — the CANONICAL conditional-call
    /// implementation (the plain spelling reaches it through
    /// <see cref="EvalResolvedCallCounted"/> and the value projection).
    /// 1. Assemble the argument supply through the shared call argument
    ///    pipeline (explicit spread expands into ordinary argument slots
    ///    BEFORE clause matching, so a multi-clause callee sees the same
    ///    supply as every other callable shape).
    /// 2. Try branches in order; first match wins.
    /// 3. Evaluate the selected branch body with pattern bindings prepended.
    /// 4. If no branch matches, raise NoMatchingBranch.
    ///
    /// <para><b>Full-input-specification rule</b>: the branch body receives input
    /// bindings ONLY from the matched pattern. No extra implicit parameters are
    /// inferred. Free identifiers in the body resolve through ordinary lexical /
    /// property / open / builtin lookup, or produce unknownName at runtime.</para>
    ///
    /// <para><b>Assumes uniform output arity</b>: after validation
    /// (<see cref="CondBranch.TopLevelOutputArity"/>), all branches produce the
    /// same top-level output arity. The evaluator does not re-check this at
    /// runtime.</para>
    ///
    /// The selected branch is a value boundary, so its public result re-counts
    /// the emitted arity with <see cref="ReCountValueBoundary"/>
    /// (<c>Result.ValueCount</c>) — a multi-output branch becomes one sequence
    /// value (count 1), matching <c>if</c> and plain calls.
    /// Lean: <c>evalConditionalCallCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalConditionalCallCounted(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallDiagnosticName calleeName,
        CallArgumentAssembly argumentAssembly = CallArgumentAssembly.OrdinaryArguments)
    {
        // Charged dynamic invocation boundary; this counted core owns the
        // boundary for both counted evaluation and its plain projection.
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return AtSpanIfMissing(limitError, FirstSpan(args));

        try
        {
            return EvalConditionalCallCountedCore(callee, args, ctx, valEnv, calleeName, argumentAssembly);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    private static EvalResult<CountedResult> EvalConditionalCallCountedCore(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallDiagnosticName calleeName,
        CallArgumentAssembly argumentAssembly)
    {
        var argResultsR = EvalConditionalCallArguments(args, ctx, valEnv, argumentAssembly);
        if (argResultsR.IsError) return argResultsR.Error;
        var argResults = argResultsR.Value;

        if (callee.HasDuplicateBranchPatterns())
            return new EvalError.DuplicateBranchPattern();

        var match = MatchCallBranches(callee.Branches, argResults);
        if (match is null)
            return new EvalError.NoMatchingBranch(calleeName.Render(ctx));

        var (branch, bindings) = match.Value;
        var wiredBody = ChildOf(callee, SelectedBranchBody(branch));
        var shadowedNames = bindings.Select(static binding => binding.Item1).ToArray();
        var newCtx = ctx.Push(callee)
            .WithCountedParamEnv(ShadowCountedParamEnv(ctx.CountedParamEnv, shadowedNames));
        var newEnv = Concat(bindings, valEnv);
        return ReCountValueBoundary(EvalAlgOutputCounted(wiredBody, newCtx, newEnv));
    }

    // ── User-defined call (Lean: evalUserCallCounted) ─────────────────────

    /// <summary>
    /// Counted user-defined call evaluation — the CANONICAL user-call
    /// implementation (the plain spelling reaches it through
    /// <see cref="EvalResolvedCallCounted"/> and the value projection).
    ///
    /// Dual-view semantics: each original argument expression is independently
    /// interpreted in two ways:
    /// <list type="bullet">
    ///   <item>Structural algorithm resolution → AlgEnv (callable meaning)</item>
    ///   <item>Eager value evaluation → ValEnv (value meaning)</item>
    /// </list>
    /// If both succeed, the parameter gets both meanings (dual-view).
    /// If only algorithm resolution succeeds, only AlgEnv is bound.
    /// If only value evaluation succeeds, only ValEnv is bound.
    /// If both fail, the eager-evaluation error is propagated. Every
    /// <see cref="Expr.AlgorithmExpr"/> contributes its contained algorithm to
    /// the AlgEnv side regardless of declaration/output count. A
    /// <see cref="Expr.Capture"/> contributes only its fresh zero-parameter
    /// value thunk, never the algorithm identity of an expression it contains.
    ///
    /// Flat fixed calls bind call-site structure: each comma argument is one
    /// argument expression, while a bare spread expression explicitly
    /// contributes its spread top-level items. Multi-output values from normal
    /// expressions, including <c>.atoms</c>, remain one argument expression.
    /// Earlier explicit argument positions remain distinct on the eager value
    /// side even if some later arguments bind only through AlgEnv.
    ///
    /// A user/property call is a value boundary: the public result preserves
    /// the structural value while re-counting the emitted arity with
    /// <see cref="ReCountValueBoundary"/> (<c>Result.ValueCount</c>). A
    /// multi-output body therefore becomes one sequence value (count 1); only
    /// caller-site <c>spread</c> re-spreads it.
    /// Lean: <c>evalUserCallCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalUserCallCounted(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallArgumentAssembly argumentAssembly,
        CallDiagnosticName calleeName)
    {
        // Charged dynamic invocation boundary (see EvaluationBudget).
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return AtSpanIfMissing(limitError, FirstSpan(args));

        try
        {
            return EvalUserCallCountedCore(callee, args, ctx, valEnv, argumentAssembly, calleeName);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    private static EvalResult<CountedResult> EvalUserCallCountedCore(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallArgumentAssembly argumentAssembly,
        CallDiagnosticName calleeName)
    {
        if (callee.Output.Count == 0)
            return new EvalError.MissingOutput();

        // Assignment-deconstruction target: project this target's slot from the group's shared
        // run-scoped bind. The projected value is re-counted at this value boundary exactly as the
        // helper body's `Param(xi)` result would be (`ReCountValueBoundary`): count = ValueCount().
        if (callee is Algorithm.User { IsAssignmentDeconstructionHelper: true } deconstructionHelper
            && TryProjectSharedDeconstructionTarget(deconstructionHelper, args, ctx, valEnv, calleeName, argumentAssembly) is { } sharedTarget)
        {
            return sharedTarget.IsError
                ? sharedTarget.Error
                : EvalResult<CountedResult>.Ok(new CountedResult(sharedTarget.Value, sharedTarget.Value.ValueCount()));
        }

        var signature = CallableSignature.FromAlgorithm(calleeName.StructuralName, callee);
        var bindingPlan = CallableBindingPlan.FromSignature(signature);

        if (bindingPlan.RequiresPatternedBinding)
        {
            var bindingsR = BindPatternedUserCall(callee, args, ctx, valEnv, calleeName, argumentAssembly);
            if (bindingsR.IsError) return bindingsR.Error;

            var bindings = bindingsR.Value;
            var grouped = WithUserCallBindingEnvironments(ctx, bindings, valEnv, callee.Params);
            return ReCountValueBoundary(EvalAlgOutputCounted(callee, grouped.Context, grouped.ValueEnvironment));
        }

        if (IsDeconstructionUserCallShape(signature))
        {
            var bindingsR = BindDeconstructionUserCall(callee, args, ctx, valEnv, calleeName, argumentAssembly);
            if (bindingsR.IsError) return bindingsR.Error;

            var bindings = bindingsR.Value;
            var deconstruction = WithUserCallBindingEnvironments(ctx, bindings, valEnv, callee.Params);
            return ReCountValueBoundary(EvalAlgOutputCounted(callee, deconstruction.Context, deconstruction.ValueEnvironment));
        }

        if (!TryGetPlanDerivedFlatFixedParameterNames(bindingPlan, out var flatFixedParams))
            flatFixedParams = callee.Params;

        var flatBindingsR = BindFlatFixedUserCallArguments(
            callee,
            calleeName,
            flatFixedParams,
            args,
            ctx,
            valEnv);
        if (flatBindingsR.IsError) return flatBindingsR.Error;

        var flatBindings = flatBindingsR.Value;
        return ReCountValueBoundary(EvalAlgOutputCounted(callee, flatBindings.Context, flatBindings.ValueEnvironment));
    }

    /// <summary>
    /// Counted dispatch for an already-resolved effective callee — the
    /// CANONICAL resolved-callee dispatch (builtin / flat-binder-equivalent /
    /// conditional / user); plain consumers reach it through the value
    /// projection of their counted entry points.
    /// Lean: <c>evalResolvedCallCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalResolvedCallCounted(
        Algorithm callee,
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallDiagnosticName calleeName,
        CallArgumentAssembly argumentAssembly = CallArgumentAssembly.OrdinaryArguments)
    {
        if (callee is Algorithm.Builtin(var builtinId))
        {
            var argAlgsR = ResolveArgAlgsWithSequenceSpread(args, ctx, valEnv);
            if (argAlgsR.IsError) return argAlgsR.Error;
            return ApplyBuiltinCountedResolved(builtinId, argAlgsR.Value, ctx, valEnv);
        }

        if (TryGetFlatBinderUserEquivalent(callee) is { } simpleCallee)
            return EvalUserCallCounted(
                simpleCallee,
                args,
                ctx,
                valEnv,
                argumentAssembly,
                calleeName);

        if (callee is Algorithm.Conditional)
            return EvalConditionalCallCounted(callee, args, ctx, valEnv, calleeName, argumentAssembly);

        return EvalUserCallCounted(
            callee,
            args,
            ctx,
            valEnv,
            argumentAssembly,
            calleeName);
    }
}
