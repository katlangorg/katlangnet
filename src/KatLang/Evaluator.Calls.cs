using System.Collections;
using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

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

    private static EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>> ResolveArgAlgsWithSequenceSpread(
        OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        return ResolveNeedSupply(args, ctx, valEnv, asynchronous: false).GetAwaiter().GetResult();
    }

    /// <summary>
    /// Errors that indicate an expression simply isn't an algorithm form and can
    /// have no independent callable identity. VALUE remains its suspended computation.
    /// A runtime CALLABLE projection's FAILURE (<see cref="EvalError.IsProjectionFailure"/>, at any
    /// wrapping depth) is never one: the computation failed, so its error propagates (NEED-06).
    /// </summary>
    private static bool IsLiftableError(EvalError error) => !error.IsProjectionFailure && error switch
    {
        EvalError.NotAnAlgorithm => true,
        EvalError.IllegalInEval => true,
        EvalError.WithContext(_, var inner) => IsLiftableError(inner),
        _ => false,
    };

    /// <summary>
    /// Whether an identity-resolution error is the completed FAILURE of a runtime CALLABLE
    /// projection, at any wrapping depth (META-S3-0b provenance) — never the static absence of
    /// an identity, whatever its kind.
    /// </summary>
    internal static bool IsProjectionFailure(EvalError error)
    {
        for (var current = error; ; current = ((EvalError.WithContext)current).Inner)
        {
            if (current.IsProjectionFailure) return true;
            if (current is not EvalError.WithContext) return false;
        }
    }

    /// <summary>
    /// The value-receiver routes' test "this receiver simply is not an algorithm" (a value
    /// receiver or a structural miss: static ABSENCE of identity, which a runtime projection
    /// FAILURE never is, NEED-06). Lean: the <c>notAnAlgorithm</c> catch of
    /// <c>resolveDotReceiver</c> / <c>projectNeedStructuralMember</c>.
    /// </summary>
    internal static bool IsAbsentIdentity(EvalError error)
        => error is EvalError.NotAnAlgorithm && !error.IsProjectionFailure;



    // ── Call evaluation ─────────────────────────────────────────────────────

    /// <summary>
    /// Lean: evalCallExpr → EvalM Result (Lean also attaches the call-context wrapper there).
    /// 1. Resolve callee.
    /// 2. If builtin: resolve args lazily as algorithms, dispatch to applyBuiltin.
    /// 3. If user-defined: delegate to EvalUserCallCounted (the need supply: cells formed,
    ///    cardinality checked before any demand, then the one need binder).
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
        ValEnv valEnv)
        => ProjectCountedValue(EvalCallCountedExpr(func, args, ctx, valEnv));

    /// <summary>
    /// The call-context frame around a callee that failed to RESOLVE, keeping the
    /// resolution error's own span. A non-inlined leaf so the span copy lives here, not in
    /// the call-recursion frame of <see cref="EvalCallCountedExpr"/> (frame-size discipline).
    /// A diagnostically transparent callee attaches no frame, exactly as in
    /// <see cref="WithCallCtx{T}"/>.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalError CalleeResolutionFailure(CallDiagnosticName diagnosticName, EvalCtx ctx, EvalError error)
        => diagnosticName.IsDiagnosticallyTransparent
            ? error
            : new EvalError.WithContext(CtxCall(diagnosticName, ctx), error) { Span = error.Span };

    /// <summary>
    /// The CALLABLE a call's CALLEE carries (DOT-09; Q-18 C-B3). A dot expression carries ONE
    /// callable identity in every algorithm-capable position, so a dot callee is read through
    /// the SAME projection a supplied argument is (<see cref="ProjectDotPathCallable"/>): an
    /// argumentless structural path is its member's own callable — <c>(Box.G)(2)</c> is the
    /// member call <c>Box.G(2)</c> and <c>(Box.V)()</c> the explicit fresh call <c>Box.V()</c>
    /// (grouping never changes identity) — and every other dot expression is a computed VALUE,
    /// which has no callable identity: <see cref="ComputedDotCalleeDescription"/>. (The parser
    /// admits a call after an argumentless dot edge only, so only a host-built tree can write a
    /// call after an argument-bearing one.) Every other callee shape resolves through canonical
    /// <see cref="ResolveAlg"/>. The ONE callee law of every call site: both evaluators and the
    /// sequence optimizer's recognition. Lean: <c>resolveCalleeAlg</c>.
    /// </summary>
    private static EvalResult<Algorithm> ResolveCallee(Expr callee, EvalCtx ctx)
        => callee is Expr.DotCall dotCallee ? ResolveDotCallee(dotCallee, ctx) : ResolveAlg(callee, ctx);

    /// <summary>
    /// The dot arm of <see cref="ResolveCallee"/>, out of line so its temporaries never enlarge
    /// the call-recursion frame (frame-size discipline).
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<Algorithm> ResolveDotCallee(Expr.DotCall callee, EvalCtx ctx)
    {
        var projected = ProjectDotPathCallable(callee, ctx);
        if (projected.IsError)
            return projected.Error;
        return projected.Value is { } member
            ? EvalResult<Algorithm>.Ok(member)
            : new EvalError.NotAnAlgorithm(ComputedDotCalleeDescription) { Span = callee.Span };
    }

    /// <summary>
    /// The structured <see cref="EvalError.NotAnAlgorithm"/> description of a dot expression
    /// in callee position that carries no callable identity — a computed VALUE (an extension
    /// call's or the <c>.string</c> intrinsic's result, a call result). Lean: the same payload
    /// in <c>resolveCalleeAlg</c>.
    /// </summary>
    internal const string ComputedDotCalleeDescription = "dot result";

    /// <summary>
    /// Counted expression-position call evaluation — the CANONICAL
    /// expression-position call dispatch (<see cref="EvalCallExpr"/> is its
    /// value projection). The callee is resolved by <see cref="ResolveCallee"/>.
    /// Lean: evalCallCountedExpr.
    /// </summary>
    private static EvalResult<CountedResult> EvalCallCountedExpr(
        Expr func,
        OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // META-S3-1: a callee spelled `X.Algorithm` is the call-reference intrinsic on a structural miss
        // (`(R.Algorithm)(x)` is the fresh call `R.Algorithm(x)`), decided out of line.
        if (IsAlgorithmEdgeCallee(func))
            return EvalAlgorithmCalleeCallCounted((Expr.DotCall)func, args, ctx, valEnv);

        var diagnosticName = CallDiagnosticName.FromExpression(func);
        var calleeR = ResolveCallee(func, ctx);
        if (calleeR.IsError)
            return CalleeResolutionFailure(diagnosticName, ctx, calleeR.Error);

        if (TryEvaluateSequencePipeline(
            SequencePipelineInvocation.PlainCall(func, args, calleeR.Value),
            ctx,
            valEnv,
            out var sequencePipelineR))
            return WithCallCtx(diagnosticName, ctx, sequencePipelineR);

        // CACHE-PUB-1: a call that may form an EMPTY supply of a publishable callee takes the
        // origin-carrying dispatch (its written callee names the property binding), decided out of line.
        if (MayFormZeroSupply(args) && TakesOriginDispatch(calleeR.Value))
            return EvalWrittenCalleeCallCounted(func, calleeR.Value, args, ctx, valEnv, diagnosticName);

        return WithCallCtx(
            diagnosticName,
            ctx,
            EvalResolvedCallCounted(calleeR.Value, args, ctx, valEnv, diagnosticName));
    }

    // ── [HOST] B2c: deferred module regions at the branch-selection boundary ──

    /// <summary>
    /// The body a SELECTED conditional branch evaluates. An ordinary branch evaluates its
    /// written body; a branch whose body is a deferred module region's placeholder
    /// (<see cref="Algorithm.DeferredRegion"/>) evaluates its MATERIALIZED body — the one
    /// eager elaboration would have produced, so the core rules from here on are unchanged.
    /// The synchronous family can only use a materialization that already exists: producing
    /// one awaits the module downloader, which the async family does through
    /// <see cref="SelectedBranchBodyAsync"/>. Every synchronous entry point rejects a root
    /// carrying deferred regions before evaluating, so reaching an unmaterialized region here
    /// means a deferred-region tree was evaluated through a synchronous path — a host
    /// configuration error, reported fail-loud exactly like the async-only host-operation
    /// rejections, never as a KatLang diagnostic.
    /// </summary>
    private static EvalResult<Algorithm> SelectedBranchBody(CondBranch branch, EvalCtx ctx)
        => branch.Body.DeferredRegion is { } region
            ? MaterializedRegionBody(region, ctx)
            : EvalResult<Algorithm>.Ok(branch.Body);

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
        if (branch.Body.DeferredRegion is not { } region)
            return EvalResult<Algorithm>.Ok(branch.Body);

        return await MaterializeRequiredRegionAsync(region, ctx).ConfigureAwait(false);
    }

    /// <summary>
    /// The synchronous family's ONE use of a deferred region: its EXISTING materialization (producing
    /// one awaits the downloader — see <see cref="SelectedBranchBody"/>), admitted for this run.
    /// </summary>
    private static EvalResult<Algorithm> MaterializedRegionBody(DeferredModuleRegion region, EvalCtx ctx)
    {
        if (!region.TryGetMaterialized(out var materialized))
            throw DeferredModuleRegion.SynchronousSelectionNotSupported();

        return AdmitMaterializedBody(region, materialized, ctx);
    }

    // THE evaluator's structural admission boundary for a materialized body, shared by every
    // consumer on both families, cached or freshly materialized alike: materialization proved the
    // body safe for the FRONT END, not for this run's evaluator profile, effective limit, and the
    // weighted position the placeholder occupies (DeferredBodyAdmission). A rejection is terminal.
    private static EvalResult<Algorithm> AdmitMaterializedBody(DeferredModuleRegion region, Algorithm body, EvalCtx ctx)
        => ctx.Budget.AdmitDeferredBody(region, body) is { } rejection
            ? rejection
            : EvalResult<Algorithm>.Ok(body);

    // Both evaluator materialization boundaries share source terminality. A required compilation
    // failure or source-token cancellation must stop the owning run even if an internal receiver
    // inspects it and returns a value. The region itself still permits retries in a fresh run.
    // A materialized body — cached or fresh — then passes the run's structural admission.
    private static async ValueTask<EvalResult<Algorithm>> MaterializeRequiredRegionAsync(DeferredModuleRegion region, EvalCtx ctx)
    {
        if (region.TryGetMaterialized(out var ready))
            return AdmitMaterializedBody(region, ready, ctx);

        try
        {
            var result = await region.MaterializeAsync(ctx.Budget.CancellationToken).ConfigureAwait(false);
            if (result.IsError)
                return ctx.Budget.RetainRequiredSourceFailure(result.Error);
            return AdmitMaterializedBody(region, result.Value, ctx);
        }
        catch (OperationCanceledException error) when (region.Loader.SourceProcessingCancellationToken.IsCancellationRequested)
        {
            ctx.Budget.RetainRequiredSourceCancellation(error);
            throw;
        }
    }

    // ── Conditional algorithm call (Lean: evalConditionalCallCounted) ───────



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
    /// the emitted arity with <see cref="ReCountValueBoundary(CountedResult)"/>
    /// (<c>Result.ValueCount</c>) — a multi-output branch becomes one sequence
    /// value (count 1), matching <c>if</c> and plain calls.
    /// Lean: <c>evalConditionalCallCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalConditionalCallCounted(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        // Charged dynamic invocation boundary; this counted core owns the
        // boundary for both counted evaluation and its plain projection.
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return AtFirstSpanIfMissing(limitError, args);

        try
        {
            return EvalConditionalCallCountedCore(callee, args, ctx, valEnv, calleeName);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    private static EvalResult<CountedResult> EvalConditionalCallCountedCore(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        return EvalNeedFamilyBodyCounted(callee, args, ctx, valEnv, calleeName);
    }

    // ── User-defined call (Lean: evalUserCallCounted) ─────────────────────

    /// <summary>
    /// Canonical user-call entry. Form supply, check cardinality, bind cells through
    /// the shared need-pattern binder, then evaluate the body. Plain unique binders
    /// transport cells without demanding VALUE or projecting CALLABLE; structural and
    /// repeated-name patterns demand only as required, in written pattern order.
    /// The counted result crosses the ordinary value boundary exactly once.
    /// Lean: <c>evalUserCallCounted</c> and <c>evalNeedUserSupply</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalUserCallCounted(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        // Charged dynamic invocation boundary (see EvaluationBudget) — the SAME enter
        // helper and scoped release the planned loop temp call (LoopExprPlan.TempCall)
        // uses, so the two strategies' charges and limit-span stamping cannot drift
        // (Evaluator.BudgetScopes.cs).
        if (TryEnterDynamicInvocation(ctx, UserCallLimitSpan(args), out var level) is { } limitError)
            return limitError;

        using (level)
        {
            return EvalUserCallCountedCore(callee, args, ctx, valEnv, calleeName);
        }
    }

    private static EvalResult<CountedResult> EvalUserCallCountedCore(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        if (callee is Algorithm.User { AssignmentDeconstructionTarget: { } target } helper
            && TryProjectSharedDeconstructionTarget(helper, target, args, ctx, valEnv) is { } projected)
            return projected.IsError ? projected.Error : EvalResult<CountedResult>.Ok(new(projected.Value, projected.Value.ValueCount()));
        return EvalNeedUserBodyCounted(callee, args, ctx, valEnv, calleeName);
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
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        // call(alias) = call(target): the ORIGINAL argument bundle reaches the target's own
        // dispatch. A safety net out of line — every binding lookup normalizes an alias first.
        if (callee is Algorithm.Alias)
            return EvalAliasCallCounted(callee, args, ctx, valEnv, calleeName);

        if (callee is Algorithm.Builtin(var builtinId))
        {
            var argAlgsR = ResolveArgAlgsWithSequenceSpread(args, ctx, valEnv);
            if (argAlgsR.IsError) return argAlgsR.Error;
            return NestMissingOutput(ApplyBuiltinCountedResolved(builtinId, argAlgsR.Value, ctx, valEnv));
        }

        if (TryGetFlatBinderUserEquivalent(callee) is { } simpleCallee)
            return EvalUserCallCounted(
                simpleCallee,
                args,
                ctx,
                valEnv,
                calleeName);

        if (callee is Algorithm.Conditional)
            return EvalConditionalCallCounted(callee, args, ctx, valEnv, calleeName);

        return EvalUserCallCounted(
            callee,
            args,
            ctx,
            valEnv,
            calleeName);
    }
}
