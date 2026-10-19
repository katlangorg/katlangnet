using KatLang.Evaluation;
using KatLang.Optimizations.Sequences;

namespace KatLang;

/// <summary>
/// <b>THE CALLABLE PROJECTION OF A CALL REFERENCE: <c>R.Algorithm</c> (META-S3-1)</b> (authoritative Lean:
/// the <c>"Algorithm"</c> arms of <c>evalDotCallCounted</c>, <c>resolveCalleeAlg</c>'s link arm,
/// <c>NeedPlan.calleeCell</c>, <c>NeedLink</c>, <c>linkValue</c> and <c>projectNeedWrittenAt</c>; rules:
/// <c>docs/design/language-rules/call-by-need.md</c> § Callable projection, CR-13..CR-16).
///
/// <para><b>The callee cell (CR-13).</b> Every invocation plan has at most one canonical callee cell
/// (<see cref="InvocationPlan.CalleeCell"/>): the plan's WRITTEN callee supplied in the plan's captured
/// caller context through the ONE supply-cell constructor (<see cref="SupplyCell"/>) — so a parameter
/// callee is that parameter's existing cell (NEED-01) and a name callee an identity-only cell over the
/// name. It is established lazily and compare-and-set retained; establishing it evaluates, prepares and
/// demands nothing.</para>
///
/// <para><b>The intrinsic (CR-14).</b> On a structural miss an edge spelled <c>Algorithm</c> reads its
/// receiver exactly as <c>Invoke</c> and <c>Arguments</c> do and requires a call reference of the
/// current run (<see cref="DecodeAlgorithmReceiver"/>). Bare, it is the callee cell's VALUE; with an
/// argument list, a fresh ordinary call of the callee cell's CALLABLE with exactly those arguments; in
/// callee position (<c>(R.Algorithm)(x)</c>) the same fresh call.</para>
///
/// <para><b>The link (CR-15).</b> A SUPPLIED <c>X.Algorithm</c> is one link cell
/// (<see cref="LinkSuspension"/>) whose receiver <c>X</c> is one lazily established receiver cell
/// shared by the link's VALUE and its CALLABLE: each channel demands that receiver's VALUE once,
/// decodes the same reference and delegates to the same callee cell's corresponding channel. The
/// link's CALLABLE is a RUNTIME projection (a node of the run's wait-for graph, S3-0a) resolved
/// asynchronously through the one adapter (<see cref="ResolveAsync{TState,T}"/>, S3-0b).</para>
///
/// <para><b>Qualified inertia (CR-16).</b> Obtaining and projecting <c>R.Algorithm</c> evaluates the
/// receiver and whatever the callee route demands, but never executes the plan's captured invocation,
/// prepares or reads its original argument supply, reads or writes the plan owner's VALUE, or changes
/// the reference.</para>
/// </summary>
public static partial class Evaluator
{
    /// <summary>The description of a captured callee that has no CALLABLE identity (NEED-06 absence).</summary>
    internal const string CapturedCalleeDescription = "captured callee";

    /// <summary><c>x.Algorithm</c> whose receiver VALUE is not a call reference.</summary>
    internal static string AlgorithmRequiresCallReferenceMessage(Result value)
        => $"`Algorithm` requires a call reference, got {DescribeOperand(value)}";

    /// <summary>
    /// The written link of a supplied <c>X.Algorithm</c> (CR-15): the ordinary written-argument
    /// suspension plus the link's ONE receiver cell, established lazily and compare-and-set retained
    /// (Lean: the cell's <c>receiver</c> memo). A discarded candidate of a racing establishment is an
    /// unattached cell nothing ever demands.
    /// </summary>
    internal sealed class LinkSuspension(EvalCtx caller, ValEnv values) : ExpressionSuspension(caller, values)
    {
        private NeedCell? _receiver;

        internal NeedCell Receiver(Expr.DotCall edge)
            => Volatile.Read(ref _receiver)
               ?? Interlocked.CompareExchange(ref _receiver, SupplyCell(edge.Target, Caller, Values, retained: true), null)
               ?? _receiver!;

        // Test observation only: whether the receiver cell has been established.
        internal bool HasReceiver => Volatile.Read(ref _receiver) is not null;
    }

    /// <summary>
    /// The canonical callee cell of <paramref name="plan"/> (CR-13): the written callee supplied in the
    /// captured caller context. Lean: <c>NeedPlan.calleeCell</c>.
    /// </summary>
    internal static NeedCell CalleeCellOf(InvocationPlan plan)
        => SupplyCell(plan.Source.Function, plan.Caller, plan.Values, retained: true);

    /// <summary>
    /// Whether a supplied argumentless dot edge's CALLABLE may be a RUNTIME projection — one that can
    /// demand a VALUE or project another cell (NEED-06): an edge spelled <c>Algorithm</c> whose
    /// intrinsic route is not statically excluded, and a parameter-rooted path in a run that already
    /// has runtime projections. A statically selected member keeps the ordinary identity-only route;
    /// this reads the front end's existing structural verdict, never resolves or projects a receiver.
    /// A path
    /// whose head parameter's cell is a runtime projection can only be formed after that cell, whose
    /// construction marked the run, so every other path stays identity-only and allocation-free.
    /// </summary>
    private static bool IsRuntimeProjectionSource(Expr.DotCall edge, EvaluationBudget budget)
        => (edge.UsesDotAlgorithmIntrinsic() && edge.EffectiveMissSelection() != LexicalFallbackSelection.Never)
            || (budget.HasRuntimeProjections && HasParameterHead(edge));

    private static bool HasParameterHead(Expr.DotCall edge)
    {
        Expr head = edge.Target;
        while (head is Expr.DotCall { Args: null } inner) head = inner.Target;
        return head is Expr.Param;
    }

    /// <summary>
    /// Decodes the receiver VALUE of <c>.Algorithm</c> into its invocation plan: a call reference of
    /// THIS run (the one ownership helper), never an argument view (CR-14). Lean: <c>decodeCallRef</c>.
    /// </summary>
    internal static EvalResult<InvocationPlan> DecodeAlgorithmReceiver(Result value, EvalCtx ctx)
    {
        if (value is not Result.CallReference { IsArgumentView: false } reference)
            return new EvalError.TypeMismatch(AlgorithmRequiresCallReferenceMessage(value));
        if (CheckCallReferenceOwnership(reference, ctx) is { } rejected)
            return rejected;
        return EvalResult<InvocationPlan>.Ok(reference.Plan);
    }

    /// <summary>
    /// The route fact of an argumentless edge spelled <c>Algorithm</c>, decided member-first exactly as
    /// <see cref="EvalDotCallCounted"/> decides it: <c>true</c> on a structural miss (a value receiver
    /// included) — the intrinsic — and <c>false</c> when the receiver declares <c>Algorithm</c> (a member,
    /// or a branch-only member whose error the ordinary route reports). Identity navigation only; a
    /// receiver navigation failure is the route's error. Lean: <c>algorithmIntrinsicRoute</c>.
    /// </summary>
    private static EvalResult<bool> IsAlgorithmIntrinsicRoute(Expr.DotCall edge, EvalCtx ctx)
    {
        var receiver = ResolveDotReceiver(edge.Target, ctx, out _);
        if (receiver.IsError)
            return IsAbsentIdentity(receiver.Error) ? EvalResult<bool>.Ok(true) : receiver.Error;
        return EvalResult<bool>.Ok(LookupPropBinding(receiver.Value, edge.Name, ctx.Budget) is null
            && !receiver.Value.DefinesConditionalBranchProperty(edge.Name));
    }

    // A bare VALUE read of the callee cell, after which the run's continuation is observed again (a cell
    // demand never absorbs a terminal run, as for an argument-view selection).
    private static EvalResult<CountedResult> CalleeValue(EvalResult<CountedResult> value, EvalCtx ctx)
        => value.IsError ? value : ctx.Budget.CheckContinuation() is { } terminal ? terminal : ReCountValueBoundary(value);

    // The CALLABLE of a decoded callee cell, or the captured callee's absence report.
    private static EvalResult<Algorithm> RequireCapturedCallee(EvalResult<Algorithm?> projected, SourceSpan? span)
        => projected.IsError ? projected.Error
            : projected.Value is { } algorithm ? EvalResult<Algorithm>.Ok(algorithm)
            : new EvalError.NotAnAlgorithm(CapturedCalleeDescription) { Span = span };

    // ── The intrinsic on the dot route (direct VALUE and fresh call) ────────────────────────────────────

    /// <summary>
    /// <c>R.Algorithm</c> / <c>R.Algorithm(args)</c> on a structural miss of an algorithm receiver: the
    /// receiver (<see cref="EvalDotReferenceIntrinsicReceiver"/>), then the plan's callee cell — bare,
    /// its VALUE (CR-14 b); with a written list, a fresh call of its CALLABLE (CR-14 c). Out of line so the
    /// recursive dot frame keeps its size. Lean: the <c>"Algorithm"</c> arm of <c>evalDotCallCounted</c>.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalDotAlgorithmIntrinsicCounted(
        Expr.DotCall dotCall, Algorithm targetAlg, bool receiverIsStructuralMember, EvalCtx ctx, ValEnv valEnv)
    {
        var receiver = EvalDotReferenceIntrinsicReceiver(dotCall, targetAlg, receiverIsStructuralMember, ctx, valEnv);
        return receiver.IsError ? receiver.Error : ApplyAlgorithmIntrinsic(dotCall, dotCall.Args, receiver.Value, ctx, valEnv);
    }

    /// <summary>
    /// <c>x.Algorithm</c> / <c>x.Algorithm(args)</c> whose receiver declares no member (a value receiver, a
    /// call result): the receiver's ordinary value, then <see cref="ApplyAlgorithmIntrinsic"/>. Lean: the
    /// <c>"Algorithm"</c> arm of the value-receiver branch of <c>evalDotCallCounted</c>.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalDotAlgorithmValueReceiverCounted(Expr.DotCall dotCall, EvalCtx ctx, ValEnv valEnv)
    {
        var receiver = Eval(dotCall.Target, ctx, valEnv);
        return receiver.IsError ? receiver.Error : ApplyAlgorithmIntrinsic(dotCall, dotCall.Args, receiver.Value, ctx, valEnv);
    }

    /// <summary>
    /// The intrinsic over its receiver's VALUE: decode, then the plan's callee cell — its VALUE when
    /// <paramref name="args"/> is <c>null</c>, otherwise the fresh ordinary call of its CALLABLE with
    /// exactly <paramref name="args"/> (named by the plan's written callee for dispatch diagnostics).
    /// Lean: <c>algorithmOfValue</c>.
    /// </summary>
    private static EvalResult<CountedResult> ApplyAlgorithmIntrinsic(
        Expr.DotCall edge, OutputBundle? args, Result receiver, EvalCtx ctx, ValEnv valEnv)
    {
        var plan = DecodeAlgorithmReceiver(receiver, ctx);
        if (plan.IsError) return plan.Error;
        var callee = plan.Value.CalleeCell;
        if (args is null)
            return CalleeValue(callee.Demand(), ctx);
        var callable = RequireCapturedCallee(callee.ProjectCallable(), edge.Span);
        if (callable.IsError) return callable.Error;
        return EvalResolvedCallCounted(callable.Value, args, ctx, valEnv, CallDiagnosticName.FromExpression(plan.Value.Source.Function));
    }

    /// <summary>MIRROR OF <see cref="EvalDotAlgorithmIntrinsicCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalDotAlgorithmIntrinsicCountedAsync(
        Expr.DotCall dotCall, Algorithm targetAlg, bool receiverIsStructuralMember, EvalCtx ctx, ValEnv valEnv)
    {
        var receiver = await EvalDotReferenceIntrinsicReceiverAsync(dotCall, targetAlg, receiverIsStructuralMember, ctx, valEnv).ConfigureAwait(false);
        return receiver.IsError ? receiver.Error : await ApplyAlgorithmIntrinsicAsync(dotCall, dotCall.Args, receiver.Value, ctx, valEnv).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalDotAlgorithmValueReceiverCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalDotAlgorithmValueReceiverCountedAsync(Expr.DotCall dotCall, EvalCtx ctx, ValEnv valEnv)
    {
        // The synchronous twin evaluates the value-only target with plain Eval; the counted twin's value
        // projection is the same value.
        var receiver = await EvalCountedAsync(dotCall.Target, ctx, valEnv).ConfigureAwait(false);
        return receiver.IsError ? receiver.Error : await ApplyAlgorithmIntrinsicAsync(dotCall, dotCall.Args, receiver.Value.Value, ctx, valEnv).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="ApplyAlgorithmIntrinsic"/> — keep in lock-step. The callee's CALLABLE is
    /// obtained through the async resolution adapter (S3-0b), which awaits a runtime projection.</summary>
    private static async ValueTask<EvalResult<CountedResult>> ApplyAlgorithmIntrinsicAsync(
        Expr.DotCall edge, OutputBundle? args, Result receiver, EvalCtx ctx, ValEnv valEnv)
    {
        var plan = DecodeAlgorithmReceiver(receiver, ctx);
        if (plan.IsError) return plan.Error;
        var callee = plan.Value.CalleeCell;
        if (args is null)
            return CalleeValue(await callee.DemandAsync().ConfigureAwait(false), ctx);
        var callable = RequireCapturedCallee(await ProjectCellCallableAsync(callee, ctx).ConfigureAwait(false), edge.Span);
        if (callable.IsError) return callable.Error;
        return await EvalResolvedCallCountedAsync(callable.Value, args, ctx, valEnv, CallDiagnosticName.FromExpression(plan.Value.Source.Function)).ConfigureAwait(false);
    }

    /// <summary>A cell's CALLABLE in the async engine: the one projection through the async resolution adapter.</summary>
    private static ValueTask<EvalResult<Algorithm?>> ProjectCellCallableAsync(NeedCell cell, EvalCtx ctx)
        => ResolveAsync(ctx, cell, static cell => cell.ProjectCallable());

    // ── The intrinsic in callee position: `(R.Algorithm)(args)` ─────────────────────────────────────────

    /// <summary>Whether a call's callee is an argumentless edge spelled <c>Algorithm</c>.</summary>
    private static bool IsAlgorithmEdgeCallee(Expr callee)
        => callee is Expr.DotCall { Args: null } edge && edge.UsesDotAlgorithmIntrinsic();

    /// <summary>
    /// A call whose callee is an argumentless edge spelled <c>Algorithm</c> (CR-14 a, c): grouping never
    /// changes identity, so on a structural miss <c>(R.Algorithm)(args)</c> is exactly the fresh call
    /// <c>R.Algorithm(args)</c> — the receiver read, decoded and the callee cell's CALLABLE called with
    /// exactly <c>args</c> — under the call's own frame, the receiver, decode and projection failures
    /// being the callee's resolution failure. A declared member <c>Algorithm</c> is the ordinary callee
    /// (DOT-09). Lean: the link arm of <c>resolveCalleeAlg</c>.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalAlgorithmCalleeCallCounted(
        Expr.DotCall edge, OutputBundle args, EvalCtx ctx, ValEnv valEnv)
    {
        var diagnosticName = CallDiagnosticName.FromExpression(edge);
        var route = IsAlgorithmIntrinsicRoute(edge, ctx);
        if (route.IsError)
            return CalleeResolutionFailure(diagnosticName, ctx, route.Error);
        if (!route.Value)
            return EvalDeclaredAlgorithmMemberCallCounted(edge, args, diagnosticName, ctx, valEnv);

        var receiver = EvalAlgorithmReceiver(edge, ctx, valEnv);
        if (receiver.IsError)
            return CalleeResolutionFailure(diagnosticName, ctx, receiver.Error);
        var plan = DecodeAlgorithmReceiver(receiver.Value, ctx);
        if (plan.IsError)
            return CalleeResolutionFailure(diagnosticName, ctx, plan.Error with { Span = plan.Error.Span ?? edge.Span });
        var callable = RequireCapturedCallee(plan.Value.CalleeCell.ProjectCallable(), edge.Span);
        if (callable.IsError)
            return CalleeResolutionFailure(diagnosticName, ctx, callable.Error);
        return WithCallCtx(diagnosticName, ctx,
            EvalResolvedCallCounted(callable.Value, args, ctx, valEnv, CallDiagnosticName.FromExpression(plan.Value.Source.Function)));
    }

    /// <summary>MIRROR OF <see cref="EvalAlgorithmCalleeCallCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalAlgorithmCalleeCallCountedAsync(
        Expr.DotCall edge, OutputBundle args, EvalCtx ctx, ValEnv valEnv)
    {
        var diagnosticName = CallDiagnosticName.FromExpression(edge);
        var route = await ResolveAsync(ctx, (edge, ctx), static state => IsAlgorithmIntrinsicRoute(state.edge, state.ctx)).ConfigureAwait(false);
        if (route.IsError)
            return CalleeResolutionFailure(diagnosticName, ctx, route.Error);
        if (!route.Value)
        {
            // MIRROR OF the synchronous member arm (the async strategy pins fusion off).
            var member = await ResolveCalleeAsync(edge, ctx).ConfigureAwait(false);
            return member.IsError
                ? CalleeResolutionFailure(diagnosticName, ctx, member.Error)
                : WithCallCtx(diagnosticName, ctx,
                    await EvalResolvedCallCountedAsync(member.Value, args, ctx, valEnv, diagnosticName).ConfigureAwait(false));
        }

        var receiver = await EvalAlgorithmReceiverAsync(edge, ctx, valEnv).ConfigureAwait(false);
        if (receiver.IsError)
            return CalleeResolutionFailure(diagnosticName, ctx, receiver.Error);
        var plan = DecodeAlgorithmReceiver(receiver.Value, ctx);
        if (plan.IsError)
            return CalleeResolutionFailure(diagnosticName, ctx, plan.Error with { Span = plan.Error.Span ?? edge.Span });
        var callable = RequireCapturedCallee(await ProjectCellCallableAsync(plan.Value.CalleeCell, ctx).ConfigureAwait(false), edge.Span);
        if (callable.IsError)
            return CalleeResolutionFailure(diagnosticName, ctx, callable.Error);
        return WithCallCtx(diagnosticName, ctx,
            await EvalResolvedCallCountedAsync(callable.Value, args, ctx, valEnv, CallDiagnosticName.FromExpression(plan.Value.Source.Function)).ConfigureAwait(false));
    }

    /// <summary>
    /// A callee <c>X.Algorithm</c> whose receiver declares a member <c>Algorithm</c>: the ordinary callee
    /// of <see cref="EvalCallCountedExpr"/> (DOT-09's one callee law, the sequence-pipeline hook and the
    /// resolved dispatch under the call frame).
    /// </summary>
    private static EvalResult<CountedResult> EvalDeclaredAlgorithmMemberCallCounted(
        Expr.DotCall edge, OutputBundle args, CallDiagnosticName diagnosticName, EvalCtx ctx, ValEnv valEnv)
    {
        var calleeR = ResolveCallee(edge, ctx);
        if (calleeR.IsError)
            return CalleeResolutionFailure(diagnosticName, ctx, calleeR.Error);
        if (TryEvaluateSequencePipeline(
            SequencePipelineInvocation.PlainCall(edge, args, calleeR.Value), ctx, valEnv, out var sequencePipelineR))
            return WithCallCtx(diagnosticName, ctx, sequencePipelineR);
        return WithCallCtx(diagnosticName, ctx, EvalResolvedCallCounted(calleeR.Value, args, ctx, valEnv, diagnosticName));
    }

    /// <summary>
    /// The receiver VALUE of an intrinsic <c>.Algorithm</c> callee, read exactly as the dot route reads
    /// it (<see cref="EvalDotReferenceIntrinsicReceiver"/> for an algorithm receiver, the ordinary value
    /// otherwise).
    /// </summary>
    private static EvalResult<Result> EvalAlgorithmReceiver(Expr.DotCall edge, EvalCtx ctx, ValEnv valEnv)
    {
        var target = ResolveDotReceiver(edge.Target, ctx, out var structural);
        return target.IsError
            ? IsAbsentIdentity(target.Error) ? Eval(edge.Target, ctx, valEnv) : target.Error
            : EvalDotReferenceIntrinsicReceiver(edge, target.Value, structural, ctx, valEnv);
    }

    /// <summary>MIRROR OF <see cref="EvalAlgorithmReceiver"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> EvalAlgorithmReceiverAsync(Expr.DotCall edge, EvalCtx ctx, ValEnv valEnv)
    {
        var target = await ResolveDotReceiverAsync(edge.Target, ctx).ConfigureAwait(false);
        EvalResult<Result> receiver;
        if (target.IsError)
        {
            if (IsAbsentIdentity(target.Error))
            {
                var counted = await EvalCountedAsync(edge.Target, ctx, valEnv).ConfigureAwait(false);
                receiver = counted.IsError ? counted.Error : EvalResult<Result>.Ok(counted.Value.Value);
            }
            else receiver = target.Error;
        }
        else receiver = await EvalDotReferenceIntrinsicReceiverAsync(edge, target.Value.Receiver, target.Value.IsStructuralMember, ctx, valEnv).ConfigureAwait(false);
        return receiver;
    }

    // ── The supplied link: VALUE and CALLABLE over one receiver cell ────────────────────────────────────

    /// <summary>
    /// The VALUE of a supplied <c>X.Algorithm</c> link on the intrinsic route (CR-15, CR-14 b): its ONE
    /// receiver cell's VALUE, decoded, then the callee cell's VALUE — the very receiver demand the link's
    /// CALLABLE uses; <c>null</c> when the edge selects a declared member (the ordinary evaluation runs).
    /// The callee's VALUE outcome is passed through as the callee cell reports it, so a consumer's slot
    /// diagnostics read it exactly as if the captured callee were written there. Lean: <c>linkValue</c>.
    /// </summary>
    internal static EvalResult<CountedResult>? TryEvalLinkValue(Expr.DotCall edge, LinkSuspension link)
    {
        var route = IsAlgorithmIntrinsicRoute(edge, link.Caller);
        if (route.IsOk && !route.Value) return null;
        return route.IsError ? route.Error : LinkedCalleeValue(edge, link);
    }

    private static EvalResult<CountedResult> LinkedCalleeValue(Expr.DotCall edge, LinkSuspension link)
    {
        var receiver = link.Receiver(edge).Demand();
        if (receiver.IsError) return receiver.Error;
        var plan = DecodeAlgorithmReceiver(receiver.Value.Value, link.Caller);
        return plan.IsError ? plan.Error : CalleeValue(plan.Value.CalleeCell.Demand(), link.Caller);
    }

    /// <summary>MIRROR OF <see cref="TryEvalLinkValue"/> — keep in lock-step.</summary>
    internal static async ValueTask<EvalResult<CountedResult>?> TryEvalLinkValueAsync(Expr.DotCall edge, LinkSuspension link)
    {
        var route = await ResolveAsync(link.Caller, (edge, link.Caller), static state => IsAlgorithmIntrinsicRoute(state.edge, state.Caller)).ConfigureAwait(false);
        if (route.IsOk && !route.Value) return null;
        if (route.IsError) return route.Error;
        var receiver = await link.Receiver(edge).DemandAsync().ConfigureAwait(false);
        if (receiver.IsError) return receiver.Error;
        var plan = DecodeAlgorithmReceiver(receiver.Value.Value, link.Caller);
        return plan.IsError ? plan.Error : CalleeValue(await plan.Value.CalleeCell.DemandAsync().ConfigureAwait(false), link.Caller);
    }

    /// <summary>
    /// The CALLABLE of a supplied <c>X.Algorithm</c> link (CR-15, CR-14 a): on the intrinsic route, its ONE
    /// receiver cell's VALUE, decoded, then the callee cell's CALLABLE — never the link's own VALUE and
    /// never the callee cell's VALUE; on a declared member, the ordinary structural projection. Runs as
    /// the link cell's runtime projection, whose completion publishes the outcome. Lean: the link arm of
    /// <c>projectNeedWrittenAt</c>.
    /// </summary>
    private static EvalResult<Algorithm?> ProjectLinkCallable(Expr.DotCall edge, LinkSuspension link)
    {
        var route = IsAlgorithmIntrinsicRoute(edge, link.Caller);
        if (route.IsError) return route.Error;
        if (!route.Value) return ProjectDotPathCallable(edge, link.Caller);
        var receiver = link.Receiver(edge).Demand();
        if (receiver.IsError) return receiver.Error;
        var plan = DecodeAlgorithmReceiver(receiver.Value.Value, link.Caller);
        return plan.IsError ? plan.Error : plan.Value.CalleeCell.ProjectCallable();
    }

    /// <summary>
    /// The asynchronous CALLABLE computation of a written argument's runtime projection: the ONE
    /// synchronous projection (<see cref="ProjectSuspendedCallable"/>) through the async resolution
    /// adapter, which performs every VALUE and runtime CALLABLE step it needs in its own order and
    /// replays each outcome where the projection reads it (S3-0b). Every cell it reaches is retry-stable:
    /// the link's receiver and the plan's callee cell are compare-and-set retained.
    /// </summary>
    internal static ValueTask<EvalResult<Algorithm?>> ProjectSuspendedCallableAsync(NeedCell cell, Expr expression, ExpressionSuspension suspension)
        => ResolveAsync(suspension.Caller, (cell, expression, suspension), static state => ProjectSuspendedCallable(state.cell, state.expression, state.suspension));
}
