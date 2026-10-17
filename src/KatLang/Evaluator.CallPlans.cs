using System.Runtime.ExceptionServices;
using KatLang.Evaluation;

namespace KatLang;

/// <summary>
/// <b>INVOCATION PLANS AND CALL REFERENCES: one supplied call, one plan, shared by VALUE and META</b>
/// (authoritative Lean: the <c>NeedPlan</c> section of <c>lean/KatLang.lean</c>; laws in
/// <c>lean/KatLangArityLaws/InvocationPlan.lean</c>, <c>CallReference.lean</c> and <c>ArgumentView.lean</c>;
/// rules: <c>docs/design/language-rules/call-by-need.md</c> § Call references, § Argument views). Plan
/// retention and execution run only in a run that RETAINS invocation plans (<see cref="EvaluationBudget.RetainsInvocationPlans"/>):
/// a run whose admitted program may perform META capture (the J7 program gate,
/// <see cref="AstStructuralPreflight.MayCaptureCalls"/>), or a test-seam run
/// (<see cref="InvocationPlanTestSeam"/>). Every other run uses ordinary expression cells. The reference
/// boundary checks in this file remain active in every run.
///
/// <para><b>Representation.</b> Every written argument's cell keeps its suspension as data
/// (<see cref="ExpressionSuspension"/>: the caller context and value environment; the written expression is
/// the cell's <see cref="NeedCell.Source"/>). A call-shaped supplied cell (<see cref="IsPlannableCall"/>) IS
/// its plan, exactly as a Lean need address is: its suspension is an <see cref="InvocationPlan"/>, which adds
/// ONE supply slot holding the plan's preparation state (Lean <c>NeedCell.plan : NeedPlanSupply</c>). The slot
/// holds the very supply object the dispatch consumes (the formed cell list, or a builtin's argument array),
/// so retaining the supply after VALUE allocates nothing beyond the ordinary call. On the VALUE path there is
/// no flight, reference or holder object: a waiter's completion source is allocated only when a second party
/// finds a preparation in progress, and the plan's <see cref="Result.CallReference"/> only on META.</para>
///
/// <para><b>Operations.</b> The cell's ordinary VALUE (<see cref="NeedCell.Demand"/>) runs
/// <see cref="EvalPlannedCallCounted"/>. META (<see cref="ReifyMeta"/>, reached by a <c>meta</c> parameter
/// through the binder's <see cref="ReferenceAdapterCell"/>) runs nothing and yields the plan's one
/// <see cref="Result.CallReference"/>. <c>R.Invoke()</c> (<see cref="InvokeCallReferenceValue"/>) executes the
/// target afresh over the SAME prepared cells. <c>R.Arguments</c> (<see cref="ArgumentsOfCallReferenceValue"/>)
/// is the reference's argument view; its operations read the plan's one supply
/// (<see cref="PrepareArgumentView"/>) without resolving the target. Forwarding is unchanged:
/// <see cref="SupplyCell"/> transports a bound parameter's existing cell, so the plan travels with that cell,
/// and a view spread (<see cref="FormSpreadSupplySlot"/>) transports the plan's original cells. Every
/// operation that decodes a reference passes <see cref="CheckCallReferenceOwnership"/>.</para>
///
/// <para><b>Why a separate dispatch.</b> A plan execution is the ordinary call's phases over a supply that
/// must SURVIVE the execution (sticky, shared by VALUE, every <c>Invoke()</c> and every view), whereas the
/// ordinary call forms a fresh supply per evaluation and may fuse it away. Phase order on every execution is
/// the ordinary call's: the call node's dispatch checkpoint, then callee resolution in the caller's context
/// (<see cref="ResolveCallee"/>), then alias normalization, then the invocation charge where the ordinary
/// dispatcher charges it, then the plan's supply (formed once, by <see cref="FormNeedSupply"/>), then the
/// cardinality gate, the binder and the body — the SAME helpers the ordinary call uses
/// (<see cref="EvalNeedUserSupplyCounted"/> / <see cref="EvalNeedFamilySupplyCounted"/> /
/// <see cref="ApplyBuiltinCountedResolved"/>). Fail-closed differences from the generic call are listed on
/// <see cref="DispatchPlannedCounted"/>.</para>
/// </summary>
public static partial class Evaluator
{
    /// <summary>The structured META refusal: the observed cell is not a supplied call computation.</summary>
    internal const string MetaRefusalDescription = "meta: not a supplied call computation";

    /// <summary>
    /// The supported plan shape: a written call whose callee is a lexical name or a parameter. A dot
    /// callee (structural or extension route) and every non-call expression are deliberately out of
    /// scope: they keep the ordinary cell, and META refuses them.
    /// </summary>
    private static Expr.Call? IsPlannableCall(Expr expression)
        => expression is Expr.Call { Function: Expr.Resolve or Expr.Param } call ? call : null;

    /// <summary>
    /// A written argument's suspension (Lean <c>NeedSuspension.expression source caller values</c>; the
    /// source is the owning cell's <see cref="NeedCell.Source"/>): the data the cell's VALUE and CALLABLE
    /// projection run over. It is never rewritten after allocation and never released, exactly as the
    /// closures it replaces were kept alive by the cell's CALLABLE projection.
    /// </summary>
    internal class ExpressionSuspension(EvalCtx caller, ValEnv values)
    {
        internal EvalCtx Caller { get; } = caller;
        internal ValEnv Values { get; } = values;
    }

    /// <summary>
    /// The ONE invocation plan of one supplied call. Its identity is its owning cell
    /// (<see cref="Owner"/>; Lean: the need address); it is that cell's suspension plus the plan's supply slot
    /// <see cref="Supply"/> (Lean <c>NeedCell.plan</c>):
    /// <list type="bullet">
    /// <item><c>null</c> — unprepared;</item>
    /// <item>a <see cref="PlanPreparation"/> — a preparation in progress (Lean <c>preparing</c>);</item>
    /// <item>the prepared supply itself — the formed <see cref="IReadOnlyList{T}"/> of cells for a user or
    /// family callee, or a builtin callee's <see cref="ResolvedArgumentAlgorithm"/> array (cells with their
    /// written sources);</item>
    /// <item>an <see cref="EvalError"/> — a sticky ordinary preparation failure;</item>
    /// <item>an <see cref="ExceptionDispatchInfo"/> — a sticky host exception or cancellation.</item>
    /// </list>
    /// A prepared slot (any outcome) never changes again (Lean <c>prepared</c> is final). The target is
    /// resolved on every execution, in the caller's context, exactly as the ordinary call resolves it;
    /// resolution is identity-only, so every execution reaches the same callable. The owning cell's VALUE is
    /// one execution inside the cell's flight (at-most-once, sticky); each <see cref="InvokePlan"/> is
    /// a fresh execution that never reads or writes that VALUE.
    /// </summary>
    internal sealed class InvocationPlan(EvalCtx caller, ValEnv values) : ExpressionSuspension(caller, values)
    {
        private NeedCell? _owner;
        private Result.CallReference? _reference;

        /// <summary>The plan's supply slot (see the type summary). Written only by the plan's preparation.</summary>
        internal object? Supply;

        // Written only by PublishPlanSupply; read through SupplyFormations.
        internal int Formations;

        /// <summary>The supplied cell this plan belongs to: its original VALUE cell.</summary>
        internal NeedCell Owner => _owner!;

        /// <summary>The written call (the owner's source).</summary>
        internal Expr.Call Source => (Expr.Call)_owner!.Source!;

        // Called once, by the owning cell's constructor, before the cell is published.
        internal void Attach(NeedCell owner) => _owner = owner;

        /// <summary>The plan's one reference, allocated on the first META. Every META returns this same object.</summary>
        internal Result.CallReference Reference
            => Volatile.Read(ref _reference) ?? Interlocked.CompareExchange(ref _reference, new Result.CallReference(this), null) ?? _reference!;

        /// <summary>Test observation: how many times this plan formed its supply (at most once).</summary>
        internal int SupplyFormations => Volatile.Read(ref Formations);

        /// <summary>
        /// Test observation: the prepared argument cells, or <c>null</c> before preparation or after a failure.
        /// A user or family plan returns the very list its executions bind.
        /// </summary>
        internal IReadOnlyList<NeedCell>? PreparedCells => Volatile.Read(ref Supply) switch
        {
            IReadOnlyList<NeedCell> cells => cells,
            ResolvedArgumentAlgorithm[] arguments => Array.ConvertAll(arguments, static argument => argument.Cell!),
            SourcedPlanSupply sourced => sourced.Cells,
            _ => null,
        };

        /// <summary>
        /// Test seam: the plan's supply as an invocation would prepare it (a user or family shape), joining a
        /// preparation in progress. Lean: <c>NeedPlan.prepare</c>.
        /// </summary>
        internal async ValueTask<EvalResult<PreparedSupply>> PrepareSupply(bool asynchronous)
        {
            var supply = asynchronous
                ? await PreparePlanSupplyAsync(this, PlanSupplyShape.Cells, byInvocation: true).ConfigureAwait(false)
                : PreparePlanSupplyCounted(this, PlanSupplyShape.Cells, byInvocation: true);
            return supply.IsError ? supply.Error : EvalResult<PreparedSupply>.Ok(new PreparedSupply(PlanCells(supply.Value)));
        }
    }

    /// <summary>
    /// The shape a plan's ONE preparation records (the slot holds the very object the first consumer
    /// needs): a user or family arm binds the cell list, a builtin arm consumes argument records with
    /// their written sources, and an ARGUMENT VIEW (CallReference S2) — which must not resolve the
    /// target to learn which arm will run — records the neutral <see cref="SourcedPlanSupply"/>, from
    /// which either arm later reads its shape without re-forming anything.
    /// </summary>
    private enum PlanSupplyShape
    {
        Cells,
        BuiltinArguments,
        Sourced,
    }

    /// <summary>
    /// A supply prepared by an argument view before any execution chose an arm (CallReference S2): the
    /// formed cells and their written sources, exactly what <see cref="FormNeedSupply"/> produced. A
    /// user or family execution binds <see cref="Cells"/> itself; a builtin execution reads argument
    /// records built from both, so its diagnostics keep the written sources an ordinary preparation
    /// keeps. Lean records sources for every plan (<c>NeedPlanSupply.prepared</c>).
    /// </summary>
    private sealed class SourcedPlanSupply(IReadOnlyList<NeedCell> cells, IReadOnlyList<Expr?> sources)
    {
        internal IReadOnlyList<NeedCell> Cells { get; } = cells;
        internal IReadOnlyList<Expr?> Sources { get; } = sources;
    }

    /// <summary>
    /// A preparation in progress. The two shared markers carry no waiter; a party that finds one and must
    /// wait replaces it by a private marker with a completion source (the only allocation of contention).
    /// <see cref="IsByInvocation"/> tells a waiter how to recognize a re-entrant preparation in its own flow.
    /// </summary>
    private sealed class PlanPreparation(bool byInvocation, TaskCompletionSource? waiters)
    {
        internal static readonly PlanPreparation ByValue = new(false, null);
        internal static readonly PlanPreparation ByInvocation = new(true, null);

        internal bool IsByInvocation { get; } = byInvocation;
        internal TaskCompletionSource? Waiters { get; } = waiters;
    }

    /// <summary>
    /// The plans whose supply an explicit invocation is preparing in the current logical flow. Only an
    /// invocation pushes a frame: a VALUE-initiated preparation is recognized through its owner's flight
    /// (<see cref="NeedCell.IsEvaluatingInCurrentFlow"/>), so the VALUE path sets no ambient state.
    /// </summary>
    private static readonly AsyncLocal<InvocationPreparationFrame?> PreparingInvocations = new();

    private sealed record InvocationPreparationFrame(InvocationPlan Plan, InvocationPreparationFrame? Parent);

    /// <summary>
    /// META: the stable reference of a supplied call's plan. It runs no target, demands no VALUE,
    /// prepares no supply and opens no spread. Any other cell (Ready data, a collector, a non-call
    /// computation, a cell of a run without plans) or a missing cell is refused with a structured
    /// <see cref="EvalError.NotAnAlgorithm"/>. Lean: <c>NeedPlan.reify</c> (<c>reifyNeedCall</c>).
    /// </summary>
    internal static EvalResult<Result.CallReference> ReifyMeta(NeedCell? cell)
        => cell?.Suspension is InvocationPlan plan
            ? EvalResult<Result.CallReference>.Ok(plan.Reference)
            : new EvalError.NotAnAlgorithm(MetaRefusalDescription) { Span = cell?.Span };

    /// <summary>
    /// THE META CAPABILITY of the binder (CallReference S1): the supplied <paramref name="cell"/> reified
    /// (<see cref="ReifyMeta"/>, a pure read of its suspension) into ONE fresh Ready adapter cell whose
    /// VALUE is the plan's reference. The original cell — its suspension, VALUE flight, CALLABLE memo and
    /// supply slot — is neither read beyond its suspension nor written, and no lock is taken. The adapter
    /// is Ready data: it has no CALLABLE identity, so a further META of it refuses. The run's
    /// continuation is observed first (a cancelled or terminal run captures nothing). A META binder can
    /// only execute in a run that retains plans (the J7 gate decided that before evaluation); reaching
    /// one in a run that does not is an internal gate defect and fails loudly instead of refusing.
    /// Lean: <c>NeedPlan.reference</c>.
    /// </summary>
    internal static EvalResult<NeedCell> ReferenceAdapterCell(NeedCell cell, EvalCtx ctx)
    {
        if (ctx.Budget.CheckContinuation() is { } terminal)
            return terminal;
        if (!ctx.Budget.RetainsInvocationPlans)
            throw new InvalidOperationException(
                "A meta parameter was bound in a run whose program gate disabled invocation plans (J7 false negative).");
        var reference = ReifyMeta(cell);
        return reference.IsError
            ? reference.Error
            : EvalResult<NeedCell>.Ok(NeedCell.Ready(new CountedResult(reference.Value, 1)));
    }

    /// <summary>
    /// THE ONE RUN-OWNERSHIP CHECK of a call reference (CallReference S1), shared by every operation that
    /// decodes a reference — <c>R.Invoke()</c> now, and any later projection of the same plan. A reference
    /// belongs to the run that captured it: one of another run is refused (its cells, caller context and
    /// supply belong to a finished or foreign run and are never executed here), and the owning run's
    /// lifetime must still be live, and its continuation is observed — a reached resource limit, a retained required-source failure or
    /// cancellation (thrown with its original exception and token) ends the operation before any plan
    /// work, whatever the plan already prepared or completed. Returns <c>null</c> when the operation may
    /// proceed.
    /// </summary>
    internal static EvalError? CheckCallReferenceOwnership(Result.CallReference reference, EvalCtx ctx)
    {
        if (!ReferenceEquals(reference.Budget, ctx.Budget))
            return new EvalError.IllegalInEval(ForeignCallReferenceMessage);
        return ctx.Budget.CheckContinuation()
            ?? (ctx.Budget.RunEnded ? new EvalError.IllegalInEval(EndedCallReferenceMessage) : null);
    }

    /// <summary>The refusal of a call reference decoded outside the run that captured it.</summary>
    internal const string ForeignCallReferenceMessage =
        "A call reference can be used only inside the run that captured it.";

    /// <summary>A retained handle cannot restart work after its owning run has exited.</summary>
    internal const string EndedCallReferenceMessage =
        "A call reference cannot be used after its run has ended.";

    /// <summary>
    /// <c>R.Invoke()</c> over the receiver's VALUE (CallReference S1): a call reference of THIS run executes
    /// its plan afresh (<see cref="InvokePlan"/>: the ordinary call's phases over the plan's one prepared
    /// supply, never reading or writing the original cell's VALUE); any other value is the intrinsic's kind
    /// rejection. The run's continuation is observed before the plan runs (the ownership check) and again
    /// after a successful execution, so an invocation can never absorb a terminal outcome.
    /// Lean: <c>invokeCallReferenceValue</c>.
    /// </summary>
    internal static EvalResult<CountedResult> InvokeCallReferenceValue(Result value, EvalCtx ctx)
    {
        if (value is not Result.CallReference { IsArgumentView: false } reference)
            return new EvalError.TypeMismatch(InvokeRequiresCallReferenceMessage(value));
        if (CheckCallReferenceOwnership(reference, ctx) is { } rejected)
            return rejected;
        var result = InvokePlan(reference.Plan);
        if (!result.IsError && CheckCallReferenceOwnership(reference, ctx) is { } terminal)
            return terminal;
        return result;
    }

    /// <summary>MIRROR OF <see cref="InvokeCallReferenceValue"/> — keep in lock-step.</summary>
    internal static async ValueTask<EvalResult<CountedResult>> InvokeCallReferenceValueAsync(Result value, EvalCtx ctx)
    {
        if (value is not Result.CallReference { IsArgumentView: false } reference)
            return new EvalError.TypeMismatch(InvokeRequiresCallReferenceMessage(value));
        if (CheckCallReferenceOwnership(reference, ctx) is { } rejected)
            return rejected;
        var result = await InvokePlanAsync(reference.Plan).ConfigureAwait(false);
        if (!result.IsError && CheckCallReferenceOwnership(reference, ctx) is { } terminal)
            return terminal;
        return result;
    }

    // ── CallReference S2: the lazy argument view `R.Arguments` ───────────────────────────────────────

    /// <summary>
    /// <c>R.Arguments</c> over the receiver's VALUE (CallReference S2): a call reference of THIS run yields
    /// its ONE argument view (<see cref="Result.CallReference.ArgumentView"/>) — nothing is run, prepared,
    /// demanded or resolved; any other value, an argument view included, is the intrinsic's kind rejection.
    /// Obtaining a view checks the reference's ownership like every operation that reaches its plan.
    /// Lean: <c>argumentsOfValue</c>.
    /// </summary>
    internal static EvalResult<CountedResult> ArgumentsOfCallReferenceValue(Result value, EvalCtx ctx)
    {
        if (value is not Result.CallReference { IsArgumentView: false } reference)
            return new EvalError.TypeMismatch(ArgumentsRequiresCallReferenceMessage(value));
        if (CheckCallReferenceOwnership(reference, ctx) is { } rejected)
            return rejected;
        return EvalResult<CountedResult>.Ok(new CountedResult(reference.ArgumentView, 1));
    }

    /// <summary>
    /// The cells of argument <paramref name="view"/> (CallReference S2): the plan's ONE sticky supply —
    /// its recorded preparation, or exactly one formation through the ordinary
    /// <see cref="FormNeedSupply"/> in the plan's caller context, shared with the original VALUE and every
    /// <c>Invoke()</c> — WITHOUT resolving or dispatching the target and without demanding any argument
    /// VALUE (formation demands nothing; only an arbitrary spread's own evaluation runs). An unprepared
    /// plan records the neutral <see cref="SourcedPlanSupply"/>. The view's ownership is checked before
    /// any plan work and again after a formation, so a terminal run is never absorbed.
    /// Lean: <c>NeedPlan.viewCells</c> (<c>argumentViewCells</c>).
    /// </summary>
    internal static EvalResult<IReadOnlyList<NeedCell>> PrepareArgumentView(Result.CallReference view, EvalCtx ctx)
    {
        if (CheckCallReferenceOwnership(view, ctx) is { } rejected)
            return rejected;
        var supply = PreparePlanSupplyCounted(view.Plan, PlanSupplyShape.Sourced, byInvocation: true);
        if (supply.IsError) return supply.Error;
        if (CheckCallReferenceOwnership(view, ctx) is { } terminal)
            return terminal;
        return EvalResult<IReadOnlyList<NeedCell>>.Ok(PlanCells(supply.Value));
    }

    /// <summary>MIRROR OF <see cref="PrepareArgumentView"/> — keep in lock-step.</summary>
    internal static async ValueTask<EvalResult<IReadOnlyList<NeedCell>>> PrepareArgumentViewAsync(Result.CallReference view, EvalCtx ctx)
    {
        if (CheckCallReferenceOwnership(view, ctx) is { } rejected)
            return rejected;
        var supply = await PreparePlanSupplyAsync(view.Plan, PlanSupplyShape.Sourced, byInvocation: true).ConfigureAwait(false);
        if (supply.IsError) return supply.Error;
        if (CheckCallReferenceOwnership(view, ctx) is { } terminal)
            return terminal;
        return EvalResult<IReadOnlyList<NeedCell>>.Ok(PlanCells(supply.Value));
    }

    /// <summary>Whether <paramref name="value"/> is an argument view (CallReference S2).</summary>
    internal static bool IsArgumentView(Result value) => value is Result.CallReference { IsArgumentView: true };

    /// <summary>
    /// The builtins an argument view supports as its WHOLE collection (CallReference S2). Lean:
    /// <c>Builtin.readsArgumentView</c>.
    /// </summary>
    internal static bool ReadsArgumentView(BuiltinId builtin)
        => builtin is BuiltinId.@count or BuiltinId.@first or BuiltinId.@last;

    /// <summary>The refusal of a builtin that does not read an argument view as its collection.</summary>
    internal static EvalError ArgumentViewUnsupported(BuiltinId builtin)
        => new EvalError.TypeMismatch(ArgumentViewUnsupportedMessage(BuiltinDisplayName(builtin)));

    /// <summary>
    /// <c>count</c>, <c>first</c> and <c>last</c> over an argument view bound as their whole collection
    /// (CallReference S2). <c>count</c> is the number of EFFECTIVE supplied cells, explicit spreads
    /// included, read from the plan's supply — no argument VALUE is demanded. <c>first</c>/<c>last</c>
    /// demand exactly the first/last cell and select its VALUE through the ordinary selection boundary;
    /// an empty supply is the failure <c>first([])</c> reports (<see cref="EvalError.BadIndex"/> in context).
    /// Lean: <c>argumentViewBuiltin</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalArgumentViewBuiltin(BuiltinId builtin, Result.CallReference view, EvalCtx ctx)
    {
        var cells = PrepareArgumentView(view, ctx);
        if (cells.IsError) return cells.Error;
        if (builtin == BuiltinId.@count)
            return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(cells.Value.Count), 1));
        if (cells.Value.Count == 0)
            return ArgumentViewEmptySelection(builtin);
        var selected = cells.Value[builtin == BuiltinId.@first ? 0 : cells.Value.Count - 1].Demand();
        return selected.IsError ? selected.Error : SelectedArgumentViewValue(selected.Value.Value, view, ctx);
    }

    /// <summary>MIRROR OF <see cref="EvalArgumentViewBuiltin"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalArgumentViewBuiltinAsync(BuiltinId builtin, Result.CallReference view, EvalCtx ctx)
    {
        var cells = await PrepareArgumentViewAsync(view, ctx).ConfigureAwait(false);
        if (cells.IsError) return cells.Error;
        if (builtin == BuiltinId.@count)
            return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(cells.Value.Count), 1));
        if (cells.Value.Count == 0)
            return ArgumentViewEmptySelection(builtin);
        var selected = await cells.Value[builtin == BuiltinId.@first ? 0 : cells.Value.Count - 1].DemandAsync().ConfigureAwait(false);
        return selected.IsError ? selected.Error : SelectedArgumentViewValue(selected.Value.Value, view, ctx);
    }

    // `first`/`last` over an empty view: the ordinary empty-collection selection failure (Q-27).
    // Lean: `argumentViewEmptySelection`.
    private static EvalError ArgumentViewEmptySelection(BuiltinId builtin)
        => new EvalError.WithContext(
            $"{BuiltinDisplayName(builtin)} selects from an empty collection, which has no position to select",
            new EvalError.BadIndex());

    // A selected cell's VALUE at the selection boundary, after the run's continuation is observed again:
    // a cell demand never absorbs a terminal run.
    private static EvalResult<CountedResult> SelectedArgumentViewValue(Result value, Result.CallReference view, EvalCtx ctx)
        => CheckCallReferenceOwnership(view, ctx) is { } terminal
            ? terminal
            : EvalResult<CountedResult>.Ok(new CountedResult(value, value.ValueCount()));

    /// <summary>
    /// The cell an argument-view selection reads at the validated position <paramref name="index"/>
    /// (CallReference S2): the plan's supply decides the position (<see cref="EvalError.BadIndex"/> past
    /// its end, positioned at the selector's slot); the cell is returned undemanded, so only it is
    /// demanded. Lean: the supply read of <c>selectViewWith</c>.
    /// </summary>
    private static EvalResult<NeedCell> ArgumentViewSelectedCell(
        IReadOnlyList<NeedCell> cells, int index, Expr slot, Expr selection)
        => index < cells.Count
            ? EvalResult<NeedCell>.Ok(cells[index])
            : new EvalError.BadIndex { Span = slot.Span ?? selection.Span };

    /// <summary>
    /// One fresh execution of <paramref name="plan"/> outside its owner's VALUE flight (an explicit
    /// invocation), at the call's value boundary. Lean: <c>NeedPlan.invoke</c> (<c>invokeNeedCall</c>).
    /// </summary>
    internal static EvalResult<CountedResult> InvokePlan(InvocationPlan plan)
        => ReCountValueBoundary(EvalPlannedCallCounted(plan, byInvocation: true));

    /// <summary>The async twin of <see cref="InvokePlan"/>.</summary>
    internal static async ValueTask<EvalResult<CountedResult>> InvokePlanAsync(InvocationPlan plan)
        => ReCountValueBoundary(await EvalPlannedCallCountedAsync(plan, byInvocation: true).ConfigureAwait(false));

    /// <summary>
    /// One execution of <paramref name="plan"/>. As the owner's VALUE it runs inside that cell's single
    /// flight (<paramref name="byInvocation"/> false); as an explicit invocation it runs outside it.
    /// Lean: <c>NeedPlan.execute</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalPlannedCallCounted(InvocationPlan plan, bool byInvocation)
    {
        var ctx = plan.Caller;
        var call = plan.Source;
        // The call node's dispatch checkpoint, which EvalCounted charges before its Call arm.
        if (ctx.Budget.TryChargeExpressionNodeWork() is { } nodeWorkError)
            return nodeWorkError;
        var name = CallDiagnosticName.FromExpression(call.Function);
        var callee = ResolveCallee(call.Function, ctx);
        if (callee.IsError)
            return WithSpanOf<CountedResult>(call, CalleeResolutionFailure(name, ctx, callee.Error));
        return WithSpanOf(call, WithCallCtx(name, ctx, DispatchPlannedCounted(plan, callee.Value, name, byInvocation)));
    }

    /// <summary>
    /// <see cref="EvalResolvedCallCounted"/> over the plan's supply instead of a fresh formation. It keeps
    /// the same arms and the same charges in the same places, and the same shared-deconstruction projection
    /// before any supply. FAIL-CLOSED difference, implementation-only: the fused sequence pipeline
    /// (<see cref="TryEvaluateSequencePipeline"/>) is not attempted, so the generic composition runs. Fusion
    /// never forms the argument supply nor completes the argument cells the generic call completes, so a
    /// fused VALUE would leave the plan without the supply and cell outcomes a later observation needs.
    /// </summary>
    private static EvalResult<CountedResult> DispatchPlannedCounted(
        InvocationPlan plan, Algorithm callee, CallDiagnosticName name, bool byInvocation)
    {
        var ctx = plan.Caller;
        if (callee is Algorithm.Alias alias)
        {
            var target = ResolveAliasTarget(alias, ctx);
            return target.IsError ? target.Error : DispatchPlannedCounted(plan, target.Value, name, byInvocation);
        }

        if (callee is Algorithm.Builtin(var builtinId))
        {
            var supply = PreparePlanSupplyCounted(plan, PlanSupplyShape.BuiltinArguments, byInvocation);
            if (supply.IsError) return supply.Error;
            return ApplyBuiltinCountedResolved(builtinId, PlanBuiltinArguments(supply.Value), ctx, plan.Values);
        }

        if (TryGetFlatBinderUserEquivalent(callee) is { } simpleCallee)
            return DispatchPlannedUserCounted(plan, simpleCallee, name, byInvocation);

        if (callee is Algorithm.Conditional)
        {
            if (ctx.Budget.TryEnterInvocation() is { } limitError)
                return AtFirstSpanIfMissing(limitError, plan.Source.Args);
            try
            {
                var supply = PreparePlanSupplyCounted(plan, PlanSupplyShape.Cells, byInvocation);
                if (supply.IsError) return supply.Error;
                return EvalNeedFamilySupplyCounted(callee, PlanCells(supply.Value), ctx, plan.Values, name);
            }
            finally
            {
                ctx.Budget.ExitInvocation();
            }
        }

        return DispatchPlannedUserCounted(plan, callee, name, byInvocation);
    }

    /// <summary>The user arm of <see cref="DispatchPlannedCounted"/>: <see cref="EvalUserCallCounted"/> over the plan's supply.</summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> DispatchPlannedUserCounted(
        InvocationPlan plan, Algorithm callee, CallDiagnosticName name, bool byInvocation)
    {
        var ctx = plan.Caller;
        var args = plan.Source.Args;
        if (TryEnterDynamicInvocation(ctx, UserCallLimitSpan(args), out var level) is { } limitError)
            return limitError;
        using (level)
        {
            if (callee is Algorithm.User { AssignmentDeconstructionTarget: { } target } helper
                && TryProjectSharedDeconstructionTarget(helper, target, args, ctx, plan.Values) is { } projected)
                return projected.IsError ? projected.Error : EvalResult<CountedResult>.Ok(new(projected.Value, projected.Value.ValueCount()));
            var supply = PreparePlanSupplyCounted(plan, PlanSupplyShape.Cells, byInvocation);
            if (supply.IsError) return supply.Error;
            return EvalNeedUserSupplyCounted(callee, PlanCells(supply.Value), ctx, plan.Values, name, variadicArityStyle: true);
        }
    }

    /// <summary>MIRROR OF <see cref="EvalPlannedCallCounted"/> — keep in lock-step (with <see cref="EvalCallCountedExprAsync"/>'s strategy pin).</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalPlannedCallCountedAsync(InvocationPlan plan, bool byInvocation)
    {
        var ctx = plan.Caller;
        var call = plan.Source;
        if (ctx.Budget.TryChargeExpressionNodeWork() is { } nodeWorkError)
            return nodeWorkError;
        ThrowIfAsyncStrategyPinningViolated(ctx);
        var name = CallDiagnosticName.FromExpression(call.Function);
        var callee = ResolveCallee(call.Function, ctx);
        if (callee.IsError)
            return WithSpanOf<CountedResult>(call, CalleeResolutionFailure(name, ctx, callee.Error));
        return WithSpanOf(call, WithCallCtx(name, ctx,
            await DispatchPlannedAsync(plan, callee.Value, name, byInvocation).ConfigureAwait(false)));
    }

    /// <summary>MIRROR OF <see cref="DispatchPlannedCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> DispatchPlannedAsync(
        InvocationPlan plan, Algorithm callee, CallDiagnosticName name, bool byInvocation)
    {
        var ctx = plan.Caller;
        if (callee is Algorithm.Alias alias)
        {
            var target = ResolveAliasTarget(alias, ctx);
            return target.IsError
                ? target.Error
                : await DispatchPlannedAsync(plan, target.Value, name, byInvocation).ConfigureAwait(false);
        }

        if (callee is Algorithm.Builtin(var builtinId))
        {
            var supply = await PreparePlanSupplyAsync(plan, PlanSupplyShape.BuiltinArguments, byInvocation).ConfigureAwait(false);
            if (supply.IsError) return supply.Error;
            return await ApplyBuiltinCountedResolvedAsync(builtinId, PlanBuiltinArguments(supply.Value), ctx, plan.Values).ConfigureAwait(false);
        }

        if (TryGetFlatBinderUserEquivalent(callee) is { } simpleCallee)
            return await DispatchPlannedUserAsync(plan, simpleCallee, name, byInvocation).ConfigureAwait(false);

        if (callee is Algorithm.Conditional)
        {
            if (ctx.Budget.TryEnterInvocation() is { } limitError)
                return AtFirstSpanIfMissing(limitError, plan.Source.Args);
            try
            {
                var supply = await PreparePlanSupplyAsync(plan, PlanSupplyShape.Cells, byInvocation).ConfigureAwait(false);
                if (supply.IsError) return supply.Error;
                return await EvalNeedFamilySupply(callee, PlanCells(supply.Value), ctx, plan.Values, name, asynchronous: true).ConfigureAwait(false);
            }
            finally
            {
                ctx.Budget.ExitInvocation();
            }
        }

        return await DispatchPlannedUserAsync(plan, callee, name, byInvocation).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="DispatchPlannedUserCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> DispatchPlannedUserAsync(
        InvocationPlan plan, Algorithm callee, CallDiagnosticName name, bool byInvocation)
    {
        var ctx = plan.Caller;
        var args = plan.Source.Args;
        if (TryEnterDynamicInvocation(ctx, UserCallLimitSpan(args), out var level) is { } limitError)
            return limitError;
        using (level)
        {
            if (callee is Algorithm.User { AssignmentDeconstructionTarget: { } target } helper
                && await TryProjectSharedDeconstructionTargetAsync(helper, target, args, ctx, plan.Values).ConfigureAwait(false) is { } projected)
                return projected.IsError ? projected.Error : EvalResult<CountedResult>.Ok(new(projected.Value, projected.Value.ValueCount()));
            var supply = await PreparePlanSupplyAsync(plan, PlanSupplyShape.Cells, byInvocation).ConfigureAwait(false);
            if (supply.IsError) return supply.Error;
            return await EvalNeedUserSupply(callee, PlanCells(supply.Value), ctx, plan.Values, name, asynchronous: true, variadicArityStyle: true).ConfigureAwait(false);
        }
    }

    // ── The plan's ONE supply preparation (Lean NeedPlan.prepare) ──────────────────────────────────────

    /// <summary>
    /// The plan's supply: the prepared outcome if there is one (no evaluator runs), otherwise exactly one
    /// formation through the ordinary <see cref="FormNeedSupply"/> in the caller context (ordinary slots
    /// suspended, spreads opened now), whose outcome — success, ordinary failure, host exception or
    /// cancellation — becomes final. A party that finds a preparation in progress waits for it, unless the
    /// preparation is its own (a re-entrant preparation is <see cref="EvalError.DemandCycle"/>; Lean
    /// <c>preparing → demandCycle</c>). No lock is held while user code (a spread operand) runs, and the
    /// uncontended path takes no lock at all (one compare-exchange to start, one exchange to publish).
    /// <paramref name="shape"/> selects the prepared shape the first consumer reads: a plan's callee is
    /// resolved identically on every execution, so one plan always takes the same arm, and an argument
    /// view records the neutral shape either arm reads (<see cref="SourcedPlanSupply"/>).
    /// </summary>
    private static EvalResult<object> PreparePlanSupplyCounted(InvocationPlan plan, PlanSupplyShape shape, bool byInvocation)
    {
        var state = Volatile.Read(ref plan.Supply);
        if (state is null)
        {
            var marker = byInvocation ? PlanPreparation.ByInvocation : PlanPreparation.ByValue;
            if (Interlocked.CompareExchange(ref plan.Supply, marker, null) is null)
                return RunPlanPreparationCounted(plan, shape, byInvocation);
            state = Volatile.Read(ref plan.Supply);
        }
        return state is PlanPreparation ? JoinPlanPreparationCounted(plan) : PlanSupplyOutcome(state!);
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<object> RunPlanPreparationCounted(InvocationPlan plan, PlanSupplyShape shape, bool byInvocation)
    {
        var previous = PreparingInvocations.Value;
        if (byInvocation) PreparingInvocations.Value = new InvocationPreparationFrame(plan, previous);
        try
        {
            var args = plan.Source.Args;
            var sources = shape == PlanSupplyShape.Cells ? null : new List<Expr?>(args.Count);
            var formed = FormNeedSupply(args, plan.Caller, plan.Values, asynchronous: false, sources).GetAwaiter().GetResult();
            return PublishPlanSupply(plan, formed, shape, sources);
        }
        catch (Exception error)
        {
            PublishPlanSupply(plan, ExceptionDispatchInfo.Capture(error));
            throw;
        }
        finally
        {
            if (byInvocation) PreparingInvocations.Value = previous;
        }
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<object> JoinPlanPreparationCounted(InvocationPlan plan)
    {
        while (true)
        {
            var state = Volatile.Read(ref plan.Supply);
            if (state is not PlanPreparation preparing) return PlanSupplyOutcome(state!);
            if (IsReentrantPlanPreparation(plan, preparing)) return new EvalError.DemandCycle { Span = plan.Source.Span };
            if (EnsurePlanWaiters(plan, preparing) is { } waiters)
                waiters.Task.GetAwaiter().GetResult();
        }
    }

    /// <summary>MIRROR OF <see cref="PreparePlanSupplyCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<object>> PreparePlanSupplyAsync(InvocationPlan plan, PlanSupplyShape shape, bool byInvocation)
    {
        var state = Volatile.Read(ref plan.Supply);
        if (state is null)
        {
            var marker = byInvocation ? PlanPreparation.ByInvocation : PlanPreparation.ByValue;
            if (Interlocked.CompareExchange(ref plan.Supply, marker, null) is null)
                return await RunPlanPreparationAsync(plan, shape, byInvocation).ConfigureAwait(false);
        }
        while (true)
        {
            state = Volatile.Read(ref plan.Supply);
            if (state is not PlanPreparation preparing) return PlanSupplyOutcome(state!);
            if (IsReentrantPlanPreparation(plan, preparing)) return new EvalError.DemandCycle { Span = plan.Source.Span };
            if (EnsurePlanWaiters(plan, preparing) is { } waiters)
                await waiters.Task.ConfigureAwait(false);
        }
    }

    /// <summary>MIRROR OF <see cref="RunPlanPreparationCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<object>> RunPlanPreparationAsync(InvocationPlan plan, PlanSupplyShape shape, bool byInvocation)
    {
        var previous = PreparingInvocations.Value;
        if (byInvocation) PreparingInvocations.Value = new InvocationPreparationFrame(plan, previous);
        try
        {
            var args = plan.Source.Args;
            var sources = shape == PlanSupplyShape.Cells ? null : new List<Expr?>(args.Count);
            var formed = await FormNeedSupply(args, plan.Caller, plan.Values, asynchronous: true, sources).ConfigureAwait(false);
            return PublishPlanSupply(plan, formed, shape, sources);
        }
        catch (Exception error)
        {
            PublishPlanSupply(plan, ExceptionDispatchInfo.Capture(error));
            throw;
        }
        finally
        {
            if (byInvocation) PreparingInvocations.Value = previous;
        }
    }

    private static EvalResult<object> PublishPlanSupply(
        InvocationPlan plan, EvalResult<IReadOnlyList<NeedCell>> formed, PlanSupplyShape shape, List<Expr?>? sources)
    {
        if (formed.IsError)
        {
            PublishPlanSupply(plan, formed.Error);
            return formed.Error;
        }
        object prepared = shape switch
        {
            PlanSupplyShape.Cells => formed.Value,
            PlanSupplyShape.BuiltinArguments => BuiltinPlanArguments(formed.Value, sources!),
            _ => new SourcedPlanSupply(formed.Value, sources!),
        };
        PublishPlanSupply(plan, prepared);
        return EvalResult<object>.Ok(prepared);
    }

    // Records the final outcome (never changed again) and wakes the waiters, if any. The formation count
    // is published first, so an observer that sees the outcome also sees the count.
    private static void PublishPlanSupply(InvocationPlan plan, object outcome)
    {
        Interlocked.Increment(ref plan.Formations);
        plan.Caller.Observations?.RecordPlanSupplyFormation();
        if (Interlocked.Exchange(ref plan.Supply, outcome) is PlanPreparation { Waiters: { } waiters })
            waiters.TrySetResult();
    }

    // Returns the completion source to wait on, or null when the slot changed and must be read again.
    private static TaskCompletionSource? EnsurePlanWaiters(InvocationPlan plan, PlanPreparation preparing)
    {
        if (preparing.Waiters is { } existing) return existing;
        var waiting = new PlanPreparation(preparing.IsByInvocation, new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously));
        return ReferenceEquals(Interlocked.CompareExchange(ref plan.Supply, waiting, preparing), preparing) ? waiting.Waiters : null;
    }

    // A preparation the current flow itself is running would wait on itself: a VALUE-initiated one when
    // the flow is inside the owner's VALUE evaluation, an invocation-initiated one when the flow's
    // invocation frames contain the plan.
    private static bool IsReentrantPlanPreparation(InvocationPlan plan, PlanPreparation preparing)
    {
        if (!preparing.IsByInvocation) return plan.Owner.IsEvaluatingInCurrentFlow();
        for (var frame = PreparingInvocations.Value; frame is not null; frame = frame.Parent)
            if (ReferenceEquals(frame.Plan, plan)) return true;
        return false;
    }

    private static EvalResult<object> PlanSupplyOutcome(object final)
    {
        if (final is EvalError error) return error;
        if (final is ExceptionDispatchInfo exception) exception.Throw();
        return EvalResult<object>.Ok(final);
    }

    private static ResolvedArgumentAlgorithm[] BuiltinPlanArguments(IReadOnlyList<NeedCell> cells, IReadOnlyList<Expr?> sources)
    {
        var arguments = new ResolvedArgumentAlgorithm[cells.Count];
        for (var i = 0; i < arguments.Length; i++)
            arguments[i] = new ResolvedArgumentAlgorithm(null) { Cell = cells[i], Source = sources[i] };
        return arguments;
    }

    // The prepared supply as the cells a user or family arm binds. A builtin-shaped supply cannot reach a
    // user arm (a plan's callee resolves identically on every execution); the conversion is defensive.
    // A supply an argument view prepared (S2) is read in either shape.
    private static IReadOnlyList<NeedCell> PlanCells(object prepared) => prepared switch
    {
        IReadOnlyList<NeedCell> cells => cells,
        SourcedPlanSupply sourced => sourced.Cells,
        ResolvedArgumentAlgorithm[] arguments => Array.ConvertAll(arguments, static argument => argument.Cell!),
        _ => throw new InvalidOperationException($"Unexpected prepared plan supply '{prepared.GetType().Name}'."),
    };

    // The prepared supply as a builtin's arguments. A cell list prepared by a user arm cannot reach a
    // builtin arm; the conversion is defensive and records no written source (diagnostic identity only).
    // A supply an argument view prepared keeps its written sources (S2).
    private static IReadOnlyList<ResolvedArgumentAlgorithm> PlanBuiltinArguments(object prepared) => prepared switch
    {
        ResolvedArgumentAlgorithm[] arguments => arguments,
        SourcedPlanSupply sourced => BuiltinPlanArguments(sourced.Cells, sourced.Sources),
        IReadOnlyList<NeedCell> cells => cells.Select(static cell => new ResolvedArgumentAlgorithm(null) { Cell = cell }).ToArray(),
        _ => throw new InvalidOperationException($"Unexpected prepared plan supply '{prepared.GetType().Name}'."),
    };

    /// <summary>
    /// The META receiver arm of a host-operation wrapper body in a test-seam run (<see cref="InvocationPlanTestSeam.MetaReceivers"/>). The receiver
    /// gets the wrapper's supplied cells, which are the transported originals. Their VALUE is NOT
    /// demanded.
    /// </summary>
    private static EvalResult<Result>? TryInvokeMetaReceiver(HostOperation hostOperation, IReadOnlyList<string> argNames, EvalCtx ctx)
    {
        if (ctx.Budget.PlanTestSeam is not { } seam
            || !seam.MetaReceivers.TryGetValue(hostOperation.Name, out var receiver))
            return null;
        var cells = new NeedCell?[argNames.Count];
        for (var i = 0; i < cells.Length; i++)
            cells[i] = ParameterNeedCell(argNames[i], ctx);
        var value = receiver(cells);
        // A receiver can inspect a failed demand/invocation and return its own value. A reached
        // resource limit or cancellation still ends the run (NEED-09); the seam cannot absorb it.
        if (ctx.Budget.CheckContinuation() is { } terminal) return terminal;
        return EvalResult<Result>.Ok(NormalizeHostOperationValue(hostOperation, value));
    }

    /// <summary>A plan's prepared argument cells, in order (test observation of <see cref="InvocationPlan.PrepareSupply"/>).</summary>
    internal sealed record PreparedSupply(IReadOnlyList<NeedCell> Cells);

    // ── CallReference S1 diagnostics (Lean: invokeRequires…Message, callReference…Message) ─────────

    /// <summary><c>R.Invoke</c> without an argument list: the intrinsic is never a property read.</summary>
    internal const string InvokeRequiresArgumentListMessage =
        "`Invoke` is a call-reference operation, not a property: write `R.Invoke()`.";

    /// <summary>Text conversion (interpolation, display) of a value that contains a call reference.</summary>
    internal const string CallReferenceHasNoTextMessage =
        "A call reference has no text: use a value computed from it, for example `R.Invoke()`.";

    /// <summary>A run result or another host-facing value that contains a call reference.</summary>
    internal const string CallReferenceLeavesRunMessage =
        "A call reference cannot leave its run: return a value computed from it, for example `R.Invoke()`.";

    /// <summary><c>x.Invoke()</c> whose receiver VALUE is not a call reference.</summary>
    internal static string InvokeRequiresCallReferenceMessage(Result value)
        => $"`Invoke` requires a call reference, got {DescribeOperand(value)}";

    // ── CallReference S2 diagnostics (Lean: arguments…Message, argumentView…Message) ─────────────

    /// <summary><c>R.Arguments(…)</c>: the view is a property of the reference, never an operation.</summary>
    internal const string ArgumentsIsPropertyMessage =
        "`Arguments` is a call-reference property, not an operation: write `R.Arguments`.";

    /// <summary><c>x.Arguments</c> whose receiver VALUE is not a call reference.</summary>
    internal static string ArgumentsRequiresCallReferenceMessage(Result value)
        => $"`Arguments` requires a call reference, got {DescribeOperand(value)}";

    /// <summary>A spread that would open an argument view into values.</summary>
    internal const string ArgumentViewSpreadMessage =
        "An argument view spreads only into an argument list, as `F(R.Arguments*)`; select its values with `R.Arguments[i]`.";

    /// <summary>A collection builtin other than <c>count</c>, <c>first</c> and <c>last</c> over an argument view.</summary>
    internal static string ArgumentViewUnsupportedMessage(string builtinName)
        => $"An argument view supports only `count`, `first`, `last`, selection and an argument spread, not `{builtinName}`.";

    /// <summary>
    /// Whether <paramref name="value"/> CONTAINS a call reference at any depth of its sequence and list
    /// structure. Iterative and DAG-safe: each shared structure node is expanded once (reference-identity
    /// memo), and a call reference is a leaf — its plan, cells and context are never followed.
    /// Lean: <c>Result.containsCallRef</c>.
    /// </summary>
    internal static bool ContainsCallReference(Result value)
    {
        if (StructureItemsOf(value) is not { } items)
            return value is Result.CallReference;

        // The structure being scanned is held in registers; a nested structure is deferred to the
        // lazily allocated stack, so a flat result (the common case) allocates nothing.
        Stack<IReadOnlyList<Result>>? pending = null;
        HashSet<Result>? expanded = null;
        while (true)
        {
            foreach (var item in items)
            {
                if (item is Result.CallReference)
                    return true;
                if (StructureItemsOf(item) is { Count: > 0 } nested
                    && (expanded ??= new HashSet<Result>(ReferenceEqualityComparer.Instance)).Add(item))
                    (pending ??= new Stack<IReadOnlyList<Result>>()).Push(nested);
            }

            if (pending is null || !pending.TryPop(out items!))
                return false;
        }

        static IReadOnlyList<Result>? StructureItemsOf(Result node) => node switch
        {
            Result.SequenceValue(var sequenceItems) => sequenceItems,
            Result.ListValue(var listItems) => listItems,
            _ => null,
        };
    }

    /// <summary>
    /// THE RUN RESULT BOUNDARY (CallReference S1, J4): a call reference is run-scoped, so a value that
    /// contains one is refused wherever it would leave the language — a run result, a host-operation
    /// argument, a host-operation return value, display and formatting — and every reference-free value
    /// passes unchanged. Lean: <c>exportRunValue</c> (the run result).
    /// </summary>
    internal static EvalError? CallReferenceBoundaryError(Result value)
        => ContainsCallReference(value) ? new EvalError.TypeMismatch(CallReferenceLeavesRunMessage) : null;

    /// <summary>The run result boundary applied to a run's counted outcome.</summary>
    internal static EvalResult<CountedResult> ExportRunValue(EvalResult<CountedResult> result)
        => result.IsOk && CallReferenceBoundaryError(result.Value.Value) is { } refused ? refused : result;

    /// <summary>The run result boundary applied to a run's value outcome.</summary>
    internal static EvalResult<Result> ExportRunValue(EvalResult<Result> result)
        => result.IsOk && CallReferenceBoundaryError(result.Value) is { } refused ? refused : result;

    /// <summary>The run result boundary applied to a run's output and its named top-level property.</summary>
    internal static EvalResult<CountedRootProgramResult> ExportRunValue(EvalResult<CountedRootProgramResult> result)
    {
        if (!result.IsOk)
            return result;
        if (CallReferenceBoundaryError(result.Value.Output.Value) is { } refusedOutput)
            return refusedOutput;
        return result.Value.TopLevelProperty is { } property && CallReferenceBoundaryError(property.Value) is { } refusedProperty
            ? refusedProperty
            : result;
    }

    // ── J7: the program gate of invocation-plan retention ──────────────────────────────────────────

    /// <summary>
    /// The J7 fact of <paramref name="expr"/> exactly as a run's admission decides it: the structural
    /// preflight's walk over the program, testing every node it visits with
    /// <see cref="AstStructuralPreflight.MayCaptureCalls"/> (the run itself takes the fact from its own
    /// preflight, <see cref="PrepareAdmittedRun"/>, with no second traversal). A tree the preflight refuses
    /// never runs; it is reported as possibly capturing (the conservative answer).
    /// </summary>
    internal static bool ProgramMayCaptureCalls(Expr expr)
        => AstStructuralPreflight.CheckAdmittedProgram(
                expr, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.EvaluatorIterativeJoinSpines, out var mayCaptureCalls) is not null
            || mayCaptureCalls;
}
