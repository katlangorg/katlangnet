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
/// ONE supply slot holding the plan's preparation state (Lean <c>NeedCell.plan : NeedPlanSupply</c>) and ONE
/// observation slot: the route of a written form whose route is not its source alone (META-S3-4,
/// <see cref="PlanRouteOf"/>; Lean <c>NeedCell.route</c>), moved together with the reference and the
/// canonical callee cell into an out-of-line holder only when an observation (META, <c>Invoke()</c>,
/// <c>.Algorithm</c>, a loop, an <c>.Algorithm</c>-route execution) needs either. The supply slot
/// holds the very supply object the dispatch consumes (the formed cell list, or a builtin's argument array),
/// so retaining the supply after VALUE allocates nothing beyond the ordinary call. On the VALUE path there is
/// no flight, reference or supply-holder object: a waiter's completion source is allocated only when a second party
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
    /// The structured refusal of a route-dependent reference operation over a captured invocation whose
    /// route is a non-callable intrinsic (META-S3-4, D-1A): <c>5.string()</c>, <c>R.Invoke()</c>,
    /// <c>R.Arguments(…)</c>. Lean: <c>NeedPlan.invocationRefusal</c>.
    /// </summary>
    internal const string InvocationRefusalDescription = "meta: not a callable invocation";

    /// <summary>
    /// THE INVOCATION DOMAIN (META-S3-4, CR-2, D-2A; Lean: <c>NeedPlan.callShape?</c>): a WRITTEN invocation —
    /// a call whose callee is a lexical name, a parameter or an argumentless dot path (every call the parser
    /// produces, <c>(t.Algorithm)(args)</c> included), or an argument-bearing dot edge <c>t.N(args)</c> (an
    /// explicitly empty list included). The decision is syntactic, total and evaluation-free: it never asks
    /// what the written form invokes (the plan's route, <see cref="PlanRouteOf"/>, decides that later).
    /// Argumentless dot edges (<c>5.Inc</c>, <c>Box.G</c>), names, values, computed and host-built callees
    /// keep the ordinary cell, and META refuses them.
    /// </summary>
    private static bool IsPlannableCall(Expr expression)
        => expression is Expr.Call { Function: Expr.Resolve or Expr.Param or Expr.DotCall { Args: null } }
            or Expr.DotCall { Args: not null };

    // ── META-S3-4: the plan's ROUTE (what a written invocation form invokes) ─────────────────────────────

    /// <summary>
    /// What a plan's written invocation form invokes (META-S3-4; Lean: <c>PlanRoute</c>):
    /// <list type="bullet">
    /// <item><see cref="Call"/> — a written call <c>f(args)</c> (its callee resolved by the one callee law on
    /// every execution), a call through a declared member spelled <c>Algorithm</c> included;</item>
    /// <item><see cref="Member"/> — <c>t.N(args)</c> selecting a declared member: callee the argumentless path
    /// <c>t.N</c> (DOT-09), supply <c>args</c>;</item>
    /// <item><see cref="AlgorithmIntrinsic"/> — <c>t.Algorithm(args)</c> or <c>(t.Algorithm)(args)</c> on a
    /// structural miss: callee the link <c>t.Algorithm</c> (CR-15), whose ONE receiver cell the plan's VALUE,
    /// every <c>Invoke()</c>, <c>.Algorithm</c> and a loop share (D-3), supply <c>args</c>;</item>
    /// <item><see cref="Extension"/> — <c>t.F(args)</c> on any other structural miss: the extension call
    /// <c>F(t, args)</c> (DOT-03, D-5), callee the lexical fallback, supply <c>t, args</c>;</item>
    /// <item><see cref="Intrinsic"/> — <c>t.string(…)</c>, <c>t.Invoke(…)</c>, <c>t.Arguments(…)</c> on a structural
    /// miss: no callable invocation (D-1A) — VALUE is the ordinary dot evaluation, every route-dependent
    /// reference operation the refusal <see cref="InvocationRefusalDescription"/>.</item>
    /// </list>
    /// </summary>
    internal enum PlanRouteKind : byte { Call, Member, AlgorithmIntrinsic, Extension, Intrinsic }

    /// <summary>
    /// A plan's retained route (<see cref="InvocationPlan.RouteState"/>). The three routes that carry no data
    /// are shared singletons, so a call-form plan and an intrinsic or <c>.Algorithm</c> dot plan allocate no
    /// route object; only a member route (the selected member and its wired algorithm, so executions
    /// never repeat the selection) and an extension route (its receiver-first bundle) allocate one.
    /// </summary>
    internal sealed class PlanRoute
    {
        internal static readonly PlanRoute Call = new(PlanRouteKind.Call);
        internal static readonly PlanRoute AlgorithmIntrinsic = new(PlanRouteKind.AlgorithmIntrinsic);
        internal static readonly PlanRoute Intrinsic = new(PlanRouteKind.Intrinsic);

        internal PlanRoute(PlanRouteKind kind) => Kind = kind;

        internal PlanRouteKind Kind { get; }

        /// <summary>Member route: the selected member (it keys an alias member's binding).</summary>
        internal Property? Member { get; init; }

        /// <summary>Member route: the member wired to its receiver (an alias is chased per execution).</summary>
        internal Algorithm? Wired { get; init; }

        /// <summary>Extension route: the effective bundle <c>t, args</c> (<see cref="BuildLexicalReceiverCallArgs"/>).</summary>
        internal OutputBundle? ExtensionArgs { get; init; }
    }

    /// <summary>
    /// The plan's route (Lean: <c>NeedPlan.routeOf</c>), decided ONCE by the first route-dependent operation —
    /// VALUE, <c>Invoke()</c>, reading the argument supply, <c>.Algorithm</c>, loop setup — and retained
    /// (compare-and-set: the first publication wins; a route failure is retained as the plan's failure,
    /// never absence). A name or parameter call — and a call through any argumentless path other than an
    /// <c>X.Algorithm</c> edge — has the call route by its source: nothing is classified or allocated.
    /// Classification is identity-only (<see cref="ComputePlanRoute"/>: the ordinary receiver resolution
    /// and the ONE dot-edge decision <see cref="SelectDotEdge"/>); through a runtime-projection receiver it
    /// performs that projection's existing single-flight receiver demand (D-4). A computation that ran
    /// under a non-initiating observation reporting a pending step is never retained.
    /// </summary>
    internal static EvalResult<PlanRoute> PlanRouteOf(InvocationPlan plan)
    {
        if (!plan.NeedsRoute) return EvalResult<PlanRoute>.Ok(PlanRoute.Call);
        if (plan.RouteState is { } known)
            return known is PlanRoute route ? EvalResult<PlanRoute>.Ok(route) : (EvalError)known;
        var computed = ComputePlanRoute(plan);
        if (NeedCell.CurrentObservation?.Pending is not null || (computed.IsError && NeedCell.IsObservationPending(computed.Error)))
            return computed;
        var final = plan.PublishRouteState(computed.IsOk ? computed.Value : computed.Error);
        return final is PlanRoute retained ? EvalResult<PlanRoute>.Ok(retained) : (EvalError)final;
    }

    /// <summary>MIRROR OF <see cref="PlanRouteOf"/>: the route through the async resolution adapter (S3-0b),
    /// which awaits a suspended runtime receiver instead of blocking on it.</summary>
    internal static ValueTask<EvalResult<PlanRoute>> PlanRouteOfAsync(InvocationPlan plan)
    {
        if (!plan.NeedsRoute) return ValueTask.FromResult(EvalResult<PlanRoute>.Ok(PlanRoute.Call));
        if (plan.RouteState is { } known)
            return ValueTask.FromResult(known is PlanRoute route ? EvalResult<PlanRoute>.Ok(route) : (EvalError)known);
        return ResolveAsync(plan.Caller, plan, static p => PlanRouteOf(p));
    }

    /// <summary>
    /// Classifies a plan's route (Lean: <c>classifyPlanRouteWith</c>): a call through an <c>X.Algorithm</c>
    /// edge takes the <c>.Algorithm</c> route fact (<see cref="IsAlgorithmIntrinsicRoute"/>, as
    /// <see cref="EvalCallCountedExpr"/> does); an argument-bearing dot edge resolves its receiver and takes
    /// the ordinary dot decision (<see cref="SelectDotEdge"/>, exactly as <see cref="EvalDotCallCounted"/>):
    /// a member, the <c>.Algorithm</c> intrinsic, a non-callable intrinsic, or the extension call. A receiver
    /// or selection failure is the route's failure.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<PlanRoute> ComputePlanRoute(InvocationPlan plan)
    {
        var ctx = plan.Caller;
        if (plan.Source is Expr.Call call)
        {
            var intrinsic = IsAlgorithmIntrinsicRoute((Expr.DotCall)call.Function, ctx);
            if (intrinsic.IsError) return intrinsic.Error;
            return EvalResult<PlanRoute>.Ok(intrinsic.Value ? PlanRoute.AlgorithmIntrinsic : PlanRoute.Call);
        }

        var dot = (Expr.DotCall)plan.Source;
        var target = ResolveDotReceiver(dot.Target, ctx, out _);
        if (target.IsError && !IsAbsentIdentity(target.Error))
            return target.Error;
        var receiver = target.IsError ? null : target.Value;
        if (SelectDotEdge(dot, receiver, ctx, out var route, out var member) is { } selectionError)
            return selectionError;
        return EvalResult<PlanRoute>.Ok(route switch
        {
            DotEdgeRoute.Member => new PlanRoute(PlanRouteKind.Member)
            {
                Member = member,
                Wired = ChildOfInContext(receiver!, member!.Value, ctx),
            },
            DotEdgeRoute.AlgorithmIntrinsic => PlanRoute.AlgorithmIntrinsic,
            DotEdgeRoute.Extension => new PlanRoute(PlanRouteKind.Extension)
            {
                ExtensionArgs = BuildLexicalReceiverCallArgs(dot.Target, dot.Args),
            },
            _ => PlanRoute.Intrinsic,
        });
    }

    /// <summary>A callable route, or the D-1A refusal for an intrinsic route.</summary>
    private static EvalResult<PlanRoute> InvocationRouteOf(EvalResult<PlanRoute> route, InvocationPlan plan)
        => route.IsOk && route.Value.Kind == PlanRouteKind.Intrinsic ? InvocationRefusal(plan) : route;

    private static EvalError InvocationRefusal(InvocationPlan plan)
        => new EvalError.NotAnAlgorithm(InvocationRefusalDescription) { Span = plan.Owner.Span };

    /// <summary>
    /// The plan's canonical callee cell after its route (CR-13): the route is established first (D-4), an
    /// intrinsic route is the D-1A refusal. Lean: <c>NeedPlan.calleeCell</c>.
    /// </summary>
    internal static EvalResult<NeedCell> PlanCalleeCell(InvocationPlan plan)
    {
        var route = InvocationRouteOf(PlanRouteOf(plan), plan);
        return route.IsError ? route.Error : EvalResult<NeedCell>.Ok(plan.CalleeCell);
    }

    /// <summary>MIRROR OF <see cref="PlanCalleeCell"/> — the route through the async resolution adapter.</summary>
    internal static async ValueTask<EvalResult<NeedCell>> PlanCalleeCellAsync(InvocationPlan plan)
    {
        var route = InvocationRouteOf(await PlanRouteOfAsync(plan).ConfigureAwait(false), plan);
        return route.IsError ? route.Error : EvalResult<NeedCell>.Ok(plan.CalleeCell);
    }

    /// <summary>The written callee name a fresh call of the plan's callee reports (route known).</summary>
    private static CallDiagnosticName PlanCalleeName(InvocationPlan plan)
        => CallDiagnosticName.FromExpression(plan.CalleeExpression);

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

        /// <summary>The plan's supply slot (see the type summary). Written only by the plan's preparation.</summary>
        internal object? Supply;

        // Written only by PublishPlanSupply; read through SupplyFormations.
        internal int Formations;

        /// <summary>
        /// The plan's OBSERVATION slot (P1, implementation-only): the state no ordinary VALUE of a call-form
        /// plan reads, kept out of line so a plan that is never observed carries one slot for it instead of
        /// three. <c>null</c> until needed; then either the plan's established route alone — a
        /// <see cref="PlanRoute"/> or the route's <see cref="EvalError"/>, so the VALUE of a route-bearing
        /// plan allocates nothing more — or a <see cref="PlanObservation"/> holding the route (if any), the
        /// one reference and the canonical callee cell. A route never changes once written, and the slot only
        /// moves from <c>null</c> to a route, from <c>null</c> to a holder, or from a route to a holder that
        /// carries it, so every reader sees the same route.
        /// </summary>
        private object? _observation;

        /// <summary>The out-of-line observation state (<see cref="_observation"/>); each field is written once.</summary>
        private sealed class PlanObservation(object? routeState)
        {
            internal object? RouteState = routeState;
            internal Result.CallReference? Reference;
            internal NeedCell? CalleeCell;
        }

        /// <summary>
        /// META-S3-4: the retained route of a plan that <see cref="NeedsRoute"/> — <c>null</c> until
        /// established, then a <see cref="PlanRoute"/> or the route's <see cref="EvalError"/>, never changed
        /// again (Lean <c>NeedCell.route</c>). Written only by <see cref="PlanRouteOf"/>, through
        /// <see cref="PublishRouteState"/>.
        /// </summary>
        internal object? RouteState
        {
            get
            {
                var state = Volatile.Read(ref _observation);
                return state is PlanObservation holder ? Volatile.Read(ref holder.RouteState) : state;
            }
        }

        /// <summary>
        /// Publishes a computed route (first writer wins) and returns the retained one: <paramref name="computed"/>
        /// or the route another party published first.
        /// </summary>
        internal object PublishRouteState(object computed)
        {
            while (true)
            {
                var state = Volatile.Read(ref _observation);
                if (state is PlanObservation holder)
                    return Interlocked.CompareExchange(ref holder.RouteState, computed, null) ?? computed;
                if (state is not null) return state;
                if (Interlocked.CompareExchange(ref _observation, computed, null) is null) return computed;
            }
        }

        // The holder, created on the first observation that needs one; it carries a route already published.
        private PlanObservation Observation
        {
            get
            {
                while (true)
                {
                    var state = Volatile.Read(ref _observation);
                    if (state is PlanObservation holder) return holder;
                    var created = new PlanObservation(state);
                    if (ReferenceEquals(Interlocked.CompareExchange(ref _observation, created, state), state)) return created;
                }
            }
        }

        /// <summary>The supplied cell this plan belongs to: its original VALUE cell.</summary>
        internal NeedCell Owner => _owner!;

        /// <summary>The written invocation (the owner's source): a call or an argument-bearing dot edge.</summary>
        internal Expr Source => _owner!.Source!;

        /// <summary>
        /// Whether the route is more than the source says (META-S3-4): an argument-bearing dot edge, or a
        /// call through an <c>X.Algorithm</c> edge. Every other call is the call route by its source.
        /// </summary>
        internal bool NeedsRoute
            => Source is Expr.DotCall || (Source is Expr.Call { Function: Expr.DotCall { Args: null } edge } && edge.UsesDotAlgorithmIntrinsic());

        /// <summary>The established route (only read after a route-establishing operation succeeded).</summary>
        internal PlanRoute Route
            => !NeedsRoute ? PlanRoute.Call
                : RouteState as PlanRoute ?? EstablishedRoute(this);

        /// <summary>The bundle the plan's ONE supply forms (route known): an extension's is receiver-first.</summary>
        internal OutputBundle Args => Source switch
        {
            Expr.Call call => call.Args,
            Expr.DotCall dot => Route.ExtensionArgs ?? dot.Args!,
            _ => throw new InvalidOperationException("Not a plannable invocation."),
        };

        /// <summary>
        /// The written callee the plan's callee cell supplies (route known; CR-13): a call's callee, the
        /// argumentless member path or <c>.Algorithm</c> edge of a dot edge, or an extension's lexical fallback.
        /// </summary>
        internal Expr CalleeExpression => Source switch
        {
            Expr.Call call => call.Function,
            Expr.DotCall dot => Route.Kind == PlanRouteKind.Extension ? dot.EffectiveLexicalFallback : dot.ArgumentlessEdge(),
            _ => throw new InvalidOperationException("Not a plannable invocation."),
        };

        // Called once, by the owning cell's constructor, before the cell is published.
        internal void Attach(NeedCell owner) => _owner = owner;

        /// <summary>The plan's one reference, allocated on the first META. Every META returns this same object.</summary>
        internal Result.CallReference Reference
        {
            get
            {
                var holder = Observation;
                return Volatile.Read(ref holder.Reference)
                    ?? Interlocked.CompareExchange(ref holder.Reference, new Result.CallReference(this), null)
                    ?? holder.Reference!;
            }
        }

        /// <summary>
        /// The plan's ONE canonical callee cell (META-S3-1, CR-13; Lean <c>NeedPlan.calleeCell</c>): the
        /// route's callee supplied in the captured caller context (<see cref="CalleeCellOf"/>), established
        /// on the first observation that needs it and retained. Read it after the route
        /// (<see cref="PlanCalleeCell"/>); once the route is established, establishing the cell evaluates,
        /// prepares and demands nothing; a racing establishment may construct a candidate that is discarded
        /// unused.
        /// </summary>
        internal NeedCell CalleeCell
        {
            get
            {
                var holder = Observation;
                return Volatile.Read(ref holder.CalleeCell)
                    ?? Interlocked.CompareExchange(ref holder.CalleeCell, CalleeCellOf(this), null)
                    ?? holder.CalleeCell!;
            }
        }

        // Test observation only: whether an observation moved the slot to its out-of-line holder.
        internal bool HasObservationHolder => Volatile.Read(ref _observation) is PlanObservation;

        // Test observation only: whether the callee cell has been established.
        internal bool HasCalleeCell
            => Volatile.Read(ref _observation) is PlanObservation holder && Volatile.Read(ref holder.CalleeCell) is not null;

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
            // META-S3-4: the route first, through the async adapter when asynchronous (never the
            // synchronous resolver under the async engine), with the D-1A refusal of an intrinsic route.
            var route = InvocationRouteOf(asynchronous ? await PlanRouteOfAsync(this).ConfigureAwait(false) : PlanRouteOf(this), this);
            if (route.IsError) return route.Error;
            var supply = asynchronous
                ? await PreparePlanSupplyAsync(this, PlanSupplyShape.Cells, byInvocation: true).ConfigureAwait(false)
                : PreparePlanSupplyCounted(this, PlanSupplyShape.Cells, byInvocation: true);
            return supply.IsError ? supply.Error : EvalResult<PreparedSupply>.Ok(new PreparedSupply(PlanCells(supply.Value)));
        }
    }

    /// <summary>
    /// The route read before any route-establishing operation — test seams that read the callee cell or
    /// the bundle directly. Production operations establish the route first.
    /// </summary>
    private static PlanRoute EstablishedRoute(InvocationPlan plan)
    {
        var route = PlanRouteOf(plan);
        return route.IsOk ? route.Value : throw new InvalidOperationException("The plan's route failed: " + route.Error);
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
    /// The binder's META capture of the parameter <paramref name="name"/> (META-DIAG-1):
    /// <see cref="ReferenceAdapterCell"/>, its canonical refusal (<see cref="MetaRefusalDescription"/>)
    /// framed with the parameter's name. Every other outcome — the adapter, a terminal resource failure,
    /// a thrown cancellation or J7 invariant violation — is the capture's own, unchanged. Lean:
    /// <c>NeedBinder.captureMeta</c>.
    /// </summary>
    private static EvalResult<NeedCell> CaptureMeta(string name, NeedCell cell, EvalCtx ctx)
    {
        var adapter = ReferenceAdapterCell(cell, ctx);
        return adapter.IsError ? AnnotateMetaBindingRefusal(name, adapter.Error) : adapter;
    }

    /// <summary>
    /// META-DIAG-1: the binder's report of a failed capture of the META parameter <paramref name="name"/>.
    /// Only the canonical capture refusal gains the frame naming the parameter, positioned where the
    /// refusal is (the supplied argument); any other error — the D-1A invocation refusal included —
    /// passes unchanged. Lean: <c>NeedPlan.bindingRefusal</c>.
    /// </summary>
    internal static EvalError AnnotateMetaBindingRefusal(string name, EvalError error)
        => error is EvalError.NotAnAlgorithm { Description: MetaRefusalDescription }
            ? new EvalError.WithContext(MetaParameterContext(name), error) { Span = error.Span }
            : error;

    /// <summary>The binder frame of a META parameter's refusal. Lean: <c>NeedPlan.metaParameterContext</c>.</summary>
    internal static string MetaParameterContext(string name) => $"while binding meta parameter '{name}'";

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
    /// <c>Invoke()</c> — over the bundle of the plan's ROUTE (META-S3-4, CR-9/D-4: the route is
    /// established first by identity resolution, which through a runtime-projection receiver performs
    /// that projection's existing receiver demand), WITHOUT dispatching the target and without demanding
    /// any argument VALUE (formation demands nothing; only an arbitrary spread's own evaluation runs). An unprepared
    /// plan records the neutral <see cref="SourcedPlanSupply"/>. The view's ownership is checked before
    /// any plan work and again after a formation, so a terminal run is never absorbed.
    /// Lean: <c>NeedPlan.viewCells</c> (<c>argumentViewCells</c>).
    /// </summary>
    internal static EvalResult<IReadOnlyList<NeedCell>> PrepareArgumentView(Result.CallReference view, EvalCtx ctx)
    {
        if (CheckCallReferenceOwnership(view, ctx) is { } rejected)
            return rejected;
        // META-S3-4 (D-4/D-5): which bundle the supply is (`t.F(a)` supplies `t, a`) is the plan's route,
        // established here — identity resolution, never the target's dispatch; an intrinsic route has
        // no callable supply (D-1A).
        var route = InvocationRouteOf(PlanRouteOf(view.Plan), view.Plan);
        if (route.IsError) return route.Error;
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
        var route = InvocationRouteOf(await PlanRouteOfAsync(view.Plan).ConfigureAwait(false), view.Plan);
        if (route.IsError) return route.Error;
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
    /// flight (<paramref name="byInvocation"/> false); as an explicit invocation it runs outside it. The
    /// node's dispatch checkpoint, then the plan's route (META-S3-4), then the route's ordinary phases under
    /// the written form's own frame: a call form exactly as <see cref="EvalCallCountedExpr"/> (its
    /// <c>.Algorithm</c> callee as <see cref="EvalAlgorithmCalleeCallCounted"/>), a dot edge exactly as
    /// <see cref="EvalCounted"/>'s dot arm. Lean: <c>NeedPlan.execute</c> / <c>executeAlong</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalPlannedCallCounted(InvocationPlan plan, bool byInvocation)
    {
        var ctx = plan.Caller;
        // The node's dispatch checkpoint, which EvalCounted charges before its Call / DotCall arm.
        if (ctx.Budget.TryChargeExpressionNodeWork() is { } nodeWorkError)
            return nodeWorkError;
        if (plan.Source is Expr.DotCall dot)
            return WithSpanOf(dot, WithDotCallCtx(dot, ctx, DispatchPlannedDotCounted(plan, dot, byInvocation)));
        var call = (Expr.Call)plan.Source;
        var name = CallDiagnosticName.FromExpression(call.Function);
        if (plan.NeedsRoute)
        {
            var route = PlanRouteOf(plan);
            if (route.IsError)
                return WithSpanOf<CountedResult>(call, CalleeResolutionFailure(name, ctx, route.Error));
            if (route.Value.Kind == PlanRouteKind.AlgorithmIntrinsic)
                return EvalPlannedAlgorithmCalleeCallCounted(plan, call, name, byInvocation);
        }
        var callee = ResolveCallee(call.Function, ctx);
        if (callee.IsError)
            return WithSpanOf<CountedResult>(call, CalleeResolutionFailure(name, ctx, callee.Error));
        return WithSpanOf(call, WithCallCtx(name, ctx, DispatchPlannedCounted(plan, callee.Value, name, byInvocation)));
    }

    /// <summary>
    /// A planned <c>(t.Algorithm)(args)</c> on the intrinsic route: exactly <see cref="EvalAlgorithmCalleeCallCounted"/>
    /// — the receiver, decoded, and the captured callee's CALLABLE, each failure the callee's resolution
    /// failure — over the plan's ONE retained receiver cell (D-3) and ONE supply.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalPlannedAlgorithmCalleeCallCounted(
        InvocationPlan plan, Expr.Call call, CallDiagnosticName name, bool byInvocation)
    {
        var ctx = plan.Caller;
        var edge = (Expr.DotCall)call.Function;
        var callee = ProjectPlannedAlgorithmCallee(plan, edge, spanDecodeFailure: true);
        if (callee.IsError)
            return WithSpanOf<CountedResult>(call, CalleeResolutionFailure(name, ctx, callee.Error));
        return WithSpanOf(call, WithCallCtx(name, ctx, DispatchPlannedCounted(plan, callee.Value.Callee, callee.Value.Name, byInvocation)));
    }

    /// <summary>
    /// The planned dot invocation (META-S3-4): the route's dispatch over the plan's ONE supply, with the
    /// ordinary dot evaluation's charges, contexts and spans (the caller attaches the dot-call context and
    /// span as <see cref="EvalCounted"/> does). Each callable route ends in the shared final dispatcher
    /// <see cref="DispatchPlannedCounted"/>; a non-callable intrinsic route is the ordinary dot evaluation
    /// as VALUE and the D-1A refusal as an invocation.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> DispatchPlannedDotCounted(InvocationPlan plan, Expr.DotCall dot, bool byInvocation)
    {
        var ctx = plan.Caller;
        var route = PlanRouteOf(plan);
        if (route.IsError) return route.Error;
        switch (route.Value.Kind)
        {
            case PlanRouteKind.Member:
            {
                // MIRROR OF the member arm of EvalDotCallCounted: an alias member is called as its
                // target through its own binding (EvalAliasMemberCounted, the CALLABLE chase).
                var wired = route.Value.Wired!;
                if (wired is Algorithm.Alias alias)
                {
                    var target = ResolveBindingAliasTarget(route.Value.Member!, alias, ctx, callable: true);
                    if (target.IsError) return target.Error;
                    wired = target.Value;
                }
                return DispatchPlannedCounted(plan, wired, CallDiagnosticName.FromKnown(dot.Name), byInvocation);
            }
            case PlanRouteKind.Extension:
            {
                // MIRROR OF CallLexicalWithReceiverCounted: the stored fallback identity decides the channel.
                var callee = dot.EffectiveLexicalFallback is Expr.Resolve(var fallbackName)
                    ? ResolveNamedAlgorithm(fallbackName, span: null, ctx)
                    : ResolveAlg(dot.EffectiveLexicalFallback, ctx);
                if (callee.IsError) return callee.Error;
                var name = dot.EffectiveLexicalFallback is Expr.Resolve(var known) ? known : dot.Name;
                return DispatchPlannedCounted(plan, callee.Value, CallDiagnosticName.FromKnown(name), byInvocation);
            }
            case PlanRouteKind.AlgorithmIntrinsic:
            {
                var callee = ProjectPlannedAlgorithmCallee(plan, dot, spanDecodeFailure: false);
                if (callee.IsError) return callee.Error;
                return DispatchPlannedCounted(plan, callee.Value.Callee, callee.Value.Name, byInvocation);
            }
            default:
                return byInvocation ? InvocationRefusal(plan) : EvalDotCallCounted(dot, ctx, plan.Values);
        }
    }

    /// <summary>
    /// The callee of a planned <c>t.Algorithm(args)</c> / <c>(t.Algorithm)(args)</c> on the intrinsic route
    /// (CR-14 c): the plan's ONE retained receiver cell — its callee cell is the link <c>t.Algorithm</c>, whose
    /// receiver cell evaluates through the ordinary invocation receiver evaluator
    /// (<see cref="EvalAlgorithmReceiver"/>; a parameter receiver is that parameter's own cell), so the
    /// receiver is demanded at most once for the plan, shared by its VALUE, every <c>Invoke()</c>, its
    /// <c>.Algorithm</c> and a loop (D-3) — decoded, then the captured plan's callee cell's CALLABLE, named by
    /// that plan's written callee. Every step's failure is reported as the ordinary intrinsic reports it: a
    /// receiver failure as it is, a decode failure positioned at the edge in callee position
    /// (<paramref name="spanDecodeFailure"/>), a missing identity as the captured callee's absence.
    /// </summary>
    private static EvalResult<(Algorithm Callee, CallDiagnosticName Name)> ProjectPlannedAlgorithmCallee(
        InvocationPlan plan, Expr.DotCall edge, bool spanDecodeFailure)
    {
        var link = plan.CalleeCell;
        var receiverCell = ((LinkSuspension)link.Suspension!).Receiver((Expr.DotCall)link.Source!);
        // Transporting a parameter retains its original cell (D-3), but an invocation still reads
        // the WRITTEN parameter through the ordinary receiver evaluator. In particular, an absent
        // CALLABLE takes Eval(param), including its dispatch checkpoint; an algorithm receiver takes
        // the uncharged parameter-demand route. Demanding the transported cell directly erases that
        // distinction and changes ordinary VALUE accounting merely because J7 retained a plan.
        var receiver = edge.Target is Expr.Param
            ? EvalAlgorithmReceiver(edge, plan.Caller, plan.Values)
            : ProjectCountedValue(receiverCell.Demand());
        if (receiver.IsError) return receiver.Error;
        var captured = DecodeAlgorithmReceiver(receiver.Value, plan.Caller);
        if (captured.IsError)
            return spanDecodeFailure ? captured.Error with { Span = captured.Error.Span ?? edge.Span } : captured.Error;
        var calleeCell = PlanCalleeCell(captured.Value);
        if (calleeCell.IsError) return calleeCell.Error;
        var callable = RequireCapturedCallee(calleeCell.Value.ProjectCallable(), edge.Span);
        if (callable.IsError) return callable.Error;
        return EvalResult<(Algorithm, CallDiagnosticName)>.Ok((callable.Value, PlanCalleeName(captured.Value)));
    }

    /// <summary>MIRROR OF <see cref="ProjectPlannedAlgorithmCallee"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<(Algorithm Callee, CallDiagnosticName Name)>> ProjectPlannedAlgorithmCalleeAsync(
        InvocationPlan plan, Expr.DotCall edge, bool spanDecodeFailure)
    {
        var link = plan.CalleeCell;
        var receiverCell = ((LinkSuspension)link.Suspension!).Receiver((Expr.DotCall)link.Source!);
        var receiver = edge.Target is Expr.Param
            ? await EvalAlgorithmReceiverAsync(edge, plan.Caller, plan.Values).ConfigureAwait(false)
            : ProjectCountedValue(await receiverCell.DemandAsync().ConfigureAwait(false));
        if (receiver.IsError) return receiver.Error;
        var captured = DecodeAlgorithmReceiver(receiver.Value, plan.Caller);
        if (captured.IsError)
            return spanDecodeFailure ? captured.Error with { Span = captured.Error.Span ?? edge.Span } : captured.Error;
        var calleeCell = await PlanCalleeCellAsync(captured.Value).ConfigureAwait(false);
        if (calleeCell.IsError) return calleeCell.Error;
        var callable = RequireCapturedCallee(await ProjectCellCallableAsync(calleeCell.Value, plan.Caller).ConfigureAwait(false), edge.Span);
        if (callable.IsError) return callable.Error;
        return EvalResult<(Algorithm, CallDiagnosticName)>.Ok((callable.Value, PlanCalleeName(captured.Value)));
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
                return AtFirstSpanIfMissing(limitError, plan.Args);
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
        var args = plan.Args;
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
        if (ctx.Budget.TryChargeExpressionNodeWork() is { } nodeWorkError)
            return nodeWorkError;
        ThrowIfAsyncStrategyPinningViolated(ctx);
        if (plan.Source is Expr.DotCall dot)
            return WithSpanOf(dot, WithDotCallCtx(dot, ctx, await DispatchPlannedDotAsync(plan, dot, byInvocation).ConfigureAwait(false)));
        var call = (Expr.Call)plan.Source;
        var name = CallDiagnosticName.FromExpression(call.Function);
        if (plan.NeedsRoute)
        {
            var route = await PlanRouteOfAsync(plan).ConfigureAwait(false);
            if (route.IsError)
                return WithSpanOf<CountedResult>(call, CalleeResolutionFailure(name, ctx, route.Error));
            if (route.Value.Kind == PlanRouteKind.AlgorithmIntrinsic)
            {
                var projected = await ProjectPlannedAlgorithmCalleeAsync(plan, (Expr.DotCall)call.Function, spanDecodeFailure: true).ConfigureAwait(false);
                if (projected.IsError)
                    return WithSpanOf<CountedResult>(call, CalleeResolutionFailure(name, ctx, projected.Error));
                return WithSpanOf(call, WithCallCtx(name, ctx,
                    await DispatchPlannedAsync(plan, projected.Value.Callee, projected.Value.Name, byInvocation).ConfigureAwait(false)));
            }
        }
        // META-S3-0b: the ONE callee law through the async resolution adapter.
        var callee = await ResolveCalleeAsync(call.Function, ctx).ConfigureAwait(false);
        if (callee.IsError)
            return WithSpanOf<CountedResult>(call, CalleeResolutionFailure(name, ctx, callee.Error));
        return WithSpanOf(call, WithCallCtx(name, ctx,
            await DispatchPlannedAsync(plan, callee.Value, name, byInvocation).ConfigureAwait(false)));
    }

    /// <summary>MIRROR OF <see cref="DispatchPlannedDotCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> DispatchPlannedDotAsync(InvocationPlan plan, Expr.DotCall dot, bool byInvocation)
    {
        var ctx = plan.Caller;
        var route = await PlanRouteOfAsync(plan).ConfigureAwait(false);
        if (route.IsError) return route.Error;
        switch (route.Value.Kind)
        {
            case PlanRouteKind.Member:
            {
                var wired = route.Value.Wired!;
                if (wired is Algorithm.Alias alias)
                {
                    var target = await ResolveAliasTargetAsync(alias, ctx, route.Value.Member!).ConfigureAwait(false);
                    if (target.IsError) return target.Error;
                    wired = target.Value;
                }
                return await DispatchPlannedAsync(plan, wired, CallDiagnosticName.FromKnown(dot.Name), byInvocation).ConfigureAwait(false);
            }
            case PlanRouteKind.Extension:
            {
                var fallback = dot.EffectiveLexicalFallback;
                var callee = fallback is Expr.Resolve(var fallbackName)
                    ? await ResolveAsync(ctx, (fallbackName, ctx), static state => ResolveNamedAlgorithm(state.fallbackName, span: null, state.ctx)).ConfigureAwait(false)
                    : await ResolveAsync(ctx, (fallback, ctx), static state => ResolveAlg(state.fallback, state.ctx)).ConfigureAwait(false);
                if (callee.IsError) return callee.Error;
                var name = fallback is Expr.Resolve(var known) ? known : dot.Name;
                return await DispatchPlannedAsync(plan, callee.Value, CallDiagnosticName.FromKnown(name), byInvocation).ConfigureAwait(false);
            }
            case PlanRouteKind.AlgorithmIntrinsic:
            {
                var callee = await ProjectPlannedAlgorithmCalleeAsync(plan, dot, spanDecodeFailure: false).ConfigureAwait(false);
                if (callee.IsError) return callee.Error;
                return await DispatchPlannedAsync(plan, callee.Value.Callee, callee.Value.Name, byInvocation).ConfigureAwait(false);
            }
            default:
                return byInvocation ? InvocationRefusal(plan) : await EvalDotCallCountedAsync(dot, ctx, plan.Values).ConfigureAwait(false);
        }
    }

    /// <summary>MIRROR OF <see cref="DispatchPlannedCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> DispatchPlannedAsync(
        InvocationPlan plan, Algorithm callee, CallDiagnosticName name, bool byInvocation)
    {
        var ctx = plan.Caller;
        if (callee is Algorithm.Alias alias)
        {
            var target = await ResolveAliasTargetAsync(alias, ctx).ConfigureAwait(false);
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
                return AtFirstSpanIfMissing(limitError, plan.Args);
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
        var args = plan.Args;
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
            var args = plan.Args;
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
            var args = plan.Args;
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
        return NormalizeHostOperationValue(hostOperation, value, ctx.Budget, ctx.Observations?.StructuralTraversal);
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
        => ScanForCallReference(value, budget: null, ScanBudgetUse.None, observations: null, completed: null, out _);

    /// <summary>
    /// <see cref="ContainsCallReference(Result)"/> for one of SEVERAL values classified together, which may
    /// share structure: <paramref name="completed"/> holds completed presence verdicts by reference
    /// identity. A fully inspected structure is clean; finding a reference proves its open ancestors
    /// forbidden, never clean. Completed clean prefixes remain reusable even when a later sibling is
    /// forbidden. Both verdicts are reused across roots (the root-property observation snapshot).
    /// </summary>
    internal static bool ContainsCallReference(Result value, Dictionary<Result, bool> completed)
        => ScanForCallReference(value, budget: null, ScanBudgetUse.None, observations: null, completed, out _);

    /// <summary>
    /// The HOST-ARGUMENT boundary (CallReference S1, J4; charged since SEC-01-FU): the
    /// <see cref="CallReferenceBoundaryError"/> scan of one host-operation argument, charged to the run as
    /// structural work. Unlike the once-per-run result export, this scan repeats for EVERY host call, so a
    /// program passing one large nested value to many calls re-walked it uncharged and uncancellably per
    /// call. Each nested structure now costs one unit per slot plus one for the structure (the unit of
    /// <c>Result.AdmitHostOperationValue</c>; the top-level value's own slots are free, so flat and scalar
    /// arguments charge nothing), flushed through <see cref="EvaluationBudget.TryChargeStructuralWork"/> —
    /// which observes cancellation — whenever 256 units are pending and at the end. A refused charge is the
    /// run's terminal limit error; a contained reference stays the ordinary <c>TypeMismatch</c>.
    /// Indexed continuation frames retain only open ancestors, and the depth-first scan charges
    /// only inspected slots and completed nested verdicts, including empty structures, never an
    /// untouched suffix. Memoized structures are not scanned or completed again.
    /// </summary>
    internal static EvalError? HostArgumentBoundaryError(
        Result value,
        EvaluationBudget budget,
        ValueTraversalObservations? observations)
    {
        var found = ScanForCallReference(value, budget, ScanBudgetUse.ChargeStructuralWork, observations, completed: null, out var limit);
        return limit ?? (found ? new EvalError.TypeMismatch(CallReferenceLeavesRunMessage) : null);
    }

    /// <summary>How <see cref="ScanForCallReference"/> uses the run budget it is given.</summary>
    private enum ScanBudgetUse : byte
    {
        /// <summary>No budget: the context-free <see cref="ContainsCallReference(Result)"/>.</summary>
        None,

        /// <summary>The host-argument boundary: nested structure work is charged (<see cref="HostArgumentBoundaryError"/>).</summary>
        ChargeStructuralWork,

        /// <summary>The run-result export: nothing is charged, cancellation is observed (<see cref="RunExportBoundaryError"/>).</summary>
        ObserveCancellation,
    }

    /// <summary>
    /// The one call-reference scan (<see cref="ContainsCallReference(Result)"/>). With
    /// <see cref="ScanBudgetUse.ChargeStructuralWork"/> it charges nested structure work to
    /// <paramref name="budget"/> (<see cref="HostArgumentBoundaryError"/>), and a refused charge stops the
    /// scan with <paramref name="limit"/> set; with <see cref="ScanBudgetUse.ObserveCancellation"/> it charges
    /// nothing and observes the run's cancellation whenever at least
    /// <see cref="Result.ValueSemanticComparer.UnitsPerCharge"/> slots were inspected since the last
    /// checkpoint (<see cref="RunExportBoundaryError"/>). A non-null <paramref name="completed"/> is the
    /// cross-scan memo of <see cref="ContainsCallReference(Result, Dictionary{Result, bool})"/>.
    /// </summary>
    private static bool ScanForCallReference(
        Result value,
        EvaluationBudget? budget,
        ScanBudgetUse budgetUse,
        ValueTraversalObservations? observations,
        Dictionary<Result, bool>? completed,
        out EvalError? limit)
    {
        limit = null;
        var exporting = budgetUse == ScanBudgetUse.ObserveCancellation;
        if (exporting)
            observations?.RecordRunExportScan();
        if (StructureItemsOf(value) is not { } items)
            return value is Result.CallReference;
        if (completed is not null && completed.TryGetValue(value, out var cached))
            return cached;

        // Indexed continuations keep pending storage proportional to depth, never to the
        // number of sibling structures. Flat values need neither a memo nor a stack, and
        // indexing avoids a boxed enumerator.
        Stack<(Result Node, int Next)>? pending = null;
        HashSet<Result>? expanded = null;
        var current = value;
        var next = 0;
        var isRoot = true;
        var units = 0;
        var uncheckedSlots = 0;
        while (true)
        {
            var segmentStart = next;
            var found = false;
            IReadOnlyList<Result>? descend = null;
            Result? descendNode = null;
            while (next < items.Count)
            {
                var item = items[next++];
                if (item is Result.CallReference)
                {
                    found = true;
                    break;
                }

                if (StructureItemsOf(item) is not { } nestedItems)
                    continue;

                if (completed is not null && completed.TryGetValue(item, out var nestedVerdict))
                {
                    if (!nestedVerdict)
                        continue;
                    found = true;
                    break;
                }

                if ((expanded ??= new HashSet<Result>(ReferenceEqualityComparer.Instance)).Add(item))
                {
                    descend = nestedItems;
                    descendNode = item;
                    break;
                }
            }

            if (exporting)
            {
                var inspected = next - segmentStart;
                observations?.RecordRunExportScanSlots(inspected);
                // A cancellation checkpoint per block of inspected slots, never a charge: the
                // export scan runs once, after evaluation, over a value the run already paid for.
                uncheckedSlots += inspected;
                if (uncheckedSlots >= Result.ValueSemanticComparer.UnitsPerCharge)
                {
                    uncheckedSlots = 0;
                    observations?.RecordRunExportScanCancellationCheckpoint();
                    budget!.ObserveCancellation();
                }
            }
            else if (budgetUse == ScanBudgetUse.ChargeStructuralWork && !isRoot)
            {
                units += next - segmentStart;
                // Finding a reference completes every open nested verdict. Otherwise only
                // a fully scanned frame completes. Never charge an untouched sibling/suffix.
                if (found)
                    units += pending!.Count;
                else if (descend is null)
                    units++;
            }

            var done = found || (descend is null && (pending is null || pending.Count == 0));
            if (units > 0 && (done || units >= Result.ValueSemanticComparer.UnitsPerCharge))
            {
                observations?.RecordStructuralWorkCharge(units);
                limit = budget!.TryChargeStructuralWork(units);
                units = 0;
                if (limit is not null)
                    return false;
            }

            if (completed is not null)
            {
                if (found)
                {
                    // Only the active path contains this reference. Earlier completed siblings
                    // keep their clean verdict; unvisited suffixes acquire no verdict at all.
                    completed[current] = true;
                    if (pending is not null)
                    {
                        foreach (var ancestor in pending)
                            completed[ancestor.Node] = true;
                    }
                }
                else if (descend is null)
                    completed[current] = false;
            }

            if (done)
                return found;

            if (descend is not null)
            {
                (pending ??= new()).Push((current, next));
                if (exporting)
                    observations?.RecordRunExportScanPendingFrames(pending.Count);
                else
                    observations?.RecordCallReferenceScanPendingFrames(pending.Count);
                items = descend;
                current = descendNode!;
                next = 0;
                isRoot = false;
            }
            else
            {
                (current, next) = pending!.Pop();
                items = StructureItemsOf(current)!;
                isRoot = pending.Count == 0;
            }
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

    /// <summary>
    /// THE RUN-RESULT EXPORT (CallReference S1, J4; SEC-01-FU2): <see cref="CallReferenceBoundaryError"/> for
    /// one value a run hands out, given the run's root context <paramref name="ctx"/>.
    ///
    /// <para><b>Skipped when no reference can exist.</b> A <see cref="Result.CallReference"/> (a reference or
    /// its argument view) is constructed only from an <see cref="InvocationPlan"/>, and a plan is allocated
    /// only in a run that RETAINS plans (<see cref="SupplyCell"/> under
    /// <see cref="EvaluationBudget.RetainsInvocationPlans"/>: the J7 gate or a test seam, decided once before
    /// evaluation and never switched off). No reference enters a run from outside: every run result,
    /// host-operation argument and interpolation refuses one, a host-operation return holding one is a host
    /// contract violation (<c>Result.AdmitHostOperationValue</c> throws), the property cache is keyed by run,
    /// and hosts cannot construct one. So a run that does not retain plans holds no reference anywhere, and
    /// its result is exported as is, with no traversal. Every retaining run — META-capable programs,
    /// programs with a deferred module region, test seams — keeps the full scan.</para>
    ///
    /// <para><b>Charging and cancellation.</b> The export scan runs ONCE, after evaluation, over a value the
    /// run already built and paid for (the memo bounds the walk by distinct nodes and their slots), so it
    /// charges no step or structural work: a successful run never fails merely because its result was
    /// inspected. Unlike the per-host-call argument scan (<see cref="HostArgumentBoundaryError"/>, charged),
    /// it observes cancellation at segment boundaries after at least
    /// <see cref="Result.ValueSemanticComparer.UnitsPerCharge"/> inspected slots. Each segment is bounded
    /// by one admitted collection's slots (<see cref="EvaluationLimits.MaxCollectionItems"/>). It throws
    /// the run token's <see cref="OperationCanceledException"/> — the outcome of the
    /// completion-boundary check that follows the export, only sooner.</para>
    /// </summary>
    private static EvalError? RunExportBoundaryError(Result value, EvalCtx ctx)
    {
        if (!ctx.Budget.RetainsInvocationPlans)
        {
            ctx.Observations?.StructuralTraversal?.RecordRunExportScanSkipped();
            return null;
        }

        return ScanForCallReference(value, ctx.Budget, ScanBudgetUse.ObserveCancellation,
                ctx.Observations?.StructuralTraversal, completed: null, out _)
            ? new EvalError.TypeMismatch(CallReferenceLeavesRunMessage)
            : null;
    }

    /// <summary>The run result boundary applied to a run's counted outcome (<see cref="RunExportBoundaryError"/>).</summary>
    internal static EvalResult<CountedResult> ExportRunValue(EvalResult<CountedResult> result, EvalCtx ctx)
        => result.IsOk && RunExportBoundaryError(result.Value.Value, ctx) is { } refused ? refused : result;

    /// <summary>The run result boundary applied to a run's value outcome (<see cref="RunExportBoundaryError"/>).</summary>
    internal static EvalResult<Result> ExportRunValue(EvalResult<Result> result, EvalCtx ctx)
        => result.IsOk && RunExportBoundaryError(result.Value, ctx) is { } refused ? refused : result;

    /// <summary>
    /// The run result boundary applied to a run's output AND its named top-level property: both leave the
    /// run, so both are checked (<see cref="RunExportBoundaryError"/>).
    /// </summary>
    internal static EvalResult<CountedRootProgramResult> ExportRunValue(EvalResult<CountedRootProgramResult> result, EvalCtx ctx)
    {
        if (!result.IsOk)
            return result;
        if (RunExportBoundaryError(result.Value.Output.Value, ctx) is { } refusedOutput)
            return refusedOutput;
        return result.Value.TopLevelProperty is { } property && RunExportBoundaryError(property.Value, ctx) is { } refusedProperty
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
                expr, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.EvaluatorIterativeJoinSpines, out var facts) is not null
            || facts.MayCaptureCalls;
}
