using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang;

/// <summary>
/// ALIASES (FWD-02 binding indirection, decided October 1 2026; M4★ whole-algorithm transport,
/// ALIAS-UNIFY-1, October 2026). An <see cref="Algorithm.Alias"/> is a BINDING whose one written row is
/// a reference to an existing algorithm, resolved in the alias's OWN scope at its declaring activation.
/// Two kinds (<see cref="Algorithm.Alias.IsReference"/>):
/// <list type="bullet">
///   <item>a TRANSPARENT REFERENCE (<c>A = R</c>): every observation of <c>A</c> is <c>R</c>'s — its
///   structural identity and members, its open provider, its invocation, its bare VALUE and its
///   publication origin;</item>
///   <item>a STRUCTURAL FORWARDING CARRIER (<c>A = { R }</c>, an inline <c>{ R }</c>): its STRUCTURE is its
///   own (its declaration, its own declarations only, its own namespace), while every explicit
///   invocation forwards its exact supplied computations FRESHLY to <c>R</c>'s target and its bare VALUE
///   delegates to the target's bare view.</item>
/// </list>
/// Three operations read an alias, each by its own chase over ONE definition (<see cref="ChaseAlias"/>,
/// Lean <c>resolveAliasChase</c>), so none can substitute for another: STRUCTURE
/// (<see cref="ResolveAliasStructure"/>) stops at a carrier, INVOCATION (<see cref="ResolveAliasTarget"/>)
/// follows both kinds at any arity, and VALUE (<see cref="ResolveAliasValueTerminal"/>) follows both kinds
/// statically to the TERMINAL binding, whose own zero-argument entry a bare read uses — no alias owns a
/// cache entry (OD-E). An alias is never an invocation: resolving it charges no step and no depth. Every
/// alias branch lives OUT OF LINE (no alias local in a calibrated recursive frame): the recursive
/// dispatch frames only test the variant and delegate here.
/// </summary>
public static partial class Evaluator
{
    /// <summary>
    /// Which reading of an alias a chase performs (M4★; Lean's <c>followCarriers</c> /
    /// <c>projectRuntime</c> flags of <c>resolveAliasChase</c>).
    /// </summary>
    internal enum AliasChase : byte
    {
        /// <summary>The algorithm an explicit call invokes: both kinds followed, runtime steps projected (<c>true</c>, <c>true</c>).</summary>
        Invocation,

        /// <summary>The full algorithm the alias denotes: references followed, a carrier is the end, runtime steps projected (<c>false</c>, <c>true</c>).</summary>
        Structure,

        /// <summary>Where a bare read goes: both kinds followed statically, ending AT the first runtime-target alias (<c>true</c>, <c>false</c>).</summary>
        Value,

        /// <summary>The static structure of a member path's receiver: references followed statically, a carrier is the end, nothing projected (<c>false</c>, <c>false</c>).</summary>
        StaticStructure,
    }

    private static bool FollowsCarriers(AliasChase chase) => chase is AliasChase.Invocation or AliasChase.Value;

    private static bool ProjectsRuntimeSteps(AliasChase chase) => chase is AliasChase.Invocation or AliasChase.Structure;

    /// <summary>How a chase ends (Lean <c>AliasChaseEnd</c>).</summary>
    private enum AliasChaseEndKind : byte
    {
        /// <summary>A non-alias, or a carrier when the chase does not follow carriers.</summary>
        Identity,

        /// <summary>A runtime reference whose binding cell projected NO callable identity.</summary>
        ValueView,

        /// <summary>The first runtime-target alias a chase that projects no runtime step of its own reaches.</summary>
        Runtime,
    }

    /// <summary>
    /// The end of a chase: the algorithm it ends at and, for an <see cref="AliasChaseEndKind.Identity"/>
    /// end, the binding (owner and declaration) of the chase's final STATIC hop, if it took one.
    /// </summary>
    private readonly record struct AliasChaseEnd(AliasChaseEndKind Kind, Algorithm Algorithm, PropertyCallBinding? Last);

    /// <summary>
    /// The memoized STATIC end of an alias binding's chain: the algorithm its static steps reach (a
    /// non-alias, a carrier for a chase that stops there, or the runtime-target alias the static part
    /// stops at) and the binding of the final static hop. A pure function of the memo key.
    /// </summary>
    internal readonly record struct AliasStaticEnd(Algorithm End, PropertyCallBinding? Last);

    /// <summary>
    /// Where a bare VALUE read goes (OD-E, M4★; Lean <c>AliasTerminal</c>): a runtime-target alias
    /// (<see cref="IsRuntime"/>) is its binding cell's VALUE; otherwise <see cref="Algorithm"/> is the
    /// terminal non-alias algorithm, read under its own <see cref="Binding"/> (the terminal binding of a
    /// static chain) — or, with no binding, its own zero-argument demand. <see cref="CrossesCarrier"/>
    /// (Q-36 with M4★): the read crosses a structural carrier, whose bare VALUE is the subordinate
    /// computation of its written row, so a missing output escaping the read is nested in the carrier's
    /// outcome; a transparent reference is its target, so its read is the target's own.
    /// </summary>
    internal readonly record struct AliasTerminal(Algorithm Algorithm, PropertyCallBinding? Binding, bool IsRuntime, bool CrossesCarrier = false);

    /// <summary>
    /// One step of an alias chase: the alias's BINDING identity — its declaration, the structural identity of
    /// the scope chain it is wired under and the nearest activation of that chain — so one declaration under
    /// two activations (a carrier passed from one call into the next) is two steps, never a cycle. Lean:
    /// <c>aliasChaseKey</c>.
    /// </summary>
    private readonly record struct AliasChaseVisit(DeclarationIdentity? Declaration, StructuralOwnerIdentity Scope, ParameterActivation? Activation)
    {
        public static AliasChaseVisit Of(Algorithm.Alias step)
            => new(step.Declaration, StructuralOwnerIdentity.FromScope(step.Parent), AliasMemoOwner(step));
    }

    /// <summary>
    /// THE ALIAS CHASE (FWD-02; runtime targets META-S3-2; M4★ whole-algorithm transport). One definition,
    /// read by <paramref name="chase"/>:
    /// <list type="bullet">
    ///   <item>a structural CARRIER ends a chase that does not follow carriers (STRUCTURE) as its own
    ///   identity, nothing evaluated;</item>
    ///   <item>a RUNTIME step (<see cref="AliasChaseMachine.AdvanceStep"/>) ends a chase that projects no runtime step of
    ///   its own (VALUE, static structure) AT the runtime-target alias, before its binding cell is touched; a projecting
    ///   chase projects the alias's ONE binding cell (<see cref="AliasBindingCell"/>): an identity
    ///   continues the chase AT ANY ARITY (L-RUN), absence ends it as a VALUE VIEW, and a projection
    ///   FAILURE propagates with its kind (never absence);</item>
    ///   <item>a STATIC step resolves the written target in the alias's own scope
    ///   (<see cref="AliasChaseMachine.TakeStep"/>): a name by the ownership-first lookup, RAW, so a target that is
    ///   itself an alias continues the chase; a member path by DECLARED members, each receiver read
    ///   through its STATIC structure.</item>
    /// </list>
    /// <para>NORMALIZED ONCE: every alias BINDING the static part passes through remembers its chain's
    /// static end (<see cref="AliasStaticEnd"/>) under its <see cref="AliasTargetKey"/> — per chase family
    /// (following carriers or not) — so a chain is chased once per declaring scope (and activation); the
    /// runtime identity beyond it is the binding cell's own sticky outcome. Only a successful static part
    /// is remembered.</para>
    /// <para>A step reaching an alias BINDING the chase has already visited — the same declaration in the same
    /// resolving scope under the same activation (<see cref="AliasChaseVisit"/>) — is an alias CYCLE:
    /// <see cref="EvalError.IllegalInEval"/>, never a hop limit and never a stack overflow (only a host-built
    /// tree forms a static one: the surface pass forms none, OD-D, and the pre-evaluation gate rejects
    /// host-built ones); an ACTIVE runtime projection re-entered is the wait-for graph's
    /// <see cref="EvalError.DemandCycle"/> (NEED-09). The STRUCTURE computations a step nests — a member
    /// path's receiver, an <c>.Algorithm</c> row's route decision — inherit only the enclosing STRUCTURE
    /// context: a structure chase's own steps (a receiver leading back into it is a cycle: <c>A = A.F</c>,
    /// <c>A = A.Algorithm</c>), never an invocation or VALUE chase's, whose steps are no structure
    /// computation (<c>A = B</c> / <c>B = { public F(x) = x * x ⏎ A.F }</c>: <c>A(3)</c> is <c>F(3)</c>, the
    /// receiver <c>A</c> read through its structure <c>B</c>). Lean: <c>EvalBody.resolveAliasChase</c>.</para>
    /// <para>NO HOST RECURSION (C# host safety only; Lean has no host stack): those nested structure computations
    /// run on the explicit stack of ONE <see cref="AliasChaseMachine"/>, never as host frames, so one chase over a
    /// chain of any length — whose links are names, member paths through alias receivers or <c>.Algorithm</c>
    /// links — needs constant host stack and work linear in the links it passes.</para>
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<AliasChaseEnd> ChaseAlias(Algorithm.Alias alias, EvalCtx ctx, AliasChase chase, Property? binding = null)
    {
        // A remembered static end that finishes the chase at once — a non-alias, or a carrier for a chase that
        // stops there — needs no machine: exactly the chase loop's first iteration on that memo hit.
        var follow = FollowsCarriers(chase);
        if (binding is not null
            && (follow || alias.IsReference)
            && PeekAliasTargetMemo(binding, alias, ctx, follow) is { } known
            && (known.End is not Algorithm.Alias reached || (!follow && !reached.IsReference)))
            return EvalResult<AliasChaseEnd>.Ok(new AliasChaseEnd(AliasChaseEndKind.Identity, known.End, known.Last));

        // A retry of an asynchronous resolution resumes the chase its previous attempt parked at the projection it
        // reported pending, instead of walking the chain above that projection again.
        if (NeedCell.CurrentObservation is { Record.ParkedChase: AliasChaseMachine parked } observation
            && parked.TryResume(alias, ctx, chase, binding, observation, out var resumed))
            return resumed;

        return new AliasChaseMachine().Chase(alias, ctx, chase, binding);
    }

    /// <summary>
    /// ONE alias chase invocation on an EXPLICIT STACK (C# host safety; implementation-only, Lean recurses on no
    /// host stack). Every chase a step nests — a member path's alias receiver (<see cref="NavigatePath"/>, Lean
    /// <c>aliasStepNavigateWith</c>) and an <c>.Algorithm</c> route decision's alias receiver or member
    /// (<see cref="NavigateRoute"/>, Lean <c>aliasRouteIsIntrinsicWith</c>) — is a <see cref="ChaseFrame"/> pushed
    /// here; the asking frame is suspended mid-navigation and resumed with the nested chase's end. Nothing here
    /// recurses: only a projecting chase's binding-cell projection evaluates, behind the cell's own stack backstop.
    /// <para>THE STRUCTURE CONTEXT is ONE visited set plus an UNDO LOG. A structure chase at the root records its
    /// steps in it; a nested chase adds its own and removes them when it finishes, so the structure computation
    /// that nested it — and everything nested below — sees them while it runs, and a sibling never does. An
    /// invocation or VALUE chase at the root keeps its steps in a set of its own and lends none (the context
    /// is empty whenever control is back at it). This is exactly the snapshot-per-nesting it replaces, in
    /// linear rather than quadratic work: the same visits count as a cycle.</para>
    /// <para>SETTLED ROUTE DECISIONS (implementation-only reuse). An <c>.Algorithm</c> link's route decision
    /// navigated CLEANLY — no alias cycle or static navigation failure, no <c>ResolveAlg</c> fallback, no
    /// non-exported member, and every runtime projection it read a PUBLISHED (sticky) outcome, success or
    /// failure — is recorded per alias declaration and declaring scope on the alias's memo owner
    /// (<see cref="AliasRouteDecision"/>), exactly where its binding cell lives, and reused by every later
    /// chase. It is a function of what it read: the alias's own scope (the static end's and the binding cell's
    /// key), declarations, and published projections, which never change; a later fresh navigation reads the
    /// same facts or a memo of them, and it cannot meet a cycle the first one did not (a structure computation
    /// that encloses the decision and is reached by it was itself reached, uncut, by the first navigation —
    /// cut-offs only grow — whose nested re-entry of the decision would have met that cycle). A navigation that
    /// met a cycle, a flow-local <see cref="EvalError.DemandCycle"/>, a pending observation or a resolution's
    /// recorded-only outcome is never recorded: it stays flow-local and is navigated again. A reused decision
    /// that read projections first observes the run's continuation exactly as its first projection would
    /// (cancellation, terminal run).</para>
    /// <para>PARKED CHASES (async resolution, implementation-only). Inside an asynchronous resolution's
    /// observation (<see cref="ResolveAsync{TState,T}"/>), a runtime projection reported pending suspends the whole
    /// machine in the resolution's flow-local record instead of unwinding it; the resolver's result is discarded
    /// for that attempt anyway. The retry is the same synchronous resolver over a superset of determined facts, so
    /// it reaches the same root chase (same alias, context, reading and binding); that chase resumes at the
    /// projection, which now reads the recorded outcome, rather than walking the chain above it again. Every
    /// frame below the projection holds what a fresh walk would recompute: the same steps, visits and memo keys
    /// (a fresh walk could only cut more through memos, whose results are equal). Only an untainted prefix can
    /// park: a recorded-only outcome loses to a subsequently published outcome on a fresh retry, so a prefix
    /// that read one must be walked again, even though both attempts belong to the same resolution.</para>
    /// </summary>
    private sealed class AliasChaseMachine
    {
        private readonly List<ChaseFrame> _frames = [];
        private HashSet<AliasChaseVisit>? _structure;
        private List<AliasChaseVisit>? _undo;

        // Monotone counters: a route decision is clean when no taint and only published projections occurred
        // between its start and its end; a reused decision that read projections counts as a projection read.
        private int _taints;
        private int _projections;

        // The root chase (null for a static path selected outside a chase, which never parks) and its arguments.
        private ChaseFrame? _root;
        private Algorithm.Alias? _rootAlias;
        private AliasChase _rootChase;
        private Property? _rootBinding;

        // The observation attempt that parked this machine, or null while it runs.
        private NeedCell.ObservationScope? _parkedIn;

        private HashSet<AliasChaseVisit> Structure => _structure ??= [];

        private List<AliasChaseVisit> Undo => _undo ??= [];

        /// <summary>The chase of <paramref name="alias"/> read by <paramref name="chase"/>, from the binding <paramref name="binding"/>'s memo.</summary>
        internal EvalResult<AliasChaseEnd> Chase(Algorithm.Alias alias, EvalCtx ctx, AliasChase chase, Property? binding)
        {
            var visited = FollowsCarriers(chase) ? new HashSet<AliasChaseVisit>() : Structure;
            var root = new ChaseFrame(ctx, chase, alias, binding, visited, undoMark: -1);
            _root = root;
            _rootAlias = alias;
            _rootChase = chase;
            _rootBinding = binding;
            _frames.Add(root);
            Run();
            return root.End;
        }

        /// <summary>
        /// Resumes this machine, parked by an earlier attempt of the same asynchronous resolution, when the retry
        /// reaches the same root chase: the parked frame repeats its runtime projection, which now reads the
        /// outcome the resolution recorded, and the chase continues from there. The same root chase is the same
        /// reading of the same alias BINDING (<see cref="AliasChaseVisit"/>: declaration, declaring scope identity
        /// and activation — a retry's lookup wires the alias afresh) from the same memo binding under the same
        /// context.
        /// </summary>
        internal bool TryResume(
            Algorithm.Alias alias, EvalCtx ctx, AliasChase chase, Property? binding, NeedCell.ObservationScope observation,
            out EvalResult<AliasChaseEnd> end)
        {
            end = default;
            if (_parkedIn is null || ReferenceEquals(_parkedIn, observation)
                || chase != _rootChase || !ReferenceEquals(binding, _rootBinding)
                || !ReferenceEquals(alias.Declaration, _rootAlias!.Declaration) || alias.Declaration is null
                || AliasChaseVisit.Of(alias) != AliasChaseVisit.Of(_rootAlias) || !ctx.Equals(_root!.Ctx))
                return false;
            observation.Record!.ParkedChase = null;
            _parkedIn = null;
            ctx.Budget.NoteAliasChaseVisit();
            Run();
            end = _root.End;
            return true;
        }

        /// <summary>
        /// The member steps of the static path <paramref name="path"/> from the scope <paramref name="owner"/>
        /// (<see cref="Evaluator.ResolveStaticPath"/>), outside any chase: its receivers' structure computations
        /// start from an empty structure context.
        /// </summary>
        internal EvalResult<Algorithm> SelectStaticPath(Algorithm owner, Expr.DotCall path, EvalCtx stepCtx, out PropertyCallBinding? hop)
        {
            var root = new ChaseFrame(stepCtx, AliasChase.StaticStructure, owner, binding: null, visited: null, undoMark: -1);
            if (BeginPath(root, owner, path, stepCtx))
            {
                _frames.Add(root);
                Run();
            }
            hop = root.Hop;
            return root.Selected;
        }

        // Runs the frame stack to completion: a frame either pushes the nested chase it needs (and is resumed with
        // its end) or finishes, unwinding the visits it added to the structure context. A parked machine stops
        // with its stack intact; the root's end is then the pending marker its attempt discards.
        private void Run()
        {
            EvalResult<AliasChaseEnd>? nested = null;
            while (true)
            {
                var frame = _frames[^1];
                if (Advance(frame, nested) is { } child)
                {
                    _frames.Add(child);
                    nested = null;
                    continue;
                }

                if (_parkedIn is not null)
                    return;
                _frames.RemoveAt(_frames.Count - 1);
                if (_frames.Count == 0)
                    return;
                Unwind(frame);
                nested = frame.End;
            }
        }

        // Resumes the frame's suspended navigation with the nested chase's end, then continues its chase loop;
        // returns the next nested chase to run, or null once the frame has finished.
        private ChaseFrame? Advance(ChaseFrame frame, EvalResult<AliasChaseEnd>? nested)
        {
            ChaseFrame? child = null;
            var next = ChaseAdvance.Continue;
            switch (frame.Navigation)
            {
                case StepNavigation.Path:
                    if ((child = NavigatePath(frame, nested)) is not null)
                        return child;
                    if (frame.Visited is null)
                        return null; // a path selected outside any chase: the selection is the result
                    next = AfterPath(frame);
                    break;

                case StepNavigation.Route:
                    if ((child = NavigateRoute(frame, nested)) is not null)
                        return child;
                    next = TakeStep(frame, frame.Step!, frame.RouteIsRuntime, out child);
                    break;

                case StepNavigation.Projection:
                    // A parked frame, resumed by its resolution's retry: repeat the runtime projection.
                    next = TakeStep(frame, frame.Step!, runtime: true, out child);
                    break;
            }

            while (next == ChaseAdvance.Continue)
                next = AdvanceStep(frame, out child);
            return next == ChaseAdvance.Suspend ? child : null;
        }

        /// <summary>
        /// One iteration of the chase loop from its top: the end (a non-alias, or a carrier for a chase that stops
        /// there), a remembered static end, the visit, then the step's kind — a RUNTIME step when its target is a
        /// runtime row (<see cref="AliasTargetRows.IsRuntimeRow"/>) and, for an <c>.Algorithm</c> link whose
        /// receiver is not a parameter, the edge takes the intrinsic route in the alias's own scope, decided
        /// member-first exactly as the dot route decides it (<see cref="NavigateRoute"/>); a receiver that declares
        /// a member <c>Algorithm</c> is an ordinary static step, and a parameter-headed row is runtime without
        /// navigating. The receiver's structure is read within the asking chase's structure context: a receiver
        /// leading back into a structure computation in progress (<c>A = A.Algorithm</c>; <c>A = B.Algorithm</c>
        /// with <c>B = A</c>) is a cycle inside the decision — a route failure, hence a runtime step, whose
        /// projection then re-enters its own flight (<see cref="EvalError.DemandCycle"/>, NEED-09) — never an
        /// unbounded re-entry of the decision. Lean: <c>resolveAliasChase</c>, <c>aliasStepIsRuntime</c>.
        /// </summary>
        private ChaseAdvance AdvanceStep(ChaseFrame frame, out ChaseFrame? child)
        {
            child = null;
            // STRUCTURE and the static structure stop at a structural carrier: its own identity.
            if (frame.Current is not Algorithm.Alias step || (!frame.Follow && !step.IsReference))
            {
                PublishAliasTargetMemo(ref frame.Pending, new AliasStaticEnd(frame.Current, frame.Last));
                return Finish(frame, EvalResult<AliasChaseEnd>.Ok(new AliasChaseEnd(AliasChaseEndKind.Identity, frame.Current, frame.Last)));
            }

            // A binding's memoized static end; a miss queues the binding for this chase's end.
            if (!frame.Projected && frame.MemoBinding is { } memoBinding)
            {
                frame.MemoBinding = null;
                var known = ReadAliasTargetMemo(memoBinding, step, frame.Ctx, frame.Follow, ref frame.Pending);
                if (known is { } end && !ReferenceEquals(end.End, step))
                {
                    frame.Current = end.End;
                    frame.Last = end.Last ?? frame.Last;
                    return ChaseAdvance.Continue;
                }
            }

            if (!Visit(frame, AliasChaseVisit.Of(step)))
                return Finish(frame, AliasCycleError(step));

            if (!AliasTargetRows.IsRuntimeRow(step.Target))
                return TakeStep(frame, step, runtime: false, out child);
            if (step.Target is not Expr.DotCall edge || HasParameterHead(edge))
                return TakeStep(frame, step, runtime: true, out child);
            if (SettledRoute(step, frame.Ctx) is { } settled)
                return TakeStep(frame, step, settled, out child);
            BeginRoute(frame, step, edge);
            if ((child = NavigateRoute(frame, nested: null)) is not null)
                return ChaseAdvance.Suspend;
            return TakeStep(frame, step, frame.RouteIsRuntime, out child);
        }

        /// <summary>
        /// The step <paramref name="step"/> once its kind is known. A RUNTIME step publishes the static end, then
        /// ends a non-projecting chase at the alias or projects its ONE binding cell. A STATIC step (Lean
        /// <c>resolveAliasStepWith</c>) is the binding the written target selects in the alias's OWN scope — the
        /// alias pushed as the head: a name by the ownership-first lexical lookup, RAW; a member path by
        /// structural navigation of DECLARED members (<see cref="NavigatePath"/>), whose final hop is the terminal
        /// binding a bare read and a publication origin of the chain use.
        /// </summary>
        private ChaseAdvance TakeStep(ChaseFrame frame, Algorithm.Alias step, bool runtime, out ChaseFrame? child)
        {
            child = null;
            frame.Navigation = StepNavigation.None;
            if (runtime)
            {
                PublishAliasTargetMemo(ref frame.Pending, new AliasStaticEnd(step, frame.Last));
                if (!frame.Project)
                    return Finish(frame, EvalResult<AliasChaseEnd>.Ok(new AliasChaseEnd(AliasChaseEndKind.Runtime, step, frame.Last)));
                _projections++;
                var cell = AliasBindingCell(step, frame.Ctx);
                var projection = cell.ProjectCallable();
                // An unpublished outcome (a recorded-only result, a flow-local DemandCycle, a pending observation
                // or terminal answer) settles no route decision; the cell's published outcome — a failure included — is
                // the sticky fact every later navigation reads.
                var published = cell.IsPublishedCallable(projection);
                if (projection.IsError)
                {
                    if (Park(frame, step, projection.Error))
                        return ChaseAdvance.Finish;
                    if (published)
                    {
                        frame.End = projection.Error;
                        return ChaseAdvance.Finish;
                    }
                    return Finish(frame, projection.Error);
                }
                if (!published)
                    _taints++;
                if (projection.Value is not { } identity)
                    return Finish(frame, EvalResult<AliasChaseEnd>.Ok(new AliasChaseEnd(AliasChaseEndKind.ValueView, step, null)));
                frame.Projected = true;
                frame.Current = identity;
                frame.Last = null;
                return ChaseAdvance.Continue;
            }

            var stepCtx = frame.Ctx.Push(step);
            switch (step.Target)
            {
                case Expr.Resolve(var name):
                {
                    var resolved = LookupLexicalRaw(step, name, stepCtx);
                    if (resolved.IsError)
                        return Finish(frame, AtSpanIfMissing(resolved.Error, step.Target.Span));
                    var hop = new PropertyCallBinding(resolved.Value.Owner, resolved.Value.Binding);
                    frame.Current = resolved.Value.ResolvedAlgorithm;
                    frame.Last = hop;
                    frame.MemoBinding = hop.Binding;
                    return ChaseAdvance.Continue;
                }

                case Expr.DotCall { Args: null } path:
                    if (BeginPath(frame, step, path, stepCtx) && (child = NavigatePath(frame, nested: null)) is not null)
                        return ChaseAdvance.Suspend;
                    return AfterPath(frame);

                default:
                    return Finish(frame, NotAStaticAliasTarget(step.Target));
            }
        }

        // The selected member becomes the chase's current step; its binding is the hop and the next memo key.
        private ChaseAdvance AfterPath(ChaseFrame frame)
        {
            frame.Navigation = StepNavigation.None;
            if (frame.Selected.IsError)
                return Finish(frame, frame.Selected.Error);
            frame.Current = frame.Selected.Value;
            frame.Last = frame.Hop;
            frame.MemoBinding = frame.Hop?.Binding;
            return ChaseAdvance.Continue;
        }

        /// <summary>
        /// Starts the static path <paramref name="path"/> from the scope <paramref name="owner"/> under
        /// <paramref name="stepCtx"/> (Lean <c>staticPathSelectWith</c> over <c>Expr.staticAliasPath?</c>): its
        /// name or block head; any other head is no static alias target. False when the head already failed.
        /// </summary>
        private static bool BeginPath(ChaseFrame frame, Algorithm owner, Expr.DotCall path, EvalCtx stepCtx)
        {
            frame.Navigation = StepNavigation.Path;
            frame.StepCtx = stepCtx;
            frame.Written = path;
            frame.Hop = null;
            frame.ValueBinding = null;
            frame.Index = 0;
            var head = CollectEdges(frame, path);
            switch (head)
            {
                case Expr.Resolve(var name):
                {
                    var resolved = LookupLexicalRaw(owner, name, stepCtx);
                    if (resolved.IsError)
                    {
                        frame.Selected = AtSpanIfMissing(resolved.Error, head.Span ?? path.Span);
                        return false;
                    }

                    frame.Value = resolved.Value.ResolvedAlgorithm;
                    frame.Hop = new PropertyCallBinding(resolved.Value.Owner, resolved.Value.Binding);
                    frame.ValueBinding = resolved.Value.Binding;
                    return true;
                }

                case Expr.AlgorithmExpr(var block):
                    frame.Value = WireToCaller(stepCtx, block);
                    return true;

                default:
                    frame.Selected = NotAStaticAliasTarget(path);
                    return false;
            }
        }

        /// <summary>
        /// The member steps of a static path (Lean <c>aliasStepNavigateWith</c>): each DECLARED member of the
        /// previous receiver read through its STATIC structure (a transparent reference is its target's, a carrier
        /// its own, a runtime reference has none — nothing is projected), wired to it and checked for
        /// accessibility from the site; a member declared only in branches is the local-only error, and a missing
        /// member or a receiver without static structure has no callable: the path is not a static alias target.
        /// An ALIAS receiver is a nested static-structure chase under the binding that selected it — the head's
        /// binding, or the previous edge's member — so its static end is read from, and published to, that
        /// binding's memo. Returns that nested chase, or null once the selection is made.
        /// </summary>
        private ChaseFrame? NavigatePath(ChaseFrame frame, EvalResult<AliasChaseEnd>? nested)
        {
            var edges = frame.Edges;
            var stepCtx = frame.StepCtx;
            while (frame.Index < edges.Count)
            {
                var edge = edges[frame.Index];
                EvalResult<AliasChaseEnd> structure;
                if (frame.Value is Algorithm.Alias receiverAlias)
                {
                    if (nested is not { } receiverEnd)
                        return Nest(receiverAlias, stepCtx, AliasChase.StaticStructure, frame.ValueBinding);
                    structure = receiverEnd;
                    nested = null;
                }
                else
                    structure = EvalResult<AliasChaseEnd>.Ok(new AliasChaseEnd(AliasChaseEndKind.Identity, frame.Value!, null));

                if (structure.IsError)
                    return Select(frame, structure.Error);
                if (structure.Value.Kind != AliasChaseEndKind.Identity)
                    return Select(frame, NotAStaticAliasTarget(frame.Written!));

                var receiver = structure.Value.Algorithm;
                var member = LookupPropBinding(receiver, edge.Name, stepCtx.Budget);
                if (member is null)
                {
                    return Select(frame, receiver.DefinesConditionalBranchProperty(edge.Name)
                        ? new EvalError.LocalOnlyProperty(OpenExprName(edge.Target), edge.Name, PropertyExposure.LocalOnlyConditionalAlgorithm)
                        { Span = edge.Span }
                        : NotAStaticAliasTarget(frame.Written!));
                }

                if (!IsAccessibleFrom(member, receiver, stepCtx))
                    return Select(frame, LocalOnlyPropertyError(OpenExprName(edge.Target), member) with { Span = edge.Span });

                frame.Value = ChildOfInContext(receiver, member.Value, stepCtx);
                frame.Hop = new PropertyCallBinding(receiver, member);
                frame.ValueBinding = member;
                frame.Index++;
            }

            return Select(frame, EvalResult<Algorithm>.Ok(frame.Value!));
        }

        // Starts the route decision of the `.Algorithm` link `step` in the alias's own scope.
        private void BeginRoute(ChaseFrame frame, Algorithm.Alias step, Expr.DotCall edge)
        {
            frame.Ctx.Budget.NoteAliasChaseVisit();
            frame.Navigation = StepNavigation.Route;
            frame.Step = step;
            frame.Written = edge;
            frame.StepCtx = frame.Ctx.Push(step);
            frame.Head = CollectEdges(frame, edge.Target);
            frame.Index = -1;
            frame.RouteTaints = _taints;
            frame.RouteProjections = _projections;
        }

        /// <summary>
        /// The settled route decision of <paramref name="step"/>, if a clean navigation recorded one (see the
        /// machine's remarks): whether the step is RUNTIME. A decision that read runtime projections observes the
        /// run's continuation first, exactly as its first projection would — cancellation throws, and a terminal
        /// run is a navigation failure, which makes the step runtime (whose own projection then reports it).
        /// </summary>
        private bool? SettledRoute(Algorithm.Alias step, EvalCtx ctx)
        {
            if (step.Declaration is null)
                return null;
            var memo = AliasMemoOwner(step) is { } activation ? activation.AliasRouteDecisions : ctx.Budget.AliasRouteDecisions;
            AliasRouteDecision settled;
            lock (memo)
                if (!memo.TryGetValue(new AliasTargetKey(step.Declaration, StructuralOwnerIdentity.FromScope(step.Parent)), out settled))
                    return null;
            ctx.Budget.NoteAliasChaseVisit();
            if (!settled.ReadProjections)
                return settled.IsRuntime;
            _projections++;
            if (ctx.Budget.CheckContinuation() is not null)
            {
                _taints++;
                return true;
            }
            return settled.IsRuntime;
        }

        // Records a clean route decision (first wins; any clean navigation computes the same decision).
        private void SettleRoute(ChaseFrame frame, bool isRuntime)
        {
            var step = frame.Step!;
            if (frame.RouteTaints != _taints || step.Declaration is null)
                return;
            var memo = AliasMemoOwner(step) is { } activation ? activation.AliasRouteDecisions : frame.Ctx.Budget.AliasRouteDecisions;
            var decision = new AliasRouteDecision(isRuntime, ReadProjections: frame.RouteProjections != _projections);
            lock (memo)
                memo.TryAdd(new AliasTargetKey(step.Declaration, StructuralOwnerIdentity.FromScope(step.Parent)), decision);
        }

        /// <summary>
        /// Parks this machine when <paramref name="error"/> is the pending marker of the asynchronous resolution
        /// observing it (<see cref="ResolveAsync{TState,T}"/>) and its prefix is untainted: the frame will repeat the projection of
        /// <paramref name="step"/> when the resolution's retry resumes the same root chase. The root's end is the
        /// marker, which the attempt discards. False outside a resolution's observation or for any other failure.
        /// </summary>
        private bool Park(ChaseFrame frame, Algorithm.Alias step, EvalError error)
        {
            if (_taints != 0 || _root is null
                || NeedCell.CurrentObservation is not { Record: { } record, Pending: not null } observation
                || !NeedCell.IsObservationPending(error))
                return false;
            frame.Navigation = StepNavigation.Projection;
            frame.Step = step;
            _parkedIn = observation;
            _root.End = error;
            record.ParkedChase = this;
            return true;
        }

        /// <summary>
        /// THE ROUTE DECISION of an <c>.Algorithm</c> link (Lean <c>aliasRouteIsIntrinsicWith</c>), its receiver
        /// navigated exactly as <see cref="ResolveDotReceiver"/> navigates it — MIRROR OF that navigation, its head
        /// (<see cref="ResolveReceiverHead"/>, <see cref="ReceiverStructure"/>) and its alias members
        /// (<see cref="NavigatedAliasMemberStructure"/>), keep in lock-step — except that an ALIAS head or member is
        /// read through its STRUCTURE by a nested chase in this chase's structure context instead of a host frame.
        /// Then the ONE dot-edge decision (<see cref="IsAlgorithmIntrinsicRoute"/>): the intrinsic exactly on a
        /// structural miss; a receiver navigation failure is the route's error, which makes the step RUNTIME.
        /// Returns the nested chase to run, or null once <see cref="ChaseFrame.RouteIsRuntime"/> is decided.
        /// </summary>
        private ChaseFrame? NavigateRoute(ChaseFrame frame, EvalResult<AliasChaseEnd>? nested)
        {
            var ctx = frame.StepCtx;
            if (frame.Index < 0)
            {
                var head = frame.Head!;
                if (nested is { } headEnd)
                {
                    frame.Selected = ReceiverStructureOf(headEnd, head);
                    nested = null;
                }
                else
                {
                    switch (head)
                    {
                        case Expr.Resolve(var name):
                        {
                            if (ctx.CallStack.Count == 0)
                            {
                                frame.Selected = new EvalError.UnknownName(name) { Span = head.Span };
                                break;
                            }

                            var resolved = ProjectRawLookup(LookupLexicalRaw(ctx.CallStack[0], name, ctx), head.Span);
                            if (resolved.IsOk && resolved.Value is Algorithm.Alias headAlias)
                                return Nest(headAlias, ctx, AliasChase.Structure, binding: null);
                            if (resolved.IsError)
                                _taints++; // a failed lookup is never settled
                            frame.Selected = resolved;
                            break;
                        }

                        case Expr.AlgorithmExpr(var block):
                        {
                            var wired = WireToCaller(ctx, block);
                            if (wired is Algorithm.Alias blockAlias)
                                return Nest(blockAlias, ctx, AliasChase.Structure, binding: null);
                            frame.Selected = EvalResult<Algorithm>.Ok(wired);
                            break;
                        }

                        default:
                            _taints++;
                            frame.Selected = ResolveAlg(head, ctx);
                            break;
                    }
                }

                frame.Index = 0;
            }

            var edges = frame.Edges;
            while (frame.Index < edges.Count)
            {
                var edge = edges[frame.Index];
                if (nested is { } memberEnd)
                {
                    // An alias member read through its STRUCTURE: a value-only runtime reference has none, so the
                    // edge is an ordinary dot result.
                    frame.Selected = memberEnd.IsError
                        ? AtSpanIfMissing(memberEnd.Error, edge.Span)
                        : memberEnd.Value.Kind == AliasChaseEndKind.Identity
                            ? EvalResult<Algorithm>.Ok(memberEnd.Value.Algorithm)
                            : Fallback(edge, ctx);
                    nested = null;
                }
                else if (frame.Selected.IsError)
                {
                    // A receiver that is simply not an algorithm makes the edge an ordinary dot result; any other
                    // navigation failure is the path's.
                    if (IsAbsentIdentity(frame.Selected.Error))
                        frame.Selected = Fallback(edge, ctx);
                }
                else
                {
                    var receiver = frame.Selected.Value;
                    var member = LookupPropBinding(receiver, edge.Name, ctx.Budget);
                    if (member is not null)
                    {
                        if (!IsExported(member))
                            _taints++; // accessibility read from the site's activation: never settled
                        if (!IsAccessibleFrom(member, receiver, ctx))
                            frame.Selected = LocalOnlyPropertyError(OpenExprName(edge.Target), member) with { Span = edge.Span };
                        else
                        {
                            var wired = ChildOfInContext(receiver, member.Value, ctx);
                            if (wired is Algorithm.Alias memberAlias)
                                return Nest(memberAlias, ctx, AliasChase.Structure, binding: null);
                            frame.Selected = EvalResult<Algorithm>.Ok(wired);
                        }
                    }
                    else if (receiver.DefinesConditionalBranchProperty(edge.Name))
                    {
                        frame.Selected = new EvalError.LocalOnlyProperty(OpenExprName(edge.Target), edge.Name, PropertyExposure.LocalOnlyConditionalAlgorithm)
                        { Span = edge.Span };
                    }
                    else
                        frame.Selected = Fallback(edge, ctx);
                }

                frame.Index++;
            }

            var navigated = frame.Selected;
            // The receiver's own `Algorithm` member, if any, is selected with an accessibility check from the site.
            if (navigated.IsOk && LookupPropBinding(navigated.Value, frame.Written!.Name, ctx.Budget) is { } declared && !IsExported(declared))
                _taints++;
            frame.RouteIsRuntime = (navigated.IsError && !IsAbsentIdentity(navigated.Error))
                || IsAlgorithmIntrinsicEdge(frame.Written!, navigated.IsError ? null : navigated.Value, ctx);
            SettleRoute(frame, frame.RouteIsRuntime);
            return null;
        }

        // An edge that is an ordinary dot result: identity resolution that may read beyond the alias's scope, so
        // the route decision that took it is never settled.
        private EvalResult<Algorithm> Fallback(Expr.DotCall edge, EvalCtx ctx)
        {
            _taints++;
            return ResolveAlg(edge, ctx);
        }

        // A receiver head's STRUCTURE (ReceiverStructure over a structure chase's end): a value-only runtime
        // reference has none — an absent identity.
        private static EvalResult<Algorithm> ReceiverStructureOf(EvalResult<AliasChaseEnd> structure, Expr written)
        {
            if (structure.IsError)
                return AtSpanIfMissing(structure.Error, written.Span);
            return structure.Value.Kind == AliasChaseEndKind.Identity
                ? EvalResult<Algorithm>.Ok(structure.Value.Algorithm)
                : new EvalError.NotAnAlgorithm(ExprKind(written)) { Span = written.Span };
        }

        // The argumentless member edges of a written path, outermost last, into the frame; returns the head.
        private static Expr CollectEdges(ChaseFrame frame, Expr target)
        {
            var edges = frame.Edges;
            edges.Clear();
            while (target is Expr.DotCall { Args: null } edge)
            {
                edges.Add(edge);
                target = edge.Target;
            }

            edges.Reverse();
            return target;
        }

        // A nested structure chase in the shared structure context, undone from the current log length.
        private ChaseFrame Nest(Algorithm.Alias alias, EvalCtx ctx, AliasChase chase, Property? binding)
            => new(ctx, chase, alias, binding, Structure, Undo.Count);

        private bool Visit(ChaseFrame frame, AliasChaseVisit visit)
        {
            if (!frame.Visited!.Add(visit))
                return false;
            frame.Ctx.Budget.NoteAliasChaseVisit();
            if (frame.UndoMark >= 0)
                Undo.Add(visit);
            return true;
        }

        // A finished nested chase's visits leave the structure context: its siblings never see them.
        private void Unwind(ChaseFrame frame)
        {
            if (frame.UndoMark < 0 || _undo is not { } undo)
                return;
            for (var index = undo.Count - 1; index >= frame.UndoMark; index--)
                _structure!.Remove(undo[index]);
            undo.RemoveRange(frame.UndoMark, undo.Count - frame.UndoMark);
        }

        private static ChaseFrame? Select(ChaseFrame frame, EvalResult<Algorithm> selected)
        {
            frame.Selected = selected;
            return null;
        }

        // A failed chase (a cycle, a lookup or projection failure) leaves every route decision it is nested in
        // unsettled.
        private ChaseAdvance Finish(ChaseFrame frame, EvalResult<AliasChaseEnd> end)
        {
            if (end.IsError)
                _taints++;
            frame.End = end;
            return ChaseAdvance.Finish;
        }
    }

    /// <summary>What a frame does next: continue its chase loop, wait for a nested chase, or end.</summary>
    private enum ChaseAdvance : byte
    {
        Continue,
        Suspend,
        Finish,
    }

    /// <summary>The navigation a chase frame has in progress for its current step.</summary>
    private enum StepNavigation : byte
    {
        None,

        /// <summary>A static member path (<see cref="AliasChaseMachine.NavigatePath"/>).</summary>
        Path,

        /// <summary>An <c>.Algorithm</c> link's route decision (<see cref="AliasChaseMachine.NavigateRoute"/>).</summary>
        Route,

        /// <summary>A runtime step's projection, reported pending by an asynchronous resolution's observation (a parked frame).</summary>
        Projection,
    }

    /// <summary>
    /// A SETTLED <c>.Algorithm</c> route decision of a runtime-row alias (C# implementation-only; see
    /// <see cref="AliasChaseMachine"/>): whether the step is RUNTIME (the intrinsic route, or a navigation
    /// failure), and whether its navigation read runtime projections, so a reuse observes the run's continuation
    /// first as that navigation's first projection did.
    /// </summary>
    internal readonly record struct AliasRouteDecision(bool IsRuntime, bool ReadProjections);

    /// <summary>
    /// One chase on the machine's stack: the chase loop's state (kind, current step, memo binding, last static
    /// hop, pending memo keys, whether a runtime step was projected, its visited set and undo mark) and the
    /// navigation it has suspended for its current step — a static path's owner context, edges, index, value
    /// and hop, or a route decision's receiver so far.
    /// </summary>
    private sealed class ChaseFrame(EvalCtx ctx, AliasChase chase, Algorithm current, Property? binding, HashSet<AliasChaseVisit>? visited, int undoMark)
    {
        internal readonly EvalCtx Ctx = ctx;
        internal readonly bool Follow = FollowsCarriers(chase);
        internal readonly bool Project = ProjectsRuntimeSteps(chase);

        /// <summary>Where this chase's own steps go: the machine's structure context, a root invocation or VALUE chase's own set, or none for a path selected outside a chase.</summary>
        internal readonly HashSet<AliasChaseVisit>? Visited = visited;

        /// <summary>The structure undo log's length when this nested chase started; -1 for a root.</summary>
        internal readonly int UndoMark = undoMark;

        internal Algorithm Current = current;
        internal Property? MemoBinding = binding;
        internal PropertyCallBinding? Last;
        internal List<(Dictionary<AliasTargetKey, AliasStaticEnd> Memo, AliasTargetKey Key)>? Pending;
        internal bool Projected;
        internal EvalResult<AliasChaseEnd> End;

        // ── The suspended navigation of the current step ──
        internal StepNavigation Navigation;
        internal Algorithm.Alias? Step;
        internal EvalCtx StepCtx;
        internal Expr.DotCall? Written;
        internal Expr? Head;
        private List<Expr.DotCall>? _edges;
        internal int Index;
        internal Algorithm? Value;
        internal Property? ValueBinding;
        internal PropertyCallBinding? Hop;

        /// <summary>A path's selection, or a route decision's receiver so far.</summary>
        internal EvalResult<Algorithm> Selected;

        internal bool RouteIsRuntime;

        /// <summary>The machine's taint and projection counters when this frame's route decision started.</summary>
        internal int RouteTaints;
        internal int RouteProjections;

        /// <summary>The argumentless member edges of the path being navigated, innermost first.</summary>
        internal List<Expr.DotCall> Edges => _edges ??= [];
    }

    // The remembered static end of an alias binding, without queueing a miss.
    private static AliasStaticEnd? PeekAliasTargetMemo(Property binding, Algorithm.Alias wired, EvalCtx ctx, bool followCarriers)
    {
        var memo = AliasMemoOwner(wired) is { } activation ? activation.AliasTargets : ctx.Budget.AliasTargets;
        return memo.TryGetValue(new AliasTargetKey(binding, StructuralOwnerIdentity.FromScope(wired.Parent), followCarriers), out var end)
            ? end
            : null;
    }

    /// <summary>
    /// THE INVOCATION CHASE (M4★; Lean <c>resolveAliasTarget</c>): the algorithm an explicit call through
    /// <paramref name="alias"/> invokes — references and carriers alike are followed, at any arity; a
    /// value-only runtime target is its VALUE VIEW (<see cref="TerminalAliasProperty"/>), never the alias
    /// again. <paramref name="binding"/> is the alias's binding, whose memo the chase reads.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<Algorithm> ResolveAliasTarget(Algorithm.Alias alias, EvalCtx ctx, Property? binding = null)
    {
        var end = ChaseAlias(alias, ctx, AliasChase.Invocation, binding);
        if (end.IsError)
            return end.Error;
        return end.Value.Kind == AliasChaseEndKind.Identity
            ? EvalResult<Algorithm>.Ok(end.Value.Algorithm)
            : EvalResult<Algorithm>.Ok(TerminalAliasProperty((Algorithm.Alias)end.Value.Algorithm));
    }

    /// <summary>
    /// THE STRUCTURE CHASE (M4★; Lean <c>resolveAliasStructure</c>): the full algorithm
    /// <paramref name="alias"/> denotes — a transparent reference's target with its own context and
    /// members, a structural carrier itself, never its forwarding target — or <c>null</c> for a value-only
    /// runtime reference, which has no structure.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<Algorithm?> ResolveAliasStructure(
        Algorithm.Alias alias, EvalCtx ctx, Property? binding = null)
    {
        var end = ChaseAlias(alias, ctx, AliasChase.Structure, binding);
        if (end.IsError)
            return end.Error;
        return end.Value.Kind == AliasChaseEndKind.Identity
            ? EvalResult<Algorithm?>.Ok(end.Value.Algorithm)
            : EvalResult<Algorithm?>.Ok(null);
    }

    /// <summary>
    /// THE VALUE CHASE (OD-E, M4★; Lean <c>resolveAliasValueTarget</c>): where a bare read of
    /// <paramref name="alias"/> goes — the TERMINAL binding of its static chain, under that binding's own
    /// key, owner and activation, or the first runtime-target alias, whose bare read is its binding
    /// cell's VALUE. Static identity navigation: a VALUE read never initiates a CALLABLE projection.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<AliasTerminal> ResolveAliasValueTerminal(Algorithm.Alias alias, EvalCtx ctx, Property? binding = null)
    {
        var end = ChaseAlias(alias, ctx, AliasChase.Value, binding);
        if (end.IsError)
            return end.Error;
        // A read that CROSSES a structural carrier is the subordinate computation of the carrier's
        // written row (Q-36 with M4★): the reference-only static chase — a prefix of the VALUE chase,
        // projecting no runtime step of its own — stops exactly at the first carrier. Lean: the `nested`
        // field of `resolveAliasValueTarget`'s terminal.
        var reference = ChaseAlias(alias, ctx, AliasChase.StaticStructure, binding);
        var crossesCarrier = reference.IsOk
            && reference.Value.Kind == AliasChaseEndKind.Identity
            && reference.Value.Algorithm is Algorithm.Alias { IsReference: false };
        return end.Value.Kind == AliasChaseEndKind.Identity
            ? EvalResult<AliasTerminal>.Ok(new AliasTerminal(end.Value.Algorithm, end.Value.Last, IsRuntime: false, crossesCarrier))
            : EvalResult<AliasTerminal>.Ok(new AliasTerminal(end.Value.Algorithm, null, IsRuntime: true, crossesCarrier));
    }

    /// <summary>
    /// Whether the STATIC structure chase of <paramref name="alias"/> — references followed, a carrier the
    /// end, nothing projected — reaches a runtime-target alias: the static identity work a supplied
    /// reference's projection takes first (Lean <c>projectNeedWritten</c>'s <c>throughAlias</c>). It
    /// walks references statically and stops at a carrier, so it never resolves a carrier's target. A
    /// static resolution failure is no reach.
    /// </summary>
    private static bool StructureReachesRuntimeAlias(Algorithm.Alias alias, EvalCtx ctx, Property? binding)
    {
        var end = ChaseAlias(alias, ctx, AliasChase.StaticStructure, binding);
        return end.IsOk && end.Value.Kind == AliasChaseEndKind.Runtime;
    }

    // Records the static end of a chase under every binding it passed (a no-op once published).
    private static void PublishAliasTargetMemo(ref List<(Dictionary<AliasTargetKey, AliasStaticEnd> Memo, AliasTargetKey Key)>? pending, AliasStaticEnd staticEnd)
    {
        if (pending is null)
            return;
        foreach (var (memo, key) in pending)
            memo[key] = staticEnd;
        pending = null;
    }

    /// <summary>
    /// THE BINDING CELL of the runtime-target alias <paramref name="wired"/> (FWD-02, META-S3-2; L-RUN, M4★):
    /// its target row supplied in the alias's OWN declaring context — the alias entered as the head,
    /// exactly where its body is evaluated — through the ONE supply-cell constructor
    /// (<see cref="SupplyCell"/>). A parameter row IS that parameter's own cell (NEED-01 transport,
    /// nothing allocated); an <c>.Algorithm</c> row is a link with its one receiver (CR-15); a
    /// parameter-rooted path is a runtime-projection reference cell. Every other row is established ONCE
    /// per declaration and declaring scope on the nearest activation of the declaring chain (or run-wide),
    /// first-wins, and retained (retry-stable, Guard B); establishing it evaluates nothing. Its VALUE is
    /// the alias's bare read and its value view's zero-supply invocation (<see cref="ValueViewCell"/>), its
    /// CALLABLE the alias's runtime identity — so every observation shares its receiver work and the
    /// supplied computation never reruns. Lean: <c>aliasBindingCell</c>.
    /// </summary>
    internal static NeedCell AliasBindingCell(Algorithm.Alias wired, EvalCtx ctx)
    {
        if (wired.Target is Expr.Param)
            return SupplyCell(wired.Target, ctx.Push(wired), [], retained: true);

        var memo = AliasMemoOwner(wired) is { } activation ? activation.AliasBindingCells : ctx.Budget.AliasBindingCells;
        var key = new AliasTargetKey(wired.Declaration!, StructuralOwnerIdentity.FromScope(wired.Parent));
        lock (memo)
            if (memo.TryGetValue(key, out var known)) return known;
        var created = SupplyCell(wired.Target, EnterAlgorithmBody(wired, ctx, []), [], retained: true);
        lock (memo)
        {
            if (memo.TryGetValue(key, out var raced)) return raced;
            memo.Add(key, created);
            return created;
        }
    }

    /// <summary>
    /// THE VALUE VIEW'S CELL (L-RUN, M4★; Lean <c>valueViewCell?</c>): the recorded binding cell of the
    /// runtime-target alias whose value view <paramref name="algorithm"/> is (<see cref="TerminalAliasProperty"/>
    /// keeps the alias's declaration and scope, so the binding-cell key finds it), read AFTER the ordinary
    /// binder's cardinality gate — a zero-supply invocation of a value-only reference returns that cell's
    /// VALUE every time, so the supplied computation never reruns. Every other algorithm has no recorded
    /// cell. A parameter row records none: its view reads the parameter, whose own cell it is. Reads only.
    /// </summary>
    private static NeedCell? ValueViewCell(Algorithm algorithm, EvalCtx ctx)
    {
        if (!ctx.Budget.MayReachRuntimeAliases || algorithm is not Algorithm.User { ParameterPatterns.Count: 0, Output.Count: 1 })
            return null;
        var memo = AliasMemoOwner(algorithm) is { } activation ? activation.AliasBindingCells : ctx.Budget.AliasBindingCells;
        var key = new AliasTargetKey(algorithm.Declaration!, StructuralOwnerIdentity.FromScope(algorithm.Parent));
        lock (memo)
            return memo.TryGetValue(key, out var cell) ? cell : null;
    }

    /// <summary>The value view of a value-only runtime reference: the alias's ordinary zero-parameter body, never the alias again (Lean <c>Algorithm.aliasPropertyView</c>).</summary>
    private static Algorithm.User TerminalAliasProperty(Algorithm.Alias alias) => new(alias);

    // The nearest activation of an alias's declaring chain, which owns its memo entries.
    private static ParameterActivation? AliasMemoOwner(Algorithm wired)
    {
        for (var level = wired.Parent; level is not null; level = level.Parent)
        {
            if (level.Activation is { } activation)
                return activation;
        }
        return null;
    }

    /// <summary>
    /// The remembered static end of the alias BINDING <paramref name="binding"/> wired as
    /// <paramref name="wired"/> for a chase that does (<paramref name="followCarriers"/>) or does not
    /// follow carriers, or null after queueing its key for the chase's end. The entry lives on the
    /// nearest activation of the declaring scope chain (so it is forgotten with that call), or run-wide
    /// when the chain has none.
    /// </summary>
    private static AliasStaticEnd? ReadAliasTargetMemo(
        Property binding,
        Algorithm.Alias wired,
        EvalCtx ctx,
        bool followCarriers,
        ref List<(Dictionary<AliasTargetKey, AliasStaticEnd> Memo, AliasTargetKey Key)>? pending)
    {
        var memo = AliasMemoOwner(wired) is { } activation ? activation.AliasTargets : ctx.Budget.AliasTargets;
        var key = new AliasTargetKey(binding, StructuralOwnerIdentity.FromScope(wired.Parent), followCarriers);
        if (memo.TryGetValue(key, out var end))
            return end;
        (pending ??= []).Add((memo, key));
        return null;
    }

    /// <summary>
    /// The memo key of an alias BINDING (a <see cref="Property"/>) or, for a runtime-alias binding cell,
    /// of an alias DECLARATION (a <see cref="DeclarationIdentity"/>, which covers inline aliases too),
    /// together with the resolving identity of the scope chain it is wired under (each level's opens and
    /// properties, by reference; every ownerless host-built level of the chain — the declaring level or
    /// any ancestor — is itself part of it, also by reference:
    /// <see cref="StructuralOwnerIdentity.FromScope"/>) and, for a static end, whether the chase follows
    /// carriers — everything its static part reads besides the activation, which selects the memo the key
    /// lives in. Compared by reference.
    /// </summary>
    internal readonly struct AliasTargetKey(object binding, StructuralOwnerIdentity scope, bool followCarriers = false) : IEquatable<AliasTargetKey>
    {
        private readonly object _binding = binding;
        private readonly StructuralOwnerIdentity _scope = scope;
        private readonly bool _followCarriers = followCarriers;

        public bool Equals(AliasTargetKey other)
            => ReferenceEquals(_binding, other._binding) && _scope.Equals(other._scope) && _followCarriers == other._followCarriers;

        public override bool Equals(object? obj) => obj is AliasTargetKey other && Equals(other);

        public override int GetHashCode()
            => HashCode.Combine(RuntimeHelpers.GetHashCode(_binding), _scope.GetHashCode(), _followCarriers);
    }

    /// <summary>
    /// The member steps of a static path from the scope <paramref name="owner"/>, under
    /// <paramref name="stepCtx"/> whose head it is (Lean <c>staticPathSelectWith</c> over
    /// <c>Expr.staticAliasPath?</c> and <c>aliasStepNavigateWith</c>): a name or block head, then each
    /// DECLARED member of the previous receiver read through its STATIC structure (a transparent reference
    /// is its target's, a carrier its own, a runtime reference has none — nothing is projected), wired to
    /// it and checked for accessibility from the site; a member declared only in branches is the local-only
    /// error, and a missing member or a receiver without static structure has no callable: the path is not
    /// a static alias target (only a host-built tree has one as an alias — the surface pass forms an alias
    /// over a statically known member only). Selecting a member reads the receiver's own declarations, so a
    /// carrier's forwarding output is never consulted. An alias's own step and a spread's written reference
    /// (<see cref="StaticReferenceTerminal"/>) both select here — one navigation,
    /// <see cref="AliasChaseMachine.NavigatePath"/>, on an explicit stack — so <c>R*</c> and <c>Y = R</c>
    /// then <c>Y*</c> select the same binding. Outside a chase, its receivers' structure computations start
    /// from an empty structure context.
    /// </summary>
    private static EvalResult<Algorithm> ResolveStaticPath(Algorithm owner, Expr.DotCall path, EvalCtx stepCtx, out PropertyCallBinding? hop)
        => new AliasChaseMachine().SelectStaticPath(owner, path, stepCtx, out hop);

    private static EvalError AliasCycleError(Algorithm.Alias step)
        => new EvalError.IllegalInEval(AliasCycleMessage) { Span = step.Target.Span };

    private static EvalError NotAStaticAliasTarget(Expr target)
        => new EvalError.IllegalInEval(AliasTargetNotStaticPathMessage(target)) { Span = target.Span };

    /// <summary>Lean: <c>aliasCycleMessage</c>.</summary>
    internal const string AliasCycleMessage
        = "callable alias cycle: an alias target leads back to an alias already on its chain";

    /// <summary>Lean: <c>aliasTargetNotStaticPathMessage</c>.</summary>
    internal static string AliasTargetNotStaticPathMessage(Expr target)
        => $"callable alias target {ExprNameRenderer.Render(target, ExprNameMode.Open)} is not a name or a declared member path";

    /// <summary>
    /// A lexical lookup that selected an alias binding, made CALLABLE (Lean <c>lookupLexicalProperty</c>):
    /// the BINDING stays the alias's own property (its exposure, accessibility and publication identity,
    /// which <see cref="PublicationBinding"/> resolves to the target's), the resolved algorithm becomes the
    /// alias's INVOCATION target.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<ResolvedLexicalProperty> NormalizeAliasBinding(ResolvedLexicalProperty resolved, EvalCtx ctx)
    {
        var target = ResolveAliasTarget((Algorithm.Alias)resolved.ResolvedAlgorithm, ctx, resolved.Binding);
        return target.IsError
            ? target.Error
            : EvalResult<ResolvedLexicalProperty>.Ok(resolved with { ResolvedAlgorithm = target.Value });
    }

    /// <summary>
    /// A VALUE read that selected an alias binding (OD-E, M4★; Lean <c>lookupLexicalValueProperty</c>):
    /// its VALUE terminal — the TERMINAL binding of its static chain (whose key, owner and activation the
    /// read uses, so an alias owns no entry) or, when the chain reaches a runtime-target alias, that alias
    /// as the resolved algorithm (its bare read is its binding cell's VALUE, never a cache entry).
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<ResolvedLexicalProperty> NormalizeAliasValueBinding(ResolvedLexicalProperty resolved, EvalCtx ctx)
    {
        var terminal = ResolveAliasValueTerminal((Algorithm.Alias)resolved.ResolvedAlgorithm, ctx, resolved.Binding);
        if (terminal.IsError)
            return terminal.Error;
        var end = terminal.Value;
        return EvalResult<ResolvedLexicalProperty>.Ok(
            !end.IsRuntime && end.Binding is { } hop
                ? new ResolvedLexicalProperty(hop.Owner, hop.Binding, end.Algorithm, end.CrossesCarrier)
                : resolved with { ResolvedAlgorithm = end.Algorithm, CrossesCarrier = end.CrossesCarrier });
    }

    /// <summary>An inline block that is an alias (<c>{ F }</c>), wired to the caller and normalized for INVOCATION (no binding, so not memoized).</summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<Algorithm> ResolveInlineAliasTarget(Algorithm alias, EvalCtx ctx)
        => ResolveAliasTarget((Algorithm.Alias)WireToCaller(ctx, alias), ctx);

    /// <summary>
    /// THE BARE READ OF A RUNTIME-TARGET ALIAS (FWD-02, META-S3-2; L-RUN, M4★): the VALUE channel of its ONE
    /// binding cell (<see cref="AliasBindingCell"/>) — the very cell its CALLABLE projects, so a computed
    /// receiver (<c>A = Mk(5).Algorithm</c>) is evaluated once whatever observes it first — reported as its
    /// property body reports it (a supplied cell under an alias head finishes with property-style
    /// provenance, never a written-argument slot's: <see cref="FinishSuppliedValue"/>). A parameter row is
    /// its property body's ordinary parameter read, which demands that parameter's own cell. Never a
    /// CALLABLE projection, and no cache entry. Lean: the runtime arm of <c>aliasValue</c>.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalRuntimeAliasValueCounted(Algorithm.Alias wired, EvalCtx ctx, ValEnv valEnv)
        => wired.Target is Expr.Param
            ? EvalCounted(wired.Target, ctx.Push(wired), valEnv)
            : AliasBindingCell(wired, ctx).Demand();

    /// <summary>
    /// THE BARE READ AT A VALUE TERMINAL (OD-E, M4★; Lean <c>terminalAccess</c>): a runtime-target alias is
    /// its binding cell's VALUE; the TERMINAL binding of a static chain is that binding's own bare read —
    /// the property access under its key, owner and activation, so a reference, a carrier and the target
    /// share ONE entry; an algorithm with no binding is its own zero-argument demand. A caller applies the
    /// zero-argument value-demand law to the terminal's algorithm first, reporting as its written reference.
    /// A missing output of a terminal binding is reported as THAT property's (M4★: the alias is its target),
    /// exactly as a lexical read of the binding reports it. Lean: <c>terminalAccess</c>.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> ReadAliasTerminalCounted(AliasTerminal terminal, EvalCtx ctx, ValEnv valEnv)
    {
        var read = terminal.IsRuntime
            ? EvalRuntimeAliasValueCounted((Algorithm.Alias)terminal.Algorithm, ctx, valEnv)
            : terminal.Binding is { } hop
                ? WithPropertyContextOnMissingOutput(hop.Binding.Name, span: null, terminal.Algorithm,
                    EvalZeroArgPropertyAccessCounted(hop.Owner, hop.Binding, ZeroArgPropertyAccessKind.CountedLexical, terminal.Algorithm, ctx, valEnv))
                : EvalZeroArgumentDemandOutputCounted(terminal.Algorithm, ctx, valEnv);
        return terminal.CrossesCarrier ? NestCarrierCrossing(read) : read;
    }

    /// <summary>
    /// A bare read whose lexical lookup selected <paramref name="resolved"/> (<see cref="LookupLexicalForValue"/>):
    /// a runtime-target alias as its resolved algorithm is its binding cell's VALUE (no cache entry); every
    /// other binding — an alias's terminal binding included — is its ordinary zero-argument property access.
    /// </summary>
    private static EvalResult<CountedResult> ReadValueBindingCounted(ResolvedLexicalProperty resolved, EvalCtx ctx, ValEnv valEnv)
    {
        var read = resolved.ResolvedAlgorithm is Algorithm.Alias runtime
            ? EvalRuntimeAliasValueCounted(runtime, ctx, valEnv)
            : EvalZeroArgPropertyAccessCounted(resolved, ctx, valEnv);
        // A read reaching its binding through a structural carrier is nested (Q-36 with M4★).
        return resolved.CrossesCarrier ? NestCarrierCrossing(read) : read;
    }

    /// <summary>
    /// An inline block alias in VALUE position (<c>{ F }</c>): its VALUE terminal's bare read
    /// (<see cref="ReadAliasTerminalCounted"/>; OD-E — the terminal binding's cached read, no entry of its
    /// own), a rejected zero-argument demand reported as its written target reference reports it
    /// (<see cref="ZeroArgumentValueDemandError"/>: <c>{ Inc }</c> with <c>Inc(x)</c> is Inc's own
    /// <see cref="EvalError.ArityMismatch"/>, never the written block's
    /// <see cref="EvalError.UnresolvedImplicitParams"/>; FA-OQ-1, Option B); a chain reaching a
    /// runtime-target alias reads that alias's binding cell. The counterpart of <see cref="EvalAlgorithmExprValue"/>.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<Result> EvalInlineAliasValue(Expr expr, Algorithm alias, EvalCtx ctx, ValEnv valEnv)
    {
        var terminalR = ResolveAliasValueTerminal((Algorithm.Alias)WireToCaller(ctx, alias), ctx);
        if (terminalR.IsError)
            return AtSpanIfMissing(terminalR.Error, expr.Span);

        var terminal = terminalR.Value;
        if (!terminal.IsRuntime && ZeroArgumentValueDemandError(expr, terminal.Algorithm) is { } rejection)
            return rejection;
        return WithSpan(expr.Span, WithSpan(((Algorithm.Alias)alias).Target.Span, ProjectCountedValue(ReadAliasTerminalCounted(terminal, ctx, valEnv))));
    }

    /// <summary>
    /// An inline block alias as a SPREAD operand (<c>{ F }*</c>): the same VALUE terminal read as
    /// <see cref="EvalInlineAliasValue"/>, whose items are spread; a failed operand is reported by
    /// <see cref="SpreadOperandFailure"/> (Q-36). The counterpart of the block arm of
    /// <see cref="EvalSequenceSpreadOperandValue"/>.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<Result> EvalAliasSpreadOperandValue(Expr expr, Algorithm alias, EvalCtx ctx, ValEnv valEnv)
    {
        var terminalR = ResolveAliasValueTerminal((Algorithm.Alias)WireToCaller(ctx, alias), ctx);
        if (terminalR.IsError)
            return AtSpanIfMissing(terminalR.Error, expr.Span);

        var terminal = terminalR.Value;
        if (!terminal.IsRuntime && ZeroArgumentValueDemandError(expr, terminal.Algorithm) is { } rejection)
            return rejection;
        var blockR = WithSpan(((Algorithm.Alias)alias).Target.Span, ProjectCountedValue(ReadAliasTerminalCounted(terminal, ctx, valEnv)));
        if (blockR.IsError)
            return SpreadOperandFailure(expr, expr.Span, blockR.Error);
        return blockR;
    }

    /// <summary>
    /// The dispatch safety net: a call whose callee reached dispatch as an unnormalized alias (a
    /// host-built tree) calls the alias's INVOCATION target with the same written arguments in the
    /// caller's context. Every binding lookup normalizes first, so front-end programs never reach this.
    /// A value-only runtime reference is its value view, an ordinary zero-parameter body.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalAliasCallCounted(
        Algorithm callee,
        OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        var target = ResolveAliasTarget((Algorithm.Alias)callee, ctx);
        return target.IsError ? target.Error : EvalResolvedCallCounted(target.Value, args, ctx, valEnv, calleeName);
    }

    /// <summary>The callback counterpart of <see cref="EvalAliasCallCounted"/>: normalized BEFORE the callback's invocation charge, so an alias charges nothing.</summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalAliasCallbackCallCounted(
        Algorithm callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        ValEnv valEnv,
        string calleeName)
    {
        var target = ResolveAliasTarget((Algorithm.Alias)callee, ctx);
        return target.IsError ? target.Error : EvalResolvedCallbackCallCounted(target.Value, args, ctx, valEnv, calleeName);
    }

    /// <summary>
    /// The demand funnel's alias arm (Lean: the alias arm of <c>evalZeroArgumentDemandOutputCounted</c>):
    /// an alias demanded with zero arguments is its VALUE terminal's bare read (OD-E, M4★) — the terminal
    /// binding's read under ITS key, owner and activation, or a runtime-target alias's binding cell's
    /// VALUE (the VALUE chase never initiates a CALLABLE projection).
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalAliasZeroArgumentDemandCounted(Algorithm algorithm, EvalCtx ctx, ValEnv valEnv)
    {
        var terminal = ResolveAliasValueTerminal((Algorithm.Alias)algorithm, ctx);
        return terminal.IsError ? terminal.Error : ReadAliasTerminalCounted(terminal.Value, ctx, valEnv);
    }

    /// <summary>
    /// A top-level property read of a binding (<see cref="EvalTopLevelZeroArgPropertyCounted"/>): an alias
    /// binding reads its VALUE terminal (<see cref="NormalizeAliasValueBinding"/>), every other binding
    /// itself.
    /// </summary>
    private static EvalResult<ResolvedLexicalProperty> NormalizeTopLevelBinding(Algorithm owner, Property binding, Algorithm wired, EvalCtx ctx)
        => wired is Algorithm.Alias
            ? NormalizeAliasValueBinding(new ResolvedLexicalProperty(owner, binding, wired), ctx)
            : EvalResult<ResolvedLexicalProperty>.Ok(new ResolvedLexicalProperty(owner, binding, wired));

    /// <summary>
    /// The structurally navigated member arm of <see cref="EvalDotCallCounted"/> for a member that is an
    /// alias (<c>Lib.A</c>, <c>Lib.A(args)</c>; Lean: the member arm of <c>evalDotCallCounted</c>): a read is
    /// the member's VALUE terminal — a runtime-target alias's binding cell VALUE, otherwise the TERMINAL
    /// binding's structural zero-argument read (OD-E: never an entry of the alias's own); a call is the
    /// INVOCATION target's ordinary call, whose publication origin is the member binding's target's
    /// (<see cref="PublicationBinding"/>).
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalAliasMemberCounted(
        Algorithm targetAlg,
        Property prop,
        Algorithm wiredAlias,
        OutputBundle? argsOpt,
        string name,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (argsOpt is null)
        {
            var terminalR = ResolveAliasValueTerminal((Algorithm.Alias)wiredAlias, ctx, prop);
            if (terminalR.IsError)
                return terminalR.Error;
            var terminal = terminalR.Value;
            // A read crossing a structural carrier is nested (Q-36 with M4★).
            if (terminal.IsRuntime)
            {
                var runtimeRead = ReCountValueBoundary(EvalRuntimeAliasValueCounted((Algorithm.Alias)terminal.Algorithm, ctx, valEnv));
                return terminal.CrossesCarrier ? NestCarrierCrossing(runtimeRead) : runtimeRead;
            }
            PropertyDeclaringOwner owner = terminal.Binding is { } hop ? hop.Owner : targetAlg;
            var binding = terminal.Binding is { } bound ? bound.Binding : prop;
            var memberRead = EvalAliasMemberRead(owner, binding, terminal.Algorithm, name, ctx, valEnv);
            return terminal.CrossesCarrier ? NestCarrierCrossing(memberRead) : memberRead;
        }

        var wiredR = ResolveAliasTarget((Algorithm.Alias)wiredAlias, ctx, prop);
        if (wiredR.IsError)
            return wiredR.Error;

        var wired = wiredR.Value;
        // CACHE-PUB-1: the selected member binding names the invocation; an alias binding publishes under
        // its TARGET's origin (OD-E / R-6).
        if (MayFormZeroSupply(argsOpt) && TakesOriginDispatch(wired))
            return EvalBoundMemberCallCounted(targetAlg, prop, wired, argsOpt, name, ctx, valEnv);

        return EvalResolvedCallCounted(wired, argsOpt, ctx, valEnv, CallDiagnosticName.FromKnown(name));
    }

    // MIRROR OF the member arm of EvalDotCallCounted (zero-argument read), over the VALUE terminal.
    private static EvalResult<CountedResult> EvalAliasMemberRead(
        PropertyDeclaringOwner owner, Property prop, Algorithm wired, string name, EvalCtx ctx, ValEnv valEnv)
    {
        var simpleCallee = TryGetFlatBinderUserEquivalent(wired);
        if (simpleCallee is not null)
        {
            return AcceptsZeroArgumentValueDemand(simpleCallee)
                ? MarkSelectedMemberOutput(ReCountValueBoundary(EvalZeroArgPropertyAccessCounted(owner, prop, ZeroArgPropertyAccessKind.CountedStructural, simpleCallee, ctx, valEnv)))
                : ZeroArgumentDemandArityMismatch(simpleCallee);
        }

        if (AcceptsZeroArgumentValueDemand(wired))
            return MarkSelectedMemberOutput(ReCountValueBoundary(EvalZeroArgPropertyAccessCounted(owner, prop, ZeroArgPropertyAccessKind.CountedStructural, wired, ctx, valEnv)));

        if (wired is Algorithm.Conditional)
            return new EvalError.NoMatchingBranch(name);

        return ZeroArgumentDemandArityMismatch(wired);
    }

    /// <summary>
    /// The <c>.string</c> intrinsic on a receiver that resolved to an alias (<c>A.string</c>,
    /// <c>Lib.A.string</c>, <c>{ F }.string</c>): the receiver is a VALUE demand, judged on its VALUE
    /// terminal's algorithm and read AS THE ALIAS through the receiver's own route
    /// (<see cref="EvalDotStringReceiverAlgOutput"/>), so every shape reads the TERMINAL binding's cached
    /// entry — the same steps as the intrinsic arm of <see cref="EvalDotCallCounted"/>.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalAliasDotStringCounted(
        Expr target,
        Algorithm aliasAlg,
        bool receiverIsStructuralMember,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var receiverR = ResolveAliasValueTerminal((Algorithm.Alias)aliasAlg, ctx);
        if (receiverR.IsError)
            return receiverR.Error;
        var val = NestMissingOutput(EvalDotStringReceiverAlgOutput(target, aliasAlg, receiverIsStructuralMember, ctx, valEnv, receiverR.Value.Algorithm));
        if (val.IsError) return val.Error;
        var outR = ResultToString(ctx, val.Value);
        if (outR.IsError) return outR.Error;
        return EvalResult<CountedResult>.Ok(new CountedResult(outR.Value, outR.Value.ValueCount()));
    }

    /// <summary>
    /// A <c>.string</c> (or call-reference intrinsic) receiver NAME whose lexical lookup selected an alias
    /// (<see cref="EvalDotStringLexicalPropertyReceiver"/>; Lean: the alias arm of the name case of
    /// <c>evalDotStringReceiverValue</c>): its VALUE terminal's bare read (<see cref="ReadAliasTerminalCounted"/>;
    /// OD-E — the terminal binding's cached entry, or a runtime-target alias's binding cell), inside the
    /// receiver's one depth-only argument level, with a missing output named as the TERMINAL binding's —
    /// exactly what the reference's former row read reported. Out of line, so the receiver frame keeps its
    /// size.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<Result> EvalAliasDotStringLexicalReceiver(Expr target, ResolvedLexicalProperty resolved, EvalCtx ctx, ValEnv valEnv)
    {
        var terminal = ResolveAliasValueTerminal((Algorithm.Alias)resolved.ResolvedAlgorithm, ctx, resolved.Binding);
        if (terminal.IsError)
            return AtSpanIfMissing(terminal.Error, target.Span);

        if (TryEnterArgumentEvaluationLevel(ctx, out var level) is { } limitError)
            return limitError;

        using (level)
        {
            return ProjectCountedValue(ReadAliasTerminalCounted(terminal.Value, ctx, valEnv));
        }
    }

    /// <summary>
    /// A written RECEIVER head (<see cref="ResolveDotReceiver"/>; Lean: the head arms of
    /// <c>resolveDotReceiver?</c>): a name's or a block's binding read through its STRUCTURE (M4★
    /// whole-algorithm transport) — a transparent reference is its target, with the target's members,
    /// context and accessibility; a structural carrier is its OWN declarations only (never its forwarding
    /// target's members); a value-only runtime reference has no structure, so the edge is an ordinary dot
    /// result (an absent identity). Every other receiver shape resolves through <see cref="ResolveAlg"/>.
    /// An alias step's <c>.Algorithm</c> route decision navigates the same head on the chase's own stack
    /// (<see cref="AliasChaseMachine.NavigateRoute"/>).
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<Algorithm> ResolveReceiverHead(Expr target, EvalCtx ctx)
    {
        switch (target)
        {
            case Expr.Resolve(var name):
            {
                if (ctx.CallStack.Count == 0)
                    return new EvalError.UnknownName(name) { Span = target.Span };
                var resolved = ProjectRawLookup(LookupLexicalRaw(ctx.CallStack[0], name, ctx), target.Span);
                return resolved.IsError ? resolved : ReceiverStructure(resolved.Value, target, ctx);
            }

            case Expr.AlgorithmExpr(var block):
                return ReceiverStructure(WireToCaller(ctx, block), target, ctx);

            default:
                return ResolveAlg(target, ctx);
        }
    }

    // A receiver's STRUCTURE: the receiver itself unless it is an alias; a value-only runtime reference
    // is an absent identity (an ordinary dot result).
    private static EvalResult<Algorithm> ReceiverStructure(Algorithm receiver, Expr written, EvalCtx ctx)
    {
        if (receiver is not Algorithm.Alias alias)
            return EvalResult<Algorithm>.Ok(receiver);
        var structure = ResolveAliasStructure(alias, ctx, binding: null);
        if (structure.IsError)
            return AtSpanIfMissing(structure.Error, written.Span);
        return structure.Value is { } algorithm
            ? EvalResult<Algorithm>.Ok(algorithm)
            : new EvalError.NotAnAlgorithm(ExprKind(written)) { Span = written.Span };
    }

    private static EvalResult<Algorithm> ProjectRawLookup(EvalResult<ResolvedLexicalProperty> resolved, SourceSpan? span)
        => resolved.IsError
            ? (resolved.Error.Span is null ? resolved.Error with { Span = span } : resolved.Error)
            : EvalResult<Algorithm>.Ok(resolved.Value.ResolvedAlgorithm);

    /// <summary>
    /// THE PUBLICATION ORIGIN OF AN ALIAS (OD-E, R-6; M4★; Lean <c>aliasOriginBinding?</c>): the property
    /// binding an explicit zero-supply invocation through <paramref name="alias"/> may publish under —
    /// never the alias's own, since an alias owns no zero-argument entry: a static chain's TERMINAL binding
    /// (<see cref="ResolveAliasValueTerminal"/>); a runtime-target alias's binding cell's own written origin
    /// (<see cref="CellCalleeBinding"/>, which follows a supplied <c>.Algorithm</c> link to its plan's
    /// canonical callee cell, CR-13). A failed chase and a value-only origin name no binding. Nothing is
    /// evaluated.
    /// </summary>
    private static PropertyCallBinding? AliasOriginBinding(Algorithm.Alias alias, EvalCtx ctx, Algorithm callee)
    {
        var terminal = ResolveAliasValueTerminal(alias, ctx);
        if (terminal.IsError)
            return null;
        if (!terminal.Value.IsRuntime)
            return terminal.Value.Binding;
        return CellCalleeBinding(AliasBindingCell((Algorithm.Alias)terminal.Value.Algorithm, ctx), callee);
    }

    // ── Async twins ──
    // Every chase may reach a runtime-target alias's projection — a projecting chase directly, a static
    // one through a route decision (`AliasChaseMachine.NavigateRoute`) whose receiver is read through its structure —
    // so the async family runs each through the ONE asynchronous resolution adapter (ResolveAsync,
    // META-S3-0b), which awaits the step and replays its outcome. A runtime alias's bare read awaits its
    // binding cell's VALUE.

    /// <summary>The async twin's INVOCATION chase: <see cref="ResolveAliasTarget"/> through <see cref="ResolveAsync{TState,T}"/>.</summary>
    internal static ValueTask<EvalResult<Algorithm>> ResolveAliasTargetAsync(Algorithm.Alias alias, EvalCtx ctx, Property? binding = null)
        => ResolveAsync(ctx, (alias, ctx, binding), static state => ResolveAliasTarget(state.alias, state.ctx, state.binding));

    /// <summary>The async twin's VALUE chase: <see cref="ResolveAliasValueTerminal"/> through <see cref="ResolveAsync{TState,T}"/>.</summary>
    private static ValueTask<EvalResult<AliasTerminal>> ResolveAliasValueTerminalAsync(Algorithm.Alias alias, EvalCtx ctx, Property? binding = null)
        => ResolveAsync(ctx, (alias, ctx, binding), static state => ResolveAliasValueTerminal(state.alias, state.ctx, state.binding));

    /// <summary>The async twin's VALUE lookup: <see cref="LookupLexicalForValue"/> through <see cref="ResolveAsync{TState,T}"/>.</summary>
    private static ValueTask<EvalResult<ResolvedLexicalProperty>> LookupLexicalForValueAsync(Algorithm alg, string name, EvalCtx ctx)
        => ResolveAsync(ctx, (alg, name, ctx), static state => LookupLexicalForValue(state.alg, state.name, state.ctx));

    /// <summary>The async twin of a VALUE read's alias normalization (<see cref="NormalizeAliasValueBinding"/>) through <see cref="ResolveAsync{TState,T}"/>.</summary>
    private static ValueTask<EvalResult<ResolvedLexicalProperty>> NormalizeAliasValueBindingAsync(ResolvedLexicalProperty resolved, EvalCtx ctx)
        => ResolveAsync(ctx, (resolved, ctx), static state => NormalizeAliasValueBinding(state.resolved, state.ctx));

    /// <summary>MIRROR OF <see cref="EvalRuntimeAliasValueCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalRuntimeAliasValueCountedAsync(Algorithm.Alias wired, EvalCtx ctx, ValEnv valEnv)
        => wired.Target is Expr.Param
            ? await EvalCountedAsync(wired.Target, ctx.Push(wired), valEnv).ConfigureAwait(false)
            : await AliasBindingCell(wired, ctx).DemandAsync().ConfigureAwait(false);

    /// <summary>MIRROR OF <see cref="ReadAliasTerminalCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> ReadAliasTerminalCountedAsync(AliasTerminal terminal, EvalCtx ctx, ValEnv valEnv)
    {
        var read = terminal.IsRuntime
            ? await EvalRuntimeAliasValueCountedAsync((Algorithm.Alias)terminal.Algorithm, ctx, valEnv).ConfigureAwait(false)
            : terminal.Binding is { } hop
                ? WithPropertyContextOnMissingOutput(hop.Binding.Name, span: null, terminal.Algorithm,
                    await EvalZeroArgPropertyAccessCountedAsync(hop.Owner, hop.Binding, ZeroArgPropertyAccessKind.CountedLexical, terminal.Algorithm, ctx, valEnv).ConfigureAwait(false))
                : await EvalZeroArgumentDemandOutputCountedAsync(terminal.Algorithm, ctx, valEnv).ConfigureAwait(false);
        return terminal.CrossesCarrier ? NestCarrierCrossing(read) : read;
    }

    /// <summary>MIRROR OF <see cref="ReadValueBindingCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> ReadValueBindingCountedAsync(ResolvedLexicalProperty resolved, EvalCtx ctx, ValEnv valEnv)
    {
        var read = resolved.ResolvedAlgorithm is Algorithm.Alias runtime
            ? await EvalRuntimeAliasValueCountedAsync(runtime, ctx, valEnv).ConfigureAwait(false)
            : await EvalZeroArgPropertyAccessCountedAsync(resolved, ctx, valEnv).ConfigureAwait(false);
        return resolved.CrossesCarrier ? NestCarrierCrossing(read) : read;
    }

    /// <summary>MIRROR OF <see cref="EvalInlineAliasValue"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> EvalInlineAliasValueAsync(Expr expr, Algorithm alias, EvalCtx ctx, ValEnv valEnv)
    {
        var terminalR = await ResolveAliasValueTerminalAsync((Algorithm.Alias)WireToCaller(ctx, alias), ctx).ConfigureAwait(false);
        if (terminalR.IsError)
            return AtSpanIfMissing(terminalR.Error, expr.Span);

        var terminal = terminalR.Value;
        if (!terminal.IsRuntime && ZeroArgumentValueDemandError(expr, terminal.Algorithm) is { } rejection)
            return rejection;
        return WithSpan(expr.Span, WithSpan(((Algorithm.Alias)alias).Target.Span, ProjectCountedValue(await ReadAliasTerminalCountedAsync(terminal, ctx, valEnv).ConfigureAwait(false))));
    }

    /// <summary>MIRROR OF <see cref="EvalAliasSpreadOperandValue"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> EvalAliasSpreadOperandValueAsync(Expr expr, Algorithm alias, EvalCtx ctx, ValEnv valEnv)
    {
        var terminalR = await ResolveAliasValueTerminalAsync((Algorithm.Alias)WireToCaller(ctx, alias), ctx).ConfigureAwait(false);
        if (terminalR.IsError)
            return AtSpanIfMissing(terminalR.Error, expr.Span);

        var terminal = terminalR.Value;
        if (!terminal.IsRuntime && ZeroArgumentValueDemandError(expr, terminal.Algorithm) is { } rejection)
            return rejection;
        var blockR = WithSpan(((Algorithm.Alias)alias).Target.Span, ProjectCountedValue(await ReadAliasTerminalCountedAsync(terminal, ctx, valEnv).ConfigureAwait(false)));
        if (blockR.IsError)
            return SpreadOperandFailure(expr, expr.Span, blockR.Error);
        return blockR;
    }

    /// <summary>MIRROR OF <see cref="EvalAliasCallCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalAliasCallCountedAsync(
        Algorithm callee,
        OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        var target = await ResolveAliasTargetAsync((Algorithm.Alias)callee, ctx).ConfigureAwait(false);
        return target.IsError
            ? target.Error
            : await EvalResolvedCallCountedAsync(target.Value, args, ctx, valEnv, calleeName).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalAliasCallbackCallCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalAliasCallbackCallCountedAsync(
        Algorithm callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        ValEnv valEnv,
        string calleeName)
    {
        var target = await ResolveAliasTargetAsync((Algorithm.Alias)callee, ctx).ConfigureAwait(false);
        return target.IsError
            ? target.Error
            : await EvalResolvedCallbackCallCountedAsync(target.Value, args, ctx, valEnv, calleeName).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalAliasZeroArgumentDemandCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalAliasZeroArgumentDemandCountedAsync(Algorithm algorithm, EvalCtx ctx, ValEnv valEnv)
    {
        var terminal = await ResolveAliasValueTerminalAsync((Algorithm.Alias)algorithm, ctx).ConfigureAwait(false);
        return terminal.IsError
            ? terminal.Error
            : await ReadAliasTerminalCountedAsync(terminal.Value, ctx, valEnv).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="NormalizeTopLevelBinding"/> — keep in lock-step.</summary>
    private static ValueTask<EvalResult<ResolvedLexicalProperty>> NormalizeTopLevelBindingAsync(Algorithm owner, Property binding, Algorithm wired, EvalCtx ctx)
        => wired is Algorithm.Alias
            ? NormalizeAliasValueBindingAsync(new ResolvedLexicalProperty(owner, binding, wired), ctx)
            : new(EvalResult<ResolvedLexicalProperty>.Ok(new ResolvedLexicalProperty(owner, binding, wired)));

    /// <summary>MIRROR OF <see cref="EvalAliasMemberCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalAliasMemberCountedAsync(
        Algorithm targetAlg,
        Property prop,
        Algorithm wiredAlias,
        OutputBundle? argsOpt,
        string name,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (argsOpt is null)
        {
            var terminalR = await ResolveAliasValueTerminalAsync((Algorithm.Alias)wiredAlias, ctx, prop).ConfigureAwait(false);
            if (terminalR.IsError)
                return terminalR.Error;
            var terminal = terminalR.Value;
            if (terminal.IsRuntime)
            {
                var runtimeRead = ReCountValueBoundary(await EvalRuntimeAliasValueCountedAsync((Algorithm.Alias)terminal.Algorithm, ctx, valEnv).ConfigureAwait(false));
                return terminal.CrossesCarrier ? NestCarrierCrossing(runtimeRead) : runtimeRead;
            }
            PropertyDeclaringOwner owner = terminal.Binding is { } hop ? hop.Owner : targetAlg;
            var binding = terminal.Binding is { } bound ? bound.Binding : prop;
            var memberRead = await EvalAliasMemberReadAsync(owner, binding, terminal.Algorithm, name, ctx, valEnv).ConfigureAwait(false);
            return terminal.CrossesCarrier ? NestCarrierCrossing(memberRead) : memberRead;
        }

        var wiredR = await ResolveAliasTargetAsync((Algorithm.Alias)wiredAlias, ctx, prop).ConfigureAwait(false);
        if (wiredR.IsError)
            return wiredR.Error;
        if (MayFormZeroSupply(argsOpt) && TakesOriginDispatch(wiredR.Value))
            return await EvalOriginCallCountedAsync(CalleeOrigin.Bound(targetAlg, prop), wiredR.Value, argsOpt, ctx, valEnv,
                CallDiagnosticName.FromKnown(name)).ConfigureAwait(false);
        return await EvalResolvedCallCountedAsync(wiredR.Value, argsOpt, ctx, valEnv, CallDiagnosticName.FromKnown(name)).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalAliasMemberRead"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalAliasMemberReadAsync(
        PropertyDeclaringOwner owner, Property prop, Algorithm wired, string name, EvalCtx ctx, ValEnv valEnv)
    {
        var simpleCallee = TryGetFlatBinderUserEquivalent(wired);
        if (simpleCallee is not null)
        {
            return AcceptsZeroArgumentValueDemand(simpleCallee)
                ? MarkSelectedMemberOutput(ReCountValueBoundary(
                    await EvalZeroArgPropertyAccessCountedAsync(
                        owner, prop, ZeroArgPropertyAccessKind.CountedStructural, simpleCallee, ctx, valEnv).ConfigureAwait(false)))
                : ZeroArgumentDemandArityMismatch(simpleCallee);
        }

        if (AcceptsZeroArgumentValueDemand(wired))
            return MarkSelectedMemberOutput(ReCountValueBoundary(
                await EvalZeroArgPropertyAccessCountedAsync(
                    owner, prop, ZeroArgPropertyAccessKind.CountedStructural, wired, ctx, valEnv).ConfigureAwait(false)));

        if (wired is Algorithm.Conditional)
            return new EvalError.NoMatchingBranch(name);

        return ZeroArgumentDemandArityMismatch(wired);
    }

    /// <summary>MIRROR OF <see cref="EvalAliasDotStringLexicalReceiver"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> EvalAliasDotStringLexicalReceiverAsync(Expr target, ResolvedLexicalProperty resolved, EvalCtx ctx, ValEnv valEnv)
    {
        var terminal = await ResolveAliasValueTerminalAsync((Algorithm.Alias)resolved.ResolvedAlgorithm, ctx, resolved.Binding).ConfigureAwait(false);
        if (terminal.IsError)
            return AtSpanIfMissing(terminal.Error, target.Span);

        if (TryEnterArgumentEvaluationLevel(ctx, out var level) is { } limitError)
            return limitError;

        using (level)
        {
            return ProjectCountedValue(await ReadAliasTerminalCountedAsync(terminal.Value, ctx, valEnv).ConfigureAwait(false));
        }
    }

    /// <summary>MIRROR OF <see cref="EvalAliasDotStringCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalAliasDotStringCountedAsync(
        Expr target,
        Algorithm aliasAlg,
        bool receiverIsStructuralMember,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var receiverR = await ResolveAliasValueTerminalAsync((Algorithm.Alias)aliasAlg, ctx).ConfigureAwait(false);
        if (receiverR.IsError)
            return receiverR.Error;
        var val = NestMissingOutput(await EvalDotStringReceiverAlgOutputAsync(target, aliasAlg, receiverIsStructuralMember, ctx, valEnv, receiverR.Value.Algorithm).ConfigureAwait(false));
        if (val.IsError) return val.Error;
        var outR = ResultToString(ctx, val.Value);
        if (outR.IsError) return outR.Error;
        return EvalResult<CountedResult>.Ok(new CountedResult(outR.Value, outR.Value.ValueCount()));
    }
}
