using System.Runtime.CompilerServices;

namespace KatLang;

/// <summary>
/// DECLARATION-LEVEL OUTPUT SPREADING (the static form, November 2026). A declaration written with a
/// postfix <c>*</c> after its name or its parameter list (<c>A* = x, y</c>, <c>A(x, y)* = x, y</c>;
/// <see cref="Algorithm.OutputSpread"/>) changes no algorithm: its parameters, inference, body and result
/// value stay what they are. It changes how CALLS to it are elaborated: this pass spreads every eligible call
/// that statically resolves to a marked declaration exactly where a written <c>*</c> would stand, inserting
/// the existing <see cref="Expr.SequenceSpread"/> (<see cref="Expr.SequenceSpread.InsertedFor"/> names the
/// declaration, for diagnostics only). After elaboration a marked program IS the program with those stars
/// written, so evaluation, Model C demand, caching, the optimizer and Lean's core are unchanged.
/// <para><b>Eligible call</b> (R1): <c>N(args)</c>, <c>(Path.N)(args)</c>, <c>Path.N(args)</c>, or an
/// extension call <c>x.N(args)</c> / <c>x.N</c> (the call <c>N(x, args)</c>) — written, or synthesized by
/// formula lifting or bare forwarding — whose callee resolves statically (owner walk, prelude, <c>open</c>,
/// static member path, module member) to a declaration whose STRUCTURAL identity — Q3's target walk, the
/// one a dot edge reads members from (<see cref="ReadDeclaration"/>) — is marked: through transparent
/// references, never through a structural forwarding carrier (a carrier is a declaration of its own), and
/// never through a runtime reference (a parameter, a runtime-target alias, a member only a runtime receiver
/// provides, an <c>.Algorithm</c> link of either class). Every decision reads the WRITTEN input of this pass
/// — the detector's stamped dot-edge verdict included, never a verdict this pass refines — so the B3-5★
/// analysis and the rewrite decide every slot alike. A read is not a call: a bare <c>P</c> never spreads.</para>
/// <para><b>Eligible position</b> (R2): exactly where a written <c>*</c> is legal and spreads — a whole output
/// row, a whole argument slot of any callee, a whole selector slot, a list element or an element of a
/// multi-slot group, the operand of an explicit <c>*</c> (the chained-spread law), and the receiver of an
/// extension-call edge, which is lowered as the parser lowers <c>A*.F(args)</c>: to <c>F(A*, args)</c>.
/// Everywhere else (operands, selection and intrinsic-edge receivers, callees) a call stays one value.</para>
/// <para><b>The receiver</b> (owner decision D1): a WRITTEN marked call as the receiver of an extension edge is
/// lowered by PARAMETER DETECTION, where the inferred names are ordered, so <c>A(x, y).F(3)</c> infers its names as
/// the call <c>F(A(x, y)*, 3)</c> does and this pass receives that call
/// (<see cref="StaticStructureQueries.LoweredReceiver"/>, <c>ParameterDetector.RewriteLoweredReceiver</c>). This pass
/// lowers only the receiver it lifted itself (<see cref="LowerLiftedMarkedReceiver"/>).</para>
/// <para><b>Argument roles</b> (owner decision D2): a slot this pass will spread — a written marked call, or a bare
/// reference to a marked declaration that formula lifting turns into a call — makes the positions after it unknown to
/// the argument roles, exactly as a written spread does. Roles and spread slots are decided together, before
/// signature selection, from static facts (<see cref="ArgumentRolesWithSpreads"/>, read by the one role walk and by
/// the rewrite, which checks each prediction: <see cref="RequirePredictedLift"/>); a reference whose lift only
/// selection decides is <see cref="DiagnosticCode.OutputSpreadReferenceNeedsCall"/> where the elaboration depends
/// on it.</para>
/// <para>Only a program whose admission met a marker asks any of this
/// (<see cref="StaticStructureOperation.AdmittedWithOutputSpreadMarkers"/>, inherited by a deferred unit), so
/// every other program elaborates exactly as before. The decision reads only static facts of this pass (the
/// region's signature map and the operation's queries), so a rewrite region keyed by its binding context
/// decides it identically wherever it is shared, and a shared implicit-argument bundle (FE-2) is never
/// touched: only the call node that holds it is wrapped.</para>
/// </summary>
internal static partial class ImplicitArgumentResolver
{
    /// <summary>
    /// THE ONE INSERTION: <paramref name="processed"/>, the rewrite of <paramref name="input"/> standing in an
    /// eligible position, spread when it is an eligible call to a marked declaration (<see cref="MarkedSlotOf"/>),
    /// and returned unchanged otherwise. The inserted node takes the call's span (no star was written), so a
    /// diagnostic positioned at it points at the call. Out of line, so the span temporary never enlarges a
    /// calibrated rewrite frame.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static Expr SpreadIfMarked(Expr input, Expr processed, SignatureMap paramMap, ResolverWalkMemos memos)
        => memos.Run.StructuralOperation.AdmittedWithOutputSpreadMarkers
            && MarkedSlotOf(input, processed, paramMap, memos.Run) is { } marker
                ? new Expr.SequenceSpread(processed) { Span = processed.Span, InsertedFor = marker }
                : processed;

    /// <summary>
    /// The marker an eligible slot spreads for: decided on the WRITTEN slot <paramref name="input"/>, except that a
    /// bare reference — a name, or an argumentless structural member path — is no call, and is spread only when
    /// formula lifting or bare forwarding made it one (<paramref name="processed"/>, decided on that call).
    /// </summary>
    private static OutputSpreadMarker? MarkedSlotOf(Expr input, Expr processed, SignatureMap paramMap, ResolutionRun run)
        => IsBareReference(input)
            ? IsCall(processed) ? MarkedCalleeOf(processed, paramMap, run) : null
            : MarkedCalleeOf(input, paramMap, run);

    /// <summary>
    /// The receiver arm of R2, for a LIFTED receiver: an extension-call edge <c>R.F(args)</c> whose written edge's lexical
    /// fallback is certainly selected (the detector's stamp) and whose receiver is a bare reference to a marked declaration
    /// that formula lifting made a call is the call <c>F(R(…)*, args)</c>, built exactly as the parser builds
    /// <c>R*.F(args)</c> — the edge's own lexical fallback as the callee, the spread receiver as the leading argument, then
    /// the processed written arguments. Null for every other edge. A receiver that is a WRITTEN call never reaches this
    /// pass as an edge (owner decision D1): parameter detection lowers it, where the inferred names are ordered
    /// (<c>ParameterDetector.RewriteLoweredReceiver</c>), and this pass decides nothing about it. A bare reference holds no
    /// inferred name, so lowering its edge here cannot move one.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static Expr? LowerLiftedMarkedReceiver(
        Expr.DotCall written, Expr.DotCall processed, SignatureMap paramMap, ResolverWalkMemos memos)
    {
        if (!memos.Run.StructuralOperation.AdmittedWithOutputSpreadMarkers
            || StampedEdgeKind(written) != DotEdgeKind.Fallback
            || !IsBareReference(written.Target)
            || !IsCall(processed.Target)
            || MarkedDeclarationOf(written.Target, paramMap, memos.Run) is not { } marker)
            return null;

        var receiver = new Expr.SequenceSpread(processed.Target) { Span = processed.Target.Span, InsertedFor = marker };
        var args = new List<Expr>(1 + (processed.Args?.Count ?? 0)) { receiver };
        if (processed.Args is { } writtenArgs)
            foreach (var argument in writtenArgs)
                args.Add(argument);
        return new Expr.Call(processed.EffectiveLexicalFallback, new OutputBundle(args)) { Span = processed.Span };
    }

    // ═══ Roles and marked spreads, decided together (owner decision D2) ═══════════════════════════════════════════

    /// <summary>
    /// What static facts settle, BEFORE signature selection, about a bare reference to a marked declaration standing in a
    /// VALUE role (<see cref="StaticLiftOf"/>): whether formula lifting turns it into a call, which the front end then
    /// spreads — making the positions after it unknown to the argument roles, exactly as a written <c>*</c> does.
    /// </summary>
    private enum StaticLift : byte
    {
        /// <summary>No bare reference to a marked declaration in a value role: nothing to predict.</summary>
        None,

        /// <summary>A READ: the callee accepts zero supplied arguments, or the closed list cannot supply them (R3: no spread, no role change).</summary>
        NotLifted,

        /// <summary>A CALL: the callee requires a supplied argument, so the reference is lifted and its call spread.</summary>
        Lifted,

        /// <summary>
        /// A SELECTION RESULT: an open body with no required parameter of its own whose rows could lift one
        /// (<c>P* = Q + 0</c>). Only signature selection decides it, and selection reads these very roles.
        /// </summary>
        Selected,
    }

    /// <summary>A bare reference: a name, or an argumentless structural member path (the two shapes formula lifting turns into calls).</summary>
    private static bool IsBareReference(Expr slot)
        => slot is Expr.Resolve || slot is Expr.DotCall { Args: null } path && StampedEdgeKind(path) == DotEdgeKind.StructuralMember;

    /// <summary>A call as formula lifting writes one: <c>N(args)</c>, or a structural member path with arguments.</summary>
    private static bool IsCall(Expr processed) => processed is Expr.Call or Expr.DotCall { Args: not null };

    /// <summary>
    /// THE ONE DECISION of the argument roles in a program with markers: the roles of a call's written argument slots and
    /// the slots the front end will spread for a marked declaration, decided TOGETHER, left to right, each slot's role read
    /// at the position state the earlier slots left (<see cref="FormulaLiftingRoles.SlotRole"/>). A slot ends the known
    /// positions when it is a written spread, a written call to a marked declaration (<see cref="MarkedCalleeOf"/>), or a
    /// bare reference to one that static facts show formula lifting will call (<see cref="StaticLift.Lifted"/>): so
    /// <c>reduce(P, Add, Inc)</c>, <c>reduce(P(x), Add, Inc)</c> with a marked <c>P(x)</c>, and <c>reduce(P*, Add, Inc)</c>
    /// with an unmarked one all classify <c>Inc</c> alike, and elaborate to the same tree. The B3-5★ signature analysis and
    /// the rewrite both read THIS (the role walk's sinks, <see cref="RewriteCall"/>,
    /// <see cref="RewriteDotCall"/>, <see cref="CertainMissDecidesALift"/>), so what an equation records, what is lifted and
    /// how a call is rewritten cannot drift; the rewrite then checks every prediction against the call it actually built
    /// (<see cref="RequirePredictedLift"/>, <paramref name="lifts"/>).
    /// <para>A reference whose lift only selection decides (<see cref="StaticLift.Selected"/>) cannot be classified here:
    /// it is the front-end error <see cref="DiagnosticCode.OutputSpreadReferenceNeedsCall"/> exactly when the elaboration
    /// depends on it — when a slot after it, up to and including the first slot that ends the known positions, depends on
    /// the position (<see cref="DependsOnPosition"/>) — reported by the rewrite (<paramref name="report"/>).
    /// Otherwise both readings elaborate alike, and the slot is spread if it was lifted.</para>
    /// <para>THE WALK DECIDES THE DEPENDENCE TOO, in one pass (<see cref="RolesWithSpreadsWalk"/>): such a reference waits,
    /// unreported, until the walk reaches a slot that depends on the position — the witness, which reports every reference
    /// then waiting, in slot order — and the references still waiting where the known positions end depend on nothing,
    /// since no later slot differs. The witness test PRECEDES the boundary test, so one slot (a marked reference that is
    /// certainly lifted where its role depends on the position) can be both. So each written slot is inspected once,
    /// whatever the number of references waiting on it: a call costs its written slots, never those slots times the
    /// waiting references (a rescan of the suffix per reference made a width-N call of selection results N(N−1)/2
    /// inspections). The reports are the rewrite's only diagnostics here, so deferring each to its witness keeps their
    /// order.</para>
    /// <para>A program without markers reads <see cref="FormulaLiftingRoles.ArgumentRoles"/> exactly as before.</para>
    /// <para>Out of line, so the calibrated rewrite frame of <see cref="RewriteCall"/> passes the arguments it always did.</para>
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static LiftingRole[] ArgumentRolesWithSpreads(
        LiftingCallee callee, OutputBundle args, int leadingSlots, bool leadingPositionsKnown,
        SignatureMap paramMap, ResolverWalkMemos memos, out StaticLift[]? lifts, bool report = false)
        => RolesWithSpreadsWalk(callee, args, leadingSlots, leadingPositionsKnown, selectedReceiver: null, paramMap, memos, out lifts, report);

    /// <summary>
    /// The one walk of <see cref="ArgumentRolesWithSpreads"/>, where a selected fallback's receiver
    /// (<paramref name="selectedReceiver"/>, <see cref="DotArgumentRolesWithSpreads"/>) is a selection result at slot 0: it
    /// waits from before the first argument, at known positions, and the witness reports it before every argument.
    /// </summary>
    private static LiftingRole[] RolesWithSpreadsWalk(
        LiftingCallee callee, OutputBundle args, int leadingSlots, bool leadingPositionsKnown, Expr? selectedReceiver,
        SignatureMap paramMap, ResolverWalkMemos memos, out StaticLift[]? lifts, bool report)
    {
        lifts = null;
        if (!memos.Run.StructuralOperation.AdmittedWithOutputSpreadMarkers)
            return FormulaLiftingRoles.ArgumentRoles(callee, args, leadingSlots, leadingPositionsKnown);

        var roles = new LiftingRole[args.Count];
        var positionKnown = leadingPositionsKnown;
        // The selection results awaiting a witness: the receiver, then each slot from `firstWaiting` on whose lift is
        // Selected (every one of them sits at a known position before the current slot).
        var waitingReceiver = report ? selectedReceiver : null;
        var firstWaiting = -1;
        for (var index = 0; index < args.Count; index++)
        {
            var role = roles[index] = FormulaLiftingRoles.SlotRole(callee, leadingSlots + index, positionKnown);
            // Once a position is unknown, every later one is: nothing after it can change a role.
            if (!positionKnown)
                continue;
            var slot = args[index];
            // A witness is tested before the slot is read as a boundary: the slot that ends the known positions still counts.
            if ((waitingReceiver is not null || firstWaiting >= 0)
                && DependsOnPosition(callee, slot, leadingSlots + index, role, paramMap, memos))
            {
                ReportWaitingSelectionResults(waitingReceiver, args, firstWaiting, index, lifts, paramMap, memos);
                waitingReceiver = null;
                firstWaiting = -1;
            }

            if (slot is Expr.SequenceSpread || MarkedCalleeOf(slot, paramMap, memos.Run) is not null)
            {
                positionKnown = false;
                continue;
            }

            var lift = MarkedReferenceLift(slot, role, paramMap, memos);
            if (lift == StaticLift.None)
                continue;
            (lifts ??= new StaticLift[args.Count])[index] = lift;
            if (lift == StaticLift.Lifted)
                positionKnown = false;
            else if (lift == StaticLift.Selected && report && firstWaiting < 0)
                firstWaiting = index;
        }

        return roles;
    }

    /// <summary>
    /// Reports the selection results a witness found waiting in <see cref="RolesWithSpreadsWalk"/>: the receiver, then
    /// every slot from <paramref name="firstWaiting"/> (none when negative) before the witness <paramref name="witness"/>
    /// whose lift is <see cref="StaticLift.Selected"/>. The ranges of successive witnesses are disjoint, so a walk reads
    /// each slot here at most once.
    /// </summary>
    private static void ReportWaitingSelectionResults(
        Expr? waitingReceiver, OutputBundle args, int firstWaiting, int witness, StaticLift[]? lifts, SignatureMap paramMap, ResolverWalkMemos memos)
    {
        if (waitingReceiver is not null)
            ReportOutputSpreadReferenceNeedsCall(waitingReceiver, paramMap, memos);
        if (firstWaiting < 0)
            return;
        for (var waiting = firstWaiting; waiting < witness; waiting++)
        {
            if (lifts![waiting] == StaticLift.Selected)
                ReportOutputSpreadReferenceNeedsCall(args[waiting], paramMap, memos);
        }
    }

    /// <summary>
    /// The roles of a dot edge's written arguments with the marked spreads among them (<see cref="ArgumentRolesWithSpreads"/>):
    /// a structural member's own slots; a selected fallback's slots after the receiver, at unknown positions after a
    /// written spread receiver or a receiver formula lifting will call for a marked declaration
    /// (<paramref name="receiverLift"/>, <see cref="ReceiverLift"/>); nothing value-demanded for an undecided edge or an
    /// intrinsic.
    /// </summary>
    private static LiftingRole[] DotArgumentRolesWithSpreads(
        Expr.DotCall edge, DotEdgeKind kind, LiftingCallee callee, StaticLift receiverLift,
        SignatureMap paramMap, ResolverWalkMemos memos, out StaticLift[]? lifts, bool report = false)
    {
        if (!memos.Run.StructuralOperation.AdmittedWithOutputSpreadMarkers)
        {
            lifts = null;
            return FormulaLiftingRoles.DotArgumentRoles(edge, kind, callee);
        }

        var args = edge.Args ?? OutputBundle.Empty;
        switch (kind)
        {
            case DotEdgeKind.StructuralMember:
                return ArgumentRolesWithSpreads(callee, args, leadingSlots: 0, leadingPositionsKnown: true, paramMap, memos, out lifts, report);

            case DotEdgeKind.Fallback:
                // The receiver is slot 0 (a selection result's positions after it are known): one walk decides its report
                // and the arguments', the receiver's first.
                return RolesWithSpreadsWalk(
                    callee, args, leadingSlots: 1,
                    leadingPositionsKnown: edge.Target is not Expr.SequenceSpread && receiverLift != StaticLift.Lifted,
                    selectedReceiver: receiverLift == StaticLift.Selected ? edge.Target : null,
                    paramMap, memos, out lifts, report);

            default:
                lifts = null;
                return FormulaLiftingRoles.ArgumentRoles(LiftingCallee.Dynamic, args);
        }
    }

    /// <summary>
    /// The static lift of a selected fallback's receiver (slot 0 of the fallback callee): decided on the WRITTEN edge's
    /// stamp, like every output-spreading decision of this pass, and only for a bare reference to a marked declaration in a
    /// value role. A lifted one is lowered to the leading spread argument of <c>F(R(…)*, args)</c>
    /// (<see cref="LowerLiftedMarkedReceiver"/>), so the positions after it are unknown, as after a written <c>R*.F</c>.
    /// </summary>
    private static StaticLift ReceiverLift(Expr.DotCall written, DotEdgeKind kind, LiftingCallee callee, SignatureMap paramMap, ResolverWalkMemos memos)
        => kind == DotEdgeKind.Fallback
            && memos.Run.StructuralOperation.AdmittedWithOutputSpreadMarkers
            && StampedEdgeKind(written) == DotEdgeKind.Fallback
                ? MarkedReferenceLift(written.Target, FormulaLiftingRoles.ReceiverRole(kind, callee), paramMap, memos)
                : StaticLift.None;

    /// <summary>The static lift of <paramref name="slot"/> when it is a bare reference to a marked declaration in a value role.</summary>
    private static StaticLift MarkedReferenceLift(Expr slot, LiftingRole role, SignatureMap paramMap, ResolverWalkMemos memos)
        => role == LiftingRole.Value && IsBareReference(slot) && MarkedDeclarationOf(slot, paramMap, memos.Run) is not null
            ? StaticLiftOf(slot, paramMap, memos)
            : StaticLift.None;

    /// <summary>
    /// Whether formula lifting turns the bare VALUE-role reference <paramref name="reference"/> into a call, as far as
    /// static facts settle it before signature selection — the rule the rewrite applies with final signatures
    /// (<see cref="TryGetLiftArguments"/>: a callee whose lifting signature requires a supplied argument, which a closed
    /// list must be able to supply), read from what selection cannot change:
    /// <list type="bullet">
    ///   <item>a FINAL signature — a registry member, a clause family (unnameable: never lifted), a closed list, a body an
    ///   earlier operation completed — decides it;</item>
    ///   <item>an OPEN body of this resolution whose OWN patterns (written, or inferred by parameter detection) require a
    ///   supplied argument is lifted: its selected signature is those patterns, then what it lifts;</item>
    ///   <item>an open body with no required parameter of its own whose rows hold no reference lifting could take
    ///   (<see cref="HoldsALiftableReference"/>) lifts nothing, so it is read;</item>
    ///   <item>every other open body is a selection result.</item>
    /// </list>
    /// A reference with no static callable identity is never lifted. The closed-list gate is read only inside a closed
    /// body's rewrite (the one place it exists), where every signature is final.
    /// </summary>
    private static StaticLift StaticLiftOf(Expr reference, SignatureMap paramMap, ResolverWalkMemos memos)
    {
        var run = memos.Run;
        if (ResolveStaticCallable(reference, paramMap, memos, out _) is not { } callable)
            return StaticLift.NotLifted;

        var operation = run.StructuralOperation;
        if (callable.Key is { } key && operation.EarlierResolvedView(key) is null
            && (operation.DetectedView(key) ?? callable.Written) is Algorithm.User { HasExplicitParameterList: false } open)
        {
            if (ParameterPattern.AcceptsZeroSuppliedSlots(open.ParameterPatterns))
                return HoldsALiftableReference(key, open, run) ? StaticLift.Selected : StaticLift.NotLifted;
        }
        else if (FinalLiftingSignature(callable, callable.DisplayName, run).Signature is not { } final || !RequiresSuppliedArguments(final))
        {
            return StaticLift.NotLifted;
        }

        return memos.PinnedRewriteContext is { ClosedParameterNames: not null } closed
            && TargetOf(callable, run).Signature.Signature is { } selected
            && ClosedListBlocksLifting(closed, selected.ParameterPatterns, memos)
                ? StaticLift.NotLifted
                : StaticLift.Lifted;
    }

    /// <summary>
    /// Whether the written rows of the open body <paramref name="body"/> hold a VALUE-role reference that could lift
    /// (D2's "potentially liftable", decided RECURSIVELY). Uses the production role walk and Q3 endpoints in the body's
    /// OWN context: a callback is never a value use, and a final zero-supply signature is certainly a read. A value-role
    /// reference can lift when its callee is
    /// <list type="bullet">
    ///   <item>a final signature that requires a supplied argument;</item>
    ///   <item>an open body of this resolution with a required parameter of its own (written, or inferred by parameter
    ///   detection);</item>
    ///   <item>an open body of this resolution whose own rows hold a reference that can lift, by this same rule in THAT
    ///   body's context;</item>
    ///   <item>a runtime fact (an <c>.Algorithm</c> link, whose signature can gain its target's parameters), which stays
    ///   conservative, as an undecided dot route does (the walk takes its fallback).</item>
    /// </list>
    /// So the verdict is REACHABILITY over contextual bodies: a body can lift exactly when a chain of such references
    /// leads from it to one of the first two or the last. A required parameter of a selected signature comes only from an
    /// own inferred name, from a lifted reference to a callee that requires arguments, or from a link class selection
    /// decides; a body that reaches none of them is given none, and a group of open bodies that read only each other
    /// reaches none. Nothing reads a selected signature or depends on the order bodies are analyzed in. Blocks are their
    /// own levels. Once per contextual body per resolution, charged to the operation's ledger.
    /// </summary>
    private static bool HoldsALiftableReference(StaticScopeKey scope, Algorithm.User body, ResolutionRun run)
    {
        var known = run.LiftableReferenceBodies ??= new(ReferenceEqualityComparer.Instance);
        if (known.TryGetValue(scope, out var holds))
            return holds;

        // Forward: every open body this one reaches through value-role references, each walked once. A body that holds a
        // direct source is liftable and is explored no further; every other body's dependencies are all explored, so the
        // bodies left unmarked form a set closed under the relation, none of which reaches a source.
        var resources = run.StructuralOperation.Queries.Resources;
        var explored = new List<StaticScopeKey>();
        var liftable = new HashSet<StaticScopeKey>(ReferenceEqualityComparer.Instance);
        var reached = new HashSet<StaticScopeKey>(ReferenceEqualityComparer.Instance) { scope };
        Dictionary<StaticScopeKey, List<StaticScopeKey>>? readers = null;
        var pending = new Stack<(StaticScopeKey Scope, Algorithm.User Body)>();
        pending.Push((scope, body));
        while (pending.TryPop(out var current))
        {
            explored.Add(current.Scope);
            var sink = new PotentialLiftSink(current.Scope, run);
            foreach (var row in AstHelpers.WrittenRows(current.Body))
                WalkLiftingRoles(row, LiftingRole.Value, null, ref sink);

            resources.Metadata(2, cancellationToken: run.CancellationToken);
            if (sink.Found)
            {
                liftable.Add(current.Scope);
                continue;
            }

            if (sink.OpenDependencies is not { } dependencies)
                continue;
            foreach (var (dependency, dependencyBody) in dependencies)
            {
                resources.Work(1, run.CancellationToken);
                if (known.TryGetValue(dependency, out var settled))
                {
                    if (settled)
                        liftable.Add(current.Scope);
                    continue;
                }

                readers ??= new(ReferenceEqualityComparer.Instance);
                if (!readers.TryGetValue(dependency, out var readersOfDependency))
                    readers.Add(dependency, readersOfDependency = []);
                readersOfDependency.Add(current.Scope);
                if (reached.Add(dependency))
                    pending.Push((dependency, dependencyBody));
            }
        }

        // Backward: a body that reads a liftable body is liftable.
        if (readers is not null && liftable.Count > 0)
        {
            var sources = new Stack<StaticScopeKey>(liftable);
            while (sources.TryPop(out var source))
            {
                if (!readers.TryGetValue(source, out var readersOfSource))
                    continue;
                foreach (var reader in readersOfSource)
                    if (liftable.Add(reader))
                        sources.Push(reader);
            }
        }

        foreach (var key in explored)
            known[key] = liftable.Contains(key);
        return liftable.Contains(scope);
    }

    /// <summary>
    /// The preselection instantiation of the ONE role walk. Its value roles are a safe superset: an undecided dot edge
    /// may take its fallback, and an automatic spread may only turn a later value role into a callable role. Thus finding
    /// no potentially lifted reference proves a read without solving any signature equations. A reference whose callee is
    /// an open body with no required parameter of its own decides nothing here: the body is recorded
    /// (<see cref="OpenDependencies"/>) and <see cref="HoldsALiftableReference"/> follows it.
    /// </summary>
    private struct PotentialLiftSink(StaticScopeKey scope, ResolutionRun run) : ILiftingWalkSink
    {
        private readonly HashSet<Expr> _values = new(ReferenceEqualityComparer.Instance);
        private readonly HashSet<Expr> _callables = new(ReferenceEqualityComparer.Instance);
        public bool Found;

        /// <summary>The open bodies the value-role references of the walked rows name, each in its own context.</summary>
        public List<(StaticScopeKey Scope, Algorithm.User Body)>? OpenDependencies;

        public bool Enter(Expr expr, LiftingRole role, StaticScopeKey? guard)
        {
            if (Found)
                return false;
            var resources = run.StructuralOperation.Queries.Resources;
            resources.Work(1, run.CancellationToken);
            if (!(role == LiftingRole.Value ? _values : _callables).Add(expr))
                return false;
            resources.Metadata(2, cancellationToken: run.CancellationToken);
            return true;
        }

        public void Exit(Expr expr, LiftingRole role, StaticScopeKey? guard) { }

        public void Reference(Expr reference, StaticScopeKey? guard)
        {
            if (CallableAt(reference, out var runtime) is not { } callable)
                return;
            var operation = run.StructuralOperation;
            if (callable.Key is { } key && operation.EarlierResolvedView(key) is null
                && (operation.DetectedView(key) ?? callable.Written) is Algorithm.User { HasExplicitParameterList: false } open)
            {
                // An open dependency may acquire parameters during selection: certainly when its own patterns require a
                // supplied argument, and through a runtime fact, which stays conservative. Otherwise only through what its
                // own rows can lift, which reachability decides.
                if (runtime || !ParameterPattern.AcceptsZeroSuppliedSlots(open.ParameterPatterns))
                    Found = true;
                else
                    (OpenDependencies ??= []).Add((key, open));
                return;
            }

            // Every other signature is already final.
            Found = FinalLiftingSignature(callable, callable.DisplayName, run).Signature is { } signature
                && RequiresSuppliedArguments(signature);
        }

        private StaticCallable? CallableAt(Expr reference) => CallableAt(reference, out _);

        private StaticCallable? CallableAt(Expr reference, out bool runtime)
        {
            var operation = run.StructuralOperation;
            var selected = operation.Read(StaticQueryKey.Project(
                StaticQueryKind.TargetWalk, scope, StaticQueryProjection.Receiver, node: reference.UnwrapGraceOperand()));
            runtime = selected.Kind == StaticFactKind.Runtime;
            // Runtime structure is not absence of a declaration: a link's signature can still gain parameters.
            return selected.Kind is StaticFactKind.Structure or StaticFactKind.Runtime && selected.Scope is { } target
                ? InvocationCallable(operation.Declaration(target), reference switch
                {
                    Expr.Resolve resolve => resolve.Name,
                    Expr.DotCall edge => edge.Name,
                    _ => "<anonymous>",
                }, run)
                : null;
        }

        public LiftingCallee CalleeKind(Expr callee)
            => CallableAt(callee) is { } callable
                ? LiftingCallee.OfAlgorithm(callable.Written, run.Prelude.IsStrictValue(callable.Written))
                : LiftingCallee.Dynamic;

        public DotEdgeKind EdgeKind(Expr.DotCall edge, out DotEdgeKind mayKind, out StaticScopeKey? link)
        {
            mayKind = default;
            link = null;
            var miss = edge.ElaboratedMissSelection ?? run.StructuralOperation.Miss(scope, edge);
            return FormulaLiftingRoles.EdgeKind(edge,
                miss == LexicalFallbackSelection.Conditional ? LexicalFallbackSelection.Always : miss);
        }

        public LiftingCallee DotEdgeCallee(Expr.DotCall edge, DotEdgeKind kind)
            => kind switch
            {
                DotEdgeKind.StructuralMember => CalleeKind(edge with { Args = null }),
                DotEdgeKind.Fallback => CalleeKind(edge.EffectiveLexicalFallback),
                _ => LiftingCallee.Dynamic,
            };

        public LiftingRole[] ArgumentRoles(LiftingCallee callee, OutputBundle args)
            => FormulaLiftingRoles.ArgumentRoles(callee, args);

        public LiftingRole[] DotArgumentRoles(Expr.DotCall edge, DotEdgeKind kind, LiftingCallee callee)
            => FormulaLiftingRoles.DotArgumentRoles(edge, kind, callee);
    }

    /// <summary>
    /// Whether the elaboration depends, at <paramref name="slot"/> (supplied position <paramref name="position"/>, whose
    /// role at a known position is <paramref name="known"/>), on a reference before it whose lift only selection decides:
    /// the slot's role differs at a known and at an unknown position — a builtin value slot of a builtin that also has a
    /// callable slot: after a spread it is a value only when every declared slot is
    /// (<see cref="FormulaLiftingRoles.SlotRole"/>; <c>reduce</c>'s initial value and a surplus slot of <c>map</c> or
    /// <c>filter</c> are such slots, <c>if</c> has none, and a callback slot is callable at both) — AND it holds a bare
    /// reference the value role could lift and the callable role keeps. Asked by the one role walk
    /// (<see cref="RolesWithSpreadsWalk"/>) of each slot at a known position while a selection result waits, so at
    /// most once per written slot; the walk stops asking at the first slot that makes the positions unknown under either
    /// reading (a written spread, a written marked call, a marked reference that is certainly lifted), after asking it.
    /// </summary>
    private static bool DependsOnPosition(
        LiftingCallee callee, Expr slot, int position, LiftingRole known, SignatureMap paramMap, ResolverWalkMemos memos)
    {
        memos.Run.Observations?.RecordOutputSpreadDependenceSlotInspection();
        return known != FormulaLiftingRoles.SlotRole(callee, position, positionKnown: false)
            && slot.UnwrapGraceOperand() is var reference && IsBareReference(reference)
            && StaticLiftOf(reference, paramMap, memos) is StaticLift.Lifted or StaticLift.Selected;
    }

    /// <summary>
    /// THE PREDICTION INVARIANT (D2), the mirror of <see cref="RequireSelectedComposition"/>: the rewrite turned a bare
    /// reference to a marked declaration into a call exactly where <see cref="StaticLiftOf"/> said it would, so the roles
    /// every phase read are the roles of the tree that was built. A difference means the static rule and formula lifting
    /// disagree — an internal defect of this pass, never a program's error — so it fails loudly instead of publishing a
    /// tree whose later slots were classified for another one. A selection result predicts nothing.
    /// </summary>
    private static void RequirePredictedLift(Expr written, Expr processed, StaticLift predicted)
    {
        if (predicted is StaticLift.None or StaticLift.Selected || IsCall(processed) == (predicted == StaticLift.Lifted))
            return;
        throw new InvalidOperationException(
            $"Implicit-argument resolution predicted that the reference '{ExprNameRenderer.Render(written, ExprNameMode.Open)}' to a declaration marked with `*` "
            + (predicted == StaticLift.Lifted ? "is lifted to a call, but the rewrite left it a read" : "stays a read, but the rewrite lifted it to a call")
            + ": the argument roles and formula lifting read different facts.");
    }

    /// <summary>
    /// Reports <see cref="DiagnosticCode.OutputSpreadReferenceNeedsCall"/> at the bare reference (inside imported content,
    /// at the import site), once per reference per region. The message gives both spellings: the call, whose result is
    /// spread, and the braced read, which is one value.
    /// <para>A transparent reference's own refused marker likewise suppresses this report, even when its target carries
    /// a valid marker. Q3's structural endpoint differs from the selected declaration exactly for such a reference;
    /// carriers keep their own structure. An unmarked alias still inherits its target's ordinary use-site obligation.</para>
    /// <para>A REFUSED MARKER DECIDES NOTHING AT ITS USES: a reference whose invocation endpoint is a runtime-target body
    /// (<see cref="IsRuntimeTargetEndpoint"/>, the selected class the rewrite forms its alias from, whatever the order
    /// bodies are processed in) names a declaration the rewrite makes a runtime-target alias, whose marker is refused at
    /// the declaration (<see cref="ReportOutputSpreadMarkerOnAlias"/>). That report is the one diagnostic of the one
    /// problem, so none is added here: such a program has a front-end error and never runs.</para>
    /// </summary>
    private static void ReportOutputSpreadReferenceNeedsCall(Expr reference, SignatureMap paramMap, ResolverWalkMemos memos)
    {
        if (memos.Diagnostics is not { } diagnostics
            || !(memos.OutputSpreadReferenceReports ??= new(ReferenceEqualityComparer.Instance)).Add(reference))
            return;
        if (HasRefusedReferenceMarker(reference, paramMap, memos.Run)
            || TryResolveCallable(reference, paramMap, memos, out _) is { } endpoint && IsRuntimeTargetEndpoint(endpoint, memos.Run))
            return;

        var written = ExprNameRenderer.Render(reference, ExprNameMode.Open);
        var declared = MarkedDeclarationOf(reference, paramMap, memos.Run)?.DeclarationName is { } name ? ExprNameRenderer.BoundName(name) : written;
        var message = DiagnosticMessage.JoinLines(
            (string.Equals(declared, written, StringComparison.Ordinal)
                ? $"`{written}` is declared with `*`"
                : $"`{written}` is `{declared}`, which is declared with `*`")
                + $", and only parameter inference decides whether `{written}` is called here, which also decides how the later arguments are treated.",
            $"Write `{written}(…)` to call it (its result is spread), or `{{ {written} }}` to read it without arguments as one value.");
        var span = reference.Span ?? memos.Run.ImportSite;
        diagnostics.Add(new Diagnostic(message, DiagnosticSeverity.Error, span) { Code = DiagnosticCode.OutputSpreadReferenceNeedsCall });
        memos.BranchDiagnosticTemplates?.Add(new BranchDiagnosticTemplate(DiagnosticCode.OutputSpreadReferenceNeedsCall, _ => message, span));
    }

    /// <summary>The route of a dot edge as parameter detection stamped it (never a verdict this pass refines).</summary>
    private static DotEdgeKind StampedEdgeKind(Expr.DotCall edge)
        => FormulaLiftingRoles.EdgeKind(edge, edge.EffectiveMissSelection());

    /// <summary>
    /// The marker of the declaration the call <paramref name="call"/> statically invokes, or null when it is no eligible
    /// call (R1, R3): the callee is read as the resolver reads every static callee (<see cref="ResolveStaticCallable"/>'s
    /// first step — the region's signature map, the prelude, the level's written opens, a structural member path), then
    /// followed to its STRUCTURAL identity by the static receiver reading (<see cref="ReadDeclaration"/>, Q3's target walk):
    /// the endpoint a transparent reference denotes, a carrier itself, and no static identity for a runtime reference. An
    /// <c>.Algorithm</c> link is never one, whatever its selected class (the reading before selection: both phases agree).
    /// A prelude or registry member is never marked.
    /// </summary>
    private static OutputSpreadMarker? MarkedCalleeOf(Expr call, SignatureMap paramMap, ResolutionRun run)
    {
        if (!run.StructuralOperation.AdmittedWithOutputSpreadMarkers)
            return null;

        var callee = call switch
        {
            Expr.Call { Function: var function } => function.UnwrapGraceOperand(),
            Expr.DotCall edge => StampedEdgeKind(edge) switch
            {
                // `Path.N(args)` invokes the member; an argumentless structural edge is a READ of it.
                DotEdgeKind.StructuralMember => edge.Args is null ? null : edge with { Args = null },
                // `x.N(args)` and `x.N` ARE the call `N(x, args)` (DOT-03).
                DotEdgeKind.Fallback => edge.EffectiveLexicalFallback.UnwrapGraceOperand(),
                // An intrinsic, or a member a runtime receiver decides: no static callee.
                _ => null,
            },
            _ => null,
        };
        return callee is null ? null : MarkedDeclarationOf(callee, paramMap, run);
    }

    /// <summary>
    /// The marker of the declaration the callee <paramref name="callee"/> — a name, or an argumentless structural member
    /// path — denotes (<see cref="MarkedCalleeOf"/>'s second step): the callee of a written call, and the bare reference
    /// formula lifting turns into one (its lifted call names the same callee).
    /// </summary>
    private static OutputSpreadMarker? MarkedDeclarationOf(Expr callee, SignatureMap paramMap, ResolutionRun run)
    {
        if (!run.StructuralOperation.AdmittedWithOutputSpreadMarkers)
            return null;

        if (OutputSpreadDeclarationOf(callee, paramMap, run) is not { } start)
            return null;

        var reading = ReadDeclaration(start, run, selectedLinks: false);
        return reading.Kind == ReceiverReadingKind.Structure ? reading.Structure!.OutputSpread : null;
    }

    /// <summary>The written declaration selected before Q3 follows transparent references to its marked structure.</summary>
    private static StaticDeclaration? OutputSpreadDeclarationOf(Expr callee, SignatureMap paramMap, ResolutionRun run)
        => callee switch
        {
            Expr.Resolve(var name) => paramMap.TryGetValue(name, out var entry)
                ? EntryDeclaration(entry, raw: true)
                : run.Prelude.TryGetMember(name, out _)
                    ? null
                    : StaticOpenedDeclaration(name, run.Level),
            Expr.DotCall { Args: null } path when StampedEdgeKind(path) == DotEdgeKind.StructuralMember
                => StructuralMemberAt(path, run.Level, StaticCycleCheck.Formation),
            _ => null,
        };

    /// <summary>
    /// A marker on a transparent reference is refused at the declaration. Read Q3's existing structural endpoint,
    /// without a new chase or signature selection: only a reference changes that contextual identity. This guard changes
    /// diagnostics of an already erroneous program only; spread insertion and argument roles still read the same marker.
    /// </summary>
    private static bool HasRefusedReferenceMarker(Expr reference, SignatureMap paramMap, ResolutionRun run)
    {
        if (OutputSpreadDeclarationOf(reference, paramMap, run) is not { Target.OutputSpread: not null } start)
            return false;

        var operation = run.StructuralOperation;
        var key = operation.ContextOf(start.Level?.StaticContext?.Key ?? operation.Queries.Keys.Root, start.Target);
        var structure = operation.Read(StaticQueryKey.TargetWalk(key, StaticCycleCheck.Formation));
        return structure.Kind == StaticFactKind.Structure && structure.Scope is { } target && !ReferenceEquals(key, target);
    }

    /// <summary>
    /// R4: the marker written on a declaration the front end forms into an ALIAS — a transparent reference
    /// (<c>B* = A</c>) or a runtime-target alias — is <see cref="DiagnosticCode.OutputSpreadMarkerOnAlias"/>:
    /// an alias's calls are its target's and spread exactly when the target is marked (a transparent reference
    /// inherits it through <see cref="MarkedCalleeOf"/>), and a runtime target has no static identity to
    /// spread. A structural forwarding carrier (<c>B* = { A }</c>) is a declaration of its own and keeps its
    /// marker. Reported once per alias formation, at the marker (the import site inside module text).
    /// </summary>
    private static void ReportOutputSpreadMarkerOnAlias(
        Algorithm.Alias alias, string targetName, AliasTarget? target, ResolverWalkMemos memos)
    {
        if (alias.OutputSpread is not { } marker || memos.Diagnostics is not { } diagnostics)
            return;
        if (!alias.HasRuntimeTarget && !alias.IsReference)
            return;

        var name = ExprNameRenderer.BoundName(marker.DeclarationName);
        var message = alias.HasRuntimeTarget
            ? DiagnosticMessage.JoinLines(
                $"'{name}' is a runtime-target alias, so it cannot carry the output-spreading marker `*`: the callable it calls is known only at run time, "
                    + "and only a call the front end resolves statically to a marked declaration is spread.",
                "Declare a marked algorithm with explicit parameters that calls it instead.")
            : DiagnosticMessage.JoinLines(
                $"'{name}' is an alias of '{ExprNameRenderer.BoundName(targetName)}', so it cannot carry the output-spreading marker `*`: "
                    + $"calls through an alias are calls of '{ExprNameRenderer.BoundName(targetName)}', and they spread exactly when it is marked.",
                $"To spread the output of calls to '{name}' itself, declare a marked wrapper: `{MarkedWrapperSuggestion(name, targetName, target)}`.");
        ReportOutputSpreadMarkerError(marker, message, memos, diagnostics);
    }

    /// <summary>
    /// R3/R4: the marker written on an <c>.Algorithm</c> link body that inference and lifting leave a CALCULATION
    /// (<c>A* = Mk.Algorithm</c> with <c>Mk(t)</c>, so <c>A(t)</c>) — the runtime-reference class is the runtime-target alias
    /// report — is <see cref="DiagnosticCode.OutputSpreadMarkerOnAlias"/>: a call through a link is never spread, because the
    /// algorithm it calls is known only at run time. Read from the written body: an unbraced lone row that is the link.
    /// </summary>
    private static void ReportOutputSpreadMarkerOnLink(Algorithm.User written, ResolverWalkMemos memos)
    {
        if (written.OutputSpread is not { } marker
            || memos.Diagnostics is not { } diagnostics
            || !IsUnbracedLoneRowBody(written)
            || written.Output[0] is not Expr.DotCall { Args: null } link
            || !link.UsesDotAlgorithmIntrinsic())
            return;

        var name = ExprNameRenderer.BoundName(marker.DeclarationName);
        ReportOutputSpreadMarkerError(marker, DiagnosticMessage.JoinLines(
            $"'{name}' is an `.Algorithm` link, so it cannot carry the output-spreading marker `*`: the algorithm a link calls is known only at run time, "
                + "and only a call the front end resolves statically to a marked declaration is spread.",
            "Declare a marked algorithm with explicit parameters that calls it instead."), memos, diagnostics);
    }

    private static void ReportOutputSpreadMarkerError(OutputSpreadMarker marker, DiagnosticMessage message, ResolverWalkMemos memos, DiagnosticBag diagnostics)
    {
        var span = marker.Span ?? memos.Run.ImportSite;
        diagnostics.Add(new Diagnostic(message, DiagnosticSeverity.Error, span) { Code = DiagnosticCode.OutputSpreadMarkerOnAlias });
        memos.BranchDiagnosticTemplates?.Add(new BranchDiagnosticTemplate(DiagnosticCode.OutputSpreadMarkerOnAlias, _ => message, span));
    }

    /// <summary>
    /// The marked wrapper the alias report suggests: <c>B(x, y)* = A(x, y)</c> over the target's top-level
    /// parameters when they are plain names (a collector forwarded as <c>xs*</c>), <c>B* = A()</c> for a
    /// target with none, and a generic wording for any other head.
    /// </summary>
    private static string MarkedWrapperSuggestion(string alias, string targetName, AliasTarget? target)
    {
        var shownTarget = ExprNameRenderer.BoundName(targetName);
        if (target?.Signature.Signature is not { } signature)
            return $"{alias}(…)* = {shownTarget}(…)";
        var parameters = new List<string>(signature.ParameterPatterns.Count);
        var arguments = new List<string>(signature.ParameterPatterns.Count);
        foreach (var pattern in signature.ParameterPatterns)
        {
            if (pattern is not CaptureParameterPattern capture)
                return $"{alias}(…)* = {shownTarget}(…)";
            var parameterName = ExprNameRenderer.BoundName(capture.Name);
            parameters.Add(capture.Kind == ParameterKind.Collecting ? "*" + parameterName : parameterName);
            arguments.Add(capture.Kind == ParameterKind.Collecting ? parameterName + "*" : parameterName);
        }

        return parameters.Count == 0
            ? $"{alias}* = {shownTarget}()"
            : $"{alias}({string.Join(", ", parameters)})* = {shownTarget}({string.Join(", ", arguments)})";
    }
}
