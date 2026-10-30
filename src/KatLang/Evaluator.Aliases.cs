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
    ///   <item>a RUNTIME step (<see cref="IsRuntimeAliasStep"/>) ends a chase that projects no runtime step of
    ///   its own (VALUE, static structure) AT the runtime-target alias, before its binding cell is touched; a projecting
    ///   chase projects the alias's ONE binding cell (<see cref="AliasBindingCell"/>): an identity
    ///   continues the chase AT ANY ARITY (L-RUN), absence ends it as a VALUE VIEW, and a projection
    ///   FAILURE propagates with its kind (never absence);</item>
    ///   <item>a STATIC step resolves the written target in the alias's own scope
    ///   (<see cref="ResolveAliasStep"/>): a name by the ownership-first lookup, RAW, so a target that is
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
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<AliasChaseEnd> ChaseAlias(
        Algorithm.Alias alias,
        EvalCtx ctx,
        AliasChase chase,
        Property? binding = null,
        HashSet<AliasChaseVisit>? outerVisited = null)
    {
        // A member path's receiver chase nests (one level per receiver): the host-stack backstop.
        if (outerVisited is not null && !RuntimeHelpers.TryEnsureSufficientExecutionStack())
            return new EvalError.EvaluationStackExhausted();

        var follow = FollowsCarriers(chase);
        var project = ProjectsRuntimeSteps(chase);
        List<(Dictionary<AliasTargetKey, AliasStaticEnd> Memo, AliasTargetKey Key)>? pending = null;
        var visited = outerVisited is null ? new HashSet<AliasChaseVisit>() : new HashSet<AliasChaseVisit>(outerVisited);
        // The STRUCTURE context the nested structure computations inherit: a structure chase's own steps; none
        // for an invocation or VALUE chase (never itself nested in a structure computation).
        var structureContext = follow ? null : visited;
        Algorithm current = alias;
        Property? memoBinding = binding;
        PropertyCallBinding? last = null;
        var projected = false;
        while (current is Algorithm.Alias step)
        {
            // STRUCTURE and the static structure stop at a structural carrier: its own identity.
            if (!follow && !step.IsReference)
                break;

            // A binding's memoized static end; a miss queues the binding for this chase's end.
            if (!projected && memoBinding is not null)
            {
                var known = ReadAliasTargetMemo(memoBinding, step, ctx, follow, ref pending);
                memoBinding = null;
                if (known is { } end && !ReferenceEquals(end.End, step))
                {
                    current = end.End;
                    last = end.Last ?? last;
                    continue;
                }
            }

            if (!visited.Add(AliasChaseVisit.Of(step)))
                return AliasCycleError(step);

            if (IsRuntimeAliasStep(step, ctx, structureContext))
            {
                PublishAliasTargetMemo(ref pending, new AliasStaticEnd(step, last));
                if (!project)
                    return EvalResult<AliasChaseEnd>.Ok(new AliasChaseEnd(AliasChaseEndKind.Runtime, step, last));
                var projection = AliasBindingCell(step, ctx).ProjectCallable();
                if (projection.IsError)
                    return projection.Error;
                if (projection.Value is not { } identity)
                    return EvalResult<AliasChaseEnd>.Ok(new AliasChaseEnd(AliasChaseEndKind.ValueView, step, null));
                projected = true;
                current = identity;
                last = null;
                continue;
            }

            var next = ResolveAliasStep(step, ctx, structureContext, out var hop);
            if (next.IsError)
                return next.Error;
            current = next.Value;
            last = hop;
            memoBinding = hop?.Binding;
        }

        PublishAliasTargetMemo(ref pending, new AliasStaticEnd(current, last));
        return EvalResult<AliasChaseEnd>.Ok(new AliasChaseEnd(AliasChaseEndKind.Identity, current, last));
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
        Algorithm.Alias alias, EvalCtx ctx, Property? binding = null, HashSet<AliasChaseVisit>? outerVisited = null)
    {
        var end = ChaseAlias(alias, ctx, AliasChase.Structure, binding, outerVisited);
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

    /// <summary>
    /// Whether the alias <paramref name="step"/> takes a RUNTIME step (META-S3-2): its target is a runtime
    /// row (<see cref="AliasTargetRows.IsRuntimeRow"/>) and — for an <c>.Algorithm</c> link whose receiver
    /// is not a parameter — the edge takes the intrinsic route in the alias's own scope, decided
    /// member-first exactly as the dot route decides it (<see cref="IsAlgorithmIntrinsicRoute"/>); a
    /// receiver that declares a member <c>Algorithm</c> is an ordinary static step. A parameter-headed row
    /// is runtime without navigating. The receiver's STRUCTURE is read within the ASKING chase's
    /// <paramref name="structureContext"/> (ALIAS-UNIFY-1; <see cref="ChaseAlias"/>): a receiver leading
    /// back into a structure computation in progress (<c>A = A.Algorithm</c>; <c>A = B.Algorithm</c> with
    /// <c>B = A</c>) is a cycle inside the decision — a route failure, hence a runtime step, whose
    /// projection then re-enters its own flight (<see cref="EvalError.DemandCycle"/>, NEED-09) — never an
    /// unbounded re-entry of the decision. Lean: <c>aliasStepIsRuntime</c>.
    /// </summary>
    private static bool IsRuntimeAliasStep(Algorithm.Alias step, EvalCtx ctx, HashSet<AliasChaseVisit>? structureContext)
    {
        if (!AliasTargetRows.IsRuntimeRow(step.Target))
            return false;
        if (step.Target is not Expr.DotCall edge || HasParameterHead(edge))
            return true;
        var route = IsAlgorithmIntrinsicRoute(edge, ctx.Push(step), structureContext ?? new HashSet<AliasChaseVisit>());
        return route.IsError || route.Value;
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
    /// One STATIC STEP of <see cref="ChaseAlias"/> (Lean <c>resolveAliasStepWith</c>): the binding the
    /// alias <paramref name="step"/>'s written target selects in the alias's OWN scope — the alias pushed
    /// as the head — with its owner and declaration (<paramref name="hop"/>, the terminal binding a bare
    /// read and a publication origin of the chain use): a name by the ownership-first lexical lookup, RAW;
    /// a member path by structural navigation of DECLARED members (<see cref="ResolveAliasStepPath"/>), each
    /// receiver's structure read within the chase's <paramref name="structureContext"/>.
    /// </summary>
    private static EvalResult<Algorithm> ResolveAliasStep(
        Algorithm.Alias step, EvalCtx ctx, HashSet<AliasChaseVisit>? structureContext, out PropertyCallBinding? hop)
    {
        hop = null;
        var stepCtx = ctx.Push(step);
        switch (step.Target)
        {
            case Expr.Resolve(var name):
            {
                var resolved = LookupLexicalRaw(step, name, stepCtx);
                if (resolved.IsError)
                    return AtSpanIfMissing(resolved.Error, step.Target.Span);
                hop = new PropertyCallBinding(resolved.Value.Owner, resolved.Value.Binding);
                return EvalResult<Algorithm>.Ok(resolved.Value.ResolvedAlgorithm);
            }

            case Expr.DotCall { Args: null } edge:
                return ResolveAliasStepPath(step, edge, stepCtx, structureContext, out hop);

            default:
                return NotAStaticAliasTarget(step);
        }
    }

    /// <summary>
    /// The member steps of a static alias path (Lean <c>Expr.staticAliasPath?</c> with
    /// <c>aliasStepNavigateWith</c>): a name or block head, then each DECLARED member of the previous
    /// receiver read through its STATIC structure (a transparent reference is its target's, a carrier its
    /// own, a runtime reference has none — nothing is projected), wired to it and checked for
    /// accessibility from the alias's site; a member declared only in branches is the local-only error,
    /// and a missing member or a receiver without static structure has no callable: the path is not a
    /// static alias target (only a host-built tree has one — the surface pass forms an alias over a
    /// statically known member only).
    /// </summary>
    private static EvalResult<Algorithm> ResolveAliasStepPath(
        Algorithm.Alias step, Expr.DotCall path, EvalCtx stepCtx, HashSet<AliasChaseVisit>? structureContext, out PropertyCallBinding? hop)
    {
        hop = null;
        var edges = new List<Expr.DotCall>();
        Expr head = path;
        while (head is Expr.DotCall { Args: null } edge)
        {
            edges.Add(edge);
            head = edge.Target;
        }
        edges.Reverse();

        Algorithm value;
        switch (head)
        {
            case Expr.Resolve(var name):
            {
                var resolved = LookupLexicalRaw(step, name, stepCtx);
                if (resolved.IsError)
                    return AtSpanIfMissing(resolved.Error, head.Span ?? step.Target.Span);
                value = resolved.Value.ResolvedAlgorithm;
                hop = new PropertyCallBinding(resolved.Value.Owner, resolved.Value.Binding);
                break;
            }

            case Expr.AlgorithmExpr(var block):
                value = WireToCaller(stepCtx, block);
                break;

            default:
                return NotAStaticAliasTarget(step);
        }

        foreach (var edge in edges)
        {
            var structure = value is Algorithm.Alias receiverAlias
                ? ChaseAlias(receiverAlias, stepCtx, AliasChase.StaticStructure, outerVisited: structureContext ??= new HashSet<AliasChaseVisit>())
                : EvalResult<AliasChaseEnd>.Ok(new AliasChaseEnd(AliasChaseEndKind.Identity, value, null));
            if (structure.IsError)
                return structure.Error;
            if (structure.Value.Kind != AliasChaseEndKind.Identity)
                return NotAStaticAliasTarget(step);

            var receiver = structure.Value.Algorithm;
            var member = LookupPropBinding(receiver, edge.Name, stepCtx.Budget);
            if (member is null)
            {
                return receiver.DefinesConditionalBranchProperty(edge.Name)
                    ? new EvalError.LocalOnlyProperty(OpenExprName(edge.Target), edge.Name, PropertyExposure.LocalOnlyConditionalAlgorithm)
                    { Span = edge.Span }
                    : NotAStaticAliasTarget(step);
            }

            if (!IsAccessibleFrom(member, receiver, stepCtx))
                return LocalOnlyPropertyError(OpenExprName(edge.Target), member) with { Span = edge.Span };

            value = ChildOfInContext(receiver, member.Value, stepCtx);
            hop = new PropertyCallBinding(receiver, member);
        }

        return EvalResult<Algorithm>.Ok(value);
    }

    private static EvalError AliasCycleError(Algorithm.Alias step)
        => new EvalError.IllegalInEval(AliasCycleMessage) { Span = step.Target.Span };

    private static EvalError NotAStaticAliasTarget(Algorithm.Alias step)
        => new EvalError.IllegalInEval(AliasTargetNotStaticPathMessage(step.Target)) { Span = step.Target.Span };

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
        return terminal.CrossesCarrier ? NestMissingOutput(read) : read;
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
        return resolved.CrossesCarrier ? NestMissingOutput(read) : read;
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
                return terminal.CrossesCarrier ? NestMissingOutput(runtimeRead) : runtimeRead;
            }
            PropertyDeclaringOwner owner = terminal.Binding is { } hop ? hop.Owner : targetAlg;
            var binding = terminal.Binding is { } bound ? bound.Binding : prop;
            var memberRead = EvalAliasMemberRead(owner, binding, terminal.Algorithm, name, ctx, valEnv);
            return terminal.CrossesCarrier ? NestMissingOutput(memberRead) : memberRead;
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
    /// <paramref name="routeVisited"/> is an alias step's route decision's chase set (<see cref="IsRuntimeAliasStep"/>).
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<Algorithm> ResolveReceiverHead(Expr target, EvalCtx ctx, HashSet<AliasChaseVisit>? routeVisited = null)
    {
        switch (target)
        {
            case Expr.Resolve(var name):
            {
                if (ctx.CallStack.Count == 0)
                    return new EvalError.UnknownName(name) { Span = target.Span };
                var resolved = ProjectRawLookup(LookupLexicalRaw(ctx.CallStack[0], name, ctx), target.Span);
                return resolved.IsError ? resolved : ReceiverStructure(resolved.Value, target, ctx, routeVisited);
            }

            case Expr.AlgorithmExpr(var block):
                return ReceiverStructure(WireToCaller(ctx, block), target, ctx, routeVisited);

            default:
                return ResolveAlg(target, ctx);
        }
    }

    // A receiver's STRUCTURE: the receiver itself unless it is an alias; a value-only runtime reference
    // is an absent identity (an ordinary dot result).
    private static EvalResult<Algorithm> ReceiverStructure(Algorithm receiver, Expr written, EvalCtx ctx, HashSet<AliasChaseVisit>? routeVisited = null)
    {
        if (receiver is not Algorithm.Alias alias)
            return EvalResult<Algorithm>.Ok(receiver);
        var structure = ResolveAliasStructure(alias, ctx, binding: null, routeVisited);
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
    // one through a route decision (`IsRuntimeAliasStep`) whose receiver is read through its structure —
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
        return terminal.CrossesCarrier ? NestMissingOutput(read) : read;
    }

    /// <summary>MIRROR OF <see cref="ReadValueBindingCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> ReadValueBindingCountedAsync(ResolvedLexicalProperty resolved, EvalCtx ctx, ValEnv valEnv)
    {
        var read = resolved.ResolvedAlgorithm is Algorithm.Alias runtime
            ? await EvalRuntimeAliasValueCountedAsync(runtime, ctx, valEnv).ConfigureAwait(false)
            : await EvalZeroArgPropertyAccessCountedAsync(resolved, ctx, valEnv).ConfigureAwait(false);
        return resolved.CrossesCarrier ? NestMissingOutput(read) : read;
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
                return terminal.CrossesCarrier ? NestMissingOutput(runtimeRead) : runtimeRead;
            }
            PropertyDeclaringOwner owner = terminal.Binding is { } hop ? hop.Owner : targetAlg;
            var binding = terminal.Binding is { } bound ? bound.Binding : prop;
            var memberRead = await EvalAliasMemberReadAsync(owner, binding, terminal.Algorithm, name, ctx, valEnv).ConfigureAwait(false);
            return terminal.CrossesCarrier ? NestMissingOutput(memberRead) : memberRead;
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
