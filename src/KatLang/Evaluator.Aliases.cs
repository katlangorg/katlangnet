using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang;

/// <summary>
/// CALLABLE ALIASES (FWD-02, binding indirection; decided October 1 2026). An
/// <see cref="Algorithm.Alias"/> is a BINDING whose callable is the one its written target
/// resolves to in the alias's OWN scope. The evaluator keeps the two identities apart:
/// <list type="bullet">
///   <item>the BINDING is the alias's own — a property read <c>A</c> is keyed by the alias's own
///   property in the zero-argument cache (<see cref="ResolvedLexicalProperty.Binding"/>), and written
///   member access <c>A.K</c> navigates the alias's own declarations (<see cref="ResolveDotReceiver"/>
///   resolves a written receiver RAW);</item>
///   <item>the CALLABLE is the target's — every place a binding becomes a callable normalizes the
///   alias to its target (<see cref="ResolveAliasTarget"/>): lexical lookup
///   (<see cref="LookupLexical"/>), a structurally navigated member, an inline block, and a top-level
///   property read. Calls, callbacks and loop steps, the callable channel of an argument, value
///   demands, builtin adapters, clause dispatch and Math and host wrappers therefore all receive the
///   target itself, and an alias is never an invocation: it charges no step and no depth.</item>
/// </list>
/// Every alias branch lives OUT OF LINE (no alias local in a calibrated recursive frame): the
/// recursive dispatch frames only test the variant and delegate here.
/// </summary>
public static partial class Evaluator
{
    /// <summary>
    /// THE ONE NORMALIZATION: <c>ResolveCallable(A) = A is an alias ? ResolveCallable(target of A,
    /// resolved in A's own scope) : A</c>. Iterative — an alias chain never grows the host stack — and
    /// each step resolves the alias's written target exactly where the alias's body would be
    /// evaluated (the alias pushed as the head): a name by the ownership-first lexical lookup, a dotted
    /// path by structural receiver navigation, so a member reached is the declared member and a target
    /// that is itself an alias continues the chase.
    /// <para><b>Runtime steps (META-S3-2).</b> A RUNTIME-TARGET ALIAS (its target a runtime row,
    /// <see cref="AliasTargetRows.IsRuntimeRow"/>) has no static step: its identity is the CALLABLE
    /// projection of its ONE binding cell in its declaring activation (<see cref="AliasBindingCell"/>).
    /// The chase has three outcomes: an ELIGIBLE callable (one that declares parameterized callable
    /// structure — FWD-02's own test, applied to the identity the run supplies), a TERMINAL ordinary
    /// property (absence, a value, a zero-parameter property: the alias's own property view
    /// <see cref="Algorithm.User(Algorithm.Alias)"/>, never the unresolved alias again, so no consumer
    /// redispatches it), or the projection's FAILURE with its provenance (never absence).
    /// <paramref name="callable"/> <c>false</c> is the VALUE chase: static steps only, ending AT the
    /// first runtime-target alias, whose bare read is its binding cell's VALUE — a VALUE read never
    /// initiates a CALLABLE projection.</para>
    /// <para>NORMALIZED ONCE: every alias BINDING the static chase passes through — <paramref name="binding"/>
    /// itself and each named link — remembers the chain's STATIC end (a non-alias target, or the
    /// runtime-target alias the chase stops at) under its <see cref="AliasTargetKey"/>, so a chain is
    /// chased once per declaring scope (and activation), and a later normalization of any of its links
    /// is one lookup; the runtime identity beyond it is the binding cell's own sticky outcome. Only a
    /// successful chase is remembered.</para>
    /// <para>A step reaching an alias declaration the chase has already visited IN THE SAME RESOLVING
    /// SCOPE is an alias CYCLE: <see cref="EvalError.IllegalInEval"/>, never a hop limit and never a
    /// stack overflow. A static cycle only a host-built tree can form (the pre-evaluation gate rejects
    /// every static one); a COMPLETED runtime projection that leads back into its own chain is the same
    /// explicit cycle, while an ACTIVE one re-entered is the wait-for graph's
    /// <see cref="EvalError.DemandCycle"/> (NEED-09). (A declaration shared by two scopes of a host DAG
    /// may legitimately be reached twice, once per scope.)</para>
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<Algorithm> ResolveAliasTarget(Algorithm.Alias alias, EvalCtx ctx, Property? binding = null, bool callable = true)
    {
        List<(Dictionary<AliasTargetKey, Algorithm> Memo, AliasTargetKey Key)>? pending = null;
        Algorithm current = binding is not null && ReadAliasTargetMemo(binding, alias, ctx, ref pending) is { } known
            ? known
            : alias;

        HashSet<(DeclarationIdentity? Declaration, Evaluation.Caching.StructuralOwnerIdentity Scope)>? visited = null;
        // The runtime-target alias whose projected identity the chase continues with: an ineligible
        // final identity is that alias's ordinary property.
        Algorithm.Alias? projectedFrom = null;
        while (current is Algorithm.Alias step)
        {
            if (!(visited ??= []).Add((step.Declaration, Evaluation.Caching.StructuralOwnerIdentity.FromScope(step.Parent))))
                return AliasCycleError(step);

            if (IsRuntimeAliasStep(step, ctx))
            {
                PublishAliasTargetMemo(ref pending, step);
                if (!callable)
                    return EvalResult<Algorithm>.Ok(step);
                var projected = AliasBindingCell(step, ctx).ProjectCallable();
                if (projected.IsError)
                    return projected.Error;
                if (projected.Value is not { } identity)
                    return EvalResult<Algorithm>.Ok(TerminalAliasProperty(step));
                projectedFrom = step;
                current = identity;
                continue;
            }

            var next = ResolveAliasStep(step, ctx, out var nextBinding);
            if (next.IsError)
                return next.Error;
            current = next.Value;
            if (projectedFrom is null
                && current is Algorithm.Alias nextAlias
                && nextBinding is not null
                && ReadAliasTargetMemo(nextBinding, nextAlias, ctx, ref pending) is { } memoized)
            {
                current = memoized;
            }
        }

        PublishAliasTargetMemo(ref pending, current);
        return projectedFrom is not null && !DeclaresParameterizedStructure(current)
            ? EvalResult<Algorithm>.Ok(TerminalAliasProperty(projectedFrom))
            : EvalResult<Algorithm>.Ok(current);
    }

    /// <summary>
    /// Whether the alias <paramref name="step"/> takes a RUNTIME step (META-S3-2): its target is a runtime
    /// row (<see cref="AliasTargetRows.IsRuntimeRow"/>) and — for an <c>.Algorithm</c> link whose receiver
    /// is not a parameter — the edge takes the intrinsic route in the alias's own scope, decided
    /// member-first exactly as the dot route decides it (<see cref="IsAlgorithmIntrinsicRoute"/>); a
    /// receiver that declares a member <c>Algorithm</c> is an ordinary static step. Identity navigation
    /// only: a parameter-headed row is runtime without navigating, so no cell is reached. Lean:
    /// <c>aliasStepIsRuntime</c>.
    /// </summary>
    private static bool IsRuntimeAliasStep(Algorithm.Alias step, EvalCtx ctx)
    {
        if (!AliasTargetRows.IsRuntimeRow(step.Target))
            return false;
        if (step.Target is not Expr.DotCall edge || HasParameterHead(edge))
            return true;
        var route = IsAlgorithmIntrinsicRoute(edge, ctx.Push(step));
        return route.IsError || route.Value;
    }

    // Records the static end of a chase under every binding it passed (a no-op once published).
    private static void PublishAliasTargetMemo(ref List<(Dictionary<AliasTargetKey, Algorithm> Memo, AliasTargetKey Key)>? pending, Algorithm staticEnd)
    {
        if (pending is null)
            return;
        foreach (var (memo, key) in pending)
            memo[key] = staticEnd;
        pending = null;
    }

    /// <summary>
    /// PARAMETERIZED CALLABLE STRUCTURE of a callable the run supplies (FWD-02 target eligibility, the
    /// front end's <c>DeclaresParameterizedStructure</c> applied at run time, META-S3-2): every builtin
    /// and clause family, and a user algorithm with at least one parameter pattern. Lean:
    /// <c>Algorithm.declaresParameterizedStructure</c>.
    /// </summary>
    private static bool DeclaresParameterizedStructure(Algorithm algorithm)
        => algorithm switch
        {
            Algorithm.Builtin or Algorithm.Conditional => true,
            Algorithm.User user => user.ParameterPatterns.Count != 0,
            Algorithm.Alias => false,
        };

    /// <summary>
    /// THE BINDING CELL of the runtime-target alias <paramref name="wired"/> (FWD-02, META-S3-2): its
    /// target row supplied in the alias's OWN declaring context — the alias entered as the head, exactly
    /// where its body is evaluated — through the ONE supply-cell constructor (<see cref="SupplyCell"/>),
    /// the construction META-S3-1's callee cell uses. A parameter row IS that parameter's own cell
    /// (NEED-01 transport, nothing allocated); an <c>.Algorithm</c> row is a link with its one receiver
    /// (CR-15); a parameter-rooted path is a runtime-projection reference cell. Every other row is
    /// established ONCE per declaration and declaring scope on the nearest activation of the declaring
    /// chain (or run-wide), first-wins, and retained: it is retry-stable (Guard B), and establishing it
    /// evaluates nothing. Its VALUE is the alias's bare read; its CALLABLE the alias's runtime identity —
    /// so eligible targets share receiver demands; D4 terminal observations claim it as <see cref="RuntimeAliasBinding"/> describes.
    /// </summary>
    internal static NeedCell AliasBindingCell(Algorithm.Alias wired, EvalCtx ctx)
        => wired.Target is Expr.Param
            ? SupplyCell(wired.Target, ctx.Push(wired), [], retained: true)
            : AliasBinding(wired, ctx).Cell;

    /// <summary>
    /// THE D4 OBSERVATION LIFETIMES OF A TERMINAL RUNTIME ALIAS (owner decision, 2026-10-19). The canonical
    /// binding cell stays sticky on both channels. Its already-performed receiver work — whichever operation
    /// performed the eligibility projection: a call, a bare read, a navigation through a parameter, a
    /// callback — belongs to the FIRST ordinary observation of the property: the bare VALUE, or the first
    /// terminal invocation, whichever comes first. A later terminal invocation evaluates the original row
    /// afresh; a bare read after a terminal invocation claimed the cell gets its own, lazily established VALUE
    /// cell that every later bare read reuses. So eligibility checking never duplicates a receiver evaluation,
    /// bare reads keep ordinary property caching, and explicit calls stay independent of one another and of
    /// the bare cache: <c>A</c>, <c>A, A</c>, <c>A()</c>, <c>A(), A()</c>, <c>A, A()</c> and <c>A(), A</c>
    /// evaluate an effectful terminal row 1, 1, 1, 2, 2 and 2 times. Lean: <c>aliasBareCell</c>,
    /// <c>claimTerminalAliasInitial</c>, <c>takeTerminalAliasInvocation</c>.
    /// </summary>
    internal sealed class RuntimeAliasBinding(NeedCell cell)
    {
        internal NeedCell Cell { get; } = cell;
        private int _initialUse; // 0 unclaimed, 1 bare VALUE, 2 terminal invocation
        private NeedCell? _bareCell;

        /// <summary>
        /// The cell a bare read of <paramref name="wired"/> demands from the reading context <paramref name="ctx"/>:
        /// the canonical cell while no terminal invocation claimed it, otherwise the one bare VALUE cell.
        /// </summary>
        internal NeedCell BareCell(Algorithm.Alias wired, EvalCtx ctx)
        {
            lock (this)
                if (_initialUse != 2) { _initialUse = 1; return Cell; }
            if (Volatile.Read(ref _bareCell) is { } known) return known;
            // The terminal call that claimed the canonical cell entered the alias's body under its own
            // binding context. The later bare observation gets an ordinary binding boundary of its own —
            // a fresh body entry from the reading context, never a copy of the claimed cell's suspension,
            // which would share that call's captured local-property caches. Lean: `aliasBareCell`
            // (`enterAlgorithmBody wired (EvalCtx.bindParameters [] ctx) []`).
            var created = SupplyCell(wired.Target, EnterAlgorithmBody(wired, WithNeedBindings(ctx, [], []), []), [], retained: true);
            return Interlocked.CompareExchange(ref _bareCell, created, null) ?? created;
        }

        internal NeedCell? TakeInitialInvocation()
        {
            lock (this)
            {
                if (_initialUse != 0) return null;
                _initialUse = 2;
                return Cell;
            }
        }
    }

    // Keep the large context out of the ordinary namespace gate's calibrated frame.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static bool AliasOpenRequiresArguments(Algorithm algorithm, in EvalCtx ctx)
    {
        var alias = (Algorithm.Alias)algorithm;
        if (alias.HasRuntimeTarget) return false;
        var target = ResolveAliasTarget(alias, ctx, callable: false);
        return target.IsError || target.Value is not Algorithm.Alias;
    }

    /// <summary>The terminal outcome of a chase: the alias's ordinary zero-parameter property, never the alias again.</summary>
    private static Algorithm.User TerminalAliasProperty(Algorithm.Alias alias) => new(alias);

    private static RuntimeAliasBinding AliasBinding(Algorithm.Alias wired, EvalCtx ctx)
    {
        var memo = AliasMemoOwner(wired) is { } activation ? activation.AliasBindingCells : ctx.Budget.AliasBindingCells;
        var key = new AliasTargetKey(wired.Declaration!, Evaluation.Caching.StructuralOwnerIdentity.FromScope(wired.Parent));
        lock (memo)
            if (memo.TryGetValue(key, out var known)) return known;
        var created = new RuntimeAliasBinding(SupplyCell(wired.Target, EnterAlgorithmBody(wired, ctx, []), [], retained: true));
        lock (memo)
        {
            if (memo.TryGetValue(key, out var raced)) return raced;
            memo.Add(key, created);
            return created;
        }
    }

    // A terminal property view has the alias's declaration, scope and ONE original row. All
    // ordinary need binders consume the same outcome, after their ordinary arity gate. This is
    // deliberately outside identity resolution: observations/retries/recognition claim nothing.
    private static NeedCell? TakeTerminalAliasInvocation(Algorithm algorithm, EvalCtx ctx)
    {
        if (!ctx.Budget.MayReachRuntimeAliases || algorithm is not Algorithm.User { ParameterPatterns.Count: 0, Output.Count: 1 })
            return null;
        var memo = AliasMemoOwner(algorithm) is { } activation ? activation.AliasBindingCells : ctx.Budget.AliasBindingCells;
        var key = new AliasTargetKey(algorithm.Declaration!, Evaluation.Caching.StructuralOwnerIdentity.FromScope(algorithm.Parent));
        RuntimeAliasBinding? binding;
        lock (memo) memo.TryGetValue(key, out binding);
        return binding?.TakeInitialInvocation();
    }


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
    /// The remembered target of the alias BINDING <paramref name="binding"/> wired as
    /// <paramref name="wired"/>, or null after queueing its key for the chase's result. The entry
    /// lives on the nearest activation of the declaring scope chain (so it is forgotten with that
    /// call), or run-wide when the chain has none.
    /// </summary>
    private static Algorithm? ReadAliasTargetMemo(
        Property binding,
        Algorithm.Alias wired,
        EvalCtx ctx,
        ref List<(Dictionary<AliasTargetKey, Algorithm> Memo, AliasTargetKey Key)>? pending)
    {
        var memo = AliasMemoOwner(wired) is { } activation ? activation.AliasTargets : ctx.Budget.AliasTargets;
        var key = new AliasTargetKey(binding, Evaluation.Caching.StructuralOwnerIdentity.FromScope(wired.Parent));
        if (memo.TryGetValue(key, out var target))
            return target;
        (pending ??= []).Add((memo, key));
        return null;
    }

    /// <summary>
    /// The memo key of an alias BINDING (a <see cref="Property"/>) or, for a runtime-alias binding cell,
    /// of an alias DECLARATION (a <see cref="DeclarationIdentity"/>, which covers inline aliases too),
    /// together with the resolving identity of the scope chain it is wired under (each level's opens and
    /// properties, by reference) — everything its target's resolution reads besides the activation,
    /// which selects the memo the key lives in. Compared by reference.
    /// </summary>
    internal readonly struct AliasTargetKey(object binding, Evaluation.Caching.StructuralOwnerIdentity scope) : IEquatable<AliasTargetKey>
    {
        private readonly object _binding = binding;
        private readonly Evaluation.Caching.StructuralOwnerIdentity _scope = scope;

        public bool Equals(AliasTargetKey other)
            => ReferenceEquals(_binding, other._binding) && _scope.Equals(other._scope);

        public override bool Equals(object? obj) => obj is AliasTargetKey other && Equals(other);

        public override int GetHashCode()
            => HashCode.Combine(RuntimeHelpers.GetHashCode(_binding), _scope.GetHashCode());
    }

    /// <summary>
    /// One step of <see cref="ResolveAliasTarget"/>: the callable the alias's written target names in
    /// its own scope, and the binding that selected it, including a declared member path.
    /// </summary>
    private static EvalResult<Algorithm> ResolveAliasStep(Algorithm.Alias step, EvalCtx ctx, out Property? binding)
    {
        binding = null;
        var stepCtx = ctx.Push(step);
        switch (step.Target)
        {
            case Expr.Resolve(var name):
            {
                var resolved = LookupLexicalRaw(step, name, stepCtx);
                if (resolved.IsError)
                    return AtSpanIfMissing(resolved.Error, step.Target.Span);
                binding = resolved.Value.Binding;
                return EvalResult<Algorithm>.Ok(resolved.Value.ResolvedAlgorithm);
            }

            case Expr.DotCall { Args: null } edge:
            {
                // A declared member path, a member named `string` included (Q-17 S-C): an edge whose
                // receiver lacks the member is a computed value, never an alias target.
                var member = ResolveDotReceiver(edge, stepCtx, out var isStructuralMember);
                if (member.IsError)
                    return AtSpanIfMissing(member.Error, step.Target.Span);
                if (isStructuralMember && member.Value is Algorithm.Alias { Parent: { } owner })
                    binding = owner.Properties.FirstOrDefault(property => property.Name == edge.Name);
                return isStructuralMember ? member : NotAStaticAliasTarget(step);
            }

            default:
                return NotAStaticAliasTarget(step);
        }
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
    /// The normalized callable of an alias BINDING wired as <paramref name="wired"/>: remembered under
    /// the binding's <see cref="AliasTargetKey"/> (see <see cref="ResolveAliasTarget"/>), so a binding
    /// read again in an equivalent scope reuses the resolved chain instead of chasing it again. Only a
    /// resolved callable is remembered; a failure is resolved (and reported) afresh. <paramref name="callable"/>
    /// <c>false</c> is the VALUE chase (see <see cref="ResolveAliasTarget"/>).
    /// </summary>
    private static EvalResult<Algorithm> ResolveBindingAliasTarget(Property binding, Algorithm.Alias wired, EvalCtx ctx, bool callable = true)
        => ResolveAliasTarget(wired, ctx, binding, callable);

    /// <summary>
    /// A lexical lookup that selected an alias binding: the BINDING stays the alias's own property
    /// (the zero-argument cache key, exposure, accessibility), the resolved algorithm becomes the
    /// alias's callable target — or, for a VALUE read (<paramref name="callable"/> <c>false</c>), the
    /// static end of its chain, which is a runtime-target alias when the chain reaches one.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<ResolvedLexicalProperty> NormalizeAliasBinding(ResolvedLexicalProperty resolved, EvalCtx ctx, bool callable = true)
    {
        var target = ResolveBindingAliasTarget(resolved.Binding, (Algorithm.Alias)resolved.ResolvedAlgorithm, ctx, callable);
        return target.IsError
            ? target.Error
            : EvalResult<ResolvedLexicalProperty>.Ok(resolved with { ResolvedAlgorithm = target.Value });
    }

    /// <summary>An inline block that is an alias (<c>{ F }</c>), wired to the caller and normalized (no binding, so not memoized).</summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<Algorithm> ResolveInlineAliasTarget(Algorithm alias, EvalCtx ctx, bool callable = true)
        => ResolveAliasTarget((Algorithm.Alias)WireToCaller(ctx, alias), ctx, callable: callable);

    /// <summary>
    /// THE BARE READ OF A RUNTIME-TARGET ALIAS (FWD-02, META-S3-2): the VALUE channel of its ONE binding
    /// cell (<see cref="AliasBindingCell"/>) — the very cell its CALLABLE projects, so a computed receiver
    /// (<c>A = Mk(5).Algorithm</c>) is shared for eligible targets; D4 bare VALUE has its own memo domain — reported as
    /// its property body reports it (a supplied cell under an alias head finishes with property-style
    /// provenance, never a written-argument slot's: <see cref="FinishSuppliedValue"/>). A parameter row is
    /// its property body's ordinary parameter read, which demands that parameter's own cell. Never a
    /// CALLABLE projection: a bare read does not initiate the runtime identity. Lean: the runtime arm of
    /// <c>aliasValue</c>.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalRuntimeAliasValueCounted(Algorithm.Alias wired, EvalCtx ctx, ValEnv valEnv)
        => wired.Target is Expr.Param
            ? EvalCounted(wired.Target, ctx.Push(wired), valEnv)
            : AliasBinding(wired, ctx).BareCell(wired, ctx).Demand();

    /// <summary>
    /// An inline block alias in VALUE position: exactly the value demand of its target — the ONE
    /// zero-argument law judged on the TARGET and reported as its written target reference reports
    /// it (<see cref="ZeroArgumentValueDemandError"/>: <c>{ Inc }</c> with <c>Inc(x)</c> is Inc's
    /// own <see cref="EvalError.ArityMismatch"/>, never the written block's
    /// <see cref="EvalError.UnresolvedImplicitParams"/>; FA-OQ-1, Option B), then the target's
    /// zero-supply demand; a chain that reaches a runtime-target alias reads that alias's binding cell
    /// (<see cref="EvalRuntimeAliasValueCounted"/>). An inline block is no property, so nothing is
    /// cached. The counterpart of <see cref="EvalAlgorithmExprValue"/>.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<Result> EvalInlineAliasValue(Expr expr, Algorithm alias, EvalCtx ctx, ValEnv valEnv)
    {
        var targetR = ResolveInlineAliasTarget(alias, ctx, callable: false);
        if (targetR.IsError)
            return AtSpanIfMissing(targetR.Error, expr.Span);

        var target = targetR.Value;
        if (target is Algorithm.Alias runtime)
            return WithSpan(expr.Span, ProjectCountedValue(EvalRuntimeAliasValueCounted(runtime, ctx, valEnv)));
        if (ZeroArgumentValueDemandError(expr, target) is { } rejection)
            return rejection;
        return WithSpan(expr.Span, EvalZeroArgumentDemandOutput(target, ctx, valEnv));
    }

    /// <summary>
    /// An inline block alias as a SPREAD operand (<c>{ F }*</c>): the same value demand as
    /// <see cref="EvalInlineAliasValue"/> — the ONE zero-argument law judged on the TARGET and
    /// reported as its written target reference reports it — whose items are spread; an operand
    /// without output is the spread-specific <see cref="EvalError.SpreadMissingOutput"/>. The
    /// counterpart of the block arm of <see cref="EvalSequenceSpreadOperandValue"/>.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<Result> EvalAliasSpreadOperandValue(Expr expr, Algorithm alias, EvalCtx ctx, ValEnv valEnv)
    {
        var targetR = ResolveInlineAliasTarget(alias, ctx, callable: false);
        if (targetR.IsError)
            return AtSpanIfMissing(targetR.Error, expr.Span);

        var target = targetR.Value;
        EvalResult<Result> blockR;
        if (target is Algorithm.Alias runtime)
            blockR = ProjectCountedValue(EvalRuntimeAliasValueCounted(runtime, ctx, valEnv));
        else
        {
            if (ZeroArgumentValueDemandError(expr, target) is { } rejection)
                return rejection;
            blockR = EvalZeroArgumentDemandOutput(target, ctx, valEnv);
        }

        if (blockR.IsError)
            return IsMissingOutputError(blockR.Error) ? SpreadMissingOutput(expr.Span) : blockR.Error;
        return blockR;
    }

    /// <summary>
    /// The dispatch safety net: a call whose callee reached dispatch as an unnormalized alias (a
    /// host-built tree) calls the alias's target with the same written arguments in the caller's
    /// context. Every binding lookup normalizes first, so front-end programs never reach this. A
    /// runtime alias's terminal property is an ordinary property callee, never this alias again.
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
    /// The demand funnel's alias arm: an alias demanded with zero arguments is its target's
    /// zero-supply demand — or, when its chain reaches a runtime-target alias, that alias's bare read
    /// (the VALUE chase never initiates a CALLABLE projection).
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalAliasZeroArgumentDemandCounted(Algorithm algorithm, EvalCtx ctx, ValEnv valEnv)
    {
        var target = ResolveAliasTarget((Algorithm.Alias)algorithm, ctx, callable: false);
        if (target.IsError) return target.Error;
        return target.Value is Algorithm.Alias runtime
            ? EvalRuntimeAliasValueCounted(runtime, ctx, valEnv)
            : EvalZeroArgumentDemandOutputCounted(target.Value, ctx, valEnv);
    }

    /// <summary>
    /// A top-level property read of an alias binding (<see cref="EvalTopLevelZeroArgPropertyCounted"/>):
    /// the static end of the binding's chain (a VALUE read), the binding itself unchanged.
    /// </summary>
    private static EvalResult<Algorithm> NormalizeTopLevelBinding(Property binding, Algorithm resolvedAlgorithm, EvalCtx ctx)
        => resolvedAlgorithm is Algorithm.Alias alias
            ? ResolveBindingAliasTarget(binding, alias, ctx, callable: false)
            : EvalResult<Algorithm>.Ok(resolvedAlgorithm);

    /// <summary>
    /// The structurally navigated member arm of <see cref="EvalDotCallCounted"/> for a member that is an
    /// alias (<c>Lib.A</c>, <c>Lib.A(args)</c>): the member's BINDING keys the zero-argument read, its
    /// normalized target is read or called — the same steps as the member arm, over the target. A read
    /// takes the VALUE chase (a runtime-target alias is read through its binding cell); a call the
    /// CALLABLE chase.
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
        var wiredR = ResolveBindingAliasTarget(prop, (Algorithm.Alias)wiredAlias, ctx, callable: argsOpt is not null);
        if (wiredR.IsError)
            return wiredR.Error;

        var wired = wiredR.Value;
        if (argsOpt is null)
            return EvalAliasMemberRead(targetAlg, prop, wired, name, ctx, valEnv);

        return EvalResolvedCallCounted(wired, argsOpt, ctx, valEnv, CallDiagnosticName.FromKnown(name));
    }

    // MIRROR OF the member arm of EvalDotCallCounted (zero-argument read), over the VALUE chase's end.
    private static EvalResult<CountedResult> EvalAliasMemberRead(
        Algorithm targetAlg, Property prop, Algorithm wired, string name, EvalCtx ctx, ValEnv valEnv)
    {
        var simpleCallee = TryGetFlatBinderUserEquivalent(wired);
        if (simpleCallee is not null)
        {
            return AcceptsZeroArgumentValueDemand(simpleCallee)
                ? MarkSelectedMemberOutput(ReCountValueBoundary(EvalZeroArgPropertyAccessCounted(targetAlg, prop, ZeroArgPropertyAccessKind.CountedStructural, simpleCallee, ctx, valEnv)))
                : ZeroArgumentDemandArityMismatch(simpleCallee);
        }

        if (AcceptsZeroArgumentValueDemand(wired))
            return MarkSelectedMemberOutput(ReCountValueBoundary(EvalZeroArgPropertyAccessCounted(targetAlg, prop, ZeroArgPropertyAccessKind.CountedStructural, wired, ctx, valEnv)));

        if (wired is Algorithm.Conditional)
            return new EvalError.NoMatchingBranch(name);

        return ZeroArgumentDemandArityMismatch(wired);
    }

    /// <summary>
    /// The <c>.string</c> intrinsic on a receiver that resolved to an alias binding (<c>A.string</c>,
    /// <c>Lib.A.string</c>): the receiver is a VALUE demand, judged on the static end of the alias's
    /// chain and read through the alias's own binding — the same steps as the intrinsic arm of
    /// <see cref="EvalDotCallCounted"/>.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalAliasDotStringCounted(
        Expr target,
        Algorithm aliasAlg,
        bool receiverIsStructuralMember,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var receiverR = ResolveAliasTarget((Algorithm.Alias)aliasAlg, ctx, callable: false);
        if (receiverR.IsError)
            return receiverR.Error;
        var val = EvalDotStringReceiverAlgOutput(target, receiverR.Value, receiverIsStructuralMember, ctx, valEnv);
        if (val.IsError) return val.Error;
        var outR = ResultToString(ctx, val.Value);
        if (outR.IsError) return outR.Error;
        return EvalResult<CountedResult>.Ok(new CountedResult(outR.Value, outR.Value.ValueCount()));
    }

    /// <summary>
    /// A written RECEIVER head (<see cref="ResolveDotReceiver"/>): a receiver is NAVIGATED, so a name or a
    /// block is the binding's own algorithm — an alias declares only its own members, never its
    /// target's (written member access never follows an alias). Every other receiver shape resolves
    /// through <see cref="ResolveAlg"/> as before.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static EvalResult<Algorithm> ResolveReceiverHead(Expr target, EvalCtx ctx)
        => target switch
        {
            Expr.Resolve(var name) => ctx.CallStack.Count == 0
                ? new EvalError.UnknownName(name) { Span = target.Span }
                : ProjectRawLookup(LookupLexicalRaw(ctx.CallStack[0], name, ctx), target.Span),
            Expr.AlgorithmExpr(var block) => EvalResult<Algorithm>.Ok(WireToCaller(ctx, block)),
            _ => ResolveAlg(target, ctx),
        };

    private static EvalResult<Algorithm> ProjectRawLookup(EvalResult<ResolvedLexicalProperty> resolved, SourceSpan? span)
        => resolved.IsError
            ? (resolved.Error.Span is null ? resolved.Error with { Span = span } : resolved.Error)
            : EvalResult<Algorithm>.Ok(resolved.Value.ResolvedAlgorithm);

    // ── Async twins ──
    // A CALLABLE chase may reach a runtime-target alias's projection, so the async family runs it
    // through the ONE asynchronous resolution adapter (ResolveAsync, META-S3-0b), which awaits the
    // binding cell's runtime projection and replays its outcome. The VALUE chase is static identity
    // navigation — it reaches no cell — and a runtime alias's bare read awaits its binding cell's VALUE.

    /// <summary>The async twin's CALLABLE chase: <see cref="ResolveAliasTarget"/> through <see cref="ResolveAsync{TState,T}"/>.</summary>
    internal static ValueTask<EvalResult<Algorithm>> ResolveAliasTargetAsync(Algorithm.Alias alias, EvalCtx ctx, Property? binding = null)
        => ResolveAsync(ctx, (alias, ctx, binding), static state => ResolveAliasTarget(state.alias, state.ctx, state.binding));

    /// <summary>MIRROR OF <see cref="EvalRuntimeAliasValueCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalRuntimeAliasValueCountedAsync(Algorithm.Alias wired, EvalCtx ctx, ValEnv valEnv)
        => wired.Target is Expr.Param
            ? await EvalCountedAsync(wired.Target, ctx.Push(wired), valEnv).ConfigureAwait(false)
            : await AliasBinding(wired, ctx).BareCell(wired, ctx).DemandAsync().ConfigureAwait(false);

    /// <summary>MIRROR OF <see cref="EvalInlineAliasValue"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> EvalInlineAliasValueAsync(Expr expr, Algorithm alias, EvalCtx ctx, ValEnv valEnv)
    {
        var targetR = ResolveInlineAliasTarget(alias, ctx, callable: false);
        if (targetR.IsError)
            return AtSpanIfMissing(targetR.Error, expr.Span);

        var target = targetR.Value;
        if (target is Algorithm.Alias runtime)
            return WithSpan(expr.Span, ProjectCountedValue(await EvalRuntimeAliasValueCountedAsync(runtime, ctx, valEnv).ConfigureAwait(false)));
        if (ZeroArgumentValueDemandError(expr, target) is { } rejection)
            return rejection;
        return WithSpan(expr.Span, await EvalZeroArgumentDemandOutputAsync(target, ctx, valEnv).ConfigureAwait(false));
    }

    /// <summary>MIRROR OF <see cref="EvalAliasSpreadOperandValue"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> EvalAliasSpreadOperandValueAsync(Expr expr, Algorithm alias, EvalCtx ctx, ValEnv valEnv)
    {
        var targetR = ResolveInlineAliasTarget(alias, ctx, callable: false);
        if (targetR.IsError)
            return AtSpanIfMissing(targetR.Error, expr.Span);

        var target = targetR.Value;
        EvalResult<Result> blockR;
        if (target is Algorithm.Alias runtime)
            blockR = ProjectCountedValue(await EvalRuntimeAliasValueCountedAsync(runtime, ctx, valEnv).ConfigureAwait(false));
        else
        {
            if (ZeroArgumentValueDemandError(expr, target) is { } rejection)
                return rejection;
            blockR = await EvalZeroArgumentDemandOutputAsync(target, ctx, valEnv).ConfigureAwait(false);
        }

        if (blockR.IsError)
            return IsMissingOutputError(blockR.Error) ? SpreadMissingOutput(expr.Span) : blockR.Error;
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
        var target = ResolveAliasTarget((Algorithm.Alias)algorithm, ctx, callable: false);
        if (target.IsError) return target.Error;
        return target.Value is Algorithm.Alias runtime
            ? await EvalRuntimeAliasValueCountedAsync(runtime, ctx, valEnv).ConfigureAwait(false)
            : await EvalZeroArgumentDemandOutputCountedAsync(target.Value, ctx, valEnv).ConfigureAwait(false);
    }

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
            var readR = ResolveBindingAliasTarget(prop, (Algorithm.Alias)wiredAlias, ctx, callable: false);
            if (readR.IsError)
                return readR.Error;
            return await EvalAliasMemberReadAsync(targetAlg, prop, readR.Value, name, ctx, valEnv).ConfigureAwait(false);
        }

        var wiredR = await ResolveAliasTargetAsync((Algorithm.Alias)wiredAlias, ctx, prop).ConfigureAwait(false);
        if (wiredR.IsError)
            return wiredR.Error;
        return await EvalResolvedCallCountedAsync(wiredR.Value, argsOpt, ctx, valEnv, CallDiagnosticName.FromKnown(name)).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalAliasMemberRead"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalAliasMemberReadAsync(
        Algorithm targetAlg, Property prop, Algorithm wired, string name, EvalCtx ctx, ValEnv valEnv)
    {
        var simpleCallee = TryGetFlatBinderUserEquivalent(wired);
        if (simpleCallee is not null)
        {
            return AcceptsZeroArgumentValueDemand(simpleCallee)
                ? MarkSelectedMemberOutput(ReCountValueBoundary(
                    await EvalZeroArgPropertyAccessCountedAsync(
                        targetAlg, prop, ZeroArgPropertyAccessKind.CountedStructural, simpleCallee, ctx, valEnv).ConfigureAwait(false)))
                : ZeroArgumentDemandArityMismatch(simpleCallee);
        }

        if (AcceptsZeroArgumentValueDemand(wired))
            return MarkSelectedMemberOutput(ReCountValueBoundary(
                await EvalZeroArgPropertyAccessCountedAsync(
                    targetAlg, prop, ZeroArgPropertyAccessKind.CountedStructural, wired, ctx, valEnv).ConfigureAwait(false)));

        if (wired is Algorithm.Conditional)
            return new EvalError.NoMatchingBranch(name);

        return ZeroArgumentDemandArityMismatch(wired);
    }

    /// <summary>MIRROR OF <see cref="EvalAliasDotStringCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalAliasDotStringCountedAsync(
        Expr target,
        Algorithm aliasAlg,
        bool receiverIsStructuralMember,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var receiverR = ResolveAliasTarget((Algorithm.Alias)aliasAlg, ctx, callable: false);
        if (receiverR.IsError)
            return receiverR.Error;
        var val = await EvalDotStringReceiverAlgOutputAsync(target, receiverR.Value, receiverIsStructuralMember, ctx, valEnv).ConfigureAwait(false);
        if (val.IsError) return val.Error;
        var outR = ResultToString(ctx, val.Value);
        if (outR.IsError) return outR.Error;
        return EvalResult<CountedResult>.Ok(new CountedResult(outR.Value, outR.Value.ValueCount()));
    }
}
