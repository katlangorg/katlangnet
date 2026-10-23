using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang;

/// <summary>
/// <b>CACHE-PUB-1: explicit zero-supply invocations establish the property cache</b> (owner decision
/// October 22 2026; authoritative Lean: the <c>invoke</c> request of
/// <c>evalZeroArgPropertyAccessCounted</c>, reached from <c>evalSuppliedCallCounted</c> through
/// <c>CalleeOrigin</c> / <c>originBinding?</c>; laws in <c>lean/KatLangArityLaws/PropertyInvocationLaws.lean</c>;
/// rule: <c>docs/design/language-rules/evaluator-and-hosting.md</c> § Zero-argument property cache).
///
/// <para><b>The rule.</b> When a property's cache entry is empty, its outermost qualifying evaluation
/// owns publication, whether it is a property-style read or an explicit zero-supply invocation; the
/// owner's success establishes the entry, bare reads reuse it, and explicit invocations stay FRESH —
/// they never obtain their result from an established entry and never replace it. A qualifying
/// invocation is an ordinary call whose callee came from an identifiable property BINDING (its
/// <see cref="CalleeOrigin"/>), whose EFFECTIVE supply — after the ordinary supply formation, so an
/// explicit spread contributing no slot counts — is empty, and whose callee accepts zero supplied
/// arguments. Builtins, host operations, anonymous blocks and computed callees name no binding; a
/// parameterized runtime-callable alias names none either. A D4 terminal alias's ordinary
/// zero-parameter property view qualifies under the alias's own binding.</para>
///
/// <para><b>One mechanism.</b> Publication is the existing <see cref="ZeroArgPropertyPublications"/> law
/// (<see cref="IZeroArgPropertyResultCache.Invoke"/>): the same key a read of that binding computes,
/// the same active-owner set, the same success-only publication, the same observation hook. The
/// call sites only decide WHETHER a call qualifies, and only on the slow path a call whose written
/// arguments are all explicit spreads (or none) takes (<see cref="MayFormZeroSupply"/>): every other
/// call keeps its ordinary, unchanged dispatch. What an owning invocation publishes is its OWN
/// execution's property-level counted output (<c>valueBoundary: false</c>), never a re-evaluation;
/// the call's caller receives that same output at the ordinary call value boundary.</para>
/// </summary>
public static partial class Evaluator
{
    /// <summary>
    /// Where the callee of an ordinary call came from — the provenance a zero-supply invocation names
    /// its property binding by, read only once its supply is known to be empty
    /// (<see cref="Binding"/>). Lean: <c>CalleeOrigin</c>.
    /// <list type="bullet">
    /// <item><see cref="None"/> — no property binding;</item>
    /// <item><see cref="Written"/> — the written callee expression, resolved in the DISPATCH context (a
    /// lexical name, an argumentless member path, a parameter);</item>
    /// <item><see cref="Cell"/> — a supplied callee cell (a captured plan's canonical callee cell);</item>
    /// <item><see cref="Bound"/> — an already selected member binding (a structural member call).</item>
    /// </list>
    /// Two references, so the slow path carries it without allocating.
    /// </summary>
    internal readonly struct CalleeOrigin
    {
        // An Expr (written callee), a NeedCell (callee cell) or a Property (bound member binding).
        private readonly object? _source;
        // The declaring owner of a bound member binding.
        private readonly Algorithm? _owner;

        private CalleeOrigin(object? source, Algorithm? owner)
        {
            _source = source;
            _owner = owner;
        }

        internal static CalleeOrigin None => default;

        internal static CalleeOrigin Written(Expr callee) => new(callee, null);

        internal static CalleeOrigin Cell(NeedCell cell) => new(cell, null);

        internal static CalleeOrigin Bound(Algorithm owner, Property binding) => new(binding, owner);

        /// <summary>
        /// The property binding this origin names, read in the dispatch context <paramref name="ctx"/>
        /// without evaluating anything. Lean: <c>originBinding?</c>.
        /// </summary>
        internal PropertyCallBinding? Binding(EvalCtx ctx, Algorithm callee) => _source switch
        {
            Expr written => WrittenCalleeBinding(written, ctx, throughParameter: true, callee),
            NeedCell cell => CellCalleeBinding(cell, callee),
            Property binding => PublicationBinding(_owner!, binding, ChildOfInContext(_owner!, binding.Value, ctx), ctx, callee),
            _ => null,
        };
    }

    /// <summary>
    /// The property binding a qualifying invocation publishes under: its declaring owner and binding.
    /// The owner is the same <see cref="PropertyDeclaringOwner"/> a property-style read of the binding
    /// carries — an ownerless host-built level included (CACHE-OWNER-D3) — so both reach one key.
    /// </summary>
    internal readonly record struct PropertyCallBinding(PropertyDeclaringOwner Owner, Property Binding);

    /// <summary>
    /// Whether a written argument list CAN form an empty supply: it holds no ordinary slot, only
    /// explicit spreads (or nothing). Syntax only — the effective supply is decided by the ordinary
    /// formation, after which a nonempty supply takes the ordinary dispatch.
    /// </summary>
    private static bool MayFormZeroSupply(OutputBundle args)
    {
        for (var i = 0; i < args.Count; i++)
            if (args[i] is not Expr.SequenceSpread) return false;
        return true;
    }

    /// <summary>
    /// A normalized callee whose zero-supply invocation can be a property calculation: a user algorithm
    /// or a clause family. A builtin is never one, and neither is a NATIVE OPERATION — a host operation
    /// or a built-in Math member, whose prelude binding is a synthetic wrapper whose one output row is
    /// its native dispatch (<see cref="IsNativeOperationWrapper"/>): <c>tick()</c> stays a fresh host
    /// call that establishes nothing, as every builtin call does (Lean models neither surface). An alias
    /// never reaches dispatch normalized (the ordinary safety net keeps it).
    /// </summary>
    private static bool IsPublishableCallee(Algorithm callee)
        => callee is Algorithm.Conditional || (callee is Algorithm.User user && !IsNativeOperationWrapper(user));

    /// <summary>
    /// The prelude wrapper of a host operation or a built-in Math member: a user algorithm whose ONLY
    /// output row is its <see cref="Expr.NativeCall"/> (<c>HostOperations.CreateExtendedPrelude</c>,
    /// <c>BuiltinRegistry</c>'s Math module). No written declaration has that shape.
    /// </summary>
    private static bool IsNativeOperationWrapper(Algorithm.User callee)
        => callee.Output.Count == 1 && callee.Output[0] is Expr.NativeCall;

    /// <summary>
    /// A selected binding as a publication identity. A runtime-target alias qualifies only when the
    /// already normalized callee is its D4 terminal property view; parameterized runtime targets
    /// (including collecting-only targets) remain excluded. This reads identity without another
    /// CALLABLE projection or VALUE demand. Lean: <c>publicationBinding?</c>.
    /// </summary>
    private static PropertyCallBinding? PublicationBinding(PropertyDeclaringOwner owner, Property binding, Algorithm wired, EvalCtx ctx, Algorithm callee)
    {
        if (wired is Algorithm.Alias alias)
        {
            var target = ResolveBindingAliasTarget(binding, alias, ctx, callable: false);
            if (target.IsError || (target.Value is Algorithm.Alias && DeclaresParameterizedStructure(callee))) return null;
        }

        return new PropertyCallBinding(owner, binding);
    }

    /// <summary>
    /// The property binding a WRITTEN callee names in <paramref name="caller"/> — the very identity
    /// resolution the callee law performed (the lexical lookup for a name, the structural navigation of
    /// <see cref="ResolveDotReceiver"/> for a member path; an argument-bearing member call names its
    /// argumentless path), read again without evaluating anything. A parameter names its supplied
    /// cell's binding (one hop: a transported cell keeps the argument originally written for it).
    /// Lean: <c>writtenCalleeBinding?</c> and the parameter arm of <c>originBinding?</c>.
    /// </summary>
    private static PropertyCallBinding? WrittenCalleeBinding(Expr written, EvalCtx caller, bool throughParameter, Algorithm callee)
    {
        switch (written)
        {
            case Expr.Resolve(var name):
            {
                if (caller.CallStack.Count == 0) return null;
                var resolved = LookupLexicalRaw(caller.CallStack[0], name, caller);
                // The lexical read's own declaring owner — an ownerless host level included
                // (CACHE-OWNER-D3) — so the invocation publishes under the read's key.
                return resolved.IsError
                    ? null
                    : PublicationBinding(resolved.Value.Owner, resolved.Value.Binding, resolved.Value.ResolvedAlgorithm, caller, callee);
            }
            case Expr.DotCall edge:
            {
                var receiver = ResolveDotReceiver(edge.Target, caller, out _);
                if (receiver.IsError) return null;
                var member = LookupPropBinding(receiver.Value, edge.Name, caller.Budget);
                return member is null
                    ? null
                    : PublicationBinding(receiver.Value, member, ChildOfInContext(receiver.Value, member.Value, caller), caller, callee);
            }
            case Expr.Param(var name) when throughParameter:
            {
                var activation = CapturedParameterActivation(name, caller);
                return LookupNeed(activation?.Needs ?? caller.NeedEnv, name) is { } cell ? CellCalleeBinding(cell, callee) : null;
            }
            default:
                return null;
        }
    }

    /// <summary>
    /// The property binding a supplied callee CELL names: its written source in its own caller context.
    /// Lean: <c>cellCalleeBinding?</c>.
    /// </summary>
    private static PropertyCallBinding? CellCalleeBinding(NeedCell cell, Algorithm callee)
    {
        // A supplied .Algorithm link carries the captured callee's binding through forwarding too.
        // Its CALLABLE has already succeeded, so following these retained edges neither demands
        // its receiver again nor touches the captured invocation's VALUE or supply. A successful
        // projection cannot contain a cycle (the run's ordinary demand-cycle gate rejects it).
        while (cell.Suspension is LinkSuspension { ProjectedCallee: { } projected })
            cell = projected;
        return cell.Suspension is { } suspension && cell.Source is { } source
            ? WrittenCalleeBinding(source, suspension.Caller, throughParameter: false, callee)
            : null;
    }

    /// <summary>
    /// The binding a zero-supply invocation of <paramref name="property"/> publishes under, or <c>null</c>
    /// when the invocation does not qualify: a callee that cannot accept zero supplied arguments is only
    /// its own ordinary call (Lean: the non-cacheable arm of <c>evalZeroArgPropertyAccessCounted</c>, whose
    /// calculation is that call), and an origin that names no binding publishes nothing.
    /// </summary>
    private static PropertyCallBinding? ZeroSupplyPublication(in CalleeOrigin origin, Algorithm property, EvalCtx ctx)
        => IsPublishableCallee(property) && AcceptsZeroSuppliedArguments(property) ? origin.Binding(ctx, property) : null;

    /// <summary>
    /// The cache execution of a qualifying invocation: EXACTLY the one a property-style read of the same
    /// binding presents (<see cref="GetOrEvaluateZeroArgPropertyResultCore"/>) — the declaring owner, the
    /// binding, the environment identity of the dispatch context, the run identity and the normalized
    /// callee's declaring scope — so both reach ONE key.
    /// </summary>
    private static ZeroArgPropertyExecution ZeroSupplyInvocationExecution(
        PropertyCallBinding binding, Algorithm property, EvalCtx ctx, ValEnv valEnv)
        => new(
            binding.Owner,
            binding.Binding,
            ZeroArgPropertyAccessKind.Invocation,
            BindingContextIdentity(ctx, valEnv),
            ctx.Budget)
        { DeclaringScope = property.Parent };

    private static EvalResult<ZeroArgPropertyResult> ToPropertyResult(EvalResult<CountedResult> output)
        => output.IsError
            ? output.Error
            : EvalResult<ZeroArgPropertyResult>.Ok(new ZeroArgPropertyResult(output.Value.Value, output.Value.EmittedCount));

    /// <summary>
    /// A qualifying zero-supply invocation through the ONE publication law
    /// (<see cref="IZeroArgPropertyResultCache.Invoke"/>): <paramref name="invocation"/> — the call's own
    /// fresh execution, producing the PROPERTY-LEVEL counted output (<see cref="ToPropertyResult"/>) —
    /// always runs; an owning success on an empty entry establishes it. The caller receives that output
    /// at the call's value boundary.
    /// </summary>
    private static EvalResult<CountedResult> EvalPublishedZeroSupplyInvocation(
        PropertyCallBinding binding, Algorithm property, EvalCtx ctx, ValEnv valEnv, Func<EvalResult<ZeroArgPropertyResult>> invocation)
    {
        var published = ctx.ZeroArgPropertyResultCache.Invoke(
            ZeroSupplyInvocationExecution(binding, property, ctx, valEnv),
            invocation);
        return published.IsError
            ? published.Error
            : EvalResult<CountedResult>.Ok(ReCountValueBoundary(new CountedResult(published.Value.Value, published.Value.EmittedCount)));
    }

    /// <summary>MIRROR OF <see cref="EvalPublishedZeroSupplyInvocation"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalPublishedZeroSupplyInvocationAsync(
        PropertyCallBinding binding, Algorithm property, EvalCtx ctx, ValEnv valEnv, Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> invocation)
    {
        // As on the async read seam: the async twin family runs only over an async-capable cache, so a
        // non-async cache here is an evaluator ownership bug — fail loud, never block or bypass it.
        if (ctx.ZeroArgPropertyResultCache is not IAsyncZeroArgPropertyResultCache asyncCache)
        {
            throw new InvalidOperationException(
                "Async evaluation requires an async-capable zero-argument property result cache on the run context.");
        }

        var published = await asyncCache.InvokeAsync(
            ZeroSupplyInvocationExecution(binding, property, ctx, valEnv),
            invocation).ConfigureAwait(false);
        return published.IsError
            ? published.Error
            : EvalResult<CountedResult>.Ok(ReCountValueBoundary(new CountedResult(published.Value.Value, published.Value.EmittedCount)));
    }

    // ── The ordinary call's dispatch for a callee with an ORIGIN (the zero-supply-capable slow path) ──

    /// <summary>
    /// The written call's slow path (<see cref="EvalCallCountedExpr"/>): the origin is the written
    /// callee in the call's own context, under the call's ordinary frame. Out of line so the
    /// call-recursion frame keeps its size. Lean: <c>evalCallCountedExpr</c>'s <c>.written f ctx</c>.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalWrittenCalleeCallCounted(
        Expr func, Algorithm callee, OutputBundle args, EvalCtx ctx, ValEnv valEnv, CallDiagnosticName diagnosticName)
        => WithCallCtx(diagnosticName, ctx,
            EvalOriginCallCounted(CalleeOrigin.Written(func), callee, args, ctx, valEnv, diagnosticName));

    /// <summary>
    /// <see cref="EvalResolvedCallCounted"/> for a call whose written arguments may form an empty supply
    /// (<see cref="MayFormZeroSupply"/>) and whose callee is publishable (<see cref="IsPublishableCallee"/>):
    /// the SAME arms, charges and phases — the invocation enter, the shared-deconstruction projection,
    /// the supply formation, the binder and the body — with the one CACHE-PUB-1 decision after the supply
    /// is formed: an empty supply of a callee whose origin names a binding is that binding's qualifying
    /// invocation. Lean: <c>evalResolvedCallCounted</c> → <c>evalSuppliedCallCounted</c> with an origin.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalOriginCallCounted(
        CalleeOrigin origin, Algorithm callee, OutputBundle args, EvalCtx ctx, ValEnv valEnv, CallDiagnosticName name)
    {
        if (TryGetFlatBinderUserEquivalent(callee) is { } simpleCallee)
            return EvalOriginUserCallCounted(origin, callee, simpleCallee, args, ctx, valEnv, name);
        return callee is Algorithm.Conditional
            ? EvalOriginFamilyCallCounted(origin, callee, args, ctx, valEnv, name)
            : EvalOriginUserCallCounted(origin, callee, callee, args, ctx, valEnv, name);
    }

    // The user arm: EvalUserCallCounted → EvalUserCallCountedCore → EvalNeedUserBodyCounted. `property` is
    // the callee as dispatched (a flat-binder family keeps its family identity for the key and its
    // family-level value boundary); `callee` is what binds.
    private static EvalResult<CountedResult> EvalOriginUserCallCounted(
        CalleeOrigin origin, Algorithm property, Algorithm callee, OutputBundle args, EvalCtx ctx, ValEnv valEnv, CallDiagnosticName name)
    {
        if (TryEnterDynamicInvocation(ctx, UserCallLimitSpan(args), out var level) is { } limitError)
            return limitError;

        using (level)
        {
            if (callee is Algorithm.User { AssignmentDeconstructionTarget: { } target } helper
                && TryProjectSharedDeconstructionTarget(helper, target, args, ctx, valEnv) is { } projected)
                return projected.IsError ? projected.Error : EvalResult<CountedResult>.Ok(new(projected.Value, projected.Value.ValueCount()));
            var occurrences = MetaOccurrenceSlots(callee, args, ctx, out var sources);
            var supply = FormNeedSupply(args, ctx, valEnv, asynchronous: false, sources).GetAwaiter().GetResult();
            if (supply.IsError) return supply.Error;
            if (supply.Value.Count == 0 && ZeroSupplyPublication(origin, property, ctx) is { } binding)
            {
                var cells = supply.Value;
                // A family's own result is already its value boundary, as its property read's is.
                var familyBoundary = property is Algorithm.Conditional;
                return EvalPublishedZeroSupplyInvocation(binding, property, ctx, valEnv,
                    () => ToPropertyResult(EvalNeedUserSupplyCounted(callee, cells, ctx, valEnv, name, variadicArityStyle: true,
                        occurrences, valueBoundary: familyBoundary)));
            }

            return EvalNeedUserSupplyCounted(callee, supply.Value, ctx, valEnv, name, variadicArityStyle: true, occurrences);
        }
    }

    // The family arm: EvalConditionalCallCounted → EvalNeedFamilyBodyCounted.
    private static EvalResult<CountedResult> EvalOriginFamilyCallCounted(
        CalleeOrigin origin, Algorithm callee, OutputBundle args, EvalCtx ctx, ValEnv valEnv, CallDiagnosticName name)
    {
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return AtFirstSpanIfMissing(limitError, args);

        try
        {
            var supply = FormNeedSupply(args, ctx, valEnv, asynchronous: false).GetAwaiter().GetResult();
            if (supply.IsError) return supply.Error;
            if (supply.Value.Count == 0 && ZeroSupplyPublication(origin, callee, ctx) is { } binding)
            {
                var cells = supply.Value;
                return EvalPublishedZeroSupplyInvocation(binding, callee, ctx, valEnv,
                    () => ToPropertyResult(EvalNeedFamilySupplyCounted(callee, cells, ctx, valEnv, name)));
            }

            return EvalNeedFamilySupplyCounted(callee, supply.Value, ctx, valEnv, name);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    /// <summary>
    /// Bound-member slow path (<see cref="EvalDotCallCounted"/>'s member arm and the alias member arm):
    /// the origin is the selected member binding under its receiver. Out of line, as for the written call.
    /// Lean: the member arm's <c>.bound targetAlg p</c>.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<CountedResult> EvalBoundMemberCallCounted(
        Algorithm owner, Property binding, Algorithm wired, OutputBundle args, string name, EvalCtx ctx, ValEnv valEnv)
        => EvalOriginCallCounted(CalleeOrigin.Bound(owner, binding), wired, args, ctx, valEnv, CallDiagnosticName.FromKnown(name));

    // ── Async twins ──

    /// <summary>MIRROR OF <see cref="EvalOriginCallCounted"/> — keep in lock-step.</summary>
    private static ValueTask<EvalResult<CountedResult>> EvalOriginCallCountedAsync(
        CalleeOrigin origin, Algorithm callee, OutputBundle args, EvalCtx ctx, ValEnv valEnv, CallDiagnosticName name)
    {
        if (TryGetFlatBinderUserEquivalent(callee) is { } simpleCallee)
            return EvalOriginUserCallCountedAsync(origin, callee, simpleCallee, args, ctx, valEnv, name);
        return callee is Algorithm.Conditional
            ? EvalOriginFamilyCallCountedAsync(origin, callee, args, ctx, valEnv, name)
            : EvalOriginUserCallCountedAsync(origin, callee, callee, args, ctx, valEnv, name);
    }

    /// <summary>MIRROR OF <see cref="EvalOriginUserCallCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalOriginUserCallCountedAsync(
        CalleeOrigin origin, Algorithm property, Algorithm callee, OutputBundle args, EvalCtx ctx, ValEnv valEnv, CallDiagnosticName name)
    {
        if (TryEnterDynamicInvocation(ctx, UserCallLimitSpan(args), out var level) is { } limitError)
            return limitError;

        using (level)
        {
            if (callee is Algorithm.User { AssignmentDeconstructionTarget: { } target } helper
                && await TryProjectSharedDeconstructionTargetAsync(helper, target, args, ctx, valEnv).ConfigureAwait(false) is { } projected)
                return projected.IsError ? projected.Error : EvalResult<CountedResult>.Ok(new(projected.Value, projected.Value.ValueCount()));
            var occurrences = MetaOccurrenceSlots(callee, args, ctx, out var sources);
            var supply = await FormNeedSupply(args, ctx, valEnv, asynchronous: true, sources).ConfigureAwait(false);
            if (supply.IsError) return supply.Error;
            if (supply.Value.Count == 0 && ZeroSupplyPublication(origin, property, ctx) is { } binding)
            {
                var cells = supply.Value;
                var familyBoundary = property is Algorithm.Conditional;
                return await EvalPublishedZeroSupplyInvocationAsync(binding, property, ctx, valEnv,
                    async () => ToPropertyResult(await EvalNeedUserSupply(callee, cells, ctx, valEnv, name, asynchronous: true,
                        variadicArityStyle: true, occurrences, valueBoundary: familyBoundary).ConfigureAwait(false))).ConfigureAwait(false);
            }

            return await EvalNeedUserSupply(callee, supply.Value, ctx, valEnv, name, asynchronous: true, variadicArityStyle: true,
                occurrences).ConfigureAwait(false);
        }
    }

    /// <summary>MIRROR OF <see cref="EvalOriginFamilyCallCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalOriginFamilyCallCountedAsync(
        CalleeOrigin origin, Algorithm callee, OutputBundle args, EvalCtx ctx, ValEnv valEnv, CallDiagnosticName name)
    {
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return AtFirstSpanIfMissing(limitError, args);

        try
        {
            var supply = await FormNeedSupply(args, ctx, valEnv, asynchronous: true).ConfigureAwait(false);
            if (supply.IsError) return supply.Error;
            if (supply.Value.Count == 0 && ZeroSupplyPublication(origin, callee, ctx) is { } binding)
            {
                var cells = supply.Value;
                return await EvalPublishedZeroSupplyInvocationAsync(binding, callee, ctx, valEnv,
                    async () => ToPropertyResult(await EvalNeedFamilySupply(callee, cells, ctx, valEnv, name, asynchronous: true)
                        .ConfigureAwait(false))).ConfigureAwait(false);
            }

            return await EvalNeedFamilySupply(callee, supply.Value, ctx, valEnv, name, asynchronous: true).ConfigureAwait(false);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }
}
