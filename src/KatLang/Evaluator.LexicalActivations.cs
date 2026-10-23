namespace KatLang;

/// <summary>
/// The parameter bindings of ONE activation of a lexical owner, captured when a call
/// enters the owner's body (<see cref="Evaluator.EnterAlgorithmBody"/>) or matches one of
/// its clauses (<c>ChildOfConditionalCall</c>): the owner's own parameter names, as bound
/// on the value tier and the need-cell tier at that moment — first binding per name,
/// exactly the tiers a captured-parameter read must see (a cell carries both the VALUE and
/// the CALLABLE channel of its parameter). Keeping the tiers together prevents a
/// shadowing caller from supplying any missing binding.
/// <para>An activation is identified by REFERENCE: two calls of one declaration are two
/// activations even when every captured value is equal (Lean: a fresh index into
/// <c>EvalState.lexicalActivations</c> per <c>recordParameterActivation</c>). It lives on
/// the activated <see cref="ScopeCtx"/> (<see cref="ScopeCtx.Activation"/>) — the head
/// scope of the entered body (<see cref="Evaluator.EvalCtx.HeadScope"/>) or the family
/// scope a selected branch body is wired under — and is runtime-only: it takes no part in
/// record equality and is not a determinant of the exported property cache key.</para>
/// </summary>
internal sealed class ParameterActivation
{
    private ParameterActivation(ValEnv values, NeedEnv needs, object valueEnvironmentIdentity)
    {
        Values = values;
        Needs = needs;
        ValueEnvironmentIdentity = valueEnvironmentIdentity;
    }

    public ValEnv Values { get; }

    internal NeedEnv Needs { get; }

    // The binding context of this activation: the fresh one an explicit call minted, or —
    // when a property-style read entered a parameterless or collecting-only owner — its
    // DECLARING activation's, never the consumer's nor the read's own empty-supply binding's
    // (CACHE-OWNER-D1, COLLECT-CACHE-1, Evaluator.DeclaringBindingIdentity).
    internal object ValueEnvironmentIdentity { get; }

    /// <summary>
    /// The normalized callable-alias targets of alias bindings declared under this activation
    /// (<see cref="Evaluator.AliasTargetKey"/>): an alias declared inside a call's body is resolved
    /// once per activation and forgotten with it. Runtime-only memoization, like the activation.
    /// </summary>
    internal Dictionary<Evaluator.AliasTargetKey, Algorithm> AliasTargets => AliasMemos;

    /// <summary>
    /// The runtime-alias BINDING CELLS of runtime-target aliases declared under this activation (FWD-02,
    /// META-S3-2; <see cref="Evaluation.EvaluationBudget.AliasBindingCells"/>): one retained cell per alias
    /// declaration and declaring scope, established on first use and forgotten with the activation.
    /// </summary>
    internal Dictionary<Evaluator.AliasTargetKey, Evaluator.RuntimeAliasBinding> AliasBindingCells => AliasMemos.BindingCells;

    // Both alias memos hang off ONE lazily created holder (published first-wins, so racing binding-cell
    // establishments meet in one dictionary): an activation that never meets an alias pays one null field.
    private AliasMemo AliasMemos
        => Volatile.Read(ref _aliasMemos)
           ?? Interlocked.CompareExchange(ref _aliasMemos, new AliasMemo(), null)
           ?? _aliasMemos!;

    private AliasMemo? _aliasMemos;

    // The alias-target memo itself, carrying the binding-cell memo created on first use.
    private sealed class AliasMemo : Dictionary<Evaluator.AliasTargetKey, Algorithm>
    {
        private Dictionary<Evaluator.AliasTargetKey, Evaluator.RuntimeAliasBinding>? _bindingCells;

        public Dictionary<Evaluator.AliasTargetKey, Evaluator.RuntimeAliasBinding> BindingCells
            => Volatile.Read(ref _bindingCells)
               ?? Interlocked.CompareExchange(ref _bindingCells, [], null)
               ?? _bindingCells!;
    }

    /// <summary>
    /// Captures the bindings of <paramref name="names"/> from the two tiers of a binding
    /// context: the value environment <paramref name="values"/> and the need-cell tier of
    /// <paramref name="ctx"/>, keeping the first binding of each owned name in environment
    /// order (Lean: <c>recordParameterActivation</c>'s two <c>filter</c>s), together with the
    /// entering context's binding identity (Lean: <c>bindingContext := ctx.bindingContext</c>):
    /// the fresh tier of the call boundary that entered the body, even when that call bound
    /// nothing (<see cref="Evaluator.BindingContextIdentity"/>) — unless a property-style read
    /// supplies the identity its owner inherits from the declaring activation
    /// (<paramref name="inheritedBindingIdentity"/>, CACHE-OWNER-D1; Lean
    /// <c>enterPropertyOwnerBody</c>).
    /// </summary>
    internal static ParameterActivation Capture(
        IReadOnlyList<string> names,
        Evaluator.EvalCtx ctx,
        ValEnv values,
        object? inheritedBindingIdentity = null)
        => new(
            FilterOwned(values, names, static binding => binding.Name),
            FilterOwned(ctx.NeedEnv, names, static binding => binding.Name),
            inheritedBindingIdentity ?? Evaluator.BindingContextIdentity(ctx, values));

    /// <summary>
    /// The bindings of <paramref name="env"/> whose names are owned, first binding per name.
    /// Parameter lists are short in every ordinary program, so a linear membership scan
    /// avoids allocating a set; a wide deconstruction signature crosses over to one.
    /// </summary>
    private static TBinding[] FilterOwned<TBinding>(
        IReadOnlyList<TBinding> env,
        IReadOnlyList<string> names,
        Func<TBinding, string> nameOf)
    {
        if (env.Count == 0 || names.Count == 0)
            return [];

        HashSet<string>? ownedSet = names.Count > Evaluator.LinearShadowNameScanLimit
            ? new HashSet<string>(names, StringComparer.Ordinal)
            : null;

        List<TBinding>? kept = null;
        for (var index = 0; index < env.Count; index++)
        {
            var binding = env[index];
            var name = nameOf(binding);
            // Removing a wide signature's name records its first binding in the same
            // hash lookup that establishes ownership. Scanning `kept` here would make
            // capturing a wide invocation quadratic even though ownership uses a set.
            var firstOwned = ownedSet is not null
                ? ownedSet.Remove(name)
                : Evaluator.ContainsOrdinal(names, name) && !AlreadyKept(kept, name, nameOf);
            if (!firstOwned)
                continue;

            (kept ??= new List<TBinding>(names.Count)).Add(binding);
        }

        return kept is null ? [] : kept.ToArray();
    }

    private static bool AlreadyKept<TBinding>(List<TBinding>? kept, string name, Func<TBinding, string> nameOf)
    {
        if (kept is null)
            return false;

        for (var index = 0; index < kept.Count; index++)
        {
            if (string.Equals(nameOf(kept[index]), name, StringComparison.Ordinal))
                return true;
        }

        return false;
    }
}

public static partial class Evaluator
{
    /// <summary>
    /// Enters an algorithm body for one call. A parameterized body gets a fresh
    /// <see cref="ParameterActivation"/> and the entered context carries the activated head
    /// scope (<see cref="EvalCtx.HeadScope"/>): the scope the body's own declaring level
    /// resolves to, the level captured-parameter reads and the accessibility law find its
    /// activation on, and the parent of every scope wired under the head. A parameterless owner with
    /// local-only properties also gets an activation, whose binding identity keys those properties:
    /// the entering context's, or — for a property-style read — the
    /// <paramref name="inheritedBindingIdentity"/> of its declaring activation (CACHE-OWNER-D1,
    /// <see cref="EvalPropertyOwnerBodyCounted"/>; a collecting-only owner's read passes the same
    /// identity after binding its empty supply, COLLECT-CACHE-1). Other parameterless bodies need no activated head
    /// scope. Lean: <c>enterAlgorithmBody</c> (<c>headScope := some (a.asScopeCtx.withActivation id)</c>)
    /// and, with an inherited identity, <c>enterPropertyOwnerBody</c>.
    /// </summary>
    internal static EvalCtx EnterAlgorithmBody(
        Algorithm algorithm,
        EvalCtx ctx,
        ValEnv values,
        IReadOnlyList<string>? parameterNames = null,
        object? inheritedBindingIdentity = null)
    {
        var names = parameterNames ?? algorithm.Params;
        if (names.Count == 0 && !HasLocalOnlyProperty(algorithm))
            return ctx.Push(algorithm);

        var headScope = new ScopeCtx(algorithm.Parent, algorithm.Opens, algorithm.Properties, names)
        {
            Owner = algorithm,
            Activation = ParameterActivation.Capture(names, ctx, values, inheritedBindingIdentity),
        };
        return ctx.Push(algorithm, headScope);
    }

    /// <summary>
    /// Whether <paramref name="algorithm"/> declares a property that is not exported: the
    /// properties whose cache identity a parameterless owner's activation retains
    /// (<see cref="EnterAlgorithmBody"/>). Indexed, so no boxed enumerator per entry.
    /// </summary>
    private static bool HasLocalOnlyProperty(Algorithm algorithm)
    {
        var properties = algorithm.Properties;
        for (var index = 0; index < properties.Count; index++)
        {
            if (properties[index].Exposure != PropertyExposure.Exported)
                return true;
        }

        return false;
    }

    /// <summary>
    /// The binding identity of the nearest ACTIVATED level of <paramref name="declaringScope"/>'s
    /// chain — the context that level's owner was entered in, independent of any consumer — or
    /// null when no level is activated (the root, an unactivated host scope). It keys a local-only
    /// property's cache entry (<c>ZeroArgPropertyCacheKey.FromExecution</c>) and is what a
    /// parameterless owner entered by a property-style read inherits (CACHE-OWNER-D1). Lean:
    /// <c>propertyOwnerBindingContext</c>.
    /// </summary>
    internal static object? DeclaringBindingIdentity(ScopeCtx? declaringScope)
    {
        for (var scope = declaringScope; scope is not null; scope = scope.Parent)
        {
            if (scope.Activation is { } activation)
                return activation.ValueEnvironmentIdentity;
        }

        return null;
    }

    /// <summary>
    /// The scope of the context's head as the site sees it: the activated head scope when the
    /// head was entered with parameters, otherwise the head's plain declaring scope. Null
    /// only for an empty call stack. Lean: <c>siteScope?</c>.
    /// </summary>
    private static ScopeCtx? SiteScope(EvalCtx ctx)
        => ctx.HeadScope ?? (ctx.Head is { } head ? AsScopeCtx(head) : null);

    /// <summary>
    /// The declaring scope of <paramref name="algorithm"/> IN the current context: static
    /// navigation may name the declaration of a currently active lexical ancestor, and then
    /// the active level — same declaration, compatible captured activations — is that scope,
    /// never a dynamically live unrelated caller. The head's own declaring scope in context is
    /// its head scope. Lean: <c>scopeInContext</c>.
    /// </summary>
    private static ScopeCtx ScopeInContext(Algorithm algorithm, EvalCtx ctx)
    {
        if (ctx.Head is not { } site)
            return AsScopeCtx(algorithm);

        if (ReferenceEquals(algorithm, site))
            return ctx.HeadScope ?? AsScopeCtx(algorithm);

        var scope = AsScopeCtx(algorithm);
        for (var level = SiteScope(ctx); level is not null; level = level.Parent)
        {
            if (IsSameDeclaringScope(scope, level) && CompatibleActivations(scope, level))
                return level;
        }

        return scope;
    }

    /// <summary>
    /// Whether every activation <paramref name="required"/> names along its chain is the one
    /// <paramref name="actual"/> carries at the same level; a level that requires no
    /// activation accepts any. Lean: <c>compatibleActivations</c>.
    /// </summary>
    private static bool CompatibleActivations(ScopeCtx? required, ScopeCtx? actual)
    {
        while (required is not null && actual is not null)
        {
            if (required.Activation is { } expected && !ReferenceEquals(expected, actual.Activation))
                return false;
            required = required.Parent;
            actual = actual.Parent;
        }
        return required is null && actual is null;
    }

    private static Algorithm ChildOfInContext(Algorithm parent, Algorithm child, EvalCtx ctx)
        => WithParent(child, ScopeInContext(parent, ctx));

    /// <summary>
    /// The activation that owns <paramref name="name"/> as read from the head's body — the
    /// nearest enclosing level binding the name, found on the head's lexical chain — or null
    /// when the head binds the name itself or no enclosing activation owns it.
    /// Lean: <c>capturedParameterActivation?</c>.
    /// </summary>
    private static ParameterActivation? CapturedParameterActivation(string name, EvalCtx ctx)
    {
        if (ctx.Head is not { } site)
            return null;

        // The head scope publishes the head's own parameter names (computed once at entry);
        // a head pushed without one — a loop step, a clause family, a builtin — reads them
        // from the algorithm.
        var ownNames = ctx.HeadScope is { } headScope ? headScope.Parameters : site.Params;
        if (ContainsOrdinal(ownNames, name))
            return null;

        var owner = site.Parent is { } parent ? RequiredParameterOwner(parent, name) : null;
        return owner?.Activation;
    }

    private static EvalCtx ParameterContext(string name, EvalCtx ctx, ref ValEnv values)
    {
        if (CapturedParameterActivation(name, ctx) is not { } activation)
            return ctx;

        values = activation.Values;
        return ctx.WithNeedEnv(activation.Needs);
    }

    internal static bool CapturedParameterNeedsOwnerLookup(string name, EvalCtx ctx, ValEnv values)
    {
        if (CapturedParameterActivation(name, ctx) is not { } activation)
            return false;
        return !ReferenceEquals(LookupVal(activation.Values, name), LookupVal(values, name));
    }
}
