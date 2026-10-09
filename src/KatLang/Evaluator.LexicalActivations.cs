namespace KatLang;

/// <summary>
/// The three binding channels of ONE activation of a lexical owner, captured when a call
/// enters the owner's body (<see cref="Evaluator.EnterAlgorithmBody"/>) or matches one of
/// its clauses (<c>ChildOfConditionalCall</c>): the owner's own parameter names, as bound
/// on the value, algorithm, and counted tiers at that moment — first binding per name,
/// exactly the tiers a captured-parameter read must see. Keeping the three channels
/// together prevents a shadowing caller from supplying any missing channel.
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
    private ParameterActivation(ValEnv values, AlgEnv algorithms, CountedParamEnv counted, NeedEnv needs,
        object valueEnvironmentIdentity, object algorithmEnvironmentIdentity, object countedEnvironmentIdentity)
    {
        Values = values;
        Algorithms = algorithms;
        Counted = counted;
        Needs = needs;
        ValueEnvironmentIdentity = valueEnvironmentIdentity;
        AlgorithmEnvironmentIdentity = algorithmEnvironmentIdentity;
        CountedEnvironmentIdentity = countedEnvironmentIdentity;
    }

    public ValEnv Values { get; }

    public AlgEnv Algorithms { get; }

    public CountedParamEnv Counted { get; }
    internal NeedEnv Needs { get; }

    // The binding context at OWNER entry, not the eventual consumer's context.
    // Parameterless property reads retain it; explicit calls bind fresh environments.
    internal object ValueEnvironmentIdentity { get; }
    internal object AlgorithmEnvironmentIdentity { get; }
    internal object CountedEnvironmentIdentity { get; }

    /// <summary>
    /// The normalized callable-alias targets of alias bindings declared under this activation
    /// (<see cref="Evaluator.AliasTargetKey"/>): an alias declared inside a call's body is resolved
    /// once per activation and forgotten with it. Runtime-only memoization, like the activation.
    /// </summary>
    internal Dictionary<Evaluator.AliasTargetKey, Algorithm> AliasTargets => _aliasTargets ??= [];

    private Dictionary<Evaluator.AliasTargetKey, Algorithm>? _aliasTargets;

    /// <summary>
    /// Captures the bindings of <paramref name="names"/> from the three tiers of a binding
    /// context: the value environment <paramref name="values"/> and the algorithm and counted
    /// tiers of <paramref name="ctx"/>, keeping the first binding of each owned name in
    /// environment order (Lean: <c>recordParameterActivation</c>'s three <c>filter</c>s).
    /// </summary>
    internal static ParameterActivation Capture(IReadOnlyList<string> names, Evaluator.EvalCtx ctx, ValEnv values)
        => new(
            FilterOwned(values, names, static binding => binding.Name),
            FilterOwned(ctx.AlgEnv, names, static binding => binding.Name),
            FilterOwned(ctx.CountedParamEnv, names, static binding => binding.Name),
            FilterOwned(ctx.NeedEnv, names, static binding => binding.Name),
            ctx.NeedEnv.Count == 0 ? Evaluator.ValueEnvironmentCacheIdentity(values) : ctx.NeedEnv,
            ctx.AlgEnv, ctx.CountedParamEnv);

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
    /// activation on, and the parent of every scope wired under the head. A parameterless owner with local properties also retains its entry context for
    /// their cache identity. Other parameterless bodies need no activated head scope.
    /// Lean: <c>enterAlgorithmBody</c> (<c>headScope := some (a.asScopeCtx.withActivation id)</c>).
    /// </summary>
    internal static EvalCtx EnterAlgorithmBody(Algorithm algorithm, EvalCtx ctx, ValEnv values, IReadOnlyList<string>? parameterNames = null)
    {
        var names = parameterNames ?? algorithm.Params;
        if (names.Count == 0 && !algorithm.Properties.Any(static property => property.Exposure != PropertyExposure.Exported))
            return ctx.Push(algorithm);

        var headScope = new ScopeCtx(algorithm.Parent, algorithm.Opens, algorithm.Properties, names)
        {
            Owner = algorithm,
            Activation = ParameterActivation.Capture(names, ctx, values),
        };
        return ctx.Push(algorithm, headScope);
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
        return ctx.WithAlgEnv(activation.Algorithms).WithCountedParamEnv(activation.Counted).WithNeedEnv(activation.Needs);
    }

    /// <summary>
    /// Whether a parameter's VALUE outcome is established on the legacy Ready tiers: it has a
    /// value (counted or value tier), or a failure is recorded on its algorithm binding. Under
    /// Model C a parameter's outcome is its supplied cell's (<see cref="KatLang.Evaluation.NeedCell"/>),
    /// demanded by the ordinary parameter read, and no binding path records an algorithm-tier
    /// failure (the eager writer, <c>SlotAlgorithmBinding</c>, was deleted). Either way a value
    /// demand of the parameter is the ordinary parameter read, never an evaluation of its
    /// algorithm channel. Lean: the value tiers the <c>.param</c> arm of <c>evalCounted</c> reads
    /// (the former <c>resolveArgAlgExpr</c> was removed with Model C).
    /// </summary>
    private static bool ParameterHasValueOutcome(string name, EvalCtx ctx, ValEnv values)
    {
        var parameterCtx = ParameterContext(name, ctx, ref values);
        return LookupCountedParam(parameterCtx.CountedParamEnv, name) is not null
            || LookupVal(values, name) is not null
            || LookupAlgBinding(parameterCtx.AlgEnv, name) is { ValueError: not null };
    }

    /// <summary>
    /// The failure recorded on a parameter's algorithm binding as its VALUE outcome (the
    /// legacy Ready tier: no Model-C binding path records one, and a supplied cell's failure
    /// is read through <see cref="EvalParamCounted"/>), read in the parameter's own binding
    /// context exactly as that read reaches the tier: <c>null</c> when the parameter has a
    /// value (a value binding always wins, as in that read) or no failed algorithm-channel
    /// binding.
    /// Lean: <c>parameterValueFailure?</c>.
    /// </summary>
    private static EvalError? ParameterValueFailure(string name, EvalCtx ctx, ValEnv values)
    {
        var parameterCtx = ParameterContext(name, ctx, ref values);
        if (LookupCountedParam(parameterCtx.CountedParamEnv, name) is not null || LookupVal(values, name) is not null)
            return null;

        return LookupAlgBinding(parameterCtx.AlgEnv, name)?.ValueError;
    }

    // A builtin value boundary must preserve an established parameter failure before
    // classifying the independent callable channel. This lookup never evaluates a body.
    private static EvalError? ParameterValueFailure(Expr? source, EvalCtx ctx, ValEnv values)
        => source is Expr.Param(var name) && ParameterValueFailure(name, ctx, values) is { } failure
            ? ParameterSlotFailure(name, source.Span, failure)
            : null;

    internal static bool CapturedParameterNeedsOwnerLookup(string name, EvalCtx ctx, ValEnv values)
    {
        if (CapturedParameterActivation(name, ctx) is not { } activation)
            return false;
        return LookupCountedParam(activation.Counted, name) != LookupCountedParam(ctx.CountedParamEnv, name)
            || !ReferenceEquals(LookupVal(activation.Values, name), LookupVal(values, name))
            || LookupAlgBinding(activation.Algorithms, name) != LookupAlgBinding(ctx.AlgEnv, name);
    }
}
