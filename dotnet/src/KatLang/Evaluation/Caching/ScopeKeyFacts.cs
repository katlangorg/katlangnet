using System.Runtime.CompilerServices;

namespace KatLang.Evaluation.Caching;

/// <summary>
/// ONE LEVEL of a resolving scope chain as the zero-argument property cache and the alias memos compare it
/// (<see cref="StructuralOwnerIdentity"/>): the level's opens and properties, the level object itself when it
/// is an OWNERLESS host-built level (HOST-NESTED-1), and the identity of the level above. A chain is a linked
/// list of these, so a level's identity is shared by every level wired beneath it instead of being copied into
/// each key (key facts per scope level, 2026-11-22; see <see cref="ScopeKeyFacts"/>).
/// <para><b>Structure only.</b> It never holds an evaluator-owned scope, an activation, a value or a run: a
/// published cache key that holds it keeps alive exactly what the former flat chain array kept alive (the live
/// declaration lists and the ownerless host levels).</para>
/// <para><b>Equality</b> (<see cref="ChainsEqual"/>) is the former array comparison: the same number of levels,
/// and at every level the same host level (or none) and opens/properties that are the same list or both empty.
/// The hash is computed once, from exactly what equality compares, so equal chains hash equally and a hash
/// difference proves inequality.</para>
/// </summary>
internal sealed class ScopeChainIdentity
{
    internal ScopeChainIdentity(
        IReadOnlyList<Expr> opens,
        IReadOnlyList<Property> properties,
        ScopeCtx? hostLevel,
        ScopeChainIdentity? parent)
    {
        Opens = opens;
        Properties = properties;
        HostLevel = hostLevel;
        Parent = parent;
        Length = (parent?.Length ?? 0) + 1;
        Hash = HashCode.Combine(
            parent?.Hash ?? 0,
            hostLevel is null ? 0 : RuntimeHelpers.GetHashCode(hostLevel),
            ComponentHash(opens),
            ComponentHash(properties));
    }

    internal IReadOnlyList<Expr> Opens { get; }

    internal IReadOnlyList<Property> Properties { get; }

    /// <summary>The ownerless host-built level at this position, compared by reference; null for an evaluator-owned level.</summary>
    internal ScopeCtx? HostLevel { get; }

    internal ScopeChainIdentity? Parent { get; }

    /// <summary>The number of levels from this one to the top of the chain.</summary>
    internal int Length { get; }

    internal int Hash { get; }

    /// <summary>
    /// Whether two chains (null is the empty chain) are the same resolving chain. A shared tail ends the
    /// comparison at once, so two keys built over one memoized level compare in constant time.
    /// </summary>
    internal static bool ChainsEqual(ScopeChainIdentity? x, ScopeChainIdentity? y)
    {
        while (!ReferenceEquals(x, y))
        {
            if (x is null || y is null
                || x.Hash != y.Hash
                || x.Length != y.Length
                || !ReferenceEquals(x.HostLevel, y.HostLevel)
                || !ComponentEquals(x.Opens, y.Opens)
                || !ComponentEquals(x.Properties, y.Properties))
            {
                return false;
            }

            x = x.Parent;
            y = y.Parent;
        }

        return true;
    }

    /// <summary>
    /// A scope level participates in name resolution ONLY through its opens and properties, so two EMPTY lists
    /// resolve identically no matter which instance they are; non-empty lists compare by REFERENCE (see
    /// <see cref="StructuralOwnerIdentity"/>).
    /// </summary>
    internal static bool ComponentEquals<T>(IReadOnlyList<T> x, IReadOnlyList<T> y)
        => ReferenceEquals(x, y) || (x.Count == 0 && y.Count == 0);

    private static int ComponentHash<T>(IReadOnlyList<T> component)
        => component.Count == 0 ? 0 : RuntimeHelpers.GetHashCode(component);
}

/// <summary>
/// What a level's chain contributes to a key: its chain identity, the nearest activation on it that an actual
/// call recorded (<see cref="ParameterActivation.OwnsInvocation"/>, the owning invocation of an exported binding
/// declared under the level), the nearest activation on it at all (the declaring binding identity of a
/// local-only one, and the owner of an alias's pure memos) and the lowest serial of its activations
/// (<see cref="ParameterActivation.Serial"/>; <see cref="long.MaxValue"/> when it has none: whether an exported
/// evaluation's watermark detaches one of them). Each is a pure function of the level's immutable chain.
/// <see cref="Empty"/> is the empty chain.
/// </summary>
internal readonly record struct LevelKeyFacts(
    ScopeChainIdentity? Chain,
    ParameterActivation? InvocationActivation,
    ParameterActivation? BindingActivation,
    long OldestActivationSerial)
{
    /// <summary>The facts of the empty chain: no level, no activation.</summary>
    internal static LevelKeyFacts Empty { get; } = new(null, null, null, long.MaxValue);
}

/// <summary>
/// THE KEY FACTS OF ONE EVALUATOR-OWNED SCOPE LEVEL (implementation-only optimization, 2026-11-22; finding
/// <c>caching-retention-key-depth-per-read</c> of the 2026-11-21 adversarial investigation, baseline
/// <c>8947d21e</c>). Every zero-argument property request computes its key, and the key's owner identity and
/// environment identity are functions of the declaring scope CHAIN: until this memo every request copied the
/// owner's whole parent chain into a fresh array, hashed it and compared it level by level against the stored
/// key, and walked the declaring chain again for its owning invocation or binding identity — work and
/// allocation proportional to the lexical depth on EVERY read, hits included. A level's facts
/// (<see cref="LevelKeyFacts"/>) are a pure function of the level's immutable chain (its parent links, lists,
/// owner and activation are all fixed at construction), so they are computed once per level object and reused
/// by every key built over it: a read then costs the same at any depth.
/// <para><b>Where it lives.</b> On the level's own runtime state, never in a table: a static evaluator-owned
/// level keeps it in its runtime slot (<see cref="ScopeCtx.StaticKeyFacts"/>), an activated level on its
/// activation (<see cref="ParameterActivation.KeyFacts"/>; an activation belongs to the one level that was
/// created with it). It therefore lives exactly as long as the level: it gives no activation, value, run or
/// scope a longer lifetime, and the chain identities it hands to keys are structure only
/// (<see cref="ScopeChainIdentity"/>). An OWNERLESS host-built level (a host's blueprint, shared across runs
/// and threads) never carries one: its facts are computed on every request, as before, down to the nearest
/// evaluator-owned level. <see cref="Level"/> is checked on every reuse, so a <c>with</c> copy of a level
/// (which carries the runtime slot) computes its own facts.</para>
/// <para><b>Concurrency.</b> A lookup uses one snapshot of a memo that names its level. Cold publication
/// coordinates with the level's open-provider memo. Identity reuse slots publish immutable objects.</para>
/// </summary>
internal sealed class ScopeKeyFacts
{
    private StructuralOwnerIdentity? _childOwner;
    private StructuralOwnerIdentity? _scope;
    private StructuralOwnerIdentity? _propertyScope;

    private ScopeKeyFacts(ScopeCtx level, LevelKeyFacts facts)
    {
        Level = level;
        Facts = facts;
    }

    /// <summary>The level these facts were computed for (a <c>with</c> copy is another level).</summary>
    internal ScopeCtx Level { get; }

    internal LevelKeyFacts Facts { get; }

    /// <summary>The chain identity of <see cref="Level"/>.</summary>
    internal ScopeChainIdentity Chain => Facts.Chain!;

    /// <summary>
    /// TEST SEAM: the number of key-fact computations that built a level's facts (one per level on the walk of a
    /// request that found the level unmemoized). Counted only while <see cref="CountComputations"/> is set on
    /// the current thread, so ordinary runs pay one thread-static read per computation and nothing per hit.
    /// </summary>
    [ThreadStatic]
    private static long t_levelComputations;

    [ThreadStatic]
    private static bool t_countComputations;

    /// <summary>TEST SEAM: starts counting this thread's level computations from zero.</summary>
    internal static void CountComputations()
    {
        t_levelComputations = 0;
        t_countComputations = true;
    }

    /// <summary>TEST SEAM: stops counting and returns this thread's level computations since <see cref="CountComputations"/>.</summary>
    internal static long StopCountingComputations()
    {
        t_countComputations = false;
        return t_levelComputations;
    }

    /// <summary>
    /// The facts of <paramref name="level"/>'s chain: memoized on an evaluator-owned level, computed for an
    /// ownerless host level (down to its nearest evaluator-owned ancestor, whose memo serves the rest).
    /// </summary>
    internal static LevelKeyFacts Describe(ScopeCtx? level)
    {
        if (level is null)
            return LevelKeyFacts.Empty;
        if (level.Owner is not null && Peek(level) is { } memo)
            return memo.Facts;
        return Compute(level, out _);
    }

    // Host-built levels have no captured activation and keep no memo. A request for the environment
    // alone can cross those levels without allocating an unused chain identity for each one.
    internal static LevelKeyFacts ForActivationLookup(ScopeCtx? level)
    {
        while (level is { Owner: null, Activation: null })
            level = level.Parent;
        return Describe(level);
    }

    /// <summary>The memoized facts of the evaluator-owned <paramref name="level"/>, computing them on first use.</summary>
    internal static ScopeKeyFacts Of(ScopeCtx level)
    {
        System.Diagnostics.Debug.Assert(level.Owner is not null, "Only an evaluator-owned level memoizes its key facts.");
        if (Peek(level) is { } memo)
            return memo;
        Compute(level, out var created);
        return created!;
    }

    /// <summary>
    /// The identity of an owner whose parent is this level (<see cref="StructuralOwnerIdentity.FromOwner"/>,
    /// <see cref="StructuralOwnerIdentity.FromPropertyOwner"/>): the last one built over this level is kept and
    /// reused while the declaration and the owner's own lists are the same objects.
    /// </summary>
    internal StructuralOwnerIdentity ChildOwnerIdentity(
        object? declaration,
        IReadOnlyList<Expr> opens,
        IReadOnlyList<Property> properties)
    {
        var cached = Volatile.Read(ref _childOwner);
        if (cached is not null && cached.IsOwnerIdentityOf(declaration, opens, properties))
            return cached;

        var created = new StructuralOwnerIdentity(declaration, new ScopeChainIdentity(opens, properties, hostLevel: null, Chain));
        Volatile.Write(ref _childOwner, created);
        return created;
    }

    /// <summary><see cref="StructuralOwnerIdentity.FromScope"/> of this level, built once.</summary>
    internal StructuralOwnerIdentity ScopeIdentity()
    {
        var cached = Volatile.Read(ref _scope);
        if (cached is not null)
            return cached;

        var created = new StructuralOwnerIdentity(declaration: null, Chain);
        Volatile.Write(ref _scope, created);
        return created;
    }

    /// <summary>
    /// <see cref="StructuralOwnerIdentity.FromPropertyScope"/> of this evaluator-owned level, built once: the
    /// level's declaration over its own chain identity, whose first level is never a host level.
    /// </summary>
    internal StructuralOwnerIdentity PropertyScopeIdentity()
    {
        var cached = Volatile.Read(ref _propertyScope);
        if (cached is not null)
            return cached;

        var created = new StructuralOwnerIdentity(Level.Declaration, Chain);
        Volatile.Write(ref _propertyScope, created);
        return created;
    }

    // The memo of an evaluator-owned level, if it is this level's.
    private static ScopeKeyFacts? Peek(ScopeCtx level)
    {
        var memo = level.Activation is { } activation ? activation.KeyFacts : level.StaticKeyFacts;
        return memo is not null && ReferenceEquals(memo.Level, level) ? memo : null;
    }

    /// <summary>
    /// Builds the facts of <paramref name="level"/> from the nearest memoized evaluator-owned level above it (or
    /// the top of the chain), publishing the facts of every evaluator-owned level on the way: the walk is paid
    /// once per level. Iterative, because a chain is as deep as lexical nesting or a host makes it.
    /// <paramref name="created"/> is the memo of <paramref name="level"/> when it is evaluator-owned.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static LevelKeyFacts Compute(ScopeCtx level, out ScopeKeyFacts? created)
    {
        created = null;
        var parent = level.Parent;
        if (parent is null)
            return Step(level, LevelKeyFacts.Empty, ref created);
        if (parent.Owner is not null && Peek(parent) is { } parentMemo)
            return Step(level, parentMemo.Facts, ref created);

        var pending = new List<ScopeCtx> { level };
        var facts = LevelKeyFacts.Empty;
        for (var current = parent; current is not null; current = current.Parent)
        {
            if (current.Owner is not null && Peek(current) is { } found)
            {
                facts = found.Facts;
                break;
            }

            pending.Add(current);
        }

        for (var i = pending.Count - 1; i > 0; i--)
        {
            ScopeKeyFacts? ignored = null;
            facts = Step(pending[i], facts, ref ignored);
        }

        return Step(level, facts, ref created);
    }

    // The facts of one level over the facts of the level above it; an evaluator-owned level publishes them.
    private static LevelKeyFacts Step(ScopeCtx level, LevelKeyFacts above, ref ScopeKeyFacts? created)
    {
        if (t_countComputations)
            t_levelComputations++;

        var activation = level.Activation;
        var facts = new LevelKeyFacts(
            new ScopeChainIdentity(level.Opens, level.Properties, level.Owner is null ? level : null, above.Chain),
            activation is { OwnsInvocation: true } ? activation : above.InvocationActivation,
            activation ?? above.BindingActivation,
            activation is null ? above.OldestActivationSerial : Math.Min(activation.Serial, above.OldestActivationSerial));
        if (level.Owner is null)
            return facts;

        // An unavailable-parameter stand-in is never a level's activation and owns no memo; such a level's facts
        // are still correct, merely not kept.
        var memo = new ScopeKeyFacts(level, facts);
        if (activation is null)
            level.PublishStaticKeyFacts(memo);
        else if (!activation.IsUnavailable)
            activation.PublishKeyFacts(memo);
        created = memo;
        return facts;
    }
}
