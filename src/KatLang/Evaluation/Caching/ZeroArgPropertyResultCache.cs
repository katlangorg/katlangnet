using System.Runtime.CompilerServices;

namespace KatLang.Evaluation.Caching;

/// <summary>
/// The DECLARING OWNER of a zero-argument property binding, from which its cache key's owner
/// identity is computed (CACHE-OWNER-D3, owner decisions O-2/O-3, October 23 2026). Exactly one of:
/// <list type="bullet">
///   <item>an evaluator-owned declaration (<see cref="Algorithm"/>) — identified structurally by
///   <see cref="StructuralOwnerIdentity.FromPropertyOwner"/>, so rebuilt owners over one resolving
///   scope keep sharing an entry;</item>
///   <item>an OWNERLESS host-built <see cref="ScopeCtx"/> level (its internal <c>Owner</c> is null:
///   a host scope kept as the parent of an opened inline block) — identified by the REFERENCE of
///   that very scope object. The evaluator never copies a host level during a run, so every read
///   through it names the same object, while two independently constructed host scopes — even
///   structurally equal ones, or ones sharing a property or a property list, or a record
///   <c>with</c> copy — stay two owners. <see cref="ScopeCtx"/>'s record (structural) equality is
///   never consulted: the key comparer compares every non-<see cref="StructuralOwnerIdentity"/>
///   owner identity with <see cref="object.ReferenceEquals"/> and hashes it with
///   <see cref="RuntimeHelpers.GetHashCode"/>.</item>
/// </list>
/// One reference wide, so carrying it costs no more than the former nullable owner. Its own
/// equality is likewise by reference (never a structural record comparison).
/// </summary>
internal readonly struct PropertyDeclaringOwner : IEquatable<PropertyDeclaringOwner>
{
    // An Algorithm (evaluator-owned declaration) or a ScopeCtx (ownerless host level); never null
    // for a constructed value.
    private readonly object _owner;

    private PropertyDeclaringOwner(object owner) => _owner = owner;

    public static implicit operator PropertyDeclaringOwner(Algorithm owner)
        => new(owner ?? throw new ArgumentNullException(nameof(owner)));

    /// <summary>
    /// The declaring owner of a property found in the scope level <paramref name="level"/>: the
    /// level's evaluator owner when it has one, otherwise the ownerless host level itself.
    /// </summary>
    internal static PropertyDeclaringOwner OfLevel(ScopeCtx level)
        => level.Owner is { } owner ? new(owner) : new(level);

    /// <summary>The evaluator-owned declaration, or <c>null</c> for an ownerless host level.</summary>
    internal Algorithm? Algorithm => _owner as Algorithm;

    /// <summary>The ownerless host-built declaring level, or <c>null</c> for an evaluator-owned declaration.</summary>
    internal ScopeCtx? HostScope => _owner as ScopeCtx;

    /// <summary>The owner component of the cache key: structural for an evaluator owner, the host level by reference.</summary>
    internal object CacheIdentity => _owner switch
    {
        Algorithm owner => StructuralOwnerIdentity.FromPropertyOwner(owner),
        ScopeCtx hostScope => hostScope,
        _ => throw new InvalidOperationException("A zero-argument property execution must name its declaring owner."),
    };

    public bool Equals(PropertyDeclaringOwner other) => ReferenceEquals(_owner, other._owner);

    public override bool Equals(object? obj) => obj is PropertyDeclaringOwner other && Equals(other);

    public override int GetHashCode() => RuntimeHelpers.GetHashCode(_owner);
}

internal readonly record struct ZeroArgPropertyExecution(
    PropertyDeclaringOwner Owner,
    Property Binding,
    ZeroArgPropertyAccessKind AccessKind,
    object ValueEnvironmentIdentity,
    object RunIdentity)
{
    internal ScopeCtx? DeclaringScope { get; init; }
}

internal readonly record struct ZeroArgPropertyResult(
    Result Value,
    int EmittedCount);

internal enum ZeroArgPropertyCacheAccessShape
{
    Lexical,
    Structural,
}

internal interface IZeroArgPropertyResultCache
{
    EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate);

    /// <summary>
    /// A qualifying explicit zero-supply INVOCATION of the property (CACHE-PUB-1, owner decision
    /// October 22 2026): <paramref name="evaluate"/> — the invocation's own fresh execution, whose
    /// result is the PROPERTY-LEVEL counted output — ALWAYS runs (an established entry never
    /// satisfies an invocation and is never replaced), and on an empty entry the invocation
    /// participates in the ONE publication law (<see cref="ZeroArgPropertyPublications.Invoke"/>):
    /// as the key's outermost owner its success establishes the entry a later property-style read
    /// reuses. There is deliberately no default: the cache OWNS the publication law, so a cache that
    /// stores reads must publish owning invocations exactly as <see cref="ZeroArgPropertyPublications"/>
    /// does, and only a cache that stores nothing (<see cref="UncachedZeroArgPropertyResultCache"/>)
    /// simply executes.
    /// </summary>
    EvalResult<ZeroArgPropertyResult> Invoke(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate);

    /// <summary>
    /// PUBLICATION PROVENANCE of a read (DECON-CACHE-2, October 2026): whether a property-style read of
    /// <paramref name="key"/> issued NOW is guaranteed to obtain the value this cache has published or
    /// will publish for the key — never a re-entrant intermediate (Q-37) and never a value the cache does
    /// not retain. Non-evaluating, charge-free and side-effect-free. The deconstruction shared bind
    /// (<see cref="RunScopedDeconstructionBindingCache"/>) stores a bind only when the source read that
    /// supplies it qualifies. The default is the conservative <c>false</c>: a cache that does not state
    /// its publication law (or stores nothing, <see cref="UncachedZeroArgPropertyResultCache"/>) never
    /// lets a group's targets share a bind, so each target executes its ordinary bind.
    /// </summary>
    bool ReadObtainsPublishedValue(ZeroArgPropertyCacheKey key) => false;
}

/// <summary>
/// The cache key, and with it the cache's semantic LAW (Lean:
/// <c>zeroArgPropertyCacheKey</c>). The scope of a stored value follows the
/// binding's exposure classification:
/// <list type="bullet">
///   <item>An <see cref="PropertyExposure.Exported"/> binding is self-contained:
///   its value depends on no input that an enclosing owner's call binds (the front
///   end's classification, which the evaluator trusts here exactly as it does for
///   <c>open</c> and structural access). The binding context at the access is
///   therefore not a determinant of the value, and ONE entry per run per declaring
///   scope (<see cref="StructuralOwnerIdentity"/> — the same identity for every
///   activation, open-provided wiring, or rebuilt structural receiver of that scope; for an
///   ownerless host-built declaring level, the level object by reference:
///   <see cref="PropertyDeclaringOwner"/>)
///   serves every property-style access: <c>Big</c> read from two thousand calls of
///   <c>F(x) = Big + x</c>, from each callback of a <c>map</c>, from every
///   iteration of a loop step, or inside an explicit <c>B()</c> call is evaluated
///   once. The environment component is the shared
///   <see cref="RunWideEnvironmentIdentity"/> sentinel.</item>
///   <item>A local-only binding (<see cref="PropertyExposure.LocalOnlyCapturedAncestorParameters"/>)
///   reads an input an enclosing owner's call binds, through the dynamically
///   threaded environments; its value is a function of the binding context, so the
///   key carries the binding-context identity at the DECLARING owner's entry (the need-cell
///   list its call boundary minted, even an empty one, or the value environment below every
///   boundary: <c>Evaluator.BindingContextIdentity</c>, CACHE-OWNER-D2) and the
///   declaring scope. Two distinct binding contexts never share an
///   entry, and consumers within one owning activation reuse its entry even through nested calls:
///   a parameterless or collecting-only owner entered by a property-style read inherits its declaring
///   activation's identity (<c>Evaluator.DeclaringBindingIdentity</c>, CACHE-OWNER-D1, COLLECT-CACHE-1),
///   so a callback, helper or
///   loop step that reads it first, a structural <c>B.V</c> and an opened <c>V</c> share one entry.
///   Scopes without an activation retain the host environment fallback.</item>
/// </list>
/// An explicit zero-supply invocation (<c>A()</c>) of the same binding computes the SAME key
/// (CACHE-PUB-1): it never reads an entry, but its owning success may establish an empty one. The
/// run identity keeps entries from crossing runs even on a host-shared cache instance. WHICH
/// completion creates the entry is <see cref="ZeroArgPropertyPublications"/>'s law (Q-37, extended
/// to invocations by CACHE-PUB-1): the outermost successful qualifying evaluation of the key.
/// </summary>
internal readonly record struct ZeroArgPropertyCacheKey(
    ZeroArgPropertyCacheAccessShape AccessShape,
    object OwnerIdentity,
    object BindingIdentity,
    object ValueEnvironmentIdentity,
    object RunIdentity)
{
    /// <summary>
    /// Environment identity of every key of an exported binding: the binding context
    /// is not a determinant of a self-contained value, so the environment component
    /// collapses to this one process-wide sentinel (the run identity still separates runs).
    /// </summary>
    internal static object RunWideEnvironmentIdentity { get; } = new();

    public static ZeroArgPropertyCacheKey FromExecution(ZeroArgPropertyExecution execution)
    {
        return execution.Binding.Exposure == PropertyExposure.Exported
            ? new(
                // Both spellings select the same exported declaration. Keep the
                // original access kind on the execution for instrumentation only.
                ZeroArgPropertyCacheAccessShape.Lexical,
                execution.Owner.CacheIdentity,
                execution.Binding,
                RunWideEnvironmentIdentity,
                execution.RunIdentity)
            : new(
                ZeroArgPropertyCacheAccessShape.Lexical,
                execution.Owner.CacheIdentity,
                execution.Binding,
                Evaluator.DeclaringBindingIdentity(execution.DeclaringScope) ?? execution.ValueEnvironmentIdentity,
                execution.RunIdentity);
    }

}

/// <summary>
/// Declaring-scope identity of a zero-arg property owner: the owner identity
/// of every binding's key (lexical and structural access alike).
/// The evaluator rebuilds the owner
/// <see cref="Algorithm"/> record on every structural access, every lexical
/// resolution through an <c>open</c>, and every activation of a nested owner
/// (<c>ChildOf</c>/<c>AsScopeCtx</c> mint fresh records and scope contexts),
/// so keying on the owner REFERENCE would defeat reuse across those paths —
/// but erasing the owner altogether (the previous process-wide sentinel) let
/// one shared <see cref="Property"/> object placed under two different owners
/// alias to a single cache entry and return the other owner's value. The
/// value actually evaluated is the property wired to
/// <c>ScopeCtx(Owner.Parent, Owner.Opens, Owner.Properties)</c>, so this
/// identity captures that scope and its complete parent chain. Non-empty
/// opens/property-list components compare BY REFERENCE; separately allocated
/// empty components compare as resolution-equivalent because they contribute
/// nothing to lookup. Each intermediate <see cref="ScopeCtx"/> can be minted
/// afresh along a nested structural path, so comparing any scope record itself
/// would split equivalent rebuilt paths. Rebuilt owners over the same resolving
/// scope therefore keep hitting at every nesting depth, while owners with
/// resolution-distinct components never collide.
/// </summary>
internal sealed class StructuralOwnerIdentity
{
    private readonly ScopeComponent[] _scopeChain;
    // By reference: an owner's declaration token, or (FromScope) an ownerless host-built level.
    private readonly object? _declaration;
    private readonly int _hashCode;

    private StructuralOwnerIdentity(ScopeComponent[] scopeChain, object? declaration = null)
    {
        _scopeChain = scopeChain;
        _declaration = declaration;
        // Immutable, and hashed on every cache operation of a key (lookup, the Q-37 active-owner
        // set, publication, statistics): compute the chain walk once.
        _hashCode = ComputeHashCode(scopeChain, declaration);
    }

    public static StructuralOwnerIdentity FromOwner(Algorithm owner, bool includeDeclaration = false)
    {
        // Every cache request computes its key (CACHE-PUB-1 added the explicit zero-supply
        // invocations), so the chain is measured first and copied into ONE exact array.
        var length = 1;
        for (var scope = owner.Parent; scope is not null; scope = scope.Parent)
            length++;

        var scopeChain = new ScopeComponent[length];
        scopeChain[0] = new ScopeComponent(owner.Opens, owner.Properties);
        var index = 1;
        for (var scope = owner.Parent; scope is not null; scope = scope.Parent)
            scopeChain[index++] = new ScopeComponent(scope.Opens, scope.Properties);

        return new StructuralOwnerIdentity(scopeChain, includeDeclaration ? owner.Declaration : null);
    }

    internal static StructuralOwnerIdentity FromPropertyOwner(Algorithm owner)
        => FromOwner(owner, includeDeclaration: true);

    /// <summary>
    /// True when this is the property-owner identity of an owner with the declaration token
    /// <paramref name="declaration"/> whose OWN property list is <paramref name="properties"/>
    /// (by reference): the root-owner check of <see cref="RootPropertyObservationSink"/>. The
    /// parent chain is deliberately not compared — wiring gives the root a run-specific parent.
    /// </summary>
    internal bool IsPropertyOwner(object? declaration, IReadOnlyList<Property> properties)
        => ReferenceEquals(_declaration, declaration)
            && _scopeChain.Length != 0
            && ReferenceEquals(_scopeChain[0].Properties, properties);

    /// <summary>
    /// The resolving identity of a SCOPE chain itself — each level's opens and properties, from
    /// <paramref name="scope"/> outward — with no owner declaration: what a name looked up from a
    /// body wired under <paramref name="scope"/> can select. A null scope is the empty chain.
    /// <para>When <paramref name="scope"/> is itself an OWNERLESS host-built level, that level OBJECT
    /// is part of the identity, by reference — the rule <see cref="PropertyDeclaringOwner"/> applies
    /// to the properties declared there (CACHE-OWNER-D3): the evaluator never copies a host level, so
    /// every use through it still names one identity, while two independently constructed host
    /// levels that share a property list (or a record <c>with</c> copy) — whose property entries are
    /// already separate — no longer share the run-wide alias memo either (HOST-ALIAS-R14).
    /// Evaluator-created levels always have an owner, so rebuilt evaluator scopes keep comparing
    /// structurally.</para>
    /// </summary>
    internal static StructuralOwnerIdentity FromScope(ScopeCtx? scope)
    {
        var scopeChain = new List<ScopeComponent>();
        for (var level = scope; level is not null; level = level.Parent)
            scopeChain.Add(new ScopeComponent(level.Opens, level.Properties));
        return new StructuralOwnerIdentity([.. scopeChain], scope is { Owner: null } hostLevel ? hostLevel : null);
    }

    public override bool Equals(object? obj)
    {
        if (obj is not StructuralOwnerIdentity other
            || !ReferenceEquals(_declaration, other._declaration)
            || _scopeChain.Length != other._scopeChain.Length)
        {
            return false;
        }

        for (var i = 0; i < _scopeChain.Length; i++)
        {
            if (!ComponentEquals(_scopeChain[i].Opens, other._scopeChain[i].Opens)
                || !ComponentEquals(_scopeChain[i].Properties, other._scopeChain[i].Properties))
            {
                return false;
            }
        }

        return true;
    }

    /// <summary>
    /// A scope level participates in name resolution ONLY through its opens and properties, so
    /// two EMPTY lists resolve identically no matter which instance they are. Comparing them by
    /// reference would split otherwise-equivalent chains: the parser gives every elaborated
    /// helper — for example each target of one assignment deconstruction — its own empty
    /// collections, so a per-target wrapper level would make every target look like a different
    /// owner. Non-empty lists still compare by REFERENCE: they are the live declaration lists,
    /// and two distinct lists are two distinct scopes even when their contents look alike.
    /// </summary>
    private static bool ComponentEquals<T>(IReadOnlyList<T> x, IReadOnlyList<T> y)
        => ReferenceEquals(x, y) || (x.Count == 0 && y.Count == 0);

    private static int ComponentHash<T>(IReadOnlyList<T> component)
        => component.Count == 0 ? 0 : RuntimeHelpers.GetHashCode(component);

    public override int GetHashCode() => _hashCode;

    private static int ComputeHashCode(ScopeComponent[] scopeChain, object? declaration)
    {
        var hash = new HashCode();
        hash.Add(declaration is null ? 0 : RuntimeHelpers.GetHashCode(declaration));
        hash.Add(scopeChain.Length);
        foreach (var component in scopeChain)
        {
            hash.Add(ComponentHash(component.Opens));
            hash.Add(ComponentHash(component.Properties));
        }

        return hash.ToHashCode();
    }

    private readonly record struct ScopeComponent(
        IReadOnlyList<Expr> Opens,
        IReadOnlyList<Property> Properties);
}

internal sealed class ZeroArgPropertyCacheKeyComparer : IEqualityComparer<ZeroArgPropertyCacheKey>
{
    public static ZeroArgPropertyCacheKeyComparer Instance { get; } = new();

    private ZeroArgPropertyCacheKeyComparer()
    {
    }

    public bool Equals(ZeroArgPropertyCacheKey x, ZeroArgPropertyCacheKey y)
        => x.AccessShape == y.AccessShape
            && OwnerIdentityEquals(x.OwnerIdentity, y.OwnerIdentity)
            && ReferenceEquals(x.BindingIdentity, y.BindingIdentity)
            && ReferenceEquals(x.ValueEnvironmentIdentity, y.ValueEnvironmentIdentity)
            && ReferenceEquals(x.RunIdentity, y.RunIdentity);

    /// <summary>
    /// Declaring-scope identity is a computed <see cref="StructuralOwnerIdentity"/>
    /// whose equality treats empty scope components as resolution-equivalent and
    /// compares non-empty components by reference — or, for a property declared in an
    /// ownerless host-built level (<see cref="PropertyDeclaringOwner"/>, CACHE-OWNER-D3), that
    /// <see cref="ScopeCtx"/> object itself, compared by REFERENCE (never its record equality).
    /// The two kinds never collide: a structural identity equals only a structural identity.
    /// </summary>
    internal static bool OwnerIdentityEquals(object x, object y)
        => x is StructuralOwnerIdentity structural
            ? structural.Equals(y)
            : ReferenceEquals(x, y);

    public int GetHashCode(ZeroArgPropertyCacheKey obj)
    {
        var hash = new HashCode();
        hash.Add(obj.AccessShape);
        hash.Add(obj.OwnerIdentity is StructuralOwnerIdentity structural
            ? structural.GetHashCode()
            : RuntimeHelpers.GetHashCode(obj.OwnerIdentity));
        hash.Add(RuntimeHelpers.GetHashCode(obj.BindingIdentity));
        hash.Add(RuntimeHelpers.GetHashCode(obj.ValueEnvironmentIdentity));
        hash.Add(RuntimeHelpers.GetHashCode(obj.RunIdentity));
        return hash.ToHashCode();
    }
}

/// <summary>
/// THE PUBLICATION LAW of the zero-argument property cache (Q-37, owner decision October 11
/// 2026, superseding the first-successful-completion rule; extended to qualifying explicit
/// zero-supply invocations by CACHE-PUB-1, owner decision October 22 2026; Lean
/// <c>evalZeroArgPropertyAccessCounted</c> over <c>EvalState.activeZeroArgProperties</c> with a
/// <c>read</c> or <c>invoke</c> request): the OUTERMOST successful qualifying evaluation of a key
/// owns its entry — a property-style read (<see cref="EvaluateMiss"/> after a miss) or an explicit
/// zero-supply invocation (<see cref="Invoke"/>) alike, in ONE ownership domain (one active set).
/// An invocation never obtains its result from an established entry and never replaces it.
/// <list type="bullet">
///   <item>A miss on a key no evaluation is currently executing makes that access the key's
///   OWNER: the key is ACTIVE while the owner's body runs and stops being active on every exit
///   (success, ordinary failure, resource limit, host exception, cancellation).</item>
///   <item>A miss on an ACTIVE key is RE-ENTRANT — the same binding reached again, directly
///   (<c>A → A</c>) or indirectly (<c>A → B → A</c>), before its owner finished: it evaluates
///   the body and returns its own (possibly intermediate) result, but publishes NOTHING. It
///   never waits on the owner, so there is no self-await and no deadlock.</item>
///   <item>Only the owner's SUCCESS is published, so every later property-style read reuses the
///   owner's result. A failed owner publishes nothing for its key; entries that OTHER keys'
///   owners published meanwhile stay (there is no rollback).</item>
///   <item>Publication never replaces an entry (under the law no other completion can reach an
///   active key's entry; <see cref="Dictionary{TKey, TValue}.TryAdd"/> keeps that guarantee
///   unconditional).</item>
/// </list>
/// Within one run evaluation is serial — the async twin awaits every access before
/// continuing — so the active set is exactly the owners on the current evaluation chain.
/// The set is keyed by the full cache key, run identity included, so a nested run sharing a
/// cache instance never sees another run's owners. Ordinary hits pay nothing extra; a miss
/// adds one set insertion and removal around the body. Not thread-safe, like the caches
/// that use it (run-scoped, sequential access).
/// <para><b>Passive observation (IV-1).</b> An optional run-owned
/// <see cref="RootPropertyObservationSink"/> is told about each publication right after this
/// law has made it, in publication order, and about nothing else: never a hit, a re-entrant
/// completion, or a failure. The sink only records; it cannot change the decision, the stored
/// entry, or the returned result. Without a sink the cost is one null check per publication.</para>
/// </summary>
internal sealed class ZeroArgPropertyPublications(RootPropertyObservationSink? sink = null)
{
    private readonly Dictionary<ZeroArgPropertyCacheKey, ZeroArgPropertyResult> _published =
        new(ZeroArgPropertyCacheKeyComparer.Instance);
    private readonly HashSet<ZeroArgPropertyCacheKey> _active = new(ZeroArgPropertyCacheKeyComparer.Instance);

    /// <summary>Number of published entries.</summary>
    internal int Count => _published.Count;

    /// <summary>Number of keys whose owner is still evaluating (zero between accesses).</summary>
    internal int ActiveOwnerCount => _active.Count;

    internal bool TryGetPublished(ZeroArgPropertyCacheKey key, out ZeroArgPropertyResult result)
        => _published.TryGetValue(key, out result);

    /// <summary>
    /// Whether a property-style read of <paramref name="key"/> issued NOW obtains the value this law
    /// publishes for the key: a published entry is served as is, and a miss on a key no evaluation is
    /// running makes the read the key's OWNER, whose success is exactly the entry it publishes (no other
    /// completion can publish an active key). Only a read of an ACTIVE key is re-entrant and returns an
    /// intermediate value that is never published. Non-evaluating and charge-free; see
    /// <see cref="IZeroArgPropertyResultCache.ReadObtainsPublishedValue"/>.
    /// </summary>
    internal bool ReadObtainsPublishedValue(ZeroArgPropertyCacheKey key)
        => _published.ContainsKey(key) || !_active.Contains(key);

    /// <summary>
    /// Evaluates a MISS of <paramref name="key"/> under the publication law;
    /// <paramref name="published"/> reports whether this access published its result.
    /// </summary>
    internal EvalResult<ZeroArgPropertyResult> EvaluateMiss(
        ZeroArgPropertyCacheKey key,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate,
        out bool published)
    {
        published = false;
        if (!_active.Add(key))
            return evaluate();

        EvalResult<ZeroArgPropertyResult> result;
        try
        {
            result = evaluate();
        }
        finally
        {
            _active.Remove(key);
        }

        if (!result.IsError && _published.TryAdd(key, result.Value))
        {
            published = true;
            sink?.Published(key, result.Value);
        }

        return result;
    }

    /// <summary>
    /// A qualifying explicit zero-supply INVOCATION of <paramref name="key"/> (CACHE-PUB-1; Lean: the
    /// <c>invoke</c> request of <c>evalZeroArgPropertyAccessCounted</c>). <paramref name="evaluate"/>
    /// ALWAYS runs: an established entry never satisfies an invocation, and it is left unchanged
    /// (the invocation neither marks the key nor publishes). On an EMPTY entry the invocation is a
    /// request of the very law <see cref="EvaluateMiss"/> implements — the key's owner when no
    /// evaluation of it is running, re-entrant otherwise — so its owning success establishes the
    /// entry (and is observed exactly like a read's publication).
    /// </summary>
    internal EvalResult<ZeroArgPropertyResult> Invoke(
        ZeroArgPropertyCacheKey key,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate,
        out bool published)
    {
        if (_published.ContainsKey(key))
        {
            published = false;
            return evaluate();
        }

        return EvaluateMiss(key, evaluate, out published);
    }

    /// <summary>MIRROR OF <see cref="Invoke"/> — keep in lock-step.</summary>
    internal ValueTask<EvalResult<ZeroArgPropertyResult>> InvokeAsync(
        ZeroArgPropertyCacheKey key,
        Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
        => _published.ContainsKey(key) ? evaluateAsync() : EvaluateMissAsync(key, evaluateAsync);

    /// <summary>MIRROR OF <see cref="EvaluateMiss"/> — keep in lock-step.</summary>
    internal async ValueTask<EvalResult<ZeroArgPropertyResult>> EvaluateMissAsync(
        ZeroArgPropertyCacheKey key,
        Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
    {
        if (!_active.Add(key))
            return await evaluateAsync().ConfigureAwait(false);

        EvalResult<ZeroArgPropertyResult> result;
        try
        {
            result = await evaluateAsync().ConfigureAwait(false);
        }
        finally
        {
            _active.Remove(key);
        }

        if (!result.IsError && _published.TryAdd(key, result.Value))
            sink?.Published(key, result.Value);
        return result;
    }
}

internal sealed class UncachedZeroArgPropertyResultCache : IZeroArgPropertyResultCache
{
    private readonly HashSet<ZeroArgPropertyCacheKey>? _seenKeys;
    private readonly ZeroArgPropertyResultCacheStatsCollector? _stats;
    private int _repeatedMissRequests;

    /// <summary>
    /// Shared STATELESS pass-through instance. It records no bookkeeping at all:
    /// this singleton is process-wide, thread safety in evaluation is by
    /// per-run isolation (see <see cref="EvaluationBudget"/>), and the seen-key
    /// tracking holds strong references to the run's algorithms, bindings, and
    /// environments — a shared mutable set was both a concurrency corruption
    /// source and an unbounded process-lifetime retention of every evaluated
    /// AST. Use <see cref="CreateForRun"/> when snapshot statistics are wanted.
    /// </summary>
    public static UncachedZeroArgPropertyResultCache Instance { get; } = new(trackStatistics: false);

    internal static UncachedZeroArgPropertyResultCache CreateForRun()
        => new(trackStatistics: true);

    private UncachedZeroArgPropertyResultCache(bool trackStatistics)
    {
        if (trackStatistics)
        {
            _seenKeys = new(ZeroArgPropertyCacheKeyComparer.Instance);
            _stats = new();
        }
    }

    public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate)
    {
        if (_stats is null || _seenKeys is null)
            return evaluate();

        var key = ZeroArgPropertyCacheKey.FromExecution(execution);
        _stats.RecordRequest(execution.AccessKind);
        _stats.RecordMiss(execution.AccessKind);

        if (!_seenKeys.Add(key))
            _repeatedMissRequests++;

        return evaluate();
    }

    /// <summary>A cache that stores nothing publishes nothing: an invocation simply executes.</summary>
    public EvalResult<ZeroArgPropertyResult> Invoke(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        => evaluate();

    public ZeroArgPropertyResultCacheSnapshot GetSnapshot()
        => (_stats ?? new ZeroArgPropertyResultCacheStatsCollector()).CreateSnapshot(
            distinctKeysCreated: _seenKeys?.Count ?? 0,
            repeatedMissRequests: _repeatedMissRequests,
            maxCacheSize: 0);
}

internal sealed class RunScopedZeroArgPropertyResultCache(RootPropertyObservationSink? observationSink = null)
    : IZeroArgPropertyResultCache
{
    private readonly ZeroArgPropertyPublications _results = new(observationSink);
    private readonly HashSet<ZeroArgPropertyCacheKey> _seenKeys = new(ZeroArgPropertyCacheKeyComparer.Instance);
    private readonly HashSet<ZeroArgPropertyCacheKey> _missedKeysWithoutStore = new(ZeroArgPropertyCacheKeyComparer.Instance);
    private readonly ZeroArgPropertyResultCacheStatsCollector _stats = new();
    private int _repeatedMissRequests;
    private int _maxCacheSize;

    public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate)
    {
        var key = ZeroArgPropertyCacheKey.FromExecution(execution);
        _stats.RecordRequest(execution.AccessKind);
        _seenKeys.Add(key);

        if (_results.TryGetPublished(key, out var cached))
        {
            _stats.RecordHit(execution.AccessKind);
            return EvalResult<ZeroArgPropertyResult>.Ok(cached);
        }

        _stats.RecordMiss(execution.AccessKind);
        if (!_missedKeysWithoutStore.Add(key))
            _repeatedMissRequests++;

        // A re-entrant miss (an outer evaluation of this key is still running) evaluates
        // but never publishes; the outermost successful evaluation publishes (Q-37).
        var result = _results.EvaluateMiss(key, evaluate, out var published);
        if (result.IsError)
            return result.Error;

        if (published)
        {
            _stats.RecordStore(execution.AccessKind);
            _missedKeysWithoutStore.Remove(key);
            if (_results.Count > _maxCacheSize)
                _maxCacheSize = _results.Count;
        }

        return result;
    }

    /// <summary>
    /// A qualifying explicit zero-supply invocation (CACHE-PUB-1): never a request of the read
    /// statistics (it is no property-style access and can never hit); an owning publication is
    /// counted as a store of the <see cref="ZeroArgPropertyAccessKind.Invocation"/> kind.
    /// </summary>
    public EvalResult<ZeroArgPropertyResult> Invoke(
        ZeroArgPropertyExecution execution,
        Func<EvalResult<ZeroArgPropertyResult>> evaluate)
    {
        var key = ZeroArgPropertyCacheKey.FromExecution(execution);
        var result = _results.Invoke(key, evaluate, out var published);
        if (published)
        {
            _stats.RecordStore(ZeroArgPropertyAccessKind.Invocation);
            _missedKeysWithoutStore.Remove(key);
            if (_results.Count > _maxCacheSize)
                _maxCacheSize = _results.Count;
        }

        return result;
    }

    /// <summary>Keys whose owning evaluation is still running (zero between accesses).</summary>
    internal int ActiveOwnerCount => _results.ActiveOwnerCount;

    public bool ReadObtainsPublishedValue(ZeroArgPropertyCacheKey key) => _results.ReadObtainsPublishedValue(key);

    public ZeroArgPropertyResultCacheSnapshot GetSnapshot()
        => _stats.CreateSnapshot(
            distinctKeysCreated: _seenKeys.Count,
            repeatedMissRequests: _repeatedMissRequests,
            maxCacheSize: _maxCacheSize);
}
