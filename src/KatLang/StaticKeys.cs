using System.Collections.Immutable;
using System.Runtime.CompilerServices;

namespace KatLang;

/// <summary>
/// B3-1: the identity of one static scope — a body in its declaring context — shared by every front-end pass and the
/// static query engine (<c>docs/design/static-structure-resolver-2026-10.md</c> § 9). It is the interned form of the
/// declaration chain <c>OpenProviderIdentity</c> already compares: the owner declaration, then the enclosing levels'
/// outward, ending at the root level — the prelude every chain is rooted at — where a loaded module restarts (Q-31 H-P).
/// Ordinary declaration scopes agree with provider identity. A branch binding region additionally distinguishes a
/// host-shared body under different patterns; declaration chains alone cannot describe those bindings. A module
/// declaration still has one key wherever it is held (Q-32 I-U).
/// Compared by reference; created only by a <c>StaticKeyTable</c>.
/// </summary>
internal sealed class StaticScopeKey
{
    private static long _nextRequirementIdentity;
    // A unique ephemeral cache label, never a language identity or graph representative.
    internal long RequirementIdentity { get; } = Interlocked.Increment(ref _nextRequirementIdentity);

    internal StaticScopeKey(StaticScopeKey? parent, object declaration, object? bindingRegion = null)
    {
        Parent = parent;
        Declaration = declaration;
        BindingRegion = bindingRegion;
        Depth = parent is null ? 0 : parent.Depth + 1;
    }

    /// <summary>The enclosing scope's key; null for the root level.</summary>
    public StaticScopeKey? Parent { get; }

    /// <summary>
    /// The owner declaration: a body's <c>DeclarationIdentity</c> (shared by every <c>with</c> copy the passes make), the body
    /// itself when it has none, or the root-level sentinel.
    /// </summary>
    public object Declaration { get; }

    /// <summary>The stable written branch pattern when this body owns branch binders; otherwise null.</summary>
    public object? BindingRegion { get; }

    /// <summary>The number of levels between this scope and the root level.</summary>
    public int Depth { get; }

    public override string ToString() => $"scope#{RuntimeHelpers.GetHashCode(this):x8}@{Depth}";
}

/// <summary>
/// One front-end operation's table of static scope keys (B3-1), and the adapters that map each pass's own scope
/// structure to them: the parameter detector's and the editor's <c>ElaboratedPropertyScope</c>, implicit-argument
/// resolution's <c>DeclaringOwners</c> chains and <c>ResolverLevel</c>s. Every adapter follows the one chain rule
/// <c>OpenProviderIdentity</c> states (<c>AppendChain</c>, <c>DeclaringOwners.Inside</c>), so the passes name the same
/// key for the same level. Not thread-safe; scope objects are remembered by reference.
/// </summary>
internal sealed class StaticKeyTable
{
    private ImmutableDictionary<(StaticScopeKey Parent, object Declaration, object? Region), StaticScopeKey> _scopes
        = ImmutableDictionary.Create<(StaticScopeKey Parent, object Declaration, object? Region), StaticScopeKey>(ChildComparer.Instance);
    private readonly Dictionary<DeclaringOwners, StaticScopeKey> _owners = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<ElaboratedPropertyScope, StaticScopeKey> _levels = new(ReferenceEqualityComparer.Instance);
    private ImmutableDictionary<(StaticScopeKey Parent, object Definition, object? Region), StaticScopeKey> _definitions
        = ImmutableDictionary.Create<(StaticScopeKey, object, object?), StaticScopeKey>(ChildComparer.Instance);
    private ImmutableDictionary<(StaticScopeKey Parent, object Declaration, object? Region), Algorithm> _firstDefinitions
        = ImmutableDictionary.Create<(StaticScopeKey, object, object?), Algorithm>(ChildComparer.Instance);
    private ImmutableDictionary<StaticScopeKey, StaticScopeKey> _providerScopes
        = ImmutableDictionary.Create<StaticScopeKey, StaticScopeKey>(ReferenceEqualityComparer.Instance);

    public StaticKeyTable() => Root = new StaticScopeKey(null, OpenProviderIdentity.RootLevelDeclaration);

    private StaticKeyTable(StaticScopeKey root) => Root = root;

    /// <summary>Preserves interned source identities without retaining a previous pass's physical scope adapters.</summary>
    internal StaticKeyTable Fork(CancellationToken cancellationToken = default)
    {
        cancellationToken.ThrowIfCancellationRequested();
        var copy = new StaticKeyTable(Root) { _scopes = _scopes, _definitions = _definitions,
            _firstDefinitions = _firstDefinitions, _providerScopes = _providerScopes };
        return copy;
    }

    /// <summary>The root level: the prelude every chain is rooted at, and the document root's own level.</summary>
    public StaticScopeKey Root { get; }

    /// <summary>The number of distinct scope keys below the root level.</summary>
    public int Count => _scopes.Count + _definitions.Count;
    internal long DefinitionIdentityStorageUnits => 2L * _firstDefinitions.Count;

    /// <summary>
    /// A graph representative for one immutable source object. Distinct host views may share a language declaration
    /// without being the same definition. Only this operation's table retains their source-object index; a published
    /// key keeps declaration/pattern/parent identities, with no reference back to this table or the source AST.
    /// </summary>
    internal StaticScopeKey DefinitionIn(StaticScopeKey parent, Algorithm body, object? region,
        StaticQueryResourceBudget resources, object? ownerIdentity = null, CancellationToken cancellationToken = default)
    {
        if (body.IsModuleRoot) return BodyIn(Root, body);
        if (_definitions.TryGetValue((parent, body, region), out var key)) return key;
        resources.Metadata(4, cancellationToken: cancellationToken);
        key = new StaticScopeKey(parent, ownerIdentity ?? OpenProviderIdentity.DeclarationOf(body), region);
        _definitions = _definitions.Add((parent, body, region), key);
        var declared = (parent, OpenProviderIdentity.DeclarationOf(body), region);
        if (!_firstDefinitions.ContainsKey(declared))
        {
            resources.Metadata(2, cancellationToken: cancellationToken);
            _firstDefinitions = _firstDefinitions.Add(declared, body);
        }
        return key;
    }

    internal Algorithm? FirstDefinitionIn(StaticScopeKey parent, Algorithm body, object? region)
        => _firstDefinitions.GetValueOrDefault((body.IsModuleRoot ? Root : parent,
            OpenProviderIdentity.DeclarationOf(body), body.IsModuleRoot ? null : region));

    internal StaticScopeKey? KnownDefinitionIn(StaticScopeKey parent, Algorithm body, object? region)
        => _definitions.GetValueOrDefault((body.IsModuleRoot ? Root : parent, body, body.IsModuleRoot ? null : region));

    /// <summary>The provider's language identity, independent of its source/view graph representative.</summary>
    internal StaticScopeKey ProviderScope(StaticScopeKey scope, StaticQueryResourceBudget resources,
        CancellationToken cancellationToken = default)
    {
        resources.Metadata(0, cancellationToken: cancellationToken);
        if (ReferenceEquals(scope, Root)) return Root;
        if (_providerScopes.TryGetValue(scope, out var known)) return known;
        var path = new Stack<StaticScopeKey>();
        var at = scope;
        while (!ReferenceEquals(at, Root) && !_providerScopes.TryGetValue(at, out known))
        {
            resources.Metadata(4, cancellationToken: cancellationToken);
            path.Push(at);
            at = at.Parent ?? Root;
        }
        known = ReferenceEquals(at, Root) ? Root : known!;
        while (path.TryPop(out var next))
        {
            known = Inside(known, next.Declaration);
            _providerScopes = _providerScopes.Add(next, known);
        }
        return known;
    }

    /// <summary>The key of the level owned by <paramref name="declaration"/> directly inside <paramref name="parent"/>.</summary>
    public StaticScopeKey Inside(StaticScopeKey parent, object declaration, object? bindingRegion = null)
    {
        ArgumentNullException.ThrowIfNull(parent);
        ArgumentNullException.ThrowIfNull(declaration);
        if (!_scopes.TryGetValue((parent, declaration, bindingRegion), out var key))
            _scopes = _scopes.Add((parent, declaration, bindingRegion), key = new StaticScopeKey(parent, declaration, bindingRegion));
        return key;
    }

    /// <summary>The key of the body <paramref name="body"/> nested in <paramref name="parent"/>: a loaded module restarts at the root level.</summary>
    public StaticScopeKey BodyIn(StaticScopeKey parent, Algorithm body, object? bindingRegion = null)
    {
        ArgumentNullException.ThrowIfNull(body);
        return Inside(body.IsModuleRoot ? Root : parent, OpenProviderIdentity.DeclarationOf(body), body.IsModuleRoot ? null : bindingRegion);
    }

    /// <summary>Implicit-argument resolution's declaring chain (<c>DeclaringOwners</c>): its root is the root level.</summary>
    public StaticScopeKey ScopeOf(DeclaringOwners owners)
    {
        ArgumentNullException.ThrowIfNull(owners);
        if (_owners.TryGetValue(owners, out var known))
            return known;

        // Outward to the first remembered link (or the root), then inward: no recursion, however deep the chain.
        var chain = new List<DeclaringOwners>();
        for (var current = owners; current is not null && !_owners.ContainsKey(current); current = current.Outer)
            chain.Add(current);
        for (var i = chain.Count - 1; i >= 0; i--)
        {
            var link = chain[i];
            _owners[link] = link.Outer is null ? Root : Inside(_owners[link.Outer], link.Declaration);
        }

        return _owners[owners];
    }

    /// <summary>A resolver level: the key of its declaring owners.</summary>
    public StaticScopeKey ScopeOf(ImplicitArgumentResolver.ResolverLevel level)
    {
        ArgumentNullException.ThrowIfNull(level);
        if (level.StaticContext is { } context) return AttachedKey(context);
        return ScopeOf(level.Owners);
    }

    /// <summary>
    /// The parameter detector's (and the editor's) level: a level with no parent is the root level, a loaded module's level
    /// is declared at the root level wherever it is held, and every other level is its owner declaration inside its
    /// parent — <c>OpenProviderIdentity</c>'s <c>AppendChain</c>.
    /// </summary>
    public StaticScopeKey ScopeOf(ElaboratedPropertyScope level)
    {
        ArgumentNullException.ThrowIfNull(level);
        if (level.StaticContext is { } context) return AttachedKey(context);
        if (_levels.TryGetValue(level, out var known))
            return known;

        var chain = new List<ElaboratedPropertyScope>();
        for (var current = level; current is not null && !_levels.ContainsKey(current); current = current.Parent)
            chain.Add(current);
        for (var i = chain.Count - 1; i >= 0; i--)
        {
            var link = chain[i];
            _levels[link] = link.Parent is null
                ? Root
                : Inside(link.IsModuleLevel ? Root : _levels[link.Parent], link.OwnerDeclaration);
        }

        return _levels[level];
    }

    private StaticScopeKey AttachedKey(StaticStructureContext context)
        => ReferenceEquals(context.Operation.Queries.Keys.Root, Root) ? context.Key
            : throw new InvalidOperationException("A physical scope belongs to another static operation's key table.");

    private sealed class ChildComparer : IEqualityComparer<(StaticScopeKey Parent, object Declaration, object? Region)>
    {
        public static ChildComparer Instance { get; } = new();

        public bool Equals((StaticScopeKey Parent, object Declaration, object? Region) x, (StaticScopeKey Parent, object Declaration, object? Region) y)
            => ReferenceEquals(x.Parent, y.Parent) && ReferenceEquals(x.Declaration, y.Declaration) && ReferenceEquals(x.Region, y.Region);

        public int GetHashCode((StaticScopeKey Parent, object Declaration, object? Region) obj)
            => HashCode.Combine(RuntimeHelpers.GetHashCode(obj.Parent), RuntimeHelpers.GetHashCode(obj.Declaration),
                obj.Region is null ? 0 : RuntimeHelpers.GetHashCode(obj.Region));
    }
}

/// <summary>The static query families of the B3 query catalog (design § 4).</summary>
internal enum StaticQueryKind : byte
{
    /// <summary>Q1: what a name selects in a scope, in one stratum.</summary>
    Binding,

    /// <summary>Q2: a level's open providers, in one stratum.</summary>
    OpenProviders,

    /// <summary>Q3: a body's static target walk (OD-D), in one stratum.</summary>
    TargetWalk,

    /// <summary>Q4: the members a structure declares.</summary>
    Members,

    /// <summary>Q5: whether a dot edge's fallback is selected (Never / MAY / MUST).</summary>
    MissSelection,

    /// <summary>Q6: whether a name is an inferred input of a body.</summary>
    IsInput,

    /// <summary>Q7: a body's ordered inferred inputs.</summary>
    Inputs,
}

/// <summary>Implementation projections within a query family, all resolved by the same engine.</summary>
internal enum StaticQueryProjection : byte
{
    Default,
    OwnedBinding,
    InferenceBinding,
    OpenedBinding,
    TargetCycle,
    RowTarget,
    Receiver,
    OpenTarget,
    ProviderRange,
    InputUse,
    ActivationRange,
    InputRange,
    OpenStructure,
    OpenRowTarget,
    InputUses,
    ReceiverExpansionCycle,
    ReceiverExpansionStep,
    OpenMatches,
    OpenMemberIndex,
    OpenPresenceWitnesses,
    PreservedOpenPresence,
    MemberSelection,
    OpenHeadBinding,
    OpenMemberAbsence,
    EmptyOpenNamespace,
    FallbackParticipation,
    InvocationTarget,
}

/// <summary>
/// The key of one static query (B3-1): its family, the scope it is asked in, and — by family — a name, a stratum and the
/// expression node it is about. Scopes and nodes compare by REFERENCE (an <c>Expr</c> record's own equality is
/// structural: two equal edges written twice are two questions), names ordinally.
/// </summary>
internal readonly struct StaticQueryKey : IEquatable<StaticQueryKey>
{
    private StaticQueryKey(StaticQueryKind kind, StaticScopeKey scope, string? name, StaticCycleCheck stratum, Expr? node,
        StaticQueryProjection projection = default, int offset = 0, int length = 0)
    {
        ArgumentNullException.ThrowIfNull(scope);
        Kind = kind;
        Scope = scope;
        Name = name;
        Stratum = stratum;
        Node = node;
        Projection = projection;
        Offset = offset;
        Length = length;
    }

    public StaticQueryKind Kind { get; }

    public StaticScopeKey Scope { get; }

    public string? Name { get; }

    public StaticCycleCheck Stratum { get; }

    public Expr? Node { get; }

    public StaticQueryProjection Projection { get; }
    public int Offset { get; }
    public int Length { get; }

    internal static StaticQueryKey Project(StaticQueryKind kind, StaticScopeKey scope, StaticQueryProjection projection,
        string? name = null, StaticCycleCheck stratum = StaticCycleCheck.Formation, Expr? node = null, int offset = 0, int length = 0)
        => new(kind, scope, name, stratum, node, projection, offset, length);

    public static StaticQueryKey Binding(StaticScopeKey scope, string name, StaticCycleCheck stratum)
        => new(StaticQueryKind.Binding, scope, name ?? throw new ArgumentNullException(nameof(name)), stratum, null);

    public static StaticQueryKey OpenProviders(StaticScopeKey level, StaticCycleCheck stratum)
        => new(StaticQueryKind.OpenProviders, level, null, stratum, null);

    public static StaticQueryKey TargetWalk(StaticScopeKey body, StaticCycleCheck stratum)
        => new(StaticQueryKind.TargetWalk, body, null, stratum, null);

    public static StaticQueryKey Members(StaticScopeKey structure)
        => new(StaticQueryKind.Members, structure, null, default, null);

    public static StaticQueryKey MissSelection(StaticScopeKey level, Expr.DotCall edge)
        => new(StaticQueryKind.MissSelection, level, null, default, edge ?? throw new ArgumentNullException(nameof(edge)));

    public static StaticQueryKey IsInput(StaticScopeKey body, string name)
        => new(StaticQueryKind.IsInput, body, name ?? throw new ArgumentNullException(nameof(name)), default, null);

    public static StaticQueryKey Inputs(StaticScopeKey body)
        => new(StaticQueryKind.Inputs, body, null, default, null);

    public bool Equals(StaticQueryKey other)
        => Kind == other.Kind
            && ReferenceEquals(Scope, other.Scope)
            && string.Equals(Name, other.Name, StringComparison.Ordinal)
            && Stratum == other.Stratum
            && ReferenceEquals(Node, other.Node)
            && Projection == other.Projection && Offset == other.Offset && Length == other.Length;

    public override bool Equals(object? obj) => obj is StaticQueryKey other && Equals(other);

    public override int GetHashCode()
        => HashCode.Combine(
            Kind,
            RuntimeHelpers.GetHashCode(Scope),
            Name is null ? 0 : StringComparer.Ordinal.GetHashCode(Name),
            Stratum,
            Node is null ? 0 : RuntimeHelpers.GetHashCode(Node), Projection, Offset, Length);

    public override string ToString() => $"{Kind}.{Projection}({Scope}{(Name is null ? "" : $", {Name}")}{(Node is null ? "" : ", node")}, {Stratum}, {Offset}+{Length})";
}
