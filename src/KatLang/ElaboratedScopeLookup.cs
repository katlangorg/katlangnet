namespace KatLang;

/// <summary>
/// Tiny adapter over elaborated AST property scopes for front-end and editor lookup.
/// This intentionally excludes evaluator-specific runtime behavior.
///
/// <para><b>Acceleration caches (M18):</b> each level lazily carries a
/// property-name index and its resolved <c>open</c> providers, and the chain
/// root is captured at construction. All three are pure acceleration over the
/// ordered data this level was built from — the ordered <see cref="Properties"/>
/// list remains the semantic authority for enumeration, ordering, and
/// diagnostics, and every cached answer is exactly what the linear walk over it
/// selects (first occurrence wins by declaration identity). The caches are safe
/// because an ordinary scope chain is confined to ONE single-threaded front-end
/// operation (a parameter detection, a semantic-model build, or a suggestion
/// computed inside one of those): every operation builds a fresh chain, level
/// property lists are snapshotted at construction, and <see cref="Property"/> is
/// an immutable record. Host mutation concurrent with a front-end operation is
/// unsupported; mutation between operations is observed by the next fresh chain.
/// The semantic model's one process-shared prelude level is the deliberate
/// exception: its immutable source and every reachable lazy lookup cache are
/// prewarmed before the level is published.</para>
///
/// <para><b>Shared open-target member indexes:</b> an <c>open</c> provider's
/// public-member index is a pure function of its target's ordered property list
/// (<see cref="OpenTargetMemberIndex"/>), so every provider of the SAME target object
/// within one operation shares one index through the operation's
/// <see cref="OpenMemberIndexCache"/> (<see cref="MemberIndexes"/>): K levels opening
/// one W-member target cost O(K + W), not O(K × W). The operation creates the cache
/// with its chain (at the chain's root, or — for the semantic model, whose chains
/// hang under the process-shared prelude level — at every level it derives from that
/// level), every level derived from a level inherits it, and it is reachable only
/// from that operation's chain: never from a target, never from the process-shared
/// prelude level, never static. A chain retained past its operation for a deferred
/// module region's demand-time continuation keeps its cache with it; those
/// continuations belong to the same parse and are serialized by its loader's
/// materialization gate, so the cache is never used by two operations at once. Only
/// the target index is shared: which providers a level has, their dedup, ambiguity,
/// and precedence stay per level.</para>
/// </summary>
internal sealed class ElaboratedPropertyScope
{
    private Dictionary<string, int>? _nameIndex;
    private int _firstNullNameIndex = -1;
    private HashSet<string>? _ownParameterNames;
    private readonly IReadOnlyList<PropertyLookupHit> _properties;
    private Algorithm? _completedPropertyView;
    private IReadOnlyList<PropertyLookupHit>? _completedProperties;
    private IReadOnlyList<ResolvedOpenProvider>? _completedProviders;
    private int _completedProviderVersion = -1;

    public ElaboratedPropertyScope(
        ElaboratedPropertyScope? parent,
        IReadOnlyList<Expr> opens,
        IReadOnlyList<PropertyLookupHit> properties,
        FrontEndTraversalObservations? observations = null,
        OpenMemberIndexCache? memberIndexes = null,
        Algorithm? owner = null,
        StaticStructureContext? staticContext = null,
        CompletedStructureContext? completedContext = null,
        Pattern? branchPattern = null,
        StaticAstPhase? sourcePhase = null,
        Algorithm? sourceBody = null,
        object? ownerIdentity = null,
        StandaloneScopeAnalysis? standaloneAnalysis = null)
    {
        // A loaded module is a source unit rooted at the prelude (Q-31 H-P): its level's enclosing
        // level is the chain's root level wherever it is held, so no lookup from inside it — by any
        // pass, the editor included — ever reaches the holder's names.
        CompletedContext = completedContext ?? (staticContext is null && parent?.StaticContext is null
            ? CompletedStructureContext.For(owner, parent, branchPattern) : null);
        if (owner?.IsModuleRoot == true && parent is not null)
            parent = parent.Root;

        BranchPattern = branchPattern;
        Parent = parent;
        Opens = opens;
        _properties = properties;
        Observations = parent?.Observations ?? observations;
        Root = parent is null ? this : parent.Root;
        MemberIndexes = memberIndexes ?? parent?.MemberIndexes;
        OwnerAlgorithm = owner;
        OwnerDeclaration = ownerIdentity ?? owner?.Declaration ?? (object?)owner ?? new object();
        SourceBody = sourceBody ?? owner ?? new Algorithm.User(null, [], opens, properties.Select(hit => hit.Property).ToArray(), []);
        SourcePhase = sourcePhase ?? (owner?.CompletedStructure is not null ? StaticAstPhase.Resolved : parent?.SourcePhase);
        _standaloneAnalysis = standaloneAnalysis;
        IsModuleLevel = owner?.IsModuleRoot == true;
        HasOpensInChain = opens.Count > 0 || parent?.HasOpensInChain == true;
        StaticContext = staticContext ?? (owner is null ? null : parent?.StaticContext?.Inside(owner));
        if (CompletedContext is { } completed) MemberIndexes?.CompletedLevels.TryAdd((completed.Facts, completed.Key), this);
    }

    /// <summary>The admitting operation shared by the compiler passes.</summary>
    internal StaticStructureContext? StaticContext { get; }
    internal Pattern? BranchPattern { get; }
    internal CompletedStructureContext? CompletedContext { get; }

    /// <summary>
    /// Whether this level is a loaded module's own body (Q-31 H-P): a declaration at the root level
    /// wherever it is held, so a declaring chain restarts there (<see cref="OpenProviderIdentity"/>).
    /// </summary>
    internal bool IsModuleLevel { get; }

    /// <summary>
    /// Whether this level or an enclosing one declares an <c>open</c> target: whether a name
    /// lookup from here can reach an open level at all (a pure fast path — the open fallback of a
    /// chain without opens provides nothing).
    /// </summary>
    internal bool HasOpensInChain { get; }

    /// <summary>
    /// The declaration whose body this level is — the algorithm the level was created from
    /// (its <see cref="Algorithm.Declaration"/>, so every <c>with</c> view of one written body is
    /// one owner) — or, for a level built without an owner, the level itself. One element of a
    /// provider's declaring-owner chain (<see cref="OpenProviderIdentity"/>).
    /// </summary>
    internal object OwnerDeclaration { get; }

    /// <summary>The algorithm this level was created from, or null for a level built without one.</summary>
    internal Algorithm? OwnerAlgorithm { get; }

    /// <summary>
    /// The owning operation's shared open-target member indexes (see the class remarks):
    /// supplied where the operation creates a level, otherwise inherited from the parent.
    /// Null for the semantic model's process-shared prelude level (and any chain created
    /// without one), whose providers then build private indexes exactly as before.
    /// </summary>
    public OpenMemberIndexCache? MemberIndexes { get; }

    public ElaboratedPropertyScope? Parent { get; }

    public IReadOnlyList<Expr> Opens { get; }

    public IReadOnlyList<PropertyLookupHit> Properties
    {
        get
        {
            var view = CompletedContext?.Facts.Facts(CompletedContext.Key)?.Body;
            if (view is null || ReferenceEquals(view, OwnerAlgorithm)) return _properties;
            if (!ReferenceEquals(view, _completedPropertyView))
            {
                _completedPropertyView = view;
                _completedProperties = view.Properties.Select(property => new PropertyLookupHit(view, property)).ToArray();
            }
            return _completedProperties!;
        }
    }

    /// <summary>
    /// The chain's outermost level, captured at construction (parent links are
    /// immutable, so it is invariant per chain). Detection and semantic-model
    /// chains root at the prelude scope their pass created, so open-target
    /// processing and prelude-shadow decisions anchor here without re-walking
    /// parent links per query.
    /// </summary>
    public ElaboratedPropertyScope Root { get; }

    /// <summary>
    /// Passive lookup-work observer inherited from the chain root (see
    /// <see cref="FrontEndTraversalObservations"/>). Null on production paths.
    /// </summary>
    public FrontEndTraversalObservations? Observations { get; }

    /// <summary>
    /// This level's own first declaration for <paramref name="name"/>, exactly
    /// as the linear scan of <see cref="Properties"/> selects it: the FIRST
    /// list entry whose property name is ordinal-equal wins, later same-name
    /// entries are ignored. Served from a lazy name→first-index map; the index
    /// exists for lookup only and is never an enumeration source.
    /// </summary>
    public PropertyLookupHit? TryLookupOwnProperty(string name)
    {
        var properties = Properties;
        if (properties.Count == 0)
            return null;

        var index = _nameIndex;
        if (index is null)
        {
            Observations?.RecordLookupNameIndexBuild();
            index = new Dictionary<string, int>(properties.Count, StringComparer.Ordinal);
            for (var i = 0; i < properties.Count; i++)
            {
                if (properties[i].Property.Name is { } propertyName)
                    index.TryAdd(propertyName, i);
                else if (_firstNullNameIndex < 0)
                    _firstNullNameIndex = i;
            }

            _nameIndex = index;
        }

        if (name is null)
            return _firstNullNameIndex >= 0 ? properties[_firstNullNameIndex] : null;

        return index.TryGetValue(name, out var propertyIndex) ? properties[propertyIndex] : null;
    }

    /// <summary>Reads the operation's Q2 providers or its completed immutable projection.</summary>
    public IReadOnlyList<ResolvedOpenProvider> GetResolvedOpenProviders(StaticCycleCheck stratum = StaticCycleCheck.Formation)
    {
        if (StaticContext is { } context) return context.Operation.Providers(context.Key, stratum);
        if (CompletedContext is { } completed)
        {
            completed.Facts.EnsureUsable();
            if (_completedProviders is null || _completedProviderVersion != completed.Facts.ViewVersion)
            {
                _completedProviders = completed.Providers(this);
                _completedProviderVersion = completed.Facts.ViewVersion;
            }
            return _completedProviders;
        }
        if (Opens.Count == 0) return [];
        var analyzed = BoundLookupContext();
        analyzed.Facts.EnsureUsable();
        if (_completedProviders is null || _completedProviderVersion != analyzed.Facts.ViewVersion)
        {
            _completedProviders = analyzed.Providers(this);
            _completedProviderVersion = analyzed.Facts.ViewVersion;
        }
        return _completedProviders;
    }

    /// <summary>
    /// Builds this level's lookup caches immediately. Ordinary chains are
    /// confined to one single-threaded front-end operation and stay lazy; the
    /// ONE legitimately long-lived shared level — the semantic model's static
    /// prelude scope, whose source algorithm is itself immutable for the
    /// process — prewarms at creation so the shared instance never mutates
    /// afterwards and concurrent semantic-model builds touch only immutable
    /// state.
    /// </summary>
    internal void PrewarmSharedLookupCaches()
    {
        _ = TryLookupOwnProperty(string.Empty);
        foreach (var provider in GetResolvedOpenProviders())
            provider.PrewarmSharedLookupCaches();
    }

    /// <summary>
    /// The parameter bindings in force INSIDE this level as parameter detection established them —
    /// attached by the detector when it enters the body (its written inputs) and again once inference
    /// knows the rest; null on every other pass's levels, whose trees already carry each parameter-owned
    /// name as <see cref="Expr.Param"/>. The static structure chase reads THIS level's own answer
    /// (<see cref="BindsParameter"/>) for a body that is still a written name (M4★): a parameter binding
    /// nearer than a same-named property makes it a runtime reference, and a level whose bindings are
    /// established is one where a name nothing declares is certainly an inferred input.
    /// </summary>
    internal IOwnedParameterBindings? ParameterBindings { get; set; }

    /// <summary>
    /// Whether THIS level itself binds <paramref name="name"/> as a parameter (M4★): by the bindings
    /// parameter detection established for it — its written and inferred inputs, a branch's binders —
    /// otherwise by the written parameters of the algorithm the level was created from (a body a static
    /// chase navigated into). A level's own answer, never a site's: the static structure chase walks from a
    /// reference's OWN scope outward, so a parameter a site shadows, or a body the chase reached by another
    /// route, answers alike wherever the chase started (<see cref="ElaboratedScopeLookup.StaticStructureWithScopeAt"/>).
    /// </summary>
    internal bool BindsParameter(string name)
    {
        if (ParameterBindings is { } bindings)
            return bindings.DeclaresParameter(this, name);
        if (CompletedContext is { } completed && completed.Facts.Facts(completed.Key) is { } facts)
            return facts.Parameters.Contains(name);
        if (BranchPattern is { } pattern && pattern.BoundNames().Contains(name, StringComparer.Ordinal)) return true;
        if (SourceBody is not Algorithm.User { ParameterPatterns.Count: > 0 } user)
            return false;
        _ownParameterNames ??= new HashSet<string>(user.Params, StringComparer.Ordinal);
        return _ownParameterNames.Contains(name);
    }

    private StandaloneScopeAnalysis? _standaloneAnalysis;
    internal Algorithm SourceBody { get; }
    internal StaticAstPhase? SourcePhase { get; }
    internal StandaloneScopeAnalysis StandaloneAnalysis(CancellationToken cancellationToken = default)
    {
        cancellationToken.ThrowIfCancellationRequested();
        if (_standaloneAnalysis is not null) return _standaloneAnalysis;
        if (SourcePhase is not { } phase || Parent is null)
            throw new InvalidOperationException("Standalone structural lookup requires explicit source phase/admission provenance.");
        // Parent facts are immutable. The new unit admits only this supplied body and its local descendants.
        return _standaloneAnalysis = Parent.StandaloneAnalysis(cancellationToken).Inside(
            SourceBody, BranchPattern, phase, OwnerAlgorithm is null ? OwnerDeclaration : null, cancellationToken);
    }
    internal CompletedStructureContext BoundLookupContext()
        => CompletedContext ?? StandaloneAnalysis().Context;

}

/// <summary>
/// One resolved <c>open</c> provider of a scope level, caching the exact target
/// algorithm the level's open declaration resolved to. Member lookup is served
/// from the target's <see cref="OpenTargetMemberIndex"/> — shared with every other
/// provider of the same target in the owning operation (<see cref="OpenMemberIndexCache"/>),
/// or built privately when the level has no cache — which replicates
/// <see cref="ElaboratedScopeLookup.TryLookupPublicProperty(Algorithm, string)"/> exactly: the
/// first list entry that matches the name AND is public wins (a private
/// same-name entry earlier in the list is skipped, never an answer). Exposure
/// takes no part in SELECTION — a public local-only member is provided by its
/// open like any other, and whether a site may use it is checked after selection
/// (the evaluator's accessibility law) — which is what lets detection, which runs
/// before exposure is classified, select exactly what the evaluator selects.
/// The target's ordered property list remains the enumeration source for
/// visible-name gathering. Everything scope-dependent — whether this provider is
/// active at a level, its dedup, and ambiguity with the level's other providers —
/// stays with the level; the provider only answers "which member does THIS target
/// provide under this name".
/// </summary>
internal sealed class ResolvedOpenProvider
{
    private readonly FrontEndTraversalObservations? _observations;
    private readonly OpenMemberIndexCache? _memberIndexes;
    private OpenTargetMemberIndex? _index;

    public ResolvedOpenProvider(
        Algorithm target,
        FrontEndTraversalObservations? observations,
        OpenMemberIndexCache? memberIndexes = null,
        OpenProviderIdentity? identity = null)
    {
        Target = target;
        _observations = observations;
        _memberIndexes = memberIndexes;
        Identity = identity;
    }

    public Algorithm Target { get; }

    /// <summary>The provider's semantic identity (<see cref="OpenProviderIdentity"/>) when its level resolved it; null for a host-built provider.</summary>
    public OpenProviderIdentity? Identity { get; }

    /// <summary>The first written open target of the level that resolved to this provider (diagnostics only).</summary>
    public Expr? Written { get; init; }

    /// <summary>
    /// The level that DECLARES the provider (M4★): a member it provides is declared in the provider's own
    /// body inside this level, which is where a member that is a reference is followed. Null for a
    /// host-built provider.
    /// </summary>
    public ElaboratedPropertyScope? Level { get; init; }

    public PropertyLookupHit? TryLookupPublicMember(string name)
    {
        var index = _index;
        if (index is null)
        {
            if (_memberIndexes is { } shared)
            {
                index = shared.IndexOf(Target);
            }
            else
            {
                _observations?.RecordLookupOpenMemberIndexBuild();
                index = OpenTargetMemberIndex.Build(Target);
            }

            _index = index;
        }

        return index.Lookup(name);
    }

    internal void PrewarmSharedLookupCaches()
        => _ = TryLookupPublicMember(string.Empty);
}

/// <summary>
/// The public-member index of ONE open target: for each ordinal name, the target's FIRST
/// PUBLIC property with that name (a private same-name entry is skipped, never an answer),
/// and the first public property with a null name. It reads nothing but the target's own
/// ordered property list — no scope, open declaration, provider, dedup, ambiguity, or
/// exposure fact — so it is invariant for the target object and immutable once built, which
/// is what lets every provider of that target within one operation share it.
/// </summary>
internal sealed class OpenTargetMemberIndex
{
    private readonly Algorithm _target;
    private readonly IReadOnlyList<Property> _properties;
    private readonly Dictionary<string, int> _firstPublicByName;
    private readonly int _firstPublicWithNullName;

    private OpenTargetMemberIndex(
        Algorithm target,
        IReadOnlyList<Property> properties,
        Dictionary<string, int> firstPublicByName,
        int firstPublicWithNullName)
    {
        _target = target;
        _properties = properties;
        _firstPublicByName = firstPublicByName;
        _firstPublicWithNullName = firstPublicWithNullName;
    }

    public static OpenTargetMemberIndex Build(Algorithm target)
    {
        var properties = target.Properties;
        var firstPublicByName = new Dictionary<string, int>(StringComparer.Ordinal);
        var firstPublicWithNullName = -1;
        for (var i = 0; i < properties.Count; i++)
        {
            var property = properties[i];
            if (!property.IsPublic)
                continue;

            if (property.Name is { } memberName)
                firstPublicByName.TryAdd(memberName, i);
            else if (firstPublicWithNullName < 0)
                firstPublicWithNullName = i;
        }

        return new OpenTargetMemberIndex(target, properties, firstPublicByName, firstPublicWithNullName);
    }

    /// <summary>The target member provided under <paramref name="name"/>, or null.</summary>
    public PropertyLookupHit? Lookup(string? name)
    {
        var position = name is null
            ? _firstPublicWithNullName
            : _firstPublicByName.TryGetValue(name, out var namedPosition) ? namedPosition : -1;
        return position >= 0 ? new PropertyLookupHit(_target, _properties[position]) : null;
    }
}

/// <summary>
/// ONE front-end operation's open-target member indexes, keyed by exact target identity
/// (reference, never record equality or spelling): the operation's providers of one target
/// share one immutable <see cref="OpenTargetMemberIndex"/>, built on first need. The owning
/// operation creates it with its scope chain (see <see cref="ElaboratedPropertyScope"/>'s
/// remarks); it is never static and never reachable from a target or from the
/// process-shared prelude level, so nothing outlives the chain it serves and no two parses
/// or model builds share it.
/// </summary>
internal sealed class OpenMemberIndexCache(FrontEndTraversalObservations? observations = null)
{
    private Dictionary<(StaticLookupFacts Facts, StaticScopeKey Key), ElaboratedPropertyScope>? _completedLevels;
    internal Dictionary<(StaticLookupFacts Facts, StaticScopeKey Key), ElaboratedPropertyScope> CompletedLevels => _completedLevels ??= new();
    internal void RecordCompletedRead() => observations?.RecordCompletedStaticStructureRead();
    private readonly Dictionary<Algorithm, OpenTargetMemberIndex> _indexes = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<ElaboratedPropertyScope, Dictionary<Algorithm, ElaboratedPropertyScope>> _bodyLevels = new();
    public ElaboratedPropertyScope BodyLevel(Algorithm body, ElaboratedPropertyScope parent)
    {
        if (!_bodyLevels.TryGetValue(parent, out var levels))
            _bodyLevels.Add(parent, levels = new(ReferenceEqualityComparer.Instance));
        if (!levels.TryGetValue(body, out var level)) levels.Add(body, level = ElaboratedScopeLookup.CreateScope(body, parent));
        return level;
    }
    internal int Count => _indexes.Count;
    public OpenTargetMemberIndex IndexOf(Algorithm target)
    {
        if (!_indexes.TryGetValue(target, out var index))
        {
            observations?.RecordLookupOpenMemberIndexBuild();
            _indexes.Add(target, index = OpenTargetMemberIndex.Build(target));
        }
        return index;
    }
}

internal readonly record struct PropertyLookupHit(Algorithm Owner, Property Property);

/// <summary>
/// The SEMANTIC identity of one <c>open</c> provider (Q-19 D-I, decided 2026-10-06): the
/// provider's declaration followed by the declarations of the owners that declare it, outward to
/// the chain's root level — the static form of the language's one callable identity (the
/// evaluator's <c>SameRepeatedCallableIdentity</c>: the same declaration in the same declaring
/// scope). Targets of one open level whose identities are equal are ONE provider, however they are
/// spelled: <c>open M, M</c>, <c>open M, (M)</c>, and <c>open Sub, Lib.Sub</c> for one declaration
/// <c>Sub</c> of <c>Lib</c>. A block written as an open target is declared at the root level (it is
/// wired to the prelude), so two written blocks are two providers however equal their members.
/// Identity never compares member names, member values, or source text. Every front-end consumer
/// that counts providers — elaborated lookup (and with it detection, the static ambiguity check and
/// the editor), exposure settlement, dependency analysis, and implicit-argument resolution — reads
/// this one identity (<see cref="ElaboratedScopeLookup.ResolveOpenProvider"/>).
/// </summary>
internal sealed class OpenProviderIdentity : IEquatable<OpenProviderIdentity>
{
    /// <summary>
    /// The chain's root level — the prelude every front-end chain is rooted at — as one element
    /// of every declaring chain, so identities computed over different chains of one program agree.
    /// </summary>
    private static readonly object RootLevel = new();

    // The provider's declaration first, then its declaring owners outward. Each element is a
    // declaration (DeclarationIdentity, compared by reference — one written declaration), the root
    // level, or, for a level or provider without a declaration, that object itself.
    private readonly object[] _declarations;
    private readonly int _hash;

    private OpenProviderIdentity(object[] declarations, bool complete)
    {
        _declarations = declarations;
        IsComplete = complete;
        var hash = new HashCode();
        hash.Add(complete);
        foreach (var declaration in declarations)
            hash.Add(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(declaration));
        _hash = hash.ToHashCode();
    }

    /// <summary>
    /// Whether the declaring chain is known all the way to the root level. The scope-free summary
    /// walk of exposure analysis (<see cref="PropertyDependencyGraphBuilder"/>) builds an identity
    /// inside a body whose enclosing levels it has not reached yet: such an identity is
    /// INCOMPLETE — declared within the levels it lists — and is extended level by level as its
    /// reference escapes (<see cref="EscapedThrough"/>) until the level that settles it completes
    /// it (<see cref="CompletedAt"/>). Two identities of one open lookup are compared only when
    /// both are complete or both end at the same level.
    /// </summary>
    internal bool IsComplete { get; }

    /// <summary>A provider declared as a property of <paramref name="level"/>: its declaration, then the owners of that level outward.</summary>
    internal static OpenProviderIdentity DeclaredAt(Algorithm provider, ElaboratedPropertyScope level)
    {
        if (provider.IsModuleRoot)
            return DeclaredAtRoot(provider);
        var declarations = new List<object> { DeclarationOf(provider) };
        AppendChain(declarations, level);
        return new([.. declarations], complete: true);
    }

    /// <summary>A provider declared as a property of the level whose declaring owners are <paramref name="owners"/>.</summary>
    internal static OpenProviderIdentity DeclaredIn(Algorithm provider, DeclaringOwners owners)
    {
        if (provider.IsModuleRoot)
            return DeclaredAtRoot(provider);
        var declarations = new List<object> { DeclarationOf(provider) };
        for (var current = owners; current is not null; current = current.Outer)
            declarations.Add(current.Declaration);
        return new([.. declarations], complete: true);
    }

    /// <summary>
    /// A provider declared at the root level, wherever it is named: a block written as an open
    /// target (it is wired to the prelude, never to its opener), and a loaded module wherever it is
    /// held (Q-31 H-P / Q-32 I-U: one module declaration, wired to the prelude, whatever spelling
    /// reaches it — <c>open 'u'</c>, <c>open M</c> for <c>M = load('u')</c>, <c>load('u').Sub</c>).
    /// </summary>
    internal static OpenProviderIdentity DeclaredAtRoot(Algorithm provider)
        => new([DeclarationOf(provider), RootLevel], complete: true);

    /// <summary>
    /// A provider declared as a property of the body <paramref name="level"/> whose enclosing
    /// levels are not known yet: an incomplete identity (see <see cref="IsComplete"/>) — unless the
    /// provider or the level is a loaded module, which is declared at the root level.
    /// </summary>
    internal static OpenProviderIdentity DeclaredWithin(Algorithm provider, Algorithm level)
        => provider.IsModuleRoot ? DeclaredAtRoot(provider)
            : level.IsModuleRoot ? new([DeclarationOf(provider), DeclarationOf(level), RootLevel], complete: true)
            : new([DeclarationOf(provider), DeclarationOf(level)], complete: false);

    /// <summary>A member of this provider: the member's declaration, then this provider's identity (a member that is itself a loaded module restarts at the root level).</summary>
    internal OpenProviderIdentity Member(Algorithm member)
        => member.IsModuleRoot ? DeclaredAtRoot(member) : new([DeclarationOf(member), .. _declarations], IsComplete);

    /// <summary>
    /// An incomplete identity whose reference escaped the body <paramref name="level"/>: declared
    /// within that level too — and complete when that level is a loaded module, which is declared at
    /// the root level wherever it is held.
    /// </summary>
    internal OpenProviderIdentity EscapedThrough(Algorithm level)
        => IsComplete ? this
            : level.IsModuleRoot ? new([.. _declarations, DeclarationOf(level), RootLevel], complete: true)
            : new([.. _declarations, DeclarationOf(level)], complete: false);

    /// <summary>An incomplete identity settled from <paramref name="level"/>: the levels it lists are inside that level, whose own chain completes it.</summary>
    internal OpenProviderIdentity CompletedAt(ElaboratedPropertyScope level)
    {
        if (IsComplete)
            return this;
        var declarations = new List<object>(_declarations);
        AppendChain(declarations, level);
        return new([.. declarations], complete: true);
    }

    private static void AppendChain(List<object> declarations, ElaboratedPropertyScope level)
    {
        for (var current = level; current is not null; current = current.Parent)
        {
            declarations.Add(current.Parent is null ? RootLevel : current.OwnerDeclaration);
            if (current.IsModuleLevel && current.Parent is not null)
            {
                // A loaded module's level is declared at the root level wherever it is held.
                declarations.Add(RootLevel);
                return;
            }
        }
    }

    /// <summary>The root level's element of a declaring chain (see <see cref="DeclaringOwners.Root"/>).</summary>
    internal static object RootLevelDeclaration => RootLevel;

    internal static object DeclarationOf(Algorithm algorithm) => algorithm.Declaration ?? (object)algorithm;

    public bool Equals(OpenProviderIdentity? other)
    {
        if (other is null || other._hash != _hash || other.IsComplete != IsComplete
            || other._declarations.Length != _declarations.Length)
            return false;
        for (var i = 0; i < _declarations.Length; i++)
        {
            if (!ReferenceEquals(_declarations[i], other._declarations[i]))
                return false;
        }

        return true;
    }

    public override bool Equals(object? obj) => Equals(obj as OpenProviderIdentity);

    public override int GetHashCode() => _hash;
}

/// <summary>One resolved open target: the provider algorithm, its semantic identity and (when known) the level that declares it.</summary>
internal readonly record struct ResolvedOpenTarget(Algorithm Target, OpenProviderIdentity Identity, ElaboratedPropertyScope? Level = null);

/// <summary>
/// The declaring owners of one level, innermost first, ending at the root level — the chain an
/// open provider's identity appends (<see cref="OpenProviderIdentity.DeclaredIn"/>) for a pass that
/// walks levels without building <see cref="ElaboratedPropertyScope"/> chains (implicit-argument
/// resolution). Immutable and persistent: a nested level extends its parent's chain in O(1).
/// </summary>
internal sealed class DeclaringOwners
{
    private DeclaringOwners(DeclaringOwners? outer, object declaration)
    {
        Outer = outer;
        Declaration = declaration;
    }

    /// <summary>The root level (the prelude every chain is rooted at).</summary>
    public static DeclaringOwners Root { get; } = new(null, OpenProviderIdentity.RootLevelDeclaration);

    /// <summary>The enclosing level's chain; null at the root.</summary>
    public DeclaringOwners? Outer { get; }

    /// <summary>This level's owner declaration (see <see cref="ElaboratedPropertyScope.OwnerDeclaration"/>).</summary>
    public object Declaration { get; }

    /// <summary>
    /// The chain of the body <paramref name="owner"/> nested in this level — or, for a loaded module,
    /// the chain of a body declared at the root level wherever it is held (Q-31 H-P).
    /// </summary>
    public DeclaringOwners Inside(Algorithm owner) => new(owner.IsModuleRoot ? Root : this, OpenProviderIdentity.DeclarationOf(owner));
    internal DeclaringOwners InsideIdentity(object declaration) => new(this, declaration);
}

/// <summary>
/// What the ownership-first OWNER WALK selects for a bare name.
/// </summary>
internal enum OwnedDeclarationKind
{
    /// <summary>No level of the chain declares the name.</summary>
    None,

    /// <summary>The deciding level owns a PARAMETER binding of that name.</summary>
    Parameter,

    /// <summary>The deciding level owns a PROPERTY of that name and no parameter.</summary>
    Property,
}

/// <summary>
/// The declaration the owner walk selected together with the level that OWNS it —
/// the C# form of Lean's <c>OwnedDeclaration</c> (<c>none | parameter level |
/// property level</c>). Constructed only through <see cref="None"/>,
/// <see cref="Parameter"/>, and <see cref="Property"/>, so a verdict can never carry a
/// payload that does not belong to its kind: a parameter verdict names its owning
/// level, a property verdict names its owning level AND the selected property, and
/// the <c>None</c> verdict (the struct's default value) names nothing. Consumers read
/// the payload through <see cref="TryGetParameter"/> / <see cref="TryGetProperty"/>,
/// which yield it exactly when the kind matches.
/// </summary>
internal readonly record struct OwnedDeclaration
{
    private readonly ElaboratedPropertyScope? _ownerScope;
    private readonly PropertyLookupHit _propertyHit;

    private OwnedDeclaration(OwnedDeclarationKind kind, ElaboratedPropertyScope? ownerScope, PropertyLookupHit propertyHit)
    {
        Kind = kind;
        _ownerScope = ownerScope;
        _propertyHit = propertyHit;
    }

    /// <summary>No level of the chain declares the name; lookup is left to opens.</summary>
    public static OwnedDeclaration None => default;

    /// <summary>The deciding level <paramref name="owner"/> binds the name as a parameter.</summary>
    public static OwnedDeclaration Parameter(ElaboratedPropertyScope owner)
    {
        ArgumentNullException.ThrowIfNull(owner);
        return new(OwnedDeclarationKind.Parameter, owner, default);
    }

    /// <summary>The deciding level <paramref name="owner"/> declares the name as the property <paramref name="hit"/> (and binds no parameter of that name).</summary>
    public static OwnedDeclaration Property(ElaboratedPropertyScope owner, PropertyLookupHit hit)
    {
        ArgumentNullException.ThrowIfNull(owner);
        if (hit.Owner is null || hit.Property is null)
            throw new ArgumentException("A property declaration requires a complete lookup hit.", nameof(hit));
        return new(OwnedDeclarationKind.Property, owner, hit);
    }

    public OwnedDeclarationKind Kind { get; }

    /// <summary>The level that decided, or null exactly for <see cref="None"/>.</summary>
    public ElaboratedPropertyScope? OwnerScope => _ownerScope;

    /// <summary>The owning level of a parameter verdict.</summary>
    public bool TryGetParameter([System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out ElaboratedPropertyScope? owner)
    {
        owner = Kind == OwnedDeclarationKind.Parameter ? _ownerScope : null;
        return owner is not null;
    }

    /// <summary>The owning level and selected property of a property verdict.</summary>
    public bool TryGetProperty([System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out ElaboratedPropertyScope? owner, out PropertyLookupHit hit)
    {
        if (Kind == OwnedDeclarationKind.Property)
        {
            owner = _ownerScope;
            hit = _propertyHit;
            return owner is not null;
        }

        owner = null;
        hit = default;
        return false;
    }
}

/// <summary>
/// Parameter ownership beside the scope chain's property tables. During discovery,
/// inferred bindings may not yet appear in an algorithm's stored signature; branch
/// binders are supplied by their pattern. Completion supplies established signatures.
/// The detector uses <c>ParameterOwnership</c>; editor frames carry equivalent tables.
/// </summary>
internal interface IOwnedParameterBindings
{
    bool ExcludesNeverCalledOwner => false;
    /// <summary>
    /// Whether <paramref name="level"/> ITSELF binds <paramref name="name"/> as
    /// a parameter: an explicit or inferred parameter of the algorithm that owns
    /// the level, or a conditional branch body's pattern binder. A SITE's map
    /// (<see cref="ParameterOwnership"/>) answers true only for the NEAREST
    /// enclosing binding of a name — an outer parameter of the same name is
    /// already shadowed by the inner one and must never decide a level the walk
    /// reaches first — so it serves walks that start at that site; a walk that
    /// starts at another scope (a static chase from a reference's own scope) asks
    /// each level its own bindings instead (<see cref="ElaboratedPropertyScope.BindsParameter"/>).
    /// </summary>
    bool DeclaresParameter(ElaboratedPropertyScope level, string name);
}

/// <summary>
/// Which OD-D verdict (M4★) a static chase applies to a written reference before it follows the reference to its
/// target — and so which STRATUM of open providers it reads (<see cref="ElaboratedPropertyScope.GetResolvedOpenProviders"/>:
/// a provider that is a written reference is followed under the same check). OD-D has two READINGS of a lone-row body's
/// target chase: the LOWER one resolves an opened name through the providers of <see cref="None"/>, which follow every
/// reference, the FINAL one through those of <see cref="Lower"/>, whose references are followed when the lower reading
/// finds no cycle. The operation solves the mutually dependent input/binding questions through
/// monotone Q1–Q7 equations, with no collection-time decider or chase suspension.
/// </summary>
internal enum StaticCycleCheck
{
    /// <summary>OD-D's lower reading itself: every reference is followed (a chain that comes back still stops).</summary>
    None,

    /// <summary>The lower verdict: OD-D's final reading — the providers it reads, and every receiver it reads.</summary>
    Lower,

    /// <summary>
    /// Alias formation: a body whose target chase returns in EITHER reading is no alias (implicit-argument resolution
    /// forms the aliases so, and a dot receiver's static structure predicts them so). Its providers are the ones every
    /// name lookup reads: a reference written as an open target is followed exactly where it becomes an alias, so the
    /// front end selects what the evaluator, which opens only formed aliases, selects — up to the navigated-body defect
    /// (SEMANTIC-ALIGNMENT.md (12), not repaired), where the detector's readings judge a navigated body through their own
    /// strata and refuse an alias the resolver forms.
    /// </summary>
    Formation,
}

internal static class ElaboratedScopeLookup
{
    /// <param name="algorithm">The level's algorithm.</param>
    /// <param name="parentOverride">The enclosing level; when null, a chain is synthesized from the algorithm's lexical parent context.</param>
    /// <param name="observations">Passive lookup observer for a new chain root (a level inherits its parent's).</param>
    /// <param name="memberIndexes">The creating operation's shared open-target member indexes; when null,
    /// the level inherits its parent's (see <see cref="ElaboratedPropertyScope"/>'s remarks).</param>
    /// <param name="staticContext">The level's context in the admitted static-structure operation; when null, derived from the parent's.</param>
    /// <param name="completedContext">The completed publication context, with no query operation.</param>
    /// <param name="branchPattern">The immediate branch body's binding region, when applicable.</param>
    /// <param name="sourcePhase">Explicit standalone input phase when no admitting or completed context is supplied.</param>
    public static ElaboratedPropertyScope CreateScope(
        Algorithm algorithm,
        ElaboratedPropertyScope? parentOverride = null,
        FrontEndTraversalObservations? observations = null,
        OpenMemberIndexCache? memberIndexes = null,
        StaticStructureContext? staticContext = null,
        CompletedStructureContext? completedContext = null,
        Pattern? branchPattern = null,
        StaticAstPhase? sourcePhase = null)
    {
        if (sourcePhase is { } phase && phase != StaticAstPhase.Resolved && algorithm.CompletedStructure is not null)
            throw new ArgumentException("A resolved publication cannot be reinterpreted as raw/name-resolved source.", nameof(sourcePhase));
        var parent = parentOverride ?? CreateParentScope(algorithm.Parent, memberIndexes, sourcePhase);
        return CreatePhysicalScope(algorithm, algorithm, parent, observations, memberIndexes, staticContext,
            completedContext, branchPattern, sourcePhase, ownerIdentity: null);
    }

    private static ElaboratedPropertyScope CreatePhysicalScope(Algorithm source, Algorithm? owner,
        ElaboratedPropertyScope? parent, FrontEndTraversalObservations? observations, OpenMemberIndexCache? indexes,
        StaticStructureContext? active, CompletedStructureContext? completed, Pattern? pattern,
        StaticAstPhase? phase, object? ownerIdentity)
    {
        completed ??= active is null && parent?.StaticContext is null ? CompletedStructureContext.For(owner, parent, pattern) : null;
        phase ??= owner?.CompletedStructure is not null ? StaticAstPhase.Resolved : parent?.SourcePhase;
        StandaloneScopeAnalysis? analysis = null;
        if (active is null && completed is null && parent is null && phase is { } input)
        {
            analysis = StandaloneScopeAnalysis.Start(source, input, ownerIdentity);
            var facts = analysis.Context.Facts;
            var prelude = facts.Prelude;
            parent = new(null, prelude.Opens, CreatePropertyHits(prelude, prelude.Properties), observations, indexes,
                prelude, completedContext: facts.Context(facts.PreludeKey), sourcePhase: input,
                standaloneAnalysis: analysis.AtPrelude());
            completed = analysis.Context;
        }
        return new(parent, source.Opens, CreatePropertyHits(owner ?? source, source.Properties), observations, indexes,
            owner, active, completed, pattern, phase, source, ownerIdentity, analysis);
    }

    public static PropertyLookupHit? TryLookupProperty(Algorithm owner, string name)
    {
        foreach (var property in owner.Properties)
        {
            if (property.Name == name)
                return new PropertyLookupHit(owner, property);
        }

        return null;
    }

    /// <summary>
    /// The first PUBLIC declaration of <paramref name="name"/> — the member an <c>open</c>
    /// provides, selected by visibility alone (the evaluator's <c>LookupPublicPropBinding</c>).
    /// </summary>
    public static PropertyLookupHit? TryLookupPublicProperty(Algorithm owner, string name)
        => TryLookupPublicProperty(owner, name, observations: null);

    private static PropertyLookupHit? TryLookupPublicProperty(
        Algorithm owner,
        string name,
        FrontEndTraversalObservations? observations)
    {
        var comparisons = 0;
        foreach (var property in owner.Properties)
        {
            comparisons++;
            if (property.Name == name
                && property.IsPublic)
            {
                observations?.RecordLookupPropertyComparisons(comparisons);
                return new PropertyLookupHit(owner, property);
            }
        }

        observations?.RecordLookupPropertyComparisons(comparisons);
        return null;
    }

    public static PropertyLookupHit? TryLookupDirectLexicalProperty(ElaboratedPropertyScope scope, string name)
    {
        var observations = scope.Observations;
        for (var current = scope; current is not null; current = current.Parent)
        {
            observations?.RecordLookupLevelVisit();
            if (current.TryLookupOwnProperty(name) is { } hit)
                return hit;
        }

        return null;
    }

    /// <summary>
    /// THE ownership-first owner walk over OWNED declarations, and the single
    /// owner of the parameter-vs-property precedence rule for the front end and
    /// the editor.
    ///
    /// <para>Search outward by owning scope: the first level that DECLARES
    /// <paramref name="name"/> wins, and within that level an established
    /// PARAMETER binding takes precedence over a property in invalid recovery trees;
    /// ParameterPropertyCollisionValidator rejects properties matching same-owner or enclosing parameters in source.
    /// "Declares" means the
    /// two kinds of owned declaration — a parameter binding
    /// (<see cref="IOwnedParameterBindings"/>) and a property of the level's own
    /// declaration list — so a captured ancestor parameter beats a property of
    /// any FARTHER owner and, in invalid recovery source, a nearer property beats an outer
    /// parameter. A level owning both selects the parameter, which is what makes
    /// a direct reference and a reference from a nested body agree.</para>
    ///
    /// <para><c>open</c> targets are not owned declarations and are consulted only
    /// after the whole direct chain, by <see cref="LookupLexicalPropertyMatches"/>.
    /// The prelude participates as the chain's outermost ordinary property level,
    /// farther than any capturing algorithm: <c>F(pi) = { pi + 1 }</c> binds the
    /// parameter rather than the <c>pi</c> alias. A
    /// <see cref="OwnedDeclarationKind.None"/> verdict leaves lookup to opens.</para>
    ///
    /// <para>The property arm selects EXACTLY what
    /// <see cref="TryLookupDirectLexicalProperty"/> selects whenever no
    /// parameter intervenes: the same per-level
    /// <see cref="ElaboratedPropertyScope.TryLookupOwnProperty"/> over the same
    /// ordered level chain.</para>
    /// </summary>
    public static OwnedDeclaration SelectOwnedDeclaration(
        ElaboratedPropertyScope scope,
        string name,
        IOwnedParameterBindings parameters)
    {
        if (scope.StaticContext is { } context) return context.Operation.Owned(context.Key, name, parameters.ExcludesNeverCalledOwner);
        var observations = scope.Observations;
        for (var current = scope; current is not null; current = current.Parent)
        {
            observations?.RecordLookupLevelVisit();

            // Same owner: the parameter wins. Asking the parameter question
            // first at EVERY level is the whole rule — an outer property can
            // never be reached while a nearer or same-level parameter binds the
            // name, and a nearer property is reached before a farther parameter.
            if (parameters.DeclaresParameter(current, name))
                return OwnedDeclaration.Parameter(current);

            if (current.TryLookupOwnProperty(name) is { } hit)
                return OwnedDeclaration.Property(current, hit);
        }

        return OwnedDeclaration.None;
    }

    /// <summary>
    /// The static target of one open expression, or null when it provides nothing: the
    /// target's head (<see cref="ResolveOpenTargetHead"/>) followed by each dotted step's
    /// PUBLIC member — the evaluator's <c>ResolveAlgForOpen</c> / Lean
    /// <c>resolveAlgForOpen</c> recursion, read through the ONE open-target decomposition
    /// (<see cref="AstHelpers.OpenTargetHead(Expr, out IReadOnlyList{string})"/>), so a
    /// name-headed and a block-headed path resolve by the same rule.
    /// </summary>
    public static Algorithm? ResolveOpenTarget(ElaboratedPropertyScope scope, Expr openExpr)
        => ResolveOpenProvider(scope, openExpr)?.Target;

    /// <summary>Reads the selected Q2 endpoint or its completed provider publication.</summary>
    public static ResolvedOpenTarget? ResolveOpenProvider(ElaboratedPropertyScope scope, Expr openExpr, StaticCycleCheck stratum = StaticCycleCheck.Formation)
    {
        if (scope.StaticContext is not { } context)
        {
            var completed = scope.BoundLookupContext();
            for (var index = 0; index < scope.Opens.Count; index++)
                if (ReferenceEquals(scope.Opens[index], openExpr)) return completed.ProviderAt(index, scope);
            return ResolvePublishedOpenExpression(scope, openExpr);
        }
        var written = context.Operation.WrittenExpression(context.Key, openExpr);
        for (var index = 0; index < scope.Opens.Count; index++)
            if (ReferenceEquals(scope.Opens[index], openExpr)) { written = context.Operation.SourceOf(context.Key).Opens[index]; break; }
        var fact = context.Operation.Read(StaticQueryKey.Project(StaticQueryKind.OpenProviders, context.Key,
            StaticQueryProjection.OpenTarget, stratum: stratum, node: written));
        if (fact.Data is not StaticScopeKey[] { Length: 1 } keys) return null;
        var body = context.Operation.SourceOf(keys[0]);
        var declaring = context.Operation.LookupLevel(keys[0].Parent ?? context.Operation.Queries.Keys.Root);
        return new(body, OpenProviderIdentity.DeclaredAt(body, declaring), declaring);
    }

    /// <summary>An ad hoc written path projects existing Q1/Q4/OD-C facts; it has no raw-reference fallback.</summary>
    private static ResolvedOpenTarget? ResolvePublishedOpenExpression(ElaboratedPropertyScope scope, Expr expression)
    {
        var head = expression.OpenTargetHead(out var members);
        ResolvedOpenTarget? selected;
        if (head is Expr.AlgorithmExpr block)
        {
            var context = scope.BoundLookupContext();
            selected = context.Facts.Context(context.Facts.PreludeKey).Open(block.Algorithm, scope.Root);
            if (selected is null && context.Facts.Child(context.Facts.PreludeKey, block.Algorithm) is null)
            {
                // A host can ask about a new inline, already bound structure after compilation.
                // Admit that graph explicitly at the open-head prelude boundary; never chase a raw row.
                var body = block.Algorithm;
                var analyzed = AnalyzedStaticStructures.ForBoundAst(body, declaringScopes: []);
                selected = analyzed.Facts.Context(analyzed.Facts.PreludeKey).Open(body, scope.Root);
            }
        }
        else if (head is Expr.Resolve name)
        {
            var owned = SelectOwnedDeclaration(scope, name.Name, OwnParameterBindings.Instance);
            if (!owned.TryGetProperty(out var declaring, out var hit)) return null;
            selected = declaring.BoundLookupContext().Open(hit.Property.Value, declaring);
        }
        else return null;
        foreach (var member in members)
        {
            if (selected is not { Level: { } declaring } provider
                || TryLookupPublicProperty(provider.Target, member) is not { } hit) return null;
            var bodyLevel = CreateScope(provider.Target, declaring, memberIndexes: scope.MemberIndexes);
            selected = bodyLevel.BoundLookupContext().Open(hit.Property.Value, bodyLevel);
        }
        return selected;
    }

    /// <summary>
    /// Why a written open target provides no algorithm — the step at which <see cref="ResolveOpenProvider"/>
    /// fails, walked over the SAME decomposition and the same stratified structure, named the way the
    /// evaluator's open resolution fails there: a name head no enclosing declaration or prelude member
    /// provides (an open head never resolves through another open), a dotted step — from a name head or
    /// an inline block head alike — that names a member its receiver's structure lacks, declares
    /// privately (open paths select public members), or declares only inside a conditional branch (a
    /// family exposes no members), or a transparent reference whose target no direct lookup provides
    /// (OD-C, M4★). Null for every target this rule does not own: a parameter-owned head, a bare inline
    /// block, and the shapes the parser rejects as <see cref="DiagnosticCode.BadOpenForm"/>.
    /// </summary>
    internal static string? DescribeUnresolvedOpenTarget(ElaboratedPropertyScope scope, Expr target)
    {
        var headExpr = target.OpenTargetHead(out var steps);
        var description = Evaluator.OpenExprName(target);
        OpenStructureStep provider;
        string receiverDescription;
        switch (headExpr)
        {
            case Expr.Resolve(var head):
                if (ResolveOpenProviderHead(scope, headExpr, out var level) is not { } resolved)
                {
                    return $"'{description}' cannot be opened because no property named '{head}' is visible here; " +
                        "the first name of an open target resolves through the enclosing declarations and the prelude, never through another open.";
                }

                provider = new OpenStructureStep(resolved.Target, resolved.Identity, level);
                receiverDescription = head;
                break;

            case Expr.AlgorithmExpr(var block):
                provider = new OpenStructureStep(block, OpenProviderIdentity.DeclaredAtRoot(block), scope.Root);
                receiverDescription = Evaluator.OpenExprName(headExpr);
                break;

            default:
                return null;
        }

        foreach (var step in steps)
        {
            if (provider.Level.CompletedContext?.OpenIsUnavailable(provider.Target, provider.Level) == true) return null;
            if (OpenStructureOf(provider, scope.Observations) is not { } receiver)
                return UnresolvedReference(description, receiverDescription);

            if (TryLookupPublicProperty(receiver.Target, step) is { } member)
            {
                var selected = member.Property.Value;
                provider = new OpenStructureStep(selected, receiver.Identity.Member(selected), BodyLevelOf(receiver.Target, receiver.Level));
                receiverDescription += "." + step;
                continue;
            }

            if (TryLookupProperty(receiver.Target, step) is not null)
                return $"'{description}' cannot be opened because property '{step}' of '{receiverDescription}' is not public; an open path selects public members only.";

            return receiver.Target.DefinesConditionalBranchProperty(step)
                ? $"'{description}' cannot be opened because '{step}' is declared only inside a conditional branch of '{receiverDescription}', and a clause family exposes no members."
                : $"'{description}' cannot be opened because '{receiverDescription}' has no property named '{step}'.";
        }

        return provider.Level.CompletedContext?.OpenIsUnavailable(provider.Target, provider.Level) == true ? null
            : OpenStructureOf(provider, scope.Observations) is null ? UnresolvedReference(description, receiverDescription) : null;

        static string UnresolvedReference(string description, string reference)
            => $"'{description}' cannot be opened because '{reference}' refers to an algorithm that no enclosing declaration or prelude member provides; " +
                "the reference of an open target resolves through the enclosing declarations and the prelude, never through another open.";
    }

    /// <summary>One provider during open resolution: the algorithm, its identity, and the level that declares it.</summary>
    private readonly record struct OpenStructureStep(Algorithm Target, OpenProviderIdentity Identity, ElaboratedPropertyScope Level);

    /// <summary>
    /// The level of <paramref name="body"/>'s own declarations inside <paramref name="parent"/>: the operation's shared
    /// one (<see cref="OpenMemberIndexCache.BodyLevel"/>), or a private one on a chain built without a cache.
    /// </summary>
    private static ElaboratedPropertyScope BodyLevelOf(Algorithm body, ElaboratedPropertyScope parent)
        => parent.MemberIndexes is { } cache ? cache.BodyLevel(body, parent) : CreateScope(body, parent);

    /// <summary>Diagnostic path adapter over Q3's OD-C projection.</summary>
    private static OpenStructureStep? OpenStructureOf(
        OpenStructureStep provider, FrontEndTraversalObservations? observations, StaticCycleCheck stratum = StaticCycleCheck.Formation)
    {
        if (provider.Level.StaticContext is { } context)
        {
            var key = context.Operation.ContextOf(context.Key, provider.Target);
            var fact = context.Operation.Read(StaticQueryKey.Project(StaticQueryKind.TargetWalk, key, StaticQueryProjection.OpenStructure, stratum: stratum));
            if (fact.Kind != StaticFactKind.Structure || fact.Scope?.Parent is not { } parent) return null;
            var body = context.Operation.SourceOf(fact.Scope);
            var level = context.Operation.LookupLevel(parent);
            return new(body, OpenProviderIdentity.DeclaredAt(body, level), level);
        }
        var completed = provider.Level.BoundLookupContext();
        return completed.Open(provider.Target, provider.Level) is { } published
            ? new(published.Target, published.Identity, published.Level!) : null;
    }

    /// <summary>
    /// The STRUCTURE of an ELABORATED algorithm (M4★, once implicit-argument resolution has formed every
    /// alias): a transparent reference's recorded structure (<see cref="Algorithm.Alias.ResolvedStructure"/>;
    /// none when its target is a runtime one), every other algorithm — a structural carrier included —
    /// itself. The views that run after resolution (the editor, the provenance finalizer, the resolver's
    /// own reads of processed bodies) read this; the detector, which runs before the aliases exist, reads
    /// <see cref="StaticReceiverStructure"/> or <see cref="StaticStructureWithScopeAt"/>.
    /// </summary>
    internal static Algorithm? ElaboratedStructure(Algorithm? algorithm)
        => algorithm is Algorithm.Alias { IsReference: true } reference ? reference.ResolvedStructure : algorithm;

    /// <summary>
    /// The STRUCTURE a static view may navigate for the receiver <paramref name="algorithm"/> (M4★): an
    /// elaborated transparent reference's recorded structure (<see cref="Algorithm.Alias.ResolvedStructure"/>;
    /// null when it has none — a runtime target), null for an unelaborated body that becomes a reference
    /// (its target is decided where its declaring scope is known: <see cref="StaticStructureWithScopeAt"/>) or whose row
    /// is an argumentless <c>.Algorithm</c> link (a runtime reference unless the body has an input of its own, which this
    /// scope-free view cannot see), and every other algorithm — a structural carrier and a calculation written as a
    /// member path from a head that is no name or block (<c>A = 6.abs</c>) included — itself. After implicit-argument
    /// resolution the views read <see cref="ElaboratedStructure"/> instead.
    /// </summary>
    internal static Algorithm? StaticReceiverStructure(Algorithm algorithm)
        => algorithm switch
        {
            Algorithm.Alias { IsReference: true } reference => reference.ResolvedStructure,
            Algorithm.User user when WillBeReference(user)
                && (StaticAliasTargets.IsStaticPath(user.Output[0]) || user.Output[0] is Expr.DotCall { Args: null } link && link.UsesDotAlgorithmIntrinsic()) => null,
            _ => algorithm,
        };

    /// <summary>
    /// The static STRUCTURE (M4★) of <paramref name="value"/>, a property declared at
    /// <paramref name="level"/>, together with the SCOPE that structure is declared at: an elaborated
    /// transparent reference's recorded structure; an unelaborated body that becomes a reference
    /// (<see cref="WillBeReference"/>) followed in ITS OWN scope — its head by the owner walk over each
    /// level's OWN parameter bindings (<see cref="ElaboratedPropertyScope.BindsParameter"/>: a parameter is a
    /// runtime reference, no static structure), then a single open provider, each member step a declared member
    /// of the previous receiver's structure — until a non-reference (a carrier included) is reached. Null when
    /// the structure is not statically known. A body whose target chase returns is no alias (OD-D, as alias
    /// formation decides it: <see cref="StaticCycleCheck.Formation"/>): the chain's first body is its own
    /// structure. The scope is what lets a member of the structure be followed in its own scope
    /// (<see cref="StaticMemberStructure"/>). The endpoint comes from Q3.
    /// </summary>
    internal static (Algorithm Structure, StaticStructureScope Scope)? StaticStructureWithScopeAt(Algorithm value, ElaboratedPropertyScope level)
    {
        if (level.StaticContext is { } context) return context.Operation.StructureAt(context.Key, value);
        return level.BoundLookupContext().Receiver(value, level);
    }

    /// <summary>
    /// The static STRUCTURE (M4★) of <paramref name="member"/>, a declared member of the statically known
    /// structure <paramref name="receiver"/> declared at <paramref name="receiverScope"/>: the member is
    /// declared in the receiver's own body — whose parameters its level answers — and followed there, so
    /// a member that is a transparent reference (written or still a lone reference row) navigates its
    /// target exactly as the evaluator's receiver resolution does. Null when it is not statically known.
    /// </summary>
    internal static (Algorithm Structure, StaticStructureScope Scope)? StaticMemberStructure(
        Algorithm receiver, StaticStructureScope receiverScope, string name, Algorithm member)
    {
        if (receiverScope.Level.StaticContext is { } context)
            return context.Operation.StructureAt(receiverScope.BodyKey ?? context.Operation.ContextOf(context.Key, receiver), member);
        if ((receiverScope.CompletedFacts ?? receiverScope.Level.CompletedContext?.Facts) is { } completedFacts)
        {
            var completed = completedFacts.Context(receiverScope.Level.CompletedContext?.Key ?? completedFacts.PreludeKey);
            var owner = receiverScope.BodyKey ?? completed.BodyKey(receiver);
            return owner is not null && completed.Facts.Member(owner, name) is { } selected
                    ? completed.ReceiverAt(selected, receiverScope.Level) : null;
        }
        var admitted = receiverScope.Level.BoundLookupContext();
        var ownerKey = receiverScope.BodyKey ?? admitted.BodyKey(receiver);
        return ownerKey is not null && admitted.Facts.Member(ownerKey, name) is { } selectedKey
            ? admitted.ReceiverAt(selectedKey, receiverScope.Level) : null;
    }

    /// <summary>Compositional receiver inspection over completed Q3/Q4 facts, without a raw-reference fallback.</summary>
    internal static StaticStructuralMemberProvider CompletedReceiver(Expr expression, ElaboratedPropertyScope scope)
        => expression.ResolveStaticStructuralMemberProvider(name =>
        {
            var selected = SelectOwnedDeclaration(scope, name, OwnParameterBindings.Instance);
            if (selected.Kind == OwnedDeclarationKind.Parameter) return new(StaticStructuralMemberProviderKind.RuntimeParameter);
            if (selected.TryGetProperty(out var owner, out var hit)) return ReadCompletedReceiver(hit.Property.Value, owner);
            return LookupSingleOpenMember(scope, name) is { } opened ? ReadCompletedReceiver(opened.Hit.Property.Value, opened.MemberLevel)
                : new(StaticStructuralMemberProviderKind.LexicalReference);
        }, block => ReadCompletedReceiver(block, scope));

    private static StaticStructuralMemberProvider ReadCompletedReceiver(Algorithm body, ElaboratedPropertyScope declaring)
        => StaticStructureWithScopeAt(body, declaring) is { } selected
            ? new(StaticStructuralMemberProviderKind.KnownAlgorithm, selected.Structure, selected.Scope)
            : new(StaticStructuralMemberProviderKind.LexicalReference);

    /// <summary>
    /// The one member an open level provides for <paramref name="name"/> — at the first open level that
    /// provides it at all — with the level that member is DECLARED at (its provider's own body inside the
    /// provider's declaring level), or null when no open provides it or the deciding level provides it
    /// more than once (the ambiguity the evaluator reports).
    /// </summary>
    internal static (PropertyLookupHit Hit, ElaboratedPropertyScope MemberLevel)? LookupSingleOpenMember(
        ElaboratedPropertyScope scope, string name, StaticCycleCheck stratum = StaticCycleCheck.Formation)
    {
        for (var current = scope; current is not null; current = current.Parent)
        {
            var providers = current.GetResolvedOpenProviders(stratum);
            PropertyLookupHit? found = null;
            ResolvedOpenProvider? owner = null;
            var count = 0;
            foreach (var provider in providers)
            {
                if (provider.TryLookupPublicMember(name) is { } hit)
                {
                    count++;
                    found = hit;
                    owner = provider;
                }
            }

            if (count == 1)
                return (found!.Value, BodyLevelOf(owner!.Target, owner.Level ?? scope.Root));
            if (count > 1)
                return null;
        }

        return null;
    }

    /// <summary>
    /// The scope a statically known receiver STRUCTURE is declared at (M4★): what lets a member of that structure be
    /// followed in its own scope (<see cref="StaticMemberStructure"/>), whose levels answer their own parameters.
    /// </summary>
    internal sealed class StaticStructureScope
    {
        internal StaticStructureScope(ElaboratedPropertyScope level, StaticScopeKey? bodyKey = null,
            StaticLookupFacts? completedFacts = null) => (Level, BodyKey, CompletedFacts) = (level, bodyKey, completedFacts);

        public ElaboratedPropertyScope Level { get; }
        internal StaticScopeKey? BodyKey { get; }
        internal StaticLookupFacts? CompletedFacts { get; }
    }

    /// <summary>
    /// The owner walk's parameter bindings during a static chase: each level's OWN
    /// (<see cref="ElaboratedPropertyScope.BindsParameter"/>). The walk starts at a reference's own scope, so the
    /// nearest level binding a name is reached first whatever site asked — never a site's map, which a parameter of
    /// the site could shadow.
    /// </summary>
    internal sealed class OwnParameterBindings : IOwnedParameterBindings
    {
        public static readonly OwnParameterBindings Instance = new();

        public bool DeclaresParameter(ElaboratedPropertyScope level, string name) => level.BindsParameter(name);
    }

    /// <summary>
    /// Whether the unelaborated body <paramref name="user"/> has the shape implicit-argument resolution
    /// makes a transparent reference (M4★, <c>ImplicitArgumentResolver.TryCompleteLoneCalleeRow</c>): an
    /// unbraced open body — no written braces, no parameter list or pattern, no declarations or opens of
    /// its own — whose one written row is a name or an argumentless member path. Whether its row names an
    /// algorithm is decided by the chase that reads it (an unresolved head is no provider).
    /// </summary>
    private static bool WillBeReference(Algorithm.User user)
        => !user.IsWrittenBlock
            && !user.HasExplicitParameterList
            && user.ParameterPatterns.Count == 0
            && user.Properties.Count == 0
            && user.Opens.Count == 0
            && !user.IsSyntheticDeconstructionPlumbing
            && !user.IsModuleRoot
            && user.Output.Count == 1
            && user.Output[0] is Expr.Resolve or Expr.DotCall { Args: null }
            && AstHelpers.WrittenRows(user).Count == 1;

    /// <summary>
    /// The provider an open target's HEAD denotes with its identity (see
    /// <see cref="ResolveOpenTargetHead"/>, whose resolution this is): a name head through the
    /// direct chain, declared at the level that holds it; a block head declared at the root level.
    /// </summary>
    internal static ResolvedOpenTarget? ResolveOpenProviderHead(ElaboratedPropertyScope scope, Expr head, out ElaboratedPropertyScope level)
    {
        level = scope.Root;
        switch (head)
        {
            case Expr.Resolve(var name):
            {
                var observations = scope.Observations;
                for (var current = scope; current is not null; current = current.Parent)
                {
                    observations?.RecordLookupLevelVisit();
                    if (current.TryLookupOwnProperty(name) is { } hit)
                    {
                        var provider = hit.Property.Value;
                        level = current;
                        return new ResolvedOpenTarget(provider, OpenProviderIdentity.DeclaredAt(provider, current));
                    }
                }

                return null;
            }

            case Expr.AlgorithmExpr(var algorithm):
                return new ResolvedOpenTarget(algorithm, OpenProviderIdentity.DeclaredAtRoot(algorithm));

            default:
                // A parameter-owned head, a recovery capture, or a non-open form: the same verdict
                // as ResolveOpenTargetHead, with a capture's empty recovery scope declared in place.
                return ResolveOpenTargetHead(scope, head) is { } recovered
                    ? new ResolvedOpenTarget(recovered, OpenProviderIdentity.DeclaredAtRoot(recovered))
                    : null;
        }
    }

    /// <summary>
    /// The algorithm an open target's HEAD (<see cref="AstHelpers.OpenTargetHead(Expr)"/>)
    /// denotes, or null when it provides nothing. A bare <see cref="Expr.Resolve"/> head
    /// resolves through the direct property chain (local properties, then the parent chain —
    /// the evaluator's <c>LookupLexicalDirect</c>), which is sound only because parameter
    /// detection has already classified every head by ownership: a head the owner walk found
    /// parameter-owned is an <see cref="Expr.Param"/> by the time any scope is built over the
    /// list, and a parameter provides nothing (static-open ownership, F2). An inline block (a
    /// written <c>{ … }</c> or a loaded module) is the provider itself.
    /// </summary>
    internal static Algorithm? ResolveOpenTargetHead(ElaboratedPropertyScope scope, Expr head)
    {
        switch (head)
        {
            case Expr.Resolve(var name):
                return TryLookupDirectLexicalProperty(scope, name)?.Property.Value;

            case Expr.Param:
                // A parameter-owned head (see ParameterDetector.ClassifyOpenTargetHeads):
                // not an open form, never a provider, and never a reason to look farther
                // outward for a same-named property.
                return null;

            case Expr.AlgorithmExpr(var algorithm):
                return algorithm;

            case Expr.Capture:
                // RECOVERY TOLERANCE: the parser rejects capture open targets
                // (`open (M, M)` is a captured value, not an algorithm — the
                // evaluator's open resolution errors with BadOpenForm), so a
                // capture open reaches frontend lookup only through a
                // diagnostic-bearing recovery tree. It contributes no names —
                // an empty scope keeps recovery lookup stable without
                // pretending the capture exposes any enclosed identity.
                return new Algorithm.User(
                    Parent: null, ParameterPatterns: [], Opens: [],
                    Properties: [], Output: OutputBundle.Empty);

            default:
                // A spread, a join, a call (an unresolved `load` included), a literal, an
                // argument-bearing dot edge, or any other shape: not an open form.
                return null;
        }
    }

    /// <summary>
    /// The open matches of <paramref name="name"/>: at the first level whose providers publicly declare it, every such
    /// member. <paramref name="stratum"/> selects the provider stratum (<see cref="ElaboratedPropertyScope.GetResolvedOpenProviders"/>).
    /// </summary>
    public static IReadOnlyList<PropertyLookupHit> LookupOpenPropertyMatches(
        ElaboratedPropertyScope scope, string name, StaticCycleCheck stratum = StaticCycleCheck.Formation)
    {
        for (var current = scope; current is not null; current = current.Parent)
        {
            var providers = current.GetResolvedOpenProviders(stratum);
            if (providers.Count == 0)
                continue;

            List<PropertyLookupHit>? hits = null;
            foreach (var provider in providers)
            {
                if (provider.TryLookupPublicMember(name) is { } hit)
                {
                    hits ??= [];
                    hits.Add(hit);
                }
            }

            if (hits is not null && hits.Count > 0)
                return hits;
        }

        return [];
    }

    public static IReadOnlyList<PropertyLookupHit> LookupLexicalPropertyMatches(ElaboratedPropertyScope scope, string name)
    {
        if (TryLookupDirectLexicalProperty(scope, name) is { } directHit)
            return [directHit];

        return LookupOpenPropertyMatches(scope, name);
    }

    /// <summary>
    /// Q-29 A-U (decided 2026-10-06): the providers of the open level a bare-name lookup of
    /// <paramref name="name"/> reaches when that level has two or more DIFFERENT providers of it
    /// (counted by <see cref="OpenProviderIdentity"/>, Q-19 D-I) — the written name then denotes no
    /// declaration — or null when lexical precedence decides first (a property of the direct chain,
    /// the prelude included; a nearer open level providing it once) or no open provides it. The
    /// caller has excluded parameters by the owner walk. Chains without any <c>open</c> answer null
    /// without a lookup.
    /// </summary>
    public static IReadOnlyList<ResolvedOpenProvider>? FindAmbiguousOpenProviders(ElaboratedPropertyScope scope, string name)
    {
        if (!scope.HasOpensInChain || TryLookupDirectLexicalProperty(scope, name) is not null)
            return null;

        for (var current = scope; current is not null; current = current.Parent)
        {
            List<ResolvedOpenProvider>? providing = null;
            foreach (var provider in current.GetResolvedOpenProviders())
            {
                if (provider.TryLookupPublicMember(name) is not null)
                    (providing ??= []).Add(provider);
            }

            if (providing is not null)
                return providing.Count > 1 ? providing : null;
        }

        return null;
    }

    private static ElaboratedPropertyScope? CreateParentScope(ScopeCtx? parent, OpenMemberIndexCache? memberIndexes,
        StaticAstPhase? sourcePhase = null)
        => parent is null ? null : CreateScope(parent, memberIndexes, sourcePhase);

    private static ElaboratedPropertyScope CreateScope(ScopeCtx scope, OpenMemberIndexCache? memberIndexes, StaticAstPhase? phase)
    {
        var source = scope.Owner is Algorithm.User user
            ? user with { Parent = null, Opens = scope.Opens, Properties = scope.Properties, Output = [],
                ParameterPatterns = scope.Parameters.Select(name => (ParameterPattern)new CaptureParameterPattern(name)).ToArray() }
            : CreateSyntheticOwner(scope);
        return CreatePhysicalScope(source, scope.Owner, CreateParentScope(scope.Parent, memberIndexes, phase), null,
            memberIndexes, null, null, null, phase, scope.Owner?.Declaration ?? (object?)scope.Owner ?? scope);
    }

    private static IReadOnlyList<PropertyLookupHit> CreatePropertyHits(Algorithm owner, IReadOnlyList<Property> properties)
    {
        var hits = new List<PropertyLookupHit>(properties.Count);
        foreach (var property in properties)
            hits.Add(new PropertyLookupHit(owner, property));
        return hits;
    }

    private static Algorithm CreateSyntheticOwner(ScopeCtx scope)
        => new Algorithm.User(
            Parent: null,
            ParameterPatterns: scope.Parameters.Select(name => (ParameterPattern)new CaptureParameterPattern(name)).ToArray(),
            Opens: scope.Opens,
            Properties: scope.Properties,
            Output: []);

}
