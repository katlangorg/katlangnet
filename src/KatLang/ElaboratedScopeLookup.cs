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
/// </summary>
internal sealed class ElaboratedPropertyScope
{
    private Dictionary<string, int>? _nameIndex;
    private int _firstNullNameIndex = -1;
    private IReadOnlyList<ResolvedOpenProvider>? _openProviders;

    public ElaboratedPropertyScope(
        ElaboratedPropertyScope? parent,
        IReadOnlyList<Expr> opens,
        IReadOnlyList<PropertyLookupHit> properties,
        FrontEndTraversalObservations? observations = null)
    {
        Parent = parent;
        Opens = opens;
        Properties = properties;
        Observations = parent?.Observations ?? observations;
        Root = parent is null ? this : parent.Root;
    }

    public ElaboratedPropertyScope? Parent { get; }

    public IReadOnlyList<Expr> Opens { get; }

    public IReadOnlyList<PropertyLookupHit> Properties { get; }

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

    /// <summary>
    /// This level's resolved <c>open</c> providers in declaration order: named
    /// targets deduplicated first-occurrence-wins by their open spelling
    /// (inline blocks never deduplicate — the evaluator's
    /// <c>ResolveAllOpens</c> rule via
    /// <see cref="ElaboratedScopeLookup.OpenTargetDedupKey"/>), unresolvable
    /// targets omitted. Resolution is pure and diagnostic-free, and it is
    /// performed LAZILY — only when a lookup actually consults this level's
    /// opens — so owned-name precedence and the no-consultation case cost
    /// exactly what they did before the cache.
    /// </summary>
    public IReadOnlyList<ResolvedOpenProvider> GetResolvedOpenProviders()
    {
        if (_openProviders is { } cached)
            return cached;

        if (Opens.Count == 0)
            return _openProviders = [];

        List<ResolvedOpenProvider>? providers = null;
        HashSet<string>? seenKeys = null;
        for (var i = 0; i < Opens.Count; i++)
        {
            var openExpr = Opens[i];
            seenKeys ??= [];
            if (!seenKeys.Add(ElaboratedScopeLookup.OpenTargetDedupKey(openExpr, i)))
                continue;

            Observations?.RecordLookupOpenTargetResolution();
            if (ElaboratedScopeLookup.ResolveOpenTarget(this, openExpr) is { } target)
                (providers ??= []).Add(new ResolvedOpenProvider(target, Observations));
        }

        return _openProviders = providers is not null ? providers : [];
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
}

/// <summary>
/// One resolved <c>open</c> provider of a scope level, caching the exact target
/// algorithm the level's open declaration resolved to. Member lookup is served
/// from a lazy name→first-QUALIFYING-index map replicating
/// <see cref="ElaboratedScopeLookup.TryLookupPublicExportedProperty"/> exactly:
/// the first list entry that matches the name AND is public AND exported wins
/// (a non-qualifying same-name entry earlier in the list is skipped, never an
/// answer). The target's ordered property list remains the enumeration source
/// for visible-name gathering.
/// </summary>
internal sealed class ResolvedOpenProvider
{
    private readonly FrontEndTraversalObservations? _observations;
    private Dictionary<string, int>? _exportedMemberIndex;
    private int _firstNullExportedMemberIndex = -1;

    public ResolvedOpenProvider(Algorithm target, FrontEndTraversalObservations? observations)
    {
        Target = target;
        _observations = observations;
    }

    public Algorithm Target { get; }

    public PropertyLookupHit? TryLookupExportedMember(string name)
    {
        var properties = Target.Properties;
        var index = _exportedMemberIndex;
        if (index is null)
        {
            _observations?.RecordLookupOpenMemberIndexBuild();
            index = new Dictionary<string, int>(StringComparer.Ordinal);
            for (var i = 0; i < properties.Count; i++)
            {
                var property = properties[i];
                if (property.IsPublic
                    && property.Exposure == PropertyExposure.Exported)
                {
                    if (property.Name is { } memberName)
                        index.TryAdd(memberName, i);
                    else if (_firstNullExportedMemberIndex < 0)
                        _firstNullExportedMemberIndex = i;
                }
            }

            _exportedMemberIndex = index;
        }

        var propertyIndex = name is null
            ? _firstNullExportedMemberIndex
            : index.TryGetValue(name, out var namedPropertyIndex) ? namedPropertyIndex : -1;
        return propertyIndex >= 0 ? new PropertyLookupHit(Target, properties[propertyIndex]) : null;
    }

    internal void PrewarmSharedLookupCaches()
        => _ = TryLookupExportedMember(string.Empty);
}

internal readonly record struct PropertyLookupHit(Algorithm Owner, Property Property);

/// <summary>
/// One spelling that authoritative lexical lookup resolves uniquely. Opened
/// names carry the exact provider property because their eligibility also
/// depends on its later final exposure classification; direct lexical names
/// do not.
/// </summary>
internal readonly record struct VisibleLexicalName(
    string Name,
    Property? RequiredExportedProperty);

internal static class ElaboratedScopeLookup
{
    public static ElaboratedPropertyScope CreateScope(
        Algorithm algorithm,
        ElaboratedPropertyScope? parentOverride = null,
        FrontEndTraversalObservations? observations = null)
        => new(
            parentOverride ?? CreateParentScope(algorithm.Parent),
            algorithm.Opens,
            CreatePropertyHits(algorithm, algorithm.Properties),
            observations);

    public static PropertyLookupHit? TryLookupProperty(Algorithm owner, string name)
    {
        foreach (var property in owner.Properties)
        {
            if (property.Name == name)
                return new PropertyLookupHit(owner, property);
        }

        return null;
    }

    public static PropertyLookupHit? TryLookupPublicExportedProperty(Algorithm owner, string name)
        => TryLookupPublicExportedProperty(owner, name, observations: null);

    private static PropertyLookupHit? TryLookupPublicExportedProperty(
        Algorithm owner,
        string name,
        FrontEndTraversalObservations? observations)
    {
        var comparisons = 0;
        foreach (var property in owner.Properties)
        {
            comparisons++;
            if (property.Name == name
                && property.IsPublic
                && property.Exposure == PropertyExposure.Exported)
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

    public static Algorithm? ResolveOpenTarget(ElaboratedPropertyScope scope, Expr openExpr)
    {
        switch (openExpr)
        {
            case Expr.Resolve(var name):
                return TryLookupDirectLexicalProperty(scope, name)?.Property.Value;

            case Expr.DotCall dotCall when dotCall.IsCoreOpenForm():
            {
                var targetAlgorithm = ResolveOpenTarget(scope, dotCall.Target);
                return targetAlgorithm is null
                    ? null
                    : TryLookupPublicExportedProperty(targetAlgorithm, dotCall.Name, scope.Observations)?.Property.Value;
            }

            case Expr.SequenceSpread(var operand):
            {
                _ = operand;
                return null;
            }

            case Expr.SequenceConstruct(var left, var right):
            {
                _ = left;
                _ = right;
                return null;
            }

            case Expr.AlgorithmExpr(var algorithm):
                return algorithm;

            case Expr.Capture:
                // RECOVERY TOLERANCE: the parser rejects capture open targets
                // (`open (M)` is a captured value, not an algorithm — the
                // evaluator's open resolution errors with BadOpenForm), so a
                // capture open reaches frontend lookup only through a
                // diagnostic-bearing recovery tree. It contributes no names —
                // an empty scope keeps recovery lookup stable without
                // pretending the capture exposes any enclosed identity.
                return new Algorithm.User(
                    Parent: null, Parameters: [], Opens: [],
                    Properties: [], Output: OutputBundle.Empty);

            default:
                return null;
        }
    }

    public static IReadOnlyList<PropertyLookupHit> LookupOpenPropertyMatches(ElaboratedPropertyScope scope, string name)
    {
        for (var current = scope; current is not null; current = current.Parent)
        {
            var providers = current.GetResolvedOpenProviders();
            if (providers.Count == 0)
                continue;

            List<PropertyLookupHit>? hits = null;
            foreach (var provider in providers)
            {
                if (provider.TryLookupExportedMember(name) is { } hit)
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

    /// <summary>
    /// Canonical dedup key for one written <c>open</c> target, matching
    /// <c>Evaluator.ResolveAllOpens</c> and Lean <c>resolveAllOpens</c>.
    /// Shared with the semantic model's scope-visibility enumeration so
    /// completion applies the same first-occurrence-wins rule as resolution.
    /// </summary>
    internal static string OpenTargetDedupKey(Expr openExpr, int index)
        => openExpr is Expr.AlgorithmExpr or Expr.Capture
            ? $"(inline#{index})"
            : Evaluator.OpenExprName(openExpr);

    public static IReadOnlyList<PropertyLookupHit> LookupLexicalPropertyMatches(ElaboratedPropertyScope scope, string name)
    {
        if (TryLookupDirectLexicalProperty(scope, name) is { } directHit)
            return [directHit];

        return LookupOpenPropertyMatches(scope, name);
    }

    /// <summary>
    /// Enumerates a bounded set of names that the authoritative
    /// <see cref="LookupLexicalPropertyMatches"/> resolves uniquely from
    /// <paramref name="scope"/>. Potential spellings are gathered once, then
    /// validated through that per-name lookup; ambiguous open providers are
    /// therefore never presented as a resolvable candidate. Returning
    /// <c>false</c> means the distinct-candidate budget was exceeded and the
    /// caller should conservatively offer no suggestion.
    /// </summary>
    internal static bool TryCollectVisibleLexicalNames(
        ElaboratedPropertyScope scope,
        ISet<string> names,
        int maxCount,
        int maxNameLength,
        out IReadOnlyList<VisibleLexicalName> visibleNames)
    {
        bool AddPotential(string name)
        {
            if (name.Length == 0 || name.Length > maxNameLength || names.Contains(name))
                return true;
            if (names.Count >= maxCount)
                return false;
            names.Add(name);
            return true;
        }

        for (var current = scope; current is not null; current = current.Parent)
        {
            foreach (var hit in current.Properties)
            {
                if (!AddPotential(hit.Property.Name))
                {
                    visibleNames = [];
                    return false;
                }
            }

            foreach (var provider in current.GetResolvedOpenProviders())
            {
                foreach (var property in provider.Target.Properties)
                {
                    if (property.IsPublic
                        && property.Exposure == PropertyExposure.Exported
                        && !AddPotential(property.Name))
                    {
                        visibleNames = [];
                        return false;
                    }
                }
            }
        }

        var resolved = new List<VisibleLexicalName>(names.Count);
        foreach (var name in names)
        {
            if (TryLookupDirectLexicalProperty(scope, name) is not null)
            {
                resolved.Add(new VisibleLexicalName(name, RequiredExportedProperty: null));
                continue;
            }

            var openHits = LookupOpenPropertyMatches(scope, name);
            if (openHits.Count == 1)
                resolved.Add(new VisibleLexicalName(name, openHits[0].Property));
        }

        visibleNames = resolved;
        return true;
    }

    private static ElaboratedPropertyScope? CreateParentScope(ScopeCtx? parent)
        => parent is null ? null : CreateScope(parent);

    private static ElaboratedPropertyScope CreateScope(ScopeCtx scope)
        => new(
            CreateParentScope(scope.Parent),
            scope.Opens,
            CreatePropertyHits(CreateSyntheticOwner(scope), scope.Properties));

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
            Parameters: [],
            Opens: scope.Opens,
            Properties: scope.Properties,
            Output: []);

}
