namespace KatLang.Semantics;

/// <summary>
/// Syntactic kind of an identifier site in source.
/// </summary>
public enum OccurrenceKind
{
    PropertyDefinition,
    ExplicitParameterDefinition,
    ConditionalBinderDefinition,
    ResolveReference,
    ParameterReference,
    DotMemberReference,
    OpenTargetReference,
    OpenTargetMemberReference,
}

/// <summary>
/// Semantic classification of an identifier occurrence.
/// </summary>
public enum IdentifierClassification
{
    PropertyDefinition,
    PropertyReference,
    ExplicitParameterDefinition,
    ExplicitParameterReference,
    ImplicitParameterReference,
    ConditionalBinderDefinition,
    ConditionalBinderReference,
    Builtin,
    // Value 8 was the retired, never-produced LoadedExternalMemberReference.
    OpenTarget = 9,
    Unresolved,
    /// <summary>
    /// The identifier's meaning cannot be determined without materializing a DEFERRED module
    /// dependency (branch-lazy module loading, B2c): it has no certain lexical resolution, and a
    /// module-backed <c>open</c> whose module is loaded only when its conditional branch is
    /// selected sits in the lookup chain (or is the receiver of the dot member) and may
    /// supply it or make an ordinary open's candidate ambiguous. Neither resolved nor known to be invalid — the semantic model never loads
    /// a branch's modules to find out — so tooling should treat it as indeterminate rather
    /// than as an error, including in completion results. A name that no deferred open could supply stays
    /// <see cref="Unresolved"/>.
    /// </summary>
    DeferredModuleReference,
}

/// <summary>
/// A source-backed identifier occurrence with an exact source span.
/// </summary>
public record IdentifierOccurrence(string Name, SourceSpan Span, OccurrenceKind Kind);

/// <summary>
/// A source-backed declaration site.
/// </summary>
public sealed record DeclarationOccurrence(string Name, SourceSpan Span, OccurrenceKind Kind)
    : IdentifierOccurrence(Name, Span, Kind);

/// <summary>
/// Semantic resolution information for one identifier site of the current document.
/// <see cref="ResolvedDeclaration"/> is the document's declaration occurrence the
/// site resolves to, or <see langword="null"/> when the target has no site in this
/// document: a builtin, an implicit parameter, an unresolved or deferred name, or a
/// property supplied by a load-elaborated module (a module-provided target keeps its
/// <see cref="ResolvedProperty"/> metadata but is locationless with respect to the
/// importing document — see <see cref="PropertyInfo.Declaration"/>).
/// </summary>
public sealed record IdentifierResolution(
    IdentifierOccurrence Occurrence,
    IdentifierClassification Classification,
    DeclarationOccurrence? ResolvedDeclaration,
    PropertyInfo? ResolvedProperty);

/// <summary>
/// Semantic information derived from a parsed KatLang root algorithm.
/// Only source-backed sites with exact spans in the CURRENT document are
/// included: every listed occurrence, declaration, and resolution site slices the
/// document's text to the identifier written there. A load-elaborated module
/// subtree (<c>open 'url'</c>, <c>load('url')</c>) is positioned in the module's
/// own source text, so it contributes no sites at any nesting depth; document
/// references that bind to its members resolve to locationless module-provided
/// targets, and its public names stay visible through the open.
/// </summary>
public sealed class SemanticModel
{
    /// <summary>
    /// Creates a semantic model from parts the builder has already made mutually consistent.
    /// Internal: every public model comes from <see cref="SemanticModelBuilder"/>, so its
    /// occurrences, resolutions, property index, and scopes all describe the same root.
    /// </summary>
    internal SemanticModel(
        Algorithm root,
        IReadOnlyList<IdentifierOccurrence> identifierOccurrences,
        IReadOnlyList<DeclarationOccurrence> declarations,
        IReadOnlyList<IdentifierResolution> identifierResolutions,
        IReadOnlyList<PropertyInfo> propertyInfos,
        IReadOnlyDictionary<DeclarationOccurrence, PropertyInfo> propertiesByDeclaration,
        IReadOnlyList<ScopeVisibility>? scopeVisibilities = null)
    {
        Root = root;
        IdentifierOccurrences = Array.AsReadOnly(identifierOccurrences.ToArray());
        Declarations = Array.AsReadOnly(declarations.ToArray());
        IdentifierResolutions = Array.AsReadOnly(identifierResolutions.ToArray());
        PropertyInfos = Array.AsReadOnly(propertyInfos.ToArray());
        ScopeVisibilities = Array.AsReadOnly(
            (scopeVisibilities ?? [new ScopeVisibility(Span: null, Symbols: [])]).ToArray());
        // Declarations are looked up by canonical occurrence identity, never by
        // name/span value: a value-equal DTO (constructed by a consumer, or shared
        // declaration nodes in a host-built tree) is not a key.
        _propertiesByDeclaration = new Dictionary<DeclarationOccurrence, PropertyInfo>(
            propertiesByDeclaration,
            ReferenceEqualityComparer.Instance);
        _propertiesByName = propertyInfos
            .GroupBy(static property => property.Name, StringComparer.Ordinal)
            .ToDictionary(
                static group => group.Key,
                static group => (IReadOnlyList<PropertyInfo>)Array.AsReadOnly(group.ToArray()),
                StringComparer.Ordinal);
    }

    private readonly IReadOnlyDictionary<DeclarationOccurrence, PropertyInfo> _propertiesByDeclaration;
    private readonly IReadOnlyDictionary<string, IReadOnlyList<PropertyInfo>> _propertiesByName;

    /// <summary>
    /// Root algorithm the model was built from.
    /// </summary>
    public Algorithm Root { get; }

    /// <summary>
    /// Source-backed identifier references and member occurrences.
    /// Declaration sites are exposed separately through <see cref="Declarations"/>.
    /// </summary>
    public IReadOnlyList<IdentifierOccurrence> IdentifierOccurrences { get; }

    /// <summary>
    /// Source-backed declaration sites of the current document. Declarations
    /// inside a load-elaborated module are sites of the module's text, not of
    /// this document, and are never listed.
    /// </summary>
    public IReadOnlyList<DeclarationOccurrence> Declarations { get; }

    /// <summary>
    /// Semantic classifications for all source-backed identifier sites of the
    /// current document, including declarations. When the occurrence resolves
    /// to a property, <see cref="IdentifierResolution.ResolvedProperty"/>
    /// exposes richer property-centered hover metadata; a module-provided target
    /// has no <see cref="IdentifierResolution.ResolvedDeclaration"/>.
    /// </summary>
    public IReadOnlyList<IdentifierResolution> IdentifierResolutions { get; }

    /// <summary>
    /// All property-centered semantic objects known to this model: every
    /// property declared in the current document, plus the targets its sites
    /// resolve to (referenced builtins and module-provided properties, both
    /// without a <see cref="PropertyInfo.Declaration"/>). Ordinary properties
    /// expose parameter information, conditional properties expose branch-head
    /// summaries, and builtins are represented conservatively when their
    /// callable shape is known.
    /// </summary>
    public IReadOnlyList<PropertyInfo> PropertyInfos { get; }

    /// <summary>
    /// The lexical scope regions of this program with their resolved visible-name
    /// sets, root first. Regions are the source hulls of scope content, so nested
    /// scopes appear as contained spans; each region's symbols already apply
    /// shadowing, open dedup/ambiguity, and direct-beats-open precedence, and
    /// exclude prelude names (see <see cref="PreludeCatalog.Symbols"/>). Scopes share
    /// immutable storage (a symbol seen from several scopes is one
    /// <see cref="VisibleSymbol"/> instance), so enumerating every symbol of every scope
    /// costs what its logical output does while the model retains far less.
    /// </summary>
    public IReadOnlyList<ScopeVisibility> ScopeVisibilities { get; }

    /// <summary>
    /// Finds the innermost scope region containing the supplied position (a region is a
    /// half-open source hull, so a position at the hull's exclusive end is outside it),
    /// falling back to the root scope for positions outside every nested region.
    /// </summary>
    public ScopeVisibility FindScopeAt(SourcePosition position)
    {
        ScopeVisibility? root = null;
        ScopeVisibility? best = null;
        SourceSpan? bestHull = null;
        foreach (var scope in ScopeVisibilities)
        {
            if (scope.Span is not { } hull)
            {
                root ??= scope;
                continue;
            }

            if (!hull.Contains(position))
                continue;

            if (best is null
                || scope.NestingDepth > best.NestingDepth
                || (scope.NestingDepth == best.NestingDepth && bestHull is { } current && IsInnerSpan(hull, current)))
            {
                best = scope;
                bestHull = hull;
            }
        }

        return best ?? root ?? new ScopeVisibility(Span: null, Symbols: []);
    }

    /// <summary>
    /// The full effective visible-name set at the supplied position: the innermost
    /// scope's resolved symbols followed by the prelude names they do not shadow.
    /// Dot-only intrinsics (<see cref="PreludeCatalog.DotIntrinsicSymbols"/>) are
    /// not bare-name-visible and are deliberately excluded. The returned read-only list
    /// reads the scope's shared storage in place rather than copying it.
    /// </summary>
    public IReadOnlyList<VisibleSymbol> GetVisibleSymbolsAt(SourcePosition position)
    {
        var scope = FindScopeAt(position);
        if (scope.View is { } view)
        {
            // A builder scope's names are unique and name-indexed: the merged list reads the
            // scope's shared view in place and keeps only the prelude symbols it does not shadow
            // (each checked by one name lookup), instead of copying the scope per query.
            var unshadowed = new List<VisibleSymbol>(PreludeSymbols.Count);
            foreach (var symbol in PreludeSymbols)
            {
                if (view.Find(symbol.Name) is null)
                    unshadowed.Add(symbol);
            }

            return new System.Collections.ObjectModel.ReadOnlyCollection<VisibleSymbol>(
                new MergedVisibleSymbolList(view, unshadowed.ToArray()));
        }

        var result = new List<VisibleSymbol>(scope.Symbols.Count + PreludeSymbols.Count);
        result.AddRange(scope.Symbols);

        var shadowed = new HashSet<string>(StringComparer.Ordinal);
        foreach (var symbol in scope.Symbols)
            shadowed.Add(symbol.Name);

        foreach (var symbol in PreludeSymbols)
        {
            if (!shadowed.Contains(symbol.Name))
                result.Add(symbol);
        }

        return Array.AsReadOnly(result.ToArray());
    }

    /// <summary>
    /// The prelude names of the prelude this model resolved against: <see cref="PreludeCatalog.Symbols"/>,
    /// plus the host operations of the parse the model was built from — ambient prelude members
    /// the owner walk reaches exactly like a builtin.
    /// </summary>
    internal IReadOnlyList<VisibleSymbol> PreludeSymbols { get; init; } = PreludeCatalog.Symbols;

    /// <summary>
    /// True when <paramref name="candidate"/> is the more deeply nested of two
    /// containing scope hulls: it starts later, or starts identically and ends
    /// earlier. Well-formed scope hulls nest, so this picks the innermost region.
    /// </summary>
    private static bool IsInnerSpan(SourceSpan candidate, SourceSpan current)
    {
        var byStart = candidate.Start.CompareTo(current.Start);
        return byStart != 0 ? byStart > 0 : candidate.End < current.End;
    }

    /// <summary>
    /// Finds the first identifier resolution whose site contains the supplied position
    /// (half-open: the site's first column is inside, the column just past its last
    /// character is not).
    /// </summary>
    public IdentifierResolution? FindResolutionAt(SourcePosition position)
        => IdentifierResolutions.FirstOrDefault(resolution => resolution.Occurrence.Span.Contains(position));

    /// <summary>
    /// Finds all identifier resolutions with the supplied name.
    /// </summary>
    public IReadOnlyList<IdentifierResolution> FindResolutions(string name)
    {
        ArgumentNullException.ThrowIfNull(name);
        return Array.AsReadOnly(IdentifierResolutions.Where(resolution => resolution.Occurrence.Name == name).ToArray());
    }

    /// <summary>
    /// Finds all declaration occurrences with the supplied name.
    /// </summary>
    public IReadOnlyList<DeclarationOccurrence> FindDeclarations(string name)
    {
        ArgumentNullException.ThrowIfNull(name);
        return Array.AsReadOnly(Declarations.Where(declaration => declaration.Name == name).ToArray());
    }

    /// <summary>
    /// Finds the first property-centered semantic object whose identifier site
    /// contains the supplied position.
    /// </summary>
    public PropertyInfo? FindPropertyAt(SourcePosition position)
        => FindResolutionAt(position)?.ResolvedProperty;

    /// <summary>
    /// Finds the property-centered semantic object associated with a specific
    /// declaration occurrence. The occurrence must be the canonical instance
    /// returned by this model; a value-equal occurrence constructed elsewhere is
    /// not a declaration identity.
    /// </summary>
    public PropertyInfo? FindPropertyByDeclaration(DeclarationOccurrence declaration)
    {
        ArgumentNullException.ThrowIfNull(declaration);
        return _propertiesByDeclaration.TryGetValue(declaration, out var property)
            ? property
            : null;
    }

    /// <summary>
    /// Finds all known property-centered semantic objects with the supplied name.
    /// </summary>
    public IReadOnlyList<PropertyInfo> FindProperties(string name)
    {
        ArgumentNullException.ThrowIfNull(name);
        return _propertiesByName.TryGetValue(name, out var properties)
            ? properties
            : [];
    }
}
