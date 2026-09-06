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
    /// <summary>
    /// Legacy classification retained for API compatibility.
    /// The default public front-end should not produce this because successful
    /// parse/elaboration removes unresolved <c>load</c> outside deferred regions, which use
    /// <see cref="DeferredModuleReference"/> instead.
    /// </summary>
    LoadedExternalMemberReference,
    OpenTarget,
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
/// Semantic resolution information for one identifier site.
/// </summary>
public sealed record IdentifierResolution(
    IdentifierOccurrence Occurrence,
    IdentifierClassification Classification,
    DeclarationOccurrence? ResolvedDeclaration,
    PropertyInfo? ResolvedProperty);

/// <summary>
/// Semantic information derived from a parsed KatLang root algorithm.
/// Only source-backed sites with exact spans are included.
/// </summary>
public sealed class SemanticModel
{
    /// <summary>
    /// Creates a semantic model.
    /// </summary>
    public SemanticModel(
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
        // Declaration coordinates are local to their source document. Preserve
        // canonical occurrence identity so equal name/span DTOs from different
        // loaded modules cannot overwrite one another.
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
    /// Source-backed declaration sites.
    /// </summary>
    public IReadOnlyList<DeclarationOccurrence> Declarations { get; }

    /// <summary>
    /// Semantic classifications for all source-backed identifier sites,
    /// including declarations. When the occurrence resolves to a property,
    /// <see cref="IdentifierResolution.ResolvedProperty"/> exposes richer
    /// property-centered hover metadata.
    /// </summary>
    public IReadOnlyList<IdentifierResolution> IdentifierResolutions { get; }

    /// <summary>
    /// All property-centered semantic objects known to this model.
    /// Ordinary properties expose parameter information, conditional
    /// properties expose branch-head summaries, and builtins are represented
    /// conservatively when their callable shape is known.
    /// </summary>
    public IReadOnlyList<PropertyInfo> PropertyInfos { get; }

    /// <summary>
    /// The lexical scope regions of this program with their resolved visible-name
    /// sets, root first. Regions are the source hulls of scope content, so nested
    /// scopes appear as contained spans; each region's symbols already apply
    /// shadowing, open dedup/ambiguity, and direct-beats-open precedence, and
    /// exclude prelude names (see <see cref="PreludeCatalog.Symbols"/>).
    /// </summary>
    public IReadOnlyList<ScopeVisibility> ScopeVisibilities { get; }

    /// <summary>
    /// Finds the innermost scope region containing the supplied position, falling
    /// back to the root scope for positions outside every nested region.
    /// </summary>
    public ScopeVisibility FindScopeAt(int lineNumber, int column)
    {
        ScopeVisibility? root = null;
        ScopeVisibility? best = null;

        foreach (var scope in ScopeVisibilities)
        {
            if (scope.Span is null)
            {
                root ??= scope;
                continue;
            }

            if (!Contains(scope.Span, lineNumber, column))
                continue;

            if (best is null
                || scope.NestingDepth > best.NestingDepth
                || (scope.NestingDepth == best.NestingDepth && IsInnerSpan(scope.Span, best.Span!)))
                best = scope;
        }

        return best ?? root ?? new ScopeVisibility(Span: null, Symbols: []);
    }

    /// <summary>
    /// The full effective visible-name set at the supplied position: the innermost
    /// scope's resolved symbols followed by the prelude names they do not shadow.
    /// Dot-only intrinsics (<see cref="PreludeCatalog.DotIntrinsicSymbols"/>) are
    /// not bare-name-visible and are deliberately excluded.
    /// </summary>
    public IReadOnlyList<VisibleSymbol> GetVisibleSymbolsAt(int lineNumber, int column)
    {
        var scope = FindScopeAt(lineNumber, column);
        var result = new List<VisibleSymbol>(scope.Symbols.Count + PreludeCatalog.Symbols.Count);
        result.AddRange(scope.Symbols);

        var shadowed = new HashSet<string>(StringComparer.Ordinal);
        foreach (var symbol in scope.Symbols)
            shadowed.Add(symbol.Name);

        foreach (var symbol in PreludeCatalog.Symbols)
        {
            if (!shadowed.Contains(symbol.Name))
                result.Add(symbol);
        }

        return Array.AsReadOnly(result.ToArray());
    }

    /// <summary>
    /// True when <paramref name="candidate"/> is the more deeply nested of two
    /// containing scope hulls: it starts later, or starts identically and ends
    /// earlier. Well-formed scope hulls nest, so this picks the innermost region.
    /// </summary>
    private static bool IsInnerSpan(SourceSpan candidate, SourceSpan current)
    {
        var byStart = candidate.StartLineNumber != current.StartLineNumber
            ? candidate.StartLineNumber.CompareTo(current.StartLineNumber)
            : candidate.StartColumn.CompareTo(current.StartColumn);
        if (byStart != 0)
            return byStart > 0;

        var byEnd = candidate.EndLineNumber != current.EndLineNumber
            ? candidate.EndLineNumber.CompareTo(current.EndLineNumber)
            : candidate.EndColumn.CompareTo(current.EndColumn);
        return byEnd < 0;
    }

    /// <summary>
    /// Finds the first identifier resolution whose span contains the supplied position.
    /// </summary>
    public IdentifierResolution? FindResolutionAt(int lineNumber, int column)
        => IdentifierResolutions.FirstOrDefault(resolution => Contains(resolution.Occurrence.Span, lineNumber, column));

    /// <summary>
    /// Finds all identifier resolutions with the supplied name.
    /// </summary>
    public IReadOnlyList<IdentifierResolution> FindResolutions(string name)
        => IdentifierResolutions.Where(resolution => resolution.Occurrence.Name == name).ToList();

    /// <summary>
    /// Finds all declaration occurrences with the supplied name.
    /// </summary>
    public IReadOnlyList<DeclarationOccurrence> FindDeclarations(string name)
        => Declarations.Where(declaration => declaration.Name == name).ToList();

    /// <summary>
    /// Finds the first property-centered semantic object whose identifier site
    /// contains the supplied position.
    /// </summary>
    public PropertyInfo? FindPropertyAt(int lineNumber, int column)
        => FindResolutionAt(lineNumber, column)?.ResolvedProperty;

    /// <summary>
    /// Finds the property-centered semantic object associated with a specific
    /// declaration occurrence. The occurrence must be the canonical instance
    /// returned by this model; source coordinates alone are not a cross-module
    /// declaration identity.
    /// </summary>
    public PropertyInfo? FindPropertyByDeclaration(DeclarationOccurrence declaration)
        => _propertiesByDeclaration.TryGetValue(declaration, out var property)
            ? property
            : null;

    /// <summary>
    /// Finds all known property-centered semantic objects with the supplied name.
    /// </summary>
    public IReadOnlyList<PropertyInfo> FindProperties(string name)
        => _propertiesByName.TryGetValue(name, out var properties)
            ? properties
            : [];

    private static bool Contains(SourceSpan span, int lineNumber, int column)
    {
        if (lineNumber < span.StartLineNumber || lineNumber > span.EndLineNumber)
            return false;

        if (lineNumber == span.StartLineNumber && column < span.StartColumn)
            return false;

        if (lineNumber == span.EndLineNumber && column > span.EndColumn)
            return false;

        return true;
    }
}
