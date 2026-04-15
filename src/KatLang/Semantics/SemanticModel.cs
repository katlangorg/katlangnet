namespace KatLang.Semantics;

/// <summary>
/// Syntactic kind of an identifier site in source.
/// </summary>
public enum OccurrenceKind
{
    PropertyDefinition,
    ExplicitParameterDefinition,
    ConditionalBinderDefinition,
    ReservedNameDefinition,
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
    /// parse/elaboration removes unresolved <c>load</c> before semantic modeling.
    /// </summary>
    LoadedExternalMemberReference,
    OpenTarget,
    ReservedName,
    Unresolved,
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
        IReadOnlyDictionary<DeclarationOccurrence, PropertyInfo> propertiesByDeclaration)
    {
        Root = root;
        IdentifierOccurrences = identifierOccurrences;
        Declarations = declarations;
        IdentifierResolutions = identifierResolutions;
        PropertyInfos = propertyInfos;
        _propertiesByDeclaration = new Dictionary<DeclarationOccurrence, PropertyInfo>(propertiesByDeclaration);
        _propertiesByName = propertyInfos
            .GroupBy(static property => property.Name, StringComparer.Ordinal)
            .ToDictionary(
                static group => group.Key,
                static group => (IReadOnlyList<PropertyInfo>)group.ToList(),
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
    /// declaration occurrence.
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