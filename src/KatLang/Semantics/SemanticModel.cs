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
    /// Member access on a receiver that originates from <c>load(...)</c>, where
    /// the current semantic pass did not verify exported members locally.
    /// This is intentionally more precise than generic <see cref="Unresolved"/>.
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
    DeclarationOccurrence? ResolvedDeclaration);

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
        IReadOnlyList<IdentifierResolution> identifierResolutions)
    {
        Root = root;
        IdentifierOccurrences = identifierOccurrences;
        Declarations = declarations;
        IdentifierResolutions = identifierResolutions;
    }

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
    /// including declarations.
    /// </summary>
    public IReadOnlyList<IdentifierResolution> IdentifierResolutions { get; }

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