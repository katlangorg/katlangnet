using KatLang;
using KatLang.Semantics;

namespace KatLang.ParserFuzz;

/// <summary>
/// Drives the registered editor surface a case selected and checks its surface-specific invariants,
/// plus the classification/builtin invariants that must hold for EVERY built model. Only surfaces
/// that actually exist in <c>KatLang.Semantics</c> are exercised — there is no completion,
/// active-parameter signature help, or incremental parser to drive.
/// </summary>
internal static class EditorSurfaces
{
    private static readonly IReadOnlyDictionary<string, int> BuiltinPlainArity = BuildBuiltinPlainArity();

    private static Dictionary<string, int> BuildBuiltinPlainArity()
    {
        var arities = new Dictionary<string, int>(StringComparer.Ordinal);
        foreach (var descriptor in BuiltinRegistry.AllBuiltins)
            arities[descriptor.Name] = descriptor.PlainParameterNames.Count;
        return arities;
    }

    /// <summary>Core invariants that hold for every built model, independent of the selected surface.</summary>
    public static void CheckCoreInvariants(string source, SemanticModel model)
    {
        CheckCommentsAndStringsAreNotIdentifiers(source, model);
        CheckBuiltinsAreNonSourceAndMatchMetadata(model);
    }

    /// <summary>Drives the focused surface and returns a stable observation summary for the fingerprint.</summary>
    public static string Exercise(EditorCase testCase, EditorToolingResult result, int cursorLine, int cursorColumn)
    {
        if (result.Model is not { } model)
            return "declined";

        return testCase.Parameters.Surface switch
        {
            EditorSurfaceKind.Classification => ExerciseClassification(model),
            EditorSurfaceKind.PositionResolution => ExercisePositionResolution(model, cursorLine, cursorColumn),
            EditorSurfaceKind.PropertyAtPosition => ExercisePropertyAtPosition(model, cursorLine, cursorColumn),
            EditorSurfaceKind.SymbolLookup => ExerciseSymbolLookup(model),
            EditorSurfaceKind.Definition => ExerciseDefinition(model, cursorLine, cursorColumn),
            EditorSurfaceKind.DocumentSymbols => ExerciseDocumentSymbols(model),
            EditorSurfaceKind.Signature => ExerciseSignature(model),
            _ => "unknown-surface",
        };
    }

    public static string ChooseLookupName(SemanticModel model)
    {
        foreach (var declaration in model.Declarations)
            if (declaration.Name.Length > 0)
                return declaration.Name;
        foreach (var resolution in model.IdentifierResolutions)
            if (resolution.Occurrence.Name.Length > 0)
                return resolution.Occurrence.Name;
        return "Output";
    }

    // ── Core invariants ──────────────────────────────────────────────────────

    /// <summary>
    /// No identifier occurrence may overlap a comment or string-literal token: the classifier must
    /// not report identifier semantics on text the lexer put inside a comment or a string.
    /// </summary>
    private static void CheckCommentsAndStringsAreNotIdentifiers(string source, SemanticModel model)
    {
        var (tokens, _) = Lexer.Tokenize(source);
        foreach (var token in tokens)
        {
            if (token.Kind is not (TokenKind.Comment or TokenKind.StringLiteral) || token.Length <= 0)
                continue;

            var tokenSpan = new SourceSpan(token.Line, token.Column, token.Line, token.Column + token.Length - 1);
            foreach (var occurrence in model.IdentifierOccurrences)
            {
                if (Overlaps(occurrence.Span, tokenSpan))
                    throw new EditorInvariantException(
                        $"An identifier occurrence '{occurrence.Name}' at {SourceSpanValidator.Describe(occurrence.Span)} " +
                        $"overlaps a {token.Kind} token at {SourceSpanValidator.Describe(tokenSpan)}: classifier reported " +
                        "identifier semantics inside a comment or string.");
            }
        }
    }

    /// <summary>
    /// Builtins carry no source declaration (a documented non-source result), and every builtin
    /// property surfaced by the model must agree with the runtime metadata's fixed-arity plain
    /// parameter count — read from the registry, never re-declared here.
    /// </summary>
    private static void CheckBuiltinsAreNonSourceAndMatchMetadata(SemanticModel model)
    {
        foreach (var resolution in model.IdentifierResolutions)
        {
            if (resolution.Classification != IdentifierClassification.Builtin)
                continue;

            if (resolution.ResolvedDeclaration is not null)
                throw new EditorInvariantException(
                    $"Builtin '{resolution.Occurrence.Name}' resolved to a SOURCE declaration " +
                    $"{SourceSpanValidator.Describe(resolution.ResolvedDeclaration.Span)}: builtins must use a non-source result.");

            if (resolution.ResolvedProperty is { } property)
                CheckBuiltinArity(property);
        }
    }

    private static void CheckBuiltinArity(PropertyInfo property)
    {
        if (!BuiltinPlainArity.TryGetValue(property.Name, out var expected))
            return;

        var actual = property.GetParameters(PropertyCallStyle.Plain).Count;
        if (actual != expected)
            throw new EditorInvariantException(
                $"Builtin '{property.Name}' surfaces {actual} plain parameter(s) but the runtime metadata declares " +
                $"{expected}: builtin arity metadata drift.");
    }

    // ── Surface exercises ────────────────────────────────────────────────────

    private static string ExerciseClassification(SemanticModel model)
    {
        var kinds = new SortedSet<string>(StringComparer.Ordinal);
        foreach (var resolution in model.IdentifierResolutions)
            kinds.Add(resolution.Classification.ToString());
        return $"classifications={kinds.Count}";
    }

    private static string ExercisePositionResolution(SemanticModel model, int line, int column)
    {
        var resolution = model.FindResolutionAt(line, column);
        if (resolution is null)
            return "resolution=none";

        if (!Contains(resolution.Occurrence.Span, line, column))
            throw new EditorInvariantException(
                $"FindResolutionAt({line},{column}) returned a resolution whose span " +
                $"{SourceSpanValidator.Describe(resolution.Occurrence.Span)} does not contain the queried position.");

        if (!model.IdentifierResolutions.Contains(resolution))
            throw new EditorInvariantException(
                $"FindResolutionAt({line},{column}) returned a resolution the model does not list.");

        return $"resolution={resolution.Classification}";
    }

    private static string ExercisePropertyAtPosition(SemanticModel model, int line, int column)
    {
        var property = model.FindPropertyAt(line, column);
        if (property is null)
            return "property=none";

        if (EditorModel.IsSyntheticName(property.Name))
            throw new EditorInvariantException(
                $"FindPropertyAt({line},{column}) returned a synthetic property '{property.Name}'.");

        if (!model.FindProperties(property.Name).Contains(property))
            throw new EditorInvariantException(
                $"FindPropertyAt({line},{column}) returned a property '{property.Name}' the model does not list.");

        return $"property={property.Shape}";
    }

    private static string ExerciseSymbolLookup(SemanticModel model)
    {
        var name = ChooseLookupName(model);

        var resolutionsByFilter = model.IdentifierResolutions.Count(r => r.Occurrence.Name == name);
        if (model.FindResolutions(name).Count != resolutionsByFilter)
            throw new EditorInvariantException(
                $"FindResolutions('{name}') returned {model.FindResolutions(name).Count} but {resolutionsByFilter} " +
                "resolutions carry that name.");

        var declarationsByFilter = model.Declarations.Count(d => d.Name == name);
        if (model.FindDeclarations(name).Count != declarationsByFilter)
            throw new EditorInvariantException(
                $"FindDeclarations('{name}') returned {model.FindDeclarations(name).Count} but {declarationsByFilter} " +
                "declarations carry that name.");

        var propertiesByFilter = model.PropertyInfos.Count(p => p.Name == name);
        if (model.FindProperties(name).Count != propertiesByFilter)
            throw new EditorInvariantException(
                $"FindProperties('{name}') returned {model.FindProperties(name).Count} but {propertiesByFilter} " +
                "property metadata objects carry that name.");

        return $"lookup={model.FindResolutions(name).Count}/{model.FindDeclarations(name).Count}/{model.FindProperties(name).Count}";
    }

    private static string ExerciseDefinition(SemanticModel model, int line, int column)
    {
        var resolution = model.FindResolutionAt(line, column);
        if (resolution?.ResolvedDeclaration is not { } declaration)
            return "definition=none";

        if (!model.Declarations.Contains(declaration))
            throw new EditorInvariantException(
                $"Go-to-definition at ({line},{column}) targets a declaration the model does not list.");

        return "definition=source";
    }

    private static string ExerciseDocumentSymbols(SemanticModel model)
    {
        foreach (var declaration in model.Declarations)
            if (EditorModel.IsSyntheticName(declaration.Name))
                throw new EditorInvariantException(
                    $"A document symbol '{declaration.Name}' is synthetic: internal helpers must not appear in the outline.");

        return $"symbols={model.Declarations.Count}/{model.PropertyInfos.Count}";
    }

    private static string ExerciseSignature(SemanticModel model)
    {
        var count = 0;
        foreach (var property in model.PropertyInfos)
        {
            _ = property.DisplaySignature;
            foreach (var signature in property.Signatures)
            {
                count++;
                if (!ReferenceEquals(property.GetParameters(signature.CallStyle), signature.Parameters)
                    && property.GetParameters(signature.CallStyle).Count != signature.Parameters.Count)
                    throw new EditorInvariantException(
                        $"Signature parameters of '{property.Name}' ({signature.CallStyle}) are inconsistent between " +
                        "the signature list and GetParameters.");
            }
        }

        return $"signatures={count}";
    }

    // ── Span helpers ─────────────────────────────────────────────────────────

    private static bool Contains(SourceSpan span, int line, int column)
    {
        if (line < span.StartLineNumber || line > span.EndLineNumber)
            return false;
        if (line == span.StartLineNumber && column < span.StartColumn)
            return false;
        if (line == span.EndLineNumber && column > span.EndColumn)
            return false;
        return true;
    }

    private static bool Overlaps(SourceSpan left, SourceSpan right)
        => ComparePosition(left.StartLineNumber, left.StartColumn, right.EndLineNumber, right.EndColumn) <= 0
           && ComparePosition(right.StartLineNumber, right.StartColumn, left.EndLineNumber, left.EndColumn) <= 0;

    private static int ComparePosition(int line, int column, int otherLine, int otherColumn)
    {
        var byLine = line.CompareTo(otherLine);
        return byLine != 0 ? byLine : column.CompareTo(otherColumn);
    }
}
