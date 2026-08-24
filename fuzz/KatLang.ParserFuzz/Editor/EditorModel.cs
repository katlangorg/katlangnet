using System.Globalization;
using System.Text;
using KatLang;
using KatLang.Semantics;

namespace KatLang.ParserFuzz;

/// <summary>Whether a semantic model was built, or why the tooling declined.</summary>
internal enum EditorToolingOutcome
{
    /// <summary>A semantic model was built and is available for querying.</summary>
    Built,

    /// <summary>The AST still carries an unresolved <c>load</c> directive. Building a semantic model
    /// from it is a documented contract violation (<c>SemanticModelBuilder.Build</c> throws), so the
    /// tooling declines exactly as a correct editor caller must, rather than tripping the guard.</summary>
    DeclinedUnresolvedLoad,
}

/// <summary>What one tooling request produced.</summary>
internal sealed record EditorToolingResult(
    EditorToolingOutcome Outcome,
    SemanticModel? Model,
    Algorithm Root,
    IReadOnlyList<Diagnostic> Diagnostics);

/// <summary>
/// The editor-tooling oracle. Runs the real parser/front end and <c>SemanticModelBuilder</c>, holds
/// the builtin-name and synthetic-name oracles read from production metadata (never re-declared),
/// checks every invariant the semantic model must satisfy, and produces a deterministic structural
/// digest of a model plus the cursor query results for the determinism comparisons.
/// </summary>
internal static class EditorModel
{
    /// <summary>
    /// Every name the semantic model is allowed to classify as a builtin, read from the production
    /// registry rather than re-declared here. A name outside this set classified as a builtin would
    /// be an invented symbol.
    /// </summary>
    public static readonly IReadOnlySet<string> AllowedBuiltinNames = BuildAllowedBuiltinNames();

    private static HashSet<string> BuildAllowedBuiltinNames()
    {
        var names = new HashSet<string>(StringComparer.Ordinal);
        foreach (var name in BuiltinRegistry.BuiltinNames) names.Add(name);
        foreach (var name in BuiltinRegistry.MathMemberNames) names.Add(name);
        foreach (var name in BuiltinRegistry.MathAliasNames) names.Add(name);
        names.Add("Math");
        names.Add("string");
        // `spread` is deliberately NOT here: since the star syntax landed it is an ordinary
        // identifier, so the tooling classifying it as a builtin would be an invented symbol.
        names.Add("load");
        return names;
    }

    /// <summary>
    /// Runs the tooling request: parse to the requested boundary, decline if the AST carries an
    /// unresolved load, otherwise build the semantic model. An unexpected exception escapes — only
    /// the documented unresolved-load contract is caught, and it is caught by PRE-CHECK, not by
    /// swallowing the guard's throw.
    /// </summary>
    public static EditorToolingResult Run(string source, EditorExecutionMode mode)
    {
        ArgumentNullException.ThrowIfNull(source);

        Algorithm root;
        IReadOnlyList<Diagnostic> diagnostics;
        if (mode == EditorExecutionMode.Elaborated)
        {
            var parsed = Parser.Parse(source);
            root = parsed.Root;
            diagnostics = parsed.Diagnostics;
        }
        else
        {
            var syntax = Parser.ParseSyntax(source);
            root = syntax.Root;
            diagnostics = syntax.Diagnostics;
        }

        if (LoadElaborationGuard.TryFindFirstUnresolvedLoad(root, out _))
            return new EditorToolingResult(EditorToolingOutcome.DeclinedUnresolvedLoad, null, root, diagnostics);

        var model = SemanticModelBuilder.Build(root);
        return new EditorToolingResult(EditorToolingOutcome.Built, model, root, diagnostics);
    }

    public static bool IsSyntheticName(string name)
        => name.Length == 0 || name.Contains('$', StringComparison.Ordinal);

    // ── Model invariants ─────────────────────────────────────────────────────

    /// <summary>
    /// Checks every property the semantic model must satisfy for the current source. A violation
    /// throws <see cref="EditorInvariantException"/>, which escapes to the fuzzing engine.
    /// </summary>
    public static void ValidateModel(string source, SemanticModel model)
    {
        ArgumentNullException.ThrowIfNull(source);
        ArgumentNullException.ThrowIfNull(model);

        var lineWidths = SourceSpanValidator.LineWidths(source);

        CheckOrdering(model);

        foreach (var occurrence in model.IdentifierOccurrences)
        {
            ValidateSpan(source, lineWidths, occurrence.Span, $"occurrence '{Safe(occurrence.Name)}'");
            CheckNoSynthetic(occurrence.Name, "identifier occurrence");
            CheckSlice(source, occurrence.Span, occurrence.Name, "occurrence");
        }

        foreach (var declaration in model.Declarations)
        {
            ValidateSpan(source, lineWidths, declaration.Span, $"declaration '{Safe(declaration.Name)}'");
            CheckNoSynthetic(declaration.Name, "declaration");
            CheckSlice(source, declaration.Span, declaration.Name, "declaration");
        }

        foreach (var resolution in model.IdentifierResolutions)
        {
            ValidateSpan(source, lineWidths, resolution.Occurrence.Span, $"resolution '{Safe(resolution.Occurrence.Name)}'");
            CheckNoSynthetic(resolution.Occurrence.Name, "resolution occurrence");
            CheckResolvedDeclaration(model, lineWidths, source, resolution);
            CheckBuiltin(resolution);
        }

        foreach (var property in model.PropertyInfos)
        {
            CheckNoSynthetic(property.Name, "property metadata");
            if (property.Declaration is { } declaration)
                ValidateSpan(source, lineWidths, declaration.Span, $"property '{Safe(property.Name)}' declaration");

            foreach (var parameter in property.Parameters)
                if (parameter.Span is { } parameterSpan)
                    ValidateSpan(source, lineWidths, parameterSpan, $"parameter '{Safe(parameter.Name)}' of '{Safe(property.Name)}'");

            foreach (var signature in property.Signatures)
                foreach (var parameter in signature.Parameters)
                    if (parameter.Span is { } parameterSpan)
                        ValidateSpan(source, lineWidths, parameterSpan, $"signature parameter '{Safe(parameter.Name)}'");

            foreach (var branch in property.ConditionalBranches)
                if (branch.HeadSpan is { } headSpan)
                    ValidateSpan(source, lineWidths, headSpan, $"branch head of '{Safe(property.Name)}'");
        }

        CheckLookupConsistency(model);
    }

    private static void CheckOrdering(SemanticModel model)
    {
        RequireSortedBySpan(model.IdentifierOccurrences.Select(o => o.Span), "identifier occurrences");
        RequireSortedBySpan(model.Declarations.Select(d => d.Span), "declarations");
        RequireSortedBySpan(model.IdentifierResolutions.Select(r => r.Occurrence.Span), "identifier resolutions");
    }

    private static void RequireSortedBySpan(IEnumerable<SourceSpan> spans, string what)
    {
        SourceSpan? previous = null;
        foreach (var span in spans)
        {
            if (previous is not null && CompareSpan(previous, span) > 0)
                throw new EditorInvariantException(
                    $"The model's {what} are not sorted by span: {SourceSpanValidator.Describe(previous)} " +
                    $"precedes {SourceSpanValidator.Describe(span)} out of order.");
            previous = span;
        }
    }

    private static void CheckResolvedDeclaration(
        SemanticModel model, int[] lineWidths, string source, IdentifierResolution resolution)
    {
        if (resolution.ResolvedDeclaration is not { } declaration)
            return;

        ValidateSpan(source, lineWidths, declaration.Span, $"resolved declaration of '{Safe(resolution.Occurrence.Name)}'");

        if (!string.Equals(declaration.Name, resolution.Occurrence.Name, StringComparison.Ordinal))
            throw new EditorInvariantException(
                $"Resolution of '{Safe(resolution.Occurrence.Name)}' points to a declaration named " +
                $"'{Safe(declaration.Name)}': tooling resolved an identifier to a differently named symbol.");

        if (!model.Declarations.Contains(declaration))
            throw new EditorInvariantException(
                $"Resolution of '{Safe(resolution.Occurrence.Name)}' points to a declaration " +
                $"{SourceSpanValidator.Describe(declaration.Span)} that is not among the model's declarations: " +
                "the target is outside the current source's declared symbols.");
    }

    private static void CheckBuiltin(IdentifierResolution resolution)
    {
        if (resolution.Classification != IdentifierClassification.Builtin)
            return;

        if (!AllowedBuiltinNames.Contains(resolution.Occurrence.Name))
            throw new EditorInvariantException(
                $"Tooling classified '{Safe(resolution.Occurrence.Name)}' as a builtin, but no such builtin exists in " +
                "the runtime metadata: an invented builtin symbol.");
    }

    private static void CheckLookupConsistency(SemanticModel model)
    {
        foreach (var declaration in model.Declarations)
        {
            if (!model.FindDeclarations(declaration.Name).Contains(declaration))
                throw new EditorInvariantException(
                    $"FindDeclarations('{Safe(declaration.Name)}') does not return a declaration the model lists.");
        }

        foreach (var property in model.PropertyInfos)
        {
            if (!model.FindProperties(property.Name).Contains(property))
                throw new EditorInvariantException(
                    $"FindProperties('{Safe(property.Name)}') does not return a property metadata object the model lists.");
        }

        foreach (var resolution in model.IdentifierResolutions)
        {
            var start = resolution.Occurrence.Span;
            var hit = model.FindResolutionAt(start.StartLineNumber, start.StartColumn);
            if (hit is null)
                throw new EditorInvariantException(
                    $"FindResolutionAt returns nothing at the start {SourceSpanValidator.Describe(start)} of an " +
                    $"occurrence '{Safe(resolution.Occurrence.Name)}' the model itself recorded.");
        }
    }

    private static void ValidateSpan(string source, int[] lineWidths, SourceSpan span, string what)
    {
        var problem = SourceSpanValidator.Validate(span, lineWidths);
        if (problem is not null)
            throw new EditorInvariantException(
                $"The span of {what} is invalid for the {source.Length.ToString(CultureInfo.InvariantCulture)}-code-unit " +
                $"source: {SourceSpanValidator.Describe(span)} ({problem}).");
    }

    private static void CheckNoSynthetic(string name, string what)
    {
        if (IsSyntheticName(name))
            throw new EditorInvariantException(
                $"A synthetic/internal name '{Safe(name)}' leaked into {what}: only source-backed identifiers may surface.");
    }

    /// <summary>
    /// The source text under an occurrence's span must be exactly the reported name — proof the site
    /// is source-backed with an exact span and no invented text. Skipped only where a carriage return
    /// inside the span region makes the offset mapping ambiguous, which never happens for an
    /// identifier token but is guarded against defensively.
    /// </summary>
    private static void CheckSlice(string source, SourceSpan span, string name, string what)
    {
        if (span.StartLineNumber != span.EndLineNumber)
            return;

        var start = EditorCursor.OffsetAtLineColumn(source, span.StartLineNumber, span.StartColumn);
        var endInclusive = EditorCursor.OffsetAtLineColumn(source, span.EndLineNumber, span.EndColumn);
        if (start < 0 || endInclusive < 0 || endInclusive < start || endInclusive >= source.Length)
            return;

        var slice = source[start..(endInclusive + 1)];
        if (slice.Contains('\r', StringComparison.Ordinal))
            return;

        if (!string.Equals(slice, name, StringComparison.Ordinal))
            throw new EditorInvariantException(
                $"The source under a {what} span {SourceSpanValidator.Describe(span)} is '{Safe(slice)}' but the tooling " +
                $"reports the name '{Safe(name)}': the span and the reported identifier disagree.");
    }

    // ── Deterministic digest ─────────────────────────────────────────────────

    /// <summary>
    /// A full structural digest of a tooling request: the whole model plus the cursor query results.
    /// Two requests for the same source, cursor and mode must produce the identical digest.
    /// </summary>
    public static string Digest(EditorToolingResult result, int cursorLine, int cursorColumn, string lookupName)
    {
        var builder = new StringBuilder(1024);
        builder.Append("outcome:").Append(result.Outcome).Append('\n');
        builder.Append("diagnostics:").Append(result.Diagnostics.Count).Append('\n');

        if (result.Model is not { } model)
            return builder.ToString();

        builder.Append("occurrences:").Append(model.IdentifierOccurrences.Count).Append('\n');
        foreach (var occurrence in model.IdentifierOccurrences)
            builder.Append(' ').Append(occurrence.Kind).Append('|').Append(Span(occurrence.Span)).Append('|')
                   .Append(occurrence.Name).Append('\n');

        builder.Append("declarations:").Append(model.Declarations.Count).Append('\n');
        foreach (var declaration in model.Declarations)
            builder.Append(' ').Append(declaration.Kind).Append('|').Append(Span(declaration.Span)).Append('|')
                   .Append(declaration.Name).Append('\n');

        builder.Append("resolutions:").Append(model.IdentifierResolutions.Count).Append('\n');
        foreach (var resolution in model.IdentifierResolutions)
        {
            builder.Append(' ').Append(resolution.Classification).Append('|').Append(Span(resolution.Occurrence.Span))
                   .Append('|').Append(resolution.ResolvedDeclaration is { } d ? Span(d.Span) : "-")
                   .Append('|').Append(resolution.ResolvedProperty is { } p ? $"{p.Name}:{p.Shape}" : "-").Append('\n');
        }

        builder.Append("properties:").Append(model.PropertyInfos.Count).Append('\n');
        foreach (var property in model.PropertyInfos)
        {
            builder.Append(' ').Append(property.Name).Append('|').Append(property.Shape).Append('|')
                   .Append(property.IsPublic ? "public" : "private").Append('|').Append(property.Exposure).Append('|')
                   .Append(property.DisplaySignature).Append('|')
                   .Append(string.Join(',', property.Parameters.Select(parameter => $"{parameter.Kind}:{parameter.DisplayName}")))
                   .Append('\n');
        }

        var resolutionAt = model.FindResolutionAt(cursorLine, cursorColumn);
        builder.Append("cursorResolution:")
               .Append(resolutionAt is null ? "none" : $"{resolutionAt.Classification}|{Span(resolutionAt.Occurrence.Span)}")
               .Append('\n');

        var propertyAt = model.FindPropertyAt(cursorLine, cursorColumn);
        builder.Append("cursorProperty:").Append(propertyAt is null ? "none" : $"{propertyAt.Name}:{propertyAt.Shape}").Append('\n');

        builder.Append("lookupResolutions:").Append(model.FindResolutions(lookupName).Count).Append('\n');
        builder.Append("lookupDeclarations:").Append(model.FindDeclarations(lookupName).Count).Append('\n');
        builder.Append("lookupProperties:").Append(model.FindProperties(lookupName).Count).Append('\n');

        return builder.ToString();
    }

    private static string Span(SourceSpan span)
        => $"{span.StartLineNumber}:{span.StartColumn}-{span.EndLineNumber}:{span.EndColumn}";

    private static int CompareSpan(SourceSpan x, SourceSpan y)
    {
        var byStartLine = x.StartLineNumber.CompareTo(y.StartLineNumber);
        if (byStartLine != 0) return byStartLine;
        var byStartColumn = x.StartColumn.CompareTo(y.StartColumn);
        if (byStartColumn != 0) return byStartColumn;
        var byEndLine = x.EndLineNumber.CompareTo(y.EndLineNumber);
        if (byEndLine != 0) return byEndLine;
        return x.EndColumn.CompareTo(y.EndColumn);
    }

    /// <summary>Diagnostic/identifier text may contain an isolated surrogate; keep reports well-formed.</summary>
    private static string Safe(string text)
    {
        var builder = new StringBuilder(text.Length);
        foreach (var c in text) builder.Append(c is >= ' ' and <= '~' ? c : '?');
        return builder.ToString();
    }
}
