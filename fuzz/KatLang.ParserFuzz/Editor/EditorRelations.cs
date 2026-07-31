using System.Text;
using KatLang;
using KatLang.Semantics;

namespace KatLang.ParserFuzz;

/// <summary>Which editor metamorphic relations ran for a case, and why the others did not.</summary>
internal sealed record EditorRelationOutcome(IReadOnlyList<string> Checked, IReadOnlyList<string> Skipped)
{
    public static readonly EditorRelationOutcome None = new([], []);

    /// <summary>Stable one-field summary for the fingerprint.</summary>
    public string Summary => Checked.Count == 0 ? "none" : string.Join('+', Checked);
}

/// <summary>
/// Trusted metamorphic relations over small source transforms. Each states a property of the current
/// documented tooling contract and names the precondition that makes it true; where a transform is
/// only neutral under conditions, the relation checks those conditions before asserting rather than
/// asserting a false equivalence.
///
/// <para>The comparison currency is a SPAN-FREE shape signature — the sorted set of
/// <c>(occurrence kind, classification, name, resolved-declaration name)</c> tuples — so a transform
/// that legitimately shifts offsets (whitespace, line endings, an appended declaration) is compared
/// on structure, not on absolute positions, while a transform that changes meaning is caught.</para>
/// </summary>
internal static class EditorRelations
{
    public const string WhitespaceNeutral = "whitespace-neutral";
    public const string LineEndingNeutral = "line-ending-neutral";
    public const string Rename = "rename";
    public const string UnrelatedDeclaration = "unrelated-declaration";
    public const string DottedOrdinary = "dotted-ordinary";

    public static EditorRelationOutcome Check(EditorCase testCase, EditorToolingResult baseResult, ref EditorPhase phase)
    {
        ArgumentNullException.ThrowIfNull(testCase);
        ArgumentNullException.ThrowIfNull(baseResult);

        var ran = new List<string>(5);
        var skipped = new List<string>(5);
        var mode = testCase.Parameters.ExecutionMode;

        phase = EditorPhase.RelationWhitespace;
        Run(WhitespaceNeutral, () => CheckWhitespaceNeutral(testCase, mode), ran, skipped);

        phase = EditorPhase.RelationLineEnding;
        Run(LineEndingNeutral, () => CheckLineEndingNeutral(testCase, mode), ran, skipped);

        phase = EditorPhase.RelationRename;
        Run(Rename, () => CheckRename(testCase, baseResult, mode), ran, skipped);

        phase = EditorPhase.RelationUnrelated;
        Run(UnrelatedDeclaration, () => CheckUnrelatedDeclaration(testCase, mode), ran, skipped);

        phase = EditorPhase.RelationDotted;
        Run(DottedOrdinary, () => CheckDottedOrdinary(testCase, baseResult), ran, skipped);

        return new EditorRelationOutcome(ran, skipped);
    }

    private static void Run(string name, Func<string?> check, List<string> ran, List<string> skipped)
    {
        var skipReason = check();
        if (skipReason is null) ran.Add(name);
        else skipped.Add(skipReason);
    }

    // ── Whitespace neutrality ────────────────────────────────────────────────

    private static string? CheckWhitespaceNeutral(EditorCase testCase, EditorExecutionMode mode)
    {
        if (EditorModel.Run(testCase.Source, mode).Model is not { } model)
            return "whitespace-model-not-built";

        var neutralIndex = FindNeutralSpaceIndex(testCase.Source);
        if (neutralIndex < 0)
            return "no-neutral-inter-token-space";

        var doubled = testCase.Source[..neutralIndex] + ' ' + testCase.Source[neutralIndex..];
        if (EditorModel.Run(doubled, mode).Model is not { } doubledModel)
            return "whitespace-doubled-model-not-built";

        RequireSameShape(WhitespaceNeutral, model, doubledModel, Identity, Identity);
        return null;
    }

    /// <summary>An index of a space that sits strictly between two tokens, where duplicating it cannot
    /// change tokenization. Returns -1 when there is no such position.</summary>
    private static int FindNeutralSpaceIndex(string source)
    {
        var (tokens, _) = Lexer.Tokenize(source);
        for (var i = 0; i + 1 < tokens.Count; i++)
        {
            var gapStart = tokens[i].Position + tokens[i].Length;
            var gapEnd = tokens[i + 1].Position;
            for (var j = gapStart; j < gapEnd; j++)
                if (source[j] == ' ')
                    return j;
        }

        return -1;
    }

    // ── Line-ending neutrality ───────────────────────────────────────────────

    private static string? CheckLineEndingNeutral(EditorCase testCase, EditorExecutionMode mode)
    {
        var lf = EditorSourceBuilder.BuildWithLineEndings(testCase.Parameters, EditorLineEndingMode.Lf);
        if (lf.Source.Contains('\r', StringComparison.Ordinal))
            return "source-supplies-its-own-cr";
        if (!lf.Source.Contains('\n', StringComparison.Ordinal))
            return "no-line-break-to-re-encode";

        var crlf = EditorSourceBuilder.BuildWithLineEndings(testCase.Parameters, EditorLineEndingMode.Crlf);

        if (EditorModel.Run(lf.Source, mode).Model is not { } lfModel)
            return "lf-model-not-built";
        if (EditorModel.Run(crlf.Source, mode).Model is not { } crlfModel)
            return "crlf-model-not-built";

        RequireSameShape(LineEndingNeutral, lfModel, crlfModel, Identity, Identity);
        return null;
    }

    // ── Rename ───────────────────────────────────────────────────────────────

    private static string? CheckRename(EditorCase testCase, EditorToolingResult baseResult, EditorExecutionMode mode)
    {
        if (HasErrors(baseResult) || baseResult.Model is not { } model)
            return "rename-requires-a-clean-model";

        if (TryChooseRenameTarget(model, out var target, out var newName) is false)
            return "no-uniquely-scoped-renameable-symbol";

        var renamed = RenameOccurrences(testCase.Source, model, target, newName);
        if (renamed is null)
            return "rename-could-not-rewrite-source";

        var renamedResult = EditorModel.Run(renamed, mode);
        if (HasErrors(renamedResult) || renamedResult.Model is not { } renamedModel)
            return "renamed-source-does-not-reparse-cleanly";

        // The renamed model must equal the original with every occurrence of the old name mapped to
        // the new one, and the old name must have vanished entirely.
        RequireSameShape(Rename, model, renamedModel, name => name == target ? newName : name, Identity);

        if (renamedModel.FindDeclarations(target).Count != 0 || renamedModel.FindResolutions(target).Count != 0)
            throw new EditorInvariantException(
                $"{Rename}: the old name '{target}' still resolves after renaming every occurrence to '{newName}'.");

        if (renamedModel.FindDeclarations(newName).Count == 0)
            throw new EditorInvariantException(
                $"{Rename}: the new name '{newName}' has no declaration after the rename.");

        return null;
    }

    private static bool TryChooseRenameTarget(SemanticModel model, out string target, out string newName)
    {
        target = "";
        newName = "";

        foreach (var declaration in model.Declarations)
        {
            var name = declaration.Name;
            if (name.Length == 0 || !IsPlainIdentifier(name))
                continue;

            // Exactly one declaration of this name, and it is a user symbol (has property metadata or
            // is a parameter/binder) — not a builtin. A single declaration keeps the rename unambiguous.
            if (model.FindDeclarations(name).Count != 1)
                continue;

            var candidate = name + "Renamed";
            if (model.FindDeclarations(candidate).Count != 0 || model.FindResolutions(candidate).Count != 0)
                continue;

            target = name;
            newName = candidate;
            return true;
        }

        return false;
    }

    private static string? RenameOccurrences(string source, SemanticModel model, string target, string newName)
    {
        var edits = new List<(int Start, int EndExclusive)>();
        foreach (var resolution in model.IdentifierResolutions)
        {
            if (!string.Equals(resolution.Occurrence.Name, target, StringComparison.Ordinal))
                continue;

            var span = resolution.Occurrence.Span;
            if (span.StartLineNumber != span.EndLineNumber)
                return null;

            var start = EditorCursor.OffsetAtLineColumn(source, span.StartLineNumber, span.StartColumn);
            var endInclusive = EditorCursor.OffsetAtLineColumn(source, span.EndLineNumber, span.EndColumn);
            if (start < 0 || endInclusive < 0 || endInclusive < start || endInclusive >= source.Length)
                return null;
            if (!string.Equals(source[start..(endInclusive + 1)], target, StringComparison.Ordinal))
                return null;

            edits.Add((start, endInclusive + 1));
        }

        if (edits.Count == 0)
            return null;

        edits.Sort((a, b) => a.Start.CompareTo(b.Start));
        var builder = new StringBuilder(source.Length + (edits.Count * newName.Length));
        var cursor = 0;
        foreach (var (start, endExclusive) in edits)
        {
            if (start < cursor)
                return null;
            builder.Append(source, cursor, start - cursor);
            builder.Append(newName);
            cursor = endExclusive;
        }

        builder.Append(source, cursor, source.Length - cursor);
        return builder.ToString();
    }

    // ── Unrelated declaration ────────────────────────────────────────────────

    private static string? CheckUnrelatedDeclaration(EditorCase testCase, EditorExecutionMode mode)
    {
        var baseResult = EditorModel.Run(testCase.Source, mode);
        if (HasErrors(baseResult) || baseResult.Model is not { } model)
            return "unrelated-requires-a-clean-model";

        const string freshName = "Zzq9";
        if (testCase.Source.Contains(freshName, StringComparison.Ordinal))
            return "fresh-name-already-present";

        var extended = testCase.Source + "\n" + freshName + " = 1";
        var extendedResult = EditorModel.Run(extended, mode);
        if (HasErrors(extendedResult) || extendedResult.Model is not { } extendedModel)
            return "extended-source-does-not-reparse-cleanly";

        // Every original structural tuple survives unchanged; the only new tuples mention the fresh name.
        var before = ShapeLines(model, Identity, Identity);
        var after = ShapeLines(extendedModel, Identity, Identity)
            .Where(line => !line.Contains(freshName, StringComparison.Ordinal))
            .ToList();

        if (!before.SequenceEqual(after))
            throw new EditorInvariantException(
                $"{UnrelatedDeclaration}: appending an unrelated '{freshName}' declaration changed the resolution of " +
                "existing symbols.\n  before: " + string.Join(" ; ", before) + "\n  after:  " + string.Join(" ; ", after));

        return null;
    }

    // ── Dotted / ordinary ────────────────────────────────────────────────────

    private static string? CheckDottedOrdinary(EditorCase testCase, EditorToolingResult baseResult)
    {
        if (!EditorTables.TemplateOf(testCase.Parameters.Template).DottedOrdinaryPair)
            return "template-has-no-dotted-ordinary-pair";
        if (HasErrors(baseResult) || baseResult.Model is not { } model)
            return "dotted-ordinary-requires-a-clean-model";

        var ordinary = model.IdentifierResolutions.FirstOrDefault(resolution =>
            resolution.Occurrence.Name == "MmF" && resolution.Occurrence.Kind == OccurrenceKind.ResolveReference);
        var dotted = model.IdentifierResolutions.FirstOrDefault(resolution =>
            resolution.Occurrence.Name == "MmF" && resolution.Occurrence.Kind == OccurrenceKind.DotMemberReference);

        if (ordinary is null || dotted is null)
            return "dotted-ordinary-forms-not-both-present";

        if (ordinary.ResolvedDeclaration is not { } ordinaryDeclaration || dotted.ResolvedDeclaration is not { } dottedDeclaration)
            throw new EditorInvariantException(
                $"{DottedOrdinary}: the ordinary and dotted spellings of 'MmF' do not both resolve to a declaration.");

        if (ordinaryDeclaration != dottedDeclaration)
            throw new EditorInvariantException(
                $"{DottedOrdinary}: ordinary 'MmF(...)' resolves to {SourceSpanValidator.Describe(ordinaryDeclaration.Span)} " +
                $"but dotted '.MmF(...)' resolves to {SourceSpanValidator.Describe(dottedDeclaration.Span)}: the same callable " +
                "resolves to two different declarations depending on call syntax.");

        return null;
    }

    // ── Shared shape comparison ──────────────────────────────────────────────

    private static string Identity(string name) => name;

    private static void RequireSameShape(
        string relation, SemanticModel left, SemanticModel right, Func<string, string> mapLeft, Func<string, string> mapRight)
    {
        var leftLines = ShapeLines(left, mapLeft, mapLeft);
        var rightLines = ShapeLines(right, mapRight, mapRight);
        if (!leftLines.SequenceEqual(rightLines))
            throw new EditorInvariantException(
                $"{relation}: the two forms produced different resolution structure.\n" +
                "  left:  " + string.Join(" ; ", leftLines) + "\n" +
                "  right: " + string.Join(" ; ", rightLines));
    }

    private static List<string> ShapeLines(SemanticModel model, Func<string, string> mapName, Func<string, string> mapResolved)
    {
        var lines = new List<string>(model.IdentifierResolutions.Count);
        foreach (var resolution in model.IdentifierResolutions)
        {
            var name = mapName(resolution.Occurrence.Name);
            var resolved = resolution.ResolvedDeclaration is { } declaration ? mapResolved(declaration.Name) : "-";
            lines.Add($"{resolution.Occurrence.Kind}|{resolution.Classification}|{name}|{resolved}");
        }

        lines.Sort(StringComparer.Ordinal);
        return lines;
    }

    private static bool HasErrors(EditorToolingResult result)
        => result.Outcome != EditorToolingOutcome.Built
           || result.Diagnostics.Any(diagnostic => diagnostic.Severity == DiagnosticSeverity.Error);

    private static bool IsPlainIdentifier(string name)
    {
        foreach (var c in name)
            if (!char.IsAsciiLetterOrDigit(c) && c != '_')
                return false;
        return name.Length > 0 && !char.IsAsciiDigit(name[0]);
    }
}
