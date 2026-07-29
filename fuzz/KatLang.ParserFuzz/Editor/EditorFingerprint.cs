using System.Text;

namespace KatLang.ParserFuzz;

/// <summary>
/// A stable structural fingerprint of an editor case and its outcome.
///
/// <para>It carries NO source text, no wall-clock reading, no process or thread id, no object
/// address, and no runtime-randomized hash. Arbitrary source content is summarized through the fixed
/// code-unit CLASS buckets the UTF-16 layer already defines, so the same case fingerprints
/// identically in every process — which is what makes the corpus, the campaign distributions and the
/// replay comparison mean anything.</para>
/// </summary>
internal static class EditorFingerprint
{
    public static string Describe(EditorCase testCase, EditorObservation observation, EditorRelationOutcome relations)
    {
        ArgumentNullException.ThrowIfNull(testCase);
        ArgumentNullException.ThrowIfNull(observation);
        ArgumentNullException.ThrowIfNull(relations);

        var parameters = testCase.Parameters;
        var builder = new StringBuilder(512);

        Append(builder, "template", EditorTables.TemplateOf(parameters.Template).Id);
        Append(builder, "surface", parameters.Surface.ToString());
        Append(builder, "execution", parameters.ExecutionMode.ToString());
        Append(builder, "cursor", parameters.Cursor.ToString());
        Append(builder, "edit", parameters.Edit.ToString());
        Append(builder, "editApplied", testCase.EditApplied ? "yes" : "no");
        Append(builder, "placement", parameters.Placement.ToString());
        Append(builder, "lineEndings", parameters.LineEndings.ToString());
        Append(builder, "injection", $"{parameters.InjectionGroup.ToString().ToLowerInvariant()}/{Utf16Tables.MembersOf(parameters.InjectionGroup)[parameters.InjectionMember].Id}");
        Append(builder, "surrogates", Utf16CodeUnits.ClassifySurrogates(testCase.SourceCodeUnits).ToString());
        Append(builder, "classes", Utf16Fingerprint.ClassSetOf(testCase.SourceCodeUnits));
        Append(builder, "sourceLen", Utf16Fingerprint.Bucket(testCase.SourceCodeUnits.Length));
        Append(builder, "scope", ScopeClass(parameters.Template));
        Append(builder, "collection", CollectionClass(parameters.Template));
        Append(builder, "dottedOrdinary", EditorTables.TemplateOf(parameters.Template).DottedOrdinaryPair ? "pair" : "-");

        Append(builder, "outcome", observation.Outcome == EditorToolingOutcome.Built ? "model" : "declined-load");
        Append(builder, "parse", observation.DiagnosticCount == 0 ? "clean" : "diagnostics");
        Append(builder, "diagBucket", Utf16Fingerprint.Bucket(observation.DiagnosticCount));
        Append(builder, "diagFirst", observation.FirstDiagnosticBucket);
        Append(builder, "diagSpan", observation.AnyMultilineDiagnosticSpan ? "multiline" : "single-line");
        Append(builder, "occurrences", Utf16Fingerprint.Bucket(observation.OccurrenceCount));
        Append(builder, "declarations", Utf16Fingerprint.Bucket(observation.DeclarationCount));
        Append(builder, "resolutions", Utf16Fingerprint.Bucket(observation.ResolutionCount));
        Append(builder, "properties", Utf16Fingerprint.Bucket(observation.PropertyCount));
        Append(builder, "symbolKinds", observation.ClassificationsPresent);
        Append(builder, "cursorClass", observation.CursorResolutionClass);
        Append(builder, "cursorProperty", observation.CursorHasProperty ? "yes" : "no");
        Append(builder, "surfaceObs", observation.SurfaceObservation);
        Append(builder, "spanCheck", "ok");        // a failure throws; it never reaches here
        Append(builder, "determinism", "stable");   // ditto
        Append(builder, "relations", relations.Summary);

        return builder.ToString();
    }

    /// <summary>Scope shape a template exercises, so the fingerprint separates root, nested-block,
    /// clause, callback, and binding scopes.</summary>
    private static string ScopeClass(EditorTemplateKind template) => template switch
    {
        EditorTemplateKind.NestedScope => "nested-block",
        EditorTemplateKind.OpenDeclaration => "open",
        EditorTemplateKind.NameShadowing => "shadowing",
        EditorTemplateKind.DuplicateDeclaration or EditorTemplateKind.MalformedClauseFamily => "duplicate",
        EditorTemplateKind.ConditionalClause or EditorTemplateKind.ClauseFamily => "conditional",
        EditorTemplateKind.Callback or EditorTemplateKind.IncompleteCallback => "callback",
        EditorTemplateKind.Deconstruction => "deconstruction",
        EditorTemplateKind.CollectingBinding or EditorTemplateKind.IncompleteCollecting => "collecting",
        EditorTemplateKind.FunctionName or EditorTemplateKind.FunctionCall or EditorTemplateKind.IncompleteCall => "function",
        EditorTemplateKind.LoadImport => "module",
        _ => "root",
    };

    /// <summary>List / sequence / collecting-binding distinction a template exercises.</summary>
    private static string CollectionClass(EditorTemplateKind template) => template switch
    {
        EditorTemplateKind.ListLiteral or EditorTemplateKind.IncompleteList or EditorTemplateKind.DottedAfterList => "list",
        EditorTemplateKind.SequenceLiteral or EditorTemplateKind.IncompleteSequence or EditorTemplateKind.DottedAfterSequence => "sequence",
        EditorTemplateKind.Spread or EditorTemplateKind.SpreadAtEndOfFile => "spread",
        EditorTemplateKind.CollectingBinding or EditorTemplateKind.IncompleteCollecting => "collecting",
        EditorTemplateKind.Deconstruction => "deconstruction",
        _ => "none",
    };

    private static void Append(StringBuilder builder, string key, string value)
    {
        if (builder.Length > 0) builder.Append('|');
        builder.Append(key).Append('=').Append(value);
    }
}
