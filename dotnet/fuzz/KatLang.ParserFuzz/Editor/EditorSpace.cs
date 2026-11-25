using System.Collections.Immutable;

namespace KatLang.ParserFuzz;

/// <summary>
/// A deterministic stratified walk of the editor parameter space. Each stratum crosses ONE pair of
/// dimensions exhaustively while pinning the rest, so every template, surface, cursor kind, edit
/// kind, execution mode, line-ending mode, injection group member and placement is reached by
/// construction — and the whole walk is the same list on every machine and in every process.
/// Normalization deduplicates points a stratum would otherwise repeat.
/// </summary>
internal static class EditorSpace
{
    private static readonly ImmutableArray<EditorTemplateKind> RepresentativeTemplates =
    [
        EditorTemplateKind.PropertyReference,
        EditorTemplateKind.DottedCall,
        EditorTemplateKind.ListLiteral,
        EditorTemplateKind.Deconstruction,
        EditorTemplateKind.ConditionalClause,
        EditorTemplateKind.NestedScope,
        EditorTemplateKind.IncompleteCall,
        EditorTemplateKind.DottedOrdinaryPair,
    ];

    public static IEnumerable<EditorParameters> EnumerateStratified()
    {
        var seen = new HashSet<EditorParameters>();

        // 1. Every template crossed with every surface.
        foreach (var template in AllTemplates())
        foreach (var surface in All<EditorSurfaceKind>())
        {
            var point = Point(template, surface: surface);
            if (seen.Add(point)) yield return point;
        }

        // 2. Every template crossed with every cursor kind.
        foreach (var template in AllTemplates())
        foreach (var cursor in All<EditorCursorKind>())
        {
            var point = Point(template, cursor: cursor);
            if (seen.Add(point)) yield return point;
        }

        // 3. Every template crossed with every edit kind.
        foreach (var template in AllTemplates())
        foreach (var edit in All<EditorEditKind>())
        {
            var point = Point(template, edit: edit);
            if (seen.Add(point)) yield return point;
        }

        // 4. Every template crossed with every execution mode and every line-ending mode.
        foreach (var template in AllTemplates())
        foreach (var execution in All<EditorExecutionMode>())
        {
            var point = Point(template, execution: execution);
            if (seen.Add(point)) yield return point;
        }

        foreach (var template in AllTemplates())
        foreach (var lineEndings in All<EditorLineEndingMode>())
        {
            var point = Point(template, lineEndings: lineEndings);
            if (seen.Add(point)) yield return point;
        }

        // 5. Every injection group member and every placement, at every representative template.
        foreach (var template in RepresentativeTemplates)
        foreach (var group in All<Utf16CodeUnitGroup>())
        for (var member = 0; member < Utf16Tables.MembersOf(group).Length; member++)
        {
            var point = Point(template, injectionGroup: group, injectionMember: member);
            if (seen.Add(point)) yield return point;
        }

        foreach (var template in RepresentativeTemplates)
        foreach (var placement in All<EditorInjectionPlacement>())
        {
            var point = Point(template, placement: placement);
            if (seen.Add(point)) yield return point;
        }

        // 6. The surrogate and whitespace groups crossed with every cursor kind — the interaction
        //    the cursor model most needs to survive.
        foreach (var group in new[] { Utf16CodeUnitGroup.Surrogates, Utf16CodeUnitGroup.Whitespace })
        for (var member = 0; member < Utf16Tables.MembersOf(group).Length; member++)
        foreach (var cursor in All<EditorCursorKind>())
        {
            var point = Point(EditorTemplateKind.PropertyReference, injectionGroup: group, injectionMember: member, cursor: cursor);
            if (seen.Add(point)) yield return point;
        }

        // 7. Every edit kind crossed with every edit-injection group, at representative templates.
        foreach (var template in RepresentativeTemplates)
        foreach (var edit in All<EditorEditKind>())
        foreach (var group in All<Utf16CodeUnitGroup>())
        {
            var point = Point(template, edit: edit, editGroup: group, editMember: 0);
            if (seen.Add(point)) yield return point;
        }

        // 8. Cursor bias and edit bias, where the strategies actually read them.
        foreach (var template in RepresentativeTemplates)
        for (var cursorBias = 0; cursorBias < EditorTables.CursorBiasCount; cursorBias++)
        {
            var point = Point(template, cursor: EditorCursorKind.InsideFirstIdentifier, cursorBias: cursorBias);
            if (seen.Add(point)) yield return point;
        }
    }

    /// <summary>Canonical payloads for the whole stratified walk — what the seed export and the
    /// determinism tests feed through the real decoder.</summary>
    public static IEnumerable<byte[]> EnumerateStratifiedPayloads()
        => EnumerateStratified().Select(EditorDecoder.Encode);

    private static IEnumerable<EditorTemplateKind> AllTemplates()
        => Enumerable.Range(0, EditorTables.TemplateCount).Select(i => (EditorTemplateKind)i);

    private static IEnumerable<T> All<T>() where T : struct, Enum => Enum.GetValues<T>();

    private static EditorParameters Point(
        EditorTemplateKind template,
        EditorSurfaceKind surface = EditorSurfaceKind.Classification,
        Utf16CodeUnitGroup injectionGroup = Utf16CodeUnitGroup.Basic,
        int injectionMember = 0,
        EditorInjectionPlacement placement = EditorInjectionPlacement.Alone,
        EditorLineEndingMode lineEndings = EditorLineEndingMode.Lf,
        EditorExecutionMode execution = EditorExecutionMode.Elaborated,
        EditorCursorKind cursor = EditorCursorKind.StartOfFile,
        int cursorBias = 0,
        EditorEditKind edit = EditorEditKind.None,
        Utf16CodeUnitGroup editGroup = Utf16CodeUnitGroup.Basic,
        int editMember = 0,
        int editBias = 0)
        => EditorDecoder.Normalize(new EditorParameters(
            template, surface, injectionGroup, injectionMember, placement, lineEndings, execution,
            cursor, cursorBias, edit, editGroup, editMember, editBias));
}
