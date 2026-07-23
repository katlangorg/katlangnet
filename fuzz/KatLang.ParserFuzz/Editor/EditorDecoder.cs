namespace KatLang.ParserFuzz;

/// <summary>
/// Maps fuzzer bytes to a normalized <see cref="EditorParameters"/> point, and back.
///
/// <para>The bytes are NOT source text. The payload selects a trusted editor template, the code-unit
/// group and member to inject into its hole (reusing the Phase 5 UTF-16 code-unit tables so
/// ill-formed UTF-16 stays representable), a cursor placement strategy, and a bounded source edit.</para>
///
/// <para>PAYLOAD LAYOUT (frozen; a byte's meaning may never be re-used):</para>
/// <code>
///   0  template         index into EditorTables.Templates
///   1  surface          which editor-tooling surface is driven
///   2  injectionGroup   which UTF-16 code-unit group the hole insertion is drawn from
///   3  injectionMember  which member of that group
///   4  placement        how the injected units sit inside the hole
///   5  lineEndings      physical encoding of every line break
///   6  execution        elaborated front end vs raw syntax boundary
///   7  cursor           cursor placement strategy
///   8  cursorBias       secondary selector for the cursor strategy
///   9  edit             the edit to apply (None = no edit)
///  10  editGroup        code-unit group for the edit's inserted units
///  11  editMember       which member of that group
///  12  editBias         secondary selector for the edit
/// </code>
///
/// <para>Every field is taken modulo its table size, so every byte string decodes — including the
/// empty one, which reads every field as zero. There is no length-bearing tail: nothing a payload
/// selects grows with an encoded integer, and bytes past the fixed prefix are ignored, so a 1 MiB
/// input decodes exactly like its 13-byte prefix.</para>
/// </summary>
internal static class EditorDecoder
{
    /// <summary>Total bounded prefix of a payload. Campaign <c>-MaxLen</c> is set from this.</summary>
    public const int MaxPayloadPrefixBytes = 13;

    public static EditorParameters Decode(ReadOnlySpan<byte> payload)
    {
        var template = (EditorTemplateKind)(At(payload, 0) % EditorTables.TemplateCount);
        var surface = (EditorSurfaceKind)(At(payload, 1) % EditorTables.SurfaceCount);
        var injectionGroup = (Utf16CodeUnitGroup)(At(payload, 2) % EditorTables.GroupCount);
        var injectionMember = At(payload, 3) % Utf16Tables.MembersOf(injectionGroup).Length;
        var placement = (EditorInjectionPlacement)(At(payload, 4) % EditorTables.PlacementCount);
        var lineEndings = (EditorLineEndingMode)(At(payload, 5) % EditorTables.LineEndingCount);
        var execution = (EditorExecutionMode)(At(payload, 6) % EditorTables.ExecutionCount);
        var cursor = (EditorCursorKind)(At(payload, 7) % EditorTables.CursorCount);
        var cursorBias = At(payload, 8) % EditorTables.CursorBiasCount;
        var edit = (EditorEditKind)(At(payload, 9) % EditorTables.EditCount);
        var editGroup = (Utf16CodeUnitGroup)(At(payload, 10) % EditorTables.GroupCount);
        var editMember = At(payload, 11) % Utf16Tables.MembersOf(editGroup).Length;
        var editBias = At(payload, 12) % EditorTables.EditBiasCount;

        return Normalize(new EditorParameters(
            template, surface, injectionGroup, injectionMember, placement, lineEndings, execution,
            cursor, cursorBias, edit, editGroup, editMember, editBias));
    }

    /// <summary>
    /// Collapses every dimension the selected case ignores, so two payloads that describe the same
    /// case normalize to the same point (and therefore share one fingerprint). Idempotent by
    /// construction: it only ever writes fixed values into ignored fields.
    /// </summary>
    public static EditorParameters Normalize(EditorParameters parameters)
    {
        ArgumentNullException.ThrowIfNull(parameters);

        var injectionMember = Clamp(parameters.InjectionMember, Utf16Tables.MembersOf(parameters.InjectionGroup).Length);
        var cursorBias = Clamp(parameters.CursorBias, EditorTables.CursorBiasCount);

        // A no-op edit draws nothing from the edit tables.
        var edits = parameters.Edit == EditorEditKind.None;
        var editGroup = edits ? Utf16CodeUnitGroup.Basic : parameters.EditGroup;
        var editMember = edits ? 0 : Clamp(parameters.EditMember, Utf16Tables.MembersOf(parameters.EditGroup).Length);
        var editBias = edits ? 0 : Clamp(parameters.EditBias, EditorTables.EditBiasCount);

        return parameters with
        {
            InjectionMember = injectionMember,
            CursorBias = cursorBias,
            EditGroup = editGroup,
            EditMember = editMember,
            EditBias = editBias,
        };
    }

    /// <summary>The canonical payload for a normalized point. <c>Decode(Encode(p)) == p</c>.</summary>
    public static byte[] Encode(EditorParameters parameters)
    {
        ArgumentNullException.ThrowIfNull(parameters);
        var normalized = Normalize(parameters);

        return
        [
            (byte)(int)normalized.Template,
            (byte)(int)normalized.Surface,
            (byte)(int)normalized.InjectionGroup,
            (byte)normalized.InjectionMember,
            (byte)(int)normalized.Placement,
            (byte)(int)normalized.LineEndings,
            (byte)(int)normalized.ExecutionMode,
            (byte)(int)normalized.Cursor,
            (byte)normalized.CursorBias,
            (byte)(int)normalized.Edit,
            (byte)(int)normalized.EditGroup,
            (byte)normalized.EditMember,
            (byte)normalized.EditBias,
        ];
    }

    private static int At(ReadOnlySpan<byte> payload, int index)
        => index < payload.Length ? payload[index] : 0;

    private static int Clamp(int value, int count)
    {
        var m = value % count;
        return m < 0 ? m + count : m;
    }
}
