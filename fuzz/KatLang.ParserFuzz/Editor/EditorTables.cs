using System.Collections.Immutable;

namespace KatLang.ParserFuzz;

/// <summary>
/// One trusted editor source template. <see cref="Prefix"/> and <see cref="Suffix"/> are written
/// with <c>\n</c> for every line break; <see cref="EditorLineEndingMode"/> decides the physical
/// encoding. The fuzz-selected code units are inserted between them.
/// </summary>
/// <param name="Id">Stable identifier used in seeds, fingerprints and reports.</param>
/// <param name="Prefix">Source text before the insertion hole.</param>
/// <param name="Suffix">Source text after the insertion hole.</param>
/// <param name="ClosedWhenBenign">
/// True when a benign (identifier-like) insertion yields a complete, diagnostic-free program — the
/// precondition hint for the trailing-newline and whitespace-neutrality relations. The relations
/// re-check the ACTUAL built source before asserting, so this is only a filter.
/// </param>
/// <param name="DottedOrdinaryPair">
/// True when the template contains BOTH an ordinary call <c>F(A, ...)</c> and the dotted spelling
/// <c>A.F(...)</c> of the same user callable, so the dotted/ordinary resolution relation can run.
/// </param>
/// <param name="ContainsLoad">
/// True when the template's fixed text contains a <c>load(...)</c> directive, so building a semantic
/// model from it must go through the documented unresolved-load DECLINE path, never a throw.
/// </param>
internal sealed record EditorTemplate(
    string Id,
    string Prefix,
    string Suffix,
    bool ClosedWhenBenign = false,
    bool DottedOrdinaryPair = false,
    bool ContainsLoad = false);

/// <summary>Where a fuzz-selected run of code units is inserted into a trusted editor template.</summary>
internal enum EditorTemplateKind
{
    Empty,
    WhitespaceOnly,
    CommentOnly,
    PropertyReference,
    IncompleteIdentifier,
    IdentifierSplit,
    IncompleteNumber,
    IncompleteString,
    UnterminatedString,
    PropertyName,
    FunctionName,
    ZeroArgProperty,
    FunctionCall,
    IncompleteCall,
    DottedCall,
    IncompleteDottedCall,
    DottedAfterSequence,
    DottedAfterList,
    Spread,
    PartialSpread,
    ListLiteral,
    SequenceLiteral,
    IncompleteList,
    IncompleteSequence,
    Assignment,
    Deconstruction,
    RestBinding,
    IncompleteRest,
    Callback,
    IncompleteCallback,
    ConditionalClause,
    ClauseFamily,
    MalformedClauseFamily,
    NestedScope,
    NameShadowing,
    DuplicateDeclaration,
    BuiltinCall,
    ExtensionBuiltinCall,
    DottedOrdinaryPair,
    OpenDeclaration,
    ErrorBeforeCursor,
    ErrorAfterCursor,
    LoadImport,
    RawStandalone,
}

/// <summary>
/// FROZEN tables for the editor target. A payload byte selects an entry by index, so reordering or
/// removing an entry changes what every existing seed and corpus unit MEANS. Append only.
///
/// <para>Every template is a small, reviewable program with ONE insertion site and — wherever
/// possible — real named declarations and references around the hole, so the semantic model has
/// something to resolve even when the hole receives difficult code units. The goal is not valid
/// programs: an incomplete or malformed program is a primary editor-tooling use case, and a
/// structured "no result" is a good outcome.</para>
/// </summary>
internal static class EditorTables
{
    public static readonly ImmutableArray<EditorTemplate> Templates =
    [
        new(EditorTemplateIds.Empty, "", ""),
        new(EditorTemplateIds.WhitespaceOnly, "  ", "  "),
        new(EditorTemplateIds.CommentOnly, "// ", ""),
        new(EditorTemplateIds.PropertyReference, "Alpha = 1\nBeta = ", "\nOutput = Alpha + Beta", ClosedWhenBenign: true),
        new(EditorTemplateIds.IncompleteIdentifier, "Output = Al", ""),
        new(EditorTemplateIds.IdentifierSplit, "Value = 1\nOutput = Va", "lue", ClosedWhenBenign: true),
        new(EditorTemplateIds.IncompleteNumber, "Output = 12", ""),
        new(EditorTemplateIds.IncompleteString, "Output = 'ab", ""),
        new(EditorTemplateIds.UnterminatedString, "Msg = 'hello", "\nOutput = Msg"),
        new(EditorTemplateIds.PropertyName, "", " = 42\nOutput = 1"),
        new(EditorTemplateIds.FunctionName, "", "(x) = x + 1\nOutput = 1"),
        new(EditorTemplateIds.ZeroArgProperty, "Value = 10\nAlias = Value\nOutput = ", "Alias", ClosedWhenBenign: true),
        new(EditorTemplateIds.FunctionCall, "Add(a, b) = a + b\nOutput = Add(1, ", "2)", ClosedWhenBenign: true),
        new(EditorTemplateIds.IncompleteCall, "Add(a, b) = a + b\nOutput = Add(1, ", ""),
        new(EditorTemplateIds.DottedCall, "Data = (1, 2, 3)\nOutput = Data.", "count", ClosedWhenBenign: true),
        new(EditorTemplateIds.IncompleteDottedCall, "Data = (1, 2, 3)\nOutput = Data.", ""),
        new(EditorTemplateIds.DottedAfterSequence, "Output = (1, 2, 3).", "count", ClosedWhenBenign: true),
        new(EditorTemplateIds.DottedAfterList, "Output = [1, 2, 3].", "count", ClosedWhenBenign: true),
        new(EditorTemplateIds.Spread, "Data = (1, 2)\nMore = (Data..., ", "3)\nOutput = More", ClosedWhenBenign: true),
        new(EditorTemplateIds.PartialSpread, "Data = (1, 2)\nOutput = Data..", ""),
        new(EditorTemplateIds.ListLiteral, "Output = [1, ", "2, 3]", ClosedWhenBenign: true),
        new(EditorTemplateIds.SequenceLiteral, "Output = (1, ", "2, 3)", ClosedWhenBenign: true),
        new(EditorTemplateIds.IncompleteList, "Output = [1, 2, ", ""),
        new(EditorTemplateIds.IncompleteSequence, "Output = (1, 2, ", ""),
        new(EditorTemplateIds.Assignment, "Total = ", "\nOutput = Total", ClosedWhenBenign: true),
        new(EditorTemplateIds.Deconstruction, "x, y, ", " = (1, 2, 3)\nOutput = x + y"),
        new(EditorTemplateIds.RestBinding, "First(head, ...rest", ") = head\nOutput = First(1, 2, 3)"),
        new(EditorTemplateIds.IncompleteRest, "First(head, ...", "\nOutput = 1"),
        new(EditorTemplateIds.Callback, "Double(x) = x * ", "\nData = [1, 2, 3]\nOutput = Data.map(Double)", ClosedWhenBenign: true),
        new(EditorTemplateIds.IncompleteCallback, "Data = [1, 2, 3]\nOutput = Data.map(", ""),
        new(EditorTemplateIds.ConditionalClause, "F(0) = 'zero'\nF(", ") = 'other'\nOutput = F(0)"),
        new(EditorTemplateIds.ClauseFamily, "Sign(0) = 0\nSign(n) = ", "\nOutput = Sign(5)", ClosedWhenBenign: true),
        new(EditorTemplateIds.MalformedClauseFamily, "G(1) = 1\nG(1) = ", "\nOutput = G(1)"),
        new(EditorTemplateIds.NestedScope, "inner = {\nx = 2\nOutput = x + ", "\n}\nOutput = inner", ClosedWhenBenign: true),
        new(EditorTemplateIds.NameShadowing, "x = 10\nF(x) = x + ", "\nOutput = F(1)", ClosedWhenBenign: true),
        new(EditorTemplateIds.DuplicateDeclaration, "Dup = 1\nDup = ", "\nOutput = Dup"),
        new(EditorTemplateIds.BuiltinCall, "Output = count((1, ", ", 3))", ClosedWhenBenign: true),
        new(EditorTemplateIds.ExtensionBuiltinCall, "Data = (1, 2, 3)\nOutput = Data.take(", ")", ClosedWhenBenign: true),
        new(EditorTemplateIds.DottedOrdinaryPair, "MmF(c, n) = c.take(n)\nData = (1, 2, 3)\nA = MmF(Data, 2)\nB = Data.MmF(", "2)\nOutput = A", ClosedWhenBenign: true, DottedOrdinaryPair: true),
        new(EditorTemplateIds.OpenDeclaration, "outer = {\npublic inner = 1\n}\nopen ", "outer\nOutput = inner"),
        new(EditorTemplateIds.ErrorBeforeCursor, "Output = 1 @ ", "2\nX = 3"),
        new(EditorTemplateIds.ErrorAfterCursor, "X = ", "\nOutput = 1 @ 2"),
        new(EditorTemplateIds.LoadImport, "Data = load('", "lib')\nOutput = Data", ContainsLoad: true),
        new(EditorTemplateIds.RawStandalone, "Output = ", ""),
    ];

    public static EditorTemplate TemplateOf(EditorTemplateKind kind) => Templates[(int)kind];

    /// <summary>ASCII letters a letter-adjacency placement uses, so a decoration never adds a
    /// character the template did not expect.</summary>
    public static readonly ImmutableArray<ushort> FillerLetters = [0x0061, 0x0042, 0x005F, 0x0079];

    /// <summary>Distinct-per-cursor-strategy secondary selectors.</summary>
    public const int CursorBiasCount = 4;

    /// <summary>Distinct-per-edit secondary selectors.</summary>
    public const int EditBiasCount = 4;

    /// <summary>
    /// Hard cap on the code units of a generated source. Enforced by construction; the readiness
    /// tests assert the whole stratified space (base and edited) stays well under it.
    /// </summary>
    public const int MaxSourceCodeUnits = 1024;

    public static int TemplateCount => Templates.Length;
    public static int SurfaceCount => Enum.GetValues<EditorSurfaceKind>().Length;
    public static int PlacementCount => Enum.GetValues<EditorInjectionPlacement>().Length;
    public static int LineEndingCount => Enum.GetValues<EditorLineEndingMode>().Length;
    public static int ExecutionCount => Enum.GetValues<EditorExecutionMode>().Length;
    public static int CursorCount => Enum.GetValues<EditorCursorKind>().Length;
    public static int EditCount => Enum.GetValues<EditorEditKind>().Length;
    public static int GroupCount => Enum.GetValues<Utf16CodeUnitGroup>().Length;
}

/// <summary>Stable template identifiers. Separate from the enum so seeds read as text.</summary>
internal static class EditorTemplateIds
{
    public const string Empty = "empty";
    public const string WhitespaceOnly = "whitespace-only";
    public const string CommentOnly = "comment-only";
    public const string PropertyReference = "property-reference";
    public const string IncompleteIdentifier = "incomplete-identifier";
    public const string IdentifierSplit = "identifier-split";
    public const string IncompleteNumber = "incomplete-number";
    public const string IncompleteString = "incomplete-string";
    public const string UnterminatedString = "unterminated-string";
    public const string PropertyName = "property-name";
    public const string FunctionName = "function-name";
    public const string ZeroArgProperty = "zero-arg-property";
    public const string FunctionCall = "function-call";
    public const string IncompleteCall = "incomplete-call";
    public const string DottedCall = "dotted-call";
    public const string IncompleteDottedCall = "incomplete-dotted-call";
    public const string DottedAfterSequence = "dotted-after-sequence";
    public const string DottedAfterList = "dotted-after-list";
    public const string Spread = "spread";
    public const string PartialSpread = "partial-spread";
    public const string ListLiteral = "list-literal";
    public const string SequenceLiteral = "sequence-literal";
    public const string IncompleteList = "incomplete-list";
    public const string IncompleteSequence = "incomplete-sequence";
    public const string Assignment = "assignment";
    public const string Deconstruction = "deconstruction";
    public const string RestBinding = "rest-binding";
    public const string IncompleteRest = "incomplete-rest";
    public const string Callback = "callback";
    public const string IncompleteCallback = "incomplete-callback";
    public const string ConditionalClause = "conditional-clause";
    public const string ClauseFamily = "clause-family";
    public const string MalformedClauseFamily = "malformed-clause-family";
    public const string NestedScope = "nested-scope";
    public const string NameShadowing = "name-shadowing";
    public const string DuplicateDeclaration = "duplicate-declaration";
    public const string BuiltinCall = "builtin-call";
    public const string ExtensionBuiltinCall = "extension-builtin-call";
    public const string DottedOrdinaryPair = "dotted-ordinary-pair";
    public const string OpenDeclaration = "open-declaration";
    public const string ErrorBeforeCursor = "error-before-cursor";
    public const string ErrorAfterCursor = "error-after-cursor";
    public const string LoadImport = "load-import";
    public const string RawStandalone = "raw-standalone";
}
