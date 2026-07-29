using System.Collections.Immutable;
using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>
/// The editor-tooling surface a case exercises. Each value names ONE surface that actually exists
/// in <c>KatLang.Semantics</c> (there is no completion, no active-parameter signature help, and no
/// incremental parser in the repository, so none is named here — see <see cref="EditorTables"/>).
/// The whole semantic model is built and every core invariant is checked for every case; the
/// surface selects which surface-specific query is driven and which observation the fingerprint
/// records.
/// </summary>
internal enum EditorSurfaceKind
{
    /// <summary>Semantic classification of every identifier occurrence (<c>IdentifierResolutions</c>).</summary>
    Classification,

    /// <summary>Position → resolution at the cursor (<c>FindResolutionAt</c>) — the hover anchor.</summary>
    PositionResolution,

    /// <summary>Position → property/signature metadata at the cursor (<c>FindPropertyAt</c>).</summary>
    PropertyAtPosition,

    /// <summary>Symbol lookup by name (<c>FindResolutions</c>/<c>FindDeclarations</c>/<c>FindProperties</c>).</summary>
    SymbolLookup,

    /// <summary>Go-to-definition: the resolved declaration for the occurrence at the cursor.</summary>
    Definition,

    /// <summary>Document symbols / outline (<c>Declarations</c> + <c>PropertyInfos</c>).</summary>
    DocumentSymbols,

    /// <summary>Callable signature / parameter metadata (<c>PropertyInfo.Signatures</c>).</summary>
    Signature,
}

/// <summary>How far the source is processed before the semantic model is built.</summary>
internal enum EditorExecutionMode
{
    /// <summary>The realistic editor path: the elaborated front end via <c>Parser.Parse</c>, then
    /// <c>SemanticModelBuilder.Build(ParseResult)</c>.</summary>
    Elaborated,

    /// <summary>The raw syntax boundary via <c>Parser.ParseSyntax</c>, then
    /// <c>SemanticModelBuilder.Build(SyntaxParseResult)</c> — editor tooling over un-elaborated
    /// recovery syntax.</summary>
    RawSyntax,
}

/// <summary>How the fuzz-selected code units sit inside the template's insertion hole.</summary>
internal enum EditorInjectionPlacement
{
    Alone,
    AfterLetter,
    BeforeLetter,
    Surrounded,
    Doubled,
}

/// <summary>
/// Physical encoding of the template's line breaks. Templates are written with <c>\n</c>; this mode
/// rewrites each one. A <c>\r</c> a case's own injected units carry is never touched.
/// </summary>
internal enum EditorLineEndingMode
{
    Lf,
    Crlf,
    LoneCr,
    Mixed,
    NoTrailingNewline,
}

/// <summary>
/// Where the cursor lands, as a MEANINGFUL boundary derived from the built source rather than a raw
/// integer. Each strategy scans the source for its feature and falls back to a bias-derived clamped
/// offset when the feature is absent, so every case yields a deterministic cursor.
/// </summary>
internal enum EditorCursorKind
{
    StartOfFile,
    EndOfFile,
    BeforeFirstToken,
    InsideFirstIdentifier,
    AfterFirstIdentifier,
    BetweenIdentifierAndDot,
    AfterDot,
    AtSpreadMarker,
    InsideArgumentList,
    AfterComma,
    InsideString,
    InsideComment,
    InsideWhitespace,
    AtCarriageReturn,
    BetweenCarriageReturnAndLineFeed,
    AfterLineFeed,
    SurrogatePairBoundary,
    BeforeIsolatedSurrogate,
    AfterIsolatedSurrogate,
    InsideMalformedToken,
    InsideDiagnosticSpan,
    AtInjection,
    BeforeEndOfFile,

    /// <summary>A position one-or-more columns past the last line — an out-of-range request whose
    /// documented contract is a <c>null</c> resolution, never a clamp or a throw.</summary>
    PastEndOfFile,
}

/// <summary>
/// A bounded source edit applied to the exact code units. Every kind either transforms an existing
/// feature or inserts one of the case's own injected units; nothing reads an unbounded length.
/// </summary>
internal enum EditorEditKind
{
    None,
    Insert,
    Delete,
    Replace,
    Append,
    Prepend,
    SplitToken,
    JoinTokens,
    AddDot,
    RemoveDot,
    AddComma,
    RemoveComma,
    AddDelimiter,
    RemoveDelimiter,
    AddNewline,
    LineFeedToCarriageReturnLineFeed,
    CarriageReturnLineFeedToLineFeed,
    AddSpreadMarker,
    RemoveSpreadMarker,
    CompleteString,
    BreakString,
    RenameLocalSymbol,
    RenameToDuplicate,
}

/// <summary>
/// The decoded, normalized parameters of one editor case. Two payloads that normalize to equal
/// parameters describe the SAME case, which is what makes the fingerprint and the corpus meaningful.
/// </summary>
internal sealed record EditorParameters(
    EditorTemplateKind Template,
    EditorSurfaceKind Surface,
    Utf16CodeUnitGroup InjectionGroup,
    int InjectionMember,
    EditorInjectionPlacement Placement,
    EditorLineEndingMode LineEndings,
    EditorExecutionMode ExecutionMode,
    EditorCursorKind Cursor,
    int CursorBias,
    EditorEditKind Edit,
    Utf16CodeUnitGroup EditGroup,
    int EditMember,
    int EditBias)
{
    /// <summary>The canonical payload for this normalized point. <c>Decode(Encode()) == this</c>.</summary>
    public byte[] Encode() => EditorDecoder.Encode(this);
}

/// <summary>
/// One fully materialized editor case: the exact base source code units, the cursor as an exact
/// UTF-16 offset, and the exact edited source code units. <see cref="SourceCodeUnits"/> and
/// <see cref="EditedCodeUnits"/> are the authoritative artifacts — the <c>string</c> forms are the
/// same units and may be ill-formed UTF-16 by design.
/// </summary>
internal sealed record EditorCase(
    EditorParameters Parameters,
    ImmutableArray<ushort> SourceCodeUnits,
    string Source,
    int CursorOffset,
    ImmutableArray<ushort> EditedCodeUnits,
    string EditedSource,
    int EditedCursorOffset,
    bool EditApplied,
    string Description)
{
    /// <summary>Four-digit hex code units of the base source — the only lossless printable form.</summary>
    public string HexUnits => Utf16CodeUnits.ToHex(SourceCodeUnits);

    /// <summary>Four-digit hex code units of the edited source.</summary>
    public string EditedHexUnits => Utf16CodeUnits.ToHex(EditedCodeUnits);

    public string Num(int value) => value.ToString(CultureInfo.InvariantCulture);
}
