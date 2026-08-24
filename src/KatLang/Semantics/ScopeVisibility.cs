namespace KatLang.Semantics;

/// <summary>
/// One name visible at a source position — the editor-facing completion view of
/// KatLang's ownership-first lexical lookup. A visible symbol is a scope QUERY
/// result, not a source-backed identifier site: <see cref="Declaration"/> links
/// the declaration occurrence when one exists (module-elaborated declarations
/// carry spans from their own module source), and prelude/implicit-parameter
/// symbols have none.
/// </summary>
public sealed record VisibleSymbol
{
    public VisibleSymbol(
        string Name,
        IdentifierClassification Classification,
        DeclarationOccurrence? Declaration,
        PropertyInfo? Property,
        IReadOnlyList<VisibleSymbol>? Members = null)
    {
        this.Name = Name;
        this.Classification = Classification;
        this.Declaration = Declaration;
        this.Property = Property;
        this.Members = Members is null or { Count: 0 }
            ? Array.Empty<VisibleSymbol>()
            : Array.AsReadOnly(Members.ToArray());
    }

    public string Name { get; }

    public IdentifierClassification Classification { get; }

    public DeclarationOccurrence? Declaration { get; }

    public PropertyInfo? Property { get; }

    /// <summary>
    /// One-level structural dot-member surface: the exported properties of an
    /// algorithm-valued symbol, exactly the members ordinary structural dot
    /// access <c>Symbol.Member</c> can reach (exposure-filtered like the
    /// semantic model's dot-member resolution; public-vs-private is deliberately
    /// ignored, matching structural access). Member symbols never carry members
    /// of their own; descendants are deliberately not flattened into this surface.
    /// </summary>
    public IReadOnlyList<VisibleSymbol> Members { get; }
}

/// <summary>
/// The effective set of non-prelude names visible in one lexical scope region.
/// <see cref="Span"/> is the source hull of the scope's content (<see langword="null"/>
/// for the root scope, which covers the whole document). <see cref="Symbols"/> is
/// the RESOLVED visible set, ordered by name: shadowing, open dedup/ambiguity,
/// and direct-beats-open precedence are already applied, so each name appears at
/// most once and agrees with what identifier resolution selects for that name in
/// this scope. Prelude names are deliberately excluded — merge
/// <see cref="PreludeCatalog.Symbols"/> for names not shadowed here (or use
/// <see cref="SemanticModel.GetVisibleSymbolsAt"/>, which does the merge).
/// </summary>
public sealed record ScopeVisibility
{
    public ScopeVisibility(
        SourceSpan? Span,
        IReadOnlyList<VisibleSymbol> Symbols,
        int NestingDepth = 0)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(NestingDepth);
        this.Span = Span;
        this.Symbols = Symbols.Count == 0
            ? Array.Empty<VisibleSymbol>()
            : Array.AsReadOnly(Symbols.ToArray());
        this.NestingDepth = NestingDepth;
    }

    public SourceSpan? Span { get; }

    public IReadOnlyList<VisibleSymbol> Symbols { get; }

    /// <summary>
    /// Lexical nesting depth, with the document root at zero. Cursor lookup
    /// uses this before span-shape tie-breakers, so scopes with identical hulls
    /// never depend on traversal or collection order.
    /// </summary>
    public int NestingDepth { get; }
}

/// <summary>
/// The prelude's editor-facing symbol catalog: every ambient name KatLang
/// provides without a declaration in source. This is derived from the same
/// registry the semantic model resolves against, so editors need no hardcoded
/// builtin lists or signature tables.
/// </summary>
public static class PreludeCatalog
{
    /// <summary>
    /// All prelude names visible in every scope unless shadowed: the builtins
    /// (<c>if</c>, <c>while</c>, <c>map</c>, ...), <c>Math</c> (whose
    /// <see cref="VisibleSymbol.Members"/> carry the Math member signatures),
    /// <c>load</c>, and the lower-camel-case Math member aliases (<c>pi</c>,
    /// <c>sin</c>, ... — each carrying its canonical member's signature).
    /// Runtime-callable entries expose plain and dot signatures
    /// through <see cref="PropertyInfo.Signatures"/>; the front-end-only
    /// <c>load</c> entry exposes only its plain source form.
    /// </summary>
    public static IReadOnlyList<VisibleSymbol> Symbols { get; }
        = SemanticModelBuilder.CreatePreludeCatalogSymbols();

    /// <summary>
    /// Receiver-only value intrinsics (<c>.string</c>): valid only after a dot,
    /// never as bare names, so they are not part of <see cref="Symbols"/>.
    /// </summary>
    public static IReadOnlyList<VisibleSymbol> DotIntrinsicSymbols { get; }
        = SemanticModelBuilder.CreateDotIntrinsicCatalogSymbols();

    /// <summary>
    /// Reserved keyword spellings (<c>div</c>, <c>mod</c>, <c>and</c>, <c>or</c>,
    /// <c>xor</c>, <c>not</c>, <c>public</c>, <c>open</c>) — lexer-level words that
    /// are not identifiers and so never appear as visible symbols.
    /// </summary>
    public static IReadOnlyList<string> KeywordNames => Lexer.KeywordNames;
}
