namespace KatLang.Semantics;

/// <summary>
/// One name visible at a source position — the editor-facing completion view of
/// KatLang's ownership-first lexical lookup. A visible symbol is a scope QUERY
/// result, not a source-backed identifier site: <see cref="Declaration"/> links
/// the document's declaration occurrence when one exists; prelude and
/// implicit-parameter symbols have none, and neither does a symbol supplied by
/// a load-elaborated module (its declaration lies in the module's own source
/// text, so it is locationless with respect to the current document while
/// <see cref="Property"/> still carries its callable metadata). Within one
/// <see cref="SemanticModel"/>, a symbol visible from several scopes is ONE instance
/// shared by all of them; distinct declarations of one spelling are distinct symbols.
/// </summary>
/// <remarks>
/// Sharing is local to one model. Generated record equality compares the public payload,
/// including the identity of <see cref="Members"/>; it is not a declaration-identity test.
/// Reusing a symbol also reuses its immutable members list, so member-bearing symbols seen
/// in several scopes compare equal. A host needing declaration identity should use the
/// model's canonical <see cref="Declaration"/> instance when one exists.
/// </remarks>
public sealed record VisibleSymbol
{
    public VisibleSymbol(
        string Name,
        IdentifierClassification Classification,
        DeclarationOccurrence? Declaration,
        PropertyInfo? Property,
        IReadOnlyList<VisibleSymbol>? Members = null)
        : this(Name, Classification, Declaration, Property, Members, shareMembers: false)
    {
    }

    // Model-owned member lists are already immutable snapshots. Keep a distinct public
    // wrapper for this symbol (record equality includes it), sharing only their backing.
    internal static VisibleSymbol FromModelMembers(
        string name, IdentifierClassification classification, DeclarationOccurrence? declaration,
        PropertyInfo? property, IReadOnlyList<VisibleSymbol> members)
        => new(name, classification, declaration, property, members, shareMembers: true);

    private VisibleSymbol(
        string name, IdentifierClassification classification, DeclarationOccurrence? declaration,
        PropertyInfo? property, IReadOnlyList<VisibleSymbol>? members, bool shareMembers)
    {
        Name = name;
        Classification = classification;
        Declaration = declaration;
        Property = property;
        Members = members is null or { Count: 0 }
            ? Array.Empty<VisibleSymbol>()
            : shareMembers
                ? new System.Collections.ObjectModel.ReadOnlyCollection<VisibleSymbol>((IList<VisibleSymbol>)members)
                : Array.AsReadOnly(members.ToArray());
    }

    public string Name { get; }

    public IdentifierClassification Classification { get; }

    public DeclarationOccurrence? Declaration { get; }

    public PropertyInfo? Property { get; }

    /// <summary>
    /// One-level structural dot-member surface: the DECLARED properties of an
    /// algorithm-valued symbol, exactly the members ordinary structural dot
    /// access <c>Symbol.Member</c> selects (selection never depends on exposure —
    /// K1-08 — and public-vs-private is deliberately ignored, matching structural
    /// access; accessibility of a local-only member is decided at the access, so it
    /// is listed here). Member symbols never carry members
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
/// <remarks>
/// A visible set is a semantic VIEW, not a snapshot the model copies per scope: scopes of one
/// model built by <see cref="SemanticModelBuilder"/> may share immutable backing storage, and
/// the same <see cref="VisibleSymbol"/> instance may appear in several scopes. Each scope still
/// exposes its own read-only <see cref="Symbols"/> list, whose contents and order are exactly
/// the scope's; enumerating every symbol of every scope remains proportional to that logical
/// output.
/// </remarks>
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

    /// <summary>
    /// A builder scope over its shared immutable visibility view (FE-4b): no symbol is copied.
    /// The public list is a distinct wrapper per scope, so storage sharing never makes two scopes'
    /// <see cref="Symbols"/> the same object (record equality stays per scope). An empty scope keeps
    /// the shared empty array and no view, exactly like a host-constructed empty scope.
    /// </summary>
    internal ScopeVisibility(SourceSpan? span, ScopeSymbolView view, int nestingDepth)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(nestingDepth);
        Span = span;
        if (view.Count == 0)
        {
            Symbols = Array.Empty<VisibleSymbol>();
        }
        else
        {
            Symbols = new System.Collections.ObjectModel.ReadOnlyCollection<VisibleSymbol>(view);
            View = view;
        }

        NestingDepth = nestingDepth;
    }

    public SourceSpan? Span { get; }

    public IReadOnlyList<VisibleSymbol> Symbols { get; }

    /// <summary>
    /// The shared view behind <see cref="Symbols"/> for a non-empty builder scope (name lookup
    /// without copying); null for host-constructed and empty scopes.
    /// </summary>
    internal ScopeSymbolView? View { get; }

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
