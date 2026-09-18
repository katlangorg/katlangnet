namespace KatLang;

/// <summary>
/// The front end's half of the one-coordinate-space rule (Task 3a). A module spliced by
/// load elaboration enters a document's tree as its locationless IMPORT VIEW
/// (<see cref="Algorithm.User.IsModuleElaborated"/>; see <c>ModuleLoader.ToImportView</c>):
/// nothing inside it carries a source location, so a diagnostic a front-end pass raises
/// against imported content — a declaration collision, an undeclared identifier in a closed
/// list or branch, a refused open provider, an ineffective Grace marker, a parameter-owned
/// open head, a refused strict-value forwarding — has no position of its own. Its position is
/// the IMPORT SITE: the span, in the current document, of the edge through which the pass
/// reached the view — the <c>load('…')</c> / <c>open '…'</c> directive when the view sits in
/// expression position (<see cref="Expr.AlgorithmExpr"/>), or the declaring property's name
/// when load elaboration made the view a property's direct value (<c>M = load('…')</c>). A
/// view nested inside another view (a module the module imports) carries no site of its own
/// and inherits the enclosing one; a deferred region records the site its body was reached
/// under so demand-time elaboration starts from it. Every pass tracks the current site as
/// walk state and applies it exactly where a diagnostic's own span is absent — never in
/// place of a span the document wrote — so local diagnostics are positioned exactly as
/// before, and imported ones at the local demand instead of at a foreign coordinate or a
/// fabricated sentinel.
/// </summary>
internal static class ImportSite
{
    /// <summary>
    /// The import site a property edge introduces: the property's declaration span when its
    /// direct value is a spliced module root, otherwise null (the enclosing site stays).
    /// </summary>
    internal static SourceSpan? OfProperty(Property property)
        => property.Value is Algorithm.User { IsModuleElaborated: true } && property.DeclarationSpans.Count > 0
            ? property.DeclarationSpans[0]
            : null;

    /// <summary>
    /// The import site an expression edge introduces: the block's own span when it wraps a
    /// spliced module root, otherwise null (the enclosing site stays).
    /// </summary>
    internal static SourceSpan? OfBlock(Expr.AlgorithmExpr block)
        => block.Algorithm is Algorithm.User { IsModuleElaborated: true } ? block.Span : null;
}
