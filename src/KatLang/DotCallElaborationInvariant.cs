namespace KatLang;

/// <summary>
/// One structured violation of the elaborated dot-edge contract.
/// </summary>
internal sealed record DotCallElaborationViolation(Expr.DotCall DotCall, string Description);

/// <summary>
/// The POST-ELABORATION dot-edge contract, stated once for both the C# and the
/// Lean model (Lean: the <c>dotMember</c> arm of <c>postElabInvariant</c>):
///
/// <para>For every <see cref="Expr.DotCall"/> in a diagnostic-free
/// source-derived elaborated tree:</para>
/// <list type="number">
/// <item><see cref="Expr.DotCall.LexicalFallback"/> is NON-NULL — <c>null</c>
/// is exclusively a raw/host-built construction shorthand for
/// <c>Resolve(Name)</c> and never a post-elaboration semantic state;</item>
/// <item>the fallback is exactly <see cref="Expr.Resolve"/> or
/// <see cref="Expr.Param"/>;</item>
/// <item>the fallback's identifier equals <see cref="Expr.DotCall.Name"/> —
/// the structural identity and the lexical callable identity name the same
/// written member;</item>
/// <item><see cref="Expr.DotCall.ExtensionMarkerSpan"/> agrees with the
/// resolution mode: present exactly on
/// <see cref="DotResolutionMode.ExtensionOnly"/> edges (the parser's
/// provenance contract for source-backed nodes).</item>
/// </list>
///
/// <para>Enforcement follows the repository's guarded-by-tests pattern for
/// producer invariants (like the parser's sequence-construct containment):
/// the front end upholds the contract by construction — the parser always
/// stores <c>Resolve(Name)</c> and <see cref="ParameterDetector"/> owns the
/// <c>null → Resolve(Name)</c> normalization and the Param rewrite — and
/// <c>DotCallFallbackInvariantTests</c> sweeps representative corpora through
/// this checker. It deliberately does NOT run inside the production pipeline:
/// a violation is a defect in an elaboration pass, not a user-facing
/// diagnostic, and host-built raw trees are intentionally allowed to omit the
/// fallback (checked only through <see cref="CheckElaborated"/> when a caller
/// asserts elaborated provenance).</para>
/// </summary>
internal static class DotCallElaborationInvariant
{
    /// <summary>
    /// Walks an elaborated tree and returns the first dot-edge contract
    /// violation, or null when the tree satisfies the contract. Callers must
    /// only pass trees they claim are diagnostic-free source elaborations
    /// (recovery trees are exempt from valid-source invariants by repository
    /// policy).
    /// </summary>
    internal static DotCallElaborationViolation? CheckElaborated(Algorithm root)
    {
        var walker = new InvariantWalker();
        walker.VisitAlgorithm(root);
        return walker.Violation;
    }

    private sealed class InvariantWalker : AstWalker
    {
        public DotCallElaborationViolation? Violation { get; private set; }

        public override void VisitExpr(Expr expr)
        {
            if (Violation is not null)
                return;

            if (expr is Expr.DotCall dotCall)
                CheckDotCall(dotCall);

            base.VisitExpr(expr);
        }

        private void CheckDotCall(Expr.DotCall dotCall)
        {
            if (dotCall.LexicalFallback is null)
            {
                Violation = new DotCallElaborationViolation(
                    dotCall,
                    "LexicalFallback is null after elaboration (null is only a raw/host construction shorthand)");
                return;
            }

            switch (dotCall.LexicalFallback)
            {
                case Expr.Resolve(var resolveName):
                    if (!string.Equals(resolveName, dotCall.Name, StringComparison.Ordinal))
                        Violation = new DotCallElaborationViolation(
                            dotCall,
                            $"Resolve fallback identifier '{resolveName}' does not match member name '{dotCall.Name}'");
                    break;

                case Expr.Param(var paramName):
                    if (!string.Equals(paramName, dotCall.Name, StringComparison.Ordinal))
                        Violation = new DotCallElaborationViolation(
                            dotCall,
                            $"Param fallback identifier '{paramName}' does not match member name '{dotCall.Name}'");
                    break;

                default:
                    Violation = new DotCallElaborationViolation(
                        dotCall,
                        $"LexicalFallback must be Resolve or Param, found {dotCall.LexicalFallback.GetType().Name}");
                    return;
            }

            if (Violation is not null)
                return;

            if (!Enum.IsDefined(dotCall.ResolutionMode))
            {
                Violation = new DotCallElaborationViolation(
                    dotCall,
                    $"ResolutionMode has invalid value {(int)dotCall.ResolutionMode}");
                return;
            }

            var hasMarker = dotCall.ExtensionMarkerSpan is not null;
            var isExtension = dotCall.ResolutionMode == DotResolutionMode.ExtensionOnly;
            if (hasMarker != isExtension)
            {
                Violation = new DotCallElaborationViolation(
                    dotCall,
                    hasMarker
                        ? "ExtensionMarkerSpan is present on an Ordinary edge"
                        : "ExtensionOnly edge carries no ExtensionMarkerSpan");
            }
        }
    }
}
