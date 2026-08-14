namespace KatLang;

/// <summary>
/// One structured violation of the elaborated DotCall contract.
/// </summary>
internal sealed record DotCallElaborationViolation(Expr Expression, string Description);

/// <summary>
/// The POST-ELABORATION DotCall contract, stated once for both the C# and the
/// Lean model (Lean: the <c>dotMember</c> arm of <c>postElabInvariant</c>):
///
/// <para>In every source-derived elaborated tree, including diagnostic
/// recovery trees:</para>
/// <list type="number">
/// <item>no <see cref="Expr.Grace"/> survives — parameter detection consumes
/// every written ordering annotation;</item>
/// <item>every <see cref="Expr.DotCall"/>'s
/// <see cref="Expr.DotCall.LexicalFallback"/> is NON-NULL — <c>null</c>
/// is exclusively a raw/host-built construction shorthand for
/// <c>Resolve(Name)</c> and never a post-elaboration semantic state;</item>
/// <item>the fallback is exactly <see cref="Expr.Resolve"/> or
/// <see cref="Expr.Param"/>;</item>
/// <item>the fallback's identifier equals <see cref="Expr.DotCall.Name"/> —
/// the structural identity and the lexical callable identity name the same
/// written member.</item>
/// </list>
///
/// <para>Grace composed with dot syntax (<c>a~.f</c> / <c>a.~f</c>) leaves NO
/// trace here: the parser builds the SAME ordinary <see cref="Expr.DotCall"/>
/// as <c>a.f</c>, carrying temporary Grace on the receiver occurrence in the
/// former and on the fallback occurrence in the latter. Parameter detection
/// consumes either annotation. An elaborated graced source is
/// therefore structurally indistinguishable from its ungraced twin except for
/// any enclosing parameter-order effect produced by the ordinary Grace law.
/// Rule 1 enforces
/// that no ordering annotation itself survives elaboration.</para>
///
/// <para>Enforcement follows the repository's guarded-by-tests pattern for
/// producer invariants (like the parser's sequence-construct containment):
/// the front end upholds the contract by construction — the parser stores
/// <c>Resolve(Name)</c> (temporarily wrapped in Grace for <c>.~name</c>) and
/// <see cref="ParameterDetector"/> owns the
/// <c>null → Resolve(Name)</c> normalization and the Param rewrite — and
/// <c>DotCallFallbackInvariantTests</c> sweeps representative corpora through
/// this checker, and the parser fuzz harness applies it to every elaboration.
/// It deliberately does NOT run inside the production pipeline:
/// a violation is a defect in an elaboration pass, not a user-facing
/// diagnostic, and host-built raw trees are intentionally allowed to omit the
/// fallback (checked only through <see cref="CheckElaborated"/> when a caller
/// asserts elaborated provenance).</para>
/// </summary>
internal static class DotCallElaborationInvariant
{
    /// <summary>
    /// Walks an elaborated tree and returns the first DotCall contract
    /// violation, or null when the tree satisfies the contract. Callers must
    /// only pass trees they claim have completed front-end elaboration. Raw
    /// and host-built trees may still contain Grace or null fallback shorthand.
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

            if (expr is Expr.Grace)
            {
                Violation = new DotCallElaborationViolation(
                    expr,
                    "Grace remains after elaboration (parameter detection must consume every ordering annotation)");
                return;
            }

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
        }
    }
}
