using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>Thrown when the raw parser violates a fuzzing invariant. Escapes to the
/// fuzzing engine (or the replay runner) as a recorded failure.</summary>
internal sealed class FuzzInvariantException(string message) : Exception(message);

/// <summary>
/// Post-parse invariants checked on every raw-parser fuzz input. These assert
/// robustness properties of the RAW parser output; they never assert that malformed
/// input is rejected — ordinary parser diagnostics are expected, not failures.
///
/// Invariants:
///   1. Diagnostic spans are well-formed and in-bounds for the source, matching the
///      lexer's exact line/column bookkeeping (see <see cref="SourceSpanValidator"/>).
///   2. The full AST (algorithms, properties, branches, patterns, expressions, nested
///      blocks) can be traversed to termination without assuming a valid program.
///   3. The surface parser never produces <see cref="Expr.SequenceConstruct"/>, an
///      internal-only sequence-join node with zero legal surface origin sites.
/// </summary>
internal static class FuzzInvariants
{
    public static void Check(string source, SyntaxParseResult result)
    {
        CheckDiagnosticSpans(source, result.Diagnostics);
        CheckAst(result.Root);
    }

    // ── Invariant 1: diagnostic spans ────────────────────────────────────────
    private static void CheckDiagnosticSpans(string source, IReadOnlyList<Diagnostic> diagnostics)
    {
        var lineWidths = SourceSpanValidator.LineWidths(source);
        foreach (var d in diagnostics)
        {
            if (d.Span is null)
                throw new FuzzInvariantException($"Diagnostic span is null: message='{d.Message}'");

            var reason = SourceSpanValidator.Validate(d.Span, lineWidths);
            if (reason is not null)
                throw new FuzzInvariantException(
                    $"Invalid diagnostic span [{reason}]: span={SourceSpanValidator.Describe(d.Span)} message='{d.Message}'");
        }
    }

    // ── Invariants 2 & 3: AST traversal + forbidden node ─────────────────────
    private static void CheckAst(Algorithm root)
        => new InvariantWalker().VisitAlgorithm(root);

    /// <summary>
    /// Reuses the shared <see cref="AstWalker"/> to recursively visit every
    /// algorithm, property, branch, pattern, expression and nested block without
    /// reflection and without assuming semantic validity. Visiting a
    /// <see cref="Expr.SequenceConstruct"/> is an immediate failure (invariant 3).
    /// </summary>
    private sealed class InvariantWalker : AstWalker
    {
        public override void VisitExpr(Expr expr)
        {
            if (expr is Expr.SequenceConstruct)
                throw new FuzzInvariantException(
                    "Surface parser produced Expr.SequenceConstruct, an internal-only " +
                    "sequence-join node that must never originate from source syntax.");

            base.VisitExpr(expr);
        }
    }
}
