using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>Thrown when the raw parser violates a fuzzing invariant. Escapes to the
/// fuzzing engine (or the replay runner) as a recorded failure.</summary>
internal sealed class FuzzInvariantException(string message) : Exception(message);

/// <summary>
/// Post-parse invariants checked on every fuzz input. These assert robustness
/// properties of the RAW parser output; they never assert that malformed input is
/// rejected — ordinary parser diagnostics are expected, not failures.
///
/// Invariants:
///   1. Diagnostic spans are well-formed and in-bounds for the source, matching the
///      lexer's exact line/column bookkeeping.
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
        // Reproduce the lexer's line/column model EXACTLY (see Lexer.Tokenize):
        //   * a line boundary is '\n' only; '\r' is transparent (advances neither
        //     line nor column), so CRLF and lone-CR inputs never desync;
        //   * every other character advances the column by one;
        //   * columns and lines are 1-based, so the largest legal column on a line
        //     is (visible width + 1) — the one-past-end position used for the EOF
        //     token and for end-exclusive lexer spans (e.g. number-too-large).
        var lineWidths = ComputeLineWidths(source);
        int maxLine = lineWidths.Count;

        foreach (var d in diagnostics)
        {
            var s = d.Span
                ?? throw Fail(d, "diagnostic span is null");

            // Positivity.
            Require(s.StartLineNumber >= 1, d, "start line < 1");
            Require(s.StartColumn >= 1, d, "start column < 1");
            Require(s.EndLineNumber >= 1, d, "end line < 1");
            Require(s.EndColumn >= 1, d, "end column < 1");

            // End position does not precede start position.
            Require(s.EndLineNumber >= s.StartLineNumber, d, "end line precedes start line");
            if (s.EndLineNumber == s.StartLineNumber)
                Require(s.EndColumn >= s.StartColumn, d, "end column precedes start column");

            // Lines are within the source.
            Require(s.StartLineNumber <= maxLine, d, $"start line {s.StartLineNumber} > line count {maxLine}");
            Require(s.EndLineNumber <= maxLine, d, $"end line {s.EndLineNumber} > line count {maxLine}");

            // Columns are plausible for their line (one-past-end allowed).
            int startMax = lineWidths[s.StartLineNumber - 1] + 1;
            int endMax = lineWidths[s.EndLineNumber - 1] + 1;
            Require(s.StartColumn <= startMax, d, $"start column {s.StartColumn} > line width+1 ({startMax})");
            Require(s.EndColumn <= endMax, d, $"end column {s.EndColumn} > line width+1 ({endMax})");
        }
    }

    /// <summary>
    /// Column width (max column index of a real character) for each 1-based line,
    /// using the lexer's rule: split on '\n', and within a line count every
    /// character except '\r'. The result always has at least one entry.
    /// </summary>
    private static List<int> ComputeLineWidths(string source)
    {
        var widths = new List<int>();
        int current = 0;
        foreach (char c in source)
        {
            if (c == '\n') { widths.Add(current); current = 0; }
            else if (c != '\r') { current++; }
        }
        widths.Add(current);
        return widths;
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

    private static void Require(bool condition, Diagnostic d, string what)
    {
        if (!condition)
            throw Fail(d, what);
    }

    private static FuzzInvariantException Fail(Diagnostic d, string what)
    {
        var s = d.Span;
        string span = s is null
            ? "<null>"
            : $"({s.StartLineNumber},{s.StartColumn})-({s.EndLineNumber},{s.EndColumn})";
        return new FuzzInvariantException($"Invalid diagnostic span [{what}]: span={span} message='{d.Message}'");
    }
}
