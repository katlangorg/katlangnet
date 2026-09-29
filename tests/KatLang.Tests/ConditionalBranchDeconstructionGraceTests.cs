namespace KatLang.Tests;

/// <summary>
/// Constitution PV-49 (PAR-06, AGENTS F10, PAT-04): Grace must be effective, and a conditional
/// branch infers nothing — its head is the complete input specification — so no marker in any
/// row the branch WRITES can reorder anything. Assignment deconstruction hoists its right-hand
/// side out of the body's output into a synthetic source whose rows are rows of the ENCLOSING
/// body (<c>AstHelpers.WrittenRows</c>), and the parser's branch Grace scan read only the
/// output: <c>F(n) = { a, b = (~n, 1) ⏎ a + b }</c> in a family ran silently, while the same
/// body under one clause and the family row <c>a = ~Rate</c> were
/// <see cref="DiagnosticCode.InvalidGraceMarker"/>. The scan now covers every written row —
/// exactly the rows the detector's branch region rewrites under its not-reported policy, which
/// relies on it — so the one report is the parser's, wherever in the right-hand side the marker
/// stands. Grace in a level that really infers (a nested property of the branch, an ordinary
/// block) stays valid.
/// </summary>
public class ConditionalBranchDeconstructionGraceTests
{
    [Theory]
    [InlineData("{ ~n }")]
    [InlineData("{ { ~n } }")]
    [InlineData("{ c, d = (~n, 1)\n c + d }")]
    public void NestedBlockGrace_HasTheSameDiagnostics_InRowAndDeconstruction(string expression)
    {
        // Preserve PV-28/Q-16: the parser scans inline output blocks, and the detector owns
        // their enclosing-binding rejection. Adding the RHS must not add another walk.
        static string[] GraceMessages(string body)
            => SourceProvenance.ExpectFrontEndError($"F(0) = 0\nF(n) = {{\n {body}\n}}\nF(5)")
                .Where(d => d.Code == DiagnosticCode.InvalidGraceMarker).Select(d => d.Message).ToArray();
        var row = GraceMessages(expression);
        var rhs = GraceMessages($"a, b = ({expression}, 1)\n a + b");
        Assert.NotEmpty(row);
        Assert.Equal(row, rhs);
    }

    [Theory]
    [InlineData("n.~count")]
    [InlineData("(~n).count")]
    [InlineData("if(true, ~n, 0)")]
    [InlineData("[(~n, 1)]")]
    public void Grace_InNestedRightHandSideExpression_IsReportedByTheBranch(string expression)
        => SingleBranchGraceDiagnostic($"F(0) = 0\nF(n) = {{\n a, b = ({expression}, 1)\n a + b\n}}\nF(5)");

    private const string BranchMessage = "Grace is not allowed in conditional branch bodies for 'F'.";

    private static Diagnostic SingleBranchGraceDiagnostic(string source)
    {
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError(source));
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Equal(BranchMessage, diagnostic.Message);
        return diagnostic;
    }

    [Theory]
    // a branch binder, a visible property, a nested operand, a list right-hand side, a call
    // argument, postfix Grace, a collecting target, a repeated binder, a later deconstruction
    [InlineData("F(0) = 0\nF(n) = {\n    a, b = (~n, 1)\n    a + b\n}\nF(5)", 3, 13, 15)]
    [InlineData("Rate = 3\nF(0) = 0\nF(n) = {\n    a, b = (~Rate, n)\n    a + b\n}\nF(5)", 4, 13, 18)]
    [InlineData("F(0) = 0\nF(n) = {\n    a, b = (n + ~n, 1)\n    a + b\n}\nF(5)", 3, 17, 19)]
    [InlineData("F(0) = 0\nF(n) = {\n    a, b = [~n, 1]\n    a + b\n}\nF(5)", 3, 13, 15)]
    [InlineData("Pair(x) = x, x\nF(0) = 0\nF(n) = {\n    a, b = Pair(~n)\n    a + b\n}\nF(5)", 4, 17, 19)]
    [InlineData("F(0) = 0\nF(n) = {\n    a, b = (n~, 1)\n    a + b\n}\nF(5)", 3, 13, 15)]
    [InlineData("F(0) = 0\nF(n) = {\n    a, *r = (~n, 1, 2)\n    a + r.count\n}\nF(5)", 3, 14, 16)]
    [InlineData("F(0, 0) = 0\nF(x, x) = {\n    a, b = (~x, 1)\n    a + b\n}\nF(5, 5)", 3, 13, 15)]
    [InlineData("F(0) = 0\nF(n) = {\n    a = n\n    b, c = (1, ~n)\n    a + b + c\n}\nF(5)", 4, 16, 18)]
    // a family nested in a block body
    [InlineData("Outer = {\n    F(0) = 0\n    F(n) = {\n        a, b = (~n, 1)\n        a + b\n    }\n    F(5)\n}\nOuter", 4, 17, 19)]
    public void Grace_InABranchDeconstructionRightHandSide_IsRejected(string source, int line, int column, int endColumn)
    {
        var diagnostic = SingleBranchGraceDiagnostic(source);
        Assert.Equal(new SourceSpan(line, column, line, endColumn), diagnostic.Span);
        Assert.Equal(
            KatLangErrorCode.InvalidGraceMarker,
            Assert.Single(Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source)).Errors).Code);
    }

    [Theory]
    // The same marker as a branch output row and as a deconstruction right-hand side of that
    // branch: one verdict, one report, at the marker.
    [InlineData("(~n, 1)", "a, b = (~n, 1)\n    a + b")]
    [InlineData("~n + 1", "a, b = (~n + 1, 0)\n    a + b")]
    public void BranchRow_AndBranchDeconstruction_AgreeOnTheSameMarker(string row, string deconstruction)
    {
        var fromRow = SingleBranchGraceDiagnostic($"F(0) = 0\nF(n) = {{\n    {row}\n}}\nF(5)");
        var fromDeconstruction = SingleBranchGraceDiagnostic($"F(0) = 0\nF(n) = {{\n    {deconstruction}\n}}\nF(5)");
        Assert.Equal(3, fromRow.Span!.Value.Start.Line);
        Assert.Equal(3, fromDeconstruction.Span!.Value.Start.Line);
    }

    [Theory]
    // A free name: the branch's closed-input rule and the Grace rule report together, exactly as
    // for the same occurrence in a branch output row (and for a single literal clause).
    [InlineData("F(0) = 0\nF(n) = {\n    a, b = (~q, n)\n    a + b\n}\nF(5)")]
    [InlineData("F(0) = 0\nF(n) = {\n    ~q + n\n}\nF(5)")]
    [InlineData("F(0) = {\n    a, b = (~q, 1)\n    a + b\n}\nF(0)")]
    public void FreeNameWithGrace_InABranch_ReportsTheGraceAndTheUndeclaredName(string source)
    {
        var diagnostics = SourceProvenance.ExpectFrontEndError(source);
        Assert.Equal(
            [DiagnosticCode.InvalidGraceMarker, DiagnosticCode.UndeclaredIdentifier],
            diagnostics.Select(d => d.Code).ToArray());
        Assert.Equal(BranchMessage, diagnostics[0].Message);
    }

    [Fact]
    public void SingleClause_UnderItsClosedList_RejectsTheSameMarkerThroughTheDetector()
    {
        // The single-clause twin of the family witness: its closed explicit list infers
        // nothing, so the detector's effectiveness rule reports the same marker.
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError("G(n) = {\n    a, b = (~n, 1)\n    a + b\n}\nG(5)"));
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Equal(new SourceSpan(2, 13, 2, 15), diagnostic.Span);
    }

    // ── Grace in a level that really infers stays valid ─────────────────────

    [Theory]
    // `~x` moves the inferred `x` ahead of `y`: D(2, 10) binds x = 2, y = 10 → 10 / 2.
    [InlineData("D = {\n    a, b = (y, ~x)\n    a / b\n}\nD(2, 10)", "5")]
    // Without the marker, D(y, x): y = 2, x = 10 → 2 / 10 — the marker was effective.
    [InlineData("D = {\n    a, b = (y, x)\n    a / b\n}\nD(2, 10)", "0.2")]
    // A property nested in a branch is its own inferring level.
    [InlineData("F(0) = 0\nF(n) = {\n    P = {\n        a, b = (y, ~x)\n        a / b\n    }\n    P(2, 10) + n\n}\nF(1)", "6")]
    // The deconstruction itself, without a marker, is unchanged.
    [InlineData("F(0) = 0\nF(n) = {\n    a, b = (n, 1)\n    a + b\n}\nF(5)", "6")]
    public void Grace_WhereALevelInfers_IsUnchanged(string source, string display)
    {
        SourceProvenance.ParseValid(source);
        Assert.Equal(display, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }
}
