namespace KatLang.Tests;

/// <summary>
/// Constitution PV-49 (PAR-06, AGENTS F10, PAT-04), kept under Q-16 G-O: Grace requires an OWN
/// inferred parameter of the owner whose written rows contain the marker, and a clause branch's
/// OWN level infers nothing — its head is the complete input specification — so no marker in any
/// row the branch WRITES is eligible. Assignment deconstruction hoists its right-hand side out of
/// the body's output into a synthetic source whose rows are rows of the ENCLOSING body
/// (<c>AstHelpers.WrittenRows</c>): <c>F(n) = { a, b = (~n, 1) ⏎ a + b }</c> in a family once ran
/// silently (the parser's former branch scan read only the output). The detector's branch region
/// rewrites every written row under its closed-branch policy, so the one report is the detector's,
/// at the marker, wherever in the right-hand side the marker stands, and hoisting never decides
/// legality. Grace in a level that really infers — a property or brace block nested in the branch,
/// an ordinary body — stays valid (<see cref="GraceOwnershipSemanticsTests"/> pins the owner law).
/// </summary>
public class ConditionalBranchDeconstructionGraceTests
{
    private const string BinderReason = "it is a binder of this clause's head";

    private static Diagnostic SingleBranchGraceDiagnostic(string source, string name, string reasonFragment)
    {
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError(source));
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.StartsWith($"Grace cannot reorder '{name}' because {reasonFragment}", diagnostic.Message, StringComparison.Ordinal);
        Assert.EndsWith("remove the marker.", diagnostic.Message, StringComparison.Ordinal);
        return diagnostic;
    }

    [Theory]
    [InlineData("{ ~n }")]
    [InlineData("{ { ~n } }")]
    [InlineData("{ c, d = (~n, 1)\n c + d }")]
    public void NestedBlockGrace_IsOneEnclosingParameterReport_InRowAndDeconstruction(string expression)
    {
        // The block is an owner of its own (Q-16(2) O): the branch binder `n` is a parameter of an
        // ENCLOSING algorithm there, so the block's region reports it — exactly once, whether the
        // block stands in a branch row or in the branch's deconstruction right-hand side, and
        // whether the marker is in the block's output or the block's own right-hand side (formerly
        // the parser's lexical scan added a second report for some of these spellings).
        static Diagnostic GraceDiagnostic(string body)
            => SingleBranchGraceDiagnostic(
                $"F(0) = 0\nF(n) = {{\n {body}\n}}\nF(5)", "n", "it already resolves to a parameter of an enclosing algorithm");
        var row = GraceDiagnostic(expression);
        var rhs = GraceDiagnostic($"a, b = ({expression}, 1)\n a + b");
        Assert.Equal(row.Message, rhs.Message);
    }

    [Theory]
    [InlineData("n.~count", "count", "it already resolves to the builtin 'count'")]
    [InlineData("(~n).count", "n", BinderReason)]
    [InlineData("if(true, ~n, 0)", "n", BinderReason)]
    [InlineData("[(~n, 1)]", "n", BinderReason)]
    public void Grace_InNestedRightHandSideExpression_IsReportedByTheBranchRegion(string expression, string name, string reason)
        => SingleBranchGraceDiagnostic($"F(0) = 0\nF(n) = {{\n a, b = ({expression}, 1)\n a + b\n}}\nF(5)", name, reason);

    [Theory]
    // a branch binder, a visible property, a nested operand, a list right-hand side, a call
    // argument, postfix Grace, a collecting target, a repeated binder, a later deconstruction
    [InlineData("F(0) = 0\nF(n) = {\n    a, b = (~n, 1)\n    a + b\n}\nF(5)", "n", BinderReason, 3, 13, 15)]
    [InlineData("Rate = 3\nF(0) = 0\nF(n) = {\n    a, b = (~Rate, n)\n    a + b\n}\nF(5)", "Rate", "it already resolves to a property", 4, 13, 18)]
    [InlineData("F(0) = 0\nF(n) = {\n    a, b = (n + ~n, 1)\n    a + b\n}\nF(5)", "n", BinderReason, 3, 17, 19)]
    [InlineData("F(0) = 0\nF(n) = {\n    a, b = [~n, 1]\n    a + b\n}\nF(5)", "n", BinderReason, 3, 13, 15)]
    [InlineData("Pair(x) = x, x\nF(0) = 0\nF(n) = {\n    a, b = Pair(~n)\n    a + b\n}\nF(5)", "n", BinderReason, 4, 17, 19)]
    [InlineData("F(0) = 0\nF(n) = {\n    a, b = (n~, 1)\n    a + b\n}\nF(5)", "n", BinderReason, 3, 13, 15)]
    [InlineData("F(0) = 0\nF(n) = {\n    a, *r = (~n, 1, 2)\n    a + r.count\n}\nF(5)", "n", BinderReason, 3, 14, 16)]
    [InlineData("F(0, 0) = 0\nF(x, x) = {\n    a, b = (~x, 1)\n    a + b\n}\nF(5, 5)", "x", BinderReason, 3, 13, 15)]
    [InlineData("F(0) = 0\nF(n) = {\n    a = n\n    b, c = (1, ~n)\n    a + b + c\n}\nF(5)", "n", BinderReason, 4, 16, 18)]
    // a family nested in a block body
    [InlineData("Outer = {\n    F(0) = 0\n    F(n) = {\n        a, b = (~n, 1)\n        a + b\n    }\n    F(5)\n}\nOuter", "n", BinderReason, 4, 17, 19)]
    public void Grace_InABranchDeconstructionRightHandSide_IsRejected(
        string source, string name, string reason, int line, int column, int endColumn)
    {
        var diagnostic = SingleBranchGraceDiagnostic(source, name, reason);
        Assert.Equal(new SourceSpan(line, column, line, endColumn), diagnostic.Span);
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.InvalidGraceMarker, error.Code);
        Assert.Equal(diagnostic.Span, error.Span);
    }

    [Theory]
    // The same marker as a branch output row and as a deconstruction right-hand side of that
    // branch: one verdict, one report, one message, at the marker — hoisting decides nothing.
    [InlineData("(~n, 1)", "a, b = (~n, 1)\n    a + b")]
    [InlineData("~n + 1", "a, b = (~n + 1, 0)\n    a + b")]
    public void BranchRow_AndBranchDeconstruction_AgreeOnTheSameMarker(string row, string deconstruction)
    {
        var fromRow = SingleBranchGraceDiagnostic($"F(0) = 0\nF(n) = {{\n    {row}\n}}\nF(5)", "n", BinderReason);
        var fromDeconstruction = SingleBranchGraceDiagnostic(
            $"F(0) = 0\nF(n) = {{\n    {deconstruction}\n}}\nF(5)", "n", BinderReason);
        Assert.Equal(fromRow.Message, fromDeconstruction.Message);
        Assert.Equal(3, fromRow.Span!.Value.Start.Line);
        Assert.Equal(3, fromDeconstruction.Span!.Value.Start.Line);
    }

    [Theory]
    // A free name: the branch's closed-input rule and the Grace rule report together, exactly as
    // for the same occurrence in a branch output row (and for a single literal clause) — in the
    // order a closed explicit list reports them: the undeclared name, then the marker.
    [InlineData("F(0) = 0\nF(n) = {\n    a, b = (~q, n)\n    a + b\n}\nF(5)")]
    [InlineData("F(0) = 0\nF(n) = {\n    ~q + n\n}\nF(5)")]
    [InlineData("F(0) = {\n    a, b = (~q, 1)\n    a + b\n}\nF(0)")]
    public void FreeNameWithGrace_InABranch_ReportsTheUndeclaredNameAndTheGrace(string source)
    {
        var diagnostics = SourceProvenance.ExpectFrontEndError(source);
        Assert.Equal(
            [DiagnosticCode.UndeclaredIdentifier, DiagnosticCode.InvalidGraceMarker],
            diagnostics.Select(d => d.Code).ToArray());
        Assert.StartsWith(
            "Grace cannot reorder 'q' because it stands on a clause branch's own level, where nothing is inferred",
            diagnostics[1].Message,
            StringComparison.Ordinal);
        Assert.Contains("An algorithm nested inside the branch may use Grace", diagnostics[1].Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SingleClause_UnderItsClosedList_RejectsTheSameMarkerThroughTheDetector()
    {
        // The single-clause twin of the family witness: its closed explicit list infers
        // nothing, so the detector's eligibility rule reports the same marker.
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError("G(n) = {\n    a, b = (~n, 1)\n    a + b\n}\nG(5)"));
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Equal(new SourceSpan(2, 13, 2, 15), diagnostic.Span);
        Assert.Contains("it already resolves to an explicit parameter", diagnostic.Message, StringComparison.Ordinal);
    }

    // ── Grace in a level that really infers stays valid ─────────────────────

    [Theory]
    // `~x` moves the inferred `x` ahead of `y`: D(2, 10) binds x = 2, y = 10 → 10 / 2.
    [InlineData("D = {\n    a, b = (y, ~x)\n    a / b\n}\nD(2, 10)", "5")]
    // Without the marker, D(y, x): y = 2, x = 10 → 2 / 10 — the marker moved `x`.
    [InlineData("D = {\n    a, b = (y, x)\n    a / b\n}\nD(2, 10)", "0.2")]
    // A property nested in a branch is its own inferring level.
    [InlineData("F(0) = 0\nF(n) = {\n    P = {\n        a, b = (y, ~x)\n        a / b\n    }\n    P(2, 10) + n\n}\nF(1)", "6")]
    // So is a brace block nested in the branch, its own deconstruction included (Q-16(2) O).
    [InlineData("Apply(f) = f(2, 10)\nF(0) = 0\nF(n) = Apply({\n    a, b = (y, ~x)\n    a / b\n}) + n\nF(1)", "6")]
    // The deconstruction itself, without a marker, is unchanged.
    [InlineData("F(0) = 0\nF(n) = {\n    a, b = (n, 1)\n    a + b\n}\nF(5)", "6")]
    public void Grace_WhereALevelInfers_IsUnchanged(string source, string display)
    {
        SourceProvenance.ParseValid(source);
        Assert.Equal(display, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }
}
