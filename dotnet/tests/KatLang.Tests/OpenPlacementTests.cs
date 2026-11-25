namespace KatLang.Tests;

/// <summary>
/// Constitution PV-25 (MOD-01): an algorithm body's one <c>open</c> declaration is its import
/// preamble, written before every declaration and output row of that body — clause definitions
/// included. The placement check counted only the properties and output rows collected so far,
/// while clause definitions are buffered in their families until the body ends, so
/// <c>P(a) = a</c> / <c>open Lib</c> was accepted although <c>P = a</c> / <c>open Lib</c> — the
/// same one-parameter callable — was <see cref="DiagnosticCode.InvalidOpenDeclaration"/>, and an
/// <c>open</c> between two clauses of one family was accepted too. The rule is per body: every
/// nested <c>{ … }</c> body, a clause body included, has its own preamble.
/// </summary>
public class OpenPlacementTests
{
    [Theory]
    [InlineData("\n")]
    [InlineData("\n# The preamble already ended.\n\n")]
    [InlineData("\r\n# Comment\r\n")]
    public void MisplacedOpen_DoesNotChangeClauseGroupingOrDeclarationOrder(string layout)
    {
        var before = "F(0) = 0" + layout;
        const string after = "F(1) = 1\nQ = 2\nF(n) = n\n3";
        var control = Parser.ParseSyntax(before + "\n" + after);
        var refused = Parser.ParseSyntax(before + "open Math\n" + after);
        Assert.Empty(control.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidOpenDeclaration, Assert.Single(refused.Diagnostics).Code);
        Assert.Equal(control.Root.Properties.Select(p => p.Name), refused.Root.Properties.Select(p => p.Name));
        var family = Assert.IsType<Algorithm.Conditional>(refused.Root.Properties.Single(p => p.Name == "F").Value);
        var expectedFamily = Assert.IsType<Algorithm.Conditional>(control.Root.Properties.Single(p => p.Name == "F").Value);
        Assert.Equal(expectedFamily.Branches.Select(b => b.Pattern), family.Branches.Select(b => b.Pattern));
        Assert.Equal(control.Root.Output.Count, refused.Root.Output.Count);
    }

    private const string PlacementMessage = "'open' declaration must appear before any properties or output expressions.";
    private const string Library = "Lib = { public X = 4 }\n";

    private static Diagnostic SinglePlacementDiagnostic(string source)
    {
        var diagnostic = Assert.Single(SourceProvenance.ParseAllowingDiagnostics(source).Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidOpenDeclaration, diagnostic.Code);
        Assert.Equal(PlacementMessage, diagnostic.Message);
        return diagnostic;
    }

    [Theory]
    // one clause (an ordinary single-clause definition), a public one, a literal clause
    [InlineData("P(a) = a\nopen Lib\n" + Library + "P(X)", 2, 1)]
    [InlineData("public P(a) = a\nopen Lib\n" + Library + "P(X)", 2, 1)]
    [InlineData("P(0) = 0\nopen Lib\n" + Library + "P(0)", 2, 1)]
    // between two clauses of one family, and after several families
    [InlineData("P(0) = 0\nopen Lib\nP(n) = n + X\n" + Library + "P(1)", 2, 1)]
    [InlineData("P(a) = a\nQ(0) = 0\nQ(n) = n\nopen Lib\n" + Library + "P(X) + Q(1)", 4, 1)]
    // a nested block body and a clause body keep the same rule for their own preamble
    [InlineData("A = {\n    P(a) = a\n    open Lib\n    P(X)\n}\n" + Library + "A", 3, 5)]
    [InlineData("P(0) = {\n    Q(a) = a\n    open Lib\n    Q(X)\n}\nP(n) = n\n" + Library + "P(0)", 3, 5)]
    public void Open_AfterAClauseDefinition_IsMisplaced(string source, int line, int column)
    {
        var diagnostic = SinglePlacementDiagnostic(source);
        Assert.Equal(new SourceSpan(line, column, line, column + 4), diagnostic.Span);
        Assert.Equal(
            KatLangErrorCode.InvalidOpenDeclaration,
            Assert.Single(Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source)).Errors).Code);
    }

    [Theory]
    // A preceding declaration decides the placement verdict by being a declaration, never by
    // its kind: the property, clause, family and deconstruction spellings agree exactly.
    [InlineData("P = a", "P(a) = a")]
    [InlineData("P = 0", "P(0) = 0")]
    [InlineData("x, y = 1, 2", "P(a) = a")]
    [InlineData("A = { 1 }", "A(0) = { 1 }")]
    public void Open_PlacementVerdict_DoesNotDependOnTheKindOfThePrecedingDeclaration(string property, string clause)
    {
        var fromProperty = SinglePlacementDiagnostic($"{property}\nopen Lib\n{Library}X");
        var fromClause = SinglePlacementDiagnostic($"{clause}\nopen Lib\n{Library}X");
        Assert.Equal(fromProperty.Span, fromClause.Span);
    }

    [Fact]
    public void SecondOpen_AfterAClauseDefinition_ReportsBothRules_LikeAfterAProperty()
    {
        static IReadOnlyList<string> Messages(string source)
            => SourceProvenance.ParseAllowingDiagnostics(source).Diagnostics.Select(d => d.Message).ToList();

        var afterClause = Messages("open Lib\nP(a) = a\nopen Lib2\n" + Library + "Lib2 = { public Y = 5 }\nP(X) + Y");
        var afterProperty = Messages("open Lib\nP = 1\nopen Lib2\n" + Library + "Lib2 = { public Y = 5 }\nP + Y");
        Assert.Equal(["Only one 'open' declaration is allowed per algorithm.", PlacementMessage], afterClause);
        Assert.Equal(afterProperty, afterClause);
    }

    [Theory]
    // open first, then clause definitions (one clause, a family)
    [InlineData("open Lib\nP(a) = a\n" + Library + "P(X)", "4")]
    [InlineData("open Lib\nP(0) = 0\nP(n) = n + X\n" + Library + "P(1)", "5")]
    // a nested body's own preamble after root clause definitions
    [InlineData("P(a) = a\nA = {\n    open Lib\n    P(X)\n}\n" + Library + "A", "4")]
    // a clause body's own preamble
    [InlineData("P(0) = {\n    open Lib\n    X\n}\nP(n) = n\n" + Library + "P(0)", "4")]
    public void Open_FirstInItsOwnBody_IsAccepted(string source, string display)
    {
        SourceProvenance.ParseValid(source);
        Assert.Equal(display, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }
}
