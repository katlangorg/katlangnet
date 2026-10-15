namespace KatLang.Tests;

public class LineFinalStarReviewRegressionTests
{
    [Fact]
    public void SelectionPrinciples_WorkedExample_KeepsItsIndependentRowAndCountExpectations()
    {
        const string definitions = "A = [[1, 2], [3, 4]]\n";
        foreach (var selection in new[] { "A[0]*", "(A[0])*" })
        {
            var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(definitions + selection));
            Assert.Equal(["1", "2"], success.OutputRows.Select(SixRouteAgreement.Neutral));
        }

        var captured = Assert.IsType<RunResult.Success>(KatLangEngine.Run(definitions + "(A*)[0]"));
        Assert.Equal("L[1, 2]", SixRouteAgreement.Neutral(Assert.Single(captured.OutputRows)));
        var count = Assert.IsType<RunResult.Success>(KatLangEngine.Run(definitions + "(A*).count"));
        Assert.Equal("2", SixRouteAgreement.Neutral(Assert.Single(count.OutputRows)));
        var fluent = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(definitions + "A*.count"));
        Assert.Equal(KatLangErrorCode.ArityMismatch, Assert.Single(fluent.Errors).Code);

        var text = File.ReadAllText(Path.Combine(RepoRoot.Find(), "docs/design/comma-output-join-spread-principles.md"));
        Assert.Contains("`(A*).count` is `2`", text, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("X = @*", 5, false)]
    [InlineData("X = (@*)", 6, true)]
    public void ReportedOperand_AttachesTheStarWithoutMakingRecoveryExecutable(string source, int column, bool capture)
    {
        var parsed = Parser.ParseSyntax(source);
        Assert.True(parsed.HasErrors);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.UnexpectedCharacter, diagnostic.Code);
        Assert.Equal(new SourceSpan(1, column, 1, column + 1), diagnostic.Span);
        Expr row = Assert.Single(Assert.Single(parsed.Root.Properties).Value.Output);
        if (capture)
            row = Assert.Single(Assert.IsType<Expr.Capture>(row).Body);
        var spread = Assert.IsType<Expr.SequenceSpread>(row);
        Assert.Equal(new SourceSpan(1, column, 1, column + 2), spread.Span);
        var placeholder = Assert.IsType<Expr.Num>(spread.Operand);
        Assert.Equal(0m, placeholder.Value);
        Assert.Equal(diagnostic.Span, placeholder.Span);
        Assert.Empty(parsed.Root.Output);
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
    }

    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    public void MalformedSpreadRun_StopsBeforeTheNextLinesMultiplication(string newline)
    {
        var source = "A **" + newline + "* B" + newline + "Later = 42" + newline + "Later";
        var parsed = Parser.ParseSyntax(source);
        Assert.True(parsed.HasErrors);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidSpreadMarker, diagnostic.Code);
        Assert.Equal(new SourceSpan(1, 1, 1, 5), diagnostic.Span);
        var product = Assert.IsType<Expr.Binary>(parsed.Root.Output[0]);
        Assert.Equal(BinaryOp.Mul, product.Op);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(product.Left).Name);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(product.Right).Name);
        Assert.Equal("Later", Assert.Single(parsed.Root.Properties).Name);
        Assert.Equal("Later", Assert.IsType<Expr.Resolve>(parsed.Root.Output[1]).Name);
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
    }

    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    public void AdjacentMalformedMarkerRuns_KeepTheFirstDiagnosticOnItsOwnLine(string newline)
    {
        // Both lines are malformed. Recovery must finish reporting the first run before
        // interpreting the leading stars on the next line through ordinary continuation.
        var source = "A **" + newline + "**, B" + newline + "Later = 42" + newline + "Later";
        var parsed = Parser.ParseSyntax(source);
        Assert.True(parsed.HasErrors);
        Assert.Equal(2, parsed.Diagnostics.Count);
        Assert.All(parsed.Diagnostics, d => Assert.Equal(DiagnosticCode.InvalidSpreadMarker, d.Code));
        Assert.Equal(new SourceSpan(1, 1, 1, 5), parsed.Diagnostics[0].Span);
        Assert.Equal(new SourceSpan(1, 1, 2, 3), parsed.Diagnostics[1].Span);
        Assert.Equal(["A", "B", "Later"], parsed.Root.Output.Select(e => Assert.IsType<Expr.Resolve>(e).Name));
        Assert.Equal("Later", Assert.Single(parsed.Root.Properties).Name);
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
    }
}
