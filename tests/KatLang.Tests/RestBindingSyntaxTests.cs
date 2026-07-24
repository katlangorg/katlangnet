namespace KatLang.Tests;

public class RestBindingSyntaxTests
{
    private static string Display(string source)
    {
        var result = KatLangEngine.Run(source);
        Assert.True(result is RunResult.Success, $"Expected success but got: {result.ToDisplayString()}");
        return result.ToDisplayString();
    }

    [Fact]
    public void PrefixRestBinding_CollectsEmptySingletonAndMultipleArgumentsAsExactLists()
    {
        Assert.Equal("[]", Display("F(...items) = items\nF()"));
        Assert.Equal("[1]", Display("F(...items) = items\nF(1)"));
        Assert.Equal("[1, 2, 3]", Display("F(...items) = items\nF(1, 2, 3)"));
    }

    [Fact]
    public void PrefixRestBinding_SupportsSumAndMovableMiddle()
    {
        Assert.Equal("6", Display("Sum(...items) = items.sum\nSum(1, 2, 3)"));
        Assert.Equal(
            "[2, 3, 4]",
            Display("Middle(first, ...middle, last) = middle\nMiddle(1, 2, 3, 4, 5)"));
    }

    [Fact]
    public void PrefixRestBinding_SupportsFrontMiddleAndFinalPositions()
    {
        Assert.Equal("[1, 2]", Display("F(...prefix, last) = prefix\nF(1, 2, 3)"));
        Assert.Equal("[2, 3]", Display("F(first, ...middle, last) = middle\nF(1, 2, 3, 4)"));
        Assert.Equal("[2, 3]", Display("F(first, ...suffix) = suffix\nF(1, 2, 3)"));
    }

    [Fact]
    public void PrefixRestDeconstruction_CollectsMovableMiddleAsExactList()
        => Assert.Equal(
            "(1, [2, 3, 4], 5)",
            Display(
                """
                first, ...middle, last = 1, 2, 3, 4, 5
                (first, middle, last)
                """));

    [Fact]
    public void Forwarding_UsesPrefixCollectAndPostfixOpenAsOppositeOperations()
        => Assert.Equal(
            "[1, 2, 3]",
            Display(
                """
                Target(...items) = items
                Forward(...items) = Target(items...)
                Forward(1, 2, 3)
                """));

    [Theory]
    [InlineData("F([1, 2])", "[[1, 2]]")]
    [InlineData("F([1, 2]...)", "[1, 2]")]
    [InlineData("F((1, 2))", "[(1, 2)]")]
    [InlineData("F((1, 2)...)", "[1, 2]")]
    [InlineData("F([])", "[[]]")]
    [InlineData("F([]...)", "[]")]
    [InlineData("F(())", "[()]")]
    [InlineData("F(()...)", "[]")]
    public void PrefixRestBinding_PreservesExistingListAndSequenceArgumentBoundaries(
        string call,
        string expected)
        => Assert.Equal(expected, Display($"F(...items) = items\n{call}"));

    [Fact]
    public void LegacyPostfixRestBinding_KeepsRuntimeSemanticsAndWarnsOnlyAtBindingSite()
    {
        const string source =
            """
            Target(items...) = items
            Forward(items...) = Target(items...)
            Forward(1, 2, 3)
            """;

        var parse = Parser.Parse(source);
        Assert.False(parse.HasErrors);
        Assert.Equal(2, parse.Diagnostics.Count);
        Assert.All(parse.Diagnostics, diagnostic =>
        {
            Assert.Equal(DiagnosticSeverity.Warning, diagnostic.Severity);
            Assert.Contains("Postfix rest binding", diagnostic.Message, StringComparison.Ordinal);
        });

        var evaluated = Evaluator.Run(new Expr.Block(parse.Root));
        Assert.True(evaluated.IsOk, evaluated.IsError ? evaluated.Error.ToString() : string.Empty);
        var list = Assert.IsType<Result.ListValue>(evaluated.Value);
        Assert.Equal([1m, 2m, 3m], list.Items.Cast<Result.Atom>().Select(static item => item.Value));
    }

    [Fact]
    public void LegacyPostfixRestDeconstruction_KeepsRuntimeSemanticsAndWarns()
    {
        const string source =
            """
            first, middle..., last = 1, 2, 3, 4
            (first, middle, last)
            """;

        var parse = Parser.Parse(source);
        Assert.False(parse.HasErrors);
        var warning = Assert.Single(parse.Diagnostics);
        Assert.Equal(DiagnosticSeverity.Warning, warning.Severity);
        Assert.Contains("write `...middle`", warning.Message, StringComparison.Ordinal);

        Assert.Equal("(1, [2, 3], 4)", Display(source));
    }

    [Fact]
    public void PrefixRestBinding_DotReceiverRemainsOneSlotUnlessExplicitlySpread()
    {
        Assert.Equal("[[1, 2]]", Display("F(...items) = items\nA = [1, 2]\nA.F"));
        Assert.Equal("[1, 2]", Display("F(...items) = items\nA = [1, 2]\n(A...).F"));
    }
}
