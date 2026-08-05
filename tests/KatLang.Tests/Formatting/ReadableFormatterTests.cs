using KatLang.Formatting;

namespace KatLang.Tests.Formatting;

/// <summary>
/// Hand-written golden expectations for the <c>readable</c> formatter. All
/// goldens pin an explicit "\n" newline so the expectations are
/// platform-independent; dedicated tests cover the platform default and custom
/// newline sequences.
/// </summary>
public class ReadableFormatterTests
{
    private static string Format(string source, OutputFormattingOptions options)
        => OutputFormatters.Readable.Format(KatLangEngine.Run(source), options);

    private static OutputFormattingOptions Options(
        int width = 100,
        int indent = 2,
        int spacing = 1,
        StringDelimiterMode delimiters = StringDelimiterMode.WhenNeeded)
        => new()
        {
            PreferredLineWidth = width,
            IndentSize = indent,
            RootOutputSpacing = spacing,
            NewLine = "\n",
            StringDelimiters = delimiters,
        };

    [Theory]
    [InlineData("(1, 2, 3)", "(1, 2, 3)")]
    [InlineData("[1, 2]", "[1, 2]")]
    [InlineData("()", "()")]
    [InlineData("[]", "[]")]
    [InlineData("7", "7")]
    [InlineData("('neto', 1473.8)", "(neto, 1473.8)")]
    [InlineData("('net_salary', 1473.8)", "(net_salary, 1473.8)")]
    [InlineData("[(1, 2), 3]", "[(1, 2), 3]")]
    public void SmallValues_StayInline(string source, string expected)
        => Assert.Equal(expected, Format(source, Options()));

    [Fact]
    public void WidthTriggered_MultilineSequence()
        => Assert.Equal(
            "(\n  10,\n  20,\n  30\n)",
            Format("(10, 20, 30)", Options(width: 8)));

    [Fact]
    public void WidthTriggered_MultilineList()
        => Assert.Equal(
            "[\n  10,\n  20,\n  30\n]",
            Format("[10, 20, 30]", Options(width: 8)));

    [Fact]
    public void NestedSequences_BreakOnlyWhereNeeded()
        => Assert.Equal(
            "(\n  (1, 2),\n  (3, 4)\n)",
            Format("((1, 2), (3, 4))", Options(width: 10)));

    [Fact]
    public void SequencesInsideList_KeepBracketsAndParentheses()
        => Assert.Equal(
            "[\n  (1, 2),\n  (3, 4)\n]",
            Format("[(1, 2), (3, 4)]", Options(width: 10)));

    [Fact]
    public void ListInsideSequence_NestsWithBrackets()
        => Assert.Equal(
            "(\n  1,\n  [\n    2,\n    3\n  ]\n)",
            Format("(1, [2, 3])", Options(width: 6)));

    [Fact]
    public void PairRun_GroupsOnePairPerLine()
        => Assert.Equal(
            "(\n  social, 681.8,\n  income, 316.2,\n  risk, 0.36\n)",
            Format("('social', 681.8, 'income', 316.2, 'risk', 0.36)", Options(width: 20)));

    [Fact]
    public void SalaryShapedValue_UsesStructuredMultilineLayout()
    {
        const string source =
            "(('neto', 1473.8), ('taxes', 998.36), ('social', 681.8, 'income', 316.2, 'risk', 0.36), ('total', 2472.16))";
        const string expected =
            "(\n" +
            "  (neto, 1473.8),\n" +
            "  (taxes, 998.36),\n" +
            "  (\n" +
            "    social, 681.8,\n" +
            "    income, 316.2,\n" +
            "    risk, 0.36\n" +
            "  ),\n" +
            "  (total, 2472.16)\n" +
            ")";

        Assert.Equal(expected, Format(source, Options(width: 40)));
    }

    [Theory]
    [InlineData(0, "1\n2")]
    [InlineData(1, "1\n\n2")]
    [InlineData(2, "1\n\n\n2")]
    public void RootOutputSpacing_PlacesBlankLinesBetweenBlocks(int spacing, string expected)
        => Assert.Equal(expected, Format("1, 2", Options(spacing: spacing)));

    [Fact]
    public void ExplicitEmptyStringRow_StaysVisibleUnderWhenNeeded()
        => Assert.Equal(
            "1\n\n''\n\n2",
            Format("1\n''\n2", Options()));

    [Fact]
    public void ExplicitEmptyStringRow_IsBlankUnderNever()
        => Assert.Equal(
            "1\n\n\n\n2",
            Format("1\n''\n2", Options(delimiters: StringDelimiterMode.Never)));

    [Theory]
    [InlineData(0, "(\n10,\n20,\n30\n)")]
    [InlineData(2, "(\n  10,\n  20,\n  30\n)")]
    [InlineData(4, "(\n    10,\n    20,\n    30\n)")]
    public void IndentSize_IsRespected(int indent, string expected)
        => Assert.Equal(expected, Format("(10, 20, 30)", Options(width: 8, indent: indent)));

    [Fact]
    public void CustomNewLine_IsUsedForEveryLineBreak()
        => Assert.Equal(
            "1\r\n\r\n2",
            OutputFormatters.Readable.Format(
                KatLangEngine.Run("1, 2"),
                new OutputFormattingOptions { NewLine = "\r\n" }));

    [Fact]
    public void DefaultNewLine_IsThePlatformNewLine()
        => Assert.Equal(
            $"1{Environment.NewLine}{Environment.NewLine}2",
            OutputFormatters.Readable.Format(KatLangEngine.Run("1, 2")));

    [Fact]
    public void LongLeafValues_AreNeverWrapped()
    {
        // Formatters never invent line breaks inside a value: a leaf longer
        // than the preferred width still renders whole on its line.
        const string text = "a rather long single string value";
        Assert.Equal($"'{text}'", Format($"'{text}'", Options(width: 5)));
    }

    [Fact]
    public void MultilineLayout_PreservesAllStructuralDelimiters()
    {
        var options = Options(width: 8);
        var text = Format("((1, 2), [3, 4], ())", options);

        // Same delimiters as canonical output, only whitespace differs.
        var exact = OutputFormatters.Exact.Format(KatLangEngine.Run("((1, 2), [3, 4], ())"));
        Assert.Equal(
            exact.Replace(" ", string.Empty),
            text.Replace(" ", string.Empty).Replace("\n", string.Empty));
    }

    [Fact]
    public void UnderscoreStrings_SurviveMultilineLayout()
        => Assert.Equal(
            "(\n  net_salary,\n  tax_rate\n)",
            Format("('net_salary', 'tax_rate')", Options(width: 10)));
}
