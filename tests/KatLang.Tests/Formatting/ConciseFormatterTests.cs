using KatLang.Formatting;

namespace KatLang.Tests.Formatting;

/// <summary>
/// Hand-written golden expectations for the <c>concise</c> formatter:
/// parentheses are hidden only in locally safe shapes, list brackets and
/// <c>()</c> always stay, and no punctuation is ever invented.
/// </summary>
public class ConciseFormatterTests
{
    private static string Format(string source, OutputFormattingOptions? options = null)
        => OutputFormatters.Concise.Format(KatLangEngine.Run(source), options ?? Options());

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

    // ── Safe parenthesis removal ─────────────────────────────────────────────

    [Theory]
    [InlineData("(1, 2, 3)", "1 2 3")]
    [InlineData("('alpha', 'beta')", "alpha beta")]
    [InlineData("('neto', 1473.8)", "neto 1473.8")]
    [InlineData("('net_salary', 1473.8)", "net_salary 1473.8")]
    public void RootSequence_SpaceJoinsWhenEveryTokenIsSafe(string source, string expected)
        => Assert.Equal(expected, Format(source));

    [Fact]
    public void SalaryShapedValue_FormsABlockWithANestedPairBlock()
    {
        const string source =
            "(('neto', 1473.8), ('taxes', 998.36), ('social', 681.8, 'income', 316.2, 'risk', 0.36), ('total', 2472.16))";
        const string expected =
            "neto 1473.8\n" +
            "taxes 998.36\n" +
            "  social 681.8\n" +
            "  income 316.2\n" +
            "  risk 0.36\n" +
            "total 2472.16";

        Assert.Equal(expected, Format(source, Options(width: 20)));
    }

    [Fact]
    public void RootBlock_HidesOuterParenthesesForMixedItems()
        => Assert.Equal("1\n[2, 3]", Format("(1, [2, 3])"));

    // ── Conservative retention ───────────────────────────────────────────────

    [Fact]
    public void SequenceInsideList_KeepsItsParentheses()
        => Assert.Equal("[(1, 2), 3]", Format("[(1, 2), 3]"));

    [Fact]
    public void WhitespaceBearingString_ForcesParentheses()
        => Assert.Equal("('a b', 1)", Format("('a b', 1)"));

    [Fact]
    public void CommaBearingString_ForcesParentheses()
        => Assert.Equal("('a,b', 1)", Format("('a,b', 1)"));

    [Fact]
    public void WhitespaceOnlyString_ForcesParentheses()
        => Assert.Equal("('   ', 1)", Format("('   ', 1)"));

    [Fact]
    public void AdjacentNestedSequences_KeepParenthesesWhenBlocksWouldMerge()
        => Assert.Equal(
            "(\n  100,\n  200,\n  300\n)\n(\n  400,\n  500,\n  600\n)",
            Format("((100, 200, 300), (400, 500, 600))", Options(width: 8)));

    [Fact]
    public void SubBlock_RequiresAPrecedingLineAndNoAdjacentBlock()
        => Assert.Equal(
            "1\n(\n  100,\n  200,\n  300\n)\n(\n  400,\n  500,\n  600\n)",
            Format("(1, (100, 200, 300), (400, 500, 600))", Options(width: 8)));

    [Fact]
    public void ChildSequenceFittingItsLine_BecomesOneLine()
        => Assert.Equal(
            "1\n100 200\n2",
            Format("(1, (100, 200), 2)", Options(width: 9)));

    [Fact]
    public void SingleSafeSubBlock_HangsOffThePrecedingLine()
        => Assert.Equal(
            "1\n  100\n  200\n  300\n2",
            Format("(1, (100, 200, 300), 2)", Options(width: 8)));

    // ── Empty values ─────────────────────────────────────────────────────────

    [Theory]
    [InlineData("()", "()")]
    [InlineData("[]", "[]")]
    public void EmptyValues_StayVisible(string source, string expected)
        => Assert.Equal(expected, Format(source));

    [Fact]
    public void EmptySequenceItem_StaysVisibleInsideABlock()
        => Assert.Equal("1\n()\n2", Format("(1, (), 2)"));

    // ── Strings under the delimiter policy ───────────────────────────────────

    [Fact]
    public void QuotedEmptyString_CanJoinALine()
        => Assert.Equal("a '' b", Format("('a', '', 'b')"));

    [Fact]
    public void UnquotedEmptyString_ForcesParentheses()
        => Assert.Equal("(a, , b)", Format("('a', '', 'b')", Options(delimiters: StringDelimiterMode.Never)));

    [Fact]
    public void NumericLookingString_IsQuotedAndJoinable()
        => Assert.Equal("'123' 5", Format("('123', 5)"));

    [Fact]
    public void NumericLookingString_UnderNever_RetainsSequenceParentheses()
        => Assert.Equal("(123, 5)", Format("('123', 5)", Options(delimiters: StringDelimiterMode.Never)));

    [Fact]
    public void StructureLookingString_IsQuotedAndJoinable()
        => Assert.Equal("'()' 1", Format("('()', 1)"));

    // ── No invented punctuation ──────────────────────────────────────────────

    [Fact]
    public void NeverInsertsAColon()
    {
        var text = Format("(('neto', 1473.8), ('taxes', 998.36))", Options(width: 15));
        Assert.DoesNotContain(":", text, StringComparison.Ordinal);
        Assert.Equal("neto 1473.8\ntaxes 998.36", text);
    }

    [Fact]
    public void ColonAppearsOnlyWhenTheStringContainsIt()
        => Assert.Equal("neto: 1473.8", Format("('neto:', 1473.8)"));

    [Fact]
    public void NoBulletsHeadingsOrCaseChanges()
    {
        var text = Format(
            "(('neto', 1473.8), ('taxes', 998.36), ('social', 681.8, 'income', 316.2, 'risk', 0.36))",
            Options(width: 20));
        Assert.DoesNotContain("-", text, StringComparison.Ordinal);
        Assert.DoesNotContain("*", text, StringComparison.Ordinal);
        Assert.DoesNotContain("#", text, StringComparison.Ordinal);
        Assert.DoesNotContain(":", text, StringComparison.Ordinal);
        Assert.Equal(text, text.ToLowerInvariant());
    }

    // ── Root outputs ─────────────────────────────────────────────────────────

    [Fact]
    public void MultipleRootOutputs_StaySeparatedBlocks()
        => Assert.Equal("a 1\n\nb 2", Format("('a', 1), ('b', 2)"));

    [Fact]
    public void ZeroRootSpacing_RetainsMultilineRootSequenceBoundary()
    {
        var oneNestedRoot = Format("((1, 2), (3, 4))", Options(width: 9, spacing: 0));
        var twoRootRows = Format("(1, 2), (3, 4)", Options(width: 9, spacing: 0));

        Assert.Equal("(\n  (1, 2),\n  (3, 4)\n)", oneNestedRoot);
        Assert.Equal("1 2\n3 4", twoRootRows);
        Assert.NotEqual(oneNestedRoot, twoRootRows);
    }

    [Fact]
    public void ZeroIndent_RetainsMultilineChildSequenceBoundary()
    {
        var nested = Format("(1, (100, 200, 300), 2)", Options(width: 8, indent: 0));
        var flat = Format("(1, 100, 200, 300, 2)", Options(width: 8, indent: 0));

        Assert.Equal("1\n(\n100,\n200,\n300\n)\n2", nested);
        Assert.Equal("1\n100\n200\n300\n2", flat);
        Assert.NotEqual(nested, flat);
    }

    [Fact]
    public void SequenceAndList_RemainDistinguishable()
    {
        // (1, 2) may lose its parentheses only because the line carries the
        // boundary; [1, 2] always keeps its brackets.
        Assert.Equal("1 2", Format("(1, 2)"));
        Assert.Equal("[1, 2]", Format("[1, 2]"));
    }

    [Fact]
    public void PairLinesInsideRetainedParentheses_KeepCanonicalCommas()
        => Assert.Equal(
            "(\n  'a b', 1,\n  'c d', 2\n)",
            Format("('a b', 1, 'c d', 2)", Options(width: 12)));

    [Fact]
    public void UnquotableHostString_ForcesSequenceParentheses()
    {
        var value = new Result.SequenceValue([new Result.Str("can't"), new Result.Atom(1)]);
        var success = new RunResult.Success(new Algorithm.User(null, [], [], [], []), value, []);

        Assert.Equal("(can't, 1)", OutputFormatters.Concise.Format(success, Options()));
    }

    [Theory]
    [InlineData('\u0085')] // NEXT LINE
    [InlineData('\u2028')] // LINE SEPARATOR
    [InlineData('\u2029')] // PARAGRAPH SEPARATOR
    public void PairRun_WithAUnicodeLineSeparatorLabel_FallsBackToOneItemPerLine(char separator)
    {
        // Not a safe concise token (whitespace), so no space join or pair
        // block forms; the retained-parentheses fallback must not group
        // pair lines either, because the separator breaks the rendered
        // line even inside quotes.
        var value = new Result.SequenceValue(
        [
            new Result.Str("a"), new Result.Atom(1),
            new Result.Str($"b{separator}c"), new Result.Atom(2),
        ]);
        var success = new RunResult.Success(new Algorithm.User(null, [], [], [], []), value, []);

        Assert.Equal(
            $"(\n  a,\n  1,\n  'b{separator}c',\n  2\n)",
            OutputFormatters.Concise.Format(success, Options(width: 12)));
    }

    [Theory]
    [InlineData('\u0085')] // NEXT LINE
    [InlineData('\u2028')] // LINE SEPARATOR
    [InlineData('\u2029')] // PARAGRAPH SEPARATOR
    public void PairRun_WithAUnicodeLineSeparatorStringValue_FallsBackToOneItemPerLine(char separator)
    {
        var value = new Result.SequenceValue(
        [
            new Result.Str("a"), new Result.Atom(1),
            new Result.Str("b"), new Result.Str($"x{separator}y"),
        ]);
        var success = new RunResult.Success(new Algorithm.User(null, [], [], [], []), value, []);

        Assert.Equal(
            $"(\n  a,\n  1,\n  b,\n  'x{separator}y'\n)",
            OutputFormatters.Concise.Format(success, Options(width: 12)));
    }
}
