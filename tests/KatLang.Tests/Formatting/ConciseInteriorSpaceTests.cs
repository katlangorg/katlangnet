using KatLang.Formatting;

namespace KatLang.Tests.Formatting;

/// <summary>
/// Concise joins and pair blocks use the rendered width and line boundaries.
/// The string-delimiter mode independently decides quoting.
/// </summary>
public class ConciseInteriorSpaceTests
{
    private const string Reproducer = """
        SalaryExpenses = {
            ('neto', 1),
            ('social tax', 3)
        }
        SalaryExpenses*
        """;

    private static OutputFormattingOptions Options(
        StringDelimiterMode mode,
        int spacing = 0,
        int width = 100,
        int? maxDisplayLength = null)
        => new()
        {
            PreferredLineWidth = width,
            IndentSize = 2,
            NewLine = "\n",
            RootOutputSpacing = spacing,
            StringDelimiters = mode,
            MaxDisplayLength = maxDisplayLength,
        };

    private static RunResult Run(string source)
    {
        var run = KatLangEngine.Run(source);
        Assert.IsType<RunResult.Success>(run);
        return run;
    }

    private static string Concise(string source, OutputFormattingOptions options)
        => OutputFormatters.Concise.Format(Run(source), options);

    [Theory]
    [InlineData(StringDelimiterMode.Never, "neto 1\nsocial tax 3")]
    [InlineData(StringDelimiterMode.WhenNeeded, "neto 1\n'social tax' 3")]
    [InlineData(StringDelimiterMode.Always, "'neto' 1\n'social tax' 3")]
    public void Reproducer_QuotingStaysIndependentOfParenthesisRemoval(StringDelimiterMode mode, string expected)
        => Assert.Equal(expected, Concise(Reproducer, Options(mode)));

    [Theory]
    [InlineData(StringDelimiterMode.Never, "neto 1\n\nsocial tax 3")]
    [InlineData(StringDelimiterMode.WhenNeeded, "neto 1\n\n'social tax' 3")]
    public void Reproducer_KeepsConfiguredRootSpacing(StringDelimiterMode mode, string expected)
        => Assert.Equal(expected, Concise(Reproducer, Options(mode, spacing: 1)));

    [Fact]
    public void Reproducer_ExactAndReadableAreUnchanged()
    {
        var run = Run(Reproducer);
        Assert.Equal(run.ToDisplayString(), OutputFormatters.Exact.Format(run, Options(StringDelimiterMode.Never)));
        Assert.Equal(
            "(neto, 1)\n(social tax, 3)",
            OutputFormatters.Readable.Format(run, Options(StringDelimiterMode.Never)));
        Assert.Equal(
            "(neto, 1)\n('social tax', 3)",
            OutputFormatters.Readable.Format(run, Options(StringDelimiterMode.WhenNeeded)));
    }

    [Theory]
    [InlineData(StringDelimiterMode.Never, "social  tax 3")]
    [InlineData(StringDelimiterMode.WhenNeeded, "'social  tax' 3")]
    [InlineData(StringDelimiterMode.Always, "'social  tax' 3")]
    public void RepeatedInteriorSpaces_ArePreservedVerbatimAndStayEligible(StringDelimiterMode mode, string expected)
        => Assert.Equal(expected, Concise("('social  tax', 3)", Options(mode)));

    [Theory]
    [InlineData(StringDelimiterMode.Never, "a b c d e")]
    [InlineData(StringDelimiterMode.WhenNeeded, "'a b c' 'd e'")]
    [InlineData(StringDelimiterMode.Always, "'a b c' 'd e'")]
    public void SeveralSpacedStrings_SpaceJoinOnOneLine(StringDelimiterMode mode, string expected)
        => Assert.Equal(expected, Concise("('a b c', 'd e')", Options(mode)));

    [Theory]
    [InlineData(StringDelimiterMode.Never, "id 1\n  net salary 1473.8\n  income  tax 500")]
    [InlineData(StringDelimiterMode.WhenNeeded, "id 1\n  'net salary' 1473.8\n  'income  tax' 500")]
    [InlineData(StringDelimiterMode.Always, "'id' 1\n  'net salary' 1473.8\n  'income  tax' 500")]
    public void NestedPairBlock_WithSpacedLabels_HidesChildPunctuation(StringDelimiterMode mode, string expected)
        => Assert.Equal(
            expected,
            Concise("(('id', 1), ('net salary', 1473.8, 'income  tax', 500))", Options(mode, spacing: 1)));

    [Theory]
    [InlineData(StringDelimiterMode.Never, 100)]
    [InlineData(StringDelimiterMode.Never, 24)]
    [InlineData(StringDelimiterMode.Never, 12)]
    [InlineData(StringDelimiterMode.Always, 100)]
    [InlineData(StringDelimiterMode.Always, 24)]
    [InlineData(StringDelimiterMode.Always, 12)]
    public void SpacedLabels_LayOutExactlyLikeSpaceFreeLabelsOfTheSameLength(StringDelimiterMode mode, int width)
    {
        // The layout decision (join, pair block, retained parentheses under
        // width pressure) is the same for 'net salary' as for 'net_salary':
        // ordinary interior spaces alone never change the shape.
        // (Never and Always quote both spellings alike, so token lengths match;
        // WhenNeeded quotes only the spaced one and is pinned explicitly above.)
        static string Spaced(string text) => text.Replace("net_salary", "net salary").Replace("income_tax", "income tax");

        foreach (var plain in new[]
        {
            "(('id', 1), ('net_salary', 1473.8, 'income_tax', 500))",
            "('net_salary', 1473.8, 'income_tax', 500)",
        })
        {
            Assert.Equal(
                Spaced(Concise(plain, Options(mode, width: width))),
                Concise(Spaced(plain), Options(mode, width: width)));
        }
    }

    [Theory]
    [InlineData(StringDelimiterMode.Never)]
    [InlineData(StringDelimiterMode.WhenNeeded)]
    [InlineData(StringDelimiterMode.Always)]
    public void NestedSequences_AndLists_KeepTheirOwnDelimiters(StringDelimiterMode mode)
    {
        var quote = mode == StringDelimiterMode.Never ? "" : "'";
        Assert.Equal(
            $"[({quote}a b{quote}, 1), 2]",
            Concise("[('a b', 1), 2]", Options(mode)));
    }

    [Theory]
    [InlineData(" lead", true)]
    [InlineData("trail ", true)]
    [InlineData("   ", true)]
    [InlineData("a, b", true)]
    [InlineData("net 1", true)]
    [InlineData("1 net", true)]
    [InlineData("x NaN", true)]
    [InlineData("a (b)", true)]
    [InlineData("a\tb", true)]
    [InlineData("a\u00A0b", true)]
    [InlineData("a\u200Bb", true)]
    [InlineData("a\0b", true)]
    [InlineData("can't", false)]
    public void SingleLineContent_JoinsRegardlessOfQuoting(string raw, bool quotable)
    {
        var value = new Result.SequenceValue([new Result.Str(raw), new Result.Atom(1)]);
        var success = new RunResult.Success(new Algorithm.User(null, [], [], [], []), value, []);
        foreach (var mode in Enum.GetValues<StringDelimiterMode>())
        {
            var token = quotable && mode != StringDelimiterMode.Never ? $"'{raw}'" : raw;
            Assert.Equal($"{token} 1", OutputFormatters.Concise.Format(success, Options(mode)));
        }
    }

    [Theory]
    [InlineData(StringDelimiterMode.Never, "id 1\n  net, salary 123\n  x NaN (tax)")]
    [InlineData(StringDelimiterMode.WhenNeeded, "id 1\n  'net, salary' '123'\n  'x NaN' '(tax)'")]
    [InlineData(StringDelimiterMode.Always, "'id' 1\n  'net, salary' '123'\n  'x NaN' '(tax)'")]
    public void NestedPairBlock_AcceptsSingleLineLabelsAndValues(StringDelimiterMode mode, string expected)
        => Assert.Equal(expected, Concise("(('id', 1), ('net, salary', '123', 'x NaN', '(tax)'))", Options(mode)));

    // ── Width and display limits ─────────────────────────────────────────────

    [Fact]
    public void NarrowWidth_StillNeverSplitsASpacedString()
    {
        var text = Concise("('social tax', 3, 'x', 4)", Options(StringDelimiterMode.Never, width: 8));
        Assert.Contains("social tax", text, StringComparison.Ordinal);
        foreach (var line in text.Split('\n'))
            Assert.NotEqual("social", line.Trim());
    }

    [Theory]
    [InlineData(StringDelimiterMode.Never)]
    [InlineData(StringDelimiterMode.WhenNeeded)]
    public void DisplayLimit_SweepIsAllOrNothing(StringDelimiterMode mode)
    {
        var run = Run(Reproducer);
        var natural = OutputFormatters.Concise.Format(run, Options(mode));
        for (var limit = 0; limit <= natural.Length + 2; limit++)
        {
            var text = OutputFormatters.Concise.Format(run, Options(mode, maxDisplayLength: limit));
            Assert.True(text.Length <= limit, $"limit {limit} returned {text.Length} units.");
            if (limit >= natural.Length)
                Assert.Equal(natural, text);
            else
                Assert.DoesNotContain("social tax", text, StringComparison.Ordinal);
        }
    }
}
