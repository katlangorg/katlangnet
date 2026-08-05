using KatLang.Formatting;

namespace KatLang.Tests.Formatting;

/// <summary>
/// Option validation, defaults, determinism, and culture invariance of the
/// formatting subsystem.
/// </summary>
public class FormattingOptionsTests
{
    // ── Defaults and validation ──────────────────────────────────────────────

    [Fact]
    public void Defaults_MatchTheDocumentedValues()
    {
        var options = OutputFormattingOptions.Default;
        Assert.Equal(100, options.PreferredLineWidth);
        Assert.Equal(2, options.IndentSize);
        Assert.Equal(Environment.NewLine, options.NewLine);
        Assert.Equal(1, options.RootOutputSpacing);
        Assert.Equal(StringDelimiterMode.WhenNeeded, options.StringDelimiters);
        Assert.Null(options.MaxDisplayLength);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(-1)]
    public void NonPositiveLineWidth_Throws(int width)
        => Assert.Throws<ArgumentOutOfRangeException>(
            () => new OutputFormattingOptions { PreferredLineWidth = width });

    [Fact]
    public void NegativeIndentAndSpacingAndLimit_Throw()
    {
        Assert.Throws<ArgumentOutOfRangeException>(() => new OutputFormattingOptions { IndentSize = -1 });
        Assert.Throws<ArgumentOutOfRangeException>(() => new OutputFormattingOptions { RootOutputSpacing = -1 });
        Assert.Throws<ArgumentOutOfRangeException>(() => new OutputFormattingOptions { MaxDisplayLength = -1 });
    }

    [Fact]
    public void NullOrEmptyNewLine_Throws()
    {
        Assert.Throws<ArgumentNullException>(() => new OutputFormattingOptions { NewLine = null! });
        Assert.Throws<ArgumentException>(() => new OutputFormattingOptions { NewLine = string.Empty });
    }

    [Fact]
    public void UndefinedDelimiterMode_Throws()
        => Assert.Throws<ArgumentOutOfRangeException>(
            () => new OutputFormattingOptions { StringDelimiters = (StringDelimiterMode)99 });

    [Fact]
    public void ExcessiveValues_AreClampedAndStayUsable()
    {
        // Huge requests construct fine (clamped to the supported ceilings) and
        // cannot create unreasonable intermediate work or overflow arithmetic.
        var options = new OutputFormattingOptions
        {
            PreferredLineWidth = int.MaxValue,
            IndentSize = int.MaxValue,
            RootOutputSpacing = int.MaxValue,
            MaxDisplayLength = int.MaxValue,
            NewLine = "\n",
        };

        var text = OutputFormatters.Readable.Format(KatLangEngine.Run("1, 2"), options);
        Assert.Equal(OutputFormattingOptions.MaxSupportedPreferredLineWidth, options.PreferredLineWidth);
        Assert.Equal(OutputFormattingOptions.MaxSupportedIndentSize, options.IndentSize);
        Assert.Equal(OutputFormattingOptions.MaxSupportedRootOutputSpacing, options.RootOutputSpacing);
        Assert.Equal(EvaluationLimits.MaxSupportedDisplayLength, options.MaxDisplayLength);
        Assert.Equal(
            "1" + string.Concat(Enumerable.Repeat("\n", OutputFormattingOptions.MaxSupportedRootOutputSpacing + 1)) + "2",
            text);
    }

    [Fact]
    public void ZeroIndent_IsLegal()
        => Assert.Equal(
            "(\n1,\n2\n)",
            OutputFormatters.Readable.Format(
                KatLangEngine.Run("(1, 2)"),
                new OutputFormattingOptions { PreferredLineWidth = 1, IndentSize = 0, NewLine = "\n" }));

    // ── Determinism ──────────────────────────────────────────────────────────

    [Fact]
    public void RepeatedCalls_ReturnByteIdenticalOutput()
    {
        var run = KatLangEngine.Run("(('neto', 1473.8), ('taxes', 998.36)), [1.5, -2.25]");
        foreach (var formatter in OutputFormatters.All)
        {
            var options = new OutputFormattingOptions { NewLine = "\n", PreferredLineWidth = 15 };
            var first = formatter.Format(run, options);
            var second = formatter.Format(run, options);
            Assert.Equal(first, second);
        }
    }

    [Fact]
    public void ExoticNewLine_IsRespectedExactly()
    {
        var run = KatLangEngine.Run("1, 2");
        var zeroSpacing = new OutputFormattingOptions { NewLine = "|", RootOutputSpacing = 0 };
        var oneSpacing = new OutputFormattingOptions { NewLine = "|", RootOutputSpacing = 1 };

        Assert.Equal("1|2", OutputFormatters.Readable.Format(run, zeroSpacing));
        Assert.Equal("1||2", OutputFormatters.Readable.Format(run, oneSpacing));
    }

    private static void RunUnderCulture(string cultureName, Action assertions)
    {
        var previous = System.Globalization.CultureInfo.CurrentCulture;
        try
        {
            System.Globalization.CultureInfo.CurrentCulture =
                System.Globalization.CultureInfo.GetCultureInfo(cultureName);
            assertions();
        }
        finally
        {
            System.Globalization.CultureInfo.CurrentCulture = previous;
        }
    }

    [Theory]
    [InlineData("de-DE")]
    [InlineData("fr-FR")]
    [InlineData("en-US")]
    public void NumericFormatting_IsCultureInvariantInEveryFormatter(string cultureName)
        => RunUnderCulture(cultureName, () =>
        {
            var options = new OutputFormattingOptions { NewLine = "\n" };

            Assert.Equal("(2.5, 3.5)", OutputFormatters.Readable.Format(KatLangEngine.Run("(2.5, 3.5)"), options));
            Assert.Equal("2.5 3.5", OutputFormatters.Concise.Format(KatLangEngine.Run("(2.5, 3.5)"), options));
            Assert.Equal("[1.5, -2.25]", OutputFormatters.Concise.Format(KatLangEngine.Run("[1.5, -2.25]"), options));
            Assert.Equal("(2.5, 3.5)", OutputFormatters.Exact.Format(KatLangEngine.Run("(2.5, 3.5)")));
        });

    [Fact]
    public void DisplayDecimals_AppliesToEveryFormatter()
    {
        const string source = "DisplayDecimals = 2\n\n(Math.Pi, Math.E)";
        var run = KatLangEngine.Run(source);
        var options = new OutputFormattingOptions { NewLine = "\n" };

        Assert.Equal("(3.14, 2.72)", OutputFormatters.Exact.Format(run));
        Assert.Equal("(3.14, 2.72)", OutputFormatters.Readable.Format(run, options));
        Assert.Equal("3.14 2.72", OutputFormatters.Concise.Format(run, options));
    }

    [Fact]
    public void OptionsInstances_AreImmutableAndShareable()
    {
        var options = new OutputFormattingOptions { NewLine = "\n", PreferredLineWidth = 8 };
        var results = new string[16];
        Parallel.For(0, results.Length, i =>
            results[i] = OutputFormatters.Readable.Format(KatLangEngine.Run("(10, 20, 30)"), options));

        Assert.All(results, text => Assert.Equal("(\n  10,\n  20,\n  30\n)", text));
    }

    [Fact]
    public void EffectivelyEqualClampedOptions_HaveRecordValueEquality()
    {
        var excessive = new OutputFormattingOptions
        {
            PreferredLineWidth = int.MaxValue,
            IndentSize = int.MaxValue,
            RootOutputSpacing = int.MaxValue,
            MaxDisplayLength = int.MaxValue,
        };
        var ceilings = new OutputFormattingOptions
        {
            PreferredLineWidth = OutputFormattingOptions.MaxSupportedPreferredLineWidth,
            IndentSize = OutputFormattingOptions.MaxSupportedIndentSize,
            RootOutputSpacing = OutputFormattingOptions.MaxSupportedRootOutputSpacing,
            MaxDisplayLength = EvaluationLimits.MaxSupportedDisplayLength,
        };

        Assert.Equal(ceilings, excessive);
        Assert.Equal(ceilings.GetHashCode(), excessive.GetHashCode());
    }

    [Fact]
    public void ConcurrentCalls_DoNotLeakLayoutOrDelimiterState()
    {
        var run = KatLangEngine.Run("('a', 1), ('income tax', 2)");
        var variants = new[]
        {
            new OutputFormattingOptions { NewLine = "\n", RootOutputSpacing = 0, StringDelimiters = StringDelimiterMode.Always },
            new OutputFormattingOptions { NewLine = "|", RootOutputSpacing = 2, StringDelimiters = StringDelimiterMode.WhenNeeded },
            new OutputFormattingOptions { NewLine = "\r\n", PreferredLineWidth = 5, StringDelimiters = StringDelimiterMode.Never },
        };
        var expected = variants.Select(options => OutputFormatters.Concise.Format(run, options)).ToArray();
        var actual = new string[96];

        Parallel.For(0, actual.Length, i =>
        {
            var optionIndex = i % variants.Length;
            actual[i] = OutputFormatters.Concise.Format(run, variants[optionIndex]);
        });

        for (var i = 0; i < actual.Length; i++)
            Assert.Equal(expected[i % variants.Length], actual[i]);
    }
}
