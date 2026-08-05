using KatLang.Formatting;
using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests.Formatting;

/// <summary>
/// The <c>exact</c> formatter is a façade over the same canonical renderer as
/// <see cref="RunResult.ToDisplayString"/>, so the two are byte-identical for
/// every outcome. The canonical-golden tests additionally pin that canonical
/// output preserves string content verbatim — including <c>_</c>, which was
/// verified to receive NO special display handling anywhere (the only
/// underscore stripping in the code base is the numeric-literal digit
/// separator in the lexer, which never touches string values).
/// </summary>
public class ExactFormatterCompatibilityTests
{
    private static readonly string[] CuratedSources =
    [
        "7",
        "1, 2, 3",
        "(1, 2)",
        "1, (2, 3)",
        "((1, 2), 3), (4, (5, 6))",
        "[1, 2, 3]",
        "[(1, 2), [3, [4]]]",
        "[[], ()]",
        "()",
        "(())",
        "[]",
        "''",
        "'text'",
        "'net_salary'",
        "'net salary'",
        "'netsalary'",
        "('a', 'b')",
        "('neto', 1473.8)",
        "0.5 + 0.5",
        "DisplayDecimals = 2\n1.5",
        "DisplayDecimals = 3\nMath.Pi",
        "DisplayDecimals = 6\n0.000000000000000000000000000",
        "SalaryExpenses(amount, recurring, reimbursed) = amount, recurring, reimbursed\n\nSalaryExpenses(3800, 1, 0)\n''\nSalaryExpenses(50, 0, 0)",
        "E = ()\nE*",
        "x, *rest = 1\nrest",
        "2 +",
        "1 / 0",
        "nonexistent",
        "T = 4",
        "Id(x) = x\nId(1, 2)",
    ];

    [Fact]
    public void ExactFormat_EqualsToDisplayString_ForCuratedCases()
    {
        foreach (var source in CuratedSources)
        {
            var run = KatLangEngine.Run(source);
            Assert.Equal(run.ToDisplayString(), OutputFormatters.Exact.Format(run));
        }
    }

    [Fact]
    public void ExactFormat_EqualsToDisplayString_ForEveryLanguageSpecCase()
    {
        foreach (var specCase in LanguageSpecCorpus.AllCases())
        {
            var run = KatLangEngine.Run(specCase.Source);
            Assert.True(
                run.ToDisplayString() == OutputFormatters.Exact.Format(run),
                $"spec case '{specCase.Id}' diverged between ToDisplayString and Exact.Format.");

            foreach (var probe in specCase.Probes)
            {
                var probeRun = KatLangEngine.Run(probe.Probe);
                Assert.Equal(probeRun.ToDisplayString(), OutputFormatters.Exact.Format(probeRun));
            }
        }
    }

    [Fact]
    public void ExactFormat_EqualsToDisplayString_ForEverySemanticExplorerCase()
    {
        foreach (var explorerCase in SemanticExplorerCorpus.AllCases())
        {
            var run = KatLangEngine.Run(explorerCase.Source);
            Assert.True(
                run.ToDisplayString() == OutputFormatters.Exact.Format(run),
                $"explorer case '{explorerCase.Id}' diverged between ToDisplayString and Exact.Format.");
        }
    }

    [Fact]
    public void ExactFormat_EqualsToDisplayString_UnderConfiguredDisplayLimits()
    {
        foreach (var source in new[] { "1, 2, 3", "[(1, 2), [3, [4]]]", "'abc', 'def'", ")(", "1 div 0", "Value = 1" })
        {
            var naturalLength = KatLangEngine.Run(source).ToDisplayString().Length;
            for (var limit = 0; limit <= naturalLength + 2; limit++)
            {
                var run = KatLangEngine.Run(source, new RunOptions
                {
                    EvaluationLimits = new EvaluationLimits { MaxDisplayLength = limit },
                });
                Assert.Equal(run.ToDisplayString(), OutputFormatters.Exact.Format(run));
            }
        }
    }

    [Fact]
    public void ExactFormat_OptionLoweredLimit_MatchesARunConfiguredWithThatLimit()
    {
        const string source = "1, 2, 3, 4, 5";
        var unrestricted = KatLangEngine.Run(source);
        for (var limit = 0; limit <= 16; limit++)
        {
            var configuredRun = KatLangEngine.Run(source, new RunOptions
            {
                EvaluationLimits = new EvaluationLimits { MaxDisplayLength = limit },
            });
            Assert.Equal(
                configuredRun.ToDisplayString(),
                OutputFormatters.Exact.Format(unrestricted, new OutputFormattingOptions { MaxDisplayLength = limit }));
        }
    }

    [Fact]
    public void ExactFormat_IgnoresLayoutAndDelimiterOptions()
    {
        var run = KatLangEngine.Run("('net_salary', 1473.8), 'x', [1, 2]");
        var canonical = run.ToDisplayString();

        Assert.Equal(canonical, OutputFormatters.Exact.Format(run, new OutputFormattingOptions
        {
            StringDelimiters = StringDelimiterMode.Always,
            PreferredLineWidth = 1,
            IndentSize = 8,
            RootOutputSpacing = 5,
            NewLine = "|",
        }));
    }

    /// <summary>
    /// Canonical goldens proving underscores were never specially handled by
    /// display: string content renders verbatim, and only the number-literal
    /// digit-separator rule (a lexer number rule, not display) consumes
    /// underscores.
    /// </summary>
    [Theory]
    [InlineData("'net_salary'", "net_salary")]
    [InlineData("'net salary'", "net salary")]
    [InlineData("'netsalary'", "netsalary")]
    [InlineData("'_'", "_")]
    [InlineData("'__'", "__")]
    [InlineData("'a_b_c'", "a_b_c")]
    [InlineData("'leading_'", "leading_")]
    [InlineData("'_trailing'", "_trailing")]
    [InlineData("('net_salary', 1473.8)", "(net_salary, 1473.8)")]
    [InlineData("['a_b', ('c_d', 1)]", "[a_b, (c_d, 1)]")]
    [InlineData("1_000", "1000")] // number-literal digit separator: lexical number syntax, not string content
    public void CanonicalDisplay_PreservesUnderscoreStringContent(string source, string expected)
    {
        var run = KatLangEngine.Run(source);
        Assert.Equal(expected, run.ToDisplayString());
        Assert.Equal(expected, OutputFormatters.Exact.Format(run));
    }
}
