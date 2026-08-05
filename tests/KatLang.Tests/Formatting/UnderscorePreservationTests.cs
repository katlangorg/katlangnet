using KatLang.Formatting;

namespace KatLang.Tests.Formatting;

/// <summary>
/// Underscores are ordinary string content. A repository search confirmed no
/// display path ever deleted, replaced, or interpreted <c>_</c> (the only
/// underscore consumption is the lexer's number-literal digit separator),
/// and these tests pin that contract for every formatter and every
/// string-delimiter mode: <c>net_salary</c>, <c>net salary</c>, and
/// <c>netsalary</c> stay visibly distinct everywhere.
/// </summary>
public class UnderscorePreservationTests
{
    private static readonly string[] UnderscoreStrings =
    [
        "net_salary",
        "net salary",
        "netsalary",
        "_",
        "__",
        "a_b_c",
        "leading_",
        "_trailing",
    ];

    public static TheoryData<string, string> FormatterAndValue()
    {
        var data = new TheoryData<string, string>();
        foreach (var formatter in OutputFormatters.All)
        {
            foreach (var value in UnderscoreStrings)
                data.Add(formatter.Id, value);
        }

        return data;
    }

    [Theory]
    [MemberData(nameof(FormatterAndValue))]
    public void EveryFormatterAndDelimiterMode_PreservesTheStringVerbatim(string formatterId, string value)
    {
        Assert.True(OutputFormatters.TryGet(formatterId, out var formatter));
        var run = KatLangEngine.Run($"'{value}'");

        foreach (var mode in new[] { StringDelimiterMode.Never, StringDelimiterMode.WhenNeeded, StringDelimiterMode.Always })
        {
            var text = formatter!.Format(run, new OutputFormattingOptions { StringDelimiters = mode });

            // The exact content appears verbatim — possibly surrounded by
            // single-quote delimiters, never altered.
            Assert.True(
                text == value || text == "'" + value + "'",
                $"{formatterId}/{mode} rendered \"{value}\" as \"{text}\".");

            // No formatter deletes underscores, converts them to whitespace,
            // or changes casing.
            Assert.Equal(value.Count(c => c == '_'), text.Count(c => c == '_'));
            Assert.Equal(value.Count(char.IsWhiteSpace), text.Count(char.IsWhiteSpace));
            Assert.DoesNotContain(text, t => char.IsUpper(t) && !value.Contains(t));
        }
    }

    [Fact]
    public void UnderscoreAndSpaceVariants_RemainVisiblyDistinct()
    {
        foreach (var formatter in OutputFormatters.All)
        {
            var underscore = formatter.Format(KatLangEngine.Run("'net_salary'"));
            var space = formatter.Format(KatLangEngine.Run("'net salary'"));
            var joined = formatter.Format(KatLangEngine.Run("'netsalary'"));

            Assert.NotEqual(underscore, space);
            Assert.NotEqual(underscore, joined);
            Assert.NotEqual(space, joined);
            Assert.Contains("net_salary", underscore, StringComparison.Ordinal);
            Assert.Contains("net salary", space, StringComparison.Ordinal);
            Assert.Contains("netsalary", joined, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void NestedSequenceAndListStructures_PreserveUnderscores()
    {
        const string source = "(('net_salary', 1473.8), ['tax_rate', ('a_b', 1)])";
        foreach (var formatter in OutputFormatters.All)
        {
            foreach (var mode in new[] { StringDelimiterMode.Never, StringDelimiterMode.WhenNeeded, StringDelimiterMode.Always })
            {
                var text = formatter.Format(
                    KatLangEngine.Run(source),
                    new OutputFormattingOptions { StringDelimiters = mode });

                Assert.Contains("net_salary", text, StringComparison.Ordinal);
                Assert.Contains("tax_rate", text, StringComparison.Ordinal);
                Assert.Contains("a_b", text, StringComparison.Ordinal);
                Assert.DoesNotContain("net salary", text, StringComparison.Ordinal);
                Assert.DoesNotContain("netsalary", text, StringComparison.Ordinal);
            }
        }
    }
}
