using KatLang.Formatting;

namespace KatLang.Tests.Formatting;

/// <summary>
/// String-delimiter policies for the layout formatters. Delimiters are
/// presentation syntax around the value: adding them never modifies the
/// string's content, and strings that cannot be quoted faithfully (KatLang has
/// no escape syntax) fall back to canonical raw rendering.
/// </summary>
public class StringDelimiterPolicyTests
{
    private static string FormatValue(string value, StringDelimiterMode mode)
        => FormatResult(new Result.Str(value), mode);

    private static string FormatResult(Result value, StringDelimiterMode mode)
    {
        var success = new RunResult.Success(
            new Algorithm.User(null, [], [], [], []),
            value,
            []);
        return OutputFormatters.Readable.Format(
            success,
            new OutputFormattingOptions { StringDelimiters = mode, NewLine = "\n" });
    }

    // ── Never ────────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("net_salary")]
    [InlineData("income tax")]
    [InlineData("123")]
    [InlineData("")]
    [InlineData(" leading")]
    [InlineData("trailing ")]
    [InlineData("()")]
    [InlineData("[1, 2]")]
    [InlineData("äöü ✓")]
    public void Never_RendersRawContent(string value)
        => Assert.Equal(value, FormatValue(value, StringDelimiterMode.Never));

    // ── WhenNeeded ───────────────────────────────────────────────────────────

    [Theory]
    [InlineData("neto", "neto")]
    [InlineData("social", "social")]
    [InlineData("net_salary", "net_salary")]
    [InlineData("income tax", "'income tax'")]
    [InlineData("äöü", "äöü")]
    [InlineData("", "''")]
    [InlineData("   ", "'   '")]
    [InlineData(" leading", "' leading'")]
    [InlineData("trailing ", "'trailing '")]
    [InlineData("123", "'123'")]
    [InlineData("1.5", "'1.5'")]
    [InlineData("-2", "'-2'")]
    [InlineData("+2", "'+2'")]
    [InlineData("1e3", "'1e3'")]
    [InlineData("1e999", "'1e999'")]
    [InlineData("1E-3", "'1E-3'")]
    [InlineData(".5", "'.5'")]
    [InlineData("5.", "'5.'")]
    [InlineData("()", "'()'")]
    [InlineData("[1, 2]", "'[1, 2]'")]
    [InlineData("a,b", "'a,b'")]
    [InlineData("tab\there", "'tab\there'")]
    [InlineData("\u00a0", "'\u00a0'")]
    [InlineData("١٢٣", "١٢٣")]
    [InlineData("😀", "😀")]
    [InlineData("neto:", "neto:")]
    [InlineData("+", "+")]
    [InlineData("-", "-")]
    public void WhenNeeded_QuotesOnlyAmbiguousStrings(string value, string expected)
        => Assert.Equal(expected, FormatValue(value, StringDelimiterMode.WhenNeeded));

    // ── Always ───────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("net_salary", "'net_salary'")]
    [InlineData("neto", "'neto'")]
    [InlineData("123", "'123'")]
    [InlineData("", "''")]
    [InlineData("income tax", "'income tax'")]
    public void Always_QuotesEveryQuotableString(string value, string expected)
        => Assert.Equal(expected, FormatValue(value, StringDelimiterMode.Always));

    // ── Unquotable host-built strings ────────────────────────────────────────

    [Theory]
    [InlineData("can't")]
    [InlineData("line1\nline2")]
    [InlineData("cr\rhere")]
    public void UnquotableHostStrings_FallBackToRawUnderEveryPolicy(string value)
    {
        // No escape syntax exists, so quoting would be unfaithful; the
        // documented conservative fallback renders the raw content unchanged.
        foreach (var mode in new[] { StringDelimiterMode.Never, StringDelimiterMode.WhenNeeded, StringDelimiterMode.Always })
            Assert.Equal(value, FormatValue(value, mode));
    }

    [Fact]
    public void AddingDelimiters_NeverModifiesContent()
    {
        foreach (var value in new[] { "net_salary", "123", "income tax", "   ", "a,b", "()", "tab\there", "äöü" })
        {
            foreach (var mode in new[] { StringDelimiterMode.WhenNeeded, StringDelimiterMode.Always })
            {
                var text = FormatValue(value, mode);
                Assert.True(
                    text == value || text == "'" + value + "'",
                    $"{mode} altered \"{value}\" into \"{text}\".");
            }
        }
    }

    [Fact]
    public void QuotedStrings_InsideStructures_KeepContentVerbatim()
    {
        var run = KatLangEngine.Run("('123', 'net_salary', 'a,b')");
        var text = OutputFormatters.Readable.Format(
            run,
            new OutputFormattingOptions { StringDelimiters = StringDelimiterMode.Always, NewLine = "\n" });

        Assert.Equal("('123', 'net_salary', 'a,b')", text);
    }

    [Fact]
    public void Exact_IgnoresTheDelimiterPolicy()
    {
        var run = KatLangEngine.Run("('123', '', 'net_salary')");
        var canonical = run.ToDisplayString();

        foreach (var mode in new[] { StringDelimiterMode.Never, StringDelimiterMode.WhenNeeded, StringDelimiterMode.Always })
        {
            Assert.Equal(canonical, OutputFormatters.Exact.Format(
                run,
                new OutputFormattingOptions { StringDelimiters = mode }));
        }
    }

    [Fact]
    public void QuotedNumericLookingString_StaysDistinctFromTheAtom()
    {
        var options = new OutputFormattingOptions { StringDelimiters = StringDelimiterMode.WhenNeeded, NewLine = "\n" };
        var atomText = OutputFormatters.Readable.Format(KatLangEngine.Run("123"), options);
        var stringText = OutputFormatters.Readable.Format(KatLangEngine.Run("'123'"), options);

        Assert.Equal("123", atomText);
        Assert.Equal("'123'", stringText);
        Assert.NotEqual(atomText, stringText);
    }

    /// <summary>
    /// Final audit (September 2026): the non-finite atoms render as <c>NaN</c>,
    /// <c>Infinity</c>, and <c>-Infinity</c>, so a STRING with exactly that content used to
    /// be indistinguishable from the atom under WhenNeeded — the confusion the
    /// numeric-looking rule exists to prevent. Those three spellings now count as
    /// numeric-looking (case-sensitively: <c>nan</c> is ordinary text).
    /// </summary>
    [Theory]
    [InlineData("N = (-2) ^ 0.5\nN", "'NaN'", "NaN")]
    [InlineData("10 ^ 9999\n", "'Infinity'", "Infinity")]
    [InlineData("-(10 ^ 9999)\n", "'-Infinity'", "-Infinity")]
    public void NonFiniteAtomSpelling_StaysDistinctFromTheAtom(string atomProgram, string stringLiteral, string spelling)
    {
        var options = new OutputFormattingOptions { StringDelimiters = StringDelimiterMode.WhenNeeded, NewLine = "\n" };
        var atomText = OutputFormatters.Readable.Format(KatLangEngine.Run(atomProgram), options);
        var stringText = OutputFormatters.Readable.Format(KatLangEngine.Run(stringLiteral), options);

        Assert.Equal(spelling, atomText);
        Assert.Equal(stringLiteral, stringText);
        Assert.NotEqual(atomText, stringText);

        // Ordinary text that merely resembles a spelling stays raw.
        Assert.Equal("nan", OutputFormatters.Readable.Format(KatLangEngine.Run("'nan'"), options));
        Assert.Equal("Infinite", OutputFormatters.Readable.Format(KatLangEngine.Run("'Infinite'"), options));
    }

    [Fact]
    public void WhitespaceBearingString_StaysDistinctFromAdjacentValues()
    {
        var options = new OutputFormattingOptions
        {
            StringDelimiters = StringDelimiterMode.WhenNeeded,
            NewLine = "\n",
        };

        var oneString = OutputFormatters.Concise.Format(KatLangEngine.Run("'income tax'"), options);
        var twoStrings = OutputFormatters.Concise.Format(KatLangEngine.Run("('income', 'tax')"), options);

        Assert.Equal("'income tax'", oneString);
        Assert.Equal("income tax", twoStrings);
        Assert.NotEqual(oneString, twoStrings);
    }
}
