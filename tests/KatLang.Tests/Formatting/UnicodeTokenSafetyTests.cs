using KatLang.Formatting;

namespace KatLang.Tests.Formatting;

/// <summary>
/// Quoting of invisible and invalid Unicode, supplementary characters, and
/// numeric-looking text. Concise preserves the content on joined lines.
/// </summary>
public class UnicodeTokenSafetyTests
{
    private static OutputFormattingOptions Preset(StringDelimiterMode mode)
        => new()
        {
            PreferredLineWidth = 100,
            IndentSize = 2,
            NewLine = "\n",
            RootOutputSpacing = 0,
            StringDelimiters = mode,
        };

    private static RunResult.Success PairOf(string label, decimal value)
        => new(
            new Algorithm.User(null, [], [], [], []),
            new Result.SequenceValue([new Result.Str(label), new Result.Atom(value)]),
            []);

    private static string Concise(string label, decimal value, StringDelimiterMode mode)
        => OutputFormatters.Concise.Format(PairOf(label, value), Preset(mode));

    [Theory]
    [InlineData("neto\u202E")]   // right-to-left override
    [InlineData("neto\u200B")]   // zero-width space
    [InlineData("\uFEFFneto")]   // BOM / zero-width no-break space
    [InlineData("net\u00ADsalary")] // soft hyphen
    [InlineData("neto\u2060")]   // word joiner
    [InlineData("neto\u200E")]   // left-to-right mark
    [InlineData("neto\u2066")]   // left-to-right isolate
    [InlineData("neto\u061C")]   // arabic letter mark
    public void InvisibleFormatCharacters_JoinUnquotedUnderNever(string label)
    {
        var text = Concise(label, 1, StringDelimiterMode.Never);

        Assert.Equal($"{label} 1", text);
        Assert.DoesNotContain("'", text, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("neto\u202E")]
    [InlineData("neto\u200B")]
    [InlineData("\uFEFFneto")]
    [InlineData("net\u00ADsalary")]
    [InlineData("neto\u2060")]
    public void InvisibleFormatCharacters_AreQuotedUnderWhenNeeded(string label)
    {
        var text = Concise(label, 1, StringDelimiterMode.WhenNeeded);
        Assert.Equal($"'{label}' 1", text);
    }

    [Fact]
    public void InvisibleFormatCharacters_AreQuotedUnderAlways()
        => Assert.Equal("'neto\u202E' 1", Concise("neto\u202E", 1, StringDelimiterMode.Always));

    [Fact]
    public void InvisibleFormatCharacters_StayQuotedInNestedPairBlocks()
    {
        var spaced = Preset(StringDelimiterMode.WhenNeeded) with { RootOutputSpacing = 1 };
        var nested = OutputFormatters.Concise.Format(
            KatLangEngine.Run("(('name', 'x'), ('a\u200B', 1, 'b', 2))"), spaced);
        Assert.Equal("name x\n  'a\u200B' 1\n  b 2", nested);
    }

    // ── Surrogate handling ────────────────────────────────────────────────────

    [Fact]
    public void UnpairedSurrogates_AreQuotedUnderWhenNeeded()
    {
        var text = OutputFormatters.Concise.Format(PairOf("\uD800x", 1), Preset(StringDelimiterMode.WhenNeeded));
        Assert.Equal("'\uD800x' 1", text);
    }

    [Fact]
    public void UnpairedSurrogates_JoinUnquotedUnderNever()
    {
        var text = OutputFormatters.Concise.Format(PairOf("\uD800x", 1), Preset(StringDelimiterMode.Never));
        Assert.Equal("\uD800x 1", text);
    }

    [Fact]
    public void WellFormedSurrogatePairs_AreOrdinarySafeContent()
    {
        // Emoji is a well-formed pair: no delimiters needed, joins like any
        // other safe token.
        Assert.Equal("😀 1", Concise("😀", 1, StringDelimiterMode.WhenNeeded));
        Assert.Equal("😀 1", Concise("😀", 1, StringDelimiterMode.Never));
        Assert.Equal("'😀' 1", Concise("😀", 1, StringDelimiterMode.Always));
    }

    // ── Digit-separator grammar in numeric-looking detection ─────────────────

    [Theory]
    [InlineData("1_000", "'1_000' 1")]        // valid KatLang number literal shape
    [InlineData("1__0", "'1__0' 1")]          // underscore runs between digits are lexical
    [InlineData("1_000.5", "'1_000.5' 1")]
    [InlineData("1_0e5", "'1_0e5' 1")]
    [InlineData("-1_000", "'-1_000' 1")]
    public void DigitSeparatorStrings_AreNumericLookingUnderWhenNeeded(string label, string expected)
        => Assert.Equal(expected, Concise(label, 1, StringDelimiterMode.WhenNeeded));

    [Fact]
    public void DigitSeparatorStrings_JoinUnquotedUnderNever()
        => Assert.Equal("1_000 1", Concise("1_000", 1, StringDelimiterMode.Never));

    [Theory]
    [InlineData("1_", "1_ 1")]      // trailing underscore: not a number literal
    [InlineData("_1000", "_1000 1")] // leading underscore: an identifier shape
    [InlineData("1_000x", "1_000x 1")]
    public void NonNumericSeparatorShapes_StayRawAndSafe(string label, string expected)
        => Assert.Equal(expected, Concise(label, 1, StringDelimiterMode.WhenNeeded));

    [Theory]
    [InlineData("\uFF11\uFF12\uFF13")] // fullwidth digits
    [InlineData("\u0661\u0662\u0663")] // arabic-indic digits
    public void UnicodeDecimalDigits_AreNotNumericLooking(string label)
    {
        // Canonical atom text is ASCII; non-ASCII digit text is ordinary label
        // content and stays raw (and joinable) under every mode.
        Assert.Equal($"{label} 1", Concise(label, 1, StringDelimiterMode.WhenNeeded));
        Assert.Equal($"{label} 1", Concise(label, 1, StringDelimiterMode.Never));
    }

    // ── Readable shares the same policy ──────────────────────────────────────

    [Fact]
    public void Readable_QuotesInvisibleContentTheSameWay()
    {
        var text = OutputFormatters.Readable.Format(
            PairOf("neto\u200B", 1), Preset(StringDelimiterMode.WhenNeeded));
        Assert.Equal("('neto\u200B', 1)", text);
    }

    // ── Content is never altered ─────────────────────────────────────────────

    [Fact]
    public void InvisibleContent_IsPreservedVerbatim()
    {
        foreach (var mode in new[] { StringDelimiterMode.Never, StringDelimiterMode.WhenNeeded, StringDelimiterMode.Always })
        {
            var text = Concise("a\u202Eb", 1, mode);
            Assert.Contains("a\u202Eb", text, StringComparison.Ordinal);
        }
    }
}
