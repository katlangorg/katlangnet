using System.Runtime.CompilerServices;
using System.Text;
using KatLang.Formatting;
using Stats = KatLang.Formatting.StructuredLayoutRenderer.LayoutWorkStatistics;

namespace KatLang.Tests.Formatting;

/// <summary>
/// Security finding F4: string classification during Readable/Concise layout
/// (quoting, token safety, line breaks) must cost work bounded per rendering
/// call — independent of how many times a string is referenced and of how many
/// distinct strings defeat the bounded identity cache — while ordinary output
/// stays byte-identical and budget exhaustion only ever selects a conservative,
/// delimited layout. Work is asserted through the layout engine's internal
/// <see cref="Stats"/> observation, never through elapsed time.
/// </summary>
public class StringClassificationWorkTests
{
    private const int References = 100_000;
    private const int MillionUnits = 1_000_000;
    private const string LimitPrefix = "Display output limit of";

    private static RunResult.Success SuccessOf(Result value)
        => new(new Algorithm.User(null, [], [], [], []), value, []);

    private static Result Seq(params Result[] items) => Result.SequenceValue.TakeOwnership(items);

    private static Result Str(string text) => new Result.Str(text);

    private static Result Num(int value) => new Result.Atom(value);

    private static string Ch(int code) => ((char)code).ToString();

    private static OutputFormatter FormatterOf(bool concise)
        => concise ? OutputFormatters.Concise : OutputFormatters.Readable;

    /// <summary>
    /// Renders one row through the layout engine with work observation. With
    /// the default budget the result must agree exactly with the public
    /// formatter contract (text on success, overflow flag either way).
    /// </summary>
    private static (bool Completed, string Written, Stats Stats) Observe(
        Result value,
        OutputFormattingOptions options,
        bool concise,
        long? budget = null)
    {
        var stats = new Stats();
        var writer = new BoundedDisplayWriter(options.EffectiveDisplayLimit(DisplayOptions.Default.MaxDisplayLength));
        var completed = StructuredLayoutRenderer.WriteRows(
            [value], DisplayOptions.Default, options, concise, writer, stats, budget);

        Assert.Equal(!completed, writer.LimitExceeded);
        Assert.True(stats.ChargedCodeUnits <= stats.ClassificationBudget);
        if (budget is null)
        {
            var rendering = FormatterOf(concise).RenderDisplay(SuccessOf(value), options);
            Assert.Equal(rendering.LimitExceeded, !completed);
            if (completed)
                Assert.Equal(rendering.Text, writer.ToString());
        }

        return (completed, writer.ToString(), stats);
    }

    private static string Lines(params string[] lines) => string.Join("\n", lines);

    // ---------------------------------------------------------------- T1

    public static TheoryData<bool, StringDelimiterMode, int, int> SharedStringCases()
    {
        var data = new TheoryData<bool, StringDelimiterMode, int, int>();
        foreach (var concise in new[] { false, true })
        foreach (var mode in new[] { StringDelimiterMode.Never, StringDelimiterMode.WhenNeeded, StringDelimiterMode.Always })
        foreach (var limit in new[] { 0, 16 })
        foreach (var spacing in new[] { 0, 1 })
            data.Add(concise, mode, limit, spacing);
        return data;
    }

    [Theory]
    [MemberData(nameof(SharedStringCases))]
    public void HundredThousandReferencesToOneMillionUnitString_ClassifyAtMostOnce(
        bool concise, StringDelimiterMode mode, int limit, int spacing)
    {
        var shared = new Result.Str(new string('x', MillionUnits));
        var items = new Result[References];
        Array.Fill(items, shared);
        var value = Result.SequenceValue.TakeOwnership(items);
        var options = new OutputFormattingOptions
        {
            NewLine = "\n",
            MaxDisplayLength = limit,
            StringDelimiters = mode,
            RootOutputSpacing = spacing,
        };

        var rendering = FormatterOf(concise).RenderDisplay(SuccessOf(value), options);
        Assert.True(rendering.LimitExceeded);
        Assert.Equal(limit == 0 ? "" : "…", rendering.Text);

        var (completed, _, stats) = Observe(value, options, concise);
        Assert.False(completed);

        // Before F4 the concise block gate alone inspected about
        // references × length = 10^11 code units. Now one string costs at most
        // one classification, and every other reference is a cache hit or is
        // rejected on its raw length before any scan.
        Assert.True(stats.LongClassifications <= 1, $"classified {stats.LongClassifications} times");
        Assert.True(stats.ScanInputCodeUnits <= MillionUnits, $"scan inputs {stats.ScanInputCodeUnits} code units");
        Assert.Equal(0, stats.UnclassifiedResults);
        Assert.Equal(0, stats.RowRestarts);
        if (concise && spacing > 0)
            Assert.True(stats.CacheHits >= References - 1, $"only {stats.CacheHits} cache hits");
    }

    // ---------------------------------------------------------------- T2

    [Fact]
    public void DistinctWrappersOfOneString_ShareOneClassification()
    {
        var text = new string('y', 200_000);
        var items = new Result[References];
        for (var i = 0; i < items.Length; i++)
            items[i] = new Result.Str(text);
        Assert.NotSame(items[0], items[1]);

        var options = new OutputFormattingOptions { NewLine = "\n", MaxDisplayLength = 16 };
        var (completed, _, stats) = Observe(Result.SequenceValue.TakeOwnership(items), options, concise: true);

        Assert.False(completed);
        Assert.Equal(1, stats.LongClassifications);
        Assert.True(stats.CacheHits >= References - 1, $"only {stats.CacheHits} cache hits");
        Assert.True(stats.ScanInputCodeUnits <= text.Length);
    }

    [Fact]
    public void EqualContentInDistinctStringObjects_IsCachedByIdentityNotContent()
    {
        // Equal content in DIFFERENT string objects must not share an entry: a
        // content-keyed cache would hash the whole string on every lookup.
        const int count = 10;
        var items = new Result[count * 2];
        for (var i = 0; i < count; i++)
        {
            var text = new string('e', 100);
            items[2 * i] = new Result.Str(text);
            items[(2 * i) + 1] = new Result.Str(text);
        }

        var options = new OutputFormattingOptions { NewLine = "\n", MaxDisplayLength = 16 };
        var (_, _, stats) = Observe(Result.SequenceValue.TakeOwnership(items), options, concise: true);

        Assert.Equal(count, stats.LongClassifications);
        Assert.True(stats.CacheHits >= count);
    }

    // ---------------------------------------------------------------- T3

    [Fact]
    public void MoreDistinctLongStringsThanTheCacheHolds_StayWithinTheBudget()
    {
        const int length = 50_000;
        var distinct = (DelimitedStringTextPolicy.FactsCacheCapacity * 2) + 3;
        var strings = new string[distinct];
        for (var k = 0; k < distinct; k++)
            strings[k] = new string('z', length);

        // Cyclic references: after the cache fills, every remaining string is
        // an uncached miss on every encounter.
        var items = new Result[References];
        for (var i = 0; i < items.Length; i++)
            items[i] = new Result.Str(strings[i % distinct]);
        var value = Result.SequenceValue.TakeOwnership(items);

        foreach (var concise in new[] { false, true })
        {
            var options = new OutputFormattingOptions { NewLine = "\n", MaxDisplayLength = 16 };
            var (completed, _, stats) = Observe(value, options, concise);

            Assert.False(completed);
            Assert.True(stats.ChargedCodeUnits <= stats.ClassificationBudget);
            Assert.True(
                stats.ScanInputCodeUnits <= stats.ClassificationBudget,
                $"scan inputs {stats.ScanInputCodeUnits} of a {stats.ClassificationBudget} budget (references × length = {(long)References * length})");
            Assert.True(stats.LongClassifications <= (stats.ClassificationBudget / length) + 1);
            if (concise)
            {
                Assert.True(stats.ClassificationExhausted);
                Assert.Equal(1, stats.RowRestarts);
            }
        }
    }

    [Fact]
    public void WidthProbesOverManyDistinctStrings_StayWithinTheBudget()
    {
        // Zero root spacing makes the concise root gate ask, for every pair
        // block child, whether its predecessor renders as one line: a space
        // join and a width-capped measurement of a sequence whose first string
        // is shorter than the line width, so both need its classification.
        // The predecessors cycle through three times more distinct strings than
        // the cache holds, so almost every check is a miss.
        const int length = 6_000;
        const int pairs = 20_000;
        var pool = new string[DelimitedStringTextPolicy.FactsCacheCapacity * 3];
        for (var k = 0; k < pool.Length; k++)
            pool[k] = new string('w', length);

        var pairBlock = Seq(Str("a"), Num(1), Str("b"), Num(2));
        var items = new Result[pairs * 2];
        for (var i = 0; i < pairs; i++)
        {
            var text = pool[i % pool.Length];
            items[2 * i] = Seq(Str(text), Str(text));
            items[(2 * i) + 1] = pairBlock;
        }

        var options = new OutputFormattingOptions
        {
            NewLine = "\n",
            MaxDisplayLength = 16,
            RootOutputSpacing = 0,
            PreferredLineWidth = OutputFormattingOptions.MaxSupportedPreferredLineWidth,
        };
        var (completed, _, stats) = Observe(Result.SequenceValue.TakeOwnership(items), options, concise: true);

        Assert.False(completed);
        Assert.True(stats.ClassificationExhausted);
        Assert.Equal(1, stats.RowRestarts);
        Assert.True(
            stats.ScanInputCodeUnits <= stats.ClassificationBudget + 1_000_000,
            $"scan inputs {stats.ScanInputCodeUnits} code units (pairs × length = {(long)pairs * length})");
    }

    // ---------------------------------------------------------------- T4

    [Theory]
    [InlineData(0)]
    [InlineData(16)]
    public void ReadablePairRun_RejectsOversizedLabelsBeforeAnyScan(int limit)
    {
        var label = new Result.Str(new string('k', MillionUnits));
        var items = new Result[References];
        for (var i = 0; i < items.Length; i += 2)
        {
            items[i] = label;
            items[i + 1] = Num(1);
        }

        var options = new OutputFormattingOptions { NewLine = "\n", MaxDisplayLength = limit };
        var (completed, _, stats) = Observe(Result.SequenceValue.TakeOwnership(items), options, concise: false);

        Assert.False(completed);
        Assert.Equal(0, stats.LongClassifications);
        Assert.Equal(0, stats.ScanInputCodeUnits);
        Assert.True(stats.LengthRefusals >= 1);
    }

    [Fact]
    public void ReadablePairRun_ClassifiesARepeatedLabelOnce()
    {
        var label = new string('k', 80);
        const int pairs = 1_000;
        var childItems = new Result[pairs * 2];
        for (var i = 0; i < pairs; i++)
        {
            childItems[2 * i] = Str(label);
            childItems[(2 * i) + 1] = Num(i % 10);
        }

        var child = Result.SequenceValue.TakeOwnership(childItems);
        var value = Seq(child, child);
        var (completed, written, stats) = Observe(value, new OutputFormattingOptions { NewLine = "\n" }, concise: false);

        var expected = new StringBuilder("(\n");
        for (var c = 0; c < 2; c++)
        {
            expected.Append("  (\n");
            for (var i = 0; i < pairs; i++)
                expected.Append("    ").Append(label).Append(", ").Append(i % 10).Append(i < pairs - 1 ? ",\n" : "\n");
            expected.Append(c == 0 ? "  ),\n" : "  )\n");
        }

        expected.Append(')');

        Assert.True(completed);
        Assert.Equal(expected.ToString(), written);
        Assert.Equal(1, stats.LongClassifications);
    }

    [Theory]
    [InlineData(0x000D)]
    [InlineData(0x000A)]
    [InlineData(0x0085)]
    [InlineData(0x2028)]
    [InlineData(0x2029)]
    public void ReadablePairRun_LabelsWithLineBreaksKeepOneItemPerLine(int breakChar)
    {
        foreach (var padding in new[] { "", new string('p', DelimitedStringTextPolicy.LongStringLength) })
        {
            var labelText = padding + "a" + Ch(breakChar) + "b";
            var child = Seq(Str(labelText), Num(1), Str("c"), Num(2));
            var (completed, written, _) = Observe(Seq(child, child), new OutputFormattingOptions { NewLine = "\n" }, concise: false);

            // CR and LF cannot be single-quoted, so they stay raw; the Unicode
            // separators are whitespace and get quoted. Either way the label
            // breaks the line, so no pair line is formed.
            var rendered = breakChar is 0x000D or 0x000A ? labelText : "'" + labelText + "'";
            var block = Lines("    " + rendered + ",", "    1,", "    c,", "    2");
            Assert.True(completed);
            Assert.Equal(Lines("(", "  (", block, "  ),", "  (", block, "  )", ")"), written);
        }
    }

    [Fact]
    public void ReadablePairRun_OrdinaryPairsAreUnchanged()
    {
        var value = Seq(Seq(Str("a"), Num(1), Str("b"), Num(2)), Seq(Str("c"), Num(3), Str("d"), Num(4)));
        var text = OutputFormatters.Readable.Format(SuccessOf(value), new OutputFormattingOptions { NewLine = "\n" });

        Assert.Equal(Lines("(", "  (", "    a, 1,", "    b, 2", "  ),", "  (", "    c, 3,", "    d, 4", "  )", ")"), text);
    }

    // ---------------------------------------------------------------- T5

    [Fact]
    public void ConciseRootGate_SharedPairChildIsClassifiedOnce()
    {
        // Every root child shares two mid-length labels that pass the
        // raw-length checks, so the zero-spacing gate classifies them for each
        // of the ~100,000 children (pair-block check, predecessor line check,
        // successor block check) and never finds an anchor: each child's
        // neighbours are block-shaped children themselves.
        var label = new string('w', 5_000);
        var child = Seq(Str(label), Num(1), Str(label), Num(2));
        var items = new Result[References];
        Array.Fill(items, child);
        items[0] = Str("h");

        var options = new OutputFormattingOptions
        {
            NewLine = "\n",
            MaxDisplayLength = 16,
            RootOutputSpacing = 0,
            PreferredLineWidth = OutputFormattingOptions.MaxSupportedPreferredLineWidth,
        };
        var (completed, _, stats) = Observe(Result.SequenceValue.TakeOwnership(items), options, concise: true);

        Assert.False(completed);
        Assert.Equal(1, stats.LongClassifications);
        Assert.True(stats.CacheHits >= References, $"only {stats.CacheHits} cache hits");
        Assert.True(stats.ScanInputCodeUnits <= label.Length + 10_000, $"scan inputs {stats.ScanInputCodeUnits}");
    }

    public static TheoryData<StringDelimiterMode, string> FallbackModes()
        => new()
        {
            { StringDelimiterMode.Never, "" },
            { StringDelimiterMode.WhenNeeded, "" },
            { StringDelimiterMode.Always, "'" },
        };

    [Theory]
    [MemberData(nameof(FallbackModes))]
    public void ConciseBudgetExhaustion_KeepsDelimitersAndCompletes(StringDelimiterMode mode, string quote)
    {
        var first = new string('l', 70);
        var second = new string('m', 70);
        var value = Seq(Str("title"), Seq(Str(first), Num(1), Str(second), Num(2)), Str("end"));
        var options = new OutputFormattingOptions { NewLine = "\n", StringDelimiters = mode };
        string Q(string text) => quote + text + quote;

        // Normal classification: the safe pair child is an indented pair block.
        var (normalCompleted, normal, normalStats) = Observe(value, options, concise: true);
        Assert.True(normalCompleted);
        Assert.Equal(
            Lines(Q("title"), "  " + Q(first) + " 1", "  " + Q(second) + " 2", Q("end")),
            normal);
        Assert.False(normalStats.ClassificationExhausted);

        // No budget: the long labels cannot be PROVEN safe, so the child keeps
        // its parentheses and one item per line. The output is complete — the
        // budget never manufactures an overflow — and string content is exact.
        var (completed, fallback, stats) = Observe(value, options, concise: true, budget: 0);
        Assert.True(completed);
        Assert.Equal(
            Lines(Q("title"), "(", "  " + Q(first) + ",", "  1,", "  " + Q(second) + ",", "  2", ")", Q("end")),
            fallback);
        Assert.True(stats.ClassificationExhausted);
        Assert.Equal(0, stats.LongClassifications);
        Assert.Equal(0, stats.ChargedCodeUnits);
    }

    [Fact]
    public void ConciseBudgetExhaustion_MidRow_ReRendersTheRowConsistently()
    {
        // 64 distinct long labels fill the identity cache during the root
        // space-join check; the pair child's long label is then classified
        // (budget permitting) WITHOUT being cached, so the zero-spacing root
        // gate admits a paren-hidden root block anchored by that pair block.
        // Later in the same row the label can no longer be classified. Without
        // a re-render the anchor would silently become a delimited child at
        // root level, and the paren-less root block would read exactly like
        // several independent root rows. The row is re-rendered instead.
        const int labelLength = 70;
        var cacheFillers = new Result[DelimitedStringTextPolicy.FactsCacheCapacity];
        var fillerTexts = new string[cacheFillers.Length];
        for (var k = 0; k < cacheFillers.Length; k++)
        {
            fillerTexts[k] = new string('s', labelLength - 2) + (char)('A' + (k / 26)) + (char)('a' + (k % 26));
            cacheFillers[k] = Str(fillerTexts[k]);
        }

        var anchorLabel = new string('L', labelLength);
        var value = Seq([.. cacheFillers, Str("h"), Seq(Str(anchorLabel), Num(1), Str("b"), Num(2)), Str("t")]);
        var options = new OutputFormattingOptions
        {
            NewLine = "\n",
            RootOutputSpacing = 0,
            PreferredLineWidth = OutputFormattingOptions.MaxSupportedPreferredLineWidth,
        };

        // Default budget: the gate's anchor really renders as an indented pair block.
        var (completed, written, stats) = Observe(value, options, concise: true);
        Assert.True(completed);
        Assert.Equal(Lines([.. fillerTexts, "h", "  " + anchorLabel + " 1", "  b 2", "t"]), written);
        Assert.Equal(0, stats.RowRestarts);

        // Budget for exactly the fillers plus one anchor classification.
        var budget = (long)labelLength * (cacheFillers.Length + 1);
        var (tightCompleted, tight, tightStats) = Observe(value, options, concise: true, budget);
        Assert.True(tightCompleted);
        Assert.True(tightStats.ClassificationExhausted);
        Assert.Equal(1, tightStats.RowRestarts);
        Assert.Equal(
            Lines(
            [
                "(",
                .. fillerTexts.Select(text => "  " + text + ","),
                "  h,",
                "  (",
                "    " + anchorLabel + ",",
                "    1,",
                "    b,",
                "    2",
                "  ),",
                "  t",
                ")",
            ]),
            tight);
    }

    // ---------------------------------------------------------------- T6

    [Theory]
    [InlineData(StringDelimiterMode.Never)]
    [InlineData(StringDelimiterMode.WhenNeeded)]
    [InlineData(StringDelimiterMode.Always)]
    public void ClassificationThreshold_PreservesExactQuotingUnderExhaustion(StringDelimiterMode mode)
    {
        foreach (var length in new[] { 63, 64, 65 })
        foreach (var suffix in new[] { "label", "'", " ", Ch(0xD800), Ch(0xD83D) + Ch(0xDE00), "\r", "\n", Ch(0x0085), Ch(0x2028), Ch(0x2029) })
        {
            var text = new string('x', length - suffix.Length) + suffix;
            var needsQuotes = suffix is not "label" && suffix != Ch(0xD83D) + Ch(0xDE00);
            var canQuote = suffix is not ("'" or "\r" or "\n");
            var quoted = canQuote && (mode == StringDelimiterMode.Always
                || (mode == StringDelimiterMode.WhenNeeded && needsQuotes));
            var expected = quoted ? "'" + text + "'" : text;

            // An exhausted optional classifier must still emit the exact
            // string token, including unquotable content and surrogate code units.
            var policy = new DelimitedStringTextPolicy(mode, classificationBudget: 0);
            Assert.Equal(length < DelimitedStringTextPolicy.LongStringLength, policy.TryClassify(text, out _));
            foreach (var limit in new[] { 0, 1, 16, expected.Length - 1, expected.Length, expected.Length + 1 })
            {
                var writer = new BoundedDisplayWriter(limit);
                var completed = policy.Append(text, writer);
                Assert.Equal(limit >= expected.Length, completed);
                Assert.Equal(!completed, writer.LimitExceeded);
                if (completed)
                    Assert.Equal(expected, writer.ToString());
            }
        }
    }

    private sealed record FactsCase(string Text, bool TokenSafeNever, bool TokenSafeQuoted, bool NeedsQuotes, bool CanQuote, bool LineBreak);

    private static IEnumerable<FactsCase> FactsCases()
    {
        // TokenSafeQuoted is the same for WhenNeeded and Always: a delimited
        // token is self-bounding, but whitespace, controls, commas, format
        // characters, unpaired surrogates, and unquotable content stay unsafe.
        yield return new("neto", true, true, false, true, false);
        yield return new("net_salary", true, true, false, true, false);
        yield return new("1_000", false, true, true, true, false);
        yield return new("-1.5e3", false, true, true, true, false);
        yield return new("NaN", false, true, true, true, false);
        yield return new("-Infinity", false, true, true, true, false);
        yield return new("", false, true, true, true, false);
        yield return new("a b", false, false, true, true, false);
        yield return new("a\tb", false, false, true, true, false);
        yield return new("a,b", false, false, true, true, false);
        yield return new("(p)", false, true, true, true, false);
        yield return new("[q]", false, true, true, true, false);
        yield return new("it's", false, false, true, false, false);
        yield return new(Ch(0x200B) + "zw", false, false, true, true, false);
        yield return new("a" + Ch(0x202E) + "b", false, false, true, true, false);
        yield return new("a" + Ch(0xD83D) + Ch(0xDE00) + "b", true, true, false, true, false);
        yield return new("a" + Ch(0xD800) + "b", false, false, true, true, false);
        yield return new("a" + Ch(0xDC00) + "b", false, false, true, true, false);
        yield return new("a\rb", false, false, true, false, true);
        yield return new("a\nb", false, false, true, false, true);
        yield return new("a" + Ch(0x0085) + "b", false, false, true, true, true);
        yield return new("a" + Ch(0x2028) + "b", false, false, true, true, true);
        yield return new("a" + Ch(0x2029) + "b", false, false, true, true, true);
    }

    [Fact]
    public void ClassificationFacts_MatchTheDelimiterAndUnicodeRules_ForShortAndCachedLongStrings()
    {
        var padding = new string('p', DelimitedStringTextPolicy.LongStringLength);
        foreach (var mode in new[] { StringDelimiterMode.Never, StringDelimiterMode.WhenNeeded, StringDelimiterMode.Always })
        {
            var policy = new DelimitedStringTextPolicy(mode, DelimitedStringTextPolicy.DefaultClassificationBudget(0));
            foreach (var sample in FactsCases())
            {
                // Letter padding preserves every character-class fact; the
                // numeric, atom-spelling and empty cases are whole-string rules
                // and are checked short only (padding makes them plain text).
                var wholeStringRule = sample.Text.Length == 0 || char.IsAsciiDigit(sample.Text[^1]) || sample.Text is "NaN" or "-Infinity";
                var texts = wholeStringRule ? [sample.Text] : new[] { sample.Text, padding + sample.Text, sample.Text + padding };
                foreach (var text in texts)
                {
                    var usesQuotes = mode switch
                    {
                        StringDelimiterMode.Always => sample.CanQuote,
                        StringDelimiterMode.WhenNeeded => sample.NeedsQuotes && sample.CanQuote,
                        _ => false,
                    };
                    var expectedSafe = mode == StringDelimiterMode.Never ? sample.TokenSafeNever : sample.TokenSafeQuoted;

                    // First call computes (and caches long strings); second is the cached answer.
                    for (var call = 0; call < 2; call++)
                    {
                        Assert.True(policy.TryClassify(text, out var facts));
                        var label = $"{mode} '{Escape(text)}' call {call}";
                        Assert.True(expectedSafe == facts.IsTokenSafe, $"IsTokenSafe {label}");
                        Assert.True(usesQuotes == facts.UsesDelimiters, $"UsesDelimiters {label}");
                        Assert.True(sample.LineBreak == facts.ContainsLineBreak, $"ContainsLineBreak {label}");
                        Assert.Equal(text.Length + (usesQuotes ? 2 : 0), facts.TokenLength);
                    }
                }
            }

            Assert.True(policy.CacheHits > 0);
        }
    }

    private static string Escape(string text)
        => string.Concat(text.Take(12).Select(c => c is >= ' ' and <= '~' ? c.ToString() : $"\\x{(int)c:X4}"));

    [Theory]
    [InlineData(StringDelimiterMode.Never)]
    [InlineData(StringDelimiterMode.WhenNeeded)]
    [InlineData(StringDelimiterMode.Always)]
    public void LongAmbiguousStrings_KeepConciseParentheses_LikeShortOnes(StringDelimiterMode mode)
    {
        // The long (cached) path makes the same structural decision as the
        // short path: one unsafe string keeps the root parentheses.
        var padding = new string('p', DelimitedStringTextPolicy.LongStringLength);
        foreach (var unsafeText in new[] { "a b", "a,b", "a" + Ch(0x200B) + "b", "a" + Ch(0xD800) + "b" })
        {
            foreach (var text in new[] { unsafeText, padding + unsafeText })
            {
                var value = Seq(Str("ok"), Str(text), Num(1));
                var options = new OutputFormattingOptions { NewLine = "\n", StringDelimiters = mode, PreferredLineWidth = 1 };
                var (completed, written, _) = Observe(value, options, concise: true);

                Assert.True(completed);
                Assert.StartsWith("(", written, StringComparison.Ordinal);
                Assert.EndsWith(")", written, StringComparison.Ordinal);
                Assert.Contains(text, written, StringComparison.Ordinal);
            }
        }
    }

    // ---------------------------------------------------------------- T7

    public static TheoryData<bool, bool> SweepCases()
        => new() { { false, false }, { false, true }, { true, false }, { true, true } };

    [Theory]
    [MemberData(nameof(SweepCases))]
    public void DisplayLimitSweep_IsExactWithAndWithoutClassificationBudget(bool concise, bool exhaustBudget)
    {
        var first = new string('l', 70);
        var second = new string('m', 70) + " sp";
        var value = Seq(Str("title"), Seq(Str(first), Num(1), Str(second), Num(2)), Str("end"));
        var budget = exhaustBudget ? 0 : (long?)null;
        var unlimited = new OutputFormattingOptions { NewLine = "\n" };
        var (fullCompleted, full, fullStats) = Observe(value, unlimited, concise, budget);
        Assert.True(fullCompleted);
        Assert.Equal(exhaustBudget, fullStats.ClassificationExhausted);
        Assert.Contains(first, full, StringComparison.Ordinal);
        Assert.Contains(second, full, StringComparison.Ordinal);

        foreach (var limit in new[] { 0, 1, 16, full.Length - 1, full.Length, full.Length + 1 })
        {
            var options = unlimited with { MaxDisplayLength = limit };
            var (completed, written, _) = Observe(value, options, concise, budget);
            Assert.Equal(limit >= full.Length, completed);
            if (completed)
                Assert.Equal(full, written);

            if (budget is null)
            {
                var rendering = FormatterOf(concise).RenderDisplay(SuccessOf(value), options);
                Assert.Equal(!completed, rendering.LimitExceeded);
                Assert.True(rendering.Text.Length <= limit);
                if (completed)
                    Assert.Equal(full, rendering.Text);
                else if (limit == 0)
                    Assert.Equal("", rendering.Text);
                else if (limit < LimitPrefix.Length)
                    Assert.Equal("…", rendering.Text);
                else
                    Assert.StartsWith(LimitPrefix, rendering.Text, StringComparison.Ordinal);
            }
        }
    }

    // ---------------------------------------------------------------- T8 / isolation

    [Theory]
    [InlineData("\n", 0)]
    [InlineData("\n", 1)]
    [InlineData("\r\n", 0)]
    [InlineData("\r\n", 1)]
    public void BudgetExhaustion_InLaterRow_PreservesEarlierRowsAndExactDisplayCharging(string newLine, int spacing)
    {
        const int length = 70;
        var labels = Enumerable.Range(0, DelimitedStringTextPolicy.FactsCacheCapacity)
            .Select(i => new string('f', length - 2) + (char)('A' + (i / 26)) + (char)('a' + (i % 26))).ToArray();
        var firstRow = Result.ListValue.TakeOwnership(labels.Select(Str).ToArray());
        var uncached = new string('z', length);
        var secondRow = Seq(Str(uncached), Num(1), Str(uncached), Num(2));
        Result[] rows = [firstRow, secondRow, Str("tail")];
        var options = new OutputFormattingOptions
        {
            NewLine = newLine,
            RootOutputSpacing = spacing,
            PreferredLineWidth = OutputFormattingOptions.MaxSupportedPreferredLineWidth,
        };
        var separator = string.Concat(Enumerable.Repeat(newLine, spacing + 1));
        var expected = "[" + string.Join(", ", labels) + "]" + separator
            + string.Join(newLine, "(", "  " + uncached + ",", "  1,", "  " + uncached + ",", "  2", ")")
            + separator + "tail";

        foreach (var limit in new[] { 0, 1, 16, expected.Length - 1, expected.Length, expected.Length + 1 })
        {
            var writer = new BoundedDisplayWriter(limit);
            var stats = new Stats();
            var completed = StructuredLayoutRenderer.WriteRows(rows, DisplayOptions.Default, options,
                concise: true, writer, stats, classificationBudget: length * (labels.Length + 1));

            Assert.Equal(limit >= expected.Length, completed);
            Assert.Equal(!completed, writer.LimitExceeded);
            if (completed)
            {
                Assert.Equal(expected, writer.ToString());
                Assert.True(stats.ClassificationExhausted);
                Assert.Equal(1, stats.RowRestarts);
                Assert.Equal(length * (labels.Length + 1), stats.ChargedCodeUnits);
            }
        }
    }

    [Fact]
    public void ConcurrentRenderings_DoNotShareClassificationState()
    {
        var shared = new string('c', 200);
        var value = Seq(Str("head"), Seq(Str(shared), Num(1), Str(shared + " x"), Num(2)), Str(shared));
        var optionSets = new[]
        {
            new OutputFormattingOptions { NewLine = "\n", StringDelimiters = StringDelimiterMode.Never },
            new OutputFormattingOptions { NewLine = "\n", StringDelimiters = StringDelimiterMode.WhenNeeded },
            new OutputFormattingOptions { NewLine = "\n", StringDelimiters = StringDelimiterMode.Always },
            new OutputFormattingOptions { NewLine = "\n", PreferredLineWidth = 10, MaxDisplayLength = 300 },
        };
        var formatters = new[] { OutputFormatters.Readable, OutputFormatters.Concise };
        var success = SuccessOf(value);
        var expected = new string[formatters.Length, optionSets.Length];
        for (var f = 0; f < formatters.Length; f++)
        for (var o = 0; o < optionSets.Length; o++)
            expected[f, o] = formatters[f].Format(success, optionSets[o]);

        Parallel.For(0, 256, iteration =>
        {
            var f = iteration % formatters.Length;
            var o = (iteration / formatters.Length) % optionSets.Length;
            Assert.Equal(expected[f, o], formatters[f].Format(success, optionSets[o]));
        });
    }

    [Fact]
    public void Rendering_RetainsNoReferenceToClassifiedStrings()
    {
        var weak = RenderAndForget();
        GC.Collect();
        GC.WaitForPendingFinalizers();
        GC.Collect();

        Assert.False(weak.TryGetTarget(out _));
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static WeakReference<string> RenderAndForget()
    {
        var text = new string('r', 10_000);
        var value = Seq(Str(text), Str(text), Num(1));
        foreach (var formatter in new[] { OutputFormatters.Readable, OutputFormatters.Concise })
            _ = formatter.Format(SuccessOf(value), new OutputFormattingOptions { NewLine = "\n" });
        return new WeakReference<string>(text);
    }

    [Fact]
    public void OrdinaryShortStrings_UseNoCacheAndNoBudget()
    {
        var value = Seq(
            Str("Salary report"),
            Seq(Str("bruto"), Num(2000), Str("tax"), Num(400), Str("neto"), Num(1600)),
            Str("Employees"),
            Seq(Seq(Str("Anna"), Num(1200)), Seq(Str("Bob"), Num(1300))));

        foreach (var concise in new[] { false, true })
        {
            var (completed, _, stats) = Observe(value, new OutputFormattingOptions { NewLine = "\n" }, concise);
            Assert.True(completed);
            Assert.Equal(0, stats.ChargedCodeUnits);
            Assert.Equal(0, stats.LongClassifications);
            Assert.Equal(0, stats.CacheHits);
            Assert.False(stats.ClassificationExhausted);
        }
    }

    [Fact]
    public void DefaultBudget_IsBaseAllowancePlusLimitMultiple()
    {
        Assert.Equal(
            DelimitedStringTextPolicy.ClassificationBaseAllowance,
            DelimitedStringTextPolicy.DefaultClassificationBudget(0));
        Assert.Equal(
            DelimitedStringTextPolicy.ClassificationBaseAllowance
                + (DelimitedStringTextPolicy.ClassificationLimitMultiplier * EvaluationLimits.MaxSupportedDisplayLength),
            DelimitedStringTextPolicy.DefaultClassificationBudget(EvaluationLimits.MaxSupportedDisplayLength));
    }
}
