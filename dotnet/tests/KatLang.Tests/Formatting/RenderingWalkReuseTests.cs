using System.Globalization;
using System.Numerics;
using KatLang.Formatting;
using KatLang.Rendering;

namespace KatLang.Tests.Formatting;

/// <summary>
/// The rendering pipeline walks a value as few times as its layout needs, and that is
/// implementation-only allocation work: it must not change a single character of output. The
/// readable and concise layouts measure each structured item through the shared renderer before
/// deciding its layout; an item that fits is written from the text its measurement kept
/// (<see cref="CappedWidthSink.Reset"/> with <c>keepText</c>), so it is walked once, not
/// measured and then rendered again. Every walk of one rendering call, canonical display rows
/// included, shares one continuation stack
/// (<see cref="ValueTextRenderer.AppendValue(Result, DisplayOptions, IStringTextPolicy, IDisplaySink, ref Stack{ValueTextRenderer.SuspendedStructure})"/>)
/// instead of allocating one per nested value. The expected texts here are written out by hand.
/// </summary>
public class RenderingWalkReuseTests
{
    private static Result Num(string literal) => new Result.Atom(Decimal128.Parse(literal, CultureInfo.InvariantCulture));

    private static Result Num(long value) => new Result.Atom(value);

    private static Result Str(string text) => new Result.Str(text);

    private static Result Seq(params Result[] items) => Result.SequenceValue.TakeOwnership(items);

    private static Result List(params Result[] items) => Result.ListValue.TakeOwnership(items);

    // One spread root row supplies every output row the value presents for the emitted count.
    private static RunResult.Success SuccessOf(Result value, int emittedCount = 1)
        => HandBuiltSuccess.OfOneSpreadRow(value, emittedCount);

    private static readonly DisplayOptions Canonical = DisplayOptions.Canonical(int.MaxValue);

    // The benchmark's NestedLists row shape: [i, [2i, [3i, i + 0.5]]].
    private static Result[] NestedRows(int count)
    {
        var rows = new Result[count];
        for (var i = 1; i <= count; i++)
            rows[i - 1] = List(Num(i), List(Num(2 * i), List(Num(3 * i), Num(i.ToString(CultureInfo.InvariantCulture) + ".5"))));
        return rows;
    }

    private static long AllocatedBy(Func<string> render)
    {
        _ = render();
        _ = render();
        var before = GC.GetAllocatedBytesForCurrentThread();
        var text = render();
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
        GC.KeepAlive(text);
        return allocated;
    }

    [Fact]
    public void MeasuringSink_KeepsExactlyTheTextItAccepted()
    {
        var sink = new CappedWidthSink();
        sink.Reset(10, keepText: true);
        Assert.True(sink.Append("ab"));
        Assert.True(sink.Append("cd".AsSpan()));
        Assert.True(sink.Append(' ', 3));
        Assert.Equal("abcd   ", sink.Text.ToString());
        Assert.Equal(3, sink.RemainingCapacity);

        // An append that crosses the cap is refused and keeps nothing; the refusal sticks.
        Assert.False(sink.Append("wxyz"));
        Assert.False(sink.Append("x"));
        Assert.Equal("abcd   ", sink.Text.ToString());

        // Reset starts a new measurement. Text longer than the first buffer is kept whole,
        // exactly up to the cap.
        sink.Reset(100, keepText: true);
        Assert.Equal(string.Empty, sink.Text.ToString());
        var text = string.Concat(Enumerable.Range(0, 20).Select(i => i.ToString("D4", CultureInfo.InvariantCulture) + ","));
        Assert.True(sink.Append(text));
        Assert.True(sink.Append('.', 100 - text.Length));
        Assert.Equal(text + new string('.', 100 - text.Length), sink.Text.ToString());
        Assert.False(sink.Append("!"));

        // Lookahead uses this same sink and only counts, even after an inline write.
        sink.Reset(10);
        Assert.True(sink.Append("ab"));
        Assert.True(sink.Text.IsEmpty);
        Assert.Equal(8, sink.RemainingCapacity);
    }

    [Fact]
    public void KeptWalkStack_IsCreatedOnceAndEmptiedAfterARefusedWalk()
    {
        Result flat = List(Num(1), Str("a b"), new Result.Bool(true));
        Result nested = List(Num(1), Seq(Num(2), List(Num(3), Seq())), Num(4));
        Stack<ValueTextRenderer.SuspendedStructure>? kept = null;

        // Scalars and flat structures need no stack.
        var writer = new BoundedDisplayWriter(int.MaxValue);
        Assert.True(ValueTextRenderer.AppendValue(Num(7), Canonical, RawStringTextPolicy.Instance, writer, ref kept));
        Assert.True(ValueTextRenderer.AppendValue(flat, Canonical, RawStringTextPolicy.Instance, writer, ref kept));
        Assert.Null(kept);
        Assert.Equal("7[1, a b, true]", writer.ToString());

        // A walk refused inside the nesting leaves its frames on the stack it created.
        var measure = new CappedWidthSink();
        measure.Reset(9);
        Assert.False(ValueTextRenderer.AppendValue(nested, Canonical, RawStringTextPolicy.Instance, measure, ref kept));
        var stack = Assert.IsType<Stack<ValueTextRenderer.SuspendedStructure>>(kept);
        Assert.NotEmpty(stack);

        // The next walk empties and reuses that stack and writes the complete text.
        writer = new BoundedDisplayWriter(int.MaxValue);
        Assert.True(ValueTextRenderer.AppendValue(nested, Canonical, RawStringTextPolicy.Instance, writer, ref kept));
        Assert.Same(stack, kept);
        Assert.Empty(stack);
        Assert.Equal("[1, (2, [3, ()]), 4]", writer.ToString());
    }

    // A list wider than the line, with items that fit inline: numbers (stored trailing zeros,
    // a negative fraction, a 71-digit integer), strings with and without a need for quotes, the
    // three empty values, a Boolean, and one value object at two positions.
    private static Result InlineItemsList()
    {
        var shared = List(Str("a b"), Str("plain"), Seq(Num(7), Num(8)));
        return List(
            List(Num(1), Num("2.50"), Num("-0.004")),
            Seq(Str("social tax"), Str("x,y"), Str(string.Empty)),
            List(Seq(), List(), new Result.Bool(true)),
            List(Num("1e70")),
            shared,
            shared);
    }

    private static readonly string Big = "1" + new string('0', 70);

    public static TheoryData<StringDelimiterMode, string> InlineItemCases() => new()
    {
        {
            StringDelimiterMode.WhenNeeded,
            "[\n" +
            "  [1, 2.50, -0.004],\n" +
            "  ('social tax', 'x,y', ''),\n" +
            "  [(), [], true],\n" +
            $"  [{Big}],\n" +
            "  ['a b', plain, (7, 8)],\n" +
            "  ['a b', plain, (7, 8)]\n" +
            "]"
        },
        {
            StringDelimiterMode.Never,
            "[\n" +
            "  [1, 2.50, -0.004],\n" +
            "  (social tax, x,y, ),\n" +
            "  [(), [], true],\n" +
            $"  [{Big}],\n" +
            "  [a b, plain, (7, 8)],\n" +
            "  [a b, plain, (7, 8)]\n" +
            "]"
        },
        {
            StringDelimiterMode.Always,
            "[\n" +
            "  [1, 2.50, -0.004],\n" +
            "  ('social tax', 'x,y', ''),\n" +
            "  [(), [], true],\n" +
            $"  [{Big}],\n" +
            "  ['a b', 'plain', (7, 8)],\n" +
            "  ['a b', 'plain', (7, 8)]\n" +
            "]"
        },
    };

    [Theory]
    [MemberData(nameof(InlineItemCases))]
    public void InlineItems_WrittenFromTheirMeasurement_KeepEveryCharacter(StringDelimiterMode mode, string expected)
    {
        var success = SuccessOf(InlineItemsList());
        var options = new OutputFormattingOptions { NewLine = "\n", StringDelimiters = mode };

        // A list root keeps its brackets in both layouts, so both lay the list out alike.
        Assert.Equal(expected, OutputFormatters.Readable.Format(success, options));
        Assert.Equal(expected, OutputFormatters.Concise.Format(success, options));

        // Indentation and newlines come from the options, never from the kept text.
        var wide = new OutputFormattingOptions { NewLine = "\r\n", IndentSize = 4, StringDelimiters = mode };
        var reindented = expected.Replace("\n  ", "\n    ", StringComparison.Ordinal).Replace("\n", "\r\n", StringComparison.Ordinal);
        Assert.Equal(reindented, OutputFormatters.Readable.Format(success, wide));
    }

    [Fact]
    public void InlineItems_InEveryLayoutPosition_KeepEveryCharacter()
    {
        // Root sequence: readable opens it (three structured children); concise hides its
        // parentheses in a block, writes the list item from its measurement, space-joins the
        // flat pair, and hangs the pair run off the preceding line.
        var success = SuccessOf(Seq(Str("Totals"), Seq(Num(1), Num(2)), List(Num(3), Num("4.0")), Seq(Str("a"), Num(1), Str("b"), Num(2))));
        var options = new OutputFormattingOptions { NewLine = "\n" };

        Assert.Equal(
            "(\n  Totals,\n  (1, 2),\n  [3, 4.0],\n  (\n    a, 1,\n    b, 2\n  )\n)",
            OutputFormatters.Readable.Format(success, options));
        Assert.Equal(
            "Totals\n1 2\n[3, 4.0]\n  a 1\n  b 2",
            OutputFormatters.Concise.Format(success, options));

        // A root that fits on the line is written from its measurement too.
        var small = SuccessOf(List(Num(1), Seq(Num(2), Str("two words")), List()));
        Assert.Equal("[1, (2, 'two words'), []]", OutputFormatters.Readable.Format(small, options));
        Assert.Equal("[1, (2, 'two words'), []]", OutputFormatters.Concise.Format(small, options));
    }

    [Fact]
    public void InlineItems_WithDecimalPlaces_UseTheRunsNumberText()
    {
        var success = (RunResult.Success)SuccessOf(List(List(Num("2.5000"), Num("0.125")), List(Num(10), Num("-0.004"))))
            .WithHostDecimalPlaces(2, 2);
        var options = new OutputFormattingOptions { NewLine = "\n", PreferredLineWidth = 20 };

        Assert.Equal("[\n  [2.50, 0.13],\n  [10.00, -0.00]\n]", OutputFormatters.Readable.Format(success, options));
        Assert.Equal("[\n  [2.50, 0.13],\n  [10.00, -0.00]\n]", OutputFormatters.Concise.Format(success, options));
    }

    [Fact]
    public void InlineItems_OverflowExactlyAtTheDisplayLimit()
    {
        // Every limit below the rendering's length returns the bounded overflow response,
        // including the limits that cut inside an item written from its measurement.
        var success = SuccessOf(InlineItemsList());
        foreach (var formatter in new[] { OutputFormatters.Readable, OutputFormatters.Concise })
        {
            var full = formatter.Format(success, new OutputFormattingOptions { NewLine = "\n" });
            for (var limit = 0; limit <= full.Length; limit++)
            {
                var rendering = formatter.RenderDisplay(success, new OutputFormattingOptions { NewLine = "\n", MaxDisplayLength = limit });
                Assert.Equal(limit < full.Length, rendering.LimitExceeded);
                if (rendering.LimitExceeded)
                {
                    // The established response: the limit message, else the marker, else nothing.
                    var message = rendering.LimitError!.Message;
                    Assert.Equal(message.Length <= limit ? message : limit >= 1 ? "…" : string.Empty, rendering.Text);
                }
                else
                {
                    Assert.Equal(full, rendering.Text);
                }
            }
        }
    }

    [Fact]
    public void NestedInlineItems_AreWalkedOnce()
    {
        // A coarse in-process bound. The layouts write two more code units per item than exact
        // ("\n" plus two spaces and "," against ", "), about 8 bytes per item in the builder and the
        // returned string, plus one layout session. Measuring an item and then rendering it again
        // formatted its four numbers twice (about 120 more bytes per item), and a continuation stack
        // per walk cost 152 bytes each, so either regression costs at least 240,000 bytes here,
        // against 96,000 allowed: the current ~20,000 plus one ArrayPool refill (32,832 B) and the
        // ~8 KB counter quantum stay below it.
        const int Items = 2_000;
        var success = SuccessOf(List(NestedRows(Items)));
        var options = new OutputFormattingOptions { NewLine = "\n" };
        var exact = AllocatedBy(() => OutputFormatters.Exact.Format(success, options));

        foreach (var formatter in new[] { OutputFormatters.Readable, OutputFormatters.Concise })
        {
            var layout = AllocatedBy(() => formatter.Format(success, options));
            Assert.True(
                layout - exact <= Items * 48L,
                $"{formatter.Id} allocated {layout} bytes against exact's {exact} for {Items} inline items");
        }
    }

    [Fact]
    public void CanonicalNestedRows_ShareOneContinuationStack()
    {
        // The same nested items as separate output rows and as one list: the texts differ only in
        // the separators (the platform newline against ", ") and the list's brackets. A
        // continuation stack per row cost 152 bytes, 304,000 bytes for 2,000 rows; 64,000 are
        // allowed for the separator difference, one ArrayPool refill and the counter quantum.
        const int Items = 2_000;
        var rows = NestedRows(Items);
        var asRows = SuccessOf(Seq(rows), emittedCount: Items);
        var asList = SuccessOf(List([.. rows]));
        Assert.Equal(Items, asRows.OutputRows.Count);

        var listBytes = AllocatedBy(() => asList.ToDisplayString());
        var rowBytes = AllocatedBy(() => asRows.ToDisplayString());
        Assert.True(rowBytes - listBytes <= Items * 32L, $"display of {Items} rows allocated {rowBytes} bytes against {listBytes} for one list");

        var exactRowBytes = AllocatedBy(() => OutputFormatters.Exact.Format(asRows));
        Assert.True(exactRowBytes - listBytes <= Items * 32L, $"exact formatting of {Items} rows allocated {exactRowBytes} bytes against {listBytes} for one list");
    }
}
