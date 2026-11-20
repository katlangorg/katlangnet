using System.Globalization;
using System.Numerics;
using KatLang.Formatting;
using KatLang.Rendering;

namespace KatLang.Tests.Formatting;

/// <summary>
/// Implementation-only allocation work in the rendering pipeline must not change a single
/// character of output. A canonical number is written to the sink from a stack buffer
/// (<see cref="ValueTextRenderer.AppendAtom"/>) and measured for layout without building its
/// text (<see cref="ValueTextRenderer.AtomLength"/>); every other number keeps the existing
/// <see cref="ValueTextRenderer.FormatAtom"/> rule, and canonical text longer than the buffer
/// uses its same fixed-point format's string path once. The value walk creates its continuation
/// stack only when it enters a nested structure, and the display writer charges strings, buffers, and repeated characters
/// through one limit check. Every expectation here is either FormatAtom's own text or written
/// out by hand, so the tests pin agreement, not a second implementation.
/// </summary>
public class DirectAtomWritingTests
{
    private static Decimal128 N(string literal) => literal switch
    {
        "NaN" => Decimal128.NaN,
        "Infinity" => Decimal128.PositiveInfinity,
        "-Infinity" => Decimal128.NegativeInfinity,
        _ => Decimal128.Parse(literal, CultureInfo.InvariantCulture),
    };

    private static DisplayOptions Places(int? min, int? max)
        => new(min, max, HostMinDecimalPlaces: null, HostMaxDecimalPlaces: null, MaxDisplayLength: int.MaxValue);

    // One spread root row supplies every output row the value presents for the emitted count.
    private static RunResult.Success SuccessOf(Result value, int emittedCount = 1)
        => HandBuiltSuccess.OfOneSpreadRow(value, emittedCount);

    // Canonical spellings on both sides of the stack buffer (63, 64, and 65 code units), the
    // fallback-only values (non-finite, and every decimal-places setting), signed zero, stored
    // trailing zeros, division-sized fractions, and the exponent extremes.
    private static readonly string[] Literals =
    [
        "0", "-0", "7", "-42", "1.50", "2.5000", "0.125", "-0.004", "99.995",
        "1e34", "1e-28", "0.3333333333333333333333333333333333",
        "1e62", "1e63", "-1e62", "1e64", "-1e63", "1e-61", "1e-62", "1e-63",
        "-1e-60", "-1e-61", "-1e-62", "0e6111", "-0e6111",
        "1234567890123456789012345678901234e32", "-1234567890123456789012345678901234e31",
        "1e300", "-1e-6176",
        "NaN", "Infinity", "-Infinity",
    ];

    private static readonly (int? Min, int? Max)[] PlaceSettings =
        [(null, null), (2, null), (null, 2), (1, 3), (0, 0), (40, 40)];

    public static TheoryData<string, int?, int?> AtomCases()
    {
        var data = new TheoryData<string, int?, int?>();
        foreach (var literal in Literals)
        {
            foreach (var (min, max) in PlaceSettings)
                data.Add(literal, min, max);
        }

        return data;
    }

    [Fact]
    public void BoundaryLiterals_StraddleTheStackBuffer()
    {
        // Without this the theory below could silently stop testing the fallback edge.
        var canonical = DisplayOptions.Canonical(int.MaxValue);
        Assert.Equal(ValueTextRenderer.AtomStackBufferLength - 1, ValueTextRenderer.FormatAtom(N("1e62"), canonical).Length);
        Assert.Equal(ValueTextRenderer.AtomStackBufferLength, ValueTextRenderer.FormatAtom(N("1e63"), canonical).Length);
        Assert.Equal(ValueTextRenderer.AtomStackBufferLength, ValueTextRenderer.FormatAtom(N("-1e62"), canonical).Length);
        Assert.Equal(ValueTextRenderer.AtomStackBufferLength + 1, ValueTextRenderer.FormatAtom(N("1e64"), canonical).Length);
        Assert.Equal(ValueTextRenderer.AtomStackBufferLength + 1, ValueTextRenderer.FormatAtom(N("-1e63"), canonical).Length);
        Assert.Equal("1" + new string('0', 63), ValueTextRenderer.FormatAtom(N("1e63"), canonical));
    }

    [Theory]
    [MemberData(nameof(AtomCases))]
    public void AppendAtom_WritesAndMeasuresExactlyFormatAtomText(string literal, int? min, int? max)
    {
        var value = N(literal);
        var options = Places(min, max);
        var expected = ValueTextRenderer.FormatAtom(value, options);

        // The display writer receives the same text and is charged its length.
        var writer = new BoundedDisplayWriter(int.MaxValue);
        Assert.True(ValueTextRenderer.AppendAtom(value, options, writer));
        Assert.Equal(expected, writer.ToString());
        Assert.Equal(expected.Length, writer.Checkpoint);

        // Layout measures the same length, and the width sink fits it exactly.
        Assert.Equal(expected.Length, ValueTextRenderer.AtomLength(value, options));
        var measure = new CappedWidthSink();
        measure.Reset(expected.Length);
        Assert.True(ValueTextRenderer.AppendAtom(value, options, measure));
        Assert.Equal(0, measure.RemainingCapacity);
        measure.Reset(expected.Length - 1);
        Assert.False(ValueTextRenderer.AppendAtom(value, options, measure));

        // One code unit short: refused before anything is written, and the refusal sticks.
        var tight = new BoundedDisplayWriter(expected.Length - 1);
        Assert.False(ValueTextRenderer.AppendAtom(value, options, tight));
        Assert.True(tight.LimitExceeded);
        Assert.Equal(string.Empty, tight.ToString());
        Assert.False(tight.Append("x"));

        // A diagnostic fragment cut inside the number keeps the same prefix as the string.
        foreach (var limit in new[] { 0, 1, expected.Length / 2, expected.Length - 1, expected.Length })
        {
            var fromString = new BoundedDiagnosticSink(limit);
            var fromAtom = new BoundedDiagnosticSink(limit);
            var stringAccepted = fromString.Append(expected);
            Assert.Equal(stringAccepted, ValueTextRenderer.AppendAtom(value, options, fromAtom));
            Assert.Equal(fromString.Truncated, fromAtom.Truncated);
            Assert.Equal(fromString.AppendAttempts, fromAtom.AppendAttempts);
            Assert.Equal(fromString.Finish(), fromAtom.Finish());
        }
    }

    [Fact]
    public void CanonicalNumbers_AreWrittenAndMeasuredWithoutBuildingTheirText()
    {
        // A coarse in-process bound, not a strict allocation assertion: the runtime formatter
        // may allocate internally, but writing or measuring a canonical number must allocate
        // clearly less than building its string first. That string is at least 32 bytes for
        // "12345", so 20,000 calls differ by hundreds of kilobytes — far above the one
        // background-GC allocation quantum this counter can misreport.
        const int Calls = 20_000;
        var value = N("12345");
        var canonical = DisplayOptions.Canonical(int.MaxValue);
        var sink = new CappedWidthSink();
        sink.Reset(int.MaxValue);
        long lengths = 0;

        for (var warm = 0; warm < 2; warm++)
        {
            ValueTextRenderer.AppendAtom(value, canonical, sink);
            lengths += ValueTextRenderer.AtomLength(value, canonical);
            sink.Append(ValueTextRenderer.FormatAtom(value, canonical));
        }

        var before = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < Calls; i++)
            ValueTextRenderer.AppendAtom(value, canonical, sink);
        var written = GC.GetAllocatedBytesForCurrentThread() - before;

        before = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < Calls; i++)
            lengths += ValueTextRenderer.AtomLength(value, canonical);
        var measured = GC.GetAllocatedBytesForCurrentThread() - before;

        before = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < Calls; i++)
            sink.Append(ValueTextRenderer.FormatAtom(value, canonical));
        var viaText = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.Equal((Calls + 2L) * 5, lengths);
        var savedAtLeast = Calls * 16L;
        Assert.True(written <= viaText - savedAtLeast, $"AppendAtom allocated {written} bytes; via text {viaText}");
        Assert.True(measured <= viaText - savedAtLeast, $"AtomLength allocated {measured} bytes; via text {viaText}");
    }

    [Fact]
    public void OversizedCanonicalNumbers_DoNotPayForFormattingTwice()
    {
        const int Calls = 2_000;
        var value = N("1e-6176");
        var canonical = DisplayOptions.Canonical(int.MaxValue);
        var sink = new CappedWidthSink();
        sink.Reset(int.MaxValue);
        long lengths = 0;
        for (var warm = 0; warm < 2; warm++)
        {
            ValueTextRenderer.AppendAtom(value, canonical, sink);
            lengths += ValueTextRenderer.AtomLength(value, canonical);
            sink.Append(ValueTextRenderer.FormatAtom(value, canonical));
        }

        var before = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < Calls; i++)
            ValueTextRenderer.AppendAtom(value, canonical, sink);
        var written = GC.GetAllocatedBytesForCurrentThread() - before;

        before = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < Calls; i++)
            lengths += ValueTextRenderer.AtomLength(value, canonical);
        var measured = GC.GetAllocatedBytesForCurrentThread() - before;

        before = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < Calls; i++)
            sink.Append(ValueTextRenderer.FormatAtom(value, canonical));
        var viaText = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.Equal((Calls + 2L) * 6_178, lengths);

        // On .NET 11 win-x64, a gen-2 trim under high memory pressure can leave 32,832 bytes
        // of pooled char buffers to refill. Rebuilding "6176" and "F6176" on fallback costs
        // 64 bytes per call, or 128,000 bytes here. One refill plus ~8 KiB of GC counter noise
        // fits on either side because 32,832 + 8,192 < 64,000 < 128,000 - 32,832 - 8,192.
        var allowance = Calls * 32L;
        Assert.True(written <= viaText + allowance, $"AppendAtom allocated {written} bytes; via text {viaText}; allowance {allowance}");
        Assert.True(measured <= viaText + allowance, $"AtomLength allocated {measured} bytes; via text {viaText}; allowance {allowance}");
    }

    [Fact]
    public void DiagnosticSink_CutsAStackWrittenNumberAtTheBudget()
    {
        var sink = new BoundedDiagnosticSink(3);
        ValueTextRenderer.AppendValue(
            new Result.Atom(12345),
            DisplayOptions.Canonical(int.MaxValue),
            QuotedDiagnosticStringPolicy.Instance,
            sink);

        Assert.True(sink.Truncated);
        Assert.Equal("123" + DiagnosticValueRenderer.TruncationMarker, sink.Finish());
    }

    [Fact]
    public void DisplayWriter_ChargesEveryOverloadThroughOneLimit()
    {
        var writer = new BoundedDisplayWriter(6);
        Assert.True(writer.Append("ab"));
        Assert.True(writer.Append("cd".AsSpan()));
        Assert.True(writer.Append('e', 1));
        Assert.False(writer.Append("fg"));
        Assert.True(writer.LimitExceeded);

        // A refusal holds for every overload, even an append that would fit.
        Assert.False(writer.Append(string.Empty));
        Assert.False(writer.Append("f".AsSpan()));
        Assert.False(writer.Append('f', 0));
        Assert.Equal("abcde", writer.ToString());

        // Rewinding clears the refusal; an append exactly filling the limit is accepted.
        writer.RewindTo(4);
        Assert.False(writer.LimitExceeded);
        Assert.True(writer.Append("ef".AsSpan()));
        Assert.Equal(6, writer.Checkpoint);
        Assert.False(writer.Append('g', 1));
        Assert.Equal("abcdef", writer.ToString());
    }

    [Fact]
    public void ValueWalk_FlatNestedAndStoppedProbes_KeepTheirText()
    {
        var canonical = DisplayOptions.Canonical(int.MaxValue);
        Result flat = new Result.ListValue([new Result.Atom(1), new Result.Str("a b"), new Result.Bool(true)]);
        Result nested = new Result.ListValue(
        [
            new Result.Atom(1),
            new Result.SequenceValue([new Result.Atom(2), new Result.ListValue([new Result.Atom(3), new Result.SequenceValue([])])]),
            new Result.Atom(4),
        ]);

        Assert.Equal("[1, a b, true]", Render(flat));
        Assert.Equal("[1, (2, [3, ()]), 4]", Render(nested));

        // A width probe that stops inside a nested child, or exactly at a closer, reports
        // "does not fit" without completing the walk.
        var measure = new CappedWidthSink();
        foreach (var cap in new[] { 0, 1, 5, 9, 18 })
        {
            measure.Reset(cap);
            Assert.False(ValueTextRenderer.AppendValue(nested, canonical, RawStringTextPolicy.Instance, measure));
        }

        measure.Reset("[1, (2, [3, ()]), 4]".Length);
        Assert.True(ValueTextRenderer.AppendValue(nested, canonical, RawStringTextPolicy.Instance, measure));

        string Render(Result value)
        {
            var writer = new BoundedDisplayWriter(int.MaxValue);
            Assert.True(ValueTextRenderer.AppendValue(value, canonical, RawStringTextPolicy.Instance, writer));
            return writer.ToString();
        }
    }

    [Fact]
    public void LongAndShortNumbers_RenderIdenticallyThroughEveryFormatter()
    {
        var big = "1" + new string('0', 70);
        var negativeTiny = "-0." + new string('0', 79) + "1";
        Result value = new Result.ListValue(
        [
            new Result.Atom(N("1e70")),
            new Result.Atom(7),
            new Result.SequenceValue([new Result.Atom(N("-1e-80")), new Result.Atom(N("2.50"))]),
        ]);
        var success = SuccessOf(value);

        var exact = $"[{big}, 7, ({negativeTiny}, 2.50)]";
        Assert.Equal(exact, success.ToDisplayString());
        Assert.Equal(exact, OutputFormatters.Exact.Format(success));

        // Readable and concise lay the list out vertically: it is wider than the line.
        var options = new OutputFormattingOptions { NewLine = "\n" };
        var vertical = $"[\n  {big},\n  7,\n  ({negativeTiny}, 2.50)\n]";
        Assert.Equal(vertical, OutputFormatters.Readable.Format(success, options));
        Assert.Equal(vertical, OutputFormatters.Concise.Format(success, options));
    }

    [Theory]
    [InlineData("1e64", "7")]
    [InlineData("12345", "678")]
    public void ConciseSpaceJoin_FitsTheMeasuredNumbersExactly(string first, string second)
    {
        // The space-joined root line is chosen only when the rendered numbers and the one
        // separator fit the preferred width, so the measured lengths of the buffer-written and
        // the fallback numbers decide the layout at the exact boundary.
        var firstText = ValueTextRenderer.FormatNumberInvariant(N(first));
        var secondText = ValueTextRenderer.FormatNumberInvariant(N(second));
        var success = SuccessOf(new Result.SequenceValue([new Result.Atom(N(first)), new Result.Atom(N(second))]));
        var lineWidth = firstText.Length + 1 + secondText.Length;

        Assert.Equal(
            $"{firstText} {secondText}",
            OutputFormatters.Concise.Format(success, new OutputFormattingOptions { NewLine = "\n", PreferredLineWidth = lineWidth }));
        Assert.Equal(
            $"{firstText}\n{secondText}",
            OutputFormatters.Concise.Format(success, new OutputFormattingOptions { NewLine = "\n", PreferredLineWidth = lineWidth - 1 }));
    }

    [Fact]
    public void LargeNumericRows_OverflowExactlyAtTheLimit()
    {
        // 2,000 rows of canonical numbers: the rendering at its exact length completes, one
        // code unit less returns the bounded overflow response for every formatter.
        var items = new Result[2_000];
        for (var i = 0; i < items.Length; i++)
            items[i] = new Result.Atom(N(i % 2 == 0 ? (i * 7).ToString(CultureInfo.InvariantCulture) : "0.0" + i.ToString(CultureInfo.InvariantCulture)));

        var success = SuccessOf(new Result.SequenceValue(items), emittedCount: items.Length);
        var expected = string.Join(Environment.NewLine, items.Select(item => ValueTextRenderer.FormatNumberInvariant(((Result.Atom)item).Value)));
        Assert.Equal(expected, success.ToDisplayString());

        foreach (var formatter in OutputFormatters.All)
        {
            var options = new OutputFormattingOptions { RootOutputSpacing = 0 };
            var full = formatter.RenderDisplay(success, options);
            Assert.False(full.LimitExceeded);
            Assert.Equal(expected, full.Text);

            var exactFit = formatter.RenderDisplay(success, new OutputFormattingOptions { RootOutputSpacing = 0, MaxDisplayLength = expected.Length });
            Assert.False(exactFit.LimitExceeded);
            Assert.Equal(expected, exactFit.Text);

            var oneShort = formatter.RenderDisplay(success, new OutputFormattingOptions { RootOutputSpacing = 0, MaxDisplayLength = expected.Length - 1 });
            Assert.True(oneShort.LimitExceeded);
            Assert.Equal(oneShort.LimitError.Message, oneShort.Text);
        }
    }
}
