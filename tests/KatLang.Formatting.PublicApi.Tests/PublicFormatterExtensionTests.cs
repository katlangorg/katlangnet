using System.Runtime.CompilerServices;
using KatLang.Formatting;

namespace KatLang.Formatting.PublicApi.Tests;

public class PublicFormatterExtensionTests
{
    [Fact]
    public void CustomFormatter_UsesOnlyThePublicPackageSurface()
    {
        Assert.DoesNotContain(
            typeof(OutputFormatter).Assembly.GetCustomAttributes(typeof(InternalsVisibleToAttribute), false)
                .Cast<InternalsVisibleToAttribute>(),
            attribute => attribute.AssemblyName.StartsWith(
                typeof(PublicFormatterExtensionTests).Assembly.GetName().Name!,
                StringComparison.Ordinal));

        var formatter = new ShapeFormatter();
        var result = KatLangEngine.Run("1, 'x', (2, 3), [4]");

        Assert.Equal(
            "A:1\nT:x\nS(A:2|A:3)\nL[A:4]",
            formatter.Format(result, new OutputFormattingOptions
            {
                NewLine = "\n",
                RootOutputSpacing = 0,
            }));
    }

    [Fact]
    public void CustomFormatter_HonorsRunNumberAndDisplayLimitsByConstruction()
    {
        var formatter = new ShapeFormatter();
        var rounded = KatLangEngine.Run("MaxDecimalPlaces = 2\nMath.Pi");
        Assert.Equal("A:3.14", formatter.Format(rounded));

        var boundedRun = KatLangEngine.Run(
            "1, 2, 3",
            new RunOptions { EvaluationLimits = new EvaluationLimits { MaxDisplayLength = 4 } });
        var text = formatter.Format(
            boundedRun,
            new OutputFormattingOptions { MaxDisplayLength = int.MaxValue });

        Assert.Equal("…", text);
        Assert.True(text.Length <= 4);
    }

    [Fact]
    public void CustomFormatter_ReceivesTheRunsEffectiveMaxDecimalPlaces()
    {
        // BoundedOutputWriter.AppendAtom reads the ONE effective maximum the run composed: the
        // host maximum alone, the program's MaxDecimalPlaces alone, and — when both are
        // present — the smaller of the two (Q-10 D-F), exactly as canonical display does.
        var formatter = new ShapeFormatter();
        var hostFilter = new RunOptions { MaxDecimalPlaces = 3 };

        var hostOnly = KatLangEngine.Run("1 / 7", hostFilter);
        var sourceOnly = KatLangEngine.Run("MaxDecimalPlaces = 6\n1 / 7");
        var hostStricter = KatLangEngine.Run("MaxDecimalPlaces = 6\n1 / 7", hostFilter);
        var sourceStricter = KatLangEngine.Run("MaxDecimalPlaces = 2\n1 / 7", hostFilter);
        var neither = KatLangEngine.Run("1 / 7");

        Assert.Equal("A:0.143", formatter.Format(hostOnly));
        Assert.Equal("A:0.142857", formatter.Format(sourceOnly));
        Assert.Equal("A:0.143", formatter.Format(hostStricter));
        Assert.Equal("A:0.14", formatter.Format(sourceStricter));
        Assert.Equal("A:" + neither.ToDisplayString(), formatter.Format(neither));

        foreach (var run in new[] { hostOnly, sourceOnly, hostStricter, sourceStricter, neither })
            Assert.Equal("A:" + run.ToDisplayString(), formatter.RenderDisplay(run).Text);
    }

    [Fact]
    public void CustomFormatter_ReceivesTheRunsEffectiveMinDecimalPlaces_AndTheFixedPlacesPair()
    {
        // The same one writer applies the minimum: it pads (whole numbers too) and never rounds,
        // composes with the program's own by the smaller count, and with a maximum of the same
        // value gives a fixed number of places.
        var formatter = new ShapeFormatter();
        var hostMinimum = new RunOptions { MinDecimalPlaces = 3 };

        var hostOnly = KatLangEngine.Run("2.5", hostMinimum);
        var sourceOnly = KatLangEngine.Run("MinDecimalPlaces = 6\n2.5");
        var hostSmaller = KatLangEngine.Run("MinDecimalPlaces = 6\n2.5", hostMinimum);
        var sourceSmaller = KatLangEngine.Run("MinDecimalPlaces = 2\n2.5", hostMinimum);
        var whole = KatLangEngine.Run("10", hostMinimum);
        var unrounded = KatLangEngine.Run("1.234567", hostMinimum);
        var fixedPlaces = KatLangEngine.Run("1.234567", new RunOptions { MinDecimalPlaces = 2, MaxDecimalPlaces = 2 });
        var split = KatLangEngine.Run("MinDecimalPlaces = 2\n10", new RunOptions { MaxDecimalPlaces = 2 });

        Assert.Equal("A:2.500", formatter.Format(hostOnly));
        Assert.Equal("A:2.500000", formatter.Format(sourceOnly));
        Assert.Equal("A:2.500", formatter.Format(hostSmaller));
        Assert.Equal("A:2.50", formatter.Format(sourceSmaller));
        Assert.Equal("A:10.000", formatter.Format(whole));
        Assert.Equal("A:1.234567", formatter.Format(unrounded));
        Assert.Equal("A:1.23", formatter.Format(fixedPlaces));
        Assert.Equal("A:10.00", formatter.Format(split));

        foreach (var run in new[] { hostOnly, sourceOnly, hostSmaller, sourceSmaller, whole, unrounded, fixedPlaces, split })
            Assert.Equal("A:" + run.ToDisplayString(), formatter.RenderDisplay(run).Text);

        // Re-applying host settings to a finished result reaches the custom formatter too.
        Assert.Equal("A:2.5", formatter.Format(sourceSmaller.WithHostDecimalPlaces(0, null)));
        Assert.Equal("A:1.2346", formatter.Format(unrounded.WithHostDecimalPlaces(null, 4)));
    }

    [Theory]
    [InlineData(0)]
    [InlineData(RunOptions.DecimalPlacesLimit)]
    public void CustomFormatter_DisplayDefaultBoundariesAndLimits_UseOnlyPublicApi(int decimals)
    {
        var formatter = new ShapeFormatter();
        var host = new RunOptions { MaxDecimalPlaces = decimals };
        var hosted = Assert.IsType<RunResult.Success>(KatLangEngine.Run("0.125", host));
        var declared = Assert.IsType<RunResult.Success>(KatLangEngine.Run($"MaxDecimalPlaces = {decimals}\n0.125"));
        // Both maximums present: the smaller one decides, whichever side supplies it (Q-10 D-F).
        var sourceDecides = Assert.IsType<RunResult.Success>(KatLangEngine.Run($"MaxDecimalPlaces = {decimals}\n0.125",
            new RunOptions { MaxDecimalPlaces = RunOptions.DecimalPlacesLimit }));
        var hostDecides = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            $"MaxDecimalPlaces = {RunOptions.DecimalPlacesLimit}\n0.125", host));
        // A maximum rounds and never pads: 0 rounds 0.125 away, 99 leaves its three digits.
        var expected = decimals == 0 ? "A:0" : "A:0.125";
        foreach (var run in new[] { hosted, declared, sourceDecides, hostDecides })
            Assert.Equal(expected, formatter.Format(run));

        // The same boundaries as a MINIMUM pad instead: 0 pads nothing, 99 pads to 99 places.
        var padded = decimals == 0 ? "A:0.125" : "A:0.125" + new string('0', 96);
        Assert.Equal(padded, formatter.Format(KatLangEngine.Run("0.125", new RunOptions { MinDecimalPlaces = decimals })));
        Assert.Equal(padded, formatter.Format(KatLangEngine.Run($"MinDecimalPlaces = {decimals}\n0.125")));

        var bounded = KatLangEngine.Run("0.125", new RunOptions
        {
            MaxDecimalPlaces = decimals,
            EvaluationLimits = new EvaluationLimits { MaxDisplayLength = 2 },
        });
        var rendering = formatter.RenderDisplay(bounded, new OutputFormattingOptions { MaxDisplayLength = 1000 });
        Assert.True(rendering.LimitExceeded);
        Assert.Equal(KatLangErrorCode.DisplayLengthLimitExceeded, rendering.LimitError!.Code);
        Assert.InRange(rendering.Text.Length, 0, 2);
    }

    [Fact]
    public void CustomFormatter_InheritsSupportedFailureAndNoOutputRendering()
    {
        var formatter = new ShapeFormatter();
        foreach (var source in new[] { "2 +", "1 / 0", "OnlyDefinition = 1" })
        {
            var result = KatLangEngine.Run(source);
            Assert.Equal(result.ToDisplayString(), formatter.Format(result));
        }
    }

    [Fact]
    public void CustomFormatter_CanEmitChargedIndentationThroughTheWriter()
    {
        var formatter = new IndentedRowsFormatter();
        var run = KatLangEngine.Run("1, 2");
        var options = new OutputFormattingOptions { NewLine = "\n", IndentSize = 3 };

        Assert.Equal("   1\n   2", formatter.Format(run, options));

        // Indentation is charged like every other code unit: the nine units of
        // "   1\n   2" fit exactly, eight do not, and overflow stays
        // all-or-nothing.
        Assert.Equal("   1\n   2", formatter.Format(run, options with { MaxDisplayLength = 9 }));
        Assert.Equal("…", formatter.Format(run, options with { MaxDisplayLength = 8 }));

        Assert.Throws<ArgumentOutOfRangeException>(
            () => new NegativeSpacesFormatter().Format(KatLangEngine.Run("1")));
    }

    [Fact]
    public void CustomFormatter_CannotBypassTheLimitByIgnoringRefusedAppends()
    {
        var formatter = new IgnoresAppendResultFormatter();
        var text = formatter.Format(
            KatLangEngine.Run("1"),
            new OutputFormattingOptions { MaxDisplayLength = 4 });

        Assert.Equal("…", text);
        Assert.True(text.Length <= 4);
    }

    [Fact]
    public void Writer_RejectsNullTextFromAnExternalFormatter()
        => Assert.Throws<ArgumentNullException>(
            () => new NullTextFormatter().Format(KatLangEngine.Run("1")));

    [Fact]
    public void BaseTemplate_RejectsIncompleteOutputWithoutWriterOverflow()
        => Assert.Throws<InvalidOperationException>(
            () => new IncompleteFormatter().Format(KatLangEngine.Run("1")));

    [Fact]
    public void CustomFormatter_WideValueDoesNotNeedSiblingSizedTraversalState()
    {
        var items = new Result[100_000];
        for (var i = 0; i < items.Length; i++)
            items[i] = new Result.Atom(i % 10);

        var value = new Result.SequenceValue(items);
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Wide()", new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.Create("Wide", (_, _) => value)),
        }));
        var formatter = new ShapeFormatter();
        var options = new OutputFormattingOptions { MaxDisplayLength = 16 };

        _ = formatter.Format(run, options);
        _ = formatter.Format(run, options);
        var before = GC.GetAllocatedBytesForCurrentThread();
        var text = formatter.Format(run, options);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.Equal("…", text);
        Assert.True(allocated < 64_000, $"external formatter allocated {allocated} bytes");
    }

    [Fact]
    public void CustomFormatter_ReportsDisplayOverflowStructurally_ThroughTheSharedTemplate()
    {
        var formatter = new ShapeFormatter();
        var run = KatLangEngine.Run("1, 2, 3");
        var options = new OutputFormattingOptions { NewLine = "\n", RootOutputSpacing = 0 };

        var complete = formatter.RenderDisplay(run, options);
        Assert.False(complete.LimitExceeded);
        Assert.Null(complete.LimitError);
        Assert.Equal(formatter.Format(run, options), complete.Text);

        var bounded = options with { MaxDisplayLength = 4 };
        var overflow = formatter.RenderDisplay(run, bounded);
        Assert.True(overflow.LimitExceeded);
        Assert.Equal("…", overflow.Text);
        Assert.Equal(formatter.Format(run, bounded), overflow.Text);
        Assert.Equal(KatLangErrorCode.DisplayLengthLimitExceeded, overflow.LimitError!.Code);
        Assert.True(overflow.LimitError.IsResourceLimit);
        Assert.Equal(4, Assert.IsType<EvalError.DisplayLengthLimitExceeded>(overflow.LimitError.Source).Limit);

        var repeated = formatter.RenderDisplay(run, options);
        Assert.False(repeated.LimitExceeded);
        Assert.Null(repeated.LimitError);
        Assert.Equal(complete.Text, repeated.Text);
    }

    [Fact]
    public void CustomFormatter_CannotSuppressTheOverflowSignalByIgnoringRefusedAppends()
    {
        var rendering = new IgnoresAppendResultFormatter().RenderDisplay(
            KatLangEngine.Run("1"),
            new OutputFormattingOptions { MaxDisplayLength = 4 });

        Assert.True(rendering.LimitExceeded);
        Assert.Equal("…", rendering.Text);
    }

    /// <summary>Minimal external formatter exercising <see cref="BoundedOutputWriter.AppendSpaces"/>.</summary>
    private sealed class IndentedRowsFormatter : OutputFormatter
    {
        public override string Id => "indented-rows";

        protected override bool WriteSuccessOutput(
            IReadOnlyList<Result> outputRows,
            OutputFormattingOptions options,
            BoundedOutputWriter writer)
        {
            for (var rowIndex = 0; rowIndex < outputRows.Count; rowIndex++)
            {
                if (rowIndex > 0 && !writer.Append(options.NewLine)) return false;
                if (!writer.AppendSpaces(options.IndentSize)) return false;
                if (outputRows[rowIndex] is Result.Atom atom && !writer.AppendAtom(atom.Value)) return false;
            }

            return true;
        }
    }

    /// <summary>Pins the writer's argument validation for external callers.</summary>
    private sealed class NegativeSpacesFormatter : OutputFormatter
    {
        public override string Id => "negative-spaces";

        protected override bool WriteSuccessOutput(
            IReadOnlyList<Result> outputRows,
            OutputFormattingOptions options,
            BoundedOutputWriter writer)
            => writer.AppendSpaces(-1);
    }

    /// <summary>Proves the base template observes writer overflow even when an implementation ignores return values.</summary>
    private sealed class IgnoresAppendResultFormatter : OutputFormatter
    {
        public override string Id => "ignores-append-result";

        protected override bool WriteSuccessOutput(
            IReadOnlyList<Result> outputRows,
            OutputFormattingOptions options,
            BoundedOutputWriter writer)
        {
            for (var i = 0; i < 100; i++)
                writer.Append("x");
            // A later empty append on either writer path cannot clear refusal.
            writer.Append(string.Empty);
            writer.AppendSpaces(0);
            return true;
        }
    }

    /// <summary>Exercises public null validation rather than relying on the internal sink.</summary>
    private sealed class NullTextFormatter : OutputFormatter
    {
        public override string Id => "null-text";

        protected override bool WriteSuccessOutput(
            IReadOnlyList<Result> outputRows,
            OutputFormattingOptions options,
            BoundedOutputWriter writer)
            => writer.Append(null!);
    }

    /// <summary>Models an implementation bug: a partial prefix is not a successful formatting.</summary>
    private sealed class IncompleteFormatter : OutputFormatter
    {
        public override string Id => "incomplete";

        protected override bool WriteSuccessOutput(
            IReadOnlyList<Result> outputRows,
            OutputFormattingOptions options,
            BoundedOutputWriter writer)
        {
            writer.Append("partial");
            return false;
        }
    }

    /// <summary>
    /// A consumer-owned formatter. Its implementation references only public
    /// KatLang and KatLang.Formatting types; this assembly is not a friend of
    /// the package assembly.
    /// </summary>
    private sealed class ShapeFormatter : OutputFormatter
    {
        public override string Id => "shape";

        protected override bool WriteSuccessOutput(
            IReadOnlyList<Result> outputRows,
            OutputFormattingOptions options,
            BoundedOutputWriter writer)
        {
            for (var rowIndex = 0; rowIndex < outputRows.Count; rowIndex++)
            {
                if (rowIndex > 0 && !writer.Append(options.NewLine))
                    return false;
                if (!WriteValue(outputRows[rowIndex], writer))
                    return false;
            }

            return true;
        }

        private static bool WriteValue(Result value, BoundedOutputWriter writer)
        {
            var frames = new Stack<WriteFrame>();
            var current = value;

            while (true)
            {
                switch (current)
                {
                    case Result.Atom atom:
                        if (!writer.Append("A:") || !writer.AppendAtom(atom.Value)) return false;
                        break;
                    case Result.Str str:
                        if (!writer.Append("T:") || !writer.Append(str.Value)) return false;
                        break;
                    case Result.SequenceValue sequence:
                        if (!OpenStructure(sequence.Items, "S(", ")", writer, frames, out current))
                            return false;
                        if (sequence.Items.Count > 0) continue;
                        break;
                    case Result.ListValue list:
                        if (!OpenStructure(list.Items, "L[", "]", writer, frames, out current))
                            return false;
                        if (list.Items.Count > 0) continue;
                        break;
                    default:
                        throw new InvalidOperationException("Unknown Result variant.");
                }

                while (frames.Count > 0)
                {
                    var frame = frames.Peek();
                    if (frame.Next < frame.Items.Count)
                    {
                        if (!writer.Append("|")) return false;
                        current = frame.Items[frame.Next++];
                        break;
                    }

                    frames.Pop();
                    if (!writer.Append(frame.Close)) return false;
                }

                if (frames.Count == 0) return true;
            }
        }

        private static bool OpenStructure(
            IReadOnlyList<Result> items,
            string open,
            string close,
            BoundedOutputWriter writer,
            Stack<WriteFrame> frames,
            out Result current)
        {
            current = null!;
            if (!writer.Append(open)) return false;
            if (items.Count == 0) return writer.Append(close);

            frames.Push(new WriteFrame(items, close) { Next = 1 });
            current = items[0];
            return true;
        }

        private sealed class WriteFrame(IReadOnlyList<Result> items, string close)
        {
            public IReadOnlyList<Result> Items { get; } = items;
            public string Close { get; } = close;
            public int Next { get; set; }
        }
    }
}
