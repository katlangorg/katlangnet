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
        var rounded = KatLangEngine.Run("DisplayDecimals = 2\nMath.Pi");
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
    public void CustomFormatter_ReceivesTheRunsEffectiveDisplayDecimals()
    {
        // BoundedOutputWriter.AppendAtom reads the ONE effective setting the run resolved: the
        // host default alone, the program's DisplayDecimals alone, and — when both are present
        // — the program's declaration, exactly as canonical display does.
        var formatter = new ShapeFormatter();
        var hostDefault = new RunOptions { DefaultDisplayDecimals = 3 };

        var hostOnly = KatLangEngine.Run("1 / 7", hostDefault);
        var sourceOnly = KatLangEngine.Run("DisplayDecimals = 6\n1 / 7");
        var both = KatLangEngine.Run("DisplayDecimals = 6\n1 / 7", hostDefault);
        var neither = KatLangEngine.Run("1 / 7");

        Assert.Equal("A:0.143", formatter.Format(hostOnly));
        Assert.Equal("A:0.142857", formatter.Format(sourceOnly));
        Assert.Equal("A:0.142857", formatter.Format(both));
        Assert.Equal("A:" + neither.ToDisplayString(), formatter.Format(neither));

        foreach (var run in new[] { hostOnly, sourceOnly, both, neither })
            Assert.Equal("A:" + run.ToDisplayString(), formatter.RenderDisplay(run).Text);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(RunOptions.MaxDisplayDecimals)]
    public void CustomFormatter_DisplayDefaultBoundariesAndLimits_UseOnlyPublicApi(int decimals)
    {
        var formatter = new ShapeFormatter();
        var host = new RunOptions { DefaultDisplayDecimals = decimals };
        var hosted = Assert.IsType<RunResult.Success>(KatLangEngine.Run("0.125", host));
        var declared = Assert.IsType<RunResult.Success>(KatLangEngine.Run($"DisplayDecimals = {decimals}\n0.125"));
        var both = Assert.IsType<RunResult.Success>(KatLangEngine.Run($"DisplayDecimals = {decimals}\n0.125",
            new RunOptions { DefaultDisplayDecimals = decimals == 0 ? 99 : 0 }));
        var expected = decimals == 0 ? "A:0" : "A:0.125" + new string('0', 96);
        foreach (var run in new[] { hosted, declared, both })
            Assert.Equal(expected, formatter.Format(run));

        var bounded = KatLangEngine.Run("0.125", new RunOptions
        {
            DefaultDisplayDecimals = decimals,
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
