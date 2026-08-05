using KatLang.Formatting;

namespace KatLang.Tests.Formatting;

/// <summary>
/// Deep- and wide-value robustness for the formatters, matching the
/// repository's existing standards: iterative traversal only (host-built
/// values nest beyond any recursion budget), auxiliary state proportional to
/// nesting depth rather than breadth, width-capped measurement so DAG-shared
/// values cannot trigger repeated whole-subtree work, and bounded output under
/// the all-or-nothing display contract.
/// </summary>
public class FormattingRobustnessTests
{
    private const string LimitPrefix = "Display output limit of";

    private static RunResult.Success SuccessOf(Result value)
        => new(new Algorithm.User(null, [], [], [], []), value, []);

    private static Result DeepList(int depth)
    {
        Result value = new Result.Atom(1);
        for (var i = 0; i < depth; i++)
            value = Result.ListValue.TakeOwnership([value]);
        return value;
    }

    private static Result DeepSequence(int depth)
    {
        Result value = new Result.Atom(1);
        for (var i = 0; i < depth; i++)
            value = Result.SequenceValue.TakeOwnership([value]);
        return value;
    }

    private static Result DeepAlternating(int depth)
    {
        Result value = new Result.Atom(1);
        for (var i = 0; i < depth; i++)
        {
            value = i % 2 == 0
                ? Result.ListValue.TakeOwnership([value])
                : Result.SequenceValue.TakeOwnership([value]);
        }

        return value;
    }

    public static TheoryData<string> FormatterIds()
    {
        var data = new TheoryData<string>();
        foreach (var formatter in OutputFormatters.All)
            data.Add(formatter.Id);
        return data;
    }

    [Theory]
    [MemberData(nameof(FormatterIds))]
    public void FiftyThousandLevels_FormatIterativelyWithoutStackGrowth(string formatterId)
    {
        Assert.True(OutputFormatters.TryGet(formatterId, out var formatter));
        var options = new OutputFormattingOptions { NewLine = "\n" };

        foreach (var value in new[] { DeepList(50_000), DeepSequence(50_000), DeepAlternating(50_000) })
        {
            var text = formatter!.Format(SuccessOf(value), options);
            Assert.True(text.Length <= EvaluationLimits.MaxSupportedDisplayLength);
        }
    }

    [Fact]
    public void DeepValue_ExactStillRendersCompletely()
    {
        // The canonical inline form of 50,000 nested lists is 100,001 units —
        // inside the default ceiling — so exact must render it fully.
        var text = OutputFormatters.Exact.Format(SuccessOf(DeepList(50_000)));
        Assert.Equal(100_001, text.Length);
        Assert.StartsWith("[[[", text, StringComparison.Ordinal);
    }

    [Fact]
    public void DeepValue_LayoutFormattersReturnTheBoundedOverflowResponse()
    {
        // Multiline layout of a 50,000-level value grows quadratically with
        // depth (indentation), so it must hit the display ceiling and return
        // the complete overflow response — never a partial rendering, never a
        // stack overflow.
        var success = SuccessOf(DeepList(50_000));
        foreach (var formatter in new[] { OutputFormatters.Readable, OutputFormatters.Concise })
        {
            var text = formatter.Format(success, new OutputFormattingOptions { NewLine = "\n" });
            Assert.StartsWith(LimitPrefix, text, StringComparison.Ordinal);
        }
    }

    [Theory]
    [MemberData(nameof(FormatterIds))]
    public void WideFlatValue_StopsWithoutBreadthSizedTraversalState(string formatterId)
    {
        Assert.True(OutputFormatters.TryGet(formatterId, out var formatter));

        var items = new Result[100_000];
        for (var i = 0; i < items.Length; i++)
            items[i] = new Result.Atom(i % 10);
        var success = SuccessOf(Result.SequenceValue.TakeOwnership(items));
        var options = new OutputFormattingOptions { MaxDisplayLength = 16, NewLine = "\n" };

        // Warm up so JIT/statics do not count toward the measured allocation.
        _ = formatter!.Format(success, options);
        _ = formatter.Format(success, options);

        var before = GC.GetAllocatedBytesForCurrentThread();
        var text = formatter.Format(success, options);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.True(text.Length <= 16);

        // A sibling-granular pending stack would allocate megabytes for the
        // 100,000 pending items before the writer could enforce its 16-unit
        // limit; indexed frames plus width-capped measurement stay far below.
        Assert.True(
            allocated < 64_000,
            $"{formatterId}: wide flat formatting allocated {allocated} bytes of traversal storage");
    }

    [Theory]
    [MemberData(nameof(FormatterIds))]
    public void DagSharedValue_IsBoundedByWidthCappedMeasurement(string formatterId)
    {
        Assert.True(OutputFormatters.TryGet(formatterId, out var formatter));

        // [A, A] doubling: 30 levels share subtrees, so the logical tree has
        // 2^30 leaves. Rendering must be bounded by the display limit and
        // per-node width caps, not by the logical tree size.
        Result value = new Result.Atom(1);
        for (var i = 0; i < 30; i++)
            value = Result.ListValue.TakeOwnership([value, value]);

        var text = formatter!.Format(
            SuccessOf(value),
            new OutputFormattingOptions { MaxDisplayLength = 10_000, NewLine = "\n" });

        Assert.True(text.Length <= 10_000);
        Assert.StartsWith(LimitPrefix, text, StringComparison.Ordinal);
    }

    [Fact]
    public void SharedWidePairRun_IsClassifiedOncePerLevelBeforeBoundedOutput()
    {
        const int width = 50_000;
        var pairItems = new Result[width];
        var label = new Result.Str("k");
        var number = new Result.Atom(1);
        for (var i = 0; i < pairItems.Length; i += 2)
        {
            pairItems[i] = label;
            pairItems[i + 1] = number;
        }

        var shared = Result.SequenceValue.TakeOwnership(pairItems);
        var parents = new Result[width];
        Array.Fill(parents, shared);
        var value = Result.SequenceValue.TakeOwnership(parents);
        var success = SuccessOf(value);
        var options = new OutputFormattingOptions
        {
            NewLine = "\n",
            RootOutputSpacing = 0,
            MaxDisplayLength = 16,
        };

        // The physical value has 100,000 slots, while the logical tree has
        // 2.5 billion. Predicate classification must follow physical DAG
        // identity rather than re-scan the shared child for every parent slot.
        var text = OutputFormatters.Concise.Format(success, options);

        Assert.Equal("…", text);
    }

    [Fact]
    public void DistinctWideChildren_DoNotCreateABreadthSizedPredicateCache()
    {
        const int childCount = 20_000;
        var label = new Result.Str("k");
        var value = new Result.Str("v");
        var children = new Result[childCount];
        for (var child = 0; child < children.Length; child++)
        {
            var pairItems = new Result[32];
            for (var i = 0; i < pairItems.Length; i += 2)
            {
                pairItems[i] = label;
                pairItems[i + 1] = value;
            }

            children[child] = Result.SequenceValue.TakeOwnership(pairItems);
        }

        var success = SuccessOf(Result.SequenceValue.TakeOwnership(children));
        var options = new OutputFormattingOptions
        {
            NewLine = "\n",
            RootOutputSpacing = 0,
            MaxDisplayLength = 16,
        };

        _ = OutputFormatters.Concise.Format(success, options);
        _ = OutputFormatters.Concise.Format(success, options);
        var before = GC.GetAllocatedBytesForCurrentThread();
        var text = OutputFormatters.Concise.Format(success, options);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.Equal("…", text);
        // Classification itself has small per-child runtime overhead, but an
        // unbounded three-table memo for 20,000 distinct children allocates
        // several megabytes. The capped cache stays comfortably below 2 MB.
        Assert.True(allocated < 2_000_000, $"wide-child formatting allocated {allocated} bytes");
    }

    [Fact]
    public void DeepValues_UnderTinyWidth_StillTerminateBounded()
    {
        var options = new OutputFormattingOptions
        {
            PreferredLineWidth = 1,
            MaxDisplayLength = 500,
            NewLine = "\n",
        };

        foreach (var formatter in new[] { OutputFormatters.Readable, OutputFormatters.Concise })
        {
            var text = formatter.Format(SuccessOf(DeepAlternating(10_000)), options);
            Assert.True(text.Length <= 500);
        }
    }

    [Fact]
    public void WidthProbe_DoesNotMaterializeAQuotedCopyOfALargeLeaf()
    {
        var large = new string('x', 500_000);
        var success = SuccessOf(new Result.SequenceValue([new Result.Str(large), new Result.Atom(1)]));
        var options = new OutputFormattingOptions
        {
            StringDelimiters = StringDelimiterMode.Always,
            PreferredLineWidth = 10,
            MaxDisplayLength = 16,
            NewLine = "\n",
        };

        _ = OutputFormatters.Concise.Format(success, options);
        var before = GC.GetAllocatedBytesForCurrentThread();
        var text = OutputFormatters.Concise.Format(success, options);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.Equal("…", text);
        Assert.True(allocated < 64_000, $"width probing allocated {allocated} bytes");
    }
}
