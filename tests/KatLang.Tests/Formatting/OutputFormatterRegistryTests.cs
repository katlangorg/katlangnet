using KatLang.Formatting;

namespace KatLang.Tests.Formatting;

/// <summary>Public built-in formatter registry: stable ids, deterministic order and lookup, safe fallback.</summary>
public class OutputFormatterRegistryTests
{
    [Fact]
    public void BuiltinIds_AreStableAndLowercase()
    {
        Assert.Equal("exact", OutputFormatters.Exact.Id);
        Assert.Equal("readable", OutputFormatters.Readable.Id);
        Assert.Equal("concise", OutputFormatters.Concise.Id);
    }

    [Fact]
    public void All_HasDeterministicOrderAndNoDuplicates()
    {
        Assert.Equal(
            ["exact", "readable", "concise"],
            OutputFormatters.All.Take(3).Select(f => f.Id).ToArray());
        Assert.Equal(
            OutputFormatters.All.Count,
            OutputFormatters.All.Select(f => f.Id).Distinct(StringComparer.Ordinal).Count());

        // The registry exposes the same instances on every read.
        Assert.Same(OutputFormatters.All[0], OutputFormatters.Exact);
        Assert.Same(OutputFormatters.All[1], OutputFormatters.Readable);
        Assert.Same(OutputFormatters.All[2], OutputFormatters.Concise);
        Assert.Equal(
            OutputFormatters.All.Select(f => f.Id),
            OutputFormatters.All.Select(f => f.Id));
    }

    [Fact]
    public void TryGet_FindsEveryBuiltinById()
    {
        foreach (var builtin in OutputFormatters.All)
        {
            Assert.True(OutputFormatters.TryGet(builtin.Id, out var found));
            Assert.Same(builtin, found);
        }
    }

    [Theory]
    [InlineData(null)]
    [InlineData("")]
    [InlineData("unknown")]
    [InlineData("Exact")]      // lookup is ordinal and case-sensitive
    [InlineData(" exact")]
    [InlineData("exact ")]
    public void TryGet_UnknownIds_ReturnFalse(string? id)
    {
        Assert.False(OutputFormatters.TryGet(id, out var formatter));
        Assert.Null(formatter);
    }

    [Fact]
    public void GetOrDefault_FallsBackToExact()
    {
        Assert.Same(OutputFormatters.Readable, OutputFormatters.GetOrDefault("readable"));
        Assert.Same(OutputFormatters.Exact, OutputFormatters.GetOrDefault("no-such-formatter"));
        Assert.Same(OutputFormatters.Exact, OutputFormatters.GetOrDefault(null));
    }

    [Fact]
    public void GetOrDefault_HonorsCallerSuppliedFallback()
    {
        Assert.Same(OutputFormatters.Concise, OutputFormatters.GetOrDefault("missing", OutputFormatters.Concise));
        Assert.Same(OutputFormatters.Readable, OutputFormatters.GetOrDefault("readable", OutputFormatters.Concise));
        Assert.Throws<ArgumentNullException>(() => OutputFormatters.GetOrDefault("exact", null!));
    }

    [Fact]
    public void BuiltinInstances_AreStatelessAndReusableAcrossCallsAndThreads()
    {
        var run = KatLangEngine.Run("(1, 2), (3, 4)");
        var expected = new string[3];
        for (var i = 0; i < OutputFormatters.All.Count; i++)
            expected[i] = OutputFormatters.All[i].Format(run);

        var results = new bool[24];
        Parallel.For(0, results.Length, i =>
        {
            var formatterIndex = i % OutputFormatters.All.Count;
            var formatter = OutputFormatters.All[formatterIndex];
            results[i] = formatter.Format(run) == expected[formatterIndex];
        });
        Assert.All(results, Assert.True);
    }

    [Fact]
    public void Format_NullResult_Throws()
        => Assert.Throws<ArgumentNullException>(() => OutputFormatters.Exact.Format(null!));

    [Fact]
    public void ExternalConsumers_CanImplementAFormatterAgainstThePublicSurface()
    {
        var formatter = new RowCountFormatter();
        var text = formatter.Format(KatLangEngine.Run("1, 2, 3"));
        Assert.Equal("rows=3", text);

        // Shared failure handling applies to custom formatters too.
        var failureText = formatter.Format(KatLangEngine.Run("1 / 0"));
        Assert.Contains("zero", failureText, StringComparison.OrdinalIgnoreCase);
    }

    /// <summary>A minimal external formatter using only public API.</summary>
    private sealed class RowCountFormatter : OutputFormatter
    {
        public override string Id => "row-count";

        protected override bool WriteSuccessOutput(
            IReadOnlyList<Result> outputRows,
            OutputFormattingOptions options,
            BoundedOutputWriter writer)
            => writer.Append($"rows={outputRows.Count}");
    }

    [Fact]
    public void EvaluateToString_RemainsTheSeparateAtomProjection()
    {
        // EvaluateToString is not a formatting mode: it stays the space-joined
        // host-atom projection, distinct from every formatter's output shape.
        Assert.Equal("1 2 3", KatLangEngine.EvaluateToString("1, (2, 3)").ReplaceLineEndings("\n"));
        Assert.Equal(
            $"1{Environment.NewLine}(2, 3)",
            OutputFormatters.Exact.Format(KatLangEngine.Run("1, (2, 3)")));
    }
}
