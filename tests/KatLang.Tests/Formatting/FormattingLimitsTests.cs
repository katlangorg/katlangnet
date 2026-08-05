using KatLang.Formatting;

namespace KatLang.Tests.Formatting;

/// <summary>
/// Every formatter honors the effective display-length limit with the
/// established all-or-nothing contract: the returned string never exceeds the
/// limit, indentation/quotes/newlines/blank lines are charged like every other
/// code unit, and over-limit rendering returns the complete bounded overflow
/// response instead of truncated output.
/// </summary>
public class FormattingLimitsTests
{
    private static string OverflowResponse(int limit)
    {
        var message = KatLangError.FromEvalError(new EvalError.DisplayLengthLimitExceeded(limit)).Message;
        if (message.Length <= limit) return message;
        return limit >= 1 ? "…" : string.Empty;
    }

    private static OutputFormattingOptions Options(int limit, int width = 100, int spacing = 1)
        => new()
        {
            MaxDisplayLength = limit,
            PreferredLineWidth = width,
            RootOutputSpacing = spacing,
            NewLine = "\n",
        };

    [Fact]
    public void EveryFormatter_SweepsTheLimitAllOrNothing()
    {
        const string source = "1, 2, 3";
        foreach (var formatter in OutputFormatters.All)
        {
            var run = KatLangEngine.Run(source);
            var natural = formatter.Format(run, Options(int.MaxValue));

            for (var limit = 0; limit <= natural.Length + 2; limit++)
            {
                var text = formatter.Format(run, Options(limit));
                Assert.True(text.Length <= limit, $"{formatter.Id}: limit {limit} returned {text.Length} units.");
                Assert.Equal(limit >= natural.Length ? natural : OverflowResponse(limit), text);
            }
        }
    }

    [Fact]
    public void Indentation_IsCharged()
    {
        // "(\n  10,\n  20,\n  30\n)" is exactly 20 units, six of them indentation.
        var run = KatLangEngine.Run("(10, 20, 30)");
        Assert.Equal(
            "(\n  10,\n  20,\n  30\n)",
            OutputFormatters.Readable.Format(run, Options(20, width: 8)));
        Assert.Equal(
            OverflowResponse(19),
            OutputFormatters.Readable.Format(run, Options(19, width: 8)));
    }

    [Fact]
    public void QuoteDelimiters_AreCharged()
    {
        var run = KatLangEngine.Run("''");
        Assert.Equal("''", OutputFormatters.Readable.Format(run, Options(2)));
        Assert.Equal(OverflowResponse(1), OutputFormatters.Readable.Format(run, Options(1)));
    }

    [Fact]
    public void CustomNewLines_AreChargedTheirActualLength()
    {
        // "1\r\n\r\n2" is 6 units: the two-unit newline is charged twice.
        var run = KatLangEngine.Run("1, 2");
        var options = new OutputFormattingOptions { NewLine = "\r\n", MaxDisplayLength = 6 };
        Assert.Equal("1\r\n\r\n2", OutputFormatters.Readable.Format(run, options));
        Assert.Equal(
            OverflowResponse(5),
            OutputFormatters.Readable.Format(run, options with { MaxDisplayLength = 5 }));
    }

    [Fact]
    public void BlankRootSeparators_AreCharged()
    {
        // Spacing 3 → "1\n\n\n\n2" = 6 units.
        var run = KatLangEngine.Run("1, 2");
        Assert.Equal("1\n\n\n\n2", OutputFormatters.Readable.Format(run, Options(6, spacing: 3)));
        Assert.Equal(
            OverflowResponse(5),
            OutputFormatters.Readable.Format(run, Options(5, spacing: 3)));
    }

    [Fact]
    public void PreservedUnderscores_AreOrdinaryChargedUnits()
    {
        var run = KatLangEngine.Run("'a_b'");
        foreach (var formatter in new[] { OutputFormatters.Exact, OutputFormatters.Concise })
        {
            Assert.Equal("a_b", formatter.Format(run, Options(3)));
            Assert.Equal(OverflowResponse(2), formatter.Format(run, Options(2)));
        }
    }

    [Fact]
    public void OverflowIsNeverPartial()
    {
        var run = KatLangEngine.Run("[111, 222, 333]");
        foreach (var formatter in OutputFormatters.All)
        {
            var text = formatter.Format(run, Options(10));
            Assert.Equal("…", text);
            Assert.DoesNotContain("111", text, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void OptionLimit_CanOnlyLowerTheRunLimit()
    {
        // The run itself was evaluated with a display limit of 5; a larger
        // per-call option cannot raise it.
        var run = KatLangEngine.Run(
            "1, 2, 3",
            new RunOptions { EvaluationLimits = new EvaluationLimits { MaxDisplayLength = 5 } });

        foreach (var formatter in OutputFormatters.All)
        {
            var text = formatter.Format(run, Options(1_000));
            Assert.True(text.Length <= 5, $"{formatter.Id} exceeded the run's own limit.");
        }
    }

    [Fact]
    public void FailureAndNoOutputRendering_AreBoundedForEveryFormatter()
    {
        foreach (var source in new[] { ")(", "1 div 0", "Value = 1" })
        {
            var naturalLength = KatLangEngine.Run(source).ToDisplayString().Length;
            for (var limit = 0; limit <= naturalLength + 2; limit++)
            {
                var run = KatLangEngine.Run(source, new RunOptions
                {
                    EvaluationLimits = new EvaluationLimits { MaxDisplayLength = limit },
                });
                foreach (var formatter in OutputFormatters.All)
                {
                    var text = formatter.Format(run);
                    Assert.True(text.Length <= limit, $"{formatter.Id}, limit {limit}, length {text.Length}");
                    Assert.Equal(run.ToDisplayString(), text);
                }
            }
        }
    }

    [Fact]
    public void UnicodeSurrogatePairs_AreChargedAsUtf16Units()
    {
        var run = KatLangEngine.Run("'😀'");
        foreach (var formatter in OutputFormatters.All)
        {
            Assert.Equal("😀", formatter.Format(run, Options(2)));
            Assert.Equal("…", formatter.Format(run, Options(1)));
        }
    }

    [Fact]
    public void OverflowState_IsIsolatedToOneFormattingCall()
    {
        var run = KatLangEngine.Run("[111, 222, 333]");
        foreach (var formatter in OutputFormatters.All)
        {
            Assert.Equal("…", formatter.Format(run, Options(3)));
            var complete = formatter.Format(run, Options(1_000));
            Assert.NotEqual("…", complete);
            Assert.Equal("…", formatter.Format(run, Options(3)));
        }
    }

    [Fact]
    public void PerCallLimit_LowersFailureAndNoOutputRendering()
    {
        foreach (var source in new[] { ")(", "1 div 0", "Value = 1" })
        {
            var run = KatLangEngine.Run(source);
            foreach (var formatter in OutputFormatters.All)
            {
                Assert.Equal("…", formatter.Format(run, Options(1)));
                Assert.Equal(string.Empty, formatter.Format(run, Options(0)));
            }
        }
    }
}
