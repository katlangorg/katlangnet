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

    [Theory]
    [InlineData("ä")]
    [InlineData("😀")]
    [InlineData("e\u0301")]
    public void Unicode_IsChargedAsUtf16Units(string value)
    {
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run($"'{value}'"));
        foreach (var formatter in OutputFormatters.All)
        {
            var exact = formatter.RenderDisplay(run, Options(value.Length));
            AssertWithinLimit(exact);
            Assert.Equal(value, exact.Text);
            Assert.Equal(formatter.Format(run, Options(value.Length)), exact.Text);

            var overflow = formatter.RenderDisplay(run, Options(value.Length - 1));
            AssertReportsOverflow(overflow, value.Length - 1);
            Assert.Equal(OverflowResponse(value.Length - 1), overflow.Text);
        }
    }

    [Fact]
    public void OverflowState_IsIsolatedToOneFormattingCall()
    {
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run("[111, 222, 333]"));
        foreach (var formatter in OutputFormatters.All)
        {
            var first = formatter.RenderDisplay(run, Options(3));
            AssertReportsOverflow(first, 3);
            Assert.Equal("…", first.Text);
            var complete = formatter.RenderDisplay(run, Options(1_000));
            AssertWithinLimit(complete);
            Assert.Equal("[111, 222, 333]", complete.Text);
            var last = formatter.RenderDisplay(run, Options(3));
            AssertReportsOverflow(last, 3);
            Assert.Equal(first.Text, last.Text);

            // Earlier rendering objects retain their own verdict after later calls.
            AssertReportsOverflow(first, 3);
            AssertWithinLimit(complete);
        }
    }

    [Fact]
    public void RenderDisplay_StatusBelongsToTheSelectedFormatter()
    {
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run("'a b'", new RunOptions
        {
            EvaluationLimits = new EvaluationLimits { MaxDisplayLength = 3 },
        }));

        AssertWithinLimit(run.RenderDisplay());
        foreach (var formatter in new[] { OutputFormatters.Readable, OutputFormatters.Concise })
        {
            // Quoting costs two units, while canonical raw display fits exactly.
            AssertReportsOverflow(formatter.RenderDisplay(run), 3);
            var raw = formatter.RenderDisplay(run, new OutputFormattingOptions
            {
                StringDelimiters = StringDelimiterMode.Never,
            });
            AssertWithinLimit(raw);
            Assert.Equal("a b", raw.Text);
        }
        AssertWithinLimit(run.RenderDisplay());
        AssertWithinLimit(OutputFormatters.Exact.RenderDisplay(run));

        var sequence = Assert.IsType<RunResult.Success>(KatLangEngine.Run("(10, 20)", new RunOptions
        {
            EvaluationLimits = new EvaluationLimits { MaxDisplayLength = 5 },
        }));
        AssertReportsOverflow(sequence.RenderDisplay(), 5);
        var concise = OutputFormatters.Concise.RenderDisplay(sequence);
        AssertWithinLimit(concise);
        Assert.Equal("10 20", concise.Text);
        AssertReportsOverflow(sequence.RenderDisplay(), 5);
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

    // ── The structured overflow signal ──────────────────────────────────────

    private static void AssertReportsOverflow(DisplayRendering rendering, int effectiveLimit)
    {
        Assert.True(rendering.LimitExceeded);
        Assert.NotNull(rendering.LimitError);
        Assert.Equal(KatLangErrorCode.DisplayLengthLimitExceeded, rendering.LimitError.Code);
        Assert.True(rendering.LimitError.IsResourceLimit);
        Assert.Equal(
            effectiveLimit,
            Assert.IsType<EvalError.DisplayLengthLimitExceeded>(rendering.LimitError.Source).Limit);
    }

    private static void AssertWithinLimit(DisplayRendering rendering)
    {
        Assert.False(rendering.LimitExceeded);
        Assert.Null(rendering.LimitError);
    }

    [Fact]
    public void EveryFormatter_RenderDisplay_FlagsExactlyTheRefusedRenderings_AndProjectsToFormat()
    {
        const string source = "1, 2, 3";
        foreach (var formatter in OutputFormatters.All)
        {
            var run = KatLangEngine.Run(source);
            var natural = formatter.Format(run, Options(int.MaxValue));

            for (var limit = 0; limit <= natural.Length + 2; limit++)
            {
                var rendering = formatter.RenderDisplay(run, Options(limit));
                Assert.Equal(formatter.Format(run, Options(limit)), rendering.Text);
                if (limit < natural.Length)
                {
                    AssertReportsOverflow(rendering, limit);
                    Assert.Equal(OverflowResponse(limit), rendering.Text);
                }
                else
                {
                    AssertWithinLimit(rendering);
                    Assert.Equal(natural, rendering.Text);
                }
            }
        }
    }

    [Fact]
    public void RenderDisplay_NamesTheEffectiveLimit_WhichAPerCallOptionCanOnlyLower()
    {
        // Six digits exceed the limit even before separators. The exact formatter
        // uses platform newlines: "1, 2, 3" fits five units on LF but not on CRLF.
        var run = KatLangEngine.Run(
            "11, 22, 33",
            new RunOptions { EvaluationLimits = new EvaluationLimits { MaxDisplayLength = 5 } });

        foreach (var formatter in OutputFormatters.All)
        {
            // A larger per-call option cannot raise the run's limit: its own 5 is enforced and reported.
            AssertReportsOverflow(formatter.RenderDisplay(run, Options(1_000)), 5);
            // A smaller one lowers it, and the report names the limit actually enforced.
            AssertReportsOverflow(formatter.RenderDisplay(run, Options(3)), 3);
        }
    }

    [Fact]
    public void RenderDisplay_FailureAndNoOutputRendering_ReportOverflowLikeCanonicalDisplay()
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
                var canonical = run.RenderDisplay();
                Assert.Equal(limit < naturalLength, canonical.LimitExceeded);
                foreach (var formatter in OutputFormatters.All)
                {
                    var rendering = formatter.RenderDisplay(run);
                    Assert.Equal(canonical.Text, rendering.Text);
                    Assert.Equal(canonical.LimitExceeded, rendering.LimitExceeded);
                    if (rendering.LimitExceeded)
                        AssertReportsOverflow(rendering, limit);
                }
            }
        }
    }

    [Fact]
    public void RenderDisplay_OutputEqualToTheOverflowResponse_IsNotOverflow_ForEveryFormatter()
    {
        // A program whose genuine output is the limit message renders (under exact display)
        // byte-identically to an overflow under that limit; only the structured signal
        // tells them apart, so it must stay silent here for every formatter.
        const int limit = 200;
        var genuine = KatLangEngine.Run($"'{OverflowResponse(limit)}'");
        foreach (var formatter in OutputFormatters.All)
        {
            var rendering = formatter.RenderDisplay(genuine, Options(limit));
            AssertWithinLimit(rendering);
            Assert.Equal(formatter.Format(genuine, Options(limit)), rendering.Text);
        }

        var genuineText = OutputFormatters.Exact.RenderDisplay(genuine, Options(limit));
        var overflow = OutputFormatters.Exact.RenderDisplay(KatLangEngine.Run("range(1, 100)"), Options(limit));
        Assert.Equal(genuineText.Text, overflow.Text);   // identical text...
        AssertWithinLimit(genuineText);                   // ...opposite verdicts
        AssertReportsOverflow(overflow, limit);
    }
}
