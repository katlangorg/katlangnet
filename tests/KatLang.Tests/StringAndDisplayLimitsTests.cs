using KatLang.Evaluation;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// Deterministic limits on language string values and on rendered output.
///
/// <para>Lengths are UTF-16 code units throughout, matching <see cref="string.Length"/>,
/// the source-span column model, and CLR string storage.</para>
///
/// <para>Note that KatLang has no string concatenation operator, so a source program
/// cannot grow a string: the per-string ceiling is defence in depth (and guards
/// hand-built ASTs), while the RENDERED-output limit is the one that closes a real
/// compact-source path — display flattens a value recursively, so a value that is legal
/// under every evaluation limit can still render enormously.</para>
/// </summary>
public class StringAndDisplayLimitsTests
{
    private static EvalResult<Result> Eval(string source, EvaluationLimits? limits = null)
        => Evaluator.Run(new Expr.Block(Parser.Parse(source).Root), limits);

    private static EvalError ErrorOf(string source, EvaluationLimits? limits = null)
    {
        var result = Eval(source, limits);
        if (!result.IsError)
            Assert.Fail($"expected a structured error, got {result.Value}");
        return Innermost(result.Error);
    }

    /// <summary>Unwraps ordinary call/property context frames to the underlying error.</summary>
    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext withContext)
            error = withContext.Inner;
        return error;
    }

    private static string Display(string source, EvaluationLimits? limits = null)
        => KatLangEngine.Run(source, new RunOptions { EvaluationLimits = limits }).ToDisplayString();

    private static EvaluationLimits Display(int maxDisplayLength) => new() { MaxDisplayLength = maxDisplayLength };

    private static EvaluationLimits Str(int maxStringLength) => new() { MaxStringLength = maxStringLength };

    private static Expr BuildStringRepeatAst(string value, long count)
    {
        var parsed = Parser.Parse($"Step(x) = 'placeholder'\nStep.repeat({count}, 0)").Root;
        var properties = parsed.Properties.Select(property =>
        {
            if (property.Name != "Step") return property;
            var step = Assert.IsType<Algorithm.User>(property.Value);
            return property with
            {
                Value = step with { Output = [new Expr.StringLiteral(value)] },
            };
        }).ToList();

        return new Expr.Block(parsed with { Properties = properties });
    }

    private static (EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget) ObserveStringRepeat(
        string value,
        long count,
        EvaluationLimits? limits,
        bool optimized)
        => Evaluator.RunCountedObserved(
            BuildStringRepeatAst(value, count),
            limits,
            enableOptimizations: optimized);

    private const string LimitPrefix = "Display output limit of";

    // ── Configuration ────────────────────────────────────────────────────────

    [Theory]
    [InlineData(-1)]
    [InlineData(int.MinValue)]
    public void NegativeLimits_Throw(int value)
    {
        Assert.Throws<ArgumentOutOfRangeException>(() => new EvaluationLimits { MaxStringLength = value });
        Assert.Throws<ArgumentOutOfRangeException>(() => new EvaluationLimits { MaxDisplayLength = value });
        Assert.Throws<ArgumentOutOfRangeException>(() => new EvaluationLimits { MaxMaterializedStringChars = value });
    }

    [Fact]
    public void ZeroLimits_AreLegalAndRejectEverything()
    {
        // Zero is a meaningful configuration here (unlike depth): no string may be created
        // and nothing may be rendered.
        Assert.IsType<EvalError.StringSizeLimitExceeded>(ErrorOf("'a'", Str(0)));
        Assert.Equal(string.Empty, Display("1", Display(0)));
    }

    [Fact]
    public void Defaults_AreTheSupportedCeilings()
    {
        Assert.Null(EvaluationLimits.Default.MaxStringLength);
        Assert.Null(EvaluationLimits.Default.MaxDisplayLength);
        Assert.Null(EvaluationLimits.Default.MaxMaterializedStringChars);
        Assert.Equal(EvaluationLimits.MaxSupportedStringLength, EvaluationLimits.Default.EffectiveMaxStringLength);
        Assert.Equal(EvaluationLimits.MaxSupportedDisplayLength, EvaluationLimits.Default.EffectiveMaxDisplayLength);
    }

    [Fact]
    public void AboveSupportedMaximum_IsClampedDown()
    {
        Assert.Equal(
            EvaluationLimits.MaxSupportedStringLength,
            new EvaluationLimits { MaxStringLength = int.MaxValue }.EffectiveMaxStringLength);
        Assert.Equal(
            EvaluationLimits.MaxSupportedDisplayLength,
            new EvaluationLimits { MaxDisplayLength = int.MaxValue }.EffectiveMaxDisplayLength);
    }

    [Fact]
    public void RepeatedAndConcurrentRuns_SharingOneOptionsInstance_EachStartFresh()
    {
        var options = new RunOptions { EvaluationLimits = new EvaluationLimits { MaxMaterializedStringChars = 12 } };
        const string source = "'abc', 'abc'";

        for (var i = 0; i < 3; i++)
            Assert.False(KatLangEngine.Run(source, options) is RunResult.EvalFailure);

        var results = new bool[16];
        Parallel.For(0, results.Length, i => results[i] = KatLangEngine.Run(source, options) is RunResult.Success);
        Assert.All(results, Assert.True);
    }

    // ── Language strings ─────────────────────────────────────────────────────

    [Fact]
    public void StringLiteral_ExactlyAtLimit_Succeeds()
        => Assert.False(Eval("'abc'", Str(3)).IsError);

    [Fact]
    public void StringLiteral_OneOverLimit_ReportsRequestedLength()
    {
        var limit = Assert.IsType<EvalError.StringSizeLimitExceeded>(ErrorOf("'abcd'", Str(3)));
        Assert.Equal(3, limit.Limit);
        Assert.Equal(4L, limit.Requested);
    }

    [Fact]
    public void EmptyStringLiteral_CostsNothing()
        => Assert.False(Eval("''", Str(0)).IsError);

    [Fact]
    public void StringLiteralError_CarriesItsSourceSpan()
        => Assert.NotNull(ErrorOf("'abcd'", Str(3)).Span);

    [Fact]
    public void NumericStringConversion_IsChargedThroughTheSameCeiling()
    {
        Assert.False(Eval("12345.string", Str(5)).IsError);
        Assert.IsType<EvalError.StringSizeLimitExceeded>(ErrorOf("12345.string", Str(4)));
    }

    [Fact]
    public void StringsThroughCallbacksAndLoops_AreCharged()
    {
        Assert.IsType<EvalError.StringSizeLimitExceeded>(
            ErrorOf("ToText(x) = x.string\n[12345].map(ToText)", Str(4)));
        Assert.IsType<EvalError.StringSizeLimitExceeded>(
            ErrorOf("Step(x) = 'abcd', 0\nStep.while(1)", Str(3)));
    }

    [Fact]
    public void OptimizedLoop_StringLiteralUsesTheAlwaysActiveCheckedConstructionPath()
    {
        var oversized = new string('x', EvaluationLimits.MaxSupportedStringLength + 1);
        foreach (var limits in new EvaluationLimits?[]
                 {
                     null,
                     new EvaluationLimits { MaxStringLength = EvaluationLimits.MaxSupportedStringLength },
                 })
        {
            foreach (var optimized in new[] { false, true })
            {
                var observed = ObserveStringRepeat(oversized, 1, limits, optimized);
                var error = Assert.IsType<EvalError.StringSizeLimitExceeded>(observed.Result.Error);
                Assert.Equal(EvaluationLimits.MaxSupportedStringLength, error.Limit);
                Assert.Equal(oversized.Length, error.Requested);
                Assert.Equal(0, observed.Budget.MaterializedStringChars);
            }
        }

        foreach (var optimized in new[] { false, true })
        {
            var observed = ObserveStringRepeat("abcd", 1, Str(3), optimized);
            Assert.IsType<EvalError.StringSizeLimitExceeded>(observed.Result.Error);
            Assert.Equal(0, observed.Budget.MaterializedStringChars);
        }
    }

    [Fact]
    public void OptimizedLoop_StringLiteralChargesEveryLogicalEvaluation()
    {
        foreach (var optimized in new[] { false, true })
        {
            var exact = ObserveStringRepeat(
                "abc",
                2,
                new EvaluationLimits { MaxMaterializedStringChars = 6 },
                optimized);
            Assert.False(exact.Result.IsError);
            Assert.Equal(6, exact.Budget.MaterializedStringChars);

            var failure = ObserveStringRepeat(
                "abc",
                2,
                new EvaluationLimits { MaxMaterializedStringChars = 5 },
                optimized);
            Assert.IsType<EvalError.StringMaterializationLimitExceeded>(failure.Result.Error);
            Assert.Equal(3, failure.Budget.MaterializedStringChars);
        }
    }

    [Fact]
    public void ConfiguredStringBudget_DoesNotDisableLoopOptimization()
    {
        var diagnostics = new LoopOptimizationDiagnostics();
        var result = Evaluator.Run(
            BuildStringRepeatAst("abc", 2),
            new KatLang.Evaluation.Caching.RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true,
            diagnostics,
            new EvaluationLimits { MaxMaterializedStringChars = 6 });

        Assert.False(result.IsError);
        var stats = diagnostics.GetSnapshot();
        Assert.Equal(1, stats.OptimizedLoopHits);
        Assert.Equal(2, stats.PlannedExpressionHits);
        Assert.Equal(0, stats.PlannedExpressionFallbacks);
        Assert.Equal(0, stats.GenericExpressionEvaluationsInsideOptimizedLoops);
    }

    [Fact]
    public void KatLangHasNoStringConcatenation_SoStringsCannotGrow()
    {
        // The reason the per-string ceiling is defence in depth rather than the closure of
        // a compact-source path: there is no operation that makes a longer string.
        var error = ErrorOf("'ab' + 'cd'");
        Assert.Contains("Strings only support", Assert.IsType<EvalError.TypeMismatch>(error).Message);
    }

    // ── Unicode ──────────────────────────────────────────────────────────────

    [Fact]
    public void AsciiAndBmpCharacters_CostOneUnitEach()
    {
        Assert.False(Eval("'abc'", Str(3)).IsError);
        Assert.False(Eval("'äöü'", Str(3)).IsError);
        Assert.IsType<EvalError.StringSizeLimitExceeded>(ErrorOf("'äöü'", Str(2)));
    }

    [Fact]
    public void SurrogatePairs_CostTwoUnitsEach()
    {
        // One supplementary-plane character is two UTF-16 code units, matching
        // string.Length — the unit this limit is defined in.
        const string source = "'\U0001D54F'";
        Assert.False(Eval(source, Str(2)).IsError);
        Assert.IsType<EvalError.StringSizeLimitExceeded>(ErrorOf(source, Str(1)));
    }

    [Fact]
    public void CombiningSequences_CostOneUnitPerCodeUnit()
    {
        const string source = "'é'";      // e + combining acute = 2 units
        Assert.False(Eval(source, Str(2)).IsError);
        Assert.IsType<EvalError.StringSizeLimitExceeded>(ErrorOf(source, Str(1)));
    }

    // ── Cumulative string materialization ────────────────────────────────────

    [Fact]
    public void CumulativeStringBudget_ExactBoundary()
    {
        var limits = new EvaluationLimits { MaxMaterializedStringChars = 6 };
        Assert.False(Eval("'abc', 'abc'", limits).IsError);
        Assert.IsType<EvalError.StringMaterializationLimitExceeded>(
            ErrorOf("'abc', 'abc', 'a'", limits));
    }

    [Fact]
    public void CumulativeStringBudget_CachedPropertyReuse_DoesNotRepay()
    {
        var limits = new EvaluationLimits { MaxMaterializedStringChars = 3 };
        Assert.False(Eval("Text = 'abc'\nText, Text, Text", limits).IsError);
        Assert.IsType<EvalError.StringMaterializationLimitExceeded>(
            ErrorOf("'abc', 'abc'", limits));
    }

    [Fact]
    public void FailedStringReservation_DoesNotCorruptTheRunTotal()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxStringLength = 10, MaxMaterializedStringChars = 10 });
        Assert.Null(budget.TryReserveString(4));
        Assert.IsType<EvalError.StringSizeLimitExceeded>(budget.TryReserveString(11));
        Assert.IsType<EvalError.StringMaterializationLimitExceeded>(budget.TryReserveString(7));
        Assert.Equal(4, budget.MaterializedStringChars);
        Assert.Null(budget.TryReserveString(6));
        Assert.Equal(10, budget.MaterializedStringChars);
    }

    // ── Rendering: output is identical below the limit ───────────────────────

    [Theory]
    [InlineData("1", "1")]
    [InlineData("'text'", "text")]
    [InlineData("()", "()")]
    [InlineData("[]", "[]")]
    [InlineData("(1, 2, 3)", "(1, 2, 3)")]
    [InlineData("[1, 2, 3]", "[1, 2, 3]")]
    [InlineData("[(1, 2), [3, [4]]]", "[(1, 2), [3, [4]]]")]
    [InlineData("[[], ()]", "[[], ()]")]
    [InlineData("DisplayDecimals = 2\n1.5", "1.50")]
    public void Rendering_BelowTheLimit_IsUnchanged(string source, string expected)
    {
        Assert.Equal(expected, Display(source));
        Assert.Equal(expected, Display(source, Display(EvaluationLimits.MaxSupportedDisplayLength)));
    }

    [Fact]
    public void MultiRowOutput_RendersEveryRow()
        => Assert.Equal($"1{Environment.NewLine}2{Environment.NewLine}3", Display("1, 2, 3"));

    // ── Rendering: exact boundaries ──────────────────────────────────────────

    [Fact]
    public void Rendering_ExactlyAtTheLimit_Succeeds()
        => Assert.Equal("[1, 2, 3]", Display("[1, 2, 3]", Display(9)));

    [Fact]
    public void Rendering_OneOverTheLimit_UsesBoundedMarker()
    {
        var text = Display("[1, 2, 3]", Display(8));
        Assert.Equal("…", text);
        Assert.True(text.Length <= 8);
    }

    [Fact]
    public void SeparatorsAndDelimiters_CountTowardTheLimit()
    {
        // "[1, 2]" is 6 units: two atoms, two brackets, and a two-unit separator.
        Assert.Equal("[1, 2]", Display("[1, 2]", Display(6)));
        Assert.Equal("…", Display("[1, 2]", Display(5)));
    }

    [Fact]
    public void RowSeparators_AreChargedTheirActualLength()
    {
        // The bound is exact on the RETURNED string, so a row separator costs what it
        // actually occupies: two units on a CRLF host, one on an LF host. Charging a
        // canonical single unit would have let the returned text exceed a limit that is
        // defined in UTF-16 code units.
        var exact = 2 + Environment.NewLine.Length;
        Assert.Equal($"1{Environment.NewLine}2", Display("1, 2", Display(exact)));
        Assert.Equal("…", Display("1, 2", Display(exact - 1)));
    }

    [Theory]
    [InlineData("1, 2, 3, 4, 5")]
    [InlineData("[1, 2, 3], [4, 5, 6]")]
    [InlineData("'abc', 'def', 'ghi'")]
    public void RenderedText_NeverExceedsTheConfiguredLimit(string source)
    {
        // Sweep every limit around the natural length: the contract is unconditional.
        var natural = Display(source).Length;
        for (var limit = 0; limit <= natural + 2; limit++)
        {
            var text = Display(source, Display(limit));
            Assert.True(text.Length <= limit, $"limit {limit} returned {text.Length} units.");
        }
    }

    [Fact]
    public void EveryRunResultVariant_AndEvaluateToString_ObeyTheSameStrictLimit()
    {
        var cases = new (string Source, Type ExpectedType)[]
        {
            ("[(1, 2), [3, [4]]]", typeof(RunResult.Success)),
            (")(", typeof(RunResult.ParseFailure)),
            ("1 div 0", typeof(RunResult.EvalFailure)),
            ("Value = 1", typeof(RunResult.NoProgramOutput)),
        };

        foreach (var (source, expectedType) in cases)
        {
            var naturalResult = KatLangEngine.Run(source);
            Assert.Equal(expectedType, naturalResult.GetType());
            var naturalLength = naturalResult.ToDisplayString().Length;
            for (var limit = 0; limit <= naturalLength + 2; limit++)
            {
                var options = new RunOptions { EvaluationLimits = Display(limit) };
                var result = KatLangEngine.Run(source, options);
                Assert.Equal(expectedType, result.GetType());
                var first = result.ToDisplayString();
                var second = result.ToDisplayString();
                Assert.Equal(first, second);
                Assert.True(first.Length <= limit, $"{result.GetType().Name}, limit {limit}, length {first.Length}");

                var evaluated = KatLangEngine.EvaluateToString(source, options);
                Assert.True(evaluated.Length <= limit, $"EvaluateToString, limit {limit}, length {evaluated.Length}");
            }
        }
    }

    [Fact]
    public void ManuallyConstructedResults_UseTheDefaultHardDisplayCeiling()
    {
        var success = new RunResult.Success(
            new Algorithm.User(null, [], [], [], []),
            new Result.Str(new string('x', EvaluationLimits.MaxSupportedDisplayLength + 1)),
            []);

        Assert.True(success.ToDisplayString().Length <= EvaluationLimits.MaxSupportedDisplayLength);
    }

    [Fact]
    public void OverflowReplacement_IsItselfStrictlyBounded()
    {
        Assert.Equal(string.Empty, Display("1, 2, 3", Display(0)));
        Assert.Equal("…", Display("1, 2, 3", Display(1)));

        var longOutput = "'" + new string('x', 200) + "'";
        var completeMessage = Display(longOutput, Display(100));
        Assert.StartsWith(LimitPrefix, completeMessage);
        Assert.True(completeMessage.Length <= 100);
    }

    [Fact]
    public void OverLimitRendering_IsNeverPartialOrTruncated()
    {
        var text = Display("[111, 222, 333]", Display(10));
        Assert.Equal("…", text);
        Assert.DoesNotContain("111", text);
    }

    // ── Rendering: the compact-source reproducer ─────────────────────────────

    private const string NestedStringDoubling =
        "ToText(x) = x.string\nValues = range(1, 200).map(ToText)\n"
        + "L0 = [Values, Values]\nL1 = [L0, L0]\nL2 = [L1, L1]\nL3 = [L2, L2]\nL4 = [L3, L3]\n"
        + "L4";

    [Fact]
    public void NestedSharedValue_EvaluatesButIsRefusedRendering()
    {
        // Every collection here is legal (two item slots per level) and the value has NO
        // host atoms, so no evaluation limit sees it grow — only rendering doubles.
        var result = KatLangEngine.Run(NestedStringDoubling, new RunOptions { EvaluationLimits = Display(1_000) });

        var success = Assert.IsType<RunResult.Success>(result);      // evaluation is unaffected
        Assert.StartsWith(LimitPrefix, success.ToDisplayString());   // rendering is refused
    }

    [Fact]
    public void RunRemainsUsableWithoutRendering()
    {
        // A caller that only wants structured values is never limited by display.
        var success = Assert.IsType<RunResult.Success>(
            KatLangEngine.Run(NestedStringDoubling, new RunOptions { EvaluationLimits = Display(1) }));
        Assert.IsType<Result.ListValue>(success.Value);
        Assert.Equal(2, ((Result.ListValue)success.Value).Items.Count);
    }

    [Fact]
    public void DeeplyNestedValues_RenderIterativelyWithoutStackGrowth()
    {
        // Host-constructed values nest far deeper than the parser allows, so rendering must
        // not recurse per level. 50,000 levels renders to 100,001 units — inside the default
        // ceiling — so this succeeding IS the evidence: the previous recursive renderer
        // would have exhausted the stack long before reaching any limit.
        Result value = new Result.Atom(1);
        for (var i = 0; i < 50_000; i++)
            value = Result.ListValue.TakeOwnership([value]);

        var success = new RunResult.Success(
            new Algorithm.User(null, [], [], [], []), value, []);

        var text = success.ToDisplayString();
        Assert.Equal(100_001, text.Length);
        Assert.StartsWith("[[[", text);
    }

    // ── API surfaces ─────────────────────────────────────────────────────────

    [Fact]
    public void EvaluateToString_IsBounded()
    {
        Assert.Equal("1 2 3", KatLangEngine.EvaluateToString("1, 2, 3"));
        Assert.Equal(
            "…",
            KatLangEngine.EvaluateToString(
                "1, 2, 3",
                new RunOptions { EvaluationLimits = Display(4) }));
        var longOutput = string.Join(", ", Enumerable.Range(1, 100));
        Assert.StartsWith(
            LimitPrefix,
            KatLangEngine.EvaluateToString(
                longOutput,
                new RunOptions { EvaluationLimits = Display(100) }));
    }

    [Fact]
    public void EvaluateToString_ExactBoundary()
        => Assert.Equal(
            "1 2 3",
            KatLangEngine.EvaluateToString("1, 2, 3", new RunOptions { EvaluationLimits = Display(5) }));

    [Fact]
    public void ErrorRendering_StillReportsEveryDiagnostic()
    {
        // Bounding the rendering surface must not discard diagnostics.
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(")("));
        Assert.NotEmpty(failure.Errors);
        Assert.NotEmpty(failure.ToDisplayString());
    }

    // ── Precedence with the other limits ─────────────────────────────────────

    [Fact]
    public void EvaluatorResourceErrors_RemainStructuredWhenRenderingIsRefused()
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(
            "range(1, 1000)",
            new RunOptions
            {
                EvaluationLimits = new EvaluationLimits { MaxCollectionItems = 10, MaxDisplayLength = 1 },
            }));
        Assert.Contains("Collection size limit", failure.Errors[0].Message);
        Assert.Equal("…", failure.ToDisplayString());
    }

    [Fact]
    public void StringLimit_IsSeparateFromCollectionLimit()
    {
        // Items and UTF-16 code units are different resources: a tiny collection limit does
        // not restrict string length, and a tiny string limit does not restrict item count.
        Assert.False(Eval("'abcdefghij'", new EvaluationLimits { MaxCollectionItems = 1 }).IsError);
        Assert.False(Eval("[1, 2, 3, 4]", new EvaluationLimits { MaxStringLength = 1 }).IsError);
    }
}
