using KatLang.Evaluation;

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
        Assert.IsType<EvalError.StringSizeLimitExceeded>(ErrorOf("Output = 'a'", Str(0)));
        Assert.StartsWith(LimitPrefix, Display("Output = 1", Display(0)));
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
        const string source = "Output = 'abc', 'abc'";

        for (var i = 0; i < 3; i++)
            Assert.False(KatLangEngine.Run(source, options) is RunResult.EvalFailure);

        var results = new bool[16];
        Parallel.For(0, results.Length, i => results[i] = KatLangEngine.Run(source, options) is RunResult.Success);
        Assert.All(results, Assert.True);
    }

    // ── Language strings ─────────────────────────────────────────────────────

    [Fact]
    public void StringLiteral_ExactlyAtLimit_Succeeds()
        => Assert.False(Eval("Output = 'abc'", Str(3)).IsError);

    [Fact]
    public void StringLiteral_OneOverLimit_ReportsRequestedLength()
    {
        var limit = Assert.IsType<EvalError.StringSizeLimitExceeded>(ErrorOf("Output = 'abcd'", Str(3)));
        Assert.Equal(3, limit.Limit);
        Assert.Equal(4L, limit.Requested);
    }

    [Fact]
    public void EmptyStringLiteral_CostsNothing()
        => Assert.False(Eval("Output = ''", Str(0)).IsError);

    [Fact]
    public void StringLiteralError_CarriesItsSourceSpan()
        => Assert.NotNull(ErrorOf("Output = 'abcd'", Str(3)).Span);

    [Fact]
    public void NumericStringConversion_IsChargedThroughTheSameCeiling()
    {
        Assert.False(Eval("Output = 12345.string", Str(5)).IsError);
        Assert.IsType<EvalError.StringSizeLimitExceeded>(ErrorOf("Output = 12345.string", Str(4)));
    }

    [Fact]
    public void StringsThroughCallbacksAndLoops_AreCharged()
    {
        Assert.IsType<EvalError.StringSizeLimitExceeded>(
            ErrorOf("ToText(x) = x.string\nOutput = [12345].map(ToText)", Str(4)));
        Assert.IsType<EvalError.StringSizeLimitExceeded>(
            ErrorOf("Step(x) = 'abcd', 0\nOutput = Step.while(1)", Str(3)));
    }

    [Fact]
    public void KatLangHasNoStringConcatenation_SoStringsCannotGrow()
    {
        // The reason the per-string ceiling is defence in depth rather than the closure of
        // a compact-source path: there is no operation that makes a longer string.
        var error = ErrorOf("Output = 'ab' + 'cd'");
        Assert.Contains("Strings only support", Assert.IsType<EvalError.TypeMismatch>(error).Message);
    }

    // ── Unicode ──────────────────────────────────────────────────────────────

    [Fact]
    public void AsciiAndBmpCharacters_CostOneUnitEach()
    {
        Assert.False(Eval("Output = 'abc'", Str(3)).IsError);
        Assert.False(Eval("Output = 'äöü'", Str(3)).IsError);
        Assert.IsType<EvalError.StringSizeLimitExceeded>(ErrorOf("Output = 'äöü'", Str(2)));
    }

    [Fact]
    public void SurrogatePairs_CostTwoUnitsEach()
    {
        // One supplementary-plane character is two UTF-16 code units, matching
        // string.Length — the unit this limit is defined in.
        const string source = "Output = '\U0001D54F'";
        Assert.False(Eval(source, Str(2)).IsError);
        Assert.IsType<EvalError.StringSizeLimitExceeded>(ErrorOf(source, Str(1)));
    }

    [Fact]
    public void CombiningSequences_CostOneUnitPerCodeUnit()
    {
        const string source = "Output = 'é'";      // e + combining acute = 2 units
        Assert.False(Eval(source, Str(2)).IsError);
        Assert.IsType<EvalError.StringSizeLimitExceeded>(ErrorOf(source, Str(1)));
    }

    // ── Cumulative string materialization ────────────────────────────────────

    [Fact]
    public void CumulativeStringBudget_ExactBoundary()
    {
        var limits = new EvaluationLimits { MaxMaterializedStringChars = 6 };
        Assert.False(Eval("Output = 'abc', 'abc'", limits).IsError);
        Assert.IsType<EvalError.StringMaterializationLimitExceeded>(
            ErrorOf("Output = 'abc', 'abc', 'a'", limits));
    }

    [Fact]
    public void CumulativeStringBudget_CachedPropertyReuse_DoesNotRepay()
    {
        var limits = new EvaluationLimits { MaxMaterializedStringChars = 3 };
        Assert.False(Eval("Text = 'abc'\nOutput = Text, Text, Text", limits).IsError);
        Assert.IsType<EvalError.StringMaterializationLimitExceeded>(
            ErrorOf("Output = 'abc', 'abc'", limits));
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
    [InlineData("Output = 1", "1")]
    [InlineData("Output = 'text'", "text")]
    [InlineData("Output = ()", "()")]
    [InlineData("Output = []", "[]")]
    [InlineData("Output = (1, 2, 3)", "(1, 2, 3)")]
    [InlineData("Output = [1, 2, 3]", "[1, 2, 3]")]
    [InlineData("Output = [(1, 2), [3, [4]]]", "[(1, 2), [3, [4]]]")]
    [InlineData("Output = [[], ()]", "[[], ()]")]
    [InlineData("DisplayDecimals = 2\nOutput = 1.5", "1.50")]
    public void Rendering_BelowTheLimit_IsUnchanged(string source, string expected)
    {
        Assert.Equal(expected, Display(source));
        Assert.Equal(expected, Display(source, Display(EvaluationLimits.MaxSupportedDisplayLength)));
    }

    [Fact]
    public void MultiRowOutput_RendersEveryRow()
        => Assert.Equal($"1{Environment.NewLine}2{Environment.NewLine}3", Display("Output = 1, 2, 3"));

    // ── Rendering: exact boundaries ──────────────────────────────────────────

    [Fact]
    public void Rendering_ExactlyAtTheLimit_Succeeds()
        => Assert.Equal("[1, 2, 3]", Display("Output = [1, 2, 3]", Display(9)));

    [Fact]
    public void Rendering_OneOverTheLimit_ReportsTheLimit()
    {
        var text = Display("Output = [1, 2, 3]", Display(8));
        Assert.Equal("Display output limit of 8 UTF-16 code units was exceeded", text);
    }

    [Fact]
    public void SeparatorsAndDelimiters_CountTowardTheLimit()
    {
        // "[1, 2]" is 6 units: two atoms, two brackets, and a two-unit separator.
        Assert.Equal("[1, 2]", Display("Output = [1, 2]", Display(6)));
        Assert.StartsWith(LimitPrefix, Display("Output = [1, 2]", Display(5)));
    }

    [Fact]
    public void RowSeparators_CountAsExactlyOneUnitOnEveryPlatform()
    {
        // "1" + separator + "2" = 3 charged units regardless of CRLF or LF, so the
        // boundary is platform-independent.
        Assert.Equal($"1{Environment.NewLine}2", Display("Output = 1, 2", Display(3)));
        Assert.StartsWith(LimitPrefix, Display("Output = 1, 2", Display(2)));
    }

    [Fact]
    public void OverLimitRendering_IsNeverPartialOrTruncated()
    {
        var text = Display("Output = [111, 222, 333]", Display(10));
        Assert.StartsWith(LimitPrefix, text);
        Assert.DoesNotContain("111", text);
        Assert.DoesNotContain("…", text);
    }

    // ── Rendering: the compact-source reproducer ─────────────────────────────

    private const string NestedStringDoubling =
        "ToText(x) = x.string\nValues = range(1, 200).map(ToText)\n"
        + "L0 = [Values, Values]\nL1 = [L0, L0]\nL2 = [L1, L1]\nL3 = [L2, L2]\nL4 = [L3, L3]\n"
        + "Output = L4";

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
        Assert.Equal("1 2 3", KatLangEngine.EvaluateToString("Output = 1, 2, 3"));
        Assert.StartsWith(
            LimitPrefix,
            KatLangEngine.EvaluateToString("Output = 1, 2, 3", new RunOptions { EvaluationLimits = Display(4) }));
    }

    [Fact]
    public void EvaluateToString_ExactBoundary()
        => Assert.Equal(
            "1 2 3",
            KatLangEngine.EvaluateToString("Output = 1, 2, 3", new RunOptions { EvaluationLimits = Display(5) }));

    [Fact]
    public void ErrorRendering_StillReportsEveryDiagnostic()
    {
        // Bounding the rendering surface must not discard diagnostics.
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("Output = )("));
        Assert.NotEmpty(failure.Errors);
        Assert.NotEmpty(failure.ToDisplayString());
    }

    // ── Precedence with the other limits ─────────────────────────────────────

    [Fact]
    public void EvaluatorResourceErrors_AreNotReplacedByDisplayLimits()
    {
        // Rendering happens after evaluation, so an evaluator resource error still wins.
        var text = Display(
            "Output = range(1, 1000)",
            new EvaluationLimits { MaxCollectionItems = 10, MaxDisplayLength = 1 });
        Assert.Contains("Collection size limit", text);
    }

    [Fact]
    public void StringLimit_IsSeparateFromCollectionLimit()
    {
        // Items and UTF-16 code units are different resources: a tiny collection limit does
        // not restrict string length, and a tiny string limit does not restrict item count.
        Assert.False(Eval("Output = 'abcdefghij'", new EvaluationLimits { MaxCollectionItems = 1 }).IsError);
        Assert.False(Eval("Output = [1, 2, 3, 4]", new EvaluationLimits { MaxStringLength = 1 }).IsError);
    }
}
