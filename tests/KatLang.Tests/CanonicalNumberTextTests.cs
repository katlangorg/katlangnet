using System.Globalization;
using System.Numerics;
using KatLang.Rendering;

namespace KatLang.Tests;

/// <summary>
/// <see cref="ValueTextRenderer.FormatNumberInvariant"/> is KatLang's ONE numeric
/// presentation owner, and its contract is positional: a finite number renders with
/// full precision and its quantum, never with an exponent marker, so the rendered
/// text is itself a KatLang numeric literal.
///
/// <para>That contract used to be inherited from <c>Decimal128.ToString</c>, which
/// was positional on the .NET 11 preview the project was developed against. .NET 11
/// RC1 implements the IEEE 754 <c>to-scientific-string</c> conversion instead —
/// exponential notation once the exponent is positive or the adjusted exponent drops
/// below -6 — so the same values started printing as <c>1E+34</c> / <c>1E-28</c>,
/// which KatLang's own lexer does not read back as one number. The VALUES were
/// unchanged throughout; only the spelling moved. Every expectation below is derived
/// from the number itself (coefficient digits and exponent), never from the runtime
/// formatter under test.</para>
///
/// <para>The boundary cases are the ones the runtime change exposed: the notation
/// switch on either side, the quantum a positive exponent cannot express positionally,
/// trailing fractional zeros, signed zero, the zero coefficient whose exponent is pure
/// padding, and the precision/exponent extremes.</para>
///
/// <para>The renderer asks the value for its stored QUANTUM exponent
/// (<c>ILogB(GetQuantum(v))</c>) and hands the resulting fractional-digit count to the
/// runtime's fixed-point formatter. <see cref="QuantumExponent_IsTheStoredScale_NotTheLeadingDigitExponent"/>
/// pins that this is the scale and not <c>ILogB(value)</c> — the two differ for every
/// value whose leading digit is not in the units place — so an edit that swapped them
/// fails here rather than silently truncating output.</para>
/// </summary>
public class CanonicalNumberTextTests
{
    private static Decimal128 N(string literal) => Decimal128.Parse(literal, CultureInfo.InvariantCulture);

    private static string Text(string literal) => ValueTextRenderer.FormatNumberInvariant(N(literal));

    /// <summary>
    /// Lays out <c>±coefficient x 10^exponent</c> positionally from the INPUTS alone.
    /// This is the independent oracle: it never consults a Decimal128 formatter, so a
    /// case built from a chosen coefficient and exponent has an expectation the
    /// implementation under test cannot influence.
    /// </summary>
    private static string ExpectedLayout(bool negative, string coefficientDigits, int exponent)
    {
        string integerPart, fractionPart;
        if (exponent >= 0)
        {
            integerPart = coefficientDigits + new string('0', exponent);
            fractionPart = string.Empty;
        }
        else if (coefficientDigits.Length > -exponent)
        {
            integerPart = coefficientDigits[..(coefficientDigits.Length + exponent)];
            fractionPart = coefficientDigits[(coefficientDigits.Length + exponent)..];
        }
        else
        {
            integerPart = "0";
            fractionPart = new string('0', -exponent - coefficientDigits.Length) + coefficientDigits;
        }

        var firstSignificant = 0;
        while (firstSignificant < integerPart.Length - 1 && integerPart[firstSignificant] == '0')
            firstSignificant++;

        return (negative ? "-" : string.Empty)
            + integerPart[firstSignificant..]
            + (fractionPart.Length == 0 ? string.Empty : "." + fractionPart);
    }

    // ── The notation boundary the runtime change moved ──────────────────────

    [Theory]
    // Positive exponent: plain digits, the coefficient padded with its exponent.
    [InlineData("1e34", "10000000000000000000000000000000000")]
    [InlineData("1e33", "1000000000000000000000000000000000")]
    [InlineData("1e30", "1000000000000000000000000000000")]
    [InlineData("123456789e20", "12345678900000000000000000000")]
    [InlineData("-1e34", "-10000000000000000000000000000000000")]
    // Adjusted exponent below -6: leading zeros written out rather than an exponent.
    [InlineData("1e-28", "0.0000000000000000000000000001")]
    [InlineData("1e-7", "0.0000001")]
    [InlineData("-1e-28", "-0.0000000000000000000000000001")]
    // Just inside the band where the runtime already stayed positional; these must
    // pass through byte-identical, which is what makes the expansion a no-op there.
    [InlineData("1e-6", "0.000001")]
    [InlineData("1e0", "1")]
    [InlineData("100", "100")]
    [InlineData("1.50", "1.50")]
    [InlineData("-0.25", "-0.25")]
    public void FiniteNumbers_RenderPositionally(string literal, string expected)
        => Assert.Equal(expected, Text(literal));

    [Theory]
    [InlineData("1e34")]
    [InlineData("1e-28")]
    [InlineData("1e6144")]
    [InlineData("1e-6176")]
    [InlineData("9.999999999999999999999999999999999e6144")]
    [InlineData("1.50")]
    [InlineData("0e3")]
    public void FiniteRendering_CarriesNoExponentMarker(string literal)
    {
        var rendered = Text(literal);
        Assert.DoesNotContain('E', rendered);
        Assert.DoesNotContain('e', rendered);
    }

    // ── Value preservation, checked without the formatter as its own oracle ──

    [Theory]
    [InlineData("1e34")]
    [InlineData("1e-28")]
    [InlineData("2.5e-15")]
    [InlineData("1.50")]
    [InlineData("0.0000001")]
    [InlineData("1e6144")]
    [InlineData("1e-6176")]
    [InlineData("-1e-6176")]
    public void RenderedText_ReparsesToTheSameValue(string literal)
    {
        var value = N(literal);
        var reparsed = N(ValueTextRenderer.FormatNumberInvariant(value));

        // Parsing is a separate code path from formatting, so this does not
        // validate the renderer against itself.
        Assert.True(Decimal128.Equals(value, reparsed));
        Assert.Equal(Decimal128.IsNegative(value), Decimal128.IsNegative(reparsed));
    }

    [Theory]
    // A non-positive exponent is fully expressible positionally, so the quantum
    // survives the round trip as written-out trailing zeros.
    [InlineData("1.50")]
    [InlineData("2.500")]
    [InlineData("1e-28")]
    [InlineData("1e-6176")]
    public void NonPositiveExponent_RoundTripsItsQuantumToo(string literal)
    {
        var value = N(literal);
        Assert.True(Decimal128.HaveSameQuantum(value, N(ValueTextRenderer.FormatNumberInvariant(value))));
    }

    [Fact]
    public void PositiveExponent_RoundTripsTheValueButNotTheQuantum()
    {
        // Documented and inherent: `1e34` and its 35 plain digits are the same
        // number, but positional notation cannot say which trailing zeros are
        // quantum padding. This pins the limit as intended behavior, not a defect.
        var value = N("1e34");
        var reparsed = N(ValueTextRenderer.FormatNumberInvariant(value));

        Assert.True(Decimal128.Equals(value, reparsed));
        Assert.False(Decimal128.HaveSameQuantum(value, reparsed));
    }

    // ── Layout rules the expansion must get exactly right ───────────────────

    [Fact]
    public void ZeroCoefficient_TreatsAPositiveExponentAsPadding()
    {
        // `0e3` is the number zero; its exponent is representation, not value, so
        // the text is `0` and never `0000`.
        Assert.Equal("0", Text("0e3"));
        Assert.Equal("0", Text("0"));
        Assert.Equal("0", Text("0e6144"));
    }

    [Fact]
    public void SignedZero_KeepsItsSignAndScale()
    {
        Assert.Equal("-0", ValueTextRenderer.FormatNumberInvariant(Decimal128.NegativeZero));

        // An underflowed literal keeps the minimum quantum, so it displays its
        // full scale rather than collapsing to `0`.
        var underflowed = ValueTextRenderer.FormatNumberInvariant(-N("0e-6176"));
        Assert.StartsWith("-0.0", underflowed);
        Assert.Equal("-0." + new string('0', 6176), underflowed);
    }

    [Fact]
    public void PrecisionAndExponentExtremes_RenderTheirFullDigitLayout()
    {
        Assert.Equal("1" + new string('0', 6144), Text("1e6144"));
        Assert.Equal("0." + new string('0', 6175) + "1", Text("1e-6176"));
        Assert.Equal(
            new string('9', 34) + new string('0', 6111),
            ValueTextRenderer.FormatNumberInvariant(Decimal128.MaxValue));
        Assert.Equal(
            "-" + new string('9', 34) + new string('0', 6111),
            ValueTextRenderer.FormatNumberInvariant(Decimal128.MinValue));

        // 34 significant digits straddling the decimal point, so neither branch of
        // the layout can quietly drop or duplicate a digit.
        Assert.Equal(
            "0.3333333333333333333333333333333333",
            ValueTextRenderer.FormatNumberInvariant(Decimal128.One / N("3")));
    }

    [Fact]
    public void NonFiniteValues_KeepTheirLiteralSpellings()
    {
        Assert.Equal("NaN", ValueTextRenderer.FormatNumberInvariant(Decimal128.NaN));
        Assert.Equal("Infinity", ValueTextRenderer.FormatNumberInvariant(Decimal128.PositiveInfinity));
        Assert.Equal("-Infinity", ValueTextRenderer.FormatNumberInvariant(Decimal128.NegativeInfinity));
    }

    [Theory]
    [InlineData("1e34")]
    [InlineData("1e-28")]
    [InlineData("1.50")]
    [InlineData("0e3")]
    [InlineData("1e6144")]
    public void CanonicalText_IsAFixedPointUnderReparsing(string literal)
    {
        // Reading the canonical text back and rendering it again must land on the same
        // text. Where the quantum survives the round trip this is exact; where a
        // positive exponent cannot be expressed positionally, the reparsed value has a
        // different quantum yet still renders identically — so display never drifts on
        // a value that has been through the language surface.
        var once = Text(literal);
        Assert.Equal(once, ValueTextRenderer.FormatNumberInvariant(N(once)));
    }

    [Theory]
    [InlineData("fr-FR")]
    [InlineData("ar-SA")]
    [InlineData("sv-SE")]
    public void Rendering_IsCultureIndependent(string culture)
    {
        // Invariant culture alone is not the whole story: the expansion also parses
        // the runtime's exponent digits, which must not pick up an ambient culture's
        // sign or digit shapes.
        var original = CultureInfo.CurrentCulture;
        try
        {
            CultureInfo.CurrentCulture = CultureInfo.GetCultureInfo(culture);
            Assert.Equal("10000000000000000000000000000000000", Text("1e34"));
            Assert.Equal("0.0000000000000000000000000001", Text("1e-28"));
            Assert.Equal("1.50", Text("1.50"));
            Assert.Equal("-0", ValueTextRenderer.FormatNumberInvariant(Decimal128.NegativeZero));
        }
        finally
        {
            CultureInfo.CurrentCulture = original;
        }
    }

    // ── The one owner is actually shared by every numeric surface ───────────

    [Fact]
    public void Display_StringConversion_AndDiagnostics_AgreeOnOneSpelling()
    {
        const string expected = "10000000000000000000000000000000000";

        // Canonical display.
        Assert.Equal(
            expected,
            Assert.IsType<RunResult.Success>(KatLangEngine.Run("1e34")).ToDisplayString());

        // The `string` conversion is language-observable, not presentation: it
        // builds a KatLang string value from the same canonical text.
        Assert.Equal(
            expected,
            Assert.IsType<RunResult.Success>(KatLangEngine.Run("(1e34).string")).ToDisplayString());

        // A diagnostic that quotes the offending VALUE quotes the same spelling
        // (the bounded diagnostic value renderer).
        var quotedValue = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("(1e34, 2) + 1")).Errors[0].Message;
        Assert.Contains($"({expected}, 2)", quotedValue);

        // ...and so does the separate, output-bounded renderer that re-renders the
        // offending EXPRESSION for a diagnostic name.
        Assert.Equal(
            $"{expected} + 1",
            ExprNameRenderer.RenderBinaryDiagnosticName(
                BinaryOp.Add, new Expr.Num(N("1e34")), new Expr.Num(Decimal128.One)));
    }

    [Fact]
    public void RenderedOutput_ReadsBackThroughTheLanguageSurface()
    {
        // End-to-end round trip: display text is valid KatLang source that
        // evaluates to the same display text. `1E+34` would lex as three tokens.
        foreach (var source in new[] { "1e34", "1e-28", "1e6144", "1.50", "0.5 + 0.5", "2 ^ -49" })
        {
            var first = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString();
            var second = Assert.IsType<RunResult.Success>(KatLangEngine.Run(first)).ToDisplayString();
            Assert.Equal(first, second);
        }
    }

    // ── The scale the renderer reads is the QUANTUM exponent ────────────────

    [Theory]
    // coefficient, exponent, the exponent of the leading digit. The two columns
    // differ whenever the leading digit is not in the units place, which is what
    // makes ILogB(value) the wrong quantity to format with.
    [InlineData("150", -2, 0)]
    [InlineData("1234567890123456789012345678901234", -17, 16)]
    [InlineData("1776356839400250464677810668945312", -48, -15)]
    [InlineData("123456789", 20, 28)]
    [InlineData("9999999999999999999999999999999999", 6111, 6144)]
    [InlineData("25", -2, -1)]
    public void QuantumExponent_IsTheStoredScale_NotTheLeadingDigitExponent(
        string coefficient, int exponent, int leadingDigitExponent)
    {
        var value = N($"{coefficient}e{exponent.ToString(CultureInfo.InvariantCulture)}");

        // The quantity the renderer uses is the stored scale we chose...
        Assert.Equal(exponent, Decimal128.ILogB(Decimal128.GetQuantum(value)));
        // ...and it is a DIFFERENT number from the value's own leading-digit exponent.
        Assert.Equal(leadingDigitExponent, Decimal128.ILogB(value));
        Assert.NotEqual(exponent, leadingDigitExponent);

        // Formatting with the wrong one would change the output, so the two are not
        // interchangeable by accident.
        Assert.Equal(
            ExpectedLayout(negative: false, coefficient, exponent),
            ValueTextRenderer.FormatNumberInvariant(value));
    }

    [Theory]
    [InlineData("0", 0)]
    [InlineData("0", 3)]
    [InlineData("0", -2)]
    [InlineData("0", -6176)]
    [InlineData("0", 6111)]
    public void ZeroCarriesAQuantumExponentToo(string coefficient, int exponent)
    {
        // A zero has no leading digit, so only the quantum exponent is defined for it —
        // and it still decides the rendered scale.
        var value = N($"{coefficient}e{exponent.ToString(CultureInfo.InvariantCulture)}");
        Assert.Equal(exponent, Decimal128.ILogB(Decimal128.GetQuantum(value)));
        Assert.Equal(
            ExpectedLayout(negative: false, coefficient, exponent),
            ValueTextRenderer.FormatNumberInvariant(value));
        Assert.Equal(
            ExpectedLayout(negative: true, coefficient, exponent),
            ValueTextRenderer.FormatNumberInvariant(-value));
    }

    // ── Coefficient/exponent-derived cases against the independent oracle ───

    public static TheoryData<bool, string, int> LayoutCases()
    {
        var data = new TheoryData<bool, string, int>();
        foreach (var negative in new[] { false, true })
        {
            // Single-digit coefficients across the notation boundary and beyond it.
            foreach (var exponent in new[] { 0, 1, 3, 6, 7, 20, 33, 34, 6111, -1, -6, -7, -28, -34, -68, -6176 })
                data.Add(negative, "1", exponent);

            // Trailing zeros inside the coefficient: the quantum is part of the value's
            // identity and must survive as written-out digits, never be trimmed.
            foreach (var (coefficient, exponent) in new (string, int)[]
                     { ("150", -2), ("2500", -3), ("100", -2), ("10", -1), ("1000", -3), ("120000", -4) })
                data.Add(negative, coefficient, exponent);

            // 34 significant digits straddling the point in both directions, so neither
            // layout branch can drop, duplicate, or misplace a digit.
            foreach (var exponent in new[] { -34, -33, -17, 0, 1, -48, -68 })
                data.Add(negative, "1234567890123456789012345678901234", exponent);

            // The precision extreme.
            data.Add(negative, "9999999999999999999999999999999999", 6111);
            data.Add(negative, "9999999999999999999999999999999999", -6142);
        }

        return data;
    }

    [Theory]
    [MemberData(nameof(LayoutCases))]
    public void ConstructedValues_MatchTheIndependentLayoutOracle(bool negative, string coefficient, int exponent)
    {
        var literal = (negative ? "-" : string.Empty)
            + coefficient + "e" + exponent.ToString(CultureInfo.InvariantCulture);
        var value = N(literal);

        // Guard the premise: the case only means anything if the chosen coefficient and
        // exponent survived parsing as the STORED representation. A silently re-scaled
        // value would make the oracle describe a different number.
        Assert.Equal(exponent, Decimal128.ILogB(Decimal128.GetQuantum(value)));

        Assert.Equal(
            ExpectedLayout(negative, coefficient, exponent),
            ValueTextRenderer.FormatNumberInvariant(value));
    }

    [Fact]
    public void TrailingZeros_AreValueIdentity_AndSurviveRendering()
    {
        // Independent expectations, written out by hand: same value, different quantum,
        // different text. Rendering must not normalize one into the other.
        Assert.Equal("1", Text("1"));
        Assert.Equal("1.0", Text("1.0"));
        Assert.Equal("1.00", Text("1.00"));
        Assert.Equal("1.000000000000000000000000000000000", Text("1.000000000000000000000000000000000"));
        Assert.Equal("-2.500", Text("-2.500"));

        // All of them are the same NUMBER; only the stored scale differs.
        foreach (var literal in new[] { "1", "1.0", "1.00", "1.000000000000000000000000000000000" })
            Assert.True(Decimal128.Equals(Decimal128.One, N(literal)));
    }

    // ── Subnormals and the exponent extremes ────────────────────────────────

    [Fact]
    public void SubnormalsAndExtremes_RenderEveryStoredDigit()
    {
        Assert.Equal("0." + new string('0', 6175) + "1", ValueTextRenderer.FormatNumberInvariant(Decimal128.Epsilon));
        Assert.Equal("-0." + new string('0', 6175) + "1", ValueTextRenderer.FormatNumberInvariant(-Decimal128.Epsilon));
        Assert.Equal("0." + new string('0', 6175) + "9", Text("9e-6176"));
        Assert.Equal("0." + new string('0', 6174) + "1", Text("1e-6175"));

        // `99e-6177` is below the minimum exponent, so the LITERAL is rounded on the
        // way in to coefficient 10 at exponent -6176 (checked here by scaling the
        // value back by its own quantum, not by reading the renderer's output). The
        // renderer prints the STORED number, so its text must show that 10 — a
        // reminder that these expectations describe the value, never the source
        // spelling.
        var rounded = N("99e-6177");
        Assert.Equal(-6176, Decimal128.ILogB(Decimal128.GetQuantum(rounded)));
        Assert.Equal("10", Decimal128.ScaleB(rounded, 6176).ToString("F0", CultureInfo.InvariantCulture));
        Assert.Equal("0." + new string('0', 6174) + "10", ValueTextRenderer.FormatNumberInvariant(rounded));

        // Epsilon is genuinely subnormal, so this is not merely a small normal value.
        Assert.True(Decimal128.IsSubnormal(Decimal128.Epsilon));
        Assert.Equal(-6176, Decimal128.ILogB(Decimal128.GetQuantum(Decimal128.Epsilon)));

        // The largest finite magnitude, both signs.
        Assert.Equal(
            new string('9', 34) + new string('0', 6111),
            ValueTextRenderer.FormatNumberInvariant(Decimal128.MaxValue));
        Assert.Equal(
            "-" + new string('9', 34) + new string('0', 6111),
            ValueTextRenderer.FormatNumberInvariant(Decimal128.MinValue));
    }

    // ── Every rendering consumer agrees, exactly ────────────────────────────

    [Theory]
    [InlineData("1e34", "10000000000000000000000000000000000")]
    [InlineData("1e-28", "0.0000000000000000000000000001")]
    [InlineData("1.50", "1.50")]
    public void EveryRenderingConsumer_ProducesTheSameSpelling(string literal, string expected)
    {
        var value = N(literal);
        var atom = new Result.Atom(value);

        // 1. Canonical display (no DisplayDecimals).
        Assert.Equal(expected, ValueTextRenderer.FormatAtom(value, new DisplayOptions(null, int.MaxValue)));

        // 2. The public run-result display surface.
        Assert.Equal(expected, Assert.IsType<RunResult.Success>(KatLangEngine.Run(literal)).ToDisplayString());

        // 3. The bounded diagnostic value renderer.
        Assert.Equal(expected, Evaluator.FormatResultForDiagnostic(atom));

        // 4. The bounded expression-name renderer.
        Assert.Equal(
            $"{expected} + 1",
            ExprNameRenderer.RenderBinaryDiagnosticName(
                BinaryOp.Add, new Expr.Num(value), new Expr.Num(Decimal128.One)));

        // 5. The language-observable `string` conversion.
        Assert.Equal(
            expected,
            Assert.IsType<RunResult.Success>(KatLangEngine.Run($"({literal}).string")).ToDisplayString());

        // 6. The editor's clause-head literal formatter.
        Assert.Equal(
            $"F({expected})",
            Semantics.ConditionalBranchHeadFormatter.Format("F", new Pattern.LitInt(value)));
    }

    [Fact]
    public void DisplayDecimals_WholeNumberArm_UsesTheSameOwner()
    {
        // `DisplayDecimals` opts into fixed-point presentation, but a whole number
        // carrying an integral quantum stays on the canonical spelling — including the
        // values whose canonical spelling the runtime would have written exponentially.
        var options = new DisplayOptions(2, int.MaxValue);
        Assert.Equal("10000000000000000000000000000000000", ValueTextRenderer.FormatAtom(N("1e34"), options));
        Assert.Equal("0", ValueTextRenderer.FormatAtom(N("0e3"), options));

        // A fractional value still takes the requested fixed-point presentation.
        Assert.Equal("1.50", ValueTextRenderer.FormatAtom(N("1.5"), options));
    }
}
