using System.Globalization;
using System.Numerics;
using KatLang.Formatting;
using KatLang.Rendering;

namespace KatLang.Tests.Hosting;

/// <summary>
/// The decimal-places DISPLAY RULE (owner decision 2026-11-12, replacing the fixed-point layout of
/// the former single setting): the ONE implementation, <see cref="ValueTextRenderer.FormatAtom"/>,
/// and the same text on every surface that goes through it. With <c>min</c> and <c>max</c> the
/// effective settings:
/// <list type="number">
///   <item>neither present — today's canonical display, the value's stored digits;</item>
///   <item>a non-finite value — its canonical spelling, always;</item>
///   <item>otherwise — round to <c>max</c> places when it is present (midpoints away from zero),
///   write the result with the fewest fractional digits that represent it exactly, pad with zeros
///   up to <c>min</c> places, write no decimal point without fractional digits, and keep the sign,
///   also of a zero and of a value that rounds to zero.</item>
/// </list>
/// Once any setting is present the text depends on the numeric VALUE only, never on its stored
/// quantum. How the effective pair is composed is <see cref="DecimalPlacesCompositionTests"/>'s
/// subject; here every pair is given directly, from the source, from the host, and to the
/// renderer.
/// </summary>
public sealed class DecimalPlacesFormattingTests
{
    private static Decimal128 N(string text)
        => Decimal128.Parse(text, NumberStyles.Float, CultureInfo.InvariantCulture);

    /// <summary>A display configuration whose effective pair is the given one, from the SOURCE side.</summary>
    private static DisplayOptions Source(int? min, int? max) => new(min, max, null, null, int.MaxValue);

    /// <summary>A display configuration whose effective pair is the given one, from the HOST side.</summary>
    private static DisplayOptions Host(int? min, int? max) => new(null, null, min, max, int.MaxValue);

    private static string Format(Decimal128 value, int? min, int? max)
    {
        var fromSource = ValueTextRenderer.FormatAtom(value, Source(min, max));
        // Whichever origin supplies the pair, the text is the same.
        Assert.Equal(fromSource, ValueTextRenderer.FormatAtom(value, Host(min, max)));
        Assert.Equal(fromSource, ValueTextRenderer.FormatAtom(value, new DisplayOptions(min, null, null, max, int.MaxValue)));
        Assert.Equal(fromSource, ValueTextRenderer.FormatAtom(value, new DisplayOptions(null, max, min, null, int.MaxValue)));
        return fromSource;
    }

    private static string Display(string source, RunOptions? options = null)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, options)).ToDisplayString().ReplaceLineEndings("\n");

    private static string Declare(int? min, int? max)
        => (min is { } a ? $"MinDecimalPlaces = {a.ToString(CultureInfo.InvariantCulture)}\n" : "")
            + (max is { } b ? $"MaxDecimalPlaces = {b.ToString(CultureInfo.InvariantCulture)}\n" : "");

    // ── The normative table ─────────────────────────────────────────────────────

    /// <summary>
    /// The § 4 table, in full and hand-written: value, then its text at min 2, at max 4, at
    /// min 2 and max 4, at min 2 and max 2, and at min 0.
    /// </summary>
    public static TheoryData<string, string, string, string, string, string> NormativeTable => new()
    {
        { "10", "10.00", "10", "10.00", "10.00", "10" },
        { "10.00", "10.00", "10", "10.00", "10.00", "10" },
        { "2.5", "2.50", "2.5", "2.50", "2.50", "2.5" },
        { "2.5000", "2.50", "2.5", "2.50", "2.50", "2.5" },
        { "1.234", "1.234", "1.234", "1.234", "1.23", "1.234" },
        { "1.234567", "1.234567", "1.2346", "1.2346", "1.23", "1.234567" },
        { "0", "0.00", "0", "0.00", "0.00", "0" },
        { "0.125", "0.125", "0.125", "0.125", "0.13", "0.125" },
        { "9.9996", "9.9996", "9.9996", "9.9996", "10.00", "9.9996" },
        { "-0.004", "-0.004", "-0.004", "-0.004", "-0.00", "-0.004" },
        { "-0", "-0.00", "-0", "-0.00", "-0.00", "-0" },
    };

    private static readonly (int? Min, int? Max)[] TableColumns = [(2, null), (null, 4), (2, 4), (2, 2), (0, null)];

    [Theory]
    [MemberData(nameof(NormativeTable))]
    public void NormativeTable_TheRenderer(string value, string min2, string max4, string min2Max4, string min2Max2, string min0)
    {
        var number = N(value);
        string[] expected = [min2, max4, min2Max4, min2Max2, min0];
        for (var column = 0; column < TableColumns.Length; column++)
        {
            var (min, max) = TableColumns[column];
            Assert.Equal(expected[column], Format(number, min, max));
        }

        // No setting: the stored digits, exactly as written.
        Assert.Equal(value, ValueTextRenderer.FormatAtom(number, DisplayOptions.Canonical(int.MaxValue)));
    }

    /// <summary>
    /// The same table through the ENGINE, with the pair declared by the program, supplied by the
    /// host, and split across the two — and identically through every built-in formatter.
    /// </summary>
    [Theory]
    [MemberData(nameof(NormativeTable))]
    public void NormativeTable_TheEngine_FromSourceAndFromHost(string value, string min2, string max4, string min2Max4, string min2Max2, string min0)
    {
        string[] expected = [min2, max4, min2Max4, min2Max2, min0];
        for (var column = 0; column < TableColumns.Length; column++)
        {
            var (min, max) = TableColumns[column];
            var fromSource = KatLangEngine.Run(Declare(min, max) + value);
            var fromHost = KatLangEngine.Run(value, new RunOptions { MinDecimalPlaces = min, MaxDecimalPlaces = max });
            var split = KatLangEngine.Run(Declare(min, null) + value, new RunOptions { MaxDecimalPlaces = max });

            foreach (var run in new[] { fromSource, fromHost, split })
            {
                Assert.IsType<RunResult.Success>(run);
                Assert.Equal(expected[column], run.ToDisplayString());
                Assert.Equal(expected[column], run.RenderDisplay().Text);
                foreach (var formatter in new[] { OutputFormatters.Exact, OutputFormatters.Readable, OutputFormatters.Concise })
                    Assert.Equal(expected[column], formatter.Format(run));
            }
        }

        Assert.Equal(value, Display(value));
    }

    // ── Rule 1: no setting is today's canonical display ─────────────────────────

    public static TheoryData<string, string> CanonicalValues => new()
    {
        { "0", "0" },
        { "-0", "-0" },
        { "0.0", "0.0" },
        { "-0.00", "-0.00" },
        { "1", "1" },
        { "1.0", "1.0" },
        { "1.50", "1.50" },
        { "2.5000", "2.5000" },
        { "10.00", "10.00" },
        { "0.000000000000000000000000000", "0.000000000000000000000000000" },
        { "1e3", "1000" },
        { "1e34", "10000000000000000000000000000000000" },
        { "1e-7", "0.0000001" },
        { "123456789.123456789", "123456789.123456789" },
        { "0.1428571428571428571428571428571429", "0.1428571428571428571428571428571429" },
        { "-2.5", "-2.5" },
    };

    /// <summary>
    /// With no setting from any origin, display is byte-identical to the canonical number text —
    /// the stored digits, trailing zeros included — and there is no new default rounding.
    /// </summary>
    [Theory]
    [MemberData(nameof(CanonicalValues))]
    public void NoSetting_IsByteIdenticalToTheCanonicalDisplay(string literal, string expected)
    {
        var value = N(literal);

        Assert.Equal(expected, ValueTextRenderer.FormatNumberInvariant(value));
        Assert.Equal(expected, ValueTextRenderer.FormatAtom(value, DisplayOptions.Default));
        Assert.Equal(expected, ValueTextRenderer.FormatAtom(value, DisplayOptions.Canonical(16)));
        Assert.False(DisplayOptions.Default.HasDecimalPlaces);

        // The engine without a setting, with an empty options object, and with explicit nulls.
        Assert.Equal(expected, Display(literal));
        Assert.Equal(expected, Display(literal, new RunOptions()));
        Assert.Equal(expected, Display(literal, new RunOptions { MinDecimalPlaces = null, MaxDecimalPlaces = null }));

        // And it is the same text `.string` gives for the number.
        Assert.Equal(expected, Display($"({literal}).string"));
    }

    [Fact]
    public void NoSetting_NonFiniteValues_KeepTheCanonicalSpellings()
    {
        Assert.Equal("NaN\nInfinity\n-Infinity", Display("Math.Sqrt(-1), 9e6144 * 10, Math.Ln(0)"));
    }

    /// <summary>Any present setting — from any origin, even a 0 or a 99 — leaves the canonical path.</summary>
    [Fact]
    public void AnyPresentSetting_SelectsTheValueBasedDisplay()
    {
        var stored = N("2.5000");
        Assert.Equal("2.5000", ValueTextRenderer.FormatAtom(stored, DisplayOptions.Canonical(int.MaxValue)));

        foreach (var options in new[]
                 {
                     new DisplayOptions(0, null, null, null, int.MaxValue),
                     new DisplayOptions(null, 99, null, null, int.MaxValue),
                     new DisplayOptions(null, null, 0, null, int.MaxValue),
                     new DisplayOptions(null, null, null, 99, int.MaxValue),
                 })
        {
            Assert.True(options.HasDecimalPlaces);
            Assert.Equal("2.5", ValueTextRenderer.FormatAtom(stored, options));
        }
    }

    // ── Rule 2: non-finite values ───────────────────────────────────────────────

    [Fact]
    public void NonFiniteValues_KeepTheirSpelling_UnderEverySetting()
    {
        foreach (var (min, max) in new (int?, int?)[] { (2, null), (null, 4), (2, 4), (2, 2), (0, null), (null, 0), (99, 99), (0, 99) })
        {
            Assert.Equal("NaN", Format(Decimal128.NaN, min, max));
            Assert.Equal("NaN", Format(-Decimal128.NaN, min, max));
            Assert.Equal("Infinity", Format(Decimal128.PositiveInfinity, min, max));
            Assert.Equal("-Infinity", Format(Decimal128.NegativeInfinity, min, max));
        }

        Assert.Equal(
            "NaN\nInfinity\n-Infinity\n1.50",
            Display("MinDecimalPlaces = 2\nMaxDecimalPlaces = 2\nMath.Sqrt(-1), 9e6144 * 10, Math.Ln(0), 1.5"));
    }

    // ── Rule 3.1: rounding ──────────────────────────────────────────────────────

    /// <summary>Midpoints round AWAY FROM ZERO, in both directions, at every place.</summary>
    [Theory]
    [InlineData("0.5", 0, "1")]
    [InlineData("1.5", 0, "2")]
    [InlineData("2.5", 0, "3")]
    [InlineData("-0.5", 0, "-1")]
    [InlineData("-2.5", 0, "-3")]
    [InlineData("0.125", 2, "0.13")]
    [InlineData("0.135", 2, "0.14")]
    [InlineData("-0.125", 2, "-0.13")]
    [InlineData("1.005", 2, "1.01")]
    [InlineData("2.675", 2, "2.68")]
    [InlineData("0.05", 1, "0.1")]
    [InlineData("0.00005", 4, "0.0001")]
    [InlineData("-0.00005", 4, "-0.0001")]
    [InlineData("0.124999", 2, "0.12")]
    [InlineData("0.4999999999999999999999999999999999", 0, "0")]
    [InlineData("1.234567890123456789012345678901235", 32, "1.23456789012345678901234567890124")]
    public void Maximum_RoundsTiesAwayFromZero(string literal, int max, string expected)
    {
        Assert.Equal(expected, Format(N(literal), null, max));
        Assert.Equal(expected, Display($"MaxDecimalPlaces = {max}\n{literal}"));

        // The same digits Math.Round gives the value — display introduces no rounding policy.
        var rounded = Assert.IsType<RunResult.Success>(KatLangEngine.Run($"Math.Round({literal}, {max})"));
        Assert.True(N(expected) == Assert.Single(rounded.Atoms));
    }

    /// <summary>A carry runs across the decimal point, and the result is then shown by its value.</summary>
    [Theory]
    [InlineData("9.9996", 2, "10", "10.00")]
    [InlineData("0.995", 2, "1", "1.00")]
    [InlineData("99.995", 2, "100", "100.00")]
    [InlineData("999.9999", 0, "1000", "1000")]
    [InlineData("-9.9996", 2, "-10", "-10.00")]
    [InlineData("0.99999", 4, "1", "1.0000")]
    [InlineData("19.995", 2, "20", "20.00")]
    [InlineData("0.095", 2, "0.1", "0.10")]
    public void Rounding_CarriesAcrossTheDecimalPoint(string literal, int places, string maximumOnly, string fixedPlaces)
    {
        Assert.Equal(maximumOnly, Format(N(literal), null, places));
        Assert.Equal(fixedPlaces, Format(N(literal), places, places));
        Assert.Equal(maximumOnly, Display($"MaxDecimalPlaces = {places}\n{literal}"));
        Assert.Equal(fixedPlaces, Display(literal, new RunOptions { MinDecimalPlaces = places, MaxDecimalPlaces = places }));
    }

    /// <summary>A value that rounds to zero is shown as a zero that keeps the value's sign.</summary>
    [Theory]
    [InlineData("0.004", 2, "0", "0.00")]
    [InlineData("-0.004", 2, "-0", "-0.00")]
    [InlineData("0.0000001", 4, "0", "0.0000")]
    [InlineData("-0.0000001", 4, "-0", "-0.0000")]
    [InlineData("0.4", 0, "0", "0")]
    [InlineData("-0.4", 0, "-0", "-0")]
    [InlineData("1e-6176", 4, "0", "0.0000")]
    [InlineData("-1e-6176", 4, "-0", "-0.0000")]
    public void ValuesThatRoundToZero_KeepTheirSign(string literal, int places, string maximumOnly, string fixedPlaces)
    {
        Assert.Equal(maximumOnly, Format(N(literal), null, places));
        Assert.Equal(fixedPlaces, Format(N(literal), places, places));
        Assert.Equal(maximumOnly, Display($"MaxDecimalPlaces = {places}\n{literal}"));
        Assert.Equal(fixedPlaces, Display($"MinDecimalPlaces = {places}\nMaxDecimalPlaces = {places}\n{literal}"));
    }

    // ── Rules 3.2–3.5: value-based digits, padding, the point, the sign ─────────

    /// <summary>Both zero signs, in every stored quantum, under each kind of pair.</summary>
    [Theory]
    [InlineData("0", "0", "0.00", "0.00")]
    [InlineData("0.0", "0", "0.00", "0.00")]
    [InlineData("0.000", "0", "0.00", "0.00")]
    [InlineData("0e3", "0", "0.00", "0.00")]
    [InlineData("-0", "-0", "-0.00", "-0.00")]
    [InlineData("-0.0", "-0", "-0.00", "-0.00")]
    [InlineData("-0.000", "-0", "-0.00", "-0.00")]
    [InlineData("-0e3", "-0", "-0.00", "-0.00")]
    public void BothZeroSigns_DependOnTheValueOnly(string literal, string max4, string min2, string min2Max2)
    {
        var value = N(literal);
        Assert.Equal(max4, Format(value, null, 4));
        Assert.Equal(max4, Format(value, 0, null));
        Assert.Equal(min2, Format(value, 2, null));
        Assert.Equal(min2Max2, Format(value, 2, 2));
    }

    /// <summary>
    /// Stored trailing zeros are removed and then the minimum pads: the same VALUE in any quantum
    /// gives the same text, whole numbers are padded like any other, and no decimal point is
    /// written without fractional digits.
    /// </summary>
    [Fact]
    public void TheTextDependsOnTheValue_NotOnTheStoredQuantum()
    {
        foreach (var spelling in new[] { "1", "1.0", "1.00", "1.000000000000000000000000000000000", "0.1e1", "10e-1" })
        {
            var value = N(spelling);
            Assert.Equal("1", Format(value, null, 4));
            Assert.Equal("1", Format(value, 0, null));
            Assert.Equal("1", Format(value, 0, 0));
            Assert.Equal("1.00", Format(value, 2, null));
            Assert.Equal("1.00", Format(value, 2, 4));
            Assert.Equal("1.0000", Format(value, 4, 4));
        }

        foreach (var spelling in new[] { "1500", "1.5e3", "15e2", "1500.0", "1500.00" })
        {
            var value = N(spelling);
            Assert.Equal("1500", Format(value, null, 2));
            Assert.Equal("1500.00", Format(value, 2, 2));
            Assert.DoesNotContain(".", Format(value, 0, null), StringComparison.Ordinal);
        }

        // A minimum never rounds, whatever it is; a maximum never pads, whatever it is.
        Assert.Equal("1.234567", Format(N("1.234567"), 2, null));
        Assert.Equal("1.234567", Format(N("1.234567"), 0, null));
        Assert.Equal("10", Format(N("10"), null, 4));
        Assert.Equal("10", Format(N("10.00"), null, 99));
    }

    /// <summary>Minimum equal to maximum is a fixed number of places, at the boundaries 0 and 99 too.</summary>
    [Fact]
    public void MinimumEqualToMaximum_IsAFixedNumberOfPlaces_IncludingTheBoundaries()
    {
        Assert.Equal("1.23\n10.00\n0.13\n-2.50", Display("1.234567, 10, 0.125, -2.5", new RunOptions { MinDecimalPlaces = 2, MaxDecimalPlaces = 2 }));
        Assert.Equal("1\n10\n0\n-3", Display("1.234567, 10, 0.125, -2.5", new RunOptions { MinDecimalPlaces = 0, MaxDecimalPlaces = 0 }));

        var ninetyNine = Display("1 / 3, 10, 0.125", new RunOptions { MinDecimalPlaces = 99, MaxDecimalPlaces = 99 }).Split('\n');
        Assert.Equal("0." + new string('3', 34) + new string('0', 65), ninetyNine[0]);
        Assert.Equal("10." + new string('0', 99), ninetyNine[1]);
        Assert.Equal("0.125" + new string('0', 96), ninetyNine[2]);
        Assert.All(ninetyNine, row => Assert.Equal(99, row.Length - row.IndexOf('.', StringComparison.Ordinal) - 1));

        // The boundaries of each setting alone.
        Assert.Equal("0." + new string('3', 34), Display("1 / 3", new RunOptions { MaxDecimalPlaces = 99 }));
        Assert.Equal("0." + new string('3', 34), Display("1 / 3", new RunOptions { MinDecimalPlaces = 0 }));
        Assert.Equal("0", Display("1 / 3", new RunOptions { MaxDecimalPlaces = 0 }));
        Assert.Equal("0." + new string('3', 34) + new string('0', 65), Display("1 / 3", new RunOptions { MinDecimalPlaces = 99 }));
    }

    // ── Magnitudes ──────────────────────────────────────────────────────────────

    [Fact]
    public void VerySmallMagnitudes_AreShownExactly_OrRoundedToTheMaximum()
    {
        var tiny = N("1e-6176");
        var exact = "0." + new string('0', 6175) + "1";
        Assert.Equal(exact, ValueTextRenderer.FormatNumberInvariant(tiny));

        // A minimum alone never rounds: the whole positional text, already longer than any minimum.
        Assert.Equal(exact, Format(tiny, 2, null));
        Assert.Equal(exact, Format(tiny, 99, null));
        // A maximum rounds it away; the sign of a negative one is kept.
        Assert.Equal("0", Format(tiny, null, 99));
        Assert.Equal("0.00", Format(tiny, 2, 99));
        Assert.Equal("-0", Format(-tiny, null, 99));

        // The engine applies the same rule and its display bound is unaffected.
        Assert.Equal("0\n-0", Display("1e-6176, -1e-6176", new RunOptions { MaxDecimalPlaces = 4 }));
    }

    [Fact]
    public void VeryLargeMagnitudes_AreWrittenInFull_AndPaddedLikeAnyWholeNumber()
    {
        var huge = N("9e6144");
        var digits = "9" + new string('0', 6144);
        Assert.Equal(digits, ValueTextRenderer.FormatNumberInvariant(huge));

        Assert.Equal(digits, Format(huge, null, 4));
        Assert.Equal(digits, Format(huge, 0, null));
        Assert.Equal(digits + ".00", Format(huge, 2, null));
        Assert.Equal(digits + "." + new string('0', 99), Format(huge, 99, 99));
        Assert.Equal("-" + digits + ".00", Format(-huge, 2, 2));

        // A 34-digit coefficient is never re-rounded by a maximum above its own scale.
        var precise = N("1234567890123456789012345678901234");
        Assert.Equal("1234567890123456789012345678901234", Format(precise, null, 0));
        Assert.Equal("1234567890123456789012345678901234.0", Format(precise, 1, 99));
    }

    /// <summary>A value that needs all 99 places is shown exactly at 99 and rounded below it.</summary>
    [Fact]
    public void AValueNeedingNinetyNinePlaces()
    {
        var value = N("1e-99");
        var exact = "0." + new string('0', 98) + "1";

        Assert.Equal(exact, Format(value, null, 99));
        Assert.Equal(exact, Format(value, 99, 99));
        Assert.Equal(exact, Format(value, 0, null));
        Assert.Equal("0", Format(value, null, 98));
        Assert.Equal("0." + new string('0', 98), Format(value, 98, 98));

        // A midpoint in the 99th place rounds away from zero into the 98th.
        Assert.Equal("0." + new string('0', 97) + "1", Format(N("5e-99"), null, 98));
        Assert.Equal("-0." + new string('0', 97) + "1", Format(N("-5e-99"), null, 98));

        // The engine, with the literal written positionally.
        Assert.Equal(exact, Display($"MaxDecimalPlaces = 99\n{exact}"));
        Assert.Equal(exact, Display(exact, new RunOptions { MinDecimalPlaces = 99, MaxDecimalPlaces = 99 }));
    }

    // ── Unchanged boundaries ────────────────────────────────────────────────────

    /// <summary>
    /// Booleans and strings are untouched; numbers nested in printed sequences and lists are
    /// formatted like top-level ones; <c>.string</c> shows a number's own digits and ignores every
    /// setting.
    /// </summary>
    [Fact]
    public void StringsBooleansAndDotString_AreUnaffected_NestedNumbersAreFormatted()
    {
        const string program = "x = 2.5000\n(10, [2.5, (1.234567, '1.50', true)]), [0.125], '10', x.string, x, false, 'a 2.5000 b'";

        Assert.Equal(
            "(10.00, [2.50, (1.23, 1.50, true)])\n[0.13]\n10\n2.5000\n2.50\nfalse\na 2.5000 b",
            Display("MinDecimalPlaces = 2\nMaxDecimalPlaces = 2\n" + program));
        Assert.Equal(
            "(10, [2.5, (1.2346, 1.50, true)])\n[0.125]\n10\n2.5000\n2.5\nfalse\na 2.5000 b",
            Display(program, new RunOptions { MaxDecimalPlaces = 4 }));
        Assert.Equal(
            "(10.00, [2.50, (1.234567, 1.50, true)])\n[0.125]\n10\n2.5000\n2.50\nfalse\na 2.5000 b",
            Display(program, new RunOptions { MinDecimalPlaces = 2 }));
        Assert.Equal(
            "(10, [2.5, (1.234567, 1.50, true)])\n[0.125]\n10\n2.5000\n2.5000\nfalse\na 2.5000 b",
            Display(program));

        // `.string` of a value a maximum displays rounded is still its own digits, and the text
        // it produces is an ordinary string afterwards.
        Assert.Equal("1.555\ntrue", Display("MaxDecimalPlaces = 1\nx = 1.555\nx.string, x.string == '1.555'"));
    }

    /// <summary>
    /// The values, atoms and output rows a host receives are the unconfigured run's, exactly —
    /// representation included — whatever pair is displayed.
    /// </summary>
    [Fact]
    public void ReturnedValuesAtomsAndRows_AreNeverAltered()
    {
        const string program = "2.5000, 10.00, 1.234567, -0.0, (0.125, [9.9996])";
        var baseline = Assert.IsType<RunResult.Success>(KatLangEngine.Run(program));
        var exact = NumericRepresentativeSelectionTests.Exact(baseline.Value);
        Assert.Equal("S[2.5000, 10.00, 1.234567, -0.0, S[0.125, L[9.9996]]]", exact);

        foreach (var (min, max) in new (int?, int?)[] { (2, null), (null, 4), (2, 4), (2, 2), (0, null), (null, 0), (99, 99) })
        {
            foreach (var run in new[]
                     {
                         Assert.IsType<RunResult.Success>(KatLangEngine.Run(Declare(min, max) + program)),
                         Assert.IsType<RunResult.Success>(KatLangEngine.Run(program, new RunOptions { MinDecimalPlaces = min, MaxDecimalPlaces = max })),
                     })
            {
                _ = run.ToDisplayString();
                Assert.Equal(exact, NumericRepresentativeSelectionTests.Exact(run.Value));
                Assert.Equal(
                    baseline.Atoms.Select(NumericRepresentativeSelectionTests.Number),
                    run.Atoms.Select(NumericRepresentativeSelectionTests.Number));
                Assert.Equal(
                    baseline.OutputRows.Select(NumericRepresentativeSelectionTests.Exact),
                    run.OutputRows.Select(NumericRepresentativeSelectionTests.Exact));
            }
        }
    }

    [Theory]
    [InlineData("de-DE")]
    [InlineData("fr-FR")]
    [InlineData("ar-SA")]
    [InlineData("en-US")]
    public void Output_IsCultureInvariant(string cultureName)
    {
        var previous = CultureInfo.CurrentCulture;
        try
        {
            CultureInfo.CurrentCulture = CultureInfo.GetCultureInfo(cultureName);

            Assert.Equal(
                "1234567.50\n-0.13\n10.00",
                Display("1234567.5, -0.125, 10", new RunOptions { MinDecimalPlaces = 2, MaxDecimalPlaces = 2 }));
            Assert.Equal("1234567.5\n-0.125\n10", Display("MaxDecimalPlaces = 4\n1234567.5, -0.125, 10"));
        }
        finally
        {
            CultureInfo.CurrentCulture = previous;
        }
    }

    /// <summary>The display-length bound applies to the formatted text, on every surface.</summary>
    [Fact]
    public void DisplayLengthLimit_AppliesToTheFormattedText()
    {
        var limits = new EvaluationLimits { MaxDisplayLength = 6 };

        // "10" fits; padded to "10.00000" it does not; rounded to "0.33" a long fraction now fits.
        Assert.False(KatLangEngine.Run("10", new RunOptions { EvaluationLimits = limits }).RenderDisplay().LimitExceeded);
        var padded = KatLangEngine.Run("10", new RunOptions { EvaluationLimits = limits, MinDecimalPlaces = 5 });
        Assert.True(padded.RenderDisplay().LimitExceeded);
        Assert.True(KatLangEngine.Run("1 / 3", new RunOptions { EvaluationLimits = limits }).RenderDisplay().LimitExceeded);
        var rounded = KatLangEngine.Run("1 / 3", new RunOptions { EvaluationLimits = limits, MaxDecimalPlaces = 2 });
        Assert.False(rounded.RenderDisplay().LimitExceeded);
        Assert.Equal("0.33", rounded.ToDisplayString());

        foreach (var formatter in new[] { OutputFormatters.Exact, OutputFormatters.Readable, OutputFormatters.Concise })
        {
            var rendering = formatter.RenderDisplay(padded);
            Assert.True(rendering.LimitExceeded);
            Assert.Equal(KatLangErrorCode.DisplayLengthLimitExceeded, rendering.LimitError!.Code);
            Assert.InRange(rendering.Text.Length, 0, 6);
            Assert.Equal("0.33", formatter.Format(rounded));
        }
    }

    /// <summary>
    /// The structured-layout measurer reads the SAME formatted text the writer appends: a run
    /// displayed under a pair lays out, at every preferred width, exactly like a run whose numbers
    /// are literally written with those digits.
    /// </summary>
    [Fact]
    public void StructuredLayout_MeasuresTheFormattedNumbers()
    {
        const string values = "[1.234567, 10, 2.5, 100.125, 0.5, 7, 33.333333, 2.5000, 12345.6789, 0.004]";
        const string written = "[1.23, 10.00, 2.50, 100.13, 0.50, 7.00, 33.33, 2.50, 12345.68, 0.00]";
        var formatted = KatLangEngine.Run($"({values}, {values})", new RunOptions { MinDecimalPlaces = 2, MaxDecimalPlaces = 2 });
        var literal = KatLangEngine.Run($"({written}, {written})");
        Assert.IsType<RunResult.Success>(formatted);

        Assert.Equal(literal.ToDisplayString(), formatted.ToDisplayString());
        foreach (var formatter in new[] { OutputFormatters.Readable, OutputFormatters.Concise })
        {
            for (var width = 1; width <= 160; width++)
            {
                var options = new OutputFormattingOptions { NewLine = "\n", PreferredLineWidth = width };
                Assert.Equal(formatter.Format(literal, options), formatter.Format(formatted, options));
            }
        }
    }
}
