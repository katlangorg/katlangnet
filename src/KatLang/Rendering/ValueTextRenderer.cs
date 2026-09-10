using System.Globalization;
using System.Numerics;

namespace KatLang.Rendering;

/// <summary>
/// Strategy used by the shared inline renderer for string leaves. Canonical
/// display supplies the raw strategy; presentation formatters may supply their
/// own policy without making <see cref="RunResult"/> depend on formatting.
/// </summary>
internal interface IStringTextPolicy
{
    bool Append(string value, IDisplaySink sink);
}

internal sealed class RawStringTextPolicy : IStringTextPolicy
{
    internal static RawStringTextPolicy Instance { get; } = new();

    private RawStringTextPolicy()
    {
    }

    public bool Append(string value, IDisplaySink sink) => sink.Append(value);
}

/// <summary>
/// Formatter-neutral, iterative rendering of KatLang values. Structural
/// punctuation and atom text have one owner; only string-leaf presentation is
/// supplied as a strategy.
/// </summary>
internal static class ValueTextRenderer
{
    internal static bool AppendValue(
        Result value,
        DisplayOptions displayOptions,
        IStringTextPolicy stringPolicy,
        IDisplaySink sink)
    {
        IReadOnlyList<Result> items;
        string close;
        switch (value)
        {
            case Result.Atom atom:
                return sink.Append(FormatAtom(atom.Value, displayOptions));
            case Result.Str str:
                return stringPolicy.Append(str.Value, sink);
            case Result.SequenceValue sequence:
                if (!sink.Append("(")) return false;
                items = sequence.Items;
                close = ")";
                break;
            case Result.ListValue list:
                if (!sink.Append("[")) return false;
                items = list.Items;
                close = "]";
                break;
            default:
                throw new InvalidOperationException("Unknown Result variant.");
        }

        var suspended = new Stack<(IReadOnlyList<Result> Items, int Next, string Close)>();
        var next = 0;

        while (true)
        {
            if (next >= items.Count)
            {
                if (!sink.Append(close)) return false;
                if (suspended.Count == 0) return true;
                (items, next, close) = suspended.Pop();
                continue;
            }

            if (next > 0 && !sink.Append(", ")) return false;
            var child = items[next];
            next++;

            switch (child)
            {
                case Result.Atom atom:
                    if (!sink.Append(FormatAtom(atom.Value, displayOptions))) return false;
                    break;
                case Result.Str str:
                    if (!stringPolicy.Append(str.Value, sink)) return false;
                    break;
                case Result.SequenceValue sequence:
                    if (!sink.Append("(")) return false;
                    suspended.Push((items, next, close));
                    (items, next, close) = (sequence.Items, 0, ")");
                    break;
                case Result.ListValue list:
                    if (!sink.Append("[")) return false;
                    suspended.Push((items, next, close));
                    (items, next, close) = (list.Items, 0, "]");
                    break;
                default:
                    throw new InvalidOperationException("Unknown Result variant.");
            }
        }
    }

    /// <summary>
    /// Formats one numeric atom for display. Formatting is presentation only —
    /// the computed Decimal128 value is never truncated or re-rounded by the
    /// runtime, so the default rendering shows the value's full precision and
    /// quantum exactly as computed (invariant culture: <c>NaN</c>,
    /// <c>Infinity</c>, <c>-Infinity</c>, and <c>-0</c> render literally).
    /// <c>DisplayDecimals</c> opts into fixed-point presentation; whole numbers
    /// carrying an integral quantum stay plain there, mirroring the previous
    /// scale-zero rule.
    /// </summary>
    internal static string FormatAtom(Decimal128 value, DisplayOptions displayOptions)
    {
        if (displayOptions.Decimals is not { } decimals)
            return FormatNumberInvariant(value);

        if (Decimal128.IsInteger(value) && Decimal128.GetQuantum(value) >= Decimal128.One)
            return FormatNumberInvariant(value);

        var format = "F" + decimals.ToString(CultureInfo.InvariantCulture);
        return value.ToString(format, CultureInfo.InvariantCulture);
    }

    /// <summary>
    /// Fixed-point format strings, indexed by fractional-digit count, so the common
    /// path allocates only its result. The size is a pure allocation tuning constant
    /// with an unconditional fallback below — correctness spans the whole Decimal128
    /// exponent range either way. It covers every quantum exponent ordinary arithmetic
    /// reaches: division and the transcendental functions settle near -34, and the
    /// deepest value in the numeric suite is <c>5 ^ -50</c> at -68.
    /// </summary>
    private static readonly string[] FixedPointFormats =
        [.. Enumerable.Range(0, 129).Select(digits => "F" + digits.ToString(CultureInfo.InvariantCulture))];

    /// <summary>
    /// KatLang's canonical culture-invariant text for ONE number. This is the single
    /// owner of numeric presentation: canonical display, the <c>string</c> conversion
    /// (<c>Evaluator.ResultToString</c>), and every diagnostic that quotes a number all
    /// route here, so a number is spelled the same way wherever the language shows it.
    ///
    /// <para>A finite value renders POSITIONALLY — full precision, quantum-faithful, and
    /// never carrying an exponent marker — so the rendered text is itself a KatLang
    /// numeric literal that reads back as the same value. That round trip is a LANGUAGE
    /// contract, not a runtime default: <c>Decimal128.ToString</c> follows the IEEE 754
    /// <c>to-scientific-string</c> conversion, which switches to exponential notation
    /// once the exponent is positive or the adjusted exponent drops below -6, and
    /// <c>1E+30</c> is not a KatLang numeric literal (the lexer reads it as three
    /// tokens). Owning the layout here also keeps the language's rendering independent
    /// of a runtime's chosen default format.</para>
    ///
    /// <para>STRATEGY: ask the value for its own scale and let the runtime's fixed-point
    /// formatter lay it out. <c>GetQuantum</c> returns the value's quantum as
    /// <c>1 x 10^q</c>, and <c>ILogB</c> reads that power back as <c>q</c> — Decimal128's
    /// radix is 10, so this is the exact stored QUANTUM exponent, a different quantity
    /// from <c>ILogB(value)</c>, which reports the exponent of the value's most
    /// significant digit (for <c>1.50</c> the two are -2 and 0). A negative <c>q</c> is
    /// exactly the number of fractional digits the value carries, so <c>"F" + -q</c>
    /// reproduces the stored digits with neither rounding nor padding; a non-negative
    /// <c>q</c> means the value is an integer multiple of <c>10^q</c>, and <c>F0</c>
    /// writes it out in full. No approximation is involved anywhere: no <c>Log10</c>, no
    /// floating-point estimate, no numeric conversion, and no fixed precision.</para>
    ///
    /// <para>Non-finite values are handled first and keep their literal <c>NaN</c> /
    /// <c>Infinity</c> / <c>-Infinity</c> spellings. They must be: a non-finite quantum
    /// makes <c>ILogB</c> return <c>int.MaxValue</c>, which is not a scale at all.</para>
    ///
    /// <para>Positional text preserves the quantum of every value whose exponent is at
    /// most zero — trailing fractional zeros are written out, so <c>1.50</c> stays
    /// <c>1.50</c> and an underflowed zero still displays its <c>0.000…0</c> scale. A
    /// POSITIVE exponent has no positional spelling that distinguishes it from the same
    /// value carrying a smaller quantum (<c>1e34</c> writes as its 35 plain digits), so
    /// only the VALUE round-trips there. That is inherent to positional notation and is
    /// the established, documented behavior, not a loss introduced here. A zero
    /// coefficient's exponent is likewise padding rather than value, and the formatter
    /// writes the single digit <c>0</c> (signed when the value is negative zero).</para>
    ///
    /// <para>The layout is longer than the exponential spelling but its length is a
    /// CONSTANT of the format, not a function of any input: Decimal128's fixed 34-digit
    /// precision and bounded exponent range cap one number at about 6,180 characters.
    /// The output-bounded consumers (<see cref="DiagnosticValueRenderer"/>,
    /// <see cref="ExprNameRenderer"/>, and the display sink) therefore keep the exact
    /// budget behavior they were calibrated against.</para>
    /// </summary>
    internal static string FormatNumberInvariant(Decimal128 value)
    {
        if (!Decimal128.IsFinite(value))
            return value.ToString(CultureInfo.InvariantCulture);

        var quantumExponent = Decimal128.ILogB(Decimal128.GetQuantum(value));
        var fractionalDigits = Math.Max(0, -quantumExponent);
        var format = fractionalDigits < FixedPointFormats.Length
            ? FixedPointFormats[fractionalDigits]
            : "F" + fractionalDigits.ToString(CultureInfo.InvariantCulture);

        return value.ToString(format, CultureInfo.InvariantCulture);
    }
}
