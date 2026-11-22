using System.Globalization;
using System.Numerics;
using System.Runtime.CompilerServices;

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
/// supplied as a strategy. <see cref="ResumableMeasurement"/> is the same walk in
/// a width-capped form that layout measurement can continue.
/// </summary>
internal static partial class ValueTextRenderer
{
    // The structural punctuation of every value walk in this class.
    private const string SequenceOpen = "(";
    private const string SequenceClose = ")";
    private const string ListOpen = "[";
    private const string ListClose = "]";
    private const string ItemSeparator = ", ";

    /// <summary>
    /// One structure the value walk has entered and will resume: its items, the index of its next
    /// item, and its closing delimiter.
    /// </summary>
    internal readonly record struct SuspendedStructure(IReadOnlyList<Result> Items, int Next, string Close);

    internal static bool AppendValue(
        Result value,
        DisplayOptions displayOptions,
        IStringTextPolicy stringPolicy,
        IDisplaySink sink)
    {
        Stack<SuspendedStructure>? suspended = null;
        return AppendValue(value, displayOptions, stringPolicy, sink, ref suspended);
    }

    /// <summary>
    /// Appends one value like <see cref="AppendValue(Result, DisplayOptions, IStringTextPolicy, IDisplaySink)"/>,
    /// with a continuation stack the caller keeps for its next walk. The first walk that enters a nested
    /// structure creates the stack and stores it in <paramref name="suspended"/>. Each structural walk
    /// clears it before visiting children because a refused walk can leave frames on it. A caller that walks many
    /// values in one rendering (canonical display walks each row; a layout walks each item it measures or
    /// writes) therefore allocates one stack, not one per nested value. One stack serves one walk at a
    /// time: string policies append text and never start another walk.
    /// <para>Kept out of line: with the stack passed by reference, tier-1 JIT with dynamic PGO
    /// inlined this whole walk into the canonical row loop, and the <c>exact</c> formatter became
    /// 30–50% slower on small nested values (measured 2026-11-21).</para>
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    internal static bool AppendValue(
        Result value,
        DisplayOptions displayOptions,
        IStringTextPolicy stringPolicy,
        IDisplaySink sink,
        ref Stack<SuspendedStructure>? suspended)
    {
        IReadOnlyList<Result> items;
        string close;
        switch (value)
        {
            case Result.Atom atom:
                return AppendAtom(atom.Value, displayOptions, sink);
            case Result.Str str:
                return stringPolicy.Append(str.Value, sink);
            case Result.Bool flag:
                return sink.Append(FormatBool(flag.Value));
            case Result.SequenceValue sequence:
                if (!sink.Append(SequenceOpen)) return false;
                items = sequence.Items;
                close = SequenceClose;
                break;
            case Result.ListValue list:
                if (!sink.Append(ListOpen)) return false;
                items = list.Items;
                close = ListClose;
                break;
            case Result.CallReference reference:
                return AppendCallReference(reference, stringPolicy, sink);
            default:
                throw new InvalidOperationException("Unknown Result variant.");
        }

        // Created on the first nested structure only: a flat sequence or list
        // (and every width-capped fit probe that stops inside one) needs none.
        // A kept stack may still hold the frames of a refused walk.
        suspended?.Clear();
        var next = 0;

        while (true)
        {
            if (next >= items.Count)
            {
                if (!sink.Append(close)) return false;
                if (suspended is null || suspended.Count == 0) return true;
                (items, next, close) = suspended.Pop();
                continue;
            }

            if (next > 0 && !sink.Append(ItemSeparator)) return false;
            var child = items[next];
            next++;

            switch (child)
            {
                case Result.Atom atom:
                    if (!AppendAtom(atom.Value, displayOptions, sink)) return false;
                    break;
                case Result.Str str:
                    if (!stringPolicy.Append(str.Value, sink)) return false;
                    break;
                case Result.Bool flag:
                    if (!sink.Append(FormatBool(flag.Value))) return false;
                    break;
                case Result.SequenceValue sequence:
                    if (!sink.Append(SequenceOpen)) return false;
                    (suspended ??= new()).Push(new(items, next, close));
                    (items, next, close) = (sequence.Items, 0, SequenceClose);
                    break;
                case Result.ListValue list:
                    if (!sink.Append(ListOpen)) return false;
                    (suspended ??= new()).Push(new(items, next, close));
                    (items, next, close) = (list.Items, 0, ListClose);
                    break;
                case Result.CallReference reference:
                    if (!AppendCallReference(reference, stringPolicy, sink)) return false;
                    break;
                default:
                    throw new InvalidOperationException("Unknown Result variant.");
            }
        }
    }

    /// <summary>
    /// A call reference has NO text (CallReference S1): every display and formatting path receives only
    /// run results, which the run
    /// boundary keeps reference-free — so only a DIAGNOSTIC (an error message describing an operand that
    /// contains a reference) can reach one, and it names the kind in words. Any other route is an
    /// internal boundary defect and fails loudly rather than inventing a display syntax. An argument view
    /// (CallReference S2) follows the same rule under its own name.
    /// </summary>
    private static bool AppendCallReference(Result.CallReference reference, IStringTextPolicy stringPolicy, IDisplaySink sink)
        => stringPolicy is QuotedDiagnosticStringPolicy
            ? sink.Append(reference.IsArgumentView ? "<argument view>" : "<call reference>")
            : throw new InvalidOperationException(Evaluator.CallReferenceHasNoTextMessage);

    /// <summary>
    /// The canonical text of a Boolean value: lowercase <c>true</c> / <c>false</c>, the
    /// same spelling as the literals, wherever the language shows one (display, the
    /// diagnostic fragments, and the neutral spec encoding). Lean: <c>Result.boolText</c>.
    /// </summary>
    internal static string FormatBool(bool value) => value ? "true" : "false";

    /// <summary>Canonical atom text up to this many UTF-16 code units is written from a stack buffer.</summary>
    internal const int AtomStackBufferLength = 64;

    /// <summary>
    /// Appends one atom's <see cref="FormatAtom"/> text to <paramref name="sink"/>. The canonical
    /// path (a finite value with no decimal-places setting) formats into a stack buffer with the
    /// same fixed-point format <see cref="FormatNumberInvariant"/> selects, so the sink receives
    /// identical text without an intermediate string. Other values go through <see cref="FormatAtom"/>;
    /// canonical text longer than the buffer uses the selected format's string path once.
    /// </summary>
    internal static bool AppendAtom(Decimal128 value, DisplayOptions displayOptions, IDisplaySink sink)
    {
        Span<char> buffer = stackalloc char[AtomStackBufferLength];
        return sink.Append(AtomText(value, displayOptions, buffer));
    }

    /// <summary>The length of <see cref="FormatAtom"/>'s text, without building it on the canonical path.</summary>
    internal static int AtomLength(Decimal128 value, DisplayOptions displayOptions)
    {
        Span<char> buffer = stackalloc char[AtomStackBufferLength];
        return AtomText(value, displayOptions, buffer).Length;
    }

    private static ReadOnlySpan<char> AtomText(
        Decimal128 value,
        DisplayOptions displayOptions,
        Span<char> destination)
    {
        if (displayOptions.HasDecimalPlaces || !Decimal128.IsFinite(value))
            return FormatAtom(value, displayOptions);

        var quantumExponent = Decimal128.ILogB(Decimal128.GetQuantum(value));
        var format = FixedPointFormat(quantumExponent);
        var signLength = Decimal128.IsNegative(value) ? 1 : 0;
        // A failed TryFormat still formats the whole number. Skip that work when its
        // fractional places (plus "0.") or integer digits already cannot fit. A finite
        // Decimal128 has at most 34 coefficient digits, so only a positive quantum can
        // make the integer part exceed this buffer. A zero with a large positive quantum
        // may take the string path too; the choice affects only allocation, never text.
        var tryBuffer = quantumExponent < 0
            ? -quantumExponent <= destination.Length - signLength - 2
            : quantumExponent == 0
                || (quantumExponent < destination.Length - signLength
                    && Decimal128.ILogB(value) < destination.Length - signLength);
        if (tryBuffer && value.TryFormat(destination, out var length, format, CultureInfo.InvariantCulture))
            return destination[..length];

        return value.ToString(format, CultureInfo.InvariantCulture);
    }

    /// <summary>
    /// Formats one numeric atom for display — the ONE implementation every rendering surface
    /// uses. Formatting is presentation only: the computed Decimal128 value is never truncated or
    /// re-rounded by the runtime.
    /// <list type="number">
    ///   <item>With NO decimal-places setting from any origin, the text is the canonical display
    ///   (<see cref="FormatNumberInvariant"/>): the value's full precision and quantum exactly as
    ///   computed, so <c>2.5000</c> stays <c>2.5000</c>. This path is taken before anything else
    ///   and does no other work.</item>
    ///   <item>A non-finite value keeps its canonical spelling (<c>NaN</c>, <c>Infinity</c>,
    ///   <c>-Infinity</c>) whatever is set — KatLang owns those spellings everywhere a number is
    ///   shown.</item>
    ///   <item>Otherwise (<see cref="FormatDecimalPlaces"/>) the effective pair — each setting the
    ///   minimum of its present origins, the program root's property and the host's
    ///   <see cref="RunOptions"/> value, composed by the engine — decides the text from the numeric
    ///   VALUE alone, never from its stored quantum.</item>
    /// </list>
    /// </summary>
    internal static string FormatAtom(Decimal128 value, DisplayOptions displayOptions)
    {
        if (!displayOptions.HasDecimalPlaces)
            return FormatNumberInvariant(value);

        // Non-finite values have no positional layout; their spelling belongs to the one
        // canonical owner.
        if (!Decimal128.IsFinite(value))
            return FormatNumberInvariant(value);

        return FormatDecimalPlaces(value, displayOptions.MinDecimalPlaces, displayOptions.MaxDecimalPlaces);
    }

    /// <summary>
    /// The decimal-places display of one FINITE number under an effective pair with at least one
    /// setting present:
    /// <list type="number">
    ///   <item>when <paramref name="maxDecimalPlaces"/> is present, round to that many places with
    ///   midpoints AWAY FROM ZERO (<c>0.125</c> at two places is <c>0.13</c>, <c>2.5</c> at none
    ///   is <c>3</c>) — KatLang owns the rounding, so no runtime formatter's tie rule is
    ///   involved;</item>
    ///   <item>write the result positionally with the FEWEST fractional digits that represent it
    ///   exactly, so trailing fractional zeros are removed even when they were stored
    ///   (<c>2.5000</c> is <c>2.5</c>, <c>10.00</c> is <c>10</c>);</item>
    ///   <item>pad with zeros up to <paramref name="minDecimalPlaces"/> places (none when it is
    ///   absent), integers included (<c>10</c> at a minimum of two is <c>10.00</c>);</item>
    ///   <item>write no decimal point when there are no fractional digits;</item>
    ///   <item>keep the sign, including for a zero and for a value that rounds to zero
    ///   (<c>-0.004</c> at two and two is <c>-0.00</c>).</item>
    /// </list>
    /// Neither setting supplies the other: an absent maximum rounds nothing and an absent minimum
    /// pads nothing. The work is exact — one Decimal128 rounding and digit-level text edits of the
    /// canonical positional spelling, with no binary floating point and no numeric conversion.
    /// </summary>
    private static string FormatDecimalPlaces(Decimal128 value, int? minDecimalPlaces, int? maxDecimalPlaces)
    {
        // A value that already carries at most `max` fractional digits IS its own rounding to
        // `max` places, so only a value with more of them is rounded. The quantum exponent `q`
        // is exact (see FormatNumberInvariant); `-q` is the number of fractional digits stored.
        var rounded = value;
        if (maxDecimalPlaces is { } max && Decimal128.ILogB(Decimal128.GetQuantum(value)) < -max)
            rounded = Decimal128.Round(value, max, MidpointRounding.AwayFromZero);

        // The canonical positional spelling carries the stored quantum: its fractional digits may
        // end in zeros. `kept` is the length of the text without them (and without a decimal point
        // left bare), and `fractionalDigits` the digits that remain after the point.
        var text = FormatNumberInvariant(rounded);
        var kept = text.Length;
        var fractionalDigits = 0;
        var point = text.IndexOf('.');
        if (point >= 0)
        {
            while (text[kept - 1] == '0')
                kept--;

            fractionalDigits = kept - point - 1;
            if (fractionalDigits == 0)
                kept = point;
        }

        var padding = Math.Max(0, (minDecimalPlaces ?? 0) - fractionalDigits);
        if (padding == 0)
            return kept == text.Length ? text : text[..kept];

        var needsPoint = fractionalDigits == 0;
        return string.Create(
            kept + (needsPoint ? 1 : 0) + padding,
            (text, kept, needsPoint),
            static (destination, state) =>
            {
                state.text.AsSpan(0, state.kept).CopyTo(destination);
                var next = state.kept;
                if (state.needsPoint)
                    destination[next++] = '.';

                destination[next..].Fill('0');
            });
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

        return value.ToString(FixedPointFormat(Decimal128.ILogB(Decimal128.GetQuantum(value))), CultureInfo.InvariantCulture);
    }

    /// <summary>
    /// The fixed-point format that writes a finite value's stored digits exactly from its
    /// quantum exponent (see <see cref="FormatNumberInvariant"/>), shared with the stack-buffer path of
    /// <see cref="AppendAtom"/>.
    /// </summary>
    private static string FixedPointFormat(int quantumExponent)
    {
        var fractionalDigits = Math.Max(0, -quantumExponent);
        return fractionalDigits < FixedPointFormats.Length
            ? FixedPointFormats[fractionalDigits]
            : "F" + fractionalDigits.ToString(CultureInfo.InvariantCulture);
    }
}
