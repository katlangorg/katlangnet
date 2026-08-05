using System.Globalization;

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

    internal static string FormatAtom(decimal value, DisplayOptions displayOptions)
    {
        if (displayOptions.Decimals is not { } decimals)
            return value.ToString(CultureInfo.InvariantCulture);

        if (value == Math.Truncate(value) && DecimalScale(value) == 0)
            return value.ToString(CultureInfo.InvariantCulture);

        var format = "F" + decimals.ToString(CultureInfo.InvariantCulture);
        return value.ToString(format, CultureInfo.InvariantCulture);
    }

    private static int DecimalScale(decimal value)
        => (decimal.GetBits(value)[3] >> 16) & 0xFF;
}
