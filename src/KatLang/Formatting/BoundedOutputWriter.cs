using KatLang.Rendering;

namespace KatLang.Formatting;

/// <summary>
/// The bounded text writer handed to <see cref="OutputFormatter"/>
/// implementations. It wraps the same all-or-nothing display sink canonical
/// rendering uses: every append is checked BEFORE it happens and charged its
/// actual UTF-16 length (text, spaces, quotes, and newlines alike), so a
/// formatter can never produce more output than the effective display limit.
/// Once an append is refused, <see cref="LimitExceeded"/> stays true, no
/// further output is produced, and the partial rendering is discarded in
/// favor of the established bounded overflow response.
/// </summary>
public sealed class BoundedOutputWriter
{
    private readonly BoundedDisplayWriter _core;
    private readonly DisplayOptions _displayOptions;

    internal BoundedOutputWriter(BoundedDisplayWriter core, DisplayOptions displayOptions)
    {
        _core = core;
        _displayOptions = displayOptions;
    }

    /// <summary>The underlying bounded sink shared with canonical rendering.</summary>
    internal BoundedDisplayWriter Core => _core;

    /// <summary>The evaluated run's display options (<c>DisplayDecimals</c> and the display limit).</summary>
    internal DisplayOptions DisplayOptions => _displayOptions;

    /// <summary>True once an append was refused; no further output is produced.</summary>
    public bool LimitExceeded => _core.LimitExceeded;

    /// <summary>Appends text; false when the display limit refuses it.</summary>
    public bool Append(string text)
    {
        ArgumentNullException.ThrowIfNull(text);
        return _core.Append(text);
    }

    /// <summary>
    /// Appends one numeric atom in canonical culture-invariant form, honoring
    /// the run's <c>DisplayDecimals</c> property exactly like canonical
    /// display.
    /// </summary>
    public bool AppendAtom(decimal value)
        => _core.Append(ValueTextRenderer.FormatAtom(value, _displayOptions));

    /// <summary>Appends repeated spaces (indentation); each space is charged.</summary>
    public bool AppendSpaces(int count)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(count);
        return _core.Append(' ', count);
    }
}
