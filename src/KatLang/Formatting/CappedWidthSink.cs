using KatLang.Rendering;

namespace KatLang.Formatting;

/// <summary>
/// Width-capped measuring sink. It counts UTF-16 code units and refuses the
/// first append that would cross the cap. A measurement can keep its accepted
/// text for an inline write. Lookahead only needs the width.
/// </summary>
internal sealed class CappedWidthSink : ICapacityDisplaySink
{
    private const int InitialTextCapacity = 32;

    private long _remaining;
    private bool _keepText;
    private char[] _text = [];
    private int _length;

    public long RemainingCapacity => Math.Max(_remaining, 0);

    /// <summary>The text accepted by the current measurement when requested.</summary>
    public ReadOnlySpan<char> Text => _text.AsSpan(0, _length);

    public void Reset(int cap, bool keepText = false)
    {
        _remaining = cap;
        _keepText = keepText;
        _length = 0;
    }

    public bool Append(string text) => Append(text.AsSpan());

    public bool Append(ReadOnlySpan<char> text)
    {
        if (!Charge(text.Length)) return false;
        if (_keepText)
            text.CopyTo(Room(text.Length));
        return true;
    }

    public bool Append(char c, int count)
    {
        if (!Charge(count)) return false;
        if (_keepText)
            Room(count).Fill(c);
        return true;
    }

    private bool Charge(int length)
    {
        _remaining -= length;
        return _remaining >= 0;
    }

    /// <summary>
    /// The next <paramref name="count"/> code units of the kept text. Only an
    /// accepted append asks, so the kept text never exceeds the cap, and the
    /// buffer grows by doubling up to the current cap
    /// (<c>_remaining + length</c> once the append is charged).
    /// </summary>
    private Span<char> Room(int count)
    {
        var length = _length + count;
        if (length > _text.Length)
        {
            var doubled = Math.Max(InitialTextCapacity, 2L * _text.Length);
            Array.Resize(ref _text, (int)Math.Max(length, Math.Min(doubled, _remaining + length)));
        }

        var room = _text.AsSpan(_length, count);
        _length = length;
        return room;
    }
}
