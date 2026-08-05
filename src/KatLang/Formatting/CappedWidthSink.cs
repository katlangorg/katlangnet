using KatLang.Rendering;

namespace KatLang.Formatting;

/// <summary>
/// Width-capped measuring sink. It counts UTF-16 code units without building
/// text and refuses the first append that would cross the cap.
/// </summary>
internal sealed class CappedWidthSink : IDisplaySink
{
    private long _remaining;

    public void Reset(int cap) => _remaining = cap;

    public bool Append(string text)
    {
        _remaining -= text.Length;
        return _remaining >= 0;
    }

    public bool Append(char c, int count)
    {
        _remaining -= count;
        return _remaining >= 0;
    }
}
