using KatLang.Rendering;

namespace KatLang.Formatting;

/// <summary>
/// Width-capped measuring sink. It counts UTF-16 code units without building
/// text and refuses the first append that would cross the cap.
/// </summary>
internal sealed class CappedWidthSink : ICapacityDisplaySink
{
    private long _remaining;

    public long RemainingCapacity => Math.Max(_remaining, 0);

    public void Reset(int cap) => _remaining = cap;

    public bool Append(string text) => Charge(text.Length);

    public bool Append(ReadOnlySpan<char> text) => Charge(text.Length);

    public bool Append(char c, int count) => Charge(count);

    private bool Charge(int length)
    {
        _remaining -= length;
        return _remaining >= 0;
    }
}
