namespace KatLang.Rendering;

/// <summary>
/// Minimal text sink shared by canonical value rendering and presentation
/// formatters. The core abstraction deliberately contains no formatter policy.
/// </summary>
internal interface IDisplaySink
{
    bool Append(string text);

    bool Append(char c, int count);
}

/// <summary>
/// A sink that knows how many more UTF-16 code units it can accept. A string
/// policy uses it to refuse a leaf whose RAW length already exceeds the
/// remaining capacity — quotes only add length — without first scanning the
/// content to decide whether quotes are needed.
/// </summary>
internal interface ICapacityDisplaySink : IDisplaySink
{
    long RemainingCapacity { get; }
}
