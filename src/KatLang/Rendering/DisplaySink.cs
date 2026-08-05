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
