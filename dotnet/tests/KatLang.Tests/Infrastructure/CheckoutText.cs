namespace KatLang.TestInfrastructure;

/// <summary>Line-ending helpers for text whose bytes depend on checkout policy.</summary>
public static class CheckoutText
{
    public static TheoryData<string> LineEndingData => new()
    {
        "\n",
        "\r\n",
    };

    public static string WithLineEndings(string text, string lineEnding)
        => text.ReplaceLineEndings(lineEnding);

    public static string Normalize(string text)
        => text.ReplaceLineEndings("\n");
}
