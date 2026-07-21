using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Shared source-span validity checks used by both the raw-parser invariants and the
/// frontend invariants. Reproduces the lexer's UTF-16 column model exactly (see
/// <c>Lexer.Tokenize</c>): a line boundary is <c>'\n'</c> only, <c>'\r'</c> is
/// transparent (advances neither line nor column), every other character advances the
/// column by one, and columns/lines are 1-based so the largest legal column on a line
/// is (visible width + 1) — the one-past-end position used for EOF / end-exclusive spans.
/// </summary>
internal static class SourceSpanValidator
{
    /// <summary>Column width (max real-character column) for each 1-based line. Always
    /// has at least one entry.</summary>
    public static int[] LineWidths(string source)
    {
        var widths = new List<int>();
        int current = 0;
        foreach (char c in source)
        {
            if (c == '\n') { widths.Add(current); current = 0; }
            else if (c != '\r') { current++; }
        }
        widths.Add(current);
        return [.. widths];
    }

    /// <summary>Returns null when the span is valid for the source, otherwise a short
    /// reason describing the violation.</summary>
    public static string? Validate(SourceSpan s, int[] lineWidths)
    {
        int maxLine = lineWidths.Length;

        if (s.StartLineNumber < 1) return "start line < 1";
        if (s.StartColumn < 1) return "start column < 1";
        if (s.EndLineNumber < 1) return "end line < 1";
        if (s.EndColumn < 1) return "end column < 1";

        if (s.EndLineNumber < s.StartLineNumber) return "end line precedes start line";
        if (s.EndLineNumber == s.StartLineNumber && s.EndColumn < s.StartColumn)
            return "end column precedes start column";

        if (s.StartLineNumber > maxLine) return $"start line {s.StartLineNumber} > line count {maxLine}";
        if (s.EndLineNumber > maxLine) return $"end line {s.EndLineNumber} > line count {maxLine}";

        int startMax = lineWidths[s.StartLineNumber - 1] + 1;
        int endMax = lineWidths[s.EndLineNumber - 1] + 1;
        if (s.StartColumn > startMax) return $"start column {s.StartColumn} > line width+1 ({startMax})";
        if (s.EndColumn > endMax) return $"end column {s.EndColumn} > line width+1 ({endMax})";

        return null;
    }

    public static string Describe(SourceSpan? s)
        => s is null ? "<null>" : $"({s.StartLineNumber},{s.StartColumn})-({s.EndLineNumber},{s.EndColumn})";
}
