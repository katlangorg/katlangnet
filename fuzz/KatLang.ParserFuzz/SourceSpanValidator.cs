using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Shared source-span validity checks used by both the raw-parser invariants and the
/// frontend invariants. Reproduces the lexer's UTF-16 column model exactly (see
/// <c>Lexer.Tokenize</c>): a line boundary is <c>'\n'</c> only, <c>'\r'</c> is
/// transparent (advances neither line nor column), every other character advances the
/// column by one, and columns/lines are 1-based so the largest legal column on a line
/// is (visible width + 1) — the one-past-end position: the end-of-file position, and the
/// exclusive <see cref="SourceSpan.End"/> of a span that runs to the end of a line.
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

    /// <summary>
    /// The 1-based (line, column) of a UTF-16 code-unit OFFSET, under the same model as
    /// <see cref="LineWidths"/>: <c>'\n'</c> starts a line, <c>'\r'</c> is transparent, and every
    /// other code unit — including one half of a surrogate pair — advances the column by one.
    ///
    /// <para>This is the offset-side projection of the one model the whole harness shares, and it
    /// is what cross-checks the lexer: the lexer tracks line/column incrementally while scanning,
    /// this recomputes them from the token's recorded offset, and the two must agree for every
    /// token. An offset equal to the source length is legal and yields the end-of-file position.</para>
    /// </summary>
    public static (int Line, int Column) LineColumnAt(string source, int offset)
    {
        ArgumentNullException.ThrowIfNull(source);
        ArgumentOutOfRangeException.ThrowIfNegative(offset);
        ArgumentOutOfRangeException.ThrowIfGreaterThan(offset, source.Length);

        int line = 1;
        int column = 1;
        for (int i = 0; i < offset; i++)
        {
            char c = source[i];
            if (c == '\n') { line++; column = 1; }
            else if (c != '\r') { column++; }
        }

        return (line, column);
    }

    /// <summary>Returns null when the span is valid for the source, otherwise a short
    /// reason describing the violation. A span is half-open: its start must address a real
    /// coordinate or the one-past-end position of a line, and so must its exclusive end
    /// (an empty span at end of file is valid). The 1-based and start-before-end checks
    /// are the constructor's own invariants, repeated here so a <c>default</c> struct that
    /// bypassed construction is still reported rather than trusted.</summary>
    public static string? Validate(SourceSpan s, int[] lineWidths)
    {
        int maxLine = lineWidths.Length;
        var (start, end) = s;

        if (start.Line < 1) return "start line < 1";
        if (start.Column < 1) return "start column < 1";
        if (end.Line < 1) return "end line < 1";
        if (end.Column < 1) return "end column < 1";

        if (end.Line < start.Line) return "end line precedes start line";
        if (end.Line == start.Line && end.Column < start.Column)
            return "end column precedes start column";

        if (start.Line > maxLine) return $"start line {start.Line} > line count {maxLine}";
        if (end.Line > maxLine) return $"end line {end.Line} > line count {maxLine}";

        int startMax = lineWidths[start.Line - 1] + 1;
        int endMax = lineWidths[end.Line - 1] + 1;
        if (start.Column > startMax) return $"start column {start.Column} > line width+1 ({startMax})";
        if (end.Column > endMax) return $"end column {end.Column} > line width+1 ({endMax})";

        return null;
    }

    public static string Describe(SourceSpan? s)
        => s is { } span ? span.ToString() : "<null>";
}
