using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>
/// Resolves a cursor kind and bias to an exact UTF-16 offset in <c>[0, length]</c> by scanning the
/// built source and its lexer tokens for a meaningful boundary, with a deterministic fallback when
/// the feature is absent. Also computes the 1-based (line, column) position the tooling is queried
/// at — the one place the harness crosses from the exact code-unit model into the semantic model's
/// line/column coordinates.
/// </summary>
internal static class EditorCursor
{
    /// <summary>Resolves the cursor to an exact offset in <c>[0, source.Length]</c>.</summary>
    public static int Resolve(EditorParameters parameters, string source, int injectionOffset)
    {
        ArgumentNullException.ThrowIfNull(parameters);
        ArgumentNullException.ThrowIfNull(source);

        var length = source.Length;
        var bias = parameters.CursorBias;
        var (tokens, lexDiagnostics) = Lexer.Tokenize(source);

        var offset = parameters.Cursor switch
        {
            EditorCursorKind.StartOfFile => 0,
            EditorCursorKind.EndOfFile => length,
            EditorCursorKind.BeforeFirstToken => FirstRealTokenStart(tokens),
            EditorCursorKind.InsideFirstIdentifier => InsideFirstToken(tokens, TokenKind.Identifier, bias),
            EditorCursorKind.AfterFirstIdentifier => AfterFirstToken(tokens, TokenKind.Identifier),
            EditorCursorKind.BetweenIdentifierAndDot => IndexOf(source, '.', bias),
            EditorCursorKind.AfterDot => IndexOf(source, '.', bias) + 1,
            EditorCursorKind.AtSpreadMarker => AtSpreadMarker(source, bias),
            EditorCursorKind.InsideArgumentList => IndexOf(source, '(', bias) + 1,
            EditorCursorKind.AfterComma => IndexOf(source, ',', bias) + 1,
            EditorCursorKind.InsideString => InsideFirstToken(tokens, TokenKind.StringLiteral, bias + 1),
            EditorCursorKind.InsideComment => InsideFirstToken(tokens, TokenKind.Comment, bias + 1),
            EditorCursorKind.InsideWhitespace => IndexOfAny(source, " \t", bias),
            EditorCursorKind.AtCarriageReturn => IndexOf(source, '\r', bias),
            EditorCursorKind.BetweenCarriageReturnAndLineFeed => BetweenCrLf(source),
            EditorCursorKind.AfterLineFeed => IndexOf(source, '\n', bias) + 1,
            EditorCursorKind.SurrogatePairBoundary => SurrogatePairBoundary(source),
            EditorCursorKind.BeforeIsolatedSurrogate => IsolatedSurrogate(source, after: false),
            EditorCursorKind.AfterIsolatedSurrogate => IsolatedSurrogate(source, after: true),
            EditorCursorKind.InsideMalformedToken => InsideMalformed(tokens, lexDiagnostics, source, bias),
            EditorCursorKind.InsideDiagnosticSpan => InsideDiagnostic(lexDiagnostics, source, bias),
            EditorCursorKind.AtInjection => injectionOffset,
            EditorCursorKind.BeforeEndOfFile => Math.Max(0, length - 1),
            EditorCursorKind.PastEndOfFile => length,
            _ => 0,
        };

        if (offset < 0)
            offset = Fallback(length, bias);

        return Math.Clamp(offset, 0, length);
    }

    /// <summary>
    /// The 1-based (line, column) the tooling is queried at. For <see cref="EditorCursorKind.PastEndOfFile"/>
    /// it deliberately returns a column past the last line, an out-of-range request whose documented
    /// contract is a <c>null</c> resolution.
    /// </summary>
    public static (int Line, int Column) QueryPosition(EditorParameters parameters, string source, int cursorOffset)
    {
        ArgumentNullException.ThrowIfNull(parameters);
        ArgumentNullException.ThrowIfNull(source);

        var offset = Math.Clamp(cursorOffset, 0, source.Length);
        var (line, column) = SourceSpanValidator.LineColumnAt(source, offset);
        if (parameters.Cursor == EditorCursorKind.PastEndOfFile)
            column += parameters.CursorBias + 1;

        return (line, column);
    }

    private static int FirstRealTokenStart(IReadOnlyList<Token> tokens)
    {
        foreach (var token in tokens)
            if (token.Kind != TokenKind.EndOfFile)
                return token.Position;
        return 0;
    }

    private static int InsideFirstToken(IReadOnlyList<Token> tokens, TokenKind kind, int inset)
    {
        foreach (var token in tokens)
        {
            if (token.Kind != kind)
                continue;
            if (token.Length <= 0)
                return token.Position;
            return token.Position + Math.Min(inset, token.Length - 1);
        }

        return -1;
    }

    private static int AfterFirstToken(IReadOnlyList<Token> tokens, TokenKind kind)
    {
        foreach (var token in tokens)
            if (token.Kind == kind)
                return token.Position + token.Length;
        return -1;
    }

    private static int IndexOf(string source, char target, int bias)
    {
        var index = -1;
        for (var skip = 0; skip <= bias; skip++)
        {
            var next = source.IndexOf(target, index + 1);
            if (next < 0)
                return index < 0 ? -1 : index;
            index = next;
        }

        return index;
    }

    private static int IndexOfAny(string source, string targets, int bias)
    {
        var index = -1;
        for (var skip = 0; skip <= bias; skip++)
        {
            var next = source.IndexOfAny(targets.ToCharArray(), index + 1);
            if (next < 0)
                return index < 0 ? -1 : index;
            index = next;
        }

        return index;
    }

    /// <summary>
    /// Lands on a star's ATTACHMENT boundary — immediately before the star or immediately
    /// after it. That boundary is where the spread-versus-multiplication decision flips
    /// (a star directly attached to the preceding token with no same-line right operand is
    /// the spread marker; anything else multiplies), so it is the cursor position where
    /// editor tooling is most likely to disagree with the parser.
    /// </summary>
    private static int AtSpreadMarker(string source, int bias)
    {
        var star = source.IndexOf('*');
        return star < 0 ? -1 : star + (bias % 2 == 0 ? 0 : 1);
    }

    private static int BetweenCrLf(string source)
    {
        var cr = source.IndexOf('\r');
        while (cr >= 0)
        {
            if (cr + 1 < source.Length && source[cr + 1] == '\n')
                return cr + 1;
            cr = source.IndexOf('\r', cr + 1);
        }

        return -1;
    }

    private static int SurrogatePairBoundary(string source)
    {
        for (var i = 0; i + 1 < source.Length; i++)
            if (char.IsHighSurrogate(source[i]) && char.IsLowSurrogate(source[i + 1]))
                return i + 1;
        return -1;
    }

    private static int IsolatedSurrogate(string source, bool after)
    {
        for (var i = 0; i < source.Length; i++)
        {
            var c = source[i];
            var pairedHigh = char.IsHighSurrogate(c) && i + 1 < source.Length && char.IsLowSurrogate(source[i + 1]);
            var pairedLow = char.IsLowSurrogate(c) && i > 0 && char.IsHighSurrogate(source[i - 1]);
            if ((char.IsHighSurrogate(c) || char.IsLowSurrogate(c)) && !pairedHigh && !pairedLow)
                return after ? i + 1 : i;
        }

        return -1;
    }

    private static int InsideMalformed(
        IReadOnlyList<Token> tokens, IReadOnlyList<Diagnostic> lexDiagnostics, string source, int bias)
    {
        var bad = InsideFirstToken(tokens, TokenKind.Bad, bias);
        return bad >= 0 ? bad : InsideDiagnostic(lexDiagnostics, source, bias);
    }

    private static int InsideDiagnostic(IReadOnlyList<Diagnostic> diagnostics, string source, int bias)
    {
        foreach (var diagnostic in diagnostics)
        {
            if (diagnostic.Span is not { } span)
                continue;
            var offset = OffsetAtLineColumn(source, span.StartLineNumber, span.StartColumn);
            if (offset >= 0)
                return Math.Min(offset + (bias % 2), source.Length);
        }

        return -1;
    }

    /// <summary>Inverse of <see cref="SourceSpanValidator.LineColumnAt"/>: the offset of a 1-based
    /// (line, column) under the same model (<c>\n</c> starts a line, <c>\r</c> is transparent).
    /// Returns -1 when the (line, column) is past the end of the source.</summary>
    internal static int OffsetAtLineColumn(string source, int line, int column)
    {
        var currentLine = 1;
        var currentColumn = 1;
        for (var i = 0; i <= source.Length; i++)
        {
            if (currentLine == line && currentColumn == column)
                return i;
            if (i == source.Length)
                return -1;

            var c = source[i];
            if (c == '\n') { currentLine++; currentColumn = 1; }
            else if (c != '\r') { currentColumn++; }
        }

        return -1;
    }

    private static int Fallback(int length, int bias)
        => length == 0 ? 0 : Math.Clamp(bias * length / EditorTables.CursorBiasCount, 0, length);
}
