namespace KatLang;

/// <summary>
/// Tokenizes a KatLang source string into a list of tokens.
/// Integers only (no floats). Comments start with <c>//</c>.
/// </summary>
public static class Lexer
{
    public static (IReadOnlyList<Token> Tokens, IReadOnlyList<Diagnostic> Diagnostics) Tokenize(string source)
    {
        var tokens = new List<Token>();
        var diagnostics = new List<Diagnostic>();
        var i = 0;
        var line = 1;
        var col = 1;

        while (i < source.Length)
        {
            var c = source[i];

            // Whitespace (including newlines — no newline tokens)
            if (char.IsWhiteSpace(c))
            {
                if (c == '\n') { line++; col = 1; }
                else if (c != '\r') { col++; }
                i++;
                continue;
            }

            // Comments — emitted as Comment tokens so callers (e.g. colorizers) can use them.
            // The parser skips them via its navigation helpers.
            if (c == '/' && i + 1 < source.Length && source[i + 1] == '/')
            {
                var commentStart = i;
                var commentLine = line;
                var commentCol = col;
                i += 2; col += 2;
                while (i < source.Length && source[i] != '\n' && source[i] != '\r')
                { i++; col++; }
                var commentText = source[(commentStart + 2)..i]; // text after the leading //
                tokens.Add(Token.CreateComment(commentText, commentStart, i - commentStart, commentLine, commentCol));
                continue;
            }

            // Numbers (integers and floating-point)
            if (char.IsDigit(c))
            {
                var start = i;
                var startLine = line;
                var startCol = col;
                while (i < source.Length && char.IsDigit(source[i]))
                { i++; col++; }

                // Check for decimal part
                if (i + 1 < source.Length && source[i] == '.' && char.IsDigit(source[i + 1]))
                {
                    i++; col++; // skip dot
                    while (i < source.Length && char.IsDigit(source[i]))
                    { i++; col++; }
                }

                var text = source[start..i];
                if (decimal.TryParse(text, System.Globalization.NumberStyles.Number, System.Globalization.CultureInfo.InvariantCulture, out var value))
                {
                    tokens.Add(Token.CreateNumber(value, start, i - start, startLine, startCol));
                }
                else
                {
                    diagnostics.Add(new Diagnostic(
                        "Number literal is too large.",
                        DiagnosticSeverity.Error,
                        new SourceSpan(startLine, startCol, line, col)));
                    tokens.Add(Token.CreateNumber(0, start, i - start, startLine, startCol));
                }
                continue;
            }

            // String literals
            if (c == '\'')
            {
                var start = i;
                var startLine = line;
                var startCol = col;
                i++; col++; // skip opening quote
                var valueStart = i;
                while (i < source.Length && source[i] != '\'' && source[i] != '\n' && source[i] != '\r')
                { i++; col++; }
                var value = source[valueStart..i];
                if (i < source.Length && source[i] == '\'')
                { i++; col++; } // skip closing quote
                else
                {
                    diagnostics.Add(new Diagnostic(
                        "Unterminated string literal.",
                        DiagnosticSeverity.Error,
                        new SourceSpan(startLine, startCol, line, col)));
                }
                tokens.Add(Token.CreateStringLiteral(value, start, i - start, startLine, startCol));
                continue;
            }

            // Identifiers and keywords
            if (char.IsLetter(c) || c == '_')
            {
                var start = i;
                var startLine = line;
                var startCol = col;
                while (i < source.Length && (char.IsLetterOrDigit(source[i]) || source[i] == '_'))
                { i++; col++; }

                var text = source[start..i];
                var token = text switch
                {
                    "div"    => Token.Create(TokenKind.KeywordDiv, start, i - start, startLine, startCol),
                    "mod"    => Token.Create(TokenKind.KeywordMod, start, i - start, startLine, startCol),
                    "and"    => Token.Create(TokenKind.KeywordAnd, start, i - start, startLine, startCol),
                    "or"     => Token.Create(TokenKind.KeywordOr, start, i - start, startLine, startCol),
                    "xor"    => Token.Create(TokenKind.KeywordXor, start, i - start, startLine, startCol),
                    "not"    => Token.Create(TokenKind.KeywordNot, start, i - start, startLine, startCol),
                    "public" => Token.Create(TokenKind.KeywordPublic, start, i - start, startLine, startCol),
                    "open"   => Token.Create(TokenKind.KeywordOpen, start, i - start, startLine, startCol),
                    _        => Token.CreateIdentifier(text, start, i - start, startLine, startCol),
                };
                tokens.Add(token);
                continue;
            }

            // Single-character tokens
            var singleStart = i;
            var singleLine = line;
            var singleCol = col;
            i++; col++;
            switch (c)
            {
                case '+': tokens.Add(Token.Create(TokenKind.Plus,      singleStart, 1, singleLine, singleCol)); break;
                case '-': tokens.Add(Token.Create(TokenKind.Minus,     singleStart, 1, singleLine, singleCol)); break;
                case '*': tokens.Add(Token.Create(TokenKind.Star,      singleStart, 1, singleLine, singleCol)); break;
                case '/': tokens.Add(Token.Create(TokenKind.Slash,     singleStart, 1, singleLine, singleCol)); break;
                case '^': tokens.Add(Token.Create(TokenKind.Caret,     singleStart, 1, singleLine, singleCol)); break;
                case '<':
                    if (i < source.Length && source[i] == '=')
                    { i++; col++; tokens.Add(Token.Create(TokenKind.LessEqual, singleStart, 2, singleLine, singleCol)); }
                    else tokens.Add(Token.Create(TokenKind.LessThan, singleStart, 1, singleLine, singleCol));
                    break;
                case '>':
                    if (i < source.Length && source[i] == '=')
                    { i++; col++; tokens.Add(Token.Create(TokenKind.GreaterEqual, singleStart, 2, singleLine, singleCol)); }
                    else tokens.Add(Token.Create(TokenKind.GreaterThan, singleStart, 1, singleLine, singleCol));
                    break;
                case '=':
                    if (i < source.Length && source[i] == '=')
                    { i++; col++; tokens.Add(Token.Create(TokenKind.EqualEqual, singleStart, 2, singleLine, singleCol)); }
                    else tokens.Add(Token.Create(TokenKind.Equals, singleStart, 1, singleLine, singleCol));
                    break;
                case '!':
                    if (i < source.Length && source[i] == '=')
                    { i++; col++; tokens.Add(Token.Create(TokenKind.BangEqual, singleStart, 2, singleLine, singleCol)); }
                    else
                    {
                        tokens.Add(Token.Bad(singleStart, 1, singleLine, singleCol));
                        diagnostics.Add(new Diagnostic(
                            "Unexpected character: '!'. Use 'not' for logical negation.",
                            DiagnosticSeverity.Error,
                            new SourceSpan(singleLine, singleCol, singleLine, singleCol)));
                    }
                    break;
                case '(': tokens.Add(Token.Create(TokenKind.LParen,     singleStart, 1, singleLine, singleCol)); break;
                case ')': tokens.Add(Token.Create(TokenKind.RParen,     singleStart, 1, singleLine, singleCol)); break;
                case '{': tokens.Add(Token.Create(TokenKind.LBrace,     singleStart, 1, singleLine, singleCol)); break;
                case '}': tokens.Add(Token.Create(TokenKind.RBrace,     singleStart, 1, singleLine, singleCol)); break;
                case ',': tokens.Add(Token.Create(TokenKind.Comma,      singleStart, 1, singleLine, singleCol)); break;
                case ';': tokens.Add(Token.Create(TokenKind.Semicolon,  singleStart, 1, singleLine, singleCol)); break;
                case ':': tokens.Add(Token.Create(TokenKind.Colon,      singleStart, 1, singleLine, singleCol)); break;
                case '.': tokens.Add(Token.Create(TokenKind.Dot,        singleStart, 1, singleLine, singleCol)); break;
                case '~': tokens.Add(Token.Create(TokenKind.Tilde,      singleStart, 1, singleLine, singleCol)); break;
                default:
                    tokens.Add(Token.Bad(singleStart, 1, singleLine, singleCol));
                    diagnostics.Add(new Diagnostic(
                        $"Unexpected character: '{c}'.",
                        DiagnosticSeverity.Error,
                        new SourceSpan(singleLine, singleCol, singleLine, singleCol)));
                    break;
            }
        }

        tokens.Add(Token.EndOfFile(i, line, col));
        return (tokens, diagnostics);
    }
}
