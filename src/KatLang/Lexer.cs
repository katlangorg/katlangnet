using System.Numerics;

namespace KatLang;

/// <summary>
/// Tokenizes a KatLang source string into a list of tokens.
/// Digit-leading base-10 numeric literals may include a fractional part, a lowercase
/// <c>e</c> exponent with an optional sign, and underscore separators within digit runs.
/// The C# runtime stores numeric values as IEEE 754 <c>Decimal128</c> (parsed directly,
/// with no narrower intermediate representation); the Lean core intentionally
/// models numeric semantics abstractly with <c>Int</c>. Comments start with <c>#</c>.
/// </summary>
public static class Lexer
{
    private static readonly (string Name, TokenKind Kind)[] KeywordDefinitions =
    [
        ("div", TokenKind.KeywordDiv),
        ("mod", TokenKind.KeywordMod),
        ("and", TokenKind.KeywordAnd),
        ("or", TokenKind.KeywordOr),
        ("xor", TokenKind.KeywordXor),
        ("not", TokenKind.KeywordNot),
        ("public", TokenKind.KeywordPublic),
        ("open", TokenKind.KeywordOpen),
    ];

    private static readonly IReadOnlyDictionary<string, TokenKind> Keywords =
        KeywordDefinitions.ToDictionary(
            static keyword => keyword.Name,
            static keyword => keyword.Kind,
            StringComparer.Ordinal);

    // ── Identifier character policy ──────────────────────────────────────────
    // THE one authoritative identifier character policy: the tokenizer's scan
    // loop, the whole-string helpers below, and every identifier-shape consumer
    // (`CallableSignature` parameter-name validation, `KatLangError` display
    // heuristics) read these predicates, so the character rule cannot fork.
    // Classification is per UTF-16 CODE UNIT (System.Char): a supplementary-
    // plane letter arrives as a surrogate pair whose halves are not letters, so
    // it is never an identifier character, and combining marks are not
    // identifier characters (a precomposed accented letter is a letter; the
    // decomposed spelling is an identifier followed by an unexpected-character
    // diagnostic). Nothing normalizes source text. The identifier terminal
    // claims in KatLang.ebnf are mechanically pinned to these predicates by
    // EbnfLexicalSyncTests.

    /// <summary>
    /// Whether <paramref name="c"/> may START an identifier: an underscore or a
    /// UTF-16 code unit in Unicode letter category Lu, Ll, Lt, Lm, or Lo
    /// (<see cref="char.IsLetter(char)"/>).
    /// </summary>
    internal static bool IsIdentifierStartChar(char c)
        => char.IsLetter(c) || c == '_';

    /// <summary>
    /// Whether <paramref name="c"/> may CONTINUE an identifier: an
    /// identifier-start code unit or a Unicode decimal digit (category Nd,
    /// <see cref="char.IsDigit(char)"/>). A digit never STARTS an identifier
    /// because the number production claims a leading digit first.
    /// </summary>
    internal static bool IsIdentifierPartChar(char c)
        => char.IsLetterOrDigit(c) || c == '_';

    /// <summary>
    /// Whether <paramref name="text"/> is identifier-SHAPED — one
    /// identifier-start code unit followed by identifier-part code units — with
    /// NO reserved-keyword exclusion: a keyword spelling such as "open" is
    /// identifier-shaped even though it lexes as a keyword token. Shape-only
    /// consumers (AST-level parameter-name validation mirroring Lean
    /// `callableParameterNameIsIdentifierLike`, diagnostic display heuristics)
    /// use this; names that must be writable in source use
    /// <see cref="IsValidIdentifier"/>.
    /// </summary>
    internal static bool IsIdentifierShaped(string text)
    {
        if (text.Length == 0 || !IsIdentifierStartChar(text[0]))
            return false;

        for (var i = 1; i < text.Length; i++)
        {
            if (!IsIdentifierPartChar(text[i]))
                return false;
        }

        return true;
    }

    /// <summary>
    /// Whether <paramref name="text"/> is lexed as one identifier token rather than a
    /// keyword. Kept on the lexer so host-facing signature validation cannot drift from
    /// the language's identifier and keyword rules.
    /// </summary>
    public static bool IsValidIdentifier(string text)
        => IsIdentifierShaped(text) && ClassifyIdentifierOrKeyword(text) == TokenKind.Identifier;

    /// <summary>
    /// The reserved keyword spellings, exactly the words
    /// <see cref="ClassifyIdentifierOrKeyword"/> refuses to lex as identifiers.
    /// Editor tooling reads this instead of hardcoding the keyword set. Both
    /// this list and identifier classification are derived from the one
    /// keyword-definition table above.
    /// </summary>
    public static IReadOnlyList<string> KeywordNames { get; } =
        Array.AsReadOnly(KeywordDefinitions.Select(static keyword => keyword.Name).ToArray());

    private static TokenKind ClassifyIdentifierOrKeyword(string text)
        => Keywords.TryGetValue(text, out var keywordKind)
            ? keywordKind
            : TokenKind.Identifier;

    /// <summary>
    /// The KatLang-facing spelling of an unexpected code unit in a diagnostic. A
    /// visible character is quoted verbatim (<c>'@'</c>). A code unit with no glyph of
    /// its own — a control character, an invisible Unicode format character (bidi
    /// controls, zero-width spaces, byte-order marks), or an UNPAIRED surrogate — is
    /// named by its code point (<c>U+001B</c>, <c>U+D83D</c>) with its category, so the
    /// message itself is always well-formed, printable UTF-16 text: a raw control
    /// character would steer the terminal or log that displays the message, and a raw
    /// lone surrogate would make the message ill-formed (rendered as U+FFFD at every
    /// UTF-8 boundary). The span still locates the code unit exactly.
    /// </summary>
    internal static string DescribeUnexpectedCharacter(char c)
        => DescribeUnexpectedCharacter(c, char.GetUnicodeCategory(c));

    private static string DescribeUnexpectedCharacter(int codePoint, System.Globalization.UnicodeCategory category)
    {
        if (category == System.Globalization.UnicodeCategory.Control)
            return $"U+{codePoint:X4} (a control character)";
        if (category == System.Globalization.UnicodeCategory.Surrogate)
            return $"U+{codePoint:X4} (an unpaired surrogate code unit)";
        if (category == System.Globalization.UnicodeCategory.Format)
            return $"U+{codePoint:X4} (an invisible format character)";
        return $"'{char.ConvertFromUtf32(codePoint)}'";
    }

    /// <summary>
    /// Tokenizes <paramref name="source"/> into its tokens and lexical diagnostics. This is
    /// the supported way to obtain <see cref="Token"/> values: the list always ends with the
    /// one <see cref="TokenKind.EndOfFile"/> token, comments are emitted as
    /// <see cref="TokenKind.Comment"/> tokens (the parser skips them), and an unexpected
    /// character becomes a <see cref="TokenKind.Bad"/> token beside its diagnostic, so the
    /// tokens are in source order and every code unit outside whitespace belongs to
    /// exactly one token, whatever the input.
    /// </summary>
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
            // The parser skips them via its navigation helpers. A '#' starts a comment
            // regardless of what precedes it (whitespace before '#' is not required);
            // the comment ends before the next newline, which keeps its normal
            // line-boundary semantics, or at end of source.
            if (c == '#')
            {
                var commentStart = i;
                var commentLine = line;
                var commentCol = col;
                i += 1; col += 1;
                while (i < source.Length && source[i] != '\n' && source[i] != '\r')
                { i++; col++; }
                var commentText = source[(commentStart + 1)..i]; // text after the leading #
                tokens.Add(Token.CreateComment(commentText, commentStart, i - commentStart, commentLine, commentCol));
                continue;
            }

            // Numbers (integers and floating-point)
            if (char.IsDigit(c))
            {
                var start = i;
                var startLine = line;
                var startCol = col;
                ScanDigits(source, ref i, ref col);

                // Check for decimal part
                if (i + 1 < source.Length && source[i] == '.' && char.IsDigit(source[i + 1]))
                {
                    i++; col++; // skip dot
                    ScanDigits(source, ref i, ref col);
                }

                // Check for scientific notation part (e, optional sign, digits)
                if (i < source.Length && source[i] == 'e')
                {
                    var savedI = i;
                    var savedCol = col;
                    i++; col++; // tentatively skip 'e'
                    if (i < source.Length && (source[i] == '+' || source[i] == '-'))
                    { i++; col++; }
                    if (i < source.Length && char.IsDigit(source[i]))
                        ScanDigits(source, ref i, ref col);
                    else
                    { i = savedI; col = savedCol; } // no digit after 'e' — backtrack
                }

                // The scan above owns the literal's extent; conversion reads exactly
                // that text. Source text parses DIRECTLY into Decimal128 — no narrower
                // intermediate representation. A finite literal with more than 34
                // significant digits rounds to the nearest representable value (IEEE
                // round-half-even). Two failure modes stay distinct: text Decimal128
                // cannot parse at all (the scan admits any Unicode decimal digit so a
                // digit never starts an identifier, but only the ASCII digits 0-9 form
                // a value) is the invalid-literal diagnostic, while a well-formed
                // literal whose magnitude exceeds the Decimal128 range (parses to an
                // infinity) is the too-large diagnostic.
                var parsed = TryParseNumberLiteral(source.AsSpan(start, i - start), out var value);
                if (parsed && Decimal128.IsFinite(value))
                {
                    tokens.Add(Token.CreateNumber(value, start, i - start, startLine, startCol));
                }
                else
                {
                    // EndColumn is inclusive: `col` sits one past the last
                    // consumed digit (at least one digit was consumed).
                    var (message, code) = parsed
                        ? ("Number literal is too large.", DiagnosticCode.NumberLiteralTooLarge)
                        : ("Number literal is not a valid KatLang number: only the ASCII digits 0-9 are recognized (with an optional fraction and a lowercase 'e' exponent).", DiagnosticCode.InvalidNumberLiteral);
                    diagnostics.Add(new Diagnostic(
                        message,
                        DiagnosticSeverity.Error,
                        new SourceSpan(startLine, startCol, line, col - 1))
                    {
                        Code = code,
                    });
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
                    // EndColumn is inclusive: `col` sits one past the last
                    // consumed code unit (at least the opening quote).
                    diagnostics.Add(new Diagnostic(
                        "Unterminated string literal.",
                        DiagnosticSeverity.Error,
                        new SourceSpan(startLine, startCol, line, col - 1))
                    {
                        Code = DiagnosticCode.UnterminatedStringLiteral,
                    });
                }
                tokens.Add(Token.CreateStringLiteral(value, start, i - start, startLine, startCol));
                continue;
            }

            // Identifiers and keywords — the scan loop reads the one shared
            // identifier character policy above, so it cannot drift from
            // whole-string validation.
            if (IsIdentifierStartChar(c))
            {
                var start = i;
                var startLine = line;
                var startCol = col;
                while (i < source.Length && IsIdentifierPartChar(source[i]))
                { i++; col++; }

                var text = source[start..i];
                var wordKind = ClassifyIdentifierOrKeyword(text);
                var token = wordKind == TokenKind.Identifier
                    ? Token.CreateIdentifier(text, start, i - start, startLine, startCol)
                    : Token.Create(wordKind, start, i - start, startLine, startCol);
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
                            new SourceSpan(singleLine, singleCol, singleLine, singleCol))
                        {
                            Code = DiagnosticCode.UnexpectedCharacter,
                        });
                    }
                    break;
                case '(': tokens.Add(Token.Create(TokenKind.LParen,     singleStart, 1, singleLine, singleCol)); break;
                case ')': tokens.Add(Token.Create(TokenKind.RParen,     singleStart, 1, singleLine, singleCol)); break;
                case '{': tokens.Add(Token.Create(TokenKind.LBrace,     singleStart, 1, singleLine, singleCol)); break;
                case '}': tokens.Add(Token.Create(TokenKind.RBrace,     singleStart, 1, singleLine, singleCol)); break;
                case '[': tokens.Add(Token.Create(TokenKind.LBracket,   singleStart, 1, singleLine, singleCol)); break;
                case ']': tokens.Add(Token.Create(TokenKind.RBracket,   singleStart, 1, singleLine, singleCol)); break;
                case ',': tokens.Add(Token.Create(TokenKind.Comma,      singleStart, 1, singleLine, singleCol)); break;
                case ';': tokens.Add(Token.Create(TokenKind.Semicolon,  singleStart, 1, singleLine, singleCol)); break;
                case ':': tokens.Add(Token.Create(TokenKind.Colon,      singleStart, 1, singleLine, singleCol)); break;
                case '.': tokens.Add(Token.Create(TokenKind.Dot,        singleStart, 1, singleLine, singleCol)); break;
                case '~': tokens.Add(Token.Create(TokenKind.Tilde,      singleStart, 1, singleLine, singleCol)); break;
                default:
                    if (char.IsHighSurrogate(c) && i < source.Length && char.IsLowSurrogate(source[i]))
                    {
                        // A well-formed pair is one scalar. Supplementary format characters
                        // need the same printable description as BMP format characters;
                        // visible scalars remain quoted over both UTF-16 code units.
                        i++; col++;
                        tokens.Add(Token.Bad(singleStart, 2, singleLine, singleCol));
                        var description = DescribeUnexpectedCharacter(
                            char.ConvertToUtf32(source, singleStart),
                            System.Globalization.CharUnicodeInfo.GetUnicodeCategory(source, singleStart));
                        diagnostics.Add(new Diagnostic(
                            $"Unexpected character: {description}.",
                            DiagnosticSeverity.Error,
                            new SourceSpan(singleLine, singleCol, singleLine, singleCol + 1))
                        {
                            Code = DiagnosticCode.UnexpectedCharacter,
                        });
                        break;
                    }

                    tokens.Add(Token.Bad(singleStart, 1, singleLine, singleCol));
                    diagnostics.Add(new Diagnostic(
                        $"Unexpected character: {DescribeUnexpectedCharacter(c)}.",
                        DiagnosticSeverity.Error,
                        new SourceSpan(singleLine, singleCol, singleLine, singleCol))
                    {
                        Code = DiagnosticCode.UnexpectedCharacter,
                    });
                    break;
            }
        }

        tokens.Add(Token.EndOfFile(i, line, col));
        return (tokens, diagnostics);
    }

    /// <summary>
    /// Advances <paramref name="i"/> and <paramref name="col"/> past a run of digits, allowing
    /// underscore digit-separators between digits. Trailing underscores (not followed by a digit)
    /// are not consumed, preserving the invariant that <c>_</c> only appears between digits.
    /// </summary>
    private static void ScanDigits(string source, ref int i, ref int col)
    {
        while (i < source.Length && char.IsDigit(source[i]))
        {
            i++; col++;
            // Consume a run of underscores only when a digit follows — enforces
            // the rule that underscores must appear between digits.
            if (i < source.Length && source[i] == '_')
            {
                var savedI = i;
                var savedCol = col;
                while (i < source.Length && source[i] == '_') { i++; col++; }
                if (i >= source.Length || !char.IsDigit(source[i]))
                {
                    // Underscore not followed by a digit: back up, stop scanning.
                    i = savedI;
                    col = savedCol;
                    break;
                }
            }
        }
    }

    /// <summary>
    /// Converts the text of an already-scanned numeric literal to its value. The scan loop
    /// alone decides where a literal ends; this reads exactly the selected text, so a false
    /// result means Decimal128 could not read it (a non-ASCII digit), never that the scan
    /// stopped early. An ordinary literal parses straight from the span over the source.
    /// Digit separators — admitted by <see cref="ScanDigits"/> only between digits — are not
    /// Decimal128 syntax, so a literal containing one is first copied without them into one
    /// exactly-sized temporary string: the rare separator form pays for the copy, the common
    /// form allocates nothing.
    /// </summary>
    private static bool TryParseNumberLiteral(ReadOnlySpan<char> literal, out Decimal128 value)
    {
        if (literal.Contains('_'))
        {
            var stripped = string.Create(literal.Length - literal.Count('_'), literal, static (destination, source) =>
            {
                var written = 0;
                foreach (var c in source)
                {
                    if (c != '_')
                        destination[written++] = c;
                }
            });
            return Decimal128.TryParse(
                stripped,
                System.Globalization.NumberStyles.Float,
                System.Globalization.CultureInfo.InvariantCulture,
                out value);
        }

        return Decimal128.TryParse(
            literal,
            System.Globalization.NumberStyles.Float,
            System.Globalization.CultureInfo.InvariantCulture,
            out value);
    }
}
