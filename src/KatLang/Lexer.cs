using System.Numerics;
using System.Text;

namespace KatLang;

/// <summary>
/// Tokenizes a KatLang source string into a list of tokens.
/// Digit-leading base-10 numeric literals may include a fractional part, a lowercase
/// <c>e</c> exponent with an optional sign, and underscore separators within digit runs.
/// The C# runtime stores numeric values as IEEE 754 <c>Decimal128</c> (parsed directly,
/// with no narrower intermediate representation); the Lean core intentionally
/// models numeric semantics abstractly with <c>Int</c>. Comments start with <c>#</c>.
/// Single-quoted strings are raw text with no escapes; double-quoted strings decode the escapes
/// <c>\"</c>, <c>\\</c>, <c>\n</c>, <c>\t</c> and the doubled braces <c>{{</c> / <c>}}</c>, and may
/// hold interpolation holes (see <c>DoubleQuotedStringLexer</c>).
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
        ("true", TokenKind.KeywordTrue),
        ("false", TokenKind.KeywordFalse),
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
    /// <exception cref="ArgumentNullException"><paramref name="text"/> is null.</exception>
    public static bool IsValidIdentifier(string text)
    {
        ArgumentNullException.ThrowIfNull(text);
        return IsIdentifierShaped(text) && ClassifyIdentifierOrKeyword(text) == TokenKind.Identifier;
    }

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

    // A well-formed surrogate pair at `index` is one scalar: described by its code point and
    // category, so a supplementary format character reads like a BMP one.
    private static string DescribeUnexpectedPair(string source, int index)
        => DescribeUnexpectedCharacter(
            char.ConvertToUtf32(source, index),
            System.Globalization.CharUnicodeInfo.GetUnicodeCategory(source, index));

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
    /// <para>The token list is always complete. The diagnostic list is bounded like every
    /// diagnostic list KatLang produces
    /// (<see cref="SourceProcessingLimits.MaxSupportedDiagnosticCount"/>): past that many lexical
    /// errors it keeps the first ones and ends with one
    /// <see cref="DiagnosticCode.DiagnosticCountExceeded"/> diagnostic, while every unrecognized
    /// character is still its own <see cref="TokenKind.Bad"/> token.</para>
    /// </summary>
    /// <exception cref="ArgumentNullException"><paramref name="source"/> is null.</exception>
    public static (IReadOnlyList<Token> Tokens, IReadOnlyList<Diagnostic> Diagnostics) Tokenize(string source)
    {
        ArgumentNullException.ThrowIfNull(source);
        var diagnostics = new DiagnosticBag();
        var tokens = Tokenize(source, diagnostics, lexicalErrorStarts: null);
        return (tokens, Array.AsReadOnly(diagnostics.ToArray()));
    }

    /// <summary>
    /// Tokenizes <paramref name="source"/>, reporting lexical diagnostics into the operation's
    /// bag. <paramref name="lexicalErrorStarts"/>, when supplied, receives the start of EVERY
    /// lexical error in source order — whether or not the bag stores its diagnostic — because
    /// the parser's clause-head recovery asks where lexical errors are, and that answer must not
    /// depend on the diagnostic budget.
    /// </summary>
    internal static IReadOnlyList<Token> Tokenize(string source, DiagnosticBag diagnostics, List<SourcePosition>? lexicalErrorStarts)
    {
        var tokens = new List<Token>();
        var i = 0;
        var line = 1;
        var col = 1;
        // Scratch state of the double-quoted string lexer, allocated on first use and reused
        // for every later string of the source.
        DoubleQuotedStringLexer? doubleQuoted = null;

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

            // Double-quoted strings, with their escapes and interpolation holes. A hole's
            // tokens are lexed by the same code-token lexer as the rest of the source.
            if (c == '"')
            {
                doubleQuoted ??= new DoubleQuotedStringLexer();
                doubleQuoted.Lex(source, ref i, ref col, line, tokens, diagnostics, lexicalErrorStarts);
                continue;
            }

            LexCodeToken(source, ref i, ref col, line, tokens, diagnostics, lexicalErrorStarts);
        }

        tokens.Add(Token.EndOfFile(i, line, col));
        return tokens.AsReadOnly();
    }

    /// <summary>
    /// Lexes ONE code token that starts at <paramref name="i"/>, which is neither whitespace,
    /// a comment start nor a double quote: a number, a single-quoted string, an identifier or
    /// keyword, an operator or delimiter, or an unexpected character (a <see cref="TokenKind.Bad"/>
    /// token beside its diagnostic). The top level of the source and every interpolation hole
    /// share this one implementation, so a hole's code is lexed exactly like code anywhere else.
    /// A token never crosses a line break, so <paramref name="line"/> is unchanged.
    /// </summary>
    private static void LexCodeToken(
        string source,
        ref int i,
        ref int col,
        int line,
        List<Token> tokens,
        DiagnosticBag diagnostics,
        List<SourcePosition>? lexicalErrorStarts)
    {
        var c = source[i];

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
                // The diagnostic covers exactly the scanned literal: the placeholder
                // token's span, whose exclusive end is the lexer's live cursor column
                // (one past the last consumed digit; at least one digit was consumed).
                var placeholder = Token.CreateNumber(0, start, i - start, startLine, startCol);
                var (message, code) = parsed
                    ? ("Number literal is too large.", DiagnosticCode.NumberLiteralTooLarge)
                    : ("Number literal is not a valid KatLang number: only the ASCII digits 0-9 are recognized (with an optional fraction and a lowercase 'e' exponent).", DiagnosticCode.InvalidNumberLiteral);
                diagnostics.Report(code, message, placeholder.Span);
                lexicalErrorStarts?.Add(placeholder.Span.Start);
                tokens.Add(placeholder);
            }
            return;
        }

        // Single-quoted string literals: raw text with no escapes, ended by the next quote
        // or the end of the line. Their payload is exactly the source text between the quotes.
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
            var terminated = i < source.Length && source[i] == '\'';
            if (terminated)
            { i++; col++; } // skip closing quote
            var literal = Token.CreateStringLiteral(value, start, i - start, startLine, startCol);
            if (!terminated)
            {
                // The diagnostic covers exactly the consumed text — the token's span,
                // whose exclusive end is the lexer's live cursor column (at least the
                // opening quote was consumed; the literal ends before the line break
                // or the end of input, so it never crosses a line).
                diagnostics.Report(DiagnosticCode.UnterminatedStringLiteral, "Unterminated string literal.", literal.Span);
                lexicalErrorStarts?.Add(literal.Span.Start);
            }
            tokens.Add(literal);
            return;
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
            return;
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
                    var bang = Token.Bad(singleStart, 1, singleLine, singleCol);
                    tokens.Add(bang);
                    diagnostics.Report(
                        DiagnosticCode.UnexpectedCharacter,
                        "Unexpected character: '!'. Use 'not' for logical negation.",
                        bang.Span);
                    lexicalErrorStarts?.Add(bang.Span.Start);
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
                    var pair = Token.Bad(singleStart, 2, singleLine, singleCol);
                    tokens.Add(pair);
                    diagnostics.Report(
                        DiagnosticCode.UnexpectedCharacter,
                        pair.Span,
                        (source, singleStart),
                        static pairAt => $"Unexpected character: {DescribeUnexpectedPair(pairAt.source, pairAt.singleStart)}.");
                    lexicalErrorStarts?.Add(pair.Span.Start);
                    break;
                }

                var unexpected = Token.Bad(singleStart, 1, singleLine, singleCol);
                tokens.Add(unexpected);
                diagnostics.Report(
                    DiagnosticCode.UnexpectedCharacter,
                    unexpected.Span,
                    c,
                    static character => $"Unexpected character: {DescribeUnexpectedCharacter(character)}.");
                lexicalErrorStarts?.Add(unexpected.Span.Start);
                break;
        }
    }

    /// <summary>
    /// Lexes double-quoted strings (STR-02). The text of a double-quoted string supports exactly
    /// the escapes <c>\"</c>, <c>\\</c>, <c>\n</c> and <c>\t</c> and the doubled braces <c>{{</c> and
    /// <c>}}</c>; a single <c>{</c> opens an INTERPOLATION HOLE — ordinary code, lexed by
    /// <see cref="LexCodeToken"/>, that ends at the first <c>}</c> at the hole's own brace depth zero
    /// — so a hole may contain brace blocks and strings of either kind, interpolated strings
    /// included. Everything lies on one physical line.
    /// <para><b>Two passes over a string, both linear.</b> <see cref="ScanExtent"/> first finds
    /// where the OUTERMOST string ends, structurally and without reporting anything; nested strings
    /// are part of that one scan. An unterminated string is then ONE unterminated
    /// <see cref="TokenKind.StringLiteral"/> token running to the end of the line with ONE
    /// diagnostic at the innermost open construct — never a flood of reports from a line whose
    /// structure is already broken, and never tokens that an enclosing construct could not close.
    /// A terminated string is tokenized by <see cref="LexTerminated"/>, which reports in source
    /// order. The structural guarantee the parser relies on follows: every
    /// <see cref="TokenKind.InterpolatedStringStart"/> has its
    /// <see cref="TokenKind.InterpolatedStringEnd"/> and every
    /// <see cref="TokenKind.InterpolationHoleOpen"/> its <see cref="TokenKind.InterpolationHoleClose"/>,
    /// properly nested, on the same line.</para>
    /// <para><b>Hole-free strings are string literals.</b> A string's text is decoded as it is
    /// scanned, and its token form is decided only when the scan reaches the string's closing quote
    /// or its first hole: a string that ends first is ONE <see cref="TokenKind.StringLiteral"/>
    /// token carrying the decoded text, exactly like a single-quoted literal for every consumer
    /// (expressions, clause-head patterns, <c>open</c> targets, <c>load</c> URLs). No string is
    /// scanned twice by the second pass, so deep nesting stays linear.</para>
    /// <para>The frame stack lives on the heap: nothing here recurses, whatever the nesting depth
    /// (the parser's recursion budget bounds the nesting it accepts).</para>
    /// </summary>
    private sealed class DoubleQuotedStringLexer
    {
        /// <summary>One open construct: a string's text, or a hole with its own brace depth.</summary>
        private struct Frame
        {
            public bool IsHole;

            /// <summary>Hole: braces opened inside the hole and not yet closed.</summary>
            public int Depth;

            /// <summary>
            /// String: no token has been emitted for it yet, because neither its closing quote nor
            /// its first hole has been reached; it becomes one StringLiteral token if it ends first.
            /// </summary>
            public bool Pending;

            /// <summary>The index of the construct's opening <c>"</c> or <c>{</c>, and its column.</summary>
            public int Start;
            public int StartColumn;
        }

        private enum OpenConstruct { DoubleQuotedText, NestedDoubleQuotedText, Hole, SingleQuotedString }

        private readonly List<Frame> _frames = [];
        private readonly StringBuilder _text = new();

        /// <summary>Lexes the double-quoted string whose opening quote is <c>source[i]</c>.</summary>
        public void Lex(
            string source,
            ref int i,
            ref int col,
            int line,
            List<Token> tokens,
            DiagnosticBag diagnostics,
            List<SourcePosition>? lexicalErrorStarts)
        {
            var start = i;
            var startCol = col;
            if (!ScanExtent(source, start, out var end, out var innermostOpener, out var innermost))
            {
                // One token and one diagnostic for the rest of the line. The token is a string
                // literal like every unterminated single-quoted one (its payload is the raw text
                // after the quote); nothing inside it is lexed, so nothing inside it is reported.
                var length = end - start;
                tokens.Add(Token.CreateStringLiteral(source[(start + 1)..end], start, length, line, startCol));
                var span = new SourceSpan(line, startCol + (innermostOpener - start), line, startCol + length);
                switch (innermost)
                {
                    case OpenConstruct.Hole:
                        diagnostics.Report(
                            DiagnosticCode.UnterminatedInterpolationHole,
                            "Unterminated interpolation hole: close the hole with '}' and the string with '\"' on the same line.",
                            span);
                        break;
                    case OpenConstruct.NestedDoubleQuotedText:
                        // The usual cause is a hole whose '}' is missing (`"{x"`): its '"' then
                        // opens a string INSIDE the hole rather than closing the outer one.
                        diagnostics.Report(
                            DiagnosticCode.UnterminatedStringLiteral,
                            "Unterminated string literal: this '\"' stands inside an interpolation hole that is still open, so it begins a string within the hole. Close the hole with '}' before the closing '\"'.",
                            span);
                        break;
                    default:
                        diagnostics.Report(DiagnosticCode.UnterminatedStringLiteral, "Unterminated string literal.", span);
                        break;
                }

                lexicalErrorStarts?.Add(span.Start);
                i = end;
                col = startCol + length;
                return;
            }

            LexTerminated(source, ref i, ref col, line, tokens, diagnostics, lexicalErrorStarts);
        }

        /// <summary>
        /// The structural pre-scan of the double-quoted string opened at <paramref name="start"/>:
        /// returns whether it is closed on its line and the index just past it (or the index of the
        /// line break / end of input that ends it). For an unterminated string it also reports the
        /// INNERMOST construct still open there and where that construct opened. It decodes and
        /// reports nothing; it only follows the same structure <see cref="LexTerminated"/> lexes:
        /// in string text an escape consumes its backslash and the character after it, a doubled
        /// brace is one unit, a single <c>{</c> opens a hole and <c>"</c> closes the string; in a
        /// hole braces nest, <c>"</c> opens a nested string, and a single-quoted string runs to its
        /// own closing quote.
        /// </summary>
        private bool ScanExtent(string source, int start, out int end, out int innermostOpener, out OpenConstruct innermost)
        {
            _frames.Clear();
            _frames.Add(new Frame { Start = start });
            var i = start + 1;
            while (i < source.Length)
            {
                var c = source[i];
                if (c is '\n' or '\r')
                    break;

                var top = _frames.Count - 1;
                if (!_frames[top].IsHole)
                {
                    switch (c)
                    {
                        case '\\':
                            // The escaped character is consumed with the backslash unless it is
                            // the line break, which ends the line (and the string) as usual.
                            i += i + 1 < source.Length && source[i + 1] is not ('\n' or '\r') ? 2 : 1;
                            continue;
                        case '{':
                            if (i + 1 < source.Length && source[i + 1] == '{')
                            {
                                i += 2;
                                continue;
                            }

                            _frames.Add(new Frame { IsHole = true, Start = i });
                            i++;
                            continue;
                        case '}':
                            i += i + 1 < source.Length && source[i + 1] == '}' ? 2 : 1;
                            continue;
                        case '"':
                            _frames.RemoveAt(top);
                            i++;
                            if (_frames.Count == 0)
                            {
                                end = i;
                                innermostOpener = start;
                                innermost = OpenConstruct.DoubleQuotedText;
                                return true;
                            }

                            continue;
                        default:
                            i++;
                            continue;
                    }
                }

                switch (c)
                {
                    case '{':
                        var opened = _frames[top];
                        opened.Depth++;
                        _frames[top] = opened;
                        i++;
                        continue;
                    case '}':
                        var closing = _frames[top];
                        if (closing.Depth == 0)
                        {
                            _frames.RemoveAt(top);
                        }
                        else
                        {
                            closing.Depth--;
                            _frames[top] = closing;
                        }

                        i++;
                        continue;
                    case '"':
                        _frames.Add(new Frame { Start = i });
                        i++;
                        continue;
                    case '\'':
                        var quote = i;
                        i++;
                        while (i < source.Length && source[i] is not ('\'' or '\n' or '\r'))
                            i++;
                        if (i < source.Length && source[i] == '\'')
                        {
                            i++;
                            continue;
                        }

                        // A single-quoted string inside a hole runs to the end of the line, so the
                        // line ends with that string open: it is the innermost open construct.
                        end = i;
                        innermostOpener = quote;
                        innermost = OpenConstruct.SingleQuotedString;
                        return false;
                    default:
                        i++;
                        continue;
                }
            }

            var innermostFrame = _frames[^1];
            end = i;
            innermostOpener = innermostFrame.Start;
            innermost = innermostFrame.IsHole ? OpenConstruct.Hole
                : _frames.Count > 1 ? OpenConstruct.NestedDoubleQuotedText
                : OpenConstruct.DoubleQuotedText;
            return false;
        }

        /// <summary>
        /// Tokenizes a double-quoted string that <see cref="ScanExtent"/> found closed on its line,
        /// reporting its invalid escapes, lone closing braces and hole comments in source order.
        /// Because the whole string is known to close before the line ends, every index read here
        /// past a backslash or a brace is inside the string.
        /// </summary>
        private void LexTerminated(
            string source,
            ref int i,
            ref int col,
            int line,
            List<Token> tokens,
            DiagnosticBag diagnostics,
            List<SourcePosition>? lexicalErrorStarts)
        {
            _frames.Clear();
            _frames.Add(new Frame { Pending = true, Start = i, StartColumn = col });
            i++; col++; // the opening quote

            while (_frames.Count > 0)
            {
                var top = _frames.Count - 1;
                if (!_frames[top].IsHole)
                {
                    LexTextRun(source, ref i, ref col, line, tokens, diagnostics, lexicalErrorStarts);
                    continue;
                }

                var c = source[i];
                if (char.IsWhiteSpace(c))
                {
                    // Never a line break: the string closes on this line.
                    i++; col++;
                    continue;
                }

                switch (c)
                {
                    case '{':
                        var opened = _frames[top];
                        opened.Depth++;
                        _frames[top] = opened;
                        tokens.Add(Token.Create(TokenKind.LBrace, i, 1, line, col));
                        i++; col++;
                        continue;
                    case '}':
                        var closing = _frames[top];
                        if (closing.Depth == 0)
                        {
                            tokens.Add(Token.Create(TokenKind.InterpolationHoleClose, i, 1, line, col));
                            _frames.RemoveAt(top);
                        }
                        else
                        {
                            closing.Depth--;
                            _frames[top] = closing;
                            tokens.Add(Token.Create(TokenKind.RBrace, i, 1, line, col));
                        }

                        i++; col++;
                        continue;
                    case '"':
                        _frames.Add(new Frame { Pending = true, Start = i, StartColumn = col });
                        i++; col++;
                        continue;
                    case '#':
                        // A comment would hide the rest of the line — the hole's '}' and the
                        // string's closing quote with it — so a hole cannot hold one. The character
                        // is reported once and, like every reported character, is invisible to the
                        // grammar.
                        var hash = Token.Bad(i, 1, line, col);
                        tokens.Add(hash);
                        diagnostics.Report(
                            DiagnosticCode.InvalidInterpolationHole,
                            "A comment cannot start inside an interpolation hole: '#' would hide the rest of the line, including the hole's '}' and the string's closing '\"'.",
                            hash.Span);
                        lexicalErrorStarts?.Add(hash.Span.Start);
                        i++; col++;
                        continue;
                    default:
                        LexCodeToken(source, ref i, ref col, line, tokens, diagnostics, lexicalErrorStarts);
                        continue;
                }
            }
        }

        /// <summary>
        /// Lexes the text run of the string frame on top of the stack, up to its next hole or its
        /// closing quote, decoding escapes and doubled braces. A string that reaches its closing
        /// quote before any hole becomes ONE <see cref="TokenKind.StringLiteral"/> token over the
        /// whole string; otherwise the run is an <see cref="TokenKind.InterpolatedStringText"/>
        /// token when it is non-empty, and the string's Start token is emitted when its first hole
        /// opens.
        /// </summary>
        private void LexTextRun(
            string source,
            ref int i,
            ref int col,
            int line,
            List<Token> tokens,
            DiagnosticBag diagnostics,
            List<SourcePosition>? lexicalErrorStarts)
        {
            var top = _frames.Count - 1;
            var runStart = i;
            var runColumn = col;
            _text.Clear();
            while (true)
            {
                var c = source[i];
                switch (c)
                {
                    case '"':
                        var closed = _frames[top];
                        if (closed.Pending)
                        {
                            tokens.Add(Token.CreateStringLiteral(
                                _text.ToString(), closed.Start, i + 1 - closed.Start, line, closed.StartColumn));
                        }
                        else
                        {
                            if (i > runStart)
                                tokens.Add(Token.CreateInterpolatedStringText(_text.ToString(), runStart, i - runStart, line, runColumn));
                            tokens.Add(Token.Create(TokenKind.InterpolatedStringEnd, i, 1, line, col));
                        }

                        _frames.RemoveAt(top);
                        i++; col++;
                        return;

                    case '\\':
                        var escaped = source[i + 1];
                        switch (escaped)
                        {
                            case '"': _text.Append('"'); break;
                            case '\\': _text.Append('\\'); break;
                            case 'n': _text.Append('\n'); break;
                            case 't': _text.Append('\t'); break;
                            default:
                                ReportInvalidEscape(source, i, col, line, diagnostics, lexicalErrorStarts);
                                // Recovery keeps the written characters; the diagnostic already
                                // makes the source invalid.
                                _text.Append('\\').Append(escaped);
                                break;
                        }

                        i += 2; col += 2;
                        continue;

                    case '{':
                        if (source[i + 1] == '{')
                        {
                            _text.Append('{');
                            i += 2; col += 2;
                            continue;
                        }

                        var opening = _frames[top];
                        if (opening.Pending)
                        {
                            tokens.Add(Token.Create(TokenKind.InterpolatedStringStart, opening.Start, 1, line, opening.StartColumn));
                            opening.Pending = false;
                            _frames[top] = opening;
                        }

                        if (i > runStart)
                            tokens.Add(Token.CreateInterpolatedStringText(_text.ToString(), runStart, i - runStart, line, runColumn));
                        tokens.Add(Token.Create(TokenKind.InterpolationHoleOpen, i, 1, line, col));
                        _frames.Add(new Frame { IsHole = true, Start = i, StartColumn = col });
                        i++; col++;
                        return;

                    case '}':
                        if (source[i + 1] == '}')
                        {
                            _text.Append('}');
                            i += 2; col += 2;
                            continue;
                        }

                        var brace = new SourceSpan(line, col, line, col + 1);
                        diagnostics.Report(
                            DiagnosticCode.UnmatchedBraceInString,
                            "Unmatched '}' in a double-quoted string: write '}}' for a literal '}' (a single '{' opens an interpolation hole, which its own '}' closes).",
                            brace);
                        lexicalErrorStarts?.Add(brace.Start);
                        _text.Append('}');
                        i++; col++;
                        continue;

                    default:
                        _text.Append(c);
                        i++; col++;
                        continue;
                }
            }
        }

        /// <summary>
        /// Reports a backslash at <paramref name="i"/> that begins no supported escape, over the
        /// backslash and the character it escapes (a whole surrogate pair when one follows).
        /// </summary>
        private static void ReportInvalidEscape(
            string source,
            int i,
            int col,
            int line,
            DiagnosticBag diagnostics,
            List<SourcePosition>? lexicalErrorStarts)
        {
            var escaped = source[i + 1];
            var width = char.IsHighSurrogate(escaped) && i + 2 < source.Length && char.IsLowSurrogate(source[i + 2]) ? 3 : 2;
            var span = new SourceSpan(line, col, line, col + width);
            diagnostics.Report(
                DiagnosticCode.InvalidStringEscape,
                span,
                (source, i, width),
                static at => DescribeInvalidEscape(at.source, at.i, at.width));
            lexicalErrorStarts?.Add(span.Start);
        }

        private static string DescribeInvalidEscape(string source, int i, int width)
        {
            const string supported =
                "The escapes of a double-quoted string are \\\" (double quote), \\\\ (backslash), \\n (line feed) and \\t (tab); write {{ and }} for literal braces.";
            var escaped = source[i + 1];
            if (escaped == 'r')
                return "'\\r' is not a supported escape: a double-quoted string cannot contain a carriage return. " + supported;

            var described = width == 3
                ? DescribeUnexpectedPair(source, i + 1)
                : DescribeUnexpectedCharacter(escaped);
            // A visible character reads as the escape itself ('\q'); one without a glyph is named
            // by its code point after the backslash.
            var escape = described.StartsWith('\'')
                ? "'\\" + described[1..]
                : "a backslash followed by " + described;
            return $"Unsupported escape sequence {escape} in a double-quoted string. " + supported;
        }
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
