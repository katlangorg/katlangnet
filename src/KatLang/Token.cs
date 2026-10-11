using System.Numerics;

namespace KatLang;

public enum TokenKind
{
    // Literals
    Number,
    Identifier,
    StringLiteral,

    // Arithmetic operators
    Plus,
    Minus,
    Star,
    Slash,
    Caret,

    // Comparison operators
    LessThan,
    GreaterThan,
    LessEqual,
    GreaterEqual,
    EqualEqual,
    BangEqual,

    // Keywords
    KeywordDiv,
    KeywordMod,
    KeywordAnd,
    KeywordOr,
    KeywordXor,
    KeywordNot,
    KeywordPublic,
    KeywordOpen,
    // The reserved Boolean literals. They are keywords, not identifiers, so
    // `true` and `false` can never name a property, parameter, or open target
    // and never become implicit parameters; the token kind carries the value.
    KeywordTrue,
    KeywordFalse,

    // Delimiters
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Semicolon,

    // Special
    Equals,
    Colon,
    Dot,
    Tilde,

    // Ignored / meta
    Comment,
    EndOfFile,

    // Error recovery
    Bad,

    // Double-quoted strings with interpolation holes (STR-02). A double-quoted string with
    // no hole is ONE StringLiteral token; a string with at least one hole is the sequence
    //   InterpolatedStringStart  { InterpolatedStringText | InterpolationHoleOpen
    //   <the hole's ordinary tokens> InterpolationHoleClose }  InterpolatedStringEnd
    // on one physical line, with every Start matched by its End and every HoleOpen by its
    // HoleClose (an unterminated interpolated string is instead one unterminated
    // StringLiteral token). Appended after Bad: the numeric values are stable public API.

    /// <summary>The opening <c>"</c> of a double-quoted string that contains an interpolation hole.</summary>
    InterpolatedStringStart,

    /// <summary>
    /// A non-empty run of text in an interpolated string; <see cref="Token.StringValue"/> is the
    /// DECODED text (escapes and doubled braces replaced), the token's extent the raw source run.
    /// </summary>
    InterpolatedStringText,

    /// <summary>The <c>{</c> that opens an interpolation hole.</summary>
    InterpolationHoleOpen,

    /// <summary>The <c>}</c> that closes an interpolation hole.</summary>
    InterpolationHoleClose,

    /// <summary>The closing <c>"</c> of an interpolated string.</summary>
    InterpolatedStringEnd,
}

/// <summary>
/// A single token of KatLang source text. KatLang creates tokens; consumers inspect
/// them: <see cref="Lexer.Tokenize(string)"/> is the supported way to obtain one, every
/// property is publicly readable, and construction and mutation are implementation-
/// internal. The public API exposes lexer-produced states; internal parser recovery
/// and friend tests may construct other states. Tokens are values: two tokens with the same kind,
/// coordinates, and payload are equal and hash alike, whichever tokenization produced
/// them.
/// </summary>
/// <remarks>
/// The payload follows the kind. <see cref="NumValue"/> is meaningful only for
/// <see cref="TokenKind.Number"/> (an invalid or too-large literal is reported as a
/// diagnostic and carries <c>0</c>). <see cref="StringValue"/> is non-null exactly for
/// <see cref="TokenKind.Identifier"/> (the name), <see cref="TokenKind.StringLiteral"/>
/// (the string's text: for a single-quoted literal exactly the source text between the
/// quotes, which has no escapes; for a double-quoted literal its DECODED text — <c>\"</c>,
/// <c>\\</c>, <c>\n</c>, <c>\t</c>, <c>{{</c> and <c>}}</c> replaced by the characters they
/// denote; for an unterminated double-quoted literal the raw source text after the opening
/// quote), <see cref="TokenKind.InterpolatedStringText"/> (the decoded text of the run), and
/// <see cref="TokenKind.Comment"/> (the text after <c>#</c>); keywords, operators, delimiters,
/// the other interpolated-string tokens, <see cref="TokenKind.EndOfFile"/>, and
/// <see cref="TokenKind.Bad"/> carry no payload — their spelling is the source slice at
/// <see cref="Position"/>/<see cref="Length"/>. The end-of-file token is always the last
/// token, sits at the source length, and has length 0. An empty <c>with { }</c> copy
/// is public and preserves every field; assigning fields in that copy is internal.
/// Public construction or deserialization is not a supported contract. Accessibility
/// is an API boundary, not protection against privileged reflection or unsafe code.
/// </remarks>
public sealed record Token
{
    internal Token(TokenKind kind, int position, int length, int line, int column, Decimal128 numValue = default, string? stringValue = null)
    {
        Kind = kind;
        Position = position;
        Length = length;
        Line = line;
        Column = column;
        NumValue = numValue;
        StringValue = stringValue;
    }

    /// <summary>The lexical class of the token.</summary>
    public TokenKind Kind { get; internal init; }

    /// <summary>The 0-based offset, in UTF-16 code units, of the token's first code unit in the source.</summary>
    public int Position { get; internal init; }

    /// <summary>
    /// The number of UTF-16 code units the token occupies, so the token's text is the source
    /// slice <c>[Position, Position + Length)</c>. In lexer output it is 0 only for
    /// the end-of-file token; the parser also uses an internal zero-length
    /// <see cref="TokenKind.Bad"/> marker for a missing expected token.
    /// </summary>
    public int Length { get; internal init; }

    /// <summary>The 1-based line on which the token starts (a line feed ends a line).</summary>
    public int Line { get; internal init; }

    /// <summary>
    /// The 1-based column at which the token starts on its line, advancing one per UTF-16
    /// code unit (a lone carriage return is whitespace that advances neither the line nor
    /// the column).
    /// </summary>
    public int Column { get; internal init; }

    /// <summary>
    /// The token's source extent in human coordinates: the half-open span from
    /// <see cref="Line"/>:<see cref="Column"/> up to but not including the column
    /// <see cref="Length"/> code units later. It is derived on every read from the token's
    /// stored offset model, never stored: no token spans a line break (a string literal and a
    /// comment end at the line's end), and columns count UTF-16 code units exactly as
    /// <see cref="Length"/> does, so the end column is <c>Column + Length</c> on the same line
    /// — a surrogate pair inside an unexpected-character token widens the span by two, a
    /// keyword by its spelling. The end-of-file token and the parser's zero-length recovery
    /// marker are EMPTY spans at their position: a location, not a fabricated one-column width.
    /// </summary>
    public SourceSpan Span => new(Line, Column, Line, Column + Length);

    /// <summary>The value of a <see cref="TokenKind.Number"/> token; <c>default</c> for every other kind.</summary>
    public Decimal128 NumValue { get; internal init; }

    /// <summary>
    /// The text payload of an identifier, string literal, interpolated-string text run
    /// (<see cref="TokenKind.InterpolatedStringText"/>, its decoded text), or comment token (see the
    /// type remarks); <see langword="null"/> for every other kind.
    /// </summary>
    public string? StringValue { get; internal init; }

    // ── Construction (lexer and parser only) ──────────────────────────────────
    // One factory per payload shape: the number and text factories fix their kind and
    // carry its payload, `Create` mints the payload-free kinds, and `EndOfFile`/`Bad`
    // their special states. The parser's `Expect` recovery mints a zero-length Bad
    // token through the same factory as the lexer's unexpected-character tokens.

    internal static Token CreateNumber(Decimal128 value, int position, int length, int line, int column)
        => new(TokenKind.Number, position, length, line, column, numValue: value);

    internal static Token CreateIdentifier(string name, int position, int length, int line, int column)
        => new(TokenKind.Identifier, position, length, line, column, stringValue: name);

    internal static Token CreateStringLiteral(string value, int position, int length, int line, int column)
        => new(TokenKind.StringLiteral, position, length, line, column, stringValue: value);

    internal static Token CreateInterpolatedStringText(string decoded, int position, int length, int line, int column)
        => new(TokenKind.InterpolatedStringText, position, length, line, column, stringValue: decoded);

    internal static Token CreateComment(string text, int position, int length, int line, int column)
        => new(TokenKind.Comment, position, length, line, column, stringValue: text);

    internal static Token Create(TokenKind kind, int position, int length, int line, int column)
        => new(kind, position, length, line, column);

    internal static Token EndOfFile(int position, int line, int column)
        => new(TokenKind.EndOfFile, position, 0, line, column);

    internal static Token Bad(int position, int length, int line, int column)
        => new(TokenKind.Bad, position, length, line, column);
}
