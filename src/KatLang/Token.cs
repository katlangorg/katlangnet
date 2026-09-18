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
/// (the text between the quotes), and <see cref="TokenKind.Comment"/> (the text after
/// <c>#</c>); keywords, operators, delimiters, <see cref="TokenKind.EndOfFile"/>, and
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

    /// <summary>The value of a <see cref="TokenKind.Number"/> token; <c>default</c> for every other kind.</summary>
    public Decimal128 NumValue { get; internal init; }

    /// <summary>
    /// The text payload of an identifier, string literal, or comment token (see the type
    /// remarks); <see langword="null"/> for every other kind.
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

    internal static Token CreateComment(string text, int position, int length, int line, int column)
        => new(TokenKind.Comment, position, length, line, column, stringValue: text);

    internal static Token Create(TokenKind kind, int position, int length, int line, int column)
        => new(kind, position, length, line, column);

    internal static Token EndOfFile(int position, int line, int column)
        => new(TokenKind.EndOfFile, position, 0, line, column);

    internal static Token Bad(int position, int length, int line, int column)
        => new(TokenKind.Bad, position, length, line, column);
}
