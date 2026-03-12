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

/// <summary>A single token produced by the lexer.</summary>
public sealed record Token(
    TokenKind Kind,
    int Position,
    int Length,
    int Line,
    int Column,
    decimal NumValue = 0,
    string? StringValue = null)
{
    public static Token CreateNumber(decimal value, int position, int length, int line, int column)
        => new(TokenKind.Number, position, length, line, column, NumValue: value);

    public static Token CreateIdentifier(string name, int position, int length, int line, int column)
        => new(TokenKind.Identifier, position, length, line, column, StringValue: name);

    public static Token CreateStringLiteral(string value, int position, int length, int line, int column)
        => new(TokenKind.StringLiteral, position, length, line, column, StringValue: value);

    public static Token CreateComment(string text, int position, int length, int line, int column)
        => new(TokenKind.Comment, position, length, line, column, StringValue: text);

    public static Token Create(TokenKind kind, int position, int length, int line, int column)
        => new(kind, position, length, line, column);

    public static Token EndOfFile(int position, int line, int column)
        => new(TokenKind.EndOfFile, position, 0, line, column);

    public static Token Bad(int position, int length, int line, int column)
        => new(TokenKind.Bad, position, length, line, column);
}
