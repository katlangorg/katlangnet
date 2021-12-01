namespace KatLang
{
    public enum TokenKind
    {
        InlineComment,              // //
        Number,                     // 123.456
        Boolean,                    // T F
        String,

        Ignore,                     // #
        Identifier,                 // identifier
        IgnoreParameter,            // #identifier
        IgnoreValue,                // #value
        Comma,                      // ,
        Semicolon,                  // ;
        Grace,                      // ~
        Assign,                     // =
        Begin,                      // (
        End,                        // )
        BeginScope,                 // {
        EndScope,                   // }
        Colon,                      // :
        Dot,                        // .

        Or,                         // or
        Xor,                        // xor
        And,                        // and
        Not,                        // not
        
        Less,                       // <
        LessEqual,                  // <=
        Greater,                    // >
        GreaterEqual,               // >=
        Equal,                      // ==
        Inequal,                    // !=

        Plus,                       // +
        Minus,                      // -
        Multiply,                   // *
        Divide,                     // /
        Pow,                        // ^
        Mod,                        // mod
        Div,                        // div
        
        Property,                   // length, if, loop, load, join, combine
        Constant,                   // pi, exp

        EndOfFile
    }

    public class Token
    {
        public readonly TokenKind Kind;
        public readonly bool IsIgnored;
        public readonly bool Boolean;
        public readonly double Number;
        public readonly string String;
        public readonly int Position;
        public readonly int Length;

        private Token(TokenKind kind, int position, int length, string? tokenName)
        {
            Kind = kind;
            IsIgnored = false;
            Boolean = false;
            Number = 0;
            String = tokenName ?? kind.ToString().ToLower();
            Position = position;
            Length = length;
        }

        private Token(string identifierName, int position, int length)
        {
            Kind = TokenKind.Identifier;
            IsIgnored = false;
            Boolean = false;
            Number = 0;
            String = identifierName;
            Position = position;
            Length = length;
        }

        private Token(double semanticValue, int position, int length)
        {
            Kind = TokenKind.Number;
            IsIgnored = false;
            Boolean = false;
            Number = semanticValue;
            String = string.Empty;
            Position = position;
            Length = length;
        }

        private Token(bool semanticValue, int position, int length)
        {
            Kind = TokenKind.Boolean;
            IsIgnored = false;
            Boolean = semanticValue;
            Number = 0;
            String = string.Empty;
            Position = position;
            Length = length;
        }

        private Token(TokenKind kind, string semanticValue, int position, int length, bool isIgnored = false)
        {
            Kind = kind;
            IsIgnored = isIgnored;
            Boolean = false;
            Number = 0;
            String = semanticValue;
            Position = position;
            Length = length;
        }

        private Token(TokenKind kind, double semanticValue, int position, int length, bool isIgnored = false)
        {
            Kind = kind;
            IsIgnored = isIgnored;
            Boolean = false;
            Number = semanticValue;
            String = string.Empty;
            Position = position;
            Length = length;
        }

        public static Token CreateToken(TokenKind keywordType, int position, int length, string? tokenName = default)
        {
            return new Token(keywordType, position, length, tokenName);
        }
        public static Token CreateIdentifier(string identifierName, int position, int length)
        {
            return new Token(identifierName, position, length);
        }
        public static Token CreateNumber(double semanticValue, int position, int length)
        {
            return new Token(semanticValue, position, length);
        }
        public static Token CreateString(string semanticValue,  int position, int length)
        {
            return new Token(TokenKind.String, semanticValue, position, length);
        }
        public static Token CreateBoolean(bool semanticValue, int position, int length)
        {
            return new Token(semanticValue, position, length);
        }
        public static Token CreateComment(string comment, int position, int length)
        {
            return new Token(TokenKind.InlineComment, comment, position, length);
        }
        public static Token CreateIgnoreParameter(string semanticValue, int position, int length)
        {
            return new Token(TokenKind.IgnoreParameter, semanticValue, position, length, true);
        }
        public static Token CreateIgnoreValue(double semanticValue, int position, int length)
        {
            return new Token(TokenKind.IgnoreValue,  semanticValue, position, length, true);
        }
        public static Token CreateIgnore(int position, int length)
        {
            return new Token(TokenKind.Ignore, position, length, "#");
        }
    }
}
