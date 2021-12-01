using System;

namespace KatLang
{
    public class KatLangException: Exception
    {
        public int Position { get; }
        public int Length { get; }

        public KatLangException(string message) : this(message, 0, 0) { }

        public KatLangException(string message, Token token): this(message, token.Position, token.Length) { }

        public KatLangException(string message, Expression expr) : this(message, expr.Position, expr.Length) { }

        public KatLangException(string message, int position, int length) : base(message)
        {
            Position = position;
            Length = length;
        }
    }

    public class KatLangRuntimeException: KatLangException
    {
        public KatLangRuntimeException(string message) : base(message) { }

        public KatLangRuntimeException(string message, Token token) : base(message, token.Position, token.Length) { }

        public KatLangRuntimeException(string message, Expression expr) : base(message, expr.Position, expr.Length) { }

        public KatLangRuntimeException(string message, int position, int length) : base(message, position, length) { }
    }
}
