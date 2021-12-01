using System.Collections.Generic;

namespace KatLang
{
    public static class Language
    {
        public class OperatorDescriptor
        {
            public OperatorDescriptor(int precedence, bool isRightAssociative = false, bool isExecutionOperator = false, bool isSymetric = false)
            {
                Precedence = precedence;
                IsRightAssociative = isRightAssociative;
                IsExecutionOperator = isExecutionOperator;
                IsSymetric = isSymetric;
            }

            public int Precedence { get; private set; }
            public bool IsRightAssociative { get; private set; }
            public bool IsExecutionOperator { get; private set; }
            public bool IsSymetric { get; private set; }
        }

        public sealed class BuiltinAlgorithm
        {
            public string Name;
            public int Arity;

            public BuiltinAlgorithm(string name, int arity)
            {
                Name = name;
                Arity = arity;
            }
        }

        public static readonly Dictionary<TokenKind, OperatorDescriptor> Operators
            = new Dictionary<TokenKind, OperatorDescriptor> {
                { TokenKind.Dot, new OperatorDescriptor(10) },
                { TokenKind.Begin, new OperatorDescriptor(10, isExecutionOperator:true) },
                { TokenKind.BeginScope, new OperatorDescriptor(10, isExecutionOperator:true) },
                { TokenKind.Colon, new OperatorDescriptor(10) },
                { TokenKind.Pow, new OperatorDescriptor(8, isRightAssociative:true) },
                { TokenKind.Mod, new OperatorDescriptor(7) },
                { TokenKind.Div, new OperatorDescriptor(7) },
                { TokenKind.Divide, new OperatorDescriptor(7) },
                { TokenKind.Multiply, new OperatorDescriptor(7, isSymetric:true) },
                { TokenKind.Plus, new OperatorDescriptor(6, isSymetric:true) },
                { TokenKind.Minus, new OperatorDescriptor(6) },
                { TokenKind.GreaterEqual, new OperatorDescriptor(5) },
                { TokenKind.Greater, new OperatorDescriptor(5) },
                { TokenKind.LessEqual, new OperatorDescriptor(5) },
                { TokenKind.Inequal, new OperatorDescriptor(5) },
                { TokenKind.Equal, new OperatorDescriptor(5) },
                { TokenKind.Less, new OperatorDescriptor(5) },
                { TokenKind.Xor, new OperatorDescriptor(4) },
                { TokenKind.And, new OperatorDescriptor(3) },
                { TokenKind.Or, new OperatorDescriptor(2, isSymetric:true) }
        };

        public static readonly Dictionary<TokenKind, OperatorDescriptor> UnaryOperators
            = new Dictionary<TokenKind, OperatorDescriptor> {
                { TokenKind.Minus, new OperatorDescriptor(9) },
                { TokenKind.Not, new OperatorDescriptor(9) },
        };

        public static readonly Dictionary<string, BuiltinAlgorithm> BuiltinAlgorithms = new Dictionary<string, BuiltinAlgorithm>
            {
                {"abs", new BuiltinAlgorithm("abs", 1)},
                {"ceil", new BuiltinAlgorithm("ceil", 1)},
                {"floor", new BuiltinAlgorithm("floor", 1)},
                {"round", new BuiltinAlgorithm("round", 2)},
                {"sign", new BuiltinAlgorithm("sign", 1)},
                {"div", new BuiltinAlgorithm("div", 2)},
                {"mod", new BuiltinAlgorithm("mod", 2)},
                {"pow", new BuiltinAlgorithm("pow", 2)},
                {"sqrt", new BuiltinAlgorithm("sqrt", 1)},
                {"ln", new BuiltinAlgorithm("ln", 1)},
                {"lg", new BuiltinAlgorithm("lg", 1)},
                {"log", new BuiltinAlgorithm("log", 2)},
                {"sin", new BuiltinAlgorithm("sin", 1)},
                {"asin", new BuiltinAlgorithm("asin", 1)},
                {"cos", new BuiltinAlgorithm("cos", 1)},
                {"acos", new BuiltinAlgorithm("acos", 1)},
                {"tan", new BuiltinAlgorithm("tan", 1)},
                {"atan", new BuiltinAlgorithm("atan", 1)}
            };

        public static readonly Dictionary<string, TokenKind> KeywordTokens = new Dictionary<string, TokenKind>
            {
                {"or", TokenKind.Or},
                {"xor", TokenKind.Xor},
                {"and", TokenKind.And},
                {"not", TokenKind.Not},
                {"mod", TokenKind.Mod},
                {"div", TokenKind.Div},
                {If, TokenKind.Property},
                {Repeat, TokenKind.Property},
                {Loop, TokenKind.Property},
                {Open, TokenKind.Property},
                {Load, TokenKind.Property},
                {Join, TokenKind.Property},
                {Combine, TokenKind.Property},
                {Length, TokenKind.Property},
                {String, TokenKind.Property},
                {Reverse, TokenKind.Property},
                {Pi, TokenKind.Constant},
                {Exp, TokenKind.Constant}
            };

        //builtin operators
        public const string Repeat = "repeat";
        public const string Loop = "loop";
        public const string If = "if";
        public const string Open = "open";
        public const string Load = "load";
        public const string Join = "join";
        public const string Combine = "combine";
        public const string String = "String";
        public const string Reverse = "Reverse";

        //builtin constants
        public const string Pi = "pi";
        public const string Exp = "exp";

        //algorithm properties
        public const string Length = "length";
    }
}
