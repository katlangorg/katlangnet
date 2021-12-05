using System;
using System.Collections.Generic;
using System.IO;
using System.Net.Http;

namespace KatLang
{
    public static class Parser
    {
        private static HttpClient? _httpClient;

        public static ParsingResult Parse(string source, Func<string, string>? katLangCodeDownloadFunc = null)
        {
            Expression? result = null;
            var errors = new List<MarkerData>();

            var interruptionPosition = 0;
            var newLines = new List<int>();

            bool completed = false;
            bool isPanicMode = false;
            while (!completed)
            {
                try
                {
                    var tokens = StringScanner.Scan(source, interruptionPosition, newLines);
                    var abstractSyntaxTree = Parse(tokens, isPanicMode);
                    completed = true; //if parsing did not caused error, then all the tokens have been read
                    var binder = new Binder(katLangCodeDownloadFunc);
                    result = binder.Bind(abstractSyntaxTree);
                }
                catch (KatLangException e)
                {
                    isPanicMode = true;
                    var startPosition = GetTokenPosition(newLines, e.Position);
                    var endPosition = GetTokenPosition(newLines, e.Position + e.Length);
                    errors.Add(new MarkerData(e.Message, MarkerSeverity.Error, startPosition.LineNumber, startPosition.Column, endPosition.LineNumber, endPosition.Column));
                    if(e.Position + e.Length <= interruptionPosition)
                    {
                        //if there was some bug, then quit detecting errors, otherwise it could lead to infinite loop
                        completed = true;
                    }
                    interruptionPosition = e.Position + e.Length;
                }
            }
            if(result == default || errors.Count > 0)
            {
                result = new AlgorithmExpression();
            }
            return new ParsingResult(result, errors);
        }

        public static string DownloadCode(string url)
        {
            if (_httpClient == default)
            {
                _httpClient = new HttpClient();
            }
            var response = _httpClient.Send(new HttpRequestMessage(HttpMethod.Get, url));
            using var stream = response.Content.ReadAsStream();
            using var reader = new StreamReader(stream);
            return reader.ReadToEnd();
        }

        private static AlgorithmExpression Parse(IEnumerable<Token> tokenStream, bool isPanicMode)
        {
            var enumerator = tokenStream.GetEnumerator();
            if (enumerator.MoveNext())
            {
                if (isPanicMode)
                {
                    Synchronize(enumerator);
                }
                var algorithm = ReadSecondOrderAlgorithm(enumerator, true);
                var token = enumerator.Current;
                if (token.Kind != TokenKind.EndOfFile)
                {
                    throw new KatLangException($"Expected end of file, but got: {token.Kind}", token);
                }
                return algorithm;
            }
            return new AlgorithmExpression();
        }

        private static TextPosition GetTokenPosition(List<int> newLines, int position)
        {
            for (var i = newLines.Count - 1; i >= 0; i--)
            {
                var newLinePosition = newLines[i];
                if (newLinePosition < position)
                {
                    return new TextPosition(i + 2, position - newLinePosition);
                }
            }
            return new TextPosition(1, position + 1);
        }

        private static AlgorithmExpression ReadSecondOrderAlgorithm(IEnumerator<Token> tokenStream, bool isParametrized)
        {
            var properties = new Dictionary<string, Expression>();

            var result = new AlgorithmExpression
            {
                Position = tokenStream.Current.Position
            };
            while (tokenStream.Current.Kind != TokenKind.EndOfFile && tokenStream.Current.Kind != TokenKind.End && tokenStream.Current.Kind != TokenKind.EndScope)
            {
                while(tokenStream.Current.Kind == TokenKind.InlineComment)
                {
                    tokenStream.MoveNext();
                }

                var identifierToken = tokenStream.Current;
                if (identifierToken.Kind == TokenKind.Identifier)
                {
                    var identifierStartPosition = tokenStream.Current.Position;
                    var parameter = ReadParameter(tokenStream, false);
                    if (tokenStream.Current.Kind == TokenKind.Assign)
                    {
                        if (parameter.GraceWeight != 0)
                        {
                            throw new KatLangException("Grace~ operator cannot be applied to property name.", identifierToken);
                        }

                        tokenStream.MoveNext();
                        var propertyBranch = ReadProperty(tokenStream, parameter.Name, identifierStartPosition);
                        if (properties.TryGetValue(propertyBranch.Name, out var existingProperty))
                        {
                            if (existingProperty is ConditionalAlgorithmExpression conditionalAlgorithm)
                            {
                                conditionalAlgorithm.AddBranch(propertyBranch);
                            }
                            else
                            {
                                throw new KatLangException($"The property '{propertyBranch.Name}' is already defined! Conditional branches can be added only to conditional properties.", propertyBranch);
                            }
                        }
                        else
                        {
                            if (propertyBranch.Condition == default)
                            {
                                properties[propertyBranch.Name] = propertyBranch.Algorithm;
                            }
                            else
                            {
                                var algorithm = new ConditionalAlgorithmExpression();
                                algorithm.AddBranch(propertyBranch);
                                properties[propertyBranch.Name] = algorithm;
                            }
                        }
                    }
                    else
                    {
                        result.Expressions.Add(ReadFirstOrderAlgorithm(tokenStream, ReadExpression(tokenStream, 0, parameter)));
                    }
                }
                else
                {
                    result.Expressions.Add(ReadFirstOrderAlgorithm(tokenStream));
                }
            }

            result.Length = tokenStream.Current.Position - result.Position;

            foreach(var property in properties)
            {
                result.Properties.Add(new PropertyExpression(property.Key, property.Value));
            }

            result.IsParametrized = isParametrized;
            return result;
        }

        private static Condition? ReadConditions(IEnumerator<Token> tokenStream)
        {
            if(tokenStream.Current.Kind == TokenKind.IgnoreValue)
            {
                var startPosition = tokenStream.Current.Position;
                var conditions = new List<double>();
                while (tokenStream.Current.Kind == TokenKind.IgnoreValue)
                {
                    conditions.Add(tokenStream.Current.Number);
                    tokenStream.MoveNext();
                    if(tokenStream.Current.Kind == TokenKind.Comma || tokenStream.Current.Kind == TokenKind.Semicolon)
                    {
                        tokenStream.MoveNext();
                    }
                }
                return new Condition(conditions)
                {
                    Position = startPosition,
                    Length = tokenStream.Current.Position - startPosition
                };
            }
            return default;
        }

        private static PropertyBranchExpression ReadProperty(IEnumerator<Token> tokenStream, string name, int startPosition)
        {
            var condition = ReadConditions(tokenStream);
            var body = ReadFirstOrderAlgorithm(tokenStream);
            return new PropertyBranchExpression(name, body, condition)
            {
                Position = startPosition,
                Length = tokenStream.Current.Position - startPosition
            };
        }

        private static AlgorithmExpression ReadFirstOrderAlgorithm(IEnumerator<Token> tokenStream, Expression? firstSubExpression = default)
        {
            var startPosition = tokenStream.Current.Position;
            var expressions = new List<Expression>();
            if (firstSubExpression != default)
            {
                expressions.Add(firstSubExpression);
            }
            while (tokenStream.Current.Kind != TokenKind.EndOfFile && tokenStream.Current.Kind != TokenKind.End && tokenStream.Current.Kind != TokenKind.EndScope)
            {
                var shouldJoin = tokenStream.Current.Kind == TokenKind.Semicolon;
                if (tokenStream.Current.Kind == TokenKind.Comma || tokenStream.Current.Kind == TokenKind.Semicolon)
                {
                    tokenStream.MoveNext();
                }
                else
                {
                    //if the separator is space instead of comma or semicolon, then the second expression belongs to a new algorithm
                    if (expressions.Count > 0)
                    {
                        break;
                    }
                }
                var next = ReadExpression(tokenStream);
                if (expressions.Count > 0 && shouldJoin)
                {
                    var previous = expressions[expressions.Count - 1];
                    expressions.RemoveAt(expressions.Count - 1);
                    expressions.Add(new PropertyExecutionExpression(new ParameterExpression(Language.Combine), new AlgorithmExpression(new List<Expression> { previous, next })));
                }
                else
                {
                    expressions.Add(next);
                }
            }
            var result = expressions.Count == 1 && expressions[0] is AlgorithmExpression algorithm ? algorithm : new AlgorithmExpression(expressions);
            result.Position = startPosition;
            result.Length = tokenStream.Current.Position - startPosition;
            return result;
        }

        private static Expression ReadExpression(IEnumerator<Token> tokenStream, int minPrecedence = 0, Expression? startingExpression = default)
        {
            var startPosition = startingExpression?.Position ?? tokenStream.Current.Position;
            
            Expression? lhs = startingExpression;

            if (startingExpression == default)
            {
                switch (tokenStream.Current.Kind)
                {
                    case TokenKind.Minus:
                    case TokenKind.Not:
                        //unary
                        var unaryKind = tokenStream.Current.Kind;
                        var unaryOp = Language.UnaryOperators[unaryKind];
                        tokenStream.MoveNext();
                        lhs = new UnaryExpression(unaryKind, ReadExpression(tokenStream, unaryOp.Precedence + 1));
                        break;
                    case TokenKind.Begin:
                        //(algorithm)
                        tokenStream.MoveNext();
                        var algorithm = ReadSecondOrderAlgorithm(tokenStream, false);
                        ReadKeyword(tokenStream, TokenKind.End);
                        lhs = algorithm.Expressions.Count == 1 && algorithm.Properties.Count == 0 ? algorithm.Expressions[0] : algorithm;
                        break;
                    case TokenKind.BeginScope:
                        //{algorithm}
                        tokenStream.MoveNext();
                        var parametrizedAlgorithm = ReadSecondOrderAlgorithm(tokenStream, true);
                        ReadKeyword(tokenStream, TokenKind.EndScope);
                        if (parametrizedAlgorithm.Expressions.Count == 1 && parametrizedAlgorithm.Properties.Count == 0 && parametrizedAlgorithm.Expressions[0] is AlgorithmExpression algo)
                        {
                            algo.IsParametrized = true;
                            return algo;
                        }
                        lhs = parametrizedAlgorithm;
                        break;
                }
            }
            if(lhs == default)
            {
                lhs = ReadAtom(tokenStream);
            }
            
            while (tokenStream.Current.Kind != TokenKind.EndOfFile
                && Language.Operators.ContainsKey(tokenStream.Current.Kind) && Language.Operators[tokenStream.Current.Kind].Precedence >= minPrecedence)
            {
                var operatorToken = tokenStream.Current;
                var descriptor = Language.Operators[operatorToken.Kind];
                var next_min_prec = descriptor.IsRightAssociative ? descriptor.Precedence : descriptor.Precedence + 1;

                if (descriptor.IsExecutionOperator)
                {
                    if (lhs is ParameterExpression identity)
                    {
                        if (identity.IsIgnored)
                        {
                            throw new KatLangException("Operator '#' cannot be applied to property calls!", operatorToken);
                        }
                        var rhs = ReadExpression(tokenStream, next_min_prec);
                        if(rhs is PropertyExecutionExpression complexPropertyExecution && complexPropertyExecution.Parent != default)
                        {
                            var input = complexPropertyExecution.Parent as AlgorithmExpression;
                            complexPropertyExecution.Parent = new PropertyExecutionExpression(identity, input);
                            lhs = rhs;
                        }
                        else
                        {
                            if(rhs is PropertyAccessExpression propertyAccess)
                            {
                                var body = new PropertyExecutionExpression(identity, propertyAccess.Algorithm.ToAlgorithm());
                                lhs = new PropertyExecutionExpression(propertyAccess.Property, new AlgorithmExpression(new List<Expression> { body }));
                            }
                            else
                            {
                                lhs = new PropertyExecutionExpression(identity, rhs.ToAlgorithm());
                            }
                        }
                        continue;
                    }
                    return lhs; //if brackets are used after some other construction than identifier, then it is considered as beginning of new expression.
                }
                else
                {
                    tokenStream.MoveNext();
                    switch (operatorToken.Kind)
                    {
                        case TokenKind.Colon:
                            if (!(lhs is ParameterExpression || lhs is AlgorithmExpression || lhs is PropertyExecutionExpression || lhs is PropertyAccessExpression))
                            {
                                throw new KatLangException("Selector content can be algorithm or parameter.", operatorToken);
                            }
                            if (tokenStream.Current.Kind == TokenKind.EndOfFile)
                            {
                                throw new KatLangException("Selector not provided.", operatorToken);
                            }
                            var selector = ReadExpression(tokenStream, next_min_prec);
                            if (!(selector is ParameterExpression || selector is ConstantExpression))
                            {
                                throw new KatLangException("Selector can be only constant or parameter.", operatorToken);
                            }
                            lhs = new ContentSelectionExpression(lhs, selector);
                            break;
                        case TokenKind.Dot:
                            if (tokenStream.Current.Kind == TokenKind.Identifier || tokenStream.Current.Kind == TokenKind.Property || tokenStream.Current.Kind == TokenKind.Grace)
                            {
                                var property = ReadParameter(tokenStream, false);
                                if(Language.Operators.TryGetValue(tokenStream.Current.Kind, out var operatorDescriptor) && operatorDescriptor.IsExecutionOperator)
                                {
                                    var propertyInput = ReadExpression(tokenStream, next_min_prec);
                                    var input = propertyInput as AlgorithmExpression;
                                    if (input == default)
                                    {
                                        input = new AlgorithmExpression(new List<Expression> { propertyInput });
                                    }
                                    lhs = new PropertyExecutionExpression(property, input, lhs);
                                }
                                else
                                {
                                    lhs = new PropertyAccessExpression(lhs, property);
                                }
                            }
                            else
                            {
                                throw new KatLangException($"After operator . should follow property name, but got {tokenStream.Current.Kind}", operatorToken);
                            }
                            break;
                        default:
                            var rhs = ReadExpression(tokenStream, next_min_prec);
                            lhs = new BinaryExpression(operatorToken.Kind, lhs, rhs);
                            break;
                    }
                }
            }

            lhs.Position = startPosition;
            lhs.Length = tokenStream.Current.Position - startPosition;

            return lhs;
        }

        private static Expression ReadAtom(IEnumerator<Token> tokenStream)
        {
            switch (tokenStream.Current.Kind)
            {
                case TokenKind.Number:
                    var numberValue = tokenStream.Current.Number;
                    tokenStream.MoveNext();
                    return new ConstantExpression(numberValue);

                case TokenKind.Grace:
                case TokenKind.Identifier:
                case TokenKind.Property:
                    return ReadParameter(tokenStream, false);

                case TokenKind.IgnoreParameter:
                    return ReadParameter(tokenStream, true);

                case TokenKind.Ignore:
                    tokenStream.MoveNext();
                    return new IgnoreArgumentExpression();

                case TokenKind.IgnoreValue:
                    throw new KatLangException("Tokens of type 'IgnoreValue' can be used only as the first expressions in the property declaration.", tokenStream.Current);

                case TokenKind.String:
                    var stringValue = tokenStream.Current.String;
                    tokenStream.MoveNext();
                    return new StringExpression(stringValue);

                case TokenKind.InlineComment:
                    tokenStream.MoveNext();
                    return ReadAtom(tokenStream);

                case TokenKind.Constant:
                    var constantToken = tokenStream.Current;
                    tokenStream.MoveNext();
                    return constantToken.String switch
                    {
                        Language.Pi => new ConstantExpression(Math.PI),
                        Language.Exp => new ConstantExpression(Math.E),
                        _ => throw new KatLangException($"Unexpected constant: '{tokenStream.Current.Kind}'.", tokenStream.Current),
                    };
                default:
                    throw new KatLangException($"Unexpected token: '{tokenStream.Current.Kind}'.", tokenStream.Current);
            }
        }


        private static void ReadKeyword(IEnumerator<Token> tokenStream, TokenKind keyword)
        {
            if (tokenStream.Current.Kind == keyword)
            {
                tokenStream.MoveNext();
            }
            else
            {
                throw new KatLangException($"Expected: '{keyword}', but got: {tokenStream.Current.Kind}", tokenStream.Current);
            }
        }

        private static ParameterExpression ReadParameter(IEnumerator<Token> tokenStream, bool ignoreIdentifier)
        {
            var startPosition = tokenStream.Current.Position;

            if(tokenStream.Current.Kind == TokenKind.Property)
            {
                var parameterName = tokenStream.Current.String;
                tokenStream.MoveNext();
                var result = new ParameterExpression(parameterName)
                {
                    Position = startPosition,
                    Length = tokenStream.Current.Position - startPosition
                };
                return result;
            }

            var graceWeight = 0;
            while(tokenStream.Current.Kind == TokenKind.Grace)
            {
                tokenStream.MoveNext();
                graceWeight--;
            }

            var expectedToken = ignoreIdentifier ? TokenKind.IgnoreParameter : TokenKind.Identifier;
            if (tokenStream.Current.Kind == expectedToken)
            {
                var parameterName = tokenStream.Current.String;
                tokenStream.MoveNext();

                while (tokenStream.Current.Kind == TokenKind.Grace)
                {
                    tokenStream.MoveNext();
                    graceWeight++;
                }

                var result = new ParameterExpression(parameterName, graceWeight, ignoreIdentifier)
                {
                    Position = startPosition,
                    Length = tokenStream.Current.Position - startPosition
                };
                return result;
            }
            throw new KatLangException($"Expected {expectedToken}, but got: {tokenStream.Current.Kind}", tokenStream.Current);
        }

        private static void Synchronize(IEnumerator<Token> tokenStream)
        {
            while (tokenStream.Current.Kind == TokenKind.Comma || tokenStream.Current.Kind == TokenKind.Semicolon
                || tokenStream.Current.Kind == TokenKind.End || tokenStream.Current.Kind == TokenKind.EndScope
                || tokenStream.Current.Kind == TokenKind.Assign || tokenStream.Current.Kind == TokenKind.Colon || tokenStream.Current.Kind == TokenKind.Dot
                || tokenStream.Current.Kind == TokenKind.And || tokenStream.Current.Kind == TokenKind.Or || tokenStream.Current.Kind == TokenKind.Xor 
                || tokenStream.Current.Kind == TokenKind.Less || tokenStream.Current.Kind == TokenKind.LessEqual
                || tokenStream.Current.Kind == TokenKind.Greater || tokenStream.Current.Kind == TokenKind.GreaterEqual
                || tokenStream.Current.Kind == TokenKind.Equal || tokenStream.Current.Kind == TokenKind.Inequal
                || tokenStream.Current.Kind == TokenKind.Plus || tokenStream.Current.Kind == TokenKind.Minus
                || tokenStream.Current.Kind == TokenKind.Multiply || tokenStream.Current.Kind == TokenKind.Divide || tokenStream.Current.Kind == TokenKind.Pow
                || tokenStream.Current.Kind == TokenKind.Mod || tokenStream.Current.Kind == TokenKind.Div)
            {
                tokenStream.MoveNext();
            }
        }
    }
}