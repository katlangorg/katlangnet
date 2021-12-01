using System.Collections.Generic;
using System.Text;

namespace KatLang
{
    public static class StringScanner
    {
        private static Token ScanIdentifier(string source, int index)
        {
            var startPosition = index;
            var sb = new StringBuilder();
            do
            {
                sb.Append(source[index]);
                index++;
            } while (index < source.Length && (char.IsLetterOrDigit(source[index]) || source[index] == '_'));

            var identifier = sb.ToString();
            return Language.KeywordTokens.TryGetValue(identifier, out TokenKind tokenKind)
                ? Token.CreateToken(tokenKind, startPosition, index - startPosition, identifier)
                : Token.CreateIdentifier(identifier, startPosition, index - startPosition);
        }

        private static Token ScanNumber(string source, int index)
        {
            var startPosition = index;
            double n = source[index] - '0';
            index++;
            while (index < source.Length && char.IsDigit(source[index]))
            {
                n = 10D * n + source[index] - '0';
                index++;
            }

            if (index + 1 < source.Length && source[index] == '.' && char.IsDigit(source[index + 1]))
            {
                index++;
                var order = 1D;
                while (index < source.Length && char.IsDigit(source[index]))
                {
                    order *= 10D;
                    n += (source[index] - '0') / order;
                    index++;
                }
            }
            
            return Token.CreateNumber(n, startPosition, index - startPosition);
        }

        private static Token ScanString(string source, int index)
        {
            var startPosition = index;
            index++;
            var sb = new StringBuilder();
            do
            {
                sb.Append(source[index]);
                index++;
            } while (index < source.Length && (source[index] != '\''));

            if(index < source.Length)
            {
                index++;
            }
            
            return Token.CreateString(sb.ToString(), startPosition, index - startPosition);
        }

        private static Token ScanAssignOrEqual(string source, int index)
        {
            var startPosition = index;
            index++;
            TokenKind tokenType;
            if (index < source.Length && source[index] == '=')
            {
                index++;
                tokenType = TokenKind.Equal;
            }
            else
            {
                tokenType = TokenKind.Assign;
            }
            
            return Token.CreateToken(tokenType, startPosition, index - startPosition);
        }

        private static Token ScanLessOrLessEqual(string source, int index)
        {
            var startPosition = index;
            index++;
            TokenKind tokenType;
            if (index < source.Length && source[index] == '=')
            {
                index++;
                tokenType = TokenKind.LessEqual;
            }
            else
            {
                tokenType = TokenKind.Less;
            }
            
            return Token.CreateToken(tokenType, startPosition, index - startPosition);
        }

        private static Token ScanGreaterOrGreaterEqual(string source, int index)
        {
            var startPosition = index;
            index++;
            TokenKind tokenType;
            if (index < source.Length && source[index] == '=')
            {
                index++;
                tokenType = TokenKind.GreaterEqual;
            }
            else
            {
                tokenType = TokenKind.Greater;
            }
            
            return Token.CreateToken(tokenType, startPosition, index - startPosition);
        }

        private static Token ScanInlineComment(string source, int startPosition, int index)
        {
            var sb = new StringBuilder();
            while (index < source.Length && source[index] != '\r' && source[index] !='\n')
            {
                sb.Append(source[index++]);
            }
            
            return Token.CreateComment(sb.ToString(), startPosition, index - startPosition);
        }

        public static IEnumerable<Token> Scan(string source, int startPosition, List<int> newLines)
        {
            if(source == null)
            {
                yield break;
            }

            var index = startPosition;

            while (index < source.Length)
            {
                var tokenStartIndex = index;
                if (char.IsWhiteSpace(source[index]))
                {
                    if(source[index] == '\n')
                    {
                        newLines.Add(index);
                    }
                    index++;
                    continue;
                }
                if (char.IsLetter(source[index]))
                {
                    var identifierToken = ScanIdentifier(source, index);
                    index += identifierToken.Length;
                    yield return identifierToken;
                    continue;
                }
                if (source[index] == '\'')
                {
                    var stringToken = ScanString(source, index);
                    index += stringToken.Length;
                    yield return stringToken;
                    continue;
                }
                if (source[index] == '#')
                {
                    index++;

                    if (index < source.Length && char.IsLetter(source[index]) || source[index] == '_')
                    {
                        var nameToken = ScanIdentifier(source, index);
                        index += nameToken.Length;
                        yield return Token.CreateIgnoreParameter(nameToken.String, tokenStartIndex, index - tokenStartIndex);
                        continue;
                    }
                    if (index < source.Length && char.IsDigit(source[index]))
                    {
                        var numberToken = ScanNumber(source, index);
                        index += numberToken.Length;
                        yield return Token.CreateIgnoreValue(numberToken.Number, tokenStartIndex, index - tokenStartIndex);
                        continue;
                    }

                    var ignoreToken = Token.CreateIgnore(tokenStartIndex, index - tokenStartIndex);
                    yield return ignoreToken;
                    continue;
                }
                if (char.IsDigit(source[index]))
                {
                    var numberToken = ScanNumber(source, index);
                    index += numberToken.Length;
                    yield return numberToken;
                    continue;
                }
                if (source[index] == '=')
                {
                    var token = ScanAssignOrEqual(source, index);
                    index += token.Length;
                    yield return token;
                    continue;
                }
                if (source[index] == '<')
                {
                    var token = ScanLessOrLessEqual(source, index);
                    index += token.Length;
                    yield return token;
                    continue;
                }
                if (source[index] == '>')
                {
                    var token = ScanGreaterOrGreaterEqual(source, index);
                    index += token.Length;
                    yield return token;
                    continue;
                }
                if (source[index] == '/')
                {
                    index++;

                    if (index < source.Length && source[index] == '/')
                    {
                        index++;
                        var token = ScanInlineComment(source, tokenStartIndex, index);
                        index += token.Length - 2; //because previously was added // using index++ 2 times
                        yield return token;
                    }
                    else
                    {
                        yield return Token.CreateToken(TokenKind.Divide, tokenStartIndex, index - tokenStartIndex);
                    }
                    continue;
                }
                if (source[index] == '*')
                {
                    index++;
                    var token = Token.CreateToken(TokenKind.Multiply, tokenStartIndex, index - tokenStartIndex);
                    yield return token;
                    continue;
                }
                if (source[index] == '+')
                {
                    index++;
                    var token = Token.CreateToken(TokenKind.Plus, tokenStartIndex, index - tokenStartIndex);
                    yield return token;
                    continue;
                }
                if (source[index] == '-')
                {
                    index++;
                    var token = Token.CreateToken(TokenKind.Minus, tokenStartIndex, index - tokenStartIndex);
                    yield return token;
                    continue;
                }
                if (source[index] == '^')
                {
                    index++;
                    var token = Token.CreateToken(TokenKind.Pow, tokenStartIndex, index - tokenStartIndex);
                    yield return token;
                    continue;
                }
                if (source[index] == '~')
                {
                    index++;
                    var token = Token.CreateToken(TokenKind.Grace, tokenStartIndex, index - tokenStartIndex);
                    yield return token;
                    continue;
                }
                if (source[index] == '(')
                {
                    index++;
                    var token = Token.CreateToken(TokenKind.Begin, tokenStartIndex, index - tokenStartIndex);
                    yield return token;
                    continue;
                }
                if (source[index] == ')')
                {
                    index++;
                    var token = Token.CreateToken(TokenKind.End, tokenStartIndex, index - tokenStartIndex);
                    yield return token;
                    continue;
                }
                if (source[index] == '{')
                {
                    index++;
                    var token = Token.CreateToken(TokenKind.BeginScope, tokenStartIndex, index - tokenStartIndex);
                    yield return token;
                    continue;
                }
                if (source[index] == '}')
                {
                    index++;
                    var token = Token.CreateToken(TokenKind.EndScope, tokenStartIndex, index - tokenStartIndex);
                    yield return token;
                    continue;
                }
                if (source[index] == ':')
                {
                    index++;
                    var token = Token.CreateToken(TokenKind.Colon, tokenStartIndex, index - tokenStartIndex);
                    yield return token;
                    continue;
                }
                if (source[index] == ',')
                {
                    index++;
                    var token = Token.CreateToken(TokenKind.Comma, tokenStartIndex, index - tokenStartIndex);
                    yield return token;
                    continue;
                }
                if (source[index] == ';')
                {
                    index++;
                    var token = Token.CreateToken(TokenKind.Semicolon, tokenStartIndex, index - tokenStartIndex);
                    yield return token;
                    continue;
                }
                if (source[index] == '!')
                {
                    index++;

                    if (source[index] == '=')
                    {
                        index++;
                        var token = Token.CreateToken(TokenKind.Inequal, tokenStartIndex, index - tokenStartIndex);
                        yield return token;
                        continue;
                    }
                    index++;
                    var expectedDifferentTokenError = new KatLangException("Expected '=' as part of '!='", tokenStartIndex, index - tokenStartIndex);
                    throw expectedDifferentTokenError;
                }
                if (source[index] == '.')
                {
                    index++;
                    var token = Token.CreateToken(TokenKind.Dot, tokenStartIndex, index - tokenStartIndex);
                    yield return token;
                    continue;
                }

                index++;
                throw new KatLangException($"Unexpected: {source[index-1]}", tokenStartIndex, 1);
            }

            yield return Token.CreateToken(TokenKind.EndOfFile, index, 0);
        }

        public static IEnumerable<Token> Scan(string source)
        {
            return Scan(source, 0, new List<int>());
        }
    }
}
