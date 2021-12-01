using System.Collections.Generic;
using System.Globalization;
using System.Text;

namespace KatLang
{
    public class ExpressionToStringConverter : Visitor
    {
#pragma warning disable CS8618
        private StringBuilder _builder;
#pragma warning restore CS8618

        public string Convert(Expression expression)
        {
            if(expression is ConstantExpression constant)
            {
                return constant.Value.ToString(CultureInfo.InvariantCulture);
            }

            _builder = new StringBuilder();

            VisitExpression(expression);

            return _builder.ToString();
        }

        protected override Expression VisitConstantExpression(ConstantExpression expression)
        {
            _builder.Append(expression.Value.ToString(CultureInfo.InvariantCulture));
            return expression;
        }

        protected override Expression VisitBinaryExpression(BinaryExpression expression)
        {
            if(expression.Lhs != default)
            {
                VisitExpression(expression.Lhs);
            }

            string op;

            switch (expression.Kind)
            {
                case TokenKind.And:
                    op = "and";
                    break;
                case TokenKind.Or:
                    op = "or";
                    break;
                case TokenKind.Xor:
                    op = "xor";
                    break;
                case TokenKind.Plus:
                    op = "+";
                    break;
                case TokenKind.Minus:
                    op = "-";
                    break;
                case TokenKind.Multiply:
                    op = "*";
                    break;
                case TokenKind.Divide:
                    op = "/";
                    break;
                case TokenKind.Mod:
                    op = "mod";
                    break;
                case TokenKind.Pow:
                    op = "^";
                    break;
                case TokenKind.Equal:
                    op = "==";
                    break;
                case TokenKind.Inequal:
                    op = "!=";
                    break;
                case TokenKind.Greater:
                    op = ">";
                    break;
                case TokenKind.Less:
                    op = "<";
                    break;
                case TokenKind.GreaterEqual:
                    op = ">=";
                    break;
                case TokenKind.LessEqual:
                    op = "<=";
                    break;
                default:
                    op = "op";
                    break;
            }

            _builder.Append(op);

            if(expression.Rhs != default)
            {
                VisitExpression(expression.Rhs);
            }

            return expression;
        }

        protected override Expression VisitAlgorithmExpression(AlgorithmExpression algorithm)
        {
            var simpleExpression = _builder.Length == 0;
            if (!simpleExpression)
            {
                _builder.Append('(');
            }

            if (algorithm.Expressions != null)
            {
                var visitedExpressions = new List<Expression>();
                foreach (var singleResult in algorithm.Expressions)
                {
                    if (visitedExpressions.Count > 0)
                    {
                        _builder.Append(',');
                    }
                    var visitedExpression = VisitExpression(singleResult);
                    if(visitedExpression != default)
                    {
                        visitedExpressions.Add(visitedExpression);
                    }
                }
                algorithm.Expressions = visitedExpressions;
            }

            if (!simpleExpression)
            {
                _builder.Append(')');
            }

            return algorithm;
        }

        protected override Expression VisitConditionalAlgorithmExpression(ConditionalAlgorithmExpression algorithm)
        {
            var simpleExpression = algorithm.ConditionalParametersCount == 0 && algorithm.Branches.Count == 0;
            if (!simpleExpression)
            {
                _builder.Append('(');
            }

            if (algorithm.Branches?.Count > 0)
            {
                foreach (var branch in algorithm.Branches)
                {
                    var needComma = false;
                    foreach (var singleResult in branch.Value.Expressions)
                    {
                        if (needComma)
                        {
                            _builder.Append(',');
                        }
                        needComma = true;
                    }
                }
            }

            if (algorithm.DefaultBranch != null)
            {
                var needComma = false;
                foreach (var singleResult in algorithm.DefaultBranch.Expressions)
                {
                    if (needComma)
                    {
                        _builder.Append(',');
                    }
                    needComma = true;
                }
            }

            if (!simpleExpression)
            {
                _builder.Append(')');
            }
            return algorithm;
        }

        protected override Expression VisitParameterExpression(ParameterExpression paramExpression)
        {
            _builder.Append(paramExpression.Name);
            return paramExpression;
        }

        protected override Expression VisitUnaryExpression(UnaryExpression expression)
        {
            switch (expression.Kind)
            {
                case TokenKind.Minus:
                    _builder.Append("-");
                    break;
                default:
                    _builder.Append($"{expression.Kind.ToString().ToLower()} ");
                    break;
            }
            VisitExpression(expression.InnerExpression);
            return expression;
        }

        protected override Expression? VisitPropertyAccessExpression(PropertyAccessExpression propertyAccess)
        {
            VisitExpression(propertyAccess.Algorithm);
            _builder.Append('.');
            VisitParameterExpression(propertyAccess.Property);

            return propertyAccess;
        }

        protected override Expression? VisitPropertyExecutionExpression(PropertyExecutionExpression expression)
        {
            _builder.Append(expression.Identity.Name);
            if(expression.Input != null)
            {
                VisitExpression(expression.Input);
            }
            return expression;
        }

        protected override Expression? VisitContentSelectionExpression(ContentSelectionExpression expression)
        {
            VisitExpression(expression.Content);
            _builder.Append(":");
            VisitExpression(expression.Selector);
            return expression;
        }
    }
}
