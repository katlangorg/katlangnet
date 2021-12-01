using System.Collections.Generic;

namespace KatLang
{
    public abstract class Visitor
    {
        protected virtual Expression? VisitExpression(Expression expression)
        {
            if (expression is ConstantExpression constant)
            {
                return VisitConstantExpression(constant);
            }
            if (expression is BinaryExpression binary)
            {
                if(binary.Kind == TokenKind.Colon)
                {
                    if(binary.Rhs == default)
                    {
                        return binary.Lhs;
                    }
                    if(binary.Lhs == null)
                    {
                        throw new KatLangException("Content selection operator cannot be applied to empty content");
                    }
                    return VisitContentSelectionExpression(new ContentSelectionExpression(binary.Lhs, binary.Rhs));
                }
                return VisitBinaryExpression(binary);
            }
            if (expression is ParameterExpression parameter)
            {
                return VisitParameterExpression(parameter);
            }
            if (expression is UnaryExpression negation)
            {
                return VisitUnaryExpression(negation);
            }
            if (expression is IgnoreArgumentExpression ignoreArguments)
            {
                return VisitIgnoreArgumentExpression(ignoreArguments);
            }
            if (expression is ContentSelectionExpression contentSelection)
            {
                return VisitContentSelectionExpression(contentSelection);
            }
            if (expression is PropertyExecutionExpression propertyExecution)
            {
                return VisitPropertyExecutionExpression(propertyExecution);
            }
            if (expression is AlgorithmExecutionExpression algorithmExecution)
            {
                return VisitAlgorithmExecutionExpression(algorithmExecution);
            }
            if (expression is AlgorithmExpression algorithm)
            {
                return VisitAlgorithmExpression(algorithm);
            }
            if (expression is PropertyAccessExpression propertyAccessExpression)
            {
                return VisitPropertyAccessExpression(propertyAccessExpression);
            }
            if (expression is ConditionalAlgorithmExpression conditionalAlgorithm)
            {
                return VisitConditionalAlgorithmExpression(conditionalAlgorithm);
            }
            if (expression is StringExpression stringExpression)
            {
                return VisitStringExpression(stringExpression);
            }
            return expression;
        }

        protected virtual StringExpression VisitStringExpression(StringExpression expression)
        {
            return expression;
        }

        protected virtual Expression VisitConstantExpression(ConstantExpression expression)
        {
            return expression;
        }

        protected virtual Expression? VisitBinaryExpression(BinaryExpression expression)
        {
            if(expression.Lhs != default)
            {
                expression.Lhs = VisitExpression(expression.Lhs);
            }
            if(expression.Rhs != default)
            {
                expression.Rhs = VisitExpression(expression.Rhs);
            }
            return expression;
        }

        protected virtual Expression? VisitContentSelectionExpression(ContentSelectionExpression expression)
        {
            var content = VisitExpression(expression.Content);
            if (content == default)
            {
                throw new KatLangException("Content selection operator cannot be applied to empty content");
            }
            var selector = VisitExpression(expression.Selector);
            if (selector == default)
            {
                return content;
            }
            expression.Content = content;
            expression.Selector = selector;
            return expression;
        }

        protected virtual ParameterExpression VisitPropertyIdentityExpression(ParameterExpression nameExpression)
        {
            return nameExpression;
        }

        protected virtual Expression? VisitParameterExpression(ParameterExpression paramExpression)
        {
            return paramExpression;
        }

        protected virtual Expression? VisitUnaryExpression(UnaryExpression expression)
        {
            var visitedInnerExpression = VisitExpression(expression.InnerExpression);
            if (visitedInnerExpression != default)
            {
                expression.InnerExpression = visitedInnerExpression;
                return expression;
            }
            return default;
        }

        protected virtual Expression? VisitIgnoreArgumentExpression(IgnoreArgumentExpression expression)
        {
            return expression;
        }

        protected virtual Expression? VisitAlgorithmExpression(AlgorithmExpression algorithm)
        {
            var visitedExpressions = new List<Expression>();
            foreach (var singleResult in algorithm.Expressions)
            {
                var visitedExpression = VisitExpression(singleResult);
                if (visitedExpression != null)
                {
                    visitedExpressions.Add(visitedExpression);
                }
            }
            algorithm.Expressions = visitedExpressions;

            return algorithm;
        }

        protected virtual Expression? VisitPropertyAccessExpression(PropertyAccessExpression propertyAccess)
        {
            var visitedAlgorithm = VisitExpression(propertyAccess.Algorithm);
            if(visitedAlgorithm == default)
            {
                throw new KatLangException("Algorithm in the property access expression reduced to nothing.");
            }
            propertyAccess.Algorithm = visitedAlgorithm;
            VisitParameterExpression(propertyAccess.Property);
            return propertyAccess;
        }

        protected virtual Expression VisitConditionalAlgorithmExpression(ConditionalAlgorithmExpression algorithm)
        {
            if (algorithm.Branches.Count > 0)
            {
                var visitedBranches = new Dictionary<Condition, AlgorithmExpression>();

                foreach (var branch in algorithm.Branches)
                {
                    var visitedExpressions = new List<Expression>();
                    foreach (var singleResult in branch.Value.Expressions)
                    {
                        var visitedExpression = VisitExpression(singleResult);
                        if(visitedExpression != default)
                        {
                            visitedExpressions.Add(visitedExpression);
                        }
                    }
                    visitedBranches.Add(branch.Key, new AlgorithmExpression(visitedExpressions, branch.Value.Properties));
                }
                algorithm.Branches = visitedBranches;
            }

            if (algorithm.DefaultBranch != default)
            {
                var visitedExpressions = new List<Expression>();
                foreach (var singleResult in algorithm.DefaultBranch.Expressions)
                {
                    var visitedExpression = VisitExpression(singleResult);
                    if(visitedExpression != default)
                    {
                        visitedExpressions.Add(visitedExpression);
                    }
                }
                algorithm.DefaultBranch = new AlgorithmExpression(visitedExpressions, algorithm.DefaultBranch.Properties);
            }
            return algorithm;
        }

        protected virtual Expression? VisitPropertyExecutionExpression(PropertyExecutionExpression expression)
        {
            expression.Identity = VisitPropertyIdentityExpression(expression.Identity);
            if (expression.Input != default)
            {
                expression.Input = VisitAlgorithmExpression(expression.Input) as AlgorithmExpression;
            }
            return expression;
        }

        protected virtual Expression? VisitAlgorithmExecutionExpression(AlgorithmExecutionExpression expression)
        {
            Expression? visitedAlgorithm = VisitAlgorithmExpression(expression.Algorithm);
            if(visitedAlgorithm is AlgorithmExpression algorithm)
            {
                expression.Algorithm = algorithm;
                if (expression.Input != default)
                {
                    expression.Input = VisitAlgorithmExpression(expression.Input) as AlgorithmExpression;
                }
                return expression;
            }
            return default;
        }
    }
}
