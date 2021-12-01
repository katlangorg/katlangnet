using System.Collections.Generic;

namespace KatLang
{
    public class ExpressionCloneMaker: Visitor
    {
        public T? Clone<T>(T original) where T : Expression
        {
            var isPrimitive = original is ConstantExpression || original is ParameterExpression;
            return isPrimitive ? original : VisitExpression(original) as T;
        }

        protected override Expression? VisitAlgorithmExpression(AlgorithmExpression algorithm)
        {
            var clone = new AlgorithmExpression(new List<Expression>(algorithm.Expressions), algorithm.Properties)
            {
                IsParametrized = algorithm.IsParametrized,
                Position = algorithm.Position,
                Length = algorithm.Length
            };
            return base.VisitAlgorithmExpression(clone);
        }

        protected override Expression? VisitContentSelectionExpression(ContentSelectionExpression expression)
        {
            var clone = new ContentSelectionExpression(expression.Content, expression.Selector)
            {
                Position = expression.Position,
                Length = expression.Length
            };
            return base.VisitContentSelectionExpression(clone);
        }

        protected override Expression? VisitBinaryExpression(BinaryExpression expression)
        {
            var clone = new BinaryExpression(expression.Kind, expression.Lhs, expression.Rhs)
            {
                Position = expression.Position,
                Length = expression.Length
            };

            return base.VisitBinaryExpression(clone);
        }

        protected override Expression? VisitPropertyExecutionExpression(PropertyExecutionExpression expression)
        {
            var clone = new PropertyExecutionExpression(expression.Identity, expression.Input, expression.Parent)
            {
                Position = expression.Position,
                Length = expression.Length
            };

            return base.VisitPropertyExecutionExpression(clone);
        }
    }
}
