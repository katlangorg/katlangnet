using System.Collections.Generic;

namespace KatLang
{
    public abstract class Expression
    {
        public int Position { get; set; }
        public int Length { get; set; }

        public override string ToString()
        {
            var builder = new System.Text.StringBuilder();
            var converter = new ExpressionToStringConverter();
            if (this is AlgorithmExpression boundAlgorithm)
            {
                foreach (var expression in boundAlgorithm.Expressions)
                {
                    if(builder.Length > 0)
                    {
                        builder.Append('\n');
                    }
                    builder.Append(converter.Convert(expression));
                }
            }
            else
            {
                builder.Append(converter.Convert(this));
            }
            return builder.ToString();
        }

        public AlgorithmExpression ToAlgorithm()
        {
            if (this is AlgorithmExpression algo)
            {
                return algo;
            }
            return new AlgorithmExpression(new List<Expression> { this });
        }
    }

    public sealed class StringExpression : Expression
    {
        public string Value { get; }

        public StringExpression(string value)
        {
            Value = value;
        }
    }

    public sealed class ConstantExpression : Expression
    {
        public double Value { get; }

        public ConstantExpression(double value)
        {
            Value = value;
        }
    }

    public sealed class ParameterExpression : Expression
    {
        public string Name { get; }

        public int GraceWeight { get; }

        public bool IsIgnored { get; }

        public ParameterExpression()
        {
            Name = "#";
            IsIgnored = true;
        }

        public ParameterExpression(string name, int graceWeight = 0, bool isIgnored = false)
        {
            Name = name;
            GraceWeight = graceWeight;
            IsIgnored = isIgnored;
        }
    }

    public sealed class UnaryExpression : Expression
    {
        public TokenKind Kind { get; }

        public Expression InnerExpression { get; internal set; }

        public UnaryExpression(TokenKind kind, Expression innerExpression)
        {
            Kind = kind;
            InnerExpression = innerExpression;
        }
    }

    public sealed class BinaryExpression : Expression
    {
        public Expression? Lhs { get; internal set; }
        public Expression? Rhs { get; internal set; }
        public TokenKind Kind { get; }

        public BinaryExpression(TokenKind kind, Expression? lhs, Expression? rhs)
        {
            Kind = kind;
            Lhs = lhs;
            Rhs = rhs;
        }
    }

    public sealed class ContentSelectionExpression : Expression
    {
        public Expression Content { get; internal set; }
        public Expression Selector { get; internal set; }

        public ContentSelectionExpression(Expression content, Expression selector)
        {
            Content = content;
            Selector = selector;
        }
    }

    public sealed class PropertyAccessExpression : Expression
    {
        public Expression Algorithm { get; internal set; }
        public ParameterExpression Property { get; }

        public PropertyAccessExpression(Expression algorithm, ParameterExpression property)
        {
            Algorithm = algorithm;
            Property = property;
        }
    }

    public sealed class IgnoreArgumentExpression : Expression { }

    public sealed class AlgorithmExpression : Expression
    {
        public IList<PropertyExpression> Properties { get; }
        public IList<Expression> Expressions { get; internal set; }
        public bool IsParametrized { get; internal set; }

        public AlgorithmExpression() : this(new List<Expression>(), new List<PropertyExpression>()) { }
        public AlgorithmExpression(IList<Expression> expressions): this(expressions, new List<PropertyExpression>()) { }
        public AlgorithmExpression(IList<Expression> expressions, IList<PropertyExpression> properties)
        {
            Expressions = expressions;
            Properties = properties;
        }
    }

    public sealed class PropertyExpression : Expression
    {
        public string Name { get; }
        public Expression Algorithm { get; }

        public PropertyExpression(string name, Expression algorithm)
        {
            Name = name;
            Algorithm = algorithm;
        }
    }

    public sealed class PropertyBranchExpression : Expression
    {
        public string Name { get; }
        public AlgorithmExpression Algorithm { get; }
        public Condition? Condition { get; }

        public PropertyBranchExpression(string name, AlgorithmExpression algorithm, Condition? condition)
        {
            Name = name;
            Algorithm = algorithm;
            Condition = condition;
        }
    }
    
    public sealed class ConditionalAlgorithmExpression: Expression
    {
        public IList<PropertyExpression> Properties { get; }
        public AlgorithmExpression? DefaultBranch { get; internal set; }
        public int ConditionalParametersCount { get; private set; }
        public Dictionary<Condition, AlgorithmExpression> Branches { get; internal set; }

        public ConditionalAlgorithmExpression() : this(new List<PropertyExpression>()) { }
        public ConditionalAlgorithmExpression(IList<PropertyExpression> properties)
        {
            Properties = properties;
            Branches = new Dictionary<Condition, AlgorithmExpression>();
        }

        public void AddBranch(PropertyBranchExpression property)
        {
            if (property.Condition == default)
            {
                if (DefaultBranch != default)
                {
                    throw new KatLangRuntimeException($"The default branch of the conditional property '{property.Name}' is already defined.", property);
                }
                DefaultBranch = property.Algorithm;
            }
            else
            {
                if (Branches.ContainsKey(property.Condition))
                {
                    throw new KatLangRuntimeException($"The conditional property '{property.Name}' already contains a branch with a condition '{property.Condition}'.", property);
                }

                Branches[property.Condition] = property.Algorithm;
                ConditionalParametersCount = property.Condition.Values.Count;
            }
        }

        public AlgorithmExpression? GetBranch(Condition condition)
        {
            if (Branches.TryGetValue(condition, out AlgorithmExpression? result))
            {
                return result;
            }
            throw new KatLangException($"Trying to access a condition {condition}, but the algorithm does not contain it");
        }
    }

    public sealed class PropertyExecutionExpression : Expression
    {
        public Expression? Parent { get; internal set; }

        public ParameterExpression Identity { get; internal set; }

        public AlgorithmExpression? Input { get; internal set; }

        public PropertyExecutionExpression(ParameterExpression identity, AlgorithmExpression? input, Expression? parent = null)
        {
            Identity = identity;
            Input = input;
            Parent = parent;
        }
    }

    public sealed class AlgorithmExecutionExpression : Expression
    {
        public AlgorithmExpression Algorithm { get; internal set; }
        public AlgorithmExpression? Input { get; internal set; }
        public ParameterExpression? PropertyExecutionIdentity { get; private set; }

        public AlgorithmExecutionExpression(AlgorithmExpression algorithm, AlgorithmExpression? input, ParameterExpression? propertyExecutionIdentity = default)
        {
            Algorithm = algorithm;
            Input = input;
            PropertyExecutionIdentity = propertyExecutionIdentity;
        }
    }
}