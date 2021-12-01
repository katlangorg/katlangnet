using System.Collections.Generic;

namespace KatLang
{
    public class Environment
    {
        private readonly Dictionary<string, Expression> _algorithms = new Dictionary<string, Expression>();
        private readonly Dictionary<string, Expression?> _parameters = new Dictionary<string, Expression?>();
        private readonly ExpressionCloneMaker _cloneMaker = new ExpressionCloneMaker();

        public Environment? Parent { get; }

        public Environment(Environment? parent, IList<PropertyExpression>? properties, IList<string> parameters, IList<Expression> arguments, ParameterDetector detector,
            ParameterExpression? propertyExecutionIdentity = default)
        {
            Parent = parent;
            JoinAlgorithm(properties);

            var numberOfBoundParameters = parameters.Count <= arguments.Count ? parameters.Count : arguments.Count;
            for (var i = 0; i < numberOfBoundParameters; i++)
            {
                var parameter = parameters[i];
                var argument = arguments[i];
                if (detector.IsParameterContainedInExpression(parameter, argument))
                {
                    throw new KatLangRuntimeException($"Infinite recursion detected. Property execution lacks an argument for the parameter '{parameter}'.", propertyExecutionIdentity ?? argument);
                }
                _parameters[parameter] = argument;
            }
            for (var i = numberOfBoundParameters; i < parameters.Count; i++)
            {
                //in inner scope is declared parameter with the same name as in outer scope and in inner scope it is not bound
                _parameters[parameters[i]] = default;
            }
        }

        public void JoinAlgorithm(IList<PropertyExpression>? properties)
        {
            if (properties != default)
            {
                foreach (var property in properties)
                {
                    _algorithms[property.Name] = property.Algorithm;
                }
            }
        }

        public Expression? GetParameterValue(string name)
        {
            if (_parameters.ContainsKey(name))
            {
                return _parameters[name];
            }
            if (Parent != default)
            {
                return Parent.GetParameterValue(name);
            }
            return default;
        }

        public bool ContainsParameter(string name)
        {
            if (_parameters.ContainsKey(name))
            {
                return true;
            }
            if (Parent != default)
            {
                return Parent.ContainsParameter(name);
            }
            return false;
        }

        public Expression? GetAlgorithm(string name)
        {
            if (_algorithms.ContainsKey(name))
            {
                return _cloneMaker.Clone(_algorithms[name]);
            }
            if (Parent != default)
            {
                return Parent.GetAlgorithm(name);
            }
            return default;
        }
    }
}