using System;
using System.Collections.Generic;
using System.Linq;

namespace KatLang
{
    public class ParameterDetector: Visitor
    {
        private readonly Func<string, bool> _isProperty;
        private List<ParameterWeightHolder>? _parameters;
        private AlgorithmExpression? _rootAlgorithm;

        public ParameterDetector(Func<string, bool> isProperty)
        {
            _isProperty = isProperty;
        }

        public bool IsParameterContainedInExpression(string parameterName, Expression expression)
        {
            _parameters = new List<ParameterWeightHolder>();

            VisitExpression(expression);

            return _parameters.Any(n => n.Name == parameterName);
        }

        public IList<string> GetOrderedAlgorithmParameters(AlgorithmExpression expression)
        {
            _rootAlgorithm = expression;
            _parameters = new List<ParameterWeightHolder>();

            VisitAlgorithmExpression(expression);

            void Swap(int aIndexVal, int bIndexVal)
            {
                var temp = _parameters[aIndexVal];
                _parameters[aIndexVal] = _parameters[bIndexVal];
                _parameters[bIndexVal] = temp;
            }

            for (var i = 0; i < _parameters.Count; i++)
            {
                var aIndex = i;
                var a = _parameters[i];

                while (true)
                {
                    if (a.Weight == 0)
                    {
                        break;
                    }
                    if (a.Weight > 0)
                    {
                        if (aIndex < _parameters.Count - 1)
                        {
                            var b = _parameters[aIndex + 1];
                            if (b.Weight < a.Weight)
                            {
                                a.Weight--;
                                Swap(aIndex, aIndex + 1);
                                aIndex++;
                                continue;
                            }
                        }
                        break;
                    }
                    if (a.Weight < 0)
                    {
                        if (aIndex > 0)
                        {
                            var b = _parameters[aIndex - 1];
                            if (b.Weight > a.Weight)
                            {
                                a.Weight++;
                                Swap(aIndex, aIndex - 1);
                                aIndex--;
                                continue;
                            }
                        }
                        break;
                    }
                }
            }

            return _parameters.Select(n => n.Name).ToList();
        }

        protected override Expression VisitParameterExpression(ParameterExpression expression)
        {
            ReadParamaters(expression);
            return expression;
        }

        protected override Expression? VisitIgnoreArgumentExpression(IgnoreArgumentExpression expression)
        {
            _parameters?.Add(new ParameterWeightHolder(new ParameterExpression()));
            return expression;
        }

        protected override ParameterExpression VisitPropertyIdentityExpression(ParameterExpression expression)
        {
            ReadParamaters(expression);
            return expression;
        }

        protected override Expression? VisitAlgorithmExpression(AlgorithmExpression algorithm)
        {
            if (algorithm == _rootAlgorithm || !algorithm.IsParametrized)
            {
                return base.VisitAlgorithmExpression(algorithm);
            }
            return algorithm;
        }

        private void ReadParamaters(ParameterExpression expression)
        {
            if (!IsKnownIdentifier(expression.Name))
            {
                var existingParameter = _parameters?.FirstOrDefault(n => n.Name == expression.Name);
                if (existingParameter != null)
                {
                    existingParameter.Weight += expression.GraceWeight;
                }
                else
                {
                    _parameters?.Add(new ParameterWeightHolder(expression));
                }
            }
        }

        private bool IsKnownIdentifier(string id)
        {
            return _isProperty(id) || Language.BuiltinAlgorithms.ContainsKey(id) || Language.KeywordTokens.ContainsKey(id);
        }
    }
}
