using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net.Http;

namespace KatLang
{
    public class Binder : Visitor
    {
        private Environment? _environment;
        private readonly ParameterDetector _detector;
        private readonly ExpressionCloneMaker _cloneMaker;
        private readonly Func<string, string> downloadKatLangCode;

        public Binder(Func<string, string> katLangCodeDownloadFunc)
        {
            _detector = new ParameterDetector(algorithmName => _environment?.GetAlgorithm(algorithmName) != default);
            _cloneMaker = new ExpressionCloneMaker();
            downloadKatLangCode = katLangCodeDownloadFunc;
        }

        public Expression? Bind(AlgorithmExpression algorithm)
        {
            var parameters = _detector.GetOrderedAlgorithmParameters(algorithm);
            _environment = new Environment(default, algorithm.Properties, parameters, new List<Expression>(), _detector);

            var visited = VisitAlgorithmExpression(algorithm);
            return visited;
        }

        protected override Expression? VisitPropertyAccessExpression(PropertyAccessExpression propertyAccess)
        {
            var expression = VisitExpression(propertyAccess.Algorithm);
            if (expression is AlgorithmExpression algorithm)
            {
                PropertyExpression? property = algorithm.Properties.FirstOrDefault(n => n.Name == propertyAccess.Property.Name);
                if (property != default)
                {
                    return property.Algorithm;
                }
                if (propertyAccess.Property.Name == Language.Length)
                {
                    return new ConstantExpression(algorithm.Expressions.Count);
                }

                var rewrittenProperty = new PropertyExecutionExpression(propertyAccess.Property, algorithm);
                return VisitPropertyExecutionExpression(rewrittenProperty);
            }
            var algorithmFromEnvironment = _environment?.GetAlgorithm(propertyAccess.Property.Name);
            if (algorithmFromEnvironment is AlgorithmExpression algorithmExpression)
            {
                var input = expression != default ? expression.ToAlgorithm() : new();
                return VisitAlgorithmExecutionExpression(new AlgorithmExecutionExpression(algorithmExpression, input, propertyAccess.Property));
            }
            if (expression is ConstantExpression numberConstant)
            {
                if (propertyAccess.Property.Name == Language.String)
                {
                    return new StringExpression(numberConstant.Value.ToString());
                }

                return VisitAlgorithmExecutionExpression(new AlgorithmExecutionExpression(propertyAccess.Property.ToAlgorithm(), expression.ToAlgorithm()));
                //throw new KatLangRuntimeException($"Trying to access non-existent property '{propertyAccess.Property.Name}' of the algorithm '{propertyAccess.Algorithm}'.", propertyAccess);
            }
            if (expression is StringExpression stringConstant)
            {
                if (propertyAccess.Property.Name == Language.Reverse)
                {
                    //return VisitPropertyExecutionExpression(new PropertyExecutionExpression(propertyAccess.Property, expression.ToAlgorithm()));
                    var charArray = stringConstant.Value.ToCharArray();
                    Array.Reverse(charArray);
                    return new StringExpression(new string(charArray));
                }
                throw new KatLangRuntimeException($"Trying to access non-existent property '{propertyAccess.Property.Name}' of the algorithm '{propertyAccess.Algorithm}'.", propertyAccess);
            }
            if (expression is PropertyExecutionExpression)
            {
                //A=load2('http') A.X+5 //trying to access nonexistent property A.X from existing algorithm A
                if (propertyAccess.Algorithm is ParameterExpression)
                {
                    throw new KatLangRuntimeException($"Trying to access non-existent property '{propertyAccess.Property.Name}' of the algorithm '{propertyAccess.Algorithm}'.", propertyAccess);
                }
                //handle the extension property
                return VisitPropertyExecutionExpression(new PropertyExecutionExpression(propertyAccess.Property, expression.ToAlgorithm()));
            }
            return propertyAccess;
        }

        protected override Expression? VisitBinaryExpression(BinaryExpression expression)
        {
            Expression? lhs = expression.Lhs != default ? VisitExpression(expression.Lhs) : default;
            Expression? rhs = expression.Rhs != default ? VisitExpression(expression.Rhs) : default;

            //TODO: figure out if in binary expressions algorithm properties are not needed and get rid of algorithm properties (otherwise the algorithm cannot be unwrapped)
            if (lhs is AlgorithmExpression lhsAlgorithm && lhsAlgorithm.Expressions.Count > 0)
            {
                lhs = lhsAlgorithm.Expressions[0];
            }
            if (rhs is AlgorithmExpression rhsAlgorithm && rhsAlgorithm.Expressions.Count > 0)
            {
                rhs = rhsAlgorithm.Expressions[0];
            }

            if (lhs is ConstantExpression lhsValueExpression && rhs is ConstantExpression rhsValueExpression)
            {
                return expression.Kind switch
                {
                    TokenKind.Pow => new ConstantExpression(Math.Pow(lhsValueExpression.Value, rhsValueExpression.Value)),
                    TokenKind.Divide => new ConstantExpression(lhsValueExpression.Value / rhsValueExpression.Value),
                    TokenKind.Multiply => new ConstantExpression(lhsValueExpression.Value * rhsValueExpression.Value),
                    TokenKind.Div => new ConstantExpression(Math.Floor(lhsValueExpression.Value / rhsValueExpression.Value)),
                    TokenKind.Mod => new ConstantExpression(lhsValueExpression.Value % rhsValueExpression.Value),
                    TokenKind.Plus => new ConstantExpression(lhsValueExpression.Value + rhsValueExpression.Value),
                    TokenKind.Minus => new ConstantExpression(lhsValueExpression.Value - rhsValueExpression.Value),
                    TokenKind.Greater => new ConstantExpression(lhsValueExpression.Value > rhsValueExpression.Value ? 1D : 0D),
                    TokenKind.GreaterEqual => new ConstantExpression(lhsValueExpression.Value >= rhsValueExpression.Value ? 1D : 0D),
                    TokenKind.Less => new ConstantExpression(lhsValueExpression.Value < rhsValueExpression.Value ? 1D : 0D),
                    TokenKind.LessEqual => new ConstantExpression(lhsValueExpression.Value <= rhsValueExpression.Value ? 1D : 0D),
                    TokenKind.Or => new ConstantExpression(lhsValueExpression.Value == 1 || rhsValueExpression.Value == 1 ? 1D : 0D),
                    TokenKind.And => new ConstantExpression(lhsValueExpression.Value == 1 && rhsValueExpression.Value == 1 ? 1D : 0D),
                    TokenKind.Xor => new ConstantExpression(lhsValueExpression.Value == 1 && rhsValueExpression.Value == 0 || lhsValueExpression.Value == 0 && rhsValueExpression.Value == 1 ? 1D : 0D),
                    TokenKind.Equal => new ConstantExpression(lhsValueExpression.Value == rhsValueExpression.Value ? 1D : 0D),
                    TokenKind.Inequal => new ConstantExpression(lhsValueExpression.Value != rhsValueExpression.Value ? 1D : 0D),
                    _ => throw new KatLangRuntimeException($"Unexpected expression: {expression}.", expression),
                };
            }
            if(lhs is StringExpression lhsStringConstant && rhs is StringExpression rhsStringConstant)
            {
                if(expression.Kind == TokenKind.Equal)
                {
                    return lhsStringConstant.Value == rhsStringConstant.Value ? new ConstantExpression(1) : new ConstantExpression(0);
                }
            }

            if(lhs == default && rhs == default)
            {
                return default;
            }

            if(lhs == default ^ rhs == default)
            {
                var descriptor = Language.Operators[expression.Kind];
                if (descriptor.IsSymetric)
                {
                    return rhs ?? lhs;
                }
                else
                {
                    if(rhs == null)
                    {
                        return lhs;
                    }
                    //for non-symetric operators non-existent left-hand-side can't be ignored
                }
            }

            expression.Lhs = lhs;
            expression.Rhs = rhs;
            return expression;
        }

        protected override Expression? VisitAlgorithmExecutionExpression(AlgorithmExecutionExpression algorithm)
        {
            if (algorithm.Algorithm.Expressions.Count == 1 && algorithm.Algorithm.Expressions[0] is PropertyAccessExpression propertyAccess)
            {
                if(propertyAccess.Algorithm is ParameterExpression parameter)
                {
                    var algo = _environment?.GetAlgorithm(parameter.Name);
                    if(algo == default)
                    {
                        //parameter.Name refers to a parameter (not a property). This might happen with following example: K=a.t

                        var algoParameters = _detector.GetOrderedAlgorithmParameters(algorithm.Algorithm);
                        var algoArguments = GetInputForAnotherAlgorithm(algorithm.Input);

                        _environment = new Environment(_environment, algorithm.Algorithm.Properties, algoParameters, algoArguments, _detector, algorithm.PropertyExecutionIdentity);
                        var res = VisitAlgorithmExpression(algorithm.Algorithm);
                        _environment = _environment.Parent;
                        return res;
                    }
                }
                //this might happen in recursive expressions like: Add1.Add1.Check.repeat(...)
                var algorithmExecution = new AlgorithmExecutionExpression(propertyAccess.Algorithm.ToAlgorithm(), algorithm.Input);
                var algorithmObject = VisitAlgorithmExecutionExpression(algorithmExecution);
                if (algorithmObject == default)
                {
                    throw new KatLangRuntimeException($"Attempt to access property {propertyAccess.Property} using invalid object.", propertyAccess.Algorithm);
                }
                var reducedPropertyAccessExpression = new PropertyAccessExpression(algorithmObject, propertyAccess.Property);
                return VisitPropertyAccessExpression(reducedPropertyAccessExpression);
            }

            Expression algorithmForParameterDetection = algorithm.Algorithm;
            if (algorithm.Algorithm.Expressions.Count == 1 && algorithm.Algorithm.Expressions[0] is ParameterExpression parameterExpression)
            {
                var visitedParameterExpression = VisitParameterExpression(parameterExpression);
                if(visitedParameterExpression != null)
                {
                    algorithmForParameterDetection = visitedParameterExpression;
                }
            }

            var parameters = _detector.GetOrderedAlgorithmParameters(algorithmForParameterDetection.ToAlgorithm());
            var arguments = GetInputForAnotherAlgorithm(algorithm.Input);

            _environment = new Environment(_environment, algorithm.Algorithm.Properties, parameters, arguments, _detector, algorithm.PropertyExecutionIdentity);
            var result = VisitAlgorithmExpression(algorithm.Algorithm);
            _environment = _environment.Parent;

            return result;
        }

        protected override Expression? VisitPropertyExecutionExpression(PropertyExecutionExpression expression)
        {
            if (expression.Parent != null)
            {
                if(expression.Parent is ParameterExpression parameterExpression)
                {
                    var visitedParent = VisitParameterExpression(parameterExpression) as AlgorithmExpression;
                    if (visitedParent != null)
                    {
                        var existingPropertyBody = visitedParent?.Properties.FirstOrDefault(n => n.Name == expression.Identity.Name)?.Algorithm;
                        if (existingPropertyBody != default)
                        {
                            //if it is property of existing algorithm
                            return VisitExpression(new AlgorithmExecutionExpression(existingPropertyBody.ToAlgorithm(), expression.Input));
                        }
                    }
                }

                var newInput = new List<Expression>() { expression.Parent };
                if (expression.Input != null)
                {
                    newInput.AddRange(expression.Input.Expressions);
                }
                return VisitExpression(new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(newInput)));
            }

            if (expression.Identity.Name == Language.Repeat)
            {
                var loopInput = expression.Input;
                if(loopInput == default)
                {
                    throw new KatLangRuntimeException($"Expected existing algorithm, but got {loopInput}.", expression.Identity);
                }
                if(loopInput.Expressions.Count < 2)
                {
                    throw new KatLangRuntimeException($"Not provided enough arguments.", expression.Identity);
                }
                var iterations = VisitExpression(loopInput.Expressions[1]) as ConstantExpression;
                if (iterations == default || iterations.Value < 0)
                {
                    throw new KatLangRuntimeException("The second argument of the loop should be a non-negative numeric value representing the number of the loop iterations.", expression.Identity);
                }
                var recursiveBody = loopInput.Expressions[0].ToAlgorithm();
                var inputOutputData = VisitAlgorithmExpression(new AlgorithmExpression(new List<Expression>(loopInput.Expressions.Skip(2))))?.ToAlgorithm();
                
                for (var i = 0; i < iterations.Value; i++)
                {
                    AlgorithmExpression recursiveLoopBody = _cloneMaker.Clone(recursiveBody)!;
                    var visitedExpression = VisitAlgorithmExecutionExpression(new AlgorithmExecutionExpression(recursiveLoopBody, inputOutputData));
                    inputOutputData = visitedExpression?.ToAlgorithm();
                }
                return inputOutputData;
            }
            if (expression.Identity.Name == Language.Loop)
            {
                var loopInput = expression.Input;
                if (loopInput == default)
                {
                    throw new KatLangRuntimeException($"Expected existing algorithm, but got {loopInput}.", expression.Identity);
                }
                if (loopInput.Expressions.Count < 1)
                {
                    throw new KatLangRuntimeException($"Not provided enough arguments.", expression.Identity);
                }
                var recursiveExpression = VisitExpression(loopInput.Expressions[0]);
                if (recursiveExpression == default)
                {
                    throw new KatLangRuntimeException("The first argument of the loop should represent a valid recursive expression.", expression.Identity);
                }
                AlgorithmExpression recursiveBody = recursiveExpression.ToAlgorithm();
                var inputOutputData = VisitAlgorithmExpression(new AlgorithmExpression(new List<Expression>(loopInput.Expressions.Skip(1))))?.ToAlgorithm();
                var parameters = _detector.GetOrderedAlgorithmParameters(recursiveBody);
                while (true)
                {
                    AlgorithmExpression recursiveLoopBody = _cloneMaker.Clone(recursiveBody)!;
                    var arguments = inputOutputData != null ? GetInputForAnotherAlgorithm(inputOutputData) : new List<Expression>();

                    _environment = new Environment(_environment, default, parameters, arguments, _detector, expression.Identity);
                    var loopContinuationExpression = VisitExpression(recursiveLoopBody.Expressions.Last());
                    if (loopContinuationExpression is AlgorithmExpression algorithm)
                    {
                        loopContinuationExpression = algorithm.Expressions.Last();
                    }
                    _environment = _environment.Parent;

                    if (loopContinuationExpression is ConstantExpression loopConstantExpression)
                    {
                        if (loopConstantExpression.Value == 1)
                        {
                            var visitedExpression = VisitAlgorithmExecutionExpression(new AlgorithmExecutionExpression(recursiveLoopBody, inputOutputData));
                            inputOutputData = visitedExpression?.ToAlgorithm();
                        }
                        else
                        {
                            return inputOutputData;
                        }
                    }
                    else
                    {
                        throw new KatLangRuntimeException($"Recursive expression '{recursiveBody}' execution lacks some arguments and loop continuation expression cannot be evaluated.", expression.Identity);
                    }
                }
            }

            Expression? visitedInput = default;
            AlgorithmExpression? inputAlgorithm = default;
            if (expression.Input != null)
            {
                var clone = _cloneMaker.Clone(expression.Input);
                if(clone != default)
                {
                    visitedInput = VisitAlgorithmExpression(clone);
                    inputAlgorithm = visitedInput is AlgorithmExpression visitedAlgorithm
                        ? visitedAlgorithm
                        : new AlgorithmExpression(visitedInput != default ? new List<Expression> { visitedInput } : new List<Expression>()); //IsClosed = expression.Input.IsClosed
                }
            }

            if (expression.Identity.Name == Language.String)
            {
                if (visitedInput is ConstantExpression numberExpression)
                {
                    return new StringExpression(numberExpression.Value.ToString());
                }
            }

            if (expression.Identity.Name == Language.Reverse)
            {
                if (visitedInput is StringExpression stringConstant)
                {
                    var charArray = stringConstant.Value.ToCharArray();
                    Array.Reverse(charArray);
                    return new StringExpression(new string(charArray));
                }
            }

            if (Language.BuiltinAlgorithms.TryGetValue(expression.Identity.Name, out var builtinAlgorithm))
            {
                #region builtin func

                var arguments = GetInputForAnotherAlgorithm(visitedInput);
                var func = builtinAlgorithm;
                if (func.Arity > arguments.Count)
                {
                    throw new KatLangRuntimeException($"Algorithm '{expression.Identity.Name}' expects {func.Arity} arguments, but received {arguments.Count}.", expression);
                }

                ConstantExpression? a;
                ConstantExpression? b;

                switch (expression.Identity.Name)
                {
                    case "abs":
                        a = arguments[0] as ConstantExpression;
                        if (a != null)
                        {
                            return new ConstantExpression(Math.Abs(a.Value));
                        }
                        return new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(arguments));
                    case "ceil":
                        a = arguments[0] as ConstantExpression;
                        if (a != null)
                        {
                            return new ConstantExpression(Math.Ceiling(a.Value));
                        }
                        return new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(arguments));
                    case "floor":
                        a = arguments[0] as ConstantExpression;
                        if (a != null)
                        {
                            return new ConstantExpression(Math.Floor(a.Value));
                        }
                        return new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(arguments));
                    case "round":
                        a = arguments[0] as ConstantExpression;
                        b = arguments[1] as ConstantExpression;
                        if (a != null && b != null)
                        {
                            return new ConstantExpression(Math.Round(a.Value, (int)b.Value));
                        }
                        return new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(arguments));
                    case "sign":
                        a = arguments[0] as ConstantExpression;
                        if (a != null)
                        {
                            return new ConstantExpression(Math.Sign(a.Value));
                        }
                        return new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(arguments));
                    case "div":
                        a = arguments[0] as ConstantExpression;
                        b = arguments[1] as ConstantExpression;
                        if (a != null && b != null)
                        {
                            return new ConstantExpression(Math.Floor(a.Value / b.Value));
                        }
                        return new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(arguments));
                    case "mod":
                        a = arguments[0] as ConstantExpression;
                        b = arguments[1] as ConstantExpression;
                        if (a != null && b != null)
                        {
                            return new ConstantExpression(a.Value % b.Value);
                        }
                        return new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(arguments));
                    case "pow":
                        a = arguments[0] as ConstantExpression;
                        b = arguments[1] as ConstantExpression;
                        if (a != null && b != null)
                        {
                            return new ConstantExpression(Math.Pow(a.Value, b.Value));
                        }
                        return new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(arguments));
                    case "sqrt":
                        a = arguments[0] as ConstantExpression;
                        if (a != null)
                        {
                            return new ConstantExpression(Math.Sqrt(a.Value));
                        }
                        return new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(arguments));
                    case "ln":
                        a = arguments[0] as ConstantExpression;
                        if (a != null)
                        {
                            return new ConstantExpression(Math.Log(a.Value));
                        }
                        return new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(arguments));
                    case "lg":
                        a = arguments[0] as ConstantExpression;
                        if (a != null)
                        {
                            return new ConstantExpression(Math.Log10(a.Value));
                        }
                        return new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(arguments));
                    case "log":
                        a = arguments[0] as ConstantExpression;
                        b = arguments[1] as ConstantExpression;
                        if (a != null && b != null)
                        {
                            return new ConstantExpression(Math.Log(a.Value, b.Value));
                        }
                        return new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(arguments));
                    case "sin":
                        a = arguments[0] as ConstantExpression;
                        if (a != null)
                        {
                            return new ConstantExpression(Math.Sin(a.Value));
                        }
                        return new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(arguments));
                    case "asin":
                        a = arguments[0] as ConstantExpression;
                        if (a != null)
                        {
                            return new ConstantExpression(Math.Asin(a.Value));
                        }
                        return new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(arguments));
                    case "cos":
                        a = arguments[0] as ConstantExpression;
                        if (a != null)
                        {
                            return new ConstantExpression(Math.Cos(a.Value));
                        }
                        return new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(arguments));
                    case "acos":
                        a = arguments[0] as ConstantExpression;
                        if (a != null)
                        {
                            return new ConstantExpression(Math.Acos(a.Value));
                        }
                        return new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(arguments));
                    case "tan":
                        a = arguments[0] as ConstantExpression;
                        if (a != null)
                        {
                            return new ConstantExpression(Math.Tan(a.Value));
                        }
                        return new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(arguments));
                    case "atan":
                        a = arguments[0] as ConstantExpression;
                        if (a != null)
                        {
                            return new ConstantExpression(Math.Atan(a.Value));
                        }
                        return new PropertyExecutionExpression(expression.Identity, new AlgorithmExpression(arguments));
                }

                #endregion
            }

            //user algorithm processing
            var parentAlgorithm = _environment?.GetAlgorithm(expression.Identity.Name);
            if (parentAlgorithm != default)
            {
                if (parentAlgorithm is ConditionalAlgorithmExpression conditionalAlgorithm)
                {
                    var arguments = GetInputForAnotherAlgorithm(visitedInput);
                    if (conditionalAlgorithm.ConditionalParametersCount > arguments.Count)
                    {
                        throw new KatLangRuntimeException("Not supplied enough arguments for function conditional parameters!", expression);
                    }

                    var conditionValues = new List<double>();
                    for (var i = 0; i < conditionalAlgorithm.ConditionalParametersCount; i++)
                    {
                        var argument = arguments[i];
                        if (VisitExpression(argument) is ConstantExpression visitedArgument)
                        {
                            conditionValues.Add(visitedArgument.Value);
                        }
                        else
                        {
                            //not all arguments are not provided for the expression evaluation, therefore leave it as is.
                            return expression;
                        }
                    }

                    //find the right branch to execute
                    var condition = new Condition(conditionValues);
                    int nonConditionalArgumentsStartIndex;
                    if (conditionalAlgorithm.Branches.TryGetValue(condition, out var branchToExecute))
                    {
                        nonConditionalArgumentsStartIndex = conditionalAlgorithm.ConditionalParametersCount;
                    }
                    else
                    {
                        nonConditionalArgumentsStartIndex = 0;
                        branchToExecute = conditionalAlgorithm.DefaultBranch;
                    }

                    var argumentsForNonConditionalParameters = new List<Expression>();
                    for (var i = nonConditionalArgumentsStartIndex; i < arguments.Count; i++)
                    {
                        var visitedArgument = VisitExpression(arguments[i]);
                        if (visitedArgument != null)
                        {
                            argumentsForNonConditionalParameters.Add(visitedArgument);
                        }
                    }

                    var resultingList = new List<Expression>();
                    if (branchToExecute != null)
                    {
                        var parameters = _detector.GetOrderedAlgorithmParameters(branchToExecute);
                        _environment = new Environment(_environment, conditionalAlgorithm.Properties, parameters, argumentsForNonConditionalParameters, _detector, expression.Identity);

                        foreach (var command in branchToExecute.Expressions)
                        {
                            var visitedCommand = VisitExpression(command);
                            if (visitedCommand != null)
                            {
                                resultingList.Add(visitedCommand);
                            }
                        }
                        _environment = _environment.Parent;

                        if (resultingList.Count > 0)
                        {
                            if (resultingList.Count == 1)
                            {
                                return resultingList[0];
                            }
                            return new AlgorithmExpression(resultingList);
                        }
                        return null;
                    }
                    else
                    {
                        throw new KatLangRuntimeException($"Non-existent conditional branch for condition: {condition}", expression.Identity);
                    }
                }
                if(parentAlgorithm is AlgorithmExpression algorithm)
                {
                    if(inputAlgorithm != null && !inputAlgorithm.IsParametrized)
                    {
                        var unboundInputParameters = _detector.GetOrderedAlgorithmParameters(inputAlgorithm);

                        foreach (var p in unboundInputParameters.ToList())
                        {
                            //TODO: think how to improve performance
                            var param = _environment?.GetParameterValue(p);
                            if (param != default)
                            {
                                unboundInputParameters.Remove(p);
                            }
                        }

                        if(unboundInputParameters.Count > 0)
                        {
                            //if input is non-parametrized algorithm with free(unbound) variable, then do not process this property execution expression
                            expression.Input = inputAlgorithm;
                            return expression;
                        }
                    }

                    return VisitAlgorithmExecutionExpression(new AlgorithmExecutionExpression(algorithm, inputAlgorithm, expression.Identity));
                }
                return parentAlgorithm;
            }

            if (expression.Identity.Name == Language.If)
            {
                var arguments = GetInputForAnotherAlgorithm(visitedInput);
                if (arguments.Count < 2)
                {
                    throw new KatLangRuntimeException($"Expression 'if' expects at least 2 parameters, but got {arguments.Count}.", expression);
                }
                var a = arguments[0] as ConstantExpression;
                if(a == default)
                {
                    return expression; //conditional argument not provided
                }
                var b = arguments[1];
                if (arguments.Count == 2)
                {
                    return a?.Value != 0 ? b : null;
                }
                var c = arguments[2];
                return a?.Value != 0 ? b : c;
            }

            if(expression.Identity.Name == Language.Load)
            {
                if (expression.Input?.Expressions.Count == 1 && expression.Input.Expressions[0] is StringExpression addressExpression)
                {
                    string code;
                    try
                    {
                        code = downloadKatLangCode(addressExpression.Value);
                    }
                    catch (Exception e)
                    {
                        throw new KatLangRuntimeException($"Invalid algorithm location: '{addressExpression.Value}'. {e.Message} {e.InnerException?.Message}", expression);
                    }

                    var result = Parser.Parse(code);
                    if(result.Errors.Count > 0)
                    {
                        throw new KatLangRuntimeException($"Invalid KatLang code at: '{addressExpression.Value}'", expression);
                    }
                    return VisitExpression(result.Expression);
                }
                throw new KatLangRuntimeException("Algorithm loading expects one parameter - URL of the KatLang code", expression);
            }

            if (expression.Identity.Name == Language.Open)
            {
                if (expression.Input?.Expressions.Count == 1 && expression.Input.Expressions[0] is StringExpression addressExpression)
                {
                    string code;
                    try
                    {
                        code = File.ReadAllText(addressExpression.Value);
                    }
                    catch (Exception e)
                    {
                        throw new KatLangRuntimeException($"File reading failed: '{addressExpression.Value}'. {e.Message} {e.InnerException?.Message}", expression);
                    }

                    var result = Parser.Parse(code);
                    if (result.Errors.Count > 0)
                    {
                        throw new KatLangRuntimeException($"Invalid KatLang code at: '{addressExpression.Value}'", expression);
                    }
                    return VisitExpression(result.Expression);
                }
                throw new KatLangRuntimeException("Algorithm opening expects one parameter - address of the KatLang code file", expression);
            }

            if (expression.Identity.Name == Language.Join)
            {
                if (expression.Input?.Expressions.Count == 1)
                {
                    if (expression.Input.Expressions[0] is StringExpression addressExpression)
                    {
                        string code;
                        try
                        {
                            code = downloadKatLangCode(addressExpression.Value);
                        }
                        catch (Exception e)
                        {
                            throw new KatLangRuntimeException($"Invlaid algorithm location: '{addressExpression.Value}'. {e.Message}", expression);
                        }

                        var result = Parser.Parse(code);
                        if (result.Errors.Count > 0)
                        {
                            throw new KatLangRuntimeException($"Invalid KatLang code at: '{addressExpression.Value}'", expression);
                        }
                        var algorithm = VisitExpression(result.Expression) as AlgorithmExpression;
                        _environment?.JoinAlgorithm(algorithm?.Properties);
                        return default;
                    }
                    if (expression.Input.Expressions[0] is ParameterExpression parameter)
                    {
                        var algorithm = _environment?.GetAlgorithm(parameter.Name) as AlgorithmExpression;
                        if (algorithm != default)
                        {
                            var result = VisitExpression(algorithm) as AlgorithmExpression;
                            _environment?.JoinAlgorithm(result?.Properties);
                        }
                        else
                        {
                            throw new KatLangRuntimeException($"Unknown property '{parameter.Name}'", expression);
                        }
                        return default;
                    }
                    throw new KatLangRuntimeException("The argument of the 'join' operator should be address of the KatLang code or algorithm expression", expression);
                }
                throw new KatLangRuntimeException("Algorithm loading expects one parameter", expression);
            }

            if (expression.Identity.Name == Language.Combine)
            {
                if(expression.Input?.Expressions?.Count == 0)
                {
                    throw new KatLangRuntimeException("No input provided for the algorithm combining!", expression);
                }
                var processedInput = new List<Expression>();
                foreach(var inputExpressionPart in expression.Input!.Expressions)
                {
                    var processedInputExpressionPart = VisitExpression(inputExpressionPart);
                    if(processedInputExpressionPart != default)
                    {
                        processedInput.Add(processedInputExpressionPart);
                    }
                }

                //cannot safely reduce the expression if it contains at least 1 unprocessed property execution.
                if(processedInput.Any(n => n is PropertyExecutionExpression))
                {
                    return new PropertyExecutionExpression(new ParameterExpression(Language.Combine), new AlgorithmExpression(processedInput));
                }

                var combinedInput = new List<Expression>();
                var combinedProperties = new List<PropertyExpression>();
                
                foreach(var input in processedInput)
                {
                    if(input is AlgorithmExpression algorithm && !algorithm.IsParametrized)
                    {
                        foreach(var algorithmPart in algorithm.Expressions)
                        {
                            combinedInput.Add(algorithmPart);
                        }
                        foreach(var property in algorithm.Properties)
                        {
                            combinedProperties.Add(property);
                        }
                    }
                    else
                    {
                        combinedInput.Add(input);
                    }
                }


                return new AlgorithmExpression(combinedInput, combinedProperties);
            }

            //it is parameter name and the paremeter is bound to some algorithm
            var parameterValue = _environment?.GetParameterValue(expression.Identity.Name);
            if (parameterValue != default)
            {
                var algorithm = parameterValue is AlgorithmExpression expression1 ? expression1 : new AlgorithmExpression(new List<Expression> { parameterValue });
                return VisitAlgorithmExecutionExpression(new AlgorithmExecutionExpression(algorithm, inputAlgorithm, expression.Identity));
            }

            //all arguments are not provided for the expression evaluation, therefore leave it as is
            expression.Input = inputAlgorithm;
            return expression;
        }

        protected override Expression? VisitParameterExpression(ParameterExpression paramExpression)
        {
            if (paramExpression.IsIgnored)
            {
                return null;
            }
            var parameterValue = _environment?.GetParameterValue(paramExpression.Name);
            if (parameterValue != null)
            {
                if(_detector.IsParameterContainedInExpression(paramExpression.Name, parameterValue))
                {
                    //avoid infinite loop
                    return parameterValue;
                }
                return VisitExpression(parameterValue);
            }
            var existingAlgorithm = _environment?.GetAlgorithm(paramExpression.Name);
            if(existingAlgorithm != null)
            {
                return VisitExpression(existingAlgorithm);
            }
            switch (paramExpression.Name)
            {
                //TODO: think about moving this little bit up the recursion calls. Constants are not parameters and they should not be processed here.
                case Language.Pi:
                    return new ConstantExpression(Math.PI);
                case Language.Exp:
                    return new ConstantExpression(Math.E);
                default:
                    return paramExpression;
            }
        }

        protected override Expression? VisitContentSelectionExpression(ContentSelectionExpression expression)
        {
            ContentSelectionExpression? result = base.VisitContentSelectionExpression(expression) as ContentSelectionExpression;
            if(result?.Content is AlgorithmExpression algorithm && result.Selector is ConstantExpression constant1)
            {
                var val = (int)constant1.Value;
                if (val < 0 || val >= algorithm.Expressions.Count)
                {
                    throw new KatLangException("Index out of range.", expression);
                }
                return algorithm.Expressions[val];
            }
            if (result?.Content is ConstantExpression content && result.Selector is ConstantExpression constant2)
            {
                if(constant2.Value != 0)
                {
                    throw new KatLangException("Index out of range.", expression);
                }
                return content;
            }
            return result;
        }

        protected override Expression? VisitUnaryExpression(UnaryExpression expression)
        {
            var innerExpression = VisitExpression(expression.InnerExpression);
            if (!ReferenceEquals(expression, innerExpression))
            {
                if (expression.Kind == TokenKind.Minus)
                {
                    return innerExpression is ConstantExpression constant ? new ConstantExpression(-constant.Value) : expression;
                }
                if(expression.Kind == TokenKind.Not)
                {
                    return innerExpression is ConstantExpression constant ? new ConstantExpression(constant.Value != 0 ? 0 : 1) : expression;
                }
            }

            return expression;
        }

        protected override Expression? VisitIgnoreArgumentExpression(IgnoreArgumentExpression expression)
        {
            return default;
        }

        protected override Expression? VisitAlgorithmExpression(AlgorithmExpression algorithm)
        {
            var result = base.VisitAlgorithmExpression(algorithm);
            return result != default ? UnwrapAlgorithm(result) : default;
        }

        private Expression? UnwrapAlgorithm(Expression expression)
        {
            if (expression is AlgorithmExpression basicAlgorithm && basicAlgorithm.Properties.Count == 0)
            {
                switch (basicAlgorithm.Expressions.Count)
                {
                    case 0:
                        return null;
                    case 1:
                        if (basicAlgorithm.IsParametrized)
                        {
                            var parameters = _detector.GetOrderedAlgorithmParameters(basicAlgorithm);
                            if(parameters.Count > 0)
                            {
                                return basicAlgorithm;
                            }
                        }
                        return UnwrapAlgorithm(basicAlgorithm.Expressions[0]);
                    default:
                        for (var i = 0; i < basicAlgorithm.Expressions.Count; i++)
                        {
                            var unwrapped = UnwrapAlgorithm(basicAlgorithm.Expressions[i]);
                            if(unwrapped != default)
                            {
                                basicAlgorithm.Expressions[i] = unwrapped;
                            }
                            else
                            {
                                basicAlgorithm.Expressions[i] = new AlgorithmExpression();
                            }
                        }
                        var partsToRemove = basicAlgorithm.Expressions.OfType<AlgorithmExpression>().Where(n => n.Expressions.Count == 0).ToList();
                        foreach (var partToRemove in partsToRemove)
                        {
                            basicAlgorithm.Expressions.Remove(partToRemove);
                        }
                        break;
                }
            }

            return expression;
        }

        private static IList<Expression> GetInputForAnotherAlgorithm(Expression? expression)
        {
            return expression is AlgorithmExpression basicAlgorithm
                ? basicAlgorithm.Expressions
                : expression != default ? new List<Expression> { expression } : new List<Expression>();
        }
    }
}
