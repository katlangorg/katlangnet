namespace KatLang.Semantics;

/// <summary>
/// Builds source-backed KatLang semantic information for editor tooling.
/// The model follows KatLang language rules such as ownership-first lookup,
/// public-only opens, explicit ordinary clause parameters, implicit
/// parameters, and conditional branch binders.
/// </summary>
public static class SemanticModelBuilder
{
    /// <summary>
    /// Builds a semantic model from a parsed KatLang root algorithm.
    /// Throws if unresolved <c>load</c> syntax reaches semantic modeling.
    /// </summary>
    public static SemanticModel Build(Algorithm root)
    {
        LoadElaborationGuard.ThrowIfUnresolvedLoad(root, "Semantic model building");
        return new Builder().Build(root);
    }

    /// <summary>
    /// Builds a semantic model from a parse result.
    /// Throws if unresolved <c>load</c> syntax reaches semantic modeling.
    /// </summary>
    public static SemanticModel Build(ParseResult parseResult)
        => Build(parseResult.Root);

    /// <summary>
    /// Enumerates source-backed identifier references and member occurrences.
    /// </summary>
    public static IReadOnlyList<IdentifierOccurrence> EnumerateIdentifierOccurrences(Algorithm root)
        => Build(root).IdentifierOccurrences;

    /// <summary>
    /// Enumerates source-backed declaration sites.
    /// </summary>
    public static IReadOnlyList<DeclarationOccurrence> EnumerateDeclarationOccurrences(Algorithm root)
        => Build(root).Declarations;

    /// <summary>
    /// Enumerates property-centered semantic objects.
    /// </summary>
    public static IReadOnlyList<PropertyInfo> EnumeratePropertyInfos(Algorithm root)
        => Build(root).PropertyInfos;

    private sealed class Builder
    {
        private static readonly Algorithm.User MathAlgorithm = CreateMathAlgorithm();
        private static readonly ScopeFrame PreludeScope = CreatePreludeScope();
        private static readonly SymbolDefinition StringIntrinsicSymbol = CreateBuiltinSymbol("string", algorithm: null, isPublic: true);

        private readonly List<IdentifierOccurrence> _identifierOccurrences = [];
        private readonly List<DeclarationOccurrence> _declarations = [];
        private readonly List<IdentifierResolution> _identifierResolutions = [];
        private readonly List<PropertyInfo> _propertyInfos = [];
        private readonly HashSet<PropertyInfo> _seenPropertyInfos = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<DeclarationOccurrence, PropertyInfo> _propertyInfoByDeclaration = [];
        private readonly Dictionary<Property, SymbolDefinition> _propertySymbolCache =
            new(ReferenceEqualityComparer.Instance);

        public SemanticModel Build(Algorithm root)
        {
            VisitAlgorithm(root, PreludeScope, extraParameters: null);

            var sortedIdentifierOccurrences = _identifierOccurrences
                .OrderBy(static occurrence => occurrence.Span, SpanComparer.Instance)
                .ToList();
            var sortedDeclarations = _declarations
                .OrderBy(static declaration => declaration.Span, SpanComparer.Instance)
                .ToList();
            var sortedIdentifierResolutions = _identifierResolutions
                .OrderBy(static resolution => resolution.Occurrence.Span, SpanComparer.Instance)
                .ToList();
            var sortedPropertyInfos = _propertyInfos
                .OrderBy(static property => property.Declaration?.Span, SpanComparer.Instance)
                .ThenBy(static property => property.Name, StringComparer.Ordinal)
                .ToList();

            return new SemanticModel(
                root,
                sortedIdentifierOccurrences,
                sortedDeclarations,
                sortedIdentifierResolutions,
                sortedPropertyInfos,
                new Dictionary<DeclarationOccurrence, PropertyInfo>(_propertyInfoByDeclaration));
        }

        private void VisitAlgorithm(
            Algorithm algorithm,
            ScopeFrame parentScope,
            IReadOnlyDictionary<string, SymbolDefinition>? extraParameters)
        {
            switch (algorithm)
            {
                case Algorithm.User user:
                    VisitUserAlgorithm(user, parentScope, extraParameters);
                    break;
                case Algorithm.Conditional conditional:
                    VisitConditionalAlgorithm(conditional, parentScope);
                    break;
                case Algorithm.Builtin:
                    break;
            }
        }

        private void VisitUserAlgorithm(
            Algorithm.User algorithm,
            ScopeFrame parentScope,
            IReadOnlyDictionary<string, SymbolDefinition>? extraParameters)
        {
            var scope = CreateScope(algorithm, parentScope, extraParameters);

            foreach (var open in algorithm.Opens)
                VisitOpenExpression(open, scope);

            foreach (var property in algorithm.Properties)
                VisitAlgorithm(property.Value, scope, extraParameters: null);

            foreach (var expr in algorithm.Output)
                VisitExpr(expr, scope);
        }

        private void VisitConditionalAlgorithm(Algorithm.Conditional algorithm, ScopeFrame parentScope)
        {
            var scope = CreateScope(algorithm, parentScope, extraParameters: null);

            foreach (var open in algorithm.Opens)
                VisitOpenExpression(open, scope);

            foreach (var branch in algorithm.Branches)
                VisitConditionalBranch(branch, scope);
        }

        private void VisitConditionalBranch(CondBranch branch, ScopeFrame parentScope)
        {
            var binderSymbols = CreateBinderSymbols(branch.Pattern);
            VisitAlgorithm(branch.Body, parentScope, binderSymbols);
        }

        private ScopeFrame CreateScope(
            Algorithm algorithm,
            ScopeFrame parentScope,
            IReadOnlyDictionary<string, SymbolDefinition>? extraParameters)
        {
            var propertySymbols = new Dictionary<string, SymbolDefinition>(StringComparer.Ordinal);
            foreach (var property in algorithm.Properties)
                propertySymbols[property.Name] = CreatePropertySymbol(property);

            var parameterSymbols = new Dictionary<string, SymbolDefinition>(StringComparer.Ordinal);
            if (extraParameters is not null)
            {
                foreach (var (name, symbol) in extraParameters)
                    parameterSymbols[name] = symbol;
            }

            var explicitParameters = algorithm.ExplicitParameters.ToDictionary(
                parameter => parameter.Name,
                StringComparer.Ordinal);

            foreach (var parameter in algorithm.ExplicitParameters)
            {
                if (parameterSymbols.ContainsKey(parameter.Name))
                    continue;

                parameterSymbols[parameter.Name] = CreateParameterSymbol(
                    parameter.Name,
                    SymbolKind.ExplicitParameter,
                    parameter.Span,
                    OccurrenceKind.ExplicitParameterDefinition,
                    IdentifierClassification.ExplicitParameterDefinition);
            }

            foreach (var parameterName in algorithm.Params)
            {
                if (parameterSymbols.ContainsKey(parameterName))
                    continue;

                parameterSymbols[parameterName] = explicitParameters.ContainsKey(parameterName)
                    ? CreateParameterSymbol(
                        parameterName,
                        SymbolKind.ExplicitParameter,
                        explicitParameters[parameterName].Span,
                        OccurrenceKind.ExplicitParameterDefinition,
                        IdentifierClassification.ExplicitParameterDefinition)
                    : new SymbolDefinition(parameterName, SymbolKind.ImplicitParameter, AlgorithmValue: null, Declaration: null, IsPublic: false, PropertyInfo: null);
            }

            if (algorithm.ExplicitOutputSpan is { } outputSpan)
                AddDeclaration("Output", outputSpan, OccurrenceKind.ReservedNameDefinition, IdentifierClassification.ReservedName);

            return new ScopeFrame(parentScope, propertySymbols, parameterSymbols, algorithm.Opens);
        }

        private SymbolDefinition CreatePropertySymbol(Property property)
        {
            if (_propertySymbolCache.TryGetValue(property, out var cached))
                return cached;

            var declarations = new List<DeclarationOccurrence>(property.DeclarationSpans.Count);
            foreach (var span in property.DeclarationSpans)
                declarations.Add(CreateDeclarationOccurrence(property.Name, span, OccurrenceKind.PropertyDefinition));

            var canonicalDeclaration = declarations.FirstOrDefault();
            var propertyInfo = CreatePropertyInfo(
                property.Name,
                SymbolKind.Property,
                property.Value,
                canonicalDeclaration,
                property.IsPublic,
                property.Exposure,
                property.DeclarationSpans);

            foreach (var declaration in declarations)
            {
                _propertyInfoByDeclaration[declaration] = propertyInfo;
                AddResolution(declaration, IdentifierClassification.PropertyDefinition, declaration, propertyInfo);
            }

            TrackPropertyInfo(propertyInfo);

            var symbol = new SymbolDefinition(
                property.Name,
                SymbolKind.Property,
                property.Value,
                canonicalDeclaration,
                property.IsPublic,
                propertyInfo);
            _propertySymbolCache[property] = symbol;
            return symbol;
        }

        private SymbolDefinition CreateLookupPropertySymbol(Algorithm owner, Property property)
        {
            if (_propertySymbolCache.TryGetValue(property, out var cached))
                return cached;

            if (!ReferenceEquals(owner, MathAlgorithm))
                return CreatePropertySymbol(property);

            var symbol = CreateBuiltinSymbol(property.Name, property.Value, property.IsPublic);
            _propertySymbolCache[property] = symbol;
            return symbol;
        }

        private static SymbolDefinition CreateBuiltinSymbol(string name, Algorithm? algorithm, bool isPublic)
            => new(
                name,
                SymbolKind.Builtin,
                algorithm,
                Declaration: null,
                isPublic,
                CreatePropertyInfo(
                    name,
                    SymbolKind.Builtin,
                    algorithm,
                    declaration: null,
                    isPublic,
                    PropertyExposure.Exported,
                    declarationSpans: null));

        private SymbolDefinition CreateParameterSymbol(
            string name,
            SymbolKind kind,
            SourceSpan? span,
            OccurrenceKind occurrenceKind,
            IdentifierClassification definitionClassification)
        {
            var declaration = span is null ? null : AddDeclaration(name, span, occurrenceKind, definitionClassification);
            return new SymbolDefinition(name, kind, AlgorithmValue: null, Declaration: declaration, IsPublic: false, PropertyInfo: null);
        }

        private IReadOnlyDictionary<string, SymbolDefinition> CreateBinderSymbols(Pattern pattern)
        {
            var symbols = new Dictionary<string, SymbolDefinition>(StringComparer.Ordinal);

            void Visit(Pattern current)
            {
                switch (current)
                {
                    case Pattern.Bind bind:
                        if (!symbols.ContainsKey(bind.Name))
                        {
                            symbols[bind.Name] = CreateParameterSymbol(
                                bind.Name,
                                SymbolKind.ConditionalBinder,
                                bind.NameSpan,
                                OccurrenceKind.ConditionalBinderDefinition,
                                IdentifierClassification.ConditionalBinderDefinition);
                        }
                        break;

                    case Pattern.Group group:
                        foreach (var item in group.Items)
                            Visit(item);
                        break;
                }
            }

            Visit(pattern);
            return symbols;
        }

        private void VisitOpenExpression(Expr expr, ScopeFrame scope)
        {
            switch (expr)
            {
                case Expr.Resolve resolve:
                {
                    var symbol = ResolveOpenHead(scope, resolve.Name);
                    var isValidOpenTarget = symbol is not null && !IsIllegalOpenTarget(symbol);
                    AddReference(
                        resolve.Name,
                        resolve.Span,
                        OccurrenceKind.OpenTargetReference,
                        isValidOpenTarget
                            ? IdentifierClassification.OpenTarget
                            : IdentifierClassification.Unresolved,
                        isValidOpenTarget ? symbol?.Declaration : null,
                        isValidOpenTarget ? symbol?.PropertyInfo : null);
                    break;
                }

                case Expr.DotCall dotCall when dotCall.Args is null:
                {
                    var targetAlgorithm = VisitOpenExpressionAndResolve(dotCall.Target, scope);
                    if (dotCall.Name == "Output")
                    {
                        AddReference(
                            dotCall.Name,
                            dotCall.MemberSpan,
                            OccurrenceKind.OpenTargetMemberReference,
                            IdentifierClassification.ReservedName,
                            declaration: null,
                            propertyInfo: null);
                        break;
                    }

                    var memberSymbol = targetAlgorithm is null ? null : TryResolvePublicProperty(targetAlgorithm, dotCall.Name);
                    var isValidOpenTarget = memberSymbol is not null && !IsIllegalOpenTarget(memberSymbol);
                    AddReference(
                        dotCall.Name,
                        dotCall.MemberSpan,
                        OccurrenceKind.OpenTargetMemberReference,
                        isValidOpenTarget
                            ? IdentifierClassification.OpenTarget
                            : IdentifierClassification.Unresolved,
                        isValidOpenTarget ? memberSymbol?.Declaration : null,
                        isValidOpenTarget ? memberSymbol?.PropertyInfo : null);
                    break;
                }

                case Expr.Combine(var left, var right):
                    VisitOpenExpression(left, scope);
                    VisitOpenExpression(right, scope);
                    break;

                case Expr.Block(var algorithm):
                    VisitAlgorithm(algorithm, scope, extraParameters: null);
                    break;

                default:
                    VisitExpr(expr, scope);
                    break;
            }
        }

        private Algorithm? VisitOpenExpressionAndResolve(Expr expr, ScopeFrame scope)
        {
            VisitOpenExpression(expr, scope);
            return TryResolveOpenExpression(expr, scope);
        }

        private void VisitExpr(Expr expr, ScopeFrame scope)
        {
            switch (expr)
            {
                case Expr.Resolve resolve:
                {
                    var symbol = ResolveLexicalProperty(scope, resolve.Name);
                    AddReference(
                        resolve.Name,
                        resolve.Span,
                        OccurrenceKind.ResolveReference,
                        ClassifyReferenceSymbol(symbol),
                        symbol?.Declaration,
                        symbol?.PropertyInfo);
                    break;
                }

                case Expr.Param parameter:
                {
                    var symbol = ResolveParameter(scope, parameter.Name);
                    AddReference(
                        parameter.Name,
                        parameter.Span,
                        OccurrenceKind.ParameterReference,
                        ClassifyParameterSymbol(symbol),
                        symbol?.Declaration,
                        propertyInfo: null);
                    break;
                }

                case Expr.Unary(_, var operand):
                    VisitExpr(operand, scope);
                    break;

                case Expr.Binary(_, var left, var right):
                    VisitExpr(left, scope);
                    VisitExpr(right, scope);
                    break;

                case Expr.Index(var target, var selector):
                    VisitExpr(target, scope);
                    VisitExpr(selector, scope);
                    break;

                case Expr.Combine(var left, var right):
                    VisitExpr(left, scope);
                    VisitExpr(right, scope);
                    break;

                case Expr.DotCall dotCall:
                    VisitExpr(dotCall.Target, scope);
                    var (classification, declaration, propertyInfo) = ResolveDotMember(dotCall, scope);
                    AddReference(
                        dotCall.Name,
                        dotCall.MemberSpan,
                        OccurrenceKind.DotMemberReference,
                        classification,
                        declaration,
                        propertyInfo);
                    if (dotCall.Args is not null)
                        VisitAlgorithm(dotCall.Args, scope, extraParameters: null);
                    break;

                case Expr.Grace(var inner, _):
                    VisitExpr(inner, scope);
                    break;

                case Expr.Block(var algorithm):
                    VisitAlgorithm(algorithm, scope, extraParameters: null);
                    break;

                case Expr.Call(var function, var args):
                    VisitExpr(function, scope);
                    VisitAlgorithm(args, scope, extraParameters: null);
                    break;

                case Expr.NativeCall:
                case Expr.Num:
                case Expr.StringLiteral:
                    break;
            }
        }

        private (IdentifierClassification Classification, DeclarationOccurrence? Declaration, PropertyInfo? PropertyInfo) ResolveDotMember(Expr.DotCall dotCall, ScopeFrame scope)
        {
            if (dotCall.Name == "Output")
                return (IdentifierClassification.ReservedName, null, null);

            if (dotCall.Name == "string")
                return (IdentifierClassification.Builtin, null, StringIntrinsicSymbol.PropertyInfo);

            if (TryResolveBuiltinFallbackOnParameterReceiver(dotCall.Target, dotCall.Name, scope) is { } parameterBuiltin)
                return (ClassifyReferenceSymbol(parameterBuiltin), parameterBuiltin.Declaration, parameterBuiltin.PropertyInfo);

            var targetAlgorithm = TryResolveAlgorithmValue(dotCall.Target, scope);
            if (targetAlgorithm is not null)
            {
                if (TryResolveDeclaredProperty(targetAlgorithm, dotCall.Name) is { } declaredProperty)
                {
                    if (declaredProperty.PropertyInfo?.IsExported == true)
                        return (ClassifyReferenceSymbol(declaredProperty), declaredProperty.Declaration, declaredProperty.PropertyInfo);

                    return (IdentifierClassification.Unresolved, null, null);
                }

                if (ConditionalBranchesDefineProperty(targetAlgorithm, dotCall.Name))
                    return (IdentifierClassification.Unresolved, null, null);

                if (ResolveLexicalProperty(scope, dotCall.Name) is { } lexicalFallback)
                    return (ClassifyReferenceSymbol(lexicalFallback), lexicalFallback.Declaration, lexicalFallback.PropertyInfo);

                return (IdentifierClassification.Unresolved, null, null);
            }

            if (!AllowsExactLexicalFallback(dotCall.Target))
                return (IdentifierClassification.Unresolved, null, null);

            if (ResolveLexicalProperty(scope, dotCall.Name) is { } lexical)
                return (ClassifyReferenceSymbol(lexical), lexical.Declaration, lexical.PropertyInfo);

            return (IdentifierClassification.Unresolved, null, null);
        }

        private SymbolDefinition? ResolveLexicalProperty(ScopeFrame scope, string name)
        {
            for (var current = scope; current is not null; current = current.Parent)
            {
                if (current.Properties.TryGetValue(name, out var local))
                    return local;
            }

            return LookupOpensInChain(scope, name);
        }

        private static SymbolDefinition? ResolveParameter(ScopeFrame scope, string name)
        {
            for (var current = scope; current is not null; current = current.Parent)
            {
                if (current.Parameters.TryGetValue(name, out var parameter))
                    return parameter;
            }

            return null;
        }

        private SymbolDefinition? LookupOpensInChain(ScopeFrame scope, string name)
        {
            for (var current = scope; current is not null; current = current.Parent)
            {
                if (current.Opens.Count == 0)
                    continue;

                var hits = new List<SymbolDefinition>();
                foreach (var openExpr in current.Opens)
                {
                    var openTarget = TryResolveOpenExpression(openExpr, current);
                    if (openTarget is null)
                        continue;

                    if (TryResolvePublicProperty(openTarget, name) is { } hit)
                        hits.Add(hit);
                }

                if (hits.Count == 1)
                    return hits[0];

                if (hits.Count > 1)
                    return null;
            }

            return null;
        }

        private SymbolDefinition? ResolveOpenHead(ScopeFrame scope, string name)
        {
            for (var current = scope; current is not null; current = current.Parent)
            {
                if (current.Properties.TryGetValue(name, out var symbol))
                    return symbol;
            }

            return null;
        }

        private Algorithm? TryResolveOpenExpression(Expr expr, ScopeFrame scope)
        {
            switch (expr)
            {
                case Expr.Resolve(var name):
                {
                    var symbol = ResolveOpenHead(scope, name);
                    return symbol is not null && !IsIllegalOpenTarget(symbol)
                        ? symbol.AlgorithmValue
                        : null;
                }

                case Expr.DotCall(var target, var name, null):
                {
                    if (name == "Output")
                        return null;

                    var targetAlgorithm = TryResolveOpenExpression(target, scope);
                    var symbol = targetAlgorithm is null ? null : TryResolvePublicProperty(targetAlgorithm, name);
                    return symbol is not null && !IsIllegalOpenTarget(symbol)
                        ? symbol.AlgorithmValue
                        : null;
                }

                case Expr.Combine(var left, var right):
                {
                    var leftAlgorithm = TryResolveOpenExpression(left, scope);
                    var rightAlgorithm = TryResolveOpenExpression(right, scope);
                    return leftAlgorithm is not null && rightAlgorithm is not null
                        ? CombineAlgorithms(leftAlgorithm, rightAlgorithm)
                        : null;
                }

                case Expr.Block(var algorithm):
                    return algorithm;

                default:
                    return null;
            }
        }

        private Algorithm? TryResolveAlgorithmValue(Expr expr, ScopeFrame scope)
        {
            switch (expr)
            {
                case Expr.Resolve(var name):
                    return ResolveLexicalProperty(scope, name)?.AlgorithmValue;

                case Expr.Block(var algorithm):
                    return algorithm;

                case Expr.Combine(var left, var right):
                {
                    var leftAlgorithm = TryResolveAlgorithmValue(left, scope);
                    var rightAlgorithm = TryResolveAlgorithmValue(right, scope);
                    return leftAlgorithm is not null && rightAlgorithm is not null
                        ? CombineAlgorithms(leftAlgorithm, rightAlgorithm)
                        : null;
                }

                case Expr.DotCall dotCall:
                    return new Algorithm.User(
                        Parent: null,
                        Params: [],
                        Opens: [],
                        Properties: [],
                        Output: [dotCall]);

                default:
                    return null;
            }
        }

        private SymbolDefinition? TryResolveBuiltinFallbackOnParameterReceiver(Expr expr, string name, ScopeFrame scope)
        {
            if (expr is not Expr.Param)
                return null;

            var lexical = ResolveLexicalProperty(scope, name);
            return lexical is { Kind: SymbolKind.Builtin, AlgorithmValue: Algorithm.Builtin }
                ? lexical
                : null;
        }

        private SymbolDefinition? TryResolveDeclaredProperty(Algorithm algorithm, string name)
        {
            var property = algorithm.Properties.FirstOrDefault(p => p.Name == name);
            return property is null ? null : CreateLookupPropertySymbol(algorithm, property);
        }

        private SymbolDefinition? TryResolvePublicProperty(Algorithm algorithm, string name)
        {
            var property = algorithm.Properties.FirstOrDefault(
                p => p.Name == name
                    && p.IsPublic
                    && p.Exposure == PropertyExposure.Exported);
            return property is null ? null : CreateLookupPropertySymbol(algorithm, property);
        }

        private static bool ConditionalBranchesDefineProperty(Algorithm algorithm, string name)
        {
            if (algorithm is not Algorithm.Conditional conditional)
                return false;

            foreach (var branch in conditional.Branches)
            {
                if (branch.Body.Properties.Any(property => property.Name == name))
                    return true;
            }

            return false;
        }

        private static bool AllowsExactLexicalFallback(Expr expr)
            => expr is Expr.Num
                or Expr.StringLiteral
                or Expr.Unary
                or Expr.Binary
                or Expr.Index
                or Expr.Call
                or Expr.NativeCall
                or Expr.DotCall;

        private static bool IsIllegalOpenTarget(SymbolDefinition symbol)
            => symbol.AlgorithmValue is Algorithm.Builtin;

        private static IdentifierClassification ClassifyReferenceSymbol(SymbolDefinition? symbol)
            => symbol?.Kind switch
            {
                SymbolKind.Property => IdentifierClassification.PropertyReference,
                SymbolKind.Builtin => IdentifierClassification.Builtin,
                SymbolKind.ExplicitParameter => IdentifierClassification.ExplicitParameterReference,
                SymbolKind.ImplicitParameter => IdentifierClassification.ImplicitParameterReference,
                SymbolKind.ConditionalBinder => IdentifierClassification.ConditionalBinderReference,
                _ => IdentifierClassification.Unresolved,
            };

        private static IdentifierClassification ClassifyParameterSymbol(SymbolDefinition? symbol)
            => symbol?.Kind switch
            {
                SymbolKind.ExplicitParameter => IdentifierClassification.ExplicitParameterReference,
                SymbolKind.ImplicitParameter => IdentifierClassification.ImplicitParameterReference,
                SymbolKind.ConditionalBinder => IdentifierClassification.ConditionalBinderReference,
                _ => IdentifierClassification.Unresolved,
            };

        private static PropertyInfo CreatePropertyInfo(
            string name,
            SymbolKind kind,
            Algorithm? algorithm,
            DeclarationOccurrence? declaration,
            bool isPublic,
            PropertyExposure exposure,
            IReadOnlyList<SourceSpan>? declarationSpans)
        {
            if (kind == SymbolKind.Builtin || algorithm is Algorithm.Builtin)
            {
                return new PropertyInfo(
                    name,
                    declaration,
                    PropertyShape.Builtin,
                    isPublic,
                    exposure,
                    CreateBuiltinParameters(name, algorithm),
                    []);
            }

            return algorithm switch
            {
                Algorithm.User user => new PropertyInfo(
                    name,
                    declaration,
                    PropertyShape.Ordinary,
                    isPublic,
                    exposure,
                    CreateOrdinaryParameters(user),
                    []),
                Algorithm.Conditional conditional => new PropertyInfo(
                    name,
                    declaration,
                    PropertyShape.Conditional,
                    isPublic,
                    exposure,
                    [],
                    CreateConditionalBranches(name, conditional, declarationSpans)),
                _ => new PropertyInfo(name, declaration, PropertyShape.Ordinary, isPublic, exposure, [], []),
            };
        }

        private static IReadOnlyList<PropertyParameterInfo> CreateOrdinaryParameters(Algorithm.User algorithm)
        {
            var explicitParameters = algorithm.ExplicitParameters.ToDictionary(
                parameter => parameter.Name,
                StringComparer.Ordinal);
            var parameters = new List<PropertyParameterInfo>(algorithm.Params.Count);

            foreach (var parameterName in algorithm.Params)
            {
                if (explicitParameters.TryGetValue(parameterName, out var explicitParameter))
                {
                    parameters.Add(new PropertyParameterInfo(
                        parameterName,
                        PropertyParameterKind.Explicit,
                        explicitParameter.Span));
                    continue;
                }

                parameters.Add(new PropertyParameterInfo(
                    parameterName,
                    PropertyParameterKind.Implicit,
                    Span: null));
            }

            return parameters;
        }

        private static IReadOnlyList<PropertyParameterInfo> CreateBuiltinParameters(string name, Algorithm? algorithm)
        {
            if (algorithm is Algorithm.User user)
            {
                return user.Params
                    .Select(parameterName => new PropertyParameterInfo(
                        parameterName,
                        PropertyParameterKind.Explicit,
                        Span: null))
                    .ToList();
            }

            string[] parameterNames = name switch
            {
                "if" => ["condition", "whenTrue", "whenFalse"],
                "while" => ["step", "initialState"],
                "repeat" => ["step", "count", "initialState"],
                "atoms" => ["value"],
                "range" => ["start", "stop"],
                "filter" => ["items...", "predicate"],
                "map" => ["items...", "transform"],
                "order" => ["items..."],
                "orderDesc" => ["items..."],
                "count" => ["items..."],
                "contains" => ["items...", "item"],
                "first" => ["items..."],
                "last" => ["items..."],
                "distinct" => ["items..."],
                "take" => ["items...", "count"],
                "skip" => ["items...", "count"],
                "min" => ["items..."],
                "max" => ["items..."],
                "sum" => ["items..."],
                "avg" => ["items..."],
                "reduce" => ["items...", "step", "initial"],
                _ => [],
            };

            return parameterNames
                .Select(parameterName => new PropertyParameterInfo(
                    parameterName,
                    PropertyParameterKind.Explicit,
                    Span: null))
                .ToList();
        }

        private static IReadOnlyList<ConditionalBranchInfo> CreateConditionalBranches(
            string name,
            Algorithm.Conditional algorithm,
            IReadOnlyList<SourceSpan>? declarationSpans)
        {
            var branches = new List<ConditionalBranchInfo>(algorithm.Branches.Count);

            for (var i = 0; i < algorithm.Branches.Count; i++)
            {
                var branch = algorithm.Branches[i];
                var headSpan = declarationSpans is not null && i < declarationSpans.Count
                    ? declarationSpans[i]
                    : null;
                branches.Add(new ConditionalBranchInfo(
                    ConditionalBranchHeadFormatter.Format(name, branch.Pattern),
                    headSpan,
                    branch.Pattern.BoundNames()));
            }

            return branches;
        }

        private void TrackPropertyInfo(PropertyInfo? propertyInfo)
        {
            if (propertyInfo is null || !_seenPropertyInfos.Add(propertyInfo))
                return;

            _propertyInfos.Add(propertyInfo);
        }

        private DeclarationOccurrence CreateDeclarationOccurrence(string name, SourceSpan span, OccurrenceKind kind)
        {
            var declaration = new DeclarationOccurrence(name, span, kind);
            _declarations.Add(declaration);
            return declaration;
        }

        private void AddResolution(
            IdentifierOccurrence occurrence,
            IdentifierClassification classification,
            DeclarationOccurrence? declaration,
            PropertyInfo? propertyInfo)
        {
            TrackPropertyInfo(propertyInfo);
            _identifierResolutions.Add(new IdentifierResolution(occurrence, classification, declaration, propertyInfo));
        }

        private void AddReference(
            string name,
            SourceSpan? span,
            OccurrenceKind kind,
            IdentifierClassification classification,
            DeclarationOccurrence? declaration,
            PropertyInfo? propertyInfo)
        {
            // SemanticModel is source-backed: if there is no real identifier token
            // in source, there is no identifier occurrence to record.
            if (span is null)
                return;

            var occurrence = new IdentifierOccurrence(name, span, kind);
            _identifierOccurrences.Add(occurrence);
            AddResolution(occurrence, classification, declaration, propertyInfo);
        }

        private DeclarationOccurrence AddDeclaration(
            string name,
            SourceSpan span,
            OccurrenceKind kind,
            IdentifierClassification classification,
            PropertyInfo? propertyInfo = null)
        {
            var declaration = CreateDeclarationOccurrence(name, span, kind);
            if (propertyInfo is not null)
                _propertyInfoByDeclaration[declaration] = propertyInfo;
            AddResolution(declaration, classification, declaration, propertyInfo);
            return declaration;
        }

        private static Algorithm CombineAlgorithms(Algorithm left, Algorithm right)
            => new Algorithm.User(
                Parent: null,
                Params: left.Params.Concat(right.Params).ToList(),
                Opens: left.Opens.Concat(right.Opens).ToList(),
                Properties: left.Properties.Concat(right.Properties).ToList(),
                Output: [new Expr.Block(left), new Expr.Block(right)]);

        private static ScopeFrame CreatePreludeScope()
        {
            var properties = new Dictionary<string, SymbolDefinition>(StringComparer.Ordinal);

            foreach (var builtin in Enum.GetValues<BuiltinId>())
            {
                var name = builtin.ToString();
                var algorithm = new Algorithm.Builtin(builtin);
                properties[name] = CreateBuiltinSymbol(name, algorithm, isPublic: true);
            }

            properties["load"] = CreateBuiltinSymbol(
                "load",
                new Algorithm.User(Parent: null, Params: ["url"], Opens: [], Properties: [], Output: []),
                isPublic: true);

            properties["Math"] = CreateBuiltinSymbol(
                "Math",
                MathAlgorithm,
                isPublic: true);

            return new ScopeFrame(parent: null, properties, parameters: new Dictionary<string, SymbolDefinition>(StringComparer.Ordinal), opens: []);
        }

        private static Algorithm.User CreateMathAlgorithm()
        {
            static Property Constant(string name)
                => new(name, new Algorithm.User(Parent: null, Params: [], Opens: [], Properties: [], Output: []), IsPublic: true);

            static Property UnaryFunction(string name)
                => new(name, new Algorithm.User(Parent: null, Params: ["x"], Opens: [], Properties: [], Output: []), IsPublic: true);

            static Property BinaryFunction(string name)
                => new(name, new Algorithm.User(Parent: null, Params: ["x", "y"], Opens: [], Properties: [], Output: []), IsPublic: true);

            return new Algorithm.User(
                Parent: null,
                Params: [],
                Opens: [],
                Properties:
                [
                    Constant("Pi"),
                    Constant("E"),
                    UnaryFunction("Abs"),
                    UnaryFunction("Ceil"),
                    UnaryFunction("Floor"),
                    UnaryFunction("Round"),
                    UnaryFunction("Sign"),
                    UnaryFunction("Sqrt"),
                    UnaryFunction("Ln"),
                    UnaryFunction("Lg"),
                    UnaryFunction("Sin"),
                    UnaryFunction("Asin"),
                    UnaryFunction("Cos"),
                    UnaryFunction("Acos"),
                    UnaryFunction("Tan"),
                    UnaryFunction("Atan"),
                    BinaryFunction("Pow"),
                    BinaryFunction("Log"),
                ],
                Output: []);
        }
    }

    private enum SymbolKind
    {
        Property,
        ExplicitParameter,
        ImplicitParameter,
        ConditionalBinder,
        Builtin,
    }

    private sealed record SymbolDefinition(
        string Name,
        SymbolKind Kind,
        Algorithm? AlgorithmValue,
        DeclarationOccurrence? Declaration,
        bool IsPublic,
        PropertyInfo? PropertyInfo);

    private sealed class ScopeFrame
    {
        public ScopeFrame(
            ScopeFrame? parent,
            IReadOnlyDictionary<string, SymbolDefinition> properties,
            IReadOnlyDictionary<string, SymbolDefinition> parameters,
            IReadOnlyList<Expr> opens)
        {
            Parent = parent;
            Properties = properties;
            Parameters = parameters;
            Opens = opens;
        }

        public ScopeFrame? Parent { get; }

        public IReadOnlyDictionary<string, SymbolDefinition> Properties { get; }

        public IReadOnlyDictionary<string, SymbolDefinition> Parameters { get; }

        public IReadOnlyList<Expr> Opens { get; }
    }

    private sealed class SpanComparer : IComparer<SourceSpan?>
    {
        public static SpanComparer Instance { get; } = new();

        public int Compare(SourceSpan? x, SourceSpan? y)
        {
            if (ReferenceEquals(x, y))
                return 0;
            if (x is null)
                return 1;
            if (y is null)
                return -1;

            var byStartLine = x.StartLineNumber.CompareTo(y.StartLineNumber);
            if (byStartLine != 0)
                return byStartLine;

            var byStartColumn = x.StartColumn.CompareTo(y.StartColumn);
            if (byStartColumn != 0)
                return byStartColumn;

            var byEndLine = x.EndLineNumber.CompareTo(y.EndLineNumber);
            if (byEndLine != 0)
                return byEndLine;

            return x.EndColumn.CompareTo(y.EndColumn);
        }
    }
}