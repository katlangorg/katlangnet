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
    /// </summary>
    public static SemanticModel Build(Algorithm root)
        => new Builder().Build(root);

    /// <summary>
    /// Builds a semantic model from a parse result.
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

    private sealed class Builder
    {
        private static readonly Algorithm.User MathAlgorithm = CreateMathAlgorithm();
        private static readonly ScopeFrame PreludeScope = CreatePreludeScope();

        private readonly List<IdentifierOccurrence> _identifierOccurrences = [];
        private readonly List<DeclarationOccurrence> _declarations = [];
        private readonly List<IdentifierResolution> _identifierResolutions = [];
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

            return new SemanticModel(root, sortedIdentifierOccurrences, sortedDeclarations, sortedIdentifierResolutions);
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
                    : new SymbolDefinition(parameterName, SymbolKind.ImplicitParameter, AlgorithmValue: null, Declaration: null, IsPublic: false);
            }

            if (algorithm.ExplicitOutputSpan is { } outputSpan)
                AddDeclaration("Output", outputSpan, OccurrenceKind.ReservedNameDefinition, IdentifierClassification.ReservedName);

            return new ScopeFrame(parentScope, propertySymbols, parameterSymbols, algorithm.Opens);
        }

        private SymbolDefinition CreatePropertySymbol(Property property)
        {
            if (_propertySymbolCache.TryGetValue(property, out var cached))
                return cached;

            DeclarationOccurrence? canonicalDeclaration = null;
            foreach (var span in property.DeclarationSpans)
            {
                var declaration = AddDeclaration(
                    property.Name,
                    span,
                    OccurrenceKind.PropertyDefinition,
                    IdentifierClassification.PropertyDefinition);
                canonicalDeclaration ??= declaration;
            }

            var symbol = new SymbolDefinition(
                property.Name,
                SymbolKind.Property,
                property.Value,
                canonicalDeclaration,
                property.IsPublic);
            _propertySymbolCache[property] = symbol;
            return symbol;
        }

        private SymbolDefinition CreateLookupPropertySymbol(Algorithm owner, Property property)
        {
            if (_propertySymbolCache.TryGetValue(property, out var cached))
                return cached;

            if (!ReferenceEquals(owner, MathAlgorithm))
                return CreatePropertySymbol(property);

            return new SymbolDefinition(
                property.Name,
                SymbolKind.Builtin,
                property.Value,
                Declaration: null,
                property.IsPublic);
        }

        private SymbolDefinition CreateParameterSymbol(
            string name,
            SymbolKind kind,
            SourceSpan? span,
            OccurrenceKind occurrenceKind,
            IdentifierClassification definitionClassification)
        {
            var declaration = span is null ? null : AddDeclaration(name, span, occurrenceKind, definitionClassification);
            return new SymbolDefinition(name, kind, AlgorithmValue: null, Declaration: declaration, IsPublic: false);
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
                    AddReference(
                        resolve.Name,
                        resolve.Span,
                        OccurrenceKind.OpenTargetReference,
                        ResolveOpenHead(scope, resolve.Name) is { } symbol && !IsIllegalOpenTarget(symbol)
                            ? IdentifierClassification.OpenTarget
                            : IdentifierClassification.Unresolved,
                        ResolveOpenHead(scope, resolve.Name)?.Declaration);
                    break;

                case Expr.DotCall dotCall when dotCall.Args is null:
                {
                    var targetAlgorithm = VisitOpenExpressionAndResolve(dotCall.Target, scope);
                    var memberSymbol = targetAlgorithm is null ? null : TryResolvePublicProperty(targetAlgorithm, dotCall.Name);
                    AddReference(
                        dotCall.Name,
                        dotCall.MemberSpan,
                        OccurrenceKind.OpenTargetMemberReference,
                        memberSymbol is not null && !IsIllegalOpenTarget(memberSymbol)
                            ? IdentifierClassification.OpenTarget
                            : IdentifierClassification.Unresolved,
                        memberSymbol?.Declaration);
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
                        symbol?.Declaration);
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
                        symbol?.Declaration);
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
                    var (classification, declaration) = ResolveDotMember(dotCall, scope);
                    AddReference(dotCall.Name, dotCall.MemberSpan, OccurrenceKind.DotMemberReference, classification, declaration);
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

        private (IdentifierClassification Classification, DeclarationOccurrence? Declaration) ResolveDotMember(Expr.DotCall dotCall, ScopeFrame scope)
        {
            if (dotCall.Name == "string")
                return (IdentifierClassification.Builtin, null);

            var targetAlgorithm = TryResolveAlgorithmValue(dotCall.Target, scope);
            if (targetAlgorithm is not null)
            {
                if (dotCall.Name == "length")
                    return (IdentifierClassification.Builtin, null);

                if (TryResolveAnyProperty(targetAlgorithm, dotCall.Name) is { } structuralProperty)
                    return (ClassifyReferenceSymbol(structuralProperty), structuralProperty.Declaration);

                if (ResolveLexicalProperty(scope, dotCall.Name) is { } lexicalFallback)
                    return (ClassifyReferenceSymbol(lexicalFallback), lexicalFallback.Declaration);

                if (IsUnverifiedLoadedExternalReceiver(targetAlgorithm, scope))
                    return (IdentifierClassification.LoadedExternalMemberReference, null);

                return (IdentifierClassification.Unresolved, null);
            }

            if (!AllowsExactLexicalFallback(dotCall.Target))
                return (IdentifierClassification.Unresolved, null);

            if (ResolveLexicalProperty(scope, dotCall.Name) is { } lexical)
                return (ClassifyReferenceSymbol(lexical), lexical.Declaration);

            return (IdentifierClassification.Unresolved, null);
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

        // Detects the conservative local case where a receiver is just a proxy for
        // load(...) and this semantic pass has not verified remote exports.
        private bool IsUnverifiedLoadedExternalReceiver(Algorithm algorithm, ScopeFrame scope)
            => IsUnverifiedLoadedExternalAlgorithm(algorithm, scope, new HashSet<Algorithm>(ReferenceEqualityComparer.Instance));

        private bool IsUnverifiedLoadedExternalAlgorithm(
            Algorithm algorithm,
            ScopeFrame scope,
            HashSet<Algorithm> visited)
        {
            if (!visited.Add(algorithm))
                return false;

            if (algorithm is not Algorithm.User user)
                return false;

            if (user.Params.Count != 0 || user.Opens.Count != 0 || user.Properties.Count != 0 || user.Output.Count != 1)
                return false;

            return user.Output[0] switch
            {
                Expr.Call(Expr.Resolve(var name), _) when name == "load" && IsBuiltinLoadName(scope, name) => true,
                Expr.Resolve(var name) when ResolveLexicalProperty(scope, name) is
                    { Kind: SymbolKind.Property, AlgorithmValue: { } nextAlgorithm } =>
                        IsUnverifiedLoadedExternalAlgorithm(nextAlgorithm, scope, visited),
                Expr.Block(var innerAlgorithm) => IsUnverifiedLoadedExternalAlgorithm(innerAlgorithm, scope, visited),
                _ => false,
            };
        }

        private bool IsBuiltinLoadName(ScopeFrame scope, string name)
            => ResolveLexicalProperty(scope, name)?.Kind == SymbolKind.Builtin;

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

        private SymbolDefinition? TryResolveAnyProperty(Algorithm algorithm, string name)
        {
            var property = algorithm.Properties.FirstOrDefault(p => p.Name == name);
            return property is null ? null : CreateLookupPropertySymbol(algorithm, property);
        }

        private SymbolDefinition? TryResolvePublicProperty(Algorithm algorithm, string name)
        {
            var property = algorithm.Properties.FirstOrDefault(p => p.Name == name && p.IsPublic);
            return property is null ? null : CreateLookupPropertySymbol(algorithm, property);
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

        private void AddReference(
            string name,
            SourceSpan? span,
            OccurrenceKind kind,
            IdentifierClassification classification,
            DeclarationOccurrence? declaration)
        {
            if (span is null)
                return;

            var occurrence = new IdentifierOccurrence(name, span, kind);
            _identifierOccurrences.Add(occurrence);
            _identifierResolutions.Add(new IdentifierResolution(occurrence, classification, declaration));
        }

        private DeclarationOccurrence AddDeclaration(
            string name,
            SourceSpan span,
            OccurrenceKind kind,
            IdentifierClassification classification)
        {
            var declaration = new DeclarationOccurrence(name, span, kind);
            _declarations.Add(declaration);
            _identifierResolutions.Add(new IdentifierResolution(declaration, classification, declaration));
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
                properties[name] = new SymbolDefinition(name, SymbolKind.Builtin, algorithm, Declaration: null, IsPublic: true);
            }

            properties["load"] = new SymbolDefinition(
                "load",
                SymbolKind.Builtin,
                new Algorithm.User(Parent: null, Params: ["url"], Opens: [], Properties: [], Output: []),
                Declaration: null,
                IsPublic: true);

            properties["Math"] = new SymbolDefinition(
                "Math",
                SymbolKind.Builtin,
                MathAlgorithm,
                Declaration: null,
                IsPublic: true);

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
        bool IsPublic);

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

    private sealed class SpanComparer : IComparer<SourceSpan>
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