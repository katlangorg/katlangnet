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
    /// Builds a semantic model from an elaborated KatLang root algorithm.
    /// Throws if unresolved <c>load</c> syntax reaches semantic modeling, and throws
    /// <see cref="ArgumentException"/> for a structurally unsafe preconstructed root
    /// (structural AST depth beyond the front-end structural gate, or a cyclic node
    /// graph) — checked non-recursively before any recursive walk, so an unsafe
    /// host-built tree cannot overflow the CLR stack. Roots from
    /// <see cref="Parser.Parse(string)"/> always pass.
    /// </summary>
    public static SemanticModel Build(Algorithm root)
        => BuildElaborated(root);

    /// <summary>
    /// Builds a semantic model from a parse result returned by the public
    /// front-end compatibility wrapper.
    /// </summary>
    public static SemanticModel Build(ParseResult parseResult)
        => BuildElaborated(parseResult.Root);

    internal static SemanticModel Build(SyntaxParseResult syntaxParseResult)
        => BuildElaborated(syntaxParseResult.Root);

    internal static SemanticModel Build(FrontEndResult frontEndResult)
        => BuildElaborated(frontEndResult.ElaboratedRoot);

    private static SemanticModel BuildElaborated(Algorithm elaboratedRoot)
    {
        // Semantic modeling walks the tree recursively, and the public Build overloads
        // accept preconstructed (host-built) roots, so the same non-recursive structural
        // preflight that protects the evaluator entry points must run before any
        // recursive walk here — including the load-guard walk below. Roots produced by
        // Parser.Parse are already within the hard ceiling and pass unchanged.
        // The builder's own recursive walk measures in the fat-frame class (building a
        // 640-node spine overflows a 512 KiB thread; a 300-node one completes within
        // it), so semantic modeling shares the evaluation/elaboration structural
        // ceiling. Roots from Parser.Parse are already elaboration-gated to the same
        // bound and pass unchanged.
        if (AstStructuralPreflight.Check(
                elaboratedRoot,
                EvaluationLimits.MaxSupportedAstDepth,
                AstConsumerProfile.FullyRecursive) is { } rejection)
        {
            throw new ArgumentException(
                rejection.Kind == AstStructuralViolation.CycleDetected
                    ? "Semantic model building requires an acyclic AST: the supplied root reaches itself again through its own children."
                    : "Semantic model building requires a structurally safe AST: the supplied root exceeds the structural AST depth limit of "
                        + $"{EvaluationLimits.MaxSupportedAstDepth} nodes, which protects the host process from stack overflow.",
                nameof(elaboratedRoot));
        }

        LoadElaborationGuard.ThrowIfUnresolvedLoad(elaboratedRoot, "Semantic model building");
        return new Builder().Build(elaboratedRoot);
    }

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
        private static readonly Algorithm.User MathAlgorithm = BuiltinRegistry.CreateMathAlgorithm(MathAlgorithmFlavor.SignatureOnly);
        private static readonly Algorithm.User PreludeAlgorithm = BuiltinRegistry.CreateSemanticPreludeAlgorithm(MathAlgorithm);
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

            var propertyScope = ElaboratedScopeLookup.CreateScope(algorithm, parentScope.PropertyScope);

            var parameterSymbols = new Dictionary<string, SymbolDefinition>(StringComparer.Ordinal);
            if (extraParameters is not null)
            {
                foreach (var (name, symbol) in extraParameters)
                    parameterSymbols[name] = symbol;
            }

            var explicitParameterNames = new HashSet<string>(
                algorithm.ExplicitParameters.Select(static parameter => parameter.Name),
                StringComparer.Ordinal);

            foreach (var parameter in algorithm.ExplicitParameters)
            {
                if (parameterSymbols.TryGetValue(parameter.Name, out var existingParameter))
                {
                    if (existingParameter.Kind == SymbolKind.ExplicitParameter)
                    {
                        AddReference(
                            parameter.Name,
                            parameter.Span,
                            OccurrenceKind.ParameterReference,
                            IdentifierClassification.ExplicitParameterReference,
                            existingParameter.Declaration,
                            propertyInfo: null);
                    }
                    continue;
                }

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

                parameterSymbols[parameterName] = explicitParameterNames.Contains(parameterName)
                    ? CreateParameterSymbol(
                        parameterName,
                        SymbolKind.ExplicitParameter,
                        algorithm.ExplicitParameters.First(parameter => parameter.Name == parameterName).Span,
                        OccurrenceKind.ExplicitParameterDefinition,
                        IdentifierClassification.ExplicitParameterDefinition)
                    : new SymbolDefinition(parameterName, SymbolKind.ImplicitParameter, AlgorithmValue: null, Declaration: null, IsPublic: false, PropertyInfo: null);
            }

            return new ScopeFrame(parentScope, propertySymbols, parameterSymbols, propertyScope);
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

            // Synthetic properties carry no declaration spans — for example the
            // shared right-hand-side source that a deconstruction binding hoists
            // (`$deconstruct$N`). They remain available for internal lookup and
            // evaluation through the symbol cache, but must not surface as
            // user-facing semantic property metadata.
            if (property.DeclarationSpans.Count > 0)
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

            if (!ReferenceEquals(owner, MathAlgorithm) && !ReferenceEquals(owner, PreludeAlgorithm))
                return CreatePropertySymbol(property);

            var symbol = CreateBuiltinSymbol(property.Name, property.Value, property.IsPublic);
            _propertySymbolCache[property] = symbol;
            return symbol;
        }

        private static SymbolDefinition CreateBuiltinSymbol(string name, Algorithm? algorithm, bool isPublic)
        {
            var propertyInfo = CreatePropertyInfo(
                name,
                SymbolKind.Builtin,
                algorithm,
                declaration: null,
                isPublic,
                PropertyExposure.Exported,
                declarationSpans: null);

            return new SymbolDefinition(
                name,
                SymbolKind.Builtin,
                algorithm,
                Declaration: null,
                isPublic,
                propertyInfo,
                propertyInfo.WithPreferredCallStyle(PropertyCallStyle.Dot));
        }

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
                        if (symbols.TryGetValue(bind.Name, out var existingBinder))
                        {
                            AddReference(
                                bind.Name,
                                bind.NameSpan,
                                OccurrenceKind.ParameterReference,
                                IdentifierClassification.ConditionalBinderReference,
                                existingBinder.Declaration,
                                propertyInfo: null);
                        }
                        else
                        {
                            symbols[bind.Name] = CreateParameterSymbol(
                                bind.Name,
                                SymbolKind.ConditionalBinder,
                                bind.NameSpan,
                                OccurrenceKind.ConditionalBinderDefinition,
                                IdentifierClassification.ConditionalBinderDefinition);
                        }
                        break;

                    case Pattern.SequenceValue group:
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

                case Expr.SequenceSpread spread:
                    // The postfix `*` spread marker is punctuation, not an
                    // identifier: it produces no occurrence, no symbol, and no
                    // classification site. The exact marker span stays
                    // available on the AST node (SpreadMarkerSpan).
                    VisitOpenExpression(spread.Operand, scope);
                    break;

                case Expr.SequenceConstruct(var left, var right):
                    VisitOpenExpression(left, scope);
                    VisitOpenExpression(right, scope);
                    break;

                case Expr.Block(var algorithm):
                    VisitAlgorithm(algorithm, PreludeScope, extraParameters: null);
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

                case Expr.SequenceSpread spread:
                    // The postfix `*` spread marker is punctuation, not an
                    // identifier: no occurrence, symbol, or classification
                    // site is created for it (SpreadMarkerSpan carries the
                    // exact marker location on the AST node).
                    VisitExpr(spread.Operand, scope);
                    break;

                case Expr.SequenceConstruct(var left, var right):
                    VisitExpr(left, scope);
                    VisitExpr(right, scope);
                    break;

                case Expr.ListLiteral(var items):
                    foreach (var item in items)
                        VisitExpr(item, scope);
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
            if (dotCall.Name == "string")
                return (IdentifierClassification.Builtin, null, StringIntrinsicSymbol.PropertyInfo);

            if (TryResolveLexicalFallbackOnParameterReceiver(dotCall.Target, dotCall.Name, scope) is { } parameterFallback)
                return (ClassifyReferenceSymbol(parameterFallback), parameterFallback.Declaration, GetDotMemberPropertyInfo(parameterFallback));

            var targetAlgorithm = TryResolveAlgorithmValue(dotCall.Target, scope);
            if (targetAlgorithm is not null)
            {
                if (TryResolveDeclaredProperty(targetAlgorithm, dotCall.Name) is { } declaredProperty)
                {
                    if (declaredProperty.PropertyInfo?.IsExported == true)
                        return (ClassifyReferenceSymbol(declaredProperty), declaredProperty.Declaration, GetDotMemberPropertyInfo(declaredProperty));

                    return (IdentifierClassification.Unresolved, null, null);
                }

                if (ConditionalBranchesDefineProperty(targetAlgorithm, dotCall.Name))
                    return (IdentifierClassification.Unresolved, null, null);

                if (ResolveLexicalProperty(scope, dotCall.Name) is { } lexicalFallback)
                    return (ClassifyReferenceSymbol(lexicalFallback), lexicalFallback.Declaration, GetDotMemberPropertyInfo(lexicalFallback));

                return (IdentifierClassification.Unresolved, null, null);
            }

            if (!AllowsExactLexicalFallback(dotCall.Target))
                return (IdentifierClassification.Unresolved, null, null);

            if (ResolveLexicalProperty(scope, dotCall.Name) is { } lexical)
                return (ClassifyReferenceSymbol(lexical), lexical.Declaration, GetDotMemberPropertyInfo(lexical));

            return (IdentifierClassification.Unresolved, null, null);
        }

        private static PropertyInfo? GetDotMemberPropertyInfo(SymbolDefinition symbol)
            => symbol.Kind == SymbolKind.Builtin
                ? symbol.DotPropertyInfo ?? symbol.PropertyInfo
                : symbol.PropertyInfo;

        private SymbolDefinition? ResolveLexicalProperty(ScopeFrame scope, string name)
        {
            var hits = ElaboratedScopeLookup.LookupLexicalPropertyMatches(scope.PropertyScope, name);
            return hits.Count == 1
                ? CreateLookupPropertySymbol(hits[0].Owner, hits[0].Property)
                : null;
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

        private SymbolDefinition? ResolveOpenHead(ScopeFrame scope, string name)
        {
            var hit = ElaboratedScopeLookup.TryLookupDirectLexicalProperty(scope.PropertyScope, name);
            return hit is null ? null : CreateLookupPropertySymbol(hit.Value.Owner, hit.Value.Property);
        }

        private Algorithm? TryResolveOpenExpression(Expr expr, ScopeFrame scope)
            => ElaboratedScopeLookup.ResolveOpenTarget(scope.PropertyScope, expr) is { } algorithm
                && algorithm is not Algorithm.Builtin
                    ? algorithm
                    : null;

        private Algorithm? TryResolveAlgorithmValue(Expr expr, ScopeFrame scope)
        {
            switch (expr)
            {
                case Expr.Resolve(var name):
                    return ResolveLexicalProperty(scope, name)?.AlgorithmValue;

                case Expr.Block(var algorithm):
                    return algorithm;

                case Expr.SequenceSpread(var operand):
                {
                    _ = operand;
                    return null;
                }

                case Expr.SequenceConstruct(var left, var right):
                {
                    _ = left;
                    _ = right;
                    return null;
                }

                case Expr.DotCall dotCall:
                    return new Algorithm.User(
                        Parent: null,
                        Parameters: [],
                        Opens: [],
                        Properties: [],
                        Output: [dotCall]);

                default:
                    return null;
            }
        }

        private SymbolDefinition? TryResolveLexicalFallbackOnParameterReceiver(Expr expr, string name, ScopeFrame scope)
        {
            if (expr is not Expr.Param)
                return null;

            return ResolveLexicalProperty(scope, name);
        }

        private SymbolDefinition? TryResolveDeclaredProperty(Algorithm algorithm, string name)
        {
            var hit = ElaboratedScopeLookup.TryLookupProperty(algorithm, name);
            return hit is null ? null : CreateLookupPropertySymbol(hit.Value.Owner, hit.Value.Property);
        }

        private SymbolDefinition? TryResolvePublicProperty(Algorithm algorithm, string name)
        {
            var hit = ElaboratedScopeLookup.TryLookupPublicExportedProperty(algorithm, name);
            return hit is null ? null : CreateLookupPropertySymbol(hit.Value.Owner, hit.Value.Property);
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
                or Expr.DotCall
                or Expr.ListLiteral;

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
            IReadOnlyList<SourceSpan>? declarationSpans,
            PropertyCallStyle preferredCallStyle = PropertyCallStyle.Plain)
        {
            if (kind == SymbolKind.Builtin || algorithm is Algorithm.Builtin)
            {
                var signatures = CreateBuiltinSignatures(name, algorithm);
                var preferredSignature = signatures.FirstOrDefault(signature => signature.CallStyle == preferredCallStyle)
                    ?? signatures.FirstOrDefault(signature => signature.CallStyle == PropertyCallStyle.Plain);

                return new PropertyInfo(
                    name,
                    declaration,
                    PropertyShape.Builtin,
                    isPublic,
                    exposure,
                    preferredSignature?.Parameters ?? [],
                    [])
                {
                    PreferredCallStyle = preferredSignature?.CallStyle ?? PropertyCallStyle.Plain,
                    Signatures = signatures,
                };
            }

            return algorithm switch
            {
                Algorithm.User user => CreateOrdinaryPropertyInfo(name, user, declaration, isPublic, exposure),
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

        private static PropertyInfo CreateOrdinaryPropertyInfo(
            string name,
            Algorithm.User algorithm,
            DeclarationOccurrence? declaration,
            bool isPublic,
            PropertyExposure exposure)
        {
            var signature = CallableSignature.FromAlgorithm(name, algorithm);
            var parameters = CreateOrdinaryParameters(signature);
            return new PropertyInfo(
                name,
                declaration,
                PropertyShape.Ordinary,
                isPublic,
                exposure,
                parameters,
                [])
            {
                Signatures = CreateOrdinarySignatures(signature, parameters),
            };
        }

        private static IReadOnlyList<PropertyParameterInfo> CreateOrdinaryParameters(CallableSignature signature)
        {
            var parameters = new List<PropertyParameterInfo>(signature.Parameters.Count);

            foreach (var parameter in signature.Parameters)
            {
                parameters.Add(new PropertyParameterInfo(
                    parameter.Name,
                    ToPropertyParameterKind(parameter.Source),
                    GetSourceSpan(parameter))
                {
                    IsCollecting = parameter.Kind == ParameterKind.Collecting,
                });
            }

            return parameters;
        }

        private static IReadOnlyList<PropertySignatureInfo> CreateOrdinarySignatures(
            CallableSignature signature,
            IReadOnlyList<PropertyParameterInfo> flatParameters)
        {
            if (signature.ParameterPatterns.Count == 0)
                return [];

            var bindingPlan = CallableBindingPlan.FromSignature(signature);
            var useFlatParameters = bindingPlan.TryGetFlatFixedLayout(out _)
                || bindingPlan.TryGetFlatCollectingLayout(out _, out _, out _);

            var patternParameterKind = signature.HasExplicitParameterList
                ? PropertyParameterKind.Explicit
                : ToPropertyParameterKind(signature.Parameters.FirstOrDefault()?.Source ?? CallableParameterSource.Implicit);

            var displayParameters = signature.ParameterPatterns
                .Select(pattern => new PropertyParameterInfo(
                    pattern.DisplayName,
                    patternParameterKind,
                    Span: null)
                {
                    DisplayNameOverride = pattern.DisplayName,
                })
                .ToList();

            var signatureParameters = useFlatParameters ? flatParameters : displayParameters;

            return [new PropertySignatureInfo(
                PropertyCallStyle.Plain,
                signature.DisplayText,
                signatureParameters)];
        }

        private static IReadOnlyList<PropertySignatureInfo> CreateBuiltinSignatures(string name, Algorithm? algorithm)
        {
            var plainSignature = CreateBuiltinCallableSignature(name, algorithm, PropertyCallStyle.Plain);
            var plainParameters = CreatePropertyParameters(plainSignature, PropertyParameterKind.Explicit);
            if (plainParameters.Count == 0)
                return [];

            var signatures = new List<PropertySignatureInfo>
            {
                new(
                    PropertyCallStyle.Plain,
                    FormatBuiltinSignature(plainSignature, PropertyCallStyle.Plain),
                    plainParameters),
            };

            var dotSignature = CreateBuiltinCallableSignature(name, algorithm, PropertyCallStyle.Dot);
            var dotParameters = CreatePropertyParameters(dotSignature, PropertyParameterKind.Explicit);
            if (!dotParameters.SequenceEqual(plainParameters))
            {
                signatures.Add(new PropertySignatureInfo(
                    PropertyCallStyle.Dot,
                    FormatBuiltinSignature(dotSignature, PropertyCallStyle.Dot),
                    dotParameters));
            }

            return signatures;
        }

        private static IReadOnlyList<PropertyParameterInfo> CreateBuiltinParameters(
            string name,
            Algorithm? algorithm,
            PropertyCallStyle callStyle)
            => CreatePropertyParameters(
                CreateBuiltinCallableSignature(name, algorithm, callStyle),
                PropertyParameterKind.Explicit);

        private static CallableSignature CreateBuiltinCallableSignature(
            string name,
            Algorithm? algorithm,
            PropertyCallStyle callStyle)
        {
            if (algorithm is Algorithm.User user)
                return CallableSignature.FromParameterDeclarations(
                    name,
                    user.Parameters,
                    CallableParameterSource.Builtin);

            if (algorithm is not Algorithm.Builtin(var builtin))
                return new CallableSignature(name, []);

            return CallableSignature.FromBuiltin(
                builtin,
                callStyle == PropertyCallStyle.Dot ? BuiltinCallStyle.Dot : BuiltinCallStyle.Plain);
        }

        private static IReadOnlyList<PropertyParameterInfo> CreatePropertyParameters(
            CallableSignature signature,
            PropertyParameterKind parameterKind)
        {
            return signature.Parameters
                .Select(parameter => new PropertyParameterInfo(
                    parameter.Name,
                    parameterKind,
                    GetSourceSpan(parameter))
                {
                    IsCollecting = parameter.Kind == ParameterKind.Collecting,
                })
                .ToList();
        }

        private static string FormatBuiltinSignature(
            CallableSignature signature,
            PropertyCallStyle callStyle)
        {
            var parameterList = string.Join(", ", signature.Parameters.Select(parameter => parameter.DisplayName));

            // Dot-call syntax injects the receiver as the fixed `collection`
            // argument, so the receiver placeholder mirrors that parameter
            // name: `collection.take(count)`, `collection.count`.
            return callStyle switch
            {
                PropertyCallStyle.Dot when signature.Parameters.Count == 0 => $"collection.{signature.Name}",
                PropertyCallStyle.Dot => $"collection.{signature.Name}({parameterList})",
                _ => signature.DisplayText,
            };
        }

        private static PropertyParameterKind ToPropertyParameterKind(CallableParameterSource source)
            => source switch
            {
                CallableParameterSource.Implicit => PropertyParameterKind.Implicit,
                _ => PropertyParameterKind.Explicit,
            };

        private static SourceSpan? GetSourceSpan(CallableParameter parameter)
            => parameter.Source == CallableParameterSource.Explicit
                && parameter.DeclaringPattern is CaptureParameterPattern capture
                    ? capture.Span
                    : null;

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

        private static ScopeFrame CreatePreludeScope()
        {
            var properties = new Dictionary<string, SymbolDefinition>(StringComparer.Ordinal);
            foreach (var property in PreludeAlgorithm.Properties)
                properties[property.Name] = CreateBuiltinSymbol(property.Name, property.Value, property.IsPublic);

            return new ScopeFrame(
                parent: null,
                properties,
                parameters: new Dictionary<string, SymbolDefinition>(StringComparer.Ordinal),
                propertyScope: ElaboratedScopeLookup.CreateScope(PreludeAlgorithm));
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
        PropertyInfo? PropertyInfo,
        PropertyInfo? DotPropertyInfo = null);

    private sealed class ScopeFrame
    {
        public ScopeFrame(
            ScopeFrame? parent,
            IReadOnlyDictionary<string, SymbolDefinition> properties,
            IReadOnlyDictionary<string, SymbolDefinition> parameters,
            ElaboratedPropertyScope propertyScope)
        {
            Parent = parent;
            Properties = properties;
            Parameters = parameters;
            PropertyScope = propertyScope;
        }

        public ScopeFrame? Parent { get; }

        public IReadOnlyDictionary<string, SymbolDefinition> Properties { get; }

        public IReadOnlyDictionary<string, SymbolDefinition> Parameters { get; }

        public ElaboratedPropertyScope PropertyScope { get; }
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
