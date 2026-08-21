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

    /// <summary>
    /// Builds <see cref="PreludeCatalog.Symbols"/> from the same signature-only
    /// prelude the semantic model resolves against.
    /// </summary>
    internal static IReadOnlyList<VisibleSymbol> CreatePreludeCatalogSymbols()
        => Builder.CreatePreludeCatalog();

    /// <summary>
    /// Builds <see cref="PreludeCatalog.DotIntrinsicSymbols"/> (the receiver-only
    /// <c>.string</c> value intrinsic).
    /// </summary>
    internal static IReadOnlyList<VisibleSymbol> CreateDotIntrinsicCatalogSymbols()
        => Builder.CreateDotIntrinsicCatalog();

    private sealed class Builder
    {
        private static readonly Algorithm.User MathAlgorithm = BuiltinRegistry.CreateMathAlgorithm(MathAlgorithmFlavor.SignatureOnly);
        private static readonly Algorithm.User PreludeAlgorithm = BuiltinRegistry.CreateSemanticPreludeAlgorithm(MathAlgorithm);
        private static readonly ScopeFrame PreludeScope = CreatePreludeScope();
        private static readonly PropertyInfo StringIntrinsicPropertyInfo = CreateStringIntrinsicPropertyInfo();
        private static readonly SymbolDefinition StringIntrinsicSymbol = new(
            "string",
            SymbolKind.Builtin,
            AlgorithmValue: null,
            Declaration: null,
            IsPublic: true,
            StringIntrinsicPropertyInfo,
            StringIntrinsicPropertyInfo);

        private readonly List<IdentifierOccurrence> _identifierOccurrences = [];
        private readonly List<DeclarationOccurrence> _declarations = [];
        private readonly List<IdentifierResolution> _identifierResolutions = [];
        private readonly List<PropertyInfo> _propertyInfos = [];
        private readonly HashSet<PropertyInfo> _seenPropertyInfos = new(ReferenceEqualityComparer.Instance);
        // SourceSpan coordinates are document-local. Two loaded modules may therefore
        // contain value-equal declaration DTOs even though they denote different
        // properties; declaration resolution carries the canonical occurrence object,
        // so this identity map must not collapse those module-local declarations.
        private readonly Dictionary<DeclarationOccurrence, PropertyInfo> _propertyInfoByDeclaration =
            new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<Property, SymbolDefinition> _propertySymbolCache =
            new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<Algorithm, IReadOnlyList<VisibleSymbol>> _memberSymbolCache =
            new(ReferenceEqualityComparer.Instance);
        private readonly List<ScopeVisibility> _scopeVisibilities = [];
        private readonly List<ScopeRegionBuilder> _regionStack = [];

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
            var sortedScopeVisibilities = _scopeVisibilities
                .OrderBy(static scope => scope.Span is null ? 0 : 1)
                .ThenBy(static scope => scope.NestingDepth)
                .ThenBy(static scope => scope.Span, SpanComparer.Instance)
                .ToList();

            return new SemanticModel(
                root,
                sortedIdentifierOccurrences,
                sortedDeclarations,
                sortedIdentifierResolutions,
                sortedPropertyInfos,
                new Dictionary<DeclarationOccurrence, PropertyInfo>(
                    _propertyInfoByDeclaration,
                    ReferenceEqualityComparer.Instance),
                sortedScopeVisibilities);
        }

        private void VisitAlgorithm(
            Algorithm algorithm,
            ScopeFrame parentScope,
            IReadOnlyDictionary<string, SymbolDefinition>? extraParameters,
            SourceSpan? regionSeedSpan = null)
        {
            switch (algorithm)
            {
                case Algorithm.User user:
                    VisitUserAlgorithm(user, parentScope, extraParameters, regionSeedSpan);
                    break;
                case Algorithm.Conditional conditional:
                    VisitConditionalAlgorithm(conditional, parentScope, regionSeedSpan);
                    break;
                case Algorithm.Builtin:
                    break;
            }
        }

        private void VisitUserAlgorithm(
            Algorithm.User algorithm,
            ScopeFrame parentScope,
            IReadOnlyDictionary<string, SymbolDefinition>? extraParameters,
            SourceSpan? regionSeedSpan = null)
        {
            var scope = CreateScope(algorithm, parentScope, extraParameters);
            var region = OpenScopeRegion(scope, regionSeedSpan, algorithm.IsModuleElaborated);
            ExtendRegionWithDeclarationAnchors(algorithm, extraParameters);

            foreach (var open in algorithm.Opens)
                VisitOpenExpression(open, scope);

            foreach (var property in algorithm.Properties)
                VisitAlgorithm(property.Value, scope, extraParameters: null);

            foreach (var expr in algorithm.Output)
                VisitExpr(expr, scope);

            CloseScopeRegion(region);
        }

        private void VisitConditionalAlgorithm(
            Algorithm.Conditional algorithm,
            ScopeFrame parentScope,
            SourceSpan? regionSeedSpan = null)
        {
            var scope = CreateScope(algorithm, parentScope, extraParameters: null);
            var region = OpenScopeRegion(scope, regionSeedSpan);
            ExtendRegionWithDeclarationAnchors(algorithm, extraParameters: null);

            foreach (var open in algorithm.Opens)
                VisitOpenExpression(open, scope);

            foreach (var branch in algorithm.Branches)
                VisitConditionalBranch(branch, scope);

            CloseScopeRegion(region);
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

            var symbol = CreateBuiltinSymbol(
                property.Name,
                property.Value,
                property.IsPublic,
                supportsLexicalDotCall: ReferenceEquals(owner, PreludeAlgorithm)
                    ? BuiltinRegistry.IsRuntimePreludeName(property.Name)
                    : null);
            _propertySymbolCache[property] = symbol;
            return symbol;
        }

        private static SymbolDefinition CreateBuiltinSymbol(
            string name,
            Algorithm? algorithm,
            bool isPublic,
            bool? supportsLexicalDotCall = null)
        {
            var propertyInfo = CreatePropertyInfo(
                name,
                SymbolKind.Builtin,
                algorithm,
                declaration: null,
                isPublic,
                PropertyExposure.Exported,
                declarationSpans: null,
                supportsLexicalDotCall: supportsLexicalDotCall);

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
            ExtendCurrentRegion(expr.Span);

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

                case Expr.DotCall dotCall when dotCall.IsCoreOpenForm():
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

                case Expr.AlgorithmExpr(var algorithm):
                    VisitAlgorithm(algorithm, PreludeScope, extraParameters: null, expr.Span);
                    break;

                case Expr.Capture(var captureBody):
                    // A capture target owns no scope: rows classify against the
                    // open-target prelude scope, matching the pre-split
                    // transparent wrapper (which added only an empty frame).
                    foreach (var row in captureBody)
                        VisitExpr(row, PreludeScope);
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
            ExtendCurrentRegion(expr.Span);

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
                    if (dotCall.Args is { } dotCallArgs)
                    {
                        // Argument bundles own no scope: slots classify in the
                        // enclosing scope, exactly like capture rows.
                        foreach (var argExpr in dotCallArgs)
                            VisitExpr(argExpr, scope);
                    }
                    break;

                case Expr.Grace(var inner, _):
                    VisitExpr(inner, scope);
                    break;

                case Expr.AlgorithmExpr(var algorithm):
                    VisitAlgorithm(algorithm, scope, extraParameters: null, expr.Span);
                    break;

                case Expr.Capture(var captureBody):
                    // Captures are transparent: rows classify in the enclosing
                    // scope (the pre-split wrapper added only an empty frame).
                    foreach (var row in captureBody)
                        VisitExpr(row, scope);
                    break;

                case Expr.Call(var function, var args):
                    VisitExpr(function, scope);
                    foreach (var argExpr in args)
                        VisitExpr(argExpr, scope);
                    break;

                case Expr.NativeCall:
                case Expr.Num:
                case Expr.StringLiteral:
                    break;
            }
        }

        private (IdentifierClassification Classification, DeclarationOccurrence? Declaration, PropertyInfo? PropertyInfo) ResolveDotMember(Expr.DotCall dotCall, ScopeFrame scope)
        {
            if (dotCall.UsesOrdinaryDotStringIntrinsic())
                return (IdentifierClassification.Builtin, null, StringIntrinsicSymbol.PropertyInfo);

            var provider = ResolveStructuralMemberProvider(dotCall.Target, scope);
            if (provider.Kind == StaticStructuralMemberProviderKind.KnownAlgorithm)
            {
                var targetAlgorithm = provider.Algorithm!;
                if (TryResolveDeclaredProperty(targetAlgorithm, dotCall.Name) is { } declaredProperty)
                {
                    if (declaredProperty.PropertyInfo?.IsExported == true)
                        return (ClassifyReferenceSymbol(declaredProperty), declaredProperty.Declaration, declaredProperty.PropertyInfo);

                    return (IdentifierClassification.Unresolved, null, null);
                }

                if (targetAlgorithm.DefinesConditionalBranchProperty(dotCall.Name))
                    return (IdentifierClassification.Unresolved, null, null);

                return ResolveDotMemberFallbackBinding(dotCall, scope);
            }

            var fallbackSelection = dotCall.GetLexicalFallbackSelection(provider);
            return fallbackSelection switch
            {
                // The editor surfaces a MAY-selected stored fallback for a
                // runtime parameter as the possible callable binding, exactly
                // like implicit signature inference. Exposure analysis remains
                // the separate MUST-selected consumer.
                LexicalFallbackSelection.Conditional
                    when provider.Kind == StaticStructuralMemberProviderKind.RuntimeParameter =>
                    ResolveDotMemberFallbackBinding(dotCall, scope),
                LexicalFallbackSelection.Always =>
                    ResolveDotMemberFallbackBinding(dotCall, scope),

                // A remaining Conditional provider is an unresolved or
                // ambiguous lexical receiver. Runtime receiver resolution can
                // fail before either dot arm is selected, so the tolerant
                // editor leaves the member unresolved. Never reaches here for
                // a conditional-branch structural member (a runtime error, not
                // fallback); ordinary declared members and `.string` returned
                // above with their richer symbol information.
                LexicalFallbackSelection.Conditional
                    or LexicalFallbackSelection.Never =>
                    (IdentifierClassification.Unresolved, null, null),
                _ => throw new InvalidOperationException(
                    $"Unhandled lexical-fallback selection: {fallbackSelection}"),
            };
        }

        /// <summary>
        /// Dot-member lexical-fallback classification, CONSUMING the dot
        /// edge's stored fallback identity: a <see cref="Expr.Param"/>
        /// fallback navigates to the parameter declaration through the
        /// ordinary parameter frames, and a <see cref="Expr.Resolve"/>
        /// fallback keeps ordinary lexical/property/open/prelude resolution
        /// under ITS OWN identifier. The front-end decided Param-vs-Resolve
        /// once; no shadow-precedence algorithm is re-run here, and
        /// <c>DotCall.Name</c> is never used for lexical resolution.
        /// </summary>
        private (IdentifierClassification Classification, DeclarationOccurrence? Declaration, PropertyInfo? PropertyInfo) ResolveDotMemberFallbackBinding(Expr.DotCall dotCall, ScopeFrame scope)
        {
            switch (dotCall.EffectiveLexicalFallback)
            {
                case Expr.Param(var parameterName):
                {
                    var parameterSymbol = ResolveParameter(scope, parameterName);
                    return (ClassifyParameterSymbol(parameterSymbol), parameterSymbol?.Declaration, null);
                }

                case Expr.Resolve(var fallbackName)
                    when ResolveLexicalProperty(scope, fallbackName) is { } lexical:
                    return (ClassifyReferenceSymbol(lexical), lexical.Declaration, GetLexicalDotFallbackPropertyInfo(lexical));

                default:
                    return (IdentifierClassification.Unresolved, null, null);
            }
        }

        private static PropertyInfo? GetLexicalDotFallbackPropertyInfo(SymbolDefinition symbol)
            => symbol.PropertyInfo?.SupportsLexicalDotCall == true
                ? symbol.DotPropertyInfo
                    ?? symbol.PropertyInfo.WithPreferredCallStyle(PropertyCallStyle.Dot)
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

        private StaticStructuralMemberProvider ResolveStructuralMemberProvider(Expr expr, ScopeFrame scope)
        {
            var provider = expr.GetStaticStructuralMemberProvider();
            if (provider.Kind != StaticStructuralMemberProviderKind.LexicalReference)
                return provider;

            if (expr is Expr.Resolve(var name)
                && ResolveLexicalProperty(scope, name)?.AlgorithmValue is { } algorithm)
            {
                return new StaticStructuralMemberProvider(
                    StaticStructuralMemberProviderKind.KnownAlgorithm,
                    algorithm);
            }

            return provider;
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
            PropertyCallStyle preferredCallStyle = PropertyCallStyle.Plain,
            bool? supportsLexicalDotCall = null)
        {
            var supportsDotFallback = supportsLexicalDotCall
                ?? SupportsLexicalDotCall(algorithm);

            if (kind == SymbolKind.Builtin || algorithm is Algorithm.Builtin)
            {
                var signatures = CreateBuiltinSignatures(name, algorithm, supportsDotFallback);
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
                    SupportsLexicalDotCall = supportsDotFallback,
                };
            }

            return algorithm switch
            {
                Algorithm.User user => CreateOrdinaryPropertyInfo(name, user, declaration, isPublic, exposure),
                Algorithm.Conditional conditional => CreateConditionalPropertyInfo(
                    name,
                    conditional,
                    declaration,
                    isPublic,
                    exposure,
                    declarationSpans),
                _ => new PropertyInfo(name, declaration, PropertyShape.Ordinary, isPublic, exposure, [], []),
            };
        }

        private static bool SupportsLexicalDotCall(Algorithm? algorithm)
            => algorithm switch
            {
                Algorithm.User user => user.ParameterPatterns.Count > 0,
                Algorithm.Conditional { Branches.Count: > 0 } conditional =>
                    conditional.Branches[0].Pattern.TopLevelArity() > 0,
                Algorithm.Builtin(var builtin) =>
                    BuiltinRegistry.GetBuiltin(builtin).PlainSignature.TopLevelParameterCount > 0,
                _ => false,
            };

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
                SupportsLexicalDotCall = signature.TopLevelParameterCount > 0,
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

            var signatures = new List<PropertySignatureInfo>
            {
                new(
                    PropertyCallStyle.Plain,
                    signature.DisplayText,
                    signatureParameters),
            };

            if (signatureParameters.Count > 0)
                signatures.Add(CreateReceiverInjectedSignature(signature.Name, signatureParameters));

            return Array.AsReadOnly(signatures.ToArray());
        }

        private static PropertyInfo CreateConditionalPropertyInfo(
            string name,
            Algorithm.Conditional algorithm,
            DeclarationOccurrence? declaration,
            bool isPublic,
            PropertyExposure exposure,
            IReadOnlyList<SourceSpan>? declarationSpans)
        {
            var arity = algorithm.Branches.Count == 0
                ? 0
                : algorithm.Branches[0].Pattern.TopLevelArity();
            var parameters = CreateConditionalSignatureParameters(algorithm, arity);
            var signatures = new List<PropertySignatureInfo>();

            if (arity > 0)
            {
                signatures.Add(new PropertySignatureInfo(
                    PropertyCallStyle.Plain,
                    CallableSignature.FormatDisplayText(
                        name,
                        parameters.Select(static parameter => parameter.DisplayName)),
                    parameters));
                signatures.Add(CreateReceiverInjectedSignature(name, parameters));
            }

            return new PropertyInfo(
                name,
                declaration,
                PropertyShape.Conditional,
                isPublic,
                exposure,
                Parameters: [],
                CreateConditionalBranches(name, algorithm, declarationSpans))
            {
                Signatures = Array.AsReadOnly(signatures.ToArray()),
                SupportsLexicalDotCall = arity > 0,
            };
        }

        private static IReadOnlyList<PropertyParameterInfo> CreateConditionalSignatureParameters(
            Algorithm.Conditional algorithm,
            int arity)
        {
            if (arity == 0)
                return [];

            var firstPattern = algorithm.Branches[0].Pattern;
            IReadOnlyList<Pattern> topLevelPatterns = firstPattern is Pattern.SequenceValue(var items)
                ? items
                : [firstPattern];
            var parameters = new PropertyParameterInfo[arity];

            for (var i = 0; i < arity; i++)
            {
                var pattern = topLevelPatterns[i];
                var name = pattern is Pattern.Bind bind && Lexer.IsValidIdentifier(bind.Name)
                    ? bind.Name
                    : arity == 1
                        ? "value"
                        : $"argument{i + 1}";
                parameters[i] = new PropertyParameterInfo(
                    name,
                    PropertyParameterKind.ConditionalBinder,
                    pattern is Pattern.Bind binder ? binder.NameSpan : null)
                {
                    IsCollecting = pattern is Pattern.Bind { ParameterKind: ParameterKind.Collecting },
                };
            }

            return Array.AsReadOnly(parameters);
        }

        private static IReadOnlyList<PropertySignatureInfo> CreateBuiltinSignatures(
            string name,
            Algorithm? algorithm,
            bool supportsLexicalDotCall)
        {
            var plainSignature = CreateBuiltinCallableSignature(name, algorithm, PropertyCallStyle.Plain);
            var plainParameters = CreatePropertyParameters(plainSignature, PropertyParameterKind.Explicit);
            if (plainParameters.Count == 0)
                return [];

            var signatures = new List<PropertySignatureInfo>
            {
                new(
                    PropertyCallStyle.Plain,
                    plainSignature.DisplayText,
                    plainParameters),
            };

            if (supportsLexicalDotCall)
            {
                var dotSignature = CreateBuiltinCallableSignature(name, algorithm, PropertyCallStyle.Dot);
                var dotParameters = CreatePropertyParameters(dotSignature, PropertyParameterKind.Explicit);
                signatures.Add(new PropertySignatureInfo(
                    PropertyCallStyle.Dot,
                    FormatReceiverInjectedSignature(name, plainParameters[0].Name, dotParameters),
                    dotParameters));
            }

            return Array.AsReadOnly(signatures.ToArray());
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
            {
                var parameters = callStyle == PropertyCallStyle.Dot
                    ? user.Parameters.Skip(1)
                    : user.Parameters;
                return CallableSignature.FromParameterDeclarations(
                    name,
                    [.. parameters],
                    CallableParameterSource.Builtin);
            }

            if (algorithm is not Algorithm.Builtin(var builtin))
                return new CallableSignature(name, []);

            return BuiltinRegistry.GetBuiltin(builtin).GetToolingSignature(
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

        private static PropertySignatureInfo CreateReceiverInjectedSignature(
            string name,
            IReadOnlyList<PropertyParameterInfo> plainParameters)
        {
            var dotParameters = Array.AsReadOnly(plainParameters.Skip(1).ToArray());
            return new PropertySignatureInfo(
                PropertyCallStyle.Dot,
                FormatReceiverInjectedSignature(name, plainParameters[0].Name, dotParameters),
                dotParameters);
        }

        private static string FormatReceiverInjectedSignature(
            string name,
            string receiverName,
            IReadOnlyList<PropertyParameterInfo> parameters)
        {
            var receiverDisplay = Lexer.IsValidIdentifier(receiverName) ? receiverName : "value";
            var parameterList = string.Join(", ", parameters.Select(static parameter => parameter.DisplayName));
            return parameters.Count == 0
                ? $"{receiverDisplay}.{name}"
                : $"{receiverDisplay}.{name}({parameterList})";
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

        // ── Scope visibility (editor completion) ────────────────────────────

        private ScopeRegionBuilder OpenScopeRegion(ScopeFrame scope, SourceSpan? seedSpan, bool isModuleRoot = false)
        {
            var isRoot = _regionStack.Count == 0;

            // A loaded module's spans are positioned in the MODULE's source text,
            // so no span inside its subtree may become a current-document scope
            // region or extend an enclosing document hull. The document root is
            // never suppressed: a host analyzing a module directly makes that
            // module's text the current document.
            var suppressed = !isRoot
                && (isModuleRoot || _regionStack[^1].Suppressed);

            var region = new ScopeRegionBuilder(scope, isRoot, suppressed, _regionStack.Count);
            region.Extend(seedSpan);
            _regionStack.Add(region);
            return region;
        }

        private void CloseScopeRegion(ScopeRegionBuilder region)
        {
            _regionStack.RemoveAt(_regionStack.Count - 1);

            if (region.Suppressed)
                return;

            // A nested scope's content is part of the enclosing scope's source
            // extent, so the hull folds outward before the region is emitted.
            if (_regionStack.Count > 0)
                _regionStack[^1].Extend(region.Hull);

            // The root region is addressable without a span. A nested scope with
            // no source anchor at all (possible only in host-built trees) has no
            // position a cursor could reach, so it is not emitted.
            if (region.IsRoot)
                _scopeVisibilities.Add(new ScopeVisibility(
                    Span: null,
                    ComputeVisibleSymbols(region.Scope),
                    region.NestingDepth));
            else if (region.Hull is { } hull)
                _scopeVisibilities.Add(new ScopeVisibility(
                    hull,
                    ComputeVisibleSymbols(region.Scope),
                    region.NestingDepth));
        }

        private void ExtendCurrentRegion(SourceSpan? span)
        {
            if (_regionStack.Count > 0 && !_regionStack[^1].Suppressed)
                _regionStack[^1].Extend(span);
        }

        private void ExtendRegionWithDeclarationAnchors(
            Algorithm algorithm,
            IReadOnlyDictionary<string, SymbolDefinition>? extraParameters)
        {
            foreach (var property in algorithm.Properties)
            {
                foreach (var span in property.DeclarationSpans)
                    ExtendCurrentRegion(span);
            }

            foreach (var parameter in algorithm.ExplicitParameters)
                ExtendCurrentRegion(parameter.Span);

            if (extraParameters is null)
                return;

            foreach (var symbol in extraParameters.Values)
                ExtendCurrentRegion(symbol.Declaration?.Span);
        }

        /// <summary>
        /// Computes the resolved visible-name set for one scope: the ownership-first
        /// direct chain (each level's parameters and own properties, an inner level
        /// deciding a name before any outer level), then open-provided public
        /// exported members level by level with the evaluator's first-occurrence
        /// open dedup and same-level ambiguity suppression — mirroring
        /// <see cref="ElaboratedScopeLookup.LookupLexicalPropertyMatches"/> so every
        /// emitted symbol agrees with what identifier resolution selects for that
        /// name in this scope. Prelude names participate in shadowing but are
        /// emitted once through <see cref="PreludeCatalog.Symbols"/>, not per scope.
        /// </summary>
        private IReadOnlyList<VisibleSymbol> ComputeVisibleSymbols(ScopeFrame scope)
        {
            var decided = new HashSet<string>(StringComparer.Ordinal);
            var symbols = new List<VisibleSymbol>();

            for (var frame = scope; frame is not null; frame = frame.Parent)
            {
                var isPrelude = ReferenceEquals(frame, PreludeScope);

                foreach (var (name, symbol) in frame.Parameters)
                {
                    if (!decided.Add(name))
                        continue;

                    symbols.Add(new VisibleSymbol(
                        name,
                        ClassifyParameterSymbol(symbol),
                        symbol.Declaration,
                        Property: null));
                }

                // Own properties come from the same per-level hit list lexical
                // lookup scans, first occurrence winning like the lookup does.
                foreach (var hit in frame.PropertyScope.Properties)
                {
                    var name = hit.Property.Name;
                    if (isPrelude)
                    {
                        // Prelude names still decide shadowing: a direct prelude
                        // name keeps opens from providing it (direct-anywhere
                        // beats open-anywhere), and the catalog emits it instead.
                        decided.Add(name);
                        continue;
                    }

                    var symbol = CreateLookupPropertySymbol(hit.Owner, hit.Property);

                    // Synthetic properties (deconstruction's hoisted shared RHS)
                    // have no declaration site and are never source-visible names.
                    if (symbol.Declaration is null)
                        continue;

                    if (!decided.Add(name))
                        continue;

                    symbols.Add(CreateVisibleSymbol(name, symbol));
                }
            }

            for (var propertyScope = scope.PropertyScope; propertyScope is not null; propertyScope = propertyScope.Parent)
                CollectOpenProvidedSymbols(propertyScope, decided, symbols);

            symbols.Sort(static (left, right) => string.CompareOrdinal(left.Name, right.Name));
            return symbols;
        }

        /// <summary>
        /// Adds one scope level's open-provided names, mirroring
        /// <see cref="ElaboratedScopeLookup.LookupOpenPropertyMatches"/>: written
        /// named targets dedup first-occurrence-wins by open spelling, inline
        /// blocks never dedup, only public exported members are provided, and a
        /// name supplied by two distinct providers at the same level is ambiguous —
        /// it resolves to nothing there, so it is suppressed rather than offered.
        /// </summary>
        private void CollectOpenProvidedSymbols(
            ElaboratedPropertyScope propertyScope,
            HashSet<string> decided,
            List<VisibleSymbol> symbols)
        {
            if (propertyScope.Opens.Count == 0)
                return;

            HashSet<string>? seenKeys = null;
            Dictionary<string, SymbolDefinition?>? levelProviders = null;

            for (var i = 0; i < propertyScope.Opens.Count; i++)
            {
                var openExpr = propertyScope.Opens[i];
                seenKeys ??= [];
                if (!seenKeys.Add(ElaboratedScopeLookup.OpenTargetDedupKey(openExpr, i)))
                    continue;

                var targetAlgorithm = ElaboratedScopeLookup.ResolveOpenTarget(propertyScope, openExpr);
                if (targetAlgorithm is null)
                    continue;

                var providedNames = new HashSet<string>(StringComparer.Ordinal);
                foreach (var property in targetAlgorithm.Properties)
                {
                    if (!property.IsPublic || property.Exposure != PropertyExposure.Exported)
                        continue;

                    // One provider supplies each of its names once (a duplicate
                    // within one provider is the first-declaration lookup rule),
                    // and a name already decided directly is never open-provided.
                    if (decided.Contains(property.Name) || !providedNames.Add(property.Name))
                        continue;

                    levelProviders ??= new(StringComparer.Ordinal);
                    levelProviders[property.Name] = levelProviders.TryGetValue(property.Name, out _)
                        ? null // second distinct provider at this level: ambiguous
                        : CreateLookupPropertySymbol(targetAlgorithm, property);
                }
            }

            if (levelProviders is null)
                return;

            foreach (var (name, symbol) in levelProviders)
            {
                decided.Add(name);
                if (symbol is not null)
                    symbols.Add(CreateVisibleSymbol(name, symbol));
            }
        }

        private VisibleSymbol CreateVisibleSymbol(string name, SymbolDefinition symbol)
            => new(
                name,
                ClassifyReferenceSymbol(symbol),
                symbol.Declaration,
                symbol.PropertyInfo,
                CreateMemberSymbols(symbol.AlgorithmValue));

        /// <summary>
        /// One-level structural dot-member surface of an algorithm-valued symbol,
        /// with the same exposure filter as <see cref="ResolveDotMember"/>:
        /// exported members only, public-vs-private deliberately ignored because
        /// structural dot access reaches private members. Conditional-valued
        /// members stay listed (a clause family is an ordinary dot target);
        /// properties declared inside clause bodies are not dot-reachable and are
        /// never listed. Member symbols carry no members of their own.
        /// </summary>
        private IReadOnlyList<VisibleSymbol> CreateMemberSymbols(Algorithm? algorithmValue)
        {
            if (algorithmValue is not Algorithm.User user || user.Properties.Count == 0)
                return [];

            if (_memberSymbolCache.TryGetValue(user, out var cached))
                return cached;

            List<VisibleSymbol>? members = null;
            var seen = new HashSet<string>(StringComparer.Ordinal);

            foreach (var property in user.Properties)
            {
                if (property.DeclarationSpans.Count == 0 || !seen.Add(property.Name))
                    continue;

                var symbol = CreateLookupPropertySymbol(user, property);
                if (symbol.PropertyInfo?.IsExported != true)
                    continue;

                members ??= [];
                members.Add(new VisibleSymbol(
                    property.Name,
                    ClassifyReferenceSymbol(symbol),
                    symbol.Declaration,
                    symbol.PropertyInfo));
            }

            if (members is null)
            {
                _memberSymbolCache[user] = [];
                return [];
            }

            members.Sort(static (left, right) => string.CompareOrdinal(left.Name, right.Name));
            var result = Array.AsReadOnly(members.ToArray());
            _memberSymbolCache[user] = result;
            return result;
        }

        public static IReadOnlyList<VisibleSymbol> CreatePreludeCatalog()
        {
            var symbols = new List<VisibleSymbol>(PreludeAlgorithm.Properties.Count);
            foreach (var property in PreludeAlgorithm.Properties)
            {
                var symbol = CreateBuiltinSymbol(
                    property.Name,
                    property.Value,
                    property.IsPublic,
                    BuiltinRegistry.IsRuntimePreludeName(property.Name));
                symbols.Add(new VisibleSymbol(
                    property.Name,
                    IdentifierClassification.Builtin,
                    Declaration: null,
                    symbol.PropertyInfo,
                    CreateMathMemberCatalog(property.Value)));
            }

            symbols.Sort(static (left, right) => string.CompareOrdinal(left.Name, right.Name));
            return Array.AsReadOnly(symbols.ToArray());
        }

        private static IReadOnlyList<VisibleSymbol> CreateMathMemberCatalog(Algorithm? algorithmValue)
        {
            if (!ReferenceEquals(algorithmValue, MathAlgorithm))
                return [];

            var members = new List<VisibleSymbol>(MathAlgorithm.Properties.Count);
            foreach (var property in MathAlgorithm.Properties)
            {
                var symbol = CreateBuiltinSymbol(property.Name, property.Value, property.IsPublic);
                members.Add(new VisibleSymbol(
                    property.Name,
                    IdentifierClassification.Builtin,
                    Declaration: null,
                    symbol.PropertyInfo));
            }

            members.Sort(static (left, right) => string.CompareOrdinal(left.Name, right.Name));
            return Array.AsReadOnly(members.ToArray());
        }

        public static IReadOnlyList<VisibleSymbol> CreateDotIntrinsicCatalog()
        {
            return [new VisibleSymbol(
                "string",
                IdentifierClassification.Builtin,
                Declaration: null,
                StringIntrinsicPropertyInfo)];
        }

        private static PropertyInfo CreateStringIntrinsicPropertyInfo()
            // `.string` is receiver-only — no plain-call form exists — so its one
            // signature surface is the dot style with no written arguments.
            => new(
                "string",
                Declaration: null,
                PropertyShape.Builtin,
                IsPublic: true,
                PropertyExposure.Exported,
                Parameters: [],
                ConditionalBranches: [])
            {
                PreferredCallStyle = PropertyCallStyle.Dot,
                Signatures = [new PropertySignatureInfo(PropertyCallStyle.Dot, "value.string", [])],
                SupportsLexicalDotCall = false,
            };

        private static ScopeFrame CreatePreludeScope()
        {
            var properties = new Dictionary<string, SymbolDefinition>(StringComparer.Ordinal);
            foreach (var property in PreludeAlgorithm.Properties)
                properties[property.Name] = CreateBuiltinSymbol(
                    property.Name,
                    property.Value,
                    property.IsPublic,
                    BuiltinRegistry.IsRuntimePreludeName(property.Name));

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

    /// <summary>
    /// Accumulates the source hull of one scope's content while the builder walks
    /// it: the union of every span observed inside the scope, seeded with the
    /// wrapping algorithm expression's span when the scope came from one (brace
    /// blocks in expression position keep their exact <c>{ ... }</c> extent;
    /// unwrapped property bodies get the hull of their declaration anchors and
    /// content spans).
    /// </summary>
    private sealed class ScopeRegionBuilder
    {
        public ScopeRegionBuilder(ScopeFrame scope, bool isRoot, bool suppressed, int nestingDepth)
        {
            Scope = scope;
            IsRoot = isRoot;
            Suppressed = suppressed;
            NestingDepth = nestingDepth;
        }

        public ScopeFrame Scope { get; }

        public bool IsRoot { get; }

        public int NestingDepth { get; }

        /// <summary>
        /// True inside a load-elaborated module subtree: spans there belong to the
        /// module's source text, so the region neither emits nor folds outward.
        /// </summary>
        public bool Suppressed { get; }

        public SourceSpan? Hull { get; private set; }

        public void Extend(SourceSpan? span)
        {
            if (span is null || Suppressed)
                return;

            if (Hull is null)
            {
                Hull = span;
                return;
            }

            var startsEarlier = span.StartLineNumber < Hull.StartLineNumber
                || (span.StartLineNumber == Hull.StartLineNumber && span.StartColumn < Hull.StartColumn);
            var endsLater = span.EndLineNumber > Hull.EndLineNumber
                || (span.EndLineNumber == Hull.EndLineNumber && span.EndColumn > Hull.EndColumn);

            if (!startsEarlier && !endsLater)
                return;

            Hull = new SourceSpan(
                startsEarlier ? span.StartLineNumber : Hull.StartLineNumber,
                startsEarlier ? span.StartColumn : Hull.StartColumn,
                endsLater ? span.EndLineNumber : Hull.EndLineNumber,
                endsLater ? span.EndColumn : Hull.EndColumn);
        }
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
