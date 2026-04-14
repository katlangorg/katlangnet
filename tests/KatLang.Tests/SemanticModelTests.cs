using KatLang.Semantics;

namespace KatLang.Tests;

public class SemanticModelTests
{
    private static SemanticModel BuildModel(string source)
    {
        var parseResult = Parser.Parse(source);
        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(d => d.Message)));
        return SemanticModelBuilder.Build(parseResult);
    }

    private static IdentifierResolution ResolutionAt(SemanticModel model, int line, int column)
        => Assert.IsType<IdentifierResolution>(model.FindResolutionAt(line, column));

    private static void AssertSpan(SourceSpan span, int startLine, int startColumn, int endLine, int endColumn)
    {
        Assert.Equal(startLine, span.StartLineNumber);
        Assert.Equal(startColumn, span.StartColumn);
        Assert.Equal(endLine, span.EndLineNumber);
        Assert.Equal(endColumn, span.EndColumn);
    }

    [Fact]
    public void Build_OrdinaryAlgorithm_TracksExactDeclarationsAndReferences()
    {
        var model = BuildModel(
            """
            apply(x) = x
            apply(5)
            """);

        var applyDeclaration = Assert.Single(model.FindDeclarations("apply"));
        Assert.Equal(OccurrenceKind.PropertyDefinition, applyDeclaration.Kind);
        AssertSpan(applyDeclaration.Span, 1, 1, 1, 5);

        var xDeclaration = Assert.Single(model.FindDeclarations("x"));
        Assert.Equal(OccurrenceKind.ExplicitParameterDefinition, xDeclaration.Kind);
        AssertSpan(xDeclaration.Span, 1, 7, 1, 7);

        var xReference = ResolutionAt(model, 1, 12);
        Assert.Equal(OccurrenceKind.ParameterReference, xReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ExplicitParameterReference, xReference.Classification);
        Assert.Equal(xDeclaration, xReference.ResolvedDeclaration);

        var applyReference = ResolutionAt(model, 2, 1);
        Assert.Equal(OccurrenceKind.ResolveReference, applyReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, applyReference.Classification);
        Assert.Equal(applyDeclaration, applyReference.ResolvedDeclaration);
    }

    [Fact]
    public void Build_NestedScope_PrefersInnerPropertyOverOuterProperty()
    {
        var model = BuildModel(
            """
            x = 1
            inner = {
            x = 2
            Output = x
            }
            inner
            """);

        var xDeclarations = model.FindDeclarations("x").ToList();
        Assert.Equal(2, xDeclarations.Count);
        var innerXDeclaration = xDeclarations.Single(d => d.Span.StartLineNumber == 3);
        AssertSpan(innerXDeclaration.Span, 3, 1, 3, 1);

        var innerXReference = ResolutionAt(model, 4, 10);
        Assert.Equal(IdentifierClassification.PropertyReference, innerXReference.Classification);
        Assert.Equal(innerXDeclaration, innerXReference.ResolvedDeclaration);

        var innerDeclaration = Assert.Single(model.FindDeclarations("inner"));
        var innerReference = ResolutionAt(model, 6, 1);
        Assert.Equal(IdentifierClassification.PropertyReference, innerReference.Classification);
        Assert.Equal(innerDeclaration, innerReference.ResolvedDeclaration);
    }

    [Fact]
    public void Build_ConditionalAlgorithm_ClassifiesBinderDefinitionsAndReferences()
    {
        var model = BuildModel(
            """
            f(0) = 0
            f(x) = x
            f(1)
            """);

        var fDeclarations = model.FindDeclarations("f").ToList();
        Assert.Equal(2, fDeclarations.Count);
        Assert.Contains(fDeclarations, declaration => declaration.Span.StartLineNumber == 1);
        Assert.Contains(fDeclarations, declaration => declaration.Span.StartLineNumber == 2);

        var xDeclaration = Assert.Single(model.FindDeclarations("x"));
        Assert.Equal(OccurrenceKind.ConditionalBinderDefinition, xDeclaration.Kind);
        AssertSpan(xDeclaration.Span, 2, 3, 2, 3);

        var xReference = ResolutionAt(model, 2, 8);
        Assert.Equal(OccurrenceKind.ParameterReference, xReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ConditionalBinderReference, xReference.Classification);
        Assert.Equal(xDeclaration, xReference.ResolvedDeclaration);

        var fReference = ResolutionAt(model, 3, 1);
        Assert.Equal(IdentifierClassification.PropertyReference, fReference.Classification);
        Assert.Equal(fDeclarations[0], fReference.ResolvedDeclaration);
    }

    [Fact]
    public void Build_OpenLookup_AllowsPrivateHeadButRequiresPublicIntermediateAndMember()
    {
        var model = BuildModel(
            """
            open outer.inner
            outer = {
            public inner = {
            public val = 1
            }
            }
            val
            """);

        var outerDeclaration = Assert.Single(model.FindDeclarations("outer"));
        AssertSpan(outerDeclaration.Span, 2, 1, 2, 5);

        var innerDeclaration = Assert.Single(model.FindDeclarations("inner"));
        AssertSpan(innerDeclaration.Span, 3, 8, 3, 12);

        var valDeclaration = Assert.Single(model.FindDeclarations("val"));
        AssertSpan(valDeclaration.Span, 4, 8, 4, 10);

        var outerOpenReference = ResolutionAt(model, 1, 6);
        Assert.Equal(OccurrenceKind.OpenTargetReference, outerOpenReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.OpenTarget, outerOpenReference.Classification);
        Assert.Equal(outerDeclaration, outerOpenReference.ResolvedDeclaration);

        var innerOpenReference = ResolutionAt(model, 1, 12);
        Assert.Equal(OccurrenceKind.OpenTargetMemberReference, innerOpenReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.OpenTarget, innerOpenReference.Classification);
        Assert.Equal(innerDeclaration, innerOpenReference.ResolvedDeclaration);

        var valReference = ResolutionAt(model, 7, 1);
        Assert.Equal(IdentifierClassification.PropertyReference, valReference.Classification);
        Assert.Equal(valDeclaration, valReference.ResolvedDeclaration);
    }

    [Fact]
    public void Build_DotCall_UsesStructuralLookupExactFallbackAndBuiltinClassification()
    {
        var model = BuildModel(
            """
            public prop = 1
            public lib = {
            public val = 1
            }
            use(x) = x.prop
            lib.val
            1.prop
            Math.Pi
            """);

        var propDeclaration = Assert.Single(model.FindDeclarations("prop"));
        AssertSpan(propDeclaration.Span, 1, 8, 1, 11);

        var valDeclaration = Assert.Single(model.FindDeclarations("val"));
        AssertSpan(valDeclaration.Span, 3, 8, 3, 10);

        var unknownMember = ResolutionAt(model, 5, 12);
        Assert.Equal(OccurrenceKind.DotMemberReference, unknownMember.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Unresolved, unknownMember.Classification);
        Assert.Null(unknownMember.ResolvedDeclaration);

        var structuralMember = ResolutionAt(model, 6, 5);
        Assert.Equal(IdentifierClassification.PropertyReference, structuralMember.Classification);
        Assert.Equal(valDeclaration, structuralMember.ResolvedDeclaration);

        var fallbackMember = ResolutionAt(model, 7, 3);
        Assert.Equal(IdentifierClassification.PropertyReference, fallbackMember.Classification);
        Assert.Equal(propDeclaration, fallbackMember.ResolvedDeclaration);

        var builtinMember = ResolutionAt(model, 8, 6);
        Assert.Equal(IdentifierClassification.Builtin, builtinMember.Classification);
        Assert.Null(builtinMember.ResolvedDeclaration);
    }

    [Fact]
    public void Build_TracksReservedOutputDeclarationAndImplicitParameterReferences()
    {
        var model = BuildModel("Output = missing");

        var outputDeclaration = Assert.Single(model.FindDeclarations("Output"));
        Assert.Equal(OccurrenceKind.ReservedNameDefinition, outputDeclaration.Kind);
        AssertSpan(outputDeclaration.Span, 1, 1, 1, 6);

        var outputResolution = ResolutionAt(model, 1, 1);
        Assert.Equal(IdentifierClassification.ReservedName, outputResolution.Classification);
        Assert.Equal(outputDeclaration, outputResolution.ResolvedDeclaration);

        var missingResolution = ResolutionAt(model, 1, 10);
        Assert.Equal(OccurrenceKind.ParameterReference, missingResolution.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, missingResolution.Classification);
        Assert.Null(missingResolution.ResolvedDeclaration);
    }

    [Fact]
    public void Build_ImplicitParametersRemainVisibleInsideBuiltinCallArguments()
    {
        var model = BuildModel(
            """
            Algo = b, ~a + b, total + if(b mod 2 == 0, b, 0), b <= 100
            Sum = Algo.while((1, 2, 0)) : 2
            Sum
            """);

        var bReferences = model.FindResolutions("b")
            .Where(resolution => resolution.Occurrence.Kind == OccurrenceKind.ParameterReference)
            .ToList();

        Assert.Equal(5, bReferences.Count);
        Assert.All(
            bReferences,
            reference =>
            {
                Assert.Equal(IdentifierClassification.ImplicitParameterReference, reference.Classification);
                Assert.Null(reference.ResolvedDeclaration);
            });
    }

    [Fact]
    public void Build_LoadedExternalDotMember_GetsDedicatedClassification()
    {
        var model = BuildModel(
            """
            A = load('https://katlang.org/algorithm.kat')
            A.X
            """);

        var aDeclaration = Assert.Single(model.FindDeclarations("A"));
        var aReference = ResolutionAt(model, 2, 1);
        Assert.Equal(IdentifierClassification.PropertyReference, aReference.Classification);
        Assert.Equal(aDeclaration, aReference.ResolvedDeclaration);

        var xReference = ResolutionAt(model, 2, 3);
        Assert.Equal(OccurrenceKind.DotMemberReference, xReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.LoadedExternalMemberReference, xReference.Classification);
        Assert.Null(xReference.ResolvedDeclaration);
    }

    [Fact]
    public void Build_OrdinaryImplicitParametersRemainUnchanged()
    {
        var model = BuildModel(
            """
            Square = x * y
            Square
            """);

        var xReference = Assert.Single(model.FindResolutions("x"));
        Assert.Equal(OccurrenceKind.ParameterReference, xReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, xReference.Classification);

        var yReference = Assert.Single(model.FindResolutions("y"));
        Assert.Equal(OccurrenceKind.ParameterReference, yReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, yReference.Classification);
    }

    [Fact]
    public void Build_NonLoadUnresolvedDotMember_RemainsUnresolved()
    {
        var model = BuildModel(
            """
            A = 5
            A.X
            """);

        var xReference = ResolutionAt(model, 2, 3);
        Assert.Equal(OccurrenceKind.DotMemberReference, xReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Unresolved, xReference.Classification);
        Assert.Null(xReference.ResolvedDeclaration);
    }

    [Fact]
    public void Build_AliasToLoadProxy_GetsLoadedExternalMemberClassification()
    {
        var model = BuildModel(
            """
            Lib = load('https://katlang.org/algorithm.kat')
            Alias = Lib
            Alias.X
            """);

        var aliasReference = ResolutionAt(model, 3, 1);
        Assert.Equal(IdentifierClassification.PropertyReference, aliasReference.Classification);

        var xReference = ResolutionAt(model, 3, 7);
        Assert.Equal(OccurrenceKind.DotMemberReference, xReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.LoadedExternalMemberReference, xReference.Classification);
        Assert.Null(xReference.ResolvedDeclaration);
    }

    [Fact]
    public void SyntaxWalker_VisitsSemanticDeclarationAndIdentifierSites()
    {
        var parseResult = Parser.Parse(
            """
            public value = 1
            apply(x) = x + value
            match(0) = 0
            match(y) = y
            Output = apply(1).string
            """);

        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(d => d.Message)));

        var walker = new CollectingWalker();
        walker.VisitAlgorithm(parseResult.Root);

        Assert.Equal(["value", "apply", "match", "match"], walker.PropertyDeclarations);
        Assert.Equal(["x"], walker.ExplicitParameters);
        Assert.Equal(1, walker.ReservedOutputs);
        Assert.Equal(["y"], walker.ConditionalBinders);
        Assert.Equal(["value", "apply"], walker.ResolveIdentifiers);
        Assert.Equal(["x", "y"], walker.ParameterIdentifiers);
        Assert.Equal(["string"], walker.DotMembers);
    }

    private sealed class CollectingWalker : SyntaxWalker
    {
        public List<string> PropertyDeclarations { get; } = [];

        public List<string> ExplicitParameters { get; } = [];

        public int ReservedOutputs { get; private set; }

        public List<string> ConditionalBinders { get; } = [];

        public List<string> ResolveIdentifiers { get; } = [];

        public List<string> ParameterIdentifiers { get; } = [];

        public List<string> DotMembers { get; } = [];

        protected override void VisitPropertyDeclaration(Property property, SourceSpan span)
            => PropertyDeclarations.Add(property.Name);

        protected override void VisitExplicitParameterDeclaration(Algorithm algorithm, ParameterDeclaration declaration)
            => ExplicitParameters.Add(declaration.Name);

        protected override void VisitReservedOutputDeclaration(Algorithm algorithm, SourceSpan span)
            => ReservedOutputs++;

        protected override void VisitConditionalBinderDeclaration(Pattern.Bind pattern, SourceSpan span)
            => ConditionalBinders.Add(pattern.Name);

        protected override void VisitResolveIdentifier(Expr.Resolve expr)
            => ResolveIdentifiers.Add(expr.Name);

        protected override void VisitParameterIdentifier(Expr.Param expr)
            => ParameterIdentifiers.Add(expr.Name);

        protected override void VisitDotMemberIdentifier(Expr.DotCall expr, SourceSpan span)
            => DotMembers.Add(expr.Name);
    }
}