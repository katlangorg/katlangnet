using KatLang.Semantics;

namespace KatLang.Tests;

public class SemanticModelTests
{
    private static Func<string, string> MockDownloader(Dictionary<string, string> files)
    {
        return url =>
        {
            if (files.TryGetValue(url, out var content))
                return content;

            var trimmed = url.TrimEnd('/');
            if (files.TryGetValue(trimmed, out content))
                return content;

            throw new Exception($"404: {url}");
        };
    }

    private static SemanticModel BuildModel(string source, Dictionary<string, string>? remoteFiles = null)
    {
        var parseResult = remoteFiles is null
            ? Parser.Parse(source)
            : Parser.Parse(source, MockDownloader(remoteFiles));
        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(d => d.Message)));
        return SemanticModelBuilder.Build(parseResult);
    }

    private static IdentifierResolution ResolutionAt(SemanticModel model, int line, int column)
        => Assert.IsType<IdentifierResolution>(model.FindResolutionAt(line, column));

    private static PropertyInfo PropertyAt(SemanticModel model, int line, int column)
        => Assert.IsType<PropertyInfo>(model.FindPropertyAt(line, column));

    private static PropertyInfo SingleProperty(SemanticModel model, string name)
        => Assert.Single(model.FindProperties(name));

    private static void AssertSpan(SourceSpan span, int startLine, int startColumn, int endLine, int endColumn)
    {
        Assert.Equal(startLine, span.StartLineNumber);
        Assert.Equal(startColumn, span.StartColumn);
        Assert.Equal(endLine, span.EndLineNumber);
        Assert.Equal(endColumn, span.EndColumn);
    }

    private static SourceSpan StringLiteralSpan(string source)
    {
        var (tokens, _) = Lexer.Tokenize(source);
        var token = Assert.Single(tokens.Where(token => token.Kind == TokenKind.StringLiteral));
        return new SourceSpan(
            token.Line,
            token.Column,
            token.Line,
            token.Column + Math.Max(token.Length, 1) - 1);
    }

    private static int ComparePosition(int line, int column, int otherLine, int otherColumn)
    {
        var lineComparison = line.CompareTo(otherLine);
        return lineComparison != 0 ? lineComparison : column.CompareTo(otherColumn);
    }

    private static bool SpansOverlap(SourceSpan left, SourceSpan right)
        => ComparePosition(left.StartLineNumber, left.StartColumn, right.EndLineNumber, right.EndColumn) <= 0
            && ComparePosition(right.StartLineNumber, right.StartColumn, left.EndLineNumber, left.EndColumn) <= 0;

    private static void AssertNoIdentifierSemanticSiteOverlaps(SemanticModel model, SourceSpan span)
    {
        Assert.DoesNotContain(
            model.IdentifierOccurrences,
            occurrence => SpansOverlap(occurrence.Span, span));
        Assert.DoesNotContain(
            model.IdentifierResolutions,
            resolution => SpansOverlap(resolution.Occurrence.Span, span));
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
    public void Build_OpenStringLiteralSugar_DoesNotEmitIdentifierSemanticsOnUrlSpan()
    {
        var source = """
            open 'https://katlang.org/algorithm.kat'
            1
            """;
        var remoteFiles = new Dictionary<string, string>
        {
            ["https://katlang.org/algorithm.kat"] = "\n\npublic Remote = 1"
        };

        var model = BuildModel(source, remoteFiles);
        var urlSpan = StringLiteralSpan(source);

        Assert.Null(model.FindResolutionAt(urlSpan.StartLineNumber, urlSpan.StartColumn));
        AssertNoIdentifierSemanticSiteOverlaps(model, urlSpan);
    }

    [Fact]
    public void Build_OpenMath_StillResolvesRealIdentifierTarget()
    {
        var model = BuildModel(
            """
            open Math
            Pi
            """);

        var mathReference = ResolutionAt(model, 1, 6);
        Assert.Equal(OccurrenceKind.OpenTargetReference, mathReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.OpenTarget, mathReference.Classification);
        Assert.Equal("Math", mathReference.Occurrence.Name);

        var piReference = ResolutionAt(model, 2, 1);
        Assert.Equal(OccurrenceKind.ResolveReference, piReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, piReference.Classification);
    }

    [Fact]
    public void Build_OpenLibSub_StillResolvesRealIdentifierTargets()
    {
        var model = BuildModel(
            """
            open Lib.Sub
            Lib = {
            public Sub = {
            public Value = 1
            }
            }
            Value
            """);

        var libDeclaration = Assert.Single(model.FindDeclarations("Lib"));
        var subDeclaration = Assert.Single(model.FindDeclarations("Sub"));
        var valueDeclaration = Assert.Single(model.FindDeclarations("Value"));

        var libOpenReference = ResolutionAt(model, 1, 6);
        Assert.Equal(OccurrenceKind.OpenTargetReference, libOpenReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.OpenTarget, libOpenReference.Classification);
        Assert.Equal(libDeclaration, libOpenReference.ResolvedDeclaration);

        var subOpenReference = ResolutionAt(model, 1, 10);
        Assert.Equal(OccurrenceKind.OpenTargetMemberReference, subOpenReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.OpenTarget, subOpenReference.Classification);
        Assert.Equal(subDeclaration, subOpenReference.ResolvedDeclaration);

        var valueReference = ResolutionAt(model, 7, 1);
        Assert.Equal(OccurrenceKind.ResolveReference, valueReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, valueReference.Classification);
        Assert.Equal(valueDeclaration, valueReference.ResolvedDeclaration);
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
    public void Build_DotCall_LengthOnImplicitParameter_IsBuiltin()
    {
        var model = BuildModel(
            """
            Args = 1, 2, 5
            Algo = p.length
            Algo(Args)
            """);

        var parameterReference = ResolutionAt(model, 2, 8);
        Assert.Equal(OccurrenceKind.ParameterReference, parameterReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, parameterReference.Classification);

        var lengthReference = ResolutionAt(model, 2, 10);
        Assert.Equal(OccurrenceKind.DotMemberReference, lengthReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, lengthReference.Classification);
        Assert.Null(lengthReference.ResolvedDeclaration);
        Assert.NotNull(lengthReference.ResolvedProperty);
        Assert.Equal(PropertyShape.Builtin, lengthReference.ResolvedProperty!.Shape);
    }

    [Fact]
    public void Build_DotCall_ReduceOnImplicitParameter_UsesBuiltinFallback()
    {
        var model = BuildModel(
            """
            CollectColumns((left, right), (leftList, rightList)) = ((left, leftList), (right, rightList))
            SplitPairs = pairs.reduce(CollectColumns, ('end', 'end'))
            """);

        var pairsReference = ResolutionAt(model, 2, 14);
        Assert.Equal(OccurrenceKind.ParameterReference, pairsReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, pairsReference.Classification);

        var reduceReference = ResolutionAt(model, 2, 20);
        Assert.Equal(OccurrenceKind.DotMemberReference, reduceReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, reduceReference.Classification);
        Assert.Null(reduceReference.ResolvedDeclaration);
        Assert.NotNull(reduceReference.ResolvedProperty);
        Assert.Equal(PropertyShape.Builtin, reduceReference.ResolvedProperty!.Shape);
        Assert.Equal(["collection", "step", "initial"], reduceReference.ResolvedProperty.Parameters.Select(parameter => parameter.Name).ToList());
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
    public void Build_OutputDotMember_IsClassifiedAsReservedName()
    {
        var source =
            """
            Algo(x) = {
              Output = x + 1
            }
            Algo.Output(6)
            """;

        var parseResult = Parser.Parse(source);
        Assert.True(parseResult.HasErrors);
        Assert.Contains(parseResult.Diagnostics, diagnostic => diagnostic.Message.Contains("Output is the designated result of an algorithm"));

        var model = SemanticModelBuilder.Build(parseResult);
        var outputReference = ResolutionAt(model, 4, 6);
        Assert.Equal(OccurrenceKind.DotMemberReference, outputReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ReservedName, outputReference.Classification);
        Assert.Null(outputReference.ResolvedDeclaration);
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
    public void Build_LoadedModuleDotMember_ResolvesExportedProperty()
    {
        var model = BuildModel(
            """
            A = load('https://katlang.org/algorithm.kat')
            A.X
            """,
            new Dictionary<string, string>
            {
                ["https://katlang.org/algorithm.kat"] = "\n\npublic X = 1"
            });

        var aDeclaration = Assert.Single(model.FindDeclarations("A"));
        var aReference = ResolutionAt(model, 2, 1);
        Assert.Equal(IdentifierClassification.PropertyReference, aReference.Classification);
        Assert.Equal(aDeclaration, aReference.ResolvedDeclaration);

        var xDeclaration = Assert.Single(model.FindDeclarations("X"));
        var xReference = ResolutionAt(model, 2, 3);
        Assert.Equal(OccurrenceKind.DotMemberReference, xReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, xReference.Classification);
        Assert.Equal(xDeclaration, xReference.ResolvedDeclaration);
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
    public void Build_RuntimeStringLiteral_DoesNotEmitIdentifierSemanticsOnStringSpan()
    {
        var source = """
            Label = 'hello'
            Label
            """;

        var model = BuildModel(source);
        var stringSpan = StringLiteralSpan(source);

        Assert.Null(model.FindResolutionAt(stringSpan.StartLineNumber, stringSpan.StartColumn));
        AssertNoIdentifierSemanticSiteOverlaps(model, stringSpan);

        var labelDeclaration = Assert.Single(model.FindDeclarations("Label"));
        var labelReference = ResolutionAt(model, 2, 1);
        Assert.Equal(IdentifierClassification.PropertyReference, labelReference.Classification);
        Assert.Equal(labelDeclaration, labelReference.ResolvedDeclaration);
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
    public void Build_AliasToLoadedModule_DoesNotUseLegacyLoadFallback()
    {
        var model = BuildModel(
            """
            Lib = load('https://katlang.org/algorithm.kat')
            Alias = Lib
            Alias.X
            """,
            new Dictionary<string, string>
            {
                ["https://katlang.org/algorithm.kat"] = "\n\npublic X = 1"
            });

        var aliasReference = ResolutionAt(model, 3, 1);
        Assert.Equal(IdentifierClassification.PropertyReference, aliasReference.Classification);

        var xReference = ResolutionAt(model, 3, 7);
        Assert.Equal(OccurrenceKind.DotMemberReference, xReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Unresolved, xReference.Classification);
        Assert.Null(xReference.ResolvedDeclaration);
    }

    [Fact]
    public void Build_UnresolvedLoadSyntax_ThrowsInvariantViolation()
    {
        var parseResult = Parser.ParseSyntax(
            """
            Lib = load('https://katlang.org/algorithm.kat')
            Lib.X
            """);

        var exception = Assert.Throws<InvalidOperationException>(() => SemanticModelBuilder.Build(parseResult));
        Assert.Contains("Unresolved load syntax", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void Build_OrdinaryPropertyInfo_ExposesExplicitParametersAndHoverResolution()
    {
        var model = BuildModel(
            """
            Add(x) = x + 1
            Add(5)
            """);

        var property = SingleProperty(model, "Add");
        Assert.Equal(PropertyShape.Ordinary, property.Shape);
        Assert.False(property.IsPublic);

        var parameter = Assert.Single(property.Parameters);
        Assert.Equal("x", parameter.Name);
        Assert.Equal(PropertyParameterKind.Explicit, parameter.Kind);
        Assert.NotNull(parameter.Span);
        AssertSpan(parameter.Span!, 1, 5, 1, 5);
        Assert.Empty(property.ConditionalBranches);

        var definitionProperty = PropertyAt(model, 1, 1);
        var referenceResolution = ResolutionAt(model, 2, 1);
        Assert.Same(property, definitionProperty);
        Assert.Same(property, referenceResolution.ResolvedProperty);
        Assert.Same(property, model.FindPropertyByDeclaration(property.Declaration!));
    }

    [Fact]
    public void Build_OrdinaryPropertyInfo_ExposesImplicitParametersInCallableOrder()
    {
        var model = BuildModel(
            """
            Square = x * y
            Square
            """);

        var property = SingleProperty(model, "Square");
        Assert.Equal(PropertyShape.Ordinary, property.Shape);
        Assert.Equal(["x", "y"], property.Parameters.Select(parameter => parameter.Name).ToList());
        Assert.Equal([PropertyParameterKind.Implicit, PropertyParameterKind.Implicit], property.Parameters.Select(parameter => parameter.Kind).ToList());
        Assert.All(property.Parameters, parameter => Assert.Null(parameter.Span));
    }

    [Fact]
    public void Build_OrdinaryPropertyInfo_ExposesMixedExplicitAndImplicitParameters()
    {
        var model = BuildModel("Add(x) = x + y");

        var property = SingleProperty(model, "Add");
        Assert.Equal(PropertyShape.Ordinary, property.Shape);
        Assert.Equal(["x", "y"], property.Parameters.Select(parameter => parameter.Name).ToList());
        Assert.Equal(PropertyParameterKind.Explicit, property.Parameters[0].Kind);
        Assert.Equal(PropertyParameterKind.Implicit, property.Parameters[1].Kind);
        Assert.NotNull(property.Parameters[0].Span);
        Assert.Null(property.Parameters[1].Span);
    }

    [Fact]
    public void Build_ExplicitOutput_RemainsReserved_And_OuterParametersStayOnAlgorithmMetadata()
    {
        var model = BuildModel(
            """
            Algo(x) = {
            Output = x + 1
            }
            Algo(6)
            """);

        var algo = SingleProperty(model, "Algo");
        Assert.Equal(PropertyShape.Ordinary, algo.Shape);
        var parameter = Assert.Single(algo.Parameters);
        Assert.Equal("x", parameter.Name);
        Assert.Equal(PropertyParameterKind.Explicit, parameter.Kind);
        Assert.NotNull(parameter.Span);

        Assert.Empty(model.FindProperties("Output"));

        var outputDeclaration = Assert.Single(model.FindDeclarations("Output"));
        Assert.Equal(OccurrenceKind.ReservedNameDefinition, outputDeclaration.Kind);

        var outputResolution = ResolutionAt(model, 2, 1);
        Assert.Equal(IdentifierClassification.ReservedName, outputResolution.Classification);
        Assert.Equal(outputDeclaration, outputResolution.ResolvedDeclaration);

        var xReference = ResolutionAt(model, 2, 10);
        Assert.Equal(IdentifierClassification.ExplicitParameterReference, xReference.Classification);

        var callReference = ResolutionAt(model, 4, 1);
        Assert.Same(algo, callReference.ResolvedProperty);
    }

    [Fact]
    public void Build_ConditionalPropertyInfo_ExposesBranchHeadsInSourceOrder()
    {
        var model = BuildModel(
            """
            F(1) = 100
            F(x) = 0
            F(1)
            """);

        var property = SingleProperty(model, "F");
        Assert.Equal(PropertyShape.Conditional, property.Shape);
        Assert.Empty(property.Parameters);
        Assert.Equal(["F(1)", "F(x)"], property.ConditionalBranches.Select(branch => branch.HeadText).ToList());
        Assert.Empty(property.ConditionalBranches[0].BinderNames);
        Assert.Equal(["x"], property.ConditionalBranches[1].BinderNames.ToList());
        Assert.Equal([1, 2], property.ConditionalBranches.Select(branch => branch.HeadSpan?.StartLineNumber).ToList());

        var declarations = model.FindDeclarations("F").ToList();
        Assert.Equal(2, declarations.Count);
        Assert.Same(property, model.FindPropertyByDeclaration(declarations[0]));
        Assert.Same(property, model.FindPropertyByDeclaration(declarations[1]));

        var referenceResolution = ResolutionAt(model, 3, 1);
        Assert.Same(property, referenceResolution.ResolvedProperty);
    }

    [Fact]
    public void Build_SinglePlainBinderClause_UsesActualUserAlgorithmShape()
    {
        var model = BuildModel(
            """
            F(x) = x
            F(1)
            """);

        var property = SingleProperty(model, "F");
        Assert.Equal(PropertyShape.Ordinary, property.Shape);
        Assert.Equal(["x"], property.Parameters.Select(parameter => parameter.Name).ToList());
        Assert.Empty(property.ConditionalBranches);
    }

    [Fact]
    public void Build_SingleLiteralClause_RemainsConditional()
    {
        var model = BuildModel(
            """
            F(1) = 1
            F(1)
            """);

        var property = SingleProperty(model, "F");
        Assert.Equal(PropertyShape.Conditional, property.Shape);
        Assert.Empty(property.Parameters);
        Assert.Single(property.ConditionalBranches);
        Assert.Equal("F(1)", property.ConditionalBranches[0].HeadText);
    }

    [Fact]
    public void Build_BuiltinPropertyInfo_ExposesConservativeShape()
    {
        var model = BuildModel("Math.Sqrt");

        var property = PropertyAt(model, 1, 6);
        Assert.Equal("Sqrt", property.Name);
        Assert.Equal(PropertyShape.Builtin, property.Shape);
        Assert.Null(property.Declaration);
        Assert.Equal(["x"], property.Parameters.Select(parameter => parameter.Name).ToList());
        Assert.All(property.Parameters, parameter => Assert.Equal(PropertyParameterKind.Explicit, parameter.Kind));
        Assert.Empty(property.ConditionalBranches);
        Assert.Contains(model.PropertyInfos, candidate => ReferenceEquals(candidate, property));
    }

    [Fact]
    public void Build_PropertyDefinitionAndReferenceShareResolvedPropertyInfo()
    {
        var model = BuildModel(
            """
            Value = 1
            A = Value + 1
            """);

        var definitionResolution = ResolutionAt(model, 1, 1);
        var referenceResolution = ResolutionAt(model, 2, 5);
        var property = SingleProperty(model, "Value");

        Assert.Equal(IdentifierClassification.PropertyDefinition, definitionResolution.Classification);
        Assert.Equal(IdentifierClassification.PropertyReference, referenceResolution.Classification);
        Assert.Same(property, definitionResolution.ResolvedProperty);
        Assert.Same(property, referenceResolution.ResolvedProperty);
        Assert.Same(property, model.FindPropertyByDeclaration(definitionResolution.ResolvedDeclaration!));
    }

    [Fact]
    public void Build_ConditionalPropertyInfo_PreservesGroupedPatternShape()
    {
        var model = BuildModel(
            """
            Pair(1, (x, y)) = x
            Pair(1, (2, 3))
            """);

        var property = SingleProperty(model, "Pair");
        Assert.Equal(PropertyShape.Conditional, property.Shape);
        var branch = Assert.Single(property.ConditionalBranches);
        Assert.Equal("Pair(1, (x, y))", branch.HeadText);
        Assert.Equal(["x", "y"], branch.BinderNames.ToList());
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