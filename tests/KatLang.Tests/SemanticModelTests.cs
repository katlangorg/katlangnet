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

    private static void AssertPropertySignature(PropertyInfo property, string expectedDisplaySignature, params string[] expectedParameters)
    {
        Assert.Equal(expectedDisplaySignature, property.DisplaySignature);
        Assert.Equal(expectedParameters, property.Parameters.Select(parameter => parameter.DisplayName).ToList());
    }

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
        var token = Assert.Single(tokens, token => token.Kind == TokenKind.StringLiteral);
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
    public void Build_IdentifiersInsideListLiterals_ProduceResolutions()
    {
        var model = BuildModel("Alpha = 1\nBeta = 2\n[Alpha, Beta, 3]");

        var alphaDeclaration = Assert.Single(model.FindDeclarations("Alpha"));
        var alphaReference = Assert.Single(
            model.IdentifierResolutions,
            resolution => resolution.Occurrence.Name == "Alpha"
                && resolution.Occurrence.Kind == OccurrenceKind.ResolveReference);
        Assert.Equal(IdentifierClassification.PropertyReference, alphaReference.Classification);
        Assert.Equal(alphaDeclaration, alphaReference.ResolvedDeclaration);
        AssertSpan(alphaReference.Occurrence.Span, 3, 2, 3, 6);

        var betaReference = Assert.Single(
            model.IdentifierResolutions,
            resolution => resolution.Occurrence.Name == "Beta"
                && resolution.Occurrence.Kind == OccurrenceKind.ResolveReference);
        AssertSpan(betaReference.Occurrence.Span, 3, 9, 3, 12);
    }

    [Fact]
    public void Build_SourceCoordinates_AreOneBasedAndEndInclusive()
    {
        var model = BuildModel("Alpha = 123\nAlpha");

        var alphaDeclaration = Assert.Single(model.FindDeclarations("Alpha"));
        Assert.Equal(OccurrenceKind.PropertyDefinition, alphaDeclaration.Kind);
        AssertSpan(alphaDeclaration.Span, 1, 1, 1, 5);

        var alphaReference = Assert.Single(
            model.IdentifierResolutions,
            resolution => resolution.Occurrence.Name == "Alpha"
                && resolution.Occurrence.Kind == OccurrenceKind.ResolveReference);
        Assert.Equal(IdentifierClassification.PropertyReference, alphaReference.Classification);
        Assert.Equal(alphaDeclaration, alphaReference.ResolvedDeclaration);
        AssertSpan(alphaReference.Occurrence.Span, 2, 1, 2, 5);

        Assert.Equal(alphaReference, model.FindResolutionAt(2, 1));
        Assert.Equal(alphaReference, model.FindResolutionAt(2, 3));
        Assert.Equal(alphaReference, model.FindResolutionAt(2, 5));
        Assert.Null(model.FindResolutionAt(2, 6));
    }

    [Fact]
    public void Build_PropertyOnlyProgram_RemainsValidPropertyDefinition()
    {
        var parseResult = Parser.Parse("T = 4");
        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(d => d.Message)));

        var model = SemanticModelBuilder.Build(parseResult);

        var declaration = Assert.Single(model.FindDeclarations("T"));
        Assert.Equal(OccurrenceKind.PropertyDefinition, declaration.Kind);
        AssertSpan(declaration.Span, 1, 1, 1, 1);

        var resolution = ResolutionAt(model, 1, 1);
        Assert.Equal(IdentifierClassification.PropertyDefinition, resolution.Classification);
        Assert.Equal(declaration, resolution.ResolvedDeclaration);
        Assert.NotNull(resolution.ResolvedProperty);
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
    public void Build_PrefixRestAndPostfixSpread_KeepDistinctSourceBackedIdentifierSites()
    {
        const string source =
            """
            Pack(...items) = items
            Values = (1, 2)
            Pack(Values...)
            """;

        var parseResult = Parser.Parse(source);
        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(d => d.Message)));
        var model = SemanticModelBuilder.Build(parseResult);

        var itemsDeclaration = Assert.Single(model.FindDeclarations("items"));
        Assert.Equal(OccurrenceKind.ExplicitParameterDefinition, itemsDeclaration.Kind);
        AssertSpan(itemsDeclaration.Span, 1, 9, 1, 13);
        Assert.Equal(itemsDeclaration, ResolutionAt(model, 1, 18).ResolvedDeclaration);

        var pack = SingleProperty(model, "Pack");
        AssertPropertySignature(pack, "Pack(...items)", "...items");

        var valuesDeclaration = Assert.Single(model.FindDeclarations("Values"));
        var spreadOperand = ResolutionAt(model, 3, 6);
        Assert.Equal(IdentifierClassification.PropertyReference, spreadOperand.Classification);
        Assert.Equal(valuesDeclaration, spreadOperand.ResolvedDeclaration);

        var packAlgorithm = Assert.Single(
            parseResult.Root.Properties,
            static property => property.Name == "Pack").Value;
        var parameter = Assert.Single(packAlgorithm.Parameters);
        Assert.Equal(RestBindingSyntax.Prefix, parameter.RestSyntax);
        AssertSpan(Assert.IsType<SourceSpan>(parameter.RestMarkerSpan), 1, 6, 1, 8);
        AssertNoIdentifierSemanticSiteOverlaps(model, Assert.IsType<SourceSpan>(parameter.RestMarkerSpan));

        var call = Assert.IsType<Expr.Call>(Assert.Single(parseResult.Root.Output));
        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(call.Args.Output));
        Assert.IsType<Expr.Resolve>(spread.Operand);
    }

    [Fact]
    public void Build_DeconstructionAssignment_TracksSourceBackedTargetDeclarations()
    {
        var model = BuildModel(
            """
            A = 1, 2, 3, 4, 5
            x, ...y, z = A
            x + y.sum + z
            """);

        var xDeclaration = Assert.Single(model.FindDeclarations("x"));
        Assert.Equal(OccurrenceKind.PropertyDefinition, xDeclaration.Kind);
        AssertSpan(xDeclaration.Span, 2, 1, 2, 1);

        var yDeclaration = Assert.Single(model.FindDeclarations("y"));
        Assert.Equal(OccurrenceKind.PropertyDefinition, yDeclaration.Kind);
        AssertSpan(yDeclaration.Span, 2, 7, 2, 7);

        var zDeclaration = Assert.Single(model.FindDeclarations("z"));
        Assert.Equal(OccurrenceKind.PropertyDefinition, zDeclaration.Kind);
        AssertSpan(zDeclaration.Span, 2, 10, 2, 10);

        // The synthetic shared-source property and the helper constructs that bind
        // the right-hand side carry no source spans, so no synthetic property ever
        // surfaces as a declaration or as property metadata, while the real
        // deconstructed variables remain visible.
        Assert.DoesNotContain(model.PropertyInfos, propertyInfo => propertyInfo.Name.StartsWith('$'));
        Assert.Single(model.FindProperties("x"));
        Assert.Single(model.FindProperties("y"));
        Assert.Single(model.FindProperties("z"));

        // The right-hand side resolves to the source property exactly once.
        var aDeclaration = Assert.Single(model.FindDeclarations("A"));
        var aReference = ResolutionAt(model, 2, 14);
        Assert.Equal(IdentifierClassification.PropertyReference, aReference.Classification);
        Assert.Equal(aDeclaration, aReference.ResolvedDeclaration);

        // Later uses resolve to the deconstructed property declarations.
        Assert.Equal(xDeclaration, ResolutionAt(model, 3, 1).ResolvedDeclaration);
    }

    [Fact]
    public void Build_RepeatedOrdinaryBinder_ReferencesFirstDeclaration()
    {
        var model = BuildModel("F(x, x) = x");

        var declaration = Assert.Single(model.FindDeclarations("x"));
        AssertSpan(declaration.Span, 1, 3, 1, 3);

        var repeatedBinder = ResolutionAt(model, 1, 6);
        Assert.Equal(OccurrenceKind.ParameterReference, repeatedBinder.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ExplicitParameterReference, repeatedBinder.Classification);
        Assert.Equal(declaration, repeatedBinder.ResolvedDeclaration);

        var bodyReference = ResolutionAt(model, 1, 11);
        Assert.Equal(declaration, bodyReference.ResolvedDeclaration);
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
    public void Build_RepeatedConditionalBinder_ReferencesFirstBranchDeclaration()
    {
        var model = BuildModel(
            """
            Equal(x, x) = 1
            Equal(x, y) = 0
            """);

        var firstBranchDeclaration = model.FindDeclarations("x")
            .Single(declaration => declaration.Span.StartLineNumber == 1);
        AssertSpan(firstBranchDeclaration.Span, 1, 7, 1, 7);

        var repeatedBinder = ResolutionAt(model, 1, 10);
        Assert.Equal(OccurrenceKind.ParameterReference, repeatedBinder.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ConditionalBinderReference, repeatedBinder.Classification);
        Assert.Equal(firstBranchDeclaration, repeatedBinder.ResolvedDeclaration);
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

        var parameterFallbackMember = ResolutionAt(model, 5, 12);
        Assert.Equal(OccurrenceKind.DotMemberReference, parameterFallbackMember.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, parameterFallbackMember.Classification);
        Assert.Equal(propDeclaration, parameterFallbackMember.ResolvedDeclaration);

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
    public void Build_DotCall_ImplicitParameterReceiverUsesLexicalPropertyFallback()
    {
        var model = BuildModel(
            """
            public _x = 0
            public _y = 1
            X = v:_x
            Y = v:_y
            public Vector = x, y
            public Neg = Vector(-v:_x, -v:_y)
            public Scale = Vector(q~*v:_x, q*v:_y)
            public Add(...vectors) = Vector(vectors.map(X).sum, vectors.map(Y).sum)
            public Subtract = a.Add(b.Neg)
            """);

        var addDeclaration = Assert.Single(model.FindDeclarations("Add"));
        var negDeclaration = Assert.Single(model.FindDeclarations("Neg"));

        var addReference = ResolutionAt(model, 9, 21);
        Assert.Equal(OccurrenceKind.DotMemberReference, addReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, addReference.Classification);
        Assert.Equal(addDeclaration, addReference.ResolvedDeclaration);
        Assert.Equal("Add", addReference.ResolvedProperty?.Name);

        var negReference = ResolutionAt(model, 9, 27);
        Assert.Equal(OccurrenceKind.DotMemberReference, negReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, negReference.Classification);
        Assert.Equal(negDeclaration, negReference.ResolvedDeclaration);
        Assert.Equal("Neg", negReference.ResolvedProperty?.Name);
    }

    [Fact]
    public void Build_DotCall_UnknownMemberOnImplicitParameterReceiverRemainsUnresolved()
    {
        var model = BuildModel("public Test = a.Unknown");

        var parameterReference = ResolutionAt(model, 1, 15);
        Assert.Equal(OccurrenceKind.ParameterReference, parameterReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, parameterReference.Classification);

        var unknownReference = ResolutionAt(model, 1, 17);
        Assert.Equal(OccurrenceKind.DotMemberReference, unknownReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Unresolved, unknownReference.Classification);
        Assert.Null(unknownReference.ResolvedDeclaration);
        Assert.Null(unknownReference.ResolvedProperty);
    }

    [Fact]
    public void Build_DotCall_SequenceSpreadDoesNotMergePropertySurface()
    {
        var model = BuildModel(
            """
            public A = {
            public X = 1
            10
            }
            public B = {
            public Y = 2
            20
            }
            C = A...B
            C.X
            C.Y
            """);

        Assert.Single(model.FindDeclarations("X"));
        Assert.Single(model.FindDeclarations("Y"));

        var xReference = ResolutionAt(model, 10, 3);
        Assert.Equal(OccurrenceKind.DotMemberReference, xReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Unresolved, xReference.Classification);
        Assert.Null(xReference.ResolvedDeclaration);
        Assert.Null(xReference.ResolvedProperty);

        var yReference = ResolutionAt(model, 11, 3);
        Assert.Equal(OccurrenceKind.DotMemberReference, yReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Unresolved, yReference.Classification);
        Assert.Null(yReference.ResolvedDeclaration);
        Assert.Null(yReference.ResolvedProperty);
    }

    [Fact]
    public void Build_DotCall_ArityOnImplicitParameter_RemainsUnresolved()
    {
        var model = BuildModel(
            """
            Args = 1, 2, 5
            Algo = p.arity
            Algo(Args)
            """);

        var parameterReference = ResolutionAt(model, 2, 8);
        Assert.Equal(OccurrenceKind.ParameterReference, parameterReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, parameterReference.Classification);

        var arityReference = ResolutionAt(model, 2, 10);
        Assert.Equal(OccurrenceKind.DotMemberReference, arityReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Unresolved, arityReference.Classification);
        Assert.Null(arityReference.ResolvedDeclaration);
        Assert.Null(arityReference.ResolvedProperty);
    }

    [Fact]
    public void Build_DotCall_LengthOnImplicitParameter_RemainsUnresolved()
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
        Assert.Equal(IdentifierClassification.Unresolved, lengthReference.Classification);
        Assert.Null(lengthReference.ResolvedDeclaration);
        Assert.Null(lengthReference.ResolvedProperty);
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
        AssertPropertySignature(reduceReference.ResolvedProperty, "collection.reduce(reducer, initial)", "reducer", "initial");
        Assert.Equal("reduce(collection, reducer, initial)", reduceReference.ResolvedProperty.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal(["collection", "reducer", "initial"], reduceReference.ResolvedProperty.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
    }

    [Fact]
    public void Build_DotCall_OrderDescOnImplicitParameter_UsesBuiltinFallback()
    {
        var model = BuildModel(
            """
            Sorted = values.orderDesc
            """);

        var valuesReference = ResolutionAt(model, 1, 10);
        Assert.Equal(OccurrenceKind.ParameterReference, valuesReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, valuesReference.Classification);

        var orderReference = ResolutionAt(model, 1, 17);
        Assert.Equal(OccurrenceKind.DotMemberReference, orderReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, orderReference.Classification);
        Assert.Null(orderReference.ResolvedDeclaration);
        Assert.NotNull(orderReference.ResolvedProperty);
        Assert.Equal(PropertyShape.Builtin, orderReference.ResolvedProperty!.Shape);
        Assert.Empty(orderReference.ResolvedProperty.Parameters);
    }

    [Fact]
    public void Build_DotCall_OrderOnInlineBlockReceiver_UsesBuiltinFallback()
    {
        var model = BuildModel(
            """
            Sorted = {1, 2, 3}.order
            """);

        var orderReference = ResolutionAt(model, 1, 20);
        Assert.Equal(OccurrenceKind.DotMemberReference, orderReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, orderReference.Classification);
        Assert.Null(orderReference.ResolvedDeclaration);
        Assert.NotNull(orderReference.ResolvedProperty);
        Assert.Equal(PropertyShape.Builtin, orderReference.ResolvedProperty!.Shape);
        Assert.Empty(orderReference.ResolvedProperty.Parameters);
    }

    [Fact]
    public void Build_InlineOpenBlock_UsesPreludeBuiltinsWithoutOpenerShadowing()
    {
        var model = BuildModel(
            """
            open {
            public Use = {1, 2}.sum
            }
            sum = 99
            Use
            """);

        var rootSumDeclaration = Assert.Single(model.FindDeclarations("sum"));
        AssertSpan(rootSumDeclaration.Span, 4, 1, 4, 3);

        var sumReference = ResolutionAt(model, 2, 21);
        Assert.Equal(OccurrenceKind.DotMemberReference, sumReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, sumReference.Classification);
        Assert.Null(sumReference.ResolvedDeclaration);
        Assert.NotNull(sumReference.ResolvedProperty);
        Assert.Equal(PropertyShape.Builtin, sumReference.ResolvedProperty!.Shape);
        Assert.Empty(sumReference.ResolvedProperty.Parameters);

        var useDeclaration = Assert.Single(model.FindDeclarations("Use"));
        var useReference = ResolutionAt(model, 5, 1);
        Assert.Equal(IdentifierClassification.PropertyReference, useReference.Classification);
        Assert.Equal(useDeclaration, useReference.ResolvedDeclaration);
    }

    [Fact]
    public void Build_DotCall_CountOnSequenceValuePropertyReceiver_UsesBuiltinFallback()
    {
        var model = BuildModel(
            """
            Values = (1, 2, 3)
            Values.count
            """);

        var valuesDeclaration = Assert.Single(model.FindDeclarations("Values"));
        AssertSpan(valuesDeclaration.Span, 1, 1, 1, 6);

        var valuesReference = ResolutionAt(model, 2, 1);
        Assert.Equal(OccurrenceKind.ResolveReference, valuesReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, valuesReference.Classification);
        Assert.Equal(valuesDeclaration, valuesReference.ResolvedDeclaration);

        var countReference = ResolutionAt(model, 2, 8);
        Assert.Equal(OccurrenceKind.DotMemberReference, countReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, countReference.Classification);
        Assert.Null(countReference.ResolvedDeclaration);
        Assert.NotNull(countReference.ResolvedProperty);
        Assert.Equal(PropertyShape.Builtin, countReference.ResolvedProperty!.Shape);
        Assert.Empty(countReference.ResolvedProperty.Parameters);
    }

    [Fact]
    public void Build_EmptyParens_CreateNoIdentifierResolutionSites()
    {
        var model = BuildModel(
            """
            ()
            (())
            """);

        // The empty sequence value `()` is a structural literal, not a named
        // reference, so it produces no identifier resolution sites.
        Assert.Empty(model.FindResolutions("empty"));
    }

    [Fact]
    public void Build_DotCall_ContainsOnSequenceValuePropertyReceiver_UsesBuiltinFallback()
    {
        var model = BuildModel(
            """
            Values = (1, 2, 3)
            Values.contains(2)
            """);

        var valuesDeclaration = Assert.Single(model.FindDeclarations("Values"));
        AssertSpan(valuesDeclaration.Span, 1, 1, 1, 6);

        var valuesReference = ResolutionAt(model, 2, 1);
        Assert.Equal(OccurrenceKind.ResolveReference, valuesReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, valuesReference.Classification);
        Assert.Equal(valuesDeclaration, valuesReference.ResolvedDeclaration);

        var containsReference = ResolutionAt(model, 2, 8);
        Assert.Equal(OccurrenceKind.DotMemberReference, containsReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, containsReference.Classification);
        Assert.Null(containsReference.ResolvedDeclaration);
        Assert.NotNull(containsReference.ResolvedProperty);
        Assert.Equal(PropertyShape.Builtin, containsReference.ResolvedProperty!.Shape);
        Assert.Equal(["item"], containsReference.ResolvedProperty.Parameters.Select(parameter => parameter.Name).ToList());
    }

    [Fact]
    public void Build_DotCall_TakeOnIndexedReceiver_UsesBuiltinFallback()
    {
        var model = BuildModel(
            """
            Data = (1, 2, 3), (4, 5)
            (Data:0).take(2)
            """);

        var takeReference = ResolutionAt(model, 2, 10);
        Assert.Equal(OccurrenceKind.DotMemberReference, takeReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, takeReference.Classification);
        Assert.Null(takeReference.ResolvedDeclaration);
        Assert.NotNull(takeReference.ResolvedProperty);
        Assert.Equal(PropertyShape.Builtin, takeReference.ResolvedProperty!.Shape);
        AssertPropertySignature(takeReference.ResolvedProperty, "collection.take(count)", "count");
        Assert.Equal("take(collection, count)", takeReference.ResolvedProperty.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal(["collection", "count"], takeReference.ResolvedProperty.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
    }

    [Fact]
    public void Build_PlainCall_Take_UsesCollectionSurfaceSignature()
    {
        var model = BuildModel("take((1, 2, 3), 2)");

        var takeReference = ResolutionAt(model, 1, 1);
        Assert.Equal(OccurrenceKind.ResolveReference, takeReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, takeReference.Classification);
        Assert.Null(takeReference.ResolvedDeclaration);
        Assert.NotNull(takeReference.ResolvedProperty);
        Assert.Equal(PropertyShape.Builtin, takeReference.ResolvedProperty!.Shape);
        AssertPropertySignature(takeReference.ResolvedProperty, "take(collection, count)", "collection", "count");
        Assert.Equal("collection.take(count)", takeReference.ResolvedProperty.GetDisplaySignature(PropertyCallStyle.Dot));
        Assert.Equal(["count"], takeReference.ResolvedProperty.GetParameters(PropertyCallStyle.Dot).Select(parameter => parameter.DisplayName).ToList());
    }

    [Fact]
    public void Build_PlainCall_Skip_UsesCollectionSurfaceSignature()
    {
        var model = BuildModel("skip((1, 2, 3), 1)");

        var skipReference = ResolutionAt(model, 1, 1);
        Assert.Equal(OccurrenceKind.ResolveReference, skipReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, skipReference.Classification);
        Assert.Null(skipReference.ResolvedDeclaration);
        Assert.NotNull(skipReference.ResolvedProperty);
        Assert.Equal(PropertyShape.Builtin, skipReference.ResolvedProperty!.Shape);
        AssertPropertySignature(skipReference.ResolvedProperty, "skip(collection, count)", "collection", "count");
        Assert.Equal("collection.skip(count)", skipReference.ResolvedProperty.GetDisplaySignature(PropertyCallStyle.Dot));
        Assert.Equal(["count"], skipReference.ResolvedProperty.GetParameters(PropertyCallStyle.Dot).Select(parameter => parameter.DisplayName).ToList());
    }

    [Fact]
    public void Build_DotCall_Take_UsesDotSurfaceSignature()
    {
        var model = BuildModel("(1, 2, 3).take(2)");

        var takeReference = ResolutionAt(model, 1, 11);
        Assert.Equal(OccurrenceKind.DotMemberReference, takeReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, takeReference.Classification);
        Assert.Null(takeReference.ResolvedDeclaration);
        Assert.NotNull(takeReference.ResolvedProperty);
        Assert.Equal(PropertyShape.Builtin, takeReference.ResolvedProperty!.Shape);
        AssertPropertySignature(takeReference.ResolvedProperty, "collection.take(count)", "count");
        Assert.Equal("take(collection, count)", takeReference.ResolvedProperty.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal(["collection", "count"], takeReference.ResolvedProperty.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
    }

    [Fact]
    public void Build_DotCall_Skip_UsesDotSurfaceSignature()
    {
        var model = BuildModel("(1, 2, 3).skip(1)");

        var skipReference = ResolutionAt(model, 1, 11);
        Assert.Equal(OccurrenceKind.DotMemberReference, skipReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, skipReference.Classification);
        Assert.Null(skipReference.ResolvedDeclaration);
        Assert.NotNull(skipReference.ResolvedProperty);
        Assert.Equal(PropertyShape.Builtin, skipReference.ResolvedProperty!.Shape);
        AssertPropertySignature(skipReference.ResolvedProperty, "collection.skip(count)", "count");
        Assert.Equal("skip(collection, count)", skipReference.ResolvedProperty.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal(["collection", "count"], skipReference.ResolvedProperty.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
    }

    [Fact]
    public void Build_DotCall_FirstOnImplicitParameter_UsesBuiltinFallback()
    {
        var model = BuildModel(
            """
            Selected = values.first
            """);

        var valuesReference = ResolutionAt(model, 1, 12);
        Assert.Equal(OccurrenceKind.ParameterReference, valuesReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, valuesReference.Classification);

        var firstReference = ResolutionAt(model, 1, 19);
        Assert.Equal(OccurrenceKind.DotMemberReference, firstReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, firstReference.Classification);
        Assert.Null(firstReference.ResolvedDeclaration);
        Assert.NotNull(firstReference.ResolvedProperty);
        Assert.Equal(PropertyShape.Builtin, firstReference.ResolvedProperty!.Shape);
        Assert.Empty(firstReference.ResolvedProperty.Parameters);
    }

    [Fact]
    public void Build_DotCall_LastOnImplicitParameter_UsesBuiltinFallback()
    {
        var model = BuildModel(
            """
            Selected = values.last
            """);

        var valuesReference = ResolutionAt(model, 1, 12);
        Assert.Equal(OccurrenceKind.ParameterReference, valuesReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, valuesReference.Classification);

        var lastReference = ResolutionAt(model, 1, 19);
        Assert.Equal(OccurrenceKind.DotMemberReference, lastReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, lastReference.Classification);
        Assert.Null(lastReference.ResolvedDeclaration);
        Assert.NotNull(lastReference.ResolvedProperty);
        Assert.Equal(PropertyShape.Builtin, lastReference.ResolvedProperty!.Shape);
        Assert.Empty(lastReference.ResolvedProperty.Parameters);
    }

    [Fact]
    public void Build_DotCall_DistinctOnImplicitParameter_UsesBuiltinFallback()
    {
        var model = BuildModel(
            """
            Selected = values.distinct
            """);

        var valuesReference = ResolutionAt(model, 1, 12);
        Assert.Equal(OccurrenceKind.ParameterReference, valuesReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, valuesReference.Classification);

        var distinctReference = ResolutionAt(model, 1, 19);
        Assert.Equal(OccurrenceKind.DotMemberReference, distinctReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, distinctReference.Classification);
        Assert.Null(distinctReference.ResolvedDeclaration);
        Assert.NotNull(distinctReference.ResolvedProperty);
        Assert.Equal(PropertyShape.Builtin, distinctReference.ResolvedProperty!.Shape);
        Assert.Empty(distinctReference.ResolvedProperty.Parameters);
    }

    [Fact]
    public void Build_DotCall_TakeOnImplicitParameter_UsesBuiltinFallback()
    {
        var model = BuildModel(
            """
            Selected = values.take(2)
            """);

        var valuesReference = ResolutionAt(model, 1, 12);
        Assert.Equal(OccurrenceKind.ParameterReference, valuesReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, valuesReference.Classification);

        var takeReference = ResolutionAt(model, 1, 19);
        Assert.Equal(OccurrenceKind.DotMemberReference, takeReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, takeReference.Classification);
        Assert.Null(takeReference.ResolvedDeclaration);
        Assert.NotNull(takeReference.ResolvedProperty);
        Assert.Equal(PropertyShape.Builtin, takeReference.ResolvedProperty!.Shape);
        AssertPropertySignature(takeReference.ResolvedProperty, "collection.take(count)", "count");
        Assert.Equal("take(collection, count)", takeReference.ResolvedProperty.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal(["collection", "count"], takeReference.ResolvedProperty.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
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
            Sum = Algo.while(1, 2, 0) : 2
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
    public void Build_OrdinaryPropertyInfo_DisplaysVariadicExplicitParameter()
    {
        var model = BuildModel("Collect(...list) = list");

        var property = SingleProperty(model, "Collect");
        Assert.Equal("Collect(...list)", property.DisplaySignature);
        var parameter = Assert.Single(property.Parameters);
        Assert.Equal("list", parameter.Name);
        Assert.Equal("...list", parameter.DisplayName);
        Assert.Equal(PropertyParameterKind.Explicit, parameter.Kind);
        Assert.True(parameter.IsVariadic);
    }

    [Fact]
    public void Build_OrdinaryPropertyInfo_DisplaysVariadicParameterBeforeSuffix()
    {
        var model = BuildModel("Scale(...values, factor) = values.map{n * factor}");

        var property = SingleProperty(model, "Scale");
        Assert.Equal("Scale(...values, factor)", property.DisplaySignature);
        Assert.Equal(["values", "factor"], property.Parameters.Select(parameter => parameter.Name).ToList());
        Assert.Equal(["...values", "factor"], property.Parameters.Select(parameter => parameter.DisplayName).ToList());
        Assert.Equal(["...values", "factor"], property.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
        Assert.Equal([PropertyParameterKind.Explicit, PropertyParameterKind.Explicit], property.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.Kind).ToList());
        Assert.Equal([true, false], property.Parameters.Select(parameter => parameter.IsVariadic).ToList());
    }

    [Fact]
    public void Build_OrdinaryPropertyInfo_DisplaysSequenceValueParameterPatternSignature()
    {
        var model = BuildModel("Step((...history, pre2), pre1) = history.count, pre2, pre1");

        var property = SingleProperty(model, "Step");
        Assert.Equal("Step((...history, pre2), pre1)", property.DisplaySignature);
        Assert.Equal(["history", "pre2", "pre1"], property.Parameters.Select(parameter => parameter.Name).ToList());
        Assert.Equal(["...history", "pre2", "pre1"], property.Parameters.Select(parameter => parameter.DisplayName).ToList());
        Assert.Equal(["(...history, pre2)", "pre1"], property.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
    }

    [Fact]
    public void Build_OrdinaryPropertyInfo_DisplaysSequenceValueExplicitParameterPatternSignature()
    {
        var model = BuildModel("F((x, y)) = x + y");

        var property = SingleProperty(model, "F");
        Assert.Equal("F((x, y))", property.DisplaySignature);
        Assert.Equal(["x", "y"], property.Parameters.Select(parameter => parameter.Name).ToList());
        Assert.Equal(["(x, y)"], property.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
        Assert.NotEqual(["x", "y"], property.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
    }

    [Fact]
    public void Build_OrdinaryPropertyInfo_DisplaysSequenceValueVariadicExplicitParameterPatternSignature()
    {
        var model = BuildModel("CountSequenceValue((...values)) = values.count");

        var property = SingleProperty(model, "CountSequenceValue");
        Assert.Equal("CountSequenceValue((...values))", property.DisplaySignature);
        Assert.Equal(["...values"], property.Parameters.Select(parameter => parameter.DisplayName).ToList());
        Assert.Equal(["(...values)"], property.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
        Assert.NotEqual(["...values"], property.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
    }

    [Fact]
    public void Build_OrdinaryPropertyInfo_DisplaysNestedSequenceValueRecursiveExplicitParameterPatternSignature()
    {
        var model = BuildModel("G(((...history), previous)) = history.count + previous");

        var property = SingleProperty(model, "G");
        Assert.Equal("G(((...history), previous))", property.DisplaySignature);
        Assert.Equal(["...history", "previous"], property.Parameters.Select(parameter => parameter.DisplayName).ToList());
        Assert.Equal(["((...history), previous)"], property.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
        Assert.NotEqual(["...history", "previous"], property.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
    }

    [Fact]
    public void Build_ImplicitLiftedSequenceValueParameterPatternSignature_PreservesShape()
    {
        var model = BuildModel(
            """
            CountSequenceValue((...items)) = items.count
            Use = CountSequenceValue
            """);

        var property = SingleProperty(model, "Use");
        Assert.Equal("Use((...items))", property.DisplaySignature);
        Assert.Equal(["...items"], property.Parameters.Select(parameter => parameter.DisplayName).ToList());
        Assert.Equal([PropertyParameterKind.Implicit], property.Parameters.Select(parameter => parameter.Kind).ToList());
        Assert.Equal(["(...items)"], property.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
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
    public void Build_ImplicitQuadratic_ExposesDotCallArgumentDependenciesInPropertyInfo()
    {
        var model = BuildModel(
            """
            Quadratic = {
                Discriminant = b ^ 2 - 4 * a * c
                Root1 = (-b + Math.Sqrt(Discriminant)) / (2 * a)
                Root2 = (-b - Math.Sqrt(Discriminant)) / (2 * a)

                Root1, Root2
            }
            Quadratic(1, -5, 6)
            """);

        Assert.Equal(["b", "a", "c"], SingleProperty(model, "Quadratic").Parameters.Select(parameter => parameter.Name).ToList());
        Assert.Equal(["b", "a", "c"], SingleProperty(model, "Discriminant").Parameters.Select(parameter => parameter.Name).ToList());
        Assert.Equal(["b", "a", "c"], SingleProperty(model, "Root1").Parameters.Select(parameter => parameter.Name).ToList());
        Assert.Equal(["b", "a", "c"], SingleProperty(model, "Root2").Parameters.Select(parameter => parameter.Name).ToList());
    }

    [Fact]
    public void Build_OrdinaryPropertyInfo_ExplicitParameterListDoesNotExposeImplicitParameters()
    {
        var parseResult = Parser.Parse("Add(x) = x + y");
        Assert.True(parseResult.HasErrors);
        Assert.Contains(parseResult.Diagnostics, diagnostic =>
            diagnostic.Severity == DiagnosticSeverity.Error
            && diagnostic.Message.Contains("Explicit parameter lists are closed"));

        var model = SemanticModelBuilder.Build(parseResult);

        var property = SingleProperty(model, "Add");
        Assert.Equal(PropertyShape.Ordinary, property.Shape);
        Assert.Equal("Add(x)", property.DisplaySignature);
        Assert.Equal(["x"], property.Parameters.Select(parameter => parameter.Name).ToList());
        Assert.Equal(PropertyParameterKind.Explicit, property.Parameters[0].Kind);
        Assert.NotNull(property.Parameters[0].Span);
        Assert.DoesNotContain(property.Parameters, parameter => parameter.Kind == PropertyParameterKind.Implicit);
    }

    [Fact]
    public void Build_LocalOnlyCapturedNestedProperty_IsNotResolvedThroughParentDotAccess()
    {
        var model = BuildModel(
            """
            Algo(x) = {
            Prop = x + 1
            x
            }
            Algo.Prop
            """);

        var property = SingleProperty(model, "Prop");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, property.Exposure);
        Assert.False(property.IsExported);

        var declarationProperty = PropertyAt(model, 2, 1);
        Assert.Same(property, declarationProperty);

        var dotResolution = ResolutionAt(model, 5, 6);
        Assert.Equal(IdentifierClassification.Unresolved, dotResolution.Classification);
        Assert.Null(dotResolution.ResolvedDeclaration);
        Assert.Null(dotResolution.ResolvedProperty);
    }

    [Fact]
    public void Build_ExportedNestedProperty_RemainsResolvedThroughParentDotAccess()
    {
        var model = BuildModel(
            """
            Library = {
            Add1 = x + 1
            }
            Library.Add1(6)
            """);

        var property = SingleProperty(model, "Add1");
        Assert.Equal(PropertyExposure.Exported, property.Exposure);
        Assert.True(property.IsExported);

        var dotResolution = ResolutionAt(model, 4, 9);
        Assert.Equal(IdentifierClassification.PropertyReference, dotResolution.Classification);
        Assert.Same(property, dotResolution.ResolvedProperty);
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
    public void Build_ConditionalPropertyInfo_PreservesSequenceValuePatternShape()
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
    public void Build_ConditionalPropertyInfo_PreservesDoubleParenSequenceValuePatternShape()
    {
        var model = BuildModel(
            """
            MarkSequenceValueRange((a, b, c)) = 1
            MarkSequenceValueRange(x) = 0
            MarkSequenceValueRange(5)
            """);

        var property = SingleProperty(model, "MarkSequenceValueRange");
        Assert.Equal(PropertyShape.Conditional, property.Shape);
        Assert.Equal(2, property.ConditionalBranches.Count);
        Assert.Equal("MarkSequenceValueRange((a, b, c))", property.ConditionalBranches[0].HeadText);
        Assert.Equal(["a", "b", "c"], property.ConditionalBranches[0].BinderNames.ToList());
        Assert.Equal("MarkSequenceValueRange(x)", property.ConditionalBranches[1].HeadText);
        Assert.Equal(["x"], property.ConditionalBranches[1].BinderNames.ToList());
    }

    [Fact]
    public void Build_ConditionalBranchProperty_IsNotResolvedThroughParentDotAccess()
    {
        var model = BuildModel(
            """
            Outer(0) = {
            Inner = 1
            0
            }
            Outer(x) = {
            Inner = x + 1
            x
            }
            Outer.Inner
            """);

        var innerProperties = model.FindProperties("Inner").ToList();
        Assert.Equal(2, innerProperties.Count);
        Assert.All(innerProperties, property =>
        {
            Assert.Equal(PropertyExposure.LocalOnlyConditionalAlgorithm, property.Exposure);
            Assert.False(property.IsExported);
        });

        var dotResolution = ResolutionAt(model, 9, 7);
        Assert.Equal(IdentifierClassification.Unresolved, dotResolution.Classification);
        Assert.Null(dotResolution.ResolvedDeclaration);
        Assert.Null(dotResolution.ResolvedProperty);
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
