using KatLang.Semantics;

namespace KatLang.Tests;

public class SemanticModelTests
{
    private static Func<string, CancellationToken, ValueTask<string>> MockDownloader(
        Dictionary<string, string> files)
    {
        return (url, _) =>
        {
            if (files.TryGetValue(url, out var content))
                return ValueTask.FromResult(content);

            var trimmed = url.TrimEnd('/');
            if (files.TryGetValue(trimmed, out content))
                return ValueTask.FromResult(content);

            throw new Exception($"404: {url}");
        };
    }

    private static SemanticModel BuildModel(string source, Dictionary<string, string>? remoteFiles = null)
    {
        // The in-memory downloader completes synchronously, so the async parse does
        // too; GetResult extracts the completed task's result without blocking.
        var parseResult = remoteFiles is null
            ? Parser.Parse(source)
            : Parser.ParseAsync(source, new RunOptions { DownloadCode = MockDownloader(remoteFiles) })
                .GetAwaiter().GetResult();
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
    public void Build_CollectingBindingAndSpreadMarker_KeepSourceBackedNameSitesOnly()
    {
        const string source =
            """
            Pack(*items) = items
            Values = (1, 2)
            Pack(Values*)
            """;

        var parseResult = Parser.Parse(source);
        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(d => d.Message)));
        var model = SemanticModelBuilder.Build(parseResult);

        var itemsDeclaration = Assert.Single(model.FindDeclarations("items"));
        Assert.Equal(OccurrenceKind.ExplicitParameterDefinition, itemsDeclaration.Kind);
        AssertSpan(itemsDeclaration.Span, 1, 7, 1, 11);
        Assert.Equal(itemsDeclaration, ResolutionAt(model, 1, 16).ResolvedDeclaration);

        var pack = SingleProperty(model, "Pack");
        AssertPropertySignature(pack, "Pack(*items)", "*items");

        var valuesDeclaration = Assert.Single(model.FindDeclarations("Values"));
        var spreadOperand = ResolutionAt(model, 3, 6);
        Assert.Equal(IdentifierClassification.PropertyReference, spreadOperand.Classification);
        Assert.Equal(valuesDeclaration, spreadOperand.ResolvedDeclaration);

        // The prefix `*` collect marker is punctuation before the binding
        // name: the name is the declaration site and the marker produces no
        // identifier semantic site of its own.
        var packAlgorithm = Assert.Single(
            parseResult.Root.Properties,
            static property => property.Name == "Pack").Value;
        var parameter = Assert.Single(packAlgorithm.Parameters);
        Assert.Equal(ParameterKind.Collecting, parameter.Kind);
        AssertSpan(Assert.IsType<SourceSpan>(parameter.CollectMarkerSpan), 1, 6, 1, 6);
        AssertNoIdentifierSemanticSiteOverlaps(model, Assert.IsType<SourceSpan>(parameter.CollectMarkerSpan));

        var call = Assert.IsType<Expr.Call>(Assert.Single(parseResult.Root.Output));
        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(call.Args));
        Assert.IsType<Expr.Resolve>(spread.Operand);

        // The postfix `*` spread marker is punctuation too: no identifier
        // occurrence, symbol, or classification is created for it.
        var spreadMarkerSpan = Assert.IsType<SourceSpan>(spread.SpreadMarkerSpan);
        AssertSpan(spreadMarkerSpan, 3, 12, 3, 12);
        AssertNoIdentifierSemanticSiteOverlaps(model, spreadMarkerSpan);
    }

    [Fact]
    public void Build_SpreadMarker_CreatesNoIdentifierSemanticSites()
    {
        const string source =
            """
            A = (1, 2)
            A*
            """;

        var parseResult = Parser.Parse(source);
        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(d => d.Message)));
        var model = SemanticModelBuilder.Build(parseResult);

        // The postfix `*` spread marker is punctuation, not an identifier: the
        // model creates no occurrence, no symbol, and no builtin classification
        // for it — only the operand keeps its identifier semantics.
        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(parseResult.Root.Output));
        var markerSpan = Assert.IsType<SourceSpan>(spread.SpreadMarkerSpan);
        AssertSpan(markerSpan, 2, 2, 2, 2);
        AssertNoIdentifierSemanticSiteOverlaps(model, markerSpan);
        Assert.Null(model.FindResolutionAt(2, 2));

        var aDeclaration = Assert.Single(model.FindDeclarations("A"));
        var operandReference = ResolutionAt(model, 2, 1);
        Assert.Equal(OccurrenceKind.ResolveReference, operandReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, operandReference.Classification);
        Assert.Equal(aDeclaration, operandReference.ResolvedDeclaration);
        AssertSpan(operandReference.Occurrence.Span, 2, 1, 2, 1);
    }

    [Fact]
    public void Build_FluentSpreadTargetAndExplicitCalleeShareImplicitParameterSemantics()
    {
        var model = BuildModel(
            """
            A = (1, 2)
            Explicit = Target(A*)
            Fluent = A*.Target
            """);

        var explicitProperty = SingleProperty(model, "Explicit");
        var fluentProperty = SingleProperty(model, "Fluent");
        Assert.Equal(
            explicitProperty.Parameters.Select(static parameter => (parameter.Name, parameter.Kind)),
            fluentProperty.Parameters.Select(static parameter => (parameter.Name, parameter.Kind)));
        Assert.Equal(
            [("Target", PropertyParameterKind.Implicit)],
            explicitProperty.Parameters.Select(static parameter => (parameter.Name, parameter.Kind)));

        var targetReferences = model.FindResolutions("Target").ToList();
        Assert.Equal(2, targetReferences.Count);
        Assert.All(
            targetReferences,
            static reference =>
            {
                Assert.Equal(OccurrenceKind.ParameterReference, reference.Occurrence.Kind);
                Assert.Equal(IdentifierClassification.ImplicitParameterReference, reference.Classification);
                Assert.Null(reference.ResolvedDeclaration);
                Assert.Null(reference.ResolvedProperty);
            });
    }

    [Fact]
    public void Build_UserDefinedSpreadName_ResolvesAsOrdinaryProperty()
    {
        var model = BuildModel(
            """
            spread = 5
            spread
            """);

        // `spread` is no longer a reserved intrinsic name: a user-defined
        // property named `spread` declares and resolves ordinarily.
        var spreadDeclaration = Assert.Single(model.FindDeclarations("spread"));
        Assert.Equal(OccurrenceKind.PropertyDefinition, spreadDeclaration.Kind);
        AssertSpan(spreadDeclaration.Span, 1, 1, 1, 6);

        var spreadReference = Assert.Single(
            model.IdentifierResolutions,
            resolution => resolution.Occurrence.Name == "spread"
                && resolution.Occurrence.Kind == OccurrenceKind.ResolveReference);
        Assert.Equal(IdentifierClassification.PropertyReference, spreadReference.Classification);
        Assert.Equal(spreadDeclaration, spreadReference.ResolvedDeclaration);
        AssertSpan(spreadReference.Occurrence.Span, 2, 1, 2, 6);
        Assert.Equal("spread", Assert.IsType<PropertyInfo>(spreadReference.ResolvedProperty).Name);
    }

    [Fact]
    public void Build_DeconstructionAssignment_TracksSourceBackedTargetDeclarations()
    {
        var model = BuildModel(
            """
            A = 1, 2, 3, 4, 5
            x, *y, z = A
            x + y.sum + z
            """);

        var xDeclaration = Assert.Single(model.FindDeclarations("x"));
        Assert.Equal(OccurrenceKind.PropertyDefinition, xDeclaration.Kind);
        AssertSpan(xDeclaration.Span, 2, 1, 2, 1);

        var yDeclaration = Assert.Single(model.FindDeclarations("y"));
        Assert.Equal(OccurrenceKind.PropertyDefinition, yDeclaration.Kind);
        AssertSpan(yDeclaration.Span, 2, 5, 2, 5);

        var zDeclaration = Assert.Single(model.FindDeclarations("z"));
        Assert.Equal(OccurrenceKind.PropertyDefinition, zDeclaration.Kind);
        AssertSpan(zDeclaration.Span, 2, 8, 2, 8);

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
        var aReference = ResolutionAt(model, 2, 12);
        Assert.Equal(IdentifierClassification.PropertyReference, aReference.Classification);
        Assert.Equal(aDeclaration, aReference.ResolvedDeclaration);

        // Later uses resolve to the deconstructed property declarations.
        Assert.Equal(xDeclaration, ResolutionAt(model, 3, 1).ResolvedDeclaration);
    }

    [Fact]
    public void Build_DeconstructionRhsImplicitName_HasOnlyWrittenProvenance()
    {
        var model = BuildModel("F = {\n a, b = x, 10\n a + b\n}\nF(1)");
        var reference = Assert.Single(model.FindResolutions("x"));
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, reference.Classification);
        AssertSpan(reference.Occurrence.Span, 2, 9, 2, 9);
        Assert.Empty(model.FindDeclarations("x"));
        Assert.DoesNotContain(model.PropertyInfos, property => property.Name.StartsWith('$'));
        Assert.DoesNotContain(model.IdentifierResolutions, resolution => resolution.Occurrence.Name.StartsWith('$'));
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
            result = x
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
            public Add(*vectors) = Vector(vectors.map(X).sum, vectors.map(Y).sum)
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
    public void Build_DotCall_UnknownMemberOnImplicitParameterReceiver_IsTheInferredFallbackParameter()
    {
        // The opaque receiver means the lexical fallback MAY be selected, so
        // the member's callable identity was inferred as an implicit
        // parameter. The editor consumes that stored identity: the occurrence
        // is still a dot member, classified as the parameter it binds.
        var model = BuildModel("public Test = a.Unknown");

        var parameterReference = ResolutionAt(model, 1, 15);
        Assert.Equal(OccurrenceKind.ParameterReference, parameterReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, parameterReference.Classification);

        var unknownReference = ResolutionAt(model, 1, 17);
        Assert.Equal(OccurrenceKind.DotMemberReference, unknownReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, unknownReference.Classification);
        // An implicit parameter has no source declaration to navigate to.
        Assert.Null(unknownReference.ResolvedDeclaration);
        Assert.Null(unknownReference.ResolvedProperty);
    }

    [Fact]
    public void Build_DotCall_MemberResolvesCallingContextParameter()
    {
        // The dot member `t` mirrors the evaluator's parameter channel: with
        // no lexical declaration in sight it resolves to the enclosing
        // explicit parameter, exactly like the plain callee `t(a)` would.
        var model = BuildModel(
            """
            K(a, t) = a.t
            K(7, {a+1})
            """);

        var tDeclaration = Assert.Single(model.FindDeclarations("t"));
        Assert.Equal(OccurrenceKind.ExplicitParameterDefinition, tDeclaration.Kind);
        AssertSpan(tDeclaration.Span, 1, 6, 1, 6);

        var memberReference = ResolutionAt(model, 1, 13);
        Assert.Equal(OccurrenceKind.DotMemberReference, memberReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ExplicitParameterReference, memberReference.Classification);
        Assert.Equal(tDeclaration, memberReference.ResolvedDeclaration);
    }

    [Fact]
    public void Build_DotCall_MemberPrefersLocalParameterOverSameNameProperty()
    {
        var model = BuildModel(
            """
            t = 5
            K(a, t) = a.t
            K(7, {a+1})
            """);

        var declarations = model.FindDeclarations("t");
        var parameterDeclaration = Assert.Single(
            declarations,
            declaration => declaration.Kind == OccurrenceKind.ExplicitParameterDefinition);

        var memberReference = ResolutionAt(model, 2, 13);
        Assert.Equal(OccurrenceKind.DotMemberReference, memberReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ExplicitParameterReference, memberReference.Classification);
        Assert.Equal(parameterDeclaration, memberReference.ResolvedDeclaration);
    }

    [Fact]
    public void Build_GracedDot_MemberClassifiesLikeTheOrdinaryDotMember()
    {
        // `K = a~.t` IS the ordinary dot edge `a.t`, so its member identifier
        // is a dot-member occurrence classified through the stored fallback —
        // here the inferred implicit parameter `t`. The graced and ungraced
        // spellings classify identically. Grace still belongs only to
        // signature ordering: postfix Grace moves `a` after `t`.
        var graced = BuildModel(
            """
            K = a~.t
            K({a+1}, 7)
            """);
        var gracedMember = ResolutionAt(graced, 1, 8);
        Assert.Equal(OccurrenceKind.DotMemberReference, gracedMember.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, gracedMember.Classification);
        Assert.Equal(
            ["t", "a"],
            SingleProperty(graced, "K").Parameters.Select(parameter => parameter.Name).ToList());

        var prefixMemberGraced = BuildModel(
            """
            K = a.~t
            K({a+1}, 7)
            """);
        var prefixMember = ResolutionAt(prefixMemberGraced, 1, 8);
        Assert.Equal(OccurrenceKind.DotMemberReference, prefixMember.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, prefixMember.Classification);
        Assert.Equal(
            ["t", "a"],
            SingleProperty(prefixMemberGraced, "K").Parameters.Select(parameter => parameter.Name).ToList());

        var ungraced = BuildModel(
            """
            K = a.t
            K(7, {a+1})
            """);
        var ungracedMember = ResolutionAt(ungraced, 1, 7);
        Assert.Equal(gracedMember.Occurrence.Kind, ungracedMember.Occurrence.Kind);
        Assert.Equal(gracedMember.Classification, ungracedMember.Classification);
        Assert.Equal(
            ["a", "t"],
            SingleProperty(ungraced, "K").Parameters.Select(parameter => parameter.Name).ToList());
    }

    [Fact]
    public void Build_RejectedComplexPostfixGraceReceiver_YieldsNoGraceOrdering()
    {
        // Ineligible Grace on a compound receiver is a parse error; the recovery
        // tree is the ordinary GRACELESS dot edge, so the editor stays
        // tolerant (spans, ordinary classification) without ever inferring a
        // multi-name Grace ordering from invalid source.
        var parseResult = Parser.Parse("K = (x + y)~.t\nK(3, 4, {a})");
        Assert.True(parseResult.HasErrors);
        Assert.Contains(
            parseResult.Diagnostics,
            d => d.Message.Contains("Grace `~` can only be applied to a parameter or name occurrence.", StringComparison.Ordinal));

        var model = SemanticModelBuilder.Build(parseResult);
        Assert.NotNull(model);
        var k = Assert.IsType<Algorithm.User>(parseResult.Root.Properties[0].Value);
        // No grace was assigned, so the recovery tree keeps ordinary semantic
        // occurrence order: receiver names first, then member/fallback.
        Assert.Equal(["x", "y", "t"], k.Params);
    }

    [Fact]
    public void Build_GracedDot_MemberNavigatesToTheStructuralMember()
    {
        // `Obj~.V` IS the ordinary dot edge `Obj.V`, so the member navigates
        // to Obj's STRUCTURAL V (line 3) — the same target the marker-free
        // spelling gives, and the same one the evaluator selects (42). The
        // marker never redirects navigation to the lexical V(x) = 99.
        var model = BuildModel(
            """
            V(x) = 99
            Obj = {
                public V = 42
                0
            }
            Obj~.V
            """);

        var structuralDeclaration = Assert.Single(
            model.FindDeclarations("V"),
            declaration => declaration.Span is { } span && span.StartLineNumber == 3);

        var memberReference = ResolutionAt(model, 6, 6);
        Assert.Equal(OccurrenceKind.DotMemberReference, memberReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, memberReference.Classification);
        Assert.Equal(structuralDeclaration, memberReference.ResolvedDeclaration);
    }

    [Fact]
    public void Build_OrdinaryDot_StructuralMemberStaysMemberBesideSameNameLexical()
    {
        // Ordinary `Obj.V` keeps structural classification: the member
        // navigates to Obj's own V, not the lexical V(x).
        var model = BuildModel(
            """
            V(x) = 99
            Obj = {
                public V = 42
                0
            }
            Obj.V
            """);

        var structuralDeclaration = Assert.Single(
            model.FindDeclarations("V"),
            declaration => declaration.Span is { } span && span.StartLineNumber == 3);

        var memberReference = ResolutionAt(model, 6, 5);
        Assert.Equal(OccurrenceKind.DotMemberReference, memberReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, memberReference.Classification);
        Assert.Equal(structuralDeclaration, memberReference.ResolvedDeclaration);
    }

    [Fact]
    public void Build_DotCall_MemberPrefersVisiblePropertyOverCapturedParameterBinding()
    {
        // Inside G, `t` is not a parameter of G; the visible property `t`
        // shadows any dynamically visible parameter binding, mirroring the
        // evaluator's captured-parameter shadow rule.
        var model = BuildModel(
            """
            t = 5
            G(x) = x.t
            K(a, t) = G(a)
            K(7, {a+1})
            """);

        var propertyDeclaration = Assert.Single(
            model.FindDeclarations("t"),
            declaration => declaration.Kind == OccurrenceKind.PropertyDefinition);

        var memberReference = ResolutionAt(model, 2, 10);
        Assert.Equal(OccurrenceKind.DotMemberReference, memberReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, memberReference.Classification);
        Assert.Equal(propertyDeclaration, memberReference.ResolvedDeclaration);
    }

    [Fact]
    public void Build_DotCall_GrandparentLexicalFallbackUsesOrdinaryScopeLookup()
    {
        var model = BuildModel(
            """
            Outer = {
                t(a) = a + 1
                Inner = {
                    K(a) = a.t
                    K(7)
                }
                Inner
            }
            Outer
            """);

        var tDeclaration = Assert.Single(
            model.FindDeclarations("t"),
            declaration => declaration.Kind == OccurrenceKind.PropertyDefinition);
        var memberReference = ResolutionAt(model, 4, 18);
        Assert.Equal(OccurrenceKind.DotMemberReference, memberReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, memberReference.Classification);
        Assert.Equal(tDeclaration, memberReference.ResolvedDeclaration);
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
            C = A*, B
            C.X
            C.Y
            """);

        Assert.Single(model.FindDeclarations("X"));
        Assert.Single(model.FindDeclarations("Y"));

        // Neither member reaches A's or B's declaration: a spread joins VALUES
        // and merges no property surface. Both are the edges' own inferred
        // fallback parameters instead.
        var xReference = ResolutionAt(model, 10, 3);
        Assert.Equal(OccurrenceKind.DotMemberReference, xReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, xReference.Classification);
        Assert.Null(xReference.ResolvedDeclaration);
        Assert.Null(xReference.ResolvedProperty);

        var yReference = ResolutionAt(model, 11, 3);
        Assert.Equal(OccurrenceKind.DotMemberReference, yReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, yReference.Classification);
        Assert.Null(yReference.ResolvedDeclaration);
        Assert.Null(yReference.ResolvedProperty);
    }

    [Fact]
    public void Build_DotCall_ArityOnImplicitParameter_IsNoIntrinsic()
    {
        // `arity` is not an intrinsic member and resolves nowhere lexically,
        // so it is just the edge's inferred fallback parameter — it must never
        // classify as a builtin or resolve to a declaration.
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
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, arityReference.Classification);
        Assert.Null(arityReference.ResolvedDeclaration);
        Assert.Null(arityReference.ResolvedProperty);
    }

    [Fact]
    public void Build_DotCall_LengthOnImplicitParameter_IsNoIntrinsic()
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
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, lengthReference.Classification);
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
    public void Build_OutputNamedProperty_IsOrdinaryPropertyDefinition()
    {
        var model = BuildModel("Output = missing");

        var outputDeclaration = Assert.Single(model.FindDeclarations("Output"));
        Assert.Equal(OccurrenceKind.PropertyDefinition, outputDeclaration.Kind);
        AssertSpan(outputDeclaration.Span, 1, 1, 1, 6);

        var outputResolution = ResolutionAt(model, 1, 1);
        Assert.Equal(IdentifierClassification.PropertyDefinition, outputResolution.Classification);
        Assert.Equal(outputDeclaration, outputResolution.ResolvedDeclaration);

        var missingResolution = ResolutionAt(model, 1, 10);
        Assert.Equal(OccurrenceKind.ParameterReference, missingResolution.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, missingResolution.Classification);
        Assert.Null(missingResolution.ResolvedDeclaration);
    }

    [Fact]
    public void Build_OutputDotMember_IsOrdinaryDotMemberReference()
    {
        var source =
            """
            Algo = {
              public Output(x) = x + 1
            }
            Algo.Output(6)
            """;

        var parseResult = Parser.Parse(source);
        Assert.False(parseResult.HasErrors);

        var model = SemanticModelBuilder.Build(parseResult);
        var outputReference = ResolutionAt(model, 4, 6);
        Assert.Equal(OccurrenceKind.DotMemberReference, outputReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, outputReference.Classification);
        Assert.NotNull(outputReference.ResolvedDeclaration);
        Assert.Equal("Output", outputReference.ResolvedDeclaration!.Name);
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

        // X is declared in the loaded module: the member resolves to it as a module-provided
        // target — no declaration site of this document, no local location.
        Assert.Empty(model.FindDeclarations("X"));
        var xReference = ResolutionAt(model, 2, 3);
        Assert.Equal(OccurrenceKind.DotMemberReference, xReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, xReference.Classification);
        Assert.Null(xReference.ResolvedDeclaration);
        var x = Assert.IsType<PropertyInfo>(xReference.ResolvedProperty);
        Assert.Equal("X", x.Name);
        Assert.Null(x.Declaration);
        Assert.True(x.IsPublic);
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
    public void Build_NonLoadUnresolvedDotMember_ResolvesToNoDeclaration()
    {
        // `A` is a plain value property, so the member has no structural
        // target: it is the edge's inferred fallback parameter and navigates
        // nowhere.
        var model = BuildModel(
            """
            A = 5
            A.X
            """);

        var xReference = ResolutionAt(model, 2, 3);
        Assert.Equal(OccurrenceKind.DotMemberReference, xReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, xReference.Classification);
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

        // The alias is a wrapper without members, so `X` never navigates into
        // the loaded module — it is the edge's own inferred fallback
        // parameter, matching the evaluator's lexical-fallback dispatch.
        var xReference = ResolutionAt(model, 3, 7);
        Assert.Equal(OccurrenceKind.DotMemberReference, xReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, xReference.Classification);
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
    public void Build_OrdinaryPropertyInfo_DisplaysCollectingExplicitParameter()
    {
        var model = BuildModel("Collect(*list) = list");

        var property = SingleProperty(model, "Collect");
        Assert.Equal("Collect(*list)", property.DisplaySignature);
        var parameter = Assert.Single(property.Parameters);
        Assert.Equal("list", parameter.Name);
        Assert.Equal("*list", parameter.DisplayName);
        Assert.Equal(PropertyParameterKind.Explicit, parameter.Kind);
        Assert.True(parameter.IsCollecting);
    }

    [Fact]
    public void Build_OrdinaryPropertyInfo_DisplaysCollectingParameterBeforeSuffix()
    {
        var model = BuildModel("Scale(*values, factor) = values.map{n * factor}");

        var property = SingleProperty(model, "Scale");
        Assert.Equal("Scale(*values, factor)", property.DisplaySignature);
        Assert.Equal(["values", "factor"], property.Parameters.Select(parameter => parameter.Name).ToList());
        Assert.Equal(["*values", "factor"], property.Parameters.Select(parameter => parameter.DisplayName).ToList());
        Assert.Equal(["*values", "factor"], property.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
        Assert.Equal([PropertyParameterKind.Explicit, PropertyParameterKind.Explicit], property.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.Kind).ToList());
        Assert.Equal([true, false], property.Parameters.Select(parameter => parameter.IsCollecting).ToList());
    }

    [Fact]
    public void Build_OrdinaryPropertyInfo_DisplaysSequenceValueParameterPatternSignature()
    {
        var model = BuildModel("Step((*history, pre2), pre1) = history.count, pre2, pre1");

        var property = SingleProperty(model, "Step");
        Assert.Equal("Step((*history, pre2), pre1)", property.DisplaySignature);
        Assert.Equal(["history", "pre2", "pre1"], property.Parameters.Select(parameter => parameter.Name).ToList());
        Assert.Equal(["*history", "pre2", "pre1"], property.Parameters.Select(parameter => parameter.DisplayName).ToList());
        Assert.Equal(["(*history, pre2)", "pre1"], property.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
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
    public void Build_OrdinaryPropertyInfo_DisplaysSequenceValueCollectingExplicitParameterPatternSignature()
    {
        var model = BuildModel("CountSequenceValue((*values)) = values.count");

        var property = SingleProperty(model, "CountSequenceValue");
        Assert.Equal("CountSequenceValue((*values))", property.DisplaySignature);
        Assert.Equal(["*values"], property.Parameters.Select(parameter => parameter.DisplayName).ToList());
        Assert.Equal(["(*values)"], property.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
        Assert.NotEqual(["*values"], property.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
    }

    [Fact]
    public void Build_OrdinaryPropertyInfo_DisplaysNestedSequenceValueRecursiveExplicitParameterPatternSignature()
    {
        var model = BuildModel("G(((*history), previous)) = history.count + previous");

        var property = SingleProperty(model, "G");
        Assert.Equal("G(((*history), previous))", property.DisplaySignature);
        Assert.Equal(["*history", "previous"], property.Parameters.Select(parameter => parameter.DisplayName).ToList());
        Assert.Equal(["((*history), previous)"], property.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
        Assert.NotEqual(["*history", "previous"], property.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
    }

    [Fact]
    public void Build_ImplicitLiftedSequenceValueParameterPatternSignature_PreservesShape()
    {
        var model = BuildModel(
            """
            CountSequenceValue((*items)) = items.count
            Use = CountSequenceValue
            """);

        var property = SingleProperty(model, "Use");
        Assert.Equal("Use((*items))", property.DisplaySignature);
        Assert.Equal(["*items"], property.Parameters.Select(parameter => parameter.DisplayName).ToList());
        Assert.Equal([PropertyParameterKind.Implicit], property.Parameters.Select(parameter => parameter.Kind).ToList());
        Assert.Equal(["(*items)"], property.GetParameters(PropertyCallStyle.Plain).Select(parameter => parameter.DisplayName).ToList());
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
    public void Build_OuterParametersStayOnAlgorithmMetadata()
    {
        var model = BuildModel(
            """
            Algo(x) = {
            x + 1
            }
            Algo(6)
            """);

        var algo = SingleProperty(model, "Algo");
        Assert.Equal(PropertyShape.Ordinary, algo.Shape);
        var parameter = Assert.Single(algo.Parameters);
        Assert.Equal("x", parameter.Name);
        Assert.Equal(PropertyParameterKind.Explicit, parameter.Kind);
        Assert.NotNull(parameter.Span);

        // No hidden `Output` symbol exists anywhere in this model.
        Assert.Empty(model.FindProperties("Output"));
        Assert.Empty(model.FindDeclarations("Output"));

        var xReference = ResolutionAt(model, 2, 1);
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

        // Declarations in a branch body classify under the ONE self-containment rule: the
        // literal `Inner = 1` is Exported, the binder-capturing `Inner = x + 1` is local-only
        // because the branch binder is an input only the family's call binds. Neither is
        // reachable through the family by name — a conditional exposes no structural
        // members — so `Outer.Inner` stays unresolved regardless of that classification.
        var innerProperties = model.FindProperties("Inner").ToList();
        Assert.Equal(2, innerProperties.Count);
        var selfContained = Assert.Single(innerProperties, property => property.Exposure == PropertyExposure.Exported);
        Assert.True(selfContained.IsExported);
        var binderCapturing = Assert.Single(
            innerProperties, property => property.Exposure == PropertyExposure.LocalOnlyCapturedAncestorParameters);
        Assert.False(binderCapturing.IsExported);

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
            apply(1).string
            """);

        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(d => d.Message)));

        var walker = new CollectingWalker();
        walker.VisitAlgorithm(parseResult.Root);

        Assert.Equal(["value", "apply", "match", "match"], walker.PropertyDeclarations);
        Assert.Equal(["x"], walker.ExplicitParameters);
        Assert.Equal(["y"], walker.ConditionalBinders);
        Assert.Equal(["value", "apply"], walker.ResolveIdentifiers);
        Assert.Equal(["x", "y"], walker.ParameterIdentifiers);
        Assert.Equal(["string"], walker.DotMembers);
    }

    private sealed class CollectingWalker : SyntaxWalker
    {
        public List<string> PropertyDeclarations { get; } = [];

        public List<string> ExplicitParameters { get; } = [];

        public List<string> ConditionalBinders { get; } = [];

        public List<string> ResolveIdentifiers { get; } = [];

        public List<string> ParameterIdentifiers { get; } = [];

        public List<string> DotMembers { get; } = [];

        protected override void VisitPropertyDeclaration(Property property, SourceSpan span)
            => PropertyDeclarations.Add(property.Name);

        protected override void VisitExplicitParameterDeclaration(Algorithm algorithm, ParameterDeclaration declaration)
            => ExplicitParameters.Add(declaration.Name);

        protected override void VisitConditionalBinderDeclaration(Pattern.Bind pattern, SourceSpan span)
            => ConditionalBinders.Add(pattern.Name);

        protected override void VisitResolveIdentifier(Expr.Resolve expr)
            => ResolveIdentifiers.Add(expr.Name);

        protected override void VisitParameterIdentifier(Expr.Param expr)
            => ParameterIdentifiers.Add(expr.Name);

        protected override void VisitDotMemberIdentifier(Expr.DotCall expr, SourceSpan span)
            => DotMembers.Add(expr.Name);
    }

    // ── Scope visibility (completion) ───────────────────────────────────────

    private static IReadOnlyList<string> SymbolNames(ScopeVisibility scope)
        => scope.Symbols.Select(static symbol => symbol.Name).ToList();

    private static VisibleSymbol SingleSymbol(ScopeVisibility scope, string name)
        => Assert.Single(scope.Symbols, symbol => symbol.Name == name);

    [Fact]
    public void ScopeVisibility_RootListsPropertiesAndImplicitParameters()
    {
        var model = BuildModel("Alpha = 1\nBeta = Alpha + missing\nBeta");

        var root = model.FindScopeAt(3, 1);
        Assert.Null(root.Span);
        Assert.Equal(["Alpha", "Beta"], SymbolNames(root));
        Assert.Equal(IdentifierClassification.PropertyReference, SingleSymbol(root, "Alpha").Classification);

        // `missing` is an implicit parameter of Beta's BODY scope, not a root name.
        var betaBody = model.FindScopeAt(2, 10);
        Assert.NotNull(betaBody.Span);
        Assert.Equal(
            IdentifierClassification.ImplicitParameterReference,
            SingleSymbol(betaBody, "missing").Classification);
    }

    [Fact]
    public void ScopeVisibility_NestedScopeAppliesOwnershipFirstShadowing()
    {
        var model = BuildModel(
            """
            X = 1
            F(a) = {
              Inner = a + 1
              X = 5
              Inner + X
            }
            F(3)
            """);

        var body = model.FindScopeAt(5, 5);
        Assert.Equal(["F", "Inner", "X", "a"], SymbolNames(body));

        // The inner X shadows the root X: exactly one entry, declared on line 4.
        var x = SingleSymbol(body, "X");
        Assert.Equal(4, x.Declaration!.Span.StartLineNumber);
        Assert.Equal(IdentifierClassification.ExplicitParameterReference, SingleSymbol(body, "a").Classification);

        // At root, X is the line-1 declaration and the parameter is not visible.
        var root = model.FindScopeAt(7, 1);
        Assert.Equal(1, SingleSymbol(root, "X").Declaration!.Span.StartLineNumber);
        Assert.DoesNotContain(root.Symbols, symbol => symbol.Name is "a" or "Inner");
    }

    [Fact]
    public void ScopeVisibility_UserPropertyShadowsBuiltinInMergedView()
    {
        var model = BuildModel("sum = 5\nsum");

        var visible = model.GetVisibleSymbolsAt(2, 1);
        var sum = Assert.Single(visible, symbol => symbol.Name == "sum");
        Assert.Equal(IdentifierClassification.PropertyReference, sum.Classification);

        // Unshadowed prelude names merge in exactly once.
        Assert.Single(visible, symbol => symbol.Name == "count");
        Assert.Single(visible, symbol => symbol.Name == "Math");
    }

    [Fact]
    public void ScopeVisibility_OpenProvidesExportedMembersOnly()
    {
        var model = BuildModel(
            """
            Lib = {
              public Tax = 0.21
              Hidden = 5
              public Rate = 1
            }
            Use = {
              open Lib
              Tax + Rate
            }
            Use
            """);

        var use = model.FindScopeAt(8, 5);
        Assert.Equal(IdentifierClassification.PropertyReference, SingleSymbol(use, "Tax").Classification);
        Assert.Single(use.Symbols, symbol => symbol.Name == "Rate");
        Assert.DoesNotContain(use.Symbols, symbol => symbol.Name == "Hidden");

        // Inside Lib itself, Hidden is an ordinary directly-visible property.
        var lib = model.FindScopeAt(3, 5);
        Assert.Single(lib.Symbols, symbol => symbol.Name == "Hidden");
    }

    [Fact]
    public void ScopeVisibility_OpenDedupAndSameLevelAmbiguityMatchLookup()
    {
        var model = BuildModel(
            """
            A = {
              public X = 1
              public Only = 2
            }
            B = {
              public X = 3
            }
            U = {
              open A, A, B
              1
            }
            U
            """);

        var u = model.FindScopeAt(10, 3);

        // `open A, A` dedups first-occurrence-wins, so A is ONE provider and
        // `Only` is offered; X has two distinct providers (A and B) at the same
        // level, is ambiguous exactly like lexical lookup, and is suppressed.
        Assert.Single(u.Symbols, symbol => symbol.Name == "Only");
        Assert.DoesNotContain(u.Symbols, symbol => symbol.Name == "X");
    }

    [Fact]
    public void ScopeVisibility_DirectPreludeBeatsOpenProvidedName()
    {
        var model = BuildModel(
            """
            Lib = {
              public sum = 42
            }
            U = {
              open Lib
              1
            }
            U
            """);

        // Direct-anywhere beats open-anywhere: the prelude `sum` wins, so the
        // scope emits no `sum` entry and the merged view shows the builtin.
        var u = model.FindScopeAt(6, 3);
        Assert.DoesNotContain(u.Symbols, symbol => symbol.Name == "sum");

        var mergedSum = Assert.Single(model.GetVisibleSymbolsAt(6, 3), symbol => symbol.Name == "sum");
        Assert.Equal(IdentifierClassification.Builtin, mergedSum.Classification);
    }

    [Fact]
    public void VisibleSymbol_MembersListStructuralDotSurface()
    {
        var model = BuildModel(
            """
            F(a) = {
              public L = a + 1
              public V = 2
              W = 3
              L + V + W
            }
            F(3)
            """);

        // Structural dot ignores public/private (W stays) but never exposes a
        // local-only property (L captures the ancestor parameter `a`).
        var f = SingleSymbol(model.FindScopeAt(7, 1), "F");
        Assert.Equal(["V", "W"], f.Members.Select(static member => member.Name).ToList());
        Assert.All(f.Members, static member => Assert.Empty(member.Members));
    }

    [Fact]
    public void ScopeVisibility_ConditionalClauseBodyBindsBinders()
    {
        var model = BuildModel(
            """
            Fib(0) = 0
            Fib(1) = 1
            Fib(n) = Fib(n - 1) + Fib(n - 2)
            Fib(10)
            """);

        var clauseBody = model.FindScopeAt(3, 15);
        Assert.Equal(
            IdentifierClassification.ConditionalBinderReference,
            SingleSymbol(clauseBody, "n").Classification);
        Assert.Single(clauseBody.Symbols, symbol => symbol.Name == "Fib");

        // Literal-clause bodies bind nothing.
        Assert.DoesNotContain(model.FindScopeAt(4, 1).Symbols, symbol => symbol.Name == "n");
    }

    [Fact]
    public void ScopeVisibility_BraceArgumentBlockKeepsExactExtent()
    {
        var model = BuildModel("K = a.t\nK(7, {x + 1})");

        var brace = model.FindScopeAt(2, 8);
        AssertSpan(brace.Span!, 2, 6, 2, 12);
        Assert.Equal(
            IdentifierClassification.ImplicitParameterReference,
            SingleSymbol(brace, "x").Classification);

        // K's one-line body scope carries its implicit parameters.
        var kBody = model.FindScopeAt(1, 6);
        Assert.Single(kBody.Symbols, symbol => symbol.Name == "a");
        Assert.Single(kBody.Symbols, symbol => symbol.Name == "t");
    }

    [Fact]
    public void ScopeVisibility_ModuleElaboratedSubtreeEmitsNoRegions()
    {
        var module =
            """
            public Tax = 0.21
            public Deep = {
              public Inner = 1
              Inner
            }
            Helper = 9
            """;
        var model = BuildModel(
            "open 'https://katlang.org/lib.kat'\nTax + 1",
            new Dictionary<string, string> { ["https://katlang.org/lib.kat"] = module });

        // Module spans belong to the module's source text: no region may claim
        // current-document positions, so only the root scope exists here.
        var root = Assert.Single(model.ScopeVisibilities);
        Assert.Null(root.Span);

        // The module's exported names are still visible (with members), and the
        // non-exported Helper is not.
        var deep = SingleSymbol(root, "Deep");
        Assert.Equal(["Inner"], deep.Members.Select(static member => member.Name).ToList());
        Assert.Single(root.Symbols, symbol => symbol.Name == "Tax");
        Assert.DoesNotContain(root.Symbols, symbol => symbol.Name == "Helper");
    }

    // ── Module provenance: imported source locations are never document sites (K7-SEM-R1) ──

    private static Func<string, CancellationToken, ValueTask<string>> TrackingDownloader(
        Dictionary<string, string> files,
        ICollection<string> fetched)
    {
        var downloader = MockDownloader(files);
        return (url, cancellationToken) =>
        {
            fetched.Add(url);
            return downloader(url, cancellationToken);
        };
    }

    private static SemanticModel BuildModel(string source, Func<string, CancellationToken, ValueTask<string>> downloader)
    {
        var parseResult = Parser.ParseAsync(source, new RunOptions { DownloadCode = downloader })
            .GetAwaiter().GetResult();
        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(d => d.Message)));
        return SemanticModelBuilder.Build(parseResult);
    }

    private static string Evaluate(string source, Dictionary<string, string> remoteFiles)
        => Evaluate(source, MockDownloader(remoteFiles));

    // The in-memory downloader completes synchronously, so the async engine run does too.
    private static string Evaluate(string source, Func<string, CancellationToken, ValueTask<string>> downloader)
        => KatLangEngine.EvaluateToStringAsync(source, new RunOptions { DownloadCode = downloader })
            .GetAwaiter().GetResult();

    private static string[] Lines(string source) => source.Replace("\r", "").Split('\n');

    /// <summary>The document text an identifier site claims: a single-line range inside the document.</summary>
    private static string SliceOf(string source, SourceSpan span)
    {
        var lines = Lines(source);
        Assert.Equal(span.StartLineNumber, span.EndLineNumber);
        Assert.InRange(span.StartLineNumber, 1, lines.Length);
        var line = lines[span.StartLineNumber - 1];
        Assert.InRange(span.StartColumn, 1, line.Length);
        Assert.InRange(span.EndColumn, span.StartColumn, line.Length);
        return line.Substring(span.StartColumn - 1, span.EndColumn - span.StartColumn + 1);
    }

    private static HashSet<DeclarationOccurrence> DocumentDeclarations(SemanticModel model)
        => new(model.Declarations, ReferenceEqualityComparer.Instance);

    /// <summary>
    /// A declaration a site, property, or symbol points at is either locationless
    /// (<see langword="null"/>) or one of the document's own declaration occurrences —
    /// never a span positioned in some other source text.
    /// </summary>
    private static void AssertDocumentTarget(HashSet<DeclarationOccurrence> declarations, DeclarationOccurrence? target)
    {
        if (target is not null)
            Assert.True(declarations.Contains(target), $"'{target.Name}' at {target.Span} is not a declaration site of this document.");
    }

    private static void AssertDocumentProperty(string source, HashSet<DeclarationOccurrence> declarations, PropertyInfo? property)
    {
        if (property is null)
            return;

        AssertDocumentTarget(declarations, property.Declaration);
        foreach (var parameter in property.Parameters.Concat(property.Signatures.SelectMany(static signature => signature.Parameters)))
        {
            if (parameter.Span is { } parameterSpan)
                Assert.Equal(parameter.Name, SliceOf(source, parameterSpan));
        }

        foreach (var branch in property.ConditionalBranches)
        {
            if (branch.HeadSpan is { } headSpan)
                Assert.Equal(property.Name, SliceOf(source, headSpan));
        }
    }

    private static void AssertDocumentSymbol(string source, HashSet<DeclarationOccurrence> declarations, VisibleSymbol symbol)
    {
        AssertDocumentTarget(declarations, symbol.Declaration);
        AssertDocumentProperty(source, declarations, symbol.Property);
        foreach (var member in symbol.Members)
            AssertDocumentSymbol(source, declarations, member);
    }

    /// <summary>
    /// The identifier-slice invariant over every public listing surface: each declaration,
    /// occurrence, and resolution site slices the document to the identifier written there,
    /// and every declaration or span reachable from a resolution, property, or visible
    /// symbol is either locationless or a document site. Scope hulls are deliberately not
    /// sliced — they are extents, not identifier sites.
    /// </summary>
    private static void AssertIdentifierSitesSliceToTheirSpelling(SemanticModel model, string source)
    {
        var declarations = DocumentDeclarations(model);

        foreach (var declaration in model.Declarations)
            Assert.Equal(declaration.Name, SliceOf(source, declaration.Span));

        foreach (var occurrence in model.IdentifierOccurrences)
            Assert.Equal(occurrence.Name, SliceOf(source, occurrence.Span));

        foreach (var resolution in model.IdentifierResolutions)
        {
            Assert.Equal(resolution.Occurrence.Name, SliceOf(source, resolution.Occurrence.Span));
            AssertDocumentTarget(declarations, resolution.ResolvedDeclaration);
            AssertDocumentProperty(source, declarations, resolution.ResolvedProperty);
        }

        foreach (var property in model.PropertyInfos)
            AssertDocumentProperty(source, declarations, property);

        foreach (var scope in model.ScopeVisibilities)
        {
            foreach (var symbol in scope.Symbols)
                AssertDocumentSymbol(source, declarations, symbol);
        }
    }

    /// <summary>
    /// The position-based query surface, swept over every character of the document: a hit
    /// is one of the listed document sites containing the position, the property and scope
    /// queries agree with it, and no visible symbol points outside the document.
    /// </summary>
    private static void AssertPositionalQueriesReturnOnlyDocumentSites(SemanticModel model, string source)
    {
        var declarations = DocumentDeclarations(model);
        var lines = Lines(source);
        for (var line = 1; line <= lines.Length; line++)
        {
            for (var column = 1; column <= lines[line - 1].Length; column++)
            {
                var resolution = model.FindResolutionAt(line, column);
                if (resolution is not null)
                {
                    Assert.Contains(model.IdentifierResolutions, candidate => ReferenceEquals(candidate, resolution));
                    Assert.Equal(resolution.Occurrence.Name, SliceOf(source, resolution.Occurrence.Span));
                    Assert.Equal(line, resolution.Occurrence.Span.StartLineNumber);
                    Assert.InRange(column, resolution.Occurrence.Span.StartColumn, resolution.Occurrence.Span.EndColumn);
                }

                Assert.Same(resolution?.ResolvedProperty, model.FindPropertyAt(line, column));
                Assert.Contains(model.ScopeVisibilities, candidate => ReferenceEquals(candidate, model.FindScopeAt(line, column)));
                foreach (var symbol in model.GetVisibleSymbolsAt(line, column))
                    AssertDocumentSymbol(source, declarations, symbol);
            }
        }
    }

    private static PropertyInfo AssertModuleProvidedTarget(IdentifierResolution resolution, string name)
    {
        // The existing no-local-location convention: the target is identified by its
        // property metadata and has no declaration site in this document.
        Assert.Null(resolution.ResolvedDeclaration);
        var target = Assert.IsType<PropertyInfo>(resolution.ResolvedProperty);
        Assert.Equal(name, target.Name);
        Assert.Null(target.Declaration);
        Assert.NotEqual(PropertyShape.Builtin, target.Shape);
        return target;
    }

    private static void AssertNoSites(SemanticModel model, params string[] names)
    {
        foreach (var name in names)
        {
            Assert.Empty(model.FindDeclarations(name));
            Assert.Empty(model.FindResolutions(name));
            Assert.DoesNotContain(model.IdentifierOccurrences, occurrence => occurrence.Name == name);
            Assert.Empty(model.FindProperties(name));
        }
    }

    [Fact]
    public void ModuleProvenance_ImportedPrivateDeclarationDoesNotHijackDocumentLookup()
    {
        // K7-SEM-R1, repro A. The module's private `Fee` is declared at MODULE coordinates
        // 2:1–2:3, which coincide with the document's `Total` reference at 2:1–2:5: a
        // definition site registered for it sorted ahead of the document's own site and won
        // FindResolutionAt(2, 1).
        const string source = "open 'https://katlang.org/lib2.kat'\nTotal + 1";
        var remoteFiles = new Dictionary<string, string>
        {
            ["https://katlang.org/lib2.kat"] = "public Total = 5\nFee = 9",
        };
        var model = BuildModel(source, remoteFiles);

        var reference = ResolutionAt(model, 2, 1);
        Assert.Equal("Total", reference.Occurrence.Name);
        AssertSpan(reference.Occurrence.Span, 2, 1, 2, 5);
        Assert.Equal(OccurrenceKind.ResolveReference, reference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, reference.Classification);
        var target = AssertModuleProvidedTarget(reference, "Total");
        Assert.Equal(PropertyShape.Ordinary, target.Shape);
        Assert.True(target.IsPublic);
        Assert.True(target.IsExported);
        Assert.Same(target, model.FindPropertyAt(2, 1));
        Assert.Same(target, Assert.Single(model.FindProperties("Total")));

        // Fee contributes no site of any kind, and neither does the imported Total's own
        // declaration: the document's reference is the only site in this model.
        AssertNoSites(model, "Fee");
        Assert.Empty(model.Declarations);
        Assert.Same(reference, Assert.Single(model.IdentifierResolutions));
        Assert.Same(reference.Occurrence, Assert.Single(model.IdentifierOccurrences));

        AssertIdentifierSitesSliceToTheirSpelling(model, source);
        AssertPositionalQueriesReturnOnlyDocumentSites(model, source);
        Assert.Equal("6", Evaluate(source, remoteFiles));
    }

    [Fact]
    public void ModuleProvenance_ImportedDeclarationsExposeNoDocumentSites()
    {
        // K7-SEM-R1, repro B. Module coordinates 1:8–1:10 slice the document's URL ("ttp")
        // and 2:1–2:6 slice "Tax + ": neither may surface as a declaration of this document,
        // and neither range may acquire an identifier-definition classification.
        const string source = "open 'https://katlang.org/lib.kat'\nTax + 1";
        var remoteFiles = new Dictionary<string, string>
        {
            ["https://katlang.org/lib.kat"] = "public Tax = 21\nHelper = 9",
        };
        var model = BuildModel(source, remoteFiles);

        Assert.Empty(model.Declarations);
        Assert.DoesNotContain(
            model.IdentifierResolutions,
            resolution => resolution.Classification == IdentifierClassification.PropertyDefinition);
        AssertNoIdentifierSemanticSiteOverlaps(model, StringLiteralSpan(source));
        Assert.Null(model.FindResolutionAt(1, 8));

        var reference = ResolutionAt(model, 2, 1);
        Assert.Equal("Tax", reference.Occurrence.Name);
        AssertSpan(reference.Occurrence.Span, 2, 1, 2, 3);
        Assert.Equal(OccurrenceKind.ResolveReference, reference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, reference.Classification);
        var target = AssertModuleProvidedTarget(reference, "Tax");
        Assert.True(target.IsPublic);
        Assert.Same(reference, Assert.Single(model.FindResolutions("Tax")));

        // Every position of "Tax + " sees the document's reference or nothing — never Helper.
        for (var column = 1; column <= 6; column++)
            Assert.Same(column <= 3 ? reference : null, model.FindResolutionAt(2, column));
        AssertNoSites(model, "Helper");

        AssertIdentifierSitesSliceToTheirSpelling(model, source);
        AssertPositionalQueriesReturnOnlyDocumentSites(model, source);
        Assert.Equal("22", Evaluate(source, remoteFiles));
    }

    [Fact]
    public void ModuleProvenance_DocumentOwnedOpenBlockAndNestedAlgorithmKeepTheirSites()
    {
        // Positive control with the same names declared by the DOCUMENT: suppression follows
        // module provenance, not the presence of an `open`. The inline open block's private
        // Fee and the nested Lib's private Helper keep their local sites even though they are
        // invisible outside their scopes.
        const string source = """
            open {
              public Total = Fee - 4
              Fee = 9
            }
            Lib = {
              public Tax = Helper + 12
              Helper = 9
            }
            Total + Lib.Tax
            """;
        var model = BuildModel(source);

        Assert.Equal(
            [("Total", 2, 10, 14), ("Fee", 3, 3, 5), ("Lib", 5, 1, 3), ("Tax", 6, 10, 12), ("Helper", 7, 3, 8)],
            model.Declarations
                .Select(static declaration => (declaration.Name, declaration.Span.StartLineNumber, declaration.Span.StartColumn, declaration.Span.EndColumn))
                .ToList());
        foreach (var declaration in model.Declarations)
        {
            Assert.Equal(OccurrenceKind.PropertyDefinition, declaration.Kind);
            var definition = Assert.Single(
                model.IdentifierResolutions,
                resolution => ReferenceEquals(resolution.Occurrence, declaration));
            Assert.Equal(IdentifierClassification.PropertyDefinition, definition.Classification);
            Assert.Same(declaration, definition.ResolvedDeclaration);
            Assert.Same(model.FindPropertyByDeclaration(declaration), definition.ResolvedProperty);
            Assert.Same(declaration, definition.ResolvedProperty!.Declaration);
        }

        var fee = Assert.Single(model.FindDeclarations("Fee"));
        var feeReference = ResolutionAt(model, 2, 18);
        Assert.Equal(OccurrenceKind.ResolveReference, feeReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, feeReference.Classification);
        Assert.Same(fee, feeReference.ResolvedDeclaration);

        var helper = Assert.Single(model.FindDeclarations("Helper"));
        var helperReference = ResolutionAt(model, 6, 16);
        Assert.Equal(IdentifierClassification.PropertyReference, helperReference.Classification);
        Assert.Same(helper, helperReference.ResolvedDeclaration);

        var total = Assert.Single(model.FindDeclarations("Total"));
        var totalReference = ResolutionAt(model, 9, 1);
        Assert.Equal(IdentifierClassification.PropertyReference, totalReference.Classification);
        Assert.Same(total, totalReference.ResolvedDeclaration);
        Assert.Same(total, totalReference.ResolvedProperty!.Declaration);

        var lib = Assert.Single(model.FindDeclarations("Lib"));
        Assert.Same(lib, ResolutionAt(model, 9, 9).ResolvedDeclaration);
        var tax = Assert.Single(model.FindDeclarations("Tax"));
        var taxReference = ResolutionAt(model, 9, 13);
        Assert.Equal(OccurrenceKind.DotMemberReference, taxReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, taxReference.Classification);
        Assert.Same(tax, taxReference.ResolvedDeclaration);

        // Visibility: the open provides Total (public) to the root, never Fee; inside the
        // block both are directly visible with their local declaration sites.
        var root = model.FindScopeAt(9, 1);
        Assert.Same(total, SingleSymbol(root, "Total").Declaration);
        Assert.DoesNotContain(root.Symbols, symbol => symbol.Name is "Fee" or "Tax" or "Helper");
        var block = model.FindScopeAt(3, 3);
        Assert.Same(fee, SingleSymbol(block, "Fee").Declaration);
        Assert.Same(total, SingleSymbol(block, "Total").Declaration);

        AssertIdentifierSitesSliceToTheirSpelling(model, source);
        AssertPositionalQueriesReturnOnlyDocumentSites(model, source);
        Assert.Equal("26", KatLangEngine.EvaluateToString(source));
    }

    [Fact]
    public void ModuleProvenance_LocalContentAfterImportedOpenKeepsItsSites()
    {
        // Suppression must not leak past the imported subtree: document declarations,
        // references, and a nested algorithm written AFTER the open keep every site, a local
        // Helper shadows the module's public Helper (direct beats open), and references to the
        // imported Total still bind to the locationless imported target.
        const string source = """
            open 'https://katlang.org/lib.kat'
            Local = Total + 1
            Helper = 3
            F = {
              Fee = Helper + Total
              Fee
            }
            Local + F
            """;
        var remoteFiles = new Dictionary<string, string>
        {
            ["https://katlang.org/lib.kat"] = "public Total = 5\nFee = 9\npublic Helper = 100",
        };
        var model = BuildModel(source, remoteFiles);

        Assert.Equal(
            [("Local", 2, 1, 5), ("Helper", 3, 1, 6), ("F", 4, 1, 1), ("Fee", 5, 3, 5)],
            model.Declarations
                .Select(static declaration => (declaration.Name, declaration.Span.StartLineNumber, declaration.Span.StartColumn, declaration.Span.EndColumn))
                .ToList());

        var helper = Assert.Single(model.FindDeclarations("Helper"));
        var helperReference = ResolutionAt(model, 5, 9);
        Assert.Equal(IdentifierClassification.PropertyReference, helperReference.Classification);
        Assert.Same(helper, helperReference.ResolvedDeclaration);
        Assert.Same(helper, helperReference.ResolvedProperty!.Declaration);

        var fee = Assert.Single(model.FindDeclarations("Fee"));
        var feeReference = ResolutionAt(model, 6, 3);
        Assert.Equal(IdentifierClassification.PropertyReference, feeReference.Classification);
        Assert.Same(fee, feeReference.ResolvedDeclaration);

        foreach (var (line, column) in new[] { (2, 9), (5, 18) })
        {
            var totalReference = ResolutionAt(model, line, column);
            Assert.Equal("Total", totalReference.Occurrence.Name);
            Assert.Equal(IdentifierClassification.PropertyReference, totalReference.Classification);
            AssertModuleProvidedTarget(totalReference, "Total");
        }

        Assert.Same(Assert.Single(model.FindDeclarations("Local")), ResolutionAt(model, 8, 1).ResolvedDeclaration);
        Assert.Same(Assert.Single(model.FindDeclarations("F")), ResolutionAt(model, 8, 9).ResolvedDeclaration);
        Assert.Equal(2, model.FindResolutions("Total").Count);
        Assert.Equal(2, model.FindResolutions("Fee").Count);
        Assert.Equal(2, model.FindResolutions("Helper").Count);

        // The nested block sees its own Fee and the local Helper; the module's private Fee and
        // public Helper never reach either scope, and Total is visible without a location.
        var block = model.FindScopeAt(6, 3);
        Assert.Same(fee, SingleSymbol(block, "Fee").Declaration);
        Assert.Same(helper, SingleSymbol(block, "Helper").Declaration);
        Assert.Null(SingleSymbol(block, "Total").Declaration);
        var root = model.FindScopeAt(8, 1);
        Assert.DoesNotContain(root.Symbols, symbol => symbol.Name == "Fee");
        Assert.Same(helper, SingleSymbol(root, "Helper").Declaration);
        var visibleTotal = SingleSymbol(root, "Total");
        Assert.Equal(IdentifierClassification.PropertyReference, visibleTotal.Classification);
        Assert.Null(visibleTotal.Declaration);
        Assert.Equal("Total", visibleTotal.Property!.Name);

        AssertIdentifierSitesSliceToTheirSpelling(model, source);
        AssertPositionalQueriesReturnOnlyDocumentSites(model, source);
        Assert.Equal("14", Evaluate(source, remoteFiles));
    }

    [Fact]
    public void ModuleProvenance_SuppressionIsInheritedAtEveryDepthAndAcrossChainedModules()
    {
        // An ordinary nested algorithm inside the module, and a module that opens another
        // module: no declaration, reference, or classification site surfaces from any depth,
        // while the document's references bind to the imported targets.
        const string source = "open 'https://katlang.org/lib.kat'\nTax + Deep.Inner";
        var remoteFiles = new Dictionary<string, string>
        {
            ["https://katlang.org/lib.kat"] = """
                open 'https://katlang.org/base.kat'
                public Tax = Base + 1
                public Deep = {
                  public Inner = Base - 19
                  Secret = 2
                  Inner
                }
                Helper = 9
                """,
            ["https://katlang.org/base.kat"] = "public Base = 20\nHidden = 3",
        };
        var fetched = new List<string>();
        var model = BuildModel(source, TrackingDownloader(remoteFiles, fetched));

        // Both modules were elaborated (not deferred): the sources were fetched and no name
        // is left indeterminate.
        Assert.Equal(["https://katlang.org/lib.kat", "https://katlang.org/base.kat"], fetched);
        Assert.DoesNotContain(
            model.IdentifierResolutions,
            resolution => resolution.Classification is IdentifierClassification.DeferredModuleReference or IdentifierClassification.Unresolved);

        Assert.Empty(model.Declarations);
        Assert.Equal(
            [("Tax", 2, 1, 3), ("Deep", 2, 7, 10), ("Inner", 2, 12, 16)],
            model.IdentifierOccurrences
                .Select(static occurrence => (occurrence.Name, occurrence.Span.StartLineNumber, occurrence.Span.StartColumn, occurrence.Span.EndColumn))
                .ToList());
        AssertNoSites(model, "Base", "Hidden", "Secret", "Helper");

        var taxReference = ResolutionAt(model, 2, 1);
        Assert.Equal(IdentifierClassification.PropertyReference, taxReference.Classification);
        AssertModuleProvidedTarget(taxReference, "Tax");

        var deepReference = ResolutionAt(model, 2, 7);
        Assert.Equal(IdentifierClassification.PropertyReference, deepReference.Classification);
        AssertModuleProvidedTarget(deepReference, "Deep");

        var innerReference = ResolutionAt(model, 2, 12);
        Assert.Equal(OccurrenceKind.DotMemberReference, innerReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, innerReference.Classification);
        var inner = AssertModuleProvidedTarget(innerReference, "Inner");
        Assert.True(inner.IsPublic);
        Assert.Same(innerReference, Assert.Single(model.FindResolutions("Inner")));

        // Visibility: lib's public names, and nothing that lib merely opened or kept private.
        // Deep's structural member surface lists its exported members (private ones included,
        // as structural dot access reaches them), every one locationless.
        var root = Assert.Single(model.ScopeVisibilities);
        Assert.Null(root.Span);
        Assert.Equal(["Deep", "Tax"], root.Symbols.Select(static symbol => symbol.Name).ToList());
        var deep = SingleSymbol(root, "Deep");
        Assert.Null(deep.Declaration);
        Assert.Equal(["Inner", "Secret"], deep.Members.Select(static member => member.Name).ToList());
        Assert.All(deep.Members, member => Assert.Null(member.Declaration));
        Assert.All(deep.Members, member => Assert.Null(member.Property!.Declaration));

        AssertIdentifierSitesSliceToTheirSpelling(model, source);
        AssertPositionalQueriesReturnOnlyDocumentSites(model, source);
        Assert.Equal("22", Evaluate(source, remoteFiles));
    }

    [Fact]
    public void ModuleProvenance_ImportedCallableMetadataCarriesNoDocumentSpans()
    {
        // Imported explicit parameters and clause binders are declarations positioned in the
        // module: they register no sites, and the imported property metadata keeps its
        // callable shape without any span a consumer could take for a document position.
        const string source = "open 'https://katlang.org/lib.kat'\nScale(2) + Pick(1)";
        var remoteFiles = new Dictionary<string, string>
        {
            ["https://katlang.org/lib.kat"] = "public Scale(x) = x * 2\npublic Pick(0) = 0\npublic Pick(n) = n",
        };
        var model = BuildModel(source, remoteFiles);

        Assert.Empty(model.Declarations);
        AssertNoSites(model, "x", "n");

        var scale = AssertModuleProvidedTarget(ResolutionAt(model, 2, 1), "Scale");
        Assert.Equal(PropertyShape.Ordinary, scale.Shape);
        AssertPropertySignature(scale, "Scale(x)", "x");
        var x = Assert.Single(scale.Parameters);
        Assert.Equal(PropertyParameterKind.Explicit, x.Kind);
        Assert.Null(x.Span);
        Assert.All(scale.Signatures.SelectMany(static signature => signature.Parameters), parameter => Assert.Null(parameter.Span));

        var pick = AssertModuleProvidedTarget(ResolutionAt(model, 2, 12), "Pick");
        Assert.Equal(PropertyShape.Conditional, pick.Shape);
        Assert.Equal(["Pick(0)", "Pick(n)"], pick.ConditionalBranches.Select(static branch => branch.HeadText).ToList());
        Assert.All(pick.ConditionalBranches, branch => Assert.Null(branch.HeadSpan));
        Assert.All(pick.Signatures.SelectMany(static signature => signature.Parameters), parameter => Assert.Null(parameter.Span));

        // Apart from the spans, the imported metadata is exactly what the same declarations
        // produce when they are written in the document itself.
        var local = BuildModel("public Scale(x) = x * 2\npublic Pick(0) = 0\npublic Pick(n) = n\nScale(2) + Pick(1)");
        var localScale = SingleProperty(local, "Scale");
        Assert.Equal(localScale.DisplaySignature, scale.DisplaySignature);
        Assert.Equal(
            localScale.Signatures.Select(static signature => signature.DisplayText),
            scale.Signatures.Select(static signature => signature.DisplayText));
        Assert.NotNull(Assert.Single(localScale.Parameters).Span);
        var localPick = SingleProperty(local, "Pick");
        Assert.Equal(localPick.DisplaySignature, pick.DisplaySignature);
        Assert.Equal(
            localPick.ConditionalBranches.Select(static branch => branch.HeadText),
            pick.ConditionalBranches.Select(static branch => branch.HeadText));
        Assert.Equal(
            localPick.Signatures.Select(static signature => signature.DisplayText),
            pick.Signatures.Select(static signature => signature.DisplayText));
        Assert.All(localPick.ConditionalBranches, branch => Assert.NotNull(branch.HeadSpan));

        AssertIdentifierSitesSliceToTheirSpelling(model, source);
        AssertPositionalQueriesReturnOnlyDocumentSites(model, source);
        Assert.Equal("5", Evaluate(source, remoteFiles));
    }

    [Fact]
    public void ModuleProvenance_LookupReachingAnUnwalkedModuleSubtreeIsLocationless()
    {
        // Provenance is structural, not a walk position: A's body is analyzed before the walk
        // reaches M's value (the module), so the lookup of T — a member of the NESTED module
        // algorithm Sub, reached through `open M.Sub` — creates T's symbol from document
        // context. It must still be locationless, and Sub/T/Hid must register no sites.
        const string source = "open M.Sub\nA = T\nM = load('https://katlang.org/lib.kat')\nA + 1";
        var remoteFiles = new Dictionary<string, string>
        {
            ["https://katlang.org/lib.kat"] = "public Sub = {\n  public T = 4\n  Hid = 1\n}",
        };
        var model = BuildModel(source, remoteFiles);

        Assert.Equal(
            [("A", 2, 1, 1), ("M", 3, 1, 1)],
            model.Declarations
                .Select(static declaration => (declaration.Name, declaration.Span.StartLineNumber, declaration.Span.StartColumn, declaration.Span.EndColumn))
                .ToList());
        AssertNoSites(model, "Hid");
        Assert.Empty(model.FindDeclarations("Sub"));
        Assert.Empty(model.FindDeclarations("T"));

        var openHead = ResolutionAt(model, 1, 6);
        Assert.Equal(OccurrenceKind.OpenTargetReference, openHead.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.OpenTarget, openHead.Classification);
        Assert.Same(Assert.Single(model.FindDeclarations("M")), openHead.ResolvedDeclaration);

        var openMember = ResolutionAt(model, 1, 8);
        Assert.Equal(OccurrenceKind.OpenTargetMemberReference, openMember.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.OpenTarget, openMember.Classification);
        AssertModuleProvidedTarget(openMember, "Sub");

        var tReference = ResolutionAt(model, 2, 5);
        Assert.Equal(OccurrenceKind.ResolveReference, tReference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, tReference.Classification);
        AssertModuleProvidedTarget(tReference, "T");
        Assert.Same(tReference, Assert.Single(model.FindResolutions("T")));

        AssertIdentifierSitesSliceToTheirSpelling(model, source);
        AssertPositionalQueriesReturnOnlyDocumentSites(model, source);
        Assert.Equal("5", Evaluate(source, remoteFiles));
    }

    [Fact]
    public void ModuleProvenance_EqualCoordinatesDoNotConflateDistinctSourceAnchors()
    {
        const string source = "open 'https://katlang.org/lib.kat'\nTotal";
        var model = BuildModel(source, new Dictionary<string, string>
        {
            ["https://katlang.org/lib.kat"] = "public Total = 5\nTotal",
        });

        // The module's own Total reference has exactly the document reference's spelling
        // AND coordinates. Only the distinct, document-backed occurrence may be emitted.
        var reference = Assert.Single(model.IdentifierResolutions);
        Assert.Equal("Total", reference.Occurrence.Name);
        Assert.Equal(OccurrenceKind.ResolveReference, reference.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.PropertyReference, reference.Classification);
        AssertSpan(reference.Occurrence.Span, 2, 1, 2, 5);
        var target = AssertModuleProvidedTarget(reference, "Total");
        Assert.Same(target, Assert.Single(model.GetVisibleSymbolsAt(2, 1), symbol => symbol.Name == "Total").Property);
        Assert.Empty(model.Declarations);
        AssertIdentifierSitesSliceToTheirSpelling(model, source);
        AssertPositionalQueriesReturnOnlyDocumentSites(model, source);
    }

    [Fact]
    public async Task ModuleProvenance_AnalyzingModuleAsCurrentRootKeepsItsOwnSites()
    {
        const string moduleSource = "open 'https://katlang.org/base.kat'\npublic Total = Base + 1\nTotal";
        var parsed = await Parser.ParseAsync("open 'https://katlang.org/lib.kat'\nTotal", new RunOptions
        {
            DownloadCode = (url, _) => ValueTask.FromResult(url.EndsWith("/lib.kat", StringComparison.Ordinal)
                ? moduleSource : "public Base = 4\nHidden = 3"),
        });
        Assert.False(parsed.HasErrors);
        Assert.False(Assert.IsType<Algorithm.User>(parsed.Root).IsModuleElaborated);
        var module = Assert.IsType<Algorithm.User>(
            Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(parsed.Root.Opens)).Algorithm);
        Assert.True(module.IsModuleElaborated);

        // Supplying the loaded algorithm itself to Build chooses THAT source as the
        // current document. Its own mark is ignored, while its nested import still counts.
        var model = SemanticModelBuilder.Build(module);
        var total = Assert.Single(model.FindDeclarations("Total"));
        AssertSpan(total.Span, 2, 8, 2, 12);
        var reference = ResolutionAt(model, 3, 1);
        Assert.Equal(IdentifierClassification.PropertyReference, reference.Classification);
        Assert.Same(total, reference.ResolvedDeclaration);
        Assert.Same(model.FindPropertyByDeclaration(total), reference.ResolvedProperty);
        var imported = ResolutionAt(model, 2, 16);
        Assert.Equal("Base", imported.Occurrence.Name);
        Assert.Equal(IdentifierClassification.PropertyReference, imported.Classification);
        AssertModuleProvidedTarget(imported, "Base");
        AssertNoSites(model, "Hidden");
        Assert.Empty(model.FindDeclarations("Base"));
        AssertIdentifierSitesSliceToTheirSpelling(model, moduleSource);
        AssertPositionalQueriesReturnOnlyDocumentSites(model, moduleSource);
    }

    [Fact]
    public async Task ModuleProvenance_CachedModuleDagSharesLocationlessTargets()
    {
        const string source = "A = load('https://katlang.org/lib.kat')\nB = load('https://katlang.org/lib.kat')\nA.F(2) + B.F(3)";
        var fetches = 0;
        var parsed = await Parser.ParseAsync(source, new RunOptions
        {
            DownloadCode = (_, _) =>
            {
                fetches++;
                return ValueTask.FromResult("public F(x) = x + 1\nHidden = 9");
            },
        });
        Assert.False(parsed.HasErrors);
        Assert.Equal(1, fetches);
        Assert.Same(parsed.Root.Properties[0].Value, parsed.Root.Properties[1].Value);

        var model = SemanticModelBuilder.Build(parsed);
        Assert.Equal(["A", "B"], model.Declarations.Select(declaration => declaration.Name));
        var first = ResolutionAt(model, 3, 3);
        var second = ResolutionAt(model, 3, 12);
        Assert.Equal(IdentifierClassification.PropertyReference, first.Classification);
        Assert.Equal(IdentifierClassification.PropertyReference, second.Classification);
        Assert.Equal(OccurrenceKind.DotMemberReference, first.Occurrence.Kind);
        Assert.Equal(OccurrenceKind.DotMemberReference, second.Occurrence.Kind);
        var target = AssertModuleProvidedTarget(first, "F");
        Assert.Same(target, AssertModuleProvidedTarget(second, "F"));
        AssertPropertySignature(target, "F(x)", "x");
        AssertNoSites(model, "Hidden", "x");
        AssertIdentifierSitesSliceToTheirSpelling(model, source);
        AssertPositionalQueriesReturnOnlyDocumentSites(model, source);
        Assert.Equal(1, fetches); // Building and querying the model perform no I/O.
    }

    [Fact]
    public async Task ModuleProvenance_SharedImportedNodesDoNotAcquireDocumentSites()
    {
        const string source = "open 'https://katlang.org/lib.kat', 'https://katlang.org/other.kat'\nAlias = 0\nLocal = 3\nLocal";
        var parsed = await Parser.ParseAsync(source, new RunOptions
        {
            DownloadCode = (url, _) => ValueTask.FromResult(url.EndsWith("/lib.kat", StringComparison.Ordinal)
                ? "public F(x) = x + 1\nFee = 9\n{ F(2) }"
                : "public F(other) = other + 2"),
        });
        Assert.False(parsed.HasErrors);
        var module = Assert.IsType<Expr.AlgorithmExpr>(parsed.Root.Opens[0]).Algorithm;
        var imported = Assert.Single(module.Properties, property => property.Name == "F");
        var alias = Assert.Single(parsed.Root.Properties, property => property.Name == "Alias");
        var sharedBlock = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(module.Output));

        // The public Build(Algorithm) path accepts shared acyclic graphs. Moving the SAME
        // imported declaration/reference under another parent does not rebase its source.
        // Alias has a local declaration and a copied algorithm with shared imported
        // body/parameter nodes. F is also installed directly: it must beat BOTH opens.
        var root = parsed.Root with
        {
            Properties = [imported, alias with { Value = imported.Value with { } },
                .. parsed.Root.Properties.Where(property => property.Name != "Alias")],
            Output = new OutputBundle([sharedBlock,
                sharedBlock with { Algorithm = sharedBlock.Algorithm with { } }, .. parsed.Root.Output]),
        };
        var model = SemanticModelBuilder.Build(root);

        Assert.Equal(["Alias", "Local"], model.Declarations.Select(declaration => declaration.Name));
        AssertNoSites(model, "F", "Fee", "x", "other");
        var local = ResolutionAt(model, 4, 1);
        Assert.Equal("Local", local.Occurrence.Name);
        Assert.Same(Assert.Single(model.FindDeclarations("Local")), local.ResolvedDeclaration);
        var aliasInfo = SingleProperty(model, "Alias");
        Assert.Same(Assert.Single(model.FindDeclarations("Alias")), aliasInfo.Declaration);
        AssertPropertySignature(aliasInfo, "Alias(x)", "x");
        Assert.Null(Assert.Single(aliasInfo.Parameters).Span);
        var visible = Assert.Single(model.GetVisibleSymbolsAt(4, 1), symbol => symbol.Name == "F");
        Assert.Equal(IdentifierClassification.PropertyReference, visible.Classification);
        Assert.Null(visible.Declaration);
        Assert.Equal("F(x)", visible.Property!.DisplaySignature);
        // The copied block's module-relative extent must not create a local scope over
        // the document's Local declaration either. This checks extent provenance, not spelling.
        Assert.Same(model.ScopeVisibilities[0], model.FindScopeAt(3, 1));
        AssertIdentifierSitesSliceToTheirSpelling(model, source);
        AssertPositionalQueriesReturnOnlyDocumentSites(model, source);
    }

    [Fact]
    public async Task ModuleProvenance_LocalAliasToImportedBodyKeepsOnlyLocalDeclarationSpans()
    {
        const string source = "open 'https://katlang.org/lib.kat'\nAlias = 0\nAlias";
        var parsed = await Parser.ParseAsync(source, new RunOptions
        {
            DownloadCode = (_, _) => ValueTask.FromResult(
                "public Pick(n, 0) = n\npublic Pick(n, k) = n + k"),
        });
        Assert.False(parsed.HasErrors);
        var module = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(parsed.Root.Opens)).Algorithm;
        var imported = Assert.Single(module.Properties);
        var alias = Assert.Single(parsed.Root.Properties);
        var model = SemanticModelBuilder.Build(parsed.Root with
        {
            // Copying the family retains shared branch patterns and bodies, whose spans
            // still belong to the module even though this algorithm has a local owner.
            Properties = [alias with { Value = imported.Value with { } }],
        });

        var info = SingleProperty(model, "Alias");
        Assert.Equal(PropertyShape.Conditional, info.Shape);
        var declaration = Assert.Single(model.FindDeclarations("Alias"));
        Assert.Same(declaration, info.Declaration);
        Assert.Same(declaration.Span, info.ConditionalBranches[0].HeadSpan);
        Assert.Equal("n", info.Signatures[0].Parameters[0].Name);
        Assert.Null(info.Signatures[0].Parameters[0].Span);
        Assert.Same(info, ResolutionAt(model, 3, 1).ResolvedProperty);
        AssertNoSites(model, "Pick", "n", "k");
        AssertIdentifierSitesSliceToTheirSpelling(model, source);
        AssertPositionalQueriesReturnOnlyDocumentSites(model, source);
    }

    [Fact]
    public void ModuleProvenance_VisibilityAndDeferredModuleBoundaryAreUnchanged()
    {
        // The eager open's public name stays visible (locationless) and its private name does
        // not leak; the deferred branch (B2c) keeps its indeterminate classification and its
        // module is never fetched — by the model build or by an evaluation that selects the
        // other branch.
        const string source = """
            open 'https://katlang.org/lib2.kat'
            F(0) = {
              open 'https://katlang.org/deferred.kat'
              Later + Total
            }
            F(1) = Total
            F(1)
            """;
        var remoteFiles = new Dictionary<string, string>
        {
            ["https://katlang.org/lib2.kat"] = "public Total = 5\nFee = 9",
        };
        var fetched = new List<string>();
        var model = BuildModel(source, TrackingDownloader(remoteFiles, fetched));
        Assert.Equal(["https://katlang.org/lib2.kat"], fetched);

        var later = Assert.Single(model.FindResolutions("Later"));
        Assert.Equal(IdentifierClassification.DeferredModuleReference, later.Classification);
        Assert.Null(later.ResolvedDeclaration);
        Assert.Null(later.ResolvedProperty);

        // Under the deferred open, the eagerly imported Total is indeterminate (the deferred
        // module may supply or ambiguate it); outside it, it is the imported target.
        var deferredTotal = ResolutionAt(model, 4, 11);
        Assert.Equal(IdentifierClassification.DeferredModuleReference, deferredTotal.Classification);
        Assert.Null(deferredTotal.ResolvedDeclaration);
        var eagerTotal = ResolutionAt(model, 6, 8);
        Assert.Equal(IdentifierClassification.PropertyReference, eagerTotal.Classification);
        AssertModuleProvidedTarget(eagerTotal, "Total");

        var visibleTotal = Assert.Single(model.GetVisibleSymbolsAt(6, 8), symbol => symbol.Name == "Total");
        Assert.Equal(IdentifierClassification.PropertyReference, visibleTotal.Classification);
        Assert.Null(visibleTotal.Declaration);
        Assert.Equal("Total", visibleTotal.Property!.Name);
        Assert.DoesNotContain(model.GetVisibleSymbolsAt(6, 8), symbol => symbol.Name == "Fee");
        var deferredVisibleTotal = Assert.Single(model.GetVisibleSymbolsAt(4, 3), symbol => symbol.Name == "Total");
        Assert.Equal(IdentifierClassification.DeferredModuleReference, deferredVisibleTotal.Classification);
        Assert.Null(deferredVisibleTotal.Declaration);
        Assert.DoesNotContain(model.GetVisibleSymbolsAt(4, 3), symbol => symbol.Name == "Fee");

        AssertNoSites(model, "Fee");
        Assert.Equal(2, model.FindDeclarations("F").Count);
        AssertIdentifierSitesSliceToTheirSpelling(model, source);
        AssertPositionalQueriesReturnOnlyDocumentSites(model, source);

        var evaluationFetches = new List<string>();
        Assert.Equal("5", Evaluate(source, TrackingDownloader(remoteFiles, evaluationFetches)));
        Assert.Equal(["https://katlang.org/lib2.kat"], evaluationFetches);
    }

    [Fact]
    public void ScopeVisibility_DeconstructionSyntheticsNeverSurface()
    {
        var model = BuildModel("x, *y = (1, 2, 3)\nx");

        var root = model.FindScopeAt(2, 1);
        Assert.Single(root.Symbols, symbol => symbol.Name == "x");
        Assert.Single(root.Symbols, symbol => symbol.Name == "y");
        Assert.DoesNotContain(root.Symbols, symbol => symbol.Name.StartsWith('$'));
    }

    [Fact]
    public void PreludeCatalog_CoversPreludeWithSignatures()
    {
        var names = PreludeCatalog.Symbols.Select(static symbol => symbol.Name).ToList();

        // Every BuiltinId spelling plus load and Math, no duplicates.
        foreach (var builtin in Enum.GetValues<BuiltinId>())
            Assert.Contains(builtin.ToString(), names);
        Assert.Contains("load", names);
        Assert.Contains("Math", names);
        Assert.Equal(names.Count, names.Distinct(StringComparer.Ordinal).Count());

        var count = Assert.Single(PreludeCatalog.Symbols, symbol => symbol.Name == "count");
        Assert.Equal("count(collection)", count.Property!.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal("collection.count", count.Property!.GetDisplaySignature(PropertyCallStyle.Dot));
        Assert.NotNull(count.Property!.FindSignature(PropertyCallStyle.Dot));

        // Every runtime callable follows the same receiver-injection rule.
        var ifSymbol = Assert.Single(PreludeCatalog.Symbols, symbol => symbol.Name == "if");
        Assert.Equal(
            "condition.if(whenTrue, whenFalse)",
            ifSymbol.Property!.FindSignature(PropertyCallStyle.Dot)!.DisplayText);

        var atoms = Assert.Single(PreludeCatalog.Symbols, symbol => symbol.Name == "atoms");
        Assert.Equal("value.atoms", atoms.Property!.FindSignature(PropertyCallStyle.Dot)!.DisplayText);

        var range = Assert.Single(PreludeCatalog.Symbols, symbol => symbol.Name == "range");
        Assert.Equal("start.range(stop)", range.Property!.FindSignature(PropertyCallStyle.Dot)!.DisplayText);

        var whileSymbol = Assert.Single(PreludeCatalog.Symbols, symbol => symbol.Name == "while");
        Assert.Equal("while(step, *init)", whileSymbol.Property!.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal("step.while(*init)", whileSymbol.Property!.GetDisplaySignature(PropertyCallStyle.Dot));
        Assert.True(whileSymbol.Property.GetParameters(PropertyCallStyle.Dot).Single().IsCollecting);

        var repeat = Assert.Single(PreludeCatalog.Symbols, symbol => symbol.Name == "repeat");
        Assert.Equal("repeat(step, count, *init)", repeat.Property!.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal("step.repeat(count, *init)", repeat.Property!.GetDisplaySignature(PropertyCallStyle.Dot));

        // `load` is front-end sugar, not a runtime lexical callable. It must
        // never be offered as the fallback in `receiver.load(...)`.
        var load = Assert.Single(PreludeCatalog.Symbols, symbol => symbol.Name == "load");
        Assert.False(load.Property!.SupportsLexicalDotCall);
        Assert.Null(load.Property.FindSignature(PropertyCallStyle.Dot));

        var math = Assert.Single(PreludeCatalog.Symbols, symbol => symbol.Name == "Math");
        Assert.NotEmpty(math.Members);
        var sqrt = Assert.Single(math.Members, member => member.Name == "Sqrt");
        Assert.Equal("Sqrt(x)", sqrt.Property!.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Single(math.Members, member => member.Name == "Pi");
    }

    [Fact]
    public void Build_DotFallbackConsumesFirstParameterForUserAndConditionalCallables()
    {
        var ordinary = BuildModel(
            "Transform(value, suffix) = value\nF(x) = x.Transform('!')");
        var ordinaryFallback = PropertyAt(ordinary, 2, 12);
        Assert.Equal(PropertyCallStyle.Dot, ordinaryFallback.PreferredCallStyle);
        Assert.Equal("value.Transform(suffix)", ordinaryFallback.DisplaySignature);
        Assert.Equal(["suffix"], ordinaryFallback.Parameters.Select(static parameter => parameter.Name).ToList());

        var conditional = BuildModel(
            "Choose(0, x) = x\nChoose(n, x) = n\nF(value) = value.Choose(1)");
        var conditionalFallback = PropertyAt(conditional, 3, 18);
        Assert.Equal(PropertyShape.Conditional, conditionalFallback.Shape);
        Assert.True(conditionalFallback.SupportsLexicalDotCall);
        Assert.Equal(PropertyCallStyle.Dot, conditionalFallback.PreferredCallStyle);
        Assert.Equal("argument1.Choose(x)", conditionalFallback.DisplaySignature);
        Assert.Equal(["x"], conditionalFallback.Parameters.Select(static parameter => parameter.Name).ToList());

        var zero = SingleProperty(BuildModel("Zero = 1\nZero"), "Zero");
        Assert.False(zero.SupportsLexicalDotCall);
        Assert.Null(zero.FindSignature(PropertyCallStyle.Dot));
    }

    [Fact]
    public void Build_StructuralMemberKeepsPlainSignatureWhileFallbackUsesDotSignature()
    {
        var model = BuildModel(
            "M = { public Transform(value, suffix) = value }\nM.Transform\nTransform(value, suffix) = value\nF(x) = x.Transform('!')");

        var structural = PropertyAt(model, 2, 3);
        Assert.Equal(PropertyCallStyle.Plain, structural.PreferredCallStyle);
        Assert.Equal("Transform(value, suffix)", structural.DisplaySignature);

        var fallback = PropertyAt(model, 4, 12);
        Assert.Equal(PropertyCallStyle.Dot, fallback.PreferredCallStyle);
        Assert.Equal("value.Transform(suffix)", fallback.DisplaySignature);
    }

    [Fact]
    public void FindScopeAt_EqualHullsUseLexicalDepthNotCollectionOrder()
    {
        var span = new SourceSpan(1, 1, 1, 5);
        var outer = new ScopeVisibility(
            span,
            [new VisibleSymbol("Outer", IdentifierClassification.PropertyReference, null, null)],
            NestingDepth: 1);
        var inner = new ScopeVisibility(
            span,
            [new VisibleSymbol("Inner", IdentifierClassification.PropertyReference, null, null)],
            NestingDepth: 2);
        var root = SourceProvenance.ParseValid("1").Root;
        var model = new SemanticModel(
            root,
            [],
            [],
            [],
            [],
            new Dictionary<DeclarationOccurrence, PropertyInfo>(),
            [outer, inner, new ScopeVisibility(null, [], NestingDepth: 0)]);

        Assert.Equal("Inner", Assert.Single(model.FindScopeAt(1, 3).Symbols).Name);
    }

    [Fact]
    public void PublicSemanticDtosSnapshotInputCollections()
    {
        var parameterInputs = new List<PropertyParameterInfo>
        {
            new("value", PropertyParameterKind.Explicit, null),
        };
        var signatureInputs = new List<PropertySignatureInfo>
        {
            new(PropertyCallStyle.Plain, "F(value)", parameterInputs),
        };
        var property = new PropertyInfo(
            "F",
            null,
            PropertyShape.Ordinary,
            false,
            PropertyExposure.Exported,
            parameterInputs,
            [])
        {
            Signatures = signatureInputs,
        };
        var memberInputs = new List<VisibleSymbol>
        {
            new("M", IdentifierClassification.PropertyReference, null, null),
        };
        var symbol = new VisibleSymbol(
            "F",
            IdentifierClassification.PropertyReference,
            null,
            property,
            memberInputs);
        var symbolInputs = new List<VisibleSymbol> { symbol };
        var scope = new ScopeVisibility(null, symbolInputs);

        parameterInputs.Clear();
        signatureInputs.Clear();
        memberInputs.Clear();
        symbolInputs.Clear();

        Assert.Single(property.Parameters);
        Assert.Single(property.Signatures);
        Assert.Single(property.Signatures[0].Parameters);
        Assert.Single(symbol.Members);
        Assert.Single(scope.Symbols);
    }

    [Fact]
    public void FindPropertyByDeclaration_DoesNotCollapseEqualModuleLocalCoordinates()
    {
        var span = new SourceSpan(1, 1, 1, 1);
        var firstDeclaration = new DeclarationOccurrence("X", span, OccurrenceKind.PropertyDefinition);
        var secondDeclaration = new DeclarationOccurrence("X", span, OccurrenceKind.PropertyDefinition);
        Assert.Equal(firstDeclaration, secondDeclaration);

        var first = new PropertyInfo(
            "First",
            firstDeclaration,
            PropertyShape.Ordinary,
            false,
            PropertyExposure.Exported,
            [],
            []);
        var second = new PropertyInfo(
            "Second",
            secondDeclaration,
            PropertyShape.Ordinary,
            false,
            PropertyExposure.Exported,
            [],
            []);
        var root = SourceProvenance.ParseValid("1").Root;
        var properties = new Dictionary<DeclarationOccurrence, PropertyInfo>(ReferenceEqualityComparer.Instance)
        {
            [firstDeclaration] = first,
            [secondDeclaration] = second,
        };
        var model = new SemanticModel(root, [], [], [], [], properties, []);

        Assert.Same(first, model.FindPropertyByDeclaration(firstDeclaration));
        Assert.Same(second, model.FindPropertyByDeclaration(secondDeclaration));
        Assert.Null(model.FindPropertyByDeclaration(
            new DeclarationOccurrence("X", span, OccurrenceKind.PropertyDefinition)));
    }

    [Fact]
    public void PreludeCatalog_DotIntrinsicsAndKeywords()
    {
        var stringIntrinsic = Assert.Single(PreludeCatalog.DotIntrinsicSymbols);
        Assert.Equal("string", stringIntrinsic.Name);
        var signature = Assert.Single(stringIntrinsic.Property!.Signatures);
        Assert.Equal(PropertyCallStyle.Dot, signature.CallStyle);
        Assert.Equal("value.string", signature.DisplayText);

        Assert.Equal(
            ["div", "mod", "and", "or", "xor", "not", "public", "open"],
            PreludeCatalog.KeywordNames);
    }

    [Fact]
    public void GetVisibleSymbolsAt_NamesAreUnique()
    {
        var model = BuildModel(
            """
            sum = 5
            F(a) = {
              count = a
              count + 1
            }
            F(2)
            """);

        foreach (var (line, column) in new[] { (1, 1), (4, 5), (6, 1) })
        {
            var names = model.GetVisibleSymbolsAt(line, column).Select(static symbol => symbol.Name).ToList();
            Assert.Equal(names.Count, names.Distinct(StringComparer.Ordinal).Count());
        }
    }
}
