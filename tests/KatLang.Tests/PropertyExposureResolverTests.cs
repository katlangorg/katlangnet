namespace KatLang.Tests;

public class PropertyExposureResolverTests
{
    [Fact]
    public void Build_SummarySiblingCycle_RemainsSeparateFromDirectSiblingDependencyFacts()
    {
        var algorithm = BuildUserAlgorithmBeforeExposure(
            "Algo",
            """
            Algo(x) = {
                Left = {
                    InnerLeft = Right
                    InnerLeft
                }
                Right = {
                    InnerRight = Left
                    InnerRight
                    x
                }
                x
            }
            """);

        var graph = PropertyDependencyGraphBuilder.Build(algorithm);
        var leftNode = graph[PropertyIndex(graph, "Left")];
        var rightNode = graph[PropertyIndex(graph, "Right")];

        Assert.Empty(leftNode.SiblingDependencyIndices);
        Assert.Equal([PropertyIndex(graph, "Right")], leftNode.SummarySiblingDependencyIndices);
        Assert.Empty(leftNode.SummaryVisiblePropertyDependencyNames);
        Assert.Empty(leftNode.RequiredAncestorOwnedParameterNames);

        Assert.Empty(rightNode.SiblingDependencyIndices);
        Assert.Equal([PropertyIndex(graph, "Left")], rightNode.SummarySiblingDependencyIndices);
        Assert.Empty(rightNode.SummaryVisiblePropertyDependencyNames);
        Assert.Equal(["x"], rightNode.RequiredAncestorOwnedParameterNames);
    }

    [Fact]
    public void Parse_SummarySiblingCycle_StillRequiresExposureFixpoint()
    {
        var result = Parser.Parse(
            """
            Algo(x) = {
                Left = {
                    InnerLeft = Right
                    InnerLeft
                }
                Right = {
                    InnerRight = Left
                    InnerRight
                    x
                }
                x
            }
            """);

        Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics.Select(d => d.Message)));

        var algorithm = Assert.IsType<Algorithm.User>(Assert.Single(result.Root.Properties).Value);
        var left = Assert.Single(algorithm.Properties, property => property.Name == "Left");
        var right = Assert.Single(algorithm.Properties, property => property.Name == "Right");

        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, left.Exposure);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, right.Exposure);

        var leftBody = Assert.IsType<Algorithm.User>(left.Value);
        var rightBody = Assert.IsType<Algorithm.User>(right.Value);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(leftBody.Properties).Exposure);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(rightBody.Properties).Exposure);
    }

    [Fact]
    public void Parse_PublicTopLevelApiCallingPrivateHelperWithCapturedNestedLocal_RemainsExported()
    {
        var result = Parser.Parse(
            """
            PrivateHelper(Candidate) = {
                Step = Candidate + 1
                Step
            }

            public PublicApi(N) = PrivateHelper(N)
            """);

        Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics.Select(d => d.Message)));

        var privateHelper = Assert.Single(result.Root.Properties, property => property.Name == "PrivateHelper");
        Assert.False(privateHelper.IsPublic);
        Assert.Equal(PropertyExposure.Exported, privateHelper.Exposure);

        var helperBody = Assert.IsType<Algorithm.User>(privateHelper.Value);
        var step = Assert.Single(helperBody.Properties, property => property.Name == "Step");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, step.Exposure);

        var publicApi = Assert.Single(result.Root.Properties, property => property.Name == "PublicApi");
        Assert.True(publicApi.IsPublic);
        Assert.Equal(PropertyExposure.Exported, publicApi.Exposure);
    }

    [Fact]
    public void Build_AncestorCaptureInsideTransparentLayers_SeedsRequiredAncestorNames()
    {
        var algorithm = BuildUserAlgorithmBeforeExposure(
            "Outer",
            """
            Outer(x) = {
                Helper(y) = y + 10
                Direct = x + 1
                Grouped = (x, 1)
                Called = Helper(x)
                x
            }
            """);

        var graph = PropertyDependencyGraphBuilder.Build(algorithm);

        Assert.Equal(["x"], graph[PropertyIndex(graph, "Direct")].RequiredAncestorOwnedParameterNames);
        Assert.Equal(["x"], graph[PropertyIndex(graph, "Grouped")].RequiredAncestorOwnedParameterNames);
        Assert.Equal(["x"], graph[PropertyIndex(graph, "Called")].RequiredAncestorOwnedParameterNames);
        Assert.Empty(graph[PropertyIndex(graph, "Helper")].RequiredAncestorOwnedParameterNames);
    }

    [Fact]
    public void Parse_AncestorCaptureInParenthesizedGroup_IsLocalOnly()
    {
        var algorithm = ParseSinglePropertyBody(
            """
            Outer(x) = {
                Direct = x + 1
                Grouped = (x, 1)
                x
            }
            """);

        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(algorithm.Properties, property => property.Name == "Direct").Exposure);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(algorithm.Properties, property => property.Name == "Grouped").Exposure);
    }

    [Fact]
    public void Parse_AncestorCaptureInCallArguments_IsLocalOnly()
    {
        var algorithm = ParseSinglePropertyBody(
            """
            Outer(x) = {
                Helper(y) = y + 10
                Called = Helper(x)
                x
            }
            """);

        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(algorithm.Properties, property => property.Name == "Called").Exposure);
        Assert.Equal(
            PropertyExposure.Exported,
            Assert.Single(algorithm.Properties, property => property.Name == "Helper").Exposure);
    }

    [Fact]
    public void Parse_AncestorCaptureThroughNestedTransparentLayers_IsLocalOnly()
    {
        var algorithm = ParseSinglePropertyBody(
            """
            Outer(x) = {
                Helper(y) = y + 10
                Other(z) = z * 2
                DoubleGrouped = ((x, 1))
                GroupedArg = Helper((x, 1))
                Chained = Helper(Other(x))
                x
            }
            """);

        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(algorithm.Properties, property => property.Name == "DoubleGrouped").Exposure);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(algorithm.Properties, property => property.Name == "GroupedArg").Exposure);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(algorithm.Properties, property => property.Name == "Chained").Exposure);
        Assert.Equal(
            PropertyExposure.Exported,
            Assert.Single(algorithm.Properties, property => property.Name == "Helper").Exposure);
        Assert.Equal(
            PropertyExposure.Exported,
            Assert.Single(algorithm.Properties, property => property.Name == "Other").Exposure);
    }

    [Fact]
    public void Parse_AncestorCaptureInDotCallArguments_IsLocalOnly()
    {
        var algorithm = ParseSinglePropertyBody(
            """
            Outer(x) = {
                Data = [1, 2, 3]
                Taken = Data.take(x)
                x
            }
            """);

        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(algorithm.Properties, property => property.Name == "Taken").Exposure);
        Assert.Equal(
            PropertyExposure.Exported,
            Assert.Single(algorithm.Properties, property => property.Name == "Data").Exposure);
    }

    [Fact]
    public void Parse_OwnCallableParametersThroughTransparentLayers_RemainExported()
    {
        var algorithm = ParseSinglePropertyBody(
            """
            Outer(x) = {
                Own(a) = (a, 1)
                Forward(b) = Own(b)
                x
            }
            """);

        Assert.Equal(
            PropertyExposure.Exported,
            Assert.Single(algorithm.Properties, property => property.Name == "Own").Exposure);
        Assert.Equal(
            PropertyExposure.Exported,
            Assert.Single(algorithm.Properties, property => property.Name == "Forward").Exposure);
    }

    [Fact]
    public void Parse_BraceBlockArgumentScopes_KeepOwnershipBoundaries()
    {
        var algorithm = ParseSinglePropertyBody(
            """
            Outer(x) = {
                Apply(f) = f(3)
                OwnedBrace = Apply({y + 1})
                CapturedBrace = Apply({x + y})
                x
            }
            """);

        // The brace block owns its free name `y`, so passing it as an argument
        // does not make the containing property depend on any ancestor parameter.
        Assert.Equal(
            PropertyExposure.Exported,
            Assert.Single(algorithm.Properties, property => property.Name == "OwnedBrace").Exposure);
        // A brace block that closes over the ancestor parameter `x` still marks
        // the containing property local-only: the brace algorithm's scope
        // boundary owns `y` but not `x`.
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(algorithm.Properties, property => property.Name == "CapturedBrace").Exposure);
    }

    private static Algorithm.User ParseSinglePropertyBody(string source)
    {
        var result = Parser.Parse(source);
        Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics.Select(d => d.Message)));
        return Assert.IsType<Algorithm.User>(Assert.Single(result.Root.Properties).Value);
    }

    private static Algorithm.User BuildUserAlgorithmBeforeExposure(string propertyName, string source)
    {
        var syntaxResult = Parser.ParseSyntax(source);
        Assert.False(syntaxResult.HasErrors, string.Join(Environment.NewLine, syntaxResult.Diagnostics.Select(d => d.Message)));

        var (parameterizedRoot, parameterDiagnostics) = ParameterDetector.Detect(syntaxResult.Root);
        Assert.DoesNotContain(parameterDiagnostics, diagnostic => diagnostic.Severity == DiagnosticSeverity.Error);

        var implicitResolvedRoot = ImplicitArgumentResolver.Resolve(parameterizedRoot);
        var property = Assert.Single(implicitResolvedRoot.Properties, candidate => candidate.Name == propertyName);
        return Assert.IsType<Algorithm.User>(property.Value);
    }

    private static int PropertyIndex(PropertyDependencyGraph graph, string propertyName)
    {
        Assert.True(graph.TryGetPropertyIndex(propertyName, out var propertyIndex));
        return propertyIndex;
    }
}