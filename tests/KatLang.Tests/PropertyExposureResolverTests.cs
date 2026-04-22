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