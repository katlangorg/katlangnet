namespace KatLang.Tests;

/// <summary>Semantic-equivalence guards for the three Phase 6 declaration-scaling fixes.</summary>
public class Phase6PerformanceRegressionTests
{
    [Fact]
    public void ParserDuplicateIndex_PreservesCaseSensitivityOrderingAndDiagnosticSpans()
    {
        var result = Parser.ParseSyntax(
            """
            A = 1
            a = 2
            x, y = (3, 4)
            F(0) = 0
            A, z = (5, 6)
            y = 7
            F = 8
            """);

        var duplicates = result.Diagnostics
            .Where(diagnostic => diagnostic.Message.Contains("already defined", StringComparison.Ordinal))
            .ToList();
        Assert.Collection(
            duplicates,
            diagnostic => Assert.Equal((5, 1), (diagnostic.Span.StartLineNumber, diagnostic.Span.StartColumn)),
            diagnostic => Assert.Equal((6, 1), (diagnostic.Span.StartLineNumber, diagnostic.Span.StartColumn)),
            diagnostic => Assert.Equal((7, 1), (diagnostic.Span.StartLineNumber, diagnostic.Span.StartColumn)));

        Assert.Equal(
            ["A", "a", "$deconstruct$0", "x", "y", "$deconstruct$1", "A", "z", "y", "F", "F"],
            result.Root.Properties.Select(property => property.Name));
    }

    [Fact]
    public void ImplicitSignatureSharing_NoLocalLeavesAndLocalShadowStayIsolated()
    {
        const string source = """
            Leaf = x
            Middle = Leaf
            Shadow = {
              Leaf = 100
              Leaf
            }
            Top = Middle
            Top(7), Shadow
            """;

        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(d => d.Message)));
        Assert.Equal(["x"], parsed.Root.Properties.Single(property => property.Name == "Middle").Value.Params);
        Assert.Equal(["x"], parsed.Root.Properties.Single(property => property.Name == "Top").Value.Params);
        Assert.Empty(parsed.Root.Properties.Single(property => property.Name == "Shadow").Value.Params);

        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal([7m, 100m], success.Atoms);
    }

    [Fact]
    public void ExposureSummarySharing_LeafCapturesAndNestedLocalMapDoNotAlias()
    {
        var parsed = Parser.Parse(
            """
            Outer(x) = {
              Captured = x
              PublicContainer = {
                public Value = 1
                Value
              }
              After = Captured
              After
            }
            """);

        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(d => d.Message)));
        var outer = Assert.IsType<Algorithm.User>(Assert.Single(parsed.Root.Properties).Value);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            outer.Properties.Single(property => property.Name == "Captured").Exposure);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            outer.Properties.Single(property => property.Name == "After").Exposure);

        var container = outer.Properties.Single(property => property.Name == "PublicContainer");
        Assert.Equal(PropertyExposure.Exported, container.Exposure);
        var containerBody = Assert.IsType<Algorithm.User>(container.Value);
        Assert.Equal(PropertyExposure.Exported, Assert.Single(containerBody.Properties).Exposure);
    }
}
