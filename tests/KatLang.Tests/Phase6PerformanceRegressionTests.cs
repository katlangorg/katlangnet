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
            diagnostic => Assert.Equal((5, 1), (Assert.NotNull(diagnostic.Span).Start.Line, Assert.NotNull(diagnostic.Span).Start.Column)),
            diagnostic => Assert.Equal((6, 1), (Assert.NotNull(diagnostic.Span).Start.Line, Assert.NotNull(diagnostic.Span).Start.Column)),
            diagnostic => Assert.Equal((7, 1), (Assert.NotNull(diagnostic.Span).Start.Line, Assert.NotNull(diagnostic.Span).Start.Column)));

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
        // Middle and Top are callable aliases whose chain normalizes to the root Leaf(x); the
        // shadowing block's own zero-parameter Leaf is read as a value, never aliased.
        foreach (var name in new[] { "Middle", "Top" })
        {
            var alias = Assert.IsType<Algorithm.Alias>(parsed.Root.Properties.Single(property => property.Name == name).Value);
            Assert.Empty(alias.Params);
            Assert.Equal(["x"], alias.ResolvedTarget!.Signature.Signature!.ParameterNames);
        }

        var shadow = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single(property => property.Name == "Shadow").Value);
        Assert.Empty(shadow.Params);

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
