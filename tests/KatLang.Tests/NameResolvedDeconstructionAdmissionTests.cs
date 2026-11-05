namespace KatLang.Tests;

/// <summary>
/// A hoisted deconstruction right-hand side is rows of the body it is written in: the synthetic source property only stores
/// them. Name-resolved admission and the standalone projection register those rows' inline blocks in that owner, exactly where
/// detection and resolution read them. <c>nameResolved: true</c> enters through
/// <see cref="ImplicitArgumentResolver.ResolveNameResolvedPrevalidated"/>, which never runs detection; <c>false</c> is the
/// normal detection route, kept as the control.
/// </summary>
public sealed class NameResolvedDeconstructionAdmissionTests
{
    private const string SourceProperty = "$deconstruct$0";

    private static Algorithm.User Block(IReadOnlyList<Property> properties, params Expr[] rows)
        => new(null, [], [], properties, new OutputBundle(rows));

    private static Algorithm.User Rows(int rowIndex, params Expr[] rows)
        => Block([], rows) with { AssignmentDeconstructionRowIndex = rowIndex };

    private static Algorithm Elaborate(Algorithm.User root, bool nameResolved)
    {
        var diagnostics = new DiagnosticBag();
        var resolved = nameResolved
            ? ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(root, diagnostics: diagnostics)
            : ImplicitArgumentResolver.ResolvePrevalidated(ParameterDetector.DetectPrevalidated(root, diagnostics: diagnostics));
        Assert.Equal(0, diagnostics.ReportedCount);
        return PropertyExposureResolver.Resolve(resolved, observations: null);
    }

    /// <summary>
    /// Parsed source. On the admission route an earlier detection only classifies its names: the detected tree then crosses the
    /// boundary as a host AST, in a fresh operation that shares nothing with that detection.
    /// </summary>
    private static Algorithm ElaborateSource(string source, bool nameResolved)
    {
        var parsed = Assert.IsType<Algorithm.User>(SourceProvenance.ParseSyntaxValidRoot(source));
        if (!nameResolved) return Elaborate(parsed, nameResolved: false);
        var detected = ParameterDetector.DetectPrevalidated(parsed);
        Assert.Empty(detected.Diagnostics);
        return Elaborate(Assert.IsType<Algorithm.User>(detected.Root), nameResolved: true);
    }

    private static void AssertValue(int expected, Algorithm exposed)
    {
        var result = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(exposed), enableOptimizations: false).Result;
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : "");
        Assert.Equal(new Result.Atom(expected), result.Value.Value);
    }

    private static Algorithm RowBlock(Algorithm owner, int row)
        => Assert.IsType<Expr.AlgorithmExpr>(owner.Properties.Single(property => property.Name == SourceProperty).Value.Output[row]).Algorithm;

    private static Algorithm.User BlockWithAMember()
        => Block([new Property("X", Block([], new Expr.Num(5)), IsPublic: true)], new Expr.Num(1));

    /// <summary>The smallest shape: one inline block in one right-hand side, with a member of its own.</summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AnInlineRowBlock_CompletesInTheEnclosingBody(bool nameResolved)
    {
        var q = Block([new Property(SourceProperty, Rows(0, new Expr.AlgorithmExpr(BlockWithAMember())))], new Expr.Num(0));
        var root = Block([new Property("Q", q, IsPublic: true)], new Expr.Num(0));

        var exposed = Elaborate(root, nameResolved);

        var publication = exposed.CompletedStructure!;
        var graph = publication.Facts;
        var qKey = graph.Member(publication.Entry!, "Q")!;
        var exposedBlock = RowBlock(exposed.Properties.Single(property => property.Name == "Q").Value, 0);
        var key = graph.Child(qKey, exposedBlock);
        Assert.NotNull(key);
        Assert.Same(qKey, key.Parent);
        Assert.Same(exposedBlock, graph.Facts(key)!.Body);
        Assert.Same(key, graph.ExactContext(exposedBlock)!.Key);
        Assert.NotNull(graph.Member(key, "X"));
        Assert.Null(graph.Child(graph.Facts(qKey)!.Members[SourceProperty], exposedBlock));
    }

    /// <summary>Admission registers what the host supplied: nothing the host left unclassified becomes a parameter here.</summary>
    [Fact]
    public void Admission_PreservesTheHostsClassifications()
    {
        var block = Block([], new Expr.Param("p"), new Expr.Resolve("Sibling"));
        var q = new Algorithm.User(null, [new CaptureParameterPattern(new ParameterDeclaration("p", null, ParameterKind.Normal))], [],
            [new Property("Sibling", Block([], new Expr.Num(1))), new Property(SourceProperty, Rows(0, new Expr.AlgorithmExpr(block)))],
            new OutputBundle([new Expr.Num(0)]));
        var root = Block([new Property("Q", q, IsPublic: true)], new Expr.Num(0));

        var exposed = Elaborate(root, nameResolved: true);

        var exposedQ = exposed.Properties.Single(property => property.Name == "Q").Value;
        Assert.Equal(["p"], exposedQ.Params);
        var exposedBlock = RowBlock(exposedQ, 0);
        Assert.Empty(exposedBlock.Params);
        Assert.Equal("p", Assert.IsType<Expr.Param>(exposedBlock.Output[0]).Name);
    }

    /// <summary>The block reads the enclosing parameter and member from its written owner, on both routes.</summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void RowBlocks_ReadTheirWrittenOwner(bool nameResolved)
    {
        const string Source = """
            Sibling = 100
            F(p) = {
                x, y = { p + 1 }, { Sibling + p }
                x + y * 10
            }
            F(2)
            """;

        AssertValue(1023, ElaborateSource(Source, nameResolved));
    }

    /// <summary>A row block's own deconstruction nests one owner deeper, and a block below an operator is still its row's block.</summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void NestedDeconstructionRows_KeepEachLevelsOwner(bool nameResolved)
    {
        const string Source = """
            F(p) = {
                a, b = {
                    c, d = { p + 1 }, 2 + { p + 2 }
                    c * d
                }, 7
                a + b
            }
            F(1)
            """;

        AssertValue(17, ElaborateSource(Source, nameResolved));
    }

    /// <summary>Two right-hand sides of one body: their written order decides the inferred parameters on both routes.</summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SeveralRightHandSides_KeepWrittenOrder(bool nameResolved)
    {
        const string Source = """
            F = {
                x, y = n + 1, { 10 }
                u, v = { 20 }, m + 1
                x + y + u + v
            }
            F(1, 2)
            """;

        var exposed = ElaborateSource(Source, nameResolved);

        Assert.Equal(["n", "m"], exposed.Properties.Single(property => property.Name == "F").Value.Params);
        AssertValue(35, exposed);
    }

    /// <summary>
    /// The standalone projection of a bound tree follows the same rule: the block's context is below the written owner, and
    /// the storage property's context owns no rows.
    /// </summary>
    [Fact]
    public void StandaloneProjection_RegistersRowBlocksInTheWrittenOwner()
    {
        var block = BlockWithAMember();
        var q = Block([new Property(SourceProperty, Rows(0, new Expr.AlgorithmExpr(block)))], new Expr.Num(0));
        var root = Block([new Property("Q", q, IsPublic: true)], new Expr.Num(0));

        var context = AnalyzedStaticStructures.ForBoundAst(root);

        var graph = context.Facts;
        var qKey = graph.Member(context.Key, "Q")!;
        var key = graph.Child(qKey, block);
        Assert.NotNull(key);
        Assert.Same(qKey, key.Parent);
        Assert.Same(block, graph.Facts(key)!.Body);
        Assert.Null(graph.Child(graph.Facts(qKey)!.Members[SourceProperty], block));
    }
}
