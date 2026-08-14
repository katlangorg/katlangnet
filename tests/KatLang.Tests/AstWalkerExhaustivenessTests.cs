namespace KatLang.Tests;

/// <summary>
/// Exhaustiveness pins for the shared <see cref="AstWalker"/>.
///
/// <para><see cref="AstStructuralPreflight"/> already fails loudly on an
/// unknown AST node kind, but <see cref="AstWalker.VisitExpr"/> used to end in
/// a silent fall-through: a new <see cref="Expr"/> variant would have been
/// skipped by every walker subclass (semantic modelling, property exposure,
/// module loading, the fuzz probes) with no test failing. These tests pin both
/// halves of the contract — every current variant is reached, and every
/// composite variant's children are actually visited.</para>
/// </summary>
public class AstWalkerExhaustivenessTests
{
    private sealed class RecordingWalker : AstWalker
    {
        public List<Expr> Visited { get; } = [];

        public override void VisitExpr(Expr expr)
        {
            Visited.Add(expr);
            base.VisitExpr(expr);
        }
    }

    private sealed class DotMetadataWalker : AstWalker
    {
        public List<SourceSpan> MemberSpans { get; } = [];

        protected override void VisitDotMemberIdentifier(Expr.DotCall expr, SourceSpan span)
            => MemberSpans.Add(span);
    }

    private static Algorithm.User EmptyAlgorithm(params Expr[] output)
        => new(Parent: null, Parameters: [], Opens: [], Properties: [], Output: output);

    /// <summary>One sample per <see cref="Expr"/> variant, with the number of expression
    /// nodes a complete walk must observe (the sample itself plus its expression children).</summary>
    public static TheoryData<string, Expr, int> ExprSamples()
    {
        var leaf = new Expr.Num(1);
        return new TheoryData<string, Expr, int>
        {
            { nameof(Expr.Param), new Expr.Param("p"), 1 },
            { nameof(Expr.Num), leaf, 1 },
            { nameof(Expr.StringLiteral), new Expr.StringLiteral("s"), 1 },
            { nameof(Expr.Unary), new Expr.Unary(UnaryOp.Minus, leaf), 2 },
            { nameof(Expr.Binary), new Expr.Binary(BinaryOp.Add, leaf, leaf), 3 },
            { nameof(Expr.Index), new Expr.Index(leaf, leaf), 3 },
            { nameof(Expr.SequenceConstruct), new Expr.SequenceConstruct(leaf, leaf), 3 },
            { nameof(Expr.EmptySequence), new Expr.EmptySequence(0), 1 },
            { nameof(Expr.SequenceSpread), new Expr.SequenceSpread(leaf), 2 },
            { nameof(Expr.ListLiteral), new Expr.ListLiteral([leaf, leaf]), 3 },
            { nameof(Expr.Resolve), new Expr.Resolve("R"), 1 },
            { nameof(Expr.DotCall), new Expr.DotCall(leaf, "M", EmptyAlgorithm(leaf).Output), 3 },
            { nameof(Expr.Grace), new Expr.Grace(leaf, 1), 2 },
            { nameof(Expr.AlgorithmExpr), new Expr.AlgorithmExpr(EmptyAlgorithm(leaf)), 2 },
            { nameof(Expr.Capture), new Expr.Capture([leaf, leaf]), 3 },
            { nameof(Expr.Call), new Expr.Call(leaf, EmptyAlgorithm(leaf).Output), 3 },
            { nameof(Expr.NativeCall), new Expr.NativeCall("Abs", ["x"]), 1 },
        };
    }

    [Theory]
    [MemberData(nameof(ExprSamples))]
    public void VisitExpr_ReachesEveryVariantAndItsChildren(string variantName, Expr sample, int expectedVisits)
    {
        var walker = new RecordingWalker();
        walker.VisitExpr(sample);

        Assert.Equal(expectedVisits, walker.Visited.Count);
        Assert.Same(sample, walker.Visited[0]);
        Assert.Equal(variantName, sample.GetType().Name);
    }

    /// <summary>
    /// The sample table above must stay complete: a newly added <see cref="Expr"/>
    /// variant has to appear here (and therefore in the walker's switch) rather
    /// than being silently unwalked.
    /// </summary>
    [Fact]
    public void ExprSamples_CoverEveryExprVariant()
    {
        var declared = typeof(Expr).GetNestedTypes()
            .Where(type => !type.IsAbstract && typeof(Expr).IsAssignableFrom(type))
            .Select(type => type.Name)
            .OrderBy(name => name, StringComparer.Ordinal)
            .ToList();

        var sampled = ExprSamples()
            .Select(row => ((Expr)row[1]!).GetType().Name)
            .OrderBy(name => name, StringComparer.Ordinal)
            .ToList();

        Assert.Equal(declared, sampled);
    }

    /// <summary>
    /// The real production walkers still traverse a parsed program end to end
    /// after the exhaustiveness guard was added — the guard is unreachable for
    /// every variant the parser and front end can produce.
    /// </summary>
    [Fact]
    public void VisitExpr_WalksAParsedProgramWithoutHittingTheGuard()
    {
        var parsed = Parser.Parse("""
            open A
            A = {
                public X = 1, 2, 3
            }
            F(a) = -a + 1
            G(*items) = items.count
            H((x, y)) = [x, y]:0
            F(7), G(1, 2), H((3, 4)), 'text', (), A.X, X, if(1, 2, 3), Math.Abs(-1)
            """);
        Assert.False(
            parsed.HasErrors,
            string.Join("; ", parsed.Diagnostics.Select(diagnostic => diagnostic.Message)));

        var walker = new RecordingWalker();
        walker.VisitAlgorithm(parsed.Root);

        Assert.NotEmpty(walker.Visited);
    }

    [Fact]
    public void VisitExpr_SurfacesTheDotMemberSpanOnce()
    {
        var memberSpan = new SourceSpan(1, 4, 1, 4);
        var edge = new Expr.DotCall(new Expr.Num(1), "F")
        {
            LexicalFallback = new Expr.Resolve("F"),
            MemberSpan = memberSpan,
        };

        var walker = new DotMetadataWalker();
        walker.VisitExpr(edge);

        Assert.Equal([memberSpan], walker.MemberSpans);
    }
}
