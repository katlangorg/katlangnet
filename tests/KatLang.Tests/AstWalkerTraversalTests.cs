namespace KatLang.Tests;

/// <summary>
/// Child-traversal pins for the shared <see cref="AstWalker"/>.
///
/// <para><see cref="AstWalker.VisitExpr"/> is a side-effect visitor written as a switch
/// STATEMENT, the one dispatch shape the closed <see cref="Expr"/> hierarchy cannot make
/// compiler-exhaustive, so it keeps a fail-loud guard for an unhandled variant. These
/// tests pin what neither the compiler nor the guard can: every current variant is
/// reached without tripping the guard, and every composite variant's children are
/// actually visited (a present-but-childless arm would silently skip a subtree for every
/// walker subclass — semantic modelling, exposure resolution, module loading, the fuzz
/// probes).</para>
/// </summary>
public class AstWalkerTraversalTests
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
        => new(Parent: null, ParameterPatterns: [], Opens: [], Properties: [], Output: output);

    /// <summary>One sample per <see cref="Expr"/> variant, with its expected child visits
    /// in order. Distinct sentinels detect a skipped child replaced by a duplicate visit.</summary>
    public static TheoryData<string, Expr, Expr[]> ExprSamples()
    {
        var leaf = new Expr.Num(1);
        var second = new Expr.Num(2);
        var third = new Expr.Num(3);
        // Name fallbacks are metadata-only in AstWalker; a host-built non-name
        // fallback is a real subtree and must reach VisitExpr.
        var fallback = new Expr.Num(4);
        return new TheoryData<string, Expr, Expr[]>
        {
            { nameof(Expr.Param), new Expr.Param("p"), [] },
            { nameof(Expr.Num), leaf, [] },
            { nameof(Expr.BoolLiteral), new Expr.BoolLiteral(true), [] },
            { nameof(Expr.StringLiteral), new Expr.StringLiteral("s"), [] },
            { nameof(Expr.Unary), new Expr.Unary(UnaryOp.Minus, leaf), [leaf] },
            { nameof(Expr.Binary), new Expr.Binary(BinaryOp.Add, leaf, second), [leaf, second] },
            // A chain visits its first operand and then every link operand in chain order.
            { nameof(Expr.Comparison), new Expr.Comparison(leaf, [new ComparisonLink(ComparisonOp.Lt, second), new ComparisonLink(ComparisonOp.Eq, third)]), [leaf, second, third] },
            { nameof(Expr.Index), new Expr.Index(leaf, second), [leaf, second] },
            { nameof(Expr.SequenceConstruct), new Expr.SequenceConstruct(leaf, second), [leaf, second] },
            { nameof(Expr.EmptySequence), new Expr.EmptySequence(0), [] },
            { nameof(Expr.SequenceSpread), new Expr.SequenceSpread(leaf), [leaf] },
            { nameof(Expr.ListLiteral), new Expr.ListLiteral([leaf, second]), [leaf, second] },
            { nameof(Expr.Resolve), new Expr.Resolve("R"), [] },
            { nameof(Expr.DotCall), new Expr.DotCall(leaf, "M", [second, third]) { LexicalFallback = fallback }, [leaf, fallback, second, third] },
            { nameof(Expr.Grace), new Expr.Grace(leaf, 1), [leaf] },
            { nameof(Expr.AlgorithmExpr), new Expr.AlgorithmExpr(EmptyAlgorithm(leaf, second)), [leaf, second] },
            { nameof(Expr.Capture), new Expr.Capture([leaf, second]), [leaf, second] },
            { nameof(Expr.Call), new Expr.Call(leaf, [second, third]), [leaf, second, third] },
            { nameof(Expr.NativeCall), new Expr.NativeCall("Abs", ["x"]), [] },
        };
    }

    [Theory]
    [MemberData(nameof(ExprSamples))]
    public void VisitExpr_ReachesEveryVariantAndItsChildren(string variantName, Expr sample, Expr[] expectedChildren)
    {
        var walker = new RecordingWalker();
        walker.VisitExpr(sample);

        Assert.Equal(expectedChildren.Length + 1, walker.Visited.Count);
        Assert.Same(sample, walker.Visited[0]);
        for (var i = 0; i < expectedChildren.Length; i++)
            Assert.Same(expectedChildren[i], walker.Visited[i + 1]);
        Assert.Equal(variantName, sample.GetType().Name);
    }

    /// <summary>
    /// The child-identity table above must keep one row per variant: the compiler proves
    /// nothing about a switch STATEMENT, so a new variant's walker arm — and its
    /// children — are pinned here or not at all.
    /// </summary>
    [Fact]
    public void ExprSamples_CoverEveryExprVariant()
        => ExprVariantCatalog.AssertCoversEveryVariant(
            ExprSamples().Select(row => (string)row[0]!),
            $"{nameof(AstWalkerTraversalTests)}.{nameof(ExprSamples)}");

    /// <summary>
    /// The real production walkers traverse a parsed program end to end: every variant
    /// the parser and front end can produce is walked without reaching the guard.
    /// </summary>
    [Fact]
    public void VisitExpr_WalksAParsedProgramEndToEnd()
    {
        var parsed = Parser.Parse("""
            open A
            A = {
                public X = 1, 2, 3
            }
            F(a) = -a + 1
            G(*items) = items.count
            H((x, y)) = [x, y]:0
            F(7), G(1, 2), H((3, 4)), 'text', (), A.X, X, if(true, 2, 3), Math.Abs(-1)
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
        var memberSpan = new SourceSpan(1, 4, 1, 5);
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
