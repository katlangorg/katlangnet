namespace KatLang.Tests;

/// <summary>
/// Source spans are semantic-editor metadata carried through both front-end
/// rewriting passes. These tests compare the input and output of each pass,
/// rather than merely checking that the final node has some non-null span.
/// </summary>
public class FrontEndSpanPreservationTests
{
    [Fact]
    public void ParameterDetection_PreservesCompositeSpansAcrossImplicitRewriting()
    {
        const string source = "K = [-x, x:0, x + 1, x*, (x, 1), {x}, H(x)]\nK";
        var syntax = Parser.ParseSyntax(source);
        Assert.False(syntax.HasErrors);

        var (detected, diagnostics) = ParameterDetector.Detect(syntax.Root);
        Assert.Empty(diagnostics);

        AssertCompositeSpansEqual(syntax.Root, detected);
    }

    [Fact]
    public void ParameterDetection_PreservesCompositeSpansAcrossBinderRewriting()
    {
        const string source = "F(1, x) = [-x, x*, (x, 1), {x}]";
        var syntax = Parser.ParseSyntax(source);
        Assert.False(syntax.HasErrors);

        var (detected, diagnostics) = ParameterDetector.Detect(syntax.Root);
        Assert.Empty(diagnostics);

        AssertCompositeSpansEqual(syntax.Root, detected);
    }

    [Fact]
    public void ParameterDetection_PreservesHostSequenceConstructSpan()
    {
        var joinSpan = new SourceSpan(4, 2, 4, 12);
        var join = new Expr.SequenceConstruct(
            new Expr.Resolve("x") { Span = new SourceSpan(4, 2, 4, 2) },
            new Expr.Num(1) { Span = new SourceSpan(4, 12, 4, 12) })
        {
            Span = joinSpan,
        };
        var root = User(output: OutputBundle.From([join]));

        var (detected, diagnostics) = ParameterDetector.Detect(root);

        Assert.Empty(diagnostics);
        Assert.Equal(joinSpan, Assert.IsType<Expr.SequenceConstruct>(Assert.Single(detected.Output)).Span);
    }

    [Fact]
    public void ParameterDetection_PreservesCompositeSpansInHostOpenTarget()
    {
        var root = User(
            opens: [HostCompositeTree()],
            output: OutputBundle.From([new Expr.Num(0)]));

        var (detected, diagnostics) = ParameterDetector.Detect(root);

        Assert.Empty(diagnostics);
        AssertCompositeSpansEqual(root.Opens, detected.Opens);
    }

    [Fact]
    public void ImplicitResolution_PreservesCompositeSpansInNeutralArgumentBundle()
    {
        var call = new Expr.Call(
            new Expr.Resolve("Unknown") { Span = new SourceSpan(8, 1, 8, 7) },
            OutputBundle.From([HostCompositeTree()]))
        {
            Span = new SourceSpan(8, 1, 8, 40),
        };
        var root = User(output: OutputBundle.From([call]));

        var resolved = ImplicitArgumentResolver.Resolve(root);

        AssertCompositeSpansEqual(root, resolved);
    }

    [Fact]
    public void ImplicitResolution_PreservesCompositeSpansInHostOpenTarget()
    {
        var root = User(
            opens: [HostCompositeTree()],
            output: OutputBundle.From([new Expr.Num(0)]));

        var resolved = ImplicitArgumentResolver.Resolve(root);

        AssertCompositeSpansEqual(root.Opens, resolved.Opens);
    }

    [Fact]
    public void ImplicitResolution_SynthesizedCallKeepsTheReferencedOccurrenceSpan()
    {
        const string source = "F = a\nG = -F";
        var syntax = Parser.ParseSyntax(source);
        Assert.False(syntax.HasErrors);
        var (detected, diagnostics) = ParameterDetector.Detect(syntax.Root);
        Assert.Empty(diagnostics);

        var beforeG = detected.Properties.Single(property => property.Name == "G").Value;
        var beforeUnary = Assert.IsType<Expr.Unary>(Assert.Single(beforeG.Output));
        var beforeReference = Assert.IsType<Expr.Resolve>(beforeUnary.Operand);

        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected);
        var afterG = resolved.Properties.Single(property => property.Name == "G").Value;
        var afterUnary = Assert.IsType<Expr.Unary>(Assert.Single(afterG.Output));
        var call = Assert.IsType<Expr.Call>(afterUnary.Operand);

        Assert.Equal(beforeUnary.Span, afterUnary.Span);
        Assert.Equal(beforeReference.Span, call.Span);
        Assert.Equal(beforeReference.Span, call.Function.Span);
    }

    private static Algorithm.User User(
        IReadOnlyList<Expr>? opens = null,
        OutputBundle? output = null)
        => new(
            Parent: null,
            Parameters: [],
            Opens: opens ?? [],
            Properties: [],
            Output: output ?? OutputBundle.Empty);

    private static Expr HostCompositeTree()
    {
        var nested = User(output: OutputBundle.From([
            new Expr.Resolve("nested") { Span = new SourceSpan(7, 30, 7, 35) }]));
        return new Expr.ListLiteral(OutputBundle.From([
            new Expr.Unary(
                UnaryOp.Minus,
                new Expr.Resolve("x") { Span = new SourceSpan(7, 3, 7, 3) })
            {
                Span = new SourceSpan(7, 2, 7, 3),
            },
            new Expr.SequenceSpread(
                new Expr.Resolve("y") { Span = new SourceSpan(7, 7, 7, 7) })
            {
                Span = new SourceSpan(7, 7, 7, 8),
                SpreadMarkerSpan = new SourceSpan(7, 8, 7, 8),
            },
            new Expr.Capture(OutputBundle.From([
                new Expr.Resolve("z") { Span = new SourceSpan(7, 12, 7, 12) },
                new Expr.Num(1) { Span = new SourceSpan(7, 15, 7, 15) }]))
            {
                Span = new SourceSpan(7, 11, 7, 16),
            },
            new Expr.AlgorithmExpr(nested)
            {
                Span = new SourceSpan(7, 20, 7, 36),
            }]))
        {
            Span = new SourceSpan(7, 1, 7, 37),
        };
    }

    private static void AssertCompositeSpansEqual(Algorithm before, Algorithm after)
        => AssertCompositeSpansEqual(CompositeNodes(before), CompositeNodes(after));

    private static void AssertCompositeSpansEqual(
        IReadOnlyList<Expr> before,
        IReadOnlyList<Expr> after)
        => AssertCompositeSpansEqual(
            before.SelectMany(CompositeNodes),
            after.SelectMany(CompositeNodes));

    private static void AssertCompositeSpansEqual(
        IEnumerable<Expr> before,
        IEnumerable<Expr> after)
    {
        var expected = before.Select(expr => (expr.GetType(), expr.Span)).ToArray();
        var actual = after.Select(expr => (expr.GetType(), expr.Span)).ToArray();
        Assert.Equal(expected, actual);
    }

    private static IEnumerable<Expr> CompositeNodes(Algorithm algorithm)
    {
        foreach (var expr in algorithm.Opens)
            foreach (var nested in CompositeNodes(expr))
                yield return nested;
        foreach (var property in algorithm.Properties)
            foreach (var nested in CompositeNodes(property.Value))
                yield return nested;
        foreach (var expr in algorithm.Output)
            foreach (var nested in CompositeNodes(expr))
                yield return nested;
        foreach (var branch in algorithm.Branches)
            foreach (var nested in CompositeNodes(branch.Body))
                yield return nested;
    }

    private static IEnumerable<Expr> CompositeNodes(Expr expr)
    {
        switch (expr)
        {
            case Expr.Unary(_, var operand):
                yield return expr;
                foreach (var nested in CompositeNodes(operand)) yield return nested;
                break;
            case Expr.Binary(_, var left, var right):
                yield return expr;
                foreach (var nested in CompositeNodes(left)) yield return nested;
                foreach (var nested in CompositeNodes(right)) yield return nested;
                break;
            case Expr.Index(var target, var selector):
                yield return expr;
                foreach (var nested in CompositeNodes(target)) yield return nested;
                foreach (var nested in CompositeNodes(selector)) yield return nested;
                break;
            case Expr.SequenceConstruct(var left, var right):
                yield return expr;
                foreach (var nested in CompositeNodes(left)) yield return nested;
                foreach (var nested in CompositeNodes(right)) yield return nested;
                break;
            case Expr.SequenceSpread(var operand):
                yield return expr;
                foreach (var nested in CompositeNodes(operand)) yield return nested;
                break;
            case Expr.ListLiteral(var items):
                yield return expr;
                foreach (var item in items)
                    foreach (var nested in CompositeNodes(item)) yield return nested;
                break;
            case Expr.AlgorithmExpr(var nestedAlgorithm):
                yield return expr;
                foreach (var nested in CompositeNodes(nestedAlgorithm)) yield return nested;
                break;
            case Expr.Capture(var body):
                yield return expr;
                foreach (var item in body)
                    foreach (var nested in CompositeNodes(item)) yield return nested;
                break;
            case Expr.Call(var function, var args):
                yield return expr;
                foreach (var nested in CompositeNodes(function)) yield return nested;
                foreach (var item in args)
                    foreach (var nested in CompositeNodes(item)) yield return nested;
                break;
            case Expr.DotCall(var target, _, var args):
                yield return expr;
                foreach (var nested in CompositeNodes(target)) yield return nested;
                if (args is not null)
                {
                    foreach (var item in args)
                        foreach (var nested in CompositeNodes(item)) yield return nested;
                }
                break;
        }
    }
}
