using System.Globalization;
using KatLang.Tests.AsyncEvaluation;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// Independent read-back oracle: fully grouped input templates and the real syntax
/// parser establish the expected tree. No renderer precedence helper is used here.
/// Calls and opaque blocks intentionally elide their contents in diagnostic names;
/// only those interiors are masked, never their surrounding operator structure.
/// </summary>
public class SourceLikeDiagnosticRenderingTests(ITestOutputHelper output)
{
    private static readonly string[] Operators =
        ["+", "-", "*", "/", "div", "mod", "^", "and", "xor", "or"];
    private static readonly string[] Comparisons = ["<", ">", "<=", ">=", "==", "!="];

    [Fact]
    public void BoundedTrees_ReadBackInEverySourcePosition()
    {
        var sources = new HashSet<string>(StringComparer.Ordinal)
        {
            "a", "0", "true", "'text'", "()", "(a, b)", "[a, b]", "[a]",
            "f(a, b)", "a.f", "a.f(b)", "a:0", "a:(b:0)", "a:(b.f)",
            "~a", "a~", "~~a", "a~~", "~a~", "a.~~f", "-a", "not a", "-a ^ b", "(-a) ^ b",
            "a ^ -b", "-(a ^ b)", "not a < b", "not (a and b)", "{ P = 1 }",
            "(a < b) < c", "a < (b < c)", "a < b < c", "a < b == c", "a == b != c",
            "(a*)", "(a*, b)", "[a*, b]", "(a.f(b)):0", "(a:0).f(b)", "(~a)(b)",
            "(a.f)(b)", "(a.f(b))(c)", "(a.f)(b).g", "((a.f)(b)):0"
        };
        foreach (var outer in Operators)
        {
            foreach (var inner in Operators)
            {
                sources.Add($"(a {inner} b) {outer} c");
                sources.Add($"a {outer} (b {inner} c)");
            }
            foreach (var unary in new[] { "-", "not " })
            {
                sources.Add($"{unary}(a {outer} b)");
                sources.Add($"({unary}a) {outer} b");
                sources.Add($"a {outer} ({unary}b)");
            }
        }
        foreach (var outer in Comparisons)
        foreach (var inner in Comparisons)
        {
            sources.Add($"(a {inner} b) {outer} c");
            sources.Add($"a {outer} (b {inner} c)");
            sources.Add($"a {outer} b {inner} c");
        }
        foreach (var comparison in Comparisons)
        {
            foreach (var binary in Operators)
            {
                sources.Add($"(a {binary} b) {comparison} c");
                sources.Add($"a {comparison} (b {binary} c)");
                sources.Add($"(a {comparison} b) {binary} c");
                sources.Add($"a {binary} (b {comparison} c)");
            }
            foreach (var unary in new[] { "-", "not " })
            {
                sources.Add($"{unary}(a {comparison} b)");
                sources.Add($"({unary}a) {comparison} b");
                sources.Add($"a {comparison} ({unary}b)");
            }
        }
        // Bounded depth-three compositions, including selectors (primary-only in
        // the parser), not just the more permissive target positions.
        foreach (var child in new[] { "-a", "not a", "a + b", "a < b", "a.f(b)", "a:0", "(a, b)", "[a]" })
        foreach (var inner in new Func<string, string>[]
        {
            s => $"({s}).f", s => $"({s}):0", s => $"a:({s})",
            s => $"({s}, b)", s => $"[{s}]"
        })
        {
            var nested = inner(child);
            sources.Add(nested);
            sources.Add($"({nested}).m");
            sources.Add($"({nested}):0");
        }

        var checks = 0;
        var failures = new List<string>();
        foreach (var source in sources.Order(StringComparer.Ordinal))
        {
            var expected = Raw(source);
            foreach (var mode in Enum.GetValues<ExprNameMode>())
            {
                var fragment = ExprNameRenderer.Render(expected, mode);
                var rendered = mode switch
                {
                    ExprNameMode.UnaryOperand => "-" + fragment,
                    ExprNameMode.SpreadOperand => fragment + "*",
                    ExprNameMode.IndexTarget => fragment + ":0",
                    ExprNameMode.IndexSelector => "z:" + fragment,
                    _ => fragment
                };
                Expr expectedParent = mode switch
                {
                    ExprNameMode.UnaryOperand => new Expr.Unary(UnaryOp.Minus, expected),
                    ExprNameMode.SpreadOperand => new Expr.SequenceSpread(expected),
                    ExprNameMode.IndexTarget => new Expr.Index(expected, new Expr.Num(0)),
                    ExprNameMode.IndexSelector => new Expr.Index(new Expr.Resolve("z"), expected),
                    _ => expected
                };
                Check(source, mode.ToString(), expectedParent, rendered);
            }
            Check(source, "dot fragment", new Expr.DotCall(expected, "m", null),
                ExprNameRenderer.RenderDotReceiver(expected) + ".m");
        }
        output.WriteLine($"{sources.Count} source trees, {checks} read-backs, {failures.Count} mismatches.");
        Assert.True(failures.Count == 0, string.Join("\n", failures.Take(30)));

        void Check(string source, string mode, Expr expected, string rendered)
        {
            checks++;
            // (...) is an explicit elision, not executable source. Substitute a
            // marker only in that exact placeholder and ignore call interiors.
            var parsed = Parser.ParseSyntax(rendered.Replace("(...)", "(Elided)").Replace("{...}", "{ Elided = 1 }"));
            if (parsed.Diagnostics.Count != 0 || parsed.Root.Output.Count != 1
                || Shape(expected) != Shape(parsed.Root.Output[0]))
                failures.Add($"{mode}: {source} -> {rendered}; expected {Shape(expected)}; got "
                    + (parsed.Diagnostics.Count == 0 ? string.Join(";", parsed.Root.Output.Select(Shape))
                        : string.Join(";", parsed.Diagnostics.Select(d => d.Message))));
        }
    }

    [Theory]
    [InlineData("~~x", "~~x*")]
    [InlineData("x~~", "x~~*")]
    [InlineData("~x~", "~x~*")]
    [InlineData("x.~~f", "x.~~f*")]
    [InlineData("(x.f)(a)", "(x.f)(...)*")]
    public void ParserSpreadRepair_PreservesTheAnnotatedOperand(string operand, string repair)
    {
        var parsed = Parser.ParseSyntax(operand + " *");
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidSpreadMarker, diagnostic.Code);
        Assert.Contains($"write `{repair}`", diagnostic.Message, StringComparison.Ordinal);
        var spread = Assert.IsType<Expr.SequenceSpread>(Raw(repair.Replace("(...)", "(Elided)")));
        Assert.Equal(Shape(Raw(operand)), Shape(spread.Operand));
    }

    [Theory]
    [InlineData(int.MinValue)]
    [InlineData(int.MaxValue)]
    public void HostGraceWeights_RemainOutputBounded(int weight)
    {
        var rendered = ExprNameRenderer.Render(new Expr.Grace(new Expr.Resolve("x"), weight), ExprNameMode.Open);
        Assert.Equal(ExprNameRenderer.MaxRenderedNameLength + ExprNameRenderer.TruncationMarker.Length, rendered.Length);
        Assert.EndsWith(ExprNameRenderer.TruncationMarker, rendered, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("a*")]
    [InlineData("a**")]
    [InlineData("(-a)*")]
    [InlineData("(not a)*")]
    [InlineData("(a + b)*")]
    [InlineData("a*.f")]
    [InlineData("(a:0)*")]
    [InlineData("(a.f(b))*")]
    public void SpreadSlots_ReadBack(string source)
    {
        var original = Raw(source);
        foreach (var mode in new[] { ExprNameMode.Open, ExprNameMode.DiagnosticName })
            Assert.Equal(Shape(original), Shape(Raw(ExprNameRenderer.Render(original, mode).Replace("(...)", "(Elided)"))));
    }

    [Theory]
    [InlineData("f = { X = 1 }\n(-2).f", KatLangErrorCode.MissingOutput, "`(-2).f`")]
    [InlineData("f = { X = 1 }\n(not true).f", KatLangErrorCode.MissingOutput, "`(not true).f`")]
    [InlineData("a = 1\nb = 2\nmissing = { X = 1 }\n(a + b).missing", KatLangErrorCode.MissingOutput, "`(a + b).missing`")]
    [InlineData("a = 1\nb = 2\nmissing = { X = 1 }\n(a < b).missing", KatLangErrorCode.MissingOutput, "`(a < b).missing`")]
    [InlineData("a = 2\n(-a):true", KatLangErrorCode.TypeMismatch, "Expected a number")]
    [InlineData("a = true\n(not a):true", KatLangErrorCode.TypeMismatch, "Expected a number")]
    [InlineData("Obj = { F = 1 }\n(Obj.F)() + true", KatLangErrorCode.TypeMismatch, "(Obj.F)(...) + true")]
    [InlineData("a = 2\n(-a):0 + true", KatLangErrorCode.TypeMismatch, "(-a):0 + true")]
    [InlineData("a = true\n(not a):0 + 1", KatLangErrorCode.TypeMismatch, "(not a):0 + 1")]
    public async Task PublicErrors_AndSuspendedTwins_PreserveExpressionText(
        string source, KatLangErrorCode code, string text)
    {
        // A leading property forces a deterministic suspension before the error.
        source = "Gate = 0\nGate\n" + source;
        var root = SourceProvenance.ParseValid(source).Root;
        var publicError = Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)).Errors);
        Assert.Equal(code, publicError.Code);
        Assert.Contains(text, publicError.Message, StringComparison.Ordinal);
        var expr = new Expr.AlgorithmExpr(root);
        var sync = Evaluator.Run(expr);
        Assert.True(sync.IsError);
        var cache = new HoldingAsyncZeroArgPropertyResultCache(1);
        var pending = Evaluator.RunAsync(expr, cache).AsTask();
        await cache.Reached.WaitAsync(TimeSpan.FromSeconds(10));
        try { Assert.False(pending.IsCompleted); }
        finally { cache.Release(); }
        var asynchronous = await pending.WaitAsync(TimeSpan.FromSeconds(10));
        Assert.True(asynchronous.IsError);
        var syncError = KatLangError.FromEvalError(sync.Error);
        var asyncError = KatLangError.FromEvalError(asynchronous.Error);
        Assert.Equal((syncError.Code, syncError.Message, syncError.Span),
            (asyncError.Code, asyncError.Message, asyncError.Span));
        Assert.Equal(publicError.Message, syncError.Message);
        output.WriteLine(publicError.Message);
    }

    private static Expr Raw(string source)
    {
        var parsed = Parser.ParseSyntax(source);
        Assert.True(parsed.Diagnostics.Count == 0,
            source + ": " + string.Join(";", parsed.Diagnostics.Select(d => d.Message)));
        return Assert.Single(parsed.Root.Output);
    }

    private static string Shape(Expr expr) => expr switch
    {
        Expr.Resolve r => $"name({r.Name})",
        Expr.Num n => $"num({n.Value.ToString(CultureInfo.InvariantCulture)})",
        Expr.BoolLiteral b => $"bool({b.Value})",
        Expr.StringLiteral s => $"string({s.Value})",
        Expr.EmptySequence e => $"empty({e.Depth})",
        Expr.Unary u => $"{u.Op}({Shape(u.Operand)})",
        Expr.Binary b => $"{b.Op}({Shape(b.Left)},{Shape(b.Right)})",
        Expr.Comparison c => $"chain({Shape(c.First)};{string.Join(';', c.Links.Select(l => $"{l.Op}:{Shape(l.Operand)}"))})",
        Expr.Index i => $"index({Shape(i.Target)},{Shape(i.Selector)})",
        Expr.DotCall d => $"dot({Shape(d.Target)},{d.Name},{(d.Args is null ? "property" : "args")},{(d.LexicalFallback is Expr.Grace g ? Shape(g) : "plain")})",
        Expr.Call c => $"call({Shape(c.Function)},args)",
        Expr.Capture c => $"capture({string.Join(';', c.Body.Select(Shape))})",
        Expr.ListLiteral l => $"list({string.Join(';', l.Items.Select(Shape))})",
        Expr.SequenceSpread s => $"spread({Shape(s.Operand)})",
        Expr.Grace g => $"grace({g.Weight},{Shape(g.Inner)})",
        Expr.AlgorithmExpr => "opaque block",
        _ => throw new InvalidOperationException($"Unclassified round-trip node {expr.GetType().Name}")
    };
}
