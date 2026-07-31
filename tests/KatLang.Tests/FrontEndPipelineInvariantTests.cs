namespace KatLang.Tests;

/// <summary>
/// Regression coverage for the default elaborated front-end
/// (<see cref="FrontEndPipeline.Process(string)"/>, the no-download overload),
/// mirroring the invariants exercised by the Phase-3 frontend fuzzing campaign:
/// raw-diagnostic prefix preservation, determinism, input independence, public-wrapper
/// parity, and clean integration with the Phase-2 parser recursion budget.
/// </summary>
public class FrontEndPipelineInvariantTests
{
    private const string NestingMessage = "Nesting is too deep";

    private static (DiagnosticSeverity, string, string) Triple(Diagnostic d)
        => (d.Severity, d.Message, d.Span is { } s ? $"{s.StartLineNumber},{s.StartColumn},{s.EndLineNumber},{s.EndColumn}" : "-");

    private static List<(DiagnosticSeverity, string, string)> Triples(IEnumerable<Diagnostic> ds)
        => ds.Select(Triple).ToList();

    /// <summary>Ordered property names reachable by walking DOWN the AST (never the
    /// parent/back-reference). Captures synthetic deconstruction property names, whose
    /// determinism is the main non-determinism risk.</summary>
    private static List<string> PropertyNames(Algorithm root)
    {
        var names = new List<string>();
        Walk(root);
        return names;

        void Walk(Algorithm a)
        {
            foreach (var p in a.Properties) { names.Add(p.Name); Walk(p.Value); }
            foreach (var e in a.Output) WalkExpr(e);
            foreach (var b in a.Branches) Walk(b.Body);
        }

        void WalkExpr(Expr e)
        {
            switch (e)
            {
                case Expr.Unary(_, var o): WalkExpr(o); break;
                case Expr.Binary(_, var l, var r): WalkExpr(l); WalkExpr(r); break;
                case Expr.Index(var t, var s): WalkExpr(t); WalkExpr(s); break;
                case Expr.SequenceSpread(var o): WalkExpr(o); break;
                case Expr.Grace(var i, _): WalkExpr(i); break;
                case Expr.ListLiteral(var items): foreach (var it in items) WalkExpr(it); break;
                case Expr.Block(var alg): Walk(alg); break;
                case Expr.Call(var f, var args): WalkExpr(f); Walk(args); break;
                case Expr.DotCall dc: WalkExpr(dc.Target); if (dc.Args is { } ar) Walk(ar); break;
            }
        }
    }

    // ── Raw diagnostics are an unchanged prefix of frontend diagnostics ───────
    [Theory]
    [InlineData("(1")]              // unclosed paren
    [InlineData("1; 2")]            // unsupported semicolon
    [InlineData("@")]               // unexpected char
    [InlineData("f(x) = x + 1")]    // clean program (empty prefix trivially holds)
    [InlineData("open 'https://katlang.org/x'")]  // load-guard path
    public void RawSyntaxDiagnostics_ArePreservedPrefixOfFrontend(string source)
    {
        var syntax = Triples(Parser.ParseSyntax(source).Diagnostics);
        var frontend = Triples(FrontEndPipeline.Process(source).Diagnostics);

        Assert.True(frontend.Count >= syntax.Count);
        Assert.Equal(syntax, frontend.Take(syntax.Count).ToList());
    }

    // ── Determinism across two Process() calls on the same source ────────────
    [Theory]
    [InlineData("Area = w * h\nArea")]
    [InlineData("x, y, z = (1, 2, 3)\nx + y + z")]
    [InlineData("fib(0) = 0\nfib(1) = 1\nfib(n) = n")]
    [InlineData("a, *mid, z = (1, 2, 3, 4)")]
    public void Frontend_Process_IsDeterministic(string source)
    {
        var first = FrontEndPipeline.Process(source);
        var second = FrontEndPipeline.Process(source);

        Assert.Equal(Triples(first.Diagnostics), Triples(second.Diagnostics));
        Assert.Equal(PropertyNames(first.ElaboratedRoot), PropertyNames(second.ElaboratedRoot));
        Assert.Equal(first.CanEvaluateAfterLoadErrors, second.CanEvaluateAfterLoadErrors);
    }

    // ── Input independence: an unrelated program between two runs of the same ─
    //    source must not change the source's result (no leaked cross-parse state).
    [Fact]
    public void Deconstruction_SyntheticNames_AreInputIndependent()
    {
        const string a = "x, *y, z = (1, 2, 3, 4)\nx + z";
        const string b = "p, q = (9, 8)\nHelper(k) = k + p\nHelper(q)";

        var a1 = PropertyNames(FrontEndPipeline.Process(a).ElaboratedRoot);
        _ = FrontEndPipeline.Process(b);                 // unrelated work in between
        _ = FrontEndPipeline.Process(b);
        var a2 = PropertyNames(FrontEndPipeline.Process(a).ElaboratedRoot);

        Assert.Equal(a1, a2);
    }

    // ── Public wrapper parity: Parser.Parse == Process().ToParseResult() ──────
    [Theory]
    [InlineData("Area = w * h")]
    [InlineData("x, y = (1, 2)\nx")]
    [InlineData("g(0) = 1\ng(n) = n * 2")]
    [InlineData("(1")]
    public void PublicWrapper_Matches_Process(string source)
    {
        var viaWrapper = Parser.Parse(source);
        var viaPipeline = FrontEndPipeline.Process(source).ToParseResult();

        Assert.Equal(Triples(viaWrapper.Diagnostics), Triples(viaPipeline.Diagnostics));
        Assert.Equal(PropertyNames(viaWrapper.Root), PropertyNames(viaPipeline.Root));
    }

    // ── Parser recursion-budget integration (Phase-2 fix) ─────────────────────
    [Fact]
    public void OverBudgetNesting_FlowsThroughFrontend_WithoutCrashOrCascade()
    {
        var deep = string.Concat(Enumerable.Repeat("(", 600)) + "1" + string.Concat(Enumerable.Repeat(")", 600));

        // Raw parse: bounded, nesting diagnostic, no crash.
        var syntax = Parser.ParseSyntax(deep);
        Assert.Contains(syntax.Diagnostics, d => d.Message.Contains(NestingMessage, StringComparison.Ordinal));

        // FrontEndPipeline.Process: does not throw; preserves the nesting diagnostic;
        // no misleading secondary cascade (a placeholder root elaborates to nothing).
        var frontend = FrontEndPipeline.Process(deep);
        Assert.Contains(frontend.Diagnostics, d => d.Message.Contains(NestingMessage, StringComparison.Ordinal));
        Assert.True(frontend.Diagnostics.Count <= 3, $"unexpected diagnostic cascade: {frontend.Diagnostics.Count}");

        // Public wrapper stays consistent.
        var wrapper = Parser.Parse(deep);
        Assert.Equal(Triples(frontend.ToParseResult().Diagnostics), Triples(wrapper.Diagnostics));
    }
}
