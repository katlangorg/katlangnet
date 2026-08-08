namespace KatLang.Tests;

/// <summary>
/// Open-ownership contract for conditional clause families, plus the deterministic
/// work-growth regression it fixes.
///
/// Contract: opens written in a clause body are BRANCH-OWNED — they stay on
/// <c>Conditional.Branches[i].Body.Opens</c> and the family is built with
/// <c>Conditional.Opens = []</c>. Previously clause 0's opens were also copied onto the
/// conditional, so the same source subtree was reachable by two paths; frontend rebuild
/// passes then unfolded a linear reference DAG into an exponential tree.
/// </summary>
public class ClauseFamilyOpenOwnershipTests
{
    private const string Library = "Library = {\n    public Value = 7\n}\n";

    /// <summary>Case(N): the pathological family — a literal clause head whose body is an
    /// unclosed parenthesis containing `open`.</summary>
    private static string Case(int n) => string.Concat(Enumerable.Repeat("M(-2, 2) = (open(o\n", n));

    private static int TreeNodes(Algorithm root)
    {
        int n = 0;
        Alg(root);
        return n;

        void Alg(Algorithm a)
        {
            if (++n > 20_000_000) return;
            foreach (var p in a.Properties) { n++; Alg(p.Value); }
            foreach (var e in a.Opens) Ex(e);
            foreach (var e in a.Output) Ex(e);
            foreach (var b in a.Branches) { n++; Alg(b.Body); }
        }

        void Ex(Expr e)
        {
            if (++n > 20_000_000) return;
            switch (e)
            {
                case Expr.Unary(_, var o): Ex(o); break;
                case Expr.Binary(_, var l, var r): Ex(l); Ex(r); break;
                case Expr.Index(var t, var s): Ex(t); Ex(s); break;
                case Expr.SequenceSpread(var o): Ex(o); break;
                case Expr.Grace(var i, _): Ex(i); break;
                case Expr.ListLiteral(var items): foreach (var it in items) Ex(it); break;
                case Expr.Block(var alg): Alg(alg); break;
                case Expr.Call(var fn, var args): Ex(fn); Alg(args); break;
                case Expr.DotCall dc: Ex(dc.Target); if (dc.Args is { } a2) Alg(a2); break;
            }
        }
    }

    // ── Ownership contract ───────────────────────────────────────────────────
    [Fact]
    public void ClauseFamily_Opens_AreBranchOwned_NotDuplicatedOntoConditional()
    {
        var body = new Algorithm.User(null, [], [new Expr.Resolve("Library")], [], [new Expr.Resolve("Value")]);
        var family = Algorithm.ElaborateClauseGroup([new CondBranch(new Pattern.LitInt(0), body)]);

        var conditional = Assert.IsType<Algorithm.Conditional>(family);
        Assert.Empty(conditional.Opens);                                   // no duplicate copy
        Assert.Single(conditional.Branches);
        Assert.Single(conditional.Branches[0].Body.Opens);                 // branch keeps ownership
    }

    // ── Valid-program semantics preserved ────────────────────────────────────
    // Under the delimiter model, a clause body that owns an open is written as
    // a brace block (`{ ... }` is the scoped algorithm form); parentheses no
    // longer carry declarations.
    [Fact]
    public void SingleLiteralClause_OpenStillResolves()
    {
        var result = KatLangEngine.Run(Library + "F(0) = {\n    open Library\n    Value\n}\nF(0)\n");
        Assert.Equal("7", Assert.IsType<RunResult.Success>(result).ToDisplayString());
    }

    [Fact]
    public void CaptureClause_OrdinaryAlgorithm_OpenStillResolves()
    {
        var result = KatLangEngine.Run(Library + "F(x) = {\n    open Library\n    Value\n}\nF(0)\n");
        Assert.Equal("7", Assert.IsType<RunResult.Success>(result).ToDisplayString());
    }

    [Theory]
    // The substantive invariant: clause-family branches OWN their opens
    // (Conditional.Opens stays empty; each branch body carries its own), so an
    // open-provided name resolves inside the branch body instead of becoming a
    // phantom clause parameter that would mismatch the family.
    [InlineData("F(0) = {\n    open Library\n    Value\n}\nF(y) = {\n    open Library\n    Value + y\n}\nF(0)\n", "7")]
    [InlineData("F(0) = (\n    1\n)\nF(y) = {\n    open Library\n    Value + y\n}\nF(1)\n", "8")]
    [InlineData("F(0) = {\n    open Library\n    Value\n}\nF(y) = {\n    open Library\n    Value + y\n}\nF(3)\n", "10")]
    public void MultiClauseFamily_OpenProvidedName_ResolvesThroughBranchOwnedOpens(string tail, string expected)
    {
        var result = KatLangEngine.Run(Library + tail);
        Assert.Equal(expected, Assert.IsType<RunResult.Success>(result).ToDisplayString());
    }

    [Theory]
    // The former parenthesized spellings of the same programs are now parser
    // rejections: `open` is an algorithm-level declaration and `( ... )` is
    // sequence/grouping syntax only.
    [InlineData("F(0) = (\n    open Library\n    Value\n)\nF(0)\n")]
    [InlineData("F(x) = (\n    open Library\n    Value\n)\nF(0)\n")]
    [InlineData("F(0) = (\n    open Library\n    Value\n)\nF(y) = (\n    open Library\n    Value + y\n)\nF(0)\n")]
    public void ClauseBodyOpenInParentheses_IsRejectedByTheParser(string tail)
    {
        var result = KatLangEngine.Run(Library + tail);
        var failure = Assert.IsType<RunResult.ParseFailure>(result);
        Assert.Contains(failure.Errors, e => e.Message.Contains(
            "An 'open' declaration is not allowed inside parentheses"));
    }

    // ── Deterministic work-growth regression (no wall-clock assertions) ──────
    [Theory]
    [InlineData(4)]
    [InlineData(10)]
    [InlineData(20)]
    [InlineData(40)]
    public void PathologicalFamily_ElaboratesWithLinearNodeCount(int n)
    {
        var root = Parser.Parse(Case(n)).Root;
        // Was 2^N (N=14 => 163,831). A generous linear bound catches any regression.
        Assert.True(TreeNodes(root) <= 40 * n + 200, $"Case({n}) elaborated to {TreeNodes(root)} nodes.");
    }

    [Fact]
    public void PathologicalFamily_GrowthIsNotExponential()
    {
        int a = TreeNodes(Parser.Parse(Case(10)).Root);
        int b = TreeNodes(Parser.Parse(Case(20)).Root);
        // The lower bound proves the measurement follows the supplied family size instead
        // of passing vacuously on a constant/empty recovery tree; the upper bound excludes
        // the former ~2^10 amplification when N doubles.
        Assert.True(b * 2 >= 3 * a, $"Case(10)={a}, Case(20)={b} — growth is not input-sensitive.");
        Assert.True(b < 4 * a, $"Case(10)={a}, Case(20)={b} — growth looks combinatorial.");
    }

    /// <summary>Generous smoke bound: Case(20) took ~139 s before the fix and ~5 ms after.
    /// The threshold has large CI margin and is not a microbenchmark.</summary>
    [Fact]
    public void PathologicalFamily_Case20_CompletesQuickly()
    {
        var sw = System.Diagnostics.Stopwatch.StartNew();
        _ = Parser.Parse(Case(20));
        sw.Stop();
        Assert.True(sw.Elapsed.TotalSeconds < 10, $"Case(20) took {sw.Elapsed.TotalSeconds:F1}s.");
    }

    // ── Malformed recovery stays bounded and well-formed ─────────────────────
    [Theory]
    [InlineData("M(-2, 2) = (open(o\nM(-2, 2) = (open(o\n")]        // literal + unclosed + open
    [InlineData("M(-2, 2) = ((o\nM(-2, 2) = ((o\n")]                // no open
    [InlineData("M(x, y) = (open(o\nM(x, y) = (open(o\n")]          // capture head
    [InlineData("M(-2, 2) = (open(o))\n")]                          // closed
    [InlineData("A(-2, 2) = (open(o\nB(-2, 2) = (open(o\n")]        // different names
    [InlineData("M(-2, 2) = (open(o\nZ = 1\nZ\n")]         // followed by valid declarations
    public void MalformedRecovery_IsBoundedAndProducesNoSequenceConstruct(string source)
    {
        var result = Parser.Parse(source);
        Assert.True(TreeNodes(result.Root) < 5000);
        Assert.All(result.Diagnostics, d =>
        {
            Assert.NotNull(d.Span);
            Assert.True(d.Span!.StartLineNumber >= 1 && d.Span.StartColumn >= 1);
        });
        Assert.False(ContainsSequenceConstruct(result.Root));
    }

    private static bool ContainsSequenceConstruct(Algorithm root)
    {
        var d = new Detector();
        d.VisitAlgorithm(root);
        return d.Found;
    }

    private sealed class Detector : AstWalker
    {
        public bool Found { get; private set; }
        public override void VisitExpr(Expr expr)
        {
            if (expr is Expr.SequenceConstruct) Found = true;
            base.VisitExpr(expr);
        }
    }
}
