namespace KatLang.Tests;

/// <summary>
/// Regression coverage mirroring the Phase-4 source-level evaluator invariants:
/// plain/counted outcome parity, public-engine parity, determinism, and result
/// structural validity. Uses the real evaluator entry points only.
/// </summary>
public class EvaluatorInvariantTests
{
    private static Expr Block(string source) => new Expr.Block(Parser.Parse(source).Root);

    private static EvalError Innermost(EvalError e)
    {
        while (e is EvalError.WithContext wc) e = wc.Inner;
        return e;
    }

    // ── Evaluator.Run and Evaluator.RunCounted agree ─────────────────────────
    [Theory]
    [InlineData("1 + 2")]
    [InlineData("(1, 2, 3)")]
    [InlineData("[1, 2, 3]")]
    [InlineData("()")]
    [InlineData("'text'")]
    [InlineData("F(x) = x * 2\nrange(1, 4).map(F)")]
    [InlineData("1 / 0")]                       // structured error
    [InlineData("missing")]            // structured error
    [InlineData("f(0) = 1\nf(n) = n\nf(9)")]
    public void PlainAndCounted_AgreeOnOutcomeAndValue(string source)
    {
        var block = Block(source);
        var plain = Evaluator.Run(block);
        var counted = Evaluator.RunCounted(block);

        Assert.Equal(plain.IsOk, counted.IsOk);
        if (plain.IsOk)
            Assert.True(Result.ValueComparer.Equals(plain.Value, counted.Value.Value));
        else
            Assert.Equal(Innermost(plain.Error).GetType(), Innermost(counted.Error).GetType());
    }

    // ── Public engine matches counted evaluation ─────────────────────────────
    [Theory]
    [InlineData("1 + 2")]
    [InlineData("(1, 2)")]
    [InlineData("[1, [2, 3]]")]
    [InlineData("range(1, 4).sum")]
    public void Engine_MatchesCountedEvaluation(string source)
    {
        var counted = Evaluator.RunCounted(Block(source));
        Assert.True(counted.IsOk);

        var engine = KatLangEngine.Run(source);
        var success = Assert.IsType<RunResult.Success>(engine);

        Assert.True(Result.ValueComparer.Equals(success.Value, counted.Value.Value));
        Assert.Equal(counted.Value.Value.ToHostAtoms(), success.Atoms);
    }

    // ── Determinism and input independence ───────────────────────────────────
    [Theory]
    [InlineData("A = 1 + 1\nA + A")]
    [InlineData("x, y = (1, 2)\nx + y")]
    [InlineData("F(x) = x + 1\nrange(1, 3).map(F)")]
    public void Evaluation_IsDeterministicAndInputIndependent(string source)
    {
        string First() => KatLangEngine.Run(source).ToDisplayString();

        var a1 = First();
        _ = KatLangEngine.Run("B = (C = 5)\nD(x) = x + 1\nD(B.C)");   // unrelated work
        var a2 = First();

        Assert.Equal(a1, a2);
    }

    // ── Result structural validity ───────────────────────────────────────────
    [Theory]
    [InlineData("(1, 2, 3)")]
    [InlineData("((1, 2), (3, 4))")]
    [InlineData("[1, [2], 3]")]
    [InlineData("[7]")]
    [InlineData("range(1, 5)")]
    public void SuccessfulResults_HaveNoSingletonSequenceAndNoNullChildren(string source)
    {
        var counted = Evaluator.RunCounted(Block(source));
        Assert.True(counted.IsOk);
        Assert.True(counted.Value.EmittedCount >= 0);
        Walk(counted.Value.Value);

        static void Walk(Result r)
        {
            switch (r)
            {
                case Result.SequenceValue sv:
                    // Singleton sequence structure is canonicalized away ([x] => x).
                    Assert.NotEqual(1, sv.Items.Count);
                    foreach (var it in sv.Items) { Assert.NotNull(it); Walk(it); }
                    break;
                case Result.ListValue lv:      // exact singleton lists ARE legal
                    foreach (var it in lv.Items) { Assert.NotNull(it); Walk(it); }
                    break;
            }
        }
    }

    // ── Modest finite recursion still evaluates (resource-probe characterization) ──
    [Fact]
    public void ModestFiniteRecursion_Evaluates()
    {
        var engine = KatLangEngine.Run("f(0) = 0\nf(n) = f(n - 1)\nf(100)");
        Assert.IsType<RunResult.Success>(engine);
    }
}
