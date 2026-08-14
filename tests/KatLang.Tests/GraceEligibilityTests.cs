namespace KatLang.Tests;

/// <summary>
/// The written-Grace eligibility law: `~` decorates exactly ONE bare
/// parameter/name occurrence — `~x` (one position earlier) and `x~` (one
/// position later) are the only supported operand shapes. Grace is NOT an
/// expression operator: attaching it to a group, call, dot result, list,
/// literal, or any other compound expression is a parse error, and no
/// ordering semantics are ever assigned to a multi-name operand. The
/// `recv~.t` applies that SAME postfix law to the receiver occurrence, while
/// `recv.~t` applies the SAME prefix law to the member/fallback occurrence;
/// their composition with DotCall is pinned in
/// <see cref="GraceDotCompositionTests"/>.
/// </summary>
public class GraceEligibilityTests
{
    private const string GraceLawFragment =
        "Grace `~` can only be applied to a parameter or name occurrence";

    private static void AssertGraceRejected(string source)
    {
        var parse = Parser.Parse(source);
        Assert.True(parse.HasErrors, $"Expected the Grace-eligibility diagnostic but the source parsed cleanly:{Environment.NewLine}{source}");
        Assert.Contains(
            parse.Diagnostics,
            diagnostic => diagnostic.Message.Contains(GraceLawFragment, StringComparison.Ordinal));
    }

    private static Result Evaluate(string source)
    {
        var provenance = SourceProvenance.ParseValid(source);
        var expr = new Expr.AlgorithmExpr(provenance.Root);

        var plain = Evaluator.Run(expr);
        Assert.False(plain.IsError, $"Expected success but got error: {(plain.IsError ? plain.Error : null)}");

        var counted = Evaluator.RunCounted(expr);
        Assert.False(counted.IsError, $"Expected counted success but got error: {(counted.IsError ? counted.Error : null)}");

        Assert.True(
            Result.ValueComparer.Equals(plain.Value, counted.Value.Value),
            $"Plain/counted divergence: {plain.Value} vs {counted.Value.Value}");
        return plain.Value;
    }

    private static void AssertAtom(string source, decimal expected)
    {
        var actual = Assert.IsType<Result.Atom>(Evaluate(source));
        Assert.Equal(expected, actual.Value);
    }

    // ── Valid: the two supported bare-name forms ────────────────────────────

    [Fact]
    public void PrefixGrace_OnBareName_MovesItOneEarlier()
    {
        // The canonical tutorial example: ~x moves x before y.
        var root = SourceProvenance.ParseValid("Divide = y / ~x\nDivide(2, 10)").Root;
        Assert.Equal(["x", "y"], Assert.IsType<Algorithm.User>(root.Properties[0].Value).Params);
        AssertAtom("Divide = y / ~x\nDivide(2, 10)", 5m);
    }

    [Fact]
    public void PostfixGrace_OnBareName_MovesItOneLater()
    {
        var root = SourceProvenance.ParseValid("K = t(a~, b)\nK(1, 2, {x + y})").Root;
        Assert.Equal(["t", "b", "a"], Assert.IsType<Algorithm.User>(root.Properties[0].Value).Params);
    }

    [Fact]
    public void GraceOnCalleeName_ThenCall_StaysTheEstablishedIdiom()
    {
        // `t~(a)` and `~f(x)`: the grace operand is the bare callee NAME; the
        // call applies to the graced name, so the one-name law is satisfied.
        var postfix = SourceProvenance.ParseValid("K = t~(a)\nK(7, {a+1})").Root;
        Assert.Equal(["a", "t"], Assert.IsType<Algorithm.User>(postfix.Properties[0].Value).Params);
        AssertAtom("K = t~(a)\nK(7, {a+1})", 8m);

        // Prefix on the first-collected name is an at-boundary no-op: the
        // grace still decorates only `f`.
        var prefix = SourceProvenance.ParseValid("K = ~f(x)\nK({a}, 1)").Root;
        Assert.Equal(["f", "x"], Assert.IsType<Algorithm.User>(prefix.Properties[0].Value).Params);
    }

    [Fact]
    public void GraceOnBareName_ThenOrdinaryDot_KeepsTheOneNameOperand()
    {
        // `~x.V`: the grace decorates the ONE name `x`; the ordinary dot
        // applies OUTSIDE the grace to the graced name's value. The dot edge's
        // fallback callable `V` joins the signature on its own (an opaque
        // receiver may need it at runtime), but it is NOT graced — only `x`
        // carries the weight. Here `x` is already first in the ordinary
        // DotCall occurrence order (x, V, z), so the prefix grace is inert.
        var root = SourceProvenance.ParseValid("K = ~x.V + z\nObj = {public V = 40}\nK(Obj, 0, 2)").Root;
        Assert.Equal(["x", "V", "z"], Assert.IsType<Algorithm.User>(root.Properties[0].Value).Params);
        // This receiver DOES carry a structural `V`, so the edge resolves
        // structurally and the unused `V` parameter never participates.
        AssertAtom("K = ~x.V + z\nObj = {public V = 40}\nK(Obj, 0, 2)", 42m);
    }

    [Fact]
    public void GraceOnBoundName_IsAValidNoOp()
    {
        AssertAtom("X = 1\nK = ~X + 2\nK", 3m);
    }

    [Fact]
    public void RepeatedMarkers_AccumulateOnTheSameName()
    {
        // `~~x` is one grace of weight -2 on the one occurrence; `~x~` nets 0.
        var doublePrefix = SourceProvenance.ParseValid("K = a + b + ~~x\nK(1, 2, 4)").Root;
        Assert.Equal(["x", "a", "b"], Assert.IsType<Algorithm.User>(doublePrefix.Properties[0].Value).Params);
    }

    // ── Invalid: complex operands, both marker positions ────────────────────

    [Theory]
    [InlineData("K = ~(x + y)")]
    [InlineData("K = (x + y)~")]
    [InlineData("K = ~(x)")]
    [InlineData("K = (x)~")]
    [InlineData("K = f(x)~")]
    [InlineData("K = x.y~")]
    [InlineData("K = ~[x]")]
    [InlineData("K = [x]~")]
    [InlineData("K = 5~")]
    [InlineData("K = (x * y + z)~")]
    public void ComplexGraceOperand_IsRejectedWithTheLawDiagnostic(string source)
        => AssertGraceRejected(source);

    [Fact]
    public void ParenthesizedName_CannotSmuggleAGraceOperand()
    {
        // `(x)` is a capture boundary, not a bare name occurrence, for the
        // grace law exactly as for structural access — parentheses never
        // smuggle an expression into Grace.
        AssertGraceRejected("K = (x)~ + 1");
        AssertGraceRejected("K = ~(x) + 1");
    }
}
