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
    // A marker run attached to a completed non-name expression at the END of
    // a physical line is the same `f(x)~` spelling: a grace marker never
    // binds across a newline in either direction, so it never becomes prefix
    // Grace on the next line's name (K5-R1).
    [InlineData("K = f(x)~\ny")]
    [InlineData("K = (x)~\n-1")]
    [InlineData("K = [1]~\nz")]
    [InlineData("K = 5~\nz")]
    // The same-line forms are the same error: a prefix-grace slot after
    // another slot on one line needs a comma (`F(1), ~c`).
    [InlineData("K = F(1)~ c")]
    [InlineData("K = (x)~ c")]
    [InlineData("K = [1]~ c")]
    [InlineData("K = 5~ c")]
    // A multi-marker run (the end-of-file marker is the `K = f(x)~` row above).
    [InlineData("K = f(x)~~~\ny")]
    // A lone run binds nothing on a later line, and a run on the last line
    // binds nothing at all.
    [InlineData("K = ~\ny")]
    [InlineData("~")]
    public void ComplexGraceOperand_IsRejectedWithTheLawDiagnostic(string source)
        => AssertGraceRejected(source);

    // ── K5-R1: the marker run is physical-line-local, and recovery keeps rows ─

    [Fact]
    public void LineFinalMarkerAfterCall_InABlockBody_IsRejectedInsteadOfReorderingTheNextRow()
    {
        // The reported program: `F(1)~` at the end of a block row silently became
        // prefix Grace on the next row's `a`, reordering the block's implicit
        // parameters (the call printed (20, 1, 10) instead of (10, 1, 20)).
        AssertGraceRejected("Q = {\n  b\n  F(1)~\n  a\n}\nF(z) = z\nQ(10, 20)");

        // The written prefix form on its own line is the supported spelling and
        // stays observable: `~b` moves `b` earlier, so `K(10, 20)` binds b = 10.
        var reordered = Evaluate("K = {\n  a\n  ~b\n}\nK(10, 20)");
        Assert.True(
            Result.ValueComparer.Equals(
                new Result.SequenceValue([new Result.Atom(20), new Result.Atom(10)]),
                reordered),
            $"Expected (20, 10) but got {reordered}");
    }

    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    public void LineFinalMarkerAfterCall_KeepsTheFollowingRowsIntact(string newline)
    {
        // `F(1)~` newline `-1` newline `7`: the run is rejected over its own
        // span and recovery consumes nothing past it, so the following rows
        // survive exactly as written — a `-1` row (never a `1` row) and `7`.
        var source = string.Join(newline, "F(z) = z", "F(1)~", "-1", "7");
        var result = Parser.ParseSyntax(source);

        var diagnostic = Assert.Single(result.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Contains(GraceLawFragment, diagnostic.Message, StringComparison.Ordinal);
        Assert.Equal(2, diagnostic.Span.StartLineNumber);

        var rows = result.Root.Output;
        Assert.Equal(3, rows.Count);
        Assert.IsType<Expr.Call>(rows[0]);
        var negated = Assert.IsType<Expr.Unary>(rows[1]);
        Assert.Equal(UnaryOp.Minus, negated.Op);
        Assert.Equal(1, Assert.IsType<Expr.Num>(negated.Operand).Value);
        Assert.Equal(7, Assert.IsType<Expr.Num>(rows[2]).Value);
    }

    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    public void LoneMarkerRun_IsLineLocal_AndLeavesTheNextRowsPrefixGraceIntact(string newline)
    {
        // `~` newline `~a`: the first line's lone marker is the one error; the
        // run never absorbs the next line's marker, so `~a` stays that row's
        // own prefix Grace (weight -1, never a merged -2).
        var source = string.Join(newline, "a = 1", "~", "~a");
        var result = Parser.ParseSyntax(source);

        var diagnostic = Assert.Single(result.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Equal(2, diagnostic.Span.StartLineNumber);
        Assert.Equal(2, diagnostic.Span.EndLineNumber);

        var grace = Assert.IsType<Expr.Grace>(result.Root.Output[^1]);
        Assert.Equal("a", Assert.IsType<Expr.Resolve>(grace.Inner).Name);
        Assert.Equal(-1, grace.Weight);
    }

    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    public void PrefixMarker_NeverBindsANameOnTheNextLine(string newline)
    {
        // `~` newline `a`: the name on the next line is a row of its own, not
        // the marker's operand.
        var source = string.Join(newline, "a = 1", "~", "a");
        var result = Parser.ParseSyntax(source);

        var diagnostic = Assert.Single(result.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Equal("a", Assert.IsType<Expr.Resolve>(result.Root.Output[^1]).Name);
        Assert.DoesNotContain(result.Root.Output, row => row is Expr.Grace);
    }

    [Fact]
    public void SameLineMarkerAfterCompoundOperand_NeedsACommaToStartAPrefixGraceSlot()
    {
        // `F(1), ~c` is two slots: the call and prefix Grace on `c`.
        var separated = Parser.ParseSyntax("F(z) = z\nc = 3\nF(1), ~c");
        Assert.False(separated.HasErrors);
        Assert.Equal(2, separated.Root.Output.Count);
        Assert.IsType<Expr.Call>(separated.Root.Output[0]);
        var grace = Assert.IsType<Expr.Grace>(separated.Root.Output[1]);
        Assert.Equal("c", Assert.IsType<Expr.Resolve>(grace.Inner).Name);
        Assert.Equal(-1, grace.Weight);

        // Without the comma the run attaches to the completed call and is the
        // law diagnostic; `c` still survives as an ordinary adjacent slot and
        // never acquires the marker.
        var rejected = Parser.ParseSyntax("F(z) = z\nc = 3\nF(1)~ c");
        var diagnostic = Assert.Single(rejected.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Equal(2, rejected.Root.Output.Count);
        Assert.IsType<Expr.Call>(rejected.Root.Output[0]);
        Assert.Equal("c", Assert.IsType<Expr.Resolve>(rejected.Root.Output[1]).Name);
    }

    [Fact]
    public void LoneMarkerBeforeADeclarationLine_KeepsTheDeclaration()
    {
        // `~` newline `Name = 1`: the run is the lone marker of its own line
        // (the property-name diagnostic needs the marker on the name's line),
        // and the declaration on the next line stays intact.
        var result = Parser.ParseSyntax("~\nName = 1\nName");
        var diagnostic = Assert.Single(result.Diagnostics);
        Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
        Assert.Contains(GraceLawFragment, diagnostic.Message, StringComparison.Ordinal);
        Assert.Equal("Name", Assert.Single(result.Root.Properties).Name);
    }

    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    public void MemberPrefixGraceRecovery_IsLineLocalAndPreservesFollowingSyntax(string newline)
    {
        foreach (var next in new[] { "b", "~b", "-1", "Name = 1", "F(z) = z" })
        {
            var source = string.Join(newline, "a.~~ # marker row", next, "7");
            var raw = Parser.ParseSyntax(source);
            var diagnostic = Assert.Single(raw.Diagnostics);
            Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
            Assert.Equal(new SourceSpan(1, 3, 1, 4), diagnostic.Span);
            Assert.Equal("a", Assert.IsType<Expr.Resolve>(raw.Root.Output[0]).Name);
            Assert.Equal(7, Assert.IsType<Expr.Num>(raw.Root.Output[^1]).Value);
            if (next == "~b")
                Assert.Equal(-1, Assert.IsType<Expr.Grace>(raw.Root.Output[1]).Weight);
            else if (next == "-1")
                Assert.Equal(UnaryOp.Minus, Assert.IsType<Expr.Unary>(raw.Root.Output[1]).Op);
            else if (next.Contains('='))
                Assert.Single(raw.Root.Properties);
            else
                Assert.Equal("b", Assert.IsType<Expr.Resolve>(raw.Root.Output[1]).Name);

            Assert.Equal(DiagnosticCode.InvalidGraceMarker, Assert.Single(Parser.Parse(source).Diagnostics).Code);
        }

        // EOF and a same-line non-name also blame the whole marker run once.
        foreach (var source in new[] { "a.~~", "a.~~ 7" })
            Assert.Equal(new SourceSpan(1, 3, 1, 4), Assert.Single(Parser.ParseSyntax(source).Diagnostics).Span);
    }

    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    public void DeclarationGraceRecovery_DoesNotMergeMarkerRunsAcrossLines(string newline)
    {
        var raw = Parser.ParseSyntax($"F(~~{newline}~a, b) = b{newline}7");
        Assert.Equal(2, raw.Diagnostics.Count);
        Assert.All(raw.Diagnostics, d =>
        {
            Assert.Equal(DiagnosticCode.InvalidGraceMarker, d.Code);
            Assert.Equal(d.Span.StartLineNumber, d.Span.EndLineNumber);
        });
        Assert.Equal(new SourceSpan(1, 3, 1, 4), raw.Diagnostics[0].Span);
        Assert.Equal("F", Assert.Single(raw.Root.Properties).Name);
        Assert.Equal(7, Assert.IsType<Expr.Num>(Assert.Single(raw.Root.Output)).Value);

        var property = Parser.ParseSyntax($"~~Name = 1{newline}7");
        Assert.Equal(new SourceSpan(1, 1, 1, 2), Assert.Single(property.Diagnostics).Span);
        Assert.Equal("Name", Assert.Single(property.Root.Properties).Name);
    }

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
