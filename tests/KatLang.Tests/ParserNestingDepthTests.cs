namespace KatLang.Tests;

/// <summary>
/// Regression coverage for the parser recursion-depth budget (see
/// <c>Parser.MaxNestingDepth</c>), added after the Phase-2 depth-probe campaign found
/// that deeply nested surface input drove the recursive-descent parser into a fatal,
/// host-terminating stack overflow at inputs as small as ~330 bytes.
///
/// Every input below that previously crashed the process is now bounded, so it is safe
/// to run these directly in-process: the parse aborts at the budget (well below any
/// native stack boundary) and returns a structured diagnostic. A test completing at all
/// is itself the proof that the input no longer overflows the stack.
/// </summary>
public class ParserNestingDepthTests
{
    private const string NestingMessage = "Nesting is too deep";

    private static string Rep(string s, int n) => string.Concat(Enumerable.Repeat(s, n));

    private static bool HasNestingDiagnostic(SyntaxParseResult r)
        => r.Diagnostics.Any(d => d.Message.Contains(NestingMessage, StringComparison.Ordinal));

    private static bool HasExpressionChainDiagnostic(SyntaxParseResult r)
        => r.Diagnostics.Any(
            d => d.Message.Contains("Expression operator or postfix chain is too deep", StringComparison.Ordinal));

    private static void AssertParses(string source)
    {
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics));
        Assert.False(HasNestingDiagnostic(result));
    }

    private static Expr SingleOutput(SyntaxParseResult result)
    {
        var user = Assert.IsType<Algorithm.User>(result.Root);
        return Assert.Single(user.Output);
    }

    // ── Realistic deep input still succeeds (comfortably within budget) ───────
    [Theory]
    [InlineData("(", ")", 90)]   // groups: 4 weighted units/level (heavy machinery)
    [InlineData("{", "}", 90)]   // blocks: 4 units/level
    [InlineData("[", "]", 120)]  // lists: 3 units/level
    [InlineData("A[", "]", 120)] // nested selections: the list literal's production, 3 units/level
    public void DeepBalanced_InBudget_ParsesWithoutError(string open, string close, int levels)
    {
        // Just under each shape's budget capacity — every capacity was proven to
        // parse on a dedicated 512 KiB thread (half the documented 1 MiB minimum),
        // so the budget, not the machine, is what stops deeper input.
        var result = Parser.ParseSyntax(Rep(open, levels) + "1" + Rep(close, levels));
        Assert.False(result.HasErrors);
        Assert.False(HasNestingDiagnostic(result));
    }

    [Theory]
    [InlineData("not ")]     // prefix not-chain (~1 weighted unit/level)
    [InlineData("-")]        // prefix minus-chain
    public void DeepPrefix_InBudget_ParsesWithoutError(string prefix)
    {
        var result = Parser.ParseSyntax(Rep(prefix, 350) + "1");
        Assert.False(result.HasErrors);
        Assert.False(HasNestingDiagnostic(result));
    }

    // ── Boundary behaviour: exact per-shape maxima parse, one beyond diagnoses ─
    [Theory]
    [InlineData("(", ")", 95)]   // 95 x 4 units + 2 = 382 <= 384; 96 x 4 + 2 = 386
    [InlineData("{", "}", 95)]
    [InlineData("[", "]", 127)]  // 127 x 3 + 2 = 383 <= 384
    [InlineData("A[", "]", 127)] // nested selections: each selector slot holds the next selection
    [InlineData("A[0, ", "]", 127)] // a sibling selector before each nested one charges nothing extra
    public void StructuralBoundary_AtMaximumParses_OneBeyondDiagnoses(string open, string close, int max)
    {
        AssertParses(Rep(open, max) + "1" + Rep(close, max));
        Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(Rep(open, max + 1) + "1" + Rep(close, max + 1))));
    }

    [Fact]
    public void PrefixBoundary_AtMaximumParses_OneBeyondDiagnoses()
    {
        // Unary levels charge one unit each: 382 + entry = 384 units exactly.
        AssertParses(Rep("-", 382) + "1");
        Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(Rep("-", 383) + "1")));
    }

    [Fact]
    public void PowerBoundary_UsesTheEstablishedExpressionChainMaximum()
    {
        // Power is parsed right-associatively and charges the cumulative recursion
        // counter, but its completed AST is also an operator chain. The established
        // 256-link chain policy is therefore the first successful-surface boundary.
        // (ParsePower deliberately holds ONE live unit per `^` level — the
        // exponent re-enters ParseUnary under the still-live entry charge — so
        // this boundary is unchanged by the power-vs-unary precedence split.)
        AssertParses(Rep("1 ^ ", Parser.MaxExpressionChainDepth) + "1");
        var oneBeyond = Parser.ParseSyntax(Rep("1 ^ ", Parser.MaxExpressionChainDepth + 1) + "1");
        Assert.True(oneBeyond.HasErrors);
        Assert.True(HasExpressionChainDiagnostic(oneBeyond));
        Assert.False(HasNestingDiagnostic(oneBeyond));
    }

    [Fact]
    public void AlternatingUnaryPowerBoundary_AtMaximumParses_OneBeyondDiagnoses()
    {
        // Under power-over-unary precedence, `-1 ^ -1 ^ ... ^ 1` nests as
        // `-(1 ^ (-(1 ^ ...)))`: each `-1 ^ ` segment holds TWO live units
        // (the prefix ParseUnary level plus the exponent's re-entered
        // ParseUnary level), and the chain guard never accumulates through the
        // interleaved unary wrappers, so the recursion budget is the first
        // boundary for this compound shape. Entry and the final operand add
        // two more units: 2N + 2 <= 384 admits N <= 191 segments.
        AssertParses(Rep("-1 ^ ", 191) + "1");
        Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(Rep("-1 ^ ", 192) + "1")));
    }

    [Fact]
    public void AlternatingUnaryPower_OverBudget_EmitsNestingDiagnostic()
        => Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(Rep("-1 ^ ", 5000) + "1")));

    [Fact]
    public void DeepUnaryExponentTail_OverBudget_EmitsNestingDiagnostic()
        => Assert.True(HasNestingDiagnostic(Parser.ParseSyntax("2 ^ " + Rep("-", 5000) + "1")));

    [Fact]
    public void CallNestingBoundary_AtMaximumParses_OneBeyondDiagnoses()
    {
        // Call argument levels charge 3 units (base 2 + call surcharge 1).
        AssertParses("f(x) = x\n" + Rep("f(", 127) + "1" + Rep(")", 127));
        Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(
            "f(x) = x\n" + Rep("f(", 128) + "1" + Rep(")", 128))));
    }

    [Fact]
    public void TrailingBraceCallBoundary_AtMaximumParses_OneBeyondDiagnoses()
    {
        // A trailing-brace call level charges 5 units: the two base charges
        // (ParseExpression + ParseUnary) plus BOTH heavy surcharges, because
        // the form runs the call machinery AND the block machinery
        // (EnterDelimitedProduction(TokenKind.RBrace, CallArgsNestingSurcharge + BlockNestingSurcharge)
        // in ParseCallArgs). 76 levels peak at 76 x 5 + 2 (innermost leaf)
        // = 382 <= 384 and parse; level 77's surcharge chokepoint reaches
        // 77 x 5 = 385 > 384 and diagnoses. The historical calibration
        // comment claimed 4 units while the implementation has always charged
        // the conservative 5 — this pins the real boundary so a one-unit
        // charge drift in either direction fails here.
        AssertParses("f(x) = x\n" + Rep("f{", 76) + "1" + Rep("}", 76));
        Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(
            "f(x) = x\n" + Rep("f{", 77) + "1" + Rep("}", 77))));
    }

    [Fact]
    public void PatternBoundary_AtMaximumParses_OneBeyondDiagnoses()
    {
        // Nested sequence patterns (each a pair: a one-item sequence pattern is invalid) and
        // nested list patterns charge the same one unit per level.
        AssertParses("F(" + Rep("(", 383) + "x" + Rep(", y)", 383) + ") = x\nF(1)");
        Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(
            "F(" + Rep("(", 384) + "x" + Rep(", y)", 384) + ") = x\nF(1)")));
        AssertParses("F(" + Rep("[", 383) + "x" + Rep("]", 383) + ") = x\nF(1)");
        Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(
            "F(" + Rep("[", 384) + "x" + Rep("]", 384) + ") = x\nF(1)")));
    }

    [Fact]
    public void MixedContainers_ChargeCumulatively_NeverPerMechanism()
    {
        // The one cumulative budget is shared by every grammar mechanism: alternating
        // group/list/block levels charge 4 + 3 + 4 units per cycle, so ~35 cycles
        // exhaust it even though each DELIMITER KIND alone is far below its own
        // capacity — per-mechanism budgets would wrongly admit this shape.
        AssertParses(Rep("([{", 34) + "1" + Rep("}])", 34));
        Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(Rep("([{", 35) + "1" + Rep("}])", 35))));
    }

    [Fact]
    public void InitialDebt_IsBoundedAndComposesWithExpressionFrames()
    {
        AssertParsesWithDebt("1", 382);

        var oneBeyond = Parser.ParseSyntax("1", 383);
        Assert.True(oneBeyond.HasErrors);
        Assert.Single(oneBeyond.Diagnostics, d => d.Message.Contains(NestingMessage, StringComparison.Ordinal));

        var hostileDebt = Parser.ParseSyntax("1", int.MaxValue);
        Assert.True(hostileDebt.HasErrors);
        Assert.Single(hostileDebt.Diagnostics, d => d.Message.Contains(NestingMessage, StringComparison.Ordinal));

        static void AssertParsesWithDebt(string source, int debt)
        {
            var result = Parser.ParseSyntax(source, debt);
            Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics));
        }
    }

    // ── Over budget: one structured, source-positioned diagnostic, no crash ───
    [Theory]
    [InlineData("(", ")")]
    [InlineData("[", "]")]
    [InlineData("A[", "]")]
    [InlineData("{", "}")]
    public void DeepBalanced_OverBudget_EmitsNestingDiagnostic(string open, string close)
    {
        var result = Parser.ParseSyntax(Rep(open, 5000) + "1" + Rep(close, 5000));
        Assert.True(result.HasErrors);
        Assert.True(HasNestingDiagnostic(result));
    }

    [Fact]
    public void DeepUnaryMinus_OverBudget_EmitsNestingDiagnostic()
        => Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(Rep("-", 5000) + "1")));

    [Fact]
    public void DeepPower_OverBudget_EmitsNestingDiagnostic()
        => Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(Rep("1 ^ ", 5000) + "1")));

    [Fact]
    public void DeepPattern_OverBudget_EmitsNestingDiagnostic()
        => Assert.True(HasNestingDiagnostic(
            Parser.ParseSyntax("F" + Rep("(", 5000) + "x" + Rep(")", 5000) + " = x\nF(1)")));

    // ── Malformed deep input recovers with a diagnostic (no crash) ────────────
    [Theory]
    [InlineData("(")]
    [InlineData("[")]
    [InlineData("{")]
    public void DeepUnclosed_OverBudget_RecoversWithoutCrash(string open)
    {
        var result = Parser.ParseSyntax(Rep(open, 5000) + "1");
        Assert.True(result.HasErrors);
    }

    [Fact]
    public void NestingDiagnostic_IsSourcePositioned()
    {
        var result = Parser.ParseSyntax(Rep("(", 5000) + "1" + Rep(")", 5000));
        var diagnostic = result.Diagnostics.First(d => d.Message.Contains(NestingMessage, StringComparison.Ordinal));
        Assert.True(Assert.NotNull(diagnostic.Span).Start.Line >= 1);
        Assert.True(Assert.NotNull(diagnostic.Span).Start.Column >= 1);
        Assert.True(Assert.NotNull(diagnostic.Span).End.Line >= Assert.NotNull(diagnostic.Span).Start.Line);
    }

    // ── Semantics preserved for in-budget programs ────────────────────────────
    [Fact]
    public void Power_StaysRightAssociative()
    {
        // 1 ^ 2 ^ 3  ==  1 ^ (2 ^ 3)
        var outer = Assert.IsType<Expr.Binary>(SingleOutput(Parser.ParseSyntax("1 ^ 2 ^ 3")));
        Assert.Equal(BinaryOp.Pow, outer.Op);
        Assert.Equal(1m, Assert.IsType<Expr.Num>(outer.Left).Value);
        var inner = Assert.IsType<Expr.Binary>(outer.Right);
        Assert.Equal(BinaryOp.Pow, inner.Op);
        Assert.Equal(2m, Assert.IsType<Expr.Num>(inner.Left).Value);
        Assert.Equal(3m, Assert.IsType<Expr.Num>(inner.Right).Value);
    }

    [Fact]
    public void ShallowUnaryChain_ShapeUnchanged()
    {
        // ---1  ==  Unary(-, Unary(-, Unary(-, 1)))
        var u1 = Assert.IsType<Expr.Unary>(SingleOutput(Parser.ParseSyntax("---1")));
        Assert.Equal(UnaryOp.Minus, u1.Op);
        var u2 = Assert.IsType<Expr.Unary>(u1.Operand);
        var u3 = Assert.IsType<Expr.Unary>(u2.Operand);
        Assert.Equal(1m, Assert.IsType<Expr.Num>(u3.Operand).Value);
    }

    [Fact]
    public void ListParenScalar_StayDistinct()
    {
        Assert.IsType<Expr.ListLiteral>(SingleOutput(Parser.ParseSyntax("[7]")));   // exact list
        Assert.IsType<Expr.Num>(SingleOutput(Parser.ParseSyntax("(7)")));           // unwrapped grouping
        Assert.IsType<Expr.Num>(SingleOutput(Parser.ParseSyntax("7")));             // scalar
    }

    // ── Grace marker-run scans are linear in the run (bug-hunt B5a, K2-R3) ────
    //
    // `LookaheadThroughTildesToPropertyDef` walked a k-marker run with
    // `PeekSignificant(offset)` for offset 0..k; that primitive restarts at the
    // current position and is O(offset) per call, so ONE row-start run cost O(k²)
    // (3.3 s for 40 000 markers, ~4x per doubling) and a parse could not be
    // interrupted until it finished. The scan now walks token indices from one
    // cursor and memoizes its verdict per run start. Pinned deterministically
    // through the parser's token-step counter (ParserTraversalObservations)
    // rather than wall-clock: doubling the run may at most 2.5x the steps. Each
    // shape's diagnostics and tree are pinned alongside — the observable structure the
    // offset walk produced, because this is a pure traversal change.

    public enum GraceRunShape
    {
        /// <summary>`1 ~~~x` at root: a same-line run after a NON-name operand is the one-name Grace law's recovery — one diagnostic over the run, `x` an ordinary adjacent row.</summary>
        PostfixRunAtRoot,

        /// <summary>The same run inside a definition body: `F(x) = 1 ~~~x` newline `F(2)`.</summary>
        PostfixRunInDefinitionBody,

        /// <summary>`~~~` newline `x = 1` newline `x`: a row-start run with no same-line name — the diagnostic-producing prefix run before a declaration.</summary>
        PrefixRunBeforeDeclaration,

        /// <summary>`~~~x`: the legal, diagnostic-free root prefix run (weight −k).</summary>
        PrefixRunOnRootName,

        /// <summary>`(~~~x)`: the same legal run as a grouped row.</summary>
        PrefixRunInGroup,
    }

    private static string Tildes(int k) => new('~', k);

    private static string GraceRunSource(GraceRunShape shape, int k) => shape switch
    {
        GraceRunShape.PostfixRunAtRoot => $"1 {Tildes(k)}x",
        GraceRunShape.PostfixRunInDefinitionBody => $"F(x) = 1 {Tildes(k)}x\nF(2)",
        GraceRunShape.PrefixRunBeforeDeclaration => $"{Tildes(k)}\nx = 1\nx",
        GraceRunShape.PrefixRunOnRootName => $"{Tildes(k)}x",
        GraceRunShape.PrefixRunInGroup => $"({Tildes(k)}x)",
        _ => throw new ArgumentOutOfRangeException(nameof(shape), shape, null),
    };

    private static void AssertGraceRunShape(GraceRunShape shape, int k, SyntaxParseResult result)
    {
        var root = Assert.IsType<Algorithm.User>(result.Root);
        switch (shape)
        {
            case GraceRunShape.PostfixRunAtRoot:
                {
                    var diagnostic = Assert.Single(result.Diagnostics);
                    Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
                    Assert.Equal(new SourceSpan(1, 3, 1, k + 3), diagnostic.Span);
                    Assert.Empty(root.Properties);
                    Assert.Equal(2, root.Output.Count);
                    Assert.Equal(1m, Assert.IsType<Expr.Num>(root.Output[0]).Value);
                    Assert.Equal("x", Assert.IsType<Expr.Resolve>(root.Output[1]).Name);
                    break;
                }

            case GraceRunShape.PostfixRunInDefinitionBody:
                {
                    var diagnostic = Assert.Single(result.Diagnostics);
                    Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
                    Assert.Equal(new SourceSpan(1, 10, 1, k + 10), diagnostic.Span);
                    var f = Assert.Single(root.Properties);
                    Assert.Equal("F", f.Name);
                    var body = Assert.IsType<Algorithm.User>(f.Value);
                    Assert.Equal("x", Assert.Single(body.Params));
                    Assert.Equal(2, body.Output.Count);
                    Assert.Equal(1m, Assert.IsType<Expr.Num>(body.Output[0]).Value);
                    Assert.Equal("x", Assert.IsType<Expr.Resolve>(body.Output[1]).Name);
                    var call = Assert.IsType<Expr.Call>(Assert.Single(root.Output));
                    Assert.Equal("F", Assert.IsType<Expr.Resolve>(call.Function).Name);
                    Assert.Equal(2m, Assert.IsType<Expr.Num>(Assert.Single(call.Args)).Value);
                    break;
                }

            case GraceRunShape.PrefixRunBeforeDeclaration:
                {
                    var diagnostic = Assert.Single(result.Diagnostics);
                    Assert.Equal(DiagnosticCode.InvalidGraceMarker, diagnostic.Code);
                    Assert.Equal(new SourceSpan(1, 1, 1, k + 1), diagnostic.Span);
                    var x = Assert.Single(root.Properties);
                    Assert.Equal("x", x.Name);
                    Assert.Equal(1m, Assert.IsType<Expr.Num>(Assert.Single(Assert.IsType<Algorithm.User>(x.Value).Output)).Value);
                    // The run's recovery placeholder, then the `x` row.
                    Assert.Equal(2, root.Output.Count);
                    Assert.Equal(0m, Assert.IsType<Expr.Num>(root.Output[0]).Value);
                    Assert.Equal("x", Assert.IsType<Expr.Resolve>(root.Output[1]).Name);
                    break;
                }

            case GraceRunShape.PrefixRunOnRootName:
                {
                    Assert.Empty(result.Diagnostics);
                    Assert.Empty(root.Properties);
                    var grace = Assert.IsType<Expr.Grace>(Assert.Single(root.Output));
                    Assert.Equal(-k, grace.Weight);
                    Assert.Equal("x", Assert.IsType<Expr.Resolve>(grace.Inner).Name);
                    break;
                }

            case GraceRunShape.PrefixRunInGroup:
                {
                    // Parentheses group syntax: `(~~~x)` is the graced name `~~~x` itself —
                    // the redundant group is erased and the marker run keeps its weight.
                    Assert.Empty(result.Diagnostics);
                    Assert.Empty(root.Properties);
                    var grace = Assert.IsType<Expr.Grace>(Assert.Single(root.Output));
                    Assert.Equal(-k, grace.Weight);
                    Assert.Equal("x", Assert.IsType<Expr.Resolve>(grace.Inner).Name);
                    break;
                }

            default:
                throw new ArgumentOutOfRangeException(nameof(shape), shape, null);
        }
    }

    private static long ObservedTokenSteps(GraceRunShape shape, int k)
    {
        var observations = new ParserTraversalObservations();
        var result = Parser.ParseSyntaxObserved(GraceRunSource(shape, k), observations);
        AssertGraceRunShape(shape, k, result);
        return observations.TokenSteps;
    }

    [Theory]
    [InlineData(GraceRunShape.PostfixRunAtRoot)]
    [InlineData(GraceRunShape.PostfixRunInDefinitionBody)]
    [InlineData(GraceRunShape.PrefixRunBeforeDeclaration)]
    [InlineData(GraceRunShape.PrefixRunOnRootName)]
    [InlineData(GraceRunShape.PrefixRunInGroup)]
    public void GraceMarkerRun_TokenStepsGrowLinearly(GraceRunShape shape)
    {
        var steps20 = ObservedTokenSteps(shape, 20_000);
        var steps40 = ObservedTokenSteps(shape, 40_000);

        // Every marker is consumed at least once, so the counter is a real cost model.
        Assert.True(steps20 >= 20_000, $"{shape}: {steps20} steps for 20 000 markers");
        // Linear: doubling the run at most 2.5x the steps (the offset walk grew ~4x).
        Assert.True(steps40 <= 2.5 * steps20, $"{shape}: {steps20} -> {steps40} steps (20k -> 40k markers)");
        // Do not run the still larger input after an already-proven complexity regression.
        var steps80 = ObservedTokenSteps(shape, 80_000);
        Assert.True(steps80 <= 2.5 * steps40, $"{shape}: {steps40} -> {steps80} steps (40k -> 80k markers)");
    }

    [Theory]
    [InlineData("{0}x = 1\nx\n42", 1)]
    [InlineData("0\n{0}public x = 1\nx\n42", 1)]
    [InlineData("{0}1\n42", 1)]
    [InlineData("{0}# comment\n{0}x\n42", 1)]
    [InlineData("a.{0}b\n42", 0)]
    [InlineData("a*{0}.F\n42", 1)]
    [InlineData("a.{0}\n{0}b\n42", 1)]
    [InlineData("F({0}x) = x\n42", 1)]
    [InlineData("x{0}\n42", 0)]
    public void GraceMarkerRun_DeclarationMemberAndRecoveryScansAreLinear(string template, int diagnosticCount)
    {
        long previousSteps = 0;
        foreach (var k in new[] { 20_000, 40_000, 80_000 })
        {
            var observations = new ParserTraversalObservations();
            var parsed = Parser.ParseSyntaxObserved(template.Replace("{0}", Tildes(k)), observations);
            Assert.Equal(diagnosticCount, parsed.Diagnostics.Count);
            Assert.All(parsed.Diagnostics, d => Assert.Equal(DiagnosticCode.InvalidGraceMarker, d.Code));
            // Every shape must consume its run and preserve a later output row.
            var root = Assert.IsType<Algorithm.User>(parsed.Root);
            Assert.Equal(42m, Assert.IsType<Expr.Num>(root.Output[^1]).Value);
            Assert.True(observations.TokenSteps >= k);
            if (previousSteps > 0)
                Assert.True(observations.TokenSteps <= 2.5 * previousSteps,
                    $"{template}: {previousSteps} -> {observations.TokenSteps} steps at {k} markers");
            previousSteps = observations.TokenSteps;
        }
    }

    /// <summary>
    /// The traversal change produced no new shape: every run shape parses to the
    /// diagnostics, spans, weights, and tree the offset walk produced, and the
    /// observed entry is the unobserved parse with a counter attached.
    /// </summary>
    [Theory]
    [InlineData(GraceRunShape.PostfixRunAtRoot, 1)]
    [InlineData(GraceRunShape.PostfixRunAtRoot, 3)]
    [InlineData(GraceRunShape.PostfixRunInDefinitionBody, 1)]
    [InlineData(GraceRunShape.PostfixRunInDefinitionBody, 3)]
    [InlineData(GraceRunShape.PrefixRunBeforeDeclaration, 1)]
    [InlineData(GraceRunShape.PrefixRunBeforeDeclaration, 3)]
    [InlineData(GraceRunShape.PrefixRunOnRootName, 1)]
    [InlineData(GraceRunShape.PrefixRunOnRootName, 3)]
    [InlineData(GraceRunShape.PrefixRunInGroup, 1)]
    [InlineData(GraceRunShape.PrefixRunInGroup, 3)]
    public void GraceMarkerRun_SmallRuns_KeepTheirShape(GraceRunShape shape, int k)
    {
        var source = GraceRunSource(shape, k);
        var unobserved = Parser.ParseSyntax(source);
        AssertGraceRunShape(shape, k, unobserved);

        var observations = new ParserTraversalObservations();
        var observed = Parser.ParseSyntaxObserved(source, observations);
        AssertGraceRunShape(shape, k, observed);
        Assert.True(observations.TokenSteps > 0);
        Assert.Equal(
            unobserved.Diagnostics.Select(d => (d.Code, d.Span, d.Message)),
            observed.Diagnostics.Select(d => (d.Code, d.Span, d.Message)));

        var elaborated = Parser.Parse(source);
        Assert.Equal(unobserved.Diagnostics, elaborated.Diagnostics);
        // Hand-written recovery/Grace expectations after elaboration. With one
        // inferred parameter, Grace changes no parameter order, and the group
        // containing Grace keeps the plain name's capture boundary (`(~~~x)`
        // elaborates exactly like `(x)`).
        var expectedSource = shape switch
        {
            GraceRunShape.PostfixRunAtRoot => "1, x",
            GraceRunShape.PostfixRunInDefinitionBody => "F(x) = 1, x\nF(2)",
            GraceRunShape.PrefixRunBeforeDeclaration => "0\nx = 1\nx",
            GraceRunShape.PrefixRunOnRootName => "x",
            GraceRunShape.PrefixRunInGroup => "(x)",
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        };
        Assert.Equal(
            LeanAstEncoder.EncodeProgram(SourceProvenance.ParseValid(expectedSource).Root),
            LeanAstEncoder.EncodeProgram(elaborated.Root));
    }

    // ── Clause-head lookahead over nested calls is linear (KL-03) ─────────────
    //
    // Every call level of `I(I(…I(1)…))` begins a row of an argument list, so the body
    // loop asks THE declaration-start relation whether `I(…) =` begins there, and the
    // clause-head confinement scan (TryFindClauseHeadClose) walked the region inside
    // that level to its `)`: one walk per level, quadratic in the depth of ONE row. The
    // pre-change parser (810049ee, the same counts as the research baseline 7db03e0a)
    // took 94, 212, 592, 1,164 and 1,928 token steps for depths 4, 8, 16, 24 and 32.
    // The region an opening delimiter opens is now decided once per parse
    // (TryCloseDelimiterRegion, a token-indexed memo whose allocation, reads and writes
    // are charged to the same counter), so a parse costs a bounded number of token
    // steps per token at every admitted depth and width, malformed regions included.
    //
    // THE BOUND: at most MaxStepsPerToken token steps per lexed token (end of input
    // included), at sampled depths from 1 to the deepest the nesting budget admits. This
    // build measures, at the deepest admitted depth: Call 5.63 (depth 127), Group and
    // Block 5.17 (54), CommentedLines 5.72 (127), Mismatch 4.97 (127), Unclosed 6.42
    // (127), and 5.66 for 16 sibling rows of depth 32. The pre-change parser measured
    // 66.0, 29.7, 97.0, 44.3, 67.0 and 19.6 there, and exceeded the bound from depth 16
    // (Mismatch from depth 32). Doubling the depth may also at most 2.5x the steps (the
    // convention of the marker-run pins above; the pre-change parser grew up to 3.6x).

    private const int MaxStepsPerToken = 8;

    private const string NestedCandidatePrefix = "I(x) = x\n";

    public enum NestedCandidateShape
    {
        /// <summary>`I(I(…I(1)…))`: one clause-head candidate per call level.</summary>
        Call,

        /// <summary>`I((I((…1…))))`: every argument a redundant group whose row is the next candidate.</summary>
        Group,

        /// <summary>`I({I({…1…})})`: every argument a brace block whose body row is the next candidate.</summary>
        Block,

        /// <summary>`I(# c` newline … `1)…)`: one level per physical line, a comment after every `(`.</summary>
        CommentedLines,

        /// <summary>`I(I(…I(1])…))` then `Good = 41`: the innermost level ends at `]`, so no candidate's region closes within itself.</summary>
        Mismatch,

        /// <summary>`I(I(…I(1` then `Good = 41`: every candidate's region reaches the end of input.</summary>
        Unclosed,
    }

    public static TheoryData<NestedCandidateShape> NestedCandidateShapes()
        => new(Enum.GetValues<NestedCandidateShape>());

    private static string NestedCandidateSource(NestedCandidateShape shape, int depth) => shape switch
    {
        NestedCandidateShape.Call => NestedCandidatePrefix + Rep("I(", depth) + "1" + Rep(")", depth),
        NestedCandidateShape.Group => NestedCandidatePrefix + Rep("I((", depth) + "1" + Rep("))", depth),
        NestedCandidateShape.Block => NestedCandidatePrefix + Rep("I({", depth) + "1" + Rep("})", depth),
        NestedCandidateShape.CommentedLines => NestedCandidatePrefix + Rep("I(# c\n", depth) + "1" + Rep(")", depth),
        NestedCandidateShape.Mismatch => NestedCandidatePrefix + Rep("I(", depth) + "1]" + Rep(")", depth) + "\nGood = 41\nGood",
        NestedCandidateShape.Unclosed => NestedCandidatePrefix + Rep("I(", depth) + "1\nGood = 41\nGood",
        _ => throw new ArgumentOutOfRangeException(nameof(shape), shape, null),
    };

    /// <summary>The deepest nesting the parser's budget admits for the shape (one more level is refused).</summary>
    private static int MaxAdmittedDepth(NestedCandidateShape shape)
        => shape is NestedCandidateShape.Group or NestedCandidateShape.Block ? 54 : 127;

    private static int[] AdmittedDepths(NestedCandidateShape shape)
        => new[] { 1, 2, 4, 8, 16, 24, 32, 64, MaxAdmittedDepth(shape) / 2, MaxAdmittedDepth(shape) }
            .Where(depth => depth <= MaxAdmittedDepth(shape))
            .Distinct()
            .Order()
            .ToArray();

    private static int TokenCount(string source) => Lexer.Tokenize(source).Tokens.Count;

    private static void AssertNestedCandidateShape(NestedCandidateShape shape, int depth, SyntaxParseResult result)
    {
        var root = Assert.IsType<Algorithm.User>(result.Root);
        switch (shape)
        {
            case NestedCandidateShape.Mismatch:
                // The innermost call takes the `]` nothing owes as its closer, the outer calls take
                // `)` each, and the one `)` left over is a root stray; `Good` stays a root declaration.
                Assert.Equal(
                    new (DiagnosticCode, SourceSpan?, string)[]
                    {
                        (DiagnosticCode.UnexpectedToken, new SourceSpan(2, 2 * depth + 2, 2, 2 * depth + 3), "Expected ')' but found ']'."),
                        (DiagnosticCode.UnexpectedToken, new SourceSpan(2, 3 * depth + 2, 2, 3 * depth + 3), "Unexpected ')' at the top level. There is no open '(' for it to close."),
                    },
                    result.Diagnostics.Select(d => (d.Code, d.Span, d.Message)));
                Assert.Equal(new[] { "Good", "I" }, root.Properties.Select(p => p.Name));
                Assert.Equal(41m, Assert.IsType<Expr.Num>(Assert.Single(Assert.IsType<Algorithm.User>(root.Properties[0].Value).Output)).Value);
                Assert.Equal(2, root.Output.Count);
                Assert.Equal("Good", Assert.IsType<Expr.Resolve>(root.Output[1]).Name);
                return;

            case NestedCandidateShape.Unclosed:
                // `Good = 41` lies inside the open argument lists: the declaration is reported there,
                // then every call reports its missing `)` at the end of input.
                Assert.Equal(depth + 1, result.Diagnostics.ReportedCount);
                Assert.Equal(
                    new (DiagnosticCode, SourceSpan?)[] { (DiagnosticCode.DeclarationInParentheses, new SourceSpan(3, 1, 3, 5)) }
                        .Concat(Enumerable.Repeat<(DiagnosticCode, SourceSpan?)>((DiagnosticCode.UnexpectedToken, new SourceSpan(4, 5, 4, 5)), depth)),
                    result.Diagnostics.Select(d => (d.Code, d.Span)));
                Assert.All(result.Diagnostics.Skip(1), d => Assert.Equal("Expected ')' but found end of input.", d.Message));
                Assert.Equal(new[] { "I" }, root.Properties.Select(p => p.Name));
                Assert.Single(root.Output);
                return;
        }

        Assert.Empty(result.Diagnostics);
        Assert.Equal(new[] { "I" }, root.Properties.Select(p => p.Name));
        var expr = Assert.Single(root.Output);
        for (var level = 0; level < depth; level++)
        {
            var call = Assert.IsType<Expr.Call>(expr);
            Assert.Equal("I", Assert.IsType<Expr.Resolve>(call.Function).Name);
            if (shape == NestedCandidateShape.Call)
                Assert.Equal(new SourceSpan(2, 2 * level + 1, 2, 3 * depth - level + 2), call.Span);
            expr = Assert.Single(call.Args);
            if (shape == NestedCandidateShape.Block)
                expr = Assert.Single(Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(expr).Algorithm).Output);
        }

        Assert.Equal(1m, Assert.IsType<Expr.Num>(expr).Value);
    }

    private static void AssertWithinLinearBound(string label, long steps, int tokens)
    {
        Assert.True(steps >= tokens, $"{label}: {steps} steps for {tokens} tokens; every token is consumed or probed at least once.");
        Assert.True(
            steps <= (long)MaxStepsPerToken * tokens,
            $"{label}: {steps} steps for {tokens} tokens ({(double)steps / tokens:F2} per token, bound {MaxStepsPerToken}).");
    }

    [Theory]
    [MemberData(nameof(NestedCandidateShapes))]
    public void NestedClauseHeadCandidates_TokenStepsStayLinearThroughTheAdmittedDepth(NestedCandidateShape shape)
    {
        var stepsByDepth = new Dictionary<int, long>();
        foreach (var depth in AdmittedDepths(shape))
        {
            var source = NestedCandidateSource(shape, depth);
            var observations = new ParserTraversalObservations();
            var result = Parser.ParseSyntaxObserved(source, observations);
            AssertNestedCandidateShape(shape, depth, result);
            AssertWithinLinearBound($"{shape} at depth {depth}", observations.TokenSteps, TokenCount(source));
            if (stepsByDepth.TryGetValue(depth / 2, out var half) && depth % 2 == 0)
                Assert.True(observations.TokenSteps <= 2.5 * half, $"{shape}: {half} -> {observations.TokenSteps} steps (depth {depth / 2} -> {depth})");
            stepsByDepth[depth] = observations.TokenSteps;

            // The observed parse is the ordinary one, and the elaborated front end agrees on the diagnostics.
            var unobserved = Parser.ParseSyntax(source);
            Assert.Equal(
                unobserved.Diagnostics.Select(d => (d.Code, d.Span, d.Message)),
                result.Diagnostics.Select(d => (d.Code, d.Span, d.Message)));
            Assert.Equal(LeanAstEncoder.EncodeProgram(unobserved.Root), LeanAstEncoder.EncodeProgram(result.Root));
            var elaborated = Parser.Parse(source);
            Assert.Equal(
                result.Diagnostics.Select(d => (d.Code, d.Span, d.Message)),
                elaborated.Diagnostics.Select(d => (d.Code, d.Span, d.Message)));
        }

        // The depths reach the budget: one level more is the structured nesting refusal.
        Assert.Contains(
            Parser.ParseSyntax(NestedCandidateSource(shape, MaxAdmittedDepth(shape) + 1)).Diagnostics,
            d => d.Code == DiagnosticCode.NestingTooDeep);
    }

    [Theory]
    [InlineData("]")]
    [InlineData("")]
    public void ClauseHeadRegionMemo_ChargesNestedReadsAndWritesOnFailure(string terminator)
    {
        const int nestedOpeners = 32;
        long ClassifyFailedHead(string body)
        {
            var observations = new ParserTraversalObservations();
            var verdicts = Parser.ClassifyDeclarationStartsInOrder(
                "F(" + body + "1" + terminator, [0], includeCommaSpanningBindingPatterns: false, observations);
            Assert.Equal(Parser.DeclarationStart.None, Assert.Single(verdicts));
            return observations.TokenSteps;
        }

        // A single classification traverses the same number of significant tokens and allocates
        // the same size memo in both inputs. Replacing names with openers adds one lookup and
        // one failure write per extra opener, for both a mismatched closer and end of input.
        var flat = ClassifyFailedHead(Rep("x ", nestedOpeners));
        var nested = ClassifyFailedHead(new string('(', nestedOpeners));
        Assert.True(nested - flat >= 2L * nestedOpeners,
            $"Expected at least two additional steps per nested opener, observed {nested - flat} steps for {nestedOpeners} openers.");
    }

    [Theory]
    [InlineData(32)]
    [InlineData(127)]
    public void NestedClauseHeadCandidates_AcrossSiblingRows_TokenStepsStayLinear(int depth)
    {
        // Width control: the same nested row repeated as independent sibling rows. Each row's
        // regions are its own, so the per-token cost must not move with the width either.
        var row = Rep("I(", depth) + "1" + Rep(")", depth);
        long previousSteps = 0;
        foreach (var width in new[] { 1, 2, 4, 8, 16 })
        {
            var source = NestedCandidatePrefix + string.Join("\n", Enumerable.Repeat(row, width));
            var observations = new ParserTraversalObservations();
            var result = Parser.ParseSyntaxObserved(source, observations);
            Assert.Empty(result.Diagnostics);
            var root = Assert.IsType<Algorithm.User>(result.Root);
            Assert.Equal(width, root.Output.Count);
            var firstRow = LeanAstEncoder.EncodeExpr(root.Output[0]);
            Assert.All(root.Output, output => Assert.Equal(firstRow, LeanAstEncoder.EncodeExpr(output)));
            AssertWithinLinearBound($"{width} rows of depth {depth}", observations.TokenSteps, TokenCount(source));
            if (previousSteps > 0)
                Assert.True(observations.TokenSteps <= 2.5 * previousSteps, $"depth {depth}: {previousSteps} -> {observations.TokenSteps} steps at width {width}");
            previousSteps = observations.TokenSteps;
        }

        Assert.False(SourceProvenance.ParseValid(NestedCandidatePrefix + string.Join("\n", Enumerable.Repeat(row, 16))).HasFrontEndErrors);
    }

    [Theory]
    [MemberData(nameof(NestedCandidateShapes))]
    public void NestedClauseHeadCandidates_ReverseQueryOrder_KeepsVerdictsAndTheLinearBound(NestedCandidateShape shape)
    {
        // A parse asks in source order, so the walk of the OUTERMOST candidate decides every
        // region inside it. Asking every token from the last to the first instead makes each
        // walk meet regions an earlier walk already decided — closed ones to skip, broken ones to
        // propagate — which is exactly the reuse the memo must charge and must not get wrong.
        foreach (var depth in AdmittedDepths(shape))
        {
            var source = NestedCandidateSource(shape, depth);
            var tokens = TokenCount(source);
            var indexes = Enumerable.Range(0, tokens).Reverse().ToArray();
            var observations = new ParserTraversalObservations();
            var verdicts = Parser.ClassifyDeclarationStartsInOrder(source, indexes, includeCommaSpanningBindingPatterns: true, observations);
            AssertWithinLinearBound($"{shape} at depth {depth}, reverse order", observations.TokenSteps, tokens);

            for (var i = 0; i < indexes.Length; i++)
            {
                var fresh = Parser.ClassifyDeclarationStartsInOrder(source, [indexes[i]], includeCommaSpanningBindingPatterns: true)[0];
                Assert.Equal(fresh, verdicts[i]);
            }

            // Only `I(x) =` (token 0) and `Good =` begin declarations: no nested candidate is a head.
            var declarations = indexes.Zip(verdicts).Where(pair => pair.Second != Parser.DeclarationStart.None).OrderBy(pair => pair.First).ToArray();
            var expected = shape is NestedCandidateShape.Mismatch or NestedCandidateShape.Unclosed
                ? new[] { Parser.DeclarationStart.ClauseDefinition, Parser.DeclarationStart.PropertyDefinition }
                : [Parser.DeclarationStart.ClauseDefinition];
            Assert.Equal(expected, declarations.Select(pair => pair.Second));
            Assert.Equal(0, declarations[0].First);
        }
    }

    /// <summary>
    /// THE declaration-start relation is a function of the token array: the clause-head region
    /// memo, like the binding-pattern and Grace memos, only shares verdicts. Every token of
    /// curated nested/malformed heads, of single-edit nested chains, and of seeded random
    /// delimiter strings is classified in source order, in reverse, and in a seeded shuffle on
    /// one parser, against a fresh parser per token, in both consumer positions.
    /// </summary>
    [Fact]
    public void ClauseHeadRegionMemo_VerdictsAgreeWithFreshClassification_InEveryQueryOrder()
    {
        var random = new Random(20261119);
        var programs = new List<string>(NestedClauseHeadPins().Select(row => (string)row[0]));
        foreach (var shape in Enum.GetValues<NestedCandidateShape>())
        {
            for (var depth = 1; depth <= 4; depth++)
                programs.Add(NestedCandidateSource(shape, depth));
        }

        // Nested chains with one token inserted, replaced, or deleted at every position, then a
        // follower offering a later `=` or `) =` or a declaration. A region broken inside must
        // break every region around it even when an outer walk meets it already decided
        // (`I(I(1]) = 1` asked inner-first is no head), and a closed one must resume exactly
        // after its own closer.
        string[] heads = ["I(", "I([", "F(x, "];
        string[] edits = ["]", "}", ")", "(", "\n", " = 1", ") = 1", "* = 1"];
        string[] followers = ["", " = 1", "\n) = 1", "\nGood = 41"];
        foreach (var head in heads)
        {
            var close = head == "I([" ? "])" : ")";
            for (var depth = 1; depth <= 3; depth++)
            {
                var parts = Enumerable.Repeat(head, depth).Append("1").Concat(Enumerable.Repeat(close, depth)).ToArray();
                var variants = new List<string>();
                for (var at = 0; at <= parts.Length; at++)
                {
                    foreach (var edit in edits)
                    {
                        variants.Add(string.Concat(parts.Take(at).Append(edit).Concat(parts.Skip(at))));
                        if (at < parts.Length)
                            variants.Add(string.Concat(parts.Take(at).Append(edit).Concat(parts.Skip(at + 1))));
                    }

                    if (at < parts.Length)
                        variants.Add(string.Concat(parts.Take(at).Concat(parts.Skip(at + 1))));
                }

                foreach (var variant in variants)
                {
                    foreach (var follower in followers)
                        programs.Add(variant + follower);
                }
            }
        }

        string[] alphabet = ["I", "F", "x", "(", "(", "(", ")", ")", ")", "[", "]", "{", "}", "=", "=", "*", ",", "1", "\n", " # c\n", "@", "public ", "true", "~", " ", "open "];
        for (var i = 0; i < 3_000; i++)
            programs.Add(string.Concat(Enumerable.Range(0, 3 + random.Next(14)).Select(_ => alphabet[random.Next(alphabet.Length)])));

        var reached = new HashSet<Parser.DeclarationStart>();
        foreach (var program in programs)
        {
            var tokens = TokenCount(program);
            var inOrder = Enumerable.Range(0, tokens).ToArray();
            var shuffled = inOrder.OrderBy(_ => random.Next()).ToArray();
            foreach (var includeComma in new[] { true, false })
            {
                var fresh = inOrder.Select(i => Parser.ClassifyDeclarationStartsInOrder(program, [i], includeComma)[0]).ToArray();
                reached.UnionWith(fresh);
                Assert.Equal(fresh, Parser.ClassifyDeclarationStartsInOrder(program, inOrder, includeComma));
                var reversed = Enumerable.Range(0, tokens).Reverse().ToArray();
                Assert.Equal(reversed.Select(i => fresh[i]), Parser.ClassifyDeclarationStartsInOrder(program, reversed, includeComma));
                var shuffledVerdicts = Parser.ClassifyDeclarationStartsInOrder(program, shuffled, includeComma);
                Assert.Equal(shuffled.Select(i => fresh[i]), shuffledVerdicts);
            }
        }

        // Non-vacuous: the corpus reaches every clause-head-dependent verdict.
        Assert.Contains(Parser.DeclarationStart.ClauseDefinition, reached);
        Assert.Contains(Parser.DeclarationStart.PublicClauseDefinition, reached);
        Assert.Contains(Parser.DeclarationStart.ReservedLiteralHead, reached);
    }

    /// <summary>
    /// Behavioral anchors of the clause-head confinement law (`syntax.md` § Line rules and
    /// declaration heads, CLAUSE-HEAD CONFINEMENT) around nested candidates — mismatched and
    /// unclosed regions with a following declaration, genuine clause definitions, the
    /// name/`(` and `)`/`=` line rules, comments and reported characters, and the
    /// output-spreading marker. Every expectation is the pre-change parser's (810049ee): raw
    /// diagnostic codes and spans in order, the root's properties, and its output count;
    /// the elaborated front end reports the same diagnostics.
    /// </summary>
    public static TheoryData<string, string, string, int> NestedClauseHeadPins() => new()
    {
        // Malformed regions: a candidate followed by a valid declaration keeps the declaration.
        { "I(x) = x\nI(I(I(1])))\nGood = 41\nGood", "UnexpectedToken [2:8, 2:9) | UnexpectedToken [2:11, 2:12)", "Good,I", 2 },
        { "I(x) = x\nI(I(I(1)}))\nGood = 41\nGood", "UnexpectedToken [2:9, 2:10) | UnexpectedToken [2:11, 2:12)", "Good,I", 2 },
        { "I(x) = x\nI(I(I([1)])))\nGood = 41\nGood", "UnexpectedToken [2:9, 2:10) | UnexpectedToken [2:10, 2:11) | UnexpectedToken [2:12, 2:13) | UnexpectedToken [2:13, 2:14)", "Good,I", 2 },
        { "I(x) = x\nI(I(I(1))))\nGood = 41\nGood", "UnexpectedToken [2:11, 2:12)", "Good,I", 2 },
        { "I(x) = x\nI(I(I(1))\nGood = 41\nGood", "DeclarationInParentheses [3:1, 3:5) | UnexpectedToken [4:5]", "I", 1 },
        // A scan never crosses a mismatch to a later `) =`: no `F` head steals `Good`.
        { "F(I(I(]\nGood = 41\n))) = 1\nGood", "UnexpectedToken [1:7, 1:8) | DeclarationInParentheses [2:1, 2:5) | UnexpectedToken [3:3, 3:4) | UnexpectedToken [3:5, 3:6)", "", 4 },
        { "F(I(]\nGood = 41\n) = 1\nGood", "UnexpectedToken [1:5, 1:6) | DeclarationInParentheses [2:1, 2:5) | UnexpectedToken [3:3, 3:4)", "", 4 },
        { "F(I([1)]\nGood = 41\n) = 1\nGood", "UnexpectedToken [1:7, 1:8) | UnexpectedToken [1:8, 1:9) | UnexpectedToken [3:1, 3:2) | UnexpectedToken [3:3, 3:4)", "Good", 4 },
        { "I(x) = x\nF(I({]\nGood = 41\n}) = 1\nGood", "UnexpectedToken [2:6, 2:7) | DeclarationInParentheses [3:1, 3:5) | UnexpectedToken [4:1, 4:2) | UnexpectedToken [4:4, 4:5)", "I", 4 },
        { "I(x) = x\nI(F(I(]\nGood = 41\n) = 1)\nGood", "UnexpectedToken [2:7, 2:8) | DeclarationInParentheses [3:1, 3:5) | UnexpectedToken [4:3, 4:4)", "I", 2 },
        // Genuine heads: inside an argument list (decided by the enclosing walk), with a call
        // pattern (recovered head), after a reserved literal, and clean nested list patterns.
        { "I(x) = x\nI(F(x) = x)\nGood = 41\nGood", "DeclarationInParentheses [2:3, 2:4)", "Good,I", 2 },
        { "I(x) = x\nI(I(I(1))) = 2\nGood = 41\nGood", "UnseparatedSameLineItem [2:4, 2:5) | UnseparatedSameLineItem [2:6, 2:7) | SingletonSequencePattern [2:6, 2:9)", "Good,I", 1 },
        { "I(x) = x\nF(a) = a\nF(I(I(1))) = 2\nGood = 41\nGood", "UnseparatedSameLineItem [3:4, 3:5) | UnseparatedSameLineItem [3:6, 3:7) | SingletonSequencePattern [3:6, 3:9)", "Good,I,F", 1 },
        { "I(x) = x\ntrue(I(I(1))) = 2\nGood = 41\nGood", "UnexpectedToken [2:1, 2:5)", "Good,I", 2 },
        { "I(x) = x\nF(a) = I(I(I(a)))\nF(I(I(1)))", "", "I,F", 1 },
        { "F([a,\n[b, c]]) = a + b + c\nF([1, [2, 3]])", "", "F", 1 },
        { "public F([a, [b]]) = a\nF([1, [2]])", "", "F", 1 },
        // Line rules: `)` and `=` share a line; the name and `(` share a line; the list inside may span lines.
        { "I(x) = x\nI(I(I(1)))\n= 2\nGood = 41\nGood", "UnexpectedToken [3:1, 3:2)", "Good,I", 4 },
        { "I(x) = x\nI\n(I(I(1)))\nGood = 41\nGood", "", "Good,I", 3 },
        { "I(x) = x\nI # c\n(I(I(1)))\nGood = 41\nGood", "", "Good,I", 3 },
        { "I(x) = x\nF(I(I(1))\n) = 1\nGood = 41\nGood", "UnseparatedSameLineItem [2:4, 2:5) | UnseparatedSameLineItem [2:6, 2:7) | SingletonSequencePattern [2:6, 2:9)", "Good,I,F", 1 },
        { "F([a, [b]]) # note\n= a\nGood = 41\nGood", "UnexpectedToken [2:1, 2:2)", "Good", 4 },
        // The output-spreading marker between the head's `)` and `=`, and the postfix star of an output row.
        { "G([a, [b]])* = a, b\nG([1, [2]])", "", "G", 1 },
        { "I(x) = x\nI(I(I(1)))* = 2\nGood = 41\nGood", "UnseparatedSameLineItem [2:4, 2:5) | UnseparatedSameLineItem [2:6, 2:7) | SingletonSequencePattern [2:6, 2:9) | MixedOutputSpreadMarkers [2:1, 2:16)", "Good,I", 1 },
        { "I(x) = x\nI(I(I(1)))*", "", "I", 1 },
        { "I(x) = x\nI(I(I(1))) * 2", "", "I", 1 },
        // Comments and reported characters are invisible to the scan.
        { "I(x) = x\nI(# c\nI(@I(1)))", "UnexpectedCharacter [3:3, 3:4)", "I", 1 },
        { "I(x) = x\nI(I(I(1)))\nI(I(I(1)))\nGood = 41\nGood", "", "Good,I", 3 },
    };

    [Theory]
    [MemberData(nameof(NestedClauseHeadPins))]
    public void NestedClauseHeadCandidates_KeepTheirDiagnosticsAndDeclarations(
        string source, string expectedDiagnostics, string expectedProperties, int expectedOutputCount)
    {
        var raw = Parser.ParseSyntax(source);
        Assert.Equal(expectedDiagnostics, string.Join(" | ", raw.Diagnostics.Select(d => $"{d.Code} {d.Span}")));
        var root = Assert.IsType<Algorithm.User>(raw.Root);
        Assert.Equal(expectedProperties, string.Join(",", root.Properties.Select(p => p.Name)));
        Assert.Equal(expectedOutputCount, root.Output.Count);

        var observations = new ParserTraversalObservations();
        var observed = Parser.ParseSyntaxObserved(source, observations);
        Assert.Equal(raw.Diagnostics.Select(d => (d.Code, d.Span, d.Message)), observed.Diagnostics.Select(d => (d.Code, d.Span, d.Message)));
        Assert.Equal(LeanAstEncoder.EncodeProgram(raw.Root), LeanAstEncoder.EncodeProgram(observed.Root));
        AssertWithinLinearBound(source, observations.TokenSteps, TokenCount(source));

        var elaborated = Parser.Parse(source);
        Assert.Equal(raw.Diagnostics.Select(d => (d.Code, d.Span, d.Message)), elaborated.Diagnostics.Select(d => (d.Code, d.Span, d.Message)));
        if (expectedDiagnostics.Length == 0)
            Assert.False(SourceProvenance.ParseValid(source).HasFrontEndErrors);
    }

    [Theory]
    [InlineData(1)]
    [InlineData(4)]
    [InlineData(32)]
    [InlineData(54)]
    public void NestedClauseHeadCandidates_ValidSpellingsElaborateToOneTree(int depth)
    {
        // Redundant groups, comments and line breaks inside open parentheses, and a reported
        // character change nothing: every spelling elaborates to the plain call chain.
        var expected = LeanAstEncoder.EncodeProgram(SourceProvenance.ParseValid(NestedCandidateSource(NestedCandidateShape.Call, depth)).Root);
        Assert.Equal(expected, LeanAstEncoder.EncodeProgram(SourceProvenance.ParseValid(NestedCandidateSource(NestedCandidateShape.Group, depth)).Root));
        Assert.Equal(expected, LeanAstEncoder.EncodeProgram(SourceProvenance.ParseValid(NestedCandidateSource(NestedCandidateShape.CommentedLines, depth)).Root));

        var reported = SourceProvenance.ParseAllowingDiagnostics(NestedCandidatePrefix + Rep("I(@", depth) + "1" + Rep(")", depth));
        Assert.Equal(Enumerable.Repeat(DiagnosticCode.UnexpectedCharacter, depth), reported.Diagnostics.Select(d => d.Code));
        Assert.Equal(expected, LeanAstEncoder.EncodeProgram(reported.Root));
    }

    // ── Surface parser never emits the internal SequenceConstruct node ────────
    [Theory]
    [InlineData("((((1))))")]
    [InlineData("[[[[1]]]]")]
    [InlineData("((((1")]            // malformed (unclosed)
    public void NoSequenceConstruct_ShallowAndMalformed(string source)
        => Assert.False(FindsSequenceConstruct(SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot(source)));

    [Fact]
    public void NoSequenceConstruct_OverBudgetPlaceholder()
        => Assert.False(FindsSequenceConstruct(
            SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot(Rep("(", 5000) + "1" + Rep(")", 5000))));

    private static bool FindsSequenceConstruct(Algorithm root)
    {
        var detector = new SequenceConstructDetector();
        detector.VisitAlgorithm(root);
        return detector.Found;
    }

    private sealed class SequenceConstructDetector : AstWalker
    {
        public bool Found { get; private set; }

        public override void VisitExpr(Expr expr)
        {
            if (expr is Expr.SequenceConstruct)
                Found = true;
            base.VisitExpr(expr);
        }
    }
}
