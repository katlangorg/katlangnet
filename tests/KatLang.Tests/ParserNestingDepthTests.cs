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
        // (EnterHeavyNesting(CallArgsNestingSurcharge + BlockNestingSurcharge)
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
        AssertParses("F" + Rep("(", 384) + "x" + Rep(")", 384) + " = x\nF(1)");
        Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(
            "F" + Rep("(", 385) + "x" + Rep(")", 385) + " = x\nF(1)")));
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
        Assert.True(diagnostic.Span.StartLineNumber >= 1);
        Assert.True(diagnostic.Span.StartColumn >= 1);
        Assert.True(diagnostic.Span.EndLineNumber >= diagnostic.Span.StartLineNumber);
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
                    Assert.Equal(new SourceSpan(1, 3, 1, k + 2), diagnostic.Span);
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
                    Assert.Equal(new SourceSpan(1, 10, 1, k + 9), diagnostic.Span);
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
                    Assert.Equal(new SourceSpan(1, 1, 1, k), diagnostic.Span);
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
            case GraceRunShape.PrefixRunInGroup:
                {
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
        // containing Grace is already unwrapped by the raw parser.
        var expectedSource = shape switch
        {
            GraceRunShape.PostfixRunAtRoot => "1 x",
            GraceRunShape.PostfixRunInDefinitionBody => "F(x) = 1 x\nF(2)",
            GraceRunShape.PrefixRunBeforeDeclaration => "0\nx = 1\nx",
            GraceRunShape.PrefixRunOnRootName or GraceRunShape.PrefixRunInGroup => "x",
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        };
        Assert.Equal(
            LeanAstEncoder.EncodeProgram(SourceProvenance.ParseValid(expectedSource).Root),
            LeanAstEncoder.EncodeProgram(elaborated.Root));
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
