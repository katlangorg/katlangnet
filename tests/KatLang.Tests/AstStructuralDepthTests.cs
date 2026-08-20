using System.Diagnostics;

namespace KatLang.Tests;

/// <summary>
/// Regression coverage for the non-recursive structural AST safety preflight.
/// Public callers can construct KatLang AST objects directly, bypassing the parser's
/// nesting budgets; before this guard, a deep host-built tree terminated the whole
/// process with a <see cref="StackOverflowException"/> inside the recursive validation
/// walker or the evaluator. These tests pin the depth definition, the boundary, the
/// error protocol, cycle/DAG handling, every evaluator entry point, and the
/// parser-front-end composition gate. The extreme depths that cannot be demonstrated
/// safely in-process run in <see cref="AstStructuralDepthProcessTests"/>.
/// </summary>
public class AstStructuralDepthTests
{
    // ── Iterative deep-tree builders (the builders themselves must never recurse) ──

    internal static Expr UnarySpine(int totalNodes, IReadOnlyList<SourceSpan?>? spans = null)
    {
        // Node 0 is the root; the leaf Num is node totalNodes - 1.
        Expr expr = new Expr.Num(1) { Span = spans?[totalNodes - 1] };
        for (var index = totalNodes - 2; index >= 0; index--)
            expr = new Expr.Unary(UnaryOp.Minus, expr) { Span = spans?[index] };
        return expr;
    }

    internal static Expr BinarySpine(int totalNodes, bool leftDeep)
    {
        Expr expr = new Expr.Num(1);
        for (var i = 0; i < totalNodes - 1; i++)
            expr = leftDeep
                ? new Expr.Binary(BinaryOp.Add, expr, new Expr.Num(1))
                : new Expr.Binary(BinaryOp.Add, new Expr.Num(1), expr);
        return expr;
    }

    internal static Expr ListSpine(int totalNodes)
    {
        Expr expr = new Expr.Num(1);
        for (var i = 0; i < totalNodes - 1; i++)
            expr = new Expr.ListLiteral([expr]);
        return expr;
    }

    /// <summary>Block(User { Output = [inner] }) nesting: 2 counted nodes per level plus the leaf.</summary>
    internal static Expr BlockSpine(int levels, Expr? leaf = null)
    {
        Expr expr = leaf ?? new Expr.Num(1);
        for (var i = 0; i < levels; i++)
            expr = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [expr]));
        return expr;
    }

    /// <summary>Call(Resolve, [inner]) nesting around a defined F (a Call node weighs two units — it absorbed its former transparent Args wrapper).</summary>
    internal static Expr CallSpine(int levels, Expr? leaf = null)
    {
        Expr expr = leaf ?? new Expr.Num(1);
        for (var i = 0; i < levels; i++)
            expr = new Expr.Call(new Expr.Resolve("F"), [expr]);

        var definition = Algorithm.ElaborateClauseDefinition(
            new Pattern.Bind("x"),
            new Algorithm.User(null, [], [], [], [new Expr.Param("x")]));
        return new Expr.AlgorithmExpr(new Algorithm.User(
            null, [], [], [new Property("F", definition)], [expr]));
    }

    /// <summary>Conditional whose branch pattern is a nested sequence-value pattern spine.</summary>
    internal static Expr PatternSpine(int patternNodes)
    {
        Pattern pattern = new Pattern.Bind("x");
        for (var i = 0; i < patternNodes - 1; i++)
            pattern = new Pattern.SequenceValue([pattern]);

        var conditional = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches: [new CondBranch(pattern, new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))]);
        return new Expr.AlgorithmExpr(new Algorithm.User(
            null, [], [], [new Property("F", conditional)], [new Expr.Num(1)]));
    }

    /// <summary>
    /// User algorithm whose parameter pattern is a nested sequence-value parameter
    /// pattern spine. Assigned through the raw record initializer so the builder
    /// itself stays O(1) per level: the convenience helper
    /// <see cref="Algorithm.WithParameterPatterns"/> eagerly flattens captures
    /// through <see cref="ParameterPattern.Captures"/> (iterative, but a full O(n)
    /// flatten per call), which is a construction-time helper outside the
    /// preflight's reach.
    /// </summary>
    internal static Expr ParameterPatternSpine(int patternNodes)
    {
        ParameterPattern pattern = new CaptureParameterPattern("x");
        for (var i = 0; i < patternNodes - 1; i++)
            pattern = new SequenceValueParameterPattern([pattern]);

        var algorithm = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]) with
        {
            ParameterPatterns = [pattern],
        };
        return new Expr.AlgorithmExpr(new Algorithm.User(
            null, [], [], [new Property("F", algorithm)], [new Expr.Num(1)]));
    }

    /// <summary>Algorithm wired to a host-built ScopeCtx parent chain.</summary>
    internal static Expr ScopeChainProgram(int scopeNodes)
    {
        ScopeCtx? scope = null;
        for (var i = 0; i < scopeNodes; i++)
            scope = new ScopeCtx(scope, [], []);
        return new Expr.AlgorithmExpr(new Algorithm.User(scope, [], [], [], [new Expr.Num(1)]));
    }

    private static EvalError AssertRejected(Expr expr, EvaluationLimits? limits = null)
    {
        var result = Evaluator.Run(expr, limits);
        Assert.True(result.IsError);
        return result.Error;
    }

    private static EvalError.AstDepthLimitExceeded AssertDepthRejected(Expr expr, EvaluationLimits? limits = null)
        => Assert.IsType<EvalError.AstDepthLimitExceeded>(AssertRejected(expr, limits));

    private static void AssertAccepted(Expr expr, EvaluationLimits? limits = null)
    {
        var result = Evaluator.Run(expr, limits);
        if (result.IsError)
        {
            Assert.IsNotType<EvalError.AstDepthLimitExceeded>(result.Error);
            Assert.IsNotType<EvalError.AstCycleDetected>(result.Error);
        }
    }

    // ── Depth definition and root counting ─────────────────────────────────────

    [Fact]
    public void DepthCounting_RootAloneIsDepthOne()
    {
        var limits = new EvaluationLimits { MaxAstDepth = 1 };
        var single = Evaluator.Run(new Expr.Num(7), limits);
        Assert.False(single.IsError);

        var two = AssertDepthRejected(UnarySpine(2), limits);
        Assert.Equal(1, two.Limit);
    }

    [Fact]
    public void DepthCounting_UnarySpineBoundaryIsExact()
    {
        var limits = new EvaluationLimits { MaxAstDepth = 40 };
        AssertAccepted(UnarySpine(40), limits);
        Assert.Equal(40, AssertDepthRejected(UnarySpine(41), limits).Limit);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void DepthCounting_BinarySpineBoundaryIsExact(bool leftDeep)
    {
        var limits = new EvaluationLimits { MaxAstDepth = 40 };
        AssertAccepted(BinarySpine(40, leftDeep), limits);
        AssertDepthRejected(BinarySpine(41, leftDeep), limits);
    }

    [Fact]
    public void DepthCounting_BlockAlgorithmNesting_CountsTwoNodesPerLevel()
    {
        // Each level contributes Expr.AlgorithmExpr + Algorithm.User; the leaf Num adds one.
        var limits = new EvaluationLimits { MaxAstDepth = 41 };
        AssertAccepted(BlockSpine(20), limits);
        AssertDepthRejected(BlockSpine(21), limits);
    }

    [Fact]
    public void DepthCounting_PatternAndParameterPatternNodes_AreCounted()
    {
        var limits = new EvaluationLimits { MaxAstDepth = 40 };
        AssertDepthRejected(PatternSpine(60), limits);
        AssertDepthRejected(ParameterPatternSpine(60), limits);
        AssertAccepted(PatternSpine(10), limits);
        AssertAccepted(ParameterPatternSpine(10), limits);
    }

    [Fact]
    public void DepthCounting_HostScopeContextChain_IsCounted()
    {
        AssertDepthRejected(ScopeChainProgram(EvaluationLimits.MaxSupportedAstDepth + 10));
        AssertAccepted(ScopeChainProgram(10));
    }

    // ── The hard ceiling ────────────────────────────────────────────────────────

    [Fact]
    public void HardCeiling_AtLimitEvaluates_OneBeyondIsRejected()
    {
        // The exact ceiling boundary: a tree at the maximum accepted depth EVALUATES
        // (the pure-expression spine shapes are machine-driven, so at-limit
        // evaluation is deterministic, not a machine stack property), and the same
        // shape one node deeper is rejected with the structured error.
        var atLimitUnary = Evaluator.Run(UnarySpine(EvaluationLimits.MaxSupportedAstDepth));
        Assert.False(atLimitUnary.IsError);
        var atLimitList = Evaluator.Run(ListSpine(EvaluationLimits.MaxSupportedAstDepth));
        Assert.False(atLimitList.IsError);

        var beyond = AssertDepthRejected(ListSpine(EvaluationLimits.MaxSupportedAstDepth + 1));
        Assert.Equal(EvaluationLimits.MaxSupportedAstDepth, beyond.Limit);
        AssertDepthRejected(UnarySpine(EvaluationLimits.MaxSupportedAstDepth + 1));
    }

    [Fact]
    public void IterativeSpines_EvaluateExactValuesAtTheCeiling()
    {
        var max = EvaluationLimits.MaxSupportedAstDepth;

        // Unary spine: (max - 1) negations of 1.
        var unary = Evaluator.RunFlat(UnarySpine(max));
        Assert.False(unary.IsError);
        Assert.Equal((max - 1) % 2 == 0 ? 1m : -1m, Assert.Single(unary.Value));

        // Left- and right-associated binary spines of +1s: value == leaf count == depth.
        var left = Evaluator.RunFlat(BinarySpine(max, leftDeep: true));
        Assert.False(left.IsError);
        Assert.Equal(max, Assert.Single(left.Value));
        var right = Evaluator.RunFlat(BinarySpine(max, leftDeep: false));
        Assert.False(right.IsError);
        Assert.Equal(max, Assert.Single(right.Value));

        // Index spine over a scalar: every projection re-selects the scalar itself.
        Expr indexSpine = new Expr.Num(1);
        for (var i = 0; i < max - 1; i++)
            indexSpine = new Expr.Index(indexSpine, new Expr.Num(0));
        var index = Evaluator.RunFlat(indexSpine);
        Assert.False(index.IsError);
        Assert.Equal(1m, Assert.Single(index.Value));

        // List spine: host-boundary flattening opens every nesting level.
        var list = Evaluator.RunFlat(ListSpine(max));
        Assert.False(list.IsError);
        Assert.Equal(1m, Assert.Single(list.Value));
    }

    [Fact]
    public void IterativeSpines_PreserveErrorShapesAndSpans()
    {
        // Machine-driven paths must decorate errors exactly like the recursive code:
        // an index expression attaches its span to child and coercion errors, while
        // unary/binary/list propagate child errors untouched.
        var indexSpan = new SourceSpan(3, 1, 3, 9);
        var badSelector = new Expr.Index(new Expr.Num(1), new Expr.StringLiteral("x")) { Span = indexSpan };
        var badSelectorR = Evaluator.Run(badSelector);
        Assert.True(badSelectorR.IsError);
        Assert.IsType<EvalError.TypeMismatch>(badSelectorR.Error);
        Assert.Equal(indexSpan, badSelectorR.Error.Span);

        var badIndex = new Expr.Index(new Expr.EmptySequence(0), new Expr.Num(5)) { Span = indexSpan };
        var badIndexR = Evaluator.Run(badIndex);
        Assert.True(badIndexR.IsError);
        Assert.IsType<EvalError.BadIndex>(badIndexR.Error);
        Assert.Equal(indexSpan, badIndexR.Error.Span);

        var unarySpan = new SourceSpan(7, 2, 7, 4);
        var unaryOnString = new Expr.Unary(UnaryOp.Minus, new Expr.StringLiteral("s")) { Span = unarySpan };
        var unaryR = Evaluator.Run(unaryOnString);
        Assert.True(unaryR.IsError);
        Assert.IsType<EvalError.TypeMismatch>(unaryR.Error);
        Assert.Equal(unarySpan, unaryR.Error.Span);

        // A failing operand inside a spine keeps ITS error and innermost span; the
        // enclosing binary adds nothing.
        var innerSpan = new SourceSpan(9, 5, 9, 6);
        var failingOperand = new Expr.Resolve("noSuchName") { Span = innerSpan };
        var nested = new Expr.Binary(
            BinaryOp.Add,
            new Expr.Unary(UnaryOp.Minus, failingOperand),
            new Expr.Num(1));
        var nestedR = Evaluator.Run(nested);
        Assert.True(nestedR.IsError);
        Assert.IsType<EvalError.UnknownName>(nestedR.Error);
        Assert.Equal(innerSpan, nestedR.Error.Span);
    }

    [Fact]
    public void DotCallLinks_WeighThreeUnits_OnTheEvaluationGate()
    {
        // Each dot-call link consumes several evaluator frames (pipeline planning,
        // algorithm resolution, lexical receiver-injection fallback), so a link costs
        // 3 depth units: 99 links (3*99 + 1 = 298) evaluate, and 100 links
        // (3*100 + 1 = 301) are structurally rejected — well below the measured
        // ~160-link (Debug) / ~250-link (Release) crash boundary of that machinery.
        Expr accepted = new Expr.Num(1);
        for (var i = 0; i < 99; i++)
            accepted = new Expr.DotCall(accepted, "count", null);
        var acceptedR = Evaluator.RunFlat(accepted);
        Assert.False(acceptedR.IsError);
        Assert.Equal(1m, Assert.Single(acceptedR.Value));

        Expr rejected = new Expr.Num(1);
        for (var i = 0; i < 100; i++)
            rejected = new Expr.DotCall(rejected, "count", null);
        var error = AssertDepthRejected(rejected);
        Assert.Equal(EvaluationLimits.MaxSupportedAstDepth, error.Limit);
    }

    [Theory]
    [InlineData(1_000)]
    [InlineData(100_000)]
    public void HardCeiling_DeepSpines_AreRejectedWithoutCrashing(int nodes)
    {
        AssertDepthRejected(UnarySpine(nodes));
        AssertDepthRejected(BinarySpine(nodes, leftDeep: true));
        AssertDepthRejected(BinarySpine(nodes, leftDeep: false));
        AssertDepthRejected(ListSpine(nodes));
        AssertDepthRejected(BlockSpine(nodes / 2));
        AssertDepthRejected(CallSpine(nodes / 2));
        AssertDepthRejected(PatternSpine(nodes));
        AssertDepthRejected(ParameterPatternSpine(nodes));
    }

    [Fact]
    public void Configuration_AboveCeilingIsClampedDown_NeverRaised()
    {
        var raised = new EvaluationLimits { MaxAstDepth = 1_000_000 };
        var error = AssertDepthRejected(UnarySpine(EvaluationLimits.MaxSupportedAstDepth + 1), raised);
        Assert.Equal(EvaluationLimits.MaxSupportedAstDepth, error.Limit);
    }

    [Fact]
    public void Configuration_LoweredLimit_IsEnforcedAndReported()
    {
        var limits = new EvaluationLimits { MaxAstDepth = 10 };
        AssertAccepted(UnarySpine(10), limits);
        Assert.Equal(10, AssertDepthRejected(UnarySpine(11), limits).Limit);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(-5)]
    public void Configuration_NonPositiveValues_AreRejected(int value)
        => Assert.Throws<ArgumentOutOfRangeException>(() => new EvaluationLimits { MaxAstDepth = value });

    // ── Error protocol ──────────────────────────────────────────────────────────

    [Fact]
    public void Rejection_IsDeterministic_AndCarriesTheCrossingNodeSpan()
    {
        var limits = new EvaluationLimits { MaxAstDepth = 25 };
        var spans = Enumerable.Range(0, 40)
            .Select(i => (SourceSpan?)new SourceSpan(1, i + 1, 1, i + 1))
            .ToList();
        var expr = UnarySpine(40, spans);

        for (var repeat = 0; repeat < 3; repeat++)
        {
            var error = AssertDepthRejected(expr, limits);
            Assert.Equal(25, error.Limit);
            // The crossing node is the 26th on the spine (index 25): the first node
            // whose path no longer fits the limit, under the fixed traversal order.
            Assert.Equal(spans[25], error.Span);
        }
    }

    [Fact]
    public void Rejection_MessageDistinguishesStructuralDepthFromRuntimeRecursion()
    {
        var error = AssertDepthRejected(UnarySpine(10_000));
        var message = KatLangError.FromEvalError(error).Message;
        Assert.Contains(
            $"Structural AST depth limit of {EvaluationLimits.MaxSupportedAstDepth}",
            message,
            StringComparison.Ordinal);
        Assert.Contains("separate from the runtime recursion limit", message, StringComparison.Ordinal);
        Assert.DoesNotContain("Expr.", message, StringComparison.Ordinal); // never renders the tree
    }

    [Fact]
    public void Rejection_TooDeepAndOtherwiseMalformed_FailsWithTheStructuralError()
    {
        // Explicit parameters with no output is a validation error found by the
        // recursive walker; the structural preflight must win without the walker (or
        // any diagnostic formatting) ever touching the unsafe subtree.
        var malformed = new Expr.AlgorithmExpr(new Algorithm.User(
            null,
            [new ParameterDeclaration("x")],
            [],
            [new Property("Deep", new Algorithm.User(null, [], [], [], [UnarySpine(10_000)]))],
            []));

        for (var repeat = 0; repeat < 3; repeat++)
            AssertDepthRejected(malformed);
    }

    [Fact]
    public void Validation_BelowTheStructuralLimit_IsUnchanged()
    {
        var violating = new Expr.AlgorithmExpr(new Algorithm.User(
            null, [new ParameterDeclaration("x")], [], [], []));
        var error = AssertRejected(violating);
        Assert.IsType<EvalError.ExplicitParametersRequireOutput>(error);
    }

    // ── Runtime MaxDepth stays a distinct, unchanged mechanism ─────────────────

    [Fact]
    public void RuntimeRecursion_StillGovernedByMaxDepth_NotByTheStructuralPreflight()
    {
        const string source = "F(0) = 0\nF(n) = F(n - 1)\nF(1000)";
        var parse = Parser.Parse(source);
        Assert.False(parse.HasErrors);

        var result = Evaluator.RunCounted(new Expr.AlgorithmExpr(parse.Root) { Span = null });
        Assert.True(result.IsError);
        var depthError = Assert.IsType<EvalError.EvaluationDepthExceeded>(FindLeaf(result.Error));
        Assert.Equal(EvaluationLimits.MaxSupportedDepth, depthError.Limit);

        var lowered = Evaluator.RunCounted(
            new Expr.AlgorithmExpr(parse.Root),
            new Evaluation.Caching.RunScopedZeroArgPropertyResultCache(),
            new EvaluationLimits { MaxDepth = 5 });
        Assert.True(lowered.IsError);
        Assert.Equal(5, Assert.IsType<EvalError.EvaluationDepthExceeded>(FindLeaf(lowered.Error)).Limit);
    }

    private static EvalError FindLeaf(EvalError error)
    {
        while (error is EvalError.WithContext(_, var inner))
            error = inner;
        return error;
    }

    // ── Breadth is not depth ────────────────────────────────────────────────────

    [Fact]
    public void WideButShallowTrees_AreAcceptedAndEvaluate()
    {
        var wide = new Expr.ListLiteral(
            Enumerable.Range(0, 50_000).Select(i => (Expr)new Expr.Num(i)).ToList());
        var result = Evaluator.Run(wide);
        Assert.False(result.IsError);
    }

    // ── Internal sequence-join spines stay iteratively consumable ──────────────

    internal static Expr SequenceConstructChain(int joinCount)
    {
        Expr expr = new Expr.Num(1);
        for (var i = 0; i < joinCount; i++)
            expr = new Expr.SequenceConstruct(expr, new Expr.Num(1));
        return expr;
    }

    [Fact]
    public void InternalJoinChains_RemainAcceptedAtAnyLengthOnEvaluatorEntryPoints()
    {
        // Deep chains of the INTERNAL sequence-join nodes are a supported host shape:
        // the validation walker and both evaluation modes walk them with explicit
        // iterative stacks (pinned by
        // Eval_SequenceSpread_LongChain_IsStackSafeForFlatAndCountedEvaluation), so
        // the preflight's evaluator profile charges them no depth.
        var spread = new Expr.SequenceSpread(SequenceConstructChain(50_000));
        var flat = Evaluator.RunFlat(spread);
        Assert.False(flat.IsError);
        Assert.Equal(50_001, flat.Value.Count);

        // Chained spread spines are equally free.
        Expr chained = new Expr.Num(7);
        for (var i = 0; i < 10_000; i++)
            chained = new Expr.SequenceSpread(chained);
        var chainedResult = Evaluator.Run(chained);
        Assert.False(chainedResult.IsError);
    }

    [Fact]
    public void AlternatingJoinAndCountedNodes_StillAccumulateDepth()
    {
        // The join exemption must not smuggle ordinary nodes past the limit: every
        // alternation with a counted node kind is one level, exactly matching how the
        // iterative spine walks re-enter recursive dispatch at each non-join node.
        Expr alternating = new Expr.Num(1);
        for (var i = 0; i < EvaluationLimits.MaxSupportedAstDepth + 60; i++)
        {
            alternating = new Expr.SequenceConstruct(alternating, new Expr.Num(1));
            alternating = new Expr.Unary(UnaryOp.Minus, alternating);
        }

        var rejection = AstStructuralPreflight.Check(
            alternating,
            EvaluationLimits.MaxSupportedAstDepth,
            AstConsumerProfile.EvaluatorIterativeJoinSpines);
        Assert.NotNull(rejection);
        Assert.Equal(AstStructuralViolation.DepthExceeded, rejection.Kind);
    }

    [Fact]
    public void InternalJoinChains_CountFully_OnTheSemanticModelGate()
    {
        // Semantic modeling recurses through the BASE walker dispatch for every node
        // kind, so its gate counts join nodes like any other node.
        var deepJoinRoot = new Algorithm.User(
            null, [], [], [], [SequenceConstructChain(50_000)]);
        Assert.Throws<ArgumentException>(() => Semantics.SemanticModelBuilder.Build(deepJoinRoot));
    }

    // ── Public pattern conveniences stay host-safe ──────────────────────────────

    [Fact]
    public void ParameterPatternCaptures_IsIterative_AndPreservesOrderAndDuplicates()
    {
        // Order and duplicate-name behavior are unchanged from the recursive flatten:
        // left-to-right depth-first, duplicates preserved, kinds and spans carried.
        var span = new SourceSpan(1, 2, 1, 3);
        var mixed = new SequenceValueParameterPattern(
        [
            new CaptureParameterPattern("a"),
            new SequenceValueParameterPattern(
            [
                new CaptureParameterPattern("b", span),
                new CaptureParameterPattern("c", null, ParameterKind.Collecting),
            ]),
            new CaptureParameterPattern("a"),
        ]);

        var captures = mixed.Captures;
        Assert.Equal(new[] { "a", "b", "c", "a" }, captures.Select(c => c.Name));
        Assert.Equal(span, captures[1].Span);
        Assert.Equal(ParameterKind.Collecting, captures[2].Kind);
        Assert.True(mixed.ContainsCollectingCapture);

        // A deep host-built pattern must not overflow the caller's stack: this exact
        // access crashed the process before the iterative flatten.
        ParameterPattern deep = new CaptureParameterPattern("x");
        for (var i = 0; i < 200_000; i++)
            deep = new SequenceValueParameterPattern([deep]);
        var deepCaptures = deep.Captures;
        Assert.Equal("x", Assert.Single(deepCaptures).Name);

        Assert.False(ParameterPattern.HasMultipleCollectingCapturesAtAnyLevel([deep]));
        var doubleCollecting = new SequenceValueParameterPattern(
        [
            new CaptureParameterPattern("p", null, ParameterKind.Collecting),
            new CaptureParameterPattern("q", null, ParameterKind.Collecting),
        ]);
        Assert.True(ParameterPattern.HasMultipleCollectingCapturesAtAnyLevel([doubleCollecting]));
    }

    [Fact]
    public void PatternBoundNames_IsIterative_AndPreservesOrder()
    {
        Pattern deep = new Pattern.Bind("leaf");
        for (var i = 0; i < 200_000; i++)
            deep = new Pattern.SequenceValue([deep]);
        Assert.Equal("leaf", Assert.Single(deep.BoundNames()));

        var mixed = new Pattern.SequenceValue(
        [
            new Pattern.Bind("a"),
            new Pattern.LitInt(1),
            new Pattern.SequenceValue([new Pattern.Bind("b"), new Pattern.Bind("a")]),
        ]);
        Assert.Equal(new[] { "a", "b", "a" }, mixed.BoundNames());
    }

    // ── Front-end gate is larger than the evaluation gate ───────────────────────

    [Fact]
    public void ParserCapacityShapes_ParseRawly_AndFailElaborationStructurally()
    {
        // The parser's cumulative recursion budget admits RAW paths up to ~385 nodes
        // (e.g. 350 prefix operators); the raw-syntax gate (640) keeps them parsing,
        // while front-end ELABORATION — whose rebuilding passes use evaluation-class
        // frames — rejects anything beyond the evaluation ceiling with one structured
        // diagnostic instead of walking it at machine-dependent stack risk.
        var source = string.Concat(Enumerable.Repeat("-", 350)) + "1";
        var raw = Parser.ParseSyntax(source);
        Assert.False(raw.HasErrors);

        var elaborated = Parser.Parse(source);
        Assert.True(elaborated.HasErrors);
        Assert.Contains(
            elaborated.Diagnostics,
            d => d.Message.Contains(
                $"structural AST depth limit of {EvaluationLimits.MaxSupportedAstDepth}",
                StringComparison.Ordinal));

        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
    }

    // ── Shared DAGs and cycles ──────────────────────────────────────────────────

    [Fact]
    public void ValidationOfCompactSharedDags_IsLinear_NotExponential()
    {
        // 250 stacked diamonds have 2^250 root-to-leaf paths. The pre-evaluation
        // validation walk memoizes visited nodes by reference identity (the violation
        // it detects is node-local, so revisits cannot change the outcome); without
        // the memo this Run call would never return. Evaluation itself then
        // short-circuits on the first path's unresolved name — per-occurrence
        // evaluation semantics of shared nodes are untouched.
        Expr node = new Expr.Resolve("noSuchName");
        for (var i = 0; i < 250; i++)
            node = new Expr.Binary(BinaryOp.Add, node, node);

        var result = Evaluator.Run(node);
        Assert.True(result.IsError);
        Assert.IsType<EvalError.UnknownName>(FindLeaf(result.Error));
    }

    [Fact]
    public void PluralValidationDiagnostics_AreDeduplicatedByNodeIdentityOnSharedHostDags()
    {
        // The validator's predicate is node-local. Its plural API therefore reports
        // one violation per distinct algorithm object, not one per incoming DAG edge;
        // pin that choice so the reference memo cannot silently change diagnostic
        // cardinality later. Parser trees do not share nodes, so source diagnostics
        // remain occurrence-equivalent.
        var sharedViolation = new Algorithm.User(
            null, [new ParameterDeclaration("x")], [], [], []);
        var root = new Algorithm.User(
            null,
            [],
            [],
            [new Property("A", sharedViolation), new Property("B", sharedViolation)],
            [new Expr.Num(1)]);

        var violations = AlgorithmValidation.FindExplicitParameterOutputViolations(root);
        Assert.Single(violations);
    }

    [Fact]
    public void SharedAcyclicSubtrees_AreNotMistakenForCycles()
    {
        var shared = UnarySpine(100);
        var diamond = new Expr.Binary(BinaryOp.Add, shared, shared);
        var result = Evaluator.Run(diamond);
        Assert.False(result.IsError);
    }

    [Fact]
    public void SharedSubtree_IsJudgedByItsLongestPath_NotItsFirstVisit()
    {
        // The shared spine is safe through the shallow left route (2 + 150 nodes) but
        // not through the deep right route (1 + 200 prefix nodes + 150 shared nodes).
        // First-visit depth tracking would wrongly accept this tree.
        var shared = UnarySpine(150);
        Expr deepRoute = shared;
        for (var i = 0; i < 200; i++)
            deepRoute = new Expr.Unary(UnaryOp.Minus, deepRoute);

        var root = new Expr.Binary(BinaryOp.Add, shared, deepRoute);
        AssertDepthRejected(root);
    }

    [Fact]
    public void ExponentialPathDag_IsCheckedInLinearTime()
    {
        // 200 stacked diamonds have 2^200 root-to-leaf paths but only ~201 nodes.
        // Without memoized per-node heights the preflight would never terminate; with
        // them it completes instantly. Only the preflight itself is exercised here:
        // the recursive consumers BEHIND the preflight (validation walker, evaluator)
        // deliberately treat each path as a separate visit, so handing them an
        // exponential-path DAG would take exponential TIME even though the depth is
        // safe — a pre-existing, documented residual outside this guard's contract.
        Expr accepted = new Expr.Num(1);
        for (var i = 0; i < 250; i++)
            accepted = new Expr.Binary(BinaryOp.Add, accepted, accepted);
        Assert.Null(AstStructuralPreflight.Check(
            accepted, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.EvaluatorIterativeJoinSpines));

        // The same shape grown past the ceiling is rejected — again in linear time.
        Expr rejected = accepted;
        for (var i = 0; i < 200; i++)
            rejected = new Expr.Binary(BinaryOp.Add, rejected, rejected);
        var rejection = AstStructuralPreflight.Check(
            rejected, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.EvaluatorIterativeJoinSpines);
        Assert.NotNull(rejection);
        Assert.Equal(AstStructuralViolation.DepthExceeded, rejection.Kind);
    }

    [Fact]
    public void CyclicExpressionGraph_IsRejectedDeterministically()
    {
        // A cycle whose path runs through EXPRESSION nodes. It cannot be
        // closed through ListLiteral/Capture/call arguments anymore: every
        // OutputBundle snapshots membership at construction, so
        // post-construction list mutation never reaches a bundle. An
        // Algorithm's Opens list is still an aliasable host collection, so the
        // cycle routes Call -> Function AlgorithmExpr -> open expression ->
        // the same Call, keeping a Call node on the cyclic path.
        var opens = new List<Expr>();
        var functionBlock = new Expr.AlgorithmExpr(new Algorithm.User(null, [], opens, [], [new Expr.Num(1)]));
        var cyclic = new Expr.Call(functionBlock, [new Expr.Num(1)]);
        opens.Add(cyclic);

        for (var repeat = 0; repeat < 3; repeat++)
        {
            var error = AssertRejected(cyclic);
            Assert.IsType<EvalError.AstCycleDetected>(error);
        }
    }

    [Fact]
    public void CyclicAlgorithmGraph_IsRejectedDeterministically()
    {
        var properties = new List<Property>();
        var algorithm = new Algorithm.User(null, [], [], properties, [new Expr.Num(1)]);
        properties.Add(new Property("Self", algorithm));

        var error = AssertRejected(new Expr.AlgorithmExpr(algorithm));
        Assert.IsType<EvalError.AstCycleDetected>(error);

        var message = KatLangError.FromEvalError(error).Message;
        Assert.Contains("reference cycle", message, StringComparison.Ordinal);
    }

    // ── Every evaluator entry point is guarded ─────────────────────────────────

    public static TheoryData<string> GuardedEntryPoints => new(
        "Run", "RunWithLimits", "RunFlat", "RunFlatWithLimits",
        "RunCounted", "RunCountedWithCache", "RunCountedObservedOptimized",
        "RunCountedObservedUnoptimized", "RunCountedWithTopLevelProperty");

    [Theory]
    [MemberData(nameof(GuardedEntryPoints))]
    public void EveryEntryPoint_RejectsDeepHostTrees(string entryPoint)
    {
        var deep = UnarySpine(10_000);
        var cache = new Evaluation.Caching.RunScopedZeroArgPropertyResultCache();
        EvalError error = entryPoint switch
        {
            "Run" => Require(Evaluator.Run(deep)),
            "RunWithLimits" => Require(Evaluator.Run(deep, EvaluationLimits.Default)),
            "RunFlat" => Require(Evaluator.RunFlat(deep)),
            "RunFlatWithLimits" => Require(Evaluator.RunFlat(deep, EvaluationLimits.Default)),
            "RunCounted" => Require(Evaluator.RunCounted(deep)),
            "RunCountedWithCache" => Require(Evaluator.RunCounted(deep, cache)),
            "RunCountedObservedOptimized" => Require(Evaluator.RunCountedObserved(deep, enableOptimizations: true).Result),
            "RunCountedObservedUnoptimized" => Require(Evaluator.RunCountedObserved(deep, enableOptimizations: false).Result),
            "RunCountedWithTopLevelProperty" => Require(Evaluator.RunCountedWithTopLevelProperty(deep, "X", cache)),
            _ => throw new InvalidOperationException(entryPoint),
        };

        Assert.Equal(
            EvaluationLimits.MaxSupportedAstDepth,
            Assert.IsType<EvalError.AstDepthLimitExceeded>(error).Limit);

        static EvalError Require<T>(EvalResult<T> result)
        {
            Assert.True(result.IsError);
            return result.Error;
        }
    }

    [Fact]
    public void Preflight_ChargesNothingToTheEvaluationBudget()
    {
        var (result, budget) = Evaluator.RunCountedObserved(UnarySpine(10_000));
        Assert.True(result.IsError);
        Assert.IsType<EvalError.AstDepthLimitExceeded>(result.Error);
        Assert.Equal(0, budget.ConsumedSteps);
        Assert.Equal(0, budget.PeakDepth);
        Assert.Equal(0, budget.MaterializedItems);
    }

    [Fact]
    public void OptimizerEligibility_AndResults_AreUnchangedForAcceptedTrees()
    {
        var parse = Parser.Parse("Values = range(1, 1000)\nValues.map(Double).sum\nDouble(x) = x * 2");
        Assert.False(parse.HasErrors);
        var program = new Expr.AlgorithmExpr(parse.Root);

        var (optimized, _) = Evaluator.RunCountedObserved(program, enableOptimizations: true);
        var (generic, _) = Evaluator.RunCountedObserved(program, enableOptimizations: false);
        Assert.False(optimized.IsError);
        Assert.False(generic.IsError);
        Assert.Equal(generic.Value.Value, optimized.Value.Value);
        Assert.Equal(generic.Value.EmittedCount, optimized.Value.EmittedCount);
    }

    [Fact]
    public void ConcurrentPreflights_AreIndependent()
    {
        var deep = UnarySpine(5_000);
        var shallow = UnarySpine(50);
        Parallel.For(0, 64, i =>
        {
            if (i % 2 == 0)
            {
                var result = Evaluator.Run(deep);
                Assert.True(result.IsError);
                Assert.IsType<EvalError.AstDepthLimitExceeded>(result.Error);
            }
            else
            {
                var result = Evaluator.Run(shallow);
                Assert.False(result.IsError);
            }
        });
    }

    // ── Parser-produced programs: unchanged inside the ceiling, gated beyond it ──

    [Fact]
    public void OrdinaryParserPrograms_AreUnaffected()
    {
        var result = KatLangEngine.Run("a = 1 + 2\na * 10");
        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal(new[] { 30m }, success.Atoms);
    }

    [Fact]
    public void ParserChainContract_AtMaxExpressionChainDepth_StillEvaluates()
    {
        var source = string.Join(" + ", Enumerable.Repeat("1", Parser.MaxExpressionChainDepth + 1));
        var result = KatLangEngine.Run(source);
        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal(new[] { (decimal)(Parser.MaxExpressionChainDepth + 1) }, success.Atoms);
    }

    [Fact]
    public void ParserContainerCapacity_FullBracketNesting_StillEvaluates()
    {
        // The deepest pure bracket nesting the parser's cumulative recursion budget
        // admits (127 levels at 3 weighted units per level) must stay inside the
        // structural ceiling and evaluate.
        const int levels = 120;
        var source = new string('[', levels) + "1" + new string(']', levels);
        var result = KatLangEngine.Run(source);
        Assert.IsType<RunResult.Success>(result);
    }

    [Fact]
    public void ComposedContainerChains_AreRejectedWithAStructuredParseDiagnostic()
    {
        // Chains restart from depth zero inside each container level, so stacked
        // in-budget chains compose into a tree far deeper than either parser budget
        // alone admits. Before the preflight this legal-looking source terminated the
        // process inside ParameterDetector; it must now produce one structured
        // diagnostic. (This very test would have crashed the runner before the fix.)
        var source = BracketChainComposition(levels: 20, chainOps: 150);
        var parse = Parser.Parse(source);
        Assert.True(parse.HasErrors);
        Assert.Contains(
            parse.Diagnostics,
            d => d.Message.Contains("structural AST depth limit", StringComparison.Ordinal));

        var engineResult = KatLangEngine.Run(source);
        Assert.IsType<RunResult.ParseFailure>(engineResult);
    }

    internal static string BracketChainComposition(int levels, int chainOps)
    {
        var builder = new System.Text.StringBuilder();
        builder.Append('[', levels).Append('1');
        for (var i = 0; i < levels; i++)
        {
            for (var j = 0; j < chainOps; j++)
                builder.Append(" + 1");
            builder.Append(']');
        }

        return builder.ToString();
    }

    // ── Semantic model building is guarded ──────────────────────────────────────

    [Fact]
    public void SemanticModelBuilder_RejectsDeepHostRoots()
    {
        var deepRoot = new Algorithm.User(null, [], [], [], [UnarySpine(50_000)]);
        var exception = Assert.Throws<ArgumentException>(
            () => Semantics.SemanticModelBuilder.Build(deepRoot));
        Assert.Contains("structural AST depth limit", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SemanticModelBuilder_RejectsCyclicHostRoots()
    {
        var properties = new List<Property>();
        var algorithm = new Algorithm.User(null, [], [], properties, [new Expr.Num(1)]);
        properties.Add(new Property("Self", algorithm));

        var exception = Assert.Throws<ArgumentException>(
            () => Semantics.SemanticModelBuilder.Build(algorithm));
        Assert.Contains("acyclic", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SemanticModelBuilder_AcceptsParserRoots()
    {
        var model = Semantics.SemanticModelBuilder.Build(Parser.Parse("x = 1\nx"));
        Assert.NotNull(model);
    }

    // ── Inherited base collections are enumerated uniformly on every subtype ────

    [Fact]
    public void InheritedCollections_OnBuiltin_AreCountedAtExactBoundaries()
    {
        // The recursive collections are virtual init properties on the Algorithm
        // BASE, so a host can place deep values on subtypes whose consumers ignore
        // them today. The preflight must measure them anyway: a Builtin carrying a
        // deep Output/Opens/pattern is a future bypass otherwise.
        foreach (var builtin in new Func<int, Algorithm>[]
        {
            depth => new Algorithm.Builtin(BuiltinId.@count) { Output = [UnarySpine(depth)] },
            depth => new Algorithm.Builtin(BuiltinId.@count) { Opens = [UnarySpine(depth)] },
            depth => new Algorithm.Builtin(BuiltinId.@count)
            {
                Properties = [new Property("P", new Algorithm.User(null, [], [], [], [UnarySpine(depth)]))],
            },
        })
        {
            // Builtin (1) + spine nodes; Properties adds one more algorithm level.
            Assert.Null(AstStructuralPreflight.Check(
                builtin(30), maxDepth: 40, AstConsumerProfile.FullyRecursive));
            var rejection = AstStructuralPreflight.Check(
                builtin(60), maxDepth: 40, AstConsumerProfile.FullyRecursive);
            Assert.NotNull(rejection);
            Assert.Equal(AstStructuralViolation.DepthExceeded, rejection.Kind);
        }

        // Exact boundary on the Output shape: root Builtin + N spine nodes.
        var atLimit = new Algorithm.Builtin(BuiltinId.@count) { Output = [UnarySpine(39)] };
        Assert.Null(AstStructuralPreflight.Check(atLimit, 40, AstConsumerProfile.FullyRecursive));
        var beyond = new Algorithm.Builtin(BuiltinId.@count) { Output = [UnarySpine(40)] };
        Assert.NotNull(AstStructuralPreflight.Check(beyond, 40, AstConsumerProfile.FullyRecursive));
    }

    [Fact]
    public void InheritedCollections_OnConditional_AreCountedAtExactBoundaries()
    {
        static Algorithm.Conditional WithPatterns(int patternNodes)
        {
            ParameterPattern pattern = new CaptureParameterPattern("x");
            for (var i = 0; i < patternNodes - 1; i++)
                pattern = new SequenceValueParameterPattern([pattern]);
            return new Algorithm.Conditional(
                null,
                [],
                [new CondBranch(new Pattern.Bind("x"), new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))])
            {
                ParameterPatterns = [pattern],
                ExplicitParameterPatterns = [pattern],
            };
        }

        // Conditional (1) + pattern spine; the same spine shared by both pattern
        // lists is memoized, not double-counted and not a false cycle.
        Assert.Null(AstStructuralPreflight.Check(WithPatterns(39), 40, AstConsumerProfile.FullyRecursive));
        var rejection = AstStructuralPreflight.Check(WithPatterns(40), 40, AstConsumerProfile.FullyRecursive);
        Assert.NotNull(rejection);
        Assert.Equal(AstStructuralViolation.DepthExceeded, rejection.Kind);
    }

    /// <summary>Alternating Spread(Construct(...)) chain: the ONE join shape whose evaluation recurses.</summary>
    internal static Expr AlternatingJoinChain(int levels)
    {
        Expr e = new Expr.EmptySequence(0);
        for (var i = 0; i < levels; i++)
            e = new Expr.SequenceSpread(new Expr.SequenceConstruct(e, new Expr.EmptySequence(0)));
        return e;
    }

    [Fact]
    public void AlternatingJoinChains_AreWeighted_AtTheExactBoundary()
    {
        // Single-kind join chains are iterative and stay free (pinned elsewhere at
        // tens of thousands of levels), but each ALTERNATION — a spread whose
        // operand is a construct — re-enters generic evaluation recursively and
        // previously overflowed a 1 MiB stack between 80 and 130 alternations
        // while the preflight charged ZERO for the whole chain. Each alternation
        // link now weighs 8 units, so the 300-unit ceiling admits exactly 37 links
        // (37*8 + 1 leaf = 297) and rejects 38 — a >=2.1x stack margin in Debug.
        var accepted = Evaluator.Run(AlternatingJoinChain(37));
        Assert.False(accepted.IsError);

        Assert.Equal(
            EvaluationLimits.MaxSupportedAstDepth,
            AssertDepthRejected(AlternatingJoinChain(38)).Limit);
    }

    [Fact]
    public void ExplicitParameterPatterns_AreMeasuredOnTheirOwn_AtExactBoundaries()
    {
        // ExplicitParameterPatterns with ParameterPatterns EMPTY: the only prior
        // coverage assigned the SAME spine to both collections, so deleting the
        // ExplicitParameterPatterns branch from TryGetChild kept every depth test
        // green — the spine stayed reachable through the sibling collection.
        static Algorithm WithExplicitOnly(int patternNodes)
        {
            ParameterPattern pattern = new CaptureParameterPattern("x");
            for (var i = 0; i < patternNodes - 1; i++)
                pattern = new SequenceValueParameterPattern([pattern]);
            return new Algorithm.User(null, [], [], [], [new Expr.Num(1)]) with
            {
                ExplicitParameterPatterns = [pattern],
            };
        }

        // Root algorithm (1) + N pattern nodes.
        Assert.Null(AstStructuralPreflight.Check(WithExplicitOnly(39), 40, AstConsumerProfile.FullyRecursive));
        var rejection = AstStructuralPreflight.Check(WithExplicitOnly(40), 40, AstConsumerProfile.FullyRecursive);
        Assert.NotNull(rejection);
        Assert.Equal(AstStructuralViolation.DepthExceeded, rejection.Kind);

        // The same shape through the public evaluator gate.
        static Expr Program(int patternNodes) => new Expr.AlgorithmExpr(new Algorithm.User(
            null, [], [], [new Property("F", WithExplicitOnly(patternNodes))], [new Expr.Num(1)]));
        AssertAccepted(Program(10));
        AssertDepthRejected(Program(EvaluationLimits.MaxSupportedAstDepth + 10));
    }

    [Fact]
    public void ScopeContextOpensAndProperties_AreMeasuredOnTheirOwn_AtExactBoundaries()
    {
        // Every other ScopeCtx in the suite is built with EMPTY Opens/Properties
        // (only Parent chains are exercised), so deleting either branch from the
        // ScopeCtx case kept the suite green. The parser never populates ScopeCtx,
        // so no source-level test can reach these incidentally.

        // Case A: the deep subtree hangs ONLY off Opens.
        // Root algorithm (1) + ScopeCtx (1) + N spine nodes.
        static Algorithm WithOpens(int spineNodes) => new Algorithm.User(
            new ScopeCtx(null, [UnarySpine(spineNodes)], []), [], [], [], [new Expr.Num(1)]);
        Assert.Null(AstStructuralPreflight.Check(WithOpens(38), 40, AstConsumerProfile.FullyRecursive));
        var opensRejection = AstStructuralPreflight.Check(WithOpens(39), 40, AstConsumerProfile.FullyRecursive);
        Assert.NotNull(opensRejection);
        Assert.Equal(AstStructuralViolation.DepthExceeded, opensRejection.Kind);

        // Case B: the deep subtree hangs ONLY off Properties[i].Value.
        // Root algorithm (1) + ScopeCtx (1) + property membrane + algorithm (1) + N spine nodes.
        static Algorithm WithProperties(int spineNodes) => new Algorithm.User(
            new ScopeCtx(null, [],
                [new Property("P", new Algorithm.User(null, [], [], [], [UnarySpine(spineNodes)]))]),
            [], [], [], [new Expr.Num(1)]);
        Assert.Null(AstStructuralPreflight.Check(WithProperties(37), 40, AstConsumerProfile.FullyRecursive));
        var propertiesRejection = AstStructuralPreflight.Check(WithProperties(38), 40, AstConsumerProfile.FullyRecursive);
        Assert.NotNull(propertiesRejection);
        Assert.Equal(AstStructuralViolation.DepthExceeded, propertiesRejection.Kind);

        // Both shapes through the public evaluator gate.
        AssertAccepted(new Expr.AlgorithmExpr(WithOpens(10)));
        AssertDepthRejected(new Expr.AlgorithmExpr(WithOpens(EvaluationLimits.MaxSupportedAstDepth + 10)));
        AssertAccepted(new Expr.AlgorithmExpr(WithProperties(10)));
        AssertDepthRejected(new Expr.AlgorithmExpr(WithProperties(EvaluationLimits.MaxSupportedAstDepth + 10)));
    }

    [Fact]
    public void InheritedCollections_CyclesAndSharing_AreJudgedCorrectly()
    {
        // A cycle routed through a Builtin's base-declared Opens is detected.
        // (Output can no longer carry this cycle: OutputBundle snapshots its
        // membership at construction, so post-construction list mutation —
        // the only way to close a cycle through a collection — cannot reach
        // a bundle. Opens is still an aliasable IReadOnlyList, keeping the
        // uniform base-surface enumeration itself pinned.)
        var opens = new List<Expr>();
        var cyclicBuiltin = new Algorithm.Builtin(BuiltinId.@count) { Opens = opens };
        opens.Add(new Expr.AlgorithmExpr(cyclicBuiltin));
        var rejection = AstStructuralPreflight.Check(
            cyclicBuiltin, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.FullyRecursive);
        Assert.NotNull(rejection);
        Assert.Equal(AstStructuralViolation.CycleDetected, rejection.Kind);

        // A shared subtree reachable through TWO base collections of the same
        // Builtin is not a cycle, and the walk stays linear (single visit).
        var shared = UnarySpine(100);
        var sharing = new Algorithm.Builtin(BuiltinId.@count)
        {
            Opens = [shared],
            Output = [shared],
        };
        Assert.Null(AstStructuralPreflight.Check(
            sharing, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.FullyRecursive));
    }

    [Fact]
    public void EvaluatorEntryPoints_RejectDeepInheritedCollections()
    {
        // Through the public evaluator gate, not only direct Check calls.
        var deepBuiltin = new Expr.AlgorithmExpr(new Algorithm.Builtin(BuiltinId.@count)
        {
            Output = [UnarySpine(10_000)],
        });
        AssertDepthRejected(deepBuiltin);

        ParameterPattern pattern = new CaptureParameterPattern("x");
        for (var i = 0; i < 10_000; i++)
            pattern = new SequenceValueParameterPattern([pattern]);
        var deepConditional = new Expr.AlgorithmExpr(new Algorithm.User(
            null,
            [],
            [],
            [
                new Property("F", new Algorithm.Conditional(
                    null,
                    [],
                    [new CondBranch(new Pattern.Bind("x"), new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))])
                {
                    ParameterPatterns = [pattern],
                }),
            ],
            [new Expr.Num(1)]));
        AssertDepthRejected(deepConditional);
    }

    // ── Membrane pass-through: Property and CondBranch add no level ─────────────

    [Fact]
    public void PropertyMembrane_PassesThroughWithoutAddingDepth()
    {
        // Root User(1) -> Property membrane -> value User(2) -> ... N algorithms
        // total, regardless of the Property records between them.
        static Algorithm PropertyChain(int algorithms)
        {
            Algorithm current = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
            for (var i = 0; i < algorithms - 1; i++)
                current = new Algorithm.User(null, [], [], [new Property("P", current)], []);
            return current;
        }

        // N algorithms measure N + 1 (the innermost body's Num output leaf), and the
        // Property records between them add NOTHING: the exact boundary sits at the
        // algorithm/output count alone.
        Assert.Null(AstStructuralPreflight.Check(
            PropertyChain(11), maxDepth: 12, AstConsumerProfile.FullyRecursive));
        var rejection = AstStructuralPreflight.Check(
            PropertyChain(12), maxDepth: 12, AstConsumerProfile.FullyRecursive);
        Assert.NotNull(rejection);
        Assert.Equal(AstStructuralViolation.DepthExceeded, rejection.Kind);
    }

    [Fact]
    public void CondBranchMembrane_PassesThroughWithoutAddingDepth()
    {
        // Root Conditional(1) -> CondBranch membrane -> body Conditional(2) -> ...
        // N algorithms total (each level also carries a leaf Pattern sibling).
        static Algorithm ConditionalChain(int algorithms)
        {
            Algorithm current = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
            for (var i = 0; i < algorithms - 1; i++)
                current = new Algorithm.Conditional(
                    null, [], [new CondBranch(new Pattern.Bind("x"), current)]);
            return current;
        }

        // N algorithms measure N + 1 (the innermost body's Num output leaf); the
        // CondBranch records between them add NOTHING, and each level's Pattern leaf
        // hangs shallower than the body chain.
        Assert.Null(AstStructuralPreflight.Check(
            ConditionalChain(11), maxDepth: 12, AstConsumerProfile.FullyRecursive));
        var rejection = AstStructuralPreflight.Check(
            ConditionalChain(12), maxDepth: 12, AstConsumerProfile.FullyRecursive);
        Assert.NotNull(rejection);
        Assert.Equal(AstStructuralViolation.DepthExceeded, rejection.Kind);
    }

    // ── Recursive-property inventory: new AST state must fail loudly ────────────

    [Fact]
    public void AstRecursivePropertyInventory_IsClosed()
    {
        // The preflight enumerates children by property; a NEW public property that
        // can carry AST nodes (directly or through a collection) would smuggle
        // unmeasured depth past the gate. This inventory turns adding one into a
        // failing test unless the enumeration is updated too.
        string[] astTypes =
        [
            nameof(Expr), nameof(Algorithm), nameof(Pattern), nameof(ParameterPattern),
            nameof(Property), nameof(CondBranch), nameof(ScopeCtx), nameof(OutputBundle),
        ];

        var known = new Dictionary<string, string[]>
        {
            // Base + subtype-declared recursive properties, by declaring type.
            [nameof(Algorithm)] = ["Parent", "ParameterPatterns", "Opens", "Properties", "Output", "Branches", "ExplicitParameterPatterns"],
            ["User"] = ["Parent", "ParameterPatterns", "Opens", "Properties", "Output"],
            ["Conditional"] = ["Parent", "Opens", "Branches"],
            ["Unary"] = ["Operand"],
            ["Binary"] = ["Left", "Right"],
            ["Index"] = ["Target", "Selector"],
            ["SequenceConstruct"] = ["Left", "Right"],
            ["SequenceSpread"] = ["Operand"],
            ["ListLiteral"] = ["Items"],
            // LexicalFallback is enumerated by TryGetChild; EffectiveLexicalFallback
            // is a computed view over it (LexicalFallback ?? Resolve(Name)) and
            // introduces no additional stored reachability.
            ["DotCall"] = ["Target", "Args", "LexicalFallback", "EffectiveLexicalFallback"],
            ["Grace"] = ["Inner"],
            ["AlgorithmExpr"] = ["Algorithm"],
            ["Capture"] = ["Body"],
            [nameof(OutputBundle)] = ["Item"],
            ["Call"] = ["Function", "Args"],
            ["SequenceValue"] = ["Items"],
            ["SequenceValueParameterPattern"] = ["Items"],
            [nameof(Property)] = ["Value"],
            [nameof(CondBranch)] = ["Pattern", "Body"],
            [nameof(ScopeCtx)] = ["Parent", "Opens", "Properties"],
        };

        var assembly = typeof(Expr).Assembly;
        var astBaseTypes = new[]
        {
            typeof(Expr), typeof(Algorithm), typeof(Pattern), typeof(ParameterPattern),
            typeof(Property), typeof(CondBranch), typeof(ScopeCtx), typeof(OutputBundle),
        };

        static bool CarriesAstNodes(Type type, Type[] astBases)
        {
            if (astBases.Any(baseType => baseType.IsAssignableFrom(type)))
                return true;
            if (type.IsGenericType)
                return type.GetGenericArguments().Any(argument => CarriesAstNodes(argument, astBases));
            return false;
        }

        var unexpected = new List<string>();
        foreach (var type in assembly.GetTypes())
        {
            var isAstType = astBaseTypes.Any(baseType =>
                baseType.IsAssignableFrom(type) && type != typeof(object));
            if (!isAstType)
                continue;

            foreach (var property in type.GetProperties(
                System.Reflection.BindingFlags.Public
                | System.Reflection.BindingFlags.Instance
                | System.Reflection.BindingFlags.DeclaredOnly))
            {
                if (!CarriesAstNodes(property.PropertyType, astBaseTypes))
                    continue;

                var declared = known.TryGetValue(type.Name, out var names) ? names : [];
                if (!declared.Contains(property.Name))
                    unexpected.Add($"{type.Name}.{property.Name}");
            }
        }

        Assert.True(
            unexpected.Count == 0,
            "New AST-carrying public properties must be added to AstStructuralPreflight.TryGetChild "
            + "and to this inventory: " + string.Join(", ", unexpected));
    }

    // ── Public front-end boundaries are gated ───────────────────────────────────

    [Fact]
    public void ParameterDetectorDetect_GatesHostRoots_AtTheExactBoundary()
    {
        // Root User(1) + unary spine K => depth K + 1.
        var max = EvaluationLimits.MaxSupportedAstDepth;
        var (atLimitRoot, atLimitDiags) = ParameterDetector.Detect(
            new Algorithm.User(null, [], [], [], [UnarySpine(max - 1)]));
        Assert.Empty(atLimitDiags);
        Assert.NotEmpty(atLimitRoot.Output);

        var (rejectedRoot, rejectedDiags) = ParameterDetector.Detect(
            new Algorithm.User(null, [], [], [], [UnarySpine(max)]));
        Assert.Empty(rejectedRoot.Output);
        Assert.Contains(
            rejectedDiags,
            d => d.Message.Contains($"structural AST depth limit of {max}", StringComparison.Ordinal));

        // Cyclic host roots fail structurally, not by hanging or overflowing.
        var properties = new List<Property>();
        var cyclic = new Algorithm.User(null, [], [], properties, [new Expr.Num(1)]);
        properties.Add(new Property("Self", cyclic));
        var (_, cyclicDiags) = ParameterDetector.Detect(cyclic);
        Assert.Contains(
            cyclicDiags,
            d => d.Message.Contains("reference cycle", StringComparison.Ordinal));

        // Safe-depth behavior is identical to the prevalidated core the pipeline uses
        // (record equality is reference-based for list members, so compare the
        // observable outcome: diagnostics and the evaluated result).
        var parsed = Parser.ParseSyntax("a = 1\na + 2");
        Assert.False(parsed.HasErrors);
        var (publicRoot, publicDiags) = ParameterDetector.Detect(parsed.SyntaxRoot);
        var (coreRoot, coreDiags) = ParameterDetector.DetectPrevalidated(parsed.SyntaxRoot);
        Assert.Equal(coreDiags.Count, publicDiags.Count);
        var publicRun = Evaluator.RunFlat(new Expr.AlgorithmExpr(ImplicitArgumentResolver.ResolvePrevalidated(publicRoot)));
        var coreRun = Evaluator.RunFlat(new Expr.AlgorithmExpr(ImplicitArgumentResolver.ResolvePrevalidated(coreRoot)));
        Assert.False(publicRun.IsError);
        Assert.Equal(coreRun.Value, publicRun.Value);
    }

    [Fact]
    public void ImplicitArgumentResolverResolve_GatesHostRoots_AtTheExactBoundary()
    {
        var max = EvaluationLimits.MaxSupportedAstDepth;
        var atLimit = ImplicitArgumentResolver.Resolve(
            new Algorithm.User(null, [], [], [], [UnarySpine(max - 1)]));
        Assert.NotEmpty(atLimit.Output);

        var depthException = Assert.Throws<ArgumentException>(() => ImplicitArgumentResolver.Resolve(
            new Algorithm.User(null, [], [], [], [UnarySpine(max)])));
        Assert.Contains("structural AST depth limit", depthException.Message, StringComparison.Ordinal);

        var properties = new List<Property>();
        var cyclic = new Algorithm.User(null, [], [], properties, [new Expr.Num(1)]);
        properties.Add(new Property("Self", cyclic));
        var cycleException = Assert.Throws<ArgumentException>(() => ImplicitArgumentResolver.Resolve(cyclic));
        Assert.Contains("acyclic", cycleException.Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task ModuleLoaderElaborate_GatesHostRoots_AtTheExactBoundary()
    {
        // Root User(1) + unary spine K => depth K + 1; the loader's boundary is the
        // raw-syntax cap its own traversal was measured against. The spines are
        // load-free, so the walk is the calibrated SYNCHRONOUS one and the returned
        // ValueTask completes synchronously.
        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(diagnostics);
        var accepted = await loader.ElaborateAsync(
            new Algorithm.User(null, [], [], [], [UnarySpine(ModuleLoader.MaxTraversalDepth - 1)]));
        Assert.Empty(diagnostics);
        Assert.NotEmpty(accepted.Output);

        var rejected = await loader.ElaborateAsync(
            new Algorithm.User(null, [], [], [], [UnarySpine(ModuleLoader.MaxTraversalDepth)]));
        Assert.Empty(rejected.Output);
        Assert.Contains(
            diagnostics,
            d => d.Message.Contains(
                $"structural AST depth limit of {ModuleLoader.MaxTraversalDepth}",
                StringComparison.Ordinal));

        // Cyclic host roots are rejected before any recursive frame.
        var cyclicDiagnostics = new List<Diagnostic>();
        var cyclicLoader = new ModuleLoader(cyclicDiagnostics);
        var properties = new List<Property>();
        var cyclic = new Algorithm.User(null, [], [], properties, [new Expr.Num(1)]);
        properties.Add(new Property("Self", cyclic));
        await cyclicLoader.ElaborateAsync(cyclic);
        Assert.Contains(
            cyclicDiagnostics,
            d => d.Message.Contains("reference cycle", StringComparison.Ordinal));
    }

    [Fact]
    public void ModuleLoaderNestedParseDebt_RoundsUpAndDecreasesCapacityMonotonically()
    {
        Assert.Equal(0, ModuleLoader.NestedParseStackDebt(0));
        Assert.Equal(1, ModuleLoader.NestedParseStackDebt(1));
        Assert.Equal(2, ModuleLoader.NestedParseStackDebt(2));
        Assert.Equal(2, ModuleLoader.NestedParseStackDebt(3));
        Assert.Equal(3, ModuleLoader.NestedParseStackDebt(4));
        Assert.Equal(427, ModuleLoader.NestedParseStackDebt(ModuleLoader.MaxTraversalDepth));
        Assert.Equal(1_431_655_765, ModuleLoader.NestedParseStackDebt(int.MaxValue));

        var previous = -1;
        for (var depth = 0; depth <= ModuleLoader.MaxTraversalDepth; depth++)
        {
            var debt = ModuleLoader.NestedParseStackDebt(depth);
            Assert.True(debt >= previous, $"Parser debt decreased at loader depth {depth}.");
            previous = debt;
        }
    }

    [Fact]
    public async Task ModuleLoaderElaborate_RechecksCachedModulesAtTheirFinalSplicePath()
    {
        const string url = "https://katlang.org/cache/deep.kat";
        var load = Assert.Single(Parser.ParseSyntax($"open '{url}'").SyntaxRoot.Opens);

        // The input host AST is safely below the raw loader ceiling. The first open
        // loads and caches a module with 80 block/algorithm levels. The second open
        // splices that cache entry beneath 250 additional block/algorithm levels:
        // skipping fetch/parse/traversal is safe, but the finished composition is
        // deeper than 640 and must not escape the public loader boundary.
        Expr deepCachedUse = load;
        for (var i = 0; i < 250; i++)
        {
            deepCachedUse = new Expr.AlgorithmExpr(
                new Algorithm.User(null, [], [], [], [deepCachedUse]));
        }

        var hostRoot = new Algorithm.User(null, [], [load, deepCachedUse], [], [new Expr.Num(1)]);
        Assert.Null(AstStructuralPreflight.Check(
            hostRoot,
            ModuleLoader.MaxTraversalDepth,
            AstConsumerProfile.FullyRecursive));

        var downloads = 0;
        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(
            diagnostics,
            (_, _) =>
            {
                downloads++;
                return ValueTask.FromResult("public S = " + new string('{', 80) + "1" + new string('}', 80));
            });

        var elaborated = await loader.ElaborateAsync(hostRoot);
        Assert.Empty(elaborated.Output);
        Assert.Equal(1, downloads);
        Assert.Contains(
            diagnostics,
            d => d.Message.Contains(
                $"structural AST depth limit of {ModuleLoader.MaxTraversalDepth}",
                StringComparison.Ordinal));
    }

    [Fact]
    public async Task ModuleLoader_MapsDownloadedRawStructuralRejectionToNestingDiagnostic()
    {
        const string url = "https://katlang.org/raw-structural-deep.kat";
        var downloads = 0;
        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(
            diagnostics,
            (_, _) =>
            {
                downloads++;
                // Parser-recursion and per-chain limits each permit this composed
                // source, but its finished raw tree is 641 levels deep.
                return ValueTask.FromResult(BracketChainComposition(levels: 9, chainOps: 70));
            });

        await loader.ElaborateAsync(Parser.ParseSyntax($"open '{url}'").SyntaxRoot);

        Assert.Equal(1, downloads);
        Assert.Equal(0, loader.CachedModuleCount);
        Assert.Contains(
            diagnostics,
            d => d.Message.Contains(url, StringComparison.Ordinal)
                && d.Message.Contains("too deeply to parse safely", StringComparison.Ordinal));
        Assert.DoesNotContain(
            diagnostics,
            d => d.Message.Contains(url, StringComparison.Ordinal)
                && d.Message.Contains("not valid KatLang source", StringComparison.Ordinal));
    }

    // ── Traversal completeness: every AST variant is known to the preflight ────

    [Fact]
    public void Preflight_KnowsEveryAstVariant()
    {
        // The preflight fails loudly on unknown node kinds instead of skipping their
        // children. This reflection sweep turns "a new AST variant was added" into a
        // failing test here, so the child enumeration cannot silently fall behind.
        string[] knownExpr =
        [
            "Param", "Num", "StringLiteral", "Unary", "Binary", "Index",
            "SequenceConstruct", "EmptySequence", "SequenceSpread", "ListLiteral",
            "Resolve", "DotCall", "Grace", "AlgorithmExpr", "Capture", "Call", "NativeCall",
        ];
        string[] knownAlgorithm = ["User", "Builtin", "Conditional"];
        string[] knownPattern = ["Bind", "LitInt", "LitString", "SequenceValue"];
        string[] knownParameterPattern = ["CaptureParameterPattern", "SequenceValueParameterPattern"];

        AssertVariants(typeof(Expr), knownExpr);
        AssertVariants(typeof(Algorithm), knownAlgorithm);
        AssertVariants(typeof(Pattern), knownPattern);

        var parameterPatterns = typeof(ParameterPattern).Assembly.GetTypes()
            .Where(t => !t.IsAbstract && typeof(ParameterPattern).IsAssignableFrom(t))
            .Select(t => t.Name)
            .OrderBy(n => n, StringComparer.Ordinal);
        Assert.Equal(knownParameterPattern.OrderBy(n => n, StringComparer.Ordinal), parameterPatterns);

        static void AssertVariants(Type baseType, string[] known)
        {
            var actual = baseType.GetNestedTypes()
                .Where(t => !t.IsAbstract && baseType.IsAssignableFrom(t))
                .Select(t => t.Name)
                .OrderBy(n => n, StringComparer.Ordinal)
                .ToList();
            Assert.Equal(known.OrderBy(n => n, StringComparer.Ordinal), actual);
        }
    }

    [Fact]
    public void Preflight_TraversesEveryExprVariantTree()
    {
        // One tree containing every Expr variant, every Algorithm variant, every
        // Pattern variant, and both ParameterPattern variants; the preflight must
        // accept it (proving each switch arm enumerates real children) and reject it
        // under a tiny limit (proving each variant's children are actually followed).
        var conditional = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches:
            [
                new CondBranch(
                    new Pattern.SequenceValue([new Pattern.LitInt(1), new Pattern.LitString("s"), new Pattern.Bind("x")]),
                    new Algorithm.User(null, [], [], [], [new Expr.Param("x")])),
            ]);
        var parameterized = new Algorithm.User(null, [], [], [], [new Expr.Num(1)])
            .WithParameterPatterns([new SequenceValueParameterPattern([new CaptureParameterPattern("q")])]);
        var everything = new Expr.AlgorithmExpr(new Algorithm.User(
            new ScopeCtx(null, [], []),
            [],
            [new Expr.Resolve("Math")],
            [
                new Property("Cond", conditional),
                new Property("Pat", parameterized),
                new Property("Builtin", new Algorithm.Builtin(BuiltinId.@count)),
            ],
            [
                new Expr.Unary(UnaryOp.Minus, new Expr.Num(1)),
                new Expr.Binary(BinaryOp.Add, new Expr.Num(1), new Expr.Num(2)),
                new Expr.Index(new Expr.ListLiteral([new Expr.Num(1)]), new Expr.Num(0)),
                new Expr.SequenceConstruct(new Expr.Num(1), new Expr.EmptySequence(0)),
                new Expr.SequenceSpread(new Expr.StringLiteral("s")),
                new Expr.Grace(new Expr.Resolve("Cond"), 1),
                new Expr.DotCall(new Expr.Num(3), "string", OutputBundle.Empty),
                new Expr.Call(new Expr.Resolve("Pat"), [new Expr.Num(1)]),
                new Expr.Capture([new Expr.Num(4), new Expr.EmptySequence(0)]),
                new Expr.NativeCall("sin", ["x"]),
            ]));

        Assert.Null(AstStructuralPreflight.Check(
            everything, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.EvaluatorIterativeJoinSpines));
        var rejection = AstStructuralPreflight.Check(
            everything, maxDepth: 3, AstConsumerProfile.FullyRecursive);
        Assert.NotNull(rejection);
        Assert.Equal(AstStructuralViolation.DepthExceeded, rejection.Kind);
    }

    [Fact]
    public void Preflight_VirtualHugeBranchCount_CannotOverflowChildInventory()
    {
        // IReadOnlyList is a host boundary, not necessarily an in-memory List<T>.
        // Count * 2 overflows for this legal virtual count; the preflight must still
        // visit the first branch body and reject its unsafe depth.
        var firstBranch = new CondBranch(
            new Pattern.Bind("x"),
            new Algorithm.User(null, [], [], [], [UnarySpine(20)]));
        var root = new Algorithm.Conditional(
            null,
            [],
            new VirtualHugeBranchList(firstBranch));

        var rejection = AstStructuralPreflight.Check(
            root,
            maxDepth: 10,
            AstConsumerProfile.FullyRecursive);

        Assert.NotNull(rejection);
        Assert.Equal(AstStructuralViolation.DepthExceeded, rejection.Kind);
    }

    private sealed class VirtualHugeBranchList(CondBranch first) : IReadOnlyList<CondBranch>
    {
        public int Count => int.MaxValue;

        public CondBranch this[int index]
            => index == 0
                ? first
                : throw new InvalidOperationException(
                    "The preflight should reject through the first branch before requesting a later virtual item.");

        public IEnumerator<CondBranch> GetEnumerator()
            => throw new InvalidOperationException("The preflight must use bounded indexed access.");

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator()
            => GetEnumerator();
    }
}

/// <summary>
/// Process-isolated regression proving the structural preflight protects against a
/// process-terminating stack overflow: an in-process test cannot demonstrate that
/// safely, so a child process builds host ASTs FAR beyond any plausible CLR-safe
/// recursion depth, exercises representative public evaluator paths, observes the
/// controlled structural rejection, writes a success marker, and exits normally.
/// Follows the subprocess convention of <see cref="ParserExpressionChainDepthTests"/>.
/// </summary>
public class AstStructuralDepthProcessTests
{
    private const string ProbeChildEnvironment = "KATLANG_AST_STRUCTURAL_PROBE_CHILD";
    private const string ProbeMarkerFileEnvironment = "KATLANG_AST_STRUCTURAL_PROBE_MARKER_FILE";
    private const string ProbeSuccessMarker = "katlang-ast-structural-preflight-ok";

    /// <summary>
    /// Wraps an in-memory synchronous fetch as the async downloader contract. The
    /// returned ValueTasks complete synchronously (a throwing fetch throws
    /// synchronously from the delegate), so probe elaborations never leave their
    /// dedicated calibrated thread.
    /// </summary>
    private static Func<string, CancellationToken, ValueTask<string>> InMemoryDownloader(
        Func<string, string> fetch)
        => (url, _) => ValueTask.FromResult(fetch(url));

    /// <summary>
    /// Runs one elaboration whose downloader completes synchronously and asserts it
    /// therefore completed synchronously — GetResult here is plain result extraction
    /// on a completed ValueTask (possibly rethrowing its synchronously-captured
    /// exception), never a blocking bridge.
    /// </summary>
    private static Algorithm ElaborateSynchronously(ModuleLoader loader, Algorithm root)
    {
        var task = loader.ElaborateAsync(root);
        Assert.True(task.IsCompleted, "Elaboration with a synchronous downloader must complete synchronously.");
        return task.GetAwaiter().GetResult();
    }

    /// <summary>
    /// Same synchronous-completion contract for whole engine runs whose downloader
    /// completes synchronously.
    /// </summary>
    private static RunResult RunEngineSynchronously(string source, RunOptions options)
    {
        var task = KatLangEngine.RunAsync(source, options);
        Assert.True(task.IsCompleted, "An engine run with a synchronous downloader must complete synchronously.");
        return task.GetAwaiter().GetResult();
    }

    /// <summary>
    /// Launches one env-gated probe-child test in a fresh <c>dotnet vstest</c> process
    /// and asserts the contract every probe shares: normal exit, no stack-overflow
    /// text, the expected success-marker file, and completion within the timeout —
    /// with captured stdout/stderr surfaced on any failure.
    /// </summary>
    private static async Task RunProbeChild(string childTestName)
    {
        var assemblyPath = typeof(AstStructuralDepthProcessTests).Assembly.Location;
        var testName = typeof(AstStructuralDepthProcessTests).FullName + "." + childTestName;
        var markerFile = Path.Combine(
            Path.GetTempPath(),
            $"katlang-ast-probe-{Guid.NewGuid():N}.txt");

        var startInfo = new ProcessStartInfo("dotnet")
        {
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
            CreateNoWindow = true,
        };
        startInfo.ArgumentList.Add("vstest");
        startInfo.ArgumentList.Add(assemblyPath);
        startInfo.ArgumentList.Add("--Tests:" + testName);
        startInfo.Environment[ProbeChildEnvironment] = "1";
        startInfo.Environment[ProbeMarkerFileEnvironment] = markerFile;
        startInfo.Environment["DOTNET_NOLOGO"] = "1";

        try
        {
            using var process = new Process { StartInfo = startInfo };
            process.Start();
            var stdoutTask = process.StandardOutput.ReadToEndAsync();
            var stderrTask = process.StandardError.ReadToEndAsync();

            var exited = true;
            using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(90));
            try
            {
                await process.WaitForExitAsync(timeout.Token);
            }
            catch (OperationCanceledException)
            {
                exited = false;
                try { process.Kill(entireProcessTree: true); }
                catch { /* process already exited */ }
                await process.WaitForExitAsync();
            }

            var stdout = await stdoutTask;
            var stderr = await stderrTask;
            var combined = stdout + Environment.NewLine + stderr;

            Assert.True(exited, $"Probe subprocess '{childTestName}' did not exit within 90 seconds."
                + Environment.NewLine + combined);
            Assert.DoesNotContain("Stack overflow", combined, StringComparison.OrdinalIgnoreCase);
            Assert.DoesNotContain("StackOverflowException", combined, StringComparison.OrdinalIgnoreCase);
            Assert.True(
                process.ExitCode == 0,
                $"Probe subprocess '{childTestName}' exited with {process.ExitCode}.{Environment.NewLine}{combined}");
            Assert.True(
                File.Exists(markerFile),
                $"Probe child '{childTestName}' did not write its success marker.{Environment.NewLine}{combined}");
            Assert.Equal(ProbeSuccessMarker, (await File.ReadAllTextAsync(markerFile)).Trim());
        }
        finally
        {
            try { File.Delete(markerFile); }
            catch { /* best-effort cleanup */ }
        }
    }

    private static void WriteProbeMarker()
    {
        var markerFile = Environment.GetEnvironmentVariable(ProbeMarkerFileEnvironment);
        Assert.False(string.IsNullOrWhiteSpace(markerFile));
        File.WriteAllText(markerFile!, ProbeSuccessMarker);
    }

    /// <summary>
    /// Runs a probe body on a dedicated thread with an exactly-sized stack, so the
    /// probe exercises the DOCUMENTED minimum supported environment (a 1 MiB thread
    /// stack) deterministically instead of whatever stack the test host happens to
    /// give its worker threads. Exceptions propagate to the caller.
    /// </summary>
    internal static void RunOnThreadWithStack(int maxStackBytes, Action body)
    {
        Exception? failure = null;
        var thread = new Thread(
            () =>
            {
                try
                {
                    body();
                }
                catch (Exception ex)
                {
                    failure = ex;
                }
            },
            maxStackBytes);
        thread.Start();
        thread.Join();
        if (failure is not null)
            System.Runtime.ExceptionServices.ExceptionDispatchInfo.Capture(failure).Throw();
    }

    [Fact]
    public async Task ExtremeHostAsts_AreRejectedInSubprocess_WithoutProcessTermination()
        => await RunProbeChild("ExtremeHostAsts_ProbeChild");

    [Fact]
    public void ExtremeHostAsts_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        // Each tree is built ITERATIVELY to depths far beyond any CLR-safe recursive
        // depth and far beyond the structural limit; a missing or late preflight
        // fast-fails this whole process instead of returning the structured error.
        var unary = AstStructuralDepthTests.UnarySpine(2_000_000);
        AssertStructuralDepthError(Evaluator.Run(unary));

        var binary = AstStructuralDepthTests.BinarySpine(1_000_000, leftDeep: true);
        AssertStructuralDepthError(Evaluator.RunFlat(binary));

        var blocks = AstStructuralDepthTests.BlockSpine(200_000);
        AssertStructuralDepthError(Evaluator.Run(blocks, EvaluationLimits.Default));

        // The parser front-end composition gate, in the same hostile-depth regime.
        var composed = AstStructuralDepthTests.BracketChainComposition(levels: 100, chainOps: 200);
        var parseResult = KatLangEngine.Run(composed);
        Assert.IsType<RunResult.ParseFailure>(parseResult);

        WriteProbeMarker();

        static void AssertStructuralDepthError<T>(EvalResult<T> result)
        {
            Assert.True(result.IsError);
            var error = Assert.IsType<EvalError.AstDepthLimitExceeded>(result.Error);
            Assert.Equal(EvaluationLimits.MaxSupportedAstDepth, error.Limit);
        }
    }

    [Fact]
    public async Task AlternatingJoinsAndNestedBuiltins_StayStructured_InSubprocess()
        => await RunProbeChild(nameof(AlternatingJoinsAndNestedBuiltins_ProbeChild));

    [Fact]
    public void AlternatingJoinsAndNestedBuiltins_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        // These are process-termination regressions, so they must execute in this
        // child rather than in the main xUnit host. A missing alternation weight or
        // builtin-argument stack probe kills only the probe process, and the parent
        // reports the absent marker/non-zero exit as an ordinary test failure.
        RunOnThreadWithStack(1_048_576, () =>
        {
            // The calibrated accepted boundary must genuinely evaluate on the
            // minimum supported stack, not merely pass the structural preflight.
            var accepted = AstStructuralDepthTests.AlternatingJoinChain(37);
            Assert.False(Evaluator.Run(accepted).IsError);
            Assert.False(Evaluator.RunFlat(accepted).IsError);
            Assert.False(Evaluator.RunCounted(accepted).IsError);

            // Far beyond the former alternating-join crash boundary, through every
            // runtime entry point. The safe exact 37/38 weighted boundary remains an
            // in-process assertion in AstStructuralDepthTests.
            var deep = AstStructuralDepthTests.AlternatingJoinChain(1000);
            Assert.IsType<EvalError.AstDepthLimitExceeded>(Evaluator.Run(deep).Error);
            Assert.IsType<EvalError.AstDepthLimitExceeded>(Evaluator.RunFlat(deep).Error);
            Assert.IsType<EvalError.AstDepthLimitExceeded>(Evaluator.RunCounted(deep).Error);

            // Source-reachable nesting: call arguments parse through 127 levels.
            // Cover the materially different builtin paths from the audit — scalar,
            // lazy branch, sequence receiver, and callback — at representative former
            // crash boundaries and at the parser ceiling.
            (string Preamble, string Prefix, string Suffix)[] builtinShapes =
            [
                ("", "sum(", ")"),
                ("", "if(1, ", ", 0)"),
                ("", "take(", ", 1)"),
                ("Id(x) = x\n", "map(", ", Id)"),
            ];

            foreach (var (preamble, prefix, suffix) in builtinShapes)
            {
                foreach (var levels in new[] { 32, 63, 90, 127 })
                {
                    var source = preamble
                        + string.Concat(Enumerable.Repeat(prefix, levels))
                        + "1"
                        + string.Concat(Enumerable.Repeat(suffix, levels));
                    var run = KatLangEngine.Run(source);
                    Assert.True(
                        run is RunResult.Success or RunResult.EvalFailure,
                        $"unexpected outcome {run.GetType().Name} for `{prefix}` at {levels} levels");

                    // The evaluator's public AST entry is a second distinct runtime
                    // funnel. Any EvalResult outcome is structured; process death is
                    // observed by the parent as a missing marker/non-zero exit.
                    _ = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
                }
            }
        });

        WriteProbeMarker();
    }

    [Fact]
    public async Task NearBoundaryShapes_EvaluateOrRejectDeterministically_InSubprocess()
        => await RunProbeChild("NearBoundaryShapes_ProbeChild");

    /// <summary>
    /// The accepted-boundary proof, on a dedicated 1 MiB thread (the documented
    /// minimum supported stack): for every materially different recursive shape, a
    /// tree ONE BELOW and EXACTLY AT the maximum accepted structural depth must
    /// actually EVALUATE through the public paths to the correct value or an
    /// established non-depth result, and ONE ABOVE must return the structured depth
    /// error — never terminate the process. The machine-driven spine shapes are
    /// additionally re-proven on a tiny 384 KiB thread, which a depth-proportional
    /// recursive implementation could not survive: that assertion doubles as the
    /// permanent mutation detector for the iterative evaluation paths.
    /// </summary>
    [Fact]
    public void NearBoundaryShapes_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        var max = EvaluationLimits.MaxSupportedAstDepth;

        RunOnThreadWithStack(1_048_576, () =>
        {
            // ── Unary spines ────────────────────────────────────────────────
            AssertFlatValue(AstStructuralDepthTests.UnarySpine(max - 1), UnaryValue(max - 1));
            AssertFlatValue(AstStructuralDepthTests.UnarySpine(max), UnaryValue(max));
            AssertDepthRejected(AstStructuralDepthTests.UnarySpine(max + 1));

            // ── Left- and right-associated binary spines ────────────────────
            AssertFlatValue(AstStructuralDepthTests.BinarySpine(max - 1, leftDeep: true), max - 1);
            AssertFlatValue(AstStructuralDepthTests.BinarySpine(max, leftDeep: true), max);
            AssertDepthRejected(AstStructuralDepthTests.BinarySpine(max + 1, leftDeep: true));
            AssertFlatValue(AstStructuralDepthTests.BinarySpine(max - 1, leftDeep: false), max - 1);
            AssertFlatValue(AstStructuralDepthTests.BinarySpine(max, leftDeep: false), max);
            AssertDepthRejected(AstStructuralDepthTests.BinarySpine(max + 1, leftDeep: false));

            // The exact-limit binary spine through every distinct evaluator path,
            // with optimizations enabled and disabled, and under the greatest
            // caller-configurable limit (clamped down to the ceiling).
            var atLimit = AstStructuralDepthTests.BinarySpine(max, leftDeep: true);
            var run = Evaluator.Run(atLimit);
            Assert.False(run.IsError);
            var counted = Evaluator.RunCounted(atLimit);
            Assert.False(counted.IsError);
            Assert.Equal(1, counted.Value.EmittedCount);
            var (observedOn, _) = Evaluator.RunCountedObserved(atLimit, enableOptimizations: true);
            Assert.False(observedOn.IsError);
            var (observedOff, _) = Evaluator.RunCountedObserved(atLimit, enableOptimizations: false);
            Assert.False(observedOff.IsError);
            var clamped = Evaluator.Run(atLimit, new EvaluationLimits { MaxAstDepth = int.MaxValue });
            Assert.False(clamped.IsError);
            var clampedBeyond = Evaluator.Run(
                AstStructuralDepthTests.BinarySpine(max + 1, leftDeep: true),
                new EvaluationLimits { MaxAstDepth = int.MaxValue });
            Assert.True(clampedBeyond.IsError);
            Assert.Equal(max, Assert.IsType<EvalError.AstDepthLimitExceeded>(clampedBeyond.Error).Limit);

            // ── Index spines (target descent + projection per level) ────────
            AssertFlatValue(IndexSpine(max - 1), 1m);
            AssertFlatValue(IndexSpine(max), 1m);
            AssertDepthRejected(IndexSpine(max + 1));

            // ── List spines ─────────────────────────────────────────────────
            AssertFlatValue(AstStructuralDepthTests.ListSpine(max - 1), 1m);
            AssertFlatValue(AstStructuralDepthTests.ListSpine(max), 1m);
            AssertDepthRejected(AstStructuralDepthTests.ListSpine(max + 1));

            // ── Nested blocks (algorithm bodies; still recursive, ceiling-bounded)
            // Two counted nodes per level make the pure shape odd-cost. An OUTER spine
            // wrapper cannot add one unit because its edge to the non-spine block is a
            // charged machine re-entry; innermost spine padding is still one iterative
            // node and retains an honest exact-ceiling construction.
            AssertFlatValue(AstStructuralDepthTests.BlockSpine((max - 1) / 2), 1m);              // depth max - 1
            AssertFlatValue(
                AstStructuralDepthTests.BlockSpine(
                    (max - 1) / 2,
                    new Expr.Unary(UnaryOp.Minus, new Expr.Num(1))),
                -1m);                                                                            // depth max
            AssertDepthRejected(AstStructuralDepthTests.BlockSpine((max + 1) / 2));              // depth max + 1

            // ── Nested calls (invocation machinery; frame cost differs from blocks)
            // At and below the limit the outcome is the value on roomy stacks or the
            // ESTABLISHED structured invocation backstop on constrained ones — never
            // a structural error, never process death.
            AssertValueOrEstablishedRuntimeStop(CallSpine((max - 4) / 2), 1m);                    // depth max - 1
            AssertValueOrEstablishedRuntimeStop(
                CallSpine(
                    (max - 4) / 2,
                    new Expr.Unary(UnaryOp.Minus, new Expr.Num(1))),
                -1m);                                                                             // depth max
            AssertDepthRejected(CallSpine((max - 2) / 2));                                        // depth max + 1

            // ── Dot-call chains (weight 3 per link) ─────────────────────────
            // Innermost unary padding stays within one iterative run; putting the same
            // wrappers OUTSIDE the dot-call chain would instead cross a charged edge.
            AssertFlatValue(DotCallChain(links: (max - 3) / 3, innerUnary: 2), 1m);               // 297 + 2 + 1 = max
            AssertFlatValue(DotCallChain(links: (max - 3) / 3, innerUnary: 1), 1m);               // depth max - 1
            AssertDepthRejected(DotCallChain(links: max / 3, innerUnary: 0));                     // 300 + 1 = max + 1

            // ── Parser-produced source reaching the same evaluation boundary ─
            // The parser's own chain guard caps a flat chain at 256 operators
            // (depth 259 through the engine), so the boundary is reached by bracket
            // nesting AROUND a maximal chain: engine depth = brackets + 256 + 3.
            AssertEngineBracketChain(brackets: max - 259 - 1, expectedValue: 257);                // depth max - 1
            AssertEngineBracketChain(brackets: max - 259, expectedValue: 257);                    // depth max
            var beyondSource = BracketChainSource(max - 259 + 1);                                 // depth max + 1
            var beyondParse = Parser.Parse(beyondSource);
            Assert.False(beyondParse.HasErrors);
            var beyondRun = KatLangEngine.Run(beyondSource);
            var beyondFailure = Assert.IsType<RunResult.EvalFailure>(beyondRun);
            Assert.Contains(
                beyondFailure.Errors,
                e => e.Message.Contains($"Structural AST depth limit of {max}", StringComparison.Ordinal));

            // ── Raw-syntax gate boundary (640, full-count profile) ──────────
            // Depths verified against the preflight's own counting: 49x12 -> 639,
            // 22x28 -> 640 parse RAWLY; 9x70 -> 641 is rejected by the raw gate.
            var rawAt = AstStructuralDepthTests.BracketChainComposition(levels: 22, chainOps: 28);
            Assert.False(Parser.ParseSyntax(rawAt).HasErrors);
            var rawBelow = AstStructuralDepthTests.BracketChainComposition(levels: 49, chainOps: 12);
            Assert.False(Parser.ParseSyntax(rawBelow).HasErrors);
            var rawBeyond = AstStructuralDepthTests.BracketChainComposition(levels: 9, chainOps: 70);
            var rawBeyondParse = Parser.ParseSyntax(rawBeyond);
            Assert.True(rawBeyondParse.HasErrors);
            Assert.Contains(
                rawBeyondParse.Diagnostics,
                d => d.Message.Contains(
                    $"structural AST depth limit of {AstStructuralPreflight.RawSyntaxMaxAstDepth}",
                    StringComparison.Ordinal));

            // Raw syntax between the elaboration gate and the raw gate parses rawly
            // but front-end ELABORATION rejects it with the structured elaboration
            // diagnostic — its rebuilding passes were measured to overflow a 1 MiB
            // thread between ~500 and ~626 nodes, so this rejection IS the fix.
            var elaborationGated = Parser.Parse(rawAt);
            Assert.True(elaborationGated.HasErrors);
            Assert.Contains(
                elaborationGated.Diagnostics,
                d => d.Message.Contains(
                    $"structural AST depth limit of {max}",
                    StringComparison.Ordinal));

            // The elaboration-gate boundary itself, on a semantically valid shape
            // (brackets around one maximal chain; parse depth = brackets + 258). The
            // engine wraps the parse root in one Block, so parse depth 299 evaluates
            // AT the evaluation ceiling (asserted with its value above), parse depth
            // 300 still elaborates but the evaluator's own gate rejects the wrapped
            // tree (asserted above as the max+1 engine case), and parse depth 301 is
            // rejected by the ELABORATION gate before any elaboration pass runs.
            var beyondElaboration = Parser.Parse(BracketChainSource(max - 259 + 2));
            Assert.True(beyondElaboration.HasErrors);
            Assert.Contains(
                beyondElaboration.Diagnostics,
                d => d.Message.Contains(
                    $"structural AST depth limit of {max}",
                    StringComparison.Ordinal));

            // ── Nested module chains through the real loader/front-end path ─
            // A 48-deep chain loads AND evaluates to its value on the 1 MiB baseline.
            var moduleResult48 = RunModuleChain(48);
            var moduleSuccess48 = Assert.IsType<RunResult.Success>(moduleResult48);
            Assert.Equal(new[] { 48m }, moduleSuccess48.Atoms);

            // The MAXIMUM permitted chain (64 nested loads) loads through the real
            // loader without any structural or parse failure; its 64-level property
            // recursion at runtime either completes or stops with the ESTABLISHED
            // dynamic invocation backstop (the CLR half-stack probe fires for 64
            // fat Debug frames on a bare 1 MiB thread) — never process death,
            // never a structural rejection.
            var moduleResult64 = RunModuleChain(64);
            if (moduleResult64 is RunResult.Success success64)
            {
                Assert.Equal(new[] { 64m }, success64.Atoms);
            }
            else
            {
                var failure64 = Assert.IsType<RunResult.EvalFailure>(moduleResult64);
                Assert.Contains(
                    failure64.Errors,
                    e => e.Message.Contains("protect the host stack", StringComparison.Ordinal)
                        || e.Message.Contains("recursion limit", StringComparison.Ordinal));
            }

            static RunResult RunModuleChain(int chainLength)
            {
                var modules = new Dictionary<string, string>(StringComparer.Ordinal);
                for (var k = 1; k < chainLength; k++)
                    modules[$"https://katlang.org/chain/m{k}.kat"] =
                        $"open 'https://katlang.org/chain/m{k + 1}.kat'\npublic X{k} = X{k + 1} + 1";
                modules[$"https://katlang.org/chain/m{chainLength}.kat"] = $"public X{chainLength} = 1";

                // In-memory downloader ValueTasks complete synchronously, so RunAsync
                // completes synchronously on this dedicated probe thread and GetResult
                // is plain result extraction, never a block.
                var task = KatLangEngine.RunAsync(
                    "open 'https://katlang.org/chain/m1.kat'\nX1",
                    new RunOptions { DownloadCode = (url, _) => ValueTask.FromResult(modules[url]) });
                Assert.True(task.IsCompleted);
                return task.GetAwaiter().GetResult();
            }
        });

        // ── The iterative-spine pin: a 384 KiB thread comfortably holds the
        // entry path's small-framed validation walk (~2 small frames per node) but
        // CANNOT hold ~300 recursive evaluation frames (~1.5 KB each in Release,
        // ~3 KB in Debug), so these succeeding is the deterministic proof that
        // spine evaluation is NOT depth-proportional.
        RunOnThreadWithStack(393_216, () =>
        {
            AssertFlatValue(AstStructuralDepthTests.UnarySpine(max), UnaryValue(max));
            AssertFlatValue(AstStructuralDepthTests.BinarySpine(max, leftDeep: true), max);
            AssertFlatValue(AstStructuralDepthTests.BinarySpine(max, leftDeep: false), max);
            AssertFlatValue(IndexSpine(max), 1m);
            AssertFlatValue(AstStructuralDepthTests.ListSpine(max), 1m);
        });

        WriteProbeMarker();

        static decimal UnaryValue(int totalNodes) => (totalNodes - 1) % 2 == 0 ? 1m : -1m;

        static Expr IndexSpine(int totalCountedNodes)
        {
            Expr expr = new Expr.Num(1);
            for (var i = 0; i < totalCountedNodes - 1; i++)
                expr = new Expr.Index(expr, new Expr.Num(0));
            return expr;
        }

        static Expr CallSpine(int levels, Expr? leaf = null)
            => AstStructuralDepthTests.CallSpine(levels, leaf);

        static Expr DotCallChain(int links, int innerUnary)
        {
            Expr expr = new Expr.Num(1);
            for (var i = 0; i < innerUnary; i++)
                expr = new Expr.Unary(UnaryOp.Minus, expr);
            for (var i = 0; i < links; i++)
                expr = new Expr.DotCall(expr, "count", null);
            return expr;
        }

        static string BracketChainSource(int brackets)
            => new string('[', brackets)
                + string.Join(" + ", Enumerable.Repeat("1", Parser.MaxExpressionChainDepth + 1))
                + new string(']', brackets);

        static void AssertEngineBracketChain(int brackets, decimal expectedValue)
        {
            var result = KatLangEngine.Run(BracketChainSource(brackets));
            var success = Assert.IsType<RunResult.Success>(result);
            Assert.Equal(new[] { expectedValue }, success.Atoms);
        }

        static void AssertFlatValue(Expr expr, decimal expected)
        {
            var result = Evaluator.RunFlat(expr);
            Assert.False(
                result.IsError,
                result.IsError ? $"Expected {expected} but got error: {result.Error}" : null);
            Assert.Equal(expected, Assert.Single(result.Value));
        }

        static void AssertDepthRejected(Expr expr)
        {
            var result = Evaluator.Run(expr);
            Assert.True(result.IsError);
            var error = Assert.IsType<EvalError.AstDepthLimitExceeded>(result.Error);
            Assert.Equal(EvaluationLimits.MaxSupportedAstDepth, error.Limit);
        }

        static void AssertValueOrEstablishedRuntimeStop(Expr expr, decimal expectedValue)
        {
            var result = Evaluator.RunFlat(expr);
            if (!result.IsError)
            {
                // A successful at-boundary call must produce the EXACT expected value —
                // an arbitrary success would hide a mis-evaluation behind the tolerance
                // for the runtime backstop.
                Assert.Equal(expectedValue, Assert.Single(result.Value));
                return;
            }

            // Established, controlled runtime outcomes only — never a structural
            // rejection of an accepted tree, never process termination.
            var leaf = result.Error;
            while (leaf is EvalError.WithContext(_, var inner))
                leaf = inner;
            Assert.True(
                leaf is EvalError.EvaluationStackExhausted or EvalError.EvaluationDepthExceeded,
                $"Unexpected at-boundary call outcome: {leaf.GetType().Name}");
        }
    }

    [Fact]
    public async Task DeepDiagnosticNames_AreBoundedDeterministically_InSubprocess()
        => await RunProbeChild("DeepDiagnosticNames_ProbeChild");

    /// <summary>
    /// The diagnostic-name rendering proof, on a dedicated 1 MiB thread: the
    /// evaluator gates deliberately accept arbitrarily long internal join/spread
    /// chains, so every path that renders an expression name — binary operand-shape
    /// contexts, call/dot-call contexts, open-form and property errors, and the
    /// sequence-pipeline optimizer's context — must stay iterative and
    /// output-bounded. Before the bounded renderer, every deep vector here
    /// terminated the process (call/dot-call contexts even on paths that would have
    /// SUCCEEDED, because they rendered eagerly).
    /// </summary>
    [Fact]
    public void DeepDiagnosticNames_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        const int deep = 50_000;
        var maxName = ExprNameRenderer.MaxRenderedNameLength + ExprNameRenderer.TruncationMarker.Length;

        RunOnThreadWithStack(1_048_576, () =>
        {
            // Ordinary-depth golden: the operand-shape context is byte-identical to
            // the former recursive renderer.
            var goldenJoin = new Expr.SequenceConstruct(
                new Expr.SequenceConstruct(new Expr.Num(1), new Expr.Num(2)), new Expr.Num(3));
            var golden = Evaluator.Run(new Expr.Binary(BinaryOp.Add, goldenJoin, new Expr.Num(1)));
            Assert.True(golden.IsError);
            Assert.Equal(
                "while evaluating `((1, 2), 3) + 1`",
                Assert.IsType<EvalError.WithContext>(golden.Error).ErrorContext.ToString());

            // 1. Binary operand-shape error over a deep join chain: bounded context,
            // deterministic elision, twice for reproducibility.
            var binary = new Expr.Binary(BinaryOp.Add, JoinChain(deep), new Expr.Num(1));
            var first = Evaluator.Run(binary);
            var second = Evaluator.Run(binary);
            Assert.True(first.IsError && second.IsError);
            var firstContext = Assert.IsType<EvalError.WithContext>(first.Error).ErrorContext.ToString();
            var secondContext = Assert.IsType<EvalError.WithContext>(second.Error).ErrorContext.ToString();
            Assert.Equal(firstContext, secondContext);
            Assert.Contains(ExprNameRenderer.TruncationMarker, firstContext, StringComparison.Ordinal);
            Assert.True(firstContext.Length <= maxName + "while evaluating ``".Length);

            // 2. Call whose callee is a deep join chain (context is error-path only).
            var callJoin = Evaluator.Run(new Expr.Call(JoinChain(deep), EmptyArgs()));
            Assert.True(callJoin.IsError);
            AssertBoundedContext(callJoin.Error, maxName);

            // 3. Call whose callee is a deep spread chain.
            var callSpread = Evaluator.Run(new Expr.Call(SpreadChain(deep), EmptyArgs()));
            Assert.True(callSpread.IsError);
            AssertBoundedContext(callSpread.Error, maxName);

            // 4. Dot-call SUCCESS on a deep join receiver: the dot-call context is
            // now DEFERRED, so no name is rendered at all — before the fix this
            // crashed even though evaluation succeeds.
            var dotSuccess = Evaluator.RunFlat(new Expr.DotCall(JoinChain(deep), "count", null));
            Assert.False(dotSuccess.IsError);
            Assert.Equal(deep + 2, Assert.Single(dotSuccess.Value));

            // 5. Dot-call ERROR on a deep join receiver: the unknown member falls
            // through structural lookup to the lexical fallback (UnknownName), and
            // the deferred dot-call context renders the receiver's name — bounded.
            var dotError = Evaluator.Run(new Expr.DotCall(JoinChain(deep), "noSuchMember", null));
            Assert.True(dotError.IsError);
            Assert.IsType<EvalError.UnknownName>(FindLeaf(dotError.Error));
            AssertBoundedContext(dotError.Error, maxName);

            // 6. Open-form error: a deep join chain used as an open target renders
            // through OpenExprName into BadOpenForm when a lookup walks the opens.
            var openError = Evaluator.Run(new Expr.AlgorithmExpr(new Algorithm.User(
                null, [], [JoinChain(deep)], [], [new Expr.Resolve("zzz")])));
            Assert.True(openError.IsError);
            var openLeaf = FindLeaf(openError.Error);
            var badOpenForm = Assert.IsType<EvalError.BadOpenForm>(openLeaf);
            Assert.True(KatLangError.FromEvalError(badOpenForm).Message.Length <= maxName + 128);

            // 7. Sequence-pipeline optimizer context over a deep join source:
            // source.filter(pred).count recognizes the pipeline and builds its
            // evaluation context through the same bounded renderer.
            var pipeline = new Expr.DotCall(
                new Expr.DotCall(
                    JoinChain(deep),
                    "filter",
                    new OutputBundle([new Expr.Binary(BinaryOp.Gt, new Expr.Param("x"), new Expr.Num(0))])),
                "count",
                null);
            var pipelineFirst = Evaluator.Run(pipeline);
            var pipelineSecond = Evaluator.Run(pipeline);
            Assert.True(pipelineFirst.IsError && pipelineSecond.IsError);
            var pipelineFirstMessage = KatLangError.FromEvalError(pipelineFirst.Error).Message;
            Assert.Equal(pipelineFirstMessage, KatLangError.FromEvalError(pipelineSecond.Error).Message);
            Assert.True(pipelineFirstMessage.Length <= 8_192);
        });

        WriteProbeMarker();

        static Expr JoinChain(int joins)
        {
            Expr chain = new Expr.SequenceConstruct(new Expr.Num(1), new Expr.Num(2));
            for (var i = 0; i < joins; i++)
                chain = new Expr.SequenceConstruct(chain, new Expr.Num(3));
            return chain;
        }

        static Expr SpreadChain(int spreads)
        {
            Expr chain = new Expr.Num(7);
            for (var i = 0; i < spreads; i++)
                chain = new Expr.SequenceSpread(chain);
            return chain;
        }

        static OutputBundle EmptyArgs() => OutputBundle.Empty;

        static EvalError FindLeaf(EvalError error)
        {
            while (error is EvalError.WithContext(_, var inner))
                error = inner;
            return error;
        }

        static void AssertBoundedContext(EvalError error, int maxName)
        {
            var withContext = Assert.IsType<EvalError.WithContext>(error);
            Assert.True(
                withContext.Context.Length <= maxName + 64,
                $"Unbounded context: {withContext.Context.Length} units");
        }
    }

    [Fact]
    public async Task PublicFrontEndBoundaries_RejectDeepHostAsts_InSubprocess()
        => await RunProbeChild("PublicFrontEndBoundaries_ProbeChild");

    /// <summary>
    /// The public front-end boundary proof, on a dedicated 1 MiB thread: the public
    /// <c>ParameterDetector.Detect</c>, <c>ImplicitArgumentResolver.Resolve</c>, and
    /// <c>ModuleLoader.Elaborate</c> APIs accept host-built ASTs directly, so each
    /// must return its established structured failure — never process death — for
    /// trees far beyond any CLR-safe recursion depth, while a pre-cancelled loader
    /// still honors cancellation first.
    /// </summary>
    [Fact]
    public void PublicFrontEndBoundaries_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        RunOnThreadWithStack(1_048_576, () =>
        {
            var max = EvaluationLimits.MaxSupportedAstDepth;

            // ParameterDetector.Detect: deep unary, binary, and pattern trees.
            foreach (var deepRoot in DeepRoots())
            {
                var (root, diagnostics) = ParameterDetector.Detect(deepRoot);
                Assert.Empty(root.Output);
                Assert.Contains(
                    diagnostics,
                    d => d.Message.Contains("structural AST depth limit", StringComparison.Ordinal));
            }

            // Exact boundary through the public API.
            var (_, atLimitDiags) = ParameterDetector.Detect(
                new Algorithm.User(null, [], [], [], [AstStructuralDepthTests.UnarySpine(max - 1)]));
            Assert.Empty(atLimitDiags);

            // ImplicitArgumentResolver.Resolve: established exception protocol.
            foreach (var deepRoot in DeepRoots())
                Assert.Throws<ArgumentException>(() => ImplicitArgumentResolver.Resolve(deepRoot));
            var resolved = ImplicitArgumentResolver.Resolve(
                new Algorithm.User(null, [], [], [], [AstStructuralDepthTests.UnarySpine(max - 1)]));
            Assert.NotEmpty(resolved.Output);

            // ModuleLoader.ElaborateAsync: placeholder + structured diagnostic at its
            // own measured ceiling, boundary-exact. Load-free spines walk
            // synchronously, so the ValueTasks complete synchronously on this thread.
            var loaderDiags = new List<Diagnostic>();
            var loader = new ModuleLoader(loaderDiags);
            var acceptedRoot = ElaborateSynchronously(loader, new Algorithm.User(
                null, [], [], [], [AstStructuralDepthTests.UnarySpine(ModuleLoader.MaxTraversalDepth - 1)]));
            Assert.Empty(loaderDiags);
            Assert.NotEmpty(acceptedRoot.Output);

            var rejectedRoot = ElaborateSynchronously(loader, new Algorithm.User(
                null, [], [], [], [AstStructuralDepthTests.UnarySpine(1_000_000)]));
            Assert.Empty(rejectedRoot.Output);
            Assert.Contains(
                loaderDiags,
                d => d.Message.Contains("structural AST depth limit", StringComparison.Ordinal));

            // Cyclic host roots: structured outcomes everywhere.
            var properties = new List<Property>();
            var cyclic = new Algorithm.User(null, [], [], properties, [new Expr.Num(1)]);
            properties.Add(new Property("Self", cyclic));
            var (_, cyclicDiags) = ParameterDetector.Detect(cyclic);
            Assert.NotEmpty(cyclicDiags);
            Assert.Throws<ArgumentException>(() => ImplicitArgumentResolver.Resolve(cyclic));

            // A pre-cancelled loader still honors cancellation FIRST, even for a
            // deep host AST (cancellation ordering is unchanged by the gate). The
            // pre-await cancellation check faults the returned ValueTask synchronously.
            using var cancelled = new CancellationTokenSource();
            cancelled.Cancel();
            var cancelledLoader = new ModuleLoader(
                [], downloadCode: null, allowedHosts: null, cancelled.Token);
            Assert.Throws<OperationCanceledException>(
                () => ElaborateSynchronously(cancelledLoader, new Algorithm.User(
                    null, [], [], [], [AstStructuralDepthTests.UnarySpine(1_000_000)])));
        });

        WriteProbeMarker();

        static IEnumerable<Algorithm> DeepRoots()
        {
            yield return new Algorithm.User(
                null, [], [], [], [AstStructuralDepthTests.UnarySpine(500_000)]);
            yield return new Algorithm.User(
                null, [], [], [], [AstStructuralDepthTests.BinarySpine(500_000, leftDeep: true)]);

            ParameterPattern pattern = new CaptureParameterPattern("x");
            for (var i = 0; i < 500_000; i++)
                pattern = new SequenceValueParameterPattern([pattern]);
            yield return new Algorithm.User(null, [], [], [], [new Expr.Num(1)]) with
            {
                ParameterPatterns = [pattern],
            };
        }
    }

    [Fact]
    public async Task ParserRecursionBudget_BoundsEveryGrammarShape_InSubprocess()
        => await RunProbeChild("ParserRecursionBudget_ProbeChild");

    /// <summary>
    /// The parser-safety proof, on a dedicated 1 MiB thread: every materially
    /// different recursive grammar shape at ONE BELOW, EXACTLY AT, and ONE BEYOND its
    /// maximum accepted level count under the ONE cumulative weighted parser
    /// recursion budget (<c>Parser.MaxNestingDepth</c> = 384 units; groups/blocks
    /// 4 units per level, lists/call arguments 3, prefix/pattern/power ~1). Below
    /// and at each boundary the source parses (and evaluates to its exact value
    /// where the later structural gates admit it); one beyond returns the
    /// established nesting diagnostic — never process death. Every accepted maximum
    /// here was ALSO proven to parse on a dedicated 512 KiB thread (half the
    /// documented envelope), so the deterministic budget, not the machine, is the
    /// binding constraint.
    /// </summary>
    [Fact]
    public void ParserRecursionBudget_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        RunOnThreadWithStack(1_048_576, () =>
        {
            static string Rep(string s, int count) => string.Concat(Enumerable.Repeat(s, count));

            static void AssertParses(string source)
            {
                var result = Parser.ParseSyntax(source);
                Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics));
                Assert.DoesNotContain(
                    result.Diagnostics,
                    d => d.Message.Contains(Parser.NestingTooDeepMessage, StringComparison.Ordinal));
            }

            static void AssertNestingRejected(string source)
            {
                var result = Parser.ParseSyntax(source);
                Assert.Contains(
                    result.Diagnostics,
                    d => d.Message.Contains(Parser.NestingTooDeepMessage, StringComparison.Ordinal));
            }

            static void AssertExpressionChainRejected(string source)
            {
                var result = Parser.ParseSyntax(source);
                Assert.Contains(
                    result.Diagnostics,
                    d => d.Message.Contains(
                        "Expression operator or postfix chain is too deep",
                        StringComparison.Ordinal));
            }

            static void AssertBoundary(Func<int, string> sourceAt, int max)
            {
                AssertParses(sourceAt(max - 1));
                AssertParses(sourceAt(max));
                AssertNestingRejected(sourceAt(max + 1));
            }

            // Groups, blocks: 4 units/level -> 95 levels max.
            AssertBoundary(n => Rep("(", n) + "1" + Rep(")", n), 95);
            AssertBoundary(n => "A = " + Rep("{", n) + "1" + Rep("}", n) + "\n1", 95);

            // Lists, call argument nesting: 3 units/level -> 127 levels max.
            AssertBoundary(n => Rep("[", n) + "1" + Rep("]", n), 127);
            AssertBoundary(n => "f(x) = x\n" + Rep("f(", n) + "1" + Rep(")", n), 127);

            // The omitted-dot graced call chain (`a~t(...)`) charges the same
            // 3 units/level but keeps one extra ParsePrimary frame LIVE under
            // each argument level (the dotted spelling pops ParsePrimary
            // before its dot continuation runs), so this dedicated
            // small-stack boundary is the proof that the added per-level
            // native frame stays inside the same budget capacity.
            AssertBoundary(n => "t(x) = x\n" + Rep("a~t(", n) + "1" + Rep(")", n), 127);

            // Prefix unary: ~1 unit/level.
            AssertBoundary(n => Rep("-", n) + "1", 382);

            // Power consumes the same recursive budget, but its completed AST is
            // also governed by the established 256-link expression-chain limit.
            AssertParses(Rep("1 ^ ", 255) + "1");
            AssertParses(Rep("1 ^ ", 256) + "1");
            AssertExpressionChainRejected(Rep("1 ^ ", 257) + "1");
            AssertNestingRejected(Rep("1 ^ ", 5_000) + "1");

            // Clause-head patterns: 1 unit/level.
            AssertBoundary(n => "F" + Rep("(", n) + "x" + Rep(")", n) + " = x\nF(1)", 384);

            // Mixed alternating containers: 11 units per ([{ cycle — the composed
            // shape a per-mechanism budget would wrongly admit.
            AssertBoundary(n => Rep("([{", n) + "1" + Rep("}])", n), 34);

            // Binary chains INSIDE every container level (the previously
            // composable-budget shape): chains parse iteratively, so the bracket
            // levels alone set the budget — 12-operator chains at each of 49
            // levels parse, while the same chains at 128 levels are rejected.
            AssertParses(AstStructuralDepthTests.BracketChainComposition(levels: 49, chainOps: 12));
            AssertNestingRejected(AstStructuralDepthTests.BracketChainComposition(levels: 128, chainOps: 12));

            // Deep malformed input recovers with structured diagnostics.
            AssertNestingRejected(Rep("(", 5_000) + "1");
            AssertNestingRejected(Rep("([{", 2_000) + "1");
            var malformed = Parser.ParseSyntax(Rep("(", 5_000) + "1");
            Assert.True(malformed.HasErrors);

            // At-boundary sources parse and EVALUATE to exact values through the
            // public engine wherever the later structural gates admit them.
            var parenValue = KatLangEngine.Run(Rep("(", 95) + "7" + Rep(")", 95));
            Assert.Equal(new[] { 7m }, Assert.IsType<RunResult.Success>(parenValue).Atoms);
            var bracketValue = KatLangEngine.Run(Rep("[", 120) + "3" + Rep("]", 120));
            Assert.Equal(new[] { 3m }, Assert.IsType<RunResult.Success>(bracketValue).Atoms);
            // 296 keeps the engine-wrapped tree just below the evaluation ceiling
            // (296 unary + Num + the two relevant engine wrapping nodes = 299).
            var unaryValue = KatLangEngine.Run(Rep("-", 296) + "1");
            Assert.Equal(new[] { 1m }, Assert.IsType<RunResult.Success>(unaryValue).Atoms);

            // The same budget protects every public parse surface: the raw
            // boundary, the elaborating front-end, and the engine.
            var beyond = Rep("(", 96) + "1" + Rep(")", 96);
            Assert.True(Parser.ParseSyntax(beyond).HasErrors);
            Assert.True(Parser.Parse(beyond).HasErrors);
            Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(beyond));
        });

        WriteProbeMarker();
    }

    [Fact]
    public async Task DeepNestedModuleChains_AreBoundedCumulatively_InSubprocess()
        => await RunProbeChild("DeepNestedModuleChains_ProbeChild");

    /// <summary>
    /// The cumulative nested-load proof, on a dedicated 1 MiB thread, through the
    /// REAL downloader/module-loader/front-end pipeline: each module in the chain
    /// places its next load underneath ~250 brace-block container levels, so nested
    /// elaboration would stack every ancestor module's traversal frames — tens of
    /// thousands of live frames from pure permitted source — without the cumulative
    /// guard. The guard must reject with the structured module-nesting diagnostic
    /// exactly where the budget crosses, while shallow chains, caching, failure
    /// recovery, and cancellation semantics stay intact.
    /// </summary>
    [Fact]
    public void DeepNestedModuleChains_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        RunOnThreadWithStack(1_048_576, () =>
        {
            // 1. Deep-nested chain through the engine: structured rejection. Each
            // module nests its next load under 60 brace levels (~125 counted
            // levels), so the cumulative budget crosses at the fifth module — while
            // every nested parse keeps a wide stack margin (module sizes are chosen
            // inside the parser's own bare-1-MiB envelope, a pre-existing bound this
            // loader guard cannot widen: a ~250-brace source exhausts a fresh 1 MiB
            // thread in the parser alone).
            var deepChain = RunEngineSynchronously(
                "open 'https://katlang.org/deep/m1.kat'\nX1",
                new RunOptions { DownloadCode = InMemoryDownloader(DeepChainModules(chain: 8, nest: 60)) });
            var deepFailure = Assert.IsType<RunResult.ParseFailure>(deepChain);
            // Rejected by the loader's cumulative accounting: with the parser's
            // stack-debt guard the third module's PARSE no longer fits above the
            // live traversal frames (both guard messages share this fragment).
            Assert.Contains(
                deepFailure.Errors,
                e => e.Message.Contains("cumulative structural", StringComparison.Ordinal));

            // 2. Shallow nested loads keep working end-to-end.
            var shallowChain = RunEngineSynchronously(
                "open 'https://katlang.org/deep/m1.kat'\nX1",
                new RunOptions { DownloadCode = InMemoryDownloader(DeepChainModules(chain: 3, nest: 4)) });
            var shallowSuccess = Assert.IsType<RunResult.Success>(shallowChain);
            Assert.Equal(new[] { 3m }, shallowSuccess.Atoms);

            // 3. Downloader failure during a depth-accounted nested load, followed
            // by successful reuse of the SAME loader run: the traversal base is
            // restored on unwind, nothing partial is cached, and the later
            // reference re-fetches and completes.
            var flakyCalls = new Dictionary<string, int>(StringComparer.Ordinal);
            string FlakyDownloader(string url)
            {
                var calls = flakyCalls.TryGetValue(url, out var seen) ? seen + 1 : 1;
                flakyCalls[url] = calls;
                if (url.EndsWith("flaky.kat", StringComparison.Ordinal) && calls == 1)
                    throw new InvalidOperationException("transient failure");
                return url.EndsWith("flaky.kat", StringComparison.Ordinal)
                    ? "public F = 41"
                    : "A = {open 'https://katlang.org/deep/flaky.kat'\nF}\nB = {open 'https://katlang.org/deep/flaky.kat'\nF}\npublic Y = B + 1";
            }

            var flakyDiags = new List<Diagnostic>();
            var flakyLoader = new ModuleLoader(flakyDiags, InMemoryDownloader(FlakyDownloader));
            var flakyParse = Parser.ParseSyntax("open 'https://katlang.org/deep/root.kat'\nY");
            Assert.False(flakyParse.HasErrors);
            ElaborateSynchronously(flakyLoader, flakyParse.SyntaxRoot);
            Assert.Contains(flakyDiags, d => d.Message.Contains("failed to fetch", StringComparison.Ordinal));
            Assert.Equal(2, flakyCalls["https://katlang.org/deep/flaky.kat"]);
            Assert.Equal(0, flakyLoader.InProgressModuleCount);
            Assert.Equal(2, flakyLoader.CachedModuleCount);

            // 4. Completed siblings stay cached and charged after a LATER rejection,
            // and the rejected module is fetched but never cached. Each deep module
            // nests its next load under 80 brace levels (322 parser units — well
            // inside the parser budget from a shallow site), so deep2's PARSE no
            // longer fits once deep1's live traversal frames impose their stack
            // debt: the chain stops at deep2 with the load-channel nesting message,
            // and deep3 is never fetched.
            var siblingCalls = new Dictionary<string, int>(StringComparer.Ordinal);
            string SiblingDownloader(string url)
            {
                siblingCalls[url] = siblingCalls.TryGetValue(url, out var seen) ? seen + 1 : 1;
                return url switch
                {
                    "https://katlang.org/deep/ok.kat" => "public K = 7",
                    "https://katlang.org/deep/deep1.kat" => NestedModule("D1", "deep2", "D2"),
                    "https://katlang.org/deep/deep2.kat" => NestedModule("D2", "deep3", "D3"),
                    "https://katlang.org/deep/deep3.kat" => "public D3 = 1",
                    _ => throw new InvalidOperationException(url),
                };

                static string NestedModule(string name, string next, string inner)
                    => $"public {name} = " + new string('{', 80)
                        + $"open 'https://katlang.org/deep/{next}.kat'\n{inner} + 1"
                        + new string('}', 80);
            }

            var siblingDiags = new List<Diagnostic>();
            var siblingLoader = new ModuleLoader(siblingDiags, InMemoryDownloader(SiblingDownloader));
            var siblingParse = Parser.ParseSyntax(
                "A = {open 'https://katlang.org/deep/ok.kat'\nK}\nB = {open 'https://katlang.org/deep/deep1.kat'\nD1}\nA");
            Assert.False(siblingParse.HasErrors);
            ElaborateSynchronously(siblingLoader, siblingParse.SyntaxRoot);
            Assert.Contains(
                siblingDiags,
                d => d.Message.Contains("cumulative structural", StringComparison.Ordinal)
                    && d.Message.Contains("deep2.kat", StringComparison.Ordinal));
            Assert.Equal(1, siblingCalls["https://katlang.org/deep/ok.kat"]);
            Assert.Equal(1, siblingCalls["https://katlang.org/deep/deep1.kat"]);
            Assert.Equal(0, siblingLoader.InProgressModuleCount);
            // ok and deep1 completed and stayed cached; deep2 was fetched once
            // (allowance and minimal parse budget were still positive, so the source
            // had to be fetched to be judged), rejected AT PARSE, and never cached;
            // deep3 was never requested.
            Assert.Equal(2, siblingLoader.CachedModuleCount);
            Assert.Equal(1, siblingCalls["https://katlang.org/deep/deep2.kat"]);
            Assert.False(siblingCalls.ContainsKey("https://katlang.org/deep/deep3.kat"));

            // 5. Cache hits splice WITHOUT re-fetching, re-traversing, or re-parsing:
            // the second reference sits under 90 brace levels, where a FRESH parse of
            // shared.kat (322 units) would no longer fit the debt-reduced parser
            // budget — the cache hit skips fetch, parse, and traversal entirely, so
            // no rejection fires and the downloader is called exactly once.
            var cacheCalls = new Dictionary<string, int>(StringComparer.Ordinal);
            string CacheDownloader(string url)
            {
                cacheCalls[url] = cacheCalls.TryGetValue(url, out var seen) ? seen + 1 : 1;
                return url.EndsWith("shared.kat", StringComparison.Ordinal)
                    ? "public S = " + new string('{', 80) + "5" + new string('}', 80)
                    : throw new InvalidOperationException(url);
            }

            var cacheDiags = new List<Diagnostic>();
            var cacheLoader = new ModuleLoader(cacheDiags, InMemoryDownloader(CacheDownloader));
            var cacheParse = Parser.ParseSyntax(
                "First = {open 'https://katlang.org/deep/shared.kat'\nS}\n"
                + "Second = " + new string('{', 90)
                + "open 'https://katlang.org/deep/shared.kat'\nS"
                + new string('}', 90) + "\nFirst");
            Assert.False(cacheParse.HasErrors);
            ElaborateSynchronously(cacheLoader, cacheParse.SyntaxRoot);
            Assert.DoesNotContain(
                cacheDiags,
                d => d.Message.Contains("cumulative structural", StringComparison.Ordinal));
            Assert.Equal(1, cacheCalls["https://katlang.org/deep/shared.kat"]);

            // 6. A load CYCLE keeps its established diagnostic (and cannot
            // double-charge: the cycle is rejected before any nested traversal).
            var cycleDiags = new List<Diagnostic>();
            var cycleLoader = new ModuleLoader(
                cycleDiags,
                InMemoryDownloader(url => url.EndsWith("c1.kat", StringComparison.Ordinal)
                    ? "open 'https://katlang.org/deep/c2.kat'\npublic C1 = 1"
                    : "open 'https://katlang.org/deep/c1.kat'\npublic C2 = 2"));
            var cycleParse = Parser.ParseSyntax("open 'https://katlang.org/deep/c1.kat'\nC1");
            Assert.False(cycleParse.HasErrors);
            ElaborateSynchronously(cycleLoader, cycleParse.SyntaxRoot);
            Assert.Contains(cycleDiags, d => d.Message.Contains("load cycle detected", StringComparison.Ordinal));
            Assert.Equal(0, cycleLoader.InProgressModuleCount);

            // 7. Cancellation during a depth-accounted nested load: the exception
            // propagates, run-local state unwinds, and a FRESH loader over the same
            // modules succeeds.
            using var cancelSource = new CancellationTokenSource();
            var cancelLoader = new ModuleLoader(
                [],
                (url, token) =>
                {
                    if (url.EndsWith("m2.kat", StringComparison.Ordinal))
                    {
                        cancelSource.Cancel();
                        token.ThrowIfCancellationRequested();
                    }

                    return ValueTask.FromResult(url.EndsWith("m1.kat", StringComparison.Ordinal)
                        ? "N1 = {open 'https://katlang.org/deep/m2.kat'\nN2 + 1}\npublic X1 = N1"
                        : "public N2 = 1");
                },
                allowedHosts: null,
                cancelSource.Token);
            var cancelParse = Parser.ParseSyntax("open 'https://katlang.org/deep/m1.kat'\nX1");
            Assert.False(cancelParse.HasErrors);
            Assert.Throws<OperationCanceledException>(
                () => ElaborateSynchronously(cancelLoader, cancelParse.SyntaxRoot));
            Assert.Equal(0, cancelLoader.InProgressModuleCount);

            var retryDiags = new List<Diagnostic>();
            var retryLoader = new ModuleLoader(
                retryDiags,
                InMemoryDownloader(url => url.EndsWith("m1.kat", StringComparison.Ordinal)
                    ? "N1 = {open 'https://katlang.org/deep/m2.kat'\nN2 + 1}\npublic X1 = N1"
                    : "public N2 = 1"));
            ElaborateSynchronously(retryLoader, cancelParse.SyntaxRoot);
            Assert.DoesNotContain(retryDiags, d => d.Severity == DiagnosticSeverity.Error);
            Assert.Equal(2, retryLoader.CachedModuleCount);

            // 8. A SHALLOW load site accepts a NEAR-BOUNDARY downloaded source: at a
            // top-level open the parser debt is a handful of units, so a module using
            // ~90 of its 95 brace-level capacity still parses, loads, and evaluates.
            var nearBoundary = RunEngineSynchronously(
                "open 'https://katlang.org/deep/near.kat'\nNB",
                new RunOptions
                {
                    DownloadCode = InMemoryDownloader(_ =>
                        "public NB = " + new string('{', 90) + "5" + new string('}', 90)),
                });
            Assert.Equal(new[] { 5m }, Assert.IsType<RunResult.Success>(nearBoundary).Atoms);

            // 9. A DEEPLY NESTED load site still accepts a SHALLOW module (the debt
            // shrinks the parse budget, it does not close it), while the SAME deep
            // site rejects a source that a shallow site accepts — the debt at work.
            var deepSitePrefix = "Deep = " + new string('{', 80)
                + "open 'https://katlang.org/deep/leafy.kat'\nLF"
                + new string('}', 80) + "\npublic X = 1";
            var deepSiteShallow = new List<Diagnostic>();
            var deepSiteLoader = new ModuleLoader(
                deepSiteShallow, InMemoryDownloader(_ => "public LF = 2"));
            var deepSiteParse = Parser.ParseSyntax(deepSitePrefix);
            Assert.False(deepSiteParse.HasErrors);
            ElaborateSynchronously(deepSiteLoader, deepSiteParse.SyntaxRoot);
            Assert.DoesNotContain(deepSiteShallow, d => d.Severity == DiagnosticSeverity.Error);

            var deepSiteDeep = new List<Diagnostic>();
            var deepSiteDeepLoader = new ModuleLoader(
                deepSiteDeep,
                InMemoryDownloader(_ => "public LF = " + new string('{', 80) + "2" + new string('}', 80)));
            ElaborateSynchronously(deepSiteDeepLoader, Parser.ParseSyntax(deepSitePrefix).SyntaxRoot);
            Assert.Contains(
                deepSiteDeep,
                d => d.Message.Contains("cumulative structural", StringComparison.Ordinal));
            Assert.Equal(0, deepSiteDeepLoader.CachedModuleCount);

            // 10. MALFORMED deep downloaded source: over-budget nesting inside a
            // module maps to the load-channel nesting message; ordinary garbage maps
            // to the invalid-source message. Neither is cached.
            var malformedDiags = new List<Diagnostic>();
            var malformedLoader = new ModuleLoader(
                malformedDiags,
                InMemoryDownloader(url => url.EndsWith("deepbad.kat", StringComparison.Ordinal)
                    ? new string('(', 5_000) + "1"
                    : "@@not katlang@@"));
            var malformedParse = Parser.ParseSyntax(
                "A = {open 'https://katlang.org/deep/deepbad.kat'\n1}\nB = {open 'https://katlang.org/deep/garbage.kat'\n1}\n1");
            Assert.False(malformedParse.HasErrors);
            ElaborateSynchronously(malformedLoader, malformedParse.SyntaxRoot);
            Assert.Contains(
                malformedDiags,
                d => d.Message.Contains("deepbad.kat", StringComparison.Ordinal)
                    && d.Message.Contains("too deeply to parse safely", StringComparison.Ordinal));
            Assert.Contains(
                malformedDiags,
                d => d.Message.Contains("garbage.kat", StringComparison.Ordinal)
                    && d.Message.Contains("not valid KatLang source", StringComparison.Ordinal));
            Assert.Equal(0, malformedLoader.CachedModuleCount);
            Assert.Equal(0, malformedLoader.InProgressModuleCount);

            // 11. A parser-budget rejection followed by SUCCESSFUL FRESH-LOADER reuse
            // of the same modules from a shallow site (the rejection is
            // position-dependent, and no partial module was cached).
            var reuseModules = InMemoryDownloader(
                _ => "public RB = " + new string('{', 80) + "9" + new string('}', 80));
            var reuseDeep = new List<Diagnostic>();
            var reuseDeepLoader = new ModuleLoader(reuseDeep, reuseModules);
            ElaborateSynchronously(reuseDeepLoader, Parser.ParseSyntax(
                "Deep = " + new string('{', 80)
                + "open 'https://katlang.org/deep/reuse.kat'\nRB"
                + new string('}', 80) + "\npublic X = 1").SyntaxRoot);
            Assert.Contains(
                reuseDeep,
                d => d.Message.Contains("cumulative structural", StringComparison.Ordinal));

            var reuseShallow = RunEngineSynchronously(
                "open 'https://katlang.org/deep/reuse.kat'\nRB",
                new RunOptions { DownloadCode = reuseModules });
            Assert.Equal(new[] { 9m }, Assert.IsType<RunResult.Success>(reuseShallow).Atoms);

            // 12. Source inspection requires one fetch: a module rejected by the
            // debt-reduced parse is downloaded exactly ONCE, rejected BEFORE any
            // recursive parse descends past the budget, and nothing beneath it is
            // ever requested. (The stricter pre-fetch short-circuit — no download at
            // all — additionally covers bases within a few levels of the traversal
            // ceiling, where even a minimal module could not parse.)
            var neverFetched = new HashSet<string>(StringComparer.Ordinal);
            string ShortCircuitDownloader(string url)
            {
                neverFetched.Add(url);
                return url switch
                {
                    "https://katlang.org/deep/sc1.kat" =>
                        "public S1 = " + new string('{', 80)
                            + "open 'https://katlang.org/deep/sc2.kat'\nS2 + 1"
                            + new string('}', 80),
                    _ => throw new InvalidOperationException(url),
                };
            }

            var shortCircuitDiags = new List<Diagnostic>();
            var shortCircuitLoader = new ModuleLoader(
                shortCircuitDiags, InMemoryDownloader(ShortCircuitDownloader));
            ElaborateSynchronously(shortCircuitLoader, Parser.ParseSyntax(
                "Deep = " + new string('{', 80)
                + "open 'https://katlang.org/deep/sc1.kat'\nS1"
                + new string('}', 80) + "\npublic X = 1").SyntaxRoot);
            Assert.Contains(
                shortCircuitDiags,
                d => d.Message.Contains("cumulative structural", StringComparison.Ordinal));
            Assert.Contains("https://katlang.org/deep/sc1.kat", neverFetched);
            Assert.DoesNotContain("https://katlang.org/deep/sc2.kat", neverFetched);
        });

        WriteProbeMarker();

        static Func<string, string> DeepChainModules(int chain, int nest)
        {
            var modules = new Dictionary<string, string>(StringComparer.Ordinal);
            for (var k = 1; k < chain; k++)
                modules[$"https://katlang.org/deep/m{k}.kat"] =
                    $"public X{k} = " + new string('{', nest)
                    + $"open 'https://katlang.org/deep/m{k + 1}.kat'\nX{k + 1} + 1"
                    + new string('}', nest);
            modules[$"https://katlang.org/deep/m{chain}.kat"] = $"public X{chain} = 1";
            return url => modules[url];
        }
    }
}
