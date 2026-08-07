using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

/// <summary>
/// Regression coverage for the iterative, output-bounded diagnostic
/// expression-name renderer (<see cref="ExprNameRenderer"/>). The golden cases pin
/// byte-identical rendering for ordinary-depth names in every mode (the renderer
/// replaced per-mode RECURSIVE helpers, so these are the compatibility contract);
/// the deep cases pin stack safety, deterministic elision, and the output bound for
/// the shapes the evaluator's structural gates deliberately accept at any depth.
/// </summary>
public class ExprNameRendererTests
{
    private static string Open(Expr e) => ExprNameRenderer.Render(e, ExprNameMode.Open);
    private static string Diag(Expr e) => ExprNameRenderer.Render(e, ExprNameMode.DiagnosticName);

    private static Expr JoinChain(int joins)
    {
        Expr chain = new Expr.SequenceConstruct(new Expr.Num(1), new Expr.Num(2));
        for (var i = 0; i < joins; i++)
            chain = new Expr.SequenceConstruct(chain, new Expr.Num(3));
        return chain;
    }

    private static Expr SpreadChain(int spreads)
    {
        Expr chain = new Expr.Num(7);
        for (var i = 0; i < spreads; i++)
            chain = new Expr.SequenceSpread(chain);
        return chain;
    }

    // ── Golden byte-identity for ordinary-depth names ───────────────────────────

    [Fact]
    public void Golden_LeavesAndSimpleComposites_RenderExactly()
    {
        Assert.Equal("x", Open(new Expr.Resolve("x")));
        Assert.Equal("p", Open(new Expr.Param("p")));
        Assert.Equal("1.5", Open(new Expr.Num(1.5m)));
        Assert.Equal("-2", Open(new Expr.Num(-2m)));
        Assert.Equal("'s'", Open(new Expr.StringLiteral("s")));
        Assert.Equal("(inline library)", Open(new Expr.Block(new Algorithm.User(null, [], [], [], []))));
        Assert.Equal("()", Open(new Expr.EmptySequence(0)));
        Assert.Equal("((()))", Open(new Expr.EmptySequence(2)));
        Assert.Equal("(nativeCall)", Open(new Expr.NativeCall("sin", ["x"])));
    }

    [Fact]
    public void Golden_OperatorAndPostfixForms_RenderExactly()
    {
        var a = new Expr.Resolve("a");
        var b = new Expr.Resolve("b");

        // Unary operand wrapping: leaves and tighter-binding postfix forms stay bare.
        Assert.Equal("-a", Open(new Expr.Unary(UnaryOp.Minus, a)));
        Assert.Equal("not a", Open(new Expr.Unary(UnaryOp.Not, a)));
        Assert.Equal("-a.f", Open(new Expr.Unary(UnaryOp.Minus, new Expr.DotCall(a, "f", null))));
        Assert.Equal(
            "-((a + b))",
            Open(new Expr.Unary(UnaryOp.Minus, new Expr.Binary(BinaryOp.Add, a, b))));
        Assert.Equal("-(-a)", Open(new Expr.Unary(UnaryOp.Minus, new Expr.Unary(UnaryOp.Minus, a))));

        // Binary open names self-parenthesize.
        Assert.Equal("(a + b)", Open(new Expr.Binary(BinaryOp.Add, a, b)));
        Assert.Equal("(a div b)", Open(new Expr.Binary(BinaryOp.IDiv, a, b)));

        // Indexing renders postfix `target:selector` with rebinding-aware wrapping.
        Assert.Equal("a:0", Open(new Expr.Index(a, new Expr.Num(0))));
        Assert.Equal("(-a):(-1)", Open(new Expr.Index(
            new Expr.Unary(UnaryOp.Minus, a), new Expr.Num(-1m))));
        Assert.Equal("a:0:1", Open(new Expr.Index(
            new Expr.Index(a, new Expr.Num(0)), new Expr.Num(1))));
        Assert.Equal("a:(b:0)", Open(new Expr.Index(a, new Expr.Index(b, new Expr.Num(0)))));
        Assert.Equal("a:(b*)", Open(new Expr.Index(a, new Expr.SequenceSpread(b))));

        // Calls and dot-calls.
        var emptyArgs = new Algorithm.User(null, [], [], [], []);
        Assert.Equal("f(...)", Open(new Expr.Call(new Expr.Resolve("f"), emptyArgs)));
        Assert.Equal("a.f", Open(new Expr.DotCall(a, "f", null)));
        Assert.Equal("a.f(...)", Open(new Expr.DotCall(a, "f", emptyArgs)));

        // Grace prefix/postfix.
        Assert.Equal("~a", Open(new Expr.Grace(a, -1)));
        Assert.Equal("a~", Open(new Expr.Grace(a, 1)));

        // Spread: unary operands re-parenthesize, everything else stays bare.
        Assert.Equal("a*", Open(new Expr.SequenceSpread(a)));
        Assert.Equal("(-a)*", Open(new Expr.SequenceSpread(new Expr.Unary(UnaryOp.Minus, a))));

        // Lists and internal joins.
        Assert.Equal("[a, b]", Open(new Expr.ListLiteral([a, b])));
        Assert.Equal("[]", Open(new Expr.ListLiteral([])));
        Assert.Equal("(1, 2)", Open(new Expr.SequenceConstruct(new Expr.Num(1), new Expr.Num(2))));
    }

    [Fact]
    public void Golden_DiagnosticNameMode_RendersExactly()
    {
        var one = new Expr.Num(1);
        var two = new Expr.Num(2);

        // Top-level binary chains render bare, nested ones stay bare through the
        // chain (matching the former recursive ExprDiagnosticName).
        Assert.Equal("1 + 2", ExprNameRenderer.RenderBinaryDiagnosticName(BinaryOp.Add, one, two));
        Assert.Equal(
            "1 + 2 + 3",
            Diag(new Expr.Binary(BinaryOp.Add, new Expr.Binary(BinaryOp.Add, one, two), new Expr.Num(3))));

        // Zero-shape blocks render as one written sequence value over their outputs.
        Assert.Equal(
            "(1, 2)",
            Diag(new Expr.Block(new Algorithm.User(null, [], [], [], [one, two]))));
        Assert.Equal("()", Diag(new Expr.Block(new Algorithm.User(null, [], [], [], []))));

        // Internal joins render as one sequence value.
        Assert.Equal(
            "((1, 2), 3)",
            Diag(new Expr.SequenceConstruct(new Expr.SequenceConstruct(one, two), new Expr.Num(3))));

        // Everything else falls back to the Open spelling.
        Assert.Equal("a.f", Diag(new Expr.DotCall(new Expr.Resolve("a"), "f", null)));
    }

    [Fact]
    public void Golden_EvaluatorErrorMessages_AreUnchangedAtOrdinaryDepth()
    {
        // End-to-end pin through public evaluation: the binary operand-shape context
        // renders exactly as before the iterative renderer.
        var join = new Expr.SequenceConstruct(
            new Expr.SequenceConstruct(new Expr.Num(1), new Expr.Num(2)), new Expr.Num(3));
        var result = Evaluator.Run(new Expr.Binary(BinaryOp.Add, join, new Expr.Num(1)));
        Assert.True(result.IsError);
        var withContext = Assert.IsType<EvalError.WithContext>(result.Error);
        Assert.Equal("while evaluating `((1, 2), 3) + 1`", withContext.ErrorContext.ToString());
    }

    // ── Bounded, deterministic deep rendering ───────────────────────────────────

    public static TheoryData<string> DeepShapes => new(
        "join", "spread", "binaryLeft", "binaryRight", "unary", "index",
        "dotcall", "call", "gracePost", "list", "blockOutput");

    private static Expr BuildDeepShape(string shape, int levels)
    {
        Expr expr = new Expr.Num(1);
        for (var i = 0; i < levels; i++)
        {
            expr = shape switch
            {
                "join" => new Expr.SequenceConstruct(expr, new Expr.Num(1)),
                "spread" => new Expr.SequenceSpread(expr),
                "binaryLeft" => new Expr.Binary(BinaryOp.Add, expr, new Expr.Num(1)),
                "binaryRight" => new Expr.Binary(BinaryOp.Add, new Expr.Num(1), expr),
                "unary" => new Expr.Unary(UnaryOp.Minus, expr),
                "index" => new Expr.Index(expr, new Expr.Num(0)),
                "dotcall" => new Expr.DotCall(expr, "f", null),
                "call" => new Expr.Call(expr, new Algorithm.User(null, [], [], [], [])),
                "gracePost" => new Expr.Grace(expr, 1),
                "list" => new Expr.ListLiteral([expr]),
                "blockOutput" => new Expr.Block(new Algorithm.User(null, [], [], [], [expr])),
                _ => throw new InvalidOperationException(shape),
            };
        }

        return expr;
    }

    [Theory]
    [MemberData(nameof(DeepShapes))]
    public void DeepChains_RenderBoundedAndDeterministic_InEveryMode(string shape)
    {
        // 200,000 levels of every recursively renderable shape: the former recursive
        // renderers overflowed the process here; the engine must return a bounded,
        // reproducible name without depth-proportional stack.
        var deep = BuildDeepShape(shape, 200_000);
        foreach (var mode in new[]
        {
            ExprNameMode.Open, ExprNameMode.DiagnosticName, ExprNameMode.UnaryOperand,
            ExprNameMode.SpreadOperand, ExprNameMode.IndexTarget, ExprNameMode.IndexSelector,
        })
        {
            var first = ExprNameRenderer.Render(deep, mode);
            var second = ExprNameRenderer.Render(deep, mode);
            Assert.Equal(first, second);
            Assert.True(
                first.Length <= ExprNameRenderer.MaxRenderedNameLength + ExprNameRenderer.TruncationMarker.Length,
                $"{shape}/{mode} rendered {first.Length} units");

            // Every deep shape elides — except a block outside DiagnosticName mode,
            // which is an opaque "(inline library)" leaf by the established rules.
            if (shape != "blockOutput" || mode == ExprNameMode.DiagnosticName)
                Assert.EndsWith(ExprNameRenderer.TruncationMarker, first);
        }
    }

    [Fact]
    public void DeepChains_ThroughEvaluatorNameHelpers_AreBounded()
    {
        // The shared internal helpers used by the evaluator AND the optimizer reason
        // strings (LoopExprPlan, SequencePipelineOptimizer summaries) all route
        // through the same engine.
        var joined = Evaluator.OpenExprName(JoinChain(200_000));
        Assert.True(joined.Length <= ExprNameRenderer.MaxRenderedNameLength + 1);

        var spread = Evaluator.OpenExprName(SpreadChain(200_000));
        Assert.True(spread.Length <= ExprNameRenderer.MaxRenderedNameLength + 1);
    }

    [Fact]
    public void HostileLeafPayloads_AreCappedWithoutMaterializing()
    {
        // A giant identifier or literal is truncated at the bound.
        var bigName = new string('n', 100_000);
        var rendered = Open(new Expr.Resolve(bigName));
        Assert.Equal(
            bigName[..ExprNameRenderer.MaxRenderedNameLength] + ExprNameRenderer.TruncationMarker,
            rendered);

        var bigLiteral = Open(new Expr.StringLiteral(new string('s', 100_000)));
        Assert.True(bigLiteral.Length <= ExprNameRenderer.MaxRenderedNameLength + 1);
        Assert.StartsWith("'sss", bigLiteral);

        // EmptySequence depth is host-controlled: the former renderer materialized
        // 2*(depth+1) characters (or threw on negatives); the engine caps the run
        // and never allocates proportional storage.
        var hugeEmpty = Open(new Expr.EmptySequence(int.MaxValue));
        Assert.True(hugeEmpty.Length <= ExprNameRenderer.MaxRenderedNameLength + 1);
        var negativeEmpty = Open(new Expr.EmptySequence(-5));
        Assert.Equal(string.Empty, negativeEmpty);
    }

    [Fact]
    public void Truncation_DoesNotSplitValidUtf16SurrogatePairs()
    {
        // Put an astral scalar exactly across the 512-unit boundary. The old
        // substring-at-room implementation retained only its high surrogate and
        // therefore manufactured ill-formed UTF-16 in the diagnostic.
        var boundaryName = new string('n', ExprNameRenderer.MaxRenderedNameLength - 1)
            + "😀tail";
        var renderedName = Open(new Expr.Resolve(boundaryName));
        Assert.Equal(
            new string('n', ExprNameRenderer.MaxRenderedNameLength - 1)
                + ExprNameRenderer.TruncationMarker,
            renderedName);
        Assert.False(HasUnpairedSurrogate(renderedName));

        // The same boundary through the general text append path (the opening quote
        // has already consumed one unit before the string payload is appended).
        var boundaryLiteral = new string('s', ExprNameRenderer.MaxRenderedNameLength - 2)
            + "😀tail";
        var renderedLiteral = Open(new Expr.StringLiteral(boundaryLiteral));
        Assert.EndsWith(ExprNameRenderer.TruncationMarker, renderedLiteral);
        Assert.False(HasUnpairedSurrogate(renderedLiteral));

        static bool HasUnpairedSurrogate(string text)
        {
            for (var i = 0; i < text.Length; i++)
            {
                if (char.IsHighSurrogate(text[i]))
                {
                    if (i + 1 >= text.Length || !char.IsLowSurrogate(text[++i]))
                        return true;
                }
                else if (char.IsLowSurrogate(text[i]))
                {
                    return true;
                }
            }

            return false;
        }
    }

    [Fact]
    public void WideCollections_AreConsumedLazilyWithinTheWorkBound()
    {
        // A public AST can carry any IReadOnlyList implementation. Count is
        // intentionally enormous and high indexes throw: an eager reverse-push loop
        // touches int.MaxValue - 1 before rendering one character, while the indexed
        // cursor needs only the small visible prefix justified by the 512-unit cap.
        var wideItems = new VirtualWideExprList();
        var list = Open(new Expr.ListLiteral(wideItems));
        Assert.EndsWith(ExprNameRenderer.TruncationMarker, list);
        Assert.True(list.Length <= ExprNameRenderer.MaxRenderedNameLength + 1);
        Assert.InRange(wideItems.MaxAccessedIndex, 0, 1_000);

        var wideOutput = new VirtualWideExprList();
        var block = Diag(new Expr.Block(new Algorithm.User(
            null, [], [], [], wideOutput)));
        Assert.EndsWith(ExprNameRenderer.TruncationMarker, block);
        Assert.True(block.Length <= ExprNameRenderer.MaxRenderedNameLength + 1);
        Assert.InRange(wideOutput.MaxAccessedIndex, 0, 1_000);
    }

    [Fact]
    public void InBoundNames_NeverCarryTheTruncationMarker()
    {
        // A name that fits the bound renders fully — elision is deterministic and
        // only ever appears past the bound.
        var chain = JoinChain(20);
        var rendered = Open(chain);
        Assert.DoesNotContain(ExprNameRenderer.TruncationMarker, rendered);
        Assert.StartsWith("(((", rendered);
        Assert.EndsWith(", 3)", rendered);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SuccessfulResolvedCalls_DoNotRenderDiagnosticNames_InEitherEvaluationMode(
        bool enableOptimizations)
    {
        var ordinary = new Expr.Call(
            new Expr.Resolve("count"),
            Arguments(new Expr.ListLiteral([new Expr.Num(1), new Expr.Num(2)])));
        var dotted = new Expr.DotCall(
            new Expr.ListLiteral([new Expr.Num(1), new Expr.Num(2)]),
            "count",
            null);

        foreach (var (expression, expected) in new (Expr Expression, decimal Expected)[]
        {
            (ordinary, 2m),
            (dotted, 2m),
        })
        {
            var flatObservations = new EvaluationObservations();
            var flat = Evaluator.RunObserved(expression, flatObservations, enableOptimizations);
            Assert.False(flat.IsError);
            Assert.Equal([expected], flat.Value.ToAtoms());
            Assert.Equal(0, flatObservations.CallDiagnosticNameRenderCount);

            var countedObservations = new EvaluationObservations();
            var (counted, _) = Evaluator.RunCountedObserved(
                expression,
                enableOptimizations: enableOptimizations,
                observations: countedObservations);
            Assert.False(counted.IsError);
            Assert.Equal([expected], counted.Value.Value.ToAtoms());
            Assert.Equal(1, counted.Value.EmittedCount);
            Assert.Equal(0, countedObservations.CallDiagnosticNameRenderCount);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SuccessfulDeepCompoundCallee_DoesNotRenderDiagnosticName(
        bool enableOptimizations)
    {
        const int joins = 50_000;
        var call = SuccessfulComplexCalleeCall(joins);

        var flatObservations = new EvaluationObservations();
        var flat = Evaluator.RunObserved(call, flatObservations, enableOptimizations);
        Assert.False(flat.IsError);
        Assert.Equal([joins + 2m], flat.Value.ToAtoms());
        Assert.Equal(0, flatObservations.CallDiagnosticNameRenderCount);

        var countedObservations = new EvaluationObservations();
        var (counted, _) = Evaluator.RunCountedObserved(
            call,
            enableOptimizations: enableOptimizations,
            observations: countedObservations);
        Assert.False(counted.IsError);
        Assert.Equal([joins + 2m], counted.Value.Value.ToAtoms());
        Assert.Equal(1, counted.Value.EmittedCount);
        Assert.Equal(0, countedObservations.CallDiagnosticNameRenderCount);
    }

    [Fact]
    public void SuccessfulFusedPipeline_DoesNotRenderDiagnosticContext()
    {
        var parse = Parser.Parse("B(x) = x > 5\nrange(1, 10).filter(B).count");
        Assert.False(parse.HasErrors);
        var diagnostics = new SequencePipelineDiagnostics();
        var observations = new EvaluationObservations();

        var (result, _) = Evaluator.RunCountedObserved(
            new Expr.Block(parse.Root),
            enableOptimizations: true,
            sequenceDiagnostics: diagnostics,
            observations: observations);

        Assert.False(result.IsError);
        Assert.Equal([5m], result.Value.Value.ToAtoms());
        Assert.Equal(1, diagnostics.GetSnapshot().FilterCountFusionHits);
        Assert.Equal(0, observations.CallDiagnosticNameRenderCount);
    }

    [Fact]
    public void OrdinaryAndDottedFailures_RetainExactDiagnosticNamesAndText()
    {
        var receiver = JoinChain(2);
        var compoundFunction = new Expr.DotCall(receiver, "count", null);
        var ordinaryFailure = new Expr.Call(compoundFunction, Arguments(new Expr.Num(9)));
        var ordinaryName = Open(compoundFunction);
        var ordinaryObservations = new EvaluationObservations();

        var ordinary = Evaluator.RunObserved(ordinaryFailure, ordinaryObservations);
        Assert.True(ordinary.IsError);
        var ordinaryContext = Assert.IsType<EvalError.WithContext>(ordinary.Error);
        Assert.Equal(
            $"while evaluating call to {ordinaryName}",
            ordinaryContext.ErrorContext.ToString());
        var ordinaryArity = Assert.IsType<EvalError.ArityMismatch>(ordinaryContext.Inner);
        Assert.Equal(ordinaryName, ordinaryArity.Signature?.DisplayText);
        Assert.Equal(
            $"Callable `{ordinaryName}` expects 0 arguments, but was called with 1 argument.",
            KatLangError.FromEvalError(ordinary.Error).Message);
        Assert.Equal(2, ordinaryObservations.CallDiagnosticNameRenderCount);

        var dottedFailure = new Expr.DotCall(receiver, "take", Arguments());
        var receiverName = Open(receiver);
        var dottedObservations = new EvaluationObservations();
        var dotted = Evaluator.RunObserved(dottedFailure, dottedObservations);
        Assert.True(dotted.IsError);
        var dottedContext = Assert.IsType<EvalError.WithContext>(dotted.Error);
        Assert.Equal(
            $"while evaluating dotCall .take of {receiverName}",
            dottedContext.ErrorContext.ToString());
        Assert.IsType<EvalError.ArityMismatch>(dottedContext.Inner);
        Assert.Equal(
            $"Property 'take' on `{receiverName}` expects 2 parameters, but was called with 1 argument.",
            KatLangError.FromEvalError(dotted.Error).Message);
        Assert.Equal(1, dottedObservations.CallDiagnosticNameRenderCount);
    }

    [Fact]
    public void ResourceLimitError_DoesNotRenderCompoundCalleeName()
    {
        var observations = new EvaluationObservations();
        var (result, _) = Evaluator.RunCountedObserved(
            SuccessfulComplexCalleeCall(joinCount: 50),
            limits: new EvaluationLimits { MaxCollectionItems = 1 },
            observations: observations);

        Assert.True(result.IsError);
        Assert.True(result.Error.IsResourceLimit);
        Assert.Equal(0, observations.CallDiagnosticNameRenderCount);
    }

    [Fact]
    public void SuccessfulComplexCallee_CallHeavyAllocationMeasurement()
    {
        const int iterations = 2_000;
        var call = SuccessfulComplexCalleeCall(joinCount: 50);

        // Warm the exact path before measuring. This is an informational focused
        // measurement, not a permanent machine-dependent allocation ceiling.
        for (var i = 0; i < 20; i++)
            Assert.False(Evaluator.Run(call).IsError);

        GC.Collect();
        GC.WaitForPendingFinalizers();
        GC.Collect();
        var before = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < iterations; i++)
            Assert.False(Evaluator.Run(call).IsError);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Console.WriteLine(
            $"successful-complex-callee allocation: {allocated} bytes / {iterations} calls "
            + $"({allocated / (double)iterations:F1} bytes/call)");
    }

    private static Expr SuccessfulComplexCalleeCall(int joinCount)
    {
        var receiver = JoinChain(joinCount);
        var callableDotExpression = new Expr.DotCall(receiver, "count", null);
        return new Expr.Call(
            callableDotExpression,
            new Algorithm.User(null, [], [], [], []));
    }

    private static Algorithm Arguments(params Expr[] expressions)
        => new Algorithm.User(null, [], [], [], expressions);

    private sealed class VirtualWideExprList : IReadOnlyList<Expr>
    {
        public int MaxAccessedIndex { get; private set; } = -1;

        public int Count => int.MaxValue;

        public Expr this[int index]
        {
            get
            {
                if (index > 10_000)
                    throw new InvalidOperationException("Renderer accessed beyond its bounded visible prefix.");

                MaxAccessedIndex = Math.Max(MaxAccessedIndex, index);
                return new Expr.Num(1);
            }
        }

        public IEnumerator<Expr> GetEnumerator()
            => throw new InvalidOperationException("Renderer must use the indexed bounded cursor.");

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator()
            => GetEnumerator();
    }
}
