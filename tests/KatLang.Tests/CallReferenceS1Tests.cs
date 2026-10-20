using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

/// <summary>
/// CallReference S1 (October 2026): the <c>meta</c> parameter modifier, the run-scoped
/// <see cref="Result.CallReference"/> value, the <c>R.Invoke()</c> intrinsic and the J7 program gate of
/// invocation-plan retention. Every source program here parses cleanly and runs through the public engine,
/// and <see cref="Observe"/> additionally requires the synchronous generic and optimized evaluator routes and
/// the forced async twin to give the SAME outcome and the SAME host effects. Host operations count effects:
/// <c>tick()</c> returns how often it ran, <c>trace(x)</c> returns <c>x</c> and counts, <c>pair()</c> returns
/// <c>(1, 2)</c> and counts. Lean: <c>KatLangArityLaws/CallReference.lean</c> (laws) and
/// <c>CallReferenceGuards.lean</c> (the same programs, executable).
/// </summary>
public class CallReferenceS1Tests
{
    private sealed class Effects
    {
        public int Ticks;
        public int Traces;
        public int Pairs;

        public override string ToString() => $"ticks={Ticks} traces={Traces} pairs={Pairs}";
    }

    private static HostOperations Operations(Effects effects) => HostOperations.Create(
        HostOperation.Create("tick", (_, _) => { effects.Ticks++; return new Result.Atom(effects.Ticks); }),
        HostOperation.Create("trace", (args, _) => { effects.Traces++; return args[0]; }, "x"),
        HostOperation.Create("pair", (_, _) =>
        {
            effects.Pairs++;
            return new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2)]);
        }));

    private static string Describe(EvalError error)
    {
        var projected = KatLangError.FromEvalError(error);
        return $"err {projected.Code}: {Innermost(error)}";
    }

    private static string Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error switch
        {
            EvalError.TypeMismatch mismatch => mismatch.Message,
            EvalError.IllegalInEval illegal => illegal.Reason,
            EvalError.NotAnAlgorithm notAnAlgorithm => notAnAlgorithm.Description,
            EvalError.ArityMismatch arity => $"{arity.Expected}/{arity.Actual}",
            _ => error.GetType().Name,
        };
    }

    private static Expr Program(string source, HostOperations operations)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    private static string Engine(string source, Effects effects)
    {
        var run = KatLangEngine.Run(source, new RunOptions { HostOperations = Operations(effects) });
        return run switch
        {
            RunResult.Success success => "ok " + SemanticExplorerHarness.Neutral(success.Value),
            RunResult.EvalFailure failure => failure.Errors[0].Source is { } source1
                ? Describe(source1)
                : $"err {failure.Errors[0].Code}: {failure.Errors[0].Message}",
            RunResult.ParseFailure parse => $"parse {parse.Errors[0].Code}: {parse.Errors[0].Message}",
            _ => run.GetType().Name,
        };
    }

    private static string Direct(string source, Effects effects, bool optimized)
    {
        var operations = Operations(effects);
        var (result, _) = Evaluator.RunCountedObserved(Program(source, operations), enableOptimizations: optimized,
            hostOperations: operations);
        return result.IsOk ? "ok " + SemanticExplorerHarness.Neutral(result.Value.Value) : Describe(result.Error);
    }

    private static string AsyncTwin(string source, Effects effects)
    {
        var operations = Operations(effects);
        var (result, _) = Evaluator.RunCountedObservedAsync(Program(source, operations),
            zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
            hostOperations: operations).AsTask().GetAwaiter().GetResult();
        return result.IsOk ? "ok " + SemanticExplorerHarness.Neutral(result.Value.Value) : Describe(result.Error);
    }

    /// <summary>
    /// The observation of <paramref name="source"/> on the public engine, after requiring the generic and
    /// optimized evaluator routes and the async twin to agree with it — outcome and host effects.
    /// </summary>
    private static (string Outcome, Effects Effects) Observe(string source)
    {
        var engineEffects = new Effects();
        var engine = Engine(source, engineEffects);
        foreach (var (route, run) in new (string, Func<Effects, string>)[]
        {
            ("generic", effects => Direct(source, effects, optimized: false)),
            ("optimized", effects => Direct(source, effects, optimized: true)),
            ("async twin", effects => AsyncTwin(source, effects)),
        })
        {
            var effects = new Effects();
            Assert.True(engine == run(effects), $"{route}: {run(new Effects())} vs engine {engine}");
            Assert.Equal(engineEffects.ToString(), effects.ToString());
        }

        return (engine, engineEffects);
    }

    private const string Prelude = """
        Square(x) = x * x
        Capture(meta operation) = operation
        T(x) = x + tick()
        Add(a, b) = a + b
        Inc(x) = x + 1
        Ap(f, x) = f(x)
        """;

    // ── Syntax and AST ──────────────────────────────────────────────────────

    [Fact]
    public void MetaModifier_DeclaresAMetaCapture_InTheElaboratedSignature()
    {
        var parsed = Parser.Parse("Capture(meta operation) = operation\nCapture(Capture(1))");
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        var capture = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single(static p => p.Name == "Capture").Value);
        var parameter = Assert.IsType<CaptureParameterPattern>(Assert.Single(capture.ParameterPatterns));
        Assert.Equal("operation", parameter.Name);
        Assert.Equal(ParameterKind.Meta, parameter.Kind);
        Assert.Equal("meta operation", parameter.Parameter.DisplayName);
    }

    [Theory]
    [InlineData("F(meta) = meta + 1\nF(2)", "ok 3")]
    [InlineData("meta = 3\nmeta", "ok 3")]
    [InlineData("F(meta, x) = meta + x\nF(2, 3)", "ok 5")]
    [InlineData("F(x, meta) = x * meta\nF(2, 3)", "ok 6")]
    public void Meta_IsAContextualModifier_AnOrdinaryNameOtherwise(string source, string expected)
        => Assert.Equal(expected, Observe(source).Outcome);

    [Theory]
    [InlineData("F(meta *x) = 1\nF(1)")]
    [InlineData("F(meta (a, b)) = 1\nF((1, 2))")]
    [InlineData("F(meta [a]) = 1\nF([1])")]
    [InlineData("F(meta 1) = 1\nF(1)")]
    [InlineData("F((meta a, b)) = 1\nF((1, 2))")]
    [InlineData("F([meta a]) = 1\nF([1])")]
    [InlineData("F(meta x, x) = 1\nF(1, 1)")]
    [InlineData("F(0) = 0\nF(meta x) = 1\nF(1)")]
    [InlineData("F(meta x, 0) = 1\nF(1, 0)")]
    public void MisplacedMeta_IsTheInvalidMetaParameterDiagnostic(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.True(parsed.HasErrors);
        Assert.Contains(parsed.Diagnostics, static d => d.Code == DiagnosticCode.InvalidMetaParameter);
        var run = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        Assert.Contains(run.Errors, static e => e.Code == KatLangErrorCode.InvalidMetaParameter);
    }

    [Fact]
    public void HostBuiltMisplacedMeta_IsRefusedBeforeEvaluation()
    {
        static Expr Root(Algorithm bad) => new Expr.AlgorithmExpr(new Algorithm.User(
            Parent: null, ParameterPatterns: [], Opens: [],
            Properties: [new Property("Bad", bad)], Output: [new Expr.Num(0)]));
        var nested = new Algorithm.User(null,
            [new ListValueParameterPattern([new CaptureParameterPattern("x", Kind: ParameterKind.Meta)])],
            [], [], [new Expr.Num(1)]);
        var repeated = new Algorithm.User(null,
            [new CaptureParameterPattern("x", Kind: ParameterKind.Meta), new CaptureParameterPattern("x")],
            [], [], [new Expr.Num(1)]);
        var family = new Algorithm.Conditional(null, [], [
            new CondBranch(new Pattern.LitInt(0), new Algorithm.User(null, [], [], [], [new Expr.Num(0)])),
            new CondBranch(new Pattern.Bind("n") { ParameterKind = ParameterKind.Meta },
                new Algorithm.User(null, [], [], [], [new Expr.Num(1)])),
        ]);
        foreach (var bad in new Algorithm[] { nested, repeated, family })
        {
            var result = Evaluator.Run(Root(bad));
            Assert.True(result.IsError);
            var illegal = Assert.IsType<EvalError.IllegalInEval>(result.Error);
            Assert.Equal(Parser.InvalidMetaParameterDiagnostic, illegal.Reason);
        }
    }

    [Theory]
    [InlineData("bare")]
    [InlineData("flat")]
    [InlineData("list")]
    [InlineData("nested")]
    [InlineData("shared")]
    public void HostBuiltMetaClauseBinder_AtAnyDepth_IsRefusedBeforeEvaluation(string shape)
    {
        var meta = new Pattern.Bind("n") { ParameterKind = ParameterKind.Meta };
        var shared = new Pattern.SequenceValue([new Pattern.Bind("b"), meta]);
        Pattern head = shape switch
        {
            "bare" => meta,
            "flat" => new Pattern.SequenceValue([new Pattern.Bind("a"), meta]),
            "list" => new Pattern.ListValue([meta]),
            "nested" => new Pattern.SequenceValue([new Pattern.Bind("a"), new Pattern.SequenceValue([new Pattern.Bind("b"), meta])]),
            "shared" => new Pattern.SequenceValue([shared, shared]),
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        };
        // One head scan serves both clause-binder rules: the kind it looks for is the only difference.
        Assert.True(head.HeadHasBinderOfKind(ParameterKind.Meta));
        Assert.False(head.HeadHasBinderOfKind(ParameterKind.Collecting));
        var family = new Algorithm.Conditional(null, [], [
            new CondBranch(head, new Algorithm.User(null, [], [], [], [new Expr.Num(1)])),
        ]);
        var result = Evaluator.Run(new Expr.AlgorithmExpr(new Algorithm.User(
            Parent: null, ParameterPatterns: [], Opens: [],
            Properties: [new Property("Bad", family)], Output: [new Expr.Num(0)])));
        Assert.Equal(Parser.InvalidMetaParameterDiagnostic, Assert.IsType<EvalError.IllegalInEval>(result.Error).Reason);
    }

    [Fact]
    public void ClauseHeadScan_DistinguishesBinderKinds()
    {
        var collecting = new Pattern.Bind("xs") { ParameterKind = ParameterKind.Collecting };
        var ordinary = new Pattern.SequenceValue([new Pattern.Bind("a"), new Pattern.ListValue([new Pattern.Bind("b")])]);
        Assert.True(new Pattern.ListValue([new Pattern.Bind("a"), collecting]).HeadHasBinderOfKind(ParameterKind.Collecting));
        Assert.False(new Pattern.ListValue([new Pattern.Bind("a"), collecting]).HeadHasBinderOfKind(ParameterKind.Meta));
        Assert.False(ordinary.HeadHasBinderOfKind(ParameterKind.Meta));
        Assert.False(ordinary.HeadHasBinderOfKind(ParameterKind.Collecting));
        Assert.True(ordinary.HeadHasBinderOfKind(ParameterKind.Normal));
    }

    // ── Capture and Invoke ──────────────────────────────────────────────────

    [Fact]
    public void Capture_ThenInvoke_ExecutesTheOriginalCall()
        => Assert.Equal("ok S[25, 25]", Observe(Prelude + """

            R = Capture(Square(5))
            R.Invoke()
            R.Invoke()
            """).Outcome);

    [Fact]
    public void Capture_IsInert_NothingOfTheCallRuns()
    {
        var (outcome, effects) = Observe(Prelude + """

            R = Capture(T(trace(5)))
            K = [R, R]
            count(K)
            """);
        Assert.Equal("ok 2", outcome);
        Assert.Equal("ticks=0 traces=0 pairs=0", effects.ToString());
    }

    [Fact]
    public void RepeatedInvoke_ExecutesTheTargetAfresh_OverOneMemoizedArgument()
    {
        var (outcome, effects) = Observe(Prelude + """

            R = Capture(T(trace(5)))
            R.Invoke()
            R.Invoke()
            """);
        Assert.Equal("ok S[6, 7]", outcome);
        Assert.Equal("ticks=2 traces=1 pairs=0", effects.ToString());
    }

    [Fact]
    public void ValueBeforeMeta_ReusesTheCellsTheValueFormed()
    {
        var (outcome, effects) = Observe(Prelude + """

            Use(v) = v + Capture(v).Invoke()
            Use(T(trace(5)))
            """);
        Assert.Equal("ok 13", outcome);
        Assert.Equal("ticks=2 traces=1 pairs=0", effects.ToString());
    }

    [Fact]
    public void MetaBeforeValue_InOneHead_SharesOneArgumentCell()
    {
        var (outcome, effects) = Observe(Prelude + """

            Both(x, meta op) = op.Invoke() * 100 + x
            G(v) = Both(v, v)
            G(T(trace(5)))
            """);
        // The invocation (tick 1) runs before the ordinary VALUE of x (tick 2).
        Assert.Equal("ok 607", outcome);
        Assert.Equal("ticks=2 traces=1 pairs=0", effects.ToString());
    }

    [Fact]
    public void Forwarding_ThroughSeveralPlainParameters_ReachesTheOriginalPlan()
    {
        var (outcome, effects) = Observe(Prelude + """

            Fwd(y) = Capture(y)
            Fwd2(z) = Fwd(z)
            Same(w) = Fwd2(w) == Capture(w)
            Same(T(trace(5))), Fwd2(T(trace(5))).Invoke()
            """);
        Assert.Equal("ok S[true, 6]", outcome);
        Assert.Equal("ticks=1 traces=1 pairs=0", effects.ToString());
    }

    [Fact]
    public void DistinctCallCells_AreDistinctReferences_EvenWhenSpelledAlike()
        => Assert.Equal("ok S[false, true]", Observe(Prelude + """

            A = Capture(Square(5))
            B = Capture(Square(5))
            A == B, A == A
            """).Outcome);

    [Fact]
    public void ReferenceIdentity_FollowsThePropertyCache_AnExplicitCallCapturesANewCell()
        => Assert.Equal("ok S[true, false]", Observe(Prelude + """

            R = Capture(Square(5))
            R == R, R == R()
            """).Outcome);

    [Fact]
    public void References_AreTransportedByPropertiesCollectionsSelectionAndIf()
        => Assert.Equal("ok S[25, 25, 25, 25, 2, 1]", Observe(Prelude + """

            R = Capture(Square(5))
            L = [R, R]
            S = (R, 1)
            L[1].Invoke(), first(L).Invoke(), if(true, R, 0).Invoke(), S[0].Invoke()
            count(distinct([R, Capture(Square(5))]))
            count(distinct([R, R]))
            """).Outcome);

    [Fact]
    public void ValueReceiver_InvokesTheReferenceAComputationReturns()
        => Assert.Equal("ok 25", Observe(Prelude + "\nCapture(Square(5)).Invoke()").Outcome);

    [Fact]
    public void HigherOrderCallableArguments_KeepTheirIdentity_AndAreNeverDemanded()
        => Assert.Equal("ok S[2, 2]", Observe(Prelude + """

            R = Capture(Ap(Inc, 1))
            R.Invoke()
            R.Invoke()
            """).Outcome);

    [Fact]
    public void ClauseFamilies_AreDispatchedAfresh_ByTheOrdinaryDispatcher()
    {
        var (outcome, effects) = Observe(Prelude + """

            Sign(0) = 100
            Sign(n) = n
            Zero = Capture(Sign(trace(0)))
            Seven = Capture(Sign(trace(7)))
            Zero.Invoke(), Zero.Invoke(), Seven.Invoke()
            """);
        Assert.Equal("ok S[100, 100, 7]", outcome);
        Assert.Equal("ticks=0 traces=2 pairs=0", effects.ToString());
    }

    [Fact]
    public void TheCapturedCallee_ResolvesInTheCapturingContext_NeverAtTheInvokingSite()
        => Assert.Equal("ok 25", Observe(Prelude + """

            R = Capture(Square(5))
            Inner = {
                Square(x) = 0
                R.Invoke()
            }
            Inner
            """).Outcome);

    [Fact]
    public void AnArbitrarySpread_IsFormedOnce_ForEveryInvocation()
    {
        var (outcome, effects) = Observe(Prelude + """

            S = Capture(Add(pair()*))
            S.Invoke() + S.Invoke()
            """);
        Assert.Equal("ok 6", outcome);
        Assert.Equal("ticks=0 traces=0 pairs=1", effects.ToString());
    }

    [Fact]
    public void AFailingCapturedCall_FailsOnInvocation_WithItsOrdinaryError()
        => Assert.Equal("err DivisionByZero: DivByZero", Observe(Prelude + """

            Div(a, b) = a / b
            R = Capture(Div(1, 0))
            R.Invoke()
            """).Outcome);

    [Fact]
    public void AStickySpreadFailure_IsTheInvocationsFailure()
        => Assert.Equal("err DivisionByZero: DivByZero", Observe(Prelude + """

            Bad = 1 / 0, 2
            R = Capture(Add(Bad*))
            R.Invoke()
            """).Outcome);

    [Fact]
    public void ReentrantInvocation_ThroughTheArgument_IsADemandCycle()
        => Assert.Equal("err DemandCycle: DemandCycle", Observe(Prelude + """

            Id(x) = x
            R = Capture(Id(R.Invoke()))
            R.Invoke()
            """).Outcome);

    // ── Refusals and the capture domain ─────────────────────────────────────

    [Theory]
    [InlineData("Capture(5)")]
    [InlineData("Capture(Square)")]
    [InlineData("Y = Square(5)\nCapture(Y)")]
    [InlineData("R = Capture(Square(5))\nCapture(R)")]
    [InlineData("Box = { public F(x) = x }\nCapture(Box.F)")]
    [InlineData("Capture(5.Inc)")]
    [InlineData("Capture(1 + Square(2))")]
    [InlineData("Capture({ Square(2) })")]
    [InlineData("Again(meta op) = Capture(op)\nAgain(Square(5))")]
    public void NonCallSupplies_AreRefused_WithoutEvaluatingAnything(string body)
    {
        var (outcome, effects) = Observe(Prelude + "\n" + body);
        Assert.Equal("err NotAnAlgorithm: meta: not a supplied call computation", outcome);
        Assert.Equal("ticks=0 traces=0 pairs=0", effects.ToString());
    }

    /// <summary>
    /// META-S3-4 (CR-2): a written member or extension invocation — before S3-4 refused — is captured,
    /// inertly: nothing runs, and the reference it yields is refused only at the run boundary (CR-6).
    /// </summary>
    [Theory]
    [InlineData("Box = { public F(x) = x + tick() }\nCapture(Box.F(T(1)))")]
    [InlineData("Capture(5.Inc())")]
    [InlineData("Capture(T(5).Add(T(1)))")]
    public void WrittenDotInvocations_AreCaptured_WithoutEvaluatingAnything(string body)
    {
        var (outcome, effects) = Observe(Prelude + "\n" + body);
        Assert.Equal("err TypeMismatch: " + Evaluator.CallReferenceLeavesRunMessage, outcome);
        Assert.Equal("ticks=0 traces=0 pairs=0", effects.ToString());
    }

    [Fact]
    public void ARedundantGroup_IsTheCallItself()
        => Assert.Equal("ok 25", Observe(Prelude + "\nCapture((Square)(5)).Invoke()").Outcome);

    [Fact]
    public void AnAdapter_HasNoCallableIdentity()
        => Assert.Equal("err NotAnAlgorithm: param(op)", Observe(Prelude + """

            Again(meta op) = op(3)
            Again(Square(5))
            """).Outcome);

    [Fact]
    public void Cardinality_PrecedesMeta()
    {
        var (outcome, effects) = Observe(Prelude + "\nCapture(pair()*)");
        Assert.StartsWith("err ArityMismatch:", outcome, StringComparison.Ordinal);
        Assert.Equal(1, effects.Pairs);
    }

    [Fact]
    public void MetaRefusal_FollowsWrittenTraversalOrder()
    {
        Assert.Equal("err DivisionByZero: DivByZero", Observe(Prelude + """

            Mix([x], meta op) = x
            Mix(1 / 0, 25)
            """).Outcome);
        Assert.Equal("err NotAnAlgorithm: meta: not a supplied call computation", Observe(Prelude + """

            Mix2(meta op, [x]) = x
            Mix2(25, 1 / 0)
            """).Outcome);
    }

    // ── The Invoke intrinsic route ──────────────────────────────────────────

    [Fact]
    public void BareInvoke_IsRefused_AndNeverExecutes()
    {
        var (outcome, effects) = Observe(Prelude + "\nR = Capture(T(1))\nR.Invoke");
        Assert.Equal("err IllegalInEval: " + Evaluator.InvokeRequiresArgumentListMessage, outcome);
        Assert.Equal(0, effects.Ticks);
    }

    [Fact]
    public void Invoke_TakesNoReplacementArguments()
    {
        var (outcome, effects) = Observe(Prelude + "\nR = Capture(T(1))\nR.Invoke(8)");
        Assert.Equal("err ArityMismatch: 0/1", outcome);
        Assert.Equal(0, effects.Ticks);
    }

    [Fact]
    public void ScalarInvoke_IsTheIntrinsicsKindError_NeverALexicalExtension()
    {
        Assert.Equal("err TypeMismatch: `Invoke` requires a call reference, got numeric value 5",
            Observe("Invoke(r) = r + 1\n5.Invoke()").Outcome);
        Assert.Equal("err TypeMismatch: `Invoke` requires a call reference, got numeric value 5",
            Observe("Invoke(r) = r + 1\nX = 5\nX.Invoke()").Outcome);
        Assert.Equal("ok 5", Observe("Invoke(r) = r + 1\nInvoke(4)").Outcome);
    }

    [Fact]
    public void ADeclaredStructuralMember_WinsOverTheIntrinsic()
        => Assert.Equal("ok S[3, 8]", Observe("""
            Box = { public Invoke = 3 }
            Box2 = { public Invoke(x) = x * 2 }
            Box.Invoke, Box2.Invoke(4)
            """).Outcome);

    [Fact]
    public void Invoke_IsNeverInferredAsAnImplicitParameter()
    {
        var parsed = Parser.Parse(Prelude + "\nG = R.Invoke()\nR = Capture(Square(5))\nG",
            new RunOptions { HostOperations = Operations(new Effects()) });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        var g = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single(static p => p.Name == "G").Value);
        Assert.Empty(g.Parameters);
        // With R undeclared, R is the one inferred name: `Invoke` never joins the implicit parameters.
        var open = Parser.Parse("G = R.Invoke()\nG(5)");
        Assert.False(open.HasErrors, string.Join(Environment.NewLine, open.Diagnostics.Select(static d => d.Message)));
        var inferred = Assert.IsType<Algorithm.User>(open.Root.Properties.Single(static p => p.Name == "G").Value);
        Assert.Equal(["R"], inferred.Parameters.Select(static parameter => parameter.Name));
    }

    [Fact]
    public void FormulaLifting_GivesTheCallerAnOrdinaryBinding_ThatStillFeedsTheMetaSlot()
    {
        var source = Prelude + "\nH = Capture.Invoke()\nH(T(trace(5)))";
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = Operations(new Effects()) });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        var h = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single(static p => p.Name == "H").Value);
        Assert.Equal(ParameterKind.Normal, Assert.Single(h.Parameters).Kind);
        var (outcome, effects) = Observe(source);
        Assert.Equal("ok 6", outcome);
        Assert.Equal("ticks=1 traces=1 pairs=0", effects.ToString());
    }

    [Fact]
    public void ALoopStep_MayCapture_TheInitialStatesOriginalCall()
        => Assert.Equal("ok S[25, 25]", Observe(Prelude + """

            R = repeat(Capture(Square(5)), 1)
            R.Invoke(), R.Invoke()
            """).Outcome);

    // ── Boundaries ──────────────────────────────────────────────────────────

    [Theory]
    [InlineData("R")]
    [InlineData("[R]")]
    [InlineData("R, 1")]
    [InlineData("[[1, R]]")]
    [InlineData("(1, (2, R))")]
    public void ARunResultContainingAReference_IsRefusedAtTheRunBoundary(string rows)
        => Assert.Equal("err TypeMismatch: " + Evaluator.CallReferenceLeavesRunMessage,
            Observe(Prelude + "\nR = Capture(Square(5))\n" + rows).Outcome);

    [Theory]
    [InlineData("\"v={R}\"")]
    [InlineData("\"v={[1, R]}\"")]
    public void Interpolation_RefusesAReference(string row)
        => Assert.Equal("err TypeMismatch: " + Evaluator.CallReferenceHasNoTextMessage,
            Observe(Prelude + "\nR = Capture(Square(5))\n" + row).Outcome);

    [Theory]
    [InlineData("R + 1")]
    [InlineData("R < R")]
    [InlineData("if(R, 1, 2)")]
    [InlineData("sum([R])")]
    [InlineData("R.string")]
    [InlineData("not R")]
    public void OrdinaryOperations_RejectAReference_WithTheirKindVerdicts(string row)
    {
        var outcome = Observe(Prelude + "\nR = Capture(Square(5))\n" + row).Outcome;
        Assert.StartsWith("err ", outcome, StringComparison.Ordinal);
        Assert.DoesNotContain("25", outcome, StringComparison.Ordinal);
    }

    [Fact]
    public void AHostOperation_NeverReceivesAReference()
    {
        var (outcome, effects) = Observe(Prelude + "\nR = Capture(Square(5))\ntrace(R)");
        Assert.Equal("err TypeMismatch: " + Evaluator.CallReferenceLeavesRunMessage, outcome);
        Assert.Equal(0, effects.Traces);
        var (nested, nestedEffects) = Observe(Prelude + "\nR = Capture(Square(5))\ntrace([[R]])");
        Assert.Equal("err TypeMismatch: " + Evaluator.CallReferenceLeavesRunMessage, nested);
        Assert.Equal(0, nestedEffects.Traces);
    }

    [Fact]
    public async Task PublicEvaluatorEntryPoints_RefuseAReferenceResult()
    {
        var operations = Operations(new Effects());
        var root = Program(Prelude + "\nR = Capture(Square(5))\nR", operations);
        var direct = Evaluator.Run(root, operations, limits: null, randomSeed: null, CancellationToken.None);
        Assert.IsType<EvalError.TypeMismatch>(direct.Error);
        var flat = Evaluator.RunFlat(root, operations, limits: null, randomSeed: null, CancellationToken.None);
        Assert.IsType<EvalError.TypeMismatch>(flat.Error);
        var asynchronous = await Evaluator.RunAsync(root, operations, limits: null, randomSeed: null, CancellationToken.None);
        Assert.IsType<EvalError.TypeMismatch>(asynchronous.Error);
    }

    [Fact]
    public void AnInternalReference_DoesNotPreventAnOrdinaryResult()
        => Assert.Equal("ok S[25, 2, true]", Observe(Prelude + """

            R = Capture(Square(5))
            L = [R, R]
            R.Invoke(), count(L), contains(L, R)
            """).Outcome);

    // ── Run ownership and terminality ───────────────────────────────────────

    /// <summary>
    /// Captures <c>Sq(5)</c> inside a real run through the internal META receiver seam (no host code ever
    /// receives a reference) and returns that run's reference; the run itself finishes normally.
    /// </summary>
    private static Result.CallReference CaptureFromRun(CancellationToken token = default,
        Action<Result.CallReference>? whileRunning = null)
    {
        Result.CallReference? captured = null;
        var operations = HostOperations.Create(
            HostOperation.Create("Grab", (_, _) => throw new InvalidOperationException("receiver missing"), "operation"));
        var experiment = new InvocationPlanTestSeam(new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>
        {
            ["Grab"] = cells =>
            {
                captured = Evaluator.ReifyMeta(cells[0]).Value;
                whileRunning?.Invoke(captured);
                return new Result.Atom(0);
            },
        });
        using (InvocationPlanTestSeam.Activate(experiment))
        {
            var (result, _) = Evaluator.RunCountedObserved(Program("Sq(x) = x * x\nGrab(Sq(5))", operations),
                hostOperations: operations, cancellationToken: token);
            Assert.True(result.IsOk);
        }

        return Assert.IsType<Result.CallReference>(captured);
    }

    private static Evaluator.EvalCtx PlanCtx(CancellationToken token = default, EvaluationLimits? limits = null)
    {
        var budget = EvaluationBudget.Create(limits, cancellationToken: token);
        budget.DecideInvocationPlanRetention(programMayCapture: true);
        return Evaluator.EvalCtx.Empty with { Budget = budget };
    }

    [Fact]
    public void AReference_ExecutesInItsOwnRun()
    {
        CaptureFromRun(whileRunning: reference =>
        {
            var invoked = Evaluator.InvokeCallReferenceValue(reference, reference.Plan.Caller);
            Assert.True(invoked.IsOk);
            Assert.Equal(new Result.Atom(25), invoked.Value.Value);
        });
    }

    [Fact]
    public void AForeignRunsReference_IsRefused_AndRunsNothing()
    {
        var reference = CaptureFromRun();
        var preparedBefore = reference.Plan.Supply;
        var stranger = CaptureFromRun().Plan.Caller;
        var invoked = Evaluator.InvokeCallReferenceValue(reference, stranger);
        var illegal = Assert.IsType<EvalError.IllegalInEval>(invoked.Error);
        Assert.Equal(Evaluator.ForeignCallReferenceMessage, illegal.Reason);
        Assert.Same(preparedBefore, reference.Plan.Supply);
    }

    [Fact]
    public void ACancelledRun_CannotBeRevivedThroughAReference_TheOriginalTokenIsKept()
    {
        using var source = new CancellationTokenSource();
        var reference = CaptureFromRun(source.Token);
        var ctx = reference.Plan.Caller;
        source.Cancel();
        var cancelled = Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.InvokeCallReferenceValue(reference, ctx));
        Assert.Equal(source.Token, cancelled.CancellationToken);
    }

    [Fact]
    public void ATerminalRun_CannotBeRevivedThroughAReference_EvenAfterASuccessfulInvocation()
    {
        var reference = CaptureFromRun(whileRunning: reference =>
            Assert.True(Evaluator.InvokeCallReferenceValue(reference, reference.Plan.Caller).IsOk));
        var ctx = reference.Plan.Caller;
        var terminal = ctx.Budget.RetainTerminal(new EvalError.EvaluationStepLimitExceeded(1));
        var refused = Evaluator.InvokeCallReferenceValue(reference, ctx);
        Assert.Same(terminal, refused.Error);
    }

    [Fact]
    public void ARetainedRequiredSourceFailure_OrSourceCancellation_EndsEveryInvocation()
    {
        var reference = CaptureFromRun();
        var failing = reference.Plan.Caller;
        var sourceFailure = new EvalError.ModuleRegionMaterializationFailed([]);
        failing.Budget.RetainRequiredSourceFailure(sourceFailure);
        Assert.Same(sourceFailure, Evaluator.InvokeCallReferenceValue(reference, failing).Error);

        var other = CaptureFromRun();
        var cancelling = other.Plan.Caller;
        using var sourceTokens = new CancellationTokenSource();
        sourceTokens.Cancel();
        var original = new OperationCanceledException(sourceTokens.Token);
        cancelling.Budget.RetainRequiredSourceCancellation(original);
        var thrown = Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.InvokeCallReferenceValue(other, cancelling));
        Assert.Same(original, thrown);
        Assert.Equal(sourceTokens.Token, thrown.CancellationToken);
    }

    [Fact]
    public void AMetaCapture_InACancelledRun_CapturesNothing()
    {
        using var source = new CancellationTokenSource();
        var ctx = PlanCtx(source.Token);
        var cell = Evaluator.SupplyCell(new Expr.Call(new Expr.Resolve("count"), [new Expr.Num(1)]), ctx, []);
        source.Cancel();
        Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.ReferenceAdapterCell(cell, ctx));
        Assert.Null(((Evaluator.InvocationPlan)cell.Suspension!).Supply);
    }

    [Fact]
    public void ConcurrentMetaObservations_OfOneCell_ShareOneReference()
    {
        var ctx = PlanCtx();
        var cell = Evaluator.SupplyCell(new Expr.Call(new Expr.Resolve("count"), [new Expr.Num(1)]), ctx, []);
        var references = new Result.CallReference[64];
        Parallel.For(0, references.Length, i =>
        {
            var adapter = Evaluator.ReferenceAdapterCell(cell, ctx);
            Assert.True(adapter.Value.TryGetReadyValue(out var value));
            references[i] = Assert.IsType<Result.CallReference>(value.Value);
        });
        Assert.All(references, reference => Assert.Same(references[0], reference));
        Assert.Null(((Evaluator.InvocationPlan)cell.Suspension!).Supply);
    }

    [Fact]
    public void AMetaBinding_InARunWhoseGateDisabledPlans_FailsLoudly()
    {
        var budget = EvaluationBudget.Create(null);
        budget.DecideInvocationPlanRetention(programMayCapture: false);
        var ctx = Evaluator.EvalCtx.Empty with { Budget = budget };
        var cell = Evaluator.SupplyCell(new Expr.Call(new Expr.Resolve("count"), [new Expr.Num(1)]), ctx, []);
        if (budget.RetainsInvocationPlans)
            return; // the forced whole-suite plan mode (ForcedInvocationPlansHook) keeps plans on
        Assert.Throws<InvalidOperationException>(() => Evaluator.ReferenceAdapterCell(cell, ctx));
    }

    // ── J7: the program gate ────────────────────────────────────────────────

    private static bool Gate(string source, RunOptions? options = null)
    {
        var parsed = Parser.Parse(source, options);
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return Evaluator.ProgramMayCaptureCalls(new Expr.AlgorithmExpr(parsed.Root));
    }

    [Fact]
    public void Gate_AMetaFreeProgram_RetainsNoPlans()
    {
        Assert.False(Gate("F(x) = x + 1\nG = { H(y) = F(y) }\nF(G.H(1))"));
        var (result, budget) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid("F(x) = x + 1\nF(F(1))").Root));
        Assert.Equal(new Result.Atom(3), result.Value.Value);
        Assert.Equal(ForcedInvocationPlansHook.Forced, budget.RetainsInvocationPlans);
    }

    [Theory]
    [InlineData("Capture(meta op) = op\n1")]                               // declared, never called
    [InlineData("Outer = { Inner = { Capture(meta op) = op\n0 }\nInner }\nOuter")] // nested scope
    [InlineData("F(x) = { Capture(meta op) = op\nx }\nF(1)")]             // inside an uncalled-at-root body
    public void Gate_AnyWrittenMetaDeclaration_RetainsPlans(string source)
    {
        Assert.True(Gate(source));
        var observations = new EvaluationObservations();
        var (_, budget) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), observations: observations);
        Assert.True(budget.RetainsInvocationPlans);
    }

    [Fact]
    public async Task Gate_AnEagerlyImportedMetaDeclaration_RetainsPlans()
    {
        var options = new RunOptions
        {
            DownloadCode = (_, _) => ValueTask.FromResult("public Capture(meta op) = op"),
        };
        var parsed = await Parser.ParseAsync("open 'https://katlang.org/s1/capture.kat'\nSquare(x) = x * x\nCapture(Square(5)).Invoke()", options);
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        Assert.True(Evaluator.ProgramMayCaptureCalls(new Expr.AlgorithmExpr(parsed.Root)));
        var run = await KatLangEngine.RunAsync("open 'https://katlang.org/s1/capture.kat'\nSquare(x) = x * x\nCapture(Square(5)).Invoke()", options);
        Assert.Equal(new Result.Atom(25), Assert.IsType<RunResult.Success>(run).Value);
    }

    /// <summary>
    /// The J7 soundness case: a program with NO written META but a deferred module region retains plans,
    /// because the region's module may declare META. Here it does: the root supplies <c>Sq(trace(5))</c> to
    /// a clause family, whose first clause completes that cell's VALUE before the second clause's deferred
    /// module (declaring <c>Capture(meta op)</c>) is even fetched — and the module still captures the
    /// ORIGINAL cell with the supply its VALUE formed.
    /// </summary>
    [Fact]
    public async Task Gate_ADeferredRegion_RetainsPlans_SoALaterModulesMetaFindsTheOriginalCell()
    {
        var effects = new Effects();
        var downloads = 0;
        var options = new RunOptions
        {
            HostOperations = Operations(effects),
            DownloadCode = (_, _) => { downloads++; return ValueTask.FromResult("public Capture(meta op) = op"); },
        };
        const string source = """
            Sq(x) = trace(x) * x
            F(0) = 0
            F(v) = {
                open 'https://katlang.org/s1/deferred-capture.kat'
                Capture(v).Invoke() + v
            }
            F(Sq(5))
            """;
        var parsed = await Parser.ParseAsync(source, options);
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        Assert.Equal(0, downloads);
        Assert.False(Gate("Sq(x) = x * x\nF(0) = 0\nF(v) = v\nF(Sq(5))"));
        Assert.True(Evaluator.ProgramMayCaptureCalls(new Expr.AlgorithmExpr(parsed.Root)));

        var run = await KatLangEngine.RunAsync(source, options);
        Assert.Equal(new Result.Atom(50), Assert.IsType<RunResult.Success>(run).Value);
        Assert.Equal(1, downloads);
        Assert.Equal(2, effects.Traces); // the original VALUE, then one fresh invocation
    }

    [Fact]
    public void Gate_AHostAttachedParentScope_IsCovered()
    {
        var capture = new Algorithm.User(null, [new CaptureParameterPattern("op", Kind: ParameterKind.Meta)], [], [],
            [new Expr.Param("op")]);
        var parent = new ScopeCtx(Parent: null, Opens: [], Properties: [new Property("Capture", capture)]);
        var root = new Algorithm.User(parent, [], [], [], [new Expr.Num(1)]);
        Assert.True(Evaluator.ProgramMayCaptureCalls(new Expr.AlgorithmExpr(root)));
        var bare = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        Assert.False(Evaluator.ProgramMayCaptureCalls(new Expr.AlgorithmExpr(bare)));
    }

    [Fact]
    public void Gate_TheDecisionIsTakenOnce_AndNeverChanges()
    {
        var budget = EvaluationBudget.Create(null);
        budget.DecideInvocationPlanRetention(programMayCapture: true);
        Assert.True(budget.RetainsInvocationPlans);
        Assert.Throws<InvalidOperationException>(() => budget.DecideInvocationPlanRetention(programMayCapture: false));
        Assert.True(budget.RetainsInvocationPlans);
    }

    [Fact]
    public void Gate_MetaFreeRuns_CreateNoPlan_MetaPossibleRuns_PlanEveryCallShapedArgument()
    {
        const string body = "F(x) = x + 1\nF(F(F(1)))";
        var free = new EvaluationObservations();
        Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(body).Root), observations: free);
        var possible = new EvaluationObservations();
        Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(SourceProvenance.ParseValid("Unused(meta op) = op\n" + body).Root), observations: possible);
        Assert.Equal(ForcedInvocationPlansHook.Forced ? 2 : 0, free.InvocationPlanCount);
        Assert.Equal(2, possible.InvocationPlanCount);
    }

    // ── Optimizers under the gate ───────────────────────────────────────────

    [Fact]
    public void SuppliedPlainPipelineFusion_StaysEnabled_WhenTheGateDisablesPlans()
    {
        const string body = """
            Id(x) = x
            Id(count(filter(range(1, 200), {v > 100})))
            """;
        var free = new SequencePipelineDiagnostics();
        var (freeResult, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(body).Root), sequenceDiagnostics: free);
        var possible = new SequencePipelineDiagnostics();
        var (possibleResult, _) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid("Unused(meta op) = op\n" + body).Root), sequenceDiagnostics: possible);
        Assert.Equal(new Result.Atom(100), freeResult.Value.Value);
        Assert.Equal(new Result.Atom(100), possibleResult.Value.Value);
        if (!ForcedInvocationPlansHook.Forced)
            Assert.True(free.FilterCountFusionHits > 0);
        // The known S0 limitation: a META-possible run plans the supplied pipeline, which runs generically.
        Assert.Equal(0, possible.FilterCountFusionHits);
    }

    [Fact]
    public void PlannedLoops_StayPlanned_WhetherOrNotMetaIsPossible()
    {
        const string body = """
            Step(i, acc) = i + 1, acc + i
            repeat(Step(0, 0), 1000)
            """;
        foreach (var prefix in new[] { "", "Unused(meta op) = op\n" })
        {
            var loops = new LoopOptimizationDiagnostics();
            var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(prefix + body).Root), loopDiagnostics: loops);
            Assert.Equal("S[1000, 499500]", SemanticExplorerHarness.Neutral(result.Value.Value));
            Assert.True(loops.OptimizedLoopHits > 0, prefix.Length == 0 ? "META-free" : "META-possible");
        }
    }

    // ── Lean encoder ────────────────────────────────────────────────────────

    [Fact]
    public void LeanEncoder_SpellsAMetaCapture()
    {
        var parsed = Parser.Parse("Capture(meta op) = op\n1");
        Assert.False(parsed.HasErrors);
        var encoded = LeanAstEncoder.EncodeExpr(new Expr.AlgorithmExpr(parsed.Root));
        Assert.Contains("{ name := \"op\", kind := .metaRef }", encoded, StringComparison.Ordinal);
    }
}
