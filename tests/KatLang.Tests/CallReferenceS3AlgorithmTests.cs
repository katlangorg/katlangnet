using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// META-S3-1 (October 2026): the public callable projection <c>R.Algorithm</c> of a call reference — the
/// captured invocation's callee as a transportable CALLABLE, independent of the invocation's original
/// argument supply (CR-13..CR-16; <c>docs/design/language-rules/call-by-need.md</c> § Callable projection).
/// Every source program runs through the public engine, and <see cref="Observe"/> requires the synchronous
/// generic and optimized evaluator routes and the async twin to give the SAME outcome, the SAME host effects
/// and the SAME semantic step count. Host operations count effects: <c>trace(x)</c> records <c>x</c> and
/// returns it, <c>tick()</c> returns how often it ran. Laziness, sharing and freshness are observed through
/// those effects, never through final values alone. Lean: <c>KatLangArityLaws/AlgorithmProjection.lean</c>
/// (laws) and <c>AlgorithmProjectionGuards.lean</c> (whole programs).
/// </summary>
public class CallReferenceS3AlgorithmTests
{
    private sealed class Effects
    {
        public readonly List<string> Traces = [];
        public int Ticks;

        public override string ToString() => $"traces=[{string.Join(",", Traces)}] ticks={Ticks}";
    }

    private static HostOperations Operations(Effects effects) => HostOperations.Create(
        HostOperation.Create("trace", (args, _) =>
        {
            lock (effects.Traces) effects.Traces.Add(SemanticExplorerHarness.Neutral(args[0]));
            return args[0];
        }, "x"),
        HostOperation.Create("tick", (_, _) => new Result.Atom(Interlocked.Increment(ref effects.Ticks))));

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

    private static string Describe(EvalError error) => $"err {KatLangError.FromEvalError(error).Code}: {Innermost(error)}";

    // The full diagnostic every route must agree on: the rendered message (context chain included) and span.
    private static string Detail(EvalResult<Evaluator.CountedResult> result)
        => result.IsOk ? "" : $"{KatLangError.FromEvalError(result.Error).Message} @{result.Error.Span}";

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
            RunResult.EvalFailure failure => failure.Errors[0].Source is { } error
                ? Describe(error)
                : $"err {failure.Errors[0].Code}: {failure.Errors[0].Message}",
            RunResult.ParseFailure parse => $"parse {parse.Errors[0].Code}: {parse.Errors[0].Message}",
            _ => run.GetType().Name,
        };
    }

    private static (string Outcome, long Steps, string Detail) Direct(string source, Effects effects, bool optimized,
        LoopOptimizationDiagnostics? loops = null)
    {
        var operations = Operations(effects);
        var (result, budget) = Evaluator.RunCountedObserved(Program(source, operations), enableOptimizations: optimized,
            loopDiagnostics: loops, hostOperations: operations);
        return (result.IsOk ? "ok " + SemanticExplorerHarness.Neutral(result.Value.Value) : Describe(result.Error),
            budget.ConsumedSteps, Detail(result));
    }

    private static (string Outcome, long Steps, string Detail) AsyncTwin(string source, Effects effects)
    {
        var operations = Operations(effects);
        var (result, budget) = Evaluator.RunCountedObservedAsync(Program(source, operations),
            zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
            hostOperations: operations).AsTask().WaitAsync(TimeSpan.FromSeconds(30)).GetAwaiter().GetResult();
        return (result.IsOk ? "ok " + SemanticExplorerHarness.Neutral(result.Value.Value) : Describe(result.Error),
            budget.ConsumedSteps, Detail(result));
    }

    /// <summary>
    /// The observation of <paramref name="source"/> on the public engine, after requiring the generic and
    /// optimized evaluator routes and the async twin to agree with it — outcome, host effects and steps.
    /// </summary>
    private static (string Outcome, Effects Effects) Observe(string source)
    {
        var engineEffects = new Effects();
        var engine = Engine(source, engineEffects);
        var genericEffects = new Effects();
        var generic = Direct(source, genericEffects, optimized: false);
        foreach (var (route, run) in new (string, Func<Effects, (string Outcome, long Steps, string Detail)>)[]
        {
            ("optimized", effects => Direct(source, effects, optimized: true)),
            ("async twin", effects => AsyncTwin(source, effects)),
        })
        {
            var effects = new Effects();
            var observed = run(effects);
            Assert.True(generic.Outcome == observed.Outcome, $"{route}: {observed.Outcome} vs generic {generic.Outcome}");
            Assert.True(generic.Steps == observed.Steps, $"{route}: {observed.Steps} steps vs generic {generic.Steps}");
            Assert.True(generic.Detail == observed.Detail, $"{route}: {observed.Detail} vs generic {generic.Detail}");
            Assert.Equal(genericEffects.ToString(), effects.ToString());
        }

        Assert.True(engine == generic.Outcome, $"engine {engine} vs generic {generic.Outcome}");
        Assert.Equal(genericEffects.ToString(), engineEffects.ToString());
        return (engine, engineEffects);
    }

    private const string Prelude = """
        Square(x) = trace(x) * x
        Inc(x) = x + 1
        Add(a, b) = a + b
        IsBig(x) = x > 1
        Capture(meta operation) = operation
        Apply(f, x) = f(x)
        Forward(f, x) = Apply(f, x)
        """;

    private static string Run(string body) => Observe(Prelude + "\n" + body).Outcome;

    private static (string Outcome, Effects Effects) Watch(string body) => Observe(Prelude + "\n" + body);

    private static string Arity(int expected, int actual) => $"err ArityMismatch: {expected}/{actual}";

    private static string TypeError(string message) => "err TypeMismatch: " + message;

    // ── CR-14 (c): a fresh call with exactly the new supply ──────────────────

    [Theory]
    [InlineData("R.Algorithm(8)", "ok 64")]
    [InlineData("(R.Algorithm)(8)", "ok 64")]
    [InlineData("R.Invoke()", "ok 25")]
    [InlineData("Apply(R.Algorithm, 7)", "ok 49")]
    [InlineData("Forward(R.Algorithm, 9)", "ok 81")]
    [InlineData("[1, 2, 3].map(R.Algorithm)", "ok L[1, 4, 9]")]
    [InlineData("R.Algorithm(R.Arguments*)", "ok 25")]
    public void TheBriefsExamples(string expression, string expected)
        => Assert.Equal(expected, Run("R = Capture(Square(5))\n" + expression));

    [Fact]
    public void AFreshCall_SuppliesExactlyTheNewArguments_TheCapturedArgumentIsNeverDemanded()
    {
        var (outcome, effects) = Watch("T(x) = x * 10\nR = Capture(T(trace(5)))\nR.Algorithm(2)");
        Assert.Equal("ok 20", outcome);
        Assert.Empty(effects.Traces);
    }

    [Fact]
    public void ZeroSupply_IsAFreshCallWithNoArguments_NeverTheCapturedInvocation()
    {
        var (outcome, effects) = Watch("R = Capture(Square(5))\nR.Algorithm()");
        Assert.Equal(Arity(1, 0), outcome);
        Assert.Empty(effects.Traces);
        Assert.Equal(Arity(1, 0), Run("R = Capture(Square(5))\n(R.Algorithm)()"));
    }

    [Fact]
    public void TheOriginalInvocation_StaysIndependent_AndReusesItsOneArgumentCell()
    {
        var (outcome, effects) = Watch("T(x) = trace(x) * 10\nR = Capture(T(trace(5)))\nR.Invoke(), R.Algorithm(2), R.Invoke()");
        Assert.Equal("ok S[50, 20, 50]", outcome);
        // The original argument `trace(5)` is demanded once (by the first Invoke); each target execution
        // traces its own bound value: 5 (argument) 5 (body), 2 (body), 5 (body).
        Assert.Equal(["5", "5", "2", "5"], effects.Traces);
    }

    [Fact]
    public void ProjectionAfterTheOriginalValueCompleted_PreservesThatValue()
    {
        var (outcome, effects) = Watch("Project(meta op) = op.Algorithm(8)\nAfter(x) = if(x > 0, (Project(x), x), 0)\nAfter(Square(5))");
        Assert.Equal("ok S[64, 25]", outcome);
        Assert.Equal(["5", "8"], effects.Traces);
    }

    [Fact]
    public void OriginalArgumentForwarding_TransportsTheOriginalCells_SharedWithInvoke()
    {
        var (outcome, effects) = Watch("T(x) = x * 10\nR = Capture(T(trace(5)))\nR.Algorithm(R.Arguments*), R.Invoke()");
        Assert.Equal("ok S[50, 50]", outcome);
        Assert.Equal(["5"], effects.Traces);
    }

    [Fact]
    public void ObtainingTheProjection_RunsNothingOfTheCapturedInvocation()
    {
        var (outcome, effects) = Watch("T(x) = trace(x) * 10\nR = Capture(T(trace(5)))\nIgnore(f) = 7\nIgnore(R.Algorithm)");
        Assert.Equal("ok 7", outcome);
        Assert.Empty(effects.Traces);
    }

    // ── Callbacks, loops and the META wrapper ───────────────────────────────

    [Theory]
    [InlineData("P = Capture(IsBig(0))\n[1, 2, 3].filter(P.Algorithm)", "ok L[2, 3]")]
    [InlineData("A = Capture(Add(0, 0))\n[1, 2, 3].reduce(A.Algorithm, 0)", "ok 6")]
    [InlineData("R = Capture(Square(5))\nEach(f, xs) = xs.map(f)\nEach(R.Algorithm, [2, 3])", "ok L[4, 9]")]
    [InlineData("R = Capture(Square(5))\nOuter(g) = [[1], [2]].map({ row.map(g) })\nOuter(R.Algorithm)", "ok L[L[1], L[4]]")]
    public void CallbacksAcceptTheProjection(string body, string expected) => Assert.Equal(expected, Run(body));

    [Fact]
    public void While_UsesTheOrdinaryConditionFirstLoop_AndTheOriginalArguments()
        => Assert.Equal("ok 3", Run("Step(x) = x + 1, x < 3\nR = Capture(Step(0))\nR.Algorithm.while(R.Arguments*)"));

    [Fact]
    public void Repeat_KeepsItsArgumentOrder()
        => Assert.Equal("ok 5", Run("Increment(x) = x + 1\nS = Capture(Increment(0))\nS.Algorithm.repeat(5, S.Arguments*)"));

    [Fact]
    public void AUserDefinedMetaWrapper_IsOrdinaryMetaCaptureDotCallAndLoop()
        => Assert.Equal("ok S[3, 3]", Run("""
            Step(x) = x + 1, x < 3
            Loop(meta operation) = operation.Algorithm.while(operation.Arguments*)
            Loop(Step(0)), Step(0).Loop
            """));

    [Fact]
    public void MultiStateLoops_KeepTheirOutputSlots()
        => Assert.Equal("ok S[S[34, 55, 1], S[34, 55, 1]]", Run("""
            Fib(a, b, n) = b, a + b, n - 1, n > 1
            R = Capture(Fib(0, 1, 10))
            R.Algorithm.while(R.Arguments*), Fib.while(0, 1, 10)
            """));

    [Fact]
    public void AFalseFirstContinuation_ReturnsTheIncomingState()
        => Assert.Equal("ok S[5, 5]", Run("Step(x) = x + 1, x < 3\nR = Capture(Step(5))\nR.Algorithm.while(R.Arguments*), Step.while(5)"));

    [Fact]
    public void TheOptimizedLoop_RecognizesAProjectedStep_WithoutChangingTheOutcome()
    {
        const string source = Prelude + "\nStep(x) = x + 1, x < 3\nR = Capture(Step(0))\nR.Algorithm.while(R.Arguments*)";
        var loops = new LoopOptimizationDiagnostics();
        var optimized = Direct(source, new Effects(), optimized: true, loops);
        Assert.Equal("ok 3", optimized.Outcome);
        Assert.Equal(1, loops.OptimizedLoopHits);
        Assert.Equal(optimized, Direct(source, new Effects(), optimized: false));
    }

    // ── Families and lexical ownership ──────────────────────────────────────

    [Fact]
    public void AFamily_IsRedispatchedByTheNewSupply_NeverFrozenToTheCapturedClause()
        => Assert.Equal("ok S[100, 6, 100]", Run("""
            F(0) = 100
            F(n) = n * 2
            R = Capture(F(0))
            R.Invoke(), R.Algorithm(3), R.Algorithm(0)
            """));

    [Fact]
    public void ANestedCallee_KeepsItsOwnersActivation_NotTheConsumersNames()
        => Assert.Equal("ok S[40, 40]", Run("""
            Outer(k) = {
              Scale(x) = x * k
              Capture(Scale(1))
            }
            Use(r) = {
              k = 1000
              Scale(x) = 0
              r.Algorithm(4)
            }
            O = Outer(10)
            Use(O), Apply(O.Algorithm, 4)
            """));

    [Fact]
    public void AParameterCallee_IsThatParametersOwnCell()
        => Assert.Equal("ok S[25, 49]", Run("""
            Hold(g) = Capture(g(5))
            R = Hold(Square)
            R.Invoke(), R.Algorithm(7)
            """));

    [Fact]
    public void ACalleeReachedThroughAnotherProjection_IsProjectedInItsCapturedContext()
        => Assert.Equal("ok S[4, 9, 16]", Run("""
            Mk(g) = Capture(g(5))
            R = Mk(Square)
            Q = Mk(R.Algorithm)
            S = Mk(Q.Algorithm)
            S.Algorithm(2), Q.Algorithm(3), Apply(S.Algorithm, 4)
            """));

    // ── CR-14 (b): bare VALUE is the callee's ordinary VALUE ─────────────────

    [Fact]
    public void BareValue_OfAParameterizedCallee_IsItsOrdinaryArityRejection()
        => Assert.Equal(Arity(1, 0), Run("R = Capture(Square(5))\nR.Algorithm"));

    [Fact]
    public void BareValue_OfAZeroParameterProperty_ReadsTheSharedPropertyCache()
    {
        var (outcome, effects) = Watch("Z = tick()\nR = Capture(Z())\nR.Algorithm, Z, R.Algorithm");
        Assert.Equal("ok S[1, 1, 1]", outcome);
        Assert.Equal(1, effects.Ticks);
        // The explicit fresh call evaluates the property's body again.
        var (fresh, freshEffects) = Watch("Z = tick()\nR = Capture(Z())\nR.Algorithm, R.Algorithm()");
        Assert.Equal("ok S[1, 2]", fresh);
        Assert.Equal(2, freshEffects.Ticks);
    }

    [Theory]
    [InlineData("[R.Algorithm]")]
    [InlineData("Apply(if(true, R.Algorithm, 0), 8)")]
    [InlineData("Keep(v) = v\nApply(Keep(R.Algorithm), 8)")]
    public void ComputedValues_NeverBecomeCallable(string body)
    {
        var outcome = Run("R = Capture(Square(5))\n" + body);
        Assert.True(outcome is "err ArityMismatch: 1/0" || outcome.StartsWith("err NotAnAlgorithm", StringComparison.Ordinal), outcome);
    }

    [Fact]
    public void ACapturedCalleeWithoutIdentity_IsReportedAsTheCapturedCallee()
        => Assert.Equal("err NotAnAlgorithm: " + Evaluator.CapturedCalleeDescription,
            Run("G(f) = Capture(f(1))\nR = G(5)\nR.Algorithm(2)"));

    // ── CR-15: one receiver for both channels of a written link ─────────────

    [Fact]
    public void BothChannelsOfOneLink_DecodeOneReceiverEvaluation()
    {
        var (outcome, effects) = Watch("""
            K(*xs) = count(xs)
            Sel(t) = if(trace(t) > 0, Capture(K(t)), Capture(K(t)))
            Both(f) = (f, f(7, 8))
            Both(Sel(1).Algorithm)
            """);
        Assert.Equal("ok S[0, 2]", outcome);
        Assert.Equal(["1"], effects.Traces);
    }

    [Fact]
    public void RepeatedCallableUses_OfOneLink_ShareItsReceiver()
    {
        var (outcome, effects) = Watch("""
            Mk(t) = if(trace(t) > 0, Capture(Square(t)), 0)
            Twice(f, x) = f(f(x))
            Twice(Mk(3).Algorithm, 2)
            """);
        Assert.Equal("ok 16", outcome);
        Assert.Equal(["3", "2", "4"], effects.Traces);
    }

    // ── CR-14 route: reservation, precedence, receivers ─────────────────────

    [Fact]
    public void ADeclaredMemberNamedAlgorithm_Wins_InEveryPosition()
        => Assert.Equal("ok S[7, 1001, 1002, 1003]", Run("""
            Box = { Algorithm = 7 }
            Lib = { Algorithm(x) = x + 1000 }
            Box.Algorithm, Lib.Algorithm(1), (Lib.Algorithm)(2), Apply(Lib.Algorithm, 3)
            """));

    [Fact]
    public void ALexicalAlgorithm_IsNeverAnExtensionFallback_ButAPlainCallStaysOrdinary()
    {
        Assert.Equal("ok 200", Run("Algorithm(x) = x * 100\nAlgorithm(2)"));
        Assert.Equal(TypeError(Evaluator.AlgorithmRequiresCallReferenceMessage(new Result.Atom(5))),
            Run("Algorithm(x) = x * 100\n5.Algorithm"));
    }

    [Fact]
    public void AnExplicitlySpreadReceiver_KeepsTheOrdinaryExtensionCall()
    {
        Assert.Equal("ok S[3, 3]", Run("Algorithm(a, b) = a + b\nKeep(v) = v\n(1, 2)*.Algorithm, Keep((1, 2)*.Algorithm)"));
    }

    [Fact]
    public void TheReservedEdge_IsNeverInferredAsAnImplicitParameter()
    {
        Assert.Equal("ok 9", Run("H = r.Algorithm(3)\nH(Capture(Square(5)))"));
        var parsed = Parser.Parse("G = R.Algorithm\nH = R.Algorithm(1)\nK = (R.Algorithm)(2)\nL = R.Algorithm.while(0)");
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        foreach (var name in new[] { "G", "H", "K" })
        {
            var property = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single(p => p.Name == name).Value);
            Assert.Equal(["R"], property.Parameters.Select(static p => p.Name));
        }
    }

    [Fact]
    public void FormulaLifting_ReadsTheProjectionsReceiverAsAValue()
        => Assert.Equal("ok 9", Run("Make(x) = Capture(Square(x))\nH = Make.Algorithm(3)\nH(2)"));

    [Fact]
    public void TheEditor_ClassifiesTheIntrinsicAndADeclaredMember()
    {
        var parsed = Parser.Parse("Capture(meta op) = op\nSq(x) = x * x\nR = Capture(Sq(5))\nBox = { Algorithm = 7 }\nR.Algorithm(2), Box.Algorithm");
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        var model = KatLang.Semantics.SemanticModelBuilder.Build(parsed);
        var sites = model.IdentifierResolutions.Where(static r => r.Occurrence.Name == AstHelpers.AlgorithmIntrinsicName && r.Occurrence.Span.Start.Line == 5)
            .OrderBy(static r => r.Occurrence.Span.Start.Column).ToList();
        Assert.Equal(2, sites.Count);
        // `R.Algorithm(2)`: a structural miss on a runtime receiver — the intrinsic.
        Assert.Equal(KatLang.Semantics.IdentifierClassification.Builtin, sites[0].Classification);
        Assert.Equal(AstHelpers.AlgorithmIntrinsicName, sites[0].ResolvedProperty!.Name);
        Assert.Null(sites[0].ResolvedDeclaration);
        // `Box.Algorithm`: the declared member wins.
        Assert.NotEqual(KatLang.Semantics.IdentifierClassification.Builtin, sites[1].Classification);
        Assert.NotNull(sites[1].ResolvedDeclaration);
    }

    [Theory]
    [InlineData("5.Algorithm")]
    [InlineData("'text'.Algorithm(1)")]
    [InlineData("[1, 2].Algorithm")]
    [InlineData("R = Capture(Square(5))\nR.Arguments.Algorithm(1)")]
    [InlineData("Inc(1).Algorithm(2)")]
    [InlineData("Apply(5.Algorithm, 1)")]
    public void AReceiverThatIsNotACallReference_IsATypeMismatch(string body)
        => Assert.StartsWith("err TypeMismatch: `Algorithm` requires a call reference", Run(body), StringComparison.Ordinal);

    [Fact]
    public void ACallReferenceStillNeverLeavesItsRun()
        => Assert.Equal(TypeError(Evaluator.CallReferenceLeavesRunMessage), Run("R = Capture(Square(5))\nKeep(r) = r\nKeep(R)"));

    // ── NEED-06 / NEED-09: cycles and failure provenance ────────────────────

    [Theory]
    [InlineData("R = Hold(R.Algorithm)\nR.Algorithm(1)")]
    [InlineData("R = Hold(R.Algorithm)\nApply(R.Algorithm, 1)")]
    [InlineData("R = Hold(R.Algorithm)\n(R.Algorithm)(1)")]
    [InlineData("R = Hold(R.Algorithm)\nR.Invoke()")]
    [InlineData("R1 = Hold(R2.Algorithm)\nR2 = Hold(R1.Algorithm)\nR1.Algorithm(1)")]
    [InlineData("Take(x) = x\nUse(x) = Apply(x.Algorithm, 0)\nR = Capture(Take(Use(R.Arguments*)))\nR.Invoke()")]
    [InlineData("Take(x) = x\nUse(x) = [0].map(x.Algorithm)\nR = Capture(Take(Use(R.Arguments*)))\nR.Invoke()")]
    [InlineData("Take(x) = x\nUse(x) = x.Algorithm.while(0)\nR = Capture(Take(Use(R.Arguments*)))\nR.Invoke()")]
    [InlineData("F(f) = f\nR = Capture(F(Q.Algorithm))\nQ = if(count([0].map(R.Arguments*)) > 0, Capture(Inc(0)), 0)\nApply(R.Arguments*, 1)")]
    public void ProjectionCycles_AreDemandCycle_OnEveryEngine(string body)
        => Assert.Equal("err DemandCycle: DemandCycle", Run("Hold(g) = Capture(g(0))\n" + body));

    [Theory]
    [InlineData("Apply(p.G, 0)", "err IllegalInEval: min requires a non-empty collection")]
    [InlineData("p.G(0)", "err IllegalInEval: min requires a non-empty collection")]
    [InlineData("(p.G)(0)", "err IllegalInEval: min requires a non-empty collection")]
    [InlineData("[1].map(p.G)", "err IllegalInEval: min requires a non-empty collection")]
    [InlineData("p.G.while(0)", "err IllegalInEval: min requires a non-empty collection")]
    [InlineData("Apply(p.G.H, 0)", "err IllegalInEval: min requires a non-empty collection")]
    public void AParameterRootedPathOverAFailingLink_KeepsTheFailure_NeverAbsence(string use, string expected)
        => Assert.Equal(expected, Run($"Bad = min([])\nUse(p) = {use}\nUse(Bad.Algorithm)"));

    [Theory]
    [InlineData("Use(5)", "err NotAnAlgorithm: param(f)")]
    [InlineData("Use(Inc(1))", "err NotAnAlgorithm: param(f)")]
    [InlineData("Box = { G(x) = x * 10 }\nUse(Box)", "ok 0")]
    public void StaticAbsence_IsUnchanged(string body, string expected)
        => Assert.Equal(expected, Run("Use(p) = Apply(p.G, 0)\n" + body));

    [Fact]
    public void ANonReferenceReceiver_IsAFailedProjection_NotAbsence()
        => Assert.StartsWith("err TypeMismatch: `Algorithm` requires a call reference",
            Run("Bad = 5\nUse(p) = Apply(p.G, 0)\nUse(Bad.Algorithm)"), StringComparison.Ordinal);

    // ── A property over the projection is a runtime-target alias (META-S3-2) ────

    [Theory]
    [InlineData("A = R.Algorithm\nA(9)", "ok 81")]
    [InlineData("A = R.Algorithm\nApply(A, 9)", "ok 81")]
    // Bare `A` is the alias's VALUE: the link's callee VALUE, exactly as before.
    [InlineData("A = R.Algorithm\nA", "err ArityMismatch: 1/0")]
    public void APropertyOverTheProjection_IsARuntimeAlias_WhoseBareReadIsItsValue(string body, string expected)
        => Assert.Equal(expected, Run("R = Capture(Square(5))\n" + body));

    // ── Run ownership (internal seam) ───────────────────────────────────────

    private static Result.CallReference CaptureFromRun(Action<Result.CallReference, Evaluator.EvalCtx>? whileRunning = null,
        string source = "Sq(x) = x * x\nGrab(Sq(5))")
    {
        Result.CallReference? captured = null;
        var operations = HostOperations.Create(
            HostOperation.Create("Grab", (_, _) => throw new InvalidOperationException("receiver missing"), "operation"));
        var experiment = new InvocationPlanTestSeam(new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>
        {
            ["Grab"] = cells =>
            {
                captured = Evaluator.ReifyMeta(cells[0]).Value;
                whileRunning?.Invoke(captured, captured.Plan.Caller);
                return new Result.Atom(0);
            },
        });
        using (InvocationPlanTestSeam.Activate(experiment))
        {
            var (result, _) = Evaluator.RunCountedObserved(Program(source, operations),
                hostOperations: operations);
            Assert.True(result.IsOk);
        }

        return Assert.IsType<Result.CallReference>(captured);
    }

    [Fact]
    public void AParameterCallee_TransportsTheExactOriginalCell()
    {
        CaptureFromRun((reference, ctx) =>
        {
            var supplied = Assert.IsType<NeedCell>(Evaluator.ParameterNeedCell("f", ctx));
            Assert.Same(supplied, reference.Plan.CalleeCell);
            Assert.False(supplied.HasCompletedValue);
            Assert.Null(reference.Plan.PreparedCells);
        }, "Sq(x) = x * x\nHold(f) = Grab(f(5))\nHold(Sq)");
    }

    [Fact]
    public void TheCalleeCell_IsCanonical_AndEstablishingItDemandsNothing()
    {
        CaptureFromRun((reference, ctx) =>
        {
            var plan = reference.Plan;
            Assert.False(plan.HasCalleeCell);
            var first = Evaluator.DecodeAlgorithmReceiver(reference, ctx);
            Assert.Same(plan, first.Value);
            var callee = plan.CalleeCell;
            Assert.Same(callee, plan.CalleeCell);
            Assert.False(callee.HasCompletedValue);
            Assert.Null(plan.PreparedCells);
            Assert.False(plan.Owner.HasCompletedValue);
            var projected = callee.ProjectCallable();
            Assert.True(projected.IsOk);
            Assert.NotNull(projected.Value);
            Assert.False(callee.HasCompletedValue);
            Assert.Null(plan.PreparedCells);
        });
    }

    [Fact]
    public void AForeignOrEndedRunsReference_IsRefusedBeforeAnyCalleeIsEstablished()
    {
        var reference = CaptureFromRun();
        var stranger = CaptureFromRun().Plan.Caller;
        var foreign = Evaluator.DecodeAlgorithmReceiver(reference, stranger);
        Assert.Equal(Evaluator.ForeignCallReferenceMessage, Assert.IsType<EvalError.IllegalInEval>(foreign.Error).Reason);
        var ended = Evaluator.DecodeAlgorithmReceiver(reference, reference.Plan.Caller);
        Assert.Equal(Evaluator.EndedCallReferenceMessage, Assert.IsType<EvalError.IllegalInEval>(ended.Error).Reason);
        Assert.False(reference.Plan.HasCalleeCell);
    }

    [Fact]
    public void AnArgumentView_IsNotDecodedAsAReference()
        => CaptureFromRun((reference, ctx) =>
            Assert.IsType<EvalError.TypeMismatch>(Evaluator.DecodeAlgorithmReceiver(reference.ArgumentView, ctx).Error));

    [Fact]
    public void ATerminalRun_EndsTheDecode_WithTheRetainedOutcome()
    {
        var reference = CaptureFromRun();
        var ctx = reference.Plan.Caller;
        var terminal = ctx.Budget.RetainTerminal(new EvalError.EvaluationStepLimitExceeded(1));
        Assert.Same(terminal, Evaluator.DecodeAlgorithmReceiver(reference, ctx).Error);
        Assert.False(reference.Plan.HasCalleeCell);
    }

    // ── META-free programs keep the lightweight ordinary route ──────────────

    [Fact]
    public void AMetaFreeProgram_HasNoRuntimeProjection()
    {
        const string source = "Box = { G(x) = x * 10 }\nUse(p) = Apply(p.G, 3)\nApply(f, x) = f(x)\nUse(Box), [1, 2].map(Box.G)";
        var operations = Operations(new Effects());
        var (result, budget) = Evaluator.RunCountedObserved(Program(source, operations), hostOperations: operations);
        Assert.Equal("S[30, L[10, 20]]", SemanticExplorerHarness.Neutral(result.Value.Value));
        Assert.False(budget.HasRuntimeProjections);
        Assert.False(budget.RetainsInvocationPlans);
    }

    [Fact]
    public void AStaticallyDeclaredAlgorithmMember_StaysIdentityOnly()
    {
        const string source = "Box = { Algorithm(x) = x * 10 }\nApply(f, x) = f(x)\nApply(Box.Algorithm, 3), [1, 2].map(Box.Algorithm)";
        var operations = Operations(new Effects());
        var (result, budget) = Evaluator.RunCountedObserved(Program(source, operations), hostOperations: operations);
        Assert.Equal("S[30, L[10, 20]]", SemanticExplorerHarness.Neutral(result.Value.Value));
        Assert.False(budget.HasRuntimeProjections);
        Assert.False(budget.RetainsInvocationPlans);
    }

    [Fact]
    public void AWrittenLink_MarksItsRunAsHavingRuntimeProjections()
    {
        const string source = Prelude + "\nR = Capture(Square(5))\nApply(R.Algorithm, 3)";
        var operations = Operations(new Effects());
        var (result, budget) = Evaluator.RunCountedObserved(Program(source, operations), hostOperations: operations);
        Assert.Equal("9", SemanticExplorerHarness.Neutral(result.Value.Value));
        Assert.True(budget.HasRuntimeProjections);
    }
}
