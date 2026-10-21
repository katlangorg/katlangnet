using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// CallReference S2 (October 2026): the lazy, read-only ARGUMENT VIEW <c>R.Arguments</c> of a call reference —
/// obtaining it, <c>count</c>, selection, <c>first</c>/<c>last</c> and the cell-preserving argument spread
/// <c>F(R.Arguments*)</c>. Every source program parses cleanly and runs through the public engine, and
/// <see cref="Observe"/> additionally requires the synchronous generic and optimized evaluator routes and the
/// forced async twin to give the SAME outcome and the SAME host effects. Host operations count effects:
/// <c>trace(x)</c> returns <c>x</c> and counts, <c>pair()</c> returns <c>(1, 2)</c> and counts, <c>tick()</c>
/// returns how often it ran. Laziness is observed through those counts and through the plans' prepared
/// supplies, never through final values alone. Lean: <c>KatLangArityLaws/ArgumentView.lean</c> (laws) and
/// <c>ArgumentViewGuards.lean</c> (the same programs, executable).
/// </summary>
public class CallReferenceS2Tests
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
        Add(x, y) = x + y
        Mul(x, y) = x * y
        First(x, y) = x
        Apply(f, x) = f(x)
        Square(x) = x * x
        Id(x) = x
        Capture(meta operation) = operation
        """;

    private static string Run(string body) => Observe(Prelude + "\n" + body).Outcome;

    private static (string Outcome, Effects Effects) Watch(string body) => Observe(Prelude + "\n" + body);

    private static string TypeError(string message) => "err TypeMismatch: " + message;

    // ── The brief's examples ────────────────────────────────────────────────

    [Theory]
    [InlineData("R.Arguments.count", "ok 2")]
    [InlineData("count(R.Arguments)", "ok 2")]
    [InlineData("R.Arguments[0]", "ok 10")]
    [InlineData("R.Arguments[1]", "ok 20")]
    [InlineData("R.Arguments[0, 1]", "ok S[10, 20]")]
    [InlineData("R.Arguments[1, 0, 1]", "ok S[20, 10, 20]")]
    [InlineData("R.Arguments.first", "ok 10")]
    [InlineData("R.Arguments.last", "ok 20")]
    [InlineData("first(R.Arguments)", "ok 10")]
    [InlineData("last(R.Arguments)", "ok 20")]
    [InlineData("R.Invoke()", "ok 30")]
    [InlineData("Mul(R.Arguments*)", "ok 200")]
    [InlineData("Mul(R.Arguments*), R.Invoke()", "ok S[200, 30]")]
    public void TheBriefsExamples(string row, string expected)
        => Assert.Equal(expected, Run("R = Capture(Add(10, 20))\n" + row));

    [Fact]
    public void TheView_IsLazy_CountReadsTheSupply_SelectionDemandsOnlyTheSelectedCell()
    {
        const string capture = "R = Capture(Add(trace(10), trace(20)))\n";
        Assert.Equal(("ok 2", 0), Traces(capture + "R.Arguments.count"));
        Assert.Equal(("ok 10", 1), Traces(capture + "R.Arguments[0]"));
        Assert.Equal(("ok 10", 1), Traces(capture + "R.Arguments[0] + R.Arguments[0] - R.Arguments[0]"));
        Assert.Equal(("ok S[10, 20]", 2), Traces(capture + "R.Arguments[0], R.Arguments[1]"));
        Assert.Equal(("ok 20", 1), Traces(capture + "R.Arguments.last"));
        Assert.Equal(("ok 2", 0), Traces(capture + "A = R.Arguments\nA.count"));

        static (string, int) Traces(string body)
        {
            var (outcome, effects) = Watch(body);
            return (outcome, effects.Traces);
        }
    }

    [Fact]
    public void ObtainingTheView_PreparesNothing_AndRunsNothing()
    {
        var (outcome, effects) = Watch("R = Capture(Add(pair()*))\nA = R.Arguments\nA == A, R == A");
        Assert.Equal("ok S[true, false]", outcome);
        Assert.Equal(0, effects.Pairs);
    }

    // ── Capture and view formation ──────────────────────────────────────────

    [Fact]
    public void TheView_OfAReferenceWhoseValueCompleted_StillProvidesTheOriginalArguments()
    {
        var (outcome, effects) = Watch("""
            Use(v) = v + Capture(v).Arguments[0] * 100
            Use(Add(trace(1), 2))
            """);
        Assert.Equal("ok 103", outcome);
        Assert.Equal(1, effects.Traces);
        Assert.Equal("ok S[30, 2]", Run("R = Capture(Add(10, 20))\nR.Invoke(), R.Arguments.count"));
    }

    [Fact]
    public void TheView_SeesThroughForwardingHops()
        => Assert.Equal("ok S[2, 1, 2]", Run("""
            Fwd(y) = Capture(y)
            Fwd2(z) = Fwd(z)
            R = Fwd2(Add(1, 2))
            R.Arguments.count, R.Arguments[0], R.Arguments.last
            """));

    [Fact]
    public void ViewIdentity_IsStable_PerReference_AndFollowsThePropertyCache()
        => Assert.Equal("ok S[true, true, false, false, false]", Run("""
            R = Capture(Add(1, 2))
            A = R.Arguments
            A == R.Arguments, R.Arguments == R.Arguments, R == R.Arguments, R().Arguments == R.Arguments, [R.Arguments] == [R]
            """));

    [Fact]
    public void ZeroArguments_CountZero_AndNoFirstPosition()
    {
        Assert.Equal("ok 0", Run("Z = 7\nR = Capture(Z())\nR.Arguments.count"));
        Assert.Equal("ok S[]", Run("Z = 7\nR = Capture(Z())\nR.Arguments[]"));
        Assert.Equal("err BadIndex: BadIndex", Run("Z = 7\nR = Capture(Z())\nR.Arguments.first"));
        Assert.Equal("err BadIndex: BadIndex", Run("Z = 7\nR = Capture(Z())\nlast(R.Arguments)"));
        Assert.Equal("err BadIndex: BadIndex", Run("Z = 7\nR = Capture(Z())\nR.Arguments[0]"));
    }

    [Theory]
    // a callable alias, a parameter callee, a conditional family, a builtin callee
    [InlineData("Plus = Add\nR = Capture(Plus(4, 5))\nR.Arguments.count, R.Arguments[1], R.Invoke()", "ok S[2, 5, 9]")]
    [InlineData("Run(f) = Capture(f(4, 5))\nR = Run(Add)\nR.Arguments[1], R.Invoke()", "ok S[5, 9]")]
    [InlineData("Sign(0) = 100\nSign(n) = n\nR = Capture(Sign(7))\nR.Arguments[0], R.Invoke()", "ok S[7, 7]")]
    [InlineData("R = Capture(if(true, 1, 2))\nR.Arguments.count, R.Arguments[2], R.Invoke()", "ok S[3, 2, 1]")]
    [InlineData("R = Capture(range(1, 3))\nR.Arguments.last, R.Invoke()", "ok S[3, L[1, 2, 3]]")]
    public void EveryCaptureableCallShape_ViewsItsWrittenArguments(string body, string expected)
        => Assert.Equal(expected, Run(body));

    [Fact]
    public void ABuiltinsArguments_StayUndemandedUntilSelected()
    {
        var (outcome, effects) = Watch("R = Capture(if(trace(true), trace(1), trace(2)))\nR.Arguments.count, R.Arguments[2]");
        Assert.Equal("ok S[3, 2]", outcome);
        Assert.Equal(1, effects.Traces);
    }

    [Fact]
    public void ABuiltinPlan_PreparedByTheView_KeepsItsWrittenSources_ForTheLaterInvocation()
    {
        // The view prepares the supply before the target is known; the later builtin invocation must
        // still bind the written slots exactly as an ordinary preparation would.
        Assert.Equal("ok S[2, L[1, 2, 3]]", Run("R = Capture(range(1, 3))\nR.Arguments.count, R.Invoke()"));
        Assert.Equal(Run("R = Capture(range(1, true))\nR.Invoke()"),
            Run("R = Capture(range(1, true))\nR.Arguments.count + R.Invoke()"));
    }

    // ── Counting and selection ──────────────────────────────────────────────

    [Fact]
    public void Count_IncludesExplicitSpreads_AndFormsTheSpreadOnceForEveryObserver()
    {
        var (outcome, effects) = Watch("R = Capture(Add(pair()*))\nR.Arguments.count, R.Invoke(), R.Arguments[1], Add(R.Arguments*)");
        Assert.Equal("ok S[2, 3, 2, 3]", outcome);
        Assert.Equal(1, effects.Pairs);
    }

    [Fact]
    public void Count_ObservesTheSupply_TheTargetsArityCheckBelongsToItsDispatch()
    {
        // Supply formation precedes the target's cardinality check in every call; the view never dispatches,
        // so a captured call with too many arguments still has a countable, selectable supply, while its
        // execution reports the ordinary arity error. A family without a matching clause likewise.
        Assert.Equal("ok S[3, 3]", Run("R = Capture(Add(1, 2, 3))\nR.Arguments.count, R.Arguments[2]"));
        Assert.Equal("err ArityMismatch: 2/3", Run("R = Capture(Add(1, 2, 3))\nR.Invoke()"));
        Assert.Equal("ok 5", Run("F(0) = 1\nR = Capture(F(5))\nR.Arguments[0]"));
        Assert.Equal("err NoMatchingBranch: NoMatchingBranch", Run("F(0) = 1\nR = Capture(F(5))\nR.Invoke()"));
    }

    [Fact]
    public void Count_DoesNotDemandAFailingArgument()
        => Assert.Equal("ok S[2, 5]", Run("R = Capture(Add(5, 1 / 0))\nR.Arguments.count, R.Arguments[0]"));

    [Fact]
    public void ASelectedFailingArgument_FailsWithItsOwnError_OnlyWhenSelected()
        => Assert.Equal("err DivisionByZero: DivByZero", Run("R = Capture(Add(5, 1 / 0))\nR.Arguments[1]"));

    [Fact]
    public void AStickyPreparationFailure_EndsEveryObservation()
    {
        foreach (var row in new[] { "R.Arguments.count", "R.Arguments[0]", "R.Arguments.first", "Add(R.Arguments*)", "R.Invoke()" })
            Assert.Equal("err DivisionByZero: DivByZero", Run("Boom = 1 / 0, 2\nR = Capture(Add(Boom*))\n" + row));
    }

    [Fact]
    public void EmptySelection_ReadsNothing_AndInvalidSelectors_FailBeforePreparation()
    {
        const string capture = "R = Capture(Add(pair()*))\n";
        Assert.Equal(("ok S[]", 0), Pairs(capture + "R.Arguments[]"));
        Assert.Equal(("err TypeMismatch: Expected a number, got a Boolean value", 0), Pairs(capture + "R.Arguments[true]"));
        Assert.Equal(("err BadIndex: BadIndex", 0), Pairs(capture + "R.Arguments[-1]"));
        Assert.Equal(("err BadIndex: BadIndex", 0), Pairs(capture + "R.Arguments[0.5]"));
        // A valid index needs the cardinality: the supply is prepared, once.
        Assert.Equal(("ok 2", 1), Pairs(capture + "R.Arguments[1]"));
        Assert.Equal(("err BadIndex: BadIndex", 1), Pairs(capture + "R.Arguments[2]"));
        Assert.Equal(("err BadIndex: BadIndex", 1), Pairs(capture + "R.Arguments[100000000000000000000]"));
        // A failing preparation is reached only by a selector that needs it.
        Assert.Equal("ok S[]", Run("Boom = 1 / 0, 2\nR = Capture(Add(Boom*))\nR.Arguments[]"));
        Assert.Equal("err TypeMismatch: Expected a number, got a Boolean value",
            Run("Boom = 1 / 0, 2\nR = Capture(Add(Boom*))\nR.Arguments[true]"));

        static (string, int) Pairs(string body)
        {
            var (outcome, effects) = Watch(body);
            return (outcome, effects.Pairs);
        }
    }

    [Fact]
    public void SelectedValues_KeepTheirStructure_SelectionIsAValueBoundary()
        => Assert.Equal("ok S[S[1, 2], L[5], S[]]", Run("""
            Three(a, b, c) = 0
            R = Capture(Three((1, 2), [5], ()))
            R.Arguments[0], R.Arguments[1], R.Arguments[2]
            """));

    [Fact]
    public void ASpreadSelectorSupply_TransportsTheViewsCells()
        => Assert.Equal("ok S[8, 7]", Run("R = Capture(Add(1, 0))\n[7, 8][R.Arguments*]"));

    // ── Cell-preserving spread ──────────────────────────────────────────────

    [Fact]
    public void TheSpread_LeavesUndemandedArgumentsSuspended()
        => Assert.Equal("ok 5", Run("R = Capture(Add(5, 1 / 0))\nFirst(R.Arguments*)"));

    [Fact]
    public void TheSpread_KeepsCallableArgumentsCallable()
        => Assert.Equal("ok S[25, 25]", Run("R = Capture(Apply(Square, 5))\nApply(R.Arguments*), R.Invoke()"));

    [Fact]
    public void TheSpread_SharesMemoizedCells_WithTheOriginalCall()
    {
        var (outcome, effects) = Watch("R = Capture(Add(trace(10), trace(20)))\nAdd(R.Arguments*) + R.Invoke() + Mul(R.Arguments*)");
        Assert.Equal("ok 260", outcome);
        Assert.Equal(2, effects.Traces);
    }

    [Fact]
    public void TheSpread_TransportsTheOriginalCellObjects()
    {
        // The destination binds the plan's very cells: the original call's VALUE, after the spread demanded
        // them, finds them completed (no second trace), and the plan's prepared list is the transported one.
        var (outcome, effects) = Watch("Use(v) = Mul(Capture(v).Arguments*) + v\nUse(Add(trace(3), trace(4)))");
        Assert.Equal("ok 19", outcome);
        Assert.Equal(2, effects.Traces);
    }

    [Theory]
    [InlineData("R = Capture(Three(true, 1, 2))\nif(R.Arguments*)", "ok 1")]
    [InlineData("R = Capture(Id([3, 9]))\nmax(R.Arguments*)", "ok 9")]
    [InlineData("R = Capture(Two([1, 2], Inc))\nmap(R.Arguments*)", "ok L[2, 3]")]
    [InlineData("R = Capture(Two(1, 2))\ncount(R.Arguments*)", "err ArityMismatch: 1/2")]
    [InlineData("R = Capture(Two(1, 2))\nCollect(R.Arguments*)", "ok L[1, 2]")]
    public void BuiltinHigherOrderAndCollectingDestinations_BindTheTransportedCells(string body, string expected)
        => Assert.Equal(expected, Run("Three(a, b, c) = 0\nTwo(a, b) = 0\nInc(x) = x + 1\nCollect(*xs) = xs\n" + body));

    [Fact]
    public void SeveralSpreadsOfOneView_ReuseItsOnePreparation()
    {
        var (outcome, effects) = Watch("R = Capture(Add(pair()*))\nA = R.Arguments\nAdd(A*) + Add(A*) + Mul(R.Arguments*)");
        Assert.Equal("ok 8", outcome);
        Assert.Equal(1, effects.Pairs);
    }

    [Fact]
    public void ASpreadOfACallsOwnView_IsADemandCycle()
        => Assert.Equal("err DemandCycle: DemandCycle", Run("Q = Capture(Add(Q.Arguments*))\nQ.Arguments.count"));

    [Fact]
    public void AStackedStar_OpensTheViewIntoValues_AndIsRefused_WhileAGroupedRecaptureIsTheView()
    {
        Assert.Equal(TypeError(Evaluator.ArgumentViewSpreadMessage), Run("R = Capture(Add(10, 20))\nMul(R.Arguments**)"));
        Assert.Equal("ok 200", Run("R = Capture(Add(10, 20))\nMul((R.Arguments)*)"));
    }

    // ── Unsupported operations and the intrinsic route ──────────────────────

    [Theory]
    [InlineData("[R.Arguments*]")]
    [InlineData("(R.Arguments*, 1)")]
    [InlineData("S = R.Arguments*\nS")]
    public void AValuePositionSpread_NeverOpensAView(string row)
        => Assert.Equal(TypeError(Evaluator.ArgumentViewSpreadMessage), Run("R = Capture(Add(10, 20))\n" + row));

    [Theory]
    [InlineData("sum(R.Arguments)", "sum")]
    [InlineData("map(R.Arguments, Square)", "map")]
    [InlineData("filter(R.Arguments, { x > 1 })", "filter")]
    [InlineData("R.Arguments.filter({ x > 1 }).count", "filter")]
    [InlineData("count(filter(R.Arguments, { x > 1 }))", "filter")]
    [InlineData("distinct(R.Arguments)", "distinct")]
    [InlineData("contains(R.Arguments, 10)", "contains")]
    [InlineData("order(R.Arguments)", "order")]
    [InlineData("reduce(R.Arguments, Add, 0)", "reduce")]
    [InlineData("atoms(R.Arguments)", "atoms")]
    public void OtherCollectionBuiltins_RefuseTheView_InsteadOfMaterializingIt(string row, string builtin)
    {
        var (outcome, effects) = Watch("R = Capture(Add(trace(10), trace(20)))\n" + row);
        Assert.Equal(TypeError(Evaluator.ArgumentViewUnsupportedMessage(builtin)), outcome);
        Assert.Equal(0, effects.Traces);
    }

    [Fact]
    public void AListContainingAView_IsAnOrdinaryCollection()
        => Assert.Equal("ok S[2, true, 20]", Run("""
            R = Capture(Add(10, 20))
            L = [R.Arguments, 1]
            count(L), contains(L, R.Arguments), L[0][1]
            """));

    [Fact]
    public void ArgumentsIsAProperty_AnArgumentListIsRefusedBeforeAnythingRuns()
    {
        Assert.Equal("err IllegalInEval: " + Evaluator.ArgumentsIsPropertyMessage, Run("R = Capture(Add(10, 20))\nR.Arguments()"));
        var (outcome, effects) = Watch("R = Capture(Add(10, 20))\nR.Arguments(trace(1))");
        Assert.Equal("err IllegalInEval: " + Evaluator.ArgumentsIsPropertyMessage, outcome);
        Assert.Equal(0, effects.Traces);
    }

    [Theory]
    [InlineData("5.Arguments", "numeric value 5")]
    [InlineData("(1, 2).Arguments", "a sequence value with 2 sequence elements: (1, 2)")]
    [InlineData("R.Arguments.Arguments", "an argument view")]
    public void ANonReferenceReceiver_IsTheIntrinsicsKindError_NeverALexicalExtension(string row, string description)
        => Assert.Equal(TypeError($"`Arguments` requires a call reference, got {description}"),
            Run("Arguments(r) = r + 1\nR = Capture(Add(10, 20))\n" + row));

    [Fact]
    public void APlainCallArguments_StaysTheUsersAlgorithm()
        => Assert.Equal("ok 5", Run("Arguments(r) = r + 1\nArguments(4)"));

    [Fact]
    public void ADeclaredStructuralMember_WinsOverTheIntrinsic()
        => Assert.Equal("ok S[3, 4]", Run("Box = { public Arguments = 3 }\nBag = { public Arguments(x) = x }\nBox.Arguments, Bag.Arguments(4)"));

    [Fact]
    public void AView_IsNotAReference_ItCannotBeInvoked()
        => Assert.Equal(TypeError("`Invoke` requires a call reference, got an argument view"),
            Run("R = Capture(Add(10, 20))\nR.Arguments.Invoke()"));

    [Fact]
    public void Arguments_IsNeverInferredAsAnImplicitParameter()
    {
        var parsed = Parser.Parse("G = R.Arguments\nH = R.Arguments.count");
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        foreach (var name in new[] { "G", "H" })
        {
            var property = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single(p => p.Name == name).Value);
            Assert.Equal(["R"], property.Parameters.Select(static p => p.Name));
        }
    }

    [Fact]
    public void FormulaLifting_ReadsTheViewsReceiverAsAValue()
        => Assert.Equal("ok 2", Run("Make(x) = Capture(Add(x, x))\nH = Make.Arguments.count\nH(3)"));

    // ── Boundaries ──────────────────────────────────────────────────────────

    [Theory]
    [InlineData("R.Arguments")]
    [InlineData("[R.Arguments]")]
    [InlineData("R.Arguments, 1")]
    [InlineData("(1, (2, R.Arguments))")]
    [InlineData("L = [R.Arguments, R.Arguments]\nM = [L, L]\nM")]
    public void ARunResultContainingAView_IsRefusedAtTheRunBoundary(string rows)
        => Assert.Equal(TypeError(Evaluator.CallReferenceLeavesRunMessage), Run("R = Capture(Add(10, 20))\n" + rows));

    [Theory]
    [InlineData("\"v={R.Arguments}\"")]
    [InlineData("\"v={[1, R.Arguments]}\"")]
    public void Interpolation_RefusesAView(string row)
        => Assert.Equal(TypeError(Evaluator.CallReferenceHasNoTextMessage), Run("R = Capture(Add(10, 20))\n" + row));

    [Fact]
    public void AHostOperation_NeverReceivesAView()
    {
        foreach (var row in new[] { "trace(R.Arguments)", "trace([[R.Arguments]])" })
        {
            var (outcome, effects) = Watch("R = Capture(Add(10, 20))\n" + row);
            Assert.Equal(TypeError(Evaluator.CallReferenceLeavesRunMessage), outcome);
            Assert.Equal(0, effects.Traces);
        }
    }

    [Theory]
    [InlineData("R.Arguments + 1")]
    [InlineData("R.Arguments < R.Arguments")]
    [InlineData("if(R.Arguments, 1, 2)")]
    [InlineData("not R.Arguments")]
    [InlineData("R.Arguments.string")]
    public void OrdinaryOperations_RejectAView_WithTheirKindVerdicts(string row)
    {
        var outcome = Run("R = Capture(Add(10, 20))\n" + row);
        Assert.StartsWith("err ", outcome, StringComparison.Ordinal);
        Assert.DoesNotContain("10", outcome, StringComparison.Ordinal);
    }

    [Fact]
    public async Task PublicEvaluatorEntryPoints_RefuseAViewResult()
    {
        var operations = Operations(new Effects());
        var root = Program(Prelude + "\nR = Capture(Add(10, 20))\nR.Arguments", operations);
        var direct = Evaluator.Run(root, operations, limits: null, randomSeed: null, CancellationToken.None);
        Assert.IsType<EvalError.TypeMismatch>(direct.Error);
        var flat = Evaluator.RunFlat(root, operations, limits: null, randomSeed: null, CancellationToken.None);
        Assert.IsType<EvalError.TypeMismatch>(flat.Error);
        var asynchronous = await Evaluator.RunAsync(root, operations, limits: null, randomSeed: null, CancellationToken.None);
        Assert.IsType<EvalError.TypeMismatch>(asynchronous.Error);
    }

    // ── Representation ──────────────────────────────────────────────────────

    [Fact]
    public void TheView_IsTheReferencesOneFacet_EqualityAndHashNeverChangeWhenItIsRead()
    {
        var ctx = PlanCtx();
        var cell = Evaluator.SupplyCell(new Expr.Call(new Expr.Resolve("count"), [new Expr.Num(1)]), ctx, []);
        var reference = Evaluator.ReifyMeta(cell).Value;
        var hashBefore = reference.GetHashCode();
        var structuralBefore = Result.ValueComparer.GetHashCode(reference);
        var view = reference.ArgumentView;
        Assert.Same(view, reference.ArgumentView);
        Assert.True(view.IsArgumentView);
        Assert.False(reference.IsArgumentView);
        Assert.Same(reference.Plan, view.Plan);
        Assert.NotEqual<Result>(reference, view);
        Assert.False(Result.ValueComparer.Equals(reference, view));
        Assert.Equal(hashBefore, reference.GetHashCode());
        Assert.Equal(structuralBefore, Result.ValueComparer.GetHashCode(reference));
        Assert.Throws<InvalidOperationException>(() => view.ArgumentView);
        // Obtaining the view prepared nothing.
        Assert.Null(((Evaluator.InvocationPlan)cell.Suspension!).Supply);
    }

    [Fact]
    public void Count_PreparesTheNeutralShape_AndTheSupplyHoldsTheOriginalCells()
    {
        var ctx = PlanCtx();
        var call = new Expr.Call(new Expr.Resolve("max"), [new Expr.Num(1), new Expr.Num(2)]);
        var cell = Evaluator.SupplyCell(call, ctx, []);
        var view = Evaluator.ReifyMeta(cell).Value.ArgumentView;
        var plan = (Evaluator.InvocationPlan)cell.Suspension!;
        var cells = Evaluator.PrepareArgumentView(view, ctx);
        Assert.True(cells.IsOk);
        Assert.Equal(2, cells.Value.Count);
        Assert.Equal(1, plan.SupplyFormations);
        Assert.Same(cells.Value, plan.PreparedCells);
        Assert.All(cells.Value, static argument => Assert.False(argument.HasCompletedValue));
        // A second read answers from the record.
        Assert.Same(cells.Value, Evaluator.PrepareArgumentView(view, ctx).Value);
        Assert.Equal(1, plan.SupplyFormations);
    }

    // ── Run ownership and terminality ───────────────────────────────────────

    private static Evaluator.EvalCtx PlanCtx(CancellationToken token = default)
    {
        var budget = EvaluationBudget.Create(null, cancellationToken: token);
        budget.DecideInvocationPlanRetention(programMayCapture: true);
        return Evaluator.EvalCtx.Empty with { Budget = budget, Services = Evaluator.RunServices.Unconfigured with { Observations = new EvaluationObservations() } };
    }

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

    [Fact]
    public void AView_WorksInItsOwnLiveRun()
    {
        CaptureFromRun(whileRunning: reference =>
        {
            var ctx = reference.Plan.Caller;
            var viewR = Evaluator.ArgumentsOfCallReferenceValue(reference, ctx);
            Assert.True(viewR.IsOk);
            var view = Assert.IsType<Result.CallReference>(viewR.Value.Value);
            var cells = Evaluator.PrepareArgumentView(view, ctx);
            Assert.True(cells.IsOk);
            Assert.Equal(new Result.Atom(5), Assert.Single(cells.Value).Demand().Value.Value);
        });
    }

    [Fact]
    public void AForeignRunsReferenceOrView_IsRefused_AndPreparesNothing()
    {
        var reference = CaptureFromRun();
        var preparedBefore = reference.Plan.Supply;
        var stranger = CaptureFromRun().Plan.Caller;
        var obtained = Evaluator.ArgumentsOfCallReferenceValue(reference, stranger);
        Assert.Equal(Evaluator.ForeignCallReferenceMessage, Assert.IsType<EvalError.IllegalInEval>(obtained.Error).Reason);
        var prepared = Evaluator.PrepareArgumentView(reference.ArgumentView, stranger);
        Assert.Equal(Evaluator.ForeignCallReferenceMessage, Assert.IsType<EvalError.IllegalInEval>(prepared.Error).Reason);
        Assert.Same(preparedBefore, reference.Plan.Supply);
    }

    [Fact]
    public async Task AnEndedRunsView_CannotRestartWork_SyncOrAsync()
    {
        var reference = CaptureFromRun();
        var view = reference.ArgumentView;
        var ctx = reference.Plan.Caller;
        var preparedBefore = reference.Plan.Supply;
        Assert.Equal(Evaluator.EndedCallReferenceMessage,
            Assert.IsType<EvalError.IllegalInEval>(Evaluator.ArgumentsOfCallReferenceValue(reference, ctx).Error).Reason);
        Assert.Equal(Evaluator.EndedCallReferenceMessage,
            Assert.IsType<EvalError.IllegalInEval>(Evaluator.PrepareArgumentView(view, ctx).Error).Reason);
        Assert.Equal(Evaluator.EndedCallReferenceMessage,
            Assert.IsType<EvalError.IllegalInEval>((await Evaluator.PrepareArgumentViewAsync(view, ctx)).Error).Reason);
        Assert.Same(preparedBefore, reference.Plan.Supply);
    }

    [Fact]
    public void ACancelledRun_CannotBeRevivedThroughAView_TheOriginalTokenIsKept()
    {
        using var source = new CancellationTokenSource();
        var ctx = PlanCtx(source.Token);
        var cell = Evaluator.SupplyCell(new Expr.Call(new Expr.Resolve("max"), [new Expr.Num(1)]), ctx, []);
        var view = Evaluator.ReifyMeta(cell).Value.ArgumentView;
        source.Cancel();
        var cancelled = Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.PrepareArgumentView(view, ctx));
        Assert.Equal(source.Token, cancelled.CancellationToken);
        Assert.Null(((Evaluator.InvocationPlan)cell.Suspension!).Supply);
    }

    [Fact]
    public void ATerminalRun_EndsEveryViewOperation_EvenAfterAPreparation()
    {
        var ctx = PlanCtx();
        var cell = Evaluator.SupplyCell(new Expr.Call(new Expr.Resolve("max"), [new Expr.Num(1)]), ctx, []);
        var reference = Evaluator.ReifyMeta(cell).Value;
        Assert.True(Evaluator.PrepareArgumentView(reference.ArgumentView, ctx).IsOk);
        var terminal = ctx.Budget.RetainTerminal(new EvalError.EvaluationStepLimitExceeded(1));
        Assert.Same(terminal, Evaluator.PrepareArgumentView(reference.ArgumentView, ctx).Error);
        Assert.Same(terminal, Evaluator.ArgumentsOfCallReferenceValue(reference, ctx).Error);
    }

    [Fact]
    public void ARetainedRequiredSourceFailure_OrSourceCancellation_EndsEveryViewOperation()
    {
        var failing = PlanCtx();
        var cell = Evaluator.SupplyCell(new Expr.Call(new Expr.Resolve("max"), [new Expr.Num(1)]), failing, []);
        var view = Evaluator.ReifyMeta(cell).Value.ArgumentView;
        var sourceFailure = new EvalError.ModuleRegionMaterializationFailed([]);
        failing.Budget.RetainRequiredSourceFailure(sourceFailure);
        Assert.Same(sourceFailure, Evaluator.PrepareArgumentView(view, failing).Error);

        var cancelling = PlanCtx();
        var other = Evaluator.ReifyMeta(Evaluator.SupplyCell(new Expr.Call(new Expr.Resolve("max"), [new Expr.Num(1)]), cancelling, []))
            .Value.ArgumentView;
        using var sourceTokens = new CancellationTokenSource();
        sourceTokens.Cancel();
        var original = new OperationCanceledException(sourceTokens.Token);
        cancelling.Budget.RetainRequiredSourceCancellation(original);
        var thrown = Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.PrepareArgumentView(other, cancelling));
        Assert.Same(original, thrown);
    }

    [Fact]
    public async Task AGenuinelySuspendingSpread_InTheCapturedCall_IsPreparedOnce_ThroughTheAsyncView()
    {
        var calls = 0;
        var operations = HostOperations.Create(HostOperation.CreateAsync("Later", async (_, _) =>
        {
            Interlocked.Increment(ref calls);
            await Task.Yield();
            return new Result.SequenceValue([new Result.Atom(3), new Result.Atom(4)]);
        }));
        var source = Prelude + "\nR = Capture(Mul(Later()*))\nR.Arguments.count, R.Arguments[1], Add(R.Arguments*), R.Invoke()";
        var run = await KatLangEngine.RunAsync(source, new RunOptions { HostOperations = operations });
        var success = Assert.IsType<RunResult.Success>(run);
        Assert.Equal("S[2, 4, 7, 12]", SemanticExplorerHarness.Neutral(success.Value));
        Assert.Equal(1, calls);
    }

    // ── Compatibility ───────────────────────────────────────────────────────

    [Fact]
    public void AMetaFreeProgram_UsingAMemberNamedArguments_KeepsTheGateOff()
    {
        var parsed = Parser.Parse("Box = { public Arguments = 3 }\nArguments(r) = r + 1\nBox.Arguments + Arguments(1)");
        Assert.False(parsed.HasErrors);
        Assert.False(Evaluator.ProgramMayCaptureCalls(new Expr.AlgorithmExpr(parsed.Root)));
        Assert.Equal("ok 5", Observe("Box = { public Arguments = 3 }\nArguments(r) = r + 1\nBox.Arguments + Arguments(1)").Outcome);
    }

    [Theory]
    [InlineData("count([1, 2, 3])", "ok 3")]
    [InlineData("[10, 20, 30][2, 0]", "ok S[30, 10]")]
    [InlineData("Add([1, 2]*)", "ok 3")]
    [InlineData("Mul((3, 4)*)", "ok 12")]
    [InlineData("[(1, 2)*, 3]", "ok L[1, 2, 3]")]
    [InlineData("[[7]]**", "ok 7")]
    [InlineData("first((5, 6)), last([5, 6])", "ok S[5, 6]")]
    [InlineData("count(filter(range(1, 10), { x > 5 }))", "ok 5")]
    public void OrdinarySequencesSelectionAndSpreads_AreUnchanged(string row, string expected)
        => Assert.Equal(expected, Run(row));
}
