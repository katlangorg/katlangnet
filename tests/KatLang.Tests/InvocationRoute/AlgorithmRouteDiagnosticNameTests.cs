using KatLang.Evaluation;

namespace KatLang.Tests.InvocationRoute;

/// <summary>
/// META-S3-4-DIAG (October 20 2026): the callee name a FRESH call of a captured callee reports on the
/// <c>.Algorithm</c> route. Whether the invocation <c>R.Algorithm(args)</c> / <c>(R.Algorithm)(args)</c> runs
/// as the ordinary intrinsic (a top-level row: no plan) or as a generalized invocation plan (a supplied
/// argument <c>Id(R.Algorithm(args))</c> in a program that spells <c>meta</c>: the J7 gate retains it), its
/// dispatch is named by the CAPTURED plan's effective callee — <c>F</c>, <c>Pack.F</c>, an extension's
/// fallback, a nested projection's own written callee — never by the reconstructed invocation's written
/// <c>R.Algorithm</c>, which only the surrounding call / dot-call context mentions. Lean was aligned to this
/// rule (<c>NeedPlan.dispatchNameIn</c>); C# was already the reference (<c>PlanCalleeName(captured)</c> in
/// <c>ProjectPlannedAlgorithmCallee</c>). Every case is checked structurally — code, innermost payload, the
/// full context chain and every span — on the synchronous generic, synchronous optimized and asynchronous
/// engines, and its semantics (outcome, effects, steps, checkpoints) agree across the three.
/// </summary>
public class AlgorithmRouteDiagnosticNameTests
{
    /// <summary>The fixture library; its line count is fixed so spans compare directly (the row is line 15).</summary>
    private const string Library = """
        Capture(meta op) = op
        Id(x) = x
        F(0) = 0
        G(x, 0) = x
        Sq(x) = trace(x) * x
        Mk(f) = Capture(f(1))
        Pack = { F(0) = 0 }
        Box5 = { Algorithm(0) = 0 }
        Op(meta op) = Capture(op.Algorithm(op.Arguments*))
        R = Capture(F(0))
        Q = Capture(Pack.F(0))
        E = Capture(5.G(0))
        S = Capture(Sq(2))
        X = Mk(5)

        """;

    private static readonly HostOperations Trace = HostOperations.Create(HostOperation.Create("trace", (args, _) => args[0], "x"));

    private static Expr Program(string row, HostOperations operations)
    {
        var parsed = Parser.Parse(Library + row, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    private static async Task<(EvalResult<Evaluator.CountedResult> Result, long Plans)> RunOn(string row, int mode)
    {
        var observations = new EvaluationObservations();
        var operations = Trace;
        var run = mode == 2
            ? await Evaluator.RunCountedObservedAsync(Program(row, operations), observations: observations, hostOperations: operations)
            : Evaluator.RunCountedObserved(Program(row, operations), enableOptimizations: mode == 1, observations: observations, hostOperations: operations);
        return (run.Item1, observations.InvocationPlanCount);
    }

    /// <summary>The full structure of a failure: every context frame with its span, then the innermost payload with its span.</summary>
    private static string Structure(EvalError error)
    {
        var frames = new List<string>();
        while (error is EvalError.WithContext context)
        {
            frames.Add($"{context.Context} @{context.Span}");
            error = context.Inner;
        }
        var payload = error switch
        {
            EvalError.NoMatchingBranch noMatch => $"NoMatchingBranch({noMatch.AlgorithmName})",
            EvalError.ArityMismatch arity => $"ArityMismatch({arity.Expected}, {arity.Actual})",
            EvalError.NotAnAlgorithm notAlgorithm => $"NotAnAlgorithm({notAlgorithm.Description})",
            EvalError.IllegalInEval illegal => $"IllegalInEval({illegal.Reason})",
            _ => $"{error.GetType().Name}[{error.Code}]",
        };
        frames.Add($"{payload} @{error.Span}");
        return string.Join(" > ", frames);
    }

    private static string InnermostName(EvalError error)
    {
        while (error is EvalError.WithContext context) error = context.Inner;
        return Assert.IsType<EvalError.NoMatchingBranch>(error).AlgorithmName;
    }

    // ── The failures: code, innermost payload, full context and spans ──────────────────────────────────

    public static TheoryData<string, string, string> Failures => new()
    {
        // 1. Ordinary `.Algorithm` invocation (a top-level row is not supplied: no plan).
        { "R.Algorithm(1)", "NoMatchingBranch",
            "while evaluating dotCall .Algorithm of R @[15:1, 15:15) > NoMatchingBranch(F) @" },
        // 2. Planned `.Algorithm` invocation: the supplied argument is a retained invocation plan.
        { "Id(R.Algorithm(1))", "NoMatchingBranch",
            "while evaluating call to Id @[15:4, 15:18) > while evaluating dotCall .Algorithm of R @[15:4, 15:18) > NoMatchingBranch(F) @" },
        // 3. Grouped syntax, ordinary and planned: the call context names the written callee, the payload the captured one.
        { "(R.Algorithm)(1)", "NoMatchingBranch",
            "while evaluating call to R.Algorithm @[15:1, 15:17) > NoMatchingBranch(F) @" },
        { "Id((R.Algorithm)(1))", "NoMatchingBranch",
            "while evaluating call to Id @[15:4, 15:20) > while evaluating call to R.Algorithm @[15:4, 15:20) > NoMatchingBranch(F) @" },
        // 4. A qualified captured callee keeps its member path.
        { "Q.Algorithm(1)", "NoMatchingBranch",
            "while evaluating dotCall .Algorithm of Q @[15:1, 15:15) > NoMatchingBranch(Pack.F) @" },
        { "Id(Q.Algorithm(1))", "NoMatchingBranch",
            "while evaluating call to Id @[15:4, 15:18) > while evaluating dotCall .Algorithm of Q @[15:4, 15:18) > NoMatchingBranch(Pack.F) @" },
        // 5. A captured extension invocation `5.G(0)` names its ordinary effective callee, the fallback `G`.
        { "E.Algorithm(1, 1)", "NoMatchingBranch",
            "while evaluating dotCall .Algorithm of E @[15:1, 15:18) > NoMatchingBranch(G) @" },
        { "Id(E.Algorithm(1, 1))", "NoMatchingBranch",
            "while evaluating call to Id @[15:4, 15:21) > while evaluating dotCall .Algorithm of E @[15:4, 15:21) > NoMatchingBranch(G) @" },
        // 7. An arity failure carries no callee name and keeps its ordinary conventions.
        { "S.Algorithm(1, 2)", "ArityMismatch",
            "while evaluating dotCall .Algorithm of S @[15:1, 15:18) > ArityMismatch(1, 2) @" },
        { "Id(S.Algorithm(1, 2))", "ArityMismatch",
            "while evaluating call to Id @[15:4, 15:21) > while evaluating dotCall .Algorithm of S @[15:4, 15:21) > ArityMismatch(1, 2) @" },
        // 8. A captured callee without callable identity (`f(1)` with `f` bound to 5) is the projection's own
        //    `NotAnAlgorithm "captured callee"` at the edge, never a name error.
        { "X.Algorithm(1)", "NotAnAlgorithm",
            "while evaluating dotCall .Algorithm of X @[15:1, 15:15) > NotAnAlgorithm(captured callee) @[15:1, 15:15)" },
        { "Id(X.Algorithm(1))", "NotAnAlgorithm",
            "while evaluating call to Id @[15:4, 15:18) > while evaluating dotCall .Algorithm of X @[15:4, 15:18) > NotAnAlgorithm(captured callee) @[15:4, 15:18)" },
        // 9. A declared member named `Algorithm` is an ordinary member call, named by its member name.
        { "Box5.Algorithm(1)", "NoMatchingBranch",
            "while evaluating dotCall .Algorithm of Box5 @[15:1, 15:18) > NoMatchingBranch(Algorithm) @" },
        { "Id(Box5.Algorithm(1))", "NoMatchingBranch",
            "while evaluating call to Id @[15:4, 15:21) > while evaluating dotCall .Algorithm of Box5 @[15:4, 15:21) > NoMatchingBranch(Algorithm) @" },
        //    An ordinary planned member call is named by its member name as well (outside META-S3-4-DIAG:
        //    Lean's planned member route still names the path `Pack.F`, recorded in SEMANTIC-ALIGNMENT).
        { "Id(Pack.F(1))", "NoMatchingBranch",
            "while evaluating call to Id @[15:4, 15:13) > while evaluating dotCall .F of Pack @[15:4, 15:13) > NoMatchingBranch(F) @" },
        // 10. A nested reconstructed META invocation: `Op` captures `op.Algorithm(op.Arguments*)`, a plan on the
        //     `.Algorithm` route. Invoking it names the callee `op` captured, `F`; a further projection of it names
        //     the immediately captured plan's written callee `op.Algorithm`, never chased further.
        { "Op(F(1)).Invoke()", "NoMatchingBranch",
            "while evaluating dotCall .Invoke of Op(...) @[9:23, 9:50) > while evaluating dotCall .Algorithm of op @[9:23, 9:50) > NoMatchingBranch(F) @" },
        { "Op(F(0)).Algorithm(1)", "NoMatchingBranch",
            "while evaluating dotCall .Algorithm of Op(...) @[15:1, 15:22) > NoMatchingBranch(op.Algorithm) @" },
        { "Id(Op(F(0)).Algorithm(1))", "NoMatchingBranch",
            "while evaluating call to Id @[15:4, 15:25) > while evaluating dotCall .Algorithm of Op(...) @[15:4, 15:25) > NoMatchingBranch(op.Algorithm) @" },
    };

    [Theory]
    [MemberData(nameof(Failures))]
    public async Task AnAlgorithmRouteFailure_HasItsFullStructure_OnEveryEngine(string row, string code, string structure)
    {
        foreach (var mode in new[] { 0, 1, 2 })
        {
            var (result, _) = await RunOn(row, mode);
            Assert.True(result.IsError, $"{row} mode {mode}: expected a failure");
            Assert.Equal(code, result.Error.Code.ToString());
            Assert.Equal(structure, Structure(result.Error));
        }
    }

    /// <summary>The planned rows really run as invocation plans: each retains one plan more than its ordinary row.</summary>
    [Theory]
    [InlineData("R.Algorithm(1)", "Id(R.Algorithm(1))")]
    [InlineData("(R.Algorithm)(1)", "Id((R.Algorithm)(1))")]
    [InlineData("Q.Algorithm(1)", "Id(Q.Algorithm(1))")]
    [InlineData("E.Algorithm(1, 1)", "Id(E.Algorithm(1, 1))")]
    public async Task ThePlannedForm_IsAPlan_AndNamesTheCapturedCalleeLikeTheOrdinaryForm(string ordinary, string planned)
    {
        foreach (var mode in new[] { 0, 1, 2 })
        {
            var (plain, plainPlans) = await RunOn(ordinary, mode);
            var (plan, plannedPlans) = await RunOn(planned, mode);
            Assert.Equal(plainPlans + 1, plannedPlans);
            Assert.Equal(InnermostName(plain.Error), InnermostName(plan.Error));
        }
    }

    private const string FailedProjectionLibrary = "Bad = min([])\nHeld = Mk(Bad.Algorithm)\n";

    public static TheoryData<string> FailedProjections => new()
    {
        { "Held.Algorithm(1)" },
        { "Id(Held.Algorithm(1))" },
        { "(Held.Algorithm)(1)" },
        { "Id((Held.Algorithm)(1))" },
    };

    [Theory]
    [MemberData(nameof(FailedProjections))]
    public async Task AFailedCapturedCallableProjection_KeepsItsOriginalFailure(string row)
    {
        var invocationContext = row.Contains("(Held.Algorithm)", StringComparison.Ordinal)
            ? "while evaluating call to Held.Algorithm"
            : "while evaluating dotCall .Algorithm of Held";
        var expectedStructure = $"{invocationContext} @[15:7, 15:14) > while evaluating call to min @[15:7, 15:14) > IllegalInEval(min requires a non-empty collection) @";
        if (row.StartsWith("Id(", StringComparison.Ordinal))
            expectedStructure = "while evaluating call to Id @[15:7, 15:14) > " + expectedStructure;
        foreach (var mode in new[] { 0, 1, 2 })
        {
            var (result, _) = await RunOn(FailedProjectionLibrary + row, mode);
            Assert.True(result.IsError, row);
            Assert.Equal("IllegalInEval", result.Error.Code.ToString());
            Assert.True(Evaluator.IsProjectionFailure(result.Error), Structure(result.Error));
            var leaf = result.Error;
            while (leaf is EvalError.WithContext context) leaf = context.Inner;
            Assert.Equal("min requires a non-empty collection", Assert.IsType<EvalError.IllegalInEval>(leaf).Reason);
            Assert.Null(leaf.Span); // The builtin payload is unspanned; its call frame owns the source span.
            Assert.Equal("[15:7, 15:14)", result.Error.Span?.ToString());
            var structure = Structure(result.Error);
            Assert.Contains("while evaluating call to min @[15:7, 15:14)", structure, StringComparison.Ordinal);
            Assert.Equal(expectedStructure, structure);
        }
    }

    // ── Engine agreement on the whole observable semantics ──────────────────────────────────────────────

    public static TheoryData<string> AgreementRows()
    {
        var data = new TheoryData<string>();
        foreach (var row in Failures) data.Add((string)row[0]);
        foreach (var row in Successes) data.Add((string)row[0]);
        foreach (var row in FailedProjections) data.Add(FailedProjectionLibrary + row);
        return data;
    }

    [Theory]
    [MemberData(nameof(AgreementRows))]
    public async Task EveryRow_HasTheSameSemantics_EffectsStepsAndCheckpoints_OnEveryEngine(string row)
    {
        // The corpus library already declares `Id(x) = x` and the META consumer `Capture`; this library's own
        // declarations of them are dropped (spans shift, but they are compared across engines only).
        var library = Library
            .Replace("Capture(meta op) = op\n", "", StringComparison.Ordinal)
            .Replace("Id(x) = x\n", "", StringComparison.Ordinal);
        var c = new InvocationRouteCorpus.Case("DIAG", library + row);
        var generic = await InvocationRouteCorpus.Observe(c, 0);
        Assert.Equal(generic.Semantic, (await InvocationRouteCorpus.Observe(c, 1)).Semantic);
        Assert.Equal(generic.Semantic, (await InvocationRouteCorpus.Observe(c, 2)).Semantic);
    }

    // ── Successful controls: the diagnostic name changes no value ─────────────────────────────────────

    public static TheoryData<string, string> Successes => new()
    {
        { "R.Algorithm(0), Id(R.Algorithm(0)), (R.Algorithm)(0), Id((R.Algorithm)(0))", "(0, 0, 0, 0)" },
        { "Id(Q.Algorithm(0)), Id(E.Algorithm(7, 0)), Id(S.Algorithm(3)), Id(Box5.Algorithm(0))", "(0, 7, 9, 0)" },
        { "Op(F(0)).Invoke(), Op(Sq(4)).Invoke(), Id(S.Algorithm(S.Arguments*))", "(0, 16, 4)" },
    };

    [Theory]
    [MemberData(nameof(Successes))]
    public async Task ASuccessfulAlgorithmRouteInvocation_KeepsItsValue_OnEveryEngine(string row, string expected)
    {
        foreach (var mode in new[] { 0, 1, 2 })
        {
            var (result, _) = await RunOn(row, mode);
            Assert.True(result.IsOk, $"{row} mode {mode}: {(result.IsError ? result.Error.ToString() : "")}");
            Assert.Equal(expected, InvocationRouteCorpus.Value(result.Value.Value));
        }
    }

    [Fact]
    public async Task TheMandatoryLoops_AreUnchanged()
    {
        foreach (var (source, expected) in new[]
        {
            ("Step(x) = x + 1, x < 3\n\nLoop(meta op) = op.Algorithm(op.Arguments*).while\n\nStep(0).Loop", "3"),
            ("Math.Abs(-3).repeat(2)", "3"),
        })
        {
            var sync = KatLangEngine.Run(source);
            Assert.Equal(expected, InvocationRouteCorpus.Value(Assert.IsType<RunResult.Success>(sync).Value));
            var asynchronous = await KatLangEngine.RunAsync(source);
            Assert.Equal(expected, InvocationRouteCorpus.Value(Assert.IsType<RunResult.Success>(asynchronous).Value));
        }
    }

    /// <summary>
    /// A genuinely suspending asynchronous run reaches the planned `.Algorithm` dispatch after a real
    /// suspension and still names the captured callee.
    /// </summary>
    [Fact]
    public async Task AfterAGenuineSuspension_ThePlannedDispatch_NamesTheCapturedCallee()
    {
        var suspensions = 0;
        var operations = HostOperations.Create(
            HostOperation.Create("trace", (args, _) => args[0], "x"),
            HostOperation.CreateAsync("aflag", async (_, _) =>
            {
                await Task.Yield();
                Interlocked.Increment(ref suspensions);
                return new Result.Bool(true);
            }));
        foreach (var (row, name) in new[]
        {
            ("if(aflag(), Id(R.Algorithm(1)), 0)", "F"),
            ("if(aflag(), Id((R.Algorithm)(1)), 0)", "F"),
            ("if(aflag(), Id(Q.Algorithm(1)), 0)", "Pack.F"),
            ("if(aflag(), Op(F(1)).Invoke(), 0)", "F"),
            // Suspend while resolving the retained receiver of the planned route itself.
            ("AsyncR = if(aflag(), Capture(F(0)), 0)\nId(AsyncR.Algorithm(1))", "F"),
            ("MkAsync(t) = if(aflag(), Capture(F(t)), 0)\nId((MkAsync(0).Algorithm)(1))", "F"),
        })
        {
            suspensions = 0;
            var (result, _) = await Evaluator.RunCountedObservedAsync(Program(row, operations), hostOperations: operations);
            Assert.True(result.IsError, row);
            Assert.Equal(name, InnermostName(result.Error));
            Assert.Equal(1, suspensions);
        }
    }
}
