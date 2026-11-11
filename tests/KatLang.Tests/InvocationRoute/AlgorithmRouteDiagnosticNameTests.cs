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

    // Async capability selects the async twins even when a receiver fails before any host call.
    // A sync-only host set makes RunCountedObservedAsync fall back to the sync evaluator.
    private static readonly HostOperations AsyncTrace = HostOperations.Create(
        HostOperation.CreateAsync("trace", (args, _) => ValueTask.FromResult(args[0]), "x"));

    private static Expr Program(string row, HostOperations operations)
    {
        var parsed = Parser.Parse(Library + row, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    private static async Task<(EvalResult<Evaluator.CountedResult> Result, long Plans)> RunOn(string row, int mode)
    {
        var observations = new EvaluationObservations();
        var operations = mode == 2 ? AsyncTrace : Trace;
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
        //    An ordinary member call is named by its member name, as the ordinary intrinsic row and as a plan
        //    (Lean's planned member route named the path `Pack.F` until the E-18 member-route correction of
        //    November 11 2026 aligned it: `NeedPlan.writtenDispatchName`). The GROUPED member callee is a
        //    written call and keeps its path on both routes.
        { "Pack.F(1)", "NoMatchingBranch",
            "while evaluating dotCall .F of Pack @[15:1, 15:10) > NoMatchingBranch(F) @" },
        { "Id(Pack.F(1))", "NoMatchingBranch",
            "while evaluating call to Id @[15:4, 15:13) > while evaluating dotCall .F of Pack @[15:4, 15:13) > NoMatchingBranch(F) @" },
        { "(Pack.F)(1)", "NoMatchingBranch",
            "while evaluating call to Pack.F @[15:1, 15:12) > NoMatchingBranch(Pack.F) @" },
        { "Id((Pack.F)(1))", "NoMatchingBranch",
            "while evaluating call to Id @[15:4, 15:15) > while evaluating call to Pack.F @[15:4, 15:15) > NoMatchingBranch(Pack.F) @" },
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

    /// <summary>The planned member rows really run as invocation plans and name the member like the ordinary rows.</summary>
    [Theory]
    [InlineData("Pack.F(1)", "Id(Pack.F(1))", "F")]
    [InlineData("Box5.Algorithm(1)", "Id(Box5.Algorithm(1))", "Algorithm")]
    [InlineData("(Pack.F)(1)", "Id((Pack.F)(1))", "Pack.F")]
    public async Task ThePlannedMemberCall_IsAPlan_AndNamesItsDispatchLikeTheOrdinaryForm(string ordinary, string planned, string name)
    {
        foreach (var mode in new[] { 0, 1, 2 })
        {
            var (plain, plainPlans) = await RunOn(ordinary, mode);
            var (plan, plannedPlans) = await RunOn(planned, mode);
            Assert.Equal(plainPlans + 1, plannedPlans);
            Assert.Equal(name, InnermostName(plain.Error));
            Assert.Equal(name, InnermostName(plan.Error));
        }
    }

    // ── The receiver's own failure on the `.Algorithm` route (E-18, November 11 2026) ──────────────────

    /// <summary>The context frames of a failure, then its payload — a missing output with its origin; no spans.</summary>
    private static string Shape(EvalError error)
    {
        var frames = new List<string>();
        while (error is EvalError.WithContext context)
        {
            frames.Add(context.Context);
            error = context.Inner;
        }
        frames.Add(error is EvalError.MissingOutput missing
            ? $"MissingOutput({(missing.IsNested ? "nested" : "own")})"
            : error.GetType().Name);
        return string.Join(" > ", frames);
    }

    /// <summary>
    /// A receiver that fails BEFORE it yields a call reference — here one with no output — reports the same
    /// failure whether <c>t.Algorithm(args)</c> runs as the ordinary intrinsic or as a retained invocation plan:
    /// the plan's retained receiver cell keeps the ordinary invocation receiver evaluator
    /// (<c>InvocationReceiverSuspension</c>, D-3), so the missing output is the intrinsic's NESTED receiver
    /// failure on both routes, with no property frame of its own. Lean's planned route read the receiver as
    /// an ordinary supplied VALUE (the receiver's OWN missing output under a property frame) until the E-18
    /// receiver-read correction of November 11 2026 gave its plan the same retained invocation receiver cell
    /// (<c>NeedInvocationRole</c>, <c>EvalBody.invocationReceiverValue</c>); the regression is
    /// <c>PlanRouteBridgeGuards.algorithmReceiverFailureAgrees</c>.
    /// </summary>
    [Theory]
    [InlineData("NoOut.Algorithm(0)", "Id(NoOut.Algorithm(0))", "while evaluating dotCall .Algorithm of NoOut")]
    [InlineData("(NoOut.Algorithm)(0)", "Id((NoOut.Algorithm)(0))", "while evaluating call to NoOut.Algorithm")]
    public async Task AReceiverWithoutOutput_FailsAlike_AsTheOrdinaryIntrinsicAndAsAPlan(string ordinary, string planned, string frame)
    {
        const string library = "NoOut = { V = 1 }\n";
        foreach (var mode in new[] { 0, 1, 2 })
        {
            var (plain, plainPlans) = await RunOn(library + ordinary, mode);
            var (plan, plannedPlans) = await RunOn(library + planned, mode);
            Assert.True(plain.IsError && plan.IsError, $"{ordinary} mode {mode}: expected failures");
            Assert.Equal(plainPlans + 1, plannedPlans);
            Assert.Equal("MissingOutput", plain.Error.Code.ToString());
            Assert.Equal("MissingOutput", plan.Error.Code.ToString());
            Assert.Equal($"{frame} > MissingOutput(nested)", Shape(plain.Error));
            Assert.Equal($"while evaluating call to Id > {frame} > MissingOutput(nested)", Shape(plan.Error));
        }
    }

    // ── The planned route's receiver READ is the ordinary invocation receiver read (D-3) ───────────────
    //
    // E-18 receiver-read correction (November 11 2026): the cases Lean's planned `.Algorithm` route got wrong
    // while its receiver cell was an ordinary supplied VALUE — a receiver without output, a member-path
    // receiver, a nested `.Algorithm` receiver, a parameter receiver under a spread — and their neighbours.
    // C# was the reference on every one of them; these tests pin that reference for the three engines, and
    // `PlanRouteBridgeGuards` pins the same programs for Lean.

    private const string ReceiverLibrary = """
        NoOut = { V = 1 }
        Lib = { Sub = { K = 3 } }
        Inner = NoOut + 1
        Al = NoOut
        RA = R
        Forced(a, b) = if(a > 0, b, b)
        Ignore(meta op) = 0
        Twice(meta op) = op.Invoke() + op.Invoke()
        Both(meta op) = op.Algorithm(0) + op.Invoke()
        Dup(x) = x + x
        PO(r) = r.Algorithm(0)
        PP(r) = Id(r.Algorithm(0))
        PI(r) = Capture(r.Algorithm(0)).Invoke()
        SO(r) = [r.Algorithm(0)*]
        SJ(r) = [Id(r.Algorithm(0))*]
        SI(r) = [Capture(r.Algorithm(0)).Invoke()*]
        LinkOf(r) = Capture(r.Algorithm(0)).Algorithm(0)
        PT(r) = Twice(r.Algorithm(0))

        """;

    private const string IdFrame = "while evaluating call to Id > ";
    private const string InvokeFrame = "while evaluating dotCall .Invoke of Capture(...) > ";

    /// <summary>An invocation whose RECEIVER read fails, and the ordinary intrinsic's failure shape.</summary>
    public static TheoryData<string, string> ReceiverFailures => new()
    {
        // A receiver without output: the intrinsic's nested receiver failure, no property frame.
        { "NoOut.Algorithm(0)", "while evaluating dotCall .Algorithm of NoOut > MissingOutput(nested)" },
        { "(NoOut.Algorithm)(0)", "while evaluating call to NoOut.Algorithm > MissingOutput(nested)" },
        // A member-path receiver: no frame of the path's own dot evaluation.
        { "Lib.Sub.Algorithm(0)", "while evaluating dotCall .Algorithm of Lib.Sub > MissingOutput(nested)" },
        { "{ V = 1 }.Algorithm(0)", "while evaluating dotCall .Algorithm of {...} > MissingOutput(nested)" },
        // A missing output nested in the receiver's own evaluation keeps its frames.
        { "Inner.Algorithm(0)", "while evaluating dotCall .Algorithm of Inner > while evaluating property NoOut > MissingOutput(nested)" },
        { "Al.Algorithm(0)", "while evaluating dotCall .Algorithm of Al > while evaluating property NoOut > MissingOutput(nested)" },
        // A receiver that is itself a written call is read as the ordinary call, never as a plan of its own.
        { "Id(NoOut).Algorithm(0)", "while evaluating dotCall .Algorithm of Id(...) > while evaluating call to Id > while evaluating property NoOut > MissingOutput(nested)" },
        // A nested reference failure: the receiver `R.Algorithm` is the intrinsic's bare VALUE read, with its
        // own dot-call frame.
        { "R.Algorithm.Algorithm(0)", "while evaluating dotCall .Algorithm of R.Algorithm > while evaluating dotCall .Algorithm of R > NoMatchingBranch" },
        // A value receiver that is no call reference.
        { "5.Algorithm(0)", "while evaluating dotCall .Algorithm of 5 > TypeMismatch" },
    };

    /// <summary>
    /// The receiver's failure is the ordinary intrinsic's on every route: the top-level row (no plan), the
    /// plan read through a parameter (<c>Id(row)</c>) and the plan executed afresh
    /// (<c>Capture(row).Invoke()</c>) report the same context chain, payload and missing-output origin below
    /// their own consumer frame — on the three engines.
    /// </summary>
    [Theory]
    [MemberData(nameof(ReceiverFailures))]
    public async Task AReceiverFailure_IsTheOrdinaryIntrinsicsFailure_AsAPlanReadAndAsAnInvocation(string row, string shape)
    {
        foreach (var mode in new[] { 0, 1, 2 })
        {
            var (plain, plainPlans) = await RunOn(ReceiverLibrary + row, mode);
            var (read, readPlans) = await RunOn(ReceiverLibrary + $"Id({row})", mode);
            var (invoked, invokedPlans) = await RunOn(ReceiverLibrary + $"Capture({row}).Invoke()", mode);
            Assert.True(plain.IsError && read.IsError && invoked.IsError, $"{row} mode {mode}: expected failures");
            Assert.Equal(plainPlans + 1, readPlans);
            Assert.Equal(plainPlans + 1, invokedPlans);
            Assert.Equal(shape, Shape(plain.Error));
            Assert.Equal(IdFrame + shape, Shape(read.Error));
            Assert.Equal(InvokeFrame + shape, Shape(invoked.Error));
            Assert.Equal(plain.Error.Code, read.Error.Code);
            Assert.Equal(plain.Error.Code, invoked.Error.Code);
        }
    }

    /// <summary>
    /// A spread distinguishes its operand's OWN missing output (<c>SpreadMissingOutput</c>) from a nested one.
    /// The receiver's missing output is nested on every route, so the three consumers stay
    /// <c>MissingOutput(nested)</c> under a spread.
    /// </summary>
    [Theory]
    [InlineData("[NoOut.Algorithm(0)*]")]
    [InlineData("[Id(NoOut.Algorithm(0))*]")]
    [InlineData("[Capture(NoOut.Algorithm(0)).Invoke()*]")]
    [InlineData("[Capture((NoOut.Algorithm)(0)).Invoke()*]")]
    public async Task UnderASpread_TheReceiversMissingOutput_StaysNested_OnEveryRoute(string row)
    {
        foreach (var mode in new[] { 0, 1, 2 })
        {
            var (result, _) = await RunOn(ReceiverLibrary + row, mode);
            Assert.True(result.IsError, $"{row} mode {mode}: expected a failure");
            Assert.Equal("MissingOutput", result.Error.Code.ToString());
            Assert.EndsWith(" > MissingOutput(nested)", Shape(result.Error), StringComparison.Ordinal);
            Assert.DoesNotContain("property NoOut", Shape(result.Error), StringComparison.Ordinal);
        }
    }

    /// <summary>
    /// A PARAMETER receiver keeps its own cell (D-3), and the planned invocation still reads the WRITTEN
    /// parameter through the ordinary invocation receiver evaluator: the ordinary row, the plan read through
    /// a parameter, the plan invoked afresh, and each of them under a spread report the same receiver failure
    /// — nested, with the frames the ordinary intrinsic gives it.
    /// </summary>
    [Theory]
    [InlineData("NoOut", "while evaluating dotCall .Algorithm of r > while evaluating property NoOut > MissingOutput(nested)")]
    [InlineData("{ V = 1 }", "while evaluating dotCall .Algorithm of r > while evaluating parameter r > MissingOutput(nested)")]
    [InlineData("Lib.Sub", "while evaluating dotCall .Algorithm of r > while evaluating dotCall .Sub of Lib > MissingOutput(nested)")]
    [InlineData("Inner", "while evaluating dotCall .Algorithm of r > while evaluating property NoOut > MissingOutput(nested)")]
    public async Task AParameterReceiverFailure_IsTheOrdinaryIntrinsicsFailure_OnEveryRoute(string argument, string tail)
    {
        foreach (var mode in new[] { 0, 1, 2 })
        {
            foreach (var wrapper in new[] { "PO", "PP", "PI", "SO", "SJ", "SI" })
            {
                var (result, plans) = await RunOn(ReceiverLibrary + $"{wrapper}({argument})", mode);
                Assert.True(result.IsError, $"{wrapper}({argument}) mode {mode}: expected a failure");
                Assert.Equal("MissingOutput", result.Error.Code.ToString());
                Assert.EndsWith(tail, Shape(result.Error), StringComparison.Ordinal);
                Assert.Equal(wrapper is "PO" or "SO" ? 0 : 1, plans);
            }
        }
    }

    /// <summary>
    /// The plan's CALLEE LINK observed through <c>.Algorithm</c> — not an execution of the plan — demands a
    /// parameter receiver's transported cell (the link's own channel, D-3); the fresh call of the captured
    /// callee succeeds over a forwarded call reference.
    /// </summary>
    [Theory]
    [InlineData("LinkOf(NoOut)", false, "while evaluating call to LinkOf > while evaluating dotCall .Algorithm of Capture(...) > while evaluating property NoOut > MissingOutput(nested)")]
    [InlineData("LinkOf(R)", true, "0")]
    public async Task ThePlansCalleeLink_OverAParameterReceiver_ReadsTheTransportedCell(string row, bool succeeds, string expected)
    {
        foreach (var mode in new[] { 0, 1, 2 })
        {
            var (result, _) = await RunOn(ReceiverLibrary + row, mode);
            Assert.Equal(succeeds, result.IsOk);
            Assert.Equal(expected, succeeds ? InvocationRouteCorpus.Value(result.Value.Value) : Shape(result.Error));
        }
    }

    /// <summary>
    /// The receiver is read LAZILY and ONCE per plan (D-3). <c>Forced(tick(), R)</c> advances the run's
    /// <c>tick()</c> counter each time it is evaluated, so the final <c>tick()</c> counts the receiver reads:
    /// capture alone reads nothing; two <c>Invoke()</c>s, the plan's <c>.Algorithm</c> followed by an
    /// <c>Invoke()</c>, and two reads of the plan's VALUE each read the receiver once; a PARAMETER receiver's
    /// argument is evaluated once however often its plan executes (<c>PT</c>); two ordinary rows read it once
    /// each. Successful invocations over an alias and over a forwarded parameter keep their values.
    /// </summary>
    [Theory]
    [InlineData("Ignore(Forced(tick(), R).Algorithm(0)), tick()", "(0, 1)")]
    [InlineData("Twice(Forced(tick(), R).Algorithm(0)), tick()", "(0, 2)")]
    [InlineData("Both(Forced(tick(), R).Algorithm(0)), tick()", "(0, 2)")]
    [InlineData("Dup(Forced(tick(), R).Algorithm(0)), tick()", "(0, 2)")]
    [InlineData("Twice((Forced(tick(), R).Algorithm)(0)), tick()", "(0, 2)")]
    [InlineData("PT(Forced(tick(), R)), tick()", "(0, 2)")]
    [InlineData("Forced(tick(), R).Algorithm(0) + Forced(tick(), R).Algorithm(0), tick()", "(0, 3)")]
    [InlineData("RA.Algorithm(0), Id(RA.Algorithm(0)), Capture(RA.Algorithm(0)).Invoke()", "(0, 0, 0)")]
    [InlineData("PO(R), PP(R), PI(R), SO(R), SJ(R), SI(R)", "(0, 0, 0, [0], [0], [0])")]
    public async Task TheRetainedReceiver_IsReadLazilyAndOncePerPlan_OnEveryEngine(string row, string expected)
    {
        foreach (var mode in new[] { 0, 1, 2 })
        {
            var (result, _) = await RunOn(ReceiverLibrary + row, mode);
            Assert.True(result.IsOk, $"{row} mode {mode}: {(result.IsError ? Shape(result.Error) : "")}");
            Assert.Equal(expected, InvocationRouteCorpus.Value(result.Value.Value));
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
