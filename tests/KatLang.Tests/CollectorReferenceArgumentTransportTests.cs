using KatLang.Evaluation;

namespace KatLang.Tests;

/// <summary>
/// A REFERENCE TO A RETAINED COLLECTOR SURVIVES AN ORDINARY ARGUMENT BOUNDARY (NEED-07, owner-authorized
/// November 2026): <c>Pass(A)</c> and <c>Pass(Box.A)</c> supply ONE ordinary argument, and only a later
/// explicit <c>v*</c> opens the collector's element cells, without materializing the whole collector. The
/// argument keeps its own cell, so VALUE and CALLABLE are unchanged; the star reads what that cell retains
/// (<c>Evaluator.WrittenCollectorSlice</c>, Lean <c>EvalBody.transparentCollectorSlice?</c> over
/// <c>EvalBody.retainedCellSlice?</c>). Every expectation is written from the contract and runs on the six
/// routes (<see cref="SixRouteAgreement"/>), which compare values, the ordered host-call log and every
/// structured error; <c>trace</c> genuinely suspends on the twin routes. Lean:
/// <c>CoreTests/CollectingCallableForwarding.lean</c> section 10, <c>WholeAlgorithmTransport.lean</c>; spec
/// cases <c>collector-reference-argument-*</c>.
/// </summary>
public sealed class CollectorReferenceArgumentTransportTests
{
    private const string Ignore = "Coll(*ys) = 0\nPass(v) = Coll(v*)\n";
    private const string Keep = "Coll(*ys) = ys\nPass(v) = Coll(v*)\n";
    private const string BoxA = "Box = {\npublic A = xs\n0\n}";

    private static async Task<SixRouteAgreement.Observation> Ok(string source, string expected, params string[] host)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation.Kind == "ok" && observation.Value == expected, $"expected {expected}, got {observation}\nsource:\n{source}");
        Assert.Equal(host, observation.HostCalls);
        return observation;
    }

    private static async Task<SixRouteAgreement.Observation> Fails(string source, string code, params string[] host)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation.Kind == "err" && observation.Errors.Single().StartsWith(code + ":", StringComparison.Ordinal),
            $"expected {code}, got {observation}\nsource:\n{source}");
        Assert.Equal(host, observation.HostCalls);
        return observation;
    }

    private static string InF(string body, string call) => $"F(*xs) = {{\n{body}\n}}\n{call}";

    // ── The witnesses ───────────────────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("A = xs\nPass(A)")]
    [InlineData(BoxA + "\nPass(Box.A)")]
    [InlineData("Pass(xs)")]
    public Task PrimaryWitnesses_NeverDemandTheFailingElement(string body)
        => Ok(Ignore + InF(body, "F(1 / 0)"), "0");

    [Theory]
    [MemberData(nameof(CollectingCallableForwardingLawTests.ReferenceChains), MemberType = typeof(CollectingCallableForwardingLawTests))]
    public async Task EveryReferenceSpelling_CrossesTheBoundary(string declarations, string operand)
    {
        await Ok(Ignore + InF($"{declarations}\nPass({operand})", "F(1 / 0)"), "0");
        await Ok(Keep + InF($"{declarations}\nPass({operand})", "F(1, 2)"), "L[1, 2]");
    }

    [Fact]
    public Task AnOpenProvidedReference_CrossesTheBoundary()
        => Ok(Ignore + InF("open Box\nBox = {\npublic A = xs\n0\n}\nPass(A)", "F(1 / 0)"), "0");

    [Theory]
    [InlineData("Relay(w) = Pass(w)\n", "A = xs\nRelay(A)")]
    [InlineData("Relay(w) = Pass(w)\nOuter(u) = Relay(u)\n", "A = xs\nOuter(A)")]
    [InlineData("Relay(w) = {\nB = w\nPass(B)\n}\n", "A = xs\nRelay(A)")]
    [InlineData("Relay(w) = {\nBox = {\npublic B = w\n0\n}\nPass(Box.B)\n}\n", BoxA + "\nRelay(Box.A)")]
    [InlineData("Relay(w) = {\nB = w\nC = B\nPass(C)\n}\nOuter(u) = {\nD = u\nRelay(D)\n}\n", "A = xs\nOuter(A)")]
    public async Task FurtherBoundaries_KeepTheOriginalCells(string helpers, string body)
    {
        await Ok(Ignore + helpers + InF(body, "F(1 / 0)"), "0");
        await Ok(Keep + helpers + InF(body, "F(1, 2)"), "L[1, 2]");
    }

    [Theory]
    [InlineData("Pass(v) = {\nB = v\nColl(B*)\n}\n")]
    [InlineData("Pass(v) = {\nBox = {\npublic B = v\n0\n}\nColl(Box.B*)\n}\n")]
    [InlineData("Pass(v) = {\nH = Coll(v*)\nH\n}\n")]
    public Task TheSpreadMayItselfBeWrittenThroughAReference(string pass)
        => Ok("Coll(*ys) = 0\n" + pass + InF("A = xs\nPass(A)", "F(1 / 0)"), "0");

    [Fact]
    public async Task AnExtensionDotArgument_IsTheSameOrdinaryArgument()
    {
        await Ok(Ignore + InF("A = xs\nA.Pass", "F(1 / 0)"), "0");
        await Ok(Ignore + InF("xs.Pass", "F(1 / 0)"), "0");
    }

    // ── One ordinary argument until an explicit spread ──────────────────────────────────────────

    [Theory]
    [InlineData("F()", "0")]
    [InlineData("F(1 / 0)", "1")]
    [InlineData("F(1, 2, 3)", "3")]
    [InlineData("F(())", "1")]
    public async Task OnlyTheExplicitStar_OpensTheSupply(string call, string opened)
    {
        const string counts = "N(*ys) = ys.count\n";
        await Ok(counts + "Pass(v) = N(v)\n" + InF("A = xs\nPass(A)", call), "1");
        await Ok(counts + "Pass(v) = N(v*)\n" + InF("A = xs\nPass(A)", call), opened);
    }

    [Theory]
    [InlineData("F()", "L[]")]
    [InlineData("F(1)", "L[1]")]
    [InlineData("F(1, 2, 3)", "L[1, 2, 3]")]
    [InlineData("F([1, 2], [3])", "L[L[1, 2], L[3]]")]
    [InlineData("F([])", "L[L[]]")]
    [InlineData("F((1, 2), 3)", "L[S[1, 2], 3]")]
    [InlineData("F((), 1)", "L[S[], 1]")]
    public async Task Shape_IsTheCollectorsExactly(string call, string expected)
    {
        await Ok(Keep + InF("A = xs\nPass(A)", call), expected);
        await Ok(Keep + InF("Pass(xs)", call), expected);
    }

    [Fact]
    public async Task AWrongOrdinaryArgumentCount_StillRejectsBeforeAnyValue()
    {
        await Fails("Pass(a, b) = 0\n" + InF("A = xs\nPass(A)", "F(1 / 0, 2)"), "ArityMismatch");
        await Fails("Pass(a, b) = 0\n" + InF("A = xs\nPass(A)", "F(trace(1), trace(2))"), "ArityMismatch");
    }

    // ── No unwanted effects, one completion ─────────────────────────────────────────────────────

    [Theory]
    [InlineData("A = xs\nPass(A)")]
    [InlineData(BoxA + "\nPass(Box.A)")]
    public async Task IgnoredElements_DoNoWork(string body)
    {
        await Ok(Ignore + InF(body, "F(trace(1), trace(2))"), "0");
        await Ok(Ignore + InF(body + ", tick()", "F(tick(), tick())"), "S[0, 1]");
    }

    [Theory]
    [InlineData("Pass(v) = Head(v*), Head(v*)\n", "S[1, 1]", "trace(1)")]
    [InlineData("Pass(v) = Head(v*), v\n", "S[1, L[1, 2]]", "trace(1)", "trace(2)")]
    [InlineData("Pass(v) = v, Head(v*)\n", "S[L[1, 2], 1]", "trace(1)", "trace(2)")]
    [InlineData("Pass(v) = Head(v*), Last(v*), v\n", "S[1, 2, L[1, 2]]", "trace(1)", "trace(2)")]
    public Task EachOriginalComputation_CompletesOnce(string pass, string expected, params string[] host)
        => Ok("Head(a, *r) = a\nLast(a, b) = b\n" + pass + InF("A = xs\nPass(A)", "F(trace(1), trace(2))"), expected, host);

    [Fact]
    public async Task AReferenceCompletedByValue_StillOpensTheOriginalCells()
    {
        // The argument's whole VALUE completes first. The later star opens the same original cells, so an
        // element is not re-run, and a callable element keeps its CALLABLE, which an opened value could not.
        await Ok(Keep + InF("A = xs\nT = A.sum\nT, Pass(A)", "F(trace(1), trace(2))"), "S[3, L[1, 2]]", "trace(1)", "trace(2)");
        await Ok("K = trace(5)\nCall(f, *rest) = f()\nPass(v) = v, Call(v*)\n" + InF("A = xs\nPass(A)", "F(K)"), "S[L[5], 5]", "trace(5)", "trace(5)");
    }

    [Fact]
    public async Task IndependentComputations_StayIndependent()
    {
        // Two written `tick()` are two computations; two opened references to one element are one.
        await Ok(Keep + InF("A = xs\nPass(A)", "F(tick(), tick())"), "L[1, 2]");
        await Ok("Head(a, *r) = a\nPass(v) = Head(v*)\n" + InF("A = xs\nPass(A), Pass(A), xs", "F(tick(), tick())"), "S[1, 1, L[1, 2]]");
    }

    // ── CALLABLE ────────────────────────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("A = xs\nPass(A)")]
    [InlineData(BoxA + "\nPass(Box.A)")]
    [InlineData("A = xs\nB = A\nPass(B)")]
    [InlineData("Pass(xs)")]
    public Task TheOriginalAlgorithmStaysInvocable(string body)
        => Ok("Inc(x) = x + 1\nApply(f, *rest) = f(9)\nPass(v) = Apply(v*)\n" + InF(body, "F(Inc, 1 / 0)"), "10");

    [Fact]
    public Task TheCallableChannelSurvivesFurtherBoundaries()
        => Ok("Inc(x) = x + 1\nApply(f, *rest) = f(9)\nPass(v) = Apply(v*)\nRelay(w) = {\nB = w\nPass(B)\n}\n" + InF("A = xs\nRelay(A)", "F(Inc, 1 / 0)"), "10");

    [Fact]
    public Task TheReferenceArgumentItself_HasNoCollectorCallable()
        => Fails("Apply(f) = f(9)\n" + InF("A = xs\nApply(A)", "F(1)"), "NotAnAlgorithm");

    // ── Precedence ──────────────────────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("A = xs\nPass(A)")]
    [InlineData(BoxA + "\nPass(Box.A)")]
    [InlineData("Pass(xs)")]
    public Task AWrongArityCallee_RejectsOnTheKnownCount(string body)
        => Fails("Two(a, b) = a\nPass(v) = Two(v*)\n" + InF(body, "F(1 / 0)"), "ArityMismatch");

    [Theory]
    [InlineData("A = xs\nSel(A)")]
    [InlineData(BoxA + "\nSel(Box.A)")]
    [InlineData("Sel(xs)")]
    public async Task ASelectorSpread_FollowsTheSameLaw(string body)
    {
        await Ok("Sel(v) = [10, 20, 30][v*]\n" + InF(body, "F(2, 0)"), "S[30, 10]");
        await Fails("Sel(v) = [10, 20][99, v*]\n" + InF(body, "F(1 / 0)"), "BadIndex");
        await Fails("Sel(v) = [10, 20][v*]\n" + InF(body, "F(0, 1 / 0)"), "DivisionByZero");
    }

    [Fact]
    public async Task ASelectorSpread_LeavesItsReceiverEager()
        => await Fails("Sel(v) = [10, 1 / 0][v*]\n" + InF("A = xs\nSel(A)", "F(0)"), "DivisionByZero");

    // ── Captured calls ──────────────────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("Cap(meta r) = r.Arguments.count\n", "1")]
    [InlineData("Cap(meta r) = 0\n", "0")]
    [InlineData("Cap(meta r) = r.Invoke()\n", "0")]
    [InlineData("Cap(meta r) = Coll(r.Arguments*)\n", "0")]
    public Task ACapturedCall_KeepsItsOneArgumentAndStaysInert(string cap, string expected)
        => Ok(Ignore + cap + InF("A = xs\nCap(Pass(A))", "F(trace(1), 1 / 0)"), expected);

    [Fact]
    public Task AnUninvokedTarget_DoesNoWork()
        => Ok("Pass(v) = trace(7)\nCap(meta r) = r.Arguments.count\n" + InF("A = xs\nCap(Pass(A))", "F(1 / 0)"), "1");

    [Fact]
    public Task EveryInvocation_ReopensTheSameCells()
        => Ok("Head(a, *r) = a\nPass(v) = Head(v*)\nCap(meta r) = r.Invoke(), r.Invoke()\n" + InF("A = xs\nCap(Pass(A))", "F(trace(1), 1 / 0)"), "S[1, 1]", "trace(1)");

    // ── Ownership ───────────────────────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("Pass(A) = Coll(A*)\n")]
    [InlineData("Pass(xs) = Coll(xs*)\n")]
    [InlineData("Pass(v) = {\nA = 7\nColl(v*)\n}\n")]
    public Task TheReceivingSite_CapturesNothing(string pass)
        => Ok("Coll(*ys) = ys\n" + pass + InF("A = xs\nPass(A)", "F(1, 2)"), "L[1, 2]");

    [Fact]
    public Task AShadowingDeclaration_SelectsItsOwnBinding()
        => Ok(Keep + InF("A = xs\nH = {\nA = 5\nPass(A)\n}\nH", "F(1, 2)"), "L[5]");

    [Fact]
    public Task EqualActivations_ShareNothing()
        => Ok(Keep + InF("A = xs\nPass(A)", "F(trace(1)), F(trace(1)), F(2)"), "S[L[1], L[1], L[2]]", "trace(1)", "trace(1)");

    [Fact]
    public async Task SeparateRuns_ShareNothing()
    {
        var source = Keep + InF("A = xs\nPass(A)", "F(tick(), tick())");
        await Ok(source, "L[1, 2]");
        await Ok(source, "L[1, 2]");
    }

    // ── Negative controls ───────────────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("A = { xs }\nPass(A)")]
    [InlineData("A = xs\nB = { A }\nPass(B)")]
    [InlineData("A = { xs }\nB = A\nPass(B)")]
    [InlineData("A = [xs*]\nPass(A)")]
    [InlineData("A = Id(xs*)\nPass(A)")]
    [InlineData("A = xs + 0\nPass(A)")]
    [InlineData("Pass({ xs })")]
    [InlineData("Pass(Id(xs))")]
    [InlineData("Pass([xs*])")]
    [InlineData("Pass((xs, 1))")]
    [InlineData("A = xs\nPass({ A })")]
    [InlineData(BoxA + "\nPass(Box.A())")]
    [InlineData("Box = {\npublic A = { xs }\n0\n}\nPass(Box.A)")]
    public async Task AComputation_StaysAnArbitrarySpread(string body)
    {
        const string helpers = Ignore + "Id(*zs) = zs\n";
        await Fails(helpers + InF(body, "F(1 / 0)"), "DivisionByZero");
    }

    [Fact]
    public async Task AnArbitrarySpread_StillRunsAtFormation()
    {
        await Ok(Ignore + "Id(*zs) = zs\n" + InF("Pass(Id(xs))", "F(trace(1), trace(2))"), "0", "trace(1)", "trace(2)");
        await Ok(Ignore + InF("A = { xs }\nPass(A)", "F(trace(1), trace(2))"), "0", "trace(1)", "trace(2)");
    }

    [Theory]
    [InlineData("Coll(*ys) = 0\nPass(v) = Coll(v*)\nF(x) = {\nA = x\nPass(A)\n}\nF(1 / 0)")]
    [InlineData("Coll(*ys) = 0\nPass(v) = Coll(v*)\nF(x) = Pass(x)\nF(1 / 0)")]
    [InlineData("Coll(*ys) = 0\nPass(v) = Coll(v*)\nPass(1 / 0)")]
    [InlineData("Coll(*ys) = 0\nPass(v) = Coll(v*)\nP = 1 / 0\nPass(P)")]
    [InlineData("Coll(*ys) = 0\nPass(v) = Coll(v*)\nP = 1 / 0\nA = P\nPass(A)")]
    public Task AnOrdinaryFailingArgument_FailsAtTheSpread(string source) => Fails(source, "DivisionByZero");

    [Fact]
    public Task AnUnusedOrdinaryArgument_StaysInert()
        => Ok("Pass(v) = 0\n" + InF("A = { xs }\nPass(A)", "F(1 / 0)"), "0");

    [Theory]
    [InlineData("Reader(b) = Pass(b.A)\nF(*xs) = {\n" + BoxA + "\nReader(Box)\n}\nF(1 / 0)")]
    [InlineData("Box(*xs) = {\npublic A = xs\n0\n}\nF(*xs) = Pass(Box.A)\nF(1 / 0)")]
    public Task AnInaccessibleOrRuntimeMember_KeepsItsRefusal(string source)
        => Fails(Ignore + source, "LocalOnlyProperty");

    // ── Whole VALUE and structural inspection stay eager ────────────────────────────────────────

    [Theory]
    [InlineData("Pass(v) = v\n")]
    [InlineData("Pass(v) = [v*]\n")]
    [InlineData("Pass(v) = (v, 1)\n")]
    [InlineData("Pass(v) = v*\n")]
    [InlineData("Pass(v) = v.sum\n")]
    [InlineData("Pass((h, *t)) = 0\n")]
    [InlineData("Pass([h, *t]) = 0\n")]
    [InlineData("Pass(v) = Keep(v**)\nKeep(*ys) = 0\n")]
    public Task AWholeRead_StillMaterializesEveryElement(string pass)
        => Fails(pass + InF("A = xs\nPass(A)", "F(10, 1 / 0)"), "DivisionByZero");

    [Fact]
    public async Task AWholeRead_KeepsItsCharges()
    {
        const string call = "F(1, 2, 3, 4, 5, 6)";
        var direct = SmallestMaterialization("Pass(v) = v\n" + InF("Pass(xs)", call));
        Assert.Equal(direct, SmallestMaterialization("Pass(v) = v\n" + InF("A = xs\nPass(A)", call)));
        await Ok("Pass(v) = v\n" + InF("A = xs\nPass(A)", "F(1, 2)"), "L[1, 2]");
    }

    // ── Failure, suspension, cancellation ───────────────────────────────────────────────────────

    [Theory]
    [InlineData("1 / 0")]
    [InlineData("[1][9]")]
    public async Task ADemandedElement_RaisesItsOriginalFailure(string element)
    {
        const string helpers = "Head(a, *r) = a\nPass(v) = Head(v*)\n";
        var direct = await SixRouteAgreement.OnEveryRouteAsync(helpers + $"F(*xs) = {{\nA = xs\nPass(xs)\n}}\nF({element}, 2)");
        var reference = await SixRouteAgreement.OnEveryRouteAsync(helpers + $"F(*xs) = {{\nA = xs\nPass(A)\n}}\nF({element}, 2)");
        Assert.Equal("err", reference.Kind);
        Assert.Equal(direct.Errors, reference.Errors);
    }

    private static HostOperations Gate(TaskCompletionSource release, List<string> entered) => HostOperations.Create(
        HostOperation.CreateAsync("wait", async (arguments, _) =>
        {
            lock (entered) entered.Add(SixRouteAgreement.Neutral(arguments[0]));
            await release.Task.ConfigureAwait(false);
            return arguments[0];
        }, "x"));

    private static async Task EnteredAsync(List<string> entered)
    {
        while (true)
        {
            lock (entered) if (entered.Count > 0) return;
            await Task.Yield();
        }
    }

    [Fact]
    public async Task AGenuineSuspension_RunsOnlyTheDemandedElementOnce()
    {
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var entered = new List<string>();
        const string source = "Second(a, b) = b\nPass(v) = Second(v*), Second(v*)\nF(*xs) = {\nA = xs\nPass(A)\n}\nF(wait(1), wait(2))";
        var run = KatLangEngine.RunAsync(source, new RunOptions { HostOperations = Gate(release, entered) });
        await EnteredAsync(entered);
        Assert.False(run.IsCompleted);
        release.SetResult();
        var result = Assert.IsType<RunResult.Success>(await run);
        Assert.Equal("S[2, 2]", SixRouteAgreement.Neutral(result.Value));
        Assert.Single(entered);
    }

    [Fact]
    public async Task CancellationDuringARealSuspension_NeitherRestartsNorLeaksActiveState()
    {
        using var cancellation = new CancellationTokenSource();
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var entered = new List<string>();
        var run = KatLangEngine.RunAsync(
            "Head(a, *r) = a\nPass(v) = Head(v*), Head(v*)\nF(*xs) = {\nA = xs\nPass(A)\n}\nF(wait(1), wait(2))",
            new RunOptions { HostOperations = Gate(release, entered), EvaluationCancellationToken = cancellation.Token });
        await EnteredAsync(entered);
        cancellation.Cancel();
        release.SetResult();
        await Assert.ThrowsAnyAsync<OperationCanceledException>(() => run);
        Assert.Single(entered);
    }

    // ── Scaling and accounting ──────────────────────────────────────────────────────────────────

    private static int SmallestMaterialization(string source)
    {
        for (var limit = 1; limit < 64; limit++)
        {
            var run = KatLangEngine.Run(source, new RunOptions { EvaluationLimits = new EvaluationLimits { MaxMaterializedItems = limit } });
            if (run is RunResult.Success) return limit;
        }
        throw new InvalidOperationException($"no budget below 64 completes:\n{source}");
    }

    [Theory]
    [InlineData("Pass(xs)")]
    [InlineData("A = xs\nPass(A)")]
    [InlineData(BoxA + "\nPass(Box.A)")]
    public void OpeningTheSlice_ReservesNoList(string body)
        => Assert.Equal(1, SmallestMaterialization(Ignore + InF(body, "F(1, 2, 3, 4, 5, 6)")));

    private const string Walk = "Coll(*ys) = 0\nWalk(w, n) = {\nB = w\nif(n == 0, Coll(B*), Walk(B, n - 1))\n}\n";

    [Fact]
    public async Task ALongChain_IsOneLoop_OverTheOriginalCells()
    {
        await Ok(Walk + InF("A = xs\nWalk(A, 30)", "F(1 / 0, trace(2))"), "0");
        Assert.Equal(1, SmallestMaterialization(Walk + InF("A = xs\nWalk(A, 30)", "F(1, 2, 3, 4, 5, 6)")));
    }

    [Fact]
    public void ALongChain_RepeatsNoListPerHop()
    {
        // The call recursion builds the chain; the star at the end walks it. Only that walk is measured, over
        // a slice whose one list costs at least 32 KiB of references. Each hop's classification allocates
        // about 2 KiB of transient lookup state, and no list, so the bound is far below one list per hop.
        // Ordinary non-tail recursion reaches the stack backstop long before a chain could matter (a 100-hop
        // `Walk` stops there with or without references): a chain is bounded by its live activations.
        static long Measure(int hops, string row)
        {
            long started = 0, allocated = -1;
            var operations = HostOperations.Create(
                HostOperation.Create("begin", (_, _) =>
                {
                    started = GC.GetAllocatedBytesForCurrentThread();
                    return new Result.Atom(0);
                }),
                HostOperation.Create("end", (_, _) =>
                {
                    allocated = GC.GetAllocatedBytesForCurrentThread() - started;
                    return new Result.Atom(0);
                }));
            var source = $"Coll(*ys) = 0\nWalk(w, n) = {{\nB = w\nif(n == 0, (begin(), {row}, end()), Walk(B, n - 1))\n}}\n"
                + $"F(*xs) = {{\nA = xs\nWalk(A, {hops})\n}}\nF(range(1, 4096)*)";
            var result = KatLangEngine.Run(source, new RunOptions { HostOperations = operations });
            Assert.IsType<RunResult.Success>(result);
            Assert.True(allocated > 0);
            return allocated;
        }

        const string opened = "Coll(B*)";
        _ = Measure(30, opened);
        _ = Measure(30, "B");
        var small = Measure(2, opened);
        var large = Measure(30, opened);
        Assert.True(large < small + (30 * 4_096), $"small={small}, large={large}");
        var whole = Measure(30, "B");
        Assert.True(whole > large, $"opened={large}, whole={whole}");
    }
}
