using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// LOOP-06 (LOOP-CF1, owner decision of October 2026): a <c>while</c> round reads its step CONDITION
/// FIRST. It forms the step's rows from the LAST row backwards, each row one complete ordinary
/// formation, until a row supplies an item; that row's last item is the Boolean continuation flag.
/// <c>false</c> returns the state that entered the round without forming the remaining earlier rows;
/// <c>true</c> forms them left to right, and the supply without its last item is the next state (a
/// one-item supply is both). Protection is ROW-granular: a call or spread inside one row stays one
/// ordinary value. Every case runs on the six established routes (sync and async engines, the
/// engine's genuinely suspending twin, the generic and optimized evaluators, the forced async twin)
/// and requires the same value, errors and host-call log on all of them and identical budget
/// counters (steps, raw checkpoints, peak depth, item and string reservations) on the three
/// evaluator routes (Q-09b). Lean: <c>WhileRound.conditionFirst</c>, laws
/// <c>KatLangArityLaws/WhileRound.lean</c>, guards <c>CoreTests/LoopConditionFirst.lean</c>.
/// </summary>
public sealed class LoopConditionFirstTests
{
    // Every bounded wait in this file is a hang guard, never a latency claim: what it waits for
    // runs as thread-pool work, which a loaded CI runner can delay well past a tight bound (a
    // 10 s guard timed out in CI in October 2026).
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);

    private const string MarkName = "mark";
    private const string Pack = "Pack(x) = 10 / (x - 1), x > 1\n";
    private const string EmptyMark = "E(n) = if(mark(n) > 0, (), ())\n";
    private const string Capture = "Capture(meta r) = r\nF(x) = x\nR = Capture(F(mark(7)))\n";

    // ── The canonical corpus: value or innermost error kind, and the exact host-effect order ─────

    /// <summary>scenario, source, expected oracle outcome (<c>ok VALUE</c> or <c>err KIND</c>), expected host log.</summary>
    public static TheoryData<string, string, string, string> Corpus() => new()
    {
        // 1/3. Initially false: the division row is never formed; zero transitions return the initial state.
        { "initial false skips division", "Step(x) = 10 / (x - 1), x > 1\nStep.while(1)", "ok 1", "" },
        { "initial false keeps two slots", "S(a, b) = mark(b), mark(a + b), a < 100\nS.while(144, 233)", "ok S[144, 233]", "" },
        // 2/4. Initially true: the flag row first, then the transition rows, every round.
        { "initial true runs transition", "Step(x) = mark(x - 1), mark(x > 1)\nStep.while(3)", "ok 1",
            "mark(true),mark(2),mark(true),mark(1),mark(false)" },
        { "countdown", "Count(x) = mark(x - 1), x > 1\nCount.while(4)", "ok 1", "mark(3),mark(2),mark(1)" },
        // 5/6. Multi-slot state and the canonical iterations keep their values.
        { "fibonacci", "Fib(a, b, n) = b, a + b, n - 1, n > 1\nFib.while(0, 1, 10)", "ok S[34, 55, 1]", "" },
        { "fibonacci stops before the first transition", "Step(a, b) = b, a + b, a < 100\nStep.while(144, 233)", "ok S[144, 233]", "" },
        { "collatz count", "C(n, k) = if(n mod 2 == 0, n / 2, 3 * n + 1), k + 1, n != 1\nC.while(27, 0)[1]", "ok 111", "" },
        { "collatz already stopped", "C(n, k) = mark(if(n mod 2 == 0, n / 2, 3 * n + 1)), k + 1, n != 1\nC.while(1, 0)", "ok S[1, 0]", "" },
        // 8. A shared local property is computed once per round, by the row that demands it first.
        { "shared local demanded by the flag", "S(x) = {\n  D = mark(x - 1)\n  D, D > 0\n}\nS.while(3)", "ok 1",
            "mark(2),mark(1),mark(0)" },
        { "shared local with effectful flag", "S(x) = {\n  Go = mark(x > 1)\n  mark(x - 1), Go\n}\nS.while(3)", "ok 1",
            "mark(true),mark(2),mark(true),mark(1),mark(false)" },
        { "bare local is shared but explicit calls stay fresh",
            "S(x) = {\n  P = mark(x)\n  P + P() + 1, P < 1\n}\nS.while(0)", "ok 1",
            "mark(0),mark(0),mark(1)" },
        // 9/10. What the flag itself needs still runs; protection is row-granular.
        { "flag needs the failing division", "Step(x) = 10 / (x - 1), 10 / (x - 1) > 0\nStep.while(1)", "err DivByZero", "" },
        { "shared failing local", "S(x) = {\n  Q = 10 / (x - 1)\n  Q, Q > 0\n}\nS.while(1)", "err DivByZero", "" },
        { "flag inside an atomic spread", Pack + "Step(x) = Pack(x)*\nStep.while(1)", "err DivByZero", "" },
        { "flag inside an atomic call row runs the call left to right",
            "P(x) = mark(x - 1), mark(x > 1)\nStep(x) = P(x)*\nStep.while(3)", "ok 1",
            "mark(2),mark(true),mark(1),mark(true),mark(0),mark(false)" },
        // 11/12. Trailing empty spreads: discovery forms them right to left, effects included.
        { "trailing empty spread", "Tail(n) = ()\nStep(n) = n + 1, n < 2, Tail(n)*\nStep.while(0)", "ok 2", "" },
        { "effectful trailing empty spreads, false", EmptyMark + "S(x) = mark(x + 1), mark(false), E(2)*, E(3)*\nS.while(1)", "ok 1",
            "mark(3),mark(2),mark(false)" },
        { "effectful trailing empty spreads, true", EmptyMark + "S(x) = mark(x + 1), mark(x < 2), E(2)*, E(3)*\nS.while(1)", "ok 2",
            "mark(3),mark(2),mark(true),mark(2),mark(3),mark(2),mark(false)" },
        { "spread flag row supplies the flag", "Done(n) = (n - 1, n > 1)\nS(a, n) = mark(a + 1), Done(n)*\nS.while(0, 3)", "ok S[2, 1]",
            "mark(1),mark(2)" },
        // 13. Dynamic output cardinality: earlier spreads form only after true.
        { "growing state", "Step(n, *h) = n + 1, (h*, mark(n))*, mark(n < 3)\nStep.while(0)", "ok S[3, 0, 1, 2]",
            "mark(true),mark(0),mark(true),mark(1),mark(true),mark(2),mark(false)" },
        // 14. A family dispatches first, then its selected clause's rows are read condition first.
        { "family-selected body", "F(0) = mark(0), mark(false)\nF(n) = mark(n - 1), mark(n > 0)\nF.while(2)", "ok 0",
            "mark(true),mark(1),mark(true),mark(0),mark(false)" },
        // 15–17. Builtin, host, alias and higher-order steps keep their eligibility.
        { "builtin step", "if.while(true, false, true)", "ok S[true, false, true]", "" },
        { "host step", "mark.while(false)", "ok false", "mark(false)" },
        { "alias step", "Count(x) = mark(x - 1), x > 1\nTwice = Count\nTwice.while(3)", "ok 1", "mark(2),mark(1)" },
        { "higher-order step", "Count(x) = mark(x - 1), x > 1\nRun(f, x) = f.while(x)\nRun(Count, 3)", "ok 1", "mark(2),mark(1)" },
        { "block step", "{ mark(x - 1), mark(x > 1) }.while(3)", "ok 1", "mark(true),mark(2),mark(true),mark(1),mark(false)" },
        // 18/19. One effective item is both the flag and the state; no item is the missing-flag BadArity.
        { "one-item supply", "S(x) = not x\nS.while(false)", "ok true", "" },
        { "one-item supply false", "S(x) = mark(not x)\nS.while(true)", "ok true", "mark(false)" },
        { "all-empty output", "E(x) = ()\nS(x) = E(x)*, E(x)*\nS.while(1)", "err BadArity", "" },
        { "non-Boolean flag", "S(x) = 1 / 0, 5\nS.while(1)", "err TypeMismatch", "" },
        { "non-Boolean flag precedes a failing row", "S(x) = 1 / 0, 'a' < 1\nS.while(1)", "err TypeMismatch", "" },
        // 20. The next round's binding checks the accepted state's arity; a false round forms no candidate.
        { "next-round arity mismatch", "Bad(a, b) = a + b, true\nBad.while(1, 2)", "err ArityMismatch", "" },
        { "discarded candidate arity", "Bad(a, b) = (a, b, a)*, a > 5\nBad.while(1, 2)", "ok S[1, 2]", "" },
        // 21. A failing initial component fails at the final materialization (LOOP-07); an overwritten one never runs.
        { "failing unread initial component", "S(x, y) = x - 1, y, x > 0\nS.while(0, 1 / 0)", "err DivByZero", "" },
        { "overwritten failing initial component", "S(x, y) = x - 1, 0, x > 0\nS.while(1, 1 / 0)", "ok S[0, 0]", "" },
        // 22. Lazy initial cells are demanded in flag-first order.
        { "lazy initial-cell order", "S(a, b) = a + b, b > 100\nS.while(mark(1), mark(2))", "ok S[1, 2]", "mark(2),mark(1)" },
        // 25/26. The independent review's counterexamples: neither direction of effect inclusion holds.
        { "old success becomes failure", "S(x) = 1 / (1 - pulse()), pulse() == 0\nS.while(2)", "err DivByZero", "pulse#0,pulse#1" },
        { "old failure becomes success", "S(x) = 1 / 0, mark(false)\nS.while(1)", "ok 1", "mark(false)" },
        // 27. A diverging or cyclic transition row is skipped by a false flag.
        { "skipped nested divergence", "Spin(x) = x + 1, true\nS(x) = Spin.while(x), mark(false)\nS.while(1)", "ok 1", "mark(false)" },
        { "skipped cyclic local", "S(x) = {\n  P = P + 1\n  P, x > 1\n}\nS.while(1)", "ok 1", "" },
        { "nested loop in the flag", "In(k) = k + 1, k < 2\nS(x) = mark(x + 1), mark(In.while(x)) > x\nS.while(0)", "ok 2",
            "mark(2),mark(1),mark(2),mark(2),mark(2)" },
        // 30. Handover from the planned round after a true verdict: no row is re-formed.
        { "zero-emission handover keeps the single-item rule",
            "W(x) = if(x == 2, (), x + 1)\nS(x) = W(x)*, mark(x != true)\nS.while(1)", "ok true",
            "mark(true),mark(true),mark(false)" },
        { "multi-emission handover", "G(x) = (x + 1, x + 1)\nS(x) = G(x)*, mark(x < 1)\nS.while(0)", "err ArityMismatch", "mark(true)" },
        // 31/32. META references and argument views cross rounds and the final VALUE boundary unchanged.
        { "call reference carried across rounds",
            Capture + "S(r, k) = {\n  V = r.Invoke()\n  r, k + V, k < 14\n}\nS.while(R, 0)[1]", "ok 14", "mark(7)" },
        { "Invoke reruns the target but retains its argument cell",
            "Capture(meta r) = r\nF(x) = mark(x)\nR = Capture(F(mark(7)))\n"
                + "S(r, k) = r, k + r.Invoke(), k < 14\nS.while(R, 0)[1]", "ok 14",
            "mark(7),mark(7),mark(7)" },
        { "META step capture stays inert until false-round final materialization",
            "F(x) = mark(x)\nS(meta r) = r.Invoke(), false\nS.while(F(mark(7)))", "ok 7",
            "mark(7),mark(7)" },
        { "argument view forwards the same cell across rounds",
            Capture + "Read(x) = x\nS(r, k) = r, k + Read(r.Arguments*), k < 14\nS.while(R, 0)[1]",
            "ok 14", "mark(7)" },
        { "argument view inspected, never demanded",
            Capture + "S(v) = v[0], v.count < 0\nS.while(R.Arguments)", "err TypeMismatch", "" },
        { "spread argument view, false round, final materialization",
            Capture + "S(x) = mark(x + 1), false\nS.while(R.Arguments*)", "ok 7", "mark(7)" },
        // repeat is unchanged: its rows are formed left to right.
        { "repeat stays left to right", "S(x) = mark(x - 1), mark(x > 1)\nrepeat(S, 1, 3)", "ok S[2, true]", "mark(2),mark(true)" },
        { "ordinary call stays left to right", "S(x) = mark(x - 1), mark(x > 1)\nS(3)", "ok S[2, true]", "mark(2),mark(true)" },
    };

    [Theory]
    [MemberData(nameof(Corpus))]
    public async Task Corpus_AgreesOnEveryRoute(string scenario, string source, string expected, string hostLog)
    {
        var (oracle, _) = await AllRoutesAsync(source);
        Assert.True(expected == oracle.Outcome, $"{scenario}: expected {expected}, got {oracle}");
        Assert.True(hostLog == string.Join(",", oracle.HostCalls), $"{scenario}: host log {string.Join(",", oracle.HostCalls)}");
    }

    // ── Newton convergence and seeded random draws ──────────────────────────────────────────────────

    [Fact]
    public async Task Newton_ConvergesOnEveryRoute()
    {
        var (oracle, _) = await AllRoutesAsync("N(x) = (x + 2 / x) / 2, abs(x * x - 2) > 0.000001\nN.while(1)");
        Assert.StartsWith("ok 1.41421356", oracle.Outcome);
    }

    /// <summary>
    /// Draws follow the new demand order: the flag row's draw precedes the transition's, and a false
    /// round draws no transition value. The result equals the explicitly flag-first program (whose
    /// order needs no condition-first reading) and the migration recipe restores the old draw order.
    /// </summary>
    // A local that reads no parameter is cached for the whole run, so every draw-bearing local reads `x`.
    [Fact]
    public async Task SeededRandom_DrawsFollowTheFlagFirstOrder()
    {
        const string plain = "W(x) = x + randomInt(1, 9), randomInt(1, 100) < 70\nW.while(0)";
        const string flagFirst = "W(x) = {\n  C = randomInt(1, 100) + 0 * x < 70\n  if(C, x + randomInt(1, 9), x), C\n}\nW.while(0)";
        const string oldOrder = "W(x) = {\n  Nx = x + randomInt(1, 9)\n  Nx, (Nx == Nx) and randomInt(1, 100) < 70\n}\nW.while(0)";
        const string oldOrderEmulation = "W(x) = {\n  Nx = x + randomInt(1, 9)\n  C = randomInt(1, 100) + 0 * x < 70\n  Nx, (Nx == Nx) and C\n}\nW.while(0)";
        var (plainResult, _) = await AllRoutesAsync(plain, seed: 7);
        var (flagFirstResult, _) = await AllRoutesAsync(flagFirst, seed: 7);
        var (oldOrderResult, _) = await AllRoutesAsync(oldOrder, seed: 7);
        var (emulated, _) = await AllRoutesAsync(oldOrderEmulation, seed: 7);
        Assert.Equal(flagFirstResult.Outcome, plainResult.Outcome);
        Assert.Equal(emulated.Outcome, oldOrderResult.Outcome);
        // Research LOOP-CF1 § E case 17b/17d (seed 7): 7 under the retired step-first order, 4 now.
        Assert.Equal("ok 4", plainResult.Outcome);
        Assert.Equal("ok 7", oldOrderResult.Outcome);
    }

    // ── Cancellation in either row ───────────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("S(x) = mark(x - 1), cancel(x > 1)\nS.while(3)", "cancel(true)")]
    [InlineData("S(x) = cancel(x - 1), mark(x > 1)\nS.while(3)", "mark(true),cancel(2)")]
    [InlineData("S(x) = mark(x - 1), cancel(x > 3)\nS.while(3)", "cancel(false)")]
    public async Task HostCancellation_InEitherRow_IsObservedAtTheNextCheckpoint(string source, string hostLog)
    {
        var (oracle, _) = await AllRoutesAsync(source);
        Assert.Equal("cancelled", oracle.Kind);
        Assert.Equal(hostLog, string.Join(",", oracle.HostCalls));
    }

    [Fact]
    public async Task PreCancelledRun_ChargesNothingBeyondTheFirstCheckpoint()
    {
        foreach (var route in SixRouteAgreement.Routes)
        {
            var (observation, _) = await ObserveAsync(route, "S(x) = mark(x - 1), mark(x > 1)\nS.while(3)", seed: null,
                limits: null, preCancel: true);
            Assert.True(observation.Kind == "cancelled", $"{route}: {observation}");
            Assert.Empty(observation.HostCalls);
        }
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public async Task CancellationWhileARowIsSuspended_DoesNotResumeTheRound(bool inFlag)
    {
        // The host completes normally AFTER cancellation. Both async entry points must observe
        // the token before any remaining row, final materialization, or next round can run.
        foreach (var engine in new[] { true, false })
        {
            using var cancellation = new CancellationTokenSource();
            var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
            var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
            var calls = new List<string>();
            var operations = HostOperations.Create(
                HostOperation.CreateAsync("hold", async (args, _) =>
                {
                    calls.Add("hold");
                    entered.TrySetResult();
                    await release.Task;
                    return args[0];
                }, "x"),
                HostOperation.Create("mark", (args, _) =>
                {
                    calls.Add($"mark({SixRouteAgreement.Neutral(args[0])})");
                    return args[0];
                }, "x"));
            var source = inFlag
                ? "S(x) = mark(x - 1), hold(x > 1)\nS.while(3)"
                : "S(x) = hold(x - 1), mark(x > 1)\nS.while(3)";
            var options = new RunOptions { HostOperations = operations, EvaluationCancellationToken = cancellation.Token };
            var parsed = Parser.Parse(source, options);
            Assert.False(parsed.HasErrors);

            async Task Run()
            {
                if (engine)
                    await KatLangEngine.RunAsync(source, options);
                else
                    await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root),
                        hostOperations: operations, cancellationToken: cancellation.Token);
            }

            var pending = Run();
            try
            {
                await entered.Task.WaitAsync(WaitLimit);
                Assert.False(pending.IsCompleted);
                Assert.Equal(inFlag ? "hold" : "mark(true),hold", string.Join(",", calls));
                cancellation.Cancel();
                release.TrySetResult();
                var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(
                    () => pending.WaitAsync(WaitLimit));
                Assert.Equal(cancellation.Token, error.CancellationToken);
                Assert.True(pending.IsCanceled);
                Assert.Equal(inFlag ? "hold" : "mark(true),hold", string.Join(",", calls));
            }
            finally
            {
                cancellation.Cancel();
                release.TrySetResult();
                try { await pending.WaitAsync(WaitLimit); }
                catch (OperationCanceledException) { }
            }
        }
    }

    // ── Step budgets: every strategy agrees under the new order at every reached limit ─────────────

    public static TheoryData<string> SweepSources() => new()
    {
        "Step(x) = 10 / (x - 1), x > 1\nStep.while(1)",
        "Count(x) = mark(x - 1), x > 1\nCount.while(4)",
        "S(x) = {\n  D = mark(x - 1)\n  D, D > 0\n}\nS.while(3)",
        EmptyMark + "S(x) = mark(x + 1), mark(x < 2), E(2)*, E(3)*\nS.while(1)",
        "Fib(a, b, n) = b, a + b, n - 1, n > 1\nFib.while(0, 1, 6)",
        "S(x) = 1 / 0, mark(false)\nS.while(1)",
        "Spin(x) = x + 1, true\nS(x) = Spin.while(x), mark(false)\nS.while(1)",
        "W(x) = if(x == 2, (), x + 1)\nS(x) = W(x)*, mark(x != true)\nS.while(1)",
        "S(x) = \"{x}ab\", x == ''\nS.while('')",
        Capture + "S(r, k) = {\n  V = r.Invoke()\n  r, k + V, k < 14\n}\nS.while(R, 0)[1]",
    };

    [Theory]
    [MemberData(nameof(SweepSources))]
    public async Task StepLimitSweep_AgreesOnEveryRoute(string source)
    {
        for (var maxSteps = 1L; maxSteps <= 24; maxSteps++)
            await AllRoutesAsync(source, limits: new EvaluationLimits { MaxSteps = maxSteps });

        // Include the actual completion edge even when a program needs more than 24 steps.
        var (complete, budget) = await AllRoutesAsync(source);
        Assert.StartsWith("ok ", complete.Outcome);
        if (budget.Steps > 1) // MaxSteps has no zero setting; a one-step run has no lower legal edge.
        {
            var (shortRun, _) = await AllRoutesAsync(source, limits: new EvaluationLimits { MaxSteps = budget.Steps - 1 });
            Assert.Equal("err EvaluationStepLimitExceeded", shortRun.Outcome);
        }
        foreach (var maxSteps in new[] { budget.Steps, budget.Steps + 1 })
        {
            var (atEdge, _) = await AllRoutesAsync(source, limits: new EvaluationLimits { MaxSteps = maxSteps });
            Assert.Equal(complete, atEdge);
        }
    }

    [Theory]
    [InlineData("S(k, v) = mark(k + 1), [k, k], mark(k < 1)\nS.while(0, ())[1]", false)]
    [InlineData("S(k, s) = k + 1, mark(\"{s}ab\"), mark(k < 2)\nS.while(0, '')[1]", true)]
    public async Task MaterializationEdges_AgreeOnEveryRoute(string source, bool strings)
    {
        var (complete, budget) = await AllRoutesAsync(source);
        Assert.StartsWith("ok ", complete.Outcome);
        var used = strings ? budget.MaterializedStringChars : budget.MaterializedItems;
        Assert.True(used > 0);
        foreach (var allowed in new[] { used - 1, used, used + 1 })
        {
            var limits = strings
                ? new EvaluationLimits { MaxMaterializedStringChars = allowed }
                : new EvaluationLimits { MaxMaterializedItems = allowed };
            var (atEdge, _) = await AllRoutesAsync(source, limits: limits);
            if (allowed < used)
                Assert.Equal(strings ? "err StringMaterializationLimitExceeded" : "err MaterializationLimitExceeded", atEdge.Outcome);
            else
                Assert.Equal(complete, atEdge);
        }
        // Also reach each per-value ceiling; the stopping round must not construct another value.
        foreach (var allowed in strings ? new[] { 3, 4 } : new[] { 1, 2 })
        {
            var limits = strings
                ? new EvaluationLimits { MaxStringLength = allowed }
                : new EvaluationLimits { MaxCollectionItems = allowed };
            var (atEdge, _) = await AllRoutesAsync(source, limits: limits);
            if (allowed == (strings ? 3 : 1))
                Assert.Equal(strings ? "err StringSizeLimitExceeded" : "err CollectionSizeLimitExceeded", atEdge.Outcome);
            else
                Assert.Equal(complete, atEdge);
        }
    }

    [Fact]
    public async Task SkippedTransition_SavesItsStepsAndCheckpoints()
    {
        // The stopping round forms only the flag row: the loop with a costly transition row and the
        // loop whose transition row is a plain parameter read charge the same.
        var (_, costly) = await AllRoutesAsync("S(x) = x * x * x * x * x * x, x > 1\nS.while(1)");
        var (_, plain) = await AllRoutesAsync("S(x) = x, x > 1\nS.while(1)");
        Assert.Equal(plain, costly);
    }

    // ── Strategy: plain steps are planned, spread-tailed steps fail closed into the generic reader ──

    [Fact]
    public void PlainStep_IsPlanned_AndReadsItsFlagFirst()
    {
        var run = ObserveOptimized("Step(x) = 10 / (x - 1), x > 1\nStep.while(1)");
        Assert.Equal("1", run.Value);
        Assert.Equal(1, run.Loops!.OptimizedLoopHits);
        Assert.Equal(1, run.Loops.LoopIterations);
    }

    [Fact]
    public void SpreadTailedStep_FallsBackWithAReason_AndAgreesWithGeneric()
    {
        // The shape is otherwise plannable (one state slot, two rows); only the spread last row refuses it.
        const string source = "Flag(n) = n > 1\nStep(n) = n - 1, Flag(n)*\nStep.while(3)";
        var optimized = ObserveOptimized(source);
        Assert.Equal("1", optimized.Value);
        Assert.Equal(0, optimized.Loops!.OptimizedLoopHits);
        Assert.Contains(optimized.Loops.LoopPlans, plan => plan.FallbackReason == "loop plan spread continuation row");
    }

    [Fact]
    public void ZeroEmissionHandover_MaterializesOnce_AfterTheTrueVerdict()
    {
        const string source = "W(x) = if(x == 2, (), x + 1)\nS(x) = W(x)*, mark(x != true)\nS.while(1)";
        var optimized = ObserveOptimized(source);
        Assert.Equal("true", optimized.Value);
        Assert.Equal(1, optimized.Loops!.OptimizedLoopHits);
        Assert.True(optimized.Loops.FallbackReasons.ContainsKey("loop expression did not emit exactly one state value"));
        Assert.Equal("mark(true),mark(true),mark(false)", string.Join(",", optimized.HostCalls));
    }

    [Theory]
    [InlineData("true")]
    [InlineData("false")]
    [InlineData("invalid")]
    public void MultiItemContinuation_FromTheCountedCellSeam_MatchesGeneric(string verdict)
    {
        // An ordinary non-spread row is a value boundary. Exercise the planner's defensive
        // multi-emission branch with a synthetic counted cell, not invented surface syntax.
        (EvalResult<Evaluator.CountedResult> Result, Budget Budget, string Calls, LoopOptimizationDiagnosticsSnapshot Loops)
            Observe(bool optimized)
        {
            var calls = new List<string>();
            NeedCell Cell(string name, Evaluator.CountedResult value)
            {
                EvalResult<Evaluator.CountedResult> Read()
                {
                    calls.Add(name);
                    return EvalResult<Evaluator.CountedResult>.Ok(value);
                }
                return new NeedCell(Read, () => ValueTask.FromResult(Read()));
            }
            Result flag = verdict == "invalid" ? new Result.Atom(7) : new Result.Bool(verdict == "true");
            var continuation = Cell("flag", new(new Result.SequenceValue([new Result.Atom(5), flag]), 2));
            var transition = Cell("transition", new(new Result.Atom(9), 1));
            var loops = new LoopOptimizationDiagnostics();
            var ctx = (Evaluator.EvalCtx.Empty with { EnableLoopOptimization = optimized, LoopDiagnostics = loops })
                .WithNeedEnv([("flag", continuation), ("transition", transition)]);
            var step = new Algorithm.User(null, [new CaptureParameterPattern("x")], [], [],
                [new Expr.Param("transition"), new Expr.Param("flag")]);
            var program = new Expr.Call(new Expr.AlgorithmExpr(new Algorithm.Builtin(BuiltinId.@while)),
                [new Expr.AlgorithmExpr(step), new Expr.Num(0)]);
            var result = Evaluator.EvalCounted(program, ctx, Array.Empty<(string, Result)>());
            var budget = ctx.Budget;
            return (result, new(budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth,
                budget.MaterializedItems, budget.MaterializedStringChars), string.Join(",", calls), loops.GetSnapshot());
        }

        var generic = Observe(optimized: false);
        var planned = Observe(optimized: true);
        Assert.Equal(generic.Budget, planned.Budget);
        Assert.Equal(generic.Calls, planned.Calls);
        Assert.Equal(verdict == "true" ? "flag,transition" : "flag", planned.Calls);
        Assert.Equal(1, planned.Loops.OptimizedLoopHits);
        Assert.Equal(generic.Result.IsError, planned.Result.IsError);
        if (verdict == "false")
            Assert.Equal("0", SixRouteAgreement.Neutral(planned.Result.Value.Value));
        else
        {
            Assert.Equal(generic.Result.Error.ToString(), planned.Result.Error.ToString());
            Assert.Equal(verdict == "true" ? typeof(EvalError.ArityMismatch) : typeof(EvalError.TypeMismatch),
                Innermost(planned.Result.Error).GetType());
        }
        Assert.Equal(verdict == "true", planned.Loops.FallbackReasons.ContainsKey("loop continuation did not emit exactly one value"));
    }

    // ── Flag diagnostics: a rejected flag is positioned at the written row that supplied it ─────────

    /// <summary>
    /// source, expected span of the flag-supplying row (start line/column, exclusive end), expected
    /// host log. The span is the ROW's: a call or spread row's items carry no provenance of their own,
    /// so no interior expression is blamed (C, D), and discovery passes over trailing empty spreads (E).
    /// </summary>
    public static TheoryData<string, int, int, int, int, string> FlagRowSpans() => new()
    {
        // A. A literal flag row.
        { "Step(x) = x + 1, 42\nStep.while(0)", 1, 18, 1, 20, "" },
        // B. A calculated flag row.
        { "Step(x) = x + 1, x + 2\nStep.while(0)", 1, 18, 1, 23, "" },
        // C. Through an ordinary call: the call row, not the callee's interior `x + 2`.
        { "GetFlag(x) = x + 2\n\nStep(x) = x + 1, GetFlag(x)\nStep.while(0)", 3, 18, 3, 28, "" },
        // D. A spread row supplies the flag (its last item): the whole spread row.
        { "P(x) = (x + 1, 7)\nStep(x) = P(x)*\nStep.while(0)", 2, 11, 2, 16, "" },
        // E. Trailing empty spreads are formed, right to left, and passed over.
        { "Tail(n) = ()\nStep(n) = n + 1, n + 5, Tail(n)*\nStep.while(0)", 2, 18, 2, 23, "" },
        { "Tail(n) = ()\nP(n) = n + 1, 7\nStep(n) = P(n)*, Tail(n)*\nStep.while(0)", 3, 11, 3, 16, "" },
        { EmptyMark + "S(x) = mark(x + 1), mark(7), E(2)*, E(3)*\nS.while(1)", 2, 21, 2, 28, "mark(3),mark(2),mark(7)" },
        // One row is both the state and the flag; a parenthesized row keeps its group extent.
        { "Step(x) = 42\nStep.while(0)", 1, 11, 1, 13, "" },
        { "Step(x) = x + 1, (42)\nStep.while(0)", 1, 18, 1, 22, "" },
        // Rejected in a later round, after accepted ones; a planned `if` row.
        { "Step(x) = x + 1, if(x < 2, true, 5)\nStep.while(0)", 1, 18, 1, 36, "" },
        // A block step and a family-selected clause body.
        { "{ x + 1, 42 }.while(0)", 1, 10, 1, 12, "" },
        { "F(0) = 1, false\nF(n) = n - 1, 9\nF.while(2)", 2, 15, 2, 16, "" },
    };

    [Theory]
    [MemberData(nameof(FlagRowSpans))]
    public async Task NonBooleanFlag_IsPositionedAtTheFlagRow_OnEveryRoute(
        string source, int startLine, int startColumn, int endLine, int endColumn, string hostLog)
    {
        // Six-route agreement covers the span too (Describe renders it), so generic, planned, sync,
        // async and forced-async report the same location.
        var (observation, _) = await AllRoutesAsync(source);
        Assert.Equal("err TypeMismatch", observation.Outcome);
        Assert.Equal(hostLog, string.Join(",", observation.HostCalls));

        var expected = new SourceSpan(startLine, startColumn, endLine, endColumn);
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source, new RunOptions
        {
            HostOperations = Operations(new HostLog(), suspending: false),
        })).Errors);
        Assert.Equal(KatLangErrorCode.TypeMismatch, error.Code);
        Assert.Equal(expected, error.Span);
        Assert.Contains("while continuation flag (the step's last output) must be a Boolean value", error.Message, StringComparison.Ordinal);
        // The rule's own error carries the position; no extra context frame was added for it.
        var innermost = Assert.IsType<EvalError.TypeMismatch>(Innermost(Assert.IsAssignableFrom<EvalError>(error.Source)));
        Assert.Equal(expected, innermost.Span);
    }

    [Fact]
    public void NonBooleanFlag_PlannedLoop_ReportsTheRowSpanWithoutHandover()
    {
        foreach (var source in new[] { "Step(x) = x + 1, 42\nStep.while(0)", "Step(x) = x + 1, if(x < 2, true, 5)\nStep.while(0)" })
        {
            var run = ObserveOptimized(source);
            Assert.Equal("err TypeMismatch", run.Value);
            Assert.Equal(1, run.Loops!.OptimizedLoopHits);
            Assert.Equal(0, run.Loops.OptimizedLoopFallbacks);
        }
    }

    [Fact]
    public void FlagRowErrors_AndAtomicBuiltinSteps_KeepTheirExistingPositions()
    {
        static KatLangError Failure(string source)
            => Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)).Errors);

        // A failure while FORMING the flag row is that row's own error, positioned as before.
        var condition = Failure("Step(x) = x + 1, if(1, true, false)\nStep.while(0)");
        Assert.Equal(KatLangErrorCode.TypeMismatch, condition.Code);
        Assert.Contains("if condition must be a Boolean value", condition.Message, StringComparison.Ordinal);
        Assert.Equal(new SourceSpan(1, 18, 1, 36), condition.Span);
        var division = Failure("Step(x) = x + 1, 1 / x > 0\nStep.while(0)");
        Assert.Equal(KatLangErrorCode.DivisionByZero, division.Code);
        Assert.Equal(new SourceSpan(1, 18, 1, 23), division.Span);

        // An atomic builtin step has no written row: the flag error stays unpositioned and the
        // enclosing call's span is the report's.
        var builtin = Failure("while(count, [1, 2])");
        Assert.Equal(KatLangErrorCode.TypeMismatch, builtin.Code);
        Assert.Equal(new SourceSpan(1, 1, 1, 21), builtin.Span);
        Assert.Null(Innermost(Assert.IsAssignableFrom<EvalError>(builtin.Source)).Span);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public async Task HostBuiltFlagRow_UsesHostSpanOrEnclosingCallFallback(bool withSpan, bool withCallSpan)
    {
        // The flag row's host-provided span wins. Without it the existing attach-if-missing
        // law may use the enclosing call's span; no position is fabricated when both are absent.
        var hostSpan = new SourceSpan(7, 3, 7, 5);
        SourceSpan? callSpan = withCallSpan ? new SourceSpan(9, 1, 9, 15) : null;
        Expr flag = withSpan ? new Expr.Num(42) { Span = hostSpan } : new Expr.Num(42);
        var program = HostBuiltWhile(flag, callSpan);
        SourceSpan? rowSpan = withSpan ? hostSpan : null;
        SourceSpan? expected = rowSpan ?? callSpan;

        foreach (var optimized in new[] { false, true })
        {
            var loops = new LoopOptimizationDiagnostics();
            var (result, _) = Evaluator.RunCountedObserved(program, enableOptimizations: optimized, loopDiagnostics: loops);
            Assert.True(result.IsError);
            Assert.IsType<EvalError.TypeMismatch>(Innermost(result.Error));
            Assert.Equal(expected, KatLangError.FromEvalError(result.Error).Span);
            Assert.Equal(rowSpan, Innermost(result.Error).Span);
            Assert.Equal(optimized ? 1 : 0, loops.GetSnapshot().OptimizedLoopHits);
        }

        var sync = Evaluator.Run(program);
        var async = await Evaluator.RunAsync(program);
        var forced = await Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache());
        Assert.Equal(expected, KatLangError.FromEvalError(sync.Error).Span);
        Assert.Equal(expected, KatLangError.FromEvalError(async.Error).Span);
        Assert.Equal(expected, KatLangError.FromEvalError(forced.Result.Error).Span);
        Assert.Equal(rowSpan, Innermost(async.Error).Span);
        Assert.Equal(rowSpan, Innermost(forced.Result.Error).Span);
        Assert.Equal(sync.Error.ToString(), async.Error.ToString());
        Assert.Equal(sync.Error.ToString(), forced.Result.Error.ToString());
    }

    // ── L10: a host-built continuation row supplies at most one item, so it never reaches the ─────────
    // planned loop's defensive multi-item branch (MultiItemContinuation_FromTheCountedCellSeam_…)

    /// <summary>
    /// Representative public non-spread expression kinds, host-built where the parser cannot write them
    /// (<see cref="Expr.SequenceConstruct"/>, a capture of a lone spread, a value block). A row is a
    /// value boundary (Q-26): its counted emission is <see cref="Result.ValueCount"/>, so a two-item
    /// value is ONE item — the flag is the whole sequence, a TypeMismatch on both strategies.
    /// </summary>
    public static TheoryData<string> HostBuiltContinuationRows() =>
        new(HostBuiltContinuationCandidates().Select(static candidate => candidate.Name));

    private static IEnumerable<(string Name, Expr Row)> HostBuiltContinuationCandidates()
    {
        Expr Five() => new Expr.Num(5);
        Expr True() => new Expr.BoolLiteral(true);
        Expr P() => new Expr.Resolve("P");
        yield return ("sequence construct", new Expr.SequenceConstruct(Five(), True()));
        yield return ("sequence construct with a spread leaf", new Expr.SequenceConstruct(new Expr.SequenceSpread(P()), True()));
        yield return ("property", P());
        yield return ("member", new Expr.DotCall(new Expr.Resolve("O"), "P"));
        yield return ("call", new Expr.Call(new Expr.Resolve("G"), new OutputBundle([new Expr.Param("x")])));
        yield return ("call of a spread argument", new Expr.Call(new Expr.Resolve("Id"), new OutputBundle([new Expr.SequenceSpread(P())])));
        yield return ("value block", new Expr.AlgorithmExpr(HostAlgorithm([], [], Five(), True())));
        yield return ("capture", new Expr.Capture(new OutputBundle([Five(), True()])));
        yield return ("capture of a lone spread", new Expr.Capture(new OutputBundle([new Expr.SequenceSpread(P())])));
        yield return ("selection", new Expr.Index(P(), new OutputBundle([new Expr.Num(0), new Expr.Num(1)])));
        yield return ("if", new Expr.Call(new Expr.AlgorithmExpr(new Algorithm.Builtin(BuiltinId.@if)), new OutputBundle([True(), P(), P()])));
    }

    [Theory]
    [MemberData(nameof(HostBuiltContinuationRows))]
    public void HostBuiltContinuationRow_IsOneItem_SoThePlannedLoopNeverTakesTheMultiItemBranch(string name)
    {
        var row = HostBuiltContinuationCandidates().Single(candidate => candidate.Name == name).Row;
        var program = HostBuiltWhile(row);
        var generic = Evaluator.RunCountedObserved(program, enableOptimizations: false).Result;
        var loops = new LoopOptimizationDiagnostics();
        var observations = new EvaluationObservations();
        var planned = Evaluator.RunCountedObserved(program, enableOptimizations: true, loopDiagnostics: loops, observations: observations).Result;

        Assert.Equal(generic.Error.ToString(), planned.Error.ToString());
        var mismatch = Assert.IsType<EvalError.TypeMismatch>(Innermost(planned.Error));
        Assert.Contains("must be a Boolean value (true or false), but was a sequence value with", mismatch.Message, StringComparison.Ordinal);
        // The loop WAS planned (the row is a generic fallback node inside the plan), and its
        // continuation supplied one item: no multi-item fallback, no handover materialization.
        var snapshot = loops.GetSnapshot();
        Assert.Equal(1, snapshot.OptimizedLoopHits);
        Assert.False(snapshot.FallbackReasons.ContainsKey("loop continuation did not emit exactly one value"));
        Assert.Equal(0, snapshot.OptimizedLoopFallbacks);
        Assert.Equal(0, observations.OptimizedLoopHandoverMaterializationCount);
        // Unpositioned host-built nodes give an unpositioned report.
        Assert.Null(KatLangError.FromEvalError(planned.Error).Span);
    }

    [Fact]
    public void HostBuiltContinuationRow_ThatSuppliesOneBoolean_RunsPlannedWithoutHandover()
    {
        // The reachable host-built shape: a join whose `()` leaf contributes nothing is the one
        // Boolean item, read by the planned loop's ordinary one-item path in every round.
        var row = new Expr.SequenceConstruct(new Expr.EmptySequence(0),
            new Expr.Comparison(new Expr.Param("x"), [new ComparisonLink(ComparisonOp.Lt, new Expr.Num(3))]));
        var program = HostBuiltWhile(row);
        var generic = Evaluator.RunCountedObserved(program, enableOptimizations: false);
        var loops = new LoopOptimizationDiagnostics();
        var observations = new EvaluationObservations();
        var planned = Evaluator.RunCountedObserved(program, enableOptimizations: true, loopDiagnostics: loops, observations: observations);

        Assert.Equal("3", SixRouteAgreement.Neutral(generic.Result.Value.Value));
        Assert.Equal("3", SixRouteAgreement.Neutral(planned.Result.Value.Value));
        Assert.Equal(generic.Budget.ConsumedSteps, planned.Budget.ConsumedSteps);
        Assert.Equal(1, loops.GetSnapshot().OptimizedLoopHits);
        Assert.Equal(0, loops.GetSnapshot().OptimizedLoopFallbacks);
        Assert.Equal(0, observations.OptimizedLoopHandoverMaterializationCount);
    }

    [Fact]
    public void HostBuiltSpreadContinuationRow_IsTheOnlyMultiItemFlagRow_AndIsNeverPlanned()
    {
        // The boundary itself: only a spread row supplies several items, and the planner refuses a
        // spread continuation row (fail closed), so the generic reader is what reads its last item.
        var program = HostBuiltWhile(new Expr.SequenceSpread(new Expr.Resolve("P")));
        var generic = Evaluator.RunCountedObserved(program, enableOptimizations: false).Result;
        var loops = new LoopOptimizationDiagnostics();
        var planned = Evaluator.RunCountedObserved(program, enableOptimizations: true, loopDiagnostics: loops).Result;

        // `x + 1, 5, true`: the flag is `true`, the next state `(x + 1, 5)` no longer fits `Step(x)`.
        Assert.Equal(generic.Error.ToString(), planned.Error.ToString());
        Assert.IsType<EvalError.ArityMismatch>(Innermost(planned.Error));
        var snapshot = loops.GetSnapshot();
        Assert.Equal(0, snapshot.OptimizedLoopHits);
        Assert.Contains(snapshot.LoopPlans, static plan => plan.FallbackReason == "loop plan spread continuation row");
    }

    /// <summary>
    /// <c>while(Step, 0)</c> over a host-built root built with the public constructors only, where
    /// <c>Step(x) = x + 1, ROW</c> and the root declares <c>P = 5, true</c>, <c>O = { P = 5, true }</c>,
    /// <c>G(y) = 5, true</c> and <c>Id(a, b) = a, b</c>. No node carries a span unless the caller set one.
    /// </summary>
    private static Expr HostBuiltWhile(Expr continuationRow, SourceSpan? loopCallSpan = null)
    {
        Algorithm.User FiveTrue() => HostAlgorithm([], [], new Expr.Num(5), new Expr.BoolLiteral(true));
        var step = HostAlgorithm([new CaptureParameterPattern("x")], [],
            new Expr.Binary(BinaryOp.Add, new Expr.Param("x"), new Expr.Num(1)), continuationRow);
        var root = HostAlgorithm([],
            [
                new Property("P", FiveTrue()),
                new Property("O", HostAlgorithm([], [new Property("P", FiveTrue(), IsPublic: true)])),
                new Property("G", HostAlgorithm([new CaptureParameterPattern("y")], [], new Expr.Num(5), new Expr.BoolLiteral(true))),
                new Property("Id", HostAlgorithm([new CaptureParameterPattern("a"), new CaptureParameterPattern("b")], [],
                    new Expr.Param("a"), new Expr.Param("b"))),
                new Property("Step", step),
            ],
            new Expr.Call(new Expr.AlgorithmExpr(new Algorithm.Builtin(BuiltinId.@while)),
                new OutputBundle([new Expr.Resolve("Step"), new Expr.Num(0)])) { Span = loopCallSpan });
        return new Expr.AlgorithmExpr(root);
    }

    private static Algorithm.User HostAlgorithm(IReadOnlyList<ParameterPattern> parameters, IReadOnlyList<Property> properties, params Expr[] rows)
        => new(null, parameters, [], properties, new OutputBundle(rows));

    // ── Harness ──────────────────────────────────────────────────────────────────────────────────────

    internal sealed record Budget(long Steps, long Checkpoints, int PeakDepth, long MaterializedItems, long MaterializedStringChars);

    internal sealed record Observation(string Kind, string? Value, IReadOnlyList<string> Errors, IReadOnlyList<string> Causes, IReadOnlyList<string> HostCalls)
    {
        public string Outcome => Kind == "ok" ? $"ok {Value}" : $"{Kind} {string.Join(",", Causes)}";

        public bool Equals(Observation? other)
            => other is not null && Kind == other.Kind && Value == other.Value
                && Errors.SequenceEqual(other.Errors) && Causes.SequenceEqual(other.Causes) && HostCalls.SequenceEqual(other.HostCalls);

        public override int GetHashCode() => HashCode.Combine(Kind, Value);

        public override string ToString()
            => $"{Kind} {Value} errors=[{string.Join(" | ", Errors)}] host=[{string.Join(",", HostCalls)}]";
    }

    private sealed class HostLog
    {
        private int _pulses = -1;
        public List<string> Calls { get; } = [];
        public CancellationTokenSource Cancellation { get; } = new();

        private Result Log(string call, Result value)
        {
            lock (Calls)
                Calls.Add(call);
            return value;
        }

        public Result Mark(Result value) => Log($"{MarkName}({SixRouteAgreement.Neutral(value)})", value);

        public Result Pulse()
        {
            var pulse = Interlocked.Increment(ref _pulses);
            return Log($"pulse#{pulse}", new Result.Atom(pulse));
        }

        public Result Cancel(Result value)
        {
            Log($"cancel({SixRouteAgreement.Neutral(value)})", value);
            Cancellation.Cancel();
            return value;
        }
    }

    private static HostOperations Operations(HostLog log, bool suspending)
        => suspending
            ? HostOperations.Create(
                HostOperation.CreateAsync(MarkName, async (args, _) => { await Task.Yield(); return log.Mark(args[0]); }, "x"),
                HostOperation.CreateAsync("pulse", async (_, _) => { await Task.Yield(); return log.Pulse(); }),
                HostOperation.CreateAsync("cancel", async (args, _) => { await Task.Yield(); return log.Cancel(args[0]); }, "x"))
            : HostOperations.Create(
                HostOperation.Create(MarkName, (args, _) => log.Mark(args[0]), "x"),
                HostOperation.Create("pulse", (_, _) => log.Pulse()),
                HostOperation.Create("cancel", (args, _) => log.Cancel(args[0]), "x"));

    private static async Task<(Observation Observation, Budget? Budget)> ObserveAsync(
        SixRouteAgreement.Route route, string source, long? seed, EvaluationLimits? limits, bool preCancel = false)
    {
        var log = new HostLog();
        if (preCancel)
            log.Cancellation.Cancel();
        var operations = Operations(log, route is SixRouteAgreement.Route.EngineAsyncTwin or SixRouteAgreement.Route.ForcedTwin);
        var options = new RunOptions
        {
            HostOperations = operations,
            RandomSeed = seed,
            EvaluationLimits = limits,
            EvaluationCancellationToken = log.Cancellation.Token,
        };
        try
        {
            switch (route)
            {
                case SixRouteAgreement.Route.EngineSync:
                    return (FromRunResult(KatLangEngine.Run(source, options), log), null);
                case SixRouteAgreement.Route.EngineAsync:
                case SixRouteAgreement.Route.EngineAsyncTwin:
                    return (FromRunResult(await KatLangEngine.RunAsync(source, options), log), null);
            }

            var parsed = Parser.Parse(source, options);
            if (parsed.HasErrors)
                return (new Observation("parse", null, [.. parsed.Diagnostics.Select(static d => d.Message)], [], [.. log.Calls]), null);

            var program = new Expr.AlgorithmExpr(parsed.Root);
            var (result, budget) = route switch
            {
                SixRouteAgreement.Route.Generic => Evaluator.RunCountedObserved(program, limits: limits, enableOptimizations: false,
                    hostOperations: operations, randomSeed: seed, cancellationToken: log.Cancellation.Token),
                SixRouteAgreement.Route.Optimized => Evaluator.RunCountedObserved(program, limits: limits, enableOptimizations: true,
                    hostOperations: operations, randomSeed: seed, cancellationToken: log.Cancellation.Token),
                SixRouteAgreement.Route.ForcedTwin => await Evaluator.RunCountedObservedAsync(program, limits: limits,
                    zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                    hostOperations: operations, randomSeed: seed, cancellationToken: log.Cancellation.Token),
                _ => throw new ArgumentOutOfRangeException(nameof(route), route, null),
            };
            var counters = new Budget(budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth,
                budget.MaterializedItems, budget.MaterializedStringChars);
            return result.IsError
                ? (FromError(KatLangError.FromEvalError(result.Error), log), counters)
                : (new Observation("ok", SixRouteAgreement.Neutral(result.Value.Value), [], [], [.. log.Calls]), counters);
        }
        catch (OperationCanceledException)
        {
            return (new Observation("cancelled", null, [], [], [.. log.Calls]), null);
        }
    }

    /// <summary>
    /// Runs <paramref name="source"/> on every route; requires every route to agree with the synchronous
    /// engine and the three evaluator routes to report identical budget counters (Q-09b).
    /// </summary>
    private static async Task<(Observation Observation, Budget Budget)> AllRoutesAsync(string source, long? seed = null, EvaluationLimits? limits = null)
    {
        var (oracle, _) = await ObserveAsync(SixRouteAgreement.Route.EngineSync, source, seed, limits);
        Assert.True(oracle.Kind != "parse", $"source must parse cleanly: {oracle}\nsource:\n{source}");
        Budget? counters = null;
        foreach (var route in SixRouteAgreement.Routes.Skip(1))
        {
            var (observation, budget) = await ObserveAsync(route, source, seed, limits);
            Assert.True(oracle.Equals(observation), $"{route}: expected {oracle}, got {observation}\nsource:\n{source}\nlimits: {limits?.MaxSteps}");
            if (budget is null)
                continue;
            if (counters is null)
                counters = budget;
            else
                Assert.True(counters == budget, $"{route}: budget {budget} differs from {counters}\nsource:\n{source}\nlimits: {limits?.MaxSteps}");
        }

        return (oracle, counters ?? new Budget(0, 0, 0, 0, 0));
    }

    private sealed record Run(string? Value, IReadOnlyList<string> HostCalls, LoopOptimizationDiagnosticsSnapshot? Loops);

    /// <summary>The optimized evaluator alone, with its loop diagnostics.</summary>
    private static Run ObserveOptimized(string source)
    {
        var log = new HostLog();
        var operations = Operations(log, suspending: false);
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        var loops = new LoopOptimizationDiagnostics();
        var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), enableOptimizations: true,
            loopDiagnostics: loops, hostOperations: operations);
        return new Run(result.IsOk ? SixRouteAgreement.Neutral(result.Value.Value) : "err " + result.Error.Code,
            [.. log.Calls], loops.GetSnapshot());
    }

    private static Observation FromRunResult(RunResult result, HostLog log) => result switch
    {
        RunResult.Success success => new("ok", SixRouteAgreement.Neutral(success.Value), [], [], [.. log.Calls]),
        RunResult.EvalFailure failure => new("err", null, [.. failure.Errors.Select(Describe)], [.. failure.Errors.Select(Cause)], [.. log.Calls]),
        RunResult.ParseFailure failure => new("parse", null, [.. failure.Errors.Select(Describe)], [.. failure.Errors.Select(Cause)], [.. log.Calls]),
        RunResult.NoProgramOutput none => new("none", null, [none.Diagnostic.Code.ToString()], [], [.. log.Calls]),
    };

    private static Observation FromError(KatLangError error, HostLog log)
        => new("err", null, [Describe(error)], [Cause(error)], [.. log.Calls]);

    private static string Describe(KatLangError error) => $"{error.Code}: {error.Message} @ {error.Span}";

    private static string Cause(KatLangError error)
        => error.Source is EvalError evalError ? Innermost(evalError).GetType().Name : "front-end";

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }
}
