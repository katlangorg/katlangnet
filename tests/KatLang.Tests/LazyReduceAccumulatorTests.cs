using System.Diagnostics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// <c>reduce</c> EVALUATES ITS ACCUMULATORS ON DEMAND (issue #203, November 2026; Lean first:
/// <c>EvalBody.evalReduceCounted</c> over <c>NeedSuspension.applied</c>, C# <c>Evaluator.ReduceFold</c>).
/// <c>reduce(collection, reducer, initial)</c> demands its collection whole, then — for a nonempty collection —
/// ONLY ITS LAST STEP: each step is the ordinary invocation <c>reducer(element, accumulator)</c> over its already
/// evaluated element and ONE deferred accumulator, whose demand runs the preceding step, or evaluates
/// <c>initial</c>. So <c>reduce([a, b], R, i)</c> is <c>R(b, R(a, i))</c> in value AND in the demand of its
/// accumulators: a reducer that ignores its accumulator skips every earlier step and the initial expression, a
/// demanded accumulator is evaluated once, and effects follow actual demand. An empty collection demands
/// <c>initial</c> once and never projects the reducer.
/// <para>Unless a test names its route, every program runs on the six established routes
/// (<see cref="SixRouteAgreement"/>: the synchronous and asynchronous engines, the engine's genuinely suspending
/// asynchronous twin, the generic and the optimized evaluator, and the forced twin), which must agree on the
/// value, every error (code, message, span) and the exact host-call log. Lean:
/// <c>CoreTests/CallbackResultBoundary.lean</c> § lazy accumulators; spec cases <c>reduce-accumulators-*</c>.</para>
/// </summary>
public sealed class LazyReduceAccumulatorTests
{
    // Every bounded wait in this file is a hang guard, never a latency claim.
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);

    // Every expectation below names its outcome (`ok VALUE` or `err CODE`), which a source the front end
    // rejects can never produce: such a source is observed as `parse` on every route.
    private static Task<SixRouteAgreement.Observation> RunAsync(string source)
        => SixRouteAgreement.OnEveryRouteAsync(source);

    private static void RequireCleanParse(string source, HostOperations operations) => ParseValidRoot(source, operations);

    // A source the front end accepts, parsed with the host operations its names resolve to.
    private static Algorithm.User ParseValidRoot(string source, HostOperations operations)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return parsed.Root;
    }

    private static string Outcome(SixRouteAgreement.Observation observation) => observation.Kind switch
    {
        "ok" => $"ok {observation.Value}",
        "err" => $"err {observation.Errors[0][..observation.Errors[0].IndexOf(':')]}",
        _ => observation.Kind,
    };

    // ── 1. The issue's regression table ───────────────────────────────────────────────────────────────

    /// <summary>source, expected outcome, expected host-call log.</summary>
    public static TheoryData<string, string, string> RegressionCases() => new()
    {
        // The initial expression and the earlier step stay unforced.
        { "Pick(item, acc) = item\nreduce([1, 2], Pick, 1 / 0)", "ok 2", "" },
        { "Pick(item, acc) = item\nreduce([1, 2], Pick, trace(7))", "ok 2", "" },
        // The earlier reducer body stays unforced.
        { "R(item, acc) = if(item == 1, 1 / 0, item)\nreduce([1, 2], R, 0)", "ok 2", "" },
        { "R(item, acc) = if(item == 1, trace(item), item)\nreduce([1, 2], R, 0)", "ok 2", "" },
        // A demanded initial value fails where it is demanded.
        { "Add(item, acc) = item + acc\nreduce([1, 2], Add, 1 / 0)", "err DivisionByZero", "" },
        // The left-fold association is preserved.
        { "Digits(item, acc) = acc * 10 + item\nreduce([1, 2, 3], Digits, 0)", "ok 123", "" },
        // An empty collection runs the initial expression once and never uses the reducer.
        { "Pick(item, acc) = item\nreduce([], Pick, trace(7))", "ok 7", "trace(7)" },
        { "Pick(item, acc) = item\nreduce([], Pick, 1 / 0)", "err DivisionByZero", "" },
        { "reduce([], trace(5), trace(7))", "ok 7", "trace(7)" },
        { "reduce((), 1 / 0, trace(7))", "ok 7", "trace(7)" },
        // The collection is demanded whole before any reducer step, and before the initial value.
        { "Pick(item, acc) = item\nreduce([1 / 0, 2], Pick, 0)", "err DivisionByZero", "" },
        { "Pick(item, acc) = item\nreduce([1 / 0, 2], Pick, trace(0))", "err DivisionByZero", "" },
        { "Pick(item, acc) = item\nreduce([trace(1), trace(2)], Pick, trace(0))", "ok 2", "trace(1),trace(2)" },
    };

    [Theory]
    [MemberData(nameof(RegressionCases))]
    public async Task Fold_DemandsOnlyWhatItsStepsDemand(string source, string expected, string hostCalls)
    {
        var observation = await RunAsync(source);
        Assert.Equal(expected, Outcome(observation));
        Assert.Equal(hostCalls, string.Join(",", observation.HostCalls));
    }

    // ── 2. Effects follow actual demand ───────────────────────────────────────────────────────────────

    [Fact]
    public async Task EffectOrder_TheLastStepDrawsFirst()
    {
        // The step for 2 runs first and draws 1, then demands its accumulator: the step for 1 draws 2.
        var hostCounter = await RunAsync("R(item, acc) = tock() * item + acc\nreduce([1, 2], R, 0)");
        Assert.Equal("ok 4", Outcome(hostCounter));
        Assert.Equal(["tock#1", "tock#2"], hostCounter.HostCalls);

        // The native counter of a fresh run gives the same value.
        var native = await RunAsync("R(item, acc) = tick() * item + acc\nreduce([1, 2], R, 0)");
        Assert.Equal("ok 4", Outcome(native));
    }

    [Fact]
    public async Task EffectOrder_IsThatOfTheNestedOrdinaryCalls()
    {
        const string reducer = "R(item, acc) = trace(item), acc\n";
        var fold = await RunAsync(reducer + "reduce([1, 2], R, trace(0))");
        var nested = await RunAsync(reducer + "R(2, R(1, trace(0)))");
        Assert.Equal(Outcome(nested), Outcome(fold));
        Assert.Equal(nested.HostCalls, fold.HostCalls);
        Assert.Equal(["trace(2)", "trace(1)", "trace(0)"], fold.HostCalls);
    }

    [Fact]
    public async Task AccumulatorReadTwice_RunsTheEarlierStepAndTheInitialComputationOnce()
    {
        // Each step reads the same accumulator twice. The trace shows the step for 2 starting first, then the
        // step for 1, then the initial computation: each exactly once.
        var observation = await RunAsync("R(item, acc) = trace(item) + acc + acc\nreduce([1, 2], R, trace(100))");
        Assert.Equal("ok 404", Outcome(observation));
        Assert.Equal(["trace(2)", "trace(1)", "trace(100)"], observation.HostCalls);

        // A fresh native counter confirms it: one draw for the start, one per step.
        var native = await RunAsync("R(item, acc) = tick() + acc + acc\nreduce([1, 2], R, tick())");
        Assert.Equal("ok 17", Outcome(native));
    }

    [Fact]
    public async Task ForwardedAccumulator_IsPassedWithoutEvaluatingIt()
    {
        const string definitions = "Ignore(x) = 0\nSecond(x, y) = y\n";
        // Forwarding the accumulator to a callee that ignores it evaluates nothing.
        var ignored = await RunAsync(definitions + "R(item, acc) = Ignore(acc) + item\nreduce([1, 2], R, trace(9))");
        Assert.Equal("ok 2", Outcome(ignored));
        Assert.Empty(ignored.HostCalls);

        // Forwarding it to a callee that reads it evaluates it once, however often the cell is forwarded.
        var read = await RunAsync(definitions + "R(item, acc) = Second(acc, acc) + Second(item, acc)\nreduce([1, 2], R, trace(9))");
        Assert.Equal("ok 36", Outcome(read));
        Assert.Equal(["trace(9)"], read.HostCalls);
    }

    // ── 3. Failures ───────────────────────────────────────────────────────────────────────────────────

    [Fact]
    public async Task DemandedEarlierStepFailure_KeepsItsErrorAndGainsOneStepFrame()
    {
        var observation = await RunAsync("R(item, acc) = if(item == 1, 1 / 0, item + acc)\nreduce([1, 2, 3], R, 0)");
        Assert.Equal("err DivisionByZero", Outcome(observation));
        var error = Assert.Single(observation.Errors);
        // One reduce step frame, however many accumulators the demand crossed.
        Assert.Equal(1, CountOccurrences(error, "while evaluating reduce step"));
        // The failing division keeps its own position inside the reducer.
        Assert.Contains("@ [1:30, 1:35)", error);
    }

    [Fact]
    public async Task DemandedInitialFailure_UsesTheInitialAccumulatorDiagnostic()
    {
        // A closed parameter list keeps `Inc` a run-time zero-argument demand (no formula lifting).
        const string definitions = "Add(item, acc) = Id(item) + acc\nId(x) = x\nInc(x) = x + 1\n";
        // A callable that requires arguments, written where the initial accumulator belongs: the dedicated
        // report, raised when a step demands the start.
        var demanded = await RunAsync(definitions + "Probe(u) = reduce([1, 2], Add, Inc)\nProbe(0)");
        Assert.Equal("err ArityMismatch", Outcome(demanded));
        Assert.Contains("initial accumulator", Assert.Single(demanded.Errors));

        // The same report for an empty collection, which demands the start itself.
        var empty = await RunAsync(definitions + "Probe(u) = reduce([], Add, Inc)\nProbe(0)");
        Assert.Equal("err ArityMismatch", Outcome(empty));
        Assert.Contains("initial accumulator", Assert.Single(empty.Errors));

        // A reducer that never demands the start never reports it.
        var skipped = await RunAsync("Pick(item, acc) = item\nInc(x) = x + 1\nProbe(u) = reduce([1, 2], Pick, Inc)\nProbe(0)");
        Assert.Equal("ok 2", Outcome(skipped));
    }

    [Fact]
    public async Task FailureOfAnEarlierElement_PrecedesEveryStep()
    {
        var observation = await RunAsync("R(item, acc) = trace(item)\nreduce([1, [2][5], 3], R, trace(0))");
        Assert.Equal("err BadIndex", Outcome(observation));
        Assert.Empty(observation.HostCalls);
    }

    // ── 4. One accumulator slot, with its ordinary value shape ────────────────────────────────────────

    /// <summary>source, expected outcome, expected host-call log.</summary>
    public static TheoryData<string, string, string> AccumulatorSlots() => new()
    {
        // An inspecting sequence pattern demands the slot through the ordinary binder.
        { "R(item, (a, b)) = (a + item, b + 1)\nreduce([4, 6], R, (0, 0))", "ok S[10, 2]", "" },
        { "R(item, (a, b)) = (item, b)\nreduce([1, 2], R, (trace(0), 0))", "ok S[2, 0]", "trace(0)" },
        { "R(item, (a, b)) = item\nreduce([1, 2], R, 1 / 0)", "err DivisionByZero", "" },
        { "R(item, [a, b]) = item\nreduce([1], R, (1, 2))", "err TypeMismatch", "" },
        { "R(item, (a, b)) = item\nreduce([1], R, (1, 2, 3))", "err ArityMismatch", "" },
        // Clause dispatch demands it: the literal head inspects the accumulator.
        { "R(item, 0) = item\nR(item, acc) = item + acc\nreduce([1, 2], R, trace(0))", "ok 3", "trace(0)" },
        { "R(0, acc) = 0\nR(item, acc) = item\nreduce([1, 2], R, trace(0))", "ok 2", "" },
        // A plain binder does not: only the body's read demands it.
        { "R(item, acc) = item\nreduce([1, 2], R, trace(0))", "ok 2", "" },
        // Empty, list and multirow accumulators occupy ONE slot and keep their ordinary value shape.
        { "Keep(item, acc) = acc\n[reduce([1, 2], Keep, ())]", "ok L[S[]]", "" },
        { "Keep(item, acc) = acc\nreduce([1, 2], Keep, [])", "ok L[]", "" },
        { "Keep(item, acc) = acc\nreduce([1, 2], Keep, (5, 6))", "ok S[5, 6]", "" },
        { "Two(item, acc) = item, acc\nreduce([1, 2], Two, 0)", "ok S[2, S[1, 0]]", "" },
        { "Coll(item, *rest) = rest\nreduce([1], Coll, (5, 6))", "ok L[S[5, 6]]", "" },
        { "Coll(item, *rest) = rest\nreduce([1], Coll, ())", "ok L[S[]]", "" },
        { "Cnt(item, acc) = count(acc)\nreduce([1, 2], Cnt, (5, 6, 7))", "ok 1", "" },
        { "Clear(item, acc) = ()\nLen(item, acc) = [acc].count\nreduce([1, 2], Len, ())", "ok 1", "" },
        // A strict builtin reducer demands the accumulator through its argument roles.
        // Math.Pow(3, Math.Pow(2, 2)).
        { "reduce([2, 3], Math.Pow, 2)", "ok 81", "" },
        { "reduce([2, 3], Math.Pow, 1 / 0)", "err DivisionByZero", "" },
        { "reduce([2, 3], Math.Pow, trace(2))", "ok 81", "trace(2)" },
        // An alias of a reducer is its target.
        { "Pick(item, acc) = item\nA = Pick\nreduce([1, 2], A, 1 / 0)", "ok 2", "" },
        // A reducer forwarded through a parameter is projected, never demanded.
        { "Pick(item, acc) = item\nFold(f, xs) = reduce(xs, f, 1 / 0)\nFold(Pick, [1, 2])", "ok 2", "" },
    };

    [Theory]
    [MemberData(nameof(AccumulatorSlots))]
    public async Task AccumulatorSlot_IsDemandedThroughTheOrdinaryBinderAndArgumentRoles(string source, string expected, string hostCalls)
    {
        var observation = await RunAsync(source);
        Assert.Equal(expected, Outcome(observation));
        Assert.Equal(hostCalls, string.Join(",", observation.HostCalls));
    }

    [Fact]
    public async Task HostReducer_DemandsTheAccumulatorAsAnOrdinaryArgument()
    {
        foreach (var suspending in new[] { false, true })
        {
            var calls = new List<string>();
            Result Join(IReadOnlyList<Result> args)
            {
                lock (calls) calls.Add($"join({SixRouteAgreement.Neutral(args[0])}, {SixRouteAgreement.Neutral(args[1])})");
                return new Result.ListValue([args[0], args[1]]);
            }

            var operation = suspending
                ? HostOperation.CreateAsync("join", async (args, _) => { await Task.Yield(); return Join(args); }, "item", "acc")
                : HostOperation.Create("join", (args, _) => Join(args), "item", "acc");
            var options = new RunOptions { HostOperations = HostOperations.Create(operation) };
            const string source = "reduce([1, 2], join, 0)";
            RequireCleanParse(source, options.HostOperations);
            var result = suspending ? await KatLangEngine.RunAsync(source, options) : KatLangEngine.Run(source, options);

            var success = Assert.IsType<RunResult.Success>(result);
            Assert.Equal("L[2, L[1, 0]]", SixRouteAgreement.Neutral(success.Value));
            // A host operation receives evaluated arguments, so the earlier step runs first.
            Assert.Equal(["join(1, 0)", "join(2, L[1, 0])"], calls);
        }
    }

    // ── 5. Synthetic accumulator slots are VALUE-only ─────────────────────────────────────────────────

    [Fact]
    public async Task InitialCallableIdentity_IsNotTransferredToTheReducer()
    {
        const string definitions = "Inc(x) = x + 1\nCall(item, acc) = acc(item)\n";
        // The ordinary call passes the callable itself.
        Assert.Equal("ok 2", Outcome(await RunAsync(definitions + "Call(1, Inc)")));
        // The fold's accumulator slot is a calculation value: it has no callable identity. (A closed
        // parameter list keeps `Inc` a run-time demand instead of a lifted formula input.)
        Assert.Equal("err NotAnAlgorithm", Outcome(await RunAsync(definitions + "Probe(u) = reduce([1], Call, Inc)\nProbe(0)")));
        // ... and neither has a completed step's result.
        Assert.Equal("err NotAnAlgorithm", Outcome(await RunAsync(
            definitions + "Later(item, acc) = if(item == 1, 5, acc(item))\nreduce([1, 2], Later, 0)")));
    }

    [Fact]
    public async Task InitialWrittenCallPlan_IsNotTransferredToTheReducer()
    {
        const string definitions = "F(x) = x + trace(x)\nCap(meta c) = c.Invoke()\n";
        // The ordinary call captures the written call it was supplied.
        var direct = await RunAsync(definitions + "R(item, acc) = Cap(acc)\nR(1, F(5))");
        Assert.Equal("ok 10", Outcome(direct));

        // The fold supplies a VALUE-only slot: a META parameter refuses it, and the original call never runs.
        var forwarded = await RunAsync(definitions + "R(item, acc) = Cap(acc)\nreduce([1], R, F(5))");
        Assert.Equal("err NotAnAlgorithm", Outcome(forwarded));
        Assert.Empty(forwarded.HostCalls);

        var declared = await RunAsync("F(x) = x + trace(x)\nR(item, meta acc) = acc.Invoke()\nreduce([1], R, F(5))");
        Assert.Equal("err NotAnAlgorithm", Outcome(declared));
        Assert.Empty(declared.HostCalls);

        // A step's accumulator is refused in the same way.
        var step = await RunAsync("R(item, meta acc) = item\nreduce([1, 2], R, 0)");
        Assert.Equal("err NotAnAlgorithm", Outcome(step));
    }

    [Fact]
    public async Task InitialRetainedSlice_IsNotTransferredToTheReducer()
    {
        const string definitions = "Cnt(item, acc) = count(acc)\n";
        // The ordinary call counts a retained collector by position, demanding no element.
        var direct = await RunAsync(definitions + "F(*xs) = Cnt(1, xs)\nF(trace(1), trace(2))");
        Assert.Equal("ok 2", Outcome(direct));
        Assert.Empty(direct.HostCalls);

        // The fold's slot is the collector's whole VALUE: one exact list, every element demanded.
        var folded = await RunAsync(definitions + "F(*xs) = reduce([1], Cnt, xs)\nF(trace(1), trace(2))");
        Assert.Equal("ok 2", Outcome(folded));
        Assert.Equal(["trace(1)", "trace(2)"], folded.HostCalls);
    }

    [Fact]
    public async Task WrittenSpread_IsFormedEvenWhenItsSlotIsIgnored()
    {
        // Supply formation evaluates an explicit spread; the slot it supplies is then never demanded.
        var observation = await RunAsync("Pick(item, acc) = item\nOne = [trace(9)]\nreduce([1, 2], Pick, One*)");
        Assert.Equal("ok 2", Outcome(observation));
        Assert.Equal(["trace(9)"], observation.HostCalls);

        // A failing spread fails the call, before the arity check and before any step.
        var failing = await RunAsync("Pick(item, acc) = trace(item)\nBad = 1 / 0\nreduce([1, 2], Pick, Bad*)");
        Assert.Equal("err DivisionByZero", Outcome(failing));
        Assert.Empty(failing.HostCalls);
    }

    // ── 6. One builtin dispatch for every spelling ────────────────────────────────────────────────────

    [Theory]
    [InlineData("reduce([1, 2], Pick, 1 / 0)")]
    [InlineData("[1, 2].reduce(Pick, 1 / 0)")]
    [InlineData("Fold = reduce\nFold([1, 2], Pick, 1 / 0)")]
    [InlineData("Fold = reduce\n[1, 2].Fold(Pick, 1 / 0)")]
    [InlineData("Fold(xs, f, i) = reduce(xs, f, i)\nFold([1, 2], Pick, 1 / 0)")]
    public async Task PlainDottedAndAliasedCalls_ShareTheLazyFold(string call)
    {
        Assert.Equal("ok 2", Outcome(await RunAsync("Pick(item, acc) = item\n" + call)));
    }

    [Theory]
    [InlineData("reduce([1, 2], T, 0)")]
    [InlineData("[1, 2].reduce(T, 0)")]
    [InlineData("Fold = reduce\nFold([1, 2], T, 0)")]
    public async Task PlainDottedAndAliasedCalls_ShareTheEffectOrder(string call)
    {
        var observation = await RunAsync("T(item, acc) = tock() * item + acc\n" + call);
        Assert.Equal("ok 4", Outcome(observation));
    }

    // ── 7. Long folds: continuations are not call depth, and skipped work never starts ────────────────

    private static (EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget) Observe(string source, bool optimized = true)
    {
        var parsed = SourceProvenance.ParseValid(source);
        return Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), enableOptimizations: optimized);
    }

    private static async Task<(EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget)> ObserveSuspendingAsync(
        string source, int waitingSteps)
    {
        var parsed = SourceProvenance.ParseValid(source);
        // Each program reads Seed at the deepest demanded step. Hold that read so the test
        // observes the real evaluator suspended with the predecessor chain still active.
        var cache = new HoldingAsyncZeroArgPropertyResultCache(holdAtAccess: 1);
        var run = Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root), zeroArgPropertyResultCache: cache).AsTask();
        try
        {
            Assert.Same(cache.Reached, await Task.WhenAny(cache.Reached, run));
            Assert.False(run.IsCompleted);
            Assert.Equal(waitingSteps, cache.ObservedBudget!.ActiveFoldContinuations);
        }
        finally
        {
            cache.Release();
        }
        return await run;
    }

    // A reducer that calls before it reads its accumulator: every step is suspended while the step
    // before it runs (the general route; `StreamedReduceFoldEquivalenceTests` covers the streamed one).
    private const string CallingAdd = "Id(x) = x\nAdd(item, acc) = Id(item) + acc\n";

    [Theory]
    [InlineData(2)]
    [InlineData(200)]
    [InlineData(3000)]
    public async Task AccumulatingFold_HoldsOneContinuationPerElement_AtTheDepthOfOneStep(int count)
    {
        var source = CallingAdd + $"Seed = 0\nreduce(range(1, {count}), Add, Seed)";
        var expected = (long)count * (count + 1) / 2;
        var (twoResult, twoBudget) = Observe(CallingAdd + "Seed = 0\nreduce(range(1, 2), Add, Seed)");
        Assert.True(twoResult.IsOk);

        foreach (var optimized in new[] { false, true })
        {
            var (result, budget) = Observe(source, optimized);
            Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
            Assert.Equal(expected.ToString(), SixRouteAgreement.Neutral(result.Value.Value));
            // Every step is suspended at once: one continuation per element, the start included.
            Assert.Equal(count, budget.PeakFoldContinuations);
            Assert.Equal(0, budget.ActiveFoldContinuations);
            // ... yet the dynamic depth is that of ONE step, whatever the length of the fold.
            Assert.Equal(twoBudget.PeakDepth, budget.PeakDepth);
            Assert.True(budget.PeakDepth < EvaluationLimits.MaxSupportedDepth);
            Assert.Equal(0, budget.CurrentDepth);
        }

        var (suspended, suspendedBudget) = await ObserveSuspendingAsync(source, count);
        Assert.True(suspended.IsOk, suspended.IsError ? suspended.Error.ToString() : null);
        Assert.Equal(expected.ToString(), SixRouteAgreement.Neutral(suspended.Value.Value));
        Assert.Equal(count, suspendedBudget.PeakFoldContinuations);
        Assert.Equal(twoBudget.PeakDepth, suspendedBudget.PeakDepth);
    }

    [Fact]
    public async Task SkippingFold_ChargesOnlyTheStepsItRuns()
    {
        // The step for 2990 ignores its accumulator: of 3000 steps only the last eleven run.
        const string skipping = "Seed = 0\nLast(item, acc) = if(item == 2990, Seed, item + acc)\nreduce(range(1, 3000), Last, 1 / 0)";
        const string accumulating = "Seed = 0\nLast(item, acc) = if(item == 0, Seed, item + acc)\nreduce(range(1, 3000), Last, Seed)";
        var expected = Enumerable.Range(2991, 10).Sum().ToString();

        var (skipped, skippedBudget) = Observe(skipping);
        var (all, allBudget) = Observe(accumulating);
        Assert.True(skipped.IsOk, skipped.IsError ? skipped.Error.ToString() : null);
        Assert.True(all.IsOk);
        Assert.Equal(expected, SixRouteAgreement.Neutral(skipped.Value.Value));
        // Ten suspended steps wait for the one that needs no accumulator.
        Assert.Equal(10, skippedBudget.PeakFoldContinuations);
        Assert.Equal(3000, allBudget.PeakFoldContinuations);
        // Executed callbacks are charged, skipped ones are not: 2989 steps and their work never start.
        Assert.True(allBudget.ConsumedSteps - skippedBudget.ConsumedSteps >= 2989,
            $"all {allBudget.ConsumedSteps}, skipping {skippedBudget.ConsumedSteps}");

        var (suspended, suspendedBudget) = await ObserveSuspendingAsync(skipping, 10);
        Assert.True(suspended.IsOk);
        Assert.Equal(expected, SixRouteAgreement.Neutral(suspended.Value.Value));
        Assert.Equal(skippedBudget.ConsumedSteps, suspendedBudget.ConsumedSteps);
        Assert.Equal(10, suspendedBudget.PeakFoldContinuations);
    }

    [Fact]
    public void GenuineRecursionInsideAReducer_StillReachesTheDepthLimit()
    {
        // The reducer calls itself without end: real call nesting, which fold continuations never hide.
        var (result, budget) = Observe("Deep(item, acc) = Deep(item, acc) + 1\nreduce(range(1, 50), Deep, 0)");
        Assert.True(result.IsError);
        Assert.True(Innermost(result.Error) is EvalError.EvaluationDepthExceeded or EvalError.EvaluationStackExhausted, result.Error.ToString());
        Assert.Equal(0, budget.CurrentDepth);
        Assert.Equal(0, budget.ActiveFoldContinuations);

        // A fold inside a reducer runs at its own depth: nesting folds is nesting calls.
        var (nested, nestedBudget) = Observe(
            CallingAdd + "Outer(item, acc) = reduce(range(1, item), Add, acc)\nreduce(range(1, 40), Outer, 0)");
        Assert.True(nested.IsOk, nested.IsError ? nested.Error.ToString() : null);
        Assert.Equal(Enumerable.Range(1, 40).Sum(static n => n * (n + 1) / 2).ToString(), SixRouteAgreement.Neutral(nested.Value.Value));
        Assert.Equal(0, nestedBudget.CurrentDepth);
    }

    [Fact]
    public void StepLimit_CountsExecutedStepsOnly()
    {
        const string source = "Pick(item, acc) = item\nreduce(range(1, 1000), Pick, 1 / 0)";
        var (unlimited, budget) = Observe(source);
        Assert.True(unlimited.IsOk);

        var parsed = SourceProvenance.ParseValid(source);
        var (exact, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), new EvaluationLimits { MaxSteps = budget.ConsumedSteps });
        Assert.True(exact.IsOk);
        // The fold needed far fewer steps than it has elements: one executed callback, not a thousand.
        Assert.True(budget.ConsumedSteps < 20, budget.ConsumedSteps.ToString());
    }

    // ── 8. Cancellation ───────────────────────────────────────────────────────────────────────────────

    [Theory]
    // The last step suspends first: no earlier step has started.
    [InlineData("R(item, acc) = pause(item) + acc\nreduce([1, 2, 3], R, 0)", 3)]
    // Every step demands its accumulator first: the step for 1 is the demanded step that suspends.
    [InlineData("R(item, acc) = acc + pause(item)\nreduce([1, 2, 3], R, 0)", 1)]
    public async Task CancellationDuringASuspendedStep_StartsNoFurtherStep(string source, int pausedItem)
    {
        using var cancellation = new CancellationTokenSource();
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var paused = new List<string>();
        var operations = HostOperations.Create(HostOperation.CreateAsync("pause", async (args, _) =>
        {
            lock (paused) paused.Add(SixRouteAgreement.Neutral(args[0]));
            reached.TrySetResult();
            await release.Task;
            return args[0];
        }, "x"));
        RequireCleanParse(source, operations);
        var task = KatLangEngine.RunAsync(source, new RunOptions { HostOperations = operations, EvaluationCancellationToken = cancellation.Token });
        try
        {
            await reached.Task.WaitAsync(WaitLimit);
            Assert.False(task.IsCompleted);
            cancellation.Cancel();
        }
        finally
        {
            release.TrySetResult();
        }

        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await task);
        Assert.Equal(cancellation.Token, thrown.CancellationToken);
        // Exactly one step reached its host call; the steps that waited behind it never started theirs.
        Assert.Equal([pausedItem.ToString()], paused);
    }

    [Fact]
    public void CancellationDuringASynchronousDemandedStep_EndsTheRunWithTheHostToken()
    {
        using var cancellation = new CancellationTokenSource();
        var stopped = new List<string>();
        var operations = HostOperations.Create(HostOperation.Create("stop", (args, _) =>
        {
            lock (stopped) stopped.Add(SixRouteAgreement.Neutral(args[0]));
            cancellation.Cancel();
            return args[0];
        }, "x"));
        const string source = "R(item, acc) = acc + stop(item)\nreduce([1, 2, 3], R, 0)";
        RequireCleanParse(source, operations);

        var thrown = Assert.ThrowsAny<OperationCanceledException>(
            () => KatLangEngine.Run(source, new RunOptions { HostOperations = operations, EvaluationCancellationToken = cancellation.Token }));
        Assert.Equal(cancellation.Token, thrown.CancellationToken);
        // The demanded step for 1 cancelled the run; the steps for 2 and 3 never reached their host call.
        Assert.Equal(["1"], stopped);
    }

    // ── 9. The synchronous route continues a long chain on a fresh stack ──────────────────────────────

    [Fact]
    public void LongAccumulatingFold_OnAOneMebibyteThread_CompletesOnFreshStacks()
    {
        const int count = 4000;
        var source = CallingAdd + $"reduce(range(1, {count}), Add, 0)";
        SourceProvenance.ParseValid(source);
        RunResult? result = null;
        Exception? failure = null;
        var startedBefore = FoldContinuationStack.Started;
        var thread = new Thread(() =>
        {
            try { result = KatLangEngine.Run(source); }
            catch (Exception error) { failure = error; }
        }, maxStackSize: 1024 * 1024);
        thread.Start();
        Assert.True(thread.Join(TimeSpan.FromMinutes(5)), "the fold did not finish");

        Assert.Null(failure);
        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal(((long)count * (count + 1) / 2).ToString(), SixRouteAgreement.Neutral(success.Value));
        // Four thousand suspended steps do not fit a 1 MiB stack: the chain continued elsewhere.
        Assert.True(FoldContinuationStack.Started > startedBefore);
    }

    [Fact]
    public void HostExceptionOnAFreshStack_ReachesTheCallerAsTheSameObject()
    {
        var thrown = new InvalidOperationException("host failure");
        var operations = HostOperations.Create(HostOperation.Create("fail", (_, _) => throw thrown));
        // The start is reached only after three thousand suspended steps, far beyond one thread's allowance.
        const string source = CallingAdd + "reduce(range(1, 3000), Add, fail())";
        RequireCleanParse(source, operations);

        var caught = Assert.Throws<InvalidOperationException>(
            () => KatLangEngine.Run(source, new RunOptions { HostOperations = operations }));
        Assert.Same(thrown, caught);
    }

    // ── 10. What a suspended step keeps alive, and where its callbacks run ───────────────────────────

    /// <summary>
    /// The asynchronous state machines on the host stack when the start of a general fold of <paramref name="count"/>
    /// steps is demanded — every step suspended — counted by the start itself, a host operation. The run stays on one
    /// 16 MiB thread: a short chain never continues elsewhere.
    /// </summary>
    private static int AsyncStateMachineFramesAtTheStart(int count)
    {
        var frames = -1;
        var probeThread = -1;
        var operations = HostOperations.Create(HostOperation.Create("probe", (_, _) =>
        {
            probeThread = Environment.CurrentManagedThreadId;
            frames = new StackTrace(false).GetFrames().Count(static frame =>
                frame.GetMethod()?.DeclaringType is { } type && typeof(IAsyncStateMachine).IsAssignableFrom(type));
            return new Result.Atom(0);
        }));
        var source = CallingAdd + $"reduce(range(1, {count}), Add, probe())";
        RequireCleanParse(source, operations);

        RunResult? result = null;
        Exception? failure = null;
        var runThread = -1;
        var thread = new Thread(() =>
        {
            runThread = Environment.CurrentManagedThreadId;
            try { result = KatLangEngine.Run(source, new RunOptions { HostOperations = operations }); }
            catch (Exception error) { failure = error; }
        }, maxStackSize: 16 * 1024 * 1024) { IsBackground = true };
        thread.Start();
        Assert.True(thread.Join(WaitLimit), "the fold did not finish");

        Assert.Null(failure);
        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal(((long)count * (count + 1) / 2).ToString(), SixRouteAgreement.Neutral(success.Value));
        Assert.Equal(runThread, probeThread);
        return frames;
    }

    [Fact]
    public void SuspendedSteps_KeepOnlyTheAccumulatorContextBoundary_OnTheSynchronousHostStack()
    {
        // One method builder restores each demander's ambient state. The step and callback dispatch add
        // no state machines of their own (formerly three machines in total per suspended step).
        Assert.InRange(AsyncStateMachineFramesAtTheStart(9) - AsyncStateMachineFramesAtTheStart(3), 0, 6);
    }

    private static int Item(Result value) => (int)((Result.Atom)value).Value;

    [Theory]
    [InlineData(false, Flow.Normal)]
    [InlineData(false, Flow.Suppressed)]
    [InlineData(true, Flow.Normal)]
    [InlineData(true, Flow.Suppressed)]
    public void SynchronousCallbacks_ResumeWithTheirOwnHostContext(bool streamed, Flow flow)
    {
        var ambient = new AsyncLocal<int>();
        var contexts = Enumerable.Range(0, 5).Select(_ => new SynchronizationContext()).ToArray();
        var caller = SynchronizationContext.Current;
        var entries = new List<int>();
        var observations = new List<(int Item, int Ambient, bool OwnContext, bool Suppressed)>();
        var operations = HostOperations.Create(
            HostOperation.Create("enter", (args, _) =>
            {
                var item = Item(args[0]);
                entries.Add(ambient.Value);
                ambient.Value = item;
                SynchronizationContext.SetSynchronizationContext(contexts[item]);
                return args[0];
            }, "x"),
            HostOperation.Create("observe", (args, _) =>
            {
                var item = Item(args[0]);
                observations.Add((item, ambient.Value, SynchronizationContext.Current == contexts[item], ExecutionContext.IsFlowSuppressed()));
                return new Result.Atom(0);
            }, "x"),
            HostOperation.Create("seed", (_, _) =>
            {
                ambient.Value = 99;
                SynchronizationContext.SetSynchronizationContext(contexts[0]);
                if (ExecutionContext.IsFlowSuppressed()) ExecutionContext.RestoreFlow();
                else ExecutionContext.SuppressFlow();
                return new Result.Atom(0);
            }));
        var body = streamed ? "acc + enter(item) + observe(item)" : "enter(item) + acc + observe(item)";
        var source = $"Add(item, acc) = {body}\nreduce(range(1, 4), Add, seed())";
        RequireCleanParse(source, operations);

        var run = HostFlow.Under(flow, () => KatLangEngine.Run(source, new RunOptions { HostOperations = operations }));
        Assert.Equal("10", SixRouteAgreement.Neutral(Assert.IsType<RunResult.Success>(run).Value));
        Assert.Equal(streamed ? new[] { 0, 0, 0, 0 } : new[] { 0, 4, 3, 2 }, entries);
        Assert.Equal(Enumerable.Range(1, 4).Select(i => (i, i, true, flow == Flow.Suppressed)), observations);
        Assert.Equal(0, ambient.Value);
        Assert.Same(caller, SynchronizationContext.Current);
    }

    /// <summary>
    /// A general fold of 4,000 steps on a 1 MiB thread, its reducer calling the host operation <c>mark</c> before
    /// its accumulator read (the descent: the last step's call first) or after it (the ascent: the first step's
    /// call first): every call runs one at a time, in that order, on the calling thread or on a fresh stack of
    /// the fold (<see cref="FoldContinuationStack"/>), never on the thread pool.
    /// </summary>
    [Theory]
    [InlineData("Add(item, acc) = mark(item) + acc", false)]
    [InlineData("Id(x) = x\nAdd(item, acc) = Id(item) + acc + 0 * mark(item)", true)]
    public void LongFoldCallbacks_RunInOrder_OnTheCallingThreadOrTheFoldsFreshStacks(string reducer, bool ascending)
    {
        const int count = 4000;
        var calls = new List<(int Item, int Thread, string? Name)>();
        var active = 0;
        var overlapped = false;
        var operations = HostOperations.Create(HostOperation.Create("mark", (args, _) =>
        {
            if (Interlocked.Increment(ref active) != 1) overlapped = true;
            lock (calls) calls.Add((Item(args[0]), Environment.CurrentManagedThreadId, Thread.CurrentThread.Name));
            Interlocked.Decrement(ref active);
            return args[0];
        }, "x"));
        var source = reducer + $"\nreduce(range(1, {count}), Add, 0)";
        RequireCleanParse(source, operations);

        RunResult? result = null;
        Exception? failure = null;
        var calling = -1;
        var thread = new Thread(() =>
        {
            calling = Environment.CurrentManagedThreadId;
            try { result = KatLangEngine.Run(source, new RunOptions { HostOperations = operations }); }
            catch (Exception error) { failure = error; }
        }, maxStackSize: 1024 * 1024);
        thread.Start();
        Assert.True(thread.Join(TimeSpan.FromMinutes(5)), "the fold did not finish");

        Assert.Null(failure);
        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal(((long)count * (count + 1) / 2).ToString(), SixRouteAgreement.Neutral(success.Value));
        Assert.False(overlapped, "two host calls overlapped");
        var expected = ascending ? Enumerable.Range(1, count) : Enumerable.Range(1, count).Reverse();
        Assert.Equal(expected, calls.Select(static call => call.Item));
        // The steps nearest the fold's own frame run on the calling thread; the chain beyond its allowance
        // continues on fresh stacks of the fold.
        Assert.Contains(calls, call => call.Thread == calling);
        Assert.Contains(calls, call => call.Thread != calling);
        Assert.All(calls, call => Assert.True(call.Thread == calling || call.Name == "KatLang fold continuation",
            $"mark({call.Item}) ran on thread {call.Thread} ({call.Name ?? "unnamed"})"));
    }

    /// <summary>
    /// The asynchronous twin keeps suspended steps on the heap: a long general fold whose reducer GENUINELY
    /// suspends in every step — before its accumulator read or after it — still makes its host calls one at a
    /// time and in the nested order.
    /// </summary>
    [Theory]
    [InlineData("Add(item, acc) = pause(item) + acc", false)]
    [InlineData("Id(x) = x\nAdd(item, acc) = Id(item) + acc + 0 * pause(item)", true)]
    public async Task LongFoldWithGenuinelySuspendingCallbacks_KeepsTheirOrder(string reducer, bool ascending)
    {
        const int count = 3000;
        var calls = new List<int>();
        var active = 0;
        var overlapped = false;
        var operations = HostOperations.Create(HostOperation.CreateAsync("pause", async (args, _) =>
        {
            if (Interlocked.Increment(ref active) != 1) overlapped = true;
            await Task.Yield();
            lock (calls) calls.Add(Item(args[0]));
            Interlocked.Decrement(ref active);
            return args[0];
        }, "x"));
        var source = reducer + $"\nreduce(range(1, {count}), Add, 0)";
        RequireCleanParse(source, operations);

        var result = await KatLangEngine.RunAsync(source, new RunOptions { HostOperations = operations }).WaitAsync(TimeSpan.FromMinutes(5));

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal(((long)count * (count + 1) / 2).ToString(), SixRouteAgreement.Neutral(success.Value));
        Assert.False(overlapped, "two host calls overlapped");
        Assert.Equal(ascending ? Enumerable.Range(1, count) : Enumerable.Range(1, count).Reverse(), calls);
    }

    // A fold of `count` elements whose step for `count - 10` ignores its accumulator, observed on a 1 MiB thread.
    private static (EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget, List<(int Item, bool OnCallingThread)> Calls)
        ObserveLongSkippingFold(int count, string reducer)
    {
        var calls = new List<(int Item, int Thread)>();
        var operations = HostOperations.Create(HostOperation.Create("mark", (args, _) =>
        {
            lock (calls) calls.Add((Item(args[0]), Environment.CurrentManagedThreadId));
            return args[0];
        }, "x"));
        var source = reducer.Replace("SKIP", (count - 10).ToString(), StringComparison.Ordinal) + $"\nreduce(range(1, {count}), Last, 1 / 0)";
        var program = new Expr.AlgorithmExpr(ParseValidRoot(source, operations));

        (EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget) observed = default;
        var calling = -1;
        Exception? failure = null;
        var thread = new Thread(() =>
        {
            calling = Environment.CurrentManagedThreadId;
            try { observed = Evaluator.RunCountedObserved(program, hostOperations: operations); }
            catch (Exception error) { failure = error; }
        }, maxStackSize: 1024 * 1024) { IsBackground = true };
        thread.Start();
        Assert.True(thread.Join(WaitLimit), "the fold did not finish");
        Assert.Null(failure);
        return (observed.Result, observed.Budget!, calls.Select(call => (call.Item, OnCallingThread: call.Thread == calling)).ToList());
    }

    [Fact]
    public void LongSkippingFold_RunsOnlyTheStepsItDemands_OnTheCallingThread()
    {
        // Of 50,000 steps only the last ten run: the step for 49,990 ignores its accumulator, so every earlier
        // step, the start (1 / 0) and every fresh stack they would have needed never start.
        const string skipping = "Last(item, acc) = if(item == SKIP, 0, mark(item) + acc)";
        const string picking = "Last(item, acc) = mark(item)";
        const int count = 50_000;
        var (result, budget, calls) = ObserveLongSkippingFold(count, skipping);
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
        Assert.Equal(Enumerable.Range(count - 9, 10).Sum().ToString(), SixRouteAgreement.Neutral(result.Value.Value));
        Assert.Equal(Enumerable.Range(count - 9, 10).Reverse(), calls.Select(static call => call.Item));
        Assert.All(calls, static call => Assert.True(call.OnCallingThread, $"mark({call.Item}) left the calling thread"));
        Assert.Equal(10, budget.PeakFoldContinuations);
        Assert.Equal(0, budget.ActiveFoldContinuations);

        // The skipped steps charge nothing: what the ten demanded steps cost beyond the one step of a fold that
        // ignores every accumulator does not depend on how many steps were skipped.
        long Beyond(int length)
        {
            var (skipped, skippedBudget, _) = ObserveLongSkippingFold(length, skipping);
            var (picked, pickedBudget, pickedCalls) = ObserveLongSkippingFold(length, picking);
            Assert.True(skipped.IsOk && picked.IsOk);
            Assert.Equal([length], pickedCalls.Select(static call => call.Item));
            return skippedBudget.ConsumedSteps - pickedBudget.ConsumedSteps;
        }

        Assert.Equal(Beyond(20_000), Beyond(count));
    }

    [Fact]
    public void AccumulatingFoldWork_IsTheSameForEveryStep_WhereverItsChainContinues()
    {
        // Every 1,000 more steps cost exactly the same charged work — the same invocations and loop
        // iterations, the same expression checkpoints (one step is charged per 4,096 of them, so the step
        // total itself is compared net of those) — however the chain is split between the calling thread
        // and fresh stacks: a continuation charges nothing of its own.
        (long Invocations, long Checkpoints) Work(int count)
        {
            var (result, budget) = Observe(CallingAdd + $"reduce(range(1, {count}), Add, 0)");
            Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
            Assert.Equal(count, budget.PeakFoldContinuations);
            Assert.Equal(0, budget.ActiveFoldContinuations);
            var checkpoints = budget.ConsumedExpressionCheckpoints;
            return (budget.ConsumedSteps - checkpoints / EvaluationBudget.ExpressionCheckpointsPerStep, checkpoints);
        }

        var work = new[] { 1000, 2000, 3000, 4000 }.Select(Work).ToArray();
        for (var i = 2; i < work.Length; i++)
        {
            Assert.Equal(work[1].Invocations - work[0].Invocations, work[i].Invocations - work[i - 1].Invocations);
            Assert.Equal(work[1].Checkpoints - work[0].Checkpoints, work[i].Checkpoints - work[i - 1].Checkpoints);
        }
    }

    [Fact]
    public void GeneralFoldSteps_AllocateLittleMoreThanStreamedSteps()
    {
        // The same work per step (one Id call, one addition) on the general route (Id(item) + acc: every step
        // suspended) and the streamed route (acc + Id(item)). A general step's own extra is its accumulator's
        // computation object and the context write of that accumulator's demand; the streamed route makes a
        // Ready cell per accumulator instead. Measured per step in November 2026 (x64, eight-step folds):
        // Release 91 B (189 B while each accumulator held a closure and two delegates). Eight thousand steps per route, all on this
        // thread: the counter's quantum (about 8 KB) moves a per-step figure by at most 1 B.
        const int count = 8;
        const int runs = 1000;
        double PerStep(string reducer)
        {
            var parsed = SourceProvenance.ParseValid(reducer + $"reduce(range(1, {count}), Add, 0)");
            var program = new Expr.AlgorithmExpr(parsed.Root);
            for (var i = 0; i < 20; i++) Assert.True(Evaluator.RunCountedObserved(program).Result.IsOk);
            var before = GC.GetAllocatedBytesForCurrentThread();
            for (var i = 0; i < runs; i++) Evaluator.RunCountedObserved(program);
            return (GC.GetAllocatedBytesForCurrentThread() - before) / (double)(runs * count);
        }

        var general = PerStep(CallingAdd);
        var streamed = PerStep("Id(x) = x\nAdd(item, acc) = acc + Id(item)\n");
        Assert.InRange(general - streamed, -64, 160);
    }

    // ── Helpers ───────────────────────────────────────────────────────────────────────────────────────

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    private static int CountOccurrences(string text, string value)
    {
        var count = 0;
        for (var index = text.IndexOf(value, StringComparison.Ordinal); index >= 0; index = text.IndexOf(value, index + value.Length, StringComparison.Ordinal))
            count++;
        return count;
    }
}
