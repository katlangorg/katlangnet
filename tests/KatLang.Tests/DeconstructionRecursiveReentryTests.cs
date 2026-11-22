using System.Globalization;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;
using Xunit.Abstractions;
using Observation = KatLang.Tests.DeconstructionMemoEligibilityTests.Observation;
using Route = KatLang.Tests.DeconstructionMemoEligibilityTests.Route;

namespace KatLang.Tests;

/// <summary>
/// THE PER-EXECUTION RE-ENTRY GUARD of the deconstruction shared-bind memo (2026-11-22; C#-only resource
/// accounting, Lean unchanged: Lean has no group memo and binds the cached source again). A bind is stored only
/// when it OWNS its execution — group, actual pattern list and source entry: no bind of that very execution was
/// running when it started (<see cref="RunScopedDeconstructionBindingCache"/>). Until then the guard was
/// GROUP-wide, so a recursive owner whose right-hand side calls it again — <c>F(k) = { x0, …, x{N-1} = if(k &gt;
/// 0, F(k - 1), 0), k, … ⏎ x0 + … }</c> — bound every inner activation once per distinct target read while the
/// outer activation's bind of the same group still ran: width N and re-entry depth D cost 1 + D·N full binds of
/// O(N) cells each (R12: seven binds) instead of one per activation, D + 1.
/// <para>These tests pin the recovered reuse and its limits on the generic, optimized and genuinely suspending
/// async routes: exactly one bind per activation at every width and depth, against each program's UNSHARED
/// execution (every helper its own bind) for value, emitted count, error text and span, and host effects in
/// order; the nonrecursive controls (the same recursion outside the bind, and separate callback activations),
/// whose counts never depended on the guard; the negative controls that must never share — distinct activations
/// with equal arguments, mutually recursive owners of one shape, Q-37 re-entry of one execution inside a recursion;
/// lazy demand and failure order; explicit <c>t()</c> calls, which now reuse their activation's collector
/// completion; cleanup after a failure or a cancellation deep inside the recursion; and retention: stored inner
/// binds die with their activations, the transient owning-execution set holds an activation only while its bind
/// runs, and allocation is the nonrecursive control's instead of quadratic in the width.</para>
/// </summary>
public sealed class DeconstructionRecursiveReentryTests(ITestOutputHelper output)
{
    private static string Names(int width, string prefix = "x")
        => string.Join(", ", Enumerable.Range(0, width).Select(i => prefix + i.ToString(CultureInfo.InvariantCulture)));

    private static string Sum(int width, string prefix = "x")
        => string.Join(" + ", Enumerable.Range(0, width).Select(i => prefix + i.ToString(CultureInfo.InvariantCulture)));

    private static string Rest(int count, string item) => string.Concat(Enumerable.Repeat(", " + item, count));

    /// <summary>Re-entry through the right-hand side: activation k's first bind is still reading its source while F(k - 1) binds.</summary>
    internal static string Recursive(int width, int depth, string baseCase = "trace(0)")
        => string.Create(CultureInfo.InvariantCulture,
            $"F(k) = {{\n    {Names(width)} = if(k > 0, F(k - 1), {baseCase}){Rest(width - 1, "k")}\n    {Sum(width)}\n}}\nF({depth})");

    /// <summary>Control: the same recursion in a body row before the targets, so no bind ever starts inside another.</summary>
    private static string BodyRecursion(int width, int depth)
        => string.Create(CultureInfo.InvariantCulture,
            $"F(k) = {{\n    {Names(width)} = k{Rest(width - 1, "k")}\n    if(k > 0, F(k - 1), trace(0)) + {Sum(width)}\n}}\nF({depth})");

    /// <summary>Control: <paramref name="count"/> separate activations from callbacks.</summary>
    private static string CallbackActivations(int width, int count)
        => string.Create(CultureInfo.InvariantCulture,
            $"G(k) = {{\n    {Names(width)} = trace(k){Rest(width - 1, "k")}\n    {Sum(width)}\n}}\nrange(1, {count}).map{{ G(n) }}.sum");

    private static Expr Program(string source) => new Expr.AlgorithmExpr(DeconstructionMemoEligibilityTests.Parse(source));

    private static Task<Observation> Observe(Expr program, Route route, EvaluationLimits? limits = null, bool shareBinds = true)
        => DeconstructionMemoEligibilityTests.Observe(program, route, limits, shareBinds);

    /// <summary>Sharing changes no value, emitted count, error text or span, and no host effect or its order — only accounting, downward.</summary>
    private static void AssertSameMeaning(Observation shared, Observation unshared)
    {
        Assert.Equal(unshared.Outcome + " | " + unshared.Effects, shared.Outcome + " | " + shared.Effects);
        Assert.True(shared.Binds <= unshared.Binds, $"{shared} vs {unshared}");
        Assert.True(shared.Steps <= unshared.Steps, $"{shared} vs {unshared}");
        Assert.True(shared.Materialized <= unshared.Materialized, $"{shared} vs {unshared}");
    }

    public static TheoryData<int, int, Route> WidthsAndDepths()
    {
        var data = new TheoryData<int, int, Route>();
        foreach (var (width, depth) in new[] { (2, 0), (2, 1), (2, 24), (3, 3), (8, 4), (16, 8), (64, 2) })
            foreach (var route in Enum.GetValues<Route>())
                data.Add(width, depth, route);
        return data;
    }

    /// <summary>
    /// ONE bind per activation at every capture width and re-entry depth: D + 1 binds where the group-wide guard
    /// took 1 + D·N (and the unshared execution, every helper on its own, (D + 1)·N). Each eliminated bind is one
    /// read of the activation's already-published source — one step and one expression checkpoint — so against
    /// the unshared run the steps and checkpoints fall by exactly the eliminated binds while the value, the one
    /// base-case trace, the peak depth and the materialized items stay.
    /// </summary>
    [Theory]
    [MemberData(nameof(WidthsAndDepths))]
    public async Task RecursiveOwner_BindsOncePerActivation(int width, int depth, Route route)
    {
        var program = Program(Recursive(width, depth));
        var shared = await Observe(program, route);
        var unshared = await Observe(program, route, shareBinds: false);
        var expected = (width - 1) * depth * (depth + 1) / 2;
        Assert.Equal(string.Create(CultureInfo.InvariantCulture, $"ok {expected} n=1 | t(0)"), shared.Comparable);
        AssertSameMeaning(shared, unshared);
        Assert.Equal(depth + 1, shared.Binds);
        Assert.Equal((depth + 1) * width, unshared.Binds);
        var eliminated = unshared.Binds - shared.Binds;
        Assert.Equal(eliminated, unshared.Steps - shared.Steps);
        Assert.Equal(eliminated, unshared.Checkpoints - shared.Checkpoints);
        Assert.Equal(unshared.PeakDepth, shared.PeakDepth);
        Assert.Equal(unshared.Materialized, shared.Materialized);
    }

    /// <summary>
    /// The nonrecursive controls never depended on the guard: the same recursion written in a body row (no bind
    /// starts inside another) and separate callback activations bind once per activation, with the accounting the
    /// group-wide guard gave them — the recursive owner now matches its body-row control bind for bind.
    /// </summary>
    [Theory]
    [InlineData(Route.Generic)]
    [InlineData(Route.Optimized)]
    [InlineData(Route.SuspendingAsync)]
    public async Task NonrecursiveControls_KeepOneBindPerActivation(Route route)
    {
        foreach (var (width, depth) in new[] { (2, 4), (8, 8), (32, 3) })
        {
            var body = await Observe(Program(BodyRecursion(width, depth)), route);
            Assert.Equal(string.Create(CultureInfo.InvariantCulture, $"ok {width * depth * (depth + 1) / 2} n=1 | t(0)"), body.Comparable);
            Assert.Equal(depth + 1, body.Binds);
            Assert.Equal((await Observe(Program(Recursive(width, depth)), route)).Binds, body.Binds);

            var callbacks = await Observe(Program(CallbackActivations(width, depth)), route);
            Assert.Equal(depth, callbacks.Binds);
            AssertSameMeaning(callbacks, await Observe(Program(CallbackActivations(width, depth)), route, shareBinds: false));
            Assert.Equal(string.Join(",", Enumerable.Range(1, depth).Select(k => string.Create(CultureInfo.InvariantCulture, $"t({k})"))), callbacks.Effects);
        }
    }

    /// <summary>
    /// NEGATIVE CONTROLS — binds that must never be shared. Every activation evaluates its OWN right-hand side
    /// (one trace each, in recursion order) and reads its own targets; two calls with equal arguments are distinct
    /// activations; and two mutually recursive owners of the same shape are distinct groups, each nested in the
    /// other's running binds. Sharing any of these would drop a trace or change a value; each binds exactly once
    /// per activation and agrees with its unshared execution.
    /// </summary>
    [Theory]
    [InlineData(Route.Generic)]
    [InlineData(Route.Optimized)]
    [InlineData(Route.SuspendingAsync)]
    public async Task DistinctActivationsAndOwners_NeverShareABind(Route route)
    {
        const string perActivation = "F(k) = {\n    a, b, c = if(k > 0, F(k - 1), 0), trace(k), k\n    a + b + c\n}\n";
        var cases = new (string Source, string Comparable, long Binds)[]
        {
            (perActivation + "F(3)", "ok 12 n=1 | t(0),t(1),t(2),t(3)", 4),
            (perActivation + "F(2) + F(2)", "ok 12 n=1 | t(0),t(1),t(2),t(0),t(1),t(2)", 6),
            (perActivation + "F(2), F(2)", "ok S[6, 6] n=2 | t(0),t(1),t(2),t(0),t(1),t(2)", 6),
            ("F(k) = {\n    a, b = if(k > 0, G(k - 1), trace(0)), k\n    a + b\n}\n"
                + "G(k) = {\n    a, b = if(k > 0, F(k - 1), trace(0)), k * 10\n    a + b\n}\nF(4), G(4)",
                "ok S[46, 64] n=2 | t(0),t(0)", 10),
        };
        foreach (var (source, comparable, binds) in cases)
        {
            var program = Program(source);
            var shared = await Observe(program, route);
            Assert.Equal(comparable, shared.Comparable);
            AssertSameMeaning(shared, await Observe(program, route, shareBinds: false));
            Assert.Equal(binds, shared.Binds);
        }
    }

    /// <summary>
    /// Q-37 re-entry of ONE execution inside a recursion: the base activation's right-hand side reads its own
    /// target <c>a</c> while its owning bind runs, so those re-entrant binds read an unpublished intermediate
    /// source and are never stored (the per-execution guard, and the publication check before it), while the
    /// outer activations, which only re-enter the GROUP, store theirs. The value is the unshared execution's,
    /// with its tocks in order.
    /// </summary>
    [Theory]
    [InlineData(Route.Generic)]
    [InlineData(Route.Optimized)]
    [InlineData(Route.SuspendingAsync)]
    public async Task OneExecutionReenteredInsideARecursion_StaysUnstored(Route route)
    {
        var program = Program("F(k) = {\n    a, b = if(k > 0, (F(k - 1), k), if(tock() < 3, (a + 1, 0), (5, 5)))\n    a + b\n}\nF(2)");
        var shared = await Observe(program, route);
        var unshared = await Observe(program, route, shareBinds: false);
        Assert.Equal("ok 10 n=1 | tock#1,tock#2,tock#3", shared.Comparable);
        AssertSameMeaning(shared, unshared);
        // F(2), F(1) and F(0) own one bind each; F(0)'s two re-entrant reads of `a` bind on their own, unstored.
        Assert.Equal(5, shared.Binds);
        Assert.Equal(8, unshared.Binds);
        Assert.Equal(unshared.Binds - shared.Binds, unshared.Steps - shared.Steps);
    }

    /// <summary>
    /// Laziness and failure order are unchanged. An activation that demands no target never evaluates its
    /// right-hand side (F(3) here returns k and stops the recursion, inside F(4)'s bind), and a failure raised in
    /// an inner activation's right-hand side, after deeper activations completed their binds, surfaces with the
    /// unshared execution's text, span and preceding effects.
    /// </summary>
    [Theory]
    [InlineData(Route.Generic)]
    [InlineData(Route.Optimized)]
    [InlineData(Route.SuspendingAsync)]
    public async Task LazyDemandAndFailureOrder_AreUnchanged(Route route)
    {
        var lazy = Program("F(k) = {\n    a, b = trace(k), if(k > 0, F(k - 1), 0)\n    if(k > 3, a + b, k)\n}\nF(5)");
        var lazyShared = await Observe(lazy, route);
        Assert.Equal("ok 12 n=1 | t(5),t(4)", lazyShared.Comparable);
        AssertSameMeaning(lazyShared, await Observe(lazy, route, shareBinds: false));
        Assert.Equal(2, lazyShared.Binds);

        var failing = Program("F(k) = {\n    a, b = if(k > 0, F(k - 1), 0), if(k == 2, 1 / 0, trace(k))\n    a + b\n}\nF(3)");
        var failedShared = await Observe(failing, route);
        var failedUnshared = await Observe(failing, route, shareBinds: false);
        Assert.StartsWith("err DivisionByZero:", failedShared.Outcome);
        Assert.Equal("t(0),t(1)", failedShared.Effects);
        AssertSameMeaning(failedShared, failedUnshared);
    }

    /// <summary>
    /// A recursive program near a step limit may now complete: the eliminated binds were charged work. At width 8
    /// and depth 4 the run needs exactly its own steps (the group-wide guard spent 28 more: 33 binds instead of
    /// 5), completes at that limit on every route and still refuses one step below it.
    /// </summary>
    [Theory]
    [InlineData(Route.Generic)]
    [InlineData(Route.Optimized)]
    [InlineData(Route.SuspendingAsync)]
    public async Task EliminatedBinds_MoveTheStepLimitVerdict(Route route)
    {
        var program = Program(Recursive(8, 4));
        var unlimited = await Observe(program, route);
        Assert.Equal("ok 70 n=1 | t(0)", unlimited.Comparable);
        Assert.Equal(5, unlimited.Binds);
        Assert.Equal(91, unlimited.Steps);
        Assert.Equal(unlimited.ToString(), (await Observe(program, route, new EvaluationLimits { MaxSteps = 91 })).ToString());
        Assert.StartsWith("err EvaluationStepLimitExceeded:", (await Observe(program, route, new EvaluationLimits { MaxSteps = 90 })).Outcome);
    }

    /// <summary>
    /// Explicit fresh calls <c>t()</c> of a collecting target in an INNER activation read their activation's
    /// stored bind (Q-38), so its collector is materialized once and every read returns that one completed list
    /// — the CLR object <c>t</c> returns —, where the group-wide guard rebound per call, re-materializing (and
    /// re-charging) the collector into a fresh list each time.
    /// </summary>
    [Theory]
    [InlineData(Route.Generic)]
    [InlineData(Route.Optimized)]
    [InlineData(Route.SuspendingAsync)]
    public async Task ExplicitCallsInAnInnerActivation_ReuseItsCollectorCompletion(Route route)
    {
        var program = Program("F(k) = {\n    h, *t = if(k > 0, F(k - 1), 0), k, k, k\n    h + t().count + t().count + t.count\n}\nF(3)");
        var shared = await Observe(program, route);
        var unshared = await Observe(program, route, shareBinds: false);
        Assert.Equal("ok 36 n=1 | ", shared.Comparable);
        AssertSameMeaning(shared, unshared);
        Assert.Equal(4, shared.Binds);
        // One materialization of t's three items per activation (and the right-hand side's four items).
        Assert.Equal(4 * (4 + 3), shared.Materialized);
        Assert.True(unshared.Materialized > shared.Materialized, $"{shared} vs {unshared}");

        // The base activation runs inside the outer activations' binds; its t and t() are one list object.
        var identity = Program("F(k) = {\n    h, *t = if(k > 0, F(k - 1), 0), k, k\n    if(k > 0, h, (t, t(), t()))\n}\nF(2)");
        var (result, _) = await RunAsync(identity, route);
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        var lists = Assert.IsType<Result.SequenceValue>(result.Value.Value).Items;
        Assert.Equal(3, lists.Count);
        Assert.Equal("L[0, 0]", SixRouteAgreement.Neutral(lists[0]));
        Assert.Same(lists[0], lists[1]);
        Assert.Same(lists[0], lists[2]);
    }

    private static async Task<(EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget)> RunAsync(
        Expr program, Route route, HostOperations? operations = null, EvaluationObservations? observations = null,
        CancellationToken cancellationToken = default)
    {
        operations ??= HostOperations.Create(
            HostOperation.Create("tock", (_, _) => new Result.Atom(0)),
            HostOperation.Create("trace", (args, _) => args[0], "x"));
        return route == Route.SuspendingAsync
            ? await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
                program, zeroArgPropertyResultCache: new SuspendingAsyncZeroArgPropertyResultCache(), observations: observations,
                hostOperations: operations, cancellationToken: cancellationToken))
            : Evaluator.RunCountedObserved(program, enableOptimizations: route == Route.Optimized, observations: observations,
                hostOperations: operations, cancellationToken: cancellationToken);
    }

    /// <summary>
    /// ASYNC CLEANUP after a failure and after a cancellation raised in the BASE activation, while every outer
    /// activation's owning bind is running: the run ends with its ordinary error (the unshared execution's) or the
    /// host's cancellation, its memo holds no owning-execution entry and stores no bind (none completed), and a
    /// fresh run of the same cancelled tree then has the ordinary one-bind-per-activation accounting.
    /// </summary>
    [Theory]
    [InlineData(Route.Generic)]
    [InlineData(Route.Optimized)]
    [InlineData(Route.SuspendingAsync)]
    public async Task FailureOrCancellationDeepInTheRecursion_LeavesNoGuardAndNoBind(Route route)
    {
        var failing = Program(Recursive(4, 5, baseCase: "1 / 0"));
        var observations = new EvaluationObservations();
        var (failed, _) = await RunAsync(failing, route, observations: observations);
        Assert.True(failed.IsError);
        Assert.Equal(KatLangErrorCode.DivisionByZero, KatLangError.FromEvalError(failed.Error).Code);
        Assert.Equal(0, observations.DeconstructionBindingCache!.RunningExecutionCount);
        Assert.Equal(0, observations.DeconstructionBindingCache.Count);
        Assert.Equal(6, observations.DeconstructionFullBindCount);
        Assert.Equal((await Observe(failing, route, shareBinds: false)).Outcome, (await Observe(failing, route)).Outcome);

        using var cts = new CancellationTokenSource();
        var stops = HostOperations.Create(
            HostOperation.Create("tock", (_, _) => new Result.Atom(0)),
            HostOperation.Create("trace", (args, _) => args[0], "x"),
            route == Route.SuspendingAsync
                ? HostOperation.CreateAsync("stop", async (_, token) =>
                {
                    await Task.Yield();
                    await cts.CancelAsync();
                    token.ThrowIfCancellationRequested();
                    return new Result.Atom(0);
                })
                : HostOperation.Create("stop", (_, token) =>
                {
                    cts.Cancel();
                    token.ThrowIfCancellationRequested();
                    return new Result.Atom(0);
                }));
        var parsed = Parser.Parse(Recursive(4, 5, baseCase: "stop()"), new RunOptions { HostOperations = stops });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        var cancelledObservations = new EvaluationObservations();
        await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
            await RunAsync(new Expr.AlgorithmExpr(parsed.Root), route, stops, cancelledObservations, cts.Token));
        Assert.Equal(0, cancelledObservations.DeconstructionBindingCache!.RunningExecutionCount);
        Assert.Equal(0, cancelledObservations.DeconstructionBindingCache.Count);
        Assert.Equal(6, cancelledObservations.DeconstructionFullBindCount);

        // The SAME tree, run again with a `stop` that does not cancel: ordinary value and one bind per activation.
        var resumes = HostOperations.Create(
            HostOperation.Create("tock", (_, _) => new Result.Atom(0)),
            HostOperation.Create("trace", (args, _) => args[0], "x"),
            HostOperation.Create("stop", (_, _) => new Result.Atom(0)));
        var freshObservations = new EvaluationObservations();
        var (fresh, _) = await RunAsync(new Expr.AlgorithmExpr(parsed.Root), route, resumes, freshObservations);
        Assert.True(fresh.IsOk, fresh.IsError ? fresh.Error.ToString() : "");
        Assert.Equal("45", SixRouteAgreement.Neutral(fresh.Value.Value));
        Assert.Equal(6, freshObservations.DeconstructionFullBindCount);
        Assert.Equal(6, freshObservations.DeconstructionBindingCache!.Count);
        Assert.Equal(0, freshObservations.DeconstructionBindingCache.RunningExecutionCount);
    }

    /// <summary>
    /// RETENTION. At the deepest point of a width-16, depth-8 recursion every activation's owning bind is running
    /// (nine entries in the transient owning-execution set) and none is stored; once the recursion returned, its
    /// nine stored binds are unreachable with their activations, the set is empty and no partition is live. Over
    /// two thousand loop rounds, collection at a fixed interval makes dead identities available for reclamation
    /// while the evaluator is still running. Table capacity stays bounded independently of the host's GC budget.
    /// </summary>
    [Fact]
    public void StoredInnerBinds_DieWithTheirActivations()
    {
        var probes = new List<(int Stored, int Running, int Live)>();
        EvaluationObservations? observations = null;
        var operations = HostOperations.Create(HostOperation.Create("probe", (_, _) =>
        {
            ForceFullCollection();
            var memo = observations!.DeconstructionBindingCache!;
            probes.Add((memo.Count, memo.RunningExecutionCount, memo.LivePartitionCount()));
            return new Result.Atom(0);
        }));

        observations = new EvaluationObservations();
        var single = Run(Recursive(16, 8, baseCase: "probe()") + " + probe()", operations, observations);
        Assert.Equal("540", single);
        Assert.Equal(9, observations.DeconstructionFullBindCount);
        Assert.Equal(new[] { (0, 9, 0), (9, 0, 0) }, probes);

        const int rounds = 2_000;
        const int collectEvery = 256;
        probes.Clear();
        observations = new EvaluationObservations();
        var loop = Recursive(8, 4, baseCase: "0");
        loop = loop[..loop.LastIndexOf('\n')] + string.Create(CultureInfo.InvariantCulture,
            $"\nStep(s) = s + 1 + F(4) * 0 + if((s + 1) mod {collectEvery} == 0, probe(), 0)\nStep(0).repeat({rounds}) + probe() * 0");
        Assert.Equal(rounds.ToString(CultureInfo.InvariantCulture), Run(loop, operations, observations));
        var memo = observations.DeconstructionBindingCache!;
        output.WriteLine($"Loop stored {memo.Count} binds with table capacity {memo.PromptTableCapacity}.");
        Assert.Equal(5 * rounds, observations.DeconstructionFullBindCount);
        Assert.Equal(5 * rounds, memo.Count);
        Assert.Equal(rounds / collectEvery + 1, probes.Count);
        for (var i = 0; i < probes.Count; i++)
        {
            var (stored, running, live) = probes[i];
            Assert.Equal(5 * Math.Min((i + 1) * collectEvery, rounds), stored);
            Assert.Equal(0, running);
            Assert.InRange(live, 0, 64);
        }
        // At most 5 * 256 new identities between collections, plus up to 64 surviving a probe.
        // The power-of-two table doubles only if more than half its entries are live.
        Assert.InRange(memo.PromptTableCapacity, 8, 4_096);
        GC.KeepAlive(memo);
    }

    private static string Run(string source, HostOperations operations, EvaluationObservations observations)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), observations: observations, hostOperations: operations);
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        return SixRouteAgreement.Neutral(result.Value.Value);
    }

    /// <summary>
    /// ALLOCATION follows the binds: a width-64, depth-8 recursion now allocates about what its body-row control
    /// allocates (measured 1.38 MB each in Release; the group-wide guard's 513 binds allocated 26.0 MB, 19 times
    /// the control). A coarse in-process ratio, warmed up, assertions outside the measured windows.
    /// </summary>
    [Fact]
    public void RecursiveOwner_AllocatesLikeItsNonrecursiveControl()
    {
        var recursive = DeconstructionMemoEligibilityTests.Parse(Recursive(64, 8));
        var control = DeconstructionMemoEligibilityTests.Parse(BodyRecursion(64, 8));
        var operations = HostOperations.Create(
            HostOperation.Create("tock", (_, _) => new Result.Atom(0)),
            HostOperation.Create("trace", (args, _) => args[0], "x"));
        long Measure(Algorithm.User root)
        {
            var best = long.MaxValue;
            for (var attempt = 0; attempt < 4; attempt++)
            {
                var before = GC.GetAllocatedBytesForCurrentThread();
                var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(root), hostOperations: operations);
                var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
                Assert.True(result.IsOk);
                best = Math.Min(best, allocated);
            }

            return best;
        }

        Measure(recursive);
        Measure(control);
        var recursiveBytes = Measure(recursive);
        var controlBytes = Measure(control);
        output.WriteLine($"recursive {recursiveBytes} B, control {controlBytes} B");
        Assert.InRange(recursiveBytes, 1, 2 * controlBytes);
    }

    private static void ForceFullCollection()
    {
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
        GC.WaitForPendingFinalizers();
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
    }
}
