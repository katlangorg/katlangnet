using System.Collections;
using System.Reflection;
using KatLang.Evaluation;
using KatLang.TestInfrastructure;
using KatLang.Tests.AsyncEvaluation;
using KatLang.Tests.InvocationRoute;

namespace KatLang.Tests;

/// <summary>
/// WIDE PARAMETER FRAMES (2026-11-21 adversarial performance and reliability investigation, baseline
/// <c>8947d21e</c>, finding <c>evaluator-runtime-quadratic-parameter-width</c>). The parameter environments are
/// ordered association lists — first match wins, a callee's own bindings before the inherited ones — and every
/// parameter read scanned the head's own names (<c>CapturedParameterActivation</c>) and then the bindings
/// (<c>LookupNeed</c>), every forwarded parameter did the same while its call's supply formed, every call
/// shadowed each inherited binding by scanning the callee's names, and the nearest-owner walk of a captured read
/// scanned each level's names: O(N) per read, O(N²) per body that reads its N parameters. Since 2026-11-22 a frame
/// of at least <see cref="Evaluator.MinimumIndexedParameterCount"/> names keeps the owned-name index its
/// activation's capture builds (<see cref="OwnedParameterNames"/>, <see cref="OwnedNeedBindings"/>; it replaced the
/// filter's former name set), lends it to the tier the call minted (<see cref="Evaluator.WideBoundNeedEnv"/>, which
/// still scans for any other name), and shadows a wide inherited tier through one set. Narrower frames keep the
/// scans. Implementation-only: these tests pin each structure against the ordered scan it replaces — first-visible
/// bindings, environment order, repeated and null names, a scope whose activation was captured for another list —
/// the absence of per-read rescans and allocations, and whole programs (own, captured, forwarded, recursive, clause
/// and nested reads, NEED-04 repeated names, depth, host edits) on the plain, counted, optimized and async routes.
/// </summary>
public class WideParameterFrameTests
{
    private const int Threshold = Evaluator.MinimumIndexedParameterCount;

    private delegate NeedCell? NeedLookup(IReadOnlyList<(string Name, NeedCell Cell)> env, string name);

    private static readonly NeedLookup LookupNeed = typeof(Evaluator)
        .GetMethod("LookupNeed", BindingFlags.NonPublic | BindingFlags.Static)!.CreateDelegate<NeedLookup>();

    private static NeedCell Cell(int value) => NeedCell.Ready(new(new Result.Atom(value), 1));

    // The ordered first-match scans every structure here must agree with.
    private static T? Linear<T>(IReadOnlyList<(string Name, T Item)> env, string name) where T : class
    {
        foreach (var (n, item) in env)
            if (string.Equals(n, name, StringComparison.Ordinal)) return item;
        return null;
    }

    private static List<(string Name, T Item)> FirstOwned<T>(IReadOnlyList<(string Name, T Item)> env, IReadOnlyList<string> names)
    {
        var kept = new List<(string Name, T Item)>();
        foreach (var binding in env)
        {
            if (names.Contains(binding.Name, StringComparer.Ordinal) && !kept.Any(k => string.Equals(k.Name, binding.Name, StringComparison.Ordinal)))
                kept.Add(binding);
        }
        return kept;
    }

    private static string[] Names(string prefix, int count) => Enumerable.Range(0, count).Select(i => prefix + i).ToArray();

    // Probe names: owned ones, near misses (case, a trailing space), unowned ones, the empty name and null.
    private static IEnumerable<string> Probes(IReadOnlyList<string> owned)
        => owned.Concat(owned.Where(static n => n is not null).Select(static n => n.ToUpperInvariant()))
            .Concat(["q0", "q7", "missing", "", "p0 ", null!]).Distinct();

    public static TheoryData<int> Widths => new() { 1, 8, 9, Threshold - 1, Threshold, Threshold + 1, 64, 300 };

    // ── The activation's capture ────────────────────────────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(Widths))]
    public void ActivationCapture_KeepsTheFirstBindingOfEachOwnedName_InEnvironmentOrder_OnBothTiers(int width)
    {
        // The owned names repeat one name and, from the threshold on, carry a null (a host-built pattern can).
        string[] names = width >= Threshold ? [.. Names("p", width - 2), "p0", null!] : Names("p", width);
        var random = new Random(9173 + width);
        var pool = names.Concat(["q0", "q1", "P0", null!]).ToArray();
        // Every pool name several times, shuffled: first bindings are not in signature order.
        var needs = Enumerable.Range(0, 3 * pool.Length).Select(i => (pool[random.Next(pool.Length)], Cell(i))).ToArray();
        var values = Enumerable.Range(0, 2 * pool.Length).Select(i => (pool[random.Next(pool.Length)], (Result)new Result.Atom(i))).ToArray();
        var ctx = Evaluator.EvalCtx.Empty.WithNeedEnv(needs);

        var captured = ParameterActivation.Capture(names, ctx, values);
        Assert.Equal(FirstOwned(values, names), captured.Values);
        Assert.Equal(FirstOwned(needs, names), captured.Needs);
        Assert.Equal(names.Length >= Threshold, captured.Needs is OwnedNeedBindings);
        if (captured.Needs is OwnedNeedBindings owned)
        {
            Assert.Same(names, owned.Owned.Names);
            foreach (var probe in Probes(names))
            {
                Assert.Same(Linear(captured.Needs, probe), owned.Find(probe));
                Assert.Same(Linear(captured.Needs, probe), LookupNeed(captured.Needs, probe));
                Assert.Equal(Evaluator.ContainsOrdinal(names, probe), owned.Owned.Owns(probe));
            }
        }

        // Nothing to filter: both tiers empty, and the wide need tier still knows which names it owns.
        var empty = ParameterActivation.Capture(names, Evaluator.EvalCtx.Empty, []);
        Assert.Empty(empty.Values);
        Assert.Empty(empty.Needs);
        Assert.Equal(names.Length >= Threshold, empty.Needs is OwnedNeedBindings { Owned.Names: var kept } && ReferenceEquals(kept, names));
    }

    // ── The minted tier ─────────────────────────────────────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(Widths))]
    public void AMintedTier_AnswersTheOrderedFirstMatch_AndItsOwnNamesWithoutScanning_OnceLent(int width)
    {
        // own: width bindings (one repeated name and, from the threshold on, a null); inherited: an overlap with own,
        // a repeated name, a null.
        string[] ownNames = width >= 2 ? [.. Names("p", width - 1), "p0"] : Names("p", width);
        if (width >= Threshold) ownNames[^2] = null!;
        (string Name, NeedCell Cell)[] own = ownNames.Select((n, i) => (n, Cell(i))).ToArray();
        (string Name, NeedCell Cell)[] inherited = [("p1", Cell(-1)), ("outer", Cell(-2)), ("outer", Cell(-3)), (null!, Cell(-4)), ("q0", Cell(-5))];
        var minted = Evaluator.Concat(own, inherited);
        var probes = Probes([.. ownNames, "outer"]).ToArray();
        Assert.Equal([.. own, .. inherited], minted);
        foreach (var probe in probes)
            Assert.Same(Linear(minted, probe), LookupNeed(minted, probe));
        if (own.Length < Threshold)
        {
            // Wide or not by the callee's OWN cells: a wide inherited part alone keeps the plain tier.
            Assert.IsType<Evaluator.BoundNeedEnv>(minted);
            Assert.IsType<Evaluator.BoundNeedEnv>(Evaluator.Concat(own, [.. inherited, .. Enumerable.Range(0, Threshold).Select(i => ("w" + i, Cell(i)))]));
            return;
        }

        var wide = Assert.IsType<Evaluator.WideBoundNeedEnv>(minted);
        Assert.IsAssignableFrom<Evaluator.BoundNeedEnv>(minted);
        Assert.False(wide.IsLent);
        Assert.True(wide.ScannedBindings > 0, "without a lender every lookup scans");

        // A fresh tier, entered by an activation over the callee's names: it lends its owned-name index, and a
        // second activation's names are not taken, so the head's own names are then answered without a scan.
        var fresh = (Evaluator.WideBoundNeedEnv)Evaluator.Concat(own, inherited);
        var lender = ParameterActivation.Capture(ownNames, Evaluator.EvalCtx.Empty.WithNeedEnv(fresh), []);
        Assert.Equal(FirstOwned(fresh, ownNames), lender.Needs);
        Assert.True(fresh.IsLent);
        _ = ParameterActivation.Capture(Names("outer", Threshold), Evaluator.EvalCtx.Empty.WithNeedEnv(fresh), []);
        foreach (var name in ownNames)
            Assert.Same(Linear(fresh, name), LookupNeed(fresh, name));
        Assert.Equal(0, fresh.ScannedBindings);
        // Every other name is scanned for, with the scan's answer.
        foreach (var probe in probes)
            Assert.Same(Linear(fresh, probe), LookupNeed(fresh, probe));
        Assert.True(fresh.ScannedBindings > 0);
    }

    // ── Membership and shadowing ────────────────────────────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(Widths))]
    public void AnActivatedHead_AnswersWhetherItBindsAName_WithoutRescanningItsNames_OnceItIsWide(int width)
    {
        var plain = Names("p", width);
        var names = new FrameReadCountingList<string>(plain);
        var owner = new Algorithm.User(null, plain.Select(static n => (ParameterPattern)new CaptureParameterPattern(n)).ToArray(), [], [], [new Expr.Num(1)]);
        var minted = Evaluator.Concat(plain.Select((n, i) => (n, Cell(i))).ToArray(), [("outer", Cell(-1))]);
        var entered = Evaluator.EnterAlgorithmBody(owner, Evaluator.EvalCtx.Empty.WithNeedEnv(minted), [], parameterNames: names, invoked: true);
        var head = Assert.IsType<ScopeCtx>(entered.HeadScope);
        Assert.Same(names, head.Parameters);

        names.Reads = 0;
        foreach (var probe in Probes(plain))
            Assert.Equal(plain.Contains(probe, StringComparer.Ordinal), Evaluator.ScopeBindsParameter(head, probe));
        if (width >= Threshold)
            Assert.Equal(0, names.Reads);
        else
            Assert.True(names.Reads > 0);

        // The head's own reads find its cells; a nested parameterless body's captured reads reach them through the
        // owner walk — both the ordered scan's answers.
        var inner = new Algorithm.User(head, [], [], [], [new Expr.Num(2)]);
        var nested = Evaluator.EnterAlgorithmBody(inner, entered, []);
        names.Reads = 0;
        foreach (var probe in plain)
        {
            Assert.Same(Linear(minted, probe), Evaluator.ParameterNeedCell(probe, entered));
            Assert.Same(Linear(minted, probe), Evaluator.ParameterNeedCell(probe, nested));
        }
        Assert.Null(Evaluator.ParameterNeedCell("missing", nested));
        // Neither the head's own reads nor the nested captured reads rescan the head's names once it is wide.
        if (width >= Threshold)
            Assert.Equal(0, names.Reads);
        else
            Assert.True(names.Reads > 0);
    }

    [Fact]
    public void AScopeWhoseActivationWasCapturedForAnotherList_IsAnsweredByItsOwnList()
    {
        // The owned-name index answers only for the very list it was built from; any other list is scanned.
        var listed = Names("a", 40);
        var captured = Names("b", 40);
        var scope = new ScopeCtx(null, [], [], listed) { Activation = ParameterActivation.Capture(captured, Evaluator.EvalCtx.Empty, []) };
        Assert.IsType<OwnedNeedBindings>(scope.Activation!.Needs);
        Assert.True(Evaluator.ScopeBindsParameter(scope, "a3"));
        Assert.False(Evaluator.ScopeBindsParameter(scope, "b3"));
        var copy = scope with { Parameters = captured };
        Assert.True(Evaluator.ScopeBindsParameter(copy, "b3"));
        Assert.False(Evaluator.ScopeBindsParameter(copy, "a3"));
    }

    public static TheoryData<int, int> ShadowShapes => new()
    {
        { 0, 40 }, { 8, 40 }, { Threshold - 1, 40 }, { Threshold, 8 }, { Threshold, 9 }, { 40, 40 }, { 300, 300 },
    };

    [Theory]
    [MemberData(nameof(ShadowShapes))]
    public void ShadowingTheInheritedTier_RemovesEveryBindingOfTheCalleesNames_InOrder(int names, int inherited)
    {
        var random = new Random(31 * names + inherited);
        var callee = Names("p", names).Concat(names >= Threshold ? [null!] : Array.Empty<string>()).ToArray();
        var pool = callee.Concat(["q0", "q1", "P1", null!]).ToArray();
        (string Name, NeedCell Cell)[] tier = Enumerable.Range(0, inherited).Select(i => (pool[random.Next(pool.Length)], Cell(i))).ToArray();
        var shadowed = Evaluator.ShadowInheritedParameterEnvironments(Evaluator.EvalCtx.Empty.WithNeedEnv(tier), callee).NeedEnv;
        Assert.Equal(tier.Where(b => !callee.Contains(b.Name, StringComparer.Ordinal)), shadowed);
    }

    // ── Allocation (isolated child process) ─────────────────────────────────────────────────────────

    [Fact]
    public void WideFrameReads_AllocateNothing_OwnAndCaptured_GcIsolatedChild()
    {
        // A read of a wide head's own parameter goes through the tier's lent index, and a nested body's captured
        // read through the owner walk and the owner's captured cells: neither scans, and neither allocates (the
        // owner walk's former `foreach` over each level's names boxed an enumerator per level).
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var plain = Names("p", 64);
        var owner = new Algorithm.User(null, plain.Select(static n => (ParameterPattern)new CaptureParameterPattern(n)).ToArray(), [], [], [new Expr.Num(1)]);
        var minted = Evaluator.Concat(plain.Select((n, i) => (n, Cell(i))).ToArray(), []);
        var entered = Evaluator.EnterAlgorithmBody(owner, Evaluator.EvalCtx.Empty.WithNeedEnv(minted), [], parameterNames: plain, invoked: true);
        var inner = new Algorithm.User(entered.HeadScope, [], [], [], [new Expr.Num(2)]);
        var nested = Evaluator.EnterAlgorithmBody(inner, entered, []);
        _ = Evaluator.ParameterNeedCell("p63", entered);
        _ = Evaluator.ParameterNeedCell("p63", nested);

        var found = 0;
        var before = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < 100; i++)
        {
            foreach (var name in plain)
            {
                if (Evaluator.ParameterNeedCell(name, entered) is not null) found++;
                if (Evaluator.ParameterNeedCell(name, nested) is not null) found++;
            }
        }
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
        Assert.Equal(2 * 100 * plain.Length, found);
        Assert.Equal(0, allocated);
        GcIsolatedAllocation.Complete();
    }

    // ── Programs on every route ─────────────────────────────────────────────────────────────────────

    private static string Describe((EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget) run)
    {
        var (result, budget) = run;
        var outcome = result.IsOk
            ? $"ok {InvocationRouteCorpus.Value(result.Value.Value)} n={result.Value.EmittedCount}"
            : $"err {result.Error.Code} | {KatLangError.FromEvalError(result.Error).Message.Replace("\n", " / ", StringComparison.Ordinal)} @{result.Error.Span}";
        return $"{outcome}\tsteps={budget.ConsumedSteps}\tcheckpoints={budget.ConsumedExpressionCheckpoints}";
    }

    /// <summary>
    /// The plain value entry, the counted generic and optimized routes and the async twin, which must agree on the
    /// outcome and on the counted routes' steps and checkpoints; returns the counted outcome.
    /// </summary>
    private static async Task<string> ObserveAllRoutes(Func<(Expr Program, HostOperations? Operations)> build)
    {
        var (plain, generic, optimized, twin) = await RouteOutcomes(build);
        Assert.Equal(generic, optimized);
        Assert.Equal(generic, twin);
        Assert.Equal(generic.StartsWith("ok ", StringComparison.Ordinal), plain.IsOk);
        if (plain.IsOk)
            Assert.StartsWith($"ok {InvocationRouteCorpus.Value(plain.Value)} n=", generic, StringComparison.Ordinal);
        else
            Assert.StartsWith($"err {plain.Error.Code} ", generic, StringComparison.Ordinal);
        return generic;
    }

    // One run per route: the plain value entry, the counted generic and optimized routes, the async twin.
    private static async Task<(EvalResult<Result> Plain, string Generic, string Optimized, string Twin)> RouteOutcomes(
        Func<(Expr Program, HostOperations? Operations)> build)
    {
        var (plainProgram, plainOperations) = build();
        var plain = Evaluator.Run(plainProgram, new KatLang.Evaluation.Caching.RunScopedZeroArgPropertyResultCache(), enableLoopOptimization: true, loopDiagnostics: null,
            enableSequencePipelineOptimization: true, sequenceDiagnostics: null, hostOperations: plainOperations);
        var (genericProgram, genericOperations) = build();
        var generic = Describe(Evaluator.RunCountedObserved(genericProgram, enableOptimizations: false, hostOperations: genericOperations));
        var (optimizedProgram, optimizedOperations) = build();
        var optimized = Describe(Evaluator.RunCountedObserved(optimizedProgram, enableOptimizations: true, hostOperations: optimizedOperations));
        var (twinProgram, twinOperations) = build();
        var twin = Describe(await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            twinProgram, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache(), hostOperations: twinOperations)));
        return (plain, generic, optimized, twin);
    }

    private static Task<string> ObserveSource(string source)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        return ObserveAllRoutes(() => (new Expr.AlgorithmExpr(root), null));
    }

    private static string List(string prefix, int from, int to) => string.Join(", ", Enumerable.Range(from, to - from + 1).Select(i => prefix + i));

    private static string Weighted(string prefix, int width) => "sum([" + string.Join(", ", Enumerable.Range(1, width).Select(i => $"{i} * {prefix}{i}")) + "])";

    private static long Sum(int width, Func<int, long> term) => Enumerable.Range(1, width).Sum(term);

    public static TheoryData<int> ProgramWidths => new() { 1, 2, 8, 17, Threshold - 1, Threshold, Threshold + 1, 64, 130 };

    [Theory]
    [MemberData(nameof(ProgramWidths))]
    public async Task OwnReads_EveryParameterAndOneRepeatedly_RepeatedCalls_OnAllRoutes(int width)
    {
        var source = $"F({List("p", 1, width)}) = {Weighted("p", width)}\n"
            + $"L({List("p", 1, width)}) = sum([{string.Join(", ", Enumerable.Repeat("p" + width, width))}]) + p1\n"
            + $"F({List("", 1, width)})\n"
            + $"range(1, 3).map{{F({string.Join(", ", Enumerable.Repeat("n", width))})}}.sum\n"
            + $"L({List("", 1, width)})\n";
        var outcome = await ObserveSource(source);
        Assert.StartsWith($"ok ({Sum(width, i => (long)i * i)}, {6L * width * (width + 1) / 2}, {(long)width * width + 1}) n=", outcome, StringComparison.Ordinal);
    }

    [Theory]
    [MemberData(nameof(ProgramWidths))]
    public async Task CapturedReads_ThroughALocalProperty_AndANestedCallee_OnAllRoutes(int width)
    {
        // S reads every parameter of its owner (captured reads through the owner's activation); the nested F shadows
        // the first `width` names of G's and reads G's last parameter, which it does not shadow.
        var outer = width + 8;
        var source = $"C({List("p", 1, width)}) = {{\n  S = {Weighted("p", width)}\n  S + p1\n}}\n"
            + $"G({List("x", 1, outer)}) = {{\n"
            + $"  F({List("x", 1, width)}, {List("y", 1, width)}) = {Weighted("x", width)} + 1000 * {Weighted("y", width)} + 1000000 * x{outer}\n"
            + $"  F({string.Join(", ", Enumerable.Range(1, width).Select(i => $"x{i} + 100"))}, {List("x", 1, width)})\n}}\n"
            + $"C({List("", 1, width)})\n"
            + $"G({List("", 1, outer)})\n";
        var outcome = await ObserveSource(source);
        var captured = Sum(width, i => (long)i * i) + 1;
        var nested = Sum(width, i => (long)i * (i + 100)) + 1000 * Sum(width, i => (long)i * i) + 1_000_000L * outer;
        Assert.StartsWith($"ok ({captured}, {nested}) n=", outcome, StringComparison.Ordinal);
    }

    [Theory]
    [MemberData(nameof(ProgramWidths))]
    public async Task ForwardedRecursiveAndClauseFamilyFrames_RebindByPosition_OnAllRoutes(int width)
    {
        // G forwards its parameters rotated; R and the family Q rotate them five times through recursion.
        const int rounds = 5;
        var rotated = string.Join(", ", Enumerable.Range(2, width - 1).Select(i => "p" + i).Append("p1"));
        var source = $"F({List("p", 1, width)}) = {Weighted("p", width)}\n"
            + $"G({List("p", 1, width)}) = F(p{width}{(width > 1 ? ", " + List("p", 1, width - 1) : "")})\n"
            + $"R(k, {List("p", 1, width)}) = if(k == 0, {Weighted("p", width)}, R(k - 1, {rotated}))\n"
            + $"Q(0, {List("p", 1, width)}) = {Weighted("p", width)}\n"
            + $"Q(k, {List("p", 1, width)}) = Q(k - 1, {rotated})\n"
            + $"G({List("", 1, width)})\n"
            + $"R({rounds}, {List("", 1, width)})\n"
            + $"Q({rounds}, {List("", 1, width)})\n";
        var outcome = await ObserveSource(source);
        var forwarded = Sum(width, i => i * (long)(i == 1 ? width : i - 1));
        var recursive = Sum(width, i => i * (long)((i - 1 + rounds) % width + 1));
        Assert.StartsWith($"ok ({forwarded}, {recursive}, {recursive}) n=", outcome, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(2)]
    [InlineData(Threshold)]
    [InlineData(64)]
    public async Task ARepeatedName_KeepsNeed04_InAWideHead_OnAllRoutes(int width)
    {
        var head = $"F({List("p", 1, width)}, p1) = p1 + 1000 * p{width}\n";
        Assert.StartsWith($"ok {1 + 1000L * width} n=", await ObserveSource(head + $"F({List("", 1, width)}, 1)\n"), StringComparison.Ordinal);
        var refused = await ObserveSource(head + $"F({List("", 1, width)}, 2)\n");
        Assert.StartsWith("err ArityMismatch", refused, StringComparison.Ordinal);
        Assert.Contains("repeated parameter 'p1' requires equal arguments", refused, StringComparison.Ordinal);
    }

    [Fact]
    public async Task TheDepthAndStackLimits_RefuseTheSameRecursion_WhateverTheFrameWidth()
    {
        // The synchronous routes run on a thread whose stack outlasts the depth limit (on a test thread a Debug
        // build can exhaust its stack first, which the async twin, hopping to fresh stacks, never does), so every
        // route meets the same limit at the same call, and no route's report depends on the frame's width.
        static string Program(int width, int depth)
            => $"D(k, {List("p", 1, width)}) = if(k == 0, p1, D(k - 1, {List("p", 1, width)}))\nD({depth}, {List("", 1, width)})\n";
        static string Code(string outcome) => outcome.Split(" | ")[0].Split(" n=")[0];
        static async Task<string[]> Codes(string source)
        {
            var root = SourceProvenance.ParseValid(source).Root;
            Expr Program() => new Expr.AlgorithmExpr(root);
            string[] synchronous = [];
            Exception? failure = null;
            var thread = new Thread(() =>
            {
                try
                {
                    var plain = Evaluator.Run(Program());
                    synchronous = [plain.IsOk ? "ok " + InvocationRouteCorpus.Value(plain.Value) : "err " + plain.Error.Code,
                        Code(Describe(Evaluator.RunCountedObserved(Program(), enableOptimizations: false))),
                        Code(Describe(Evaluator.RunCountedObserved(Program(), enableOptimizations: true)))];
                }
                catch (Exception exception)
                {
                    failure = exception;
                }
            }, maxStackSize: 64 * 1024 * 1024);
            thread.Start();
            thread.Join();
            Assert.Null(failure);
            var twin = Code(Describe(await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
                Program(), zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache()))));
            return [.. synchronous, twin];
        }

        Assert.Equal(["ok 1", "ok 1", "ok 1", "ok 1"], await Codes(Program(1, 20)));
        Assert.Equal(["ok 1", "ok 1", "ok 1", "ok 1"], await Codes(Program(64, 20)));
        string[] refused = ["err EvaluationDepthExceeded", "err EvaluationDepthExceeded", "err EvaluationDepthExceeded", "err EvaluationDepthExceeded"];
        Assert.Equal(refused, await Codes(Program(1, 400)));
        Assert.Equal(refused, await Codes(Program(64, 400)));
    }

    [Theory]
    [InlineData(3)]
    [InlineData(Threshold + 8)]
    public async Task AHostEditOfAWideStoredHead_BetweenTwoCallsOfOneRun_IsObservedByTheSecondCall(int width)
    {
        // F(1, …, width), Edit(), F(1, …, width): the host swaps the first two names of F's caller-owned head
        // between the calls. Nothing derived from one call's head — its names, indexes or tier — serves the next.
        (Expr Program, HostOperations? Operations) Build()
        {
            var head = Names("p", width).Select(static n => (ParameterPattern)new CaptureParameterPattern(n)).ToList();
            var edit = HostOperation.Create("SwapHead", (_, _) =>
            {
                (head[0], head[1]) = (head[1], head[0]);
                return new Result.Atom(0);
            });
            Expr body = new Expr.Binary(BinaryOp.Add,
                new Expr.Binary(BinaryOp.Mul, new Expr.Param("p0"), new Expr.Num(10)),
                new Expr.Binary(BinaryOp.Add, new Expr.Param("p1"), new Expr.Binary(BinaryOp.Mul, new Expr.Param("p" + (width - 1)), new Expr.Num(1000))));
            var callee = new Algorithm.User(null, head, [], [], [body]);
            Expr Call() => new Expr.Call(new Expr.Resolve("F"), OutputBundle.TakeOwnership(Enumerable.Range(1, width).Select(static i => (Expr)new Expr.Num(i)).ToArray()));
            var program = new Expr.AlgorithmExpr(new Algorithm.User(
                null, [], [], [new Property("F", callee)], [Call(), new Expr.NativeCall(edit.NativeName, []), Call()]));
            return (program, HostOperations.Create(edit));
        }

        var outcome = await ObserveAllRoutes(Build);
        Assert.StartsWith($"ok ({12 + 1000L * width}, 0, {21 + 1000L * width}) n=", outcome, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("plain")]
    [InlineData("counted")]
    [InlineData("async")]
    public async Task WideForwarding_OnlyDemandsTheLastArgument_BeforeCancellation(string route)
    {
        using var cancellation = new CancellationTokenSource();
        var seen = new List<string>();
        var operations = HostOperations.Create(
            HostOperation.Create("Unused", (_, _) => { seen.Add("unused"); return new Result.Atom(1); }),
            HostOperation.Create("Stop", (_, _) => { seen.Add("stop"); cancellation.Cancel(); return new Result.Atom(2); }));
        var names = List("p", 1, Threshold);
        var arguments = string.Join(", ", Enumerable.Repeat("Unused()", Threshold - 1).Append("Stop()"));
        var source = $"Read({names}) = p{Threshold} + p1\nForward({names}) = Read({names})\nForward({arguments})";
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));
        var program = new Expr.AlgorithmExpr(parsed.Root);
        var token = cancellation.Token;
        var error = route switch
        {
            "plain" => Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.Run(program, operations, null, null, token)),
            "counted" => Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(program, hostOperations: operations, cancellationToken: token)),
            "async" => await Assert.ThrowsAnyAsync<OperationCanceledException>(() => AsyncEvaluationHarness.Complete(
                Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache(),
                    hostOperations: operations, cancellationToken: token))),
            _ => throw new ArgumentOutOfRangeException(nameof(route)),
        };
        Assert.Equal(token, error.CancellationToken);
        Assert.Equal(["stop"], seen);
    }
}

// Both frame preparation tests count element visits through indexing and enumeration.
internal sealed class FrameReadCountingList<T>(IReadOnlyList<T> items) : IReadOnlyList<T>
{
    public int Reads { get; set; }
    public int Count => items.Count;
    public T this[int index]
    {
        get
        {
            Reads++;
            return items[index];
        }
    }

    public IEnumerator<T> GetEnumerator()
    {
        for (var i = 0; i < Count; i++)
            yield return this[i];
    }

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}
