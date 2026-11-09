using System.Numerics;
using System.Globalization;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// The run-local clause-family preparation memo (SEC-03 follow-up, November 2026): a family's
/// duplicate-head verdict and translated heads are decided ONCE per run per branch-list reference
/// (<c>Evaluator.NeedFamilyPreparationCache</c>, held by the run's <see cref="EvaluationBudget"/>),
/// and the runtime duplicate index observes the run's cancellation token. Nothing observable
/// changes: verdicts, errors, clause order, resource counters. Counts are read from the passive
/// <see cref="EvaluationObservations.ClauseFamilyPreparationCount"/>; cancellation is placed through
/// <see cref="EvaluationObservations.FamilyDuplicateIndex"/>'s checkpoint hook.
/// </summary>
public class ClauseFamilyPreparationTests
{
    public enum Route { Generic, Optimized, AsyncTwin }

    public static TheoryData<Route> Routes => new() { Route.Generic, Route.Optimized, Route.AsyncTwin };

    private static readonly Route[] AllRoutes = [Route.Generic, Route.Optimized, Route.AsyncTwin];

    private const string Fib = "Fib(0) = 0\nFib(1) = 1\nFib(n) = Fib(n - 1) + Fib(n - 2)\nFib(15)";

    private static Expr Program(string source) => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private static async Task<(EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget)> RunOn(
        Route route, Expr expr, EvaluationObservations observations, CancellationToken token = default)
    {
        if (route is Route.AsyncTwin)
        {
            return await Evaluator.RunCountedObservedAsync(
                expr,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                observations: observations,
                cancellationToken: token);
        }

        return Evaluator.RunCountedObserved(
            expr,
            enableOptimizations: route is Route.Optimized,
            observations: observations,
            cancellationToken: token);
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    private static int Dispatches(ClauseAttemptObservations attempts)
        => attempts.Attempts.Select(static a => a.Dispatch).Distinct().Count();

    private static string Trace(ClauseAttemptObservations attempts)
        => string.Join(" ", attempts.Attempts.Select(static a => $"{a.Dispatch}:{a.Clause}:{a.Outcome}"));

    // ── host-built ASTs ─────────────────────────────────────────────────────────

    private static Algorithm.User Body(int value)
        => new(Parent: null, ParameterPatterns: [], Opens: [], Properties: [], Output: [new Expr.Num(value)]);

    private static CondBranch Branch(Pattern head, int value) => new(head, Body(value));

    private static Pattern Params(params Pattern[] items) => new Pattern.SequenceValue(items);

    private static Pattern.Bind B(string name) => new(name);

    private static Pattern.LitInt N(string text)
        => new(Decimal128.Parse(text, NumberStyles.Float, CultureInfo.InvariantCulture));

    private static Expr.AlgorithmExpr HostProgram(IReadOnlyList<Property> properties, params Expr[] output)
        => new(new Algorithm.User(Parent: null, ParameterPatterns: [], Opens: [], Properties: properties, Output: output));

    private static Expr Call(string name, params Expr[] args)
        => new Expr.Call(new Expr.Resolve(name), new OutputBundle(args));

    private static Expr Num(int value) => new Expr.Num(value);

    private static Expr List(params Expr[] items) => new Expr.ListLiteral(new OutputBundle(items));

    // ── 1. one preparation per run for a recursive family ───────────────────────

    // Resource counters of Fib(15) measured on the pre-memo baseline (HEAD 3fb26190) on each route.
    private static (long Steps, long Checkpoints, long Structural, int PeakDepth, long Items, long Chars) BaselineCounters(Route route)
        => route switch
        {
            Route.Generic => FibGeneric,
            Route.Optimized => FibOptimized,
            _ => FibAsync,
        };

    private static readonly (long, long, long, int, long, long) FibGeneric = (1977, 18737, 0, 15, 0, 0);
    private static readonly (long, long, long, int, long, long) FibOptimized = (1977, 18737, 0, 15, 0, 0);
    private static readonly (long, long, long, int, long, long) FibAsync = (1977, 18737, 0, 15, 0, 0);

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task RecursiveFamily_IsPreparedOncePerRun_AcrossAllItsCalls_WithBaselineCounters(Route route)
    {
        var attempts = new ClauseAttemptObservations();
        var observations = new EvaluationObservations { ClauseAttempts = attempts };
        var (result, budget) = await RunOn(route, Program(Fib), observations);

        Assert.False(result.IsError, result.IsError ? $"{route}: {result.Error}" : null);
        Assert.Equal(new Result.Atom(610), result.Value.Value, Result.ValueComparer);
        Assert.Equal(1973, Dispatches(attempts));
        Assert.Equal(1, observations.ClauseFamilyPreparationCount);
        Assert.Equal(
            BaselineCounters(route),
            (budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.ConsumedStructuralWorkUnits,
                budget.PeakDepth, budget.MaterializedItems, budget.MaterializedStringChars));
    }

    [Fact]
    public async Task EveryRun_PreparesAfresh()
    {
        var expr = Program(Fib);
        for (var run = 0; run < 3; run++)
        {
            var observations = new EvaluationObservations();
            var (result, _) = await RunOn(Route.Generic, expr, observations);
            Assert.False(result.IsError);
            Assert.Equal(1, observations.ClauseFamilyPreparationCount);
        }
    }

    // ── 2. wired copies share one entry ─────────────────────────────────────────

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task WiredCopies_FromSeveralScopes_AndThroughAnAlias_ShareOnePreparation(Route route)
    {
        // F is looked up from the root, from inside Outer's activation, and through the alias G:
        // every lookup returns a fresh wired copy, all sharing F's one branch list.
        const string source = "F(0) = 1\nF(x) = x\nOuter(n) = F(n) + F(n + 1)\nG = F\nOuter(0) + F(3) + G(4)";
        var attempts = new ClauseAttemptObservations();
        var observations = new EvaluationObservations { ClauseAttempts = attempts };
        var (result, _) = await RunOn(route, Program(source), observations);

        Assert.False(result.IsError, result.IsError ? $"{route}: {result.Error}" : null);
        Assert.Equal(new Result.Atom(9), result.Value.Value, Result.ValueComparer);
        Assert.Equal(4, Dispatches(attempts));
        Assert.True(attempts.Attempts.Select(static a => a.Family).Distinct(ReferenceEqualityComparer.Instance).Count() > 1,
            "the calls should reach distinct wired copies of the family");
        Assert.Equal(1, observations.ClauseFamilyPreparationCount);
    }

    // ── 3. a replaced list is its own entry ─────────────────────────────────────

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task ReplacedBranchList_InOneRun_GetsItsOwnPreparationAndVerdict(Route route)
    {
        var family = new Algorithm.Conditional(Parent: null, Opens: [],
            Branches: [Branch(N("0"), 10), Branch(B("x"), 20)]);
        // Same declaration identity, replaced list: x and y are match-equivalent.
        var duplicate = family with { Branches = [Branch(N("0"), 10), Branch(B("x"), 20), Branch(B("y"), 30)] };
        Assert.False(family.HasDuplicateBranchPatterns());
        Assert.True(duplicate.HasDuplicateBranchPatterns());

        // F alone succeeds.
        var fineObservations = new EvaluationObservations();
        var (fine, _) = await RunOn(route,
            HostProgram([new Property("F", family, IsPublic: true), new Property("G", duplicate, IsPublic: true)], Call("F", Num(1))),
            fineObservations);
        Assert.False(fine.IsError, fine.IsError ? $"{route}: {fine.Error}" : null);
        Assert.Equal(new Result.Atom(20), fine.Value.Value, Result.ValueComparer);
        Assert.Equal(1, fineObservations.ClauseFamilyPreparationCount);

        // Both in one run: F's call matches, then G's call is the duplicate error.
        var attempts = new ClauseAttemptObservations();
        var observations = new EvaluationObservations { ClauseAttempts = attempts };
        var (both, _) = await RunOn(route,
            HostProgram([new Property("F", family, IsPublic: true), new Property("G", duplicate, IsPublic: true)],
                new Expr.Binary(BinaryOp.Add, Call("F", Num(1)), Call("G", Num(1)))),
            observations);
        Assert.True(both.IsError, $"{route}: expected the duplicate-branch error");
        Assert.IsType<EvalError.DuplicateBranchPattern>(Innermost(both.Error));
        Assert.Equal("1:0:NonMatch 1:1:Matched", Trace(attempts));
        Assert.Equal(2, observations.ClauseFamilyPreparationCount);
    }

    // ── 4. host edits between runs are observed ─────────────────────────────────

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task HostEditsOfACallerOwnedList_BetweenRuns_AreObserved(Route route)
    {
        var branches = new List<CondBranch> { Branch(N("0"), 10), Branch(B("x"), 20) };
        var family = new Algorithm.Conditional(Parent: null, Opens: [], Branches: branches);
        var expr = HostProgram([new Property("F", family, IsPublic: true)], Call("F", Num(5)));

        var (first, _) = await RunOn(route, expr, new EvaluationObservations());
        Assert.False(first.IsError, first.IsError ? $"{route}: {first.Error}" : null);
        Assert.Equal(new Result.Atom(20), first.Value.Value, Result.ValueComparer);

        branches.Add(Branch(B("y"), 30));
        var (second, _) = await RunOn(route, expr, new EvaluationObservations());
        Assert.True(second.IsError, $"{route}: the appended duplicate must be observed");
        Assert.IsType<EvalError.DuplicateBranchPattern>(Innermost(second.Error));

        branches.RemoveAt(branches.Count - 1);
        var (third, _) = await RunOn(route, expr, new EvaluationObservations());
        Assert.False(third.IsError, third.IsError ? $"{route}: {third.Error}" : null);
        Assert.Equal(new Result.Atom(20), third.Value.Value, Result.ValueComparer);
    }

    // ── 5. cancellation inside the first preparation ────────────────────────────

    private static Algorithm.Conditional LongStringFamily(int count, int length)
    {
        var branches = new List<CondBranch>(count);
        for (var i = 0; i < count; i++)
            branches.Add(Branch(new Pattern.LitString(i.ToString("D6", CultureInfo.InvariantCulture) + new string('k', length)), i));
        return new Algorithm.Conditional(Parent: null, Opens: [], Branches: branches);
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task Cancellation_InsideTheFirstPreparation_IsTheRunsToken_AndNothingRunsAfterwards(Route route)
    {
        const int cancelAt = 40;
        var family = LongStringFamily(1024, 6000);
        var expr = HostProgram([new Property("F", family, IsPublic: true)], Call("F", new Expr.StringLiteral("absent")));

        using var cts = new CancellationTokenSource();
        var index = new PatternComparisonObservations { CheckpointReached = ordinal => { if (ordinal == cancelAt) cts.Cancel(); } };
        var attempts = new ClauseAttemptObservations();
        var observations = new EvaluationObservations { ClauseAttempts = attempts, FamilyDuplicateIndex = index };

        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => RunOn(route, expr, observations, cts.Token));
        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.Equal(cancelAt, index.CancellationCheckpointCount);
        Assert.True(index.CanonicalKeyCount < family.Branches.Count, $"{route}: the index ran to completion");
        Assert.Empty(attempts.Attempts);
        Assert.Equal(0, observations.ClauseFamilyPreparationCount);

        // Uncancelled, the same family is distinct, so the call is an ordinary no-match.
        var completeIndex = new PatternComparisonObservations();
        var completeObservations = new EvaluationObservations { FamilyDuplicateIndex = completeIndex };
        var (complete, _) = await RunOn(route, expr, completeObservations);
        Assert.True(complete.IsError);
        Assert.IsType<EvalError.NoMatchingBranch>(Innermost(complete.Error));
        Assert.Equal(family.Branches.Count, completeIndex.CanonicalKeyCount);
        Assert.True(completeIndex.CancellationCheckpointCount > cancelAt);
        Assert.Equal(1, completeObservations.ClauseFamilyPreparationCount);
    }

    // ── 6. equivalence with the public verdict and the written clause order ─────

    public static TheoryData<string> EquivalenceCases => new(EquivalenceFamilies.Keys);

    // Each case: the host family, the call's arguments, and the expected outcome (null = duplicate).
    private static readonly Dictionary<string, (Func<IReadOnlyList<CondBranch>> Branches, Func<Expr[]> Args, int? Expected)> EquivalenceFamilies = new()
    {
        ["alpha-renamed binders"] = (() => [Branch(Params(B("a"), B("b")), 1), Branch(Params(B("x"), B("y")), 2)], () => [Num(1), Num(2)], null),
        ["repeated binders, equal"] = (() => [Branch(Params(B("v"), B("v")), 1), Branch(Params(B("a"), B("b")), 2)], () => [Num(3), Num(3)], 1),
        ["repeated binders, unequal"] = (() => [Branch(Params(B("v"), B("v")), 1), Branch(Params(B("a"), B("b")), 2)], () => [Num(3), Num(4)], 2),
        ["repeated binders, renamed"] = (() => [Branch(Params(B("v"), B("v")), 1), Branch(Params(B("w"), B("w")), 2)], () => [Num(3), Num(3)], null),
        ["NaN literals"] = (() => [Branch(N("NaN"), 1), Branch(N("NaN"), 2)], () => [Num(1)], null),
        ["signed zeros"] = (() => [Branch(N("0"), 1), Branch(N("-0"), 2)], () => [Num(0)], null),
        ["quantum-differing literals"] = (() => [Branch(N("1.5"), 1), Branch(N("1.50"), 2)], () => [new Expr.Num(Decimal128.Parse("1.5", CultureInfo.InvariantCulture))], null),
        ["distinct literals"] = (() => [Branch(N("1"), 1), Branch(N("2"), 2), Branch(B("x"), 3)], () => [Num(2)], 2),
        ["list versus binder"] = (() => [Branch(new Pattern.ListValue([B("a")]), 1), Branch(B("a"), 2)], () => [Num(5)], 2),
        ["list matched"] = (() => [Branch(new Pattern.ListValue([B("a")]), 1), Branch(B("a"), 2)], () => [List(Num(5))], 1),
        ["list versus binder parameter"] = (() => [Branch(Params(new Pattern.ListValue([B("a")]), B("b")), 1), Branch(Params(B("a"), B("b")), 2)], () => [Num(1), Num(2)], 2),
        ["list parameter matched"] = (() => [Branch(Params(new Pattern.ListValue([B("a")]), B("b")), 1), Branch(Params(B("a"), B("b")), 2)], () => [List(Num(1)), Num(2)], 1),
        ["sequence versus list kinds"] = (() => [Branch(new Pattern.ListValue([new Pattern.SequenceValue([B("a"), B("b")])]), 1),
            Branch(new Pattern.ListValue([new Pattern.ListValue([B("a"), B("b")])]), 2)], () => [List(List(Num(1), Num(2)))], 2),
        ["nested structure, renamed"] = (() => [Branch(new Pattern.ListValue([B("a"), new Pattern.ListValue([B("b")])]), 1),
            Branch(new Pattern.ListValue([B("x"), new Pattern.ListValue([B("y")])]), 2)], () => [List(Num(1), List(Num(2)))], null),
        ["nested structure, distinct"] = (() => [Branch(new Pattern.ListValue([B("a"), new Pattern.ListValue([B("b")])]), 1),
            Branch(new Pattern.ListValue([B("a"), B("b")]), 2)], () => [List(Num(1), Num(2))], 2),
    };

    [Theory]
    [MemberData(nameof(EquivalenceCases))]
    public async Task HostFamilies_DecideLikeThePublicVerdict_AndSelectTheWrittenClause_OnEveryRoute(string name)
    {
        var (branches, args, expected) = EquivalenceFamilies[name];
        var family = new Algorithm.Conditional(Parent: null, Opens: [], Branches: branches());
        Assert.Equal(expected is null, family.HasDuplicateBranchPatterns());
        foreach (var route in AllRoutes)
        {
            var observations = new EvaluationObservations();
            var (result, _) = await RunOn(route, HostProgram([new Property("F", family, IsPublic: true)], Call("F", args())), observations);
            if (expected is { } value)
            {
                Assert.False(result.IsError, result.IsError ? $"{name}/{route}: {result.Error}" : null);
                Assert.Equal(new Result.Atom(value), result.Value.Value, Result.ValueComparer);
            }
            else
            {
                Assert.True(result.IsError, $"{name}/{route}: expected the duplicate-branch error");
                Assert.IsType<EvalError.DuplicateBranchPattern>(Innermost(result.Error));
            }
            Assert.Equal(1, observations.ClauseFamilyPreparationCount);
        }
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task DuplicateVerdict_PrecedesTheArityDecision_OnEveryCall(Route route)
    {
        // No clause accepts three values, yet the duplicate verdict comes first, on every call.
        var family = new Algorithm.Conditional(Parent: null, Opens: [],
            Branches: [Branch(B("a"), 1), Branch(B("b"), 2)]);
        var attempts = new ClauseAttemptObservations();
        var observations = new EvaluationObservations { ClauseAttempts = attempts };
        var (result, _) = await RunOn(route, HostProgram([new Property("F", family, IsPublic: true)], Call("F", Num(1), Num(2), Num(3))), observations);
        Assert.True(result.IsError);
        Assert.IsType<EvalError.DuplicateBranchPattern>(Innermost(result.Error));
        Assert.Empty(attempts.Attempts);

        // Without the duplicate, the same supply is the first clause's ArityMismatch.
        var distinct = family with { Branches = [Branch(B("a"), 1), Branch(N("2"), 2)] };
        var (mismatch, _) = await RunOn(route, HostProgram([new Property("F", distinct, IsPublic: true)], Call("F", Num(1), Num(2), Num(3))), new EvaluationObservations());
        Assert.True(mismatch.IsError);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(mismatch.Error));
        Assert.Equal((1, 3), (arity.Expected, arity.Actual));
    }

    // ── 7. activation publishes binder names in written order ───────────────────

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task Activation_PublishesTheBindersInOrder_ToTheBodyAndAnInnerCapture(Route route)
    {
        // The body reads both binders in order, and an inner block captures them; an outer
        // property spelled like a binder is shadowed by the clause's own binding.
        const string source = "a = 100\nF(0, y) = y\nF(a, b) = {\n  Inner = a * 10 + b\n  Inner - b + a\n}\nF(3, 4), F(0, 7)";
        var observations = new EvaluationObservations();
        var (result, _) = await RunOn(route, Program(source), observations);
        Assert.False(result.IsError, result.IsError ? $"{route}: {result.Error}" : null);
        Assert.Equal([33m, 7m], result.Value.Value.ToAtoms().Select(static d => (decimal)d).ToArray());
        Assert.Equal(1, observations.ClauseFamilyPreparationCount);
    }
}
