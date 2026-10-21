using KatLang.Evaluation;
namespace KatLang.Tests;

/// <summary>
/// SEC-02-FU2 clause-attempt observations (<see cref="ClauseAttemptObservations"/>): which clauses a
/// family dispatch actually began binding. Outcome-only tests cannot see a dispatch that wrongly
/// continues past a terminal error, because the run's retained terminal error (Q-02) stops the later
/// clause at its first demand or checkpoint — the final error stays right and no effect runs. The
/// attempt trace makes that prohibited attempt itself visible.
/// </summary>
public partial class SharedValueGraphComplexityTests
{
    private static async Task<(EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget, ClauseAttemptObservations Attempts)> RunAttemptsOn(
        Route route,
        string source,
        EvaluationLimits? limits = null,
        HostOperations? hostOperations = null,
        Action<long>? beforeCharge = null,
        bool requireSuspension = true,
        CancellationToken token = default)
    {
        var attempts = new ClauseAttemptObservations();
        var observations = new EvaluationObservations
        {
            StructuralTraversal = new ValueTraversalObservations { BeforeStructuralWorkCharge = beforeCharge },
            ClauseAttempts = attempts,
        };
        var (result, budget, _) = await RunComparisonOn(route, source, limits, hostOperations, evaluation: observations, requireSuspension: requireSuspension, token: token);
        return (result, budget, attempts);
    }

    /// <summary>The trace as <c>dispatch:clause:outcome</c> entries, comparable across runs and routes.</summary>
    private static string Trace(ClauseAttemptObservations attempts)
        => string.Join(" ", attempts.Attempts.Select(static a => $"{a.Dispatch}:{a.Clause}:{a.Outcome}"));

    // ── C5/C6: a terminal refusal stops the dispatch at the refused clause ────────────────

    [Theory]
    [InlineData("F([W][0], [X][0])", "1:0:Matched", 0)]
    [InlineData("F([W][0], [Y][0])", "1:0:NonMatch 1:1:Matched", 1)]
    public async Task TerminalRefusal_IsTheRefusedClausesOwnOutcome_AndNoLaterClauseIsAttempted(
        string call, string unlimitedTrace, int unlimitedEffects)
    {
        // The second clause's head is two unique names: it binds without demanding anything, so a
        // dispatch that turned the refusal into the first clause's non-match would ATTEMPT and MATCH
        // it, and only its body's first checkpoint would stop on the retained terminal error.
        var source = LargeProgram("F(v, v) = 1\nF(a, b) = effect(1)\n" + call);
        foreach (var route in AllRoutes)
        {
            var log = new EffectLog();
            var (unlimited, budget, attempts) = await RunAttemptsOn(route, source, hostOperations: log.Operations());
            Assert.False(unlimited.IsError, unlimited.IsError ? $"{route}: {unlimited.Error}" : null);
            Assert.Equal(unlimitedTrace, Trace(attempts));
            Assert.Equal(unlimitedEffects, log.Calls);

            var structuralSteps = budget.ConsumedStructuralWorkUnits / EvaluationBudget.StructuralWorkUnitsPerStep;
            Assert.True(structuralSteps >= 4, $"{route}: {budget.ConsumedStructuralWorkUnits}");
            var refusedLog = new EffectLog();
            var (refused, _, refusedAttempts) = await RunAttemptsOn(
                route, source, new EvaluationLimits { MaxSteps = budget.ConsumedSteps - structuralSteps }, refusedLog.Operations());
            Assert.True(refused.IsError, $"{route}: expected the step limit");
            Assert.IsType<EvalError.EvaluationStepLimitExceeded>(Innermost(refused.Error));
            // Exactly the first clause was attempted, and its attempt ended in the refusal itself.
            Assert.Equal("1:0:Error", Trace(refusedAttempts));
            Assert.Equal([0], refusedAttempts.AttemptedClauses);
            Assert.Equal(0, refusedLog.Calls);
        }
    }

    [Fact]
    public async Task Cancellation_InsideAClausesComparison_LeavesItsAttemptPending_AndAttemptsNoOther()
    {
        foreach (var route in AllRoutes)
        {
            using var cts = new CancellationTokenSource();
            var log = new EffectLog();
            var attempts = new ClauseAttemptObservations();
            var observations = new EvaluationObservations
            {
                StructuralTraversal = new ValueTraversalObservations { BeforeStructuralWorkCharge = ordinal => { if (ordinal == 2) cts.Cancel(); } },
                ClauseAttempts = attempts,
            };
            var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => RunComparisonOn(
                route,
                LargeProgram("F(v, v) = 1\nF(a, b) = effect(1)\nF([W][0], [Y][0])"),
                hostOperations: log.Operations(),
                evaluation: observations,
                token: cts.Token));
            Assert.Equal(cts.Token, thrown.CancellationToken);
            Assert.Equal("1:0:Pending", Trace(attempts));
            Assert.Equal(0, log.Calls);
        }
    }

    // ── C7: ordinary first-match dispatch ────────────────────────────────────────────────

    public static TheoryData<string, string, object> OrdinaryDispatches => new()
    {
        // An earlier match: later clauses are never attempted.
        { "G(0) = 10\nG(n) = 20\nG(0)", "1:0:Matched", 10m },
        // A literal mismatch is the clause's non-match; the search continues.
        { "G(0) = 10\nG(n) = 20\nG(5)", "1:0:NonMatch 1:1:Matched", 20m },
        // Repeated names: equal agreement matches, unequal agreement is a non-match.
        { "F(v, v) = 1\nF(a, b) = 2\nF(3, 3)", "1:0:Matched", 1m },
        { "F(v, v) = 1\nF(a, b) = 2\nF(3, 4)", "1:0:NonMatch 1:1:Matched", 2m },
        { "F(v, v) = 1\nF(a, b) = 2\nF([1, [2]], [1, [2]])", "1:0:Matched", 1m },
        { "F(v, v) = 1\nF(a, b) = 2\nF([1, [2]], [1, [3]])", "1:0:NonMatch 1:1:Matched", 2m },
        // Two calls of one family are two dispatches, each with its own attempts.
        { "G(0) = 10\nG(n) = 20\nG(0) + G(1)", "1:0:Matched 2:0:NonMatch 2:1:Matched", 30m },
        // Nested: the outer clause's literal demands its argument, whose own dispatch runs inside
        // the outer attempt; the outer clause then fails and the next outer clause is attempted.
        { "Inner(0) = 0\nInner(n) = 1\nOuter(0) = 100\nOuter(n) = 200\nOuter(Inner(5))",
            "1:0:NonMatch 2:0:NonMatch 2:1:Matched 1:1:Matched", 200m },
        // A family loop step dispatches once per round.
        { "S(0) = 0\nS(n) = n - 1\nS(3).repeat(2)", "1:0:NonMatch 1:1:Matched 2:0:NonMatch 2:1:Matched", 1m },
    };

    [Theory]
    [MemberData(nameof(OrdinaryDispatches))]
    public async Task OrdinaryDispatch_AttemptsClausesInWrittenOrder_UntilTheFirstMatch_OnEveryRoute(
        string source, string expectedTrace, object expected)
    {
        foreach (var route in AllRoutes)
        {
            // These programs read no property, so the suspending twin has nothing to suspend on.
            var (result, _, attempts) = await RunAttemptsOn(route, source, requireSuspension: false);
            Assert.False(result.IsError, result.IsError ? $"{route}: {result.Error}" : null);
            Assert.Equal(new Result.Atom((decimal)expected), result.Value.Value, Result.ValueComparer);
            Assert.Equal(expectedTrace, Trace(attempts));
        }
    }

    [Fact]
    public async Task NestedDispatches_RecordTheirOwnFamilies()
    {
        var (_, _, attempts) = await RunAttemptsOn(
            Route.Generic, "Inner(0) = 0\nInner(n) = 1\nOuter(0) = 100\nOuter(n) = 200\nOuter(Inner(5))");
        var trace = attempts.Attempts;
        Assert.Equal(4, trace.Count);
        Assert.NotSame(trace[0].Family, trace[1].Family);
        Assert.Same(trace[1].Family, trace[2].Family);
        Assert.Same(trace[0].Family, trace[3].Family);
    }

    [Fact]
    public async Task NestedDispatches_KeepTheirAttemptsAcrossAGenuineAsyncSuspension()
    {
        var (result, _, attempts) = await RunAttemptsOn(Route.SuspendingTwin,
            "A = 5\nInner(0) = 0\nInner(n) = 1\nOuter(0) = 100\nOuter(n) = 200\nOuter(Inner(A))");
        Assert.False(result.IsError);
        Assert.Equal(new Result.Atom(200), result.Value.Value, Result.ValueComparer);
        Assert.Equal("1:0:NonMatch 2:0:NonMatch 2:1:Matched 1:1:Matched", Trace(attempts));
        var trace = attempts.Attempts;
        Assert.Same(trace[0].Family, trace[3].Family);
        Assert.Same(trace[1].Family, trace[2].Family);
        Assert.NotSame(trace[0].Family, trace[1].Family);
    }

    [Theory]
    // A required evaluation error in a clause's demand ends the search with that error.
    [InlineData("G(0) = 10\nG(n) = 20\nG(1 + true)")]
    // A repeated name's demanded contribution failing is the attempt's error, not its non-match.
    [InlineData("F(v, v) = 1\nF(a, b) = 2\nF(1, 1 + true)")]
    public async Task RequiredEvaluationError_EndsTheSearch_AtTheAttemptingClause(string source)
    {
        foreach (var route in AllRoutes)
        {
            // These programs read no property, so the suspending twin has nothing to suspend on.
            var (result, _, attempts) = await RunAttemptsOn(route, source, requireSuspension: false);
            Assert.True(result.IsError, $"{route}: expected an error");
            Assert.IsType<EvalError.TypeMismatch>(Innermost(result.Error));
            Assert.Equal("1:0:Error", Trace(attempts));
        }
    }

    [Fact]
    public async Task FamilyLevelDecisions_AreNotAttempts()
    {
        // No clause accepts the supply count: the family's ArityMismatch, decided before any clause.
        // (Clauses of one validated family share one top-level arity and collect nothing, so the
        // drivers' per-clause cardinality skip never differs between clauses of a written family.)
        var (arity, _, arityAttempts) = await RunAttemptsOn(Route.Generic, "H(a, b) = 2\nH(0, b) = 1\nH(1, 2, 3)");
        Assert.True(arity.IsError);
        Assert.IsType<EvalError.ArityMismatch>(Innermost(arity.Error));
        Assert.Empty(arityAttempts.Attempts);

        // An empty family (host-built; no source spells one) refuses every supply without an attempt.
        static Algorithm.User Body(params Expr[] output) => new(null, [], [], [], output);
        var empty = new Algorithm.Conditional(Parent: null, Opens: [], Branches: []);
        var attempts = new ClauseAttemptObservations();
        var (result, _) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(Body(new Expr.Call(new Expr.AlgorithmExpr(empty), [new Expr.Num(1)]))),
            observations: new EvaluationObservations { ClauseAttempts = attempts });
        Assert.True(result.IsError);
        Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
        Assert.Empty(attempts.Attempts);
    }

    [Theory]
    [InlineData("G(0) = 0\nG(1) = 1\nG(2)", "1:0:NonMatch 1:1:NonMatch")]
    [InlineData("Inner(0) = 0\nInner(1) = 1\nOuter(0) = 10\nOuter(n) = 20\nOuter(Inner(2))",
        "1:0:Error 2:0:NonMatch 2:1:NonMatch")]
    public async Task UnmatchedDispatch_KeepsItsOwnOutcomes_WhenItsFailureReachesAParentAttempt(
        string source, string expectedTrace)
    {
        foreach (var route in AllRoutes)
        {
            var (result, _, attempts) = await RunAttemptsOn(route, source, requireSuspension: false);
            Assert.True(result.IsError);
            Assert.IsType<EvalError.NoMatchingBranch>(Innermost(result.Error));
            Assert.Equal(expectedTrace, Trace(attempts));
        }
    }

    // ── C8 / infrastructure: run-scoped, passive, isolated ──────────────────────────────

    [Fact]
    public async Task ClauseAttemptObservation_IsPassive_RunScoped_AndIsolatedBetweenParallelRuns()
    {
        const string source = "Inner(0) = 0\nInner(n) = 1\nOuter(0) = 100\nOuter(n) = 200\nOuter(Inner(5)) + Outer(Inner(0))";
        var expr = ParseValidWith(source, operations: null);

        // Observation changes neither result nor accounting; a run without it records nothing.
        var (plain, plainBudget) = Evaluator.RunCountedObserved(expr);
        var (unobserved, unobservedBudget) = Evaluator.RunCountedObserved(expr, observations: new EvaluationObservations());
        var first = new ClauseAttemptObservations();
        var (observed, observedBudget) = Evaluator.RunCountedObserved(expr, observations: new EvaluationObservations { ClauseAttempts = first });
        Assert.Equal(plain.Value.Value, observed.Value.Value, Result.ValueComparer);
        Assert.Equal(plain.Value.Value, unobserved.Value.Value, Result.ValueComparer);
        Assert.Equal(plainBudget.ConsumedSteps, observedBudget.ConsumedSteps);
        Assert.Equal(plainBudget.ConsumedSteps, unobservedBudget.ConsumedSteps);

        var expected = Trace(first);
        Assert.Equal("1:0:NonMatch 2:0:NonMatch 2:1:Matched 1:1:Matched 3:0:Matched 4:0:Matched", expected);

        // A fresh run starts empty: the same program records the same trace, never an accumulation.
        var second = new ClauseAttemptObservations();
        Evaluator.RunCountedObserved(expr, observations: new EvaluationObservations { ClauseAttempts = second });
        Assert.Equal(expected, Trace(second));

        var traces = await Task.WhenAll(Enumerable.Range(0, 8).Select(_ => Task.Run(() =>
        {
            var own = new ClauseAttemptObservations();
            Evaluator.RunCountedObserved(expr, observations: new EvaluationObservations { ClauseAttempts = own });
            return Trace(own);
        })));
        Assert.All(traces, trace => Assert.Equal(expected, trace));
        Assert.Equal(expected, Trace(first));
    }
}
