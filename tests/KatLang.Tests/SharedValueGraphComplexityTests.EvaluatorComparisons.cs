using System.Numerics;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;
namespace KatLang.Tests;

/// <summary>
/// SEC-02-FU: every evaluator-owned structural comparison — <c>==</c>/<c>!=</c> and NEED-04's
/// repeated-name agreement (ordinary calls and clause families alike) — runs through the SEC-02
/// operation comparer whenever it has structural or string work to do, so its walk charges the run's
/// budget and observes host cancellation exactly like <c>contains</c> and <c>distinct</c>; and string
/// payload is charged by length in every operation walk. Before it, <c>==</c> and the binder used the
/// context-free <see cref="Result.ValueComparer"/>: a deep or wide comparison charged nothing, could
/// not be cancelled, and could not be stopped by <c>MaxSteps</c>.
/// </summary>
public partial class SharedValueGraphComplexityTests
{
    /// <summary>
    /// W and X are independent equal lists of 20,000 numbers, Y differs only in its last number:
    /// one comparison of W with X or Y inspects 20,000 child slots — four full structural steps.
    /// <c>effect</c> is a recording host operation, the observable "later effect".
    /// </summary>
    private static string LargeProgram(string body)
        => $$"""
            W = range(1, 20000)
            X = range(1, 20000).map{n * 1}
            Y = range(1, 20000).map{if(n == 20000, 0, n)}
            {{body}}
            """;

    private const long LargeComparisonUnits = 20_000 + 1; // Every child slot, then the one completed root.

    private sealed class EffectLog
    {
        private int _calls;

        public int Calls => Volatile.Read(ref _calls);

        public HostOperations Operations()
            => HostOperations.Create(HostOperation.Create("effect", (args, _) =>
            {
                Interlocked.Increment(ref _calls);
                return new Result.Atom(7);
            }, "x"));
    }

    private static async Task<(EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget, ValueTraversalObservations Traversal)> RunComparisonOn(
        Route route,
        string source,
        EvaluationLimits? limits = null,
        HostOperations? hostOperations = null,
        Action<long>? beforeCharge = null,
        EvaluationObservations? evaluation = null,
        CancellationToken token = default)
    {
        var observations = evaluation
            ?? new EvaluationObservations { StructuralTraversal = new ValueTraversalObservations { BeforeStructuralWorkCharge = beforeCharge } };
        var traversal = observations.StructuralTraversal!;
        var expr = ParseValidWith(source, hostOperations);
        if (route is not (Route.ForcedTwin or Route.SuspendingTwin))
        {
            var (result, budget) = Evaluator.RunCountedObserved(
                expr,
                limits,
                enableOptimizations: route is Route.Optimized,
                observations: observations,
                hostOperations: hostOperations,
                cancellationToken: token);
            return (result, budget, traversal);
        }

        var suspendingCache = route is Route.SuspendingTwin ? new SuspendingAsyncZeroArgPropertyResultCache() : null;
        var (asyncResult, asyncBudget) = await Evaluator.RunCountedObservedAsync(
            expr,
            limits,
            zeroArgPropertyResultCache: (IZeroArgPropertyResultCache?)suspendingCache ?? new RunScopedAsyncZeroArgPropertyResultCache(),
            observations: observations,
            hostOperations: hostOperations,
            cancellationToken: token);
        if (suspendingCache is not null)
            Assert.True(suspendingCache.AsyncAccesses > 0);
        return (asyncResult, asyncBudget, traversal);
    }

    /// <summary>A source the front end accepts, parsed with the host operations its names resolve to.</summary>
    private static Expr ParseValidWith(string source, HostOperations? operations)
    {
        if (operations is null)
            return new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    // ── T1/T2: deep and wide == / != are charged ───────────────────────────────────────────

    [Theory]
    [InlineData("W == X", true)]
    [InlineData("W != X", false)]
    [InlineData("W == Y", false)]
    [InlineData("W != Y", true)]
    public void EqualityOperators_ChargeTheirStructuralWalk(string body, bool expected)
    {
        var (result, budget, traversal) = RunObserved(LargeProgram(body));
        AssertBool(expected, result);
        // Equal and deepest-difference walks both inspect every slot and complete (or fail) the root.
        Assert.Equal(LargeComparisonUnits, budget.ConsumedStructuralWorkUnits);
        Assert.Equal(budget.ConsumedStructuralWorkUnits, traversal.StructuralWorkUnits);
        Assert.Equal(1, traversal.EqualityPairExpansionCount);
    }

    [Fact]
    public void EqualityOperators_OnIndependentSharedDags_WalkDistinctPairsOnly()
    {
        // Independent equal DAGs share no object: the walk decides the distinct reference pairs, never the 2^40 paths.
        var (equal, equalBudget, equalTraversal) = RunObserved(DagProgram("A == B"));
        AssertBool(true, equal);
        Assert.Equal(LanguageFullWalk, equalTraversal.EqualityPairExpansionCount);
        Assert.True(equalBudget.ConsumedStructuralWorkUnits > 0);

        var (unequal, _, unequalTraversal) = RunObserved(DagProgram("A != C"));
        AssertBool(true, unequal);
        Assert.Equal(LanguageMismatchWalk, unequalTraversal.EqualityPairExpansionCount);
        Assert.True(unequalTraversal.StructuralWorkUnits > 0);
    }

    [Fact]
    public void ScalarAndTrivialComparisons_ChargeNothingAndCreateNoOperation()
    {
        // Scalars, one shared reference, different kinds or counts, empties, and short strings are
        // decided in O(1) by the context-free comparer: no unit, no charge, no expansion.
        var (result, budget, traversal) = RunObserved(
            "W = range(1, 300)\n1 == 1, 1.5 == 1.50, true == 1, \"ab\" == \"ab\", W == W, [1, 2] == (1, 2), [1] == [1, 2], [] == [], () == ()");
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal(0, budget.ConsumedStructuralWorkUnits);
        Assert.Equal(0, traversal.StructuralWorkChargeCount);
        Assert.Equal(0, traversal.EqualityPairExpansionCount);
    }

    [Fact]
    public void ComparisonChain_KeepsItsLinksAndOperandOrder_AndChargesEachLink()
    {
        // `W == X == W` compares W with X, then X with W — two walks, both charged, both true.
        var (chain, budget, traversal) = RunObserved(LargeProgram("W == X == W"));
        AssertBool(true, chain);
        Assert.Equal(2 * LargeComparisonUnits, budget.ConsumedStructuralWorkUnits);
        Assert.Equal(2, traversal.EqualityPairExpansionCount);

        // A false link does not short-circuit: every operand is still evaluated and every link compared.
        var (falseLink, falseBudget, _) = RunObserved(LargeProgram("W == Y == X"));
        AssertBool(false, falseLink);
        Assert.Equal(2 * LargeComparisonUnits, falseBudget.ConsumedStructuralWorkUnits);
    }

    // ── T3/T4/T6: cancellation inside one long comparison, descent and unwind ─────────────

    private static EvaluationBudget CancellableBudget(CancellationTokenSource cts)
        => EvaluationBudget.Create(limits: null, cancellationToken: cts.Token);

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void EvaluatorEquality_ObservesCancellationWhileCompletingDeepFrames(bool equal)
    {
        const int depth = 4 * Result.ValueSemanticComparer.UnitsPerCharge;
        using var cts = new CancellationTokenSource();
        var observations = new ValueTraversalObservations { BeforeStructuralWorkCharge = ordinal => { if (ordinal == 5) cts.Cancel(); } };

        // Every child slot is inspected within the first four charges; the fifth falls in the
        // successful completion unwind (equal) or the mismatch propagation (unequal).
        var thrown = Assert.ThrowsAny<OperationCanceledException>(() => Result.EvaluatorValueEquals(
            SingletonChain(depth, 1), SingletonChain(depth, equal ? 1 : 2), CancellableBudget(cts), observations));
        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.Equal(depth, observations.EqualityPairExpansionCount);
        Assert.Equal(5, observations.StructuralWorkChargeCount);
    }

    [Fact]
    public void EvaluatorEquality_ObservesCancellationDuringDescent_OfAWideMismatch()
    {
        using var cts = new CancellationTokenSource();
        var observations = new ValueTraversalObservations { BeforeStructuralWorkCharge = ordinal => { if (ordinal == 3) cts.Cancel(); } };
        var thrown = Assert.ThrowsAny<OperationCanceledException>(() => Result.EvaluatorValueEquals(
            Chain(5_000, 1), Chain(5_000, 2), CancellableBudget(cts), observations));
        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.Equal(3L * Result.ValueSemanticComparer.UnitsPerCharge, observations.StructuralWorkUnits);
    }

    [Theory]
    [InlineData("W == X")]
    [InlineData("W != Y")]
    [InlineData("Same(v, v) = 1\nSame([W][0], [X][0])")]
    [InlineData("F(v, v) = 1\nF(a, b) = effect(1)\nF([W][0], [Y][0])")]
    public async Task EvaluatorComparisons_ObserveCancellationInsideTheWalk_OnEveryRoute(string body)
    {
        foreach (var route in AllRoutes)
        {
            using var cts = new CancellationTokenSource();
            var log = new EffectLog();
            var charges = 0L;
            var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => RunComparisonOn(
                route,
                LargeProgram(body),
                hostOperations: log.Operations(),
                beforeCharge: ordinal =>
                {
                    charges = ordinal;
                    if (ordinal == 2) cts.Cancel();
                },
                token: cts.Token));
            Assert.Equal(cts.Token, thrown.CancellationToken);
            Assert.Equal(2, charges);
            // Cancellation inside the agreement never falls through to the later clause.
            Assert.Equal(0, log.Calls);
        }
    }

    // ── T5/T9/T10: a finite step budget is terminal inside the comparison ─────────────────

    /// <summary>
    /// Runs <paramref name="source"/> unlimited, then at the budget that leaves its comparison
    /// short: the comparison is the program's only structural work, so its own steps are exactly
    /// <c>units / 4096</c>, and removing them leaves the walk refused part-way.
    /// </summary>
    private static async Task AssertRefusedInsideTheComparison(string source, Result expected, int expectedEffects)
    {
        foreach (var route in AllRoutes)
        {
            var log = new EffectLog();
            var (unlimited, budget, traversal) = await RunComparisonOn(route, source, hostOperations: log.Operations());
            if (unlimited.IsError)
                Assert.Fail($"{route}: {unlimited.Error}");
            Assert.True(Result.ValueComparer.Equals(expected, unlimited.Value.Value), $"{route}: {unlimited.Value.Value}");
            Assert.Equal(expectedEffects, log.Calls);
            var structuralSteps = budget.ConsumedStructuralWorkUnits / EvaluationBudget.StructuralWorkUnitsPerStep;
            Assert.True(structuralSteps >= 4, $"{route}: {budget.ConsumedStructuralWorkUnits}");

            // The exact budget admits the run unchanged.
            var exactLog = new EffectLog();
            var (exact, exactBudget, _) = await RunComparisonOn(
                route, source, new EvaluationLimits { MaxSteps = budget.ConsumedSteps }, exactLog.Operations());
            Assert.False(exact.IsError, exact.IsError ? $"{route}: {exact.Error}" : null);
            Assert.True(Result.ValueComparer.Equals(expected, exact.Value.Value));
            Assert.Equal(budget.ConsumedSteps, exactBudget.ConsumedSteps);
            Assert.Equal(expectedEffects, exactLog.Calls);

            var refusedLog = new EffectLog();
            var refusedObservations = new EvaluationObservations { StructuralTraversal = new ValueTraversalObservations() };
            var (refused, refusedBudget, refusedTraversal) = await RunComparisonOn(
                route,
                source,
                new EvaluationLimits { MaxSteps = budget.ConsumedSteps - structuralSteps },
                refusedLog.Operations(),
                evaluation: refusedObservations);
            Assert.True(refused.IsError, $"{route}: expected the step limit, got {(refused.IsError ? null : refused.Value.Value)}");
            // Never BadArity, ArityMismatch, NoMatchingBranch, or a later clause's value.
            Assert.IsType<EvalError.EvaluationStepLimitExceeded>(Innermost(refused.Error));
            Assert.IsType<EvalError.EvaluationStepLimitExceeded>(refusedBudget.CheckContinuation());
            Assert.True(refusedTraversal.StructuralWorkUnits < LargeComparisonUnits, $"{route}: refused after the walk");
            Assert.True(traversal.StructuralWorkUnits >= LargeComparisonUnits);
            Assert.Equal(0, refusedLog.Calls);
            // No family ran out of clauses (NoMatchingBranch renders the call's name). The binder
            // returns the refusal itself; the run's retained terminal error (Q-02) is the second line
            // of defence that would stop a later clause at its first demand or checkpoint.
            Assert.Equal(0, refusedObservations.CallDiagnosticNameRenderCount);
        }
    }

    [Theory]
    [InlineData("W == X", true)]
    [InlineData("W != Y", true)]
    [InlineData("W == Y", false)]
    public Task EqualityOperators_StopAtAFiniteStepBudget(string body, bool expected)
        => AssertRefusedInsideTheComparison(LargeProgram(body), new Result.Bool(expected), expectedEffects: 0);

    [Fact]
    public Task RepeatedNameAgreement_StopsAtAFiniteStepBudget_AsTheStepLimitError()
        => AssertRefusedInsideTheComparison(LargeProgram("Same(v, v) = 1\nSame([W][0], [X][0])"), new Result.Atom(1), expectedEffects: 0);

    [Fact]
    public Task ClauseFamily_EqualAgreement_IsRefusedTerminally()
        => AssertRefusedInsideTheComparison(
            LargeProgram("F(v, v) = 1\nF(a, b) = effect(1)\nF([W][0], [X][0])"), new Result.Atom(1), expectedEffects: 0);

    [Fact]
    public Task ClauseFamily_UnequalAgreement_SelectsTheLaterClause_ButARefusalNeverDoes()
        // Unlimited, the genuine mismatch is the first clause's non-match and the second clause runs
        // its effect; refused, the run ends with no effect at all.
        => AssertRefusedInsideTheComparison(
            LargeProgram("F(v, v) = 1\nF(a, b) = effect(1)\nF([W][0], [Y][0])"), new Result.Atom(7), expectedEffects: 1);

    [Fact]
    public async Task ClauseFamily_RefusedAgreement_IsNeverTheClauseNonMatch()
    {
        // The later clause rejects without passing any checkpoint (its literal inspects an already
        // demanded argument), so a refusal turned into the first clause's non-match would surface as
        // NoMatchingBranch instead of the step limit.
        const string family = "F(v, v) = 1\nF(a, 0) = effect(1)\n";
        await AssertRefusedInsideTheComparison(LargeProgram(family + "F([W][0], [X][0])"), new Result.Atom(1), expectedEffects: 0);

        var (mismatch, _, _) = RunObserved(LargeProgram("F(v, v) = 1\nF(a, 0) = 2\nF([W][0], [Y][0])"));
        Assert.True(mismatch.IsError);
        Assert.IsType<EvalError.NoMatchingBranch>(Innermost(mismatch.Error));
    }

    // ── T7: repeated-name outcomes, demand order, and one session per binder head ─────────

    [Fact]
    public void RepeatedNameAgreement_KeepsItsOutcomes()
    {
        var (equal, equalBudget, _) = RunObserved(LargeProgram("Same(v, v) = 1\nSame([W][0], [X][0])"));
        AssertNumber(1, equal);
        Assert.Equal(LargeComparisonUnits, equalBudget.ConsumedStructuralWorkUnits);

        var (unequal, _, _) = RunObserved(LargeProgram("Same(v, v) = 1\nSame([W][0], [Y][0])"));
        Assert.True(unequal.IsError);
        Assert.IsType<EvalError.BadArity>(Innermost(unequal.Error));

        // Different emitted counts are decided before any value comparison.
        var (counts, countsBudget, _) = RunObserved(LargeProgram("Same(v, v) = 1\nSame(W, (W, W))"));
        Assert.True(counts.IsError);
        Assert.IsType<EvalError.BadArity>(Innermost(counts.Error));
        Assert.Equal(0, countsBudget.ConsumedStructuralWorkUnits);
    }

    [Fact]
    public void RepeatedNameAgreement_DemandsInWrittenOrder_AndEachArgumentOnce()
    {
        var order = new List<decimal>();
        var operations = HostOperations.Create(HostOperation.Create("trace", (args, _) =>
        {
            lock (order) order.Add((decimal)((Result.Atom)args[0]).Value);
            return Result.ListValue.TakeOwnership([.. Enumerable.Range(1, 300).Select(i => (Result)new Result.Atom(i))]);
        }, "x"));
        var expr = ParseValidWith("Same(v, w, v) = 1\nSame(trace(1), trace(2), trace(3))", operations);
        var (result, budget) = Evaluator.RunCountedObserved(expr, hostOperations: operations);
        AssertNumber(1, result);
        // The repeated name's two occurrences are demanded when reached; the unique `w` is never demanded.
        Assert.Equal([1m, 3m], order);
        Assert.True(budget.ConsumedStructuralWorkUnits >= 300 + 1, budget.ConsumedStructuralWorkUnits.ToString());
    }

    [Fact]
    public void RepeatedNameAgreements_OfOneHead_ShareOneComparisonSession()
    {
        // The second agreement compares the same two references again: its nested pairs are answered
        // from the head's session, so only the narrow top-level pair is expanded a second time.
        var (result, _, traversal) = RunObserved(DagProgram("Same3(v, v, v) = 1\nSame3([A][0], [B][0], [B][0])"));
        AssertNumber(1, result);
        Assert.Equal(LanguageFullWalk + 1, traversal.EqualityPairExpansionCount);

        // Separate calls never share a session.
        var (twice, _, twiceTraversal) = RunObserved(DagProgram("Same(v, v) = 1\nSame([A][0], [B][0]), Same([A][0], [B][0])"));
        Assert.False(twice.IsError, twice.IsError ? twice.Error.ToString() : null);
        Assert.Equal(2 * LanguageFullWalk, twiceTraversal.EqualityPairExpansionCount);
    }

    // ── T11/T16: the verdicts are exactly the public comparer's ───────────────────────────

    private static Result[] SemanticMatrix()
    {
        var plan = new Evaluator.InvocationPlan(Evaluator.EvalCtx.Empty, []);
        var reference = new Result.CallReference(plan);
        var otherReference = new Result.CallReference(new Evaluator.InvocationPlan(Evaluator.EvalCtx.Empty, []));
        var shared = SharedDag(6);
        var longText = new string('k', 64 * 40);
        return
        [
            new Result.Atom(Decimal128.NaN),
            new Result.Atom(Decimal128.NaN),
            new Result.Atom(Decimal128.Parse("1.5", System.Globalization.CultureInfo.InvariantCulture)),
            new Result.Atom(Decimal128.Parse("1.50", System.Globalization.CultureInfo.InvariantCulture)),
            new Result.Atom(Decimal128.Zero),
            new Result.Atom(Decimal128.NegativeZero),
            new Result.Atom(1),
            new Result.Bool(true),
            new Result.Bool(false),
            new Result.Str("a"),
            new Result.Str("a"),
            new Result.Str(longText),
            new Result.Str(new string('k', 64 * 40)),
            new Result.Str(new string('k', 64 * 40 - 1) + "j"),
            List(),
            Seq(),
            List(Atom(1), Atom(2)),
            Seq(Atom(1), Atom(2)),
            List(Atom(1), Atom(2)),
            List(Seq(Atom(1)), new Result.Str(longText)),
            List(Seq(Atom(1)), new Result.Str(new string('k', 64 * 40))),
            shared,
            SharedDag(6),
            SharedDag(6, leafB: 3),
            List(shared, shared),
            List(SharedDag(6), SharedDag(6)),
            reference,
            reference.ArgumentView,
            otherReference,
            List(reference, reference.ArgumentView),
            List(reference, reference.ArgumentView),
            List(otherReference, reference.ArgumentView),
        ];
    }

    [Fact]
    public void EvaluatorEquality_MatchesThePublicComparer_OverTheSemanticMatrix()
    {
        var values = SemanticMatrix();
        var budget = EvaluationBudget.Create(limits: null);
        foreach (var left in values)
        {
            foreach (var right in values)
            {
                var verdict = Result.EvaluatorValueEquals(left, right, budget, observations: null);
                Assert.False(verdict.IsError);
                Assert.Equal(Result.ValueComparer.Equals(left, right), verdict.Value);
            }
        }

        // The public comparer still needs no evaluation context, and its hashes agree with the
        // charged operation hashes, string payload included.
        var comparer = OperationComparer(out _);
        foreach (var value in values)
            Assert.Equal(Result.ValueComparer.GetHashCode(value), comparer.GetHashCode(value));
        Assert.Null(comparer.CompleteOperation());
        Assert.Equal(Result.ValueComparer.GetHashCode(values[11]), Result.ValueComparer.GetHashCode(values[12]));
        Assert.Equal(Result.ValueComparer.GetHashCode(values[19]), Result.ValueComparer.GetHashCode(values[20]));
    }

    [Fact]
    public void EvaluatorEquality_LanguageLevelSemanticsAreUnchanged()
        => EvaluatorTestSupport.AssertEvalBools(
            "1.5 == 1.50, -0 == 0, true == 1, true != false, \"ab\" == \"ab\", [1, 2] == (1, 2), [] == [], () == (), [[1], (2, 3)] == [[1], (2, 3)], [[1], (2, 3)] == [[1], [2, 3]]",
            true, true, false, true, true, false, true, true, true, false);

    // ── T13: string payload is charged by length ───────────────────────────────────────────

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task LiteralStringPattern_ChargesPayload_AndRefusalNeverSelectsAnotherClause(bool nested)
    {
        const int length = 64 * 5_000;
        foreach (var equal in new[] { true, false })
        {
            var text = new string('k', length - 1) + (equal ? "k" : "j");
            var literal = new string('k', length);
            var head = nested ? $"[\"{literal}\", unused]" : $"\"{literal}\"";
            var argument = nested ? "[Text, 0]" : "Text";
            var source = $"Text = \"{text}\"\nF({head}) = 1\nF(other) = effect(1)\nF({argument})";
            foreach (var route in AllRoutes)
            {
                var effects = new EffectLog();
                var (result, budget, _) = await RunComparisonOn(route, source, hostOperations: effects.Operations());
                AssertNumber(equal ? 1 : 7, result);
                Assert.Equal(equal ? 0 : 1, effects.Calls);
                Assert.Equal(length / Result.ValueSemanticComparer.StringCharsPerUnit, budget.ConsumedStructuralWorkUnits);

                var refusedEffects = new EffectLog();
                var (refused, _, refusedTraversal) = await RunComparisonOn(route, source,
                    new EvaluationLimits { MaxSteps = 2 }, refusedEffects.Operations());
                Assert.True(refused.IsError);
                Assert.IsType<EvalError.EvaluationStepLimitExceeded>(Innermost(refused.Error));
                Assert.Equal(1, refusedTraversal.StructuralWorkChargeCount);
                Assert.Equal(0, refusedEffects.Calls);
            }
        }
    }

    [Fact]
    public async Task LiteralStringPattern_ObservesCancellationAtItsPayloadCharge()
    {
        var text = new string('k', LongLength);
        var source = $"Text = \"{text}\"\nF(\"{text}\") = 1\nF(other) = effect(1)\nF(Text)";
        foreach (var route in AllRoutes)
        {
            using var cts = new CancellationTokenSource();
            var effects = new EffectLog();
            var charges = 0L;
            var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => RunComparisonOn(route, source,
                hostOperations: effects.Operations(),
                beforeCharge: ordinal => { charges = ordinal; cts.Cancel(); }, token: cts.Token));
            Assert.Equal(cts.Token, thrown.CancellationToken);
            Assert.Equal(1, charges);
            Assert.Equal(0, effects.Calls);
        }
    }

    private const int LongLength = 64 * 1_000;

    private static Result LongStr(char last = 'z') => new Result.Str(new string('k', LongLength - 1) + last);

    private static (EvalResult<bool> Verdict, long Units) ChargedEquals(Result left, Result right)
    {
        var budget = EvaluationBudget.Create(limits: null);
        var verdict = Result.EvaluatorValueEquals(left, right, budget, observations: null);
        return (verdict, budget.ConsumedStructuralWorkUnits);
    }

    [Fact]
    public void StringEquality_ChargesPayloadOnlyWhenItCanReadPastTheLength()
    {
        const long payload = LongLength / Result.ValueSemanticComparer.StringCharsPerUnit;

        Assert.Equal((true, 0L), Unpack(ChargedEquals(new Result.Str(new string('k', 63)), new Result.Str(new string('k', 63)))));
        Assert.Equal((true, payload), Unpack(ChargedEquals(LongStr(), LongStr())));
        Assert.Equal((false, payload), Unpack(ChargedEquals(LongStr(), LongStr('y'))));
        // Different lengths are decided by the length check; one shared text by identity.
        Assert.Equal((false, 0L), Unpack(ChargedEquals(LongStr(), new Result.Str(new string('k', LongLength + 1)))));
        var text = new string('k', LongLength);
        Assert.Equal((true, 0L), Unpack(ChargedEquals(new Result.Str(text), new Result.Str(text))));
        // Nested leaves: one inspection and one completion, plus the payload.
        Assert.Equal((true, payload + 2), Unpack(ChargedEquals(List(LongStr()), List(LongStr()))));

        static (bool, long) Unpack((EvalResult<bool> Verdict, long Units) charged)
        {
            Assert.False(charged.Verdict.IsError);
            return (charged.Verdict.Value, charged.Units);
        }
    }

    [Fact]
    public void StringPayload_IsChargedBeforeTheNativeRead_AndObservesCancellation()
    {
        using var cts = new CancellationTokenSource();
        var observations = new ValueTraversalObservations { BeforeStructuralWorkCharge = _ => cts.Cancel() };
        var thrown = Assert.ThrowsAny<OperationCanceledException>(() => Result.EvaluatorValueEquals(
            LongStr(), LongStr(), CancellableBudget(cts), observations));
        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.Equal(1, observations.StructuralWorkChargeCount);
        Assert.Equal(LongLength / Result.ValueSemanticComparer.StringCharsPerUnit, observations.StructuralWorkUnits);

        var refusing = EvaluationBudget.Create(new EvaluationLimits { MaxSteps = 1 });
        Assert.Null(refusing.TryChargeStep());
        var refused = Result.EvaluatorValueEquals(
            new Result.Str(new string('k', 64 * 5_000)), new Result.Str(new string('k', 64 * 5_000)), refusing, observations: null);
        Assert.True(refused.IsError);
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(refused.Error);
    }

    [Fact]
    public void Operation_RepeatedLongStringReferences_AreHashedAndComparedOnce()
    {
        const long payload = LongLength / Result.ValueSemanticComparer.StringCharsPerUnit;
        var text = LongStr();
        var equalText = LongStr();

        // distinct over N references to one long string hashes it once; an independent equal text is
        // hashed once more and compared once.
        var budget = EvaluationBudget.Create(limits: null);
        var comparer = OperationComparer(out _, budget);
        var kept = new HashSet<Result>(comparer);
        foreach (var item in Repeated(text, RepeatCount, equalText, equalText))
            kept.Add(item);
        Assert.Null(comparer.CompleteOperation());
        Assert.Single(kept);
        Assert.Equal(3 * payload, budget.ConsumedStructuralWorkUnits);

        // contains over N references to one long string searching an equal text compares it once.
        var containsBudget = EvaluationBudget.Create(limits: null);
        var containsComparer = OperationComparer(out _, containsBudget);
        foreach (var item in Repeated(text, RepeatCount))
            Assert.True(containsComparer.Equals(item, equalText));
        Assert.Null(containsComparer.CompleteOperation());
        Assert.Equal(payload, containsBudget.ConsumedStructuralWorkUnits);

        // Nested in a shared node: hashed once inside the node, and the node once.
        var nested = List(text, Atom(1));
        var nestedBudget = EvaluationBudget.Create(limits: null);
        var nestedComparer = OperationComparer(out _, nestedBudget);
        var hashes = Repeated(List(nested, nested), RepeatCount).Select(nestedComparer.GetHashCode).Distinct().ToArray();
        Assert.Null(nestedComparer.CompleteOperation());
        Assert.Single(hashes);
        Assert.Equal(Result.ValueComparer.GetHashCode(List(nested, nested)), hashes[0]);
        Assert.True(nestedBudget.ConsumedStructuralWorkUnits < 2 * payload, nestedBudget.ConsumedStructuralWorkUnits.ToString());
    }

    [Theory]
    [InlineData("text(1) == text(2)", true)]
    [InlineData("text(1) != text(2)", false)]
    [InlineData("contains((text(1), text(2), 5), text(3))", true)]
    [InlineData("distinct((text(1), text(2), text(3))).count", 1)]
    [InlineData("Same(v, v) = 1\nSame(text(1), text(2))", 1)]
    public void LongHostStrings_AreChargedByLength_AtLanguageLevel(string body, object expected)
    {
        var operations = HostOperations.Create(HostOperation.Create(
            "text", (_, _) => new Result.Str(new string('k', LongLength)), "n"));
        var expr = ParseValidWith(body, operations);
        var (result, budget) = Evaluator.RunCountedObserved(expr, hostOperations: operations);
        if (expected is bool flag)
            AssertBool(flag, result);
        else
            AssertNumber((int)expected, result);
        Assert.True(
            budget.ConsumedStructuralWorkUnits >= LongLength / Result.ValueSemanticComparer.StringCharsPerUnit,
            budget.ConsumedStructuralWorkUnits.ToString());
    }

    // ── T12/T17: every route and every non-binding limit agree ─────────────────────────────

    [Theory]
    [InlineData("W == X, W != Y, W == X == W")]
    [InlineData("Same(v, v) = 1\nSame([W][0], [X][0])")]
    [InlineData("F(v, v) = 1\nF(a, b) = effect(1)\nF([W][0], [Y][0]), F([W][0], [X][0])")]
    [InlineData("range(1, 3).map{if(W == X, n, 0 - n)}")]
    [InlineData("Step(a, b, k) = a, b, k + if(a == b, 1, 0)\nStep(W, X, 0).repeat(3)[2]")]
    [InlineData("Small = range(1, 400).map{[n mod 7, [n mod 3]]}\nSmall.filter{n == [1, [1]]}.count")]
    public async Task EvaluatorComparisons_AgreeAcrossRoutesAndNonBindingLimits(string body)
    {
        var source = LargeProgram(body);
        var expected = new List<string>();
        var units = new List<long>();
        foreach (var route in AllRoutes)
        {
            foreach (var limits in new EvaluationLimits?[] { null, EvaluationLimits.Default, new() { MaxSteps = long.MaxValue }, new() { MaxSteps = 10_000_000 } })
            {
                var log = new EffectLog();
                var (result, budget, traversal) = await RunComparisonOn(route, source, limits, log.Operations());
                if (result.IsError)
                    Assert.Fail($"{route}: {result.Error}");
                units.Add(budget.ConsumedStructuralWorkUnits);
                expected.Add(string.Join(
                    " | ",
                    Describe(result.Value.Value),
                    result.Value.EmittedCount,
                    budget.ConsumedSteps,
                    budget.ConsumedStructuralWorkUnits,
                    traversal.EqualityPairExpansionCount,
                    traversal.StructuralWorkChargeCount,
                    log.Calls));
            }
        }

        Assert.All(expected, observation => Assert.Equal(expected[0], observation));
        Assert.True(units[0] > 0);
    }

    [Fact]
    public void EqualityInPlannedLoopState_ChargesAndCancelsInsideThePlannedComparison()
    {
        var expr = ParseValidWith(LargeProgram(
            "Step(a, b, k) = a, b, k + if(a == b, 1, 0)\nStep(W, X, 0).repeat(3)[2]"), operations: null);
        var diagnostics = new LoopOptimizationDiagnostics();
        var (planned, budget) = Evaluator.RunCountedObserved(expr, loopDiagnostics: diagnostics);
        var (generic, genericBudget) = Evaluator.RunCountedObserved(expr, enableOptimizations: false);
        AssertNumber(3, planned);
        AssertNumber(3, generic);
        Assert.Equal(3 * LargeComparisonUnits, budget.ConsumedStructuralWorkUnits);
        Assert.Equal(budget.ConsumedStructuralWorkUnits, genericBudget.ConsumedStructuralWorkUnits);
        Assert.Equal(budget.ConsumedSteps, genericBudget.ConsumedSteps);
        Assert.True(diagnostics.OptimizedLoopHits > 0);
        Assert.Equal(9, diagnostics.PlannedBuiltinOperations); // Three ==, if, and + operations.
        Assert.Empty(diagnostics.FallbackReasons);
        Assert.Equal(0, diagnostics.GenericExpressionEvaluationsInsideOptimizedLoops);

        var refusedTraversal = new ValueTraversalObservations();
        var refusedDiagnostics = new LoopOptimizationDiagnostics();
        var (refused, refusedBudget) = Evaluator.RunCountedObserved(expr,
            new EvaluationLimits { MaxSteps = budget.ConsumedSteps - budget.ConsumedStructuralWorkUnits / EvaluationBudget.StructuralWorkUnitsPerStep },
            loopDiagnostics: refusedDiagnostics,
            observations: new EvaluationObservations { StructuralTraversal = refusedTraversal });
        Assert.True(refused.IsError);
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(Innermost(refused.Error));
        Assert.True(refusedDiagnostics.PlannedBuiltinOperations > 0);
        Assert.Empty(refusedDiagnostics.FallbackReasons);
        // An attempted structural charge was refused inside the comparison, before all three walks.
        Assert.True(refusedTraversal.StructuralWorkUnits > refusedBudget.ConsumedStructuralWorkUnits);
        Assert.True(refusedTraversal.StructuralWorkUnits < 3 * LargeComparisonUnits);

        using var cts = new CancellationTokenSource();
        var cancelledDiagnostics = new LoopOptimizationDiagnostics();
        var traversal = new ValueTraversalObservations { BeforeStructuralWorkCharge = ordinal => { if (ordinal == 2) cts.Cancel(); } };
        var thrown = Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(expr,
            loopDiagnostics: cancelledDiagnostics,
            observations: new EvaluationObservations { StructuralTraversal = traversal }, cancellationToken: cts.Token));
        Assert.Equal(cts.Token, thrown.CancellationToken);
        Assert.True(cancelledDiagnostics.OptimizedLoopHits > 0);
        Assert.True(cancelledDiagnostics.PlannedBuiltinOperations > 0);
        Assert.Empty(cancelledDiagnostics.FallbackReasons);
        Assert.Equal(2, traversal.StructuralWorkChargeCount);
    }

    // ── T15: sessions never outlive their comparison or run ───────────────────────────────

    [Fact]
    public void ComparisonSession_IsRetired_WhenItsFinalPartialBatchIsRefused()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxSteps = 1 });
        Assert.Null(budget.TryChargeStructuralWork(EvaluationBudget.StructuralWorkUnitsPerStep - 1));
        Assert.Null(budget.TryChargeStep());
        var comparer = Result.CreateOperationComparer(budget, observations: null);
        // Two units stay pending until TryEquals flushes: the refusal is outside Equals's walk.
        var result = comparer.TryEquals(List(Atom(1)), List(Atom(1)));
        Assert.True(result.IsError);
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(result.Error);
        Assert.Throws<InvalidOperationException>(() => comparer.TryEquals(Atom(1), Atom(1)));
    }

    [Fact]
    public async Task EqualityComparisons_DoNotShareMemos_AcrossExpressionsOrRuns()
    {
        var (one, _, oneTraversal) = RunObserved(DagProgram("A == B"));
        var (two, _, twoTraversal) = RunObserved(DagProgram("A == B, A == B"));
        AssertBool(true, one);
        Assert.False(two.IsError);
        Assert.Equal(2 * oneTraversal.EqualityPairExpansionCount, twoTraversal.EqualityPairExpansionCount);

        var source = LargeProgram("W == X, W != Y");
        var (_, firstBudget, first) = RunObserved(source);
        var runs = Enumerable.Range(0, 8).Select(_ => Task.Run(() =>
        {
            var (result, budget, traversal) = RunObserved(source);
            Assert.False(result.IsError);
            Assert.Equal(firstBudget.ConsumedSteps, budget.ConsumedSteps);
            return traversal.StructuralWorkUnits;
        })).ToArray();
        Assert.All(await Task.WhenAll(runs), units => Assert.Equal(first.StructuralWorkUnits, units));
    }
}
