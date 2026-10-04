using KatLang.Evaluation;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

/// <summary>
/// STRATEGY-NEUTRAL BUDGET ACCOUNTING (Q-09b, decided 2026-10-04): every execution strategy
/// charges every evaluation budget at the same LOGICAL points, so no configured limit ever has
/// to select a strategy (<c>Evaluator.CreateRootCtx</c>). The planned loops and the fused
/// <c>filter</c>→<c>count</c> pipeline replace generic evaluation that charges a step per
/// iteration and one expression-work checkpoint per dispatch head and per spine transition
/// (<see cref="EvaluationBudget.TryChargeExpressionNodeWork"/>), and that RESERVES the item
/// slots of the collections it materializes; the optimized strategies must charge exactly the
/// same.
///
/// <para>The oracle is the GENERIC strategy of the same run (<c>enableOptimizations: false</c>).
/// Equality is asserted on the RAW checkpoint count, not merely on whole steps: a single
/// missing or surplus checkpoint per iteration is invisible to step totals until it crosses a
/// 4096-checkpoint block (the prototype's 0.1–0.4 % residue), and the raw count sees it at once.
/// Every case also proves the optimized path was actually taken, so a regression that silently
/// falls back to the generic strategy cannot pass as parity.</para>
///
/// <para>The tight-boundary sweeps then run BOTH strategies at every step budget from 1 to the
/// unlimited consumption + 1 (sampled for long programs) and require the identical outcome,
/// error tree, counters at the failure point, and host-operation trace: the k-th step charge
/// happens at the same point — after the same effects, under the same diagnostic boundaries —
/// on both strategies.</para>
/// </summary>
public class StrategyNeutralBudgetParityTests
{
    internal sealed class HostLog
    {
        private int _ticks;
        public List<string> Calls { get; } = [];

        public Result Tick()
        {
            var t = Interlocked.Increment(ref _ticks);
            Calls.Add($"tick#{t}");
            return new Result.Atom(t);
        }

        public Result Trace(Result value)
        {
            Calls.Add($"trace({SemanticExplorerHarness.Neutral(value)})");
            return value;
        }
    }

    internal static HostOperations Operations(HostLog log) => HostOperations.Create(
        HostOperation.Create("tick", (_, _) => log.Tick()),
        HostOperation.Create("trace", (args, _) => log.Trace(args[0]), "x"));

    /// <summary>One observed run: the full outcome plus every budget counter the run charged.</summary>
    internal sealed record Observation(
        string Outcome,
        string? ErrorTree,
        long Steps,
        long Checkpoints,
        int PeakDepth,
        long Items,
        long StringUnits,
        string HostTrace,
        long LoopHits,
        long FusionHits)
    {
        /// <summary>Everything that must be identical between strategies (not the strategy markers).</summary>
        public string Accounting
            => $"{Outcome}\n{ErrorTree}\nsteps={Steps} checkpoints={Checkpoints} depth={PeakDepth} items={Items} strings={StringUnits}\nhost={HostTrace}";
    }

    internal static Expr Program(string source, HostOperations? operations)
    {
        var parsed = operations is null
            ? Parser.Parse(source)
            : Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, $"source must parse cleanly:\n{source}\n{string.Join("\n", parsed.Diagnostics)}");
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    internal static Observation Observe(
        string source,
        bool optimize,
        EvaluationLimits? limits = null,
        long? seed = null)
    {
        var log = new HostLog();
        var operations = UsesHostOperations(source) ? Operations(log) : null;
        var loops = new LoopOptimizationDiagnostics();
        var sequences = new SequencePipelineDiagnostics();
        var (result, budget) = Evaluator.RunCountedObserved(
            Program(source, operations),
            limits,
            enableOptimizations: optimize,
            loopDiagnostics: loops,
            sequenceDiagnostics: sequences,
            hostOperations: operations,
            randomSeed: seed);
        return new Observation(
            result.IsError
                ? $"err {result.Error.GetType().Name}"
                : $"ok {SemanticExplorerHarness.Neutral(result.Value.Value)} n={result.Value.EmittedCount}",
            result.IsError ? DescribeErrorTree(result.Error) : null,
            budget.ConsumedSteps,
            budget.ConsumedExpressionCheckpoints,
            budget.PeakDepth,
            budget.MaterializedItems,
            budget.MaterializedStringChars,
            string.Join(",", log.Calls),
            loops.OptimizedLoopHits,
            sequences.FilterCountFusionHits);
    }

    private static bool UsesHostOperations(string source)
        => source.Contains("tick(", StringComparison.Ordinal) || source.Contains("trace(", StringComparison.Ordinal);

    /// <summary>Which optimized strategy a case must exercise.</summary>
    [Flags]
    public enum Exercises
    {
        PlannedLoop = 1,
        Fusion = 2,
    }

    /// <summary>
    /// The parity corpus: every planned-node kind in every dispatch context (step row, spine
    /// operand, delegated operand, <c>if</c> argument, temp body), partially planned steps,
    /// handover, nested and mixed loops and pipelines, and every fused pipeline form with direct
    /// range and generic sources. Each source parses cleanly; each value is the generic value.
    /// </summary>
    public static readonly IReadOnlyList<(string Id, string Source, Exercises Exercises)> Corpus =
    [
        ("inline-step", "repeat({x + 1}, 50, 0)", Exercises.PlannedLoop),
        ("named-step", "Step(s) = s + 1\nrepeat(Step, 50, 0)", Exercises.PlannedLoop),
        ("bare-state-row", "Step(s) = s\nrepeat(Step, 30, 7)", Exercises.PlannedLoop),
        ("block-initial-state", "Step(s, t) = s + 1, if(s > 2, t, t + 1)\nrepeat(Step, 30, { 7 }, { 1 + 2 })", Exercises.PlannedLoop),
        ("forwarded-block-initial-state", "Step(s) = s * 2 mod 1000\nF(x) = repeat(Step, 20, x)\nF({ 3 })", Exercises.PlannedLoop),
        ("constant-row", "Step(s) = 5\nrepeat(Step, 30, 7)", Exercises.PlannedLoop),
        ("nested-spine", "Step(s) = (s + 1) * 2 - s / 4\nrepeat(Step, 40, 1)", Exercises.PlannedLoop),
        ("unary", "Step(s) = -s + 1\nrepeat(Step, 40, 3)", Exercises.PlannedLoop),
        ("unary-of-spine", "Step(s) = -(s - 3)\nrepeat(Step, 41, 1)", Exercises.PlannedLoop),
        ("not-and-logic", "Step(s, b) = s + 1, not b and (s > 2 or b)\nrepeat(Step, 25, 0, true)", Exercises.PlannedLoop),
        ("comparison-chain", "Step(s, t) = s + 1, if(0 < s < 30 <= 40, t + 1, t)\nrepeat(Step, 45, 0, 0)", Exercises.PlannedLoop),
        ("comparison-false-link", "Step(s, t) = s + 1, if(s < 3 < 2 != false, t + 1, t)\nrepeat(Step, 20, 0, 0)", Exercises.PlannedLoop),
        ("if-state-branches", "Step(s) = if(s > 10, s, s + 2)\nrepeat(Step, 40, 0)", Exercises.PlannedLoop),
        ("if-constant-branches", "Step(s, t) = s + 1, if(s > 10, 1, 2)\nrepeat(Step, 30, 0, 0)", Exercises.PlannedLoop),
        ("nested-if", "Step(s) = if(s > 10, if(s > 20, s - 3, s - 1), s + 2)\nrepeat(Step, 60, 0)", Exercises.PlannedLoop),
        ("if-in-spine", "Step(s) = 1 + if(s > 4, s, 2 * s) * 2\nrepeat(Step, 12, 1)", Exercises.PlannedLoop),
        ("string-branches", "Step(s, t) = s + 1, if(s > 3, 'big', 'small')\nrepeat(Step, 9, 0, 'none')", Exercises.PlannedLoop),
        ("temps", "Step(s) = {\n  T1 = s + 1\n  T2 = T1 * 2\n  T2 - s\n}\nrepeat(Step, 30, 1)", Exercises.PlannedLoop),
        ("temp-as-if-argument", "Step(s) = {\n  T = s * 2\n  if(s > 5, T, s + 1)\n}\nrepeat(Step, 25, 0)", Exercises.PlannedLoop),
        ("temp-explicit-call", "Step(s) = {\n  T = s * 2\n  T() + T - 1\n}\nrepeat(Step, 20, 1)", Exercises.PlannedLoop),
        ("temp-chain", "Step(s) = {\n  A = s + 1\n  B = A + A\n  C = B * A\n  C - B\n}\nrepeat(Step, 15, 1)", Exercises.PlannedLoop),
        ("while-loop", "Step(s) = s + 1, s < 60\nwhile(Step, 0)", Exercises.PlannedLoop),
        ("while-two-state", "Step(a, b) = b, a + b, b < 1000\nwhile(Step, 0, 1)", Exercises.PlannedLoop),
        ("while-temps", "Step(s) = {\n  N = s + 3\n  N, N < 90\n}\nwhile(Step, 0)", Exercises.PlannedLoop),
        ("need-parameter", "F(k) = repeat({x + k}, 30, 0)\nF(5)", Exercises.PlannedLoop),
        ("need-parameter-if-argument", "F(k) = repeat({if(x > k, k, x + 1)}, 30, 0)\nF(7)", Exercises.PlannedLoop),
        ("pending-initial-state", "Seed = 3 * 4\nrepeat({x + 1}, 10, Seed)", Exercises.PlannedLoop),
        ("pending-initial-state-if", "Seed = 3 * 4\nStep(s) = if(s > 20, s, s + 1)\nrepeat(Step, 15, Seed)", Exercises.PlannedLoop),
        ("partial-fallback-row", "Step(s, t) = s + 1, t + [s].count\nrepeat(Step, 25, 0, 0)", Exercises.PlannedLoop),
        ("fallback-with-temps", "Step(s, t) = {\n  T = s * 3\n  s + 1, t + [T].count\n}\nrepeat(Step, 20, 0, 0)", Exercises.PlannedLoop),
        ("handover-arity-change", "Step(s) = if(s > 3, (s, s), s + 1)\nrepeat(Step, 6, 0)", Exercises.PlannedLoop),
        ("nested-loops", "Inner(n) = repeat({x + 1}, n, 0)\nStep(s) = s + Inner(3)\nrepeat(Step, 20, 0)", Exercises.PlannedLoop),
        ("loop-in-temp-call", "F(n) = repeat({x * 2}, n, 1)\nStep(s) = s + F(4)\nrepeat(Step, 10, 0)", Exercises.PlannedLoop),
        ("division-by-zero", "Step(s) = 10 / (s - 5)\nrepeat(Step, 9, 0)", Exercises.PlannedLoop),
        ("type-error-in-if", "Step(s) = if(s, 1, 2)\nrepeat(Step, 3, 0)", Exercises.PlannedLoop),
        ("fused-dot-range", "P(x) = x > 10\nrange(1, 50).filter(P).count", Exercises.Fusion),
        ("fused-dot-block", "range(1, 60).filter({ x mod 3 == 0 }).count", Exercises.Fusion),
        ("fused-plain-plain", "count(filter(range(1, 40), { x > 5 }))", Exercises.Fusion),
        ("fused-plain-dot", "count(range(1, 40).filter({ x > 5 }))", Exercises.Fusion),
        ("fused-generic-source", "L = [1, 2, 3, 4, 5, 6]\nL.filter({ x > 2 }).count", Exercises.Fusion),
        ("fused-empty-range", "range(5, 1).filter({ x > 2 }).count", Exercises.Fusion),
        ("fused-none-kept", "range(1, 30).filter({ x > 100 }).count", Exercises.Fusion),
        ("fused-all-kept", "range(1, 30).filter({ x > 0 }).count", Exercises.Fusion),
        ("fused-predicate-error", "range(1, 10).filter({ 10 / (x - 4) > 0 }).count", Exercises.Fusion),
        ("fused-recursive", "R(n) = if(n > 0, range(n, n).filter({ R(x - 1) >= 0 }).count, 0)\nR(12)", Exercises.Fusion),
        ("fused-in-loop-row", "Step(s) = s + range(1, 10).filter({ x > 3 }).count\nrepeat(Step, 12, 0)", Exercises.PlannedLoop | Exercises.Fusion),
        ("loop-in-predicate", "range(1, 15).filter({ repeat({ y + 1 }, x, 0) > 5 }).count", Exercises.PlannedLoop | Exercises.Fusion),
        ("host-effects-in-loop", "Step(s) = s + 1\nG(a, b) = a + b\nG(trace(1) + repeat(Step, 20, 0), trace(2))", Exercises.PlannedLoop),
        ("host-effects-in-fallback-row", "Step(s, t) = s + 1, t + trace(s)\nrepeat(Step, 12, 0, 0)", Exercises.PlannedLoop),
        ("host-effects-in-predicate", "range(1, 12).filter({ trace(x) > 6 }).count", Exercises.Fusion),
        ("seeded-random-in-loop", "Step(s, t) = s + 1, t + randomInt(0, 9)\nrepeat(Step, 15, 0, 0)", Exercises.PlannedLoop),
        ("temp-slot-row", "Step(s) = {\n  T = s + 2\n  T\n}\nrepeat(Step, 25, 0)", Exercises.PlannedLoop),
        ("temp-call-row", "Step(s) = {\n  T = s + 2\n  T()\n}\nrepeat(Step, 25, 0)", Exercises.PlannedLoop),
        ("temp-call-if-argument", "Step(s) = {\n  T = s + 2\n  if(s < 20, T(), T)\n}\nrepeat(Step, 25, 0)", Exercises.PlannedLoop),
        ("temp-forwarding-call", "Step = {\n  G = v0 + v1\n  G, G + v0\n}\nrepeat(Step, 12, 1, 2)", Exercises.PlannedLoop),
        ("exported-temp", "Step(s) = {\n  K = 10 * 3\n  s + K\n}\nrepeat(Step, 25, 0)", Exercises.PlannedLoop),
        ("comparison-spine-child", "Step(s, b) = s + 1, (s < 3) == (b != false)\nrepeat(Step, 12, 0, true)", Exercises.PlannedLoop),
        ("string-constant-row", "Step(s, t) = s + 1, 'tag'\nrepeat(Step, 10, 0, 'start')", Exercises.PlannedLoop),
        ("string-operand", "Step(s, b) = s + 1, 'ab' == 'ab'\nrepeat(Step, 10, 0, false)", Exercises.PlannedLoop),
        ("alias-step", "Step(s) = s * 2 + 1\nA = Step\nrepeat(A, 12, 0)", Exercises.PlannedLoop),
        ("dotted-step", "Lib = {\n  Step(s) = s + 3\n}\nrepeat(Lib.Step, 12, 0)", Exercises.PlannedLoop),
        ("crosstalk-captured", "G(a) = {\n    Step = {\n        T = a + 1\n        n + if(a > 0, T, T() + 1)\n    }\n    Step.repeat(20, 0)\n}\nf(0) = G(1)\nf(k) = f(k - 1)\nf(6)", Exercises.PlannedLoop),
        ("crosstalk-callback-bound", "H(a) = {\n    Step = {\n        T = a * 2\n        n + if(a > 1, T, T())\n    }\n    Step.repeat(5, 0)\n}\nrange(1, 3).map(H).sum", Exercises.PlannedLoop),
        ("crosstalk-temp-alias-chain", "Step = {\n    C = 1\n    D = C\n    E = D\n    n + if(D > 0, E, E()) + E()\n}\nStep.repeat(30, 0)", Exercises.PlannedLoop),
        ("crosstalk-temp-call-chain", "Step = {\n    A = 7\n    B = A + 1\n    C = A() + B\n    n + B() + C()\n}\nStep.repeat(30, 0)", Exercises.PlannedLoop),
        ("crosstalk-string-temp-if", "Step = {\n    T = 'aaaa'\n    n + if(T == T(), 1, 0)\n}\nStep.repeat(40, 0)", Exercises.PlannedLoop),
        ("crosstalk-multi-state", "Step = {\n    T = a + b\n    T() + a, if(T() < 40, a, b)\n}\nStep.repeat(5, 1, 1) : 0", Exercises.PlannedLoop),
        ("while-nested-if-temp-call", "Step = {\n    T = 7\n    n + if(n < 30, if(n < 10, 1, 2), 3), T() > 5 and n < 40\n}\nStep.while(0)", Exercises.PlannedLoop),
        // Q-26 (2026-10-04): a nested loop written as a step row is ONE value, so the planned frame
        // keeps such a step planned where it formerly handed the iteration over to the generic loop;
        // the spread row still supplies several items and hands over. Both must charge exactly the
        // generic accounting, effects and draws included.
        ("nested-loop-row-one-slot", "Fib(x, y) = y, x + y\nStepN(p, n) = repeat(Fib, 1, n, n), n + 1\nrepeat(StepN, 20, 0, 0)", Exercises.PlannedLoop),
        ("nested-loop-row-spread-handover", "Fib(x, y) = y, x + y\nStepM(a, b) = { repeat(Fib, 1, a, b)* }\nrepeat(StepM, 12, 0, 1)", Exercises.PlannedLoop),
        ("nested-while-row-one-slot", "Body(a) = a + 1, a < 3\nStepW(p, n) = while(Body, n), n + 1\nrepeat(StepW, 15, 0, 0)", Exercises.PlannedLoop),
        ("nested-zero-slot-loop-row", "Drop(*xs) = { ()* }\nStepZ(p, n) = repeat(Drop, 1, n), n + 1\nrepeat(StepZ, 10, 0, 0)", Exercises.PlannedLoop),
        ("nested-loop-row-host-effects", "Fib(x, y) = y, x + y\nStepT(p, n) = repeat(Fib, 1, trace(n), n), n + 1\nrepeat(StepT, 8, 0, 0)", Exercises.PlannedLoop),
        ("nested-loop-row-seeded-random", "Fib(x, y) = y, x + y\nStepR(p, n) = repeat(Fib, 1, randomInt(0, 9), n), n + 1\nrepeat(StepR, 10, 0, 0)", Exercises.PlannedLoop),
    ];

    public static TheoryData<string> CorpusIds()
    {
        var data = new TheoryData<string>();
        foreach (var (id, _, _) in Corpus)
            data.Add(id);
        return data;
    }

    private static (string Source, Exercises Exercises) CaseOf(string id)
    {
        var found = Corpus.Single(entry => entry.Id == id);
        return (found.Source, found.Exercises);
    }

    [Theory]
    [MemberData(nameof(CorpusIds))]
    public void OptimizedStrategy_ChargesExactlyTheGenericAccounting(string caseId)
    {
        var (source, exercises) = CaseOf(caseId);
        var generic = Observe(source, optimize: false, seed: 7);
        var optimized = Observe(source, optimize: true, seed: 7);

        Assert.Equal(0, generic.LoopHits);
        Assert.Equal(0, generic.FusionHits);
        if (exercises.HasFlag(Exercises.PlannedLoop))
            Assert.True(optimized.LoopHits > 0, $"{caseId}: the planned loop strategy was not taken");
        if (exercises.HasFlag(Exercises.Fusion))
            Assert.True(optimized.FusionHits > 0, $"{caseId}: the fused pipeline strategy was not taken");

        Assert.Equal(generic.Accounting, optimized.Accounting);
    }

    /// <summary>
    /// Step budgets to sweep for a run that consumes <paramref name="steps"/> unlimited: every
    /// budget up to 400, then a stratified sample, always including the tight boundary
    /// (consumption − 2 … + 1), the unbounded <see cref="long.MaxValue"/>, and — through the
    /// stride — failure points inside long loops.
    /// </summary>
    internal static IEnumerable<long> StepBudgets(long steps)
    {
        var budgets = new SortedSet<long>();
        for (var t = 1L; t <= Math.Min(steps + 1, 400); t++)
            budgets.Add(t);
        var stride = Math.Max(1, steps / 150);
        for (var t = 1L; t <= steps + 1; t += stride)
            budgets.Add(t);
        foreach (var delta in new[] { -2L, -1L, 0L, 1L })
        {
            if (steps + delta >= 1)
                budgets.Add(steps + delta);
        }

        budgets.Add(long.MaxValue);
        return budgets;
    }

    /// <summary>
    /// The tight-boundary law: at EVERY step budget — so at every one of the run's step charges,
    /// whichever charge fails — the optimized and generic strategies report the same outcome, the
    /// same error tree (kind, payload, spans, context frames), the same counters at the failure
    /// point, and the same host effects before it. A strategy that charged a step at a different
    /// point (even with equal totals) disagrees at the budget where that charge fails.
    /// </summary>
    [Theory]
    [MemberData(nameof(CorpusIds))]
    public void StepBudgetSweep_FailsAtTheSamePointOnEveryStrategy(string caseId)
    {
        var (source, _) = CaseOf(caseId);
        var unlimited = Observe(source, optimize: false, seed: 7);
        foreach (var budget in StepBudgets(unlimited.Steps))
        {
            var limits = new EvaluationLimits { MaxSteps = budget };
            var generic = Observe(source, optimize: false, limits, seed: 7);
            var optimized = Observe(source, optimize: true, limits, seed: 7);
            Assert.True(
                generic.Accounting == optimized.Accounting,
                $"{caseId} MaxSteps={budget}:\n--- generic\n{generic.Accounting}\n--- optimized\n{optimized.Accounting}");
            if (budget >= unlimited.Steps)
                Assert.Equal(unlimited.Accounting, generic.Accounting);
            else
                Assert.Equal("err EvaluationStepLimitExceeded", generic.Outcome);
        }
    }

    /// <summary>
    /// The same law for the cumulative materialization budget: fused pipelines reserve the item
    /// slots of the collections they elide at the generic composition's own reservation points, so
    /// every item budget fails at the same point, after the same effects, with the same error.
    /// </summary>
    [Theory]
    [MemberData(nameof(CorpusIds))]
    public void MaterializationBudgetSweep_FailsAtTheSamePointOnEveryStrategy(string caseId)
    {
        var (source, _) = CaseOf(caseId);
        var unlimited = Observe(source, optimize: false, seed: 7);
        for (var budget = 1L; budget <= unlimited.Items + 1; budget++)
        {
            var limits = new EvaluationLimits { MaxMaterializedItems = budget };
            var generic = Observe(source, optimize: false, limits, seed: 7);
            var optimized = Observe(source, optimize: true, limits, seed: 7);
            Assert.True(
                generic.Accounting == optimized.Accounting,
                $"{caseId} MaxMaterializedItems={budget}:\n--- generic\n{generic.Accounting}\n--- optimized\n{optimized.Accounting}");
        }
    }

    /// <summary>
    /// String budgets: both strategies create every string at the same point (strings are never
    /// elided), so each cumulative and per-string budget fails identically — at its tight boundary
    /// and one below it.
    /// </summary>
    [Theory]
    [MemberData(nameof(CorpusIds))]
    public void StringBudgetSweep_FailsAtTheSamePointOnEveryStrategy(string caseId)
    {
        var (source, _) = CaseOf(caseId);
        var unlimited = Observe(source, optimize: false, seed: 7);
        var budgets = new List<EvaluationLimits>();
        for (var units = 0L; units <= unlimited.StringUnits + 1; units++)
            budgets.Add(new EvaluationLimits { MaxMaterializedStringChars = units });
        for (var length = 0; length <= 8; length++)
            budgets.Add(new EvaluationLimits { MaxStringLength = length });

        foreach (var limits in budgets)
        {
            var generic = Observe(source, optimize: false, limits, seed: 7);
            var optimized = Observe(source, optimize: true, limits, seed: 7);
            Assert.True(
                generic.Accounting == optimized.Accounting,
                $"{caseId} {limits}:\n--- generic\n{generic.Accounting}\n--- optimized\n{optimized.Accounting}");
        }
    }

    /// <summary>
    /// LONG-LOOP EXACTNESS. The bulk step is charged by the checkpoint that completes each block
    /// of <see cref="EvaluationBudget.ExpressionCheckpointsPerStep"/>, so a planned evaluation that
    /// omitted even one checkpoint per iteration drifts by one whole step every few hundred
    /// iterations (the 2026-10-03 prototype's 0.1–0.4 % residue). Iteration counts here walk the
    /// first three block boundaries one iteration at a time and add large non-multiples; the
    /// optimized run must equal the generic one in RAW checkpoints and steps at every count, and
    /// a step budget of exactly the consumption (and one less) must give the same verdict.
    /// </summary>
    [Theory]
    [InlineData("repeat({x + 1}, {N}, 0)", 6, 3)]
    [InlineData("Step(s) = {\n  T1 = s + 1\n  T2 = T1 + 1\n  T3 = T2 + 1\n  T4 = T3 + 1\n  T5 = T4 + 1\n  T6 = T5 + 1\n  T7 = T6 + 1\n  T8 = T7 + 1\n  T9 = T8 + 1\n  T10 = T9 + 1\n  T10\n}\nrepeat(Step, {N}, 0)", null, null)]
    [InlineData("Step(s) = if(s > 5, s - 1, s + 2) * 1\nrepeat(Step, {N}, 0)", null, null)]
    [InlineData("Step(s, t) = s + 1, if(0 < s < 1000000 != false, t + 1, t)\nrepeat(Step, {N}, 0, 0)", null, null)]
    [InlineData("Step(s) = s + 1, s < {N}\nwhile(Step, 0)", null, null)]
    public void LongLoops_ChargeExactlyTheGenericCheckpoints_AcrossBlockBoundaries(string template, int? perIteration, int? setup)
    {
        var counts = new SortedSet<long> { 1, 99_999 };
        // The iteration counts at which the generic checkpoint total crosses each of the first
        // three block boundaries, walked one iteration at a time on both sides.
        var oneIteration = Observe(template.Replace("{N}", "1"), optimize: false);
        var twoIterations = Observe(template.Replace("{N}", "2"), optimize: false);
        var slope = twoIterations.Checkpoints - oneIteration.Checkpoints;
        var intercept = oneIteration.Checkpoints - slope;
        if (perIteration is { } expectedSlope)
            Assert.Equal(expectedSlope, slope);
        if (setup is { } expectedSetup)
            Assert.Equal(expectedSetup, intercept);
        for (var block = 1; block <= 3; block++)
        {
            var crossing = (EvaluationBudget.ExpressionCheckpointsPerStep * (long)block - intercept) / slope;
            for (var n = crossing - 3; n <= crossing + 3; n++)
            {
                if (n >= 1)
                    counts.Add(n);
            }
        }

        foreach (var n in counts)
        {
            var source = template.Replace("{N}", n.ToString(System.Globalization.CultureInfo.InvariantCulture));
            var generic = Observe(source, optimize: false);
            var optimized = Observe(source, optimize: true);
            Assert.True(optimized.LoopHits == 1, $"N={n}: the planned loop was not taken");
            Assert.True(generic.Accounting == optimized.Accounting, $"N={n}:\n--- generic\n{generic.Accounting}\n--- optimized\n{optimized.Accounting}");

            foreach (var budget in new[] { generic.Steps - 1, generic.Steps })
            {
                if (budget < 1)
                    continue;
                var limits = new EvaluationLimits { MaxSteps = budget };
                var genericAtBudget = Observe(source, optimize: false, limits);
                var optimizedAtBudget = Observe(source, optimize: true, limits);
                Assert.True(genericAtBudget.Accounting == optimizedAtBudget.Accounting, $"N={n} MaxSteps={budget}");
                Assert.Equal(budget < generic.Steps, genericAtBudget.Outcome.StartsWith("err ", StringComparison.Ordinal));
            }
        }
    }

    /// <summary>
    /// A step limit that falls on the dispatch head of a PENDING initial-state cell — the loop's
    /// state supplied as a written block, demanded at the step's first read — fails inside that
    /// parameter read, and the generic read positions the limit at the READING reference
    /// (<c>Evaluator.DemandParameter</c> through <c>ParameterSlotFailure</c>). The planned state-slot
    /// read must pass the same reference span (found by the October 2026 independent review: it
    /// passed none, so the limit surfaced at the enclosing call instead). Root rows slide the
    /// 4096-checkpoint block boundary across the cell head; the state is read in value position, as
    /// an <c>if</c> argument, inside a temp body, and after being forwarded through a parameter.
    /// </summary>
    [Theory]
    [InlineData("Step(s) = s + 1\n{ROWS}repeat(Step, 1, { 7 })", 1L)]
    [InlineData("Step(s) = if(s > 0, s, 0)\n{ROWS}repeat(Step, 1, { 7 })", 1L)]
    [InlineData("Step(s) = {\n  T = s * 2\n  T + 1\n}\n{ROWS}repeat(Step, 1, { 7 })", 2L)]
    [InlineData("Step(s) = s + 1\nF(x) = repeat(Step, 1, x)\n{ROWS}F({ 7 })", 2L)]
    public void PendingBlockStateRead_PositionsAStepLimitLikeTheGenericRead(string template, long maxSteps)
    {
        var limits = new EvaluationLimits { MaxSteps = maxSteps };
        var stepLimitedInsideTheLoop = 0;
        for (var rows = 4070; rows <= 4100; rows++)
        {
            var source = template.Replace("{ROWS}", string.Concat(Enumerable.Repeat("1\n", rows)), StringComparison.Ordinal);
            var generic = Observe(source, optimize: false, limits);
            var optimized = Observe(source, optimize: true, limits);
            Assert.True(optimized.LoopHits == 1, $"rows={rows}: the planned loop was not taken");
            Assert.True(
                generic.Accounting == optimized.Accounting,
                $"rows={rows}:\n--- generic\n{generic.Accounting}\n--- optimized\n{optimized.Accounting}");
            if (generic.Outcome == "err EvaluationStepLimitExceeded" && generic.Checkpoints > rows + 1)
                stepLimitedInsideTheLoop++;
        }

        Assert.True(stepLimitedInsideTheLoop > 0, "the sweep never put the step limit inside the loop");
    }

    /// <summary>
    /// A planned temp CALL is the generic call only when that call TRANSPORTS every argument's
    /// existing binding (<c>LoopOptimizer.TransportsForwardedArguments</c>). The front end never
    /// produces a temp whose forwarded parameter would not transport — a temp only acquires the
    /// parameters its step forwards from its own state — so the guard is pinned from a prebuilt AST
    /// (the <see cref="EvaluatorDefensiveBranchTests"/> convention): the step <c>{ F(x) + 0 }</c> over
    /// a local <c>F(*x) = x + 0</c> whose one parameter COLLECTS. The generic call binds
    /// <c>x = [5]</c> and fails on <c>[5] + 0</c>; planning the call as a transport of the step's
    /// <c>x</c> would read the state value instead and succeed. The planned loop must keep that call
    /// generic and agree with the generic strategy on the outcome, the error tree and every counter.
    /// </summary>
    [Fact]
    public void PlannedTempCall_StaysGenericForAHostBuiltNonTransportingSignature()
    {
        var collectingTemp = new Algorithm.User(
            Parent: null,
            ParameterPatterns: [new CaptureParameterPattern("x", Kind: ParameterKind.Collecting)],
            Opens: [],
            Properties: [],
            Output: [new Expr.Binary(BinaryOp.Add, new Expr.Param("x"), new Expr.Num(0))]);
        var step = new Algorithm.User(
            Parent: null,
            ParameterPatterns: [new CaptureParameterPattern("x")],
            Opens: [],
            Properties: [new Property("F", collectingTemp)],
            Output: [new Expr.Binary(
                BinaryOp.Add,
                new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Param("x")])),
                new Expr.Num(0))]);
        var program = new Expr.AlgorithmExpr(new Algorithm.User(
            Parent: null,
            ParameterPatterns: [],
            Opens: [],
            Properties: [],
            Output: [new Expr.Call(
                new Expr.Resolve("repeat"),
                new OutputBundle([new Expr.AlgorithmExpr(step), new Expr.Num(3), new Expr.Num(5)]))]));

        string Describe(bool optimize, LoopOptimizationDiagnostics loops)
        {
            var (result, budget) = Evaluator.RunCountedObserved(program, enableOptimizations: optimize, loopDiagnostics: loops);
            return (result.IsError ? "err " + DescribeErrorTree(result.Error) : "ok " + SemanticExplorerHarness.Neutral(result.Value.Value))
                + $"\nsteps={budget.ConsumedSteps} checkpoints={budget.ConsumedExpressionCheckpoints} items={budget.MaterializedItems}";
        }

        var generic = Describe(optimize: false, new LoopOptimizationDiagnostics());
        var plannedDiagnostics = new LoopOptimizationDiagnostics();
        var optimized = Describe(optimize: true, plannedDiagnostics);
        Assert.StartsWith("err ", generic, StringComparison.Ordinal);
        Assert.Equal(generic, optimized);
        Assert.Equal(1, plannedDiagnostics.OptimizedLoopHits);
    }

    /// <summary>
    /// A runaway planned loop under a finite step budget stays on the planned strategy and stops
    /// with <see cref="EvalError.EvaluationStepLimitExceeded"/> exactly where the generic loop
    /// stops — the regression a per-iteration step charge exists to prevent (without it, removing
    /// the strategy switch let a runaway planned loop run forever under <c>MaxSteps</c>). A host
    /// cancellation token is the backstop that turns such a regression into a failure instead of a
    /// hang.
    /// </summary>
    [Theory]
    [InlineData("Step(s) = s + 1, true\nwhile(Step, 0)", 50_000L)]
    [InlineData("Step(s) = s + 1, s > -1\nwhile(Step, 0)", 777L)]
    [InlineData("Step(s) = s * 1\nrepeat(Step, 1000000000000000, 1)", 123_457L)]
    [InlineData("Step(s) = {\n  T = s + 1\n  if(T > 0, T, s)\n}\nrepeat(Step, 1000000000000000, 0)", 9_999L)]
    public void RunawayPlannedLoop_StopsAtTheGenericStepBudget(string source, long maxSteps)
    {
        var program = Program(source, operations: null);
        var limits = new EvaluationLimits { MaxSteps = maxSteps };
        EvalResult<Evaluator.CountedResult> Run(bool optimize, LoopOptimizationDiagnostics diagnostics, out EvaluationBudget budget)
        {
            using var backstop = new CancellationTokenSource(TimeSpan.FromSeconds(60));
            var (result, observed) = Evaluator.RunCountedObserved(
                program, limits, enableOptimizations: optimize, loopDiagnostics: diagnostics, cancellationToken: backstop.Token);
            budget = observed;
            return result;
        }

        var plannedDiagnostics = new LoopOptimizationDiagnostics();
        var planned = Run(optimize: true, plannedDiagnostics, out var plannedBudget);
        var generic = Run(optimize: false, new LoopOptimizationDiagnostics(), out var genericBudget);

        Assert.Equal(1, plannedDiagnostics.OptimizedLoopHits);
        Assert.Equal(0, plannedDiagnostics.OptimizedLoopFallbacks);
        Assert.Equal(maxSteps, Assert.IsType<EvalError.EvaluationStepLimitExceeded>(planned.Error).Limit);
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(generic.Error);
        Assert.Equal(DescribeErrorTree(generic.Error), DescribeErrorTree(planned.Error));
        Assert.Equal(maxSteps, plannedBudget.ConsumedSteps);
        Assert.Equal(genericBudget.ConsumedSteps, plannedBudget.ConsumedSteps);
        Assert.Equal(genericBudget.ConsumedExpressionCheckpoints, plannedBudget.ConsumedExpressionCheckpoints);
    }
}
