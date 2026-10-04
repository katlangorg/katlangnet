using System.Collections.Immutable;

namespace KatLang.ParserFuzz;

/// <summary>
/// One reviewed optimizer-versus-generic source, together with the optimizer path its OPTIMIZED
/// execution must be proven to take.
/// </summary>
/// <param name="RequiredPaths">
/// Paths the optimized run must show. A template is not admitted as an optimizer comparison
/// unless the optimizer really selected the intended path — proving that an outer loop WRAPPER
/// ran is explicitly not enough, which is why <c>LoopExecutions</c> alone is never a requirement.
/// </param>
internal sealed record MetamorphicOptimizerSource(
    string Id,
    string Source,
    MetamorphicOptimizerPath RequiredPaths);

/// <summary>
/// Phase 3 Group A — the SAME trusted source executed twice, once with the optimizers enabled
/// and once with them disabled.
///
/// <code>
/// left:  optimizations ON   (the optimized strategies)
/// right: optimizations OFF  (the generic reference execution)
/// </code>
///
/// <para><b>Equivalence argument.</b> There is nothing to rewrite: both members are the same
/// source text. Only the execution POLICY differs, and the runtime documents the optimizers as
/// meaning-preserving, so semantic equality is the contract itself rather than an inference about
/// two spellings. The optimizers change how the work is EXECUTED, never how it is ACCOUNTED: every
/// strategy charges every budget identically (Q-09b, 2026-10-04 — limits observe a run and never
/// choose its strategy), so the operational relation is
/// <see cref="MetamorphicOperationalRelation.ExactObservedWorkEqual"/>: materialized items, string
/// units, evaluation steps, and peak dynamic depth all equal (the optimizer EVIDENCE differs by
/// design, so it is not compared). (It was the directional
/// <c>WorkNeverIncreases</c> while planned loops charged no per-iteration step and fused pipelines
/// reserved nothing.)</para>
///
/// <para><b>Direction is fixed and explicit.</b> The optimized run is always the LEFT member, and
/// the fingerprint records the direction. What the payload varies instead is the EXECUTION ORDER:
/// which of the two policies runs first. Every relation here must hold both ways round, so a
/// policy that only agrees when it runs on a clean process is a state leak rather than an
/// optimization.</para>
///
/// <para><b>Why the limit policy is nearly fixed.</b> Only the modes this mixed loop/sequence
/// table was measured under are generated. (A configured cumulative item, step, or string budget
/// once disabled fusion or loop planning and so could not satisfy the optimizer-hit requirement;
/// since Q-09b none does, and <c>LimitConfigurationTransparencyTests</c> pins that directly.)
/// The per-collection ceiling is kept because the runtime
/// explicitly promises it is optimizer-INDEPENDENT (a fused pipeline reserves, and so rejects,
/// exactly the collection sizes a generic one does —
/// <c>EvaluationBudget.TryReserveCollection</c>), which makes it the budget worth comparing
/// here.</para>
/// </summary>
internal static class MetamorphicOptimizerTemplate
{
    private const int SourceDimension = 0;
    private const int OrderDimension = 1;

    private const string Loop = MetamorphicTables.NamePrefix + "Step";
    private const string Pred = MetamorphicTables.NamePrefix + "Even";
    private const string Double = MetamorphicTables.DoubleCallback;

    /// <summary>A loop plan was selected AND at least one planned expression executed inside it.</summary>
    private const MetamorphicOptimizerPath Planned =
        MetamorphicOptimizerPath.OptimizedLoopSelected | MetamorphicOptimizerPath.PlannedExpressionExecuted;

    /// <summary>
    /// A loop plan was selected, but the body still fell back to a generic expression evaluation
    /// inside it — the distinction between "the optimizer ran" and "the optimizer ran the plan".
    /// </summary>
    private const MetamorphicOptimizerPath PartiallyPlanned =
        MetamorphicOptimizerPath.OptimizedLoopSelected | MetamorphicOptimizerPath.GenericExpressionInsideOptimizedLoop;

    private const MetamorphicOptimizerPath Fused = MetamorphicOptimizerPath.FusedPipelineExecuted;

    private const MetamorphicOptimizerPath ShortCircuit = MetamorphicOptimizerPath.LoopShortCircuited;

    private const MetamorphicOptimizerPath FellBack =
        MetamorphicOptimizerPath.LoopFallbackExecuted | MetamorphicOptimizerPath.GenericLoopExecuted;

    /// <summary>
    /// Reviewed sources. Each one's declared path is MEASURED, not assumed: the committed sweep
    /// (<c>MetamorphicPhase3FamilyTests.OptimizerSources_TakeExactlyTheDeclaredPath</c>) runs
    /// every entry and fails if the optimized execution does not show it, so the table cannot
    /// drift away from what the optimizers actually do.
    /// </summary>
    internal static readonly ImmutableArray<MetamorphicOptimizerSource> Sources =
    [
        // ── Loops: the zero-iteration short circuit, BEFORE the optimizer ──────
        // `RepeatLoopCounted` returns the initial state when the count is zero, before the
        // optimizer flag, the shape check, or the state-slot check are reached. Declaring it as
        // an optimizer hit would be false; declaring the short circuit is what is actually proven.
        new("repeat-zero-iterations", $"{Loop} = x + 1\n{Loop}.repeat(0, 0)", ShortCircuit),

        // ── Loops: the loop optimizer selecting a plan ─────────────────────────
        new("repeat-one-iteration", $"{Loop} = x + 1\n{Loop}.repeat(1, 0)", Planned),
        new("repeat-many-iterations", $"{Loop} = x + 1\n{Loop}.repeat(12, 0)", Planned),
        new("repeat-multi-slot-state", $"{Loop} = a + 1, total + a\n{Loop}.repeat(6, 1, 0):1", Planned),
        new("while-scalar-state", $"{Loop} = x - 1, x > 1\n{Loop}.while(9)", Planned),
        new("while-multi-slot-state", $"{Loop} = n - 1, total + n, n > 1\n{Loop}.while(8, 0):1", Planned),
        new("repeat-conditional-body",
            $"{Loop} = x + if(x > 3, 2, 1)\n{Loop}.repeat(7, 0)", Planned),
        new("repeat-boolean-state", $"{Loop}(b) = not b\n{Loop}.repeat(7, false)", Planned),
        new("while-boolean-state-transition",
            $"{Loop}(x) = if(x == true, 0, true), x != 0\n{Loop}.while(true)", Planned),
        new("repeat-boolean-equality", $"{Loop}(b) = b == 1\n{Loop}.repeat(3, true)", Planned),

        // ── Loops: suspended initial cells remain demandable in a plan ──────────
        new("repeat-list-state", $"{Loop} = xs\n{Loop}.repeat(3, [1, 2])", Planned),
        new("repeat-sequence-state", $"{Loop} = xs\n{Loop}.repeat(3, (1, 2))", Planned),
        new("repeat-string-state", $"{Loop} = xs\n{Loop}.repeat(2, 'ab')", Planned),
        new("repeat-nested-list-state", $"{Loop} = xs\n{Loop}.repeat(2, [[1, 2], [3]])", Planned),
        new("repeat-empty-list-state", $"{Loop} = xs\n{Loop}.repeat(2, [])", Planned),

        new("repeat-clause-family-step", $"{Loop}(0) = 0\n{Loop}(n) = n + 1\n{Loop}.repeat(2, 1)", FellBack),

        // ── Sequence-pipeline fusion ───────────────────────────────────────────
        new("fuse-dotted-range-filter-count",
            $"{Pred}(x) = x mod 2 == 0\nrange(1, 12).filter({Pred}).count", Fused),
        new("fuse-plain-range-filter-count",
            $"{Pred}(x) = x mod 2 == 0\ncount(range(1, 12).filter({Pred}))", Fused),
        new("fuse-descending-range",
            $"{Pred}(x) = x mod 2 == 0\nrange(12, 1).filter({Pred}).count", Fused),
        new("fuse-singleton-range",
            $"{Pred}(x) = x == 5\nrange(5, 5).filter({Pred}).count", Fused),
        new("fuse-list-property-source",
            $"{MetamorphicTables.ReceiverProperty} = [1, 2, 3, 4]\n{Pred}(x) = x > 2\n" +
            $"{MetamorphicTables.ReceiverProperty}.filter({Pred}).count", Fused),
        new("fuse-empty-list-source",
            $"{MetamorphicTables.ReceiverProperty} = []\n{Pred}(x) = x > 2\n" +
            $"{MetamorphicTables.ReceiverProperty}.filter({Pred}).count", Fused),
        new("fuse-nested-list-source",
            $"{MetamorphicTables.ReceiverProperty} = [[1, 2], [3]]\n{Pred}(x) = x.count > 1\n" +
            $"{MetamorphicTables.ReceiverProperty}.filter({Pred}).count", Fused),
        new("fuse-string-list-source",
            $"{MetamorphicTables.ReceiverProperty} = ['abc', 'de']\n{Pred}(x) = x.count > 0\n" +
            $"{MetamorphicTables.ReceiverProperty}.filter({Pred}).count", Fused),
        new("fuse-sequence-source",
            $"{MetamorphicTables.ReceiverProperty} = (1, 2, 3, 4)\n{Pred}(x) = x > 2\n" +
            $"{MetamorphicTables.ReceiverProperty}.filter({Pred}).count", Fused),

        // ── Fusion crossed with the rest of the collection surface ─────────────
        new("fuse-then-collection-builtins",
            $"{Pred}(x) = x mod 2 == 0\n{Double}(x) = x * 2\n" +
            $"range(1, 10).filter({Pred}).count, [1, 2, 3].map({Double}), [3, 1, 2].order, " +
            "[3, 1, 2].orderDesc, [1, 1, 2].distinct, take([1, 2, 3], 2), skip([1, 2, 3], 1), sum([1, 2, 3])",
            Fused),
        new("fuse-then-callback-pipelines",
            $"{Pred}(x) = x mod 2 == 0\n{Double}(x) = x * 2\n{MetamorphicTables.AddCallback}(a, b) = a + b\n" +
            $"range(1, 8).filter({Pred}).count, [[1, 2], [3]].map(count), ['ab', 'cde'].map(count), " +
            $"[1, 2, 3].map({Double}), reduce([1, 2, 3], {MetamorphicTables.AddCallback}, 0)",
            Fused),
        new("fuse-then-value-shapes",
            $"{Pred}(x) = x mod 2 == 0\n" +
            $"range(1, 6).filter({Pred}).count, 7, 'ab', [], [7], [[1, 2], [3, 4]], (1, 2, 3), " +
            "([1, 2], [3, 4]), ()",
            Fused),
        new("fuse-then-callback-error",
            $"{Pred}(x) = x mod 2 == 0\nrange(1, 8).filter({Pred}).count, [()].map(min)",
            Fused),

        // ── Both optimizers in one program ─────────────────────────────────────
        new("loop-and-fusion",
            $"{Pred}(x) = x mod 2 == 0\n{Loop} = x + 1\n" +
            $"{Loop}.repeat(5, 0), range(1, 10).filter({Pred}).count",
            Planned | Fused),
        new("loop-with-string-constant",
            $"{Loop} = x + count('ab')\n{Loop}.repeat(4, 0)", PartiallyPlanned),
        new("loop-with-user-callback-body",
            $"{Double}(x) = x * 2\n{Loop} = {Double}(x)\n{Loop}.repeat(4, 1)", PartiallyPlanned),
    ];

    internal static int SourceCount => Sources.Length;

    /// <summary>Execution orders this family generates: left first, then right first.</summary>
    internal static readonly ImmutableArray<MetamorphicExecutionOrder> Orders =
        [MetamorphicExecutionOrder.LeftFirst, MetamorphicExecutionOrder.RightFirst];

    /// <summary>
    /// The limit modes this family may run under. Only fusion-neutral budgets are generated;
    /// see the type doc for why a cumulative budget cannot be used here.
    /// </summary>
    internal static readonly ImmutableArray<MetamorphicLimitMode> LimitModes =
    [
        MetamorphicLimitMode.Default,
        MetamorphicLimitMode.PerCollectionItems,
        MetamorphicLimitMode.Generous,
    ];

    internal static MetamorphicOptimizerSource SourceOf(MetamorphicParameters parameters)
        => Sources[parameters.Extra(SourceDimension)];

    internal static MetamorphicExecutionOrder OrderOf(MetamorphicParameters parameters)
        => Orders[parameters.Extra(OrderDimension)];

    internal static MetamorphicParameters Normalize(MetamorphicParameters parameters) => parameters;

    internal static MetamorphicPrecondition Validate(MetamorphicParameters parameters)
    {
        var source = SourceOf(parameters);

        if (source.RequiredPaths == MetamorphicOptimizerPath.None)
            return MetamorphicPrecondition.Rejected("optimizer-source-declares-no-optimizer-path");

        // A source that declares a fallback path is still an optimizer comparison — the optimizer
        // ran and chose the generic route — but it must not ALSO claim to have been optimized,
        // or the template would be asserting two different executions at once.
        if (source.RequiredPaths.HasFlag(MetamorphicOptimizerPath.LoopFallbackExecuted)
            && source.RequiredPaths.HasFlag(MetamorphicOptimizerPath.OptimizedLoopSelected))
        {
            return MetamorphicPrecondition.Rejected("optimizer-source-declares-both-plan-and-fallback");
        }

        return MetamorphicPrecondition.Ok;
    }

    internal static string DescribeVariant(MetamorphicParameters parameters)
    {
        var source = SourceOf(parameters);
        // The flags enum renders with ", " separators; the fingerprint uses spaces as its own
        // delimiter, so the path set is written without them.
        return $"optimizerSource={source.Id} " +
               $"expectedPath={source.RequiredPaths.ToString().Replace(", ", "+", StringComparison.Ordinal)} " +
               $"direction=optimized-left order={OrderOf(parameters)}";
    }

    internal static MetamorphicCase Build(MetamorphicParameters parameters)
    {
        var source = SourceOf(parameters);

        var testCase = MetamorphicCaseFactory.Create(
            parameters,
            source.Source,
            source.Source,
            Validate(parameters),
            $"optimizer source '{source.Id}' expected to take {source.RequiredPaths}");

        return testCase with
        {
            // Same source, different policy. The optimized member is always the LEFT one.
            LeftProfile = MetamorphicExecutionProfile.Observed(testCase.Limits, enableOptimizations: true),
            RightProfile = MetamorphicExecutionProfile.Observed(testCase.Limits, enableOptimizations: false),
            ExecutionOrder = OrderOf(parameters),
            LeftEvidence = new MetamorphicSideEvidence(RequiredPaths: source.RequiredPaths),
            // The generic side must be genuinely generic: no plan selected, nothing fused.
            RightEvidence = new MetamorphicSideEvidence(
                ForbiddenPaths: MetamorphicOptimizerPath.OptimizedLoopSelected
                    | MetamorphicOptimizerPath.PlannedExpressionExecuted
                    | MetamorphicOptimizerPath.FusedPipelineExecuted),
        };
    }
}
