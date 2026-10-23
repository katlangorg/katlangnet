using KatLang.Evaluation;
namespace KatLang.Tests;

/// <summary>
/// SEC-02-FU2 single-comparison walk: one evaluator comparison (<see cref="Result.EvaluatorValueEquals"/>)
/// keeps a frame only for a parent with children still to visit and records each expanded pair once,
/// instead of the operation walk's frame per level and in-progress/final verdicts. It must decide the
/// same verdict with exactly the same charged units, charge boundaries (so cancellation checkpoints),
/// and expanded pairs as the operation walk of <c>contains</c>/<c>distinct</c> — its oracle here — and
/// the context-free <see cref="Result.ValueComparer"/>.
/// </summary>
public partial class SharedValueGraphComplexityTests
{
    private sealed record WalkObservation(bool Equal, long Units, long Charges, long Expansions, long Frames, string Boundaries);

    private static WalkObservation ObserveWalk(Result left, Result right, bool single)
    {
        var boundaries = new List<long>();
        ValueTraversalObservations observations = null!;
        observations = new ValueTraversalObservations { BeforeStructuralWorkCharge = _ => boundaries.Add(observations.StructuralWorkUnits) };
        var budget = EvaluationBudget.Create(limits: null);
        var verdict = single
            ? Result.EvaluatorValueEquals(left, right, budget, observations)
            : Result.CreateOperationComparer(budget, observations).TryEquals(left, right);
        Assert.False(verdict.IsError);
        Assert.Equal(observations.StructuralWorkUnits, budget.ConsumedStructuralWorkUnits);
        return new(verdict.Value, observations.StructuralWorkUnits, observations.StructuralWorkChargeCount,
            observations.EqualityPairExpansionCount, observations.EqualityFrameSuspensionCount, string.Join(",", boundaries));
    }

    /// <summary>A parent whose nested child comes FIRST: each level keeps a frame for its trailing leaf.</summary>
    private static Result HeadChain(int depth, decimal leaf) => Chain(depth, leaf);

    /// <summary>A parent whose nested child comes LAST: every descent is a tail descent.</summary>
    private static Result TailChain(int depth, decimal leaf)
    {
        var node = List(Atom(leaf));
        for (var i = 0; i < depth; i++)
            node = List(Atom(i), node);
        return node;
    }

    /// <summary>A complete binary tree of fresh nodes (no sharing); <paramref name="leaf"/> is its last leaf.</summary>
    private static Result Tree(int depth, decimal leaf, ref int counter)
    {
        if (depth == 0)
            return List(Atom(counter++), Atom(leaf));
        var first = Tree(depth - 1, 0, ref counter);
        var second = Tree(depth - 1, leaf, ref counter);
        return List(first, second);
    }

    private static Result IndependentTree(int depth, decimal leaf)
    {
        var counter = 0;
        return Tree(depth, leaf, ref counter);
    }

    /// <summary>Two references to one wide list per slot: the second is answered by the recorded first.</summary>
    private static Result RepeatedWide(decimal last)
    {
        var wide = List([.. Enumerable.Range(0, 40).Select(i => Atom(i == 39 ? last : i))]);
        return Seq(List(wide, wide), List(wide, Atom(1)), wide);
    }

    public static TheoryData<string> WalkShapes =>
    [
        "singleton", "singleton-mismatch", "head", "head-mismatch", "tail", "tail-mismatch",
        "tree", "tree-mismatch", "dag", "dag-mismatch", "wide", "wide-mismatch",
        "repeated-wide", "repeated-wide-mismatch", "kind-mismatch-deep", "long-string-deep", "long-string-deep-mismatch",
        "empty-children",
    ];

    private static (Result Left, Result Right) WalkShape(string shape) => shape switch
    {
        "singleton" => (SingletonChain(1_500, 1), SingletonChain(1_500, 1)),
        "singleton-mismatch" => (SingletonChain(1_500, 1), SingletonChain(1_500, 2)),
        "head" => (HeadChain(1_500, 1), HeadChain(1_500, 1)),
        "head-mismatch" => (HeadChain(1_500, 1), HeadChain(1_500, 2)),
        "tail" => (TailChain(1_500, 1), TailChain(1_500, 1)),
        "tail-mismatch" => (TailChain(1_500, 1), TailChain(1_500, 2)),
        "tree" => (IndependentTree(9, 1), IndependentTree(9, 1)),
        "tree-mismatch" => (IndependentTree(9, 1), IndependentTree(9, 2)),
        "dag" => (SharedDag(30), SharedDag(30)),
        "dag-mismatch" => (SharedDag(30), SharedDag(30, leafB: 3)),
        "wide" => (List([.. Enumerable.Range(0, 3_000).Select(i => Atom(i))]),
            List([.. Enumerable.Range(0, 3_000).Select(i => Atom(i))])),
        "wide-mismatch" => (List([.. Enumerable.Range(0, 3_000).Select(i => Atom(i))]),
            List([.. Enumerable.Range(0, 3_000).Select(i => Atom(i == 2_999 ? -1 : i))])),
        "repeated-wide" => (RepeatedWide(39), RepeatedWide(39)),
        "repeated-wide-mismatch" => (RepeatedWide(39), RepeatedWide(-1)),
        "kind-mismatch-deep" => (List(Atom(1), SingletonChain(300, 1)), List(Atom(1), Seq(SingletonChain(299, 1)))),
        "long-string-deep" => (TailChainOf(new Result.Str(new string('k', 5_000))), TailChainOf(new Result.Str(new string('k', 5_000)))),
        "long-string-deep-mismatch" => (TailChainOf(new Result.Str(new string('k', 5_000))), TailChainOf(new Result.Str(new string('k', 4_999) + "z"))),
        "empty-children" => (List(List(), Seq(), List(List(), Atom(1))), List(List(), Seq(), List(List(), Atom(1)))),
        _ => throw new ArgumentOutOfRangeException(nameof(shape)),
    };

    private static Result TailChainOf(Result leaf)
    {
        var node = List(leaf);
        for (var i = 0; i < 400; i++)
            node = List(Atom(i), node);
        return node;
    }

    [Theory]
    [MemberData(nameof(WalkShapes))]
    public void SingleComparisonWalk_MatchesTheOperationWalk_UnitForUnit(string shape)
    {
        var (left, right) = WalkShape(shape);
        var single = ObserveWalk(left, right, single: true);
        var operation = ObserveWalk(left, right, single: false);

        Assert.Equal(Result.ValueComparer.Equals(left, right), single.Equal);
        Assert.Equal(operation.Equal, single.Equal);
        // The same work, charged at the same unit boundaries — so the same cancellation checkpoints.
        Assert.Equal(operation.Units, single.Units);
        Assert.Equal(operation.Charges, single.Charges);
        Assert.Equal(operation.Boundaries, single.Boundaries);
        // The same distinct pairs expanded: no DAG path is ever re-walked.
        Assert.Equal(operation.Expansions, single.Expansions);
        // Fewer frames: only parents with children still to visit are suspended.
        Assert.True(single.Frames <= operation.Frames, $"{single.Frames} > {operation.Frames}");
    }

    [Fact]
    public void LongStringVerdicts_SurviveTheFirstStructuralMemoEntry()
    {
        // String payload verdicts and structural verdicts share the operation's dictionary. The
        // first string creates it before the first structural descent seeds a retained pair.
        var leftText = new Result.Str(new string('k', 16_449));
        var rightText = new Result.Str(new string('k', 16_449));
        var left = List(leftText, List(List(Atom(1))), leftText);
        var right = List(rightText, List(List(Atom(1))), rightText);
        var single = ObserveWalk(left, right, single: true);
        var operation = ObserveWalk(left, right, single: false);

        // Three root inspections and its completion, two nested inspections and completions,
        // and exactly ONE string payload read: the last root slot reads its retained verdict.
        Assert.Equal(8 + 16_449 / Result.ValueSemanticComparer.StringCharsPerUnit, single.Units);
        Assert.Equal(single.Units, operation.Units);
        Assert.Equal(single.Boundaries, operation.Boundaries);
        Assert.True(single.Equal);
        Assert.True(operation.Equal);
    }

    [Fact]
    public void LongStringVerdicts_SurviveWideStructureCompletion_AndLaterComparisons()
    {
        var leftText = new Result.Str(new string('k', 16_449));
        var rightText = new Result.Str(new string('k', 16_449));
        var left = List([leftText, .. Enumerable.Range(1, 15).Select(i => Atom(i))]);
        var right = List([rightText, .. Enumerable.Range(1, 15).Select(i => Atom(i))]);
        var observations = new ValueTraversalObservations();
        var comparer = Result.CreateOperationComparer(EvaluationBudget.Create(limits: null), observations);
        var initial = comparer.TryEquals(left, right);
        Assert.False(initial.IsError);
        Assert.True(initial.Value);
        var units = observations.StructuralWorkUnits;
        var charges = observations.StructuralWorkChargeCount;

        // Retaining the completed wide pair must preserve the payload verdict already recorded
        // by the same walk; a subsequent comparison of that string pair does no further work.
        var repeated = comparer.TryEquals(leftText, rightText);
        Assert.False(repeated.IsError);
        Assert.True(repeated.Value);
        Assert.Equal(units, observations.StructuralWorkUnits);
        Assert.Equal(charges, observations.StructuralWorkChargeCount);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void SingleComparisonWalk_SuspendsNoFrame_ForATailDescentChain(bool equal)
    {
        foreach (var (left, right, depth) in new[]
        {
            (SingletonChain(2_000, 1), SingletonChain(2_000, equal ? 1 : 2), 2_000),
            (TailChain(2_000, 1), TailChain(2_000, equal ? 1 : 2), 2_001),
        })
        {
            var single = ObserveWalk(left, right, single: true);
            var operation = ObserveWalk(left, right, single: false);
            Assert.Equal(equal, single.Equal);
            Assert.Equal(0, single.Frames);
            Assert.Equal(depth - 1, operation.Frames);
            Assert.Equal(depth, single.Expansions);
            // Every logical completion (equal) or abandoned level (mismatch) is still one unit.
            Assert.Equal(operation.Units, single.Units);
        }
    }

    [Fact]
    public void SingleComparisonWalk_KeepsFramesProportionalToDepth_NeverToSiblings()
    {
        // A head chain keeps one frame per level (each has a trailing leaf); a wide flat pair none.
        var head = ObserveWalk(HeadChain(1_000, 1), HeadChain(1_000, 1), single: true);
        Assert.Equal(1_000, head.Frames);
        var wide = ObserveWalk(List([.. Enumerable.Range(0, 5_000).Select(i => Atom(i))]), List([.. Enumerable.Range(0, 5_000).Select(i => Atom(i))]), single: true);
        Assert.Equal(0, wide.Frames);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void SingleComparisonWalk_IsRefusedByAFiniteBudget_WhileUnwindingFoldedLevels(bool equal)
    {
        // 12,288 levels descended with no frame: 12,288 inspections, then 12,288 completions (equal)
        // or abandoned levels (mismatch) — six steps of structural work in all. Four steps cover the
        // descent and part of the unwind, so the refusal falls inside the folded unwind.
        const int depth = 3 * EvaluationBudget.StructuralWorkUnitsPerStep;
        var left = SingletonChain(depth, 1);
        var right = SingletonChain(depth, equal ? 1 : 2);
        var unlimited = ObserveWalk(left, right, single: true);
        Assert.True(unlimited.Units >= 2L * depth, unlimited.Units.ToString());

        var observations = new ValueTraversalObservations();
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxSteps = 4 });
        var refused = Result.EvaluatorValueEquals(left, right, budget, observations);
        Assert.True(refused.IsError);
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(refused.Error);
        Assert.Equal(depth, observations.EqualityPairExpansionCount);
        Assert.Equal(0, observations.EqualityFrameSuspensionCount);
        // Refused after the whole descent, before the unwind finished.
        Assert.True(observations.StructuralWorkUnits > depth, observations.StructuralWorkUnits.ToString());
        Assert.True(observations.StructuralWorkUnits < unlimited.Units, observations.StructuralWorkUnits.ToString());
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(budget.CheckContinuation());
    }

    [Fact]
    public void SingleComparison_ReturnsTheRefusalOfItsFinalPartialBatch()
    {
        var budget = EvaluationBudget.Create(new EvaluationLimits { MaxSteps = 1 });
        Assert.Null(budget.TryChargeStructuralWork(EvaluationBudget.StructuralWorkUnitsPerStep - 1));
        Assert.Null(budget.TryChargeStep());
        var observations = new ValueTraversalObservations();
        // Two units (one inspection, one completion) stay pending until the comparison's final flush.
        var result = Result.EvaluatorValueEquals(List(Atom(1)), List(Atom(1)), budget, observations);
        Assert.True(result.IsError);
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(result.Error);
        Assert.Equal(1, observations.StructuralWorkChargeCount);
        Assert.Equal(2, observations.StructuralWorkUnits);
    }

    [Fact]
    public async Task SingleComparisonWalk_OnAliasedSelfReferentialGraphs_Terminates()
    {
        // The invariant-violating probe of Operation_AliasedSelfReferentialGraphTerminates, through
        // the single-comparison walk: its expanded-pair record keeps it total.
        var storage = new Result[1];
        var cyclic = Result.ListValue.TakeOwnership(storage);
        storage[0] = cyclic;
        var otherStorage = new Result[1];
        var otherCyclic = Result.ListValue.TakeOwnership(otherStorage);
        otherStorage[0] = otherCyclic;

        var walk = Task.Run(() =>
        {
            Assert.False(Result.EvaluatorValueEquals(cyclic, otherCyclic, EvaluationBudget.Create(limits: null), observations: null).IsError);
            Assert.False(Result.EvaluatorValueEquals(List(cyclic, Atom(1)), List(otherCyclic, Atom(1)), EvaluationBudget.Create(limits: null), observations: null).IsError);
        });
        var finished = await Task.WhenAny(walk, Task.Delay(TimeSpan.FromSeconds(30)));
        Assert.True(ReferenceEquals(finished, walk), "the single-comparison walk did not terminate on an aliased graph");
        await walk;
    }

    // ── Task A: the in-place scalar decisions are exactly the comparer's ───────────────────

    [Fact]
    public void ScalarFastPath_DecidesExactlyThePublicComparersVerdict_WithoutCharging()
    {
        var nan = new Result.Atom(System.Numerics.Decimal128.NaN);
        Result[] scalars =
        [
            new Result.Atom(1), new Result.Atom(System.Numerics.Decimal128.Parse("1.00")), new Result.Atom(2),
            nan, new Result.Atom(System.Numerics.Decimal128.NaN),
            new Result.Atom(System.Numerics.Decimal128.Parse("0")), new Result.Atom(System.Numerics.Decimal128.Parse("-0")),
            new Result.Atom(System.Numerics.Decimal128.PositiveInfinity), new Result.Atom(System.Numerics.Decimal128.NegativeInfinity),
            new Result.Bool(true), new Result.Bool(true), new Result.Bool(false),
            new Result.Str("1"), new Result.Str("true"), List(), Seq(), List(Atom(1)), Seq(Atom(1)),
        ];
        var observations = new ValueTraversalObservations();
        var budget = EvaluationBudget.Create(limits: null);
        foreach (var left in scalars)
        {
            foreach (var right in scalars)
            {
                var verdict = Result.EvaluatorValueEquals(left, right, budget, observations);
                Assert.False(verdict.IsError);
                Assert.Equal(Result.ValueComparer.Equals(left, right), verdict.Value);
                Assert.Equal(Result.ValueComparer.Equals(right, left), Result.EvaluatorValueEquals(right, left, budget, observations).Value);
            }
        }

        // NaN is one value, quantum and the sign of zero are ignored, a number never equals a Boolean.
        Assert.True(Result.EvaluatorValueEquals(nan, nan, budget, observations).Value);
        Assert.True(Result.EvaluatorValueEquals(scalars[0], scalars[1], budget, observations).Value);
        Assert.True(Result.EvaluatorValueEquals(scalars[5], scalars[6], budget, observations).Value);
        Assert.False(Result.EvaluatorValueEquals(new Result.Atom(1), new Result.Bool(true), budget, observations).Value);
        Assert.False(Result.EvaluatorValueEquals(new Result.Bool(true), new Result.Atom(1), budget, observations).Value);
        // Every pair here is decided in O(1): nothing was walked or charged.
        Assert.Equal(0, observations.EqualityPairExpansionCount);
        Assert.Equal(0, observations.StructuralWorkChargeCount);
    }

    [Fact]
    public void ScalarFastPath_AllocatesNothing_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var budget = EvaluationBudget.Create(limits: null);
        (Result Left, Result Right)[] pairs =
        [
            (new Result.Atom(42), new Result.Atom(42)),
            (new Result.Atom(42), new Result.Atom(43)),
            (new Result.Atom(System.Numerics.Decimal128.NaN), new Result.Atom(System.Numerics.Decimal128.NaN)),
            (new Result.Bool(true), new Result.Bool(true)),
            (new Result.Atom(1), new Result.Bool(true)),
            (new Result.Str("short text"), new Result.Str(new string("short text".ToCharArray()))),
        ];
        foreach (var (left, right) in pairs)
            _ = Result.EvaluatorValueEquals(left, right, budget, observations: null);

        var before = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < 1_000; i++)
        {
            foreach (var (left, right) in pairs)
                _ = Result.EvaluatorValueEquals(left, right, budget, observations: null);
        }

        Assert.Equal(0, GC.GetAllocatedBytesForCurrentThread() - before);
        GcIsolatedAllocation.Complete();
    }
}
