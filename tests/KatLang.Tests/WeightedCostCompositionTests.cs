namespace KatLang.Tests;

/// <summary>
/// One composable weighted evaluation mechanism, as measured against the PRODUCTION
/// cost model (<c>AstStructuralPreflight</c>). <see cref="DeclaredWeight"/> is a pin,
/// not a source of truth:
/// <see cref="WeightedCostCompositionTests.MechanismTable_LayerWeightsMatchProduction"/>
/// measures each layer's marginal cost through the production preflight and fails if a
/// production weight changes without this table being updated.
/// </summary>
/// <param name="Name">Diagnostic name reported on every failure.</param>
/// <param name="DeclaredWeight">Expected marginal production cost of ONE layer.</param>
/// <param name="Wrap">Wraps one layer of this mechanism around an inner expression.</param>
internal sealed record WeightedMechanism(
    string Name,
    int DeclaredWeight,
    Func<Expr, Expr> Wrap);

/// <summary>
/// The COST-MODEL COMPOSITION MATRIX.
///
/// <para><b>Why this family exists.</b> Every weighted mechanism represented by
/// <c>AstStructuralPreflight</c>'s node/transition costs was calibrated against a PURE chain
/// of its own kind, and each pure-chain calibration is pinned by
/// <see cref="AstStructuralDepthTests"/>. Two defects were nevertheless found by hand
/// where the per-kind premise held and the COMPOSITION did not:</para>
/// <list type="bullet">
///   <item>the internal sequence-join kinds were free "because every consumer walks
///   their spines iteratively" — true WITHIN one kind, false for the
///   spread-of-construct ALTERNATION, which re-enters generic evaluation recursively
///   and overflowed a 1 MiB stack while the preflight charged zero (now 8 units);</item>
///   <item>nested builtin calls weighed 2 units per level but consumed ~11 CLR frames
///   per level and charged no dynamic depth at all, so the ceiling admitted trees that
///   terminated the process (now bounded by the depth-charged
///   <c>EvaluationBudget.TryEnterArgumentEvaluation</c> chokepoint).</item>
/// </list>
///
/// <para><b>The invariant under test is not the arithmetic.</b> It is: if a composition
/// is ACCEPTED by the production preflight at the documented ceiling, its actual
/// execution must be safe — every evaluator entry point must return a value or a
/// structured resource <see cref="EvalError"/>, never a process death, an unhandled CLR
/// exception, or a strategy disagreement caused solely by composition.</para>
///
/// <para><b>Host-constructed ASTs are the primary generator</b>, deliberately: the
/// source-driven layers (parser fuzz, spec corpus, editor fuzz) were already strong when
/// both defects above were found, because both lived in host-built shapes near a resource
/// boundary. Some generated compositions are shapes the PARSER would reject (a spread used
/// as an index target, for instance); host construction is the documented external origin
/// mechanism for exactly these nodes, and the evaluator gates — not the parser — are what
/// must stay safe.</para>
///
/// <para><b>Semantic neutrality.</b> Every mechanism layer is a FIXED POINT at the scalar
/// <c>1</c>, so an arbitrarily deep composition of any mixture still evaluates to exactly
/// <c>1</c>. That makes the value assertion uniform across the matrix and makes a
/// degenerate builder — one whose layers are elided, short-circuited, or never evaluated —
/// detectable instead of silently passing. See
/// <see cref="MechanismTable_EachLayerPerformsRealWork"/>.</para>
/// </summary>
public class WeightedCostCompositionTests
{
    /// <summary>The documented ceiling every evaluator entry point enforces.</summary>
    private const int Ceiling = EvaluationLimits.MaxSupportedAstDepth;

    private const AstConsumerProfile EvaluatorProfile =
        AstConsumerProfile.EvaluatorIterativeJoinSpines;

    /// <summary>The terminal expression every composition bottoms out in (cost 1, value 1).</summary>
    internal static Expr Base() => new Expr.Num(1);

    // ── The mechanism table ──────────────────────────────────────────────────
    //
    // Each Wrap is a FIXED POINT at the scalar 1 and performs real dispatch:
    //   Index         x:0             projection through the iterative spine machine
    //   Capture       (x)             written value boundary
    //   Call          sum(x)          real builtin call; the post-binding collection view
    //                                 of a scalar is a one-item collection, so sum(1) == 1
    //   AlgorithmExpr {x}             scope-owning algorithm expression (1 + Algorithm 1)
    //   DotCall       x.count         receiver injection -> count(x) == 1, NO written args
    //   ArgsDotCall   x.contains(1)   receiver injection -> contains(x, 1) == 1, WITH args
    //   Alternation   (x, ())*        spread-of-construct: the one join shape that recurses
    //
    // Join (SequenceConstruct, weight ZERO) is deliberately NOT in this table: a zero-cost
    // mechanism can never saturate a cost ceiling, so it cannot participate in the
    // saturating matrix. It is covered separately, and more aggressively, by the
    // ZeroWeightJoins_* tests below.

    internal static readonly WeightedMechanism Index =
        new("Index", 1, inner => new Expr.Index(inner, new Expr.Num(0)));

    internal static readonly WeightedMechanism Capture =
        new("Capture", 2, inner => new Expr.Capture([inner]));

    internal static readonly WeightedMechanism Call =
        new("Call", 2, inner => new Expr.Call(new Expr.Resolve("sum"), [inner]));

    internal static readonly WeightedMechanism AlgorithmExpr =
        new("AlgorithmExpr", 2, inner =>
            new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [inner])));

    internal static readonly WeightedMechanism DotCall =
        new("DotCall", 3, inner => new Expr.DotCall(inner, "count", null));

    internal static readonly WeightedMechanism ArgsDotCall =
        new("ArgsDotCall", 4, inner => new Expr.DotCall(inner, "contains", [new Expr.Num(1)]));

    internal static readonly WeightedMechanism Alternation =
        new("Alternation", 8, inner =>
            new Expr.SequenceSpread(new Expr.SequenceConstruct(inner, new Expr.EmptySequence(0))));

    /// <summary>The ZERO-weight mechanism, excluded from the saturating matrix.</summary>
    internal static readonly WeightedMechanism Join =
        new("Join", 0, inner => new Expr.SequenceConstruct(inner, new Expr.EmptySequence(0)));

    internal static readonly IReadOnlyList<WeightedMechanism> Mechanisms =
        [Index, Capture, Call, AlgorithmExpr, DotCall, ArgsDotCall, Alternation];

    internal static Expr BinarySpineWithCompositeSideBranches(int layers)
    {
        var tree = Base();
        for (var i = 0; i < layers; i++)
        {
            tree = new Expr.Binary(
                BinaryOp.Add,
                tree,
                new Expr.Capture([new Expr.Num(0)]));
        }

        return tree;
    }

    internal static Expr JoinSpineWithCompositeSideBranches(int layers)
    {
        var tree = Base();
        for (var i = 0; i < layers; i++)
        {
            tree = new Expr.SequenceConstruct(
                tree,
                new Expr.Capture([new Expr.EmptySequence(0)]));
        }

        return tree;
    }

    private static WeightedMechanism ByName(string name)
        => Mechanisms.Append(Join).Single(mechanism => mechanism.Name == name);

    private static bool HasOutermostMechanism(Expr tree, WeightedMechanism mechanism)
        => mechanism.Name switch
        {
            "Index" => tree is Expr.Index,
            "Capture" => tree is Expr.Capture,
            "Call" => tree is Expr.Call,
            "AlgorithmExpr" => tree is Expr.AlgorithmExpr,
            "DotCall" => tree is Expr.DotCall { Args: null },
            "ArgsDotCall" => tree is Expr.DotCall { Args: not null },
            "Alternation" => tree is Expr.SequenceSpread(Expr.SequenceConstruct),
            "Join" => tree is Expr.SequenceConstruct,
            _ => throw new InvalidOperationException($"Unknown mechanism '{mechanism.Name}'."),
        };

    // ── Production-derived cost measurement ──────────────────────────────────

    /// <summary>
    /// The EXACT production structural cost of one tree, derived from the production
    /// preflight alone: acceptance is monotone in <c>maxDepth</c>, so the cost is the
    /// smallest limit that accepts. No weight arithmetic is duplicated here, which is what
    /// lets the matrix ASSERT additivity rather than assume it. Returns <c>Ceiling + 1</c>
    /// for trees the ceiling itself rejects — the measurable range stops there, because
    /// <c>Check</c> clamps any larger request down to the ceiling.
    /// </summary>
    internal static int MeasureCost(object root)
        => MeasureCost(root, Ceiling, EvaluatorProfile);

    private static int MeasureCost(object root, int ceiling, AstConsumerProfile profile)
    {
        if (AstStructuralPreflight.Check(root, ceiling, profile) is not null)
            return ceiling + 1;

        var low = 1;
        var high = ceiling;
        while (low < high)
        {
            var mid = low + ((high - low) / 2);
            if (AstStructuralPreflight.Check(root, mid, profile) is null)
                high = mid;
            else
                low = mid + 1;
        }

        return low;
    }

    /// <summary>Marginal production cost of one more layer of <paramref name="mechanism"/>.</summary>
    private static int MeasureLayerWeight(WeightedMechanism mechanism)
        => MeasureLayerWeight(mechanism, Ceiling, EvaluatorProfile);

    private static int MeasureLayerWeight(
        WeightedMechanism mechanism,
        int ceiling,
        AstConsumerProfile profile)
        => MeasureCost(mechanism.Wrap(mechanism.Wrap(Base())), ceiling, profile)
            - MeasureCost(mechanism.Wrap(Base()), ceiling, profile);

    // ── Saturating interleave construction ──────────────────────────────────

    /// <summary>
    /// One generated matrix cell, carrying everything a failure diagnostic needs so a
    /// reviewer never has to reconstruct the case from a test index.
    /// </summary>
    internal sealed record CompositionCase(Expr Tree, string Description);

    /// <summary>
    /// Builds a maximally interleaved composition of <paramref name="first"/> (OUTERMOST)
    /// and <paramref name="second"/> whose production cost is accepted at
    /// <paramref name="targetCost"/> and locally maximal for either additional mechanism.
    ///
    /// <para><b>Remainder handling.</b> The base costs 1, so the layers must sum to
    /// <c>targetCost - 1</c> — an ODD number at the 300 ceiling. Every pair drawn from the
    /// even weights (2, 4, 8) can only reach an even total, so an exact solution needs
    /// padding. Padding is <see cref="Index"/> layers (weight 1) placed INNERMOST, outside
    /// the interleaved region, and the measured solver minimises it among equally deep
    /// candidates. The pad count is reported in the description so it is never
    /// invisible.</para>
    ///
    /// <para>The outermost layer is always <paramref name="first"/>, so the ordered pair
    /// (A, B) stays structurally distinguishable from (B, A) even when the counts coincide:
    /// stack and frame composition can be directional.</para>
    /// </summary>
    internal static CompositionCase BuildSaturatingInterleave(
        WeightedMechanism first,
        WeightedMechanism second,
        int targetCost)
    {
        Assert.True(
            first.DeclaredWeight > 0 && second.DeclaredWeight > 0,
            "A zero-weight mechanism can never saturate a cost ceiling; cover it with the zero-weight tests.");

        // MEASUREMENT-DRIVEN, not arithmetic-driven. Re-entry is an edge cost, so a
        // layer's marginal cost depends on what it wraps. Complete (second, first) cycles
        // are built innermost-outward, which makes `first` structurally outermost by
        // construction. A small measured search over innermost weight-one padding handles
        // remainders without changing that direction. The search range covers twice the
        // largest transition charge; after the first padding layer, each further Index is
        // in one iterative spine and advances the candidate by one unit.
        if (ReferenceEquals(first, second))
        {
            Expr? bestPure = null;
            var bestPureLayers = 0;
            var bestPurePad = 0;
            var bestPureCost = -1;

            for (var pad = 0; pad <= 16; pad++)
            {
                var pure = Base();
                for (var i = 0; i < pad; i++)
                    pure = Index.Wrap(pure);

                var pureLayers = 0;
                while (MeasureCost(first.Wrap(pure)) <= targetCost)
                {
                    pure = first.Wrap(pure);
                    pureLayers++;
                }

                var pureCost = MeasureCost(pure);
                if (pureLayers < 2
                    || pureCost < bestPureCost
                    || pureCost == bestPureCost && pad >= bestPurePad)
                {
                    continue;
                }

                bestPure = pure;
                bestPureLayers = pureLayers;
                bestPurePad = pad;
                bestPureCost = pureCost;
            }

            Assert.NotNull(bestPure);
            return new CompositionCase(
                bestPure!,
                $"{first.Name} -> {second.Name}; counts: {first.Name}={bestPureLayers}; "
                + $"layers={bestPureLayers}; pattern=pure; pad(Index)={bestPurePad}; "
                + $"measured cost={bestPureCost} of target {targetCost}");
        }

        Expr? bestTree = null;
        var bestCost = -1;
        var bestPad = int.MaxValue;
        var bestFirstCount = 0;
        var bestSecondCount = 0;

        for (var pad = 0; pad <= 16; pad++)
        {
            var candidateTree = Base();
            for (var i = 0; i < pad; i++)
                candidateTree = Index.Wrap(candidateTree);

            var firstCount = 0;
            var secondCount = 0;
            while (true)
            {
                var pair = first.Wrap(second.Wrap(candidateTree));
                if (MeasureCost(pair) > targetCost)
                    break;

                candidateTree = pair;
                firstCount++;
                secondCount++;
            }

            if (firstCount == 0)
                continue;

            // Extra first layers preserve direction and use any remainder that cannot fit
            // another complete interleaved cycle.
            while (MeasureCost(first.Wrap(candidateTree)) <= targetCost)
            {
                candidateTree = first.Wrap(candidateTree);
                firstCount++;
            }

            if (MeasureCost(second.Wrap(candidateTree)) <= targetCost)
                continue;

            var candidateCost = MeasureCost(candidateTree);
            if (candidateCost < bestCost || candidateCost == bestCost && pad >= bestPad)
                continue;

            bestTree = candidateTree;
            bestCost = candidateCost;
            bestPad = pad;
            bestFirstCount = firstCount;
            bestSecondCount = secondCount;
        }

        Assert.NotNull(bestTree);
        var layers = bestFirstCount + bestSecondCount;
        return new CompositionCase(
            bestTree!,
            $"{first.Name} -> {second.Name}; counts: {first.Name}={bestFirstCount}, "
            + $"{second.Name}={bestSecondCount}; layers={layers}; pattern=directed alternating; "
            + $"pad(Index)={bestPad}; measured cost={bestCost} of target {targetCost}");
    }

    /// <summary>
    /// Asserts the composition sits ON the production boundary: it is accepted at
    /// <paramref name="targetCost"/>, and adding one more layer of EITHER mechanism would
    /// exceed it. This is a stronger and more robust statement than "the arithmetic sums to
    /// the ceiling" — it needs no weight arithmetic at all, so it stays correct under a
    /// context-dependent cost model.
    /// </summary>
    private static void AssertMaximalAtTarget(
        CompositionCase composition,
        WeightedMechanism first,
        WeightedMechanism second,
        int targetCost)
    {
        var measured = MeasureCost(composition.Tree);
        Assert.True(
            measured == targetCost,
            $"Composition does not reach its exact target ({measured} != {targetCost})."
            + $"{Environment.NewLine}  {composition.Description}");

        foreach (var mechanism in new[] { first, second })
        {
            Assert.True(
                MeasureCost(mechanism.Wrap(composition.Tree)) > targetCost,
                $"Composition is NOT maximal: another {mechanism.Name} layer still fits under "
                + $"{targetCost} (measured {measured})."
                + $"{Environment.NewLine}  {composition.Description}");
        }
    }

    // ── Safety assertion across entry points ────────────────────────────────

    private readonly record struct EntryPointOutcome(bool IsError, EvalError? Error, Result? Value);

    private static EntryPointOutcome Describe(EvalResult<Result> result)
        => result.IsError ? new(true, result.Error, null) : new(false, null, result.Value);

    private static EntryPointOutcome Describe(EvalResult<Evaluator.CountedResult> result)
        => result.IsError ? new(true, result.Error, null) : new(false, null, result.Value.Value);

    private static EntryPointOutcome Describe(EvalResult<Evaluator.CountedRootProgramResult> result)
        => result.IsError ? new(true, result.Error, null) : new(false, null, result.Value.Output.Value);

    private static EntryPointOutcome Describe(EvalResult<IReadOnlyList<decimal>> result)
        => result.IsError ? new(true, result.Error, null) : new(false, null, null);

    /// <summary>Every guarded evaluator entry point, applied to one tree.</summary>
    private static IReadOnlyList<(string Name, Func<EntryPointOutcome> Run)> EntryPoints(Expr tree)
    {
        return
        [
            ("Run", () => Describe(Evaluator.Run(tree))),
            ("RunWithLimits", () => Describe(Evaluator.Run(tree, EvaluationLimits.Default))),
            ("RunFlat", () => Describe(Evaluator.RunFlat(tree))),
            ("RunFlatWithLimits", () => Describe(Evaluator.RunFlat(tree, EvaluationLimits.Default))),
            ("RunCounted", () => Describe(Evaluator.RunCounted(tree))),
            ("RunCountedWithCache", () => Describe(Evaluator.RunCounted(
                tree,
                new Evaluation.Caching.RunScopedZeroArgPropertyResultCache()))),
            ("RunCountedObservedOptimized",
                () => Describe(Evaluator.RunCountedObserved(tree, enableOptimizations: true).Result)),
            ("RunCountedObservedUnoptimized",
                () => Describe(Evaluator.RunCountedObserved(tree, enableOptimizations: false).Result)),
            ("RunCountedWithTopLevelProperty",
                () => Describe(Evaluator.RunCountedWithTopLevelProperty(
                    tree,
                    "X",
                    new Evaluation.Caching.RunScopedZeroArgPropertyResultCache()))),
        ];
    }

    internal static string LeafKind(EvalError error)
    {
        while (error is EvalError.WithContext(_, var inner))
            error = inner;
        return error.GetType().Name;
    }

    /// <summary>
    /// The core invariant. For an accepted composition, every entry point must return
    /// either the expected fixed-point value or a structured RESOURCE error — and no entry
    /// point may throw. A non-resource error would mean the generated program is not
    /// semantically representative of the mechanism under test (a builder defect); an
    /// exception or a process death is the calibration defect this family exists to find.
    /// Resource-ness is decided by the PRODUCTION predicate
    /// <c>EvalError.IsResourceLimit</c>, not by a duplicated list of error names.
    /// </summary>
    internal static void AssertSafeAcrossEntryPoints(CompositionCase composition)
    {
        Result? agreedValue = null;
        var agreedSource = "";

        foreach (var (name, run) in EntryPoints(composition.Tree))
        {
            EntryPointOutcome outcome;
            try
            {
                outcome = run();
            }
            catch (Exception ex)
            {
                Assert.Fail(
                    $"Composition threw {ex.GetType().Name} instead of returning a result."
                    + $"{Environment.NewLine}  {composition.Description}"
                    + $"{Environment.NewLine}  entry point: {name}"
                    + $"{Environment.NewLine}  {ex.Message}");
                return;
            }

            if (outcome.IsError)
            {
                Assert.True(
                    outcome.Error!.IsResourceLimit,
                    $"Composition produced the NON-resource error '{LeafKind(outcome.Error!)}'."
                    + $"{Environment.NewLine}  {composition.Description}"
                    + $"{Environment.NewLine}  entry point: {name}");
                continue;
            }

            if (outcome.Value is not { } value)
                continue;

            // Every mechanism layer is a fixed point at 1, so a successful composition of
            // any mixture at any depth must still be exactly 1. A different value means a
            // layer changed the program's meaning.
            Assert.True(
                Result.ValueComparer.Equals(value, new Result.Atom(1)),
                $"Composition evaluated to {value} instead of the fixed point 1."
                + $"{Environment.NewLine}  {composition.Description}"
                + $"{Environment.NewLine}  entry point: {name}");

            // Plain, counted, observed, and optimized strategies must agree: prior
            // resource defects crossed exactly this boundary.
            if (agreedValue is null)
            {
                agreedValue = value;
                agreedSource = name;
            }
            else
            {
                Assert.True(
                    Result.ValueComparer.Equals(agreedValue, value),
                    $"Entry points disagree on the composition's value."
                    + $"{Environment.NewLine}  {composition.Description}"
                    + $"{Environment.NewLine}  {agreedSource} = {agreedValue}, {name} = {value}");
            }
        }
    }

    // ── Table pins ──────────────────────────────────────────────────────────

    public static TheoryData<string> AllMechanismNames()
    {
        var data = new TheoryData<string>();
        foreach (var mechanism in Mechanisms.Append(Join))
            data.Add(mechanism.Name);
        return data;
    }

    public static TheoryData<string> WeightedMechanismNames()
    {
        var data = new TheoryData<string>();
        foreach (var mechanism in Mechanisms)
            data.Add(mechanism.Name);
        return data;
    }

    [Theory]
    [MemberData(nameof(AllMechanismNames))]
    public void MechanismTable_LayerWeightsMatchProduction(string name)
    {
        var mechanism = ByName(name);
        var measured = MeasureLayerWeight(mechanism);
        Assert.True(
            measured == mechanism.DeclaredWeight,
            $"Production layer weight for {mechanism.Name} is {measured}, the table says "
            + $"{mechanism.DeclaredWeight}. Update the table and re-derive the matrix rather "
            + "than adjusting the measurement.");
    }

    [Theory]
    [MemberData(nameof(AllMechanismNames))]
    public void MechanismTable_EachLayerPerformsRealWork(string name)
    {
        var mechanism = ByName(name);

        foreach (var layers in new[] { 1, 10, 100 })
        {
            var tree = Base();
            for (var i = 0; i < layers; i++)
                tree = mechanism.Wrap(tree);

            var plain = Evaluator.Run(tree);
            var counted = Evaluator.RunCounted(tree);

            if (plain.IsError)
            {
                // Deep enough stacks legitimately exhaust a budget (the Alternation
                // mechanism passes the 300-unit ceiling at 38 layers, for instance).
                Assert.True(
                    plain.Error.IsResourceLimit,
                    $"{mechanism.Name} x{layers} produced the non-resource error {LeafKind(plain.Error)}.");
                Assert.True(
                    counted.IsError,
                    $"{mechanism.Name} x{layers}: plain failed with {LeafKind(plain.Error)} but counted succeeded.");
                continue;
            }

            Assert.True(
                Result.ValueComparer.Equals(plain.Value, new Result.Atom(1)),
                $"{mechanism.Name} x{layers} evaluated to {plain.Value}, expected the fixed point 1.");
            Assert.False(
                counted.IsError,
                $"{mechanism.Name} x{layers}: counted failed but plain succeeded.");
            Assert.True(
                Result.ValueComparer.Equals(plain.Value, counted.Value.Value),
                $"{mechanism.Name} x{layers}: plain and counted disagree.");
        }
    }

    [Fact]
    public void ArgsDotCall_IsDistinctFromPlainDotCall_InTheProductionModel()
    {
        // The evaluator gate charges an args-bearing DotCall one unit MORE than a bare one
        // (it absorbs the former transparent Args wrapper algorithm). A builder that
        // silently produced Args: null would collapse the two matrix kinds into one and
        // quietly halve this family's dot-call coverage.
        var bare = Assert.IsType<Expr.DotCall>(DotCall.Wrap(Base()));
        var withArgs = Assert.IsType<Expr.DotCall>(ArgsDotCall.Wrap(Base()));

        Assert.Null(bare.Args);
        Assert.NotNull(withArgs.Args);
        Assert.NotEmpty(withArgs.Args);

        Assert.Equal(3, MeasureLayerWeight(DotCall));
        Assert.Equal(4, MeasureLayerWeight(ArgsDotCall));

        // The absorbed Args-wrapper unit is charged on BOTH profiles — the args-bearing
        // shape is always exactly one unit dearer than the bare one. What differs between
        // the profiles is the dot LINK cost itself (3 units on the evaluator gate, where
        // each link's resolution machinery spends several large frames; 1 unit on the
        // small-framed front-end gate).
        const int rawCeiling = AstStructuralPreflight.RawSyntaxMaxAstDepth;
        const AstConsumerProfile recursive = AstConsumerProfile.FullyRecursive;
        Assert.Equal(1, MeasureLayerWeight(DotCall, rawCeiling, recursive));
        Assert.Equal(2, MeasureLayerWeight(ArgsDotCall, rawCeiling, recursive));
        Assert.Equal(
            MeasureLayerWeight(ArgsDotCall) - MeasureLayerWeight(DotCall),
            MeasureLayerWeight(ArgsDotCall, rawCeiling, recursive)
                - MeasureLayerWeight(DotCall, rawCeiling, recursive));
    }

    // ── The ordered-pair matrix ─────────────────────────────────────────────

    public static TheoryData<string, string> OrderedPairs()
    {
        var data = new TheoryData<string, string>();
        foreach (var first in Mechanisms)
            foreach (var second in Mechanisms)
                data.Add(first.Name, second.Name);
        return data;
    }

    [Theory]
    [MemberData(nameof(OrderedPairs))]
    public void WeightedCostComposition_AllOrderedPairs_AreSafeAtCeiling(string firstName, string secondName)
    {
        var first = ByName(firstName);
        var second = ByName(secondName);
        var composition = BuildSaturatingInterleave(first, second, Ceiling);

        AssertMaximalAtTarget(composition, first, second, Ceiling);
        Assert.Null(AstStructuralPreflight.Check(composition.Tree, Ceiling, EvaluatorProfile));

        AssertSafeAcrossEntryPoints(composition);
    }

    [Theory]
    [MemberData(nameof(OrderedPairs))]
    public void WeightedCostComposition_OrderedPairsKeepTheFirstMechanismOutermost(
        string firstName,
        string secondName)
    {
        var first = ByName(firstName);
        var second = ByName(secondName);
        var forward = BuildSaturatingInterleave(first, second, Ceiling);

        Assert.True(
            HasOutermostMechanism(forward.Tree, first),
            $"Ordered-pair builder did not leave {first.Name} outermost.{Environment.NewLine}"
            + $"  {forward.Description}");

        if (ReferenceEquals(first, second))
            return;

        var reverse = BuildSaturatingInterleave(second, first, Ceiling);
        Assert.True(
            HasOutermostMechanism(reverse.Tree, second),
            $"Reversed builder did not leave {second.Name} outermost.{Environment.NewLine}"
            + $"  {reverse.Description}");
        Assert.False(
            HasOutermostMechanism(forward.Tree, second),
            $"Forward and reverse cases collapsed to the same outer mechanism: {first.Name}/{second.Name}.");
    }

    [Theory]
    [MemberData(nameof(OrderedPairs))]
    public void WeightedCostComposition_CeilingNeighbours_AreCoherent(string firstName, string secondName)
    {
        var first = ByName(firstName);
        var second = ByName(secondName);

        // At the ceiling and just below it: accepted (the ceiling is inclusive) and safe.
        foreach (var target in new[] { Ceiling - 1, Ceiling })
        {
            var composition = BuildSaturatingInterleave(first, second, target);
            AssertMaximalAtTarget(composition, first, second, target);
            Assert.Null(AstStructuralPreflight.Check(composition.Tree, Ceiling, EvaluatorProfile));
            AssertSafeAcrossEntryPoints(composition);
        }

        // Just beyond: the maximal accepted composition plus ONE more layer of either
        // mechanism must be rejected by the preflight, and the entry point must report the
        // structured limit rather than attempting evaluation. Because the accepted case is
        // MAXIMAL, this is the true +1 boundary for this shape whatever a layer costs.
        var atCeiling = BuildSaturatingInterleave(first, second, Ceiling);
        foreach (var mechanism in new[] { first, second })
        {
            var beyond = mechanism.Wrap(atCeiling.Tree);
            Assert.NotNull(AstStructuralPreflight.Check(beyond, Ceiling, EvaluatorProfile));

            var rejected = Evaluator.Run(beyond);
            Assert.True(
                rejected.IsError,
                $"Beyond-ceiling composition was accepted.{Environment.NewLine}"
                + $"  {atCeiling.Description} + one {mechanism.Name} layer");
            Assert.Equal(Ceiling, Assert.IsType<EvalError.AstDepthLimitExceeded>(rejected.Error).Limit);
        }
    }

    [Theory]
    [MemberData(nameof(AllMechanismNames))]
    public void PureChainCost_IsAdditive(string name)
    {
        // Within ONE mechanism the model IS additive, which is what makes the per-kind
        // calibrations meaningful: k layers cost the base plus k marginal weights.
        var mechanism = ByName(name);
        var baseCost = MeasureCost(Base());

        var tree = Base();
        for (var layers = 1; layers <= 12; layers++)
        {
            tree = mechanism.Wrap(tree);
            var expected = baseCost + (layers * mechanism.DeclaredWeight);
            Assert.True(
                MeasureCost(tree) == expected,
                $"{mechanism.Name} x{layers}: measured {MeasureCost(tree)}, expected {expected} "
                + "— pure chains must stay additive.");
        }
    }

    [Fact]
    public void CostModel_IsContextDependent_ForMachineIteratedKinds()
    {
        // The corrected model is deliberately NON-additive ACROSS kinds for the two
        // machine-iterated families, and this documents exactly where. A traversed edge
        // inside one machine is cheap; an edge that delegates to a different mechanism pays
        // the calibrated re-entry cost because that is where the evaluator actually spends
        // a fresh recursive frame. Any test that predicts composition costs by summing
        // per-kind node weights is therefore wrong by construction; the matrix measures.
        var inner = Capture.Wrap(Base());

        // Spine kind: 1 unit over another spine node, a full re-entry over a non-spine one.
        Assert.Equal(1, MeasureCost(Index.Wrap(Index.Wrap(Base()))) - MeasureCost(Index.Wrap(Base())));
        Assert.Equal(8, MeasureCost(Index.Wrap(inner)) - MeasureCost(inner));

        // Join kind: free in a spine's interior, a full re-entry at the hand-off.
        var joins = Join.Wrap(Join.Wrap(Base()));
        Assert.Equal(0, MeasureCost(joins) - MeasureCost(Base()));
        Assert.Equal(8, MeasureCost(Join.Wrap(inner)) - MeasureCost(inner));

        // A spread -> construct alternation followed by construct -> capture contains TWO
        // nested CLR-recursive transitions. Each traversed edge owns one charge; treating
        // them as the same hand-off undercounts the actual evaluator call chain.
        Assert.Equal(16, MeasureCost(Alternation.Wrap(inner)) - MeasureCost(inner));
    }

    [Fact]
    public void ReentryCharges_AreScopedToTheTraversedChildPath()
    {
        // A hand-off is an EDGE cost, not a property of every path through the parent
        // node. Each right-hand capture below is evaluated sequentially by ONE iterative
        // binary-machine run; none of those shallow side branches remains on the CLR
        // stack while the machine continues down the left spine. Charging the whole
        // Binary node would multiply the hand-off cost along the unrelated left path and
        // reject this parser-sized, stack-safe shape after only a few dozen layers.
        var binaryWithCompositeSideBranches =
            BinarySpineWithCompositeSideBranches(Parser.MaxExpressionChainDepth);

        Assert.Equal(Parser.MaxExpressionChainDepth + 10, MeasureCost(binaryWithCompositeSideBranches));
        Assert.Null(AstStructuralPreflight.Check(
            binaryWithCompositeSideBranches,
            Ceiling,
            EvaluatorProfile));
        AssertSafeAcrossEntryPoints(new CompositionCase(
            binaryWithCompositeSideBranches,
            "parser-capacity binary spine with shallow composite side branches"));

        // SequenceConstructLeaves flattens the entire left join spine before evaluating
        // its leaves. The captures on the right are therefore also shallow, sequential
        // hand-offs. The cost is one join->capture edge plus that capture's own path,
        // independent of how many zero-weight construct nodes precede it.
        var joinWithCompositeSideBranches = JoinSpineWithCompositeSideBranches(20_000);

        Assert.Equal(11, MeasureCost(joinWithCompositeSideBranches));
        Assert.Null(AstStructuralPreflight.Check(
            joinWithCompositeSideBranches,
            maxDepth: 11,
            EvaluatorProfile));

        var joinResult = Evaluator.Run(joinWithCompositeSideBranches);
        Assert.False(joinResult.IsError);
        Assert.True(Result.ValueComparer.Equals(joinResult.Value, new Result.Atom(1)));
    }

    [Fact]
    public void OrdinarySourceBinarySpine_WithCallSideOperands_RemainsSupported()
    {
        // Source-reachable form of the same path-accounting regression. The parser and
        // fully-recursive front-end gate accept this ordinary flat expression, and the
        // iterative evaluator machine keeps its binary spine off the CLR stack. A
        // node-wide hand-off charge nevertheless rejected it at the evaluator gate.
        const int operators = 64;
        var source = "1" + string.Concat(Enumerable.Repeat(" + sum(0)", operators));

        var parsed = SourceProvenance.ParseValid(source);
        var result = Evaluator.Run(new Expr.AlgorithmExpr(parsed.Root));

        Assert.False(
            result.IsError,
            result.IsError ? $"unexpected {LeafKind(result.Error)}" : string.Empty);
        Assert.True(Result.ValueComparer.Equals(result.Value, new Result.Atom(1)));
    }

    [Fact]
    public void CostModel_RepresentativeExtensionsAreMonotone()
    {
        // Small representative trees keep the measurement below the hard ceiling, so a
        // saturated "301" sentinel cannot hide a decrease. Every wrapper either adds cost
        // or (for a join-spine interior) leaves it unchanged; none may make a deeper tree
        // cheaper than the child it contains.
        var samples = new Expr[]
        {
            Base(),
            Index.Wrap(Index.Wrap(Base())),
            Capture.Wrap(Index.Wrap(Base())),
            Join.Wrap(Capture.Wrap(Base())),
            Alternation.Wrap(Base()),
        };

        foreach (var sample in samples)
        {
            var before = MeasureCost(sample);
            foreach (var mechanism in Mechanisms.Append(Join))
            {
                var after = MeasureCost(mechanism.Wrap(sample));
                Assert.True(
                    after >= before,
                    $"Adding {mechanism.Name} decreased production cost from {before} to {after}.");
            }
        }

        var oneAlternation = Alternation.Wrap(Base());
        var twoAlternations = Alternation.Wrap(oneAlternation);
        Assert.Equal(8, MeasureCost(twoAlternations) - MeasureCost(oneAlternation));

        var oneJoinHandoff = Join.Wrap(Capture.Wrap(Base()));
        var deeperJoinHandoff = Join.Wrap(Capture.Wrap(oneJoinHandoff));
        Assert.True(MeasureCost(deeperJoinHandoff) > MeasureCost(oneJoinHandoff));
    }

    [Fact]
    public void SharedSubtreeHeight_IsCombinedWithEachIncomingTransitionEdge()
    {
        // The child height is context-independent and may be memoized by reference; the
        // incoming transition is occurrence-specific and must be added by the parent. Put
        // the cheap occurrence first so the charged occurrence exercises the completed-
        // shared-node path in AstStructuralPreflight.Check.
        var shared = new Expr.Capture([new Expr.Num(1)]);
        var root = new Expr.Capture([
            shared,
            new Expr.Index(shared, new Expr.Num(0)),
        ]);

        // Root Capture 2 + Index 1 + transition surcharge 7 + shared Capture/Num 3.
        Assert.Equal(13, MeasureCost(root));
        Assert.Null(AstStructuralPreflight.Check(root, 13, EvaluatorProfile));
        Assert.NotNull(AstStructuralPreflight.Check(root, 12, EvaluatorProfile));
    }

    // ── Named regressions for the historical defects ────────────────────────

    [Fact]
    public void Call_DotCall_Composition_IsSafeAtConfiguredCeiling()
    {
        // The F2 shape generalized: nested builtin calls weighed 2 units per level while
        // consuming ~11 CLR frames, and charged no dynamic depth, so a saturated chain
        // terminated the process. Interleaving them with dot-call links (3 units, their own
        // resolution frames) stresses both calibrations at once, in both orders.
        foreach (var composition in new[]
        {
            BuildSaturatingInterleave(Call, DotCall, Ceiling),
            BuildSaturatingInterleave(DotCall, Call, Ceiling),
        })
        {
            Assert.True(MeasureCost(composition.Tree) <= Ceiling, composition.Description);
            Assert.Null(AstStructuralPreflight.Check(composition.Tree, Ceiling, EvaluatorProfile));
            AssertSafeAcrossEntryPoints(composition);
        }
    }

    [Fact]
    public void Alternation_Call_Composition_IsSafeAtConfiguredCeiling()
    {
        // The F1 shape generalized: the spread-of-construct alternation was free and
        // overflowed a 1 MiB stack. It now weighs 8 units, so the ceiling admits ~37 links;
        // this pins that those links stay safe when the recursion they re-enter runs
        // THROUGH another mechanism's frames instead of directly into itself.
        foreach (var composition in new[]
        {
            BuildSaturatingInterleave(Alternation, Call, Ceiling),
            BuildSaturatingInterleave(Call, Alternation, Ceiling),
        })
        {
            Assert.True(MeasureCost(composition.Tree) <= Ceiling, composition.Description);
            Assert.Null(AstStructuralPreflight.Check(composition.Tree, Ceiling, EvaluatorProfile));
            AssertSafeAcrossEntryPoints(composition);
        }
    }

    // ── High-risk triples ───────────────────────────────────────────────────

    public static TheoryData<string, string, string> HighRiskTriples()
    {
        // Chosen for distinct evaluator frame families rather than exhaustively: a real
        // call, a dot-resolution link, a written value boundary, a scope-owning algorithm,
        // and the recursive join alternation.
        var data = new TheoryData<string, string, string>();
        data.Add("Call", "DotCall", "Capture");
        data.Add("Alternation", "Call", "DotCall");
        data.Add("Capture", "ArgsDotCall", "Call");
        data.Add("Alternation", "Capture", "Call");
        data.Add("AlgorithmExpr", "DotCall", "Alternation");
        return data;
    }

    [Theory]
    [MemberData(nameof(HighRiskTriples))]
    public void WeightedCostComposition_HighRiskTriples_AreSafeAtCeiling(string a, string b, string c)
    {
        var first = ByName(a);
        var composition = BuildSaturatingTriple(first, ByName(b), ByName(c), Ceiling);

        var measured = MeasureCost(composition.Tree);
        Assert.True(
            measured <= Ceiling,
            $"Generated triple exceeds the {Ceiling} ceiling (measured {measured})."
            + $"{Environment.NewLine}  {composition.Description}");
        Assert.Null(AstStructuralPreflight.Check(composition.Tree, Ceiling, EvaluatorProfile));
        Assert.True(
            HasOutermostMechanism(composition.Tree, first),
            $"Triple builder did not leave {first.Name} outermost.{Environment.NewLine}"
            + $"  {composition.Description}");

        AssertSafeAcrossEntryPoints(composition);
    }

    /// <summary>
    /// Round-robin ABCABC... saturation, MEASURED against the production model layer by
    /// layer for the same reason the pair builder is (see
    /// <see cref="CostModel_IsContextDependent_ForMachineIteratedKinds"/>): a layer's cost
    /// depends on what it wraps, so the cycle count cannot be computed in closed form.
    /// </summary>
    internal static CompositionCase BuildSaturatingTriple(
        WeightedMechanism first,
        WeightedMechanism second,
        WeightedMechanism third,
        int targetCost)
    {
        Expr? bestTree = null;
        var bestCost = -1;
        var bestPad = int.MaxValue;
        var bestFirstCount = 0;
        var bestCycleCount = 0;

        // As for ordered pairs, grow only complete reversed cycles so `first` is
        // outermost by construction; measured innermost padding handles the remainder.
        for (var pad = 0; pad <= 16; pad++)
        {
            var candidateTree = Base();
            for (var i = 0; i < pad; i++)
                candidateTree = Index.Wrap(candidateTree);

            var cycles = 0;
            while (true)
            {
                var triple = first.Wrap(second.Wrap(third.Wrap(candidateTree)));
                if (MeasureCost(triple) > targetCost)
                    break;

                candidateTree = triple;
                cycles++;
            }

            if (cycles == 0)
                continue;

            var firstCount = cycles;
            while (MeasureCost(first.Wrap(candidateTree)) <= targetCost)
            {
                candidateTree = first.Wrap(candidateTree);
                firstCount++;
            }

            if (MeasureCost(second.Wrap(candidateTree)) <= targetCost
                || MeasureCost(third.Wrap(candidateTree)) <= targetCost)
            {
                continue;
            }

            var candidateCost = MeasureCost(candidateTree);
            if (candidateCost < bestCost || candidateCost == bestCost && pad >= bestPad)
                continue;

            bestTree = candidateTree;
            bestCost = candidateCost;
            bestPad = pad;
            bestFirstCount = firstCount;
            bestCycleCount = cycles;
        }

        Assert.NotNull(bestTree);
        return new CompositionCase(
            bestTree!,
            $"{first.Name} -> {second.Name} -> {third.Name}; "
            + $"counts: {first.Name}={bestFirstCount}, {second.Name}={bestCycleCount}, "
            + $"{third.Name}={bestCycleCount}; pattern=directed round-robin; "
            + $"pad(Index)={bestPad}; measured cost={bestCost} of target {targetCost}");
    }

    // ── Zero-weight mechanism: bounded by an independent property, not by cost ──

    [Fact]
    public void ZeroWeightJoins_CostNothing_AndAreBoundedByIterativeEvaluation()
    {
        // A pure SequenceConstruct chain costs ZERO however long it is, so the cost model
        // provides NO bound at all. What makes that safe is a different property, not
        // another preflight dimension: every consumer behind the evaluator gate walks a
        // SINGLE-KIND join spine with an explicit iterative stack. Stating that contract
        // here keeps the zero weight from being mistaken for "protected by a limit".
        var deep = Base();
        for (var i = 0; i < 20_000; i++)
            deep = Join.Wrap(deep);

        Assert.Equal(MeasureCost(Base()), MeasureCost(deep));
        Assert.Null(AstStructuralPreflight.Check(deep, 1, EvaluatorProfile));

        var plain = Evaluator.Run(deep);
        Assert.False(
            plain.IsError,
            $"A 20,000-level zero-weight join chain failed: {(plain.IsError ? LeafKind(plain.Error) : "")}");
        Assert.True(Result.ValueComparer.Equals(plain.Value, new Result.Atom(1)));

        var counted = Evaluator.RunCounted(deep);
        Assert.False(counted.IsError);
        Assert.True(Result.ValueComparer.Equals(counted.Value.Value, new Result.Atom(1)));
    }

    public static TheoryData<string, int> JoinInterleavedCases()
    {
        var data = new TheoryData<string, int>();
        foreach (var mechanism in Mechanisms)
            foreach (var joinsPerLayer in new[] { 1, 8, 64 })
                data.Add(mechanism.Name, joinsPerLayer);
        return data;
    }

    [Theory]
    [MemberData(nameof(JoinInterleavedCases))]
    public void ZeroWeightJoins_InterleavedWithWeightedLayers_StayBounded(string weightedName, int joinsPerLayer)
    {
        // THE generalized F1 shape, and the case that exposed F6. Join layers are inserted
        // between every weighted layer and the composition is grown to the ceiling. What
        // the corrected model charges is each RE-ENTRY into recursive evaluation, so the
        // admitted layer count is independent of how many joins sit in each spine — the
        // measured frame cost behaves the same way (identical outcomes for 1, 8 and 64
        // joins per layer), which is exactly why the charge is per hand-off and not per
        // join node. All three multiplicities are therefore expected to produce the SAME
        // layer count at the ceiling, asserted below.
        var composition = BuildJoinInterleaved(ByName(weightedName), joinsPerLayer, Ceiling);

        var measured = MeasureCost(composition.Tree);
        Assert.True(
            measured <= Ceiling && measured > Ceiling - 12,
            $"Join-interleaved composition is at cost {measured}, expected to saturate {Ceiling}."
            + $"{Environment.NewLine}  {composition.Description}");

        Assert.Null(AstStructuralPreflight.Check(composition.Tree, Ceiling, EvaluatorProfile));

        AssertSafeAcrossEntryPoints(composition);
    }

    [Theory]
    [MemberData(nameof(WeightedMechanismNames))]
    public void ZeroWeightJoins_AdmittedLayerCount_IsIndependentOfSpineLength(string weightedName)
    {
        // Spine LENGTH is free; only hand-offs are charged. If a future change started
        // charging per join node instead, the admitted layer counts would diverge with the
        // multiplicity and this pins that they must not.
        var mechanism = ByName(weightedName);
        var counts = new[] { 1, 8, 64 }
            .Select(joins => LayersAtCeiling(mechanism, joins))
            .Distinct()
            .ToList();

        Assert.True(
            counts.Count == 1,
            $"{mechanism.Name}: admitted layer count varies with join multiplicity ({string.Join(", ", counts)}); "
            + "the join re-entry charge must depend on hand-offs, not spine length.");
    }

    /// <summary>
    /// The greatest number of <paramref name="weighted"/> layers (each preceded by
    /// <paramref name="joinsPerLayer"/> join layers) whose production cost still fits the
    /// ceiling. Derived by measurement, so it tracks the production model automatically.
    /// </summary>
    private static int LayersAtCeiling(WeightedMechanism weighted, int joinsPerLayer)
    {
        var layers = 0;
        while (MeasureCost(JoinInterleavedTree(weighted, joinsPerLayer, layers + 1)) <= Ceiling)
            layers++;
        return layers;
    }

    private static Expr JoinInterleavedTree(WeightedMechanism weighted, int joinsPerLayer, int layers)
    {
        var tree = Base();
        for (var i = 0; i < layers; i++)
        {
            for (var j = 0; j < joinsPerLayer; j++)
                tree = Join.Wrap(tree);
            tree = weighted.Wrap(tree);
        }

        return tree;
    }

    /// <summary>
    /// Saturates the ceiling with alternating join spines and <paramref name="weighted"/>
    /// layers. The layer count is MEASURED against the production model rather than
    /// computed from the weight table, because a join spine's cost depends on the hand-off
    /// it performs and not on its length.
    /// </summary>
    internal static CompositionCase BuildJoinInterleaved(
        WeightedMechanism weighted,
        int joinsPerLayer,
        int targetCost)
    {
        var layers = LayersAtCeiling(weighted, joinsPerLayer);
        Assert.True(layers >= 1, $"{weighted.Name}: no join-interleaved layer fits the ceiling.");

        var tree = JoinInterleavedTree(weighted, joinsPerLayer, layers);
        var measured = MeasureCost(tree);

        // Top up with weight-1 padding innermost so the case really sits on the boundary.
        var pad = targetCost - measured;
        for (var i = 0; i < pad && MeasureCost(Index.Wrap(tree)) <= targetCost; i++)
            tree = Index.Wrap(tree);

        return new CompositionCase(
            tree,
            $"Join x{joinsPerLayer} -> {weighted.Name}, repeated {layers}x; "
            + $"pad(Index)={MeasureCost(tree) - measured}; cost={MeasureCost(tree)} of {targetCost}; "
            + $"real node depth ~{layers * (joinsPerLayer + 1)}");
    }

    [Fact]
    public void ZeroWeightJoinHandoff_IsChargedPerReentry_NotPerJoinNode()
    {
        // F6 named regression. ONE zero-cost join per layer was enough to turn every
        // weight-1 and weight-2 layer into a recursive hand-off; the pure chains were safe
        // at 299 and 149 layers respectively while the interleaved trees measured exactly
        // 300 and terminated the process. The corrected model charges the hand-off, so the
        // interleaved forms no longer reach a crashing depth — while a PURE spine of any
        // length stays free.
        foreach (var mechanism in new[] { Index, Capture, AlgorithmExpr })
        {
            // The pure chain the per-kind calibration measured is still accepted...
            var pureLayers = (Ceiling - 1) / mechanism.DeclaredWeight;
            var pure = Base();
            for (var i = 0; i < pureLayers; i++)
                pure = mechanism.Wrap(pure);
            Assert.Null(AstStructuralPreflight.Check(pure, Ceiling, EvaluatorProfile));

            // ...while the same layer count interleaved with ONE join each is now rejected,
            // because every layer performs a charged hand-off.
            var interleaved = JoinInterleavedTree(mechanism, joinsPerLayer: 1, layers: pureLayers);
            Assert.NotNull(AstStructuralPreflight.Check(interleaved, Ceiling, EvaluatorProfile));

            // Spine length itself remains free: the same number of join nodes in ONE spine,
            // performing ONE hand-off, is still accepted.
            var oneSpine = mechanism.Wrap(NestedJoins(Base(), pureLayers));
            Assert.Null(AstStructuralPreflight.Check(oneSpine, Ceiling, EvaluatorProfile));
        }
    }

    private static Expr NestedJoins(Expr inner, int count)
    {
        for (var i = 0; i < count; i++)
            inner = Join.Wrap(inner);
        return inner;
    }
}

/// <summary>
/// Process-isolated half of the cost-model composition matrix. The failure mode this
/// family exists to catch is an uncatchable <see cref="StackOverflowException"/>, which an
/// in-process assertion cannot observe: it terminates the whole test host, so the run is
/// simply "aborted" with no attribution to a matrix cell. Each probe therefore runs the
/// highest-risk exact-ceiling compositions in a child <c>dotnet vstest</c> process on a
/// thread with the DOCUMENTED minimum supported stack (1 MiB), asserts the structured
/// outcome, and writes a success marker; the parent classifies normal exit, crash,
/// stack-overflow text, and timeout.
///
/// <para>Follows the subprocess convention of <see cref="AstStructuralDepthProcessTests"/>
/// and reuses its <c>RunOnThreadWithStack</c> helper, so the stack size a probe measures
/// against is exact rather than whatever the host happens to give a worker thread.</para>
///
/// <para>The split is deliberate: the ordinary pair matrix runs in-process (fast, and the
/// production preflight is what keeps it safe), while the shapes that HISTORICALLY killed
/// the process get one isolated test each.</para>
/// </summary>
public class WeightedCostCompositionProcessTests
{
    private const string ProbeChildEnvironment = "KATLANG_COST_COMPOSITION_PROBE_CHILD";
    private const string ProbeMarkerFileEnvironment = "KATLANG_COST_COMPOSITION_PROBE_MARKER_FILE";
    private const string ProbeSuccessMarker = "katlang-cost-composition-ok";

    /// <summary>The documented minimum supported thread stack.</summary>
    private const int SupportedStackBytes = 1024 * 1024;

    [Fact]
    public async Task AllOrderedPairs_AtCeiling_SurviveOnTheMinimumSupportedStack_InSubprocess()
        => await RunProbeChild("AllOrderedPairs_AtCeiling_ProbeChild");

    [Fact]
    public async Task ZeroWeightJoinInterleavings_AtCeiling_SurviveOnTheMinimumSupportedStack_InSubprocess()
        => await RunProbeChild("ZeroWeightJoinInterleavings_AtCeiling_ProbeChild");

    [Fact]
    public void AllOrderedPairs_AtCeiling_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        AstStructuralDepthProcessTests.RunOnThreadWithStack(SupportedStackBytes, () =>
        {
            foreach (var first in WeightedCostCompositionTests.Mechanisms)
            {
                foreach (var second in WeightedCostCompositionTests.Mechanisms)
                {
                    var composition = WeightedCostCompositionTests.BuildSaturatingInterleave(
                        first, second, EvaluationLimits.MaxSupportedAstDepth);
                    WeightedCostCompositionTests.AssertSafeAcrossEntryPoints(composition);
                }
            }
        });

        WriteProbeMarker();
    }

    [Fact]
    public void ZeroWeightJoinInterleavings_AtCeiling_ProbeChild()
    {
        if (Environment.GetEnvironmentVariable(ProbeChildEnvironment) != "1")
            return;

        // The F6 shape at every multiplicity. Before the join re-entry charge, ONE join per
        // weight-1 or weight-2 layer terminated the process here while the corresponding
        // pure chain was safe at the same layer count.
        AstStructuralDepthProcessTests.RunOnThreadWithStack(SupportedStackBytes, () =>
        {
            foreach (var mechanism in WeightedCostCompositionTests.Mechanisms)
            {
                foreach (var joinsPerLayer in new[] { 1, 8, 64 })
                {
                    var composition = WeightedCostCompositionTests.BuildJoinInterleaved(
                        mechanism, joinsPerLayer, EvaluationLimits.MaxSupportedAstDepth);
                    WeightedCostCompositionTests.AssertSafeAcrossEntryPoints(composition);
                }
            }

            // Review regression: shallow composite siblings are sequential leaves of one
            // iterative machine run, not recursive re-entries along the deep spine path.
            // Both parser-sized expression spines and very long zero-weight join spines
            // must therefore remain accepted and safe on the documented stack.
            WeightedCostCompositionTests.AssertSafeAcrossEntryPoints(new(
                WeightedCostCompositionTests.BinarySpineWithCompositeSideBranches(
                    Parser.MaxExpressionChainDepth),
                "binary spine with shallow composite side branches"));
            WeightedCostCompositionTests.AssertSafeAcrossEntryPoints(new(
                WeightedCostCompositionTests.JoinSpineWithCompositeSideBranches(20_000),
                "join spine with shallow composite side branches"));
        });

        WriteProbeMarker();
    }

    private static async Task RunProbeChild(string childTestName)
    {
        var assemblyPath = typeof(WeightedCostCompositionProcessTests).Assembly.Location;
        var testName = typeof(WeightedCostCompositionProcessTests).FullName + "." + childTestName;
        var markerFile = Path.Combine(
            Path.GetTempPath(),
            $"katlang-cost-composition-probe-{Guid.NewGuid():N}.txt");

        var startInfo = new System.Diagnostics.ProcessStartInfo("dotnet")
        {
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
            CreateNoWindow = true,
        };
        startInfo.ArgumentList.Add("vstest");
        startInfo.ArgumentList.Add(assemblyPath);
        startInfo.ArgumentList.Add("--Tests:" + testName);
        startInfo.Environment[ProbeChildEnvironment] = "1";
        startInfo.Environment[ProbeMarkerFileEnvironment] = markerFile;
        startInfo.Environment["DOTNET_NOLOGO"] = "1";

        try
        {
            using var process = new System.Diagnostics.Process { StartInfo = startInfo };
            process.Start();
            var stdoutTask = process.StandardOutput.ReadToEndAsync();
            var stderrTask = process.StandardError.ReadToEndAsync();

            var exited = true;
            using var timeout = new CancellationTokenSource(TimeSpan.FromSeconds(180));
            try
            {
                await process.WaitForExitAsync(timeout.Token);
            }
            catch (OperationCanceledException)
            {
                exited = false;
                try { process.Kill(entireProcessTree: true); }
                catch { /* process already exited */ }
                await process.WaitForExitAsync();
            }

            var combined = await stdoutTask + Environment.NewLine + await stderrTask;

            Assert.True(
                exited,
                $"Probe subprocess '{childTestName}' did not exit within 180 seconds."
                + Environment.NewLine + combined);
            Assert.DoesNotContain("Stack overflow", combined, StringComparison.OrdinalIgnoreCase);
            Assert.DoesNotContain("StackOverflowException", combined, StringComparison.OrdinalIgnoreCase);
            Assert.True(
                process.ExitCode == 0,
                $"Probe subprocess '{childTestName}' exited with {process.ExitCode}."
                + Environment.NewLine + combined);
            Assert.True(
                File.Exists(markerFile),
                $"Probe child '{childTestName}' did not write its success marker."
                + Environment.NewLine + combined);
            Assert.Equal(ProbeSuccessMarker, (await File.ReadAllTextAsync(markerFile)).Trim());
        }
        finally
        {
            try { File.Delete(markerFile); }
            catch { /* best-effort cleanup */ }
        }
    }

    private static void WriteProbeMarker()
    {
        var markerFile = Environment.GetEnvironmentVariable(ProbeMarkerFileEnvironment);
        Assert.False(string.IsNullOrWhiteSpace(markerFile));
        File.WriteAllText(markerFile!, ProbeSuccessMarker);
    }
}
