using KatLang.Tests.AstGraphFuzz;

namespace KatLang.Tests;

/// <summary>
/// Deterministic adversarial constructors around the structural-preflight boundary. Each family
/// targets one previously dangerous process-death class from the production cost model:
/// spine re-entry alternation, join alternation, join hand-off, pure zero-weight join spines,
/// shared subtrees reached through routes of different cost, wide shallow fan-out, and shared
/// diamonds whose EVALUATION (not stack) is the unbounded dimension. No stale cost constants:
/// the exact boundary is derived from <see cref="EvaluationLimits.MaxSupportedAstDepth"/> and
/// the families binary-search their maximum accepted size against the REAL preflight, then pin
/// a safety ENVELOPE that fails if a future cost-model edit re-admits a dangerous class.
/// The maximum accepted member of each family is additionally executed on a 1 MiB stack in
/// <see cref="AstGraphFuzzProcessTests"/>.
/// </summary>
internal static class BoundaryFamilies
{
    /// <summary>Pure iterative unary spine: weighted cost = count + 1 (leaf).</summary>
    internal static Expr UnaryChain(int unaryCount)
    {
        Expr e = new Expr.Num(5);
        for (var i = 0; i < unaryCount; i++)
            e = new Expr.Unary(UnaryOp.Minus, e);
        return e;
    }

    /// <summary>
    /// Spine/non-spine alternation: <c>Index(Capture([inner]), 0)</c> per layer — each layer
    /// re-enters the recursive machine from the iterative expression-spine machine.
    /// Evaluates to the leaf value at every depth.
    /// </summary>
    internal static Expr SpineReentryChain(int layers)
    {
        Expr e = new Expr.Num(5);
        for (var i = 0; i < layers; i++)
            e = new Expr.Index(new Expr.Capture([e]), new Expr.Num(0));
        return e;
    }

    /// <summary>
    /// Join alternation: <c>Spread(Construct(inner, 0))</c> per layer — the spread-of-construct
    /// re-entry link between the two iterative join helpers. Each layer appends one item.
    /// </summary>
    internal static Expr JoinAlternationChain(int alternations)
    {
        Expr e = new Expr.Num(1);
        for (var i = 0; i < alternations; i++)
            e = new Expr.SequenceSpread(new Expr.SequenceConstruct(e, new Expr.Num(0)));
        return e;
    }

    /// <summary>
    /// Join hand-off: <c>Construct(F(inner), ())</c> per layer — every layer hands off from
    /// the iterative join machine into a recursive user call, while the empty-sequence right
    /// operand (dropped by construct-join semantics) keeps the running value a SCALAR so
    /// <c>F(x) = x + 1</c> stays applicable at every depth. Requires the helper program scope,
    /// so callers wrap it via <see cref="AstGraphFuzzer.WrapInProgram"/>. The accepted edge
    /// evaluates to 1 + layer count.
    /// </summary>
    internal static Expr JoinHandoffChain(int handoffs)
    {
        Expr e = new Expr.Num(1);
        for (var i = 0; i < handoffs; i++)
        {
            e = new Expr.SequenceConstruct(
                new Expr.Call(new Expr.Resolve("F"), [e]),
                new Expr.EmptySequence(0));
        }

        return e;
    }

    /// <summary>Arbitrarily long single-kind join spine: a supported, pinned, zero-weight shape.</summary>
    internal static Expr PureJoinSpine(int constructs)
    {
        Expr e = new Expr.Num(1);
        for (var i = 0; i < constructs; i++)
            e = new Expr.SequenceConstruct(e, new Expr.Num(1));
        return e;
    }

    /// <summary>
    /// The classic shared doubling diamond: <c>e = e + e</c> with BOTH operands the same
    /// reference. Physical size O(depth); weighted structural depth = depth + 1 (spine nodes);
    /// semantic evaluation work 2^depth. Preflight accepts it — stack safety is per-path — and
    /// the unbounded dimension is governed by the (opt-in) step budget, exactly like a long
    /// loop. Callers must always evaluate it under a configured MaxSteps.
    /// </summary>
    internal static Expr DoublingDiamond(int depth)
    {
        Expr e = new Expr.Num(1);
        for (var i = 0; i < depth; i++)
            e = new Expr.Binary(BinaryOp.Add, e, e);
        return e;
    }

    /// <summary>One chargeable work node referenced <paramref name="occurrences"/> times under a shallow root.</summary>
    internal static Expr SharedWideRoot(int occurrences)
    {
        var work = new Expr.Call(
            new Expr.Resolve("sum"),
            [new Expr.Capture([new Expr.Num(1), new Expr.Num(2), new Expr.Num(3), new Expr.Num(4)])]);
        var slots = new Expr[occurrences];
        Array.Fill(slots, work);
        return new Expr.Capture(new OutputBundle(slots));
    }

    /// <summary>
    /// One shared subtree reached through a short route AND a long route. With the long route
    /// sized so (route + shared height) exceeds the limit, the graph must be REJECTED even
    /// though the shared subtree alone (and the short route) is fine — the memoized shared
    /// height must be re-judged per path.
    /// </summary>
    internal static Expr SharedDeepRouteDiamond(int sharedHeight, int longRoute)
    {
        var shared = UnaryChain(sharedHeight);
        Expr route = shared;
        for (var i = 0; i < longRoute; i++)
            route = new Expr.Unary(UnaryOp.Minus, route);
        return new Expr.Capture([shared, route]);
    }

    /// <summary>
    /// Largest n in [1, hi] with <paramref name="build"/>(n) preflight-accepted under the
    /// evaluator profile, verifying the family is monotone at the boundary (n+1 rejects).
    /// </summary>
    internal static int MaxAccepted(Func<int, Expr> build, int hi)
    {
        static bool Accepted(Expr program)
            => AstStructuralPreflight.Check(
                program, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.EvaluatorIterativeJoinSpines)
                is null;

        var lo = 1;
        Assert.True(Accepted(build(lo)), "family floor must be accepted");
        Assert.False(Accepted(build(hi)), "family ceiling must be rejected — envelope too small?");
        while (hi - lo > 1)
        {
            var mid = lo + ((hi - lo) / 2);
            if (Accepted(build(mid)))
                lo = mid;
            else
                hi = mid;
        }

        Assert.True(Accepted(build(lo)));
        Assert.False(Accepted(build(lo + 1)));
        return lo;
    }
}

/// <summary>
/// In-process verdict-level boundary campaign: exact accepted/rejected edges, per-family safety
/// envelopes, shared-route re-judgment, and the accepted-but-semantically-huge diamond staying
/// governed by the structured step budget. The 1 MiB physical execution of every maximum
/// accepted member lives in <see cref="AstGraphFuzzProcessTests"/>.
/// </summary>
public class AstGraphFuzzBoundaryTests
{
    private static AstStructuralRejection? Check(Expr program)
        => AstStructuralPreflight.Check(
            program, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.EvaluatorIterativeJoinSpines);

    [Fact]
    public void UnaryChain_HasAnExactAcceptedEdge_DerivedFromTheCeiling()
    {
        // Cost = chain length + leaf, so the exact boundary is MaxSupportedAstDepth - 1 links.
        var exactlyAtLimit = BoundaryFamilies.UnaryChain(EvaluationLimits.MaxSupportedAstDepth - 1);
        Assert.Null(Check(exactlyAtLimit));

        var oneOver = BoundaryFamilies.UnaryChain(EvaluationLimits.MaxSupportedAstDepth);
        var rejection = Check(oneOver);
        Assert.NotNull(rejection);
        Assert.Equal(AstStructuralViolation.DepthExceeded, rejection.Kind);

        // The accepted edge EVALUATES (iterative spine): (-1)^299 * 5 = -5.
        var result = Evaluator.Run(exactlyAtLimit);
        Assert.False(result.IsError);
        Assert.Equal([-5m], result.Value.ToAtoms());

        // And the rejected edge surfaces the STRUCTURED error through the entry point.
        var rejected = Evaluator.Run(oneOver);
        Assert.True(rejected.IsError);
        var error = Assert.IsType<EvalError.AstDepthLimitExceeded>(rejected.Error);
        Assert.Equal(EvaluationLimits.MaxSupportedAstDepth, error.Limit);
    }

    [Fact]
    public void SpineReentryAlternation_StaysInsideItsSafetyEnvelope()
    {
        var maxAccepted = BoundaryFamilies.MaxAccepted(BoundaryFamilies.SpineReentryChain, hi: 60);

        // Process-isolated probes measured overflow at ~60 alternations on a 1 MiB Debug
        // stack; the envelope fails this test if a cost-model edit ever re-admits that class.
        Assert.InRange(maxAccepted, 20, 40);

        var rejected = Evaluator.Run(BoundaryFamilies.SpineReentryChain(maxAccepted + 1));
        Assert.True(rejected.IsError);
        Assert.IsType<EvalError.AstDepthLimitExceeded>(rejected.Error);

        var accepted = Evaluator.Run(BoundaryFamilies.SpineReentryChain(maxAccepted));
        Assert.False(accepted.IsError);
        Assert.Equal([5m], accepted.Value.ToAtoms());
    }

    [Fact]
    public void JoinAlternation_StaysInsideItsSafetyEnvelope()
    {
        var maxAccepted = BoundaryFamilies.MaxAccepted(BoundaryFamilies.JoinAlternationChain, hi: 80);
        Assert.InRange(maxAccepted, 25, 40);

        var rejected = Evaluator.Run(BoundaryFamilies.JoinAlternationChain(maxAccepted + 1));
        Assert.True(rejected.IsError);
        Assert.IsType<EvalError.AstDepthLimitExceeded>(rejected.Error);

        // The accepted edge evaluates: each layer appends one 0 item after the leading 1.
        var accepted = Evaluator.Run(BoundaryFamilies.JoinAlternationChain(maxAccepted));
        Assert.False(accepted.IsError);
        var atoms = accepted.Value.ToAtoms();
        Assert.Equal(maxAccepted + 1, atoms.Count);
        Assert.Equal(1m, atoms[0]);
    }

    [Fact]
    public void JoinHandoff_StaysInsideItsSafetyEnvelope()
    {
        static Expr Wrapped(int n)
            => AstGraphFuzzer.WrapInProgram(BoundaryFamilies.JoinHandoffChain(n));

        var maxAccepted = BoundaryFamilies.MaxAccepted(Wrapped, hi: 80);
        Assert.InRange(maxAccepted, 20, 40);

        var rejected = Evaluator.Run(Wrapped(maxAccepted + 1));
        Assert.True(rejected.IsError);
        Assert.IsType<EvalError.AstDepthLimitExceeded>(rejected.Error);

        // Each layer applies F once to the running scalar: 1 + layer count.
        var accepted = Evaluator.Run(Wrapped(maxAccepted));
        Assert.False(accepted.IsError, accepted.IsError ? accepted.Error.ToString() : null);
        Assert.Equal([1m + maxAccepted], accepted.Value.ToAtoms());
    }

    [Fact]
    public void PureJoinSpine_OfThousandsOfNodes_StaysAcceptedAndIterative()
    {
        // A construct spine forms ONE sequence VALUE containing every joined item (the join is
        // a value former, not a multi-row emitter)...
        var spine = AstGraphFuzzer.WrapInProgram(BoundaryFamilies.PureJoinSpine(4_000));
        Assert.Null(Check(spine));

        var joined = Evaluator.RunCounted(spine);
        Assert.False(joined.IsError);
        Assert.Equal(1, joined.Value.EmittedCount);
        Assert.Equal(4_001, joined.Value.Value.ToAtoms().Count);

        // ...while a SPREAD row over the same spine re-supplies the items to root output
        // accumulation, which keeps the multi-item emission.
        var spreadRow = AstGraphFuzzer.WrapInProgram(
            new Expr.SequenceSpread(BoundaryFamilies.PureJoinSpine(4_000)));
        Assert.Null(Check(spreadRow));

        var spread = Evaluator.RunCounted(spreadRow);
        Assert.False(spread.IsError);
        Assert.Equal(4_001, spread.Value.EmittedCount);
    }

    [Fact]
    public void WideShallowCapture_IsAcceptedAndEvaluates()
    {
        var items = new Expr[2_000];
        for (var i = 0; i < items.Length; i++)
            items[i] = new Expr.Num(1);
        var wide = new Expr.Capture(new OutputBundle(items));

        Assert.Null(Check(wide));
        var count = Evaluator.Run(new Expr.DotCall(wide, "count"));
        Assert.False(count.IsError);
        Assert.Equal([2_000m], count.Value.ToAtoms());
    }

    [Fact]
    public void SharedSubtree_ReachedThroughALongerRoute_IsReJudgedAtThatDepth()
    {
        // Shared subtree height 150; short route sees it at depth ~152 (fine); the long route
        // adds 160 more levels, so its path is ~311 > 300: the WHOLE graph must reject, and the
        // fully expanded clone must agree — sharing must not hide the deeper occurrence.
        var rejectedShared = BoundaryFamilies.SharedDeepRouteDiamond(sharedHeight: 150, longRoute: 160);
        var sharedRejection = Check(rejectedShared);
        Assert.NotNull(sharedRejection);
        Assert.Equal(AstStructuralViolation.DepthExceeded, sharedRejection.Kind);

        var clonedEquivalent = new Expr.Capture([
            BoundaryFamilies.UnaryChain(150),
            BoundaryFamilies.UnaryChain(310),
        ]);
        var clonedRejection = Check(clonedEquivalent);
        Assert.NotNull(clonedRejection);
        Assert.Equal(sharedRejection.Kind, clonedRejection.Kind);

        // With a short second route the same sharing is accepted and evaluates.
        var acceptedShared = BoundaryFamilies.SharedDeepRouteDiamond(sharedHeight: 150, longRoute: 100);
        Assert.Null(Check(acceptedShared));
        var result = Evaluator.Run(acceptedShared);
        Assert.False(result.IsError);
    }

    [Fact]
    public void DoublingDiamond_IsAcceptedByPreflight_AndGovernedByTheStepBudget()
    {
        // Physical size 41 nodes, semantic work 2^40: the preflight (a STACK-safety gate)
        // accepts it — per-path depth is tiny — and the unbounded dimension is semantic WORK,
        // governed by the opt-in step budget like any long computation. Verdict only at this
        // size: even the budgeted run of the full shape is far too slow for CI.
        Assert.Null(Check(BoundaryFamilies.DoublingDiamond(40)));

        // The budgeted execution contract is pinned at depth 20 (2^20 ≈ 1M semantic
        // operations). Bulk expression work is charged at checkpoint granularity (~4096
        // operations per step), so a 100-step budget trips after ~410k operations — safely
        // inside the shape, in milliseconds: structured failure, deterministically, twice.
        var diamond = BoundaryFamilies.DoublingDiamond(20);
        Assert.Null(Check(diamond));

        var limits = new EvaluationLimits { MaxSteps = 100 };
        for (var attempt = 0; attempt < 2; attempt++)
        {
            var result = Evaluator.Run(diamond, limits);
            Assert.True(result.IsError);
            var error = result.Error;
            while (error is EvalError.WithContext context)
                error = context.Inner;
            Assert.IsType<EvalError.EvaluationStepLimitExceeded>(error);
        }
    }

    /// <summary>
    /// Physical sharing must not change the RESOURCE verdict: the same semantic program shaped
    /// as a shared DAG and as an expanded clone tree must succeed/fail identically under the
    /// same configured step budget (invariant 13).
    /// </summary>
    [Fact]
    public void StepVerdict_IsIndependentOfPhysicalSharing()
    {
        var sharedSmall = BoundaryFamilies.DoublingDiamond(6);

        Expr ClonedDiamond(int depth)
        {
            if (depth == 0)
                return new Expr.Num(1);
            return new Expr.Binary(BinaryOp.Add, ClonedDiamond(depth - 1), ClonedDiamond(depth - 1));
        }

        var cloned = ClonedDiamond(6);

        foreach (var maxSteps in new long[] { 40, 100_000 })
        {
            var limits = new EvaluationLimits { MaxSteps = maxSteps };
            var sharedResult = Evaluator.Run(sharedSmall, limits);
            var clonedResult = Evaluator.Run(cloned, limits);
            Assert.Equal(sharedResult.IsError, clonedResult.IsError);
            if (sharedResult.IsError)
            {
                Assert.Equal(sharedResult.Error.GetType(), clonedResult.Error.GetType());
            }
            else
            {
                Assert.Equal([64m], sharedResult.Value.ToAtoms());
                Assert.Equal([64m], clonedResult.Value.ToAtoms());
            }
        }
    }
}
