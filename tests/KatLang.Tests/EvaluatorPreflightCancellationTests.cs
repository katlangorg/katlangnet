using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// The evaluator's admission walks observe the run's cancellation token (finding
/// lifting-signatures-fe3-sharing-breaks-on-meeting-names of the 2026-11-21 adversarial performance audit): the
/// structural preflight before its first edge and after every <see cref="AstStructuralPreflight.CancellationCheckpointEdges"/>
/// edges (<see cref="FrontEndCancellationCheckpoint.EvaluatorPreflight"/>), the pre-evaluation validation walk at every
/// algorithm it expands. Before, a run read its token before the preflight and next at its first evaluation chokepoint,
/// so a host could not cancel the admission of a large program — owners whose meeting names keep their signatures
/// distinct, or an expanded host-built tree — however long it took.
///
/// <para>The walk's verdict, its program facts (J7 plan retention, runtime-alias reach, alias freedom, node counts) and
/// its hand-over are those of a walk without a token: cancellation is the only new outcome. Every cancellation is placed
/// by the checkpoint hook, which runs BEFORE the token is read, so the cancelling checkpoint itself observes it; tests
/// assert outcomes, token identity and edge counts, never time. Host-only policy: Lean has no cancellation.</para>
/// </summary>
public sealed class EvaluatorPreflightCancellationTests
{
    private const int Block = AstStructuralPreflight.CancellationCheckpointEdges;
    private const int Limit = EvaluationLimits.MaxSupportedAstDepth;
    private const AstConsumerProfile Profile = AstConsumerProfile.EvaluatorIterativeJoinSpines;

    /// <summary>
    /// A host-built program of <paramref name="owners"/> owners, each holding its OWN <paramref name="width"/>-wide
    /// parameter list (nothing shared): the expanded structure an admission walks edge by edge.
    /// </summary>
    private static Expr ExpandedOwners(int owners, int width)
    {
        var properties = new List<Property>();
        for (var i = 0; i < owners; i++)
        {
            ParameterPattern[] patterns = [.. Enumerable.Range(0, width).Select(j => new CaptureParameterPattern($"v{j}"))];
            properties.Add(new Property($"A{i}", new Algorithm.User(null, patterns, [], [], new OutputBundle([new Expr.Param("v0")]))));
        }

        return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], properties, new OutputBundle([new Expr.Num(1)])));
    }

    /// <summary>Owners whose own names meet one callee at distinct names: parsed, their parts stay distinct per owner.</summary>
    private static Expr DistinctMeetingOwners(int owners, int width)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(
            $"G = {string.Join(" + ", Enumerable.Range(0, width).Select(i => $"v{i}"))}\n"
                + string.Concat(Enumerable.Range(0, owners).Select(i => $"A{i} = G + v{i % width}\n")) + "1").Root);

    private static (FrontEndTraversalObservations Traversal, CancellationTokenSource Source) CancelAt(
        FrontEndCancellationCheckpoint kind, long ordinal)
    {
        var source = new CancellationTokenSource();
        var traversal = new FrontEndTraversalObservations
        {
            CheckpointReached = (reached, count) =>
            {
                if (reached == kind && count == ordinal)
                    source.Cancel();
            },
        };
        return (traversal, source);
    }

    private static long Edges(Expr program)
    {
        var traversal = new FrontEndTraversalObservations();
        Assert.Null(AstStructuralPreflight.Check(program, Limit, Profile, traversal));
        return traversal.StructuralPreflightEdges;
    }

    [Fact]
    public void CancelledAtThePreflightBoundary_EscapesWithTheRunToken_BeforeAnyEdge()
    {
        var program = ExpandedOwners(64, 64);
        var (traversal, cancellation) = CancelAt(FrontEndCancellationCheckpoint.EvaluatorPreflight, 1);
        using (cancellation)
        {
            var error = Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(program,
                observations: new EvaluationObservations { PreEvaluationTraversal = traversal }, cancellationToken: cancellation.Token));
            Assert.Equal(cancellation.Token, error.CancellationToken);
        }

        Assert.Equal(0, traversal.StructuralPreflightEdges);
        Assert.Equal(1, traversal.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.EvaluatorPreflight));
        // The validation walk never started.
        Assert.Equal(0, traversal.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.WalkerAlgorithm));
        Assert.Equal(0, traversal.WalkerSteps);
    }

    /// <summary>
    /// A cancellation requested inside the walk stops it at the next block boundary: the walk has followed exactly the
    /// blocks before the cancelling checkpoint, on the synchronous route, the async fast path and the async twin path.
    /// </summary>
    [Theory]
    [InlineData(2, "sync")]
    [InlineData(4, "sync")]
    [InlineData(3, "async")]
    [InlineData(3, "twin")]
    public async Task CancelledInsideTheWalk_StopsWithinOneBlockOfEdges(long ordinal, string route)
    {
        foreach (var program in new[] { ExpandedOwners(72, 64), DistinctMeetingOwners(96, 80) })
        {
            Assert.InRange(Edges(program), ordinal * Block, long.MaxValue);
            var (traversal, cancellation) = CancelAt(FrontEndCancellationCheckpoint.EvaluatorPreflight, ordinal);
            using (cancellation)
            {
                var observations = new EvaluationObservations { PreEvaluationTraversal = traversal };
                var error = route switch
                {
                    "sync" => Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(program,
                        observations: observations, cancellationToken: cancellation.Token)),
                    "async" => await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await Evaluator.RunCountedObservedAsync(program,
                        observations: observations, cancellationToken: cancellation.Token)),
                    _ => await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await Evaluator.RunCountedObservedAsync(program,
                        zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                        observations: observations, cancellationToken: cancellation.Token)),
                };
                Assert.Equal(cancellation.Token, error.CancellationToken);
            }

            Assert.Equal((ordinal - 1) * Block, traversal.StructuralPreflightEdges);
            Assert.Equal(ordinal, traversal.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.EvaluatorPreflight));
            Assert.Equal(0, traversal.WalkerSteps);
        }
    }

    /// <summary>
    /// The validation walk that follows an accepted preflight observes the same token at every algorithm: the whole
    /// preflight ran, its blocks were all observed, and the walk stops at the cancelling algorithm.
    /// </summary>
    [Fact]
    public void TheValidationWalk_ObservesTheRunToken_AfterTheWholePreflight()
    {
        var program = ExpandedOwners(48, 48);
        var edges = Edges(program);
        var (traversal, cancellation) = CancelAt(FrontEndCancellationCheckpoint.WalkerAlgorithm, 3);
        using (cancellation)
        {
            var error = Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(program,
                observations: new EvaluationObservations { PreEvaluationTraversal = traversal }, cancellationToken: cancellation.Token));
            Assert.Equal(cancellation.Token, error.CancellationToken);
        }

        Assert.Equal(edges, traversal.StructuralPreflightEdges);
        Assert.Equal(1 + edges / Block, traversal.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.EvaluatorPreflight));
        Assert.Equal(3, traversal.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.WalkerAlgorithm));
    }

    public static TheoryData<string> AdmissionPrograms =>
    [
        "expanded",
        "meeting",
        "loop",
        "meta",
        "alias",
        "deep",
    ];

    private static (Expr Program, EvaluationLimits? Limits) AdmissionProgram(string name) => name switch
    {
        "expanded" => (ExpandedOwners(40, 40), null),
        "meeting" => (DistinctMeetingOwners(40, 40), null),
        // J7: a loop spelling makes the run retain plans per site.
        "loop" => (AsyncEvaluationHarness.Ast("Countdown = x - 1, x > 1\nCountdown(5).while"), null),
        "meta" => (AsyncEvaluationHarness.Ast("Square(x) = x * x\nCapture(meta operation) = operation\nR = Capture(Square(5))\nR.Invoke()"), null),
        "alias" => (AsyncEvaluationHarness.Ast("F(x) = x + 1\nA = F\nA(2)"), null),
        // Refused by the structural preflight under a lowered depth limit.
        _ => (AsyncEvaluationHarness.Ast("[[[[[[[[1]]]]]]]]"), new EvaluationLimits { MaxAstDepth = 5 }),
    };

    /// <summary>
    /// A token that is never cancelled changes nothing but the checkpoint count: the same verdict, program facts, table
    /// hand-over, plan-retention decision and result as a run without one, accepted or refused.
    /// </summary>
    [Theory]
    [MemberData(nameof(AdmissionPrograms))]
    public void ALiveToken_ChangesNoVerdictFactOrPlanGate(string name)
    {
        var (program, limits) = AdmissionProgram(name);
        var limit = (limits ?? EvaluationLimits.Default).EffectiveMaxAstDepth;
        using var live = new CancellationTokenSource();
        var plainVerdict = AstStructuralPreflight.CheckAdmittedProgram(program, limit, Profile, out var plainFacts);
        var liveVerdict = AstStructuralPreflight.CheckAdmittedProgram(program, limit, Profile, out var liveFacts,
            cancellationToken: live.Token);
        Assert.Equal(plainVerdict, liveVerdict);
        Assert.Equal(plainFacts, liveFacts);

        var plain = new FrontEndTraversalObservations();
        var (plainResult, plainBudget) = Evaluator.RunCountedObserved(program, limits,
            observations: new EvaluationObservations { PreEvaluationTraversal = plain });
        var observed = new FrontEndTraversalObservations();
        var (liveResult, liveBudget) = Evaluator.RunCountedObserved(program, limits,
            observations: new EvaluationObservations { PreEvaluationTraversal = observed }, cancellationToken: live.Token);

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(plainResult), AsyncEvaluationHarness.NeutralOf(liveResult));
        Assert.Equal(plainResult.IsError ? plainResult.Error.Span : null, liveResult.IsError ? liveResult.Error.Span : null);
        Assert.Equal(plainBudget.RetainsInvocationPlans, liveBudget.RetainsInvocationPlans);
        Assert.Equal(plainBudget.UsesPerSiteInvocationPlans, liveBudget.UsesPerSiteInvocationPlans);
        Assert.Equal(plainBudget.MayReachRuntimeAliases, liveBudget.MayReachRuntimeAliases);
        Assert.Equal(plainBudget.ConsumedSteps, liveBudget.ConsumedSteps);
        Assert.Equal(plain.StructuralPreflightEdges, observed.StructuralPreflightEdges);
        Assert.Equal(plain.StructuralPreflightCapacityHints, observed.StructuralPreflightCapacityHints);
        Assert.Equal(plain.PreEvaluationHandedOverTables, observed.PreEvaluationHandedOverTables);
        Assert.Equal(plain.PreEvaluationAliasReachTables, observed.PreEvaluationAliasReachTables);
        Assert.Equal(plain.WalkerSteps, observed.WalkerSteps);

        // Without a token the walk records no checkpoint of its own; with one, one per block plus its start.
        Assert.Equal(0, plain.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.EvaluatorPreflight));
        Assert.Equal(1 + observed.StructuralPreflightEdges / Block,
            observed.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.EvaluatorPreflight));
        Assert.Equal(name == "deep", liveResult.IsError && liveResult.Error is EvalError.AstDepthLimitExceeded);
    }

    /// <summary>
    /// Host cancellation preempts the verdict: a program the preflight would refuse still escapes as a cancellation when
    /// the token is cancelled at the preflight boundary, exactly as an already cancelled token did at the entry.
    /// </summary>
    [Fact]
    public void ACancellationAtTheBoundary_PreemptsARefusal()
    {
        var (program, limits) = AdmissionProgram("deep");
        var (traversal, cancellation) = CancelAt(FrontEndCancellationCheckpoint.EvaluatorPreflight, 1);
        using (cancellation)
        {
            var error = Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(program, limits,
                observations: new EvaluationObservations { PreEvaluationTraversal = traversal }, cancellationToken: cancellation.Token));
            Assert.Equal(cancellation.Token, error.CancellationToken);
        }

        Assert.Equal(0, traversal.StructuralPreflightEdges);
    }

    [Fact]
    public void ACancellationDuringRejection_StopsTheReplayOfAWideSharedBundle()
    {
        var span = new SourceSpan(7, 1, 7, 2);
        Expr deep = new Expr.Num(1);
        for (var i = 0; i < 10; i++)
            deep = new Expr.Unary(UnaryOp.Minus, deep);
        var slots = Enumerable.Repeat<Expr>(new Expr.Num(0), 3 * Block).Append(deep with { Span = span }).ToArray();
        var shared = new OutputBundle(slots);
        Expr second = new Expr.Call(new Expr.Resolve("F"), shared);
        for (var i = 0; i < 8; i++)
            second = new Expr.Unary(UnaryOp.Minus, second);
        var root = new Expr.Binary(BinaryOp.Add, new Expr.Call(new Expr.Resolve("F"), shared), second);
        const int limit = 24;
        var plain = new FrontEndTraversalObservations();
        var rejection = AstStructuralPreflight.CheckAdmittedProgram(root, limit, Profile, out _, observations: plain);
        Assert.Equal(new AstStructuralRejection(AstStructuralViolation.DepthExceeded, span), rejection);

        // The ordinary descent is complete. Cancel one block into the replay that locates the crossing slot.
        var ordinal = 1 + plain.StructuralPreflightEdges / Block + 2;
        var (traversal, cancellation) = CancelAt(FrontEndCancellationCheckpoint.EvaluatorPreflight, ordinal);
        using (cancellation)
        {
            var error = Assert.ThrowsAny<OperationCanceledException>(() => AstStructuralPreflight.CheckAdmittedProgram(
                root, limit, Profile, out _, observations: traversal, cancellationToken: cancellation.Token));
            Assert.Equal(cancellation.Token, error.CancellationToken);
        }
        Assert.Equal(plain.StructuralPreflightEdges, traversal.StructuralPreflightEdges);
        Assert.Equal(ordinal, traversal.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.EvaluatorPreflight));
    }

    /// <summary>
    /// The front end's own structural checks take no token: whichever profile they walk, they record no evaluator
    /// checkpoint, and a parse records none either.
    /// </summary>
    [Fact]
    public void FrontEndChecks_RecordNoEvaluatorCheckpoint()
    {
        var program = DistinctMeetingOwners(40, 40);
        foreach (var profile in new[] { AstConsumerProfile.FullyRecursive, Profile })
        {
            var observations = new FrontEndTraversalObservations();
            Assert.Null(AstStructuralPreflight.Check(program, Limit, profile, observations));
            Assert.InRange(observations.StructuralPreflightEdges, Block, long.MaxValue);
            Assert.Equal(0, observations.CancellationCheckpoints);
        }

        var parse = new FrontEndTraversalObservations();
        Assert.False(Parser.ParseObserved("G = v0 + v1\nA = G + v0\nA(1, 2)", options: null, parse).HasErrors);
        Assert.Equal(0, parse.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.EvaluatorPreflight));
    }

    [Theory]
    [InlineData("valid", "valid")]
    [InlineData("valid", "nested")]
    [InlineData("valid", "repeated")]
    [InlineData("nested", "valid")]
    [InlineData("repeated", "valid")]
    public void MetaPlacement_MatchesPlainHostLists_AcrossOwnersOfOneTail(string headForm, string tailForm)
    {
        static ParameterPattern[] Part(string name, string form)
        {
            var meta = new CaptureParameterPattern(name, Kind: ParameterKind.Meta);
            return form switch
            {
                "nested" => [new ListValueParameterPattern([meta])],
                "repeated" => [new CaptureParameterPattern(name), meta],
                _ => [meta],
            };
        }

        var head = Part("h", headForm);
        var tail = ImplicitSignatureTemplate.Flat(Part("t", tailForm));
        Expr Program(bool share)
        {
            Algorithm.User Owner(ParameterPattern[] local) => new(null,
                share ? ImplicitSignatureTemplate.Compose(local, tail) : [.. local, .. tail],
                [], [], [new Expr.Num(1)]);
            return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [],
                [new Property("A", Owner([new CaptureParameterPattern("a")])), new Property("B", Owner(head))],
                [new Expr.Num(0)]));
        }

        var compact = Program(true);
        var plain = Program(false);
        Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(compact, Limit, Profile, out var compactFacts));
        Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(plain, Limit, Profile, out var plainFacts));
        Assert.True(plainFacts.HasMetaBinder && compactFacts.HasMetaBinder);
        Assert.Equal(plainFacts.MayCaptureCalls, compactFacts.MayCaptureCalls);
        var expected = AlgorithmValidation.FindFirstPreEvaluationViolation(plain);
        var actual = AlgorithmValidation.FindFirstPreEvaluationViolation(compact);
        Assert.Equal(expected, actual);
        if (headForm == "valid" && tailForm == "valid")
            Assert.Null(actual);
        else
            Assert.IsType<PreEvaluationAstViolation.InvalidMetaParameter>(actual);
    }
}
