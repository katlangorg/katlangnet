using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// A host-constructed <see cref="Expr"/> AST is legally a DAG, not a tree: the structural
/// preflight accepts shared acyclic subtrees (reference-memoized), so the front-end passes
/// behind it must do work proportional to the DISTINCT reachable nodes they traverse — never to
/// the root-to-node paths. A doubling diamond (<c>N0 = leaf; Nk = Binary(N(k-1), N(k-1))</c>)
/// has k distinct interior nodes but 2^k paths, so a path-expanding walk is exponential in k on
/// input the preflight accepts (M4 of the architecture review).
///
/// <para>The work counts here are exact and deterministic, measured through the passive
/// pass-scoped <see cref="FrontEndTraversalObservations"/> handed to the internal observation
/// overloads; the production paths carry no observer. Timing is deliberately not the pass/fail
/// signal — the "completes at all" witnesses use depths (250/600 doublings) where a
/// path-expanding walk could not finish in any amount of real time, so completion itself is the
/// proof. The deep cases additionally run under a generous SECONDARY wall-clock net
/// (<see cref="AssertCompletesUnderWallClockGuard(Func{Task})"/>) so a regression there fails
/// deterministically instead of wedging the run.</para>
///
/// <para>Semantics are pinned against the tree-vs-DAG oracle: a shared DAG must elaborate
/// exactly like its fully duplicated tree (free-name discovery, implicit lifting, exposure,
/// dependency edges, grace-weight arithmetic), while the rewritten output must PRESERVE the
/// input's sharing rather than expanding it. The one deliberate per-NODE behavior is side-effect
/// multiplicity: a shared erroneous node is diagnosed once per diagnostic context, and a shared
/// load call is one load site per constant load-context/live-depth region.</para>
/// </summary>
public class FrontEndDagComplexityTests
{
    /// <summary>Depths chosen so path-expanding walks differ by 2^20 between them.</summary>
    private const int ShallowDepth = 20;

    private const int DeepDepth = 40;

    private static Algorithm.User EmptyAlgorithm(params Expr[] output)
        => new(Parent: null, Parameters: [], Opens: [], Properties: [], Output: output);

    /// <summary>
    /// The doubling diamond: depth interior Binary nodes, one shared leaf, 2^depth root-to-leaf
    /// paths. Every level references the SAME child object twice.
    /// </summary>
    private static Expr BinaryDiamond(int depth, Expr leaf)
    {
        var node = leaf;
        for (var i = 0; i < depth; i++)
            node = new Expr.Binary(BinaryOp.Add, node, node);
        return node;
    }

    /// <summary>
    /// The fully expanded tree with the same semantic content as <see cref="BinaryDiamond"/>:
    /// every occurrence is a FRESH node (2^depth leaves), so it must stay small.
    /// </summary>
    private static Expr BinaryTree(int depth, Func<Expr> leafFactory)
        => depth == 0
            ? leafFactory()
            : new Expr.Binary(BinaryOp.Add, BinaryTree(depth - 1, leafFactory), BinaryTree(depth - 1, leafFactory));

    /// <summary>
    /// Asserts the rewritten diamond kept its sharing at every level, including a childless
    /// leaf that a rewrite may replace (Resolve to Param/Call). Analysis walks can reprocess a
    /// leaf in O(1), but a rewriting pass must memoize a replaced leaf or it expands one shared
    /// input object into several output objects.
    /// </summary>
    private static Expr AssertDiamondSharingPreserved(Expr rewrittenRoot, int depth)
    {
        var current = rewrittenRoot;
        for (var level = 0; level < depth; level++)
        {
            var binary = Assert.IsType<Expr.Binary>(current);
            Assert.Same(binary.Left, binary.Right);
            current = binary.Left;
        }

        return current;
    }

    /// <summary>
    /// Generous SECONDARY wall-clock net for the deep cases. The PRIMARY regression signal
    /// stays the exact expansion counters and sharing pins, which fail within seconds at
    /// <see cref="ShallowDepth"/> under a broken memo — but the deep shapes wrapped in this
    /// guard (2^40 to 2^600 root-to-node paths) would spin through path expansion instead of
    /// reaching any assertion, wedging the run until an outer job timeout. The guard turns
    /// that hang into a deterministic failure. A healthy build finishes each wrapped
    /// traversal in milliseconds, so thirty seconds cannot flake, and timing is never the
    /// pass/fail signal for correct code — the same pattern as the aliased-cycle probe in
    /// <c>SharedValueGraphComplexityTests</c>. The work runs on a pool thread, which keeps
    /// the documented 1 MiB default stack the deep shapes are calibrated for.
    /// </summary>
    private static async Task AssertCompletesUnderWallClockGuard(Func<Task> traversalWork)
    {
        var work = Task.Run(traversalWork);
        var finished = await Task.WhenAny(work, Task.Delay(TimeSpan.FromSeconds(30)));
        Assert.True(
            ReferenceEquals(finished, work),
            "The deep shared-DAG traversal did not complete within the generous wall-clock guard. "
            + "Distinct-node-bounded work finishes in milliseconds, so this indicates a "
            + "path-expanding (exponential) traversal regression.");
        await work;
    }

    private static Task AssertCompletesUnderWallClockGuard(Action traversalWork)
        => AssertCompletesUnderWallClockGuard(() =>
        {
            traversalWork();
            return Task.CompletedTask;
        });

    // ── 1. ParameterDetector ────────────────────────────────────────────────

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public Task Detector_DiamondWithFreeName_ExpandsEachDistinctNodeOnce(int depth)
        => AssertCompletesUnderWallClockGuard(() =>
        {
            var observations = new FrontEndTraversalObservations();
            var root = EmptyAlgorithm(BinaryDiamond(depth, new Expr.Resolve("q")));

            var (detected, diagnostics) = ParameterDetector.DetectPrevalidated(root, null, observations);

            Assert.Empty(diagnostics);
            // Free-name discovery is unchanged: the one distinct free leaf infers ONE parameter.
            Assert.Equal(["q"], detected.Params);

            // Exactly the `depth` distinct interior nodes expand, once per walk (collection and
            // rewrite are separate walks); the shared leaf is childless and never counted. The
            // path-expanding walk expanded 2^(depth+1) - 1 occurrences.
            Assert.Equal(depth, observations.DetectorCollectExpansions);
            Assert.Equal(depth, observations.DetectorRewriteExpansions);

            // The rewritten output preserves the input DAG's sharing and still rewrote the
            // occurrence: the single shared leaf became a Param.
            var rewrittenLeaf = AssertDiamondSharingPreserved(detected.Output[0], depth);
            Assert.Equal("q", Assert.IsType<Expr.Param>(rewrittenLeaf).Name);
        });

    [Fact]
    public Task Detector_WorkGrowsLinearlyWithDiamondDepth()
        => AssertCompletesUnderWallClockGuard(() =>
        {
            var shallow = new FrontEndTraversalObservations();
            var deep = new FrontEndTraversalObservations();

            ParameterDetector.DetectPrevalidated(
                EmptyAlgorithm(BinaryDiamond(ShallowDepth, new Expr.Resolve("q"))), null, shallow);
            ParameterDetector.DetectPrevalidated(
                EmptyAlgorithm(BinaryDiamond(DeepDepth, new Expr.Resolve("q"))), null, deep);

            // Twenty more levels cost twenty more expansions per walk, not 2^20 times as many.
            Assert.Equal(DeepDepth - ShallowDepth, deep.DetectorCollectExpansions - shallow.DetectorCollectExpansions);
            Assert.Equal(DeepDepth - ShallowDepth, deep.DetectorRewriteExpansions - shallow.DetectorRewriteExpansions);
        });

    [Fact]
    public void Detector_MemoIsPerCall_ASecondDetectionRecountsInFull()
    {
        var observations = new FrontEndTraversalObservations();
        var root = EmptyAlgorithm(BinaryDiamond(ShallowDepth, new Expr.Resolve("q")));

        ParameterDetector.DetectPrevalidated(root, null, observations);
        ParameterDetector.DetectPrevalidated(root, null, observations);

        // No memo state survives a detection: the second call re-expands every node.
        Assert.Equal(2 * ShallowDepth, observations.DetectorCollectExpansions);
        Assert.Equal(2 * ShallowDepth, observations.DetectorRewriteExpansions);
    }

    /// <summary>
    /// The near-ceiling completion witness: 250 doublings pass the structural preflight
    /// (weighted depth 252 of 300) and have 2^250 root-to-leaf paths, so a path-expanding
    /// walk could not finish in any amount of real time — completion IS the boundedness proof.
    /// </summary>
    [Fact]
    public Task Detector_NearCeilingDiamond_CompletesWithCorrectInference()
        => AssertCompletesUnderWallClockGuard(() =>
        {
            var root = EmptyAlgorithm(BinaryDiamond(250, new Expr.Resolve("q")));

            var (detected, diagnostics) = ParameterDetector.Detect(root);

            Assert.Empty(diagnostics);
            Assert.Equal(["q"], detected.Params);
            AssertDiamondSharingPreserved(detected.Output[0], 250);
        });

    [Fact]
    public void Detector_DiamondAndDuplicatedTree_InferTheSameSignature()
    {
        const int depth = 6;
        var (dagDetected, dagDiagnostics) = ParameterDetector.Detect(
            EmptyAlgorithm(BinaryDiamond(depth, new Expr.Resolve("q"))));
        var (treeDetected, treeDiagnostics) = ParameterDetector.Detect(
            EmptyAlgorithm(BinaryTree(depth, () => new Expr.Resolve("q"))));

        Assert.Empty(dagDiagnostics);
        Assert.Empty(treeDiagnostics);
        Assert.Equal(treeDetected.Params, dagDetected.Params);
    }

    // ── 1b. Grace weights stay per semantic occurrence ──────────────────────

    private static IReadOnlyList<string> DetectParams(params Expr[] output)
    {
        var (detected, diagnostics) = ParameterDetector.Detect(EmptyAlgorithm(output));
        Assert.Empty(diagnostics);
        return detected.Params;
    }

    /// <summary>
    /// Grace weight is the ONE per-occurrence-additive fact of free-name collection, so it is
    /// the discriminating oracle for the memo's weight effects: a shared graced leaf under a
    /// depth-2 diamond has FOUR semantic occurrences (weight -4, enough to move the parameter
    /// left past two earlier names), where a per-distinct-node accounting would contribute -1
    /// (one move) and a per-edge accounting -2. The duplicated tree must agree exactly.
    /// </summary>
    [Fact]
    public void Detector_SharedGraceLeaf_AccumulatesWeightPerOccurrenceLikeTheDuplicatedTree()
    {
        const int depth = 2;
        var dagParams = DetectParams(
            new Expr.Resolve("a"),
            new Expr.Resolve("b"),
            BinaryDiamond(depth, new Expr.Grace(new Expr.Resolve("g"), -1)));
        var treeParams = DetectParams(
            new Expr.Resolve("a"),
            new Expr.Resolve("b"),
            BinaryTree(depth, () => new Expr.Grace(new Expr.Resolve("g"), -1)));

        Assert.Equal(["g", "a", "b"], dagParams);
        Assert.Equal(treeParams, dagParams);
    }

    /// <summary>
    /// Beyond any materializable tree (2^200 occurrences), the accumulated weight saturates
    /// deterministically instead of overflowing; ordering still reflects an extreme weight.
    /// </summary>
    [Fact]
    public Task Detector_AstronomicalGraceMultiplicity_SaturatesInsteadOfOverflowing()
        => AssertCompletesUnderWallClockGuard(() =>
        {
            var detectedParams = DetectParams(
                BinaryDiamond(200, new Expr.Grace(new Expr.Resolve("g"), 1)),
                new Expr.Resolve("a"));

            // Postfix weight moves g rightward past a; saturation keeps the walk finite and the
            // outcome deterministic.
            Assert.Equal(["a", "g"], detectedParams);
        });

    /// <summary>
    /// Saturating addition is ordered, not reducible to one net delta: (+Max, +Max, -Max)
    /// maps zero back to zero, while its arithmetic sum is +Max. Replaying a shared subtree's
    /// memo must therefore compose the same per-occurrence clamp operations as a cloned tree.
    /// </summary>
    [Fact]
    public void Detector_SharedMixedSaturatingGraceEffects_MatchDuplicatedTree()
    {
        static Expr WeightSequence()
            => new Expr.Capture(new OutputBundle(
            [
                new Expr.Grace(new Expr.Resolve("g"), int.MaxValue),
                new Expr.Grace(new Expr.Resolve("g"), int.MaxValue),
                new Expr.Grace(new Expr.Resolve("g"), -int.MaxValue),
            ]));

        var sharedSequence = WeightSequence();
        var dagParams = DetectParams(sharedSequence, sharedSequence, new Expr.Resolve("a"));
        var treeParams = DetectParams(WeightSequence(), WeightSequence(), new Expr.Resolve("a"));

        Assert.Equal(["g", "a"], dagParams);
        Assert.Equal(treeParams, dagParams);
    }

    /// <summary>
    /// The composable effect uses an arbitrary-precision offset, so the amount assembled from
    /// stacked wrappers on ONE host-built occurrence must not overflow an int before it reaches
    /// that effect. Positive and negative overflow would otherwise wrap to the opposite sign and
    /// reverse parameter movement.
    /// </summary>
    [Fact]
    public void Detector_StackedGraceWeights_DoNotOverflowBeforeSaturation()
    {
        var positive = DetectParams(
            new Expr.Grace(
                new Expr.Grace(new Expr.Resolve("g"), int.MaxValue),
                1),
            new Expr.Resolve("a"));
        var negative = DetectParams(
            new Expr.Resolve("a"),
            new Expr.Grace(
                new Expr.Grace(new Expr.Resolve("g"), int.MinValue),
                -1));

        Assert.Equal(["a", "g"], positive);
        Assert.Equal(["g", "a"], negative);
    }

    /// <summary>
    /// The diagnostic span search is memoized per searched name: a diamond inside an illegal
    /// conditional-branch body still reports the free identifier (with node-bounded search
    /// work), and the check-mode collection stays name-deduplicated.
    /// </summary>
    [Fact]
    public Task Detector_ConditionalBranchDiamond_ReportsTheFreeNameOnce()
        => AssertCompletesUnderWallClockGuard(() =>
        {
            var observations = new FrontEndTraversalObservations();
            var body = EmptyAlgorithm(BinaryDiamond(DeepDepth, new Expr.Resolve("zzFree")));
            var conditional = new Algorithm.Conditional(
                Parent: null,
                Opens: [],
                Branches: [new CondBranch(new Pattern.Bind("b"), body)]);
            var root = new Algorithm.User(
                null, [], [], [new Property("Cond", conditional)], OutputBundle.Empty);

            var (_, diagnostics) = ParameterDetector.DetectPrevalidated(root, null, observations);

            Assert.Single(diagnostics, d => d.Message.Contains("zzFree"));
            // The DeclaredNameCheck collection walk and the binder rewrite walk each expand the
            // diamond's interior once; the no-hit span search is bounded the same way (the leaf
            // itself is the hit, so at most every interior node expands once).
            Assert.Equal(DeepDepth, observations.DetectorCollectExpansions);
            Assert.Equal(DeepDepth, observations.DetectorRewriteExpansions);
            Assert.InRange(observations.DetectorSpanSearchExpansions, 1, DeepDepth);
        });

    [Fact]
    public void Detector_ConditionalBranchSharedBinderLeaf_RewritesOnceAndStaysShared()
    {
        var sharedBinder = new Expr.Resolve("b");
        var body = EmptyAlgorithm(new Expr.Binary(BinaryOp.Add, sharedBinder, sharedBinder));
        var conditional = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches: [new CondBranch(new Pattern.Bind("b"), body)]);
        var root = new Algorithm.User(
            null, [], [], [new Property("Cond", conditional)], OutputBundle.Empty);

        var (detected, diagnostics) = ParameterDetector.Detect(root);

        Assert.Empty(diagnostics);
        var detectedConditional = Assert.IsType<Algorithm.Conditional>(detected.Properties[0].Value);
        var rewritten = Assert.IsType<Expr.Binary>(detectedConditional.Branches[0].Body.Output[0]);
        Assert.Same(rewritten.Left, rewritten.Right);
        Assert.Equal("b", Assert.IsType<Expr.Param>(rewritten.Left).Name);
    }

    /// <summary>
    /// A conditional branch body has its own property-processing loop. Its non-conditional
    /// property values still share one constant branch scope/capture/diagnostic context, so
    /// two properties referencing ONE value algorithm must not re-expand it or turn it into
    /// two rewritten objects. Conditional values stay occurrence-specific because their
    /// diagnostics name the referencing property.
    /// </summary>
    [Fact]
    public Task Detector_ConditionalBranchSharedPropertyValue_ExpandsOnceAndStaysShared()
        => AssertCompletesUnderWallClockGuard(() =>
        {
            const int depth = DeepDepth;
            var observations = new FrontEndTraversalObservations();
            var sharedValue = EmptyAlgorithm(BinaryDiamond(depth, new Expr.Resolve("b")));
            var branchBody = new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties:
                [
                    new Property("First", sharedValue),
                    new Property("Second", sharedValue),
                ],
                Output: OutputBundle.Empty);
            var conditional = new Algorithm.Conditional(
                Parent: null,
                Opens: [],
                Branches: [new CondBranch(new Pattern.Bind("b"), branchBody)]);
            var root = new Algorithm.User(
                null, [], [], [new Property("Cond", conditional)], OutputBundle.Empty);

            var (detected, diagnostics) = ParameterDetector.DetectPrevalidated(
                root, null, observations);

            Assert.Empty(diagnostics);
            Assert.Equal(depth, observations.DetectorCollectExpansions);
            Assert.Equal(depth, observations.DetectorRewriteExpansions);
            var detectedConditional = Assert.IsType<Algorithm.Conditional>(detected.Properties[0].Value);
            var detectedBranchBody = Assert.IsType<Algorithm.User>(detectedConditional.Branches[0].Body);
            Assert.Same(detectedBranchBody.Properties[0].Value, detectedBranchBody.Properties[1].Value);
            var rewrittenLeaf = AssertDiamondSharingPreserved(
                detectedBranchBody.Properties[0].Value.Output[0], depth);
            Assert.Equal("b", Assert.IsType<Expr.Param>(rewrittenLeaf).Name);
        });

    /// <summary>
    /// A diagnostic-span search for `target` must prove the preceding shared diamond contains
    /// no such name without expanding its 2^depth paths. The first diagnostic searches for the
    /// diamond's own `other` name; the second is the discriminating no-hit traversal.
    /// </summary>
    [Fact]
    public Task Detector_ExplicitDiagnosticSpanSearch_IsBoundedAcrossSharedNoHitSubtree()
        => AssertCompletesUnderWallClockGuard(() =>
        {
            const int depth = DeepDepth;
            var parsed = SourceProvenance.ParseValid("F(x) = x").Root;
            var f = Assert.Single(parsed.Properties, p => p.Name == "F");
            var fValue = Assert.IsType<Algorithm.User>(f.Value) with
            {
                Output = new OutputBundle(
                [
                    BinaryDiamond(depth, new Expr.Resolve("other")),
                    new Expr.Resolve("target"),
                ]),
            };
            var root = parsed with { Properties = [f.WithValue(fValue)] };
            var observations = new FrontEndTraversalObservations();

            var (_, diagnostics) = ParameterDetector.DetectPrevalidated(root, null, observations);

            Assert.Equal(2, diagnostics.Count);
            Assert.Contains(diagnostics, d => d.Message.Contains("other"));
            Assert.Contains(diagnostics, d => d.Message.Contains("target"));
            Assert.Equal(2 * depth, observations.DetectorSpanSearchExpansions);
        });

    [Fact]
    public Task DetectorAndResolver_OpenDiamond_RewriteEachDistinctNodeOnceAndPreserveSharing()
        => AssertCompletesUnderWallClockGuard(() =>
        {
            const int depth = DeepDepth;
            var open = (Expr)new Expr.Num(1);
            for (var i = 0; i < depth; i++)
                open = new Expr.SequenceConstruct(open, open);
            var root = new Algorithm.User(null, [], [open], [], OutputBundle.Empty);

            var detectorObservations = new FrontEndTraversalObservations();
            var (detected, diagnostics) = ParameterDetector.DetectPrevalidated(
                root, null, detectorObservations);
            Assert.Empty(diagnostics);
            Assert.Equal(depth, detectorObservations.DetectorRewriteExpansions);

            var resolverObservations = new FrontEndTraversalObservations();
            var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, resolverObservations);
            Assert.Equal(depth, resolverObservations.ResolverRewriteExpansions);

            var current = Assert.Single(resolved.Opens);
            for (var i = 0; i < depth; i++)
            {
                var construct = Assert.IsType<Expr.SequenceConstruct>(current);
                Assert.Same(construct.Left, construct.Right);
                current = construct.Left;
            }
        });

    // ── 2. ImplicitArgumentResolver ─────────────────────────────────────────

    /// <summary>Elaborated helper scope: one param-bearing property for lifting probes.</summary>
    private static Algorithm.User LiftingHelpers()
        => (Algorithm.User)SourceProvenance.ParseValid("F(x) = x + 1").Root;

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public Task Resolver_DiamondOverLiftableReference_ExpandsEachDistinctNodeOnce(int depth)
        => AssertCompletesUnderWallClockGuard(() =>
        {
            var root = LiftingHelpers() with
            {
                Output = new OutputBundle([BinaryDiamond(depth, new Expr.Resolve("F"))]),
            };
            var (detected, detectorDiagnostics) = ParameterDetector.DetectPrevalidated(root);
            Assert.Empty(detectorDiagnostics);

            var observations = new FrontEndTraversalObservations();
            var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations);

            // Lifting semantics are unchanged: the bare reference became an explicit F(x) call
            // and x was lifted into the root signature.
            Assert.Contains("x", resolved.Params);
            var rewrittenLeaf = AssertDiamondSharingPreserved(resolved.Output[0], depth);
            var liftedCall = Assert.IsType<Expr.Call>(rewrittenLeaf);
            Assert.Equal("F", Assert.IsType<Expr.Resolve>(liftedCall.Function).Name);
            Assert.Equal("x", Assert.IsType<Expr.Param>(Assert.Single(liftedCall.Args)).Name);

            // The diamond's `depth` interior nodes expand once per walk. F's explicitly
            // parameterized body skips dependency collection entirely but its one Binary is
            // rewritten, so the rewrite counter carries exactly one extra expansion.
            Assert.Equal(depth, observations.ResolverCollectExpansions);
            Assert.Equal(depth + 1, observations.ResolverRewriteExpansions);
        });

    [Fact]
    public Task Resolver_WorkGrowsLinearlyWithDiamondDepth()
        => AssertCompletesUnderWallClockGuard(() =>
        {
            static FrontEndTraversalObservations Observe(int depth)
            {
                var root = LiftingHelpers() with
                {
                    Output = new OutputBundle([BinaryDiamond(depth, new Expr.Resolve("F"))]),
                };
                var (detected, _) = ParameterDetector.DetectPrevalidated(root);
                var observations = new FrontEndTraversalObservations();
                ImplicitArgumentResolver.ResolvePrevalidated(detected, observations);
                return observations;
            }

            var shallow = Observe(ShallowDepth);
            var deep = Observe(DeepDepth);

            Assert.Equal(DeepDepth - ShallowDepth, deep.ResolverCollectExpansions - shallow.ResolverCollectExpansions);
            Assert.Equal(DeepDepth - ShallowDepth, deep.ResolverRewriteExpansions - shallow.ResolverRewriteExpansions);
        });

    [Fact]
    public Task Resolver_NearCeilingDiamond_CompletesWithLiftingIntact()
        => AssertCompletesUnderWallClockGuard(() =>
        {
            var root = LiftingHelpers() with
            {
                Output = new OutputBundle([BinaryDiamond(248, new Expr.Resolve("F"))]),
            };
            var (detected, _) = ParameterDetector.DetectPrevalidated(root);

            var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected);

            Assert.Contains("x", resolved.Params);
            var leaf = AssertDiamondSharingPreserved(resolved.Output[0], 248);
            Assert.IsType<Expr.Call>(leaf);
        });

    /// <summary>
    /// Call position is a real memo-key dimension: one shared Resolve is a liftable value
    /// occurrence in the first row but an explicitly-called callee in the second row.
    /// </summary>
    [Fact]
    public void Resolver_SharedResolveInValueAndCallPositions_SplitsContextSensitiveRewrite()
    {
        var sharedF = new Expr.Resolve("F");
        var root = LiftingHelpers() with
        {
            Output = new OutputBundle(
            [
                new Expr.ListLiteral(new OutputBundle([sharedF])),
                new Expr.Call(sharedF, new OutputBundle([new Expr.Num(3)])),
            ]),
        };
        var (detected, diagnostics) = ParameterDetector.DetectPrevalidated(root);
        Assert.Empty(diagnostics);

        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected);

        Assert.Contains("x", resolved.Params);
        var liftedValue = Assert.IsType<Expr.Call>(
            Assert.IsType<Expr.ListLiteral>(resolved.Output[0]).Items[0]);
        Assert.Single(liftedValue.Args);
        var explicitCall = Assert.IsType<Expr.Call>(resolved.Output[1]);
        Assert.Equal("F", Assert.IsType<Expr.Resolve>(explicitCall.Function).Name);
        Assert.Single(explicitCall.Args);
    }

    /// <summary>
    /// Full front-end tree-vs-DAG oracle, judged by EVALUATION: with no free names the
    /// diamond of additions over F(3) computes 4 * 2^depth, identically for the shared DAG
    /// and its duplicated tree.
    /// </summary>
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void FrontEnd_DiamondAndDuplicatedTree_EvaluateIdentically(bool shared)
    {
        const int depth = 6;
        static Expr LiftedLeaf() => new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Num(3)]));
        var payload = shared
            ? BinaryDiamond(depth, LiftedLeaf())
            : BinaryTree(depth, LiftedLeaf);
        var root = LiftingHelpers() with { Output = new OutputBundle([payload]) };

        var (detected, diagnostics) = ParameterDetector.DetectPrevalidated(root);
        Assert.Empty(diagnostics);
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected);
        var exposed = PropertyExposureResolver.Resolve(resolved);

        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(exposed));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([(Decimal128)(4m * (1 << depth))], result.Value);
    }

    // ── 3. PropertyExposureResolver ─────────────────────────────────────────

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public Task Exposure_Diamond_ExpandsEachDistinctNodeOnce(int depth)
        => AssertCompletesUnderWallClockGuard(() =>
        {
            var observations = new FrontEndTraversalObservations();
            var root = EmptyAlgorithm(BinaryDiamond(depth, new Expr.Num(1)));

            var rewritten = PropertyExposureResolver.Resolve(root, observations);

            Assert.Equal(depth, observations.ExposureRewriteExpansions);
            AssertDiamondSharingPreserved(((Algorithm.User)rewritten).Output[0], depth);
        });

    /// <summary>
    /// Exposure classification is unchanged by sharing: ONE brace algorithm whose property
    /// captures an ancestor-owned parameter, referenced from two capture rows, is classified
    /// once (LocalOnlyCapturedAncestorParameters) and stays one shared rewritten object.
    /// </summary>
    [Fact]
    public void Exposure_SharedCapturingAlgorithm_ClassifiesOnceAndPreservesSharing()
    {
        // Parsed original: G(a) = ({ H = a ... }, 1). Re-wire G's body so the SAME brace
        // algorithm expression appears in TWO capture rows.
        var parsedRoot = SourceProvenance.ParseValid("G(a) = ({\nH = a\nH\n}, 1)").Root;
        var gProperty = Assert.Single(parsedRoot.Properties, p => p.Name == "G");
        var gValue = Assert.IsType<Algorithm.User>(gProperty.Value);
        var capture = Assert.IsType<Expr.Capture>(gValue.Output[0]);
        var sharedBrace = Assert.IsType<Expr.AlgorithmExpr>(capture.Body[0]);

        var rewiredG = gValue with
        {
            Output = new OutputBundle([new Expr.Capture(new OutputBundle([sharedBrace, sharedBrace]))]),
        };
        var rewiredRoot = parsedRoot with
        {
            Properties = [gProperty.WithValue(rewiredG)],
        };

        var rewritten = PropertyExposureResolver.Resolve(rewiredRoot);

        var rewrittenG = Assert.IsType<Algorithm.User>(
            Assert.Single(rewritten.Properties, p => p.Name == "G").Value);
        var rewrittenCapture = Assert.IsType<Expr.Capture>(rewrittenG.Output[0]);
        Assert.Same(rewrittenCapture.Body[0], rewrittenCapture.Body[1]);
        var rewrittenBrace = Assert.IsType<Expr.AlgorithmExpr>(rewrittenCapture.Body[0]);
        var hProperty = Assert.Single(rewrittenBrace.Algorithm.Properties, p => p.Name == "H");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, hProperty.Exposure);
    }

    [Fact]
    public void Exposure_SharedPropertyValueAlgorithm_IsClassifiedOnceAndStaysShared()
    {
        // TWO properties referencing ONE value algorithm (the shape module elaboration
        // produces when the same URL is loaded twice at one level).
        var sharedValue = EmptyAlgorithm(new Expr.Num(7));
        var root = new Algorithm.User(
            null,
            [],
            [],
            [new Property("M1", sharedValue), new Property("M2", sharedValue)],
            OutputBundle.Empty);

        var rewritten = PropertyExposureResolver.Resolve(root);

        Assert.Same(rewritten.Properties[0].Value, rewritten.Properties[1].Value);
        Assert.All(rewritten.Properties, p => Assert.Equal(PropertyExposure.Exported, p.Exposure));
    }

    // ── 4. PropertyDependencyGraphBuilder ───────────────────────────────────

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public Task DependencyGraph_Diamond_ExpandsEachDistinctNodeOnce(int depth)
        => AssertCompletesUnderWallClockGuard(() =>
        {
            var observations = new FrontEndTraversalObservations();
            var root = new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties:
                [
                    new Property("A", EmptyAlgorithm(BinaryDiamond(depth, new Expr.Resolve("B")))),
                    new Property("B", EmptyAlgorithm(new Expr.Num(1))),
                ],
                Output: OutputBundle.Empty);

            var orderGraph = PropertyDependencyGraphBuilder.BuildDependencyOrder(root, observations: observations);
            var summaryGraph = PropertyDependencyGraphBuilder.BuildSummaries(root, observations: observations);

            // The dependency SET is identical to the tree expansion's: one edge A -> B, neither
            // lost nor duplicated (indices are a set), regardless of the 2^depth paths.
            Assert.Equal([1], orderGraph[0].SiblingDependencyIndices);
            Assert.Equal([1], summaryGraph[0].SummarySiblingDependencyIndices);
            Assert.Empty(orderGraph[1].SiblingDependencyIndices);

            Assert.Equal(depth, observations.DependencySiblingExpansions);
            Assert.Equal(depth, observations.DependencySeedExpansions);
        });

    [Fact]
    public void DependencyGraph_DiamondAndDuplicatedTree_ProduceIdenticalNodes(
    )
    {
        const int depth = 6;
        static Algorithm.User TwoPropertyRoot(Expr referencing)
            => new(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties:
                [
                    new Property("A", EmptyAlgorithm(referencing)),
                    new Property("B", EmptyAlgorithm(new Expr.Num(1))),
                ],
                Output: OutputBundle.Empty);

        static Expr ReferencingLeaf()
            => new Expr.Binary(BinaryOp.Add, new Expr.Resolve("B"), new Expr.Param("p"));

        var dagRoot = TwoPropertyRoot(BinaryDiamond(depth, ReferencingLeaf()));
        var treeRoot = TwoPropertyRoot(BinaryTree(depth, ReferencingLeaf));

        var dagOrder = PropertyDependencyGraphBuilder.BuildDependencyOrder(dagRoot);
        var treeOrder = PropertyDependencyGraphBuilder.BuildDependencyOrder(treeRoot);
        Assert.Equal(treeOrder[0].SiblingDependencyIndices, dagOrder[0].SiblingDependencyIndices);

        var dag = PropertyDependencyGraphBuilder.BuildSummaries(dagRoot);
        var tree = PropertyDependencyGraphBuilder.BuildSummaries(treeRoot);
        Assert.Equal(tree[0].SummarySiblingDependencyIndices, dag[0].SummarySiblingDependencyIndices);
        Assert.Equal(tree[0].SummaryVisiblePropertyDependencyNames, dag[0].SummaryVisiblePropertyDependencyNames);
        Assert.Equal(tree[0].RequiredAncestorOwnedParameterNames, dag[0].RequiredAncestorOwnedParameterNames);
        // The captured name is reported straight from the walk: the summary channel takes
        // no ancestor-owned context at all (which is what makes empty-locals summaries
        // memoizable by node reference — see PropertyDependencyGraphBuilder.SummaryMemo).
        Assert.Equal(["p"], dag[0].RequiredAncestorOwnedParameterNames);
    }

    /// <summary>
    /// The same shared expression reached from TWO different property owners contributes to
    /// each owner's node independently (the memo is per Build region and per property walk,
    /// never global), so per-owner dependency context is preserved.
    /// </summary>
    [Fact]
    public void DependencyGraph_ExpressionSharedAcrossProperties_ContributesToEachOwner()
    {
        var sharedReference = new Expr.Binary(BinaryOp.Add, new Expr.Resolve("C"), new Expr.Num(1));
        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties:
            [
                new Property("A", EmptyAlgorithm(sharedReference)),
                new Property("B", EmptyAlgorithm(sharedReference)),
                new Property("C", EmptyAlgorithm(new Expr.Num(1))),
            ],
            Output: OutputBundle.Empty);

        var graph = PropertyDependencyGraphBuilder.BuildDependencyOrder(root);

        Assert.Equal([2], graph[0].SiblingDependencyIndices);
        Assert.Equal([2], graph[1].SiblingDependencyIndices);
    }

    /// <summary>
    /// Owner and transparent-bundle attribution are distinct memo contexts. The shared Unary
    /// below names A's local B property: its direct occurrence consumes B's local summary,
    /// while the occurrence inside a neutral call argument crosses a transparent bundle whose
    /// local-summary map is empty and therefore remains a visible dependency named B.
    /// </summary>
    [Fact]
    public void DependencyGraph_SharedExpressionAcrossOwnerAndTransparentContexts_KeepsBothAttributions()
    {
        var shared = new Expr.Unary(UnaryOp.Minus, new Expr.Resolve("B"));
        var aValue = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("B", EmptyAlgorithm(new Expr.Num(1)))],
            Output: new OutputBundle(
            [
                shared,
                new Expr.Call(new Expr.Resolve("Neutral"), new OutputBundle([shared])),
            ]));
        var root = new Algorithm.User(
            null, [], [], [new Property("A", aValue)], OutputBundle.Empty);

        var graph = PropertyDependencyGraphBuilder.BuildSummaries(root);

        Assert.Contains("B", graph[0].SummaryVisiblePropertyDependencyNames);
    }

    // ── 4b. M17: per-channel builder entries + resolution-scoped summary memo ──

    /// <summary>
    /// The implicit-argument resolver consumes ONLY the dependency/order channel. Nested
    /// property values give the summary channel real work IF it ran; a recursive output row
    /// gives the order channel an observable sibling expansion, proving the observer was
    /// live on the builder path.
    /// </summary>
    [Fact]
    public void Resolver_ConsumesOnlyTheDependencyOrderChannel()
    {
        var observations = new FrontEndTraversalObservations();
        var nested = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("Inner", EmptyAlgorithm(new Expr.Param("p")))],
            Output: new OutputBundle([new Expr.Resolve("Inner")]));
        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties:
            [
                new Property("A", nested),
                new Property("B", EmptyAlgorithm(
                    new Expr.Binary(BinaryOp.Add, new Expr.Resolve("A"), new Expr.Num(1)))),
            ],
            Output: new OutputBundle([new Expr.Resolve("B")]));

        ImplicitArgumentResolver.ResolvePrevalidated(root, observations);

        Assert.Equal(1, observations.DependencySiblingExpansions);
        // The summary channel never ran: no expression seed expanded, no algorithm summary
        // computed (M17 — the resolver reads only the topological property order).
        Assert.Equal(0, observations.DependencySeedExpansions);
        Assert.Equal(0, observations.DependencyAlgorithmSummaryComputations);
    }

    /// <summary>
    /// Depth+1 distinct nested algorithm values: value_1..value_depth each wrap the previous
    /// as their one property, and the innermost leaf captures the ancestor-owned name `p`.
    /// The root holds value_depth as property "Top".
    /// </summary>
    private static Algorithm.User NestedPropertyChainRoot(int depth)
    {
        var value = EmptyAlgorithm(new Expr.Param("p"));
        for (var level = 1; level <= depth; level++)
        {
            value = new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [new Property($"N{level}", value)],
                Output: new OutputBundle([new Expr.Resolve($"N{level}")]));
        }

        return new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("Top", value)],
            Output: OutputBundle.Empty);
    }

    /// <summary>
    /// ONE completed-summary computation per distinct algorithm value for the WHOLE exposure
    /// resolution — before M17 each level's subtree summary was recomputed at every ancestor
    /// level (O(depth^2) subtree work; the measured pre-change expression-seed counts grew
    /// ~4x per depth doubling). The count is exact, so a disabled or narrowed memo fails
    /// deterministically.
    /// </summary>
    [Theory]
    [InlineData(4)]
    [InlineData(16)]
    public void Exposure_NestedChain_ComputesEachDistinctAlgorithmSummaryOnce(int depth)
    {
        var observations = new FrontEndTraversalObservations();
        var root = NestedPropertyChainRoot(depth);

        var rewritten = PropertyExposureResolver.Resolve(root, observations);

        Assert.Equal(depth + 1, observations.DependencyAlgorithmSummaryComputations);

        // Classification is the ordinary recursive-capture result at every level.
        var rewrittenRoot = (Algorithm.User)rewritten;
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(rewrittenRoot.Properties).Exposure);
        var top = Assert.IsType<Algorithm.User>(Assert.Single(rewrittenRoot.Properties).Value);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(top.Properties).Exposure);
    }

    /// <summary>
    /// A descendant algorithm SHARED by two parents (the module-elaboration shape) is
    /// summarized once per resolution and classifies identically at every use.
    /// </summary>
    [Fact]
    public void Exposure_SharedDescendantAcrossParents_SummarizedOncePerResolution()
    {
        var observations = new FrontEndTraversalObservations();
        var sharedChild = EmptyAlgorithm(new Expr.Param("p"));
        var parentA = new Algorithm.User(
            null, [], [],
            [new Property("CA", sharedChild)],
            new OutputBundle([new Expr.Resolve("CA")]));
        var parentB = new Algorithm.User(
            null, [], [],
            [new Property("CB", sharedChild)],
            new OutputBundle([new Expr.Resolve("CB")]));
        var root = new Algorithm.User(
            null, [], [],
            [new Property("PA", parentA), new Property("PB", parentB)],
            OutputBundle.Empty);
        Assert.Same(parentA.Properties[0].Value, parentB.Properties[0].Value);

        var rewritten = (Algorithm.User)PropertyExposureResolver.Resolve(root, observations);

        // parentA, parentB, and the shared child: three distinct algorithms, the shared
        // child counted once.
        Assert.Equal(3, observations.DependencyAlgorithmSummaryComputations);
        Assert.All(rewritten.Properties, property => Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters, property.Exposure));
        var rewrittenParentA = Assert.IsType<Algorithm.User>(rewritten.Properties[0].Value);
        var rewrittenParentB = Assert.IsType<Algorithm.User>(rewritten.Properties[1].Value);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(rewrittenParentA.Properties).Exposure);
        Assert.Equal(
            PropertyExposure.LocalOnlyCapturedAncestorParameters,
            Assert.Single(rewrittenParentB.Properties).Exposure);
    }

    /// <summary>
    /// The completed-summary memo lives on ONE resolution: a second independent resolution
    /// of the same root performs its own first computations in full (no static or cross-run
    /// summary state).
    /// </summary>
    [Fact]
    public void Exposure_SummaryMemoIsPerResolution_ASecondResolutionRecountsInFull()
    {
        var root = NestedPropertyChainRoot(8);
        var first = new FrontEndTraversalObservations();
        var second = new FrontEndTraversalObservations();

        PropertyExposureResolver.Resolve(root, first);
        PropertyExposureResolver.Resolve(root, second);

        Assert.Equal(9, first.DependencyAlgorithmSummaryComputations);
        Assert.Equal(9, second.DependencyAlgorithmSummaryComputations);
    }

    /// <summary>
    /// Concurrent resolutions over the SAME immutable AST and over a distinct AST each own
    /// their completed-summary memo and observation counters. No locks or shared counter
    /// state are needed because all three memo lifetimes are resolution-local.
    /// </summary>
    [Fact]
    public async Task Exposure_SummaryMemoIsResolutionLocal_UnderConcurrentResolutions()
    {
        var sharedRoot = NestedPropertyChainRoot(8);
        var distinctRoot = NestedPropertyChainRoot(4);
        var first = new FrontEndTraversalObservations();
        var second = new FrontEndTraversalObservations();
        var distinct = new FrontEndTraversalObservations();

        await Task.WhenAll(
            Task.Run(() => PropertyExposureResolver.Resolve(sharedRoot, first)),
            Task.Run(() => PropertyExposureResolver.Resolve(sharedRoot, second)),
            Task.Run(() => PropertyExposureResolver.Resolve(distinctRoot, distinct)));

        Assert.Equal(9, first.DependencyAlgorithmSummaryComputations);
        Assert.Equal(9, second.DependencyAlgorithmSummaryComputations);
        Assert.Equal(5, distinct.DependencyAlgorithmSummaryComputations);
    }

    /// <summary>
    /// The completed-summary memo is keyed by node REFERENCE: two structurally equal but
    /// distinct algorithm objects summarize independently (a value/record-equality key would
    /// collapse them).
    /// </summary>
    [Fact]
    public void DependencyGraph_DistinctButEqualAlgorithms_SummarizeIndependently()
    {
        var observations = new FrontEndTraversalObservations();
        var original = EmptyAlgorithm(new Expr.Binary(BinaryOp.Add, new Expr.Param("p"), new Expr.Num(1)));
        var structuralTwin = original with { };
        Assert.NotSame(original, structuralTwin);
        Assert.Equal(original, structuralTwin);

        var root = new Algorithm.User(
            null, [], [],
            [new Property("A", original), new Property("B", structuralTwin)],
            OutputBundle.Empty);

        var graph = PropertyDependencyGraphBuilder.BuildSummaries(
            root, new PropertyDependencyGraphBuilder.SummaryMemo(), observations);

        Assert.Equal(2, observations.DependencyAlgorithmSummaryComputations);
        Assert.Equal(["p"], graph[0].RequiredAncestorOwnedParameterNames);
        Assert.Equal(["p"], graph[1].RequiredAncestorOwnedParameterNames);
    }

    /// <summary>
    /// Summary seeds are mutable accumulators, so no stored or shared seed instance may ever
    /// be handed out directly. Three aliasing routes are pinned: (1) L's row makes a LITERAL's
    /// empty seed the Binary accumulator and unions "x" into it — a shared empty-seed
    /// singleton would leak "x" into every later empty summary (M); (2) P1 unions "x" into
    /// the shared child algorithm's FIRST returned seed, proving the store-side pristine clone
    /// survives first-caller accumulation; (3) P2 unions "y" into a cache-HIT seed, and P3
    /// proves the stored seed itself did not escape from the hit side.
    /// </summary>
    [Fact]
    public void DependencyGraph_SharedChildSummary_IsNotPollutedByAnEarlierOwnersAccumulation()
    {
        var sharedChild = new Expr.AlgorithmExpr(EmptyAlgorithm(new Expr.Num(7)));
        var lValue = EmptyAlgorithm(new Expr.Binary(BinaryOp.Add, new Expr.Num(1), new Expr.Param("x")));
        var mValue = EmptyAlgorithm(new Expr.Num(2));
        var p1Value = EmptyAlgorithm(new Expr.Binary(BinaryOp.Add, sharedChild, new Expr.Param("x")));
        var p2Value = EmptyAlgorithm(new Expr.Binary(BinaryOp.Add, sharedChild, new Expr.Param("y")));
        var p3Value = EmptyAlgorithm(sharedChild);
        var root = new Algorithm.User(
            null, [], [],
            [
                new Property("L", lValue),
                new Property("M", mValue),
                new Property("P1", p1Value),
                new Property("P2", p2Value),
                new Property("P3", p3Value),
            ],
            OutputBundle.Empty);

        var graph = PropertyDependencyGraphBuilder.BuildSummaries(root);

        Assert.Equal(["x"], graph[0].RequiredAncestorOwnedParameterNames);
        Assert.Empty(graph[1].RequiredAncestorOwnedParameterNames);
        Assert.Equal(["x"], graph[2].RequiredAncestorOwnedParameterNames);
        Assert.Equal(["y"], graph[3].RequiredAncestorOwnedParameterNames);
        Assert.Empty(graph[4].RequiredAncestorOwnedParameterNames);
    }

    [Fact]
    public void DependencyGraph_SummarySeedClone_CopiesEveryMutableSetInBothDirections()
    {
        var original = new PropertyDependencyGraphBuilder.SummarySeed(["p"], ["Visible"]);
        var clone = original.Clone();

        original.RequiredAncestorOwnedParameterNames.Add("original-only");
        original.VisiblePropertyDependencyNames.Add("original-visible-only");
        clone.RequiredAncestorOwnedParameterNames.Add("clone-only");
        clone.VisiblePropertyDependencyNames.Add("clone-visible-only");

        Assert.Equal(["original-only", "p"], original.RequiredAncestorOwnedParameterNames.Order(StringComparer.Ordinal));
        Assert.Equal(["Visible", "original-visible-only"], original.VisiblePropertyDependencyNames.Order(StringComparer.Ordinal));
        Assert.Equal(["clone-only", "p"], clone.RequiredAncestorOwnedParameterNames.Order(StringComparer.Ordinal));
        Assert.Equal(["Visible", "clone-visible-only"], clone.VisiblePropertyDependencyNames.Order(StringComparer.Ordinal));
        Assert.Same(StringComparer.Ordinal, original.RequiredAncestorOwnedParameterNames.Comparer);
        Assert.Same(StringComparer.Ordinal, original.VisiblePropertyDependencyNames.Comparer);
        Assert.Same(StringComparer.Ordinal, clone.RequiredAncestorOwnedParameterNames.Comparer);
        Assert.Same(StringComparer.Ordinal, clone.VisiblePropertyDependencyNames.Comparer);
    }

    /// <summary>
    /// The topological property order stays deterministic after the channel split: ready
    /// properties leave in DECLARATION (index) order, a dependent follows its dependency,
    /// and a dependency cycle falls back to appending the cyclic members in index order.
    /// </summary>
    [Fact]
    public void DependencyOrder_TopologicalOrder_IsDeterministicWithDeclarationOrderTies()
    {
        var acyclic = new Algorithm.User(
            null, [], [],
            [
                new Property("A", EmptyAlgorithm(new Expr.Num(1))),
                new Property("B", EmptyAlgorithm(new Expr.Unary(UnaryOp.Minus, new Expr.Resolve("D")))),
                new Property("C", EmptyAlgorithm(new Expr.Num(2))),
                new Property("D", EmptyAlgorithm(new Expr.Num(3))),
            ],
            OutputBundle.Empty);
        Assert.Equal(
            [0, 2, 3, 1],
            PropertyDependencyGraphBuilder.BuildDependencyOrder(acyclic).TopologicalOrder);

        var cyclic = new Algorithm.User(
            null, [], [],
            [
                new Property("X", EmptyAlgorithm(new Expr.Unary(UnaryOp.Minus, new Expr.Resolve("Y")))),
                new Property("Y", EmptyAlgorithm(new Expr.Unary(UnaryOp.Minus, new Expr.Resolve("X")))),
            ],
            OutputBundle.Empty);
        Assert.Equal(
            [0, 1],
            PropertyDependencyGraphBuilder.BuildDependencyOrder(cyclic).TopologicalOrder);
    }

    /// <summary>
    /// ONE User body is both a conditional branch body (its binder `b` owns the body's free
    /// name) and an ordinary property value (nothing owns `b`). The branch-body summary is
    /// genuinely context-sensitive, so it must neither be admitted to nor served from the
    /// empty-locals completed-summary memo — in either processing order.
    /// </summary>
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void DependencyGraph_BranchBodySummaries_KeepBinderContextOutOfTheSharedMemo(bool conditionalFirst)
    {
        var sharedBody = EmptyAlgorithm(new Expr.Param("b"));
        var conditional = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches: [new CondBranch(new Pattern.Bind("b"), sharedBody)]);
        var condProperty = new Property("Cond", conditional);
        var plainProperty = new Property("Plain", sharedBody);
        var root = new Algorithm.User(
            null, [], [],
            conditionalFirst ? [condProperty, plainProperty] : [plainProperty, condProperty],
            OutputBundle.Empty);
        Assert.Same(sharedBody, conditional.Branches[0].Body);
        Assert.Same(sharedBody, plainProperty.Value);

        var graph = PropertyDependencyGraphBuilder.BuildSummaries(root);

        Assert.True(graph.TryGetPropertyIndex("Cond", out var condIndex));
        Assert.True(graph.TryGetPropertyIndex("Plain", out var plainIndex));
        // Under its branch binder the body owns `b`: no ancestor requirement.
        Assert.Empty(graph[condIndex].RequiredAncestorOwnedParameterNames);
        // As a plain property value (empty locals) the SAME node leaves `b` free.
        Assert.Equal(["b"], graph[plainIndex].RequiredAncestorOwnedParameterNames);
    }

    // ── 5. ModuleLoader ─────────────────────────────────────────────────────

    private static ModuleLoader CreateLoader(
        List<Diagnostic> diagnostics,
        FrontEndTraversalObservations? observations = null,
        Func<string, CancellationToken, ValueTask<string>>? downloader = null)
        => new(diagnostics, downloader ?? ((url, ct) => ValueTask.FromResult("public X = 1")))
        {
            TraversalObservations = observations,
        };

    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public Task Loader_SyncWalkDiamond_ExpandsEachDistinctNodeOnce(int depth)
        => AssertCompletesUnderWallClockGuard(async () =>
        {
            var observations = new FrontEndTraversalObservations();
            var diagnostics = new List<Diagnostic>();
            var loader = CreateLoader(diagnostics, observations);

            var elaborated = await loader.ElaborateAsync(EmptyAlgorithm(BinaryDiamond(depth, new Expr.Num(1))));

            Assert.Empty(diagnostics);
            // Rewrite walk: the root algorithm plus the `depth` interior nodes, each once.
            Assert.Equal(depth + 1, observations.LoaderWalkExpansions);
            // Marker pre-scan: root algorithm, `depth` interior nodes, and the leaf, each once.
            Assert.Equal(depth + 2, observations.LoaderMarkerExpansions);
            AssertDiamondSharingPreserved(elaborated.Output[0], depth);
        });

    [Fact]
    public Task Loader_NearCeilingDiamond_Completes()
        => AssertCompletesUnderWallClockGuard(async () =>
        {
            var diagnostics = new List<Diagnostic>();
            var loader = CreateLoader(diagnostics);

            var elaborated = await loader.ElaborateAsync(
                EmptyAlgorithm(BinaryDiamond(600, new Expr.Num(1))));

            Assert.Empty(diagnostics);
            AssertDiamondSharingPreserved(elaborated.Output[0], 600);
        });

    private static Expr LoadCall()
        => new Expr.Call(
            new Expr.Resolve("load"),
            new OutputBundle([new Expr.StringLiteral("https://katlang.org/module.kat")]));

    /// <summary>
    /// The whole diamond spine is load-bearing, so this exercises the ASYNC twin walk: it
    /// stays distinct-node-bounded, and the shared (illegally positioned) load node is
    /// diagnosed ONCE — at one constant context/depth a shared node is one load site, not one per path (2^depth today
    /// would mean 2^40 diagnostics before this fix ran out of time to emit them).
    /// </summary>
    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public Task Loader_AsyncWalkDiamondOverLoad_IsBoundedAndDiagnosesTheSharedNodeOnce(int depth)
        => AssertCompletesUnderWallClockGuard(async () =>
        {
            var observations = new FrontEndTraversalObservations();
            var diagnostics = new List<Diagnostic>();
            var loader = CreateLoader(diagnostics, observations);
            var root = new Algorithm.User(
                null,
                [],
                [],
                [new Property("Mod", EmptyAlgorithm(BinaryDiamond(depth, LoadCall())))],
                OutputBundle.Empty);

            await loader.ElaborateAsync(root);

            Assert.Single(diagnostics, d => d.Message.Contains("load not allowed in runtime expression"));
            // Async walk: root algorithm + Mod's value algorithm + `depth` interior nodes + the
            // shared load node, each once.
            Assert.Equal(depth + 3, observations.LoaderWalkExpansions);
            // Marker: root + Mod's value algorithm + `depth` interior nodes (the load call is
            // marked, not expanded), each once.
            Assert.Equal(depth + 2, observations.LoaderMarkerExpansions);
        });

    /// <summary>
    /// A capture diamond keeps the definition context, so the shared load node at the bottom
    /// is VALID: it is fetched, budget-charged, and spliced exactly once per node identity,
    /// while the loader's per-URL cache already guarantees one download. Two syntactically
    /// independent load nodes naming the same URL stay two splice sites (one download).
    /// </summary>
    [Fact]
    public async Task Loader_SharedLoadNode_IsOneLoadSite_WhileDistinctNodesStayDistinctSites()
    {
        var downloads = 0;
        Func<string, CancellationToken, ValueTask<string>> countingDownloader = (url, ct) =>
        {
            downloads++;
            return ValueTask.FromResult("public X = 1");
        };

        // Shared node under a capture diamond (context-inheriting positions).
        var sharedLoad = LoadCall();
        var captureDiamond = (Expr)sharedLoad;
        for (var i = 0; i < ShallowDepth; i++)
            captureDiamond = new Expr.Capture(new OutputBundle([captureDiamond, captureDiamond]));
        var sharedDiagnostics = new List<Diagnostic>();
        var sharedLoader = CreateLoader(sharedDiagnostics, downloader: countingDownloader);
        var sharedRoot = new Algorithm.User(
            null, [], [], [new Property("Mod", EmptyAlgorithm(captureDiamond))], OutputBundle.Empty);

        var elaborated = await sharedLoader.ElaborateAsync(sharedRoot);

        Assert.Empty(sharedDiagnostics);
        Assert.Equal(1, downloads);
        var modValue = Assert.Single(elaborated.Properties, p => p.Name == "Mod").Value;
        var rewrittenCapture = Assert.IsType<Expr.Capture>(((Algorithm.User)modValue).Output[0]);
        Assert.Same(rewrittenCapture.Body[0], rewrittenCapture.Body[1]);

        // Two DISTINCT load nodes with the same URL: still one download (URL cache), but two
        // independent splice sites producing two wrappers over the one cached module.
        downloads = 0;
        var distinctDiagnostics = new List<Diagnostic>();
        var distinctLoader = CreateLoader(distinctDiagnostics, downloader: countingDownloader);
        var distinctRoot = new Algorithm.User(
            null,
            [],
            [],
            [new Property("Mod", EmptyAlgorithm(new Expr.Capture(new OutputBundle([LoadCall(), LoadCall()]))))],
            OutputBundle.Empty);

        var distinctElaborated = await distinctLoader.ElaborateAsync(distinctRoot);

        Assert.Empty(distinctDiagnostics);
        Assert.Equal(1, downloads);
        var distinctValue = Assert.Single(distinctElaborated.Properties, p => p.Name == "Mod").Value;
        var distinctCapture = Assert.IsType<Expr.Capture>(((Algorithm.User)distinctValue).Output[0]);
        Assert.NotSame(distinctCapture.Body[0], distinctCapture.Body[1]);
        Assert.Same(
            Assert.IsType<Expr.AlgorithmExpr>(distinctCapture.Body[0]).Algorithm,
            Assert.IsType<Expr.AlgorithmExpr>(distinctCapture.Body[1]).Algorithm);
    }

    /// <summary>
    /// Live traversal depth is part of a load-bearing rewrite's context. The first occurrence
    /// below leaves too little parser stack budget for the downloaded module, while the SAME
    /// load node's later shallow occurrence is admissible. A context-only memo incorrectly
    /// reused the deep placeholder at the shallow site and prevented the valid retry.
    /// </summary>
    [Fact]
    public async Task Loader_SharedLoadNodeAtDifferentLiveDepths_DoesNotReuseDepthRejection()
    {
        var downloads = 0;
        Func<string, CancellationToken, ValueTask<string>> downloader = (url, ct) =>
        {
            downloads++;
            return ValueTask.FromResult($"public X = {new string('-', 250)}1");
        };

        var sharedLoad = LoadCall();
        var deepOccurrence = (Expr)sharedLoad;
        const int deepCaptureCount = 240;
        for (var i = 0; i < deepCaptureCount; i++)
            deepOccurrence = new Expr.Capture(new OutputBundle([deepOccurrence]));

        var diagnostics = new List<Diagnostic>();
        var loader = CreateLoader(diagnostics, downloader: downloader);
        var propertyValue = EmptyAlgorithm(deepOccurrence, sharedLoad);
        var root = new Algorithm.User(
            null, [], [], [new Property("Mod", propertyValue)], OutputBundle.Empty);

        var elaborated = await loader.ElaborateAsync(root);

        // The rejected deep parse is not cached; the shallow occurrence retries and succeeds.
        Assert.Equal(2, downloads);
        Assert.Single(diagnostics, d => d.Message.Contains("too deeply", StringComparison.OrdinalIgnoreCase));

        var rewrittenValue = Assert.IsType<Algorithm.User>(
            Assert.Single(elaborated.Properties, p => p.Name == "Mod").Value);
        var rewrittenDeep = rewrittenValue.Output[0];
        for (var i = 0; i < deepCaptureCount; i++)
            rewrittenDeep = Assert.IsType<Expr.Capture>(rewrittenDeep).Body[0];

        Assert.IsType<Expr.Num>(rewrittenDeep);
        Assert.IsType<Expr.AlgorithmExpr>(rewrittenValue.Output[1]);
        Assert.NotSame(rewrittenDeep, rewrittenValue.Output[1]);
    }

    /// <summary>
    /// Sync/async tree-vs-DAG parity: a shared capture DAG whose spine carries a load
    /// elaborates (through the async twins) to the same module content and diagnostics as the
    /// equivalent duplicated tree, with sharing preserved on the DAG side only.
    /// </summary>
    [Fact]
    public async Task Loader_SharedDagAndDuplicatedTree_ElaborateEquivalently()
    {
        const int depth = 4;
        static Expr CaptureTree(int levels, Func<Expr> leafFactory)
            => levels == 0
                ? leafFactory()
                : new Expr.Capture(new OutputBundle(
                    [CaptureTree(levels - 1, leafFactory), CaptureTree(levels - 1, leafFactory)]));

        var sharedLeaf = LoadCall();
        var dagPayload = (Expr)sharedLeaf;
        for (var i = 0; i < depth; i++)
            dagPayload = new Expr.Capture(new OutputBundle([dagPayload, dagPayload]));

        static async Task<(Algorithm Elaborated, List<Diagnostic> Diagnostics)> Elaborate(Expr payload)
        {
            var diagnostics = new List<Diagnostic>();
            var loader = CreateLoader(diagnostics);
            var root = new Algorithm.User(
                null, [], [], [new Property("Mod", EmptyAlgorithm(payload))], OutputBundle.Empty);
            return (await loader.ElaborateAsync(root), diagnostics);
        }

        var (dagElaborated, dagDiagnostics) = await Elaborate(dagPayload);
        var (treeElaborated, treeDiagnostics) = await Elaborate(CaptureTree(depth, LoadCall));

        Assert.Empty(dagDiagnostics);
        Assert.Empty(treeDiagnostics);

        // Both spliced the stub module everywhere; compare the flattened splice counts and
        // module identity through evaluation-free structural probes.
        static int CountSplices(Expr expr) => expr switch
        {
            Expr.Capture(var body) => body.Sum(CountSplices),
            Expr.AlgorithmExpr => 1,
            _ => 0,
        };

        var dagMod = (Algorithm.User)Assert.Single(dagElaborated.Properties, p => p.Name == "Mod").Value;
        var treeMod = (Algorithm.User)Assert.Single(treeElaborated.Properties, p => p.Name == "Mod").Value;
        // The DAG preserves sharing (1 distinct splice reached through 2^depth paths); the
        // tree keeps 2^depth independent splice sites. Both represent the same semantics.
        Assert.Equal(1 << depth, CountSplices(treeMod.Output[0]));
        var dagCapture = Assert.IsType<Expr.Capture>(dagMod.Output[0]);
        Assert.Same(dagCapture.Body[0], dagCapture.Body[1]);
    }

    [Fact]
    public Task LoadElaborationGuard_SharedLoadDiamond_CompletesAndReportsTheNodeOnce()
        => AssertCompletesUnderWallClockGuard(() =>
        {
            var root = EmptyAlgorithm(BinaryDiamond(DeepDepth, LoadCall()));

            var diagnostics = LoadElaborationGuard.CreateUnavailableDiagnostics(root);

            Assert.Single(diagnostics);
            Assert.Contains("module elaboration is unavailable", diagnostics[0].Message);
        });

    // ── 6. Module elaboration produces shared trees the pipeline now absorbs ─

    /// <summary>
    /// Loading the same URL twice splices ONE cached module algorithm under two properties —
    /// the elaborated tree is a DAG from ordinary parsed source. The detector's property-loop
    /// memo elaborates the shared module once and the whole run stays correct.
    /// </summary>
    [Fact]
    public async Task Pipeline_DoubleLoadOfOneModule_RunsCorrectlyOverTheSharedSplice()
    {
        var modules = new Dictionary<string, string>
        {
            ["https://katlang.org/lib.kat"] = "public Seven = 7",
        };
        var result = await KatLangEngine.RunAsync(
            """
            M1 = load('https://katlang.org/lib.kat')
            M2 = load('https://katlang.org/lib.kat')
            M1.Seven + M2.Seven
            """,
            new RunOptions { DownloadCode = (url, _) => ValueTask.FromResult(modules[url]) });

        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal([(Decimal128)14m], success.Atoms);
    }
}
