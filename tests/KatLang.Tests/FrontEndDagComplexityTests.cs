using System.Numerics;
using KatLang.Semantics;

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

    [Fact]
    public void RegionKeys_DistinguishNamesContainingTheirDelimiters()
    {
        Assert.NotEqual(
            FrontEndRegionKeys.NameSet(["x", "y"]),
            FrontEndRegionKeys.NameSet(["x\u0001y"]));
        Assert.NotEqual(
            FrontEndRegionKeys.ClosedBranchSpecification(
                new Pattern.SequenceValue([new Pattern.Bind("x"), new Pattern.Bind("y")])),
            FrontEndRegionKeys.ClosedBranchSpecification(new Pattern.Bind("x:0,y")));

        var body = EmptyAlgorithm(new Expr.Resolve("x"));
        var root = EmptyAlgorithm() with
        {
            Properties =
            [
                new Property("Pair", new Algorithm.Conditional(null, [],
                    [new CondBranch(new Pattern.SequenceValue([new Pattern.Bind("x"), new Pattern.Bind("y")]), body)])),
                new Property("Joined", new Algorithm.Conditional(null, [],
                    [new CondBranch(new Pattern.Bind("x\u0001y"), body)])),
            ],
        };

        var (detected, diagnostics) = ParameterDetector.Detect(root);

        Assert.IsType<Expr.Param>(detected.Properties[0].Value.Branches[0].Body.Output[0]);
        Assert.IsType<Expr.Resolve>(detected.Properties[1].Value.Branches[0].Body.Output[0]);
        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, Assert.Single(diagnostics).Code);
    }

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

    /// <summary>
    /// A load beneath a DIAMOND of nested clause families — at every level two families share
    /// ONE branch body, so the root-to-load paths double per level (B2c). Initial elaboration
    /// never descends into an alternative branch body: it expands the root and its output
    /// call, the outermost body and its output call, and the two families, defers both
    /// branches, and performs no download — whatever the depth.
    /// </summary>
    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public Task Loader_ClauseFamilyDiamondOverLoad_DefersAlternativesWithoutExpandingPaths(int depth)
        => AssertCompletesUnderWallClockGuard(async () =>
        {
            var downloads = 0;
            var observations = new FrontEndTraversalObservations();
            var diagnostics = new List<Diagnostic>();
            var loader = CreateLoader(diagnostics, observations, (url, ct) =>
            {
                downloads++;
                return ValueTask.FromResult("public X = 1");
            });

            var elaborated = await loader.ElaborateAsync(ClauseFamilyDiamond(depth, load: true));

            Assert.Empty(diagnostics);
            Assert.Equal(0, downloads);
            Assert.Equal(2, loader.DeferredRegionCount);
            Assert.Equal(6, observations.LoaderWalkExpansions);
            Assert.False(LoadElaborationGuard.TryFindFirstUnresolvedLoad(elaborated, out _));
        });

    /// <summary>
    /// The demand side of the same diamond: evaluating one path (<c>Mod.Left(0)</c>, whose
    /// every level again selects <c>Left(0)</c>) materializes exactly the regions on that
    /// path, one level at a time — each nested family is deferred again when its enclosing
    /// body is materialized — while every <c>Right</c> region, sharing the very same raw body,
    /// stays untouched, and the per-URL cache keeps the one download. The eager provisional
    /// elaboration of the two deferred placeholders is bounded as well (M4): each placeholder
    /// is one detector region whose nested shared bodies elaborate once per level, so the
    /// provisional work is linear in the depth — never the 2^depth paths — and the demand-time
    /// elaboration of every selected level is bounded the same way.
    /// </summary>
    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public Task Loader_ClauseFamilyDiamondOverLoad_MaterializesOnlyTheSelectedPath(int depth)
        => AssertCompletesUnderWallClockGuard(async () =>
        {
            var downloads = 0;
            var diagnostics = new List<Diagnostic>();
            var loader = CreateLoader(diagnostics, observations: null, (url, ct) =>
            {
                downloads++;
                return ValueTask.FromResult("public X = 1");
            });

            var elaborated = await loader.ElaborateAsync(ClauseFamilyDiamond(depth, load: true));
            Assert.Empty(diagnostics);
            var detectorObservations = new FrontEndTraversalObservations();
            var (detected, detectorDiagnostics) = ParameterDetector.DetectPrevalidated(elaborated, null, detectorObservations);
            Assert.Empty(detectorDiagnostics);
            // Left's and Right's placeholders are distinct clones of the shared body, so each
            // is its own provisional region over the same nested chain: two chains of `depth`
            // regions, not 2^depth.
            Assert.Equal(2 * depth, detectorObservations.DetectorBranchBodyRegionExpansions);
            var exposed = PropertyExposureResolver.Resolve(ImplicitArgumentResolver.Resolve(detected));
            DeferredModuleRegions.MarkRootRequiresAsyncEvaluation(exposed);
            var demandObservations = new FrontEndTraversalObservations();
            loader.TraversalObservations = demandObservations;

            var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(exposed));

            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
            Assert.Equal([1m], result.Value);
            Assert.Equal(1, downloads);
            Assert.Equal(depth * depth, demandObservations.DetectorBranchBodyRegionExpansions);
            Assert.Equal(depth, demandObservations.ResolverBranchBodyRegionExpansions);
            Assert.Equal(depth + 2, demandObservations.ExposureAlgorithmExpansions);
            Assert.Equal(4 * depth, demandObservations.LoaderWalkExpansions);
            Assert.Equal(depth * (depth - 1), demandObservations.DependencyBranchBodySummaryComputations);
            Console.WriteLine($"Demand depth={depth}: detector={demandObservations.DetectorBranchBodyRegionExpansions}, "
                + $"resolver={demandObservations.ResolverBranchBodyRegionExpansions}, exposure={demandObservations.ExposureAlgorithmExpansions}, "
                + $"loader={demandObservations.LoaderWalkExpansions}, summaries={demandObservations.DependencyBranchBodySummaryComputations}");
            var current = Assert.IsType<Algorithm.User>(Assert.Single(exposed.Properties, p => p.Name == "Mod").Value);
            for (var level = 0; level < depth; level++)
            {
                var left = Assert.IsType<Algorithm.Conditional>(Assert.Single(current.Properties, p => p.Name == "Left").Value);
                var right = Assert.IsType<Algorithm.Conditional>(Assert.Single(current.Properties, p => p.Name == "Right").Value);
                Assert.True(DeferredModuleRegions.TryGet(Assert.Single(left.Branches).Body, out var leftRegion));
                Assert.True(DeferredModuleRegions.TryGet(Assert.Single(right.Branches).Body, out var rightRegion));
                Assert.NotSame(leftRegion, rightRegion);
                Assert.Same(leftRegion!.RawBody, rightRegion!.RawBody);
                Assert.Equal(1, leftRegion.MaterializationAttempts);
                Assert.Equal(0, rightRegion.MaterializationAttempts);
                Assert.True(leftRegion.TryGetMaterialized(out var materialized));
                current = Assert.IsType<Algorithm.User>(materialized);
            }
            Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(current.Opens));
        });

    // ── 6. Shared conditional families (M4): once per distinct node and semantic region ──

    /// <summary>
    /// <c>Mod.Left(0)</c> over <paramref name="depth"/> levels of <c>Left</c>/<c>Right</c>
    /// families whose single branches share ONE body object per level — 2^depth root-to-leaf
    /// paths through depth + 2 distinct bodies. With <paramref name="load"/> the innermost
    /// body opens a module (the B2c shape); without it the diamond is load-free.
    /// </summary>
    private static Algorithm.User ClauseFamilyDiamond(int depth, bool load)
    {
        Algorithm body = load
            ? EmptyAlgorithm(new Expr.Resolve("X")) with { Opens = [LoadCall()] }
            : EmptyAlgorithm(new Expr.Num(1));
        for (var level = 0; level < depth; level++)
        {
            Algorithm.Conditional Family() => new(null, [], [new CondBranch(new Pattern.LitInt(0), body)]);
            body = EmptyAlgorithm(new Expr.Call(new Expr.Resolve("Left"), new OutputBundle([new Expr.Num(0)]))) with
            {
                Properties = [new Property("Left", Family()), new Property("Right", Family())],
            };
        }
        return new Algorithm.User(
            null,
            [],
            [],
            [new Property("Mod", body)],
            new OutputBundle([new Expr.DotCall(new Expr.Resolve("Mod"), "Left", new OutputBundle([new Expr.Num(0)]))]));
    }

    /// <summary>
    /// Asserts a rewritten family diamond kept its sharing at every level: the Left and Right
    /// families' branch bodies are ONE object, and returns the innermost body.
    /// </summary>
    private static Algorithm AssertFamilyDiamondSharingPreserved(Algorithm rewrittenRoot, int depth)
    {
        var current = Assert.IsType<Algorithm.User>(Assert.Single(rewrittenRoot.Properties, p => p.Name == "Mod").Value);
        for (var level = 0; level < depth; level++)
        {
            var left = Assert.IsType<Algorithm.Conditional>(Assert.Single(current.Properties, p => p.Name == "Left").Value);
            var right = Assert.IsType<Algorithm.Conditional>(Assert.Single(current.Properties, p => p.Name == "Right").Value);
            Assert.Same(Assert.Single(left.Branches).Body, Assert.Single(right.Branches).Body);
            current = Assert.IsType<Algorithm.User>(left.Branches[0].Body);
        }

        return current;
    }

    /// <summary>
    /// The three front-end passes over the load-free family diamond: every branch body is
    /// elaborated ONCE per semantic region — here one region per level, since Left and Right
    /// reach the shared body under the same parent scope, binder set, signature-map state, and
    /// visible summaries — so every counter is linear in the depth while the path count is
    /// 2^depth, and the rewritten trees keep the sharing at every level. Region counts are the
    /// primary signal; the expression counters show each region's own output row expanding
    /// once (plus the root's <c>Mod.Left(0)</c> and Mod's <c>Left(0)</c>).
    /// </summary>
    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public Task FrontEnd_ClauseFamilyDiamond_ElaboratesEachBranchBodyOncePerRegion(int depth)
        => AssertCompletesUnderWallClockGuard(() =>
        {
            var root = ClauseFamilyDiamond(depth, load: false);

            var detectorObservations = new FrontEndTraversalObservations();
            var (detected, detectorDiagnostics) = ParameterDetector.DetectPrevalidated(root, null, detectorObservations);
            Assert.Empty(detectorDiagnostics);
            Assert.Equal(depth, detectorObservations.DetectorBranchBodyRegionExpansions);
            Assert.Equal(depth + 1, detectorObservations.DetectorRewriteExpansions);
            Assert.Equal(depth + 1, detectorObservations.DetectorCollectExpansions);
            AssertFamilyDiamondSharingPreserved(detected, depth);

            var resolverObservations = new FrontEndTraversalObservations();
            var resolverDiagnostics = new List<Diagnostic>();
            var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, resolverObservations, resolverDiagnostics);
            Assert.Empty(resolverDiagnostics);
            Assert.Equal(depth, resolverObservations.ResolverBranchBodyRegionExpansions);
            Assert.Equal(depth + 1, resolverObservations.ResolverRewriteExpansions);
            AssertFamilyDiamondSharingPreserved(resolved, depth);

            var exposureObservations = new FrontEndTraversalObservations();
            var exposed = PropertyExposureResolver.Resolve(resolved, exposureObservations);
            // Root, Mod, and each shared body once.
            Assert.Equal(depth + 2, exposureObservations.ExposureAlgorithmExpansions);
            Assert.Equal(depth + 1, exposureObservations.ExposureRewriteExpansions);
            // Every family node once (two per level, memoized by node) plus Mod's body.
            Assert.Equal(2 * depth + 1, exposureObservations.DependencyAlgorithmSummaryComputations);
            // Every shared branch body once per binder set — one per level.
            Assert.Equal(depth, exposureObservations.DependencyBranchBodySummaryComputations);
            AssertFamilyDiamondSharingPreserved(exposed, depth);

            Assert.Equal([1m], Evaluator.RunFlat(new Expr.AlgorithmExpr(exposed)).Value);
        });

    /// <summary>
    /// A branch body shared by two families under ONE semantic region is rewritten once, yet
    /// each family still receives the closed-branch diagnostic worded with its own name (the
    /// family name is the only thing that distinguishes the two reports), while a diagnostic
    /// of a node NESTED inside the shared body — which names no family — is reported once for
    /// the region. None of that depends on which family is declared first.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Detector_SharedBranchBody_RewritesOnceAndReportsPerFamily_IndependentOfOrder(bool reversed)
    {
        // One raw branch body from real syntax: an inner explicit-parameter algorithm with an
        // undeclared name (a nested, family-independent diagnostic) and a free name in the
        // branch output (the family-worded closed-branch diagnostic).
        var parsed = Parser.ParseSyntax("F(0) = {\n    Inner(a) = zzInner\n    zzFree\n}\nF(1) = 0\nF(0)");
        Assert.False(parsed.HasErrors);
        var syntax = parsed.SyntaxRoot;
        var sharedBody = Assert.IsType<Algorithm.Conditional>(Assert.Single(syntax.Properties, p => p.Name == "F").Value).Branches[0].Body;
        Algorithm.Conditional Family() => new(null, [], [new CondBranch(new Pattern.LitInt(0), sharedBody)]);
        var left = new Property("Left", Family());
        var right = new Property("Right", Family());
        var root = new Algorithm.User(null, [], [], reversed ? [right, left] : [left, right], OutputBundle.Empty);
        var observations = new FrontEndTraversalObservations();

        var (detected, diagnostics) = ParameterDetector.DetectPrevalidated(root, null, observations);

        Assert.Equal(1, observations.DetectorBranchBodyRegionExpansions);
        var leftBody = Assert.IsType<Algorithm.Conditional>(Assert.Single(detected.Properties, p => p.Name == "Left").Value).Branches[0].Body;
        var rightBody = Assert.IsType<Algorithm.Conditional>(Assert.Single(detected.Properties, p => p.Name == "Right").Value).Branches[0].Body;
        Assert.Same(leftBody, rightBody);

        var messages = diagnostics.Select(d => d.Message).ToList();
        Assert.Equal(3, diagnostics.Count);
        Assert.All(diagnostics, d => Assert.Equal(DiagnosticCode.UndeclaredIdentifier, d.Code));
        Assert.Single(messages, m => m.Contains("'zzInner' is used in an explicitly parameterized algorithm", StringComparison.Ordinal));
        Assert.Single(messages, m => m.Contains("'zzFree' is used in conditional branch 'Left'", StringComparison.Ordinal));
        Assert.Single(messages, m => m.Contains("'zzFree' is used in conditional branch 'Right'", StringComparison.Ordinal));
        // Both family reports carry the free name's own span.
        var freeSpans = diagnostics.Where(d => d.Message.Contains("zzFree", StringComparison.Ordinal)).Select(d => d.Span).Distinct().ToList();
        Assert.Single(freeSpans);
    }

    /// <summary>
    /// The same raw body under two genuinely different regions is elaborated independently:
    /// a binder set that binds the body's free name versus one that does not, and a parent
    /// scope that declares the name versus one that does not. The memo must never serve one
    /// region's rewrite or diagnostics to the other.
    /// </summary>
    [Fact]
    public void Detector_SharedBranchBody_UnderDistinctRegions_ElaboratesIndependently()
    {
        var sharedBody = EmptyAlgorithm(new Expr.Resolve("x") { Span = new SourceSpan(1, 1, 1, 1) });
        var binds = new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.Bind("x"), sharedBody)]);
        var literal = new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.LitInt(0), sharedBody)]);
        var declaringBlock = new Algorithm.User(
            null, [], [],
            [new Property("x", EmptyAlgorithm(new Expr.Num(1))), new Property("Declared", literal)],
            OutputBundle.Empty);
        var root = new Algorithm.User(
            null, [], [],
            [new Property("Binds", binds), new Property("Free", literal), new Property("Block", declaringBlock)],
            OutputBundle.Empty);
        var observations = new FrontEndTraversalObservations();

        var (detected, diagnostics) = ParameterDetector.DetectPrevalidated(root, null, observations);

        // Three regions: (root scope, binder x), (root scope, no binders), (block scope, no binders).
        Assert.Equal(3, observations.DetectorBranchBodyRegionExpansions);
        var bindsBody = Assert.IsType<Algorithm.Conditional>(detected.Properties[0].Value).Branches[0].Body;
        var freeBody = Assert.IsType<Algorithm.Conditional>(detected.Properties[1].Value).Branches[0].Body;
        var declaredBody = Assert.IsType<Algorithm.Conditional>(
            Assert.IsType<Algorithm.User>(detected.Properties[2].Value).Properties[1].Value).Branches[0].Body;
        Assert.NotSame(bindsBody, freeBody);
        Assert.NotSame(freeBody, declaredBody);
        Assert.Equal("x", Assert.IsType<Expr.Param>(bindsBody.Output[0]).Name);
        Assert.IsType<Expr.Resolve>(freeBody.Output[0]);
        Assert.IsType<Expr.Resolve>(declaredBody.Output[0]);
        // Exactly the unbound, undeclared occurrence is reported — under its own family.
        var diagnostic = Assert.Single(diagnostics);
        Assert.Contains("'x' is used in conditional branch 'Free'", diagnostic.Message, StringComparison.Ordinal);
    }

    /// <summary>
    /// The resolver's region is the signature SNAPSHOT of a body's free names: when two
    /// families sharing one body genuinely observe different signatures for a name the body
    /// reads, the body is rewritten again under the new observation and only the family that
    /// saw the lifted signature reports the blocked forwarding — exactly what two separate
    /// bodies would do — while families reached under one observation share one rewrite.
    /// Within an ACYCLIC property graph every consumer is processed after the siblings it
    /// reads (complete dependency edges), so distinct observations arise only in a sibling
    /// CYCLE, where the order falls back to declaration order: here P and R reference each
    /// other, every family depends on P, and the fallback processes Before and Early (P still
    /// detected: no parameters), then P (lifting `x` from the bare `Math.Abs`), then Late.
    /// </summary>
    [Fact]
    public void Resolver_SharedBranchBody_SplitsOnObservedSignatures_AndSharesWithinOne()
    {
        // `Math.Abs(P)` is a proven strict-value position: the blocked forwarding is diagnosed
        // exactly when the visible signature of P carries the lifted `x`.
        var parsed = Parser.ParseSyntax("P = Math.Abs + R\nR = P + 1\nF(0) = Math.Abs(P)\nF(1) = 0\nF(0)");
        Assert.False(parsed.HasErrors);
        var syntax = parsed.SyntaxRoot;
        var sharedBody = Assert.IsType<Algorithm.Conditional>(Assert.Single(syntax.Properties, p => p.Name == "F").Value).Branches[0].Body;
        var p = Assert.Single(syntax.Properties, p => p.Name == "P");
        var r = Assert.Single(syntax.Properties, p => p.Name == "R");
        Algorithm.Conditional Family() => new(null, [], [new CondBranch(new Pattern.LitInt(0), sharedBody)]);
        var root = new Algorithm.User(
            null, [], [],
            [new Property("Before", Family()), new Property("Early", Family()), p, r, new Property("Late", Family())],
            OutputBundle.Empty);
        var (detected, detectorDiagnostics) = ParameterDetector.DetectPrevalidated(root);
        Assert.Empty(detectorDiagnostics);
        var observations = new FrontEndTraversalObservations();
        var diagnostics = new List<Diagnostic>();

        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations, diagnostics);

        Assert.Equal(2, observations.ResolverBranchBodyRegionExpansions);
        Algorithm BodyOf(string family)
            => Assert.IsType<Algorithm.Conditional>(Assert.Single(resolved.Properties, prop => prop.Name == family).Value).Branches[0].Body;
        Assert.Same(BodyOf("Before"), BodyOf("Early"));
        Assert.NotSame(BodyOf("Early"), BodyOf("Late"));
        var diagnostic = Assert.Single(diagnostics);
        Assert.Equal(DiagnosticCode.UndeclaredIdentifier, diagnostic.Code);
        Assert.Contains("conditional branch 'Late'", diagnostic.Message, StringComparison.Ordinal);
    }

    /// <summary>
    /// The resolver's family-worded diagnostic is replayed per family sharing one body under
    /// ONE map state: both families report the blocked forwarding in their own name, from one
    /// rewrite, in either declaration order.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Resolver_SharedBranchBody_ReplaysBlockedForwardingPerFamily_IndependentOfOrder(bool reversed)
    {
        // P's implicit `y` is detected directly, so every family sees P(y) whatever the loop order.
        var parsed = Parser.ParseSyntax("P = y + 1\nF(0) = Math.Abs(P)\nF(1) = 0\nF(0)");
        Assert.False(parsed.HasErrors);
        var syntax = parsed.SyntaxRoot;
        var sharedBody = Assert.IsType<Algorithm.Conditional>(Assert.Single(syntax.Properties, p => p.Name == "F").Value).Branches[0].Body;
        var p = Assert.Single(syntax.Properties, p => p.Name == "P");
        Algorithm.Conditional Family() => new(null, [], [new CondBranch(new Pattern.LitInt(0), sharedBody)]);
        var left = new Property("Left", Family());
        var right = new Property("Right", Family());
        var root = new Algorithm.User(null, [], [], reversed ? [p, right, left] : [p, left, right], OutputBundle.Empty);
        var (detected, _) = ParameterDetector.DetectPrevalidated(root);
        var observations = new FrontEndTraversalObservations();
        var diagnostics = new List<Diagnostic>();

        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations, diagnostics);

        Assert.Equal(1, observations.ResolverBranchBodyRegionExpansions);
        Assert.Same(
            Assert.IsType<Algorithm.Conditional>(Assert.Single(resolved.Properties, prop => prop.Name == "Left").Value).Branches[0].Body,
            Assert.IsType<Algorithm.Conditional>(Assert.Single(resolved.Properties, prop => prop.Name == "Right").Value).Branches[0].Body);
        Assert.Equal(2, diagnostics.Count);
        Assert.Single(diagnostics, d => d.Message.Contains("conditional branch 'Left'", StringComparison.Ordinal));
        Assert.Single(diagnostics, d => d.Message.Contains("conditional branch 'Right'", StringComparison.Ordinal));
        Assert.Single(diagnostics.Select(d => d.Span).Distinct());
    }

    /// <summary>
    /// Exposure classification of a shared branch body is computed once per region and the
    /// families keep ONE rewritten object; a body shared between a family and a plain property
    /// summarizes under both contexts (binder-owned versus empty locals) but is rewritten once.
    /// </summary>
    [Fact]
    public void Exposure_SharedBranchBody_ClassifiesOnceAndPreservesSharing()
    {
        var sharedBody = new Algorithm.User(
            null, [], [],
            [new Property("Captures", EmptyAlgorithm(new Expr.Param("b"))), new Property("Plain", EmptyAlgorithm(new Expr.Num(1)))],
            new OutputBundle([new Expr.Resolve("Plain")]));
        Algorithm.Conditional Family() => new(null, [], [new CondBranch(new Pattern.Bind("b"), sharedBody)]);
        var root = new Algorithm.User(
            null, [], [],
            [new Property("Left", Family()), new Property("Right", Family()), new Property("Value", sharedBody)],
            OutputBundle.Empty);
        var observations = new FrontEndTraversalObservations();

        var rewritten = PropertyExposureResolver.Resolve(root, observations);

        // Root, the shared body once (its two property values are leaves).
        Assert.Equal(4, observations.ExposureAlgorithmExpansions);
        Assert.Equal(1, observations.DependencyBranchBodySummaryComputations);
        var leftBody = Assert.IsType<Algorithm.Conditional>(rewritten.Properties[0].Value).Branches[0].Body;
        var rightBody = Assert.IsType<Algorithm.Conditional>(rewritten.Properties[1].Value).Branches[0].Body;
        Assert.Same(leftBody, rightBody);
        Assert.Same(leftBody, rewritten.Properties[2].Value);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, Assert.Single(leftBody.Properties, p => p.Name == "Captures").Exposure);
        Assert.Equal(PropertyExposure.Exported, Assert.Single(leftBody.Properties, p => p.Name == "Plain").Exposure);
    }

    // ── 7. Shared property VALUES in the resolver: once per free-name signature snapshot ──

    /// <summary>
    /// A property-value diamond: every level has two properties sharing ONE value algorithm,
    /// so the innermost value is reachable through 2^depth paths. Every value's output is a
    /// Binary, so each rewrite records exactly one resolver rewrite expansion.
    /// </summary>
    private static Algorithm.User PropertyValueDiamond(int depth, string leafName)
    {
        Algorithm value = EmptyAlgorithm(new Expr.Binary(BinaryOp.Add, new Expr.Resolve(leafName), new Expr.Num(0)));
        for (var level = 0; level < depth; level++)
        {
            var shared = value;
            value = EmptyAlgorithm(new Expr.Binary(BinaryOp.Add, new Expr.Resolve("P1"), new Expr.Num(0))) with
            {
                Properties = [new Property("P1", shared), new Property("P2", shared)],
            };
        }

        return (Algorithm.User)value;
    }

    /// <summary>
    /// Every value in the diamond reads only the signatures of its FREE names (here the
    /// root's <c>Leaf</c>; <c>P1</c> is its own property), so under one observation each value
    /// is rewritten once — the resolver's region is the signature snapshot of the value's free
    /// names, never the referencing property or the path — and the rewritten tree keeps the
    /// sharing at every level.
    /// </summary>
    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public Task Resolver_PropertyValueDiamond_RewritesEachValueOncePerRegion(int depth)
        => AssertCompletesUnderWallClockGuard(() =>
        {
            var root = new Algorithm.User(
                null, [], [],
                [new Property("Leaf", EmptyAlgorithm(new Expr.Num(1))), new Property("Mod", PropertyValueDiamond(depth, "Leaf"))],
                new OutputBundle([new Expr.Resolve("Mod")]));
            var (detected, detectorDiagnostics) = ParameterDetector.DetectPrevalidated(root);
            Assert.Empty(detectorDiagnostics);
            var observations = new FrontEndTraversalObservations();

            var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations, new List<Diagnostic>());

            // Leaf's value and the depth + 1 diamond values, each once.
            Assert.Equal(depth + 2, observations.ResolverAlgorithmRegionExpansions);
            Assert.Equal(depth + 1, observations.ResolverRewriteExpansions);
            var current = Assert.IsType<Algorithm.User>(Assert.Single(resolved.Properties, p => p.Name == "Mod").Value);
            for (var level = 0; level < depth; level++)
            {
                Assert.Same(current.Properties[0].Value, current.Properties[1].Value);
                current = Assert.IsType<Algorithm.User>(current.Properties[0].Value);
            }
        });

    /// <summary>
    /// The same diamond under two blocks whose <c>Leaf</c> differs — a plain constant versus a
    /// value lifting an implicit <c>y</c> — is two genuinely different observations per
    /// level: the values are rewritten independently (the lifted <c>y</c> propagates up the
    /// whole chain under the lifting block only), each still once per observation, never once
    /// per path.
    /// </summary>
    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public Task Resolver_PropertyValueDiamond_UnderDistinctObservations_RewritesIndependentlyOncePerRegion(int depth)
        => AssertCompletesUnderWallClockGuard(() =>
        {
            var diamond = PropertyValueDiamond(depth, "Leaf");
            Algorithm.User Block(Algorithm leaf)
                => new(null, [], [], [new Property("Leaf", leaf), new Property("Mod", diamond)], new OutputBundle([new Expr.Resolve("Mod")]));
            var root = new Algorithm.User(
                null, [], [],
                [
                    new Property("Plain", Block(EmptyAlgorithm(new Expr.Num(1)))),
                    new Property("Lifting", Block(EmptyAlgorithm(new Expr.Binary(BinaryOp.Add, new Expr.Resolve("y"), new Expr.Num(1))))),
                ],
                OutputBundle.Empty);
            var (detected, _) = ParameterDetector.DetectPrevalidated(root);
            var observations = new FrontEndTraversalObservations();

            var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations, new List<Diagnostic>());

            // Two blocks, two leaf values, and the depth + 1 diamond values once per observation.
            Assert.Equal(2 * (depth + 1) + 4, observations.ResolverAlgorithmRegionExpansions);
            var plain = Assert.IsType<Algorithm.User>(Assert.Single(Assert.IsType<Algorithm.User>(resolved.Properties[0].Value).Properties, p => p.Name == "Mod").Value);
            var lifting = Assert.IsType<Algorithm.User>(Assert.Single(Assert.IsType<Algorithm.User>(resolved.Properties[1].Value).Properties, p => p.Name == "Mod").Value);
            Assert.NotSame(plain, lifting);
            Assert.Empty(plain.Params);
            Assert.Equal(["y"], lifting.Params);
        });

    /// <summary>
    /// The processing-order channel sees every value-position sibling reference in a property's
    /// whole value subtree: nested property values and conditional branch bodies contribute
    /// edges, a nested body's own property shadows the same-named sibling, a neutral call
    /// argument lifts nothing, and a block literal inside such an argument is a body of its
    /// own. Complete edges are what make sibling declaration order unobservable.
    /// </summary>
    [Fact]
    public void DependencyOrder_SeesNestedBodiesAndBranchBodies_UnderShadowingAndTransparency()
    {
        Expr B() => new Expr.Resolve("B");
        var root = new Algorithm.User(
            null, [], [],
            [
                // A = { Inner = B + 1  Inner }
                new Property("A", EmptyAlgorithm(new Expr.Resolve("Inner")) with
                {
                    Properties = [new Property("Inner", EmptyAlgorithm(new Expr.Binary(BinaryOp.Add, B(), new Expr.Num(1))))],
                }),
                // F(0) = B
                new Property("F", new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.LitInt(0), EmptyAlgorithm(B()))])),
                // C = { B = 1  B + 1 }: the nested B shadows the sibling.
                new Property("C", EmptyAlgorithm(new Expr.Binary(BinaryOp.Add, B(), new Expr.Num(1))) with
                {
                    Properties = [new Property("B", EmptyAlgorithm(new Expr.Num(1)))],
                }),
                // D = Apply(B): a neutral argument is transparent.
                new Property("D", EmptyAlgorithm(new Expr.Call(new Expr.Resolve("Apply"), new OutputBundle([B()])))),
                // E = Apply({ B }): the block literal inside the argument is a body of its own.
                new Property("E", EmptyAlgorithm(new Expr.Call(new Expr.Resolve("Apply"), new OutputBundle([new Expr.AlgorithmExpr(EmptyAlgorithm(B()))])))),
                new Property("B", EmptyAlgorithm(new Expr.Num(5))),
            ],
            OutputBundle.Empty);

        var order = PropertyDependencyGraphBuilder.BuildDependencyOrder(root);

        Assert.True(order.TryGetPropertyIndex("B", out var b));
        Assert.Equal([b], order[0].SiblingDependencyIndices);
        Assert.Equal([b], order[1].SiblingDependencyIndices);
        Assert.Empty(order[2].SiblingDependencyIndices);
        Assert.Empty(order[3].SiblingDependencyIndices);
        Assert.Equal([b], order[4].SiblingDependencyIndices);
        // B is processed before every consumer, whatever the declaration order.
        var topological = order.TopologicalOrder.ToList();
        Assert.True(topological.IndexOf(b) < topological.IndexOf(0));
        Assert.True(topological.IndexOf(b) < topological.IndexOf(1));
        Assert.True(topological.IndexOf(b) < topological.IndexOf(4));
    }

    /// <summary>
    /// Sibling declaration order is not observable: two programs that differ only in the order
    /// of their sibling declarations — a family and the sibling it reads at the root, a
    /// sibling that itself depends on another, a nested block reading a sibling, and families
    /// on both sides of a sibling inside a block — report the same diagnostics and produce the
    /// same outcome, because every consumer is processed after the siblings it reads.
    /// </summary>
    [Theory]
    [InlineData("P = Math.Abs\nF(0) = Math.Abs(P)\nF(1) = 0\nF(0)", "F(0) = Math.Abs(P)\nF(1) = 0\nP = Math.Abs\nF(0)")]
    [InlineData("P = Q + 1\nQ = y * 2\nF(0) = Math.Abs(P)\nF(1) = 0\nF(0)", "F(0) = Math.Abs(P)\nF(1) = 0\nQ = y * 2\nP = Q + 1\nF(0)")]
    [InlineData("P = Math.Abs\nA = {\n    Inner = Math.Abs(P)\n    Inner\n}\nA", "A = {\n    Inner = Math.Abs(P)\n    Inner\n}\nP = Math.Abs\nA")]
    [InlineData(
        "Q = y * 2\nBlock = {\n    Before(0) = Math.Abs(P)\n    Before(1) = 0\n    P = Q + 1\n    Late(0) = Math.Abs(P)\n    Late(1) = 0\n    Before(0) + Late(0)\n}\nBlock",
        "Q = y * 2\nBlock = {\n    Late(0) = Math.Abs(P)\n    Late(1) = 0\n    P = Q + 1\n    Before(0) = Math.Abs(P)\n    Before(1) = 0\n    Before(0) + Late(0)\n}\nBlock")]
    public void FrontEnd_SiblingDeclarationOrder_DoesNotChangeDiagnosticsOrOutcome(string source, string reordered)
    {
        static IReadOnlyList<string> Diagnostics(string program)
            => Parser.Parse(program).Diagnostics
                .Select(d => d.Code + ": " + d.Message)
                .OrderBy(text => text, StringComparer.Ordinal)
                .ToList();

        static string Outcome(string program)
            => KatLangEngine.Run(program) switch
            {
                RunResult.Success success => "success " + success.ToDisplayString(),
                RunResult.ParseFailure failure => "parse " + string.Join(",", failure.Errors.Select(e => e.Code).OrderBy(c => c)),
                RunResult.EvalFailure failure => "eval " + string.Join(",", failure.Errors.Select(e => e.Code).OrderBy(c => c)),
                var other => other.GetType().Name,
            };

        Assert.Equal(Diagnostics(source), Diagnostics(reordered));
        Assert.Equal(Outcome(source), Outcome(reordered));
    }

    // ── 8. SemanticModelBuilder: one analysis per (node, scope frame) ────────

    /// <summary>
    /// An expression diamond in one body is one scope frame: every node is analyzed once and
    /// the shared leaf is one identifier occurrence, not 2^depth of them.
    /// </summary>
    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public Task SemanticModel_ExpressionDiamond_AnalyzesEachNodeOncePerFrame(int depth)
        => AssertCompletesUnderWallClockGuard(() =>
        {
            var leaf = new Expr.Resolve("Leaf") { Span = new SourceSpan(2, 1, 2, 4) };
            var root = new Algorithm.User(
                null, [], [],
                [new Property("Leaf", EmptyAlgorithm(new Expr.Num(1)))],
                new OutputBundle([BinaryDiamond(depth, leaf)]));
            var (detected, _) = ParameterDetector.Detect(root);
            var observations = new FrontEndTraversalObservations();

            var model = SemanticModelBuilder.Build(detected, observations);

            // Leaf's own `1`, then the diamond's depth interior nodes and its one leaf.
            Assert.Equal(depth + 2, observations.SemanticModelExpressionVisits);
            var occurrence = Assert.Single(model.IdentifierOccurrences);
            Assert.Equal("Leaf", occurrence.Name);
            Assert.Equal(
                IdentifierClassification.PropertyReference,
                Assert.Single(model.FindResolutions("Leaf"), r => r.Occurrence.Kind == OccurrenceKind.ResolveReference).Classification);
        });

    /// <summary>
    /// A shared property-value diamond: the same value under two properties of one body is
    /// one occurrence, so the builder analyzes every distinct algorithm once — root, the leaf
    /// value, and the depth + 1 diamond values.
    /// </summary>
    [Theory]
    [InlineData(ShallowDepth)]
    [InlineData(DeepDepth)]
    public Task SemanticModel_PropertyValueDiamond_AnalyzesEachAlgorithmOncePerFrame(int depth)
        => AssertCompletesUnderWallClockGuard(() =>
        {
            var root = new Algorithm.User(
                null, [], [],
                [new Property("Leaf", EmptyAlgorithm(new Expr.Num(1))), new Property("Mod", PropertyValueDiamond(depth, "Leaf"))],
                new OutputBundle([new Expr.Resolve("Mod")]));
            var (detected, _) = ParameterDetector.Detect(root);
            var observations = new FrontEndTraversalObservations();

            SemanticModelBuilder.Build(detected, observations);

            Assert.Equal(depth + 3, observations.SemanticModelAlgorithmVisits);
        });

    /// <summary>
    /// The semantic model stays OCCURRENCE-oriented where contexts genuinely differ: one body
    /// under two families whose patterns declare their own <c>x</c>, and as a plain property
    /// value, is three analyses — the binder references resolve to their own family's
    /// declaration, and the plain value's <c>x</c> is unbound — each analyzed once.
    /// </summary>
    [Fact]
    public void SemanticModel_SharedBody_UnderDistinctBinderTables_IsAnalyzedPerFamily()
    {
        var body = EmptyAlgorithm(new Expr.Param("x") { Span = new SourceSpan(9, 1, 9, 1) });
        Algorithm.Conditional Family(int line)
            => new(null, [], [new CondBranch(new Pattern.Bind("x") { NameSpan = new SourceSpan(line, 1, line, 1) }, body)]);
        var root = new Algorithm.User(
            null, [], [],
            [new Property("Left", Family(1)), new Property("Right", Family(2)), new Property("Value", body)],
            OutputBundle.Empty);
        var observations = new FrontEndTraversalObservations();

        var model = SemanticModelBuilder.Build(root, observations);

        // Root, two families, the body under each family's binder table, and as a plain value.
        Assert.Equal(6, observations.SemanticModelAlgorithmVisits);
        var references = model.FindResolutions("x").Where(r => r.Occurrence.Kind == OccurrenceKind.ParameterReference).ToList();
        Assert.Equal(3, references.Count);
        Assert.Contains(references, r => r.Classification == IdentifierClassification.ConditionalBinderReference && r.ResolvedDeclaration?.Span.StartLineNumber == 1);
        Assert.Contains(references, r => r.Classification == IdentifierClassification.ConditionalBinderReference && r.ResolvedDeclaration?.Span.StartLineNumber == 2);
        Assert.Contains(references, r => r.Classification == IdentifierClassification.Unresolved);
    }

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
