namespace KatLang.Tests;

/// <summary>
/// FE-1: a scope that sees W names and contains K nested scopes, properties, or branches must cost
/// O(K + W) semantic-context work, never O(K × W). Every front-end context is built ONCE and then
/// EXTENDED by what a nested scope adds — persistent maps share the inherited entries, canonical name
/// sets (<see cref="NameSetInterner"/>) extend a context's content identity by the names added, and a
/// wide owner's parameter names are materialized once per resolution, and a promotion only captures
/// its near-miss suggestion context — so these pins count the W-sized work itself
/// (<see cref="FrontEndTraversalObservations.ContextEntriesWritten"/>,
/// <see cref="FrontEndTraversalObservations.ContextNamesCanonicalized"/>,
/// <see cref="FrontEndTraversalObservations.OwnerParameterNamesMaterialized"/>,
/// <see cref="FrontEndTraversalObservations.SummaryQualificationProbes"/>,
/// <see cref="FrontEndTraversalObservations.NameSetOperationSteps"/>,
/// <see cref="FrontEndTraversalObservations.SuggestionCandidatesExamined"/>), exactly, at two sizes.
/// A regression that copies, re-sorts, or re-materializes the wide context per child multiplies
/// them by K. The derivation diamonds pin the other half: region identity stays CONTENT-canonical,
/// so equal contexts reached through different extension orders share one region instead of
/// splitting per derivation path (which is exponential in the diamond depth). A design-independent
/// allocation guard backs the counters: it holds whatever a regression counts or fails to count.
/// </summary>
public class WideSemanticContextComplexityTests
{
    private static string Names(string prefix, int count)
        => string.Join(", ", Enumerable.Range(0, count).Select(i => $"{prefix}{i}"));

    private static Algorithm.User Syntax(string source) => SourceProvenance.ParseSyntaxValidRoot(source);

    private static Algorithm Detect(Algorithm root)
    {
        var (detected, diagnostics) = ParameterDetector.DetectPrevalidated(root);
        Assert.Empty(diagnostics);
        return detected;
    }

    private static Algorithm Resolve(Algorithm detected)
    {
        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations: null, diagnostics);
        Assert.Empty(diagnostics);
        return resolved;
    }

    private static Algorithm.User User(IReadOnlyList<ParameterPattern> parameters, IReadOnlyList<Property> properties, params Expr[] output)
        => new(null, parameters, [], properties, new OutputBundle(output));

    private static ParameterPattern[] Captures(string prefix, int count)
        => Enumerable.Range(0, count).Select(i => (ParameterPattern)new CaptureParameterPattern($"{prefix}{i}")).ToArray();

    // ── Resolver: the visible signature map ──────────────────────────────────

    /// <summary>
    /// K root properties whose values are blocks declaring a local property: the root extends the
    /// empty map by its K signatures and records each processed one; each block extends the root's
    /// map by its ONE local and records it — 4K entries. Copying the K-entry parent map per block
    /// (the former <c>new Dictionary(parentParamMap)</c>) wrote K per block.
    /// </summary>
    [Theory]
    [InlineData(300)]
    [InlineData(600)]
    public void Resolver_BlocksUnderAWideSiblingScope_ExtendTheSignatureMapByTheirOwnLocals(int blocks)
    {
        var source = string.Concat(Enumerable.Range(0, blocks).Select(i => $"P{i} = {{a = 1\n1}}\n")) + "1";
        var detected = Detect(Syntax(source));
        var observations = new FrontEndTraversalObservations();
        var diagnostics = new DiagnosticBag();

        _ = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations, diagnostics);

        Assert.Empty(diagnostics);
        Assert.Equal(4 * blocks, observations.ContextEntriesWritten);
    }

    /// <summary>
    /// W root properties and K clause families whose second branch owns an unresolved load (a
    /// DEFERRED region): each deferred branch keeps an O(1) snapshot of the visible map. The root
    /// extends the empty map by its W + K signatures and records its W processed plain values —
    /// 2W + K entries; a copying snapshot wrote W + K per deferred branch (and kept every copy alive
    /// in the tree).
    /// </summary>
    [Theory]
    [InlineData(300, 200)]
    [InlineData(600, 400)]
    public async Task Resolver_DeferredBranchesUnderAWideScope_SnapshotTheSignatureMapWithoutCopying(int width, int families)
    {
        var source = string.Concat(Enumerable.Range(0, width).Select(i => $"P{i} = 1\n"))
            + string.Concat(Enumerable.Range(0, families).Select(i =>
                $"B{i}(0) = 0\nB{i}(k) = {{\nm = load('https://katlang.org/m')\nm.V + k\n}}\n"))
            + "1";
        var loaderDiagnostics = new DiagnosticBag();
        var loader = new ModuleLoader(loaderDiagnostics, (url, ct) => ValueTask.FromResult("public V = 1"));
        var elaborated = await loader.ElaborateAsync(Syntax(source));
        Assert.Empty(loaderDiagnostics);
        Assert.Equal(families, loader.DeferredRegionCount);
        var detected = Detect(elaborated);
        var observations = new FrontEndTraversalObservations();
        var diagnostics = new DiagnosticBag();

        _ = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations, diagnostics);

        Assert.Empty(diagnostics);
        Assert.Equal(2 * width + families, observations.ContextEntriesWritten);
    }

    // ── Detector: parameter ownership and branch-body region keys ────────────

    /// <summary>
    /// An owner of W written parameters with K output blocks, each inferring one parameter: the
    /// owner writes its W bindings once and each block writes its ONE — W + K entries. Copying the
    /// inherited ownership map per block wrote W per block.
    /// </summary>
    [Theory]
    [InlineData(400, 300)]
    [InlineData(800, 600)]
    public void Detector_BlocksUnderAWideOwner_ExtendOwnershipByTheirOwnParameters(int width, int blocks)
    {
        var source = $"F({Names("v", width)}) = v0" + string.Concat(Enumerable.Repeat(", {a + 1}", blocks)) + "\n1";
        var observations = new FrontEndTraversalObservations();

        var (_, diagnostics) = ParameterDetector.DetectPrevalidated(Syntax(source), null, observations);

        Assert.Empty(diagnostics);
        Assert.Equal(width + blocks, observations.ContextEntriesWritten);
    }

    /// <summary>
    /// K clause families declared in an owner of W parameters: every branch body's region key
    /// carries the captured names' CONTENT identity, canonicalized once for the one ownership map
    /// they share — W names in all. Sorting and joining the W captured names per branch body cost
    /// K × W.
    /// </summary>
    [Theory]
    [InlineData(400, 300)]
    [InlineData(800, 600)]
    public void Detector_BranchBodiesUnderAWideOwner_CanonicalizeTheCapturedNamesOnce(int width, int families)
    {
        var source = $"F({Names("v", width)}) = {{\n"
            + string.Concat(Enumerable.Range(0, families).Select(i => $"B{i}(0) = 1\n"))
            + "v0\n}\n1";
        var observations = new FrontEndTraversalObservations();

        var (_, diagnostics) = ParameterDetector.DetectPrevalidated(Syntax(source), null, observations);

        Assert.Empty(diagnostics);
        Assert.Equal(families, observations.DetectorBranchBodyRegionExpansions);
        Assert.Equal(width, observations.ContextNamesCanonicalized);
    }

    // ── Detector: near-miss suggestion contexts ──────────────────────────────

    private static (FrontEndTraversalObservations Observations, Algorithm Detected) DetectObserved(string source)
    {
        var observations = new FrontEndTraversalObservations();
        var (detected, diagnostics) = ParameterDetector.DetectPrevalidated(Syntax(source), null, observations);
        Assert.Empty(diagnostics);
        return (observations, detected);
    }

    private static string PromotingBlocks(int width, int blocks)
        => $"F({Names("v", width)}) = v0" + string.Concat(Enumerable.Repeat(", {a + 1}", blocks)) + "\n1";

    private static IEnumerable<ImplicitParameterProvenance> BlockNotes(Algorithm detected)
        => Assert.IsType<Algorithm.User>(Assert.Single(detected.Properties, p => p.Name == "F").Value).Output
            .OfType<Expr.AlgorithmExpr>()
            .Select(block => Assert.Single(Assert.IsType<Algorithm.User>(block.Algorithm).Parameters).InferredProvenance!);

    /// <summary>
    /// K blocks promoting a name under an owner of W parameters: each promotion only CAPTURES its
    /// suggestion context, so detection compares no candidate at all, and the context work — the
    /// canonicalized names and the set-algebra steps — is the same for K and 2K promotions, because
    /// every block shares the owner's derived context. Computing the suggestion at promotion
    /// re-collected, re-resolved, and re-compared the W visible names per block (up to 512
    /// candidates × a 64 × 64 distance table each: ~3 ms per block, ~100 s at the source ceiling).
    /// </summary>
    [Theory]
    [InlineData(150)]
    [InlineData(300)]
    public void Detector_PromotionsUnderAWideOwner_CaptureSuggestionContextsOnce(int width)
    {
        var (fewer, fewerTree) = DetectObserved(PromotingBlocks(width, 200));
        var (more, moreTree) = DetectObserved(PromotingBlocks(width, 400));

        Assert.Equal(0, fewer.SuggestionCandidatesExamined);
        Assert.Equal(0, more.SuggestionCandidatesExamined);
        Assert.Equal(fewer.ContextNamesCanonicalized, more.ContextNamesCanonicalized);
        Assert.Equal(fewer.NameSetOperationSteps, more.NameSetOperationSteps);
        Assert.All(BlockNotes(moreTree), note => Assert.False(note.IsSuggestionEvaluated));
        Assert.Equal(400, BlockNotes(moreTree).Count());
        Assert.Equal(200, BlockNotes(fewerTree).Count());
    }

    /// <summary>
    /// The wide half of the same pin: widening the owner by W names canonicalizes exactly those W
    /// names once, whatever the number of promoting blocks.
    /// </summary>
    [Fact]
    public void Detector_SuggestionContextWork_GrowsWithTheOwnerWidthOnce()
    {
        var (narrow, _) = DetectObserved(PromotingBlocks(150, 300));
        var (wide, _) = DetectObserved(PromotingBlocks(300, 300));

        Assert.Equal(150, wide.ContextNamesCanonicalized - narrow.ContextNamesCanonicalized);
    }

    /// <summary>
    /// K blocks each declaring a DISTINCT local property beside the promoted name: every block is its
    /// own suggestion context, derived from the enclosing one by its one own name — K more names
    /// canonicalized for K more blocks, never K × W.
    /// </summary>
    [Fact]
    public void Detector_BlocksWithDistinctLocals_DeriveTheirSuggestionContextsIncrementally()
    {
        static string Source(int width, int blocks)
            => $"F({Names("v", width)}) = v0"
                + string.Concat(Enumerable.Range(0, blocks).Select(i => $", {{b{i} = a + 1\nb{i}}}"))
                + "\n1";

        // Both widths stay within the 512-candidate work bound, so every block derives its context.
        var (fewer, _) = DetectObserved(Source(150, 200));
        var (more, _) = DetectObserved(Source(150, 400));
        var (wider, _) = DetectObserved(Source(300, 200));

        Assert.Equal(0, more.SuggestionCandidatesExamined);
        Assert.Equal(200, more.ContextNamesCanonicalized - fewer.ContextNamesCanonicalized);
        Assert.Equal(150, wider.ContextNamesCanonicalized - fewer.ContextNamesCanonicalized);
        // Each block's union with the enclosing context walks the paths of its own name only.
        Assert.True(
            more.NameSetOperationSteps - fewer.NameSetOperationSteps <= 200 * 32,
            $"200 more blocks took {more.NameSetOperationSteps - fewer.NameSetOperationSteps} set-algebra steps");
    }

    /// <summary>
    /// The suggestion is computed on first read — when a diagnostic renders it — from the captured
    /// candidates, once: a second read compares nothing.
    /// </summary>
    [Fact]
    public void Suggestion_IsEvaluatedOnFirstRead_FromTheCapturedCandidates()
    {
        var (observations, detected) = DetectObserved(PromotingBlocks(20, 3) + "\nV0 = 1");
        var note = BlockNotes(detected).First();

        Assert.False(note.IsSuggestionEvaluated);
        _ = note.SuggestedName;
        var examined = observations.SuggestionCandidatesExamined;
        _ = note.SuggestedName;

        Assert.True(note.IsSuggestionEvaluated);
        Assert.True(examined > 20, $"examined {examined} candidates");
        Assert.Equal(examined, observations.SuggestionCandidatesExamined);
    }

    // ── Collision validation ─────────────────────────────────────────────────

    /// <summary>
    /// The collision validator over an owner of W parameters with K blocks of one parameter each:
    /// one context per signature (the empty root context, the owner's, one per block), each
    /// EXTENDING its enclosing context — W + K declaration entries and W + K canonicalized names.
    /// Copying the enclosing declarations and re-sorting every name per block cost K × W.
    /// </summary>
    [Theory]
    [InlineData(400, 300)]
    [InlineData(800, 600)]
    public void CollisionValidator_BlocksUnderAWideOwner_ExtendTheirContextByTheirOwnNames(int width, int blocks)
    {
        var source = $"F({Names("v", width)}) = v0" + string.Concat(Enumerable.Repeat(", {a + 1}", blocks)) + "\n1";
        var resolved = Resolve(Detect(Syntax(source)));
        var observations = new FrontEndTraversalObservations();
        var diagnostics = new DiagnosticBag();

        new ParameterPropertyCollisionValidator(diagnostics, programRoot: resolved) { TraversalObservations = observations }
            .VisitAlgorithm(resolved);

        Assert.Empty(diagnostics);
        Assert.Equal(width + blocks, observations.ContextEntriesWritten);
        Assert.Equal(width + blocks, observations.ContextNamesCanonicalized);
        Assert.Equal(blocks + 2, observations.CollisionContextInterns);
    }

    /// <summary>
    /// A chain of DERIVATION diamonds: at every level one shared body is reached under the same
    /// visible names through two different extension orders (<c>x</c> then <c>y</c>, and <c>y</c>
    /// then <c>x</c>). Context identity is the name set's CONTENT, so the shared body is validated
    /// once per level — five algorithm expansions per level — where a derivation-dependent identity
    /// validates it once per path, 2^depth times.
    /// </summary>
    [Theory]
    [InlineData(8)]
    [InlineData(16)]
    public void CollisionValidator_DerivationDiamond_ValidatesEachBodyOncePerNameSet(int depth)
    {
        Algorithm current = User([], [], new Expr.Num(1));
        for (var level = 1; level <= depth; level++)
        {
            var shared = new Expr.AlgorithmExpr(current);
            Algorithm.User Owner(string name, Expr inner) => User([new CaptureParameterPattern(name)], [], inner);
            var xThenY = Owner($"x{level}", new Expr.AlgorithmExpr(Owner($"y{level}", shared)));
            var yThenX = Owner($"y{level}", new Expr.AlgorithmExpr(Owner($"x{level}", shared)));
            current = User([], [], new Expr.AlgorithmExpr(xThenY), new Expr.AlgorithmExpr(yThenX));
        }

        var root = User(Captures("w", 200), [], new Expr.AlgorithmExpr(current));
        var observations = new FrontEndTraversalObservations();
        var diagnostics = new DiagnosticBag();

        new ParameterPropertyCollisionValidator(diagnostics) { TraversalObservations = observations }.VisitAlgorithm(root);

        Assert.Empty(diagnostics);
        // The wide root and the leaf, plus each level's body and its four owners.
        Assert.Equal(5 * depth + 2, observations.WalkerAlgorithmExpansions);
    }

    // ── Summaries and exposure ───────────────────────────────────────────────

    /// <summary>
    /// K properties of an owner of W parameters, each requiring one of them: the owner's W names are
    /// materialized ONCE per resolution, and each property's single requirement is qualified by
    /// probing that one name — once in each of the two fixed-point rounds, 2K probes (the output
    /// row's <c>v0</c> is owned directly and needs none) — never by scanning the owner's W
    /// parameters per property per round.
    /// </summary>
    [Theory]
    [InlineData(400, 300)]
    [InlineData(800, 600)]
    public void Summaries_PropertiesOfAWideOwner_ShareOneParameterNameSet(int width, int properties)
    {
        var source = $"F({Names("v", width)}) = {{\n"
            + string.Concat(Enumerable.Range(0, properties).Select(i => $"P{i} = v0\n"))
            + "v0\n}\n1";
        var resolved = Resolve(Detect(Syntax(source)));
        var observations = new FrontEndTraversalObservations();

        _ = PropertyExposureResolver.Resolve(resolved, observations);

        Assert.Equal(width, observations.OwnerParameterNamesMaterialized);
        Assert.Equal(2 * properties, observations.SummaryQualificationProbes);
    }

    // ── Sibling-order walk: shadow scopes ─────────────────────────────────────

    /// <summary>
    /// A property value declaring W properties with K output blocks, each declaring one: entering
    /// each block EXTENDS the value's shadow names by one — W + K canonicalized names. Copying and
    /// re-sorting the W enclosing names per block cost K × W.
    /// </summary>
    [Theory]
    [InlineData(400, 300)]
    [InlineData(800, 600)]
    public void DependencyOrder_BodiesUnderAWideShadowScope_ExtendTheShadowNamesByTheirOwn(int width, int blocks)
    {
        var source = "V = {\n"
            + string.Concat(Enumerable.Range(0, width).Select(i => $"p{i} = 1\n"))
            + string.Concat(Enumerable.Repeat("{x = 1\nx}\n", blocks))
            + "p0\n}\n1";
        var detected = Assert.IsType<Algorithm.User>(Detect(Syntax(source)));
        var observations = new FrontEndTraversalObservations();

        _ = PropertyDependencyGraphBuilder.BuildDependencyOrder(detected, observations: observations);

        Assert.Equal(width + blocks, observations.ContextNamesCanonicalized);
    }

    /// <summary>
    /// The sibling-order walk's DERIVATION diamond: one shared body per level is reached under the
    /// same shadow names through two orders of nested bodies (declaring <c>p</c> then <c>q</c>, and
    /// <c>q</c> then <c>p</c>). The shadow key is the names' CONTENT, so the shared body is walked
    /// once per level, never once per path.
    /// </summary>
    [Theory]
    [InlineData(8)]
    [InlineData(16)]
    public void DependencyOrder_DerivationDiamond_WalksEachBodyOncePerShadowSet(int depth)
    {
        static Property Declare(string name) => new(name, User([], [], new Expr.Num(1)));
        Algorithm current = User([], [], new Expr.Num(1));
        for (var level = 1; level <= depth; level++)
        {
            var shared = new Expr.AlgorithmExpr(current);
            Algorithm.User Body(string name, Expr inner) => User([], [Declare(name)], inner);
            var pThenQ = Body($"p{level}", new Expr.AlgorithmExpr(Body($"q{level}", shared)));
            var qThenP = Body($"q{level}", new Expr.AlgorithmExpr(Body($"p{level}", shared)));
            current = User([], [], new Expr.AlgorithmExpr(pThenQ), new Expr.AlgorithmExpr(qThenP));
        }

        var root = User([], [new Property("V", current), new Property("W", User([], [], new Expr.Num(2)))], new Expr.Num(1));
        var observations = new FrontEndTraversalObservations();

        _ = PropertyDependencyGraphBuilder.BuildDependencyOrder(root, observations: observations);

        // Each level's four bodies enter one name each; the shared body adds none of its own.
        Assert.Equal(4 * depth, observations.ContextNamesCanonicalized);
        // Every level's body and its four owners' output rows, each walked once.
        Assert.Equal(5 * depth, observations.DependencySiblingExpansions);
    }

    // ── A shared diamond under a wide context ─────────────────────────────────

    /// <summary>
    /// The clause-family diamond (two families per level share ONE branch body, 2^depth paths)
    /// declared in an owner of W parameters beside W root properties. Region counts stay one per
    /// level in every pass, sharing survives, and the W-wide context is paid ONCE: the captured
    /// names canonicalized once, the owner's parameter names materialized once, and the resolver
    /// writing each root signature twice plus two locals per level.
    /// </summary>
    [Theory]
    [InlineData(300, 8)]
    [InlineData(300, 24)]
    public void FrontEnd_FamilyDiamondUnderAWideContext_PaysTheWideContextOnce(int width, int depth)
    {
        Algorithm body = User([], [], new Expr.Num(1));
        for (var level = 0; level < depth; level++)
        {
            Algorithm.Conditional Family() => new(null, [], [new CondBranch(new Pattern.LitInt(0), body)]);
            body = User([], [new Property("Left", Family()), new Property("Right", Family())],
                new Expr.Call(new Expr.Resolve("Left"), new OutputBundle([new Expr.Num(0)])));
        }

        var mod = Assert.IsType<Algorithm.User>(body) with { ParameterPatterns = Captures("v", width) };
        var root = User(
            [],
            [.. Enumerable.Range(0, width).Select(i => new Property($"P{i}", User([], [], new Expr.Num(1)))), new Property("Mod", mod)],
            new Expr.Num(1));

        var detectorObservations = new FrontEndTraversalObservations();
        var (detected, detectorDiagnostics) = ParameterDetector.DetectPrevalidated(root, null, detectorObservations);
        Assert.Empty(detectorDiagnostics);
        Assert.Equal(depth, detectorObservations.DetectorBranchBodyRegionExpansions);
        Assert.Equal(width, detectorObservations.ContextNamesCanonicalized);
        AssertSharedAtEveryLevel(detected, depth);

        var resolverObservations = new FrontEndTraversalObservations();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, resolverObservations, new DiagnosticBag());
        Assert.Equal(depth, resolverObservations.ResolverBranchBodyRegionExpansions);
        Assert.Equal(2 * width + 2 * depth + 2, resolverObservations.ContextEntriesWritten);
        AssertSharedAtEveryLevel(resolved, depth);

        var exposureObservations = new FrontEndTraversalObservations();
        var exposed = PropertyExposureResolver.Resolve(resolved, exposureObservations);
        Assert.Equal(depth, exposureObservations.DependencyBranchBodySummaryComputations);
        Assert.Equal(width, exposureObservations.OwnerParameterNamesMaterialized);
        AssertSharedAtEveryLevel(exposed, depth);

        var collisionObservations = new FrontEndTraversalObservations();
        var collisions = new DiagnosticBag();
        new ParameterPropertyCollisionValidator(collisions, programRoot: exposed) { TraversalObservations = collisionObservations }
            .VisitAlgorithm(exposed);
        Assert.Empty(collisions);
        Assert.Equal(width, collisionObservations.ContextNamesCanonicalized);
        Assert.Equal(2, collisionObservations.CollisionContextInterns);
    }

    // ── Design-independent guard: a child's cost does not grow with the context width ──

    // Thread-local allocation of one run of an already-prepared pass, after a warming run.
    private static long Allocation(Action pass)
    {
        pass();
        var before = GC.GetAllocatedBytesForCurrentThread();
        pass();
        return GC.GetAllocatedBytesForCurrentThread() - before;
    }

    /// <summary>
    /// A workload factory: (width W, children K) → the pass under test over inputs prepared
    /// outside the measured action.
    /// </summary>
    public static TheoryData<string> WidthWorkloads =>
        ["resolver-blocks", "detector-blocks", "detector-branches", "collision-blocks", "exposure-properties", "sibling-walk-blocks"];

    private static Action WidthWorkload(string workload, int width, int children)
    {
        switch (workload)
        {
            case "resolver-blocks":
            {
                var detected = Detect(Syntax(
                    string.Concat(Enumerable.Range(0, width).Select(i => $"Q{i} = 1\n"))
                    + string.Concat(Enumerable.Range(0, children).Select(i => $"P{i} = {{a = 1\n1}}\n"))
                    + "1"));
                return () => ImplicitArgumentResolver.ResolvePrevalidated(detected);
            }

            case "detector-blocks":
            {
                var syntax = Syntax(PromotingBlocks(width, children));
                return () => ParameterDetector.DetectPrevalidated(syntax);
            }

            case "detector-branches":
            {
                var syntax = Syntax($"F({Names("v", width)}) = {{\n"
                    + string.Concat(Enumerable.Range(0, children).Select(i => $"B{i}(0) = 1\n"))
                    + "v0\n}\n1");
                return () => ParameterDetector.DetectPrevalidated(syntax);
            }

            case "collision-blocks":
            {
                var resolved = Resolve(Detect(Syntax(PromotingBlocks(width, children))));
                return () => new ParameterPropertyCollisionValidator(new DiagnosticBag(), programRoot: resolved).VisitAlgorithm(resolved);
            }

            case "exposure-properties":
            {
                var resolved = Resolve(Detect(Syntax($"F({Names("v", width)}) = {{\n"
                    + string.Concat(Enumerable.Range(0, children).Select(i => $"P{i} = v0\n"))
                    + "v0\n}\n1")));
                return () => PropertyExposureResolver.Resolve(resolved);
            }

            case "sibling-walk-blocks":
            {
                var detected = Assert.IsType<Algorithm.User>(Detect(Syntax("V = {\n"
                    + string.Concat(Enumerable.Range(0, width).Select(i => $"p{i} = 1\n"))
                    + string.Concat(Enumerable.Repeat("{x = 1\nx}\n", children))
                    + "p0\n}\n1")));
                return () => PropertyDependencyGraphBuilder.BuildDependencyOrder(detected);
            }

            default:
                throw new ArgumentOutOfRangeException(nameof(workload), workload, null);
        }
    }

    /// <summary>
    /// Whatever is counted where, the allocation K children add to a pass must not depend on how
    /// many names the context they are nested in sees. Widening the context leaves the children's
    /// share nearly unchanged when every child extends the shared context by its own few names (a
    /// persistent insert costs O(log W)); it grows with the width when each child copies, re-sorts,
    /// or re-materializes the W-name context, as every pass did before FE-1 (measured against the
    /// pre-FE-1 passes: 3.0× to 4.2× here). The resolver's and the summaries' former per-child copy
    /// was a smaller part of a child's cost, so their context widens 16× instead of 4×; the
    /// detector's stays within the 512-candidate suggestion bound, where the former eager
    /// suggestion work scaled with W.
    /// </summary>
    [Theory]
    [MemberData(nameof(WidthWorkloads))]
    public void ChildAllocation_DoesNotGrowWithTheContextWidth(string workload)
    {
        const int children = 300;
        const int narrow = 100;
        var wide = workload is "resolver-blocks" or "exposure-properties" ? 1600 : 400;

        var narrowShare = Allocation(WidthWorkload(workload, narrow, children)) - Allocation(WidthWorkload(workload, narrow, 0));
        var wideShare = Allocation(WidthWorkload(workload, wide, children)) - Allocation(WidthWorkload(workload, wide, 0));

        var ratio = (double)wideShare / narrowShare;
        Assert.True(
            ratio < 1.6,
            $"{workload}: {children} children allocated {narrowShare} bytes under a {narrow}-name context but {wideShare} bytes " +
            $"under a {wide}-name one ({ratio:F2}x); a per-child copy of the context grows with the width.");
    }

    private static void AssertSharedAtEveryLevel(Algorithm root, int depth)
    {
        var current = Assert.IsType<Algorithm.User>(Assert.Single(Assert.IsType<Algorithm.User>(root).Properties, p => p.Name == "Mod").Value);
        for (var level = 0; level < depth; level++)
        {
            var left = Assert.IsType<Algorithm.Conditional>(Assert.Single(current.Properties, p => p.Name == "Left").Value);
            var right = Assert.IsType<Algorithm.Conditional>(Assert.Single(current.Properties, p => p.Name == "Right").Value);
            Assert.Same(Assert.Single(left.Branches).Body, Assert.Single(right.Branches).Body);
            current = Assert.IsType<Algorithm.User>(left.Branches[0].Body);
        }
    }
}
