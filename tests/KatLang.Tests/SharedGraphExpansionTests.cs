using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// One shared body under DISTINCT parents, every level (SHARED-GRAPH-1, November 2026): a legal host graph of 3d + 3
/// algorithms with 2^d paths. Before this repair detection copied a body per path, name-resolved registration and the
/// exposure summary channel walked per path, and pre-evaluation validation split alias contexts per path, so the program was
/// refused near depth 10. A body is now processed once per BINDING REGION: contexts whose free names select the same
/// declarations. These tests pin that the count follows distinct bindings, in both directions: an irrelevant parent difference
/// splits nothing, and each binding difference that changes a meaning still splits (an oracle fails if a key loses one).
/// </summary>
public sealed class SharedGraphExpansionTests
{
    private static Algorithm.User Block(IReadOnlyList<Property> properties, params Expr[] rows)
        => new(null, [], [], properties, new OutputBundle(rows));

    private static Property Public(string name, Algorithm value) => new(name, value, IsPublic: true);
    private static Expr Add(Expr left, Expr right) => new Expr.Binary(BinaryOp.Add, left, right);
    private static Expr Name(string name) => new Expr.Resolve(name);
    private static Expr Number(int value) => new Expr.Num(value);

    private static (Algorithm.User Left, Algorithm.User Right) Parents(Algorithm shared, bool different)
        => (Block(different ? [Public("S", shared), Public("OnlyLeft", Block([], Number(7)))] : [Public("S", shared)], Name("S")),
            Block(different ? [Public("OnlyRight", Block([], Number(8))), Public("S", shared)] : [Public("S", shared)],
                different ? Add(Name("S"), Number(0)) : Name("S")));

    /// <summary>Level i holds <c>L</c> and <c>R</c>, two distinct objects that each hold level i + 1: 2^depth paths.</summary>
    private static Algorithm.User DistinctParents(int depth, bool different = false, Algorithm? leaf = null)
    {
        var value = leaf ?? Block([], Add(Name("Leaf"), Number(0)));
        for (var level = 0; level < depth; level++)
        {
            var (left, right) = Parents(value, different);
            value = Block([Public("L", left), Public("R", right)], Add(Name("L"), Name("R")));
        }

        return Block([Public("Leaf", Block([], Number(1))), Public("Mod", value)], Name("Mod"));
    }

    /// <summary>A structurally identical tree of the same graph, every shared node copied once per path.</summary>
    private static Algorithm CloneTree(Algorithm algorithm)
    {
        Expr Expression(Expr expr) => expr switch
        {
            Expr.AlgorithmExpr block => new Expr.AlgorithmExpr(CloneTree(block.Algorithm)),
            Expr.Binary binary => binary with { Left = Expression(binary.Left), Right = Expression(binary.Right) },
            Expr.Call call => call with { Function = Expression(call.Function), Args = new OutputBundle([.. call.Args.Select(Expression)]) },
            _ => expr,
        };
        return algorithm switch
        {
            Algorithm.User user => user with { Parent = null, Opens = [.. user.Opens.Select(Expression)],
                Properties = [.. user.Properties.Select(property => property.WithValue(CloneTree(property.Value)))],
                Output = new OutputBundle([.. user.Output.Select(Expression)]) },
            Algorithm.Conditional family => family with { Parent = null, Opens = [.. family.Opens.Select(Expression)],
                Branches = [.. family.Branches.Select(branch => new CondBranch(branch.Pattern, CloneTree(branch.Body)))] },
            _ => algorithm,
        };
    }

    private static (Algorithm Exposed, FrontEndTraversalObservations Detection, FrontEndTraversalObservations Exposure, DiagnosticBag Diagnostics, StaticStructureOperation? Operation)
        Elaborate(Algorithm.User root, bool nameResolved, bool allowDiagnostics = false)
    {
        var diagnostics = new DiagnosticBag();
        var detection = new FrontEndTraversalObservations();
        StaticStructureOperation? operation = null;
        Algorithm resolved;
        if (nameResolved)
            resolved = ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(root, detection, diagnostics);
        else
        {
            var detected = ParameterDetector.DetectPrevalidated(root, observations: detection, diagnostics: diagnostics);
            operation = detected.Operation;
            resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, detection, diagnostics);
        }

        if (!allowDiagnostics) Assert.Equal(0, diagnostics.ReportedCount);
        new ParameterPropertyCollisionValidator(diagnostics, programRoot: resolved).VisitAlgorithm(resolved);
        OpenProviderValidator.Validate(resolved, diagnostics, (HostOperations?)null);
        InferredParameterOutputValidator.ValidateProgram(resolved, diagnostics);
        if (!allowDiagnostics) Assert.Equal(0, diagnostics.ReportedCount);
        var exposure = new FrontEndTraversalObservations();
        return (PropertyExposureResolver.Resolve(resolved, exposure), detection, exposure, diagnostics, operation);
    }

    private static Decimal128[] Evaluate(Algorithm exposed)
    {
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(exposed));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        return [.. result.Value];
    }

    private static Decimal128[] FullFrontEnd(Algorithm.User root, bool nameResolved) => Evaluate(Elaborate(root, nameResolved).Exposed);

    private static long CountAlgorithms(object root)
    {
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance) { root };
        var pending = new Stack<object>([root]);
        long algorithms = 0;
        while (pending.TryPop(out var node))
        {
            if (node is Algorithm) algorithms++;
            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
                if (seen.Add(child)) pending.Push(child);
        }

        return algorithms;
    }

    private static long PublishedContexts(StaticStructureOperation operation)
        => operation.Queries.Keys.DefinitionCount;

    // ── Scaling: deterministic counts, never time ─────────────────────────────────────────────────

    [Fact]
    public void StandaloneAnalysis_ProjectsEquivalentOccurrencesWithoutExpandingTheirPaths()
    {
        var shallow = AnalyzedStaticStructures.ForBoundAst(DistinctParents(6));
        var deepRoot = DistinctParents(24);
        var deep = AnalyzedStaticStructures.ForBoundAst(deepRoot);
        Assert.Null(deepRoot.CompletedStructure); // Analysis is never Q9 completion.
        Assert.True(deep.Facts.Scopes.Count() < 4 * shallow.Facts.Scopes.Count());
        CompletedStructureContext Child(CompletedStructureContext parent, Algorithm body)
            => parent.Facts.Context(parent.Facts.Child(parent.Key, body)!);
        var mod = Child(deep, Member(deepRoot, "Mod").Value);
        var modBody = Member(deepRoot, "Mod").Value;
        var left = Child(mod, Member(modBody, "L").Value);
        var right = Child(mod, Member(modBody, "R").Value);
        var shared = Member(Member(modBody, "L").Value, "S").Value;
        var unadmittedCopy = Assert.IsType<Algorithm.User>(shared) with { Output = [Number(99)] };
        Assert.Null(deep.Facts.Child(left.Key, unadmittedCopy));
        var leftChild = Child(left, shared);
        var rightChild = Child(right, shared);
        Assert.NotSame(leftChild.Key, rightChild.Key);
        Assert.Same(left.Key, leftChild.Key.Parent);
        Assert.Same(right.Key, rightChild.Key.Parent);
        var leftMember = leftChild.Facts.Facts(leftChild.Key)!.Members["L"];
        var rightMember = rightChild.Facts.Facts(rightChild.Key)!.Members["L"];
        Assert.Same(leftChild.Key, leftMember.Parent);
        Assert.Same(rightChild.Key, rightMember.Parent);
        Assert.NotEqual(leftChild.Facts.Facts(leftMember)!.Receiver.Identity,
            rightChild.Facts.Facts(rightMember)!.Receiver.Identity);
        Assert.Equal(CountAlgorithms(deepRoot), CountAlgorithms(PropertyExposureResolver.Resolve(deepRoot)));
    }

    [Fact]
    public void StandaloneAnalysis_KeepsDifferentOpenProvidersAndTheirDeclaringContexts()
    {
        var shared = Block([], Name("V")) with { Opens = [Name("Lib")] };
        var leftLib = Block([Public("V", Block([], Number(7)))], Number(0));
        var rightLib = Block([Public("V", Block([], Number(9)))], Number(0));
        var left = Block([Public("Lib", leftLib), Public("S", shared)], Name("S"));
        var right = Block([Public("Lib", rightLib), Public("S", shared)], Name("S"));
        var root = Block([Public("Left", left), Public("Right", right)], Add(Name("Left"), Name("Right")));
        var context = AnalyzedStaticStructures.ForBoundAst(root);
        var facts = context.Facts;
        var leftKey = facts.Member(context.Key, "Left")!;
        var rightKey = facts.Member(context.Key, "Right")!;
        var leftShared = facts.Child(leftKey, shared)!;
        var rightShared = facts.Child(rightKey, shared)!;
        Assert.Same(facts.Member(leftKey, "Lib"), Assert.Single(facts.Facts(leftShared)!.Providers).Target);
        Assert.Same(facts.Member(rightKey, "Lib"), Assert.Single(facts.Facts(rightShared)!.Providers).Target);
        Assert.NotSame(facts.Facts(leftShared)!.Providers[0].Target, facts.Facts(rightShared)!.Providers[0].Target);
        Assert.Equal([(Decimal128)16], Evaluate(PropertyExposureResolver.Resolve(root)));
    }

    [Fact]
    public void StandaloneQuerySource_CanBeExtendedBelowASharedOccurrence()
    {
        var root = DistinctParents(2);
        var analysis = StandaloneScopeAnalysis.Start(root, StaticAstPhase.Resolved);
        foreach (var name in new[] { "Mod", "R", "S", "L", "S" })
        {
            var body = analysis.Context.Facts.Facts(analysis.Context.Key)!.Body!;
            analysis = analysis.Inside(Member(body, name).Value, null, StaticAstPhase.Resolved, ownerIdentity: null);
            Assert.True(analysis.Source.Contexts.ContainsKey(analysis.Context.Key));
        }
        var extra = Block([], Number(5));
        var extended = analysis.Inside(extra, null, StaticAstPhase.Resolved, ownerIdentity: null);
        Assert.Same(extra, extended.Context.Facts.Facts(extended.Context.Key)!.Body);
    }

    [Fact]
    public void StandaloneAnalysis_CancellationAfterReuseAndResourceRefusalPublishNothing_AndPermitFreshRetry()
    {
        var root = DistinctParents(8);
        using var cancellation = new CancellationTokenSource();
        var operation = StaticStructureAdmission.Create(root, phase: StaticAstPhase.Resolved,
            cancellationToken: cancellation.Token).Operation;
        var reused = 0;
        operation.Queries.Observations = new FrontEndTraversalObservations
        {
            StageObserver = (name, _) => { if (name == "analysis-region-reuse") { reused++; cancellation.Cancel(); } },
        };
        var error = Assert.ThrowsAny<OperationCanceledException>(() =>
            AnalyzedStaticStructures.ForAdmittedSource(operation.Context(operation.Root), cancellation.Token));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal(1, reused);
        Assert.True(operation.Queries.Resources.IsFailed);
        Assert.Null(root.CompletedStructure);
        Assert.Throws<StaticQueryLimitExceededException>(() => AnalyzedStaticStructures.ForBoundAst(root,
            sourceProcessingLimits: new SourceProcessingLimits { MaxStaticStructureBytes = 128 * 1024 }));
        Assert.Null(root.CompletedStructure);
        var retry = AnalyzedStaticStructures.ForBoundAst(root);
        Assert.Same(root, retry.Facts.Facts(retry.Key)!.Body);
        Assert.Null(root.CompletedStructure);
        Assert.Equal([(Decimal128)256], Evaluate(PropertyExposureResolver.Resolve(root)));
    }

    /// <summary>
    /// The historical witness, with parents equal and parents that differ only in what no shared body reads, on both entries.
    /// Depth 24 has 16 million paths and was refused near depth 10: output, regions and contexts now grow by a constant per
    /// level, exactly, so any path-shaped regression fails on the count rather than on a clock.
    /// </summary>
    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void DistinctParents_CostOneRegionPerLevel(bool nameResolved, bool different)
    {
        var (shallow, deep) = (Elaborate(DistinctParents(12, different), nameResolved), Elaborate(DistinctParents(24, different), nameResolved));
        var outputPerLevel = (CountAlgorithms(deep.Exposed) - CountAlgorithms(shallow.Exposed)) / 12;
        Assert.Equal(different ? 5 : 3, outputPerLevel);
        Assert.Equal(12, deep.Exposure.ExposureSharedRegionExpansions - shallow.Exposure.ExposureSharedRegionExpansions);
        Assert.Equal(12, deep.Exposure.ExposureSharedRegionHits - shallow.Exposure.ExposureSharedRegionHits);
        Assert.Equal(12 * (different ? 5 : 3), deep.Exposure.ExposureAlgorithmExpansions - shallow.Exposure.ExposureAlgorithmExpansions);
        Assert.True(deep.Exposure.DependencyAlgorithmSummaryComputations <= 2 * shallow.Exposure.DependencyAlgorithmSummaryComputations + 8,
            $"summaries {shallow.Exposure.DependencyAlgorithmSummaryComputations} -> {deep.Exposure.DependencyAlgorithmSummaryComputations}");
        if (!nameResolved)
        {
            Assert.Equal(24, deep.Detection.DetectorSharedRegionExpansions);
            Assert.Equal(24, deep.Detection.DetectorSharedRegionHits);
            Assert.True(PublishedContexts(deep.Operation!) <= 2 * PublishedContexts(shallow.Operation!),
                $"contexts {PublishedContexts(shallow.Operation!)} -> {PublishedContexts(deep.Operation!)}");
        }
    }

    /// <summary>
    /// The neighbors of the same shape: an open below the shared region, a shared clause family, a block literal in place of a
    /// property, a dot edge, and an implicit parameter crossing every level. The expansion must not have moved next door.
    /// </summary>
    [Theory]
    [InlineData("open")]
    [InlineData("family")]
    [InlineData("block")]
    [InlineData("dot")]
    [InlineData("miss")]
    [InlineData("parameter")]
    public void NeighboringShapes_StayBoundedAtDepthsFarBeyondTheBudgetForTheirPaths(string shape)
    {
        foreach (var nameResolved in new[] { false, true })
        {
            var (start, shallow, deep) = (Elaborate(Neighbor(shape, 6), nameResolved), Elaborate(Neighbor(shape, 12), nameResolved),
                Elaborate(Neighbor(shape, 24), nameResolved));
            // Exactly linear in the depth, whatever each shape's constant is: the second 12 levels cost twice the 6 before them.
            Assert.Equal(2 * (CountAlgorithms(shallow.Exposed) - CountAlgorithms(start.Exposed)),
                CountAlgorithms(deep.Exposed) - CountAlgorithms(shallow.Exposed));
            Assert.Equal(2 * (shallow.Exposure.ExposureAlgorithmExpansions - start.Exposure.ExposureAlgorithmExpansions),
                deep.Exposure.ExposureAlgorithmExpansions - shallow.Exposure.ExposureAlgorithmExpansions);
        }
    }

    private static Algorithm.User Neighbor(string shape, int depth)
    {
        static Algorithm.User Level(Algorithm shared) => Block(
            [Public("L", Block([Public("S", shared)], Name("S"))), Public("R", Block([Public("S", shared)], Name("S")))],
            Add(Name("L"), Name("R")));
        Algorithm value;
        switch (shape)
        {
            case "open":
                value = new Algorithm.User(null, [], [Name("Lib")], [], new OutputBundle([Add(Name("Member"), Number(0))]));
                for (var level = 0; level < depth; level++) value = Level(value);
                break;
            case "dot":
                value = Block([], Add(new Expr.DotCall(Name("Lib"), "Member", null), Number(0)));
                for (var level = 0; level < depth; level++) value = Level(value);
                break;
            case "parameter":
                value = Block([], Add(Name("x"), Number(0)));
                for (var level = 0; level < depth; level++) value = Level(value);
                break;
            case "block":
                value = Block([], Add(Name("Lib"), Number(0)));
                for (var level = 0; level < depth; level++)
                {
                    var shared = new Expr.AlgorithmExpr(value);
                    value = Block([], Add(new Expr.AlgorithmExpr(Block([], Add(shared, Number(0)))), new Expr.AlgorithmExpr(Block([], Add(shared, Number(1))))));
                }
                break;
            case "miss":
                value = Block([], Add(new Expr.DotCall(Name("Lib"), "absent", null) { LexicalFallback = Name("absent") }, Number(0)));
                for (var level = 0; level < depth; level++) value = Level(value);
                return Block([Public("Lib", Block([Public("Member", Block([], Number(5)))], Number(0))), Public("Mod", value)], Number(0));
            case "family":
                value = Block([], Add(Name("Lib"), Number(0)));
                for (var level = 0; level < depth; level++)
                {
                    var family = new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.LitInt(0), Block([Public("S", value)], Name("S")))]);
                    var call = new Expr.Call(Name("F"), new OutputBundle([Number(0)]));
                    value = Block([Public("L", Block([Public("F", family)], call)), Public("R", Block([Public("F", family)], call))], Add(Name("L"), Name("R")));
                }
                break;
            default: throw new ArgumentOutOfRangeException(nameof(shape));
        }

        return Block([Public("Lib", Block([Public("Member", Block([], Number(5)))], Number(0))), Public("Mod", value)], Name("Mod"));
    }

    /// <summary>A parsed program holds no body reached twice, so no region key is ever computed for it.</summary>
    [Fact]
    public void ATree_DoesNoRegionWork()
    {
        var observations = new FrontEndTraversalObservations();
        var root = SourceProvenance.ParseSyntaxValidRoot("A = { public B = 1\n 2 }\nC = { public B = 3\n A + 4 }\nC + A.B");
        ParameterDetector.DetectPrevalidated(root, observations: observations);
        Assert.Equal(0, observations.DetectorSharedRegionExpansions + observations.DetectorSharedRegionHits);
    }

    // ── Reuse: and every fact that must keep regions apart ─────────────────────────────────────────

    /// <summary>A shared DAG evaluates like the tree it stands for, at a depth whose tree is small.</summary>
    [Theory]
    [InlineData("open")]
    [InlineData("family")]
    [InlineData("block")]
    [InlineData("dot")]
    public void SharedGraphs_EvaluateLikeTheirTrees(string shape)
    {
        var graph = Neighbor(shape, 5);
        var tree = (Algorithm.User)CloneTree(graph);
        Assert.True(CountAlgorithms(tree) > 4 * CountAlgorithms(graph));
        foreach (var nameResolved in new[] { false, true })
        {
            if (shape == "block" && nameResolved) continue; // A block holding Lib is a detected read: name-resolved input has none.
            Assert.Equal(FullFrontEnd(tree, nameResolved), FullFrontEnd(graph, nameResolved));
        }
    }

    [Fact]
    public void ADistinctParentGraph_EvaluatesLikeItsTree()
    {
        const int Depth = 6;
        var graph = DistinctParents(Depth, different: true);
        var expected = (Decimal128)(1 << Depth);
        Assert.Equal([expected], FullFrontEnd(graph, nameResolved: false));
        Assert.Equal([expected], FullFrontEnd((Algorithm.User)CloneTree(graph), nameResolved: false));
    }

    /// <summary>Equal binding, irrelevant parent difference: ONE processing, whose output object both parents hold.</summary>
    [Fact]
    public void AnIrrelevantParentDifference_SharesOneBody()
    {
        var (exposed, detection, exposure, _, _) = Elaborate(DistinctParents(1, different: true), nameResolved: false);
        Assert.Equal(1, detection.DetectorSharedRegionHits);
        Assert.Equal(1, exposure.ExposureSharedRegionHits);
        var mod = ((Algorithm.User)exposed).Properties.Single(property => property.Name == "Mod").Value;
        Assert.Same(
            mod.Properties.Single(property => property.Name == "L").Value.Properties.Single(property => property.Name == "S").Value,
            mod.Properties.Single(property => property.Name == "R").Value.Properties.Single(property => property.Name == "S").Value);
    }

    /// <summary>
    /// Parents binding the shared body's free name to DIFFERENT declarations with equal displayed shape: never one region, in
    /// the input order that would hide it either way. A memo ignoring the binding answers 2, 2.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DifferentDeclarationsOfOneFreeName_NeverShareARegion(bool nameResolved)
    {
        var shared = Block([], Add(Name("V"), Number(0)));
        var root = Block(
            [
                Public("Left", Block([Public("V", Block([], Number(1))), Public("S", shared)], Name("S"))),
                Public("Right", Block([Public("V", Block([], Number(2))), Public("S", shared)], Name("S"))),
            ],
            new Expr.DotCall(Name("Left"), "S", null), new Expr.DotCall(Name("Right"), "S", null));
        var elaborated = Elaborate(root, nameResolved);
        Assert.Equal([(Decimal128)1, (Decimal128)2], Evaluate(elaborated.Exposed));
        Assert.Equal(0, elaborated.Detection.DetectorSharedRegionHits);
    }

    /// <summary>A name that is a property under one parent and an inferred parameter under the other is two elaborations.</summary>
    [Fact]
    public void APropertyAndAnInferredParameter_NeverShareARegion()
    {
        var shared = Block([], Add(Name("x"), Number(0)));
        var root = Block(
            [
                Public("Left", Block([Public("x", Block([], Number(1))), Public("S", shared)], Name("S"))),
                Public("Right", Block([Public("S", shared)], Add(Name("S"), Name("x")))),
            ],
            Name("Left"), new Expr.Call(Name("Right"), new OutputBundle([Number(5)])));
        var elaborated = Elaborate(root, nameResolved: false);
        Assert.Equal(0, elaborated.Detection.DetectorSharedRegionHits);
        Assert.Equal([(Decimal128)1, (Decimal128)10], Evaluate(elaborated.Exposed));
    }

    /// <summary>
    /// A direct declaration outranks the shared body's own open while an enclosing OPENED one does not, though both answer
    /// the name: comparing only "what the name finally denotes" outward would merge these.
    /// </summary>
    [Fact]
    public void OwnedAndOpenedBindings_AreSeparateFacts()
    {
        var inner = Block([Public("M", Block([], Number(3)))], Number(0));
        var shared = new Algorithm.User(null, [], [new Expr.AlgorithmExpr(inner)], [], new OutputBundle([Add(Name("M"), Number(0))]));
        var outer = Block([Public("M", Block([], Number(2)))], Number(0));
        var root = Block(
            [
                Public("Left", Block([Public("M", Block([], Number(1))), Public("S", shared)], Name("S"))),
                Public("Right", new Algorithm.User(null, [], [new Expr.AlgorithmExpr(outer)], [Public("S", shared)], new OutputBundle([Name("S")]))),
            ],
            Name("Left"), Name("Right"));
        var tree = (Algorithm.User)CloneTree(root);
        var expected = FullFrontEnd(tree, nameResolved: false);
        Assert.Equal([(Decimal128)1, (Decimal128)3], expected);
        Assert.Equal(expected, FullFrontEnd(root, nameResolved: false));
    }

    /// <summary>
    /// An inline open block of a shared body is rooted at the prelude, one context whichever occurrence reaches it, so a body
    /// processed in two regions still elaborates it once (a second publication of that context used to be an internal failure).
    /// </summary>
    [Fact]
    public void AnInlineOpenBlock_IsOneContextInEveryRegion()
    {
        var provider = Block([Public("M", Block([], Number(3)))], Number(0));
        var shared = new Algorithm.User(null, [], [new Expr.AlgorithmExpr(provider)], [], new OutputBundle([Add(Name("M"), Name("V"))]));
        var root = Block(
            [
                Public("Left", Block([Public("V", Block([], Number(1))), Public("S", shared)], Name("S"))),
                Public("Right", Block([Public("V", Block([], Number(2))), Public("S", shared)], Name("S"))),
            ],
            Name("Left"), Name("Right"));
        Assert.Equal([(Decimal128)4, (Decimal128)5], FullFrontEnd(root, nameResolved: false));
    }

    /// <summary>
    /// The sharpest owned/opened fixture: both parents' final answer for <c>M</c> is the SAME property of the SAME scope (one
    /// declares it, the other opens the first), yet the body's own open sits between them: an owned hit outranks it, an
    /// outer opened one does not. A footprint of the final binding alone merges these two contexts.
    /// </summary>
    [Fact]
    public void OneDeclarationReachedByOwnershipAndByOpen_IsTwoRegions()
    {
        var inner = Block([Public("M", Block([], Number(3)))], Number(0));
        var shared = new Algorithm.User(null, [], [new Expr.AlgorithmExpr(inner)], [], new OutputBundle([Add(Name("M"), Number(0))]));
        var root = Block(
            [
                Public("Left", Block([Public("M", Block([], Number(1))), Public("S", shared)], Name("S"))),
                Public("Right", new Algorithm.User(null, [], [Name("Left")], [Public("S", shared)], new OutputBundle([Name("S")]))),
            ],
            Name("Left"), Name("Right"));
        var elaborated = Elaborate(root, nameResolved: false);
        Assert.Equal(0, elaborated.Detection.DetectorSharedRegionHits);
        Assert.Equal([(Decimal128)1, (Decimal128)3], Evaluate(elaborated.Exposed));
    }

    private static Property Member(Algorithm owner, string name) => owner.Properties.Single(property => property.Name == name);

    /// <summary>
    /// The same supplied body whose free name is a self-contained value under one parent and a value capturing that parent's
    /// parameter under the other: exposure and the summary channel must see that <c>Q</c> and <c>S</c> are exported on one
    /// side and local-only on the other.
    /// </summary>
    [Fact]
    public void ACaptureBehindAFreeName_SplitsExposureAndSummaries()
    {
        var shared = Block([Public("Q", Block([], Add(Name("V"), Number(0))))], Add(Name("Q"), Number(0)));
        var left = Block([Public("V", Block([], Number(1))), Public("S", shared)], Number(0));
        var right = new Algorithm.User(null, [new CaptureParameterPattern("x")], [],
            [Public("V", Block([], new Expr.Param("x"))), Public("S", shared)], new OutputBundle([Number(0)])) { HasExplicitParameterList = true };
        var root = Block([Public("Left", left), Public("Right", right)], Number(0));

        // Through the whole pipeline resolution may keep the two apart; the standalone entry hands exposure the one shared body.
        foreach (var exposed in new[] { Elaborate(root, nameResolved: true).Exposed, PropertyExposureResolver.Resolve(root) })
        {
            var (exposedLeft, exposedRight) = (Member(exposed, "Left").Value, Member(exposed, "Right").Value);
            Assert.Equal(PropertyExposure.Exported, Member(exposedLeft, "S").Exposure);
            Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, Member(exposedRight, "S").Exposure);
            Assert.Equal(PropertyExposure.Exported, Member(Member(exposedLeft, "S").Value, "Q").Exposure);
            Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, Member(Member(exposedRight, "S").Value, "Q").Exposure);
        }
    }

    /// <summary>
    /// One value object declared at two levels, while the parameter that value captures is one level out on one side and two
    /// on the other. The body reads no parameter of its own: the level that DECLARES its free name separates the regions.
    /// </summary>
    [Fact]
    public void OneValueDeclaredAtTwoLevels_KeepsEachSidesCaptureDistance()
    {
        var value = Block([], new Expr.Param("x"));
        var shared = Block([Public("Q", Block([], Add(Name("V"), Number(0))))], Add(Name("Q"), Number(0)));
        var left = new Algorithm.User(null, [new CaptureParameterPattern("x")], [], [Public("V", value), Public("S", shared)], new OutputBundle([Number(0)]))
        {
            HasExplicitParameterList = true,
        };
        var right = Block([Public("V", value), Public("S", shared)], Number(0));
        var owner = new Algorithm.User(null, [new CaptureParameterPattern("x")], [], [Public("Left", left), Public("Right", right)], new OutputBundle([Number(0)]))
        {
            HasExplicitParameterList = true,
        };

        var exposedOwner = Member(Elaborate(Block([Public("Owner", owner)], Number(0)), nameResolved: true).Exposed, "Owner").Value;
        var (leftS, rightS) = (Member(Member(exposedOwner, "Left").Value, "S"), Member(Member(exposedOwner, "Right").Value, "S"));
        Assert.Equal(0, Assert.Single(leftS.CaptureRequirements!).OwnerDepth);
        Assert.Equal(1, Assert.Single(rightS.CaptureRequirements!).OwnerDepth);
        Assert.Equal(1, Assert.Single(Member(leftS.Value, "Q").CaptureRequirements!).OwnerDepth);
        Assert.Equal(2, Assert.Single(Member(rightS.Value, "Q").CaptureRequirements!).OwnerDepth);
    }

    /// <summary>A name's owner one level out and two levels out are different relative positions: never one rewritten body.</summary>
    [Fact]
    public void OneDepthWithTwoOwnerPositions_IsTwoExposureRegions()
    {
        var shared = Block([Public("Q", Block([], new Expr.Param("x")))], Number(0));
        var left = Block([Public("S", shared)], Number(0));
        var right = new Algorithm.User(null, [new CaptureParameterPattern("x")], [], [Public("S", shared)], new OutputBundle([Number(0)])) { HasExplicitParameterList = true };
        var owner = new Algorithm.User(null, [new CaptureParameterPattern("x")], [],
            [Public("Left", left), Public("Right", right)], new OutputBundle([Number(0)])) { HasExplicitParameterList = true };
        var root = Block([Public("Owner", owner)], Number(0));

        var exposedOwner = Member(Elaborate(root, nameResolved: true).Exposed, "Owner").Value;
        var (leftBody, rightBody) = (Member(Member(exposedOwner, "Left").Value, "S").Value, Member(Member(exposedOwner, "Right").Value, "S").Value);
        Assert.NotSame(leftBody, rightBody);
        Assert.Equal(2, Assert.Single(Member(leftBody, "Q").CaptureRequirements!).OwnerDepth);
        Assert.Equal(1, Assert.Single(Member(rightBody, "Q").CaptureRequirements!).OwnerDepth);
    }

    /// <summary>
    /// One body at two depths whose free name carries a capture only through an outer summary: no name of the body differs,
    /// only the distance to that owner, which the rewritten metadata records relative to each occurrence.
    /// </summary>
    [Fact]
    public void ACaptureCarriedByASummary_KeepsItsDistanceAtEachDepth()
    {
        var shared = Block([Public("Q", Block([], Add(Name("P"), Number(0))))], Number(0));
        var owner = new Algorithm.User(null, [new CaptureParameterPattern("x")], [],
            [Public("P", Block([], new Expr.Param("x"))), Public("Near", shared), Public("Far", Block([Public("Near", shared)], Number(0)))],
            new OutputBundle([Number(0)])) { HasExplicitParameterList = true };
        var root = Block([Public("Owner", owner)], Number(0));

        var exposedOwner = Member(Elaborate(root, nameResolved: true).Exposed, "Owner").Value;
        var (near, far) = (Member(exposedOwner, "Near").Value, Member(Member(exposedOwner, "Far").Value, "Near").Value);
        Assert.NotSame(near, far);
        Assert.Equal(Assert.Single(Member(near, "Q").CaptureRequirements!).OwnerDepth + 1, Assert.Single(Member(far, "Q").CaptureRequirements!).OwnerDepth);
    }

    /// <summary>
    /// Parameters of two parents at the same relative position: exposure's metadata is one (it is relative), detection's
    /// owners are two, and each activation reads its own argument: sharing is syntax, never activation state.
    /// </summary>
    [Fact]
    public void ACapturedParameter_KeepsItsOwnerAndActivation()
    {
        var shared = Block([Public("Q", Block([], Add(Name("x"), Number(0))))], Name("Q"));
        var root = Block(
            [
                Public("Left", Block([Public("S", shared)], Add(Name("S"), Name("x")))),
                Public("Right", Block([Public("S", shared)], Add(Name("S"), Name("x")))),
            ],
            new Expr.Call(Name("Left"), new OutputBundle([Number(1)])), new Expr.Call(Name("Right"), new OutputBundle([Number(10)])));
        var elaborated = Elaborate(root, nameResolved: false);
        Assert.Equal(0, elaborated.Detection.DetectorSharedRegionHits);
        Assert.Equal([(Decimal128)2, (Decimal128)20], Evaluate(elaborated.Exposed));
    }

    /// <summary>One body at two depths under one owner: owner positions are relative, so the two are exposure regions apart.</summary>
    [Fact]
    public void OneBodyAtTwoDepths_KeepsItsOwnCapturePositions()
    {
        var shared = Block([Public("Q", Block([], Add(Name("x"), Number(0))))], Name("Q"));
        var owner = Block(
            [Public("Near", shared), Public("Far", Block([Public("Near", shared)], Name("Near")))],
            Add(Add(Name("Near"), Name("Far")), Name("x")));
        var root = Block([Public("Owner", owner)], new Expr.Call(Name("Owner"), new OutputBundle([Number(3)])));
        Assert.Equal([(Decimal128)9], FullFrontEnd(root, nameResolved: false));
        Assert.Equal([(Decimal128)9], FullFrontEnd((Algorithm.User)CloneTree(root), nameResolved: false));
    }

    /// <summary>Genuinely different outermost contexts: twice the regions, never 2^depth, and each side keeps its meaning.</summary>
    [Fact]
    public void OneRelevantDifference_DoublesTheRegions()
    {
        const int Depth = 16;
        var inner = DistinctParents(Depth).Properties.Single(property => property.Name == "Mod").Value;
        var root = Block(
            [
                Public("Left", Block([Public("Leaf", Block([], Number(1))), Public("S", inner)], Name("S"))),
                Public("Right", Block([Public("Leaf", Block([], Number(2))), Public("S", inner)], Name("S"))),
            ],
            Add(Name("Left"), Name("Right")));
        var elaborated = Elaborate(root, nameResolved: false);
        Assert.Equal(2 * (Depth + 1), elaborated.Detection.DetectorSharedRegionExpansions);
        Assert.Equal(2 * Depth, elaborated.Detection.DetectorSharedRegionHits);

        var small = DistinctParents(3).Properties.Single(property => property.Name == "Mod").Value;
        var evaluated = Block(
            [
                Public("Left", Block([Public("Leaf", Block([], Number(1))), Public("S", small)], Name("S"))),
                Public("Right", Block([Public("Leaf", Block([], Number(2))), Public("S", small)], Name("S"))),
            ],
            Add(Name("Left"), Name("Right")));
        Assert.Equal([(Decimal128)24], FullFrontEnd(evaluated, nameResolved: false));
    }

    // ── Occurrences keep their identities ──────────────────────────────────────────────────────────

    /// <summary>
    /// Every occurrence of a body detection served has its own context by member and by <c>Child</c>, facts selecting its own
    /// context, and the declaring identity of its own path: a shared view never merges occurrences.
    /// </summary>
    [Fact]
    public void ServedOccurrences_KeepContextsSelectionsAndIdentities()
    {
        var (exposed, _, _, _, _) = Elaborate(DistinctParents(3), nameResolved: false);
        var publication = exposed.CompletedStructure!;
        var graph = publication.Facts;
        var mod = graph.Member(publication.Entry!, "Mod")!;
        StaticScopeKey Walk(params string[] path) => path.Aggregate(mod, (key, name) => graph.Member(key, name)!);
        var left = Walk("L", "S", "L", "S", "R", "S");
        var right = Walk("R", "S", "R", "S", "R", "S");
        Assert.NotSame(left, right);
        var (leftFacts, rightFacts) = (graph.Facts(left)!, graph.Facts(right)!);
        Assert.Same(leftFacts.Body, rightFacts.Body);
        Assert.Same(left, leftFacts.Open.Target);
        Assert.Same(right, rightFacts.Open.Target);
        Assert.Same(left, leftFacts.Receiver.Target);
        Assert.Same(right, rightFacts.Receiver.Target);
        Assert.NotEqual(leftFacts.Open.Identity, rightFacts.Open.Identity);
        Assert.Same(right, graph.Child(right.Parent!, rightFacts.Body!));
        Assert.Same(left, graph.Child(left.Parent!, leftFacts.Body!));
    }

    /// <summary>
    /// The editor model over an elaborated DAG: one analysis per binding region, so the depth that used to be unreachable does
    /// not turn into per-path scopes here; and a binding difference still gives each side its own analysis.
    /// </summary>
    [Fact]
    public void TheSemanticModel_AnalyzesOneBodyPerBindingRegion()
    {
        var (start, shallow, deep) = (new FrontEndTraversalObservations(), new FrontEndTraversalObservations(), new FrontEndTraversalObservations());
        KatLang.Semantics.SemanticModelBuilder.Build(Elaborate(DistinctParents(6), nameResolved: false).Exposed, start);
        KatLang.Semantics.SemanticModelBuilder.Build(Elaborate(DistinctParents(12), nameResolved: false).Exposed, shallow);
        KatLang.Semantics.SemanticModelBuilder.Build(Elaborate(DistinctParents(24), nameResolved: false).Exposed, deep);
        Assert.Equal(2 * (shallow.SemanticModelAlgorithmVisits - start.SemanticModelAlgorithmVisits),
            deep.SemanticModelAlgorithmVisits - shallow.SemanticModelAlgorithmVisits);

        var shared = Block([], Add(Name("V"), Number(0)));
        var root = Block(
            [
                Public("Left", Block([Public("V", Block([], Number(1))), Public("S", shared)], Name("S"))),
                Public("Right", Block([Public("V", Block([], Number(2))), Public("S", shared)], Name("S"))),
            ],
            Name("Left"), Name("Right"));
        var observations = new FrontEndTraversalObservations();
        KatLang.Semantics.SemanticModelBuilder.Build(Elaborate(root, nameResolved: true).Exposed, observations);
        // The root, both parents with their V, and the shared body under each.
        Assert.Equal(7, observations.SemanticModelAlgorithmVisits);
    }

    /// <summary>A shared body's sibling order under each parent is not observable, and neither is the order of the parents.</summary>
    [Fact]
    public void WrittenOrder_ChangesNothing()
    {
        var shared = Block([], Add(Name("V"), Number(0)));
        Algorithm.User Program(bool reversed)
        {
            var value = Block([], Number(4));
            var left = Block(reversed ? [Public("S", shared), Public("V", value)] : [Public("V", value), Public("S", shared)], Name("S"));
            var right = Block([Public("S", shared)], Name("S"));
            var first = Public("Left", left);
            var second = Public("Right", right);
            return Block(reversed ? [Public("V", Block([], Number(9))), second, first] : [first, second, Public("V", Block([], Number(9)))],
                Name("Left"), Name("Right"));
        }

        Assert.Equal([(Decimal128)4, (Decimal128)9], FullFrontEnd(Program(false), nameResolved: false));
        Assert.Equal([(Decimal128)4, (Decimal128)9], FullFrontEnd(Program(true), nameResolved: false));
    }

    // ── Diagnostics are an occurrence's own ────────────────────────────────────────────────────────

    /// <summary>
    /// A shared body that reports stays once per reach, like its tree: a clean memo may not swallow a report, under an
    /// undeclared name in a closed list or a closed branch alike.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AReportingBody_ReportsAtEveryReach(bool branch)
    {
        Algorithm.User Program(Func<Algorithm> shared) => Block(
            [
                Public("Left", Block([Public("S", shared())], Name("S"))),
                Public("Right", Block([Public("S", shared())], Name("S"))),
            ],
            Number(0));
        Algorithm Body() => branch
            ? new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.LitInt(0), Block([], Name("missing")))])
            : Block([], Name("missing")) with { HasExplicitParameterList = true };
        var one = Body();
        var graph = Program(() => one);
        var tree = Program(Body);
        var fromGraph = new DiagnosticBag();
        var fromTree = new DiagnosticBag();
        ParameterDetector.DetectPrevalidated(graph, diagnostics: fromGraph);
        ParameterDetector.DetectPrevalidated(tree, diagnostics: fromTree);
        Assert.Equal(2, fromTree.ReportedCount);
        Assert.Equal(fromTree.ReportedCount, fromGraph.ReportedCount);
        Assert.Equal(fromTree.Select(diagnostic => diagnostic.Message), fromGraph.Select(diagnostic => diagnostic.Message));
    }

    /// <summary>
    /// An alias valid under one parent and a cycle under the other: the validated region of the first may not hide the second,
    /// though the alias is one object. The node-relative context splits exactly on the head the alias reads.
    /// </summary>
    [Fact]
    public void AnAliasCycleUnderOneParent_IsNotHiddenByTheOther()
    {
        var alias = new Algorithm.Alias(null, [], [], Name("T"));
        var shared = Block([Public("A", alias)], Number(0));
        var cyclic = new Algorithm.Alias(null, [], [], new Expr.DotCall(Name("S"), "A", null));
        Algorithm.User Program(bool cycleFirst)
        {
            var good = Public("Good", Block([Public("T", Block([], Number(1))), Public("S", shared)], Number(0)));
            var bad = Public("Bad", Block([Public("T", cyclic), Public("S", shared)], Number(0)));
            return Block(cycleFirst ? [bad, good] : [good, bad], Number(0));
        }

        Assert.NotNull(AlgorithmValidation.FindFirstPreEvaluationViolation(new Expr.AlgorithmExpr(Program(false))));
        Assert.NotNull(AlgorithmValidation.FindFirstPreEvaluationViolation(new Expr.AlgorithmExpr(Program(true))));

        // Every alias of this cycle is shared with a valid context, so only the node-relative context finds it: X reads Y, which
        // is a number under Good and an alias back to X under Bad, and that alias reads a Good-side name elsewhere.
        var x = new Algorithm.Alias(null, [], [], Name("Y"));
        var body = Block([Public("X", x)], Number(0));
        var back = new Algorithm.Alias(null, [], [], new Expr.DotCall(Name("S"), "X", null));
        var goodFirst = Block(
            [
                Public("Good", Block([Public("Y", Block([], Number(1))), Public("Z", back), Public("S", body)], Number(0))),
                Public("Bad", Block([Public("Y", back), Public("S", body)], Number(0))),
            ],
            Number(0));
        Assert.NotNull(AlgorithmValidation.FindFirstPreEvaluationViolation(new Expr.AlgorithmExpr(goodFirst)));

        // Parents that declare a head only their own aliases read do not split a body that never reads it.
        var depth = 40;
        Algorithm value = Block([], Number(1));
        for (var level = 0; level < depth; level++)
        {
            var next = value;
            value = Block(
                [Public("L", new Algorithm.Alias(null, [], [Public("S", next)], Name("S"))), Public("R", new Algorithm.Alias(null, [], [Public("S", next)], Name("S")))],
                Name("L"));
        }
        var observations = new FrontEndTraversalObservations();
        Assert.Null(AlgorithmValidation.FindFirstPreEvaluationViolation(new Expr.AlgorithmExpr(value), observations));
        Assert.True(observations.WalkerAlgorithmExpansions < 16 * depth, $"walker expansions {observations.WalkerAlgorithmExpansions}");
    }

    // ── Resources: necessary growth is charged, refused and retryable ──────────────────────────────

    /// <summary>
    /// Every level's parents bind a name the leaf reads differently, so the leaf has 2^depth binding tuples: each context reads
    /// other declarations, and evaluation tells them apart. Detection keeps them distinct (exact count at a small depth) and the
    /// operation's ledger refuses the deep graph with the same category as before, leaving the ledger failed and no answer.
    /// </summary>
    private static Algorithm.User EveryLevelBindsDifferently(int depth)
    {
        Expr row = Number(0);
        for (var level = 0; level < depth; level++) row = Add(row, Name($"V{level}"));
        Algorithm value = Block([], row);
        for (var level = depth - 1; level >= 0; level--)
        {
            var left = Block([Public($"V{level}", Block([], Number(1))), Public("S", value)], Name("S"));
            var right = Block([Public($"V{level}", Block([], Number(2))), Public("S", value)], Name("S"));
            value = Block([Public("L", left), Public("R", right)], Add(Name("L"), Name("R")));
        }

        return Block([Public("Mod", value)], Name("Mod"));
    }

    [Fact]
    public void NecessaryContexts_AreKept_AndChargedUntilRefused()
    {
        var small = Elaborate(EveryLevelBindsDifferently(4), nameResolved: false);
        Assert.Equal(0, small.Detection.DetectorSharedRegionHits);
        Assert.Equal(2 + 4 + 8 + 16, small.Detection.DetectorSharedRegionExpansions);
        Assert.Equal([(Decimal128)96], Evaluate(small.Exposed));

        var root = EveryLevelBindsDifferently(16);
        var operation = StaticStructureAdmission.Create(root).Operation;
        Assert.Throws<StaticQueryLimitExceededException>(() => ParameterDetector.DetectPrevalidated(root, structuralOperation: operation));
        Assert.True(operation.Queries.Resources.IsFailed);
        Assert.Throws<StaticQueryLimitExceededException>(() => ParameterDetector.DetectPrevalidated(root));
    }

    [Fact]
    public void BindingFootprint_AdmitsStorageBeforeAllocation_AndChargesEquality()
    {
        var root = Block([], Number(0));
        var (operation, measurement) = StaticStructureAdmission.Create(root);
        var names = new NameSetInterner().With(NameSetInterner.Empty,
            Enumerable.Range(0, 4096).Select(index => $"N{index}"));
        var ledger = operation.Queries.Resources;
        ledger.Reserve(measurement.Limits.MaxStorageUnits - ledger.StorageUnits - 16);
        var before = GC.GetAllocatedBytesForCurrentThread();
        Assert.Throws<StaticQueryLimitExceededException>(() => BindingFootprint.At(operation, operation.Root, names));
        // A coarse guard: the refused 288 KiB array must never have been allocated.
        Assert.True(GC.GetAllocatedBytesForCurrentThread() - before < 64 * 1024);
        Assert.True(ledger.IsFailed);

        var retry = StaticStructureAdmission.Create(root).Operation;
        var narrow = new NameSetInterner().With(NameSetInterner.Empty, ["N"]);
        var first = BindingFootprint.At(retry, retry.Root, narrow)!;
        var second = BindingFootprint.At(retry, retry.Root, narrow)!;
        var work = retry.Queries.Resources.AdapterWork;
        Assert.Equal(first, second);
        Assert.True(retry.Queries.Resources.AdapterWork >= work + 3);
        using var cancellation = new CancellationTokenSource();
        var cancelledOperation = StaticStructureAdmission.Create(root, cancellationToken: cancellation.Token).Operation;
        var cancelledFirst = BindingFootprint.At(cancelledOperation, cancelledOperation.Root, narrow)!;
        var cancelledSecond = BindingFootprint.At(cancelledOperation, cancelledOperation.Root, narrow)!;
        cancellation.Cancel();
        Assert.ThrowsAny<OperationCanceledException>(() => cancelledFirst.Equals(cancelledSecond));
        Assert.True(cancelledOperation.Queries.Resources.IsFailed);
    }

    /// <summary>Cancellation between detected regions fails the operation; the same input then elaborates in full on a new one.</summary>
    [Fact]
    public void CancellationBelowAServedRegion_LeavesTheInputRetryable()
    {
        var root = DistinctParents(8);
        using var cancellation = new CancellationTokenSource();
        var observer = new FrontEndTraversalObservations
        {
            StageObserver = (name, begin) => { if (name == "completed-publication" && begin) cancellation.Cancel(); },
        };
        var error = Assert.ThrowsAny<OperationCanceledException>(
            () => ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(root, observer, cancellationToken: cancellation.Token));
        Assert.Equal(cancellation.Token, error.CancellationToken);

        Assert.Equal([(Decimal128)256], FullFrontEnd(root, nameResolved: true));
    }

    /// <summary>Exposure's own census observes the caller's token before it walks a graph.</summary>
    [Fact]
    public void ExposureObservesCancellationBeforeItsCensus()
    {
        var resolved = Elaborate(DistinctParents(2), nameResolved: false);
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        Assert.ThrowsAny<OperationCanceledException>(() => SharedBodyCensus.Of(resolved.Exposed, cancellation.Token));
    }

    // ── The census ─────────────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// Sharing through an expression reaches the algorithm below it, a shared family its branch bodies, and a deferred region
    /// below a shared body excludes it: its forked context belongs to one occurrence.
    /// </summary>
    [Fact]
    public void TheCensus_FollowsExpressionsAndFamilies_AndExcludesDeferredRegions()
    {
        var below = Block([], Number(1));
        var wrapper = new Expr.AlgorithmExpr(below);
        var census = SharedBodyCensus.Of(Block([], wrapper, wrapper))!;
        Assert.True(census.Holds(below));

        var branch = Block([], Number(2));
        var family = new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.LitInt(0), branch)]);
        census = SharedBodyCensus.Of(Block([Public("A", family), Public("B", family)], Number(0)))!;
        Assert.True(census.Holds(branch));

        Assert.Null(SharedBodyCensus.Of(Block([Public("A", Block([], Number(1)))], Number(0))));
    }
}
