namespace KatLang.Tests;

/// <summary>
/// Traversal-semantics pins for the hand-written <see cref="Expr"/> walks of the
/// front-end elaboration passes: ParameterDetector, ImplicitArgumentResolver,
/// PropertyExposureResolver, PropertyDependencyGraphBuilder, and ModuleLoader,
/// together with the parser's Grace scan and the semantic model visitor.
///
/// <para>For expression-shaped dispatch, variant COVERAGE is the compiler's job:
/// <see cref="Expr"/> is a closed hierarchy, and the full-hierarchy switch expressions
/// are compiler-exhaustive (a new variant fails the build there).
/// What remains for tests is behavior the compiler cannot see:</para>
/// <list type="number">
///   <item>the four side-effect COLLECTORS, parser scan, semantic visitor, and loader's async twin are switch
///   statements and keep a runtime guard; every current variant is pinned to dispatch
///   through them without tripping it;</item>
///   <item>representative true leaves are preserved by reference (intentionally
///   ignored, not accidentally skipped);</item>
///   <item>every composite variant's children are actually traversed with each pass's
///   own semantics (free-name detection, implicit-call lifting, exposure
///   classification, sibling ordering, load elaboration) — a present-but-childless
///   arm is compiler-exhaustive and still wrong.</item>
/// </list>
/// </summary>
public class FrontEndTraversalTests
{
    private static Algorithm.User EmptyAlgorithm(params Expr[] output)
        => new(Parent: null, Parameters: [], Opens: [], Properties: [], Output: output);

    private static IReadOnlyDictionary<string, Expr> VariantSamples => ExprVariantCatalog.Samples;

    // ── Statement-form traversals: runtime guards pinned per variant ─────────
    //
    // These seven walks are side-effect switch statements (collectors, visitors, and the loader's
    // awaiting twin), the one dispatch shape a closed hierarchy cannot make
    // compiler-exhaustive, so each keeps a fail-loud guard. Every current variant must
    // dispatch through each of them without hitting it; the theory fails with a message
    // naming the traversal and the variant.

    private static Task RunParameterDetectorCollectFreeParams(Expr sample)
    {
        var (detected, _) = ParameterDetector.Detect(EmptyAlgorithm(sample));
        Assert.NotNull(detected);
        return Task.CompletedTask;
    }

    private static Task RunImplicitCollectImplicitDeps(Expr sample)
    {
        Assert.NotNull(ImplicitArgumentResolver.Resolve(EmptyAlgorithm(sample)));
        return Task.CompletedTask;
    }

    private static Task RunImplicitCollectReferenceNames(Expr sample)
    {
        // The free-reference-name walk keys the region memo of every NESTED algorithm, so the
        // sample sits in a property value's output.
        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("Nested", EmptyAlgorithm(sample))],
            Output: OutputBundle.Empty);
        Assert.NotNull(ImplicitArgumentResolver.Resolve(root));
        return Task.CompletedTask;
    }

    private static Task RunDependencyCollectSiblingIndices(Expr sample)
    {
        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties:
            [
                new Property("A", EmptyAlgorithm(sample)),
                new Property("B", EmptyAlgorithm(new Expr.Num(1))),
            ],
            Output: OutputBundle.Empty);
        Assert.Equal(2, PropertyDependencyGraphBuilder.BuildDependencyOrder(root).Count);
        return Task.CompletedTask;
    }

    private static async Task RunModuleLoaderAsyncWalkDispatch(Expr sample)
    {
        // A leaf can never be load-bearing, so normal routing cannot enter the
        // async switch for leaf variants. Invoke this one private dispatch
        // boundary directly to pin all of its explicit leaf arms as well as its
        // recursive arms; recursive load behavior remains covered through the
        // loader's ElaborateAsync boundary by
        // ModuleLoader_AsyncWalkNeverSkipsALoadInsideARecursiveChild.
        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(
            diagnostics,
            (url, cancellationToken) => ValueTask.FromResult("public X = 1"));
        var method = typeof(ModuleLoader).GetMethod(
            "ProcessExprAsync",
            System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic);
        Assert.NotNull(method);
        var contextType = method.GetParameters()[1].ParameterType;
        var context = Enum.Parse(contextType, "TopLevel");
        var pending = Assert.IsType<ValueTask<Expr>>(
            method.Invoke(loader, [sample, context, 0]));

        Assert.NotNull(await pending);
    }

    private static readonly IReadOnlyDictionary<string, Func<Expr, Task>> RuntimeGuardedTraversals =
        new Dictionary<string, Func<Expr, Task>>(StringComparer.Ordinal)
        {
            ["ParameterDetector.CollectFreeParams"] = RunParameterDetectorCollectFreeParams,
            ["ImplicitArgumentResolver.CollectImplicitDeps"] = RunImplicitCollectImplicitDeps,
            ["ImplicitArgumentResolver.CollectReferenceNames"] = RunImplicitCollectReferenceNames,
            ["PropertyDependencyGraphBuilder.CollectSiblingDependencyIndices"] = RunDependencyCollectSiblingIndices,
            ["ModuleLoader.ProcessExprAsync"] = RunModuleLoaderAsyncWalkDispatch,
            ["Parser.ScanPendingForGraceSpan"] = sample =>
            {
                Assert.Null(FindGraceSpan(sample));
                return Task.CompletedTask;
            },
            ["SemanticModelBuilder.VisitExpr"] = sample =>
            {
                Assert.NotNull(Semantics.SemanticModelBuilder.Build(EmptyAlgorithm(sample)));
                return Task.CompletedTask;
            },
        };

    // The parser scan runs before the public parse boundary and must remain iterative;
    // direct invocation also covers the internal join node the parser never produces.
    private static SourceSpan? FindGraceSpan(Expr sample)
    {
        var scan = typeof(Parser).GetMethod("ScanPendingForGraceSpan",
            System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Static)!;
        return (SourceSpan?)scan.Invoke(null, [new Stack<Expr>([sample])]);
    }

    public static TheoryData<string, string> RuntimeGuardedTraversalMatrix()
    {
        var data = new TheoryData<string, string>();
        foreach (var traversal in RuntimeGuardedTraversals.Keys.OrderBy(name => name, StringComparer.Ordinal))
        {
            foreach (var variant in ExprVariantCatalog.DeclaredVariantNames)
                data.Add(traversal, variant);
        }

        return data;
    }

    /// <summary>
    /// Every current <see cref="Expr"/> variant has an explicit policy in every
    /// statement-form front-end traversal: the pass completes without hitting a
    /// fail-loud guard. (Ordinary diagnostics are fine — several samples are
    /// deliberately illegal in some positions; silence about a VARIANT is what the
    /// guards forbid.)
    /// </summary>
    [Theory]
    [MemberData(nameof(RuntimeGuardedTraversalMatrix))]
    public async Task RuntimeGuardedTraversal_HasAnExplicitPolicyForVariant(string traversal, string variant)
        => await RuntimeGuardedTraversals[traversal](VariantSamples[variant]);

    // ── Intentional-leaf pins (preserved by reference, not skipped) ─────────

    public static TheoryData<string> RewritingLeafVariants() => new()
    {
        nameof(Expr.Num),
        nameof(Expr.StringLiteral),
        nameof(Expr.EmptySequence),
        nameof(Expr.NativeCall),
        nameof(Expr.Param),
    };

    [Theory]
    [MemberData(nameof(RewritingLeafVariants))]
    public void ParameterDetector_PreservesLeafOutputRowsByReference(string variant)
    {
        var sample = VariantSamples[variant];
        var (detected, diagnostics) = ParameterDetector.Detect(EmptyAlgorithm(sample));

        Assert.Empty(diagnostics);
        Assert.Same(sample, detected.Output[0]);
    }

    [Theory]
    [MemberData(nameof(RewritingLeafVariants))]
    public void ImplicitArgumentResolver_PreservesLeafOutputRowsByReference(string variant)
    {
        var sample = VariantSamples[variant];
        var resolved = ImplicitArgumentResolver.Resolve(EmptyAlgorithm(sample));

        Assert.Same(sample, resolved.Output[0]);
    }

    [Theory]
    [MemberData(nameof(RewritingLeafVariants))]
    public void PropertyExposureResolver_PreservesLeafOutputRowsByReference(string variant)
    {
        var sample = VariantSamples[variant];
        var resolved = PropertyExposureResolver.Resolve(EmptyAlgorithm(sample));

        Assert.Same(sample, resolved.Output[0]);
    }

    [Theory]
    [MemberData(nameof(RewritingLeafVariants))]
    public async Task ModuleLoader_PreservesLeafOutputRowsByReference(string variant)
    {
        var sample = VariantSamples[variant];
        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(
            diagnostics,
            (url, cancellationToken) => ValueTask.FromResult("public X = 1"));

        var elaborated = await loader.ElaborateAsync(EmptyAlgorithm(sample));

        Assert.Empty(diagnostics);
        Assert.Same(sample, elaborated.Output[0]);
    }

    /// <summary>
    /// A bound Resolve is an intentional non-rewrite in the detector: it stays a
    /// lexical reference (same instance), never a parameter.
    /// </summary>
    [Fact]
    public void ParameterDetector_KeepsABoundResolveAsALexicalReference()
    {
        var boundReference = new Expr.Resolve("R");
        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("R", EmptyAlgorithm(new Expr.Num(7)))],
            Output: new OutputBundle([boundReference]));

        var (detected, diagnostics) = ParameterDetector.Detect(root);

        Assert.Empty(diagnostics);
        Assert.Empty(detected.Params);
        Assert.Same(boundReference, detected.Output[0]);
    }

    // ── ParameterDetector: recursive child positions detect free names ──────

    [Fact]
    public void ParameterDetector_CallRewritePreservesArgumentBeforeCalleeDiagnostics()
    {
        // Rewriting historically visits the argument bundle before the callee. Moving
        // this arm into a switch expression must not reverse observable diagnostics.
        var diagnostics = SourceProvenance.ExpectFrontEndError("F(x) = x\nK(x) = ~F(~x)\nK(1)");

        Assert.Equal(2, diagnostics.Count);
        Assert.All(diagnostics, d => Assert.Equal(DiagnosticCode.InvalidGraceMarker, d.Code));
        Assert.Equal(new SourceSpan(2, 11, 2, 12), diagnostics[0].Span);
        Assert.Equal(new SourceSpan(2, 8, 2, 9), diagnostics[1].Span);
    }

    private static IReadOnlyDictionary<string, Func<Expr, Expr>> RecursiveEmbeddings { get; } =
        new Dictionary<string, Func<Expr, Expr>>(StringComparer.Ordinal)
        {
            ["Unary.Operand"] = child => new Expr.Unary(UnaryOp.Minus, child),
            ["Binary.Left"] = child => new Expr.Binary(BinaryOp.Add, child, new Expr.Num(1)),
            ["Binary.Right"] = child => new Expr.Binary(BinaryOp.Add, new Expr.Num(1), child),
            ["Index.Target"] = child => new Expr.Index(child, new Expr.Num(0)),
            ["Index.Selector"] = child => new Expr.Index(new Expr.Num(1), child),
            ["SequenceConstruct.Left"] = child => new Expr.SequenceConstruct(child, new Expr.Num(1)),
            ["SequenceConstruct.Right"] = child => new Expr.SequenceConstruct(new Expr.Num(1), child),
            ["SequenceSpread.Operand"] = child => new Expr.SequenceSpread(child),
            ["ListLiteral.Item"] = child => new Expr.ListLiteral([child]),
            ["Capture.Row"] = child => new Expr.Capture([child]),
            ["Call.Function"] = child => new Expr.Call(child, OutputBundle.Empty),
            // The callee name is deliberately distinct from the probe name so a
            // detector assertion on the probe proves ARGUMENT descent, not a
            // coincidental function-position occurrence.
            ["Call.Argument"] = child => new Expr.Call(new Expr.Resolve("callee9"), new OutputBundle([child])),
            ["DotCall.Target"] = child => new Expr.DotCall(child, "M", new OutputBundle([new Expr.Num(1)])),
            ["DotCall.Argument"] = child => new Expr.DotCall(new Expr.Num(1), "M", new OutputBundle([child])),
            ["Grace.Inner"] = child => new Expr.Grace(child, 1),
        };

    public static TheoryData<string> RecursiveEmbeddingPositions()
    {
        var data = new TheoryData<string>();
        foreach (var position in RecursiveEmbeddings.Keys.OrderBy(name => name, StringComparer.Ordinal))
            data.Add(position);
        return data;
    }

    [Theory]
    [MemberData(nameof(RecursiveEmbeddingPositions))]
    public void SemanticModel_VisitsNamesInsideRecursiveChildren(string position)
    {
        var span = new SourceSpan(1, 1, 1, 2);
        var embedded = RecursiveEmbeddings[position](new Expr.Resolve("q") { Span = span });
        var model = Semantics.SemanticModelBuilder.Build(EmptyAlgorithm(embedded));

        Assert.Contains(model.IdentifierOccurrences, occurrence => occurrence.Name == "q" && occurrence.Span == span);
    }

    [Theory]
    [MemberData(nameof(RecursiveEmbeddingPositions))]
    public void Parser_GraceScanVisitsItsChildrenAndHonorsGraceBoundaries(string position)
    {
        var span = new SourceSpan(1, 1, 1, 3);
        var embedded = RecursiveEmbeddings[position](new Expr.Grace(new Expr.Resolve("q"), 1) { Span = span });

        // Even a spanless written Grace is a match boundary: it does not search Inner.
        Assert.Equal(position == "Grace.Inner" ? null : span, FindGraceSpan(embedded));
    }

    [Fact]
    public void Parser_GraceScanVisitsBlockRowsAndStoredDotFallback()
    {
        var span = new SourceSpan(1, 1, 1, 3);
        var grace = new Expr.Grace(new Expr.Resolve("q"), 1) { Span = span };
        Assert.Equal(span, FindGraceSpan(new Expr.AlgorithmExpr(EmptyAlgorithm(grace))));
        Assert.Equal(span, FindGraceSpan(new Expr.DotCall(new Expr.Num(1), "q") { LexicalFallback = grace }));
    }

    /// <summary>
    /// Every structurally composite variant has at least one semantic child
    /// embedding below, so the per-position theories cover a newly added composite
    /// variant's children — the property the compiler's exhaustiveness proof does not
    /// reach. <see cref="Expr.AlgorithmExpr"/> is the one ownership boundary and is
    /// pinned separately (<see cref="ParameterDetector_LeavesAlgorithmExprNamesToTheNestedScope"/>).
    /// </summary>
    [Fact]
    public void RecursiveEmbeddings_CoverEveryStructurallyRecursiveVariant()
        => ExprVariantCatalog.AssertCoversEveryCompositeVariant(
            RecursiveEmbeddings.Values.Select(embed => embed(new Expr.Num(1)).GetType().Name),
            $"{nameof(FrontEndTraversalTests)}.{nameof(RecursiveEmbeddings)}",
            nameof(Expr.AlgorithmExpr));

    private sealed class ParamOccurrenceCollector : AstWalker
    {
        public HashSet<string> ParamNames { get; } = [];

        protected override void VisitParameterIdentifier(Expr.Param expr)
            => ParamNames.Add(expr.Name);
    }

    /// <summary>
    /// A free identifier inside every recursive child position is detected as an
    /// implicit parameter AND its occurrence is rewritten to <see cref="Expr.Param"/> —
    /// the collection and rewrite walks both descended into the child.
    /// </summary>
    [Theory]
    [MemberData(nameof(RecursiveEmbeddingPositions))]
    public void ParameterDetector_DetectsFreeNamesInsideRecursiveChildren(string position)
    {
        var embedded = RecursiveEmbeddings[position](new Expr.Resolve("q"));
        var (detected, _) = ParameterDetector.Detect(EmptyAlgorithm(embedded));

        Assert.Contains("q", detected.Params);

        var collector = new ParamOccurrenceCollector();
        collector.VisitAlgorithm(detected);
        Assert.Contains("q", collector.ParamNames);
    }

    /// <summary>
    /// The one intentional ownership boundary: an <see cref="Expr.AlgorithmExpr"/>
    /// owns its names, so a free identifier inside it becomes the NESTED
    /// algorithm's parameter, never the enclosing one's.
    /// </summary>
    [Fact]
    public void ParameterDetector_LeavesAlgorithmExprNamesToTheNestedScope()
    {
        var embedded = new Expr.AlgorithmExpr(EmptyAlgorithm(new Expr.Resolve("q")));
        var (detected, _) = ParameterDetector.Detect(EmptyAlgorithm(embedded));

        Assert.Empty(detected.Params);
        var nested = Assert.IsType<Expr.AlgorithmExpr>(detected.Output[0]);
        Assert.Contains("q", nested.Algorithm.Params);
    }

    // ── ImplicitArgumentResolver: recursive child positions lift ────────────

    public static TheoryData<string, string> LiftingPositions() => new()
    {
        { "Unary.Operand", "F(x) = x + 1\n-F" },
        { "Binary.Left", "F(x) = x + 1\nF + 2" },
        { "Binary.Right", "F(x) = x + 1\n2 + F" },
        { "Index.Target", "F(x) = x + 1\nF:0" },
        { "Index.Selector", "F(x) = x + 1\n(1, 2):F" },
        { "SequenceSpread.Operand", "F(x) = x + 1\nF*" },
        { "ListLiteral.Item", "F(x) = x + 1\n[F]" },
    };

    private sealed class LiftedCallFinder : AstWalker
    {
        private readonly string _calleeName;

        public LiftedCallFinder(string calleeName) => _calleeName = calleeName;

        public bool FoundLiftedCall { get; private set; }

        public override void VisitExpr(Expr expr)
        {
            if (expr is Expr.Call(Expr.Resolve(var name), _) && name == _calleeName)
                FoundLiftedCall = true;
            base.VisitExpr(expr);
        }
    }

    /// <summary>
    /// A bare reference to a param-bearing property inside each recursive value
    /// position is rewritten to an explicit implicit-argument call — the
    /// resolver's rewrite walk descended into the child.
    /// </summary>
    [Theory]
    [MemberData(nameof(LiftingPositions))]
    public void ImplicitArgumentResolver_LiftsBareReferencesInsideRecursiveChildren(string position, string source)
    {
        _ = position;
        var root = SourceProvenance.ParseValid(source).Root;

        var finder = new LiftedCallFinder("F");
        finder.VisitAlgorithm(root);

        Assert.True(finder.FoundLiftedCall, $"expected a lifted F(...) call in: {source}");
        Assert.Contains("x", root.Params);
    }

    /// <summary>
    /// Capture rows intentionally do NOT lift (grouping suppresses callable
    /// identity), and a neutral call-argument slot still descends into a nested
    /// brace algorithm whose own rows DO lift — the two documented transparent
    /// context behaviors of <c>ProcessExprNested</c>.
    /// </summary>
    [Fact]
    public void ImplicitArgumentResolver_CaptureRowsStayBareWhileNestedAlgorithmsLift()
    {
        var captureRoot = SourceProvenance.ParseValid("F(x) = x + 1\n(F, 1)").Root;
        var captureRow = Assert.IsType<Expr.Capture>(captureRoot.Output[0]);
        Assert.IsType<Expr.Resolve>(captureRow.Body[0]);

        var nestedRoot = SourceProvenance.ParseValid("F(x) = x + 1\nG(a) = a\nG({-F})").Root;
        var finder = new LiftedCallFinder("F");
        finder.VisitAlgorithm(nestedRoot);
        Assert.True(finder.FoundLiftedCall, "expected the brace-argument algorithm's row to lift F");
    }

    // ── PropertyExposureResolver: nested algorithms in child positions ──────

    public static TheoryData<string, string> ExposurePositions() => new()
    {
        { "ListLiteral.Item", "G(a) = [{\nH = a\nH\n}]" },
        { "Unary.Operand", "G(a) = -{\nH = a\nH\n}" },
        { "Call.Argument", "K(x) = x\nG(a) = K({\nH = a\nH\n})" },
        { "Capture.Row", "G(a) = ({\nH = a\nH\n}, 1)" },
    };

    private sealed class PropertyExposureFinder : AstWalker
    {
        private readonly string _propertyName;

        public PropertyExposureFinder(string propertyName) => _propertyName = propertyName;

        public PropertyExposure? FoundExposure { get; private set; }

        protected override void VisitProperty(Property property)
        {
            if (property.Name == _propertyName)
                FoundExposure = property.Exposure;
            base.VisitProperty(property);
        }
    }

    /// <summary>
    /// A nested brace algorithm inside each recursive child position gets its
    /// properties exposure-classified: a property capturing an ancestor-owned
    /// parameter is marked local-only, which requires the exposure rewrite walk
    /// to have descended through the position.
    /// </summary>
    [Theory]
    [MemberData(nameof(ExposurePositions))]
    public void PropertyExposureResolver_ClassifiesPropertiesInsideRecursiveChildren(string position, string source)
    {
        _ = position;
        var root = SourceProvenance.ParseValid(source).Root;

        var finder = new PropertyExposureFinder("H");
        finder.VisitAlgorithm(root);

        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, finder.FoundExposure);
    }

    // ── PropertyDependencyGraphBuilder: sibling refs in child positions ─────

    public static TheoryData<string> SiblingDependencyPositions()
    {
        var data = new TheoryData<string>();
        foreach (var position in new[]
        {
            "Unary.Operand",
            "Binary.Left",
            "Binary.Right",
            "Index.Target",
            "Index.Selector",
            "SequenceConstruct.Left",
            "SequenceConstruct.Right",
            "SequenceSpread.Operand",
            "ListLiteral.Item",
            "Grace.Inner",
        })
        {
            data.Add(position);
        }

        return data;
    }

    private static PropertyDependencyGraph BuildSiblingGraph(Expr referencingBody)
        => PropertyDependencyGraphBuilder.BuildDependencyOrder(new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties:
            [
                new Property("A", EmptyAlgorithm(referencingBody)),
                new Property("B", EmptyAlgorithm(new Expr.Num(1))),
            ],
            Output: OutputBundle.Empty));

    /// <summary>
    /// A sibling reference inside each recursive value position produces a
    /// processing-order dependency edge — the dependency walk descended into
    /// the child.
    /// </summary>
    [Theory]
    [MemberData(nameof(SiblingDependencyPositions))]
    public void PropertyDependencyGraphBuilder_FindsSiblingReferencesInsideRecursiveChildren(string position)
    {
        var embedded = RecursiveEmbeddings[position](new Expr.Resolve("B"));
        var graph = BuildSiblingGraph(embedded);

        Assert.Contains(1, graph[0].SiblingDependencyIndices);
    }

    /// <summary>
    /// The split SUMMARY channel independently descends through every recursive value
    /// position. This is the semantic mutation guard for misclassifying one explicit arm as
    /// a leaf: the compiler catches a MISSING arm of the summary switch expression, while
    /// this test catches a present-but-non-recursive arm.
    /// </summary>
    [Theory]
    [MemberData(nameof(SiblingDependencyPositions))]
    public void PropertyDependencyGraphBuilder_FindsSummaryNamesInsideRecursiveChildren(string position)
    {
        var embedded = RecursiveEmbeddings[position](new Expr.Param("captured"));
        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("A", EmptyAlgorithm(embedded))],
            Output: OutputBundle.Empty);

        var graph = PropertyDependencyGraphBuilder.BuildSummaries(root);

        Assert.Equal(["captured"], graph[0].RequiredAncestorOwnedParameterNames);
    }

    /// <summary>
    /// The two documented negative positions stay negative: a CALLED sibling
    /// (call-function position, and a dot-call-with-arguments target) is not a
    /// processing-order dependency.
    /// </summary>
    [Fact]
    public void PropertyDependencyGraphBuilder_KeepsCallPositionsOutOfSiblingOrdering()
    {
        var calledSibling = BuildSiblingGraph(new Expr.Call(new Expr.Resolve("B"), OutputBundle.Empty));
        Assert.DoesNotContain(1, calledSibling[0].SiblingDependencyIndices);

        var dotCalledSibling = BuildSiblingGraph(
            new Expr.DotCall(new Expr.Resolve("B"), "M", new OutputBundle([new Expr.Num(1)])));
        Assert.DoesNotContain(1, dotCalledSibling[0].SiblingDependencyIndices);
    }

    // ── ModuleLoader: loads inside recursive child positions are never skipped ──

    private sealed class UnresolvedLoadCounter : AstWalker
    {
        public int UnresolvedLoads { get; private set; }

        public override void VisitExpr(Expr expr)
        {
            if (expr.TryGetUnresolvedLoadArguments(out _))
                UnresolvedLoads++;
            base.VisitExpr(expr);
        }
    }

    private sealed class SplicedModuleFinder : AstWalker
    {
        public bool FoundModuleProperty { get; private set; }

        public override void VisitAlgorithm(Algorithm algorithm)
        {
            if (algorithm.Properties.Any(property => property.Name == "X"))
                FoundModuleProperty = true;
            base.VisitAlgorithm(algorithm);
        }
    }

    private static Expr LoadCall()
        => new Expr.Call(
            new Expr.Resolve("load"),
            new OutputBundle([new Expr.StringLiteral("https://katlang.org/module.kat")]));

    /// <summary>
    /// Load-bearing positions for the loader's ASYNC twin walk: whether the
    /// position is a runtime-expression context (where the load must be
    /// REPORTED, proving it was seen) or a definition context (where the load
    /// must be ELABORATED into the stub module).
    /// </summary>
    public static TheoryData<string, bool> LoadBearingPositions() => new()
    {
        // Runtime-expression child contexts: the load is reported, never skipped.
        { "Unary.Operand", true },
        { "Binary.Left", true },
        { "Binary.Right", true },
        { "Index.Target", true },
        { "Index.Selector", true },
        { "Call.Function", true },
        { "Call.Argument", true },
        { "DotCall.Target", true },
        { "DotCall.Argument", true },
        // Context-inheriting children inside a property definition: the load
        // elaborates to the stub module.
        { "SequenceConstruct.Left", false },
        { "SequenceConstruct.Right", false },
        { "SequenceSpread.Operand", false },
        { "ListLiteral.Item", false },
        { "Capture.Row", false },
        { "Grace.Inner", false },
        { "DotCall.ArglessTarget", false },
        { "AlgorithmExpr.OutputRow", false },
    };

    private static Expr EmbedLoad(string position)
        => position switch
        {
            "Call.Function" => new Expr.Call(LoadCall(), OutputBundle.Empty),
            "DotCall.ArglessTarget" => new Expr.DotCall(LoadCall(), "M"),
            "AlgorithmExpr.OutputRow" => new Expr.AlgorithmExpr(EmptyAlgorithm(LoadCall())),
            _ => RecursiveEmbeddings[position](LoadCall()),
        };

    /// <summary>
    /// A load call inside every recursive child position is SEEN by the async
    /// twin walk: it either elaborates into the stub module or reports the
    /// runtime-position diagnostic, and no unresolved load ever survives —
    /// a silently skipped variant would leave the load call in the tree.
    /// </summary>
    [Theory]
    [MemberData(nameof(LoadBearingPositions))]
    public async Task ModuleLoader_AsyncWalkNeverSkipsALoadInsideARecursiveChild(string position, bool expectsRuntimePositionError)
    {
        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(
            diagnostics,
            (url, cancellationToken) => ValueTask.FromResult("public X = 1"));
        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("Mod", EmptyAlgorithm(EmbedLoad(position)))],
            Output: OutputBundle.Empty);

        var elaborated = await loader.ElaborateAsync(root);

        var loadCounter = new UnresolvedLoadCounter();
        loadCounter.VisitAlgorithm(elaborated);
        Assert.Equal(0, loadCounter.UnresolvedLoads);

        if (expectsRuntimePositionError)
        {
            Assert.Contains(diagnostics, d => d.Message.Contains("load not allowed in runtime expression"));
        }
        else
        {
            Assert.Empty(diagnostics);
            var moduleFinder = new SplicedModuleFinder();
            moduleFinder.VisitAlgorithm(elaborated);
            Assert.True(moduleFinder.FoundModuleProperty, $"expected the stub module to be spliced at {position}");
        }
    }

    // ── ModuleLoader: clause-family positions — shared opens eager, branch bodies deferred ──

    /// <summary>
    /// Clause-family positions for the loader walks (B2c). A family's OWN open list (host
    /// trees) is shared by every alternative and is elaborated eagerly. Everything under an
    /// alternative branch body — its opens, a property value, an output row, a runtime
    /// expression, an inner family, a family in expression position — is a deferred module
    /// region: the walks never descend into it, so no download, no diagnostic, and the load
    /// directive stays inside the region INTENTIONALLY (the post-elaboration guard knows it
    /// is deferred, not forgotten) until evaluation selects the branch.
    /// </summary>
    public static TheoryData<string, bool> ClauseFamilyLoadBearingPositions() => new()
    {
        { "Conditional.Opens", false },
        { "Branch.Opens", true },
        { "Branch.PropertyValue", true },
        { "Branch.OutputRow", true },
        { "Branch.OutputRow.RuntimeExpr", true },
        { "NestedConditional.Branch.Opens", true },
        { "ExpressionPositionConditional.Branch.Opens", true },
    };

    private static Algorithm EmbedClauseFamilyLoad(string position)
    {
        static Algorithm.Conditional Family(IReadOnlyList<Expr> opens, Algorithm body)
            => new(null, opens, [new CondBranch(new Pattern.LitInt(0), body)]);
        return position switch
        {
            "Conditional.Opens" => Family([LoadCall()], EmptyAlgorithm(new Expr.Num(1))),
            "Branch.Opens" => Family([], EmptyAlgorithm(new Expr.Num(1)) with { Opens = [LoadCall()] }),
            "Branch.PropertyValue" => Family([], EmptyAlgorithm(new Expr.Num(1)) with
            {
                Properties = [new Property("Lib", EmptyAlgorithm(LoadCall()))],
            }),
            "Branch.OutputRow" => Family([], EmptyAlgorithm(LoadCall())),
            "Branch.OutputRow.RuntimeExpr" => Family([], EmptyAlgorithm(new Expr.Unary(UnaryOp.Minus, LoadCall()))),
            "NestedConditional.Branch.Opens" => Family([], EmptyAlgorithm(new Expr.Num(1)) with
            {
                Properties =
                [
                    new Property("Inner", Family([], EmptyAlgorithm(new Expr.Num(1)) with { Opens = [LoadCall()] })),
                ],
            }),
            "ExpressionPositionConditional.Branch.Opens" => EmptyAlgorithm(
                new Expr.AlgorithmExpr(Family([], EmptyAlgorithm(new Expr.Num(1)) with { Opens = [LoadCall()] }))),
            _ => throw new ArgumentOutOfRangeException(nameof(position)),
        };
    }

    [Theory]
    [MemberData(nameof(ClauseFamilyLoadBearingPositions))]
    public async Task ModuleLoader_DefersEveryClauseFamilyBranchPosition(string position, bool deferred)
    {
        var downloads = 0;
        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(
            diagnostics,
            (url, cancellationToken) =>
            {
                downloads++;
                return ValueTask.FromResult("public X = 1");
            });
        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("Mod", EmbedClauseFamilyLoad(position))],
            Output: OutputBundle.Empty);

        var elaborated = await loader.ElaborateAsync(root);

        Assert.Empty(diagnostics);
        var loadCounter = new UnresolvedLoadCounter();
        loadCounter.VisitAlgorithm(elaborated);
        if (deferred)
        {
            Assert.Equal(0, downloads);
            Assert.Equal(1, loader.DeferredRegionCount);
            // The directive survives inside the deferred region by design; the guard
            // distinguishes that from an unresolved load the pipeline forgot.
            Assert.Equal(1, loadCounter.UnresolvedLoads);
            Assert.False(LoadElaborationGuard.TryFindFirstUnresolvedLoad(elaborated, out _));
        }
        else
        {
            Assert.Equal(1, downloads);
            Assert.Equal(0, loader.DeferredRegionCount);
            Assert.Equal(0, loadCounter.UnresolvedLoads);
            var moduleFinder = new SplicedModuleFinder();
            moduleFinder.VisitAlgorithm(elaborated);
            Assert.True(moduleFinder.FoundModuleProperty, $"expected the stub module to be spliced at {position}");
        }
    }
}
