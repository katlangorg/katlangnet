namespace KatLang.Tests;

/// <summary>
/// Mechanical exhaustiveness pins for the hand-written <see cref="Expr"/>
/// traversals of the front-end elaboration passes (H4 Stage 1): ParameterDetector,
/// ImplicitArgumentResolver, PropertyExposureResolver, PropertyDependencyGraphBuilder,
/// and ModuleLoader.
///
/// <para>Each of those passes used to end its expression switches in a silent
/// default (<c>_ =&gt; expr</c> / <c>_ =&gt; null</c> / <c>default: break</c>), so a
/// newly added <see cref="Expr"/> variant would have been silently skipped —
/// changing elaboration semantics with no compile-time error. The switches now
/// enumerate intentional leaves explicitly and fail loudly on an unknown variant.
/// These tests pin the contract mechanically:</para>
/// <list type="number">
///   <item>the per-variant sample table is reflection-complete, so a new variant
///   must first be added here;</item>
///   <item>every current variant dispatches through every targeted traversal
///   without hitting a fail-loud exhaustiveness guard;</item>
///   <item>representative true leaves are preserved by reference (intentionally
///   ignored, not accidentally skipped);</item>
///   <item>representative recursive variants prove their children are actually
///   traversed with each pass's own semantics (free-name detection, implicit-call
///   lifting, exposure classification, sibling ordering, load elaboration).</item>
/// </list>
/// </summary>
public class FrontEndTraversalExhaustivenessTests
{
    // ── Variant samples (reflection-complete) ───────────────────────────────

    private static Algorithm.User EmptyAlgorithm(params Expr[] output)
        => new(Parent: null, Parameters: [], Opens: [], Properties: [], Output: output);

    /// <summary>
    /// One embeddable sample per concrete <see cref="Expr"/> variant. Samples are
    /// immutable records and are freely shared across embedding positions.
    /// </summary>
    private static IReadOnlyDictionary<string, Expr> VariantSamples { get; } = BuildVariantSamples();

    private static IReadOnlyDictionary<string, Expr> BuildVariantSamples()
    {
        var leaf = new Expr.Num(1);
        return new Dictionary<string, Expr>(StringComparer.Ordinal)
        {
            [nameof(Expr.Param)] = new Expr.Param("p"),
            [nameof(Expr.Num)] = leaf,
            [nameof(Expr.StringLiteral)] = new Expr.StringLiteral("s"),
            [nameof(Expr.Unary)] = new Expr.Unary(UnaryOp.Minus, leaf),
            [nameof(Expr.Binary)] = new Expr.Binary(BinaryOp.Add, leaf, leaf),
            [nameof(Expr.Index)] = new Expr.Index(leaf, leaf),
            [nameof(Expr.SequenceConstruct)] = new Expr.SequenceConstruct(leaf, leaf),
            [nameof(Expr.EmptySequence)] = new Expr.EmptySequence(0),
            [nameof(Expr.SequenceSpread)] = new Expr.SequenceSpread(leaf),
            [nameof(Expr.ListLiteral)] = new Expr.ListLiteral([leaf, leaf]),
            [nameof(Expr.Resolve)] = new Expr.Resolve("R"),
            [nameof(Expr.DotCall)] = new Expr.DotCall(leaf, "M", new OutputBundle([leaf])),
            [nameof(Expr.Grace)] = new Expr.Grace(leaf, 1),
            [nameof(Expr.AlgorithmExpr)] = new Expr.AlgorithmExpr(EmptyAlgorithm(leaf)),
            [nameof(Expr.Capture)] = new Expr.Capture([leaf, leaf]),
            [nameof(Expr.Call)] = new Expr.Call(leaf, new OutputBundle([leaf])),
            [nameof(Expr.NativeCall)] = new Expr.NativeCall("Abs", ["x"]),
        };
    }

    private static IReadOnlyList<string> DeclaredExprVariantNames()
        => typeof(Expr).GetNestedTypes()
            .Where(type => !type.IsAbstract && typeof(Expr).IsAssignableFrom(type))
            .Select(type => type.Name)
            .OrderBy(name => name, StringComparer.Ordinal)
            .ToList();

    private static bool HasStructuralExprChildren(Type variantType)
        => variantType
            .GetProperties(System.Reflection.BindingFlags.Public
                | System.Reflection.BindingFlags.Instance
                | System.Reflection.BindingFlags.DeclaredOnly)
            .Any(property =>
                typeof(Expr).IsAssignableFrom(property.PropertyType)
                || typeof(Algorithm).IsAssignableFrom(property.PropertyType)
                || typeof(OutputBundle).IsAssignableFrom(property.PropertyType)
                || typeof(IEnumerable<Expr>).IsAssignableFrom(property.PropertyType));

    /// <summary>
    /// A newly added <see cref="Expr"/> variant must appear in the sample table
    /// before any traversal can be pinned for it — this is the forcing function
    /// that turns "new AST variant" into per-traversal test failures below.
    /// </summary>
    [Fact]
    public void VariantSamples_CoverEveryExprVariant()
    {
        Assert.Equal(
            DeclaredExprVariantNames(),
            VariantSamples.Keys.OrderBy(name => name, StringComparer.Ordinal).ToList());
    }

    /// <summary>
    /// The sample table alone could be updated with a child-free sample for a new
    /// composite variant, allowing every pass to classify it as a leaf while the
    /// reflection-completeness test stayed green. Derive structural recursion from
    /// the actual public AST shape so the leaf set cannot grow that way silently.
    /// </summary>
    [Fact]
    public void StructuralLeafSet_IsDerivedFromTheActualExprShape()
    {
        var structuralLeaves = typeof(Expr).GetNestedTypes()
            .Where(type => !type.IsAbstract && typeof(Expr).IsAssignableFrom(type))
            .Where(type => !HasStructuralExprChildren(type))
            .Select(type => type.Name)
            .OrderBy(name => name, StringComparer.Ordinal)
            .ToList();

        Assert.Equal(
            new[]
            {
                nameof(Expr.EmptySequence),
                nameof(Expr.NativeCall),
                nameof(Expr.Num),
                nameof(Expr.Param),
                nameof(Expr.Resolve),
                nameof(Expr.StringLiteral),
            }.OrderBy(name => name, StringComparer.Ordinal),
            structuralLeaves);
    }

    // ── Traversal drivers ───────────────────────────────────────────────────
    //
    // Each driver embeds one sample in every syntactic position needed to reach
    // ALL of that component's Expr switches. A traversal whose switch lacks an
    // explicit case for the sample's variant now throws its fail-loud
    // exhaustiveness guard, failing the theory with a message naming the
    // traversal and the variant.

    private static Task RunParameterDetectorOpenExpr(Expr sample)
    {
        var root = new Algorithm.User(null, [], [sample], [], OutputBundle.Empty);
        var (detected, _) = ParameterDetector.Detect(root);
        Assert.NotNull(detected);
        return Task.CompletedTask;
    }

    private static Task RunParameterDetectorProcessExpr(Expr sample)
    {
        var root = new Algorithm.User(
            null, [], [new Expr.Capture([sample])], [], OutputBundle.Empty);
        var (detected, _) = ParameterDetector.Detect(root);
        Assert.NotNull(detected);
        return Task.CompletedTask;
    }

    private static Task RunParameterDetectorOutputWalks(Expr sample)
    {
        var (detected, _) = ParameterDetector.Detect(EmptyAlgorithm(sample));
        Assert.NotNull(detected);
        return Task.CompletedTask;
    }

    private static Task RunParameterDetectorConditionalRewrite(Expr sample)
    {
        var conditional = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches: [new CondBranch(new Pattern.Bind("b"), EmptyAlgorithm(sample))]);
        var root = new Algorithm.User(
            null, [], [], [new Property("Cond", conditional)], OutputBundle.Empty);
        var (detected, _) = ParameterDetector.Detect(root);
        Assert.NotNull(detected);
        return Task.CompletedTask;
    }

    private static Task RunParameterDetectorResolveSpanSearch(Expr sample)
    {
        // The sentinel is deliberately after the sample, so locating its
        // diagnostic span must first search through the sample's whole shape.
        var body = EmptyAlgorithm(sample, new Expr.Resolve("zzUndeclaredFreeName"));
        var conditional = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches: [new CondBranch(new Pattern.Bind("b"), body)]);
        var root = new Algorithm.User(
            null, [], [], [new Property("Cond", conditional)], OutputBundle.Empty);
        var (detected, _) = ParameterDetector.Detect(root);
        Assert.NotNull(detected);
        return Task.CompletedTask;
    }

    private static Task RunImplicitOpenExpr(Expr sample)
    {
        var root = new Algorithm.User(null, [], [sample], [], OutputBundle.Empty);
        Assert.NotNull(ImplicitArgumentResolver.Resolve(root));
        return Task.CompletedTask;
    }

    private static Task RunImplicitNestedExpr(Expr sample)
    {
        var root = EmptyAlgorithm(new Expr.Capture([sample]));
        Assert.NotNull(ImplicitArgumentResolver.Resolve(root));
        return Task.CompletedTask;
    }

    private static Task RunImplicitOutputWalks(Expr sample)
    {
        Assert.NotNull(ImplicitArgumentResolver.Resolve(EmptyAlgorithm(sample)));
        return Task.CompletedTask;
    }

    private static Task RunExposureRewrite(Expr sample)
    {
        Assert.NotNull(PropertyExposureResolver.Resolve(EmptyAlgorithm(sample)));
        return Task.CompletedTask;
    }

    private static Task RunDependencyWalks(Expr sample)
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

        Assert.Equal(2, PropertyDependencyGraphBuilder.Build(root).Count);
        return Task.CompletedTask;
    }

    private static async Task RunModuleLoaderSyncWalk(Expr sample)
    {
        var diagnostics = new List<Diagnostic>();
        var loader = new ModuleLoader(
            diagnostics,
            (url, cancellationToken) => ValueTask.FromResult("public X = 1"));

        var elaborated = await loader.ElaborateAsync(EmptyAlgorithm(sample));
        Assert.NotNull(elaborated);
    }

    private static async Task RunModuleLoaderAsyncWalkDispatch(Expr sample)
    {
        // A leaf can never be load-bearing, so normal routing cannot enter the
        // async switch for leaf variants. Invoke this one private dispatch
        // boundary directly to pin all of its explicit leaf arms as well as its
        // recursive arms; recursive load behavior remains covered through the
        // public API by ModuleLoader_AsyncWalkNeverSkipsALoadInsideARecursiveChild.
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

    private static readonly IReadOnlyDictionary<string, Func<Expr, Task>> TraversalDrivers =
        new Dictionary<string, Func<Expr, Task>>(StringComparer.Ordinal)
        {
            ["ParameterDetector.ProcessOpenExpr"] = RunParameterDetectorOpenExpr,
            ["ParameterDetector.RewriteBinderRefs"] = RunParameterDetectorConditionalRewrite,
            ["ParameterDetector.CollectFreeParams"] = RunParameterDetectorOutputWalks,
            ["ParameterDetector.RewriteParams"] = RunParameterDetectorOutputWalks,
            ["ParameterDetector.ProcessExpr"] = RunParameterDetectorProcessExpr,
            ["ParameterDetector.FindResolveSpan"] = RunParameterDetectorResolveSpanSearch,
            ["ImplicitArgumentResolver.ProcessOpenExpr"] = RunImplicitOpenExpr,
            ["ImplicitArgumentResolver.CollectImplicitDeps"] = RunImplicitOutputWalks,
            ["ImplicitArgumentResolver.RewriteImplicitCalls"] = RunImplicitOutputWalks,
            ["ImplicitArgumentResolver.ProcessExprNested"] = RunImplicitNestedExpr,
            ["PropertyExposureResolver.RewriteExpr"] = RunExposureRewrite,
            ["PropertyDependencyGraphBuilder.CollectSummarySeed"] = RunDependencyWalks,
            ["PropertyDependencyGraphBuilder.CollectSiblingDependencyIndices"] = RunDependencyWalks,
            ["ModuleLoader.ProcessExpr"] = RunModuleLoaderSyncWalk,
            ["ModuleLoader.ProcessExprAsync"] = RunModuleLoaderAsyncWalkDispatch,
        };

    [Fact]
    public void TraversalInventory_IsExactlyTheFifteenH4Sites()
        => Assert.Equal(15, TraversalDrivers.Count);

    public static TheoryData<string, string> TraversalVariantMatrix()
    {
        var data = new TheoryData<string, string>();
        foreach (var traversal in TraversalDrivers.Keys.OrderBy(name => name, StringComparer.Ordinal))
        {
            foreach (var variant in VariantSamples.Keys.OrderBy(name => name, StringComparer.Ordinal))
                data.Add(traversal, variant);
        }

        return data;
    }

    /// <summary>
    /// Every current <see cref="Expr"/> variant has an explicit policy in every
    /// targeted front-end traversal: the pass completes without hitting a
    /// fail-loud exhaustiveness guard. (Ordinary diagnostics are fine — several
    /// samples are deliberately illegal in some positions; silence about a
    /// VARIANT is what the guards forbid.)
    /// </summary>
    [Theory]
    [MemberData(nameof(TraversalVariantMatrix))]
    public async Task Traversal_HasAnExplicitPolicyForVariant(string traversal, string variant)
        => await TraversalDrivers[traversal](VariantSamples[variant]);

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

    /// <summary>
    /// Every structurally composite variant has at least one semantic child
    /// embedding below. Together with the per-position theories, this prevents a
    /// newly added composite variant from being represented only by a child-free
    /// sample and silently classified as a leaf by all traversal switches.
    /// </summary>
    [Fact]
    public void RecursiveEmbeddings_CoverEveryStructurallyRecursiveVariant()
    {
        var structurallyRecursive = typeof(Expr).GetNestedTypes()
            .Where(type => !type.IsAbstract && typeof(Expr).IsAssignableFrom(type))
            .Where(HasStructuralExprChildren)
            .Select(type => type.Name)
            .OrderBy(name => name, StringComparer.Ordinal)
            .ToList();
        var embeddedVariants = RecursiveEmbeddings.Values
            .Select(embed => embed(new Expr.Num(1)).GetType().Name)
            .Append(nameof(Expr.AlgorithmExpr))
            .Distinct(StringComparer.Ordinal)
            .OrderBy(name => name, StringComparer.Ordinal)
            .ToList();

        Assert.Equal(structurallyRecursive, embeddedVariants);
    }

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
        => PropertyDependencyGraphBuilder.Build(new Algorithm.User(
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
}
