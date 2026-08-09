namespace KatLang.Tests;

/// <summary>
/// Containment guards for the internal AST node <see cref="Expr.SequenceConstruct"/>.
///
/// Provenance (July 2026 audit, docs/design/sequence-boundary-audit-2026-07.md §7):
/// the node is the retained encoding of the removed binary spread-join (a
/// spread directly joined to a right operand, from the era before a spread
/// expression became its own expression-list slot — today `A*, B`). The parser
/// and all current production transformations have ZERO ORIGIN SITES for it —
/// written parentheses parse to <see cref="Expr.Block"/> /
/// <see cref="Expr.EmptySequence"/>, and the elaboration visitors only
/// REBUILD an existing node (they cannot introduce one into an AST that did
/// not already contain it). The public AST API and Lean's `sequenceConstruct`
/// helper remain intentional EXTERNAL origin mechanisms. Its value evaluation
/// (EvalSequenceConstructCounted) DROPS `()` leaves, which written sequence
/// syntax never does, so routing surface syntax through it would silently
/// violate the visible-empty rule.
///
/// These tests make that hazard fail loudly:
/// 1. surface syntax must never parse or elaborate to a SequenceConstruct
///    (per-form pins plus a sweep over the whole semantic-explorer corpus;
///    Parser.Parse runs the full FrontEndPipeline, so the scanned ASTs are
///    post-elaboration — the sweep covers the transformation passes too);
/// 2. the surface forms must keep their intended AST family;
/// 3. production visitors preserve an externally originated node (rebuild,
///    never drop or duplicate);
/// 4. the node's own semantics are pinned directly (Lean twins live in
///    lean/SemanticExplorerCases.lean internal-node section and CoreTests).
/// </summary>
public class SequenceConstructContainmentTests
{
    // ----- scanner --------------------------------------------------------------

    private sealed class SequenceConstructScanner : AstWalker
    {
        public int Found { get; private set; }

        public override void VisitExpr(Expr expr)
        {
            if (expr is Expr.SequenceConstruct)
                Found++;
            base.VisitExpr(expr);
        }
    }

    private static int CountSequenceConstructNodes(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, $"expected parseable source, got errors for: {source}");
        var scanner = new SequenceConstructScanner();
        scanner.VisitAlgorithm(parsed.Root);
        return scanner.Found;
    }

    // ----- 1. parser unreachability ---------------------------------------------

    public static TheoryData<string> SurfaceSequenceForms => new()
    {
        "()",
        "(1)",
        "(1, 2)",
        "((), 1)",
        "(1, ())",
        "((1, 2), 3)",
        "A = (1, 2)\n(A*)",
        "A = (1, 2)\n(A*, 99)",
        "A = (1, 2)\nA* 99",
        "A = (1, 2)\nA*, 99",
        "1, 2",
        "1 2 3",
        "P = (), 99\nP",
        "take(((), ()), 2)",
        "f(a, b) = a\nf(1, 2)",
        "x, y = (1, 2)*\nx",
        "F(*a) = a\nF((1, 2)*, 3)",
        "(1*, (), 2*)",
        // Exact list literals are a genuine surface node (Expr.ListLiteral),
        // never a route into the internal join node.
        "[]",
        "[1]",
        "[1, 2, 3]",
        "[[1, 2], [3, 4]]",
        "[()]",
        "A = (1, 2)\n[A*, 99]",
        "A = [1, 2]\n(A*, 99)",
        "x, y = [1, 2]\nx",
        "F(*a) = a\nF([1, 2]*, 3)",
    };

    [Theory]
    [MemberData(nameof(SurfaceSequenceForms))]
    public void SurfaceSequenceSyntax_NeverParsesToSequenceConstruct(string source)
        => Assert.Equal(0, CountSequenceConstructNodes(source));

    [Fact]
    public void EntireSemanticExplorerCorpus_ParsesWithoutSequenceConstruct()
    {
        foreach (var explorerCase in SemanticExplorerCorpus.AllCases())
        {
            var parsed = Parser.Parse(explorerCase.Source);
            if (parsed.HasErrors)
                continue; // deliberate parse-error cases

            var scanner = new SequenceConstructScanner();
            scanner.VisitAlgorithm(parsed.Root);
            Assert.True(scanner.Found == 0,
                $"corpus case '{explorerCase.Id}' parsed to {scanner.Found} Expr.SequenceConstruct node(s); " +
                "surface syntax must never route through the internal node " +
                "(it drops () leaves, violating visible-empty semantics).");
        }
    }

    /// <summary>
    /// Production visitors are REBUILD sites, not origin sites: given an
    /// externally originated <see cref="Expr.SequenceConstruct"/> (public AST
    /// API), an elaboration pass preserves exactly the node it was handed —
    /// it neither drops it nor introduces additional ones.
    /// </summary>
    [Fact]
    public void ProductionVisitor_PreservesExternallyOriginatedNode()
    {
        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [],
            Output: [Sc(N(1), N(2))]);

        var (detected, diagnostics) = ParameterDetector.Detect(root);
        Assert.DoesNotContain(diagnostics, d => d.Severity == DiagnosticSeverity.Error);

        var scanner = new SequenceConstructScanner();
        scanner.VisitAlgorithm(detected);
        Assert.Equal(1, scanner.Found);
    }

    // ----- 2. surface forms keep their intended AST family ----------------------

    [Fact]
    public void ParenthesizedSequenceSyntax_UsesExpectedNodes()
    {
        static Expr SingleRootOutput(string source)
        {
            var root = (Algorithm.User)SourceProvenance.ParseValid(source).Root;
            return Assert.Single(root.Output);
        }

        // `()` is the empty-sequence literal node.
        Assert.IsType<Expr.EmptySequence>(SingleRootOutput("()"));

        // Scalar parentheses stay transparent.
        var one = Assert.IsType<Expr.Num>(SingleRootOutput("(1)"));
        Assert.Equal(1m, one.Value);

        // A parenthesized list is a zero-parameter block whose output slots are
        // the items; a `()` item stays an EmptySequence slot.
        var pair = Assert.IsType<Expr.Block>(SingleRootOutput("((), 1)"));
        var pairAlg = Assert.IsType<Algorithm.User>(pair.Algorithm);
        Assert.Collection(pairAlg.Output,
            item => Assert.IsType<Expr.EmptySequence>(item),
            item => Assert.Equal(1m, Assert.IsType<Expr.Num>(item).Value));

        // A spread item inside parentheses is a SequenceSpread slot in the block.
        var spread = Assert.IsType<Expr.Block>(SingleRootOutput("A = (1, 2)\n(A*, 99)"));
        var spreadAlg = Assert.IsType<Algorithm.User>(spread.Algorithm);
        Assert.Collection(spreadAlg.Output,
            item => Assert.IsType<Expr.SequenceSpread>(item),
            item => Assert.Equal(99m, Assert.IsType<Expr.Num>(item).Value));
    }

    // ----- 3. direct internal-node semantics (pinned) ---------------------------
    //
    // NOTE: SequenceConstruct(Left, Right) is a binary node — spines of zero or
    // one leaf are not constructible, so the smallest internal form has two
    // leaves. Neutral encoding: S[...] = sequence value, n = root emitted count.

    private static Expr N(int n) => new Expr.Num(n);
    private static Expr E() => new Expr.EmptySequence(0);

    private static Expr Blk(params Expr[] outputs) => new Expr.Block(new Algorithm.User(
        Parent: null, Parameters: [], Opens: [], Properties: [], Output: outputs));

    private static Expr Sc(params Expr[] leaves)
        => leaves.Aggregate((l, r) => new Expr.SequenceConstruct(l, r));

    public static TheoryData<string, string> DirectNodeCases => new()
    {
        // internal node                        pinned observation (root value position)
        { "sc[(), 1]", "ok raw=1 n=1" },        // surface ((), 1) keeps S[S[], 1]
        { "sc[1, ()]", "ok raw=1 n=1" },        // surface (1, ()) keeps S[1, S[]]
        { "sc[(), ()]", "ok raw=S[] n=1" },     // surface ((), ()) keeps S[S[], S[]]
        { "sc[(1,2), ()]", "ok raw=S[1, 2] n=1" },
        { "sc[(), (1,2)]", "ok raw=S[1, 2] n=1" },
        { "sc[1, 2]", "ok raw=S[1, 2] n=1" },   // agrees with surface (1, 2)
        { "sc[(1,2), (3,4)]", "ok raw=S[S[1, 2], S[3, 4]] n=1" },
        { "sc[(1,2)*, 3]", "ok raw=S[1, 2, 3] n=1" },
    };

    private static readonly IReadOnlyDictionary<string, Func<Expr>> DirectNodeBuilders =
        new Dictionary<string, Func<Expr>>
        {
            ["sc[(), 1]"] = () => Sc(E(), N(1)),
            ["sc[1, ()]"] = () => Sc(N(1), E()),
            ["sc[(), ()]"] = () => Sc(E(), E()),
            ["sc[(1,2), ()]"] = () => Sc(Blk(N(1), N(2)), E()),
            ["sc[(), (1,2)]"] = () => Sc(E(), Blk(N(1), N(2))),
            ["sc[1, 2]"] = () => Sc(N(1), N(2)),
            ["sc[(1,2), (3,4)]"] = () => Sc(Blk(N(1), N(2)), Blk(N(3), N(4))),
            ["sc[(1,2)*, 3]"] = () => Sc(new Expr.SequenceSpread(Blk(N(1), N(2))), N(3)),
        };

    [Theory]
    [MemberData(nameof(DirectNodeCases))]
    public void DirectSequenceConstruct_DropsEmptyLeavesAndSplicesSpreads(string caseId, string expectedNeutral)
    {
        // ObserveAst also cross-checks the plain and counted evaluators.
        var observation = SemanticExplorerHarness.ObserveAst(caseId, DirectNodeBuilders[caseId]());
        Assert.Equal(expectedNeutral, observation.Neutral);
    }

    /// <summary>
    /// The required counterexample, stated as one comparison: the internal
    /// node evaluates <c>SequenceConstruct[(), 1]</c> to the bare atom
    /// <c>1</c> (the `()` leaf drops and the singleton collapses), while the
    /// written form <c>((), 1)</c> keeps the empty item visible. These are
    /// INTENTIONALLY different: the internal node is not the representation
    /// of written parentheses and must never become surface-reachable.
    /// </summary>
    [Fact]
    public void DirectSequenceConstruct_IsIntentionallyDifferentFromWrittenParentheses()
    {
        var internalObs = SemanticExplorerHarness.ObserveAst("sc[(), 1]", Sc(E(), N(1)));
        var surfaceObs = SemanticExplorerHarness.Observe("surface", "((), 1)");

        Assert.Equal("ok raw=1 n=1", internalObs.Neutral);
        Assert.Equal("ok raw=S[S[], 1] n=1", surfaceObs.Neutral);
        Assert.NotEqual(internalObs.Neutral, surfaceObs.Neutral);
    }

    /// <summary>
    /// A <see cref="Expr.SequenceConstruct"/> in call-FUNCTION position cannot
    /// resolve to an algorithm, and the structured
    /// <see cref="EvalError.NotAnAlgorithm"/> DESCRIPTION payload is exactly
    /// <c>"sequence construct expression"</c> — verbatim the Lean
    /// <c>resolveAlg</c> table entry (T4-3). Pinned on both the plain and the
    /// counted evaluation paths; only the payload is pinned here — the
    /// surrounding call-context WORDING is allowed to differ between Lean and
    /// C# under the alignment policy.
    /// </summary>
    [Fact]
    public void SequenceConstructAsCallFunction_IsNotAnAlgorithmWithLeanAlignedDescription()
    {
        var call = new Expr.Call(
            Sc(N(1), N(2)),
            new Algorithm.User(Parent: null, Parameters: [], Opens: [], Properties: [], Output: [N(3)]));
        var root = new Expr.Block(new Algorithm.User(
            Parent: null, Parameters: [], Opens: [], Properties: [], Output: [call]));

        static EvalError Innermost(EvalError error)
        {
            while (error is EvalError.WithContext context)
                error = context.Inner;

            return error;
        }

        var plain = Evaluator.Run(root);
        Assert.True(plain.IsError);
        var plainError = Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(plain.Error));
        Assert.Equal("sequence construct expression", plainError.Description);

        var counted = Evaluator.RunCounted(root);
        Assert.True(counted.IsError);
        var countedError = Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(counted.Error));
        Assert.Equal("sequence construct expression", countedError.Description);
    }

    // ----- 4. lone SequenceConstruct builtin argument ---------------------------
    //
    // A lone SequenceConstruct argument to a builtin is an ordinary value
    // expression: it value-evaluates to ONE grouped sequence value (through
    // the same ()-dropping evaluation as everywhere else) and then counts as
    // exactly ONE argument against the builtin's fixed signature, where the
    // post-binding collection view opens its lone boundary — exactly like
    // Lean and like the written grouped surface form.

    private static Expr BuiltinCall(string name, params Expr[] args) => new Expr.Call(
        new Expr.Resolve(name),
        new Algorithm.User(Parent: null, Parameters: [], Opens: [], Properties: [], Output: args));

    [Fact]
    public void LoneSequenceConstructBuiltinArgument_BehavesLikeGroupedSurfaceArgument()
    {
        // take(SC[1, 2, 5], 2) ≡ take((1, 2, 5), 2): the internal join is ONE
        // collection argument beside the explicit fixed `count` argument, and
        // the collection-producing builtin returns one exact list value.
        var grouped = SemanticExplorerHarness.ObserveAst("take-sc", BuiltinCall("take", Sc(N(1), N(2), N(5)), N(2)));
        var surface = SemanticExplorerHarness.Observe("take-surface", "take((1, 2, 5), 2)");
        Assert.Equal("ok raw=L[1, 2] n=1", grouped.Neutral);
        Assert.Equal(surface.Neutral, grouped.Neutral);

        // sum(SC[1, 2]) ≡ sum((1, 2)).
        var sum = SemanticExplorerHarness.ObserveAst("sum-sc", BuiltinCall("sum", Sc(N(1), N(2))));
        Assert.Equal("ok raw=3 n=1", sum.Neutral);
        Assert.Equal(SemanticExplorerHarness.Observe("sum-surface", "sum((1, 2))").Neutral, sum.Neutral);

        // take(SC[1, (2, 5)], 2) ≡ take((1, (2, 5)), 2): the nested pair stays
        // one opaque collection item on BOTH sides.
        var blockLeaf = SemanticExplorerHarness.ObserveAst("take-sc-pair", BuiltinCall("take", Sc(N(1), Blk(N(2), N(5))), N(2)));
        var blockLeafSurface = SemanticExplorerHarness.Observe("take-surface-pair", "take((1, (2, 5)), 2)");
        Assert.Equal("ok raw=L[1, S[2, 5]] n=1", blockLeaf.Neutral);
        Assert.Equal(blockLeafSurface.Neutral, blockLeaf.Neutral);

        // A lone SequenceConstruct is still exactly ONE argument against the
        // fixed take(collection, count) signature: a missing `count` is an
        // ordinary arity error — like the grouped surface form, on BOTH sides.
        var missingCount = SemanticExplorerHarness.ObserveAst("take-sc-missing-count", BuiltinCall("take", Sc(N(1), N(2), N(5))));
        var missingCountSurface = SemanticExplorerHarness.Observe("take-surface-missing-count", "take((1, 2, 5))");
        Assert.Equal("err arity", missingCount.Neutral);
        Assert.Equal(missingCountSurface.Neutral, missingCount.Neutral);
    }

    [Fact]
    public void LoneSequenceConstructBuiltinArgument_StillDropsEmptyLeaves()
    {
        // count(SC[(), 1, 2]) loses the () leaf (internal semantics), so the
        // bound collection is (1, 2) and the count is 2, while the written
        // count(((), 1, 2)) keeps the () as a countable item and counts 3.
        // Pinned as intentionally different — this is exactly the hazard that
        // must never become surface-reachable.
        var internalCount = SemanticExplorerHarness.ObserveAst("count-sc-empty", BuiltinCall("count", Sc(E(), N(1), N(2))));
        var surfaceCount = SemanticExplorerHarness.Observe("count-surface-empty", "count(((), 1, 2))");

        Assert.Equal("ok raw=2 n=1", internalCount.Neutral);
        Assert.Equal("ok raw=3 n=1", surfaceCount.Neutral);
        Assert.NotEqual(internalCount.Neutral, surfaceCount.Neutral);

        // The same divergence observed at a collection-producing boundary:
        // with the explicit `count` argument, take(SC[(), 1, 2], 2) keeps
        // [1, 2] while the written take(((), 1, 2), 2) keeps [(), 1].
        var internalTake = SemanticExplorerHarness.ObserveAst("take-sc-empty", BuiltinCall("take", Sc(E(), N(1), N(2)), N(2)));
        var surfaceTake = SemanticExplorerHarness.Observe("take-surface-empty", "take(((), 1, 2), 2)");

        Assert.Equal("ok raw=L[1, 2] n=1", internalTake.Neutral);
        Assert.Equal("ok raw=L[S[], 1] n=1", surfaceTake.Neutral);
        Assert.NotEqual(internalTake.Neutral, surfaceTake.Neutral);
    }
}
