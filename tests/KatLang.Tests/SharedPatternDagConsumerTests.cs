using System.Reflection;
using KatLang.Evaluation;
using KatLang.Semantics;
using KatLang.TestInfrastructure;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// SHARED-DAG GUARANTEE for the pattern consumers beyond signature validation
/// (docs/design/language-rules/evaluator-and-hosting.md § Shared-DAG guarantee; sibling of
/// <see cref="SharedPatternDagValidationTests"/>): the front-end parameter-name sets, open-provider
/// admission (<see cref="Evaluator.RequiresArguments"/>), the lifting-recovery rewrite, contract
/// comparison and the library's <see cref="AstWalker"/> subclasses read a host-built pattern that
/// holds the same sub-pattern twice per level with work linear in its distinct nodes, and with the
/// verdicts of the equivalent tree. For a tree every helper is exactly its per-occurrence twin.
/// </summary>
public class SharedPatternDagConsumerTests(ITestOutputHelper output)
{
    private const int Levels = 45;
    private const int BudgetLimit = 1_000_000;

    // Reads per distinct item edge (two per diamond level) a consumer may spend.
    private const int ReadsPerEdge = 16;

    // ── 1. Trees: every new helper is its per-occurrence twin ───────────────

    [Fact]
    public void OnTrees_TheExpandOnceHelpers_AreThePerOccurrenceOnes()
    {
        var random = new Random(20261110);
        for (var round = 0; round < 1000; round++)
        {
            var (dag, _) = RandomDag(random);
            var origin = new Dictionary<ParameterPattern, ParameterPattern>(ReferenceEqualityComparer.Instance);
            var tree = dag.Select(pattern => CloneTree(pattern, origin)).ToArray();
            var context = $"round {round}: {string.Join(", ", tree.Select(static p => p.DisplayName))}";

            var flatten = ParameterPattern.FlattenCaptures(tree);
            Assert.True(flatten.SequenceEqual(ParameterPattern.CapturesExpandingSharedNodesOnce(tree), ReferenceEqualityComparer.Instance), context);
            Assert.True(ParameterPattern.CountCaptures(tree) == ParameterPattern.CountCapturesExpandingSharedNodesOnce(tree), context);
            Assert.True((flatten.Count > 0) == ParameterPattern.HasAnyCapture(tree), context);
            var user = new Algorithm.User(null, tree, [], [], [new Expr.Num(1)]);
            Assert.True((user.ParameterCount > 0) == Evaluator.RequiresArguments(user), context);

            var recovered = ParameterPattern.KeepFirstCollectingCapturePerLevel(tree);
            Assert.Equal(OracleKeepFirst(tree), recovered.Select(static p => p.DisplayName));
            if (!ParameterPattern.HasMultipleCollectingCapturesAtAnyLevel(tree))
                Assert.Same(tree, recovered);

            var twin = dag.Select(pattern => CloneTree(pattern, origin)).ToArray();
            for (var index = 0; index < tree.Length; index++)
            {
                Assert.True(ParameterPattern.ContractComparer.Equals(tree[index], twin[index]), context);
                Assert.Equal(OracleContractHash(tree[index]), ParameterPattern.ContractComparer.GetHashCode(tree[index]));
                Assert.Equal(OracleContractHash(tree[index]), ParameterPattern.ContractComparer.GetHashCode(twin[index]));
            }
        }
    }

    // ── 2. Random DAGs against their cloned trees ───────────────────────────

    [Fact]
    public void RandomSmallDags_AgreeWithTheirClonedTrees()
    {
        var random = new Random(20261111);
        var sharedCases = 0;
        var unequalPairs = 0;
        for (var round = 0; round < 1000; round++)
        {
            var (dag, sharesNodes) = RandomDag(random);
            if (sharesNodes)
                sharedCases++;
            var origin = new Dictionary<ParameterPattern, ParameterPattern>(ReferenceEqualityComparer.Instance);
            var tree = dag.Select(pattern => CloneTree(pattern, origin)).ToArray();
            var context = $"round {round}: {string.Join(", ", tree.Select(static p => p.DisplayName))}";

            // Name sets: the same names in first-occurrence order (CloneTree keeps declarations).
            Assert.True(FirstOccurrences(ParameterPattern.FlattenCaptures(tree))
                .SequenceEqual(FirstOccurrences(ParameterPattern.CapturesExpandingSharedNodesOnce(dag)), ReferenceEqualityComparer.Instance), context);
            Assert.True(ParameterPattern.HasAnyCapture(tree) == ParameterPattern.HasAnyCapture(dag), context);
            Assert.True(Evaluator.RequiresArguments(new Algorithm.User(null, tree, [], [], [new Expr.Num(1)]))
                == Evaluator.RequiresArguments(new Algorithm.User(null, dag, [], [], [new Expr.Num(1)])), context);

            // Recovery: the tree's recovered shape, sharing exactly where the input shared.
            var recoveredDag = ParameterPattern.KeepFirstCollectingCapturePerLevel(dag);
            Assert.Equal(OracleKeepFirst(tree), recoveredDag.Select(static p => p.DisplayName));
            AssertSharingMirrored(dag, recoveredDag, context);

            // Contract comparison: the tree's verdict and hash, for equal and unequal pairs.
            for (var index = 0; index < dag.Length; index++)
            {
                Assert.True(ParameterPattern.ContractComparer.Equals(dag[index], tree[index]), context);
                Assert.Equal(OracleContractHash(tree[index]), ParameterPattern.ContractComparer.GetHashCode(dag[index]));
                var other = dag[(index + 1) % dag.Length];
                var expected = OracleContractEquals(tree[index], CloneTree(other, origin));
                unequalPairs += expected ? 0 : 1;
                Assert.True(expected == ParameterPattern.ContractComparer.Equals(dag[index], other), context);
            }
        }

        output.WriteLine($"1000 cases, {sharedCases} with shared nodes, {unequalPairs} unequal contract pairs");
        Assert.True(sharedCases > 500);
        Assert.True(unequalPairs > 200);
    }

    // ── 3. Diamonds: linear work at 45 and 90 levels ────────────────────────

    public static TheoryData<string> Kinds() => new() { "sequence", "list", "unpack" };

    [Theory]
    [MemberData(nameof(Kinds))]
    public void NameSets_OnASharedDiamond_AreTheTreeNames_AndLinear(string kind)
        => AssertLinear($"name sets/{kind}", levels =>
        {
            var budget = new PatternReadBudget(BudgetLimit);
            ParameterPattern[] patterns = [Diamond(kind, Bottom("pair"), levels, budget), new CaptureParameterPattern("z")];
            Assert.Equal(["x", "y", "z"], ParameterPattern.CapturesExpandingSharedNodesOnce(patterns).Select(static c => c.Name).Distinct());
            Assert.Equal(3, ParameterPattern.CountCapturesExpandingSharedNodesOnce(patterns));
            return budget.Reads;
        });

    [Theory]
    [MemberData(nameof(Kinds))]
    public void ColdTemplateNameCountAndOpenAdmission_StayLinearWithoutBuildingOccurrenceFacts(string kind)
    {
        foreach (var bottom in new[] { "pair", "empty" })
        {
            AssertLinear($"cold template/{kind}/{bottom}", levels =>
            {
                var budget = new PatternReadBudget(BudgetLimit);
                var template = ImplicitSignatureTemplate.Flat([Diamond(kind, Bottom(bottom), levels, budget)]);
                Assert.Equal(bottom == "pair" ? 2 : 0, ParameterPattern.CountCapturesExpandingSharedNodesOnce(template));
                Assert.Equal(bottom == "pair", ParameterPattern.HasAnyCapture(template));
                Assert.Equal(bottom == "pair", Evaluator.RequiresArguments(new Algorithm.User(null, template, [], [], [new Expr.Num(1)])));
                Assert.Null(template.ComputedFacts);
                return budget.Reads;
            });
        }
    }

    [Theory]
    [MemberData(nameof(Kinds))]
    public void WarmTemplateNameCount_IsTheExpandOnceCount(string kind)
    {
        var template = ImplicitSignatureTemplate.Flat([Diamond(kind, Bottom("pair"), 4, new PatternReadBudget(BudgetLimit))]);
        // Occurrence facts remain per path by contract; a name-set charge must count its own walk.
        Assert.Equal(32, template.Facts.CaptureCount);
        Assert.Equal(2, ParameterPattern.CapturesExpandingSharedNodesOnce(template).Count);
        Assert.Equal(2, ParameterPattern.CountCapturesExpandingSharedNodesOnce(template));
    }

    [Fact]
    public void CompletedUniqueTemplateFacts_KeepTheConstantTimeShortcut()
    {
        var budget = new PatternReadBudget(BudgetLimit);
        var template = ImplicitSignatureTemplate.Flat([new ListValueParameterPattern(
            new BudgetedPatternItems<ParameterPattern>(new CaptureParameterPattern("x"), new CaptureParameterPattern("y"), budget))]);
        Assert.Equal(2, template.Facts.CaptureCount);
        budget.Reads = 0;
        Assert.Equal(2, ParameterPattern.CountCapturesExpandingSharedNodesOnce(template));
        Assert.True(ParameterPattern.HasAnyCapture(template));
        Assert.Equal(0, budget.Reads);
    }

    [Fact]
    public void RecoveryAndContractMemos_ObserveHostMutationsBetweenCalls()
    {
        var items = new List<ParameterPattern>
        {
            new CaptureParameterPattern("a", Kind: ParameterKind.Collecting),
            new CaptureParameterPattern("b", Kind: ParameterKind.Collecting),
        };
        ParameterPattern[] patterns = [new ListValueParameterPattern(items)];
        var twin = CloneTree(patterns[0], new(ReferenceEqualityComparer.Instance));
        Assert.True(ParameterPattern.ContractComparer.Equals(patterns[0], twin));
        Assert.Equal(OracleContractHash(twin), ParameterPattern.ContractComparer.GetHashCode(patterns[0]));
        var recovered = Assert.Single(ParameterPattern.KeepFirstCollectingCapturePerLevel(patterns));
        Assert.Equal(ParameterKind.Normal, ((CaptureParameterPattern)ParameterPattern.StructuralItems(recovered)![1]).Kind);
        Assert.Equal(ParameterKind.Collecting, ((CaptureParameterPattern)items[1]).Kind);

        items[1] = new CaptureParameterPattern("c");
        Assert.False(ParameterPattern.ContractComparer.Equals(patterns[0], twin));
        Assert.Equal(OracleContractHash(patterns[0]), ParameterPattern.ContractComparer.GetHashCode(patterns[0]));
        Assert.Same(patterns, ParameterPattern.KeepFirstCollectingCapturePerLevel(patterns));
    }

    [Theory]
    [MemberData(nameof(Kinds))]
    public void CompletedParameterNameSet_OnASharedSignature_IsTheTreeSet_AndLinear(string kind)
    {
        var expected = CompletedNames(Tree(kind, Bottom("pair"), 4));
        Assert.Equal(["x", "y"], expected);
        AssertLinear($"completed names/{kind}", levels =>
        {
            var budget = new PatternReadBudget(BudgetLimit);
            Assert.Equal(expected, CompletedNames(Diamond(kind, Bottom("pair"), levels, budget)));
            return budget.Reads;
        });

        static string[] CompletedNames(ParameterPattern signature)
        {
            // Publish a completed pass view directly: detection's separate occurrence-list
            // consumer must not prevent this regression from reaching CompleteLookups.
            var raw = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
            var operation = new StaticStructureOperation(raw, new StaticQueryLimits(100_000, 64, 100_000, 1_000_000, 1_000_000),
                prelude: new Algorithm.User(null, [], [], [], []));
            var resolved = raw with { ParameterPatterns = [signature] };
            operation.Publish(operation.Root, StaticPublicationStage.Detected, raw);
            operation.Publish(operation.Root, StaticPublicationStage.Resolved, resolved);
            operation.CompleteLookups(resolved);
            var facts = resolved.CompletedStructure!.Facts.Facts(operation.Root)!;
            Assert.Same(resolved, facts.Body);
            return facts.Parameters.Order(StringComparer.Ordinal).ToArray();
        }
    }

    [Fact]
    public void BranchNameSets_InLiveAndMaterializedContexts_AreTheTreeSet_AndLinear()
    {
        var expected = Names(HeadTree(4));
        Assert.Equal(["x", "y", "x", "y"], expected);
        AssertLinear("live and materialized branch names", levels =>
        {
            var budget = new PatternReadBudget(BudgetLimit);
            Assert.Equal(expected, Names(HeadDiamond(levels, budget)));
            return budget.Reads;
        });

        static string[] Names(Pattern head)
        {
            var limits = new StaticQueryLimits(100_000, 64, 100_000, 1_000_000, 1_000_000);
            var root = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
            var body = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
            var queries = new StaticStructureQueries(root, limits, prelude: new Algorithm.User(null, [], [], [], []), phase: StaticAstPhase.Resolved);
            var live = queries.BranchBodyIn(queries.Root, body, head);
            var materialization = new StaticStructureQueries(queries.Freeze(), limits, StaticAstPhase.Resolved);
            var loaded = materialization.MaterializedBranchIn(queries.Root, body, head);
            return [.. queries.WrittenParametersOf(live).Order(StringComparer.Ordinal),
                .. materialization.WrittenParametersOf(loaded).Order(StringComparer.Ordinal)];
        }
    }

    [Theory]
    [MemberData(nameof(Kinds))]
    public void OpenAdmission_OnASharedDiamond_IsTheTreeVerdict_AndLinear(string kind)
    {
        foreach (var bottom in new[] { "x", "empty" })
        {
            var expected = bottom == "x";
            Assert.Equal(expected, Evaluator.RequiresArguments(Callee(Tree(kind, Bottom(bottom), 4))));
            AssertLinear($"open admission/{kind}/{bottom}", levels =>
            {
                var budget = new PatternReadBudget(BudgetLimit);
                var dag = Diamond(kind, Bottom(bottom), levels, budget);
                Assert.Equal(expected, ParameterPattern.HasAnyCapture([dag]));
                Assert.Equal(expected, Evaluator.RequiresArguments(Callee(dag)));
                return budget.Reads;
            });
        }
    }

    [Theory]
    [MemberData(nameof(Kinds))]
    public void LiftingRecovery_OnASharedDiamond_KeepsTheTreeShapeAndTheSharing_AndLinear(string kind)
    {
        var tree = Tree(kind, Bottom("collectors"), 3);
        var expected = OracleKeepFirst([tree]);
        var small = ParameterPattern.KeepFirstCollectingCapturePerLevel([Diamond(kind, Bottom("collectors"), 3, new PatternReadBudget(BudgetLimit))]);
        Assert.Equal(expected, small.Select(static p => p.DisplayName));

        AssertLinear($"recovery/{kind}", levels =>
        {
            var budget = new PatternReadBudget(BudgetLimit);
            var recovered = Assert.Single(ParameterPattern.KeepFirstCollectingCapturePerLevel([Diamond(kind, Bottom("collectors"), levels, budget)]));
            var reads = budget.Reads;
            // Each recovered level shares one recovered child, down to the recovered bottom.
            var node = recovered;
            for (var level = 0; level < levels; level++)
            {
                var items = ParameterPattern.StructuralItems(node)!;
                Assert.Same(items[0], items[1]);
                node = items[0];
            }

            var bottom = ParameterPattern.StructuralItems(node)!;
            Assert.Equal(ParameterKind.Collecting, ((CaptureParameterPattern)bottom[0]).Kind);
            Assert.Equal(ParameterKind.Normal, ((CaptureParameterPattern)bottom[1]).Kind);
            return reads;
        });
    }

    [Theory]
    [MemberData(nameof(Kinds))]
    public void ContractComparison_OnSharedDiamonds_IsTheTreeVerdict_AndLinear(string kind)
    {
        var treeHash = OracleContractHash(Tree(kind, Bottom("pair"), 4));
        Assert.Equal(treeHash, ParameterPattern.ContractComparer.GetHashCode(Diamond(kind, Bottom("pair"), 4, new PatternReadBudget(BudgetLimit))));

        AssertLinear($"contract/{kind}", levels =>
        {
            var budget = new PatternReadBudget(BudgetLimit);
            var left = Diamond(kind, Bottom("pair"), levels, budget);
            var right = Diamond(kind, Bottom("pair"), levels, budget);
            var different = Diamond(kind, Bottom("collectors"), levels, budget);
            Assert.True(ParameterPattern.ContractComparer.Equals(left, right));
            Assert.False(ParameterPattern.ContractComparer.Equals(left, different));
            Assert.Equal(ParameterPattern.ContractComparer.GetHashCode(left), ParameterPattern.ContractComparer.GetHashCode(right));
            var set = new HashSet<ParameterPattern>(ParameterPattern.ContractComparer) { left };
            Assert.False(set.Add(right));
            Assert.True(set.Add(different));
            return budget.Reads;
        });
    }

    // ── 4. Public routes ────────────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(Kinds))]
    public void OpenOfASharedSignature_IsTheTreeOutcome_WithBoundedReads(string kind)
    {
        var expected = Outcome(Evaluator.Run(OpenRoot(Tree(kind, Bottom("x"), 4))));
        Assert.StartsWith("IllegalInOpen", expected);
        Assert.Contains("open providers must have an empty effective parameter list", expected);

        var budget = new PatternReadBudget(BudgetLimit);
        var actual = Outcome(Evaluator.Run(OpenRoot(Diamond(kind, Bottom("x"), Levels, budget))));
        output.WriteLine($"{kind}: open reads = {budget.Reads}");
        // The message quotes a bounded prefix of the per-occurrence names: x, x, …
        Assert.StartsWith("IllegalInOpen", actual);
        Assert.Contains("open providers must have an empty effective parameter list (found: x, x", actual);
        Assert.InRange(budget.Reads, 1, ReadsPerEdge * 2 * Levels);
    }

    /// <summary>
    /// The editor model's name-resolution parameter table reads the expand-once name set; a small
    /// shared signature models exactly like its tree. (Its property metadata — signature help, the
    /// parameter list — is PER OCCURRENCE by contract, so a deep shared signature is not linear
    /// there: <c>CreateOrdinaryPropertyInfo</c> reads <see cref="Algorithm.User.Parameters"/>.)
    /// </summary>
    [Theory]
    [MemberData(nameof(Kinds))]
    public void SemanticModelOfASmallSharedSignature_ResolvesAsTheTree(string kind)
    {
        var expected = Resolutions(SemanticModelBuilder.Build(ModelRoot(Tree(kind, Bottom("pair"), 4))));
        Assert.Contains("x ", expected);
        var actual = Resolutions(SemanticModelBuilder.Build(ModelRoot(Diamond(kind, Bottom("pair"), 4, new PatternReadBudget(BudgetLimit)))));
        Assert.Equal(expected, actual);
    }

    // ── 5. AstWalker audit ──────────────────────────────────────────────────

    /// <summary>
    /// Every production <see cref="AstWalker"/> subclass is classified: it either skips clause
    /// heads (a no-op <see cref="AstWalker.VisitPattern"/>, because it reads nothing from them) or
    /// walks them with its own DAG-safe walk. A new walker fails here until it is classified.
    /// </summary>
    [Fact]
    public void EveryLibraryAstWalker_SkipsOrLinearlyWalksClauseHeads()
    {
        string[] ownLinearHeadWalk =
        [
            // Ast.cs: the pre-evaluation validator overrides VisitPattern with a visited set.
            "PreEvaluationValidationWalker",
            // Its VisitConditionalBranch never calls the base: an expand-once binder walk of its own.
            "ParameterPropertyCollisionValidator",
        ];
        string[] skipsHeads =
        [
            "InvariantWalker", "InferredParameterOutputValidator", "LoadWalker", "LoadBearingMarker",
            "OpenProviderValidator", "OpenPresence", "DotMemberProvenanceFinalizer", "ModuleProvidedAlgorithmCollector",
        ];
        var walkers = typeof(AstWalker).Assembly.GetTypes()
            .Where(static type => type.IsSubclassOf(typeof(AstWalker)))
            .Select(static type => type.Name)
            .Order(StringComparer.Ordinal)
            .ToArray();
        Assert.Equal(ownLinearHeadWalk.Concat(skipsHeads).Order(StringComparer.Ordinal), walkers);

        var visitPattern = typeof(AstWalker).GetMethod(nameof(AstWalker.VisitPattern))!;
        foreach (var type in typeof(AstWalker).Assembly.GetTypes().Where(static type => type.IsSubclassOf(typeof(AstWalker))))
        {
            var declared = type.GetMethod(nameof(AstWalker.VisitPattern), BindingFlags.Public | BindingFlags.Instance)!;
            Assert.True(declared.DeclaringType == type || type.Name == "ParameterPropertyCollisionValidator",
                $"{type.Name} inherits the per-path base clause-head walk.");
            Assert.Equal(visitPattern.GetBaseDefinition(), declared.GetBaseDefinition());
        }
    }

    [Fact]
    public async Task LibraryWalkers_OverASharedClauseHead_CompleteWithBoundedReads()
    {
        var (expected, _) = WalkerOutcomes(FamilyRoot(HeadTree(4), Tree("sequence", Bottom("pair"), 4)), new PatternReadBudget(BudgetLimit));
        Assert.Contains("ParameterPropertyCollision", expected);
        var budget = new PatternReadBudget(BudgetLimit);
        var (actual, perWalker) = WalkerOutcomes(FamilyRoot(HeadDiamond(Levels, budget), Diamond("sequence", Bottom("pair"), Levels, budget)), budget);
        output.WriteLine(string.Join(", ", perWalker.Select(static entry => $"{entry.Key}={entry.Value}")));
        Assert.Equal(expected, actual);
        foreach (var (walker, reads) in perWalker)
            Assert.True(reads <= ReadsPerEdge * 2 * Levels, $"{walker}: {reads} reads");
        // Clause heads and signatures are read only by the walkers that need their names (static
        // structure, the collision validator); the others skip heads and never read a signature.
        Assert.All(perWalker.Where(static entry => entry.Key is not ("collision" or "open")), static entry => Assert.Equal(0, entry.Value));

        var loaderBudget = new PatternReadBudget(BudgetLimit);
        var diagnostics = new DiagnosticBag();
        var loader = new ModuleLoader(diagnostics, (_, _) => ValueTask.FromResult("public X = 1"));
        await loader.ElaborateAsync(FamilyRoot(HeadDiamond(Levels, loaderBudget), Diamond("sequence", Bottom("pair"), Levels, loaderBudget)));
        output.WriteLine($"loader reads = {loaderBudget.Reads}");
        Assert.DoesNotContain(diagnostics, static diagnostic => diagnostic.Severity == DiagnosticSeverity.Error);
        Assert.InRange(loaderBudget.Reads, 0, ReadsPerEdge * 2 * Levels);

        static (string Outcomes, Dictionary<string, int> Reads) WalkerOutcomes(Algorithm.User root, PatternReadBudget budget)
        {
            var reads = new Dictionary<string, int>();
            var outcomes = new List<string>();
            var before = budget.Reads;
            void Mark(string walker)
            {
                reads[walker] = budget.Reads - before;
                before = budget.Reads;
            }

            outcomes.Add($"invariant {DotCallElaborationInvariant.CheckElaborated(root)?.ToString() ?? "none"}");
            Mark("invariant");
            outcomes.Add($"load {LoadElaborationGuard.TryFindFirstUnresolvedLoad(root, out _)}");
            Mark("load");
            var bag = new DiagnosticBag();
            OpenProviderValidator.Validate(root, bag, hostOperations: null);
            Mark("open");
            InferredParameterOutputValidator.ValidateProgram(root, bag);
            Mark("inferred");
            new ParameterPropertyCollisionValidator(bag, programRoot: root).VisitAlgorithm(root);
            Mark("collision");
            outcomes.AddRange(bag.Select(static diagnostic => $"{diagnostic.Code}: {diagnostic.Message}"));
            return (string.Join(" | ", outcomes), reads);
        }
    }

    // ── Measurement ─────────────────────────────────────────────────────────

    private void AssertLinear(string label, Func<int, int> measure)
    {
        var reads45 = measure(Levels);
        var reads90 = measure(2 * Levels);
        output.WriteLine($"{label}: reads at {Levels} levels = {reads45}, at {2 * Levels} levels = {reads90}");
        Assert.InRange(reads45, 1, ReadsPerEdge * 2 * Levels);
        // Linear: twice the levels cost at most twice the reads, up to one level's constant.
        Assert.InRange(reads90, 1, 2 * reads45 + 2 * ReadsPerEdge);
    }

    // ── Shapes ──────────────────────────────────────────────────────────────

    // A fresh bottom: x; (x, y); (*a, *b); [] (no capture at all).
    private static ParameterPattern Bottom(string bottom) => bottom switch
    {
        "pair" => new SequenceValueParameterPattern([new CaptureParameterPattern("x"), new CaptureParameterPattern("y")]),
        "collectors" => new SequenceValueParameterPattern([
            new CaptureParameterPattern("a", Kind: ParameterKind.Collecting),
            new CaptureParameterPattern("b", Kind: ParameterKind.Collecting)]),
        "empty" => new ListValueParameterPattern([]),
        _ => new CaptureParameterPattern("x"),
    };

    private static ParameterPattern Structural(string kind, IReadOnlyList<ParameterPattern> items) => kind switch
    {
        "sequence" => new SequenceValueParameterPattern(items),
        "list" => new ListValueParameterPattern(items),
        _ => new UnpackingParameterPattern(items),
    };

    // Shares one sub-pattern twice per level: levels + 1 distinct nodes, 2^levels bottom occurrences.
    private static ParameterPattern Diamond(string kind, ParameterPattern bottom, int levels, PatternReadBudget budget)
    {
        var pattern = bottom;
        for (var level = 0; level < levels; level++)
            pattern = Structural(kind, new BudgetedPatternItems<ParameterPattern>(pattern, pattern, budget));
        return pattern;
    }

    // The same shape with a fresh node per occurrence (fresh declarations too).
    private static ParameterPattern Tree(string kind, ParameterPattern bottom, int levels)
        => levels == 0
            ? CloneTree(bottom, new(ReferenceEqualityComparer.Instance), freshDeclarations: true)
            : Structural(kind, [Tree(kind, bottom, levels - 1), Tree(kind, bottom, levels - 1)]);

    private static Pattern HeadDiamond(int levels, PatternReadBudget budget)
    {
        Pattern pattern = new Pattern.SequenceValue([new Pattern.Bind("x"), new Pattern.Bind("y")]);
        for (var level = 0; level < levels; level++)
            pattern = new Pattern.SequenceValue(new BudgetedPatternItems<Pattern>(pattern, pattern, budget));
        return pattern;
    }

    private static Pattern HeadTree(int levels)
        => levels == 0
            ? new Pattern.SequenceValue([new Pattern.Bind("x"), new Pattern.Bind("y")])
            : new Pattern.SequenceValue([HeadTree(levels - 1), HeadTree(levels - 1)]);

    private static Algorithm.User Callee(ParameterPattern pattern)
        => new(null, [pattern], [], [], [new Expr.Num(1)]);

    private static Expr OpenRoot(ParameterPattern shared)
        => new Expr.AlgorithmExpr(new Algorithm.User(null, [], [new Expr.Resolve("F")], [new Property("F", Callee(shared))], [new Expr.Resolve("Q")]));

    private static Algorithm.User ModelRoot(ParameterPattern shared)
    {
        var callee = new Algorithm.User(null, [shared], [], [], [new Expr.Param("x") { Span = new SourceSpan(1, 10, 1, 11) }]);
        return new Algorithm.User(null, [], [], [new Property("F", callee)], [new Expr.Num(7)]);
    }

    // `F = { ((…)) => 1 }; G(…) = { x = 1; x }; Lib = { X = 1 }; open Lib; 7`: a family whose one
    // branch head nests the head pattern, and a callee whose signature binds x beside a property x.
    private static Algorithm.User FamilyRoot(Pattern nested, ParameterPattern signature)
    {
        var one = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        var callee = new Algorithm.User(null, [signature], [], [new Property("x", one) { DeclarationSpans = [new SourceSpan(2, 5, 2, 6)] }], [new Expr.Num(1)]);
        var body = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        var family = new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.SequenceValue([nested]), body)]);
        var lib = new Algorithm.User(null, [], [], [new Property("X", new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))], []);
        return new Algorithm.User(null, [], [new Expr.Resolve("Lib")],
            [new Property("F", family), new Property("G", callee), new Property("Lib", lib)], [new Expr.Num(7)]);
    }

    private static string Outcome(EvalResult<Result> result)
        => result.IsError
            ? $"{Unwrap(result.Error).GetType().Name} {Unwrap(result.Error)}"
            : result.Value is Result.Atom atom ? $"ok {atom.Value}" : $"ok {result.Value}";

    private static EvalError Unwrap(EvalError error)
        => error is EvalError.WithContext context ? Unwrap(context.Inner) : error;

    // Every identifier resolution of the model: name, classification and kind.
    private static string Resolutions(SemanticModel model)
        => string.Join(" | ", model.IdentifierResolutions.Select(static resolution
            => $"{resolution.Occurrence.Name} {resolution.Classification} {resolution.Occurrence.Kind}"));

    // ── Random DAGs and the tree oracles ────────────────────────────────────

    private static readonly string[] Names = ["a", "b", "c"];
    private static readonly string[] KindNames = ["sequence", "list", "unpack"];

    private static (ParameterPattern[] Patterns, bool SharesNodes) RandomDag(Random random)
    {
        var pool = new List<(ParameterPattern Node, int Height)>();
        var leaves = random.Next(1, 4);
        for (var index = 0; index < leaves; index++)
        {
            var kind = random.Next(3) == 0 ? ParameterKind.Collecting : ParameterKind.Normal;
            pool.Add((new CaptureParameterPattern(Names[random.Next(Names.Length)], Kind: kind), 0));
        }

        var uses = new Dictionary<ParameterPattern, int>(ReferenceEqualityComparer.Instance);
        var structural = random.Next(1, 7);
        for (var index = 0; index < structural; index++)
        {
            var items = new List<ParameterPattern>();
            var height = 0;
            var count = random.Next(0, 4);
            for (var item = 0; item < count; item++)
            {
                var candidates = pool.Where(static entry => entry.Height < 6).ToList();
                var pick = candidates[Math.Max(0, candidates.Count - 1 - random.Next(Math.Min(3, candidates.Count)) - (random.Next(3) == 0 ? random.Next(candidates.Count) : 0))];
                items.Add(pick.Node);
                uses[pick.Node] = uses.GetValueOrDefault(pick.Node) + 1;
                height = Math.Max(height, pick.Height + 1);
            }

            pool.Add((Structural(KindNames[random.Next(KindNames.Length)], items), Math.Max(1, height)));
        }

        var top = new ParameterPattern[random.Next(1, 4)];
        for (var index = 0; index < top.Length; index++)
        {
            var pick = pool[Math.Max(0, pool.Count - 1 - random.Next(Math.Min(3, pool.Count)))].Node;
            top[index] = pick;
            uses[pick] = uses.GetValueOrDefault(pick) + 1;
        }

        return (top, uses.Values.Any(static count => count > 1));
    }

    // A tree copy: a fresh node per occurrence, keeping each leaf's declaration unless asked not to.
    private static ParameterPattern CloneTree(
        ParameterPattern pattern, Dictionary<ParameterPattern, ParameterPattern> origin, bool freshDeclarations = false)
    {
        ParameterPattern clone = ParameterPattern.StructuralItems(pattern) is { } items
            ? ParameterPattern.WithStructuralItems(pattern, items.Select(item => CloneTree(item, origin, freshDeclarations)).ToArray())
            : freshDeclarations
                ? new CaptureParameterPattern(((CaptureParameterPattern)pattern).Name, Kind: ((CaptureParameterPattern)pattern).Kind)
                : new CaptureParameterPattern(((CaptureParameterPattern)pattern).Parameter);
        origin[clone] = pattern;
        return clone;
    }

    private static IEnumerable<ParameterDeclaration> FirstOccurrences(IEnumerable<ParameterDeclaration> captures)
    {
        var seen = new HashSet<string>(StringComparer.Ordinal);
        return captures.Where(capture => seen.Add(capture.Name)).ToArray();
    }

    // The plain recursive recovery over a tree, rendered.
    private static string[] OracleKeepFirst(IReadOnlyList<ParameterPattern> tree)
        => Recover(tree).Select(static p => p.DisplayName).ToArray();

    private static ParameterPattern[] Recover(IReadOnlyList<ParameterPattern> level)
    {
        var collecting = false;
        var result = new ParameterPattern[level.Count];
        for (var index = 0; index < level.Count; index++)
        {
            result[index] = level[index] switch
            {
                CaptureParameterPattern { Kind: ParameterKind.Collecting } capture when collecting
                    => new CaptureParameterPattern(capture.Name),
                CaptureParameterPattern capture => capture,
                var group => ParameterPattern.WithStructuralItems(group, Recover(ParameterPattern.StructuralItems(group)!)),
            };
            collecting |= level[index] is CaptureParameterPattern { Kind: ParameterKind.Collecting };
        }

        return result;
    }

    // The recovered DAG shares a recovered node exactly where the input shared the original one.
    private static void AssertSharingMirrored(IReadOnlyList<ParameterPattern> input, IReadOnlyList<ParameterPattern> recovered, string context)
    {
        var map = new Dictionary<ParameterPattern, ParameterPattern>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<(ParameterPattern Input, ParameterPattern Output)>();
        for (var index = 0; index < input.Count; index++)
            pending.Push((input[index], recovered[index]));
        while (pending.TryPop(out var pair))
        {
            if (ParameterPattern.StructuralItems(pair.Input) is not { } items)
                continue;
            if (map.TryGetValue(pair.Input, out var known))
            {
                Assert.True(ReferenceEquals(known, pair.Output), context);
                continue;
            }

            map.Add(pair.Input, pair.Output);
            var outputItems = ParameterPattern.StructuralItems(pair.Output)!;
            for (var index = 0; index < items.Count; index++)
                pending.Push((items[index], outputItems[index]));
        }
    }

    // The plain recursive contract equality and hash (the comparer's former per-path form).
    private static bool OracleContractEquals(ParameterPattern left, ParameterPattern right)
        => (left, right) switch
        {
            (CaptureParameterPattern a, CaptureParameterPattern b) => a.Name == b.Name && a.Kind == b.Kind,
            (SequenceValueParameterPattern a, SequenceValueParameterPattern b) => ItemsEqual(a.Items, b.Items),
            (ListValueParameterPattern a, ListValueParameterPattern b) => ItemsEqual(a.Items, b.Items),
            (UnpackingParameterPattern a, UnpackingParameterPattern b) => ItemsEqual(a.Items, b.Items),
            _ => false,
        };

    private static bool ItemsEqual(IReadOnlyList<ParameterPattern> left, IReadOnlyList<ParameterPattern> right)
        => left.Count == right.Count && left.Zip(right).All(static pair => OracleContractEquals(pair.First, pair.Second));

    private static int OracleContractHash(ParameterPattern pattern)
    {
        var hash = new HashCode();
        hash.Add(pattern switch
        {
            CaptureParameterPattern => 0,
            SequenceValueParameterPattern => 1,
            ListValueParameterPattern => 2,
            UnpackingParameterPattern => 3,
            _ => throw new InvalidOperationException(),
        });
        if (pattern is CaptureParameterPattern capture)
        {
            hash.Add(capture.Name, StringComparer.Ordinal);
            hash.Add(capture.Kind);
        }
        else
        {
            foreach (var item in ParameterPattern.StructuralItems(pattern)!)
                hash.Add(OracleContractHash(item));
        }

        return hash.ToHashCode();
    }
}
