using KatLang.Semantics;
using KatLang.TestInfrastructure;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// SHARED-DAG GUARANTEE end to end for host-built signatures that reach the EVALUATOR'S
/// signature diagnostics (docs/design/language-rules/evaluator-and-hosting.md § Shared-DAG
/// guarantee; sibling of <see cref="SharedPatternDagValidationTests"/> and
/// <see cref="SharedPatternDagConsumerTests"/>). Deferred module bodies retain publicly reachable
/// memberships: a host can install a shared signature before materialization, so the public async
/// run route also reaches parameter detection and implicit-argument resolution. On the run routes,
/// a rejection whose REPORT is small — a
/// zero-argument demand, an arity mismatch, a block's missing implicit arguments without
/// captures, reduce's accumulator hint without captures — is built with work linear in the
/// distinct pattern nodes; a report that PUBLISHES one name per capture occurrence (K of them) is
/// built with work proportional to K, and one that renders the pattern is proportional to the
/// rendered text. For a tree every helper is exactly its per-occurrence twin.
/// </summary>
public class SharedSignatureDagEndToEndTests(ITestOutputHelper output)
{
    private const int BudgetLimit = 1_000_000;

    // Reads per distinct item edge (two per diamond level) a run route may spend.
    private const int ReadsPerEdge = 16;

    private static readonly int[] Depths = [15, 30, 45, 90];

    [Theory]
    [InlineData("empty", 15)]
    [InlineData("empty", 30)]
    [InlineData("empty", 45)]
    [InlineData("empty", 90)]
    [InlineData("x", 15)]
    [InlineData("x", 30)]
    [InlineData("x", 45)]
    [InlineData("x", 90)]
    public async Task DeferredLiftedHostSignature_MergesAndBuildsArgumentsWithoutPathExpansion(string bottom, int depth)
    {
        var (value, reads) = await RunLiftedDeferredSignature(bottom, depth, expanded: false, invokeLifted: false);
        Assert.Equal(new Result.Atom(7), value);
        output.WriteLine($"deferred lifting/{bottom}: depth {depth}, reads = {reads}, result = 7");
        Assert.InRange(reads, 1, 256 * (depth + 1));
    }

    [Theory]
    [InlineData("empty")]
    [InlineData("x")]
    public async Task DeferredLiftedHostSignature_ExecutesLikeItsExpandedTree(string bottom)
    {
        var tree = await RunLiftedDeferredSignature(bottom, 4, expanded: true, invokeLifted: true);
        var dag = await RunLiftedDeferredSignature(bottom, 4, expanded: false, invokeLifted: true);
        Assert.Equal(new Result.Atom(2), tree.Value);
        Assert.Equal(tree.Value, dag.Value);
    }

    private static async Task<(Result Value, int Reads)> RunLiftedDeferredSignature(
        string bottom, int depth, bool expanded, bool invokeLifted)
    {
        var finalRow = invokeLifted ? bottom == "x" ? "H([9])" : "H()" : "7";
        var source = "F(0) = 0\nF(n) = { open 'https://katlang.org/shared-dag-probe'\nG([x, x]) = 1\nH = G + 1\n"
            + finalRow + " }\nF(1)";
        var downloads = 0;
        var parsed = await SourceProvenance.ParseValidAsync(source, new RunOptions
        {
            DownloadCode = (_, _) => { downloads++; return ValueTask.FromResult("public ModuleValue = 1"); },
        });
        Assert.Equal(0, downloads);
        var family = Assert.IsType<Algorithm.Conditional>(parsed.Root.Properties.Single(static p => p.Name == "F").Value);
        var body = family.Branches[1].Body;
        var nested = Assert.IsType<Algorithm.User>(body.Properties.Single(static p => p.Name == "G").Value);
        var group = Assert.IsType<ListValueParameterPattern>(nested.ParameterPatterns[0]);
        var items = Assert.IsAssignableFrom<IList<ParameterPattern>>(group.Items);
        var budget = new PatternReadBudget(20_000);
        items[0] = expanded ? Tree(Bottom(bottom), depth) : Diamond("sequence", Bottom(bottom), depth, budget);
        items[1] = expanded ? Tree(Bottom(bottom), depth) : items[0];
        var result = await Evaluator.RunAsync(new Expr.AlgorithmExpr(parsed.Root));
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        Assert.Equal(1, downloads);
        return (result.Value, budget.Reads);
    }

    [Theory]
    [InlineData("empty", 15)]
    [InlineData("empty", 30)]
    [InlineData("empty", 45)]
    [InlineData("empty", 90)]
    [InlineData("x", 15)]
    [InlineData("x", 30)]
    [InlineData("x", 45)]
    [InlineData("x", 90)]
    public async Task DeferredHostSignature_ReachesDetectorAndResolver_WithDistinctInputWork(string bottom, int depth)
    {
        const string source = "F(0) = 0\nF(n) = { open 'https://katlang.org/shared-dag-probe'\nG([x, x]) = 1\n7 }\nF(1)";
        var downloads = 0;
        var parsed = await SourceProvenance.ParseValidAsync(source, new RunOptions
        {
            DownloadCode = (_, _) => { downloads++; return ValueTask.FromResult("public ModuleValue = 1"); },
        });
        Assert.Equal(0, downloads);
        var family = Assert.IsType<Algorithm.Conditional>(parsed.Root.Properties.Single(static p => p.Name == "F").Value);
        var body = family.Branches[1].Body;
        var nested = Assert.IsType<Algorithm.User>(body.Properties.Single(static p => p.Name == "G").Value);
        var group = Assert.IsType<ListValueParameterPattern>(nested.ParameterPatterns[0]);
        // The public placeholder view retains this membership from the raw deferred body.
        // No internal entry point or admission bypass installs the host-built DAG.
        var items = Assert.IsAssignableFrom<IList<ParameterPattern>>(group.Items);
        var budget = new PatternReadBudget(20_000);
        var shared = Diamond("sequence", Bottom(bottom), depth, budget);
        items[0] = shared;
        items[1] = shared;
        var result = await Evaluator.RunAsync(new Expr.AlgorithmExpr(parsed.Root));
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        Assert.Equal(new Result.Atom(7), result.Value);
        Assert.Equal(1, downloads);
        output.WriteLine($"deferred/{bottom}: depth {depth}, reads = {budget.Reads}, result = 7");
        // This route also completes module loading, detection, selection, rewriting and exposure.
        Assert.InRange(budget.Reads, 1, 2 * ReadsPerEdge * 2 * (depth + 1));
    }

    // ── 1. The output-sensitive walk is the per-occurrence flatten ──────────

    [Fact]
    public void OnTreesAndDags_TheBarrenSkippingWalk_IsTheFilteredFlatten()
    {
        var random = new Random(20261112);
        var sharedCases = 0;
        var barrenSkips = 0;
        Func<ParameterDeclaration, bool>?[] selectors =
        [
            null,
            static parameter => parameter.Name == "a",
            static parameter => parameter.Kind == ParameterKind.Collecting,
            static _ => false,
        ];
        for (var round = 0; round < 1000; round++)
        {
            var (dag, sharesNodes) = RandomDag(random);
            sharedCases += sharesNodes ? 1 : 0;
            var tree = dag.Select(CloneTree).ToArray();
            var context = $"round {round}: {string.Join(", ", tree.Select(static p => p.DisplayName))}";
            foreach (var select in selectors)
            {
                var expected = ParameterPattern.FlattenCaptures(tree).Where(parameter => select is null || select(parameter)).ToArray();
                Assert.True(expected.SequenceEqual(ParameterPattern.SelectCapturesSkippingBarrenNodes(tree, select), ReferenceEqualityComparer.Instance), context);
                var fromDag = ParameterPattern.SelectCapturesSkippingBarrenNodes(dag, select);
                Assert.True(expected.SequenceEqual(fromDag, ReferenceEqualityComparer.Instance), context);
                barrenSkips += sharesNodes && expected.Length < ParameterPattern.FlattenCaptures(dag).Count ? 1 : 0;
            }

            var user = new Algorithm.User(null, tree, [], [], [new Expr.Num(1)]);
            Assert.Equal(user.Params, ParameterPattern.CaptureNamesSkippingBarrenNodes(dag));
            Assert.Equal(user.Params, ParameterPattern.CaptureNamesSkippingBarrenNodes(tree));
            Assert.Equal(user.HasAnyParameter, user.ParameterCount != 0);
        }

        output.WriteLine($"1000 cases, {sharedCases} with shared nodes, {barrenSkips} filtered selections on shared DAGs");
        Assert.True(sharedCases > 500);
        Assert.True(barrenSkips > 200);
    }

    /// <summary>
    /// Parser-built signatures — explicit, structured, inferred, lifted and cycle-completed — get
    /// exactly the old per-occurrence names and provenance notes (same notes, same order, by
    /// reference): the projection change is invisible to every parsed program.
    /// </summary>
    [Theory]
    [InlineData("F(x, y) = x + y\nF(1, 2)")]
    [InlineData("F((a, b), [c, *d], *e) = a\nF((1, 2), [3])")]
    [InlineData("F = x + y\nG = F + z\nG(1, 2, 3)")]
    [InlineData("P(p) = p\nQ(p) = p\nA = B + P\nB = A + Q\n0")]
    [InlineData("Lib = { Get = valeu + 1 }\nH = Lib.Get + w\n0")]
    public void ParsedSignatures_KeepTheirPerOccurrenceNamesAndNotes(string source)
    {
        var parsed = SourceProvenance.ParseValid(source).Parsed;
        var users = 0;
        var noted = 0;
        foreach (var user in UserAlgorithms(parsed.Root))
        {
            users++;
            Assert.Equal(user.Params, ParameterPattern.CaptureNamesSkippingBarrenNodes(user.ParameterPatterns));
            var expected = ImplicitParameterProvenance.CollectFrom(user.Parameters);
            var actual = ImplicitParameterProvenance.CollectFromPatterns(user.ParameterPatterns);
            Assert.Equal(expected is null, actual is null);
            if (expected is null)
                continue;
            noted++;
            Assert.True(expected.SequenceEqual(actual!, ReferenceEqualityComparer.Instance), source);
            Assert.Equal(user.ParameterCount != 0, user.HasAnyParameter);
        }

        output.WriteLine($"{users} user algorithms, {noted} with provenance notes");
        Assert.True(users > 1);
    }

    [Fact]
    public void ProvenanceNotes_OfASharedSignatureHoldingParsedDeclarations_AreTheTreeNotesPerOccurrence()
    {
        // A host may splice a parsed (provenance-bearing) declaration into its own shared pattern.
        var parsed = SourceProvenance.ParseValid("F = x + y\n0").Parsed;
        var inferred = UserAlgorithms(parsed.Root).Single(static user => user.Params.SequenceEqual(["x", "y"]));
        var x = ((CaptureParameterPattern)inferred.ParameterPatterns[0]).Parameter;
        Assert.NotNull(x.InferredProvenance);

        ParameterPattern noted = new SequenceValueParameterPattern([new CaptureParameterPattern(x), new ListValueParameterPattern([])]);
        ParameterPattern[] Signature(ParameterPattern barren) => [new SequenceValueParameterPattern([barren, noted, barren]), noted];

        // The tree oracle at a small depth: the old per-occurrence projection of the cloned tree.
        var small = Signature(Diamond("list", new ListValueParameterPattern([]), 4, new PatternReadBudget(BudgetLimit)));
        var expected = ImplicitParameterProvenance.CollectFrom(new Algorithm.User(null, small.Select(CloneTree).ToArray(), [], [], [new Expr.Num(1)]).Parameters);
        Assert.Equal(2, expected!.Count);
        Assert.True(expected.SequenceEqual(ImplicitParameterProvenance.CollectFromPatterns(small)!, ReferenceEqualityComparer.Instance));

        // Deep: the same two notes, with work linear in the distinct nodes.
        foreach (var depth in new[] { 45, 90 })
        {
            var budget = new PatternReadBudget(BudgetLimit);
            var actual = ImplicitParameterProvenance.CollectFromPatterns(Signature(Diamond("list", new ListValueParameterPattern([]), depth, budget)));
            Assert.True(expected.SequenceEqual(actual!, ReferenceEqualityComparer.Instance));
            Assert.InRange(budget.Reads, 1, ReadsPerEdge * 2 * depth);
        }
    }

    // ── 2. Run routes whose report is small: linear in the distinct nodes ────

    public static TheoryData<string, string> SmallReportRoutes()
    {
        var data = new TheoryData<string, string>();
        foreach (var scenario in new[] { "property", "explicit", "tooMany" })
        foreach (var bottom in new[] { "x", "empty" })
            data.Add(scenario, bottom);
        // With a capture these two publish one name per occurrence (section 3).
        data.Add("block", "empty");
        data.Add("reduceInitial", "empty");
        data.Add("dotReceiver", "empty");
        return data;
    }

    [Theory]
    [MemberData(nameof(SmallReportRoutes))]
    public async Task SmallReports_OnASharedSignature_AreTheTreeReports_AndLinear(string scenario, string bottom)
    {
        // The tree oracle at a depth whose expansion is small: structure and rendered message.
        var expected = Report(Evaluator.Run(Root(scenario, Tree(Bottom(bottom), 4))));
        var small = Report(Evaluator.Run(Root(scenario, Diamond("sequence", Bottom(bottom), 4, new PatternReadBudget(BudgetLimit)))));
        Assert.Equal(expected, small);
        output.WriteLine($"{scenario}/{bottom}: {expected}");

        var treeRun = Evaluator.RunCountedObserved(Root(scenario, Tree(Bottom(bottom), 4)));
        var dagRun = Evaluator.RunCountedObserved(Root(scenario, Diamond("sequence", Bottom(bottom), 4, new PatternReadBudget(BudgetLimit))));
        Assert.Equal(treeRun.Budget.ConsumedSteps, dagRun.Budget.ConsumedSteps);
        Assert.Equal(treeRun.Budget.ConsumedExpressionCheckpoints, dagRun.Budget.ConsumedExpressionCheckpoints);
        Assert.Equal(treeRun.Budget.ConsumedStructuralWorkUnits, dagRun.Budget.ConsumedStructuralWorkUnits);
        Assert.Equal(treeRun.Budget.PeakDepth, dagRun.Budget.PeakDepth);

        var reads = new List<int>();
        foreach (var depth in Depths)
        {
            foreach (var route in new[] { "Run", "RunAsync", "RunFlat", "RunFlatAsync" })
            {
                var budget = new PatternReadBudget(BudgetLimit);
                var root = Root(scenario, Diamond("sequence", Bottom(bottom), depth, budget));
                var error = route switch
                {
                    "Run" => Evaluator.Run(root).Error,
                    "RunAsync" => (await Evaluator.RunAsync(root)).Error,
                    "RunFlat" => Evaluator.RunFlat(root).Error,
                    _ => (await Evaluator.RunFlatAsync(root)).Error,
                };
                Assert.Equal(Shape(Evaluator.Run(Root(scenario, Tree(Bottom(bottom), 4))).Error), Shape(error));
                Assert.InRange(budget.Reads, 1, ReadsPerEdge * 2 * depth);
                if (route == "Run")
                    reads.Add(budget.Reads);
            }
        }

        output.WriteLine($"{scenario}/{bottom}: Run reads at depths {string.Join("/", Depths)} = {string.Join(", ", reads)}");
        // Linear: doubling the depth at most doubles the reads, up to one level's constant.
        Assert.InRange(reads[3], 1, 2 * reads[2] + 2 * ReadsPerEdge);
        Assert.InRange(reads[1], 1, 2 * reads[0] + 2 * ReadsPerEdge);
    }

    // ── 3. Run routes that publish K names: proportional to K ────────────────

    [Fact]
    public async Task MemberNavigation_OverACaptureFreeSignature_DoesNotExpandItsPaths()
    {
        static Expr MemberRoot(ParameterPattern signature)
        {
            var member = new Algorithm.User(null, [], [], [], [new Expr.Num(42)]);
            var owner = new Algorithm.User(null, [signature], [], [new Property("V", member)], [new Expr.Num(1)]);
            return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("F", owner)],
                [new Expr.DotCall(new Expr.Resolve("F"), "V")]));
        }

        var tree = Evaluator.Run(MemberRoot(Tree(Bottom("empty"), 4)));
        Assert.True(tree.IsOk);
        foreach (var depth in Depths)
        {
            var budget = new PatternReadBudget(20_000);
            var result = Evaluator.Run(MemberRoot(Diamond("sequence", Bottom("empty"), depth, budget)));
            Assert.True(result.IsOk);
            Assert.Equal(tree.Value, result.Value);
            Assert.InRange(budget.Reads, 1, ReadsPerEdge * 2 * depth);
            output.WriteLine($"member navigation: depth {depth}, reads = {budget.Reads}, result = 42");
            var asyncBudget = new PatternReadBudget(20_000);
            var asyncResult = await Evaluator.RunAsync(MemberRoot(Diamond("sequence", Bottom("empty"), depth, asyncBudget)));
            Assert.True(asyncResult.IsOk);
            Assert.Equal(tree.Value, asyncResult.Value);
            Assert.InRange(asyncBudget.Reads, 1, ReadsPerEdge * 2 * depth);
        }
    }

    [Theory]
    [InlineData("block")]
    [InlineData("reduceInitial")]
    public void PerOccurrenceNameReports_OnASharedSignature_AreOutputSensitive(string scenario)
    {
        var tree = Report(Evaluator.Run(Root(scenario, Tree(Bottom("x"), 4))));
        Assert.Equal(tree, Report(Evaluator.Run(Root(scenario, Diamond("sequence", Bottom("x"), 4, new PatternReadBudget(BudgetLimit))))));

        foreach (var depth in new[] { 8, 12 })
        {
            var budget = new PatternReadBudget(BudgetLimit);
            var error = Evaluator.Run(Root(scenario, Diamond("sequence", Bottom("x"), depth, budget))).Error;
            var names = PublishedNames(error);
            var occurrences = 1 << depth;
            Assert.Equal(occurrences, names.Count);
            Assert.All(names, static name => Assert.Equal("x", name));
            output.WriteLine($"{scenario}: depth {depth}, K = {occurrences} published names, reads = {budget.Reads}");
            // Pattern-item reads track distinct input; names.Count tracks output separately.
            Assert.InRange(budget.Reads, 1, ReadsPerEdge * 2 * depth);
        }

        // A sparse DAG: one capture beside a deep shared capture-free group publishes one name.
        var sparseBudget = new PatternReadBudget(BudgetLimit);
        var sparse = new SequenceValueParameterPattern([Diamond("list", Bottom("empty"), 45, sparseBudget), new CaptureParameterPattern("x")]);
        Assert.Equal(["x"], PublishedNames(Evaluator.Run(Root(scenario, sparse)).Error));
        Assert.InRange(sparseBudget.Reads, 1, ReadsPerEdge * 2 * 45);
    }

    [Theory]
    [InlineData("block", 15)]
    [InlineData("block", 45)]
    [InlineData("reduceInitial", 15)]
    [InlineData("reduceInitial", 45)]
    public void SharedContributingTails_AreReadOnceWhileEveryOccurrenceIsPublished(string scenario, int tailDepth)
    {
        // A diamond over a long, single-capture tail. Re-expanding contributing nodes would
        // read the entire tail K times even though the report contains only K names.
        const int diamondDepth = 8;
        var budget = new PatternReadBudget(100_000);
        ParameterPattern tail = new CaptureParameterPattern("x");
        ParameterPattern empty = new ListValueParameterPattern([]);
        for (var level = 0; level < tailDepth; level++)
            tail = new ListValueParameterPattern(new BudgetedPatternItems<ParameterPattern>(empty, tail, budget));
        var signature = Diamond("sequence", tail, diamondDepth, budget);
        var names = PublishedNames(Evaluator.Run(Root(scenario, signature)).Error);
        Assert.Equal(1 << diamondDepth, names.Count);
        Assert.All(names, static name => Assert.Equal("x", name));
        output.WriteLine($"{scenario}: tail depth {tailDepth}, K = {names.Count}, reads = {budget.Reads}");
        Assert.InRange(budget.Reads, 1, ReadsPerEdge * 2 * (tailDepth + diamondDepth));
    }

    // ── 4. Routes that render the pattern: proportional to the rendered text ─

    /// <summary>
    /// A single-argument shape rejection quotes the pattern (<c>sequence pattern `((x, x), …)`</c>)
    /// and the semantic model publishes the rendered signature (<see cref="PropertySignatureInfo.DisplayText"/>):
    /// both outputs hold the expanded pattern, so their work is bounded by the rendered size R,
    /// never avoidable without changing what they publish.
    /// </summary>
    [Fact]
    public void RenderedPatternOutputs_AreBoundedByTheirRenderedSize()
    {
        foreach (var depth in new[] { 8, 11 })
        {
            var expandedNodes = (1 << (depth + 1)) - 1;
            var budget = new PatternReadBudget(BudgetLimit);
            var callError = Evaluator.Run(Root("oneArgument", Diamond("sequence", Bottom("empty"), depth, budget))).Error;
            var message = KatLangError.FromEvalError(callError).Message;
            Assert.Contains("sequence pattern `((", message);
            Assert.True(message.Length >= expandedNodes, $"{message.Length} < {expandedNodes}");
            output.WriteLine($"one-argument call: depth {depth}, message length {message.Length}, reads {budget.Reads}");
            Assert.InRange(budget.Reads, 1, 4 * expandedNodes);

            var modelBudget = new PatternReadBudget(BudgetLimit);
            var model = SemanticModelBuilder.Build(ModelRoot(Diamond("sequence", Bottom("empty"), depth, modelBudget)));
            var resolved = model.IdentifierResolutions.Single(static resolution => resolution.Occurrence.Name == "F").ResolvedProperty!;
            var rendered = resolved.Signatures.Sum(static signature => signature.DisplayText.Length);
            Assert.Empty(resolved.Parameters);
            Assert.True(rendered >= expandedNodes, $"{rendered} < {expandedNodes}");
            output.WriteLine($"semantic model: depth {depth}, rendered signature length {rendered}, reads {modelBudget.Reads}");
            Assert.InRange(modelBudget.Reads, 1, 16 * expandedNodes);
        }
    }

    // ── 5. Ownership and stack ──────────────────────────────────────────────

    [Fact]
    public void ColdOccurrenceTemplateFacts_KeepTheirContract_WithoutExpandingCaptureFreePaths()
    {
        foreach (var depth in new[] { 15, 90 })
        {
            var budget = new PatternReadBudget(20_000);
            var template = ImplicitSignatureTemplate.Flat([Diamond("list", Bottom("empty"), depth, budget)]);
            Assert.Null(template.ComputedFacts);
            var facts = template.Facts;
            Assert.Empty(facts.Captures);
            Assert.Empty(facts.Names);
            Assert.Empty(facts.NameSet);
            Assert.Equal(0, facts.CaptureCount);
            Assert.True(facts.HasEmptyGroup);
            Assert.False(facts.HasRecoveryPlaceholder);
            var coldReads = budget.Reads;
            Assert.Same(facts, template.ComputedFacts);
            Assert.Same(facts, template.Facts);
            Assert.Equal(coldReads, budget.Reads);
            Assert.InRange(coldReads, 1, ReadsPerEdge * 2 * depth);
        }
    }

    [Fact]
    public void BarrenMemo_IsCallLocal_AndObservesHostMutationsBetweenCalls()
    {
        var items = new List<ParameterPattern> { new ListValueParameterPattern([]) };
        var shared = new ListValueParameterPattern(items);
        ParameterPattern[] patterns = [new SequenceValueParameterPattern([shared, shared]), shared];
        var callee = new Algorithm.User(null, patterns, [], [], [new Expr.Num(1)]);
        Assert.Empty(ParameterPattern.CaptureNamesSkippingBarrenNodes(patterns));
        Assert.False(callee.HasAnyParameter);

        // The host fills the shared group: all three occurrences now contribute.
        items.Add(new CaptureParameterPattern("q"));
        Assert.Equal(["q", "q", "q"], ParameterPattern.CaptureNamesSkippingBarrenNodes(patterns));
        Assert.Equal(callee.Params, ParameterPattern.CaptureNamesSkippingBarrenNodes(patterns));
        Assert.True(callee.HasAnyParameter);
        Assert.Equal(["q", "q", "q"], PublishedNames(Evaluator.Run(Root("block", patterns)).Error));

        items.RemoveAt(1);
        Assert.Empty(ParameterPattern.CaptureNamesSkippingBarrenNodes(patterns));
        Assert.Empty(PublishedNames(Evaluator.Run(Root("block", patterns)).Error));
    }

    [Fact]
    public void BarrenSkippingWalk_IsIterative_OnAVeryDeepHostPattern()
    {
        ParameterPattern chain = new CaptureParameterPattern("deep");
        ParameterPattern empty = new ListValueParameterPattern([]);
        for (var level = 0; level < 200_000; level++)
            chain = new ListValueParameterPattern([empty, chain]);
        var captures = ParameterPattern.SelectCapturesSkippingBarrenNodes([chain]);
        Assert.Equal("deep", Assert.Single(captures).Name);
        Assert.Empty(ParameterPattern.SelectCapturesSkippingBarrenNodes([chain], static _ => false));
    }

    // ── Roots ───────────────────────────────────────────────────────────────

    private static Expr Root(string scenario, ParameterPattern shared) => Root(scenario, [shared]);

    private static Expr Root(string scenario, IReadOnlyList<ParameterPattern> signature)
    {
        var callee = new Algorithm.User(null, signature, [], [], [new Expr.Num(1)]) { HasExplicitParameterList = scenario == "explicit" };
        Expr result = scenario switch
        {
            "tooMany" => new Expr.Call(new Expr.Resolve("F"), [new Expr.Num(1), new Expr.Num(2)]),
            "oneArgument" => new Expr.Call(new Expr.Resolve("F"), [new Expr.Num(1)]),
            "block" => new Expr.AlgorithmExpr(callee),
            "reduceInitial" => new Expr.Call(new Expr.Resolve("reduce"), [new Expr.Num(1), new Expr.Resolve("F"), new Expr.Resolve("F")]),
            "dotReceiver" => new Expr.DotCall(new Expr.Resolve("F"), "x"),
            _ => new Expr.Resolve("F"),
        };
        return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("F", callee)], [result]));
    }

    private static Algorithm.User ModelRoot(ParameterPattern shared)
    {
        var callee = new Algorithm.User(null, [shared], [], [], [new Expr.Num(1)]);
        return new Algorithm.User(null, [], [], [new Property("F", callee)],
            [new Expr.Resolve("F") { Span = new SourceSpan(1, 1, 1, 2) }]);
    }

    // ── Reports ─────────────────────────────────────────────────────────────

    // The structured shape without rendered text: kinds, counts, contexts' name counts, notes.
    private static string Shape(EvalError error) => error switch
    {
        EvalError.WithContext context => $"{context.ErrorContext.GetType().Name}[{ContextNames(context.ErrorContext)?.Count}] > {Shape(context.Inner)}",
        EvalError.ArityMismatch arity => $"ArityMismatch {arity.Expected}/{arity.Actual} notes={arity.InferredImplicitParameters?.Count}",
        EvalError.UnresolvedImplicitParams missing => $"UnresolvedImplicitParams {missing.ParamNames.Count} notes={missing.InferredImplicitParameters?.Count}",
        _ => error.GetType().Name,
    };

    private static IReadOnlyList<string>? ContextNames(ErrorContext context) => context switch
    {
        ImplicitParameterContext implicitContext => implicitContext.ParamNames,
        ReduceInitialAccumulatorContext reduce => reduce.RequiredParameterNames,
        _ => null,
    };

    private static string Report(EvalResult<Result> result)
    {
        Assert.True(result.IsError);
        return $"{Shape(result.Error)} | {KatLangError.FromEvalError(result.Error).Message}";
    }

    private static IReadOnlyList<string> PublishedNames(EvalError error)
    {
        for (var current = error; ;)
        {
            if (current is EvalError.WithContext context)
            {
                if (ContextNames(context.ErrorContext) is { } names)
                    return names;
                current = context.Inner;
                continue;
            }

            return current is EvalError.UnresolvedImplicitParams missing ? missing.ParamNames : throw new InvalidOperationException($"no names: {error}");
        }
    }

    // ── Shapes ──────────────────────────────────────────────────────────────

    private static ParameterPattern Bottom(string bottom)
        => bottom == "empty" ? new ListValueParameterPattern([]) : new CaptureParameterPattern("x");

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
    private static ParameterPattern Tree(ParameterPattern bottom, int levels)
        => levels == 0
            ? bottom is CaptureParameterPattern capture ? new CaptureParameterPattern(capture.Name) : new ListValueParameterPattern([])
            : new SequenceValueParameterPattern([Tree(bottom, levels - 1), Tree(bottom, levels - 1)]);

    // A tree copy: a fresh structural node per occurrence, keeping each leaf's declaration.
    private static ParameterPattern CloneTree(ParameterPattern pattern)
        => ParameterPattern.StructuralItems(pattern) is { } items
            ? ParameterPattern.WithStructuralItems(pattern, items.Select(CloneTree).ToArray())
            : new CaptureParameterPattern(((CaptureParameterPattern)pattern).Parameter);

    private static IEnumerable<Algorithm.User> UserAlgorithms(Algorithm root)
    {
        var pending = new Stack<Algorithm>();
        pending.Push(root);
        while (pending.TryPop(out var algorithm))
        {
            if (algorithm is not Algorithm.User user)
                continue;
            yield return user;
            foreach (var property in user.Properties)
                pending.Push(property.Value);
        }
    }

    private static readonly string[] Names = ["a", "b", "c"];
    private static readonly string[] KindNames = ["sequence", "list", "unpack"];

    // Uneven multi-parent DAGs: leaves and capture-free groups shared at several heights.
    private static (ParameterPattern[] Patterns, bool SharesNodes) RandomDag(Random random)
    {
        var pool = new List<(ParameterPattern Node, int Height)>();
        var leaves = random.Next(1, 4);
        for (var index = 0; index < leaves; index++)
        {
            var kind = random.Next(3) == 0 ? ParameterKind.Collecting : ParameterKind.Normal;
            pool.Add((new CaptureParameterPattern(Names[random.Next(Names.Length)], Kind: kind), 0));
        }

        for (var index = random.Next(0, 3); index > 0; index--)
            pool.Add((Structural(KindNames[random.Next(KindNames.Length)], []), 1));

        var uses = new Dictionary<ParameterPattern, int>(ReferenceEqualityComparer.Instance);
        var structural = random.Next(1, 8);
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
}
