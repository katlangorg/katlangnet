using System.Numerics;
using KatLang.Evaluation;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// SEC-F3 — a materialized deferred module body passes the EVALUATOR's structural admission
/// before the evaluator consumes it: the evaluator-weighted profile, the consuming run's
/// effective <see cref="EvaluationLimits.MaxAstDepth"/>, and the weighted position its
/// placeholder occupies (<see cref="DeferredBodyAdmission"/>). Materialization's own gates are
/// the front end's (<see cref="AstConsumerProfile.FullyRecursive"/>), which a dot-call chain
/// passes at a third of its evaluator weight. The reference verdict is ordinary admission of the
/// COMPOSED tree — the root with every reached placeholder replaced by its materialized body —
/// so the deferred and eager boundaries are pinned to coincide. Every downloader is in-memory.
/// </summary>
public class DeferredBodyEvaluatorAdmissionTests
{
    private const string Deep = "https://katlang.org/admission/deep.kat";
    private const string Shallow = "https://katlang.org/admission/shallow.kat";
    private const string Missing = "https://katlang.org/admission/missing.kat";
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);

    // `1.count.count…` is 1 at every length; each link weighs 3 evaluator units and 1 front-end unit.
    private static string DotChainModule(int links)
        => "public X = 1" + string.Concat(Enumerable.Repeat(".count", links)) + "\n";

    // A unary chain weighs one unit per link on every profile and evaluates on the iterative spine
    // machine, so a body near the ceiling still produces its value on a test thread.
    private static string UnaryChainModule(int links)
        => "public X = " + new string('-', 2 * links) + "1\n";

    private static string Family(string url, string output) => $"F(0) = 42\nF(n) = {{ open '{url}'\nX }}\n{output}";

    private sealed class Modules(params (string Url, string Source)[] files)
    {
        private readonly Dictionary<string, string> _files = files.ToDictionary(f => f.Url, f => f.Source, StringComparer.Ordinal);

        public List<string> Events { get; } = [];

        public int Fetches => Events.Count(e => e.StartsWith("fetch", StringComparison.Ordinal));

        public RunOptions Options(EvaluationLimits? limits = null) => new()
        {
            AllowedHosts = ["katlang.org"],
            EvaluationLimits = limits,
            HostOperations = HostOperations.Create(HostOperation.Create("Tick", (_, _) => { Events.Add("tick"); return new Result.Atom(42); })),
            DownloadCode = (url, _) =>
            {
                Events.Add("fetch " + url);
                return _files.TryGetValue(url, out var source) ? ValueTask.FromResult(source) : throw new Exception($"404: {url}");
            },
        };
    }

    private static Task<EvalResult<Evaluator.CountedResult>> RunDirect(Algorithm root, Modules modules, EvaluationLimits? limits = null, bool suspending = false)
        => Evaluator.RunCountedAsync(
            new Expr.AlgorithmExpr(root),
            suspending ? new SuspendingAsyncZeroArgPropertyResultCache() : new PassThroughAsyncZeroArgPropertyResultCache(),
            limits,
            modules.Options().HostOperations).AsTask();

    // ── Reference: ordinary admission of the composed tree ──────────────────

    /// <summary>The root with every materialized placeholder (recursively) replaced by its body.</summary>
    private static Algorithm Composed(Algorithm algorithm)
    {
        if (algorithm.DeferredRegion is { } region && region.TryGetMaterialized(out var body))
            return Composed(body switch
            {
                Algorithm.User user => user with { Parent = algorithm.Parent },
                Algorithm.Conditional family => family with { Parent = algorithm.Parent },
                Algorithm.Alias alias => alias with { Parent = algorithm.Parent },
                Algorithm.Builtin => body,
            });

        return algorithm switch
        {
            Algorithm.Conditional conditional => conditional with
            {
                Opens = conditional.Opens.Select(ComposedOpen).ToList(),
                Branches = conditional.Branches.Select(b => b with { Body = Composed(b.Body) }).ToList(),
            },
            Algorithm.User user => user with
            {
                Opens = user.Opens.Select(ComposedOpen).ToList(),
                Properties = user.Properties.Select(p => p with { Value = Composed(p.Value) }).ToList(),
            },
            _ => algorithm,
        };
    }

    // An elaborated `open 'url'` holds the loaded module as an algorithm expression.
    private static Expr ComposedOpen(Expr open)
        => open is Expr.AlgorithmExpr block ? block with { Algorithm = Composed(block.Algorithm) } : open;

    private static bool ComposedAdmitted(Algorithm root, int limit)
    {
        var composed = new Expr.AlgorithmExpr(Composed(root));
        // The reference is only meaningful if it replaced every materialized placeholder.
        Assert.DoesNotContain(Regions(composed), region => region.IsMaterialized);
        return AstStructuralPreflight.Check(composed, limit, AstConsumerProfile.EvaluatorIterativeJoinSpines) is null;
    }

    /// <summary>Every region reachable through the structural children, and through every materialized body.</summary>
    private static List<DeferredModuleRegion> Regions(object root)
    {
        var regions = new List<DeferredModuleRegion>();
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>([root]);
        while (pending.TryPop(out var node))
        {
            if (!seen.Add(node))
                continue;
            if (node is Algorithm { DeferredRegion: { } region })
            {
                if (!regions.Contains(region)) regions.Add(region);
                if (region.TryGetMaterialized(out var body)) pending.Push(body);
            }

            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
                pending.Push(child);
        }

        return regions;
    }

    private static DeferredModuleRegion OnlyRegion(Algorithm root) => Assert.Single(Regions(root));

    private static void AssertDepthRejected(EvalResult<Evaluator.CountedResult> result, int limit)
    {
        Assert.True(result.IsError, "expected a structural rejection");
        var error = Assert.IsType<EvalError.AstDepthLimitExceeded>(result.Error);
        Assert.Equal(limit, error.Limit);
        Assert.True(error.IsResourceLimit);
        Assert.Equal(KatLangErrorCode.AstDepthLimitExceeded, error.Code);
    }

    /// <summary>
    /// An ADMITTED tree's outcome: its exact value, or one of the established controlled runtime
    /// stops an at-ceiling tree may meet on a small test-thread stack (host headroom is not
    /// semantic, Q-09; <c>AstStructuralDepthTests</c> applies the same tolerance) — never a
    /// structural rejection.
    /// </summary>
    private static void AssertAdmittedOutcome(EvalResult<Evaluator.CountedResult> result, decimal expected)
    {
        if (!result.IsError)
        {
            Assert.Equal([(Decimal128)expected], result.Value.Value.ToAtoms());
            return;
        }

        var leaf = result.Error;
        while (leaf is EvalError.WithContext(_, var inner))
            leaf = inner;
        Assert.True(leaf is EvalError.EvaluationStackExhausted or EvalError.EvaluationDepthExceeded, leaf.ToString());
    }

    private static void AssertValue(EvalResult<Evaluator.CountedResult> result, decimal expected)
    {
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([(Decimal128)expected], result.Value.Value.ToAtoms());
    }

    // ── T1: the evaluator-weighted profile, not the front end's ─────────────

    [Fact]
    public async Task T1_DotChainBody_PassesTheFrontEndGates_ButIsRejectedByEvaluatorAdmission()
    {
        var modules = new Modules((Deep, DotChainModule(120)));
        var provenance = await SourceProvenance.ParseValidAsync(Family(Deep, "F(1)"), modules.Options());
        var region = OnlyRegion(provenance.Root);

        var result = await RunDirect(provenance.Root, modules);

        AssertDepthRejected(result, EvaluationLimits.MaxSupportedAstDepth);
        // Materialization SUCCEEDED: every front-end gate admitted the body, and it stays cached.
        Assert.True(region.TryGetMaterialized(out var body));
        Assert.Equal(1, region.MaterializationAttempts);
        Assert.Null(AstStructuralPreflight.Check(body, EvaluationLimits.MaxSupportedAstDepth - region.Depth, AstConsumerProfile.FullyRecursive));
        Assert.False(ComposedAdmitted(provenance.Root, EvaluationLimits.MaxSupportedAstDepth));
    }

    [Fact]
    public async Task T1_Engine_ReportsTheSameStructuralErrorAsTheEagerEquivalent_AtTheImportSite()
    {
        var modules = new Modules((Deep, DotChainModule(120)));
        var deferred = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(Family(Deep, "F(1)"), modules.Options()));
        var eager = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync($"open '{Deep}'\nX", modules.Options()));

        var deferredError = Assert.Single(deferred.Errors);
        var eagerError = Assert.Single(eager.Errors);
        Assert.Equal(KatLangErrorCode.AstDepthLimitExceeded, eagerError.Code);
        Assert.Equal(eagerError.Code, deferredError.Code);
        Assert.Equal(eagerError.Message, deferredError.Message);
        Assert.True(deferredError.IsResourceLimit);
        // Module content is locationless: both positions are the written `open` URL of the importing document.
        var span = Assert.NotNull(deferredError.Span);
        Assert.Equal(2, span.Start.Line);
        Assert.Equal(Family(Deep, "").Split('\n')[1].IndexOf('\'') + 1, span.Start.Column);
    }

    [Fact]
    public async Task T1_DeferredAndComposedVerdicts_CoincideAcrossTheDotChainBoundary()
    {
        var verdicts = new List<bool>();
        for (var links = 90; links <= 102; links++)
        {
            var modules = new Modules((Deep, DotChainModule(links)));
            var provenance = await SourceProvenance.ParseValidAsync(Family(Deep, "F(1)"), modules.Options());
            var result = await RunDirect(provenance.Root, modules);
            var admitted = ComposedAdmitted(provenance.Root, EvaluationLimits.MaxSupportedAstDepth);
            if (admitted) AssertAdmittedOutcome(result, 1);
            else AssertDepthRejected(result, EvaluationLimits.MaxSupportedAstDepth);
            verdicts.Add(admitted);
        }

        // The window straddles the boundary: the largest accepted body still evaluates.
        Assert.Contains(true, verdicts);
        Assert.Contains(false, verdicts);
    }

    // ── T2: the consuming run's configured limit ────────────────────────────

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    public async Task T2_ConfiguredLowerLimit_IsEnforcedOnTheDeferredBody(int route)
    {
        const int Limit = 100;
        var limits = new EvaluationLimits { MaxAstDepth = Limit };
        var modules = new Modules((Deep, DotChainModule(40)));
        var source = Family(Deep, "F(1)");
        if (route == 0)
        {
            var failure = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(source, modules.Options(limits)));
            var error = Assert.Single(failure.Errors);
            Assert.Equal(KatLangErrorCode.AstDepthLimitExceeded, error.Code);
            Assert.True(error.IsResourceLimit);
            Assert.Contains($"{Limit} weighted units", error.Message, StringComparison.Ordinal);
            Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, modules.Options()));
            return;
        }

        var provenance = await SourceProvenance.ParseValidAsync(source, modules.Options());
        AssertDepthRejected(await RunDirect(provenance.Root, modules, limits, suspending: route == 2), Limit);
        Assert.False(ComposedAdmitted(provenance.Root, Limit));
        Assert.True(ComposedAdmitted(provenance.Root, EvaluationLimits.MaxSupportedAstDepth));
        AssertValue(await RunDirect(provenance.Root, modules, suspending: route == 2), 1);
    }

    // ── T3: the enclosing structure contributes weighted depth ──────────────

    private static string Nested(int levels, string inner)
    {
        for (var level = 0; level < levels; level++)
            inner = $"P{level} = {{\n{inner}\n}}\nP{level}";
        return inner;
    }

    [Fact]
    public async Task T3_ABodySafeInIsolation_IsRejectedWhereTheEnclosingTreeTakesItOverTheLimit()
    {
        const int Links = 93;
        var verdicts = new List<bool>();
        foreach (var levels in new[] { 0, 4, 8, 12, 16, 20, 24 })
        {
            var modules = new Modules((Deep, DotChainModule(Links)));
            var provenance = await SourceProvenance.ParseValidAsync(Nested(levels, Family(Deep, "F(1)")), modules.Options());
            var region = OnlyRegion(provenance.Root);
            var result = await RunDirect(provenance.Root, modules);
            Assert.True(region.TryGetMaterialized(out var body));
            // The body ALONE is always within the ceiling at the root position.
            Assert.Null(AstStructuralPreflight.Check(body, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.EvaluatorIterativeJoinSpines));
            var admitted = ComposedAdmitted(provenance.Root, EvaluationLimits.MaxSupportedAstDepth);
            if (admitted) AssertAdmittedOutcome(result, 1);
            else AssertDepthRejected(result, EvaluationLimits.MaxSupportedAstDepth);
            verdicts.Add(admitted);
        }

        Assert.True(verdicts[0]);
        Assert.False(verdicts[^1]);
    }

    [Fact]
    public async Task T3_NearBoundary_TheDeepestAcceptedNestingStillEvaluates_AndOneMoreLevelIsRejected()
    {
        // The enclosing weight comes from a deep STATIC occurrence of the shared family, while the
        // run selects it through the shallow one: the evaluator's own stack stays shallow, so the
        // deepest admitted composition evaluates to its exact value on a test thread.
        const int Links = 110;
        var modules = new Modules((Deep, UnaryChainModule(Links)));
        var provenance = await SourceProvenance.ParseValidAsync(Family(Deep, "F(1)"), modules.Options());
        int? lastAccepted = null;
        for (var levels = 0; levels <= 120; levels++)
        {
            var root = WithDeepOccurrence(provenance.Root, levels);
            var result = await RunDirect(root, modules);
            if (ComposedAdmitted(root, EvaluationLimits.MaxSupportedAstDepth))
            {
                AssertValue(result, 1);
                lastAccepted = levels;
                continue;
            }

            AssertDepthRejected(result, EvaluationLimits.MaxSupportedAstDepth);
            Assert.Equal(levels - 1, lastAccepted);
            Assert.True(lastAccepted > 0, "the body alone must be admitted at the root position");
            return;
        }

        Assert.Fail("the nesting sweep never crossed the limit");
    }

    /// <summary>The root with the SAME family object also placed under <paramref name="levels"/> nested blocks (host composition).</summary>
    private static Algorithm.User WithDeepOccurrence(Algorithm.User root, int levels)
    {
        var family = root.Properties.Single(p => p.Name == "F");
        Algorithm deep = new Algorithm.User(null, [], [], [family], OutputBundle.Empty);
        for (var level = 0; level < levels; level++)
            deep = new Algorithm.User(null, [], [], [new Property("W", deep)], OutputBundle.Empty);
        return root with { Properties = [.. root.Properties, new Property("Deep", deep)] };
    }

    [Fact]
    public async Task T3_SharedFamily_IsJudgedAtItsDeepestOccurrence_EvenWhenSelectedThroughTheShallowOne()
    {
        var modules = new Modules((Deep, DotChainModule(80)));
        var provenance = await SourceProvenance.ParseValidAsync(Family(Deep, "F(1)"), modules.Options());
        var root = WithDeepOccurrence(provenance.Root, 60);

        AssertDepthRejected(await RunDirect(root, modules), EvaluationLimits.MaxSupportedAstDepth);
        Assert.False(ComposedAdmitted(root, EvaluationLimits.MaxSupportedAstDepth));
        // The same cached body, consumed by the unshared root, is admitted.
        AssertAdmittedOutcome(await RunDirect(provenance.Root, modules), 1);
        Assert.Equal(1, modules.Fetches);
    }

    [Theory]
    [InlineData(60)]
    [InlineData(80)]
    [InlineData(95)]
    [InlineData(99)]
    public async Task T3_NestedRegion_IsJudgedAtThePrefixItsEnclosingMaterializedBodyGivesIt(int innerLinks)
    {
        // The inner family exists only inside the OUTER region's materialized body.
        var modules = new Modules((Shallow, "public S = 0"), (Deep, DotChainModule(innerLinks)));
        var source = $"F(0) = {{\n  open '{Shallow}'\n  {Nested(6, $"G(0) = 0\nG(n) = {{ open '{Deep}'\nX + S }}\nG(1)")}\n}}\nF(1) = 0\nF(0)";
        var provenance = await SourceProvenance.ParseValidAsync(source, modules.Options());

        var result = await RunDirect(provenance.Root, modules);

        var regions = Regions(provenance.Root).Distinct().ToList();
        Assert.Equal(2, regions.Count);
        Assert.All(regions, region => Assert.True(region.IsMaterialized));
        if (ComposedAdmitted(provenance.Root, EvaluationLimits.MaxSupportedAstDepth)) AssertAdmittedOutcome(result, 1);
        else AssertDepthRejected(result, EvaluationLimits.MaxSupportedAstDepth);
    }

    [Theory]
    [InlineData(130, false)]
    [InlineData(138, false)]
    [InlineData(141, true)]
    [InlineData(144, true)]
    public async Task T3_ModuleFamilyReachedThroughTwoMaterializedBodies_IsJudgedAgainAtTheDeeperPrefix(int innerLinks, bool rejected)
    {
        // One module unit holds a deferred family G, opened at the top of a shallow deferred body
        // (F) and under twelve nested blocks of a second one (H). The program unit is shared, so
        // both bodies reach the SAME G placeholder: G is first admitted at F's prefix, then H's
        // admission raises G's recorded prefix and G's next consumption is judged again there.
        const string Module = "https://katlang.org/admission/module.kat";
        var modules = new Modules(
            (Module, $"public G(0) = 0\npublic G(n) = {{ open '{Deep}'\nX }}"),
            (Deep, UnaryChainModule(innerLinks)));
        var declarations = $"F(0) = {{ open '{Module}'\nG(1) }}\nF(1) = 0\n"
            + $"H(0) = {{ {Nested(12, $"open '{Module}'\nG(1)")} }}\nH(1) = 0\n";
        var provenance = await SourceProvenance.ParseValidAsync(declarations + "F(0) + H(0)", modules.Options());

        var result = await RunDirect(provenance.Root, modules);

        Assert.Equal(3, Regions(provenance.Root).Distinct().Count());
        Assert.Equal(!rejected, ComposedAdmitted(provenance.Root, EvaluationLimits.MaxSupportedAstDepth));
        if (rejected) AssertDepthRejected(result, EvaluationLimits.MaxSupportedAstDepth);
        else AssertValue(result, 2);

        // Control: through the shallow body alone, G's body is admitted at every size here.
        var shallow = await SourceProvenance.ParseValidAsync(declarations + "F(0)", modules.Options());
        AssertValue(await RunDirect(shallow.Root, modules), 1);
    }

    [Fact]
    public async Task T3_ReparentedPlaceholder_IsJudgedWithTheParentTheEvaluatorConsumes()
    {
        const int Limit = 100;
        var modules = new Modules((Deep, "public X = 1"));
        var syntax = Parser.ParseSyntax(Family(Deep, "F(1)"));
        Assert.False(syntax.HasErrors);
        var family = Assert.IsType<Algorithm.Conditional>(syntax.Root.Properties.Single(p => p.Name == "F").Value);
        var branch = family.Branches[1];
        var body = Assert.IsType<Algorithm.User>(branch.Body);
        ScopeCtx? originalParent = null;
        for (var level = 0; level < 80; level++)
            originalParent = new ScopeCtx(originalParent, [], []);
        family = family with { Branches = [family.Branches[0], branch with { Body = body with { Parent = originalParent } }] };
        var diagnostics = new DiagnosticBag();
        var loaded = await new ModuleLoader(diagnostics, modules.Options().DownloadCode!).ElaborateAsync(
            syntax.Root with { Properties = [new Property("F", family)] });
        var (detected, detectionDiagnostics) = ParameterDetector.Detect(loaded);
        Assert.Empty(detectionDiagnostics);
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, diagnostics: diagnostics);
        new ParameterPropertyCollisionValidator(diagnostics).VisitAlgorithm(resolved);
        var exposed = Assert.IsType<Algorithm.User>(PropertyExposureResolver.Resolve(resolved));
        Assert.Empty(diagnostics);

        // Ordinary placeholder views preserve the region while replacing its parent. Both
        // consumption routes replace the materialized body's original parent before using it.
        family = Assert.IsType<Algorithm.Conditional>(exposed.Properties.Single(p => p.Name == "F").Value);
        body = Assert.IsType<Algorithm.User>(family.Branches[1].Body);
        Assert.NotNull(body.DeferredRegion);
        family = family with { Branches = [family.Branches[0], family.Branches[1] with { Body = body with { Parent = null } }] };
        var root = WithDeepOccurrence(exposed with { Properties = [new Property("F", family)] }, 25);
        Assert.Null(AstStructuralPreflight.Check(new Expr.AlgorithmExpr(root), Limit, AstConsumerProfile.EvaluatorIterativeJoinSpines));

        AssertValue(await RunDirect(root, modules, new EvaluationLimits { MaxAstDepth = Limit }), 1);
        Assert.True(ComposedAdmitted(root, Limit));
        Assert.Equal(1, modules.Fetches);
    }

    private sealed class ReadCountingList<T>(IReadOnlyList<T> items) : IReadOnlyList<T>
    {
        public int Reads { get; private set; }
        public int Count => items.Count;
        public T this[int index] { get { Reads++; return items[index]; } }
        public IEnumerator<T> GetEnumerator() => items.GetEnumerator();
        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    [Theory]
    [InlineData(16, false)]
    [InlineData(32, false)]
    [InlineData(16, true)]
    [InlineData(32, true)]
    public void T3_SharedModulePayload_IsNotRescannedForEveryDeferredBody(int regionCount, bool nested)
    {
        // Observe actual member reads at the admission boundary. Distinct deferred bodies
        // share one module's declarations, as real module-unit splices do. Work must follow
        // the unique structural graph rather than regionCount times the shared payload.
        var members = new ReadCountingList<Property>(Enumerable.Range(0, regionCount * 64)
            .Select(i => new Property($"P{i}", new Algorithm.User(null, [], [], [], [new Expr.Num(i)]))).ToArray());
        var raw = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        var loader = new ModuleLoader(new DiagnosticBag(), (_, _) => ValueTask.FromResult("public X = 1"));
        var nestedRegion = new DeferredModuleRegion(loader, raw, ModuleLoader.LoadContext.PropertyDef, 0, 0, null);
        var shared = new Algorithm.User(null, [], nested ? [new Expr.AlgorithmExpr(raw with { DeferredRegion = nestedRegion })] : [],
            members, [new Expr.Num(1)]);
        var regions = Enumerable.Range(0, regionCount).Select(_ => new DeferredModuleRegion(
            loader, raw, ModuleLoader.LoadContext.PropertyDef, 0, 0, null)).ToArray();
        var root = new Expr.AlgorithmExpr(raw with
        {
            Properties = regions.Select((region, i) => new Property($"F{i}", raw with { DeferredRegion = region })).ToArray(),
        });
        Assert.Null(AstStructuralPreflight.Check(root, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.EvaluatorIterativeJoinSpines));
        var admission = new DeferredBodyAdmission(root, EvaluationLimits.MaxSupportedAstDepth);
        foreach (var region in regions)
            Assert.Null(admission.Admit(region, raw with { Properties = [new Property("Module", shared)] }));

        Assert.InRange(members.Reads, members.Count, 8 * members.Count);
    }

    [Fact]
    public void T3_SharedMemo_RejectionKeepsTheFreshChecksGroupingSlotAndSpan()
    {
        var payload = SourceProvenance.ParseValid(new string('-', 20) + "1").Root.Output[0];
        var arguments = new OutputBundle([payload]);
        var memo = new AstStructuralPreflight.DeferredAdmissionMemo();
        Assert.Null(AstStructuralPreflight.CheckDeferredBody(arguments, 100, memo, out _));
        var first = new Expr.Call(new Expr.Resolve("count"), arguments);
        Expr second = new Expr.Call(new Expr.Resolve("count"), arguments);
        for (var level = 0; level < 10; level++)
            second = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [second]));
        var body = new Algorithm.User(null, [], [], [], [first, second]);

        var expected = Assert.IsType<AstStructuralRejection>(AstStructuralPreflight.Check(
            body, 40, AstConsumerProfile.EvaluatorIterativeJoinSpines));
        Assert.NotNull(expected.Span);
        Assert.Equal(expected, AstStructuralPreflight.CheckDeferredBody(body, 40, memo, out _));
    }

    [Fact]
    public async Task T7_StructuralCycle_IsRetainedEvenThoughItIsNotAnOrdinaryResourceLimit()
    {
        var modules = new Modules((Deep, "public X = 1"));
        var provenance = await SourceProvenance.ParseValidAsync(Family(Deep, "F(1)"), modules.Options());
        var members = new List<Property>();
        var cyclicBody = new Algorithm.User(null, [], [], members, [new Expr.Num(1)]);
        members.Add(new Property("Self", cyclicBody));
        var budget = EvaluationBudget.Create(null);
        budget.RecordDeferredBodyAdmission(new Expr.AlgorithmExpr(provenance.Root), EvaluationLimits.MaxSupportedAstDepth);

        // Directly exercise the structural gate: no recursive consumer sees this host-built
        // cycle, and an internal receiver cannot turn its refusal into a continuing run.
        var rejection = Assert.IsType<EvalError.AstCycleDetected>(budget.AdmitDeferredBody(OnlyRegion(provenance.Root), cyclicBody));
        Assert.Same(rejection, budget.CheckContinuation());
        Assert.Equal(0, modules.Fetches);
    }

    // ── T4: one cached materialization, two runs, two limits ────────────────

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public async Task T4_CachedBody_IsJudgedByEachRunsOwnLimit_InEitherOrder(bool permissiveFirst)
    {
        var restrictive = new EvaluationLimits { MaxAstDepth = 100 };
        var modules = new Modules((Deep, DotChainModule(40)));
        var provenance = await SourceProvenance.ParseValidAsync(Family(Deep, "F(1), F(1)"), modules.Options());
        var region = OnlyRegion(provenance.Root);

        for (var pass = 0; pass < 2; pass++)
        {
            foreach (var permissive in permissiveFirst ? new[] { true, false } : [false, true])
            {
                var result = await RunDirect(provenance.Root, modules, permissive ? null : restrictive);
                if (permissive)
                {
                    Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
                    Assert.Equal([(Decimal128)1, (Decimal128)1], result.Value.Value.ToAtoms());
                }
                else
                {
                    AssertDepthRejected(result, 100);
                }

                // The shared materialization is untouched by any run's admission verdict.
                Assert.True(region.IsMaterialized);
                Assert.Equal(1, region.MaterializationAttempts);
                Assert.Equal(1, modules.Fetches);
            }
        }
    }

    // ── T5: every evaluator consumption path ────────────────────────────────

    public static TheoryData<string> SelectionRoutes => new()
    {
        "F(1)",
        "Choose = count([7])\nF(Choose)",
        "[1, 1].map(F)",
        "Apply(fn, x) = fn(x)\nApply(F, 1)",
        "Lib = { public F(0) = 42\npublic F(n) = { open 'URL'\nX } }\nLib.F(1)",
        "Pick(0) = 42\nPick(n) = 99\nPick(F(1))",
        "if(true, F(1), 0)",
        "Ignore(x) = 42\nUse(x) = x + 0\nUse(Ignore(0) + F(1))",
    };

    [Theory]
    [MemberData(nameof(SelectionRoutes))]
    public async Task T5_EverySelectionRoute_IsAdmitted_FirstTimeAndCached(string output)
    {
        foreach (var links in new[] { 120, 10 })
        {
            var modules = new Modules((Deep, DotChainModule(links)));
            var source = Family(Deep, output.Replace("URL", Deep, StringComparison.Ordinal));
            var provenance = await SourceProvenance.ParseValidAsync(source, modules.Options());
            for (var run = 0; run < 2; run++)
            {
                var result = await RunDirect(provenance.Root, modules, suspending: run == 1);
                if (links == 120)
                {
                    AssertDepthRejected(result, EvaluationLimits.MaxSupportedAstDepth);
                }
                else
                {
                    Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
                }
            }

            Assert.All(Regions(provenance.Root).Where(r => r.IsMaterialized), r => Assert.Equal(1, r.MaterializationAttempts));
        }
    }

    [Theory]
    [InlineData(120, true)]
    [InlineData(10, false)]
    public async Task T5_FlatBinderEquivalent_TheAlgorithmOutputPath_IsAdmitted(int links, bool rejected)
    {
        // A one-clause host family over flat binders is evaluated through its user equivalent: the
        // placeholder view's OUTPUT is demanded (EvalAlgOutputPreparedCoreAsync), not a branch.
        var modules = new Modules((Deep, DotChainModule(links)));
        var syntax = Parser.ParseSyntax($"F(0) = {{\n    open '{Deep}'\n    x + y + X\n}}\nF(1) = 0\nF(1, 2)");
        Assert.False(syntax.HasErrors);
        var body = Assert.IsType<Algorithm.Conditional>(syntax.Root.Properties.Single(p => p.Name == "F").Value).Branches[0].Body;
        var family = new Algorithm.Conditional(null, [],
            [new CondBranch(new Pattern.SequenceValue([new Pattern.Bind("x"), new Pattern.Bind("y")]), body)]);
        var root = syntax.Root with { Properties = [new Property("F", family)] };
        var diagnostics = new DiagnosticBag();
        var loaded = await new ModuleLoader(diagnostics, modules.Options().DownloadCode!).ElaborateAsync(root);
        var (detected, _) = ParameterDetector.Detect(loaded);
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, diagnostics: diagnostics);
        new ParameterPropertyCollisionValidator(diagnostics).VisitAlgorithm(resolved);
        var exposed = PropertyExposureResolver.Resolve(resolved);
        Assert.Empty(diagnostics);
        Assert.Equal(0, modules.Fetches);

        for (var run = 0; run < 2; run++)
        {
            var result = await RunDirect(exposed, modules);
            if (rejected) AssertDepthRejected(result, EvaluationLimits.MaxSupportedAstDepth);
            else AssertValue(result, 4);
        }

        Assert.Equal(1, modules.Fetches);
    }

    // ── T6: laziness is unchanged ───────────────────────────────────────────

    [Theory]
    [InlineData("F(0)")]
    [InlineData("Ignore(x) = 42\nIgnore(F(1))")]
    [InlineData("if(false, F(1), 42)")]
    [InlineData("Ignore(fn) = 42\nIgnore(F)")]
    public async Task T6_AnUnselectedExcessiveBody_IsNeitherFetchedNorJudged(string output)
    {
        var modules = new Modules((Deep, DotChainModule(250)));
        var provenance = await SourceProvenance.ParseValidAsync(Family(Deep, output), modules.Options());

        AssertValue(await RunDirect(provenance.Root, modules), 42);
        Assert.Equal(0, modules.Fetches);
        Assert.False(OnlyRegion(provenance.Root).IsMaterialized);
        Assert.Equal(0, OnlyRegion(provenance.Root).MaterializationAttempts);
    }

    // ── T7: a structural rejection is terminal ──────────────────────────────

    [Theory]
    [InlineData("Tick(), F(1), Tick()", new[] { "tick", "fetch" })]
    [InlineData("Pick(0) = 42\nPick(n) = 99\nTick(), Pick(F(1)), Tick()", new[] { "tick", "fetch" })]
    [InlineData("Then(x, y) = x + y\nThen(F(1), Tick())\nTick()", new[] { "fetch" })]
    [InlineData("Keep(*xs) = xs\nKeep(Tick(), F(1)*, Tick())", new[] { "fetch" })]
    public async Task T7_StructuralRejection_StopsEveryLaterHostEffect(string output, string[] expected)
    {
        var modules = new Modules((Deep, DotChainModule(120)));
        var provenance = await SourceProvenance.ParseValidAsync(Family(Deep, output), modules.Options());

        AssertDepthRejected(await RunDirect(provenance.Root, modules), EvaluationLimits.MaxSupportedAstDepth);

        Assert.Equal(expected, modules.Events.Select(e => e.StartsWith("fetch", StringComparison.Ordinal) ? "fetch" : e));
    }

    // ── T8: cancellation and source failures keep their protocols ───────────

    [Fact]
    public async Task T8_SourceFailure_KeepsItsMaterializationClassification()
    {
        var modules = new Modules();
        var failure = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(Family(Missing, "F(1)"), modules.Options()));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.LoadFetchFailed, error.Code);
        Assert.False(error.IsResourceLimit);
        Assert.Equal(2, Assert.NotNull(error.Span).Start.Line);
    }

    [Fact]
    public async Task T8_CancellationDuringTheDeferredDownload_PropagatesAndPublishesNoBody()
    {
        using var cancellation = new CancellationTokenSource();
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var options = new RunOptions
        {
            AllowedHosts = ["katlang.org"],
            DownloadCode = async (_, token) =>
            {
                entered.SetResult();
                await Task.Delay(Timeout.Infinite, token);
                return DotChainModule(120);
            },
        };
        var provenance = await SourceProvenance.ParseValidAsync(Family(Deep, "F(1)"), options);
        var region = OnlyRegion(provenance.Root);
        var pending = Evaluator.RunCountedAsync(new Expr.AlgorithmExpr(provenance.Root), new PassThroughAsyncZeroArgPropertyResultCache(),
            cancellationToken: cancellation.Token).AsTask();
        await entered.Task.WaitAsync(WaitLimit);
        cancellation.Cancel();

        var error = await Assert.ThrowsAsync<OperationCanceledException>(async () => await pending.WaitAsync(WaitLimit));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.False(region.IsMaterialized);
    }

    [Fact]
    public async Task T8_CancelledRun_OverACachedRejectedBody_StillThrowsItsCancellation()
    {
        var modules = new Modules((Deep, DotChainModule(120)));
        var provenance = await SourceProvenance.ParseValidAsync(Family(Deep, "F(1)"), modules.Options());
        AssertDepthRejected(await RunDirect(provenance.Root, modules), EvaluationLimits.MaxSupportedAstDepth);

        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var error = await Assert.ThrowsAsync<OperationCanceledException>(() => Evaluator.RunCountedAsync(
            new Expr.AlgorithmExpr(provenance.Root), new PassThroughAsyncZeroArgPropertyResultCache(), cancellationToken: cancellation.Token).AsTask());
        Assert.Equal(cancellation.Token, error.CancellationToken);
    }

    // ── T9: valid programs keep their results ───────────────────────────────

    public static TheoryData<string> ValidPrograms => new()
    {
        "F(1)",
        "F(1) + F(2)",
        "[1, 2].map(F)",
        "Apply(fn, x) = fn(x)\nApply(F, 1)",
        "Step(s) = s + F(1)\nrepeat(Step(0), 3)",
        "Step(s) = s + F(1), false\nwhile(Step(0))",
        "Capture(meta operation) = operation\nCapture(F(1)).Invoke() + Capture(F(2)).Invoke()",
        "Lib = { public F(0) = 42\npublic F(n) = { open 'URL'\nX } }\nLib.F(1) + F(1)",
    };

    [Theory]
    [MemberData(nameof(ValidPrograms))]
    public async Task T9_ValidDeferredPrograms_MatchTheirEagerEquivalent(string output)
    {
        var modules = new Modules((Deep, DotChainModule(20)));
        var deferred = await KatLangEngine.RunAsync(Family(Deep, output.Replace("URL", Deep, StringComparison.Ordinal)), modules.Options());
        var eager = await KatLangEngine.RunAsync(
            "F(0) = 42\nF(n) = 1\n" + output.Replace("{ open 'URL'\nX }", "1", StringComparison.Ordinal), modules.Options());
        var expected = Assert.IsType<RunResult.Success>(eager);
        Assert.Equal(expected.ToDisplayString(), Assert.IsType<RunResult.Success>(deferred).ToDisplayString());
    }

    [Fact]
    public async Task T9_NestedDeferredRegions_KeepTheirResults_AndMaterializeOnce()
    {
        var modules = new Modules((Shallow, "public S = 5"), (Deep, DotChainModule(20)));
        var source = $"F(0) = {{\n  open '{Shallow}'\n  G(0) = 0\n  G(n) = {{ open '{Deep}'\nX + S }}\n  G(1) + G(2)\n}}\nF(1) = 0\nF(0) + F(0)";
        var provenance = await SourceProvenance.ParseValidAsync(source, modules.Options());
        for (var run = 0; run < 2; run++)
            AssertValue(await RunDirect(provenance.Root, modules, suspending: run == 1), 24);
        var regions = Regions(provenance.Root).Distinct().ToList();
        Assert.Equal(2, regions.Count);
        Assert.All(regions, region => Assert.Equal(1, region.MaterializationAttempts));
        Assert.Equal(2, modules.Fetches);
    }

    [Fact]
    public async Task T9_ProgramsWithoutDeferredRegions_KeepTheirSynchronousPath()
    {
        var withRegion = await SourceProvenance.ParseValidAsync(Family(Deep, "F(0)"), new Modules((Deep, "public X = 1")).Options());
        Assert.True(DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.AlgorithmExpr(withRegion.Root)));
        // A program without deferred regions records no deferred admission and keeps the synchronous family.
        var plain = Evaluator.RunFlat(new Expr.AlgorithmExpr(SourceProvenance.ParseValid("F(0) = 42\nF(n) = n\nF(3)").Root));
        Assert.False(plain.IsError);
        Assert.Equal([3m], plain.Value);
    }
}
