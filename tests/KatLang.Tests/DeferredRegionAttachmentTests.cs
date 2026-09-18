using System.Reflection;
using System.Runtime.CompilerServices;

namespace KatLang.Tests;

/// <summary>
/// Deferred-region state lives ON the placeholder body (September 2026, invalid-state audit
/// §3.2): <see cref="Algorithm.DeferredRegion"/> is an equality-transparent slot the record
/// copy constructor carries, so every ordinary <c>with</c> view of a placeholder — parent
/// wiring, a parameter-list replacement, a host copy, the flat-binder equivalent — is a view
/// of the same region with no registration step, while each rewriting front-end pass installs
/// a FORK (the same occurrence plus its own context) on the output view it produces. There is
/// no side table keyed on body identity and no root mark: the tree itself answers whether a
/// run can reach a region. Region identity is the placeholder's own and is NOT declaration
/// identity: the loader clones one placeholder per deferred branch occurrence, and the clones
/// of one shared raw body keep that body's <see cref="Algorithm.Declaration"/>.
/// Host-only by nature: Lean's input model has no external modules and no demand timing.
/// </summary>
public class DeferredRegionAttachmentTests
{
    private const string ModuleA = "https://katlang.org/attach/a.kat";
    private const string ModuleM = "https://katlang.org/attach/m.kat";

    private static Expr Load(string url)
        => new Expr.Call(new Expr.Resolve("load"), new OutputBundle([new Expr.StringLiteral(url)]));

    private sealed class CountingModules
    {
        private readonly Dictionary<string, string> _files;

        public CountingModules(params (string Url, string Source)[] files)
            => _files = files.ToDictionary(file => file.Url, file => file.Source, StringComparer.Ordinal);

        public Dictionary<string, int> Fetches { get; } = new(StringComparer.Ordinal);

        public int this[string url] => Fetches.GetValueOrDefault(url);

        public ValueTask<string> Download(string url, CancellationToken cancellationToken)
        {
            Fetches[url] = this[url] + 1;
            return _files.TryGetValue(url, out var source)
                ? ValueTask.FromResult(source)
                : throw new Exception($"404: {url}");
        }

        public RunOptions Options => new() { DownloadCode = Download };
    }

    private static CountingModules Modules()
        => new((ModuleA, "public A = 1"), (ModuleM, "public F(0) = {\n    open '" + ModuleA + "'\n    A + 10\n}\npublic F(n) = n"));

    /// <summary>A load-bearing branch body: <c>{ open ModuleA; A + 1 }</c>.</summary>
    private static Algorithm.User LoadBearingBody()
        => new(null, [], [Load(ModuleA)], [],
            [new Expr.Binary(BinaryOp.Add, new Expr.Resolve("A"), new Expr.Num(1))]);

    /// <summary>A two-clause host family <c>F(0) = body / F(n) = n</c> over <paramref name="body"/>.</summary>
    private static Algorithm.Conditional Family(Algorithm body)
        => new(null, [],
        [
            new CondBranch(new Pattern.LitInt(0), body),
            new CondBranch(new Pattern.Bind("n"), new Algorithm.User(null, [], [], [], [new Expr.Param("n")])),
        ]);

    private static Algorithm.User Root(Algorithm.Conditional family, int argument)
        => new(null, [], [], [new Property("F", family)],
            [new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Num(argument)]))]);

    private static Algorithm.Conditional FamilyOf(Algorithm root, string name = "F")
        => Assert.IsType<Algorithm.Conditional>(Assert.Single(root.Properties, p => p.Name == name).Value);

    private static Algorithm.User Placeholder(Algorithm root, string name = "F")
        => Assert.IsType<Algorithm.User>(FamilyOf(root, name).Branches[0].Body);

    private static DeferredModuleRegion RegionOf(Algorithm body)
    {
        var region = body.DeferredRegion;
        Assert.NotNull(region);
        return region;
    }

    /// <summary>The internal stages in the pipeline's order, each returning its output tree.</summary>
    private static Algorithm.User Detect(Algorithm tree)
    {
        var (detected, diagnostics) = ParameterDetector.Detect(tree);
        Assert.Empty(diagnostics);
        return Assert.IsType<Algorithm.User>(detected);
    }

    private static Algorithm.User Resolve(Algorithm tree)
    {
        var diagnostics = new List<Diagnostic>();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(tree, diagnostics: diagnostics);
        Assert.Empty(diagnostics);
        return Assert.IsType<Algorithm.User>(resolved);
    }

    private static Algorithm.User Validate(Algorithm.User tree)
    {
        var diagnostics = new List<Diagnostic>();
        new ParameterPropertyCollisionValidator(diagnostics, programRoot: tree).VisitAlgorithm(tree);
        Assert.Empty(diagnostics);
        return tree;
    }

    private static Algorithm.User Expose(Algorithm tree) => Assert.IsType<Algorithm.User>(PropertyExposureResolver.Resolve(tree));

    private static async Task<Algorithm.User> LoadAsync(Algorithm root, CountingModules modules)
    {
        var diagnostics = new List<Diagnostic>();
        var loaded = await new ModuleLoader(diagnostics, modules.Download).ElaborateAsync(root);
        Assert.Empty(diagnostics);
        return Assert.IsType<Algorithm.User>(loaded);
    }

    private static async Task<Algorithm.User> ElaborateAsync(Algorithm root, CountingModules modules)
        => Expose(Validate(Resolve(Detect(await LoadAsync(root, modules)))));

    // ── A. Attachment: ordinary copies are views of the same region ─────────

    [Fact]
    public async Task LoaderPlaceholder_CarriesItsRegion_ThroughEveryOrdinaryCopy()
    {
        var body = LoadBearingBody();
        var loaded = await LoadAsync(Root(Family(body), 0), Modules());
        var placeholder = Placeholder(loaded);
        var region = RegionOf(placeholder);

        Assert.NotSame(body, placeholder);
        Assert.Same(body, region.RawBody);
        Assert.Null(body.DeferredRegion);
        Assert.Same(body.Declaration, placeholder.Declaration);

        // Every `with` view — the evaluator's parent wiring, parameter replacements, a host
        // copy, a copy of a copy — carries the region object itself, with no registration.
        var scope = new ScopeCtx(null, [], []);
        Assert.Same(region, (placeholder with { }).DeferredRegion);
        Assert.Same(region, (placeholder with { Parent = scope }).DeferredRegion);
        Assert.Same(region, placeholder.WithParameters([new ParameterDeclaration("x")]).DeferredRegion);
        Assert.Same(region, placeholder.WithParams(["a", "b"]).DeferredRegion);
        Assert.Same(region, ((placeholder with { Parent = scope }) with { Output = [new Expr.Num(2)] }).DeferredRegion);

        // Only an explicit replacement changes the slot; fresh construction never carries one.
        Assert.Null((placeholder with { DeferredRegion = null }).DeferredRegion);
        Assert.Null(new Algorithm.User(null, [], [], [], [new Expr.Num(1)]).DeferredRegion);
        Assert.Null(new Algorithm.Conditional(null, [], []).DeferredRegion);
        Assert.Null(new Algorithm.Builtin(BuiltinId.count).DeferredRegion);
    }

    [Fact]
    public async Task FlatBinderEquivalent_IsAViewOfTheBranchRegion_AndSharesItsMaterialization()
    {
        // A host one-clause family with a flat multi-binder head evaluates through its
        // ordinary-call equivalent, a `with` view of the branch body: it carries the SAME
        // region object, so demanding it materializes the branch's region once, and both the
        // branch and the equivalent see that one materialization.
        var modules = Modules();
        var family = new Algorithm.Conditional(null, [],
            [new CondBranch(new Pattern.SequenceValue([new Pattern.Bind("x"), new Pattern.Bind("y")]),
                new Algorithm.User(null, [], [Load(ModuleA)], [],
                    [new Expr.Binary(BinaryOp.Add, new Expr.Binary(BinaryOp.Add, new Expr.Resolve("x"), new Expr.Resolve("y")), new Expr.Resolve("A"))]))]);
        var root = new Algorithm.User(null, [], [], [new Property("F", family)],
            [new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Num(1), new Expr.Num(2)]))]);
        var exposed = await ElaborateAsync(root, modules);
        var branchRegion = RegionOf(Placeholder(exposed));
        var method = typeof(Evaluator).GetMethod("TryGetFlatBinderUserEquivalent", BindingFlags.NonPublic | BindingFlags.Static)!;
        var equivalent = Assert.IsType<Algorithm.User>(method.Invoke(null, [FamilyOf(exposed)]));
        Assert.Same(branchRegion, equivalent.DeferredRegion);
        Assert.Same(Placeholder(exposed).Declaration, equivalent.Declaration);
        Assert.Equal(0, modules[ModuleA]);

        for (var run = 0; run < 2; run++)
        {
            var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(exposed));
            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
            Assert.Equal([4m], result.Value);
        }

        Assert.Equal(1, modules[ModuleA]);
        Assert.Equal(1, branchRegion.MaterializationAttempts);
        Assert.True(branchRegion.TryGetMaterialized(out var materialized));
        Assert.Null(materialized.DeferredRegion);
        Assert.Same(Placeholder(exposed).Declaration, materialized.Declaration);
    }

    // ── B. Identity: one region per occurrence, never per declaration ───────

    [Fact]
    public async Task RegionIdentity_IsNotDeclarationIdentity()
    {
        // ONE raw body object under two branches (a legal host DAG): two placeholders that are
        // views of the one declaration — and two independent regions, from the loader through
        // every pass to materialization. Keying regions by declaration would merge them.
        var modules = Modules();
        var shared = LoadBearingBody();
        var family = new Algorithm.Conditional(null, [],
        [
            new CondBranch(new Pattern.LitInt(0), shared),
            new CondBranch(new Pattern.LitInt(1), shared),
            new CondBranch(new Pattern.Bind("n"), new Algorithm.User(null, [], [], [], [new Expr.Param("n")])),
        ]);
        var loaded = await LoadAsync(Root(family, 0), modules);
        var loaderFamily = FamilyOf(loaded);
        Assert.Same(shared.Declaration, loaderFamily.Branches[0].Body.Declaration);
        Assert.Same(shared.Declaration, loaderFamily.Branches[1].Body.Declaration);
        Assert.NotSame(RegionOf(loaderFamily.Branches[0].Body), RegionOf(loaderFamily.Branches[1].Body));

        var exposed = Expose(Validate(Resolve(Detect(loaded))));
        var exposedFamily = FamilyOf(exposed);
        var region0 = RegionOf(exposedFamily.Branches[0].Body);
        var region1 = RegionOf(exposedFamily.Branches[1].Body);
        Assert.NotSame(region0, region1);
        Assert.Same(region0.RawBody, region1.RawBody);
        Assert.Same(shared.Declaration, exposedFamily.Branches[0].Body.Declaration);
        Assert.Same(shared.Declaration, exposedFamily.Branches[1].Body.Declaration);

        var first = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(exposed));
        Assert.False(first.IsError, first.IsError ? first.Error.ToString() : null);
        Assert.Equal([2m], first.Value);
        Assert.Equal(1, region0.MaterializationAttempts);
        Assert.Equal(0, region1.MaterializationAttempts);
        Assert.True(region0.TryGetMaterialized(out var materialized));
        Assert.Same(shared.Declaration, materialized.Declaration);
        Assert.False(region1.IsMaterialized);

        var second = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(exposed with
        {
            Output = [new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Num(1)]))],
        }));
        Assert.False(second.IsError, second.IsError ? second.Error.ToString() : null);
        Assert.Equal([2m], second.Value);
        Assert.Equal(1, region1.MaterializationAttempts);
        Assert.Equal(1, modules[ModuleA]);
    }

    [Fact]
    public async Task OneModuleSplicedAtTwoSites_KeepsOneRegionPerFrontEndContext()
    {
        // The loader splices ONE cached module algorithm at every load site, so the module's
        // deferred placeholder is one object reached by the front end from two importing
        // owners. Each pass forks the region it finds on the output view it produces for the
        // context it was reached under, so two owners with different scopes get two complete,
        // independent regions over the one raw body, and selecting one path materializes
        // exactly that region. The deferred code reads q as a property in First and as an
        // ancestor parameter in Second, so stale phase snapshots change actual evaluation.
        var modules = new CountingModules(
            (ModuleA, "public A = 1"),
            (ModuleM, "public F(0) = {\n    open '" + ModuleA + "'\n    q + A + 10\n}\npublic F(n) = n"));
        var parsed = await SourceProvenance.ParseValidAsync(
            $"First = {{\n    q = 1\n    Lib = load('{ModuleM}')\n    Lib.F(0)\n}}\n" +
            $"Second(q) = {{\n    Lib = load('{ModuleM}')\n    Lib.F(0)\n}}\n" +
            "First, Second(100)",
            modules.Options);
        Assert.Equal(1, modules[ModuleM]);
        Assert.Equal(0, modules[ModuleA]);

        static Algorithm PlaceholderUnder(Algorithm owner)
            => FamilyOf(Assert.IsType<Algorithm.User>(Assert.Single(owner.Properties, p => p.Name == "Lib").Value)).Branches[0].Body;
        var firstPlaceholder = PlaceholderUnder(Assert.Single(parsed.Root.Properties, p => p.Name == "First").Value);
        var secondPlaceholder = PlaceholderUnder(Assert.Single(parsed.Root.Properties, p => p.Name == "Second").Value);
        var firstRegion = RegionOf(firstPlaceholder);
        var secondRegion = RegionOf(secondPlaceholder);
        Assert.NotSame(firstPlaceholder, secondPlaceholder);
        Assert.NotSame(firstRegion, secondRegion);
        Assert.Same(firstRegion.RawBody, secondRegion.RawBody);
        Assert.Same(firstRegion.Loader, secondRegion.Loader);
        Assert.Same(firstPlaceholder.Declaration, secondPlaceholder.Declaration);
        Assert.NotSame(firstRegion.Detection!.ParentScope, secondRegion.Detection!.ParentScope);
        Assert.NotNull(firstRegion.Resolution);
        Assert.NotNull(firstRegion.Validation);
        Assert.NotNull(firstRegion.Exposure);
        Assert.NotNull(secondRegion.Resolution);
        Assert.NotNull(secondRegion.Validation);
        Assert.NotNull(secondRegion.Exposure);

        var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root with
        {
            Output = [new Expr.Resolve("First")],
        }));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([12m], result.Value);
        Assert.Equal(1, firstRegion.MaterializationAttempts);
        Assert.Equal(0, secondRegion.MaterializationAttempts);
        Assert.Equal(1, modules[ModuleA]);

        var both = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));
        Assert.False(both.IsError, both.IsError ? both.Error.ToString() : null);
        Assert.Equal([12m, 111m], both.Value);
        Assert.Equal(1, firstRegion.MaterializationAttempts);
        Assert.Equal(1, secondRegion.MaterializationAttempts);
        Assert.Equal(1, modules[ModuleA]);
    }

    // ── C. Phase accumulation on the output views ────────────────────────────

    [Fact]
    public async Task FrontEndPasses_AccumulateContexts_OnTheirOutputViews()
    {
        var loaded = await LoadAsync(Root(Family(LoadBearingBody()), 0), Modules());
        var created = RegionOf(Placeholder(loaded));
        Assert.Null(created.Detection);
        Assert.Null(created.Resolution);
        Assert.Null(created.Validation);
        Assert.Null(created.Exposure);

        // Detection: a fork on the detector's output view, the loader facts intact.
        var detected = Detect(loaded);
        var afterDetection = RegionOf(Placeholder(detected));
        Assert.NotSame(created, afterDetection);
        Assert.Same(created.RawBody, afterDetection.RawBody);
        Assert.Same(created.Loader, afterDetection.Loader);
        Assert.Equal(created.Depth, afterDetection.Depth);
        Assert.NotNull(afterDetection.Detection);
        Assert.Null(afterDetection.Resolution);
        Assert.Null(afterDetection.Validation);
        Assert.Null(afterDetection.Exposure);
        Assert.Null(created.Detection);

        // Resolution: added without losing detection.
        var resolved = Resolve(detected);
        var afterResolution = RegionOf(Placeholder(resolved));
        Assert.NotSame(afterDetection, afterResolution);
        Assert.Same(afterDetection.Detection, afterResolution.Detection);
        Assert.NotNull(afterResolution.Resolution);
        Assert.Null(afterResolution.Validation);
        Assert.Null(afterResolution.Exposure);

        // Validation: the observation walk rewrites nothing, so it records IN PLACE on the
        // region the tree already carries; nothing earlier is lost.
        Validate(resolved);
        Assert.Same(afterResolution, RegionOf(Placeholder(resolved)));
        Assert.NotNull(afterResolution.Validation);
        Assert.Same(afterDetection.Detection, afterResolution.Detection);
        Assert.Null(afterResolution.Exposure);

        // Exposure: the final fork carries every earlier context and the recorded bindings.
        var exposed = Expose(resolved);
        var final = RegionOf(Placeholder(exposed));
        Assert.NotSame(afterResolution, final);
        Assert.Same(afterDetection.Detection, final.Detection);
        Assert.Same(afterResolution.Resolution, final.Resolution);
        Assert.Same(afterResolution.Validation, final.Validation);
        Assert.NotNull(final.Exposure);
        Assert.Same(created.RawBody, final.RawBody);
        Assert.Same(created.Loader, final.Loader);

        // Placeholders keep the raw body's declaration through every view; forks start with
        // their own (empty) materialization state.
        Assert.Same(created.RawBody.Declaration, Placeholder(exposed).Declaration);
        Assert.False(final.IsMaterialized);
        Assert.Equal(0, final.MaterializationAttempts);
    }

    [Fact]
    public async Task Materialization_RequiresEveryContext()
    {
        var modules = Modules();
        var loaded = await LoadAsync(Root(Family(LoadBearingBody()), 0), modules);
        var resolved = Resolve(Detect(loaded));
        var incomplete = RegionOf(Placeholder(resolved));
        Assert.Null(incomplete.Validation);
        Assert.Null(incomplete.Exposure);

        var rejection = await Assert.ThrowsAsync<InvalidOperationException>(
            async () => await incomplete.MaterializeAsync(CancellationToken.None));
        Assert.Contains("complete elaboration context", rejection.Message, StringComparison.Ordinal);

        // A fork carries the incompleteness too, and the loader's placeholder has nothing.
        var forked = incomplete.WithExposure(new PropertyExposureResolver.DeferredBranchContext(
            RegionOf(Placeholder(Expose(Validate(Resolve(Detect(loaded)))))).Exposure!.Scope));
        Assert.Null(forked.Validation);
        await Assert.ThrowsAsync<InvalidOperationException>(async () => await forked.MaterializeAsync(CancellationToken.None));
        await Assert.ThrowsAsync<InvalidOperationException>(
            async () => await RegionOf(Placeholder(loaded)).MaterializeAsync(CancellationToken.None));
        Assert.Equal(0, modules[ModuleA]);
        Assert.Equal(0, incomplete.MaterializationAttempts);
    }

    // ── D. No registration step, no root mark ───────────────────────────────

    [Fact]
    public async Task EveryPassOutput_CarriesACompleteRegion_WithoutAnyRegistration()
    {
        // The missed-copy regression: under a side table, a pass that rebuilt the placeholder
        // and forgot to re-register left an unannotated body — the raw loads inside it then
        // surfaced as an ordinary unresolved-load failure at evaluation. Here every pass
        // output is checked to carry a region derived from the loader's, and the evaluated
        // tree is a HOST COPY of the root (which under a root-mark design had to be re-marked
        // by hand) evaluated through the sync and async entry points.
        var modules = Modules();
        var loaded = await LoadAsync(Root(Family(LoadBearingBody()), 0), modules);
        var loaderRegion = RegionOf(Placeholder(loaded));
        var stages = new List<(string Name, Algorithm.User Tree)> { ("loader", loaded) };
        stages.Add(("detector", Detect(stages[^1].Tree)));
        stages.Add(("resolver", Resolve(stages[^1].Tree)));
        stages.Add(("validator", Validate(stages[^1].Tree)));
        stages.Add(("exposure", Expose(stages[^1].Tree)));
        foreach (var (name, tree) in stages)
        {
            var region = Placeholder(tree).DeferredRegion;
            Assert.True(region is not null, $"the {name} output lost its deferred region");
            Assert.Same(loaderRegion.RawBody, region.RawBody);
            Assert.Same(loaderRegion.Loader, region.Loader);
        }

        var copy = stages[^1].Tree with
        {
            Output = [new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Num(0)])), new Expr.Num(7)],
        };
        Assert.True(DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.AlgorithmExpr(copy)));
        Assert.True(DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.Capture(new OutputBundle([new Expr.AlgorithmExpr(copy)]))));
        Assert.Throws<InvalidOperationException>(() => Evaluator.Run(new Expr.AlgorithmExpr(copy)));
        Assert.Throws<InvalidOperationException>(() => Evaluator.RunFlat(new Expr.AlgorithmExpr(copy)));
        Assert.Equal(0, modules[ModuleA]);

        var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(copy));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([2m, 7m], result.Value);
        Assert.Equal(1, modules[ModuleA]);
        Assert.Equal(1, RegionOf(Placeholder(copy)).MaterializationAttempts);

        // Selecting only the eager alternative keeps the tree async-routed (a region is
        // reachable) but performs no module work.
        var eager = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(stages[^1].Tree with
        {
            Output = [new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Num(5)]))],
        }));
        Assert.False(eager.IsError);
        Assert.Equal([5m], eager.Value);
        Assert.Equal(1, modules[ModuleA]);
    }

    [Fact]
    public async Task RoutingIsAnsweredByTheTree_NotByAMark()
    {
        var modules = Modules();
        var parsed = await SourceProvenance.ParseValidAsync(
            $"F(0) = {{\n    open '{ModuleA}'\n    A\n}}\nF(n) = n\nF(1)", modules.Options);
        var root = parsed.Root;
        Assert.True(DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.AlgorithmExpr(root)));

        // A copy of the root, a subtree lifted out of it, and a host tree that merely
        // references the family all route async — they all reach a placeholder.
        Assert.True(DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.AlgorithmExpr(root with { Output = [new Expr.Num(1)] })));
        Assert.True(DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.AlgorithmExpr(FamilyOf(root))));
        Assert.True(DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.AlgorithmExpr(
            new Algorithm.User(null, [], [], [new Property("G", FamilyOf(root))], [new Expr.Num(1)]))));

        // Replacing the family with its eager alternative alone removes every region: the same
        // shape of tree is synchronous again, with no stale mark to say otherwise.
        var withoutRegions = root with
        {
            Properties = [new Property("F", FamilyOf(root) with { Branches = [FamilyOf(root).Branches[1]] })],
        };
        Assert.False(DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.AlgorithmExpr(withoutRegions)));
        var synchronous = Evaluator.RunFlat(new Expr.AlgorithmExpr(withoutRegions));
        Assert.False(synchronous.IsError);
        Assert.Equal([1m], synchronous.Value);
        Assert.Equal(0, modules[ModuleA]);
    }

    // ── E. Record semantics: the slot is invisible to structural equality ────

    [Fact]
    public async Task RegionSlot_IsTransparentToStructuralEqualityHashingAndPrinting()
    {
        var body = LoadBearingBody();
        var loaded = await LoadAsync(Root(Family(body), 0), Modules());
        var placeholder = Placeholder(loaded);
        Assert.NotNull(placeholder.DeferredRegion);

        // The placeholder is a shallow clone of the raw body: structurally equal, hashing
        // alike, printing alike, and one member of an equality-based set.
        Assert.Equal(body, placeholder);
        Assert.Equal(placeholder, body);
        Assert.Equal(body.GetHashCode(), placeholder.GetHashCode());
        Assert.Equal(body.ToString(), placeholder.ToString());
        Assert.DoesNotContain("DeferredRegion", placeholder.ToString(), StringComparison.Ordinal);
        Assert.DoesNotContain("DeferredModuleRegion", placeholder.ToString(), StringComparison.Ordinal);
        Assert.Single(new HashSet<Algorithm> { body, placeholder, placeholder with { }, placeholder with { DeferredRegion = null } });

        // Forks with different contexts do not distinguish their carriers either.
        var exposed = Expose(Validate(Resolve(Detect(loaded))));
        var final = Placeholder(exposed);
        Assert.NotSame(placeholder.DeferredRegion, final.DeferredRegion);
        Assert.Equal(final with { DeferredRegion = null }, final);
        Assert.Equal((final with { DeferredRegion = null }).GetHashCode(), final.GetHashCode());
        Assert.Equal((final with { DeferredRegion = null }).ToString(), final.ToString());
    }

    // ── F. Traversal: the region is runtime state, never a structural child ──

    [Fact]
    public async Task RegionState_IsNotAStructuralChild()
    {
        var body = LoadBearingBody();
        var loaded = await LoadAsync(Root(Family(body), 0), Modules());
        var placeholder = Placeholder(loaded);
        var region = RegionOf(placeholder);

        // The structural child enumeration of a placeholder is exactly the raw body's: the
        // region and its raw body are not children, and neither is a nested region's.
        var placeholderChildren = Children(placeholder);
        var bodyChildren = Children(body);
        Assert.Equal(bodyChildren.Count, placeholderChildren.Count);
        Assert.DoesNotContain(placeholderChildren, child => child is DeferredModuleRegion);
        Assert.DoesNotContain(placeholderChildren, child => ReferenceEquals(child, region.RawBody));
        Assert.Null(AstStructuralPreflight.Check(loaded, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.FullyRecursive));
        Assert.Equal(
            AstStructuralPreflight.Check(Root(Family(body), 0), 3, AstConsumerProfile.FullyRecursive) is null,
            AstStructuralPreflight.Check(loaded, 3, AstConsumerProfile.FullyRecursive) is null);

        // The structural walkers skip a placeholder by its slot, never by shape: the guard
        // does not report the raw loads a placeholder keeps, while the raw body's are found.
        Assert.False(LoadElaborationGuard.TryFindFirstUnresolvedLoad(loaded, out _));
        Assert.True(LoadElaborationGuard.TryFindFirstUnresolvedLoad(Root(Family(body), 0), out _));
    }

    private static List<object> Children(object node)
    {
        var children = new List<object>();
        for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
            children.Add(child);
        return children;
    }

    // ── G. Re-deferral: a raw body never carries a region ───────────────────

    [Fact]
    public async Task ReDeferringAPlaceholder_StripsTheEarlierRegionFromTheRawBody()
    {
        // An elaborated tree handed to a second loader: the placeholder is load-bearing again
        // and is deferred again, over a region-free copy of itself, so nothing derived from
        // the new raw body (its materialization) can ever be a placeholder of the first run.
        var modules = Modules();
        var first = await LoadAsync(Root(Family(LoadBearingBody()), 0), modules);
        var firstPlaceholder = Placeholder(first);
        var firstRegion = RegionOf(firstPlaceholder);

        var secondDiagnostics = new List<Diagnostic>();
        var secondLoader = new ModuleLoader(secondDiagnostics, modules.Download);
        var second = await secondLoader.ElaborateAsync(first);
        Assert.Empty(secondDiagnostics);
        Assert.Equal(1, secondLoader.DeferredRegionCount);
        var secondPlaceholder = Placeholder(second);
        var secondRegion = RegionOf(secondPlaceholder);
        Assert.NotSame(firstRegion, secondRegion);
        Assert.NotSame(firstPlaceholder, secondRegion.RawBody);
        Assert.Null(secondRegion.RawBody.DeferredRegion);
        Assert.Equal(firstPlaceholder, secondRegion.RawBody);
        Assert.Same(firstPlaceholder.Declaration, secondRegion.RawBody.Declaration);
        // The first elaboration's placeholder and region are untouched by the second.
        Assert.Same(firstRegion, firstPlaceholder.DeferredRegion);
        Assert.Null(firstRegion.RawBody.DeferredRegion);

        // The invariant is enforced at construction as well.
        Assert.Throws<ArgumentException>(() => new DeferredModuleRegion(
            secondLoader, firstPlaceholder, ModuleLoader.LoadContext.PropertyDef, 1, 0));
        Assert.Equal(0, modules[ModuleA]);
    }

    // ── H. Lifetime: a completed materialization roots nothing ──────────────

    [Fact]
    public async Task CompletedMaterialization_LeavesTheTreeRegionAndLoaderCollectible()
    {
        var references = await MaterializeAndForget();
        for (var attempt = 0; attempt < 5 && references.Any(reference => reference.Reference.IsAlive); attempt++)
        {
            GC.Collect();
            GC.WaitForPendingFinalizers();
            GC.Collect();
        }

        foreach (var (kind, reference) in references)
            Assert.False(reference.IsAlive, $"the {kind} stayed reachable after the run and the tree were dropped");
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static async Task<List<(string Kind, WeakReference Reference)>> MaterializeAndForget()
    {
        var modules = Modules();
        var parsed = await SourceProvenance.ParseValidAsync(
            $"F(0) = {{\n    open '{ModuleA}'\n    A + 1\n}}\nF(n) = n\nF(0)", modules.Options);
        var placeholder = Placeholder(parsed.Root);
        var region = RegionOf(placeholder);
        var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([2m], result.Value);
        Assert.True(region.TryGetMaterialized(out var materialized));
        return
        [
            ("root", new WeakReference(parsed.Root)),
            ("placeholder", new WeakReference(placeholder)),
            ("region", new WeakReference(region)),
            ("raw body", new WeakReference(region.RawBody)),
            ("materialized body", new WeakReference(materialized)),
            ("loader", new WeakReference(region.Loader)),
        ];
    }
}
