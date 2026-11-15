using System.Diagnostics;
using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// DEFERRED LOAD CYCLES (owner decision 2026-11-15; audit of 2026-11-14 §1.6, "self-reaching
/// deferred regions"). Deferred materialization agrees with eager loading on load cycles: a
/// selected branch whose loads would close a module load cycle — counting the loads written inside
/// other modules' branches — is refused with the existing <see cref="DiagnosticCode.LoadCycle"/>
/// at its FIRST selection, positioned at the import site, never cached, and never a clause
/// non-match. Before, the region's materialized body spliced a module view that contained the
/// region's own placeholder, the composed program graph was cyclic, and the evaluator's
/// deferred-body admission misread each repetition as nesting until
/// <c>AstDepthLimitExceeded</c> (<c>rep.kat</c>: OK at <c>repeat(72)</c>, refused at 73).
///
/// <para>The rule (<c>ModuleLoader.LoadDeferredRegionAsync</c>): a region records the modules in
/// progress at deferral (<see cref="DeferredModuleRegion.ImportChain"/>); its materialization
/// installs that chain as the loader's modules in progress (so a load of a chain module is the
/// ordinary step-4 cycle) and checks every module it splices, hit or miss, for a path in the
/// static import graph back to the chain (<c>ModuleLoader.RefusesCycleClosingSplice</c>). Eager
/// elaboration is unchanged, so a cycle only through branches that are never selected stays
/// accepted. Every program runs through <see cref="KatLangEngine.RunAsync"/> with an in-memory
/// downloader that counts its calls; a test that observes the loader's own state parses the same
/// source with <see cref="Parser.ParseAsync"/> and evaluates that tree. Every source is checked
/// for a clean parse first.</para>
/// </summary>
public class DeferredLoadCycleTests
{
    // Hang guards only, never latency claims (CI thread-pool scheduling can be slow).
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);

    private const string Host = "modules.example";

    private static string Url(string name) => $"https://{Host}/{name}.kat";

    private static string Open(params string[] names)
        => "open " + string.Join(", ", names.Select(name => $"'{Url(name)}'"));

    private static string Branch(string head, string module, string output)
        => $"{head} = {{\n  open '{Url(module)}'\n  {output}\n}}\n";

    private static readonly Dictionary<string, string> Library = new(StringComparer.Ordinal)
    {
        // Self-opening module: its branch opens the module that contains it.
        ["rep"] = "public " + Branch("H(0)", "rep", "5") + "public H(n) = n\n",
        // A→B→A: ma's branch opens mb, which opens ma eagerly.
        ["ma"] = "public " + Branch("H(0)", "mb", "Y") + "public H(n) = n\npublic Z = 1\n",
        ["mb"] = $"{Open("ma")}\npublic Y = Z + 4\n",
        // Two-region cycle: ma2's branch loads mb2, and mb2's branch loads ma2.
        ["ma2"] = "public " + Branch("H(0)", "mb2", "G(0)") + "public H(n) = n\n",
        ["mb2"] = "public " + Branch("G(0)", "ma2", "H(5)") + "public G(n) = n\n",
        // Acyclic shapes.
        ["d"] = "public X = 10\n",
        ["top"] = "public " + Branch("L(0)", "left", "LV") + "public L(n) = n\npublic " + Branch("R(0)", "right", "RV") + "public R(n) = n\n",
        ["left"] = $"public LV = {{ {Open("d")}\n X }}\n",
        ["right"] = $"public RV = {{ {Open("d")}\n X + 1 }}\n",
        ["leftd"] = "public " + Branch("LD(0)", "d", "X") + "public LD(n) = n\npublic LV = LD(0)\n",
        ["rightd"] = "public " + Branch("RD(0)", "d", "X + 1") + "public RD(n) = n\npublic RV = RD(0)\n",
        ["m"] = "public " + Branch("H(0)", "leaf", "Leaf") + "public H(n) = n\n",
        ["leaf"] = "public Leaf = 7\n",
        ["leaf2"] = "public Leaf2 = 8\n",
        ["leaf3"] = "public Leaf3 = 9\n",
        // One loaded module per materialization exit path (see ExitPath).
        ["hub"] = "public " + Branch("K(1)", "leaf", "Leaf")
            + "public " + Branch("K(2)", "fail", "Fail")
            + "public " + Branch("K(3)", "slow", "Slow")
            + "public " + Branch("K(4)", "leaf2", "Nope")
            + "public " + Branch("K(5)", "broken", "1")
            + "public " + Branch("K(6)", "back", "1")
            + "public " + Branch("K(7)", "leaf3", "Leaf3")
            + "public K(n) = n\n",
        ["back"] = $"{Open("hub")}\npublic Back = 1\n",
        ["broken"] = "public X = (\n",
        ["fail"] = "public Fail = 1\n",
        ["slow"] = "public Slow = 1\n",
    };

    // A linear chain c1 → c2 → … → c20: each branch loads the next module on demand.
    private static string ChainModule(int index, int length)
        => index < length
            ? "public " + Branch($"W{index}(0)", $"c{index + 1}", $"V{index + 1}") + $"public W{index}(n) = n\npublic V{index} = W{index}(0)\n"
            : $"public V{length} = {length}\n";

    /// <summary>
    /// An in-memory downloader that counts its calls per URL. <c>fail.kat</c> throws, and
    /// <c>slow.kat</c> waits for its token after signalling that it was entered (both host
    /// behaviors, not module text).
    /// </summary>
    private sealed class CountingModules
    {
        private readonly Dictionary<string, string> _sources;

        public CountingModules(Dictionary<string, string> sources)
            => _sources = sources;

        public Dictionary<string, int> Fetches { get; } = new(StringComparer.Ordinal);

        public int this[string name] => Fetches.GetValueOrDefault(Url(name));

        public int Total => Fetches.Values.Sum();

        public TaskCompletionSource SlowEntered { get; } = new(TaskCreationOptions.RunContinuationsAsynchronously);

        public HostOperations? HostOperations { get; init; }

        public async ValueTask<string> Download(string url, CancellationToken cancellationToken)
        {
            lock (Fetches)
                Fetches[url] = Fetches.GetValueOrDefault(url) + 1;
            var name = url[$"https://{Host}/".Length..^".kat".Length];
            if (name == "fail")
                throw new InvalidOperationException("transport down");
            if (name == "slow")
            {
                SlowEntered.TrySetResult();
                await Task.Delay(Timeout.Infinite, cancellationToken);
            }

            return _sources.TryGetValue(name, out var source) ? source : throw new InvalidOperationException($"404: {url}");
        }

        public RunOptions Options => new()
        {
            AllowedHosts = [Host],
            DownloadCode = Download,
            HostOperations = HostOperations,
        };
    }

    private static CountingModules Modules(Dictionary<string, string>? sources = null, HostOperations? hostOperations = null)
        => new(sources ?? Library) { HostOperations = hostOperations };

    private static string Root(string[] opens, string call, int repetitions)
        => $"{Open(opens)}\nStep(x) = {call} + x\nStep(0).repeat({repetitions})";

    /// <summary>
    /// The source checks every test makes first: each module text parses cleanly as raw syntax,
    /// and the root program passes the whole front end, eager loads included (a cycle through a
    /// deferred branch never makes the parse fail).
    /// </summary>
    private static async Task AssertCleanSources(string root, Dictionary<string, string>? sources = null, HostOperations? hostOperations = null)
    {
        foreach (var module in (sources ?? Library).Where(module => module.Key != "broken"))
            SourceProvenance.ParseSyntaxValidRoot(module.Value);
        Assert.True(Parser.ParseSyntax(Library["broken"]).HasErrors);
        await SourceProvenance.ParseValidAsync(root, Modules(sources, hostOperations).Options);
    }

    private static SourcePosition ImportSite(string root, string module)
    {
        var firstLine = root.Split('\n')[0];
        var column = firstLine.IndexOf($"'{Url(module)}'", StringComparison.Ordinal);
        Assert.True(column >= 0, $"{module} is not opened on the root's first line");
        return new SourcePosition(1, column + 1);
    }

    /// <summary>
    /// The public outcome of a refused selection: ONE <see cref="RunResult.EvalFailure"/> error with
    /// the existing <see cref="KatLangErrorCode.LoadCycle"/> code and message format, naming the
    /// module whose load closes the cycle, positioned at the import site of the module that
    /// contains the selected branch, and outside <see cref="KatLangError.IsResourceLimit"/>.
    /// </summary>
    private static void AssertLoadCycle(RunResult result, string root, string importSite, string closing)
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.LoadCycle, error.Code);
        Assert.False(error.IsResourceLimit);
        Assert.Contains($"load cycle detected: {Url(closing)}", error.Message, StringComparison.Ordinal);
        Assert.Equal(ImportSite(root, importSite), Assert.NotNull(error.Span).Start);
    }

    private static void AssertValue(RunResult result, decimal expected)
    {
        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal([(Decimal128)expected], success.Value.ToAtoms());
    }

    /// <summary>The refused materialization as the evaluator reports it: the region's own failure, carrying LoadCycle.</summary>
    private static void AssertMaterializationLoadCycle<T>(EvalResult<T> result, string closing)
    {
        Assert.True(result.IsError, "the refused selection produced a value");
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        var failure = Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(error);
        var diagnostic = Assert.Single(failure.Diagnostics);
        Assert.Equal(DiagnosticCode.LoadCycle, diagnostic.Code);
        Assert.Equal($"load cycle detected: {Url(closing)}", diagnostic.Message);
        Assert.Equal(KatLangErrorCode.LoadCycle, KatLangError.FromEvalError(result.Error).Code);
        Assert.False(result.Error.IsResourceLimit);
    }

    /// <summary>Every deferred region reachable from <paramref name="root"/>, by reference, in first-reach order.</summary>
    private static List<DeferredModuleRegion> Regions(object root)
    {
        var regions = new List<DeferredModuleRegion>();
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var visited = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>();
        pending.Push(root);
        while (pending.TryPop(out var node))
        {
            if (!visited.Add(node))
                continue;
            if (node is Algorithm { DeferredRegion: { } region } && seen.Add(region))
                regions.Add(region);
            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
                pending.Push(child);
        }

        return regions;
    }

    /// <summary>The one region reachable from <paramref name="root"/> whose written body loads <paramref name="loadedModule"/>.</summary>
    private static DeferredModuleRegion RegionNamed(object root, string loadedModule)
        => Assert.Single(Regions(root), region => WrittenLoadUrls(region.RawBody).Contains(Url(loadedModule)));

    private static HashSet<string> WrittenLoadUrls(Algorithm body)
    {
        var urls = new HashSet<string>(StringComparer.Ordinal);
        var visited = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>();
        pending.Push(body);
        while (pending.TryPop(out var node))
        {
            if (!visited.Add(node))
                continue;
            if (node is Expr expr && expr.TryGetUnresolvedLoadArguments(out var args)
                && args is [Expr.StringLiteral { Value: var url }])
                urls.Add(url);
            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
                pending.Push(child);
        }

        return urls;
    }

    private static async Task AssertFlat(Expr program, HostOperations operations, decimal expected)
    {
        var result = await Evaluator.RunFlatAsync(program, operations, null, null, CancellationToken.None);
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([(Decimal128)expected], result.Value);
    }

    private static void AssertLoaderAtRest(ModuleLoader loader)
    {
        Assert.Equal(0, loader.InProgressModuleCount);
        Assert.Empty(loader.InProgressChain);
        Assert.Equal(0, loader.SourceBudget.CurrentDepth);
    }

    // ── 1. A self-opening module ────────────────────────────────────────────

    [Theory]
    [InlineData(1)]
    [InlineData(72)]
    [InlineData(73)]
    [InlineData(10_000)]
    public async Task SelfOpeningModule_IsRefusedAsALoadCycle_AtItsFirstSelection_InEveryRun(int repetitions)
    {
        var root = Root(["rep"], "H(0)", repetitions);
        await AssertCleanSources(root);

        // A later run selects the branch again and is refused again; each run downloads once.
        for (var run = 0; run < 2; run++)
        {
            var modules = Modules();
            AssertLoadCycle(await KatLangEngine.RunAsync(root, modules.Options), root, importSite: "rep", closing: "rep");
            Assert.Equal(1, modules["rep"]);
            Assert.Equal(1, modules.Total);
        }
    }

    [Fact]
    public async Task SelfOpeningModule_ReselectedOnOneTree_RefusesAgain_WithoutCachingTheFailureOrDownloadingAgain()
    {
        var modules = Modules();
        var parsed = await SourceProvenance.ParseValidAsync(Root(["rep"], "H(0)", 1), modules.Options);
        Assert.Equal(1, modules.Total);
        var region = Assert.Single(Regions(parsed.Root));
        // The chain is the modules in progress at deferral: the region's own module.
        Assert.Equal<string>([Url("rep")], region.ImportChain);
        Assert.Equal(1, region.ImportDepth);

        for (var attempt = 1; attempt <= 3; attempt++)
        {
            AssertMaterializationLoadCycle(await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root)), closing: "rep");
            Assert.Equal(attempt, region.MaterializationAttempts);
            Assert.False(region.IsMaterialized);
            Assert.Equal(1, modules.Total);
            AssertLoaderAtRest(region.Loader);
        }
    }

    // ── 2. A→B→A ────────────────────────────────────────────────────────────

    public static TheoryData<string[], string, string, int> OpenerCycles
    {
        get
        {
            var data = new TheoryData<string[], string, string, int>();
            foreach (var repetitions in new[] { 1, 48, 49 })
            {
                // Only ma: mb is fetched by the materialization and its eager load of ma is the
                // ordinary step-4 cycle (ma is on the installed chain).
                data.Add(["ma"], "ma", "ma", repetitions);
                // ma, then mb: mb is a cache hit whose recorded target ma is on the chain.
                data.Add(["ma", "mb"], "ma", "mb", repetitions);
                // mb, then ma: ma is fetched inside mb, so H(0)'s chain is [mb, ma] and mb is on it.
                data.Add(["mb", "ma"], "mb", "mb", repetitions);
            }

            return data;
        }
    }

    [Theory]
    [MemberData(nameof(OpenerCycles))]
    public async Task BranchOpeningAModuleThatOpensItsOwnModule_IsRefused_AtTheFirstSelection(
        string[] opens, string importSite, string closing, int repetitions)
    {
        var root = Root(opens, "H(0)", repetitions);
        await AssertCleanSources(root);
        var modules = Modules();

        AssertLoadCycle(await KatLangEngine.RunAsync(root, modules.Options), root, importSite, closing);
        Assert.Equal(1, modules["ma"]);
        Assert.Equal(1, modules["mb"]);
        Assert.Equal(2, modules.Total);
    }

    // ── 3. The two-region cycle, in every order ────────────────────────────

    public static TheoryData<string[], string, string, string, int> TwoRegionCycles
    {
        get
        {
            var data = new TheoryData<string[], string, string, string, int>();
            foreach (var repetitions in new[] { 1, 37 })
            {
                data.Add(["ma2"], "H(0)", "ma2", "mb2", repetitions);
                data.Add(["ma2", "mb2"], "H(0)", "ma2", "mb2", repetitions);
                data.Add(["ma2", "mb2"], "G(0)", "mb2", "ma2", repetitions);
                data.Add(["mb2", "ma2"], "H(0)", "ma2", "mb2", repetitions);
                data.Add(["mb2", "ma2"], "G(0)", "mb2", "ma2", repetitions);
                // ma2 is a cache MISS here: only the check of a fetched module refuses it.
                data.Add(["mb2"], "G(0)", "mb2", "ma2", repetitions);
            }

            return data;
        }
    }

    [Theory]
    [MemberData(nameof(TwoRegionCycles))]
    public async Task TwoRegionCycle_IsRefused_AtTheFirstSelectionOfEitherBranch_WhateverTheLoadOrder(
        string[] opens, string call, string importSite, string closing, int repetitions)
    {
        var root = Root(opens, call, repetitions);
        await AssertCleanSources(root);
        var modules = Modules();

        AssertLoadCycle(await KatLangEngine.RunAsync(root, modules.Options), root, importSite, closing);
        Assert.Equal(1, modules["ma2"]);
        Assert.Equal(1, modules["mb2"]);
    }

    [Fact]
    public async Task RefusedCacheMiss_StaysCached_AndItsReselectionIsRefusedAsAHit_WithoutAnotherDownload()
    {
        var modules = Modules();
        var parsed = await SourceProvenance.ParseValidAsync(Root(["mb2"], "G(0)", 1), modules.Options);
        var region = Assert.Single(Regions(parsed.Root));
        Assert.Equal<string>([Url("mb2")], region.ImportChain);
        Assert.Equal(0, region.Loader.LoadCycleReachVisits);

        AssertMaterializationLoadCycle(await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root)), closing: "ma2");
        // ma2 is valid, so it stays cached: only the splice that closes the cycle was refused,
        // and its download stays charged.
        Assert.Equal(2, region.Loader.CachedModuleCount);
        Assert.Equal(1, modules["ma2"]);
        Assert.Equal(2, region.Loader.SourceBudget.ModuleCount);

        // The reselection meets ma2 as a cache HIT, and the hit check gives the same verdict.
        AssertMaterializationLoadCycle(await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root)), closing: "ma2");
        Assert.Equal(2, region.MaterializationAttempts);
        Assert.Equal(1, modules["ma2"]);
        Assert.Equal(2, modules.Total);
        Assert.Equal(2, region.Loader.SourceBudget.ModuleCount);
        AssertLoaderAtRest(region.Loader);
    }

    // ── 4. A cycle only through an unselected branch stays accepted ─────────

    public static TheoryData<string[], string, int, int> UnselectedCycles => new()
    {
        { ["ma"], "H(5)", 15, 1 },
        { ["ma", "mb"], "H(5)", 15, 2 },
        { ["mb", "ma"], "H(5)", 15, 2 },
        { ["ma2"], "H(5)", 15, 1 },
        { ["mb2"], "G(3)", 9, 1 },
        { ["ma2", "mb2"], "G(3)", 9, 2 },
        { ["rep"], "H(5)", 15, 1 },
    };

    [Theory]
    [MemberData(nameof(UnselectedCycles))]
    public async Task CycleOnlyThroughAnUnselectedBranch_StaysAccepted(string[] opens, string call, int expected, int downloads)
    {
        var root = Root(opens, call, 3);
        await AssertCleanSources(root);
        var modules = Modules();

        AssertValue(await KatLangEngine.RunAsync(root, modules.Options), expected);
        Assert.Equal(downloads, modules.Total);
    }

    // ── 5. Acyclic deferred programs are unchanged ──────────────────────────

    public static TheoryData<string, decimal, int> AcyclicPrograms => new()
    {
        // A linear chain of 20 modules loaded on demand, each by the previous one's branch.
        { Branch("F(0)", "c1", "V1") + "F(n) = n\nF(0)", 20, 20 },
        // The same chain with the first module opened eagerly: every region has a chain to check.
        { $"{Open("c1")}\nV1", 20, 20 },
        // A diamond: two branches of the document load the same module.
        { Branch("A(0)", "d", "X") + "A(n) = n\n" + Branch("B(0)", "d", "X + 1") + "B(n) = n\nA(0) + B(0)", 21, 1 },
        // A diamond under a module: two branches load modules that both load d.
        { $"{Open("top")}\nL(0) + R(0)", 21, 4 },
        // One module loaded on demand from two different modules' regions.
        { $"{Open("leftd", "rightd")}\nLV + RV", 21, 3 },
    };

    [Theory]
    [MemberData(nameof(AcyclicPrograms))]
    public async Task AcyclicDeferredProgram_IsUnchanged(string root, decimal expected, int downloads)
    {
        var sources = new Dictionary<string, string>(Library, StringComparer.Ordinal);
        for (var index = 1; index <= 20; index++)
            sources[$"c{index}"] = ChainModule(index, 20);
        await AssertCleanSources(root, sources);
        var modules = Modules(sources);

        AssertValue(await KatLangEngine.RunAsync(root, modules.Options), expected);
        Assert.Equal(downloads, modules.Total);
        Assert.All(modules.Fetches.Values, count => Assert.Equal(1, count));
    }

    [Fact]
    public async Task ImportChain_IsTheModulesInProgressAtDeferral_AndAccumulatesThroughMaterializations()
    {
        // ma is fetched inside mb, so its branch records both modules, outermost first.
        var nested = await SourceProvenance.ParseValidAsync(Root(["mb", "ma"], "H(5)", 1), Modules().Options);
        var region = Assert.Single(Regions(nested.Root));
        Assert.Equal<string>([Url("mb"), Url("ma")], region.ImportChain);
        Assert.Equal(2, region.ImportDepth);

        // A branch of the document records the empty chain; a branch deferred while a
        // materialization walks records the installed chain plus the modules entered since.
        var sources = new Dictionary<string, string>(Library, StringComparer.Ordinal);
        for (var index = 1; index <= 3; index++)
            sources[$"c{index}"] = ChainModule(index, 3);
        var chain = await SourceProvenance.ParseValidAsync(Branch("F(0)", "c1", "V1") + "F(n) = n\nF(0)", Modules(sources).Options);
        var outer = Assert.Single(Regions(chain.Root));
        Assert.Empty(outer.ImportChain);
        var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(chain.Root));
        Assert.Equal([(Decimal128)3], result.Value);
        Assert.True(outer.TryGetMaterialized(out var firstBody));
        var second = RegionNamed(firstBody, "c2");
        Assert.Equal<string>([Url("c1")], second.ImportChain);
        Assert.True(second.TryGetMaterialized(out var secondBody));
        Assert.Equal<string>([Url("c1"), Url("c2")], RegionNamed(secondBody, "c3").ImportChain);
        AssertLoaderAtRest(outer.Loader);
    }

    [Fact]
    public async Task NonCyclicBranch_Selected10000Times_IsUnchanged_AndMaterializesOnce()
    {
        var root = $"{Open("m")}\nStep(x) = H(0) + x\nStep(0).repeat(10000)";
        await AssertCleanSources(root);
        var modules = Modules();

        AssertValue(await KatLangEngine.RunAsync(root, modules.Options), 70_000);
        Assert.Equal(1, modules["m"]);
        Assert.Equal(1, modules["leaf"]);

        // No admission observation counter exists, so the recorded prefix is pinned through its
        // outcome: one materialization, cached, consumed 10,000 times without a structural refusal.
        var parsed = await SourceProvenance.ParseValidAsync(root, Modules().Options);
        var region = Assert.Single(Regions(parsed.Root));
        var flat = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));
        Assert.Equal([(Decimal128)70_000], flat.Value);
        Assert.True(region.IsMaterialized);
        Assert.Equal(1, region.MaterializationAttempts);
        AssertLoaderAtRest(region.Loader);
    }

    // ── 6. The chain is restored after every materialization exit path ─────

    public enum ExitPath
    {
        /// <summary>hub's K(1) loads leaf.kat and publishes.</summary>
        Success = 1,

        /// <summary>hub's K(2) loads fail.kat, whose download throws.</summary>
        DownloaderException = 2,

        /// <summary>hub's K(3) loads slow.kat; the evaluation is cancelled while it downloads.</summary>
        CancellationMidDownload = 3,

        /// <summary>hub's K(4) loads leaf2.kat, but its body reads an undeclared name.</summary>
        FrontEndErrorInTheBody = 4,

        /// <summary>hub's K(5) loads broken.kat, which is not valid KatLang source.</summary>
        InvalidModuleSource = 5,

        /// <summary>hub's K(6) loads back.kat, which opens hub: a cycle after entering a module.</summary>
        LoadCycleAfterEnteringAModule = 6,

        /// <summary>rep's H(0) opens rep: a cycle on the chain itself.</summary>
        LoadCycleOnTheChain = 0,
    }

    private const string ExitPathRoot =
        "open 'https://modules.example/rep.kat', 'https://modules.example/hub.kat'\n"
        + "Choose(0) = H(0)\n"
        + "Choose(100) = {\n  open 'https://modules.example/rep.kat'\n  H(5)\n}\n"
        + "Choose(n) = K(n)\n"
        + "Choose(Pick())";

    [Theory]
    [InlineData(ExitPath.Success)]
    [InlineData(ExitPath.DownloaderException)]
    [InlineData(ExitPath.CancellationMidDownload)]
    [InlineData(ExitPath.FrontEndErrorInTheBody)]
    [InlineData(ExitPath.InvalidModuleSource)]
    [InlineData(ExitPath.LoadCycleAfterEnteringAModule)]
    [InlineData(ExitPath.LoadCycleOnTheChain)]
    public async Task EveryMaterializationExitPath_RestoresTheChain_AndLaterSelectionsAreUnaffected(ExitPath path)
    {
        var pick = (int)path;
        var operations = HostOperations.Create(HostOperation.Create("Pick", (_, _) => new Result.Atom(Volatile.Read(ref pick))));
        await AssertCleanSources(ExitPathRoot, hostOperations: operations);

        // The public outcome of the exit path (the cancellation path is pinned on the tree below).
        if (path != ExitPath.CancellationMidDownload)
        {
            var publicModules = Modules(hostOperations: operations);
            AssertExitPathOutcome(path, await KatLangEngine.RunAsync(ExitPathRoot, publicModules.Options));
        }

        var modules = Modules(hostOperations: operations);
        var parsed = await SourceProvenance.ParseValidAsync(ExitPathRoot, modules.Options);
        var loader = Regions(parsed.Root)[0].Loader;
        var hubRegions = Regions(parsed.Root).Where(region => region.ImportChain.SequenceEqual([Url("hub")])).ToList();
        Assert.Equal(7, hubRegions.Count);
        AssertLoaderAtRest(loader);
        var program = new Expr.AlgorithmExpr(parsed.Root);

        if (path == ExitPath.CancellationMidDownload)
        {
            using var cancellation = new CancellationTokenSource();
            var pending = Evaluator.RunFlatAsync(program, operations, null, null, cancellation.Token);
            await modules.SlowEntered.Task.WaitAsync(WaitLimit);
            // Mid-download the region's chain is installed and slow.kat has entered it.
            Assert.Equal<string>([Url("hub"), Url("slow")], loader.InProgressChain);
            cancellation.Cancel();
            var error = await Assert.ThrowsAsync<OperationCanceledException>(async () => await pending.WaitAsync(WaitLimit));
            Assert.Equal(cancellation.Token, error.CancellationToken);
            // The abandoned work finishes unwinding before it releases the loader's gate.
            await loader.MaterializationGate.WaitAsync().WaitAsync(WaitLimit);
            loader.MaterializationGate.Release();
        }
        else
        {
            var result = await Evaluator.RunFlatAsync(program, operations, null, null, CancellationToken.None);
            AssertExitPathOutcome(path, result.IsError ? KatLangError.FromEvalError(result.Error) : null, result.IsError ? null : result.Value);
        }

        AssertLoaderAtRest(loader);

        // An unrelated region of the same module still materializes normally under its own chain,
        // and a later load of the cycle's module from outside every module is unaffected.
        Volatile.Write(ref pick, 7);
        await AssertFlat(program, operations, 9);
        AssertLoaderAtRest(loader);
        Volatile.Write(ref pick, 100);
        await AssertFlat(program, operations, 5);
        AssertLoaderAtRest(loader);

        // A failed exit path is not cached: selecting it again reports the same failure.
        if (path is not (ExitPath.Success or ExitPath.CancellationMidDownload))
        {
            Volatile.Write(ref pick, (int)path);
            var again = await Evaluator.RunFlatAsync(program, operations, null, null, CancellationToken.None);
            Assert.True(again.IsError);
            AssertExitPathOutcome(path, KatLangError.FromEvalError(again.Error), null);
            AssertLoaderAtRest(loader);
        }
    }

    private static void AssertExitPathOutcome(ExitPath path, RunResult result)
    {
        if (result is RunResult.Success success)
            AssertExitPathOutcome(path, null, success.Value.ToAtoms());
        else
            AssertExitPathOutcome(path, Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors), null);
    }

    private static void AssertExitPathOutcome(ExitPath path, KatLangError? error, IReadOnlyList<Decimal128>? value)
    {
        if (path == ExitPath.Success)
        {
            Assert.Null(error);
            Assert.Equal([(Decimal128)7], value);
            return;
        }

        var failure = Assert.IsType<KatLangError>(error);
        Assert.False(failure.IsResourceLimit);
        Assert.Equal(path switch
        {
            ExitPath.DownloaderException => KatLangErrorCode.LoadFetchFailed,
            ExitPath.FrontEndErrorInTheBody => KatLangErrorCode.UndeclaredIdentifier,
            ExitPath.InvalidModuleSource => KatLangErrorCode.InvalidLoadedSource,
            _ => KatLangErrorCode.LoadCycle,
        }, failure.Code);
        if (path == ExitPath.LoadCycleAfterEnteringAModule)
            Assert.Contains($"load cycle detected: {Url("hub")}", failure.Message, StringComparison.Ordinal);
        if (path == ExitPath.LoadCycleOnTheChain)
            Assert.Contains($"load cycle detected: {Url("rep")}", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task CycleVerdicts_FollowTheKnownModules_ACachedModuleCanAddAPathAnEarlierSpliceDidNotHave()
    {
        // X's branch splices u, then fetches w, then splices u again at a second site. u's only
        // target, w (in u's own branch), is unknown at the first splice, so u does not reach X
        // then. w's branch loads X, so w's splice closes a cycle; once w is cached, u reaches X
        // through it, and the second splice of u is refused as well.
        var sources = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["x"] = "public R(0) = {\n  " + Open("u", "w") + $"\n  U2 = load('{Url("u")}')\n  1\n}}\npublic R(n) = n\n",
            ["u"] = "public " + Branch("UB(0)", "w", "1") + "public UB(n) = n\npublic UV = 1\n",
            ["w"] = "public " + Branch("WB(0)", "x", "1") + "public WB(n) = n\npublic WV = 2\n",
        };
        foreach (var module in sources.Values)
            SourceProvenance.ParseSyntaxValidRoot(module);
        var root = $"{Open("x", "u")}\nR(0)";
        var modules = Modules(sources);
        var parsed = await SourceProvenance.ParseValidAsync(root, modules.Options);
        var region = RegionNamed(parsed.Root, "u");
        Assert.Equal<string>([Url("x")], region.ImportChain);

        var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));

        Assert.True(result.IsError);
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        var failure = Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(error);
        Assert.Equal(
            [$"load cycle detected: {Url("w")}", $"load cycle detected: {Url("u")}"],
            failure.Diagnostics.Select(diagnostic => diagnostic.Message));
        Assert.All(failure.Diagnostics, diagnostic => Assert.Equal(DiagnosticCode.LoadCycle, diagnostic.Code));
        Assert.Equal(1, modules["w"]);
        AssertLoaderAtRest(region.Loader);

        var publicModules = Modules(sources);
        AssertLoadCycle(await KatLangEngine.RunAsync(root, publicModules.Options), root, importSite: "x", closing: "w");
    }

    // ── 7. The reachability walk is linear in the known modules ─────────────

    [Theory]
    [InlineData(125, 1)]
    [InlineData(250, 1)]
    [InlineData(125, 20)]
    [InlineData(250, 20)]
    public async Task CacheHitReachabilityWalk_VisitsEachKnownModuleOnce(int length, int sites)
    {
        // `all` opens m1..mN eagerly, and each m_i's branch loads m_{i+1}: N cached modules
        // chained through deferred edges. m0's branch opens `entry` (a miss), which loads m1 (a
        // hit) at `sites` load sites. The first m1 check walks the whole chain once, and the later
        // sites reuse its verdict; entry's own check, after entry is cached, walks entry plus the
        // chain. Nothing reaches m0, so every splice is accepted: 2N + 1 visits whatever the
        // number of sites (a walk per site would be about (sites + 1) * N). 1,000 modules cannot
        // be cached in one run: every download takes one of at most
        // SourceProcessingLimits.MaxSupportedModuleCount (256) slots, so N + 3 modules stay within it.
        Assert.True(length + 3 <= SourceProcessingLimits.MaxSupportedModuleCount);
        var sources = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["all"] = Open([.. Enumerable.Range(1, length).Select(index => $"m{index}")]) + "\npublic All = 1\n",
            ["m0"] = "public " + Branch("F(0)", "entry", "E") + "public F(n) = n\n",
            ["entry"] = $"{Open("m1")}\n"
                + string.Concat(Enumerable.Range(1, sites - 1).Select(index => $"A{index} = load('{Url("m1")}')\n"))
                + "public E = 1\n",
        };
        for (var index = 1; index <= length; index++)
            sources[$"m{index}"] = index < length
                ? "public " + Branch($"P{index}(0)", $"m{index + 1}", "1") + $"public P{index}(n) = n\n"
                : $"public P{index} = 1\n";
        var root = $"{Open("all", "m0")}\nF(0)";
        foreach (var module in sources.Values)
            SourceProvenance.ParseSyntaxValidRoot(module);

        var publicModules = Modules(sources);
        AssertValue(await KatLangEngine.RunAsync(root, publicModules.Options), 1);
        Assert.Equal(length + 3, publicModules.Total);

        var modules = Modules(sources);
        var parsed = await SourceProvenance.ParseValidAsync(root, modules.Options);
        var region = RegionNamed(parsed.Root, "entry");
        Assert.Equal<string>([Url("m0")], region.ImportChain);
        var loader = region.Loader;
        // Eager elaboration runs no reachability check.
        Assert.Equal(0, loader.LoadCycleReachVisits);

        var clock = Stopwatch.StartNew();
        var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root));
        clock.Stop();

        Assert.Equal([(Decimal128)1], result.Value);
        Assert.Equal(2L * length + 1, loader.LoadCycleReachVisits);
        Assert.True(clock.Elapsed < WaitLimit, $"materialization took {clock.Elapsed}");
        AssertLoaderAtRest(loader);
    }
}
