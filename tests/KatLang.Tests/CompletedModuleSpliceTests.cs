using System.Numerics;
using System.Reflection;
using System.Text;

namespace KatLang.Tests;

/// <summary>
/// COMPLETED MODULE VIEWS (November 2026; C#-only work sharing, no value, diagnostic, classification or limit change,
/// Lean unchanged; <see cref="CompletedModuleViews"/>). A load-bearing clause branch is elaborated when it is selected,
/// as a front-end operation of its own. When its body splices a module an earlier operation completed, it receives that
/// module's one declaration, yet every selection still walked the whole module: the loader's two structural gates over
/// the composed body and its unresolved-load check, the static admission measure, signature analysis of the module's
/// bodies, and the walk of the module's free reference names behind the branch's region key. Measured before (Release,
/// one later selection of a branch that opens a completed module of W members, each <c>public F(x) = Helper(x) + i</c>):
/// 6,266 KiB at 1,000 members and 23,486 KiB at 4,000. Signature analysis used 3,921 / 14,200 KiB, each loader gate
/// 442 / 1,915 KiB, the load check 394 / 1,680 KiB and the measure 333 / 1,433 KiB. After sharing: about 651 / 1,975 KiB,
/// and about 320 / 545 KiB once exposure's shared-body census took each resolved declaration's census unit instead of
/// walking it (331 / 1,432 KiB, 2026-11-25).
///
/// <para>These tests pin, with a fixed in-memory downloader:</para>
/// <list type="bullet">
///   <item>THE WORK BOUND: from the second selection on, the stage counters (composed-body gate edges, load-check
///   expansions, admission edges, analyzed bodies) are the same for a module of 24 members and one of 240, and every
///   counter is the same in the layouts whose other work does not read the module's width; the first selection that
///   splices the view (cold) and every selection without the store (the reference mode) grow with the width;</item>
///   <item>EQUALITY: over a corpus of module programs, the values or errors, the diagnostics, and the exposure metadata and
///   signatures of every materialized body are the same with the store, without it, and in the verifying mode, which
///   recomputes every reused fact and every reused walk the ordinary way and throws on a difference;</item>
///   <item>ISOLATION AND LIMITS: an attempt that publishes nothing (refused, malformed module, cancelled, over a limit)
///   leaves nothing and reports the same diagnostics cold and warm; concurrent runs publish what a sequential run
///   publishes; one parse never reads another's; a low aggregate, a low static-structure envelope and a composed body
///   deeper than the elaboration ceiling are refused exactly as the ordinary walks refuse them.</item>
/// </list>
/// </summary>
public class CompletedModuleSpliceTests
{
    private const string Host = "modules.example";

    private static string Url(string name) => $"https://{Host}/{name}.kat";

    private const string Tiny = "public V = 1\npublic W(x) = x * 2\n";

    private const string Tiny2 = "public Z = 4\npublic Q(x) = x - 1\n";

    /// <summary>The in-memory host of one run over one library: download counts per module.</summary>
    private sealed class RunHost(IReadOnlyDictionary<string, string> library, SourceProcessingLimits? limits = null)
    {
        public Dictionary<string, int> Fetches { get; } = new(StringComparer.Ordinal);

        public int TotalFetches => Fetches.Values.Sum();

        public RunOptions Options => new()
        {
            AllowedHosts = [Host],
            SourceProcessingLimits = limits,
            DownloadCode = (url, _) =>
            {
                lock (Fetches)
                    Fetches[url] = Fetches.GetValueOrDefault(url) + 1;
                var name = url[$"https://{Host}/".Length..^".kat".Length];
                return library.TryGetValue(name, out var source)
                    ? ValueTask.FromResult(source)
                    : throw new InvalidOperationException($"404: {url}");
            },
        };
    }

    public sealed record Program(string Name, string Source, IReadOnlyDictionary<string, string> Library, string[] Families)
    {
        public override string ToString() => Name;
    }

    private static async Task<Algorithm.User> ParseDeferred(Program program, RunHost host)
    {
        var parsed = await SourceProvenance.ParseValidAsync(program.Source, host.Options);
        Assert.Empty(parsed.Diagnostics);
        Assert.True(DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.AlgorithmExpr(parsed.Root)), "the program holds no deferred region");
        return parsed.Root;
    }

    private static Task<EvalResult<IReadOnlyList<Decimal128>>> RunFlat(Algorithm.User root, CancellationToken cancellationToken = default)
        => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), null, cancellationToken);

    /// <summary>The region of the one deferred clause of the family at <paramref name="path"/> below <paramref name="owner"/>.</summary>
    private static DeferredModuleRegion RegionAt(Algorithm owner, params string[] path)
    {
        for (var index = 0; index < path.Length - 1; index++)
            owner = owner.Properties.Single(property => property.Name == path[index]).Value;
        var family = Assert.IsType<Algorithm.Conditional>(owner.Properties.Single(property => property.Name == path[^1]).Value);
        var region = Assert.Single(family.Branches, static branch => branch.Body.DeferredRegion is not null).Body.DeferredRegion;
        Assert.NotNull(region);
        return region;
    }

    private static CompletedModuleViews StoreOf(DeferredModuleRegion region) => region.Loader.ModuleUnits.CompletedViews;

    /// <summary>Runs <paramref name="run"/> with every materialization it starts in <paramref name="mode"/>.</summary>
    private static async Task<T> In<T>(CompletedModuleViews.Mode mode, Func<Task<T>> run)
    {
        var saved = CompletedModuleViews.ModeForTesting.Value;
        CompletedModuleViews.ModeForTesting.Value = mode;
        try
        {
            return await run();
        }
        finally
        {
            CompletedModuleViews.ModeForTesting.Value = saved;
        }
    }

    /// <summary>Every numeric counter of one materialization, by name.</summary>
    private static SortedDictionary<string, long> Counters(FrontEndTraversalObservations observations)
    {
        var counters = new SortedDictionary<string, long>(StringComparer.Ordinal);
        foreach (var property in typeof(FrontEndTraversalObservations).GetProperties(BindingFlags.Public | BindingFlags.Instance))
        {
            if (property.GetIndexParameters().Length != 0)
                continue;
            if (property.PropertyType == typeof(long))
                counters[property.Name] = (long)property.GetValue(observations)!;
            else if (property.PropertyType == typeof(int))
                counters[property.Name] = (int)property.GetValue(observations)!;
        }

        return counters;
    }

    private static string Render(SortedDictionary<string, long> counters)
        => string.Join(", ", counters.Where(static counter => counter.Value != 0).Select(static counter => $"{counter.Key}={counter.Value}"));

    /// <summary>The counters of the stages this store narrows: what each stage walked of the composed body.</summary>
    private static readonly string[] StageCounters =
    [
        nameof(FrontEndTraversalObservations.DeferredCompositionGateEdges),
        nameof(FrontEndTraversalObservations.DeferredLoadCheckExpansions),
        nameof(FrontEndTraversalObservations.DeferredAdmissionEdges),
        nameof(FrontEndTraversalObservations.SignatureAnalysisBodies),
        nameof(FrontEndTraversalObservations.SignatureAnalysisExpansions),
        nameof(FrontEndTraversalObservations.ContextEntriesWritten),
        nameof(FrontEndTraversalObservations.DeferredCensusExpansions),
    ];

    private static string StageView(SortedDictionary<string, long> counters)
        => string.Join(", ", StageCounters.Select(name => $"{name}={counters.GetValueOrDefault(name)}"));

    // ── The wide programs ───────────────────────────────────────────────────

    public enum Layout
    {
        /// <summary>Every branch opens the module; nothing loads it eagerly, so the first selection fetches and completes it.</summary>
        BranchOpens,

        /// <summary>The root opens the module and every branch opens it again: the parse completed it.</summary>
        RootAndBranchOpen,

        /// <summary>A root property holds the module and every branch opens it: the parse completed it.</summary>
        RootPropertyBranchOpens,

        /// <summary>Every branch holds the module in a property of its own and reads a member path.</summary>
        BranchProperty,
    }

    private static string MemberLines(int width, string prefix = "F")
    {
        var text = new StringBuilder("Helper(x) = x * 2\n");
        for (var index = 0; index < width; index++)
            text.Append($"public {prefix}{index}(x) = Helper(x) + {index}\n");
        return text.ToString();
    }

    /// <summary><paramref name="branches"/> families <c>G0 …</c>, each with one load-bearing branch that splices the module and reads member <c>F&lt;i&gt;</c>.</summary>
    private static Program Wide(Layout layout, int width, int branches)
    {
        var library = new Dictionary<string, string>(StringComparer.Ordinal) { ["lib"] = MemberLines(width) };
        var source = new StringBuilder();
        if (layout == Layout.RootAndBranchOpen)
            source.Append($"open '{Url("lib")}'\n");
        else if (layout == Layout.RootPropertyBranchOpens)
            source.Append($"Lib = load('{Url("lib")}')\n");

        var families = new string[branches];
        for (var index = 0; index < branches; index++)
        {
            families[index] = $"G{index}";
            var body = layout == Layout.BranchProperty
                ? $"    L = load('{Url("lib")}')\n    L.F{index}(n)\n"
                : $"    open '{Url("lib")}'\n    F{index}(n)\n";
            source.Append($"G{index}(0) = 0\nG{index}(n) = {{\n{body}}}\n");
        }

        for (var index = 0; index < branches; index++)
            source.Append($"G{index}(1)\n");
        return new($"{layout}/{width}", source.ToString(), library, families);
    }

    /// <summary>
    /// Materializes every family's region in order through the real <see cref="DeferredModuleRegion.MaterializeAsync"/>,
    /// each with a fresh observer on its loader: the counters of that one materialization, and the bytes it allocated on
    /// the calling thread (a synchronously completing downloader runs it inline).
    /// </summary>
    private static async Task<(SortedDictionary<string, long>[] Work, long[] Allocated, DeferredModuleRegion[] Regions, Algorithm.User Root)> MaterializeAll(
        Program program, CompletedModuleViews.Mode mode)
    {
        var host = new RunHost(program.Library);
        var root = await ParseDeferred(program, host);
        var count = program.Families.Length;
        var work = new SortedDictionary<string, long>[count];
        var allocated = new long[count];
        var regions = new DeferredModuleRegion[count];
        await In(mode, async () =>
        {
            for (var index = 0; index < count; index++)
            {
                var region = regions[index] = RegionAt(root, program.Families[index]);
                var observations = new FrontEndTraversalObservations();
                region.Loader.TraversalObservations = observations;
                var before = GC.GetAllocatedBytesForCurrentThread();
                var pending = region.MaterializeAsync(CancellationToken.None);
                Assert.True(pending.IsCompleted, "the materialization left the calling thread");
                var body = await pending;
                allocated[index] = GC.GetAllocatedBytesForCurrentThread() - before;
                Assert.True(body.IsOk, body.IsOk ? "" : body.Error.ToString());
                work[index] = Counters(observations);
            }

            return 0;
        });
        return (work, allocated, regions, root);
    }

    // ── The work bound ──────────────────────────────────────────────────────

    /// <summary>
    /// THE BOUND. Five branches splice one module and read five of its members. From the second selection on, what the
    /// composed-body gate, the load check, the admission measure, signature analysis and exposure's shared-body census
    /// walk is the same for a module of 24 members and one of 240: each takes the published facts of the completed view
    /// (and its published free reference names, the completing operation's resolved signatures, and the resolved
    /// declaration's census unit) instead of walking it. In the three layouts whose other work does not read the module's
    /// width, EVERY counter is the same from the second selection on, and in the fourth (a branch that holds the module
    /// in a property of its own) from the third. The first selection that splices the view is the cold control (it walks
    /// the view once and publishes its facts), and the reference mode is the control for the defect: there every
    /// selection walks the module again in every stage.
    /// </summary>
    [Theory]
    [InlineData(Layout.BranchOpens)]
    [InlineData(Layout.RootAndBranchOpen)]
    [InlineData(Layout.RootPropertyBranchOpens)]
    [InlineData(Layout.BranchProperty)]
    public async Task LaterSelections_DoNoWorkInTheWidthOfASplicedCompletedModule(Layout layout)
    {
        const int branches = 5;
        const int narrowWidth = 24;
        const int wideWidth = 240;
        var narrow = await MaterializeAll(Wide(layout, narrowWidth, branches), CompletedModuleViews.Mode.Shared);
        var wide = await MaterializeAll(Wide(layout, wideWidth, branches), CompletedModuleViews.Mode.Shared);
        var completedByTheParse = layout is Layout.RootAndBranchOpen or Layout.RootPropertyBranchOpens;

        // Cold: the first selection walks the view in the gate, the load check, the measure and the exposure census, and
        // publishes its facts.
        foreach (var stage in new[] { "DeferredCompositionGateEdges", "DeferredLoadCheckExpansions", "DeferredAdmissionEdges", "DeferredCensusExpansions" })
            Assert.True(wide.Work[0][stage] - narrow.Work[0][stage] >= wideWidth - narrowWidth, $"{stage}: {StageView(narrow.Work[0])} / {StageView(wide.Work[0])}");
        Assert.Equal(1, wide.Work[0]["CompletedModuleViewsPublished"]);
        Assert.Equal(0, wide.Work[0]["CompletedModuleViewReuses"]);
        Assert.Equal(0, wide.Work[0]["CompletedModuleCensusReuses"]);
        // A module the parse completed is never analyzed again; one the first selection fetches is analyzed there, once.
        Assert.Equal(completedByTheParse ? 1 : 0, wide.Work[0]["CompletedModuleAnalysesSkipped"]);
        if (!completedByTheParse)
            Assert.True(wide.Work[0]["SignatureAnalysisBodies"] >= wideWidth, StageView(wide.Work[0]));

        // Warm: the module's width is no input of a later selection's stages.
        for (var index = 1; index < branches; index++)
        {
            Assert.True(StageCounters.All(name => narrow.Work[index].GetValueOrDefault(name) == wide.Work[index].GetValueOrDefault(name)),
                $"selection {index}:\n  {narrowWidth}: {StageView(narrow.Work[index])}\n  {wideWidth}: {StageView(wide.Work[index])}");
            // One reuse per stage: the gate took the view's height, the load check skipped it, the measure counted its unit;
            // and the exposure census took the resolved declaration's census unit.
            Assert.Equal(3, wide.Work[index]["CompletedModuleViewReuses"]);
            Assert.Equal(1, wide.Work[index]["CompletedModuleCensusReuses"]);
            Assert.Equal(1, wide.Work[index]["CompletedModuleAnalysesSkipped"]);
            Assert.Equal(1, wide.Work[index]["CompletedModuleFreeNameReuses"]);
            Assert.Equal(0, wide.Work[index]["CompletedModuleViewsPublished"]);
            Assert.True(wide.Work[index]["SignatureAnalysisBodies"] < narrowWidth, StageView(wide.Work[index]));
            // A branch that holds the module in its own property summarizes the module once more at its second selection,
            // the first that reads it as an earlier operation's completed content, which keeps that summary; from the
            // third on it adopts it (CompletedProviderSummaries, A module a branch holds; CompletedProviderSummaryTests).
            if (layout != Layout.BranchProperty || index >= 2)
                Assert.True(narrow.Work[index].SequenceEqual(wide.Work[index]),
                    $"selection {index}:\n  {narrowWidth}: {Render(narrow.Work[index])}\n  {wideWidth}: {Render(wide.Work[index])}");
        }

        Assert.Equal(1, StoreOf(wide.Regions[0]).Count);
        Assert.True(StoreOf(wide.Regions[0]).HasPublished(wide.Regions[0].Loader.CachedViewOf(Url("lib"))!));

        // The reference: without the store every selection walks the module in every stage, as every one did before.
        var unshared = await MaterializeAll(Wide(layout, wideWidth, branches), CompletedModuleViews.Mode.Unshared);
        // On the same cold body, the reference walks all edges twice, once at each ceiling.
        Assert.Equal(2 * wide.Work[0]["DeferredCompositionGateEdges"], unshared.Work[0]["DeferredCompositionGateEdges"]);
        for (var index = 0; index < branches; index++)
        {
            foreach (var stage in new[] { "DeferredCompositionGateEdges", "DeferredLoadCheckExpansions", "DeferredAdmissionEdges", "SignatureAnalysisBodies",
                "DeferredCensusExpansions" })
                Assert.True(unshared.Work[index][stage] >= wideWidth, $"selection {index}, {stage}: {StageView(unshared.Work[index])}");
            Assert.Equal(0, unshared.Work[index]["CompletedModuleViewReuses"]);
            Assert.Equal(0, unshared.Work[index]["CompletedModuleCensusReuses"]);
            Assert.Equal(0, unshared.Work[index]["CompletedModuleAnalysesSkipped"]);
            Assert.Equal(0, unshared.Work[index]["CompletedModuleFreeNameReuses"]);
        }

        Assert.Equal(0, StoreOf(unshared.Regions[0]).Count);
    }

    /// <summary>
    /// A coarse allocation bound over the same programs (in-process: a later selection allocates hundreds of kilobytes,
    /// far above the ~8 KB counter quantum; the minimum over the later selections damps a collection in the window). What
    /// a later selection allocates PER MODULE MEMBER fell more than tenfold in a Release harness (about 5.6 KB to 0.5 KB at
    /// 1,000 members, and to under 0.1 KB between 1,000 and 4,000 members once exposure's census took the declaration's
    /// census unit; the rest is the per-attempt lookup index of the branch's own open level, a documented residual), so
    /// the slope with the store is held below a quarter of the reference's.
    /// </summary>
    [Fact]
    public async Task LaterSelections_AllocateLittleInTheWidthOfASplicedCompletedModule()
    {
        const int branches = 5;
        // Warm-up: the first run of each mode pays type loading and JIT for its paths.
        await MaterializeAll(Wide(Layout.BranchOpens, 40, branches), CompletedModuleViews.Mode.Shared);
        await MaterializeAll(Wide(Layout.BranchOpens, 40, branches), CompletedModuleViews.Mode.Unshared);

        async Task<long> LaterSelection(int width, CompletedModuleViews.Mode mode)
            => (await MaterializeAll(Wide(Layout.BranchOpens, width, branches), mode)).Allocated[1..].Min();

        const int narrowWidth = 300;
        const int wideWidth = 1200;
        var sharedSlope = (double)(await LaterSelection(wideWidth, CompletedModuleViews.Mode.Shared)
            - await LaterSelection(narrowWidth, CompletedModuleViews.Mode.Shared)) / (wideWidth - narrowWidth);
        var unsharedSlope = (double)(await LaterSelection(wideWidth, CompletedModuleViews.Mode.Unshared)
            - await LaterSelection(narrowWidth, CompletedModuleViews.Mode.Unshared)) / (wideWidth - narrowWidth);

        Assert.True(unsharedSlope > 1000, $"without the store a later selection allocated {unsharedSlope:F0} bytes per module member");
        Assert.True(sharedSlope * 4 < unsharedSlope,
            $"a later selection allocated {sharedSlope:F0} bytes per module member with the store and {unsharedSlope:F0} without");
    }

    // ── Equality over a corpus ──────────────────────────────────────────────

    private static readonly (string Kind, string[] Lines, string[] Reads)[] MemberKinds =
    [
        ("plain", ["public F0(x) = x + 0", "public F1(x) = x + 1", "public F2(x) = x + 2"], ["F0", "F1", "F2"]),
        ("const", ["public Base = 10", "public F0(x) = x + Base", "public F1(x) = x * Base", "public F2(x) = Base"], ["F0", "F1", "F2"]),
        ("helper", ["Helper(x) = x * 2", "public F0(x) = Helper(x) + 0", "public F1(x) = Helper(Helper(x))", "public F2(x) = x"], ["F0", "F1", "F2"]),
        ("chain", ["public F0(x) = x", "public F1(x) = F0(x) + 1", "public F2(x) = F1(x) + F0(x)"], ["F0", "F1", "F2"]),
        ("builtin", ["public F0(x) = sqrt(x) + 0", "public F1(x) = abs(x) + sqrt(x * x)", "public F2(x) = abs(0 - x)"], ["F0", "F1", "F2"]),
        ("mutual", ["public F0(x) = if(x <= 0, 0, F1(x - 1))", "public F1(x) = if(x <= 0, 1, F0(x - 1))", "public F2(x) = F0(x) + F1(x)"],
            ["F0", "F1", "F2"]),
        ("family", ["public F0(0) = 10", "public F0(x) = x + 1", "public F1(x) = F0(x) + F0(0)", "public F2(x) = x"], ["F0", "F1", "F2"]),
        ("nested", ["Inner = {\n    public Deep(x) = x + 7\n    Hidden = 3\n}", "public F0(x) = Inner.Deep(x)", "public F1(x) = x + 1",
            "public F2(x) = Inner.Deep(Inner.Deep(x))"], ["F0", "F1", "F2"]),
        ("alias", ["public F0(x) = x + 5", "public F1 = F0", "public F2(x) = F1(x) + 1"], ["F0", "F1", "F2"]),
        ("decon", ["a, b = 3, 4", "public F0(x) = x + a", "public F1(x) = x + b", "public F2(x) = a + b"], ["F0", "F1", "F2"]),
        // Members whose signatures are INFERRED: F0 lifts q, F1 lifts F0's q, F2 calls them explicitly.
        ("lifted", ["public F0 = q + 1", "public F1 = F0 * 2", "public F2(x) = F1(x) + F0(x)"], ["F2", "F2", "F2"]),
        ("block", ["public F0(x) = { y = x + 1\n    y * 2 }", "public F1(x) = { T = { public U(z) = z + x }\n    T.U(1) }", "public F2(x) = x"],
            ["F0", "F1", "F2"]),
        // A declaration-level output-spreading marker in the module (D1/R4): the branch's call is spread.
        ("spread", ["public P(x)* = x, x + 1", "public F0(x) = Two(P(x))", "Two(a, b) = a * b", "public F1(x) = x", "public F2(x) = x + 2"],
            ["F0", "F1", "F2"]),
    ];

    private static string ModuleOf(string[] lines, string? opens = null) => (opens is null ? "" : $"open '{Url(opens)}'\n") + string.Join('\n', lines) + "\n";

    /// <summary>Four families, each with one load-bearing branch: <paramref name="head"/> then the row <paramref name="row"/>, all selected.</summary>
    private static (string Source, string[] Families) Families(Func<int, string> head, Func<int, string> row, int branches = 4)
    {
        var text = new StringBuilder();
        for (var index = 0; index < branches; index++)
            text.Append($"G{index}(0) = 0\nG{index}(n) = {{\n{head(index)}    {row(index)}\n}}\n");
        for (var index = 0; index < branches; index++)
            text.Append($"G{index}(1)\n");
        return (text.ToString(), [.. Enumerable.Range(0, branches).Select(static index => $"G{index}")]);
    }

    private static Program Make(string name, string prefix, (string Source, string[] Families) families, Dictionary<string, string> library)
        => new(name, prefix + families.Source, library, families.Families);

    /// <summary>
    /// Small multi-branch programs over completed modules: thirteen kinds of member bodies (plain, a module constant, a
    /// private helper, a chain, builtins, mutual recursion, a clause family, a nested block, an alias, a deconstruction,
    /// inferred signatures, block bodies, an output-spreading marker) in nine layouts (a branch opens the module; the root
    /// opens it too; a root property holds it; a branch holds it in a property of its own; a module that opens another
    /// module, which a branch also opens directly; two modules in one branch; the same view spliced twice in one branch;
    /// a branch that opens a module and that module's own dependency; a nested deferred branch), and special programs: a
    /// branch whose own property lifts the module's inferred members,
    /// a module that holds a placeholder, two URLs serving the same text, and a branch the forwarding rule refuses.
    /// </summary>
    public static TheoryData<Program> Corpus()
    {
        var corpus = new TheoryData<Program>();
        foreach (var (kind, lines, reads) in MemberKinds)
        {
            var library = new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["tiny"] = Tiny,
                ["tiny2"] = Tiny2,
                ["lib"] = ModuleOf(lines),
                ["libopen"] = ModuleOf(lines, opens: "tiny2"),
            };
            string Read(int index) => reads[index % 3];
            void Add(string layout, string prefix, (string, string[]) families) => corpus.Add(Make($"{layout}/{kind}", prefix, families, library));

            Add("branch opens", "", Families(_ => $"    open '{Url("lib")}'\n", index => $"{Read(index)}(n)"));
            Add("root and branch open", $"open '{Url("lib")}'\n",
                Families(_ => $"    open '{Url("tiny")}', '{Url("lib")}'\n", index => $"V + {Read(index)}(n)"));
            Add("root property, branch opens", $"Lib = load('{Url("lib")}')\n",
                Families(_ => $"    open '{Url("lib")}'\n", index => $"Lib.{Read(index)}(n) + {Read(index + 1)}(n)"));
            Add("branch property", "", Families(_ => $"    L = load('{Url("lib")}')\n", index => $"L.{Read(index)}(n)"));
            Add("nested module", "", Families(
                index => index % 2 == 0 ? $"    open '{Url("libopen")}'\n" : $"    open '{Url("tiny2")}'\n",
                index => index % 2 == 0 ? $"{Read(index)}(n)" : "Z + Q(n)"));
            Add("two modules", "", Families(_ => $"    open '{Url("tiny")}', '{Url("lib")}'\n", index => $"V + W(n) + {Read(index)}(n)"));
            Add("same view twice", "", Families(_ => $"    open '{Url("lib")}'\n    L = load('{Url("lib")}')\n",
                index => $"L.{Read(index)}(n) + {Read(index + 1)}(n)"));
            // A module root reached through two parts: the branch opens a module and that module's own dependency.
            Add("module and its dependency", "", Families(_ => $"    open '{Url("libopen")}', '{Url("tiny2")}'\n",
                index => $"Z + {Read(index)}(n)"));
            Add("nested deferred branch", "", Families(
                index => $"    open '{Url("lib")}'\n    H(0) = 1\n    H(m) = {{\n        open '{Url("tiny2")}'\n        Z + {Read(index + 1)}(m)\n    }}\n",
                index => $"{Read(index)}(n) + H(n)"));
        }

        foreach (var special in SpecialPrograms())
            corpus.Add(special);
        return corpus;
    }

    private const string LiftedMembers = "public F0 = q + 1\npublic F1 = F0 * 2\npublic F2(x) = F1(x) + x\n";

    /// <summary>A branch whose OWN property lifts the module's inferred members: its selection reads their final signatures.</summary>
    private static readonly Program BranchLiftsModuleMembers = Make("branch lifts module members", "",
        Families(index => $"    open '{Url("lib")}'\n    H = F{index % 2} + 1\n", _ => "H(n) + F2(n)"),
        new(StringComparer.Ordinal) { ["lib"] = LiftedMembers });

    private const string PlaceholderMembers =
        "public F0(x) = x + 1\npublic P(0) = 0\npublic P(m) = {\n    open 'https://modules.example/tiny2.kat'\n    Z + m\n}\npublic F1(x) = P(x) + 1\n";

    /// <summary>A completed module that holds a load-bearing branch of its own, spliced by every branch.</summary>
    private static readonly Program ModuleHoldingAPlaceholder = Make("module holding a placeholder", "",
        Families(_ => $"    open '{Url("defer")}'\n", index => $"{new[] { "F0", "F1", "P" }[index % 3]}(n)"),
        new(StringComparer.Ordinal) { ["tiny2"] = Tiny2, ["defer"] = PlaceholderMembers });

    /// <summary>Two canonical URLs serving the same text: two views, two declarations, two sets of facts.</summary>
    private static readonly Program SameTextTwoUrls = Make("same text at two urls", "",
        Families(_ => $"    A = load('{Url("lib")}')\n    B = load('{Url("copy")}')\n", index => $"A.F{index % 3}(n) + B.F{(index + 1) % 3}(n)"),
        new(StringComparer.Ordinal) { ["lib"] = ModuleOf(MemberKinds[2].Lines), ["copy"] = ModuleOf(MemberKinds[2].Lines) });

    /// <summary>A closed branch reads a module member whose inferred parameter it cannot forward: the reference stays a zero-argument demand.</summary>
    private static readonly Program ClosedBranchReadsInferredMember = Make("closed branch reads an inferred member", "",
        Families(_ => $"    open '{Url("lib")}'\n", index => $"F{index % 2} + n"),
        new(StringComparer.Ordinal) { ["lib"] = LiftedMembers });

    private static readonly Dictionary<string, string> RefusalLibrary = new(StringComparer.Ordinal)
    {
        ["lib"] = ModuleOf(MemberKinds[2].Lines),
        // A member that needs an enclosing parameter: the forwarding refusal.
        ["m"] = "public X = y * 10\n",
    };

    /// <summary>
    /// A branch that splices the completed module and is REFUSED when selected (the other module's member needs the
    /// enclosing <c>y</c>), selected after a branch that publishes the module's facts and twice more.
    /// </summary>
    private static readonly Program RefusedForwarding = new("refused forwarding",
        $"Good(0) = 0\nGood(n) = {{\n    open '{Url("lib")}'\n    F1(n)\n}}\n"
        + $"Owner(y) = {{\n    F(0) = 0\n    F(n) = {{\n        open '{Url("lib")}', '{Url("m")}'\n        X + F2(n)\n    }}\n    F(1)\n}}\n"
        + "Good(1)\nOwner(5)\n",
        RefusalLibrary, ["Good", "Owner/F", "Owner/F"]);

    private static IEnumerable<Program> SpecialPrograms()
        => [BranchLiftsModuleMembers, ModuleHoldingAPlaceholder, SameTextTwoUrls, ClosedBranchReadsInferredMember, RefusedForwarding];

    /// <summary>The diagnostics of a materialization failure (code, message, span), or the error's text.</summary>
    private static string DescribeError(EvalError error)
    {
        var terminal = error;
        var contexts = new StringBuilder();
        while (terminal is EvalError.WithContext frame)
        {
            contexts.Append(frame.ErrorContext).Append(" > ");
            terminal = frame.Inner;
        }

        return terminal is EvalError.ModuleRegionMaterializationFailed failed
            ? contexts + string.Join(" | ", failed.Diagnostics.Select(static diagnostic => $"{diagnostic.Code}: {diagnostic.Message} @{diagnostic.Span}"))
            : contexts + terminal.ToString();
    }

    /// <summary>The exposure metadata and signature of every algorithm below <paramref name="root"/>, and the regions its tree carries.</summary>
    private static void Describe(object root, StringBuilder text, HashSet<object> seen, List<DeferredModuleRegion> regions)
    {
        var pending = new Stack<object>();
        pending.Push(root);
        while (pending.TryPop(out var node))
        {
            if (!seen.Add(node))
                continue;
            if (node is Algorithm algorithm)
            {
                if (algorithm.DeferredRegion is { } region)
                    regions.Add(region);
                text.Append('(').AppendJoin(',', algorithm.ParameterPatterns.Select(static pattern => pattern.DisplayName)).Append(')');
                if (algorithm is Algorithm.User or Algorithm.Alias)
                {
                    foreach (var property in algorithm.Properties)
                    {
                        text.Append(property.Name).Append(':').Append(property.Exposure).Append(':').Append(property.IsPublic)
                            .Append(':').AppendJoin(',', property.RequiredAncestorParameters);
                        if (property.CaptureRequirements is { } captures)
                            text.Append(':').AppendJoin(',', captures.Select(static capture => capture.ToString()));
                        text.Append(';');
                    }
                }

                text.Append('|');
            }

            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
                pending.Push(child);
        }
    }

    private sealed record Observed(string Outcome, string Exposure, long Reuses, long Skipped, long NameReuses, int Published, int Downloads);

    /// <summary>
    /// One fresh parse of <paramref name="program"/>: every family's region materialized in order, then the values of a
    /// run (or the error and its diagnostics), the exposure metadata and signatures of every body the run materialized,
    /// nested regions included, in discovery order, and what the store reused and kept.
    /// </summary>
    private static async Task<Observed> Observe(Program program, CompletedModuleViews.Mode mode)
    {
        var host = new RunHost(program.Library);
        var root = await ParseDeferred(program, host);
        var top = new List<DeferredModuleRegion>();
        Describe(root, new StringBuilder(), new HashSet<object>(ReferenceEqualityComparer.Instance), top);
        var observations = new FrontEndTraversalObservations();
        top[0].Loader.TraversalObservations = observations;
        var outcome = new StringBuilder();
        await In(mode, async () =>
        {
            // Every family once in order, so the later ones are warm, then the whole program.
            foreach (var family in program.Families)
            {
                var body = await RegionAt(root, family.Split('/')).MaterializeAsync(CancellationToken.None);
                outcome.Append(family).Append(": ").Append(body.IsOk ? "ok" : DescribeError(body.Error)).Append('\n');
            }

            var flat = await RunFlat(root);
            outcome.Append(flat.IsOk ? "values " + string.Join(' ', flat.Value) : "error " + DescribeError(flat.Error));
            return 0;
        });

        var exposure = new StringBuilder();
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var visited = new HashSet<DeferredModuleRegion>(ReferenceEqualityComparer.Instance);
        var queue = new Queue<DeferredModuleRegion>(top);
        while (queue.TryDequeue(out var region))
        {
            if (!visited.Add(region))
                continue;
            if (!region.TryGetMaterialized(out var body))
            {
                exposure.Append("<not materialized>#");
                continue;
            }

            var nested = new List<DeferredModuleRegion>();
            Describe(body, exposure, seen, nested);
            exposure.Append('#');
            foreach (var inner in nested)
                queue.Enqueue(inner);
        }

        return new(outcome.ToString(), exposure.ToString(), observations.CompletedModuleViewReuses, observations.CompletedModuleAnalysesSkipped,
            observations.CompletedModuleFreeNameReuses, StoreOf(top[0]).Count, host.TotalFetches);
    }

    /// <summary>
    /// EQUALITY. Every program of the corpus gives the same outcome — values, or the same refusal with the same
    /// diagnostics (code, message, span) — at every selection, and every body it materializes carries the same exposure
    /// metadata and the same signatures, with the store, without it, and in the verifying mode. In that mode the engine
    /// also walks every reused view the ordinary way (the gate's verdict and height, the load check's verdict and position,
    /// the measure's totals and limits) and recomputes every reused fact from its view, and throws on the first
    /// difference, so an outcome here means no reuse differed. The signature-analysis skip is judged by the outcome: the
    /// reference analyzes the completed module and selects its members' signatures itself.
    /// </summary>
    [Theory]
    [MemberData(nameof(Corpus))]
    public async Task ReusedFacts_AreTheOnesEachMaterializationWouldCompute(Program program)
    {
        var unshared = await Observe(program, CompletedModuleViews.Mode.Unshared);
        var shared = await Observe(program, CompletedModuleViews.Mode.Shared);
        var verified = await Observe(program, CompletedModuleViews.Mode.Verified);

        Assert.Equal(unshared.Outcome, shared.Outcome);
        Assert.Equal(unshared.Outcome, verified.Outcome);
        Assert.Equal(unshared.Exposure, shared.Exposure);
        Assert.Equal(unshared.Exposure, verified.Exposure);
        Assert.Equal(unshared.Downloads, shared.Downloads);
        Assert.Equal(unshared.Downloads, verified.Downloads);
        Assert.Equal((0L, 0L, 0L, 0), (unshared.Reuses, unshared.Skipped, unshared.NameReuses, unshared.Published));
        Assert.Equal((shared.Reuses, shared.Skipped, shared.NameReuses, shared.Published),
            (verified.Reuses, verified.Skipped, verified.NameReuses, verified.Published));

        if (ReferenceEquals(program, RefusedForwarding))
        {
            // Refused at every selection, warm (after Good published) exactly as the reference reports it; the refused
            // attempts publish nothing (Good's module alone is kept).
            var refusals = shared.Outcome.Split('\n').Where(static line => line.StartsWith("Owner/F: ", StringComparison.Ordinal)).ToArray();
            Assert.Equal(2, refusals.Length);
            Assert.Contains(nameof(DiagnosticCode.DeferredBranchForwardsEnclosingParameter), refusals[0], StringComparison.Ordinal);
            Assert.Equal(refusals[0], refusals[1]);
            Assert.Equal(1, shared.Published);
            return;
        }

        if (!ReferenceEquals(program, ClosedBranchReadsInferredMember))
        {
            Assert.StartsWith($"{program.Families[0]}: ok", unshared.Outcome, StringComparison.Ordinal);
            Assert.Contains("values ", unshared.Outcome, StringComparison.Ordinal);
            Assert.DoesNotContain("<not materialized>", shared.Exposure, StringComparison.Ordinal);
        }

        // The corpus exercises the store: every program publishes facts and reuses them in a later selection.
        Assert.True(shared.Published > 0 && shared.Reuses > 0 && shared.Skipped > 0,
            $"{program}: {shared.Published} published, {shared.Reuses} reuses, {shared.Skipped} analyses skipped");
        if (ReferenceEquals(program, SameTextTwoUrls))
            Assert.Equal(2, shared.Published);
    }

    // ── The census of a composition ─────────────────────────────────────────

    private static Algorithm.User Block(params Property[] properties) => new(null, [], [], properties, OutputBundle.Empty);

    private static Algorithm.User Rows(params Expr[] rows) => new(null, [], [], [], rows);

    /// <summary>A hand-built module root: a body carrying the mark of a spliced import view.</summary>
    private static Algorithm.User ModuleRoot(params Property[] properties)
        => new(null, [], [], properties, OutputBundle.Empty) { IsModuleElaborated = true };

    private static Property Member(string name, Algorithm value) => new(name, value, IsPublic: true);

    private static List<Algorithm> AlgorithmsBelow(object root)
    {
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>();
        pending.Push(root);
        var algorithms = new List<Algorithm>();
        while (pending.TryPop(out var node))
        {
            if (!seen.Add(node))
                continue;
            if (node is Algorithm algorithm)
                algorithms.Add(algorithm);
            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
                pending.Push(child);
        }

        return algorithms;
    }

    private static T InViews<T>(CompletedModuleViews.Mode mode, Func<T> run)
    {
        var saved = CompletedModuleViews.ModeForTesting.Value;
        CompletedModuleViews.ModeForTesting.Value = mode;
        try
        {
            return run();
        }
        finally
        {
            CompletedModuleViews.ModeForTesting.Value = saved;
        }
    }

    /// <summary>
    /// THE CENSUS OF A COMPOSITION IS THE ORDINARY CENSUS. Exposure's shared-body census of a materialization counts every
    /// module root its input splices as one unit (<see cref="SharedBodyCensus.OfLoadedBody"/>). Over hand-built bodies
    /// that splice marked module roots, sharing inside one part (a module whose members share an expression holding a
    /// block; a body whose rows share an expression holding a module root; a module whose members share an expression
    /// holding another module root) and sharing ACROSS independently contributed parts (one root held twice by the body;
    /// a dependency two modules splice; a dependency the body and a module both splice), and module roots elaborated to
    /// callable aliases (one only the body reaches, walked as the body's own nodes; one a module reaches, which makes the
    /// census walk the ordinary way), give exactly the bodies the ordinary walk marks, and the same answer for every
    /// algorithm of the graph: cold, where each unit is computed and
    /// staged; warm, where the units an earlier attempt published are taken, in the sharing and the verifying mode; and in
    /// the reference mode, which walks everything. A unit is published only by an attempt that publishes, and only for a
    /// declaration the registry holds as completed.
    /// </summary>
    [Fact]
    public async Task TheCensusOfAComposition_MarksWhatTheOrdinaryWalkMarks_InsideAndAcrossParts()
    {
        Algorithm.User Leaf(string name) => ModuleRoot(Member(name, Rows(new Expr.Num(1))));
        var cases = new List<(string Name, Algorithm.User Root, Algorithm.User[] Modules, Algorithm[] Expected)>();

        var once = Leaf("A");
        cases.Add(("a root reached once", Block(Member("L", once)), [once], []));

        var twice = Leaf("A");
        cases.Add(("one root held twice by the body", Block(Member("L", twice), Member("M", twice)), [twice], [twice]));

        var other = Leaf("A");
        cases.Add(("a distinct module with identical members", Block(Member("L", twice), Member("M", twice), Member("N", other)),
            [twice, other], [twice]));

        var parsed = await ParseDeferred(ModuleHoldingAPlaceholder, new RunHost(ModuleHoldingAPlaceholder.Library));
        var family = Assert.IsType<Algorithm.Conditional>(parsed.Properties.Single(p => p.Name == "G0").Value);
        var deferredBody = family.Branches.Single(b => b.Body.DeferredRegion is not null).Body;
        var deferredModule = ModuleRoot(Member("P", deferredBody));
        var container = ModuleRoot(Member("P", deferredModule));
        cases.Add(("a shared module containing a deferred region", Block(Member("Direct", deferredModule), Member("Container", container)),
            [deferredModule, container], [])); // Marked by both edges, ineligible for a shared region.

        var block = Block(Member("Q", Rows(new Expr.Num(7))));
        var sharedRow = new Expr.Binary(BinaryOp.Add, new Expr.AlgorithmExpr(block), new Expr.Num(1));
        var inside = ModuleRoot(Member("A", Rows(sharedRow)), Member("B", Rows(sharedRow)));
        cases.Add(("an expression two members of a module share", Block(Member("L", inside)), [inside], [block]));

        var dependency = Leaf("D");
        var left = ModuleRoot(Member("X", dependency));
        var right = ModuleRoot(Member("Y", dependency));
        cases.Add(("a dependency two modules splice", Block(Member("L", left), Member("R", right)), [left, right, dependency], [dependency]));

        var direct = Leaf("D");
        var holder = ModuleRoot(Member("X", direct));
        cases.Add(("a dependency the body and a module splice", Block(Member("L", holder), Member("D", direct)), [holder, direct], [direct]));

        var belowBody = Leaf("A");
        var bodyRow = new Expr.Binary(BinaryOp.Add, new Expr.AlgorithmExpr(belowBody), new Expr.Num(1));
        cases.Add(("a root below an expression the body shares", Block(Member("P", Rows(bodyRow)), Member("Q", Rows(bodyRow))),
            [belowBody], [belowBody]));

        var belowUnit = Leaf("D");
        var unitRow = new Expr.Binary(BinaryOp.Add, new Expr.AlgorithmExpr(belowUnit), new Expr.Num(1));
        var sharing = ModuleRoot(Member("A", Rows(unitRow)), Member("B", Rows(unitRow)));
        cases.Add(("a root below an expression a module shares", Block(Member("L", sharing)), [sharing, belowUnit], [belowUnit]));

        // A module root elaborated to a callable alias is no unit. The body walks one only it reaches as its own nodes; a
        // unit that reaches one makes the census walk the ordinary way, whether the body reaches it too or not.
        Algorithm.Alias AliasRoot() => new(new Algorithm.User(null, [], [], [], [new Expr.Resolve("abs")]) { IsModuleElaborated = true },
            new Expr.Resolve("abs"));
        var bodyAlias = AliasRoot();
        var beside = Leaf("A");
        cases.Add(("an alias root the body holds twice", Block(Member("L", bodyAlias), Member("M", bodyAlias), Member("N", beside)),
            [beside], [bodyAlias]));
        var alias = AliasRoot();
        var aliasHolder = ModuleRoot(Member("X", alias));
        cases.Add(("an alias root the body and a module splice", Block(Member("L", alias), Member("M", aliasHolder)), [aliasHolder], [alias]));
        var innerAlias = AliasRoot();
        var aliasTwice = ModuleRoot(Member("X", innerAlias), Member("Y", innerAlias));
        cases.Add(("an alias root a module splices twice", Block(Member("L", aliasTwice)), [aliasTwice], [innerAlias]));

        foreach (var (name, root, modules, expected) in cases)
        {
            var composes = !modules.Any(static module => AlgorithmsBelow(module).Any(static algorithm => algorithm is Algorithm.Alias { IsModuleElaborated: true }));
            var ordinary = SharedBodyCensus.Of(root);
            var algorithms = AlgorithmsBelow(root);
            Assert.All(algorithms, algorithm => Assert.Equal(expected.Contains(algorithm, ReferenceEqualityComparer.Instance), ordinary?.Holds(algorithm) == true));

            void AssertOrdinary(SharedBodyCensus? census, string at)
            {
                Assert.True(SharedBodyCensus.SameBodies(ordinary, census), $"{name}, {at}: the census by units differs from the ordinary walk");
                Assert.All(algorithms, algorithm => Assert.Equal(ordinary?.Holds(algorithm) == true, census?.Holds(algorithm) == true));
            }

            var registry = new ModuleUnitRegistry();
            var reference = new FrontEndTraversalObservations();
            AssertOrdinary(InViews(CompletedModuleViews.Mode.Unshared,
                () => SharedBodyCensus.OfLoadedBody(root, registry.CompletedViews.BeginAttempt(registry, reference))), "reference");

            // Cold. Its modules are not completed units of the registry, so publishing it keeps nothing.
            var cold = new FrontEndTraversalObservations();
            var attempt = InViews(CompletedModuleViews.Mode.Shared, () => registry.CompletedViews.BeginAttempt(registry, cold));
            AssertOrdinary(SharedBodyCensus.OfLoadedBody(root, attempt), "cold");
            Assert.Equal(0, cold.CompletedModuleCensusReuses);
            // Composed cold, every node is expanded once, by the body's part or by the one unit it belongs to.
            if (composes)
                Assert.Equal(reference.DeferredCensusExpansions, cold.DeferredCensusExpansions);
            attempt.Publish();
            void AssertNothingKept(string at)
            {
                var next = new FrontEndTraversalObservations();
                AssertOrdinary(InViews(CompletedModuleViews.Mode.Shared,
                    () => SharedBodyCensus.OfLoadedBody(root, registry.CompletedViews.BeginAttempt(registry, next))), at);
                Assert.Equal((0L, cold.DeferredCensusExpansions), (next.CompletedModuleCensusReuses, next.DeferredCensusExpansions));
            }

            AssertNothingKept("after a publication of modules the registry does not hold");

            // The registry holds every module as a completed unit. An attempt that publishes nothing still leaves nothing;
            // a publishing one keeps their units.
            var completed = new Dictionary<Algorithm, Algorithm>(ReferenceEqualityComparer.Instance);
            foreach (var module in modules)
                completed.Add(module, module);
            registry.Publish([new(ReferenceEqualityComparer.Instance), new(ReferenceEqualityComparer.Instance), completed], continuation: null);
            attempt = InViews(CompletedModuleViews.Mode.Shared, () => registry.CompletedViews.BeginAttempt(registry, observations: null));
            AssertOrdinary(SharedBodyCensus.OfLoadedBody(root, attempt), "unpublished");
            AssertNothingKept("after an attempt that published nothing");
            attempt.Publish();

            foreach (var mode in new[] { CompletedModuleViews.Mode.Shared, CompletedModuleViews.Mode.Verified })
            {
                var warm = new FrontEndTraversalObservations();
                AssertOrdinary(InViews(mode, () => SharedBodyCensus.OfLoadedBody(root, registry.CompletedViews.BeginAttempt(registry, warm))), $"warm {mode}");
                if (composes)
                {
                    // Every distinct module root is taken as published; only the body's own nodes are walked.
                    Assert.Equal(modules.Length, warm.CompletedModuleCensusReuses);
                    Assert.True(warm.DeferredCensusExpansions < cold.DeferredCensusExpansions, $"{name}: {warm.DeferredCensusExpansions} warm, {cold.DeferredCensusExpansions} cold");
                }
                else
                {
                    // The ordinary walk ran: every node was expanded again.
                    Assert.True(warm.DeferredCensusExpansions >= reference.DeferredCensusExpansions,
                        $"{name}: {warm.DeferredCensusExpansions} warm, {reference.DeferredCensusExpansions} in the reference");
                }
            }
        }
    }

    // ── Isolation ───────────────────────────────────────────────────────────

    private static (DiagnosticCode Code, string Message, SourceSpan? Span)[] Diagnostics(EvalResult<Algorithm> refused)
    {
        Assert.True(refused.IsError, "the selection published a body");
        var failure = Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(refused.Error);
        return [.. failure.Diagnostics.Select(static diagnostic => (diagnostic.Code, diagnostic.Message, diagnostic.Span))];
    }

    /// <summary>
    /// AN ATTEMPT THAT PUBLISHES NOTHING LEAVES NOTHING. A branch that splices the module and is refused when selected
    /// stages the module's facts at every selection and drops them with the attempt: the store stays empty, and every
    /// refused selection walks the module again and reports the same diagnostic. Once another branch has published, the
    /// refused one reuses the facts and still reports exactly the diagnostic of its cold selection: code, message, span.
    /// </summary>
    [Fact]
    public async Task ARefusedAttempt_LeavesNothing_AndReportsTheSameBeforeAndAfterOthersPublish()
    {
        var host = new RunHost(RefusalLibrary);
        var root = await ParseDeferred(RefusedForwarding, host);
        var refusedRegion = RegionAt(root, "Owner", "F");
        var store = StoreOf(refusedRegion);

        (DiagnosticCode Code, string Message, SourceSpan? Span)[]? cold = null;
        SortedDictionary<string, long>? coldWork = null;
        for (var selection = 1; selection <= 3; selection++)
        {
            var observations = new FrontEndTraversalObservations();
            refusedRegion.Loader.TraversalObservations = observations;
            var diagnostics = Diagnostics(await refusedRegion.MaterializeAsync(CancellationToken.None));
            Assert.Equal(DiagnosticCode.DeferredBranchForwardsEnclosingParameter, Assert.Single(diagnostics).Code);
            Assert.Equal(0, observations.CompletedModuleViewReuses);
            Assert.Equal(0, observations.CompletedModuleViewsPublished);
            Assert.Equal(0, store.Count);
            Assert.False(refusedRegion.IsMaterialized);
            var work = Counters(observations);
            if (cold is null)
                (cold, coldWork) = (diagnostics, work);
            else
            {
                Assert.Equal(cold, diagnostics);
                Assert.Equal(StageView(coldWork!), StageView(work));
            }
        }

        // A branch that publishes makes the module's facts visible.
        var good = await RegionAt(root, "Good").MaterializeAsync(CancellationToken.None);
        Assert.True(good.IsOk, good.IsOk ? "" : good.Error.ToString());
        Assert.Equal(1, store.Count);

        // The refused branch reuses them now, and is refused exactly as before.
        var warm = new FrontEndTraversalObservations();
        refusedRegion.Loader.TraversalObservations = warm;
        Assert.Equal(cold, Diagnostics(await refusedRegion.MaterializeAsync(CancellationToken.None)));
        Assert.True(warm.CompletedModuleViewReuses > 0, "the refused attempt reused nothing after another branch published");
        Assert.True(warm.DeferredCompositionGateEdges < coldWork!["DeferredCompositionGateEdges"],
            $"{warm.DeferredCompositionGateEdges} gate edges warm, {coldWork["DeferredCompositionGateEdges"]} cold");
        Assert.False(refusedRegion.IsMaterialized);
        // Whatever the refused attempts staged (the second module's facts too) was dropped.
        Assert.Equal(1, store.Count);
        Assert.False(store.HasPublished(refusedRegion.Loader.CachedViewOf(Url("m"))!));

        var flat = await RunFlat(root);
        Assert.True(flat.IsError, "the refused branch evaluated");
    }

    /// <summary>
    /// A CANCELLED ATTEMPT LEAVES NOTHING. The attempt is cancelled at its unit's freeze, after its load staged the module's
    /// facts; the cancellation keeps the evaluation token's identity, nothing is published, and the next selection walks
    /// the module again, publishes, and keeps the value.
    /// </summary>
    [Fact]
    public async Task ACancelledAttempt_LeavesNothing_AndTheNextSelectionPublishes()
    {
        var program = Wide(Layout.BranchOpens, 12, branches: 2);
        var host = new RunHost(program.Library);
        var root = await ParseDeferred(program, host);
        var region = RegionAt(root, "G0");
        var store = StoreOf(region);

        for (var selection = 1; selection <= 3; selection++)
        {
            using var cancellation = new CancellationTokenSource();
            var observations = new FrontEndTraversalObservations
            {
                StageObserver = (name, begin) =>
                {
                    if (name == "deferred-freeze" && begin)
                        cancellation.Cancel();
                },
            };
            region.Loader.TraversalObservations = observations;
            var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await region.MaterializeAsync(cancellation.Token));
            Assert.Equal(cancellation.Token, error.CancellationToken);
            Assert.True(observations.DeferredCompositionGateEdges > 12, "the cancelled attempt never walked the module");
            Assert.Equal(0, observations.CompletedModuleViewReuses);
            Assert.Equal(0, store.Count);
            Assert.False(region.IsMaterialized);
            Assert.Equal(selection, region.MaterializationAttempts);
        }

        region.Loader.TraversalObservations = null;
        var body = await region.MaterializeAsync(CancellationToken.None);
        Assert.True(body.IsOk, body.IsOk ? "" : body.Error.ToString());
        Assert.Equal(1, store.Count);
        var flat = await RunFlat(root);
        Assert.False(flat.IsError, flat.IsError ? flat.Error.ToString() : "");
        Assert.Equal([(Decimal128)2, 3], flat.Value);
    }

    /// <summary>
    /// CONCURRENT SELECTIONS. Eight runs of one parsed tree start together, in the verifying mode: the loader's gate
    /// serializes the materializations, each region is materialized once, every run returns the sequential values, and
    /// the store holds what one sequential run publishes.
    /// </summary>
    [Fact]
    public async Task ConcurrentRunsOfOneTree_PublishWhatASequentialRunPublishes()
    {
        const int branches = 6;
        var program = Wide(Layout.RootAndBranchOpen, 40, branches);
        var expected = Enumerable.Range(0, branches).Select(static index => (Decimal128)(2 + index)).ToArray();

        var sequentialRoot = await ParseDeferred(program, new RunHost(program.Library));
        var sequential = await In(CompletedModuleViews.Mode.Verified, () => RunFlat(sequentialRoot));
        Assert.Equal(expected, sequential.Value);
        var sequentialCount = StoreOf(RegionAt(sequentialRoot, "G0")).Count;
        Assert.Equal(1, sequentialCount);

        var host = new RunHost(program.Library);
        var root = await ParseDeferred(program, host);
        var runs = await In(CompletedModuleViews.Mode.Verified, async () =>
        {
            using var start = new ManualResetEventSlim();
            var tasks = Enumerable.Range(0, 8).Select(_ => Task.Run(async () =>
            {
                start.Wait();
                return await RunFlat(root);
            })).ToArray();
            start.Set();
            return await Task.WhenAll(tasks);
        });

        Assert.All(runs, run =>
        {
            Assert.False(run.IsError, run.IsError ? run.Error.ToString() : "");
            Assert.Equal(expected, run.Value);
        });
        for (var index = 0; index < branches; index++)
        {
            var region = RegionAt(root, $"G{index}");
            Assert.True(region.IsMaterialized);
            Assert.Equal(1, region.MaterializationAttempts);
        }

        Assert.Equal(sequentialCount, StoreOf(RegionAt(root, "G0")).Count);
        Assert.All(host.Fetches.Values, static count => Assert.Equal(1, count));
    }

    /// <summary>
    /// ONE STORE PER PARSE. A store belongs to one loader, which belongs to one parse of one document: nothing is static,
    /// so a second parse of the same source starts cold whatever the first one published, and does the same work.
    /// </summary>
    [Fact]
    public async Task ASecondParse_ReadsNothingOfTheFirst()
    {
        var program = Wide(Layout.BranchOpens, 30, 3);
        var first = await MaterializeAll(program, CompletedModuleViews.Mode.Shared);
        // The same URLs and graph shape, with fresh content in the second parse.
        var replacement = new Dictionary<string, string>
        {
            ["lib"] = program.Library["lib"].Replace("x * 2", "x * 7", StringComparison.Ordinal),
        };
        var second = await MaterializeAll(program with { Library = replacement }, CompletedModuleViews.Mode.Shared);

        Assert.NotSame(StoreOf(first.Regions[0]), StoreOf(second.Regions[0]));
        Assert.Equal(1, StoreOf(first.Regions[0]).Count);
        for (var index = 0; index < program.Families.Length; index++)
            Assert.True(first.Work[index].SequenceEqual(second.Work[index]),
                $"selection {index}:\n  {Render(first.Work[index])}\n  {Render(second.Work[index])}");
        Assert.Equal(0, second.Work[0]["CompletedModuleViewReuses"]);
        Assert.Equal([(Decimal128)2, 3, 4], (await RunFlat(first.Root)).Value);
        Assert.Equal([(Decimal128)7, 8, 9], (await RunFlat(second.Root)).Value);
    }

    /// <summary>
    /// TWO URLS, TWO VIEWS. Two canonical URLs serving byte-identical text are two modules (Q-31/Q-32): two downloads, two
    /// views, two sets of facts, and a later branch reuses both.
    /// </summary>
    [Fact]
    public async Task DistinctUrlsWithTheSameText_KeepDistinctFacts()
    {
        var host = new RunHost(SameTextTwoUrls.Library);
        var root = await ParseDeferred(SameTextTwoUrls, host);
        var first = await RegionAt(root, "G0").MaterializeAsync(CancellationToken.None);
        Assert.True(first.IsOk, first.IsOk ? "" : first.Error.ToString());
        var loader = RegionAt(root, "G0").Loader;
        var lib = loader.CachedViewOf(Url("lib"))!;
        var copy = loader.CachedViewOf(Url("copy"))!;
        Assert.NotSame(lib, copy);
        Assert.True(StoreOf(RegionAt(root, "G0")).HasPublished(lib));
        Assert.True(StoreOf(RegionAt(root, "G0")).HasPublished(copy));
        Assert.Equal(2, StoreOf(RegionAt(root, "G0")).Count);

        var warm = new FrontEndTraversalObservations();
        loader.TraversalObservations = warm;
        var second = await RegionAt(root, "G1").MaterializeAsync(CancellationToken.None);
        Assert.True(second.IsOk, second.IsOk ? "" : second.Error.ToString());
        // Two views, three stages each.
        Assert.Equal(6, warm.CompletedModuleViewReuses);
        Assert.Equal(2, warm.CompletedModuleAnalysesSkipped);
        Assert.Equal(2, host.TotalFetches);
    }

    // ── Malformed modules and low limits ────────────────────────────────────

    [Fact]
    public async Task LoadCheckSkipsOnlyThePublishedView_AndPositionsAnUnresolvedLoad()
    {
        var program = Wide(Layout.BranchOpens, 4, branches: 2);
        var root = await ParseDeferred(program, new RunHost(program.Library));
        var region = RegionAt(root, "G0");
        Assert.True((await region.MaterializeAsync(CancellationToken.None)).IsOk);
        var view = Assert.IsType<Algorithm.User>(region.Loader.CachedViewOf(Url("lib")));

        // Model a loader omission beside a successful splice. This copy has the original declaration
        // identity, but a different open list. The first directive already has its refusal.
        var raw = Parser.ParseSyntax($"open '{Url("refused")}', '{Url("unresolved")}'");
        Assert.False(raw.HasErrors);
        var opens = raw.SyntaxRoot.Opens;
        var changed = view with { Opens = opens };
        var body = raw.SyntaxRoot with { Opens = [new Expr.AlgorithmExpr(view), new Expr.AlgorithmExpr(changed)] };
        var refused = new HashSet<Expr>(ReferenceEqualityComparer.Instance) { opens[0] };
        var observations = new FrontEndTraversalObservations();
        var attempt = region.Loader.ModuleUnits.BeginOperation().BeginCompletedViews(observations)!;

        Assert.True(LoadElaborationGuard.TryFindFirstUnresolvedLoad(body, refused, out var ordinary));
        Assert.NotNull(ordinary);
        Assert.Equal(opens[1].Span, ordinary);
        Assert.True(LoadElaborationGuard.TryFindFirstUnresolvedLoad(body, refused, attempt, out var shared));
        Assert.Equal(ordinary, shared);
        Assert.Equal(1, observations.CompletedModuleViewReuses);
    }

    /// <summary>
    /// A MALFORMED MODULE. A branch whose module does not parse is refused with the established load-site diagnostic at
    /// every selection, before and after another branch published a completed module both splice, in every mode; it
    /// publishes nothing, and the completed module's facts stay the only ones.
    /// </summary>
    [Fact]
    public async Task AMalformedModule_IsRefusedAsBefore_AndLeavesNothing()
    {
        var library = new Dictionary<string, string>(StringComparer.Ordinal) { ["lib"] = MemberLines(20), ["bad"] = "public B(x) = x +\n" };
        var program = new Program("malformed",
            $"Good(0) = 0\nGood(n) = {{\n    open '{Url("lib")}'\n    F1(n)\n}}\n"
            + $"Bad(0) = 0\nBad(n) = {{\n    open '{Url("lib")}', '{Url("bad")}'\n    F2(n) + B(n)\n}}\n"
            + "Good(1)\nBad(1)\n",
            library, ["Good", "Bad"]);

        async Task<(DiagnosticCode, string, SourceSpan?)[][]> Selections(CompletedModuleViews.Mode mode, bool goodFirst)
        {
            var root = await ParseDeferred(program, new RunHost(library));
            return await In(mode, async () =>
            {
                var refusals = new List<(DiagnosticCode, string, SourceSpan?)[]>();
                if (goodFirst)
                    Assert.True((await RegionAt(root, "Good").MaterializeAsync(CancellationToken.None)).IsOk);
                for (var selection = 0; selection < 2; selection++)
                    refusals.Add(Diagnostics(await RegionAt(root, "Bad").MaterializeAsync(CancellationToken.None)));
                Assert.Equal(goodFirst && mode != CompletedModuleViews.Mode.Unshared ? 1 : 0, StoreOf(RegionAt(root, "Bad")).Count);
                return refusals.ToArray();
            });
        }

        var reference = await Selections(CompletedModuleViews.Mode.Unshared, goodFirst: false);
        Assert.Equal(DiagnosticCode.InvalidLoadedSource, Assert.Single(reference[0]).Item1);
        foreach (var mode in Enum.GetValues<CompletedModuleViews.Mode>())
        {
            foreach (var goodFirst in new[] { false, true })
            {
                var selections = await Selections(mode, goodFirst);
                Assert.All(selections, refusal => Assert.Equal(reference[0], refusal));
            }
        }
    }

    /// <summary>
    /// A LOW AGGREGATE. Every splice still charges the module's weight: under an aggregate that fits the document, the
    /// module's download and one further splice, the third selection's splice is refused with the established
    /// <see cref="DiagnosticCode.AggregateSourceLengthExceeded"/> at its load site, in every mode, after the store
    /// published the module's facts; the refused attempt publishes nothing.
    /// </summary>
    [Fact]
    public async Task ALowAggregate_RefusesTheSameSplice_InEveryMode()
    {
        var program = Wide(Layout.BranchOpens, 20, branches: 3);
        var module = program.Library["lib"];
        var limits = new SourceProcessingLimits { MaxAggregateSourceLength = program.Source.Length + 2L * module.Length };

        async Task<string[]> Selections(CompletedModuleViews.Mode mode)
        {
            var host = new RunHost(program.Library, limits);
            var root = await ParseDeferred(program, host);
            return await In(mode, async () =>
            {
                var outcomes = new List<string>();
                foreach (var family in program.Families)
                {
                    var body = await RegionAt(root, family).MaterializeAsync(CancellationToken.None);
                    outcomes.Add(body.IsOk ? "ok" : DescribeError(body.Error));
                }

                Assert.Equal(mode == CompletedModuleViews.Mode.Unshared ? 0 : 1, StoreOf(RegionAt(root, "G0")).Count);
                return outcomes.ToArray();
            });
        }

        var reference = await Selections(CompletedModuleViews.Mode.Unshared);
        Assert.Equal(["ok", "ok"], reference[..2]);
        Assert.Contains(nameof(DiagnosticCode.AggregateSourceLengthExceeded), reference[2], StringComparison.Ordinal);
        Assert.Equal(reference, await Selections(CompletedModuleViews.Mode.Shared));
        Assert.Equal(reference, await Selections(CompletedModuleViews.Mode.Verified));
    }

    /// <summary>
    /// A LOW STATIC-STRUCTURE ENVELOPE. The admission measure of a loaded body that splices a completed module (counted as
    /// its published unit) and a leaf module shared by two parents and spliced directly gives, for every
    /// envelope from far below to above what the body needs, exactly the ordinary walk's answer: the same measurement and
    /// limits where it admits, and the same refusal — the same sentence, so the same bound — where it refuses, cold (no
    /// facts published) and warm. An end-to-end program cannot isolate the measure: an envelope low enough for it is low
    /// enough for the parse's own entry bound, one entry per KiB.
    /// </summary>
    [Fact]
    public async Task ALowStaticEnvelope_IsMeasuredAndRefusedAsTheOrdinaryWalk_ColdOrWarm()
    {
        var library = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["outer"] = $"open '{Url("tiny2")}'\n" + MemberLines(30),
            ["tiny2"] = Tiny2,
            ["sibling"] = $"open '{Url("tiny2")}'\npublic S(n) = Q(n) + 2\n",
        };
        var program = Make("envelope", "",
            Families(_ => $"    open '{Url("outer")}', '{Url("sibling")}', '{Url("tiny2")}'\n    K = [1, 2, 3, n]\n",
                index => $"F{index}(n) + Z + S(n) + K[0]", branches: 2),
            library);
        var root = await ParseDeferred(program, new RunHost(library));
        var first = await RegionAt(root, "G0").MaterializeAsync(CancellationToken.None);
        Assert.True(first.IsOk, first.IsOk ? "" : first.Error.ToString());
        var region = RegionAt(root, "G1");
        var loader = region.Loader;
        Assert.Equal(3, StoreOf(region).Count);
        var loaded = await loader.LoadDeferredRegionAsync(region, loader.CreateDiagnosticBag(), loader.CreateMaterializationLedger(),
            moduleViews: null, CancellationToken.None);
        var prelude = region.Structure!.Registry.StructuralContinuation!.Prelude;
        var needed = StaticStructureAdmission.Measure(loaded, prelude);
        Assert.True(needed.Nodes > 300, $"{needed.Nodes} nodes");

        static string Outcome(Func<StaticStructureAdmission.Measurement> measure)
        {
            try
            {
                return measure().ToString();
            }
            catch (StaticQueryLimitExceededException error)
            {
                return "refused: " + StaticStructureAdmission.Rejection(error).Message;
            }
        }

        var envelopes = new List<long> { 1, 32, 1024 };
        foreach (var factor in new long[] { 8, 32 })
        {
            foreach (var count in new[] { needed.Nodes, needed.Edges })
            {
                for (var delta = -2; delta <= 2; delta++)
                    envelopes.Add(factor * count + delta);
            }
        }

        envelopes.Add(64 * 1024 * 1024);
        var refusals = 0;
        foreach (var envelope in envelopes.Where(static envelope => envelope > 0).Distinct())
        {
            var limits = new SourceProcessingLimits { MaxStaticStructureBytes = envelope };
            var reference = Outcome(() => StaticStructureAdmission.Measure(loaded, prelude, limits));
            refusals += reference.StartsWith("refused", StringComparison.Ordinal) ? 1 : 0;
            // Warm: the units published by the first selection.
            Assert.Equal(reference, Outcome(() => StaticStructureAdmission.MeasureLoadedBody(loaded, prelude, limits,
                loader.ModuleUnits.BeginOperation().BeginCompletedViews(null))));
            // Cold: a fresh store computes every unit from its view.
            Assert.Equal(reference, Outcome(() => StaticStructureAdmission.MeasureLoadedBody(loaded, prelude, limits,
                new ModuleUnitRegistry().CompletedViews.BeginAttempt(new ModuleUnitRegistry(), null))));
        }

        Assert.True(refusals >= 3, $"{refusals} refused envelopes");
    }

    /// <summary>
    /// A COMPOSED BODY DEEPER THAN THE ELABORATION CEILING. One module of a deep member is spliced by a shallow branch,
    /// which fits and publishes the view's facts, and by a branch nested deeper, which does not fit: the gate takes the
    /// view's published height at the raw-syntax cap, the measured height exceeds the elaboration ceiling, and the ordinary
    /// gate replayed at that ceiling reports exactly the reference's <see cref="DiagnosticCode.AstDepthLimitExceeded"/>,
    /// with its span, cold or warm, in every mode.
    /// </summary>
    [Fact]
    public async Task AComposedBodyDeeperThanTheCeiling_IsRefusedAsBefore_ColdOrWarm()
    {
        // An operator chain parses iteratively (no nesting charge per link), so the module parses at any load site, and
        // its member is about 240 levels deep under the fully recursive profile.
        var library = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["deep"] = $"public D(x) = x{string.Concat(Enumerable.Repeat(" + 1", 240))}\n",
        };
        const int nesting = 60;
        var nested = new StringBuilder();
        for (var level = 0; level < nesting; level++)
            nested.Append($"N{level} = {{\n");
        nested.Append($"Deep(0) = 0\nDeep(n) = {{\n    open '{Url("deep")}'\n    D(n) + 1\n}}\nDeep(1)\n");
        for (var level = nesting - 1; level >= 0; level--)
            nested.Append("}\n").Append(level > 0 ? $"N{level}\n" : "");

        var program = new Program("deep",
            $"Shallow(0) = 0\nShallow(n) = {{\n    open '{Url("deep")}'\n    D(n)\n}}\n" + nested + "Shallow(1)\nN0\n",
            library, ["Shallow", string.Join('/', Enumerable.Range(0, nesting).Select(static level => $"N{level}")) + "/Deep"]);

        async Task<string[]> Selections(CompletedModuleViews.Mode mode, bool shallowFirst)
        {
            var root = await ParseDeferred(program, new RunHost(library));
            return await In(mode, async () =>
            {
                var outcomes = new List<string>();
                foreach (var family in shallowFirst ? program.Families : [program.Families[1], program.Families[1], program.Families[0]])
                {
                    var body = await RegionAt(root, family.Split('/')).MaterializeAsync(CancellationToken.None);
                    outcomes.Add(body.IsOk ? "ok" : DescribeError(body.Error));
                }

                return outcomes.ToArray();
            });
        }

        foreach (var shallowFirst in new[] { true, false })
        {
            var reference = await Selections(CompletedModuleViews.Mode.Unshared, shallowFirst);
            Assert.Equal("ok", shallowFirst ? reference[0] : reference[2]);
            Assert.Contains(nameof(DiagnosticCode.AstDepthLimitExceeded), shallowFirst ? reference[1] : reference[0], StringComparison.Ordinal);
            Assert.Equal(reference, await Selections(CompletedModuleViews.Mode.Shared, shallowFirst));
            Assert.Equal(reference, await Selections(CompletedModuleViews.Mode.Verified, shallowFirst));
        }
    }
}
