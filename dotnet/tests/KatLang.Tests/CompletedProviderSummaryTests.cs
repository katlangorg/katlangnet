using System.Numerics;
using System.Reflection;
using System.Text;
using SummarySeed = KatLang.PropertyDependencyGraphBuilder.SummarySeed;

namespace KatLang.Tests;

/// <summary>
/// COMPLETED PROVIDER SUMMARIES (November 2026; C#-only work sharing, no value, diagnostic or classification changes,
/// Lean unchanged; <see cref="CompletedProviderSummaries"/>). A load-bearing clause branch is elaborated when it is
/// selected, as a front-end operation of its own. When its body reads ONE member of a body an earlier operation
/// completed (a module an enclosing scope opens, a member path through a property that holds a module or an inline
/// block), exposure charges that member's summary seed, which is one entry of the provider's WHOLE summary. Every
/// materialization used to compute that summary again: K selected branches over one W-member provider cost O(K × W),
/// in a shape no source-processing limit bounds (each branch splices only its own small module) and that evaluation
/// steps do not count (measured before the share: 2.36 GB and 5.8 s for 92 KB of source, against 113 MB for the same
/// program with nothing deferred).
///
/// <para>A materialization that publishes its unit now publishes the summaries of completed content it computed, and
/// a later one adopts them, re-anchored at its own contexts seed by seed. These tests pin, with a fixed in-memory
/// downloader:</para>
/// <list type="bullet">
///   <item>THE WORK BOUND: from the third selection on, EVERY traversal counter of a materialization is the same for
///   a provider of 24 members and one of 240, in four layouts and with members that do and do not read their
///   siblings; the first selection (cold) and every selection without the share (the reference mode) grow with the
///   width; a branch that reads no provider member never paid for it; a module a branch holds in a property of its own
///   (alone, beside a root property, twice, through an inline open block) is kept by the first selection that reads it
///   as an earlier operation's completed content and adopted from the next one on, one entry per exact view;</item>
///   <item>EQUALITY: over a corpus of programs, the run values and the exposure metadata of every materialized body
///   are the same with the share, without it, and in the verifying mode, which computes every adopted summary again
///   and compares it seed by seed (names, references in order, the facts object and key of every origin);</item>
///   <item>ISOLATION: an attempt that publishes nothing (refused, cancelled; one that holds a completed module
///   included) leaves nothing in the share and its diagnostics are the same before and after other branches published;
///   a provider that holds a placeholder is never kept; concurrent selections publish what a sequential run publishes;
///   one parse never reads another's;</item>
///   <item>OWNER DECISION PENDING (<c>docs/design/completed-module-output-seed-owner-decision-brief-2026-11.md</c>): a
///   wide member-read layouts with output rows or opens traverse both module views on each later selection, a
///   unit keeps nothing it completed itself, and fourteen witnesses of that output seed are the same with and without
///   the share.</item>
/// </list>
/// <para>Host conventions are those of <see cref="DeferredAttemptCacheRetentionTests"/>: an in-memory downloader that
/// counts its calls, <c>AllowedHosts = ["modules.example"]</c>, a clean parse that downloads nothing, and regions
/// materialized through the real <see cref="DeferredModuleRegion.MaterializeAsync"/> or a run of the parsed tree.</para>
/// </summary>
public class CompletedProviderSummaryTests
{
    private const string Host = "modules.example";

    private static string Url(string name) => $"https://{Host}/{name}.kat";

    private const string Tiny = "public V = 1\npublic W(x) = x * 2\n";

    private const string Tiny2 = "public Z = 4\npublic Q(x) = x - 1\n";

    [Fact]
    public void ReanchoringSharedParts_VisitsEachEdgeBoundedly_WhenStagingAndAdopting()
    {
        var origin = SourceProvenance.ParseValid("1").Root.CompletedStructure!.Facts;
        var at = origin.Context(origin.PreludeKey);
        var names = Enumerable.Range(0, SummarySeed.CopiedCompletedEntries + 1).Select(i => $"N{i}").ToArray();
        var reference = new PendingReference("M", ["F"], at);
        var left = new SummarySeed(visiblePropertyDependencyNames: names, pendingReferences: [reference]);
        var unchanged = new SummarySeed(visiblePropertyDependencyNames: names);
        var right = unchanged;
        // Two parents share the previous pair of completed parts at each level.
        const int levels = 8;
        for (var level = 0; level < levels; level++)
        {
            SummarySeed Parent() => new SummarySeed(visiblePropertyDependencyNames: names).AbsorbCompleted(left).AbsorbCompleted(right);
            (left, right) = (Parent(), Parent());
        }
        var root = new SummarySeed().AbsorbCompleted(left).AbsorbCompleted(right);
        var nodes = 2 * levels + 3;
        var counted = new CountingSeedComparer();
        var staged = new Dictionary<SummarySeed, SummarySeed>(counted);
        var stored = root.Reanchored(Reanchor, staged, null, CancellationToken.None);
        Assert.Equal(nodes, staged.Count);
        Assert.Same(unchanged, staged[unchanged]);
        Assert.InRange(counted.Probes, 1, 20 * nodes);

        var anchored = staged.Where(pair => !ReferenceEquals(pair.Key, pair.Value))
            .Select(pair => pair.Value).ToHashSet();
        counted = new CountingSeedComparer();
        var adopted = new Dictionary<SummarySeed, SummarySeed>(counted);
        var result = stored.Reanchored(Reanchor, adopted, anchored, CancellationToken.None);
        Assert.Equal(nodes - 1, adopted.Count);
        Assert.InRange(counted.Probes, 1, 20 * nodes);
        Assert.NotSame(reference, Assert.Single(result.Clone().PendingReferences));
        Assert.Same(reference, Assert.Single(root.Clone().PendingReferences));
        Assert.Equal(names.Length, result.Clone().VisiblePropertyDependencyNames.Count);

        static PendingReference Reanchor(PendingReference item) => new(item.Head, item.Members, item.Origin);
    }

    private sealed class CountingSeedComparer : IEqualityComparer<SummarySeed>
    {
        public int Probes { get; private set; }
        public bool Equals(SummarySeed? x, SummarySeed? y) => ReferenceEquals(x, y);
        public int GetHashCode(SummarySeed seed)
        {
            Probes++;
            return ReferenceEqualityComparer.Instance.GetHashCode(seed);
        }
    }

    /// <summary>The in-memory host of one run over one library: download counts per module.</summary>
    private sealed class RunHost(IReadOnlyDictionary<string, string> library)
    {
        public Dictionary<string, int> Fetches { get; } = new(StringComparer.Ordinal);

        public int TotalFetches => Fetches.Values.Sum();

        public RunOptions Options => new()
        {
            AllowedHosts = [Host],
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

    public sealed record Program(string Name, string Source, IReadOnlyDictionary<string, string> Library)
    {
        public bool RequiresAdoption { get; init; } = true;
        public override string ToString() => Name;
    }

    private static async Task<Algorithm.User> ParseDeferred(Program program, RunHost host, FrontEndTraversalObservations? stage = null)
    {
        foreach (var module in program.Library.Values)
            SourceProvenance.ParseSyntaxValidRoot(module);
        Algorithm.User root;
        if (stage is null)
        {
            var parsed = await SourceProvenance.ParseValidAsync(program.Source, host.Options);
            Assert.Empty(parsed.Diagnostics);
            root = parsed.Root;
        }
        else
        {
            var compiled = await FrontEndPipeline.ProcessAsync(program.Source, host.Options, comparisonObservations: null, stage);
            Assert.Empty(compiled.Diagnostics);
            root = Assert.IsType<Algorithm.User>(compiled.ElaboratedRoot);
        }

        Assert.True(DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.AlgorithmExpr(root)), "the program holds no deferred region");
        // The parse downloads what the root loads itself, once; a branch's own module only when the branch is selected.
        Assert.All(host.Fetches, static fetch => Assert.Equal(1, fetch.Value));
        Assert.DoesNotContain(Url("tiny"), host.Fetches.Keys);
        return root;
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

    private static CompletedProviderSummaries ShareOf(DeferredModuleRegion region) => region.Loader.ModuleUnits.CompletedProviders;

    /// <summary>Runs <paramref name="run"/> with every materialization it starts in <paramref name="mode"/>.</summary>
    private static async Task<T> In<T>(CompletedProviderSummaries.Mode mode, Func<Task<T>> run)
    {
        var saved = CompletedProviderSummaries.ModeForTesting.Value;
        CompletedProviderSummaries.ModeForTesting.Value = mode;
        try
        {
            return await run();
        }
        finally
        {
            CompletedProviderSummaries.ModeForTesting.Value = saved;
        }
    }

    // ── The wide programs ───────────────────────────────────────────────────

    public enum Layout
    {
        /// <summary>The root opens the provider module; a branch reads a member by name.</summary>
        OpenedModule,

        /// <summary>A root property holds the provider module; a branch reads a member path.</summary>
        ModuleProperty,

        /// <summary>The provider is an inline block of the root; a branch reads a member path.</summary>
        BlockPath,

        /// <summary>The root opens its inline provider block; a branch reads a member by name.</summary>
        OpenedBlock,
    }

    public enum Members
    {
        /// <summary><c>public F7(x) = x + 7</c>: no member reads another.</summary>
        Plain,

        /// <summary><c>public F7(x) = Helper(x) + 7</c>: every member reads a private sibling.</summary>
        Helper,
    }

    private static string MemberLines(Members members, int width, string indent)
    {
        var text = new StringBuilder();
        if (members == Members.Helper)
            text.Append(indent).Append("Helper(x) = x * 2\n");
        for (var index = 0; index < width; index++)
            text.Append(indent).Append(members == Members.Helper
                ? $"public F{index}(x) = Helper(x) + {index}\n"
                : $"public F{index}(x) = x + {index}\n");
        return text.ToString();
    }

    /// <summary>
    /// <paramref name="branches"/> clause families <c>G0 … </c>, each with one load-bearing branch that opens the tiny
    /// module and, when <paramref name="reads"/>, reads member <c>F&lt;i&gt;</c> of a <paramref name="width"/>-member
    /// provider; every family is selected once by a root row.
    /// </summary>
    private static Program Wide(Layout layout, Members members, int width, int branches, bool reads = true)
    {
        var library = new Dictionary<string, string>(StringComparer.Ordinal) { ["tiny"] = Tiny };
        var source = new StringBuilder();
        switch (layout)
        {
            case Layout.OpenedModule:
                library["lib"] = MemberLines(members, width, "");
                source.Append($"open '{Url("lib")}'\n");
                break;
            case Layout.ModuleProperty:
                library["lib"] = MemberLines(members, width, "");
                source.Append($"Lib = load('{Url("lib")}')\n");
                break;
            case Layout.BlockPath:
                source.Append("Lib = {\n").Append(MemberLines(members, width, "    ")).Append("}\n");
                break;
            case Layout.OpenedBlock:
                source.Append("open Lib\nLib = {\n").Append(MemberLines(members, width, "    ")).Append("}\n");
                break;
        }

        var byName = layout is Layout.OpenedModule or Layout.OpenedBlock;
        for (var index = 0; index < branches; index++)
        {
            var read = !reads ? "n" : byName ? $"F{index}(n)" : $"Lib.F{index}(n)";
            source.Append($"G{index}(0) = 0\nG{index}(n) = {{\n    open '{Url("tiny")}'\n    V + W(n) + {read}\n}}\n");
        }

        for (var index = 0; index < branches; index++)
            source.Append($"G{index}(1)\n");
        return new($"{layout}/{members}/{width}", source.ToString(), library);
    }

    /// <summary>What row <c>G&lt;i&gt;(1)</c> of <see cref="Wide"/> evaluates to: <c>V + W(1) + F&lt;i&gt;(1)</c>, or <c>V + W(1) + 1</c>.</summary>
    private static Decimal128 WideValue(Members members, int index, bool reads = true)
        => 1 + 2 + (!reads ? 1 : members == Members.Helper ? 2 + index : 1 + index);

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

    /// <summary>
    /// Materializes every family's region in order through the real <see cref="DeferredModuleRegion.MaterializeAsync"/>,
    /// each with a fresh observer on its loader: the counters of that one materialization. Also returns the bytes each
    /// materialization allocated on the calling thread (a synchronously completing downloader runs it inline).
    /// </summary>
    private static async Task<(SortedDictionary<string, long>[] Work, long[] Allocated, DeferredModuleRegion[] Regions)> MaterializeAll(
        Program program, int branches, CompletedProviderSummaries.Mode mode)
    {
        var host = new RunHost(program.Library);
        var root = await ParseDeferred(program, host);
        var work = new SortedDictionary<string, long>[branches];
        var allocated = new long[branches];
        var regions = new DeferredModuleRegion[branches];
        await In(mode, async () =>
        {
            for (var index = 0; index < branches; index++)
            {
                var region = regions[index] = RegionAt(root, $"G{index}");
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
        return (work, allocated, regions);
    }

    public static TheoryData<Layout, Members> Shapes()
    {
        var shapes = new TheoryData<Layout, Members>();
        foreach (var layout in Enum.GetValues<Layout>())
        {
            foreach (var members in Enum.GetValues<Members>())
                shapes.Add(layout, members);
        }

        return shapes;
    }

    // ── The work bound ──────────────────────────────────────────────────────

    /// <summary>
    /// THE BOUND. Five branches read five members of one provider. From the third selection on, every traversal counter
    /// of the materialization is identical for a provider of 24 members and one of 240: the provider's summary is
    /// adopted, nothing below it is walked, and nothing is kept again. The FIRST selection is the cold control (it
    /// computes every member's summary once for the program), and the reference mode without the share is the control
    /// for the defect: there every selection evaluates every member again.
    /// </summary>
    [Theory]
    [MemberData(nameof(Shapes))]
    public async Task LaterSelections_DoNoWorkInTheWidthOfACompletedProvider(Layout layout, Members members)
    {
        const int branches = 5;
        const int narrowWidth = 24;
        const int wideWidth = 240;
        var narrow = await MaterializeAll(Wide(layout, members, narrowWidth, branches), branches, CompletedProviderSummaries.Mode.Shared);
        var wide = await MaterializeAll(Wide(layout, members, wideWidth, branches), branches, CompletedProviderSummaries.Mode.Shared);

        // Cold: the first selection summarizes the provider, member by member.
        Assert.True(wide.Work[0]["SummaryMemberEvaluations"] >= wideWidth, Render(wide.Work[0]));
        Assert.True(wide.Work[0]["SummaryMemberEvaluations"] - narrow.Work[0]["SummaryMemberEvaluations"] >= wideWidth - narrowWidth,
            $"{Render(narrow.Work[0])}\n{Render(wide.Work[0])}");
        Assert.True(wide.Work[0]["CompletedProviderSummariesKept"] > 0, Render(wide.Work[0]));
        Assert.Equal(0, wide.Work[0]["CompletedProviderSummaryAdoptions"]);

        // Warm: the width of the provider is no input of a later selection's work.
        for (var index = 2; index < branches; index++)
        {
            Assert.True(narrow.Work[index].SequenceEqual(wide.Work[index]),
                $"selection {index}:\n  {narrowWidth}: {Render(narrow.Work[index])}\n  {wideWidth}: {Render(wide.Work[index])}");
            Assert.True(wide.Work[index]["CompletedProviderSummaryAdoptions"] > 0, Render(wide.Work[index]));
            Assert.Equal(0, wide.Work[index]["CompletedProviderSummariesKept"]);
            Assert.True(wide.Work[index]["SummaryMemberEvaluations"] < narrowWidth, Render(wide.Work[index]));
        }

        // What was kept is bounded by the provider contexts the branches asked for, not by the selections.
        var share = ShareOf(wide.Regions[0]);
        Assert.InRange(share.Count, 1, 4);
        Assert.Equal(ShareOf(narrow.Regions[0]).Count, share.Count);

        // The reference: without the share every selection pays the provider's width, as every one did before it.
        var unshared = await MaterializeAll(Wide(layout, members, wideWidth, branches), branches, CompletedProviderSummaries.Mode.Unshared);
        for (var index = 0; index < branches; index++)
        {
            Assert.True(unshared.Work[index]["SummaryMemberEvaluations"] >= wideWidth, $"selection {index}: {Render(unshared.Work[index])}");
            Assert.Equal(0, unshared.Work[index]["CompletedProviderSummaryAdoptions"]);
            Assert.Equal(0, unshared.Work[index]["CompletedProviderSummariesKept"]);
        }

        Assert.Equal(0, ShareOf(unshared.Regions[0]).Count);
    }

    /// <summary>
    /// The trigger is a member READ. A branch that names no member of the provider computed no summary of it before the
    /// share and computes, keeps and adopts none now, whatever the provider's width.
    /// </summary>
    [Theory]
    [InlineData(Layout.OpenedModule)]
    [InlineData(Layout.BlockPath)]
    public async Task ABranchThatReadsNoMember_NeverPaysForTheProvider(Layout layout)
    {
        const int branches = 3;
        foreach (var mode in new[] { CompletedProviderSummaries.Mode.Shared, CompletedProviderSummaries.Mode.Unshared })
        {
            var narrow = await MaterializeAll(Wide(layout, Members.Helper, 24, branches, reads: false), branches, mode);
            var wide = await MaterializeAll(Wide(layout, Members.Helper, 240, branches, reads: false), branches, mode);
            for (var index = 1; index < branches; index++)
            {
                Assert.True(narrow.Work[index].SequenceEqual(wide.Work[index]),
                    $"{mode}, selection {index}:\n  {Render(narrow.Work[index])}\n  {Render(wide.Work[index])}");
                Assert.Equal(0, wide.Work[index]["CompletedProviderSummaryAdoptions"]);
                Assert.True(wide.Work[index]["SummaryMemberEvaluations"] < 24, Render(wide.Work[index]));
            }

            Assert.Equal(0, ShareOf(wide.Regions[0]).Count);
        }
    }

    /// <summary>
    /// A coarse allocation bound over the same programs (in-process: a selection allocates hundreds of kilobytes, far
    /// above the ~8 KB counter quantum; the minimum over the later selections damps a collection in the window).
    /// Quadrupling the provider's width used to multiply a later selection's allocation by about 3.4 (2.9 MB to 10.1 MB
    /// at 1,000 and 4,000 members); with the share it grows by the levels a lookup still builds over the provider. The
    /// unshared reference keeps the old growth.
    /// <para>The bound is on that GROWTH PER MEMBER, at most 160 bytes, the allowance the former bound
    /// <c>wide &lt; 1.6 × narrow</c> gave when it was introduced (7549d7d5). In the Debug test build the growth is 140
    /// bytes per member at 7549d7d5, at 7de84650 and with the November 25 2026 exposure candidate alike (125.6 / 126.1 /
    /// 125.9 KB from 300 to 1,200 members), but the ratio rose from 1.53 to 1.59, because later allocation work took 24 KB
    /// off the part of a selection that does not depend on the width: the ratio's room shrank whenever anything else
    /// improved, and a 1,200-member sample of 341,408 bytes against 213,160 crossed it on an unchanged growth.</para>
    /// </summary>
    [Fact]
    public async Task LaterSelections_AllocateAlmostNothingInTheWidthOfACompletedProvider()
    {
        const int branches = 6;
        // Warm-up: the first run of each mode pays type loading and JIT for its paths.
        await MaterializeAll(Wide(Layout.OpenedModule, Members.Helper, 50, branches), branches, CompletedProviderSummaries.Mode.Shared);
        await MaterializeAll(Wide(Layout.OpenedModule, Members.Helper, 50, branches), branches, CompletedProviderSummaries.Mode.Unshared);

        async Task<long> LaterSelection(int width, CompletedProviderSummaries.Mode mode)
            => (await MaterializeAll(Wide(Layout.OpenedModule, Members.Helper, width, branches), branches, mode)).Allocated[2..].Min();

        var narrow = await LaterSelection(300, CompletedProviderSummaries.Mode.Shared);
        var wide = await LaterSelection(1200, CompletedProviderSummaries.Mode.Shared);
        var narrowUnshared = await LaterSelection(300, CompletedProviderSummaries.Mode.Unshared);
        var wideUnshared = await LaterSelection(1200, CompletedProviderSummaries.Mode.Unshared);

        Assert.True(wide - narrow < 160L * (1200 - 300),
            $"with the share a later selection allocated {narrow} bytes at 300 members and {wide} at 1,200");
        Assert.True(wideUnshared > narrowUnshared * 2.5,
            $"without the share a later selection allocated {narrowUnshared} bytes at 300 members and {wideUnshared} at 1,200");
        Assert.True(wideUnshared > wide * 10, $"at 1,200 members a later selection allocated {wide} bytes with the share and {wideUnshared} without");
    }

    /// <summary>The wide programs keep their values through the public engine: one download per module, in every mode.</summary>
    [Theory]
    [MemberData(nameof(Shapes))]
    public async Task WidePrograms_KeepTheirValues(Layout layout, Members members)
    {
        const int branches = 5;
        var program = Wide(layout, members, 40, branches);
        var expected = Enumerable.Range(0, branches).Select(index => WideValue(members, index)).ToArray();
        foreach (var mode in Enum.GetValues<CompletedProviderSummaries.Mode>())
        {
            var host = new RunHost(program.Library);
            var root = await ParseDeferred(program, host);
            var flat = await In(mode, () => RunFlat(root));
            Assert.False(flat.IsError, flat.IsError ? flat.Error.ToString() : "");
            Assert.Equal(expected, flat.Value);
            Assert.All(host.Fetches.Values, static count => Assert.Equal(1, count));
        }
    }

    // ── A module a branch holds ─────────────────────────────────────────────

    public enum OwnedLayout
    {
        /// <summary>Every branch holds the module in a property of its own and reads a member path; nothing loads it eagerly.</summary>
        BranchProperty,

        /// <summary>As <see cref="BranchProperty"/>, and a root property holds the module too: the parse completed it.</summary>
        RootAndBranchProperty,

        /// <summary>Every branch holds the module in two properties of its own (one root reached twice) and reads both.</summary>
        BranchPropertyTwice,

        /// <summary>Every branch opens an inline block whose property holds the module, and reads a member path through it.</summary>
        BranchInlineOpen,
    }

    /// <summary>
    /// <paramref name="branches"/> clause families <c>G0 …</c>, each with one load-bearing branch that holds a
    /// <paramref name="width"/>-member module in <paramref name="layout"/> and reads member <c>F&lt;i&gt;</c> through it;
    /// every row evaluates to <see cref="WideValue"/>.
    /// </summary>
    private static Program Owned(OwnedLayout layout, Members members, int width, int branches, string url = "lib")
    {
        var library = new Dictionary<string, string>(StringComparer.Ordinal) { ["tiny"] = Tiny, [url] = MemberLines(members, width, "") };
        var source = new StringBuilder();
        if (layout == OwnedLayout.RootAndBranchProperty)
            source.Append($"Lib = load('{Url(url)}')\n");
        for (var index = 0; index < branches; index++)
        {
            var body = layout switch
            {
                OwnedLayout.BranchPropertyTwice => $"    open '{Url("tiny")}'\n    L = load('{Url(url)}')\n    M = load('{Url(url)}')\n"
                    + $"    V + W(n) + L.F{index}(n) + M.F{index}(n) - M.F{index}(n)\n",
                OwnedLayout.BranchInlineOpen => $"    open '{Url("tiny")}', {{ public L = load('{Url(url)}') }}\n    V + W(n) + L.F{index}(n)\n",
                _ => $"    open '{Url("tiny")}'\n    L = load('{Url(url)}')\n    V + W(n) + L.F{index}(n)\n",
            };
            source.Append($"G{index}(0) = 0\nG{index}(n) = {{\n{body}}}\n");
        }

        for (var index = 0; index < branches; index++)
            source.Append($"G{index}(1)\n");
        return new($"{layout}/{members}/{width}", source.ToString(), library);
    }

    public static TheoryData<OwnedLayout, Members> OwnedShapes()
    {
        var shapes = new TheoryData<OwnedLayout, Members>();
        foreach (var layout in Enum.GetValues<OwnedLayout>())
        {
            foreach (var members in Enum.GetValues<Members>())
                shapes.Add(layout, members);
        }

        return shapes;
    }

    /// <summary>
    /// A MODULE A BRANCH HOLDS. These modules have no opens or output rows. Reading the resolved module's output
    /// requirements yields an empty seed. The member path charges its exact classified provider, whose summary the
    /// first selection that inherits it keeps. From the selection after the keeping one, EVERY traversal counter is
    /// the same for a module of 24 members and one of 240. Before, every selection summarized the whole module again
    /// (16,349 KiB at 1,000 members and 62,300 KiB at 4,000, Release); the reference mode is that control.
    /// </summary>
    [Theory]
    [MemberData(nameof(OwnedShapes))]
    public async Task BranchOwnedModules_LaterSelectionsDoNoWorkInTheModuleWidth(OwnedLayout layout, Members members)
    {
        const int branches = 5;
        const int narrowWidth = 24;
        const int wideWidth = 240;
        var narrow = await MaterializeAll(Owned(layout, members, narrowWidth, branches), branches, CompletedProviderSummaries.Mode.Shared);
        var wide = await MaterializeAll(Owned(layout, members, wideWidth, branches), branches, CompletedProviderSummaries.Mode.Shared);
        var keeper = layout == OwnedLayout.RootAndBranchProperty ? 0 : 1;

        // Cold: the first selection summarizes the module member by member, and adopts nothing.
        Assert.True(wide.Work[0]["SummaryMemberEvaluations"] >= wideWidth, Render(wide.Work[0]));
        Assert.True(wide.Work[0]["SummaryMemberEvaluations"] - narrow.Work[0]["SummaryMemberEvaluations"] >= wideWidth - narrowWidth,
            $"{Render(narrow.Work[0])}\n{Render(wide.Work[0])}");
        Assert.Equal(0, wide.Work[0]["CompletedProviderSummaryAdoptions"]);

        // The keeping selection summarizes the module of an earlier operation once more and keeps it.
        Assert.True(wide.Work[keeper]["SummaryMemberEvaluations"] >= wideWidth, Render(wide.Work[keeper]));
        Assert.True(wide.Work[keeper]["CompletedProviderSummariesKept"] > 0, Render(wide.Work[keeper]));

        // Warm: the width of the module is no input of a later selection's work.
        for (var index = keeper + 1; index < branches; index++)
        {
            Assert.True(narrow.Work[index].SequenceEqual(wide.Work[index]),
                $"selection {index}:\n  {narrowWidth}: {Render(narrow.Work[index])}\n  {wideWidth}: {Render(wide.Work[index])}");
            Assert.True(wide.Work[index]["CompletedProviderSummaryAdoptions"] > 0, Render(wide.Work[index]));
            Assert.True(wide.Work[index]["SummaryMemberEvaluations"] < narrowWidth, Render(wide.Work[index]));
        }

        // What was kept is bounded by the contexts the branches asked for, not by the selections or the width.
        Assert.Equal(ShareOf(narrow.Regions[0]).Count, ShareOf(wide.Regions[0]).Count);

        // The reference: without the share every selection pays the module's width, as every one did before.
        var unshared = await MaterializeAll(Owned(layout, members, wideWidth, branches), branches, CompletedProviderSummaries.Mode.Unshared);
        for (var index = 0; index < branches; index++)
        {
            Assert.True(unshared.Work[index]["SummaryMemberEvaluations"] >= wideWidth, $"selection {index}: {Render(unshared.Work[index])}");
            Assert.Equal(0, unshared.Work[index]["CompletedProviderSummaryAdoptions"]);
            Assert.Equal(0, unshared.Work[index]["CompletedProviderSummariesKept"]);
        }

        Assert.Equal(0, ShareOf(unshared.Regions[0]).Count);
    }

    /// <summary>The branch-owned programs keep their values through the public engine: one download per module, in every mode.</summary>
    [Theory]
    [MemberData(nameof(OwnedShapes))]
    public async Task BranchOwnedModules_KeepTheirValues(OwnedLayout layout, Members members)
    {
        const int branches = 5;
        var program = Owned(layout, members, 40, branches);
        var expected = Enumerable.Range(0, branches).Select(index => WideValue(members, index)).ToArray();
        foreach (var mode in Enum.GetValues<CompletedProviderSummaries.Mode>())
        {
            var host = new RunHost(program.Library);
            var root = await ParseDeferred(program, host);
            var flat = await In(mode, () => RunFlat(root));
            Assert.False(flat.IsError, flat.IsError ? flat.Error.ToString() : "");
            Assert.Equal(expected, flat.Value);
            Assert.All(host.Fetches.Values, static count => Assert.Equal(1, count));
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task BranchOwnedModuleWithOpensOrOutput_UsesTheOrdinaryOutputSummary(bool opens)
    {
        const int width = 40;
        const int branches = 4;
        var basis = Owned(OwnedLayout.BranchProperty, Members.Helper, width, branches);
        var library = new Dictionary<string, string>(basis.Library)
        {
            ["tiny2"] = Tiny2,
            ["lib"] = opens ? $"open '{Url("tiny2")}'\n" + basis.Library["lib"] : basis.Library["lib"] + "F0(3)\n",
        };
        var program = basis with { Library = library };
        var reference = await Observe(program, CompletedProviderSummaries.Mode.Unshared);
        Assert.StartsWith("values ", reference.Outcome, StringComparison.Ordinal);
        foreach (var mode in new[] { CompletedProviderSummaries.Mode.Shared, CompletedProviderSummaries.Mode.Verified })
        {
            var actual = await Observe(program, mode);
            Assert.Equal((reference.Outcome, reference.Exposure, reference.Downloads), (actual.Outcome, actual.Exposure, actual.Downloads));
            var selections = await MaterializeAll(program, branches, mode);
            Assert.All(selections.Work, counters => Assert.True(counters["SummaryMemberEvaluations"] >= width, Render(counters)));
        }
    }

    /// <summary>
    /// A coarse allocation bound over a branch-owned module (in-process ratios, as above). A later selection used to
    /// allocate about 16 KB per module member; from the third selection on it now allocates the levels a lookup still
    /// builds over the module (about 45 bytes per member, measured at 168 KiB / 298 KiB at 1,000 / 4,000 members).
    /// </summary>
    [Fact]
    public async Task BranchOwnedModules_AllocateAlmostNothingInTheModuleWidth()
    {
        const int branches = 6;
        await MaterializeAll(Owned(OwnedLayout.BranchProperty, Members.Helper, 50, branches), branches, CompletedProviderSummaries.Mode.Shared);
        await MaterializeAll(Owned(OwnedLayout.BranchProperty, Members.Helper, 50, branches), branches, CompletedProviderSummaries.Mode.Unshared);

        async Task<long> LaterSelection(int width, CompletedProviderSummaries.Mode mode)
            => (await MaterializeAll(Owned(OwnedLayout.BranchProperty, Members.Helper, width, branches), branches, mode)).Allocated[2..].Min();

        var narrow = await LaterSelection(300, CompletedProviderSummaries.Mode.Shared);
        var wide = await LaterSelection(1200, CompletedProviderSummaries.Mode.Shared);
        var narrowUnshared = await LaterSelection(300, CompletedProviderSummaries.Mode.Unshared);
        var wideUnshared = await LaterSelection(1200, CompletedProviderSummaries.Mode.Unshared);

        Assert.True(wide < narrow * 1.6, $"with the share a later selection allocated {narrow} bytes at 300 members and {wide} at 1,200");
        Assert.True(wideUnshared > narrowUnshared * 2.5,
            $"without the share a later selection allocated {narrowUnshared} bytes at 300 members and {wideUnshared} at 1,200");
        Assert.True(wideUnshared > wide * 10, $"at 1,200 members a later selection allocated {wide} bytes with the share and {wideUnshared} without");
    }

    /// <summary>
    /// ONE ENTRY PER EXACT VIEW. Two canonical URLs serve the same text, so the loader holds two module views, two
    /// declarations and two publications. Branches hold them alternately: each view's summary is kept by the second
    /// selection that holds THAT view and adopted by the third, never served from the other view's entry, whose origins
    /// name the other publication. Values are the reference's.
    /// </summary>
    [Fact]
    public async Task DistinctModuleViews_KeepDistinctSummaries()
    {
        const int branches = 6;
        const int width = 60;
        var lines = MemberLines(Members.Helper, width, "");
        var library = new Dictionary<string, string>(StringComparer.Ordinal) { ["tiny"] = Tiny, ["lib"] = lines, ["copy"] = lines };
        var source = new StringBuilder();
        for (var index = 0; index < branches; index++)
        {
            var url = Url(index % 2 == 0 ? "lib" : "copy");
            source.Append($"G{index}(0) = 0\nG{index}(n) = {{\n    open '{Url("tiny")}'\n    L = load('{url}')\n    V + W(n) + L.F{index}(n)\n}}\n");
        }

        for (var index = 0; index < branches; index++)
            source.Append($"G{index}(1)\n");
        var program = new Program("two views", source.ToString(), library);
        var shared = await MaterializeAll(program, branches, CompletedProviderSummaries.Mode.Shared);

        // Selections 0 and 1 complete one view each; 2 and 3 summarize them as earlier content and keep; 4 and 5 adopt.
        for (var index = 0; index < 4; index++)
            Assert.True(shared.Work[index]["SummaryMemberEvaluations"] >= width, $"selection {index}: {Render(shared.Work[index])}");
        for (var index = 2; index < 4; index++)
            Assert.True(shared.Work[index]["CompletedProviderSummariesKept"] > 0, $"selection {index}: {Render(shared.Work[index])}");
        for (var index = 4; index < branches; index++)
        {
            Assert.True(shared.Work[index]["SummaryMemberEvaluations"] < width, $"selection {index}: {Render(shared.Work[index])}");
            Assert.True(shared.Work[index]["CompletedProviderSummaryAdoptions"] > 0, $"selection {index}: {Render(shared.Work[index])}");
        }

        Assert.True(shared.Work[4].SequenceEqual(shared.Work[5]), $"{Render(shared.Work[4])}\n{Render(shared.Work[5])}");
        foreach (var mode in new[] { CompletedProviderSummaries.Mode.Unshared, CompletedProviderSummaries.Mode.Verified })
        {
            var root = await ParseDeferred(program, new RunHost(library));
            var flat = await In(mode, () => RunFlat(root));
            Assert.False(flat.IsError, flat.IsError ? flat.Error.ToString() : "");
            Assert.Equal(Enumerable.Range(0, branches).Select(index => WideValue(Members.Helper, index)).ToArray(), flat.Value);
        }
    }

    // ── Output seeds of branch-held modules (owner decision pending) ────────

    /// <summary>
    /// The branch-held module shapes whose output seed every selection still computes. The options for them are in
    /// <c>docs/design/completed-module-output-seed-owner-decision-brief-2026-11.md</c>; the tests below pin today's
    /// behavior, which the publication policy keeps until the owner decides.
    /// </summary>
    public enum OutputSeedLayout
    {
        /// <summary>The branch-held module ends with the output row <c>F0(3)</c>.</summary>
        OutputRow,

        /// <summary>The branch-held module opens another module first.</summary>
        Opens,

        /// <summary>As <see cref="Opens"/>, and member <c>F0</c> reads <c>Z</c>, a name the opened module provides.</summary>
        OpensReadByAMember,

        /// <summary>As <see cref="OutputRow"/>, and a root property holds the module too: the parse completed it.</summary>
        OutputRowCompletedByTheParse,

        /// <summary>As <see cref="Opens"/>, and a root property holds the module too: the parse completed it.</summary>
        OpensCompletedByTheParse,
    }

    /// <summary>
    /// <see cref="Owned"/> (<see cref="OwnedLayout.BranchProperty"/>, or <see cref="OwnedLayout.RootAndBranchProperty"/>
    /// for the layouts the parse completes) over a <paramref name="width"/>-member module of the shape
    /// <paramref name="layout"/> names; every row still evaluates to <see cref="WideValue"/>.
    /// </summary>
    private static Program OutputSeedProgram(OutputSeedLayout layout, int width, int branches)
    {
        var completedByTheParse = layout is OutputSeedLayout.OutputRowCompletedByTheParse or OutputSeedLayout.OpensCompletedByTheParse;
        var basis = Owned(completedByTheParse ? OwnedLayout.RootAndBranchProperty : OwnedLayout.BranchProperty, Members.Helper, width, branches);
        var members = MemberLines(Members.Helper, width, "");
        var module = layout switch
        {
            OutputSeedLayout.OutputRow or OutputSeedLayout.OutputRowCompletedByTheParse => members + "F0(3)\n",
            OutputSeedLayout.OpensReadByAMember => $"open '{Url("tiny2")}'\n"
                + members.Replace("public F0(x) = Helper(x) + 0\n", "public F0(x) = Helper(x) + Z - 4\n", StringComparison.Ordinal),
            _ => $"open '{Url("tiny2")}'\n" + members,
        };
        var library = new Dictionary<string, string>(basis.Library, StringComparer.Ordinal) { ["tiny2"] = Tiny2, ["lib"] = module };
        return basis with { Name = $"{layout}/{width}", Library = library };
    }

    /// <summary>
    /// TODAY'S COST OF A BRANCH-HELD MODULE WITH OUTPUT ROWS OR OPENS (owner decision pending). The branch's property
    /// needs the output seed of the module's RESOLVED view, which the sealed table of the completing operation marks as
    /// superseded, while the member path charges the CLASSIFIED view that table names. Every selection over a module an
    /// earlier operation completed therefore summarizes the whole module twice: the resolved root at its sealed
    /// publication, which no exact request asks for and so is never kept, and the classified member path, whose keep
    /// window reads the first walk's results at the same contexts and so is never kept either. Nothing is kept or
    /// adopted at any width, and every such selection does the same work: there is no warm-up. With neither opens nor
    /// rows the output seed is empty and is not computed, so the plain layout's later selections do no work in the width
    /// (<see cref="BranchOwnedModules_LaterSelectionsDoNoWorkInTheModuleWidth"/>). Release harness at 1,000 / 4,000
    /// members: about 16,298 / 61,760 KiB at every later selection, for output rows and opens alike.
    /// </summary>
    [Theory]
    [InlineData(OutputSeedLayout.OutputRow)]
    [InlineData(OutputSeedLayout.Opens)]
    [InlineData(OutputSeedLayout.OpensReadByAMember)]
    [InlineData(OutputSeedLayout.OutputRowCompletedByTheParse)]
    [InlineData(OutputSeedLayout.OpensCompletedByTheParse)]
    public async Task BranchOwnedModuleWithOutputOrOpens_SummarizesBothViewsAtEverySelection_AndKeepsNothing(OutputSeedLayout layout)
    {
        const int branches = 4;
        const int narrowWidth = 24;
        const int wideWidth = 240;
        var narrow = await MaterializeAll(OutputSeedProgram(layout, narrowWidth, branches), branches, CompletedProviderSummaries.Mode.Shared);
        var wide = await MaterializeAll(OutputSeedProgram(layout, wideWidth, branches), branches, CompletedProviderSummaries.Mode.Shared);
        // The first selection over an earlier operation's module: the parse's, or the first selection's.
        var first = layout is OutputSeedLayout.OutputRowCompletedByTheParse or OutputSeedLayout.OpensCompletedByTheParse ? 0 : 1;

        for (var index = first; index < branches; index++)
        {
            var counters = wide.Work[index];
            Assert.True(counters["SummaryMemberEvaluations"] >= 2 * wideWidth, $"selection {index}: {Render(counters)}");
            Assert.True(counters["SummaryMemberEvaluations"] - narrow.Work[index]["SummaryMemberEvaluations"] >= 2 * (wideWidth - narrowWidth),
                $"selection {index}:\n  {narrowWidth}: {Render(narrow.Work[index])}\n  {wideWidth}: {Render(counters)}");
            Assert.Equal(0, counters["CompletedProviderSummariesKept"]);
            Assert.Equal(0, counters["CompletedProviderSummaryAdoptions"]);
        }

        for (var index = first + 2; index < branches; index++)
            Assert.True(wide.Work[first + 1].SequenceEqual(wide.Work[index]),
                $"selection {first + 1}: {Render(wide.Work[first + 1])}\nselection {index}: {Render(wide.Work[index])}");
        Assert.Equal(0, ShareOf(narrow.Regions[0]).Count);
        Assert.Equal(0, ShareOf(wide.Regions[0]).Count);
    }

    /// <summary>
    /// A UNIT KEEPS NOTHING IT COMPLETED ITSELF (today's publication policy; option B of the owner decision brief would
    /// change it). The selection that completes the module summarizes it in its own unit, whose facts are not inherited
    /// content, and keeps nothing; the next selection summarizes the module once more, now an earlier operation's
    /// content, and keeps it; the selection after that adopts it. Release harness at 1,000 / 4,000 members: 20,218 /
    /// 76,959 KiB for the keeping selection, then about 237 / 370 KiB.
    /// </summary>
    [Fact]
    public async Task ABranchThatCompletesAModule_KeepsNothingOfItsOwn_AndTheNextSelectionKeeps()
    {
        const int width = 240;
        const int branches = 3;
        var shared = await MaterializeAll(Owned(OwnedLayout.BranchProperty, Members.Helper, width, branches), branches,
            CompletedProviderSummaries.Mode.Shared);

        var completing = shared.Work[0];
        Assert.True(completing["SummaryMemberEvaluations"] >= width, Render(completing));
        Assert.Equal(0, completing["CompletedProviderSummariesKept"]);
        Assert.Equal(0, completing["CompletedProviderSummaryAdoptions"]);

        var keeping = shared.Work[1];
        Assert.True(keeping["SummaryMemberEvaluations"] >= width, Render(keeping));
        Assert.True(keeping["CompletedProviderSummariesKept"] > 0, Render(keeping));
        Assert.Equal(0, keeping["CompletedProviderSummaryAdoptions"]);

        var adopting = shared.Work[2];
        Assert.True(adopting["SummaryMemberEvaluations"] < 24, Render(adopting));
        Assert.True(adopting["CompletedProviderSummaryAdoptions"] > 0, Render(adopting));
        Assert.True(ShareOf(shared.Regions[0]).Count > 0, "nothing was published");
    }

    private static readonly string WitnessMembers = MemberLines(Members.Helper, 6, "");

    /// <summary>
    /// A witness program whose load-bearing branches each hold the module <paramref name="module"/>
    /// in their own property <c>L</c> and evaluate <paramref name="body"/> (by default <c>W(n) + L.F&lt;i&gt;(n)</c>).
    /// </summary>
    private static Program Witness(string name, string module, Func<int, string>? body = null, string root = "",
        IReadOnlyDictionary<string, string>? more = null, int branches = 4)
    {
        var library = new Dictionary<string, string>(StringComparer.Ordinal) { ["tiny"] = Tiny, ["tiny2"] = Tiny2, ["lib"] = module };
        foreach (var (url, text) in more ?? new Dictionary<string, string>())
            library[url] = text;
        body ??= index => $"L = load('{Url("lib")}')\n    W(n) + L.F{index % 3}(n)";
        return new Program(name, root + Families(branches, body), library);
    }

    /// <summary>
    /// SHARING-DISABLED DIFFERENTIAL WITNESSES for the output seed of a branch-held module: the shapes any reuse of that
    /// seed must keep exact — output rows that read a helper member, an opened name, a nested block, a lifted parameter
    /// or a clause family; opens read by a member; a member whose escaping path into a nested module is bound by that
    /// member (its owner is a different node in the resolved and in the classified view); a module root elaborated to a
    /// callable alias; two views of one text; a module the parse completed; a module held through an inline open block
    /// or twice; and a module holding a load-bearing branch of its own.
    /// </summary>
    public static TheoryData<Program> OutputSeedWitnesses()
    {
        var row = WitnessMembers + "F0(3)\n";
        var opens = $"open '{Url("tiny2")}'\n";
        var witnesses = new TheoryData<Program>
        {
            Witness("output row reading a helper member", row),
            Witness("same member name from different open providers",
                opens + "public F0(x) = Z + x\n",
                index => $"L = load('{Url(index % 2 == 0 ? "lib" : "copy")}')\n    L.F0(n)",
                more: new Dictionary<string, string>(StringComparer.Ordinal)
                {
                    ["copy"] = $"open '{Url("otherProvider")}'\npublic F0(x) = Z + x\n",
                    ["otherProvider"] = "public Z = 40\n",
                }, branches: 8),
            Witness("opens read by a member", opens
                + WitnessMembers.Replace("public F0(x) = Helper(x) + 0\n", "public F0(x) = Helper(x) + Z - 4\n", StringComparison.Ordinal)),
            Witness("output row reading an opened name", opens + WitnessMembers + "Z + F0(1)\n"),
            Witness("member path into a nested module, bound by the member",
                $"T2 = load('{Url("tiny2")}')\n" + WitnessMembers + "public FB(x) = T2.Q(x) + Helper(x)\nFB(3)\n",
                index => $"L = load('{Url("lib")}')\n    L.FB(n) + L.F{index % 3}(n)"),
            Witness("output row reading a nested block", WitnessMembers + "Inner = {\n    public Deep(x) = x + 7\n}\nInner.Deep(2)\n"),
            Witness("output row with a lifted parameter", WitnessMembers + "q + 1\n"),
            Witness("module root elaborated to an alias", WitnessMembers + "public K = q + 1\nK\n"),
            Witness("output row calling a clause family", WitnessMembers + "public P(0) = 0\npublic P(m) = m + 1\nP(2)\n"),
            Witness("two views of one text", row,
                index => $"L = load('{Url(index % 2 == 0 ? "lib" : "copy")}')\n    W(n) + L.F{index % 3}(n)",
                more: new Dictionary<string, string>(StringComparer.Ordinal) { ["copy"] = row }, branches: 8),
            Witness("completed by the parse", row,
                index => $"L = load('{Url("lib")}')\n    L.F{index % 3}(n) + Lib.F{(index + 1) % 3}(n)", root: $"Lib = load('{Url("lib")}')\n"),
            Witness("held twice", row,
                index => $"L = load('{Url("lib")}')\n    M = load('{Url("lib")}')\n    L.F{index % 3}(n) + M.F{(index + 1) % 3}(n)"),
            Witness("load-bearing branch inside the module", PlaceholderMembers + "F0(2)\n",
                index => $"L = load('{Url("lib")}')\n    W(n) + L.{new[] { "F0", "F1", "P" }[index % 3]}(n)"),
        };
        witnesses.Add(new Program("held through an inline open block",
            string.Concat(Enumerable.Range(0, 4).Select(index =>
                $"G{index}(0) = 0\nG{index}(n) = {{\n    open '{Url("tiny")}', {{ public L = load('{Url("lib")}') }}\n    V + L.F{index % 3}(n)\n}}\n"))
            + string.Concat(Enumerable.Range(0, 4).Select(static index => $"G{index}(1)\n")),
            new Dictionary<string, string>(StringComparer.Ordinal) { ["tiny"] = Tiny, ["tiny2"] = Tiny2, ["lib"] = row }));
        return witnesses;
    }

    /// <summary>
    /// The witnesses give the same values, materialize bodies with the same exposure metadata and download the same
    /// modules with the share, in the verifying mode and without the share (the reference). Each alternating-URL case selects each module four times,
    /// covering an adoption opportunity for both candidate policies.
    /// </summary>
    [Theory]
    [MemberData(nameof(OutputSeedWitnesses))]
    public async Task OutputSeedWitnesses_AreTheSameWithAndWithoutTheShare(Program program)
    {
        var unshared = await Observe(program, CompletedProviderSummaries.Mode.Unshared);
        var shared = await Observe(program, CompletedProviderSummaries.Mode.Shared);
        var verified = await Observe(program, CompletedProviderSummaries.Mode.Verified);

        Assert.StartsWith("values ", unshared.Outcome, StringComparison.Ordinal);
        Assert.Equal(unshared.Outcome, shared.Outcome);
        Assert.Equal(unshared.Outcome, verified.Outcome);
        Assert.Equal(unshared.Exposure, shared.Exposure);
        Assert.Equal(unshared.Exposure, verified.Exposure);
        Assert.DoesNotContain("<not materialized>", unshared.Exposure, StringComparison.Ordinal);
        Assert.Equal(unshared.Downloads, shared.Downloads);
        Assert.Equal(unshared.Downloads, verified.Downloads);
        Assert.Equal((0L, 0L, 0), (unshared.Adoptions, unshared.Kept, unshared.Published));
    }

    /// <summary>
    /// A refused branch and two publishing ones hold a module with an output row (see <see cref="RefusedOwnerAndPublished"/>,
    /// declared later: a property, so that it is read after that field is initialized).
    /// </summary>
    private static Program RefusedRowOwnerAndPublished => RefusedOwnerAndPublished with
    {
        Name = "refused holder of a module with an output row, and published",
        Library = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["m"] = "public X = y * 10\n",
            ["lib"] = MemberLines(Members.Helper, 30, "") + "F0(3)\n",
        },
    };

    /// <summary>
    /// ISOLATION FOR A MODULE WITH AN OUTPUT ROW. A refused attempt that holds the module, before and after a branch
    /// completed it, publishes nothing and reports the diagnostics of the reference (code, message, span), and an attempt
    /// cancelled at its unit's seal publishes nothing either; the share holds what the publishing selections leave, and
    /// the values are the reference's. Today that is nothing at all; any reuse of the output seed must keep these.
    /// </summary>
    [Fact]
    public async Task AttemptsHoldingAModuleWithAnOutputRow_PublishNothingWhenRefusedOrCancelled()
    {
        var program = RefusedRowOwnerAndPublished;
        var root = await ParseDeferred(program, new RunHost(program.Library));
        var refusedRegion = RegionAt(root, "G", "F");
        var share = ShareOf(refusedRegion);
        var referenceRoot = await ParseDeferred(program, new RunHost(program.Library));
        var reference = await In(CompletedProviderSummaries.Mode.Unshared,
            async () => Diagnostics(await RegionAt(referenceRoot, "G", "F").MaterializeAsync(CancellationToken.None)));
        Assert.Equal(DiagnosticCode.DeferredBranchForwardsEnclosingParameter, Assert.Single(reference).Code);

        Assert.Equal(reference, Diagnostics(await refusedRegion.MaterializeAsync(CancellationToken.None)));
        Assert.Equal(0, share.Count);
        var good = await RegionAt(root, "Good").MaterializeAsync(CancellationToken.None);
        Assert.True(good.IsOk, good.IsOk ? "" : good.Error.ToString());
        var afterGood = share.Count;
        for (var selection = 0; selection < 2; selection++)
        {
            Assert.Equal(reference, Diagnostics(await refusedRegion.MaterializeAsync(CancellationToken.None)));
            Assert.Equal(afterGood, share.Count);
            Assert.False(refusedRegion.IsMaterialized);
        }

        var other = await RegionAt(root, "Other").MaterializeAsync(CancellationToken.None);
        Assert.True(other.IsOk, other.IsOk ? "" : other.Error.ToString());
        var afterOther = share.Count;
        Assert.Equal(reference, Diagnostics(await refusedRegion.MaterializeAsync(CancellationToken.None)));
        Assert.Equal(afterOther, share.Count);
        Assert.False(refusedRegion.IsMaterialized);
        var flat = await RunFlat(root);
        Assert.False(flat.IsError, flat.IsError ? flat.Error.ToString() : "");
        Assert.Equal([(Decimal128)3, 4], flat.Value);

        var cancelled = OutputSeedProgram(OutputSeedLayout.OutputRow, 12, branches: 3);
        Action? atSeal = null;
        var stage = new FrontEndTraversalObservations
        {
            StageObserver = (name, begin) =>
            {
                if (name == "retarget-and-seal" && begin)
                    atSeal?.Invoke();
            },
        };
        var cancelledRoot = await ParseDeferred(cancelled, new RunHost(cancelled.Library), stage);
        var firstBody = await RegionAt(cancelledRoot, "G0").MaterializeAsync(CancellationToken.None);
        Assert.True(firstBody.IsOk, firstBody.IsOk ? "" : firstBody.Error.ToString());
        var region = RegionAt(cancelledRoot, "G1");
        var published = ShareOf(region).Count;
        for (var selection = 1; selection <= 2; selection++)
        {
            using var cancellation = new CancellationTokenSource();
            var sealedAt = 0;
            atSeal = () =>
            {
                sealedAt++;
                cancellation.Cancel();
            };
            var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await region.MaterializeAsync(cancellation.Token));
            atSeal = null;
            Assert.Equal(cancellation.Token, error.CancellationToken);
            Assert.Equal(1, sealedAt);
            Assert.Equal(published, ShareOf(region).Count);
            Assert.False(region.IsMaterialized);
        }

        var cancelledFlat = await RunFlat(cancelledRoot);
        Assert.False(cancelledFlat.IsError, cancelledFlat.IsError ? cancelledFlat.Error.ToString() : "");
        Assert.Equal(Enumerable.Range(0, 3).Select(index => WideValue(Members.Helper, index)).ToArray(), cancelledFlat.Value);
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
        ("nested", ["Inner = {\n        public Deep(x) = x + 7\n        Hidden = 3\n    }", "public F0(x) = Inner.Deep(x)", "public F1(x) = x + 1",
            "public F2(x) = Inner.Deep(Inner.Deep(x))"], ["F0", "F1", "F2"]),
        ("alias", ["public F0(x) = x + 5", "public F1 = F0", "public F2(x) = F1(x) + 1"], ["F0", "F1", "F2"]),
        ("decon", ["a, b = 3, 4", "public F0(x) = x + a", "public F1(x) = x + b", "public F2(x) = a + b"], ["F0", "F1", "F2"]),
        ("lifted", ["public F0 = q + 1", "public F1(x) = x + 1", "public F2(x) = F1(x) + F0(x)"], ["F1", "F2", "F1"]),
        ("block", ["public F0(x) = { y = x + 1\n        y * 2 }", "public F1(x) = { T = { public U(z) = z + x }\n        T.U(1) }", "public F2(x) = x"],
            ["F0", "F1", "F2"]),
    ];

    private static string ModuleOf(string[] lines, bool opensAnother = false)
        => (opensAnother ? $"open '{Url("tiny2")}'\n" : "") + string.Join('\n', lines) + "\n";

    private static string BlockOf(string[] lines, string indent = "    ")
        => "Lib = {\n" + string.Concat(lines.Select(line => indent + line + "\n")) + "}\n";

    private static string Families(int branches, Func<int, string> body)
        => string.Concat(Enumerable.Range(0, branches).Select(index =>
                $"G{index}(0) = 0\nG{index}(n) = {{\n    open '{Url("tiny")}'\n    {body(index)}\n}}\n"))
            + string.Concat(Enumerable.Range(0, branches).Select(static index => $"G{index}(1)\n"));

    /// <summary>
    /// Small multi-branch programs over varied completed providers: twelve kinds of member bodies (plain, a module
    /// constant, a private helper, a chain, builtins, mutual recursion, a clause family, a nested block, an alias, a
    /// deconstruction, an implicit parameter, block bodies) in fifteen layouts (a module the root opens, with different or
    /// the same member per branch, held by a property, an inline block by path and opened, a block that reads root
    /// names, a branch that opens the root's module again, a nested deferred branch, a provider that opens another
    /// module, a two-level member path; and a module a branch holds in a property of its own: alone, beside a root
    /// property that holds it too, in two properties, through an inline open block, and a module that opens another),
    /// and three special providers (a placeholder inside a block and inside a module, a provider below a parameterized
    /// owner).
    /// </summary>
    public static TheoryData<Program> Corpus()
    {
        const int branches = 4;
        var corpus = new TheoryData<Program>();
        foreach (var (kind, lines, reads) in MemberKinds)
        {
            var library = new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["tiny"] = Tiny,
                ["tiny2"] = Tiny2,
                ["lib"] = ModuleOf(lines),
                ["libopen"] = ModuleOf(lines, opensAnother: true),
            };
            void Add(string layout, string source, bool requiresAdoption = true)
                => corpus.Add(new Program($"{layout}/{kind}", source, library) { RequiresAdoption = requiresAdoption });

            Add("opened module", $"open '{Url("lib")}'\n" + Families(branches, index => $"V + W(n) + {reads[index % 3]}(n)"));
            Add("opened module, one member", $"open '{Url("lib")}'\n" + Families(branches, _ => $"V + {reads[0]}(n)"));
            Add("module property", $"Lib = load('{Url("lib")}')\n" + Families(branches, index => $"W(n) + Lib.{reads[index % 3]}(n)"));
            Add("block path", BlockOf(lines) + Families(branches, index => $"W(n) + Lib.{reads[index % 3]}(n)"));
            Add("opened block", "open Lib\n" + BlockOf(lines)
                + Families(branches, index => $"V + {reads[index % 3]}(n) + {reads[(index + 1) % 3]}(n)"));
            if (kind is "plain" or "const" or "helper" or "chain")
            {
                var outer = BlockOf(lines).Replace("x + 0", "x + Scale", StringComparison.Ordinal)
                    .Replace("x + Base", "x + Base + Scale", StringComparison.Ordinal)
                    .Replace("= x\n", "= x + Scale\n", StringComparison.Ordinal);
                Add("block reading root names", "Scale = 3\nOther(x) = x + Scale\n" + outer
                    + Families(branches, index => $"Other(n) + Lib.{reads[index % 3]}(n)"));
            }

            Add("module opened again by the branch", $"open '{Url("lib")}'\n"
                + string.Concat(Enumerable.Range(0, branches).Select(index =>
                    $"G{index}(0) = 0\nG{index}(n) = {{\n    open '{Url("tiny")}', '{Url("lib")}'\n    V + {reads[index % 3]}(n)\n}}\n"))
                + string.Concat(Enumerable.Range(0, branches).Select(static index => $"G{index}(1)\n")));
            Add("nested deferred branch", $"open '{Url("lib")}'\n"
                + string.Concat(Enumerable.Range(0, branches).Select(index =>
                    $"G{index}(0) = 0\nG{index}(n) = {{\n    open '{Url("tiny")}'\n    H(0) = 1\n    H(m) = {{\n        open '{Url("tiny2")}'\n"
                    + $"        Z + {reads[(index + 1) % 3]}(m)\n    }}\n    V + {reads[index % 3]}(n) + H(n)\n}}\n"))
                + string.Concat(Enumerable.Range(0, branches).Select(static index => $"G{index}(1)\n")));
            Add("provider opening a module", $"open '{Url("libopen")}'\n" + Families(branches, index => $"V + {reads[index % 3]}(n)"));
            Add("two-level path", "Outer = {\n    " + BlockOf(lines, "        ").Replace("\n}", "\n    }", StringComparison.Ordinal) + "}\n"
                + Families(branches, index => $"W(n) + Outer.Lib.{reads[index % 3]}(n)"));
            // Branch-held providers with no opens or output rows.
            Add("branch property", Families(branches, index => $"L = load('{Url("lib")}')\n    W(n) + L.{reads[index % 3]}(n)"));
            Add("root and branch property", $"Lib = load('{Url("lib")}')\n"
                + Families(branches, index => $"L = load('{Url("lib")}')\n    L.{reads[index % 3]}(n) + Lib.{reads[(index + 1) % 3]}(n)"));
            Add("branch property twice", Families(branches,
                index => $"L = load('{Url("lib")}')\n    M = load('{Url("lib")}')\n    L.{reads[index % 3]}(n) + M.{reads[(index + 1) % 3]}(n)"));
            Add("branch property through an inline open", string.Concat(Enumerable.Range(0, branches).Select(index =>
                    $"G{index}(0) = 0\nG{index}(n) = {{\n    open '{Url("tiny")}', {{ public L = load('{Url("lib")}') }}\n    V + L.{reads[index % 3]}(n)\n}}\n"))
                + string.Concat(Enumerable.Range(0, branches).Select(static index => $"G{index}(1)\n")));
            Add("branch property, a module opening another",
                Families(branches, index => $"L = load('{Url("libopen")}')\n    W(n) + L.{reads[index % 3]}(n)"), requiresAdoption: false);
        }

        foreach (var special in SpecialPrograms())
            corpus.Add(special);
        return corpus;
    }

    private const string PlaceholderMembers =
        "public F0(x) = x + 1\npublic P(0) = 0\npublic P(m) = {\n    open 'https://modules.example/tiny2.kat'\n    Z + m\n}\npublic F1(x) = P(x) + 1\n";

    private static readonly Program PlaceholderInABlock = new("placeholder in a block",
        "Lib = {\n" + string.Concat(PlaceholderMembers.Split('\n', StringSplitOptions.RemoveEmptyEntries).Select(static line => "    " + line + "\n"))
        + "}\n" + Families(4, static index => $"W(n) + Lib.{new[] { "F0", "F1", "P" }[index % 3]}(n)"),
        new Dictionary<string, string>(StringComparer.Ordinal) { ["tiny"] = Tiny, ["tiny2"] = Tiny2 });

    private static readonly Program PlaceholderInAModule = new("placeholder in a module",
        $"open '{Url("defer")}'\n" + Families(4, static index => $"V + {new[] { "F0", "F1", "P" }[index % 3]}(n)"),
        new Dictionary<string, string>(StringComparer.Ordinal) { ["tiny"] = Tiny, ["tiny2"] = Tiny2, ["defer"] = PlaceholderMembers });

    private static readonly Program ProviderBelowAnOwner = new("provider below a parameterized owner",
        "Make(p) = {\n    Lib = {\n        public F0(x) = x + p\n        public F1(x) = x + 1\n    }\n"
        + $"    T(0) = 0\n    T(n) = {{\n        open '{Url("tiny")}'\n        V + Lib.F0(n) + Lib.F1(n)\n    }}\n"
        + $"    U(0) = 0\n    U(n) = {{\n        open '{Url("tiny")}'\n        W(n) + Lib.F1(n) + p\n    }}\n"
        + "    T(1) + U(1) + T(2)\n}\nMake(5)\nMake(6)\n",
        new Dictionary<string, string>(StringComparer.Ordinal) { ["tiny"] = Tiny });

    private static IEnumerable<Program> SpecialPrograms() => [PlaceholderInABlock, PlaceholderInAModule, ProviderBelowAnOwner];

    /// <summary>The exposure metadata of every property below <paramref name="root"/>, and the regions its tree carries.</summary>
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

    private sealed record Observed(string Outcome, string Exposure, long Adoptions, long Kept, int Published, int Downloads);

    /// <summary>
    /// One fresh parse of <paramref name="program"/>, evaluated in <paramref name="mode"/>: the values or the error,
    /// and the exposure metadata of every body the run materialized, nested regions included, in discovery order.
    /// </summary>
    private static async Task<Observed> Observe(Program program, CompletedProviderSummaries.Mode mode)
    {
        var host = new RunHost(program.Library);
        var root = await ParseDeferred(program, host);
        var top = new List<DeferredModuleRegion>();
        Describe(root, new StringBuilder(), new HashSet<object>(ReferenceEqualityComparer.Instance), top);
        var observations = new FrontEndTraversalObservations();
        top[0].Loader.TraversalObservations = observations;
        var flat = await In(mode, () => RunFlat(root));
        var outcome = flat.IsOk ? "values " + string.Join(' ', flat.Value) : "error " + flat.Error;

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

        return new(outcome, exposure.ToString(), observations.CompletedProviderSummaryAdoptions, observations.CompletedProviderSummariesKept,
            ShareOf(top[0]).Count, host.TotalFetches);
    }

    /// <summary>
    /// EQUALITY. Every program of the corpus gives the same values, and every body it materializes carries the same
    /// exposure metadata (exposure, required ancestor parameters, capture requirements of every property), with the
    /// share, without it, and in the verifying mode. In that mode the engine computes every adopted summary itself and
    /// throws on the first seed that differs in a name, a reference, their order, or the facts object or key of an
    /// origin, so a value here means no adopted seed differed.
    /// </summary>
    [Theory]
    [MemberData(nameof(Corpus))]
    public async Task AdoptedSummaries_AreTheOnesEachMaterializationWouldCompute(Program program)
    {
        var unshared = await Observe(program, CompletedProviderSummaries.Mode.Unshared);
        var shared = await Observe(program, CompletedProviderSummaries.Mode.Shared);
        var verified = await Observe(program, CompletedProviderSummaries.Mode.Verified);

        Assert.StartsWith("values ", unshared.Outcome, StringComparison.Ordinal);
        Assert.Equal(unshared.Outcome, shared.Outcome);
        Assert.Equal(unshared.Outcome, verified.Outcome);
        Assert.Equal(unshared.Exposure, shared.Exposure);
        Assert.Equal(unshared.Exposure, verified.Exposure);
        Assert.DoesNotContain("<not materialized>", shared.Exposure, StringComparison.Ordinal);
        Assert.Equal(unshared.Downloads, shared.Downloads);

        Assert.Equal((0L, 0L, 0), (unshared.Adoptions, unshared.Kept, unshared.Published));
        // A placeholder disqualifies the whole provider. A branch-held module with opens needs its ordinary
        // output summary, so only independently eligible exact requests can adopt in those corpus programs.
        if (ReferenceEquals(program, PlaceholderInABlock) || ReferenceEquals(program, PlaceholderInAModule))
        {
            Assert.Equal((0L, 0L, 0), (shared.Adoptions, shared.Kept, shared.Published));
            Assert.Equal((0L, 0L, 0), (verified.Adoptions, verified.Kept, verified.Published));
        }
        else if (program.RequiresAdoption)
        {
            Assert.True(shared.Adoptions > 0 && shared.Published > 0, $"{program}: {shared.Adoptions} adoptions, {shared.Published} published");
            Assert.True(verified.Adoptions > 0 && verified.Published > 0,
                $"{program}: {verified.Adoptions} verified adoptions, {verified.Published} published");
        }
    }

    /// <summary>
    /// A PROVIDER THAT HOLDS A PLACEHOLDER IS NEVER KEPT. The facts of a load-bearing branch inside the provider are
    /// replaced when that branch materializes, so a summary computed across it is not a fact of completed content: it
    /// is computed by every materialization, as before, and the values stay those of the reference.
    /// </summary>
    [Fact]
    public async Task AProviderThatHoldsAPlaceholder_IsComputedByEveryMaterialization()
    {
        foreach (var program in new[] { PlaceholderInABlock, PlaceholderInAModule })
        {
            var host = new RunHost(program.Library);
            var root = await ParseDeferred(program, host);
            var regions = Enumerable.Range(0, 4).Select(index => RegionAt(root, $"G{index}")).ToArray();
            var evaluations = new long[regions.Length];
            for (var index = 0; index < regions.Length; index++)
            {
                var observations = new FrontEndTraversalObservations();
                regions[index].Loader.TraversalObservations = observations;
                var body = await regions[index].MaterializeAsync(CancellationToken.None);
                Assert.True(body.IsOk, body.IsOk ? "" : body.Error.ToString());
                Assert.Equal(0, observations.CompletedProviderSummaryAdoptions);
                Assert.Equal(0, observations.CompletedProviderSummariesKept);
                evaluations[index] = observations.SummaryMemberEvaluations;
            }

            // Every selection evaluated the provider's members again.
            Assert.All(evaluations, static count => Assert.True(count >= 3, $"{count} member evaluations"));
            Assert.Equal(0, ShareOf(regions[0]).Count);
        }
    }

    // ── Isolation ───────────────────────────────────────────────────────────

    private static readonly Dictionary<string, string> RefusalLibrary = new(StringComparer.Ordinal)
    {
        ["tiny"] = Tiny,
        // A member that needs an enclosing parameter: the forwarding refusal.
        ["m"] = "public X = y * 10\n",
    };

    /// <summary>
    /// A provider read by a branch that is REFUSED when selected (its module's member needs the enclosing <c>y</c>)
    /// and by two that publish, both reading one member the refused branch does not read.
    /// </summary>
    private static readonly Program RefusedAndPublished = new("refused and published",
        "Lib = {\n    Helper(x) = x * 2\n    public F0(x) = Helper(x) + 0\n    public F1(x) = Helper(x) + 1\n    public F2(x) = Helper(x) + 2\n}\n"
        + "G(y) = {\n  F(0) = 0\n"
        + $"  F(n) = {{ open '{Url("m")}'\n    X + Lib.F0(n)\n }}\n"
        + "  R = F(1)\n  R\n}\n"
        + $"Good(0) = 0\nGood(n) = {{\n    open '{Url("tiny")}'\n    V + Lib.F1(n)\n}}\n"
        + $"Other(0) = 0\nOther(n) = {{\n    open '{Url("tiny")}'\n    V + Lib.F1(n)\n}}\n"
        + "Good(1)\nOther(1)\n",
        RefusalLibrary);

    private static (DiagnosticCode Code, string Message, SourceSpan? Span)[] Diagnostics(EvalResult<Algorithm> refused)
    {
        Assert.True(refused.IsError, "the selection published a body");
        var failure = Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(refused.Error);
        return [.. failure.Diagnostics.Select(static diagnostic => (diagnostic.Code, diagnostic.Message, diagnostic.Span))];
    }

    /// <summary>
    /// AN ATTEMPT THAT PUBLISHES NOTHING LEAVES NOTHING. The refused branch computes the provider's summary at every
    /// selection and stages it, and the stage is dropped with the attempt: the share stays empty, and every refused
    /// selection does the same work and reports the same diagnostic. Once another branch has published, the refused
    /// one adopts, and still reports exactly the diagnostic of its cold selection: code, message and span.
    /// </summary>
    [Fact]
    public async Task ARefusedAttempt_LeavesNothing_AndReportsTheSameBeforeAndAfterOthersPublish()
    {
        var host = new RunHost(RefusedAndPublished.Library);
        var root = await ParseDeferred(RefusedAndPublished, host);
        var refusedRegion = RegionAt(root, "G", "F");
        var share = ShareOf(refusedRegion);

        (DiagnosticCode Code, string Message, SourceSpan? Span)[]? cold = null;
        long coldEvaluations = 0;
        for (var selection = 1; selection <= 3; selection++)
        {
            var observations = new FrontEndTraversalObservations();
            refusedRegion.Loader.TraversalObservations = observations;
            var diagnostics = Diagnostics(await refusedRegion.MaterializeAsync(CancellationToken.None));
            Assert.Equal(DiagnosticCode.DeferredBranchForwardsEnclosingParameter, Assert.Single(diagnostics).Code);
            Assert.True(observations.CompletedProviderSummariesKept > 0, "the refused attempt staged nothing: it never read the provider");
            Assert.Equal(0, observations.CompletedProviderSummaryAdoptions);
            Assert.Equal(0, share.Count);
            Assert.False(refusedRegion.IsMaterialized);
            if (cold is null)
                (cold, coldEvaluations) = (diagnostics, observations.SummaryMemberEvaluations);
            else
            {
                Assert.Equal(cold, diagnostics);
                Assert.Equal(coldEvaluations, observations.SummaryMemberEvaluations);
            }
        }

        // A branch that publishes makes its summaries visible.
        var good = await RegionAt(root, "Good").MaterializeAsync(CancellationToken.None);
        Assert.True(good.IsOk, good.IsOk ? "" : good.Error.ToString());
        var published = share.Count;
        Assert.True(published > 0, "the published attempt kept nothing");

        // The refused branch adopts now, and is refused exactly as before.
        var warm = new FrontEndTraversalObservations();
        refusedRegion.Loader.TraversalObservations = warm;
        Assert.Equal(cold, Diagnostics(await refusedRegion.MaterializeAsync(CancellationToken.None)));
        Assert.True(warm.CompletedProviderSummaryAdoptions > 0, "the refused attempt adopted nothing after another branch published");
        Assert.True(warm.SummaryMemberEvaluations < coldEvaluations, $"{warm.SummaryMemberEvaluations} member evaluations warm, {coldEvaluations} cold");
        Assert.False(refusedRegion.IsMaterialized);

        // Whatever the refused attempts staged was dropped: after the second published branch the share holds exactly
        // what it holds in a parse whose refused branch was never selected.
        var other = await RegionAt(root, "Other").MaterializeAsync(CancellationToken.None);
        Assert.True(other.IsOk, other.IsOk ? "" : other.Error.ToString());
        var controlRoot = await ParseDeferred(RefusedAndPublished, new RunHost(RefusedAndPublished.Library));
        foreach (var family in new[] { "Good", "Other" })
        {
            var control = await RegionAt(controlRoot, family).MaterializeAsync(CancellationToken.None);
            Assert.True(control.IsOk, control.IsOk ? "" : control.Error.ToString());
        }

        Assert.Equal(ShareOf(RegionAt(controlRoot, "Good")).Count, share.Count);
        var flat = await RunFlat(root);
        Assert.False(flat.IsError, flat.IsError ? flat.Error.ToString() : "");
        Assert.Equal([(Decimal128)4, 4], flat.Value);
    }

    /// <summary>
    /// A branch that is REFUSED when selected (the other module's member needs the enclosing <c>y</c>) and holds the
    /// module two publishing branches hold too.
    /// </summary>
    private static readonly Program RefusedOwnerAndPublished = new("refused branch-owned module and published",
        $"G(y) = {{\n  F(0) = 0\n  F(n) = {{ open '{Url("m")}'\n    L = load('{Url("lib")}')\n    X + L.F0(n)\n }}\n  R = F(1)\n  R\n}}\n"
        + $"Good(0) = 0\nGood(n) = {{\n    L = load('{Url("lib")}')\n    L.F1(n)\n}}\n"
        + $"Other(0) = 0\nOther(n) = {{\n    L = load('{Url("lib")}')\n    L.F2(n)\n}}\n"
        + "Good(1)\nOther(1)\n",
        new Dictionary<string, string>(StringComparer.Ordinal) { ["m"] = "public X = y * 10\n", ["lib"] = MemberLines(Members.Helper, 30, "") });

    /// <summary>
    /// A REFUSED ATTEMPT THAT HOLDS A COMPLETED MODULE KEEPS NOTHING. Before any branch completed the module, the refused
    /// branch completes it itself and has nothing to keep. Once a branch published the module, the refused one summarizes
    /// it as an earlier operation's content and stages that summary at every selection, and the stage is dropped with the
    /// attempt: the share does not grow, every such selection does the same work, and the diagnostics (code, message,
    /// span) are those of the cold selection. Once another branch kept the summary, the refused one adopts it and is
    /// refused exactly as before; the share then holds what a parse whose refused branch was never selected holds.
    /// </summary>
    [Fact]
    public async Task ARefusedAttemptHoldingACompletedModule_KeepsNothing_AndReportsTheSame()
    {
        var program = RefusedOwnerAndPublished;
        var root = await ParseDeferred(program, new RunHost(program.Library));
        var refusedRegion = RegionAt(root, "G", "F");
        var share = ShareOf(refusedRegion);

        var cold = Diagnostics(await refusedRegion.MaterializeAsync(CancellationToken.None));
        Assert.Equal(DiagnosticCode.DeferredBranchForwardsEnclosingParameter, Assert.Single(cold).Code);
        var referenceRoot = await ParseDeferred(program, new RunHost(program.Library));
        var reference = await In(CompletedProviderSummaries.Mode.Unshared,
            async () => Diagnostics(await RegionAt(referenceRoot, "G", "F").MaterializeAsync(CancellationToken.None)));
        Assert.Equal(reference, cold);
        Assert.Equal(0, share.Count);

        var good = await RegionAt(root, "Good").MaterializeAsync(CancellationToken.None);
        Assert.True(good.IsOk, good.IsOk ? "" : good.Error.ToString());
        var afterGood = share.Count;

        long? evaluations = null;
        for (var selection = 0; selection < 2; selection++)
        {
            var observations = new FrontEndTraversalObservations();
            refusedRegion.Loader.TraversalObservations = observations;
            Assert.Equal(cold, Diagnostics(await refusedRegion.MaterializeAsync(CancellationToken.None)));
            Assert.True(observations.CompletedProviderSummariesKept > 0, "the refused attempt staged nothing: it never summarized the completed module");
            Assert.Equal(0, observations.CompletedProviderSummaryAdoptions);
            Assert.Equal(afterGood, share.Count);
            Assert.False(refusedRegion.IsMaterialized);
            if (evaluations is null)
                evaluations = observations.SummaryMemberEvaluations;
            else
                Assert.Equal(evaluations, observations.SummaryMemberEvaluations);
        }

        var other = await RegionAt(root, "Other").MaterializeAsync(CancellationToken.None);
        Assert.True(other.IsOk, other.IsOk ? "" : other.Error.ToString());
        Assert.True(share.Count > afterGood, "the second publishing branch kept nothing");
        var warm = new FrontEndTraversalObservations();
        refusedRegion.Loader.TraversalObservations = warm;
        Assert.Equal(cold, Diagnostics(await refusedRegion.MaterializeAsync(CancellationToken.None)));
        Assert.True(warm.CompletedProviderSummaryAdoptions > 0, "the refused attempt adopted nothing after another branch kept the module's summary");
        Assert.True(warm.SummaryMemberEvaluations < evaluations, $"{warm.SummaryMemberEvaluations} member evaluations warm, {evaluations} before");

        var controlRoot = await ParseDeferred(program, new RunHost(program.Library));
        foreach (var family in new[] { "Good", "Other" })
        {
            var control = await RegionAt(controlRoot, family).MaterializeAsync(CancellationToken.None);
            Assert.True(control.IsOk, control.IsOk ? "" : control.Error.ToString());
        }

        Assert.Equal(ShareOf(RegionAt(controlRoot, "Good")).Count, share.Count);
        var flat = await RunFlat(root);
        Assert.False(flat.IsError, flat.IsError ? flat.Error.ToString() : "");
        Assert.Equal([(Decimal128)3, 4], flat.Value);
    }

    /// <summary>
    /// A CANCELLED ATTEMPT THAT HOLDS A COMPLETED MODULE KEEPS NOTHING. After the first branch completed the module, the
    /// second one is cancelled at its unit's seal, when its exposure has summarized the module and staged the summary;
    /// nothing is published, three times, and the next selection keeps it, and the third branch adopts it.
    /// </summary>
    [Fact]
    public async Task ACancelledAttemptHoldingACompletedModule_KeepsNothing_AndTheNextSelectionKeeps()
    {
        var program = Owned(OwnedLayout.BranchProperty, Members.Helper, 12, branches: 3);
        var host = new RunHost(program.Library);
        Action? atSeal = null;
        var stage = new FrontEndTraversalObservations
        {
            StageObserver = (name, begin) =>
            {
                if (name == "retarget-and-seal" && begin)
                    atSeal?.Invoke();
            },
        };
        var root = await ParseDeferred(program, host, stage);
        var first = await RegionAt(root, "G0").MaterializeAsync(CancellationToken.None);
        Assert.True(first.IsOk, first.IsOk ? "" : first.Error.ToString());
        var region = RegionAt(root, "G1");
        var share = ShareOf(region);
        var published = share.Count;

        for (var selection = 1; selection <= 3; selection++)
        {
            using var cancellation = new CancellationTokenSource();
            var kept = stage.CompletedProviderSummariesKept;
            long stagedAtSeal = 0;
            atSeal = () =>
            {
                stagedAtSeal = stage.CompletedProviderSummariesKept - kept;
                cancellation.Cancel();
            };
            var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await region.MaterializeAsync(cancellation.Token));
            atSeal = null;
            Assert.Equal(cancellation.Token, error.CancellationToken);
            Assert.True(stagedAtSeal > 0, "the cancelled attempt had staged nothing when it was cancelled");
            Assert.Equal(published, share.Count);
            Assert.False(region.IsMaterialized);
            Assert.Equal(selection, region.MaterializationAttempts);
        }

        var body = await region.MaterializeAsync(CancellationToken.None);
        Assert.True(body.IsOk, body.IsOk ? "" : body.Error.ToString());
        Assert.True(share.Count > published, "the published attempt kept nothing");
        var adoptions = stage.CompletedProviderSummaryAdoptions;
        var third = await RegionAt(root, "G2").MaterializeAsync(CancellationToken.None);
        Assert.True(third.IsOk, third.IsOk ? "" : third.Error.ToString());
        Assert.True(stage.CompletedProviderSummaryAdoptions > adoptions, "the third branch adopted nothing");
        var flat = await RunFlat(root);
        Assert.False(flat.IsError, flat.IsError ? flat.Error.ToString() : "");
        Assert.Equal(Enumerable.Range(0, 3).Select(index => WideValue(Members.Helper, index)).ToArray(), flat.Value);
    }

    /// <summary>
    /// A CANCELLED ATTEMPT LEAVES NOTHING. The attempt is cancelled at its unit's seal, after its exposure walk
    /// computed and staged the provider's summary; the cancellation keeps the evaluation token's identity, nothing is
    /// published, and the next selection computes again, publishes, and keeps the value.
    /// </summary>
    [Fact]
    public async Task ACancelledAttempt_LeavesNothing_AndTheNextSelectionPublishes()
    {
        var program = Wide(Layout.BlockPath, Members.Helper, 12, branches: 2);
        var host = new RunHost(program.Library);
        Action? atSeal = null;
        var stage = new FrontEndTraversalObservations
        {
            StageObserver = (name, begin) =>
            {
                if (name == "retarget-and-seal" && begin)
                    atSeal?.Invoke();
            },
        };
        var root = await ParseDeferred(program, host, stage);
        var region = RegionAt(root, "G0");
        var share = ShareOf(region);

        for (var selection = 1; selection <= 3; selection++)
        {
            using var cancellation = new CancellationTokenSource();
            var kept = stage.CompletedProviderSummariesKept;
            long stagedAtSeal = 0;
            atSeal = () =>
            {
                stagedAtSeal = stage.CompletedProviderSummariesKept - kept;
                cancellation.Cancel();
            };
            var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await region.MaterializeAsync(cancellation.Token));
            atSeal = null;
            Assert.Equal(cancellation.Token, error.CancellationToken);
            Assert.True(stagedAtSeal > 0, "the cancelled attempt had staged nothing when it was cancelled");
            Assert.Equal(0, share.Count);
            Assert.False(region.IsMaterialized);
            Assert.Equal(selection, region.MaterializationAttempts);
        }

        var body = await region.MaterializeAsync(CancellationToken.None);
        Assert.True(body.IsOk, body.IsOk ? "" : body.Error.ToString());
        Assert.True(share.Count > 0, "the published attempt kept nothing");
        var flat = await RunFlat(root);
        Assert.False(flat.IsError, flat.IsError ? flat.Error.ToString() : "");
        Assert.Equal([WideValue(Members.Helper, 0), WideValue(Members.Helper, 1)], flat.Value);
    }

    /// <summary>
    /// CONCURRENT SELECTIONS. Eight runs of one parsed tree start together, in the verifying mode: the loader's gate
    /// serializes the materializations, each region is materialized once, every run returns the sequential values,
    /// and the share holds what one sequential run publishes; for a module the root opens and for one every branch holds.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ConcurrentRunsOfOneTree_PublishWhatASequentialRunPublishes(bool branchOwned)
    {
        const int branches = 6;
        var program = branchOwned
            ? Owned(OwnedLayout.BranchProperty, Members.Helper, 40, branches)
            : Wide(Layout.OpenedModule, Members.Helper, 40, branches);
        var expected = Enumerable.Range(0, branches).Select(index => WideValue(Members.Helper, index)).ToArray();

        var sequentialHost = new RunHost(program.Library);
        var sequentialRoot = await ParseDeferred(program, sequentialHost);
        var sequential = await In(CompletedProviderSummaries.Mode.Verified, () => RunFlat(sequentialRoot));
        Assert.Equal(expected, sequential.Value);
        var sequentialCount = ShareOf(RegionAt(sequentialRoot, "G0")).Count;

        var host = new RunHost(program.Library);
        var root = await ParseDeferred(program, host);
        var runs = await In(CompletedProviderSummaries.Mode.Verified, async () =>
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

        Assert.Equal(sequentialCount, ShareOf(RegionAt(root, "G0")).Count);
        Assert.All(host.Fetches.Values, static count => Assert.Equal(1, count));
    }

    /// <summary>
    /// ONE SHARE PER PARSE. A share belongs to one loader, which belongs to one parse of one document: nothing is
    /// static, so a second parse of the same source starts cold whatever the first one published.
    /// </summary>
    [Fact]
    public async Task ASecondParse_ReadsNothingOfTheFirst()
    {
        const int branches = 3;
        var program = Wide(Layout.OpenedModule, Members.Helper, 30, branches);
        var first = await MaterializeAll(program, branches, CompletedProviderSummaries.Mode.Shared);
        var second = await MaterializeAll(program, branches, CompletedProviderSummaries.Mode.Shared);

        Assert.NotSame(ShareOf(first.Regions[0]), ShareOf(second.Regions[0]));
        Assert.True(ShareOf(first.Regions[0]).Count > 0);
        for (var index = 0; index < branches; index++)
            Assert.True(first.Work[index].SequenceEqual(second.Work[index]),
                $"selection {index}:\n  {Render(first.Work[index])}\n  {Render(second.Work[index])}");
        Assert.Equal(0, second.Work[0]["CompletedProviderSummaryAdoptions"]);
    }

    // ── A completed module spliced into a branch ────────────────────────────

    /// <summary>
    /// ONE MODULE DECLARATION, VALIDATED ONCE PER PROGRAM. A branch that opens a module the program already completed
    /// receives that declaration: the collision, open-provider and output rules judged it in the operation that
    /// completed it and do not walk it again (<see cref="ModuleUnitRegistry.SkipsValidationOf"/>): the first selection
    /// elaborates the module and skips nothing, and every later one skips exactly three walks, one per rule, whatever
    /// the module's width. Signature analysis no longer enters it either: the first selection analyzes the module's
    /// bodies, and a later one reads their completed signatures (<see cref="ModuleUnits.ReceivesEarlierResolution"/>;
    /// the loader's and the measure's walks of the view are <c>CompletedModuleSpliceTests</c>' subject).
    /// </summary>
    [Fact]
    public async Task ACompletedModuleSplicedIntoABranch_IsNotValidatedAgain()
    {
        const int branches = 4;
        static Program Spliced(int width)
        {
            var library = new Dictionary<string, string>(StringComparer.Ordinal) { ["lib"] = MemberLines(Members.Helper, width, "") };
            var source = new StringBuilder();
            for (var index = 0; index < branches; index++)
                source.Append($"G{index}(0) = 0\nG{index}(n) = {{\n    open '{Url("lib")}'\n    F{index}(n)\n}}\n");
            for (var index = 0; index < branches; index++)
                source.Append($"G{index}(1)\n");
            return new($"spliced/{width}", source.ToString(), library);
        }

        foreach (var width in new[] { 24, 240 })
        {
            var program = Spliced(width);
            var host = new RunHost(program.Library);
            var root = await ParseDeferred(program, host);
            var registry = RegionAt(root, "G0").Loader.ModuleUnits;
            for (var index = 0; index < branches; index++)
            {
                var region = RegionAt(root, $"G{index}");
                var observations = new FrontEndTraversalObservations();
                region.Loader.TraversalObservations = observations;
                var skipped = registry.ValidationWalksSkipped;
                var body = await region.MaterializeAsync(CancellationToken.None);
                Assert.True(body.IsOk, body.IsOk ? "" : body.Error.ToString());
                // The first selection elaborates and validates the module; a later one receives it, judged.
                Assert.Equal(index == 0 ? 0 : 3, registry.ValidationWalksSkipped - skipped);
                // The first selection analyzes the module's bodies; a later one analyzes the branch body alone.
                if (index == 0)
                    Assert.True(observations.SignatureAnalysisBodies >= width, $"width {width}, selection {index}: {Render(Counters(observations))}");
                else
                    Assert.Equal((1L, 1L), (observations.SignatureAnalysisBodies, observations.CompletedModuleAnalysesSkipped));
            }

            var flat = await RunFlat(root);
            Assert.False(flat.IsError, flat.IsError ? flat.Error.ToString() : "");
            Assert.Equal(Enumerable.Range(0, branches).Select(static index => (Decimal128)(2 + index)).ToArray(), flat.Value);
            Assert.Equal(1, host.TotalFetches);
        }
    }
}
