using System.Diagnostics;
using System.Text;
using Xunit.Abstractions;

namespace KatLang.Tests.ExposureCensus;

/// <summary>
/// The E-18 route census (discovery, 2026-11-14): programs generated over the whole route space of a
/// static selection inside <c>F(y)</c> (<see cref="CensusGrid"/>), checked mechanically for the two
/// properties under test — exposure is exact (U: under-charge, O: over-charge, W: work, and T: a deconstruction
/// cell gives what its rows twin gives) and the model refuses exactly the under-declared trees (M, through Lean,
/// outside the canonical targets).
///
/// <para>The census FIXES NOTHING. Every gap it finds is listed in <c>census-gaps.txt</c> (the ratchet):
/// the default test computes the gaps of its deterministic 3-way subset and requires them to equal the
/// list restricted to that subset, so a new gap fails it and so does a listed gap that no longer occurs.
/// The fix run takes the ratchet as its acceptance test. Since the E-18 F1 closeout (2026-11-15, owner
/// decisions Q1–Q3) the list holds the three lines no decision removes: two over-charges of the fixed
/// self-checks and the model's stricter verdict on one of them. An exported reader whose escaped read fails at
/// a check that can never pass where the evaluator makes it is no gap: it is counted in the impossible-check
/// class (decided by the grid and by behavior, which must agree), and no published requirement may be one that
/// no chain can supply.</para>
///
/// <para>THE EXTENSION (2026-11-17): the heads <c>rt-capture</c> and <c>rt-alg-call</c> and the ending
/// <c>result-member</c> (<see cref="CensusGrid.ExtensionHeads"/>, <see cref="CensusGrid.ExtensionEnds"/>) generate cells of
/// their own (<see cref="CensusGrid.GenerateExtension"/>), with their own stored cover <c>census-extension-subset.txt</c>
/// and their own count pins, so the grid's cells, cover and counts are those of every earlier run. The settlement families
/// of 0a1718d2 (<see cref="CensusGrid.SettlementFamilies"/>) run with them. Check R compares every
/// <c>rt-alg-call</c> cell with its static-route twin.</para>
///
/// <para>Modes (<c>KATLANG_EXPOSURE_CENSUS</c>; output directory <c>KATLANG_EXPOSURE_CENSUS_OUT</c>):
/// <c>full</c> — every valid case of the grid and of the extension, the settlement families and every work family, compared
/// with the whole list (it also writes the recomputed covers and the model sample's retained witnesses, the regeneration path
/// of the stored files; the grid's outputs keep their names, the extension's are <c>full-extension-*.txt</c>);
/// <c>work</c> — the work families alone;
/// <c>twins</c> — every block-headed reference cell against its declared copy, the same literal given a name
/// (owner decisions Q3, 2026-11-14, and D2, 2026-11-15; the default suite compares the stored cover's cells);
/// <c>emit-lean</c> — writes the encodings (3-way subset) as Lean batch files for <c>lake env lean</c>;
/// <c>check-lean</c> — reads the batch outputs and compares M1–M4 with the list (the model sample is the grid's alone);
/// <c>emit-head</c> — writes every valid case's probe programs for the HEAD a4b545e8 probe, the probe's scratch project
/// (<see cref="CensusHeadProbe"/>, tracked in this folder) and the commands that build and run it;
/// <c>check-head</c> — reads that probe's output (<c>head.out</c>), classifies over-charges as inherited or
/// new and runs the HEAD self-checks. Without the variable only the default subsets run.</para>
/// </summary>
public sealed class ExposureCensusTests(ITestOutputHelper output)
{
    private const string ModeVariable = "KATLANG_EXPOSURE_CENSUS";
    private const string OutVariable = "KATLANG_EXPOSURE_CENSUS_OUT";
    // Full mode independently recomputes the valid universe and its cover. Pin its observed triple
    // count here too, so dropping a subset entry cannot silently shrink default-suite coverage.
    // (5,495 before the deconstruction position, the mid-fallback ending and the fallback requirement of
    // 2026-11-16; every earlier triple is still a valid one, since no earlier cell changed.)
    private const int ValidTripleCount = 6861;

    // The impossible-check class (CensusRunner.Run): observations that are no gap, pinned so that the class can
    // neither grow nor shrink unnoticed. Full mode pins the whole valid grid, the default mode its stored cover.
    // Full: the 7,478 of the earlier cells, unchanged, plus 5,599 of the cells the 2026-11-16 dimensions added.
    private const int ImpossibleObservationsInFull = 13077;
    private const int ImpossibleObservationsInDefault = 163;

    // The extension's pins (2026-11-17). Every valid triple of the widened grid: the grid's 6,861 plus the 1,186 only extension
    // cells have; the union of the two stored covers holds them all (full mode recomputes both).
    private const int WidenedValidTripleCount = 8047;
    // Impossible-check observations of the extension's cells and the settlement families: the whole extension in full mode,
    // its stored cover plus the families in the default mode (34 of the cover's cells, one re-entry and four hop readers).
    private const int ExtensionImpossibleObservationsInFull = 5557;
    private const int ExtensionImpossibleObservationsInDefault = 39;

    private static string? Mode => Environment.GetEnvironmentVariable(ModeVariable) is { Length: > 0 } mode ? mode : null;

    private static string OutDirectory
        => Environment.GetEnvironmentVariable(OutVariable) is { Length: > 0 } path
            ? path
            : throw new InvalidOperationException($"{OutVariable} must name an output directory for census mode {Mode}.");

    private static string RatchetPath => Path.Combine(RepoRoot.Find(), "tests", "KatLang.Tests", "ExposureCensus", "census-gaps.txt");

    // C#-side checks the default and full modes compute; M lines belong to check-lean.
    private static readonly HashSet<string> CSharpChecks = new(StringComparer.Ordinal) { "U", "O", "E", "H", "T", "R" };

    internal static List<CensusGap> ReadRatchet()
        => File.ReadLines(RatchetPath).Where(l => l.Length > 0 && !l.StartsWith('#'))
            .Select(l => CensusGap.Parse(l) ?? throw new InvalidDataException($"Malformed ratchet line: {l}")).ToList();

    // O's inherited/new split is decided against HEAD a4b545e8's metadata (check-head); the computed class
    // is "over-charge" and the ratchet carries the decided tag.
    private static string Key(CensusGap gap)
        => $"{gap.Check}\t{(gap.Class.StartsWith("over-charge", StringComparison.Ordinal) ? "over-charge" : gap.Class)}\t{gap.Id}\t{gap.Reader}\t{gap.Detail}";

    private static string SubsetPath => Path.Combine(RepoRoot.Find(), "tests", "KatLang.Tests", "ExposureCensus", "census-subset.txt");

    /// <summary>
    /// The default subset: the greedy 3-way cover of the VALID grid cases, stored in
    /// <c>census-subset.txt</c> (validity needs a parse of every case, which only full mode affords; full
    /// mode recomputes the cover and requires the file to equal it).
    /// </summary>
    internal static IReadOnlyList<CensusCase> Subset()
        => File.ReadLines(SubsetPath).Where(l => l.Length > 0 && !l.StartsWith('#'))
            .Select(id => CensusGrid.TryParseId(id) ?? throw new InvalidDataException($"Not a census id: {id}")).ToArray();

    private static string ExtensionSubsetPath => Path.Combine(RepoRoot.Find(), "tests", "KatLang.Tests", "ExposureCensus", "census-extension-subset.txt");

    /// <summary>
    /// The extension's default subset, stored in <c>census-extension-subset.txt</c>: the greedy cover of the triples of the
    /// VALID extension cells that no valid grid cell has (<see cref="CensusGrid.ThreeWayCover(IReadOnlyList{CensusCase}, IReadOnlySet{string}?)"/>),
    /// so that it and <see cref="Subset"/> together hold every valid triple of the widened grid.
    /// </summary>
    internal static IReadOnlyList<CensusCase> ExtensionSubset()
        => File.ReadLines(ExtensionSubsetPath).Where(l => l.Length > 0 && !l.StartsWith('#'))
            .Select(id => CensusGrid.TryParseId(id) ?? throw new InvalidDataException($"Not a census id: {id}")).ToArray();

    private const string ExtensionSubsetHeader =
        "# E-18 route census extension subset: the greedy cover of the valid extension cells' triples that no valid grid cell has (full mode recomputes it).";

    private static IReadOnlyList<CensusCase> ExtensionCover(IReadOnlyList<CensusCase> validGrid, IReadOnlyList<CensusCase> validExtension)
        => CensusGrid.ThreeWayCover(validExtension, CensusGrid.Triples(validGrid));

    private static string WitnessPath => Path.Combine(RepoRoot.Find(), "tests", "KatLang.Tests", "ExposureCensus", "census-model-witnesses.txt");

    // Keep known model findings sampled when an expanded grid chooses a different greedy cover.
    // These stable witnesses remain after the corresponding ratchet entry is fixed and removed; a witness leaves
    // only when its case leaves the valid grid (full mode writes the list of those still valid and requires the
    // stored file to equal it).
    private static IReadOnlyList<CensusCase> ModelCases()
        => Subset().Concat(CensusGrid.Fixed()).Concat(File.ReadLines(WitnessPath).Where(line => line.Length > 0 && !line.StartsWith('#'))
            .Select(id => CensusGrid.TryParseId(id) ?? throw new InvalidDataException($"Not a model witness id: {id}")))
            .DistinctBy(@case => @case.Id, StringComparer.Ordinal).ToArray();

    private static async Task<List<CensusCaseResult>> RunAll(IReadOnlyList<CensusCase> cases, bool collectLean, int parallelism = 1)
    {
        var results = new CensusCaseResult[cases.Count];
        await Parallel.ForEachAsync(Enumerable.Range(0, cases.Count), new ParallelOptions { MaxDegreeOfParallelism = parallelism },
            async (i, _) => results[i] = await CensusRunner.Run(cases[i], collectLean));
        return [.. results];
    }

    private static int FullParallelism => Math.Max(1, Environment.ProcessorCount - 2);

    private static void AssertMatchesRatchet(IReadOnlyList<CensusGap> computed, ISet<string> evaluatedIds, ISet<string> checks, string scope,
        bool completeDomain = false)
    {
        var listed = ReadRatchet().Where(g => checks.Contains(g.Check) && (completeDomain || evaluatedIds.Contains(g.Id))).Select(Key).ToHashSet(StringComparer.Ordinal);
        var found = computed.Where(g => checks.Contains(g.Check)).Select(Key).ToHashSet(StringComparer.Ordinal);
        var added = found.Except(listed).Order(StringComparer.Ordinal).ToArray();
        var gone = listed.Except(found).Order(StringComparer.Ordinal).ToArray();
        Assert.True(added.Length == 0 && gone.Length == 0,
            $"Census ratchet ({scope}) differs from census-gaps.txt.\nNEW gaps ({added.Length}):\n{string.Join("\n", added.Take(40))}\n"
            + $"LISTED gaps that no longer occur ({gone.Length}):\n{string.Join("\n", gone.Take(40))}");
    }

    private void WriteIfRequested(string name, IEnumerable<string> lines)
    {
        if (Environment.GetEnvironmentVariable(OutVariable) is not { Length: > 0 } directory) return;
        Directory.CreateDirectory(directory);
        File.WriteAllLines(Path.Combine(directory, name), lines);
        output.WriteLine($"wrote {Path.Combine(directory, name)}");
    }

    private static IEnumerable<string> Summary(IReadOnlyList<CensusCaseResult> results)
    {
        foreach (var group in results.Where(r => r.Skipped is not null).GroupBy(r => r.Skipped!).OrderByDescending(g => g.Count()))
            yield return $"skipped\t{group.Count()}\t{group.Key}";
        yield return $"valid\t{results.Count(r => r.Skipped is null)}";
        yield return $"inside-works\t{results.Count(r => r.Skipped is null && r.InsideWorks)}";
        yield return $"impossible-check\t{results.Sum(r => r.Impossible.Count)}";
        yield return $"unsupplied-requirement-cases\t{results.Count(r => r.UnsuppliedRequirements.Count > 0)}";
        foreach (var group in results.SelectMany(r => r.Gaps).GroupBy(g => $"{g.Check}\t{g.Class}").OrderBy(g => g.Key, StringComparer.Ordinal))
            yield return $"gaps\t{group.Key}\t{group.Count()}";
    }

    // The Q1 invariant: no valid case publishes a requirement no level of its declaring chain can supply.
    private static List<string> Unsupplied(IReadOnlyList<CensusCaseResult> results)
        => results.Where(r => r.UnsuppliedRequirements.Count > 0)
            .Select(r => $"{r.Case.Id}\t{string.Join(" ; ", r.UnsuppliedRequirements)}").ToList();

    private static IEnumerable<string> Observations(IReadOnlyList<CensusCaseResult> results)
        => results.Where(r => r.Skipped is null).Select(r =>
            $"{r.Case.Id}\t{string.Join(" ", r.Metadata.Select(m => $"{m.Key}={m.Value}"))}\t{string.Join(" ; ", r.Outcomes.Select(o => $"{o.Key}: {o.Value}"))}");

    // ── Default mode ──────────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// The deterministic 3-way subset (every combination of three dimension values that occurs in a
    /// generated case), the controls and the self-check cases: their gaps equal the ratchet restricted to
    /// them.
    /// </summary>
    [Fact]
    public async Task DefaultSubset_GapsEqualTheRatchet()
    {
        var clock = Stopwatch.StartNew();
        var subset = Subset();
        var cases = subset.Concat(CensusGrid.Fixed()).ToArray();
        var results = await RunAll(cases, collectLean: false);
        clock.Stop();
        output.WriteLine($"subset {subset.Count} + fixed {CensusGrid.Fixed().Count}; triples {CensusGrid.TripleCount(subset)}; {clock.Elapsed.TotalSeconds:F1} s");
        // The subset holds valid cases only (full mode keeps it so).
        Assert.All(results, r => Assert.Null(r.Skipped));
        foreach (var line in Summary(results)) output.WriteLine(line);
        WriteIfRequested("default-summary.txt", Summary(results).Prepend($"time\t{clock.Elapsed.TotalSeconds:F1} s\tcases\t{cases.Length}"));
        WriteIfRequested("default-gaps.txt", results.SelectMany(r => r.Gaps).Select(g => g.Line));
        WriteIfRequested("default-observations.txt", Observations(results));
        WriteIfRequested("default-impossible.txt", results.SelectMany(r => r.Impossible).Select(g => g.Line));
        WriteIfRequested("default-unsupplied-requirements.txt", Unsupplied(results));

        // Generation is total over the subset: a case that does not parse is a skip, never a silent drop.
        Assert.Equal(cases.Length, results.Count);
        AssertMatchesRatchet(results.SelectMany(r => r.Gaps).ToList(), cases.Select(c => c.Id).ToHashSet(StringComparer.Ordinal), CSharpChecks, "default subset");
        Assert.Equal(ImpossibleObservationsInDefault, results.Sum(r => r.Impossible.Count));
        Assert.Empty(Unsupplied(results));
    }

    [Fact]
    public void Generation_IsDeterministic_AndTheSubsetCoversEveryTriple()
    {
        var (all, excluded) = CensusGrid.Generate();
        var (again, _) = CensusGrid.Generate();
        Assert.Equal(all.Select(c => c.Id), again.Select(c => c.Id));
        Assert.Equal(all.Select(c => c.Body), again.Select(c => c.Body));
        Assert.Equal(all.Count, all.Select(c => c.Id).Distinct(StringComparer.Ordinal).Count());
        Assert.Empty(all.Select(c => c.Id).Intersect(excluded.Select(e => e.Id)));
        var generated = all.Select(c => c.Id).ToHashSet(StringComparer.Ordinal);
        var subset = Subset();
        Assert.All(subset, c => Assert.Contains(c.Id, generated));
        Assert.Equal(subset.Count, subset.Select(c => c.Id).Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(ValidTripleCount, CensusGrid.TripleCount(subset));
        // The cover algorithm is deterministic and covers every triple of its input.
        var cover = CensusGrid.ThreeWayCover(subset);
        Assert.Equal(cover.Select(c => c.Id), CensusGrid.ThreeWayCover(subset).Select(c => c.Id));
        Assert.Equal(CensusGrid.TripleCount(subset), CensusGrid.TripleCount(cover));
    }

    // ── Default mode: the extension and the settlement families ───────────────────────────────────

    /// <summary>
    /// The extension's stored cover and the settlement families (<see cref="CensusGrid.SettlementFamilies"/>): their gaps
    /// equal the ratchet restricted to them, and their impossible-check observations are pinned.
    /// </summary>
    [Fact]
    public async Task DefaultExtension_GapsEqualTheRatchet()
    {
        var clock = Stopwatch.StartNew();
        var subset = ExtensionSubset();
        var families = CensusGrid.SettlementFamilies();
        var cases = subset.Concat(families).ToArray();
        var results = await RunAll(cases, collectLean: false);
        clock.Stop();
        output.WriteLine($"extension subset {subset.Count} + settlement families {families.Count}; {clock.Elapsed.TotalSeconds:F1} s");
        Assert.All(results, r => Assert.Null(r.Skipped));
        foreach (var line in Summary(results)) output.WriteLine(line);
        WriteIfRequested("default-extension-summary.txt", Summary(results).Prepend($"time\t{clock.Elapsed.TotalSeconds:F1} s\tcases\t{cases.Length}"));
        WriteIfRequested("default-extension-gaps.txt", results.SelectMany(r => r.Gaps).Select(g => g.Line));
        WriteIfRequested("default-extension-observations.txt", Observations(results));
        WriteIfRequested("default-extension-impossible.txt", results.SelectMany(r => r.Impossible).Select(g => g.Line));
        WriteIfRequested("default-extension-unsupplied-requirements.txt", Unsupplied(results));

        Assert.Equal(cases.Length, results.Count);
        // Check R ran on the stored cover (it compares every rt-alg-call cell with its static-route twin).
        Assert.Contains(subset, CensusRunner.HasStaticRouteTwin);
        AssertMatchesRatchet(results.SelectMany(r => r.Gaps).ToList(), cases.Select(c => c.Id).ToHashSet(StringComparer.Ordinal), CSharpChecks,
            "default extension subset");
        Assert.Equal(ExtensionImpossibleObservationsInDefault, results.Sum(r => r.Impossible.Count));
        Assert.Empty(Unsupplied(results));
    }

    [Fact]
    public void ExtensionGeneration_IsDeterministic_LeavesTheGridAlone_AndTheCoversHoldEveryTriple()
    {
        var (grid, gridExcluded) = CensusGrid.Generate();
        var (extension, excluded) = CensusGrid.GenerateExtension();
        var (again, _) = CensusGrid.GenerateExtension();
        Assert.Equal(extension.Select(c => c.Id), again.Select(c => c.Id));
        Assert.Equal(extension.Select(c => c.Body), again.Select(c => c.Body));
        Assert.Equal(extension.Count, extension.Select(c => c.Id).Distinct(StringComparer.Ordinal).Count());
        Assert.Empty(extension.Select(c => c.Id).Intersect(excluded.Select(e => e.Id)));
        // Every cell of the extension uses a new value, and the grid of earlier runs is exactly the rest of the widened product.
        Assert.All(extension, c => Assert.True(CensusGrid.IsExtension(c.Dim("head"), c.Dim("end")), c.Id));
        Assert.Empty(grid.Select(c => c.Id).Intersect(extension.Select(c => c.Id).Concat(excluded.Select(e => e.Id))));
        var widened = CensusGrid.AllHeads.Length * CensusGrid.Positions.Length * CensusGrid.OpenLevels.Length * CensusGrid.ReaderKinds.Length
            * CensusGrid.Places.Length * CensusGrid.AllEnds.Length * CensusGrid.Requirements.Length;
        Assert.Equal(widened, grid.Count + gridExcluded.Count + extension.Count + excluded.Count);

        var generated = extension.Select(c => c.Id).ToHashSet(StringComparer.Ordinal);
        var subset = ExtensionSubset();
        Assert.All(subset, c => Assert.Contains(c.Id, generated));
        Assert.Equal(subset.Count, subset.Select(c => c.Id).Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(WidenedValidTripleCount, CensusGrid.Triples([.. Subset(), .. subset]).Count);
        // The covered-triple cover is the plain cover when nothing is covered yet, and covers exactly what is left.
        var gridSubset = Subset();
        Assert.Equal(CensusGrid.ThreeWayCover(gridSubset).Select(c => c.Id), CensusGrid.ThreeWayCover(gridSubset, covered: null).Select(c => c.Id));
        var rest = CensusGrid.ThreeWayCover(subset, CensusGrid.Triples(gridSubset));
        Assert.True(CensusGrid.Triples([.. gridSubset, .. subset]).SetEquals(CensusGrid.Triples([.. gridSubset, .. rest])));
        Assert.True(rest.Count <= subset.Count);
        // The settlement families have distinct ids and readers, and parse cleanly with every probe.
        var families = CensusGrid.SettlementFamilies();
        Assert.Equal(families.Count, families.Select(f => f.Id).Distinct(StringComparer.Ordinal).Count());
        Assert.All(families, f => Assert.Equal(f.Readers.Count, f.Readers.Select(r => r.Label).Distinct(StringComparer.Ordinal).Count()));
        Assert.All(families, f => Assert.NotNull(CensusRunner.Probes(f)));
    }

    /// <summary>The controls stay exported and every probe of theirs succeeds.</summary>
    [Fact]
    public async Task Controls_StayExported()
    {
        foreach (var @case in CensusGrid.Fixed().Where(c => c.Kind == "control"))
        {
            var result = await CensusRunner.Run(@case, collectLean: false);
            Assert.Null(result.Skipped);
            Assert.Equal("exported", result.Metadata["A"]);
            Assert.All(result.Outcomes, o => Assert.StartsWith("ok ", o.Value, StringComparison.Ordinal));
            Assert.Empty(result.Gaps);
        }
    }

    /// <summary>
    /// Self-checks on the current build: O flags I25 (listed as an inherited over-charge), the static-prefix
    /// case's exported copy is "needed" (its M2 flag is the check-lean run's), and W flags the Box family and
    /// the Mid(p) discharge family.
    /// </summary>
    [Fact]
    public async Task SelfChecks_CurrentBuild()
    {
        var fixedCases = CensusGrid.Fixed().ToDictionary(c => c.Id, StringComparer.Ordinal);
        var i25 = await CensusRunner.Run(fixedCases["selfcheck=I25-eager-own-open"], collectLean: false);
        Assert.Contains(i25.Gaps, g => g is { Check: "O", Class: "over-charge", Reader: "A", Detail: "r=y@0" });
        Assert.Contains(ReadRatchet(), g => g is { Check: "O", Class: "over-charge-inherited", Id: "selfcheck=I25-eager-own-open" });

        // The static prefix of a runtime open: the front end charges the reader, and the selection model now refuses
        // the copy without that requirement (no M2 line; NavigationSourceDomainGuards.CheckSites.staticPrefixRuntimeOpen_*).
        var prefix = await CensusRunner.Run(fixedCases["selfcheck=static-prefix-runtime-open"], collectLean: true);
        Assert.Equal("LocalOnlyCapturedAncestorParameters[y@0]", prefix.Metadata["A"]);
        Assert.Contains(prefix.Lean, item => item.Role == "copy-needed");
        Assert.DoesNotContain(ReadRatchet(), g => g.Id == "selfcheck=static-prefix-runtime-open");

        // The two families the host checks of 2026-11-14 flagged settle within the bound.
        foreach (var family in new[] { CensusWork.BoxSelfCheck(), CensusWork.DischargeSelfCheck() })
        {
            var measured = CensusWork.Measure(family);
            output.WriteLine($"{family.Id}: frames {string.Join(" / ", measured.Frames)}; checkpoints {string.Join(" / ", measured.Checkpoints)}");
            Assert.True(measured.WithinBound, measured.Problem);
            Assert.DoesNotContain(ReadRatchet(), g => g.Check == "W" && g.Id == family.Id);
        }
    }

    // ── Full mode ─────────────────────────────────────────────────────────────────────────────────

    /// <summary>Every W family (doubling and depth); flagged ones are appended to <paramref name="gaps"/>.</summary>
    private static List<string> RunWork(List<CensusGap> gaps)
    {
        var work = new List<string>();
        foreach (var (family, why) in CensusWork.Families().Append((CensusWork.BoxSelfCheck(), null)).Append((CensusWork.DischargeSelfCheck(), null)))
        {
            if (why is not null) { work.Add($"{family.Id}\texcluded\t{why}"); continue; }
            if (CensusWork.Diagnostics(family.Program(CensusWork.Widths[0])) is { } diagnostics) { work.Add($"{family.Id}\tskipped\t{diagnostics}"); continue; }
            var measured = CensusWork.Measure(family);
            work.Add($"{family.Id}\t{(measured.WithinBound ? "ok" : "FLAG")}\tframes {string.Join("/", measured.Frames)}\tcheckpoints {string.Join("/", measured.Checkpoints)}\t{measured.Problem}");
            if (!measured.WithinBound) gaps.Add(new CensusGap("W", "work-bound", family.Id, "-", measured.Problem!));
        }
        foreach (var head in CensusGrid.Heads.Where(h => !h.StartsWith("rt-", StringComparison.Ordinal) && h != "opened"))
            foreach (var reader in CensusGrid.ReaderKinds)
            {
                var id = $"W|depth|head={head}|reader={reader}";
                var source = CensusWork.DepthProgram(head, reader, 8);
                if (CensusWork.Diagnostics(source) is { } diagnostics) { work.Add($"{id}\tskipped\t{diagnostics}"); continue; }
                var (max, levels, bound) = CensusWork.MeasureDepth(source, 8);
                work.Add($"{id}\t{(max <= 1 ? "ok" : "FLAG")}\tlevels {levels}\tmax-per-level {max}\twith-bound-owners {bound}");
                if (max > 1) gaps.Add(new CensusGap("W", "work-depth-resettled", id, "-", $"max-per-level {max}"));
            }
        return work;
    }

    /// <summary><c>work</c> mode: the W families alone, compared with the ratchet's W lines.</summary>
    [Fact]
    public void WorkMode_FamiliesEqualTheRatchet()
    {
        if (Mode != "work") return;
        var clock = Stopwatch.StartNew();
        var gaps = new List<CensusGap>();
        var work = RunWork(gaps);
        output.WriteLine($"work families {work.Count}; flagged {gaps.Count}; {clock.Elapsed.TotalSeconds:F1} s");
        WriteIfRequested("work-gaps.txt", gaps.Select(g => g.Line));
        WriteIfRequested("work.txt", work);
        AssertMatchesRatchet(gaps, work.Select(w => w.Split('\t')[0]).ToHashSet(StringComparer.Ordinal),
            new HashSet<string>(["W"], StringComparer.Ordinal), "work", completeDomain: true);
    }

    [Fact]
    public async Task FullMode_EveryValidCaseAndFamily_GapsEqualTheRatchet()
    {
        if (Mode != "full") return;
        var clock = Stopwatch.StartNew();
        var (all, excluded) = CensusGrid.Generate();
        var cases = all.Concat(CensusGrid.Fixed()).ToArray();
        var results = await RunAll(cases, collectLean: false, FullParallelism);
        var caseTime = clock.Elapsed;
        var valid = results.Where(r => r.Skipped is null && r.Case.Kind == "grid").Select(r => r.Case).ToArray();
        var gaps = results.SelectMany(r => r.Gaps).ToList();
        var cover = CensusGrid.ThreeWayCover(valid);
        WriteIfRequested("census-subset.txt", cover.Select(c => c.Id).Prepend("# E-18 route census default subset: the greedy 3-way cover of the valid grid cases (full mode recomputes it)."));
        // The model sample's retained witnesses are valid cases: one that left the valid grid leaves the sample.
        var validIds = valid.Select(c => c.Id).ToHashSet(StringComparer.Ordinal);
        var storedWitnesses = File.ReadAllLines(WitnessPath);
        var validWitnesses = storedWitnesses.Where(line => line.Length == 0 || line.StartsWith('#') || validIds.Contains(line)).ToArray();
        WriteIfRequested("census-model-witnesses.txt", validWitnesses);

        // The extension and the settlement families run after the grid, so that the grid's outputs and time keep their meaning.
        var extensionClock = Stopwatch.StartNew();
        var (extension, extensionExcluded) = CensusGrid.GenerateExtension();
        var families = CensusGrid.SettlementFamilies();
        var extensionCases = extension.Concat(families).ToArray();
        var extensionResults = await RunAll(extensionCases, collectLean: false, FullParallelism);
        extensionClock.Stop();
        var validExtension = extensionResults.Where(r => r.Skipped is null && r.Case.Kind == "grid").Select(r => r.Case).ToArray();
        var extensionCover = ExtensionCover(valid, validExtension);
        WriteIfRequested("census-extension-subset.txt", extensionCover.Select(c => c.Id).Prepend(ExtensionSubsetHeader));
        var extensionGaps = extensionResults.SelectMany(r => r.Gaps).ToList();
        var widenedTriples = CensusGrid.Triples([.. valid, .. validExtension]).Count;

        var work = RunWork(gaps);
        clock.Stop();

        var excludedCount = excluded.Count;
        var summary = Summary(results).Prepend($"time\tcases {caseTime.TotalSeconds:F1} s\ttotal {clock.Elapsed.TotalSeconds:F1} s")
            .Prepend($"generated\t{all.Count}\texcluded\t{excludedCount}\tfixed\t{CensusGrid.Fixed().Count}")
            .Append($"triples-generated\t{CensusGrid.TripleCount(all)}\ttriples-valid\t{CensusGrid.TripleCount(valid)}\tcover\t{cover.Count}\tcover-triples\t{CensusGrid.TripleCount(cover)}")
            .Append($"work-families\t{work.Count}\tflagged\t{work.Count(w => w.Contains("\tFLAG\t", StringComparison.Ordinal))}")
            .ToArray();
        foreach (var line in summary) output.WriteLine(line);
        WriteIfRequested("full-summary.txt", summary);
        WriteIfRequested("full-gaps.txt", gaps.Select(g => g.Line));
        WriteIfRequested("full-work.txt", work);
        WriteIfRequested("full-observations.txt", Observations(results));
        WriteIfRequested("full-skipped.txt", results.Where(r => r.Skipped is not null).Select(r => $"{r.Case.Id}\t{r.Skipped}"));
        WriteIfRequested("full-excluded.txt", excluded.Select(e => $"{e.Id}\t{e.Reason}"));
        WriteIfRequested("full-impossible.txt", results.SelectMany(r => r.Impossible).Select(g => g.Line));
        WriteIfRequested("full-unsupplied-requirements.txt", Unsupplied(results));

        var extensionSummary = Summary(extensionResults).Prepend($"time\tcases {extensionClock.Elapsed.TotalSeconds:F1} s")
            .Prepend($"generated\t{extension.Count}\texcluded\t{extensionExcluded.Count}\tsettlement-families\t{families.Count}")
            .Append($"triples-widened-valid\t{widenedTriples}\textension-only-triples\t{widenedTriples - CensusGrid.TripleCount(valid)}"
                + $"\tcover\t{extensionCover.Count}\tcover-triples\t{CensusGrid.TripleCount(extensionCover)}")
            .Append($"static-route-twins\t{validExtension.Count(CensusRunner.HasStaticRouteTwin)}")
            .Concat(CensusGrid.ExtensionHeads.Concat(CensusGrid.ExtensionEnds).Select(value =>
                $"valid-with\t{value}\t{validExtension.Count(c => c.Dim("head") == value || c.Dim("end") == value)}"))
            .ToArray();
        foreach (var line in extensionSummary) output.WriteLine("extension " + line);
        WriteIfRequested("full-extension-summary.txt", extensionSummary);
        WriteIfRequested("full-extension-gaps.txt", extensionGaps.Select(g => g.Line));
        WriteIfRequested("full-extension-observations.txt", Observations(extensionResults));
        WriteIfRequested("full-extension-skipped.txt", extensionResults.Where(r => r.Skipped is not null).Select(r => $"{r.Case.Id}\t{r.Skipped}"));
        WriteIfRequested("full-extension-excluded.txt", extensionExcluded.Select(e => $"{e.Id}\t{e.Reason}"));
        WriteIfRequested("full-extension-impossible.txt", extensionResults.SelectMany(r => r.Impossible).Select(g => g.Line));
        WriteIfRequested("full-extension-unsupplied-requirements.txt", Unsupplied(extensionResults));

        Assert.Equal(cover.Select(c => c.Id), Subset().Select(c => c.Id));
        Assert.Equal(validWitnesses, storedWitnesses);
        Assert.Equal(extensionCover.Select(c => c.Id), ExtensionSubset().Select(c => c.Id));
        Assert.Equal(WidenedValidTripleCount, widenedTriples);
        Assert.All(extensionResults.Where(r => r.Case.Kind == "settlement"), r => Assert.Null(r.Skipped));
        AssertMatchesRatchet([.. gaps, .. extensionGaps],
            cases.Concat(extensionCases).Select(c => c.Id).Concat(work.Select(w => w.Split('\t')[0])).ToHashSet(StringComparer.Ordinal),
            new HashSet<string>(CSharpChecks.Append("W"), StringComparer.Ordinal), "full", completeDomain: true);
        Assert.Equal(ImpossibleObservationsInFull, results.Sum(r => r.Impossible.Count));
        Assert.Equal(ExtensionImpossibleObservationsInFull, extensionResults.Sum(r => r.Impossible.Count));
        Assert.Empty(Unsupplied(results));
        Assert.Empty(Unsupplied(extensionResults));
    }

    // ── Twins: a block-headed reference resolves like a named one (owner decision Q3, 2026-11-14) ─────

    /// <summary>What the twin comparison reads of one case: diagnostics, inferred signatures and outcomes.</summary>
    private static List<string> TwinFacts(CensusCase @case)
    {
        var facts = new List<string>();
        var rows = new List<(string Label, string Row)> { ("in5", CensusRunner.Inside5), ("in7", CensusRunner.Inside7), ("same", CensusRunner.SameRun) };
        rows.AddRange(@case.Readers.Select(reader => ($"esc:{reader.Label}", reader.Escaped)));
        foreach (var (label, row) in rows)
        {
            var source = @case.Body + row + "\n";
            var parsed = Parser.Parse(source);
            if (parsed.HasErrors)
            {
                facts.Add($"{label} diagnostics: " + string.Join(",", parsed.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error)
                    .Select(d => d.Code.ToString()).Distinct().Order(StringComparer.Ordinal)));
                continue;
            }

            if (label == "in5")
            {
                var model = KatLang.Semantics.SemanticModelBuilder.Build(parsed);
                // The declarations a block-headed program and its declared copy both write (the copy adds only the
                // literal's name, CensusGrid.DeclaredCopy).
                foreach (var name in new[] { "F", "L", "A", "K", "B", "D", "N" })
                    facts.Add($"signature {name}: " + string.Join(" / ", model.FindProperties(name).Select(p => p.DisplaySignature)));
            }

            facts.Add($"{label} outcome: " + CensusRunner.Render(Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root))));
        }

        return facts;
    }

    /// <summary>
    /// Every given block-headed cell against its declared copy (<see cref="CensusGrid.DeclaredCopy"/>): the pairs
    /// whose twin facts differ, each with its differing facts. Q3 admits no difference, so there is no exemption: a
    /// cell is equal to its copy or it is listed. A cell without a declared copy throws; none is skipped.
    /// </summary>
    private static List<string> DeclaredCopyDifferences(IReadOnlyList<CensusCase> cells, int parallelism)
    {
        var details = new string?[cells.Count];
        Parallel.For(0, cells.Count, new ParallelOptions { MaxDegreeOfParallelism = parallelism }, i =>
        {
            var (cell, copy) = (TwinFacts(cells[i]), TwinFacts(CensusGrid.DeclaredCopy(cells[i])));
            if (cell.SequenceEqual(copy, StringComparer.Ordinal)) return;
            var detail = string.Join(" ; ", cell.Zip(copy).Where(pair => pair.First != pair.Second).Select(pair => $"{pair.First} <> {pair.Second}"));
            details[i] = cell.Count == copy.Count ? detail : $"fact counts {cell.Count} <> {copy.Count} ; {detail}";
        });
        return Enumerable.Range(0, cells.Count).Where(i => details[i] is not null).Select(i => $"{cells[i].Id}\t{details[i]}").ToList();
    }

    private static string[] TwinSummary(int pairs, int differ) => [$"pairs\t{pairs}", $"equal\t{pairs - differ}", $"differ\t{differ}"];

    /// <summary>
    /// <c>twins</c> mode: every generated <c>blockref</c> cell, valid or not, against its declared copy (owner
    /// decision D2, 2026-11-15). The two programs differ only in how <c>L</c>'s target is headed, so the error
    /// diagnostics of each probe, the signatures of the declarations both write and every probe outcome must be
    /// equal. Every differing pair is written out with its differing facts, and any one fails the run.
    /// </summary>
    [Fact]
    public void TwinsMode_BlockHeadedReferencesMatchTheirDeclaredCopies()
    {
        if (Mode != "twins") return;
        var (all, _) = CensusGrid.Generate();
        var cells = all.Where(c => c.Dim("head") == "blockref").ToArray();
        var differences = DeclaredCopyDifferences(cells, FullParallelism);
        var summary = TwinSummary(cells.Length, differences.Count);
        WriteIfRequested("twins-differences.txt", differences);
        WriteIfRequested("twins-summary.txt", summary);
        output.WriteLine(string.Join("; ", summary).Replace('\t', ' '));
        Assert.NotEmpty(cells);
        Assert.True(differences.Count == 0,
            $"Block-headed cells that differ from their declared copies ({differences.Count} of {cells.Length}):\n" + string.Join("\n", differences.Take(40)));
    }

    /// <summary>
    /// The default suite's share of the twin comparison, so that CI keeps Q3's equality: every <c>blockref</c> cell
    /// of the stored cover equals its declared copy. The <c>twins</c> mode compares the whole generated grid.
    /// </summary>
    [Fact]
    public void DefaultSubset_BlockHeadedReferencesMatchTheirDeclaredCopies()
    {
        var clock = Stopwatch.StartNew();
        var cells = Subset().Where(c => c.Dim("head") == "blockref").ToArray();
        var differences = DeclaredCopyDifferences(cells, parallelism: 1);
        var summary = TwinSummary(cells.Length, differences.Count);
        output.WriteLine($"{string.Join("; ", summary).Replace('\t', ' ')}; {clock.Elapsed.TotalSeconds:F1} s");
        WriteIfRequested("default-twins-differences.txt", differences);
        WriteIfRequested("default-twins-summary.txt", summary);
        Assert.NotEmpty(cells);
        Assert.True(differences.Count == 0,
            $"Block-headed cells of the stored cover that differ from their declared copies ({differences.Count} of {cells.Length}):\n"
            + string.Join("\n", differences.Take(40)));
    }

    // ── Model check (Lean, outside the canonical targets) ────────────────────────────────────────────

    [Fact]
    public async Task EmitLean_WritesTheEncodingBatches()
    {
        if (Mode != "emit-lean") return;
        var results = await RunAll(ModelCases(), collectLean: true, FullParallelism);
        Assert.All(results, result => Assert.Null(result.Skipped));
        var items = results.SelectMany(r => r.Lean).ToList();
        var batches = CensusLean.Emit(items, OutDirectory);
        output.WriteLine($"{items.Count} encodings in {batches} batches ({results.Count(r => r.Skipped is null)} valid cases)");
    }

    [Fact]
    public async Task CheckLean_ModelGapsEqualTheRatchet()
    {
        if (Mode != "check-lean") return;
        var results = await RunAll(ModelCases(), collectLean: true, FullParallelism);
        Assert.All(results, result => Assert.Null(result.Skipped));
        var gaps = CensusLean.Check(OutDirectory, results.SelectMany(result => result.Lean).ToArray());
        WriteIfRequested("lean-gaps.txt", gaps.Select(g => g.Line));
        foreach (var group in gaps.GroupBy(g => $"{g.Check}\t{g.Class}").OrderBy(g => g.Key, StringComparer.Ordinal))
            output.WriteLine($"{group.Key}\t{group.Count()}");
        var ids = File.ReadLines(Path.Combine(OutDirectory, "manifest.tsv")).Select(l => l.Split('\t')[1]).ToHashSet(StringComparer.Ordinal);
        AssertMatchesRatchet(gaps, ids, new HashSet<string>(["M", "M1", "M2", "M3", "M4"], StringComparer.Ordinal), "lean", completeDomain: true);
    }

    // ── HEAD a4b545e8 comparison ────────────────────────────────────────────────────────────────────

    [Fact]
    public void EmitHead_WritesEveryProbeProgram()
    {
        if (Mode != "emit-head") return;
        var lines = HeadPrograms();
        Directory.CreateDirectory(OutDirectory);
        File.WriteAllLines(Path.Combine(OutDirectory, "head-programs.tsv"), lines);
        // Parsing the HEAD input inventory already identifies the valid grid. Publish its cover as
        // an ignored bootstrap artifact, so the default time budget can be checked before full mode.
        var validIds = lines.Select(line => line[..line.IndexOf('\t')]).ToHashSet(StringComparer.Ordinal);
        var (all, _) = CensusGrid.Generate();
        var valid = all.Where(@case => validIds.Contains(@case.Id)).ToArray();
        var cover = CensusGrid.ThreeWayCover(valid);
        File.WriteAllLines(Path.Combine(OutDirectory, "census-subset.txt"), cover.Select(@case => @case.Id));
        var (extension, _) = CensusGrid.GenerateExtension();
        var validExtension = extension.Where(@case => validIds.Contains(@case.Id)).ToArray();
        var extensionCover = ExtensionCover(valid, validExtension);
        File.WriteAllLines(Path.Combine(OutDirectory, "census-extension-subset.txt"), extensionCover.Select(@case => @case.Id).Prepend(ExtensionSubsetHeader));
        var gridProbes = lines.Count(line => !IsExtensionProgram(line));
        File.WriteAllText(Path.Combine(OutDirectory, "coverage.txt"),
            $"valid-grid={valid.Length}; triples={CensusGrid.TripleCount(valid)}; cover={cover.Count}; probes={gridProbes}\n"
            + $"valid-extension={validExtension.Length}; widened-triples={CensusGrid.Triples([.. valid, .. validExtension]).Count}; "
            + $"extension-cover={extensionCover.Count}; settlement-families={CensusGrid.SettlementFamilies().Count}; probes={lines.Count - gridProbes}\n");
        // The HEAD probe's scratch project (it compiles this folder's CensusHeadProbe.cs) and the commands that run it.
        CensusHeadProbe.WriteProject(Path.Combine(OutDirectory, "head-probe"), HeadProbeSourcePath);
        File.WriteAllLines(Path.Combine(OutDirectory, "head-probe-steps.txt"), CensusHeadProbe.Steps(OutDirectory));
        output.WriteLine($"{lines.Count} probe programs ({gridProbes} of the grid and the fixed cases)");
    }

    internal static string HeadProbeSourcePath => Path.Combine(RepoRoot.Find(), "tests", "KatLang.Tests", "ExposureCensus", "CensusHeadProbe.cs");

    /// <summary>
    /// Every probe program of every valid case, in the order the HEAD probe's output follows: the grid and the fixed cases
    /// (the inventory of earlier runs, unchanged), then the extension and the settlement families.
    /// </summary>
    private static List<string> HeadPrograms()
    {
        var (all, _) = CensusGrid.Generate();
        var (extension, _) = CensusGrid.GenerateExtension();
        return all.Concat(CensusGrid.Fixed()).Concat(extension).Concat(CensusGrid.SettlementFamilies())
            .SelectMany(@case => CensusRunner.Probes(@case) is { } probes
                ? probes.Select(p => $"{@case.Id}\t{p.Label}\t{p.Source.Replace("\n", "\\n")}") : []).ToList();
    }

    // A settlement family, or a grid id whose head or ending is an extension value (read from the id; no program is built).
    private static bool IsExtensionId(string id)
    {
        if (id.StartsWith("settlement=", StringComparison.Ordinal)) return true;
        var parts = id.Split('|');
        return parts.Length == CensusGrid.DimensionNames.Length && parts[0].StartsWith("head=", StringComparison.Ordinal)
            && parts[5].StartsWith("end=", StringComparison.Ordinal) && CensusGrid.IsExtension(parts[0]["head=".Length..], parts[5]["end=".Length..]);
    }

    private static bool IsExtensionProgram(string line) => IsExtensionId(line[..line.IndexOf('\t')]);

    /// <summary>
    /// Reads the HEAD probe's output: per program, the metadata of every non-exported declaration and the
    /// outcome. Classifies every over-charge of the ratchet (inherited when HEAD charged the same requirement
    /// of the same declaration) and runs the HEAD self-checks (U flags R2, S1 and the enclosing-level open). It also
    /// compares the INSIDE outcomes of every valid case with HEAD's: an inside probe that succeeded on HEAD and fails
    /// now is a gap (<c>regression-vs-head</c>); the opposite direction and a changed value are report-only lists. The
    /// grid's and the fixed cases' lists keep their names; the extension's and the settlement families' are
    /// <c>head-extension-*.txt</c>.
    /// </summary>
    [Fact]
    public void CheckHead_ClassifiesOverChargesAndRunsTheHeadSelfChecks()
    {
        if (Mode != "check-head") return;
        var programs = HeadPrograms();
        Assert.Equal(programs, File.ReadAllLines(Path.Combine(OutDirectory, "head-programs.tsv")));
        var head = HeadOutput.Read(Path.Combine(OutDirectory, "head.out"));
        head.RequireComplete(programs.Select(p => p.Split('\t')).Select(p => (p[0], p[1])).ToArray());
        var (all, _) = CensusGrid.Generate();
        var (extension, _) = CensusGrid.GenerateExtension();
        var cases = all.Concat(CensusGrid.Fixed()).Concat(extension).Concat(CensusGrid.SettlementFamilies()).ToDictionary(c => c.Id, StringComparer.Ordinal);

        var report = new List<string>();
        var mismatched = new List<string>();
        foreach (var gap in ReadRatchet().Where(g => g.Check == "O" && g.Class.StartsWith("over-charge", StringComparison.Ordinal)))
        {
            var reader = cases[gap.Id].Readers.Single(r => r.Label == gap.Reader);
            var path = "root." + string.Join(".", reader.Path);
            var requirement = gap.Detail["r=".Length..];
            var inherited = head.Metadata(gap.Id, "in5").TryGetValue(path, out var described)
                && described[(described.IndexOf('[') + 1)..].TrimEnd(']').Split(',').Contains(requirement, StringComparer.Ordinal);
            var expected = inherited ? "over-charge-inherited" : "over-charge-new";
            report.Add($"{gap.Id}\t{gap.Reader}\t{gap.Detail}\tHEAD {described ?? "exported"}\t{expected}");
            if (gap.Class != expected) mismatched.Add($"{gap.Line} -> {expected}");
        }

        var headGaps = new List<string>();
        var engineGaps = new List<string>();
        foreach (var id in head.CaseIds)
        {
            var @case = cases[id];
            var o = head.Outcomes(id);
            foreach (var label in new[] { "in5", "in7", "same" }.Concat(@case.Readers.Select(r => $"esc:{r.Label}")))
                if (o[label] != o[label + ":async"] || o[label] != o[label + ":forced"])
                    engineGaps.Add($"E\tengine-disagreement-head\t{id}\t-\t{label}: {o[label]}; async={o[label + ":async"]}; forced={o[label + ":forced"]}");
            if (!o.TryGetValue("in5", out var five) || !o.TryGetValue("in7", out var seven) || !o.TryGetValue("same", out var same)) continue;
            if (five.StartsWith("OK ", StringComparison.Ordinal) && seven.StartsWith("OK ", StringComparison.Ordinal)
                && same.StartsWith("OK ", StringComparison.Ordinal) && same != $"OK S[{five[3..]}, {seven[3..]}]")
                headGaps.Add($"U\tunder-charge-wrong-value\t{id}\t-\tsame={same}; separate={five} / {seven}");
            foreach (var reader in @case.Readers)
            {
                var path = "root." + string.Join(".", reader.Path);
                if (head.Metadata(id, "in5").ContainsKey(path)) continue;
                if (o.TryGetValue($"esc:{reader.Label}", out var escaped) && escaped.StartsWith("FAIL LocalOnlyProperty", StringComparison.Ordinal))
                    headGaps.Add($"U\tunder-charge-masked-access\t{id}\t{reader.Label}\t{escaped}");
            }
        }
        // The grid's and the fixed cases' lists keep the names and contents of earlier runs; the extension's are head-extension-*.
        void WriteSplit(string name, IReadOnlyList<string> lines, int idColumn)
        {
            WriteIfRequested($"head-{name}.txt", lines.Where(line => !IsExtensionId(line.Split('\t')[idColumn])));
            WriteIfRequested($"head-extension-{name}.txt", lines.Where(line => IsExtensionId(line.Split('\t')[idColumn])));
        }
        WriteSplit("overcharge-classes", report, 0);
        WriteSplit("gaps", headGaps, 2);
        WriteSplit("engine-gaps", engineGaps, 2);

        // Inside outcomes, HEAD against now (the synchronous route on both sides; full mode checks the others).
        var compared = head.CaseIds.Order(StringComparer.Ordinal).Select(id => cases[id]).ToArray();
        var now = new IReadOnlyList<(string Label, string Outcome)>?[compared.Length];
        Parallel.For(0, compared.Length, new ParallelOptions { MaxDegreeOfParallelism = FullParallelism },
            i => now[i] = CensusRunner.InsideOutcomes(compared[i]));
        var regressions = new List<string>();
        var revived = new List<string>();
        var valueChanges = new List<string>();
        for (var i = 0; i < compared.Length; i++)
        {
            var id = compared[i].Id;
            var before = head.Outcomes(id);
            foreach (var (label, current) in now[i] ?? throw new InvalidDataException($"A HEAD case no longer parses cleanly: {id}"))
            {
                var headOutcome = before[label];
                var headWorked = headOutcome.StartsWith("OK ", StringComparison.Ordinal);
                var worksNow = current.StartsWith("ok ", StringComparison.Ordinal);
                if (headWorked && !worksNow)
                    regressions.Add($"E\tregression-vs-head\t{id}\t-\t{label}: HEAD={headOutcome}; now={current}");
                else if (!headWorked && worksNow)
                    revived.Add($"{id}\t{label}\tHEAD={headOutcome}\tnow={current}");
                else if (headWorked && worksNow && headOutcome[3..] != current[3..])
                    valueChanges.Add($"{id}\t{label}\tHEAD={headOutcome}\tnow={current}");
            }
        }
        WriteSplit("regressions", regressions, 2);
        WriteSplit("revived", revived, 0);
        WriteSplit("value-changes", valueChanges, 0);
        var regressedCases = regressions.Select(line => line.Split('\t')[2]).Distinct(StringComparer.Ordinal).Count();
        foreach (var (scope, inScope) in new (string, Func<string, bool>)[] { ("grid", id => !IsExtensionId(id)), ("extension", IsExtensionId) })
        {
            int Count(IEnumerable<string> lines, int idColumn) => lines.Count(line => inScope(line.Split('\t')[idColumn]));
            output.WriteLine($"{scope}: cases {head.CaseIds.Count(inScope)}; inside outcomes: regressions {Count(regressions, 2)}; "
                + $"failed on HEAD and succeed now {Count(revived, 0)}; value changes {Count(valueChanges, 0)}; "
                + $"HEAD U gaps {Count(headGaps, 2)}; HEAD engine gaps {Count(engineGaps, 2)}");
        }
        output.WriteLine($"inside outcomes: regressions {regressions.Count} in {regressedCases} cases; "
            + $"failed on HEAD and succeed now {revived.Count}; value changes {valueChanges.Count}");
        output.WriteLine($"over-charges classified {report.Count}; mismatched tags {mismatched.Count}; HEAD U gaps {headGaps.Count}");

        Assert.Contains(headGaps, g => g.Contains("\thead=ref1|pos=value|open=none|reader=plain|place=outside|end=found|req=container\tA\t", StringComparison.Ordinal));
        Assert.Contains(headGaps, g => g.StartsWith("U\tunder-charge-wrong-value\tselfcheck=S1-audit-inline-block", StringComparison.Ordinal));
        Assert.Contains(headGaps, g => g.Contains("\thead=name|pos=open|open=enc1-used|reader=plain|place=outside|end=found|req=container\tA\t", StringComparison.Ordinal));
        Assert.True(mismatched.Count == 0, "Over-charge tags differ from HEAD's metadata:\n" + string.Join("\n", mismatched.Take(40)));
        Assert.True(regressions.Count == 0,
            $"Inside probes that succeeded on HEAD a4b545e8 fail now ({regressions.Count} outcomes in {regressedCases} cases):\n"
            + string.Join("\n", regressions.Take(40)));
    }

    /// <summary>
    /// The HEAD probe's output, <c>head.out</c>: tab-separated lines <c>id \t probe \t META|OUT \t text</c>, written by
    /// <see cref="CensusHeadProbe.RunAsync"/> (tracked in this folder; <c>emit-head</c> writes its scratch project and the
    /// commands, <see cref="CensusHeadProbe.Steps"/>). THE PROTOCOL:
    /// <list type="bullet">
    /// <item><c>META</c> (probe <c>in5</c> only): <c>root.&lt;path&gt;: &lt;Exposure&gt;[name@depth,...]</c>, one per non-exported
    /// declaration reachable through property values; a missing path is an exported declaration, a duplicate path is
    /// rejected.</item>
    /// <item><c>OUT</c>: the outcome of every probe on the three routes, as the probes <c>&lt;probe&gt;</c> (synchronous),
    /// <c>&lt;probe&gt;:async</c> and <c>&lt;probe&gt;:forced</c>, each <c>OK &lt;neutral&gt;</c>, <c>FAIL &lt;Error&gt;[:subject]</c>,
    /// <c>PARSE &lt;codes&gt;</c> or <c>EXCEPTION &lt;type&gt;</c>; <see cref="RequireComplete"/> demands all three for every
    /// program of <c>head-programs.tsv</c> and nothing else, and a duplicate is rejected.</item>
    /// </list>
    /// Lines with fewer than four fields are ignored; any other kind is ignored too.
    /// </summary>
    internal sealed class HeadOutput
    {
        private readonly Dictionary<(string, string), Dictionary<string, string>> _metadata = new();
        private readonly Dictionary<string, Dictionary<string, string>> _outcomes = new(StringComparer.Ordinal);

        public IEnumerable<string> CaseIds => _outcomes.Keys;

        public Dictionary<string, string> Metadata(string id, string probe)
            => _metadata.TryGetValue((id, probe), out var map) ? map : new Dictionary<string, string>(StringComparer.Ordinal);

        public Dictionary<string, string> Outcomes(string id) => _outcomes[id];

        public void RequireComplete(IReadOnlyList<(string Id, string Probe)> programs)
        {
            var expected = programs.SelectMany(p => new[] { (p.Id, p.Probe), (p.Id, p.Probe + ":async"), (p.Id, p.Probe + ":forced") })
                .ToHashSet();
            var actual = _outcomes.SelectMany(entry => entry.Value.Keys.Select(probe => (entry.Key, probe))).ToHashSet();
            if (programs.Count == 0 || !expected.SetEquals(actual))
                throw new InvalidDataException("HEAD output is incomplete or contains unexpected probes; require every program on all three routes.");
        }

        public static HeadOutput Read(string path)
        {
            var head = new HeadOutput();
            foreach (var line in File.ReadLines(path))
            {
                var parts = line.Split('\t', 4);
                if (parts.Length != 4) continue;
                var (id, probe, kind, text) = (parts[0], parts[1], parts[2], parts[3]);
                if (kind == "META")
                {
                    var colon = text.IndexOf(": ", StringComparison.Ordinal);
                    if (colon < 1) throw new InvalidDataException($"Malformed HEAD metadata: {line}");
                    if (!head._metadata.TryGetValue((id, probe), out var map)) head._metadata[(id, probe)] = map = new(StringComparer.Ordinal);
                    if (!map.TryAdd(text[..colon], text[(colon + 2)..])) throw new InvalidDataException($"Duplicate HEAD metadata: {line}");
                }
                else if (kind == "OUT")
                {
                    if (!head._outcomes.TryGetValue(id, out var map)) head._outcomes[id] = map = new(StringComparer.Ordinal);
                    if (!map.TryAdd(probe, text)) throw new InvalidDataException($"Duplicate HEAD outcome: {line}");
                }
            }
            return head;
        }
    }
}
