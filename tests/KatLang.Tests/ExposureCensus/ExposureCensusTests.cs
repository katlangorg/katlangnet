using System.Diagnostics;
using System.Text;
using Xunit.Abstractions;

namespace KatLang.Tests.ExposureCensus;

/// <summary>
/// The E-18 route census (discovery, 2026-11-14): programs generated over the whole route space of a
/// static selection inside <c>F(y)</c> (<see cref="CensusGrid"/>), checked mechanically for the two
/// properties under test — exposure is exact (U: under-charge, O: over-charge, W: work) and the model
/// refuses exactly the under-declared trees (M, through Lean, outside the canonical targets).
///
/// <para>The census FIXES NOTHING. Every gap it finds is listed in <c>census-gaps.txt</c> (the ratchet):
/// the default test computes the gaps of its deterministic 3-way subset and requires them to equal the
/// list restricted to that subset, so a new gap fails it and so does a listed gap that no longer occurs.
/// The fix run takes the ratchet as its acceptance test.</para>
///
/// <para>Modes (<c>KATLANG_EXPOSURE_CENSUS</c>; output directory <c>KATLANG_EXPOSURE_CENSUS_OUT</c>):
/// <c>full</c> — every valid case and every work family, compared with the whole list;
/// <c>emit-lean</c> — writes the encodings (3-way subset) as Lean batch files for <c>lake env lean</c>;
/// <c>check-lean</c> — reads the batch outputs and compares M1–M4 with the list;
/// <c>emit-head</c> — writes every valid case's probe programs for the HEAD a4b545e8 probe;
/// <c>check-head</c> — reads that probe's output (<c>head.out</c>), classifies over-charges as inherited or
/// new and runs the HEAD self-checks. Without the variable only the default subset runs.</para>
/// </summary>
public sealed class ExposureCensusTests(ITestOutputHelper output)
{
    private const string ModeVariable = "KATLANG_EXPOSURE_CENSUS";
    private const string OutVariable = "KATLANG_EXPOSURE_CENSUS_OUT";
    // Full mode independently recomputes the valid universe and its cover. Pin its observed triple
    // count here too, so dropping a subset entry cannot silently shrink default-suite coverage.
    private const int ValidTripleCount = 5577;

    private static string? Mode => Environment.GetEnvironmentVariable(ModeVariable) is { Length: > 0 } mode ? mode : null;

    private static string OutDirectory
        => Environment.GetEnvironmentVariable(OutVariable) is { Length: > 0 } path
            ? path
            : throw new InvalidOperationException($"{OutVariable} must name an output directory for census mode {Mode}.");

    private static string RatchetPath => Path.Combine(RepoRoot.Find(), "tests", "KatLang.Tests", "ExposureCensus", "census-gaps.txt");

    // C#-side checks the default and full modes compute; M lines belong to check-lean.
    private static readonly HashSet<string> CSharpChecks = new(StringComparer.Ordinal) { "U", "O", "E", "H" };

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

    // Keep known model findings sampled when an expanded grid chooses a different greedy cover.
    // These stable witnesses remain after the corresponding ratchet entry is fixed and removed.
    private static IReadOnlyList<CensusCase> ModelCases()
        => Subset().Concat(CensusGrid.Fixed()).Concat(File.ReadLines(Path.Combine(RepoRoot.Find(), "tests", "KatLang.Tests",
                "ExposureCensus", "census-model-witnesses.txt")).Where(line => line.Length > 0 && !line.StartsWith('#'))
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
        foreach (var group in results.SelectMany(r => r.Gaps).GroupBy(g => $"{g.Check}\t{g.Class}").OrderBy(g => g.Key, StringComparer.Ordinal))
            yield return $"gaps\t{group.Key}\t{group.Count()}";
    }

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

        // Generation is total over the subset: a case that does not parse is a skip, never a silent drop.
        Assert.Equal(cases.Length, results.Count);
        AssertMatchesRatchet(results.SelectMany(r => r.Gaps).ToList(), cases.Select(c => c.Id).ToHashSet(StringComparer.Ordinal), CSharpChecks, "default subset");
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

        var prefix = await CensusRunner.Run(fixedCases["selfcheck=static-prefix-runtime-open"], collectLean: true);
        Assert.Equal("LocalOnlyCapturedAncestorParameters[y@0]", prefix.Metadata["A"]);
        Assert.Contains(prefix.Lean, item => item.Role == "copy-needed");
        Assert.Contains(ReadRatchet(), g => g is { Check: "M2", Id: "selfcheck=static-prefix-runtime-open" });

        foreach (var family in new[] { CensusWork.BoxSelfCheck(), CensusWork.DischargeSelfCheck() })
        {
            var measured = CensusWork.Measure(family);
            output.WriteLine($"{family.Id}: frames {string.Join(" / ", measured.Frames)}; checkpoints {string.Join(" / ", measured.Checkpoints)}");
            Assert.False(measured.WithinBound);
            Assert.Contains(ReadRatchet(), g => g.Check == "W" && g.Id == family.Id);
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

        Assert.Equal(cover.Select(c => c.Id), Subset().Select(c => c.Id));
        AssertMatchesRatchet(gaps, cases.Select(c => c.Id).Concat(work.Select(w => w.Split('\t')[0])).ToHashSet(StringComparer.Ordinal),
            new HashSet<string>(CSharpChecks.Append("W"), StringComparer.Ordinal), "full", completeDomain: true);
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
        File.WriteAllText(Path.Combine(OutDirectory, "coverage.txt"),
            $"valid-grid={valid.Length}; triples={CensusGrid.TripleCount(valid)}; cover={cover.Count}; probes={lines.Count}\n");
        output.WriteLine($"{lines.Count} probe programs");
    }

    private static List<string> HeadPrograms()
    {
        var (all, _) = CensusGrid.Generate();
        return all.Concat(CensusGrid.Fixed()).SelectMany(@case => CensusRunner.Probes(@case) is { } probes
            ? probes.Select(p => $"{@case.Id}\t{p.Label}\t{p.Source.Replace("\n", "\\n")}") : []).ToList();
    }

    /// <summary>
    /// Reads the HEAD probe's output: per program, the metadata of every non-exported declaration and the
    /// outcome. Classifies every over-charge of the ratchet (inherited when HEAD charged the same requirement
    /// of the same declaration) and runs the HEAD self-checks (U flags R2, S1 and the enclosing-level open).
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
        var cases = all.Concat(CensusGrid.Fixed()).ToDictionary(c => c.Id, StringComparer.Ordinal);

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
        WriteIfRequested("head-overcharge-classes.txt", report);
        WriteIfRequested("head-gaps.txt", headGaps);
        WriteIfRequested("head-engine-gaps.txt", engineGaps);
        output.WriteLine($"over-charges classified {report.Count}; mismatched tags {mismatched.Count}; HEAD U gaps {headGaps.Count}");

        Assert.Contains(headGaps, g => g.Contains("\thead=ref1|pos=value|open=none|reader=plain|place=outside|end=found|req=container\tA\t", StringComparison.Ordinal));
        Assert.Contains(headGaps, g => g.StartsWith("U\tunder-charge-wrong-value\tselfcheck=S1-audit-inline-block", StringComparison.Ordinal));
        Assert.Contains(headGaps, g => g.Contains("\thead=name|pos=open|open=enc1-used|reader=plain|place=outside|end=found|req=container\tA\t", StringComparison.Ordinal));
        Assert.True(mismatched.Count == 0, "Over-charge tags differ from HEAD's metadata:\n" + string.Join("\n", mismatched.Take(40)));
    }

    /// <summary>The HEAD probe's output format: <c>id \t probe \t META|OUT \t text</c>.</summary>
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
