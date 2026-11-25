using static KatLang.Tests.LanguageSpec.ExposureShapeSpecFamily;

namespace KatLang.Tests.LanguageSpec;

/// <summary>
/// THE DEFERRED-BRANCH ROUTE of the exposure-shape matrix (EXPORTED-DETACHED follow-up, November
/// 2026): the async, C#-only companion of <see cref="ExposureShapeSpecFamily"/>. Every program of
/// <see cref="ExposureShapeSpecFamily.DeferredCells"/> — a container, a capture position, a
/// placement, a variant and a root-row order — runs through <see cref="KatLangEngine.RunAsync"/>
/// with an in-memory downloader that counts its calls, and must give its HAND-WRITTEN outcome and
/// download count.
/// <para>The sources are generated (<see cref="ExposureShapeSpecFamily.DeferredProgram"/>,
/// <see cref="ExposureShapeSpecFamily.DeferredModules"/>); the expectations are the reviewed table
/// and are never taken from a run. Each cell shows a SELECTED materialization (the module is
/// downloaded, the unit compiled and judged), its EAGER TWIN (nothing deferred: the oracle of an
/// accepted shape) and a NEVER-SELECTED control (no download, no module work, no judgement). The
/// coverage checks below keep the cross product complete: no container, capture position,
/// placement, variant or row order can be dropped unnoticed.</para>
/// <para>Lean has no deferred-region model, so this suite has no Lean counterpart; the four-route
/// family in the spec corpus stays the Lean-comparable part of the matrix.</para>
/// </summary>
public class ExposureShapeDeferredRouteTests
{
    /// <summary>The in-memory module host of one run: the companion's generated modules and a download count per URL.</summary>
    private sealed class ModuleHost
    {
        private static readonly IReadOnlyDictionary<string, string> Modules = DeferredModules();

        public Dictionary<string, int> Fetches { get; } = new(StringComparer.Ordinal);

        public int TotalFetches => Fetches.Values.Sum();

        public RunOptions Options => new()
        {
            AllowedHosts = [DeferredModuleHost],
            DownloadCode = (url, _) =>
            {
                lock (Fetches)
                    Fetches[url] = Fetches.GetValueOrDefault(url) + 1;
                var name = url[$"https://{DeferredModuleHost}/".Length..^".kat".Length];
                return Modules.TryGetValue(name, out var source)
                    ? ValueTask.FromResult(source)
                    : throw new InvalidOperationException($"404: {url}");
            },
        };
    }

    private static readonly (string Name, string Rows)[] RowPrograms =
    [
        ("inside", InsideRows),
        ("outside-after-call", OutsideAfterCall),
        ("outside-before-call", OutsideBeforeCall),
    ];

    private static readonly DeferredVariant[] Variants =
        [DeferredVariant.Selected, DeferredVariant.EagerTwin, DeferredVariant.NeverSelected];

    private static string VariantSlug(DeferredVariant variant) => variant switch
    {
        DeferredVariant.Selected => "selected",
        DeferredVariant.EagerTwin => "eager-twin",
        DeferredVariant.NeverSelected => "never-selected",
        _ => throw new InvalidOperationException(variant.ToString()),
    };

    private static RowOutcomes Outcomes(DeferredCell cell, DeferredVariant variant) => variant switch
    {
        DeferredVariant.Selected => cell.Selected,
        DeferredVariant.EagerTwin => cell.EagerTwin,
        DeferredVariant.NeverSelected => cell.NeverSelected,
        _ => throw new InvalidOperationException(variant.ToString()),
    };

    private static Expected ExpectedOf(RowOutcomes outcomes, string rowProgram) => rowProgram switch
    {
        "inside" => outcomes.Inside,
        "outside-after-call" => outcomes.OutsideAfterCall,
        "outside-before-call" => outcomes.OutsideBeforeCall,
        _ => throw new InvalidOperationException(rowProgram),
    };

    /// <summary>One id per program of the matrix: cell, variant, row order.</summary>
    public static TheoryData<string> ProgramIds()
    {
        var data = new TheoryData<string>();
        foreach (var id in AllProgramIds())
            data.Add(id);
        return data;
    }

    private static List<string> AllProgramIds()
    {
        var ids = new List<string>();
        foreach (var cell in DeferredCells)
        {
            foreach (var variant in Variants)
            {
                foreach (var (name, _) in RowPrograms)
                    ids.Add($"{DeferredSlug(cell)}/{VariantSlug(variant)}/{name}");
            }
        }

        return ids;
    }

    private static (DeferredCell Cell, DeferredVariant Variant, string RowName, string Rows) Locate(string id)
    {
        var parts = id.Split('/');
        var cell = Assert.Single(DeferredCells, candidate => DeferredSlug(candidate) == parts[0]);
        var variant = Assert.Single(Variants, candidate => VariantSlug(candidate) == parts[1]);
        var (name, rows) = Assert.Single(RowPrograms, candidate => candidate.Name == parts[2]);
        return (cell, variant, name, rows);
    }

    /// <summary>A run's observable outcome: its atoms, or its error codes.</summary>
    private static string DeferredOutcomeOf(RunResult result) => result switch
    {
        RunResult.Success success => "ok " + string.Join(", ", success.Atoms),
        RunResult.EvalFailure failure => "error " + string.Join(",", failure.Errors.Select(error => error.Code)),
        RunResult.ParseFailure failure => "parse-error " + string.Join(",", failure.Errors.Select(error => error.Code)),
        _ => result.GetType().Name,
    };

    [Theory]
    [MemberData(nameof(ProgramIds))]
    public async Task DeferredRouteProgram_HasItsHandWrittenOutcome_AndDownloadCount(string id)
    {
        var (cell, variant, rowName, rows) = Locate(id);
        var source = DeferredProgram(cell, variant, rows);
        var expected = ExpectedOf(Outcomes(cell, variant), rowName);

        // A source-based test parses cleanly first: a deferred branch is never judged by the parse,
        // so the refused shapes are legal source too.
        var parsed = await SourceProvenance.ParseValidAsync(source, new ModuleHost().Options);
        Assert.DoesNotContain(parsed.Diagnostics, diagnostic => diagnostic.Severity == DiagnosticSeverity.Error);

        var host = new ModuleHost();
        var result = await KatLangEngine.RunAsync(source, host.Options);

        Assert.True(expected.Outcome == DeferredOutcomeOf(result),
            $"{id}: expected {expected.Outcome}, was {DeferredOutcomeOf(result)}\n{source}");
        Assert.True(expected.Downloads == host.TotalFetches,
            $"{id}: expected {expected.Downloads} download(s), was {host.TotalFetches}\n{source}");
        // Only the cell's own module is ever requested.
        Assert.All(host.Fetches.Keys, url => Assert.Equal(DeferredModuleUrl(DeferredModuleName(cell)), url));
    }

    /// <summary>
    /// A refused materialization is the STRUCTURED refusal: one error, the dedicated code, no resource
    /// limit, naming the enclosing parameter and the explicit repair.
    /// </summary>
    [Fact]
    public async Task InadmissibleShapes_AreTheStructuredForwardingRefusal()
    {
        var refused = DeferredCells.Where(cell => cell.Selected.Inside.Outcome == DeferredForwardingRefused).ToArray();
        Assert.NotEmpty(refused);

        foreach (var cell in refused)
        {
            var host = new ModuleHost();
            var result = await KatLangEngine.RunAsync(DeferredProgram(cell, DeferredVariant.Selected, InsideRows), host.Options);

            var failure = Assert.IsType<RunResult.EvalFailure>(result);
            var error = Assert.Single(failure.Errors);
            Assert.Equal(KatLangErrorCode.DeferredBranchForwardsEnclosingParameter, error.Code);
            Assert.False(error.IsResourceLimit);
            Assert.Contains("the enclosing parameter 'y'", error.Message, StringComparison.Ordinal);
            Assert.Contains("(y)", error.Message, StringComparison.Ordinal);
            Assert.NotNull(error.Span);
        }
    }

    /// <summary>Every module text of the companion is legal source on its own.</summary>
    [Fact]
    public void GeneratedModules_ParseCleanly()
    {
        var modules = DeferredModules();

        Assert.Equal(1 + DeferredCells.Count(cell => cell.Placement == Placement.Module), modules.Count);
        foreach (var module in modules.Values)
            SourceProvenance.ParseSyntaxValidRoot(module);
    }

    // ── Coverage of the matrix ─────────────────────────────────────────────────────────────────

    [Fact]
    public void Matrix_CrossesEveryContainerAndCapturePosition_WithEveryPlacementItHas()
    {
        var containers = Enum.GetValues<Container>();
        var captures = Enum.GetValues<Capture>();

        // Site placement: the full cross product.
        var site = DeferredCells.Where(cell => cell.Placement == Placement.Site)
            .Select(cell => (cell.Container, cell.Capture)).ToArray();
        Assert.Equal(containers.SelectMany(container => captures.Select(capture => (container, capture))).Order(), site.Order());

        // Module placement: every container a module can declare. An inline block head is written in
        // the branch itself, so it has none.
        var module = DeferredCells.Where(cell => cell.Placement == Placement.Module)
            .Select(cell => (cell.Container, cell.Capture)).ToArray();
        Assert.Equal(
            containers.Where(container => container != Container.InlineHead)
                .SelectMany(container => captures.Select(capture => (container, capture))).Order(),
            module.Order());

        Assert.Equal(14, DeferredCells.Count);
        Assert.Equal(DeferredCells.Count, DeferredCells.Select(DeferredSlug).Distinct(StringComparer.Ordinal).Count());
    }

    [Fact]
    public void Matrix_RunsEveryVariantAndRowOrderOfEveryCell()
    {
        var ids = AllProgramIds().ToArray();

        // 14 cells x 3 variants x 3 root-row programs.
        Assert.Equal(126, ids.Length);
        Assert.Equal(ids.Length, ids.Distinct(StringComparer.Ordinal).Count());
        foreach (var cell in DeferredCells)
        {
            foreach (var variant in Variants)
            {
                foreach (var (name, _) in RowPrograms)
                    Assert.Contains($"{DeferredSlug(cell)}/{VariantSlug(variant)}/{name}", ids);
            }
        }

        // The programs of one cell differ: no variant or row order is a duplicate source.
        var sources = DeferredCells.SelectMany(cell => Variants.SelectMany(variant => RowPrograms.Select(row
            => DeferredProgram(cell, variant, row.Rows)))).ToArray();
        Assert.Equal(sources.Length, sources.Distinct(StringComparer.Ordinal).Count());
    }

    [Fact]
    public void Matrix_ShowsMaterialization_Refusal_AndTheZeroDownloadControl()
    {
        // A selected branch downloads its module in the inside program of every cell; the eager twin
        // always loads; the never-selected control never does, in any row order.
        Assert.All(DeferredCells, cell => Assert.Equal(1, cell.Selected.Inside.Downloads));
        Assert.All(DeferredCells, cell => Assert.All(
            new[] { cell.EagerTwin.Inside, cell.EagerTwin.OutsideAfterCall, cell.EagerTwin.OutsideBeforeCall },
            expected => Assert.Equal(1, expected.Downloads)));
        Assert.All(DeferredCells, cell => Assert.All(
            new[] { cell.NeverSelected.Inside, cell.NeverSelected.OutsideAfterCall, cell.NeverSelected.OutsideBeforeCall },
            expected => Assert.Equal(0, expected.Downloads)));
        Assert.All(DeferredCells, cell => Assert.Equal("ok 0, 0", cell.NeverSelected.Inside.Outcome));

        // Each kind of outcome the route can have is present: per-call values, the access refusal,
        // the forwarding refusal of an inadmissible shape, and an admissible module-provided shape.
        var selected = DeferredCells.SelectMany(cell => new[] { cell.Selected.Inside, cell.Selected.OutsideAfterCall, cell.Selected.OutsideBeforeCall })
            .Select(expected => expected.Outcome).ToHashSet(StringComparer.Ordinal);
        Assert.Contains("ok 5, 7", selected);
        Assert.Contains("ok 1, 1", selected);
        Assert.Contains(DeferredLocalOnly, selected);
        Assert.Contains(DeferredForwardingRefused, selected);

        // An accepted selected shape has exactly its eager twin's outcomes (eager parity); a refused
        // one is the only place the two differ.
        foreach (var cell in DeferredCells)
        {
            if (cell.Selected.Inside.Outcome == DeferredForwardingRefused)
            {
                Assert.NotEqual(cell.Selected.Inside.Outcome, cell.EagerTwin.Inside.Outcome);
                continue;
            }

            Assert.Equal(cell.EagerTwin.Inside.Outcome, cell.Selected.Inside.Outcome);
            Assert.Equal(cell.EagerTwin.OutsideAfterCall.Outcome, cell.Selected.OutsideAfterCall.Outcome);
            Assert.Equal(cell.EagerTwin.OutsideBeforeCall.Outcome, cell.Selected.OutsideBeforeCall.Outcome);
        }
    }
}
