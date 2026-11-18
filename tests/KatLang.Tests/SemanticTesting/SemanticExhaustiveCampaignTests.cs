using System.Collections.Immutable;
using System.Globalization;
using System.Text.Json;
using KatLang.ParserFuzz;
using Xunit.Abstractions;

namespace KatLang.Tests.SemanticTesting;

/// <summary>
/// Exhaustive campaigns over the FINITE nested recipes and the wide nested recipe (fuzz/README.md
/// § Campaigns, § Families and interactions). The enumeration of <c>seed-nested</c> (3,472 programs)
/// and <c>seed-nested-wide</c> (26,064) is exact, deterministic and complete — every seeded case is
/// one of its programs; an enumerated id is canonical and rebuilds its program; an exhaustive
/// campaign reports its distinct sources and (source, profile) pairs and whether it is complete; a
/// planted failure is found, persisted and reduced; supervised batches keep failure isolation; and a
/// fixed strided slice of both recipes runs in process here, as the CI smoke of the exhaustive mode.
/// </summary>
public class SemanticExhaustiveCampaignTests(ITestOutputHelper output)
{
    private const int NestedPrograms = 3_472;
    private const int WidePrograms = 26_064;

    private static readonly Lazy<SemanticExhaustive.Enumeration> Nested = new(() => SemanticExhaustive.Enumerate(SemanticCorpus.NestedSeedRecipe));
    private static readonly Lazy<SemanticExhaustive.Enumeration> Wide = new(() => SemanticExhaustive.Enumerate(SemanticCorpus.NestedWideSeedRecipe));

    /// <summary>Every non-cancellation profile, in the corpus order: what an enumerated program runs.</summary>
    private static readonly string[] AllProfiles =
    [
        SemanticProfiles.SyncGeneric, SemanticProfiles.SyncOptimized, SemanticProfiles.AsyncTwin,
        SemanticProfiles.EngineRun, SemanticProfiles.EngineRunAsync, SemanticProfiles.SyncOptimizedRerun,
    ];

    private static SemanticCase Program(string recipe, SemanticExhaustive.EnumeratedProgram program)
        => SemanticCorpus.ExhaustiveBuilder(recipe, program.Choices).Build();

    private static string[] Listing(string root)
        => [.. Directory.GetFiles(root, "*", SearchOption.AllDirectories).Select(f => Path.GetRelativePath(root, f).Replace('\\', '/')).Order(StringComparer.Ordinal)];

    // ── Enumeration ─────────────────────────────────────────────────────────

    /// <summary>
    /// Both finite recipes enumerate an exact number of choice sequences, each its own program with
    /// its own id, in strictly increasing (depth-first) order of the choice sequences; <c>seed</c> is
    /// refused as not finite.
    /// </summary>
    [Fact]
    public void TheFiniteRecipes_EnumerateEveryProgramOnce_InDepthFirstOrder()
    {
        Assert.Equal([SemanticCorpus.NestedSeedRecipe, SemanticCorpus.NestedWideSeedRecipe, SemanticCorpus.NestedWiderSeedRecipe], SemanticCorpus.FiniteRecipes.ToArray());
        foreach (var (enumeration, count) in new[] { (Nested.Value, NestedPrograms), (Wide.Value, WidePrograms) })
        {
            Assert.Equal(count, enumeration.Sequences);
            Assert.Equal(count, enumeration.Programs.Length);
            Assert.Equal(count, enumeration.Programs.Select(static p => p.CaseId).Distinct(StringComparer.Ordinal).Count());
            for (var i = 1; i < enumeration.Programs.Length; i++)
                Assert.True(Compare(enumeration.Programs[i - 1].Choices, enumeration.Programs[i].Choices) < 0, $"order broken at {i}");
            Assert.All(enumeration.Programs, p => Assert.Equal(
                SemanticRecipe.CasePrefix + enumeration.Recipe + "/all/" + string.Join(".", p.Choices), p.CaseId));
        }

        Assert.Equal("sem2b/v1/seed-nested/all/0.0.0.0.0", Nested.Value.Programs[0].CaseId);
        Assert.Equal("sem2b/v1/seed-nested-wide/all/0.0.0.0.0.0.0.0.0", Wide.Value.Programs[0].CaseId);
        Assert.Throws<ArgumentException>(() => SemanticExhaustive.Enumerate(SemanticCorpus.SeedRecipe));

        static int Compare(ImmutableArray<int> a, ImmutableArray<int> b)
        {
            for (var i = 0; i < Math.Min(a.Length, b.Length); i++)
                if (a[i] != b[i]) return a[i].CompareTo(b[i]);
            return a.Length.CompareTo(b.Length);
        }
    }

    /// <summary>
    /// The enumeration is COMPLETE: every seeded case of either recipe (16 indices of 16 seeds each)
    /// is an enumerated program — the same members and the same constructed expectation — and differs
    /// only in its identity (tier, seed, index) and its profile selection.
    /// </summary>
    [Fact]
    public void EverySeededCase_IsAnEnumeratedProgram()
    {
        foreach (var (recipe, enumeration) in new[] { (SemanticCorpus.NestedSeedRecipe, Nested.Value), (SemanticCorpus.NestedWideSeedRecipe, Wide.Value) })
        {
            var bySource = new Dictionary<string, SemanticCase>(StringComparer.Ordinal);
            foreach (var program in enumeration.Programs)
            {
                var built = Program(recipe, program);
                bySource.Add(built.Source, built);
            }

            var seeded = 0;
            for (var seed = 0x5EED_2B00_0001UL; seed <= 0x5EED_2B00_0010UL; seed++)
            {
                for (var index = 0; index < 16; index++)
                {
                    var c = SemanticCorpus.SeededBuilder(recipe, seed, index).Build();
                    Assert.True(bySource.TryGetValue(c.Source, out var enumerated), $"{c.CaseId} is not enumerated:\n{c.Source}");
                    Assert.Equal(c.Members.ToArray(), enumerated.Members.ToArray());
                    Assert.Equal(c.Expected.ToString(), enumerated.Expected.ToString());
                    Assert.Equal(c.Expected.ValueIdentity, enumerated.Expected.ValueIdentity);
                    Assert.Equal(c.Paths, enumerated.Paths);
                    Assert.Equal(c.Features.ToArray(), enumerated.Features.ToArray());
                    Assert.Equal(("seeded", SemanticCorpus.ExhaustiveTier), (c.Tier, enumerated.Tier));
                    if (c.Kind == SemanticCaseKind.InvalidFrontEnd) Assert.Equal(c.Profiles.ToArray(), enumerated.Profiles.ToArray());
                    else
                    {
                        Assert.Subset(AllProfiles.ToHashSet(StringComparer.Ordinal), c.Profiles.ToHashSet(StringComparer.Ordinal));
                        Assert.Equal(AllProfiles, enumerated.Profiles.ToArray());
                    }
                    seeded++;
                }
            }

            Assert.Equal(256, seeded);
        }
    }

    /// <summary>
    /// An enumerated id rebuilds its program from the id alone (recipe mode replays it, export writes
    /// it), and only CANONICAL choice sequences are ids: a chance written as anything but 0 or its
    /// percentage, a pick outside its dimension, a truncated or extended sequence, malformed text and
    /// <c>seed</c> (not finite) are refused.
    /// </summary>
    [Fact]
    public void EnumeratedIds_RebuildTheirProgram_AndOnlyCanonicalSequencesAreIds()
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-exhaustive-ids-");
        try
        {
            foreach (var (recipe, enumeration) in new[] { (SemanticCorpus.NestedSeedRecipe, Nested.Value), (SemanticCorpus.NestedWideSeedRecipe, Wide.Value) })
            {
                var sample = enumeration.Programs.Where((_, i) => i % 997 == 0).Append(enumeration.Programs[^1]).ToArray();
                foreach (var program in sample)
                {
                    Assert.True(SemanticCorpus.TryBuilder(program.CaseId, SemanticRecipe.RecipeVersion, out var builder, out var problem), problem);
                    Assert.Equal(program.CaseId, builder.CaseId);
                    var recorder = new RecordingChooser(builder.NewChooser());
                    var built = builder.Build(recorder).Case;
                    Assert.Equal(program.Choices.ToArray(), SemanticReducer.Values(recorder.Choices).ToArray());
                    Assert.Equal((program.CaseId, SemanticCorpus.ExhaustiveTier, (ulong?)null, (int?)null), (built.CaseId, built.Tier, built.Seed, built.Index));
                    Assert.Equal(built.Kind == SemanticCaseKind.InvalidFrontEnd
                        ? [SemanticProfiles.SyncOptimized, SemanticProfiles.EngineRun, SemanticProfiles.EngineRunAsync]
                        : AllProfiles, built.Profiles.ToArray());
                }

                var exported = Path.Combine(root.FullName, SemanticReplay.SafeName(sample[1].CaseId) + ".json");
                Assert.Equal(0, SemanticReplay.RunExport(["semantic-export", sample[1].CaseId, exported]));
                var outcome = SemanticReplay.Replay(File.ReadAllText(exported), SemanticReplay.Mode.Recipe);
                Assert.True(outcome.Passed, outcome.Report);
                Assert.Equal(sample[1].CaseId, outcome.CaseId);
            }

            // seed-nested: outer 0, a failing chance (0 of 25), width 0, one context, the list context.
            Assert.True(SemanticCorpus.TryBuilder("sem2b/v1/seed-nested/all/0.0.0.0.0", SemanticRecipe.RecipeVersion, out _, out var accepted), accepted);
            string[] refused =
            [
                "sem2b/v1/seed-nested/all/0.24.0.0.0",   // a 25 % chance is 0 or 25
                "sem2b/v1/seed-nested/all/2.0.0.0.0",    // nested.outer has two values
                "sem2b/v1/seed-nested/all/0.0.0.0",      // truncated
                "sem2b/v1/seed-nested/all/0.0.0.0.0.0",  // extended
                "sem2b/v1/seed-nested/all/0.0.x",
                "sem2b/v1/seed-nested/all/",
                "sem2b/v1/seed-nested/all/0..0",
                "sem2b/v1/seed-nested-wide/all/9",
                "sem2b/v1/seed/all/0",                   // seed is not finite: an ordinary malformed seeded id
            ];
            foreach (var id in refused)
            {
                Assert.False(SemanticCorpus.TryBuilder(id, SemanticRecipe.RecipeVersion, out _, out var problem), id);
                output.WriteLine($"{id}: {problem}");
            }
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    // ── Campaigns ───────────────────────────────────────────────────────────

    private static SemanticCampaignOptions Exhaustive(string recipe, string outDir, int maxCases) => new()
    {
        Recipe = recipe,
        Exhaustive = true,
        MaxCases = maxCases,
        OutputDirectory = outDir,
        InProcessRunner = static c => SemanticRunner.Run(c),
    };

    /// <summary>
    /// An exhaustive campaign over the first programs of <c>seed-nested</c>: it plans the whole
    /// enumeration, executes exactly its prefix in order, runs each program under all six profiles,
    /// reports the distinct sources and pairs, is not complete, and writes the same summary twice.
    /// Through the command, <c>--exhaustive</c> runs the wide recipe the same way.
    /// </summary>
    [Fact]
    public void AnExhaustiveCampaign_RunsItsEnumerationInOrder_AndIsDeterministic()
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-exhaustive-campaign-");
        try
        {
            var executed = new List<string>();
            SemanticCampaignOptions Options(string name) => Exhaustive(SemanticCorpus.NestedSeedRecipe, Path.Combine(root.FullName, name), 24) with
            {
                InProcessRunner = c =>
                {
                    executed.Add(c.CaseId);
                    return SemanticRunner.Run(c);
                },
            };

            var first = SemanticCampaign.Run(Options("a"), TextWriter.Null);
            _ = SemanticCampaign.Run(Options("b"), TextWriter.Null);
            output.WriteLine(first.Describe());

            var ids = Nested.Value.Programs.Take(24).Select(static p => p.CaseId).ToArray();
            Assert.Equal([.. ids, .. ids], executed.ToArray());
            Assert.Equal((NestedPrograms, 24, 24, NestedPrograms), (first.Planned, first.Executed, first.Passed, first.Sequences!.Value));
            Assert.Equal(SemanticCampaignStop.CaseBudget, first.Stop);
            Assert.False(first.Complete);
            Assert.Equal((ids[^1], Nested.Value.Programs[24].CaseId), (first.LastCovered, first.FirstUncovered));
            Assert.Equal((24, 24 * AllProfiles.Length), (first.DistinctSources, first.DistinctSourceProfiles));

            var a = File.ReadAllText(Path.Combine(root.FullName, "a", SemanticCampaign.SummaryFile));
            Assert.Equal(a, File.ReadAllText(Path.Combine(root.FullName, "b", SemanticCampaign.SummaryFile)));
            Assert.Equal([SemanticCampaign.SummaryFile], Listing(Path.Combine(root.FullName, "a")));
            using (var document = JsonDocument.Parse(a))
            {
                var json = document.RootElement;
                Assert.Equal("exhaustive", json.GetProperty("mode").GetString());
                Assert.Equal("seed-nested", json.GetProperty("recipe").GetString());
                Assert.Equal(JsonValueKind.Null, json.GetProperty("firstSeed").ValueKind);
                Assert.Equal(JsonValueKind.Null, json.GetProperty("casesPerSeed").ValueKind);
                Assert.Equal(SemanticCampaignOptions.DefaultBatchSize, json.GetProperty("batchSize").GetInt32());
                Assert.Equal((NestedPrograms, NestedPrograms, 24), (json.GetProperty("sequences").GetInt32(), json.GetProperty("planned").GetInt32(), json.GetProperty("maxCases").GetInt32()));
                Assert.Equal((24, 144), (json.GetProperty("distinctSources").GetInt32(), json.GetProperty("distinctSourceProfiles").GetInt32()));
                Assert.False(json.GetProperty("complete").GetBoolean());
                Assert.Equal("case-budget", json.GetProperty("stop").GetString());
            }

            // The command: --exhaustive over the wide recipe, its unbounded case budget written as null.
            var log = new StringWriter();
            var wideOut = Path.Combine(root.FullName, "wide");
            Assert.Equal(0, SemanticCampaign.RunCampaign(
                ["semantic-campaign", "--exhaustive", "--recipe", "seed-nested-wide", "--max-cases", "12", "--out", wideOut],
                log, o => o with { InProcessRunner = static c => SemanticRunner.Run(c) }));
            output.WriteLine(log.ToString());
            Assert.Contains("semantic-campaign: recipe seed-nested-wide, exhaustive (26064 programs from 26064 choice sequences, in process): planned=26064 executed=12 passed=12 failed=0 distinct-sources=12 distinct-source-profiles=",
                log.ToString(), StringComparison.Ordinal);
            Assert.Contains(" complete=no first-uncovered=" + Wide.Value.Programs[12].CaseId, log.ToString(), StringComparison.Ordinal);
            Assert.True(SemanticCampaign.TryParse(["semantic-campaign", "--exhaustive", "--recipe", "seed-nested"], out var defaults, out var problem), problem);
            Assert.Equal((true, int.MaxValue, TimeSpan.FromSeconds(SemanticCampaignOptions.DefaultExhaustiveMaxSeconds), SemanticCampaignOptions.DefaultBatchSize),
                (defaults.Exhaustive, defaults.MaxCases, defaults.MaxTime, defaults.BatchSize));
            Assert.Contains("/artifacts/semantic-campaign/seed-nested-exhaustive-", defaults.OutputDirectory.Replace('\\', '/'), StringComparison.Ordinal);
            Assert.Null(defaults.Problem());

            // The rerun budget of failing batch members: a default, settable down to none, exhaustive only.
            Assert.Equal(SemanticCampaignOptions.DefaultMaxReruns, defaults.MaxReruns);
            Assert.True(SemanticCampaign.TryParse(["semantic-campaign", "--exhaustive", "--recipe", "seed-nested", "--max-reruns", "0"], out var noReruns, out problem), problem);
            Assert.Equal(0, noReruns.MaxReruns);
            Assert.Null(noReruns.Problem());
            Assert.Equal("--max-reruns must be non-negative", (defaults with { MaxReruns = -1 }).Problem());
            Assert.False(SemanticCampaign.TryParse(["semantic-campaign", "--seeds", "1", "--max-reruns", "3"], out _, out problem));
            Assert.Equal("--max-reruns applies only to --exhaustive", problem);
            Assert.Contains("[--batch-size N] [--max-reruns N]", SemanticCampaign.Usage, StringComparison.Ordinal);
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    /// <summary>
    /// A COMPLETE exhaustive campaign reports its complete count: every enumerated program executed
    /// once, each source distinct, six profiles each, <c>complete: true</c>. The runner here only
    /// records (the strided slice below evaluates); generation is the subject.
    /// </summary>
    [Fact]
    public void ACompleteExhaustiveCampaign_ReportsItsCompleteCount()
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-exhaustive-complete-");
        try
        {
            var invalid = 0;
            var result = SemanticCampaign.Run(Exhaustive(SemanticCorpus.NestedSeedRecipe, root.FullName, int.MaxValue) with
            {
                InProcessRunner = c =>
                {
                    if (c.Kind == SemanticCaseKind.InvalidFrontEnd) invalid++;
                    // Synthetic observations for this bookkeeping-only test. Coverage counts
                    // observations; it cannot assume requested profiles ran without a result.
                    return new SemanticCaseResult(c.CaseId, SemanticVerdict.Passed, [],
                        [.. c.Profiles.Select(static p => new SemanticProfileRun(p, SemanticMember.BaseRole, false,
                            "bookkeeping only", null, [], 0, 0, false, false, null))], SemanticPath.None, [], []);
                },
            }, TextWriter.Null);
            output.WriteLine(result.Describe());
            Assert.Equal(0, invalid);
            Assert.Equal((NestedPrograms, NestedPrograms, NestedPrograms), (result.Planned, result.Executed, result.Passed));
            Assert.Equal(SemanticCampaignStop.Completed, result.Stop);
            Assert.True(result.Complete);
            Assert.Null(result.FirstUncovered);
            Assert.Equal((NestedPrograms, NestedPrograms * AllProfiles.Length), (result.DistinctSources, result.DistinctSourceProfiles));
            var summary = File.ReadAllText(Path.Combine(root.FullName, SemanticCampaign.SummaryFile));
            Assert.Contains("\"maxCases\": null,", summary, StringComparison.Ordinal);
            Assert.Contains("\"complete\": true,", summary, StringComparison.Ordinal);
            Assert.Contains("\"distinctSourceProfiles\": 20832,", summary, StringComparison.Ordinal);
            Assert.Contains(" stop=completed complete=yes ", result.Describe(), StringComparison.Ordinal);
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    [Fact]
    public void AnUnansweredCase_DoesNotClaimAnyProfileCoverage()
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-exhaustive-no-observations-");
        try
        {
            var result = SemanticCampaign.Run(Exhaustive(SemanticCorpus.NestedSeedRecipe, root.FullName, 1) with
            {
                Reduce = false,
                InProcessRunner = static c => new SemanticCaseResult(c.CaseId, SemanticVerdict.Crash, [], [], SemanticPath.None, [], []),
            }, TextWriter.Null);
            Assert.Equal((1, 0, 1), (result.Executed, result.Passed, result.Failures.Length));
            Assert.Equal((1, 0), (result.DistinctSources, result.DistinctSourceProfiles));
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    /// <summary>
    /// The CI smoke of the exhaustive mode: a FIXED strided slice across the whole enumeration of both
    /// finite recipes (every 97th <c>seed-nested</c> program, every 401st <c>seed-nested-wide</c>
    /// program) runs in process under every profile and passes. The full sweeps are manual
    /// (<c>semantic-campaign --exhaustive</c>; fuzz/README.md § Campaigns).
    /// </summary>
    [Fact]
    public void AStridedSliceOfBothFiniteRecipes_PassesInProcess()
    {
        foreach (var (recipe, enumeration, stride) in new[] { (SemanticCorpus.NestedSeedRecipe, Nested.Value, 97), (SemanticCorpus.NestedWideSeedRecipe, Wide.Value, 401) })
        {
            var ran = 0;
            for (var i = 0; i < enumeration.Programs.Length; i += stride)
            {
                var c = Program(recipe, enumeration.Programs[i]);
                var result = SemanticRunner.Run(c);
                Assert.True(result.Passed, $"{c.CaseId}: {string.Join("; ", result.Findings.Take(3))}\n{c.Source}");
                ran++;
            }

            output.WriteLine($"{recipe}: {ran} programs of {enumeration.Programs.Length}");
            Assert.Equal((enumeration.Programs.Length + stride - 1) / stride, ran);
        }
    }

    /// <summary>The planted shape: a wrong value on <c>base@sync-optimized</c> for programs in the live <c>if</c> context.</summary>
    private const string Trigger = "if(true";

    private static SemanticCaseResult FaultyRun(SemanticCase c)
        => SemanticRunner.Run(c, c.Source.Contains(Trigger, StringComparison.Ordinal) ? SemanticReductionTests.WrongValue : null);

    /// <summary>
    /// A planted failure in an exhaustive campaign is found, persisted and reduced exactly as in a
    /// seeded one: of the first eight <c>seed-nested</c> programs only the second sits in the live
    /// <c>if</c>; its descriptor replays the planted signature in recipe mode (rebuilt from the
    /// enumerated id), and its reduction record is a v1 record the id rebuilds.
    /// </summary>
    [Fact]
    public void APlantedExhaustiveFailure_IsFoundPersistedAndReduced()
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-exhaustive-planted-");
        try
        {
            var outDir = Path.Combine(root.FullName, "out");
            var log = new StringWriter();
            var exit = SemanticCampaign.RunCampaign(
                ["semantic-campaign", "--exhaustive", "--recipe", "seed-nested", "--max-cases", "8", "--max-attempts", "40", "--out", outDir],
                log, o => o with { InProcessRunner = FaultyRun });
            output.WriteLine(log.ToString());
            Assert.Equal(1, exit);

            const string id = "sem2b/v1/seed-nested/all/0.0.0.0.1";
            Assert.Equal(id, Nested.Value.Programs[1].CaseId);
            using var document = JsonDocument.Parse(File.ReadAllText(Path.Combine(outDir, SemanticCampaign.SummaryFile)));
            var json = document.RootElement;
            Assert.Equal((8, 7, 1), (json.GetProperty("executed").GetInt32(), json.GetProperty("passed").GetInt32(), json.GetProperty("failed").GetInt32()));
            var failure = Assert.Single(json.GetProperty("failures").EnumerateArray().ToArray());
            Assert.Equal(id, failure.GetProperty("caseId").GetString());
            Assert.Equal("seed-nested", failure.GetProperty("recipe").GetString());
            var signature = new SemanticFailureSignature(SemanticVerdict.Mismatch, SemanticMember.BaseRole, SemanticProfiles.SyncOptimized, "outcome");
            Assert.Equal(signature.Facet, failure.GetProperty("signature").GetProperty("facet").GetString());

            var descriptor = File.ReadAllText(Path.Combine(outDir, "failures", SemanticReplay.SafeName(id) + ".json"));
            Assert.True(SemanticDescriptor.TryParse(descriptor, out var parsed, out var problem), problem);
            Assert.Equal((id, SemanticCorpus.ExhaustiveTier), (parsed.Case.CaseId, parsed.Case.Tier));
            Assert.Equal(signature, SemanticFailureSignature.Of(SemanticReplay.Replay(descriptor, SemanticReplay.Mode.Recipe, SemanticReductionTests.WrongValue).Result!));
            Assert.True(SemanticReplay.Replay(descriptor, SemanticReplay.Mode.Recipe).Passed, "the program passes without the planted fault");

            var reduction = failure.GetProperty("reduction");
            Assert.Contains(reduction.GetProperty("status").GetString(), new[] { nameof(SemanticReductionStatus.Reduced), nameof(SemanticReductionStatus.AlreadyMinimal) });
            var recordPath = Path.Combine(outDir, reduction.GetProperty("record").GetString()!);
            Assert.True(SemanticReduction.TryParseRecord(File.ReadAllText(recordPath), out var record, out problem), problem);
            Assert.Equal((id, signature), (record.OriginalCaseId, record.Signature));
            Assert.StartsWith("sem2b/v1/reduced/seed-nested/all/0.0.0.0.1/", record.ReducedCaseId, StringComparison.Ordinal);
            Assert.True(SemanticReduction.TryRebuild(record, out var reduced, out problem), problem);
            Assert.Contains(Trigger, reduced.Source, StringComparison.Ordinal);
            Assert.Equal(signature, SemanticFailureSignature.Of(FaultyRun(reduced)));
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    // ── Supervised batches ──────────────────────────────────────────────────

    private const string ModeVariable = "KATLANG_SEM2C_EXHAUSTIVE_WORKER_MODE";
    private const string ManifestVariable = "KATLANG_SEM2C_EXHAUSTIVE_WORKER_MANIFEST";
    private const string DescriptorVariable = "KATLANG_SEM2C_EXHAUSTIVE_WORKER_DESCRIPTOR";
    private const string ResultVariable = "KATLANG_SEM2C_EXHAUSTIVE_WORKER_RESULT";
    private const string BatchMode = "batch";
    private const string BatchOnlyCrashMode = "batch-only-crash";
    private const string AfterResultsCrashMode = "after-results-crash";
    private const string SingleMode = "single";
    private const string PassingSingleMode = "passing-single";

    /// <summary>The planted crash: the worker process ends abruptly, without a result, in the dead-branch <c>if</c> context.</summary>
    private const string CrashTrigger = "if(false";

    private const int CrashExitCode = 70;

    /// <summary>The child's fault for one member: exit for the crash trigger, the planted wrong value for <see cref="Trigger"/>.</summary>
    private static Func<SemanticProfileRun, SemanticProfileRun>? ChildFault(SemanticCase c)
    {
        if (c.Source.Contains(CrashTrigger, StringComparison.Ordinal)) Environment.Exit(CrashExitCode);
        return c.Source.Contains(Trigger, StringComparison.Ordinal) ? SemanticReductionTests.WrongValue : null;
    }

    private static Dictionary<string, string> ChildEnvironment(string mode) => new()
    {
        [ModeVariable] = mode,
        ["DOTNET_NOLOGO"] = "1",
    };

    private static string[] ChildArguments(string method) =>
    [
        "vstest",
        typeof(SemanticExhaustiveCampaignTests).Assembly.Location,
        "--Tests:" + typeof(SemanticExhaustiveCampaignTests).FullName + "." + method,
    ];

    private static SemanticBatchWorkerCommand BatchChild(string manifest)
        => BatchChild(manifest, BatchMode);

    private static SemanticBatchWorkerCommand BatchChild(string manifest, string mode)
    {
        var environment = ChildEnvironment(mode);
        environment[ManifestVariable] = manifest;
        return new SemanticBatchWorkerCommand("dotnet", ChildArguments(nameof(BatchWorker_Child)), environment, manifest);
    }

    private static SemanticWorkerCommand SingleChild(string descriptor, string result, SemanticReplay.Mode mode)
        => SingleChild(descriptor, result, SingleMode);

    private static SemanticWorkerCommand SingleChild(string descriptor, string result, string workerMode)
    {
        var environment = ChildEnvironment(workerMode);
        environment[DescriptorVariable] = descriptor;
        environment[ResultVariable] = result;
        return new SemanticWorkerCommand("dotnet", ChildArguments(nameof(SingleWorker_Child)), environment, descriptor, result);
    }

    /// <summary>
    /// Supervised batches keep failure isolation and persisted reproducers. The first six
    /// <c>seed-nested-wide</c> programs (one two-level success in the contexts bare, list, live
    /// <c>if</c>, dead <c>if</c>, property and cached property) go to ONE batch child; it answers the
    /// first three — the third with the planted wrong value — and dies on the fourth. The fourth then
    /// runs alone in a single-case child (the standard supervisor: a crash, its evidence kept), and
    /// the last two run in a second batch that passes. Every descriptor was persisted before
    /// dispatch; the failing batch's entire reproducer is retained, and the clean batch is removed. (The planted wrong value
    /// needs SUCCESS cases: on an expected failure it forges an observation no worker can write, which
    /// the result reader rejects as malformed.)
    /// </summary>
    [Fact]
    public void SupervisedBatches_IsolateACrash_AndKeepEveryFailingReproducer()
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-exhaustive-batches-");
        try
        {
            var result = SemanticCampaign.Run(new SemanticCampaignOptions
            {
                Recipe = SemanticCorpus.NestedWideSeedRecipe,
                Exhaustive = true,
                MaxCases = 6,
                BatchSize = 6,
                Reduce = false,
                OutputDirectory = root.FullName,
                BatchWorkerCommand = BatchChild,
                WorkerCommand = SingleChild,
            }, TextWriter.Null);
            output.WriteLine(result.Describe());
            var supervision = Path.Combine(root.FullName, "work", "batch-00001.txt.supervision.txt");
            if (File.Exists(supervision)) output.WriteLine(File.ReadAllText(supervision));

            var programs = Wide.Value.Programs.Take(6).Select(static p => p.CaseId).ToArray();
            Assert.Equal((6, 4), (result.Executed, result.Passed));
            Assert.Equal(5 * AllProfiles.Length, result.DistinctSourceProfiles);
            Assert.Equal(programs[5], result.LastCovered);
            Assert.Equal(
                [(programs[2], SemanticVerdict.Mismatch), (programs[3], SemanticVerdict.Crash)],
                result.Failures.Select(static f => (f.CaseId, f.Verdict)).ToArray());
            Assert.Equal("value", result.Failures[0].Signature.Facet);

            string Safe(int i) => SemanticReplay.SafeName(programs[i]);
            var batch = File.ReadAllText(Path.Combine(root.FullName, "work", "batch-00001.txt.supervision.txt"));
            Assert.Contains("\"ChildFailure\": " + (int)SemanticVerdict.Crash, batch, StringComparison.Ordinal);
            var manifest = Path.Combine(root.FullName, "work", "batch-00001.txt");
            var lines = File.ReadAllLines(manifest);
            Assert.Equal(6, lines.Length);
            Assert.All(lines, static line => Assert.True(File.Exists(line.Split('\t')[0]), "every preceding descriptor is part of the batch reproducer"));
            Assert.All(result.Failures, f => Assert.Equal("work/batch-00001.txt", f.BatchManifest));
            Assert.False(File.Exists(Path.Combine(root.FullName, "work", "batch-00002.txt")));
            Assert.False(Directory.Exists(Path.Combine(root.FullName, "work", "batch-00002")));
            Assert.True(File.Exists(Path.Combine(root.FullName, "work", "batch-00001", "rerun", Safe(3) + ".json.result.json.supervision.txt")));

            // The kept reproducers replay: the mismatch passes without the fault, and the crash's
            // descriptor is the enumerated program itself.
            Assert.True(SemanticReplay.Replay(File.ReadAllText(Path.Combine(root.FullName, "failures", Safe(2) + ".json")), SemanticReplay.Mode.Recipe).Passed);
            Assert.True(SemanticDescriptor.TryParse(File.ReadAllText(Path.Combine(root.FullName, "failures", Safe(3) + ".json")), out var crashed, out var problem), problem);
            Assert.Equal(programs[3], crashed.Case.CaseId);
            Assert.Contains(CrashTrigger, crashed.Case.Source, StringComparison.Ordinal);
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    /// <summary>A crash seen only in a batch, before or after the last result, must never become a passing campaign.</summary>
    [Theory]
    [InlineData(BatchOnlyCrashMode, 4)]
    [InlineData(AfterResultsCrashMode, 3)]
    public void AChildCrash_RemainsAFailureWhenEveryStandaloneCasePasses(string workerMode, int count)
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-batch-only-crash-");
        try
        {
            var outDir = Path.Combine(root.FullName, "out");
            var log = new StringWriter();
            var exit = SemanticCampaign.RunCampaign(
                ["semantic-campaign", "--exhaustive", "--recipe", "seed-nested-wide", "--max-cases", count.ToString(CultureInfo.InvariantCulture),
                    "--batch-size", count.ToString(CultureInfo.InvariantCulture), "--no-reduce", "--out", outDir], log,
                o => o with
                {
                    BatchWorkerCommand = manifest => BatchChild(manifest, workerMode),
                    WorkerCommand = static (descriptor, result, _) => SingleChild(descriptor, result, PassingSingleMode),
                });
            output.WriteLine(log.ToString());
            Assert.Equal(1, exit);
            using var document = JsonDocument.Parse(File.ReadAllText(Path.Combine(outDir, SemanticCampaign.SummaryFile)));
            var json = document.RootElement;
            Assert.Equal((count, count - 1, 1), (json.GetProperty("executed").GetInt32(), json.GetProperty("passed").GetInt32(), json.GetProperty("failed").GetInt32()));
            var failure = Assert.Single(json.GetProperty("failures").EnumerateArray());
            Assert.Equal(nameof(SemanticVerdict.Crash), failure.GetProperty("verdict").GetString());
            Assert.Equal(Wide.Value.Programs[count - 1].CaseId, failure.GetProperty("caseId").GetString());
            var manifest = Path.Combine(outDir, failure.GetProperty("batchManifest").GetString()!);
            var lines = File.ReadAllLines(manifest);
            Assert.Equal(count, lines.Length);
            foreach (var line in lines)
            {
                var parts = line.Split('\t');
                Assert.True(File.Exists(parts[0]));
                Assert.True(SemanticReplay.Replay(File.ReadAllText(parts[0]), SemanticReplay.Mode.Recipe).Passed);
            }

            Assert.True(File.Exists(manifest + ".supervision.txt"));
            if (workerMode == BatchOnlyCrashMode) Assert.Contains("standalone rerun Passed; original batch failure retained", log.ToString(), StringComparison.Ordinal);
            else Assert.All(lines, static line => Assert.True(File.Exists(line.Split('\t')[1])));
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    /// <summary>The batch child half. Inert (returns immediately) unless launched by the supervised test above.</summary>
    [Fact]
    public void BatchWorker_Child()
    {
        var mode = Environment.GetEnvironmentVariable(ModeVariable);
        if (mode is not (BatchMode or BatchOnlyCrashMode or AfterResultsCrashMode)) return;
        var manifest = Environment.GetEnvironmentVariable(ManifestVariable)!;
        Func<SemanticProfileRun, SemanticProfileRun>? Filter(SemanticCase c)
        {
            if (mode == BatchMode) return ChildFault(c);
            if (mode == BatchOnlyCrashMode && c.Source.Contains(CrashTrigger, StringComparison.Ordinal)) Environment.Exit(CrashExitCode);
            return null;
        }

        Assert.Equal(0, SemanticReplay.WorkBatch(manifest, SemanticReplay.Mode.Recipe, Filter));
        if (mode == AfterResultsCrashMode) Environment.Exit(CrashExitCode);
    }

    /// <summary>The single-case child half. Inert (returns immediately) unless launched by the supervised test above.</summary>
    [Fact]
    public void SingleWorker_Child()
    {
        var mode = Environment.GetEnvironmentVariable(ModeVariable);
        if (mode is not (SingleMode or PassingSingleMode)) return;
        var descriptor = Environment.GetEnvironmentVariable(DescriptorVariable)!;
        var result = Environment.GetEnvironmentVariable(ResultVariable)!;
        Assert.True(SemanticDescriptor.TryParse(File.ReadAllText(descriptor), out var parsed, out var problem), problem);
        Assert.Equal(0, SemanticReplay.Work(descriptor, result, SemanticReplay.Mode.Recipe, mode == SingleMode ? ChildFault(parsed.Case) : null));
    }

    // ── The wide recipe ─────────────────────────────────────────────────────

    /// <summary>
    /// <c>seed-nested-wide</c> writes every shape the brief names, in all three group extents, with the
    /// three runtime failure kinds and the four intended refusals: counted over its whole enumeration.
    /// Every valid program parses cleanly (the strided slice and the full sweeps run them); every
    /// refusal names the diagnostic its shape violates.
    /// </summary>
    [Fact]
    public void TheWideRecipe_WritesEveryShapeExtentFailureAndRefusal()
    {
        var features = new Dictionary<string, int>(StringComparer.Ordinal);
        var kinds = new Dictionary<SemanticCaseKind, int>();
        var errors = new SortedSet<string>(StringComparer.Ordinal);
        var refusals = new SortedSet<string>(StringComparer.Ordinal);
        foreach (var program in Wide.Value.Programs)
        {
            var c = Program(SemanticCorpus.NestedWideSeedRecipe, program);
            kinds[c.Kind] = kinds.GetValueOrDefault(c.Kind) + 1;
            foreach (var feature in c.Features) features[feature] = features.GetValueOrDefault(feature) + 1;
            if (c.Expected.ErrorCategory is { } error) errors.Add(error);
            if (c.Kind == SemanticCaseKind.InvalidFrontEnd)
            {
                var refusal = c.Features.Single(static f => f.StartsWith("refusal-", StringComparison.Ordinal));
                refusals.Add(refusal + ":" + c.Expected.Diagnostic + "/" + c.Expected.DiagnosticPhase);
                Assert.Single(c.Members);
            }
            else
            {
                Assert.InRange(c.Members.Length, 2, 3); // base and alpha-rename, and declaration-reorder over two root declarations
            }
        }

        foreach (var (key, value) in features.Where(static p => p.Key.StartsWith("wide-", StringComparison.Ordinal) || p.Key.StartsWith("layout-", StringComparison.Ordinal)).OrderBy(static p => p.Key, StringComparer.Ordinal))
            output.WriteLine($"{key}: {value}");
        Assert.Equal(
            (2016 + 1824 + 2016 + 1920, 2016 + 1824 + 2016 + 1920, 576 * 9, 2016 * 2, 576 * 2, 144),
            (features["wide-pattern"], features["wide-parameters"], features["wide-clauses"], features["wide-deconstruct-result"],
                features["wide-deconstruct-collector"], features["wide-refusal"]));
        Assert.Equal(WidePrograms / 3, features["layout-tight"]);
        Assert.Equal(WidePrograms / 3, features["layout-padded"]);
        Assert.Equal(WidePrograms / 3, features["layout-broken"]);
        Assert.InRange(features["three-level"], 1, WidePrograms - 1);
        Assert.True(features["collector-both-levels"] > 0 && features["parameter-list"] > 0 && features["clause-family"] > 0
            && features["catch-all"] > 0 && features["deconstruction"] > 0 && features["async"] > 0, "a shape is missing");
        Assert.Equal(["ArityMismatch", "NoMatchingBranch", "TypeMismatch"], errors.ToArray());
        Assert.Equal(
            [
                "refusal-clause-arity:BranchArityMismatch/syntax",
                "refusal-clause-collector:InvalidCollectingBinding/syntax",
                "refusal-duplicate-layout:DuplicateBranchPattern/syntax",
                "refusal-singleton-group:SingletonSequencePattern/syntax",
            ],
            refusals.ToArray());
        Assert.Equal(WidePrograms, kinds.Values.Sum());
        output.WriteLine(string.Join(", ", kinds.OrderBy(static p => p.Key).Select(static p => $"{p.Key}={p.Value}")));
    }

    /// <summary>
    /// What the wide recipe constructs, pinned on four programs: a parameter list whose structural
    /// argument runs at the call while the plain tail waits for the body and the collected arguments
    /// never run (NEED-04, NEED-07); one argument too many, rejected before any argument runs
    /// (NEED-05); a three-level clause family in the one-item-per-line extent whose literal clause
    /// does not match, so the second clause does, the argument running once; and two clauses of one
    /// structure in different extents, refused as duplicates.
    /// </summary>
    [Theory]
    [InlineData("1.1.0.0.1.0.0.1.0.0",
        "v1(v4, (v2, v3), *v5) = [v4, v2, v3, count(v5)]\nv1(trace(1), (wait(2), trace(3)), wait(4), trace(5))\n997",
        "value ([1, 2, 3, 2], 997)", "wait:2,trace:3,trace:1")]
    [InlineData("1.0.0.0.0.0.3.0.0",
        "v1((v2, v3), v4) = [v2, v3, v4]\nv1((trace(1), wait(2)), trace(3), wait(4))\n997",
        "error ArityMismatch", "")]
    [InlineData("2.1.0.0.0.2.0.1.2.0",
        "v1((\n  (\n    (\n      1,\n      v3),\n    v4),\n  v5)) = [1, v3, v4, v5]\nv1((((v6, v7), v8), v9)) = [2, v6, v7, v8, v9]\nv1((((trace(2), wait(2)), trace(3)), wait(4)))\n997",
        "value ([2, 2, 2, 3, 4], 997)", "trace:2,wait:2,trace:3,wait:4")]
    [InlineData("5.1.0.0.0.0",
        "v1(((v2, v3), v4)) = [1, v2, v3, v4]\nv1(( ( v5 , v6 ) , v7 )) = [2, v5, v6, v7]\nv1(((trace(1), wait(2)), trace(3)))\n997",
        "refusal DuplicateBranchPattern/syntax", "")]
    public void TheWideRecipe_ConstructsItsExpectationFromTheDemandLaws(string choices, string source, string outcome, string events)
    {
        var id = "sem2b/v1/seed-nested-wide/all/" + choices;
        Assert.Contains(id, Wide.Value.Programs.Select(static p => p.CaseId));
        Assert.True(SemanticCorpus.TryBuilder(id, SemanticRecipe.RecipeVersion, out var builder, out var problem), problem);
        var c = builder.Build();
        Assert.Equal(source, c.Source);
        var e = c.Expected;
        Assert.Equal(outcome, e.Kind switch
        {
            SemanticCaseKind.ValidSuccess => "value " + Render(e.Value!),
            SemanticCaseKind.ValidRuntimeFailure => "error " + e.ErrorCategory,
            _ => $"refusal {e.Diagnostic}/{e.DiagnosticPhase}",
        });
        Assert.Equal(events, string.Join(",", e.Events));
        var result = SemanticRunner.Run(c);
        Assert.True(result.Passed, string.Join("; ", result.Findings));
        if (choices == "1.1.0.0.1.0.0.1.0.0") Assert.True(c.Paths.HasFlag(SemanticPath.LazyTransport), c.Paths.ToString());
        if (choices == "1.0.0.0.0.0.3.0.0") Assert.Equal(SemanticPath.CardinalityBeforeDemand, c.Paths);

        static string Render(Result value) => value switch
        {
            Result.Atom atom => atom.Value.ToString(CultureInfo.InvariantCulture),
            Result.ListValue list => "[" + string.Join(", ", list.Items.Select(Render)) + "]",
            Result.SequenceValue sequence => "(" + string.Join(", ", sequence.Items.Select(Render)) + ")",
            _ => throw new ArgumentOutOfRangeException(nameof(value), value, "not a constructed value"),
        };
    }
}
