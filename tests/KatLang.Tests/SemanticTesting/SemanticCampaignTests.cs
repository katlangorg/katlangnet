using System.Collections.Immutable;
using System.Globalization;
using System.Text.Json;
using KatLang.ParserFuzz;
using Xunit.Abstractions;

namespace KatLang.Tests.SemanticTesting;

/// <summary>
/// SEM-2C structure-aware reduction and the bounded <c>semantic-campaign</c> (fuzz/README.md
/// § Reduction, § Campaigns): the generator's recorded spans are well-formed derived metadata that
/// never change a replay; the span moves reduce a known multi-fragment shape strictly further than
/// the block moves alone; a campaign over a tiny seed range is deterministic and stops at its case
/// and time budgets; a planted failure (the runner's inert observation seam) is found, persisted with
/// its signature and reduced — in process, through the command's argument parsing, and once through
/// supervised children. <c>--recipe seed-nested</c> searches the nested-pattern recipe the same way:
/// its campaign is deterministic and records its recipe, its ids replay through
/// <c>semantic-replay</c>, and a planted nested failure is found, persisted and reduced.
/// </summary>
public class SemanticCampaignTests(ITestOutputHelper output)
{
    /// <summary>The planted failing shape: a wrong value on <c>base@sync-optimized</c> whenever the source contains it.</summary>
    private const string Trigger = ".Arguments";

    /// <summary>A 3-fragment seeded success whose trigger sits in its first fragment (the README's block-limitation example).</summary>
    private const string KnownShape = "sem2b/v1/seed/5EED2B000001/1";

    private const ulong Seed = 0x5EED_2B00_0001UL;

    private static readonly SemanticFailureSignature Planted =
        new(SemanticVerdict.Mismatch, SemanticMember.BaseRole, SemanticProfiles.SyncOptimized, "value");

    private static SemanticCaseResult FaultyRun(SemanticCase c)
        => SemanticRunner.Run(c, c.Source.Contains(Trigger, StringComparison.Ordinal) ? SemanticReductionTests.WrongValue : null);

    private static SemanticCaseBuilder Builder(string caseId)
    {
        Assert.True(SemanticCorpus.TryBuilder(caseId, SemanticRecipe.RecipeVersion, out var builder, out var problem), problem);
        return builder;
    }

    private static readonly string[] SpanIds =
    [
        KnownShape,
        "sem2b/v1/seed/5EED2B000003/3",
        "sem2b/v1/seed/5EED2B000006/15",
        "sem2b/v1/seed-nested/5EED2B000001/2",
        "sem2b/v1/sys/meta/0",
        "sem2b/v1/sys/triple/collect+meta+failure-fail",
    ];

    // ── Spans ───────────────────────────────────────────────────────────────

    /// <summary>
    /// Spans lie inside the recorded sequence, nest properly, have earlier governors, and a seeded
    /// case has one fragment span per root fragment. Recording them changes nothing: a plain replay
    /// of the recorded values (no span observer at all) rebuilds the identical case, and a recorded
    /// replay reproduces the same trace AND the same spans.
    /// </summary>
    [Fact]
    public void Spans_AreWellFormedDerivedMetadata_AndNeverChangeAReplay()
    {
        foreach (var id in SpanIds)
        {
            var builder = Builder(id);
            var recorder = new RecordingChooser(builder.NewChooser());
            var built = builder.Build(recorder);
            var spans = recorder.Spans;
            Assert.NotEmpty(spans);
            for (var i = 0; i < spans.Length; i++)
            {
                var span = spans[i];
                Assert.Equal(i, span.Ordinal);
                Assert.Contains(span.Kind, new[] { "fragment", "production", "context" });
                Assert.InRange(span.Start, 0, recorder.Choices.Length);
                Assert.InRange(span.End, span.Start, recorder.Choices.Length);
                Assert.True(span.Governor < span.Start, $"{id}: {span} has a later governor");
                foreach (var other in spans.Take(i))
                    Assert.True(other.End <= span.Start || (other.Start <= span.Start && span.End <= other.End), $"{id}: {other} and {span} overlap");
            }

            if (id.Contains("/seed/", StringComparison.Ordinal))
            {
                Assert.Equal(built.Fragments, spans.Count(s => s.Kind == "fragment"));
                Assert.All(spans.Where(s => s.Kind == "fragment"), s => Assert.Equal(0, s.Governor)); // compose.count
            }

            var plain = builder.Build(new ReplayingChooser(SemanticReducer.Values(recorder.Choices)));
            Assert.Equal(SemanticDescriptor.Write(built.Case), SemanticDescriptor.Write(plain.Case));
            var replay = new RecordingChooser(new ReplayingChooser(SemanticReducer.Values(recorder.Choices)));
            Assert.Equal(SemanticDescriptor.Write(built.Case), SemanticDescriptor.Write(builder.Build(replay).Case));
            Assert.Equal(recorder.Choices.ToArray(), replay.Choices.ToArray());
            Assert.Equal(spans.ToArray(), replay.Spans.ToArray());
        }

        // The corpus builds are untouched: the fixed-corpus digest pinned before spans existed.
        var pathBlock = SemanticRecipe.CasePrefix + "sys/path/";
        Assert.Equal(SemanticReductionTests.FixedCorpusDigest,
            SemanticReductionTests.CorpusDigest(SemanticCorpus.All().Where(c => !c.CaseId.StartsWith(pathBlock, StringComparison.Ordinal))));
    }

    /// <summary>
    /// The minimal alternative of a span keeps the prefix, generates every decision inside the span as
    /// 0, and resumes with the decisions after it; its trace is an ordinary sequence that replays alone.
    /// </summary>
    [Fact]
    public void SpanReplacement_GeneratesTheMinimalAlternative_AndItsTraceReplaysPlainly()
    {
        var builder = Builder(KnownShape);
        var recorder = new RecordingChooser(builder.NewChooser());
        _ = builder.Build(recorder);
        var values = SemanticReducer.Values(recorder.Choices);
        var production = recorder.Spans.First(s => s.Kind == "production" && s.Length > 1);

        var replaced = new RecordingChooser(new SpanReplacingChooser(values, production.Ordinal, production.End));
        var built = builder.Build(replaced);
        var span = replaced.Spans[production.Ordinal];
        Assert.Equal(production.Start, span.Start);
        Assert.Equal(values.Take(production.Start), SemanticReducer.Values(replaced.Choices).Take(production.Start));
        Assert.All(replaced.Choices.Skip(span.Start).Take(span.Length), c => Assert.Equal(0, c.Value));
        Assert.Equal(values[production.End], replaced.Choices[span.End].Value); // resumes after the original span

        var plain = builder.Build(new ReplayingChooser(SemanticReducer.Values(replaced.Choices)));
        Assert.Equal(SemanticDescriptor.Write(built.Case), SemanticDescriptor.Write(plain.Case));
    }

    /// <summary>
    /// The known shape — three fragments, the trigger in the first — reduces strictly further with the
    /// span moves: the block moves alone keep all three fragments (306 -> 169 characters), the span
    /// moves delete whole fragments with their governing count (306 -> 74, one fragment). Both keep the
    /// signature, both reach their fixpoint within the bound, and the span reduction is deterministic.
    /// </summary>
    [Fact]
    public void SpanMoves_ReduceAKnownShapeStrictlyFurtherThanBlockMovesAlone()
    {
        var bounds = new SemanticReductionOptions { MaxAttempts = 200, Runner = FaultyRun };
        var withSpans = SemanticReducer.Reduce(Builder(KnownShape), bounds);
        var blocksOnly = SemanticReducer.Reduce(Builder(KnownShape), bounds with { SpanMoves = false });
        output.WriteLine("spans:  " + withSpans.Describe());
        output.WriteLine("blocks: " + blocksOnly.Describe());
        output.WriteLine(withSpans.Reduced.Source);

        Assert.Equal(3, withSpans.OriginalSize.Fragments);
        foreach (var result in new[] { withSpans, blocksOnly })
        {
            Assert.Equal(SemanticReductionStatus.Reduced, result.Status);
            Assert.Equal(Planted, result.Signature);
            Assert.False(result.AttemptLimitReached);
            Assert.Empty(result.GenerationFailures);
            Assert.Equal(Planted, SemanticFailureSignature.Of(FaultyRun(result.Reduced)));
        }

        Assert.True(withSpans.ReducedSize.CompareTo(blocksOnly.ReducedSize) < 0, $"{withSpans.ReducedSize} is not smaller than {blocksOnly.ReducedSize}");
        Assert.Equal(3, blocksOnly.ReducedSize.Fragments);
        Assert.Equal(1, withSpans.ReducedSize.Fragments);
        Assert.Contains(withSpans.Accepted, s => s.Move.StartsWith("delete fragment span", StringComparison.Ordinal));
        Assert.DoesNotContain(blocksOnly.Accepted, s => s.Move.Contains("span", StringComparison.Ordinal));
        Assert.Equal(1, withSpans.ReducedSpans.Count(s => s.Kind == "fragment"));

        // Deterministic, and the record is still v1: it regenerates the reduced case through TryRebuild.
        var again = SemanticReducer.Reduce(Builder(KnownShape), bounds);
        var record = SemanticReduction.WriteRecord(SemanticReduction.RecordOf(withSpans));
        Assert.Equal(record, SemanticReduction.WriteRecord(SemanticReduction.RecordOf(again)));
        Assert.Contains("\"formatVersion\": 1", record, StringComparison.Ordinal);
        Assert.True(SemanticReduction.TryParseRecord(record, out var parsed, out var problem), problem);
        Assert.True(SemanticReduction.TryRebuild(parsed, out var rebuilt, out problem), problem);
        Assert.Equal(withSpans.Reduced.Source, rebuilt.Source);
    }

    // ── Campaign ────────────────────────────────────────────────────────────

    private static SemanticCampaignOptions Tiny(string outDir) => new()
    {
        FirstSeed = Seed,
        LastSeed = Seed + 1,
        CasesPerSeed = 2,
        MaxCases = 3,
        OutputDirectory = outDir,
        InProcessRunner = static c => SemanticRunner.Run(c),
    };

    private static string[] Listing(string root)
        => [.. Directory.GetFiles(root, "*", SearchOption.AllDirectories).Select(f => Path.GetRelativePath(root, f).Replace('\\', '/')).Order(StringComparer.Ordinal)];

    /// <summary>
    /// A tiny range (2 seeds x 2 cases = 4 planned) under a 3-case budget covers exactly the first
    /// three ids in seed-then-index order, stops with <c>case-budget</c> and names the first uncovered
    /// id; two runs write byte-identical summaries and the same files.
    /// </summary>
    [Fact]
    public void ACampaign_OverATinyRange_IsDeterministicAndStopsAtItsCaseBudget()
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-campaign-");
        try
        {
            var first = SemanticCampaign.Run(Tiny(Path.Combine(root.FullName, "a")), TextWriter.Null);
            var second = SemanticCampaign.Run(Tiny(Path.Combine(root.FullName, "b")), TextWriter.Null);
            output.WriteLine(first.Describe());

            Assert.Equal([(Seed, 0), (Seed, 1), (Seed + 1, 0), (Seed + 1, 1)], SemanticCampaign.Plan(Tiny("x")).ToArray());
            Assert.Equal(4, first.Planned);
            Assert.Equal(3, first.Executed);
            Assert.Equal(SemanticCampaignStop.CaseBudget, first.Stop);
            Assert.Equal(SemanticCampaign.CaseId(Seed + 1, 0), first.LastCovered);
            Assert.Equal(SemanticCampaign.CaseId(Seed + 1, 1), first.FirstUncovered);
            Assert.Equal(3, first.Passed);
            Assert.Empty(first.Failures);

            var a = File.ReadAllText(Path.Combine(root.FullName, "a", SemanticCampaign.SummaryFile));
            Assert.Equal(a, File.ReadAllText(Path.Combine(root.FullName, "b", SemanticCampaign.SummaryFile)));
            Assert.Equal(Listing(Path.Combine(root.FullName, "a")), Listing(Path.Combine(root.FullName, "b")));
            Assert.Equal([SemanticCampaign.SummaryFile], Listing(Path.Combine(root.FullName, "a")));
            Assert.Contains("\"stop\": \"case-budget\"", a, StringComparison.Ordinal);
            Assert.Contains("\"firstUncovered\": \"sem2b/v1/seed/5EED2B000002/1\"", a, StringComparison.Ordinal);
            Assert.DoesNotContain(root.FullName.Replace('\\', '/'), a.Replace("\\\\", "/"), StringComparison.OrdinalIgnoreCase);
            Assert.Equal(first.Verdicts, second.Verdicts);

            // The whole plan without a binding budget: completed, nothing uncovered.
            var all = SemanticCampaign.Run(Tiny(Path.Combine(root.FullName, "c")) with { MaxCases = 10 }, TextWriter.Null);
            Assert.Equal(SemanticCampaignStop.Completed, all.Stop);
            Assert.Equal(4, all.Executed);
            Assert.Null(all.FirstUncovered);

            // A used output directory is refused: a campaign only ever writes into a new or empty one.
            Assert.Throws<IOException>(() => SemanticCampaign.Run(Tiny(Path.Combine(root.FullName, "a")), TextWriter.Null));
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    /// <summary>
    /// The time budget is checked before every case: with a clock that advances one second per reading
    /// and a two-second budget, the campaign stops with <c>time-budget</c> after the cases it began in time.
    /// </summary>
    [Fact]
    public void ACampaign_StopsAtItsTimeBudget_AndReportsWhatItCovered()
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-campaign-time-");
        try
        {
            var ticks = 0;
            var result = SemanticCampaign.Run(Tiny(root.FullName) with
            {
                MaxCases = 10,
                MaxTime = TimeSpan.FromSeconds(2),
                Clock = () => TimeSpan.FromSeconds(ticks++),
            }, TextWriter.Null);
            Assert.Equal(SemanticCampaignStop.TimeBudget, result.Stop);
            Assert.Equal(2, result.Executed); // the readings 0 and 1 are inside the budget, 2 is not
            Assert.Equal(SemanticCampaign.CaseId(Seed + 1, 0), result.FirstUncovered);
            Assert.Contains("\"stop\": \"time-budget\"", File.ReadAllText(Path.Combine(root.FullName, SemanticCampaign.SummaryFile)), StringComparison.Ordinal);
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    [Fact]
    public void TheTimeBudget_StopsAnActiveReduction_BeforeAnotherCandidateRuns()
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-reduction-time-");
        try
        {
            var executions = 0;
            var elapsed = TimeSpan.Zero;
            var result = SemanticCampaign.Run(Tiny(root.FullName) with
            {
                MaxTime = TimeSpan.FromSeconds(2),
                Clock = () => elapsed,
                InProcessRunner = c =>
                {
                    Assert.True(elapsed < TimeSpan.FromSeconds(2), "a new execution started after the time budget");
                    var judged = FaultyRun(c);
                    // Two searched cases, the original's recheck, then one reduction candidate.
                    if (++executions == 4) elapsed = TimeSpan.FromSeconds(2);
                    return judged;
                },
            }, TextWriter.Null);

            Assert.Equal(4, executions);
            Assert.Equal(2, result.Executed);
            Assert.Equal(SemanticCampaignStop.TimeBudget, result.Stop);
            Assert.Equal(SemanticCampaign.CaseId(Seed + 1, 0), result.FirstUncovered);
            var failure = Assert.Single(result.Failures);
            Assert.Equal(Planted, failure.Signature);
            Assert.Equal(1, failure.ReductionAttempts);
            Assert.Equal("time budget exhausted", failure.ReductionStopped);
            Assert.NotNull(failure.ReductionRecord);
            Assert.True(SemanticReduction.TryParseRecord(File.ReadAllText(Path.Combine(root.FullName, failure.ReductionRecord)), out var record, out var problem), problem);
            Assert.True(SemanticReduction.TryRebuild(record, out _, out problem), problem);
            Assert.Contains("\"stopped\": \"time budget exhausted\"", File.ReadAllText(Path.Combine(root.FullName, SemanticCampaign.SummaryFile)), StringComparison.Ordinal);
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AFailure_ThatDoesNotReproduceItsOriginalSignature_IsNotReduced(bool differentFailure)
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-changed-failure-");
        try
        {
            var executions = 0;
            var result = SemanticCampaign.Run(Tiny(root.FullName) with
            {
                LastSeed = Seed,
                InProcessRunner = c => ++executions <= 2 ? FaultyRun(c)
                    : differentFailure ? new SemanticCaseResult(c.CaseId, SemanticVerdict.Crash, ["planted different failure"], [], SemanticPath.None, [], [])
                    : SemanticRunner.Run(c),
            }, TextWriter.Null);

            Assert.Equal(3, executions); // No candidates are judged for the changed baseline.
            var failure = Assert.Single(result.Failures);
            Assert.Equal(Planted, failure.Signature);
            Assert.Equal(nameof(SemanticReductionStatus.NothingToReduce), failure.ReductionStatus);
            Assert.Contains(differentFailure ? "Crash" : "Passed", failure.ReductionSkipped, StringComparison.Ordinal);
            Assert.Null(failure.ReducedDescriptor);
            Assert.Null(failure.ReductionRecord);
            Assert.Empty(Directory.GetFiles(root.FullName, "*.reduction.json", SearchOption.AllDirectories));
            Assert.True(File.Exists(Path.Combine(root.FullName, failure.Descriptor)));
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    /// <summary>
    /// A planted failure is found, persisted and reduced through the COMMAND (argument parsing, exit
    /// code, output layout): seed 5EED2B000001 index 1 carries the trigger, index 0 does not. The
    /// failure descriptor replays to the same signature under the fault, the signature sidecar names
    /// it, and the reduced record is a v1 record that regenerates a strictly smaller case with the
    /// same signature. <c>--no-reduce</c> persists the failure and writes no reduction.
    /// </summary>
    [Fact]
    public void APlantedFailure_IsFoundPersistedAndReduced_ThroughTheCommand()
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-campaign-planted-");
        try
        {
            var outDir = Path.Combine(root.FullName, "out");
            var log = new StringWriter();
            var exit = SemanticCampaign.RunCampaign(
                ["semantic-campaign", "--seeds", "5EED2B000001", "--cases-per-seed", "2", "--max-cases", "8", "--max-attempts", "200", "--out", outDir],
                log, o => o with { InProcessRunner = FaultyRun });
            output.WriteLine(log.ToString());
            Assert.Equal(1, exit);

            var summary = File.ReadAllText(Path.Combine(outDir, SemanticCampaign.SummaryFile));
            output.WriteLine(summary);
            Assert.Contains("\"executed\": 2", summary, StringComparison.Ordinal);
            Assert.Contains("\"failed\": 1", summary, StringComparison.Ordinal);
            Assert.Contains("\"stop\": \"completed\"", summary, StringComparison.Ordinal);

            var safe = SemanticReplay.SafeName(KnownShape);
            var descriptor = Path.Combine(outDir, "failures", safe + ".json");
            Assert.True(SemanticDescriptor.TryParse(File.ReadAllText(descriptor), out var parsed, out var problem), problem);
            Assert.Equal(KnownShape, parsed.Case.CaseId);
            Assert.Equal("Mismatch", parsed.RecordedVerdict);
            Assert.Equal(Planted, SemanticFailureSignature.Of(SemanticReplay.Replay(File.ReadAllText(descriptor), SemanticReplay.Mode.Recipe, SemanticReductionTests.WrongValue).Result!));
            var signature = File.ReadAllText(Path.Combine(outDir, "failures", safe + ".signature.json"));
            Assert.Contains("\"facet\": \"value\"", signature, StringComparison.Ordinal);
            Assert.Contains("\"profile\": \"" + SemanticProfiles.SyncOptimized + "\"", signature, StringComparison.Ordinal);
            // Campaign sidecars are metadata; directory replay must select only the descriptor.
            Assert.Equal(0, SemanticReplay.RunReplay(["semantic-replay", Path.Combine(outDir, "failures")]));

            var recordPath = Assert.Single(Directory.GetFiles(Path.Combine(outDir, "reduced", safe), "*.reduction.json"));
            Assert.True(SemanticReduction.TryParseRecord(File.ReadAllText(recordPath), out var record, out problem), problem);
            Assert.Equal(KnownShape, record.OriginalCaseId);
            Assert.Equal(Planted, record.Signature);
            Assert.Equal(nameof(SemanticReductionStatus.Reduced), record.Status);
            Assert.False(record.Supervised);
            Assert.True(record.ReducedSize.CompareTo(record.OriginalSize) < 0);
            Assert.Equal(1, record.ReducedSize.Fragments);
            Assert.True(SemanticReduction.TryRebuild(record, out var reduced, out problem), problem);
            Assert.Equal(Planted, SemanticFailureSignature.Of(FaultyRun(reduced)));
            Assert.True(File.Exists(recordPath[..^".reduction.json".Length] + ".json"));
            Assert.Contains("\"reducedCaseId\": \"" + record.ReducedCaseId + "\"", summary, StringComparison.Ordinal);
            Assert.Contains("\"originalSourceLength\": " + record.OriginalSize.SourceLength.ToString(CultureInfo.InvariantCulture), summary, StringComparison.Ordinal);
            Assert.False(Directory.Exists(Path.Combine(outDir, "work")), "an in-process campaign dispatches no worker");

            // --no-reduce: the failure is persisted, nothing is reduced.
            var noReduce = Path.Combine(root.FullName, "no-reduce");
            Assert.Equal(1, SemanticCampaign.RunCampaign(
                ["semantic-campaign", "--seeds", "5EED2B000001", "--cases-per-seed", "2", "--no-reduce", "--out", noReduce],
                TextWriter.Null, o => o with { InProcessRunner = FaultyRun }));
            Assert.True(File.Exists(Path.Combine(noReduce, "failures", safe + ".json")));
            Assert.False(Directory.Exists(Path.Combine(noReduce, "reduced")));
            Assert.Contains("\"skipped\": \"disabled (--no-reduce)\"", File.ReadAllText(Path.Combine(noReduce, SemanticCampaign.SummaryFile)), StringComparison.Ordinal);

            // Without the fault the same range passes.
            Assert.Equal(0, SemanticCampaign.RunCampaign(
                ["semantic-campaign", "--seeds", "5EED2B000001", "--cases-per-seed", "2", "--out", Path.Combine(root.FullName, "clean")],
                TextWriter.Null, o => o with { InProcessRunner = static c => SemanticRunner.Run(c) }));
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    // ── Recipes ─────────────────────────────────────────────────────────────

    /// <summary>The planted nested shape: the OUTER-LIST nested pattern head <c>[(a, *rest), z]</c>.</summary>
    private const string NestedTrigger = "[(";

    /// <summary>The nested ids of the first fixed-corpus seed; indices 0-3 are the fixed corpus's own nested cases.</summary>
    private const string NestedIds = "sem2b/v1/seed-nested/5EED2B000001/";

    private static SemanticCaseResult NestedFaultyRun(SemanticCase c)
        => SemanticRunner.Run(c, c.Source.Contains(NestedTrigger, StringComparison.Ordinal) ? SemanticReductionTests.WrongValue : null);

    /// <summary>
    /// <c>--recipe</c>: the default is <c>seed</c> (its default output directory keeps its name), both
    /// recipe names parse, the nested default output directory is prefixed by its recipe, an unknown
    /// name is a usage problem, and every recipe name is the id segment <c>TryBuilder</c> rebuilds.
    /// </summary>
    [Fact]
    public void TheRecipeOption_DefaultsToSeed_AndEveryRecipeNameIsARebuildableIdSegment()
    {
        Assert.Equal(["seed", "seed-nested"], SemanticCorpus.SeededRecipes.ToArray());
        Assert.True(SemanticCampaign.TryParse(["semantic-campaign", "--seeds", "0x10..12"], out var byDefault, out var problem), problem);
        Assert.Equal(SemanticCorpus.SeedRecipe, byDefault.Recipe);
        Assert.True(SemanticCampaign.TryParse(["semantic-campaign", "--seeds", "0x10..12", "--recipe", "seed"], out var named, out problem), problem);
        Assert.Equal(SemanticCorpus.SeedRecipe, named.Recipe);
        Assert.Contains("/artifacts/semantic-campaign/10-12x16-", named.OutputDirectory.Replace('\\', '/'), StringComparison.Ordinal);

        Assert.True(SemanticCampaign.TryParse(["semantic-campaign", "--recipe", "seed-nested", "--seeds", "0x10..12"], out var nested, out problem), problem);
        Assert.Equal(SemanticCorpus.NestedSeedRecipe, nested.Recipe);
        Assert.Equal((0x10UL, 0x12UL, 3L * SemanticCampaignOptions.DefaultCasesPerSeed), (nested.FirstSeed, nested.LastSeed, nested.PlannedCases));
        Assert.Contains("/artifacts/semantic-campaign/seed-nested-10-12x16-", nested.OutputDirectory.Replace('\\', '/'), StringComparison.Ordinal);
        Assert.Null(nested.Problem());
        Assert.Equal(SemanticCampaign.Plan(byDefault).ToArray(), SemanticCampaign.Plan(nested).ToArray()); // the plan is recipe-independent

        Assert.False(SemanticCampaign.TryParse(["semantic-campaign", "--seeds", "1", "--recipe", "nested"], out _, out problem));
        Assert.Contains("seed, seed-nested", problem, StringComparison.Ordinal);
        Assert.Contains("[--recipe seed|seed-nested]", SemanticCampaign.Usage, StringComparison.Ordinal);
        Assert.NotNull((byDefault with { Recipe = "nested" }).Problem()); // the seam path is validated too

        foreach (var recipe in SemanticCorpus.SeededRecipes)
        {
            var id = SemanticCampaign.CaseId(0x10, 3, recipe);
            Assert.Equal("sem2b/v1/" + recipe + "/10/3", id);
            Assert.True(SemanticCorpus.TryBuilder(id, SemanticRecipe.RecipeVersion, out var builder, out problem), problem);
            Assert.Equal(id, builder.CaseId);
        }

        Assert.Equal(SemanticCampaign.CaseId(0x10, 3), SemanticCampaign.CaseId(0x10, 3, SemanticCorpus.SeedRecipe));
    }

    /// <summary>
    /// <c>--recipe seed-nested</c> plans the same (seed, index) pairs as the default and executes exactly
    /// the nested recipe's own cases, in order. Two runs write byte-identical summaries and the same
    /// files; the summary records the recipe and differs from the default recipe's summary over the same
    /// range and budget ONLY by the recipe name (the <c>recipe</c> field and the ids). An unknown recipe
    /// is refused before anything is written.
    /// </summary>
    [Fact]
    public void ANestedCampaign_ExecutesTheNestedRecipesOwnCases_AndIsDeterministic()
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-campaign-nested-");
        try
        {
            var executed = new List<SemanticCase>();
            SemanticCampaignOptions Nested(string name) => Tiny(Path.Combine(root.FullName, name)) with
            {
                Recipe = SemanticCorpus.NestedSeedRecipe,
                InProcessRunner = c =>
                {
                    executed.Add(c);
                    return SemanticRunner.Run(c);
                },
            };

            var first = SemanticCampaign.Run(Nested("a"), TextWriter.Null);
            var second = SemanticCampaign.Run(Nested("b"), TextWriter.Null);
            var seeded = SemanticCampaign.Run(Tiny(Path.Combine(root.FullName, "seed")), TextWriter.Null);
            output.WriteLine(first.Describe());

            string[] ids = [NestedIds + "0", NestedIds + "1", "sem2b/v1/seed-nested/5EED2B000002/0"];
            Assert.Equal([.. ids, .. ids], executed.Select(c => c.CaseId).ToArray());
            (ulong Seed, int Index)[] pairs = [(Seed, 0), (Seed, 1), (Seed + 1, 0)];
            foreach (var ((seed, index), ran) in pairs.Zip(executed))
            {
                Assert.Equal(SemanticCampaign.CaseId(seed, index, SemanticCorpus.NestedSeedRecipe), ran.CaseId);
                Assert.Equal(SemanticDescriptor.Write(SemanticCorpus.NestedSeededCase(seed, index)), SemanticDescriptor.Write(ran));
                Assert.Contains(ran.Features, f => f == "nested-pattern");
            }

            Assert.Equal(SemanticCorpus.NestedSeedRecipe, first.Options.Recipe);
            Assert.Equal((4L, 3, 3), (first.Planned, first.Executed, first.Passed));
            Assert.Equal(SemanticCampaignStop.CaseBudget, first.Stop);
            Assert.Equal(ids[2], first.LastCovered);
            Assert.Equal("sem2b/v1/seed-nested/5EED2B000002/1", first.FirstUncovered);
            Assert.Empty(first.Failures);
            Assert.Equal(first.Verdicts, second.Verdicts);

            var a = File.ReadAllText(Path.Combine(root.FullName, "a", SemanticCampaign.SummaryFile));
            Assert.Equal(a, File.ReadAllText(Path.Combine(root.FullName, "b", SemanticCampaign.SummaryFile)));
            Assert.Equal(Listing(Path.Combine(root.FullName, "a")), Listing(Path.Combine(root.FullName, "b")));
            Assert.Equal([SemanticCampaign.SummaryFile], Listing(Path.Combine(root.FullName, "a")));
            Assert.Contains("\"recipe\": \"seed-nested\"", a, StringComparison.Ordinal);
            Assert.Contains("\"firstUncovered\": \"sem2b/v1/seed-nested/5EED2B000002/1\"", a, StringComparison.Ordinal);

            // The default recipe over the same range: the same summary apart from the recipe name.
            var s = File.ReadAllText(Path.Combine(root.FullName, "seed", SemanticCampaign.SummaryFile));
            Assert.Equal(SemanticCorpus.SeedRecipe, seeded.Options.Recipe);
            Assert.Contains("\"recipe\": \"seed\"", s, StringComparison.Ordinal);
            Assert.DoesNotContain("seed-nested", s, StringComparison.Ordinal);
            Assert.Equal(s, a.Replace("seed-nested", "seed", StringComparison.Ordinal));

            var refused = Path.Combine(root.FullName, "refused");
            Assert.Throws<ArgumentException>(() => SemanticCampaign.Run(Tiny(refused) with { Recipe = "nested" }, TextWriter.Null));
            Assert.False(Directory.Exists(refused));
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    /// <summary>
    /// Every id a nested campaign plans is an ordinary recipe id: <c>semantic-export</c> writes its
    /// descriptor from the id alone, and <c>semantic-replay</c> replays that descriptor in recipe mode
    /// (rebuilt from the id and drift-checked) and from its exact sources.
    /// </summary>
    [Fact]
    public void TheIdsOfANestedCampaign_ReplayThroughSemanticReplay()
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-campaign-nested-replay-");
        try
        {
            var options = Tiny("unused") with { Recipe = SemanticCorpus.NestedSeedRecipe, CasesPerSeed = 3 };
            var ids = SemanticCampaign.Plan(options).Select(p => SemanticCampaign.CaseId(p.Seed, p.Index, options.Recipe)).ToArray();
            Assert.Equal(6, ids.Length);
            foreach (var id in ids)
            {
                Assert.StartsWith("sem2b/v1/seed-nested/", id, StringComparison.Ordinal);
                var file = Path.Combine(root.FullName, SemanticReplay.SafeName(id) + ".json");
                Assert.Equal(0, SemanticReplay.RunExport(["semantic-export", id, file]));
                var outcome = SemanticReplay.Replay(File.ReadAllText(file), SemanticReplay.Mode.Recipe);
                Assert.True(outcome.Passed, outcome.Report);
                Assert.Equal(id, outcome.CaseId);
                Assert.StartsWith("[recipe] ", outcome.Report, StringComparison.Ordinal);
            }

            Assert.Equal(ids.Length, Directory.GetFiles(root.FullName, "*.json").Length);
            Assert.Equal(0, SemanticReplay.RunReplay(["semantic-replay", root.FullName]));
            Assert.Equal(0, SemanticReplay.RunReplay(["semantic-replay", "--exact-source", root.FullName]));
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    /// <summary>
    /// A planted nested failure is found, persisted and reduced through the COMMAND with
    /// <c>--recipe seed-nested</c>. Of the four nested cases of seed 5EED2B000001, indices 1 and 3 carry
    /// the outer-list pattern: index 1 (a success) fails with a wrong value, index 3 (the
    /// wrong-inner-kind runtime failure) with a wrong outcome; indices 0 and 2 (outer sequence) pass.
    /// Each failure names its recipe in the summary and in its signature sidecar, its descriptor
    /// replays through <c>semantic-replay</c> and reproduces its signature under the fault, and its
    /// reduction is a strictly smaller NESTED case with the same signature and the two-context stack
    /// cut to the single list context every nested case has (measured: 97 -> 82 and 95 -> 66
    /// characters). The default recipe over the same range searches no nested id.
    /// </summary>
    [Fact]
    public void APlantedNestedFailure_IsFoundPersistedAndReduced_ThroughTheCommand()
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-campaign-nested-planted-");
        try
        {
            var outDir = Path.Combine(root.FullName, "out");
            var log = new StringWriter();
            var exit = SemanticCampaign.RunCampaign(
                ["semantic-campaign", "--recipe", "seed-nested", "--seeds", "5EED2B000001", "--cases-per-seed", "4", "--max-attempts", "200", "--out", outDir],
                log, o => o with { InProcessRunner = NestedFaultyRun });
            output.WriteLine(log.ToString());
            Assert.Equal(1, exit);
            Assert.Contains("semantic-campaign: recipe seed-nested, seeds 5EED2B000001..5EED2B000001 x 4:", log.ToString(), StringComparison.Ordinal);

            var summary = File.ReadAllText(Path.Combine(outDir, SemanticCampaign.SummaryFile));
            output.WriteLine(summary);
            using var document = JsonDocument.Parse(summary);
            var json = document.RootElement;
            Assert.Equal("seed-nested", json.GetProperty("recipe").GetString());
            Assert.Equal((4, 2, 2), (json.GetProperty("executed").GetInt32(), json.GetProperty("passed").GetInt32(), json.GetProperty("failed").GetInt32()));
            Assert.Equal("completed", json.GetProperty("stop").GetString());
            Assert.Equal(NestedIds + "3", json.GetProperty("lastCovered").GetString());
            var failures = json.GetProperty("failures").EnumerateArray().ToArray();
            Assert.Equal(2, failures.Length);

            (string Index, string Facet)[] planted = [("1", "value"), ("3", "outcome")];
            foreach (var ((index, facet), failure) in planted.Zip(failures))
            {
                var id = NestedIds + index;
                var signature = Planted with { Facet = facet };
                Assert.Equal(id, failure.GetProperty("caseId").GetString());
                Assert.Equal("seed-nested", failure.GetProperty("recipe").GetString());
                Assert.Equal(facet, failure.GetProperty("signature").GetProperty("facet").GetString());

                // The persisted descriptor is an ordinary recipe descriptor that fails the planted way.
                var safe = SemanticReplay.SafeName(id);
                Assert.Equal("failures/" + safe + ".json", failure.GetProperty("descriptor").GetString());
                var descriptor = File.ReadAllText(Path.Combine(outDir, "failures", safe + ".json"));
                Assert.True(SemanticDescriptor.TryParse(descriptor, out var parsed, out var problem), problem);
                Assert.Equal(id, parsed.Case.CaseId);
                Assert.Equal("Mismatch", parsed.RecordedVerdict);
                Assert.Contains(NestedTrigger, parsed.Case.Source, StringComparison.Ordinal);
                Assert.Equal(signature, SemanticFailureSignature.Of(SemanticReplay.Replay(descriptor, SemanticReplay.Mode.Recipe, SemanticReductionTests.WrongValue).Result!));

                using var sidecar = JsonDocument.Parse(File.ReadAllText(Path.Combine(outDir, "failures", safe + ".signature.json")));
                Assert.Equal(id, sidecar.RootElement.GetProperty("caseId").GetString());
                Assert.Equal("seed-nested", sidecar.RootElement.GetProperty("recipe").GetString());
                Assert.Equal(facet, sidecar.RootElement.GetProperty("signature").GetProperty("facet").GetString());

                // The reduction: a strictly smaller nested case, same signature, rebuilt from its v1 record.
                var reduction = failure.GetProperty("reduction");
                Assert.Equal(nameof(SemanticReductionStatus.Reduced), reduction.GetProperty("status").GetString());
                var recordPath = Path.Combine(outDir, reduction.GetProperty("record").GetString()!);
                Assert.True(SemanticReduction.TryParseRecord(File.ReadAllText(recordPath), out var record, out problem), problem);
                Assert.Equal(id, record.OriginalCaseId);
                Assert.Equal(signature, record.Signature);
                Assert.Equal(nameof(SemanticReductionStatus.Reduced), record.Status);
                Assert.False(record.Supervised);
                Assert.True(record.ReducedSize.CompareTo(record.OriginalSize) < 0);
                Assert.True(record.ReducedSize.Declarations < record.OriginalSize.Declarations, "no context declaration was removed");
                Assert.StartsWith("sem2b/v1/reduced/seed-nested/5EED2B000001/" + index + "/", record.ReducedCaseId, StringComparison.Ordinal);
                Assert.Equal(record.ReducedCaseId, reduction.GetProperty("reducedCaseId").GetString());
                Assert.Equal(record.OriginalSize.SourceLength, reduction.GetProperty("originalSourceLength").GetInt32());
                Assert.Equal(record.ReducedSize.SourceLength, reduction.GetProperty("reducedSourceLength").GetInt32());
                Assert.True(SemanticReduction.TryRebuild(record, out var reduced, out problem), problem);
                output.WriteLine($"{id}: {record.OriginalSize.SourceLength} -> {record.ReducedSize.SourceLength}\n{reduced.Source}");
                Assert.Contains(NestedTrigger, reduced.Source, StringComparison.Ordinal);
                Assert.Contains(reduced.Features, f => f == "nested-pattern");
                Assert.Equal(["ctx-list"], reduced.Features.Where(f => f.StartsWith("ctx-", StringComparison.Ordinal)).ToArray());
                Assert.Equal(signature, SemanticFailureSignature.Of(NestedFaultyRun(reduced)));
                Assert.True(File.Exists(recordPath[..^".reduction.json".Length] + ".json"));
            }

            // Campaign sidecars are metadata: directory replay selects the two descriptors, which pass without the fault.
            Assert.Equal(2, Directory.GetFiles(Path.Combine(outDir, "failures"), "*.signature.json").Length);
            Assert.Equal(0, SemanticReplay.RunReplay(["semantic-replay", Path.Combine(outDir, "failures")]));
            Assert.False(Directory.Exists(Path.Combine(outDir, "work")), "an in-process campaign dispatches no worker");

            // Without the fault the same nested range passes.
            Assert.Equal(0, SemanticCampaign.RunCampaign(
                ["semantic-campaign", "--recipe", "seed-nested", "--seeds", "5EED2B000001", "--cases-per-seed", "4", "--out", Path.Combine(root.FullName, "clean")],
                TextWriter.Null, o => o with { InProcessRunner = static c => SemanticRunner.Run(c) }));

            // The default recipe over the same range and fault searches the seed/ ids, never a nested one.
            var seedOut = Path.Combine(root.FullName, "seed");
            _ = SemanticCampaign.RunCampaign(
                ["semantic-campaign", "--seeds", "5EED2B000001", "--cases-per-seed", "4", "--no-reduce", "--out", seedOut],
                TextWriter.Null, o => o with { InProcessRunner = NestedFaultyRun });
            var seedSummary = File.ReadAllText(Path.Combine(seedOut, SemanticCampaign.SummaryFile));
            Assert.Contains("\"recipe\": \"seed\"", seedSummary, StringComparison.Ordinal);
            Assert.Contains("\"lastCovered\": \"sem2b/v1/seed/5EED2B000001/3\"", seedSummary, StringComparison.Ordinal);
            Assert.DoesNotContain("seed-nested", seedSummary, StringComparison.Ordinal);
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    [Theory]
    [InlineData("")]
    [InlineData("--seeds xyz")]
    [InlineData("--seeds 5..4")]
    [InlineData("--seeds 1 --max-cases 0")]
    [InlineData("--seeds 1 --cases-per-seed -3")]
    [InlineData("--seeds 1 --bogus 2")]
    [InlineData("--seeds 0..FFFFFF")]
    [InlineData("--seeds 1 --deadline-seconds 4294968")]
    [InlineData("--seeds 1 --recipe nested")]
    [InlineData("--seeds 1 --recipe SEED-NESTED")]
    public void UsageErrors_ExitWithTwo_AndWriteNothing(string arguments)
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-campaign-usage-");
        try
        {
            var outDir = Path.Combine(root.FullName, "out");
            var args = arguments.Split(' ', StringSplitOptions.RemoveEmptyEntries);
            Assert.Equal(2, SemanticCampaign.RunCampaign(["semantic-campaign", .. args, "--out", outDir], TextWriter.Null, o => o with { InProcessRunner = static c => SemanticRunner.Run(c) }));
            Assert.False(Directory.Exists(outDir));
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    [Fact]
    public void TheDefaultOutput_IsUnderTheIgnoredArtifactsFolder_AndANonEmptyOutIsRefused()
    {
        Assert.True(SemanticCampaign.TryParse(["semantic-campaign", "--seeds", "0x10..12"], out var options, out var problem), problem);
        Assert.Equal((0x10UL, 0x12UL, 3L * SemanticCampaignOptions.DefaultCasesPerSeed), (options.FirstSeed, options.LastSeed, options.PlannedCases));
        var normalized = options.OutputDirectory.Replace('\\', '/');
        Assert.Contains("/artifacts/semantic-campaign/10-12x16-", normalized, StringComparison.Ordinal);
        Assert.False(SemanticCampaign.ContainsTrackedPaths(options.OutputDirectory));
        Assert.True(SemanticCampaign.ContainsTrackedPaths(Path.Combine(RepoRoot.Find(), "fuzz", "KatLang.ParserFuzz", "SemanticTestcases")));

        var root = Directory.CreateTempSubdirectory("katlang-sem2c-campaign-used-");
        try
        {
            File.WriteAllText(Path.Combine(root.FullName, "tracked.txt"), "keep");
            Assert.Equal(2, SemanticCampaign.RunCampaign(["semantic-campaign", "--seeds", "1", "--out", root.FullName], TextWriter.Null,
                o => o with { InProcessRunner = static c => SemanticRunner.Run(c) }));
            Assert.Equal(["tracked.txt"], Listing(root.FullName));
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    // ── Supervised ──────────────────────────────────────────────────────────

    [Fact]
    public void ASupervisorFailure_UsesTheSameSignatureInSearchAndReduction()
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-supervisor-failure-");
        try
        {
            var missingWorker = "katlang-missing-worker-" + Guid.NewGuid().ToString("N");
            var result = SemanticCampaign.Run(new SemanticCampaignOptions
            {
                FirstSeed = Seed,
                LastSeed = Seed,
                CasesPerSeed = 1,
                MaxAttempts = 1,
                OutputDirectory = root.FullName,
                WorkerCommand = (descriptor, resultPath, _) => new SemanticWorkerCommand(missingWorker, [], new Dictionary<string, string>(), descriptor, resultPath),
            }, TextWriter.Null);

            var failure = Assert.Single(result.Failures);
            Assert.Equal(SemanticVerdict.HarnessFailure, failure.Verdict);
            Assert.Null(failure.ReductionSkipped);
            Assert.NotNull(failure.ReductionRecord);
            Assert.True(SemanticReduction.TryParseRecord(File.ReadAllText(Path.Combine(root.FullName, failure.ReductionRecord)), out var record, out var problem), problem);
            Assert.Equal(failure.Signature, record.Signature);
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    private const string ModeVariable = "KATLANG_SEM2C_CAMPAIGN_WORKER_MODE";
    private const string DescriptorVariable = "KATLANG_SEM2C_CAMPAIGN_WORKER_DESCRIPTOR";
    private const string ResultVariable = "KATLANG_SEM2C_CAMPAIGN_WORKER_RESULT";
    private const string ReadyVariable = "KATLANG_SEM2C_CAMPAIGN_WORKER_READY";
    private const string ReplayModeVariable = "KATLANG_SEM2C_CAMPAIGN_WORKER_REPLAY";
    private const string FaultMode = "fault-on-trigger";

    private static SemanticWorkerCommand ChildWorker(string descriptor, string result, SemanticReplay.Mode mode)
    {
        var ready = result + ".ready";
        return new SemanticWorkerCommand(
            "dotnet",
            [
                "vstest",
                typeof(SemanticCampaignTests).Assembly.Location,
                "--Tests:" + typeof(SemanticCampaignTests).FullName + "." + nameof(Worker_Child),
            ],
            new Dictionary<string, string>
            {
                [ModeVariable] = FaultMode,
                [DescriptorVariable] = descriptor,
                [ResultVariable] = result,
                [ReadyVariable] = ready,
                [ReplayModeVariable] = mode.ToString(),
                ["DOTNET_NOLOGO"] = "1",
            },
            descriptor,
            result)
        {
            ReadyPath = ready,
        };
    }

    /// <summary>
    /// The supervised path end to end: every case runs in a bounded child
    /// in RECIPE mode, the child for the trigger case fails with the planted signature, which travels in
    /// its result document; the failure is persisted, its worker evidence retained, and the passing
    /// case's evidence removed. With reduction enabled the original and candidates run in exact-source
    /// children, and the reduced record preserves the searched failure's signature.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ASupervisedCampaign_FindsThePlantedFailureInAChild_AndRetainsItsEvidence(bool reduce)
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-campaign-supervised-");
        try
        {
            var result = SemanticCampaign.Run(new SemanticCampaignOptions
            {
                FirstSeed = Seed,
                LastSeed = Seed,
                CasesPerSeed = 2,
                Reduce = reduce,
                MaxAttempts = 10,
                OutputDirectory = root.FullName,
                WorkerCommand = ChildWorker,
            }, TextWriter.Null);
            output.WriteLine(result.Describe());
            Assert.True(result.Options.Supervised);
            Assert.Equal(2, result.Executed);
            Assert.Equal(1, result.Passed);
            var failure = Assert.Single(result.Failures);
            Assert.Equal(KnownShape, failure.CaseId);
            Assert.Equal(Planted, failure.Signature);

            var safe = SemanticReplay.SafeName(KnownShape);
            Assert.Equal(
                [
                    SemanticCampaign.SummaryFile,
                    "failures/" + safe + ".json",
                    "failures/" + safe + ".signature.json",
                    "work/" + safe + ".json",
                    "work/" + safe + ".json.result.json",
                    "work/" + safe + ".json.result.json.ready",
                    "work/" + safe + ".json.result.json.supervision.txt",
                ],
                Listing(root.FullName).Where(p => !p.StartsWith("reduced/", StringComparison.Ordinal)).ToArray());
            Assert.Contains("\"supervised\": true", File.ReadAllText(Path.Combine(root.FullName, SemanticCampaign.SummaryFile)), StringComparison.Ordinal);
            if (reduce)
            {
                Assert.Null(failure.ReductionSkipped);
                Assert.NotNull(failure.ReductionRecord);
                Assert.True(SemanticReduction.TryParseRecord(File.ReadAllText(Path.Combine(root.FullName, failure.ReductionRecord)), out var record, out var problem), problem);
                Assert.True(record.Supervised);
                Assert.Equal(Planted, record.Signature);
                Assert.Equal(nameof(SemanticReductionStatus.Reduced), record.Status);
                Assert.True(record.ReducedSize.CompareTo(record.OriginalSize) < 0);
                Assert.True(SemanticReduction.TryRebuild(record, out var rebuilt, out problem), problem);
                Assert.Equal(Planted, SemanticFailureSignature.Of(FaultyRun(rebuilt)));
                var evidence = Path.Combine(root.FullName, "reduced", safe, "evidence");
                Assert.Equal(record.Attempts + 1, Directory.GetFiles(evidence, "*.supervision.txt").Length);
                Assert.True(record.Attempts >= 1, "no reduction candidate ran in a child");
            }
            else
            {
                Assert.False(Directory.Exists(Path.Combine(root.FullName, "reduced")));
            }
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    /// <summary>The child half. Inert (returns immediately) unless launched by the supervised campaign above.</summary>
    [Fact]
    public void Worker_Child()
    {
        if (Environment.GetEnvironmentVariable(ModeVariable) != FaultMode) return;

        var descriptor = Environment.GetEnvironmentVariable(DescriptorVariable)!;
        var result = Environment.GetEnvironmentVariable(ResultVariable)!;
        var ready = Environment.GetEnvironmentVariable(ReadyVariable)!;
        var mode = Enum.Parse<SemanticReplay.Mode>(Environment.GetEnvironmentVariable(ReplayModeVariable)!);
        File.WriteAllText(ready + ".pending", Environment.ProcessId.ToString(CultureInfo.InvariantCulture));
        File.Move(ready + ".pending", ready);

        Assert.True(SemanticDescriptor.TryParse(File.ReadAllText(descriptor), out var parsed, out var problem), problem);
        var faulty = parsed.Case.Source.Contains(Trigger, StringComparison.Ordinal);
        Assert.Equal(0, SemanticReplay.Work(descriptor, result, mode, faulty ? SemanticReductionTests.WrongValue : null));
    }
}
