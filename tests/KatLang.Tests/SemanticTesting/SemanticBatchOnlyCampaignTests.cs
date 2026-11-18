using System.Collections.Immutable;
using System.Text.Json;
using KatLang.ParserFuzz;
using KatLang.TestInfrastructure;
using Xunit.Abstractions;

namespace KatLang.Tests.SemanticTesting;

/// <summary>
/// Batch-only failures of exhaustive campaigns (fuzz/README.md § Campaigns), end to end through
/// supervised children with the test-only planted-fault seam (<see cref="SemanticPlantedFault"/>): the
/// planted observation is well-formed for every case kind; a planted failure is DETECTED in a supervised
/// batch on a success and on an expected failure, and classified standalone because it recurs alone; a
/// failure planted only after an earlier batch member ran is CLASSIFIED batch-only and keeps its complete
/// batch reproducer, which replays; and SEQUENCE reduction shrinks its prefix to that one trigger member,
/// after which the failing program is reduced in that context. The children are
/// <see cref="SubprocessProbe"/> processes (no test-host start), so a sequence reduction's many batch
/// children stay affordable.
///
/// <para>The programs are the first ones of <c>seed-nested-wider</c>: indices 0–7 are a two-level
/// success in each context (bare, list, live <c>if</c>, dead <c>if</c>, property, cached property,
/// wrapper, brace), 8–15 the same with one item too many (an expected <c>ArityMismatch</c>).</para>
/// </summary>
public class SemanticBatchOnlyCampaignTests(ITestOutputHelper output)
{
    private static readonly Lazy<SemanticExhaustive.Enumeration> Wider = new(() => SemanticExhaustive.Enumerate(SemanticCorpus.NestedWiderSeedRecipe));

    private static string Id(int index) => Wider.Value.Programs[index].CaseId;

    private static SemanticCase Program(int index)
        => SemanticCorpus.ExhaustiveBuilder(SemanticCorpus.NestedWiderSeedRecipe, Wider.Value.Programs[index].Choices).Build();

    private static string Safe(int index) => SemanticReplay.SafeName(Id(index));

    private static string[] Ids(IEnumerable<SemanticCase> cases) => [.. cases.Select(static c => c.CaseId)];

    private static string[] Ids(IEnumerable<int> indices) => [.. indices.Select(Id)];

    // ── The seam ────────────────────────────────────────────────────────────

    /// <summary>
    /// The planted observation is wrong but WELL-FORMED for a success, an expected runtime failure and an
    /// intended front-end refusal: in process each fails with the planted signature (and passes without
    /// it), and through a worker's result document the supervisor judges it an ordinary mismatch with the
    /// same signature. The value-forging fault, by contrast, is malformed output on the expected failure.
    /// </summary>
    [Fact]
    public void ThePlantedFault_IsAWellFormedWrongObservation_ForEveryCaseKind()
    {
        var success = Program(0);
        var failure = Program(8);
        Assert.True(SemanticCorpus.TryReconstruct("sem2b/v1/sys/invalid/duplicate-property", SemanticRecipe.RecipeVersion, out var refusal, out var problem), problem);
        Assert.Equal(
            [SemanticCaseKind.ValidSuccess, SemanticCaseKind.ValidRuntimeFailure, SemanticCaseKind.InvalidFrontEnd],
            new[] { success.Kind, failure.Kind, refusal.Kind });

        var root = Directory.CreateTempSubdirectory("katlang-sem2c-planted-shape-");
        try
        {
            foreach (var (c, expected) in new[] { (success, SemanticPlantedFault.ValidSignature), (failure, SemanticPlantedFault.ValidSignature), (refusal, SemanticPlantedFault.RefusalSignature) })
            {
                Assert.True(SemanticRunner.Run(c).Passed, c.CaseId);
                var faulted = SemanticRunner.Run(c, SemanticPlantedFault.WrongEvent);
                Assert.Equal(expected, SemanticFailureSignature.Of(faulted));

                var path = Path.Combine(root.FullName, SemanticReplay.SafeName(c.CaseId) + ".result.json");
                File.WriteAllText(path, SemanticDescriptor.WriteResultDocument(faulted));
                var (verdict, summary, detail) = SemanticSupervisor.JudgeResult(c, path, 0);
                output.WriteLine($"{c.CaseId}: {verdict} {detail}");
                Assert.Equal(SemanticVerdict.Mismatch, verdict);
                Assert.Equal(expected, SemanticFailureSignature.Of(summary!.CoverageResult));
            }

            var forged = Path.Combine(root.FullName, "forged-value.result.json");
            File.WriteAllText(forged, SemanticDescriptor.WriteResultDocument(SemanticRunner.Run(failure, SemanticReductionTests.WrongValue)));
            Assert.Equal(SemanticVerdict.MalformedOutput, SemanticSupervisor.JudgeResult(failure, forged, 0).Verdict);
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    // ── Detection ───────────────────────────────────────────────────────────

    /// <summary>
    /// DETECTION: a fault planted on the dead-<c>if</c> success (program 3) and on the expected
    /// <c>ArityMismatch</c> (program 8) is found in ONE supervised batch of ten: both are well-formed
    /// mismatches with the planted signature (never malformed output), both recur in their single-case
    /// rerun and so are classified standalone, and both descriptors are persisted and replay the planted
    /// signature in recipe mode.
    /// </summary>
    [Fact]
    public void APlantedFault_IsDetectedInASupervisedBatch_OnASuccessAndOnAnExpectedFailure()
    {
        Assert.Equal(SemanticCaseKind.ValidSuccess, Program(3).Kind);
        Assert.Equal(SemanticCaseKind.ValidRuntimeFailure, Program(8).Kind);
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-planted-detect-");
        try
        {
            var planted = new Planted([Id(3), Id(8)], Trigger: null);
            var log = new StringWriter();
            var result = SemanticCampaign.Run(planted.Campaign(root.FullName, members: 10, reduce: false, maxAttempts: 0), log);
            output.WriteLine(log.ToString());

            Assert.Equal((10, 8), (result.Executed, result.Passed));
            Assert.Equal(
                [(Id(3), SemanticVerdict.Mismatch), (Id(8), SemanticVerdict.Mismatch)],
                result.Failures.Select(static f => (f.CaseId, f.Verdict)).ToArray());
            Assert.All(result.Failures, f =>
            {
                Assert.Equal(SemanticPlantedFault.ValidSignature, f.Signature);
                Assert.Equal(SemanticFailureClass.Standalone, f.Classification);
                Assert.Equal(SemanticPlantedFault.ValidSignature, SemanticFailureSignature.Of(f.StandaloneRerun!));
                Assert.Equal("work/batch-00001.txt", f.BatchManifest);
                Assert.Null(f.BatchReproducer);
                Assert.Null(f.Sequence);
            });
            Assert.Equal(0, result.BatchFailures);

            using var document = JsonDocument.Parse(File.ReadAllText(Path.Combine(root.FullName, SemanticCampaign.SummaryFile)));
            var json = document.RootElement;
            Assert.Equal((2, 0, 0), Classifications(json));
            foreach (var failure in json.GetProperty("failures").EnumerateArray())
            {
                Assert.Equal("standalone", failure.GetProperty("classification").GetString());
                Assert.Equal("Mismatch", failure.GetProperty("standalone").GetProperty("verdict").GetString());
                Assert.Equal("host-events", failure.GetProperty("signature").GetProperty("facet").GetString());
                Assert.False(failure.TryGetProperty("batchReproducer", out _));
            }

            foreach (var index in new[] { 3, 8 })
            {
                var descriptor = File.ReadAllText(Path.Combine(root.FullName, "failures", Safe(index) + ".json"));
                Assert.True(SemanticReplay.Replay(descriptor, SemanticReplay.Mode.Recipe).Passed, "the program passes without the planted fault");
                Assert.Equal(SemanticPlantedFault.ValidSignature,
                    SemanticFailureSignature.Of(SemanticReplay.Replay(descriptor, SemanticReplay.Mode.Recipe, SemanticPlantedFault.WrongEvent).Result!));
            }
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    // ── The rerun budget ────────────────────────────────────────────────────

    /// <summary>
    /// THE RERUN BUDGET (<c>--max-reruns</c>): a fault planted on three programs across two batches, with a
    /// budget of ONE standalone rerun. The first failing member is rerun and classified standalone, exactly as
    /// without a budget; the two after it are recorded with their batch failure, UNCLASSIFIED — no standalone
    /// rerun, no batch reproducer, no reduction (reducing would rerun them alone) — and the summary, the log
    /// and <c>Describe</c> say so. The default budget (<see cref="SemanticCampaignOptions.DefaultMaxReruns"/>)
    /// reruns every failure of the detection test above.
    /// </summary>
    [Fact]
    public void TheRerunBudget_LeavesTheFailuresPastItUnclassified_WithoutARerunOrAReduction()
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-planted-reruns-");
        try
        {
            var planted = new Planted([Id(3), Id(5), Id(8)], Trigger: null);
            var log = new StringWriter();
            var options = planted.Campaign(root.FullName, members: 10, reduce: true, maxAttempts: 0) with { BatchSize = 6, MaxReruns = 1 };
            Assert.Equal(64, SemanticCampaignOptions.DefaultMaxReruns);
            var result = SemanticCampaign.Run(options, log);
            output.WriteLine(log.ToString());

            Assert.Equal((10, 7), (result.Executed, result.Passed));
            Assert.Equal(
                [(Id(3), SemanticFailureClass.Standalone), (Id(5), SemanticFailureClass.Unclassified), (Id(8), SemanticFailureClass.Unclassified)],
                result.Failures.Select(static f => (f.CaseId, f.Classification)).ToArray());
            var rerun = result.Failures[0];
            Assert.Equal(
                ["work/batch-00001.txt", "work/batch-00001.txt", "work/batch-00002.txt"],
                result.Failures.Select(static f => f.BatchManifest!).ToArray());
            Assert.Equal(SemanticPlantedFault.ValidSignature, SemanticFailureSignature.Of(rerun.StandaloneRerun!));
            Assert.NotEqual("not rerun alone (--max-reruns spent): an unclassified failure is not reduced", rerun.ReductionSkipped);
            foreach (var unclassified in result.Failures.Skip(1))
            {
                Assert.Equal(SemanticPlantedFault.ValidSignature, unclassified.Signature);
                Assert.Null(unclassified.StandaloneRerun);
                Assert.Null(unclassified.BatchReproducer);
                Assert.Null(unclassified.Sequence);
                Assert.Null(unclassified.ReductionStatus);
                Assert.Equal(0, unclassified.ReductionAttempts);
                Assert.Equal("not rerun alone (--max-reruns spent): an unclassified failure is not reduced", unclassified.ReductionSkipped);
                Assert.True(File.Exists(Path.Combine(root.FullName, unclassified.BatchManifest!)));
                Assert.Contains($"batch member {unclassified.CaseId}: no standalone rerun (all 1 reruns spent, --max-reruns); unclassified; manifest=",
                    log.ToString(), StringComparison.Ordinal);
            }

            Assert.Equal((0, 2), (result.BatchFailures, result.UnclassifiedFailures));
            Assert.Contains(" failed=3 unclassified=2 ", result.Describe(), StringComparison.Ordinal);
            Assert.False(Directory.Exists(Path.Combine(root.FullName, "failures", Safe(5) + ".batch")));

            using var document = JsonDocument.Parse(File.ReadAllText(Path.Combine(root.FullName, SemanticCampaign.SummaryFile)));
            var json = document.RootElement;
            Assert.Equal(1, json.GetProperty("maxReruns").GetInt32());
            Assert.Equal((1, 0, 0), Classifications(json));
            Assert.Equal(2, json.GetProperty("classifications").GetProperty("unclassified").GetInt32());
            var failures = json.GetProperty("failures").EnumerateArray().ToArray();
            Assert.True(failures[0].TryGetProperty("standalone", out _));
            foreach (var failure in failures.Skip(1))
            {
                Assert.Equal("unclassified", failure.GetProperty("classification").GetString());
                Assert.False(failure.TryGetProperty("standalone", out _));
                Assert.False(failure.TryGetProperty("batchReproducer", out _));
            }

            var signature = File.ReadAllText(Path.Combine(root.FullName, "failures", Safe(8) + ".signature.json"));
            Assert.Contains("\"classification\": \"unclassified\"", signature, StringComparison.Ordinal);
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    // ── Classification ──────────────────────────────────────────────────────

    /// <summary>
    /// CLASSIFICATION: the fault on program 6 is armed only once program 2 has run in the same worker, so
    /// it fails in its batch of eight and passes alone. The campaign classifies it batch-only (the summary,
    /// the signature sidecar and <c>Describe</c> say so) instead of reporting a failure that did not
    /// reproduce, and persists its COMPLETE batch reproducer — the seven members 0–6 in batch order, with
    /// a <c>kl-sem2c-batch-reproducer</c> record — which reproduces through <c>semantic-batch-replay</c>.
    /// </summary>
    [Fact]
    public void ABatchOnlyFailure_IsClassified_AndKeepsItsCompleteBatchReproducer()
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-planted-classify-");
        try
        {
            var planted = new Planted([Id(6)], Trigger: Id(2));
            var log = new StringWriter();
            var result = SemanticCampaign.Run(planted.Campaign(root.FullName, members: 8, reduce: false, maxAttempts: 0), log);
            output.WriteLine(log.ToString());

            var failure = Assert.Single(result.Failures);
            Assert.Equal((Id(6), SemanticVerdict.Mismatch, SemanticFailureClass.BatchOnly), (failure.CaseId, failure.Verdict, failure.Classification));
            Assert.Equal(SemanticPlantedFault.ValidSignature, failure.Signature);
            Assert.Equal(SemanticVerdict.Passed, failure.StandaloneRerun!.Verdict);
            Assert.Equal((8, 7, 1), (result.Executed, result.Passed, result.BatchFailures));
            Assert.Contains(" failed=1 batch-only=1 ", result.Describe(), StringComparison.Ordinal);
            Assert.Contains($"batch member {Id(6)}: standalone rerun Passed; manifest=", log.ToString(), StringComparison.Ordinal);

            Assert.Equal($"failures/{Safe(6)}.batch/manifest.txt", failure.BatchReproducer);
            var manifest = Path.Combine(root.FullName, failure.BatchReproducer!);
            Assert.True(SemanticBatchSequence.TryLoad(manifest, out var mode, out var members, out var problem), problem);
            Assert.Equal(SemanticReplay.Mode.Recipe, mode);
            Assert.Equal(Ids(Enumerable.Range(0, 7)), Ids(members.Select(static m => m.Case)));
            Assert.All(File.ReadAllLines(manifest), static line => Assert.DoesNotContain(":", line, StringComparison.Ordinal)); // relative paths only

            using (var record = JsonDocument.Parse(File.ReadAllText(Path.Combine(Path.GetDirectoryName(manifest)!, "batch.json"))))
            {
                var json = record.RootElement;
                Assert.Equal((SemanticBatchSequence.ReproducerFormat, 1, "batch-only", Id(6)),
                    (json.GetProperty("format").GetString(), json.GetProperty("formatVersion").GetInt32(), json.GetProperty("classification").GetString(), json.GetProperty("caseId").GetString()));
                Assert.Equal("Passed", json.GetProperty("standalone").GetProperty("verdict").GetString());
                Assert.Equal("work/batch-00001.txt", json.GetProperty("originalManifest").GetString());
                Assert.Equal(Ids(Enumerable.Range(0, 7)), json.GetProperty("members").EnumerateArray().Select(static m => m.GetString()!).ToArray());
            }

            using (var summary = JsonDocument.Parse(File.ReadAllText(Path.Combine(root.FullName, SemanticCampaign.SummaryFile))))
            {
                var json = summary.RootElement;
                Assert.Equal((0, 1, 0), Classifications(json));
                var entry = Assert.Single(json.GetProperty("failures").EnumerateArray().ToArray());
                Assert.Equal("batch-only", entry.GetProperty("classification").GetString());
                Assert.Equal(failure.BatchReproducer, entry.GetProperty("batchReproducer").GetString());
                Assert.Equal("Passed", entry.GetProperty("standalone").GetProperty("verdict").GetString());
                Assert.Equal("disabled (--no-reduce)", entry.GetProperty("reduction").GetProperty("skipped").GetString());
            }

            Assert.Contains("\"classification\": \"batch-only\"", File.ReadAllText(Path.Combine(root.FullName, "failures", Safe(6) + ".signature.json")), StringComparison.Ordinal);

            // The persisted reproducer reproduces from its own files, through the command.
            var replay = new StringWriter();
            Assert.Equal(1, SemanticBatchSequence.RunReplay(["semantic-batch-replay", manifest], replay, planted.Batch));
            output.WriteLine(replay.ToString());
            Assert.Contains($"{Id(6)}: Mismatch ", replay.ToString(), StringComparison.Ordinal);
            Assert.Contains("7 member(s), 1 failed; child exited cleanly; last member Mismatch", replay.ToString(), StringComparison.Ordinal);
            Assert.False(File.Exists(Path.ChangeExtension(members[^1].DescriptorPath, ".json.result.json")), "a replay never writes beside the reproducer");
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    // ── Sequence reduction ──────────────────────────────────────────────────

    /// <summary>
    /// SEQUENCE REDUCTION: with reduction on, the batch-only failure's six-member prefix shrinks to exactly
    /// its trigger (program 2) — the reduced sequence replays the failure, and the victim with no prefix
    /// passes, so it is one-minimal — and then the failing program is reduced IN that context: its reduced
    /// case fails after the trigger with the planted signature (its context reproducer replays) and passes
    /// alone.
    /// </summary>
    [Fact]
    public void ABatchOnlyFailure_IsReducedToItsTrigger_AndThenAsAProgramInThatContext()
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-planted-sequence-");
        try
        {
            var planted = new Planted([Id(6)], Trigger: Id(2));
            var log = new StringWriter();
            var result = SemanticCampaign.Run(planted.Campaign(root.FullName, members: 8, reduce: true, maxAttempts: 8), log);
            output.WriteLine(log.ToString());

            var failure = Assert.Single(result.Failures);
            Assert.Equal((Id(6), SemanticFailureClass.BatchOnly), (failure.CaseId, failure.Classification));
            var sequence = failure.Sequence!;
            Assert.Equal(SemanticSequenceStatus.Reduced, sequence.Status);
            Assert.Equal(Ids(Enumerable.Range(0, 6)), Ids(sequence.Original));
            Assert.Equal([Id(2)], Ids(sequence.Reduced));
            Assert.InRange(sequence.Attempts, 3, 8);
            Assert.False(sequence.Stopped);

            // The reduced sequence: the trigger, then the failing case; it reproduces.
            Assert.Equal($"reduced/{Safe(6)}.sequence/manifest.txt", failure.SequenceManifest);
            var reducedSequence = Path.Combine(root.FullName, failure.SequenceManifest!);
            Assert.True(SemanticBatchSequence.TryLoad(reducedSequence, out _, out var members, out var problem), problem);
            Assert.Equal([Id(2), Id(6)], Ids(members.Select(static m => m.Case)));
            Assert.Equal(SemanticPlantedFault.ValidSignature,
                SemanticFailureSignature.Of(SemanticBatchSequence.LastResult(SemanticBatchSequence.Replay(reducedSequence, planted.Batch, SemanticSupervisor.DefaultDeadline))!));
            using (var record = JsonDocument.Parse(File.ReadAllText(Path.Combine(root.FullName, failure.SequenceRecord!))))
            {
                var json = record.RootElement;
                Assert.Equal((SemanticBatchSequence.SequenceFormat, "Reduced"), (json.GetProperty("format").GetString(), json.GetProperty("status").GetString()));
                Assert.Equal([Id(2)], json.GetProperty("reducedPrefix").EnumerateArray().Select(static m => m.GetString()!).ToArray());
            }

            // One-minimal: without the trigger, the failing case passes in a batch child too.
            var alone = Directory.CreateTempSubdirectory("katlang-sem2c-planted-alone-");
            try
            {
                var run = SemanticBatchSequence.Run(SemanticBatchSequence.Persist(alone.FullName, [Program(6)], SemanticReplay.Mode.Recipe), planted.Batch, SemanticSupervisor.DefaultDeadline);
                Assert.True(SemanticBatchSequence.LastResult(run)!.Passed);
            }
            finally
            {
                alone.Delete(recursive: true);
            }

            // The program, reduced in that context.
            Assert.Contains(failure.ReductionStatus, new[] { nameof(SemanticReductionStatus.Reduced), nameof(SemanticReductionStatus.AlreadyMinimal) });
            Assert.StartsWith(SemanticRecipe.CasePrefix + SemanticReduction.ReducedLocalPrefix + Id(6)[SemanticRecipe.CasePrefix.Length..] + "/", failure.ReducedCaseId, StringComparison.Ordinal);
            Assert.True(SemanticReduction.TryParseRecord(File.ReadAllText(Path.Combine(root.FullName, failure.ReductionRecord!)), out var reduction, out problem), problem);
            Assert.Equal((Id(6), SemanticPlantedFault.ValidSignature), (reduction.OriginalCaseId, reduction.Signature));
            Assert.True(SemanticReduction.TryRebuild(reduction, out var reduced, out problem), problem);
            Assert.True(SemanticRunner.Run(reduced).Passed, "the reduced program passes alone");

            Assert.Equal($"reduced/{Safe(6)}.sequence/program/manifest.txt", failure.ReductionContext);
            var context = Path.Combine(root.FullName, failure.ReductionContext!);
            Assert.True(SemanticBatchSequence.TryLoad(context, out var contextMode, out var contextMembers, out problem), problem);
            Assert.Equal(SemanticReplay.Mode.ExactSource, contextMode);
            Assert.Equal([Id(2), failure.ReducedCaseId!], Ids(contextMembers.Select(static m => m.Case)));
            Assert.Equal(SemanticPlantedFault.ValidSignature,
                SemanticFailureSignature.Of(SemanticBatchSequence.LastResult(SemanticBatchSequence.Replay(context, planted.Batch, SemanticSupervisor.DefaultDeadline))!));

            using var summary = JsonDocument.Parse(File.ReadAllText(Path.Combine(root.FullName, SemanticCampaign.SummaryFile)));
            var entry = Assert.Single(summary.RootElement.GetProperty("failures").EnumerateArray().ToArray());
            var sequenceJson = entry.GetProperty("sequenceReduction");
            Assert.Equal(("Reduced", 6, 1), (sequenceJson.GetProperty("status").GetString(), sequenceJson.GetProperty("originalPrefix").GetInt32(), sequenceJson.GetProperty("reducedPrefix").GetInt32()));
            Assert.Equal(failure.ReductionContext, entry.GetProperty("reduction").GetProperty("context").GetString());
            Assert.False(Directory.Exists(Path.Combine(root.FullName, "reduced", Safe(6) + ".sequence", "evidence")), "judged candidates leave no scratch evidence");
        }
        finally
        {
            root.Delete(recursive: true);
        }
    }

    /// <summary>
    /// The sequence reducer over a synthetic predicate (in process): it finds the two members a failure
    /// needs, in their original order; an empty prefix that reproduces costs two executions; a prefix that
    /// does not reproduce is reported, never reduced; and the execution bound and the stop signal hold.
    /// </summary>
    [Fact]
    public void TheSequenceReducer_FindsAMinimalReproducingPrefixInOrder_WithinItsBounds()
    {
        var cases = Enumerable.Range(0, 12).Select(Program).ToArray();
        bool Needs(IReadOnlyList<SemanticCase> prefix)
        {
            var at3 = prefix.ToList().IndexOf(cases[3]);
            var at9 = prefix.ToList().IndexOf(cases[9]);
            return at3 >= 0 && at9 > at3;
        }

        var two = SemanticSequenceReducer.Reduce(cases, Needs, 100);
        output.WriteLine(two.Describe());
        Assert.Equal(SemanticSequenceStatus.Reduced, two.Status);
        Assert.Equal(Ids(new[] { cases[3], cases[9] }), Ids(two.Reduced));
        Assert.Equal(Ids(cases), Ids(two.Original));
        Assert.False(two.AttemptLimitReached);

        var empty = SemanticSequenceReducer.Reduce(cases, static _ => true, 100);
        Assert.Equal((SemanticSequenceStatus.Reduced, 0, 2), (empty.Status, empty.Reduced.Length, empty.Attempts));

        var never = SemanticSequenceReducer.Reduce(cases, static _ => false, 100);
        Assert.Equal((SemanticSequenceStatus.NotReproduced, 1), (never.Status, never.Attempts));

        var bounded = SemanticSequenceReducer.Reduce(cases, Needs, 4);
        Assert.Equal((4, true), (bounded.Attempts, bounded.AttemptLimitReached));
        Assert.True(Needs(bounded.Reduced), "a bounded reduction still ends on a reproducing prefix");

        var stopped = SemanticSequenceReducer.Reduce(cases, Needs, 100, static () => true);
        Assert.Equal((SemanticSequenceStatus.NotReproduced, 0, true), (stopped.Status, stopped.Attempts, stopped.Stopped));
    }

    private static (int Standalone, int BatchOnly, int BatchDependent) Classifications(JsonElement summary)
    {
        var classes = summary.GetProperty("classifications");
        return (classes.GetProperty("standalone").GetInt32(), classes.GetProperty("batch-only").GetInt32(), classes.GetProperty("batch-dependent").GetInt32());
    }

    // ── Planted children ────────────────────────────────────────────────────

    private const string VictimsVariable = "KATLANG_SEM2C_PLANTED_VICTIMS";
    private const string TriggerVariable = "KATLANG_SEM2C_PLANTED_TRIGGER";
    private const string ManifestVariable = "KATLANG_SEM2C_PLANTED_MANIFEST";
    private const string DescriptorVariable = "KATLANG_SEM2C_PLANTED_DESCRIPTOR";
    private const string ResultVariable = "KATLANG_SEM2C_PLANTED_RESULT";
    private const string ModeVariable = "KATLANG_SEM2C_PLANTED_MODE";

    /// <summary>A planted defect and the supervised children that carry it (batch and single-case).</summary>
    private sealed record Planted(IReadOnlyList<string> Victims, string? Trigger)
    {
        private Dictionary<string, string> Environment() => new()
        {
            ["DOTNET_NOLOGO"] = "1",
            [VictimsVariable] = string.Join(" ", Victims),
            [TriggerVariable] = Trigger ?? "",
        };

        public SemanticBatchWorkerCommand Batch(string manifest)
        {
            var start = SubprocessProbe.StartInfo(typeof(SemanticBatchOnlyCampaignTests), nameof(PlantedBatchWorker));
            var environment = Environment();
            environment[ManifestVariable] = manifest;
            return new SemanticBatchWorkerCommand(start.FileName, [.. start.ArgumentList], environment, manifest);
        }

        public SemanticWorkerCommand Single(string descriptor, string result, SemanticReplay.Mode mode)
        {
            var start = SubprocessProbe.StartInfo(typeof(SemanticBatchOnlyCampaignTests), nameof(PlantedSingleWorker));
            var environment = Environment();
            environment[DescriptorVariable] = descriptor;
            environment[ResultVariable] = result;
            environment[ModeVariable] = mode.ToString();
            return new SemanticWorkerCommand(start.FileName, [.. start.ArgumentList], environment, descriptor, result);
        }

        /// <summary>An exhaustive <c>seed-nested-wider</c> campaign over its first <paramref name="members"/> programs, in ONE batch.</summary>
        public SemanticCampaignOptions Campaign(string outDir, int members, bool reduce, int maxAttempts) => new()
        {
            Recipe = SemanticCorpus.NestedWiderSeedRecipe,
            Exhaustive = true,
            MaxCases = members,
            BatchSize = members,
            Reduce = reduce,
            MaxAttempts = maxAttempts,
            OutputDirectory = outDir,
            BatchWorkerCommand = Batch,
            WorkerCommand = Single,
        };

        public static Planted FromEnvironment()
            => new(Variable(VictimsVariable).Split(' ', StringSplitOptions.RemoveEmptyEntries), Variable(TriggerVariable) is { Length: > 0 } trigger ? trigger : null);
    }

    private static string Variable(string name)
        => System.Environment.GetEnvironmentVariable(name) ?? throw new InvalidOperationException($"{name} is not set: run only as a planted child");

    /// <summary>The planted batch child (a <see cref="SubprocessProbe"/> method, never a test): <c>semantic-batch-worker</c> with the defect installed.</summary>
    public static void PlantedBatchWorker()
    {
        var planted = Planted.FromEnvironment();
        var defect = new SemanticPlantedFault.Defect(planted.Victims, planted.Trigger);
        var exit = SemanticReplay.WorkBatch(Variable(ManifestVariable), SemanticReplay.Mode.Recipe, defect.For);
        if (exit != 0) throw new InvalidOperationException($"the planted batch worker left {exit} member(s) without a result");
    }

    /// <summary>The planted single-case child: <c>semantic-worker</c> with the defect installed (a fresh process: never armed by a trigger).</summary>
    public static void PlantedSingleWorker()
    {
        var planted = Planted.FromEnvironment();
        var defect = new SemanticPlantedFault.Defect(planted.Victims, planted.Trigger);
        var descriptor = Variable(DescriptorVariable);
        if (!SemanticDescriptor.TryParse(File.ReadAllText(descriptor), out var parsed, out var problem))
            throw new InvalidDataException(problem);
        var exit = SemanticReplay.Work(descriptor, Variable(ResultVariable), Enum.Parse<SemanticReplay.Mode>(Variable(ModeVariable)), defect.For(parsed.Case));
        if (exit != 0) throw new InvalidOperationException($"the planted worker exited with {exit}");
    }
}
