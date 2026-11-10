using System.Collections.Immutable;
using KatLang.ParserFuzz;
using Xunit.Abstractions;

namespace KatLang.Tests.SemanticTesting;

/// <summary>
/// SEM-2C end-to-end SUPERVISED reduction (fuzz/README.md § Reduction): <c>semantic-reduce
/// --supervised</c> runs the original and every candidate in a bounded child worker, and the child
/// here fails on a KNOWN SHAPE — a wrong value on <c>base@sync-optimized</c> whenever the source
/// contains a <c>repeat</c> loop (<see cref="Trigger"/>), injected through the runner's observation
/// seam exactly as the in-process reduction tests inject theirs. The child is this test assembly re-entered through
/// <c>dotnet vstest</c> (<see cref="Worker_Child"/>, the <see cref="SemanticSupervisionTests"/>
/// convention), launched through <see cref="SemanticReduction.RunReduce(string[], Func{string, string, SemanticWorkerCommand}?, string?)"/>'s
/// internal worker-command seam, so the fault never exists in the fuzz consumer. Nothing depends on
/// timing: each child signals readiness before its workload, so a slow host start cannot consume
/// the workload deadline, and the outcome is a pure function of the candidate's source.
/// </summary>
public class SemanticSupervisedReductionTests(ITestOutputHelper output)
{
    private const string ModeVariable = "KATLANG_SEM2C_REDUCE_WORKER_MODE";
    private const string DescriptorVariable = "KATLANG_SEM2C_REDUCE_WORKER_DESCRIPTOR";
    private const string ResultVariable = "KATLANG_SEM2C_REDUCE_WORKER_RESULT";
    private const string ReadyVariable = "KATLANG_SEM2C_REDUCE_WORKER_READY";
    private const string FaultMode = "fault-on-trigger";

    /// <summary>The known failing shape.</summary>
    internal const string Trigger = "repeat";

    /// <summary>
    /// A small systematic loop case, 81 -> 35 source characters. With the SEM-2C span moves it takes
    /// two children: the original and one accepted candidate (minimizing the loop production reaches
    /// the minimum at once). The block-only reducer took three, one a rejected candidate that lost its
    /// <c>repeat</c> and passed; rejection of a passing child result is the same code path in process
    /// (<see cref="AssertLocallyMinimal"/>) and a passing child is <see cref="SemanticSupervisionTests"/>' normal worker.
    /// </summary>
    internal const string CaseId = "sem2b/v1/sys/loop/4";

    private const int MaxAttempts = 40;

    private static readonly SemanticFailureSignature Expected =
        new(SemanticVerdict.Mismatch, SemanticMember.BaseRole, SemanticProfiles.SyncOptimized, "value");

    private static SemanticWorkerCommand ChildWorker(string descriptor, string result)
    {
        var ready = result + ".ready";
        return new SemanticWorkerCommand(
            "dotnet",
            [
                "vstest",
                typeof(SemanticSupervisedReductionTests).Assembly.Location,
                "--Tests:" + typeof(SemanticSupervisedReductionTests).FullName + "." + nameof(Worker_Child),
            ],
            new Dictionary<string, string>
            {
                [ModeVariable] = FaultMode,
                [DescriptorVariable] = descriptor,
                [ResultVariable] = result,
                [ReadyVariable] = ready,
                ["DOTNET_NOLOGO"] = "1",
            },
            descriptor,
            result)
        {
            ReadyPath = ready,
        };
    }

    /// <summary>The injected engine "defect", in process: what the child does to every candidate.</summary>
    private static SemanticCaseResult FaultyRun(SemanticCase c)
        => SemanticRunner.Run(c, c.Source.Contains(Trigger, StringComparison.Ordinal) ? SemanticReductionTests.WrongValue : null);

    private static SemanticCaseBuilder Builder()
    {
        Assert.True(SemanticCorpus.TryBuilder(CaseId, SemanticRecipe.RecipeVersion, out var builder, out var problem), problem);
        return builder;
    }

    [Fact]
    public void ASupervisedReduction_OfAChildThatFailsOnAKnownShape_IsMinimalStableAndKeepsItsSignature()
    {
        var root = Directory.CreateTempSubdirectory("katlang-sem2c-supervised-reduce-");
        try
        {
            var outDir = Path.Combine(root.FullName, "out");
            var evidence = Path.Combine(root.FullName, "evidence");
            var exit = SemanticReduction.RunReduce(
                ["semantic-reduce", CaseId, outDir, "--supervised", "--max-attempts", MaxAttempts.ToString(System.Globalization.CultureInfo.InvariantCulture)],
                ChildWorker, evidence);
            Assert.Equal(0, exit);

            // ── The artifacts: one descriptor and one record, the record supervised and complete.
            var recordPath = Assert.Single(Directory.GetFiles(outDir, "*.reduction.json"));
            var descriptorPath = recordPath[..^".reduction.json".Length] + ".json";
            Assert.True(SemanticReduction.TryParseRecord(File.ReadAllText(recordPath), out var record, out var problem), problem);
            output.WriteLine(File.ReadAllText(recordPath));
            Assert.True(record.Supervised);
            Assert.Equal(CaseId, record.OriginalCaseId);
            Assert.Equal(nameof(SemanticReductionStatus.Reduced), record.Status);
            Assert.Equal(Expected, record.Signature);
            Assert.False(record.AttemptLimitReached, "the supervised reduction did not reach its fixpoint within the bound");
            Assert.True(record.ReducedSize.CompareTo(record.OriginalSize) < 0);

            // ── Every child ran: the original plus one per executed candidate, each with its retained
            // descriptor, result and supervision sidecar. A child ACCEPTED a candidate (same signature),
            // and every failing child carried structured finding records the signature was classified from.
            var children = Directory.GetFiles(evidence, "candidate-*.json").Where(f => !f.EndsWith(".result.json", StringComparison.Ordinal)).Order(StringComparer.Ordinal).ToList();
            Assert.Equal(record.Attempts + 1, children.Count);
            var verdicts = new List<SemanticVerdict>();
            foreach (var child in children)
            {
                Assert.True(File.Exists(child + ".result.json.supervision.txt"), child);
                Assert.True(SemanticDescriptor.TryParseResult(File.ReadAllText(child + ".result.json"), out var summary, out problem), problem);
                verdicts.Add(summary.Verdict);
                if (summary.Verdict == SemanticVerdict.Passed) continue;
                Assert.True(SemanticFailureSignature.HasAlignedRecords(summary.CoverageResult), child);
                Assert.Equal(Expected, SemanticFailureSignature.Of(summary.CoverageResult));
            }

            output.WriteLine("child verdicts: " + string.Join(", ", verdicts));
            Assert.Equal(SemanticVerdict.Mismatch, verdicts[0]); // the original
            Assert.True(verdicts.Count(v => v == SemanticVerdict.Mismatch) >= 2, "no candidate was accepted through a child");
            Assert.Equal([SemanticVerdict.Mismatch, SemanticVerdict.Mismatch], verdicts); // span moves: original + one accepted child
            Assert.All(verdicts, v => Assert.True(v is SemanticVerdict.Passed or SemanticVerdict.Mismatch, v.ToString()));

            // ── Stable: the supervised record is exactly the in-process reduction's under the same fault.
            var inProcess = SemanticReducer.Reduce(Builder(), new SemanticReductionOptions { MaxAttempts = MaxAttempts, Runner = FaultyRun });
            Assert.Equal(SemanticReduction.WriteRecord(SemanticReduction.RecordOf(inProcess) with { Supervised = true }), File.ReadAllText(recordPath));

            // ── The signature is preserved: the record regenerates the descriptor's case, which fails
            // the same way under the fault (in process and in exact-source replay) and passes without it.
            Assert.True(SemanticReduction.TryRebuild(record, out var reduced, out problem), problem);
            var descriptor = File.ReadAllText(descriptorPath);
            Assert.True(SemanticDescriptor.TryParse(descriptor, out var parsed, out problem), problem);
            Assert.Null(SemanticReplay.Drift(parsed.Case, reduced));
            Assert.Equal("Mismatch", parsed.RecordedVerdict);
            Assert.Contains(Trigger, reduced.Source, StringComparison.Ordinal);
            Assert.Equal(Expected, SemanticFailureSignature.Of(FaultyRun(reduced)));
            Assert.Equal(Expected, SemanticFailureSignature.Of(SemanticReplay.Replay(descriptor, SemanticReplay.Mode.ExactSource, SemanticReductionTests.WrongValue).Result!));
            Assert.True(SemanticRunner.Run(reduced).Passed);

            // ── Minimal: no move the reducer makes yields a strictly smaller generated case with the same signature.
            AssertLocallyMinimal(Builder(), record.ReducedChoices, record.ReducedSize);
        }
        finally
        {
            try { root.Delete(recursive: true); }
            catch (IOException) { /* best effort; evidence is in a temporary directory */ }
        }
    }

    /// <summary>
    /// Every deletion of 1–8 consecutive choices, every zeroing and every decrement of the reduced
    /// sequence either generates a case that is not strictly smaller or does not fail with the
    /// expected signature (it passes, or fails another way).
    /// </summary>
    private static void AssertLocallyMinimal(SemanticCaseBuilder builder, ImmutableArray<SemanticChoice> choices, SemanticCaseSize size)
    {
        var values = SemanticReducer.Values(choices);
        var candidates = new List<ImmutableArray<int>>();
        foreach (var block in new[] { 8, 4, 2, 1 })
            for (var i = 0; i + block <= values.Length; i++)
                candidates.Add(values.RemoveRange(i, block));
        for (var i = 0; i < values.Length; i++)
        {
            if (values[i] == 0) continue;
            candidates.Add(values.SetItem(i, 0));
            candidates.Add(values.SetItem(i, values[i] - 1));
        }

        foreach (var candidate in candidates)
        {
            var replay = new RecordingChooser(new ReplayingChooser(candidate));
            var built = builder.Build(replay);
            if (SemanticReducer.SizeOf(built, replay.Choices).CompareTo(size) >= 0) continue;
            var result = FaultyRun(built.Case);
            Assert.True(result.Passed || SemanticFailureSignature.Of(result) != Expected,
                $"a smaller case keeps the signature: [{string.Join(",", candidate)}]\n{built.Case.Source}");
        }

        // The moves were generated and replayed; a reduced case with NO strictly smaller neighbour is
        // minimal in the strongest sense (sys/loop/4 reduces to exactly such a case).
        Assert.True(candidates.Count >= values.Length, $"only {candidates.Count} moves tried");
    }

    /// <summary>The child half. Inert (returns immediately) unless launched by the reduction above.</summary>
    [Fact]
    public void Worker_Child()
    {
        if (Environment.GetEnvironmentVariable(ModeVariable) != FaultMode) return;

        var descriptor = Environment.GetEnvironmentVariable(DescriptorVariable)!;
        var result = Environment.GetEnvironmentVariable(ResultVariable)!;
        var ready = Environment.GetEnvironmentVariable(ReadyVariable)!;
        // Readiness is published only after the writer closes (see SemanticSupervisionTests.Worker_Child).
        File.WriteAllText(ready + ".pending", Environment.ProcessId.ToString(System.Globalization.CultureInfo.InvariantCulture));
        File.Move(ready + ".pending", ready);

        Assert.True(SemanticDescriptor.TryParse(File.ReadAllText(descriptor), out var parsed, out var problem), problem);
        var faulty = parsed.Case.Source.Contains(Trigger, StringComparison.Ordinal);
        Assert.Equal(0, SemanticReplay.Work(descriptor, result, SemanticReplay.Mode.ExactSource, faulty ? SemanticReductionTests.WrongValue : null));
    }
}
