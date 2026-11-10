using System.Collections.Immutable;
using KatLang.ParserFuzz;
using Xunit.Abstractions;

namespace KatLang.Tests.SemanticTesting;

/// <summary>
/// SEM-2C automatic reduction of failing SEM-2B cases (fuzz/README.md § Reduction): recording and
/// replaying choosers are transparent, every replayed choice sequence is a generated case with a
/// constructed expectation, a failing case shrinks to a smaller generated case with the SAME failure
/// signature, a passing case is refused, the work is bounded and deterministic, and the reduced
/// artifact round-trips, is refused in recipe mode and reproduces in exact-source replay. Faults are
/// injected only through <see cref="SemanticRunner.Run"/>'s inert observation seam.
/// </summary>
public class SemanticReductionTests(ITestOutputHelper output)
{
    private const string Trigger = ".Arguments";

    private static readonly string[] RecordedIds =
    [
        "sem2b/v1/seed/5EED2B000001/0",
        "sem2b/v1/seed/5EED2B000002/5",
        "sem2b/v1/seed/5EED2B000003/3",
        "sem2b/v1/seed/5EED2B000006/15",
        "sem2b/v1/seed-nested/5EED2B000001/2",
        "sem2b/v1/sys/meta/0",
        "sem2b/v1/sys/cancel/1",
        "sem2b/v1/sys/invalid/duplicate-property",
        "sem2b/v1/sys/triple/collect+meta+failure-fail",
    ];

    private static SemanticCaseBuilder Builder(string caseId)
    {
        Assert.True(SemanticCorpus.TryBuilder(caseId, SemanticRecipe.RecipeVersion, out var builder, out var problem), problem);
        return builder;
    }

    /// <summary>A wrong value on the base member under sync-optimized: an anchor (and parity, relation) mismatch.</summary>
    internal static SemanticProfileRun WrongValue(SemanticProfileRun run)
        => run.Profile == SemanticProfiles.SyncOptimized && run.Member == SemanticMember.BaseRole && run.Observation is { } o
            ? run with { Observation = o with { Semantic = MetamorphicSemanticObservation.OfValue(new Result.Atom(123456), o.Semantic.EmittedCount) } }
            : run;

    /// <summary>A DIFFERENT failure: an extra host event on the generic profile.</summary>
    private static SemanticProfileRun ExtraEvent(SemanticProfileRun run)
        => run.Profile == SemanticProfiles.SyncGeneric && run.Member == SemanticMember.BaseRole ? run with { Events = [.. run.Events, "trace:4242"] } : run;

    /// <summary>The injected engine "defect": a wrong value whenever the base source contains the trigger.</summary>
    private static SemanticCaseResult FaultyRun(SemanticCase c) => SemanticRunner.Run(c, c.Source.Contains(Trigger, StringComparison.Ordinal) ? WrongValue : null);

    /// <summary>Every source fails, but only trigger sources fail the ORIGINAL way.</summary>
    private static SemanticCaseResult TwoFaultRun(SemanticCase c) => SemanticRunner.Run(c, c.Source.Contains(Trigger, StringComparison.Ordinal) ? WrongValue : ExtraEvent);

    /// <summary>A seeded multi-fragment success whose trigger sits in one fragment, so there is something to delete.</summary>
    private static readonly Lazy<SemanticCase> FailingSeeded = new(() => SemanticCorpus.Seeded().First(c =>
        c.Kind == SemanticCaseKind.ValidSuccess && c.CaseId.Contains("/seed/", StringComparison.Ordinal)
        && c.Source.Contains(Trigger, StringComparison.Ordinal) && c.Features.Any(f => f.StartsWith("compose:", StringComparison.Ordinal))));

    private static readonly SemanticReductionOptions TestBounds = new() { MaxAttempts = 60, Runner = FaultyRun };

    private static readonly Lazy<SemanticReductionResult> Reduction = new(() => SemanticReducer.Reduce(Builder(FailingSeeded.Value.CaseId), TestBounds));

    // ── Choosers ────────────────────────────────────────────────────────────

    [Fact]
    public void Recording_IsTransparent_TheRecordedGenerationEqualsTheCorpusCase()
    {
        foreach (var id in RecordedIds)
        {
            var builder = Builder(id);
            var recorder = new RecordingChooser(builder.NewChooser());
            var recorded = builder.Build(recorder).Case;
            Assert.True(SemanticCorpus.TryReconstruct(id, SemanticRecipe.RecipeVersion, out var plain, out var problem), problem);
            AssertSameCase(plain, recorded);
            Assert.NotEmpty(recorder.Choices);
            Assert.All(recorder.Choices, c => Assert.InRange(c.Value, 0, c.Count - 1));
        }

        foreach (var seed in SemanticCorpus.Seeds.Take(2))
        {
            for (var index = 0; index < 4; index++)
            {
                AssertSameCase(SemanticCorpus.SeededCase(seed, index), SemanticCorpus.SeededBuilder(seed, index).Build(new RecordingChooser(SemanticChooser.Seeded(seed, index))).Case);
                AssertSameCase(SemanticCorpus.NestedSeededCase(seed, index), SemanticCorpus.NestedSeededBuilder(seed, index).Build(new RecordingChooser(SemanticChooser.Seeded(seed, index))).Case);
            }
        }
    }

    [Fact]
    public void ReplayOfAnUnmodifiedRecording_ReproducesTheCaseAndItsTrace()
    {
        foreach (var id in RecordedIds)
        {
            var builder = Builder(id);
            var recorder = new RecordingChooser(builder.NewChooser());
            var original = builder.Build(recorder).Case;
            var replay = new RecordingChooser(new ReplayingChooser(SemanticReducer.Values(recorder.Choices)));
            AssertSameCase(original, builder.Build(replay).Case);
            Assert.Equal(recorder.Choices.ToArray(), replay.Choices.ToArray());
        }
    }

    /// <summary>
    /// The fixed corpus is unchanged by the builder refactor: the digest of every descriptor (minus
    /// build provenance) was recorded from the pre-reducer revision 1e9ccf85. The SEM-2C named path
    /// block (<c>sys/path/…</c>, new ids only) is excluded, so the pin still covers exactly the cases it
    /// was recorded over; <see cref="SemanticPathCoverageTests"/> pins the block's own invariants.
    /// </summary>
    [Fact]
    public void FixedCorpus_RendersByteIdentically()
    {
        var pathBlock = SemanticRecipe.CasePrefix + "sys/path/";
        var digest = CorpusDigest(SemanticCorpus.All().Where(c => !c.CaseId.StartsWith(pathBlock, StringComparison.Ordinal)));
        Assert.True(digest == FixedCorpusDigest, $"SEM-2B fixed corpus digest changed: {digest}");
    }

    internal const string FixedCorpusDigest = "sha256:f685889dee9d75c1c506b6cf4ed432fa2ee08ddb26bc98eece943b2a48398369";

    internal static string CorpusDigest(IEnumerable<SemanticCase> cases)
        => SemanticFingerprint.Of(string.Concat(cases.Select(c => string.Join("\n",
            SemanticDescriptor.Write(c).Split('\n').Where(l => !l.TrimStart().StartsWith("\"provenance\"", StringComparison.Ordinal))))));

    /// <summary>
    /// Every replayed sequence is a real generated case: block deletions at every offset, an exhausted
    /// (empty) sequence and an all-maximal one never throw, valid kinds parse cleanly, and every
    /// expectation is constructed. Without clamping, a shifted or maximal value indexes out of range.
    /// </summary>
    [Fact]
    public void NoCandidateGenerationThrows_AndEveryCandidateIsAValidGeneratedCase()
    {
        var checkedCount = 0;
        foreach (var id in RecordedIds)
        {
            var builder = Builder(id);
            var recorder = new RecordingChooser(builder.NewChooser());
            _ = builder.Build(recorder);
            var values = SemanticReducer.Values(recorder.Choices);
            List<ImmutableArray<int>> candidates = [ImmutableArray<int>.Empty, [.. Enumerable.Repeat(int.MaxValue, values.Length + 16)]];
            foreach (var block in new[] { 1, 3, 8 })
                for (var i = 0; i + block <= values.Length; i += block == 1 ? 1 : 2)
                    candidates.Add(values.RemoveRange(i, block));
            for (var i = 0; i < values.Length; i++) candidates.Add(values.SetItem(i, int.MaxValue));

            foreach (var candidate in candidates)
            {
                SemanticBuiltCase built;
                try
                {
                    built = builder.Build(new ReplayingChooser(candidate));
                }
                catch (Exception exception)
                {
                    Assert.Fail($"{id}: generation threw {exception.GetType().Name}: {exception.Message} for choices [{string.Join(",", candidate)}]");
                    throw;
                }

                Assert.True(SemanticReducer.FrontEndClean(built.Case), $"{id}: a valid candidate was rejected by the front end: [{string.Join(",", candidate)}]\n{built.Case.Source}");
                Assert.True(SemanticReducer.ExpectationConstructed(built.Case.Expected), $"{id}: candidate without a constructed expectation");
                Assert.True(built.Fragments >= 1 && built.Declarations >= 0);
                checkedCount++;
            }
        }

        Assert.True(checkedCount > 200, $"only {checkedCount} candidates checked");
    }

    // ── Reduction ───────────────────────────────────────────────────────────

    [Fact]
    public void FailingSeededCase_ReducesToASmallerCaseWithTheSameSignature()
    {
        var result = Reduction.Value;
        output.WriteLine(result.Describe());
        output.WriteLine("original:\n" + result.Original.Source);
        output.WriteLine("reduced:\n" + result.Reduced.Source);
        Assert.Equal(SemanticReductionStatus.Reduced, result.Status);
        Assert.Equal(FailingSeeded.Value.CaseId, result.OriginalCaseId);
        Assert.Equal(new SemanticFailureSignature(SemanticVerdict.Mismatch, SemanticMember.BaseRole, SemanticProfiles.SyncOptimized, "value"), result.Signature);
        Assert.Equal(result.Signature, SemanticFailureSignature.Of(result.ReducedResult));
        Assert.True(result.ReducedSize.CompareTo(result.OriginalSize) < 0, result.Describe());
        Assert.True(result.Reduced.Source.Length < result.Original.Source.Length, result.Describe());
        Assert.Contains(Trigger, result.Reduced.Source, StringComparison.Ordinal);
        Assert.InRange(result.Attempts, 1, TestBounds.MaxAttempts);
        Assert.Empty(result.GenerationFailures);
        Assert.NotEmpty(result.Accepted);
        Assert.All(result.Accepted, step => Assert.True(step.FrontEndClean && step.ExpectationConstructed, step.Move));
        Assert.True(SemanticReducer.FrontEndClean(result.Reduced));
        // The reduced case is a generated case: the unfaulted runner passes it.
        Assert.True(SemanticRunner.Run(result.Reduced).Passed);
    }

    /// <summary>A smaller candidate that fails DIFFERENTLY is never accepted (mutation target: the signature check).</summary>
    [Fact]
    public void ACandidateThatFailsDifferently_IsRejected()
    {
        var result = SemanticReducer.Reduce(Builder(FailingSeeded.Value.CaseId), TestBounds with { Runner = TwoFaultRun });
        Assert.Equal(new SemanticFailureSignature(SemanticVerdict.Mismatch, SemanticMember.BaseRole, SemanticProfiles.SyncOptimized, "value"), result.Signature);
        Assert.Equal(result.Signature, SemanticFailureSignature.Of(result.ReducedResult));
        Assert.Contains(Trigger, result.Reduced.Source, StringComparison.Ordinal);
        Assert.Empty(result.GenerationFailures);

        // The premise: a source without the trigger fails too, with another signature.
        var other = SemanticCorpus.Seeded().First(s => s.Kind == SemanticCaseKind.ValidSuccess && !s.Source.Contains(Trigger, StringComparison.Ordinal));
        var otherResult = TwoFaultRun(other);
        Assert.False(otherResult.Passed);
        Assert.NotEqual(result.Signature, SemanticFailureSignature.Of(otherResult));
    }

    [Fact]
    public void Signature_IgnoresMessageText_ButNotLocationOrFacet()
    {
        var semanticCase = FailingSeeded.Value;
        var a = SemanticRunner.Run(semanticCase, WrongValue);
        var b = SemanticRunner.Run(semanticCase, run => run.Profile == SemanticProfiles.SyncOptimized && run.Member == SemanticMember.BaseRole && run.Observation is { } o
            ? run with { Observation = o with { Semantic = MetamorphicSemanticObservation.OfValue(new Result.Atom(777777), o.Semantic.EmittedCount) } }
            : run);
        Assert.NotEqual(a.Findings[0], b.Findings[0]);
        Assert.Equal(SemanticFailureSignature.Of(a), SemanticFailureSignature.Of(b));
        Assert.NotEqual(SemanticFailureSignature.Of(a), SemanticFailureSignature.Of(SemanticRunner.Run(semanticCase, ExtraEvent)));
        Assert.Equal(new SemanticFailureSignature(SemanticVerdict.Passed, "-", "-", "-"), SemanticFailureSignature.Of(SemanticRunner.Run(semanticCase)));
    }

    [Fact]
    public void Signature_DistinguishesComparedCountersOnTheSamePair()
    {
        SemanticCaseResult WithCounterFault(bool items, long increment) => SemanticRunner.Run(FailingSeeded.Value, run =>
            run.Profile == SemanticProfiles.SyncOptimized && run.Member == SemanticMember.BaseRole && run.Observation is { } o
                ? run with { Observation = items
                    ? o with { MaterializedItems = o.MaterializedItems + increment }
                    : o with { EvaluationSteps = o.EvaluationSteps + increment } }
                : run);

        var items = SemanticFailureSignature.Of(WithCounterFault(items: true, 1));
        var steps = SemanticFailureSignature.Of(WithCounterFault(items: false, 1));
        Assert.Equal(SemanticVerdict.Mismatch, items.Verdict);
        Assert.Equal(items.Verdict, steps.Verdict);
        Assert.Equal(items.Profile, steps.Profile);
        Assert.StartsWith("parity:", items.Profile, StringComparison.Ordinal);
        Assert.NotEqual(items, steps);
        Assert.Equal(items, SemanticFailureSignature.Of(WithCounterFault(items: true, 17)));
    }

    [Fact]
    public void Signature_PreservesTheProfileOfARejectedPath()
    {
        var semanticCase = SemanticCorpus.All().First(c => c.Kind == SemanticCaseKind.ValidSuccess
            && c.Paths.HasFlag(SemanticPath.OptimizedLoop));
        SemanticCaseResult WithoutEvidence(string profile) => SemanticRunner.Run(semanticCase, run =>
            run.Profile == profile && run.Member == SemanticMember.BaseRole && run.Observation is { } o
                ? run with { Observation = o with { OptimizerEvidence = null } }
                : run);
        var generic = SemanticFailureSignature.Of(WithoutEvidence(SemanticProfiles.SyncGeneric));
        var optimized = SemanticFailureSignature.Of(WithoutEvidence(SemanticProfiles.SyncOptimized));
        Assert.Equal(SemanticVerdict.MissingObservation, generic.Verdict);
        Assert.Equal("path:OptimizedLoop", generic.Facet);
        Assert.Equal(generic.Facet, optimized.Facet);
        Assert.Equal(SemanticProfiles.SyncGeneric, generic.Profile);
        Assert.Equal(SemanticProfiles.SyncOptimized, optimized.Profile);
        Assert.NotEqual(generic, optimized);
    }

    [Fact]
    public void APassingCase_IsRefused_WithItsOwnExitCode()
    {
        var result = SemanticReducer.Reduce(Builder(FailingSeeded.Value.CaseId));
        Assert.Equal(SemanticReductionStatus.NothingToReduce, result.Status);
        Assert.Equal(0, result.Attempts);

        var outDir = Directory.CreateTempSubdirectory("katlang-sem2c-reduce-test-");
        try
        {
            Assert.Equal(SemanticReduction.NothingToReduceExitCode, SemanticReduction.RunReduce(["semantic-reduce", FailingSeeded.Value.CaseId, outDir.FullName]));
            Assert.Empty(Directory.GetFiles(outDir.FullName));
            Assert.Equal(2, SemanticReduction.RunReduce(["semantic-reduce", "sem2b/v1/sys/no-such-case", outDir.FullName]));
            Assert.Equal(2, SemanticReduction.RunReduce(["semantic-reduce", FailingSeeded.Value.CaseId]));
        }
        finally
        {
            outDir.Delete(recursive: true);
        }

        Assert.NotEqual(0, SemanticReduction.NothingToReduceExitCode);
        Assert.NotEqual(1, SemanticReduction.NothingToReduceExitCode);
        Assert.NotEqual(2, SemanticReduction.NothingToReduceExitCode);
    }

    [Fact]
    public void AnOversizedDescriptor_IsRefusedWithTheDocumentedExitCode()
    {
        var directory = Directory.CreateTempSubdirectory("katlang-sem2c-oversized-");
        try
        {
            var path = Path.Combine(directory.FullName, "oversized.json");
            using (var stream = File.Create(path)) stream.SetLength(SemanticDescriptor.MaxDescriptorChars * 4L + 1);
            var outputPath = Path.Combine(directory.FullName, "out");
            Assert.Equal(2, SemanticReduction.RunReduce(["semantic-reduce", path, outputPath]));
            Assert.False(Directory.Exists(outputPath));
        }
        finally
        {
            directory.Delete(recursive: true);
        }
    }

    [Fact]
    public void AGeneratorPreconditionFailure_StopsAtTheFirstSequenceAndRetainsIt()
    {
        var original = Builder(FailingSeeded.Value.CaseId);
        var failing = new SemanticCaseBuilder(original.LocalId, () => new FixedChooser(), g =>
        {
            if (g.Pick("review.precondition", 2) == 0) throw new InvalidOperationException("precondition sentinel");
            return original.Build(original.NewChooser());
        });
        var result = SemanticReducer.Reduce(failing, TestBounds);
        Assert.Equal(1, result.Generations);
        Assert.Equal(0, result.Attempts);
        var failure = Assert.Single(result.GenerationFailures);
        Assert.Empty(failure.Choices);
        Assert.Contains("precondition sentinel", failure.Error, StringComparison.Ordinal);
        Assert.Equal(result.OriginalSize, result.ReducedSize);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ABrokenGeneratedContract_StopsBeforeExecutingTheCandidate(bool missingExpectation)
    {
        var original = Builder(FailingSeeded.Value.CaseId);
        var failing = new SemanticCaseBuilder(original.LocalId, () => new FixedChooser(), g =>
        {
            var built = original.Build(original.NewChooser());
            if (g.Pick("review.contract", 2) != 0) return built;
            return built with { Case = missingExpectation
                ? built.Case with { Expected = built.Case.Expected with { Value = null } }
                : built.Case with { Members = built.Case.Members.SetItem(1, built.Case.Members[1] with { Source = "1 +" }) } };
        });
        var executions = 0;
        var result = SemanticReducer.Reduce(failing, TestBounds with { Runner = c => { executions++; return FaultyRun(c); } });
        Assert.Equal(1, executions); // the original only; never evaluate the malformed recovery tree
        Assert.Equal(1, result.Generations);
        Assert.Equal(0, result.Attempts);
        Assert.Single(result.GenerationFailures);
        Assert.Equal(result.Original.Source, result.Reduced.Source);
    }

    private sealed class FixedChooser : SemanticChooser
    {
        public override int Pick(string dimension, int count) => count - 1;
    }

    [Fact]
    public void TheAttemptLimitIsRespected_AndTwoRunsGiveIdenticalOutput()
    {
        var bounded = TestBounds with { MaxAttempts = 3 };
        var first = SemanticReducer.Reduce(Builder(FailingSeeded.Value.CaseId), bounded);
        var second = SemanticReducer.Reduce(Builder(FailingSeeded.Value.CaseId), bounded);
        Assert.InRange(first.Attempts, 0, 3);
        Assert.True(first.AttemptLimitReached, first.Describe());
        Assert.Equal(SemanticReduction.WriteRecord(SemanticReduction.RecordOf(first)), SemanticReduction.WriteRecord(SemanticReduction.RecordOf(second)));
        Assert.Equal(SemanticDescriptor.Write(first.Reduced), SemanticDescriptor.Write(second.Reduced));

        var full = Reduction.Value;
        var again = SemanticReducer.Reduce(Builder(FailingSeeded.Value.CaseId), TestBounds);
        Assert.Equal(SemanticReduction.WriteRecord(SemanticReduction.RecordOf(full)), SemanticReduction.WriteRecord(SemanticReduction.RecordOf(again)));
    }

    [Fact]
    public void SimplerChoicesForAnIdenticalCase_AreNormalizationAndNotAReduction()
    {
        var original = Builder(FailingSeeded.Value.CaseId);
        var builder = new SemanticCaseBuilder(original.LocalId, () => new FixedChooser(), g =>
        {
            _ = g.Pick("review.inert", 2);
            return original.Build(original.NewChooser());
        });
        var result = SemanticReducer.Reduce(builder, TestBounds with { MaxAttempts = 0 });
        Assert.NotEmpty(result.Accepted);
        Assert.Equal(SemanticReductionStatus.AlreadyMinimal, result.Status);
        Assert.Equal(result.OriginalSize.SourceLength, result.ReducedSize.SourceLength);
        Assert.Equal(result.OriginalSize.Fragments, result.ReducedSize.Fragments);
        Assert.Equal(result.OriginalSize.Declarations, result.ReducedSize.Declarations);
        Assert.True(result.ReducedSize.ChoiceSum < result.OriginalSize.ChoiceSum);
        Assert.Equal(0, result.ReducedSize.CompareTo(result.OriginalSize));
        Assert.Equal(0, result.Attempts);
        Assert.Equal(SemanticDescriptor.Write(result.Original), SemanticDescriptor.Write(result.Reduced));
    }

    /// <summary>A systematic case has a per-id builder too (ids unchanged) and reduces the same way.</summary>
    [Fact]
    public void ASystematicCase_ReducesThroughItsOwnBuilder()
    {
        var semanticCase = SemanticCorpus.Systematic().First(c => c.Kind == SemanticCaseKind.ValidSuccess
            && c.Source.Contains(Trigger, StringComparison.Ordinal) && c.CaseId.Contains("/pair/", StringComparison.Ordinal));
        var result = SemanticReducer.Reduce(Builder(semanticCase.CaseId), TestBounds with { MaxAttempts = 30 });
        Assert.NotEqual(SemanticReductionStatus.NothingToReduce, result.Status);
        Assert.Equal(result.Signature, SemanticFailureSignature.Of(result.ReducedResult));
        Assert.Contains(Trigger, result.Reduced.Source, StringComparison.Ordinal);
        Assert.Empty(result.GenerationFailures);
        Assert.True(result.ReducedSize.CompareTo(result.OriginalSize) <= 0);
    }

    // ── Artifacts ───────────────────────────────────────────────────────────

    [Fact]
    public void ReductionRecord_RejectsContradictoryMetadataAndRecipeDrift()
    {
        var record = SemanticReduction.RecordOf(Reduction.Value);
        var contradictions = new[]
        {
            record with { Signature = record.Signature with { Verdict = SemanticVerdict.Passed } },
            record with { Generations = -1 },
            record with { MaxAttempts = -1 },
            record with { Status = nameof(SemanticReductionStatus.AlreadyMinimal) },
            record with { ReducedSize = record.ReducedSize with { SourceLength = -1 } },
            record with { OriginalSize = record.OriginalSize with { Fragments = 0 } },
            record with { OriginalSize = record.OriginalSize with { Choices = record.OriginalSize.Choices + 1 } },
            record with { ReducedSize = record.ReducedSize with { ChoiceSum = record.ReducedSize.ChoiceSum + 1 } },
        };
        foreach (var invalid in contradictions)
            Assert.False(SemanticReduction.TryParseRecord(SemanticReduction.WriteRecord(invalid), out _, out _));

        var drifted = new[]
        {
            record with { OriginalChoices = record.OriginalChoices.SetItem(0, record.OriginalChoices[0] with { Dimension = "changed" }) },
            record with { OriginalSize = record.OriginalSize with { SourceLength = record.OriginalSize.SourceLength + 1 } },
            record with { ReducedSize = record.ReducedSize with { Declarations = record.ReducedSize.Declarations + 1 } },
            record with { ReducedChoices = record.ReducedChoices.SetItem(0, record.ReducedChoices[0] with { Dimension = "changed" }) },
        };
        foreach (var invalid in drifted)
        {
            Assert.True(SemanticReduction.TryParseRecord(SemanticReduction.WriteRecord(invalid), out var parsed, out var problem), problem);
            Assert.False(SemanticReduction.TryRebuild(parsed, out _, out problem));
            Assert.NotEmpty(problem);
        }
    }

    [Fact]
    public void TheReducedArtifact_RoundTrips_IsRefusedInRecipeMode_AndReproducesInExactSource()
    {
        var result = Reduction.Value;
        var reduced = SemanticReduction.AsReduced(result.Reduced, result.OriginalCaseId, result.ReducedChoices);
        Assert.StartsWith(SemanticRecipe.CasePrefix + SemanticReduction.ReducedLocalPrefix, reduced.CaseId, StringComparison.Ordinal);
        Assert.Equal(SemanticReduction.ReducedTier, reduced.Tier);

        // The descriptor: an ordinary v1 descriptor under the reserved id.
        var descriptor = SemanticDescriptor.Write(reduced, result.ReducedResult with { CaseId = reduced.CaseId });
        Assert.True(SemanticDescriptor.TryParse(descriptor, out var parsed, out var problem), problem);
        Assert.Equal(SemanticDescriptor.Write(reduced), SemanticDescriptor.Write(parsed.Case));

        // The record: versioned, round-trips, and regenerates exactly the descriptor's case.
        var record = SemanticReduction.RecordOf(result);
        var recordText = SemanticReduction.WriteRecord(record);
        Assert.True(SemanticReduction.TryParseRecord(recordText, out var parsedRecord, out problem), problem);
        Assert.Equal(recordText, SemanticReduction.WriteRecord(parsedRecord));
        Assert.Equal(result.OriginalCaseId, parsedRecord.OriginalCaseId);
        Assert.Equal(reduced.CaseId, parsedRecord.ReducedCaseId);
        Assert.True(SemanticReduction.TryRebuild(parsedRecord, out var rebuilt, out problem), problem);
        Assert.Null(SemanticReplay.Drift(parsed.Case, rebuilt));
        Assert.False(SemanticDescriptor.TryParse(recordText, out _, out _));
        Assert.False(SemanticReduction.TryParseRecord(recordText.Replace("\"formatVersion\": 1", "\"formatVersion\": 2", StringComparison.Ordinal), out _, out problem));
        Assert.Contains("unsupported", problem, StringComparison.Ordinal);
        Assert.False(SemanticReduction.TryParseRecord(descriptor, out _, out _));

        // Recipe mode refuses it explicitly; the recipe never rebuilds a reduced id.
        var recipe = SemanticReplay.Replay(descriptor, SemanticReplay.Mode.Recipe);
        Assert.False(recipe.Passed);
        Assert.NotNull(recipe.Problem);
        Assert.Contains("is a REDUCED case", recipe.Report, StringComparison.Ordinal);
        Assert.Contains("--exact-source", recipe.Report, StringComparison.Ordinal);
        Assert.False(SemanticCorpus.TryReconstruct(reduced.CaseId, SemanticRecipe.RecipeVersion, out _, out problem));
        Assert.Contains("is a REDUCED case", problem, StringComparison.Ordinal);

        // Exact-source replay reproduces the failure under the same injected fault, and passes without it.
        var faulted = SemanticReplay.Replay(descriptor, SemanticReplay.Mode.ExactSource, WrongValue);
        Assert.Equal(SemanticVerdict.Mismatch, faulted.Verdict);
        Assert.Equal(result.Signature, SemanticFailureSignature.Of(faulted.Result!));
        Assert.True(SemanticReplay.Replay(descriptor, SemanticReplay.Mode.ExactSource).Passed);

        // A directory replay reads the descriptor and skips the record beside it.
        var dir = Directory.CreateTempSubdirectory("katlang-sem2c-artifact-test-");
        try
        {
            var stem = Path.Combine(dir.FullName, SemanticReplay.SafeName(reduced.CaseId));
            File.WriteAllText(stem + ".json", descriptor);
            File.WriteAllText(stem + ".reduction.json", recordText);
            Assert.Equal(0, SemanticReplay.RunReplay(["semantic-replay", "--exact-source", dir.FullName]));
            Assert.Equal(2, SemanticReplay.RunReplay(["semantic-replay", dir.FullName]));
        }
        finally
        {
            dir.Delete(recursive: true);
        }
    }

    private static void AssertSameCase(SemanticCase expected, SemanticCase actual)
    {
        Assert.Equal(expected.CaseId, actual.CaseId);
        Assert.Equal(expected.Tier, actual.Tier);
        Assert.Equal(expected.Seed, actual.Seed);
        Assert.Equal(expected.Index, actual.Index);
        Assert.Equal(expected.Members.ToArray(), actual.Members.ToArray());
        Assert.Equal(expected.Expected.ToString(), actual.Expected.ToString());
        Assert.Equal(expected.Expected.ValueIdentity, actual.Expected.ValueIdentity);
        Assert.Equal(expected.Expected.CancelledEventsPrefix.ToArray(), actual.Expected.CancelledEventsPrefix.ToArray());
        Assert.Equal(expected.Families.ToArray(), actual.Families.ToArray());
        Assert.Equal(expected.Features.ToArray(), actual.Features.ToArray());
        Assert.Equal(expected.Paths, actual.Paths);
        Assert.Equal(expected.MinimumCacheHits, actual.MinimumCacheHits);
        Assert.Equal(expected.Profiles.ToArray(), actual.Profiles.ToArray());
        Assert.Null(SemanticReplay.Drift(expected, actual));
        Assert.Equal(SemanticDescriptor.Write(expected), SemanticDescriptor.Write(actual));
    }
}
