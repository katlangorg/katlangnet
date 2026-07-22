using System.Globalization;
using KatLang.ParserFuzz;
using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests;

/// <summary>
/// Deterministic coverage for the operational-metamorphic fuzz target
/// (<c>KATLANG_FUZZ_MODE=metamorphic</c>, <c>fuzz/KatLang.ParserFuzz/Metamorphic</c>).
///
/// <para>The harness core is compiled into this assembly as shared source, so these tests
/// exercise the very decoder, template, executor, comparator, and replay driver the campaign
/// runs. Nothing here depends on libFuzzer, SharpFuzz, or a fuzzing loop.</para>
///
/// <para>Phase 1's parameter space is finite (a few hundred normalized points), so several
/// tests are EXHAUSTIVE rather than sampled: the campaign's job is to keep the harness honest
/// over time, not to discover Phase 1's own space.</para>
/// </summary>
public class MetamorphicFuzzHarnessTests
{
    private static string SeedDirectory =>
        Path.Combine(RepoRoot.Find(), "fuzz", "KatLang.ParserFuzz", "MetamorphicTestcases");

    private static List<MetamorphicParameters> AllParameters => MetamorphicTemplates.EnumerateAllParameters().ToList();

    // ── Decoder ──────────────────────────────────────────────────────────────

    [Fact]
    public void Decoder_MapsTheSameBytesToTheSameCase()
    {
        foreach (var payload in SamplePayloads())
        {
            var first = MetamorphicDecoder.Decode(payload);
            var second = MetamorphicDecoder.Decode(payload);
            Assert.Equal(first, second);
            Assert.Equal(MetamorphicTemplates.Build(first).LeftSource, MetamorphicTemplates.Build(second).LeftSource);
            Assert.Equal(MetamorphicTemplates.Build(first).RightSource, MetamorphicTemplates.Build(second).RightSource);
        }
    }

    [Fact]
    public void Decoder_KeepsEveryDimensionInsideItsConfiguredTable()
    {
        // Every byte value at every position, so no reduction can escape its table.
        for (var position = 0; position < MetamorphicParameters.EncodedLength; position++)
        {
            for (var value = 0; value <= byte.MaxValue; value++)
            {
                var payload = new byte[MetamorphicParameters.EncodedLength];
                payload[position] = (byte)value;

                var parameters = MetamorphicDecoder.Decode(payload);
                Assert.InRange(parameters.FamilyIndex, 0, MetamorphicDecoder.FamilyTable.Length - 1);
                Assert.InRange(parameters.RangeStopIndex, 0, MetamorphicDecoder.RangeStopTable.Length - 1);
                Assert.InRange(parameters.LimitModeIndex, 0, MetamorphicDecoder.LimitModeTable.Length - 1);
                Assert.InRange(parameters.CumulativeOffsetIndex, 0, MetamorphicDecoder.OffsetTable.Length - 1);
                Assert.InRange(parameters.PerCollectionOffsetIndex, 0, MetamorphicDecoder.OffsetTable.Length - 1);
                Assert.InRange(parameters.OptimizeIndex, 0, 1);
                Assert.Contains(parameters.RangeStop, MetamorphicDecoder.RangeStopTable);
            }
        }
    }

    [Fact]
    public void Decoder_HandlesShortAndEmptyInputDeterministically()
    {
        // Missing bytes read as zero, so a truncated input is the same case as the input
        // zero-padded to full length — never an exception and never a discarded run.
        for (var length = 0; length <= MetamorphicParameters.EncodedLength; length++)
        {
            var truncated = new byte[length];
            for (var i = 0; i < length; i++) truncated[i] = (byte)(i + 1);

            var padded = new byte[MetamorphicParameters.EncodedLength];
            truncated.CopyTo(padded, 0);

            Assert.Equal(MetamorphicDecoder.Decode(padded), MetamorphicDecoder.Decode(truncated));
        }
    }

    [Fact]
    public void Decoder_ReadsOnlyThePayloadPrefixOfAnArbitrarilyLargeInput()
    {
        // Guards the "no allocation proportional to arbitrary input" property: a 64 KiB input
        // decodes to exactly the case its first six bytes select.
        var large = new byte[64 * 1024];
        for (var i = 0; i < large.Length; i++) large[i] = (byte)(i * 31 + 7);

        var prefix = large.AsSpan(0, MetamorphicParameters.EncodedLength).ToArray();
        Assert.Equal(MetamorphicDecoder.Decode(prefix), MetamorphicDecoder.Decode(large));
    }

    [Fact]
    public void Decoder_NormalizesDimensionsTheSelectedLimitModeDoesNotUse()
    {
        foreach (var parameters in AllParameters)
        {
            switch (parameters.LimitMode)
            {
                case MetamorphicLimitMode.Default:
                    Assert.Equal(0, parameters.CumulativeOffset);
                    Assert.Equal(0, parameters.PerCollectionOffset);
                    break;
                case MetamorphicLimitMode.CumulativeItems:
                    Assert.Equal(0, parameters.PerCollectionOffset);
                    break;
                case MetamorphicLimitMode.PerCollectionItems:
                    Assert.Equal(0, parameters.CumulativeOffset);
                    break;
            }
        }
    }

    [Fact]
    public void Decoder_RoundTripsEveryCanonicalEncoding()
    {
        foreach (var parameters in AllParameters)
        {
            var encoded = parameters.Encode();
            Assert.Equal(MetamorphicParameters.EncodedLength, encoded.Length);
            Assert.Equal(parameters, MetamorphicDecoder.Decode(encoded));
        }
    }

    [Fact]
    public void Decoder_NeverSelectsAnEnormousCollection()
    {
        foreach (var parameters in AllParameters)
        {
            var cardinality = MetamorphicTemplates.RangeCardinality(parameters.RangeStop);
            Assert.InRange(cardinality, 1, MetamorphicDecoder.MaxPhase1Cardinality);
        }
    }

    [Fact]
    public void Cardinality_UsesCheckedWideArithmeticAtTheExtremes()
    {
        // Not reachable from the table, but the helper must not silently overflow if a future
        // family widens the domain: the inclusive distance from 1 is computed in 64-bit.
        Assert.Equal(1L, MetamorphicTemplates.RangeCardinality(1));
        Assert.Equal(2L, MetamorphicTemplates.RangeCardinality(0));
        Assert.Equal((long)int.MaxValue, MetamorphicTemplates.RangeCardinality(int.MaxValue));
        Assert.Equal(2147483650L, MetamorphicTemplates.RangeCardinality(int.MinValue));
    }

    // ── Template ─────────────────────────────────────────────────────────────

    [Fact]
    public void Template_GeneratesTwoValidProgramsForEveryParameterPoint()
    {
        foreach (var parameters in AllParameters)
        {
            var testCase = MetamorphicTemplates.Build(parameters);

            Assert.False(Parser.Parse(testCase.LeftSource).HasErrors, testCase.LeftSource);
            Assert.False(Parser.Parse(testCase.RightSource).HasErrors, testCase.RightSource);
            Assert.NotEqual(testCase.LeftSource, testCase.RightSource);
        }
    }

    [Fact]
    public void Template_EmitsTheOrdinaryCallOnTheLeftAndTheDottedCallOnTheRight()
    {
        foreach (var parameters in AllParameters)
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            var stop = parameters.RangeStop.ToString(CultureInfo.InvariantCulture);

            Assert.Equal($"Output = count(range(1, {stop}))", testCase.LeftSource);
            Assert.Equal($"Output = range(1, {stop}).count", testCase.RightSource);

            // Structural member access is a DIFFERENT language construct and is explicitly out
            // of this relation's scope, so the template must never accidentally produce it.
            Assert.DoesNotContain("public", testCase.LeftSource, StringComparison.Ordinal);
            Assert.DoesNotContain("public", testCase.RightSource, StringComparison.Ordinal);
            Assert.DoesNotContain("Output.", testCase.RightSource, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void Template_ExpectedCardinalityMatchesWhatTheLanguageActuallyMaterializes()
    {
        foreach (var stop in MetamorphicDecoder.RangeStopTable)
        {
            var expected = MetamorphicTemplates.RangeCardinality(stop);
            var source = $"Output = count(range(1, {stop.ToString(CultureInfo.InvariantCulture)}))";

            Assert.True(MetamorphicExecutor.TryObserve(source, null, true, out var observation, out _));
            Assert.Equal("ok", observation.Semantic.Outcome);
            Assert.Equal(expected.ToString(CultureInfo.InvariantCulture), observation.Semantic.Structure);
            Assert.Equal(expected, observation.MaterializedItems);
        }
    }

    [Fact]
    public void Template_PlacesLimitsExactlyAroundTheExpectedTotal()
    {
        foreach (var parameters in AllParameters)
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            var total = testCase.ExpectedItemTotal;

            if (parameters.LimitMode == MetamorphicLimitMode.Default)
            {
                Assert.Null(testCase.Limits);
                continue;
            }

            Assert.NotNull(testCase.Limits);

            var wantsCumulative = parameters.LimitMode
                is MetamorphicLimitMode.CumulativeItems or MetamorphicLimitMode.Both;
            var wantsPerCollection = parameters.LimitMode
                is MetamorphicLimitMode.PerCollectionItems or MetamorphicLimitMode.Both;

            Assert.Equal(
                wantsCumulative ? Math.Max(1, total + parameters.CumulativeOffset) : null,
                testCase.Limits!.MaxMaterializedItems);
            Assert.Equal(
                wantsPerCollection ? (int?)Math.Max(1, total + parameters.PerCollectionOffset) : null,
                testCase.Limits.MaxCollectionItems);
        }
    }

    [Fact]
    public void Template_SatisfiesItsOwnPreconditionsAtEveryParameterPoint()
    {
        foreach (var parameters in AllParameters)
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            Assert.True(
                testCase.Precondition.Satisfied,
                $"{parameters} rejected: {testCase.Precondition.Reason}");
        }
    }

    [Fact]
    public void Template_RejectsAnUnregisteredFamilyRatherThanBuildingAnUntrustedPair()
        => Assert.Throws<ArgumentOutOfRangeException>(
            () => MetamorphicTemplates.Build(new MetamorphicParameters(
                FamilyIndex: MetamorphicDecoder.FamilyTable.Length, 0, 0, 1, 1, 0)));

    // ── Executor ─────────────────────────────────────────────────────────────

    [Fact]
    public void Executor_AgreesSemanticallyAndOnMaterializationForEveryRangeStop()
    {
        foreach (var stop in MetamorphicDecoder.RangeStopTable)
        {
            var parameters = ParametersFor(stop, MetamorphicLimitMode.Default, 0, 0, optimize: true);
            var execution = MetamorphicExecutor.Execute(MetamorphicTemplates.Build(parameters));

            Assert.True(execution.Accepted, execution.RejectionReason);
            Assert.Equal(execution.Left!.Semantic, execution.Right!.Semantic);
            Assert.Equal(execution.Left.MaterializedItems, execution.Right.MaterializedItems);
            Assert.Equal(execution.Left.MaterializedStringChars, execution.Right.MaterializedStringChars);
            Assert.Equal(0, execution.Left.MaterializedStringChars);
            Assert.Equal(execution.Case.ExpectedItemTotal, execution.Left.MaterializedItems);
        }
    }

    [Fact]
    public void Executor_CrossesTheSameCumulativeBoundaryOnBothSides()
    {
        foreach (var stop in new[] { 1, 0, 5, 8 })
        {
            var cardinality = MetamorphicTemplates.RangeCardinality(stop);
            for (var budget = 1L; budget <= cardinality + 2; budget++)
            {
                var limits = new EvaluationLimits { MaxMaterializedItems = budget };
                var left = $"Output = count(range(1, {stop.ToString(CultureInfo.InvariantCulture)}))";
                var right = $"Output = range(1, {stop.ToString(CultureInfo.InvariantCulture)}).count";

                Assert.True(MetamorphicExecutor.TryObserve(left, limits, true, out var a, out _));
                Assert.True(MetamorphicExecutor.TryObserve(right, limits, true, out var b, out _));

                Assert.Equal(a.Semantic, b.Semantic);
                Assert.Equal(budget >= cardinality ? "ok" : "err", a.Semantic.Outcome);
                Assert.Equal(budget < cardinality, a.Semantic.IsResourceLimit);
            }
        }
    }

    [Fact]
    public void Executor_GivesEachSideFreshState()
    {
        // Running the identical program twice must produce byte-identical observations: a
        // leaked budget or a shared property cache would show up as different counters.
        const string source = "Output = range(1, 9).count";
        Assert.True(MetamorphicExecutor.TryObserve(source, null, true, out var first, out _));
        Assert.True(MetamorphicExecutor.TryObserve(source, null, true, out var second, out _));
        Assert.Equal(first, second);
        Assert.Equal(9, first.MaterializedItems);
    }

    [Fact]
    public void Executor_IsIsolatedAcrossAnUnrelatedEvaluation()
    {
        // A/B/A: left, unrelated source, left.
        MetamorphicExecutor.AssertIsolated("Output = count(range(1, 6))", null, true);
        MetamorphicExecutor.AssertIsolated("Output = range(1, 6).count", null, true);
        MetamorphicExecutor.AssertIsolated(
            "Output = range(1, 6).count", new EvaluationLimits { MaxMaterializedItems = 6 }, true);
    }

    [Fact]
    public void Executor_ReusesOneImmutableLimitsInstanceWithoutSharingCounters()
    {
        // The same EvaluationLimits object is deliberately handed to many runs; if it carried
        // run state, the second and later runs would see an exhausted budget.
        var shared = new EvaluationLimits { MaxMaterializedItems = 5, MaxCollectionItems = 5 };
        for (var repeat = 0; repeat < 4; repeat++)
        {
            var execution = MetamorphicExecutor.Execute(
                MetamorphicTemplates.Build(ParametersFor(5, MetamorphicLimitMode.Both, 0, 0, optimize: true)));
            Assert.True(execution.Accepted);
            Assert.Equal("ok", execution.Left!.Semantic.Outcome);

            Assert.True(MetamorphicExecutor.TryObserve("Output = range(1, 5).count", shared, true, out var direct, out _));
            Assert.Equal("ok", direct.Semantic.Outcome);
            Assert.Equal(5, direct.MaterializedItems);
        }
    }

    [Fact]
    public void Executor_ReportsAPreconditionFailureRatherThanAMismatch()
    {
        var rejected = MetamorphicTemplates.Build(ParametersFor(5, MetamorphicLimitMode.Default, 0, 0, true)) with
        {
            Precondition = MetamorphicPrecondition.Rejected("synthetic-precondition"),
        };

        var execution = MetamorphicExecutor.Execute(rejected);
        Assert.False(execution.Accepted);
        Assert.Equal("synthetic-precondition", execution.RejectionReason);
        Assert.Null(execution.Left);
        Assert.Null(execution.Right);
        Assert.Contains("rejected:synthetic-precondition", MetamorphicFingerprint.Describe(execution, null), StringComparison.Ordinal);
    }

    [Fact]
    public void Executor_RejectsUnparsableTemplateOutputInsteadOfComparingIt()
    {
        var broken = MetamorphicTemplates.Build(ParametersFor(5, MetamorphicLimitMode.Default, 0, 0, true)) with
        {
            LeftSource = "Output = count(range(1,",
        };

        var execution = MetamorphicExecutor.Execute(broken);
        Assert.False(execution.Accepted);
        Assert.Equal("left-parse-error", execution.RejectionReason);
    }

    // ── Comparator: every relation-specific diagnostic ───────────────────────

    [Fact]
    public void Comparator_AcceptsAnIdenticalPair()
        => Assert.Null(MetamorphicComparator.Compare(SampleCase(), Ok("5", 1, 5, 0), Ok("5", 1, 5, 0)));

    [Fact]
    public void Comparator_ReportsASemanticStructureMismatch()
    {
        var mismatch = MetamorphicComparator.Compare(SampleCase(), Ok("5", 1, 5, 0), Ok("L[1, 2]", 1, 5, 0));
        Assert.Equal(MetamorphicMismatchKind.SemanticStructure, mismatch!.Kind);
        Assert.Equal(MetamorphicMismatchClass.Semantic, mismatch.Class);
        Assert.Contains("neutral structural value", mismatch.Headline, StringComparison.Ordinal);
    }

    [Fact]
    public void Comparator_ReportsAnEmittedCountMismatch()
    {
        var mismatch = MetamorphicComparator.Compare(SampleCase(), Ok("5", 1, 5, 0), Ok("5", 2, 5, 0));
        Assert.Equal(MetamorphicMismatchKind.EmittedCount, mismatch!.Kind);
        Assert.Equal(MetamorphicMismatchClass.Semantic, mismatch.Class);
        Assert.Contains("emitted count", mismatch.Headline, StringComparison.Ordinal);
    }

    [Fact]
    public void Comparator_ReportsAnItemMaterializationMismatch()
    {
        var mismatch = MetamorphicComparator.Compare(SampleCase(), Ok("5", 1, 5, 0), Ok("5", 1, 10, 0));
        Assert.Equal(MetamorphicMismatchKind.MaterializedItems, mismatch!.Kind);
        Assert.Equal(MetamorphicMismatchClass.Operational, mismatch.Class);
        Assert.Contains("materialized collection-item slots", mismatch.Headline, StringComparison.Ordinal);
    }

    [Fact]
    public void Comparator_ReportsAStringMaterializationMismatch()
    {
        var mismatch = MetamorphicComparator.Compare(SampleCase(), Ok("5", 1, 5, 0), Ok("5", 1, 5, 3));
        Assert.Equal(MetamorphicMismatchKind.MaterializedStringChars, mismatch!.Kind);
        Assert.Equal(MetamorphicMismatchClass.Operational, mismatch.Class);
        Assert.Contains("materialized string UTF-16 units", mismatch.Headline, StringComparison.Ordinal);
    }

    [Fact]
    public void Comparator_ReportsAResourceLimitVerdictMismatch()
    {
        var languageFailure = Err("BadIndex", null, isResourceLimit: false);
        var budgetFailure = Err("MaterializationLimitExceeded", "limit=4", isResourceLimit: true);

        var mismatch = MetamorphicComparator.Compare(SampleCase(), languageFailure, budgetFailure);
        Assert.Equal(MetamorphicMismatchKind.ResourceLimitVerdict, mismatch!.Kind);
        Assert.Equal(MetamorphicMismatchClass.ResourceBoundary, mismatch.Class);
        Assert.Contains("resource-limit verdict", mismatch.Headline, StringComparison.Ordinal);
    }

    [Fact]
    public void Comparator_ReportsAnOutcomeMismatchBeforeAnythingElse()
    {
        var mismatch = MetamorphicComparator.Compare(
            SampleCase(), Ok("5", 1, 5, 0), Err("MaterializationLimitExceeded", "limit=4", true));
        Assert.Equal(MetamorphicMismatchKind.SemanticOutcome, mismatch!.Kind);
        Assert.Equal(MetamorphicMismatchClass.Semantic, mismatch.Class);
    }

    [Fact]
    public void Comparator_ReportsErrorKindAndPayloadMismatchesSeparately()
    {
        var kind = MetamorphicComparator.Compare(
            SampleCase(),
            Err("MaterializationLimitExceeded", "limit=4", true),
            Err("CollectionSizeLimitExceeded", "limit=4", true));
        Assert.Equal(MetamorphicMismatchKind.SemanticErrorCategory, kind!.Kind);
        Assert.Equal(MetamorphicMismatchClass.ResourceBoundary, kind.Class);

        var payload = MetamorphicComparator.Compare(
            SampleCase(),
            Err("CollectionSizeLimitExceeded", "limit=4,requested=5", true),
            Err("CollectionSizeLimitExceeded", "limit=4,requested=9", true));
        Assert.Equal(MetamorphicMismatchKind.SemanticErrorPayload, payload!.Kind);
    }

    [Fact]
    public void Comparator_ProducesAnActionableReproductionReport()
    {
        var report = MetamorphicInvariants.Run([0x00, 0x04, 0x01, 0x01, 0x01, 0x00]);
        var mismatch = new MetamorphicMismatch(
            MetamorphicMismatchKind.MaterializedItems, MetamorphicMismatchClass.Operational,
            "materialized collection-item slots", "5", "10");

        var text = MetamorphicInvariants.Describe(report, mismatch);
        foreach (var required in new[]
        {
            "dotted-collection-call", "MaterializedItems", "SemanticEqual", "ExactMaterializationEqual",
            "Output = count(range(1, 5))", "Output = range(1, 5).count", "maxMaterializedItems=5",
            "optimizer policy:", "precondition:", "left semantic:", "right semantic:",
            "left operational:", "right operational:", "fingerprint:", "metamorphic-replay --payload",
            "Lean-representable:", "raw fuzz input:", "replay payload (hex):",
        })
        {
            Assert.Contains(required, text, StringComparison.Ordinal);
        }
    }

    // ── Fingerprint ──────────────────────────────────────────────────────────

    [Fact]
    public void Fingerprint_IsStableAndDistinguishesEveryDeclaredDimension()
    {
        var seen = new Dictionary<string, MetamorphicParameters>(StringComparer.Ordinal);
        foreach (var parameters in AllParameters)
        {
            var execution = MetamorphicExecutor.Execute(MetamorphicTemplates.Build(parameters));
            var fingerprint = MetamorphicFingerprint.Describe(execution, null);

            Assert.Equal(fingerprint, MetamorphicFingerprint.Describe(execution, null));
            Assert.DoesNotContain("System.", fingerprint, StringComparison.Ordinal);
            Assert.False(seen.ContainsKey(fingerprint), $"{parameters} shares a fingerprint with {seen.GetValueOrDefault(fingerprint)}");
            seen[fingerprint] = parameters;
        }

        // The dimensions the report must be able to separate are all present.
        var sample = seen.Keys.First();
        foreach (var field in new[]
        {
            "family=", "status=", "precondition=", "limitMode=", "cumulativeOffset=",
            "perCollectionOffset=", "optimizer=", "left=", "right=",
            "semanticMismatch=", "resourceMismatch=", "operationalMismatch=",
        })
        {
            Assert.Contains(field, sample, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void Fingerprint_NamesTheMismatchClassAndKind()
    {
        var execution = MetamorphicExecutor.Execute(
            MetamorphicTemplates.Build(ParametersFor(5, MetamorphicLimitMode.Default, 0, 0, true)));
        var mismatch = new MetamorphicMismatch(
            MetamorphicMismatchKind.MaterializedItems, MetamorphicMismatchClass.Operational, "items", "5", "10");

        var fingerprint = MetamorphicFingerprint.Describe(execution, mismatch);
        Assert.Contains("operationalMismatch=MaterializedItems", fingerprint, StringComparison.Ordinal);
        Assert.Contains("semanticMismatch=none", fingerprint, StringComparison.Ordinal);
        Assert.Contains("resourceMismatch=none", fingerprint, StringComparison.Ordinal);
    }

    // ── The declared relations, exhaustively over Phase 1's whole space ──────

    [Fact]
    public void EveryParameterPoint_SatisfiesTheDeclaredSemanticAndOperationalRelations()
    {
        var accepted = 0;
        var rejected = new List<string>();

        foreach (var parameters in AllParameters)
        {
            // Exactly what the fuzz callback does, including its harness self-checks.
            MetamorphicInvariants.Check(parameters.Encode());

            var report = MetamorphicInvariants.Run(parameters.Encode());
            Assert.Null(report.Mismatch);
            if (report.Accepted) accepted++;
            else rejected.Add($"{parameters}: {report.RejectionReason}");
        }

        Assert.Empty(rejected);
        Assert.Equal(AllParameters.Count, accepted);
        Assert.True(accepted >= 500, $"expected a few hundred normalized parameter points, got {accepted}.");
    }

    // ── Neutral encoding mirrors the repository's established form ───────────

    [Fact]
    public void NeutralEncoding_MirrorsTheSemanticExplorerEncoding()
    {
        Result[] values =
        [
            new Result.Atom(0m),
            new Result.Atom(-12.5m),
            new Result.Str("abc"),
            new Result.SequenceValue([]),
            new Result.SequenceValue([new Result.Atom(1m), new Result.Atom(2m)]),
            new Result.ListValue([]),
            new Result.ListValue([new Result.Atom(7m)]),
            new Result.ListValue([new Result.SequenceValue([new Result.Atom(1m), new Result.Str("x")]), new Result.ListValue([])]),
        ];

        foreach (var value in values)
            Assert.Equal(SemanticExplorerHarness.Neutral(value), MetamorphicValue.Neutral(value));

        // Order and nesting stay distinguishable.
        Assert.NotEqual(
            MetamorphicValue.Neutral(new Result.ListValue([new Result.Atom(1m), new Result.Atom(2m)])),
            MetamorphicValue.Neutral(new Result.ListValue([new Result.Atom(2m), new Result.Atom(1m)])));
        Assert.NotEqual(
            MetamorphicValue.Neutral(new Result.ListValue([])),
            MetamorphicValue.Neutral(new Result.SequenceValue([])));
    }

    [Fact]
    public void NeutralEncoding_IsStackSafeForDeeplyNestedValues()
    {
        Result deep = new Result.Atom(1m);
        for (var i = 0; i < 50_000; i++) deep = new Result.ListValue([deep]);

        Assert.StartsWith("L[L[", MetamorphicValue.Neutral(deep), StringComparison.Ordinal);
    }

    [Fact]
    public void ErrorObservation_UsesStableKindsAndMachineIndependentPayloads()
    {
        var span = new SourceSpan(2, 3, 2, 7);

        Assert.Equal(
            "MaterializationLimitExceeded",
            MetamorphicValue.ErrorCategory(new EvalError.MaterializationLimitExceeded(5) { Span = span }));
        Assert.Equal(
            "limit=5,requested=6",
            MetamorphicValue.ErrorPayload(new EvalError.CollectionSizeLimitExceeded(5, 6) { Span = span }));

        // The context chain is unwrapped, and prose/positions never enter the identity.
        var wrapped = new EvalError.WithContext(
            new ProgramEvaluationContext(), new EvalError.DivByZero { Span = span });
        Assert.Equal("DivByZero", MetamorphicValue.ErrorCategory(wrapped));
        Assert.Null(MetamorphicValue.ErrorPayload(wrapped));
    }

    // ── Replay ───────────────────────────────────────────────────────────────

    [Fact]
    public void Replay_RunsEveryCuratedSeedCleanly()
        => Assert.Equal(0, MetamorphicReplay.RunReplay(["metamorphic-replay", SeedDirectory]));

    [Fact]
    public void Replay_IsDeterministicWhenRepeated()
    {
        Assert.Equal(0, MetamorphicReplay.RunReplay(["metamorphic-replay", SeedDirectory]));
        Assert.Equal(0, MetamorphicReplay.RunReplay(["metamorphic-replay", SeedDirectory]));

        foreach (var seed in LoadCuratedSeeds())
        {
            var first = MetamorphicInvariants.Run(seed.Payload);
            var second = MetamorphicInvariants.Run(seed.Payload);
            Assert.Equal(first.Fingerprint, second.Fingerprint);
            Assert.Equal(first.Execution.Left, second.Execution.Left);
            Assert.Equal(first.Execution.Right, second.Execution.Right);
        }
    }

    [Fact]
    public void Replay_UsesTheSameDecoderAndExecutorAsFuzzing()
    {
        foreach (var seed in LoadCuratedSeeds())
        {
            var decoded = MetamorphicDecoder.Decode(seed.Payload);
            Assert.Equal(seed.DeclaredFamily, decoded.Family);

            var report = MetamorphicInvariants.Run(seed.Payload);
            Assert.Equal(decoded, report.Parameters);
            Assert.Null(report.Mismatch);

            // The fuzz callback itself must accept every tracked seed.
            MetamorphicInvariants.Check(seed.Payload);
        }
    }

    [Fact]
    public void Replay_AcceptsAnAdHocEncodedPayload()
        => Assert.Equal(0, MetamorphicReplay.RunReplay(["metamorphic-replay", "--payload", "000401010100"]));

    [Fact]
    public void Replay_ReadsRawArtifactsWhoseContentIsThePayload()
    {
        // The triage path for a libFuzzer crash or corpus artifact: the FILE is the payload.
        var directory = Path.Combine(Path.GetTempPath(), "katlang-metamorphic-raw-" + Guid.NewGuid().ToString("N"));
        try
        {
            Assert.Equal(0, MetamorphicReplay.RunExportSeeds(["metamorphic-seeds", directory, SeedDirectory]));
            Assert.Equal(0, MetamorphicReplay.RunReplay(["metamorphic-replay", "--raw", directory]));

            // Arbitrary bytes are a valid payload too: the decoder is total.
            File.WriteAllBytes(Path.Combine(directory, "arbitrary"), [0xDE, 0xAD, 0xBE, 0xEF]);
            Assert.Equal(0, MetamorphicReplay.RunReplay(["metamorphic-replay", "--raw", directory]));
        }
        finally
        {
            if (Directory.Exists(directory)) Directory.Delete(directory, recursive: true);
        }
    }

    [Fact]
    public void Replay_ReportsMalformedSeedMetadataClearly()
    {
        AssertSeedProblem("bytes=00 00 00 01 01 00", "missing 'family=' field.");
        AssertSeedProblem("family=nope bytes=000000010100", "unknown relation family 'nope'.");
        AssertSeedProblem("family=dotted-collection-call", "missing 'bytes=' field.");
        AssertSeedProblem("family=dotted-collection-call bytes=", "'bytes=' is empty; a seed must carry at least one payload byte.");
        AssertSeedProblem("family=dotted-collection-call bytes=000", "odd number of hex digits");
        AssertSeedProblem("family=dotted-collection-call bytes=zz00", "non-hex pair");
        AssertSeedProblem(
            "family=dotted-collection-call bytes=" + new string('0', 1024),
            "exceeds the 256-byte seed payload limit.");

        static void AssertSeedProblem(string line, string expected)
        {
            Assert.False(MetamorphicSeedFile.TryParse(line, "test", 1, out _, out var problem));
            Assert.Contains(expected, problem, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void Replay_ReportsAMissingSeedPathInsteadOfSilentlyPassing()
        => Assert.Equal(1, MetamorphicReplay.RunReplay(
            ["metamorphic-replay", Path.Combine(SeedDirectory, "no-such-manifest.txt")]));

    [Fact]
    public void Replay_RefusesToReportSuccessWhenItVerifiedNothing()
    {
        Assert.Equal(2, MetamorphicReplay.RunReplay(["metamorphic-replay"]));

        var empty = Path.Combine(Path.GetTempPath(), "katlang-metamorphic-empty-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(empty);
        try
        {
            Assert.Equal(2, MetamorphicReplay.RunReplay(["metamorphic-replay", empty]));
        }
        finally
        {
            Directory.Delete(empty, recursive: true);
        }
    }

    [Fact]
    public void CuratedSeeds_CoverTheRequiredCategories()
    {
        var seeds = LoadCuratedSeeds();
        var cases = seeds.Select(seed => MetamorphicTemplates.Build(MetamorphicDecoder.Decode(seed.Payload))).ToList();

        Assert.InRange(seeds.Count, 9, 40);
        Assert.All(seeds, seed => Assert.Equal(MetamorphicFamily.DottedCollectionCall, seed.DeclaredFamily));
        Assert.All(seeds, seed => Assert.NotEqual("", seed.Description));

        Assert.Contains(cases, c => c.ExpectedItemTotal == 1);                       // smallest valid range
        Assert.Contains(cases, c => c.ExpectedItemTotal == 2);                       // nearest form to N = 0
        Assert.Contains(cases, c => c.ExpectedItemTotal > 2);                        // several items
        Assert.Contains(cases, c => c.Limits is null);                               // default limits
        Assert.Contains(cases, c => c.EnableOptimizations);                          // optimizations enabled
        Assert.Contains(cases, c => !c.EnableOptimizations);                         // optimizations disabled
        Assert.Contains(cases, c => c.Limits?.MaxMaterializedItems == c.ExpectedItemTotal - 1);   // one below
        Assert.Contains(cases, c => c.Limits?.MaxMaterializedItems == c.ExpectedItemTotal);       // exactly at
        Assert.Contains(cases, c => c.Limits?.MaxMaterializedItems == c.ExpectedItemTotal + 1);   // one above
        Assert.Contains(cases, c => c.Limits?.MaxCollectionItems == (int)c.ExpectedItemTotal);    // per-collection
    }

    [Fact]
    public void SeedExport_WritesOneCorpusFilePerSeed()
    {
        var directory = Path.Combine(Path.GetTempPath(), "katlang-metamorphic-seed-export-" + Guid.NewGuid().ToString("N"));
        try
        {
            Assert.Equal(0, MetamorphicReplay.RunExportSeeds(["metamorphic-seeds", directory, SeedDirectory]));

            var written = Directory.GetFiles(directory);
            Assert.Equal(LoadCuratedSeeds().Count, written.Length);
            Assert.All(written, file => Assert.Equal(
                MetamorphicParameters.EncodedLength, File.ReadAllBytes(file).Length));
        }
        finally
        {
            if (Directory.Exists(directory)) Directory.Delete(directory, recursive: true);
        }
    }

    // ── Helpers ──────────────────────────────────────────────────────────────

    private static List<MetamorphicSeed> LoadCuratedSeeds()
    {
        var problems = new List<string>();
        var seeds = MetamorphicSeedFile.Load(Path.Combine(SeedDirectory, "seeds.txt"), problems).ToList();
        Assert.Empty(problems);
        return seeds;
    }

    private static MetamorphicParameters ParametersFor(
        int rangeStop, MetamorphicLimitMode mode, int cumulativeOffset, int perCollectionOffset, bool optimize)
        => MetamorphicDecoder.Decode(
        [
            0,
            (byte)MetamorphicDecoder.RangeStopTable.IndexOf(rangeStop),
            (byte)MetamorphicDecoder.LimitModeTable.IndexOf(mode),
            (byte)MetamorphicDecoder.OffsetTable.IndexOf(cumulativeOffset),
            (byte)MetamorphicDecoder.OffsetTable.IndexOf(perCollectionOffset),
            (byte)(optimize ? 0 : 1),
        ]);

    private static MetamorphicCase SampleCase()
        => MetamorphicTemplates.Build(ParametersFor(5, MetamorphicLimitMode.CumulativeItems, 0, 0, optimize: true));

    private static MetamorphicOperationalObservation Ok(string structure, int emitted, long items, long stringChars)
        => new(MetamorphicSemanticObservation.Success(structure, emitted), 0, items, stringChars, 0, "on");

    private static MetamorphicOperationalObservation Err(string category, string? payload, bool isResourceLimit)
        => new(MetamorphicSemanticObservation.Failure(category, payload, isResourceLimit), 0, 0, 0, 0, "on");

    private static IEnumerable<byte[]> SamplePayloads()
    {
        yield return [];
        yield return [0x00];
        yield return [0xFF];
        yield return [0x00, 0x04, 0x01, 0x01, 0x01, 0x00];
        yield return [0xAB, 0xCD, 0xEF, 0x12, 0x34, 0x56];
        yield return [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF];
    }
}
