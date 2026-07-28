using System.Globalization;
using KatLang.Evaluation.Caching;
using KatLang.ParserFuzz;
using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests;

/// <summary>
/// Deterministic coverage for the Phase 3 metamorphic relation families: optimized-versus-generic
/// execution, cached-property reuse against rebuilt computation, entry-point parity, and the
/// resource-budget laws.
///
/// <para>Phase 3's additions are all execution-POLICY additions — a per-side profile, a run plan,
/// an execution order, an evidence gate — so the first thing these tests pin is that they are
/// completely inert for every Phase 1 and Phase 2 case. After that the sweeps are stratified the
/// same way Phase 2's are: each family's own dimensions crossed exhaustively under its first limit
/// mode, then every execution policy crossed against representative points.</para>
/// </summary>
public class MetamorphicPhase3FamilyTests
{
    private static string SeedDirectory =>
        Path.Combine(RepoRoot.Find(), "fuzz", "KatLang.ParserFuzz", "MetamorphicTestcases");

    private static List<MetamorphicParameters> Stratified { get; } =
        MetamorphicTemplates.EnumerateStratifiedParameters().ToList();

    private static IEnumerable<MetamorphicParameters> OfFamily(MetamorphicFamily family)
        => Stratified.Where(parameters => parameters.Family == family);

    private static readonly MetamorphicFamily[] Phase3Families =
    [
        MetamorphicFamily.OptimizerGenericParity,
        MetamorphicFamily.CachedPropertyReuse,
        MetamorphicFamily.EntryPointParity,
        MetamorphicFamily.BudgetLaw,
    ];

    private static readonly MetamorphicFamily[] LegacyFamilies =
    [
        MetamorphicFamily.DottedCollectionCall,
        MetamorphicFamily.DottedCollectionBuiltin,
        MetamorphicFamily.UserExtensionCall,
        MetamorphicFamily.DottedChain,
        MetamorphicFamily.BuiltinCallbackWrapper,
    ];

    private static MetamorphicCase Build(params byte[] payload)
        => MetamorphicTemplates.Build(MetamorphicDecoder.Decode(payload));

    private static byte FamilyByte(MetamorphicFamily family)
        => (byte)MetamorphicDecoder.FamilyTable.IndexOf(family);

    /// <summary>Builds one case of <paramref name="family"/> from its appended dimensions.</summary>
    private static MetamorphicCase BuildOf(
        MetamorphicFamily family, int mode, int primary, int secondary, int optimize, params int[] extras)
    {
        var payload = new byte[MetamorphicParameters.CommonPayloadLength + extras.Length];
        payload[0] = FamilyByte(family);
        payload[2] = (byte)mode;
        payload[3] = (byte)primary;
        payload[4] = (byte)secondary;
        payload[5] = (byte)optimize;
        for (var i = 0; i < extras.Length; i++)
            payload[MetamorphicParameters.CommonPayloadLength + i] = (byte)extras[i];
        return Build(payload);
    }

    // ── Backward compatibility: Phase 3 is inert for Phase 1 and Phase 2 ─────

    /// <summary>
    /// Every Phase 1 and Phase 2 parameter point still builds a case whose execution shape is
    /// exactly what it was before Phase 3 existed: both sides observed through
    /// <c>Evaluator.RunCountedObserved</c> under ONE shared limits instance and ONE shared
    /// optimizer policy, run sequentially, left first, with no evidence gate and no boundary law.
    ///
    /// <para>This is the compatibility surface that matters most. The payload tests in
    /// <c>MetamorphicPhase2FamilyTests</c> pin the decoded parameters and the generated program
    /// text; this pins that nothing Phase 3 added can change how those programs are RUN.</para>
    /// </summary>
    [Fact]
    public void EveryLegacyParameterPoint_KeepsItsExactPrePhase3ExecutionShape()
    {
        var checkedPoints = 0;
        foreach (var parameters in Stratified.Where(p => LegacyFamilies.Contains(p.Family)))
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            checkedPoints++;

            Assert.Equal(
                MetamorphicExecutionProfile.Observed(testCase.Limits, testCase.EnableOptimizations),
                testCase.LeftProfile);
            Assert.Equal(
                MetamorphicExecutionProfile.Observed(testCase.Limits, testCase.EnableOptimizations),
                testCase.RightProfile);
            Assert.Same(testCase.LeftProfile.Limits, testCase.RightProfile.Limits);
            Assert.Equal(MetamorphicRunPlan.Sequential, testCase.RunPlan);
            Assert.Equal(MetamorphicExecutionOrder.LeftFirst, testCase.ExecutionOrder);
            Assert.Equal(MetamorphicBoundaryStop.None, testCase.BoundaryStop);
            Assert.Null(testCase.ExpectedResourceKind);
            Assert.Null(testCase.InterferenceSource);
            Assert.True(testCase.LeftEvidence.IsEmpty);
            Assert.True(testCase.RightEvidence.IsEmpty);
            Assert.False(testCase.CollectsEvidence);
            Assert.Equal(MetamorphicSemanticRelation.SemanticEqual, testCase.SemanticRelation);
        }

        Assert.True(checkedPoints > 500, $"expected a broad legacy sweep, checked only {checkedPoints}.");
    }

    /// <summary>
    /// Every tracked seed still decodes to the same family and re-encodes to the same bytes, and
    /// the legacy seeds keep their exact generated program pair. Hand-written expectations, not
    /// derived from the templates: a template change that alters a committed seed must fail here.
    /// </summary>
    [Theory]
    [InlineData("000401010100", "Output = count(range(1, 5))", "Output = range(1, 5).count")]
    [InlineData("00000001 0100", "Output = count(range(1, 1))", "Output = range(1, 1).count")]
    [InlineData("00070100 0100", "Output = count(range(1, -3))", "Output = range(1, -3).count")]
    public void FrozenLegacySeeds_StillGenerateTheirExactProgramPair(string hex, string left, string right)
    {
        Assert.True(MetamorphicSeedFile.TryParseHex(hex, out var payload, out var problem), problem);
        var testCase = Build(payload);

        Assert.Equal(MetamorphicFamily.DottedCollectionCall, testCase.Family);
        Assert.Equal(left, testCase.LeftSource);
        Assert.Equal(right, testCase.RightSource);
        Assert.Equal(MetamorphicSurface.EvaluatorRunCountedObserved, testCase.LeftProfile.Surface);
        Assert.Equal(MetamorphicSurface.EvaluatorRunCountedObserved, testCase.RightProfile.Surface);
    }

    /// <summary>
    /// The registry's first five entries keep their exact identity AND their exact order, so byte
    /// 0 values 0-4 still select precisely the families they selected before Phase 3.
    ///
    /// <para>This is the payload-compatibility statement that matters for tracked seeds, and it is
    /// written out by hand rather than derived: appending a family is safe, reordering one silently
    /// changes what every committed Phase 1/2 payload means.</para>
    ///
    /// <para><b>What appending does change</b> is the meaning of byte 0 values at or above the old
    /// family count for payloads LONGER than six bytes — the family index is a modulus over the
    /// registry, so a seven-byte payload whose first byte was 5 used to wrap to index 0 and now
    /// reaches the first Phase 3 family. That was equally true when Phase 2 appended to Phase 1's
    /// single-entry table, and it is exactly why the tracked seeds all carry a first byte inside
    /// the family range and why version-zero payloads force index 0 unconditionally. Untracked
    /// campaign corpora are regenerated scratch data and carry no compatibility claim.</para>
    /// </summary>
    [Fact]
    public void TheFirstFiveRegistryEntries_KeepTheirExactIdentityAndOrder()
    {
        string[] frozen =
        [
            "dotted-collection-call",
            "dotted-collection-builtin",
            "user-extension-call",
            "dotted-chain",
            "builtin-callback-wrapper",
        ];

        for (var index = 0; index < frozen.Length; index++)
        {
            Assert.Equal(frozen[index], MetamorphicFamilyRegistry.All[index].Id);

            // A seven-byte payload whose first byte is `index` must still reach that same family.
            var payload = new byte[MetamorphicParameters.CommonPayloadLength + 1];
            payload[0] = (byte)index;
            Assert.Equal(MetamorphicFamilyRegistry.All[index].Family, MetamorphicDecoder.Decode(payload).Family);
        }

        // Frozen Phase 1/2 families + the Phase 3 families + the appended Group E
        // spread-spelling-parity family (spread(X) vs X.spread).
        Assert.Equal(frozen.Length + Phase3Families.Length + 1, MetamorphicFamilyRegistry.All.Length);
    }

    /// <summary>Old payload LENGTHS still select old families: nothing Phase 3 added is reachable in six bytes.</summary>
    [Fact]
    public void ShortPayloads_NeverSelectAPhase3Family()
    {
        for (var length = 0; length <= MetamorphicParameters.CommonPayloadLength; length++)
        {
            for (var value = 0; value <= byte.MaxValue; value++)
            {
                var payload = new byte[length];
                Array.Fill(payload, (byte)value);
                var decoded = MetamorphicDecoder.Decode(payload);
                Assert.DoesNotContain(decoded.Family, Phase3Families);
                Assert.Equal(MetamorphicFamily.DottedCollectionCall, decoded.Family);
            }
        }
    }

    /// <summary>The whole tracked seed corpus still replays with no mismatch and no non-determinism.</summary>
    [Fact]
    public void EveryTrackedSeed_ReplaysDeterministicallyWithoutMismatch()
    {
        var problems = new List<string>();
        var seeds = Directory.EnumerateFiles(SeedDirectory)
            .OrderBy(path => path, StringComparer.Ordinal)
            .SelectMany(path => MetamorphicSeedFile.Load(path, problems))
            .ToList();

        Assert.Empty(problems);
        Assert.NotEmpty(seeds);

        foreach (var seed in seeds)
        {
            var first = MetamorphicInvariants.Run(seed.Payload);
            var again = MetamorphicInvariants.Run(seed.Payload);

            Assert.Equal(seed.DeclaredFamily, first.Parameters.Family);
            Assert.Equal(first.Fingerprint, again.Fingerprint);
            Assert.Equal(first.Execution.Left, again.Execution.Left);
            Assert.Equal(first.Execution.Right, again.Execution.Right);
            if (first.Mismatch is { } mismatch)
                Assert.Fail($"{seed.Location}: {MetamorphicInvariants.Describe(first, mismatch)}");
        }
    }

    // ── Registry and declaration completeness ────────────────────────────────

    [Fact]
    public void EveryPhase3Family_IsCompletelyDeclared()
    {
        foreach (var family in Phase3Families)
        {
            var definition = MetamorphicFamilyRegistry.Get(family);

            Assert.False(string.IsNullOrWhiteSpace(definition.Id));
            Assert.False(string.IsNullOrWhiteSpace(definition.Group));
            Assert.False(string.IsNullOrWhiteSpace(definition.Description));
            Assert.NotEmpty(definition.SupportedLimitModes);
            Assert.NotNull(definition.Normalize);
            Assert.NotNull(definition.ValidatePreconditions);
            Assert.NotNull(definition.Build);
            Assert.NotNull(definition.DescribeVariantCore);
            Assert.False(definition.UsesLegacyRangeStop);
            Assert.InRange(definition.ExtraDimensionCount, 1, MetamorphicParameters.MaxExtraDimensions);
            Assert.True(definition.LeanRepresentable);
        }

        // Ids and family values stay unique across ALL nine families.
        Assert.Equal(
            MetamorphicFamilyRegistry.All.Length,
            MetamorphicFamilyRegistry.All.Select(d => d.Id).Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(
            MetamorphicFamilyRegistry.All.Length,
            MetamorphicFamilyRegistry.All.Select(d => d.Family).Distinct().Count());
    }

    /// <summary>Every registered surface has an adapter, a unique id, and the outcome facet.</summary>
    [Fact]
    public void EverySurface_IsRegisteredWithAnAdapterAndHonestFacets()
    {
        foreach (var surface in Enum.GetValues<MetamorphicSurface>())
        {
            var definition = MetamorphicSurfaces.Get(surface);
            Assert.Equal(surface, definition.Surface);
            Assert.False(string.IsNullOrWhiteSpace(definition.Id));
            Assert.True(definition.Facets.HasFlag(MetamorphicFacets.Outcome));

            // Only the observed evaluator entry point hands back a budget, and only it accepts an
            // optimizer policy. Any other surface claiming either would be claiming a capability
            // the production signature does not have.
            var isObserved = surface == MetamorphicSurface.EvaluatorRunCountedObserved;
            Assert.Equal(isObserved, definition.Facets.HasFlag(MetamorphicFacets.OperationalCounters));
            Assert.Equal(isObserved, definition.SupportsOptimizerPolicy);

            // Engine surfaces take source text and report a parse failure as an outcome; evaluator
            // surfaces consume an already-parsed root.
            Assert.Equal(!definition.UsesFrontEndPipeline, definition.RequiresParsableSource);

            // The engine's public error type keeps a message and a span, not the structured
            // EvalError, so no engine surface may claim the structured-error facet.
            Assert.Equal(
                !definition.UsesFrontEndPipeline, definition.Facets.HasFlag(MetamorphicFacets.StructuredError));
        }
    }

    /// <summary>No registered surface pair may be vacuous, and none may need an impossible source.</summary>
    [Fact]
    public void EverySurfacePair_ComparesMoreThanTheBareOutcome()
    {
        foreach (var pair in MetamorphicEntryPointTemplate.Pairs)
        {
            Assert.NotEqual(MetamorphicFacets.Outcome, pair.Shared);
            Assert.True(pair.Shared.HasFlag(MetamorphicFacets.Outcome));
            Assert.NotEqual(pair.Left, pair.Right);
        }
    }

    /// <summary>Every resource dimension is declared with a legal minimum and a real stop kind.</summary>
    [Fact]
    public void EveryResourceDimension_IsCompletelyDeclared()
    {
        foreach (var dimension in MetamorphicBoundaryPolicy.All)
        {
            Assert.False(string.IsNullOrWhiteSpace(dimension.Id));
            Assert.InRange(dimension.MinimumLegalLimit, 0, 1);
            Assert.True(dimension.SearchCeiling > dimension.MinimumLegalLimit);
            Assert.NotEqual(MetamorphicBoundaryStop.None, dimension.Stop);
            Assert.False(string.IsNullOrWhiteSpace(dimension.ExpectedResourceKind));

            // Constructing the limits at the minimum and at the ceiling must both be legal.
            _ = dimension.WithValue(Math.Max(dimension.MinimumLegalLimit, 1));
            _ = dimension.WithValue(dimension.SearchCeiling);
        }
    }

    // ── Group A: optimizer versus generic ────────────────────────────────────

    /// <summary>
    /// Every optimizer template really takes the path it declares, and the generic run really is
    /// generic. This is what makes "optimizer versus generic" a classification rather than a hope:
    /// a template whose optimizer shape changes fails HERE rather than silently degrading the
    /// campaign into comparing two identical executions.
    /// </summary>
    [Fact]
    public void OptimizerSources_TakeExactlyTheDeclaredPath()
    {
        foreach (var source in MetamorphicOptimizerTemplate.Sources)
        {
            var optimized = ObserveWithEvidence(source.Source, enableOptimizations: true);
            var generic = ObserveWithEvidence(source.Source, enableOptimizations: false);

            var optimizedPaths = Assert.IsType<MetamorphicOptimizerEvidence>(optimized.OptimizerEvidence).Paths;
            var genericPaths = Assert.IsType<MetamorphicOptimizerEvidence>(generic.OptimizerEvidence).Paths;

            Assert.True(
                (optimizedPaths & source.RequiredPaths) == source.RequiredPaths,
                $"'{source.Id}' declares {source.RequiredPaths} but the optimized run took {optimizedPaths}.");

            Assert.False(
                genericPaths.HasFlag(MetamorphicOptimizerPath.OptimizedLoopSelected),
                $"'{source.Id}' selected an optimized loop with optimizations DISABLED.");
            Assert.False(
                genericPaths.HasFlag(MetamorphicOptimizerPath.FusedPipelineExecuted),
                $"'{source.Id}' fused a pipeline with optimizations DISABLED.");
            Assert.False(
                genericPaths.HasFlag(MetamorphicOptimizerPath.PlannedExpressionExecuted),
                $"'{source.Id}' executed a planned expression with optimizations DISABLED.");
        }
    }

    /// <summary>The table distinguishes every optimizer path the runtime distinguishes.</summary>
    [Fact]
    public void OptimizerTable_CoversEveryDistinguishedExecutionPath()
    {
        var declared = MetamorphicOptimizerTemplate.Sources
            .Aggregate(MetamorphicOptimizerPath.None, (all, source) => all | source.RequiredPaths);

        Assert.True(declared.HasFlag(MetamorphicOptimizerPath.OptimizedLoopSelected));
        Assert.True(declared.HasFlag(MetamorphicOptimizerPath.PlannedExpressionExecuted));
        Assert.True(declared.HasFlag(MetamorphicOptimizerPath.GenericExpressionInsideOptimizedLoop));
        Assert.True(declared.HasFlag(MetamorphicOptimizerPath.LoopFallbackExecuted));
        Assert.True(declared.HasFlag(MetamorphicOptimizerPath.GenericLoopExecuted));
        Assert.True(declared.HasFlag(MetamorphicOptimizerPath.FusedPipelineExecuted));
        Assert.True(declared.HasFlag(MetamorphicOptimizerPath.LoopShortCircuited));
    }

    /// <summary>
    /// The zero-iteration repeat is classified as a SHORT CIRCUIT, not as a generic loop: the
    /// count check returns before the optimizer is consulted at all, so nothing recorded a
    /// fallback. Collapsing the two would let a template claim it exercised a fallback it never
    /// reached.
    /// </summary>
    [Fact]
    public void ZeroIterationRepeat_IsShortCircuitedRatherThanFallenBack()
    {
        var observation = ObserveWithEvidence("MmStep = x + 1\nOutput = MmStep.repeat(0, 0)", enableOptimizations: true);
        var evidence = Assert.IsType<MetamorphicOptimizerEvidence>(observation.OptimizerEvidence);

        Assert.True(evidence.Paths.HasFlag(MetamorphicOptimizerPath.LoopShortCircuited));
        Assert.False(evidence.Paths.HasFlag(MetamorphicOptimizerPath.GenericLoopExecuted));
        Assert.False(evidence.Paths.HasFlag(MetamorphicOptimizerPath.LoopFallbackExecuted));
        Assert.Equal(0, evidence.OptimizedLoopHits);
        Assert.Equal(0, evidence.OptimizedLoopFallbacks);
        Assert.Equal(1, evidence.LoopExecutions);
    }

    /// <summary>
    /// The whole optimizer family: every accepted point agrees semantically and never charges more
    /// optimized than generic, and at least one point genuinely charges LESS (otherwise the
    /// directional relation would be untested).
    /// </summary>
    [Fact]
    public void OptimizerFamily_AgreesSemanticallyAndNeverChargesMore()
    {
        var accepted = 0;
        var strictlyCheaper = 0;

        foreach (var parameters in OfFamily(MetamorphicFamily.OptimizerGenericParity))
        {
            var execution = MetamorphicExecutor.Execute(MetamorphicTemplates.Build(parameters));
            if (execution is not { Accepted: true, Left: { } left, Right: { } right }) continue;

            accepted++;
            Assert.Null(MetamorphicComparator.Compare(execution.Case, left, right));
            Assert.Equal(left.Semantic, right.Semantic);
            Assert.True(left.MaterializedItems <= right.MaterializedItems);
            Assert.True(left.EvaluationSteps <= right.EvaluationSteps);
            if (left.MaterializedItems < right.MaterializedItems || left.EvaluationSteps < right.EvaluationSteps)
                strictlyCheaper++;
        }

        Assert.True(accepted > 50, $"expected a broad optimizer sweep, accepted only {accepted}.");
        Assert.True(strictlyCheaper > 0, "no optimizer point charged strictly less; the relation is untested.");
    }

    /// <summary>
    /// An optimizer template whose declared path is not taken is REJECTED by name, never compared.
    /// Built by asking a fusion template to run with optimizations off on BOTH sides.
    /// </summary>
    [Fact]
    public void OptimizerCase_IsRejectedWhenTheDeclaredPathIsNotExercised()
    {
        var fused = MetamorphicOptimizerTemplate.Sources
            .Select((source, index) => (source, index))
            .First(entry => entry.source.RequiredPaths.HasFlag(MetamorphicOptimizerPath.FusedPipelineExecuted));

        var testCase = BuildOf(MetamorphicFamily.OptimizerGenericParity, 0, 1, 1, 0, fused.index, 0);
        var forcedGeneric = testCase with
        {
            LeftProfile = testCase.LeftProfile with { EnableOptimizations = false },
        };

        var execution = MetamorphicExecutor.Execute(forcedGeneric);
        Assert.False(execution.Accepted);
        Assert.Equal("left-optimizer-path-not-exercised", execution.RejectionReason);
    }

    /// <summary>
    /// The per-collection ceiling is optimizer-INDEPENDENT: the fused pipeline must reject exactly
    /// the collection sizes the generic path rejects. This is the one budget the family compares,
    /// and it is compared at every size around the boundary.
    /// </summary>
    [Fact]
    public void OptimizedAndGenericPaths_ShareTheSamePerCollectionBoundary()
    {
        const string source = "MmEven(x) = x mod 2 == 0\nOutput = range(1, 12).filter(MmEven).count";

        for (var limit = 1; limit <= 16; limit++)
        {
            var limits = new EvaluationLimits { MaxCollectionItems = limit };
            var optimized = Observe(source, limits, enableOptimizations: true);
            var generic = Observe(source, limits, enableOptimizations: false);

            Assert.Equal(generic.Semantic, optimized.Semantic);
        }
    }

    // ── Group B: cached versus rebuilt ───────────────────────────────────────

    /// <summary>
    /// The cached side evaluates the property ONCE and serves every later access from the cache;
    /// the rebuilt side evaluates an independent property per use and never serves one from cache.
    /// </summary>
    [Fact]
    public void CacheTemplates_ProveReuseOnOneSideAndIndependenceOnTheOther()
    {
        var checkedTemplates = 0;

        for (var sourceIndex = 0; sourceIndex < MetamorphicCacheTemplate.SourceCount; sourceIndex++)
        for (var reuseIndex = 0; reuseIndex < MetamorphicCacheTemplate.ReuseCounts.Length; reuseIndex++)
        {
            var source = MetamorphicCacheTemplate.Sources[sourceIndex];
            if (!source.RequiresReuseEvidence) continue;

            var uses = MetamorphicCacheTemplate.ReuseCounts[reuseIndex];
            var testCase = BuildOf(MetamorphicFamily.CachedPropertyReuse, 0, 1, 1, 0, sourceIndex, reuseIndex, 0);
            checkedTemplates++;

            var cached = ObserveWithEvidence(testCase.LeftSource, enableOptimizations: true);
            var rebuilt = ObserveWithEvidence(testCase.RightSource, enableOptimizations: true);

            var cachedEvidence = Assert.IsType<MetamorphicCacheEvidence>(cached.CacheEvidence);
            var rebuiltEvidence = Assert.IsType<MetamorphicCacheEvidence>(rebuilt.CacheEvidence);

            Assert.True(
                cachedEvidence.Hits >= uses - 1,
                $"'{source.Id}' x{uses}: cached side recorded only {cachedEvidence.Hits} hit(s).");
            Assert.Equal(0, rebuiltEvidence.Hits);
            Assert.True(
                rebuiltEvidence.Misses >= uses,
                $"'{source.Id}' x{uses}: rebuilt side recorded only {rebuiltEvidence.Misses} miss(es).");

            // The property really was evaluated once on the cached side, and once per copy on the
            // rebuilt side, which is what makes the work relation directional rather than trivial.
            Assert.True(cachedEvidence.Stores < rebuiltEvidence.Stores || cachedEvidence.Stores == 1);
        }

        Assert.True(checkedTemplates > 20, $"expected a broad cache sweep, checked only {checkedTemplates}.");
    }

    /// <summary>The rebuilt form binds DISTINCT properties, so it cannot accidentally share an entry.</summary>
    [Fact]
    public void RebuiltForm_UsesDistinctPropertiesRatherThanInliningTheExpression()
    {
        var testCase = BuildOf(MetamorphicFamily.CachedPropertyReuse, 0, 1, 1, 0, 2, 1, 0);

        Assert.Contains("MmA1 = ", testCase.RightSource, StringComparison.Ordinal);
        Assert.Contains("MmA2 = ", testCase.RightSource, StringComparison.Ordinal);
        Assert.Contains("MmA3 = ", testCase.RightSource, StringComparison.Ordinal);
        Assert.DoesNotContain("MmA1", testCase.LeftSource, StringComparison.Ordinal);
        Assert.Equal(3, MetamorphicCacheTemplate.ReuseCounts[1]);
    }

    /// <summary>Every accepted cache point agrees semantically and the cached side never charges more.</summary>
    [Fact]
    public void CacheFamily_AgreesSemanticallyAndNeverChargesMore()
    {
        var accepted = 0;
        var strictlyCheaper = 0;

        foreach (var parameters in OfFamily(MetamorphicFamily.CachedPropertyReuse))
        {
            var execution = MetamorphicExecutor.Execute(MetamorphicTemplates.Build(parameters));
            if (execution is not { Accepted: true, Left: { } left, Right: { } right }) continue;

            accepted++;
            Assert.Null(MetamorphicComparator.Compare(execution.Case, left, right));
            Assert.Equal(left.Semantic, right.Semantic);
            if (!left.Semantic.IsResourceLimit && !right.Semantic.IsResourceLimit)
            {
                Assert.True(left.MaterializedItems <= right.MaterializedItems);
                Assert.True(left.EvaluationSteps <= right.EvaluationSteps);
                if (left.MaterializedItems < right.MaterializedItems
                    || left.MaterializedStringChars < right.MaterializedStringChars
                    || left.EvaluationSteps < right.EvaluationSteps)
                {
                    strictlyCheaper++;
                }
            }
        }

        Assert.True(accepted > 50, $"expected a broad cache sweep, accepted only {accepted}.");
        Assert.True(strictlyCheaper > 0, "no cached point charged strictly less; the relation is untested.");
    }

    /// <summary>
    /// An erroring property is NOT stored, so a later access re-evaluates it. This is the current
    /// contract, and the template that names it exists to keep the contract visible.
    /// </summary>
    [Fact]
    public void ErroringProperty_IsNotCachedAndBothFormsReportTheSameError()
    {
        var index = MetamorphicCacheTemplate.Sources
            .Select((source, i) => (source, i))
            .First(entry => entry.source.Id == "erroring-property").i;

        var testCase = BuildOf(MetamorphicFamily.CachedPropertyReuse, 0, 1, 1, 0, index, 0, 0);
        var execution = MetamorphicExecutor.Execute(testCase);

        Assert.True(execution.Accepted, execution.RejectionReason);
        var left = Assert.IsType<MetamorphicOperationalObservation>(execution.Left);
        var right = Assert.IsType<MetamorphicOperationalObservation>(execution.Right);

        Assert.Equal("err", left.Semantic.Outcome);
        Assert.Equal(left.Semantic, right.Semantic);
        Assert.Equal(0, Assert.IsType<MetamorphicCacheEvidence>(left.CacheEvidence).Stores);
        Assert.Null(MetamorphicComparator.Compare(testCase, left, right));
    }

    /// <summary>
    /// MEASURED cache-surface fact, pinned so the template table cannot quietly claim otherwise:
    /// a bare property reference in an ordinary call ARGUMENT position records no zero-argument
    /// property cache request at all, while the SAME property used as a dotted receiver does.
    ///
    /// <para>Both forms produce identical values, so this is a missed reuse rather than a defect —
    /// the repository documents the cache as something property-style access <i>may</i> use. It is
    /// recorded here because the cached-versus-rebuilt family would otherwise silently claim a
    /// reuse it demonstrably does not get, and because a future change in either direction should
    /// be a deliberate, visible one.</para>
    /// </summary>
    [Fact]
    public void ArgumentPositionPropertyReference_DoesNotConsultTheCache()
    {
        var argument = ObserveWithEvidence("MmA = range(1, 6)\nOutput = sum(MmA), sum(MmA)", enableOptimizations: true);
        var receiver = ObserveWithEvidence("MmA = range(1, 6)\nOutput = MmA.sum, MmA.sum", enableOptimizations: true);

        var argumentCache = Assert.IsType<MetamorphicCacheEvidence>(argument.CacheEvidence);
        var receiverCache = Assert.IsType<MetamorphicCacheEvidence>(receiver.CacheEvidence);

        Assert.Equal(0, argumentCache.Requests);
        Assert.Equal(0, argumentCache.Hits);
        Assert.Equal(2, receiverCache.Requests);
        Assert.Equal(1, receiverCache.Hits);

        // The values are the same either way; only the reuse differs.
        Assert.Equal(receiver.Semantic.Structure, argument.Semantic.Structure);
        Assert.Equal(receiver.Semantic.EmittedCount, argument.Semantic.EmittedCount);
    }

    /// <summary>A cumulative budget cannot bind equally on the two forms, so those modes are rejected by name.</summary>
    [Fact]
    public void CacheFamily_RejectsCumulativeBudgetsByName()
    {
        var definition = MetamorphicFamilyRegistry.Get(MetamorphicFamily.CachedPropertyReuse);

        for (var mode = 0; mode < definition.SupportedLimitModes.Length; mode++)
        {
            var testCase = BuildOf(MetamorphicFamily.CachedPropertyReuse, mode, 1, 1, 0, 2, 0, 0);
            var isCumulative = definition.SupportedLimitModes[mode]
                is MetamorphicLimitMode.CumulativeItems
                or MetamorphicLimitMode.Both
                or MetamorphicLimitMode.CumulativeStrings;

            Assert.Equal(!isCumulative, testCase.Precondition.Satisfied);
            if (isCumulative)
                Assert.Equal("rebuilt-form-does-not-share-the-cumulative-budget", testCase.Precondition.Reason);
        }
    }

    // ── Group C: entry-point parity ──────────────────────────────────────────

    /// <summary>Every accepted entry-point point agrees on every facet the two surfaces share.</summary>
    [Fact]
    public void EntryPointFamily_AgreesOnEverySharedFacet()
    {
        var accepted = 0;
        var comparedRenderedText = 0;
        var comparedHostAtoms = 0;

        foreach (var parameters in OfFamily(MetamorphicFamily.EntryPointParity))
        {
            var execution = MetamorphicExecutor.Execute(MetamorphicTemplates.Build(parameters));
            if (execution is not { Accepted: true, Left: { } left, Right: { } right }) continue;

            accepted++;
            Assert.Null(MetamorphicComparator.Compare(execution.Case, left, right));

            var shared = left.Facets & right.Facets;
            if (shared.HasFlag(MetamorphicFacets.HostAtoms)) comparedHostAtoms++;
            if (shared.HasFlag(MetamorphicFacets.RenderedText)
                && left.Projection?.RenderedProjection == right.Projection?.RenderedProjection)
            {
                comparedRenderedText++;
            }
        }

        Assert.True(accepted > 100, $"expected a broad entry-point sweep, accepted only {accepted}.");
        Assert.True(comparedHostAtoms > 0, "no entry-point pair compared the host-atom projection.");
        Assert.True(comparedRenderedText > 0, "no entry-point pair compared rendered text.");
    }

    /// <summary>
    /// Observing a run must not change it: <c>RunCountedObserved</c> agrees with <c>RunCounted</c>
    /// on value, emitted count, and structured error for every entry-point source — and attaching
    /// the optimizer diagnostics channel changes neither the result nor the counters.
    /// </summary>
    [Fact]
    public void ObservedExecution_DoesNotChangeSemanticsOrCounters()
    {
        foreach (var source in MetamorphicEntryPointTemplate.Sources.Where(s => s.Parses))
        {
            var observed = Observe(source.Source, limits: null, enableOptimizations: true);
            var withEvidence = ObserveWithEvidence(source.Source, enableOptimizations: true);

            Assert.Equal(observed.Semantic, withEvidence.Semantic);
            Assert.Equal(observed.EvaluationSteps, withEvidence.EvaluationSteps);
            Assert.Equal(observed.MaterializedItems, withEvidence.MaterializedItems);
            Assert.Equal(observed.MaterializedStringChars, withEvidence.MaterializedStringChars);
            Assert.Equal(observed.PeakDynamicDepth, withEvidence.PeakDynamicDepth);

            var block = new Expr.Block(Parser.Parse(source.Source).Root);
            var counted = Evaluator.RunCounted(block, new RunScopedZeroArgPropertyResultCache());
            Assert.Equal(observed.Semantic.Outcome == "err", counted.IsError);
            if (!counted.IsError)
                Assert.Equal(observed.Semantic.EmittedCount, counted.Value.EmittedCount);
        }
    }

    /// <summary>
    /// The rendering surfaces are bounded and honest about their PROJECTION.
    ///
    /// <para><c>EvaluateToString</c> returns space-joined host atoms on success and the structured
    /// diagnostic rendering otherwise, so it equals <c>Run(...).ToDisplayString()</c> on failures
    /// and deliberately differs on successes. Both are always within the configured display limit.</para>
    /// </summary>
    [Fact]
    public void EngineRenderingSurfaces_AreBoundedAndDeclareTheirProjection()
    {
        foreach (var source in MetamorphicEntryPointTemplate.Sources)
        {
            var run = KatLangEngine.Run(source.Source);
            var display = run.ToDisplayString();
            var joined = KatLangEngine.EvaluateToString(source.Source);

            Assert.True(display.Length <= EvaluationLimits.MaxSupportedDisplayLength);
            Assert.True(joined.Length <= EvaluationLimits.MaxSupportedDisplayLength);

            if (run is RunResult.Success) continue;

            // Every non-success renders identically through both surfaces.
            Assert.Equal(display, joined);
        }
    }

    /// <summary>Atom projection is only compared where the surface really produces it.</summary>
    [Fact]
    public void AtomProjectionSurfaces_AgreeWherePresentAndAreAbsentOnFailure()
    {
        foreach (var source in MetamorphicEntryPointTemplate.Sources.Where(s => s.Parses))
        {
            var flat = ObserveThrough(MetamorphicSurface.EvaluatorRunFlat, source.Source);
            var engine = ObserveThrough(MetamorphicSurface.EngineEvaluateToAtoms, source.Source);

            Assert.Equal(flat.Semantic.Outcome, engine.Semantic.Outcome);
            Assert.Equal(flat.Projection?.HostAtoms, engine.Projection?.HostAtoms);
            if (flat.Semantic.Outcome == "err") Assert.Null(flat.Projection?.HostAtoms);
        }
    }

    /// <summary>A malformed source may only be paired with two engine surfaces; anything else is rejected.</summary>
    [Fact]
    public void MalformedSource_IsRejectedForSurfacesThatNeedAParsableRoot()
    {
        var parseFailure = MetamorphicEntryPointTemplate.Sources
            .Select((source, index) => (source, index))
            .First(entry => !entry.source.Parses);

        for (var pairIndex = 0; pairIndex < MetamorphicEntryPointTemplate.PairCount; pairIndex++)
        {
            var testCase = BuildOf(
                MetamorphicFamily.EntryPointParity, 0, 1, 1, 0, parseFailure.index, pairIndex, 0);
            var pair = MetamorphicEntryPointTemplate.Pairs[pairIndex];

            Assert.Equal(!pair.NeedsParsableSource, testCase.Precondition.Satisfied);
            if (pair.NeedsParsableSource)
                Assert.Equal("surface-pair-requires-a-parsable-source", testCase.Precondition.Reason);
        }
    }

    /// <summary>Independent entry-point invocations reusing one options object stay identical, in both orders.</summary>
    [Fact]
    public void EntryPointInvocations_AreIsolatedInEitherExecutionOrder()
    {
        var options = new RunOptions { EvaluationLimits = new EvaluationLimits { MaxMaterializedItems = 5_000 } };

        foreach (var source in MetamorphicEntryPointTemplate.Sources)
        {
            var firstRun = KatLangEngine.Run(source.Source, options).ToDisplayString();
            _ = KatLangEngine.Run(MetamorphicExecutor.IsolationProbeSource, options).ToDisplayString();
            var secondRun = KatLangEngine.Run(source.Source, options).ToDisplayString();
            Assert.Equal(firstRun, secondRun);

            var firstString = KatLangEngine.EvaluateToString(source.Source, options);
            _ = KatLangEngine.EvaluateToString(MetamorphicExecutor.IsolationProbeSource, options);
            var secondString = KatLangEngine.EvaluateToString(source.Source, options);
            Assert.Equal(firstString, secondString);
        }
    }

    // ── Group D: budget laws ─────────────────────────────────────────────────

    /// <summary>Every accepted budget-law point satisfies the law it declared.</summary>
    [Fact]
    public void BudgetLawFamily_SatisfiesEveryDeclaredLaw()
    {
        var accepted = 0;
        var byLaw = new SortedDictionary<string, int>(StringComparer.Ordinal);

        foreach (var parameters in OfFamily(MetamorphicFamily.BudgetLaw))
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            var execution = MetamorphicExecutor.Execute(testCase);
            if (execution is not { Accepted: true, Left: { } left, Right: { } right }) continue;

            accepted++;
            var law = MetamorphicBudgetLawTemplate.LawOf(parameters).ToString();
            byLaw[law] = byLaw.GetValueOrDefault(law) + 1;

            if (MetamorphicComparator.Compare(testCase, left, right) is { } mismatch)
                Assert.Fail($"{parameters}: {mismatch.Headline}\n  left: {left}\n  right: {right}");
        }

        Assert.True(accepted > 100, $"expected a broad budget-law sweep, accepted only {accepted}.");
        foreach (var law in Enum.GetValues<MetamorphicBudgetLaw>())
            Assert.True(byLaw.ContainsKey(law.ToString()), $"no accepted case exercised {law}.");
    }

    /// <summary>
    /// The exact boundary law, verified independently of the harness: for every (source,
    /// dimension) pair with a derivable boundary, one below FAILS with the dimension's own
    /// structured resource error, exactly at it SUCCEEDS, and above it succeeds identically.
    ///
    /// <para>Only ONE limit changes across the three executions; every other policy comes from the
    /// dimension's own baseline, which is what keeps the comparison a boundary test rather than a
    /// policy change.</para>
    /// </summary>
    [Fact]
    public void ExactBoundaries_FailBelow_SucceedAt_AndStaySucceededAbove()
    {
        var verified = 0;
        var byDimension = new SortedDictionary<string, int>(StringComparer.Ordinal);

        foreach (var source in MetamorphicBudgetLawTemplate.Sources)
        foreach (var dimension in MetamorphicBoundaryPolicy.All)
        {
            var boundary = MetamorphicBoundaryPolicy.Derive(source.Source, dimension.Dimension);
            if (!boundary.Found) continue;

            var at = ObserveThrough(dimension.Surface, source.Source,
                MetamorphicBoundaryPolicy.LimitsAt(dimension.Dimension, boundary.Value));
            var below = ObserveThrough(dimension.Surface, source.Source,
                MetamorphicBoundaryPolicy.LimitsAt(dimension.Dimension, boundary.Value - 1));
            var above = ObserveThrough(dimension.Surface, source.Source,
                MetamorphicBoundaryPolicy.LimitsAt(dimension.Dimension, boundary.Value + 1));

            var where = $"'{source.Id}' / {dimension.Id} @ {boundary.Value.ToString(CultureInfo.InvariantCulture)}";
            Assert.Equal("ok", at.Semantic.Outcome);
            Assert.Equal("ok", above.Semantic.Outcome);
            Assert.Equal(at.Semantic.Structure, above.Semantic.Structure);
            Assert.Equal(at.Semantic.EmittedCount, above.Semantic.EmittedCount);

            if (dimension.Stop == MetamorphicBoundaryStop.ResourceError)
            {
                Assert.Equal("err", below.Semantic.Outcome);
                Assert.True(below.Semantic.IsResourceLimit, where);
                Assert.Equal(dimension.ExpectedResourceKind, below.Semantic.ErrorCategory);
            }
            else
            {
                // Display length is a rendering policy: the run still succeeds, but the returned
                // text is bounded and therefore different.
                Assert.Equal("ok", below.Semantic.Outcome);
                Assert.NotEqual(at.Projection?.RenderedText, below.Projection?.RenderedText);
                Assert.True(below.Projection!.RenderedLength <= below.Projection.RenderedLimit, where);
            }

            verified++;
            byDimension[dimension.Id] = byDimension.GetValueOrDefault(dimension.Id) + 1;
        }

        Assert.True(verified > 20, $"expected many verified boundaries, got {verified}.");
        foreach (var dimension in MetamorphicBoundaryPolicy.All)
            Assert.True(byDimension.ContainsKey(dimension.Id), $"no source produced a {dimension.Id} boundary.");
    }

    /// <summary>Monotonic success: once a program fits, every larger tested limit still fits identically.</summary>
    [Fact]
    public void MonotonicSuccess_HoldsForEveryDerivableBoundary()
    {
        foreach (var source in MetamorphicBudgetLawTemplate.Sources)
        foreach (var dimension in MetamorphicBoundaryPolicy.All)
        {
            var boundary = MetamorphicBoundaryPolicy.Derive(source.Source, dimension.Dimension);
            if (!boundary.Found) continue;

            var at = ObserveThrough(dimension.Surface, source.Source,
                MetamorphicBoundaryPolicy.LimitsAt(dimension.Dimension, boundary.Value));

            foreach (var extra in new[] { 0, 1, 4, 32 })
            {
                var larger = ObserveThrough(dimension.Surface, source.Source,
                    MetamorphicBoundaryPolicy.LimitsAt(dimension.Dimension, boundary.Value + extra));

                Assert.Equal(at.Semantic.Outcome, larger.Semantic.Outcome);
                Assert.Equal(at.Semantic.Structure, larger.Semantic.Structure);
                Assert.Equal(at.Semantic.EmittedCount, larger.Semantic.EmittedCount);
            }
        }
    }

    /// <summary>A failed reservation leaves nothing behind: the next independent run matches a control.</summary>
    [Fact]
    public void FailedReservation_LeavesNoTraceInALaterIndependentRun()
    {
        foreach (var source in MetamorphicBudgetLawTemplate.Sources)
        foreach (var dimension in MetamorphicBoundaryPolicy.All)
        {
            var boundary = MetamorphicBoundaryPolicy.Derive(source.Source, dimension.Dimension);
            if (!boundary.Found) continue;

            var generous = MetamorphicBoundaryPolicy.GenerousLimits(dimension.Dimension, boundary.Value);
            var failing = MetamorphicBoundaryPolicy.LimitsAt(dimension.Dimension, boundary.Value - 1);

            var control = ObserveThrough(dimension.Surface, source.Source, generous);
            var failed = ObserveThrough(dimension.Surface, source.Source, failing);
            var after = ObserveThrough(dimension.Surface, source.Source, generous);

            Assert.Equal(control, after);
            if (dimension.Stop == MetamorphicBoundaryStop.ResourceError)
            {
                Assert.Equal("err", failed.Semantic.Outcome);
                // The failing run's own counters stop at the documented prefix: a rejected
                // reservation never moves the cumulative total past the limit it was refused at.
                if (failed.Facets.HasFlag(MetamorphicFacets.OperationalCounters))
                    Assert.True(failed.MaterializedItems <= control.MaterializedItems);
            }
        }
    }

    /// <summary>
    /// In-budget neutrality: a limit comfortably above what a run needs changes neither the result
    /// nor the work nor which optimizer path was taken.
    /// </summary>
    [Fact]
    public void InBudgetNeutrality_ChangesNeitherResultNorWorkNorOptimizerPath()
    {
        foreach (var source in MetamorphicBudgetLawTemplate.Sources)
        foreach (var dimension in MetamorphicBoundaryPolicy.All)
        {
            if (dimension.Surface != MetamorphicSurface.EvaluatorRunCountedObserved) continue;

            var boundary = MetamorphicBoundaryPolicy.Derive(source.Source, dimension.Dimension);
            if (!boundary.Found) continue;

            var baseline = ObserveWithEvidence(source.Source, true, dimension.Baseline);
            var generous = ObserveWithEvidence(
                source.Source, true, MetamorphicBoundaryPolicy.GenerousLimits(dimension.Dimension, boundary.Value));

            var where = $"'{source.Id}' / {dimension.Id}";
            Assert.Equal(baseline.Semantic, generous.Semantic);
            Assert.Equal(baseline.MaterializedItems, generous.MaterializedItems);
            Assert.Equal(baseline.MaterializedStringChars, generous.MaterializedStringChars);
            Assert.Equal(baseline.EvaluationSteps, generous.EvaluationSteps);
            Assert.Equal(baseline.PeakDynamicDepth, generous.PeakDynamicDepth);
            Assert.True(
                baseline.OptimizerEvidence == generous.OptimizerEvidence,
                $"{where}: optimizer path changed from {baseline.OptimizerEvidence} to {generous.OptimizerEvidence}.");
        }
    }

    /// <summary>
    /// Bounded, GENUINELY SIMULTANEOUS isolation: many overlapping runs sharing ONE immutable
    /// limits/options instance produce exactly the sequential control's observation. No timing is
    /// asserted and no completion order is relied on.
    ///
    /// <para>This is the test that carries the simultaneity the fuzzing loop deliberately gave up.
    /// It runs without coverage instrumentation, so overlapping evaluations cost it nothing, and it
    /// covers every risk class the loop's ordered hand-off cannot reach on its own: two evaluations
    /// inside the evaluator at the same instant, reading one shared immutable
    /// <see cref="EvaluationLimits"/> and one shared <see cref="RunOptions"/>.</para>
    /// </summary>
    [Fact]
    public void SimultaneousRuns_MatchTheSequentialControlExactly()
    {
        const int Degree = 8;
        var limits = new EvaluationLimits { MaxMaterializedItems = 10_000, MaxCollectionItems = 10_000 };
        var options = new RunOptions { EvaluationLimits = limits };

        foreach (var source in MetamorphicBudgetLawTemplate.Sources)
        foreach (var surface in new[] { MetamorphicSurface.EvaluatorRunCountedObserved, MetamorphicSurface.EngineRun })
        {
            // ONE profile and ONE options instance, shared by the control and by every worker.
            var profile = new MetamorphicExecutionProfile(surface, limits, EnableOptimizations: true);
            var control = ObserveShared(source.Source, profile, options);
            var results = new MetamorphicOperationalObservation?[Degree];
            var barrier = new Barrier(Degree);

            // The barrier makes the workers overlap on purpose instead of by luck; it is a
            // rendezvous, not a timing assertion, and nothing depends on who leaves it first.
            Parallel.For(0, Degree, new ParallelOptions { MaxDegreeOfParallelism = Degree }, index =>
            {
                barrier.SignalAndWait();
                results[index] = ObserveShared(source.Source, profile, options);
            });

            var where = $"'{source.Id}' through {MetamorphicSurfaces.Get(surface).Id}";
            for (var index = 0; index < Degree; index++)
                Assert.True(control == results[index], $"{where}: worker {index} observed {results[index]}, control {control}.");
        }
    }

    /// <summary>
    /// The same simultaneity check for the two entry points that carry their own top-level
    /// plumbing, in BOTH execution orders, repeated so an A/B/A pattern of overlapping runs is
    /// covered rather than a single burst.
    /// </summary>
    [Fact]
    public void SimultaneousRuns_AreStableAcrossRepeatsAndReversedOrder()
    {
        const int Degree = 6;
        var limits = new EvaluationLimits { MaxMaterializedItems = 10_000, MaxCollectionItems = 10_000 };
        var options = new RunOptions { EvaluationLimits = limits };
        var probe = MetamorphicExecutor.IsolationProbeSource;

        foreach (var surface in new[] { MetamorphicSurface.EvaluatorRunCountedObserved, MetamorphicSurface.EngineRun })
        {
            var profile = new MetamorphicExecutionProfile(surface, limits, EnableOptimizations: true);
            var probeProfile = new MetamorphicExecutionProfile(surface, limits, EnableOptimizations: true);

            foreach (var source in new[] { "Output = range(1, 9).count", "Output = 'abcd', 'ef'" })
            {
                var first = ObserveShared(source, profile, options);

                // A: overlapping runs of the subject. B: overlapping runs of an unrelated program.
                // A again: the subject must be exactly what it was before B ever ran.
                for (var round = 0; round < 3; round++)
                {
                    var forward = round % 2 == 0;
                    var results = new MetamorphicOperationalObservation?[Degree];
                    var barrier = new Barrier(Degree);
                    Parallel.For(0, Degree, new ParallelOptions { MaxDegreeOfParallelism = Degree }, index =>
                    {
                        barrier.SignalAndWait();
                        // Reversed order: half the rounds run the probe before the subject.
                        if (!forward) _ = ObserveShared(probe, probeProfile, options);
                        results[index] = ObserveShared(source, profile, options);
                        if (forward) _ = ObserveShared(probe, probeProfile, options);
                    });

                    for (var index = 0; index < Degree; index++)
                    {
                        Assert.True(
                            first == results[index],
                            $"round {round} (forward={forward}) worker {index}: {results[index]} != {first}");
                    }
                }

                Assert.Equal(first, ObserveShared(source, profile, options));
            }
        }
    }

    /// <summary>
    /// The fuzz loop's own bounded-isolation plan, exercised end to end through the executor: it
    /// uses <see cref="MetamorphicExecutor.ParallelTaskCount"/> DISTINCT threads, every one of them
    /// observes identically, and the case is accepted with no mismatch — in either execution order.
    /// </summary>
    [Fact]
    public void BoundedIsolationPlan_RunsOnDistinctThreadsAndAgreesInBothOrders()
    {
        Assert.True(MetamorphicExecutor.ParallelTaskCount > 1, "a bounded-isolation plan needs more than one thread.");

        var lawIndex = Array.IndexOf(MetamorphicBudgetLawTemplate.Laws.ToArray(), MetamorphicBudgetLaw.RunIsolation);
        var parallelIndex = MetamorphicBudgetLawTemplate.IsolationModes.IndexOf(MetamorphicIsolationMode.BoundedParallel);
        var executed = 0;

        for (var sourceIndex = 0; sourceIndex < MetamorphicBudgetLawTemplate.SourceCount; sourceIndex++)
        for (var dimensionIndex = 0; dimensionIndex < MetamorphicBoundaryPolicy.All.Length; dimensionIndex++)
        {
            var testCase = BuildOf(
                MetamorphicFamily.BudgetLaw, 0, 1, 1, 0, sourceIndex, lawIndex, dimensionIndex, parallelIndex);
            if (!testCase.Precondition.Satisfied) continue;

            Assert.Equal(MetamorphicRunPlan.BoundedParallel, testCase.RunPlan);

            foreach (var order in new[] { MetamorphicExecutionOrder.LeftFirst, MetamorphicExecutionOrder.RightFirst })
            {
                var execution = MetamorphicExecutor.Execute(testCase with { ExecutionOrder = order });
                if (!execution.Accepted) continue;

                var mismatch = MetamorphicComparator.Compare(execution.Case, execution.Left!, execution.Right!);
                Assert.True(
                    mismatch is null,
                    $"source {sourceIndex}, dimension {MetamorphicBoundaryPolicy.All[dimensionIndex].Id}, " +
                    $"order {order}: {mismatch?.Headline}");
                executed++;
            }
        }

        Assert.True(executed > 20, $"expected many executed isolation plans, got {executed}.");
    }

    /// <summary>
    /// The bounded-isolation plan really does put each observation on a DIFFERENT thread. Proved
    /// by construction rather than by timing: the executor starts one dedicated thread per index,
    /// so a run-scoped value that was thread-affine could not survive the hand-off.
    /// </summary>
    [Fact]
    public void BoundedIsolationPlan_ObservesFromDistinctThreads()
    {
        var seen = new System.Collections.Concurrent.ConcurrentBag<int>();
        var limits = new EvaluationLimits { MaxMaterializedItems = 10_000 };
        var profile = new MetamorphicExecutionProfile(
            MetamorphicSurface.EvaluatorRunCountedObserved, limits, EnableOptimizations: true);
        var options = MetamorphicExecutor.OptionsFor(profile);

        var lawIndex = Array.IndexOf(MetamorphicBudgetLawTemplate.Laws.ToArray(), MetamorphicBudgetLaw.RunIsolation);
        var parallelIndex = MetamorphicBudgetLawTemplate.IsolationModes.IndexOf(MetamorphicIsolationMode.BoundedParallel);

        // Not every (source, dimension) pair yields a derivable boundary — a source that never
        // recurses has no depth boundary — so take the first pair the family actually admits.
        var testCase = (
            from sourceIndex in Enumerable.Range(0, MetamorphicBudgetLawTemplate.SourceCount)
            from dimensionIndex in Enumerable.Range(0, MetamorphicBoundaryPolicy.All.Length)
            let candidate = BuildOf(
                MetamorphicFamily.BudgetLaw, 0, 1, 1, 0, sourceIndex, lawIndex, dimensionIndex, parallelIndex)
            where candidate.Precondition.Satisfied
            select candidate).First();

        Assert.Equal(MetamorphicRunPlan.BoundedParallel, testCase.RunPlan);
        Assert.Equal("threads-4-ordered", MetamorphicExecutor.DescribeRunPlan(testCase));

        // The executor's own thread naming is the observable: one dedicated, uniquely named thread
        // per index. Reproduce the shape here so the claim is checked rather than assumed.
        var threads = new Thread[MetamorphicExecutor.ParallelTaskCount];
        for (var i = 0; i < threads.Length; i++)
        {
            threads[i] = new Thread(() =>
            {
                seen.Add(Environment.CurrentManagedThreadId);
                Assert.True(
                    MetamorphicSurfaces.TryObserve(
                        testCase.RightSource, profile, options, false, out _, out var reason),
                    reason);
            })
            { IsBackground = true };
        }

        foreach (var thread in threads) thread.Start();
        foreach (var thread in threads) thread.Join();

        Assert.Equal(MetamorphicExecutor.ParallelTaskCount, seen.Distinct().Count());
    }

    /// <summary>
    /// Cache, budget-counter and optimizer-diagnostic isolation, checked from overlapping threads:
    /// a run-scoped cache, a run-scoped budget and a run-scoped diagnostics channel must each be
    /// created per run, so every worker sees the SAME profile as a lone sequential control.
    /// </summary>
    [Fact]
    public void RunScopedCacheBudgetAndDiagnostics_AreNotSharedBetweenOverlappingRuns()
    {
        const int Degree = 8;
        var limits = new EvaluationLimits { MaxMaterializedItems = 10_000, MaxCollectionItems = 10_000 };

        // One source per contamination channel: a reused property (cache), a loop (optimizer
        // diagnostics), and a string builder (the string budget counters).
        var sources = new[]
        {
            $"{MetamorphicTables.ReceiverProperty} = range(1, 8)\n" +
            $"Output = {MetamorphicTables.ReceiverProperty}.count, {MetamorphicTables.ReceiverProperty}.sum",
            $"{MetamorphicTables.ReceiverProperty}Step = x + 1\nOutput = {MetamorphicTables.ReceiverProperty}Step.repeat(6, 0)",
            "Output = 'abcd', 'ef', 'ghij'",
        };

        foreach (var source in sources)
        {
            var control = ObserveWithEvidence(source, true, limits);
            Assert.NotNull(control.CacheEvidence);
            Assert.NotNull(control.OptimizerEvidence);

            var results = new MetamorphicOperationalObservation?[Degree];
            var barrier = new Barrier(Degree);
            Parallel.For(0, Degree, new ParallelOptions { MaxDegreeOfParallelism = Degree }, index =>
            {
                barrier.SignalAndWait();
                results[index] = ObserveWithEvidence(source, true, limits);
            });

            for (var index = 0; index < Degree; index++)
            {
                var worker = results[index]!;
                Assert.Equal(control.CacheEvidence, worker.CacheEvidence);
                Assert.Equal(control.OptimizerEvidence, worker.OptimizerEvidence);
                Assert.Equal(control.EvaluationSteps, worker.EvaluationSteps);
                Assert.Equal(control.MaterializedItems, worker.MaterializedItems);
                Assert.Equal(control.MaterializedStringChars, worker.MaterializedStringChars);
                Assert.Equal(control.PeakDynamicDepth, worker.PeakDynamicDepth);
            }
        }
    }

    /// <summary>
    /// A run that FAILS its reservation, executed simultaneously with runs that succeed, must not
    /// contaminate them — the structured-failure half of the isolation law.
    /// </summary>
    [Fact]
    public void SimultaneousFailingAndSucceedingRuns_DoNotContaminateEachOther()
    {
        const int Degree = 8;
        const string Source = "Output = range(1, 12).count";
        var generous = new EvaluationLimits { MaxMaterializedItems = 10_000 };
        var failing = new EvaluationLimits { MaxMaterializedItems = 1 };

        var okControl = Observe(Source, generous, enableOptimizations: true);
        var failControl = Observe(Source, failing, enableOptimizations: true);
        Assert.Equal("ok", okControl.Semantic.Outcome);
        Assert.Equal("err", failControl.Semantic.Outcome);
        Assert.True(failControl.Semantic.IsResourceLimit);

        var results = new MetamorphicOperationalObservation?[Degree];
        var barrier = new Barrier(Degree);
        Parallel.For(0, Degree, new ParallelOptions { MaxDegreeOfParallelism = Degree }, index =>
        {
            barrier.SignalAndWait();
            // Alternating workers reserve far more than they may, while the others succeed.
            results[index] = Observe(Source, index % 2 == 0 ? generous : failing, enableOptimizations: true);
        });

        for (var index = 0; index < Degree; index++)
            Assert.Equal(index % 2 == 0 ? okControl : failControl, results[index]);
    }

    private static MetamorphicOperationalObservation ObserveShared(
        string source, MetamorphicExecutionProfile profile, RunOptions options)
    {
        Assert.True(
            MetamorphicSurfaces.TryObserve(source, profile, options, false, out var observation, out var reason),
            reason);
        return observation;
    }

    /// <summary>
    /// The bounded boundary search is deterministic and stays inside its probe budget, and what it
    /// finds is the same value on every repetition.
    /// </summary>
    [Fact]
    public void BoundedBoundarySearch_IsDeterministicAndBounded()
    {
        foreach (var source in MetamorphicBudgetLawTemplate.BoundaryTemplates)
        foreach (var dimension in MetamorphicBoundaryPolicy.SearchedDimensions)
        {
            var first = MetamorphicBoundaryPolicy.Derive(source.Source, dimension.Dimension);
            var second = MetamorphicBoundaryPolicy.Derive(source.Source, dimension.Dimension);

            Assert.Equal(first, second);
            Assert.InRange(first.Probes, 0, MetamorphicBoundaryPolicy.MaxSearchProbes);
            if (first.Found) Assert.InRange(first.Value, dimension.MinimumLegalLimit, dimension.SearchCeiling);
        }
    }

    /// <summary>
    /// Every dimension whose boundary comes from a bounded SEARCH declares an explicit finite
    /// interval, and the two ends of that interval are the only thing the search may probe.
    /// </summary>
    [Fact]
    public void SearchedDimensions_DeclareAnExplicitBoundedInterval()
    {
        var searched = MetamorphicBoundaryPolicy.SearchedDimensions.ToList();
        Assert.NotEmpty(searched);

        foreach (var dimension in searched)
        {
            var interval = MetamorphicBoundaryPolicy.IntervalOf(dimension.Dimension);
            Assert.Equal(dimension.Id, interval.Id);
            Assert.Equal(dimension.MinimumLegalLimit, interval.Low);
            Assert.Equal(dimension.SearchCeiling, interval.High);
            Assert.True(interval.Count > 1, $"{interval}: a searched interval needs more than one value.");
            // A bisection over the interval must fit in the probe budget, or the bound is a lie.
            var doublings = (int)Math.Ceiling(Math.Log2(interval.High + 1.0));
            Assert.True(
                (2 * doublings) + 2 <= MetamorphicBoundaryPolicy.MaxSearchProbes,
                $"{interval}: needs up to {(2 * doublings) + 2} probes but the budget is " +
                $"{MetamorphicBoundaryPolicy.MaxSearchProbes}.");
        }
    }

    /// <summary>
    /// <b>The monotonicity law, proved over the COMPLETE bounded interval rather than sampled.</b>
    ///
    /// <para>For a fixed source, a fixed execution surface, a fixed optimizer policy and ONE
    /// resource dimension, every limit value the search could ever probe is executed. Once the
    /// program fits at some limit <c>L</c>, every larger limit in the interval must also fit, must
    /// produce the same neutral structural value and the same emitted count, and must not turn into
    /// some different non-resource failure. Below the first success only the dimension's own
    /// structured resource error is allowed — a different failure there would mean the search had
    /// been measuring something other than the resource it names.</para>
    ///
    /// <para>The sweep calls the search's OWN predicate
    /// (<see cref="MetamorphicBoundaryPolicy.SucceedsAt"/>) and its own observation entry point, so
    /// the law cannot be proved about a different notion of "fits" than the search uses. Optimizer
    /// policies are validated separately and never mixed: an optimizer that validly avoids
    /// materializing is allowed to move the boundary, but within one policy the law is absolute.</para>
    /// </summary>
    [Fact]
    public void SearchedBoundaries_AreMonotoneAcrossTheirCompleteInterval()
    {
        var units = (
            from template in MetamorphicBudgetLawTemplate.BoundaryTemplates
            from dimension in MetamorphicBoundaryPolicy.SearchedDimensions
            from optimize in new[] { true, false }
            select (template, dimension, optimize)).ToList();

        var failures = new string?[units.Count];
        var sweeps = new (long First, long Count)[units.Count];

        // The sweep is pure and shares no state, so it may run concurrently; results are collected
        // BY INDEX and asserted in order, so the outcome never depends on completion order.
        Parallel.For(0, units.Count, index =>
        {
            var (template, dimension, optimize) = units[index];
            failures[index] = SweepCompleteInterval(template, dimension, optimize, out var first, out var count);
            sweeps[index] = (first, count);
        });

        var withTransition = 0;
        long executed = 0;
        for (var index = 0; index < units.Count; index++)
        {
            var (template, dimension, optimize) = units[index];
            var where =
                $"[{MetamorphicCase.FamilyIdOf(MetamorphicFamily.BudgetLaw)}] template '{template.Id}', " +
                $"dimension '{dimension.Id}', optimizer={(optimize ? "on" : "off")}";
            Assert.True(failures[index] is null, $"{where}: {failures[index]}");

            // The sweep is only worth anything if it really visited every value: everything from
            // the first success to the ceiling must have succeeded, and everything below it failed.
            var interval = MetamorphicBoundaryPolicy.IntervalOf(dimension.Dimension);
            var (first, successes) = sweeps[index];
            Assert.True(
                successes == interval.High - first + 1,
                $"{where}: swept {successes} successes but {interval} has {interval.High - first + 1} at or above {first}.");

            executed += interval.Count;
            if (first > interval.Low) withTransition++;
        }

        // A sweep that never observed a failure-to-success transition would prove nothing, so at
        // least some registered template must genuinely cross its boundary inside the interval.
        Assert.True(withTransition > 0, "no searched template crossed its boundary inside the interval.");
        Assert.True(executed > 100_000, $"the exhaustive sweep executed only {executed} limit values.");
    }

    /// <summary>
    /// Executes EVERY limit value of one dimension's complete bounded interval for one template
    /// under one optimizer policy, and returns the first failed obligation, or <c>null</c>.
    /// </summary>
    private static string? SweepCompleteInterval(
        MetamorphicBudgetSource template,
        MetamorphicResourceDimensionDefinition dimension,
        bool optimize,
        out long firstSuccess,
        out long successCount)
    {
        var interval = MetamorphicBoundaryPolicy.IntervalOf(dimension.Dimension);
        firstSuccess = long.MaxValue;
        successCount = 0;

        MetamorphicSemanticObservation? reference = null;
        for (var value = interval.Low; value <= interval.High; value++)
        {
            if (!MetamorphicBoundaryPolicy.TryObserveAt(
                    template.Source, dimension, value, out var observation, optimize))
            {
                return $"limit {Text(value)} could not be observed at all.";
            }

            var semantic = observation.Semantic;
            var succeeded = semantic.Outcome == "ok";

            // 3. no later limit may fail once one has succeeded.
            if (!succeeded && reference is not null)
            {
                return $"succeeded at {Text(firstSuccess)} but FAILED again at {Text(value)} " +
                       $"({semantic.ErrorCategory ?? "unknown"}); monotonicity is violated over {interval}.";
            }

            if (!succeeded)
            {
                // Below the first success only this dimension's OWN structured resource error is
                // allowed; anything else means the sweep is not measuring what it claims.
                if (!semantic.IsResourceLimit || semantic.ErrorCategory != dimension.ExpectedResourceKind)
                {
                    return $"limit {Text(value)} failed with '{semantic.ErrorCategory ?? "unknown"}' " +
                           $"(resourceLimit={semantic.IsResourceLimit}) instead of {dimension.ExpectedResourceKind}.";
                }

                continue;
            }

            // 4. every successful result carries the same neutral semantic observation.
            if (reference is null)
            {
                reference = semantic;
                firstSuccess = value;
            }
            else if (semantic != reference)
            {
                return $"succeeded at {Text(firstSuccess)} with [{reference}] but at {Text(value)} " +
                       $"produced [{semantic}]; the semantic result changed with a non-binding limit.";
            }

            successCount++;
        }

        if (reference is null) return $"no limit in {interval} succeeded, so there is no boundary to validate.";

        // 5. the search helper's boundary IS the first successful limit — but only for the policy
        // the helper itself runs under. Derive never varies the optimizer policy.
        if (optimize)
        {
            var derived = MetamorphicBoundaryPolicy.Derive(template.Source, dimension.Dimension);
            var reported = derived.Found ? derived.Value : firstSuccess;
            if (reported != firstSuccess)
            {
                return $"the bounded search reported {Text(reported)} but the first successful limit is " +
                       $"{Text(firstSuccess)} (stop={derived.Stop}, probes={derived.Probes}).";
            }

            // A first success ON the lower bound has no failing neighbour, and the helper must say
            // so rather than handing a boundary law a case it cannot express. Conversely, a helper
            // that declares no usable boundary anywhere else contradicts what the sweep just saw.
            var onLowerBound = firstSuccess <= interval.Low;
            if (onLowerBound && derived.Found)
                return $"the lower bound {Text(interval.Low)} already succeeds but the search still reported a usable boundary.";
            if (onLowerBound && derived.Stop != MetamorphicBoundaryStopReason.LowerBoundAlreadySucceeds)
                return $"the lower bound already succeeds but the search classified the stop as {derived.Stop}.";
            if (!onLowerBound && !derived.Found)
            {
                return $"the sweep found a usable boundary at {Text(firstSuccess)} but the search reported " +
                       $"none (stop={derived.Stop}, reason={derived.Reason}).";
            }

            if (derived.Probes > MetamorphicBoundaryPolicy.MaxSearchProbes)
                return $"the search used {derived.Probes} probes, over its budget of {MetamorphicBoundaryPolicy.MaxSearchProbes}.";
        }

        // 6/7/8. one below fails with the expected kind where such a value exists, the boundary
        // itself succeeds, and the interval's largest value still succeeds.
        if (firstSuccess > interval.Low)
        {
            if (MetamorphicBoundaryPolicy.SucceedsAt(template.Source, dimension, firstSuccess - 1, optimize))
                return $"limit {Text(firstSuccess - 1)} was expected to fail but succeeded.";
        }

        if (!MetamorphicBoundaryPolicy.SucceedsAt(template.Source, dimension, firstSuccess, optimize))
            return $"the boundary {Text(firstSuccess)} did not succeed on re-execution.";
        if (!MetamorphicBoundaryPolicy.SucceedsAt(template.Source, dimension, interval.High, optimize))
            return $"the interval's maximum {Text(interval.High)} did not succeed.";

        return null;

        static string Text(long value) => value.ToString(CultureInfo.InvariantCulture);
    }

    /// <summary>
    /// The equivalent-form boundary law is only applied where the declared operational relation is
    /// exact: a pair whose two spellings legitimately differ in invocation accounting may not
    /// claim a shared work boundary.
    /// </summary>
    [Fact]
    public void EquivalentFormLaw_ExcludesWorkDimensionsForNonExactPairs()
    {
        var lawIndex = Array.IndexOf(
            MetamorphicBudgetLawTemplate.Laws.ToArray(), MetamorphicBudgetLaw.EquivalentFormBoundaryParity);

        for (var formIndex = 0; formIndex < MetamorphicBudgetLawTemplate.FormCount; formIndex++)
        for (var dimensionIndex = 0; dimensionIndex < MetamorphicBoundaryPolicy.All.Length; dimensionIndex++)
        {
            var testCase = BuildOf(
                MetamorphicFamily.BudgetLaw, 0, 1, 1, 0, formIndex, lawIndex, dimensionIndex, 0);
            var forms = MetamorphicBudgetLawTemplate.Forms[formIndex];
            var dimension = MetamorphicBoundaryPolicy.All[dimensionIndex];
            var isWork = dimension.Dimension
                is MetamorphicResourceDimension.Depth or MetamorphicResourceDimension.Steps;

            if (isWork && !forms.SharesWorkBoundary)
            {
                Assert.False(testCase.Precondition.Satisfied);
                Assert.Equal("equivalent-forms-do-not-share-a-work-boundary", testCase.Precondition.Reason);
            }
        }
    }

    /// <summary>One limit at a time: no budget-law case ever configures two dimensions at once.</summary>
    [Fact]
    public void BudgetLawCases_VaryExactlyOneResourceDimension()
    {
        foreach (var parameters in OfFamily(MetamorphicFamily.BudgetLaw))
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            if (!testCase.Precondition.Satisfied) continue;

            foreach (var limits in new[] { testCase.LeftProfile.Limits, testCase.RightProfile.Limits })
            {
                if (limits is null) continue;
                var configured = ConfiguredDimensionCount(limits);
                Assert.True(configured <= 1, $"{parameters}: {configured} dimensions configured at once.");
            }
        }
    }

    private static int ConfiguredDimensionCount(EvaluationLimits limits)
    {
        var count = 0;
        if (limits.MaxDepth is not null) count++;
        if (limits.MaxSteps is not null) count++;
        if (limits.MaxCollectionItems is not null) count++;
        if (limits.MaxMaterializedItems is not null) count++;
        if (limits.MaxStringLength is not null) count++;
        if (limits.MaxMaterializedStringChars is not null) count++;
        if (limits.MaxDisplayLength is not null) count++;
        return count;
    }

    // ── Isolation fingerprints: what they must and must not distinguish ──────

    /// <summary>
    /// Isolation payloads and their fingerprints, used by the tests below. Each entry is
    /// (label, payload) for one bounded-isolation case built straight from decoded bytes, so the
    /// fingerprints are exactly what a campaign would record.
    /// </summary>
    private static string IsolationFingerprint(byte source, byte dimension, byte isolation, byte order = 0)
    {
        var lawIndex = Array.IndexOf(MetamorphicBudgetLawTemplate.Laws.ToArray(), MetamorphicBudgetLaw.RunIsolation);
        var payload = new byte[MetamorphicParameters.CommonPayloadLength + 4];
        payload[0] = FamilyByte(MetamorphicFamily.BudgetLaw);
        payload[3] = order;
        payload[MetamorphicParameters.CommonPayloadLength] = source;
        payload[MetamorphicParameters.CommonPayloadLength + 1] = (byte)lawIndex;
        payload[MetamorphicParameters.CommonPayloadLength + 2] = dimension;
        payload[MetamorphicParameters.CommonPayloadLength + 3] = isolation;
        return MetamorphicInvariants.Run(payload).Fingerprint;
    }

    private static byte SequentialIsolationByte =>
        (byte)MetamorphicBudgetLawTemplate.IsolationModes.IndexOf(MetamorphicIsolationMode.Sequential);

    private static byte ParallelIsolationByte =>
        (byte)MetamorphicBudgetLawTemplate.IsolationModes.IndexOf(MetamorphicIsolationMode.BoundedParallel);

    /// <summary>
    /// The first resource dimension running through <paramref name="surface"/> whose isolation case
    /// for <paramref name="source"/> is actually ADMITTED — a source that never recurses has no
    /// depth boundary, and a rejected case would compare rejection reasons, not isolation.
    /// </summary>
    private static byte AdmittedIsolationDimension(byte source, MetamorphicSurface surface)
    {
        var lawIndex = Array.IndexOf(MetamorphicBudgetLawTemplate.Laws.ToArray(), MetamorphicBudgetLaw.RunIsolation);
        for (var index = 0; index < MetamorphicBoundaryPolicy.All.Length; index++)
        {
            if (MetamorphicBoundaryPolicy.All[index].Surface != surface) continue;
            var testCase = BuildOf(
                MetamorphicFamily.BudgetLaw, 0, 1, 1, 0, source, lawIndex, index, ParallelIsolationByte);
            if (testCase.Precondition.Satisfied) return (byte)index;
        }

        throw new InvalidOperationException($"no admitted isolation dimension for source {source} on {surface}.");
    }

    /// <summary>
    /// Repeating a bounded-isolation execution produces the SAME fingerprint every time, including
    /// when the repetitions themselves overlap on different threads. This is the property that
    /// makes an isolation corpus unit mean something: a fingerprint that drifted with the schedule
    /// would make every replay a coin flip.
    /// </summary>
    [Fact]
    public void IsolationFingerprints_AreIdenticalOnEveryRepetitionAndFromEveryThread()
    {
        foreach (var isolation in new[] { SequentialIsolationByte, ParallelIsolationByte })
        {
            var expected = IsolationFingerprint(source: 0, dimension: 3, isolation);

            for (var repeat = 0; repeat < 4; repeat++)
                Assert.Equal(expected, IsolationFingerprint(source: 0, dimension: 3, isolation));

            // Same case, computed from several threads at once. Nothing about WHERE it ran may
            // reach the fingerprint.
            var fromThreads = new string[6];
            var barrier = new Barrier(fromThreads.Length);
            Parallel.For(0, fromThreads.Length, index =>
            {
                barrier.SignalAndWait();
                fromThreads[index] = IsolationFingerprint(source: 0, dimension: 3, isolation);
            });

            foreach (var fingerprint in fromThreads) Assert.Equal(expected, fingerprint);
        }
    }

    /// <summary>
    /// The isolation fingerprint carries no scheduling-dependent data: no thread or process id, no
    /// task index, no completion order, no timing, no hash code. Checked positively — the current
    /// thread's own id must not appear — as well as by name.
    /// </summary>
    [Fact]
    public void IsolationFingerprints_ContainNoSchedulingDependentData()
    {
        var fingerprint = IsolationFingerprint(source: 0, dimension: 3, ParallelIsolationByte);

        // The word "thread" legitimately appears in the run-plan LABEL, which describes the plan
        // rather than any particular thread. What may never appear is an identity or a duration.
        foreach (var forbidden in new[]
                 {
                     "threadId", "ThreadId", "managedThread", "processId", "ProcessId",
                     "completion", "schedule", "elapsed", "Elapsed", "Ticks", "HashCode", "@0",
                 })
        {
            Assert.DoesNotContain(forbidden, fingerprint, StringComparison.Ordinal);
        }

        Assert.DoesNotContain(
            "=" + Environment.CurrentManagedThreadId.ToString(CultureInfo.InvariantCulture) + "|",
            fingerprint,
            StringComparison.Ordinal);
        Assert.DoesNotContain(
            "=" + Environment.ProcessId.ToString(CultureInfo.InvariantCulture) + "|",
            fingerprint,
            StringComparison.Ordinal);

        // The run plan is named for what it does, and the name is part of the recorded shape.
        Assert.Contains("runPlan=threads-4-ordered", fingerprint, StringComparison.Ordinal);
    }

    /// <summary>
    /// Materially distinct isolation risk classes stay distinguishable: the sequential and
    /// multi-threaded plans, the two execution orders, the two entry-point classes, and the
    /// different run-scoped state a source exercises must never share a fingerprint.
    /// </summary>
    [Fact]
    public void IsolationFingerprints_DistinguishEveryMateriallyDistinctRiskClass()
    {
        // The display-length dimension is the one that runs through the ENGINE surface; every
        // other dimension runs through the observed evaluator. That is the entry-point class split.
        // Both must be dimensions source 0 actually exercises, or the case is rejected and the
        // comparison would be about rejection reasons rather than about isolation.
        var engineDimension = AdmittedIsolationDimension(source: 0, MetamorphicSurface.EngineRun);
        var evaluatorDimension = AdmittedIsolationDimension(source: 0, MetamorphicSurface.EvaluatorRunCountedObserved);

        var distinct = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["sequential"] = IsolationFingerprint(0, evaluatorDimension, SequentialIsolationByte),
            ["threaded"] = IsolationFingerprint(0, evaluatorDimension, ParallelIsolationByte),
            ["threaded/engine-surface"] = IsolationFingerprint(0, engineDimension, ParallelIsolationByte),
            ["threaded/other-source"] = IsolationFingerprint(2, evaluatorDimension, ParallelIsolationByte),
            ["sequential/engine-surface"] = IsolationFingerprint(0, engineDimension, SequentialIsolationByte),
        };

        var seen = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var (label, fingerprint) in distinct)
        {
            Assert.False(
                seen.TryGetValue(fingerprint, out var clash),
                $"'{label}' and '{clash}' share a fingerprint but are different isolation risk classes.");
            seen[fingerprint] = label;
        }

        // The two isolation modes must differ in the RUN-PLAN feature specifically, not by accident
        // of some other dimension: the sequential mode interposes unrelated runs, the other hands
        // the evaluator between threads.
        Assert.Contains("runPlan=after-3-interleaved-runs", distinct["sequential"], StringComparison.Ordinal);
        Assert.Contains("runPlan=threads-4-ordered", distinct["threaded"], StringComparison.Ordinal);
    }

    /// <summary>
    /// Success, structured resource failure, and an isolation VIOLATION are three different
    /// outcomes and may never collide in the fingerprint — otherwise a campaign summary could not
    /// tell a clean isolation run from a leaking one.
    /// </summary>
    [Fact]
    public void IsolationFingerprints_SeparateSuccessFailureAndContamination()
    {
        var lawIndex = Array.IndexOf(MetamorphicBudgetLawTemplate.Laws.ToArray(), MetamorphicBudgetLaw.RunIsolation);
        var parallelIndex = MetamorphicBudgetLawTemplate.IsolationModes.IndexOf(MetamorphicIsolationMode.BoundedParallel);
        var testCase = (
            from sourceIndex in Enumerable.Range(0, MetamorphicBudgetLawTemplate.SourceCount)
            from dimensionIndex in Enumerable.Range(0, MetamorphicBoundaryPolicy.All.Length)
            let candidate = BuildOf(
                MetamorphicFamily.BudgetLaw, 0, 1, 1, 0, sourceIndex, lawIndex, dimensionIndex, parallelIndex)
            where candidate.Precondition.Satisfied
            select candidate).First();

        var execution = MetamorphicExecutor.Execute(testCase);
        Assert.True(execution.Accepted, execution.RejectionReason);
        var clean = execution.Left!;

        var fingerprints = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["clean"] = MetamorphicFingerprint.Describe(execution, null),
        };

        // Three DIFFERENT contamination kinds, each of which a leaking run could plausibly show.
        var contaminations = new (string Label, MetamorphicOperationalObservation Right)[]
        {
            ("semantic", clean with { Semantic = clean.Semantic with { EmittedCount = 99 } }),
            ("counters", clean with { MaterializedItems = clean.MaterializedItems + 7 }),
            ("cache", clean with
            {
                CacheEvidence = (clean.CacheEvidence ?? MetamorphicCacheEvidence.Unobserved) with { Hits = 42 },
            }),
            ("optimizer", clean with
            {
                OptimizerEvidence = (clean.OptimizerEvidence ?? MetamorphicOptimizerEvidence.Unobserved) with
                {
                    Paths = MetamorphicOptimizerPath.FusedPipelineExecuted,
                },
            }),
        };

        foreach (var (label, right) in contaminations)
        {
            var broken = execution with { Right = right };
            var mismatch = MetamorphicComparator.Compare(testCase, clean, right);
            Assert.True(mismatch is not null, $"contamination '{label}' was not detected at all.");
            Assert.Equal(MetamorphicMismatchClass.StateIsolation, mismatch!.Class);
            fingerprints[label] = MetamorphicFingerprint.Describe(broken, mismatch);
        }

        var seen = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var (label, fingerprint) in fingerprints)
        {
            Assert.False(
                seen.TryGetValue(fingerprint, out var clash),
                $"contamination '{label}' shares a fingerprint with '{clash}'.");
            seen[fingerprint] = label;
        }
    }

    /// <summary>
    /// <b>Why no dimension was normalized away and no family was re-weighted.</b>
    ///
    /// <para>Both corrections target the size of the isolation law's CASE space, and the measured
    /// case space is already tiny: the whole bounded-isolation law expresses only a few dozen
    /// distinct fingerprints. A campaign that stored two thousand corpus units for it was therefore
    /// not storing distinct cases, and shrinking the case space further could not have helped.
    /// This test pins that fact so the reasoning stays checkable.</para>
    /// </summary>
    [Fact]
    public void BoundedIsolationLaw_ExpressesOnlyASmallCaseSpace()
    {
        var fingerprints = new HashSet<string>(StringComparer.Ordinal);

        for (var sourceIndex = 0; sourceIndex < MetamorphicBudgetLawTemplate.SourceCount; sourceIndex++)
        for (var dimensionIndex = 0; dimensionIndex < MetamorphicBoundaryPolicy.All.Length; dimensionIndex++)
        foreach (var order in new byte[] { 0, 1 })
            fingerprints.Add(IsolationFingerprint((byte)sourceIndex, (byte)dimensionIndex, ParallelIsolationByte, order));

        Assert.True(fingerprints.Count > 1, "the isolation law must express more than one case.");
        Assert.True(
            fingerprints.Count <= 200,
            $"the bounded-isolation law expresses {fingerprints.Count} distinct cases; the refinement " +
            "argument assumes this space is small compared with the corpus it used to occupy.");
    }

    // ── Comparator: every Phase 3 mismatch class is reachable and classified ──

    /// <summary>
    /// Deliberately broken pairs must produce the intended mismatch classification. A comparator
    /// that silently accepts a wrong relation would make every green campaign meaningless.
    /// </summary>
    [Fact]
    public void Comparator_ClassifiesEveryDeliberatelyBrokenPhase3Relation()
    {
        var optimizerCase = BuildOf(MetamorphicFamily.OptimizerGenericParity, 0, 1, 1, 0, 12, 0);
        var left = Observe(optimizerCase.LeftSource, null, true);
        var right = Observe(optimizerCase.RightSource, null, false);

        // 1. Optimizer semantic mismatch.
        Assert.Equal(
            MetamorphicMismatchKind.SemanticStructure,
            Require(MetamorphicComparator.Compare(
                optimizerCase,
                left with { Semantic = left.Semantic with { Structure = "S[9]" } },
                right)).Kind);

        // 2. Wrong directional materialization: the optimized side charging MORE.
        var overcharging = left with { MaterializedItems = right.MaterializedItems + 1 };
        var directional = Require(MetamorphicComparator.Compare(optimizerCase, overcharging, right));
        Assert.Equal(MetamorphicMismatchKind.MaterializedItems, directional.Kind);
        Assert.Equal(MetamorphicMismatchClass.Operational, directional.Class);

        // 3. Cache relation inversion: the cached side charging more steps than the rebuilt one.
        var cacheCase = BuildOf(MetamorphicFamily.CachedPropertyReuse, 0, 1, 1, 0, 10, 1, 0);
        var cached = Observe(cacheCase.LeftSource, null, true);
        var rebuilt = Observe(cacheCase.RightSource, null, true);
        var inverted = Require(MetamorphicComparator.Compare(
            cacheCase, cached with { EvaluationSteps = rebuilt.EvaluationSteps + 1 }, rebuilt));
        Assert.Equal(MetamorphicMismatchKind.EvaluationSteps, inverted.Kind);

        // 4. Entry-point semantic mismatch on a SHARED facet.
        var entryCase = BuildOf(MetamorphicFamily.EntryPointParity, 0, 1, 1, 0, 0, 0, 0);
        var entryLeft = ObserveThrough(MetamorphicSurface.EvaluatorRunCountedObserved, entryCase.LeftSource);
        var entryRight = ObserveThrough(MetamorphicSurface.EvaluatorRunCounted, entryCase.RightSource);
        Assert.Equal(
            MetamorphicMismatchKind.EmittedCount,
            Require(MetamorphicComparator.Compare(
                entryCase, entryLeft, entryRight with { Semantic = entryRight.Semantic with { EmittedCount = 99 } })).Kind);

        // 5. Rendered-text mismatch between two surfaces with the SAME projection.
        var renderCase = entryCase with
        {
            SemanticRelation = MetamorphicSemanticRelation.SameStructuredOutcome,
            OperationalRelation = MetamorphicOperationalRelation.NotCompared,
        };
        var renderLeft = ObserveThrough(MetamorphicSurface.EngineRun, "Output = 1, 2, 3");
        var renderRight = renderLeft with
        {
            Projection = renderLeft.Projection! with { RenderedText = "different" },
        };
        var rendering = Require(MetamorphicComparator.Compare(renderCase, renderLeft, renderRight));
        Assert.Equal(MetamorphicMismatchKind.RenderedText, rendering.Kind);
        Assert.Equal(MetamorphicMismatchClass.Rendering, rendering.Class);

        // 6. A rendering surface returning more units than its limit.
        var overLong = renderLeft with
        {
            Projection = renderLeft.Projection! with { RenderedLimit = 1 },
        };
        var bound = Require(MetamorphicComparator.Compare(renderCase, overLong, renderRight));
        Assert.Equal(MetamorphicMismatchKind.RenderedLength, bound.Kind);
        Assert.Equal(MetamorphicMismatchClass.Rendering, bound.Class);
    }

    /// <summary>The boundary and isolation laws are classified as such, not as ordinary semantics.</summary>
    [Fact]
    public void Comparator_ClassifiesBoundaryMonotonicityAndIsolationViolations()
    {
        var testCase = BuildOf(MetamorphicFamily.OptimizerGenericParity, 0, 1, 1, 0, 12, 0);
        var ok = Observe(testCase.LeftSource, null, true);
        var failed = Observe("Output = range(1, 200000).count", null, true);

        // Monotonicity: a larger limit turning success into failure.
        var monotonic = testCase with
        {
            SemanticRelation = MetamorphicSemanticRelation.MonotonicSuccess,
            OperationalRelation = MetamorphicOperationalRelation.NotCompared,
        };
        var regression = Require(MetamorphicComparator.Compare(monotonic, ok, failed));
        Assert.Equal(MetamorphicMismatchKind.MonotonicRegression, regression.Kind);
        Assert.Equal(MetamorphicMismatchClass.ResourceBoundary, regression.Class);

        // Boundary: one below the boundary NOT stopping.
        var boundary = testCase with
        {
            SemanticRelation = MetamorphicSemanticRelation.SameResourceBoundary,
            OperationalRelation = MetamorphicOperationalRelation.NotCompared,
            BoundaryStop = MetamorphicBoundaryStop.ResourceError,
            ExpectedResourceKind = "MaterializationLimitExceeded",
        };
        var stop = Require(MetamorphicComparator.Compare(boundary, ok, ok));
        Assert.Equal(MetamorphicMismatchKind.BoundaryStopKind, stop.Kind);

        // Boundary: the AT-boundary member failing.
        var atBoundary = Require(MetamorphicComparator.Compare(boundary, failed, failed));
        Assert.Equal(MetamorphicMismatchKind.BoundarySuccess, atBoundary.Kind);

        // Isolation: two independent runs differing at all.
        var isolation = testCase with
        {
            SemanticRelation = MetamorphicSemanticRelation.IndependentRunStable,
            OperationalRelation = MetamorphicOperationalRelation.IdenticalWork,
        };
        var leak = Require(MetamorphicComparator.Compare(isolation, ok, ok with { EvaluationSteps = ok.EvaluationSteps + 1 }));
        Assert.Equal(MetamorphicMismatchClass.StateIsolation, leak.Class);
        Assert.Equal(MetamorphicMismatchKind.EvaluationSteps, leak.Kind);
    }

    /// <summary>Counters are never compared when a surface cannot report them.</summary>
    [Fact]
    public void OperationalCounters_AreNotComparedWhenASurfaceCannotReportThem()
    {
        var observed = ObserveThrough(MetamorphicSurface.EvaluatorRunCountedObserved, "Output = range(1, 5).count");
        var plain = ObserveThrough(MetamorphicSurface.EvaluatorRun, "Output = range(1, 5).count");

        Assert.False(MetamorphicComparator.WorkIsComparable(observed, plain));
        Assert.True(MetamorphicComparator.WorkIsComparable(observed, observed));
    }

    // ── Decoder, fingerprints, and rejection reasons ─────────────────────────

    /// <summary>Every Phase 3 parameter point round-trips through its canonical encoding.</summary>
    [Fact]
    public void EveryPhase3ParameterPoint_RoundTripsThroughItsEncoding()
    {
        var points = 0;
        foreach (var parameters in Stratified.Where(p => Phase3Families.Contains(p.Family)))
        {
            var encoded = parameters.Encode();
            Assert.Equal(parameters.EncodedLength, encoded.Length);
            Assert.True(encoded.Length <= MetamorphicDecoder.MaxPayloadLength);
            Assert.Equal(parameters, MetamorphicDecoder.Decode(encoded));
            points++;
        }

        Assert.True(points > 500, $"expected a broad Phase 3 sweep, got {points}.");
    }

    /// <summary>
    /// Dimensions a budget law does not use collapse to their canonical index, so no two payloads
    /// build the same case under different fingerprints. Normalization is idempotent.
    /// </summary>
    [Fact]
    public void UnusedBudgetLawDimensions_CollapseToOneCanonicalPoint()
    {
        var neutralLaw = Array.IndexOf(
            MetamorphicBudgetLawTemplate.Laws.ToArray(), MetamorphicBudgetLaw.InBudgetNeutral);

        var seen = new HashSet<MetamorphicParameters>();
        for (var primary = 0; primary < MetamorphicDecoder.OffsetTable.Length; primary++)
        for (var isolation = 0; isolation < MetamorphicBudgetLawTemplate.IsolationModes.Length; isolation++)
        {
            var decoded = MetamorphicDecoder.Decode(
            [
                FamilyByte(MetamorphicFamily.BudgetLaw), 0, 0, (byte)primary, 0, 0,
                0, (byte)neutralLaw, 0, (byte)isolation,
            ]);

            Assert.Equal(decoded, MetamorphicDecoder.Decode(decoded.Encode()));
            seen.Add(decoded);
        }

        Assert.Single(seen);
    }

    /// <summary>Materially different Phase 3 templates never share a fingerprint.</summary>
    [Fact]
    public void Phase3Fingerprints_AreStableAndDistinguishMateriallyDifferentCases()
    {
        var byFingerprint = new Dictionary<string, MetamorphicParameters>(StringComparer.Ordinal);
        var collisions = 0;

        foreach (var parameters in Stratified.Where(p => Phase3Families.Contains(p.Family)))
        {
            var report = MetamorphicInvariants.Run(parameters.Encode());
            var again = MetamorphicInvariants.Run(parameters.Encode());
            Assert.Equal(report.Fingerprint, again.Fingerprint);

            if (byFingerprint.TryGetValue(report.Fingerprint, out var other) && other != parameters) collisions++;
            else byFingerprint[report.Fingerprint] = parameters;
        }

        Assert.True(byFingerprint.Count > 400, $"expected many distinct fingerprints, got {byFingerprint.Count}.");
        Assert.Equal(0, collisions);
    }

    /// <summary>Fingerprints never contain a value that varies between machines or runs.</summary>
    [Fact]
    public void Phase3Fingerprints_ContainNoUnstableValue()
    {
        foreach (var parameters in Stratified.Where(p => Phase3Families.Contains(p.Family)).Take(200))
        {
            var fingerprint = MetamorphicInvariants.Run(parameters.Encode()).Fingerprint;

            // Markers of the four things a fingerprint must never carry: a CLR type/hash rendering,
            // a memory address, a thread or process identity, and a timing.
            foreach (var unstable in new[]
                     {
                         "System.", "0x", "Thread", "Process", "Ticks", "Elapsed", "elapsed",
                         "HashCode", "@0", "\n", "\r",
                     })
            {
                Assert.DoesNotContain(unstable, fingerprint, StringComparison.Ordinal);
            }
        }
    }

    /// <summary>
    /// Every Phase 3 rejection carries a stable, documented reason and never reaches the
    /// comparator, so a high rejection rate can never hide unexplained coverage loss.
    ///
    /// <para>The inventory is written out by hand. Boundary-derivation reasons are prefixed with
    /// the resource dimension that produced them, so they are matched by SUFFIX against the
    /// dimension-independent forms — a new dimension inherits the inventory, a new KIND of
    /// rejection does not.</para>
    /// </summary>
    [Fact]
    public void EveryPhase3Rejection_IsOneOfTheDocumentedReasons()
    {
        string[] exactReasons =
        [
            // Group A: the optimizer-hit evidence gate.
            "left-optimizer-path-not-exercised",
            "right-optimizer-path-unexpectedly-exercised",
            "optimizer-source-declares-no-optimizer-path",
            "optimizer-source-declares-both-plan-and-fallback",
            // Group B: the cache-evidence gate and the budget the two forms cannot share.
            "rebuilt-form-does-not-share-the-cumulative-budget",
            "cache-use-does-not-consume-the-property",
            "cache-reuse-count-below-two",
            "left-cache-reuse-not-observed",
            "right-cache-reuse-unexpectedly-observed",
            // Group C: surface pairs that cannot see the source or would compare nothing.
            "surface-pair-requires-a-parsable-source",
            "surface-pair-shares-only-the-outcome",
            // Group D: laws that do not apply to a pair or a dimension.
            "equivalent-forms-do-not-share-a-work-boundary",
            "display-limit-does-not-fail-a-reservation",
            "interference-run-did-not-fail",
            "interference-source-missing",
            // Executor-wide: the machine-dependent backstop is classified, never compared.
            "platform-dependent-stack-backstop",
        ];

        string[] boundarySuffixes =
        [
            "-not-exercised-by-this-source",
            "-boundary-below-smallest-usable-limit",
            "-baseline-run-did-not-succeed",
            "-surface-rendered-nothing",
            "-no-success-below-search-ceiling",
            "-search-probe-budget",
            "-baseline-parse-error",
        ];

        var reasons = new SortedSet<string>(StringComparer.Ordinal);
        var rejected = 0;
        var total = 0;

        foreach (var parameters in Stratified.Where(p => Phase3Families.Contains(p.Family)))
        {
            total++;
            var report = MetamorphicInvariants.Run(parameters.Encode());
            if (report.Accepted) continue;

            rejected++;
            Assert.Null(report.Mismatch);
            Assert.False(string.IsNullOrWhiteSpace(report.RejectionReason));
            Assert.DoesNotContain(' ', report.RejectionReason);
            reasons.Add(report.RejectionReason);

            var documented = exactReasons.Contains(report.RejectionReason, StringComparer.Ordinal)
                || boundarySuffixes.Any(suffix => report.RejectionReason.EndsWith(suffix, StringComparison.Ordinal));
            Assert.True(documented, $"undocumented rejection reason '{report.RejectionReason}' ({parameters}).");
        }

        // Rejection is expected — many (source, dimension) pairs simply do not exercise a
        // dimension — but it must stay a bounded minority of the generated space.
        Assert.True(rejected < total / 2, $"{rejected} of {total} Phase 3 points were rejected.");
        Assert.NotEmpty(reasons);
    }

    /// <summary>
    /// Every Phase 3 generated source parses (except the ONE deliberately malformed entry-point
    /// template) and none of them uses structural member syntax, which stays out of scope for the
    /// whole metamorphic layer.
    /// </summary>
    [Fact]
    public void EveryPhase3GeneratedSource_ParsesUnlessDeliberatelyMalformed()
    {
        var malformed = MetamorphicEntryPointTemplate.Sources.Where(s => !s.Parses).Select(s => s.Source).ToHashSet();
        Assert.Single(malformed);

        foreach (var parameters in Stratified.Where(p => Phase3Families.Contains(p.Family)))
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            foreach (var source in new[] { testCase.LeftSource, testCase.RightSource })
            {
                Assert.DoesNotContain("public ", source, StringComparison.Ordinal);
                Assert.DoesNotContain("Output.", source, StringComparison.Ordinal);
                if (!malformed.Contains(source)) Assert.False(Parser.Parse(source).HasErrors, source);
            }
        }
    }

    /// <summary>
    /// A generous explicit budget behaves exactly like the default policy for the Phase 3
    /// families too — the same statement Phase 2 makes about its own families.
    /// </summary>
    [Fact]
    public void GenerousLimits_BehaveExactlyLikeTheDefaultPolicyForPhase3Families()
    {
        var checkedCases = 0;

        foreach (var parameters in Stratified
                     .Where(p => Phase3Families.Contains(p.Family) && p.LimitMode == MetamorphicLimitMode.Generous))
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            if (!testCase.Precondition.Satisfied) continue;

            Assert.Null(testCase.Limits!.MaxSteps);
            Assert.Null(testCase.Limits.MaxStringLength);
            Assert.Null(testCase.Limits.MaxMaterializedStringChars);

            foreach (var profile in new[] { testCase.LeftProfile, testCase.RightProfile })
            {
                var free = profile with { Limits = null };
                if (!MetamorphicSurfaces.TryObserve(
                        testCase.LeftSource, profile, MetamorphicExecutor.OptionsFor(profile), false,
                        out var bounded, out _))
                {
                    continue;
                }

                Assert.True(MetamorphicSurfaces.TryObserve(
                    testCase.LeftSource, free, MetamorphicExecutor.OptionsFor(free), false, out var unbounded, out _));
                Assert.Equal(unbounded, bounded);
            }

            checkedCases++;
        }

        Assert.True(checkedCases > 0, "the generous policy produced no comparable Phase 3 case");
    }

    // ── Observation helpers ──────────────────────────────────────────────────

    private static MetamorphicOperationalObservation Observe(
        string source, EvaluationLimits? limits, bool enableOptimizations)
    {
        Assert.True(
            MetamorphicExecutor.TryObserve(source, limits, enableOptimizations, out var observation, out var reason),
            reason);
        return observation;
    }

    private static MetamorphicOperationalObservation ObserveWithEvidence(
        string source, bool enableOptimizations, EvaluationLimits? limits = null)
        => ObserveThrough(MetamorphicSurface.EvaluatorRunCountedObserved, source, limits, enableOptimizations, true);

    private static MetamorphicOperationalObservation ObserveThrough(
        MetamorphicSurface surface,
        string source,
        EvaluationLimits? limits = null,
        bool enableOptimizations = true,
        bool collectEvidence = false)
    {
        var profile = new MetamorphicExecutionProfile(surface, limits, enableOptimizations);
        Assert.True(
            MetamorphicSurfaces.TryObserve(
                source, profile, MetamorphicExecutor.OptionsFor(profile), collectEvidence,
                out var observation, out var reason),
            reason);
        return observation;
    }

    private static MetamorphicMismatch Require(MetamorphicMismatch? mismatch)
        => Assert.IsType<MetamorphicMismatch>(mismatch);
}
