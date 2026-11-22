using System.Reflection;
using Xunit.Sdk;

namespace KatLang.Tests.Infrastructure;

/// <summary>
/// THE SLOW TIER (owner decisions 6 and 7, 2026-11-20). A test that carries
/// <c>[Trait("Tier", "Slow")]</c> runs nightly and before every release instead of on every pull
/// request: <c>scripts/validate-all.ps1 -Tier Fast</c> runs every other test, <c>-Tier Slow</c> only
/// these, and <c>-Tier Full</c> both. The tiers split the suite by ONE trait, so no test can drop out
/// of both. This inventory pins every Slow test with its category, the reason it may wait for the
/// nightly run, and its per-pull-request slice when it has one: a separate, untagged test whose cases
/// are a strict subset of the slow test's. Adding or removing a Slow tag updates
/// <see cref="Inventory"/> in the same diff, like the tutorial's skip inventory.
/// </summary>
public class SlowTierInventoryTests
{
    internal const string TraitName = "Tier";
    internal const string SlowValue = "Slow";

    internal enum Category
    {
        /// <summary>Checks the testing tools themselves (fuzz harnesses, campaigns, generators), not KatLang.</summary>
        HarnessSelfCheck,

        /// <summary>The Debug copy of a stress or stack probe whose Release copy runs on every pull request (stack-suite job).</summary>
        StressDebugCopy,

        /// <summary>An exhaustive boundary or limit scan; its slice keeps a representative boundary on every route.</summary>
        ExhaustiveScan,

        /// <summary>A full-size stack or memory check; a slice exists only when a smaller size still tells recursion from iteration.</summary>
        FullSizeStackOrMemory,

        /// <summary>An old-versus-new (reference against production) algorithm check; its slice is stratified.</summary>
        OldVersusNew,

        /// <summary>A further corpus variant of a sweep whose primary corpus stays per pull request.</summary>
        CorpusVariant,
    }

    /// <summary>One Slow test: <c>Class.Method</c>, relative to <c>KatLang.Tests.</c>.</summary>
    internal sealed record SlowTest(string Test, Category Category, string Reason, string? Slice = null);

    internal static readonly SlowTest[] Inventory =
    [
        // ── Debug copies of stress and stack probes whose Release copies run on every pull request ──
        new("EvaluatorOpenChainStackProcessTests.OpenChain_NeverCrashes_UnderCpuLoad",
            Category.StressDebugCopy,
            "A probe child sweeps the open-chain window while one busy thread per processor loads the machine "
            + "(several minutes). Its Release copy runs on every pull request in the stack-suite job, and the "
            + "unloaded Debug sweep stays per pull request."),
        new("DeferredCompileStackProcessTests.DeferredCompile_NeverCrashes_AcrossThreadSizes_UnderCpuLoad",
            Category.StressDebugCopy,
            "A probe child sweeps every thread size of a deferred compile while one busy thread per processor "
            + "loads the machine (several minutes). Its Release copy runs on every pull request in the "
            + "stack-suite job, and the unloaded Debug sweep stays per pull request."),
        new("AstStructuralDepthProcessTests.DeepHostAsts_NativeRecordEqualityAndHashing_AreStackSafe_InSubprocess",
            Category.StressDebugCopy,
            "A probe child compares and hashes the 200,000-level record graphs of every shape on a constrained stack. "
            + "Its Release copy runs on every pull request in the stack-suite job, and two of the shapes stay per "
            + "pull request in process (NativeRecordEqualityTests)."),

        // ── Harness self-checks ──
        new("EditorReadinessTests.EveryStratifiedPoint_RunsTheWholeHarnessWithoutAnUnexpectedException",
            Category.HarnessSelfCheck,
            "Runs the whole editor fuzz harness over all 5,322 stratified points to prove the campaign's reach "
            + "(it shares one execution per point with the two facts below). The editor fuzz harness tests and "
            + "the semantic-model tests stay per pull request."),
        new("EditorReadinessTests.EveryStratifiedPoint_ProducesAStableFingerprint",
            Category.HarnessSelfCheck,
            "A second, independent harness execution per stratified point must reproduce the first one's "
            + "fingerprint: a determinism check of the editor fuzz harness."),
        new("EditorReadinessTests.Fingerprints_CarryNothingThatCouldDifferBetweenRuns",
            Category.HarnessSelfCheck,
            "Scans every stratified point's harness fingerprint for run-dependent text (thread ids, timings, "
            + "hash codes): a check of the editor fuzz harness's reports."),
        .. SemanticHarnessChecks(),
        new("EditorFuzzHarnessTests.RepeatedRuns_AreIdentical_AndIndependentAcrossInterleaving",
            Category.HarnessSelfCheck,
            "Determinism of the editor fuzz harness: repeated and interleaved runs of its cases are identical."),
        new("Utf16FuzzHarnessTests.EveryCaseIsRepeatable_Isolated_AndOrderIndependent",
            Category.HarnessSelfCheck,
            "Determinism of the UTF-16 fuzz harness: every case repeats, isolated and in any order."),
        new("MetamorphicPhase4ReadinessTests.TheStratifiedSample_ReachesEveryFamilyRelationAndExecutionShape",
            Category.HarnessSelfCheck,
            "The metamorphic harness's coverage-balance probe: its stratified sample reaches every declared dimension."),
        new("MetamorphicPhase4AuditTests.EveryRejection_IsNamedMeasurableAndLeavesRealCoverage",
            Category.HarnessSelfCheck,
            "Audits the metamorphic harness's rejection vocabulary and per-family rejection rates."),

        // ── Exhaustive scans ──
        new("Q09IndependentHostileReviewTests.ExactRawTargets_AndEveryTransitionNearBulkBoundary_OnThreeRoutes",
            Category.ExhaustiveScan,
            "Seven loop and pipeline bodies padded to eleven raw-checkpoint targets of up to 32,768 rows, each "
            + "under seven step limits on three routes, plus the batch-end checkpoint slid over every prefix near "
            + "4096 for every body: about 9,500 executions.",
            "Q09IndependentHostileReviewTests.ExactRawTargets_AtTheFirstBulkBoundary_OnThreeRoutes"),
        new("MetamorphicPhase3FamilyTests.SearchedBoundaries_AreMonotoneAcrossTheirCompleteInterval",
            Category.ExhaustiveScan,
            "Every limit value of the complete search interval of both searched dimensions for 23 boundary "
            + "templates with the optimizer on and off: 92 units of about 4,100 executions each.",
            "MetamorphicPhase3FamilyTests.SearchedBoundaries_AreMonotoneAcrossTheirCompleteInterval_ForTwoTemplates"),
        new("StrategyNeutralBudgetParityTests.LongLoops_ChargeExactlyTheGenericCheckpoints_AcrossBlockBoundaries",
            Category.ExhaustiveScan,
            "Five loop templates at every iteration count within three of the first three checkpoint-block "
            + "boundaries and at 99,999 iterations, each generic against planned and at the exact step budget "
            + "and one below; the long runs dominate.",
            "StrategyNeutralBudgetParityTests.LongLoops_ChargeExactlyTheGenericCheckpoints_AcrossTheFirstBlockBoundary"),
        new("ResourceLimitTerminalityTests.TheLimitLaw_ALimitMayStopARunButNeverChangeItsValue",
            Category.ExhaustiveScan,
            "Seventeen absorption-shaped programs under two seeds at every value of six limit sweeps (548 values), "
            + "each a whole engine run: about 18,600 runs.",
            "ResourceLimitTerminalityTests.TheLimitLaw_ALimitMayStopARunButNeverChangeItsValue_ForFiveShapes"),
        new("IntegerDivisionContractTests.BoundaryMatrix_SourceEvaluationAndPlannedLoop_AgreeWithTheHelper",
            Category.ExhaustiveScan,
            "Every same-quantum row of the integer-division boundary matrix under four sign combinations, each a "
            + "parsed div and mod display plus a generic and a planned loop. The helper matrix, which covers every "
            + "row and quantum, stays per pull request.",
            "IntegerDivisionContractTests.BoundaryMatrix_SourceEvaluationAndPlannedLoop_AgreeWithTheHelper_OnEveryEighthRow"),
        new("BudgetCrossTalkMatrixTests.EngineAgreesOnSuccessWithTheStructuredSurfaces",
            Category.ExhaustiveScan,
            "Every budget case, primary limit and probe under every subset of the seven other limits (128 subsets), "
            + "on the engine and the structured evaluator.",
            "BudgetCrossTalkMatrixTests.EngineAgreesOnSuccessWithTheStructuredSurfaces_ForNoneEachAndAllOtherLimits"),
        new("BudgetCrossTalkMatrixTests.BudgetConfiguration_UnrelatedLimitValueDoesNotChangeVerdict",
            Category.ExhaustiveScan,
            "Every budget case, primary limit and probe under each unrelated limit at every non-binding value and "
            + "every pair of unrelated limits at every combination of their values (210 configurations per probe).",
            "BudgetCrossTalkMatrixTests.BudgetConfiguration_UnrelatedLimitValueDoesNotChangeVerdict_ForEveryPairAtItsFirstValues"),

        // ── Old-versus-new algorithm checks ──
        new("AliasAndBareForwardingTests.AnAlias_IsItsCallee_ForEverySupply",
            Category.OldVersusNew,
            "The alias transparency law: a direct call against an alias and a three-level alias chain, on every "
            + "route, for 28 callee shapes under 39 supplies (about 3,300 compared programs).",
            "AliasAndBareForwardingTests.AnAlias_IsItsCallee_ForEightRepresentativeSupplies"),
        new("DotCallValueBoundaryTests.DottedCall_AssemblesTheArgumentsOfTheDirectCall",
            Category.OldVersusNew,
            "R.F(args) against F(R, args), spread and unspread, for 29 receivers of every value kind and origin "
            + "against every callee shape: about 1,600 compared program pairs.",
            "DotCallValueBoundaryTests.DottedCall_AssemblesTheArgumentsOfTheDirectCall_ForARotatingQuarterOfTheCallees"),
        new("ScopeVisibilityIterativeUpdateTests.IterativeUpdates_MatchTheRecursiveAlgorithm_NodeForNodeAndMakeForMake",
            Category.OldVersusNew,
            "The iterative scope-visibility updates against the recursive reference, node for node, over 120 rows "
            + "(10 scripts x 6 priority modes x 2 collision settings), a few of them degenerate shapes of 20-30 s. "
            + "The Release stack-suite job still runs all 120 rows on every pull request.",
            "ScopeVisibilityIterativeUpdateTests.IterativeUpdates_MatchTheRecursiveAlgorithm_OnAStratifiedSlice"),

        // ── Full-size stack and memory checks ──
        new("NativeRecordEqualityTests.TwoHundredThousandLevels_EqualAndHashWithoutRecursion",
            Category.FullSizeStackOrMemory,
            "Equality and hashing of 200,000-level record graphs in fourteen shapes, in process. The slice keeps two "
            + "shapes at the full depth, which still tells recursion from iteration.",
            "NativeRecordEqualityTests.TwoHundredThousandLevels_EqualAndHashWithoutRecursion_ForTwoShapes"),
        new("CallableAliasBindingIndirectionTests.AlgorithmLinkChains_ReportTheSameArityMismatchOnEveryRoute",
            Category.FullSizeStackOrMemory,
            "The required 10,000-link .Algorithm chain on every route and a 1 MiB stack. The slice keeps the 3- and "
            + "1,000-link rows; about 300 links exhausted the stack before the fix, so 1,000 still tells recursion "
            + "from iteration.",
            "CallableAliasBindingIndirectionTests.AlgorithmLinkChains_ReportTheSameArityMismatchOnEveryRoute_UpToAThousandLinks"),
        new("CallableAliasBindingIndirectionTests.AliasChains_NormalizeOnAOneMebibyteStack",
            Category.FullSizeStackOrMemory,
            "Alias chains of up to 10,000 links to seven kinds of target on a 1 MiB stack. The slice keeps every "
            + "target below 10,000 links; the host-built 2,000-hop chain on a 1 MiB stack also stays per pull request.",
            "CallableAliasBindingIndirectionTests.AliasChains_NormalizeOnAOneMebibyteStack_UpToAThousandLinks"),
        new("CallableAliasBindingIndirectionTests.MemberPathAliasChains_NormalizeOnAOneMebibyteStack",
            Category.FullSizeStackOrMemory,
            "Member-path alias chains of up to 10,000 links, plain and mixed, on a 1 MiB stack. The slice keeps "
            + "both forms below 10,000 links.",
            "CallableAliasBindingIndirectionTests.MemberPathAliasChains_NormalizeOnAOneMebibyteStack_UpToAThousandLinks"),
        new("LocalOnlyLoopStepPeakMemoryProcessTests.PeakWorkingSet_StaysWithinSixteenMiB_FromTenToTheFifthToTenToTheSixthRounds",
            Category.FullSizeStackOrMemory,
            "Five probe children, each comparing the peak working set of 10^5 and 10^6 loop rounds; a smaller "
            + "round count is no subset of these cases. The deterministic reclaim tests of the same file stay per "
            + "pull request."),
        new("IdentityKeyedRunStorePeakMemoryProcessTests.PeakWorkingSet_StaysWithinFortyMiB_FromTenToTheFifthToTenToTheSixthRounds",
            Category.FullSizeStackOrMemory,
            "Three probe children, each comparing the peak working set of 10^5 and 10^6 rounds; a smaller round "
            + "count is no subset of these cases. The deterministic retention tests of the same file stay per pull "
            + "request."),

        // ── Further corpus variants ──
        .. ExplorerCorpusVariants(),
    ];

    /// <summary>
    /// All four variants draw on the 2,821 semantic-explorer programs. The open variants skip programs with a root open.
    /// The four LanguageSpec variants stay per pull request: they caught a real defect on 2026-11-16.
    /// </summary>
    private static IEnumerable<SlowTest> ExplorerCorpusVariants()
        => from variant in new[] { "HolderVariant", "OpenVariant" }
           from shape in new[] { "RootParameters", "RootAndCallableParameters" }
           select new SlowTest(
               $"DeferredProvisionalParitySweepTests.SemanticExplorerCorpus_{variant}_{shape}",
               Category.CorpusVariant,
               "Sweeps eligible semantic-explorer programs as load-bearing clause bodies against the same text "
               + "without the load. The same frame's LanguageSpec variants stay per pull request.");

    /// <summary>
    /// The long checks of the semantic campaign harness (supervised workers, batches, reduction and its
    /// wider recipe): they test the campaign tooling the nightly semantic sweeps use, not KatLang. Each
    /// class's shorter checks stay per pull request.
    /// </summary>
    private static IEnumerable<SlowTest> SemanticHarnessChecks()
        => new[]
        {
            "SemanticCampaignTests.ASupervisedCampaign_FindsThePlantedFailureInAChild_AndRetainsItsEvidence",
            "SemanticSupervisionTests.MalformedOrIncompleteOutput_HasItsOwnClassification",
            "SemanticSupervisionTests.Timeout_TerminatesTheWorkerTree_AndKeepsTheReproducer",
            "SemanticSupervisionTests.UnbrokenOutput_IsBoundedAndDrained_AndSupervisionEvidenceIsRetained",
            "SemanticSupervisionTests.BatchProgressDeadline_CountsFromReadiness_NotFromLaunch",
            "SemanticSupervisionTests.NormalCompletion_ReturnsTheWorkersSemanticVerdict",
            "SemanticSupervisionTests.AbnormalExit_IsACrash_AndTheReproducerIsRetained",
            "SemanticSupervisionTests.ExternalCancellation_TerminatesAnAlreadyRunningWorker",
            "SemanticNestedWiderTests.EveryWiderProgram_ParsesCleanly_InEveryMember",
            "SemanticExhaustiveCampaignTests.SupervisedBatches_IsolateACrash_AndKeepEveryFailingReproducer",
            "SemanticExhaustiveCampaignTests.AChildCrash_RemainsAFailureWhenEveryStandaloneCasePasses",
            "SemanticSupervisedReductionTests.ASupervisedReduction_OfAChildThatFailsOnAKnownShape_IsMinimalStableAndKeepsItsSignature",
        }.Select(static test => new SlowTest(
            "SemanticTesting." + test,
            Category.HarnessSelfCheck,
            "One of the long checks of the semantic campaign harness (supervision, batches, reduction or recipe "
            + "generation); the tool's shorter checks stay per pull request."));

    private const string Namespace = "KatLang.Tests.";

    [Fact]
    public void EverySlowTag_IsPinnedByTheInventory_AndEveryEntryIsTagged()
    {
        var tagged = TaggedTests().Order(StringComparer.Ordinal).ToArray();
        var pinned = Inventory.Select(static entry => entry.Test).Order(StringComparer.Ordinal).ToArray();
        Assert.Equal(pinned.Distinct(StringComparer.Ordinal).Count(), pinned.Length);
        Assert.Equal(pinned, tagged);
    }

    [Fact]
    public void TheTierTrait_HasOnlyTheSlowValue_AndOnlyOnTestMethods()
    {
        foreach (var (member, name, value) in TierTraits())
        {
            Assert.True(value == SlowValue, $"{member} carries [Trait(\"{name}\", \"{value}\")]; the only tier value is \"{SlowValue}\".");
            var method = FindMethod(member.StartsWith(Namespace, StringComparison.Ordinal) ? member[Namespace.Length..] : member);
            Assert.True(method is not null && IsTest(method), $"{member} carries the tier trait but is not a [Fact] or [Theory] method.");
        }
    }

    [Fact]
    public void EveryEntry_StatesItsReason_AndEverySliceRunsPerPullRequest()
    {
        foreach (var entry in Inventory)
        {
            Assert.False(string.IsNullOrWhiteSpace(entry.Reason), $"{entry.Test} needs a reason.");
            if (entry.Slice is not { } slice)
                continue;
            var method = FindMethod(slice);
            Assert.True(method is not null, $"The slice {slice} of {entry.Test} is not a test method.");
            Assert.True(IsTest(method!), $"The slice {slice} of {entry.Test} is not a [Fact] or [Theory].");
            Assert.False(IsSlow(method!), $"The slice {slice} of {entry.Test} is itself Slow, so no pull request runs it.");
            Assert.True(method!.DeclaringType == FindMethod(entry.Test)!.DeclaringType,
                $"The slice {slice} of {entry.Test} belongs in the same class, beside the cases it repeats.");
        }
    }

    /// <summary>
    /// A theory slice repeats rows of its slow theory: every data row of the slice is a data row of the
    /// slow theory. (A slice may also narrow the work inside a row; that part is argued in its reason.)
    /// </summary>
    [Fact]
    public void EveryTheorySlice_RepeatsRowsOfItsSlowTheory()
    {
        foreach (var entry in Inventory)
        {
            if (entry.Slice is not { } slice)
                continue;
            var full = FindMethod(entry.Test)!;
            var part = FindMethod(slice)!;
            if (!IsTheory(full) || !IsTheory(part)
                || !full.GetParameters().Select(static p => p.ParameterType).SequenceEqual(part.GetParameters().Select(static p => p.ParameterType)))
            {
                continue;
            }

            var rows = Rows(full).Select(RowKey).ToHashSet(StringComparer.Ordinal);
            foreach (var row in Rows(part))
                Assert.True(rows.Contains(RowKey(row)), $"The slice {slice} has the row ({RowKey(row)}), which {entry.Test} does not run.");
        }
    }

    /// <summary>
    /// The AGENTS.md coverage map names the slow tests of every area, because local V3 runs those of the
    /// areas a change touches: every class with a Slow test is named there (a sub-namespace such as
    /// <c>SemanticTesting</c> may stand for its classes).
    /// </summary>
    [Fact]
    public void EverySlowClass_IsNamedInTheCoverageMapsSlowTierBullet()
    {
        var agents = File.ReadAllLines(Path.Combine(RepoRoot.Find(), "AGENTS.md"));
        var bullet = Assert.Single(agents, static line => line.StartsWith("- Slow tier by area", StringComparison.Ordinal));
        foreach (var entry in Inventory)
        {
            var parts = entry.Test.Split('.');
            var className = parts[^2];
            var named = bullet.Contains($"`{className}`", StringComparison.Ordinal)
                || (parts.Length > 2 && bullet.Contains($"`{parts[0]}`", StringComparison.Ordinal));
            Assert.True(named, $"{entry.Test}: the slow-tier bullet of the AGENTS.md coverage map does not name {className}.");
        }
    }

    [Fact]
    public void EveryStressDebugCopy_KeepsItsReleaseCopyInTheStackSuite()
    {
        var script = File.ReadAllText(Path.Combine(RepoRoot.Find(), "scripts", "validate-stack-suites.ps1"));
        foreach (var entry in Inventory.Where(static entry => entry.Category == Category.StressDebugCopy))
        {
            var type = FindMethod(entry.Test)?.DeclaringType;
            Assert.NotNull(type);
            Assert.Contains($"\"{type!.FullName}\"", script, StringComparison.Ordinal);
        }
    }

    private static Assembly TestAssembly => typeof(SlowTierInventoryTests).Assembly;

    private static IEnumerable<(string Member, string Name, string Value)> TierTraits()
    {
        foreach (var type in TestAssembly.GetTypes())
        {
            foreach (var (name, value) in Traits(type))
                yield return (type.FullName!, name, value);
            foreach (var method in type.GetMethods(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static | BindingFlags.DeclaredOnly))
                foreach (var (name, value) in Traits(method))
                    yield return (type.FullName + "." + method.Name, name, value);
        }
    }

    private static IEnumerable<(string Name, string Value)> Traits(MemberInfo member)
        => member.GetCustomAttributesData()
            .Where(static data => data.AttributeType == typeof(TraitAttribute))
            .Select(static data => ((string)data.ConstructorArguments[0].Value!, (string)data.ConstructorArguments[1].Value!))
            .Where(static trait => trait.Item1 == TraitName);

    private static IEnumerable<string> TaggedTests()
        => TierTraits().Where(static trait => trait.Value == SlowValue)
            .Select(static trait => trait.Member.StartsWith(Namespace, StringComparison.Ordinal) ? trait.Member[Namespace.Length..] : trait.Member);

    private static bool IsSlow(MethodInfo method)
        => Traits(method).Any(static trait => trait.Value == SlowValue) || Traits(method.DeclaringType!).Any(static trait => trait.Value == SlowValue);

    private static bool IsTest(MethodInfo method)
        => method.GetCustomAttributes<FactAttribute>(inherit: true).Any();

    private static bool IsTheory(MethodInfo method)
        => method.GetCustomAttributes<TheoryAttribute>(inherit: true).Any();

    private static IEnumerable<object?[]> Rows(MethodInfo method)
        => method.GetCustomAttributes<DataAttribute>(inherit: true).SelectMany(data => data.GetData(method));

    private static string RowKey(object?[] row)
        => string.Join(", ", row.Select(static value => value switch
        {
            null => "null",
            string text => "\"" + text + "\"",
            bool flag => flag ? "true" : "false",
            IFormattable number => number.ToString(null, System.Globalization.CultureInfo.InvariantCulture),
            var other => other.ToString(),
        }));

    private static Type? FindType(string name) => TestAssembly.GetType(Namespace + name);

    private static MethodInfo? FindMethod(string name)
    {
        var separator = name.LastIndexOf('.');
        if (separator < 1)
            return null;
        return FindType(name[..separator])?.GetMethod(name[(separator + 1)..],
            BindingFlags.Public | BindingFlags.Instance | BindingFlags.Static | BindingFlags.DeclaredOnly);
    }
}
