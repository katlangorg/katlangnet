using System.Globalization;
using System.Text;
using KatLang.ParserFuzz;

namespace KatLang.Tests;

/// <summary>
/// Phase 4 campaign-readiness probes: the checks that decide whether a long campaign is worth
/// starting at all.
///
/// <para>Three questions. Does a deterministic stratified sample actually REACH every family,
/// relation, optimizer path, cache profile, surface pair, resource dimension, budget law, run
/// plan, and execution order the harness claims to test — or would a campaign spend thirty
/// minutes exploring a fraction of it? Is everything a payload can select BOUNDED? And is the
/// whole pipeline DETERMINISTIC — twice in one process, in reversed order, and through replay?</para>
///
/// <para>Set <c>KATLANG_METAMORPHIC_READINESS_REPORT</c> to a file path to have the coverage
/// distribution written there. The assertions do not depend on it; it exists so a campaign report
/// can quote measured numbers instead of estimates.</para>
/// </summary>
public class MetamorphicPhase4ReadinessTests
{
    private static List<MetamorphicParameters> Stratified { get; } =
        MetamorphicTemplates.EnumerateStratifiedParameters().ToList();

    private sealed record Tally(SortedDictionary<string, int> Counts)
    {
        public Tally() : this(new SortedDictionary<string, int>(StringComparer.Ordinal)) { }

        public void Add(string key) => Counts[key] = Counts.GetValueOrDefault(key) + 1;

        public IEnumerable<string> Keys => Counts.Keys;

        public int Total => Counts.Values.Sum();

        public override string ToString()
            => string.Join(", ", Counts.Select(pair =>
                $"{pair.Key}={pair.Value.ToString(CultureInfo.InvariantCulture)}"));
    }

    /// <summary>
    /// The coverage-balance probe. Runs the deterministic stratified sample and requires every
    /// declared dimension of the harness to be reached, with no family reduced to nothing by its
    /// own preconditions.
    /// </summary>
    [Fact]
    public void TheStratifiedSample_ReachesEveryFamilyRelationAndExecutionShape()
    {
        var acceptedByFamily = new Tally();
        var rejectedByFamily = new Tally();
        var rejectionReasons = new Tally();
        var semanticRelations = new Tally();
        var operationalRelations = new Tally();
        var optimizerPaths = new Tally();
        var cacheProfiles = new Tally();
        var surfacePairs = new Tally();
        var budgetLaws = new Tally();
        var resourceDimensions = new Tally();
        var runPlans = new Tally();
        var executionOrders = new Tally();
        var outcomes = new Tally();
        var workComparison = new Tally();

        foreach (var parameters in Stratified)
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            var execution = MetamorphicExecutor.Execute(testCase);
            var family = testCase.FamilyId;

            if (execution.Accepted) acceptedByFamily.Add(family);
            else
            {
                rejectedByFamily.Add(family);
                rejectionReasons.Add(family + "/" + execution.RejectionReason);
            }

            semanticRelations.Add(testCase.SemanticRelation.ToString());
            operationalRelations.Add(testCase.OperationalRelation.ToString());
            runPlans.Add(MetamorphicExecutor.DescribeRunPlan(testCase));
            executionOrders.Add(testCase.ExecutionOrder.ToString());

            if (testCase.Family == MetamorphicFamily.EntryPointParity)
                surfacePairs.Add(MetamorphicEntryPointTemplate.PairOf(parameters).Id);

            if (testCase.Family == MetamorphicFamily.BudgetLaw)
            {
                budgetLaws.Add(MetamorphicBudgetLawTemplate.LawOf(parameters).ToString());
                resourceDimensions.Add(MetamorphicBudgetLawTemplate.DimensionOf(parameters).Id);
            }

            if (!execution.Accepted) continue;

            foreach (var side in new[] { execution.Left, execution.Right })
            {
                if (side is null) continue;
                outcomes.Add(Outcome(side));
                if (side.OptimizerEvidence is { } optimizer) optimizerPaths.Add(optimizer.Feature);
                if (side.CacheEvidence is { } cache) cacheProfiles.Add(cache.Feature);
            }

            if (execution is { Left: { } left, Right: { } right })
                workComparison.Add(MetamorphicComparator.WorkIsComparable(left, right) ? "compared" : "partial");
        }

        WriteReport(new (string, Tally)[]
        {
            ("accepted by family", acceptedByFamily),
            ("rejected by family", rejectedByFamily),
            ("rejections by family and reason", rejectionReasons),
            ("semantic relations", semanticRelations),
            ("operational relations", operationalRelations),
            ("optimizer paths", optimizerPaths),
            ("cache profiles", cacheProfiles),
            ("entry-point pairs", surfacePairs),
            ("budget laws", budgetLaws),
            ("resource dimensions", resourceDimensions),
            ("run plans", runPlans),
            ("execution orders", executionOrders),
            ("side outcomes", outcomes),
            ("operational comparison", workComparison),
        });

        // Every registered family must leave accepted coverage behind.
        foreach (var definition in MetamorphicFamilyRegistry.All)
        {
            Assert.True(
                acceptedByFamily.Counts.GetValueOrDefault(definition.Id) > 0,
                $"Family '{definition.Id}' contributes no accepted case: {rejectionReasons}");
        }

        // Every declared relation, on both axes.
        foreach (var relation in Enum.GetValues<MetamorphicSemanticRelation>())
            Assert.Contains(relation.ToString(), semanticRelations.Keys);
        foreach (var relation in Enum.GetValues<MetamorphicOperationalRelation>())
            Assert.Contains(relation.ToString(), operationalRelations.Keys);

        // Every registered entry-point pair, budget law, and resource dimension.
        foreach (var pair in MetamorphicEntryPointTemplate.Pairs)
            Assert.Contains(pair.Id, surfacePairs.Keys);
        foreach (var law in MetamorphicBudgetLawTemplate.Laws)
            Assert.Contains(law.ToString(), budgetLaws.Keys);
        foreach (var dimension in MetamorphicBoundaryPolicy.All)
            Assert.Contains(dimension.Id, resourceDimensions.Keys);

        // Both execution orders, and every run plan the harness can build.
        Assert.Contains(MetamorphicExecutionOrder.LeftFirst.ToString(), executionOrders.Keys);
        Assert.Contains(MetamorphicExecutionOrder.RightFirst.ToString(), executionOrders.Keys);
        Assert.Equal(
            Enum.GetValues<MetamorphicRunPlan>().Length,
            runPlans.Keys.Count());

        // Every distinguished optimizer path the evidence model can classify, and cache profiles
        // covering a miss, a single hit, and several hits.
        foreach (var path in Enum.GetValues<MetamorphicOptimizerPath>())
        {
            if (path == MetamorphicOptimizerPath.None) continue;
            Assert.True(
                optimizerPaths.Keys.Any(feature => feature.Contains(path.ToString(), StringComparison.Ordinal)),
                $"No accepted case exercised optimizer path {path}: {optimizerPaths}");
        }

        Assert.True(cacheProfiles.Keys.Any(f => f.StartsWith("h0", StringComparison.Ordinal)), "No cache MISS profile.");
        Assert.True(cacheProfiles.Keys.Any(f => f.StartsWith("h1", StringComparison.Ordinal)), "No single-HIT profile.");
        Assert.True(
            cacheProfiles.Keys.Any(f => !f.StartsWith("h0", StringComparison.Ordinal) && !f.StartsWith("h1", StringComparison.Ordinal)),
            "No multiple-hit cache profile.");

        // Success, ordinary semantic failure, and resource-limit failure all reached.
        Assert.Contains("ok", outcomes.Keys);
        Assert.True(outcomes.Keys.Any(o => o.StartsWith("semantic:", StringComparison.Ordinal)), "No semantic failure.");
        Assert.True(outcomes.Keys.Any(o => o.StartsWith("resource:", StringComparison.Ordinal)), "No resource failure.");

        // And the campaign must actually reach the WORK comparison rather than stopping at
        // semantics for everything.
        Assert.True(workComparison.Counts.GetValueOrDefault("compared") > workComparison.Total / 2,
            $"Most accepted pairs never reached the operational comparison: {workComparison}");

        // No single family may dominate the sample so heavily that the others are noise.
        var largest = acceptedByFamily.Counts.Values.Max();
        Assert.True(
            largest < acceptedByFamily.Total * 3 / 4,
            $"One family holds {largest} of {acceptedByFamily.Total} accepted cases: {acceptedByFamily}");
    }

    private static string Outcome(MetamorphicOperationalObservation observation)
    {
        var semantic = observation.Semantic;
        if (semantic.Outcome != "err") return "ok";
        return (semantic.IsResourceLimit ? "resource:" : "semantic:") + (semantic.ErrorCategory ?? "unknown");
    }

    private static void WriteReport(IReadOnlyList<(string Title, Tally Tally)> sections)
    {
        var path = Environment.GetEnvironmentVariable("KATLANG_METAMORPHIC_READINESS_REPORT");
        if (string.IsNullOrWhiteSpace(path)) return;

        var text = new StringBuilder(4096);
        text.AppendLine("metamorphic readiness: deterministic stratified sample");
        text.Append("points: ").AppendLine(Stratified.Count.ToString(CultureInfo.InvariantCulture));
        foreach (var (title, tally) in sections)
        {
            text.AppendLine();
            text.Append(title).Append(" (").Append(tally.Total.ToString(CultureInfo.InvariantCulture)).AppendLine("):");
            foreach (var pair in tally.Counts)
                text.Append("  ").Append(pair.Key).Append(" = ").AppendLine(pair.Value.ToString(CultureInfo.InvariantCulture));
        }

        File.WriteAllText(path, text.ToString());
    }

    /// <summary>
    /// The determinism probe: the same payloads twice in one process, in reversed order, and
    /// through the deterministic replay path must agree on the semantic observation, the
    /// operational observation, the fingerprint, acceptance, and mismatch classification.
    ///
    /// <para>Fresh-process determinism is covered by the campaign's own corpus replay, which runs
    /// in its own process and is required to be byte-identical; this covers everything a single
    /// process can establish.</para>
    /// </summary>
    [Fact]
    public void TheWholePipeline_IsDeterministicForwardsBackwardsAndThroughReplay()
    {
        var payloads = Stratified
            .Where((_, index) => index % 37 == 0)
            .Select(parameters => parameters.Encode())
            .ToList();

        Assert.True(payloads.Count > 30, $"Only {payloads.Count} determinism probes were selected.");

        var forward = payloads.Select(payload => MetamorphicInvariants.Run(payload)).ToList();

        // Same payloads, reversed order, in the same process: nothing may depend on what ran before.
        var backward = Enumerable.Reverse(payloads).Select(payload => MetamorphicInvariants.Run(payload)).ToList();
        backward.Reverse();

        // And a third pass, to separate "stable" from "stable the second time".
        var again = payloads.Select(payload => MetamorphicInvariants.Run(payload)).ToList();

        for (var i = 0; i < payloads.Count; i++)
        {
            var where = forward[i].Parameters.ToString();

            foreach (var other in new[] { backward[i], again[i] })
            {
                Assert.Equal(forward[i].Parameters, other.Parameters);
                Assert.Equal(forward[i].Accepted, other.Accepted);
                Assert.Equal(forward[i].RejectionReason, other.RejectionReason);
                Assert.Equal(forward[i].Execution.Left, other.Execution.Left);
                Assert.Equal(forward[i].Execution.Right, other.Execution.Right);
                Assert.Equal(forward[i].Fingerprint, other.Fingerprint);
                Assert.Equal(forward[i].Mismatch?.Kind, other.Mismatch?.Kind);
                Assert.Equal(forward[i].Mismatch?.Class, other.Mismatch?.Class);
                Assert.True(other.Mismatch is null, $"{where}: the readiness probe found a mismatch.");
            }
        }
    }

    /// <summary>
    /// The throughput and bounds probe. Every quantity a payload can influence is bounded by a
    /// fixed harness constant rather than by an encoded integer, and the most expensive shapes the
    /// campaign can build stay small.
    ///
    /// <para>No wall-clock assertion: a timing threshold would fail on a loaded machine and prove
    /// nothing about the harness. What is asserted is the structural bound that makes the runtime
    /// small in the first place.</para>
    /// </summary>
    [Fact]
    public void NothingAPayloadSelects_GrowsWithAnEncodedInteger()
    {
        long worstItems = 0;
        long worstStrings = 0;
        var worstSource = 0;
        var worstLimit = 0L;

        foreach (var parameters in Stratified)
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            worstItems = Math.Max(worstItems, testCase.ExpectedItemTotal);
            worstStrings = Math.Max(worstStrings, testCase.ExpectedStringTotal);
            worstSource = Math.Max(worstSource, Math.Max(testCase.LeftSource.Length, testCase.RightSource.Length));

            foreach (var limits in new[] { testCase.LeftProfile.Limits, testCase.RightProfile.Limits, testCase.InterferenceLimits })
            {
                if (limits is null) continue;
                worstLimit = Math.Max(worstLimit, LargestConfiguredLimit(limits));
            }
        }

        // The bounds themselves. Each one is a fixed constant of the harness or of the runtime's
        // supported range, never a decoded value.
        Assert.True(worstItems <= 100_000, $"A case expects {worstItems} materialized items.");
        Assert.True(worstStrings <= 100_000, $"A case expects {worstStrings} materialized string units.");
        Assert.True(worstSource <= 4_096, $"A case generates a {worstSource}-character source.");
        Assert.True(worstLimit <= EvaluationLimits.MaxSupportedDisplayLength, $"A case configures a limit of {worstLimit}.");

        // Recursion, search, and concurrency are all fixed and small.
        Assert.Equal(4, MetamorphicExecutor.ParallelTaskCount);
        Assert.Equal(3, MetamorphicExecutor.InterleavedRunCount);
        Assert.Equal(32, MetamorphicBoundaryPolicy.MaxSearchProbes);
        Assert.Equal(4_096, MetamorphicBoundaryPolicy.SearchCeilingItems);

        // The decoder reads a fixed prefix, so an arbitrarily large input costs the same as a
        // ten-byte one and cannot make the harness allocate.
        var huge = new byte[1 << 20];
        for (var i = 0; i < huge.Length; i++) huge[i] = (byte)(i * 31);
        var decodedHuge = MetamorphicDecoder.Decode(huge);
        Assert.Equal(decodedHuge, MetamorphicDecoder.Decode(huge.AsSpan(0, MetamorphicDecoder.MaxPayloadLength)));
        Assert.True(decodedHuge.Encode().Length <= MetamorphicDecoder.MaxPayloadLength);
    }

    private static long LargestConfiguredLimit(EvaluationLimits limits)
    {
        long largest = 0;
        if (limits.MaxDepth is { } depth) largest = Math.Max(largest, depth);
        if (limits.MaxSteps is { } steps) largest = Math.Max(largest, steps);
        if (limits.MaxMaterializedItems is { } items) largest = Math.Max(largest, items);
        if (limits.MaxCollectionItems is { } collection) largest = Math.Max(largest, collection);
        if (limits.MaxMaterializedStringChars is { } chars) largest = Math.Max(largest, chars);
        if (limits.MaxStringLength is { } stringLength) largest = Math.Max(largest, stringLength);
        if (limits.MaxDisplayLength is { } display) largest = Math.Max(largest, display);
        return largest;
    }
}
