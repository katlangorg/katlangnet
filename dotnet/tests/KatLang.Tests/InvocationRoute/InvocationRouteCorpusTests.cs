namespace KatLang.Tests.InvocationRoute;

/// <summary>
/// META-S3-4: the generalized invocation-capture corpus on every engine. Each case's semantics — outcome,
/// emitted count, host effects in order, semantic steps, raw expression checkpoints and materialization
/// counters — must be identical on the synchronous generic, synchronous optimized and asynchronous engines
/// and equal its frozen expectation (<see cref="InvocationRouteExpectations"/>); each ordinary/planned pair
/// must agree on the same engine; each bounded MaxSteps scan must agree across the three engines.
/// </summary>
public class InvocationRouteCorpusTests
{
    public static TheoryData<string> CaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var c in InvocationRouteCorpus.Cases) data.Add(c.Id);
        return data;
    }

    public static TheoryData<string> EquivalencePairs()
    {
        var data = new TheoryData<string>();
        foreach (var c in InvocationRouteCorpus.Cases.Where(c => c.Plain)) data.Add(c.Id[..^1]);
        return data;
    }

    public static TheoryData<string, int> ScanPoints()
    {
        var data = new TheoryData<string, int>();
        foreach (var id in InvocationRouteCorpus.ScanIds)
            for (var limit = 1; limit <= 24; limit++)
                data.Add(id, limit);
        return data;
    }

    [Fact]
    public void TheCorpus_HasItsReviewedShape()
    {
        var ids = InvocationRouteCorpus.Cases.Select(c => c.Id).ToList();
        Assert.Equal(164, ids.Count);
        Assert.Equal(ids.Count, ids.Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(35, InvocationRouteCorpus.Cases.Count(c => c.Plain));
        Assert.All(InvocationRouteCorpus.Cases.Where(c => c.Plain), c => Assert.Contains(c.Id[..^1] + "m", ids));
        Assert.Equal(10, ids.Count(id => id.StartsWith("EQ1", StringComparison.Ordinal) && id.Length == 6 && id.EndsWith('p')));
        Assert.Equal(216, ScanPoints().Count);
        Assert.Equal(ids.Order(StringComparer.Ordinal), InvocationRouteExpectations.Semantics.Keys.Order(StringComparer.Ordinal));
    }

    /// <summary>
    /// The process plan mode is exactly its switch, and it is effective: in the forced whole-suite plan run a
    /// META-free program routes its supplied invocations through plans (its META twin's, see
    /// <see cref="InvocationRouteExpectations.RetentionOf"/>) with unchanged semantics; otherwise it forms none.
    /// </summary>
    [Fact]
    public async Task TheProcessPlanMode_FollowsItsSwitch_AndIsEffective()
    {
        Assert.Equal(Environment.GetEnvironmentVariable(ForcedInvocationPlansHook.Variable) == "1", ForcedInvocationPlansHook.Forced);
        var plain = await InvocationRouteCorpus.Observe(InvocationRouteCorpus.ById("EQ1p"), 0);
        Assert.Equal(InvocationRouteExpectations.Semantics["EQ1p"], plain.Semantic);
        Assert.Equal(ForcedInvocationPlansHook.Forced ? (2L, 2L) : (0L, 0L), (plain.Plans, plain.Formations));
    }

    [Theory]
    [MemberData(nameof(CaseIds))]
    public async Task EveryCase_HasItsSemantics_OnEveryEngine(string id)
    {
        var c = InvocationRouteCorpus.ById(id);
        var expected = InvocationRouteExpectations.Semantics[id];
        var (plans, formations) = InvocationRouteExpectations.RetentionOf(c);
        foreach (var mode in InvocationRouteCorpus.ModesOf(c))
        {
            var observed = await InvocationRouteCorpus.Observe(c, mode);
            Assert.True(expected == observed.Semantic, $"{id} mode {mode}:\n expected {expected}\n observed {observed.Semantic}");
            if (mode == InvocationRouteCorpus.ModesOf(c)[0])
            {
                Assert.Equal(plans, observed.Plans);
                Assert.Equal(formations, observed.Formations);
            }
        }
    }

    [Theory]
    [MemberData(nameof(EquivalencePairs))]
    public async Task APlannedInvocation_HasTheOrdinaryValue_ChargesAndDiagnostics(string pair)
    {
        foreach (var mode in new[] { 0, 1, 2 })
        {
            var ordinary = await InvocationRouteCorpus.Observe(InvocationRouteCorpus.ById(pair + "p"), mode);
            var planned = await InvocationRouteCorpus.Observe(InvocationRouteCorpus.ById(pair + "m"), mode);
            Assert.True(ordinary.Semantic == planned.Semantic, $"{pair} mode {mode}:\n ordinary {ordinary.Semantic}\n planned  {planned.Semantic}");
        }
    }

    [Theory]
    [MemberData(nameof(ScanPoints))]
    public async Task ABoundedStepLimit_AgreesOnEveryEngine(string id, int limit)
    {
        var c = InvocationRouteCorpus.ById(id) with { Limits = new EvaluationLimits { MaxSteps = limit } };
        var generic = await InvocationRouteCorpus.Observe(c, 0);
        var optimized = await InvocationRouteCorpus.Observe(c, 1);
        var asynchronous = await InvocationRouteCorpus.Observe(c, 2);
        Assert.Equal(generic.Semantic, optimized.Semantic);
        Assert.Equal(generic.Semantic, asynchronous.Semantic);
    }

    [Fact]
    public async Task EngineFacts_TheOptimizedLoop_RealSuspension_HostExceptionsAndCancellation()
    {
        // The projected step of the rebuilt wrappers is planned by the native loop optimizer.
        foreach (var id in new[] { "A1", "A2", "A4", "B1", "C1", "C3", "D1", "X13" })
            Assert.True((await InvocationRouteCorpus.Observe(InvocationRouteCorpus.ById(id), 1)).Loops > 0, id);
        // The async engine genuinely suspends where the corpus says so.
        foreach (var id in new[] { "A5", "S6e", "X18" })
            Assert.True((await InvocationRouteCorpus.Observe(InvocationRouteCorpus.ById(id), 2)).Suspensions > 0, id);
        foreach (var mode in new[] { 0, 1, 2 })
        {
            // The rebuilt invocation's argument is the ORIGINAL cell: `trace(7)` runs once.
            Assert.Equal("7,7,7", (await InvocationRouteCorpus.Observe(InvocationRouteCorpus.ById("S3"), mode)).Trace);
            // The original host exception propagates through Invoke() (Observe checks its identity).
            Assert.Equal("THROW same host exception", (await InvocationRouteCorpus.Observe(InvocationRouteCorpus.ById("X7b"), mode)).Outcome);
            // Cancellation inside a captured member call and inside a rebuilt loop carries the run's token.
            Assert.Equal("cancelled", (await InvocationRouteCorpus.Observe(InvocationRouteCorpus.ById("X8"), mode)).Outcome);
            Assert.Equal("cancelled", (await InvocationRouteCorpus.Observe(InvocationRouteCorpus.ById("X8b"), mode)).Outcome);
        }
    }
}
