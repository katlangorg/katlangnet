using System.Numerics;
using System.Reflection;
using System.Text;
using KatLang.Evaluation;

namespace KatLang.Tests;

/// <summary>
/// 2.06: the elaboration passes observe the source-processing cancellation token in bounded blocks of
/// work (<see cref="FrontEndTraversalObservations.ObserveCancellation"/>): per algorithm and per property
/// or output row in detection and resolution, per algorithm in the completed-signature validators, and per
/// algorithm level, level-equation evaluation, settlement frame and summary-channel unit in exposure.
/// Before, a host that cancelled while exposure settled an opened chain waited for the whole pass (about
/// 48 s for 5,000 links in Release); see <c>docs/design/language-rules/evaluator-and-hosting.md</c>
/// § Budgets and cancellation.
///
/// <para>Every cancellation here is placed deterministically by the checkpoint hook
/// (<see cref="FrontEndTraversalObservations.CheckpointReached"/>), which runs BEFORE the token is read, so
/// the cancelling checkpoint itself observes the cancellation and the block it starts never runs. Tests
/// assert outcomes, token identity and counts, never elapsed time. Host-only policy: Lean has no
/// cancellation, so no Lean case corresponds.</para>
/// </summary>
public sealed class FrontEndCancellationCheckpointTests
{
    private const int ChainLength = 64;
    private const int CancellingOrdinal = 100;

    private static string Chain(int length = ChainLength)
        => ExposureOpenChainComplexityTests.NestedOwnerChain(length, last: "p");

    /// <summary>A copy of <c>FrontEndElaborationScenarios.BuildWidePropertiesSource</c> (benchmarks).</summary>
    private static string WideProperties(int count = 400)
    {
        var source = new StringBuilder();
        for (var i = 0; i < count; i++)
        {
            source.AppendLine($"W{i}(y{i}) = {{");
            source.AppendLine($"Inner{i} = y{i} * 2");
            source.AppendLine($"Inner{i} + 1");
            source.AppendLine("}");
        }

        source.AppendLine($"W{count - 1}(3)");
        return source.ToString();
    }

    private static string Source(string shape) => shape switch
    {
        "chain" => Chain(),
        "wide" => WideProperties(),
        _ => throw new ArgumentOutOfRangeException(nameof(shape)),
    };

    /// <summary>An observer whose hook cancels <paramref name="source"/> at the <paramref name="ordinal"/>-th checkpoint of <paramref name="kind"/>.</summary>
    private sealed class CancelAt
    {
        public readonly FrontEndTraversalObservations Observations;
        public long CheckpointsAtCancel = -1;
        public long SettlementFramesAtCancel = -1;
        public SortedDictionary<string, long>? CountersAtCancel;
        public bool Armed = true;
        public long Offset;

        public CancelAt(CancellationTokenSource source, FrontEndCancellationCheckpoint kind, long ordinal)
        {
            FrontEndTraversalObservations observations = null!;
            observations = new FrontEndTraversalObservations
            {
                CheckpointReached = (reached, reachedOrdinal) =>
                {
                    if (!Armed || reached != kind || reachedOrdinal != Offset + ordinal || source.IsCancellationRequested)
                        return;
                    CheckpointsAtCancel = observations.CancellationCheckpoints;
                    SettlementFramesAtCancel = observations.RequiredAncestorSettlementFrames;
                    CountersAtCancel = Counters(observations);
                    source.Cancel();
                },
            };
            Observations = observations;
        }
    }

    /// <summary>The elaborated tree (Lean encoding), every property's exposure facts, and the diagnostics.</summary>
    private static string Snapshot(ParseResult result)
    {
        var text = new StringBuilder(LeanAstEncoder.EncodeProgram(result.Root)).Append('\n');
        new ExposureWalker(text).VisitAlgorithm(result.Root);
        foreach (var diagnostic in result.Diagnostics)
            text.Append('\n').Append(diagnostic.Code).Append(' ').Append(diagnostic.Span).Append(' ').Append(diagnostic.Message);
        return text.ToString();
    }

    private sealed class ExposureWalker(StringBuilder text) : AstWalker
    {
        private readonly HashSet<object> _seen = new(ReferenceEqualityComparer.Instance);

        public override void VisitAlgorithm(Algorithm algorithm)
        {
            if (_seen.Add(algorithm)) base.VisitAlgorithm(algorithm);
        }

        protected override void VisitProperty(Property property)
        {
            text.Append(property.Name).Append(':').Append(property.Exposure).Append('[')
                .AppendJoin(',', property.RequiredAncestorParameters).Append("][")
                .AppendJoin(',', (property.CaptureRequirements ?? []).Select(c => $"{c.Name}@{c.OwnerDepth}")).Append("];");
            base.VisitProperty(property);
        }
    }

    /// <summary>
    /// Every public counter of an observer, by name (the new checkpoint counter included).
    /// <see cref="FrontEndTraversalObservations.SummaryKeyCharacters"/> is among them: it counts each process-global id
    /// inside a key (<c>OwnerQualifiedParameter.OwnerKey</c>, an incrementing id) as one character, so its value no
    /// longer depends on how many ids the process issued before and two runs of one input agree on it.
    /// </summary>
    private static SortedDictionary<string, long> Counters(FrontEndTraversalObservations observations)
    {
        var counters = new SortedDictionary<string, long>(StringComparer.Ordinal);
        foreach (var property in typeof(FrontEndTraversalObservations).GetProperties(BindingFlags.Instance | BindingFlags.Public))
            if (property.PropertyType == typeof(long) || property.PropertyType == typeof(int))
                counters[property.Name] = Convert.ToInt64(property.GetValue(observations));
        counters["StaticQueryEvaluations.Distinct"] = observations.StaticQueryEvaluations.Count;
        counters["StaticQueryEvaluations.Total"] = observations.StaticQueryEvaluations.Values.Sum();
        counters["StaticQueryAnswers"] = observations.StaticQueryAnswers.Count;
        counters["CompletedStaticStructureReads"] = observations.CompletedStaticStructureReads;
        foreach (var kind in Enum.GetValues<FrontEndCancellationCheckpoint>())
            counters["Checkpoints." + kind] = observations.CancellationCheckpointsOf(kind);
        return counters;
    }

    private static void AssertSameCounters(FrontEndTraversalObservations expected, FrontEndTraversalObservations actual)
        => AssertSameCounters(Counters(expected), Counters(actual));

    /// <summary>
    /// Nothing ran after the cancelling checkpoint: every counter stands where the hook saw it. The hook runs before
    /// the token is read, so the checkpoint that cancels also throws; a hook run after the read would let the block
    /// it guards run first, and that block records work (a frame, an evaluation, a set operation).
    /// </summary>
    private static void AssertNothingAfterTheCancellingCheckpoint(CancelAt cancel)
    {
        Assert.NotNull(cancel.CountersAtCancel);
        AssertSameCounters(cancel.CountersAtCancel, Counters(cancel.Observations));
    }

    private static void AssertSameCounters(SortedDictionary<string, long> left, SortedDictionary<string, long> right)
    {
        var differing = left.Where(pair => right[pair.Key] != pair.Value).Select(pair => $"{pair.Key}: {pair.Value} vs {right[pair.Key]}").ToList();
        Assert.True(differing.Count == 0, string.Join("; ", differing));
    }

    /// <summary>The chain through the internal pass helpers, its operation owning <paramref name="token"/>.</summary>
    private static (Algorithm Resolved, StaticStructureOperation Operation) Resolved(string source, CancellationToken token)
    {
        var syntax = SourceProvenance.ParseSyntaxValidRoot(source);
        var operation = StaticStructureAdmission.Create(syntax, cancellationToken: token).Operation;
        var detected = ParameterDetector.DetectPrevalidated(syntax, structuralOperation: operation);
        Assert.Empty(detected.Diagnostics);
        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations: null, diagnostics);
        Assert.Empty(diagnostics);
        return (resolved, operation);
    }

    private static void AssertChainClassification(Algorithm root, int length = ChainLength)
    {
        var owner = ExposureOpenChainComplexityTests.Member(root, "O").Value;
        for (var i = 1; i <= length; i++)
        {
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, $"P{i}"));
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, $"P{i}", $"A{i}"), ("p", 1));
        }

        ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(owner, "R"), ("p", 0));
    }

    // ── 1. Exposure settlement ───────────────────────────────────────────────

    /// <remarks>
    /// With <paramref name="operationOwnsToken"/> (the pipeline's arrangement) the static-query reads inside a frame's
    /// body observe the token as well; without it only the exposure pass's own checkpoints do. A reference frame's
    /// first block only pushes its published frame, which records nothing, so the rows after ordinal 100
    /// cancel at a published frame's checkpoint (101, 2, 1001): its block settles through counted seed frames, so a
    /// hook placed after the token read would let that block run and change a counter.
    /// </remarks>
    [Theory]
    [InlineData(CancellingOrdinal, true)]
    [InlineData(CancellingOrdinal + 1, true)]
    [InlineData(CancellingOrdinal + 1, false)]
    [InlineData(2, false)]
    [InlineData(1001, false)]
    public void ExposureSettlement_CancelledAtAFrame_StopsBeforeThatFrameRuns_AndPublishesNothing(long ordinal, bool operationOwnsToken)
    {
        using var cancellation = new CancellationTokenSource();
        var (resolved, _) = Resolved(Chain(), operationOwnsToken ? cancellation.Token : CancellationToken.None);
        var cancel = new CancelAt(cancellation, FrontEndCancellationCheckpoint.ExposureSettlementFrame, ordinal);

        var error = Assert.Throws<OperationCanceledException>(
            () => PropertyExposureResolver.Resolve(resolved, cancel.Observations, cancellationToken: cancellation.Token));

        Assert.Equal(cancellation.Token, error.CancellationToken);
        // The cancelling checkpoint observed the cancellation: the frame it guards never ran, so no frame
        // and no checkpoint followed (a hook placed after the token read would admit one more of each).
        Assert.Equal(ordinal, cancel.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.ExposureSettlementFrame));
        Assert.Equal(cancel.CheckpointsAtCancel, cancel.Observations.CancellationCheckpoints);
        AssertNothingAfterTheCancellingCheckpoint(cancel);
        Assert.Equal(cancel.SettlementFramesAtCancel, cancel.Observations.RequiredAncestorSettlementFrames);
        // The unfinished unit's publication is rejected, never sealed (PropertyExposureResolver.Resolve).
        var facts = Assert.IsType<CompletedStaticStructures>(resolved.CompletedStructure!.Facts);
        Assert.False(facts.IsSealed);
        Assert.True(facts.IsFailed);

        // A fresh elaboration classifies the chain exactly as ExposureOpenChainComplexityTests pins it.
        var fresh = new FrontEndTraversalObservations();
        AssertChainClassification(ExposureOpenChainComplexityTests.Exposed(Chain(), fresh));
        Assert.InRange(fresh.RequiredAncestorSettlementFrames, ordinal + 1, (long)ChainLength * (ChainLength + 3));
    }

    [Theory]
    [InlineData("ExposureAlgorithm", 3)]
    [InlineData("ExposureLevelEvaluation", 10)]
    [InlineData("SummaryChannel", 10)]
    public void ExposurePass_CancelledAtAnyOfItsUnits_EscapesWithTheToken_AndNoLaterCheckpoint(string kindName, long ordinal)
    {
        var kind = Enum.Parse<FrontEndCancellationCheckpoint>(kindName);
        using var cancellation = new CancellationTokenSource();
        var (resolved, _) = Resolved(Chain(), cancellation.Token);
        var cancel = new CancelAt(cancellation, kind, ordinal);

        var error = Assert.Throws<OperationCanceledException>(
            () => PropertyExposureResolver.Resolve(resolved, cancel.Observations, cancellationToken: cancellation.Token));

        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal(ordinal, cancel.Observations.CancellationCheckpointsOf(kind));
        Assert.Equal(cancel.CheckpointsAtCancel, cancel.Observations.CancellationCheckpoints);
        AssertNothingAfterTheCancellingCheckpoint(cancel);
        Assert.True(resolved.CompletedStructure!.Facts is CompletedStaticStructures { IsSealed: false, IsFailed: true });
    }

    // ── 2. Detection, resolution and the validators ──────────────────────────

    [Theory]
    [InlineData("DetectorAlgorithm")]
    [InlineData("DetectorRow")]
    [InlineData("ResolverAlgorithm")]
    [InlineData("ResolverRow")]
    [InlineData("WalkerAlgorithm")]
    [InlineData("ExposureAlgorithm")]
    public void WideProperties_CancelledInsideAPass_StopsAtTheCancellingCheckpoint_AndLeavesNoState(string kindName)
    {
        const long Ordinal = 50;
        var kind = Enum.Parse<FrontEndCancellationCheckpoint>(kindName);
        var source = WideProperties();
        var uncancelled = Snapshot(Parser.Parse(source));
        using var cancellation = new CancellationTokenSource();
        var cancel = new CancelAt(cancellation, kind, Ordinal);

        var error = Assert.Throws<OperationCanceledException>(() => Parser.ParseObserved(
            source, new RunOptions { SourceProcessingCancellationToken = cancellation.Token }, cancel.Observations));

        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal(Ordinal, cancel.Observations.CancellationCheckpointsOf(kind));
        Assert.Equal(cancel.CheckpointsAtCancel, cancel.Observations.CancellationCheckpoints);
        AssertNothingAfterTheCancellingCheckpoint(cancel);
        // Nothing the cancelled run touched survives in shared state (the prelude, the module registry,
        // the builtin scopes): a fresh parse is the uncancelled one.
        Assert.Equal(uncancelled, Snapshot(Parser.Parse(source)));
        Assert.Equal(uncancelled, Snapshot(SourceProvenance.ParseValid(source).Parsed));
    }

    // ── 3. Public route parity ──────────────────────────────────────────────

    [Fact]
    public async Task ParseAndParseAsync_CancelledFromTheHook_StopAtTheSameCheckpoint_WithTheSourceToken()
    {
        var source = Chain();
        using var syncCancellation = new CancellationTokenSource();
        var sync = new CancelAt(syncCancellation, FrontEndCancellationCheckpoint.ExposureSettlementFrame, CancellingOrdinal);
        var syncError = Assert.Throws<OperationCanceledException>(() => Parser.ParseObserved(
            source, new RunOptions { SourceProcessingCancellationToken = syncCancellation.Token }, sync.Observations));
        Assert.Equal(syncCancellation.Token, syncError.CancellationToken);
        AssertNothingAfterTheCancellingCheckpoint(sync);

        using var asyncCancellation = new CancellationTokenSource();
        var asynchronous = new CancelAt(asyncCancellation, FrontEndCancellationCheckpoint.ExposureSettlementFrame, CancellingOrdinal);
        var task = Parser.ParseObservedAsync(
            source, new RunOptions { SourceProcessingCancellationToken = asyncCancellation.Token }, asynchronous.Observations);
        // No downloader: the async front end runs inline and delivers the cancellation through the task.
        Assert.True(task.IsCanceled);
        var asyncError = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => task);
        Assert.Equal(asyncCancellation.Token, asyncError.CancellationToken);
        AssertNothingAfterTheCancellingCheckpoint(asynchronous);

        AssertSameCounters(sync.Observations, asynchronous.Observations);
        Assert.Equal(sync.CheckpointsAtCancel, asynchronous.Observations.CancellationCheckpoints);

        // Uncancelled, the two routes reach the same checkpoints and the same result.
        var syncObserved = new FrontEndTraversalObservations();
        var asyncObserved = new FrontEndTraversalObservations();
        var syncResult = Parser.ParseObserved(source, options: null, syncObserved);
        var asyncResult = await Parser.ParseObservedAsync(source, options: null, asyncObserved);
        Assert.Equal(Snapshot(syncResult), Snapshot(asyncResult));
        AssertSameCounters(syncObserved, asyncObserved);
        Assert.True(syncObserved.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.ExposureSettlementFrame) > CancellingOrdinal);
    }

    // ── 4. Deferred branch ──────────────────────────────────────────────────

    private const string ModuleUrl = "https://katlang.org/lazy/chain.kat";
    private const string DeferredProgram = $"F(0) = 0\nF(1) = {{\n    N = load('{ModuleUrl}')\n    N.V\n}}\nF(1)";
    private static readonly TimeSpan HangGuard = TimeSpan.FromSeconds(60);

    /// <summary>
    /// Runs an evaluation on a 64 MiB thread: the async evaluation family's frames are larger than the sync ones, and a
    /// 64-link chain read through opens nests deeper than a test-runner thread allows. The downloader completes
    /// synchronously, so the whole run — materialization included — stays on that thread.
    /// </summary>
    private static Task<T> OnLargeStack<T>(Func<Task<T>> run)
    {
        var completion = new TaskCompletionSource<T>(TaskCreationOptions.RunContinuationsAsynchronously);
        var thread = new Thread(() =>
        {
            try { completion.SetResult(run().WaitAsync(HangGuard).GetAwaiter().GetResult()); }
            catch (OperationCanceledException error) { completion.SetCanceled(error.CancellationToken); }
            catch (Exception error) { completion.SetException(error); }
        }, 64 * 1024 * 1024);
        thread.Start();
        return completion.Task;
    }

    private static string ChainModule()
        => ExposureOpenChainComplexityTests.NestedOwnerChain(ChainLength, last: "p", call: "") + "public V = O(1)";

    [Theory]
    [InlineData("evaluation")]
    [InlineData("source")]
    public async Task DeferredBranch_CancelledInsideItsExposure_PublishesNothing_AndALaterEvaluationMaterializes(string cancelled)
    {
        using var sourceCancellation = new CancellationTokenSource();
        using var evaluationCancellation = new CancellationTokenSource();
        var trigger = cancelled == "source" ? sourceCancellation : evaluationCancellation;
        var downloads = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) =>
            {
                Interlocked.Increment(ref downloads);
                return ValueTask.FromResult(ChainModule());
            },
            SourceProcessingCancellationToken = sourceCancellation.Token,
        };
        var cancel = new CancelAt(trigger, FrontEndCancellationCheckpoint.ExposureSettlementFrame, CancellingOrdinal) { Armed = false };
        var parsed = await Parser.ParseObservedAsync(DeferredProgram, options, cancel.Observations);
        Assert.Empty(parsed.Diagnostics);
        var root = parsed.Root;
        var family = Assert.IsType<Algorithm.Conditional>(root.Properties.Single(property => property.Name == "F").Value);
        var region = family.Branches[1].Body.DeferredRegion;
        Assert.NotNull(region);
        Assert.Equal(0, downloads);

        // Armed only for the materialization: its settlement frames come after the eager parse's.
        cancel.Offset = cancel.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.ExposureSettlementFrame);
        cancel.Armed = true;
        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(
            () => OnLargeStack(() => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), limits: null, evaluationCancellation.Token)));

        Assert.Equal(trigger.Token, error.CancellationToken);
        Assert.True(cancel.CheckpointsAtCancel > 0, "the cancellation was never placed inside the deferred exposure");
        Assert.Equal(cancel.CheckpointsAtCancel, cancel.Observations.CancellationCheckpoints);
        AssertNothingAfterTheCancellingCheckpoint(cancel);
        Assert.False(region.IsMaterialized);
        Assert.Equal(1, region.MaterializationAttempts);
        Assert.Equal(0, region.Loader.InProgressModuleCount);

        if (cancelled == "source")
            return; // the host's source token stays authoritative for every later materialization

        cancel.Armed = false;
        var retry = await OnLargeStack(() => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), limits: null, CancellationToken.None));
        Assert.False(retry.IsError, retry.IsError ? retry.Error.ToString() : "");
        Assert.Equal(new[] { (Decimal128)ChainLength }, retry.Value);
        Assert.True(region.IsMaterialized);
        Assert.Equal(2, region.MaterializationAttempts);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ProvenanceFinalizer_CancellationRejectsOnlyThisUnfinishedExposure(bool previouslySealed)
    {
        const string source = "Lib = { public Double(x) = x * 2 }\nUse = Lib.Dubel(4)\nUse";
        var expected = Snapshot(SourceProvenance.ParseValid(source).Parsed);
        using var cancellation = new CancellationTokenSource();
        var resolved = previouslySealed
            ? SourceProvenance.ParseValid(source).Root
            : Resolved(source, cancellation.Token).Resolved;
        var facts = Assert.IsType<CompletedStaticStructures>(resolved.CompletedStructure!.Facts);
        Assert.Equal(previouslySealed, facts.IsSealed);
        var cancel = new CancelAt(cancellation, FrontEndCancellationCheckpoint.WalkerAlgorithm, 1);

        var error = Assert.Throws<OperationCanceledException>(
            () => PropertyExposureResolver.Resolve(resolved, cancel.Observations, cancellationToken: cancellation.Token));

        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal(1, cancel.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.WalkerAlgorithm));
        AssertNothingAfterTheCancellingCheckpoint(cancel);
        if (previouslySealed)
        {
            // A completed foreign publication survives a later consumer's cancellation.
            Assert.False(facts.IsFailed);
            facts.EnsureUsable();
        }
        else
        {
            // Structural sealing precedes provenance finalization. Cancelling that last walk still
            // aborts this exposure unit; its facts must not become a successful publication.
            Assert.True(facts.IsFailed);
            Assert.Throws<InvalidOperationException>(facts.EnsureUsable);
        }

        Assert.Equal(expected, Snapshot(SourceProvenance.ParseValid(source).Parsed));
    }

    // ── 5. Uncancelled runs ─────────────────────────────────────────────────

    [Theory]
    [InlineData("chain")]
    [InlineData("wide")]
    public void LiveNeverCancelledToken_ChangesNoTreeDiagnosticOrCounter(string shape)
    {
        var source = Source(shape);
        var tokenless = new FrontEndTraversalObservations();
        var tokenlessResult = Parser.ParseObserved(source, options: null, tokenless);
        using var live = new CancellationTokenSource();
        var observed = new FrontEndTraversalObservations();
        var liveResult = Parser.ParseObserved(source, new RunOptions { SourceProcessingCancellationToken = live.Token }, observed);

        Assert.Equal(Snapshot(tokenlessResult), Snapshot(liveResult));
        Assert.Equal(Snapshot(Parser.Parse(source)), Snapshot(liveResult));
        AssertSameCounters(tokenless, observed);
        Assert.True(observed.CancellationCheckpoints > 0);
        Assert.True(observed.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.DetectorAlgorithm) > 0);
        Assert.True(observed.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.ResolverAlgorithm) > 0);
        Assert.True(observed.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.WalkerAlgorithm) > 0);
        Assert.True(observed.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.ExposureAlgorithm) > 0);
    }

    [Fact]
    public void ExposureWithALiveToken_ChargesTheLedgerAndCountersExactlyAsWithout()
    {
        using var live = new CancellationTokenSource();
        var (withToken, withOperation) = Resolved(Chain(), live.Token);
        var (without, withoutOperation) = Resolved(Chain(), CancellationToken.None);
        var observedWith = new FrontEndTraversalObservations();
        var observedWithout = new FrontEndTraversalObservations();

        var exposedWith = PropertyExposureResolver.Resolve(withToken, observedWith, cancellationToken: live.Token);
        var exposedWithout = PropertyExposureResolver.Resolve(without, observedWithout);

        Assert.Equal(LeanAstEncoder.EncodeProgram(exposedWithout), LeanAstEncoder.EncodeProgram(exposedWith));
        AssertChainClassification(exposedWith);
        AssertSameCounters(observedWithout, observedWith);
        var a = withOperation.Queries.Resources;
        var b = withoutOperation.Queries.Resources;
        Assert.Equal((b.AdapterWork, b.MetadataUnits, b.PeakStorageUnits, b.StorageUnits, b.IsFailed),
            (a.AdapterWork, a.MetadataUnits, a.PeakStorageUnits, a.StorageUnits, a.IsFailed));
        Assert.InRange(observedWith.RequiredAncestorSettlementFrames, 1, (long)ChainLength * (ChainLength + 3));
        Assert.True(observedWith.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.ExposureSettlementFrame) >= CancellingOrdinal);
    }
}
