using System.Text;

namespace KatLang.Tests;

/// <summary>
/// SETTLEMENT FRAME CHARGE (<see cref="PropertyExposureResolver.SettlementFrameWork"/>; C#-only host resource policy,
/// no classification or Lean rule): every settlement frame of the exposure pass costs the operation that admitted the
/// unit one unit of static work, so a program whose settlement outgrows its source is refused with one unpositioned
/// <see cref="DiagnosticCode.StaticStructureLimitExceeded"/> instead of running unmetered.
///
/// <para>The shapes. A member chain whose links own a parameter binds one more owner at every link, so no exact
/// settlement key repeats; no link reads those owners, so the share answers each walk by its footprint
/// (<see cref="ExposureSettlementFootprintTests"/>): 4D − 4 frames on the audit's reproduction,
/// <c>P{i} = { public A(x) = P{i-1}.A(1) + 1 }</c>, and 8D − 12 for <see cref="BranchingChain"/>, whose links read TWO
/// members below (formerly D² and exponential: 17,639 frames at 16 links, refused from 25). The feasible witness of a
/// refusal under the unlowered work bound is now the branching chain inside seventeen nested owners whose parameters
/// its first member reads (<see cref="ExposureSettlementFootprintTests.NestedOwnerBranchingChain"/>): one more owner
/// than a footprint records, so its settlements answer their exact bound owners only and the frames grow
/// exponentially again (9,504 at 16 links, refused from 24).</para>
///
/// <para>The work bound is operation-scaled (<see cref="StaticStructureAdmission"/>: 16,384 + 1,024 per admitted node
/// and edge) and does not move with <see cref="SourceProcessingLimits.MaxStaticStructureBytes"/>: a lowered envelope
/// can refuse a long chain through its own entry and storage caps (before settlement begins when the chain is far
/// past them). Envelopes large enough to admit the work-bound threshold still refuse through the frame charge.</para>
///
/// <para>The oracle is the ledger and deterministic work, never elapsed time.</para>
/// </summary>
public sealed class ExposureSettlementFrameChargeTests
{
    private const string ModuleHost = "modules.example";

    private static string Chain(int length, string argument = "1")
        => ExposureSettlementShareTests.ExplicitParameterMemberChain(length, argument);

    /// <summary>The member lines of a chain whose links each call the members of the TWO links below.</summary>
    private static string BranchingLines(int length, string indent = "")
    {
        var source = new StringBuilder();
        source.Append(indent).Append("P0 = { public A(x) = x + 1 }\n");
        source.Append(indent).Append("P1 = { public A(x) = P0.A(1) + 1 }\n");
        for (var i = 2; i <= length; i++)
            source.Append(indent).Append($"P{i} = {{ public A(x) = P{i - 1}.A(1) + P{i - 2}.A(1) }}\n");
        return source.ToString();
    }

    private static string BranchingChain(int length) => BranchingLines(length) + "0\n";

    private static RunOptions Envelope(long bytes) => new() { SourceProcessingLimits = new() { MaxStaticStructureBytes = bytes } };

    /// <summary>
    /// Detection and resolution of <paramref name="source"/> in an operation admitted exactly as the pipeline admits it
    /// (<see cref="StaticStructureAdmission.Create"/>), with its limits passed through <paramref name="bound"/>: the
    /// resolved root carries that operation's unsealed unit, and exposure charges its ledger.
    /// </summary>
    internal static (Algorithm Resolved, StaticQueryResourceBudget Ledger, StaticQueryLimits Limits) Resolved(
        string source, Func<StaticQueryLimits, StaticQueryLimits>? bound = null)
    {
        var syntax = SourceProvenance.ParseSyntaxValidRoot(source);
        var prelude = BuiltinRegistry.SharedSemanticPreludeAlgorithm;
        var measurement = StaticStructureAdmission.Measure(syntax, prelude);
        var limits = bound?.Invoke(measurement.Limits) ?? measurement.Limits;
        var operation = new StaticStructureOperation(syntax, limits, prelude)
        {
            AdmittedWithoutOpens = !measurement.HasOpens,
            AdmittedWithOutputSpreadMarkers = measurement.HasOutputSpreadMarkers,
        };
        var detected = ParameterDetector.DetectPrevalidated(syntax, structuralOperation: operation);
        Assert.Empty(detected.Diagnostics);
        var diagnostics = new DiagnosticBag();
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations: null, diagnostics);
        Assert.Empty(diagnostics);
        return (resolved, operation.Queries.Resources, limits);
    }

    /// <summary>Every property's exposure metadata, by path, in declaration order.</summary>
    internal static string Metadata(Algorithm root)
    {
        var lines = new StringBuilder();
        var pending = new Stack<(string Path, Algorithm Body)>();
        pending.Push(("", root));
        while (pending.TryPop(out var at))
        {
            for (var index = at.Body.Properties.Count - 1; index >= 0; index--)
            {
                var property = at.Body.Properties[index];
                var path = at.Path + "." + property.Name;
                lines.Append(path).Append('|').Append(property.Exposure)
                    .Append('|').AppendJoin(',', property.RequiredAncestorParameters)
                    .Append('|').AppendJoin(',', (property.CaptureRequirements ?? []).Select(capture => $"{capture.Name}@{capture.OwnerDepth}"))
                    .Append('\n');
                pending.Push((path, property.Value));
            }
        }

        return lines.ToString();
    }

    private static void AssertEveryMemberExported(Algorithm root, int length)
    {
        for (var i = 0; i <= length; i++)
        {
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, $"P{i}"));
            ExposureOpenChainComplexityTests.AssertRequires(ExposureOpenChainComplexityTests.Member(root, $"P{i}", "A"));
        }
    }

    /// <summary>
    /// The work-bound refusal's own last sentence: the bound does not move with the envelope, so the envelope
    /// sentence ("a host may only lower it") would misstate the remedy.
    /// </summary>
    internal const string WorkBoundSentence =
        "This bound scales with the size of the analyzed program (16,384 + 1,024 per node and edge) rather than with the host's static-structure envelope, so no envelope setting raises or lowers it.";

    /// <summary>The complete text of a work-bound refusal under <paramref name="bound"/>.</summary>
    internal static string WorkBoundRefusal(long bound)
        => $"Static structure analysis exceeded its resource bound. The static operation exceeded its work bound ({bound}). {WorkBoundSentence}";

    private static void AssertOneUnpositionedWorkBoundRefusal(ParseResult refused)
    {
        var refusal = Assert.Single(refused.Diagnostics);
        Assert.Equal(DiagnosticCode.StaticStructureLimitExceeded, refusal.Code);
        Assert.Equal(DiagnosticSeverity.Error, refusal.Severity);
        Assert.Null(refusal.Span);
        Assert.Contains("exceeded its work bound", refusal.Message, StringComparison.Ordinal);
        Assert.Matches(@"^Static structure analysis exceeded its resource bound\. The static operation exceeded its work bound \(\d+\)\. ", refusal.Message);
        Assert.EndsWith(" " + WorkBoundSentence, refusal.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("may only lower it", refusal.Message, StringComparison.Ordinal);
        Assert.True(refused.HasErrors);
        // Nothing is published: an unevaluable placeholder root with no completed structure.
        Assert.Empty(refused.Root.Properties);
        Assert.Null(refused.Root.CompletedStructure);
    }

    // ── 1. One unit per frame, on the operation's ledger ────────────────────────────────────────────

    /// <summary>
    /// The ledger's work rises by exactly <see cref="PropertyExposureResolver.SettlementFrameWork"/> at every frame,
    /// before the frame is counted, whatever the shape: the residual chains the share cannot serve, a chain it serves
    /// in linear frames, a captured terminal, and the reuse shapes of November 2026. Besides its frames, settlement charges
    /// only what it counts as reuse work (2026-11-25): one unit per live summary a kept settlement's reuse compares
    /// (<see cref="FrontEndTraversalObservations.SettlementLiveReadChecks"/>), one per name snapshotted, one per seed part
    /// examined or name a kept part set is built from (<see cref="FrontEndTraversalObservations.SettlementSeedPartWork"/>),
    /// and one per entry a live-read name interner creates
    /// (<see cref="FrontEndTraversalObservations.SettlementLiveNameEntries"/>). So the work at every frame, and at the last
    /// one, is the work before exposure plus the frames and those counts.
    /// </summary>
    [Theory]
    [InlineData("explicit-parameter")]
    [InlineData("explicit-parameter-read")]
    [InlineData("branching")]
    [InlineData("opened")]
    [InlineData("captured")]
    [InlineData("component")]
    [InlineData("live-open-walks")]
    [InlineData("live-member")]
    [InlineData("live-overlapping")]
    [InlineData("seed-parts")]
    public void EveryFrame_ChargesOneUnitOfTheOperationsWork_BeforeItIsCounted(string shape)
    {
        var source = shape switch
        {
            "explicit-parameter" => Chain(96),
            "explicit-parameter-read" => Chain(96, "x"),
            "branching" => BranchingChain(12),
            "opened" => ExposureOpenChainComplexityTests.NestedOwnerChain(128),
            "captured" => ExposureOpenChainComplexityTests.NestedOwnerChain(128, last: "p"),
            "component" => ExposureSettlementComponentTests.ReportWitness,
            "live-open-walks" => ExposureResidualReuseTests.LiveOpenFamily(24, 24),
            "live-member" => ExposureResidualReuseTests.LiveMemberFamily(24, 24),
            "live-overlapping" => ExposureResidualReuseTests.OverlappingLiveReads(24, 12),
            "seed-parts" => ExposureResidualReuseTests.NavigatedChain(48, depth: 2),
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        };
        var (resolved, ledger, limits) = Resolved(source);
        var before = ledger.WorkCharged;
        var observations = new FrontEndTraversalObservations();
        long seen = 0;
        long firstMismatch = 0;
        long Reuse() => observations.SettlementLiveReadChecks + observations.SettlementSnapshotNames + observations.SettlementSeedPartWork
            + observations.SettlementLiveNameEntries;
        observations.RequiredAncestorSettlementObserver = _ =>
        {
            seen++;
            if (firstMismatch == 0 && ledger.WorkCharged != before + seen * PropertyExposureResolver.SettlementFrameWork + Reuse())
                firstMismatch = seen;
        };

        _ = PropertyExposureResolver.Resolve(resolved, observations);

        Assert.Equal(0, firstMismatch);
        Assert.True(seen > 0);
        Assert.Equal(seen, observations.RequiredAncestorSettlementFrames);
        if (shape.StartsWith("live", StringComparison.Ordinal))
            Assert.True(observations.SettlementLiveNameEntries > 0);
        if (shape is "live-open-walks" or "live-member")
        {
            Assert.True(observations.SettlementLiveReadChecks > 0);
            Assert.True(observations.SettlementSnapshotNames > 0);
        }
        if (shape == "seed-parts")
            Assert.True(observations.SettlementSeedPartWork > 0);
        // What follows the last frame is the unit's retargeting and sealing, charged as before.
        Assert.InRange(ledger.WorkCharged, before + seen * PropertyExposureResolver.SettlementFrameWork + Reuse(), limits.MaxEvaluations);
        Assert.False(ledger.IsFailed);
    }

    /// <summary>
    /// The charge is a function of the source alone: two elaborations charge the same work and count the same frames,
    /// and a live source-processing token changes neither (the charge observes no token and is no checkpoint).
    /// </summary>
    [Fact]
    public void TheCharge_IsDeterministic_AndObservesNoToken()
    {
        foreach (var source in new[] { Chain(64), BranchingChain(10), ExposureOpenChainComplexityTests.NestedOwnerChain(48, last: "p") })
        {
            (long Work, long Frames, long Checkpoints, string Metadata) Run(CancellationToken token)
            {
                var (resolved, ledger, _) = Resolved(source);
                var observations = new FrontEndTraversalObservations();
                var exposed = PropertyExposureResolver.Resolve(resolved, observations, cancellationToken: token);
                return (ledger.WorkCharged, observations.RequiredAncestorSettlementFrames,
                    observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.ExposureSettlementFrame), Metadata(exposed));
            }

            using var live = new CancellationTokenSource();
            var first = Run(CancellationToken.None);
            Assert.Equal(first, Run(CancellationToken.None));
            Assert.Equal(first, Run(live.Token));
            Assert.True(first.Frames > 0);
        }
    }

    // ── 2. The work bound refuses the first frame beyond it ─────────────────────────────────────────

    /// <summary>
    /// The audit's reproduction at 64 links takes 252 frames (4D − 4; 4,096 before footprints). Under a work bound that
    /// leaves room for exactly k of them, k frames are admitted and the next is refused before it is counted or
    /// settled: the ledger fails at the bound, and the unit is rejected unsealed, so nothing can be published from it.
    /// </summary>
    [Fact]
    public void AWorkBoundTheFramesExceed_RefusesTheFirstFrameBeyondIt_AndPublishesNothing()
    {
        const int Length = 64;
        var source = Chain(Length);
        var funded = Resolved(source);
        var before = funded.Ledger.WorkCharged;
        var fundedObservations = new FrontEndTraversalObservations();
        _ = PropertyExposureResolver.Resolve(funded.Resolved, fundedObservations);
        var frames = fundedObservations.RequiredAncestorSettlementFrames;
        Assert.Equal(4L * Length - 4, frames);

        foreach (var admitted in new[] { 0L, 1L, frames / 2, frames - 1 })
        {
            var tight = Resolved(source, limits => limits with { MaxEvaluations = before + admitted });
            Assert.Equal(before, tight.Ledger.WorkCharged);
            var observations = new FrontEndTraversalObservations();

            var error = Assert.Throws<StaticQueryLimitExceededException>(
                () => PropertyExposureResolver.Resolve(tight.Resolved, observations));

            Assert.Contains("exceeded its work bound", error.Message, StringComparison.Ordinal);
            Assert.Equal(admitted, observations.RequiredAncestorSettlementFrames);
            Assert.Equal(before + admitted, tight.Ledger.WorkCharged);
            Assert.True(tight.Ledger.IsFailed);
            var unit = tight.Resolved.CompletedStructure!.Facts;
            Assert.True(unit.IsFailed);
            Assert.False(unit.IsSealed);
            Assert.Throws<InvalidOperationException>(unit.EnsureUsable);
        }
    }

    /// <summary>
    /// The bound is inclusive and the admitted result does not depend on how much room was left: the exact work of the
    /// whole elaboration is admitted with the metadata of the unlowered run, and one unit less is refused.
    /// </summary>
    [Fact]
    public void TheExactWorkOfAnElaboration_IsAdmittedUnchanged_AndOneUnitLessIsRefused()
    {
        var source = Chain(64, "x");
        var funded = Resolved(source);
        var expected = Metadata(PropertyExposureResolver.Resolve(funded.Resolved, new FrontEndTraversalObservations()));
        var total = funded.Ledger.WorkCharged;

        var exact = Resolved(source, limits => limits with { MaxEvaluations = total });
        Assert.Equal(expected, Metadata(PropertyExposureResolver.Resolve(exact.Resolved, new FrontEndTraversalObservations())));
        Assert.Equal(total, exact.Ledger.WorkCharged);
        Assert.False(exact.Ledger.IsFailed);

        var shortOfIt = Resolved(source, limits => limits with { MaxEvaluations = total - 1 });
        Assert.Throws<StaticQueryLimitExceededException>(
            () => PropertyExposureResolver.Resolve(shortOfIt.Resolved, new FrontEndTraversalObservations()));
        Assert.True(shortOfIt.Ledger.IsFailed);
    }

    // ── 3. The source entries: eager parse and deferred materialization ─────────────────────────────

    /// <summary>
    /// EAGER PARSE, unlowered envelope. The branching chain elaborates in exactly 8D − 12 frames with every member
    /// exported, at twenty-five links too, which were refused before footprints (1,346,161 frames against a work bound
    /// near 910,000), and at 256.
    /// </summary>
    [Fact]
    public void ABranchingMemberChain_IsAdmittedInLinearFrames_UnderTheDefaultEnvelope()
    {
        foreach (var length in new[] { 16, 25, 64, 256 })
        {
            var observations = new FrontEndTraversalObservations();
            var admitted = Parser.ParseObserved(BranchingChain(length), options: null, observations);
            Assert.Empty(admitted.Diagnostics);
            AssertEveryMemberExported(admitted.Root, length);
            Assert.Equal(8L * length - 12, observations.RequiredAncestorSettlementFrames);
        }
    }

    /// <summary>
    /// EAGER PARSE, unlowered envelope, past the footprint bound: the branching chain inside seventeen nested owners
    /// elaborates at sixteen links (9,504 frames) and needs more frames than its work bound at twenty-four, so it is
    /// refused inside settlement with exactly one unpositioned <see cref="DiagnosticCode.StaticStructureLimitExceeded"/>
    /// naming that bound, and nothing is published. The frames admitted before the refusal stay within the bound the
    /// admission measured.
    /// </summary>
    [Fact]
    public void AnOverCapFootprintChain_IsRefusedByItsWorkBound_UnderTheDefaultEnvelope()
    {
        const int Admitted = 16;
        const int Refused = 24;
        var admittedObservations = new FrontEndTraversalObservations();
        var admitted = Parser.ParseObserved(ExposureSettlementFootprintTests.NestedOwnerBranchingChain(17, Admitted),
            options: null, admittedObservations);
        Assert.Empty(admitted.Diagnostics);
        Assert.InRange(admittedObservations.RequiredAncestorSettlementFrames, 1L << (Admitted / 2), 1L << (Admitted - 2));

        var source = ExposureSettlementFootprintTests.NestedOwnerBranchingChain(17, Refused);
        var bound = StaticStructureAdmission.Measure(SourceProvenance.ParseSyntaxValidRoot(source),
            BuiltinRegistry.SharedSemanticPreludeAlgorithm).Limits.MaxEvaluations;
        var observations = new FrontEndTraversalObservations();

        var refused = Parser.ParseObserved(source, options: null, observations);

        AssertOneUnpositionedWorkBoundRefusal(refused);
        Assert.Contains($"({bound})", Assert.Single(refused.Diagnostics).Message, StringComparison.Ordinal);
        // Refused INSIDE settlement: most of the bound went to frames, and none beyond it was counted.
        Assert.InRange(observations.RequiredAncestorSettlementFrames, bound / 2, bound);
    }

    /// <summary>
    /// The work bound does not move with the envelope: under a 4-MiB envelope the over-cap chain of twenty-four links
    /// is refused by the same bound, through the engine as a parse failure, while twenty-five branching links run.
    /// </summary>
    [Fact]
    public void ALoweredEnvelope_LeavesTheWorkBoundWhereItIs()
    {
        var options = Envelope(4L * 1024 * 1024);
        var source = ExposureSettlementFootprintTests.NestedOwnerBranchingChain(17, 24);
        var bound = StaticStructureAdmission.Measure(SourceProvenance.ParseSyntaxValidRoot(source),
            BuiltinRegistry.SharedSemanticPreludeAlgorithm, options.SourceProcessingLimits).Limits.MaxEvaluations;
        Assert.Equal(bound, StaticStructureAdmission.Measure(SourceProvenance.ParseSyntaxValidRoot(source),
            BuiltinRegistry.SharedSemanticPreludeAlgorithm).Limits.MaxEvaluations);

        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source, options));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.StaticStructureLimitExceeded, error.Code);
        Assert.Equal(WorkBoundRefusal(bound), error.Message);

        Assert.Equal("0", Assert.IsType<RunResult.Success>(KatLangEngine.Run(BranchingChain(25), options)).ToDisplayString());
    }

    /// <summary>
    /// The audit's chain under a lowered envelope (8 MiB). 256 links elaborate with exactly the metadata of the
    /// unlowered run and the same frames: the charge refuses nothing there, because the work bound is not the
    /// envelope's. 4,096 links are refused with exactly one <see cref="DiagnosticCode.StaticStructureLimitExceeded"/>,
    /// and by the envelope's own caps: the chain is far past them (8 MiB admits 440 links), so no settlement frame ran
    /// and this refusal is NOT the frame charge's (it predates it). The chain's 4D − 4 frames stay far below its work
    /// bound (16,384 + 1,024F for its F ≈ 20D admitted nodes and edges), so the frame charge no longer refuses it at
    /// any length an envelope admits.
    /// </summary>
    [Fact]
    public void UnderALoweredEnvelope_256LinksElaborateUnchanged_And4096AreRefusedBeforeSettlement()
    {
        var options = Envelope(8L * 1024 * 1024);
        var defaultObservations = new FrontEndTraversalObservations();
        var unlowered = Parser.ParseObserved(Chain(256), options: null, defaultObservations);
        Assert.Empty(unlowered.Diagnostics);
        var loweredObservations = new FrontEndTraversalObservations();

        var lowered = Parser.ParseObserved(Chain(256), options, loweredObservations);

        Assert.Empty(lowered.Diagnostics);
        AssertEveryMemberExported(lowered.Root, 256);
        Assert.Equal(Metadata(unlowered.Root), Metadata(lowered.Root));
        Assert.Equal(4L * 256 - 4, loweredObservations.RequiredAncestorSettlementFrames);
        Assert.Equal(defaultObservations.RequiredAncestorSettlementFrames, loweredObservations.RequiredAncestorSettlementFrames);

        var observations = new FrontEndTraversalObservations();
        var refused = Parser.ParseObserved(Chain(4096), options, observations);
        var refusal = Assert.Single(refused.Diagnostics);
        Assert.Equal(DiagnosticCode.StaticStructureLimitExceeded, refusal.Code);
        Assert.Null(refusal.Span);
        Assert.DoesNotContain("work bound", refusal.Message, StringComparison.Ordinal);
        Assert.EndsWith(" " + StaticStructureAdmission.EnvelopeSentence, refusal.Message, StringComparison.Ordinal);
        Assert.Equal(0, observations.RequiredAncestorSettlementFrames);
        Assert.Empty(refused.Root.Properties);
        Assert.Null(refused.Root.CompletedStructure);
    }

    private static RunOptions ModuleOptions()
        => new()
        {
            AllowedHosts = [ModuleHost],
            DownloadCode = (_, _) => ValueTask.FromResult("Z = 10\n0"),
        };

    /// <summary>
    /// <paramref name="lines"/> inside a branch body that loads a module: a deferred unit, compiled when <c>G(1)</c>
    /// selects it.
    /// </summary>
    private static string InADeferredUnit(string lines)
        => "G(0) = 0\nG(a) = {\n    M = load('https://" + ModuleHost + "/m.kat')\n" + lines + "    M.Z + a\n}\nG(1)";

    /// <summary>
    /// DEFERRED MATERIALIZATION charges its own operation: the eager parse admits both programs (the provisional branch
    /// body is not settled level by level); the selected branch's twenty-eight branching links, refused at
    /// materialization before footprints, now run; and the over-cap chain of twenty-four links is refused when the
    /// branch is materialized, with the structural resource error naming the work bound.
    /// </summary>
    [Fact]
    public async Task ABranchingChainInADeferredUnit_IsChargedToItsMaterialization()
    {
        var branching = InADeferredUnit(BranchingLines(28, "    "));
        var overCap = InADeferredUnit(ExposureSettlementFootprintTests.NestedOwnerBranchingDeclaration(17, 24, "    "));
        Assert.Empty((await Parser.ParseAsync(branching, ModuleOptions())).Diagnostics);
        Assert.Empty((await Parser.ParseAsync(overCap, ModuleOptions())).Diagnostics);

        var success = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(branching, ModuleOptions()));
        Assert.Equal("11", success.ToDisplayString());

        var refused = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(overCap, ModuleOptions()));
        Assert.Contains(refused.Errors, error => error.Code == KatLangErrorCode.StaticStructureLimitExceeded
            && error.Message.Contains("exceeded its work bound", StringComparison.Ordinal));
    }

    // ── 4. Standalone analysis has no operation ─────────────────────────────────────────────────────

    /// <summary>
    /// A tree whose unit is already sealed has no operation left: its producer's ledger was released at the seal.
    /// Exposing it again settles the same frames and charges nothing, while the source entry, which must complete a
    /// unit of its own, refuses such a tree as an internal error instead of running uncharged.
    /// </summary>
    [Fact]
    public void ACompletedTree_HasNoOperationToCharge_AndTheSourceEntryRequiresOne()
    {
        var (resolved, ledger, _) = Resolved(Chain(32));
        var first = new FrontEndTraversalObservations();
        var exposed = PropertyExposureResolver.Resolve(resolved, first);
        var charged = ledger.WorkCharged;
        Assert.True(exposed.CompletedStructure!.Facts.IsSealed);
        Assert.Null(exposed.CompletedStructure!.Facts.ProducerLedger);

        var again = new FrontEndTraversalObservations();
        var reexposed = PropertyExposureResolver.Resolve(exposed, again);

        Assert.Equal(first.RequiredAncestorSettlementFrames, again.RequiredAncestorSettlementFrames);
        Assert.Equal(Metadata(exposed), Metadata(reexposed));
        Assert.Equal(charged, ledger.WorkCharged);

        var error = Assert.Throws<InvalidOperationException>(() => PropertyExposureResolver.ResolveCompilation(
            exposed, observations: null, hostOperations: null, modules: null, CancellationToken.None));
        Assert.Contains("source exposure requires the unsealed structural unit", error.Message, StringComparison.Ordinal);
    }
}
