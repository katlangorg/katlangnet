using System.Text;

namespace KatLang.Tests;

using Mode = PropertyExposureResolver.SettlementShareMode;
using static StaticOwnerWalkTests;

/// <summary>
/// EXPOSURE IN DEEP, WIDE SCOPES (2026-11-24; implementation only, no classification or Lean rule). A level's equation
/// settles every reference that escapes the property it solves, so a body D blocks deep that reads N names declared at
/// the root takes D·N settlement frames: each enclosing level settles the N references once, and each settlement
/// resolves to the declaring level's final summary. The run's share answers none of them across levels, because its
/// keys hold the level (<c>PropertyExposureResolver.SettlementShare</c>).
///
/// <para>Pinned here: settlement work (frames, top-level resolutions, settlement checkpoints and the ledger's charge per
/// frame) for named, opened and halfway-declared reads, deep-narrow and shallow-wide controls, an ambiguous open and a
/// bound-owner control that settles no reference; classification against the unshared and per-path settlements and an
/// expectation written without the analysis; exposure allocation linear in D·N under a per-frame bound; own-property
/// lookups that allocate nothing per lookup; the entry-bound refusal at a lowered envelope; and cancellation at a
/// settlement frame.</para>
/// </summary>
public sealed class ExposureDepthWidthTests
{
    // ── Shapes ──────────────────────────────────────────────────────────────

    private static IEnumerable<string> Reads(string prefix, int names) => Enumerable.Range(0, names).Select(i => $"{prefix}{i}");

    // D nested blocks B0..B{D-1}; the innermost holds the rows, and each level outputs the block it declares.
    private static void AppendNest(StringBuilder source, int depth, IEnumerable<string> rows)
    {
        for (var i = 0; i < depth; i++)
            source.Append($"B{i} = {{\n");
        foreach (var row in rows)
            source.Append(row).Append('\n');
        for (var i = depth - 1; i >= 0; i--)
            source.Append($"}}\nB{i}\n");
    }

    /// <summary>The same reads of names a root <c>open</c> supplies.</summary>
    private static string Opened(int depth, int names)
    {
        var source = new StringBuilder("open M\nM = {\n");
        for (var i = 0; i < names; i++)
            source.Append($"public P{i} = {i}\n");
        source.Append("0\n}\n");
        AppendNest(source, depth, Reads("P", names));
        return source.ToString();
    }

    /// <summary>The same reads of names declared in the body of block depth / 2.</summary>
    private static string Halfway(int depth, int names)
    {
        var source = new StringBuilder();
        var declaring = depth / 2;
        for (var i = 0; i < depth; i++)
        {
            source.Append($"B{i} = {{\n");
            if (i == declaring)
                for (var j = 0; j < names; j++)
                    source.Append($"P{j} = {j}\n");
        }
        foreach (var row in Reads("P", names))
            source.Append(row).Append('\n');
        for (var i = depth - 1; i >= 0; i--)
            source.Append($"}}\nB{i}\n");
        return source.ToString();
    }

    /// <summary>The same reads, P0 provided by two opened algorithms: a real ambiguous open.</summary>
    private static string Ambiguous(int depth, int names)
    {
        var source = new StringBuilder("open M, N\nM = {\npublic P0 = 0\n0\n}\nN = {\npublic P0 = 1\n0\n}\n");
        for (var i = 1; i < names; i++)
            source.Append($"P{i} = {i}\n");
        AppendNest(source, depth, Reads("P", names));
        return source.ToString();
    }

    /// <summary>The same reads of the outermost owner's explicit parameters: requirements, never pending references.</summary>
    private static string Bound(int depth, int names)
    {
        var source = new StringBuilder($"F({string.Join(", ", Reads("p", names))}) = {{\n");
        AppendNest(source, depth, Reads("p", names));
        source.Append($"}}\nF({string.Join(", ", Enumerable.Range(0, names))})\n");
        return source.ToString();
    }

    private static string Shape(string shape, int depth, int names) => shape switch
    {
        "named" => AliasChain(depth, names),
        "opened" => Opened(depth, names),
        "halfway" => Halfway(depth, names),
        "ambiguous" => Ambiguous(depth, names),
        "bound" => Bound(depth, names),
        _ => throw new ArgumentOutOfRangeException(nameof(shape)),
    };

    // ── Harness ─────────────────────────────────────────────────────────────

    private sealed record Parsed(string Diagnostics, string Metadata, FrontEndTraversalObservations Observations);

    /// <summary>The eager parse, observed, under a share mode and the component rule (the defaults are production's).</summary>
    private static Parsed Parse(string source, Mode mode = Mode.Footprint, bool perPath = false)
    {
        var observations = new FrontEndTraversalObservations();
        var previousMode = PropertyExposureResolver.SettlementShareModeForTesting.Value;
        var previousPath = PropertyExposureResolver.ComponentSettlementsPerPathForTesting.Value;
        PropertyExposureResolver.SettlementShareModeForTesting.Value = mode;
        PropertyExposureResolver.ComponentSettlementsPerPathForTesting.Value = perPath;
        try
        {
            var parsed = Parser.ParseObserved(source, options: null, observations);
            var diagnostics = string.Join("\n", parsed.Diagnostics.Select(d => $"{d.Code}@{d.Span} {d.Message}"));
            return new(diagnostics, ExposureSettlementFrameChargeTests.Metadata(parsed.Root), observations);
        }
        finally
        {
            PropertyExposureResolver.SettlementShareModeForTesting.Value = previousMode;
            PropertyExposureResolver.ComponentSettlementsPerPathForTesting.Value = previousPath;
        }
    }

    /// <summary>
    /// Detection and resolution in an operation admitted as the pipeline admits it: the resolved root carries the unsealed
    /// unit, and exposure charges that operation's ledger.
    /// </summary>
    private static (Algorithm Resolved, StaticQueryResourceBudget Ledger) Resolved(string source)
    {
        var syntax = SourceProvenance.ParseSyntaxValidRoot(source);
        var prelude = BuiltinRegistry.SharedSemanticPreludeAlgorithm;
        var measurement = StaticStructureAdmission.Measure(syntax, prelude);
        var operation = new StaticStructureOperation(syntax, measurement.Limits, prelude)
        {
            AdmittedWithoutOpens = !measurement.HasOpens,
            AdmittedWithOutputSpreadMarkers = measurement.HasOutputSpreadMarkers,
        };
        var detected = ParameterDetector.DetectPrevalidated(syntax, structuralOperation: operation);
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detected, observations: null, new DiagnosticBag());
        return (resolved, operation.Queries.Resources);
    }

    /// <summary>The bytes this thread allocates in exposure alone, unobserved (the production path).</summary>
    private static long ExposureBytes(string source)
    {
        var (resolved, _) = Resolved(source);
        var before = GC.GetAllocatedBytesForCurrentThread();
        var exposed = PropertyExposureResolver.Resolve(resolved, observations: null);
        var bytes = GC.GetAllocatedBytesForCurrentThread() - before;
        GC.KeepAlive(exposed);
        return bytes;
    }

    // ── 1. Settlement work ──────────────────────────────────────────────────

    /// <summary>
    /// One settlement frame per enclosing level and escaping read, whatever the share keeps: every level from the reader
    /// up to the declaring one settles the N reads of the property it solves. Names declared halfway down stop the
    /// settlements at their level, and the bound-owner control settles none: parameter reads are requirements, resolved
    /// in place. Each frame is one top-level resolution, pushes two settlement checkpoints (the reference's frame and its
    /// published route), and charges the operation's ledger one unit before it is counted. The live snapshot, live-name and
    /// seed work between frames has its own charge.
    /// </summary>
    [Theory]
    [InlineData("named", 1, 1, 1)]
    [InlineData("named", 90, 1, 90)] // deep and narrow
    [InlineData("named", 1, 2048, 2048)] // shallow and wide
    [InlineData("named", 16, 64, 1024)]
    [InlineData("named", 88, 64, 5632)]
    [InlineData("opened", 88, 64, 5632)]
    [InlineData("halfway", 88, 64, 2752)] // the 43 levels below the declaring one
    [InlineData("ambiguous", 88, 64, 5632)]
    [InlineData("bound", 88, 64, 0)]
    public void SettlementWork_IsOneFramePerEnclosingLevelAndRead(string shape, int depth, int names, long frames)
    {
        var source = Shape(shape, depth, names);
        var parsed = Parse(source);
        Assert.Equal(frames, parsed.Observations.RequiredAncestorSettlementFrames);
        Assert.Equal(frames, parsed.Observations.RequiredAncestorResolutionComputations);
        Assert.Equal(2 * frames, parsed.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.ExposureSettlementFrame));

        var (resolved, ledger) = Resolved(source);
        var before = ledger.WorkCharged;
        long counted = 0, mismatch = 0;
        var observations = new FrontEndTraversalObservations();
        observations.RequiredAncestorSettlementObserver = _ =>
        {
            counted++;
            var reuse = observations.SettlementSnapshotNames + observations.SettlementLiveReadChecks + observations.SettlementSeedPartWork
                + observations.SettlementLiveNameEntries;
            if (mismatch == 0 && ledger.WorkCharged != before + counted * PropertyExposureResolver.SettlementFrameWork + reuse)
                mismatch = counted;
        };
        _ = PropertyExposureResolver.Resolve(resolved, observations);
        Assert.Equal(0, mismatch);
        Assert.Equal(frames, counted);
    }

    // ── 2. Classification ───────────────────────────────────────────────────

    /// <summary>
    /// The published metadata is the unshared settlement's and the per-path walk's, and what reachability alone gives:
    /// a read of a constant declaration requires nothing, so every property is exported, whatever the depth (the
    /// ambiguous read charges nothing either, and is the front end's one diagnostic at its occurrence), while every block
    /// under the bound owner requires its parameters, captured at the block's distance from the owner's body.
    /// </summary>
    [Theory]
    [InlineData("named", 1, 1)]
    [InlineData("named", 90, 1)]
    [InlineData("named", 1, 256)]
    [InlineData("named", 24, 48)]
    [InlineData("opened", 24, 48)]
    [InlineData("halfway", 24, 48)]
    [InlineData("ambiguous", 24, 48)]
    [InlineData("bound", 24, 12)]
    public void Classification_IsTheUnsharedAndPerPathClassification(string shape, int depth, int names)
    {
        var source = Shape(shape, depth, names);
        var production = Parse(source);
        var unshared = Parse(source, Mode.Unshared);
        var perPath = Parse(source, perPath: true);
        Assert.Equal((production.Metadata, production.Diagnostics), (unshared.Metadata, unshared.Diagnostics));
        Assert.Equal((production.Metadata, production.Diagnostics), (perPath.Metadata, perPath.Diagnostics));

        if (shape == "ambiguous")
        {
            var line = 9 + names + depth;
            Assert.Equal($"AmbiguousOpen@[{line}:1, {line}:3) 'P0' is ambiguous: 2 different opened algorithms provide it at the same open level (M, N), "
                + "so it names no single declaration. Qualify it with the algorithm you mean, or open only one of them.", production.Diagnostics);
        }
        else
            Assert.Equal("", production.Diagnostics);

        var properties = production.Metadata.Split('\n', StringSplitOptions.RemoveEmptyEntries);
        var outsideBlocks = shape switch
        {
            "opened" => names + 1,    // M and its names
            "ambiguous" => names + 3, // M.P0, N.P0, their containers, and P1 through the last name
            "bound" => 1,            // F
            _ => names,
        };
        Assert.Equal(depth + outsideBlocks, properties.Length);
        foreach (var line in properties)
        {
            var fields = line.Split('|');
            if (shape != "bound" || !fields[0].StartsWith(".F.", StringComparison.Ordinal))
            {
                Assert.Equal($"{fields[0]}|Exported||", line);
                continue;
            }

            var block = fields[0].Split('.').Length - 3;
            var parameters = Reads("p", names).Order(StringComparer.Ordinal).ToArray();
            Assert.Equal($"{fields[0]}|LocalOnlyCapturedAncestorParameters|{string.Join(",", parameters)}|"
                + string.Join(",", parameters.Select(parameter => $"{parameter}@{block}")), line);
        }
    }

    // ── 3. Allocation ───────────────────────────────────────────────────────

    // Exposure bytes per settlement frame at depth 88 and width 128, before and after the 2026-11-24 trims: 3,835 and 2,634
    // in a Debug build, 3,267 and 2,067 in a Release build. Each bound fails the former allocation by about a sixth.
#if DEBUG
    private const long BytesPerFrame = 3_200;
#else
    private const long BytesPerFrame = 2_600;
#endif

    /// <summary>
    /// Exposure allocates linearly in D·N (doubling the width or the depth about doubles it) and stays under
    /// <see cref="BytesPerFrame"/> per settlement frame. A coarse in-process bound: the least of three warmed-up runs,
    /// never a strict count.
    /// </summary>
    [Fact]
    public void ExposureAllocation_IsLinearInDepthTimesWidth_AndBoundedPerFrame()
    {
        long Least(string source) => Enumerable.Range(0, 3).Min(_ => ExposureBytes(source));
        ExposureBytes(AliasChain(4, 8));
        var narrow = Least(AliasChain(88, 64));
        var wide = Least(AliasChain(88, 128));
        var shallow = Least(AliasChain(44, 128));
        Assert.InRange((double)wide / narrow, 1.7, 2.3);
        Assert.InRange((double)wide / shallow, 1.7, 2.3);
        Assert.True(wide < BytesPerFrame * 88 * 128, $"{wide:N0} bytes for {88 * 128:N0} settlement frames ({wide / (88.0 * 128):N0} per frame)");
    }

    [Theory]
    [InlineData("named", 44, 1, 88, 1)]
    [InlineData("named", 1, 128, 1, 256)]
    [InlineData("opened", 24, 32, 24, 64)]
    [InlineData("bound", 24, 32, 24, 64)]
    public void DoublingOneDimension_StaysWithinLinearAllocationGrowth(
        string shape, int smallDepth, int smallWidth, int largeDepth, int largeWidth)
    {
        ExposureBytes(Shape(shape, 4, 8));
        var small = ExposureBytes(Shape(shape, smallDepth, smallWidth));
        var large = ExposureBytes(Shape(shape, largeDepth, largeWidth));
        // Allow fixed per-document costs, dictionary growth and GC counter noise.
        Assert.True(large <= 2.5 * small, $"{shape}: {small:N0} -> {large:N0} bytes");
        if (shape == "bound")
        {
            // Parameters are direct requirements. At the same dimensions they bypass the settlement frames
            // and the associated storage for pending references.
            var named = ExposureBytes(AliasChain(largeDepth, largeWidth));
            Assert.True(large < named / 2, $"bound {large:N0}, named {named:N0} bytes");
        }
    }

    /// <summary>
    /// An own-property lookup allocates nothing once its level's name index exists: the getter it reads once allocated a
    /// closure over its local on every call, 24 bytes per lookup (about seven per settlement frame on these shapes, and
    /// one per level a detection or editor lookup visits). The coarse bound allows 64 KiB over 100,000 lookups.
    /// </summary>
    [Fact]
    public void OwnPropertyLookups_AllocateNothingPerLookup()
    {
        var scope = ElaboratedScopeLookup.CreateScope(EvaluatorTestSupport.ParseValidRoot(AliasChain(1, 64)));
        Assert.Equal("P63", scope.TryLookupOwnProperty("P63")?.Property.Name);
        const int Lookups = 100_000;
        var found = 0;
        var before = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < Lookups; i++)
            if (scope.TryLookupOwnProperty("P63") is not null)
                found++;
        var bytes = GC.GetAllocatedBytesForCurrentThread() - before;
        Assert.Equal(Lookups, found);
        Assert.True(bytes < 64 * 1024, $"{bytes:N0} bytes for {Lookups:N0} lookups");
    }

    // ── 4. Refusal and cancellation ─────────────────────────────────────────

    /// <summary>
    /// Under a lowered envelope (one static entry per KiB) the deep, wide reads are refused by the static entry bound
    /// before exposure begins: at 8 MiB and depth 32, width 171 is one unpositioned diagnostic with nothing published,
    /// and width 170 is admitted and settles its D·N frames. The boundary is the same before the 2026-11-24 trims.
    /// </summary>
    [Fact]
    public void ALoweredEnvelope_RefusesTheDeepWideReadsBeforeExposure()
    {
        var options = new RunOptions { SourceProcessingLimits = new() { MaxStaticStructureBytes = 8L * 1024 * 1024 } };
        var refused = Parser.Parse(AliasChain(32, 171), options);
        var diagnostic = Assert.Single(refused.Diagnostics);
        Assert.Equal(DiagnosticCode.StaticStructureLimitExceeded, diagnostic.Code);
        Assert.Null(diagnostic.Span);
        Assert.Equal("Static structure analysis exceeded its resource bound. The static queries exceeded their entry bound (8192). "
            + StaticStructureAdmission.EnvelopeSentence, diagnostic.Message);
        Assert.Null(refused.Root.CompletedStructure);

        var observations = new FrontEndTraversalObservations();
        var admitted = Parser.ParseObserved(AliasChain(32, 170), options, observations);
        Assert.Empty(admitted.Diagnostics);
        Assert.Equal(32L * 170, observations.RequiredAncestorSettlementFrames);
    }

    /// <summary>
    /// Cancellation at a settlement frame stops the deep, wide settlement there: nothing is settled after the
    /// checkpoint that cancelled, the unit is rejected, and a fresh parse of the same source then exposes in full.
    /// </summary>
    [Fact]
    public void CancellationAtASettlementFrame_StopsTheSettlement()
    {
        const int Depth = 24, Names = 32, Ordinal = Depth * Names;
        using var cancellation = new CancellationTokenSource();
        long framesAtCancel = -1;
        FrontEndTraversalObservations observations = null!;
        observations = new FrontEndTraversalObservations
        {
            CheckpointReached = (kind, ordinal) =>
            {
                if (kind != FrontEndCancellationCheckpoint.ExposureSettlementFrame || ordinal != Ordinal || cancellation.IsCancellationRequested)
                    return;
                framesAtCancel = observations.RequiredAncestorSettlementFrames;
                cancellation.Cancel();
            },
        };

        var (resolved, _) = Resolved(AliasChain(Depth, Names));
        var unit = resolved.CompletedStructure!.Facts;
        var error = Assert.ThrowsAny<OperationCanceledException>(
            () => PropertyExposureResolver.Resolve(resolved, observations, cancellationToken: cancellation.Token));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.True(unit.IsFailed);
        Assert.False(unit.IsSealed);
        Assert.Equal(Ordinal / 2, framesAtCancel);
        Assert.Equal(framesAtCancel, observations.RequiredAncestorSettlementFrames);
        Assert.Equal(Ordinal, observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.ExposureSettlementFrame));

        var completed = Parse(AliasChain(Depth, Names));
        Assert.Equal(Depth * Names, completed.Observations.RequiredAncestorSettlementFrames);
    }
}
