using System.Numerics;
using System.Reflection;
using System.Runtime.CompilerServices;

namespace KatLang.Tests;

/// <summary>
/// A MATERIALIZATION ATTEMPT LEAVES NOTHING IN THE LOOKUP CACHE OF THE CHAIN RECORDED AT ITS BRANCH (2026-11-17;
/// C#-only resource rule, no value, diagnostic or classification changes, Lean unchanged). A load-bearing clause
/// branch is elaborated when it is selected, under the scope chain the parse recorded at the branch. That chain,
/// and its <see cref="OpenMemberIndexCache"/>, live as long as the parsed tree, and every level the attempt's
/// passes create registers in that one cache. An attempt that is refused publishes nothing and is judged again at
/// the next selection, so before this rule every refused selection left its levels, its facts object and its
/// elaborated body there (measured: 63 KB per refused selection of a unit with ten nested bodies, 3.7 MB with a
/// thousand), and a host that parses once and evaluates the tree repeatedly grew the cache without bound.
///
/// <para>The cache now journals what an attempt adds to its four tables (completed levels, block-head levels,
/// member indexes, body levels) and removes exactly those entries when the attempt ends
/// (<c>DeferredModuleRegion.RunCoreAsync</c>), however it ends: refused, cancelled, faulted or published. Every
/// test here reads the four counts of the recorded chain's cache before the first selection and after later ones
/// and requires them equal; the refused programs must report the same diagnostic at every selection and the
/// published ones must keep their value. The sharing inside ONE attempt is unchanged, and is observed from inside
/// a real attempt and through the journal directly.</para>
///
/// <para>THE EARLY TAKE-BACK (2026-11-19; the same resource rule, nothing observable changes). An attempt that
/// reaches its freeze takes its entries back just before it (<c>DeferredModuleRegion.CompileLoadedBody</c>), so they
/// are not part of the materialization's live peak, and keeps its claim on the cache until
/// <c>RunCoreAsync</c> ends it. Between the two the cache refuses every add, before any table changes: an entry
/// added then would be one no journal removes. The two direct tests of that state are at "The early take-back".</para>
///
/// <para>Host conventions are those of <see cref="DeferredOpenTargetValidationTests"/>: an in-memory downloader
/// that counts its calls, <c>AllowedHosts = ["modules.example"]</c>, a clean parse that downloads nothing, and the
/// materialization's own diagnostic list read through
/// <see cref="Evaluator.RunFlatAsync(Expr, EvaluationLimits?, CancellationToken)"/> over the parsed tree. A test
/// that must act INSIDE an attempt parses through <c>FrontEndPipeline.ProcessAsync</c> with a passive stage
/// observer, which the loader hands to its demand-time passes.</para>
/// </summary>
public class DeferredAttemptCacheRetentionTests
{
    private const string Host = "modules.example";

    private static string Url(string name) => $"https://{Host}/{name}.kat";

    private static readonly Dictionary<string, string> Library = new(StringComparer.Ordinal)
    {
        // Supplies no name any program reads.
        ["unused"] = "public ZzUnused = 0\n",
        // A member that needs an enclosing parameter: the forwarding refusal.
        ["m"] = "public X = y * 10\n",
        // Callables whose parameters make a group of the unit unsettled: the refused signature selection.
        ["cb"] = "public X(x) = x\npublic Y(y) = y\n",
        ["b"] = "public B = 2\n",
        ["plain"] = "public K = 7\n",
    };

    private static readonly string LoadUnused = "load('" + Url("unused") + "')";

    /// <summary>The in-memory host of one run: download counts per module.</summary>
    private sealed class RunHost
    {
        public Dictionary<string, int> Fetches { get; } = new(StringComparer.Ordinal);

        public int TotalFetches => Fetches.Values.Sum();

        public RunOptions Options => new()
        {
            AllowedHosts = [Host],
            DownloadCode = (url, _) =>
            {
                lock (Fetches)
                    Fetches[url] = Fetches.GetValueOrDefault(url) + 1;
                var name = url[$"https://{Host}/".Length..^".kat".Length];
                return Library.TryGetValue(name, out var source)
                    ? ValueTask.FromResult(source)
                    : throw new InvalidOperationException($"404: {url}");
            },
        };
    }

    /// <summary>The four tables of a chain's lookup cache, by count.</summary>
    private readonly record struct Tables(int CompletedLevels, int OpenBlockHeadLevels, int MemberIndexes, int BodyLevels)
    {
        public static Tables Of(OpenMemberIndexCache cache)
            => new(cache.CompletedLevels.Count, cache.OpenBlockHeadLevels.Count, cache.Count, cache.BodyLevelCount);

        public int Total => CompletedLevels + OpenBlockHeadLevels + MemberIndexes + BodyLevels;
    }

    /// <summary>
    /// A passive observer of the unit's exposure stage "retarget-and-seal", which every attempt that reaches exposure
    /// passes after validation and the exposure walk: the one point where a test can act inside an attempt. The
    /// parse passes the same stage, so the handler is set only once the tree exists.
    /// </summary>
    private sealed class SealStage
    {
        public Action? AtSeal { get; set; }

        public FrontEndTraversalObservations Observations { get; }

        public SealStage()
            => Observations = new FrontEndTraversalObservations
            {
                StageObserver = (name, begin) =>
                {
                    if (name == "retarget-and-seal" && begin)
                        AtSeal?.Invoke();
                },
            };
    }

    /// <summary>
    /// The whole front end over a deferred program: every module text parses cleanly as raw syntax, and the
    /// program's parse is clean, holds a region and downloads nothing.
    /// </summary>
    private static async Task<Algorithm.User> ParseDeferred(string source, RunHost host, SealStage? stage = null)
    {
        foreach (var module in Library.Values)
            SourceProvenance.ParseSyntaxValidRoot(module);
        Algorithm.User root;
        if (stage is null)
        {
            var parsed = await SourceProvenance.ParseValidAsync(source, host.Options);
            Assert.Empty(parsed.Diagnostics);
            root = parsed.Root;
        }
        else
        {
            var compiled = await FrontEndPipeline.ProcessAsync(source, host.Options, comparisonObservations: null, stage.Observations);
            Assert.False(compiled.HasErrors, string.Join('\n', compiled.Diagnostics.Select(static diagnostic => diagnostic.Message)));
            Assert.Empty(compiled.Diagnostics);
            root = Assert.IsType<Algorithm.User>(compiled.ElaboratedRoot);
        }

        Assert.True(DeferredModuleRegion.RequiresAsyncEvaluation(new Expr.AlgorithmExpr(root)), "the program holds no deferred region");
        Assert.Equal(0, host.TotalFetches);
        return root;
    }

    private static Task<EvalResult<IReadOnlyList<Decimal128>>> RunFlat(Algorithm.User root, CancellationToken cancellationToken = default)
        => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), null, cancellationToken);

    /// <summary>The diagnostic list of the materialization a run of <paramref name="root"/> refused, by code, message and span.</summary>
    private static async Task<(DiagnosticCode Code, string Message, SourceSpan? Span)[]> Refused(Algorithm.User root)
    {
        var result = await RunFlat(root);
        Assert.True(result.IsError, "the selection produced a value");
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        var failure = Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(error);
        Assert.False(result.Error.IsResourceLimit);
        return [.. failure.Diagnostics.Select(static diagnostic => (diagnostic.Code, diagnostic.Message, diagnostic.Span))];
    }

    private static async Task AssertValue(Algorithm.User root, int expected)
    {
        var flat = await RunFlat(root);
        Assert.False(flat.IsError, flat.IsError ? flat.Error.ToString() : "");
        Assert.Equal([(Decimal128)expected], flat.Value);
    }

    private static async Task<string> Display(string source)
        => Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, new RunHost().Options)).ToDisplayString();

    /// <summary>The same text with every load of the unused module removed: nothing is deferred.</summary>
    private static string PlainTwin(string deferred)
    {
        var twin = deferred.Replace(LoadUnused, "0", StringComparison.Ordinal);
        Assert.NotEqual(deferred, twin);
        Assert.DoesNotContain("load(", twin, StringComparison.Ordinal);
        return twin;
    }

    /// <summary>The region of the one deferred clause of the family at <paramref name="path"/> below <paramref name="owner"/>.</summary>
    private static DeferredModuleRegion RegionAt(Algorithm owner, params string[] path)
    {
        for (var index = 0; index < path.Length - 1; index++)
            owner = owner.Properties.Single(property => property.Name == path[index]).Value;
        var family = Assert.IsType<Algorithm.Conditional>(owner.Properties.Single(property => property.Name == path[^1]).Value);
        var region = Assert.Single(family.Branches, static branch => branch.Body.DeferredRegion is not null).Body.DeferredRegion;
        Assert.NotNull(region);
        return region;
    }

    /// <summary>The lookup cache of the chain recorded at <paramref name="region"/>'s branch.</summary>
    private static OpenMemberIndexCache CacheOf(DeferredModuleRegion region)
    {
        var cache = region.Exposure!.Scope.PropertyScope.MemberIndexes;
        Assert.NotNull(cache);
        return cache;
    }

    // ── The programs ────────────────────────────────────────────────────────

    /// <summary>A load-bearing branch whose rows follow the holder of the unused module.</summary>
    private static string Unit(string rows, string call = "F(1)")
        => "F(0) = 0\n" +
           "F(n) = { H = " + LoadUnused + "\n" +
           rows +
           " }\n" +
           call + "\n";

    /// <summary>A branch whose module provides <c>X</c>, which needs the enclosing <c>y</c>: refused after exposure.</summary>
    private static string Forwarding(string rows)
        => "G(y) = {\n" +
           "  F(0) = 0\n" +
           "  F(n) = { open '" + Url("m") + "'\n" +
           rows +
           " }\n" +
           "  R = F(1)\n" +
           "  R\n" +
           "}\n" +
           "G(1)\n";

    /// <summary>Three bodies of one unit, each opening a block of its own (the unit of <see cref="DeferredOpenTargetValidationTests"/>).</summary>
    private static readonly string ThreeBlocks = Unit(
        "  A = { open { public X = 1 }\n" +
        "    X }\n" +
        "  B = { open { public Y = 2 }\n" +
        "    Y }\n" +
        "  C = { open { public Z = 3 }\n" +
        "    Z }\n" +
        "  A + B + C");

    /// <summary>
    /// A dot edge whose member is no member of its receiver and whose receiver an open provides: the provenance
    /// finalizer of the unit's exposure judges it, through the opened target's member index and its body level.
    /// </summary>
    private static string DotOriginRows(string indent)
        => indent + "S = { public P = { public W = 4 } }\n" +
           indent + "Q(x) = 5\n" +
           indent + "A = { open S\n" +
           indent + "  P.zz }\n";

    public sealed record RefusedCase(string Name, string Deferred, string[] Path, DiagnosticCode Code)
    {
        public override string ToString() => Name;
    }

    private const string ForwardingRefusal = "a forwarding refusal";
    private const string ForwardingRefusalAfterTheFinalizer = "a forwarding refusal after the provenance finalizer";

    /// <summary>
    /// Every way a selection is refused. The first six reach a pass that runs under the recorded chain (validation,
    /// exposure) and write its cache (measured 2026-11-17, and these rows fail when the take-back is disabled). The
    /// last two stop before any such pass and write nothing: their pins hold trivially, and they are here because
    /// they are ways an attempt ends.
    /// </summary>
    private static readonly RefusedCase[] RefusedCases =
    [
        // Open-provider validation: completed levels and a block-head level.
        new("an unresolvable block-headed path",
            Unit("  A = { open { public X = 1 }.Nope\n" +
                 "    X }\n" +
                 "  B = { open { public Y = 2 }\n" +
                 "    Y }\n" +
                 "  A(5) + B"),
            ["F"], DiagnosticCode.UnresolvedOpenTarget),
        // ... whose description walks a step into the block: a body level too.
        new("an unresolvable path two steps into a block",
            Unit("  A = { open { public S = { public X = 1 } }.S.Nope\n" +
                 "    X }\n" +
                 "  A(5)"),
            ["F"], DiagnosticCode.UnresolvedOpenTarget),
        // Decided after exposure.
        new(ForwardingRefusal,
            Forwarding("    B = { open { public Y = 2 }\n" +
                       "      Y }\n" +
                       "    X + B"),
            ["G", "F"], DiagnosticCode.DeferredBranchForwardsEnclosingParameter),
        // ... after the provenance finalizer ran: a member index and a body level too.
        new(ForwardingRefusalAfterTheFinalizer,
            Forwarding(DotOriginRows("    ") +
                       "    X + A(Q)"),
            ["G", "F"], DiagnosticCode.DeferredBranchForwardsEnclosingParameter),
        new("a parameter collision",
            "F(0) = 42\n" +
            "F(v) = { open '" + Url("b") + "'\n" +
            "  A = { open { public X = 1 }\n" +
            "    X }\n" +
            "  v = 5\n" +
            "  A }\n" +
            "F(7)\n",
            ["F"], DiagnosticCode.ParameterPropertyCollision),
        new("an output-rule refusal",
            "F(0) = 0\n" +
            "F(n) = {\n" +
            "  open '" + Url("plain") + "'\n" +
            "  A = { open { public X = 1 }\n" +
            "    X }\n" +
            "  G = { a, b = q, 1 }\n" +
            "  K + n + A\n" +
            "}\n" +
            "F(1)\n",
            ["F"], DiagnosticCode.ExplicitParametersRequireOutput),
        new("a refused signature selection",
            "F(0) = 0\n" +
            "F(n) = { open '" + Url("cb") + "'\n" +
            "  A = B + X\n" +
            "  B = A + Y\n" +
            "  7 }\n" +
            "F(1)\n",
            ["F"], DiagnosticCode.SelfDependentInferredParameters),
        new("a failed fetch",
            "F(0) = 0\n" +
            "F(n) = { H = load('" + Url("missing") + "')\n" +
            "  A = { open { public X = 1 }\n" +
            "    X }\n" +
            "  A }\n" +
            "F(1)\n",
            ["F"], DiagnosticCode.LoadFetchFailed),
    ];

    public static TheoryData<RefusedCase> RefusedData()
    {
        var data = new TheoryData<RefusedCase>();
        foreach (var item in RefusedCases)
            data.Add(item);
        return data;
    }

    // ── Refused, at every selection ─────────────────────────────────────────

    [Theory]
    [MemberData(nameof(RefusedData))]
    public async Task RefusedSelection_LeavesTheRecordedChainsCacheAsTheParseLeftIt(RefusedCase program)
    {
        var host = new RunHost();
        var root = await ParseDeferred(program.Deferred, host);
        var region = RegionAt(root, program.Path);
        var cache = CacheOf(region);
        var before = Tables.Of(cache);

        var first = await Refused(root);
        Assert.Equal(program.Code, first[0].Code);
        Assert.Equal(before, Tables.Of(cache));

        // Judged again at every selection, with the same report, and nothing accumulates: 1, 3 and 20 selections.
        for (var selection = 2; selection <= 20; selection++)
        {
            Assert.Equal(first, await Refused(root));
            Assert.Equal(before, Tables.Of(cache));
        }

        Assert.Equal(20, region.MaterializationAttempts);
        Assert.False(region.IsMaterialized);
    }

    [Theory]
    [InlineData(ForwardingRefusal)]
    [InlineData(ForwardingRefusalAfterTheFinalizer)]
    public async Task AttemptRefusedAfterExposure_HeldItsEntriesWhileItRan(string name)
    {
        // The one point where a test can look inside an attempt is the unit's seal, which only an attempt that
        // reaches exposure passes: a forwarding refusal is decided after it. There the validation and exposure
        // levels of the attempt are registered, with one block-head level; afterwards none of them is.
        var program = RefusedCases.Single(item => item.Name == name);
        var host = new RunHost();
        var stage = new SealStage();
        var root = await ParseDeferred(program.Deferred, host, stage);
        var region = RegionAt(root, program.Path);
        var cache = CacheOf(region);
        var before = Tables.Of(cache);

        Tables? inside = null;
        stage.AtSeal = () => inside = Tables.Of(cache);
        var refused = await Refused(root);
        stage.AtSeal = null;
        Assert.Equal(program.Code, refused[0].Code);

        Assert.NotNull(inside);
        Assert.True(inside.Value.CompletedLevels > before.CompletedLevels,
            $"inside the attempt the cache held {inside.Value.CompletedLevels} completed levels, {before.CompletedLevels} before it");
        Assert.Equal(before.OpenBlockHeadLevels + 1, inside.Value.OpenBlockHeadLevels);
        Assert.Equal(before, Tables.Of(cache));
    }

    // ── Cancelled and faulted ───────────────────────────────────────────────

    [Fact]
    public async Task CancelledAttempt_LeavesNothing_AndTheNextSelectionPublishes()
    {
        var host = new RunHost();
        var stage = new SealStage();
        var root = await ParseDeferred(ThreeBlocks, host, stage);
        var region = RegionAt(root, "F");
        var cache = CacheOf(region);
        var before = Tables.Of(cache);

        for (var selection = 1; selection <= 20; selection++)
        {
            using var cancellation = new CancellationTokenSource();
            var written = 0;
            stage.AtSeal = () =>
            {
                // The attempt is in flight: its levels are registered, and it is cancelled here.
                written = Tables.Of(cache).Total - before.Total;
                cancellation.Cancel();
            };
            var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => RunFlat(root, cancellation.Token));
            stage.AtSeal = null;
            Assert.Equal(cancellation.Token, error.CancellationToken);
            Assert.True(written > 0, "the cancelled attempt had written nothing when it was cancelled");
            Assert.Equal(before, Tables.Of(cache));
            Assert.Equal(selection, region.MaterializationAttempts);
            Assert.False(region.IsMaterialized);
        }

        // Nothing of the cancelled attempts stands in the way: the same tree publishes, with the twin's value.
        await AssertValue(root, 6);
        Assert.True(region.IsMaterialized);
        Assert.Equal(21, region.MaterializationAttempts);
        Assert.Equal(before, Tables.Of(cache));
        Assert.Equal("6", await Display(PlainTwin(ThreeBlocks)));
    }

    [Fact]
    public async Task FaultedAttempt_LeavesNothing_AndTheNextSelectionPublishes()
    {
        var host = new RunHost();
        var stage = new SealStage();
        var root = await ParseDeferred(ThreeBlocks, host, stage);
        var region = RegionAt(root, "F");
        var cache = CacheOf(region);
        var before = Tables.Of(cache);

        for (var selection = 1; selection <= 3; selection++)
        {
            var written = 0;
            stage.AtSeal = () =>
            {
                written = Tables.Of(cache).Total - before.Total;
                throw new InvalidOperationException("the stage observer failed");
            };
            // An exception no pass handles: the attempt faults, and the fault reaches the caller unchanged.
            var error = await Assert.ThrowsAsync<InvalidOperationException>(() => RunFlat(root));
            stage.AtSeal = null;
            Assert.Equal("the stage observer failed", error.Message);
            Assert.True(written > 0, "the faulted attempt had written nothing when it failed");
            Assert.Equal(before, Tables.Of(cache));
            Assert.Equal(selection, region.MaterializationAttempts);
            Assert.False(region.IsMaterialized);
        }

        await AssertValue(root, 6);
        Assert.True(region.IsMaterialized);
        Assert.Equal(before, Tables.Of(cache));
    }

    // ── Published ───────────────────────────────────────────────────────────

    public static TheoryData<string, string, int> PublishedUnits() => new()
    {
        { "three open-target blocks", ThreeBlocks, 6 },
        { "a dot edge judged by the provenance finalizer", Unit(DotOriginRows("  ") + "  A(Q)"), 5 },
    };

    [Theory]
    [MemberData(nameof(PublishedUnits))]
    public async Task PublishedUnit_LeavesNothingEither_AndKeepsItsValue(string name, string deferred, int expected)
    {
        Assert.NotEmpty(name);
        Assert.Equal(expected.ToString(System.Globalization.CultureInfo.InvariantCulture), await Display(PlainTwin(deferred)));

        var host = new RunHost();
        var root = await ParseDeferred(deferred, host);
        var region = RegionAt(root, "F");
        var cache = CacheOf(region);
        var before = Tables.Of(cache);

        // The strict rule holds for a published attempt: the unit is the tree it returned, not an entry here.
        for (var selection = 1; selection <= 4; selection++)
        {
            await AssertValue(root, expected);
            Assert.Equal(before, Tables.Of(cache));
            Assert.True(region.IsMaterialized);
            Assert.Equal(1, region.MaterializationAttempts);
            Assert.Equal(1, host.TotalFetches);
        }
    }

    [Fact]
    public async Task OneAttempt_SharesItsEntriesWhileItRuns_ExactlyAsBefore()
    {
        // Seen from inside the real attempt, at the unit's seal: validation and the exposure walk are done.
        var host = new RunHost();
        var stage = new SealStage();
        var root = await ParseDeferred(ThreeBlocks, host, stage);
        var region = RegionAt(root, "F");
        var cache = CacheOf(region);
        var before = Tables.Of(cache);
        Assert.Equal(new Tables(4, 0, 0, 0), before);

        var seals = 0;
        Tables inside = default;
        stage.AtSeal = () =>
        {
            seals++;
            inside = Tables.Of(cache);
        };
        await AssertValue(root, 6);
        stage.AtSeal = null;
        Assert.Equal(1, seals);

        // What the cache used to hold for good once this unit had materialized (measured 2026-11-17: 4 completed
        // levels before, 17 after, one block-head level): K = 3 open-target blocks still share ONE prelude level
        // over the unit's facts, and every level of the attempt is registered for the attempt's own lookups.
        Assert.Equal(new Tables(17, 1, 0, 0), inside);
        Assert.Equal(before, Tables.Of(cache));
    }

    [Fact]
    public async Task MemberIndexAndBodyLevel_AreSharedInsideAnAttempt_AndTakenBackWithIt()
    {
        // K bodies of one unit, each opening the same block and reading its member through a dot edge.
        const int bodies = 6;
        var rows = "  S = { public P = { public W = 4 } }\n" + "  Q(x) = 5\n";
        for (var index = 1; index <= bodies; index++)
            rows += $"  A{index} = {{ open S\n    P.zz }}\n";
        var deferred = Unit(rows + "  A1(Q)");
        Assert.Equal("5", await Display(PlainTwin(deferred)));

        var host = new RunHost();
        var root = await ParseDeferred(deferred, host);
        var region = RegionAt(root, "F");
        var cache = CacheOf(region);
        var before = Tables.Of(cache);
        await AssertValue(root, 5);
        Assert.True(region.TryGetMaterialized(out var unit));
        Assert.Equal(before, Tables.Of(cache));

        // The journal directly, over the materialized unit: the lookups an attempt's passes make under the chain.
        var chain = region.Exposure!.Scope.PropertyScope;
        var attempt = cache.BeginMaterializationAttempt();
        var unitLevel = ElaboratedScopeLookup.CreateScope(unit, chain, completedContext: CompletedStructureContext.For(unit, chain));
        var memberLevels = new HashSet<ElaboratedPropertyScope>(ReferenceEqualityComparer.Instance);
        for (var index = 1; index <= bodies; index++)
        {
            var body = unit.Properties.Single(property => property.Name == $"A{index}").Value;
            var bodyLevel = ElaboratedScopeLookup.CreateScope(body, unitLevel, completedContext: CompletedStructureContext.For(body, unitLevel));
            var opened = ElaboratedScopeLookup.LookupSingleOpenMember(bodyLevel, "P");
            Assert.NotNull(opened);
            memberLevels.Add(opened.Value.MemberLevel);
        }

        // K providers of one target: ONE member index and ONE body level, for as long as the attempt runs.
        var inside = Tables.Of(cache);
        Assert.Equal(before.MemberIndexes + 1, inside.MemberIndexes);
        Assert.Equal(before.BodyLevels + 1, inside.BodyLevels);
        Assert.Single(memberLevels);
        Assert.True(inside.CompletedLevels >= before.CompletedLevels + bodies + 1,
            $"the attempt registered {inside.CompletedLevels - before.CompletedLevels} completed levels for {bodies} bodies");

        // A second attempt cannot begin while this one writes the cache (the materialization gate serializes them).
        Assert.Throws<InvalidOperationException>(() => cache.BeginMaterializationAttempt());

        attempt.TakeBack();
        Assert.Equal(before, Tables.Of(cache));
        // Idempotent, and the cache takes the next attempt.
        attempt.TakeBack();
        Assert.Equal(before, Tables.Of(cache));
        cache.BeginMaterializationAttempt().TakeBack();
        Assert.Equal(before, Tables.Of(cache));

        // Outside an attempt nothing is journaled: an entry written then stays (the eager parse's own writes).
        var kept = ElaboratedScopeLookup.CreateScope(unit, chain, completedContext: CompletedStructureContext.For(unit, chain));
        Assert.Same(kept, cache.CompletedLevels[(kept.CompletedContext!.Facts, kept.CompletedContext.Key)]);
        Assert.Equal(before.CompletedLevels + 1, cache.CompletedLevels.Count);
    }

    // ── The early take-back, and the writes the cache refuses after it ──────

    /// <summary>
    /// A published unit whose cache a test then drives directly, as
    /// <see cref="MemberIndexAndBodyLevel_AreSharedInsideAnAttempt_AndTakenBackWithIt"/> does: the cache, the chain
    /// recorded at the branch, the materialized unit, and the observations the parse gave the cache (it counts a
    /// member-index build there).
    /// </summary>
    private static async Task<(OpenMemberIndexCache Cache, ElaboratedPropertyScope Chain, Algorithm Unit, FrontEndTraversalObservations Observations)>
        PublishedUnitToDriveDirectly()
    {
        var rows = "  S = { public P = { public W = 4 } }\n" + "  Q(x) = 5\n";
        for (var index = 1; index <= 3; index++)
            rows += $"  A{index} = {{ open S\n    P.zz }}\n";
        var host = new RunHost();
        var stage = new SealStage();
        var root = await ParseDeferred(Unit(rows + "  A1(Q)"), host, stage);
        var region = RegionAt(root, "F");
        var cache = CacheOf(region);
        var before = Tables.Of(cache);
        await AssertValue(root, 5);
        Assert.True(region.TryGetMaterialized(out var unit));
        // The published attempt took its entries back before its freeze and ended its claim afterwards.
        Assert.Equal(before, Tables.Of(cache));
        return (cache, region.Exposure!.Scope.PropertyScope, unit, stage.Observations);
    }

    /// <summary>
    /// The body-level tables of a cache by parent, an EMPTY table included: <see cref="OpenMemberIndexCache.BodyLevelCount"/>
    /// sums the bodies and cannot see a parent that holds none, which is what a refused add must not leave.
    /// </summary>
    private static System.Collections.IDictionary BodyLevelTablesByParent(OpenMemberIndexCache cache)
        => (System.Collections.IDictionary)typeof(OpenMemberIndexCache)
            .GetField("_bodyLevels", BindingFlags.NonPublic | BindingFlags.Instance)!.GetValue(cache)!;

    private static void AssertRefusedAfterTakeBack(Action add)
    {
        var error = Assert.Throws<InvalidOperationException>(add);
        Assert.Contains("after it took its entries back", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task TakeBackBeforeFreeze_RestoresEveryTable_AndEveryAddIsRefusedUntilTheAttemptEnds()
    {
        var (cache, chain, unit, observations) = await PublishedUnitToDriveDirectly();
        Algorithm Body(string name) => unit.Properties.Single(property => property.Name == name).Value;
        ElaboratedPropertyScope LevelOf(Algorithm body, ElaboratedPropertyScope parent)
            => ElaboratedScopeLookup.CreateScope(body, parent, completedContext: CompletedStructureContext.For(body, parent));
        var eagerFacts = chain.Root.CompletedContext!.Facts;

        // What the cache holds before the attempt, one entry in each table. Written outside an attempt, so it stays,
        // as the parse's own entries do.
        var unitLevel = LevelOf(unit, chain);
        var unitKey = (unitLevel.CompletedContext!.Facts, unitLevel.CompletedContext.Key);
        Assert.NotSame(eagerFacts, unitKey.Facts);
        Assert.Same(unitLevel, cache.CompletedLevels[unitKey]);
        cache.OpenBlockHeadLevels.Add(unitKey.Facts, unitLevel);
        var builds = observations.LookupOpenMemberIndexBuilds;
        var heldIndex = cache.IndexOf(Body("S"));
        Assert.Equal(builds + 1, observations.LookupOpenMemberIndexBuilds);
        var heldBodyLevel = cache.BodyLevel(Body("S"), unitLevel);
        var original = Tables.Of(cache);
        var parents = BodyLevelTablesByParent(cache);
        var originalParents = parents.Count;
        builds = observations.LookupOpenMemberIndexBuilds;

        void AssertOriginal()
        {
            Assert.Equal(original, Tables.Of(cache));
            Assert.Same(heldIndex, cache.IndexOf(Body("S")));
            Assert.Same(unitLevel, cache.CompletedLevels[unitKey]);
            Assert.Same(unitLevel, cache.OpenBlockHeadLevels[unitKey.Facts]);
            Assert.Equal(originalParents, parents.Count);
            var held = Assert.IsAssignableFrom<System.Collections.IDictionary>(parents[unitLevel]);
            Assert.Single(held);
            Assert.Same(heldBodyLevel, held[Body("S")]);
            Assert.Equal(builds, observations.LookupOpenMemberIndexBuilds);
        }

        // The attempt adds to all four tables: a body under a parent the cache knows, and one under a new parent.
        var attempt = cache.BeginMaterializationAttempt();
        var attemptLevel = LevelOf(Body("A2"), unitLevel);
        var attemptKey = (attemptLevel.CompletedContext!.Facts, attemptLevel.CompletedContext.Key);
        Assert.Same(attemptLevel, cache.CompletedLevels[attemptKey]);
        cache.OpenBlockHeadLevels.Add(eagerFacts, chain.Root);
        cache.IndexOf(Body("A1"));
        cache.BodyLevel(Body("A1"), unitLevel);
        cache.BodyLevel(Body("S"), attemptLevel);
        var inside = Tables.Of(cache);
        Assert.True(inside.CompletedLevels > original.CompletedLevels);
        Assert.Equal(original.OpenBlockHeadLevels + 1, inside.OpenBlockHeadLevels);
        Assert.Equal(original.MemberIndexes + 1, inside.MemberIndexes);
        Assert.Equal(original.BodyLevels + 2, inside.BodyLevels);
        Assert.Equal(originalParents + 1, parents.Count);
        builds = observations.LookupOpenMemberIndexBuilds;

        // The early take-back: every count is what it was, the attempt's entries are gone, the held ones are not.
        attempt.TakeBackBeforeFreeze();
        AssertOriginal();
        Assert.False(cache.CompletedLevels.ContainsKey(attemptKey));
        Assert.False(cache.OpenBlockHeadLevels.ContainsKey(eagerFacts));
        Assert.False(parents.Contains(attemptLevel));

        // A read of a held entry is what it always was.
        Assert.Same(heldBodyLevel, cache.BodyLevel(Body("S"), unitLevel));
        Assert.True(cache.CompletedLevels.TryGetValue(unitKey, out var foundLevel));
        Assert.Same(unitLevel, foundLevel);
        Assert.True(cache.OpenBlockHeadLevels.TryGetValue(unitKey.Facts, out var foundHead));
        Assert.Same(unitLevel, foundHead);
        AssertOriginal();

        // So is a TryAdd of a key the table holds, by a caller or by a level that registers itself: a no-op.
        Assert.False(cache.CompletedLevels.TryAdd(unitKey, attemptLevel));
        Assert.False(cache.OpenBlockHeadLevels.TryAdd(unitKey.Facts, attemptLevel));
        Assert.NotSame(unitLevel, LevelOf(unit, chain));
        AssertOriginal();

        // Every add is refused, before its table changes and before anything is built or counted for it.
        AssertRefusedAfterTakeBack(() => cache.IndexOf(Body("A1")));
        AssertOriginal();
        // A new body under a parent the cache holds: the parent's table keeps exactly what it held. The unit is a
        // body whose level registers no completed key of its own (shown below, where the add is accepted), so its
        // refusal is the body-level table's own and not that of a level registering itself.
        AssertRefusedAfterTakeBack(() => cache.BodyLevel(unit, unitLevel));
        AssertOriginal();
        AssertRefusedAfterTakeBack(() => cache.BodyLevel(Body("A1"), unitLevel));
        AssertOriginal();
        // A parent the cache has not seen: no table is created for it.
        AssertRefusedAfterTakeBack(() => cache.BodyLevel(Body("S"), attemptLevel));
        AssertOriginal();
        Assert.False(parents.Contains(attemptLevel));
        AssertRefusedAfterTakeBack(() => cache.CompletedLevels.TryAdd(attemptKey, attemptLevel));
        AssertOriginal();
        AssertRefusedAfterTakeBack(() => cache.CompletedLevels.Add(attemptKey, attemptLevel));
        AssertOriginal();
        // A new level registers itself in the completed levels: creating one under a key the cache lacks is the same add.
        AssertRefusedAfterTakeBack(() => LevelOf(Body("A2"), unitLevel));
        AssertOriginal();
        Assert.False(cache.CompletedLevels.ContainsKey(attemptKey));
        AssertRefusedAfterTakeBack(() => cache.OpenBlockHeadLevels.Add(eagerFacts, chain.Root));
        AssertOriginal();
        AssertRefusedAfterTakeBack(() => cache.OpenBlockHeadLevels.TryAdd(eagerFacts, chain.Root));
        AssertOriginal();
        Assert.False(cache.OpenBlockHeadLevels.ContainsKey(eagerFacts));

        // The attempt still holds the cache: no other attempt begins, and a second early take-back changes nothing.
        var second = Assert.Throws<InvalidOperationException>(() => cache.BeginMaterializationAttempt());
        Assert.Contains("another attempt is still writing", second.Message, StringComparison.Ordinal);
        attempt.TakeBackBeforeFreeze();
        AssertRefusedAfterTakeBack(() => cache.IndexOf(Body("A1")));
        AssertOriginal();

        // The take-back that ends the attempt removes nothing more, and is idempotent; an early one after it is a no-op.
        attempt.TakeBack();
        AssertOriginal();
        attempt.TakeBack();
        attempt.TakeBackBeforeFreeze();
        AssertOriginal();

        // The cache takes the next attempt, whose adds are accepted and taken back as ever.
        var next = cache.BeginMaterializationAttempt();
        cache.IndexOf(Body("A1"));
        cache.BodyLevel(Body("S"), attemptLevel);
        Assert.Equal(original.MemberIndexes + 1, cache.Count);
        Assert.Equal(original.BodyLevels + 1, cache.BodyLevelCount);
        Assert.True(parents.Contains(attemptLevel));
        // The body refused above under the held parent: accepted now, and its level registers no completed key.
        var completedLevels = cache.CompletedLevels.Count;
        cache.BodyLevel(unit, unitLevel);
        Assert.Equal(completedLevels, cache.CompletedLevels.Count);
        Assert.Equal(original.BodyLevels + 2, cache.BodyLevelCount);
        builds = observations.LookupOpenMemberIndexBuilds;
        next.TakeBack();
        AssertOriginal();

        // Outside an attempt nothing is refused and nothing is journaled: the entry stays.
        cache.IndexOf(Body("A1"));
        Assert.Equal(original.MemberIndexes + 1, cache.Count);
    }

    [Fact]
    public async Task TakeBackBeforeFreeze_OfAnAttemptThatAddedNothing_RefusesWritesAllTheSame()
    {
        var (cache, chain, unit, _) = await PublishedUnitToDriveDirectly();
        var body = unit.Properties.Single(static property => property.Name == "S").Value;
        var original = Tables.Of(cache);
        var parents = BodyLevelTablesByParent(cache);
        var originalParents = parents.Count;

        var attempt = cache.BeginMaterializationAttempt();
        attempt.TakeBackBeforeFreeze();
        Assert.Equal(original, Tables.Of(cache));

        AssertRefusedAfterTakeBack(() => cache.IndexOf(body));
        AssertRefusedAfterTakeBack(() => cache.BodyLevel(body, chain));
        Assert.Equal(original, Tables.Of(cache));
        Assert.Equal(originalParents, parents.Count);
        Assert.Throws<InvalidOperationException>(() => cache.BeginMaterializationAttempt());

        attempt.TakeBack();
        Assert.Equal(original, Tables.Of(cache));
        Assert.Equal(originalParents, parents.Count);

        // An attempt that never takes its entries back early is unchanged: its adds are accepted until it ends.
        var plain = cache.BeginMaterializationAttempt();
        cache.IndexOf(body);
        cache.BodyLevel(body, chain);
        Assert.Equal(original.MemberIndexes + 1, cache.Count);
        Assert.Equal(original.BodyLevels + 1, cache.BodyLevelCount);
        plain.TakeBack();
        Assert.Equal(original, Tables.Of(cache));
        Assert.Equal(originalParents, parents.Count);
    }

    // ── Several units, and a region below a unit ────────────────────────────

    [Fact]
    public async Task TwoUnitsOfOneProgram_ShareOneCache_AndNeitherLeavesAnythingInIt()
    {
        var deferred =
            "F(0) = 0\n" +
            "F(n) = { H = " + LoadUnused + "\n" +
            "  A = { open { public X = 1 }.Nope\n" +
            "    X }\n" +
            "  A(5) }\n" +
            "P(0) = 0\n" +
            "P(n) = { H = " + LoadUnused + "\n" +
            "  A = { open { public Y = 1 }\n" +
            "    Y }\n" +
            "  A + 5 }\n" +
            "P(1) + F(1)\n";
        var host = new RunHost();
        var root = await ParseDeferred(deferred, host);
        var refused = RegionAt(root, "F");
        var published = RegionAt(root, "P");
        var cache = CacheOf(refused);
        Assert.Same(cache, CacheOf(published));
        var before = Tables.Of(cache);

        var first = await Refused(root);
        Assert.Equal(DiagnosticCode.UnresolvedOpenTarget, Assert.Single(first).Code);
        for (var selection = 2; selection <= 20; selection++)
        {
            Assert.Equal(first, await Refused(root));
            Assert.Equal(before, Tables.Of(cache));
        }

        Assert.True(published.IsMaterialized);
        Assert.Equal(1, published.MaterializationAttempts);
        Assert.Equal(20, refused.MaterializationAttempts);
        Assert.Equal(1, host.TotalFetches);
    }

    /// <summary>
    /// A load-bearing family NESTED in a unit. The inner region records its chain during the outer unit's exposure:
    /// its levels are levels of the outer attempt, and they share the eager chain's cache object.
    /// </summary>
    private static string Nested(string innerRows)
        => Unit("  S = { public T = { public P = 4 } }\n" +
                "  Z = { public W = { public V = 2 } }\n" +
                "  L = Z.W\n" +
                "  G(0) = 0\n" +
                "  G(m) = { H2 = " + LoadUnused + "\n" +
                innerRows +
                " }\n" +
                "  G(1)");

    [Fact]
    public async Task RegionBelowAPublishedUnit_Refused_LeavesNothing_AndIsJudgedAgainWithTheSameReport()
    {
        var deferred = Nested(
            "    A = { open { public X = 1 }.Nope\n" +
            "      X }\n" +
            "    B = { open S.T\n" +
            "      P }\n" +
            "    C = { open L\n" +
            "      V }\n" +
            "    A(5) + B + C");
        var host = new RunHost();
        var root = await ParseDeferred(deferred, host);
        var outer = RegionAt(root, "F");
        var cache = CacheOf(outer);
        var before = Tables.Of(cache);

        var first = await Refused(root);
        Assert.Equal(DiagnosticCode.UnresolvedOpenTarget, Assert.Single(first).Code);
        Assert.Equal(before, Tables.Of(cache));
        Assert.True(outer.TryGetMaterialized(out var unit));
        var inner = RegionAt(unit, "G");
        // The chain the inner region recorded is the outer attempt's, whose entries are gone: only the region holds it.
        Assert.Same(cache, CacheOf(inner));

        for (var selection = 2; selection <= 20; selection++)
        {
            Assert.Equal(first, await Refused(root));
            Assert.Equal(before, Tables.Of(cache));
        }

        Assert.Equal(1, outer.MaterializationAttempts);
        Assert.Equal(20, inner.MaterializationAttempts);
        Assert.False(inner.IsMaterialized);
        // One download serves both units and every attempt.
        Assert.Equal(1, host.TotalFetches);
    }

    [Fact]
    public async Task RegionBelowAPublishedUnit_Published_LeavesNothing_AndHasItsTwinsValue()
    {
        // The inner unit opens a dotted path and an alias whose targets the OUTER unit declares beside the family,
        // so its lookups pass through levels the outer attempt created.
        var deferred = Nested(
            "    A = { open { public X = 1 }\n" +
            "      X }\n" +
            "    B = { open S.T\n" +
            "      P }\n" +
            "    C = { open L\n" +
            "      V }\n" +
            "    A + B + C + m");
        Assert.Equal("8", await Display(PlainTwin(deferred)));
        Assert.Equal("8", await Display(deferred));

        var host = new RunHost();
        var root = await ParseDeferred(deferred, host);
        var outer = RegionAt(root, "F");
        var cache = CacheOf(outer);
        var before = Tables.Of(cache);

        for (var selection = 1; selection <= 4; selection++)
        {
            await AssertValue(root, 8);
            Assert.Equal(before, Tables.Of(cache));
        }

        Assert.True(outer.TryGetMaterialized(out var unit));
        var inner = RegionAt(unit, "G");
        Assert.Same(cache, CacheOf(inner));
        Assert.True(inner.IsMaterialized);
        Assert.Equal(1, outer.MaterializationAttempts);
        Assert.Equal(1, inner.MaterializationAttempts);
    }

    // ── Reclaim ─────────────────────────────────────────────────────────────

    [Fact]
    public async Task RefusedAttempt_ItsFactsAndItsLevelsAreReclaimed_WhileTheTreeLives()
    {
        var host = new RunHost();
        var stage = new SealStage();
        var program = RefusedCases.Single(static item => item.Name == ForwardingRefusal);
        var root = await ParseDeferred(program.Deferred, host, stage);
        var region = RegionAt(root, program.Path);
        var cache = CacheOf(region);
        var before = Tables.Of(cache);

        var (facts, level) = await RefuseOnceAndForget(root, region, stage);
        ForceFullCollection();

        // Nothing reachable from the tree, the region or the loader holds the refused attempt.
        Assert.False(facts.IsAlive, "the refused attempt's facts object is still reachable");
        Assert.False(level.IsAlive, "a level of the refused attempt is still reachable");
        Assert.Equal(before, Tables.Of(cache));
        Assert.Equal(1, region.MaterializationAttempts);
        GC.KeepAlive(root);
        GC.KeepAlive(region);
        GC.KeepAlive(cache);
    }

    /// <summary>
    /// One refused selection, whose facts object and one of whose levels are captured weakly from inside the
    /// attempt. Not inlined, and it returns weak references only, so no frame of the caller holds the attempt.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static async Task<(WeakReference Facts, WeakReference Level)> RefuseOnceAndForget(
        Algorithm.User root, DeferredModuleRegion region, SealStage stage)
    {
        var cache = CacheOf(region);
        var eager = region.Exposure!.Scope.PropertyScope.Root.CompletedContext!.Facts;
        WeakReference? facts = null;
        WeakReference? level = null;
        stage.AtSeal = () =>
        {
            // The attempt's own facts: the ones the cache holds besides the eager program's.
            var key = cache.CompletedLevels.Keys.First(key => !ReferenceEquals(key.Facts, eager));
            facts = new WeakReference(key.Facts);
            level = new WeakReference(cache.CompletedLevels[key]);
        };
        var refused = await Refused(root);
        stage.AtSeal = null;
        Assert.Equal(DiagnosticCode.DeferredBranchForwardsEnclosingParameter, refused[0].Code);
        Assert.NotNull(facts);
        Assert.NotNull(level);
        return (facts, level);
    }

    private static void ForceFullCollection()
    {
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
        GC.WaitForPendingFinalizers();
        GC.Collect(GC.MaxGeneration, GCCollectionMode.Forced, blocking: true);
    }
}
