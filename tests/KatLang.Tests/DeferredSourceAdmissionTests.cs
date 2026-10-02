using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// Required compilation units receive host admission checks; suspended supplied computations
/// do no source work. All acquisition is deterministic in-memory work, never HTTP.
/// </summary>
public class DeferredSourceAdmissionTests
{
    private const string Url = "https://katlang.org/admission/big.kat";
    private static readonly string Module = "public X = 1\npublic Inc(x) = x + 1\n#".PadRight(295, 'p');
    private const string HistoricalUrl = "https://mods.test/big.kat";
    private const string HistoricalModule =
        "# padding comment to make this module longer than the configured source limit ................................................................\n"
        + "# more padding ...........................................................................................................................\n"
        + "public X = 1\n";
    private const int RestrictiveLimit = 250;

    public static TheoryData<int> Routes => new() { 0, 1, 2 };
    public static TheoryData<int, bool> RoutesAndPolicy => new()
    {
        { 0, false }, { 0, true }, { 1, false }, { 1, true }, { 2, false }, { 2, true },
    };

    private static string Family(string output, string body = "X", bool includeOpen = true)
        => $"F(0) = 42\nF(n) = {{ {(includeOpen ? $"open '{Url}'\n" : "")}{body} }}\n{output}";

    private static string HistoricalWitness(bool demand)
        => $"F(0) = 0\nF(n) = {{\n  open '{HistoricalUrl}'\n  X + randomInt(0, 1000)\n}}\n"
            + $"G(x, y) = {(demand ? "x + y" : "y")}\nG({{ F(1) }}, randomInt(0, 1000))\n";

    [Theory]
    [MemberData(nameof(RoutesAndPolicy))]
    public async Task HistoricalPv50_UnusedFirstArgumentKeepsFirstSeededDraw_WithoutSourceWork(int route, bool restrictive)
    {
        var fixture = new Fixture(route, restrictive);
        var source = HistoricalWitness(demand: false);
        Assert.Equal(124, source.Length);
        Assert.Equal(295, HistoricalModule.Length);
        var observation = await Observe(source, fixture, route);
        AssertValue(observation, 209);
        AssertNoSourceWork(observation, fixture);
    }

    [Theory]
    [MemberData(nameof(RoutesAndPolicy))]
    public async Task DemandedDeferredSource_IsAdmittedOrRefused_WithoutAlternativeSeededSuccess(int route, bool restrictive)
    {
        var fixture = new Fixture(route, restrictive);
        var observation = await Observe(HistoricalWitness(demand: true), fixture, route);
        if (restrictive) AssertRefusal(observation);
        else AssertValue(observation, 921);
        Assert.Equal(1, fixture.Fetches);
        AssertMaterialization(observation, ready: !restrictive, attempts: 1);
    }

    public static TheoryData<int, string> UnusedSupplies
    {
        get
        {
            var data = new TheoryData<int, string>();
            foreach (var route in new[] { 0, 1, 2 })
                foreach (var output in new[]
                {
                    "Ignore(x) = 42\nIgnore(F(1))",
                    "Ignore(x) = 42\nIgnore({ F(1) })",
                    "Ignore(x) = 42\nA = F\nIgnore(A(1))",
                    "Ignore(*xs) = 42\nIgnore(F(1), 2)",
                    "Pick(0, x) = 42\nPick(n, x) = 99\nPick(0, F(1))",
                }) data.Add(route, output);
            return data;
        }
    }

    [Theory]
    [MemberData(nameof(UnusedSupplies))]
    public async Task UnusedDeferredSupply_PerformsNoAcquisitionOrMaterialization(int route, string output)
    {
        var fixture = new Fixture(route, restrictive: true);
        var observation = await Observe(Family(output), fixture, route);
        AssertValue(observation, 42);
        AssertNoSourceWork(observation, fixture);
    }

    public static TheoryData<int, bool, bool> IfSelections
    {
        get
        {
            var data = new TheoryData<int, bool, bool>();
            foreach (var route in new[] { 0, 1, 2 })
                foreach (var condition in new[] { false, true })
                    foreach (var deferredWhenTrue in new[] { false, true })
                        data.Add(route, condition, deferredWhenTrue);
            return data;
        }
    }

    [Theory]
    [MemberData(nameof(IfSelections))]
    public async Task If_OnlyTheSelectedSuppliedComputationRequiresDeferredSource(int route, bool condition, bool deferredWhenTrue)
    {
        var alternatives = deferredWhenTrue ? "F(1), 42" : "42, F(1)";
        var fixture = new Fixture(route, restrictive: true);
        var observation = await Observe(Family($"if({condition.ToString().ToLowerInvariant()}, {alternatives})"), fixture, route);
        if (condition == deferredWhenTrue)
        {
            AssertRefusal(observation);
            Assert.Equal(1, fixture.Fetches);
            AssertMaterialization(observation, ready: false, attempts: 1);
        }
        else
        {
            AssertValue(observation, 42);
            AssertNoSourceWork(observation, fixture);
        }
    }

    [Theory]
    [MemberData(nameof(RoutesAndPolicy))]
    public async Task Family_AnUnselectedRegionDoesNoWork_AndASelectedRefusalIsRaised(int route, bool selected)
    {
        var fixture = new Fixture(route, restrictive: true);
        var observation = await Observe(Family(selected ? "F(1)" : "F(0)"), fixture, route);
        if (selected)
        {
            AssertRefusal(observation);
            Assert.Equal(1, fixture.Fetches);
        }
        else
        {
            AssertValue(observation, 42);
            AssertNoSourceWork(observation, fixture);
        }
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task RequiredAdmissionFailure_IsNotAPatternNonMatch_AndStopsFollowingEffects(int route)
    {
        var fixture = new Fixture(route, restrictive: true);
        var source = Family("Pick(0) = 42\nPick(n) = 99\nTick(), Pick(F(1)), Tick()");
        var observation = await Observe(source, fixture, route);
        AssertRefusal(observation);
        Assert.Equal(1, fixture.Fetches);
        Assert.Equal(["tick", "fetch"], fixture.Events);
    }

    [Theory]
    [MemberData(nameof(RoutesAndPolicy))]
    public async Task Forwarding_TransportsTheDeferredCell_AndOnlyTargetValueDemandCompilesIt(int route, bool demand)
    {
        var fixture = new Fixture(route, restrictive: true);
        var source = Family($"Target(x) = {(demand ? "x" : "42")}\nForward(x) = Target\nForward(F(1))");
        var observation = await Observe(source, fixture, route);
        if (demand) { AssertRefusal(observation); Assert.Equal(1, fixture.Fetches); }
        else { AssertValue(observation, 42); AssertNoSourceWork(observation, fixture); }
    }

    [Theory]
    [MemberData(nameof(RoutesAndPolicy))]
    public async Task KnownFamilyCallableIdentity_NeedsNoDeferredBodyCompilation_UntilInvocation(int route, bool invoke)
    {
        var fixture = new Fixture(route, restrictive: true);
        var output = invoke ? "Apply(fn, x) = fn(x)\nApply(F, 1)" : "Ignore(fn) = 42\nIgnore(F)";
        var observation = await Observe(Family(output), fixture, route);
        if (invoke) { AssertRefusal(observation); Assert.Equal(1, fixture.Fetches); }
        else { AssertValue(observation, 42); AssertNoSourceWork(observation, fixture); }
    }

    [Theory]
    [MemberData(nameof(RoutesAndPolicy))]
    public async Task DeferredModuleCallableMember_RequiresSourceDeclarations_WithoutZeroArgumentValueDemand(int route, bool restrictive)
    {
        var fixture = new Fixture(route, restrictive);
        var body = $"M = load('{Url}')\nApply(fn, x) = fn(x)\nApply(M.Inc, 3)";
        var observation = await Observe(Family("F(1)", body, includeOpen: false), fixture, route);
        if (restrictive) AssertRefusal(observation);
        else AssertValue(observation, 4);
        Assert.Equal(1, fixture.Fetches);
        AssertMaterialization(observation, ready: !restrictive, attempts: 1);
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task ArbitrarySpread_RequiresDeferredValueToFormSupply_BeforeIgnoringCalleeRuns(int route)
    {
        var fixture = new Fixture(route, restrictive: true);
        var observation = await Observe(Family("Ignore(*xs) = Tick()\nIgnore(F(1)*)"), fixture, route);
        AssertRefusal(observation);
        Assert.Equal(["fetch"], fixture.Events);
        AssertMaterialization(observation, ready: false, attempts: 1);
    }

    [Theory]
    [MemberData(nameof(RoutesAndPolicy))]
    public async Task KnownCollectorSlice_TransfersCellsWithoutCompilingTheirDeferredValues(int route, bool explicitOpen)
    {
        var forwarding = explicitOpen ? "Ignore(xs*)" : "Ignore";
        var fixture = new Fixture(route, restrictive: true);
        var observation = await Observe(Family($"Ignore(*xs) = 42\nForward(*xs) = {forwarding}\nForward(F(1))"), fixture, route);
        AssertValue(observation, 42);
        AssertNoSourceWork(observation, fixture);
    }

    [Theory]
    [MemberData(nameof(RoutesAndPolicy))]
    public async Task SelectedCompilationUnit_ProcessesItsStaticImport_EvenWhenNoMemberValueIsUsed(int route, bool restrictive)
    {
        var fixture = new Fixture(route, restrictive);
        var observation = await Observe(Family("F(1)", $"M = load('{Url}')\n42", includeOpen: false), fixture, route);
        if (restrictive) AssertRefusal(observation);
        else AssertValue(observation, 42);
        Assert.Equal(1, fixture.Fetches);
    }

    [Fact]
    public async Task SourceRefusal_RetainsInitialParseFailureAndDeferredEvalFailurePhases()
    {
        var eager = new Fixture(0, restrictive: true);
        var initial = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync($"M = load('{Url}')\n42", eager.Options));
        var initialError = Assert.Single(initial.Errors);
        Assert.Equal(KatLangErrorCode.SourceLengthExceeded, initialError.Code);
        Assert.False(initialError.IsResourceLimit);
        Assert.Equal(1, eager.Fetches);

        var deferred = new Fixture(0, restrictive: true);
        var source = Family("F(1)");
        await SourceProvenance.ParseValidAsync(source, deferred.Options);
        var selected = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(source, deferred.Options));
        var selectedError = Assert.Single(selected.Errors);
        Assert.Equal(KatLangErrorCode.SourceLengthExceeded, selectedError.Code);
        Assert.False(selectedError.IsResourceLimit);
        Assert.Equal(2, Assert.NotNull(selectedError.Span).Start.Line);
        Assert.Equal(1, deferred.Fetches);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task PreCancelledRun_PerformsNoDeferredAcquisition(bool sourceCancellation)
    {
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var fetches = 0;
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = sourceCancellation ? cancellation.Token : default,
            EvaluationCancellationToken = sourceCancellation ? default : cancellation.Token,
            DownloadCode = (_, _) => { fetches++; return ValueTask.FromResult(Module); },
        };
        var error = await Assert.ThrowsAsync<OperationCanceledException>(() => KatLangEngine.RunAsync(Family("F(1)"), options));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal(0, fetches);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task CancellationDuringRequiredAcquisition_PropagatesOriginalToken_AndPublishesNoBody(bool sourceCancellation)
    {
        using var cancellation = new CancellationTokenSource();
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var aborted = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var fetches = 0;
        var effects = 0;
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = sourceCancellation ? cancellation.Token : default,
            HostOperations = HostOperations.Create(HostOperation.Create("Tick", (_, _) => { effects++; return new Result.Atom(42); })),
            DownloadCode = async (_, token) =>
            {
                fetches++;
                entered.SetResult();
                try { await Task.Delay(Timeout.Infinite, token); }
                finally { aborted.SetResult(); }
                return Module;
            },
        };
        var provenance = await SourceProvenance.ParseValidAsync(Family("F(1), Tick()"), options);
        var region = Region(provenance.Root);
        var pending = Evaluator.RunCountedAsync(new Expr.AlgorithmExpr(provenance.Root), new SuspendingAsyncZeroArgPropertyResultCache(),
            hostOperations: options.HostOperations, cancellationToken: sourceCancellation ? default : cancellation.Token).AsTask();
        await entered.Task.WaitAsync(TimeSpan.FromSeconds(10));
        cancellation.Cancel();
        var error = await Assert.ThrowsAsync<OperationCanceledException>(async () => await pending.WaitAsync(TimeSpan.FromSeconds(10)));
        await aborted.Task.WaitAsync(TimeSpan.FromSeconds(10));
        await region.Loader.MaterializationGate.WaitAsync().WaitAsync(TimeSpan.FromSeconds(10));
        region.Loader.MaterializationGate.Release();
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal(1, fetches);
        Assert.Equal(0, effects);
        Assert.Equal(1, region.MaterializationAttempts);
        Assert.False(region.IsMaterialized);
        Assert.Equal(0, region.Loader.CachedModuleCount);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ReadyCompilationBody_IsPreserved_WhileOnlyEvaluationCancellationStopsFurtherLanguageWork(bool sourceCancellation)
    {
        using var cancellation = new CancellationTokenSource();
        var fetches = 0;
        var options = new RunOptions
        {
            SourceProcessingCancellationToken = sourceCancellation ? cancellation.Token : default,
            DownloadCode = (_, _) => { fetches++; return ValueTask.FromResult(Module); },
        };
        var provenance = await SourceProvenance.ParseValidAsync(Family("F(1)"), options);
        var expression = new Expr.AlgorithmExpr(provenance.Root);
        var region = Region(provenance.Root);
        var first = await Evaluator.RunCountedAsync(expression, new PassThroughAsyncZeroArgPropertyResultCache());
        Assert.False(first.IsError);
        Assert.Equal([(Decimal128)1], first.Value.Value.ToAtoms());
        cancellation.Cancel();
        if (sourceCancellation)
        {
            var second = await Evaluator.RunCountedAsync(expression, new SuspendingAsyncZeroArgPropertyResultCache());
            Assert.False(second.IsError);
            Assert.Equal(first.Value, second.Value);
        }
        else
        {
            var error = await Assert.ThrowsAsync<OperationCanceledException>(async () => await Evaluator.RunCountedAsync(
                expression, new SuspendingAsyncZeroArgPropertyResultCache(), cancellationToken: cancellation.Token));
            Assert.Equal(cancellation.Token, error.CancellationToken);
        }
        Assert.True(region.IsMaterialized);
        Assert.Equal(1, region.MaterializationAttempts);
        Assert.Equal(1, fetches);
    }

    private sealed class Fixture(int route, bool restrictive)
    {
        public int Fetches { get; private set; }
        public List<string> Events { get; } = [];
        public RunOptions Options => new()
        {
            RandomSeed = 3,
            AllowedHosts = ["katlang.org", "mods.test"],
            SourceProcessingLimits = restrictive ? new SourceProcessingLimits { MaxSourceLength = RestrictiveLimit } : null,
            HostOperations = HostOperations.Create(HostOperation.Create("Tick", (_, _) => { Events.Add("tick"); return new Result.Atom(42); })),
            DownloadCode = async (url, _) =>
            {
                Fetches++;
                Events.Add("fetch");
                if (route == 2) await Task.Yield();
                return url == HistoricalUrl ? HistoricalModule : Module;
            },
        };
    }

    private sealed record Observation(Result? Value, KatLangErrorCode? Code, bool IsResourceLimit, DeferredModuleRegion? Region);

    private static async Task<Observation> Observe(string source, Fixture fixture, int route)
    {
        Assert.True(source.Length < RestrictiveLimit);
        Assert.True(Module.Length > RestrictiveLimit);
        var options = fixture.Options;
        var provenance = await SourceProvenance.ParseValidAsync(source, options);
        Assert.Equal(0, fixture.Fetches);
        if (route == 0)
        {
            // The engine owns its private parse. Region counters below observe the actual tree
            // only on the direct counted routes; the engine's public outcome/fetches are pinned.
            var run = await KatLangEngine.RunAsync(source, options);
            if (run is RunResult.Success success) return new(success.Value, null, false, null);
            var failure = Assert.IsType<RunResult.EvalFailure>(run);
            var error = Assert.Single(failure.Errors);
            return new(null, error.Code, error.IsResourceLimit, null);
        }
        IZeroArgPropertyResultCache cache = route == 1 ? new PassThroughAsyncZeroArgPropertyResultCache() : new SuspendingAsyncZeroArgPropertyResultCache();
        var result = await Evaluator.RunCountedAsync(new Expr.AlgorithmExpr(provenance.Root), cache, hostOperations: options.HostOperations, randomSeed: 3);
        if (result.IsError) return new(null, result.Error.Code, result.Error.IsResourceLimit, Region(provenance.Root));
        Assert.Equal(1, result.Value.EmittedCount);
        return new(result.Value.Value, null, false, Region(provenance.Root));
    }

    private static DeferredModuleRegion Region(Algorithm.User root)
    {
        var region = Assert.IsType<Algorithm.Conditional>(root.Properties.Single(p => p.Name == "F").Value).Branches[1].Body.DeferredRegion;
        Assert.NotNull(region);
        return region;
    }

    private static void AssertValue(Observation observation, int expected)
    {
        Assert.Null(observation.Code);
        Assert.NotNull(observation.Value);
        Assert.Equal([(Decimal128)expected], observation.Value.ToAtoms());
    }

    private static void AssertRefusal(Observation observation)
    {
        Assert.Null(observation.Value);
        Assert.Equal(KatLangErrorCode.SourceLengthExceeded, observation.Code);
        Assert.False(observation.IsResourceLimit);
    }

    private static void AssertNoSourceWork(Observation observation, Fixture fixture)
    {
        Assert.Equal(0, fixture.Fetches);
        Assert.Empty(fixture.Events);
        AssertMaterialization(observation, ready: false, attempts: 0);
    }

    private static void AssertMaterialization(Observation observation, bool ready, int attempts)
    {
        if (observation.Region is not { } region) return;
        Assert.Equal(ready, region.IsMaterialized);
        Assert.Equal(attempts, region.MaterializationAttempts);
    }
}
