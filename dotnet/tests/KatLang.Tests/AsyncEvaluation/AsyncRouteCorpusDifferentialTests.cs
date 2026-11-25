using System.Globalization;
using KatLang.ParserFuzz;
using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// Every program of the four differential corpora through the PUBLIC asynchronous route — an asynchronous host
/// operation configured, which routes the run through the async twin family (<c>RequiresAsyncEvaluationPath</c>;
/// <see cref="AsyncRouteDecisionTests"/>) — compared with the synchronous route on the same program and the same
/// host-operation names, in the neutral encoding the corpora share with the Lean artifacts.
///
/// <para><b>Routes.</b> A SOURCE program runs through <see cref="KatLangEngine.Run(string, RunOptions?)"/> with a
/// synchronous operation and through <see cref="KatLangEngine.RunAsync"/> with an asynchronous operation of the same
/// name and arity, so both runs see the same ambient prelude. A HOST-BUILT tree (the host-parent corpus and the
/// explorer's internal-node cases; no source form exists) runs through the low-level
/// <c>Evaluator.Run</c>/<c>Evaluator.RunAsync(Expr, HostOperations, …)</c> pair the same way. The explorer,
/// language-spec and host-parent programs configure a probe operation (<see cref="ProbeName"/>) that they never
/// demand: it only selects the twin route (a demanded probe genuinely suspends; see
/// <see cref="TheAsynchronousProbe_SuspendsWhenDemanded_AndAgreesWithTheSynchronousRoute"/>); the SEM-2B generated
/// programs configure their own <c>trace</c>/<c>wait</c> fixture (<see cref="MetamorphicHostFixture"/>), whose
/// asynchronous <c>wait</c> GENUINELY suspends the run and is released in arrival order, and their host events are
/// compared too.</para>
///
/// <para><b>Comparison.</b> Outcome variant, value (<see cref="SemanticExplorerHarness.Neutral"/>), emitted count,
/// numeric atoms, every diagnostic's code, span and message, the display text, and — for evaluation failures —
/// the structured error through <see cref="DifferentialErrors.RequireAgreement"/>. Any difference is a finding,
/// except a Q-09a STACK-HEADROOM verdict (<see cref="KatLangErrorCode.EvaluationStackExhausted"/> on one route) for
/// a case listed in <see cref="StackHeadroomExclusions"/>: the twin route may hop to a fresh stack and go deeper,
/// or stop at a shared synchronous helper's backstop sooner, and where that happens is host-dependent.</para>
///
/// <para><b>Coverage before this suite.</b> <see cref="AsyncTwinDifferentialTests"/> ran the language-spec and
/// explorer SOURCE programs through the twin family by an async-capable property cache
/// (<c>Evaluator.RunCountedObservedAsync</c>), never through <see cref="KatLangEngine.RunAsync"/> or a host
/// operation, and not the explorer's internal-node cases; the host-parent harness ran its trees through a
/// suspending async cache; SEM-2B ran its <c>async-twin</c> profile on every valid BASE program and its
/// <c>engine-run-async</c> profile only on a subset (waiting cases, every fourth case, invalid cases), and its
/// transformation members only synchronously.</para>
/// </summary>
public class AsyncRouteCorpusDifferentialTests
{
    /// <summary>The unused probe operation that routes a source program through the twins.</summary>
    internal const string ProbeName = "asyncRouteProbe";

    /// <summary>
    /// Q-09a stack-headroom exclusions by exact program id, each with a reason. Only a deep program whose routes
    /// differ by an <see cref="KatLangErrorCode.EvaluationStackExhausted"/> verdict belongs here; any other
    /// difference is a finding. Empty: no corpus program reaches the host-stack backstop on either route.
    /// </summary>
    internal static readonly IReadOnlyDictionary<string, string> StackHeadroomExclusions =
        new Dictionary<string, string>(StringComparer.Ordinal);

    private static readonly IReadOnlyDictionary<string, SpecCase> SpecById =
        LanguageSpecCorpus.AllCases().ToDictionary(static c => c.Id, StringComparer.Ordinal);

    private static readonly IReadOnlyDictionary<string, ExplorerCase> ExplorerById =
        SemanticExplorerCorpus.AllCases().ToDictionary(static c => c.Id, StringComparer.Ordinal);

    private static readonly IReadOnlyDictionary<string, InternalNodeCase> InternalNodeById =
        SemanticExplorerCorpus.InternalNodeCases().ToDictionary(static c => c.Id, StringComparer.Ordinal);

    private static readonly IReadOnlyDictionary<string, SemanticMember> GeneratedById =
        SemanticCorpus.All()
            .SelectMany(static c => c.Members.Select(m => (Id: c.CaseId + "/" + m.Role, Member: m)))
            .ToDictionary(static p => p.Id, static p => p.Member, StringComparer.Ordinal);

    private static readonly IReadOnlyDictionary<string, HostParentCase> HostParentById =
        HostParentDifferentialCorpus.AllCases().ToDictionary(static c => c.Id, StringComparer.Ordinal);

    public static TheoryData<string> SpecCaseIds() => Ids(SpecById.Keys);

    public static TheoryData<string> ExplorerCaseIds() => Ids(ExplorerById.Keys);

    public static TheoryData<string> InternalNodeCaseIds() => Ids(InternalNodeById.Keys);

    public static TheoryData<string> GeneratedProgramIds() => Ids(GeneratedById.Keys);

    public static TheoryData<string> HostParentCaseIds() => Ids(HostParentById.Keys);

    [Theory]
    [MemberData(nameof(SpecCaseIds))]
    public async Task LanguageSpecCase_RunAsync_MatchesRun(string caseId)
        => await AssertSourceRoutesAgree("spec:" + caseId, SpecById[caseId].Source);

    [Theory]
    [MemberData(nameof(ExplorerCaseIds))]
    public async Task ExplorerCase_RunAsync_MatchesRun(string caseId)
        => await AssertSourceRoutesAgree("explorer:" + caseId, ExplorerById[caseId].Source);

    [Theory]
    [MemberData(nameof(InternalNodeCaseIds))]
    public async Task ExplorerInternalNodeCase_EvaluatorRunAsync_MatchesRun(string caseId)
    {
        var root = new Expr.AlgorithmExpr(new Algorithm.User(
            Parent: null, ParameterPatterns: [], Opens: [], Properties: [], Output: [InternalNodeById[caseId].RootOutput()]));
        await AssertTreeRoutesAgree("explorer-internal:" + caseId, root);
    }

    [Theory]
    [MemberData(nameof(HostParentCaseIds))]
    public async Task HostParentCase_EvaluatorRunAsync_MatchesRun(string caseId)
        => await AssertTreeRoutesAgree("host-parent:" + caseId, HostParentById[caseId].Program);

    /// <summary>
    /// SEM-2B: every member (base and transformations) of every generated case, valid or not, through
    /// <see cref="KatLangEngine.RunAsync"/> with the GATED fixture (each demanded <c>wait</c> genuinely suspends),
    /// against <see cref="KatLangEngine.Run(string, RunOptions?)"/> with the synchronous fixture; the host events
    /// must agree too.
    /// </summary>
    [Theory]
    [MemberData(nameof(GeneratedProgramIds))]
    public void SemanticGeneratedProgram_RunAsyncWithGenuineSuspension_MatchesRun(string programId)
    {
        var source = GeneratedById[programId].Source;
        var id = "generated:" + programId;

        var syncHost = MetamorphicHostFixture.Synchronous();
        var sync = KatLangEngine.Run(source, new RunOptions { HostOperations = syncHost.Operations, EvaluationLimits = SemanticProfiles.Limits });

        var asyncHost = MetamorphicHostFixture.Gated();
        var asynchronous = asyncHost.Drive(
            token => KatLangEngine.RunAsync(source, new RunOptions
            {
                HostOperations = asyncHost.Operations,
                EvaluationLimits = SemanticProfiles.Limits,
                EvaluationCancellationToken = token,
            }),
            MetamorphicHostFixture.DefaultWatchdog);

        RequireAgreement(id, sync, asynchronous);
        Assert.True(syncHost.Events.SequenceEqual(asyncHost.Events, StringComparer.Ordinal),
            $"ASYNC-ROUTE DIVERGENCE {id}: host events differ — sync [{string.Join(", ", syncHost.Events)}], async [{string.Join(", ", asyncHost.Events)}].");
    }

    /// <summary>The exclusions are exact ids of corpus programs, each with a reason.</summary>
    [Fact]
    public void StackHeadroomExclusions_NameCorpusProgramsWithReasons()
    {
        var all = AllProgramIds().ToHashSet(StringComparer.Ordinal);
        Assert.All(StackHeadroomExclusions, static pair => Assert.False(string.IsNullOrWhiteSpace(pair.Value), pair.Key));
        Assert.All(StackHeadroomExclusions.Keys, key => Assert.Contains(key, all));
    }

    /// <summary>
    /// The suite enumerates every program of the four corpora (ids are unique across them), and each corpus
    /// contributes programs.
    /// </summary>
    [Fact]
    public void EveryCorpusProgram_IsEnumerated()
    {
        var ids = AllProgramIds().ToList();
        Assert.Equal(ids.Count, ids.Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(LanguageSpecCorpus.AllCases().Count, SpecById.Count);
        Assert.Equal(SemanticExplorerCorpus.AllCases().Count, ExplorerById.Count);
        Assert.Equal(SemanticExplorerCorpus.InternalNodeCases().Count, InternalNodeById.Count);
        Assert.Equal(SemanticCorpus.All().Sum(static c => c.Members.Length), GeneratedById.Count);
        Assert.Equal(HostParentDifferentialCorpus.AllCases().Count, HostParentById.Count);
        Assert.All(new[] { SpecById.Count, ExplorerById.Count, InternalNodeById.Count, GeneratedById.Count, HostParentById.Count },
            static count => Assert.True(count > 0));
    }

    /// <summary>
    /// Each asynchronous route's configuration contains an asynchronous operation, so the route rule
    /// (<c>RequiresAsyncEvaluationPath</c>) sends it through the twins; each synchronous route's contains none.
    /// </summary>
    [Fact]
    public void TheAsynchronousConfigurations_SelectTheTwinRoute()
    {
        Assert.True(AsynchronousProbe().ContainsAsynchronousOperations);
        Assert.True(MetamorphicHostFixture.Gated().Operations.ContainsAsynchronousOperations);
        Assert.False(SynchronousProbe().ContainsAsynchronousOperations);
        Assert.False(MetamorphicHostFixture.Synchronous().Operations.ContainsAsynchronousOperations);
    }

    /// <summary>
    /// The probe configuration the source and tree corpora use suspends a DEMANDED call: the run is held at the
    /// operation (not completed) until released, then agrees with the synchronous route. (The corpus programs never
    /// demand the probe, so for them it only selects the twin route; SEM-2B's gated <c>wait</c> suspends inside the
    /// generated programs themselves.)
    /// </summary>
    [Fact]
    public async Task TheAsynchronousProbe_SuspendsWhenDemanded_AndAgreesWithTheSynchronousRoute()
    {
        var limit = TimeSpan.FromSeconds(30);
        var source = ProbeName + "(41) + 1";
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var run = KatLangEngine.RunAsync(source, new RunOptions
        {
            HostOperations = AsynchronousProbe(() =>
            {
                reached.TrySetResult();
                return release.Task;
            }),
        });
        await reached.Task.WaitAsync(limit);
        Assert.False(run.IsCompleted, "the demanded asynchronous probe did not hold the run");
        release.SetResult();
        var asynchronous = await run.WaitAsync(limit);

        var sync = KatLangEngine.Run(source, new RunOptions { HostOperations = SynchronousProbe() });
        Assert.IsType<RunResult.Success>(sync);
        RequireAgreement("probe:demanded", sync, asynchronous);

        // The yielding form the corpora configure agrees too.
        await AssertSourceRoutesAgree("probe:demanded-yield", source);
    }

    // ── Routes ──────────────────────────────────────────────────────────────

    private static HostOperations SynchronousProbe()
        => HostOperations.Create(HostOperation.Create(ProbeName, static (args, _) => args[0], "x"));

    /// <summary>
    /// The asynchronous probe: a demanded call GENUINELY suspends (it yields, or awaits <paramref name="hold"/>) before
    /// returning its argument. The corpus programs never demand it; it is configured so the route rule selects the twins.
    /// </summary>
    private static HostOperations AsynchronousProbe(Func<Task>? hold = null)
        => HostOperations.Create(HostOperation.CreateAsync(ProbeName, async (args, _) =>
        {
            if (hold is null)
                await Task.Yield();
            else
                await hold();
            return args[0];
        }, "x"));

    private static async Task AssertSourceRoutesAgree(string id, string source)
    {
        var sync = KatLangEngine.Run(source, new RunOptions { HostOperations = SynchronousProbe() });
        var asynchronous = await AsyncEvaluationHarness.Complete(
            new ValueTask<RunResult>(KatLangEngine.RunAsync(source, new RunOptions { HostOperations = AsynchronousProbe() })));
        RequireAgreement(id, sync, asynchronous);
    }

    private static async Task AssertTreeRoutesAgree(string id, Expr program)
    {
        var sync = Evaluator.Run(program, SynchronousProbe(), limits: null, randomSeed: null, CancellationToken.None);
        var asynchronous = await AsyncEvaluationHarness.Complete(new ValueTask<EvalResult<Result>>(
            Evaluator.RunAsync(program, AsynchronousProbe(), limits: null, randomSeed: null, CancellationToken.None)));

        var left = AsyncEvaluationHarness.NeutralOf(sync);
        var right = AsyncEvaluationHarness.NeutralOf(asynchronous);
        if (left == right)
        {
            if (sync.IsError)
                DifferentialErrors.RequireAgreement(id, sync.Error, asynchronous.Error);
            else
                Assert.True(Result.ValueComparer.Equals(sync.Value, asynchronous.Value), $"{id}: values differ structurally");
            return;
        }

        var headroom = IsStackHeadroom(sync) || IsStackHeadroom(asynchronous);
        if (headroom && StackHeadroomExclusions.ContainsKey(id))
            return;
        Assert.Fail($"ASYNC-ROUTE DIVERGENCE {id}: sync {left} / async {right}" + HeadroomHint(headroom));
    }

    // ── Comparison ──────────────────────────────────────────────────────────

    private static void RequireAgreement(string id, RunResult sync, RunResult asynchronous)
    {
        var left = NeutralOf(sync);
        var right = NeutralOf(asynchronous);
        if (left == right)
        {
            Assert.Equal(sync.ToDisplayString(), asynchronous.ToDisplayString());
            if (sync is RunResult.EvalFailure syncFailure && asynchronous is RunResult.EvalFailure asyncFailure)
            {
                foreach (var (expected, actual) in syncFailure.Errors.Zip(asyncFailure.Errors))
                {
                    if (expected.Source is { } expectedError && actual.Source is { } actualError)
                        DifferentialErrors.RequireAgreement(id, expectedError, actualError);
                    else
                        Assert.Equal(expected.Source is null, actual.Source is null);
                }
            }

            if (sync is RunResult.Success syncSuccess && asynchronous is RunResult.Success asyncSuccess)
                Assert.True(Result.ValueComparer.Equals(syncSuccess.Value, asyncSuccess.Value), $"{id}: values differ structurally");
            return;
        }

        var headroom = IsStackHeadroom(sync) || IsStackHeadroom(asynchronous);
        if (headroom && StackHeadroomExclusions.ContainsKey(id))
            return;
        Assert.Fail($"ASYNC-ROUTE DIVERGENCE {id}:\n  sync  {left}\n  async {right}" + HeadroomHint(headroom));
    }

    /// <summary>The neutral engine outcome: variant, value, count, atoms, and every diagnostic's code, span and message.</summary>
    internal static string NeutralOf(RunResult run)
        => run switch
        {
            RunResult.Success success =>
                $"ok raw={SemanticExplorerHarness.Neutral(success.Value)} n={success.EmittedCount} atoms=[{string.Join(", ", success.Atoms.Select(static a => a.ToString()))}]",
            RunResult.NoProgramOutput none => "no-output " + Describe(none.Diagnostic),
            RunResult.ParseFailure parse => "parse-failure " + string.Join(" | ", parse.Errors.Select(Describe)),
            RunResult.EvalFailure failure => "eval-failure " + string.Join(" | ", failure.Errors.Select(Describe)),
        };

    private static string Describe(KatLangError error)
        => string.Create(CultureInfo.InvariantCulture, $"{error.Code} {error.Span?.ToString() ?? "-"} {error.Message}");

    private static bool IsStackHeadroom(RunResult run)
        => run is RunResult.EvalFailure failure && failure.Errors.Any(static e => e.Code == KatLangErrorCode.EvaluationStackExhausted);

    private static bool IsStackHeadroom(EvalResult<Result> result)
        => result.IsError
            && SemanticExplorerHarness.ErrorCategory(result.Error).Contains("StackExhausted", StringComparison.OrdinalIgnoreCase);

    private static string HeadroomHint(bool headroom)
        => headroom
            ? "\n  (one route reports EvaluationStackExhausted: a Q-09a stack-headroom difference; list the id in StackHeadroomExclusions with a reason only if the program is deliberately deep)"
            : "";

    private static IEnumerable<string> AllProgramIds()
        => SpecById.Keys.Select(static k => "spec:" + k)
            .Concat(ExplorerById.Keys.Select(static k => "explorer:" + k))
            .Concat(InternalNodeById.Keys.Select(static k => "explorer-internal:" + k))
            .Concat(GeneratedById.Keys.Select(static k => "generated:" + k))
            .Concat(HostParentById.Keys.Select(static k => "host-parent:" + k));

    private static TheoryData<string> Ids(IEnumerable<string> ids)
    {
        var data = new TheoryData<string>();
        foreach (var id in ids.OrderBy(static id => id, StringComparer.Ordinal))
            data.Add(id);
        return data;
    }
}
