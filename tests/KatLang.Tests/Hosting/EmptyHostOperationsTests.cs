using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests.Hosting;

/// <summary>
/// Pins that the EMPTY host-operation configuration (<c>HostOperations.Create()</c>
/// with zero operations) behaves observably identically to the null / no-host
/// configuration: same engine results (sync and async), same evaluator results through
/// the public host-operation overloads, the synchronous fast path kept (routing never
/// selects the async twin), implicit-parameter detection unchanged, and one shared
/// instance safe across concurrent runs. The empty set is constructible public API,
/// so this equivalence is a contract, not an accident of "null means none".
/// </summary>
public class EmptyHostOperationsTests
{
    /// <summary>
    /// A program touching the three name-resolution families an extended prelude could
    /// disturb: a Math member, an ordinary user property, and an implicit parameter
    /// (the unresolved <c>unknownName</c> inside <c>K</c> is promoted to a parameter
    /// and supplied at the call site).
    /// </summary>
    private const string MixedSource = "A = Math.Abs(0 - 2)\nF(x) = x * 10\nK = unknownName + 1\nA, F(A), K(41)";

    private static RunOptions EmptyOptions() => new() { HostOperations = HostOperations.Create() };

    [Fact]
    public void EmptySet_HasNoOperationsNoAsyncFlagAndNoDispatchEntries()
    {
        var empty = HostOperations.Create();

        Assert.Empty(empty.Operations);
        Assert.False(empty.ContainsAsynchronousOperations);
        Assert.False(empty.TryGetByNativeName(HostOperations.NativeNamePrefix + "Anything", out _));
    }

    [Fact]
    public void EngineRun_EmptyConfiguration_MatchesNullConfiguration()
    {
        var baseline = KatLangEngine.Run(MixedSource);
        var configured = KatLangEngine.Run(MixedSource, EmptyOptions());

        Assert.IsType<RunResult.Success>(baseline);
        Assert.Equal(baseline.GetType(), configured.GetType());
        Assert.Equal(baseline.ToDisplayString(), configured.ToDisplayString());
        Assert.Equal(
            KatLangEngine.EvaluateToString(MixedSource),
            KatLangEngine.EvaluateToString(MixedSource, EmptyOptions()));
    }

    [Fact]
    public async Task EngineRunAsync_EmptyConfiguration_KeepsSynchronousFastPathAndResult()
    {
        // No async-capable component is configured, so the engine's async entry must
        // execute the synchronous pipeline inline: the returned task is already
        // complete when the call returns, and the outcome is the sync outcome.
        var task = KatLangEngine.RunAsync(MixedSource, EmptyOptions());
        Assert.True(task.IsCompletedSuccessfully);
        var asyncResult = await task;

        var baseline = KatLangEngine.Run(MixedSource);
        Assert.Equal(baseline.GetType(), asyncResult.GetType());
        Assert.Equal(baseline.ToDisplayString(), asyncResult.ToDisplayString());

        var stringTask = KatLangEngine.EvaluateToStringAsync(MixedSource, EmptyOptions());
        Assert.True(stringTask.IsCompletedSuccessfully);
        Assert.Equal(KatLangEngine.EvaluateToString(MixedSource), await stringTask);
    }

    [Fact]
    public async Task EvaluatorHostOverloads_EmptyConfiguration_MatchPlainOverloads()
    {
        var root = SourceProvenance.ParseValid(MixedSource).Root;
        var empty = HostOperations.Create();

        var plain = Evaluator.Run(new Expr.AlgorithmExpr(root));
        var viaEmpty = Evaluator.Run(
            new Expr.AlgorithmExpr(root), empty, limits: null, CancellationToken.None);

        Assert.False(plain.IsError);
        Assert.False(viaEmpty.IsError);
        Assert.Equal(plain.Value, viaEmpty.Value, Result.ValueComparer);

        // The async host-operation overload with the empty set keeps the synchronous
        // fast path — routing never selects the async twin — and matches too.
        var asyncTask = Evaluator.RunAsync(
            new Expr.AlgorithmExpr(root), empty, limits: null, CancellationToken.None);
        Assert.True(asyncTask.IsCompletedSuccessfully);
        var viaEmptyAsync = await asyncTask;
        Assert.False(viaEmptyAsync.IsError);
        Assert.Equal(plain.Value, viaEmptyAsync.Value, Result.ValueComparer);
    }

    [Fact]
    public void ImplicitParameterDetection_EmptyConfiguration_Unchanged()
    {
        // An unresolved bare name must still become an implicit parameter under the
        // empty configuration: the argumentless report row fails identically to the
        // null configuration (mirrors the configured-vs-unconfigured contrast pinned
        // by HostOperationApiTests).
        var baseline = KatLangEngine.Run("Data * 2");
        var configured = KatLangEngine.Run("Data * 2", EmptyOptions());

        Assert.False(baseline.IsSuccess);
        Assert.Equal(baseline.GetType(), configured.GetType());
        Assert.Equal(baseline.ToDisplayString(), configured.ToDisplayString());
    }

    [Fact]
    public void OneEmptyInstance_IsSafeAcrossConcurrentRuns()
    {
        var empty = HostOperations.Create();
        var baseline = KatLangEngine.EvaluateToString(MixedSource);

        var results = new string[8];
        Parallel.For(0, results.Length, i =>
            results[i] = KatLangEngine.EvaluateToString(MixedSource, new RunOptions { HostOperations = empty }));

        Assert.All(results, r => Assert.Equal(baseline, r));
    }

    // ── Corpus differential: the empty configuration changes nothing ────────

    private static readonly IReadOnlyDictionary<string, SpecCase> SpecById =
        LanguageSpecCorpus.AllCases().ToDictionary(static c => c.Id, StringComparer.Ordinal);

    [Theory]
    [MemberData(nameof(HostOperationApiTests.SpecCaseIds), MemberType = typeof(HostOperationApiTests))]
    public void EmptyConfiguration_ChangesNoProgramOutcome(string caseId)
    {
        var source = SpecById[caseId].Source;

        var baseline = KatLangEngine.Run(source);
        var configured = KatLangEngine.Run(source, EmptyOptions());

        Assert.Equal(baseline.GetType(), configured.GetType());
        Assert.Equal(baseline.ToDisplayString(), configured.ToDisplayString());
    }
}
