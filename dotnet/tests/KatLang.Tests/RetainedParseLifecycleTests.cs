using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// The lifecycle of a retained <see cref="Parser.ParseAsync"/> result whose program loads modules on
/// demand, as documented on <see cref="ParseResult"/>, <see cref="Parser.ParseAsync"/>,
/// <see cref="RunOptions.SourceProcessingCancellationToken"/> and the asynchronous evaluator entry
/// points (findings <c>lifecycle-parse-token-poisons-retained-parse</c> and
/// <c>modules-deferred-erroneous-parse-materialization-ioe</c> of the 2026-11-21 adversarial
/// investigation, baseline <c>8947d21e</c>). These pin the deferred loader's EXISTING policy, which
/// the documentation now states; none of it changed.
///
/// <para>(1) THE PARSE-TIME TOKEN STAYS AUTHORITATIVE. A clause branch whose modules load on demand is
/// compiled when evaluation first selects it, under the source-processing token the tree was parsed
/// with. Once that token is cancelled, every later selection of a branch that has not loaded yet
/// fails with an <see cref="OperationCanceledException"/> carrying it, before any module work and
/// ahead of the run's own evaluation token; branches loaded earlier and code that selects no unloaded
/// branch are unaffected. Inside one <see cref="KatLangEngine.RunAsync"/> the same token is observed
/// when evaluation selects such a branch.</para>
///
/// <para>(2) AN ERRONEOUS RESULT IS NOT A PROGRAM. The engine's source gate never evaluates it; its
/// root handed to the evaluator directly cannot compile a branch that loads on demand. Selection
/// can throw <see cref="InvalidOperationException"/> before any module work when the
/// error stopped the passes that prepare the branch (a refused signature inference), otherwise after
/// the branch's modules were loaded (downloads stay charged, a loaded module stays cached), unless a
/// module failure is met first, which is the ordinary materialization failure.</para>
///
/// <para>Every downloader is in memory and deterministic, and every wait is a hang guard, never a
/// latency claim. Host-only: Lean has no external modules.</para>
/// </summary>
public class RetainedParseLifecycleTests
{
    private const string ModuleA = "https://katlang.org/lifecycle/a.kat";
    private const string ModuleB = "https://katlang.org/lifecycle/b.kat";
    private const string Missing = "https://katlang.org/lifecycle/missing.kat";
    private const string FamilyF = $"F(0) = 0\nF(1) = {{\n    N = load('{ModuleA}')\n    N.V\n}}\n";
    private const string FamilyG = $"G(0) = 0\nG(1) = {{\n    M = load('{ModuleB}')\n    M.W\n}}\n";

    private static readonly TimeSpan HangGuard = TimeSpan.FromSeconds(30);

    private sealed class CountingDownloader
    {
        private readonly object _lock = new();
        private readonly Dictionary<string, int> _calls = new(StringComparer.Ordinal);

        public int this[string url]
        {
            get { lock (_lock) return _calls.GetValueOrDefault(url); }
        }

        public ValueTask<string> Download(string url, CancellationToken cancellationToken)
        {
            lock (_lock)
                _calls[url] = _calls.GetValueOrDefault(url) + 1;
            return url switch
            {
                ModuleA => ValueTask.FromResult("public V = 7"),
                ModuleB => ValueTask.FromResult("public W = 8"),
                _ => throw new InvalidOperationException($"404: {url}"),
            };
        }
    }

    private static DeferredModuleRegion Region(Algorithm root, string family)
    {
        var conditional = Assert.IsType<Algorithm.Conditional>(root.Properties.Single(property => property.Name == family).Value);
        return Assert.IsType<DeferredModuleRegion>(conditional.Branches[1].Body.DeferredRegion);
    }

    private static void AssertValue(EvalResult<IReadOnlyList<Decimal128>> result, int expected)
    {
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : "");
        Assert.Equal([(Decimal128)expected], result.Value);
    }

    // ── 1. The parse-time token over a retained tree ──────────────────────────

    [Fact]
    public async Task ACancelledParseToken_RefusesEveryLaterSelectionOfAnUnloadedBranch_WithThatToken()
    {
        using var parseCancellation = new CancellationTokenSource();
        using var evaluation = new CancellationTokenSource();
        var which = 0;
        var hosts = HostOperations.Create(HostOperation.Create("Which", (_, _) => new Result.Atom(Volatile.Read(ref which))));
        var downloads = new CountingDownloader();
        var options = new RunOptions
        {
            HostOperations = hosts,
            SourceProcessingCancellationToken = parseCancellation.Token,
            DownloadCode = downloads.Download,
        };
        const string sharedModuleFamily = $"H(0) = 0\nH(1) = {{ N = load('{ModuleA}')\n N.V }}\n";
        const string Program = FamilyF + FamilyG + sharedModuleFamily
            + "if(Which() == 0, F(1), if(Which() == 1, G(1), if(Which() == 2, 5, H(1))))";
        var root = (await SourceProvenance.ParseValidAsync(Program, options)).Root;
        var regionF = Region(root, "F");
        var regionG = Region(root, "G");
        Task<EvalResult<IReadOnlyList<Decimal128>>> Run(CancellationToken cancellationToken = default)
            => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(root), hosts, limits: null, randomSeed: null, cancellationToken);

        // F's branch loads while the token is live.
        AssertValue(await Run().WaitAsync(HangGuard), 7);
        Assert.True(regionF.IsMaterialized);

        parseCancellation.Cancel();

        // A branch loaded earlier, and code that selects no unloaded branch, are unaffected.
        AssertValue(await Run(evaluation.Token).WaitAsync(HangGuard), 7);
        Volatile.Write(ref which, 2);
        AssertValue(await Run(evaluation.Token).WaitAsync(HangGuard), 5);

        // G's branch can no longer load from this tree: every selection fails with the PARSE token,
        // before any module work, although the run's own token is live.
        Volatile.Write(ref which, 1);
        for (var selection = 0; selection < 2; selection++)
        {
            var cancelled = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Run(evaluation.Token).WaitAsync(HangGuard));
            Assert.Equal(parseCancellation.Token, cancelled.CancellationToken);
        }
        Assert.False(evaluation.IsCancellationRequested);
        Assert.False(regionG.IsMaterialized);
        Assert.Equal(0, regionG.MaterializationAttempts);
        Assert.Equal(0, downloads[ModuleB]);
        Assert.Equal(1, downloads[ModuleA]);

        // H needs compilation even though F has already fetched the module that H uses.
        Volatile.Write(ref which, 3);
        var cachedModuleSelection = await Assert.ThrowsAnyAsync<OperationCanceledException>(
            () => Run(evaluation.Token).WaitAsync(HangGuard));
        Assert.Equal(parseCancellation.Token, cachedModuleSelection.CancellationToken);
        Assert.Equal(0, Region(root, "H").MaterializationAttempts);
        Assert.Equal(1, downloads[ModuleA]);

        // Parsing again under a live token is the way back.
        Volatile.Write(ref which, 1);
        var reparsed = (await SourceProvenance.ParseValidAsync(Program, new RunOptions
        {
            HostOperations = hosts,
            DownloadCode = downloads.Download,
        })).Root;
        AssertValue(await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(reparsed), hosts, null, null, evaluation.Token).WaitAsync(HangGuard), 8);
        Assert.Equal(1, downloads[ModuleB]);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task EngineEntry_SourceTokenCancelledDuringEvaluation_EndsTheRunWithThatToken_OnlyWhenAnUnloadedBranchIsSelected(bool atoms)
    {
        foreach (var selects in new[] { true, false })
        {
            using var source = new CancellationTokenSource();
            using var evaluation = new CancellationTokenSource();
            var downloads = new CountingDownloader();
            var stops = 0;
            var options = new RunOptions
            {
                HostOperations = HostOperations.Create(HostOperation.Create("Stop", (_, _) =>
                {
                    Interlocked.Increment(ref stops);
                    source.Cancel();
                    return new Result.Atom(1);
                })),
                SourceProcessingCancellationToken = source.Token,
                EvaluationCancellationToken = evaluation.Token,
                DownloadCode = downloads.Download,
            };
            // Source processing has completed when Stop() runs (it is evaluation); F(1) then selects
            // the unloaded branch, while F(0) selects a clause that loads nothing.
            var program = FamilyF + (selects ? "Stop() + F(1)" : "Stop() + F(0)");

            if (selects)
            {
                var cancelled = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
                {
                    if (atoms)
                        await KatLangEngine.EvaluateToAtomsAsync(program, options).WaitAsync(HangGuard);
                    else
                        await KatLangEngine.RunAsync(program, options).WaitAsync(HangGuard);
                });
                Assert.Equal(source.Token, cancelled.CancellationToken);
            }
            else if (atoms)
            {
                Assert.Equal([(Decimal128)1], await KatLangEngine.EvaluateToAtomsAsync(program, options).WaitAsync(HangGuard));
            }
            else
            {
                var success = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(program, options).WaitAsync(HangGuard));
                Assert.Equal("1", success.ToDisplayString());
            }

            Assert.Equal(1, Volatile.Read(ref stops));
            Assert.True(source.IsCancellationRequested);
            Assert.False(evaluation.IsCancellationRequested);
            Assert.Equal(0, downloads[ModuleA]);
        }
    }

    // ── 2. An erroneous result is not evaluable ───────────────────────────────

    /// <summary>A front-end error outside the deferred branch.</summary>
    public enum FrontEndError
    {
        Syntax,
        Collision,
        MissingModule,
        RefusedInference,
    }

    private static string Erroneous(FrontEndError error) => FamilyF + error switch
    {
        FrontEndError.Syntax => "Bad = (1, 2]\nF(1)",
        FrontEndError.Collision => "Coll(cy) = {\n    cy = 1\n    cy\n}\nF(1)",
        FrontEndError.MissingModule => $"M = load('{Missing}')\nF(1)",
        FrontEndError.RefusedInference => "X(x) = x\nY(y) = y\nA = B + X\nB = A + Y\nF(1)",
        _ => throw new ArgumentOutOfRangeException(nameof(error)),
    };

    private static DiagnosticCode CodeOf(FrontEndError error) => error switch
    {
        FrontEndError.Syntax => DiagnosticCode.UnexpectedToken,
        FrontEndError.Collision => DiagnosticCode.ParameterPropertyCollision,
        FrontEndError.MissingModule => DiagnosticCode.LoadFetchFailed,
        FrontEndError.RefusedInference => DiagnosticCode.SelfDependentInferredParameters,
        _ => throw new ArgumentOutOfRangeException(nameof(error)),
    };

    [Theory]
    [InlineData(FrontEndError.Syntax)]
    [InlineData(FrontEndError.Collision)]
    [InlineData(FrontEndError.MissingModule)]
    [InlineData(FrontEndError.RefusedInference)]
    public async Task AnErroneousResult_IsRefusedByTheEngine_AndEverySelectionOfItsDeferredBranchThrows(FrontEndError error)
    {
        var downloads = new CountingDownloader();
        var options = new RunOptions { DownloadCode = downloads.Download };
        var source = Erroneous(error);

        var parsed = await Parser.ParseAsync(source, options).WaitAsync(HangGuard);
        Assert.True(parsed.HasErrors);
        Assert.Contains(parsed.Diagnostics, diagnostic => diagnostic.Code == CodeOf(error));
        var region = Region(parsed.Root, "F");

        // The source gate: the engine never evaluates an erroneous parse, so the branch loads nothing.
        Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(source, options).WaitAsync(HangGuard));
        Assert.Equal(0, downloads[ModuleA]);

        // Outside the contract: the root handed to the evaluator directly cannot compile the branch.
        for (var selection = 0; selection < 2; selection++)
        {
            await Assert.ThrowsAsync<InvalidOperationException>(
                () => Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root)).WaitAsync(HangGuard));
            Assert.False(region.IsMaterialized);
        }

        // No module work when the error stopped the passes that prepare the branch; otherwise the
        // module was downloaded once (it stays cached and charged) and each selection was an attempt.
        var prepared = error != FrontEndError.RefusedInference;
        Assert.Equal(prepared ? 1 : 0, downloads[ModuleA]);
        Assert.Equal(prepared ? 2 : 0, region.MaterializationAttempts);
    }

    [Fact]
    public async Task AnErroneousResult_WhoseBranchModuleFailsToLoad_ReportsTheOrdinaryMaterializationFailure()
    {
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = (url, _) =>
            {
                calls++;
                throw new InvalidOperationException($"404: {url}");
            },
        };
        var parsed = await Parser.ParseAsync(Erroneous(FrontEndError.Collision), options).WaitAsync(HangGuard);
        Assert.True(parsed.HasErrors);

        var result = await Evaluator.RunFlatAsync(new Expr.AlgorithmExpr(parsed.Root)).WaitAsync(HangGuard);

        Assert.True(result.IsError);
        Assert.Equal(KatLangErrorCode.LoadFetchFailed, result.Error.Code);
        Assert.Equal(1, calls);
        Assert.False(Region(parsed.Root, "F").IsMaterialized);
    }
}
