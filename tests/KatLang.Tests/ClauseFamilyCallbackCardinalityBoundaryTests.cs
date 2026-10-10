using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

public sealed partial class ClauseFamilyCallbackCardinalityTests
{
    public static TheoryData<string, string, string> RepeatedBranchCallbacks() => new()
    {
        { "compatible repeated binding", "F((x, x)) = 10\nF((x, y)) = 20\nmap([(1, 1)], F)", "L[10]" },
        { "incompatible binding falls through", "F((x, x)) = 10\nF((x, y)) = 20\nmap([(1, 2)], F)", "L[20]" },
        { "first of two compatible clauses", "F((x, x)) = 10\nF((x, y)) = 20\nmap([(1, 1), (1, 2)], F)", "L[10, 20]" },
        { "literal precedes binder", "F((0, 0)) = 30\nF((x, x)) = 10\nF((x, y)) = 20\nmap([(0, 0), (1, 1), (1, 2)], F)", "L[30, 10, 20]" },
        { "selected later clause emits two rows", "F((x, x)) = 10, 11\nF((x, y)) = 20, 21\nmap([(1, 2)], F)", "L[S[20, 21]]" },
        { "ordinary later clause is one value", "F((x, x)) = 10, 11\nF((x, y)) = 20, 21\nF((1, 2))", "S[20, 21]" },
        { "reduce falls through", "R(x, x) = 10\nR(x, y) = x + y\nreduce([1, 2], R, 0)", "3" },
        { "reduce later clause emits two rows", "R(x, x) = 10, 11\nR(x, y) = x, y\nreduce([1], R, 0)", "S[1, 0]" },
    };

    [Theory]
    [MemberData(nameof(RepeatedBranchCallbacks))]
    public async Task RepeatedNameBranchSelection_PreservesCallbackBoundary(string label, string source, string expected)
    {
        // The repeated-name verdict selects the clause; the selected clause's rows are the ordinary call result
        // (HO-03), exactly the ordinary call's one value.
        Assert.False(string.IsNullOrWhiteSpace(label));
        var (observation, _) = await AllRoutesAsync(source);
        Assert.Equal(("ok", expected, 1), (observation.Kind, observation.Value, observation.Count));
    }

    public static TheoryData<string, string> AdditionalCallbackRoutes() => new()
    {
        { Fam + "Use(f) = map([0], f)\nRelay(*fs) = Use(fs*)\nRelay(F)", "L[S[1, 2]]" },
        { Fam + "Use(f) = map([0], f)\nRelay(f) = Use\nRelay(F)", "L[S[1, 2]]" },
        { Fam + "Box = { public Apply(f) = map([0], f) }\nBox.Apply(F)", "L[S[1, 2]]" },
        { Red + "A = R\nB = A\nreduce([1], { B(e, a) }, 0)", "S[1, 0]" },
        { "P(0) = ()\nP(n) = true\nfilter([0], P)", "err filter" },
        { "P(0) = 7\nP(n) = true\nA = P\nB = A\nKeep(p) = filter([0], p)\nKeep(B)", "err filter" },
        { "P(0) = true\nP(n) = false\nA = P\nB = A\nKeep(p) = filter([0, 1], p)\nKeep(B)", "L[0]" },
    };

    [Theory]
    [MemberData(nameof(AdditionalCallbackRoutes))]
    public async Task AdditionalCallableRoutes_KeepTheirConsumerContract(string source, string expected)
    {
        var (observation, _) = await AllRoutesAsync(source);
        if (!expected.StartsWith("err ", StringComparison.Ordinal))
            Assert.Equal(("ok", expected, 1), (observation.Kind, observation.Value, observation.Count));
        else
        {
            Assert.Equal("err filter", expected);
            var error = Assert.Single(observation.Errors);
            Assert.StartsWith("TypeMismatch: ", error);
            Assert.Contains("filter predicate result must be a Boolean", error);
        }
    }

    private const string DeferredGood = "https://katlang.org/d1-independent/good.kat";
    private const string DeferredMissing = "https://katlang.org/d1-independent/missing.kat";

    public static TheoryData<string, string, string, string[]> DeferredCallbacks() => new()
    {
        { $"F(0) = {{ open '{DeferredGood}'\ntrace(A), trace(A + 1) }}\nF(n) = n, n\nmap([0], F)", "public A = 1", "L[S[1, 2]]", ["1", "2"] },
        { $"F(0) = {{ open '{DeferredGood}'\n(trace(A), trace(A + 1)) }}\nF(n) = (n, n)\nmap([0, 0], F)", "public A = 1", "L[S[1, 2], S[1, 2]]", ["1", "2", "1", "2"] },
        { $"R(e, 0) = {{ open '{DeferredGood}'\ntrace(A + e), trace(0) }}\nR(e, a) = e, a\nreduce([2], R, 0)", "public A = 1", "S[3, 0]", ["3", "0"] },
        { $"R(e, 0) = {{ open '{DeferredGood}'\n(trace(A + e), trace(0)) }}\nR(e, a) = (e, a)\nreduce([2], R, 0)", "public A = 1", "S[3, 0]", ["3", "0"] },
        { $"F(0) = trace(7)\nF(n) = {{ open '{DeferredMissing}'\nX }}\nA = F\nB = A\nUse(f) = map([0], f)\nUse(B)", "public A = 1", "L[7]", ["7"] },
        { $"F(0) = {{ open '{DeferredGood}'\ntrace(A), trace(A + 1) }}\nF(n) = n, n\nAlias = F\nUse(f) = map([0], f)\nUse(Alias)", "public A = 1", "L[S[1, 2]]", ["1", "2"] },
        { $"F(0) = {{ open '{DeferredGood}'\ntrace(A) / 0 }}\nF(n) = n\nmap([0], F)", "public A = 1", "err div0", ["1"] },
        { $"open '{DeferredGood}'\nmap([0], F)", "public F(0) = 1, 2\npublic F(n) = n, n", "L[S[1, 2]]", [] },
        { $"M = load('{DeferredGood}')\nmap([0], M.F)", "public F(0) = 1, 2\npublic F(n) = n, n", "L[S[1, 2]]", [] },
        { $"open '{DeferredGood}'\nGo([0])", "F(0) = 1, 2\nF(n) = n, n\npublic Go(xs) = map(xs, F)", "L[S[1, 2]]", [] },
    };

    [Theory]
    [MemberData(nameof(DeferredCallbacks))]
    public async Task DeferredOrLoadedFamilyCallback_ReturnsTheOrdinaryCallResult(
        string source, string moduleSource, string expected, string[] expectedEffects)
    {
        // Deferred trees require async evaluation even with an inline downloader. Use fresh loaders
        // for the engine and observed evaluator, with inline and actually suspending acquisitions.
        Observation? oracle = null;
        Budget? oracleBudget = null;
        foreach (var suspending in new[] { false, true })
        foreach (var engine in new[] { true, false })
        {
            var fetches = new List<string>();
            var effects = new List<string>();
            async ValueTask<string> Download(string url, CancellationToken token)
            {
                fetches.Add(url);
                if (suspending) await Task.Yield();
                token.ThrowIfCancellationRequested();
                if (url != DeferredGood) throw new InvalidOperationException("unselected source acquired");
                return moduleSource;
            }
            Result Trace(IReadOnlyList<Result> args)
            {
                effects.Add(SixRouteAgreement.Neutral(args[0]));
                return args[0];
            }
            var operations = suspending
                ? HostOperations.Create(HostOperation.CreateAsync("trace", async (args, token) =>
                    { await Task.Yield(); token.ThrowIfCancellationRequested(); return Trace(args); }, "x"))
                : HostOperations.Create(HostOperation.Create("trace", (args, _) => Trace(args), "x"));
            var options = new RunOptions { DownloadCode = Download, HostOperations = operations };
            Observation observed;
            if (engine)
                observed = FromRunResult(await KatLangEngine.RunAsync(source, options), new HostLog());
            else
            {
                var parsed = await Parser.ParseAsync(source, options);
                Assert.Empty(parsed.Diagnostics);
                var (result, budget) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root),
                    zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), hostOperations: operations);
                observed = result.IsError ? FromError(KatLangError.FromEvalError(result.Error), new HostLog())
                    : new("ok", SixRouteAgreement.Neutral(result.Value.Value), result.Value.EmittedCount, [], [], []);
                var counters = new Budget(budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth,
                    budget.MaterializedItems, budget.MaterializedStringChars);
                if (oracleBudget is not null) Assert.Equal(oracleBudget, counters);
                oracleBudget = counters;
            }
            Assert.True(observed.Kind is "ok" or "err", observed.ToString());
            Assert.Equal(expectedEffects, effects);
            Assert.DoesNotContain(DeferredMissing, fetches);
            Assert.Equal(source.Contains(DeferredGood, StringComparison.Ordinal) ? 1 : 0, fetches.Count);
            if (expected.StartsWith("err ", StringComparison.Ordinal))
            {
                Assert.Equal("err div0", expected);
                Assert.StartsWith("DivisionByZero: ", Assert.Single(observed.Errors));
            }
            else Assert.Equal(("ok", expected, 1), (observed.Kind, observed.Value, observed.Count));
            if (oracle is not null) Assert.Equal(oracle, observed);
            oracle = observed;
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task SelectedDeferredCallback_SourceFailureRetainsItsDiagnostic(bool suspending)
    {
        var requests = 0;
        var options = new RunOptions
        {
            DownloadCode = async (_, _) =>
            {
                requests++;
                if (suspending) await Task.Yield();
                throw new InvalidOperationException("missing module");
            },
        };
        var source = $"F(0) = {{ open '{DeferredMissing}'\nX, X }}\nF(n) = n, n\nmap([0], F)";
        var parsed = await Parser.ParseAsync(source, options);
        Assert.Empty(parsed.Diagnostics);
        Assert.Equal(0, requests);
        var result = await Evaluator.RunCountedAsync(new Expr.AlgorithmExpr(parsed.Root), new RunScopedAsyncZeroArgPropertyResultCache());
        Assert.True(result.IsError);
        Assert.Equal(KatLangErrorCode.LoadFetchFailed, result.Error.Code);
        Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(Innermost(result.Error));
        Assert.Contains("map", KatLangError.FromEvalError(result.Error).Message);
        Assert.Equal(1, result.Error.Span?.Start.Line);
        Assert.Equal(1, requests);
    }

    [Theory]
    [InlineData(false, false, "reduce", "S[1, 0]")]
    [InlineData(false, true, "reduce", "S[1, 0]")]
    [InlineData(false, false, "call", "S[1, 0]")]
    [InlineData(false, false, "repeat", "S[1, 0]")]
    [InlineData(true, true, "compatible", "1")]
    [InlineData(true, true, "reduce", "err branch")]
    public async Task HostBuiltFlatFamily_PreservesCardinalityAndItsDocumentedDispatchDomain(
        bool repeated, bool oneRow, string operation, string expected)
    {
        var names = repeated ? new[] { "x", "x" } : ["x", "y"];
        OutputBundle rows = repeated ? [new Expr.Param("x")]
            : oneRow ? [new Expr.Capture([new Expr.Param("x"), new Expr.Param("y")])]
            : [new Expr.Param("x"), new Expr.Param("y")];
        var body = new Algorithm.User(null, [], [], [], rows);
        var family = new Algorithm.Conditional(null, [], [new(new Pattern.SequenceValue(names.Select(n => (Pattern)new Pattern.Bind(n)).ToArray()), body)]);
        Expr output = operation switch
        {
            "call" => new Expr.Call(new Expr.Resolve("F"), [new Expr.Num(1), new Expr.Num(0)]),
            "repeat" => new Expr.Call(new Expr.Resolve("repeat"), [new Expr.Resolve("F"), new Expr.Num(1), new Expr.Num(1), new Expr.Num(0)]),
            _ => new Expr.Call(new Expr.Resolve("reduce"), [new Expr.ListLiteral([new Expr.Num(1)]), new Expr.Resolve("F"), new Expr.Num(operation == "compatible" ? 1 : 0)]),
        };
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("F", family)], [output]));
        Budget? previous = null;
        foreach (var route in new[] { 0, 1, 2 })
        {
            var (result, budget) = route == 2
                ? await Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache())
                : Evaluator.RunCountedObserved(program, enableOptimizations: route == 1);
            if (expected.StartsWith("err ", StringComparison.Ordinal))
            {
                // FORMAL-08: this host-only core shape differs from Lean's flat user fallback.
                Assert.Equal("err branch", expected);
                Assert.True(result.IsError);
                var noMatch = Assert.IsType<EvalError.NoMatchingBranch>(Innermost(result.Error));
                Assert.Equal("reduce step", noMatch.AlgorithmName);
            }
            else
            {
                Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
                Assert.Equal(expected, SixRouteAgreement.Neutral(result.Value.Value));
                Assert.Equal(1, result.Value.EmittedCount);
            }
            var counters = new Budget(budget.ConsumedSteps, budget.ConsumedExpressionCheckpoints, budget.PeakDepth,
                budget.MaterializedItems, budget.MaterializedStringChars);
            if (previous is not null) Assert.Equal(previous, counters);
            previous = counters;
        }
    }

    [Fact]
    public async Task DeferredCallbackCancellation_AbortsAcquisitionAndRetriesWithoutCachingFailure()
    {
        using var cancellation = new CancellationTokenSource();
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var attempts = 0;
        var options = new RunOptions
        {
            DownloadCode = async (_, token) =>
            {
                if (++attempts == 1)
                {
                    entered.SetResult();
                    await Task.Delay(Timeout.InfiniteTimeSpan, token);
                }
                return "public A = 1";
            },
        };
        var parsed = await Parser.ParseAsync($"F(0) = {{ open '{DeferredGood}'\nA, A + 1 }}\nF(n) = n, n\nmap([0], F)", options);
        Assert.Empty(parsed.Diagnostics);
        Assert.Equal(0, attempts);
        var program = new Expr.AlgorithmExpr(parsed.Root);
        var first = Evaluator.RunCountedAsync(program, new RunScopedAsyncZeroArgPropertyResultCache(), cancellationToken: cancellation.Token).AsTask();
        await entered.Task.WaitAsync(TimeSpan.FromSeconds(15));
        Assert.False(first.IsCompleted);
        cancellation.Cancel();
        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => first.WaitAsync(TimeSpan.FromSeconds(15)));
        Assert.Equal(cancellation.Token, exception.CancellationToken);
        var retry = await Evaluator.RunCountedAsync(program, new RunScopedAsyncZeroArgPropertyResultCache()).AsTask().WaitAsync(TimeSpan.FromSeconds(15));
        // The retry acquires the source again (the cancelled acquisition was never cached) and the selected clause's
        // two rows are its ordinary call result, one element (HO-03).
        Assert.True(retry.IsOk, retry.IsError ? retry.Error.ToString() : "");
        Assert.Equal("L[S[1, 2]]", SixRouteAgreement.Neutral(retry.Value.Value));
        Assert.Equal(2, attempts);
    }
}
