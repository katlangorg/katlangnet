using static KatLang.Tests.SixRouteAgreement;

namespace KatLang.Tests;

/// <summary>Independent FA-OQ-1 seam regressions; expectations come from Option B and Model C.</summary>
public class InlineAliasFinalReviewTests
{
    private const string Inc = "Inc(x) = x + 1\n";

    public static TheoryData<string, string, string, string?, string?, string[]> Witnesses => new()
    {
        { "local-alias", Inc + "K(z) = count({ A = Inc\n A })\nK(1)", "arity", "A", "A }", [] },
        { "local-shadow", Inc + "K(z) = count({ Inc(a, b) = a + b\n Inc })\nK(1)", "arity2", "Inc", "Inc }", [] },
        { "nested-spread", Inc + "K(z) = [{ { { Inc } } }*]\nK(1)", "arity", "Inc", "Inc }", [] },
        { "grouped-target", Inc + "K(z) = count({ ((Inc)) })\nK(1)", "arity", "Inc", "Inc))", [] },
        { "deep-member", "Lib = { public Box = { public F(x) = x } }\nK(z) = count({ Lib.Box.F })\nK(1)", "arity", null, "Lib.Box.F }", [] },
        { "member-family", "Lib = { public E(1) = 10\n public E(2) = 20 }\nK(z) = count({ Lib.E })\nK(1)", "family", "E", "Lib.E }", [] },
        { "parameter-reclassification", Inc + "Read(v) = count(v)\nK(z) = Read({ Inc })\nK(1)", "arity", "Inc", "Inc }", [] },
        { "eager-spread-before-demand", Inc + "First(a, b) = a\nK(z) = First({ Inc }, trace(9)*)\nK(1)", "arity", "Inc", "Inc }", ["trace(9)"] },
        { "capture-is-not-alias", Inc + "K(z) = count({ (Inc, 1) })\nK(1)", "unresolved", null, null, [] },
        { "second-row-is-not-alias", Inc + "K(z) = count({ Inc, () })\nK(1)", "unresolved", null, null, [] },
        { "reduce-family-contract", "E(1) = 10\nE(2) = 20\nAdd(a,b) = a+b\nK(z) = reduce([1], Add, { E })\nK(1)", "family", "E", "E }", [] },
        { "lazy-collector-transport", Inc + "Ignore(v) = 7\nPass(*xs) = Ignore(xs)\nPass({ Inc })", "7", null, null, [] },
        { "unselected-nested-alias", Inc + "K(z) = if(false, { { Inc } }, 7)\nK(1)", "7", null, null, [] },
        { "callable-after-transport", Inc + "Apply(f, x) = f(x)\nPass(f, x) = Apply(f, x)\nPass({ A = Inc\n A }, 4)", "5", null, null, [] },
        { "zero-accepting-chain", "Only(*xs) = xs\nA = Only\nB = A\nK(z) = count({ B })\nK(1)", "0", null, null, [] },
        { "zero-property-values", "Z = 4\nK(z) = { Z }, { { Z } }, Z\nK(1)", "S[4, 4, 4]", null, null, [] },
        { "one-cell-two-demands", "Only(*xs) = tick()\nTwice(v) = v + v\nTwice({ Only })", "2", null, null, ["tick#1"] },
    };

    [Theory]
    [MemberData(nameof(Witnesses))]
    public async Task IndependentSeams_RespectTargetContractAndDemandOrder(
        string id, string source, string expected, string? target, string? spanAnchor, string[] hostCalls)
    {
        var observed = await OnEveryRouteAsync(source);
        Assert.Equal(hostCalls, observed.HostCalls);
        if (expected is not ("arity" or "arity2" or "family" or "unresolved"))
        {
            Assert.Equal("ok", observed.Kind);
            Assert.Equal(expected, observed.Value);
            return;
        }

        Assert.Equal("err", observed.Kind); // A front-end rejection cannot stand in for the intended demand.
        // The effectful spread uses the six-route host fixture; inspect the same error through its engine observation.
        if (hostCalls.Length == 0)
        {
            var parsed = SourceProvenance.ParseValid(source);
            var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), enableOptimizations: false);
            Assert.True(result.IsError, id);
            var inner = result.Error;
            while (inner is EvalError.WithContext context) inner = context.Inner;
            switch (expected)
            {
                case "arity":
                case "arity2":
                    var arity = Assert.IsType<EvalError.ArityMismatch>(inner);
                    Assert.Equal((expected == "arity2" ? 2 : 1, 0), (arity.Expected, arity.Actual));
                    break;
                case "family":
                    Assert.Equal(target, Assert.IsType<EvalError.NoMatchingBranch>(inner).AlgorithmName);
                    break;
                case "unresolved":
                    Assert.Equal(new[] { "x" }, Assert.IsType<EvalError.UnresolvedImplicitParams>(inner).ParamNames);
                    break;
            }
        }

        var error = Assert.Single(observed.Errors);
        Assert.StartsWith(expected == "unresolved" ? "UnresolvedImplicitParams:" : expected == "family" ? "NoMatchingBranch:" : "ArityMismatch:", error);
        if (target is not null && expected.StartsWith("arity", StringComparison.Ordinal))
            Assert.Contains($"Property '{target}' expects {(expected == "arity2" ? "2 parameters" : "1 parameter")}, but was called with 0 arguments.", error);
        if (spanAnchor is not null)
        {
            var start = source.LastIndexOf(spanAnchor, StringComparison.Ordinal);
            Assert.True(start >= 0, id);
            var length = spanAnchor.Split(' ')[0].TrimEnd(')').Length;
            var line = 1 + source[..start].Count(static c => c == '\n');
            var column = start - (source.LastIndexOf('\n', start - 1) + 1) + 1;
            Assert.EndsWith($"@ [{line}:{column}, {line}:{column + length})", error);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task DeferredAliasDemand_ResumesAfterAcquisition_OnlyForSelectedBranch(bool selected)
    {
        const string source = "K(0) = 7\nK(z) = {\n open 'https://katlang.org/lazy/alias.kat'\n count({ Imported })\n}\n";
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource<string>(TaskCreationOptions.RunContinuationsAsynchronously);
        var reads = 0;
        var options = new RunOptions
        {
            DownloadCode = async (_, _) =>
            {
                Interlocked.Increment(ref reads);
                entered.TrySetResult();
                return await release.Task;
            },
        };
        var program = source + (selected ? "K(1)" : "K(0)");
        var parsed = await Parser.ParseAsync(program, options);
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
        Assert.Equal(0, reads);
        var pending = KatLangEngine.RunAsync(program, options);
        try
        {
            if (selected)
            {
                await entered.Task.WaitAsync(TimeSpan.FromSeconds(10));
                Assert.False(pending.IsCompleted); // Demand must actually cross an asynchronous acquisition seam.
                release.SetResult("public Imported(x) = x + 1");
                var failure = Assert.IsType<RunResult.EvalFailure>(await pending.WaitAsync(TimeSpan.FromSeconds(10)));
                var error = Assert.Single(failure.Errors);
                Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
                Assert.Contains("Property 'Imported' expects 1 parameter, but was called with 0 arguments.", error.Message);
                Assert.Equal("[4:10, 4:18)", error.Span?.ToString());
                Assert.Equal(1, reads);
            }
            else
            {
                var success = Assert.IsType<RunResult.Success>(await pending.WaitAsync(TimeSpan.FromSeconds(10)));
                Assert.Equal("7", Neutral(success.Value));
                Assert.Equal(0, reads);
            }
        }
        finally
        {
            release.TrySetResult("public Imported(x) = x + 1");
            await pending.WaitAsync(TimeSpan.FromSeconds(10));
        }
    }
}
