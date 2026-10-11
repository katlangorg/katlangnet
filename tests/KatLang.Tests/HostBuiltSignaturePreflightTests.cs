using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

public class HostBuiltSignaturePreflightTests
{
    public static IEnumerable<object[]> InvalidHeads()
    {
        foreach (var shape in new[] { "repeat-top", "repeat-list", "repeat-sequence", "repeat-unpack", "repeat-cross-level", "clause-bare", "clause-flat", "clause-list", "clause-sequence" })
            foreach (var use in new[] { "unused", "call", "bare", "callback", "loop", "alias" })
                for (var route = 0; route < 6; route++)
                    yield return [shape, use, route];
    }

    [Theory]
    [MemberData(nameof(InvalidHeads))]
    public async Task InvalidHead_IsRejectedBeforeAnyEffect_OnEveryEntryRoute(string shape, string use, int route)
    {
        var effects = 0;
        var hosts = route is 2 or 5
            ? HostOperations.Create(HostOperation.CreateAsync("tick", async (_, _) =>
                { await Task.Yield(); effects++; return new Result.Atom(1); }))
            : HostOperations.Create(HostOperation.Create("tick", (_, _) =>
                { effects++; return new Result.Atom(1); }));
        var source = "F(x)=x\nAlias=F\ntick()\n" + (use switch
        {
            "unused" => "7",
            "call" => "F(1, 2)",
            "bare" => "F",
            "callback" => "map([1], F)",
            "loop" => "repeat(F, 1, 0)",
            "alias" => "Alias(1, 2)",
            _ => throw new ArgumentOutOfRangeException(nameof(use)),
        });
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = hosts });
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
        var invalid = InvalidAlgorithm(shape);
        var root = parsed.Root with
        {
            Properties = parsed.Root.Properties.Select(p => p.Name == "F" ? p with { Value = invalid } : p).ToArray(),
        };
        var expression = new Expr.AlgorithmExpr(root);
        EvalError error;
        if (route < 3)
        {
            var result = route == 0
                ? Evaluator.Run(expression, hosts, null, null, default)
                : await Evaluator.RunAsync(expression, hosts, null, null, default);
            Assert.True(result.IsError);
            error = result.Error;
        }
        else
        {
            var (result, _) = route == 5
                ? await Evaluator.RunCountedObservedAsync(expression,
                    zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), hostOperations: hosts)
                : Evaluator.RunCountedObserved(expression, enableOptimizations: route == 4, hostOperations: hosts);
            Assert.True(result.IsError);
            error = result.Error;
        }
        var illegal = Assert.IsType<EvalError.IllegalInEval>(error);
        Assert.Equal(shape.StartsWith("repeat", StringComparison.Ordinal)
            ? "Repeated parameter names cannot include collecting bindings."
            : "Collecting bindings are only supported in ordinary explicit parameter lists.", illegal.Reason);
        Assert.Equal(KatLangErrorCode.IllegalInEval, error.Code);
        Assert.Equal(0, effects);
    }

    private static Algorithm InvalidAlgorithm(string shape)
    {
        static CaptureParameterPattern Fixed() => new("x");
        static CaptureParameterPattern Collected() => new("x", Kind: ParameterKind.Collecting);
        ParameterPattern[] patterns = shape switch
        {
            "repeat-top" => [Fixed(), Collected()],
            "repeat-list" => [new ListValueParameterPattern([Fixed(), Collected()])],
            "repeat-sequence" => [new SequenceValueParameterPattern([Fixed(), Collected()])],
            "repeat-unpack" => [new UnpackingParameterPattern([Fixed(), Collected()])],
            "repeat-cross-level" => [Fixed(), new ListValueParameterPattern([Collected()])],
            _ => [],
        };
        var body = new Algorithm.User(null, patterns, [], [], [new Expr.Num(7)]);
        if (patterns.Length != 0)
            return body;
        var collecting = new Pattern.Bind("xs") { ParameterKind = ParameterKind.Collecting };
        Pattern head = shape switch
        {
            "clause-bare" => collecting,
            "clause-flat" => new Pattern.SequenceValue([new Pattern.Bind("a"), collecting]),
            "clause-list" => new Pattern.ListValue([collecting]),
            "clause-sequence" => new Pattern.SequenceValue([new Pattern.Bind("a"), new Pattern.SequenceValue([new Pattern.Bind("b"), collecting])]),
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        };
        return new Algorithm.Conditional(null, [], [new CondBranch(head, body)]);
    }

    [Theory]
    [InlineData("singleton", "A sequence pattern with exactly one non-collecting item is invalid: KatLang has no one-item sequence value. Bind the whole value with a plain name, or use the list pattern `[x]` for a one-element list.")]
    [InlineData("multiple", "Only one collecting binding is allowed per pattern level.")]
    [InlineData("repeat", "Repeated parameter names cannot include collecting bindings.")]
    public void SignatureRuleOrder_PrecedesMissingOutput(string shape, string expected)
    {
        var x = new CaptureParameterPattern("x");
        var xs = new CaptureParameterPattern("x", Kind: ParameterKind.Collecting);
        ParameterPattern[] patterns = shape switch
        {
            "singleton" => [new SequenceValueParameterPattern([x]), xs, xs],
            "multiple" => [xs, xs],
            "repeat" => [x, xs],
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        };
        var result = Evaluator.Run(new Expr.AlgorithmExpr(new Algorithm.User(null, patterns, [], [], [])));
        Assert.Equal(expected, Assert.IsType<EvalError.IllegalInEval>(result.Error).Reason);
    }

    [Theory]
    [InlineData("F(x,x)=x\nF(1,1)", "1")]
    [InlineData("F(x,*xs)=xs\nF(1,2,3)", "[2, 3]")]
    public async Task ValidRepeatedFixedNamesAndDistinctCollectors_KeepTheirValues(string source, string expected)
    {
        for (var route = 0; route < 6; route++)
        {
            var result = await ModelCProductionTests.Observe(source, route);
            Assert.Null(result.Error);
            Assert.Equal(expected, result.Value);
        }
    }

    [Theory]
    [InlineData("F(x,*x)=x\n7")]
    [InlineData("F([x,*x])=x\n7")]
    public void WrittenRepeatedCollectingName_IsAlreadyAFrontEndError(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.InvalidCollectingBinding);
    }
}
