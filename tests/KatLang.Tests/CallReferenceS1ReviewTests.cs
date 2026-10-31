using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>Independent S1 review: a reference's owning run must still be live.</summary>
public class CallReferenceS1ReviewTests
{
    private sealed class PatternReadBudget
    {
        public int Reads;
    }

    private sealed class BudgetedPatternItems(ParameterPattern first, ParameterPattern second,
        PatternReadBudget budget) : IReadOnlyList<ParameterPattern>
    {
        public int Count => 2;
        public ParameterPattern this[int index]
        {
            get
            {
                if (++budget.Reads > 2000)
                    throw new InvalidOperationException("META scan expanded shared parameter-pattern paths.");
                return index == 0 ? first : second;
            }
        }
        public IEnumerator<ParameterPattern> GetEnumerator()
        {
            yield return this[0];
            yield return this[1];
        }
        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    private static ParameterPattern SharedPattern(string kind, string name, PatternReadBudget budget)
    {
        ParameterPattern pattern = new CaptureParameterPattern(name);
        for (var i = 0; i < 45; i++)
        {
            var items = new BudgetedPatternItems(pattern, pattern, budget);
            pattern = kind switch
            {
                "sequence" => new SequenceValueParameterPattern(items),
                "list" => new ListValueParameterPattern(items),
                _ => new UnpackingParameterPattern(items),
            };
        }
        return pattern;
    }

    [Theory]
    [InlineData("sequence", "none")]
    [InlineData("list", "none")]
    [InlineData("unpack", "none")]
    [InlineData("sequence", "unique")]
    [InlineData("list", "unique")]
    [InlineData("unpack", "unique")]
    [InlineData("sequence", "repeated")]
    [InlineData("list", "repeated")]
    [InlineData("unpack", "repeated")]
    public void MetaValidation_SharedPatterns_AreBounded_AndRetainDuplicateOccurrences(string kind, string meta)
    {
        var budget = new PatternReadBudget();
        var shared = SharedPattern(kind, meta == "repeated" ? "op" : "x", budget);
        ParameterPattern[] patterns = meta == "none" ? [shared]
            : [new CaptureParameterPattern("op", Kind: ParameterKind.Meta), shared];
        Assert.Equal(meta != "none", ParameterPattern.HasMetaCapture(patterns));
        var violation = ParameterPattern.FindMetaViolation(patterns);
        if (meta == "repeated") Assert.Equal("op", violation?.Name);
        else Assert.Null(violation);
        Assert.InRange(budget.Reads, 1, 2000);
    }

    [Fact]
    public void MetaValidation_NestedMeta_PrecedesATopLevelDuplicate_AfterASharedSubgraph()
    {
        var budget = new PatternReadBudget();
        var shared = SharedPattern("list", "x", budget);
        ParameterPattern[] patterns = [new CaptureParameterPattern("op", Kind: ParameterKind.Meta),
            new CaptureParameterPattern("op"), new ListValueParameterPattern([shared,
                new CaptureParameterPattern("nested", Kind: ParameterKind.Meta)])];
        Assert.Equal("nested", ParameterPattern.FindMetaViolation(patterns)?.Name);
        Assert.InRange(budget.Reads, 1, 2000);
    }

    [Theory]
    [InlineData("leaf")]
    [InlineData("list")]
    [InlineData("sequence")]
    [InlineData("dag")]
    public async Task HostReturns_RefuseReferencesDuringNormalization_EvenInAMetaFreeRun(string shape)
    {
        var budget = EvaluationBudget.Create(null);
        budget.DecideInvocationPlanRetention(true);
        var ctx = Evaluator.EvalCtx.Empty with { Budget = budget };
        var cell = Evaluator.SupplyCell(new Expr.Call(new Expr.Resolve("count"), [new Expr.Num(1)]), ctx, []);
        var reference = Evaluator.ReifyMeta(cell).Value;
        Result returned = shape switch
        {
            "leaf" => reference,
            "sequence" => new Result.SequenceValue([new Result.Atom(1), reference]),
            _ => new Result.ListValue([reference]),
        };
        if (shape == "dag")
            for (var i = 0; i < 20; i++) returned = new Result.ListValue([returned, returned]);
        // Internal normalization still transports a reference. The host return contract is
        // checked independently of J7, including a foreign handle injected by this test seam.
        Assert.True(Evaluator.ContainsCallReference(returned.Normalize()));
        Assert.Contains("Host operation 'Leak' returned a call reference",
            Assert.Throws<InvalidOperationException>(() => KatLangEngine.Run("Leak()", new RunOptions
            {
                HostOperations = HostOperations.Create(HostOperation.Create("Leak", (_, _) => returned)),
            })).Message, StringComparison.Ordinal);
        var thrown = await Assert.ThrowsAsync<InvalidOperationException>(async () => await KatLangEngine.RunAsync("Leak()", new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.CreateAsync("Leak", (_, _) => ValueTask.FromResult(returned))),
        }));
        Assert.Contains("Host operation 'Leak' returned a call reference", thrown.Message, StringComparison.Ordinal);
        Assert.Null(((Evaluator.InvocationPlan)cell.Suspension!).Supply);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task InvokeAcrossARealSuspension_KeepsTheRunLive_ThenClosesIt(bool cancel)
    {
        Result.CallReference? reference = null;
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        using var tokenSource = new CancellationTokenSource();
        tokenSource.Cancel();
        var cancellation = new OperationCanceledException(tokenSource.Token);
        var pauses = 0;
        var operations = HostOperations.Create(
            HostOperation.Create("Grab", (_, _) => throw new InvalidOperationException("missing receiver"), "operation"),
            HostOperation.CreateAsync("Pause", async (args, _) =>
            {
                pauses++;
                entered.TrySetResult();
                await release.Task;
                if (cancel) throw cancellation;
                return args[0];
            }, "x"));
        var experiment = new InvocationPlanTestSeam(new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>
        {
            ["Grab"] = cells =>
            {
                reference = Evaluator.ReifyMeta(cells[0]).Value;
                return new Result.Atom(0);
            },
        });
        const string source = "Capture(meta op) = op\nUse(v) = { Grab(v)\nCapture(v).Invoke() }\nUse(Pause(5))";
        using (InvocationPlanTestSeam.Activate(experiment))
        {
            var running = KatLangEngine.RunAsync(source, new RunOptions { HostOperations = operations });
            try
            {
                await entered.Task.WaitAsync(TimeSpan.FromSeconds(45));
                Assert.False(running.IsCompleted);
                var live = Assert.IsType<Result.CallReference>(reference);
                Assert.False(live.Budget.RunEnded);
                Assert.Null(Evaluator.CheckCallReferenceOwnership(live, live.Plan.Caller));
            }
            finally
            {
                release.TrySetResult();
            }
            if (cancel)
                Assert.Same(cancellation, await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await running));
            else
                Assert.IsType<RunResult.Success>(await running);
        }
        var completed = Assert.IsType<Result.CallReference>(reference);
        Assert.True(completed.Budget.RunEnded);
        var refused = await Evaluator.InvokeCallReferenceValueAsync(completed, completed.Plan.Caller);
        Assert.Equal(Evaluator.EndedCallReferenceMessage, Assert.IsType<EvalError.IllegalInEval>(refused.Error).Reason);
        Assert.Equal(1, pauses);
    }

    public static IEnumerable<object[]> RunExits()
    {
        foreach (var entry in new[] { "value", "counted", "observed", "property",
            "async-value", "async-counted", "async-observed", "async-property" })
        foreach (var exit in new[] { "success", "error", "exception" })
        foreach (var prepared in new[] { false, true })
            yield return [entry, exit, prepared];
    }

    [Theory]
    [MemberData(nameof(RunExits))]
    public async Task EveryRunExit_RefusesLaterInvocation_WithoutRunningThePlan(
        string entry, string exit, bool prepared)
    {
        Result.CallReference? reference = null;
        var hostException = new InvalidOperationException("review host failure");
        var operations = HostOperations.Create(
            HostOperation.Create("Grab", (_, _) => throw new InvalidOperationException("missing receiver"), "operation"),
            HostOperation.Create("fail", (_, _) => throw hostException));
        var experiment = new InvocationPlanTestSeam(new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>
        {
            ["Grab"] = cells =>
            {
                reference = Evaluator.ReifyMeta(cells[0]).Value;
                Assert.Null(Evaluator.CheckCallReferenceOwnership(reference, reference.Plan.Caller));
                if (prepared)
                    Assert.True(Evaluator.InvokeCallReferenceValue(reference, reference.Plan.Caller).IsOk);
                return new Result.Atom(0);
            },
        });
        var tail = exit switch { "success" => "0", "error" => "1 / 0", _ => "fail()" };
        var source = "F(x) = x + tick()\nTop = 0\nGrab(F(5))\n" + tail;
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors);
        var root = new Expr.AlgorithmExpr(parsed.Root);

        async Task<bool> RunEntry() => entry switch
        {
            "value" => Evaluator.Run(root, operations, null, null, default).IsOk,
            "counted" => Evaluator.RunCounted(root, new RunScopedZeroArgPropertyResultCache(), hostOperations: operations).IsOk,
            "observed" => Evaluator.RunCountedObserved(root, hostOperations: operations).Result.IsOk,
            "property" => Evaluator.RunCountedWithTopLevelProperty(root, "Top",
                new RunScopedZeroArgPropertyResultCache(), hostOperations: operations).IsOk,
            "async-value" => (await Evaluator.RunAsync(root, new RunScopedAsyncZeroArgPropertyResultCache(),
                hostOperations: operations)).IsOk,
            "async-counted" => (await Evaluator.RunCountedAsync(root, new RunScopedAsyncZeroArgPropertyResultCache(),
                hostOperations: operations)).IsOk,
            "async-observed" => (await Evaluator.RunCountedObservedAsync(root,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), hostOperations: operations)).Result.IsOk,
            "async-property" => (await Evaluator.RunCountedWithTopLevelPropertyAsync(root, "Top",
                new RunScopedAsyncZeroArgPropertyResultCache(), hostOperations: operations)).IsOk,
            _ => throw new ArgumentException("unknown entry", nameof(entry)),
        };

        using (InvocationPlanTestSeam.Activate(experiment))
        {
            if (exit == "exception")
                Assert.Same(hostException, await Assert.ThrowsAsync<InvalidOperationException>(async () => await RunEntry()));
            else
                Assert.Equal(exit == "success", await RunEntry());
        }

        var captured = Assert.IsType<Result.CallReference>(reference);
        var ctx = captured.Plan.Caller;
        var supply = captured.Plan.Supply;
        Assert.True(ctx.Budget.RunEnded);
        var sync = Evaluator.InvokeCallReferenceValue(captured, ctx);
        var asyncResult = await Evaluator.InvokeCallReferenceValueAsync(captured, ctx);
        Assert.Equal(Evaluator.EndedCallReferenceMessage, Assert.IsType<EvalError.IllegalInEval>(sync.Error).Reason);
        Assert.Equal(Evaluator.EndedCallReferenceMessage, Assert.IsType<EvalError.IllegalInEval>(asyncResult.Error).Reason);
        Assert.Same(supply, captured.Plan.Supply);
        Assert.Equal(prepared ? 1 : 0, ctx.Budget.TickCount);
    }
}
