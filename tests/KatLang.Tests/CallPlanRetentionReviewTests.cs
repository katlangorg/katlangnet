using KatLang.Evaluation;

namespace KatLang.Tests;

public partial class InvocationPlanTests
{
    [Theory]
    [InlineData(false, false, false)]
    [InlineData(false, true, false)]
    [InlineData(true, false, false)]
    [InlineData(true, true, false)]
    [InlineData(false, true, true)]
    public async Task S0_Review_RequiredSourceFailure_CannotBeAbsorbedByAMetaReceiver(
        bool demandValue, bool failureInSpread, bool preparationOnly)
    {
        const string url = "https://katlang.org/s0-review/invalid.kat";
        var downloads = 0;
        var ticks = 0;
        EvalError? observed = null;
        var operations = HostOperations.Create(
            HostOperation.Create("Meta", (_, _) => throw new InvalidOperationException("META receiver missing"), "operation"),
            HostOperation.Create("tick", (_, _) => { ticks++; return Zero; }));
        var options = new RunOptions
        {
            HostOperations = operations,
            DownloadCode = (_, _) => { downloads++; return ValueTask.FromResult(")"); },
        };
        var argument = failureInSpread ? "Add2(F(1)*)" : "F(1)";
        var parsed = await Parser.ParseAsync($$"""
            F(0) = 0
            F(n) = {
                open '{{url}}'
                (1, 2)
            }
            Add2(a, b) = a + b
            Meta({{argument}})
            tick()
            """, options);
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
        Assert.Equal(0, downloads);
        var experiment = new InvocationPlanTestSeam(new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>
        {
            ["Meta"] = cells =>
            {
                var cell = cells[0]!;
                if (preparationOnly)
                {
                    var prepared = Reify(cell).Plan.PrepareSupply(true).AsTask().GetAwaiter().GetResult();
                    Assert.True(prepared.IsError);
                    observed = prepared.Error;
                }
                else
                {
                    var attempted = demandValue
                        ? cell.DemandAsync().AsTask().GetAwaiter().GetResult()
                        : Reify(cell).InvokeAsync().AsTask().GetAwaiter().GetResult();
                    Assert.True(attempted.IsError);
                    observed = attempted.Error;
                }
                return Zero; // The receiver deliberately tries to absorb the required source refusal.
            },
        });
        using var activation = InvocationPlanTestSeam.Activate(experiment);
        var (result, budget) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root),
            hostOperations: operations);
        Assert.NotNull(observed);
        static EvalError Cause(EvalError error)
        {
            while (error is EvalError.WithContext context) error = context.Inner;
            return error;
        }
        var sourceFailure = Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(Cause(observed));
        Assert.False(sourceFailure.IsResourceLimit);
        Assert.True(result.IsError, "META receiver absorbed a required module compilation failure");
        Assert.Same(sourceFailure, Cause(result.Error));
        Assert.Same(sourceFailure, Cause(Assert.IsAssignableFrom<EvalError>(budget.CheckContinuation())));
        Assert.Equal(1, downloads);
        Assert.Equal(0, ticks);
        // Failure terminates this budget, but is not a permanent cache entry in the module loader.
        var (retry, retryBudget) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root),
            hostOperations: operations);
        Assert.True(retry.IsError);
        Assert.NotSame(budget, retryBudget);
        Assert.Equal(2, downloads);
        Assert.Equal(0, ticks);
    }

    [Theory]
    [InlineData("value")]
    [InlineData("invocation")]
    [InlineData("preparation")]
    public async Task S0_Review_RequiredSourceCancellation_CannotBeAbsorbedByAMetaReceiver(string route)
    {
        using var sourceCancellation = new CancellationTokenSource();
        OperationCanceledException? observed = null;
        var operations = HostOperations.Create(
            HostOperation.Create("Meta", (_, _) => throw new InvalidOperationException("META receiver missing"), "operation"));
        var argument = route == "preparation" ? "Add2(F(1)*)" : "F(1)";
        var parsed = await Parser.ParseAsync("F(0) = 0\nF(n) = { open 'https://katlang.org/s0-review/cancel.kat'\n7 }\n"
            + "Add2(a, b) = a + b\nMeta(" + argument + ")",
            new RunOptions
            {
                HostOperations = operations,
                SourceProcessingCancellationToken = sourceCancellation.Token,
                DownloadCode = (_, _) =>
                {
                    sourceCancellation.Cancel();
                    sourceCancellation.Token.ThrowIfCancellationRequested();
                    return ValueTask.FromResult("public V = 7");
                },
            });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
        using var activation = InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam(
            new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>
            {
                ["Meta"] = cells =>
                {
                    observed = Assert.ThrowsAny<OperationCanceledException>(() =>
                    {
                        if (route == "value") cells[0]!.DemandAsync().AsTask().GetAwaiter().GetResult();
                        else if (route == "preparation") Reify(cells[0]).Plan.PrepareSupply(true).AsTask().GetAwaiter().GetResult();
                        else Reify(cells[0]).InvokeAsync().AsTask().GetAwaiter().GetResult();
                    });
                    return Zero;
                },
            }));
        var escaped = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
            await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root), hostOperations: operations));
        Assert.Equal(sourceCancellation.Token, escaped.CancellationToken);
        Assert.Same(observed, escaped);
    }

    [Fact]
    public async Task S0_Review_DirectDeferredPlaceholderFailure_IsRetainedByTheOwningRun()
    {
        var parsed = await Parser.ParseAsync("F(0) = 0\nF(n) = { open 'https://katlang.org/s0-review/invalid.kat'\n7 }\n0",
            new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult(")") });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.Root.Properties).Value);
        var placeholder = family.Branches[1].Body;
        Assert.NotNull(placeholder.DeferredRegion);
        // A host-built root reaches the other materialization boundary, directly in algorithm output.
        var (result, budget) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(placeholder));
        Assert.True(result.IsError);
        var terminal = Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(budget.CheckContinuation());
        Assert.False(terminal.IsResourceLimit);
        Assert.Equal(terminal.Code, result.Error.Code);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task S0_Review_TransitiveValuePreparationReentry_IsADemandCycle(bool asynchronous)
    {
        Result.CallReference? reference = null;
        EvalResult<Evaluator.CountedResult>? reentered = null;
        var calls = 0;
        var pair = new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2)]);
        var operation = asynchronous
            ? HostOperation.CreateAsync("pair", async (_, _) =>
            {
                await Task.Yield();
                calls++;
                reentered = await reference!.InvokeAsync();
                return pair;
            })
            : HostOperation.Create("pair", (_, _) =>
            {
                calls++;
                reentered = reference!.Invoke();
                return pair;
            });
        var probe = new Probe { PairOverride = operation };
        probe.OnMeta = cells => { reference = Reify(cells[0]); return Zero; };
        // The spread calls Wrap, whose parameter demand starts a SECOND cell's VALUE.
        // Reentry therefore needs the owner's transitive wait-for edge, not Current == owner.
        const string source = "Add2(a, b) = a + b\nWrap(v) = v\nProbe(x) = (Meta(x), x)\nProbe(Add2(Wrap(pair())*))";
        var outcome = asynchronous
            ? await probe.RunAsyncTwin(source).WaitAsync(TimeSpan.FromSeconds(30))
            : await Task.Run(() => probe.Run(source)).WaitAsync(TimeSpan.FromSeconds(30));
        Assert.Equal("S[0, 3]", outcome);
        Assert.Equal(KatLangErrorCode.DemandCycle, reentered!.Value.Error.Code);
        Assert.Equal(1, calls);
        Assert.Equal(1, reference!.Plan.SupplyFormations);
        Assert.Equal(0, reference.Plan.Owner.ActiveDependencyCount);
        Assert.True(reference.Plan.Owner.Demand().IsOk);
    }

    [Theory]
    [InlineData("ordinary")]
    [InlineData("exception")]
    [InlineData("cancellation")]
    public async Task S0_Review_PreparationFailure_WakesAllWaiters_AndPublishesTheOriginalOutcome(string failure)
    {
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        Exception original = failure == "cancellation"
            ? new OperationCanceledException("host cancellation", cancellation.Token)
            : new InvalidOperationException("host preparation failure");
        var calls = 0;
        var probe = new Probe
        {
            PairOverride = HostOperation.CreateAsync("pair", async (_, _) =>
            {
                Interlocked.Increment(ref calls);
                entered.TrySetResult();
                await release.Task;
                if (failure != "ordinary") throw original;
                return new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2)]);
            }),
        };
        Result.CallReference? reference = null;
        probe.OnMeta = cells => { reference = Reify(cells[0]); return Zero; };
        var source = "F(*xs) = count(xs)\nProbe(x) = (Meta(x), x)\nProbe(F(pair()*"
            + (failure == "ordinary" ? ", (1 / 0)*" : "") + "))";
        var run = probe.ObserveAsyncTwin(source);
        try
        {
            await entered.Task.WaitAsync(TimeSpan.FromSeconds(30));
            var plan = reference!.Plan;
            var waiters = Enumerable.Range(0, 8)
                .Select(_ => plan.PrepareSupply(true).AsTask()).ToList();
            Assert.All(waiters, waiter => Assert.False(waiter.IsCompleted));
            using var started = new CountdownEvent(4);
            waiters.AddRange(Enumerable.Range(0, 4).Select(_ => Task.Factory.StartNew(() =>
            {
                started.Signal();
                return plan.PrepareSupply(false).GetAwaiter().GetResult();
            }, CancellationToken.None, TaskCreationOptions.LongRunning, TaskScheduler.Default)));
            Assert.True(started.Wait(TimeSpan.FromSeconds(30)));
            release.TrySetResult();
            if (failure == "ordinary")
            {
                Assert.StartsWith("err DivisionByZero", await run.WaitAsync(TimeSpan.FromSeconds(30)));
                var outcomes = await Task.WhenAll(waiters).WaitAsync(TimeSpan.FromSeconds(30));
                Assert.All(outcomes, outcome =>
                {
                    Assert.Equal(KatLangErrorCode.DivisionByZero, outcome.Error.Code);
                    Assert.Same(outcomes[0].Error, outcome.Error);
                });
                Assert.Same(outcomes[0].Error, (await plan.PrepareSupply(true)).Error);
                Assert.Equal(KatLangErrorCode.DivisionByZero, reference.Invoke().Error.Code);
            }
            else
            {
                Assert.Same(original, await Record.ExceptionAsync(() => run.WaitAsync(TimeSpan.FromSeconds(30))));
                foreach (var waiter in waiters)
                    Assert.Same(original, await Record.ExceptionAsync(async () =>
                        await waiter.WaitAsync(TimeSpan.FromSeconds(30))));
                Assert.Same(original, await Record.ExceptionAsync(async () => await plan.PrepareSupply(true)));
                Assert.Same(original, Record.Exception(() => reference.Invoke()));
                Assert.Same(original, Record.Exception(() => plan.Owner.Demand()));
            }
            Assert.True(plan.Owner.HasCompletedValue);
            Assert.Null(plan.PreparedCells);
            Assert.Equal(1, plan.SupplyFormations);
            Assert.Equal(1, calls);
            Assert.Equal(0, plan.Owner.ActiveDependencyCount);
            Assert.Same(reference, Reify(plan.Owner));
        }
        finally
        {
            release.TrySetResult();
        }
    }
}
