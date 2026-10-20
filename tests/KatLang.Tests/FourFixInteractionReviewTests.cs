using KatLang.Evaluation;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

public class FourFixInteractionReviewTests
{
    [Theory]
    [InlineData(50)]
    [InlineData(100)]
    public void ParentChainAlsoReachedThroughProperties_StaysLinear(int length)
    {
        ScopeCtx? scope = null;
        for (var index = 0; index < length; index++)
            scope = new ScopeCtx(scope, [], [new($"P{index}", new Algorithm.User(scope, [], [], [], [new Expr.Num(1)]))]);
        var expression = new Expr.AlgorithmExpr(new Algorithm.User(scope, [], [], [], [new Expr.Num(7)]));
        var observations = new FrontEndTraversalObservations();
        Assert.Null(AlgorithmValidation.FindFirstPreEvaluationViolation(expression, observations));
        Assert.Equal(length, observations.PreEvaluationParentScopeExpansions);
        Assert.Equal(2 * length - 1, observations.PreEvaluationParentScopeLinks);
        Assert.Equal(length + 1, observations.WalkerAlgorithmExpansions);
        Assert.Equal(new Result.Atom(7), Evaluator.Run(expression).Value);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SharedOuterScope_ReachedByAnEarlierProperty_PreservesDepthFirstErrorOrder(bool earlierEdge)
    {
        var outer = new ScopeCtx(null, [], [new("OuterBad", new Algorithm.User(null,
            [new CaptureParameterPattern("a", Kind: ParameterKind.Collecting),
             new CaptureParameterPattern("b", Kind: ParameterKind.Collecting)], [], [], [new Expr.Num(1)]))]);
        var inner = new ScopeCtx(outer, [],
            [new("P", new Algorithm.User(earlierEdge ? outer : null, [], [], [], [new Expr.Num(1)])),
             new("InnerBad", new Algorithm.User(null,
                [new SequenceValueParameterPattern([new CaptureParameterPattern("x")])], [], [], [new Expr.Num(1)]))]);
        var expression = OpenedThrough(inner, new Expr.Num(7));
        var (result, budget) = Evaluator.RunCountedObserved(expression);
        Assert.Equal(earlierEdge ? Parser.MultipleCollectingBindingsPerLevelDiagnostic : Parser.SingletonSequencePatternDiagnostic,
            Assert.IsType<EvalError.IllegalInEval>(result.Error).Reason);
        Assert.Equal(0, budget.ConsumedSteps);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void NonRefusalExceptionFromHostHead_IsNotSwallowedByEligibility(bool cancellation)
    {
        // Stable membership, but a host implementation can fail one read. The failure is armed
        // after preflight, in the repeat count. A broad catch would hide it and run the step.
        var failure = cancellation ? (Exception)new OperationCanceledException() : new ArgumentException("host head read");
        var head = new FailingHostHead(failure);
        var arm = HostOperation.Create("arm", (_, _) => { head.Armed = true; return new Result.Atom(1); });
        var step = new Algorithm.User(null, head, [], [], [new Expr.Param("x")]);
        // META-S3-3: the step is named and its captured call `S(3)` supplies the initial state; the count
        // is demanded after that supply is prepared (RP-1), still before the first iteration.
        var expression = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("S", step)],
            [new Expr.Call(new Expr.Resolve("repeat"),
                [new Expr.Call(new Expr.Resolve("S"), [new Expr.Num(3)]), new Expr.NativeCall(arm.NativeName, [])])]));
        var loops = new LoopOptimizationDiagnostics();
        var observations = new EvaluationObservations();
        var thrown = Record.Exception(() => Evaluator.RunCountedObserved(expression,
            loopDiagnostics: loops, observations: observations, hostOperations: HostOperations.Create(arm)));
        Assert.Same(failure, thrown);
        Assert.False(head.Armed);
        Assert.Equal(0, loops.OptimizedLoopHits);
        Assert.Equal(0, observations.GenericLoopStepBindingPreparationCount);
    }

    private sealed class FailingHostHead(Exception failure) : IReadOnlyList<ParameterPattern>
    {
        private static readonly ParameterPattern Capture = new CaptureParameterPattern("x");
        public bool Armed { get; set; }
        public int Count
        {
            get
            {
                if (Armed) { Armed = false; throw failure; }
                return 1;
            }
        }
        public ParameterPattern this[int index] => index == 0 ? Capture : throw new ArgumentOutOfRangeException(nameof(index));
        public IEnumerator<ParameterPattern> GetEnumerator()
        {
            _ = Count;
            yield return Capture;
        }
        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    [Fact]
    public void ReusedHostScope_IsValidatedAgainAfterChangesBetweenRuns()
    {
        var members = new List<Property> { new("V", new Algorithm.User(null, [], [], [], [new Expr.Num(7)])) };
        var expression = OpenedThrough(new ScopeCtx(null, [], members), new Expr.Num(7));
        Assert.Equal(new Result.Atom(7), Evaluator.Run(expression).Value);
        members.Add(new("Bad", new Algorithm.User(null,
            [new CaptureParameterPattern("a", Kind: ParameterKind.Collecting),
             new CaptureParameterPattern("b", Kind: ParameterKind.Collecting)], [], [], [new Expr.Num(1)])));
        var (refused, budget) = Evaluator.RunCountedObserved(expression);
        Assert.Equal(Parser.MultipleCollectingBindingsPerLevelDiagnostic,
            Assert.IsType<EvalError.IllegalInEval>(refused.Error).Reason);
        Assert.Equal(0, budget.ConsumedSteps);
    }

    [Fact]
    public async Task ShadowedAncestorAliasChain_ResolvesAtEachDeclaringScope()
    {
        var step = new Algorithm.User(null, [new CaptureParameterPattern("x")], [], [],
            [new Expr.Binary(BinaryOp.Add, new Expr.Param("x"), new Expr.Num(1))]);
        var outer = new ScopeCtx(null, [],
            [new("A", step), new("B", new Algorithm.Alias(null, [], [], new Expr.Resolve("A")))]);
        var inner = new ScopeCtx(outer, [], [new("A", new Algorithm.Alias(null, [], [], new Expr.Resolve("B")))]);
        var expression = OpenedThrough(inner, new Expr.Call(new Expr.AlgorithmExpr(new Algorithm.Builtin(BuiltinId.@repeat)),
            [new Expr.Call(new Expr.Resolve("A"), [new Expr.Num(0)]), new Expr.Num(3)]));
        Assert.Null(AlgorithmValidation.FindFirstPreEvaluationViolation(expression));
        var (generic, genericBudget) = Evaluator.RunCountedObserved(expression, enableOptimizations: false);
        var loops = new LoopOptimizationDiagnostics();
        var (planned, plannedBudget) = Evaluator.RunCountedObserved(expression, loopDiagnostics: loops);
        Assert.False(generic.IsError);
        Assert.Equal(new Result.Atom(3), generic.Value.Value);
        Assert.Equal(generic.Value, planned.Value);
        Assert.Equal(genericBudget.ConsumedSteps, plannedBudget.ConsumedSteps);
        Assert.Equal(1, loops.OptimizedLoopHits);
        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var (asyncResult, _) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
            expression, zeroArgPropertyResultCache: cache));
        Assert.Equal(generic.Value, asyncResult.Value);
        Assert.True(cache.AsyncAccesses > 0);
        Assert.Equal(0, cache.SyncAccesses);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ScopeGraphCycle_IsRefusedBeforeRecursiveValidation(bool optimize)
    {
        var members = new List<Property>();
        var scope = new ScopeCtx(null, [], members);
        members.Add(new("Cycle", new Algorithm.User(scope, [], [], [], [new Expr.Num(1)])));
        var expression = OpenedThrough(scope, new Expr.Num(7));
        var (result, budget) = Evaluator.RunCountedObserved(expression, enableOptimizations: optimize);
        Assert.IsType<EvalError.AstCycleDetected>(result.Error);
        Assert.Equal(0, budget.ConsumedSteps);
        var (asyncResult, _) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(expression));
        Assert.IsType<EvalError.AstCycleDetected>(asyncResult.Error);
    }

    [Theory]
    [InlineData("repeat", false, false)]
    [InlineData("repeat", false, true)]
    [InlineData("repeat", true, false)]
    [InlineData("repeat", true, true)]
    [InlineData("while", false, false)]
    [InlineData("while", false, true)]
    [InlineData("while", true, false)]
    [InlineData("while", true, true)]
    public async Task AncestorStep_ShadowedCaptureAndMutatedHead_SurviveHandover(
        string loop, bool collectors, bool failAfterHandover)
    {
        var generic = await Run(optimize: false, asynchronous: false);
        var planned = await Run(optimize: true, asynchronous: false);
        var suspending = await Run(optimize: false, asynchronous: true);
        Assert.Equal(generic.Outcome, planned.Outcome);
        Assert.Equal(generic.Outcome, suspending.Outcome);
        Assert.Equal(generic.Budget, planned.Budget);
        Assert.Equal(generic.Budget, suspending.Budget);
        // LOOP-06 (condition first): the stopping `while` round (state 11) reads only its flag
        // `state != 11`, so its transition row — the fifth `mutate()` under the retired step-first
        // order — is never formed: four calls on every loop and route.
        Assert.Equal(4, generic.Calls);
        Assert.Equal(generic.Calls, planned.Calls);
        Assert.Equal(generic.Calls, suspending.Calls);
        Assert.Equal(1, planned.Hits);
        Assert.Equal(1, planned.Handovers);
        Assert.Equal(1, planned.Preparations);
        Assert.Equal(1, generic.Preparations);
        Assert.Equal(1, suspending.Preparations);

        async Task<(string Outcome, LoopPlanEligibilityFailClosedTests.Budget Budget, int Calls,
            long Hits, long Handovers, long Preparations)> Run(bool optimize, bool asynchronous)
        {
            var head = new List<ParameterPattern>();
            var calls = 0;
            Result Mutate()
            {
                calls++;
                if (calls == 2)
                {
                    head.Clear();
                    if (collectors)
                    {
                        head.Add(new CaptureParameterPattern("state", Kind: ParameterKind.Collecting));
                        head.Add(new CaptureParameterPattern("other", Kind: ParameterKind.Collecting));
                    }
                }
                return new Result.Atom(calls);
            }
            var operations = HostOperations.Create(asynchronous
                ? HostOperation.CreateAsync("mutate", async (_, _) => { await Task.Yield(); return Mutate(); })
                : HostOperation.Create("mutate", (_, _) => Mutate()));
            var next = failAfterHandover ? "if(n == 4, 1 / 0, if(state == (), 10, state + 1))" : "if(state == (), 10, state + 1)";
            var source = "Call(state) = state()\nEmpty = ()\nNext(state, n) = if(n == 2, Empty, " + next + ")\nStep(state) = Call({ Next(state, mutate()) })"
                + (loop == "while" ? ", state != 11\nwhile(Step(0))" : "\nrepeat(Step(0), 4)");
            var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
            Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics.Select(d => d.Message)));
            var members = parsed.Root.Properties.ToArray();
            var index = Array.FindIndex(members, p => p.Name == "Step");
            var step = Assert.IsType<Algorithm.User>(members[index].Value);
            head.AddRange(step.ParameterPatterns);
            members[index] = members[index] with { Value = step with { ParameterPatterns = head } };
            var prelude = new ScopeCtx(null, [], operations.RuntimePreludeAlgorithm.Properties);
            var expression = OpenedThrough(new ScopeCtx(prelude, [], members), Assert.Single(parsed.Root.Output));
            var diagnostics = new LoopOptimizationDiagnostics();
            var observations = new EvaluationObservations();
            var cache = new SuspendingAsyncZeroArgPropertyResultCache();
            var (result, budget) = asynchronous
                ? await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(expression,
                    zeroArgPropertyResultCache: cache, loopDiagnostics: diagnostics, observations: observations, hostOperations: operations))
                : Evaluator.RunCountedObserved(expression, enableOptimizations: optimize,
                    loopDiagnostics: diagnostics, observations: observations, hostOperations: operations);
            Assert.True(head.Count == (collectors ? 2 : 0),
                $"Expected the rewrite after iteration 2; calls={calls}; result={(result.IsError ? result.Error.ToString() : result.Value.ToString())}");
            if (asynchronous) { Assert.True(cache.AsyncAccesses > 0); Assert.Equal(0, cache.SyncAccesses); }
            string outcome;
            if (failAfterHandover)
            {
                Assert.True(result.IsError);
                var reported = KatLangError.FromEvalError(result.Error);
                Assert.Equal(KatLangErrorCode.DivisionByZero, reported.Code);
                outcome = result.Error.ToString()!;
            }
            else
            {
                Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
                Assert.Equal(new Result.Atom(11), result.Value.Value);
                Assert.Equal(1, result.Value.EmittedCount);
                outcome = result.Value.ToString();
            }
            return (outcome, LoopPlanEligibilityFailClosedTests.Budget.Of(budget), calls,
                diagnostics.OptimizedLoopHits, observations.OptimizedLoopHandoverMaterializationCount,
                observations.GenericLoopStepBindingPreparationCount);
        }
    }

    private static Expr OpenedThrough(ScopeCtx scope, Expr row)
        => new Expr.AlgorithmExpr(new Algorithm.User(null, [],
            [new Expr.AlgorithmExpr(new Algorithm.User(scope, [], [],
                [new("Run", new Algorithm.User(null, [], [], [], [row]), IsPublic: true)], []))],
            [], [new Expr.Resolve("Run")]));

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task DeferredPlaceholder_StillValidatesItsHostParentBeforeAnyDemand(bool aliasCycle)
    {
        var fetches = 0;
        var parsed = await Parser.ParseAsync("F(0) = { open 'https://katlang.org/review.kat'\n V }\nF(n) = n\n7",
            new RunOptions { DownloadCode = (_, _) => { fetches++; return ValueTask.FromResult("public V = 1"); } });
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics.Select(d => d.Message)));
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.Root.Properties).Value);
        var placeholder = Assert.IsType<Algorithm.User>(family.Branches[0].Body);
        Assert.NotNull(placeholder.DeferredRegion);
        IReadOnlyList<Property> members = aliasCycle
            ? [new("A", new Algorithm.Alias(null, [], [], new Expr.Resolve("B"))),
               new("B", new Algorithm.Alias(null, [], [], new Expr.Resolve("A")))]
            : [new("Bad", new Algorithm.User(null,
                [new CaptureParameterPattern("a", Kind: ParameterKind.Collecting),
                 new CaptureParameterPattern("b", Kind: ParameterKind.Collecting)], [], [], [new Expr.Num(1)]))];
        var held = placeholder with { Parent = new ScopeCtx(null, [], members) };
        var branches = family.Branches.ToArray();
        branches[0] = branches[0] with { Body = held };
        var expression = new Expr.AlgorithmExpr(parsed.Root with { Properties = [new("F", family with { Branches = branches })] });
        var expected = aliasCycle ? Evaluator.AliasCycleMessage : Parser.MultipleCollectingBindingsPerLevelDiagnostic;

        var (asyncResult, asyncBudget) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(expression));
        Assert.True(asyncResult.IsError, "An undemanded placeholder must not hide an invalid host parent scope.");
        Assert.Equal(expected, Assert.IsType<EvalError.IllegalInEval>(asyncResult.Error).Reason);
        Assert.Equal(0, asyncBudget.ConsumedSteps);
        Assert.NotNull(AlgorithmValidation.FindFirstPreEvaluationViolation(expression));
        if (aliasCycle)
        {
            Assert.True(AstStructuralPreflight.ReachesAlias(expression, new(ReferenceEqualityComparer.Instance)));
            var heads = AstStructuralPreflight.AliasTargetHeads(expression);
            Assert.Contains("A", heads);
            Assert.Contains("B", heads);
        }
        Assert.Equal(0, fetches);
    }
}
