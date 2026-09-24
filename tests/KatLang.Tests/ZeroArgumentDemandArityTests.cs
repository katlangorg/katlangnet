using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// ZERO-ARGUMENT VALUE DEMAND FOLLOWS ACTUAL CALL ARITY (September 2026).
///
/// <para>A callable may satisfy a zero-argument value demand IF AND ONLY IF an ordinary
/// call supplying zero arguments can bind it (C#
/// <c>Evaluator.AcceptsZeroSuppliedArguments</c> over
/// <c>ParameterPattern.MinimumSuppliedSlots</c>, Lean
/// <c>Algorithm.acceptsZeroSuppliedArguments</c> over
/// <c>ParameterPattern.minimumSuppliedSlots</c> — the very rule the binder enforces).
/// A COLLECTING parameter contributes ZERO required slots, so <c>Only(*xs) = xs</c> is a
/// valid value expression exactly because <c>Only()</c> is legal; <c>Head(x, *rest)</c>
/// still requires one supplied value and stays rejected, reporting that MINIMUM rather
/// than its two declared captures.</para>
///
/// <para>The rule changes ELIGIBILITY only. Cache policy, evaluation counts, laziness,
/// the algorithm/callback channel, and the front end's value-context lifting decision are
/// all unchanged — this suite pins each of those separately from the eligibility law.</para>
/// </summary>
public class ZeroArgumentDemandArityTests
{
    // ── Fixtures: one signature family per accepted/rejected shape ──────────

    /// <summary>
    /// Representative signature families and the MINIMUM supplied-argument count their
    /// binder enforces. <c>null</c> means the callable accepts an empty supply.
    /// </summary>
    public static TheoryData<string, string, bool, int?> SignatureFamilies() => new()
    {
        { "Zero = 42", "Zero", true, null },
        { "Only(*xs) = xs", "Only", true, null },
        { "Head(x, *rest) = x", "Head", false, 1 },
        { "Tail(*rest, z) = z", "Tail", false, 1 },
        { "Mid(x, *rest, z) = x", "Mid", false, 2 },
        { "Pair(x, y) = x + y", "Pair", false, 2 },
        { "One((x)) = x", "One", false, 1 },
        { "GroupedCollecting((x, *rest)) = x", "GroupedCollecting", false, 1 },
        { "GroupedOnly((*xs)) = xs", "GroupedOnly", false, 1 },
        { "GroupThenCollecting((a, b), *rest) = a", "GroupThenCollecting", false, 1 },
        // A clause family with no zero-arity branch: both spellings fail, and the failure
        // is the ordinary dispatch one rather than an arity report.
        { "Fam(0) = 1\nFam(x) = 2", "Fam", false, null },
    };

    private static EvalResult<Result> Eval(string source)
        => Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));

    private static EvalError Innermost(EvalError error)
        => error is EvalError.WithContext context ? Innermost(context.Inner) : error;

    private static IReadOnlyList<Decimal128> Atoms(EvalResult<Result> result)
    {
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        return result.Value.ToAtoms();
    }

    private static void AssertEmptyList(EvalResult<Result> result)
    {
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal(new Result.ListValue([]), result.Value, Result.ValueComparer);
    }

    // ── 1. The metamorphic law: eligibility(F) == legality(F()) ─────────────

    /// <summary>
    /// THE LAW. For every signature family, a bare demand of <c>F</c> succeeds exactly
    /// when the ordinary call <c>F()</c> succeeds. This compares LEGALITY only — cache
    /// behavior and evaluation counts are pinned separately below, because the rule
    /// deliberately does not make the two spellings operationally identical.
    /// </summary>
    [Theory]
    [MemberData(nameof(SignatureFamilies))]
    public void ZeroDemandEligibility_AgreesWithZeroCallLegality(
        string declaration,
        string name,
        bool acceptsZeroSupply,
        int? minimumSupply)
    {
        var demand = Eval($"{declaration}\n{name}");
        var call = Eval($"{declaration}\n{name}()");

        Assert.Equal(call.IsError, demand.IsError);
        Assert.Equal(acceptsZeroSupply, !demand.IsError);

        if (acceptsZeroSupply)
        {
            // Both spellings denote the same value; only their cache behavior differs.
            Assert.Equal(demand.Value, call.Value, Result.ValueComparer);
            return;
        }

        if (minimumSupply is not { } minimum)
            return;

        // The rejected side reports the callable's TRUE minimum supplied count on both
        // sides — never the flattened declared capture count.
        var demandArity = Assert.IsType<EvalError.ArityMismatch>(Innermost(demand.Error));
        Assert.Equal(minimum, demandArity.Expected);
        Assert.Equal(0, demandArity.Actual);

        switch (Innermost(call.Error))
        {
            case EvalError.ArityMismatch callArity:
                Assert.Equal(minimum, callArity.Expected);
                Assert.Equal(0, callArity.Actual);
                break;
            case EvalError.VariadicArityMismatch variadic:
                Assert.Equal(minimum, variadic.ExpectedMinimum);
                Assert.Equal(0, variadic.Actual);
                break;
            default:
                Assert.Fail($"Unexpected zero-argument call rejection: {call.Error}");
                break;
        }
    }

    /// <summary>
    /// Host-built equivalents of the same families, so the rule is deterministic for
    /// signatures a host constructs directly rather than only for parsed ones. A pattern
    /// with ZERO captures still consumes its supplied slot.
    /// </summary>
    [Fact]
    public void HostBuiltSignatures_DecideTheSameWay()
    {
        static Algorithm.User Callee(params ParameterPattern[] patterns)
            => new(null, patterns, [], [], [new Expr.Num(5)]);

        static EvalResult<Result> RunWith(Algorithm.User callee, bool explicitCall)
            => Evaluator.Run(new Expr.AlgorithmExpr(new Algorithm.User(
                Parent: null,
                ParameterPatterns: [],
                Opens: [],
                Properties: [new Property("F", callee)],
                Output:
                [
                    explicitCall
                        ? new Expr.Call(new Expr.Resolve("F"), OutputBundle.Empty)
                        : new Expr.Resolve("F"),
                ])));

        var collectingOnly = Callee(new CaptureParameterPattern("xs", Kind: ParameterKind.Collecting));
        var captureless = Callee(new SequenceValueParameterPattern([]));
        var requiredPrefix = Callee(
            new CaptureParameterPattern("x"),
            new CaptureParameterPattern("rest", Kind: ParameterKind.Collecting));
        var emptyTopLevel = Callee();
        var capturelessThenCollector = Callee(new SequenceValueParameterPattern([]),
            new CaptureParameterPattern("rest", Kind: ParameterKind.Collecting));

        foreach (var (callee, accepts) in new[]
        {
            (collectingOnly, true), (captureless, false), (requiredPrefix, false),
            (emptyTopLevel, true), (capturelessThenCollector, false),
        })
        {
            var demand = RunWith(callee, explicitCall: false);
            var call = RunWith(callee, explicitCall: true);
            Assert.Equal(call.IsError, demand.IsError);
            Assert.Equal(accepts, !demand.IsError);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task HostBuiltBlockInWrittenSlot_UsesTheOrdinaryDemandLaw(bool zeroArityFamily)
    {
        Algorithm callable = zeroArityFamily
            ? new Algorithm.Conditional(null, [],
                [new CondBranch(new Pattern.SequenceValue([]), new Algorithm.User(null, [], [], [], [new Expr.Num(7)]))])
            : new Algorithm.User(null, [new SequenceValueParameterPattern([])], [], [], [new Expr.Num(5)]);
        var block = new Expr.AlgorithmExpr(callable);
        // These host-built blocks both have zero CAPTURES. One accepts an empty call;
        // the other requires one supplied slot. A list/capture must preserve that decision.
        Assert.Equal(zeroArityFamily, Evaluator.AcceptsZeroSuppliedArguments(callable));
        foreach (var row in new Expr[] { block, new Expr.Capture([block]), new Expr.ListLiteral([block]) })
        {
            var ast = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [row]));
            var sync = Evaluator.Run(ast);
            var asyncResult = await AsyncEvaluationHarness.Complete(
                Evaluator.RunAsync(ast, new RunScopedAsyncZeroArgPropertyResultCache()));
            Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(asyncResult));
            if (zeroArityFamily)
            {
                Assert.False(sync.IsError, sync.IsError ? sync.Error.ToString() : null);
                Result expected = row is Expr.ListLiteral ? new Result.ListValue([new Result.Atom(7)]) : new Result.Atom(7);
                Assert.Equal(expected, sync.Value, Result.ValueComparer);
            }
            else
            {
                Assert.True(sync.IsError);
                Assert.IsType<EvalError.UnresolvedImplicitParams>(Innermost(sync.Error));
            }
        }
    }

    [Theory]
    [InlineData("take(Source, Next())")]
    [InlineData("Source.take(Next())")]
    public void CollectionValueDemand_PreservesArgumentEffectOrder(string row)
    {
        var effects = new List<string>();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("Data", (_, _) => { effects.Add("source"); return new Result.ListValue([new Result.Atom(7)]); }),
                HostOperation.Create("Next", (_, _) => { effects.Add("control"); return new Result.Atom(1); })),
        };
        var result = KatLangEngine.Run($"Source(*xs) = Data()\n{row}", options);
        Assert.Equal("[7]", Assert.IsType<RunResult.Success>(result).ToDisplayString());
        Assert.Equal(["source", "control"], effects);
    }

    [Fact]
    public async Task CollectionValueDemand_SuspendsBeforeLaterArgumentEffects()
    {
        var gate = new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously);
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var effects = new List<string>();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Data", async (_, _) =>
                {
                    effects.Add("source");
                    entered.SetResult();
                    return await gate.Task;
                }),
                HostOperation.Create("Next", (_, _) => { effects.Add("control"); return new Result.Atom(1); })),
        };
        var run = KatLangEngine.RunAsync("Source(*xs) = Data()\ntake(Source, Next())", options);
        await entered.Task.WaitAsync(TimeSpan.FromSeconds(45));
        Assert.False(run.IsCompleted);
        Assert.Equal(["source"], effects);
        gate.SetResult(new Result.ListValue([new Result.Atom(7)]));
        Assert.Equal("[7]", Assert.IsType<RunResult.Success>(await run.WaitAsync(TimeSpan.FromSeconds(45))).ToDisplayString());
        Assert.Equal(["source", "control"], effects);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ZeroArityFamily_InAnUnusedCallbackSlot_IsNeverValueDemanded(bool inlineBlock)
    {
        var invocations = 0;
        var host = HostOperations.Create(HostOperation.Create("Tick", (_, _) =>
        {
            invocations++;
            return new Result.Atom(7);
        }));
        var family = new Algorithm.Conditional(null, [],
            [new CondBranch(new Pattern.SequenceValue([]), new Algorithm.User(null, [], [], [],
                [new Expr.Call(new Expr.Resolve("Tick"), OutputBundle.Empty)]))]);
        var ast = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("F", family)],
            [new Expr.Call(new Expr.Resolve("map"), [new Expr.ListLiteral([]),
                inlineBlock ? new Expr.AlgorithmExpr(family) : new Expr.Resolve("F")])]));
        AssertEmptyList(Evaluator.Run(ast, host, limits: null, randomSeed: null, cancellationToken: default));
        AssertEmptyList(await AsyncEvaluationHarness.Complete(
            Evaluator.RunAsync(ast, new RunScopedAsyncZeroArgPropertyResultCache(), hostOperations: host)));
        Assert.Equal(0, invocations);
    }

    [Theory]
    [InlineData("S.filter(P).count")]
    [InlineData("count(S.filter(P))")]
    public void FilterCountFusion_DemandsCollectingSourceOnce_AndPreservesBudget(string row)
    {
        var calls = 0;
        var host = HostOperations.Create(HostOperation.Create("Data", (_, _) =>
        {
            calls++;
            return new Result.ListValue([new Result.Atom(1), new Result.Atom(2), new Result.Atom(3)]);
        }));
        var source = $"S(*xs) = Data()\nP(x) = x > 1\n{row}";
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = host });
        Assert.Empty(parsed.Diagnostics);
        var ast = new Expr.AlgorithmExpr(parsed.Root);
        var diagnostics = new SequencePipelineDiagnostics();
        var (fused, fusedBudget) = Evaluator.RunCountedObserved(ast, sequenceDiagnostics: diagnostics, hostOperations: host);
        Assert.Equal(1, diagnostics.GetSnapshot().FilterCountFusionHits);
        Assert.Equal(1, calls);
        var (generic, genericBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false, hostOperations: host);
        Assert.Equal(2, calls);
        Assert.Equal([2m], fused.Value.Value.ToAtoms());
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(fused));
        Assert.Equal(genericBudget.ConsumedSteps, fusedBudget.ConsumedSteps);
        Assert.Equal(genericBudget.PeakDepth, fusedBudget.PeakDepth);
        Assert.Equal(0, fusedBudget.CurrentDepth);
    }

    [Fact]
    public void LocalCollectingPropertyCache_IsScopedToEachActivation()
    {
        const string source = """
            Outer(v) = {
                R(*xs) = v + Tick()
                R, R
            }
            Outer(2), Outer(10), Outer(2)
            """;
        var calls = 0;
        var host = HostOperations.Create(HostOperation.Create("Tick", (_, _) => new Result.Atom(++calls)));
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = host });
        Assert.Empty(parsed.Diagnostics);
        var cache = new CountingCache();
        var (result, _) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root),
            zeroArgPropertyResultCache: cache, hostOperations: host);
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([3m, 3m, 12m, 12m, 5m, 5m], result.Value.Value.ToAtoms());
        Assert.Equal(3, calls);
        Assert.Equal(6, cache.Requests.GetValueOrDefault("R"));
        Assert.Equal(3, cache.Evaluations.GetValueOrDefault("R"));
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    public async Task DeepDemandChains_RespectTheSameDepthBudget(int collectingMode)
    {
        var properties = Enumerable.Range(0, 48).Select(index => new Property($"P{index}",
            new Algorithm.User(null,
                collectingMode == 1 || collectingMode == 2 && index % 2 == 0
                    ? [new CaptureParameterPattern($"xs{index}", Kind: ParameterKind.Collecting)] : [],
                [], [], [index == 47 ? new Expr.Num(7) : new Expr.Resolve($"P{index + 1}")]))).ToArray();
        var ast = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], properties, [new Expr.Resolve("P0")]));
        foreach (var limit in new[] { 24, 64 })
        {
            var (sync, budget) = Evaluator.RunCountedObserved(ast, new EvaluationLimits { MaxDepth = limit });
            var (asyncResult, asyncBudget) = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
                ast, new EvaluationLimits { MaxDepth = limit }, new RunScopedAsyncZeroArgPropertyResultCache()));
            Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(asyncResult));
            Assert.Equal(budget.PeakDepth, asyncBudget.PeakDepth);
            Assert.Equal(budget.ConsumedSteps, asyncBudget.ConsumedSteps);
            Assert.Equal(0, budget.CurrentDepth);
            Assert.Equal(0, asyncBudget.CurrentDepth);
            if (limit == 24)
                Assert.IsType<EvalError.EvaluationDepthExceeded>(Innermost(sync.Error));
            else
            {
                Assert.False(sync.IsError, sync.IsError ? sync.Error.ToString() : null);
                Assert.Equal([7m], sync.Value.Value.ToAtoms());
                Assert.Equal(48, budget.PeakDepth);
            }
        }
    }

    [Fact]
    public async Task RecursiveCollectingDemand_IsBoundedWithoutCacheDeadlock()
    {
        var ast = AsyncEvaluationHarness.Ast("R(*xs) = R\nR");
        var limits = new EvaluationLimits { MaxDepth = 24 };
        var sync = Evaluator.Run(ast, limits);
        var asyncResult = await AsyncEvaluationHarness.Complete(
            Evaluator.RunAsync(ast, new RunScopedAsyncZeroArgPropertyResultCache(), limits));
        Assert.IsType<EvalError.EvaluationDepthExceeded>(Innermost(sync.Error));
        Assert.IsType<EvalError.EvaluationDepthExceeded>(Innermost(asyncResult.Error));
    }

    [Fact]
    public void CollectingLocalProperty_DeclinesTempPlanning_InsideAnActuallyPlannedLoop()
    {
        const string source = "Step(s, prior) = { R(*xs) = s\ns + 1, R }\nrepeat(Step, 3, 0, 0)";
        var ast = AsyncEvaluationHarness.Ast(source);
        var diagnostics = new LoopOptimizationDiagnostics();
        var (planned, _) = Evaluator.RunCountedObserved(ast, loopDiagnostics: diagnostics);
        var (generic, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(planned));
        Assert.Equal([3m, 2m], planned.Value.Value.ToAtoms());
        var snapshot = diagnostics.GetSnapshot();
        Assert.True(snapshot.OptimizedLoopHits > 0);
        Assert.True(snapshot.PlannedExpressionHits > 0);
        Assert.Contains(snapshot.LoopPlans, plan => plan.Temps.Any(temp => temp.Name == "R" && !temp.Planned));
    }

    [Theory]
    [InlineData("F(x, *rest) = x", "7", "7")]
    [InlineData("F(*rest, x) = x", "7", "7")]
    [InlineData("F((*xs)) = xs", "[7]", "[7]")]
    [InlineData("F((x, y), *rest) = x", "[7, 8]", "7")]
    public void PlainAndCountedCallbackBinders_KeepTheSameTopLevelMinimum(string declaration, string argument, string expected)
    {
        string Display(string row) => Assert.IsType<RunResult.Success>(KatLangEngine.Run(declaration + "\n" + row)).ToDisplayString();
        Assert.Equal(expected, Display($"F({argument})"));
        Assert.Equal("[" + expected + "]", Display($"map([{argument}], F)"));
        Assert.IsType<EvalError.ArityMismatch>(Innermost(Eval(declaration + "\nF").Error));
        Assert.True(Eval(declaration + "\nF()").IsError);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    public void DemandChains_NearTheSupportedCeiling_AreSafeOnOneMiBStacks(int collectingMode)
    {
        var properties = Enumerable.Range(0, EvaluationLimits.MaxSupportedDepth - 1).Select(index => new Property($"P{index}",
            new Algorithm.User(null,
                collectingMode == 1 || collectingMode == 2 && index % 2 == 0
                    ? [new CaptureParameterPattern($"xs{index}", Kind: ParameterKind.Collecting)] : [],
                [], [], [index == EvaluationLimits.MaxSupportedDepth - 2 ? new Expr.Num(7) : new Expr.Resolve($"P{index + 1}")]))).ToArray();
        var ast = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], properties, [new Expr.Resolve("P0")]));
        foreach (var useAsync in new[] { false, true })
        {
            AstStructuralDepthProcessTests.RunOnThreadWithStack(1_048_576, () =>
            {
                var result = useAsync
                    ? Evaluator.RunAsync(ast, new RunScopedAsyncZeroArgPropertyResultCache()).GetAwaiter().GetResult()
                    : Evaluator.Run(ast);
                if (result.IsError)
                    Assert.IsType<EvalError.EvaluationStackExhausted>(Innermost(result.Error));
                else
                    Assert.Equal([7m], Atoms(result));
            });
        }
    }

    // ── 2. The core acceptance examples ────────────────────────────────────

    [Fact]
    public void BareCollectingOnlyCallable_IsAValidValueExpression_AtTheRootAndInEveryDemandPosition()
    {
        const string decl = "Only(*xs) = xs\n";
        AssertEmptyList(Eval(decl + "Only"));
        AssertEmptyList(Eval(decl + "Only()"));
        var (counted, _) = Evaluator.RunCountedObserved(AsyncEvaluationHarness.Ast(decl + "Only"));
        Assert.IsType<Result.ListValue>(counted.Value.Value);
        Assert.Equal(1, counted.Value.EmittedCount);
        AssertEmptyList(Eval(decl + "if(true, Only, 0)"));
        AssertEmptyList(Eval(decl + "take(Only, 0)"));
        AssertEmptyList(Eval("Obj = {\n  public M(*xs) = xs\n}\nObj.M"));

        // Collection builtins obtain the demanded value first and then apply their own
        // collection view; dotted and plain spellings agree.
        Assert.Equal([0m], Atoms(Eval(decl + "count(Only)")));
        Assert.Equal([0m], Atoms(Eval(decl + "Only.count")));
        Assert.Equal([0m], Atoms(Eval(decl + "sum(Only)")));
        Assert.Equal([0m], Atoms(Eval(decl + "Only.sum")));

        // A fixed user parameter that demands a value, and a nested property read.
        Assert.Equal([0m], Atoms(Eval(decl + "Id(v) = v.count\nId(Only)")));
        Assert.Equal([0m], Atoms(Eval(decl + "Outer = {\n  Inner = Only.count\n  Inner\n}\nOuter")));

        // Two root rows: the demand is one value per row.
        Assert.Equal([1m], Atoms(Eval(decl + "Only, 1")));
    }

    [Fact]
    public void ParenthesesAreTransparentToEligibility()
    {
        const string decl = "Only(*xs) = xs\n";
        AssertEmptyList(Eval(decl + "(Only)"));
        AssertEmptyList(Eval(decl + "((Only))"));
        Assert.Equal([0m], Atoms(Eval(decl + "(Only).count")));
        Assert.Equal([0m], Atoms(Eval(decl + "((Only)).count")));

        // The rejected side is transparent too.
        const string head = "Head(x, *rest) = x\n";
        Assert.True(Eval(head + "(Head)").IsError);
        Assert.True(Eval(head + "((Head))").IsError);
    }

    /// <summary>
    /// A nested pattern's scalar one-item fallback accepts ONE supplied value; it never
    /// means the callable accepts none. <c>P(7)</c> binds, <c>P()</c> and bare <c>P</c>
    /// both reject.
    /// </summary>
    [Fact]
    public void NestedPatternScalarFallback_DoesNotImplyZeroSupplyAcceptance()
    {
        const string decl = "P((*xs)) = xs\n";
        Assert.Equal(new Result.ListValue([new Result.Atom(7)]), Eval(decl + "P(7)").Value, Result.ValueComparer);
        Assert.Equal(new Result.ListValue([new Result.Atom(7)]), Eval(decl + "P([7])").Value, Result.ValueComparer);
        Assert.True(Eval(decl + "P()").IsError);
        Assert.True(Eval(decl + "P").IsError);

        const string pair = "Q((x, *rest)) = x, rest.count\n";
        Assert.Equal([7m, 0m], Atoms(Eval(pair + "Q(7)")));
        Assert.True(Eval(pair + "Q()").IsError);
        Assert.True(Eval(pair + "Q").IsError);
    }

    // ── 3. Value channel versus algorithm channel ──────────────────────────

    [Fact]
    public void AlgorithmValuedPositions_KeepTheAlgorithm()
    {
        static string Display(string source)
            => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString();

        // A callback parameter receives the callable itself: each element is collected,
        // so the demanded value `[]` never appears.
        Assert.Equal("[[1], [2]]", Display("Only(*xs) = xs\nmap((1, 2), Only)"));
        Assert.Equal("[3]", Display("Big(*xs) = xs.first > 2\nfilter((1, 2, 3), Big)"));

        // A loop step position is an algorithm position too.
        Assert.Equal("1", Display("Step(*s) = s.count\nrepeat(Step, 1, 9)"));

        // A higher-order algorithm argument bound to a fixed parameter keeps BOTH
        // channels: calling it supplies arguments, reading it demands the value.
        Assert.Equal("2", Display("Only(*xs) = xs\nApply(g) = g(1, 2).count\nApply(Only)"));
        Assert.Equal("0", Display("Only(*xs) = xs\nRead(g) = g.count\nRead(Only)"));
    }

    /// <summary>
    /// The front end's value-context LIFTING decision is made BEFORE the evaluator's
    /// demand law and is unchanged: an arithmetic operand, a list element, and a
    /// registry-strict Math argument still lift the referenced callable's parameters into
    /// the enclosing signature — for a collecting and a fixed parameter alike — instead of
    /// demanding the callable in place. The lifted parameter keeps its KIND, so a lifted
    /// COLLECTING parameter makes the root accept the empty supply (which is exactly what
    /// the explicit-call spelling of the same row does), while a lifted FIXED one still
    /// leaves the program with an argument nobody can supply.
    /// </summary>
    [Theory]
    [InlineData("Only + 1")]
    [InlineData("[Only]")]
    [InlineData("abs(Only)")]
    public void ValueContextLifting_IsUnchanged(string row)
    {
        var collectingRoot = SourceProvenance.ParseValid($"Only(*xs) = xs\n{row}").Root;
        var fixedRoot = SourceProvenance.ParseValid(
            $"Inc(x) = x + 1\n{row.Replace("Only", "Inc", StringComparison.Ordinal)}").Root;

        // Lifting happened in BOTH cases: the row's reference is not a bare name any more,
        // and the root gained the callee's parameter with the callee's own kind.
        var lifted = Assert.Single(collectingRoot.Parameters);
        Assert.Equal("xs", lifted.Name);
        Assert.Equal(ParameterKind.Collecting, lifted.Kind);

        var liftedFixed = Assert.Single(fixedRoot.Parameters);
        Assert.Equal("x", liftedFixed.Name);
        Assert.Equal(ParameterKind.Normal, liftedFixed.Kind);

        // The fixed lift still has an argument nobody can supply.
        var fixedResult = Evaluator.Run(new Expr.AlgorithmExpr(fixedRoot));
        Assert.True(fixedResult.IsError);
        Assert.IsType<EvalError.UnresolvedImplicitParams>(Innermost(fixedResult.Error));

        // The collecting lift accepts the empty supply, and the outcome is exactly the
        // one the explicitly called spelling of the same row produces.
        var collecting = Evaluator.Run(new Expr.AlgorithmExpr(collectingRoot));
        var explicitCall = Eval($"Only(*xs) = xs\n{row.Replace("Only", "Only()", StringComparison.Ordinal)}");
        Assert.Equal(explicitCall.IsError, collecting.IsError);
        if (collecting.IsError)
            Assert.Equal(Innermost(explicitCall.Error).Code, Innermost(collecting.Error).Code);
        else
            Assert.Equal(explicitCall.Value, collecting.Value, Result.ValueComparer);
    }

    // ── 4. Cache: eligibility changed, policy did not ──────────────────────

    /// <summary>
    /// Run-scoped cache that counts property-demand requests and ACTUAL evaluations by
    /// property name, mirroring <see cref="ZeroArgPropertyCacheScopeTests"/>.
    /// </summary>
    private sealed class CountingCache : IAsyncZeroArgPropertyResultCache
    {
        private readonly RunScopedAsyncZeroArgPropertyResultCache _inner = new();

        public Dictionary<string, int> Requests { get; } = new(StringComparer.Ordinal);

        public Dictionary<string, int> Evaluations { get; } = new(StringComparer.Ordinal);

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            Count(Requests, execution.Binding.Name);
            return _inner.GetOrEvaluate(execution, () =>
            {
                Count(Evaluations, execution.Binding.Name);
                return evaluate();
            });
        }

        public ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
            ZeroArgPropertyExecution execution,
            Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
        {
            Count(Requests, execution.Binding.Name);
            return _inner.GetOrEvaluateAsync(execution, () =>
            {
                Count(Evaluations, execution.Binding.Name);
                return evaluateAsync();
            });
        }

        private static void Count(Dictionary<string, int> counts, string name)
            => counts[name] = counts.GetValueOrDefault(name) + 1;
    }

    /// <summary>
    /// A newly eligible collecting-only property enters the ORDINARY property-demand
    /// path: repeated bare reads share one evaluation exactly as a zero-parameter
    /// property's do, while explicit <c>F()</c> calls keep their established cache
    /// bypass and re-evaluate. Eligibility is what changed; cache policy is not.
    /// </summary>
    [Fact]
    public void BareDemand_UsesTheOrdinaryPropertyCache_WhileExplicitCallsStillBypassIt()
    {
        static (CountingCache Cache, EvalResult<Result> Result) RunCounting(string source)
        {
            var cache = new CountingCache();
            return (cache, Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), cache));
        }

        // Three bare property-style reads: three cache requests, ONE evaluation.
        var (demandCache, demand) = RunCounting("Only(*xs) = xs\n(Only, Only, Only).count");
        Assert.Equal([3m], Atoms(demand));
        Assert.Equal(3, demandCache.Requests.GetValueOrDefault("Only"));
        Assert.Equal(1, demandCache.Evaluations.GetValueOrDefault("Only"));

        // Three explicit calls: the established call path never consults the cache.
        var (callCache, call) = RunCounting("Only(*xs) = xs\n(Only(), Only(), Only()).count");
        Assert.Equal([3m], Atoms(call));
        Assert.Equal(0, callCache.Requests.GetValueOrDefault("Only"));

        // The same contrast for a zero-parameter property, so the collecting signature is
        // demonstrably on the SAME path rather than on one of its own.
        var (zeroParameterCache, _) = RunCounting("A = 7\n(A, A, A).count");
        Assert.Equal(3, zeroParameterCache.Requests.GetValueOrDefault("A"));
        Assert.Equal(1, zeroParameterCache.Evaluations.GetValueOrDefault("A"));

        // A builtin VALUE slot demands its argument DIRECTLY and bypasses the entry, in
        // the dotted spelling exactly as in the written one — unchanged by this rule.
        var (dottedCache, dotted) = RunCounting("Only(*xs) = xs\nOnly.count, count(Only)");
        Assert.Equal([0m, 0m], Atoms(dotted));
        Assert.Equal(0, dottedCache.Requests.GetValueOrDefault("Only"));
    }

    /// <summary>
    /// A host-backed collecting-only property executes the expected number of times: once
    /// for three bare demands (the cache), once per explicit call. The operation counter
    /// is the observable, never a timing.
    /// </summary>
    [Fact]
    public void HostBackedEligibleProperty_ExecutesTheExpectedNumberOfTimes()
    {
        static (int Invocations, string Display) RunCounting(string source)
        {
            var invocations = 0;
            var options = new RunOptions
            {
                HostOperations = HostOperations.Create(
                    HostOperation.Create("Tick", (_, _) =>
                    {
                        invocations++;
                        return new Result.Atom(1);
                    })),
            };

            var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, options));
            return (invocations, result.ToDisplayString());
        }

        // Three bare demands share one cached evaluation, so the host operation runs ONCE.
        // `Tick()` is an explicit call, so the counter reflects `Only`'s BODY executions
        // rather than the host operation's own property-demand cache entry.
        var bare = RunCounting("Only(*xs) = xs, Tick()\n(Only, Only, Only).count");
        Assert.Equal("3", bare.Display);
        Assert.Equal(1, bare.Invocations);

        // Three explicit calls keep their established cache bypass: three executions.
        var explicitCalls = RunCounting("Only(*xs) = xs, Tick()\n(Only(), Only(), Only()).count");
        Assert.Equal("3", explicitCalls.Display);
        Assert.Equal(3, explicitCalls.Invocations);

        // A zero-parameter property behaves identically, confirming ONE shared policy.
        var zeroParameter = RunCounting("A = Tick()\n(A, A, A).count");
        Assert.Equal("3", zeroParameter.Display);
        Assert.Equal(1, zeroParameter.Invocations);
    }

    /// <summary>
    /// A random-backed newly eligible property consumes the expected number of draws from
    /// the run's seeded stream: one for three bare demands (one evaluation), three for
    /// three explicit calls. Two runs with one seed reproduce each other.
    /// </summary>
    [Theory]
    [InlineData(0L)]
    [InlineData(1L)]
    [InlineData(-1L)]
    [InlineData(20260922L)]
    public void RandomBackedEligibleProperty_ConsumesTheExpectedRandomStream(long seed)
    {
        string Run(string source)
            => Assert.IsType<RunResult.Success>(
                KatLangEngine.Run(source, new RunOptions { RandomSeed = seed })).ToDisplayString();

        const string draw = "randomInt(1, 1000000)";
        const string bare = "Only(*xs) = " + draw + "\nOnly, Only, Only, " + draw;
        const string called = "Only(*xs) = " + draw + "\nOnly(), Only(), Only(), " + draw;

        static string[] Lines(string display)
            => display.Split('\n').Select(static line => line.Trim()).ToArray();

        var bareValues = Lines(Run(bare));
        var calledValues = Lines(Run(called));
        var reference = Lines(Run(string.Join(", ", Enumerable.Repeat(draw, 4))));

        // A trailing independent draw proves the exact position of the stream, including
        // any hidden preliminary evaluation. Never assume random values are distinct.
        Assert.Equal([reference[0], reference[0], reference[0], reference[1]], bareValues);
        Assert.Equal(reference, calledValues);
        Assert.Equal(reference, Lines(Run("Only(*xs) = " + draw +
            "\nfirst(Only), Only.first, first((Only)), " + draw)));
    }

    // ── 5. Strategy parity: sync, async suspension, planned/generic ─────────

    /// <summary>
    /// The sync evaluator, the async twin under GENUINE suspension, and the run with loop
    /// optimization disabled all agree on the demanded value.
    /// </summary>
    [Fact]
    public async Task SyncAsyncAndGenericStrategies_Agree()
    {
        // `Only` is read as a bare property (the cache seam, where the async twin
        // suspends), inside a loop step (planned versus generic), and through a
        // collection builtin in both spellings.
        const string source = """
            Only(*xs) = xs
            Step(s) = s + (Only, Only).count
            repeat(Step, 3, 0), Only.count, count(Only), (Only, Only).count
            """;

        var ast = AsyncEvaluationHarness.Ast(source);
        var sync = Evaluator.Run(ast);
        var generic = Evaluator.Run(ast, new RunScopedAsyncZeroArgPropertyResultCache(), enableLoopOptimization: false);

        var suspending = new SuspendingAsyncZeroArgPropertyResultCache();
        var asyncResult = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedAsync(ast, suspending));

        Assert.Equal([6m, 0m, 0m, 2m], Atoms(sync));
        Assert.Equal([6m, 0m, 0m, 2m], Atoms(generic));
        Assert.False(asyncResult.IsError, asyncResult.IsError ? asyncResult.Error.ToString() : null);
        Assert.Equal([6m, 0m, 0m, 2m], asyncResult.Value.Value.ToAtoms());

        // The async run genuinely suspended and resumed on the property seam.
        Assert.True(suspending.AsyncAccesses > 0);
        Assert.True(suspending.ObservedThreadHop);
    }

    /// <summary>
    /// A newly eligible property backed by a genuinely suspending host operation is
    /// demanded, suspends, and executes its body exactly once across resumption; the
    /// cached value then serves the later reads.
    /// </summary>
    [Fact]
    public async Task SuspendingHostOperation_BehindAnEligibleProperty_ExecutesOnce()
    {
        var gate = new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously);
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var invocations = 0;

        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Held", async (_, _) =>
                {
                    Interlocked.Increment(ref invocations);
                    reached.TrySetResult();
                    return await gate.Task;
                })),
        };

        var run = KatLangEngine.RunAsync("Only(*xs) = Held()\n(Only, Only).count", options);

        var arrived = await Task.WhenAny(reached.Task, Task.Delay(TimeSpan.FromSeconds(45)));
        Assert.Same(reached.Task, arrived);
        Assert.False(run.IsCompleted);

        gate.TrySetResult(new Result.Atom(5));
        var completed = await Task.WhenAny(run, Task.Delay(TimeSpan.FromSeconds(45)));
        Assert.Same(run, completed);

        Assert.Equal("2", Assert.IsType<RunResult.Success>(await run).ToDisplayString());
        Assert.Equal(1, Volatile.Read(ref invocations));
    }

    /// <summary>
    /// Cancellation while a newly eligible property's demand is suspended propagates as
    /// <see cref="OperationCanceledException"/> and the later effect never runs.
    /// </summary>
    [Fact]
    public async Task CancellationDuringAnEligibleDemand_Propagates_AndLaterEffectsDoNotRun()
    {
        using var cancellation = new CancellationTokenSource();
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var gate = new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously);
        var laterInvocations = 0;
        var heldInvocations = 0;

        var options = new RunOptions
        {
            EvaluationCancellationToken = cancellation.Token,
            HostOperations = HostOperations.Create(
                HostOperation.CreateAsync("Held", async (_, _) =>
                {
                    Interlocked.Increment(ref heldInvocations);
                    reached.TrySetResult();
                    return await gate.Task;
                }),
                HostOperation.Create("Later", (_, _) =>
                {
                    Interlocked.Increment(ref laterInvocations);
                    return new Result.Atom(1);
                })),
        };

        var run = KatLangEngine.RunAsync("Only(*xs) = Held()\n(Only, Only).count + Later", options);

        var arrived = await Task.WhenAny(reached.Task, Task.Delay(TimeSpan.FromSeconds(45)));
        Assert.Same(reached.Task, arrived);
        Assert.False(run.IsCompleted);

        await cancellation.CancelAsync();
        gate.TrySetResult(new Result.Atom(5));

        var exception = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await run.WaitAsync(TimeSpan.FromSeconds(45)));
        Assert.Equal(cancellation.Token, exception.CancellationToken);
        Assert.Equal(0, Volatile.Read(ref laterInvocations));
        Assert.Equal(1, Volatile.Read(ref heldInvocations));

        // Reuse the exact host-operation configuration in an independent run. Neither
        // the suspended value nor a cancellation result may leak through the cache.
        var retry = await KatLangEngine.RunAsync("Only(*xs) = Held()\n(Only, Only).count + Later",
            new RunOptions { HostOperations = options.HostOperations });
        Assert.Equal("3", Assert.IsType<RunResult.Success>(retry).ToDisplayString());
        Assert.Equal(2, Volatile.Read(ref heldInvocations));
        Assert.Equal(1, Volatile.Read(ref laterInvocations));
    }

    // ── 6. Diagnostics of the rejected side ────────────────────────────────

    /// <summary>
    /// A rejected bare demand reports the MINIMUM supplied count it actually requires,
    /// with the demand-site span and the ordinary property context. Before this rule it
    /// reported the flattened declared capture count (2 for <c>Head(x, *rest)</c>, 2 for
    /// <c>P((x, y))</c>), which no zero-argument call ever claimed.
    /// </summary>
    [Theory]
    [InlineData("Head(x, *rest) = x", "Head", 1)]
    [InlineData("Tail(*rest, z) = z", "Tail", 1)]
    [InlineData("Mid(x, *rest, z) = x", "Mid", 2)]
    [InlineData("Pair(x, y) = x + y", "Pair", 2)]
    [InlineData("P((x, y)) = x + y", "P", 1)]
    [InlineData("G((a, b), *rest) = a", "G", 1)]
    public void RejectedDemand_ReportsTheMinimumSuppliedCount(string declaration, string name, int minimum)
    {
        var result = Eval($"{declaration}\n{name}");
        Assert.True(result.IsError);

        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
        Assert.Equal(minimum, arity.Expected);
        Assert.Equal(0, arity.Actual);

        var rendered = KatLangError.FromEvalError(result.Error);
        Assert.Equal(KatLangErrorCode.ArityMismatch, rendered.Code);
        Assert.Contains($"Property '{name}' expects {minimum} parameter", rendered.Message, StringComparison.Ordinal);
        Assert.Equal(2, Assert.NotNull(rendered.Span).Start.Line);
        Assert.Equal(1, Assert.NotNull(rendered.Span).Start.Column);
    }

    /// <summary>
    /// A clause family's bare demand keeps the ordinary zero-argument dispatch failure
    /// (no branch matches an empty argument list), naming the family.
    /// </summary>
    [Fact]
    public void ClauseFamilyWithoutAZeroArityBranch_KeepsItsOrdinaryFailure()
    {
        var demand = Eval("Fam(0) = 1\nFam(x) = 2\nFam");
        var call = Eval("Fam(0) = 1\nFam(x) = 2\nFam()");

        Assert.Equal("Fam", Assert.IsType<EvalError.NoMatchingBranch>(Innermost(demand.Error)).AlgorithmName);
        Assert.Equal("Fam", Assert.IsType<EvalError.NoMatchingBranch>(Innermost(call.Error)).AlgorithmName);
    }

    /// <summary>
    /// A host-built clause family whose branch pattern has top-level arity ZERO genuinely
    /// dispatches for <c>F()</c>, so bare <c>F</c> is eligible too and selects the same
    /// branch. This is the family side of the eligibility equivalence.
    /// </summary>
    [Fact]
    public void ClauseFamilyWithAZeroArityBranch_IsDemandable()
    {
        var family = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches: [new CondBranch(new Pattern.SequenceValue([]), new Algorithm.User(null, [], [], [], [new Expr.Num(7)]))]);

        static EvalResult<Result> RunWith(Algorithm family, Expr row)
            => Evaluator.Run(new Expr.AlgorithmExpr(new Algorithm.User(
                Parent: null,
                ParameterPatterns: [],
                Opens: [],
                Properties: [new Property("F", family)],
                Output: [row])));

        var demand = RunWith(family, new Expr.Resolve("F"));
        var call = RunWith(family, new Expr.Call(new Expr.Resolve("F"), OutputBundle.Empty));

        Assert.Equal([7m], Atoms(demand));
        Assert.Equal([7m], Atoms(call));
    }

    // ── 7. Builtins keep their own rejection ───────────────────────────────

    /// <summary>
    /// A builtin accepts no zero-argument supply, and its rejection stays the builtin's
    /// own signature-worded arity error — the very message <c>sum()</c> produces — not a
    /// parameter-list report from the demand law.
    /// </summary>
    [Theory]
    [InlineData("sum")]
    [InlineData("count")]
    [InlineData("first")]
    [InlineData("last")]
    [InlineData("take")]
    [InlineData("skip")]
    [InlineData("map")]
    [InlineData("filter")]
    [InlineData("reduce")]
    [InlineData("range")]
    [InlineData("contains")]
    [InlineData("atoms")]
    public void BuiltinDemand_KeepsTheBuiltinsOwnArityRejection(string builtin)
    {
        var demand = Eval(builtin);
        var call = Eval(builtin + "()");

        Assert.True(demand.IsError);
        Assert.True(call.IsError);
        Assert.Equal(
            KatLangError.FromEvalError(call.Error).Message,
            KatLangError.FromEvalError(demand.Error).Message);
        Assert.Equal(Innermost(call.Error).Code, Innermost(demand.Error).Code);
    }
}
