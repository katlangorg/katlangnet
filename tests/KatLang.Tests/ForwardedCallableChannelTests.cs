using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// A FORWARDED CALLABLE KEEPS ITS ALGORITHM CHANNEL IN INVOKING BUILTIN SLOTS (September 2026).
///
/// <para>A callable that can satisfy a zero-argument value demand (<c>Cnt(*xs) = xs.count</c>,
/// whose zero-argument value is 0) is bound on BOTH channels when it is passed to a user
/// parameter: <c>Apply(Cnt, xs)</c> binds <c>f</c>'s value to 0 and its algorithm to <c>Cnt</c>.
/// A builtin argument naming such a parameter used to resolve to the value side everywhere,
/// so <c>Apply(f, xs) = map(xs, f)</c> handed <c>map</c> a zero-parameter wrapper of the value
/// 0 and failed with "Expected 0 parameters", while <c>map(xs, Cnt)</c> mapped every element.</para>
///
/// <para>The rule now: a slot that INVOKES its argument — the <c>map</c> mapper, the
/// <c>filter</c> predicate, the <c>reduce</c> reducer, a <c>while</c>/<c>repeat</c> step —
/// invokes the parameter's ALGORITHM-channel binding
/// (<c>ResolvedArgumentAlgorithm.InvokedAlgorithm</c>; Lean <c>ResolvedArgumentAlgorithm.invoked</c>),
/// so direct and forwarded consumer slots invoke the same callable. Forwarding retains
/// ordinary eager binding effects; consumer selection adds no value demand. Every VALUE slot (the
/// collection, <c>reduce</c>'s <c>initial</c>, the loop state, the <c>if</c> branches) still
/// reads the bound value and never re-runs the callable's body. A parameter bound on the value
/// channel only has no algorithm binding and keeps its old behavior. Lean: the forwarded
/// callable guards in <c>CoreTests/ValueDemand.lean</c>; the
/// <c>forwarded-callable-keeps-its-algorithm-channel</c> spec case.</para>
/// </summary>
public class ForwardedCallableChannelTests
{
    private const string Callables =
        "Cnt(*xs) = xs.count\n"
        + "Only(*xs) = xs\n"
        + "Big(*xs) = xs.sum > 1\n"
        + "SumAll(*xs) = xs.sum\n"
        + "CountStep(*s) = s.count + 1\n"
        + "SumWhile(*s) = s.sum + 1, s.sum + 1 < 3\n"
        + "Z(*xs) = 10 / xs.count\n";

    /// <summary>
    /// Label, the direct program, the forwarded program, and the display both produce. Every
    /// forwarded callable except <c>Z</c> satisfies a zero-argument value demand, so each row
    /// failed before the fix; <c>Z</c>'s demand divides by zero, so it was never bound on the
    /// value channel and is the control.
    /// </summary>
    public static TheoryData<string, string, string, string> DirectAndForwarded => new()
    {
        { "map", "map([1, 2], Cnt)", "Apply(f, xs) = map(xs, f)\nApply(Cnt, [1, 2])", "[1, 1]" },
        { "dot map", "[1, 2].map(Cnt)", "Apply(f, xs) = xs.map(f)\nApply(Cnt, [1, 2])", "[1, 1]" },
        { "dot map on a written receiver", "[1, 2].map(Cnt)", "Apply(f) = [1, 2].map(f)\nApply(Cnt)", "[1, 1]" },
        { "map with list results", "map([(1, 2), 3], Only)", "Apply(f, xs) = map(xs, f)\nApply(Only, [(1, 2), 3])", "[[1, 2], [3]]" },
        { "filter", "filter([1, 2, 3], Big)", "Apply(f, xs) = filter(xs, f)\nApply(Big, [1, 2, 3])", "[2, 3]" },
        { "dot filter", "[1, 2, 3].filter(Big)", "Apply(f, xs) = xs.filter(f)\nApply(Big, [1, 2, 3])", "[2, 3]" },
        { "reduce", "reduce([1, 2, 3], SumAll, 0)", "Apply(f, xs) = reduce(xs, f, 0)\nApply(SumAll, [1, 2, 3])", "6" },
        { "dot reduce", "[1, 2, 3].reduce(SumAll, 0)", "Apply(f, xs) = xs.reduce(f, 0)\nApply(SumAll, [1, 2, 3])", "6" },
        { "repeat step", "repeat(CountStep, 3, 9)", "Apply(g) = repeat(g, 3, 9)\nApply(CountStep)", "2" },
        { "while step", "while(SumWhile, 0)", "Apply(g) = while(g, 0)\nApply(SumWhile)", "2" },
        { "nested captured parameter", "[1, 2].map(Cnt)", "Outer(xs) = { Inner(g) = xs.map(g)\nInner(Cnt) }\nOuter([1, 2])", "[1, 1]" },
        { "property alias", "G = Only\nmap([1], G)", "G = Only\nApply(f, xs) = map(xs, f)\nApply(G, [1])", "[[1]]" },
        { "implicit parameters", "[1, 2].map(Cnt)", "Apply = xs.map(f)\nApply([1, 2], Cnt)", "[1, 1]" },
        { "two forwarding levels", "map([1, 2], Cnt)", "Apply(f, xs) = map(xs, f)\nTwice(f, xs) = Apply(f, xs)\nTwice(Cnt, [1, 2])", "[1, 1]" },
        { "control: never value-bound", "map([1, 2], Z)", "Apply(f, xs) = map(xs, f)\nApply(Z, [1, 2])", "[10, 10]" },
        { "control: call position", "Cnt(1, 1)", "Apply(f, x) = f(x, x)\nApply(Cnt, 1)", "2" },
    };

    [Theory]
    [MemberData(nameof(DirectAndForwarded))]
    public void DirectAndForwardedConsumers_SelectTheSameCallable(
        string label, string direct, string forwarded, string expected)
    {
        Assert.Equal(expected, Display(Callables + direct));
        Assert.Equal(expected, Display(Callables + forwarded));

        // These pure fixtures compare results across execution strategies. The separate host
        // and random tests preserve forwarding's ordinary eager binding effects.
        var directPaths = AssertStrategiesAgree(Callables + direct, label + " (direct)");
        var forwardedPaths = AssertStrategiesAgree(Callables + forwarded, label + " (forwarded)");
        Assert.Equal(directPaths, forwardedPaths);
    }

    // ── The fused filter→count pipeline ─────────────────────────────────────

    [Theory]
    [InlineData("[1, 2, 3].filter(Big).count", "Apply(f, xs) = xs.filter(f).count\nApply(Big, [1, 2, 3])", "2")]
    [InlineData("count(filter(range(1, 5), Big))", "Apply(f) = count(filter(range(1, 5), f))\nApply(Big)", "4")]
    [InlineData("range(1, 5).filter(Big).count", "Apply(f) = range(1, 5).filter(f).count\nApply(Big)", "4")]
    [InlineData("Alias = Big\ncount(filter(range(1, 3), Alias))", "Alias = Big\nB(f) = count(filter(range(1, 3), f))\nA(g) = B(g)\nA(Alias)", "2")]
    public void FusedFilterCount_InvokesTheForwardedPredicate(string direct, string forwarded, string expected)
    {
        foreach (var source in new[] { Callables + direct, Callables + forwarded })
        {
            var ast = AsyncEvaluationHarness.Ast(source);
            var sequence = new SequencePipelineDiagnostics();
            var (fused, _) = Evaluator.RunCountedObserved(ast, sequenceDiagnostics: sequence);
            var (generic, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);

            Assert.Equal(1, sequence.GetSnapshot().FilterCountFusionHits);
            Assert.Equal($"ok raw={expected} n=1", AsyncEvaluationHarness.NeutralOf(fused));
            Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(fused));
        }
    }

    // ── VALUE slots read the bound value and never re-run the body ─────────

    [Theory]
    [InlineData("R(x, acc) = acc + x\nApply(i) = reduce([1, 2], R, i)\nApply(Seed)", "10")]
    [InlineData("Apply(xs) = count(xs)\nApply(Seed)", "1")]
    [InlineData("Apply(f) = if(true, f, 0)\nApply(Seed)", "7")]
    [InlineData("Step(s) = s + 1\nApply(i) = repeat(Step, 2, i)\nApply(Seed)", "9")]
    [InlineData("Apply(i) = take([1, 2, 3], i)\nApply(Seed)", "[1, 2, 3]")]
    [InlineData("Apply(i) = skip([1, 2, 3], i)\nApply(Seed)", "[]")]
    [InlineData("Apply(i) = range(i, i)\nApply(Seed)", "[7]")]
    [InlineData("R(x, acc) = acc + x\nreduce([1, 2], R, Seed)", "10")]
    public void ValueSlots_ReadTheBoundValue_TheBodyRunsOnceForTheBinding(string program, string expected)
    {
        // `Seed` is zero-argument-demand eligible, so binding `Apply(Seed)` runs its body
        // once for the parameter's value. A value slot reads that value: had it taken the
        // algorithm channel, the builtin would demand `Seed` again and tick twice.
        var ticks = new List<Decimal128>();
        var display = DisplayWith("Seed(*xs) = Tick(7)\n" + program, TickOperations(ticks));

        Assert.Equal(expected, display);
        Assert.Equal([(Decimal128)7], ticks);
    }

    [Fact]
    public void CallbackSlot_InvokesTheCallablePerItem_WithoutRedemandingItsValue()
    {
        var directTicks = new List<Decimal128>();
        Assert.Equal("[1, 1]", DisplayWith("Cnt(*xs) = Tick(xs.count)\nmap([5, 6], Cnt)", TickOperations(directTicks)));
        Assert.Equal([(Decimal128)1, 1], directTicks);

        // The binding demands the value once (Tick(0)); map then invokes the callable once per
        // element and never demands the value again.
        var forwardedTicks = new List<Decimal128>();
        Assert.Equal(
            "[1, 1]",
            DisplayWith("Cnt(*xs) = Tick(xs.count)\nApply(f, xs) = map(xs, f)\nApply(Cnt, [5, 6])", TickOperations(forwardedTicks)));
        Assert.Equal([(Decimal128)0, 1, 1], forwardedTicks);
    }

    // ── Parameters without an algorithm binding keep their behavior ─────────

    [Theory]
    [InlineData("map([1], 5)", "Apply(f, xs) = map(xs, f)\nApply(5, [1])")]
    [InlineData("A = 5\nmap([1], A)", "A = 5\nApply(f, xs) = map(xs, f)\nApply(A, [1])")]
    [InlineData("repeat(5, 1, 0)", "Apply(g) = repeat(g, 1, 0)\nApply(5)")]
    public void ZeroParameterCallbacks_AreRejectedAlike_DirectAndForwarded(string direct, string forwarded)
    {
        // A value-only parameter has no algorithm binding, so the invoking slot still receives
        // its value; a forwarded zero-parameter property is invoked like the direct one. Both
        // spellings reject the zero-parameter callback with the same structured error.
        var directR = Evaluator.Run(AsyncEvaluationHarness.Ast(direct));
        var forwardedR = Evaluator.Run(AsyncEvaluationHarness.Ast(forwarded));

        Assert.True(directR.IsError);
        Assert.True(forwardedR.IsError);
        Assert.Equal(Describe(Innermost(directR.Error)), Describe(Innermost(forwardedR.Error)));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void HostBuiltZeroArityFamily_ForwardedAsMapper_IsInvokedAsTheFamily(bool withItems)
    {
        // `Fam() = 7` has no surface spelling (a clause head needs a pattern), and a family's
        // branches share one arity, so a host-built zero-arity family accepts ONLY zero
        // supplied values: it is demand-eligible (value 7) and therefore bound on both
        // channels. As a mapper the FAMILY is invoked — rejected for one supplied item
        // exactly as the direct spelling rejects it, never as the zero-parameter wrapper of
        // its value — and an empty collection invokes nothing.
        var family = new Algorithm.Conditional(null, [],
            [new CondBranch(new Pattern.SequenceValue([]), new Algorithm.User(null, [], [], [], [new Expr.Num(7)]))]);
        var apply = new Algorithm.User(
            null,
            [new CaptureParameterPattern("f"), new CaptureParameterPattern("xs")],
            [],
            [],
            [new Expr.Call(new Expr.Resolve("map"), [new Expr.Param("xs"), new Expr.Param("f")])]);
        var items = new Expr.ListLiteral(withItems ? [new Expr.Num(1)] : []);
        Expr Program(Expr output) => new Expr.AlgorithmExpr(new Algorithm.User(
            null, [], [], [new Property("Fam", family), new Property("Apply", apply)], [output]));

        var direct = Evaluator.Run(Program(new Expr.Call(new Expr.Resolve("map"), [items, new Expr.Resolve("Fam")])));
        var forwarded = Evaluator.Run(Program(new Expr.Call(new Expr.Resolve("Apply"), [new Expr.Resolve("Fam"), items])));

        if (!withItems)
        {
            Assert.Equal("ok raw=L[]", AsyncEvaluationHarness.NeutralOf(direct));
            Assert.Equal("ok raw=L[]", AsyncEvaluationHarness.NeutralOf(forwarded));
            return;
        }

        Assert.True(direct.IsError);
        Assert.True(forwarded.IsError);
        Assert.Equal(Describe(Innermost(direct.Error)), Describe(Innermost(forwarded.Error)));
        Assert.Equal(
            KatLangError.FromEvalError(Innermost(direct.Error)).Message,
            KatLangError.FromEvalError(Innermost(forwarded.Error)).Message);
    }

    // ── Async: the twin threads the same channel through a genuine suspension ─

    [Fact]
    public async Task SuspendedForwardedCallback_InvokesTheCallable_ExactlyAsTheSyncPath()
    {
        const string source = "Cnt(*xs) = Tick(xs.count)\nApply(f, xs) = map(xs, f)\nApply(Cnt, [5, 6])";
        var syncTicks = new List<Decimal128>();
        var expected = DisplayWith(source, TickOperations(syncTicks));
        Assert.Equal("[1, 1]", expected);
        Assert.Equal([(Decimal128)0, 1, 1], syncTicks);

        var ticks = new List<Decimal128>();
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var operations = HostOperations.Create(HostOperation.CreateAsync("Tick", async (args, _) =>
        {
            ticks.Add(Assert.IsType<Result.Atom>(args[0]).Value);
            // Suspend inside the first CALLBACK invocation (the binding's value demand is
            // Tick(0)), so the rest of map runs after resumption.
            if (ticks.Count == 2)
            {
                reached.SetResult();
                await release.Task;
            }
            return args[0];
        }, "value"));
        var ast = new Expr.AlgorithmExpr(Parse(source, operations));
        var pending = Evaluator.RunCountedAsync(ast, new PassThroughAsyncZeroArgPropertyResultCache(), hostOperations: operations).AsTask();
        try
        {
            await reached.Task.WaitAsync(TimeSpan.FromSeconds(45));
            Assert.False(pending.IsCompleted);
            Assert.Equal([(Decimal128)0, 1], ticks);
        }
        finally
        {
            release.TrySetResult();
        }

        var result = await pending.WaitAsync(TimeSpan.FromSeconds(45));
        Assert.Equal("ok raw=L[1, 1] n=1", AsyncEvaluationHarness.NeutralOf(result));
        Assert.Equal(syncTicks, ticks);
    }

    [Theory]
    [InlineData("repeat(Step, 3, 0)", "3")]
    [InlineData("while(Step, 0)", "2")]
    public void ForwardedFixedStep_ActuallyExecutesAnOptimizedLoop(string call, string expected)
    {
        var step = call.StartsWith("while", StringComparison.Ordinal) ? "Step = s + 1, s + 1 < 3\n" : "Step = s + 1\n";
        foreach (var source in new[] { step + call, step + $"Apply(g) = {call.Replace("Step", "g")}\nApply(Step)" })
        {
            var ast = AsyncEvaluationHarness.Ast(source);
            var loops = new LoopOptimizationDiagnostics();
            var (optimized, _) = Evaluator.RunCountedObserved(ast, loopDiagnostics: loops);
            var (generic, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
            Assert.Equal(1, loops.GetSnapshot().OptimizedLoopHits);
            Assert.Equal($"ok raw={expected} n=1", AsyncEvaluationHarness.NeutralOf(optimized));
            Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(optimized));
        }
    }

    [Fact]
    public async Task CancellationInsideForwardedCallback_DoesNotReplayOrInvokeTheNextItem()
    {
        using var cancellation = new CancellationTokenSource();
        var ticks = new List<Decimal128>();
        var reached = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var operations = HostOperations.Create(HostOperation.CreateAsync("Tick", async (args, _) =>
        {
            ticks.Add(Assert.IsType<Result.Atom>(args[0]).Value);
            if (ticks.Count == 2)
            {
                reached.SetResult();
                await release.Task;
            }
            return args[0];
        }, "value"));
        var pending = KatLangEngine.RunAsync(
            "Cnt(*xs) = Tick(xs.count)\nB(g) = map([7, 8], g)\nA(f) = B(f)\nA(Cnt)",
            new RunOptions { HostOperations = operations, EvaluationCancellationToken = cancellation.Token });
        try
        {
            await reached.Task.WaitAsync(TimeSpan.FromSeconds(45));
            Assert.False(pending.IsCompleted);
            Assert.Equal([(Decimal128)0, 1], ticks);
            cancellation.Cancel();
        }
        finally
        {
            release.TrySetResult();
        }
        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(
            () => pending.WaitAsync(TimeSpan.FromSeconds(45)));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal([(Decimal128)0, 1], ticks);
    }

    [Fact]
    public void ForwardingSelection_ConsumesNoExtraRandomDraw_AndPreservesTheBoundValue()
    {
        const string definition = "R(*xs) = Math.Random(0, 1)\n";
        const string forwarded = "B(g) = [map([5, 6], g), g, g, Math.Random(0, 1)]\nA(f) = B(f)\nA(R)";
        // The control explicitly performs the ordinary eager binding once, followed by
        // two invocations. The final independent draw detects any extra classification draw.
        const string control = "Control(saved) = [[R(5), R(6)], saved, saved, Math.Random(0, 1)]\nControl(R)";
        var options = new RunOptions { RandomSeed = 20260923 };
        var actual = Assert.IsType<RunResult.Success>(KatLangEngine.Run(definition + forwarded, options));
        var baseline = Assert.IsType<RunResult.Success>(KatLangEngine.Run(definition + control, options));
        Assert.True(Result.ValueComparer.Equals(baseline.Value, actual.Value),
            $"Expected {SemanticExplorerHarness.Neutral(baseline.Value)}, got {SemanticExplorerHarness.Neutral(actual.Value)}");
    }

    // ── Helpers ─────────────────────────────────────────────────────────────

    /// <summary>
    /// Generic, optimized, and async-twin execution agree (value and consumed steps), and the
    /// returned pair records which optimizers engaged, so a caller can pin that forwarding
    /// does not change the execution strategy.
    /// </summary>
    private static (long LoopHits, long FusionHits) AssertStrategiesAgree(string source, string label)
    {
        var ast = AsyncEvaluationHarness.Ast(source);
        var (generic, genericBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var loops = new LoopOptimizationDiagnostics();
        var sequence = new SequencePipelineDiagnostics();
        var (optimized, _) = Evaluator.RunCountedObserved(
            ast, enableOptimizations: true, loopDiagnostics: loops, sequenceDiagnostics: sequence);
        var expected = AsyncEvaluationHarness.NeutralOf(generic);
        Assert.True(generic.IsOk, $"{label}: {expected}");
        Assert.Equal(expected, AsyncEvaluationHarness.NeutralOf(optimized));

        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var (asyncResult, asyncBudget) = AsyncEvaluationHarness
            .Complete(Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: cache))
            .GetAwaiter()
            .GetResult();
        Assert.Equal(expected, AsyncEvaluationHarness.NeutralOf(asyncResult));
        Assert.Equal(genericBudget.ConsumedSteps, asyncBudget.ConsumedSteps);
        Assert.Equal(0, cache.SyncAccesses);

        return (loops.GetSnapshot().OptimizedLoopHits, sequence.GetSnapshot().FilterCountFusionHits);
    }

    private static string Display(string source)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString().ReplaceLineEndings("\n");

    private static string DisplayWith(string source, HostOperations operations)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, new RunOptions { HostOperations = operations }))
            .ToDisplayString()
            .ReplaceLineEndings("\n");

    private static Algorithm.User Parse(string source, HostOperations operations)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(static diagnostic => diagnostic.Message)));
        return parsed.Root;
    }

    private static HostOperations TickOperations(List<Decimal128> ticks)
        => HostOperations.Create(HostOperation.Create("Tick", (args, _) =>
        {
            ticks.Add(Assert.IsType<Result.Atom>(args[0]).Value);
            return args[0];
        }, "value"));

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    private static string Describe(EvalError error) => error switch
    {
        EvalError.ArityMismatch arity => $"ArityMismatch({arity.Expected}, {arity.Actual})",
        EvalError.NoMatchingBranch noMatch => $"NoMatchingBranch({noMatch.AlgorithmName})",
        _ => $"{error.GetType().Name}[{error.Code}]",
    };
}
