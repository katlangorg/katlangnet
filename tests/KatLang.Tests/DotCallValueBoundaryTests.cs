using KatLang.Tests.AsyncEvaluation;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

/// <summary>
/// DOT-CALL PASSES A VALUE. SPREAD OPENS A VALUE.
///
/// <para>The metamorphic invariant family of extension-call fallback: for every
/// receiver <c>R</c>, callee <c>F</c>, and argument list, <c>R.F(args)</c> assembles
/// exactly the arguments of <c>F(R, args)</c> and <c>R*.F(args)</c> exactly those of
/// <c>F(R*, args)</c> — same value, same emitted count, same error kind, and the same
/// outcome under the generic, the optimized, and the async strategies. The receiver's
/// origin (literal, group, brace block, property, call result, conditional, selection)
/// never changes the argument it supplies, a collecting callee binds the receiver by the
/// collector supply-boundary law exactly as it binds the written argument (a lone
/// sequence-valued receiver opens one level, a list stays exact — see
/// <see cref="CollectorSupplyBoundaryTests"/>), and the receiver is evaluated exactly
/// once, first. Together with the selection rule: selection chooses a value, dot-call
/// passes a value, spread opens a value.</para>
///
/// <para>Lean: <c>callLexicalWithReceiverCounted</c> dispatches
/// <c>prepareLexicalDotCallArgs</c> through the one <c>evalResolvedCallCounted</c>; laws
/// <c>dot_receiver_is_ordinary_leading_argument</c> and
/// <c>spread_dot_receiver_is_ordinary_spread_argument</c> in
/// <c>lean/KatLangArityLaws.lean</c>; CoreTests <c>DotReceiverSegments</c>. The expected
/// table itself is pinned in <see cref="DotCallCollectingReceiverTests"/>.</para>
/// </summary>
public class DotCallValueBoundaryTests
{
    /// <summary>
    /// Shared definitions every program starts with: the receivers that need a
    /// name and every callee shape under test.
    /// </summary>
    private const string Definitions =
        "P = (1, 2)\n" +
        "E = ()\n" +
        "L = [1, 2]\n" +
        "Fz(x) = ()\n" +
        "A = ((1, 2), 3)\n" +
        "B = ((), 1)\n" +
        "C = (3, [1, 2])\n" +
        "Fixed(x) = [x]\n" +
        "Two(x, y) = [x, y]\n" +
        "Id(x) = x\n" +
        "Keep(x) = true\n" +
        "Reduce(x, acc) = acc\n" +
        "Coll(*xs) = xs\n" +
        "PrefixColl(x, *rest) = ([x], rest)\n" +
        "CollSuffix(*rest, z) = (rest, [z])\n" +
        "Pat((x, *y)) = ([x], y)\n" +
        "Fam((a, b)) = a + b\n" +
        "Fam(x) = 0\n";

    /// <summary>
    /// Representative receivers: every value kind and every origin. Each entry
    /// is the receiver EXPRESSION exactly as it is written before <c>.F</c>.
    /// </summary>
    public static TheoryData<string> Receivers =>
    [
        "()",
        "1",
        "'s'",
        "true",
        "(1, 2)",
        "((1, 2))",
        "[]",
        "[1, 2]",
        "[()]",
        "[[1, 2], [3]]",
        "[[1, 2]]",
        "(P*)",
        "((1, 2), 3)",
        "{1, 2}",
        "P",
        "E",
        "L",
        "Fz(1)",
        "if(true, (), 1)",
        "if(false, (), P)",
        "A:0",
        "B:0",
        "C:1",
        "first(A)",
        "last(C)",
        "first(B)",
        "A:0:1",
        "map(A, Id):0",
        "Id(P)",
    ];

    /// <summary>Every callee shape, with and without extra written arguments.</summary>
    private static readonly (string Callee, string ExtraArgs)[] Callees =
    [
        ("Fixed", ""),
        ("Two", ""),
        ("Two", "(9)"),
        ("Coll", ""),
        ("Coll", "(9)"),
        ("PrefixColl", ""),
        ("PrefixColl", "(9, 8)"),
        ("CollSuffix", ""),
        ("CollSuffix", "(9)"),
        ("Pat", ""),
        ("Fam", ""),
        ("count", ""),
        ("first", ""),
        ("last", ""),
        ("sum", ""),
        ("min", ""),
        ("max", ""),
        ("avg", ""),
        ("distinct", ""),
        ("order", ""),
        ("orderDesc", ""),
        ("map", "(Id)"),
        ("filter", "(Keep)"),
        ("reduce", "(Reduce, ())"),
        ("take", "(1)"),
        ("skip", "(1)"),
        ("contains", "(1)"),
    ];

    private static string Neutral(string source)
        => SemanticExplorerHarness.Observe("dot-call", source).Neutral;

    private static string DottedSource(string receiver, string callee, string extraArgs, bool spread)
        => Definitions + receiver + (spread ? "*" : "") + "." + callee + extraArgs;

    private static string DirectSource(string receiver, string callee, string extraArgs, bool spread)
    {
        var rest = extraArgs.Length == 0 ? "" : ", " + extraArgs[1..^1];
        return Definitions + callee + "(" + receiver + (spread ? "*" : "") + rest + ")";
    }

    // ── R.F(args) ≡ F(R, args) and R*.F(args) ≡ F(R*, args) ─────────────────

    [Theory]
    [MemberData(nameof(Receivers))]
    public void DottedCall_AssemblesTheArgumentsOfTheDirectCall(string receiver)
    {
        foreach (var (callee, extraArgs) in Callees)
        {
            foreach (var spread in new[] { false, true })
            {
                var dotted = DottedSource(receiver, callee, extraArgs, spread);
                var direct = DirectSource(receiver, callee, extraArgs, spread);
                Assert.True(
                    Neutral(direct) == Neutral(dotted),
                    $"{(spread ? "R*.F" : "R.F")} ≠ {(spread ? "F(R*)" : "F(R)")} for receiver `{receiver}`, callee `{callee}{extraArgs}`:"
                    + $"{Environment.NewLine}  dotted: {Neutral(dotted)}{Environment.NewLine}  direct: {Neutral(direct)}");
            }
        }
    }

    [Theory]
    [MemberData(nameof(Receivers))]
    public void DottedCall_AgreesAcrossGenericOptimizedAndAsyncExecution(string receiver)
    {
        foreach (var (callee, extraArgs) in Callees)
        {
            foreach (var spread in new[] { false, true })
                AssertStrategiesAgree(DottedSource(receiver, callee, extraArgs, spread));
        }
    }

    // ── The receiver is one written slot bound by the collector law; spread opens exactly one boundary ──

    [Theory]
    [MemberData(nameof(Receivers))]
    public void CollectingCallee_BindsTheReceiverByTheCollectorLaw_AndSpreadOpensOneBoundary(string receiver)
    {
        // Unspread: `R.Coll` is `Coll(R)` — one written slot at a lone collector, so the
        // collector supply-boundary law decides: a sequence-valued receiver (`()` and
        // `P` included) opens one level to its items, every other value is the one
        // collected item. Beside a written argument the receiver is collected exactly.
        var value = KatLangEngine.Run(Definitions + receiver);
        var receiverValue = Assert.IsType<RunResult.Success>(value).Value;
        var expectedCollected = receiverValue is Result.SequenceValue sequence
            ? sequence.Items
            : [receiverValue];
        var collected = Assert.IsType<RunResult.Success>(KatLangEngine.Run(DottedSource(receiver, "Coll", "", spread: false)));
        var collectedList = Assert.IsType<Result.ListValue>(collected.Value);
        Assert.Equal(expectedCollected.Count, collectedList.Items.Count);
        for (var i = 0; i < expectedCollected.Count; i++)
            Assert.True(Result.ValueComparer.Equals(expectedCollected[i], collectedList.Items[i]),
                $"`{receiver}.Coll` collected {collected.ToDisplayString()} instead of the collector-law binding");

        var beside = Assert.IsType<RunResult.Success>(KatLangEngine.Run(DottedSource(receiver, "Coll", "(9)", spread: false)));
        var besideList = Assert.IsType<Result.ListValue>(beside.Value);
        Assert.Equal(2, besideList.Items.Count);
        Assert.True(Result.ValueComparer.Equals(receiverValue, besideList.Items[0]),
            $"`{receiver}.Coll(9)` collected {beside.ToDisplayString()} instead of the exact receiver value beside 9");

        // Spread: exactly one boundary — the receiver's SpreadItems view, collected
        // exactly as final items (a lone spread-produced sequence value stays one item).
        var spreadCollected = Assert.IsType<RunResult.Success>(KatLangEngine.Run(DottedSource(receiver, "Coll", "", spread: true)));
        var spreadList = Assert.IsType<Result.ListValue>(spreadCollected.Value);
        var expectedItems = receiverValue.SpreadItems();
        Assert.Equal(expectedItems.Count, spreadList.Items.Count);
        for (var i = 0; i < expectedItems.Count; i++)
            Assert.True(Result.ValueComparer.Equals(expectedItems[i], spreadList.Items[i]));
    }

    // ── Receiver evaluation: once, first, through the ordinary argument path ─

    [Fact]
    public void Receiver_IsEvaluatedOnce_AndBeforeTheWrittenArguments()
    {
        // A host operation that counts its calls and returns the call number:
        // `Tick()` (the explicit call bypasses the property cache) in receiver
        // position is evaluated exactly once and before the written argument,
        // in both spellings.
        foreach (var (source, expectedDisplay) in new[]
        {
            ("Pair(a, b) = (a, b)\nTick().Pair(Tick())", "(1, 2)"),
            ("Pair(a, b) = (a, b)\nPair(Tick(), Tick())", "(1, 2)"),
            ("Coll(*xs) = xs\nTick().Coll(Tick(), Tick())", "[1, 2, 3]"),
            ("Coll(*xs) = xs\nColl(Tick(), Tick(), Tick())", "[1, 2, 3]"),
            ("Tick().count", "1"),
            ("count(Tick())", "1"),
        })
        {
            var counter = 0;
            var options = new RunOptions
            {
                HostOperations = HostOperations.Create(
                    HostOperation.Create("Tick", (_, _) => new Result.Atom(++counter))),
            };
            var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, options));
            Assert.Equal(expectedDisplay, run.ToDisplayString());
            Assert.Equal(source.Split("Tick()").Length - 1, counter);
        }
    }

    [Fact]
    public void BuiltinReceiver_IsDemandedLikeTheBuiltinsWrittenArgument()
    {
        // A collection builtin's `collection` slot demands a NAMED receiver through
        // the zero-argument value-demand law exactly as `count(A)` does — never
        // through the property cache — so a random-backed property observes the
        // same fresh draw in both spellings, while a parameterized receiver is the
        // same collection-argument demand rejection.
        var seeded = new RunOptions { RandomSeed = 7 };
        var dotted = Assert.IsType<RunResult.Success>(KatLangEngine.Run("R = random(1, 1000000)\nR.sum", seeded));
        var direct = Assert.IsType<RunResult.Success>(KatLangEngine.Run("R = random(1, 1000000)\nsum(R)", seeded));
        Assert.Equal(direct.ToDisplayString(), dotted.ToDisplayString());

        // The captured spelling reads the cached property value in both forms.
        var dottedCaptured = Assert.IsType<RunResult.Success>(KatLangEngine.Run("R = random(1, 1000000)\n(R).sum == R", seeded));
        var directCaptured = Assert.IsType<RunResult.Success>(KatLangEngine.Run("R = random(1, 1000000)\nsum((R)) == R", seeded));
        Assert.Equal("true", dottedCaptured.ToDisplayString());
        Assert.Equal("true", directCaptured.ToDisplayString());

        // A user call reads its argument through the value environment in both
        // spellings, so the cached draw is shared.
        var dottedUser = Assert.IsType<RunResult.Success>(KatLangEngine.Run("R = random(1, 1000000)\nG(x) = x\nR.G == R", seeded));
        var directUser = Assert.IsType<RunResult.Success>(KatLangEngine.Run("R = random(1, 1000000)\nG(x) = x\nG(R) == R", seeded));
        Assert.Equal("true", dottedUser.ToDisplayString());
        Assert.Equal("true", directUser.ToDisplayString());

        // Populate the cache BEFORE the builtin calls, then observe multiple draws
        // and a following sentinel. A first-read-only comparison cannot catch an
        // accidental receiver-only cache hit or a changed random-stream position.
        foreach (var seed in new[] { 7L, 0L, long.MinValue })
        {
            const string prefix = "R = random(1, 1000000)\nR\n";
            const string suffix = "\nR()\nR\nrandom(1, 1000000)";
            var options = new RunOptions { RandomSeed = seed };
            var cachedDot = Assert.IsType<RunResult.Success>(KatLangEngine.Run(prefix + "R.sum\nR.sum" + suffix, options));
            var cachedCall = Assert.IsType<RunResult.Success>(KatLangEngine.Run(prefix + "sum(R)\nsum(R)" + suffix, options));
            Assert.Equal(cachedCall.ToDisplayString(), cachedDot.ToDisplayString());
        }

        foreach (var (dottedSource, directSource) in new[]
        {
            ("Inc(x) = x + 1\nInc.count", "Inc(x) = x + 1\ncount(Inc)"),
            ("Inc(x) = x + 1\nInc.first", "Inc(x) = x + 1\nfirst(Inc)"),
            ("Inc(x) = x + 1\nColl(*xs) = xs\nInc.Coll", "Inc(x) = x + 1\nColl(*xs) = xs\nColl(Inc)"),
            ("Fam(0) = 1\nFam(x) = 2\nFam.count", "Fam(0) = 1\nFam(x) = 2\ncount(Fam)"),
            ("NoOut = { X = 1 }\nNoOut.count", "NoOut = { X = 1 }\ncount(NoOut)"),
        })
        {
            Assert.Equal(Neutral(directSource), Neutral(dottedSource));
            var dottedError = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(dottedSource));
            var directError = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(directSource));
            Assert.Equal(Assert.Single(directError.Errors).Code, Assert.Single(dottedError.Errors).Code);
        }
    }

    // ── Structural members and intrinsics are not extension fallback ────────

    [Fact]
    public void StructuralMember_WinsBeforeExtensionFallback()
    {
        const string source = """
            X(o) = 99
            Obj = {
                public X = 5
                public Y(v) = v * 2
            }
            Obj.X, X(Obj), Obj.Y(3)
            """;
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal($"5{Environment.NewLine}99{Environment.NewLine}6", run.ToDisplayString());
    }

    [Fact]
    public void StringIntrinsic_StaysAnIntrinsic()
    {
        // `.string` is the spelling-recognized intrinsic (category 2 of dot
        // resolution), not extension fallback: there is no lexical `string`
        // callable to rewrite it to, and it stays a value on both receiver forms.
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run("N = 42\n42.string, (42).string, N.string"));
        Assert.Equal($"42{Environment.NewLine}42{Environment.NewLine}42", run.ToDisplayString());
        Assert.All(run.OutputRows, row => Assert.IsType<Result.Str>(row));
    }

    // ── Error kinds agree where the same computation is performed ───────────

    [Fact]
    public void ErrorKinds_AgreeBetweenTheSpellings()
    {
        foreach (var (dotted, direct) in new[]
        {
            ("Two(a, b) = a + b\n(1, 2).Two", "Two(a, b) = a + b\nTwo((1, 2))"),
            ("Two(a, b) = a + b\n(1, 2).Two(3, 4)", "Two(a, b) = a + b\nTwo((1, 2), 3, 4)"),
            ("Inc(x) = x + 1\n(1, 2).Inc", "Inc(x) = x + 1\nInc((1, 2))"),
            ("F(x, acc) = x + acc\nX = (1, 2, 3)\nX.reduce(F)", "F(x, acc) = x + acc\nX = (1, 2, 3)\nreduce(X, F)"),
            ("NoOut = { X = 1 }\nColl(*xs) = xs\nNoOut.Coll", "NoOut = { X = 1 }\nColl(*xs) = xs\nColl(NoOut)"),
            ("M = ((1, 2), 3)\n[1, 2].min", "M = ((1, 2), 3)\nmin([1, 2])"),
            ("(1, 'a').sum", "sum((1, 'a'))"),
            ("Pat((x, *y)) = y\n().Pat", "Pat((x, *y)) = y\nPat(())"),
            ("Pat((x, *y)) = y\n()*.Pat", "Pat((x, *y)) = y\nPat(()*)"),
            ("Fam((a, b)) = a\nFam(0) = 0\n[1, 2].Fam", "Fam((a, b)) = a\nFam(0) = 0\nFam([1, 2])"),
            ("(1, 2)*.count", "count((1, 2)*)"),
            ("F(x) = x\n(1, 2, 3)*.F", "F(x) = x\nF((1, 2, 3)*)"),
        })
        {
            Assert.Equal(Neutral(direct), Neutral(dotted));
        }
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(3)]
    public async Task ArgumentEffects_AndFailures_AgreeAfterRealSuspension(int failingSlot)
    {
        // Ordinary call assembly may retain a value error for the algorithm channel.
        // Compare its actual trace, including the fatal spread path that stops assembly,
        // rather than assuming that every value error must stop every callable shape.
        foreach (var spread in new[] { false, true })
        foreach (var declaration in new[]
        {
            "F(a, b, c) = [a, b, c]",
            "F(*xs) = xs",
            "F((a), b, c) = [a, b, c]",
            "F(0, b, c) = 0\nF(a, b, c) = [a, b, c]",
        })
        {
            string Slot(int n) => failingSlot == n ? $"(Probe({n}) / 0)" : $"Probe({n})";
            var receiver = Slot(1) + (spread ? "*" : "");
            var direct = $"{declaration}\nF({receiver}, {Slot(2)}, {Slot(3)})";
            var dotted = $"{declaration}\n{receiver}.F({Slot(2)}, {Slot(3)})";
            var baseline = await ObserveEffects(direct, suspend: false);
            foreach (var (source, suspend) in new[] { (dotted, false), (direct, true), (dotted, true) })
            {
                var actual = await ObserveEffects(source, suspend);
                Assert.Equal(baseline.Outcome, actual.Outcome);
                Assert.Equal(baseline.Trace, actual.Trace);
            }

            Assert.Equal(baseline.Trace.Distinct(), baseline.Trace);
            Assert.Equal(baseline.Trace.Order(), baseline.Trace);
            if (failingSlot == 0)
                Assert.Equal(new[] { 1, 2, 3 }, baseline.Trace);
            if (spread && failingSlot == 1)
                Assert.Equal(new[] { 1 }, baseline.Trace);
        }

        async Task<(string Outcome, int[] Trace)> ObserveEffects(string source, bool suspend)
        {
            var trace = new List<int>();
            var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
            var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
            Result Record(IReadOnlyList<Result> args)
            {
                var value = Assert.IsType<Result.Atom>(Assert.Single(args));
                trace.Add((int)value.Value);
                return value;
            }
            var operation = suspend
                ? HostOperation.CreateAsync("Probe", async (args, _) =>
                {
                    var value = Record(args);
                    entered.TrySetResult();
                    await release.Task;
                    return value;
                }, "n")
                : HostOperation.Create("Probe", (args, _) => Record(args), "n");
            var operations = HostOperations.Create(operation);
            var parsed = await SourceProvenance.ParseValidAsync(source, new RunOptions { HostOperations = operations });
            var ast = new Expr.AlgorithmExpr(parsed.Root);
            EvalResult<Evaluator.CountedResult> result;
            if (suspend)
            {
                var pending = Evaluator.RunCountedObservedAsync(ast, hostOperations: operations).AsTask();
                await entered.Task.WaitAsync(TimeSpan.FromSeconds(10));
                Assert.False(pending.IsCompleted);
                release.SetResult();
                result = (await pending.WaitAsync(TimeSpan.FromSeconds(10))).Result;
            }
            else
                result = Evaluator.RunCountedObserved(ast, enableOptimizations: false, hostOperations: operations).Result;

            if (failingSlot != 0)
            {
                Assert.True(result.IsError);
                var error = result.Error;
                while (error is EvalError.WithContext(_, var inner)) error = inner;
                Assert.IsType<EvalError.DivByZero>(error);
            }
            else
            {
                Assert.True(result.IsOk);
                Assert.Equal(1, result.Value.EmittedCount);
                Assert.Equal(new Result[] { new Result.Atom(1), new Result.Atom(2), new Result.Atom(3) },
                    Assert.IsType<Result.ListValue>(result.Value.Value).Items);
            }
            return (AsyncEvaluationHarness.NeutralOf(result), trace.ToArray());
        }
    }

    [Theory]
    [InlineData("A = ((1, 2), (), [3, 4])", "A", "3")]
    [InlineData("A = []", "A", "0")]
    [InlineData("", "range(1, 4)", "4")]
    public void FilterCount_ActuallyFuses_AndKeepsCallbackValues(string definitions, string receiver, string expected)
    {
        // The predicate observes the callback item through a collecting dotted receiver
        // beside a written argument, so the item is collected EXACTLY and compared with
        // the written list `[x, 9]` — the fused path must see the same item value.
        var prefix = definitions + "\nKeep(x) = x.Coll(9) == [x, 9]\nColl(*xs) = xs\n";
        var dotted = prefix + receiver + ".filter(Keep).count";
        var direct = prefix + "count(filter(" + receiver + ", Keep))";
        var sequence = new SequencePipelineDiagnostics();
        var (fused, _) = Evaluator.RunCountedObserved(AsyncEvaluationHarness.Ast(dotted), sequenceDiagnostics: sequence);
        var (generic, _) = Evaluator.RunCountedObserved(AsyncEvaluationHarness.Ast(direct), enableOptimizations: false);
        Assert.True(fused.IsOk, fused.IsError ? fused.Error.ToString() : "");
        Assert.Equal(expected, Assert.IsType<Result.Atom>(fused.Value.Value).Value.ToString());
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(fused));
        Assert.Equal(1, sequence.GetSnapshot().FilterCountFusionHits);
    }

    [Fact]
    public async Task PlannedLoop_AndHigherOrderFallback_ApplyTheCollectorLawLikeDirectCalls()
    {
        // `Apply(r, f) = r.f` is `f(r)`: the receiver parameter is ONE written slot of
        // the callback call, so a sequence-valued receiver opens one level at the lone
        // collector (`()` to zero items, `(1, 2)` to two) while a list stays one item —
        // identically inside the planned loop, the generic path, and the async twin.
        const string definitions = "Coll(*xs) = xs\nApply(r, f) = r.f\n";
        foreach (var (receiver, expected) in new[] { ("()", "0"), ("(1, 2)", "6"), ("[]", "3"), ("[1, 2]", "3") })
        {
            var prefix = definitions + $"Step(n) = n + count(Apply({receiver}, Coll))\n";
            var source = prefix + "repeat(Step, 3, 0)";
            var loop = new LoopOptimizationDiagnostics();
            var ast = AsyncEvaluationHarness.Ast(source);
            var (planned, _) = Evaluator.RunCountedObserved(ast, loopDiagnostics: loop);
            var (generic, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
            var cache = new SuspendingAsyncZeroArgPropertyResultCache();
            var (asyncResult, _) = await AsyncEvaluationHarness.Complete(
                Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: cache));
            Assert.True(planned.IsOk);
            Assert.Equal(expected, Assert.IsType<Result.Atom>(planned.Value.Value).Value.ToString());
            Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(planned));
            Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(asyncResult));
            Assert.Equal(1, loop.GetSnapshot().OptimizedLoopHits);
            Assert.True(loop.GetSnapshot().GenericExpressionEvaluationsInsideOptimizedLoops > 0);
            Assert.Equal(0, cache.SyncAccesses);
        }
    }

    [Theory]
    [InlineData("Probe(1)", "Probe(2)", false)]
    [InlineData("(Probe(1) / 0)", "Probe(2)", true)]
    [InlineData("range(Probe(1) / 0, 4)", "Probe(2)", true)]
    [InlineData("range(Probe(1), 4)", "(Probe(2) / 0)", false)]
    public async Task FusedPreparation_PreservesEffectsAndFirstError(string receiver, string predicate, bool sourceDivisionError)
    {
        string? baseline = null;
        foreach (var dotted in new[] { false, true })
        foreach (var strategy in new[] { "generic", "optimized", "async" })
        {
            var trace = new List<int>();
            var operations = HostOperations.Create(HostOperation.Create("Probe", (args, _) =>
            {
                var value = Assert.IsType<Result.Atom>(Assert.Single(args));
                trace.Add((int)value.Value);
                return value;
            }, "n"));
            var source = dotted
                ? $"{receiver}.filter({predicate}).count"
                : $"count(filter({receiver}, {predicate}))";
            var parsed = await SourceProvenance.ParseValidAsync(source, new RunOptions { HostOperations = operations });
            var ast = new Expr.AlgorithmExpr(parsed.Root);
            var result = strategy == "async"
                ? (await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(ast,
                    zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache(), hostOperations: operations))).Result
                : Evaluator.RunCountedObserved(ast, enableOptimizations: strategy == "optimized",
                    hostOperations: operations).Result;
            var outcome = AsyncEvaluationHarness.NeutralOf(result);
            baseline ??= outcome;
            Assert.Equal(baseline, outcome);
            Assert.Equal(new[] { 1, 2 }, trace);
            Assert.True(result.IsError);
            // With a valid source, the zero-parameter predicate fails callback arity;
            // its eager value-attempt error does not replace its algorithm identity.
            Assert.Equal(sourceDivisionError ? KatLangErrorCode.DivisionByZero : KatLangErrorCode.ArityMismatch, result.Error.Code);
        }
    }

    // ── Helpers ─────────────────────────────────────────────────────────────

    private static void AssertStrategiesAgree(string source)
    {
        var ast = new Expr.AlgorithmExpr(ParseValidRoot(source));
        var (generic, genericBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var (planned, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: true);
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(planned));

        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var (asyncResult, asyncBudget) = AsyncEvaluationHarness
            .Complete(Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: cache))
            .GetAwaiter()
            .GetResult();
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(asyncResult));
        Assert.Equal(genericBudget.ConsumedSteps, asyncBudget.ConsumedSteps);
        Assert.Equal(genericBudget.PeakDepth, asyncBudget.PeakDepth);
        Assert.Equal(0, cache.SyncAccesses);
    }
}
