using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

/// <summary>
/// PARENTHESES GROUP SYNTAX; THEY DO NOT INTRODUCE A SEMANTIC BOUNDARY.
///
/// <para>The metamorphic invariant family of redundant expression parentheses: for every
/// ordinary expression <c>E</c> and every consumer <c>T</c>, <c>T(E)</c>, <c>T((E))</c>, and
/// <c>T(((E)))</c> agree on value, emitted count, and error kind — through root output,
/// ordinary and collecting call arguments, explicit spread, dot-call receivers, fluent
/// spread receivers, selection, list elements, stored properties, patterned and clause-family
/// binding, callbacks, loop state, operators, builtin value slots, and the <c>.string</c>
/// intrinsic — and under the generic, the optimized, and the genuinely suspending async
/// strategies. Grouping never changes how often an argument is evaluated, its position in the
/// evaluation order, whether a property read goes through the zero-argument cache or is
/// demanded directly, or which receiver a dot edge navigates. The parser erases every group of
/// exactly one non-spread slot (<c>Parser.IsRedundantGrouping</c>), so no later layer can
/// observe it; the only surviving captures are the groups whose parentheses do something
/// (several slots, or a lone spread).</para>
///
/// <para>Together with the settled rules: selection chooses a value, dot-call passes a value,
/// spread opens a value — and parentheses group syntax. The canonical expectations live in
/// the <c>parentheses-group-syntax</c> language-spec case; this suite is the observer matrix.</para>
/// </summary>
public class RedundantParenthesesTransparencyTests
{
    /// <summary>Shared definitions: named values of every kind and every callee shape.</summary>
    private const string Definitions =
        "P = (1, 2)\n" +
        "E = ()\n" +
        "L = [1, 2]\n" +
        "N = ((1, 2), 3)\n" +
        "M = [[1, 2], []]\n" +
        "B = ((), 1)\n" +
        "Fz(x) = ()\n" +
        "Fp(x) = (1, 2)\n" +
        "Id(x) = x\n" +
        "Two(x, y) = [x, y]\n" +
        "Coll(*xs) = xs\n" +
        "Pat((x, *y)) = ([x], y)\n" +
        "Sing((x)) = x\n" +
        "Fam((a, b)) = a + b\n" +
        "Fam(x) = 0\n" +
        "Keep(x) = true\n" +
        "Reduce(x, acc) = acc\n" +
        "Step(s) = s\n" +
        "Obj = { public X = 7 }\n";

    /// <summary>
    /// Representative expressions <c>E</c>: literals, the empty sequence, sequence and list
    /// values (nested included), names, calls returning <c>()</c> and <c>(1, 2)</c>, structural
    /// members, selections of every kind (an empty sequence and a list included), blocks,
    /// conditionals, and a captured spread.
    /// </summary>
    public static TheoryData<string> Expressions =>
    [
        "1",
        "'s'",
        "true",
        "()",
        "(1, 2)",
        "[]",
        "[1, 2]",
        "P",
        "E",
        "L",
        "N",
        "M",
        "B",
        "Id(1)",
        "Fz(1)",
        "Fp(1)",
        "Obj.X",
        "P:0",
        "N:0",
        "M:1",
        "B:0",
        "first(N)",
        "last(N)",
        "first(B)",
        "if(true, P, L)",
        "if(false, P, L)",
        "{1, 2}",
        "(P*)",
    ];

    /// <summary>
    /// The observers: every context that could reveal a hidden boundary. <c>$</c> stands for
    /// the expression under test.
    /// </summary>
    private static readonly string[] Observers =
    [
        "$",
        "$, 9",
        "Id($)",
        "Two($, 9)",
        "Coll($)",
        "Coll($, 9)",
        "Coll(9, $)",
        "Coll($*)",
        "Coll(9, $*)",
        "$.Id",
        "$.Coll",
        "$.Coll(9)",
        "$.count",
        "$.first",
        "$.map(Id)",
        "$*.Coll",
        "$*.count",
        "$:0",
        "[$]",
        "[$, 9]",
        "[$*]",
        "X = $\nX",
        "X = $\nX.Coll",
        "X = $\nX:0",
        "Pat($)",
        "Sing($)",
        "Fam($)",
        "map([$], Id)",
        "filter([$], Keep)",
        "reduce([1], Reduce, $)",
        "repeat(Step, 1, $)",
        "$ == $",
        "count($)",
        "first($)",
        "if(true, $, 0)",
        "$ + 1",
        "$.string",
        "{ $ }",
        "Q = { public V = $ }\nQ.V",
        "x, *y = $\ny",
    ];

    private static string Grouped(string expression, int depth)
        => new string('(', depth) + expression + new string(')', depth);

    private static string Program(string observer, string expression, int depth)
        => Definitions + observer.Replace("$", Grouped(expression, depth), StringComparison.Ordinal);

    private static string Neutral(string source)
        => SemanticExplorerHarness.Observe("parentheses", source).Neutral;

    // ── E ≡ (E) ≡ ((E)) through every observer ──────────────────────────────

    [Theory]
    [MemberData(nameof(Expressions))]
    public void RedundantParentheses_AreTransparentThroughEveryObserver(string expression)
    {
        foreach (var observer in Observers)
        {
            var bare = Neutral(Program(observer, expression, 0));
            Assert.NotEqual("parseError", bare);
            foreach (var depth in new[] { 1, 2, 3 })
            {
                var grouped = Neutral(Program(observer, expression, depth));
                Assert.True(
                    bare == grouped,
                    $"`{observer.Replace("$", Grouped(expression, depth), StringComparison.Ordinal)}` ≠ `{observer.Replace("$", expression, StringComparison.Ordinal)}`:"
                    + $"{Environment.NewLine}  bare:    {bare}{Environment.NewLine}  grouped: {grouped}");
            }
        }
    }

    [Theory]
    [MemberData(nameof(Expressions))]
    public void RedundantParentheses_AgreeAcrossGenericOptimizedAndAsyncExecution(string expression)
    {
        foreach (var observer in Observers)
        foreach (var depth in new[] { 1, 2 })
            AssertStrategiesAgree(Program(observer, expression, depth), Program(observer, expression, 0));
    }

    // ── The elaborated AST is the same node ─────────────────────────────────

    [Theory]
    [InlineData("P", "(P)")]
    [InlineData("P", "((P))")]
    [InlineData("Obj.X", "(Obj).X")]
    [InlineData("Obj.X", "((Obj)).X")]
    [InlineData("Obj.X", "(Obj.X)")]
    [InlineData("Id(1)", "(Id)(1)")]
    [InlineData("Id(1)", "(Id(1))")]
    [InlineData("P:0", "(P):0")]
    [InlineData("P:0", "(P:0)")]
    [InlineData("P*.Coll", "(P)*.Coll")]
    [InlineData("Coll(P*)", "Coll((P)*)")]
    [InlineData("[P]", "[(P)]")]
    [InlineData("()", "(())")]
    [InlineData("(1, 2)", "((1, 2))")]
    [InlineData("(P*)", "((P*))")]
    [InlineData("{1, 2}", "({1, 2})")]
    public void ElaboratedProgram_IsIdenticalModuloSpans(string bare, string grouped)
    {
        // The Lean-encoded elaborated program is span-free, so equality here means the two
        // spellings reach every semantic layer as ONE tree.
        var bareRoot = ParseValidRoot(Definitions + bare);
        var groupedRoot = ParseValidRoot(Definitions + grouped);
        Assert.Equal(LeanAstEncoder.EncodeProgram(bareRoot), LeanAstEncoder.EncodeProgram(groupedRoot));
    }

    // ── Evaluation count and order, sync and after genuine suspension ───────

    public static TheoryData<string, string, int[]> EffectPrograms => new()
    {
        { "Pair(a, b) = (a, b)\nPair((Probe(1)), Probe(2))", "Pair(a, b) = (a, b)\nPair(Probe(1), Probe(2))", new[] { 1, 2 } },
        { "Pair(a, b) = (a, b)\n(Probe(1)).Pair(Probe(2))", "Pair(a, b) = (a, b)\nProbe(1).Pair(Probe(2))", new[] { 1, 2 } },
        { "Pair(a, b) = (a, b)\n((Probe(1))).Pair((Probe(2)))", "Pair(a, b) = (a, b)\nPair(Probe(1), Probe(2))", new[] { 1, 2 } },
        { "Coll(*xs) = xs\nColl((Probe(1)), ((Probe(2))), Probe(3))", "Coll(*xs) = xs\nColl(Probe(1), Probe(2), Probe(3))", new[] { 1, 2, 3 } },
        { "Coll(*xs) = xs\n((Probe(1)))*.Coll(Probe(2))", "Coll(*xs) = xs\nProbe(1)*.Coll(Probe(2))", new[] { 1, 2 } },
        { "Pat((x, *y)) = ([x], y)\nPat(((Probe(1), Probe(2))))", "Pat((x, *y)) = ([x], y)\nPat((Probe(1), Probe(2)))", new[] { 1, 2 } },
        { "X = (Probe(1))\nX, X, (X)", "X = Probe(1)\nX, X, X", new[] { 1 } },
        { "if(true, (Probe(1)), 0), (Probe(2))", "if(true, Probe(1), 0), Probe(2)", new[] { 1, 2 } },
        { "[(Probe(1)), ((Probe(2)))]", "[Probe(1), Probe(2)]", new[] { 1, 2 } },
        { "count(((Probe(1))))", "count(Probe(1))", new[] { 1 } },
        // Failure paths: the failing slot stops the assembly at the same point.
        { "Pair(a, b) = (a, b)\nPair((Probe(1) / 0), Probe(2))", "Pair(a, b) = (a, b)\nPair(Probe(1) / 0, Probe(2))", new[] { 1 } },
        { "Pair(a, b) = (a, b)\nPair(Probe(1), ((Probe(2) / 0)))", "Pair(a, b) = (a, b)\nPair(Probe(1), Probe(2) / 0)", new[] { 1, 2 } },
        { "Coll(*xs) = xs\n((Probe(1) / 0)).Coll(Probe(2))", "Coll(*xs) = xs\n(Probe(1) / 0).Coll(Probe(2))", new[] { 1 } },
    };

    [Theory]
    [MemberData(nameof(EffectPrograms))]
    public async Task ArgumentEffects_AndFailures_AgreeWithTheBareSpelling_SyncAndSuspended(
        string grouped, string bare, int[] expectedTrace)
    {
        var baseline = await ObserveEffects(bare, suspend: false);
        Assert.Equal(expectedTrace, baseline.Trace);
        foreach (var (source, suspend) in new[] { (grouped, false), (bare, true), (grouped, true) })
        {
            var actual = await ObserveEffects(source, suspend);
            Assert.Equal(baseline.Outcome, actual.Outcome);
            Assert.Equal(baseline.Trace, actual.Trace);
        }
    }

    private static async Task<(string Outcome, int[] Trace)> ObserveEffects(string source, bool suspend)
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
        {
            result = Evaluator.RunCountedObserved(ast, enableOptimizations: false, hostOperations: operations).Result;
        }

        return (AsyncEvaluationHarness.NeutralOf(result), trace.ToArray());
    }

    // ── Cache and value demand: grouping never changes the access path ──────

    [Theory]
    [InlineData("A.count, A.count", 2)]
    [InlineData("(A).count, (A).count", 2)]
    [InlineData("((A)).count, ((A)).count", 2)]
    [InlineData("count((A)), count((A))", 2)]
    [InlineData("sum(A), sum((A))", 2)]
    [InlineData("A, (A), ((A))", 1)]
    [InlineData("X = (A)\nX, X, A", 1)]
    [InlineData("X = A\nY = (A)\nX == Y, (X) == (Y)", 1)]
    [InlineData("if(true, A, 0), if(true, (A), 0)", 2)]
    [InlineData("A.string, (A).string", 2)]
    [InlineData("A(), (A)()", 2)]
    [InlineData("[A, (A)], [(A)]:0", 1)]
    [InlineData("Two(x, y) = [x, y]\nTwo(A, (A))", 1)]
    public async Task HostBackedProperty_IsDemandedIdenticallyInEverySpelling(string output, int expectedCalls)
    {
        // A builtin value slot and an explicit call demand the property directly (one host
        // call per demand); a value-position read is served from the zero-argument cache
        // (one host call per run). Redundant parentheses pick neither path — they are not
        // there. The async host operation genuinely yields, so the suspended twin is
        // measured too.
        foreach (var asynchronous in new[] { false, true })
        {
            var calls = 0;
            Result Produce()
            {
                calls++;
                return new Result.Atom(100 * calls);
            }
            var operation = asynchronous
                ? HostOperation.CreateAsync("Data", async (_, _) => { await Task.Yield(); return Produce(); })
                : HostOperation.Create("Data", (_, _) => Produce());
            var options = new RunOptions { HostOperations = HostOperations.Create(operation) };
            var source = "A = Data()\n" + output;
            var result = asynchronous
                ? await KatLangEngine.RunAsync(source, options)
                : KatLangEngine.Run(source, options);
            Assert.IsType<RunResult.Success>(result);
            Assert.Equal(expectedCalls, calls);
        }
    }

    [Theory]
    [InlineData("sum(R) == sum(R)", "false")]
    [InlineData("sum((R)) == sum((R))", "false")]
    [InlineData("(R).sum == (R).sum", "false")]
    [InlineData("R.sum == R.sum", "false")]
    [InlineData("((R)).sum == sum(R)", "false")]
    [InlineData("R == R", "true")]
    [InlineData("(R) == (R)", "true")]
    [InlineData("R == ((R))", "true")]
    [InlineData("X = (R)\nX == R", "true")]
    [InlineData("R() == R()", "false")]
    [InlineData("(R)() == R()", "false")]
    [InlineData("R.string == R.string", "false")]
    [InlineData("(R).string == (R).string", "false")]
    [InlineData("if(true, R, 0) == if(true, (R), 0)", "false")]
    [InlineData("X = if(true, (R), 0)\nX == X", "true")]
    public async Task RandomBackedProperty_DrawsIdenticallyInEverySpelling(string output, string expected)
    {
        // A trailing draw pins the exact stream position: Boolean equality alone
        // cannot distinguish two draws from three or more accidental evaluations.
        foreach (var seed in new[] { 7L, 0L, long.MinValue })
        {
            var draws = expected == "true" ? 1 : 2;
            var reference = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
                string.Join(", ", Enumerable.Repeat("random(1, 1000000)", draws + 1)),
                new RunOptions { RandomSeed = seed }));
            var sentinel = SemanticExplorerHarness.Neutral(reference.OutputRows[^1]);
            var wanted = $"ok raw=S[{expected}, {sentinel}] n=2";
            var ast = AsyncEvaluationHarness.Ast("R = random(1, 1000000)\n" + output + ", random(1, 1000000)");
            foreach (var optimize in new[] { false, true })
                Assert.Equal(wanted, AsyncEvaluationHarness.NeutralOf(
                    Evaluator.RunCountedObserved(ast, enableOptimizations: optimize, randomSeed: seed).Result));
            var cache = new PassThroughAsyncZeroArgPropertyResultCache();
            var asyncRun = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
                ast, zeroArgPropertyResultCache: cache, randomSeed: seed));
            Assert.Equal(wanted, AsyncEvaluationHarness.NeutralOf(asyncRun.Result));
            Assert.Equal(0, cache.SyncAccesses);
        }
    }

    [Theory]
    [InlineData("7", "L[7]")]
    [InlineData("true", "L[true]")]
    [InlineData("'s'", "L['s']")]
    [InlineData("[7]", "L[7]")]
    [InlineData("[()]", "L[]")]
    [InlineData("[(1, 2)]", "L[1, 2]")]
    [InlineData("[[1, 2]]", "L[1, 2]")]
    public void NestedOrdinaryPattern_KeepsScalarFallbackAndRealListBoundaries(string argument, string expected)
    {
        // Only a list can retain a unary STRUCTURE. Scalars need no wrapper:
        // each ordinary sequence-value pattern treats a scalar as one item.
        const string declaration = "P(((*xs))) = xs\n";
        for (var depth = 0; depth <= 3; depth++)
        {
            var source = declaration + "P(" + Grouped(argument, depth) + ")";
            Assert.Equal($"ok raw={expected} n=1", Neutral(source));
            AssertStrategiesAgree(source, declaration + "P(" + argument + ")");
        }
    }

    [Fact]
    public void DotMemberArguments_AndCallingTheDotResult_KeepTheirDifferentGrammar()
    {
        const string declarations = "M = { public Add(x) = x + 1 }\n";
        var member = Assert.IsType<Expr.DotCall>(Assert.Single(ParseValidRoot(declarations + "M.Add(1)").Output));
        Assert.Single(Assert.IsType<OutputBundle>(member.Args));
        Assert.Equal("ok raw=2 n=1", Neutral(declarations + "M.Add(1)"));

        foreach (var target in new[] { "(M.Add)", "((M.Add))", "(((M.Add)))" })
        {
            // The closing group ends the dot production before the call delimiter.
            // The result is Call(DotCall(args: null), args), not a Capture node.
            var call = Assert.IsType<Expr.Call>(Assert.Single(ParseValidRoot(declarations + target + "(1)").Output));
            Assert.Null(Assert.IsType<Expr.DotCall>(call.Function).Args);
            var result = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(ParseValidRoot(declarations + target + "(1)"))).Result;
            Assert.True(result.IsError);
            var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
            Assert.Equal(0, arity.Expected);
            Assert.Equal(1, arity.Actual);
        }
    }

    [Theory]
    [InlineData("()")]
    [InlineData("7")]
    [InlineData("[1, 2]")]
    [InlineData("(1, 2)")]
    [InlineData("repeat({a, b}, 1, 1, 2)")]
    public async Task HostBuiltSingleRowCapture_PatternBindingUsesItsValue(string expression)
    {
        // The host API still supports this node even though redundant expression
        // grouping no longer produces it. A pattern must not see the host row list.
        var root = ParseValidRoot("P((*xs)) = xs\nP(" + expression + ")");
        var call = Assert.IsType<Expr.Call>(Assert.Single(root.Output));
        var argument = Assert.Single(call.Args);
        var expected = AsyncEvaluationHarness.NeutralOf(Evaluator.RunCounted(new Expr.AlgorithmExpr(root)));
        for (var depth = 1; depth <= 3; depth++)
        {
            argument = new Expr.Capture([argument]);
            var host = new Expr.AlgorithmExpr(root with { Output = [call with { Args = [argument] }] });
            foreach (var optimize in new[] { false, true })
                Assert.Equal(expected, AsyncEvaluationHarness.NeutralOf(
                    Evaluator.RunCountedObserved(host, enableOptimizations: optimize).Result));
            var cache = new PassThroughAsyncZeroArgPropertyResultCache();
            Assert.Equal(expected, AsyncEvaluationHarness.NeutralOf(
                await AsyncEvaluationHarness.Complete(Evaluator.RunCountedAsync(host, cache))));
        }
    }

    [Theory]
    [InlineData("Missing = { public V = 1 }\n", "Missing", KatLangErrorCode.MissingOutput)]
    [InlineData("Missing = { public V = 1 }\n", "(Missing*)", KatLangErrorCode.SpreadMissingOutput)]
    [InlineData("", "P:9", KatLangErrorCode.BadIndex)]
    [InlineData("", "'s' + 1", KatLangErrorCode.TypeMismatch)]
    [InlineData("", "Two(1)", KatLangErrorCode.ArityMismatch)]
    [InlineData("", "count(Two)", KatLangErrorCode.ArityMismatch)]
    public void GroupingPreservesStructuredErrorCode(string declarations, string expression, KatLangErrorCode code)
    {
        for (var depth = 0; depth <= 3; depth++)
        {
            var source = Definitions + declarations + Grouped(expression, depth);
            SourceProvenance.ParseValid(source);
            var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
            Assert.Equal(code, Assert.Single(failure.Errors).Code);
        }
    }

    // ── Structural members, extension fallback, and the intrinsic ───────────

    [Fact]
    public void GroupedReceiver_NavigatesExactlyLikeTheBareReceiver()
    {
        const string source = """
            X(o) = 99
            Obj = {
                public X = 7
                public Y(v) = v * 2
                0
            }
            Q(z) = (Obj).X
            Obj.X, (Obj).X, ((Obj)).X, Q(0), (Obj).Y(3), ((Obj)).Y(3), X((Obj)), 3.X, (3).X
            """;
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal(
            string.Join(Environment.NewLine, "7", "7", "7", "7", "6", "6", "99", "99", "99"),
            run.ToDisplayString());

        // Only a genuine capture receiver has no structural identity.
        var capture = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            "X(o) = 99\nObj = {\n    public X = 7\n    0\n}\n(Obj*).X, (Obj, Obj).X"));
        Assert.Equal($"99{Environment.NewLine}99", capture.ToDisplayString());
    }

    [Fact]
    public void StringIntrinsic_IsTheSameValueAndTheSameDemandInEverySpelling()
    {
        // `.string` stays the spelling-recognized intrinsic on a numeric receiver (never
        // extension fallback), and a grouped receiver is the same receiver.
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            "A = 42\nA.string == (A).string, 42.string == ((42)).string, (1 + 2).string == ((1 + 2)).string, ((A)).string"));
        Assert.Equal(string.Join(Environment.NewLine, "true", "true", "true", "42"), run.ToDisplayString());
        Assert.IsType<Result.Str>(run.OutputRows[3]);

        // A non-numeric receiver is the same intrinsic rejection in both spellings.
        var bare = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("(1, 2).string"));
        var grouped = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("((1, 2)).string"));
        Assert.Equal(Assert.Single(bare.Errors).Code, Assert.Single(grouped.Errors).Code);
        Assert.Equal(KatLangErrorCode.TypeMismatch, Assert.Single(grouped.Errors).Code);
    }

    // ── Optimizers converge on the same path ────────────────────────────────

    [Theory]
    [InlineData("A.filter(Keep).count", "(A).filter(Keep).count", true)]
    [InlineData("A.filter(Keep).count", "((A)).filter(Keep).count", true)]
    [InlineData("A.filter(Keep).count", "(A).filter((Keep)).count", true)]
    [InlineData("range(1, 5).filter(Keep).count", "(range(1, 5)).filter(Keep).count", true)]
    [InlineData("count(filter(range(1, 5), Keep))", "count(filter((range(1, 5)), (Keep)))", true)]
    [InlineData("count(filter(A, Keep))", "count(filter((A), Keep))", false)]
    [InlineData("filter(A, Keep).count", "filter((A), (Keep)).count", false)]
    public void FilterCountFusion_TakesTheSamePathForGroupedSpellings(string bare, string grouped, bool fuses)
    {
        // The optimizer sees the same tree, so the grouped spelling fuses exactly when the
        // bare spelling fuses (the forms that fuse today are pinned here as the anchor; the
        // written-call forms over a property source do not, and the group does not change
        // that either).
        const string definitions = "Keep(x) = x > 1\nA = range(1, 5)\n";
        var bareDiagnostics = new SequencePipelineDiagnostics();
        var groupedDiagnostics = new SequencePipelineDiagnostics();
        var (bareResult, _) = Evaluator.RunCountedObserved(AsyncEvaluationHarness.Ast(definitions + bare), sequenceDiagnostics: bareDiagnostics);
        var (groupedResult, _) = Evaluator.RunCountedObserved(AsyncEvaluationHarness.Ast(definitions + grouped), sequenceDiagnostics: groupedDiagnostics);
        var (generic, _) = Evaluator.RunCountedObserved(AsyncEvaluationHarness.Ast(definitions + grouped), enableOptimizations: false);
        Assert.True(groupedResult.IsOk, groupedResult.IsError ? groupedResult.Error.ToString() : "");
        Assert.Equal("4", Assert.IsType<Result.Atom>(groupedResult.Value.Value).Value.ToString());
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(groupedResult));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(bareResult), AsyncEvaluationHarness.NeutralOf(groupedResult));
        Assert.Equal(fuses ? 1 : 0, bareDiagnostics.GetSnapshot().FilterCountFusionHits);
        Assert.Equal(bareDiagnostics.GetSnapshot().FilterCountFusionHits, groupedDiagnostics.GetSnapshot().FilterCountFusionHits);
    }

    [Theory]
    [InlineData("n + T")]
    [InlineData("n + (T)")]
    [InlineData("n + ((T))")]
    [InlineData("(n) + (T) * ((2))")]
    public void PlannedLoop_PlansGroupedSpellingsLikeTheBareOnes(string expression)
    {
        var source = "Step(n) = {\n    T = 2\n    " + expression + "\n}\nStep.repeat(3, 0)";
        var loop = new LoopOptimizationDiagnostics();
        var ast = AsyncEvaluationHarness.Ast(source);
        var (planned, _) = Evaluator.RunCountedObserved(ast, loopDiagnostics: loop);
        var (generic, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        Assert.True(planned.IsOk);
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(planned));
        var snapshot = loop.GetSnapshot();
        Assert.Equal(1, snapshot.OptimizedLoopHits);
        Assert.True(Assert.Single(Assert.Single(snapshot.LoopPlans).Expressions).Planned);
    }

    // ── Genuinely suspended async agrees with the sync oracle ───────────────

    [Theory]
    [InlineData("Coll(*xs) = xs\nA = (1, 2)\n((A)).Coll")]
    [InlineData("Coll(*xs) = xs\nA = (1, 2)\nColl(((A)))")]
    [InlineData("Coll(*xs) = xs\nA = ()\n(A).Coll, ((A))*.Coll")]
    [InlineData("Pat((x, *y)) = ([x], y)\nA = (1, 2, 3)\nPat(((A)))")]
    [InlineData("Obj = { public X = 7\n0 }\nV = Obj.X\n(V), ((V)) + 1")]
    [InlineData("A = [1, 2]\nV = A\n((V)):0, (V).count")]
    public async Task SuspendedRun_ProducesTheSynchronousOutcome_ForGroupedSpellings(string source)
    {
        var ast = AsyncEvaluationHarness.Ast(source);
        var sync = Evaluator.RunCounted(ast);
        var cache = new HoldingAsyncZeroArgPropertyResultCache(holdAtAccess: 1);
        var pending = Evaluator.RunCountedAsync(ast, cache).AsTask();
        try
        {
            await cache.Reached.WaitAsync(TimeSpan.FromSeconds(10));
            Assert.False(pending.IsCompleted);
        }
        finally
        {
            cache.Release();
        }
        var async = await pending.WaitAsync(TimeSpan.FromSeconds(10));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(async));
        Assert.True(cache.AsyncAccesses > 0);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(3)]
    public async Task CancellationDuringGroupedCacheRead_StopsBeforeTheNextEffect(int depth)
    {
        var calls = 0;
        var operations = HostOperations.Create(HostOperation.Create("Later", (_, _) =>
        {
            calls++;
            return new Result.Atom(9);
        }));
        var parsed = await SourceProvenance.ParseValidAsync("A = 7\n" + Grouped("A", depth) + ", Later()",
            new RunOptions { HostOperations = operations });
        using var cancellation = new CancellationTokenSource();
        var cache = new HoldingAsyncZeroArgPropertyResultCache(holdAtAccess: 1);
        var pending = Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root),
            zeroArgPropertyResultCache: cache, hostOperations: operations, cancellationToken: cancellation.Token).AsTask();
        try
        {
            await cache.Reached.WaitAsync(TimeSpan.FromSeconds(10));
            Assert.False(pending.IsCompleted);
            cancellation.Cancel();
        }
        finally
        {
            cache.Release();
        }
        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => pending.WaitAsync(TimeSpan.FromSeconds(10)));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal(0, calls);
    }

    // ── Helpers ─────────────────────────────────────────────────────────────

    private static void AssertStrategiesAgree(string grouped, string bare)
    {
        var groupedAst = new Expr.AlgorithmExpr(ParseValidRoot(grouped));
        var bareAst = new Expr.AlgorithmExpr(ParseValidRoot(bare));
        var (bareGeneric, bareBudget) = Evaluator.RunCountedObserved(bareAst, enableOptimizations: false);
        var (generic, genericBudget) = Evaluator.RunCountedObserved(groupedAst, enableOptimizations: false);
        var (planned, _) = Evaluator.RunCountedObserved(groupedAst, enableOptimizations: true);
        var expected = AsyncEvaluationHarness.NeutralOf(bareGeneric);
        Assert.Equal(expected, AsyncEvaluationHarness.NeutralOf(generic));
        Assert.Equal(expected, AsyncEvaluationHarness.NeutralOf(planned));

        // Operational counters agree with the bare spelling too: the group charged nothing.
        Assert.Equal(bareBudget.ConsumedSteps, genericBudget.ConsumedSteps);
        Assert.Equal(bareBudget.PeakDepth, genericBudget.PeakDepth);
        Assert.Equal(bareBudget.MaterializedItems, genericBudget.MaterializedItems);

        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var (asyncResult, asyncBudget) = AsyncEvaluationHarness
            .Complete(Evaluator.RunCountedObservedAsync(groupedAst, zeroArgPropertyResultCache: cache))
            .GetAwaiter()
            .GetResult();
        Assert.Equal(expected, AsyncEvaluationHarness.NeutralOf(asyncResult));
        Assert.Equal(genericBudget.ConsumedSteps, asyncBudget.ConsumedSteps);
        Assert.Equal(genericBudget.PeakDepth, asyncBudget.PeakDepth);
        Assert.Equal(0, cache.SyncAccesses);
    }
}
