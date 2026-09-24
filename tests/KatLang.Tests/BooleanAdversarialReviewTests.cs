using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using KatLang.ParserFuzz;
using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

public class BooleanAdversarialReviewTests
{
    public static TheoryData<string, string> SuccessfulPrograms() => new()
    {
        { "true, false", "S[true, false]" },
        { "[true, false]", "L[true, false]" },
        { "if(true == 1, 10, 20)", "20" },
        { "if(not 1 == 1, 10, 20)", "20" },
        { "range(-2, 2).filter{x >= 0}", "L[0, 1, 2]" },
        { "range(-2, 2).map{x >= 0}", "L[false, false, true, true, true]" },
        { "range(-2, 2).map{x >= 0}.contains(true)", "true" },
        { "1 == true, true == 1, 0 == false, false == 0", "S[false, false, false, false]" },
        { "1 != true, true != 1, 0 != false, false != 0", "S[true, true, true, true]" },
        { "distinct([true, 1, false, 0, true, 1])", "L[true, 1, false, 0]" },
        { "F((true, x)) = not x\nF((false, x)) = x\nF((true, false)), F((false, true))", "S[true, true]" },
        { "F(x, x) = true\nF(x, y) = false\nF(true, 1), F(false, 0), F(true, true)", "S[false, false, true]" },
        { "a, *b = true, false, 1\n[a, b]", "L[true, L[false, 1]]" },
        { "open M\nM = { public Flag = true }\nFlag, M.Flag", "S[true, true]" },
        { "P = true\nF(x) = (P)\nrange(0, 2).filter(F).count", "3" },
        { "Apply(f, x) = f(x)\nF(x) = Apply({v >= 0}, x)\nrange(-2, 2).filter(F).count", "3" },
        { "F(x) = if(x, false, true)\nmap([true, false], F)", "L[false, true]" },
        { "S(x) = if(x == true, 0, true)\nS.repeat(4, true)", "true" },
        { "S(x) = if(x == true, 0, true), x != 0\nS.while(true)", "0" },
        { "S(b) = not b\nS.while(false)", "true" },
        { "S(x) = [true, false], false\nS.while(7)", "7" },
        { "if({true}, false, 1 / 0)", "false" },
        { "F(x) = { true, ()* }\nrange(0, 2).filter(F).count", "3" },
        { "F(x) = ()*, false\nrange(0, 2).filter(F).count", "0" },
    };

    [Theory]
    [MemberData(nameof(SuccessfulPrograms))]
    public async Task ValuesAndBoundaries_AgreeAcrossExecutionPaths(string source, string expected)
    {
        var result = await AssertPaths(source);
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : source);
        Assert.Equal(expected, SemanticExplorerHarness.Neutral(result.Value));
    }

    public static TheoryData<string, string> PredicateShapes()
    {
        var data = new TheoryData<string, string>();
        foreach (var shape in new[] { "0", "1", "-1", "()", "[true]", "[[true]]", "(true, false)", "((), true)", "(true, ())", "(true, 1)", "([true], false)", "'true'" })
        {
            data.Add($"if({shape}, 10, 20)", "if condition");
            data.Add($"F(x) = {shape}\nrange(0, 2).filter(F).count", "filter predicate result");
            data.Add($"S(x) = x, {shape}\nS.while(0)", "while continuation flag");
            data.Add($"S(x) = if({shape}, x, x)\nS.repeat(1, true)", "if condition");
        }
        return data;
    }

    [Theory]
    [MemberData(nameof(PredicateShapes))]
    public async Task PredicateConsumers_RejectTheWholeMalformedValue(string source, string role)
    {
        var result = await AssertPaths(source);
        Assert.True(result.IsError, source);
        Assert.Contains(role, Assert.IsType<EvalError.TypeMismatch>(Innermost(result.Error)).Message);
    }

    public static TheoryData<string> PlannedOperators()
    {
        var data = new TheoryData<string>();
        foreach (var op in new[] { "<", "<=", ">", ">=", "==", "!=", "and", "or", "xor", "+", "-", "*", "/", "div", "mod", "^" })
        foreach (var values in new[] { ("true", "false"), ("true", "1"), ("1", "true"), ("1", "0") })
            data.Add($"S(x, y) = x {op} y, y\nS.repeat(1, {values.Item1}, {values.Item2})");
        return data;
    }

    [Theory]
    [MemberData(nameof(PlannedOperators))]
    public async Task EveryOperator_UsesTheSameValueKindsAndDiagnosticsInAPlan(string source)
        => await AssertPaths(source, requirePlan: true);

    [Theory]
    [InlineData("S(b) = not b\nS.repeat(5, false)")]
    [InlineData("S(x) = if(x == true, 0, true)\nS.repeat(4, true)")]
    [InlineData("S(x) = if(x == true, 0, true), x != 0\nS.while(true)")]
    [InlineData("S(x) = if(x, false, true)\nS.repeat(4, false)")]
    [InlineData("S(x) = false and (1 / 0 == x)\nS.repeat(1, true)")]
    [InlineData("S(x) = true or (1 / 0 == x)\nS.repeat(1, true)")]
    public async Task BooleanPlans_ActuallyExecuteWithoutExpressionFallback(string source)
        => await AssertPaths(source, requirePlan: true);

    [Theory]
    [InlineData("true")]
    [InlineData("false")]
    [InlineData("x >= 0")]
    [InlineData("[true]")]
    [InlineData("true, false")]
    [InlineData("(), true")]
    [InlineData("true, ()")]
    [InlineData("x")]
    public async Task FilterCount_ActuallyFuses_AndPreservesTheEntirePredicateError(string body)
        => await AssertPaths($"F(x) = {body}\nrange(-2, 2).filter(F).count", requireFusion: true);

    [Theory]
    [InlineData("F(*true) = 1")]
    [InlineData("F((x, *false)) = x")]
    [InlineData("*true = 1")]
    [InlineData("(x, false) = (1, 2)")]
    [InlineData("open true")]
    [InlineData("M = { public false = 1 }\nopen M")]
    [InlineData("M = { public A = 1 }\nM.true")]
    public void ReservedLiterals_NeverBecomeBindings(string source)
        => Assert.True(Parser.Parse(source).HasErrors, source);

    [Theory]
    [InlineData(true, "true")]
    [InlineData(false, "false")]
    public void FuzzFingerprint_PreservesBooleanLiteralAndPatternPayloads(bool value, string text)
    {
        // Locationless nodes ensure the difference comes from the payload, not token width.
        static string Literal(bool flag) => FrontEndFingerprint.ComputeParseResult(
            new Algorithm.User(null, [], [], [], [new Expr.BoolLiteral(flag)]), []);
        Assert.Contains($"Bool{{{text}}}", Literal(value));
        Assert.NotEqual(Literal(value), Literal(!value));
        var parsed = SourceProvenance.ParseValid($"F({text}) = 1\nF({text})");
        Assert.Contains($"LBool{{{text}}}", FrontEndFingerprint.ComputeParseResult(parsed.Root, []));
    }

    [Fact]
    public async Task HostBooleans_NormalizeBeforeCaching_AndRemainInStructuredResults()
    {
        foreach (var asynchronous in new[] { false, true })
        {
            var calls = 0;
            Result Produce()
            {
                calls++;
                return new Result.SequenceValue([new Result.SequenceValue([new Result.Bool(true)])]);
            }
            var operation = asynchronous
                ? HostOperation.CreateAsync("Flag", async (_, _) => { await Task.Yield(); return Produce(); })
                : HostOperation.Create("Flag", (_, _) => Produce());
            var options = new RunOptions { HostOperations = HostOperations.Create(operation) };
            // The three value-position reads share ONE host evaluation through the
            // zero-argument property cache; the `if` condition is a builtin value slot,
            // which demands the property directly (a second host call) — and redundant
            // parentheses around it change nothing (parentheses group syntax).
            const string source = "Flag, Flag, not Flag, if((Flag), true, false)";
            var result = asynchronous
                ? await KatLangEngine.RunAsync(source, options)
                : KatLangEngine.Run(source, options);
            var success = Assert.IsType<RunResult.Success>(result);
            Assert.Equal("S[true, true, false, true]", SemanticExplorerHarness.Neutral(success.Value));
            Assert.Empty(success.Atoms);
            Assert.Equal(2, calls);
        }
        Assert.Empty(KatLangEngine.EvaluateToAtoms("true"));
        Assert.Empty(await KatLangEngine.EvaluateToAtomsAsync("false"));
        Assert.Empty(await KatLangEngine.EvaluateToAtomsAsync("[true, false]"));
    }

    private static async Task<EvalResult<Result>> AssertPaths(
        string source, bool requirePlan = false, bool requireFusion = false)
    {
        var ast = Program(source);
        var generic = Evaluator.Run(ast, new RunScopedZeroArgPropertyResultCache(), false, null, false, null);
        var loop = new LoopOptimizationDiagnostics();
        var sequence = new SequencePipelineDiagnostics();
        var optimized = Evaluator.Run(ast, new RunScopedZeroArgPropertyResultCache(), true, loop, true, sequence);
        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var twin = await Evaluator.RunCountedAsync(ast, cache);
        Assert.Equal(0, cache.SyncAccesses);
        Assert.Equal(generic.IsError, optimized.IsError);
        Assert.Equal(generic.IsError, twin.IsError);
        if (generic.IsError)
        {
            Assert.Equal(DescribeErrorTree(generic.Error), DescribeErrorTree(optimized.Error));
            Assert.Equal(DescribeErrorTree(generic.Error), DescribeErrorTree(twin.Error));
        }
        else
        {
            Assert.Equal(generic.Value, optimized.Value, Result.ValueComparer);
            Assert.Equal(generic.Value, twin.Value.Value, Result.ValueComparer);
        }
        if (requirePlan)
        {
            Assert.Equal(1, loop.GetSnapshot().OptimizedLoopHits);
            Assert.Equal(0, loop.GetSnapshot().GenericExpressionEvaluationsInsideOptimizedLoops);
        }
        if (requireFusion)
            Assert.Equal(1, sequence.GetSnapshot().FilterCountFusionHits);
        return generic;
    }
}
