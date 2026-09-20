using System.Collections;
using System.Numerics;
using System.Reflection;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

public class ComparisonChainHostileReviewTests
{
    [Theory]
    [InlineData("3 < 2 < 1", "false")]
    [InlineData("true == true == true", "true")]
    [InlineData("true != false != true", "true")]
    [InlineData("true == 1 == false", "false")]
    [InlineData("true == true == false", "false")]
    [InlineData("1 + 1 < 3 == 2 + 0", "false")]
    [InlineData("-2 ^ 2 < 0 == true", "false")]
    public void HostileBooleanExamples(string source, string expected)
    {
        SourceProvenance.ParseValid(source);
        Assert.Equal(expected, Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString());
    }

    [Theory]
    [InlineData("(-2).abs < true", "(-2).abs < true")]
    [InlineData("(not true).count < false", "(not true).count < false")]
    [InlineData("(-2).abs:0 < true", "(-2).abs:0 < true")]
    public void FailingLinkNames_PreservePostfixReceiverGrouping(string source, string expected)
    {
        SourceProvenance.ParseValid(source);
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)).Errors);
        Assert.Equal(KatLangErrorCode.TypeMismatch, error.Code);
        Assert.Contains($"while evaluating `{expected}`", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DiagnosticNames_RoundTripOperatorTrees()
    {
        // Source-derived trees, not a value oracle: equal final values cannot hide a
        // lost grouping boundary. Include all binary pairs and each chain operand slot.
        string[] operators = ["+", "-", "*", "/", "div", "mod", "^", "and", "xor", "or", "<", "<=", ">", ">=", "==", "!="];
        var atoms = new List<string> { "a", "not a", "-a", "-a ^ b", "a < b == c", "(-a).f", "(not a).f", "a:(b < c)", "(a < b):0" };
        atoms.AddRange(operators.Select(op => $"a {op} b"));
        foreach (var child in atoms)
        {
            foreach (var op in operators)
            {
                Check($"({child}) {op} c");
                Check($"c {op} ({child})");
            }
            Check($"a < ({child}) == c");
            Check($"not ({child})");
            Check($"-({child})");
        }

        static void Check(string source)
        {
            var original = Raw(source);
            var rendered = ExprNameRenderer.Render(original, ExprNameMode.DiagnosticName);
            Assert.Equal(Shape(original), Shape(Raw(rendered)));
        }
    }

    private static Expr Raw(string source)
    {
        var parsed = Parser.ParseSyntax(source);
        Assert.False(parsed.HasErrors, source + ": " + string.Join("; ", parsed.Diagnostics.Select(d => d.Message)));
        return Assert.Single(parsed.Root.Output);
    }

    [Theory]
    [InlineData("a < b <= c")]
    [InlineData("(a < b <= c)")]
    [InlineData("F(a < b <= c)")]
    [InlineData("[a < b <= c]")]
    [InlineData("P = a < b <= c")]
    [InlineData("Outer = { Inner = a < b <= c\nInner }")]
    [InlineData("xs:(a < b <= c)")]
    [InlineData("xs.map{ a < b <= c }")]
    [InlineData("if(a < b <= c, 1, 0)")]
    [InlineData("F(0) = a < b <= c\nF(x) = false")]
    [InlineData("a <\n b <=\n c")]
    public void EverySurfaceContext_UsesTheSameChainNode(string source)
    {
        var parsed = Parser.ParseSyntax(source);
        Assert.False(parsed.HasErrors, string.Join(';', parsed.Diagnostics));
        var visitor = new ChainVisitor();
        visitor.VisitAlgorithm(parsed.Root);
        var chain = Assert.Single(visitor.Chains);
        Assert.Equal([ComparisonOp.Lt, ComparisonOp.Le], chain.Links.Select(link => link.Op));
        Assert.Equal(["a", "b", "c"], new[] { chain.First }.Concat(chain.Links.Select(link => link.Operand)).Select(operand => Assert.IsType<Expr.Resolve>(operand).Name));
    }

    private sealed class ChainVisitor : AstWalker
    {
        public List<Expr.Comparison> Chains { get; } = [];
        protected override bool VisitsExplicitParameterDeclarations => false;
        public override void VisitExpr(Expr expr)
        {
            if (expr is Expr.Comparison chain) Chains.Add(chain);
            base.VisitExpr(expr);
        }
    }

    private static string Shape(Expr expr) => expr switch
    {
        Expr.Num n => n.Value.ToString(System.Globalization.CultureInfo.InvariantCulture),
        Expr.Resolve r => r.Name,
        Expr.Unary u => $"{u.Op}({Shape(u.Operand)})",
        Expr.Binary b => $"{b.Op}({Shape(b.Left)},{Shape(b.Right)})",
        Expr.Comparison c => $"cmp({Shape(c.First)};{string.Join(';', c.Links.Select(l => $"{l.Op}:{Shape(l.Operand)}"))})",
        Expr.Index i => $"index({Shape(i.Target)},{Shape(i.Selector)})",
        Expr.DotCall d => $"dot({Shape(d.Target)},{d.Name})",
        Expr.Capture c => $"capture({string.Join(';', c.Body.Select(Shape))})",
        _ => throw new InvalidOperationException($"Unexpected round-trip test node {expr.GetType().Name}"),
    };

    [Fact]
    public void NegativeHostLiterals_KeepTheirGroupingInEveryPostfixPosition()
    {
        var negative = new Expr.Num(-2);
        foreach (var mode in new[] { ExprNameMode.Open, ExprNameMode.DiagnosticName })
        {
            Assert.Equal("(-2).abs", ExprNameRenderer.Render(new Expr.DotCall(negative, "abs", null), mode));
            Assert.Equal("(-2):0", ExprNameRenderer.Render(new Expr.Index(negative, new Expr.Num(0)), mode));
            Assert.Equal("(-2)*", ExprNameRenderer.Render(new Expr.SequenceSpread(negative), mode));
            Assert.Equal("(-2)(...)", ExprNameRenderer.Render(new Expr.Call(negative, OutputBundle.Empty), mode));
        }
    }

    [Fact]
    public void LinklessHostChain_IsNotNamedAsItsOperand()
    {
        var chain = new Expr.Comparison(new Expr.Num(7), []);
        Assert.Equal(new Result.Bool(true), Evaluator.Run(chain).Value);
        // The host-only vacuous chain returns true, not 7; there is no source
        // spelling for it. Use an explicit diagnostic placeholder, like {...}.
        foreach (var mode in new[] { ExprNameMode.Open, ExprNameMode.DiagnosticName })
            Assert.Equal("<comparison with no links>", ExprNameRenderer.Render(chain, mode));
    }

    [Theory]
    [InlineData("A() < B() <= C() != D()", "ABCD", null)]
    [InlineData("D() < B() < C() < A()", "DBCA", null)]
    [InlineData("A() < B() < true < C()", "AB", KatLangErrorCode.TypeMismatch)]
    [InlineData("D() < B() < true < C()", "DB", KatLangErrorCode.TypeMismatch)]
    [InlineData("A() < B() < 1 / 0 < C()", "AB", KatLangErrorCode.DivisionByZero)]
    [InlineData("1 / 0 < A() < B()", "", KatLangErrorCode.DivisionByZero)]
    public async Task OperandTraces_AreIncrementalAcrossCallbacksLoopsAndTwins(
        string chain, string expectedTrace, KatLangErrorCode? expectedError)
    {
        foreach (var template in new[] { "{0}", "map([0], {{ if(x == 0, {0}, true) }})", "range(0, 0).filter{{ if(x == 0, {0}, true) }}.count", "Step(x) = x + if({0}, 1, 0)\nStep.repeat(1, 0)" })
        {
            var source = string.Format(System.Globalization.CultureInfo.InvariantCulture, template, chain);
            foreach (var mode in new[] { "generic", "optimized", "async" })
            {
                var trace = new List<string>();
                var operations = HostOperations.Create(new[] { "A", "B", "C", "D" }.Select((name, index) =>
                    mode == "async"
                        ? HostOperation.CreateAsync(name, async (_, _) => { await Task.Yield(); trace.Add(name); return new Result.Atom(index + 1); })
                        : HostOperation.Create(name, (_, _) => { trace.Add(name); return new Result.Atom(index + 1); })).ToArray());
                var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
                Assert.False(parsed.HasErrors, source + ": " + string.Join(';', parsed.Diagnostics));
                var ast = new Expr.AlgorithmExpr(parsed.Root);
                var result = mode == "async"
                    ? (await Evaluator.RunCountedObservedAsync(ast, hostOperations: operations)).Result
                    : Evaluator.RunCountedObserved(ast, enableOptimizations: mode == "optimized", hostOperations: operations).Result;
                Assert.Equal(expectedTrace, string.Concat(trace));
                Assert.Equal(expectedError.HasValue, result.IsError);
                if (expectedError is { } code) Assert.Equal(code, result.Error.Code);
            }
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task CancellationAfterFalse_StopsBeforeTheNextHostOperation(bool asynchronous)
    {
        using var cancellation = new CancellationTokenSource();
        var trace = new List<string>();
        Result Cancel()
        {
            trace.Add("Cancel");
            cancellation.Cancel();
            return new Result.Atom(4);
        }
        var operations = HostOperations.Create(
            asynchronous
                ? HostOperation.CreateAsync("Cancel", async (_, _) => { await Task.Yield(); return Cancel(); })
                : HostOperation.Create("Cancel", (_, _) => Cancel()),
            HostOperation.Create("Later", (_, _) => { trace.Add("Later"); return new Result.Atom(5); }));
        var options = new RunOptions { HostOperations = operations, EvaluationCancellationToken = cancellation.Token };
        const string source = "3 < 2 < Cancel() < Later()";
        Assert.False(Parser.Parse(source, options).HasErrors);
        var error = asynchronous
            ? await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await KatLangEngine.RunAsync(source, options))
            : Assert.ThrowsAny<OperationCanceledException>(() => KatLangEngine.Run(source, options));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal(["Cancel"], trace);
    }

    [Fact]
    public async Task DeferredModuleChain_RunsOnceAndPositionsTheLinkInTheLoadingDocument()
    {
        var trace = new List<string>();
        var downloads = 0;
        var operations = HostOperations.Create(
            HostOperation.CreateAsync("Tick", async (_, _) => { await Task.Yield(); trace.Add("Tick"); return new Result.Atom(2); }),
            HostOperation.Create("Later", (_, _) => { trace.Add("Later"); return new Result.Atom(4); }));
        var options = new RunOptions
        {
            HostOperations = operations,
            DownloadCode = async (_, _) => { await Task.Yield(); downloads++; return "\n\n\npublic Check = 3 < Tick() < true < Later()"; },
        };
        const string source = "F(0) = false\nF(n) = { open 'https://katlang.org/chain.kat'\nCheck }\nF(1)";
        var parsed = await Parser.ParseAsync(source, options);
        Assert.False(parsed.HasErrors, string.Join(';', parsed.Diagnostics));
        Assert.Equal(0, downloads);
        var result = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root), hostOperations: operations);
        Assert.True(result.Result.IsError);
        Assert.Equal(KatLangErrorCode.TypeMismatch, result.Result.Error.Code);
        Assert.Equal(["Tick"], trace);
        Assert.Equal(1, downloads);
        Assert.Contains("Tick(...) < true", result.Result.Error.ToString(), StringComparison.Ordinal);
        Assert.Equal(new SourceSpan(3, 1, 3, 6), result.Result.Error.Span);
    }

    [Theory]
    [InlineData("'xxxxxxxxxx' != T() == 'xxxxxxxxxx'", 30, false)]
    [InlineData("3 < 2 < true == T()", 0, true)]
    public void FullyPlannedChains_AreEagerAfterFalseAndStopAtALinkError(string condition, long units, bool error)
    {
        var parsed = SourceProvenance.ParseValid($"Step = {{\nT = 'xxxxxxxxxx'\nn + if({condition}, 1, 0)\n}}\nStep.repeat(1, 0)");
        foreach (var optimized in new[] { false, true })
        {
            var diagnostics = new LoopOptimizationDiagnostics();
            var observed = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), enableOptimizations: optimized, loopDiagnostics: diagnostics);
            Assert.Equal(error, observed.Result.IsError);
            if (error) Assert.Equal(KatLangErrorCode.TypeMismatch, observed.Result.Error.Code);
            Assert.Equal(units, observed.Budget.MaterializedStringChars);
            if (optimized)
            {
                var snapshot = diagnostics.GetSnapshot();
                Assert.Equal(1, snapshot.OptimizedLoopHits);
                Assert.Equal(0, snapshot.PlannedExpressionFallbacks);
            }
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task WideChains_ChargeWorkAndHaveSyncAsyncBudgetParity(bool falseFirstLink)
    {
        // Flat width no longer consumes AST depth, but must still consume execution work.
        var source = (falseFirstLink ? "1 < " : "") + string.Join(" <= ", Enumerable.Range(0, 20_001));
        var ast = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var sync = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var twin = await Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache());
        Assert.False(sync.Result.IsError);
        Assert.Equal($"ok raw={(falseFirstLink ? "false" : "true")} n=1", AsyncEvaluationHarness.NeutralOf(sync.Result));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync.Result), AsyncEvaluationHarness.NeutralOf(twin.Result));
        Assert.True(sync.Budget.ConsumedSteps > 1);
        Assert.Equal(sync.Budget.ConsumedSteps, twin.Budget.ConsumedSteps);
        var limit = new EvaluationLimits { MaxSteps = 1 };
        var limited = Evaluator.RunCountedObserved(ast, limits: limit);
        var limitedTwin = await Evaluator.RunCountedObservedAsync(ast, limits: limit, zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache());
        Assert.IsType<EvalError.EvaluationStepLimitExceeded>(EvaluatorTestSupport.Innermost(limited.Result.Error));
        Assert.Equal(limited.Result.Error.Code, limitedTwin.Result.Error.Code);
        Assert.Equal(limited.Budget.ConsumedSteps, limitedTwin.Budget.ConsumedSteps);
    }

    [Fact]
    public void ExpressionNameRendering_DoesNotReadLinksBeyondItsOutputBound()
    {
        foreach (var mode in new[] { ExprNameMode.Open, ExprNameMode.DiagnosticName })
        {
            var links = new BoundedReadList<ComparisonLink>(new(ComparisonOp.Lt, new Expr.Num(1)), 1_000_000, 300);
            var rendered = ExprNameRenderer.Render(new Expr.Comparison(new Expr.Num(0), links), mode);
            Assert.EndsWith(ExprNameRenderer.TruncationMarker, rendered);
            Assert.InRange(rendered.Length, 1, ExprNameRenderer.MaxRenderedNameLength + 1);
            Assert.InRange(links.Reads, 1, 300);
        }
    }

    [Fact]
    public void PlanDiagnosticRendering_DoesNotReadLinksBeyondItsOutputBound()
    {
        var expr = new Expr.Num(1);
        var constant = new LoopExprPlan.Constant(expr, PlannedLoopValue.FromResult(new Result.Atom(1)));
        var links = new BoundedReadList<LoopComparisonLink>(new(ComparisonOp.Lt, constant), 1_000_000, 300);
        var plan = new LoopExprPlan.Comparison(expr, constant, links);
        var describe = typeof(LoopOptimizer).GetMethod("DescribeLoopExprPlan", BindingFlags.Static | BindingFlags.NonPublic)!;
        var rendered = Assert.IsType<string>(describe.Invoke(null, [plan]));
        Assert.StartsWith("Compare(Const(1) LessThan Const(1)", rendered);
        Assert.EndsWith("...", rendered);
        Assert.InRange(rendered.Length, 1, 2051);
        Assert.InRange(links.Reads, 1, 300);
    }

    private sealed class BoundedReadList<T>(T item, int count, int maximumReads) : IReadOnlyList<T>
    {
        public int Count => count;
        public int Reads { get; private set; }
        public T this[int index]
        {
            get
            {
                Assert.InRange(index, 0, Count - 1);
                Assert.True(++Reads <= maximumReads, "Renderer read beyond the prefix that fits its output bound.");
                return item;
            }
        }
        public IEnumerator<T> GetEnumerator() => throw new InvalidOperationException("Indexed prefix access required.");
        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
    }
}
