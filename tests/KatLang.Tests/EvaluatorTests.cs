namespace KatLang.Tests;

public class EvaluatorTests
{
    // Must match the high-precision literals in Evaluator.MathAlgorithm.
    private const decimal KatPi = 3.1415926535897932384626433833m;
    private const decimal KatE  = 2.7182818284590452353602874714m;

    private static EvalResult<IReadOnlyList<decimal>> Eval(string source)
    {
        var ast = Parser.Parse(source).Root;
        return Evaluator.RunFlat(new Expr.Block(ast));
    }

    /// <summary>
    /// Evaluate after marking all parsed properties as public.
    /// Used by tests that need open visibility on user-defined modules
    /// (since all parsed properties default to private).
    /// </summary>
    private static EvalResult<IReadOnlyList<decimal>> EvalAllPublic(string source)
    {
        var ast = Parser.Parse(source).Root;
        return Evaluator.RunFlat(new Expr.Block(MakeAllPublic(ast)));
    }

    /// <summary>
    /// Recursively marks all properties in an algorithm tree as IsPublic = true.
    /// </summary>
    private static Algorithm MakeAllPublic(Algorithm alg) => alg switch
    {
        Algorithm.User => alg with
        {
            Properties = alg.Properties.Select(p =>
                new Property(p.Name, MakeAllPublic(p.Value), IsPublic: true, Exposure: p.Exposure)).ToList(),
            Output = alg.Output.Select(MakeAllPublicExpr).ToList(),
            Opens = alg.Opens.Select(MakeAllPublicExpr).ToList(),
        },
        _ => alg,
    };

    private static Expr MakeAllPublicExpr(Expr expr) => expr switch
    {
        Expr.Block(var a) => new Expr.Block(MakeAllPublic(a)) { Span = expr.Span },
        Expr.Call(var f, var args) => new Expr.Call(MakeAllPublicExpr(f), MakeAllPublic(args)) { Span = expr.Span },
        Expr.DotCall(var t, var n, var da) => new Expr.DotCall(
            MakeAllPublicExpr(t), n, da is not null ? MakeAllPublic(da) : null) { Span = expr.Span },
        Expr.Binary(var op, var l, var r) => new Expr.Binary(op, MakeAllPublicExpr(l), MakeAllPublicExpr(r)) { Span = expr.Span },
        Expr.Unary(var op, var o) => new Expr.Unary(op, MakeAllPublicExpr(o)) { Span = expr.Span },
        Expr.Index(var t, var s) => new Expr.Index(MakeAllPublicExpr(t), MakeAllPublicExpr(s)) { Span = expr.Span },
        Expr.Combine(var l, var r) => new Expr.Combine(MakeAllPublicExpr(l), MakeAllPublicExpr(r)) { Span = expr.Span },
        _ => expr,
    };

    private static void AssertEval(string source, params decimal[] expected)
    {
        var result = Eval(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal(expected, result.Value);
    }

    private static void AssertEvalApprox(string source, decimal expected, int precision = 10)
    {
        var result = Eval(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Single(result.Value);
        Assert.Equal(expected, result.Value[0], precision);
    }

    private static void AssertEvalAllPublic(string source, params decimal[] expected)
    {
        var result = EvalAllPublic(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal(expected, result.Value);
    }

    private static void AssertEvalFails(string source)
    {
        var result = Eval(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: [{string.Join(", ", result.Value)}]");
    }

    private static void AssertEvalFailsWithTypeMismatch(string source, string expectedSubstring)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected TypeMismatch error but got: {result.Value}");
        var error = result.Error;
        // Unwrap WithContext as needed
        while (error is EvalError.WithContext wc)
            error = wc.Inner;
        var tm = Assert.IsType<EvalError.TypeMismatch>(error);
        Assert.Contains(expectedSubstring, tm.Message);
    }

    private static void AssertEvalFailsWithIllegalInEval(string source, string expectedSubstring)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected IllegalInEval error but got: {result.Value}");
        var error = result.Error;
        while (error is EvalError.WithContext wc)
            error = wc.Inner;
        var illegal = Assert.IsType<EvalError.IllegalInEval>(error);
        Assert.Contains(expectedSubstring, illegal.Reason);
    }

    private static EvalResult<Result> EvalFull(string source)
    {
        var ast = Parser.Parse(source).Root;
        return Evaluator.Run(new Expr.Block(ast));
    }

    private static (EvalResult<Result> Result, Evaluator.MemoizationStats Stats) EvalFullWithMemoizationStats(string source)
    {
        var ast = Parser.Parse(source).Root;
        return Evaluator.RunWithMemoizationStats(new Expr.Block(ast));
    }

    private static void AssertMemoizationStats(
        Evaluator.MemoizationStats stats,
        int expectedHits,
        int expectedStores,
        int expectedMisses,
        int expectedBypasses = 0)
    {
        Assert.Equal(expectedHits, stats.PropertyCacheHitCount);
        Assert.Equal(expectedStores, stats.PropertyCacheStoreCount);
        Assert.Equal(expectedMisses, stats.PropertyCacheMissCount);
        Assert.Equal(expectedBypasses, stats.PropertyCacheBypassCount);
    }

    private static void AssertEvalString(string source, string expected)
    {
        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        var str = Assert.IsType<Result.Str>(result.Value);
        Assert.Equal(expected, str.Value);
    }

    private static void AssertEvalAllPublicFails(string source)
    {
        var result = EvalAllPublic(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: [{string.Join(", ", result.Value)}]");
    }

    private static EvalError? GetEvalError(string source)
    {
        var result = Eval(source);
        return result.IsError ? result.Error : null;
    }

    private static void AssertArityMismatchMessage(string source, string expectedMessage)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Equal(expectedMessage, formatted);
        Assert.DoesNotContain("while evaluating", formatted);
    }

    private static void AssertLocalOnlyPropertyMessage(string source, string expectedMessage)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Equal(expectedMessage, formatted);
        Assert.DoesNotContain("while evaluating", formatted);

        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;

        Assert.IsType<EvalError.LocalOnlyProperty>(error);
    }

    private static void AssertInnermostMissingOutput(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        Assert.IsType<EvalError.MissingOutput>(error);
    }

    private static void AssertInnermostSpecialOutputAccess(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        Assert.IsType<EvalError.SpecialOutputAccess>(error);
    }

    private static void AssertMissingOutputMessage(
        string source,
        string expectedMessage,
        int? expectedLine = null,
        int? expectedColumn = null)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        AssertInnermostMissingOutput(result.Error);

        var formatted = KatLangError.FromEvalError(result.Error);
        Assert.Equal(expectedMessage, formatted.Message);
        Assert.DoesNotContain("while evaluating", formatted.Message);

        if (expectedLine is not null)
            Assert.Equal(expectedLine, formatted.StartLine);
        if (expectedColumn is not null)
            Assert.Equal(expectedColumn, formatted.StartColumn);
    }

    private static void AssertFilterPredicateShapeFails(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("filter predicate must return exactly one atomic numeric value", formatted);

        var error = result.Error;
        var contexts = new List<string>();
        while (error is EvalError.WithContext wc)
        {
            contexts.Add(wc.Context);
            error = wc.Inner;
        }

        Assert.Contains(contexts, context => context.Contains("filter predicate must return exactly one atomic numeric value"));
        Assert.IsType<EvalError.BadArity>(error);
    }

    private static void AssertReduceStepShapeFails(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("reduce step must return a single accumulator value", formatted);

        var error = result.Error;
        var contexts = new List<string>();
        while (error is EvalError.WithContext wc)
        {
            contexts.Add(wc.Context);
            error = wc.Inner;
        }

        Assert.Contains(contexts, context => context.Contains("reduce step must return a single accumulator value"));
        Assert.IsType<EvalError.BadArity>(error);
    }

    private static void AssertMapTransformShapeFails(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("map transform must return a single element", formatted);

        var error = result.Error;
        var contexts = new List<string>();
        while (error is EvalError.WithContext wc)
        {
            contexts.Add(wc.Context);
            error = wc.Inner;
        }

        Assert.Contains(contexts, context => context.Contains("map transform must return a single element"));
        Assert.IsType<EvalError.BadArity>(error);
    }

    private static void AssertSumElementShapeFails(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("sum expects each collection element to be a single numeric value", formatted);

        var error = result.Error;
        var contexts = new List<string>();
        while (error is EvalError.WithContext wc)
        {
            contexts.Add(wc.Context);
            error = wc.Inner;
        }

        Assert.Contains(contexts, context => context.Contains("sum expects each collection element to be a single numeric value"));
        Assert.IsType<EvalError.BadArity>(error);
    }

    private static void AssertBuiltinFailureWithContext(string source, string expectedContext)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains(expectedContext, formatted);

        var error = result.Error;
        var contexts = new List<string>();
        while (error is EvalError.WithContext wc)
        {
            contexts.Add(wc.Context);
            error = wc.Inner;
        }

        Assert.Contains(contexts, context => context.Contains(expectedContext));
        Assert.IsType<EvalError.BadArity>(error);
    }

    [Fact]
    public void Eval_Memoizes_RepeatedEligiblePropertyWithinSingleRun()
    {
        var source = """
            Values = range(1, 5)
            Values.sum + Values.sum
            """;

        var (result, stats) = EvalFullWithMemoizationStats(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([30m], result.Value.ToAtoms());
        AssertMemoizationStats(stats, expectedHits: 1, expectedStores: 1, expectedMisses: 1);
    }

    [Fact]
    public void Eval_Memoization_Reuses_ClosedLexicalPropertyAcrossCallerContexts()
    {
        var source = """
            Values = range(1, 100)
            Square = x * x
            SquaresTotal = Values.map(Square).sum
            Values.sum ^ 2 - SquaresTotal
            """;

        var (result, stats) = EvalFullWithMemoizationStats(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([25164150m], result.Value.ToAtoms());
        Assert.True(
            stats.PropertyCacheHitCount > 0,
            $"Expected at least one memoization hit, but saw stats: {stats}");
    }

    [Fact]
        public void Eval_Memoization_Distinguishes_SamePropertyTextAcrossReceiverContexts()
    {
        var source = """
                        Left = {
                            Value = 1
                        }
                        Right = {
                            Value = 2
                        }
                        Left.Value + Left.Value + Right.Value + Right.Value
            """;

        var (result, stats) = EvalFullWithMemoizationStats(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([6m], result.Value.ToAtoms());
        AssertMemoizationStats(stats, expectedHits: 2, expectedStores: 2, expectedMisses: 2);
    }

    [Fact]
    public void Eval_Memoization_DoesNotCache_ParameterizedCallResults()
    {
        var source = """
            Inc = x + 1
            Inc(1) + Inc(2)
            """;

        var (result, stats) = EvalFullWithMemoizationStats(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([5m], result.Value.ToAtoms());
        AssertMemoizationStats(stats, expectedHits: 0, expectedStores: 0, expectedMisses: 0);
    }

    [Fact]
    public void Eval_Memoization_CacheIsIsolatedPerRun()
    {
        var source = """
            Values = range(1, 5)
            Values.sum + Values.sum
            """;

        var ast = Parser.Parse(source).Root;

        var first = Evaluator.RunWithMemoizationStats(new Expr.Block(ast));
        var second = Evaluator.RunWithMemoizationStats(new Expr.Block(ast));

        if (first.Result.IsError)
            Assert.Fail($"Expected first run success but got error: {first.Result.Error}");
        if (second.Result.IsError)
            Assert.Fail($"Expected second run success but got error: {second.Result.Error}");

        Assert.Equal(first.Result.Value.ToAtoms(), second.Result.Value.ToAtoms());
        AssertMemoizationStats(first.Stats, expectedHits: 1, expectedStores: 1, expectedMisses: 1);
        AssertMemoizationStats(second.Stats, expectedHits: 1, expectedStores: 1, expectedMisses: 1);
    }

    [Fact]
    public void Eval_Memoization_PreservesRecursivePropertyBehavior()
    {
        var source = """
            Recursive = {
              Step = if(n == 0, 0, Step(n - 1))
              Step(4)
            }
            Recursive + Recursive
            """;

        var (result, stats) = EvalFullWithMemoizationStats(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([0m], result.Value.ToAtoms());
        AssertMemoizationStats(stats, expectedHits: 1, expectedStores: 1, expectedMisses: 1);
    }

    [Fact]
    public void Eval_Memoization_Distinguishes_HigherOrderAlgorithmContexts()
    {
        var source = """
                        Left = {
                            Step = x + 1
                            Value = Step(10)
            }
                        Right = {
                            Step = x + 2
                            Value = Step(10)
                        }
                        Left.Value + Left.Value + Right.Value + Right.Value
            """;

        var (result, stats) = EvalFullWithMemoizationStats(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([46m], result.Value.ToAtoms());
        AssertMemoizationStats(stats, expectedHits: 2, expectedStores: 2, expectedMisses: 2);
    }

    [Fact]
    public void Eval_Memoization_Distinguishes_SameLexicalPropertyTextAcrossNestedBindings()
    {
        var source = """
            Outer = {
                Left = {
                    Value = 10
                    Value + Value
                }
                Right = {
                    Value = 20
                    Value + Value
                }
                Left + Right
            }
            Outer
            """;

        var (result, stats) = EvalFullWithMemoizationStats(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([60m], result.Value.ToAtoms());
        AssertMemoizationStats(stats, expectedHits: 2, expectedStores: 5, expectedMisses: 5);
    }

    [Fact]
    public void Eval_Memoization_Keeps_CallerBoundZeroParamLexicalPropertyOnContextualKey()
    {
        var shared = new Property(
            "Shared",
            new Algorithm.User(
                Parent: null,
                Params: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Param("x")]));

        var caller = new Property(
            "Caller",
            new Algorithm.User(
                Parent: null,
                Params: ["x"],
                Opens: [],
                Properties: [shared],
                Output:
                [
                    new Expr.Binary(
                        BinaryOp.Add,
                        new Expr.Resolve("Shared"),
                        new Expr.Resolve("Shared"))
                ]));

        var oneArg = new Algorithm.User(
            Parent: null,
            Params: [],
            Opens: [],
            Properties: [],
            Output: [new Expr.Num(1)]);

        var twoArg = new Algorithm.User(
            Parent: null,
            Params: [],
            Opens: [],
            Properties: [],
            Output: [new Expr.Num(2)]);

        var root = new Algorithm.User(
            Parent: null,
            Params: [],
            Opens: [],
            Properties: [caller],
            Output:
            [
                new Expr.Binary(
                    BinaryOp.Add,
                    new Expr.Call(new Expr.Resolve("Caller"), oneArg),
                    new Expr.Call(new Expr.Resolve("Caller"), twoArg))
            ]);

        var (result, stats) = Evaluator.RunWithMemoizationStats(new Expr.Block(root));
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([6m], result.Value.ToAtoms());
        AssertMemoizationStats(stats, expectedHits: 2, expectedStores: 2, expectedMisses: 2);
    }

    [Fact]
    public void Eval_Memoization_SharedBindingAcrossDefinitionScopes_DoesNotContaminateOpenDependentMeaning()
    {
        var sharedClosedBinding = new Property(
            "Shared",
            new Algorithm.User(
                Parent: null,
                Params: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Resolve("Base")])) ;

        var localBaseBinding = new Property(
            "Base",
            new Algorithm.User(
                Parent: null,
                Params: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Num(1)]));

        var openBaseBinding = new Property(
            "Base",
            new Algorithm.User(
                Parent: null,
                Params: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Num(2)]),
            IsPublic: true);

        var libraryBinding = new Property(
            "Lib",
            new Algorithm.User(
                Parent: null,
                Params: [],
                Opens: [],
                Properties: [openBaseBinding],
                Output: []),
            IsPublic: true);

        var structuralWrapperBinding = new Property(
            "StructuralWrapper",
            new Algorithm.User(
                Parent: null,
                Params: [],
                Opens: [],
                Properties: [localBaseBinding, sharedClosedBinding],
                Output:
                [
                    new Expr.Binary(
                        BinaryOp.Add,
                        new Expr.Resolve("Shared"),
                        new Expr.Resolve("Shared"))
                ]));

        var openWrapperBinding = new Property(
            "OpenWrapper",
            new Algorithm.User(
                Parent: null,
                Params: [],
                Opens: [new Expr.Resolve("Lib")],
                Properties: [sharedClosedBinding],
                Output:
                [
                    new Expr.Binary(
                        BinaryOp.Add,
                        new Expr.Resolve("Shared"),
                        new Expr.Resolve("Shared"))
                ]));

        var root = new Algorithm.User(
            Parent: null,
            Params: [],
            Opens: [],
            Properties: [libraryBinding, structuralWrapperBinding, openWrapperBinding],
            Output:
            [
                new Expr.Binary(
                    BinaryOp.Add,
                    new Expr.Resolve("StructuralWrapper"),
                    new Expr.Resolve("OpenWrapper"))
            ]);

        var (result, stats) = Evaluator.RunWithMemoizationStats(new Expr.Block(root));
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal(
            [6m],
            result.Value.ToAtoms());
        Assert.True(
            stats.PropertyCacheHitCount >= 2,
            $"Expected memoization to remain active within each wrapper without cross-scope contamination, but saw stats: {stats}");
    }

    // â”€â”€ Numbers â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Number_ReturnsValue()
        => AssertEval("42", 42);

    [Fact]
    public void Eval_NegativeNumber_ReturnsNegatedValue()
        => AssertEval("-5", -5);

    [Fact]
    public void Eval_DoubleNegative_ReturnsPositive()
        => AssertEval("--5", 5);

    [Fact]
    public void Eval_Zero_ReturnsZero()
        => AssertEval("0", 0);

    [Fact]
    public void Eval_LargeNumber_ReturnsCorrectValue()
        => AssertEval("9876543210", 9876543210.0m);

    [Fact]
    public void Eval_FloatingPoint_ReturnsValue()
        => AssertEval("3.14", 3.14m);

    [Fact]
    public void Eval_FloatingPoint_Arithmetic()
    {
        AssertEval("1.5 + 2.5", 4.0m);
        AssertEval("3.0 * 2.5", 7.5m);
    }

    // â”€â”€ Arithmetic â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Addition_ReturnsSum()
        => AssertEval("1 + 2", 3);

    [Fact]
    public void Eval_Subtraction_ReturnsDifference()
        => AssertEval("5 - 3", 2);

    [Fact]
    public void Eval_Multiplication_ReturnsProduct()
        => AssertEval("4 * 3", 12);

    [Fact]
    public void Eval_ChainedAddition_LeftAssociative()
        => AssertEval("10 - 3 - 2", 5);

    [Fact]
    public void Eval_MixedOperations_CorrectPrecedence()
        => AssertEval("1 + 2 * 3", 7);

    [Fact]
    public void Eval_ParenthesesOverridePrecedence()
        => AssertEval("(1 + 2) * 3", 9);

    [Fact]
    public void Eval_ComplexArithmetic()
        => AssertEval("5 * 3 - 2", 13);

    [Fact]
    public void Eval_BinaryMinusWithUnaryMinus()
        => AssertEval("5 - -3", 8);

    [Fact]
    public void Eval_NegativeResult()
        => AssertEval("3 - 10", -7);

    // â”€â”€ Comparisons â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_LessThan_True_Returns1()
        => AssertEval("3 < 5", 1);

    [Fact]
    public void Eval_LessThan_False_Returns0()
        => AssertEval("5 < 3", 0);

    [Fact]
    public void Eval_LessThan_Equal_Returns0()
        => AssertEval("3 < 3", 0);

    [Fact]
    public void Eval_GreaterThan_True_Returns1()
        => AssertEval("5 > 3", 1);

    [Fact]
    public void Eval_GreaterThan_False_Returns0()
        => AssertEval("3 > 5", 0);

    [Fact]
    public void Eval_GreaterThan_Equal_Returns0()
        => AssertEval("3 > 3", 0);

    // â”€â”€ Output lists â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_CommaList_ReturnsMultipleValues()
        => AssertEval("1, 2, 3", 1, 2, 3);

    [Fact]
    public void Eval_CommaListWithExpressions()
        => AssertEval("1 + 1, 2 * 2, 3 - 1", 2, 4, 2);

    // â”€â”€ Indexing â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Index_ReturnsElement()
        => AssertEval("(1, 2, 3):1", 2);

    [Fact]
    public void Eval_Index_FirstElement()
        => AssertEval("(1, 2, 3):0", 1);

    [Fact]
    public void Eval_Index_LastElement()
        => AssertEval("(1, 2, 3):2", 3);

    [Fact]
    public void Eval_Index_OutOfBounds_Fails()
        => AssertEvalFails("(1, 2, 3):5");

    [Fact]
    public void Eval_Index_NegativeIndex_Fails()
    {
        var source = """
            X = 1, 2, 3
            i = 0 - 1
            X:i
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_Index_SingleAtom()
        => AssertEval("5:0", 5);

    [Fact]
    public void Eval_Index_ChainedIndex()
        => AssertEval("((1, 2), (3, 4)):1:0", 3);

    // â”€â”€ Properties â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Property_ReturnsValue()
    {
        var source = """
            X = 5
            X
            """;
        AssertEval(source, 5);
    }

    [Fact]
    public void Eval_Property_WithExpression()
    {
        var source = """
            X = 2 + 3
            X
            """;
        AssertEval(source, 5);
    }

    [Fact]
    public void Eval_Property_MultipleOutputs()
    {
        var source = """
            X = 1, 2, 3
            X
            """;
        AssertEval(source, 1, 2, 3);
    }

    [Fact]
    public void Eval_Property_ReferenceAnother()
    {
        var source = """
            A = 5
            B = A + 1
            B
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_PropertyAccess_Length()
    {
        var source = """
            X = 1, 2, 3
            X.length
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_PropertyAccess_LengthSingle()
    {
        var source = """
            X = 5
            X.length
            """;
        AssertEval(source, 1);
    }

    // ── string intrinsic tests ──────────────────────────────────────────

    [Fact]
    public void Eval_StringIntrinsic_SimpleInteger()
    {
        // 123.string → "123"
        AssertEvalString("123.string", "123");
    }

    [Fact]
    public void Eval_StringIntrinsic_Zero()
    {
        // 0.string → "0"
        AssertEvalString("0.string", "0");
    }

    [Fact]
    public void Eval_StringIntrinsic_NegativeNumber()
    {
        // (-5).string → "-5"
        AssertEvalString("(-5).string", "-5");
    }

    [Fact]
    public void Eval_StringIntrinsic_Decimal()
    {
        // 1.20.string → "1.20"
        // Canonical representation preserves decimal trailing zeros (C# decimal behavior)
        AssertEvalString("1.20.string", "1.20");
    }

    [Fact]
    public void Eval_StringIntrinsic_PropertyBound()
    {
        // A = 123; A.string → "123"
        var source = """
            A = 123
            A.string
            """;
        AssertEvalString(source, "123");
    }

    [Fact]
    public void Eval_StringIntrinsic_ReturnsRealStringValue()
    {
        // Result must be a first-class string value usable in equality comparison
        var source = """
            A = 123
            A.string == '123'
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_StringIntrinsic_WorksThroughDotCallPath()
    {
        // Works through ordinary dot-call builtin-property path, analogous to length
        var source = """
            X = 42
            X.string
            """;
        AssertEvalString(source, "42");
    }

    [Fact]
    public void Eval_StringIntrinsic_OnStringValue_Fails()
    {
        // Applying .string to a string value should fail with typeMismatch
        AssertEvalFailsWithTypeMismatch("'hello'.string", "numeric receiver");
    }

    [Fact]
    public void Eval_StringIntrinsic_OnMultiOutput_Fails()
    {
        // Applying .string to a multi-output value should fail
        var source = """
            X = 1, 2
            X.string
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_StringIntrinsic_ExpressionResult()
    {
        // Works on computed expression results
        var source = """
            A = 10 + 5
            A.string
            """;
        AssertEvalString(source, "15");
    }

    [Fact]
    public void Eval_PropertyAccess_SubProperty()
    {
        var source = """
            X = (Y = 42
            Y)
            X.Y
            """;
        AssertEval(source, 42);
    }

    // â”€â”€ Blocks â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Block_ReturnsOutput()
        => AssertEval("{1 + 2}", 3);

    [Fact]
    public void Eval_InlineBlock_ReturnsOutput()
        => AssertEval("(1, 2, 3)", 1, 2, 3);

    // â”€â”€ If builtin â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_If_TrueCondition_ReturnsThenBranch()
        => AssertEval("if(1, (10), (20))", 10);

    [Fact]
    public void Eval_If_FalseCondition_ReturnsElseBranch()
        => AssertEval("if(0, (10), (20))", 20);

    [Fact]
    public void Eval_If_NonZeroCondition_ReturnsThenBranch()
        => AssertEval("if(5, (10), (20))", 10);

    [Fact]
    public void Eval_If_NegativeCondition_ReturnsThenBranch()
        => AssertEval("if(-1, (10), (20))", 10);

    [Fact]
    public void Eval_If_WithExpressions()
        => AssertEval("if(3 > 2, (100), (200))", 100);

    [Fact]
    public void Eval_If_MultipleOutputs()
        => AssertEval("if(1, (1, 2), (3, 4))", 1, 2);

    // â”€â”€ Repeat builtin â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Repeat_SingleParam()
        => AssertEval("repeat({x + 1}, (3), (0))", 3);

    [Fact]
    public void Eval_Repeat_ZeroIterations()
        => AssertEval("repeat({x + 1}, (0), (5))", 5);

    [Fact]
    public void Eval_Repeat_MultipleParams()
        => AssertEval("repeat({a + 1, b + a}, (3), (0, 0))", 3, 3);

    [Fact]
    public void Eval_Repeat_NegativeCount_Fails()
        => AssertEvalFails("repeat({x}, (-1), (0))");

    [Fact]
    public void Eval_Repeat_Factorial()
        => AssertEval("repeat({n + 1, acc * n}, (5), (1, 1)):1", 120);

    // â”€â”€ While builtin â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_While_CountDown()
        => AssertEval("while({x - 1, x - 1}, (3))", 1);

    [Fact]
    public void Eval_While_EvenFibonacciSum()
    {
        // Sums even Fibonacci numbers <= 100: 2 + 8 + 34 = 44.
        // Grace (~a) reorders detected params [b, a, total] -> [a, b, total].
        // Initial state (1, 2, 0): a=1, b=2, total=0.
        // The step with b=144 (first even Fibonacci > 100) triggers cont=0;
        // pre-check semantics return the prior state (total=44), not the updated one.
        var source = """
            Algo = b, ~a + b, total + if(b mod 2 == 0, b, 0), b <= 100
            Sum = Algo.while((1, 2, 0)) : 2
            Sum
            """;
        AssertEval(source, 44);
    }

    [Fact]
    public void Eval_While_ImmediateExit()
        => AssertEval("while({x, 0}, (5))", 5);

    [Fact]
    public void Eval_While_DotCall_SumMultiplesOf3Or5()
    {
        var source = """
            Algo = n - 1, result + if(n mod 3==0 or n mod 5==0, n, 0), n > 2
            Init = x, 0
            Sum = Algo.while(Init(x)) : 1
            Sum(999)
            """;
        AssertEval(source, 233168);
    }

    // ── While/repeat dotCall multi-item init lowering ──────────────────────────────────

    [Fact]
    public void Eval_While_DotCall_BareComma_Works()
    {
        // Algo.while(x, 0) with bare comma: evaluator packages multi-item init
        var source = """
            Algo = n - 1, result + if(n mod 3==0 or n mod 5==0, n, 0), n > 2
            Sum = Algo.while(x, 0) : 1
            Sum(999)
            """;
        AssertEval(source, 233168);
    }

    [Fact]
    public void Eval_While_DotCall_ParenGroupedInit()
    {
        // Algo.while((x, 0)): (x, 0) is ordinary grouping producing a block ─
        // single arg, no packaging needed, works as before
        var source = """
            Algo = n - 1, result + if(n mod 3==0 or n mod 5==0, n, 0), n > 2
            Sum = Algo.while((x, 0)) : 1
            Sum(999)
            """;
        AssertEval(source, 233168);
    }

    [Fact]
    public void Eval_While_DotCall_ExistingInit_StillWorks()
    {
        // Init(x) as single arg still works
        var source = """
            Algo = n - 1, result + if(n mod 3==0 or n mod 5==0, n, 0), n > 2
            Init = x, 0
            Sum = Algo.while(Init(x)) : 1
            Sum(999)
            """;
        AssertEval(source, 233168);
    }

    [Fact]
    public void Eval_While_DotCall_ParenGroupedInit_NoParams()
    {
        // x inside (x, 0) resolves from the enclosing algorithm's scope
        var source = """
            Algo = n - 1, result + if(n mod 3==0 or n mod 5==0, n, 0), n > 2
            Sum = Algo.while((x, 0)) : 1
            Sum(999)
            """;
        AssertEval(source, 233168);
    }

    // â”€â”€ Atoms builtin â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_While_DirectCall_MultiInit()
    {
        // while(Step, s1, s2, ...) lowers to while(Step, block([s1, s2, ...]))
        var source = """
            Step = n - 1, acc + n, n > 1
            while(Step, 5, 0) : 1
            """;
        // 5+4+3+2 = 14 (stops when n=1, cont=0, returns prior state)
        AssertEval(source, 14);
    }

    [Fact]
    public void Eval_Repeat_DirectCall_MultiInit()
    {
        // repeat(Step, n, s1, s2) lowers to repeat(Step, n, block([s1, s2]))
        var source = """
            Step = a + 1, b + a
            repeat(Step, 3, 0, 0)
            """;
        AssertEval(source, 3, 3);
    }

    [Fact]
    public void Eval_Repeat_DotCall_MultiInit()
    {
        // Step.repeat(n, s1, s2) fallback packages to repeat(Step, n, block([s1, s2]))
        var source = """
            Step = a + 1, b + a
            Step.repeat(3, 0, 0)
            """;
        AssertEval(source, 3, 3);
    }

    [Fact]
    public void Eval_While_DotCall_SingleInit_StillWorks()
    {
        var source = """
            Step = x - 1, x - 1
            Step.while(3)
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Repeat_DotCall_SingleInit_StillWorks()
    {
        var source = """
            Step = x + 1
            Step.repeat(3, 0)
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_While_DirectCall_SingleInit_StillWorks()
        => AssertEval("while({x - 1, x - 1}, 3)", 1);

    [Fact]
    public void Eval_Repeat_DirectCall_SingleInit_StillWorks()
        => AssertEval("repeat({x + 1}, 3, 0)", 3);

    [Fact]
    public void Eval_DotCall_TrailingBrace_StillWorks()
    {
        var source = """
            F = x + 1
            F{3}
            """;
        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_DotCall_PropertyPrecedence_WhileShadow()
    {
        // If algorithm A has a real property named while, dotCall must
        // resolve as property call, not lexical builtin fallback packaging
        var source = """
            A = {
                while = x + 1
            }
            A.while(10)
            """;
        AssertEval(source, 11);
    }

    [Fact]
    public void Eval_DotCall_PropertyPrecedence_RepeatShadow()
    {
        var source = """
            A = {
                repeat = x * 2
            }
            A.repeat(5)
            """;
        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_While_DotCall_NoArgs_Fails()
    {
        var source = """
            Step = x - 1, x > 0
            Step.while()
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_Repeat_DotCall_NoArgs_Fails()
    {
        var source = """
            Step = x + 1
            Step.repeat()
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_Repeat_DotCall_OneArg_Fails()
    {
        var source = """
            Step = x + 1
            Step.repeat(3)
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_ParenSubExpr_FirstArg_Works()
    {
        var source = """
            F = a + b
            F((1 + 2) mod 2, 10)
            """;
        AssertEval(source, 11);
    }

    [Fact]
    public void Eval_If_ParenSubExpr_FirstArg_Works()
        => AssertEval("if((1 + 2) mod 2 == 0, 1, 0)", 0);

    [Fact]
    public void Eval_DoubleParens_IsOrdinaryGrouping()
    {
        var source = """
            X = ((1 + 2))
            X
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Atoms_FlattensGroups()
        => AssertEval("atoms(((1, 2), (3, 4)))", 1, 2, 3, 4);

    [Fact]
    public void Eval_Atoms_SingleValue()
        => AssertEval("atoms((5))", 5);

    // ── Range builtin ────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Range_AscendingInclusive()
        => AssertEval("range(1, 10)", 1, 2, 3, 4, 5, 6, 7, 8, 9, 10);

    [Fact]
    public void Eval_Range_DescendingInclusive()
        => AssertEval("range(10, 1)", 10, 9, 8, 7, 6, 5, 4, 3, 2, 1);

    [Fact]
    public void Eval_Range_SingletonWhenEqual()
        => AssertEval("range(5, 5)", 5);

    [Fact]
    public void Eval_Range_NegativeToPositive()
        => AssertEval("range(-2, 2)", -2, -1, 0, 1, 2);

    [Fact]
    public void Eval_Range_NonIntegerStart_Fails()
        => AssertEvalFailsWithIllegalInEval("range(1.5, 5)", "range start must be an integer");

    [Fact]
    public void Eval_Range_NonIntegerStop_Fails()
        => AssertEvalFailsWithIllegalInEval("range(1, 5.2)", "range stop must be an integer");

    [Fact]
    public void Eval_Range_Combine_PreservesOrdering()
        => AssertEval("range(3, 1); 0", 3, 2, 1, 0);

    // ── Filter builtin ───────────────────────────────────────────────────────

    [Fact]
    public void Eval_Filter_AscendingRange_KeepsMatchingItems()
    {
        var source = """
            IsEven = x mod 2 == 0
            filter(range(1, 10), IsEven)
            """;
        AssertEval(source, 2, 4, 6, 8, 10);
    }

    [Fact]
    public void Eval_Filter_DescendingRange_PreservesOriginalOrder()
    {
        var source = """
            IsEven = x mod 2 == 0
            filter(range(10, 1), IsEven)
            """;
        AssertEval(source, 10, 8, 6, 4, 2);
    }

    [Fact]
    public void Eval_Filter_AllTrue_ReturnsSameCollection()
    {
        var source = """
            IsPositive = x > 0
            filter(range(1, 4), IsPositive)
            """;
        AssertEval(source, 1, 2, 3, 4);
    }

    [Fact]
    public void Eval_Filter_AllFalse_ReturnsEmptyCollection()
    {
        var source = """
            IsNegative = x < 0
            filter(range(1, 4), IsNegative)
            """;
        AssertEval(source);
    }

    [Fact]
    public void Eval_Filter_EmptyCollection_ReturnsEmptyCollection()
    {
        var source = """
            IsEven = x mod 2 == 0
            IsNegative = x < 0
            range(1, 4).filter(IsNegative).filter(IsEven)
            """;
        AssertEval(source);
    }

    [Fact]
    public void Eval_Filter_GroupedElements_ArePreservedWhole()
    {
        var source = """
            KeepPair = pair:0 mod 2 == 0
            filter(((1, 10), (2, 20), (3, 30), (4, 40)), KeepPair)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var outer = Assert.IsType<Result.Group>(result.Value);
        Assert.Collection(
            outer.Items,
            first =>
            {
                var pair = Assert.IsType<Result.Group>(first);
                Assert.Collection(
                    pair.Items,
                    a => Assert.Equal(2m, Assert.IsType<Result.Atom>(a).Value),
                    b => Assert.Equal(20m, Assert.IsType<Result.Atom>(b).Value));
            },
            second =>
            {
                var pair = Assert.IsType<Result.Group>(second);
                Assert.Collection(
                    pair.Items,
                    a => Assert.Equal(4m, Assert.IsType<Result.Atom>(a).Value),
                    b => Assert.Equal(40m, Assert.IsType<Result.Atom>(b).Value));
            });
    }

    [Fact]
    public void Eval_Filter_MultiOutputFalseLikePredicate_FailsWithContext()
    {
        var source = """
            Bad(x) = 0, 999
            filter(range(1, 3), Bad)
            """;

        AssertFilterPredicateShapeFails(source);
    }

    [Fact]
    public void Eval_Filter_MultiOutputTrueLikePredicate_FailsWithContext()
    {
        var source = """
            Bad(x) = 5, 0
            filter(range(1, 3), Bad)
            """;

        AssertFilterPredicateShapeFails(source);
    }

    [Fact]
    public void Eval_Filter_GroupedPredicateResult_FailsWithContext()
    {
        var source = """
            Bad(x) = (1, 0)
            filter(range(1, 3), Bad)
            """;

        AssertFilterPredicateShapeFails(source);
    }

    [Fact]
    public void Eval_Filter_EmptyPredicateResult_FailsWithContext()
    {
        var source = """
            IsNegative = y < 0
            Bad(x) = range(1, 3).filter(IsNegative)
            filter(range(1, 3), Bad)
            """;

        AssertFilterPredicateShapeFails(source);
    }

    [Fact]
    public void Eval_Filter_StringPredicateResult_FailsWithContext()
    {
        var source = """
            Bad(x) = x.string
            filter(range(1, 3), Bad)
            """;

        AssertFilterPredicateShapeFails(source);
    }

    [Fact]
    public void Eval_Filter_ArityMismatch_FollowsBuiltinConvention()
    {
        var result = EvalFull("filter(range(1, 3))");
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var error = result.Error;
        var contexts = new List<string>();
        while (error is EvalError.WithContext wc)
        {
            contexts.Add(wc.Context);
            error = wc.Inner;
        }

        Assert.Contains(contexts, context => context.Contains("expected 2 arguments"));
        Assert.IsType<EvalError.ArityMismatch>(error);
    }

    // ── Map builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Map_DotCall_DoublesEachElement()
    {
        var source = """
            Double = x * 2
            range(1, 5).map(Double)
            """;

        AssertEval(source, 2, 4, 6, 8, 10);
    }

    [Fact]
    public void Eval_Map_OrdinaryBuiltinCall_SquaresEachElement()
    {
        var source = """
            Square = x * x
            map(range(1, 5), Square)
            """;

        AssertEval(source, 1, 4, 9, 16, 25);
    }

    [Fact]
    public void Eval_Map_PreservesOriginalOrder()
    {
        var source = """
            Tag = x * 10 + 1
            map(range(5, 1), Tag)
            """;

        AssertEval(source, 51, 41, 31, 21, 11);
    }

    [Fact]
    public void Eval_Map_EmptyCollection_ReturnsEmptyCollection()
    {
        var source = """
            Double = x * 2
            IsNegative = x < 0
            map(range(1, 4).filter(IsNegative), Double)
            """;

        AssertEval(source);
    }

    [Fact]
    public void Eval_Map_GroupedElements_ArePassedWhole()
    {
        var source = """
            TakeValue = pair:1
            map(((1, 10), (2, 20), (3, 30)), TakeValue)
            """;

        AssertEval(source, 10, 20, 30);
    }

    [Fact]
    public void Eval_Map_GroupedTransformResult_IsAccepted()
    {
        var source = """
            PairWithSquare(x) = (x, x * x)
            range(1, 3).map(PairWithSquare)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var outer = Assert.IsType<Result.Group>(result.Value);
        Assert.Collection(
            outer.Items,
            first =>
            {
                var pair = Assert.IsType<Result.Group>(first);
                Assert.Collection(
                    pair.Items,
                    a => Assert.Equal(1m, Assert.IsType<Result.Atom>(a).Value),
                    b => Assert.Equal(1m, Assert.IsType<Result.Atom>(b).Value));
            },
            second =>
            {
                var pair = Assert.IsType<Result.Group>(second);
                Assert.Collection(
                    pair.Items,
                    a => Assert.Equal(2m, Assert.IsType<Result.Atom>(a).Value),
                    b => Assert.Equal(4m, Assert.IsType<Result.Atom>(b).Value));
            },
            third =>
            {
                var pair = Assert.IsType<Result.Group>(third);
                Assert.Collection(
                    pair.Items,
                    a => Assert.Equal(3m, Assert.IsType<Result.Atom>(a).Value),
                    b => Assert.Equal(9m, Assert.IsType<Result.Atom>(b).Value));
            });
    }

    [Fact]
    public void Eval_Map_EmptyTransformResult_FailsWithContext()
    {
        var source = """
            IsNegative = y < 0
            Bad(x) = range(1, 3).filter(IsNegative)
            range(1, 3).map(Bad)
            """;

        AssertMapTransformShapeFails(source);
    }

    [Fact]
    public void Eval_Map_MultiOutputTransformResult_FailsWithContext()
    {
        var source = """
            Bad(x) = x, x * x
            range(1, 3).map(Bad)
            """;

        AssertMapTransformShapeFails(source);
    }

    // ── Count builtin ────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Count_OrdinaryBuiltinCall_CountsAscendingRange()
        => AssertEval("count(range(1, 5))", 5);

    [Fact]
    public void Eval_Count_DotCall_CountsAscendingRange()
        => AssertEval("range(1, 5).count", 5);

    [Fact]
    public void Eval_Count_DescendingRange_ReturnsElementCount()
        => AssertEval("count(range(5, 1))", 5);

    [Fact]
    public void Eval_Count_FilterComposition_ReturnsKeptCount()
    {
        var source = """
            IsEven = x mod 2 == 0
            range(1, 10).filter(IsEven).count
            """;

        AssertEval(source, 5);
    }

    [Fact]
    public void Eval_Count_MapComposition_ReturnsMappedCount()
    {
        var source = """
            Square = x * x
            range(1, 4).map(Square).count
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Count_EmptyCollection_ReturnsZero()
    {
        var source = """
            IsNegative = x < 0
            count(range(1, 4).filter(IsNegative))
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_Count_GroupedElements_CountsTopLevelGroups()
        => AssertEval("count(((1, 2), (3, 4)))", 2);

    [Fact]
    public void Eval_Count_SingleAtomicInput_ReturnsOne()
        => AssertEval("count(5)", 1);

    [Fact]
    public void Eval_Count_StringInput_ReturnsOne()
        => AssertEval("count('hello')", 1);

    // ── Min builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Min_OrdinaryBuiltinCall_FindsAscendingRangeMinimum()
        => AssertEval("min(range(1, 5))", 1);

    [Fact]
    public void Eval_Min_DotCall_FindsAscendingRangeMinimum()
        => AssertEval("range(1, 5).min", 1);

    [Fact]
    public void Eval_Min_DescendingRange_ReturnsLowestValue()
        => AssertEval("min(range(5, 1))", 1);

    [Fact]
    public void Eval_Min_FilterComposition_ReturnsKeptMinimum()
    {
        var source = """
            IsEven = x mod 2 == 0
            range(1, 10).filter(IsEven).min
            """;

        AssertEval(source, 2);
    }

    [Fact]
    public void Eval_Min_MapComposition_ReturnsMappedMinimum()
    {
        var source = """
            Negate = -x
            range(1, 4).map(Negate).min
            """;

        AssertEval(source, -4);
    }

    [Fact]
    public void Eval_Min_EmptyCollection_FailsWithContext()
    {
        var source = """
            IsNegative = x < 0
            min(range(1, 4).filter(IsNegative))
            """;

        AssertBuiltinFailureWithContext(source, "min requires a non-empty collection");
    }

    [Fact]
    public void Eval_Min_SingleAtomicInput_ReturnsSameValue()
        => AssertEval("min(5)", 5);

    [Fact]
    public void Eval_Min_GroupedElements_FailWithContext()
        => AssertBuiltinFailureWithContext("min(((1, 2), (3, 4)))", "min expects each collection element to be a single numeric value");

    [Fact]
    public void Eval_Min_StringElement_FailsWithContext()
        => AssertBuiltinFailureWithContext("min('hello')", "min expects each collection element to be a single numeric value");

    // ── Max builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Max_OrdinaryBuiltinCall_FindsAscendingRangeMaximum()
        => AssertEval("max(range(1, 5))", 5);

    [Fact]
    public void Eval_Max_DotCall_FindsAscendingRangeMaximum()
        => AssertEval("range(1, 5).max", 5);

    [Fact]
    public void Eval_Max_DescendingRange_ReturnsHighestValue()
        => AssertEval("max(range(5, 1))", 5);

    [Fact]
    public void Eval_Max_FilterComposition_ReturnsKeptMaximum()
    {
        var source = """
            IsEven = x mod 2 == 0
            range(1, 10).filter(IsEven).max
            """;

        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Max_MapComposition_ReturnsMappedMaximum()
    {
        var source = """
            Negate = -x
            range(1, 4).map(Negate).max
            """;

        AssertEval(source, -1);
    }

    [Fact]
    public void Eval_Max_EmptyCollection_FailsWithContext()
    {
        var source = """
            IsNegative = x < 0
            max(range(1, 4).filter(IsNegative))
            """;

        AssertBuiltinFailureWithContext(source, "max requires a non-empty collection");
    }

    [Fact]
    public void Eval_Max_SingleAtomicInput_ReturnsSameValue()
        => AssertEval("max(5)", 5);

    [Fact]
    public void Eval_Max_GroupedElements_FailWithContext()
        => AssertBuiltinFailureWithContext("max(((1, 2), (3, 4)))", "max expects each collection element to be a single numeric value");

    [Fact]
    public void Eval_Max_StringElement_FailsWithContext()
        => AssertBuiltinFailureWithContext("max('hello')", "max expects each collection element to be a single numeric value");

    // ── Sum builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Sum_OrdinaryBuiltinCall_AddsAscendingRange()
        => AssertEval("sum(range(1, 5))", 15);

    [Fact]
    public void Eval_Sum_DotCall_AddsAscendingRange()
        => AssertEval("range(1, 5).sum", 15);

    [Fact]
    public void Eval_Sum_DescendingRange_ReturnsTotal()
        => AssertEval("sum(range(5, 1))", 15);

    [Fact]
    public void Eval_Sum_FilterComposition_ReturnsTotal()
    {
        var source = """
            IsEven = x mod 2 == 0
            range(1, 10).filter(IsEven).sum
            """;

        AssertEval(source, 30);
    }

    [Fact]
    public void Eval_Sum_MapComposition_ReturnsTotal()
    {
        var source = """
            Square = x * x
            range(1, 4).map(Square).sum
            """;

        AssertEval(source, 30);
    }

    [Fact]
    public void Eval_Sum_EmptyCollection_ReturnsZero()
    {
        var source = """
            IsNegative = x < 0
            sum(range(1, 4).filter(IsNegative))
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_Sum_SingleAtomicInput_ReturnsSameValue()
        => AssertEval("sum(5)", 5);

    [Fact]
    public void Eval_Sum_GroupedElements_FailWithContext()
        => AssertSumElementShapeFails("sum(((1, 2), (3, 4)))");

    [Fact]
    public void Eval_Sum_StringElement_FailsWithContext()
        => AssertSumElementShapeFails("sum('hello')");

    // ── Avg builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Avg_OrdinaryBuiltinCall_FindsAscendingRangeMean()
        => AssertEval("avg(range(1, 5))", 3);

    [Fact]
    public void Eval_Avg_DotCall_FindsAscendingRangeMean()
        => AssertEval("range(1, 5).avg", 3);

    [Fact]
    public void Eval_Avg_DescendingRange_ReturnsMean()
        => AssertEval("avg(range(5, 1))", 3);

    [Fact]
    public void Eval_Avg_FilterComposition_ReturnsKeptMean()
    {
        var source = """
            IsEven = x mod 2 == 0
            range(1, 10).filter(IsEven).avg
            """;

        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_Avg_MapComposition_ReturnsFractionalMean()
    {
        var source = """
            Square = x * x
            range(1, 4).map(Square).avg
            """;

        AssertEval(source, 7.5m);
    }

    [Fact]
    public void Eval_Avg_EmptyCollection_FailsWithContext()
    {
        var source = """
            IsNegative = x < 0
            avg(range(1, 4).filter(IsNegative))
            """;

        AssertBuiltinFailureWithContext(source, "avg requires a non-empty collection");
    }

    [Fact]
    public void Eval_Avg_SingleAtomicInput_ReturnsSameValue()
        => AssertEval("avg(5)", 5);

    [Fact]
    public void Eval_Avg_GroupedElements_FailWithContext()
        => AssertBuiltinFailureWithContext("avg(((1, 2), (3, 4)))", "avg expects each collection element to be a single numeric value");

    [Fact]
    public void Eval_Avg_StringElement_FailsWithContext()
        => AssertBuiltinFailureWithContext("avg('hello')", "avg expects each collection element to be a single numeric value");

    // ── Reduce builtin ───────────────────────────────────────────────────────

    [Fact]
    public void Eval_Reduce_DotCall_AddsLeftToRight()
    {
        var source = """
            Add = x + total
            range(1, 5).reduce(Add, 0)
            """;

        AssertEval(source, 15);
    }

    [Fact]
    public void Eval_Reduce_OrdinaryBuiltinCall_Multiplies()
    {
        var source = """
            Mul = x * total
            reduce(range(1, 4), Mul, 1)
            """;

        AssertEval(source, 24);
    }

    [Fact]
    public void Eval_Reduce_IsLeftToRight()
    {
        var source = """
            Digits = x + acc * 10
            range(1, 4).reduce(Digits, 0)
            """;

        AssertEval(source, 1234);
    }

    [Fact]
    public void Eval_Reduce_EmptyCollection_ReturnsNumericInitial()
    {
        var source = """
            Add = x + total
            IsNegative = x < 0
            reduce(range(1, 4).filter(IsNegative), Add, 0)
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_Reduce_EmptyCollection_ReturnsGroupedInitialUnchanged()
    {
        var source = """
            Add = x + total
            IsNegative = x < 0
            range(1, 4).filter(IsNegative).reduce(Add, (7, 9))
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var group = Assert.IsType<Result.Group>(result.Value);
        Assert.Collection(
            group.Items,
            first => Assert.Equal(7m, Assert.IsType<Result.Atom>(first).Value),
            second => Assert.Equal(9m, Assert.IsType<Result.Atom>(second).Value));
    }

    [Fact]
    public void Eval_Reduce_GroupedElements_ArePassedWhole()
    {
        var source = """
            TakeValue((tag, value), acc) = acc + value
            reduce(((1, 10), (2, 20), (3, 30)), TakeValue, 0)
            """;

        AssertEval(source, 60);
    }

    [Fact]
    public void Eval_Reduce_GroupedAccumulator_IsAccepted()
    {
        var source = """
            Stats(x, acc) = (x + acc:0, acc:1 + 1)
            range(1, 4).reduce(Stats, (0, 0))
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var group = Assert.IsType<Result.Group>(result.Value);
        Assert.Collection(
            group.Items,
            first => Assert.Equal(10m, Assert.IsType<Result.Atom>(first).Value),
            second => Assert.Equal(4m, Assert.IsType<Result.Atom>(second).Value));
    }

    [Fact]
    public void Eval_Reduce_GroupedAccumulator_WithOrdinaryWrapperHelper_StillWorks()
    {
        var source = """
            Keep(sum, count) = (sum, count)
            Stats(x, acc) = Keep(x + acc:0, acc:1 + 1)
            range(1, 4).reduce(Stats, (0, 0))
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var group = Assert.IsType<Result.Group>(result.Value);
        Assert.Collection(
            group.Items,
            first => Assert.Equal(10m, Assert.IsType<Result.Atom>(first).Value),
            second => Assert.Equal(4m, Assert.IsType<Result.Atom>(second).Value));
    }

    [Fact]
    public void Eval_Reduce_GroupedElements_AndGroupedAccumulator_ArePassedWhole()
    {
        var source = """
            TakeStats((tag, value), (sum, count)) = (sum + value, count + 1)
            reduce(((1, 10), (2, 20), (3, 30)), TakeStats, (0, 0))
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var group = Assert.IsType<Result.Group>(result.Value);
        Assert.Collection(
            group.Items,
            first => Assert.Equal(60m, Assert.IsType<Result.Atom>(first).Value),
            second => Assert.Equal(3m, Assert.IsType<Result.Atom>(second).Value));
    }

    [Fact]
    public void Eval_Reduce_DotCall_OnImplicitParameterReceiver_UsesBuiltinFallback()
    {
        var source = """
            CollectColumns((left, right), (leftList, rightList)) = ((left, leftList), (right, rightList))
            SplitPairs = pairs.reduce(CollectColumns, ('end', 'end'))
            SplitPairs(((1, 10), (2, 20)))
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var group = Assert.IsType<Result.Group>(result.Value);
        Assert.Collection(
            group.Items,
            first =>
            {
                var left = Assert.IsType<Result.Group>(first);
                Assert.Collection(
                    left.Items,
                    head => Assert.Equal(2m, Assert.IsType<Result.Atom>(head).Value),
                    tail =>
                    {
                        var nested = Assert.IsType<Result.Group>(tail);
                        Assert.Collection(
                            nested.Items,
                            nestedHead => Assert.Equal(1m, Assert.IsType<Result.Atom>(nestedHead).Value),
                            nestedTail => Assert.Equal("end", Assert.IsType<Result.Str>(nestedTail).Value));
                    });
            },
            second =>
            {
                var right = Assert.IsType<Result.Group>(second);
                Assert.Collection(
                    right.Items,
                    head => Assert.Equal(20m, Assert.IsType<Result.Atom>(head).Value),
                    tail =>
                    {
                        var nested = Assert.IsType<Result.Group>(tail);
                        Assert.Collection(
                            nested.Items,
                            nestedHead => Assert.Equal(10m, Assert.IsType<Result.Atom>(nestedHead).Value),
                            nestedTail => Assert.Equal("end", Assert.IsType<Result.Str>(nestedTail).Value));
                    });
            });
    }

    [Fact]
    public void Eval_Reduce_EmptyStepResult_FailsWithContext()
    {
        var source = """
            IsNegative = y < 0
            Bad(x, acc) = range(1, 3).filter(IsNegative)
            range(1, 3).reduce(Bad, 0)
            """;

        AssertReduceStepShapeFails(source);
    }

    [Fact]
    public void Eval_Reduce_MultiOutputStepResult_FailsWithContext()
    {
        var source = """
            Bad(x, acc) = acc, x
            range(1, 3).reduce(Bad, 0)
            """;

        AssertReduceStepShapeFails(source);
    }

    // â”€â”€ User-defined functions â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_UserFunction_SingleParam()
    {
        var source = """
            F = x + 1
            F(5)
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_UserFunction_MultipleParams()
    {
        var source = """
            Add = a + b
            Add(3, 4)
            """;
        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_UserFunction_WithBraces()
    {
        var source = """
            Double = x * 2
            Double{3}
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_UserFunction_ReturnsMultipleOutputs()
    {
        var source = """
            Swap = a, b
            Swap(1, 2)
            """;
        AssertEval(source, 1, 2);
    }

    [Fact]
    public void Eval_UserFunction_Chained()
    {
        var source = """
            F = x + 1
            F(F(1))
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_UserFunction_RecursiveProperty()
    {
        var source = """
            Numbers = 3, 5, 9
            Numbers:0
            """;
        AssertEval(source, 3);
    }

    // â”€â”€ Complex examples â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_SumExample_Returns24()
    {
        var source = """
            Numbers = 3, 5, 9, 1, 0, 6
            Add = a + 1, total + Numbers:a
            Sum = repeat(Add, (Numbers.length), (0, 0)) : 1
            Sum
            """;
        AssertEval(source, 24);
    }

    [Fact]
    public void Eval_Fibonacci()
    {
        var source = """
            Fib = a + b, a
            repeat(Fib, (10), (1, 0)):0
            """;
        AssertEval(source, 89);
    }

    [Fact]
    public void Eval_ConditionalMax()
    {
        AssertEval("if(5 > 3, (5), (3))", 5);
        AssertEval("if(2 > 7, (2), (7))", 7);
    }

    // â”€â”€ Combine (semicolon) â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Combine_MergesAlgorithms()
    {
        var source = """
            A = 1, 2
            B = 3, 4
            atoms((A; B))
            """;
        AssertEval(source, 1, 2, 3, 4);
    }

    // â”€â”€ Math built-in â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_MathPi_ReturnsMathPI()
    {
        var result = Eval("Math.Pi");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatPi, result.Value[0]);
    }

    [Fact]
    public void Eval_MathE_ReturnsMathE()
    {
        var result = Eval("Math.E");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatE, result.Value[0]);
    }

    [Fact]
    public void Eval_MathPi_InExpression()
    {
        var result = Eval("Math.Pi * 2");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatPi * 2, result.Value[0]);
    }

    [Fact]
    public void Eval_MathE_InExpression()
    {
        var result = Eval("Math.E + 1");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatE + 1, result.Value[0]);
    }

    [Fact]
    public void Eval_MathPi_InPropertyBody()
    {
        var source = """
            Circumference = Math.Pi * 2 * r
            Circumference(5)
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatPi * 2 * 5, result.Value[0]);
    }

    [Fact]
    public void Eval_MathPi_UserPropertyOverrides()
    {
        var source = """
            Math = (Pi = 3
            Pi)
            Math.Pi
            """;
        AssertEval(source, 3);
    }

    // â”€â”€ Math functions â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_MathAbs_Positive()
        => AssertEval("Math.Abs(5)", 5);

    [Fact]
    public void Eval_MathAbs_Negative()
        => AssertEval("Math.Abs(-3)", 3);

    [Fact]
    public void Eval_MathCeil()
        => AssertEval("Math.Ceil(2.3)", 3);

    [Fact]
    public void Eval_MathFloor()
        => AssertEval("Math.Floor(2.7)", 2);

    [Fact]
    public void Eval_MathRound()
        => AssertEval("Math.Round(2.5)", 2); // banker's rounding

    [Fact]
    public void Eval_MathRound_Up()
        => AssertEval("Math.Round(3.5)", 4); // banker's rounding

    [Fact]
    public void Eval_MathSign_Positive()
        => AssertEval("Math.Sign(42)", 1);

    [Fact]
    public void Eval_MathSign_Negative()
        => AssertEval("Math.Sign(-7)", -1);

    [Fact]
    public void Eval_MathSign_Zero()
        => AssertEval("Math.Sign(0)", 0);

    [Fact]
    public void Eval_MathSqrt()
        => AssertEval("Math.Sqrt(9)", 3);

    [Fact]
    public void Eval_MathPow()
        => AssertEval("Math.Pow(2, 10)", 1024);

    [Fact]
    public void Eval_MathLn()
    {
        var result = Eval("Math.Ln(Math.E)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(1.0m, result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathLg()
    {
        var result = Eval("Math.Lg(1000)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(3.0m, result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathLog()
    {
        var result = Eval("Math.Log(8, 2)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(3.0m, result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathSin()
    {
        var result = Eval("Math.Sin(0)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(0.0m, result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathCos()
    {
        var result = Eval("Math.Cos(0)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(1.0m, result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathAsin()
    {
        var result = Eval("Math.Asin(1)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal((decimal)(Math.PI / 2), result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathAcos()
    {
        var result = Eval("Math.Acos(1)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(0.0m, result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathTan()
    {
        var result = Eval("Math.Tan(0)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(0.0m, result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathTan_NearSingularity_ReturnsLargeValue()
    {
        // Tan(Pi/2) is near a singularity — result is a large finite value.
        // After normalization, it should still be a large number (not zero or error).
        var result = Eval("Math.Tan(Math.Pi/2)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.True(result.Value[0] > 1_000_000_000_000m, "Tan near singularity should be large");
    }

    [Fact]
    public void Eval_MathSin_PiOverSix()
    {
        // Verify trig with Pi-derived args: sin(π/6) ≈ 0.5
        var result = Eval("Math.Sin(Math.Pi/6)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(0.5m, result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathAtan()
    {
        var result = Eval("Math.Atan(1)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal((decimal)(Math.PI / 4), result.Value[0], 10);
    }

    // ── Trig normalization (floating-point residue cleanup) ─────────────────

    [Fact]
    public void Eval_MathSin_Pi_ReturnsZero()
        => AssertEval("Math.Sin(Math.Pi)", 0);

    [Fact]
    public void Eval_MathCos_PiOver2_ReturnsZero()
        => AssertEval("Math.Cos(Math.Pi / 2)", 0);

    [Fact]
    public void Eval_MathTan_Pi_ReturnsZero()
        => AssertEval("Math.Tan(Math.Pi)", 0);

    [Fact]
    public void Eval_MathSin_Zero_ReturnsZero()
        => AssertEval("Math.Sin(0)", 0);

    [Fact]
    public void Eval_MathCos_Zero_ReturnsOne()
        => AssertEval("Math.Cos(0)", 1);

    [Fact]
    public void Eval_MathSin_One_ReturnsApproximate()
    {
        // Sin(1) ≈ 0.8414709848... — should be a sensible approximate result
        var result = Eval("Math.Sin(1)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(0.841470984807897m, result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathSin_Pi_ViaOpen_ReturnsZero()
    {
        var source = """
            open Math
            Sin(Pi)
            """;
        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_MathSqrt_InExpression()
        => AssertEval("Math.Sqrt(16) + 1", 5);

    [Fact]
    public void Eval_MathFn_ViaOpen()
    {
        var source = """
            open Math
            Abs(-5)
            """;
        AssertEval(source, 5);
    }

    [Fact]
    public void Eval_MathFn_ViaOpen_TwoParam()
    {
        var source = """
            open Math
            Pow(2, 8)
            """;
        AssertEval(source, 256);
    }

    // â”€â”€ Open resolution â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Open_MathPi()
    {
        var source = """
            open Math
            Pi
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatPi, result.Value[0]);
    }

    [Fact]
    public void Eval_Open_MathE()
    {
        var source = """
            open Math
            E
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatE, result.Value[0]);
    }

    [Fact]
    public void Eval_Open_MathInExpression()
    {
        var source = """
            open Math
            Pi * 2
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatPi * 2, result.Value[0]);
    }

    [Fact]
    public void Eval_Open_UserDefinedModule()
    {
        var source = """
            M = (public X = 42
            X)
            open M
            X
            """;
        AssertEvalAllPublic(source, 42);
    }

    [Fact]
    public void Eval_Open_CombineOpens()
    {
        var source = """
            A = (public X = 1
            X)
            B = (public Y = 2
            Y)
            open A; B
            X + Y
            """;
        AssertEvalAllPublic(source, 3);
    }

    [Fact]
    public void Eval_Open_MissingProperty_Fails()
    {
        var source = """
            open Math
            Foo
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_Open_InPropertyBody()
    {
        var source = """
            open Math
            Circumference = Pi * 2 * r
            Circumference(5)
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatPi * 2 * 5, result.Value[0]);
    }

    [Fact]
    public void Eval_Open_DirectFunctionOpen()
    {
        var source = """
            Lib = (public F = x + 1)
            open Lib
            F(10)
            """;
        AssertEvalAllPublic(source, 11);
    }

    [Fact]
    public void Eval_Open_DotAccess_NestedResolve()
    {
        var source = """
            Lib = (Helper = x + 1
              UseHelper = Helper(x)
            )
            Lib.UseHelper(10)
            """;
        AssertEval(source, 11);
    }


    [Fact]
    public void Eval_Open_LibraryOpenWithNestedResolve()
    {
        var source = """
            Lib = (public Helper = x + 1
              public UseHelper = Helper(x)
            )
            open Lib
            UseHelper(10)
            """;
        AssertEvalAllPublic(source, 11);
    }

    [Fact]
    public void Eval_Open_LibraryIsolatedFromOpenerScope()
    {
        // In the Opens model, libraries are isolated: they do NOT get access
        // to the opener's scope. Fn lives in Wrapper but is not visible to Lib.
        var source = """
            Lib = (Apply = Fn(x))
            Wrapper = (
              Fn = x * 2
              open Lib
              Apply(5)
            )
            Wrapper
            """;
        AssertEvalAllPublicFails(source);
    }

    [Fact]
    public void Eval_Open_LibraryCannotAccessOpenerProperty()
    {
        // Library's property references a name that only exists in the opening scope.
        // Opens are isolated â€” Factor is not visible to Lib.
        var source = """
            Lib = (Calc = x * Factor)
            Main = (
              Factor = 3
              open Lib
              Calc(5)
            )
            Main
            """;
        AssertEvalAllPublicFails(source);
    }

    [Fact]
    public void Eval_Open_LibraryWithOwnDependencies()
    {
        // A library can reference its own properties (sibling resolution works).
        var source = """
            Lib = (
              public Helper = x + 1
              public UseHelper = Helper(x)
            )
            open Lib
            UseHelper(10)
            """;
        AssertEvalAllPublic(source, 11);
    }

    // â”€â”€ Extension call (dot-call) â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_DotCall_LexicalSingleParam()
    {
        // Lean: resolveAlg on literal fails â†’ use algorithm target instead
        var source = """
            Inc = x + 1
            V = 5
            V.Inc
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_DotCall_LexicalWithArgs()
    {
        // Lean: resolveAlg on literal fails â†’ use algorithm target instead
        var source = """
            Add = a + b
            V = 3
            V.Add(4)
            """;
        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_DotCall_Chaining()
    {
        // Lean: resolveAlg on literal fails â†’ use algorithm target instead
        var source = """
            Inc = x + 1
            Double = x * 2
            V = 3
            V.Inc.Double
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_DotCall_StructuralProperty()
    {
        // 0-param structural property â†’ value access (navigation only)
        var source = """
            X = (Inc = x + 1
            5)
            X.Inc(5)
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_DotCall_StructuralProperty_NoArgs_Fails()
    {
        // Structural property with params but no args â†’ arity mismatch
        // (navigation only: no receiver injection for structural properties)
        var source = """
            X = (Inc = x + 1
            5)
            X.Inc
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_DotCall_StructuralWithArgs()
    {
        // Navigation only: all args must be provided explicitly (no receiver injection)
        var source = """
            X = (Add = a + b
            5)
            X.Add(5, 10)
            """;
        AssertEval(source, 15);
    }

    [Fact]
    public void Eval_DotCall_StructuralNoReceiverInjection()
    {
        // Confirm receiver value is NOT injected as first arg.
        // X has output 42, but F gets args directly: a=10, b=20 â†’ 30 (not 42+10=52)
        var source = """
            X = (F = a + b
            42)
            X.F(10, 20)
            """;
        AssertEval(source, 30);
    }

    [Fact]
    public void Eval_DotCall_LexicalFallback_ReceiverIsLeft()
    {
        // Num.Double: receiver=Num (left), name=Double (right)
        // Lexical fallback: call Double(Num) -> x=3, x*2=6
        var source = """
            Num = 3
            Double = x * 2
            Num.Double
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_DotCall_MissingProperty_UsesKatLangFacingMessage()
    {
        var source = """
            Lib = {
                A = 1
            }
            Lib.B
            """;

        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var contextual = Assert.IsType<EvalError.WithContext>(result.Error);
        var unresolved = Assert.IsType<EvalError.UnknownName>(contextual.Inner);
        Assert.Equal("B", unresolved.Name);

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.DoesNotContain("dotCall", formatted);
        Assert.DoesNotContain("Unknown name: B", formatted);
        Assert.Contains("Property 'B' was not found on `Lib`", formatted);
        Assert.Contains("visible algorithm or property named 'B'", formatted);
        Assert.Contains("`Lib` as the first argument", formatted);
    }

    [Fact]
    public void Eval_DotCall_MissingProperty_OnExpression_RendersReceiver()
    {
        var result = EvalFull("(2 + 3).B");
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("`(2 + 3)`", formatted);
        Assert.Contains("Property 'B' was not found", formatted);
    }

    [Fact]
    public void Eval_DotCall_LexicalFallback_WithVisibleName_StillWorks()
    {
        var source = """
            B = x + 1
            5.B
            """;

        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_UnknownName_OutsideDotCall_RemainsPlain()
    {
        var formatted = KatLangError.FromEvalError(new EvalError.UnknownName("B")).Message;
        Assert.Equal("Unknown name: B", formatted);
    }

    [Fact]
    public void Eval_MissingOutput_DefinitionOnlyProgram_RemainsValid()
        => AssertEval(
            """
            A = {
                X = 1
            }
            """);

    [Fact]
    public void Eval_MissingOutput_PropertyAccess_RemainsValid()
        => AssertEval(
            """
            A = {
                X = 1
            }
            A.X
            """,
            1);

    [Fact]
    public void Eval_MissingOutput_HigherOrderArgument_RemainsValid()
        => AssertEval(
            """
            Apply(f) = f(4)
            Inc(x) = x + 1
            Apply(Inc)
            """,
            5);

    [Fact]
    public void Eval_MissingOutput_NestedNoOutputProperty_RemainsValidWhenNotForced()
        => AssertEval(
            """
            Holder = {
                F = {
                    X = 1
                }
                0
            }
            Holder
            """,
            0);

    [Fact]
    public void Eval_MissingOutput_FinalPropertyUse_UsesKatLangFacingMessage()
        => AssertMissingOutputMessage(
            """
            A = {
                X = 1
            }
            A
            """,
            "Property 'A' has no output here. Add an Output expression inside 'A', or use one of its properties, for example `A.X`.",
            expectedLine: 4,
            expectedColumn: 1);

    [Fact]
    public void Eval_MissingOutput_CallUse_UsesKatLangFacingMessage()
        => AssertMissingOutputMessage(
            """
            A = {
                X = 1
            }
            A()
            """,
            "Cannot call 'A' because it does not define an output. Add an Output expression inside it, or call one of its properties instead.",
            expectedLine: 4,
            expectedColumn: 1);

    [Fact]
    public void Eval_MissingOutput_CallWithArgument_UsesKatLangFacingMessage()
        => AssertMissingOutputMessage(
            """
            Algo = {
                Prop = 7
            }
            Algo(6)
            """,
            "Cannot call 'Algo' because it does not define an output. Add an Output expression inside it, or call one of its properties instead.",
            expectedLine: 4,
            expectedColumn: 1);

    [Fact]
    public void Eval_MissingOutput_BinaryUse_UsesKatLangFacingMessage()
        => AssertMissingOutputMessage(
            """
            A = {
                X = 1
            }
            A + 1
            """,
            "Property 'A' has no output here. Add an Output expression inside 'A', or use one of its properties, for example `A.X`.",
            expectedLine: 4,
            expectedColumn: 1);

    [Fact]
    public void Eval_MissingOutput_UnaryUse_UsesKatLangFacingMessage()
        => AssertMissingOutputMessage(
            """
            A = {
                X = 1
            }
            -A
            """,
            "Property 'A' has no output here. Add an Output expression inside 'A', or use one of its properties, for example `A.X`.",
            expectedLine: 4,
            expectedColumn: 2);

    [Fact]
    public void Eval_MissingOutput_AssignmentOnlyFailsWhenForcedLater()
        => AssertMissingOutputMessage(
            """
            A = {
                X = 1
            }
            B = A
            B
            """,
            "Property 'A' has no output here. Add an Output expression inside 'A', or use one of its properties, for example `A.X`.");

    [Fact]
    public void Eval_MissingOutput_StructuralArgumentUse_CanStillSucceed()
        => AssertEval(
            """
            A = {
                X = 1
            }
            Use(f) = 0
            Use(A)
            """,
            0);

    [Fact]
    public void Eval_DotCall_ReversedReceiver_ProducesError()
    {
        // Double.Num: receiver=Double (parameterised), name=Num (0-param)
        // Lexical fallback: call Num(Double) -> Num has 0 params, 1 arg -> ArityMismatch
        var source = """
            Num = 3
            Double = x * 2
            Double.Num
            """;
        AssertEvalFails(source);
        var err = GetEvalError(source);
        Assert.IsType<EvalError.WithContext>(err);
        var inner = ((EvalError.WithContext)err!).Inner;
        Assert.IsType<EvalError.ArityMismatch>(inner);
        var arity = (EvalError.ArityMismatch)inner;
        Assert.Equal(0, arity.Expected); // Num has 0 params
        Assert.Equal(1, arity.Actual);   // 1 arg (the receiver Double)
    }

    [Fact]
    public void Eval_DotCall_WithArgs_LexicalFallback()
    {
        // V.Add(4): receiver=V, name=Add -> call Add(V, 4) -> a=3, b=4, a+b=7
        var source = """
            Add = a + b
            V = 3
            V.Add(4)
            """;
        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_DotCall_StructuralProperty_ArityMismatch_Propagated()
    {
        // X.Inc: Inc has params but no args -> ArityMismatch propagated through dotCall
        var source = """
            X = (Inc = x + 1
            5)
            X.Inc
            """;
        AssertEvalFails(source);
        var err = GetEvalError(source);
        Assert.IsType<EvalError.WithContext>(err);
        var inner = ((EvalError.WithContext)err!).Inner;
        Assert.IsType<EvalError.ArityMismatch>(inner);
    }
    // â”€â”€ Division, mod, power â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    // ── Extension properties on arbitrary receiver expressions ───────────────

    [Fact]
    public void Eval_DotCall_IntegerLiteral_Receiver()
    {
        // 5.Square → Square(5) → n*n = 25
        var source = """
            Square = n * n
            5.Square
            """;
        AssertEval(source, 25);
    }

    [Fact]
    public void Eval_DotCall_ParenExpr_Receiver()
    {
        // (2 + 3).Square → Square(5) → n*n = 25
        var source = """
            Square = n * n
            (2 + 3).Square
            """;
        AssertEval(source, 25);
    }

    [Fact]
    public void Eval_DotCall_ArbitraryExprReceiver_AlgorithmReceiver_StillWorks()
    {
        // A = 5; A.Square → Square(5) → 25 (existing behavior preserved)
        var source = """
            Square = n * n
            A = 5
            A.Square
            """;
        AssertEval(source, 25);
    }

    [Fact]
    public void Eval_DotCall_IntegerLiteral_Receiver_WithArgs()
    {
        // 5.Add(3) → Add(5, 3) → a+b = 8
        var source = """
            Add = a + b
            5.Add(3)
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_DotCall_ParenExpr_Receiver_WithArgs()
    {
        // (2 + 3).Add(7) → Add(5, 7) → a+b = 12
        var source = """
            Add = a + b
            (2 + 3).Add(7)
            """;
        AssertEval(source, 12);
    }

    [Fact]
    public void Eval_DotCall_SameLineSpaceSeparated()
    {
        // "Add = a + b 2.Add(6)" → Add has body "a + b", then "2.Add(6)" is output
        var source = "Add = a + b 2.Add(6)";
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_DotCall_ParenExprReceiver_SameLineSpaceSeparated()
    {
        // "Add = a + b (2).Add(6)" → Add has body "a + b", then "(2).Add(6)" is output
        var source = "Add = a + b (2).Add(6)";
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_DotCall_DecimalLiteral_Receiver()
    {
        // 2.0.Double → Double(2.0) → x*2 = 4.0
        var source = """
            Double = x * 2
            2.0.Double
            """;
        AssertEval(source, 4.0m);
    }

    [Fact]
    public void Eval_Division()
        => AssertEval("10 / 4", 2.5m);

    [Fact]
    public void Eval_IntegerDivision()
        => AssertEval("10 div 3", 3);

    [Fact]
    public void Eval_IntegerDivision_Truncates()
        => AssertEval("-7 div 2", -3);

    [Fact]
    public void Eval_DivisionByZero_Fails()
        => AssertEvalFails("5 / 0");

    [Fact]
    public void Eval_IntegerDivisionByZero_Fails()
        => AssertEvalFails("5 div 0");

    [Fact]
    public void Eval_Modulo()
        => AssertEval("10 mod 3", 1);

    [Fact]
    public void Eval_ModuloByZero_Fails()
        => AssertEvalFails("10 mod 0");

    [Fact]
    public void Eval_Power()
        => AssertEval("2 ^ 10", 1024);

    [Fact]
    public void Eval_Power_ZeroExponent()
        => AssertEval("5 ^ 0", 1);

    [Fact]
    public void Eval_Power_NegativeExponent()
        => AssertEval("2 ^ -3", 0.125m);

    // â”€â”€ Comparison operators â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_LessEqual_True()
        => AssertEval("3 <= 3", 1);

    [Fact]
    public void Eval_LessEqual_False()
        => AssertEval("4 <= 3", 0);

    [Fact]
    public void Eval_GreaterEqual_True()
        => AssertEval("3 >= 3", 1);

    [Fact]
    public void Eval_GreaterEqual_False()
        => AssertEval("2 >= 3", 0);

    [Fact]
    public void Eval_Equal_True()
        => AssertEval("5 == 5", 1);

    [Fact]
    public void Eval_Equal_False()
        => AssertEval("5 == 6", 0);

    [Fact]
    public void Eval_NotEqual_True()
        => AssertEval("5 != 6", 1);

    [Fact]
    public void Eval_NotEqual_False()
        => AssertEval("5 != 5", 0);

    // â”€â”€ Logical operators â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_And_TrueTrue()
        => AssertEval("1 and 1", 1);

    [Fact]
    public void Eval_And_TrueFalse()
        => AssertEval("1 and 0", 0);

    [Fact]
    public void Eval_And_FalseFalse()
        => AssertEval("0 and 0", 0);

    [Fact]
    public void Eval_Or_TrueFalse()
        => AssertEval("1 or 0", 1);

    [Fact]
    public void Eval_Or_FalseFalse()
        => AssertEval("0 or 0", 0);

    [Fact]
    public void Eval_Xor_TrueFalse()
        => AssertEval("1 xor 0", 1);

    [Fact]
    public void Eval_Xor_TrueTrue()
        => AssertEval("1 xor 1", 0);

    [Fact]
    public void Eval_Xor_FalseFalse()
        => AssertEval("0 xor 0", 0);

    [Fact]
    public void Eval_Not_Zero()
        => AssertEval("not 0", 1);

    [Fact]
    public void Eval_Not_NonZero()
        => AssertEval("not 5", 0);

    [Fact]
    public void Eval_Not_DoubleNegation()
        => AssertEval("not not 1", 1);

    // â”€â”€ Operator combinations â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_CompoundExpression_IfWithComparison()
    {
        var source = """
            X = 10
            if(X >= 5, 1, 0)
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_LogicalInIf()
    {
        var source = """
            A = 3
            B = 7
            if(A > 0 and B > 0, 1, 0)
            """;
        AssertEval(source, 1);
    }

    // â”€â”€ Edge cases â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_EmptySource_ReturnsEmpty()
    {
        var result = Eval("");
        Assert.True(result.IsOk);
        Assert.Empty(result.Value);
    }

    [Fact]
    public void Eval_UndefinedProperty_Fails()
        => AssertEvalFails("X");

    [Fact]
    public void Eval_UnknownIdentifier_ReturnsUnresolvedImplicitParams()
    {
        // "Sum" is detected as a parameter by ParameterDetector, so the root
        // block has params=["Sum"].  Block value-position semantics:
        // 1+ params => UnresolvedImplicitParams.
        var err = GetEvalError("Sum");
        Assert.NotNull(err);
        while (err is EvalError.WithContext wc)
            err = wc.Inner;
        var uip = Assert.IsType<EvalError.UnresolvedImplicitParams>(err);
        Assert.Equal(["Sum"], uip.ParamNames);
    }

    [Fact]
    public void Eval_UnknownIdentifier_ReturnsUnresolvedImplicitParamsType()
    {
        // "Sum" becomes a parameter → block has 1 param → UnresolvedImplicitParams in value position.
        var err = GetEvalError("Sum");
        Assert.NotNull(err);
        while (err is EvalError.WithContext wc)
            err = wc.Inner;
        Assert.IsType<EvalError.UnresolvedImplicitParams>(err);
    }

    [Fact]
    public void Eval_DivByZero_HasCorrectSpan()
    {
        var err = GetEvalError("5 / 0");
        Assert.NotNull(err);
        Assert.NotNull(err.Span);
        // Binary expression "5 / 0" spans full expression
        Assert.Equal(1, err.Span.StartLineNumber);
        Assert.Equal(1, err.Span.StartColumn);
        Assert.Equal(1, err.Span.EndLineNumber);
        Assert.Equal(5, err.Span.EndColumn);
    }

    [Fact]
    public void Eval_UnknownIdentifier_MultiLine_ReturnsUnresolvedImplicitParams()
    {
        // Y is detected as a parameter → block has 1 param → UnresolvedImplicitParams.
        var source = """
            X = 5
            Y
            """;
        var err = GetEvalError(source);
        Assert.NotNull(err);
        while (err is EvalError.WithContext wc)
            err = wc.Inner;
        Assert.IsType<EvalError.UnresolvedImplicitParams>(err);
    }

    [Fact]
    public void Eval_WrongParamCount_Fails()
    {
        var source = """
            F = a + b
            F(1)
            """;
        AssertEvalFails(source);
    }

        [Fact]
        public void Eval_ArityMismatch_TooManyArguments_UsesUserFacingMessage()
        {
            AssertArityMismatchMessage(
                """
                A = x
                A(1, 2)
                """,
                "Property 'A' expects 1 parameter, but was called with 2 arguments.");
        }

        [Fact]
        public void Eval_ArityMismatch_TooFewArguments_UsesUserFacingMessage()
        {
            AssertArityMismatchMessage(
                """
                Add = a + b
                Add(1)
                """,
                "Property 'Add' expects 2 parameters, but was called with 1 argument.");
        }

        [Fact]
        public void Eval_ArityMismatch_NoArgumentsProvided_UsesUserFacingMessage()
        {
            var source = """
                A = x
                A
                """;

            var result = EvalFull(source);
            if (result.IsOk)
                Assert.Fail($"Expected evaluation failure but got: {result.Value}");

            var contextual = Assert.IsType<EvalError.WithContext>(result.Error);
            Assert.Equal("while evaluating property A", contextual.Context);
            var arity = Assert.IsType<EvalError.ArityMismatch>(contextual.Inner);
            Assert.Equal(1, arity.Expected);
            Assert.Equal(0, arity.Actual);

            var formatted = KatLangError.FromEvalError(result.Error).Message;
            Assert.Equal("Property 'A' expects 1 parameter, but was called with 0 arguments.", formatted);
        }

        [Fact]
        public void Eval_ArityMismatch_ZeroParameterPropertyCalledWithArguments_UsesUserFacingMessage()
        {
            AssertArityMismatchMessage(
                """
                A = 1
                A(1)
                """,
                "Property 'A' expects 0 parameters, but was called with 1 argument.");
        }
    [Fact]
    public void Eval_ArityMismatch_InnerCall_SpanPointsToInnerCall()
    {
        // Inner has 0 params; calling Inner(param) inside Outer should produce
        // an error whose span points to Inner(param), not the outer Outer(50000).
        var source = """
            Inner = 5
            Outer = param - Inner(param)
            Outer(50000)
            """;
        var err = GetEvalError(source);
        Assert.NotNull(err);
        Assert.NotNull(err.Span);
        // Span should point to "Inner(param)" on line 2, NOT "Outer(50000)" on line 3.
        Assert.Equal(2, err.Span.StartLineNumber);
    }

    // â”€â”€ Grace operator end-to-end tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_GracePrefix_ReordersParams()
    {
        // Without grace: F(a,b) where a=first-appearance â†’ a=2, b=3
        // F = b + ~a * 10 â†’ params [a, b] (a moved left)
        // F(2, 3) â†’ a=2, b=3 â†’ 3 + 2*10 = 23
        var source = """
            F = b + ~a * 10
            F(2, 3)
            """;
        AssertEval(source, 23);
    }

    [Fact]
    public void Eval_GracePostfix_ReordersParams()
    {
        // F = a~ + b â†’ first-appearance [a, b], a~ moves right â†’ params [b, a]
        // F(2, 3) â†’ b=2, a=3 â†’ 3 + 2 = 5
        var source = """
            F = a~ + b
            F(2, 3)
            """;
        AssertEval(source, 5);
    }

    [Fact]
    public void Eval_NoGrace_Baseline()
    {
        // Without grace: F(a,b), a=first â†’ a=2, b=3 â†’ 2 + 3*10 = 32
        var source = """
            F = a + b * 10
            F(2, 3)
            """;
        AssertEval(source, 32);
    }

    [Fact]
    public void Eval_GraceWithImplicitArgs()
    {
        // F = b + ~a â†’ params [a, b]
        // G uses F implicitly: G = F + 1
        // G(2, 3) â†’ F(2,3) + 1 â†’ (3 + 2) + 1 = 6
        var source = """
            F = b + ~a
            G = F + 1
            G(2, 3)
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_GraceDoublePrefixThreeParams()
    {
        // F = c + b + ~~a â†’ first-appearance [c, b, a], ~~a moves a 2 left â†’ [a, c, b]
        // F(1, 2, 3) â†’ a=1, c=2, b=3 â†’ 2 + 3 + 1 = 6
        var source = """
            F = c + b + ~~a
            F(1, 2, 3)
            """;
        AssertEval(source, 6);
    }

    // â”€â”€ Open-specific tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Open_MultipleOpens()
    {
        var source = """
            A = (public X = 1)
            B = (public Y = 2)
            open A, B
            X + Y
            """;
        AssertEvalAllPublic(source, 3);
    }

    [Fact]
    public void Eval_Open_UnbracketedCommaList_ResolvesFromSecondLib()
    {
        // open Lib2, Lib3 → two separate opens; Val3 resolves from Lib3
        var source = """
            Lib2 = (public Val2 = 20)
            Lib3 = (public Val3 = 30)
            open Lib2, Lib3
            Val3
            """;
        AssertEvalAllPublic(source, 30);
    }

    [Fact]
    public void Eval_Open_AmbiguityFails()
    {
        // Both A and B provide X â†’ ambiguity â†’ should fail
        var source = """
            A = (public X = 1)
            B = (public X = 2)
            open A, B
            X
            """;
        AssertEvalAllPublicFails(source);
    }

    [Fact]
    public void Eval_Open_LocalOverridesOpen()
    {
        // Local property takes priority over imported name
        var source = """
            Lib = (public X = 99)
            open Lib
            X = 1
            X
            """;
        AssertEvalAllPublic(source, 1);
    }

    [Fact]
    public void Eval_Open_CombinedLibrary()
    {
        // Semicolon merges two libs into one import (no ambiguity)
        var source = """
            A = (public X = 1)
            B = (public Y = 2)
            open A; B
            X + Y
            """;
        AssertEvalAllPublic(source, 3);
    }

    [Fact]
    public void Eval_Open_NotTransitive()
    {
        // Lib1's opens should not be visible to the opener
        var source = """
            Inner = (public Z = 42)
            Lib1 = (
                open Inner
                W = Z
            )
            open Lib1
            Z
            """;
        // Z is not transitively visible â†’ fail
        AssertEvalAllPublicFails(source);
    }

    [Fact]
    public void Eval_Open_SelfNameInOpenExpression_Fails()
    {
        // "self" is no longer a keyword — it's now just an identifier.
        // Using it in open position fails because there's no algorithm named "self".
        var source = """
            HiddenLib = (X = 42)
            open self.HiddenLib
            X
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_Open_ChildResolvesFromParentOpens()
    {
        // Lean test: parent-open visibility.
        // Parent opens Lib; Child does NOT open it.
        // Child resolves "X" via parent chain â†’ parent opens â†’ Lib.
        var source = """
            Lib = (public X = 42)
            Main = (
                open Lib
                Child = (X)
                Child
            )
            Main
            """;
        AssertEvalAllPublic(source, 42);
    }

    [Fact]
    public void Eval_Open_StructuralOwnershipTakesPrecedenceOverOpens()
    {
        // Ownership-first model: structural properties in the parent chain
        // always take precedence over opened namespaces.
        //
        // Wrapper resolves "Val" via:
        //   1. Local props â†’ none
        //   2. Parent structural: Main â†’ no Val; Root â†’ Val = 0 found!
        //   3. Opens never consulted (structural wins)
        //
        // Even though Main opens Lib which has Val = 42, the root's
        // structural Val = 0 takes precedence.
        var source = """
            Val = 0
            Main = (
                Lib = (public Val = 42)
                open Lib
                Wrapper = (
                    Val
                )
                Wrapper
            )
            Main
            """;
        AssertEvalAllPublic(source, 0);
    }

    // â”€â”€ Property visibility tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Visibility_OpenCanSeePublicButNotPrivate()
    {
        // Library with one public and one private property.
        // Open should see the public one but not the private one.
        // Lean: open target itself must also be public (lookupLexicalDirectUnwiredPublic).
        var source = """
            public Lib = (public X = 42
            Y = 99)
            open Lib
            X
            """;
        AssertEval(source, 42);

        // Now try Y (private) â€” should fail
        var sourceY = """
            public Lib = (public X = 42
            Y = 99)
            open Lib
            Y
            """;
        AssertEvalFails(sourceY);
    }

    [Fact]
    public void Eval_Visibility_NotPublicPropertyOnPrivateIntermediate()
    {
        // open Lib.Sub where Sub exists but is private → NotPublicProperty.
        // Lib doesn't need public (it's in the ownership chain), but Sub must
        // be public because it's an intermediate on the open path.
        var source = """
            Lib = (Sub = (public X = 42
            X))
            open Lib.Sub
            X
            """;
        AssertEvalFails(source);
    }

    // â”€â”€ Open normalization acceptance tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Open_PropPathInOpen_Works()
    {
        // Acceptance A: Lib.Sub in open â†’ prop-path resolves correctly
        var source = """
            public Lib = (public Sub = (public X = 1))
            open Lib.Sub
            X
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Open_DotCallWithArgs_Fails()
    {
        // Acceptance B: Lib.Sub() â†’ call-like dot syntax in open â†’ parse error
        var source = """
            public Lib = (public Sub = (public X = 1))
            open Lib.Sub()
            X
            """;
        // Parser emits diagnostic for invalid open form
        var result = KatLang.Parser.Parse(source);
        Assert.True(result.HasErrors);
    }

    [Fact]
    public void Eval_Open_MultipleOpensCommaForm_Works()
    {
        // Acceptance C: multiple opens with comma-separated form
        var source = """
            public Lib2 = (public Val = 2)
            public Lib3 = (public Val2 = 3)
            open Lib2, Lib3
            Val2
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Open_PrivateIntermediate_Fails()
    {
        // Acceptance D: private intermediate on open path
        var source = """
            Lib = (Sub = (public X = 1))
            open Lib.Sub
            X
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_Visibility_OwnershipFirstShadowingBeatsOpens()
    {
        // Structural property in parent chain beats opened property,
        // even when the structural property is private.
        // Opens enforce public-only, but structural always wins first.
        var source = """
            Val = 0
            Main = (
                Lib = (Val = 42)
                open Lib
                Wrapper = (
                    Val
                )
                Wrapper
            )
            Main
            """;
        // Make Lib and its Val public so the open path works
        AssertEvalAllPublic(source, 0);
    }

    [Fact]
    public void Eval_Visibility_AmbiguousOpenWithTwoPublicProviders()
    {
        // Two opens provide the same public name â†’ AmbiguousOpen error
        var source = """
            A = (public X = 1)
            B = (public X = 2)
            open A, B
            X
            """;
        AssertEvalAllPublicFails(source);

        // Verify it's specifically an AmbiguousOpen error
        var ast = Parser.Parse(source).Root;
        var publicAst = MakeAllPublic(ast);
        var result = Evaluator.RunFlat(new Expr.Block(publicAst));
        Assert.True(result.IsError);
        // Unwrap WithContext if present
        var err = result.Error;
        while (err is EvalError.WithContext wc)
            err = wc.Inner;
        Assert.IsType<EvalError.AmbiguousOpen>(err);
    }

    [Fact]
    public void Eval_Visibility_AllParsedPropertiesPrivateByDefault()
    {
        // Parsed properties are private by default.
        // Opening a user-defined library with default visibility should
        // not expose any properties through opens.
        var source = """
            Lib = (X = 42)
            open Lib
            X
            """;
        // Without MakeAllPublic, X should NOT be visible through opens
        AssertEvalFails(source);
    }

    // â”€â”€ Public keyword syntax tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_PublicKeyword_OpenCanSeePublicProperty()
    {
        var source = """
            Lib = (public Val = 42)
            open Lib
            Val
            """;
        // Lib itself must also be public for open resolution to find it
        AssertEvalAllPublic(source, 42);
    }

    [Fact]
    public void Eval_PublicKeyword_EndToEnd()
    {
        // Full end-to-end: public keyword makes property visible through opens.
        // Lean: open target must also be public (lookupLexicalDirectUnwiredPublic).
        var source = """
            public Lib = (public Val = 42)
            open Lib
            Val
            """;
        AssertEval(source, 42);
    }

    [Fact]
    public void Eval_PublicKeyword_PrivateNotVisible()
    {
        // Library with one public and one private property
        // Lean: open target itself must be public
        var source = """
            public Lib = (public X = 1
            Y = 2)
            open Lib
            X
            """;
        AssertEval(source, 1);

        // Y is private, should fail
        var sourceY = """
            public Lib = (public X = 1
            Y = 2)
            open Lib
            Y
            """;
        AssertEvalFails(sourceY);
    }

    [Fact]
    public void Eval_PublicKeyword_InBlock()
    {
        // Lean: open target must be public
        var source = """
            public Lib = {public Val = 42}
            open Lib
            Val
            """;
        AssertEval(source, 42);
    }

    // â”€â”€ Opens-aware parameter detection (Lean: shouldTreatAsImplicitParam) â”€â”€

    [Fact]
    public void Eval_Open_LowercasePublicProperty_ResolvesViaOpen()
    {
        // Lowercase public property visible through opens should NOT become a param.
        // Lean: shouldTreatAsImplicitParam uses lookupLexical which includes opens.
        // Lean: open target must also be public (lookupLexicalDirectUnwiredPublic).
        var source = """
            public Lib = (public val = 42)
            open Lib
            val
            """;
        AssertEval(source, 42);
    }

    [Fact]
    public void Eval_Open_LowercasePublicFunction_CanBeCalled()
    {
        // Opened lowercase function name: should stay as Resolve, not become param.
        // Lean: open target must also be public.
        var source = """
            public Lib = (public inc = x + 1)
            open Lib
            inc(5)
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_Open_PropertyBodySeesOpenedNames()
    {
        // "val" in F's body is visible through parent's opens (not a param of F).
        // Lean: open target must also be public.
        var source = """
            public Lib = (public val = 42)
            open Lib
            F = val + 1
            F
            """;
        AssertEval(source, 43);
    }

    // -- open visibility: container does not need to be public ----------------
    // Rule: open never requires the opened algorithm itself to be public.
    //       It only requires the algorithm to be available in the current context.
    //       open imports only public members of that algorithm.

    [Fact]
    public void Eval_Open_LocalNonPublicAlgorithm_CanBeOpened()
    {
        // open never requires the opened algorithm itself to be public.
        // It only requires the algorithm to be available in the current context.
        // open imports only public members of that algorithm.
        var source = """
            open Lib
            Lib = {
                public Pi = 3
            }
            Pi
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Open_LocalPublicAlgorithm_CanStillBeOpened()
    {
        // Public open target also works (public is not required, but not harmful).
        var source = """
            open Lib
            public Lib = {
                public Pi = 3
            }
            Pi
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Open_NonPublicMember_NotImported()
    {
        // open imports only public members. Non-public members must not be visible.
        var source = """
            open Lib
            Lib = {
                Pi = 3
            }
            Pi
            """;
        var result = Eval(source);
        Assert.True(result.IsError);
    }

    [Fact]
    public void Eval_Open_QualifiedAccess_StillWorks()
    {
        // Qualified dot-access should keep current intended behavior.
        var source = """
            Lib = {
                public Pi = 3
            }
            Lib.Pi
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Open_NestedLocalOpen_Works()
    {
        // open inside a nested algorithm body can open a sibling definition.
        var source = """
            A = {
                open Lib
                Lib = {
                    public Pi = 3
                }
                Pi
            }
            A
            """;
        AssertEval(source, 3);
    }

    // â”€â”€ BinaryOp.Pow evaluator coverage â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Pow_IntegerExponentCases_Work()
    {
        AssertEval("2 ^ 0", 1);
        AssertEval("2 ^ 3", 8);
        AssertEval("5 ^ 4", 625);
        AssertEval("(-2) ^ 3", -8);
        AssertEval("(-2) ^ 4", 16);
        AssertEval("0 ^ 5", 0);
        AssertEval("0 ^ 0", 1);
        AssertEval("1 ^ 25", 1);
    }

    [Fact]
    public void Eval_Pow_NegativeIntegerExponentCases_Work()
    {
        AssertEval("2 ^ -3", 0.125m);
        AssertEval("10 ^ -2", 0.01m);
        AssertEval("(-2) ^ -3", -0.125m);
        AssertEval("1 ^ -25", 1);
    }

    [Fact]
    public void Eval_Pow_FractionalExponentCases_UseMathPow()
    {
        AssertEvalApprox("9 ^ 0.5", 3m, precision: 10);
        AssertEvalApprox("27 ^ 1.5", 140.2961154131m, precision: 10);
    }

    [Fact]
    public void Eval_Pow_FractionalExponent_MatchesMathPowNormalization()
    {
        AssertEval("0.0000000000000001 ^ 1.5 == Math.Pow(0.0000000000000001, 1.5)", 1);
    }

    [Fact]
    public void Eval_Pow_ZeroToNegativeInteger_FailsClearly()
    {
        AssertEvalFailsWithIllegalInEval("0 ^ -1", "zero cannot be raised to a negative integer exponent");
    }

    [Fact]
    public void Eval_Pow_ExponentOne_DoesNotOverflowFromFinalSquaring()
    {
        AssertEval("79228162514264337593543950335 ^ 1", 79228162514264337593543950335m);
    }

    // ── Numeric overflow ─────────────────────────────────────────────────────

    [Fact]
    public void Eval_Pow_Overflow_ReturnsNumericOverflow()
    {
        var err = GetEvalError("10 ^ 30");
        Assert.NotNull(err);
        Assert.IsType<EvalError.NumericOverflow>(err);
    }

    [Fact]
    public void Eval_Pow_NormalRange_Succeeds()
    {
        AssertEval("10 ^ 2", 100);
    }

    [Fact]
    public void Eval_Mul_Overflow_ReturnsNumericOverflow()
    {
        // decimal.MaxValue is ~7.9e28; multiplying two large values overflows
        var err = GetEvalError("79228162514264337593543950335 * 2");
        Assert.NotNull(err);
        Assert.IsType<EvalError.NumericOverflow>(err);
    }

    // â”€â”€ evalCall args wiring (Lean: wireToCaller in user-defined call path) â”€â”€

    [Fact]
    public void Eval_CallArgsWiring_PropertyAsArgument()
    {
        // Caller property usable as argument: G resolves in caller scope
        var source = """
            G = 7
            F = x + 1
            F(G)
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_CallArgsWiring_PropertyDotAccessAsArgument()
    {
        // Property with dot-access usable as argument
        var source = """
            G = (public Val = 7)
            F = x + 1
            F(G.Val)
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_CallArgsWiring_MultiplePropertyArgs()
    {
        // Multiple properties as arguments
        var source = """
            A = 3
            B = 5
            Add = x + y
            Add(A, B)
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_CallArgsWiring_NestedBlockScopeNotSmuggled()
    {
        // Block introduces its own scope â€” inner names don't leak
        var source = """
            F = x + 1
            F({10})
            """;
        AssertEval(source, 11);
    }

    // â”€â”€ NetSalary scenario (dotCall on parameterised algorithm) â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_NetSalary_DotCallIncomeTax_FailsWhenOuterParamsAreCaptured()
    {
                var source = @"
                        NetSalary = {
                            SocialSecurityTax = grossSalary * 0.105
                            NonTaxableMinimum = grossSalary - SocialSecurityTax - 75
                            ChildTaxCredit = numberOfChildren * 162
                            TaxableIncome = NonTaxableMinimum - ChildTaxCredit
                            IncomeTax = TaxableIncome * 0.24

                            grossSalary - SocialSecurityTax - IncomeTax
                        }
                        NetSalary.IncomeTax(1000, 2)
                        ";

        AssertLocalOnlyPropertyMessage(
                        source,
                        "Property 'IncomeTax' on `NetSalary` is local-only because it depends on parameter(s) owned by the enclosing algorithm.");
    }

    [Fact]
    public void Eval_NetSalary_DirectCall_UsesAlgorithmParameters()
    {
        // NetSalary(1000, 2) binds the algorithm-level interface directly.
        // Output = 1000 - 105 - 119.04 = 775.96
        var source = """
            NetSalary = {
              SocialSecurityTax = grossSalary * 0.105
              NonTaxableMinimum = grossSalary - SocialSecurityTax - 75
              ChildTaxCredit = numberOfChildren * 162
              TaxableIncome = NonTaxableMinimum - ChildTaxCredit
              IncomeTax = TaxableIncome * 0.24
              
              grossSalary - SocialSecurityTax - IncomeTax
            }
            NetSalary(1000, 2)
            """;
        AssertEval(source, 775.96m);
    }

    [Fact]
    public void Eval_NetSalary_SelfContainedProperty_DotCall()
    {
        // Working approach: IncomeTax explicitly uses its own free variables.
        // grossSalary=1000, numberOfChildren=2:
        // (1000 - 1000*0.105 - 75 - 2*162) * 0.24 = 496 * 0.24 = 119.04
        var source = """
            NetSalary = {
              IncomeTax = (grossSalary - grossSalary * 0.105 - 75 - numberOfChildren * 162) * 0.24
            }
            NetSalary.IncomeTax(1000, 2)
            """;
        AssertEval(source, 119.04m);
    }

    // ── Semicolon: structural combining operator ────────────────────────────

    // A. Existing property detection still works

    [Fact]
    public void Eval_PropertyDetection_TwoPrivateProperties()
    {
        AssertEval("A = 5 B = 10 A + B", 15);
    }

    [Fact]
    public void Eval_PropertyDetection_PublicAndPrivateProperties()
    {
        AssertEval("public A = 5 B = 10 A + B", 15);
    }

    // B. Comma-only outputs still work

    [Fact]
    public void Eval_CommaOnly_MultipleOutputs()
    {
        AssertEval("1 + 2, 2 + 3", 3, 5);
    }

    // C. Structural combining flattens

    [Fact]
    public void Eval_Combine_TwoFragments()
    {
        AssertEval("1 + 2, 2 + 3; 3 + 4", 3, 5, 7);
    }

    [Fact]
    public void Eval_Combine_MultipleFragments()
    {
        AssertEval("1 + 2, 2 + 3; 3 + 4; 4 + 5, 5 + 6, 6 + 7", 3, 5, 7, 9, 11, 13);
    }

    // D. Combining algorithms by reference

    [Fact]
    public void Eval_Combine_ByReference()
    {
        var source = """
            Property1 = 1
            Property2 = 2, 3
            Property1; Property2
            """;
        AssertEval(source, 1, 2, 3);
    }

    // E. Structural extension of algorithm fragments

    [Fact]
    public void Eval_Combine_StructuralExtension()
    {
        // Simplified version of the motivating pattern:
        // Combine calls with additional expressions
        var source = """
            Next = if(a > 5, (a - 1, b + 1), (b - 1, a + 1))
            Result = Next(10, 0); 10 > 5
            Result
            """;
        AssertEval(source, 9, 1, 1);
    }

    // F. Nested algorithm with semicolon

    [Fact]
    public void Eval_Combine_InParenAlgorithm()
    {
        // (1 + 2; 3 + 4) is a parameterless nested algorithm with semicolon
        AssertEval("(1 + 2; 3 + 4)", 3, 7);
    }

    [Fact]
    public void Eval_Combine_AsFunctionArg()
    {
        // Foo receives a multi-output argument via semicolon combining
        var source = """
            Foo = x, y
            Foo(1 + 2; 3 + 4)
            """;
        AssertEval(source, 3, 7);
    }

    // G. Capturing algorithm with semicolon

    [Fact]
    public void Eval_Combine_InBraceAlgorithm()
    {
        var source = "{ X = 10 X + 1; X + 2 }";
        AssertEval(source, 11, 12);
    }

    // H. Ordinary grouped arithmetic expression unchanged

    [Fact]
    public void Eval_ParenGrouping_ArithmeticUnchanged()
    {
        AssertEval("1 + (2 * 3)", 7);
    }

    // I. Multiline formatting remains irrelevant

    [Fact]
    public void Eval_Combine_MultilineEquivalentToOneline()
    {
        var multiline = """
            1 + 2, 2 + 3;
            3 + 4;
            4 + 5, 5 + 6
            """;
        var oneline = "1 + 2, 2 + 3; 3 + 4; 4 + 5, 5 + 6";
        var r1 = Eval(multiline);
        var r2 = Eval(oneline);
        Assert.Equal(r1.Value, r2.Value);
    }

    // Additional: simple combine of two literals

    [Fact]
    public void Eval_Combine_SimpleLiterals()
    {
        AssertEval("1; 2", 1, 2);
    }

    [Fact]
    public void Eval_Combine_PropertyBody()
    {
        AssertEval("A = 1; 2 A", 1, 2);
    }

    // ── Higher-Order Algorithm Parameters ────────────────────────────────────

    [Fact]
    public void Eval_HigherOrder_AlgoCallsPassedAlgorithm()
    {
        // Algo = func(9); F = a + 1; Algo(F) → F(9) → 9+1 = 10
        AssertEval("Algo = func(9)\nF = a + 1\nAlgo(F)", 10);
    }

    [Fact]
    public void Eval_HigherOrder_PassAlgorithmWithArgs()
    {
        // Apply = func(x); F = a + 1; Apply(F, 5) → F(5) → 5+1 = 6
        AssertEval("Apply = func(x)\nF = a + 1\nApply(F, 5)", 6);
    }

    [Fact]
    public void Eval_HigherOrder_ZeroParamAlgorithmAsValue()
    {
        // Use = func; V = 42; Use(V) → V evaluates to 42
        AssertEval("Use = func\nV = 42\nUse(V)", 42);
    }

    [Fact]
    public void Eval_HigherOrder_MultiParamNeedsExplicitCall()
    {
        // Use = func; F = a + 1; Use(F) → F has params, used bare → arityMismatch
        AssertEvalFails("Use = func\nF = a + 1\nUse(F)");
    }

    [Fact]
    public void Eval_HigherOrder_NonAlgorithmArg_NotAnAlgorithm()
    {
        // Algo = func(9); Algo(5) → 5 is not an algorithm → notAnAlgorithm
        AssertEvalFails("Algo = func(9)\nAlgo(5)");
    }

    [Fact]
    public void Eval_HigherOrder_NestedAlgorithmPassing()
    {
        // Outer = func(10); Inner = func(a); F = a * 2; Inner(F, Outer(F))
        // Outer(F) → F(10) → 20; Inner(F, 20) → F(20) → 40
        AssertEval("Outer = func(10)\nInner = func(a)\nF = a * 2\nInner(F, Outer(F))", 40);
    }

    [Fact]
    public void Eval_HigherOrder_AlgorithmWithMultipleParams()
    {
        // Algo = func(3, 4); F = a + b; Algo(F) → F(3, 4) → 7
        AssertEval("Algo = func(3, 4)\nF = a + b\nAlgo(F)", 7);
    }

    [Fact]
    public void Eval_HigherOrder_DualView_BothAlgAndValueMeaning()
    {
        // V = 42 is a 0-param algorithm that also evaluates to a value.
        // When passed as argument, both AlgEnv and ValEnv bindings should be available.
        // Use = func; V = 42; Use(V) → ValEnv has func=42, AlgEnv has func=V
        // Param("func") checks ValEnv first → 42
        AssertEval("Use = func\nV = 42\nUse(V)", 42);
    }

    [Fact]
    public void Eval_HigherOrder_DotCall_StructuralPropertyWithHOF()
    {
        // Structural property Apply takes a higher-order func param + value param
        // Must use same dual-view binding logic as normal user-defined calls
        var source = """
            A = (Apply = func(x)
            0)
            F = a + 1
            A.Apply(F, 5)
            """;
        AssertEvalAllPublic(source, 6);
    }

    [Fact]
    public void Eval_HigherOrder_DotCall_StructuralPropertyPassesAlgorithm()
    {
        // Structural property Algo calls a passed algorithm with fixed value
        var source = """
            A = (Algo = func(9)
            0)
            F = a + 1
            A.Algo(F)
            """;
        AssertEvalAllPublic(source, 10);
    }

    [Fact]
    public void Eval_HigherOrder_GroupedValueBeforeAlgorithmOnlyArg_PreservesArgumentBoundary()
    {
        var source = """
            OccurrenceCount = filter(values, predicate).count
            OccurrenceCount((1, 2), {n mod 2 == 0})
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_HigherOrder_InlinePredicate_CapturesOuterValueParameter()
    {
        var source = """
            OccurrenceCount(values, target) = filter(values, {item == target}).count
            OccurrenceCount((1, 2), 2)
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_HigherOrder_FinalGroupedValueStillUnpacksAfterAlgorithmOnlyArgument()
    {
        var source = """
            Inc = x + 1
            UsePair(f, x, y) = f(x) + y
            UsePair(Inc, (10, 20))
            """;

        AssertEval(source, 31);
    }

    [Fact]
    public void Eval_HigherOrder_GraceReordersCallableParameter()
    {
        var source = """
            IsEven = x mod 2 == 0
            Choose = if(predicate~(x), x, 0)
            Choose(3, IsEven)
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_HigherOrder_FlatMultiBinderClause_UsesOrdinaryBinding()
    {
        var source = """
            IsEven = y mod 2 == 0
            Choose(x, predicate) = if(predicate(x), x, 0)
            Choose(4, IsEven)
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_HigherOrder_FlatMultiBinderClause_FalsePredicate_UsesElseBranch()
    {
        var source = """
            IsEven = y mod 2 == 0
            Choose(x, predicate) = if(predicate(x), x, 0)
            Choose(3, IsEven)
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_HigherOrder_FlatMultiBinderClause_DotCallUsesOrdinaryBinding()
    {
        var source = """
            Holder = (
                Apply(x, transform) = transform(x)
                Apply
            )
            Increment = y + 1
            Holder.Apply(9, Increment)
            """;

        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_ClauseDefinition_SingleBinder_ElaboratesToOrdinaryAlgorithm()
    {
        var source = """
            Id(x) = x
            Id(7)
            """;

        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_ClauseDefinition_SingleBinder_HigherOrderCallUsesOrdinaryBinding()
    {
        var source = """
            Apply(f) = f(4)
            Double(x) = x * 2
            Apply(Double)
            """;

        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_ClauseDefinition_SingleBinder_RejectsExtraArguments()
    {
        var error = GetEvalError("""
            Id(x) = x
            Id(1, 2)
            """);

        Assert.NotNull(error);

        while (error is EvalError.WithContext withContext)
            error = withContext.Inner;

        var arity = Assert.IsType<EvalError.ArityMismatch>(error);
        Assert.Equal(1, arity.Expected);
        Assert.Equal(2, arity.Actual);
    }

    [Fact]
    public void Eval_DirectCall_UsesAlgorithmLevelExplicitParameters()
    {
        var source = """
            Algo(x) = {
              Output = x + 1
            }
            Algo(6)
            """;

        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_DirectCall_MultiParameterAlgorithmLevelDefinition_SupportsExplicitOutput()
    {
        var source = """
            ImpactOnEarth(mass, height) = {
              Gravity = 9.81
              Output = mass * Gravity * height
            }
            ImpactOnEarth(3, 2)
            """;

        AssertEval(source, 58.86m);
    }

    [Fact]
    public void Eval_DirectCall_ShorthandBodyStillWorks()
    {
        AssertEval(
            """
            Algo(x) = x + 1
            Algo(6)
            """,
            7);
    }

    [Fact]
    public void Eval_DirectCall_UsesAlgorithmArityInDiagnostics()
    {
        AssertArityMismatchMessage(
            """
            Algo(x) = {
              Output = x + 1
            }
            Algo()
            """,
            "Property 'Algo' expects 1 parameter, but was called with 0 arguments.");
    }

    [Fact]
    public void Eval_DirectCall_ZeroParamExplicitOutput_PreservesExistingBehavior()
    {
        AssertEval(
            """
            Algo = {
              Output = 5
            }
            Algo()
            """,
            5);

        AssertArityMismatchMessage(
            """
            Algo = {
              Output = 5
            }
            Algo(6)
            """,
            "Property 'Algo' expects 0 parameters, but was called with 1 argument.");
    }

    [Fact]
    public void Eval_DirectCall_DoesNotMakeHelperCallableThroughAlgorithmName()
    {
        AssertArityMismatchMessage(
            """
            Algo = {
              Helper(x) = x * 2
              Output = 5
            }
            Algo(6)
            """,
            "Property 'Algo' expects 0 parameters, but was called with 1 argument.");
    }

    [Fact]
    public void Eval_DirectCall_PreservesHelperDotCall()
    {
        var source = """
            Algo = {
              Helper(x) = x * 2
              Output = 5
            }
            Algo.Helper(6)
            """;

        AssertEval(source, 12);
    }

        [Fact]
        public void Eval_NestedHelperCapture_RemainsCallableLocally()
        {
                AssertEval(
                        """
                        Algo(x) = {
                            Prop = x + 1
                            Prop * 2
                        }
                        Algo(6)
                        """,
                        14);
        }

        [Fact]
        public void Eval_ImplicitAndExplicitOuterOwnership_StayEquivalentForLocalUse()
        {
                AssertEval(
                        """
                        Algo = {
                            Prop = x + 1
                            x
                        }
                        Algo(6)
                        """,
                        6);

                AssertEval(
                        """
                        Algo(x) = {
                            Prop = x + 1
                            x
                        }
                        Algo(6)
                        """,
                        6);
        }

        [Fact]
        public void Eval_CapturedNestedProperty_DotAccess_IsLocalOnly()
        {
                AssertLocalOnlyPropertyMessage(
                        """
                        Algo(x) = {
                            Prop = x + 1
                            x
                        }
                        Algo.Prop
                        """,
                        "Property 'Prop' on `Algo` is local-only because it depends on parameter(s) owned by the enclosing algorithm.");
        }

        [Fact]
        public void Eval_CapturedNestedProperty_DotCall_IsLocalOnly()
        {
                AssertLocalOnlyPropertyMessage(
                        """
                        Algo(x) = {
                            Prop = x + 1
                            x
                        }
                        Algo.Prop(6)
                        """,
                        "Property 'Prop' on `Algo` is local-only because it depends on parameter(s) owned by the enclosing algorithm.");
        }

        [Fact]
        public void Eval_ImplicitlyOwnedCapturedNestedProperty_DotAccess_IsLocalOnly()
        {
                AssertLocalOnlyPropertyMessage(
                        """
                        Algo = {
                            Prop = x + 1
                            x
                        }
                        Algo.Prop
                        """,
                        "Property 'Prop' on `Algo` is local-only because it depends on parameter(s) owned by the enclosing algorithm.");
        }

    [Fact]
    public void Eval_ContainerWithParametrizedChildProperty_RemainsCallable()
    {
        AssertEval(
            """
            Algo = {
              Prop(x, y) = 7
            }
            Algo.Prop(1, 2)
            """,
            7);
    }

    [Fact]
    public void Eval_PlainContainerAlgorithm_RemainsValid()
    {
        AssertEval(
            """
            Algo = {
              Prop = 7
            }
            Algo.Prop
            """,
            7);
    }

    [Fact]
    public void Eval_DirectCall_NestedAlgorithmLevelDefinition_PreservesNestedCalls()
    {
        var source = """
            Outer = {
              Inner(x) = {
                Output = x + 10
              }
              Inner(5)
            }
            Outer, Outer.Inner(5)
            """;

        AssertEval(source, 15, 15);
    }

        [Fact]
        public void Eval_ConditionalBranchProperty_IsLocalOnly()
        {
                AssertLocalOnlyPropertyMessage(
                        """
                        Outer(0) = {
                            Inner = 1
                            0
                        }
                        Outer(x) = {
                            Inner = x + 1
                            x
                        }
                        Outer.Inner
                        """,
                        "Property 'Inner' on `Outer` is local-only because properties defined inside conditional algorithms are not publicly visible.");
        }

        [Fact]
        public void Eval_ConditionalBranchProperties_AreNeverExposedThroughParent()
        {
                AssertLocalOnlyPropertyMessage(
                        """
                        Outer(0) = {
                            First = 1
                            0
                        }
                        Outer(x) = {
                            Second = x + 1
                            x
                        }
                        Outer.Second
                        """,
                        "Property 'Second' on `Outer` is local-only because properties defined inside conditional algorithms are not publicly visible.");
        }

    [Fact]
    public void Eval_ManualAlgorithmWithExplicitParametersWithoutOutput_IsRejected()
    {
        var invalid = new Algorithm.User(
            Parent: null,
            Params: ["x"],
            Opens: [],
            Properties:
            [
                new Property(
                    "Prop",
                    new Algorithm.User(
                        Parent: null,
                        Params: [],
                        Opens: [],
                        Properties: [],
                        Output: [new Expr.Num(7m)]))
            ],
            Output: [])
        {
            ExplicitParameters = [new ParameterDeclaration("x", new SourceSpan(1, 6, 1, 6))]
        };

        var result = Evaluator.Run(new Expr.Block(invalid));

        Assert.True(result.IsError);
        Assert.IsType<EvalError.ExplicitParametersRequireOutput>(result.Error);
        Assert.Equal(
            AlgorithmValidation.ExplicitParametersRequireOutputMessage,
            KatLangError.FromEvalError(result.Error).Message);
    }

    [Fact]
    public void Eval_ManualOutputDotCall_IsRejected()
    {
        var callee = new Algorithm.User(
            Parent: null,
            Params: ["x"],
            Opens: [],
            Properties: [],
            Output: [new Expr.Binary(BinaryOp.Add, new Expr.Param("x"), new Expr.Num(1m))]);

        var root = new Algorithm.User(
            Parent: null,
            Params: [],
            Opens: [],
            Properties: [new Property("Algo", callee)],
            Output:
            [
                new Expr.DotCall(
                    new Expr.Resolve("Algo"),
                    "Output",
                    new Algorithm.User(Parent: null, Params: [], Opens: [], Properties: [], Output: [new Expr.Num(6m)]))
            ]);

        var result = Evaluator.Run(new Expr.Block(root));

        Assert.True(result.IsError);
        AssertInnermostSpecialOutputAccess(result.Error);
        Assert.Equal(
            "Output is the designated result of an algorithm and cannot be accessed through property syntax. Call the algorithm directly instead. Instead of `Algo.Output(...)`, write `Algo(...)`.",
            KatLangError.FromEvalError(result.Error).Message);
    }

    [Fact]
    public void Eval_ManualNestedOutputDotCall_UsesReceiverSpecificGuidance()
    {
        var inner = new Algorithm.User(
            Parent: null,
            Params: ["x"],
            Opens: [],
            Properties: [],
            Output: [new Expr.Binary(BinaryOp.Add, new Expr.Param("x"), new Expr.Num(10m))]);

        var outer = new Algorithm.User(
            Parent: null,
            Params: [],
            Opens: [],
            Properties: [new Property("Inner", inner)],
            Output: []);

        var root = new Algorithm.User(
            Parent: null,
            Params: [],
            Opens: [],
            Properties: [new Property("Outer", outer)],
            Output:
            [
                new Expr.DotCall(
                    new Expr.DotCall(new Expr.Resolve("Outer"), "Inner"),
                    "Output",
                    new Algorithm.User(Parent: null, Params: [], Opens: [], Properties: [], Output: [new Expr.Num(6m)]))
            ]);

        var result = Evaluator.Run(new Expr.Block(root));

        Assert.True(result.IsError);
        AssertInnermostSpecialOutputAccess(result.Error);
        Assert.Equal(
            "Output is the designated result of an algorithm and cannot be accessed through property syntax. Call the algorithm directly instead. Instead of `Outer.Inner.Output(...)`, write `Outer.Inner(...)`.",
            KatLangError.FromEvalError(result.Error).Message);
    }

    [Fact]
    public void Eval_ClauseDefinition_GroupedPattern_RemainsConditionalWholeArgument()
    {
        var source = """
            Stats(x, (acc, counter)) = (x + acc, counter + 1)
            Stats(3, (0, 0))
            """;

        AssertEval(source, 3, 1);
    }

    [Fact]
    public void Eval_ClauseGroup_LiteralThenPlainBinder_RemainsConditional()
    {
        var source = """
            F(0) = 0
            F(x) = 1
            F(2)
            """;

        AssertEval(source, 1);
    }

    // ── Inline block arguments (higher-order) ────────────────────────────────

    [Fact]
    public void Eval_InlineBlock_PassedInParens()
    {
        // Apply = func(x); Apply({a + 1}, 5) → {a+1}(5) → 6
        AssertEval("Apply = func(x)\nApply({a + 1}, 5)", 6);
    }

    [Fact]
    public void Eval_InlineBlock_DotCall_PassedInParens()
    {
        // A.Apply = func(x); A.Apply({a + 1}, 5) → 6
        var source = """
            A = (Apply = func(x)
            0)
            A.Apply({a + 1}, 5)
            """;
        AssertEvalAllPublic(source, 6);
    }

    [Fact]
    public void Eval_InlineBlock_ZeroParamInParens()
    {
        // Use = func; Use({42}) → 42
        AssertEval("Use = func\nUse({42})", 42);
    }

    [Fact]
    public void Eval_InlineBlock_TrailingBrace_SingleArg()
    {
        // Algo = func(9); Algo{a + 1} → {a+1}(9) → 10
        AssertEval("Algo = func(9)\nAlgo{a + 1}", 10);
    }

    [Fact]
    public void Eval_InlineBlock_TrailingBrace_ZeroParam()
    {
        // Use = func; Use{42} → 42
        AssertEval("Use = func\nUse{42}", 42);
    }

    [Fact]
    public void Eval_InlineBlock_TrailingBrace_ArityMismatch()
    {
        // Use = func; Use{a + 1} → block has param a, bare usage → arityMismatch
        AssertEvalFails("Use = func\nUse{a + 1}");
    }

    // ── Explicit output syntax ──────────────────────────────────────────────

    [Fact]
    public void Eval_ExplicitOutput_BasicForm()
    {
        // Explicit: Output = A should work the same as implicit A
        AssertEval("A = 6\nOutput = A", 6);
    }

    [Fact]
    public void Eval_ExplicitOutput_NumericLiteral()
    {
        AssertEval("Output = 42", 42);
    }

    [Fact]
    public void Eval_ExplicitOutput_Expression()
    {
        AssertEval("A = 3\nOutput = A + 1", 4);
    }

    [Fact]
    public void Eval_ExplicitOutput_InMiddleOfProperties()
    {
        // Output defined between properties should still work
        AssertEval("A = 1\nOutput = A + B\nB = 2", 3);
    }

    [Fact]
    public void Eval_ExplicitOutput_MultipleValues()
    {
        AssertEval("Output = 1, 2, 3", 1, 2, 3);
    }

    [Fact]
    public void Eval_ExplicitOutput_EquivalentToImplicit()
    {
        // Both forms should produce the same result
        var implicitResult = Eval("A = 6\nA");
        var explicitResult = Eval("A = 6\nOutput = A");
        Assert.True(implicitResult.IsOk);
        Assert.True(explicitResult.IsOk);
        Assert.Equal(implicitResult.Value, explicitResult.Value);
    }

    [Fact]
    public void Eval_ExplicitOutput_InsideBlock()
    {
        var source = """
            X = {
              A = 3
              Output = A + 1
              B = 2
            }
            X
            """;
        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_ExplicitOutput_WithParametrizedProperty()
    {
        // Explicit output with a property that has implicit params
        AssertEval("Add = x + y\nOutput = Add(3, 4)", 7);
    }

    [Fact]
    public void Eval_ImplicitOutput_StillWorks()
    {
        // Ensure implicit output is unaffected
        AssertEval("A = 6\nA", 6);
    }

    // ── if builtin ───────────────────────────────────────────────────────────────

    [Fact]
    public void Eval_If3_TrueCondition_ReturnsThenBranch()
        => AssertEval("if(1 == 1, 5, 6)", 5);

    [Fact]
    public void Eval_If3_FalseCondition_ReturnsElseBranch()
        => AssertEval("if(1 == 2, 5, 6)", 6);

    [Fact]
    public void Eval_If3_TrueInAddition()
        => AssertEval("10 + if(1 == 1, 5, 0)", 15);

    [Fact]
    public void Eval_If3_FalseInAddition()
        => AssertEval("10 + if(1 == 2, 5, 0)", 10);

    [Fact]
    public void Eval_If3_CompatibleWithEarlierCoverage_True()
        => AssertEval("if(1 == 1, 5, 6)", 5);

    [Fact]
    public void Eval_If3_CompatibleWithEarlierCoverage_False()
        => AssertEval("if(1 == 2, 5, 6)", 6);

    [Fact]
    public void Eval_If2_RuntimeBuiltinCall_FailsWithExplicitArityMessage()
    {
        var expr = new Expr.Call(
            new Expr.Resolve("if"),
            new Algorithm.User(
                Parent: null,
                Params: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Num(1), new Expr.Num(5)]));

        var result = Evaluator.Run(expr);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("Builtin 'if' expects 3 arguments: condition, whenTrue, whenFalse.", formatted);
    }

    [Fact]
    public void Eval_If2_RuntimeBuiltinCallInBinary_FailsInsteadOfPropagatingEmptyResult()
    {
        var expr = new Expr.Binary(
            BinaryOp.Mul,
            new Expr.Num(10),
            new Expr.Call(
                new Expr.Resolve("if"),
                new Algorithm.User(
                    Parent: null,
                    Params: [],
                    Opens: [],
                    Properties: [],
                    Output:
                    [
                        new Expr.Binary(BinaryOp.Lt, new Expr.Num(7), new Expr.Num(6)),
                        new Expr.Num(1),
                    ])));

        var result = Evaluator.Run(expr);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("Builtin 'if' expects 3 arguments: condition, whenTrue, whenFalse.", formatted);
    }

    // ── Clause definitions and conditional algorithms ───────────────────────

    [Fact]
    public void Eval_ClauseDefinition_KCombinator_OrdinarySingleClause()
    {
        // K(a, b) = a  ⟹  K(10, 20) => 10
        var source = """
            K(a, b) = a
            K(10, 20)
            """;
        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_ClauseDefinition_SecondProjection_OrdinarySingleClause()
    {
        // Verify we can return the second binding too
        var source = """
            Snd(a, b) = b
            Snd(10, 20)
            """;
        AssertEval(source, 20);
    }

    [Fact]
    public void Eval_Conditional_SingletonGroupPattern_MatchesSingleElementTuple()
    {
        // K(a, (b)) = a  ⟹  K(1, (2, 3)) should fail
        // because (b) is a 1-element group pattern that does not match (2, 3).
        var source = """
            K(a, (b)) = a
            K(1, (2, 3))
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);
        Assert.IsType<EvalError.WithContext>(error);
        var inner = ((EvalError.WithContext)error!).Inner;
        Assert.IsType<EvalError.NoMatchingBranch>(inner);
    }

    [Fact]
    public void Eval_ClauseDefinition_OrdinarySingleClause_AcceptsGroupedSecondArgument()
    {
        // K(a, b) = a  ⟹  K(1, (2, 3)) => 1
        // Ordinary call binding still accepts a grouped second argument as one value.
        var source = """
            K(a, b) = a
            K(1, (2, 3))
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Conditional_SingletonGroupPattern_MatchesNormalizedSingleton()
    {
        // K(a, (b)) = a  ⟹  K(1, (2)) => 1
        // (2) normalizes to Atom(2); (b) is a 1-element group pattern
        // that matches the normalized singleton.
        var source = """
            K(a, (b)) = a
            K(1, (2))
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Conditional_MultipleBranches_LiteralMatch()
    {
        // Else(1, (a, b)) = a
        // Else(c, (a, b)) = b
        var source = """
            Else(1, (a, b)) = a
            Else(c, (a, b)) = b
            Else(1, (2, 3))
            """;
        AssertEval(source, 2);
    }

    [Fact]
    public void Eval_Conditional_MultipleBranches_FallbackBranch()
    {
        // Same as above but first branch doesn't match (c != 1)
        var source = """
            Else(1, (a, b)) = a
            Else(c, (a, b)) = b
            Else(0, (2, 3))
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Conditional_NonExhaustive_NoMatch()
    {
        // Sign(1) = 1
        // Sign(-1) = -1
        // Sign(0) should fail with NoMatchingBranch
        var source = """
            Sign(1) = 1
            Sign(-1) = -1
            Sign(0)
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);
        Assert.IsType<EvalError.WithContext>(error);
        var inner = ((EvalError.WithContext)error!).Inner;
        Assert.IsType<EvalError.NoMatchingBranch>(inner);
    }

    [Fact]
    public void Eval_Conditional_NonExhaustive_MatchExists()
    {
        var source = """
            Sign(1) = 100
            Sign(-1) = -100
            Sign(1)
            """;
        AssertEval(source, 100);
    }

    [Fact]
    public void Eval_Conditional_FirstMatchWins()
    {
        // F(x) = 1  (catch-all, always matches)
        // F(1) = 2  (never reached)
        // F(1) => 1 (first branch wins)
        var source = """
            F(x) = 1
            F(1) = 2
            F(1)
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Conditional_NestedPatternShapeMismatch()
    {
        // Else expects (c, (a, b)) but we pass three flat args
        var source = """
            Else(1, (a, b)) = a
            Else(c, (a, b)) = b
            Else(1, 2, 3)
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);
        Assert.IsType<EvalError.WithContext>(error);
        var inner = ((EvalError.WithContext)error!).Inner;
        Assert.IsType<EvalError.NoMatchingBranch>(inner);
    }

    [Fact]
    public void Eval_Conditional_OrdinaryAlgorithmUnchanged()
    {
        // Ordinary (non-conditional) algorithms should still work
        var source = """
            Add = a + b
            Add(3, 4)
            """;
        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_Conditional_BinderUsedInExpression()
    {
        // Branch body can use binders in arithmetic
        var source = """
            Double(x) = x + x
            Double(5)
            """;
        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Conditional_NegativeLiteralPattern()
    {
        var source = """
            F(-1) = 100
            F(x) = 0
            F(-1)
            """;
        AssertEval(source, 100);
    }

    [Fact]
    public void Eval_Conditional_NegativeLiteralPattern_NoMatch()
    {
        var source = """
            F(-1) = 100
            F(x) = 0
            F(5)
            """;
        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_Conditional_MultipleOutputInBranch()
    {
        // Branch body returns multiple values
        var source = """
            Swap(a, b) = b, a
            Swap(1, 2)
            """;
        AssertEval(source, 2, 1);
    }

    [Fact]
    public void Eval_Conditional_DotCallAccess()
    {
        // Access conditional property via dot syntax with args
        var source = """
            M = (F(x) = x + 1
            F)
            M.F(10)
            """;
        AssertEval(source, 11);
    }

    [Fact]
    public void Eval_Conditional_SingleArg()
    {
        // Single argument pattern
        var source = """
            Inc(x) = x + 1
            Inc(5)
            """;
        AssertEval(source, 6);
    }

    // ── Regression: conditional branch body accesses enclosing scope (issue #19) ──

    [Fact]
    public void Eval_Conditional_BranchBody_AccessesSiblingProperty()
    {
        // Branch bodies must be able to read sibling properties of the enclosing algorithm.
        // Before the fix, branch.Body had no parent wiring → UnknownName for Price.
        var source = """
            Price = 0.80
            Discount(1) = Price * 0.9
            Discount(x) = Price
            Discount(1)
            """;
        AssertEval(source, 0.72m);
    }

    [Fact]
    public void Eval_Conditional_BranchBody_AccessesSiblingProperty_AllBranches()
    {
        // Verify every branch (not just the first) can access sibling properties.
        var source = """
            TomatoPrice = 1.20
            ApplePrice = 0.80
            CucumberPrice = 0.60
            Expense(1, qty) = TomatoPrice * qty
            Expense(2, qty) = ApplePrice * qty
            Expense(3, qty) = CucumberPrice * qty
            Expense(1, 10), Expense(2, 10), Expense(3, 10)
            """;
        AssertEval(source, 12.0m, 8.0m, 6.0m);
    }

    [Fact]
    public void Eval_Conditional_BranchBody_AccessesGrandparentProperty()
    {
        // Sibling properties defined one level higher than the conditional algorithm
        // must also be reachable from branch bodies.
        var source = """
            Outer = {
                Price = 2.50
                Inner = {
                    F(x) = Price * x
                    F(4)
                }
                Inner
            }
            Outer
            """;
        AssertEval(source, 10.0m);
    }

    [Fact]
    public void Eval_Conditional_BranchBody_BinderAndSiblingCombined()
    {
        // Branch body uses both a pattern binder (qty) and a sibling property (Rate).
        var source = """
            Rate = 1.5
            Scale(qty) = Rate * qty
            Scale(4)
            """;
        AssertEval(source, 6.0m);
    }

    // ── Full-input-specification rule: conditional branch params ─────────

    [Fact]
    public void Eval_ClauseDefinition_OrdinarySingleClause_IgnoredBinderPreserved()
    {
        // K(a, b) = a — b is intentionally unused, no error
        var source = """
            K(a, b) = a
            K(10, 20)
            """;
        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Conditional_FullPattern_StructuredBranches()
    {
        // Each branch pattern fully describes accepted input shape
        var source = """
            Else(1, (a, b)) = a
            Else(c, (a, b)) = b
            Else(1, (20, 30))
            """;
        AssertEval(source, 20);
    }

    [Fact]
    public void Eval_Conditional_FullPattern_CatchAllBranch()
    {
        var source = """
            Else(1, (a, b)) = a
            Else(c, (a, b)) = b
            Else(0, (20, 30))
            """;
        AssertEval(source, 30);
    }

    [Fact]
    public void Eval_Conditional_ExtraImplicitParam_Rejected()
    {
        // F(1, a) = a + b — b is not bound by pattern and not a resolved name
        // This must fail because b is not a pattern binder and not lexically resolvable.
        var source = """
            F(1, a) = a + b
            F(1, 5)
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);
    }

    [Fact]
    public void Eval_Conditional_FreeIdResolvedLexically_Succeeds()
    {
        // Pattern binder + lexically resolvable name: Rate is a sibling property
        var source = """
            Rate = 2
            F(x) = x * Rate
            F(5)
            """;
        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Conditional_OrdinaryAlgorithmStillInfersParams()
    {
        // Ordinary (non-conditional) algorithms still infer implicit parameters
        var source = """
            Add = a + b
            Add(3, 4)
            """;
        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_Conditional_OrdinaryAlgorithmGraceStillWorks()
    {
        // Grace still works in ordinary algorithms
        var source = """
            Sub = a - ~b
            Sub(3, 10)
            """;
        AssertEval(source, 7);
    }

    // ── Uniform top-level output arity: valid multi-output branches ─────

    [Fact]
    public void Eval_Conditional_SameOutputArity2_BothBranches()
    {
        // Both branches return top-level arity 2 — valid
        var source = """
            F(1, x) = x, x + 1
            F(2, x) = 0, x
            F(1, 5)
            """;
        AssertEval(source, 5, 6);
    }

    [Fact]
    public void Eval_Conditional_SameOutputArity2_SecondBranch()
    {
        // Second branch matches, also returns arity 2
        var source = """
            F(1, x) = x, x + 1
            F(2, x) = 0, x
            F(2, 5)
            """;
        AssertEval(source, 0, 5);
    }

    [Fact]
    public void Eval_Conditional_SameOutputArity1_WithSiblingProperties()
    {
        // Classic example: same output arity 1 across branches with sibling properties
        var source = """
            TomatoPrice = 1.20
            ApplePrice = 0.80
            Expense(1, qty) = TomatoPrice * qty
            Expense(2, qty) = ApplePrice * qty
            Expense(1, 10)
            """;
        AssertEval(source, 12.0m);
    }

    [Fact]
    public void Eval_Conditional_SameOutputArity2_NestedStructureDiffers()
    {
        // Both branches return top-level arity 2; nested internal structure differs — valid
        var source = """
            G(1, x) = x, (x + 1, x + 2)
            G(2, x) = x, x * 2
            G(1, 10)
            """;
        AssertEval(source, 10, 11, 12);
    }

    // ── Additional conditional algorithm tests ──────────────────────────────

    [Fact]
    public void Eval_Conditional_DefinitionAndCallDisambiguated()
    {
        // First two lines: definitions; third line: call
        var source = """
            F(1) = 100
            F(x) = 0
            F(1)
            """;
        AssertEval(source, 100);
    }

    [Fact]
    public void Eval_Conditional_CallInExpressionContext()
    {
        // G = F(1) is a property definition where F(1) is a call expression
        var source = """
            F(1) = 100
            F(x) = 0
            G = F(1)
            G
            """;
        AssertEval(source, 100);
    }

    [Fact]
    public void Eval_ConditionalSugar_FirstMatchWins()
    {
        var source = """
            F(x) = 1
            F(1) = 2
            F(1)
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_ConditionalSugar_ExtraImplicitParam_Rejected()
    {
        // b is not bound in the pattern; should be rejected
        var source = """
            F(1, a) = a + b
            F(2, a) = a
            F(1, 5)
            """;
        var parseResult = Parser.Parse(source);
        Assert.True(parseResult.HasErrors);
        Assert.Contains(parseResult.Diagnostics, d =>
            d.Message.Contains("Identifier 'b' is used in conditional branch 'F'") &&
            d.Message.Contains("not declared in the branch pattern") &&
            d.Message.Contains("A(y) = y"));
    }

    [Fact]
    public void Eval_Conditional_ClauseSyntax_MultipleCallResults()
    {
        // Clause-style branch syntax works for multiple calls
        var source = """
            F(1) = 100
            F(x) = 0
            F(1), F(42)
            """;
        AssertEval(source, 100, 0);
    }

    // ── String literals: first-class value tests ────────────────────────────

    [Fact]
    public void Eval_String_SimpleLiteral()
    {
        AssertEvalString("'hello'", "hello");
    }

    [Fact]
    public void Eval_String_EmptyLiteral()
    {
        AssertEvalString("''", "");
    }

    [Fact]
    public void Eval_String_PropertyBinding()
    {
        AssertEvalString("""
            A = 'hello'
            A
            """, "hello");
    }

    [Fact]
    public void Eval_String_EqualityTrue()
    {
        AssertEval("'a' == 'a'", 1);
    }

    [Fact]
    public void Eval_String_EqualityFalse()
    {
        AssertEval("'a' == 'b'", 0);
    }

    [Fact]
    public void Eval_String_EqualityCaseSensitive()
    {
        // 'Apples' != 'apples' — exact, case-sensitive comparison
        AssertEval("'Apples' == 'apples'", 0);
    }

    [Fact]
    public void Eval_String_Inequality()
    {
        AssertEval("'a' != 'b'", 1);
    }

    [Fact]
    public void Eval_String_InequalitySame()
    {
        AssertEval("'a' != 'a'", 0);
    }

    [Fact]
    public void Eval_String_ArgumentCall()
    {
        // Echo = x, Echo('hello') should return the string
        AssertEvalString("""
            Echo = x
            Echo('hello')
            """, "hello");
    }

    [Fact]
    public void Eval_String_ConditionalDispatch()
    {
        AssertEval("""
            Price('apples') = 0.80
            Price('apples')
            """, 0.80m);
    }

    [Fact]
    public void Eval_String_ConditionalDispatch_MultiBranch()
    {
        AssertEval("""
            Price('tomatoes') = 1.20
            Price('apples') = 0.80
            Price('cucumbers') = 0.60
            Price('cucumbers')
            """, 0.60m);
    }

    [Fact]
    public void Eval_String_ConditionalDispatch_IndirectCall()
    {
        // Item = 'apples', Price('apples') = 0.80, Price(Item) should resolve
        AssertEval("""
            Item = 'apples'
            Price('apples') = 0.80
            Price(Item)
            """, 0.80m);
    }

    [Fact]
    public void Eval_String_ReturnFromAlgorithm()
    {
        AssertEvalString("""
            Name = 'KatLang'
            Name
            """, "KatLang");
    }

    [Fact]
    public void Eval_String_ConditionalExpense()
    {
        // Full example from spec: Price('apples') = 0.80, Expense = Price(item) * quantity
        AssertEval("""
            Price('tomatoes') = 1.20
            Price('apples') = 0.80
            Price('cucumbers') = 0.60
            Expense = Price(item) * quantity
            Expense('apples', 3)
            """, 2.40m);
    }

    [Fact]
    public void Eval_String_ConditionalNoMatch_Fails()
    {
        // Unmatched branch fails with NoMatchingBranch, not a crash
        AssertEvalFails("""
            Price('apples') = 0.80
            Price('bananas')
            """);
    }

    [Fact]
    public void Eval_String_MixedBranches_NumericAndString()
    {
        // Conditional with both numeric and string literal patterns
        AssertEval("""
            F('a') = 1
            F(0) = 2
            F('a')
            """, 1);
    }

    [Fact]
    public void Eval_String_MixedBranches_NumericAndString_MatchNumeric()
    {
        AssertEval("""
            F('a') = 1
            F(0) = 2
            F(0)
            """, 2);
    }

    [Fact]
    public void Eval_String_BinderFallbackAfterStringLiteral()
    {
        // Binder pattern as fallback after string literal patterns
        AssertEval("""
            F('a') = 1
            F(x) = 0
            F('b')
            """, 0);
    }

    // ── String literals: negative/error tests ───────────────────────────────

    [Fact]
    public void Eval_String_MultiplyFails()
    {
        // 'a' * 3 should fail (strings don't support arithmetic)
        AssertEvalFailsWithTypeMismatch("'a' * 3", "string and non-string");
    }

    [Fact]
    public void Eval_String_AddNumberFails()
    {
        // 1 + 'a' should fail (mixed types)
        AssertEvalFailsWithTypeMismatch("1 + 'a'", "string and non-string");
    }

    [Fact]
    public void Eval_String_AddStringsFails()
    {
        // 'a' + 'b' should fail (no string concatenation)
        AssertEvalFailsWithTypeMismatch("'a' + 'b'", "only support == and !=");
    }

    [Fact]
    public void Eval_String_UnaryMinusFails()
    {
        // Unary minus on a string literal should fail
        var strExpr = new Expr.StringLiteral("hello");
        var unaryExpr = new Expr.Unary(UnaryOp.Minus, strExpr);
        var alg = new Algorithm.User(Parent: null, Params: [], Opens: [],
            Properties: [], Output: [unaryExpr]);
        var result = Evaluator.Run(new Expr.Block(alg));
        Assert.True(result.IsError);
        var error = result.Error;
        while (error is EvalError.WithContext wc) error = wc.Inner;
        var tm = Assert.IsType<EvalError.TypeMismatch>(error);
        Assert.Contains("not supported for strings", tm.Message);
    }

    [Fact]
    public void Eval_String_ComparisonLtFails()
    {
        // 'a' < 'b' should fail (no string ordering)
        AssertEvalFailsWithTypeMismatch("'a' < 'b'", "only support == and !=");
    }

    [Fact]
    public void Eval_String_MixedEqualityFails()
    {
        // 1 == 'a' should fail (mixed types in equality)
        AssertEvalFailsWithTypeMismatch("1 == 'a'", "string and non-string");
    }

    [Fact]
    public void Eval_String_SinFails()
    {
        // Math.Sin('a') should fail with type mismatch (builtin expects numeric argument)
        AssertEvalFailsWithTypeMismatch("Math.Sin('a')", "Expected a number, got a string");
    }

    // ── Top-level unresolved implicit parameters ──

    [Fact]
    public void Eval_TopLevel_SingleImplicitParam_ErrorMessage()
    {
        var result = EvalFull("a + 1");
        if (result.IsOk)
            Assert.Fail($"Expected error but got: {result.Value}");
        var error = result.Error;
        var uip = Assert.IsType<EvalError.UnresolvedImplicitParams>(error);
        Assert.Equal(["a"], uip.ParamNames);
        var formatted = KatLangError.FromEvalError(error).Message;
        Assert.Contains("Identifier 'a' does not resolve to a property or other visible name here", formatted);
        Assert.Contains("KatLang interprets it as an implicit parameter", formatted);
        Assert.Contains("Its value is provided by the caller", formatted);
        Assert.Contains("No argument was provided", formatted);
        Assert.Contains("expected 1 argument, got 0", formatted);
        Assert.DoesNotContain("not defined in the current scope", formatted);
    }

    [Fact]
    public void Eval_TopLevel_MultipleImplicitParams_ErrorMessage()
    {
        var result = EvalFull("a + b");
        if (result.IsOk)
            Assert.Fail($"Expected error but got: {result.Value}");
        var error = result.Error;
        var uip = Assert.IsType<EvalError.UnresolvedImplicitParams>(error);
        Assert.Equal(2, uip.ParamNames.Count);
        var formatted = KatLangError.FromEvalError(error).Message;
        Assert.Contains("Identifiers 'a' and 'b' do not resolve to properties or other visible names here", formatted);
        Assert.Contains("KatLang interprets them as implicit parameters", formatted);
        Assert.Contains("Their values are provided by the caller", formatted);
        Assert.Contains("No arguments were provided", formatted);
        Assert.Contains("expected 2 arguments, got 0", formatted);
        Assert.DoesNotContain("not defined in the current scope", formatted);
    }

    [Fact]
    public void Eval_InnerCall_ArityMismatch_StillGeneric()
    {
        // A normal arity mismatch inside a call (too many args) should NOT be UnresolvedImplicitParams
        var source = """
            G(x) = x + 1
            G(1, 2)
            """;
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected error but got: {result.Value}");
        var error = result.Error;
        while (error is EvalError.WithContext wc)
            error = wc.Inner;
        Assert.IsNotType<EvalError.UnresolvedImplicitParams>(error);
    }
}
