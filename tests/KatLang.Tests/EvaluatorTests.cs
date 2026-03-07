namespace KatLang.Tests;

public class EvaluatorTests
{
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
                new Property(p.Name, MakeAllPublic(p.Value), IsPublic: true)).ToList(),
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
        Expr.Prop(var t, var n) => new Expr.Prop(MakeAllPublicExpr(t), n) { Span = expr.Span },
        _ => expr,
    };

    private static void AssertEval(string source, params decimal[] expected)
    {
        var result = Eval(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal(expected, result.Value);
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
        // Grace (~a) reorders detected params [b, a, sum] -> [a, b, sum].
        // Initial state (1, 2, 0): a=1, b=2, sum=0.
        // The step with b=144 (first even Fibonacci > 100) triggers cont=0;
        // pre-check semantics return the prior state (sum=44), not the updated one.
        var source = """
            Algo = b, ~a + b, sum + if(b mod 2 == 0, b, 0), b <= 100
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

    // â”€â”€ While dotCall double-parens grouping â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_While_DotCall_BareComma_Fails()
    {
        // Test B: Algo.while(x, 0) with single parens â†’ 2 separate args â†’ arity mismatch
        var source = """
            Algo = n - 1, result + if(n mod 3==0 or n mod 5==0, n, 0), n > 2
            Sum = Algo.while(x, 0) : 1
            Sum(999)
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_While_DotCall_DoubleParens()
    {
        // Test A: Algo.while((x, 0)) double-parens groups (x, 0) as single init argument
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
    public void Eval_While_DotCall_DoubleParens_NoParams()
    {
        // x inside ((x, 0)) must NOT become a param of the synthetic block;
        // it resolves from the enclosing algorithm's scope
        var source = """
            Algo = n - 1, result + if(n mod 3==0 or n mod 5==0, n, 0), n > 2
            Sum = Algo.while((x, 0)) : 1
            Sum(999)
            """;
        AssertEval(source, 233168);
    }

    // â”€â”€ Atoms builtin â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Atoms_FlattensGroups()
        => AssertEval("atoms(((1, 2), (3, 4)))", 1, 2, 3, 4);

    [Fact]
    public void Eval_Atoms_SingleValue()
        => AssertEval("atoms((5))", 5);

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
            Add = a + 1, sum + Numbers:a
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
        Assert.Equal((decimal)Math.PI, result.Value[0]);
    }

    [Fact]
    public void Eval_MathE_ReturnsMathE()
    {
        var result = Eval("Math.E");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal((decimal)Math.E, result.Value[0]);
    }

    [Fact]
    public void Eval_MathPi_InExpression()
    {
        var result = Eval("Math.Pi * 2");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal((decimal)Math.PI * 2, result.Value[0]);
    }

    [Fact]
    public void Eval_MathE_InExpression()
    {
        var result = Eval("Math.E + 1");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal((decimal)Math.E + 1, result.Value[0]);
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
        Assert.Equal((decimal)Math.PI * 2 * 5, result.Value[0]);
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
    public void Eval_MathAtan()
    {
        var result = Eval("Math.Atan(1)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal((decimal)(Math.PI / 4), result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathSqrt_InExpression()
        => AssertEval("Math.Sqrt(16) + 1", 5);

    [Fact]
    public void Eval_MathFn_ViaOpen()
    {
        var source = """
            open = Math
            Abs(-5)
            """;
        AssertEval(source, 5);
    }

    [Fact]
    public void Eval_MathFn_ViaOpen_TwoParam()
    {
        var source = """
            open = Math
            Pow(2, 8)
            """;
        AssertEval(source, 256);
    }

    // â”€â”€ Open resolution â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Open_MathPi()
    {
        var source = """
            open = Math
            Pi
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal((decimal)Math.PI, result.Value[0]);
    }

    [Fact]
    public void Eval_Open_MathE()
    {
        var source = """
            open = Math
            E
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal((decimal)Math.E, result.Value[0]);
    }

    [Fact]
    public void Eval_Open_MathInExpression()
    {
        var source = """
            open = Math
            Pi * 2
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal((decimal)Math.PI * 2, result.Value[0]);
    }

    [Fact]
    public void Eval_Open_UserDefinedModule()
    {
        var source = """
            M = (public X = 42
            X)
            open = M
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
            open = A; B
            X + Y
            """;
        AssertEvalAllPublic(source, 3);
    }

    [Fact]
    public void Eval_Open_MissingProperty_Fails()
    {
        var source = """
            open = Math
            Foo
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_Open_InPropertyBody()
    {
        var source = """
            open = Math
            Circumference = Pi * 2 * r
            Circumference(5)
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal((decimal)Math.PI * 2 * 5, result.Value[0]);
    }

    [Fact]
    public void Eval_Open_DirectFunctionOpen()
    {
        var source = """
            Lib = (public F = x + 1)
            open = Lib
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
            open = Lib
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
              open = Lib
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
              open = Lib
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
            open = Lib
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

    // â”€â”€ Division, mod, power â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

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
        => AssertEval("2 ^ -1", 0);  // Lean: if y < 0 then 0

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
    public void Eval_UnknownIdentifier_ReturnsUnknownNameError()
    {
        var err = GetEvalError("Sum");
        Assert.NotNull(err);
        while (err is EvalError.WithContext wc)
            err = wc.Inner;
        Assert.IsType<EvalError.UnknownName>(err);
        Assert.Equal("Sum", ((EvalError.UnknownName)err).Name);
    }

    [Fact]
    public void Eval_UnknownIdentifier_HasCorrectSpan()
    {
        var err = GetEvalError("Sum");
        Assert.NotNull(err);
        // The outermost error should carry the Span
        Assert.NotNull(err.Span);
        Assert.Equal(1, err.Span.StartLineNumber);
        Assert.Equal(1, err.Span.StartColumn);
        Assert.Equal(1, err.Span.EndLineNumber);
        Assert.Equal(3, err.Span.EndColumn);
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
    public void Eval_UnknownIdentifier_MultiLine_HasCorrectSpan()
    {
        var source = """
            X = 5
            Y
            """;
        var err = GetEvalError(source);
        Assert.NotNull(err);
        Assert.NotNull(err.Span);
        Assert.Equal(2, err.Span.StartLineNumber);
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
            open = A, B
            X + Y
            """;
        AssertEvalAllPublic(source, 3);
    }

    [Fact]
    public void Eval_Open_UnbracketedCommaList_ResolvesFromSecondLib()
    {
        // open = Lib2, Lib3 â†’ two separate opens; Val3 resolves from Lib3
        var source = """
            Lib2 = (public Val2 = 20)
            Lib3 = (public Val3 = 30)
            open = Lib2, Lib3
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
            open = A, B
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
            open = Lib
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
            open = A; B
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
                open = Inner
                W = Z
            )
            open = Lib1
            Z
            """;
        // Z is not transitively visible â†’ fail
        AssertEvalAllPublicFails(source);
    }

    [Fact]
    public void Eval_Open_SelfInOpenExpression_Fails()
    {
        // Lean: resolveAlgDirect returns error for self (illegalInOpen "self").
        // self.HiddenLib would allow the algorithm to open its own property,
        // leaking names that should only be reachable via explicit property access.
        // The open must fail, so X is unreachable.
        //
        // Lean equivalent:
        //   alg [] [prop self "HiddenLib"] [("HiddenLib", alg [] [] [("X", alg [] [] [] [num 42])] [])] [resolve "X"]
        var source = """
            HiddenLib = (X = 42)
            open = self.HiddenLib
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
                open = Lib
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
                open = Lib
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
            open = Lib
            X
            """;
        AssertEval(source, 42);

        // Now try Y (private) â€” should fail
        var sourceY = """
            public Lib = (public X = 42
            Y = 99)
            open = Lib
            Y
            """;
        AssertEvalFails(sourceY);
    }

    [Fact]
    public void Eval_Visibility_NotPublicPropertyOnPrivateIntermediate()
    {
        // open = Lib.Sub where Sub exists but is private â†’ NotPublicProperty.
        // Lib doesn't need public (it's in the ownership chain), but Sub must
        // be public because it's an intermediate on the open path.
        var source = """
            Lib = (Sub = (public X = 42
            X))
            open = Lib.Sub
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
            open = Lib.Sub
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
            open = Lib.Sub()
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
            open = Lib2, Lib3
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
            open = Lib.Sub
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
                open = Lib
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
            open = A, B
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
            open = Lib
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
            open = Lib
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
            open = Lib
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
            open = Lib
            X
            """;
        AssertEval(source, 1);

        // Y is private, should fail
        var sourceY = """
            public Lib = (public X = 1
            Y = 2)
            open = Lib
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
            open = Lib
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
            open = Lib
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
            open = Lib
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
            open = Lib
            F = val + 1
            F
            """;
        AssertEval(source, 43);
    }

    // â”€â”€ Fix: resolveAlgForOpen public-only lookup â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Open_PrivateAlgorithm_FailsWithNotPublicProperty()
    {
        // Lean: lookupLexicalDirectUnwiredPublic rejects private open targets
        var source = """
            Lib = (public val = 42)
            open = Lib
            val
            """;
        // Lib is private â†’ open should fail with NotPublicProperty
        var result = Eval(source);
        Assert.True(result.IsError);
    }

    [Fact]
    public void Eval_Open_PublicAlgorithm_Succeeds()
    {
        // Public open target should work
        var source = """
            public Lib = (public val = 42)
            open = Lib
            val
            """;
        AssertEval(source, 42);
    }

    // â”€â”€ Fix: BinaryOp.Pow negative exponent guard â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Pow_NegativeExponent_ReturnsZero()
    {
        // Lean: if y < 0 then 0 else intPow x y.toNat
        AssertEval("2 ^ -1", 0);
    }

    [Fact]
    public void Eval_Pow_ZeroExponent_ReturnsOne()
    {
        AssertEval("5 ^ 0", 1);
    }

    [Fact]
    public void Eval_Pow_PositiveExponent_Works()
    {
        AssertEval("2 ^ 10", 1024);
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
    public void Eval_NetSalary_DotCallIncomeTax()
    {
        // NetSalary.IncomeTax(1000, 2) works because:
        // 1. Navigation-only: dot finds IncomeTax inside NetSalary, args bind directly
        // 2. ImplicitArgumentResolver transitively propagates params through sibling
        //    property chains: IncomeTax â†’ TaxableIncome â†’ NonTaxableMinimum (grossSalary),
        //                                                ChildTaxCredit (numberOfChildren)
        // SocialSecurityTax = 1000 * 0.105 = 105
        // NonTaxableMinimum = 1000 - 105 - 75 = 820
        // ChildTaxCredit = 2 * 162 = 324
        // TaxableIncome = 820 - 324 = 496
        // IncomeTax = 496 * 0.24 = 119.04
        //
        // Output expression is present â€” NetSalary is parameterized but since
        // dotCall uses navigation-only semantics (no receiver injection),
        // NetSalary is never evaluated as a receiver.
        var source = """
            NetSalary = {
              SocialSecurityTax = grossSalary * 0.105
              NonTaxableMinimum = grossSalary - SocialSecurityTax - 75
              ChildTaxCredit = numberOfChildren * 162
              TaxableIncome = NonTaxableMinimum - ChildTaxCredit
              IncomeTax = TaxableIncome * 0.24
              
              grossSalary - SocialSecurityTax - IncomeTax
            }
            NetSalary.IncomeTax(1000, 2)
            """;
        AssertEval(source, 119.04m);
    }

    [Fact]
    public void Eval_NetSalary_DotCallOutput()
    {
        // NetSalary.Output(1000, 2) â€” the "Output" property also gains
        // transitive params [grossSalary, numberOfChildren] via IncomeTax.
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
}
