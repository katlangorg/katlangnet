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
        Expr.ResultJoin(var l, var r) => new Expr.ResultJoin(MakeAllPublicExpr(l), MakeAllPublicExpr(r)) { Span = expr.Span },
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

    private static void AssertUnknownDotMember(string source, string expectedName)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var contextual = Assert.IsType<EvalError.WithContext>(result.Error);
        var unresolved = Assert.IsType<EvalError.UnknownName>(contextual.Inner);
        Assert.Equal(expectedName, unresolved.Name);
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

    private static void AssertResultJoinMissingOutput(string source, string expectedSide)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Equal($"Cannot join results because the {expectedSide} side does not produce output.", formatted);

        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;

        var joinError = Assert.IsType<EvalError.ResultJoinMissingOutput>(error);
        Assert.Equal(expectedSide, joinError.Side);
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

    private static void AssertBuiltinFailureWithExactContext(string source, string expectedContext)
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

        Assert.Contains(expectedContext, contexts);
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

    private static void AssertGroupedAtoms(Result value, params decimal[] expected)
    {
        var group = Assert.IsType<Result.Group>(value);
        Assert.Equal(expected.Length, group.Items.Count);

        for (var i = 0; i < expected.Length; i++)
            Assert.Equal(expected[i], Assert.IsType<Result.Atom>(group.Items[i]).Value);
    }

    private static void AssertNestedGroupedAtoms(Result value, params decimal[][] expectedGroups)
    {
        var outer = Assert.IsType<Result.Group>(value);
        Assert.Equal(expectedGroups.Length, outer.Items.Count);

        for (var groupIndex = 0; groupIndex < expectedGroups.Length; groupIndex++)
        {
            var group = Assert.IsType<Result.Group>(outer.Items[groupIndex]);
            var expected = expectedGroups[groupIndex];
            Assert.Equal(expected.Length, group.Items.Count);

            for (var itemIndex = 0; itemIndex < expected.Length; itemIndex++)
                Assert.Equal(expected[itemIndex], Assert.IsType<Result.Atom>(group.Items[itemIndex]).Value);
        }
    }

    private static void AssertAtomValue(Result value, decimal expected)
        => Assert.Equal(expected, Assert.IsType<Result.Atom>(value).Value);

    [Fact]
    public void Eval_RepeatedEligiblePropertyWithinSingleRun()
    {
        var source = """
            Values = range(1, 5)
            Values.count + Values.count
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([10m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_ClosedLexicalProperty_RemainsCorrectAcrossCallerContexts()
    {
        var source = """
            Measure(values) = {
                Count = values.count
                Count + Count
            }
            Measure((1, 2)) + Measure((3, 4, 5))
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([4m], result.Value.ToAtoms());
    }

    [Fact]
        public void Eval_Distinguishes_SamePropertyTextAcrossReceiverContexts()
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

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([6m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_ParameterizedCallResults_RemainDistinct()
    {
        var source = """
            Inc = x + 1
            Inc(1) + Inc(2)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([5m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_RepeatedRuns_AreConsistent()
    {
        var source = """
            Values = range(1, 5)
            Values.count + Values.count
            """;

        var ast = Parser.Parse(source).Root;

        var first = Evaluator.Run(new Expr.Block(ast));
        var second = Evaluator.Run(new Expr.Block(ast));

        if (first.IsError)
            Assert.Fail($"Expected first run success but got error: {first.Error}");
        if (second.IsError)
            Assert.Fail($"Expected second run success but got error: {second.Error}");

        Assert.Equal(first.Value.ToAtoms(), second.Value.ToAtoms());
    }

    [Fact]
    public void Eval_PreservesRecursivePropertyBehavior()
    {
        var source = """
            Recursive = {
              Step = if(n == 0, 0, Step(n - 1))
              Step(4)
            }
            Recursive + Recursive
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([0m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_RecursiveDotCallArgumentUsesCurrentValueBinding()
    {
        var source = """
            reduceCollection(values) = {
                list = atoms(values)
                if(
                    list.count <= 1,
                    list,
                    list.skip(1).reduceCollection
                )
            }
            reduceCollection((1,2,3,4))
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Distinguishes_HigherOrderAlgorithmContexts()
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

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([46m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_Distinguishes_SameLexicalPropertyTextAcrossNestedBindings()
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

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([60m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_Keeps_CallerBoundZeroParamLexicalProperty_Contextual()
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

            var result = Evaluator.Run(new Expr.Block(root));
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([6m], result.Value.ToAtoms());
    }

    [Fact]
        public void Eval_SharedBindingAcrossDefinitionScopes_DoesNotContaminateOpenDependentMeaning()
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

            var result = Evaluator.Run(new Expr.Block(root));
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal(
            [6m],
            result.Value.ToAtoms());
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
    public void Eval_Index_NamedAtomicSelection_ProjectsAtom()
        => AssertEval(
            """
            A = 7, 8
            A:0
            """,
            7);

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

    [Fact]
    public void Eval_Index_GroupedSelection_ProjectsTopLevelContent()
    {
        var result = EvalFull(
            """
            A = (1, 2), (3, 4)
            A:0
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertGroupedAtoms(result.Value, 1, 2);
    }

    [Fact]
    public void Eval_Index_GroupedSelection_CountAndDotCallCountAgree()
        => AssertEval(
            """
            A = (1, 2), (3, 4)
            count(A:0)
            (A:0).count
            """,
            2,
            2);

    [Fact]
    public void Eval_Index_NestedGroupedSelection_ProjectsOneLevelOnly()
    {
        var result = EvalFull(
            """
            A = ((1, 2), (3, 4)), ((5, 6), (7, 8))
            A:0
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertNestedGroupedAtoms(result.Value, [1m, 2m], [3m, 4m]);
    }

    [Fact]
    public void Eval_Index_NestedGroupedSelection_CountsProjectedContentOneLevelAtATime()
        => AssertEval(
            """
            A = ((1, 2), (3, 4)), ((5, 6), (7, 8))
            count(A:0)
            count(A:0:1)
            """,
            2,
            2);

    [Fact]
    public void Eval_Index_ChainedGroupedSelection_ProjectsEachStep()
    {
        var result = EvalFull(
            """
            A = ((1, 2), (3, 4)), ((5, 6), (7, 8))
            A:0:1
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertGroupedAtoms(result.Value, 3, 4);
    }

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
    public void Eval_Arity_IsNoLongerRecognizedAsIntrinsic_OnPropertyReceiver()
    {
        var source = """
            Data = 1, 7
            Data.arity
            """;

        AssertUnknownDotMember(source, "arity");
    }

    [Fact]
    public void Eval_Arity_IsNoLongerRecognizedAsIntrinsic_OnInlineParenReceiver()
        => AssertUnknownDotMember("(1, 7).arity", "arity");

    [Fact]
    public void Eval_Arity_IsNoLongerRecognizedAsIntrinsic_OnNestedParenReceiver()
        => AssertUnknownDotMember("((1, 7)).arity", "arity");

    [Fact]
    public void Eval_Length_IsNoLongerRecognizedAsIntrinsic()
    {
        AssertUnknownDotMember(
            """
            X = 1, 2, 3
            X.length
            """,
            "length");
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
        // Works through the ordinary dot-call builtin-property path.
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
    public void Eval_Range_ResultJoin_PreservesOrdering()
        => AssertEval("range(3, 1); 0", 3, 2, 1, 0);

    // ── Filter builtin ───────────────────────────────────────────────────────

    [Fact]
    public void Eval_Filter_DirectCallMultiArgs_KeepsMatchingItems()
    {
        var source = """
            IsEven = x mod 2 == 0
            filter(1, 2, 3, 4, 5, 6, IsEven)
            """;
        AssertEval(source, 2, 4, 6);
    }

    [Fact]
    public void Eval_Filter_CommaSeparatedRangeArgument_PreservesOuterBoundary()
    {
        var source = """
            IsEven = x mod 2 == 0
            filter(range(3, 6), 8, IsEven)
            """;

        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_Filter_ResultJoinInsideSingleArgument_FlattensOuterIteration()
    {
        var source = """
            IsEven = x mod 2 == 0
            filter(range(3, 6); 8, IsEven)
            """;

        AssertEval(source, 4, 6, 8);
    }

    [Fact]
    public void Eval_Filter_RangeArgument_PreservesBoundaryShapeForPredicate()
    {
        var source = """
            KeepWholeRange((a, b, c, d, e)) = 1
            KeepWholeRange(x) = 0
            filter(range(1, 5), KeepWholeRange)
            """;

        AssertEval(source, 1, 2, 3, 4, 5);
    }

    [Fact]
    public void Eval_Filter_DirectCallMixedArgs_PreservesRangeBoundaryShapeForPredicate()
    {
        var source = """
            KeepWideRange((a, b, c, d)) = 1
            KeepWideRange(x) = 0
            filter(1, 2, range(3, 6), KeepWideRange)
            """;

        AssertEval(source, 3, 4, 5, 6);
    }

    [Fact]
    public void Eval_Filter_ResultJoinInsideSingleArgument_ProjectsContentForGroupedPatternPredicate()
    {
        var source = """
            KeepThreeGroup((a, b, c)) = 1
            KeepThreeGroup(x) = 0
            filter(1; range(2, 4), KeepThreeGroup)
            """;

        AssertEval(source);
    }

    [Fact]
    public void Eval_Filter_GroupedElements_ArePreservedWhole()
    {
        var source = """
            KeepPair = pair:0 mod 2 == 0
            filter((1, 10), (2, 20), (3, 30), (4, 40), KeepPair)
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
    public void Eval_Filter_MultiOutputPredicate_FailsWithContext()
    {
        var source = """
            Bad(x) = 0, 999
            filter(1, 2, 3, Bad)
            """;

        AssertFilterPredicateShapeFails(source);
    }

    [Fact]
    public void Eval_Filter_GroupedPredicateResult_FailsWithContext()
    {
        var source = """
            Bad(x) = (1, 0)
            filter(1, 2, 3, Bad)
            """;

        AssertFilterPredicateShapeFails(source);
    }

    [Fact]
    public void Eval_Filter_EmptyPredicateResult_FailsWithContext()
    {
        var source = """
            Bad(x) = take(1, 0)
            filter(1, 2, 3, Bad)
            """;

        AssertFilterPredicateShapeFails(source);
    }

    [Fact]
    public void Eval_Filter_StringPredicateResult_FailsWithContext()
    {
        var source = """
            Bad(x) = x.string
            filter(1, 2, 3, Bad)
            """;

        AssertFilterPredicateShapeFails(source);
    }

    [Fact]
    public void Eval_Filter_ArityMismatch_FollowsBuiltinConvention()
    {
        var result = EvalFull("filter(1)");
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var error = result.Error;
        var contexts = new List<string>();
        while (error is EvalError.WithContext wc)
        {
            contexts.Add(wc.Context);
            error = wc.Inner;
        }

        Assert.Contains(contexts, context => context.Contains("expected at least 2 arguments"));
        Assert.IsType<EvalError.ArityMismatch>(error);
    }

    // ── Map builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Map_DirectCallMultiArgs_TransformsEachItem()
    {
        var source = """
            Double = x * 2
            map(1, 2, 3, Double)
            """;

        AssertEval(source, 2, 4, 6);
    }

    [Fact]
    public void Eval_Map_RangeArgument_PreservesOuterBoundaryForHigherOrderIteration()
    {
        var source = """
            TopLevelItemCount(item) = item.count
            map(range(3, 6), TopLevelItemCount)
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Map_PreservesOriginalOrder()
    {
        var source = """
            Tag = x * 10 + 1
            map(5, 4, 3, 2, 1, Tag)
            """;

        AssertEval(source, 51, 41, 31, 21, 11);
    }

    [Fact]
    public void Eval_Map_RangeArgument_WithScalarTransform_FailsWithoutFlattening()
    {
        var source = """
            AddOne = x + 1
            map(range(1, 5), AddOne)
            """;

        AssertBuiltinFailureWithContext(
            source,
            "while evaluating map transform (map passes each iterated collection item as collected; ordinary boundaries stay whole and explicit result join/: iterate content)");
    }

    [Fact]
    public void Eval_Map_DirectCallMixedArgs_PreservesRangeBoundary()
    {
        var source = """
            MarkGroupedRange((a, b, c)) = 1
            MarkGroupedRange(x) = 0
            map(1, range(2, 4), MarkGroupedRange)
            """;

        AssertEval(source, 0, 1);
    }

    [Fact]
    public void Eval_Map_ResultJoinInsideSingleArgument_ProjectsContentForGroupedPatternTransform()
    {
        var source = """
            MarkGroupedRange((a, b, c)) = 1
            MarkGroupedRange(x) = 0
            map(1; range(2, 4), MarkGroupedRange)
            """;

        AssertEval(source, 0, 0, 0, 0);
    }

    [Fact]
    public void Eval_Map_GroupedElements_ArePassedWhole()
    {
        var source = """
            TakeValue = pair:1
            map((1, 10), (2, 20), (3, 30), TakeValue)
            """;

        AssertEval(source, 10, 20, 30);
    }

    [Fact]
    public void Eval_Map_GroupedTransformResult_IsAccepted()
    {
        var source = """
            PairWithSquare(x) = (x, x * x)
            map(1, 2, 3, PairWithSquare)
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
            Bad(x) = take(1, 0)
            map(1, 2, 3, Bad)
            """;

        AssertMapTransformShapeFails(source);
    }

    [Fact]
    public void Eval_Map_MultiOutputTransformResult_FailsWithContext()
    {
        var source = """
            Bad(x) = x, x * x
            map(1, 2, 3, Bad)
            """;

        AssertMapTransformShapeFails(source);
    }

    // ── Order builtins ──────────────────────────────────────────────────────

    [Fact]
    public void Eval_Order_DirectCallMultiArgs_SortsAscending()
        => AssertEval("order(3, 4, 2, 1, 3, 3)", 1, 2, 3, 3, 3, 4);

    [Fact]
    public void Eval_Order_WrapperMultiOutputArg_ExpandsTopLevelItems()
    {
        var source = """
            Values = 3, 4, 2, 1, 3, 3
            order(Values)
            """;

        AssertEval(source, 1, 2, 3, 3, 3, 4);
    }

    [Fact]
    public void Eval_Order_SingleGroupedArg_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "order((3, 4, 2, 1, 3, 3))",
            "order expects each collection element to be a single numeric value; item 0 was grouped value");

    [Fact]
    public void Eval_Order_ProjectedSelection_PlainAndDotCallAgree()
        => AssertEval(
            """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            order(Data:0)
            (Data:0).order
            """,
            1,
            2,
            4,
            6,
            7,
            1,
            2,
            4,
            6,
            7);

    [Fact]
    public void Eval_Order_DirectCallMixedArgs_ExpandsRangeTopLevelItems()
        => AssertEval("order(3, 4, range(1, 5), 7)", 1, 2, 3, 3, 4, 4, 5, 7);

    [Fact]
    public void Eval_Order_DotCall_RangeBoundaryMatchesPlainCallFailure()
        => AssertEval("range(5, 1).order", 1, 2, 3, 4, 5);

    [Fact]
    public void Eval_Order_DotCall_InlineParenReceiver_PreservesBoundary()
        => AssertEval("(3, 5, 3, 6, 3).order", 3, 3, 3, 5, 6);

    [Fact]
    public void Eval_Order_DoubleParenReceiver_DotCallMatchesGroupedPlainCall()
        => AssertBuiltinFailureWithExactContext(
            "((3, 5, 3, 6, 3)).order",
            "order expects each collection element to be a single numeric value; item 0 was grouped value");

    [Fact]
    public void Eval_Order_UnsupportedElement_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "order(1, 'hello')",
            "order expects each collection element to be a single numeric value; item 1 was string value \"hello\"");

    [Fact]
    public void Eval_Order_GroupedMultiArgs_FailWithContext()
        => AssertBuiltinFailureWithExactContext(
            "order((1, 2), (3, 4))",
            "order expects each collection element to be a single numeric value; item 0 was grouped value");

    [Fact]
    public void Eval_OrderDesc_DirectCallMultiArgs_SortsDescending()
        => AssertEval("orderDesc(3, 4, 2, 1, 3, 3)", 4, 3, 3, 3, 2, 1);

    [Fact]
    public void Eval_OrderDesc_WrapperMultiOutputArg_ExpandsTopLevelItems()
    {
        var source = """
            Values = 3, 4, 2, 1, 3, 3
            orderDesc(Values)
            """;

        AssertEval(source, 4, 3, 3, 3, 2, 1);
    }

    [Fact]
    public void Eval_OrderDesc_SingleGroupedArg_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "orderDesc((3, 4, 2, 1, 3, 3))",
            "orderDesc expects each collection element to be a single numeric value; item 0 was grouped value");

    [Fact]
    public void Eval_OrderDesc_GroupedMultiArgs_FailWithContext()
        => AssertBuiltinFailureWithExactContext(
            "orderDesc((1, 2), (3, 4))",
            "orderDesc expects each collection element to be a single numeric value; item 0 was grouped value");

    [Fact]
    public void Eval_Order_IndexedNumericDiagnostic_IncludesItemIndex()
        => AssertBuiltinFailureWithContext(
            "order(1, (2, 3))",
            "order expects each collection element to be a single numeric value; item 1 was grouped value");

    [Fact]
    public void Eval_OrderDesc_IndexedNumericDiagnostic_IncludesItemIndex()
        => AssertBuiltinFailureWithContext(
            "orderDesc(1, (2, 3))",
            "orderDesc expects each collection element to be a single numeric value; item 1 was grouped value");

    // ── Count builtin ────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Count_OrdinaryBuiltinCall_CountsRangeTopLevelItems()
        => AssertEval("count(range(1, 5))", 5);

    [Fact]
    public void Eval_Count_DotCall_CountsRangeTopLevelItems()
        => AssertEval("range(1, 5).count", 5);

    [Fact]
    public void Eval_Count_DotCall_EmptyFilterReceiver_ReturnsZero()
        => AssertEval("(1, 5, 3).filter{ n mod 2 == 0 }.count", 0);

    [Fact]
    public void Eval_Count_DotCall_EmptyFilterReceiverWithNamedPredicate_ReturnsZero()
    {
        var source = """
            IsEven = n mod 2 == 0
            (1, 5, 3).filter(IsEven).count
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_Count_NoArguments_Fails()
        => AssertEvalFails("count()");

    [Fact]
    public void Eval_SequenceBuiltinDotCall_EmptyFilterReceiver_RespectsEmptyPolicies()
    {
        AssertEval("(1, 5, 3).filter{ n mod 2 == 0 }.sum", 0);
        AssertBuiltinFailureWithExactContext(
            "(1, 5, 3).filter{ n mod 2 == 0 }.first",
            "first requires a non-empty collection");
        AssertBuiltinFailureWithExactContext(
            "(1, 5, 3).filter{ n mod 2 == 0 }.last",
            "last requires a non-empty collection");
    }

    [Fact]
    public void Eval_Count_DescendingRange_CountsTopLevelItems()
        => AssertEval("count(range(5, 1))", 5);

    [Fact]
    public void Eval_Count_GroupedElements_CountsTopLevelGroups()
        => AssertEval("count(((1, 2), (3, 4)))", 1);

    [Fact]
    public void Eval_Count_SingleAtomicInput_ReturnsOne()
        => AssertEval("count(5)", 1);

    [Fact]
    public void Eval_Count_StringInput_ReturnsOne()
        => AssertEval("count('hello')", 1);

    [Fact]
    public void Eval_Count_DirectCallMultiArgs_CountsTopLevelItems()
        => AssertEval("count(1, 7)", 2);

    [Fact]
    public void Eval_Count_DirectCallMixedArgs_CountsExpandedRangeTopLevelItems()
        => AssertEval("count(3, 4, range(1, 5), 7)", 8);

    [Fact]
    public void Eval_Count_SingleGroupedArg_CountsOneTopLevelItem()
        => AssertEval("count((1, 7))", 1);

    [Fact]
    public void Eval_Count_GroupedMultiArgs_CountTopLevelGroups()
        => AssertEval("count((1, 2), (3, 4))", 2);

    [Fact]
    public void Eval_Count_InlineParenReceiver_DotCallPreservesBoundary()
        => AssertEval("(1, 7).count", 2);

    [Fact]
    public void Eval_Count_WrapperMultiOutputBoundary_CountsExpandedTopLevelItems()
    {
        var source = """
            Values = 1, 2, 3
            count(Values)
            """;

        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Count_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            count(Data:0)
            (Data:0).count
            """;

        AssertEval(source, 5, 5);
    }

    [Fact]
    public void Eval_Count_ProjectedExpressionAndNamedProjectionAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            Projected = Data:0
            count(Data:0)
            count(Projected)
            """;

        AssertEval(source, 5, 5);
    }

    // ── Contains builtin ─────────────────────────────────────────────────────

    [Fact]
    public void Eval_Contains_OrdinaryBuiltinCall_SearchesExpandedRangeTopLevelItems()
        => AssertEval("contains(range(1, 5), 3)", 1);

    [Fact]
    public void Eval_Contains_OrdinaryBuiltinCall_DoesNotTreatRangeAsOneGroupedValue()
        => AssertEval("contains(range(1, 5), (1, 2, 3, 4, 5))", 0);

    [Fact]
    public void Eval_Contains_DotCall_MatchesPlainCallReceiverSemantics()
        => AssertEval("range(1, 5).contains(4)", 1);

    [Fact]
    public void Eval_Contains_DirectCallMixedArgs_SearchesExpandedRangeTopLevelItems()
        => AssertEval("contains(3, 4, range(1, 5), 7, 5)", 1);

    [Fact]
    public void Eval_Contains_DirectCallMixedArgs_DoesNotMatchGroupedRangeValue()
        => AssertEval("contains(3, 4, range(1, 5), 7, (1, 2, 3, 4, 5))", 0);

    [Fact]
    public void Eval_Contains_GroupedItem_UsesOrdinaryValueEquality()
        => AssertEval("contains((1, 2), (1, 2))", 1);

    [Fact]
    public void Eval_Contains_DoesNotSearchInsideNestedGroupedMembers()
        => AssertEval("contains(((1, 2), (3, 4)), (1, 2))", 0);

    [Fact]
    public void Eval_Contains_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            contains(Data:0, 4)
            (Data:0).contains(4)
            """;

        AssertEval(source, 1, 1);
    }

    [Fact]
    public void Eval_Contains_MultiOutputSearchedItem_PreservesGroupedValue()
    {
        var source = """
            Item = 1, 2
            contains((1, 2), Item)
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Contains_ArityMismatch_RequiresSequenceAndItem()
    {
        var result = EvalFull("contains(1)");
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("expected at least 2 arguments (one or more sequence arguments plus item)", formatted);
        Assert.Contains("while evaluating call to contains", formatted);

        var error = result.Error;
        while (error is EvalError.WithContext wc)
            error = wc.Inner;

        Assert.IsType<EvalError.ArityMismatch>(error);
    }

    // ── First/last builtins ────────────────────────────────────────────────

    [Fact]
    public void Eval_First_OrdinaryBuiltinCall_ReturnsFirstExpandedRangeItem()
        => AssertEval("first(range(1, 5))", 1);

    [Fact]
    public void Eval_Last_OrdinaryBuiltinCall_ReturnsLastExpandedRangeItem()
        => AssertEval("last(range(1, 5))", 5);

    [Fact]
    public void Eval_First_DotCall_PreservesRangeBoundaryItem()
        => AssertEval("range(1, 5).first", 1);

    [Fact]
    public void Eval_Last_DotCall_PreservesRangeBoundaryItem()
        => AssertEval("range(1, 5).last", 5);

    [Fact]
    public void Eval_First_DirectCallMultiResult_Shorthand_ReturnsFirstOutput()
        => AssertEval("first(1, 2, 3)", 1);

    [Fact]
    public void Eval_Last_DirectCallMultiResult_Shorthand_ReturnsLastOutput()
        => AssertEval("last(1, 2, 3)", 3);

    [Fact]
    public void Eval_First_SingleGroupedArg_PreservesGroup()
    {
        var result = EvalFull("first((1, 2))");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertGroupedAtoms(result.Value, 1, 2);
    }

    [Fact]
    public void Eval_First_MultiArgGroupedInputs_PreservesFirstGroup()
    {
        var result = EvalFull("first((1, 2), (3, 4))");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertGroupedAtoms(result.Value, 1, 2);
    }

    [Fact]
    public void Eval_Last_SingleGroupedArg_PreservesGroup()
    {
        var result = EvalFull("last((1, 2))");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertGroupedAtoms(result.Value, 1, 2);
    }

    [Fact]
    public void Eval_Last_MultiArgGroupedInputs_PreservesLastGroup()
    {
        var result = EvalFull("last((1, 2), (3, 4))");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertGroupedAtoms(result.Value, 3, 4);
    }

    [Fact]
    public void Eval_First_PropertyOutput_PreservesBoundaryItem()
    {
        var source = """
            Values = 4, 5, 6
            Head = Values.first
            Head
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Last_IntermediateProperty_PreservesBoundaryItem()
    {
        var source = """
            Values = 4, 5, 6
            Tail = Values.last
            Tail
            """;

        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_First_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            first(Data:0)
            (Data:0).first
            """;

        AssertEval(source, 7, 7);
    }

    [Fact]
    public void Eval_Last_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            last(Data:0)
            (Data:0).last
            """;

        AssertEval(source, 1, 1);
    }

    [Fact]
    public void Eval_First_InlineParenReceiver_DotCallPreservesBoundary()
        => AssertEval("(4, 5, 6).first", 4);

    [Fact]
    public void Eval_Last_InlineParenReceiver_DotCallPreservesBoundary()
        => AssertEval("(4, 5, 6).last", 6);

    // ── Distinct builtin ───────────────────────────────────────────────────

    [Fact]
    public void Eval_Distinct_OrdinaryBuiltinCall_RemovesLaterDuplicatesPreservingFirstOccurrence()
        => AssertEval("distinct(3, 1, 3, 2, 1, 2)", 3, 1, 2);

    [Fact]
    public void Eval_Distinct_DotCall_PreservesNamedBoundaryItem()
    {
        var source = """
            Values = 3, 1, 3, 2, 1, 2
            Values.distinct
            """;

        AssertEval(source, 3, 1, 2);
    }

    [Fact]
    public void Eval_Distinct_AllEqualInput_ReturnsSingleValue()
        => AssertEval("distinct(4, 4, 4, 4)", 4);

    [Fact]
    public void Eval_Distinct_AlreadyDistinctInput_PreservesOrder()
        => AssertEval("distinct(1, 2, 3)", 1, 2, 3);

    [Fact]
    public void Eval_Distinct_GroupedItems_RemoveDuplicateGroupsByValue()
    {
        var result = EvalFull("distinct((1, 2), (1, 2), (3, 4))");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertNestedGroupedAtoms(result.Value, [1m, 2m], [3m, 4m]);
    }

    [Fact]
    public void Eval_Distinct_GroupedWrapperOutput_PreservesSingleGroupedItem()
    {
        var source = """
            Values = ((1, 2), (1, 2), (3, 4))
            distinct(Values)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertNestedGroupedAtoms(result.Value, [1m, 2m], [1m, 2m], [3m, 4m]);
    }

    [Fact]
    public void Eval_Distinct_MultiOutputWrapper_DeduplicatesExpandedTopLevelItems()
    {
        var source = """
            Values = (1, 2), (1, 2), (3, 4)
            distinct(Values)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertNestedGroupedAtoms(result.Value, [1m, 2m], [3m, 4m]);
    }

    [Fact]
    public void Eval_Distinct_InlineParenReceiver_DotCallPreservesBoundaryItem()
        => AssertEval("(1, 2, 1, 3).distinct", 1, 2, 3);

    [Fact]
    public void Eval_Distinct_GroupedReceiver_DotCallPreservesGroupedValue()
    {
        var source = """
            Values = (1, 2, 1, 3)
            Values.distinct
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertGroupedAtoms(result.Value, 1, 2, 1, 3);
    }

    // ── Take/skip builtins ────────────────────────────────────────────────

    [Fact]
    public void Eval_Take_OrdinaryBuiltinCall_ReturnsLeadingItems()
        => AssertEval("take(1, 2, 3, 4, 5, 3)", 1, 2, 3);

    [Fact]
    public void Eval_Skip_OrdinaryBuiltinCall_ReturnsRemainingItems()
        => AssertEval("skip(1, 2, 3, 4, 5, 3)", 4, 5);

    [Fact]
    public void Eval_Take_DotCall_PreservesRangeBoundaryItem()
        => AssertEval("range(1, 5).take(3)", 1, 2, 3);

    [Fact]
    public void Eval_Skip_DotCall_DropsWholeRangeBoundaryItem()
        => AssertEval("range(1, 5).skip(3)", 4, 5);

    [Fact]
    public void Eval_Take_InlineParenReceiver_DotCallPreservesBoundaryItem()
        => AssertEval("(1, 2, 3).take(2)", 1, 2);

    [Fact]
    public void Eval_Skip_InlineParenReceiver_DotCallDropsBoundaryItem()
        => AssertEval("(1, 2, 3).skip(1)", 2, 3);

    [Fact]
    public void Eval_Take_GroupedReceiver_DotCallPreservesGroupedValue()
    {
        var source = """
            Values = (1, 2, 3)
            Values.take(2)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertGroupedAtoms(result.Value, 1, 2, 3);
    }

    [Fact]
    public void Eval_Skip_GroupedReceiver_DotCallTreatsGroupedValueAsSingleItem()
    {
        var source = """
            Values = (1, 2, 3)
            Values.skip(1)
            """;

        AssertEval(source);
    }

    [Fact]
    public void Eval_Take_ZeroCount_ReturnsEmpty()
        => AssertEval("take(1, 2, 3, 0)");

    [Fact]
    public void Eval_Skip_ZeroCount_ReturnsOriginalSequence()
        => AssertEval("skip(1, 2, 3, 0)", 1, 2, 3);

    [Fact]
    public void Eval_Take_NegativeCount_ReturnsEmpty()
        => AssertEval("take(1, 2, 3, -2)");

    [Fact]
    public void Eval_Skip_NegativeCount_ReturnsOriginalSequence()
        => AssertEval("skip(1, 2, 3, -2)", 1, 2, 3);

    [Fact]
    public void Eval_Take_CountLargerThanLength_ReturnsWholeSequence()
        => AssertEval("take(1, 2, 3, 10)", 1, 2, 3);

    [Fact]
    public void Eval_Skip_CountLargerThanLength_ReturnsEmpty()
        => AssertEval("skip(1, 2, 3, 10)");

    [Fact]
    public void Eval_Take_GroupedItems_PreservesFirstGroup()
    {
        var result = EvalFull("take((1, 2), (3, 4), 1)");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertGroupedAtoms(result.Value, 1, 2);
    }

    [Fact]
    public void Eval_Skip_GroupedItems_PreservesSecondGroup()
    {
        var result = EvalFull("skip((1, 2), (3, 4), 1)");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertGroupedAtoms(result.Value, 3, 4);
    }

    [Fact]
    public void Eval_Take_GroupedWrapperOutput_PreservesSingleGroupedItem()
    {
        var source = """
            Values = (1, 2, 3)
            take(Values, 1)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertGroupedAtoms(result.Value, 1, 2, 3);
    }

    [Fact]
    public void Eval_Take_MultiOutputWrapper_KeepsExpandedTopLevelPrefix()
    {
        var source = """
            Values = 1, 2, 3
            take(Values, 1)
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Skip_GroupedWrapperOutput_ReturnsEmptyAfterSkippingSingleGroupedItem()
    {
        var source = """
            Values = (1, 2, 3)
            skip(Values, 1)
            """;

        AssertEval(source);
    }

    [Fact]
    public void Eval_Skip_MultiOutputWrapper_DropsExpandedTopLevelPrefix()
    {
        var source = """
            Values = 1, 2, 3
            skip(Values, 1)
            """;

        AssertEval(source, 2, 3);
    }

    [Fact]
    public void Eval_Take_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            take(Data:0, 2)
            (Data:0).take(2)
            """;

        AssertEval(source, 7, 6, 7, 6);
    }

    [Fact]
    public void Eval_Skip_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            skip(Data:0, 2)
            (Data:0).skip(2)
            """;

        AssertEval(source, 4, 2, 1, 4, 2, 1);
    }

    [Fact]
    public void Eval_Take_EmptyCountArgument_FailsWithContext()
        => AssertBuiltinFailureWithContext(
            "take(1, 2, take(1, 0))",
            "take count must be exactly one whole-number value");

    [Fact]
    public void Eval_Take_GroupedCountArgument_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "take(3, 4, (1, 2))",
            "take count must be exactly one whole-number value");

    [Fact]
    public void Eval_Take_FractionalCountArgument_FailsWithContext()
        => AssertBuiltinFailureWithContext(
            "take(1, 2, 1.5)",
            "take count must be exactly one whole-number value");

    [Fact]
    public void Eval_Skip_StringCountArgument_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "skip(1, 2, 'hello')",
            "skip count must be exactly one whole-number value");

    [Fact]
    public void Eval_Skip_MultipleValueCountArgument_FailsWithContext()
    {
        var source = """
            Bad = 1, 2
            skip(3, 4, Bad)
            """;

        AssertBuiltinFailureWithContext(source, "skip count must be exactly one whole-number value");
    }

    // ── Min builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Min_OrdinaryBuiltinCall_ExpandsRangeTopLevelItems()
        => AssertEval("min(range(1, 5))", 1);

    [Fact]
    public void Eval_Min_DotCall_DoesNotFlattenRangeBoundary()
        => AssertEval("range(1, 5).min", 1);

    [Fact]
    public void Eval_Min_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            min(Data:0)
            (Data:0).min
            """;

        AssertEval(source, 1, 1);
    }

    [Fact]
    public void Eval_Min_InlineParenReceiver_DotCallPreservesBoundary()
        => AssertEval("(10, 4, 7).min", 4);

    [Fact]
    public void Eval_Min_GroupedReceiver_DotCallMatchesGroupedPlainCall()
    {
        var source = """
            Values = (10, 4, 7)
            Values.min
            """;

        AssertBuiltinFailureWithExactContext(
            source,
            "min expects each collection element to be a single numeric value; item 0 was grouped value");
    }

    [Fact]
    public void Eval_Min_SingleAtomicInput_ReturnsSameValue()
        => AssertEval("min(5)", 5);

    [Fact]
    public void Eval_Min_DirectCallMultiArgs_FindsMinimum()
        => AssertEval("min(10, 4, 7)", 4);

    [Fact]
    public void Eval_Min_GroupedElements_FailWithContext()
        => AssertBuiltinFailureWithExactContext(
            "min(((1, 2), (3, 4)))",
            "min expects each collection element to be a single numeric value; item 0 was grouped value");

    [Fact]
    public void Eval_Min_StringElement_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "min('hello')",
            "min expects each collection element to be a single numeric value; item 0 was string value \"hello\"");

    [Fact]
    public void Eval_Min_IndexedNumericDiagnostic_IncludesItemIndex()
        => AssertBuiltinFailureWithContext(
            "min(1, (2, 3))",
            "min expects each collection element to be a single numeric value; item 1 was grouped value");

    // ── Max builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Max_OrdinaryBuiltinCall_ExpandsRangeTopLevelItems()
        => AssertEval("max(range(1, 5))", 5);

    [Fact]
    public void Eval_Max_DotCall_DoesNotFlattenRangeBoundary()
        => AssertEval("range(1, 5).max", 5);

    [Fact]
    public void Eval_Max_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            max(Data:0)
            (Data:0).max
            """;

        AssertEval(source, 7, 7);
    }

    [Fact]
    public void Eval_Max_InlineBraceReceiver_DotCallPreservesBoundary()
        => AssertEval("{10, 4, 7}.max", 10);

    [Fact]
    public void Eval_Max_GroupedReceiver_DotCallMatchesGroupedPlainCall()
    {
        var source = """
            Values = (10, 4, 7)
            Values.max
            """;

        AssertBuiltinFailureWithExactContext(
            source,
            "max expects each collection element to be a single numeric value; item 0 was grouped value");
    }

    [Fact]
    public void Eval_Max_SingleAtomicInput_ReturnsSameValue()
        => AssertEval("max(5)", 5);

    [Fact]
    public void Eval_Max_DirectCallMultiArgs_FindsMaximum()
        => AssertEval("max(10, 4, 7)", 10);

    [Fact]
    public void Eval_Max_GroupedElements_FailWithContext()
        => AssertBuiltinFailureWithExactContext(
            "max(((1, 2), (3, 4)))",
            "max expects each collection element to be a single numeric value; item 0 was grouped value");

    [Fact]
    public void Eval_Max_StringElement_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "max('hello')",
            "max expects each collection element to be a single numeric value; item 0 was string value \"hello\"");

    [Fact]
    public void Eval_Max_IndexedNumericDiagnostic_IncludesItemIndex()
        => AssertBuiltinFailureWithContext(
            "max(1, (2, 3))",
            "max expects each collection element to be a single numeric value; item 1 was grouped value");

    // ── Sum builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Sum_OrdinaryBuiltinCall_ExpandsRangeTopLevelItems()
        => AssertEval("sum(range(1, 5))", 15);

    [Fact]
    public void Eval_Sum_OrdinaryBuiltinCall_ExpandsLargeRangeTopLevelItems()
        => AssertEval("sum(range(1, 100))", 5050);

    [Fact]
    public void Eval_Sum_WrapperBoundToRange_ExpandsTopLevelItems()
    {
        var source = """
            P = range(1, 100)
            sum(P)
            """;

        AssertEval(source, 5050);
    }

    [Fact]
    public void Eval_Sum_DotCall_DoesNotFlattenRangeBoundary()
        => AssertEval("range(1, 5).sum", 15);

    [Fact]
    public void Eval_Sum_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            sum(Data:0)
            (Data:0).sum
            """;

        AssertEval(source, 20, 20);
    }

    [Fact]
    public void Eval_Sum_InlineBraceReceiver_DotCallPreservesBoundary()
        => AssertEval("{3, 5, 3}.sum", 11);

    [Fact]
    public void Eval_Sum_GroupedReceiver_DotCallMatchesGroupedPlainCall()
    {
        var source = """
            Values = (10, 20, 30)
            Values.sum
            """;

        AssertBuiltinFailureWithExactContext(
            source,
            "sum expects each collection element to be a single numeric value; item 0 was grouped value");
    }

    [Fact]
    public void Eval_Sum_NestedGroupedReceiver_DotCallPreservesNestedGroups()
        => AssertBuiltinFailureWithExactContext(
            "((1, 2), (3, 4)).sum",
            "sum expects each collection element to be a single numeric value; item 0 was grouped value");

    [Fact]
    public void Eval_Sum_SingleAtomicInput_ReturnsSameValue()
        => AssertEval("sum(5)", 5);

    [Fact]
    public void Eval_Sum_DirectCallMultiArgs_AddsValues()
        => AssertEval("sum(10, 20, 30)", 60);

    [Fact]
    public void Eval_Sum_GroupedElements_FailWithContext()
        => AssertBuiltinFailureWithExactContext(
            "sum(((1, 2), (3, 4)))",
            "sum expects each collection element to be a single numeric value; item 0 was grouped value");

    [Fact]
    public void Eval_Sum_StringElement_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "sum('hello')",
            "sum expects each collection element to be a single numeric value; item 0 was string value \"hello\"");

    [Fact]
    public void Eval_Sum_IndexedNumericDiagnostic_IncludesItemIndex()
        => AssertBuiltinFailureWithContext(
            "sum(1, (2, 3))",
            "sum expects each collection element to be a single numeric value; item 1 was grouped value");

    [Fact]
    public void Eval_Sum_ProjectedNestedGroupedSelection_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            """
            A = ((1, 2), (3, 4)), ((5, 6), (7, 8))
            sum(A:0)
            """,
            "sum expects each collection element to be a single numeric value; item 0 was grouped value");

    // ── Avg builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Avg_OrdinaryBuiltinCall_ExpandsRangeTopLevelItems()
        => AssertEval("avg(range(1, 5))", 3);

    [Fact]
    public void Eval_Avg_DotCall_DoesNotFlattenRangeBoundary()
        => AssertEval("range(1, 5).avg", 3);

    [Fact]
    public void Eval_Avg_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            avg(Data:0)
            (Data:0).avg
            """;

        AssertEval(source, 4, 4);
    }

    [Fact]
    public void Eval_Avg_InlineParenReceiver_DotCallPreservesBoundary()
        => AssertEval("(10, 4, 7).avg", 7);

    [Fact]
    public void Eval_Avg_GroupedReceiver_DotCallMatchesGroupedPlainCall()
    {
        var source = """
            Values = (10, 20, 30)
            Values.avg
            """;

        AssertBuiltinFailureWithExactContext(
            source,
            "avg expects each collection element to be a single numeric value; item 0 was grouped value");
    }

    [Fact]
    public void Eval_Avg_NonExactPositiveMean_UsesLeanFloorSemantics()
        => AssertEval("avg(1, 2)", 1);

    [Fact]
    public void Eval_Avg_NonExactNegativeMean_UsesLeanFloorSemantics()
        => AssertEval("avg(-1, -2)", -2);

    [Fact]
    public void Eval_Avg_SingleAtomicInput_ReturnsSameValue()
        => AssertEval("avg(5)", 5);

    [Fact]
    public void Eval_Avg_DirectCallMultiArgs_ComputesMean()
        => AssertEval("avg(10, 20, 30)", 20);

    [Fact]
    public void Eval_Avg_GroupedElements_FailWithContext()
        => AssertBuiltinFailureWithExactContext(
            "avg(((1, 2), (3, 4)))",
            "avg expects each collection element to be a single numeric value; item 0 was grouped value");

    [Fact]
    public void Eval_Avg_StringElement_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "avg('hello')",
            "avg expects each collection element to be a single numeric value; item 0 was string value \"hello\"");

    [Fact]
    public void Eval_Avg_IndexedNumericDiagnostic_IncludesItemIndex()
        => AssertBuiltinFailureWithContext(
            "avg(1, (2, 3))",
            "avg expects each collection element to be a single numeric value; item 1 was grouped value");

    // ── Reduce builtin ───────────────────────────────────────────────────────

    [Fact]
    public void Eval_Reduce_DirectCallMultiArgs_AddsLeftToRight()
    {
        var source = """
            Add = x + total
            reduce(1, 2, 3, 4, Add, 0)
            """;

        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Reduce_RangeArgument_PreservesOuterBoundaryForHigherOrderIteration()
    {
        var source = """
            AddItemCount(item, acc) = item.count + acc
            reduce(range(3, 6), AddItemCount, 0)
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Reduce_DirectCallMixedArgs_DoesNotSpreadRangeBoundary()
    {
        var source = """
            AddItemCount(x, acc) = x.count + acc
            reduce(1, 2, range(3, 4), AddItemCount, 0)
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Reduce_DirectCallMixedArgs_PreservesRangeBoundaryShapeForStep()
    {
        var source = """
            AddGroupedRange((a, b, c), acc) = acc + 100
            AddGroupedRange(x, acc) = acc + x
            reduce(1, range(2, 4), AddGroupedRange, 0)
            """;

        AssertEval(source, 101);
    }

    [Fact]
    public void Eval_Reduce_ResultJoinInsideSingleArgument_ProjectsContentForStep()
    {
        var source = """
            AddGroupedRange((a, b, c), acc) = acc + 100
            AddGroupedRange(x, acc) = acc + x
            reduce(1; range(2, 4), AddGroupedRange, 0)
            """;

        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Reduce_IsLeftToRight()
    {
        var source = """
            Digits = x + acc * 10
            reduce(1, 2, 3, 4, Digits, 0)
            """;

        AssertEval(source, 1234);
    }

    [Fact]
    public void Eval_Reduce_ArityMismatch_RequiresAtLeastThreeArguments()
    {
        var result = EvalFull(
            """
            Add = x + total
            reduce(1, Add)
            """);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("expected at least 3 arguments", formatted);
        Assert.Contains("while evaluating call to reduce", formatted);

        var error = result.Error;
        while (error is EvalError.WithContext wc)
            error = wc.Inner;

        Assert.IsType<EvalError.ArityMismatch>(error);
    }

    [Fact]
    public void Eval_Reduce_ParameterizedInitialAccumulator_ReportsCallSiteWithHint()
    {
        var result = EvalFull("Add = x + total\nreduce(1, 2, 3, Add)");
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error);
        Assert.Equal(2, formatted.StartLine);
        Assert.Equal(1, formatted.StartColumn);
        Assert.Contains("`reduce` is `reduce(items..., step, initial)`", formatted.Message);
        Assert.Contains("'x' and 'total'", formatted.Message);
        Assert.Contains("add an initial accumulator", formatted.Message);
        Assert.DoesNotContain("Unknown name: x", formatted.Message);
        Assert.DoesNotContain("Bad arity", formatted.Message);

        var error = result.Error;
        while (error is EvalError.WithContext context)
        {
            if (context.ErrorContext is ReduceInitialAccumulatorContext)
            {
                Assert.IsType<EvalError.BadArity>(context.Inner);
                return;
            }

            error = context.Inner;
        }

        Assert.Fail("Expected reduce initial-accumulator context.");
    }

    [Fact]
    public void Eval_Reduce_DotCallParameterizedInitialAccumulator_ReportsCallSiteWithHint()
    {
        var result = EvalFull(
            """
            Add = x + total
            Values = 1, 2, 3
            Values.reduce(Add)
            """);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error);
        Assert.Equal(3, formatted.StartLine);
        Assert.Equal(1, formatted.StartColumn);
        Assert.Contains("`reduce` is `reduce(items..., step, initial)`", formatted.Message);
        Assert.Contains("'x' and 'total'", formatted.Message);
        Assert.Contains("add an initial accumulator", formatted.Message);
        Assert.DoesNotContain("Unknown name: x", formatted.Message);
        Assert.DoesNotContain("Bad arity", formatted.Message);
    }

    [Fact]
    public void Eval_Reduce_GroupedElements_ArePassedWhole()
    {
        var source = """
            TakeValue((tag, value), acc) = acc + value
            reduce((1, 10), (2, 20), (3, 30), TakeValue, 0)
            """;

        AssertEval(source, 60);
    }

    [Fact]
    public void Eval_Reduce_GroupedAccumulator_IsAccepted()
    {
        var source = """
            Stats(x, acc) = (x + acc:0, acc:1 + 1)
            reduce(1, 2, 3, 4, Stats, (0, 0))
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
            reduce((1, 10), (2, 20), (3, 30), TakeStats, (0, 0))
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
    public void Eval_Reduce_GroupedReceiver_DotCall_ProjectsCurrentItemLikeSelection()
    {
        var source = """
            AddItemCount(item, acc) = item.count + acc
            Values = (1, 2, 3)
            Values.reduce(AddItemCount, 0)
            """;

        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Reduce_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Add = x + total
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            reduce(Data:0, Add, 0)
            (Data:0).reduce(Add, 0)
            """;

        AssertEval(source, 20, 20);
    }

    [Fact]
    public void Eval_Reduce_CurrentItem_MatchesSelection_PlainAndDotCall()
    {
        var source = """
            Signature(current, acc) = acc * 100 + current.count * 10 + current.sum
            Items = (1, 2), (3, 4)
            (Items:0).count
            (Items:0).sum
            (Items:1).count
            (Items:1).sum
            Items.reduce(Signature, 0)
            reduce((1, 2), (3, 4), Signature, 0)
            """;

        AssertEval(source, 2, 3, 2, 7, 2327, 2327);
    }

    [Fact]
    public void Eval_Reduce_CurrentItem_ProjectsOneLevelOnly()
    {
        var source = """
            Signature(current, acc) = acc * 100 + current.count * 10 + (current:0).count
            Items = ((1, 2), (3, 4))
            (Items:0).count
            Items.reduce(Signature, 0)
            reduce(((1, 2), (3, 4)), Signature, 0)
            """;

        AssertEval(source, 2, 22, 22);
    }

    [Fact]
    public void Eval_Reduce_Accumulator_DoesNotAutoProject()
    {
        var source = """
            Signature(current, acc) = (acc:0 * 100 + current.count * 10 + acc.count, acc.count)
            Items = (1, 2), (3, 4)
            Items.reduce(Signature, (0, 9, 8))
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertGroupedAtoms(result.Value, 2121m, 1m);
    }

    [Fact]
    public void Eval_Reduce_EmptyStepResult_FailsWithContext()
    {
        var source = """
            Bad(x, acc) = take(1, 0)
            reduce(1, 2, 3, Bad, 0)
            """;

        AssertReduceStepShapeFails(source);
    }

    [Fact]
    public void Eval_Reduce_MultiOutputStepResult_FailsWithContext()
    {
        var source = """
            Bad(x, acc) = acc, x
            reduce(1, 2, 3, Bad, 0)
            """;

        AssertReduceStepShapeFails(source);
    }

    // ── Higher-order boundary regressions ───────────────────────────────────

    [Fact]
    public void Eval_Filter_InlineBraceReceiver_DotCallPreservesBoundary()
    {
        var source = """
            IsLarge = x > 1
            {1, 2, 3, 4}.filter(IsLarge)
            """;

        AssertEval(source, 2, 3, 4);
    }

    [Fact]
    public void Eval_Filter_GroupedReceiver_DotCallTreatsGroupedValueAsSingleItem()
    {
        var source = """
            KeepSecondEven(pair) = pair:1 mod 2 == 0
            Values = (1, 2)
            Values.filter(KeepSecondEven)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertGroupedAtoms(result.Value, 1, 2);
    }

    [Fact]
    public void Eval_Map_InlineParenReceiver_DotCallPreservesBoundary()
    {
        var source = """
            AddOne = x + 1
            (1, 2, 3).map(AddOne)
            """;

        AssertEval(source, 2, 3, 4);
    }

    [Fact]
    public void Eval_Reduce_InlineParenReceiver_DotCall_UsesTopLevelItems()
    {
        var source = """
            Add = x + total
            (1, 2, 3).reduce(Add, 0)
            """;

        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_Map_GroupedReceiver_DotCall_ProjectsCallbackItemLikeSelection()
    {
        var source = """
            TakeFirst(x) = x:0
            Values = (1, 2, 3)
            Values.map(TakeFirst)
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_UsesReceiverTopLevelItemsAndProjectedCallbackCounts()
    {
        var source = """
            Items = range(1, 3), 7
            Items.count
            (Items:0).count
            (Items:1).count
            Items.map{x.count}
            """;

        AssertEval(source, 2, 3, 1, 3, 1);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_FilterAndSelectionUseProjectedCallbackItems()
    {
        var source = """
            Items = range(1, 3), 7
            Items.map{x:0}
            Items.filter{x.count == 3}.count
            """;

        AssertEval(source, 1, 7, 1);
    }

    [Fact]
    public void Eval_HigherOrder_DotCall_GroupedNamedReceiver_DoesNotAutoExpand()
    {
        var source = """
            TopLevelItemCount(item) = item.count
            AddTopLevelItemCount(item, acc) = item.count + acc
            Pairs = ((1, 2), (3, 4))
            Pairs.count
            Pairs.map(TopLevelItemCount)
            Pairs.reduce(AddTopLevelItemCount, 0)
            """;

        AssertEval(source, 1, 2, 2);
    }

    [Fact]
    public void Eval_Map_CallbackItem_FirstProjectionMatchesSelection()
    {
        var source = """
            TakeFirst(report) = report:0
            map((7, 6, 4, 2, 1), (1, 2, 7, 8, 9), TakeFirst)
            """;

        AssertEval(source, 7, 1);
    }

    [Fact]
    public void Eval_Map_GroupedPairs_ProjectOneLevelOnly()
    {
        var source = """
            TakeFirst(x) = x:0
            map((1, 2), (3, 4), TakeFirst)
            """;

        AssertEval(source, 1, 3);
    }

    [Fact]
    public void Eval_Filter_PracticalSafeReportStyle_UsesProjectedCallbackReport()
    {
        var source = """
            IsSafe(report) =
                report:0 > report:(0 + 1) and
                report:1 > report:(1 + 1) and
                report:2 > report:(2 + 1) and
                report:3 > report:(3 + 1) and
                report:0 - report:(0 + 1) <= 3 and
                report:1 - report:(1 + 1) <= 3 and
                report:2 - report:(2 + 1) <= 3 and
                report:3 - report:(3 + 1) <= 3
            filter((7, 6, 4, 2, 1), (1, 2, 7, 8, 9), IsSafe)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertGroupedAtoms(result.Value, 7m, 6m, 4m, 2m, 1m);
    }

    [Fact]
    public void Eval_HigherOrder_DotCall_IndexedGroupedReceiver_ProjectsOneLevel()
    {
        var source = """
            TopLevelItemCount(item) = item.count
            AddTopLevelItemCount(item, acc) = item.count + acc
            Bags = ((1, 2), (3, 4)), ((5, 6), (7, 8))
            (Bags:0).count
            (Bags:0).map(TopLevelItemCount)
            (Bags:0).reduce(AddTopLevelItemCount, 0)
            """;

        AssertEval(source, 2, 2, 2, 4);
    }

    // ── Uniform counted sequence extraction regressions ────────────────────

    [Fact]
    public void Eval_Filter_WrapperSingleGroupedOutput_TreatsGroupAsOneItem()
    {
        var source = """
            KeepSecondEven(pair) = pair:1 mod 2 == 0
            Values = (1, 2)
            filter(Values, KeepSecondEven)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertGroupedAtoms(result.Value, 1m, 2m);
    }

    [Fact]
    public void Eval_Map_WrapperSingleGroupedOutput_MapsOneGroupedItem()
    {
        var source = """
            TakeValue(pair) = pair:1
            Values = (1, 2)
            map(Values, TakeValue)
            """;

        AssertEval(source, 2);
    }

    [Fact]
    public void Eval_Reduce_WrapperSingleGroupedOutput_FoldsWholeGroupOnce()
    {
        var source = """
            AddValue(pair, total) = total + pair:1
            Values = (1, 2)
            reduce(Values, AddValue, 0)
            """;

        AssertEval(source, 2);
    }

    [Fact]
    public void Eval_Sum_WrapperMultiOutput_ExpandsTopLevelItems()
    {
        var source = """
            Values = 10, 20, 30
            sum(Values)
            """;

        AssertEval(source, 60);
    }

    [Fact]
    public void Eval_Min_WrapperMultiOutput_ExpandsTopLevelItems()
    {
        var source = """
            Values = 10, 4, 7
            min(Values)
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Max_WrapperMultiOutput_ExpandsTopLevelItems()
    {
        var source = """
            Values = 10, 4, 7
            max(Values)
            """;

        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Avg_WrapperMultiOutput_ExpandsTopLevelItems()
    {
        var source = """
            Values = 10, 20, 30
            avg(Values)
            """;

        AssertEval(source, 20);
    }

    // -- Sequence builtin dot-call regression sweep --------------------------

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Count_ExplicitReceiverSweep()
        => AssertEval(
            """
            Values = 1, 2, 3
            Grouped = (1, 2, 3)
            Data = (3, 1, 2), (9, 8, 7)
            Values.count
            count(Values)
            Grouped.count
            count(Grouped)
            (Data:0).count
            count(Data:0)
            """,
            3,
            3,
            1,
            1,
            3,
            3);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Contains_ExplicitReceiverSweep()
        => AssertEval(
            """
            Values = 1, 2, 3
            Grouped = (1, 2, 3)
            Data = (3, 1, 2), (9, 8, 7)
            Values.contains(2)
            contains(Values, 2)
            Grouped.contains(2)
            Grouped.contains((1, 2, 3))
            (Data:0).contains(2)
            contains(Data:0, 2)
            """,
            1,
            1,
            0,
            1,
            1,
            1);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_OrderAndOrderDesc_ProjectionSweep()
        => AssertEval(
            """
            Values = 3, 1, 2
            Data = (3, 1, 2), (9, 8, 7)
            Values.order
            Values.orderDesc
            (Data:0).order
            order(Data:0)
            (Data:0).orderDesc
            orderDesc(Data:0)
            """,
            1,
            2,
            3,
            3,
            2,
            1,
            1,
            2,
            3,
            1,
            2,
            3,
            3,
            2,
            1,
            3,
            2,
            1);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_OrderAndOrderDesc_UngroupedHelpersMatchPlainCall()
    {
        AssertEval(
            """
            Values = 3, 1, 2
            order(Values)
            orderDesc(Values)
            """,
            1,
            2,
            3,
            3,
            2,
            1);

        AssertBuiltinFailureWithExactContext(
            """
            Grouped = (3, 1, 2)
            Grouped.order
            """,
            "order expects each collection element to be a single numeric value; item 0 was grouped value");

        AssertBuiltinFailureWithExactContext(
            """
            Grouped = (3, 1, 2)
            Grouped.orderDesc
            """,
            "orderDesc expects each collection element to be a single numeric value; item 0 was grouped value");
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_FirstAndLast_ProjectionSweep()
        => AssertEval(
            """
            Values = 5, 6, 7
            Data = (9, 8, 7), (3, 2, 1)
            Values.first
            Values.last
            (Data:0).first
            first(Data:0)
            (Data:0).last
            last(Data:0)
            """,
            5,
            7,
            9,
            9,
            7,
            7);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_FirstAndLast_GroupedReceiversAgreeWithPlainCall()
    {
        var result = EvalFull(
            """
            Grouped = (5, 6, 7)
            Grouped.first
            first(Grouped)
            Grouped.last
            last(Grouped)
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertNestedGroupedAtoms(
            result.Value,
            [5m, 6m, 7m],
            [5m, 6m, 7m],
            [5m, 6m, 7m],
            [5m, 6m, 7m]);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Distinct_ProjectionSweep()
        => AssertEval(
            """
            Values = 1, 2, 1, 3
            Data = (1, 2, 1, 3), (9, 8, 9)
            Values.distinct
            (Data:0).distinct
            distinct(Data:0)
            """,
            1,
            2,
            3,
            1,
            2,
            3,
            1,
            2,
            3);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Distinct_GroupedReceiversAgreeWithPlainCall()
    {
        var result = EvalFull(
            """
            Grouped = (1, 2, 1, 3)
            Grouped.distinct
            distinct(Grouped)
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertNestedGroupedAtoms(result.Value, [1m, 2m, 1m, 3m], [1m, 2m, 1m, 3m]);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_TakeAndSkip_ExplicitReceiverSweep()
        => AssertEval(
            """
            Values = 1, 2, 3
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            Values.take(2)
            take(Values, 2)
            Values.skip(1)
            skip(Values, 1)
            (Data:0).take(2)
            take(Data:0, 2)
            (Data:0).skip(2)
            skip(Data:0, 2)
            """,
            1,
            2,
            1,
            2,
            2,
            3,
            2,
            3,
            7,
            6,
            7,
            6,
            4,
            2,
            1,
            4,
            2,
            1);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_TakeAndSkip_GroupedReceiversAgreeWithPlainCall()
    {
        var takeResult = EvalFull(
            """
            Grouped = (1, 2, 3)
            Grouped.take(2)
            take(Grouped, 2)
            """);

        if (takeResult.IsError)
            Assert.Fail($"Expected success but got error: {takeResult.Error}");

        AssertNestedGroupedAtoms(takeResult.Value, [1m, 2m, 3m], [1m, 2m, 3m]);

        AssertEval(
            """
            Grouped = (1, 2, 3)
            Grouped.skip(1)
            skip(Grouped, 1)
            """);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_InlineReceiver_StripsOneOuterBlockLayer()
        => AssertEval(
            """
            AddOne = x + 1
            IsLarge = x > 1
            Add = x + total
            (1, 2, 3).count
            (1, 2, 3).contains(2)
            (3, 1, 2).order
            (5, 6, 7).first
            (5, 6, 7).last
            (1, 2, 1, 3).distinct
            (1, 2, 3).take(2)
            (1, 2, 3).skip(1)
            (10, 4, 7).min
            {10, 4, 7}.max
            {3, 5, 3}.sum
            (10, 4, 7).avg
            (1, 2, 3).map(AddOne)
            {1, 2, 3, 4}.filter(IsLarge)
            (1, 2, 3).reduce(Add, 0)
            """,
            3,
            1,
            1,
            2,
            3,
            5,
            7,
            1,
            2,
            3,
            1,
            2,
            2,
            3,
            4,
            10,
            11,
            7,
            2,
            3,
            4,
            2,
            3,
            4,
            6);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_NumericAggregations_ProjectionSweep()
        => AssertEval(
            """
            Values = 1, 2, 3
            Data = (3, 1, 2), (9, 8, 7)
            Values.sum
            Values.avg
            Values.min
            Values.max
            (Data:0).sum
            sum(Data:0)
            (Data:0).avg
            avg(Data:0)
            (Data:0).min
            min(Data:0)
            (Data:0).max
            max(Data:0)
            """,
            6,
            2,
            1,
            3,
            6,
            6,
            2,
            2,
            1,
            1,
            3,
            3);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_NumericAggregations_UngroupedHelpersMatchPlainCall()
    {
        AssertEval(
            """
            Values = 1, 2, 3
            sum(Values)
            avg(Values)
            min(Values)
            max(Values)
            """,
            6,
            2,
            1,
            3);

        AssertBuiltinFailureWithExactContext(
            """
            Grouped = (1, 2, 3)
            Grouped.sum
            """,
            "sum expects each collection element to be a single numeric value; item 0 was grouped value");

        AssertBuiltinFailureWithExactContext(
            """
            Grouped = (1, 2, 3)
            Grouped.avg
            """,
            "avg expects each collection element to be a single numeric value; item 0 was grouped value");

        AssertBuiltinFailureWithExactContext(
            """
            Grouped = (1, 2, 3)
            Grouped.min
            """,
            "min expects each collection element to be a single numeric value; item 0 was grouped value");

        AssertBuiltinFailureWithExactContext(
            """
            Grouped = (1, 2, 3)
            Grouped.max
            """,
            "max expects each collection element to be a single numeric value; item 0 was grouped value");
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Map_ExplicitReceiverSweep()
        => AssertEval(
            """
            ItemCount(x) = x.count
            AddOne = x + 1
            Items = (1, 2, 3), 7
            Grouped = (1, 2, 3)
            Data = (1, 2, 3), (4, 5, 6)
            Items.map(ItemCount)
            map(Items, ItemCount)
            Grouped.map(ItemCount)
            map(Grouped, ItemCount)
            (Data:0).map(AddOne)
            map(Data:0, AddOne)
            """,
            3,
            1,
            2,
            3,
            3,
            2,
            3,
            4,
            2,
            3,
            4);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Filter_ExplicitReceiverSweep()
        => AssertEval(
            """
            KeepCountThree(x) = x.count == 3
            IsLarge = x > 1
            Items = (1, 2, 3), (4, 5, 6), 7
            Grouped = (1, 2, 3)
            Data = (1, 2, 3), (4, 5, 6)
            Items.filter(KeepCountThree).count
            filter(Items, KeepCountThree).count
            Grouped.filter(KeepCountThree).count
            filter(Grouped, KeepCountThree).count
            (Data:0).filter(IsLarge).count
            filter(Data:0, IsLarge).count
            """,
            2,
            1,
            1,
            1,
            2,
            2);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Reduce_ExplicitReceiverSweep()
        => AssertEval(
            """
            AddItemCount(item, acc) = item.count + acc
            Add = x + total
            Items = (1, 2, 3), 7
            Grouped = (1, 2, 3)
            Data = (1, 2, 3), (4, 5, 6)
            Items.reduce(AddItemCount, 0)
            reduce(Items, AddItemCount, 0)
            Grouped.reduce(AddItemCount, 0)
            reduce(Grouped, AddItemCount, 0)
            (Data:0).reduce(Add, 0)
            reduce(Data:0, Add, 0)
            """,
            4,
            2,
            3,
            3,
            6,
            6);

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
            Sum = repeat(Add, (6), (0, 0)) : 1
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

    // â”€â”€ Result join (semicolon) â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_ResultJoin_JoinsReferencedResults()
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
    public void Eval_Open_ResultJoinTargetFails()
    {
        var source = """
            A = (public X = 1
            X)
            B = (public Y = 2
            Y)
            open A; B
            X + Y
            """;
        AssertEvalAllPublicFails(source);
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
        var dotContext = Assert.IsType<DotCallContext>(contextual.ErrorContext);
        Assert.Equal("Lib", dotContext.ReceiverDescription);
        Assert.Equal("B", dotContext.PropertyName);
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
    public void Eval_MissingOutput_CallUse_CarriesStructuredCallContext()
    {
        var result = EvalFull(
            """
            A = {
                X = 1
            }
            A()
            """);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var contextual = Assert.IsType<EvalError.WithContext>(result.Error);
        var callContext = Assert.IsType<CallContext>(contextual.ErrorContext);
        Assert.Equal("A", callContext.CalleeDescription);
        Assert.IsType<EvalError.MissingOutput>(contextual.Inner);

        Assert.Equal(
            "Cannot call 'A' because it does not define an output. Add an Output expression inside it, or call one of its properties instead.",
            KatLangError.FromEvalError(result.Error).Message);
    }

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
    public void Eval_DotCall_ReceiverBoundary_NormalCallStillUnpacksFinalArg()
    {
        AssertEval(
            """
            F = a + b
            F(3, 7)
            """,
            10);

        AssertEval(
            """
            F = a + b
            F((3, 7))
            """,
            10);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_ScalarReceiverWithExplicitArgStillWorks()
    {
        var source = """
            F = a + b
            (3).F(7)
            """;

        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_MultiOutputReceiverDoesNotSpread()
    {
        var source = """
            F = a + b
            (3, 7).F
            """;

        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_EmptyArgsDoNotSpreadMultiOutputReceiver()
    {
        var source = """
            F = a + b
            (3, 7).F()
            """;

        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_CountedPathDoesNotSpreadMultiOutputReceiver()
    {
        var source = """
            F = a + b
            ((3, 7).F).count
            """;

        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_OneParamReceivesGroupedReceiver()
    {
        var result = EvalFull(
            """
            G = x
            (3, 7).G
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        AssertGroupedAtoms(result.Value, 3, 7);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_FinalExplicitArgStillUnpacks()
    {
        var source = """
            H = a + b + c
            (3).H((4, 5))
            """;

        AssertEval(source, 12);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_SequenceBuiltinsStillExpandReceiverContent()
    {
        AssertEval("(3, 7).sum", 10);
        AssertEval("(3, 7).count", 2);
        AssertEval("(3, 7).first", 3);
        AssertEval("(3, 7).last", 7);
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
    public void Eval_UnknownIdentifier_CarriesStructuredImplicitParameterContext()
    {
        var error = GetEvalError("Sum");
        Assert.NotNull(error);

        var contextual = Assert.IsType<EvalError.WithContext>(error);
        var implicitContext = Assert.IsType<ImplicitParameterContext>(contextual.ErrorContext);
        Assert.Equal(["Sum"], implicitContext.ParamNames);
        Assert.Equal(0, implicitContext.ProvidedArgumentCount);

        var unresolved = Assert.IsType<EvalError.UnresolvedImplicitParams>(contextual.Inner);
        Assert.Equal(["Sum"], unresolved.ParamNames);

        var formatted = KatLangError.FromEvalError(error).Message;
        Assert.Contains("KatLang interprets it as an implicit parameter", formatted);
        Assert.Contains("expected 1 argument, got 0", formatted);
        Assert.DoesNotContain("while evaluating", formatted);
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
        public void Eval_ArityMismatch_DirectCall_CarriesStructuredCallContext()
        {
            var source = """
                Add = a + b
                Add(1)
                """;

            var result = EvalFull(source);
            if (result.IsOk)
                Assert.Fail($"Expected evaluation failure but got: {result.Value}");

            var contextual = Assert.IsType<EvalError.WithContext>(result.Error);
            var callContext = Assert.IsType<CallContext>(contextual.ErrorContext);
            Assert.Equal("Add", callContext.CalleeDescription);

            var arity = Assert.IsType<EvalError.ArityMismatch>(contextual.Inner);
            Assert.Equal(2, arity.Expected);
            Assert.Equal(1, arity.Actual);

            Assert.Equal(
                "Property 'Add' expects 2 parameters, but was called with 1 argument.",
                KatLangError.FromEvalError(result.Error).Message);
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
            var propertyContext = Assert.IsType<PropertyEvaluationContext>(contextual.ErrorContext);
            Assert.Equal("A", propertyContext.PropertyName);
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
    public void Eval_Open_ResultJoinDoesNotMergeLibraries()
    {
        var source = """
            A = (public X = 1)
            B = (public Y = 2)
            open A; B
            X + Y
            """;
        AssertEvalAllPublicFails(source);
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

    // ── Semicolon: result join operator ─────────────────────────────────────

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

    // C. Result join emits immediate results

    [Fact]
    public void Eval_ResultJoin_TwoFragments()
    {
        AssertEval("1 + 2, 2 + 3; 3 + 4", 3, 5, 7);
    }

    [Fact]
    public void Eval_ResultJoin_MultipleFragments()
    {
        AssertEval("1 + 2, 2 + 3; 3 + 4; 4 + 5, 5 + 6, 6 + 7", 3, 5, 7, 9, 11, 13);
    }

    [Fact]
    public void Eval_ResultJoin_LongChain_IsStackSafeForFlatAndCountedEvaluation()
    {
        const int itemCount = 8192;
        var chain = LongOneChain(itemCount);

        var flatR = Evaluator.RunFlat(chain);
        if (flatR.IsError)
            Assert.Fail($"Expected success but got error: {flatR.Error}");
        Assert.Equal(Enumerable.Repeat(1m, itemCount), flatR.Value);

        var countedRoot = new Expr.Block(new Algorithm.User(
            Parent: null,
            Params: [],
            Opens: [],
            Properties: [new Property("Values", new Algorithm.User(
                Parent: null,
                Params: [],
                Opens: [],
                Properties: [],
                Output: [chain]))],
            Output:
            [
                BuiltinCall("sum", new Expr.Resolve("Values")),
                BuiltinCall("count", new Expr.Resolve("Values"))
            ]));

        var countedR = Evaluator.RunFlat(countedRoot);
        if (countedR.IsError)
            Assert.Fail($"Expected success but got error: {countedR.Error}");
        Assert.Equal([(decimal)itemCount, (decimal)itemCount], countedR.Value);

        static Expr LongOneChain(int count)
        {
            Expr expr = new Expr.Num(1);
            for (var i = 1; i < count; i++)
                expr = new Expr.ResultJoin(expr, new Expr.Num(1));
            return expr;
        }

        static Expr BuiltinCall(string name, Expr arg) =>
            new Expr.Call(
                new Expr.Resolve(name),
                new Algorithm.User(
                    Parent: null,
                    Params: [],
                    Opens: [],
                    Properties: [],
                    Output: [arg]));
    }

    [Fact]
    public void Eval_ResultJoin_SequenceBuiltins_ConsumeFlatTopLevelItems()
    {
        AssertEval("sum(1; 2; 3; 4)", 10);
        AssertEval("count(1; 2; 3; 4)", 4);
        AssertEval("first(1; 2; 3; 4)", 1);
        AssertEval("last(1; 2; 3; 4)", 4);
    }

    [Fact]
    public void Eval_ResultJoin_CommaSimilarityForSimpleConstants()
    {
        var source = """
            A = 1, 2
            B = 1; 2
            A.count
            B.count
            """;

        AssertEval(source, 2, 2);
    }

    [Fact]
    public void Eval_ResultJoin_GroupsJoinOneLevel()
    {
        AssertEval("(1, 2); 3", 1, 2, 3);
        AssertEval("1; (2, 3)", 1, 2, 3);
        AssertEval("(1, 2); (3, 4)", 1, 2, 3, 4);
    }

    [Fact]
    public void Eval_ResultJoin_NestedGroupsArePreserved()
    {
        var nestedLeft = EvalFull("((1, 2)); 3");
        if (nestedLeft.IsError)
            Assert.Fail($"Expected success but got error: {nestedLeft.Error}");

        var leftGroup = Assert.IsType<Result.Group>(nestedLeft.Value);
        Assert.Equal(2, leftGroup.Items.Count);
        AssertGroupedAtoms(leftGroup.Items[0], 1, 2);
        AssertAtomValue(leftGroup.Items[1], 3);

        var nestedMiddle = EvalFull("(1, (2, 3)); 4");
        if (nestedMiddle.IsError)
            Assert.Fail($"Expected success but got error: {nestedMiddle.Error}");

        var middleGroup = Assert.IsType<Result.Group>(nestedMiddle.Value);
        Assert.Equal(3, middleGroup.Items.Count);
        AssertAtomValue(middleGroup.Items[0], 1);
        AssertGroupedAtoms(middleGroup.Items[1], 2, 3);
        AssertAtomValue(middleGroup.Items[2], 4);
    }

    [Fact]
    public void Eval_ResultJoin_InlineDotCallCountMatchesComma()
    {
        AssertEval("(1; 2).count", 2);
        AssertEval("(1, 2).count", 2);
    }

    [Fact]
    public void Eval_ResultJoin_GroupedLeaves_CountJoinedTopLevelItems()
    {
        AssertEval("count((1, 2); 3)", 3);
        AssertEval("count(1; (2, 3))", 3);
    }

    [Fact]
    public void Eval_ResultJoin_MixedPropertyAndMultiOutput_SumsExpandedItems()
    {
        var source = """
            P = 1, 2
            X = sum(P; 3; 4; 5)
            X
            """;
        AssertEval(source, 15);
    }

    [Fact]
    public void Eval_ResultJoin_ErrorOrder_StopsAtEarlierLeaf()
    {
        var error = GetEvalError("1; Math.Nope; 1 / 0");
        Assert.NotNull(error);

        var inner = error!;
        while (inner is EvalError.WithContext context)
            inner = context.Inner;

        var unknown = Assert.IsType<EvalError.UnknownName>(inner);
        Assert.Equal("Nope", unknown.Name);
    }

    // D. Result joining by reference

    [Fact]
    public void Eval_ResultJoin_ByReference()
    {
        var source = """
            Property1 = 1
            Property2 = 2, 3
            Property1; Property2
            """;
        AssertEval(source, 1, 2, 3);
    }

    // E. Result joining call outputs with additional expressions

    [Fact]
    public void Eval_ResultJoin_Extension()
    {
        // Simplified version of the motivating pattern:
        // Result join calls with additional expressions.
        var source = """
            Next = if(a > 5, (a - 1, b + 1), (b - 1, a + 1))
            Result = Next(10, 0); 10 > 5
            Result
            """;
        AssertEval(source, 9, 1, 1);
    }

    // F. Nested algorithm with semicolon result join

    [Fact]
    public void Eval_ResultJoin_InParenAlgorithm()
    {
        // (1 + 2; 3 + 4) is a parameterless nested algorithm with result join.
        AssertEval("(1 + 2; 3 + 4)", 3, 7);
    }

    [Fact]
    public void Eval_ResultJoin_AsFunctionArg()
    {
        // Foo receives a multi-output argument via semicolon result join.
        var source = """
            Foo = x, y
            Foo(1 + 2; 3 + 4)
            """;
        AssertEval(source, 3, 7);
    }

    // G. Capturing algorithm with semicolon result join

    [Fact]
    public void Eval_ResultJoin_InBraceAlgorithm()
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
    public void Eval_ResultJoin_MultilineEquivalentToOneline()
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

    [Fact]
    public void Eval_ResultJoin_DotCallReceiverBoundaryCanBeJoined()
    {
        var commaSource = """
            A = 1, 2
            F = a, 3
            A.F
            """;

        var commaResult = EvalFull(commaSource);
        if (commaResult.IsError)
            Assert.Fail($"Expected success but got error: {commaResult.Error}");

        var commaGroup = Assert.IsType<Result.Group>(commaResult.Value);
        Assert.Equal(2, commaGroup.Items.Count);
        AssertGroupedAtoms(commaGroup.Items[0], 1, 2);
        AssertAtomValue(commaGroup.Items[1], 3);

        var joinSource = """
            A = 1, 2
            F = a; 3
            A.F
            """;

        AssertEval(joinSource, 1, 2, 3);
    }

    [Fact]
    public void Eval_ResultJoin_DoesNotPreserveOrMergeProperties()
    {
        var valueSource = """
            A = {
                X = 1
                10
            }

            B = {
                Y = 2
                20
            }

            C = A; B
            C
            """;
        AssertEval(valueSource, 10, 20);

        var xSource = """
            A = {
                X = 1
                10
            }

            B = {
                Y = 2
                20
            }

            C = A; B
            C.X
            """;
        AssertEvalFails(xSource);

        var ySource = """
            A = {
                X = 1
                10
            }

            B = {
                Y = 2
                20
            }

            C = A; B
            C.Y
            """;
        AssertEvalFails(ySource);
    }

    [Fact]
    public void Eval_ResultJoin_NoOutputOperandFails()
    {
        var leftSource = """
            Bad = {
                X = 1
            }

            Bad; 3
            """;
        AssertResultJoinMissingOutput(leftSource, "left");

        var rightSource = """
            Bad = {
                X = 1
            }

            3; Bad
            """;
        AssertResultJoinMissingOutput(rightSource, "right");
    }

    // Additional: simple result join of two literals

    [Fact]
    public void Eval_ResultJoin_SimpleLiterals()
    {
        AssertEval("1; 2", 1, 2);
        AssertEval("1; 2; 3", 1, 2, 3);
    }

    [Fact]
    public void Eval_ResultJoin_PropertyBody()
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
        // Named algorithm V = 42 resolves structurally and also evaluates to a value.
        // This is about lexical algorithm lookup, not zero-parameter inline blocks.
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
    public void Eval_HigherOrder_GroupedValueBeforeAlgorithmOnlyArg_KeepsFilteredGroupCountAsOne()
    {
        var source = """
            OccurrenceCount = filter(values, predicate).count
            OccurrenceCount((1, 2), {n:0 mod 2 == 1})
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_HigherOrder_InlinePredicate_CapturesOuterValueParameter_WithoutUnwrappingGroupedResult()
    {
        var source = """
            OccurrenceCount(target) = {
                MatchesTarget(pair) = pair:1 == target:1
                filter((1, 10), (2, 20), (2, 30), MatchesTarget)
            }
            OccurrenceCount((2, 20))
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertGroupedAtoms(result.Value, 2m, 20m);
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
    public void Eval_ClauseGroup_DoubleParenGroupedPattern_MatchesSingleBinderArity()
    {
        var source = """
            MarkGroupedRange((a, b, c)) = 1
            MarkGroupedRange(x) = 0
            MarkGroupedRange(5)
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_ClauseGroup_DoubleParenGroupedPattern_MatchesSingleRangeArgument()
    {
        var source = """
            MarkGroupedRange((a, b, c)) = 1
            MarkGroupedRange(x) = 0
            MarkGroupedRange(range(1, 3))
            """;

        AssertEval(source, 1);
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
    public void Eval_InlineBlock_ZeroParamSingleOutputInParens_RemainsValueStructure()
    {
        // Zero-parameter inline blocks stay value/output structures in
        // higher-order argument position.
        AssertEval("Apply(f) = f\nApply({123})", 123);
    }

    [Fact]
    public void Eval_InlineBlock_ZeroParamSingleOutputInParens_IsNotAutoCallable()
    {
        // A zero-parameter inline block does not become callable just because
        // it emits exactly one output.
        AssertEvalFails("Apply(f) = f()\nApply({123})");
    }

    [Fact]
    public void Eval_InlineBlock_ZeroParamMultiOutputInParens_RemainsValueStructure()
    {
        // Output count does not change higher-order binding mode.
        AssertEval("Apply(f) = f\nApply({1, 2})", 1, 2);
    }

    [Fact]
    public void Eval_InlineBlock_ZeroParamMultiOutputInParens_IsNotAutoCallable()
    {
        // Multi-output zero-parameter inline blocks follow the same rule as
        // single-output ones: they stay value/output structures rather than
        // callable higher-order arguments.
        AssertEvalFails("Apply(f) = f()\nApply({1, 2})");
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
        var contextual = Assert.IsType<EvalError.WithContext>(error);
        var implicitContext = Assert.IsType<ImplicitParameterContext>(contextual.ErrorContext);
        Assert.Equal(["a"], implicitContext.ParamNames);
        Assert.Equal(0, implicitContext.ProvidedArgumentCount);

        var uip = Assert.IsType<EvalError.UnresolvedImplicitParams>(contextual.Inner);
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
        var contextual = Assert.IsType<EvalError.WithContext>(error);
        var implicitContext = Assert.IsType<ImplicitParameterContext>(contextual.ErrorContext);
        Assert.Equal(["a", "b"], implicitContext.ParamNames);
        Assert.Equal(0, implicitContext.ProvidedArgumentCount);

        var uip = Assert.IsType<EvalError.UnresolvedImplicitParams>(contextual.Inner);
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
