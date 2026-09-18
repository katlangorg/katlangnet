using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorStringTests
{
    [Fact]
    public void Eval_Arity_IsNoLongerRecognizedAsIntrinsic_OnPropertyReceiver()
        => AssertUnknownDotMember(ClosedMemberProbe("Data = 1, 7\n", "Data.arity"), "arity");

    [Fact]
    public void Eval_Arity_IsNoLongerRecognizedAsIntrinsic_OnInlineParenReceiver()
        => AssertUnknownDotMember(ClosedMemberProbe("", "(1, 7).arity"), "arity");

    [Fact]
    public void Eval_Arity_IsNoLongerRecognizedAsIntrinsic_OnNestedParenReceiver()
        => AssertUnknownDotMember(ClosedMemberProbe("", "((1, 7)).arity"), "arity");

    [Fact]
    public void Eval_Length_IsNoLongerRecognizedAsIntrinsic()
        => AssertUnknownDotMember(ClosedMemberProbe("X = 1, 2, 3\n", "X.length"), "length");

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

    // ── `.string(args)`: the intrinsic is a ZERO-parameter member ───────────

    /// <summary>
    /// Final audit (September 2026): a written argument list on the <c>.string</c>
    /// intrinsic used to be silently DROPPED (<c>A.string(1)</c> converted <c>A</c> as
    /// if no arguments were written). The intrinsic is a zero-parameter member: the
    /// written slots are assembled exactly like every call's — each slot evaluated once,
    /// spreads opened — and then rejected by arity (<c>ArityMismatch(0, n)</c>), the
    /// outcome <c>Obj.V(1)</c> has for a declared zero-parameter member, on BOTH receiver
    /// paths (algorithm receiver, value receiver). Lean:
    /// <c>rejectDotStringIntrinsicArguments</c>, CoreTests <c>Strings.lean</c>.
    /// </summary>
    [Theory]
    [InlineData("A = 42\nA.string(1)", 1)]                        // algorithm receiver (named property)
    [InlineData("A = 42\nA.string(1, 2)", 2)]
    [InlineData("42.string(1)", 1)]                               // value receiver (notAnAlgorithm path)
    [InlineData("(10 + 5).string(1, 2, 3)", 3)]
    [InlineData("S = 1, 2\nA = 42\nA.string(S*)", 2)]              // a spread slot counts by its opened items
    [InlineData("S = 1, 2\nA = 42\nA.string(0, S*)", 3)]
    [InlineData("Obj = {\n    5\n}\nObj.string(1)", 1)]           // brace algorithm receiver
    public void Eval_StringIntrinsic_RejectsWrittenArguments_ByArity(string source, int written)
        => AssertEvalFailsWithArityMismatch(source, expected: 0, actual: written);

    [Theory]
    [InlineData("A = 42\nA.string()", "42")]
    [InlineData("42.string()", "42")]
    [InlineData("E = ()\nA = 42\nA.string(E*)", "42")]            // a spread of nothing writes no slot
    public void Eval_StringIntrinsic_EmptyWrittenArgumentList_StaysTheIntrinsic(string source, string expected)
        => AssertEvalString(source, expected);

    [Fact]
    public void Eval_StringIntrinsic_WrittenArgumentsAreEvaluatedBeforeTheArityRejection()
    {
        // Assembly precedes the rejection, so a failing slot reports ITS error, exactly as
        // for any call whose argument fails before arity is checked.
        var result = EvalFull("A = 42\nA.string(1 / 0)");
        Assert.True(result.IsError);
        Assert.IsType<EvalError.DivByZero>(Innermost(result.Error));
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
        var alg = new Algorithm.User(Parent: null, ParameterPatterns: [], Opens: [],
            Properties: [], Output: [unaryExpr]);
        var result = Evaluator.Run(new Expr.AlgorithmExpr(alg));
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
    public void Eval_String_MixedEquality_DifferentKinds_ReturnsZero()
    {
        // `==` compares values structurally; a number and a string are different
        // value kinds, so they compare unequal (0) rather than raising a type
        // mismatch. Arithmetic/ordering on mixed string operands still fails.
        AssertEval("1 == 'a'", 0);
    }

    [Fact]
    public void Eval_String_MixedInequality_DifferentKinds_ReturnsOne()
        => AssertEval("1 != 'a'", 1);

    [Fact]
    public void Eval_String_SinFails()
    {
        // Math.Sin('a') should fail with type mismatch (builtin expects numeric argument)
        AssertEvalFailsWithTypeMismatch("Math.Sin('a')", "Expected a number, got a string");
    }
}
