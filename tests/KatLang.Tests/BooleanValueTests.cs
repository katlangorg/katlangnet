using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

/// <summary>
/// The first-class Boolean value model (September 2026), pinned end to end: `true` and
/// `false` are a value kind of their own (Lean <c>Result.bool</c>, C# <c>Result.Bool</c>),
/// never numbers; comparisons and the logical operators produce and consume them; every
/// predicate position — the <c>if</c> condition, a <c>filter</c> predicate result, the
/// <c>while</c> continuation flag — REQUIRES one; equality stays total across kinds while
/// ordering and arithmetic reject Booleans; and there is no numeric truthiness anywhere:
/// the programs that once relied on `0`/non-zero truth now fail with a
/// <see cref="EvalError.TypeMismatch"/> that names the value actually supplied.
/// Lean twins: <c>lean/CoreTests/Numerics.lean</c>, <c>Conditionals.lean</c>,
/// <c>SequenceCallbackBuiltins.lean</c>, <c>CollectingParameters.lean</c>.
/// </summary>
public class BooleanValueTests
{
    private static string Display(string source)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString().ReplaceLineEndings("\n");

    private static KatLangError EngineFailure(string source)
        => Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)).Errors);

    private static Expr Program(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    // ── Literals, lexing, and display ───────────────────────────────────────

    [Fact]
    public void Literals_AreDistinctFirstClassValues()
    {
        AssertEvalBool("true", true);
        AssertEvalBool("false", false);
        AssertEvalBools("true, false", true, false);
        AssertEvalBool("(true)", true);
        AssertEvalBool("((false))", false);
        Assert.IsType<Result.Bool>(Assert.IsType<RunResult.Success>(KatLangEngine.Run("true")).Value);
    }

    [Fact]
    public void Literals_DisplayLowercase_InEveryPosition()
    {
        Assert.Equal("true\nfalse", Display("true\nfalse"));
        Assert.Equal("(true, 1)", Display("(true, 1)"));
        Assert.Equal("[true, false]", Display("[true, false]"));
        Assert.Equal("((false, x), [true])", Display("((false, 'x'), [true])"));
        Assert.Equal("true", Evaluator.FormatResultForDiagnostic(new Result.Bool(true)));
    }

    [Fact]
    public void Literals_AreKeywordTokens_NeverIdentifiers()
    {
        var (tokens, diagnostics) = Lexer.Tokenize("true false trueish");
        Assert.Empty(diagnostics);
        Assert.Equal(
            [TokenKind.KeywordTrue, TokenKind.KeywordFalse, TokenKind.Identifier, TokenKind.EndOfFile],
            tokens.Select(t => t.Kind));
        Assert.False(Lexer.IsValidIdentifier("true"));
        Assert.False(Lexer.IsValidIdentifier("false"));
        Assert.True(Lexer.IsValidIdentifier("trueish"));
        Assert.Contains("true", Lexer.KeywordNames);
        Assert.Contains("false", Lexer.KeywordNames);
    }

    // ── Reserved names ──────────────────────────────────────────────────────

    [Theory]
    [InlineData("true = 1", "true", 1)]
    [InlineData("false = 0\nfalse", "false", 1)]
    [InlineData("public true = 1", "true", 8)]
    [InlineData("false(x) = x", "false", 1)]
    [InlineData("F(x) = x\ntrue(y) = y", "true", 1)]
    public void ReservedLiteral_CannotBeDeclared(string source, string spelling, int column)
    {
        var parsed = Parser.Parse(source);
        Assert.True(parsed.HasErrors, $"`{source}` must not parse cleanly");
        var diagnostic = Assert.Single(
            parsed.Diagnostics,
            d => d.Message.Contains($"'{spelling}' is the reserved Boolean literal, not a name", StringComparison.Ordinal));
        Assert.Contains("cannot be shadowed", diagnostic.Message, StringComparison.Ordinal);
        Assert.NotNull(diagnostic.Span);
        Assert.Equal(column, Assert.NotNull(diagnostic.Span).Start.Column);
    }

    [Theory]
    [InlineData("true, x = 1, 2")]
    [InlineData("a, false = 1, 2")]
    [InlineData("x, *true = 1, 2, 3")]
    public void ReservedLiteral_CannotBeADeconstructionTarget(string source)
        => Assert.True(Parser.Parse(source).HasErrors, $"`{source}` must not parse cleanly");

    [Fact]
    public void ReservedLiteral_IsNeverAnImplicitParameter()
    {
        // `true` is a literal, so an algorithm reading it infers nothing from it: F has
        // exactly the one free name `x`.
        AssertEvalBool("F = true and x\nF(false)", false);
        AssertEvalBool("F = true and x\nF(true)", true);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(FailureOf("F = x or false\nF(true, false)")));
        Assert.Equal(1, arity.Expected);
        Assert.Equal(2, arity.Actual);
    }

    [Fact]
    public void ReservedLiteral_IsALiteralPattern_InConditionalAlgorithms()
    {
        // `F(true)` is the literal pattern `.litBool true`, never a binder named `true`.
        Assert.Equal("pos\nnonpos", Display("Sign(true) = 'pos'\nSign(false) = 'nonpos'\nSign(5 > 0)\nSign(-5 > 0)"));
        AssertEval("Flip(true, a, b) = a\nFlip(false, a, b) = b\nFlip(1 < 2, 10, 20)", 10);
        AssertEval("Flip(true, a, b) = a\nFlip(false, a, b) = b\nFlip(1 > 2, 10, 20)", 20);

        // A number never matches a Boolean pattern, and vice versa: the kinds are disjoint.
        Assert.IsType<EvalError.NoMatchingBranch>(Innermost(FailureOf("F(true) = 1\nF(1)")));
        Assert.IsType<EvalError.NoMatchingBranch>(Innermost(FailureOf("F(1) = 1\nF(true)")));
        Assert.IsType<EvalError.NoMatchingBranch>(Innermost(FailureOf("F(true) = 1\nF((true, true))")));

        // Match-equivalent Boolean patterns are the ordinary duplicate-branch rejection.
        Assert.Equal(
            KatLangErrorCode.DuplicateBranchPattern,
            Assert.Single(Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("F(true) = 1\nF(true) = 2\nF(true)")).Errors).Code);
    }

    private static EvalError FailureOf(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"`{source}` unexpectedly succeeded with {result.Value}");
        return result.Error;
    }

    // ── Comparisons ─────────────────────────────────────────────────────────

    [Theory]
    [InlineData("1 < 2", true)]
    [InlineData("2 < 1", false)]
    [InlineData("2 <= 2", true)]
    [InlineData("3 <= 2", false)]
    [InlineData("2 > 1", true)]
    [InlineData("1 > 2", false)]
    [InlineData("2 >= 2", true)]
    [InlineData("1 >= 2", false)]
    [InlineData("2 == 2", true)]
    [InlineData("2 == 3", false)]
    [InlineData("2 != 3", true)]
    [InlineData("2 != 2", false)]
    [InlineData("'a' == 'a'", true)]
    [InlineData("'a' != 'a'", false)]
    [InlineData("(1, 2) == (1, 2)", true)]
    [InlineData("[1] == [1]", true)]
    [InlineData("() == ()", true)]
    public void EveryComparison_ProducesABoolean(string source, bool expected)
        => AssertEvalBool(source, expected);

    [Theory]
    [InlineData("true == true", true)]
    [InlineData("true == false", false)]
    [InlineData("false != true", true)]
    [InlineData("true == 1", false)]
    [InlineData("true != 1", true)]
    [InlineData("false == 0", false)]
    [InlineData("false != 0", true)]
    [InlineData("true == 'true'", false)]
    [InlineData("true == (true)", true)]
    [InlineData("true == [true]", false)]
    [InlineData("false == ()", false)]
    [InlineData("(true, 1) == (true, 1)", true)]
    [InlineData("(true, 1) == (1, 1)", false)]
    [InlineData("[true, false] == [true, false]", true)]
    [InlineData("[true] == (true)", false)]
    public void Equality_IsTotalAcrossKinds_AndNeverConvertsABoolean(string source, bool expected)
        => AssertEvalBool(source, expected);

    [Theory]
    [InlineData("true < false", "<", "left operand was a Boolean value: true")]
    [InlineData("true > 0", ">", "left operand was a Boolean value: true")]
    [InlineData("1 <= false", "<=", "right operand was a Boolean value: false")]
    [InlineData("0 >= true", ">=", "right operand was a Boolean value: true")]
    public void Ordering_RejectsBooleans_NamingTheOperand(string source, string op, string blame)
        => AssertEvalFailsWithTypeMismatch(source, $"operator `{op}` expects numeric scalar operands, but the {blame}");

    // ── Arithmetic rejects Booleans ─────────────────────────────────────────

    [Theory]
    [InlineData("true + 1", "+", "left operand was a Boolean value: true")]
    [InlineData("1 * false", "*", "right operand was a Boolean value: false")]
    [InlineData("true - true", "-", "left operand was a Boolean value: true")]
    [InlineData("2 / false", "/", "right operand was a Boolean value: false")]
    [InlineData("true div 1", "div", "left operand was a Boolean value: true")]
    [InlineData("5 mod true", "mod", "right operand was a Boolean value: true")]
    [InlineData("true ^ 2", "^", "left operand was a Boolean value: true")]
    public void Arithmetic_RejectsBooleans_NamingTheOperand(string source, string op, string blame)
        => AssertEvalFailsWithTypeMismatch(source, $"operator `{op}` expects numeric scalar operands, but the {blame}");

    [Fact]
    public void UnaryMinus_RejectsABoolean()
        => AssertEvalFailsWithTypeMismatch("-true", "operator `-` expects a numeric scalar operand, but the operand was a Boolean value: true");

    [Fact]
    public void NumericBuiltins_RejectBooleans()
    {
        AssertEvalFails("sum((true, 1))");
        AssertEvalFails("Math.Abs(true)");
        AssertEvalFails("range(true, 3)");
        AssertEvalFails("true.string");
        AssertEvalFails("order((true, 1))");
    }

    // ── Logical operators ───────────────────────────────────────────────────

    [Theory]
    [InlineData("true and true", true)]
    [InlineData("true and false", false)]
    [InlineData("false and true", false)]
    [InlineData("false and false", false)]
    [InlineData("true or true", true)]
    [InlineData("true or false", true)]
    [InlineData("false or true", true)]
    [InlineData("false or false", false)]
    [InlineData("true xor true", false)]
    [InlineData("true xor false", true)]
    [InlineData("false xor true", true)]
    [InlineData("false xor false", false)]
    [InlineData("not true", false)]
    [InlineData("not false", true)]
    [InlineData("not not true", true)]
    [InlineData("(true)and(false)", false)]
    [InlineData("1 < 2 and 2 < 3", true)]
    [InlineData("1 < 2 and not (2 < 3)", false)]
    [InlineData("1 > 2 or 2 > 1 xor false", true)]
    public void LogicalOperators_AreBooleanAlgebra(string source, bool expected)
        => AssertEvalBool(source, expected);

    [Theory]
    [InlineData("1 and true", "and", "left operand was numeric value 1")]
    [InlineData("true and 1", "and", "right operand was numeric value 1")]
    [InlineData("0 or false", "or", "left operand was numeric value 0")]
    [InlineData("false or 'a'", "or", "right operand was a string: 'a'")]
    [InlineData("true xor ()", "xor", "right operand was a sequence value with 0 sequence elements: ()")]
    [InlineData("[true] and true", "and", "left operand was a list value with 1 element: [true]")]
    [InlineData("(true, false) or true", "or", "left operand was a sequence value with 2 sequence elements: (true, false)")]
    public void LogicalOperators_RejectNonBooleans_NamingTheOperand(string source, string op, string blame)
        => AssertEvalFailsWithTypeMismatch(source, $"operator `{op}` expects Boolean operands, but the {blame}");

    [Theory]
    [InlineData("not 1", "numeric value 1")]
    [InlineData("not 0", "numeric value 0")]
    [InlineData("not -0", "numeric value -0")]
    [InlineData("not 'x'", "a string: 'x'")]
    [InlineData("not ()", "a sequence value with 0 sequence elements: ()")]
    [InlineData("not [true]", "a list value with 1 element: [true]")]
    [InlineData("not (true, true)", "a sequence value with 2 sequence elements: (true, true)")]
    public void Not_RejectsNonBooleans_NamingTheOperand(string source, string blame)
        => AssertEvalFailsWithTypeMismatch(source, $"operator `not` expects a Boolean operand, but the operand was {blame}");

    [Fact]
    public void LogicalOperators_EvaluateBothOperands_WithoutShortCircuit()
    {
        // The established evaluation order is preserved: both operands are evaluated left
        // to right before the operator is applied, so a failing right operand fails even
        // when the left operand already decides the result.
        Assert.IsType<EvalError.DivByZero>(Innermost(FailureOf("false and (1 / 0 == 1)")));
        Assert.IsType<EvalError.DivByZero>(Innermost(FailureOf("true or (1 / 0 == 1)")));
        Assert.IsType<EvalError.DivByZero>(Innermost(FailureOf("Boom = 1 / 0 == 1\nfalse and Boom")));
        // ...and the left operand is validated first: a numeric left operand is blamed even
        // when the right operand would have been rejected too.
        AssertEvalFailsWithTypeMismatch("1 and 2", "operator `and` expects Boolean operands, but the left operand was numeric value 1");
    }

    [Theory]
    [InlineData("not 5 > 3", false)]
    [InlineData("not 2 > 3", true)]
    [InlineData("not 5 == 5", false)]
    [InlineData("not 5 == 4", true)]
    [InlineData("not 5 != 4", false)]
    [InlineData("not 5 < 3", true)]
    [InlineData("not 3 <= 3", false)]
    [InlineData("not 2 >= 3", true)]
    [InlineData("not true == false", true)]
    [InlineData("not true == 1", true)]
    [InlineData("not 'a' == 'a'", false)]
    [InlineData("not 1 + 1 > 3", true)]
    [InlineData("not 2 ^ 3 > 7", false)]
    [InlineData("not 0 ^ 0 == 1", false)]
    [InlineData("not not 5 > 3", true)]
    [InlineData("not (5 > 3)", false)]
    [InlineData("(not true) == false", true)]
    [InlineData("(not true) == (5 > 3)", false)]
    public void Not_BindsBelowTheComparisons(string source, bool expected)
        // comparisons > not > and > xor > or: `not x > 3` is `not (x > 3)`.
        => AssertEvalBool(source, expected);

    [Theory]
    [InlineData("A = true\nB = false\nnot A and B", false)]
    [InlineData("A = false\nB = false\nnot A and B", false)]
    [InlineData("A = true\nB = true\nnot A or B", true)]
    [InlineData("A = true\nB = true\nnot A xor B", true)]
    [InlineData("not 1 > 2 and 2 > 1", true)]
    [InlineData("1 > 2 or not 2 > 3", true)]
    [InlineData("not 1 > 2 xor 2 > 3", true)]
    public void Not_BindsTighterThanTheLogicalOperators(string source, bool expected)
        // `not A and B` is `(not A) and B` (`not (A and B)` would be true for
        // A = B = false), and `not A or B` is `(not A) or B` (`not (A or B)`
        // would be false for A = B = true).
        => AssertEvalBool(source, expected);

    [Fact]
    public void ExplicitGrouping_KeepsTheOtherStructure_AndTypesAccordingly()
    {
        AssertEvalBool("(not true) == false", true);
        AssertEvalFailsWithTypeMismatch("(not true) > 3", "operator `>` expects numeric scalar operands, but the left operand was a Boolean value: false");
        // With the parentheses the operand of `not` is the number; without them it is
        // the comparison, so the Boolean-operand diagnostic is never misattributed.
        AssertEvalFailsWithTypeMismatch("(not 5) > 3", "operator `not` expects a Boolean operand, but the operand was numeric value 5");
        AssertEvalBool("not 5 > 3", false);
        // A parenthesized Boolean exponent is `^`'s numeric-scalar rejection; the bare
        // `2 ^ not false` is a parse error instead (`not` cannot be an operand of `^`).
        AssertEvalFailsWithTypeMismatch("2 ^ (not false)", "operator `^` expects numeric scalar operands, but the right operand was a Boolean value: true");
        Assert.True(Parser.Parse("2 ^ not false").HasErrors);
    }

    [Fact]
    public void Not_OverAComparison_RendersFaithfullyInDiagnostics()
    {
        // The context frame spells the written grouping back: a `not` under a
        // tighter operator keeps parentheses, a negated comparison stays bare.
        var grouped = EngineFailure("(not true) > 3");
        Assert.Contains("while evaluating `(not true) > 3`", grouped.Message, StringComparison.Ordinal);
        var negated = EngineFailure("not true > 3");
        Assert.Contains("while evaluating `true > 3`", negated.Message, StringComparison.Ordinal);
        Assert.Contains("operator `>` expects numeric scalar operands, but the left operand was a Boolean value: true", negated.Message, StringComparison.Ordinal);
    }

    // ── if ──────────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("if(true, 1, 2)", 1)]
    [InlineData("if(false, 1, 2)", 2)]
    [InlineData("if((true), 1, 2)", 1)]
    [InlineData("if(1 < 2 and not (3 > 4), 1, 2)", 1)]
    [InlineData("Flag = 5 > 2\nif(Flag, 1, 2)", 1)]
    [InlineData("true.if(1, 2)", 1)]
    [InlineData("false.if(1, 2)", 2)]
    [InlineData("Args = (false, 1, 2)\nif(Args*)", 2)]
    public void If_SelectsByABooleanCondition(string source, int expected)
        => AssertEval(source, expected);

    [Theory]
    [InlineData("if(1, 1, 2)", "numeric value 1")]
    [InlineData("if(0, 1, 2)", "numeric value 0")]
    [InlineData("if(-1, 1, 2)", "numeric value -1")]
    [InlineData("if(0.5, 1, 2)", "numeric value 0.5")]
    [InlineData("if('x', 1, 2)", "a string: 'x'")]
    [InlineData("if((), 1, 2)", "a sequence value with 0 sequence elements: ()")]
    [InlineData("if([true], 1, 2)", "a list value with 1 element: [true]")]
    [InlineData("if((true, false), 1, 2)", "a sequence value with 2 sequence elements: (true, false)")]
    [InlineData("N = 1 < 2\nif((N, N), 1, 2)", "a sequence value with 2 sequence elements: (true, true)")]
    public void If_RejectsANonBooleanCondition_NamingTheValue(string source, string described)
    {
        AssertEvalFailsWithTypeMismatch(source, $"if condition must be a Boolean value (true or false), but was {described}");
        Assert.Equal(KatLangErrorCode.TypeMismatch, EngineFailure(source).Code);
    }

    [Fact]
    public void If_ConditionRejection_IsUnspannedInnermost_WithTheCallSpanOutside()
    {
        var error = FailureOf("if(1, 10, 20)");
        var innermost = Assert.IsType<EvalError.TypeMismatch>(Innermost(error));
        Assert.Null(innermost.Span);
        Assert.Equal(["while evaluating call to if"], LoopDiagnosticParityAssertions.ContextChain(error));
        Assert.Equal(new SourceSpan(1, 1, 1, 14), EngineFailure("if(1, 10, 20)").Span);
    }

    [Fact]
    public void If_StillEvaluatesOnlyTheSelectedBranch()
    {
        AssertEval("if(true, 10, 1 / 0)", 10);
        AssertEval("if(false, 1 / 0, 20)", 20);
        AssertEval("Boom = 1 / 0\nif(1 > 2, Boom, 7)", 7);
    }

    // ── filter and contains ─────────────────────────────────────────────────

    [Fact]
    public void Filter_KeepsElementsWhosePredicateIsTrue()
    {
        Assert.Equal("[2, 4, 6]", Display("range(1, 6).filter{x mod 2 == 0}"));
        Assert.Equal("[3]", Display("IsBig(x) = x > 2\n(1, 2, 3).filter(IsBig)"));
        Assert.Equal("[]", Display("None(x) = false\nfilter((1, 2, 3), None)"));
        Assert.Equal("[1, 2]", Display("All(x) = true\nfilter((1, 2), All)"));
        Assert.Equal("[7]", Display("Wrapped(x) = (x == 7)\nfilter((6, 7), Wrapped)"));
        Assert.Equal("[true]", Display("filter((true, false), {x})"));
    }

    [Theory]
    [InlineData("filter((1, 2), {x})", "numeric value 1")]
    [InlineData("filter((0, 1), {x})", "numeric value 0")]
    [InlineData("filter((1, 2), {x, x})", "a sequence value with 2 sequence elements: (1, 1)")]
    [InlineData("filter((1, 2), {x.string})", "a string: '1'")]
    [InlineData("filter((1, 2), {[x > 0]})", "a list value with 1 element: [true]")]
    [InlineData("filter((1, 2), {if(x > 0, (), ())})", "a sequence value with 0 sequence elements: ()")]
    public void Filter_RejectsANonBooleanPredicateResult_NamingTheValue(string source, string described)
    {
        AssertEvalFailsWithTypeMismatch(source, $"filter predicate result must be a Boolean value (true or false), but was {described}");
        var error = FailureOf(source);
        Assert.Equal(["while evaluating call to filter"], LoopDiagnosticParityAssertions.ContextChain(error));
        Assert.Equal(KatLangErrorCode.TypeMismatch, EngineFailure(source).Code);
    }

    [Fact]
    public void Filter_NeverInvokesThePredicate_OverAnEmptySource()
        => Assert.Equal("[]", Display("filter((), {x})"));

    [Theory]
    [InlineData("contains((1, 2), 2)", true)]
    [InlineData("(1, 2).contains(3)", false)]
    [InlineData("contains((true, 1), true)", true)]
    [InlineData("contains((1, 2), true)", false)]
    [InlineData("contains([false], false)", true)]
    [InlineData("contains((), 1)", false)]
    [InlineData("contains((1, true), 1)", true)]
    [InlineData("contains(((true, 1), 2), (true, 1))", true)]
    public void Contains_ProducesABoolean(string source, bool expected)
        => AssertEvalBool(source, expected);

    // ── Booleans inside sequences, lists, bindings, and collection builtins ──

    [Fact]
    public void Booleans_ParticipateInSequencesListsAndBindings_WithoutSpecialRules()
    {
        AssertEvalBool("x, y = true, 1\nx", true);
        AssertEval("x, y = true, 1\ny", 1);
        Assert.Equal("[true, false]", Display("*all = true, false\nall"));
        AssertEval("count((true, false))", 2);
        AssertEval("count([true])", 1);
        Assert.Equal("[true, false]", Display("distinct((true, true, false))"));
        Assert.Equal("[true, false]", Display("take((true, false, true), 2)"));
        AssertEvalResults("(true, (false, 1)):1", new Result.Bool(false), new Result.Atom(1));
        AssertEvalBool("[true, 1]:0", true);
        AssertEvalBool("A = (true, 2)\nB = { A* }\nB:0", true);
        Assert.Equal("[true, 3]", Display("F(*items) = items\nF(true, 3)"));
        AssertEvalBool("F((x, y)) = x and y == 2\nF((true, 2))", true);
        // `atoms` collects numbers only: a Boolean is not an atom.
        Assert.Equal("[1]", Display("atoms((true, 1))"));
        Assert.Equal("[]", Display("atoms(true)"));
    }

    [Fact]
    public void Booleans_FlowThroughCallbacks_AndHigherOrderAlgorithms()
    {
        Assert.Equal("[false, true, true]", Display("map((1, 2, 3), {x > 1})"));
        AssertEvalBool("Apply(f, v) = f(v)\nApply({x > 1}, 2)", true);
        AssertEvalBool("Negate(f, v) = not f(v)\nNegate({x > 1}, 2)", false);
        AssertEvalBool("All(e, acc) = e and acc\nreduce((true, false, true), All, true)", false);
        AssertEvalBool("Any(e, acc) = e or acc\nreduce((false, true), Any, false)", true);
        AssertEvalBool("Both(p, q, v) = p(v) and q(v)\nBoth({x > 1}, {x < 5}, 3)", true);
        AssertEval("IsSmall(v) = v < 3\nStep(x) = x + 1, IsSmall(x)\nStep.while(0)", 3);
    }

    [Fact]
    public void BooleanProperties_AreCachedLikeAnyOtherValue()
    {
        AssertEvalBools("Flag = 1 < 2\nFlag, Flag, Flag == Flag", true, true, true);
        AssertEval("Limit = 5 > 2\nStep = x + 1, Limit and x < 3\nStep.while(0)", 3);
        var cache = new RunScopedZeroArgPropertyResultCache();
        var result = Evaluator.Run(Program("Flag = 1 < 2\nFlag, Flag, not Flag"), cache);
        Assert.False(result.IsError);
        Assert.Equal(
            Result.FromItems([new Result.Bool(true), new Result.Bool(true), new Result.Bool(false)]),
            result.Value,
            Result.ValueComparer);
        Assert.Equal(1, cache.GetSnapshot().Stores);
    }

    // ── Loops: optimized and generic strategies agree ──────────────────────

    [Fact]
    public void Loops_AgreeAcrossStrategies_WithBooleanStateAndFlags()
    {
        AssertEvalLoopModes("Step = x + 1, x < 10\nStep.while(0)", 10);
        AssertEvalResultLoopModes("Toggle(b) = not b\nToggle.repeat(3, false)", new Result.Bool(true));
        AssertEvalResultLoopModes(
            "Step(a, b) = a + 1, not b, a < 3\nStep.while(0, true)",
            Result.FromItems([new Result.Atom(3), new Result.Bool(false)]));
        AssertEvalLoopModes("Outer(flag) = { Step = x + if(flag, 1, 2)\n Step.repeat(3, 0) }\nOuter(true)", 3);
        AssertEvalLoopModes("Outer(flag) = { Step = x + if(flag, 1, 2)\n Step.repeat(3, 0) }\nOuter(false)", 6);
        AssertEvalLoopModes("Step = x + 1, (x mod 2 == 0) or x < 5\nStep.while(0)", 5);
        AssertEvalResultLoopModes("Step(x) = x + 1, x < 2\nStep.while(0) == 2", new Result.Bool(true));
    }

    [Theory]
    [InlineData("Step = x + 1, x\nStep.while(0)", "numeric value 0")]
    [InlineData("Step = x, 1\nStep.while(5)", "numeric value 1")]
    [InlineData("Step = x + 1, 'go'\nStep.while(0)", "a string: 'go'")]
    [InlineData("Step = x + 1, (true, true)\nStep.while(0)", "a sequence value with 2 sequence elements: (true, true)")]
    public void While_RejectsANonBooleanContinuationFlag_InBothStrategies(string source, string described)
    {
        var expected = $"while continuation flag (the step's last output) must be a Boolean value (true or false), but was {described}";
        foreach (var optimize in new[] { false, true })
        {
            var result = EvalFull(source, enableLoopOptimization: optimize);
            Assert.True(result.IsError, $"expected a failure (optimized: {optimize})");
            var innermost = Assert.IsType<EvalError.TypeMismatch>(Innermost(result.Error));
            Assert.Equal(expected, innermost.Message);
        }
    }

    // ── Async twin and the public engine surface ────────────────────────────

    [Fact]
    public async Task AsyncTwin_ProducesTheSameBooleans()
    {
        var ast = Program("A = 1 < 2\nB = not A\nA, B, if(A, 10, 20), (A, B) == (true, false)");
        var sync = Evaluator.RunCounted(ast);
        Assert.False(sync.IsError);
        var twin = await Evaluator.RunCountedAsync(ast, new PassThroughAsyncZeroArgPropertyResultCache());
        Assert.False(twin.IsError);
        Assert.Equal(sync.Value.Value, twin.Value.Value, Result.ValueComparer);
        Assert.Equal(
            Result.FromItems([new Result.Bool(true), new Result.Bool(false), new Result.Atom(10), new Result.Bool(true)]),
            twin.Value.Value,
            Result.ValueComparer);

        Assert.Equal("true", Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync("1 < 2")).ToDisplayString());
        Assert.Equal(
            KatLangErrorCode.TypeMismatch,
            Assert.Single(Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync("if(1, 1, 2)")).Errors).Code);
    }

    [Fact]
    public void Engine_RendersBooleans_AndProjectsNoAtomsForThem()
    {
        Assert.Equal("true", Display("1 < 2"));
        Assert.Equal("false\n3", Display("2 < 1\n3"));
        // The lossy atom projection is numeric only: a Boolean contributes no atom.
        Assert.Empty(KatLangEngine.EvaluateToAtoms("1 < 2"));
        Assert.Equal([(Decimal128)3], KatLangEngine.EvaluateToAtoms("(1 < 2, 3)"));
        Assert.Empty(Assert.IsType<RunResult.Success>(KatLangEngine.Run("true")).Atoms);
    }

    [Fact]
    public void Engine_ReportsBooleanTypeErrors_WithSpans()
    {
        var and = EngineFailure("1 and 2");
        Assert.Equal(KatLangErrorCode.TypeMismatch, and.Code);
        Assert.Contains("while evaluating `1 and 2`", and.Message, StringComparison.Ordinal);
        Assert.Contains("operator `and` expects Boolean operands, but the left operand was numeric value 1", and.Message, StringComparison.Ordinal);
        Assert.Equal(new SourceSpan(1, 1, 1, 8), and.Span);

        var not = EngineFailure("X = 5\nnot X");
        Assert.Equal(KatLangErrorCode.TypeMismatch, not.Code);
        Assert.Equal(new SourceSpan(2, 1, 2, 6), not.Span);

        var flag = EngineFailure("Step = x, 1\nStep.while(0)");
        Assert.Equal(KatLangErrorCode.TypeMismatch, flag.Code);
        Assert.Contains("while continuation flag (the step's last output) must be a Boolean value (true or false), but was numeric value 1", flag.Message, StringComparison.Ordinal);
    }

    // ── Value equality, hashing, and normalization ──────────────────────────

    [Fact]
    public void ValueComparer_TreatsBooleansAsTheirOwnKind()
    {
        var comparer = Result.ValueComparer;
        Assert.True(comparer.Equals(new Result.Bool(true), new Result.Bool(true)));
        Assert.False(comparer.Equals(new Result.Bool(true), new Result.Bool(false)));
        Assert.False(comparer.Equals(new Result.Bool(true), new Result.Atom(1)));
        Assert.False(comparer.Equals(new Result.Bool(false), new Result.Atom(0)));
        Assert.False(comparer.Equals(new Result.Bool(true), new Result.Str("true")));
        // The comparer is structural over canonical values: a Boolean inside a list is a
        // different value, and equal Booleans hash alike while different ones do not.
        Assert.False(comparer.Equals(new Result.Bool(true), Result.ListValue.TakeOwnership([new Result.Bool(true)])));
        Assert.Equal(comparer.GetHashCode(new Result.Bool(true)), comparer.GetHashCode(new Result.Bool(true)));
        Assert.NotEqual(comparer.GetHashCode(new Result.Bool(true)), comparer.GetHashCode(new Result.Bool(false)));
        Assert.Equal("[true, false]", Display("distinct((1 < 2, 2 < 3, false, (true)))"));
    }

    [Fact]
    public void AsBool_IsTheOneTruthView()
    {
        Assert.True(new Result.Bool(true).AsBool());
        Assert.False(new Result.Bool(false).AsBool());
        Assert.True(Result.SequenceValue.TakeOwnership([new Result.Bool(true)]).AsBool());
        Assert.Null(new Result.Atom(1).AsBool());
        Assert.Null(new Result.Atom(0).AsBool());
        Assert.Null(new Result.Str("true").AsBool());
        Assert.Null(Result.ListValue.TakeOwnership([new Result.Bool(true)]).AsBool());
        Assert.Null(Result.SequenceValue.TakeOwnership([]).AsBool());
        Assert.Null(Result.SequenceValue.TakeOwnership([new Result.Bool(true), new Result.Bool(true)]).AsBool());
        Assert.Null(new Result.Bool(true).AsNum());
    }

    // ── Regression: numeric truthiness is gone ──────────────────────────────

    [Theory]
    [InlineData("if(1, 1, 2)")]
    [InlineData("if(0, 1, 2)")]
    [InlineData("if(-1, 1, 2)")]
    [InlineData("if(Math.Sqrt(-1), 1, 2)")]
    [InlineData("if((1, 2), 1, 2)")]
    [InlineData("if(range(1, 3), 1, 2)")]
    [InlineData("1 and 1")]
    [InlineData("0 or 1")]
    [InlineData("1 xor 0")]
    [InlineData("not 0")]
    [InlineData("not 7")]
    [InlineData("filter((1, 2), {x})")]
    [InlineData("filter((1, 2), {x * 0 + 1})")]
    [InlineData("(1, 2).filter{x - x}")]
    [InlineData("Step = x, 1\nStep.while(0)")]
    [InlineData("while({x + 1, x - 2}, 0)")]
    [InlineData("Step = x - 1, x - 1\nStep.while(3)")]
    public void ProgramsThatReliedOnNumericTruth_NowFailWithATypeMismatch(string source)
    {
        var error = FailureOf(source);
        Assert.IsType<EvalError.TypeMismatch>(Innermost(error));
        Assert.Equal(KatLangErrorCode.TypeMismatch, EngineFailure(source).Code);
    }
}
