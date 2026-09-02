using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorExpressionListTests
{
    // â”€â”€ Output lists â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_CommaList_ReturnsMultipleValues()
        => AssertEval("1, 2, 3", 1, 2, 3);

    [Fact]
    public void Eval_CommaListWithExpressions()
        => AssertEval("1 + 1, 2 * 2, 3 - 1", 2, 4, 2);

    [Fact]
    public void Eval_CommaWithSequenceValueRowPreservesStructure()
    {
        AssertEval("1, (2, 3)", 1, 2, 3);
        AssertEvalCounted("1, (2, 3)", 2, Result.FromItems([Atom(1), SequenceValue(Atom(2), Atom(3))]));
    }

    [Fact]
    public void Eval_NewlineSequenceConstructAfterCommaPreservesStructure()
    {
        AssertEval(
            """
            1, 2
            3
            """,
            1,
            2,
            3);
        AssertEvalCounted(
            """
            1, 2
            3
            """,
            3,
            Result.FromItems([Atom(1), Atom(2), Atom(3)]));
    }

    [Fact]
    public void Eval_CommaPackagesMultiOutputPropertyBoundary()
    {
        AssertEval(
            """
            A = 1, 2
            A, 3
            """,
            1,
            2,
            3);
        AssertEvalCounted(
            """
            A = 1, 2
            A, 3
            """,
            2,
            Result.FromItems([SequenceValue(Atom(1), Atom(2)), Atom(3)]));
    }

    [Fact]
    public void Eval_ArithmeticCommaNewlinePreservesCommaAndSequenceStructure()
    {
        AssertEval(
            """
            1 + 2, 2 + 3
            3 + 4
            """,
            3,
            5,
            7);
        AssertEvalCounted(
            """
            1 + 2, 2 + 3
            3 + 4
            """,
            3,
            Result.FromItems([Atom(3), Atom(5), Atom(7)]));
    }

    [Fact]
    public void Eval_CommaPreservesExplicitSequenceValueItem()
        => AssertEvalCounted(
            "(1, 2), 3",
            2,
            Result.FromItems([SequenceValue(Atom(1), Atom(2)), Atom(3)]));

    [Fact]
    public void Eval_ExplicitSequenceValueTripleEmitsOneSequenceValue()
        => AssertEvalCounted(
            "(1, 2, 3)",
            1,
            SequenceValue(Atom(1), Atom(2), Atom(3)));

    // ── Implicit expression-list separator by adjacency ─────────────────────

    [Fact]
    public void Eval_SameLineAdjacency_ConstructsExpressionList()
    {
        AssertEval("1 2", 1, 2);
        AssertEvalCounted("1 2", 2, ResultFromAtoms(1, 2));
    }

    [Theory]
    [InlineData("1 2 3")]
    [InlineData("1\n2\n3")]
    public void Eval_AdjacencyNewline_ConstructExpressionList(string source)
        => AssertEvalCounted(source, 3, ResultFromAtoms(1, 2, 3));

    [Fact]
    public void Eval_ParenthesizedCommaChain_ConstructsSequenceValue()
        => AssertEvalCounted("(1, 2, 3)", 1, ResultFromAtoms(1, 2, 3));

    [Theory]
    [InlineData("1, 2 3")]
    [InlineData("1, (2, 3)")]
    public void Eval_AdjacencyAfterComma_UsesExpressionListStructure(string source)
    {
        if (source.Contains("(2, 3)", StringComparison.Ordinal))
            AssertEvalCounted(source, 2, Result.FromItems([Atom(1), SequenceValue(Atom(2), Atom(3))]));
        else
            AssertEvalCounted(source, 3, ResultFromAtoms(1, 2, 3));
    }

    [Theory]
    [InlineData("(1 2)")]
    [InlineData("((1, 2))")]
    [InlineData("(1\n2)")]
    public void Eval_ParenthesizedAdjacency_EmitsOneSequenceValue(string source)
        => AssertEvalCounted(source, 1, SequenceValue(Atom(1), Atom(2)));

    [Theory]
    [InlineData("(1 2 3)")]
    [InlineData("(1\n2\n3)")]
    [InlineData("((1, 2, 3))")]
    public void Eval_ParenthesizedAdjacencyTriple_EmitsOneSequenceValue(string source)
        => AssertEvalCounted(source, 1, SequenceValue(Atom(1), Atom(2), Atom(3)));

    [Theory]
    [InlineData("X(*values) = values.count\nX(1 2)")]
    [InlineData("X(*values) = values.count\nX (1 2)")]
    public void Eval_CallArgumentAdjacency_BindsAsItemSupply(string source)
        // X(*values) collects the supplied argument slots. The adjacency form `1 2`
        // supplies two slots, so the collecting parameter captures two supplied arguments.
        => AssertEval(source, 2);

    [Theory]
    [InlineData("X(*values) = values.count\nX((1, 2))")]
    [InlineData("X(*values) = values.count\nX ((1, 2))")]
    public void Eval_CallArgumentGroupedSequence_SingleVariadicCollectsOneArgument(string source)
        // The call supplies one sequence-valued argument, and the collecting parameter
        // collects the supplied slots as one exact list: [(1, 2)], count 1.
        => AssertEval(source, 1);

    [Fact]
    public void Eval_SingleVariadicWithCollectionOperation_GroupedArgumentIsOneElement()
    {
        // F((1, 2)) supplies one argument: the sequence value (1, 2). The collecting
        // parameter collects it as the one-element list [(1, 2)], so x.sum hits the
        // per-element numeric constraint and fails. Only explicit spread opens the
        // call boundary: F((1, 2)*) supplies two arguments and sums to 3.
        AssertEvalFails(
            """
            F(*x) = x.sum
            F((1, 2))
            """);

        AssertEval(
            """
            F(*x) = x.sum
            F((1, 2)*)
            """,
            3);
    }

    [Fact]
    public void Eval_FixedCall_InlineSequenceValueArgumentRequiresExplicitSpread()
    {
        AssertEvalFailsWithArityMismatch(
            """
            Add(x, y) = x + y
            Add((1, 2))
            """,
            expected: 2,
            actual: 1);

        AssertEval(
            """
            Add(x, y) = x + y
            Add((1, 2)*)
            """,
            3);
    }

    [Fact]
    public void Eval_MixedVariadicCall_PlainSequenceArgumentPreservesBoundary()
    {
        AssertEval(
            """
            A = 1, 2
            G(first, *rest) = first.count, rest.count
            G(A)
            """,
            2, 0);

        AssertEval(
            """
            G(first, *rest) = first.count, rest.count
            G((1, 2))
            """,
            2, 0);
    }

    [Fact]
    public void Eval_MixedVariadicCall_ExplicitSpreadOpensSequenceArgument()
    {
        AssertEval(
            """
            A = 1, 2
            G(first, *rest) = first.count, rest.count
            G(A*)
            """,
            1, 1);

        AssertEval(
            """
            G(first, *rest) = first.count, rest.count
            G((1, 2)*)
            """,
            1, 1);
    }

    [Theory]
    [InlineData("Add(a, b) = a + b\nAdd(1 2)")]
    [InlineData("Add(a, b) = a + b\nAdd (1 2)")]
    [InlineData("Add(a, b) = a + b\nAdd((1, 2))")]
    [InlineData("Add(a, b) = a + b\nAdd ((1, 2))")]
    public void Eval_CallArgumentAdjacency_IsImplicitComma(string source)
    {
        if (source.Contains("((1, 2))", StringComparison.Ordinal))
            AssertEvalFailsWithArityMismatch(source, expected: 2, actual: 1);
        else
            AssertEval(source, 3);
    }

    [Theory]
    [InlineData("Add(a, b) = a + b\nAdd(1, 2)")]
    [InlineData("Add(a, b) = a + b\nAdd (1, 2)")]
    public void Eval_CallArgumentComma_RemainsTwoArguments(string source)
        => AssertEval(source, 3);

    // ── Whitespace and newlines before call delimiters ───────────────────────

    [Theory]
    [InlineData("Add = a + b\n2.Add(6)")]
    [InlineData("Add = a + b\n2.Add (6)")]
    public void Eval_DotCallWhitespaceBeforeParen_IsCallContinuation(string source)
        => AssertEval(source, 8);

    [Theory]
    [InlineData("(1, 2, 3).map{n * 2}")]
    [InlineData("(1, 2, 3).map { n * 2 }")]
    public void Eval_CallbackBraceWhitespace_IsCallContinuation(string source)
        => AssertEval(source, 2, 4, 6);

    [Theory]
    [InlineData("Twice(f) = f(1) + f(1)\nTwice{n + 1}")]
    [InlineData("Twice(f) = f(1) + f(1)\nTwice {n + 1}")]
    public void Eval_DirectBraceCallWhitespace_IsCallContinuation(string source)
        => AssertEval(source, 4);

    [Fact]
    public void Eval_ExplicitSeparatorBeforeParen_StillWinsOverCallContinuation()
    {
        // Same-line whitespace before '(' continues the call, so a
        // zero-parameter property called with arguments fails with arity.
        AssertEvalFailsWithArityMismatch("A = 5\nA (1, 2)", expected: 0, actual: 2);

        // A physical newline never continues a closed expression into a
        // call: `A` newline `(1, 2)` becomes two expression-list slots.
        AssertEvalCounted(
            "A = 5\nA\n(1, 2)",
            2,
            Result.FromItems([Atom(5), SequenceValue(Atom(1), Atom(2))]));

        // Comma also keeps the values as separate expression-list slots.
        AssertEvalCounted(
            "A = 5\nA, (1, 2)",
            2,
            Result.FromItems([Atom(5), SequenceValue(Atom(1), Atom(2))]));
    }

    [Theory]
    [InlineData("Add(a, b) = a + b\nAdd\n(1, 2)")]
    public void Eval_NewlineBeforeCallDelimiter_IsExpressionListNotCall(string source)
    {
        // Not the call Add(1, 2): the bare `Add` row fails to resolve its
        // implicit parameters.
        var result = EvalFull(source);
        Assert.True(result.IsError, $"Expected the joined form to fail but got: {(result.IsOk ? result.Value : null)}");
        Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
    }

    [Fact]
    public void Eval_OpenedCallDelimiterSpansLines_RemainsCall()
        => AssertEval("Add(a, b) = a + b\nAdd(\n1, 2\n)", 3);

    [Fact]
    public void Eval_OpenedBraceCallbackSpansLines_RemainsCall()
        => AssertEval("(1, 2, 3).map{\nn * 2\n}", 2, 4, 6);

    [Fact]
    public void Eval_LeadingDotOnNextLine_ContinuesDotCallChain()
        // The newline call boundary is about '(' and '{' only: a '.'-led
        // line still continues the dot-call chain, so method-chain layout
        // keeps working as long as each delimiter follows its member name on
        // the same line.
        => AssertEval("(1, 2, 3)\n.map { n * 2 }\n.sum", 12);

    [Theory]
    [InlineData("Pair = 1, 2\nP = Pair:0\nP")]
    [InlineData("Pair = 1, 2\nP = Pair : 0\nP")]
    public void Eval_SameLineIndexing_SelectsIndexedItem(string source)
        // Same-line whitespace around ':' is insignificant; postfix indexing
        // continues the expression before it.
        => AssertEval(source, 1);

    [Fact]
    public void Eval_ParenLedLineAfterDefinitionBody_DoesNotCreateRecursivePropertyCall()
    {
        // Regression: `A = Identity` newline `(A)` once parsed as
        // `A = Identity(A)`, so evaluating A recursed through itself. The
        // newline ends the body; evaluation terminates with the ordinary
        // unresolved-implicit-parameter error for the bare `Identity` body.
        var result = EvalFull("Identity = x\n\nA = Identity\n(A)\n\nA");

        Assert.True(result.IsError, $"Expected unresolved-parameter failure but got: {(result.IsOk ? result.Value : null)}");
        Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
    }

    [Theory]
    [InlineData("X(*values) = values.count\nX(1, 2 3)")]
    [InlineData("X(*values) = values.count\nX(1, (2, 3))")]
    public void Eval_CallArgumentMixedCommaAndAdjacency_BindsItemSupply(string source)
    {
        // X(*values) collects the argument slots. `1, 2 3` is three slots
        // (count 3); `1, (2, 3)` is two slots, the second a grouped value
        // preserved as a sibling (count 2).
        if (source.Contains("(2, 3)", StringComparison.Ordinal))
            AssertEval(source, 2);
        else
            AssertEval(source, 3);
    }

    [Theory]
    [InlineData("A B*")]
    [InlineData("A\nB*")]
    public void Eval_AdjacencyBeforePostfixSequenceSpread_CreatesExpressionListSlots(string source)
    {
        var program = "A = 1\nB = 2, 3\n" + source;
        AssertEvalCounted(program, 3, ResultFromAtoms(1, 2, 3));
    }

    [Theory]
    [InlineData("X(a b*)")]
    [InlineData("X(a\nb*)")]
    public void Eval_CallArgumentAdjacencyBeforePostfixSequenceSpread_BindsItemSupply(string source)
    {
        // `a b*` is three slots (1, 2, 3); X(*values) collects them as separate arguments.
        var program = "a = 1\nb = 2, 3\nX(*values) = values.count\n" + source;
        AssertEval(program, 3);
    }

    [Theory]
    [InlineData("X((a, b*))")]
    [InlineData("X((a\nb*))")]
    public void Eval_SequenceValuePostfixSequenceSpreadInCall_BindsAsOneSequenceValueArgument(string source)
    {
        // Explicit parentheses materialize the spread items into one argument,
        // which the collecting parameter collects as the one-element list [(1, 2, 3)].
        var program = "a = 1\nb = 2, 3\nX(*values) = values.count\n" + source;
        AssertEval(program, 1);
    }

    [Theory]
    [InlineData("A B*, C")]
    [InlineData("A\nB*\nC")]
    public void Eval_MiddlePostfixSequenceSpread_CreatesExpressionListSlots(string source)
    {
        var program = "A = 1\nB = 2, 3\nC = 4\n" + source;
        AssertEvalCounted(program, 4, ResultFromAtoms(1, 2, 3, 4));
    }

    [Theory]
    [InlineData("A, B C*")]
    [InlineData("A, B\nC*")]
    public void Eval_CommaContributionBeforeJoinedPostfixSequenceSpread_PreservesCommaStructure(string source)
    {
        var program = "A = 1, 2\nB = 3\nC = 4\n" + source;
        AssertEvalCounted(program, 3, Result.FromItems([SequenceValue(Atom(1), Atom(2)), Atom(3), Atom(4)]));
    }

    [Theory]
    [InlineData("F(a, b, c) = a + b + c\nF(1 2, 3*)")]
    [InlineData("F(a, b, c) = a + b + c\nF(1\n2, 3*)")]
    [InlineData("F(a, b, c) = a + b + c\nF(1, (2, 3)*)")]
    public void Eval_MixedCommaAndJoinWithSpreadSlot_SpreadAppliesOnlyToItsOperand(string source)
        => AssertEval(source, 6);

    [Fact]
    public void Eval_DefinitionSeparatedCommaSlotSpreadContribution_PreservesCommaStructure()
    {
        var program = "A = 1\nB = 2\nC = 3\n\nA\nP = 9\nB, C*";
        AssertEvalCounted(program, 3, ResultFromAtoms(1, 2, 3));
    }

    /// <summary>
    /// Track 13: these four sources put a property declaration (<c>P = 9</c>)
    /// inside a call's parentheses. The delimiter model made that a PARSER
    /// error ("A property declaration is not allowed inside parentheses"), so
    /// the argument-grouping behavior they were written to describe is no
    /// longer expressible. They kept passing only because the evaluator helper
    /// ignored parser diagnostics and ran the recovery tree.
    ///
    /// <para>
    /// The grouping semantics itself is still covered at ROOT, where a
    /// definition row between slots IS legal — see
    /// <see cref="Eval_DefinitionSeparatedCommaSlotSpreadContribution_PreservesCommaStructure"/>.
    /// What remains true for the parenthesized spelling is the rejection, so
    /// that is what these now assert.
    /// </para>
    /// </summary>
    [Theory]
    [InlineData("F(a, b, c) = a + b + c\nA = 1\nB = 2\nC = 3\n\nF(\nA\nP = 9\nB, C*\n)")]
    [InlineData("F(a, b, c) = a + b + c\nA = 1\nB = 2\nC = 3\nF(\nA*, B\nP = 9\nC\n)")]
    [InlineData("F(a, b) = a + b\nA = 1\nC = 2\nF(\nA*, ()\nP = 9\nC\n)")]
    [InlineData("F(a, b) = a + b\nA = 1\nC = 2\nF(\nA*\nP = 9\nC\n)")]
    public void Eval_DefinitionInsideCallParentheses_IsRejectedByTheParser(string source)
    {
        var diagnostics = SourceProvenance.ExpectFrontEndError(source);
        Assert.Contains(
            diagnostics,
            d => d.Message.Contains("property declaration is not allowed inside parentheses", StringComparison.Ordinal));
    }

    [Fact]
    public void Eval_ParenthesizedSequenceValueRow_EmitsOneSequenceValueOutput()
        => AssertEvalCounted("(1, 3)", 1, ResultFromAtoms(1, 3));

    [Theory]
    [InlineData("A = 10\nA\n-1")]
    [InlineData("A = 10\nA # comment\n-1")]
    public void Eval_CommentDoesNotEnableBinaryContinuationAcrossNewline(string source)
        // Comments are semantically invisible for line boundaries: both
        // forms are the two output rows 10 and -1, never the subtraction 9.
        => AssertEvalCounted(source, 2, ResultFromAtoms(10, -1));

    // The three `PostfixSpreadThen...InCall` tests that lived here asserted
    // argument grouping around a `P = 9` declaration written INSIDE a call's
    // parentheses. The delimiter model made that spelling a parser error, so
    // their sources became illegal and they only kept passing because the
    // evaluator helper ignored parser diagnostics (Track 13). Their sources are
    // preserved as rejection cases in
    // Eval_DefinitionInsideCallParentheses_IsRejectedByTheParser, and the
    // grouping semantics itself remains covered at root by
    // Eval_DefinitionSeparatedCommaSlotSpreadContribution_PreservesCommaStructure.

    [Theory]
    [InlineData("P\n= 1\nP")]
    [InlineData("P # comment\n= 1\nP")]
    public void Eval_CommentBeforeEqualsLine_DefinesPropertyIdentically(string source)
        => AssertEval(source, 1);

    [Fact]
    public void Eval_AdjacencyNeverSplitsTokens()
    {
        AssertEval("ab = 7\nab", 7);
        AssertEval("12", 12);
    }

    [Theory]
    [InlineData("2(3)")]
    [InlineData("2 (3)")]
    [InlineData("2\n(3)")]
    public void Eval_NumberBeforeParenthesizedExpression_IsAdjacencyNotMultiplication(string source)
        => AssertEvalCounted(source, 2, ResultFromAtoms(2, 3));
}
