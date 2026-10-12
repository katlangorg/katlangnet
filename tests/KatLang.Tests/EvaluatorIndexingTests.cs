using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

public class EvaluatorIndexingTests
{
    private static void AssertNestedSequenceValueAtoms(Result value, params Decimal128[][] expectedGroups)
    {
        var outer = Assert.IsType<Result.SequenceValue>(value);
        Assert.Equal(expectedGroups.Length, outer.Items.Count);

        for (var groupIndex = 0; groupIndex < expectedGroups.Length; groupIndex++)
        {
            var group = Assert.IsType<Result.SequenceValue>(outer.Items[groupIndex]);
            var expected = expectedGroups[groupIndex];
            Assert.Equal(expected.Length, group.Items.Count);

            for (var itemIndex = 0; itemIndex < expected.Length; itemIndex++)
                Assert.Equal(expected[itemIndex], Assert.IsType<Result.Atom>(group.Items[itemIndex]).Value);
        }
    }

    // â”€â”€ Indexing â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Index_ReturnsElement()
        => AssertEval("(1, 2, 3)[1]", 2);

    [Fact]
    public void Eval_Index_FirstElement()
        => AssertEval("(1, 2, 3)[0]", 1);

    [Fact]
    public void Eval_Index_NamedAtomicSelection_ReturnsAtom()
        => AssertEval(
            """
            A = 7, 8
            A[0]
            """,
            7);

    [Fact]
    public void Eval_Index_LastElement()
        => AssertEval("(1, 2, 3)[2]", 3);

    [Fact]
    public void Eval_Index_OutOfBounds_Fails()
        => AssertEvalFails("(1, 2, 3)[5]");

    [Fact]
    public void Eval_Index_NegativeIndex_Fails()
    {
        var source = """
            X = 1, 2, 3
            i = 0 - 1
            X[i]
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_Index_SingleAtom()
        => AssertEval("5[0]", 5);

    [Fact]
    public void Eval_Index_ChainedIndex()
        => AssertEval("((1, 2), (3, 4))[1][0]", 3);

    [Fact]
    public void Eval_Index_SequenceValueSelection_ReturnsStoredValue()
    {
        var result = EvalFull(
            """
            A = (1, 2), (3, 4)
            A[0]
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertSequenceValueAtoms(result.Value, 1, 2);
    }

    [Fact]
    public void Eval_Index_SequenceValueSelection_CountAndDotCallCountAgree()
        => AssertEval(
            """
            A = (1, 2), (3, 4)
            count(A[0])
            (A[0]).count
            """,
            2,
            2);

    [Fact]
    public void Eval_Index_NestedSequenceValueSelection_PreservesNestedValue()
    {
        var result = EvalFull(
            """
            A = ((1, 2), (3, 4)), ((5, 6), (7, 8))
            A[0]
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertNestedSequenceValueAtoms(result.Value, [1m, 2m], [3m, 4m]);
    }

    [Fact]
    public void Eval_Index_NestedSequenceValueSelection_CountOpensTheSelectedValue()
        => AssertEval(
            """
            A = ((1, 2), (3, 4)), ((5, 6), (7, 8))
            count(A[0])
            count(A[0][1])
            """,
            2,
            2);

    [Fact]
    public void Eval_Index_ChainedSequenceValueSelection_SelectsEachStep()
    {
        var result = EvalFull(
            """
            A = ((1, 2), (3, 4)), ((5, 6), (7, 8))
            A[0][1]
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertSequenceValueAtoms(result.Value, 3, 4);
    }

    private static EvalError.BadIndex AssertEvalFailsWithBadIndex(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected BadIndex error but got: {result.Value}");

        return Assert.IsType<EvalError.BadIndex>(Innermost(result.Error));
    }

    // Index validation is one shared selector path, so every selector kind
    // accepted or rejected for a sequence target behaves identically for an
    // exact list target.

    [Theory]
    [InlineData("()[0]")]
    [InlineData("[][0]")]
    [InlineData("(1, 2)[2]")]
    [InlineData("[1, 2][2]")]
    [InlineData("[1, 2][100]")]
    [InlineData("A = []\nA[0]")]
    public void Eval_Index_EmptyOrOutOfRangeTarget_FailsWithBadIndex(string source)
        => AssertEvalFailsWithBadIndex(source);

    [Theory]
    [InlineData("X = 1, 2, 3\ni = 0 - 1\nX[i]")]
    [InlineData("X = [1, 2, 3]\ni = 0 - 1\nX[i]")]
    [InlineData("(1, 2, 3)[1.5]")]
    [InlineData("[1, 2, 3][1.5]")]
    public void Eval_Index_NegativeOrNonIntegralSelector_FailsWithBadIndex(string source)
        => AssertEvalFailsWithBadIndex(source);

    [Theory]
    [InlineData("(1, 2, 3)[3000000000]")]
    [InlineData("[1, 2, 3][3000000000]")]
    public void Eval_Index_SelectorBeyondIntRange_FailsWithBadIndex(string source)
        // C#-only guard for the host int cast; Lean's unbounded integer
        // selector reaches the same out-of-range badIndex through select?.
        => AssertEvalFailsWithBadIndex(source);

    [Theory]
    [InlineData("(1, 2, 3)['1']")]
    [InlineData("[1, 2, 3]['1']")]
    public void Eval_Index_StringSelector_FailsWithTypeMismatch(string source)
        => AssertEvalFailsWithTypeMismatch(source, "Expected a number, got a string");

    [Theory]
    [InlineData("(1, 2, 3)[(0, 1)]")]
    [InlineData("[1, 2, 3][(0, 1)]")]
    [InlineData("(1, 2, 3)[[0]]")]
    [InlineData("[1, 2, 3][[0]]")]
    [InlineData("(1, 2, 3)[()]")]
    [InlineData("[1, 2, 3][()]")]
    public void Eval_Index_NonNumericStructuredSelector_FailsWithTypeMismatch(string source)
    {
        // A structured selector is a present value of the wrong KIND (Q-27), exactly like a
        // string or Boolean selector — never an arity error.
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected TypeMismatch error but got: {result.Value}");

        var mismatch = Assert.IsType<EvalError.TypeMismatch>(Innermost(result.Error));
        Assert.StartsWith("Expected a number, got a ", mismatch.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("(1, 2, 3)[1 div 0]")]
    [InlineData("[1, 2, 3][1 div 0]")]
    public void Eval_Index_FailedSelectorExpression_PropagatesError(string source)
        => AssertEvalFails(source);

    [Fact]
    public void Eval_Index_OutOfRangeError_SpanAgreesAcrossTargetKinds()
    {
        // `(1, 2)[9]` and `[1, 2][9]` occupy the same source columns, so the
        // out-of-range projection error must carry the identical span.
        var sequenceError = AssertEvalFailsWithBadIndex("(1, 2)[9]");
        var listError = AssertEvalFailsWithBadIndex("[1, 2][9]");

        Assert.NotNull(sequenceError.Span);
        Assert.NotNull(listError.Span);
        Assert.Equal(sequenceError.Span, listError.Span);
        Assert.Equal("Bad index", KatLangError.FromEvalError(listError).Message);
    }

    // ── Index diagnostics: source-faithful names and selector-error spans ────

    /// <summary>
    /// Diagnostic expression names use KatLang source syntax, so a selection must
    /// render as postfix brackets `target[selector]` (October 2026). The retired
    /// colon spelling would be actively misleading — `:` is not KatLang syntax —
    /// so <paramref name="forbiddenColonName"/>, the former rendering of this
    /// selection, must never appear.
    /// </summary>
    /// <summary>
    /// The receiver-rendering probe: <paramref name="definitions"/> plus the
    /// dot edge under test, wrapped by <see cref="ClosedMemberProbe"/>. An
    /// index result is a value with no members, so the edge's fallback name is
    /// certain and the closed list checks it statically (Q-75 F-A): the front
    /// end renders the receiver in that diagnostic, and the runtime miss —
    /// reachable only from a host-built tree — renders it through the same
    /// <c>ExprNameRenderer.RenderDotReceiver</c>. Both must be source-faithful.
    /// </summary>
    private static void AssertIndexDiagnosticName(
        string definitions, string expression, string expectedName, string forbiddenColonName)
    {
        var source = ClosedMemberProbe(definitions, expression);
        var diagnostic = AssertCertainFallbackNameUndeclared(source, "Missing", expectedName);
        Assert.DoesNotContain(forbiddenColonName, diagnostic.Message);

        var result = EvalHostBuilt(source);
        if (result.IsOk)
            Assert.Fail($"Expected a diagnostic but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains($"`{expectedName}`", formatted);
        Assert.DoesNotContain(forbiddenColonName, formatted);
    }

    [Theory]
    // The renderer is syntax-based, so a sequence target and a list target
    // render identically.
    [InlineData("Rows = [[1, 2]]\n")]
    [InlineData("Rows = [[1, 2], [3, 4]]\n")]
    [InlineData("Rows = ((1, 2), (3, 4))\n")]
    public void Eval_Index_DiagnosticName_RendersSourceFaithfulBracketSyntax(string definitions)
        => AssertIndexDiagnosticName(definitions, "Rows[0].Missing", "Rows[0]", "Rows:0");

    [Fact]
    public void Eval_Index_ChainedDiagnosticName_RendersEachSelector()
        => AssertIndexDiagnosticName(
            "Rows = [[[1]]]\n", "Rows[0][0].Missing", "Rows[0][0]", "Rows:0:0");

    [Fact]
    public void Eval_Index_DiagnosticName_RendersEverySelectorSlot()
    {
        // Several selectors, none, and a spread slot render as the written list.
        AssertIndexDiagnosticName(
            "Rows = ((1, 2), (3, 4))\n", "Rows[1, 0, 1].Missing", "Rows[1, 0, 1]", "Rows:1");
        AssertIndexDiagnosticName(
            "Rows = ((1, 2), (3, 4))\nIs = [0]\n", "Rows[Is*].Missing", "Rows[Is*]", "Rows:");
    }

    [Fact]
    public void Eval_Index_DiagnosticName_ParenthesizesOperandsThatWouldRebind()
    {
        // Selection binds tighter than every binary operator, so a bare
        // `Rows + Rows[0]` would read as `Rows + (Rows[0])`.
        AssertIndexDiagnosticName(
            "Rows = (1, 2)\n",
            "(Rows + Rows)[0].Missing",
            "(Rows + Rows)[0]",
            "(Rows + Rows):0");

        // A selector sits inside the brackets' expression list; in this base
        // (Open) spelling a binary renders self-parenthesized, exactly as a
        // list element does.
        AssertIndexDiagnosticName(
            "Rows = ((1, 2), (3, 4))\ni = 0\n",
            "Rows[i + 1].Missing",
            "Rows[(i + 1)]",
            "Rows:(i + 1)");

        // Established call abbreviation is preserved on a selection receiver.
        AssertIndexDiagnosticName(
            "", "take([1, 2, 3], 1)[0].Missing", "take(...)[0]", "take(...):0");

        // A list-literal selector renders as the list it is (one list value —
        // the selection itself fails at run time with a kind mismatch).
        AssertIndexDiagnosticName(
            "Rows = ((1, 2), (3, 4))\n", "Rows[[0]].Missing", "Rows[[0]]", "Rows:[0]");
    }

    [Fact]
    public void Eval_Spread_DiagnosticName_ParenthesizesOperandsThatWouldRebind()
    {
        Assert.Equal(
            "(-A)*",
            Evaluator.OpenExprName(
                new Expr.SequenceSpread(
                    new Expr.Unary(UnaryOp.Minus, new Expr.Resolve("A")))));
        Assert.Equal(
            "(A + B)*",
            Evaluator.OpenExprName(
                new Expr.SequenceSpread(
                    new Expr.Binary(
                        BinaryOp.Add,
                        new Expr.Resolve("A"),
                        new Expr.Resolve("B")))));
        Assert.Equal(
            "A**",
            Evaluator.OpenExprName(
                new Expr.SequenceSpread(
                    new Expr.SequenceSpread(new Expr.Resolve("A")))));
    }

    /// <summary>
    /// The Index case of EvalExpressionSpineCounted owns the index-expression span, so plain and
    /// counted evaluation must report the identical error kind and span.
    /// </summary>
    private static void AssertIndexErrorAgreesAcrossEvaluators(string source)
    {
        var ast = ParseValidRoot(source);
        var plain = Evaluator.Run(new Expr.AlgorithmExpr(ast));
        var counted = Evaluator.RunCounted(new Expr.AlgorithmExpr(ast));

        if (plain.IsOk || counted.IsOk)
            Assert.Fail($"Expected both evaluators to fail for: {source}");

        Assert.NotNull(plain.Error.Span);
        Assert.Equal(plain.Error.Span, counted.Error.Span);
        Assert.Equal(Innermost(plain.Error).GetType(), Innermost(counted.Error).GetType());
        Assert.Equal(
            KatLangError.FromEvalError(plain.Error).Message,
            KatLangError.FromEvalError(counted.Error).Message);
    }

    [Theory]
    // Sequence/list twins: the span must not depend on the target kind.
    [InlineData("(1, 2)['x']")]
    [InlineData("[1, 2]['x']")]
    [InlineData("(1, 2)[(0, 1)]")]
    [InlineData("[1, 2][(0, 1)]")]
    [InlineData("(1, 2)[()]")]
    [InlineData("[1, 2][()]")]
    [InlineData("(1, 2)[1 div 0]")]
    [InlineData("[1, 2][1 div 0]")]
    [InlineData("(1, 2)[1.5]")]
    [InlineData("[1, 2][1.5]")]
    [InlineData("(1, 2)[3000000000]")]
    [InlineData("[1, 2][3000000000]")]
    [InlineData("(1, 2)[2]")]
    [InlineData("[1, 2][2]")]
    // Nested projection, and an index reached through the plain evaluator as a
    // binary operand.
    [InlineData("[[1, 2]][5][0]")]
    [InlineData("[[1, 2]][0][5]")]
    [InlineData("[[1, 2]][0][1 div 0]")]
    [InlineData("[1, 2]['x'] + 0")]
    [InlineData("(1, 2)['x'] + 0")]
    public void Eval_Index_SelectorError_AgreesAcrossPlainAndCountedEvaluation(string source)
        => AssertIndexErrorAgreesAcrossEvaluators(source);

    [Theory]
    // A selector that names no position, or is no number, is located at its OWN written
    // selector slot (with several selectors, the one that failed), never escaping
    // unlocated. Columns are 1-based and the end column is exclusive.
    [InlineData("[1, 2]['x']", 1, 8, 1, 11)]
    [InlineData("(1, 2)['x']", 1, 8, 1, 11)]
    [InlineData("[1, 2][(0, 1)]", 1, 8, 1, 14)]
    [InlineData("[1, 2][()]", 1, 8, 1, 10)]
    [InlineData("[1, 2][3000000000]", 1, 8, 1, 18)]
    [InlineData("[1, 2][0, 7]", 1, 11, 1, 12)]
    // Nested selection points at the failing selector of the failing selection: the
    // inner `5` for an inner failure, the outer `5` for an outer one.
    [InlineData("[[1, 2]][5][0]", 1, 10, 1, 11)]
    [InlineData("[[1, 2]][0][5]", 1, 13, 1, 14)]
    // A selector sub-expression that fails on its own keeps its own span (the slot
    // it was written in); WithSpan only fills a missing one.
    [InlineData("[1, 2][1 div 0]", 1, 8, 1, 15)]
    [InlineData("[[1, 2]][0][1 div 0]", 1, 13, 1, 20)]
    // A spread selector: a cell it formed fails at the written spread slot, and a failure while
    // the spread is formed keeps its own inner span.
    [InlineData("[1, 2][[0, 7]*]", 1, 8, 1, 15)]
    [InlineData("I = [0, 7]\n[1, 2][I*]", 2, 8, 2, 10)]
    [InlineData("[1, 2][0, ([1 div 0])*]", 1, 13, 1, 20)]
    public void Eval_Index_SelectorError_CarriesSelectorSlotSpan(
        string source, int startLine, int startColumn, int endLine, int endColumn)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected a diagnostic but got: {result.Value}");

        var error = KatLangError.FromEvalError(result.Error);
        Assert.Equal(new SourceSpan(startLine, startColumn, endLine, endColumn), error.Span);
    }

    [Theory]
    [InlineData("[1, 2][0, 7]")]
    [InlineData("[1, 2][[0, 7]*]")]
    [InlineData("I = [0, 7]\n[1, 2][I*]")]
    [InlineData("[1, 2][0, ([1 div 0])*]")]
    [InlineData("[1, 2]['x']")]
    public async Task Eval_Index_SelectorErrorSpan_AgreesOnTheAsyncTwin(string source)
    {
        // The async twin positions every selector failure exactly like the synchronous machine.
        var sync = EvalFull(source);
        Assert.True(sync.IsError);
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var (asyncResult, _) = await Evaluator.RunCountedObservedAsync(
            program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache());
        Assert.True(asyncResult.IsError);
        var expected = KatLangError.FromEvalError(sync.Error);
        var actual = KatLangError.FromEvalError(asyncResult.Error);
        Assert.Equal(expected.Code, actual.Code);
        Assert.Equal(expected.Span, actual.Span);
    }

    [Fact]
    public void Eval_Index_SelectorErrorInPropertyBody_ReportsTheSelectorNotTheUseSite()
    {
        // The plain evaluator reaches this selection as a binary operand. Without a
        // span of its own the error was filled in by an outer use-site span,
        // mislocating the defect to `X` on line 2; it is the written selector `'x'`.
        var result = EvalFull("X = [1, 2]['x'] + 0\nX");
        if (result.IsOk)
            Assert.Fail($"Expected a diagnostic but got: {result.Value}");

        var error = KatLangError.FromEvalError(result.Error);
        Assert.Equal(new SourceSpan(1, 12, 1, 15), error.Span);
    }
}
