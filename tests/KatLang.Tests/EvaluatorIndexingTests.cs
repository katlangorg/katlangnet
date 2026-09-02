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
    public void Eval_Index_SequenceValueSelection_ProjectsTopLevelContent()
    {
        var result = EvalFull(
            """
            A = (1, 2), (3, 4)
            A:0
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
            count(A:0)
            (A:0).count
            """,
            2,
            2);

    [Fact]
    public void Eval_Index_NestedSequenceValueSelection_ProjectsOneLevelOnly()
    {
        var result = EvalFull(
            """
            A = ((1, 2), (3, 4)), ((5, 6), (7, 8))
            A:0
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertNestedSequenceValueAtoms(result.Value, [1m, 2m], [3m, 4m]);
    }

    [Fact]
    public void Eval_Index_NestedSequenceValueSelection_CountsProjectedContentOneLevelAtATime()
        => AssertEval(
            """
            A = ((1, 2), (3, 4)), ((5, 6), (7, 8))
            count(A:0)
            count(A:0:1)
            """,
            2,
            2);

    [Fact]
    public void Eval_Index_ChainedSequenceValueSelection_ProjectsEachStep()
    {
        var result = EvalFull(
            """
            A = ((1, 2), (3, 4)), ((5, 6), (7, 8))
            A:0:1
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
    [InlineData("():0")]
    [InlineData("[]:0")]
    [InlineData("(1, 2):2")]
    [InlineData("[1, 2]:2")]
    [InlineData("[1, 2]:100")]
    [InlineData("A = []\nA:0")]
    public void Eval_Index_EmptyOrOutOfRangeTarget_FailsWithBadIndex(string source)
        => AssertEvalFailsWithBadIndex(source);

    [Theory]
    [InlineData("X = 1, 2, 3\ni = 0 - 1\nX:i")]
    [InlineData("X = [1, 2, 3]\ni = 0 - 1\nX:i")]
    [InlineData("(1, 2, 3):1.5")]
    [InlineData("[1, 2, 3]:1.5")]
    public void Eval_Index_NegativeOrNonIntegralSelector_FailsWithBadIndex(string source)
        => AssertEvalFailsWithBadIndex(source);

    [Theory]
    [InlineData("(1, 2, 3):3000000000")]
    [InlineData("[1, 2, 3]:3000000000")]
    public void Eval_Index_SelectorBeyondIntRange_FailsWithBadIndex(string source)
        // C#-only guard for the host int cast; Lean's unbounded integer
        // selector reaches the same out-of-range badIndex through select?.
        => AssertEvalFailsWithBadIndex(source);

    [Theory]
    [InlineData("(1, 2, 3):'1'")]
    [InlineData("[1, 2, 3]:'1'")]
    public void Eval_Index_StringSelector_FailsWithTypeMismatch(string source)
        => AssertEvalFailsWithTypeMismatch(source, "Expected a number, got a string");

    [Theory]
    [InlineData("(1, 2, 3):(0, 1)")]
    [InlineData("[1, 2, 3]:(0, 1)")]
    [InlineData("(1, 2, 3):[0]")]
    [InlineData("[1, 2, 3]:[0]")]
    [InlineData("(1, 2, 3):()")]
    [InlineData("[1, 2, 3]:()")]
    public void Eval_Index_NonNumericStructuredSelector_FailsWithBadArity(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected BadArity error but got: {result.Value}");

        Assert.IsType<EvalError.BadArity>(Innermost(result.Error));
    }

    [Theory]
    [InlineData("(1, 2, 3):(1 div 0)")]
    [InlineData("[1, 2, 3]:(1 div 0)")]
    public void Eval_Index_FailedSelectorExpression_PropagatesError(string source)
        => AssertEvalFails(source);

    [Fact]
    public void Eval_Index_OutOfRangeError_SpanAgreesAcrossTargetKinds()
    {
        // `(1, 2):9` and `[1, 2]:9` occupy the same source columns, so the
        // out-of-range projection error must carry the identical span.
        var sequenceError = AssertEvalFailsWithBadIndex("(1, 2):9");
        var listError = AssertEvalFailsWithBadIndex("[1, 2]:9");

        Assert.NotNull(sequenceError.Span);
        Assert.NotNull(listError.Span);
        Assert.Equal(sequenceError.Span, listError.Span);
        Assert.Equal("Bad index", KatLangError.FromEvalError(listError).Message);
    }

    // ── Index diagnostics: source-faithful names and selector-error spans ────

    /// <summary>
    /// Diagnostic expression names use KatLang source syntax, so an index must
    /// render as `target:selector`. Bracket text would be actively misleading:
    /// `[...]` is exact list literal syntax, so `Rows[0]` reads back as the
    /// adjacency `Rows, [0]`. <paramref name="forbiddenBracketName"/> is the
    /// pre-fix rendering; a bracket selector such as `Rows:[0]` is legitimate
    /// syntax, so only the bracket form of this specific index is banned.
    /// </summary>
    /// <summary>
    /// The receiver-rendering probe: <paramref name="definitions"/> plus the
    /// dot edge under test, wrapped by <see cref="ClosedMemberProbe"/> so the
    /// unresolvable member reaches the runtime lookup that renders the
    /// receiver.
    /// </summary>
    private static void AssertIndexDiagnosticName(
        string definitions, string expression, string expectedName, string forbiddenBracketName)
    {
        var result = EvalFull(ClosedMemberProbe(definitions, expression));
        if (result.IsOk)
            Assert.Fail($"Expected a diagnostic but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains($"`{expectedName}`", formatted);
        Assert.DoesNotContain(forbiddenBracketName, formatted);
    }

    [Theory]
    // The renderer is syntax-based, so a sequence target and a list target
    // render identically.
    [InlineData("Rows = [[1, 2]]\n")]
    [InlineData("Rows = [[1, 2], [3, 4]]\n")]
    [InlineData("Rows = ((1, 2), (3, 4))\n")]
    public void Eval_Index_DiagnosticName_RendersSourceFaithfulColonSyntax(string definitions)
        => AssertIndexDiagnosticName(definitions, "Rows:0.Missing", "Rows:0", "Rows[0]");

    [Fact]
    public void Eval_Index_ChainedDiagnosticName_RendersEachSelector()
        => AssertIndexDiagnosticName(
            "Rows = [[[1]]]\n", "Rows:0:0.Missing", "Rows:0:0", "Rows[0][0]");

    [Fact]
    public void Eval_Index_DiagnosticName_ParenthesizesOperandsThatWouldRebind()
    {
        // Indexing binds tighter than every binary operator, so a bare
        // `Rows + Rows:0` would read as `Rows + (Rows:0)`.
        AssertIndexDiagnosticName(
            "Rows = (1, 2)\n",
            "(Rows + Rows):0.Missing",
            "(Rows + Rows):0",
            "(Rows + Rows)[0]");

        // The selector is a primary in source syntax, so a compound selector
        // keeps the parentheses it was written with.
        AssertIndexDiagnosticName(
            "Rows = ((1, 2), (3, 4))\ni = 0\n",
            "Rows:(i + 1).Missing",
            "Rows:(i + 1)",
            "Rows[(i + 1)]");

        // Established call abbreviation is preserved on an index target.
        AssertIndexDiagnosticName(
            "", "take([1, 2, 3], 1):0.Missing", "take(...):0", "take(...)[0]");

        // A list-literal selector is legitimate syntax and stays bare: the ban
        // above is on bracket INDEXING, not on brackets as such.
        AssertIndexDiagnosticName(
            "Rows = ((1, 2), (3, 4))\n", "Rows:[0].Missing", "Rows:[0]", "Rows[[0]]");
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
    /// EvalIndexSelectionCounted owns the index-expression span, so plain and
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
    [InlineData("(1, 2):'x'")]
    [InlineData("[1, 2]:'x'")]
    [InlineData("(1, 2):(0, 1)")]
    [InlineData("[1, 2]:(0, 1)")]
    [InlineData("(1, 2):()")]
    [InlineData("[1, 2]:()")]
    [InlineData("(1, 2):(1 div 0)")]
    [InlineData("[1, 2]:(1 div 0)")]
    [InlineData("(1, 2):1.5")]
    [InlineData("[1, 2]:1.5")]
    [InlineData("(1, 2):3000000000")]
    [InlineData("[1, 2]:3000000000")]
    [InlineData("(1, 2):2")]
    [InlineData("[1, 2]:2")]
    // Nested projection, and an index reached through the plain evaluator as a
    // binary operand.
    [InlineData("[[1, 2]]:5:0")]
    [InlineData("[[1, 2]]:0:5")]
    [InlineData("[[1, 2]]:0:(1 div 0)")]
    [InlineData("[1, 2]:'x' + 0")]
    [InlineData("(1, 2):'x' + 0")]
    public void Eval_Index_SelectorError_AgreesAcrossPlainAndCountedEvaluation(string source)
        => AssertIndexErrorAgreesAcrossEvaluators(source);

    [Theory]
    // A selector error carries the full `target:selector` span rather than
    // escaping unlocated. Columns are 1-based and end-exclusive.
    [InlineData("[1, 2]:'x'", 1, 1, 1, 10)]
    [InlineData("(1, 2):'x'", 1, 1, 1, 10)]
    [InlineData("[1, 2]:(0, 1)", 1, 1, 1, 13)]
    [InlineData("[1, 2]:()", 1, 1, 1, 9)]
    [InlineData("[1, 2]:3000000000", 1, 1, 1, 17)]
    // Nested projection points at the failing index expression: the inner
    // `[[1, 2]]:5` for an inner failure, the whole expression for an outer one.
    [InlineData("[[1, 2]]:5:0", 1, 1, 1, 10)]
    [InlineData("[[1, 2]]:0:5", 1, 1, 1, 12)]
    // A selector sub-expression that fails on its own keeps its own, more
    // specific span; WithSpan only fills a missing one.
    [InlineData("[1, 2]:(1 div 0)", 1, 9, 1, 15)]
    [InlineData("[[1, 2]]:0:(1 div 0)", 1, 13, 1, 19)]
    public void Eval_Index_SelectorError_CarriesIndexExpressionSpan(
        string source, int startLine, int startColumn, int endLine, int endColumn)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected a diagnostic but got: {result.Value}");

        var error = KatLangError.FromEvalError(result.Error);
        Assert.Equal((startLine, startColumn, endLine, endColumn),
            (error.StartLine, error.StartColumn, error.EndLine, error.EndColumn));
    }

    [Fact]
    public void Eval_Index_SelectorErrorInPropertyBody_ReportsTheIndexNotTheUseSite()
    {
        // The plain evaluator reaches this index as a binary operand. Without a
        // span of its own the error was filled in by an outer use-site span,
        // mislocating the defect to `X` on line 2.
        var result = EvalFull("X = [1, 2]:'x' + 0\nX");
        if (result.IsOk)
            Assert.Fail($"Expected a diagnostic but got: {result.Value}");

        var error = KatLangError.FromEvalError(result.Error);
        Assert.Equal((1, 5, 1, 14),
            (error.StartLine, error.StartColumn, error.EndLine, error.EndColumn));
    }
}
