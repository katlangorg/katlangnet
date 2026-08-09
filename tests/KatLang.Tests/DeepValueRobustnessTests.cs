namespace KatLang.Tests;

/// <summary>
/// Deeply nested values are legal — evaluation limits bound only per-collection
/// breadth, so an ordinary in-budget loop builds a depth-n value in n steps —
/// and every whole-value walk must complete without exhausting the host stack:
/// a <see cref="StackOverflowException"/> terminates the embedding process
/// uncatchably. Language-level cases run well beyond the pre-fix crash
/// boundary (~3,700 nesting levels for structural equality on the default
/// 1 MiB stack); direct cases push the <see cref="Result"/> walks further.
/// </summary>
public class DeepValueRobustnessTests
{
    private const int LanguageDepth = 50_000;
    private const int DirectDepth = 200_000;

    // ── Language-level regression coverage ──────────────────────────────────

    private static EvalResult<IReadOnlyList<decimal>> Eval(string source)
    {
        var ast = SourceProvenance.ParseValid(source).Root;
        return Evaluator.RunFlat(new Expr.AlgorithmExpr(ast));
    }

    private static void AssertEval(string source, params decimal[] expected)
    {
        var result = Eval(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal(expected, result.Value);
    }

    private static string DeepListProgram(string body, int depthA = LanguageDepth, int depthB = LanguageDepth)
        => $"""
            Wrap = [x]
            A = Wrap.repeat({depthA}, 0)
            B = Wrap.repeat({depthB}, 0)
            C = Wrap.repeat({depthA}, 1)
            {body}
            """;

    [Fact]
    public void DeepListEqualityIsTrue()
        => AssertEval(DeepListProgram("A == B"), 1);

    [Fact]
    public void DeepListEqualityIsFalseAtTheLeaf()
        => AssertEval(DeepListProgram("A == C"), 0);

    [Fact]
    public void DeepListEqualityIsFalseOnDepthMismatch()
        => AssertEval(DeepListProgram("A == B", depthB: LanguageDepth - 1), 0);

    [Fact]
    public void DeepListInequalityOperator()
        => AssertEval(DeepListProgram("A != B, A != C"), 0, 1);

    [Fact]
    public void DeepSequenceEquality()
        => AssertEval($"""
            Wrap = (x, 7)
            A = Wrap.repeat({LanguageDepth}, 0)
            B = Wrap.repeat({LanguageDepth}, 0)
            C = Wrap.repeat({LanguageDepth}, 1)
            A == B, A == C
            """, 1, 0);

    [Fact]
    public void DeepDistinct()
        => AssertEval(DeepListProgram("distinct((A, B, C)).count"), 2);

    [Fact]
    public void DeepContains()
        => AssertEval(DeepListProgram("contains((A, 5), B), contains((A, 5), C)"), 1, 0);

    [Fact]
    public void DeepAtomsBuiltin()
        => AssertEval(DeepListProgram("atoms(A).count, atoms(A):0"), 1, 0);

    [Fact]
    public void DeepDotCallReceiverReification()
        => AssertEval(DeepListProgram("A.count"), 1);

    [Fact]
    public void DeepIndexSelectionNormalizesProjectedValue()
        => AssertEval(DeepListProgram("A:0"), 0);

    [Fact]
    public void DeepValueFlattensToHostAtoms()
        => AssertEval(DeepListProgram("A"), 0);

    [Fact]
    public void DeepValueInNumericOperandDiagnosticDoesNotCrash()
    {
        var result = Eval(DeepListProgram("A + 1"));
        Assert.True(result.IsError);

        var error = result.Error;
        while (error is EvalError.WithContext(_, var inner))
            error = inner;
        Assert.IsType<EvalError.TypeMismatch>(error);
    }

    [Fact]
    public void DeepValueInCallbackPositionReportsErrorWithoutCrashing()
    {
        var result = Eval(DeepListProgram("[9].map(A)"));
        Assert.True(result.IsError);
    }

    // ── Direct coverage of the Result walks at greater depth ────────────────

    private static Result DeepListChain(int depth, decimal leaf)
    {
        Result value = new Result.Atom(leaf);
        for (var i = 0; i < depth; i++)
            value = Result.ListValue.TakeOwnership([value]);
        return value;
    }

    private static Result DeepSequencePairChain(int depth, decimal leaf)
    {
        Result value = new Result.Atom(leaf);
        for (var i = 0; i < depth; i++)
            value = Result.SequenceValue.TakeOwnership([value, new Result.Atom(7)]);
        return value;
    }

    private static Result DeepSingletonSequenceChain(int depth, decimal leaf)
    {
        Result value = new Result.Atom(leaf);
        for (var i = 0; i < depth; i++)
            value = Result.SequenceValue.TakeOwnership([value]);
        return value;
    }

    [Fact]
    public void ValueComparerHandlesDeepListChains()
    {
        Assert.True(Result.ValueComparer.Equals(
            DeepListChain(DirectDepth, 0), DeepListChain(DirectDepth, 0)));
        Assert.False(Result.ValueComparer.Equals(
            DeepListChain(DirectDepth, 0), DeepListChain(DirectDepth, 1)));
        Assert.False(Result.ValueComparer.Equals(
            DeepListChain(DirectDepth, 0), DeepListChain(DirectDepth - 1, 0)));
    }

    [Fact]
    public void ValueComparerHandlesDeepSequenceChains()
    {
        Assert.True(Result.ValueComparer.Equals(
            DeepSequencePairChain(DirectDepth, 0), DeepSequencePairChain(DirectDepth, 0)));
        Assert.False(Result.ValueComparer.Equals(
            DeepSequencePairChain(DirectDepth, 0), DeepSequencePairChain(DirectDepth, 1)));
        // Kinds stay distinct at every depth: a list chain never equals a
        // singleton sequence chain over the same leaf.
        Assert.False(Result.ValueComparer.Equals(
            DeepListChain(DirectDepth, 0), DeepSingletonSequenceChain(DirectDepth, 0)));
    }

    [Fact]
    public void ValueComparerHashesDeepValuesConsistently()
    {
        Assert.Equal(
            Result.ValueComparer.GetHashCode(DeepListChain(DirectDepth, 0)),
            Result.ValueComparer.GetHashCode(DeepListChain(DirectDepth, 0)));

        var seen = new HashSet<Result>(Result.ValueComparer)
        {
            DeepListChain(DirectDepth, 0),
            DeepListChain(DirectDepth, 0),
            DeepListChain(DirectDepth, 1),
        };
        Assert.Equal(2, seen.Count);
    }

    [Fact]
    public void NormalizeHandlesDeepValues()
    {
        // A redundant singleton sequence chain canonicalizes all the way to
        // its leaf; exact list structure is preserved at full depth.
        Assert.Equal(new Result.Atom(4), DeepSingletonSequenceChain(DirectDepth, 4).Normalize());
        Assert.True(Result.ValueComparer.Equals(
            DeepListChain(DirectDepth, 0), DeepListChain(DirectDepth, 0).Normalize()));
    }

    [Fact]
    public void AtomViewsHandleDeepValues()
    {
        Assert.Equal([3m], DeepSingletonSequenceChain(DirectDepth, 3).ToAtoms());
        Assert.Equal([5m], DeepListChain(DirectDepth, 5).LanguageAtoms());
        Assert.Equal([6m], DeepListChain(DirectDepth, 6).ToHostAtoms());
        // Truth testing keeps lists opaque regardless of nesting.
        Assert.Empty(DeepListChain(DirectDepth, 5).ToAtoms());
    }

    [Fact]
    public void DiagnosticFormattingHandlesDeepValues()
    {
        const int depth = 100_000;
        var text = Evaluator.FormatResultForDiagnostic(DeepListChain(depth, 0));
        Assert.Equal(2 * depth + 1, text.Length);
        Assert.StartsWith("[[[", text);
        Assert.EndsWith("]]]", text);
        Assert.Equal('0', text[depth]);
    }
}
