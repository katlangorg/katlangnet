using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// Full-structure BINARY parity for the async expression-spine twin — the SYN-01
/// counterpart of <see cref="UnaryAsyncTwinStructuredParityTests"/>. The corpus-wide
/// differential suite already runs the SYN-01 spec and explorer cases through the twin
/// path under a Lean-neutral error category; these cases additionally compare every
/// structured error node and rendered diagnostic field, so an async-only regression of
/// the empty-operand rule (a twin arm that reintroduced the old passthrough, or one
/// that lost the binary context or span) is caught at the exact node.
/// </summary>
public class BinaryAsyncTwinStructuredParityTests
{
    public static TheoryData<string, string> BinaryOperandMatrix()
        => new()
        {
            // The canonical SYN-01 reproductions, with the empty operand routed
            // through a property so the async cache seam is genuinely exercised.
            { "empty divisor", "X = ()\n10 / X" },
            { "empty dividend", "X = ()\nX / 10" },
            { "empty left of ordering", "X = ()\nX > 10" },
            { "empty right of ordering", "X = ()\n10 > X" },
            { "empty left of and", "X = ()\nX and 7" },
            { "empty right of and", "X = ()\n7 and X" },
            { "empty left of or", "X = ()\nX or 7" },
            { "empty right of or", "X = ()\n7 or X" },
            { "empty plus string", "X = ()\nX + 'text'" },
            { "string plus empty", "X = ()\n'text' + X" },
            { "both operands empty", "X = ()\nX + X" },
            { "empty under an enclosing binary", "X = ()\n(X + 1) * 2" },
            { "empty in a callback body", "X = ()\nM(a) = a + X\nmap((1, 2), M)" },
            // Contrast: the other non-scalar operand kinds take the same path.
            { "sequence operand", "X = (1, 2)\nX + 3" },
            { "list operand", "X = [1, 2]\n3 + X" },
            // Controls: structural equality and ordinary scalar results are unchanged.
            { "empty equals empty", "X = ()\nX == X" },
            { "empty differs from atom", "X = ()\nX != 0" },
            { "numeric arithmetic", "X = 3\nX + 4" },
            { "numeric ordering", "X = 3\nX > 4" },
        };

    [Theory]
    [MemberData(nameof(BinaryOperandMatrix))]
    public async Task AsyncTwin_BinaryOutcomeMatchesSyncGenericInFull(string label, string source)
    {
        Assert.False(string.IsNullOrEmpty(label));
        var ast = Program(source);
        var sync = Evaluator.RunCountedObserved(ast, enableOptimizations: false).Result;

        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var asyncResult = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedAsync(ast, cache));

        Assert.Equal(sync.IsError, asyncResult.IsError);
        if (sync.IsError)
        {
            Assert.Equal(DescribeErrorTree(sync.Error), DescribeErrorTree(asyncResult.Error));

            var syncRendered = KatLangError.FromEvalError(sync.Error);
            var asyncRendered = KatLangError.FromEvalError(asyncResult.Error);
            Assert.Equal(syncRendered.Message, asyncRendered.Message);
            Assert.Equal(syncRendered.Code, asyncRendered.Code);
            Assert.Equal(
                (syncRendered.StartLine, syncRendered.StartColumn, syncRendered.EndLine, syncRendered.EndColumn),
                (asyncRendered.StartLine, asyncRendered.StartColumn, asyncRendered.EndLine, asyncRendered.EndColumn));
        }
        else
        {
            Assert.Equal(sync.Value.Value, asyncResult.Value.Value, Result.ValueComparer);
            Assert.Equal(sync.Value.EmittedCount, asyncResult.Value.EmittedCount);
        }

        Assert.True(cache.AsyncAccesses > 0, "the operand property must route through the async cache seam");
        Assert.Equal(0, cache.SyncAccesses);
    }

    [Theory]
    [InlineData("10 / X", "right")]
    [InlineData("X > 10", "left")]
    [InlineData("X and 7", "left")]
    [InlineData("X + X", "left")]
    public async Task AsyncTwin_EmptyOperandAfterSuspension_KeepsTheSpannedContextAndBlame(string expression, string side)
    {
        var ast = Program($"X = ()\n{expression}");
        var sync = Evaluator.RunCountedObserved(ast, enableOptimizations: false).Result;
        Assert.True(sync.IsError);
        var syncInnermost = Assert.IsType<EvalError.TypeMismatch>(Innermost(sync.Error));
        Assert.Contains($"the {side} operand was a sequence value with 0 sequence elements: ()", syncInnermost.Message);
        Assert.Equal([$"while evaluating `{expression}`"], ContextChain(sync.Error));
        // The rejection is located at the whole binary expression on line 2; after a
        // genuine suspension the twin must report the identical tree, not a copy that
        // lost the context frame or its span.
        Assert.Equal(((int?)2, (int?)1, (int?)2, (int?)expression.Length), Span(sync.Error));

        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var result = await AsyncEvaluationHarness.Complete(Evaluator.RunCountedAsync(ast, cache));
        Assert.True(result.IsError);
        Assert.Equal(DescribeErrorTree(sync.Error), DescribeErrorTree(result.Error));
        Assert.Equal(Span(sync.Error), Span(result.Error));
        Assert.Equal(KatLangError.FromEvalError(sync.Error).Message, KatLangError.FromEvalError(result.Error).Message);
        Assert.True(cache.AsyncAccesses > 0);
        Assert.NotEmpty(cache.ThreadHops);
        Assert.Equal(0, cache.SyncAccesses);
    }
}
