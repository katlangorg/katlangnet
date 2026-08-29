using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests.AsyncEvaluation;

/// <summary>
/// Full-structure unary parity for the async expression-spine twin. The corpus-wide
/// differential suite intentionally uses a Lean-neutral error category; these cases
/// additionally compare every structured error node and rendered diagnostic field.
/// </summary>
public class UnaryAsyncTwinStructuredParityTests
{
    public static TheoryData<string, string> UnaryOperandMatrix()
        => new()
        {
            { "minus numeric", "X = 3\n-X" },
            { "minus zero", "X = 0\n-X" },
            { "not zero", "X = 0\nnot X" },
            { "not non-zero", "X = 3\nnot X" },
            { "empty sequence", "X = ()\n-X" },
            { "minus string", "X = 'text'\n-X" },
            { "not string", "X = 'text'\nnot X" },
            { "list", "X = [1, 2]\n-X" },
            { "non-singleton sequence", "X = (1, 2)\nnot X" },
            { "sequence collapsing to atom", "X = ((3))\n-X" },
            { "nested unary failure", "X = 'text'\nnot -X" },
        };

    [Theory]
    [MemberData(nameof(UnaryOperandMatrix))]
    public async Task AsyncTwin_UnaryOutcomeMatchesSyncGenericInFull(string label, string source)
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
}
