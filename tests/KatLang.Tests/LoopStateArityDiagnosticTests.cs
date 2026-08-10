using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// Patterned loop-step state diagnostics report the binder-computed TOP-LEVEL
/// state-slot count, never the flattened capture count: <c>Step((x, y))</c> has
/// ONE state slot, so <c>Step.repeat(3, 1, 1)</c> is <c>ArityMismatch(1, 2)</c>
/// — not the formerly contradictory <c>ArityMismatch(2, 2)</c>. The context's
/// parameter names are the matching top-level display labels
/// (<c>"(x, y)"</c> is one entry). Covers <c>repeat</c> and <c>while</c>, loop
/// optimization enabled and disabled, and plain and counted evaluation.
/// No Lean change: this restores C#'s structured payload to the existing Lean
/// binder result.
/// </summary>
public class LoopStateArityDiagnosticTests
{
    private static Expr Program(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        return error;
    }

    private static IReadOnlyList<ErrorContext> Contexts(EvalError error)
    {
        var contexts = new List<ErrorContext>();
        while (error is EvalError.WithContext context)
        {
            contexts.Add(context.ErrorContext);
            error = context.Inner;
        }

        return contexts;
    }

    /// <summary>
    /// Any arity mismatch specifically attributed to
    /// <see cref="LoopStateBindingContext"/> must never carry
    /// <c>Expected == Actual</c> — that contradiction is exactly the flattened
    /// recomputation bug this family pins against.
    /// </summary>
    private static void AssertNoContradictoryLoopStateMismatch(EvalError error)
    {
        var current = error;
        while (current is EvalError.WithContext context)
        {
            if (context.ErrorContext is LoopStateBindingContext
                && context.Inner is EvalError.ArityMismatch mismatch)
            {
                Assert.NotEqual(mismatch.Expected, mismatch.Actual);
            }

            current = context.Inner;
        }
    }

    /// <summary>
    /// Evaluates the source in all four modes — plain and counted evaluation,
    /// each with loop optimization disabled and enabled — requires failure in
    /// every mode with ONE shared rendered message, and returns the errors.
    /// </summary>
    private static (string Message, IReadOnlyList<EvalError> Errors) FailInAllEvaluationModes(string source)
    {
        var program = Program(source);
        var errors = new List<EvalError>();

        foreach (var enableOptimization in new[] { false, true })
        {
            var plain = Evaluator.Run(
                program,
                new RunScopedZeroArgPropertyResultCache(),
                enableOptimization);
            Assert.True(plain.IsError, $"expected plain failure (optimization={enableOptimization})");
            errors.Add(plain.Error);

            var (counted, _) = Evaluator.RunCountedObserved(program, enableOptimizations: enableOptimization);
            Assert.True(counted.IsError, $"expected counted failure (optimization={enableOptimization})");
            errors.Add(counted.Error);
        }

        var message = Assert.Single(errors
            .Select(static error => KatLangError.FromEvalError(error).Message)
            .Distinct());

        foreach (var error in errors)
            AssertNoContradictoryLoopStateMismatch(error);

        return (message, errors);
    }

    private static void AssertLoopStatePayload(
        IReadOnlyList<EvalError> errors,
        int expectedStateSlots,
        int actualStateValues,
        IReadOnlyList<string> topLevelParameterLabels)
    {
        foreach (var error in errors)
        {
            var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
            Assert.Equal(expectedStateSlots, arity.Expected);
            Assert.Equal(actualStateValues, arity.Actual);

            var loopContext = Assert.Single(Contexts(error).OfType<LoopStateBindingContext>());
            Assert.Equal(topLevelParameterLabels, loopContext.StepParameterNames);
            Assert.Equal(actualStateValues, loopContext.ActualStateValueCount);
        }
    }

    [Fact]
    public void PatternedStep_Repeat_ReportsOneTopLevelStateSlot()
    {
        var (message, errors) = FailInAllEvaluationModes(
            """
            Step((x, y)) = (y, x + y)
            Step.repeat(3, 1, 1)
            """);

        AssertLoopStatePayload(errors, expectedStateSlots: 1, actualStateValues: 2, ["(x, y)"]);
        Assert.Contains(
            "`repeat` step expects 1 state value for 1 parameter '(x, y)'",
            message,
            StringComparison.Ordinal);
        Assert.Contains("current loop state has 2 state values", message, StringComparison.Ordinal);
    }

    [Fact]
    public void PatternedStep_While_ReportsOneTopLevelStateSlot()
    {
        var (message, errors) = FailInAllEvaluationModes(
            """
            Step((x, y)) = (y, x + y), 0
            Step.while(1, 1)
            """);

        AssertLoopStatePayload(errors, expectedStateSlots: 1, actualStateValues: 2, ["(x, y)"]);
        Assert.Contains(
            "`while` step expects 1 state value for 1 parameter '(x, y)'",
            message,
            StringComparison.Ordinal);
        Assert.Contains("current loop state has 2 state values", message, StringComparison.Ordinal);
    }

    [Fact]
    public void PatternedStep_TwoTopLevelSlots_ReportsTwoVersusThree()
    {
        var (message, errors) = FailInAllEvaluationModes(
            """
            Step((x, y), z) = z
            Step.repeat(1, 1, 2, 3)
            """);

        AssertLoopStatePayload(errors, expectedStateSlots: 2, actualStateValues: 3, ["(x, y)", "z"]);
        Assert.Contains(
            "`repeat` step expects 2 state values for 2 parameters '(x, y)' and 'z'",
            message,
            StringComparison.Ordinal);
        Assert.Contains("current loop state has 3 state values", message, StringComparison.Ordinal);
    }

    [Fact]
    public void PatternedStep_GroupedInitialState_StillSucceeds()
    {
        // The correctly grouped call binds the ONE state slot and keeps working.
        var program = Program(
            """
            Step((x, y)) = (y, x + y)
            Step.repeat(3, (1, 1))
            """);
        var expected = new Result.SequenceValue([new Result.Atom(3), new Result.Atom(5)]);

        foreach (var enableOptimization in new[] { false, true })
        {
            var plain = Evaluator.Run(
                program,
                new RunScopedZeroArgPropertyResultCache(),
                enableOptimization);
            Assert.False(plain.IsError, $"expected plain success (optimization={enableOptimization}) but got: {(plain.IsError ? plain.Error : null)}");
            Assert.True(
                Result.ValueComparer.Equals(expected, plain.Value),
                $"Expected {expected} but got {plain.Value} (optimization={enableOptimization})");

            var (counted, _) = Evaluator.RunCountedObserved(program, enableOptimizations: enableOptimization);
            Assert.False(counted.IsError, $"expected counted success (optimization={enableOptimization})");
            Assert.True(
                Result.ValueComparer.Equals(expected, counted.Value.Value),
                $"Expected {expected} but got {counted.Value.Value} (counted, optimization={enableOptimization})");
        }
    }
}
