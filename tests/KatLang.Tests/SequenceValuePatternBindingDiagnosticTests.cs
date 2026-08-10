namespace KatLang.Tests;

/// <summary>
/// A mismatch produced at a nested <see cref="SequenceValueParameterPattern"/>
/// level is attributed to the WRITTEN pattern group via
/// <see cref="SequenceValueParameterBindingContext"/> — never to the enclosing
/// call's argument count: <c>F((b, c)) = b</c> called as <c>F((1, 2, 3))</c>
/// describes <c>(b, c)</c> receiving three values instead of claiming
/// <c>F</c> was called with three arguments. The innermost Lean-aligned
/// <c>ArityMismatch(Expected, Actual)</c> and the outer call/dot-call contexts
/// are preserved; genuine top-level call-arity mismatches are never wrapped;
/// assignment deconstruction keeps its own
/// <see cref="DeconstructionBindingContext"/> wording with precedence.
/// </summary>
public class SequenceValuePatternBindingDiagnosticTests
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
    /// Fails the source under BOTH plain and counted evaluation, requires one
    /// shared rendered message (plain/counted diagnostic parity), and returns
    /// the plain error for structured assertions.
    /// </summary>
    private static (string Message, EvalError PlainError) FailWithParity(string source)
    {
        var program = Program(source);

        var plain = Evaluator.Run(program);
        Assert.True(plain.IsError, $"expected plain evaluation failure for: {source}");

        var counted = Evaluator.RunCounted(program);
        Assert.True(counted.IsError, $"expected counted evaluation failure for: {source}");

        var plainMessage = KatLangError.FromEvalError(plain.Error).Message;
        var countedMessage = KatLangError.FromEvalError(counted.Error).Message;
        Assert.Equal(plainMessage, countedMessage);

        return (plainMessage, plain.Error);
    }

    [Fact]
    public void NestedGroup_OverSupplied_IsAttributedToThePatternNotTheCall()
    {
        var (message, error) = FailWithParity(
            """
            F((b, c)) = b
            F((1, 2, 3))
            """);

        Assert.Equal("Sequence-value parameter pattern `(b, c)` expects 2 values, but received 3 values.", message);
        Assert.DoesNotContain("was called with 3 arguments", message, StringComparison.Ordinal);

        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal(2, arity.Expected);
        Assert.Equal(3, arity.Actual);

        var contexts = Contexts(error);
        var patternContext = Assert.Single(contexts.OfType<SequenceValueParameterBindingContext>());
        Assert.Equal("(b, c)", patternContext.PatternDisplayName);
        Assert.False(patternContext.HasCollectingItem);
        // The outer call context stays in the structured tree.
        Assert.Contains(contexts, static context => context is CallContext);
    }

    [Fact]
    public void SecondParameterGroup_UnderSupplied_DescribesThePattern()
    {
        var (message, error) = FailWithParity(
            """
            F(a, (b, c)) = a
            F(1, 2)
            """);

        Assert.Equal("Sequence-value parameter pattern `(b, c)` expects 2 values, but received 1 value.", message);
        Assert.DoesNotContain("was called with 1 argument", message, StringComparison.Ordinal);

        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal(2, arity.Expected);
        Assert.Equal(1, arity.Actual);
    }

    [Fact]
    public void DotCallForm_IsAttributedToThePattern()
    {
        var (message, error) = FailWithParity(
            """
            Lib = {
              F((b, c)) = b
            }
            Lib.F((1, 2, 3))
            """);

        Assert.Equal("Sequence-value parameter pattern `(b, c)` expects 2 values, but received 3 values.", message);

        var contexts = Contexts(error);
        Assert.Single(contexts.OfType<SequenceValueParameterBindingContext>());
        // The outer dot-call context stays in the structured tree.
        Assert.Contains(contexts, static context => context is DotCallContext);
    }

    [Fact]
    public void DeeperNesting_NamesTheInnermostFailingGroup()
    {
        var (message, error) = FailWithParity(
            """
            F((b, (c, d))) = b
            F((1, (2, 3, 4)))
            """);

        Assert.Equal("Sequence-value parameter pattern `(c, d)` expects 2 values, but received 3 values.", message);

        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal(2, arity.Expected);
        Assert.Equal(3, arity.Actual);
    }

    [Fact]
    public void CollectingGroup_Underflow_UsesAtLeastWording()
    {
        var (message, error) = FailWithParity(
            """
            F((b, *c, d)) = b
            F((1))
            """);

        Assert.Equal("Sequence-value parameter pattern `(b, *c, d)` expects at least 2 values, but received 1 value.", message);

        var patternContext = Assert.Single(Contexts(error).OfType<SequenceValueParameterBindingContext>());
        Assert.True(patternContext.HasCollectingItem);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal(2, arity.Expected);
        Assert.Equal(1, arity.Actual);
    }

    [Fact]
    public void GenuineTopLevelCallArityMismatch_IsNeverWrapped()
    {
        // Positive control: a real top-level argument-count failure keeps the
        // signature-first call rendering and carries no nested-pattern context.
        var (message, error) = FailWithParity(
            """
            F(a, (b, c)) = a
            F(1, 2, 3)
            """);

        Assert.Equal("Callable `F(a, (b, c))` expects 2 arguments, but was called with 3 arguments.", message);
        Assert.Empty(Contexts(error).OfType<SequenceValueParameterBindingContext>());
    }

    [Fact]
    public void AssignmentDeconstruction_KeepsAssignmentWordingWithPrecedence()
    {
        // The parser-elaborated deconstruction helper binds through an inline
        // sequence-value pattern; its failures must STILL surface as the
        // assignment-focused wording, with DeconstructionBindingContext
        // replacing the nested pattern context.
        var (message, error) = FailWithParity("x, y = (1, 2, 3)\nx");

        Assert.Contains(
            "Assignment pattern `x, y` expects 2 values from the right-hand side, but it supplied 3 values.",
            message,
            StringComparison.Ordinal);
        Assert.DoesNotContain("Sequence-value parameter pattern", message, StringComparison.Ordinal);

        var contexts = Contexts(error);
        Assert.Single(contexts.OfType<DeconstructionBindingContext>());
        Assert.Empty(contexts.OfType<SequenceValueParameterBindingContext>());
    }

    [Fact]
    public void LoopStateNestedGroup_IsAttributedToThePattern()
    {
        // A grouped loop-state slot whose ITEMS mismatch the nested pattern is a
        // nested-pattern failure (the top-level state-slot count is fine), so it
        // renders against the written group, not the loop or the call.
        var (message, error) = FailWithParity(
            """
            Step((x, y)) = (y, x + y)
            Step.repeat(3, (1, 2, 3))
            """);

        Assert.Equal("Sequence-value parameter pattern `(x, y)` expects 2 values, but received 3 values.", message);
        Assert.Single(Contexts(error).OfType<SequenceValueParameterBindingContext>());
    }
}
