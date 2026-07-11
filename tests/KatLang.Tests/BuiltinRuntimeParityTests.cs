namespace KatLang.Tests;

public class BuiltinRuntimeParityTests
{
    public static TheoryData<string, string, string, int, int> SequenceBuiltinArityDiagnosticCases => new()
    {
        { "map()", "map", "map(values..., mapper)", 1, 0 },
        { "take()", "take", "take(values..., count)", 1, 0 },
        { "skip()", "skip", "skip(values..., count)", 1, 0 },
        { "reduce(1)", "reduce", "reduce(values..., reducer, initial)", 2, 1 },
    };

    public static TheoryData<BuiltinId> RequireNonEmptySequenceBuiltinCases => new()
    {
        BuiltinId.first,
        BuiltinId.last,
        BuiltinId.min,
        BuiltinId.max,
        BuiltinId.avg,
    };

    public static TheoryData<string, string, string, int, int> FixedBuiltinArityDiagnosticCases => new()
    {
        { "range(1)", "range(start, stop)", "Callable `range(start, stop)` expects 2 arguments, but was called with 1 argument.", 0, 1 },
        { "atoms(1, 2)", "atoms(value)", "Callable `atoms(value)` expects 1 argument, but was called with 2 arguments.", 0, 2 },
    };

    [Theory]
    [MemberData(nameof(SequenceBuiltinArityDiagnosticCases))]
    public void SequenceBuiltinArityDiagnostics_IncludeSignatureDisplay(
        string source,
        string builtinName,
        string signatureDisplay,
        int expectedMinimum,
        int actual)
    {
        var error = AssertEvalFails(source, out var message);

        // Rest-shaped builtins are item supplies (unbounded max), so the arity floor reads
        // "expects at least N item(s)".
        Assert.Equal(
            $"while evaluating call to {builtinName}: Builtin '{builtinName}' expects at least {expectedMinimum} item(s) for {signatureDisplay}, but received {actual}.",
            message);

        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal(expectedMinimum, arity.Expected);
        Assert.Equal(actual, arity.Actual);
        Assert.NotNull(arity.Signature);
        Assert.Equal(signatureDisplay, arity.Signature.DisplayText);
    }

    [Fact]
    public void SequenceBuiltinValidArity_TakeSequenceAndCountSuffix()
        => AssertEval("take((1, 2, 3), 2)", 1, 2);

    [Fact]
    public void SequenceBuiltinSuffixKindDiagnostics_UseDescriptorName()
    {
        var error = AssertEvalFails("""
            take((1, 2), 'x')
            """, out var message);

        Assert.Contains("take count must be exactly one whole-number value", message, StringComparison.Ordinal);
        Assert.IsType<EvalError.BadArity>(Innermost(error));
    }

    [Theory]
    [MemberData(nameof(RequireNonEmptySequenceBuiltinCases))]
    public void SequenceBuiltinEmptyPolicyMetadata_MatchesRuntimeDiagnostics(BuiltinId builtinId)
    {
        var builtin = BuiltinRegistry.GetBuiltin(builtinId);
        Assert.NotNull(builtin.SequenceMetadata);
        Assert.Equal(SequenceBuiltinEmptyPolicy.RequireAnyItem, builtin.SequenceMetadata.Value.EmptyPolicy);

        var error = AssertEvalFails($"{builtin.Name}(())", out var message);

        Assert.Contains($"{builtin.Name} requires a non-empty collection", message, StringComparison.Ordinal);
        Assert.IsType<EvalError.BadArity>(Innermost(error));
    }

    [Fact]
    public void Eval_Avg_EmptySource_FailsWithContext()
        => AssertEmptySequenceBuiltinFailsWithContext("avg(())", "avg");

    [Fact]
    public void Eval_Min_EmptySource_FailsWithContext()
        => AssertEmptySequenceBuiltinFailsWithContext("min(())", "min");

    [Fact]
    public void Eval_Max_EmptySource_FailsWithContext()
        => AssertEmptySequenceBuiltinFailsWithContext("max(())", "max");

    [Fact]
    public void Eval_Map_BuiltinAsCallback_AppliesPerItem()
        => AssertEval("map((1, 2, 3), count)", 1, 1, 1);

    [Fact]
    public void Eval_Filter_BuiltinAsPredicate_AppliesPerItem()
        => AssertEval("filter((0, 1, 2), distinct)", 1, 2);

    [Theory]
    [MemberData(nameof(FixedBuiltinArityDiagnosticCases))]
    public void FixedBuiltinArityDiagnostics_UseSignatureDisplay(
        string source,
        string signatureDisplay,
        string expectedMessage,
        int expected,
        int actual)
    {
        var error = AssertEvalFails(source, out var message);

        Assert.Equal(expectedMessage, message);

        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal(expected, arity.Expected);
        Assert.Equal(actual, arity.Actual);
        Assert.NotNull(arity.Signature);
        Assert.Equal(signatureDisplay, arity.Signature.DisplayText);
    }

    [Fact]
    public void FixedBuiltinIfArityDiagnostics_UseSignatureDisplay_WhenEvaluatorReceivesWrongArity()
    {
        var error = AssertEvalFails(
            EvalBuiltinCall(BuiltinId.@if, new Expr.Num(1), new Expr.Num(2)),
            out var message);

        Assert.Equal(
            "Callable `if(condition, whenTrue, whenFalse)` expects 3 arguments, but was called with 2 arguments.",
            message);

        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal(3, arity.Expected);
        Assert.Equal(2, arity.Actual);
        Assert.NotNull(arity.Signature);
        Assert.Equal("if(condition, whenTrue, whenFalse)", arity.Signature.DisplayText);
    }

    private static EvalResult<Result> EvalFull(string source)
    {
        var parseResult = Parser.Parse(source);
        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(static diagnostic => diagnostic.Message)));

        return Evaluator.Run(new Expr.Block(parseResult.Root));
    }

    private static EvalResult<Result> EvalBuiltinCall(BuiltinId builtinId, params Expr[] arguments)
    {
        var argumentAlgorithm = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [],
            Output: arguments);
        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [],
            Output: [new Expr.Call(new Expr.Block(new Algorithm.Builtin(builtinId)), argumentAlgorithm)]);

        return Evaluator.Run(new Expr.Block(root));
    }

    private static void AssertEval(string source, params decimal[] expected)
    {
        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal(expected, result.Value.ToAtoms());
    }

    private static void AssertEmptySequenceBuiltinFailsWithContext(string source, string builtinName)
    {
        var error = AssertEvalFails(source, out var message);

        Assert.Contains($"while evaluating call to {builtinName}", message, StringComparison.Ordinal);
        Assert.Contains($"{builtinName} requires a non-empty collection", message, StringComparison.Ordinal);
        Assert.IsType<EvalError.BadArity>(Innermost(error));
    }

    private static EvalError AssertEvalFails(string source, out string message)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        message = KatLangError.FromEvalError(result.Error).Message;
        return result.Error;
    }

    private static EvalError AssertEvalFails(EvalResult<Result> result, out string message)
    {
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        message = KatLangError.FromEvalError(result.Error).Message;
        return result.Error;
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        return error;
    }
}