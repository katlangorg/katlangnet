namespace KatLang.Tests;

public class BuiltinRuntimeParityTests
{
    public static TheoryData<string, string, string, int, int> CollectionBuiltinArityDiagnosticCases => new()
    {
        { "map()", "map(collection, mapper)", "Callable `map(collection, mapper)` expects 2 arguments, but was called with 0 arguments.", 2, 0 },
        { "take()", "take(collection, count)", "Callable `take(collection, count)` expects 2 arguments, but was called with 0 arguments.", 2, 0 },
        { "skip()", "skip(collection, count)", "Callable `skip(collection, count)` expects 2 arguments, but was called with 0 arguments.", 2, 0 },
        { "reduce(1)", "reduce(collection, reducer, initial)", "Callable `reduce(collection, reducer, initial)` expects 3 arguments, but was called with 1 argument.", 3, 1 },
        { "sum()", "sum(collection)", "Callable `sum(collection)` expects 1 argument, but was called with 0 arguments.", 1, 0 },
        { "count(1, 2, 3)", "count(collection)", "Callable `count(collection)` expects 1 argument, but was called with 3 arguments.", 1, 3 },
    };

    public static TheoryData<BuiltinId> RequireNonEmptyCollectionBuiltinCases => new()
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
    [MemberData(nameof(CollectionBuiltinArityDiagnosticCases))]
    public void CollectionBuiltinArityDiagnostics_UseOrdinaryFixedSignatureDisplay(
        string source,
        string signatureDisplay,
        string expectedMessage,
        int expected,
        int actual)
    {
        var error = AssertEvalFails(source, out var message);

        // Collection builtins are ordinary fixed-arity callables, so their
        // arity diagnostics use the same style as every other fixed builtin.
        Assert.Equal(expectedMessage, message);

        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal(expected, arity.Expected);
        Assert.Equal(actual, arity.Actual);
        Assert.NotNull(arity.Signature);
        Assert.Equal(signatureDisplay, arity.Signature.DisplayText);
    }

    [Fact]
    public void CollectionBuiltinValidArity_TakeCollectionAndCount()
        // take returns one exact list value [1, 2]; the host-boundary
        // flattening in AssertEval sees its two items.
        => AssertEval("take((1, 2, 3), 2)", 1, 2);

    [Fact]
    public void CollectionBuiltinControlKindDiagnostics_UseDescriptorName()
    {
        var error = AssertEvalFails("""
            take((1, 2), 'x')
            """, out var message);

        Assert.Contains("take count must be exactly one whole-number value", message, StringComparison.Ordinal);
        Assert.IsType<EvalError.BadArity>(Innermost(error));
    }

    [Theory]
    [MemberData(nameof(RequireNonEmptyCollectionBuiltinCases))]
    public void CollectionBuiltinEmptyPolicyMetadata_MatchesRuntimeDiagnostics(BuiltinId builtinId)
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
        // count(item) is 1 per scalar item, so the result is the list [1, 1, 1].
        => AssertEval("map((1, 2, 3), count)", 1, 1, 1);

    [Fact]
    public void Eval_Filter_CollectionBuiltinAsPredicate_RejectsListResult()
    {
        // A collection-producing builtin returns one exact LIST per item, and
        // lists have no truth value, so the strict predicate contract rejects it.
        var error = AssertEvalFails("filter((0, 1, 2), distinct)", out var message);

        Assert.Contains("filter predicate must return exactly one atomic numeric value", message, StringComparison.Ordinal);
        Assert.IsType<EvalError.BadArity>(Innermost(error));
    }

    [Fact]
    public void Eval_Filter_ScalarBuiltinAsPredicate_AppliesPerItem()
        // sum(item) is one atomic numeric value per item, so the predicate
        // keeps the truthy items: filter((0, 1, 2), sum) = [1, 2].
        => AssertEval("filter((0, 1, 2), sum)", 1, 2);

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

        return Evaluator.Run(new Expr.AlgorithmExpr(parseResult.Root));
    }

    private static EvalResult<Result> EvalBuiltinCall(BuiltinId builtinId, params Expr[] arguments)
    {
        OutputBundle argumentBundle = arguments;
        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [],
            Output: [new Expr.Call(new Expr.AlgorithmExpr(new Algorithm.Builtin(builtinId)), argumentBundle)]);

        return Evaluator.Run(new Expr.AlgorithmExpr(root));
    }

    private static void AssertEval(string source, params decimal[] expected)
    {
        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        // Host-boundary flattening (ToHostAtoms) opens list results too, so
        // flat expectations cover exact-list builtin results.
        Assert.Equal(expected, result.Value.ToHostAtoms());
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