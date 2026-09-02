using KatLang.Evaluation;
using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

/// <summary>
/// Shared, stateless helpers for the evaluator test classes: the former private helpers of the single
/// <c>EvaluatorTests</c> class, imported by each split class through <c>using static</c> so test bodies
/// call them unqualified exactly as before. Every member is static and pure over its arguments (no
/// shared mutable state), which keeps the split classes eligible for xUnit class-level parallelism.
/// <c>ParseValidRoot</c> is the strict-source helper sanctioned by AGENTS.md beside
/// <see cref="SourceProvenance.ParseValid"/>.
/// </summary>
internal static class EvaluatorTestSupport
{
    // Must match the constant the Math prelude serves (Decimal128's own
    // correctly-rounded 34-digit value).
    internal static readonly Decimal128 KatPi = Decimal128.Pi;

    /// <summary>
    /// STRICT-SOURCE: parses, REQUIRES a clean front end, then evaluates.
    ///
    /// <para>
    /// Track 13: these helpers previously took <c>Parser.Parse(source).Root</c>
    /// and discarded <c>Diagnostics</c>, so a test whose source the parser
    /// rejected still evaluated the recovery tree and could pass on an
    /// unrelated failure — which is exactly how a test named for the
    /// <c>NotPublicProperty</c> evaluator branch passed without ever reaching
    /// it. Tests that intend malformed source must not use these helpers; see
    /// <see cref="SourceProvenance.ParseAllowingDiagnostics"/>.
    /// </para>
    /// </summary>
    internal static Algorithm ParseValidRoot(string source)
    {
        var parsed = Parser.Parse(source);
        if (parsed.HasErrors)
        {
            Assert.Fail(
                "Evaluator test source must parse and elaborate cleanly, but the front end reported:"
                + Environment.NewLine
                + string.Join(Environment.NewLine, parsed.Diagnostics.Select(d => "  - " + d.Message.Split('\n')[0]))
                + Environment.NewLine + "Source:" + Environment.NewLine + source);
        }

        return parsed.Root;
    }

    internal static EvalResult<IReadOnlyList<Decimal128>> Eval(string source)
        => Evaluator.RunFlat(new Expr.AlgorithmExpr(ParseValidRoot(source)));

    internal static EvalResult<IReadOnlyList<Decimal128>> Eval(string source, bool enableLoopOptimization)
    {
        var full = EvalFull(source, enableLoopOptimization);
        return full.IsError
            ? full.Error
            : EvalResult<IReadOnlyList<Decimal128>>.Ok(full.Value.ToHostAtoms());
    }

    /// <summary>
    /// Evaluate after marking all parsed properties as public.
    /// Used by tests that need open visibility on user-defined modules
    /// (since all parsed properties default to private).
    /// </summary>
    internal static EvalResult<IReadOnlyList<Decimal128>> EvalAllPublic(string source)
    {
        var ast = ParseValidRoot(source);
        return Evaluator.RunFlat(new Expr.AlgorithmExpr(MakeAllPublic(ast)));
    }

    /// <summary>
    /// Recursively marks all properties in an algorithm tree as IsPublic = true.
    /// </summary>
    internal static Algorithm MakeAllPublic(Algorithm alg) => alg switch
    {
        Algorithm.User => alg with
        {
            Properties = alg.Properties.Select(p =>
                new Property(p.Name, MakeAllPublic(p.Value), IsPublic: true, Exposure: p.Exposure)).ToList(),
            Output = alg.Output.Select(MakeAllPublicExpr).ToList(),
            Opens = alg.Opens.Select(MakeAllPublicExpr).ToList(),
        },
        _ => alg,
    };

    internal static Expr MakeAllPublicExpr(Expr expr) => expr switch
    {
        Expr.AlgorithmExpr(var a) => new Expr.AlgorithmExpr(MakeAllPublic(a)) { Span = expr.Span },
        Expr.Capture(var captureBody) => new Expr.Capture(new OutputBundle(
            captureBody.Select(MakeAllPublicExpr).ToList()))
        { Span = expr.Span },
        Expr.Call(var f, var args) => new Expr.Call(MakeAllPublicExpr(f), MakeAllPublicArgs(args)) { Span = expr.Span },
        Expr.DotCall dotCall => dotCall with
        {
            Target = MakeAllPublicExpr(dotCall.Target),
            Args = dotCall.Args is { } dotArgs ? MakeAllPublicArgs(dotArgs) : null,
        },
        Expr.Binary(var op, var l, var r) => new Expr.Binary(op, MakeAllPublicExpr(l), MakeAllPublicExpr(r)) { Span = expr.Span },
        Expr.Unary(var op, var o) => new Expr.Unary(op, MakeAllPublicExpr(o)) { Span = expr.Span },
        Expr.Index(var t, var s) => new Expr.Index(MakeAllPublicExpr(t), MakeAllPublicExpr(s)) { Span = expr.Span },
        Expr.SequenceConstruct(var l, var r) => new Expr.SequenceConstruct(MakeAllPublicExpr(l), MakeAllPublicExpr(r)) { Span = expr.Span },
        Expr.SequenceSpread(var operand) => new Expr.SequenceSpread(MakeAllPublicExpr(operand)) { Span = expr.Span },
        Expr.ListLiteral(var items) => new Expr.ListLiteral(items.Select(MakeAllPublicExpr).ToList()) { Span = expr.Span },
        _ => expr,
    };

    internal static OutputBundle MakeAllPublicArgs(OutputBundle args)
        => new(args.Select(MakeAllPublicExpr).ToList());

    internal static void AssertEval(string source, params Decimal128[] expected)
    {
        var result = Eval(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal(expected, result.Value);
    }


    internal static void AssertEvalLoopModes(string source, params Decimal128[] expected)
    {
        var generic = Eval(source, enableLoopOptimization: false);
        if (generic.IsError)
            Assert.Fail($"Expected generic success but got error: {generic.Error}");
        Assert.Equal(expected, generic.Value);

        var optimized = Eval(source, enableLoopOptimization: true);
        if (optimized.IsError)
            Assert.Fail($"Expected optimized success but got error: {optimized.Error}");
        Assert.Equal(expected, optimized.Value);
    }

    internal static Result ResultFromAtoms(params Decimal128[] expected)
        => Result.FromItems(expected.Select(static number => new Result.Atom(number)));

    internal static Result Atom(decimal value) => new Result.Atom(value);

    internal static Result SequenceValue(params Result[] items) => new Result.SequenceValue(items);

    internal static Result ListValue(params Result[] items) => new Result.ListValue(items);

    internal static void AssertEvalCounted(string source, int expectedEmittedCount, Result expectedValue)
    {
        var parseResult = Parser.Parse(source);
        if (parseResult.HasErrors)
        {
            var message = string.Join(Environment.NewLine, parseResult.Diagnostics.Select(static diagnostic => diagnostic.Message));
            Assert.Fail($"Expected parse success but got diagnostics:{Environment.NewLine}{message}");
        }

        var result = Evaluator.RunCounted(new Expr.AlgorithmExpr(parseResult.Root));
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal(expectedEmittedCount, result.Value.EmittedCount);
        Assert.True(
            Result.ValueComparer.Equals(expectedValue, result.Value.Value),
            $"Expected {expectedValue} but got {result.Value.Value}");
    }

    internal static void AssertEvalResultLoopModes(string source, Result expected)
    {
        var generic = EvalFull(source, enableLoopOptimization: false);
        if (generic.IsError)
            Assert.Fail($"Expected generic success but got error: {generic.Error}");
        Assert.True(Result.ValueComparer.Equals(expected, generic.Value), $"Expected {expected} but got {generic.Value}");

        var optimized = EvalFull(source, enableLoopOptimization: true);
        if (optimized.IsError)
            Assert.Fail($"Expected optimized success but got error: {optimized.Error}");
        Assert.True(Result.ValueComparer.Equals(expected, optimized.Value), $"Expected {expected} but got {optimized.Value}");
    }

    internal static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        return error;
    }

    internal static void AssertEvalEmptyOutput(string source)
    {
        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var group = Assert.IsType<Result.SequenceValue>(result.Value);
        Assert.Empty(group.Items);
    }

    internal static void AssertEvalApprox(string source, Decimal128 expected, int decimalPlaces = 10)
    {
        var result = Eval(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Single(result.Value);
        AssertApproximatelyEqual(expected, result.Value[0], decimalPlaces);
    }

    /// <summary>
    /// Tolerance comparison for transcendental results: Decimal128's math is high
    /// precision but not guaranteed correctly rounded, so expectations allow half a
    /// unit in the asserted decimal place (the same contract xunit's decimal
    /// precision overload expressed for the old representation).
    /// </summary>
    internal static void AssertApproximatelyEqual(Decimal128 expected, Decimal128 actual, int decimalPlaces)
    {
        var tolerance = Decimal128.ScaleB(Decimal128.One, -decimalPlaces) / 2;
        Assert.True(
            Decimal128.Abs(expected - actual) <= tolerance,
            $"Expected {actual} to equal {expected} within {decimalPlaces} decimal places.");
    }

    internal static void AssertEvalAllPublic(string source, params Decimal128[] expected)
    {
        var result = EvalAllPublic(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal(expected, result.Value);
    }

    internal static void AssertEvalFails(string source)
    {
        var result = Eval(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: [{string.Join(", ", result.Value)}]");
    }

    internal static EvalError.ArityMismatch AssertEvalFailsWithArityMismatch(
        string source,
        int expected,
        int actual)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected ArityMismatch error but got: {result.Value}");

        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
        Assert.Equal(expected, arity.Expected);
        Assert.Equal(actual, arity.Actual);
        return arity;
    }

    internal static void AssertEvalFailsWithMissingOutput(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        AssertInnermostMissingOutput(result.Error);
    }

    internal static void AssertEvalFailsWithTypeMismatch(string source, string expectedSubstring)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected TypeMismatch error but got: {result.Value}");
        var error = result.Error;
        // Unwrap WithContext as needed
        while (error is EvalError.WithContext wc)
            error = wc.Inner;
        var tm = Assert.IsType<EvalError.TypeMismatch>(error);
        Assert.Contains(expectedSubstring, tm.Message);
    }

    internal static void AssertEvalFailsWithIllegalInEval(string source, string expectedSubstring)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected IllegalInEval error but got: {result.Value}");
        var error = result.Error;
        while (error is EvalError.WithContext wc)
            error = wc.Inner;
        var illegal = Assert.IsType<EvalError.IllegalInEval>(error);
        Assert.Contains(expectedSubstring, illegal.Reason);
    }

    internal static EvalResult<Result> EvalFull(string source)
    {
        var ast = ParseValidRoot(source);
        return Evaluator.Run(new Expr.AlgorithmExpr(ast));
    }

    internal static EvalResult<Result> EvalFull(string source, bool enableLoopOptimization)
    {
        var ast = ParseValidRoot(source);
        return Evaluator.Run(
            new Expr.AlgorithmExpr(ast),
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization);
    }

    internal static EvalResult<Result> EvalFull(
        string source,
        bool enableLoopOptimization,
        bool enableSequencePipelineOptimization)
    {
        var ast = ParseValidRoot(source);
        return Evaluator.Run(
            new Expr.AlgorithmExpr(ast),
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: enableSequencePipelineOptimization,
            sequenceDiagnostics: null);
    }

    internal static void AssertEvalSequenceModes(string source, params Decimal128[] expected)
    {
        var generic = EvalFull(
            source,
            enableLoopOptimization: true,
            enableSequencePipelineOptimization: false);
        if (generic.IsError)
            Assert.Fail($"Expected generic sequence success but got error: {generic.Error}");
        Assert.Equal(expected, generic.Value.ToHostAtoms());

        var optimized = EvalFull(
            source,
            enableLoopOptimization: true,
            enableSequencePipelineOptimization: true);
        if (optimized.IsError)
            Assert.Fail($"Expected optimized sequence success but got error: {optimized.Error}");
        Assert.Equal(expected, optimized.Value.ToHostAtoms());
    }

    internal static void AssertEvalResultSequenceModes(string source, Result expected)
    {
        var generic = EvalFull(
            source,
            enableLoopOptimization: true,
            enableSequencePipelineOptimization: false);
        if (generic.IsError)
            Assert.Fail($"Expected generic sequence success but got error: {generic.Error}");
        Assert.True(Result.ValueComparer.Equals(expected, generic.Value), $"Expected {expected} but got {generic.Value}");

        var optimized = EvalFull(
            source,
            enableLoopOptimization: true,
            enableSequencePipelineOptimization: true);
        if (optimized.IsError)
            Assert.Fail($"Expected optimized sequence success but got error: {optimized.Error}");
        Assert.True(Result.ValueComparer.Equals(expected, optimized.Value), $"Expected {expected} but got {optimized.Value}");
    }

    internal static void AssertEvalString(string source, string expected)
    {
        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        var str = Assert.IsType<Result.Str>(result.Value);
        Assert.Equal(expected, str.Value);
    }

    internal static EvalError? GetEvalError(string source)
    {
        var result = Eval(source);
        return result.IsError ? result.Error : null;
    }

    internal static void AssertArityMismatchMessage(string source, string expectedMessage)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Equal(expectedMessage, formatted);
        Assert.DoesNotContain("while evaluating", formatted);
    }

    /// <summary>
    /// Wraps one expression in a CLOSED explicit-parameter probe so a dot
    /// edge's unresolvable member reaches the RUNTIME lookup.
    ///
    /// Implicit parameter inference includes a dot edge's lexical fallback
    /// whenever that fallback may be selected, so at root (or in any
    /// implicitly parameterized body) an unresolvable member name becomes an
    /// implicit parameter instead. A closed explicit parameter list asks the
    /// DEFINITE question and takes no fallback contribution — the MAY vs MUST
    /// distinction — so the member stays a lexical name and its runtime miss
    /// stays observable.
    /// </summary>
    internal static string ClosedMemberProbe(string definitions, string expression)
        => $"{definitions}Probe(probeInput) = {expression}\nProbe(0)";

    internal static void AssertUnknownDotMember(string source, string expectedName)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        // Skip the probe's outer call frame to reach the dot edge's own context.
        var error = result.Error;
        while (error is EvalError.WithContext { Inner: EvalError.WithContext nested })
            error = nested;

        var contextual = Assert.IsType<EvalError.WithContext>(error);
        var unresolved = Assert.IsType<EvalError.UnknownName>(contextual.Inner);
        Assert.Equal(expectedName, unresolved.Name);
    }

    internal static void AssertLocalOnlyPropertyMessage(string source, string expectedMessage)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Equal(expectedMessage, formatted);
        Assert.DoesNotContain("while evaluating", formatted);

        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;

        Assert.IsType<EvalError.LocalOnlyProperty>(error);
    }

    internal static void AssertInnermostMissingOutput(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        Assert.IsType<EvalError.MissingOutput>(error);
    }

    internal static void AssertMissingOutputMessage(
        string source,
        string expectedMessage,
        int? expectedLine = null,
        int? expectedColumn = null)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        AssertInnermostMissingOutput(result.Error);

        var formatted = KatLangError.FromEvalError(result.Error);
        Assert.Equal(expectedMessage, formatted.Message);
        Assert.DoesNotContain("while evaluating", formatted.Message);

        if (expectedLine is not null)
            Assert.Equal(expectedLine, formatted.StartLine);
        if (expectedColumn is not null)
            Assert.Equal(expectedColumn, formatted.StartColumn);
    }

    internal static void AssertSequenceValueAtoms(Result value, params Decimal128[] expected)
    {
        var group = Assert.IsType<Result.SequenceValue>(value);
        Assert.Equal(expected.Length, group.Items.Count);

        for (var i = 0; i < expected.Length; i++)
            Assert.Equal(expected[i], Assert.IsType<Result.Atom>(group.Items[i]).Value);
    }

    /// <summary>
    /// Asserts that <paramref name="value"/> is an exact list value whose
    /// elements are sequence values with the given atom contents — the shape
    /// collection-producing builtins return for kept sequence-valued items.
    /// </summary>
    internal static void AssertListOfSequenceValueAtoms(Result value, params Decimal128[][] expectedGroups)
    {
        var outer = Assert.IsType<Result.ListValue>(value);
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

    internal static void AssertAtomValue(Result value, decimal expected)
        => Assert.Equal(expected, Assert.IsType<Result.Atom>(value).Value);
}
