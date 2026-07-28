using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

public class EvaluatorTests
{
    // Must match the high-precision literals in Evaluator.MathAlgorithm.
    private const decimal KatPi = 3.1415926535897932384626433833m;
    private const decimal KatE  = 2.7182818284590452353602874714m;

    private static EvalResult<IReadOnlyList<decimal>> Eval(string source)
    {
        var ast = Parser.Parse(source).Root;
        return Evaluator.RunFlat(new Expr.Block(ast));
    }

    private static EvalResult<IReadOnlyList<decimal>> Eval(string source, bool enableLoopOptimization)
    {
        var full = EvalFull(source, enableLoopOptimization);
        return full.IsError
            ? full.Error
            : EvalResult<IReadOnlyList<decimal>>.Ok(full.Value.ToHostAtoms());
    }

    /// <summary>
    /// Evaluate after marking all parsed properties as public.
    /// Used by tests that need open visibility on user-defined modules
    /// (since all parsed properties default to private).
    /// </summary>
    private static EvalResult<IReadOnlyList<decimal>> EvalAllPublic(string source)
    {
        var ast = Parser.Parse(source).Root;
        return Evaluator.RunFlat(new Expr.Block(MakeAllPublic(ast)));
    }

    /// <summary>
    /// Recursively marks all properties in an algorithm tree as IsPublic = true.
    /// </summary>
    private static Algorithm MakeAllPublic(Algorithm alg) => alg switch
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

    private static Expr MakeAllPublicExpr(Expr expr) => expr switch
    {
        Expr.Block(var a) => new Expr.Block(MakeAllPublic(a)) { Span = expr.Span },
        Expr.Call(var f, var args) => new Expr.Call(MakeAllPublicExpr(f), MakeAllPublic(args)) { Span = expr.Span },
        Expr.DotCall(var t, var n, var da) => new Expr.DotCall(
            MakeAllPublicExpr(t), n, da is not null ? MakeAllPublic(da) : null) { Span = expr.Span },
        Expr.Binary(var op, var l, var r) => new Expr.Binary(op, MakeAllPublicExpr(l), MakeAllPublicExpr(r)) { Span = expr.Span },
        Expr.Unary(var op, var o) => new Expr.Unary(op, MakeAllPublicExpr(o)) { Span = expr.Span },
        Expr.Index(var t, var s) => new Expr.Index(MakeAllPublicExpr(t), MakeAllPublicExpr(s)) { Span = expr.Span },
        Expr.SequenceConstruct(var l, var r) => new Expr.SequenceConstruct(MakeAllPublicExpr(l), MakeAllPublicExpr(r)) { Span = expr.Span },
        Expr.SequenceSpread(var operand) => new Expr.SequenceSpread(MakeAllPublicExpr(operand)) { Span = expr.Span },
        Expr.ListLiteral(var items) => new Expr.ListLiteral(items.Select(MakeAllPublicExpr).ToList()) { Span = expr.Span },
        _ => expr,
    };

    private static void AssertEval(string source, params decimal[] expected)
    {
        var result = Eval(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal(expected, result.Value);
    }


    private static void AssertEvalLoopModes(string source, params decimal[] expected)
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

    private static Result ResultFromAtoms(params decimal[] expected)
        => Result.FromItems(expected.Select(static number => new Result.Atom(number)));

    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result SequenceValue(params Result[] items) => new Result.SequenceValue(items);

    private static Result ListValue(params Result[] items) => new Result.ListValue(items);

    private static void AssertEvalCounted(string source, int expectedEmittedCount, Result expectedValue)
    {
        var parseResult = Parser.Parse(source);
        if (parseResult.HasErrors)
        {
            var message = string.Join(Environment.NewLine, parseResult.Diagnostics.Select(static diagnostic => diagnostic.Message));
            Assert.Fail($"Expected parse success but got diagnostics:{Environment.NewLine}{message}");
        }

        var result = Evaluator.RunCounted(new Expr.Block(parseResult.Root));
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal(expectedEmittedCount, result.Value.EmittedCount);
        Assert.True(
            Result.ValueComparer.Equals(expectedValue, result.Value.Value),
            $"Expected {expectedValue} but got {result.Value.Value}");
    }

    private static void AssertEvalResultLoopModes(string source, Result expected)
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

    private static (EvalError Generic, EvalError Optimized) AssertEvalFailsInBothLoopModes(string source)
    {
        var generic = EvalFull(source, enableLoopOptimization: false);
        if (generic.IsOk)
            Assert.Fail($"Expected generic evaluation failure but got: {generic.Value}");

        var optimized = EvalFull(source, enableLoopOptimization: true);
        if (optimized.IsOk)
            Assert.Fail($"Expected optimized evaluation failure but got: {optimized.Value}");

        Assert.Equal(
            KatLangError.FromEvalError(generic.Error).Message,
            KatLangError.FromEvalError(optimized.Error).Message);

        return (generic.Error, optimized.Error);
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        return error;
    }

    private static void AssertEvalEmptyOutput(string source)
    {
        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var group = Assert.IsType<Result.SequenceValue>(result.Value);
        Assert.Empty(group.Items);
    }

    private static void AssertEvalApprox(string source, decimal expected, int precision = 10)
    {
        var result = Eval(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Single(result.Value);
        Assert.Equal(expected, result.Value[0], precision);
    }

    private static void AssertEvalAllPublic(string source, params decimal[] expected)
    {
        var result = EvalAllPublic(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal(expected, result.Value);
    }

    private static void AssertEvalFails(string source)
    {
        var result = Eval(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: [{string.Join(", ", result.Value)}]");
    }

    private static EvalError.ArityMismatch AssertEvalFailsWithArityMismatch(
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

    private static void AssertEvalFailsWithMissingOutput(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        AssertInnermostMissingOutput(result.Error);
    }

    private static void AssertEvalFailsWithTypeMismatch(string source, string expectedSubstring)
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

    private static void AssertNumericScalarOperandFailure(string source, params string[] expectedSubstrings)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected numeric scalar operand failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        foreach (var expectedSubstring in expectedSubstrings)
            Assert.Contains(expectedSubstring, formatted);
        Assert.DoesNotContain("Bad arity", formatted);

        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;

        Assert.IsType<EvalError.TypeMismatch>(error);
    }

    private static void AssertEvalFailsWithIllegalInEval(string source, string expectedSubstring)
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

    private static EvalResult<Result> EvalFull(string source)
    {
        var ast = Parser.Parse(source).Root;
        return Evaluator.Run(new Expr.Block(ast));
    }

    private static EvalResult<Result> EvalFull(string source, bool enableLoopOptimization)
    {
        var ast = Parser.Parse(source).Root;
        return Evaluator.Run(
            new Expr.Block(ast),
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization);
    }

    private static EvalResult<Result> EvalFull(
        string source,
        bool enableLoopOptimization,
        bool enableSequencePipelineOptimization)
    {
        var ast = Parser.Parse(source).Root;
        return Evaluator.Run(
            new Expr.Block(ast),
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: enableSequencePipelineOptimization,
            sequenceDiagnostics: null);
    }

    private static (EvalResult<Result> Result, LoopOptimizationDiagnosticsSnapshot Stats) EvalFullWithLoopDiagnostics(
        string source,
        bool enableLoopOptimization = true)
    {
        var ast = Parser.Parse(source).Root;
        var diagnostics = new LoopOptimizationDiagnostics();
        var result = Evaluator.Run(
            new Expr.Block(ast),
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization,
            diagnostics);
        return (result, diagnostics.GetSnapshot());
    }

    private static (EvalResult<Result> Result, SequencePipelineDiagnosticsSnapshot Stats) EvalFullWithSequenceDiagnostics(
        string source,
        bool enableSequencePipelineOptimization = true)
    {
        var ast = Parser.Parse(source).Root;
        var diagnostics = new SequencePipelineDiagnostics();
        var result = Evaluator.Run(
            new Expr.Block(ast),
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: enableSequencePipelineOptimization,
            sequenceDiagnostics: diagnostics);
        return (result, diagnostics.GetSnapshot());
    }

    // A root evaluation context whose call stack is the runtime prelude, so
    // builtin names (count, filter, range, ...) resolve to builtins — matching
    // the context Evaluator.Run installs. White-box optimizer tests that call
    // SequencePipelineOptimizer.TryExecute directly for a DOT pipeline need this
    // because the dot-form CountResolvesToBuiltin check resolves `count` by name
    // (unlike the plain form, which carries an explicit builtin callee).
    private static Evaluator.EvalCtx PreludeEvalCtx()
        => new(
            [BuiltinRegistry.CreateRuntimePreludeAlgorithm()],
            [],
            [],
            UncachedZeroArgPropertyResultCache.Instance,
            UncachedDeconstructionBindingCache.Instance,
            EnableLoopOptimization: true,
            LoopDiagnostics: null,
            EnableSequencePipelineOptimization: true,
            SequenceDiagnostics: null,
            Observations: null,
            Budget: EvaluationBudget.Create(null));

    private static (
        EvalResult<Result> Result,
        LoopOptimizationDiagnosticsSnapshot LoopStats,
        SequencePipelineDiagnosticsSnapshot SequenceStats) EvalFullWithOptimizationDiagnostics(
            string source,
            bool enableLoopOptimization = true,
            bool enableSequencePipelineOptimization = true)
    {
        var ast = Parser.Parse(source).Root;
        var loopDiagnostics = new LoopOptimizationDiagnostics();
        var sequenceDiagnostics = new SequencePipelineDiagnostics();
        var result = Evaluator.Run(
            new Expr.Block(ast),
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization,
            loopDiagnostics,
            enableSequencePipelineOptimization,
            sequenceDiagnostics);
        return (result, loopDiagnostics.GetSnapshot(), sequenceDiagnostics.GetSnapshot());
    }

    private static void AssertEvalSequenceModes(string source, params decimal[] expected)
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

    private static void AssertEvalResultSequenceModes(string source, Result expected)
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

    private static string YellowstoneSource(string finalExpression) =>
        $$"""
          GcdStep = b~, a mod b, a mod b != 0
          Gcd = GcdStep.while(a, b):1

          FindNext(history..., pre1, pre2) = {
              IsYSCandidate = not history.contains(candidate) and
                  Gcd(candidate, pre1) == 1 and Gcd(candidate, pre2) != 1
              FindStep = candidate + 1, not IsYSCandidate
              FindStep.while(1):0
          }
          YSStep((history...), pre2, pre1) = {
              Next = FindNext(history.spread, pre1, pre2)
              (history.spread, Next), pre1, Next
          }
          {{finalExpression}}
          """;

    private static LoopPlanDiagnosticSnapshot AssertSingleLoopPlan(
        LoopOptimizationDiagnosticsSnapshot stats,
        string identity)
    {
        var plan = Assert.Single(stats.LoopPlans, plan => plan.Identity == identity);
        Assert.True(plan.Optimized, $"Expected optimized loop plan for {identity}, got fallback: {plan.FallbackReason}");
        return plan;
    }

    private static LoopExpressionDiagnosticSnapshot AssertLoopExpression(
        LoopPlanDiagnosticSnapshot plan,
        string role,
        int? index)
        => Assert.Single(
            plan.Expressions,
            expression => expression.Role == role && expression.Index == index);

    private static LoopTempDiagnosticSnapshot AssertLoopTemp(
        LoopPlanDiagnosticSnapshot plan,
        string name)
        => Assert.Single(
            plan.Temps,
            temp => temp.Name == name);

    private static void AssertEvalString(string source, string expected)
    {
        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        var str = Assert.IsType<Result.Str>(result.Value);
        Assert.Equal(expected, str.Value);
    }

    private static void AssertEvalAllPublicFails(string source)
    {
        var result = EvalAllPublic(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: [{string.Join(", ", result.Value)}]");
    }

    private static EvalError? GetEvalError(string source)
    {
        var result = Eval(source);
        return result.IsError ? result.Error : null;
    }

    private static void AssertArityMismatchMessage(string source, string expectedMessage)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Equal(expectedMessage, formatted);
        Assert.DoesNotContain("while evaluating", formatted);
    }

    private static void AssertUnknownDotMember(string source, string expectedName)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var contextual = Assert.IsType<EvalError.WithContext>(result.Error);
        var unresolved = Assert.IsType<EvalError.UnknownName>(contextual.Inner);
        Assert.Equal(expectedName, unresolved.Name);
    }

    private static void AssertLocalOnlyPropertyMessage(string source, string expectedMessage)
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

    private static void AssertInnermostMissingOutput(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        Assert.IsType<EvalError.MissingOutput>(error);
    }

    private static void AssertSpreadMissingOutput(
        string source,
        int expectedStartLine,
        int expectedStartColumn,
        int expectedEndLine,
        int expectedEndColumn)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Equal(
            $"Cannot spread because the spread operand has no defined output.\nUse `spread(())` if you intended to spread zero items.",
            formatted);

        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;

        var spreadError = Assert.IsType<EvalError.SpreadMissingOutput>(error);
        var span = spreadError.Span;
        Assert.NotNull(span);
        Assert.Equal(expectedStartLine, span!.StartLineNumber);
        Assert.Equal(expectedStartColumn, span.StartColumn);
        Assert.Equal(expectedEndLine, span.EndLineNumber);
        Assert.Equal(expectedEndColumn, span.EndColumn);
    }

    private static void AssertInnermostSpecialOutputAccess(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        Assert.IsType<EvalError.SpecialOutputAccess>(error);
    }

    private static void AssertMissingOutputMessage(
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

    private static void AssertFilterPredicateShapeFails(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("filter predicate must return exactly one atomic numeric value", formatted);

        var error = result.Error;
        var contexts = new List<string>();
        while (error is EvalError.WithContext wc)
        {
            contexts.Add(wc.Context);
            error = wc.Inner;
        }

        Assert.Contains(contexts, context => context.Contains("filter predicate must return exactly one atomic numeric value"));
        Assert.IsType<EvalError.BadArity>(error);
    }

    private static void AssertReduceStepShapeFails(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("reduce step must return a single accumulator value", formatted);

        var error = result.Error;
        var contexts = new List<string>();
        while (error is EvalError.WithContext wc)
        {
            contexts.Add(wc.Context);
            error = wc.Inner;
        }

        Assert.Contains(contexts, context => context.Contains("reduce step must return a single accumulator value"));
        Assert.IsType<EvalError.BadArity>(error);
    }

    private static void AssertMapTransformShapeFails(string source)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("map transform must return a single element", formatted);

        var error = result.Error;
        var contexts = new List<string>();
        while (error is EvalError.WithContext wc)
        {
            contexts.Add(wc.Context);
            error = wc.Inner;
        }

        Assert.Contains(contexts, context => context.Contains("map transform must return a single element"));
        Assert.IsType<EvalError.BadArity>(error);
    }

    private static void AssertBuiltinFailureWithExactContext(string source, string expectedContext)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains(expectedContext, formatted);

        var error = result.Error;
        var contexts = new List<string>();
        while (error is EvalError.WithContext wc)
        {
            contexts.Add(wc.Context);
            error = wc.Inner;
        }

        Assert.Contains(expectedContext, contexts);
        Assert.IsType<EvalError.BadArity>(error);
    }

    private static void AssertBuiltinFailureWithContext(string source, string expectedContext)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains(expectedContext, formatted);

        var error = result.Error;
        var contexts = new List<string>();
        while (error is EvalError.WithContext wc)
        {
            contexts.Add(wc.Context);
            error = wc.Inner;
        }

        Assert.Contains(contexts, context => context.Contains(expectedContext));
        Assert.IsType<EvalError.BadArity>(error);
    }

    private static void AssertSequenceValueAtoms(Result value, params decimal[] expected)
    {
        var group = Assert.IsType<Result.SequenceValue>(value);
        Assert.Equal(expected.Length, group.Items.Count);

        for (var i = 0; i < expected.Length; i++)
            Assert.Equal(expected[i], Assert.IsType<Result.Atom>(group.Items[i]).Value);
    }

    private static void AssertNestedSequenceValueAtoms(Result value, params decimal[][] expectedGroups)
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

    /// <summary>
    /// Asserts that <paramref name="value"/> is an exact list value whose
    /// elements are sequence values with the given atom contents — the shape
    /// collection-producing builtins return for kept sequence-valued items.
    /// </summary>
    private static void AssertListOfSequenceValueAtoms(Result value, params decimal[][] expectedGroups)
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

    private static void AssertAtomValue(Result value, decimal expected)
        => Assert.Equal(expected, Assert.IsType<Result.Atom>(value).Value);

    [Fact]
    public void Eval_RepeatedEligiblePropertyWithinSingleRun()
    {
        var source = """
            Values = range(1, 5)
            Values.count + Values.count
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([10m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_ClosedLexicalProperty_RemainsCorrectAcrossCallerContexts()
    {
        var source = """
            Measure(values) = {
                Count = values.count
                Count + Count
            }
            Measure((1, 2)) + Measure((3, 4, 5))
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([10m], result.Value.ToAtoms());
    }

    [Fact]
        public void Eval_Distinguishes_SamePropertyTextAcrossReceiverContexts()
    {
        var source = """
                        Left = {
                            Value = 1
                        }
                        Right = {
                            Value = 2
                        }
                        Left.Value + Left.Value + Right.Value + Right.Value
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([6m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_ParameterizedCallResults_RemainDistinct()
    {
        var source = """
            Inc = x + 1
            Inc(1) + Inc(2)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([5m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_RepeatedRuns_AreConsistent()
    {
        var source = """
            Values = range(1, 5)
            Values.count + Values.count
            """;

        var ast = Parser.Parse(source).Root;

        var first = Evaluator.Run(new Expr.Block(ast));
        var second = Evaluator.Run(new Expr.Block(ast));

        if (first.IsError)
            Assert.Fail($"Expected first run success but got error: {first.Error}");
        if (second.IsError)
            Assert.Fail($"Expected second run success but got error: {second.Error}");

        Assert.Equal(first.Value.ToAtoms(), second.Value.ToAtoms());
    }

    [Fact]
    public void Eval_PreservesRecursivePropertyBehavior()
    {
        var source = """
            Recursive = {
              Step = if(n == 0, 0, Step(n - 1))
              Step(4)
            }
            Recursive + Recursive
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([0m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_RecursiveDotCallArgumentUsesCurrentValueBinding()
    {
        // `atoms` now traverses list values directly, so `atoms(values)` on a
        // spread-recaptured list works without a workaround. The explicit
        // spread (`rest = list.skip(1).spread`) is kept because a sequence-shaped
        // recursion argument is what exercises the current-value binding here.
        var source = """
            reduceCollection(values) = {
                list = atoms(values)
                rest = list.skip(1).spread
                if(
                    list.count <= 1,
                    list,
                    rest.reduceCollection
                )
            }
            reduceCollection((1,2,3,4))
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Distinguishes_HigherOrderAlgorithmContexts()
    {
        var source = """
                        Left = {
                            Step = x + 1
                            Value = Step(10)
            }
                        Right = {
                            Step = x + 2
                            Value = Step(10)
                        }
                        Left.Value + Left.Value + Right.Value + Right.Value
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([46m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_Distinguishes_SameLexicalPropertyTextAcrossNestedBindings()
    {
        var source = """
            Outer = {
                Left = {
                    Value = 10
                    Value + Value
                }
                Right = {
                    Value = 20
                    Value + Value
                }
                Left + Right
            }
            Outer
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([60m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_Keeps_CallerBoundZeroParamLexicalProperty_Contextual()
    {
        var shared = new Property(
            "Shared",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Param("x")]));

        var caller = new Property(
            "Caller",
            new Algorithm.User(
                Parent: null,
                Parameters: Algorithm.NormalParameters(["x"]),
                Opens: [],
                Properties: [shared],
                Output:
                [
                    new Expr.Binary(
                        BinaryOp.Add,
                        new Expr.Resolve("Shared"),
                        new Expr.Resolve("Shared"))
                ]));

        var oneArg = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [],
            Output: [new Expr.Num(1)]);

        var twoArg = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [],
            Output: [new Expr.Num(2)]);

        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [caller],
            Output:
            [
                new Expr.Binary(
                    BinaryOp.Add,
                    new Expr.Call(new Expr.Resolve("Caller"), oneArg),
                    new Expr.Call(new Expr.Resolve("Caller"), twoArg))
            ]);

            var result = Evaluator.Run(new Expr.Block(root));
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([6m], result.Value.ToAtoms());
    }

    [Fact]
        public void Eval_SharedBindingAcrossDefinitionScopes_DoesNotContaminateOpenDependentMeaning()
    {
        var sharedClosedBinding = new Property(
            "Shared",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Resolve("Base")])) ;

        var localBaseBinding = new Property(
            "Base",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Num(1)]));

        var openBaseBinding = new Property(
            "Base",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Num(2)]),
            IsPublic: true);

        var libraryBinding = new Property(
            "Lib",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [openBaseBinding],
                Output: []),
            IsPublic: true);

        var structuralWrapperBinding = new Property(
            "StructuralWrapper",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [localBaseBinding, sharedClosedBinding],
                Output:
                [
                    new Expr.Binary(
                        BinaryOp.Add,
                        new Expr.Resolve("Shared"),
                        new Expr.Resolve("Shared"))
                ]));

        var openWrapperBinding = new Property(
            "OpenWrapper",
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [new Expr.Resolve("Lib")],
                Properties: [sharedClosedBinding],
                Output:
                [
                    new Expr.Binary(
                        BinaryOp.Add,
                        new Expr.Resolve("Shared"),
                        new Expr.Resolve("Shared"))
                ]));

        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [libraryBinding, structuralWrapperBinding, openWrapperBinding],
            Output:
            [
                new Expr.Binary(
                    BinaryOp.Add,
                    new Expr.Resolve("StructuralWrapper"),
                    new Expr.Resolve("OpenWrapper"))
            ]);

            var result = Evaluator.Run(new Expr.Block(root));
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal(
            [6m],
            result.Value.ToAtoms());
    }

    // â”€â”€ Numbers â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Number_ReturnsValue()
        => AssertEval("42", 42);

    [Fact]
    public void Eval_NegativeNumber_ReturnsNegatedValue()
        => AssertEval("-5", -5);

    [Fact]
    public void Eval_DoubleNegative_ReturnsPositive()
        => AssertEval("--5", 5);

    [Fact]
    public void Eval_Zero_ReturnsZero()
        => AssertEval("0", 0);

    [Fact]
    public void Eval_LargeNumber_ReturnsCorrectValue()
        => AssertEval("9876543210", 9876543210.0m);

    [Fact]
    public void Eval_FloatingPoint_ReturnsValue()
        => AssertEval("3.14", 3.14m);

    [Fact]
    public void Eval_FloatingPoint_Arithmetic()
    {
        AssertEval("1.5 + 2.5", 4.0m);
        AssertEval("3.0 * 2.5", 7.5m);
    }

    // â”€â”€ Arithmetic â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Addition_ReturnsSum()
        => AssertEval("1 + 2", 3);

    [Fact]
    public void Eval_Subtraction_ReturnsDifference()
        => AssertEval("5 - 3", 2);

    [Fact]
    public void Eval_Multiplication_ReturnsProduct()
        => AssertEval("4 * 3", 12);

    [Fact]
    public void Eval_ChainedAddition_LeftAssociative()
        => AssertEval("10 - 3 - 2", 5);

    [Fact]
    public void Eval_MixedOperations_CorrectPrecedence()
        => AssertEval("1 + 2 * 3", 7);

    [Fact]
    public void Eval_ParenthesesOverridePrecedence()
        => AssertEval("(1 + 2) * 3", 9);

    [Fact]
    public void Eval_ComplexArithmetic()
        => AssertEval("5 * 3 - 2", 13);

    [Fact]
    public void Eval_BinaryMinusWithUnaryMinus()
        => AssertEval("5 - -3", 8);

    [Fact]
    public void Eval_NegativeResult()
        => AssertEval("3 - 10", -7);

    // â”€â”€ Comparisons â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_LessThan_True_Returns1()
        => AssertEval("3 < 5", 1);

    [Fact]
    public void Eval_LessThan_False_Returns0()
        => AssertEval("5 < 3", 0);

    [Fact]
    public void Eval_LessThan_Equal_Returns0()
        => AssertEval("3 < 3", 0);

    [Fact]
    public void Eval_GreaterThan_True_Returns1()
        => AssertEval("5 > 3", 1);

    [Fact]
    public void Eval_GreaterThan_False_Returns0()
        => AssertEval("3 > 5", 0);

    [Fact]
    public void Eval_GreaterThan_Equal_Returns0()
        => AssertEval("3 > 3", 0);

    // â”€â”€ Output lists â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_CommaList_ReturnsMultipleValues()
        => AssertEval("1, 2, 3", 1, 2, 3);

    [Fact]
    public void Eval_CommaListWithExpressions()
        => AssertEval("1 + 1, 2 * 2, 3 - 1", 2, 4, 2);

    [Fact]
    public void Eval_CommaWithSequenceValueRowPreservesStructure()
    {
        AssertEval("1, (2, 3)", 1, 2, 3);
        AssertEvalCounted("1, (2, 3)", 2, Result.FromItems([Atom(1), SequenceValue(Atom(2), Atom(3))]));
    }

    [Fact]
    public void Eval_NewlineSequenceConstructAfterCommaPreservesStructure()
    {
        AssertEval(
            """
            1, 2
            3
            """,
            1,
            2,
            3);
        AssertEvalCounted(
            """
            1, 2
            3
            """,
            3,
            Result.FromItems([Atom(1), Atom(2), Atom(3)]));
    }

    [Fact]
    public void Eval_CommaPackagesMultiOutputPropertyBoundary()
    {
        AssertEval(
            """
            A = 1, 2
            A, 3
            """,
            1,
            2,
            3);
        AssertEvalCounted(
            """
            A = 1, 2
            A, 3
            """,
            2,
            Result.FromItems([SequenceValue(Atom(1), Atom(2)), Atom(3)]));
    }

    [Fact]
    public void Eval_ArithmeticCommaNewlinePreservesCommaAndSequenceStructure()
    {
        AssertEval(
            """
            1 + 2, 2 + 3
            3 + 4
            """,
            3,
            5,
            7);
        AssertEvalCounted(
            """
            1 + 2, 2 + 3
            3 + 4
            """,
            3,
            Result.FromItems([Atom(3), Atom(5), Atom(7)]));
    }

    [Fact]
    public void Eval_CommaPreservesExplicitSequenceValueItem()
        => AssertEvalCounted(
            "(1, 2), 3",
            2,
            Result.FromItems([SequenceValue(Atom(1), Atom(2)), Atom(3)]));

    [Fact]
    public void Eval_ExplicitSequenceValueTripleEmitsOneSequenceValue()
        => AssertEvalCounted(
            "(1, 2, 3)",
            1,
            SequenceValue(Atom(1), Atom(2), Atom(3)));

    // ── Implicit expression-list separator by adjacency ─────────────────────

    [Fact]
    public void Eval_SameLineAdjacency_ConstructsExpressionList()
    {
        AssertEval("1 2", 1, 2);
        AssertEvalCounted("1 2", 2, ResultFromAtoms(1, 2));
    }

    [Theory]
    [InlineData("1 2 3")]
    [InlineData("1\n2\n3")]
    public void Eval_AdjacencyNewline_ConstructExpressionList(string source)
        => AssertEvalCounted(source, 3, ResultFromAtoms(1, 2, 3));

    [Fact]
    public void Eval_ParenthesizedCommaChain_ConstructsSequenceValue()
        => AssertEvalCounted("(1, 2, 3)", 1, ResultFromAtoms(1, 2, 3));

    [Theory]
    [InlineData("1, 2 3")]
    [InlineData("1, (2, 3)")]
    public void Eval_AdjacencyAfterComma_UsesExpressionListStructure(string source)
    {
        if (source.Contains("(2, 3)", StringComparison.Ordinal))
            AssertEvalCounted(source, 2, Result.FromItems([Atom(1), SequenceValue(Atom(2), Atom(3))]));
        else
            AssertEvalCounted(source, 3, ResultFromAtoms(1, 2, 3));
    }

    [Theory]
    [InlineData("(1 2)")]
    [InlineData("((1, 2))")]
    [InlineData("(1\n2)")]
    public void Eval_ParenthesizedAdjacency_EmitsOneSequenceValue(string source)
        => AssertEvalCounted(source, 1, SequenceValue(Atom(1), Atom(2)));

    [Theory]
    [InlineData("(1 2 3)")]
    [InlineData("(1\n2\n3)")]
    [InlineData("((1, 2, 3))")]
    public void Eval_ParenthesizedAdjacencyTriple_EmitsOneSequenceValue(string source)
        => AssertEvalCounted(source, 1, SequenceValue(Atom(1), Atom(2), Atom(3)));

    [Theory]
    [InlineData("X(values...) = values.count\nX(1 2)")]
    [InlineData("X(values...) = values.count\nX (1 2)")]
    public void Eval_CallArgumentAdjacency_BindsAsItemSupply(string source)
        // X(values.spread) consumes an item supply. The adjacency form `1 2` supplies
        // two slots, so the variadic parameter captures two supplied arguments.
        => AssertEval(source, 2);

    [Theory]
    [InlineData("X(values...) = values.count\nX((1, 2))")]
    [InlineData("X(values...) = values.count\nX ((1, 2))")]
    public void Eval_CallArgumentGroupedSequence_SingleVariadicCollectsOneArgument(string source)
        // The call supplies one sequence-valued argument, and the variadic parameter
        // collects the supplied slots as one exact list: [(1, 2)], count 1.
        => AssertEval(source, 1);

    [Fact]
    public void Eval_SingleVariadicWithCollectionOperation_GroupedArgumentIsOneElement()
    {
        // F((1, 2)) supplies one argument: the sequence value (1, 2). The variadic parameter
        // capture collects it as the one-element list [(1, 2)], so x.sum hits the
        // per-element numeric constraint and fails. Only explicit spread opens the
        // call boundary: F((1, 2).spread) supplies two arguments and sums to 3.
        AssertEvalFails(
            """
            F(x...) = x.sum
            F((1, 2))
            """);

        AssertEval(
            """
            F(x...) = x.sum
            F((1, 2).spread)
            """,
            3);
    }

    [Fact]
    public void Eval_FixedCall_InlineSequenceValueArgumentRequiresExplicitSpread()
    {
        AssertEvalFailsWithArityMismatch(
            """
            Add(x, y) = x + y
            Add((1, 2))
            """,
            expected: 2,
            actual: 1);

        AssertEval(
            """
            Add(x, y) = x + y
            Add((1, 2).spread)
            """,
            3);
    }

    [Fact]
    public void Eval_MixedVariadicCall_PlainSequenceArgumentPreservesBoundary()
    {
        AssertEval(
            """
            A = 1, 2
            G(first, rest...) = first.count, rest.count
            G(A)
            """,
            2, 0);

        AssertEval(
            """
            G(first, rest...) = first.count, rest.count
            G((1, 2))
            """,
            2, 0);
    }

    [Fact]
    public void Eval_MixedVariadicCall_ExplicitSpreadOpensSequenceArgument()
    {
        AssertEval(
            """
            A = 1, 2
            G(first, rest...) = first.count, rest.count
            G(A.spread)
            """,
            1, 1);

        AssertEval(
            """
            G(first, rest...) = first.count, rest.count
            G((1, 2).spread)
            """,
            1, 1);
    }

    [Theory]
    [InlineData("Add(a, b) = a + b\nAdd(1 2)")]
    [InlineData("Add(a, b) = a + b\nAdd (1 2)")]
    [InlineData("Add(a, b) = a + b\nAdd((1, 2))")]
    [InlineData("Add(a, b) = a + b\nAdd ((1, 2))")]
    public void Eval_CallArgumentAdjacency_IsImplicitComma(string source)
    {
        if (source.Contains("((1, 2))", StringComparison.Ordinal))
            AssertEvalFailsWithArityMismatch(source, expected: 2, actual: 1);
        else
            AssertEval(source, 3);
    }

    [Theory]
    [InlineData("Add(a, b) = a + b\nAdd(1, 2)")]
    [InlineData("Add(a, b) = a + b\nAdd (1, 2)")]
    public void Eval_CallArgumentComma_RemainsTwoArguments(string source)
        => AssertEval(source, 3);

    // ── Whitespace and newlines before call delimiters ───────────────────────

    [Theory]
    [InlineData("Add = a + b\n2.Add(6)")]
    [InlineData("Add = a + b\n2.Add (6)")]
    public void Eval_DotCallWhitespaceBeforeParen_IsCallContinuation(string source)
        => AssertEval(source, 8);

    [Theory]
    [InlineData("(1, 2, 3).map{n * 2}")]
    [InlineData("(1, 2, 3).map { n * 2 }")]
    public void Eval_CallbackBraceWhitespace_IsCallContinuation(string source)
        => AssertEval(source, 2, 4, 6);

    [Theory]
    [InlineData("Twice(f) = f(1) + f(1)\nTwice{n + 1}")]
    [InlineData("Twice(f) = f(1) + f(1)\nTwice {n + 1}")]
    public void Eval_DirectBraceCallWhitespace_IsCallContinuation(string source)
        => AssertEval(source, 4);

    [Fact]
    public void Eval_ExplicitSeparatorBeforeParen_StillWinsOverCallContinuation()
    {
        // Same-line whitespace before '(' continues the call, so a
        // zero-parameter property called with arguments fails with arity.
        AssertEvalFailsWithArityMismatch("A = 5\nA (1, 2)", expected: 0, actual: 2);

        // A physical newline never continues a closed expression into a
        // call: `A` newline `(1, 2)` becomes two expression-list slots.
        AssertEvalCounted(
            "A = 5\nA\n(1, 2)",
            2,
            Result.FromItems([Atom(5), SequenceValue(Atom(1), Atom(2))]));

        // Comma also keeps the values as separate expression-list slots.
        AssertEvalCounted(
            "A = 5\nA, (1, 2)",
            2,
            Result.FromItems([Atom(5), SequenceValue(Atom(1), Atom(2))]));
    }

    [Theory]
    [InlineData("Add(a, b) = a + b\nAdd\n(1, 2)")]
    public void Eval_NewlineBeforeCallDelimiter_IsExpressionListNotCall(string source)
    {
        // Not the call Add(1, 2): the bare `Add` row fails to resolve its
        // implicit parameters.
        var result = EvalFull(source);
        Assert.True(result.IsError, $"Expected the joined form to fail but got: {(result.IsOk ? result.Value : null)}");
        Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
    }

    [Fact]
    public void Eval_OpenedCallDelimiterSpansLines_RemainsCall()
        => AssertEval("Add(a, b) = a + b\nAdd(\n1, 2\n)", 3);

    [Fact]
    public void Eval_OpenedBraceCallbackSpansLines_RemainsCall()
        => AssertEval("(1, 2, 3).map{\nn * 2\n}", 2, 4, 6);

    [Fact]
    public void Eval_LeadingDotOnNextLine_ContinuesDotCallChain()
        // The newline call boundary is about '(' and '{' only: a '.'-led
        // line still continues the dot-call chain, so method-chain layout
        // keeps working as long as each delimiter follows its member name on
        // the same line.
        => AssertEval("(1, 2, 3)\n.map { n * 2 }\n.sum", 12);

    [Theory]
    [InlineData("Pair = 1, 2\nP = Pair:0\nP")]
    [InlineData("Pair = 1, 2\nP = Pair : 0\nP")]
    public void Eval_SameLineIndexing_SelectsIndexedItem(string source)
        // Same-line whitespace around ':' is insignificant; postfix indexing
        // continues the expression before it.
        => AssertEval(source, 1);

    [Fact]
    public void Eval_ParenLedLineAfterDefinitionBody_DoesNotCreateRecursivePropertyCall()
    {
        // Regression: `A = Identity` newline `(A)` once parsed as
        // `A = Identity(A)`, so evaluating A recursed through itself. The
        // newline ends the body; evaluation terminates with the ordinary
        // unresolved-implicit-parameter error for the bare `Identity` body.
        var result = EvalFull("Identity = x\n\nA = Identity\n(A)\n\nA");

        Assert.True(result.IsError, $"Expected unresolved-parameter failure but got: {(result.IsOk ? result.Value : null)}");
        Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
    }

    [Theory]
    [InlineData("X(values...) = values.count\nX(1, 2 3)")]
    [InlineData("X(values...) = values.count\nX(1, (2, 3))")]
    public void Eval_CallArgumentMixedCommaAndAdjacency_BindsItemSupply(string source)
    {
        // X(values.spread) consumes the item supply. `1, 2 3` is three slots
        // (count 3); `1, (2, 3)` is two slots, the second a grouped value
        // preserved as a sibling (count 2).
        if (source.Contains("(2, 3)", StringComparison.Ordinal))
            AssertEval(source, 2);
        else
            AssertEval(source, 3);
    }

    [Theory]
    [InlineData("A B.spread")]
    [InlineData("A\nB.spread")]
    public void Eval_AdjacencyBeforePostfixSequenceSpread_CreatesExpressionListSlots(string source)
    {
        var program = "A = 1\nB = 2, 3\n" + source;
        AssertEvalCounted(program, 3, ResultFromAtoms(1, 2, 3));
    }

    [Theory]
    [InlineData("X(a b.spread)")]
    [InlineData("X(a\nb.spread)")]
    public void Eval_CallArgumentAdjacencyBeforePostfixSequenceSpread_BindsItemSupply(string source)
    {
        // `a b.spread` is three slots (1, 2, 3); X(values.spread) binds them as one item supply.
        var program = "a = 1\nb = 2, 3\nX(values...) = values.count\n" + source;
        AssertEval(program, 3);
    }

    [Theory]
    [InlineData("X((a, b.spread))")]
    [InlineData("X((a\nb.spread))")]
    public void Eval_SequenceValuePostfixSequenceSpreadInCall_BindsAsOneSequenceValueArgument(string source)
    {
        // Explicit parentheses materialize the spread items into one argument,
        // which the variadic parameter collects as the one-element list [(1, 2, 3)].
        var program = "a = 1\nb = 2, 3\nX(values...) = values.count\n" + source;
        AssertEval(program, 1);
    }

    [Theory]
    [InlineData("A B.spread C")]
    [InlineData("A\nB.spread\nC")]
    public void Eval_MiddlePostfixSequenceSpread_CreatesExpressionListSlots(string source)
    {
        var program = "A = 1\nB = 2, 3\nC = 4\n" + source;
        AssertEvalCounted(program, 4, ResultFromAtoms(1, 2, 3, 4));
    }

    [Theory]
    [InlineData("A, B C.spread")]
    [InlineData("A, B\nC.spread")]
    public void Eval_CommaContributionBeforeJoinedPostfixSequenceSpread_PreservesCommaStructure(string source)
    {
        var program = "A = 1, 2\nB = 3\nC = 4\n" + source;
        AssertEvalCounted(program, 3, Result.FromItems([SequenceValue(Atom(1), Atom(2)), Atom(3), Atom(4)]));
    }

    [Theory]
    [InlineData("F(a, b, c) = a + b + c\nF(1 2, 3.spread)")]
    [InlineData("F(a, b, c) = a + b + c\nF(1\n2, 3.spread)")]
    [InlineData("F(a, b, c) = a + b + c\nF(1, (2, 3).spread)")]
    public void Eval_MixedCommaAndJoinWithSpreadSlot_SpreadAppliesOnlyToItsOperand(string source)
        => AssertEval(source, 6);

    [Fact]
    public void Eval_DefinitionSeparatedCommaSlotSpreadContribution_PreservesCommaStructure()
    {
        var program = "A = 1\nB = 2\nC = 3\n\nA\nP = 9\nB, C.spread";
        AssertEvalCounted(program, 3, ResultFromAtoms(1, 2, 3));
    }

    [Fact]
    public void Eval_DefinitionSeparatedCommaSlotSpreadContributionInCallArguments_PreservesTwoArguments()
    {
        var program = "F(a, b, c) = a + b + c\nA = 1\nB = 2\nC = 3\n\nF(\nA\nP = 9\nB, C.spread\n)";
        AssertEval(program, 6);
    }

    [Fact]
    public void Eval_ExplicitOutputWithSequenceValueComma_EmitsOneSequenceValueOutput()
        => AssertEvalCounted("Output = (1, 3)", 1, ResultFromAtoms(1, 3));

    [Theory]
    [InlineData("A = 10\nA\n-1")]
    [InlineData("A = 10\nA // comment\n-1")]
    public void Eval_CommentDoesNotEnableBinaryContinuationAcrossNewline(string source)
        // Comments are semantically invisible for line boundaries: both
        // forms are the two output rows 10 and -1, never the subtraction 9.
        => AssertEvalCounted(source, 2, ResultFromAtoms(10, -1));

    [Theory]
    [InlineData("F(a, b, c) = a + b + c\nA = 1\nB = 2\nC = 3\nF(\nA.spread B\nP = 9\nC\n)")]
    public void Eval_PostfixSpreadThenLaterOutputInCall_IsOneSequenceValueArgument(string source)
        => AssertEval(source, 6);

    [Theory]
    [InlineData("F(a, b) = a + b\nA = 1\nC = 2\nF(\nA.spread, ()\nP = 9\nC\n)")]
    public void Eval_PostfixSpreadThenEmptyThenLaterOutputInCall_IsOneSequenceValueArgument(string source)
        => AssertEvalFailsWithArityMismatch(source, expected: 2, actual: 3);

    [Theory]
    [InlineData("F(a, b) = a + b\nA = 1\nC = 2\nF(\nA.spread\nP = 9\nC\n)")]
    public void Eval_PostfixSpreadThenLaterOutputInCall_StaysOneJoinedArgument(string source)
        => AssertEval(source, 3);

    [Theory]
    [InlineData("P\n= 1\nP")]
    [InlineData("P // comment\n= 1\nP")]
    public void Eval_CommentBeforeEqualsLine_DefinesPropertyIdentically(string source)
        => AssertEval(source, 1);

    [Fact]
    public void Eval_AdjacencyNeverSplitsTokens()
    {
        AssertEval("ab = 7\nab", 7);
        AssertEval("12", 12);
    }

    [Theory]
    [InlineData("2(3)")]
    [InlineData("2 (3)")]
    [InlineData("2\n(3)")]
    public void Eval_NumberBeforeParenthesizedExpression_IsAdjacencyNotMultiplication(string source)
        => AssertEvalCounted(source, 2, ResultFromAtoms(2, 3));

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
    private static void AssertIndexDiagnosticName(
        string source, string expectedName, string forbiddenBracketName)
    {
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected a diagnostic but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains($"`{expectedName}`", formatted);
        Assert.DoesNotContain(forbiddenBracketName, formatted);
    }

    [Theory]
    // The renderer is syntax-based, so a sequence target and a list target
    // render identically.
    [InlineData("Rows = [[1, 2]]\nRows:0.Missing")]
    [InlineData("Rows = [[1, 2], [3, 4]]\nRows:0.Missing")]
    [InlineData("Rows = ((1, 2), (3, 4))\nRows:0.Missing")]
    public void Eval_Index_DiagnosticName_RendersSourceFaithfulColonSyntax(string source)
        => AssertIndexDiagnosticName(source, "Rows:0", "Rows[0]");

    [Fact]
    public void Eval_Index_ChainedDiagnosticName_RendersEachSelector()
        => AssertIndexDiagnosticName(
            "Rows = [[[1]]]\nRows:0:0.Missing", "Rows:0:0", "Rows[0][0]");

    [Fact]
    public void Eval_Index_DiagnosticName_ParenthesizesOperandsThatWouldRebind()
    {
        // Indexing binds tighter than every binary operator, so a bare
        // `Rows + Rows:0` would read as `Rows + (Rows:0)`.
        AssertIndexDiagnosticName(
            "Rows = (1, 2)\n(Rows + Rows):0.Missing",
            "(Rows + Rows):0",
            "(Rows + Rows)[0]");

        // The selector is a primary in source syntax, so a compound selector
        // keeps the parentheses it was written with.
        AssertIndexDiagnosticName(
            "Rows = ((1, 2), (3, 4))\ni = 0\nRows:(i + 1).Missing",
            "Rows:(i + 1)",
            "Rows[(i + 1)]");

        // Established call abbreviation is preserved on an index target.
        AssertIndexDiagnosticName(
            "take([1, 2, 3], 1):0.Missing", "take(...):0", "take(...)[0]");

        // A list-literal selector is legitimate syntax and stays bare: the ban
        // above is on bracket INDEXING, not on brackets as such.
        AssertIndexDiagnosticName(
            "Rows = ((1, 2), (3, 4))\nRows:[0].Missing", "Rows:[0]", "Rows[[0]]");
    }

    /// <summary>
    /// EvalIndexSelectionCounted owns the index-expression span, so plain and
    /// counted evaluation must report the identical error kind and span.
    /// </summary>
    private static void AssertIndexErrorAgreesAcrossEvaluators(string source)
    {
        var ast = Parser.Parse(source).Root;
        var plain = Evaluator.Run(new Expr.Block(ast));
        var counted = Evaluator.RunCounted(new Expr.Block(ast));

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

    // â”€â”€ Properties â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Property_ReturnsValue()
    {
        var source = """
            X = 5
            X
            """;
        AssertEval(source, 5);
    }

    [Fact]
    public void Eval_Property_WithExpression()
    {
        var source = """
            X = 2 + 3
            X
            """;
        AssertEval(source, 5);
    }

    [Fact]
    public void Eval_Property_MultipleOutputs()
    {
        var source = """
            X = 1, 2, 3
            X
            """;
        AssertEval(source, 1, 2, 3);
    }

    [Fact]
    public void Eval_Property_ReferenceAnother()
    {
        var source = """
            A = 5
            B = A + 1
            B
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_Arity_IsNoLongerRecognizedAsIntrinsic_OnPropertyReceiver()
    {
        var source = """
            Data = 1, 7
            Data.arity
            """;

        AssertUnknownDotMember(source, "arity");
    }

    [Fact]
    public void Eval_Arity_IsNoLongerRecognizedAsIntrinsic_OnInlineParenReceiver()
        => AssertUnknownDotMember("(1, 7).arity", "arity");

    [Fact]
    public void Eval_Arity_IsNoLongerRecognizedAsIntrinsic_OnNestedParenReceiver()
        => AssertUnknownDotMember("((1, 7)).arity", "arity");

    [Fact]
    public void Eval_Length_IsNoLongerRecognizedAsIntrinsic()
    {
        AssertUnknownDotMember(
            """
            X = 1, 2, 3
            X.length
            """,
            "length");
    }

    // ── string intrinsic tests ──────────────────────────────────────────

    [Fact]
    public void Eval_StringIntrinsic_SimpleInteger()
    {
        // 123.string → "123"
        AssertEvalString("123.string", "123");
    }

    [Fact]
    public void Eval_StringIntrinsic_Zero()
    {
        // 0.string → "0"
        AssertEvalString("0.string", "0");
    }

    [Fact]
    public void Eval_StringIntrinsic_NegativeNumber()
    {
        // (-5).string → "-5"
        AssertEvalString("(-5).string", "-5");
    }

    [Fact]
    public void Eval_StringIntrinsic_Decimal()
    {
        // 1.20.string → "1.20"
        // Canonical representation preserves decimal trailing zeros (C# decimal behavior)
        AssertEvalString("1.20.string", "1.20");
    }

    [Fact]
    public void Eval_StringIntrinsic_PropertyBound()
    {
        // A = 123; A.string → "123"
        var source = """
            A = 123
            A.string
            """;
        AssertEvalString(source, "123");
    }

    [Fact]
    public void Eval_StringIntrinsic_ReturnsRealStringValue()
    {
        // Result must be a first-class string value usable in equality comparison
        var source = """
            A = 123
            A.string == '123'
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_StringIntrinsic_WorksThroughDotCallPath()
    {
        // Works through the ordinary dot-call builtin-property path.
        var source = """
            X = 42
            X.string
            """;
        AssertEvalString(source, "42");
    }

    [Fact]
    public void Eval_StringIntrinsic_OnStringValue_Fails()
    {
        // Applying .string to a string value should fail with typeMismatch
        AssertEvalFailsWithTypeMismatch("'hello'.string", "numeric receiver");
    }

    [Fact]
    public void Eval_StringIntrinsic_OnMultiOutput_Fails()
    {
        // Applying .string to a multi-output value should fail
        var source = """
            X = 1, 2
            X.string
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_StringIntrinsic_ExpressionResult()
    {
        // Works on computed expression results
        var source = """
            A = 10 + 5
            A.string
            """;
        AssertEvalString(source, "15");
    }

    [Fact]
    public void Eval_PropertyAccess_SubProperty()
    {
        var source = """
            X = (Y = 42
            Y)
            X.Y
            """;
        AssertEval(source, 42);
    }

    // â”€â”€ Blocks â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Block_ReturnsOutput()
        => AssertEval("{1 + 2}", 3);

    [Fact]
    public void Eval_InlineBlock_ReturnsOutput()
        => AssertEval("(1, 2, 3)", 1, 2, 3);

    // â”€â”€ If builtin â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_If_TrueCondition_ReturnsThenBranch()
        => AssertEval("if(1, (10), (20))", 10);

    [Fact]
    public void Eval_If_FalseCondition_ReturnsElseBranch()
        => AssertEval("if(0, (10), (20))", 20);

    [Fact]
    public void Eval_If_NonZeroCondition_ReturnsThenBranch()
        => AssertEval("if(5, (10), (20))", 10);

    [Fact]
    public void Eval_If_NegativeCondition_ReturnsThenBranch()
        => AssertEval("if(-1, (10), (20))", 10);

    [Fact]
    public void Eval_If_WithExpressions()
        => AssertEval("if(3 > 2, (100), (200))", 100);

    [Fact]
    public void Eval_If_MultipleOutputs()
        => AssertEval("if(1, (1, 2), (3, 4))", 1, 2);

    // Issue #130: a selected branch that is a multi-output property such as
    // `X = 1, 2, 3` is observed as one grouped sequence value (emitted count 1),
    // exactly like value-position property access — not three separate outputs.
    [Theory]
    [InlineData("X = 1, 2, 3\nif(1, X, X)")]
    [InlineData("X = 1, 2, 3\nif(0, X, X)")]
    public void Eval_If_MultiOutputBranchProperty_CollapsesToOneSequenceValue(string source)
        => AssertEvalCounted(source, 1, ResultFromAtoms(1, 2, 3));

    [Fact]
    public void Eval_If_DistinctMultiOutputBranches_TrueSelectsThenAsOneValue()
        => AssertEvalCounted("X = 1, 2, 3\nY = 10, 20, 30\nif(1, X, Y)", 1, ResultFromAtoms(1, 2, 3));

    [Fact]
    public void Eval_If_DistinctMultiOutputBranches_FalseSelectsElseAsOneValue()
        => AssertEvalCounted("X = 1, 2, 3\nY = 10, 20, 30\nif(0, X, Y)", 1, ResultFromAtoms(10, 20, 30));

    [Fact]
    public void Eval_If_ParenthesizedBranchProperty_StaysOneSequenceValue()
        => AssertEvalCounted("X = (1, 2, 3)\nif(1, X, X)", 1, ResultFromAtoms(1, 2, 3));

    [Fact]
    public void Eval_If_SpreadResult_OpensSelectedBranchIntoItems()
        => AssertEvalCounted("X = 1, 2, 3\nif(1, X, X).spread", 3, ResultFromAtoms(1, 2, 3));

    // Issue #131: an explicit spread argument opens its value into the three `if`
    // call-argument slots, so `if(X.spread)` with `X = 1, 2, 3` is equivalent to
    // `if(1, 2, 3)` and selects the `whenTrue` branch (2) as one value.
    [Theory]
    [InlineData("TrueResult = 1, 2, 3\nif(TrueResult.spread)")]
    [InlineData("TrueResult = (1, 2, 3)\nif(TrueResult.spread)")]
    [InlineData("Pair = 2, 3\nif(1, Pair.spread)")]
    public void Eval_If_SpreadArgument_OpensIntoThreeArguments(string source)
        => AssertEvalCounted(source, 1, Atom(2));

    // A direct builtin `if(X.spread)` matches the user-wrapper `MyIF(X.spread)` path.
    [Fact]
    public void Eval_If_SpreadArgument_MatchesUserWrapper()
    {
        var direct = EvalFull("TrueResult = 1, 2, 3\nif(TrueResult.spread)");
        var wrapped = EvalFull("TrueResult = 1, 2, 3\nMyIF(a, b, c) = if(a, b, c)\nMyIF(TrueResult.spread)");
        Assert.False(direct.IsError);
        Assert.False(wrapped.IsError);
        Assert.True(Result.ValueComparer.Equals(direct.Value, wrapped.Value));
        Assert.True(Result.ValueComparer.Equals(direct.Value, Atom(2)));
    }

    // A spread whose expanded count is not 3 now reaches evaluation and fails with
    // the normal builtin arity mismatch (expected 3), not a parser arity error.
    [Fact]
    public void Eval_If_SpreadArgument_WrongExpandedArity_FailsAtEvaluation()
        => AssertEvalFailsWithArityMismatch("Two = 1, 2\nif(Two.spread)", expected: 3, actual: 2);

    // The fix changes counted/display provenance only; the selected branch value
    // is unchanged, so operations that consume the value still open it as before.
    [Theory]
    [InlineData("X = 1, 2, 3\ncount(if(1, X, X))", 3)]
    [InlineData("X = 1, 2, 3\nsum(if(1, X, X))", 6)]
    [InlineData("X = 1, 2, 3\nfirst(if(1, X, X))", 1)]
    public void Eval_If_MultiOutputBranchProperty_ValueIsInvariant(string source, int expected)
        => AssertEval(source, expected);

    // ── Property / call / builtin boundary arity = 1 ──────────────────────────
    // A property/call/builtin RESULT boundary always returns ONE value: a body or
    // collection that internally produces an item supply is observed by the caller
    // as one sequence value (emitted count 1). Only an explicit caller-site
    // `spread(value)` / `value.spread` slot contributes it back to the surrounding
    // item supply. This generalizes the
    // lexical property-access and `if`-branch behavior to every value boundary.
    // Lean: reCountValueBoundary.

    // User-defined variadic call: the collecting binding collects the supplied argument
    // slots as one exact immutable list value.
    [Fact]
    public void Eval_UserCall_VariadicReturn_IsOneListValue()
        => AssertEvalCounted("F(a...) = a\nF(5, 9)", 1, ListValue(Atom(5), Atom(9)));

    [Fact]
    public void Eval_UserCall_VariadicReturnWithBodySpread_IsOneSequenceValue()
        => AssertEvalCounted("F(a...) = a.spread\nF(5, 9)", 1, ResultFromAtoms(5, 9));

    // Body `a, 0`: the variadic capture stays grouped as a nested list value.
    [Fact]
    public void Eval_UserCall_VariadicCommaSlot_GroupsCaptureAsNestedValue()
        => AssertEvalCounted(
            "F(a...) = a, 0\nF(5, 9)",
            1,
            Result.FromItems([ListValue(Atom(5), Atom(9)), Atom(0)]));

    // Body `a.spread, 0`: the body spread flattens the capture into sibling slots, and
    // the boundary still returns the whole flat item supply as one value.
    [Fact]
    public void Eval_UserCall_VariadicBodySpreadThenSlot_IsOneFlatSequenceValue()
        => AssertEvalCounted("F(a...) = a.spread, 0\nF(5, 9)", 1, ResultFromAtoms(5, 9, 0));

    // Caller-site spread turns the returned value back into an item supply.
    [Fact]
    public void Eval_UserCall_CallerSpread_OpensReturnedValue()
        => AssertEvalCounted("F(a...) = a\nF(5, 9).spread", 2, ResultFromAtoms(5, 9));

    // Explicit zero-arg call `X()` is a call boundary (unlike property access `X`)
    // and now also returns one value.
    [Fact]
    public void Eval_ExplicitZeroArgCall_IsOneSequenceValue()
        => AssertEvalCounted("X = 1, 2, 3\nX()", 1, ResultFromAtoms(1, 2, 3));

    // Regression: lexical zero-arg property access was already arity 1.
    [Fact]
    public void Eval_LexicalPropertyAccess_StaysOneSequenceValue()
        => AssertEvalCounted("X = 1, 2, 3\nX", 1, ResultFromAtoms(1, 2, 3));

    // Structural dot zero-arg access now matches lexical access (arity 1).
    [Fact]
    public void Eval_StructuralDotZeroArgAccess_IsOneSequenceValue()
        => AssertEvalCounted("M = {\n  Public P = 1, 2, 3\n  P\n}\nM.P", 1, ResultFromAtoms(1, 2, 3));

    // Internal variadic forwarding is unaffected: the body still sees the raw item
    // exact list, so collection builtins open it after binding and explicit
    // spread-forwarding re-spreads it at the caller-selected boundary.
    [Theory]
    [InlineData("F(a...) = sum(a)\nF(5, 9)", 14)]
    [InlineData("F(a...) = count(a)\nF(5, 9)", 2)]
    [InlineData("G(a...) = a.spread\nsum(G(5, 9))", 14)]
    [InlineData("F(a...) = a\nsum(F(5, 9))", 14)]
    public void Eval_VariadicForwarding_UsesCollectedListViews(string source, int expected)
        => AssertEval(source, expected);

    // Collection-producing builtins return one exact immutable list value;
    // spread opens it.
    [Theory]
    [InlineData("X = 3, 1, 2\nX.order", 1)]
    [InlineData("X = 1, 2, 3, 3\nX.distinct", 1)]
    public void Eval_CollectionBuiltin_IsOneExactListValue(string source, int expectedCount)
        => AssertEvalCounted(source, expectedCount, ListValue(Atom(1), Atom(2), Atom(3)));

    [Fact]
    public void Eval_CollectionBuiltin_OrderSpread_OpensIntoItems()
        => AssertEvalCounted("X = 3, 1, 2\nX.order.spread", 3, ResultFromAtoms(1, 2, 3));

    [Fact]
    public void Eval_CollectionBuiltin_Take_IsOneExactListValue()
        => AssertEvalCounted("X = 1, 2, 3\nX.take(2)", 1, ListValue(Atom(1), Atom(2)));

    [Fact]
    public void Eval_CollectionBuiltin_TakeSpread_OpensIntoItems()
        => AssertEvalCounted("X = 1, 2, 3\nX.take(2).spread", 2, ResultFromAtoms(1, 2));

    [Fact]
    public void Eval_CollectionBuiltin_Skip_IsOneExactListValue()
        => AssertEvalCounted("X = 1, 2, 3\nX.skip(1)", 1, ListValue(Atom(2), Atom(3)));

    [Fact]
    public void Eval_CollectionBuiltin_Filter_IsOneExactListValue()
        => AssertEvalCounted("IsBig = x > 1\nX = 1, 2, 3\nX.filter(IsBig)", 1, ListValue(Atom(2), Atom(3)));

    [Fact]
    public void Eval_CollectionBuiltin_Map_IsOneExactListValue()
        => AssertEvalCounted("Double = x * 2\nX = 1, 2, 3\nX.map(Double)", 1, ListValue(Atom(2), Atom(4), Atom(6)));

    [Fact]
    public void Eval_CollectionBuiltin_Range_IsOneExactListValue()
        => AssertEvalCounted("range(1, 3)", 1, ListValue(Atom(1), Atom(2), Atom(3)));

    [Fact]
    public void Eval_CollectionBuiltin_RangeSpread_OpensIntoItems()
        => AssertEvalCounted("range(1, 3).spread", 3, ResultFromAtoms(1, 2, 3));

    [Fact]
    public void Eval_CollectionBuiltin_Atoms_IsOneExactListValue()
        => AssertEvalCounted("atoms((1, (2, 3)))", 1, ListValue(Atom(1), Atom(2), Atom(3)));

    [Fact]
    public void Eval_CollectionBuiltin_OrderDesc_IsOneExactListValue()
        => AssertEvalCounted("X = 3, 1, 2\nX.orderDesc", 1, ListValue(Atom(3), Atom(2), Atom(1)));

    [Fact]
    public void Eval_CollectionBuiltin_OrderDescSpread_OpensIntoItems()
        => AssertEvalCounted("X = 3, 1, 2\nX.orderDesc.spread", 3, ResultFromAtoms(3, 2, 1));

    [Fact]
    public void Eval_CollectionBuiltin_DistinctSpread_OpensIntoItems()
        => AssertEvalCounted("X = 1, 1, 2, 3\nX.distinct.spread", 3, ResultFromAtoms(1, 2, 3));

    [Fact]
    public void Eval_CollectionBuiltin_SkipSpread_OpensIntoItems()
        => AssertEvalCounted("X = 1, 2, 3\nX.skip(1).spread", 2, ResultFromAtoms(2, 3));

    [Fact]
    public void Eval_CollectionBuiltin_FilterSpread_OpensIntoItems()
        => AssertEvalCounted("IsBig = x > 1\nX = 1, 2, 3\nX.filter(IsBig).spread", 2, ResultFromAtoms(2, 3));

    [Fact]
    public void Eval_CollectionBuiltin_MapSpread_OpensIntoItems()
        => AssertEvalCounted("Double = x * 2\nX = 1, 2, 3\nX.map(Double).spread", 3, ResultFromAtoms(2, 4, 6));

    [Fact]
    public void Eval_CollectionBuiltin_AtomsSpread_OpensIntoItems()
        => AssertEvalCounted("atoms((1, (2, 3))).spread", 3, ResultFromAtoms(1, 2, 3));

    // A collection-builtin result fed into another sequence builtin is still
    // opened by singleton-boundary normalization (value-based, not count-based).
    [Theory]
    [InlineData("sum(range(1, 4))", 10)]
    [InlineData("X = 3, 1, 2\nsum(X.order)", 6)]
    public void Eval_CollectionBuiltin_ResultStillConsumedByBuiltin(string source, int expected)
        => AssertEval(source, expected);

    // Chaining a collection builtin onto a collection builtin still works: the
    // lone list result is opened as the collection input of the next builtin.
    [Fact]
    public void Eval_CollectionBuiltin_ChainedOrder_IsOneExactListValue()
        => AssertEvalCounted("X = 3, 1, 2\nX.order.order", 1, ListValue(Atom(1), Atom(2), Atom(3)));

    // Regression: scalar/reduction builtins were already arity 1 and are unchanged.
    [Fact]
    public void Eval_ScalarReduction_Sum_StaysOneValue()
        => AssertEvalCounted("X = 1, 2, 3\nX.sum", 1, Atom(6));

    [Fact]
    public void Eval_Reduce_StaysOneAccumulatorValue()
        => AssertEvalCounted("Add = x + total\nreduce((1, 2, 3, 4), Add, 0)", 1, Atom(10));

    // Regression: a map transform that emits more than one value is still rejected;
    // the boundary rule must NOT silently turn it into one sequence-valued element.
    [Fact]
    public void Eval_Map_MultiOutputCallback_StillRejected()
        => AssertEvalFails("Pair = x, x * 10\n(1, 2, 3).map(Pair)");

    // Regression: root output is NOT a call boundary and stays multi-output.
    [Fact]
    public void Eval_RootOutput_StaysMultiOutput()
        => AssertEvalCounted("1, 2, 3", 3, ResultFromAtoms(1, 2, 3));

    [Fact]
    public void Eval_RootOutput_Spread_StaysMultiOutput()
        => AssertEvalCounted("X = 1, 2, 3\nX.spread", 3, ResultFromAtoms(1, 2, 3));

    // Regression: while/repeat intentionally preserve multi-slot loop state and are
    // NOT collapsed by the boundary rule.
    [Fact]
    public void Eval_Repeat_MultiSlotLoopState_StaysMultiSlot()
        => AssertEvalCounted("repeat({a + 1, b + a}, 3, 0, 0)", 2, ResultFromAtoms(3, 3));

    // Regression: redundant empty-sequence nesting is canonicalized before the
    // public boundary is observed.
    [Fact]
    public void Eval_Boundary_CanonicalizesNestedEmptySequence()
        => AssertEvalCounted("F = (())\nF", 1, SequenceValue());

    [Fact]
    public void Eval_Boundary_PreservesSingletonSequenceValue()
        => AssertEvalCounted("F = ((1, 2))\nF", 1, SequenceValue(Atom(1), Atom(2)));

    // â”€â”€ Repeat builtin â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Repeat_SingleParam()
        => AssertEval("repeat({x + 1}, (3), (0))", 3);

    [Fact]
    public void Eval_Repeat_ZeroIterations()
        => AssertEval("repeat({x + 1}, (0), (5))", 5);

    [Fact]
    public void Eval_Repeat_MultipleParams()
        => AssertEval("repeat({a + 1, b + a}, 3, 0, 0)", 3, 3);

    [Fact]
    public void Eval_Repeat_NegativeCount_Fails()
        => AssertEvalFails("repeat({x}, (-1), (0))");

    [Fact]
    public void Eval_Repeat_Factorial()
        => AssertEval("repeat({n + 1, acc * n}, 5, 1, 1):1", 120);

    [Fact]
    public void Eval_Repeat_SimultaneousUpdate_UsesOldStateForAllOutputs()
    {
        var source = """
            Step = b, ~a
            Step.repeat(1, 1, 2)
            """;
        AssertEvalLoopModes(source, 2, 1);
    }

    [Fact]
    public void Eval_LoopStage2_PlannedCases_MatchGenericMode()
    {
        var cases = new (string Source, decimal[] Expected)[]
        {
            ("""
                Step = k + 1
                Step.repeat(5, 2):0
                """, [7m]),
            ("""
                Step = k + 1, k <= 10
                Step.while(2):0
                """, [11m]),
            ("""
                Step = k + 1, k * k <= 100
                Step.while(2):0
                """, [11m]),
            ("""
                Outer(num) = {
                    Step = k + 1, k * k <= num
                    Step.while(2):0
                }
                Outer(100)
                """, [11m]),
            ("""
                Test = {
                    Step = k + 1, k <= 10
                    Step.while(2):0
                }

                Run(n) = {
                    Step = value + 1, total + Test()
                    Step.repeat(n, 1, 0):1
                }

                Run(5)
                """, [55m]),
        };

        foreach (var (source, expected) in cases)
            AssertEvalLoopModes(source, expected);
    }

    [Fact]
    public void Eval_LoopStage2_MinimalRepeat_UsesPlannedExpressionDiagnostics()
    {
        var source = """
            Step = k + 1
            Step.repeat(5, 2):0
            """;

        var (result, stats) = EvalFullWithLoopDiagnostics(source);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal([7m], result.Value.ToAtoms());
        Assert.Equal(1, stats.OptimizedLoopHits);
        Assert.Equal(1, stats.LoopPlanBuilds);
        Assert.Equal(5, stats.LoopIterations);
        Assert.Equal(5, stats.PlannedExpressionHits);
        Assert.Equal(0, stats.PlannedExpressionFallbacks);
        Assert.Equal(0, stats.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.Equal(5, stats.PlannedBuiltinOperations);

        var plan = AssertSingleLoopPlan(stats, "Step.repeat");
        Assert.Equal("repeat", plan.Kind);
        Assert.Equal(1, plan.StateArity);
        Assert.Equal(1, plan.BuildCount);
        Assert.Equal(1, plan.ExecutionCount);
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal("Add(StateSlot(k), Const(1))", output.PlanSummary);
        Assert.Null(output.FallbackReason);
    }

    [Fact]
    public void Eval_LoopStage2_MinimalWhile_ReportsOutputAndContinuationPlans()
    {
        var source = """
            Step = k + 1, k <= 100
            Step.while(2):0
            """;

        var (result, stats) = EvalFullWithLoopDiagnostics(source);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal([101m], result.Value.ToAtoms());

        var plan = AssertSingleLoopPlan(stats, "Step.while");
        Assert.Equal("while", plan.Kind);
        Assert.Equal(1, plan.StateArity);

        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal("Add(StateSlot(k), Const(1))", output.PlanSummary);

        var continuation = AssertLoopExpression(plan, "continuation", null);
        Assert.True(continuation.Planned);
        Assert.Equal("LessOrEqual(StateSlot(k), Const(100))", continuation.PlanSummary);
    }

    [Fact]
    public void Eval_OptimizedLoop_VariadicStep_RejectedAtEligibilityGate()
    {
        var source = """
            Step(values...) = values, 0
            Step.while(1, 2, 3)
            """;

        AssertEvalLoopModes(source, 1, 2, 3);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([1m, 2m, 3m], result.Value.ToAtoms());
        Assert.Equal(0, stats.OptimizedLoopHits);
        Assert.Equal(1, stats.FallbackReasons["variadic loop step"]);
    }

    [Fact]
    public void Eval_OptimizedLoop_SequenceValuePatternStep_RejectedAtEligibilityGate()
    {
        var source = """
            Step((x, y)) = x + 1, y + 1, 0
            Step.while((1, 2))
            """;

        AssertEvalLoopModes(source, 1, 2);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([1m, 2m], result.Value.ToAtoms());
        Assert.Equal(0, stats.OptimizedLoopHits);
        Assert.Equal(1, stats.FallbackReasons["variadic loop step"]);
    }

    [Fact]
    public void Eval_OptimizedLoop_FlatFixedScalarStep_RemainsOptimized()
    {
        var source = """
            Step(x) = x + 1, x < 3
            Step.while(1)
            """;

        AssertEvalLoopModes(source, 3);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([3m], result.Value.ToAtoms());
        Assert.Equal(1, stats.OptimizedLoopHits);
        Assert.Equal(0, stats.PlannedExpressionFallbacks);
        Assert.Equal(0, stats.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.DoesNotContain("variadic loop step", stats.FallbackReasons.Keys);
    }

    [Fact]
    public void Eval_LoopStage3A_RepeatOutput_PlansIf()
    {
        var source = """
            Step = x + if(x == 2, 10, 1)
            Step.repeat(3, 1):0
            """;

        AssertEvalLoopModes(source, 13);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(stats, "Step.repeat");
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal(
            "Add(StateSlot(x), If(Equal(StateSlot(x), Const(2)), Const(10), Const(1)))",
            output.PlanSummary);
    }

    [Fact]
    public void Eval_LoopStage3A_RepeatOutput_PlansIfWithCapturedSlot()
    {
        var source = """
            Outer(n) = {
                Step = x + if(x <= n, 1, 0)
                Step.repeat(5, 0):0
            }
            Outer(3)
            """;

        AssertEvalLoopModes(source, 4);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(stats, "Outer.Step.repeat");
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal(
            "Add(StateSlot(x), If(LessOrEqual(StateSlot(x), CapturedSlot(n)), Const(1), Const(0)))",
            output.PlanSummary);
    }

    [Fact]
    public void Eval_LoopStage3A_PlannedIf_PreservesLazyBranchEvaluation()
    {
        var source = """
            Step = x + if(x == 1, 1, 1 / 0)
            Step.repeat(1, 1):0
            """;

        AssertEvalLoopModes(source, 2);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(stats, "Step.repeat");
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Contains("If(", output.PlanSummary, StringComparison.Ordinal);
        Assert.Contains("Divide(Const(1), Const(0))", output.PlanSummary, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_LoopStage3A_IfPlanning_RespectsLexicalShadowing()
    {
        var source = """
            if(a, b, c) = b + c
            Step = if(x, 10, 1)
            Step.repeat(1, 0):0
            """;

        AssertEvalLoopModes(source, 11);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(stats, "Step.repeat");
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.False(output.Planned);
        Assert.Equal("unsupported call: if", output.FallbackReason);
    }

    [Fact]
    public void Eval_LoopStage3B_LocalTempOutput_IsPlanned()
    {
        var source = """
            Step = {
                A = x + 1
                A
            }
            Step.repeat(3, 0):0
            """;

        AssertEvalLoopModes(source, 3);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(stats, "Step.repeat");
        var temp = AssertLoopTemp(plan, "A");
        Assert.True(temp.Planned, temp.FallbackReason);
        Assert.Equal("Add(StateSlot(x), Const(1))", temp.PlanSummary);

        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal("TempSlot(A)", output.PlanSummary);
    }

    [Fact]
    public void Eval_LoopStage3B_LocalTemp_RecomputesEachIteration()
    {
        var source = """
            Step = {
                A = x
                A + 1
            }
            Step.repeat(3, 0):0
            """;

        AssertEvalLoopModes(source, 3);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(stats, "Step.repeat");
        var temp = AssertLoopTemp(plan, "A");
        Assert.True(temp.Planned, temp.FallbackReason);
        Assert.Equal("StateSlot(x)", temp.PlanSummary);

        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal("Add(TempSlot(A), Const(1))", output.PlanSummary);
    }

    [Fact]
    public void Eval_LoopStage3B_UnusedLocalTemp_IsNotEvaluated()
    {
        var source = """
            Step = {
                A = 1 / 0
                x + 1
            }
            Step.repeat(1, 0):0
            """;

        AssertEvalLoopModes(source, 1);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(stats, "Step.repeat");
        var temp = AssertLoopTemp(plan, "A");
        Assert.True(temp.Planned, temp.FallbackReason);
        Assert.Equal("Divide(Const(1), Const(0))", temp.PlanSummary);

        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal("Add(StateSlot(x), Const(1))", output.PlanSummary);
    }

    [Fact]
    public void Eval_LoopStage3B_LocalTemp_UsedByContinuation()
    {
        var source = """
            Step = {
                A = x + 1
                A, A <= 5
            }
            Step.while(0):0
            """;

        AssertEvalLoopModes(source, 5);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal([5m], result.Value.ToAtoms());
        Assert.Equal(1, stats.OptimizedLoopHits);

        var plan = AssertSingleLoopPlan(stats, "Step.while");
        var temp = AssertLoopTemp(plan, "A");
        Assert.True(temp.Planned, temp.FallbackReason);
        Assert.Equal("Add(StateSlot(x), Const(1))", temp.PlanSummary);

        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal("TempSlot(A)", output.PlanSummary);

        var continuation = AssertLoopExpression(plan, "continuation", null);
        Assert.True(continuation.Planned);
        Assert.Equal("LessOrEqual(TempSlot(A), Const(5))", continuation.PlanSummary);
    }

    [Fact]
    public void Eval_LoopStage3B_SquareFreeLocalTemp_PlansInnerLoop()
    {
        var source = """
            IsSquareFree(num) = {
                Step = {
                    K2 = k * k
                    k + 1, s + if(num mod K2 == 0, 1, 0), K2 <= num and s <= 0
                }
                Step.while(2, 0):1 == 0
            }
            IsSquareFree(100)
            """;

        AssertEvalLoopModes(source, 0);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(stats, "IsSquareFree.Step.while");
        var temp = AssertLoopTemp(plan, "K2");
        Assert.True(temp.Planned, temp.FallbackReason);
        Assert.Equal("Multiply(StateSlot(k), StateSlot(k))", temp.PlanSummary);

        var output0 = AssertLoopExpression(plan, "output", 0);
        Assert.True(output0.Planned);
        Assert.Equal("Add(StateSlot(k), Const(1))", output0.PlanSummary);

        var output1 = AssertLoopExpression(plan, "output", 1);
        Assert.True(output1.Planned);
        Assert.Contains("TempSlot(K2)", output1.PlanSummary, StringComparison.Ordinal);
        Assert.Contains("If(", output1.PlanSummary, StringComparison.Ordinal);

        var continuation = AssertLoopExpression(plan, "continuation", null);
        Assert.True(continuation.Planned);
        Assert.Contains("LessOrEqual(TempSlot(K2), CapturedSlot(num))", continuation.PlanSummary, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_LoopStage3B_UnsupportedParameterizedLocalTemp_FallsBackClearly()
    {
        var source = """
            Step = {
                A(x) = x + 1
                A(k), k <= 10
            }
            Step.while(0):0
            """;

        AssertEvalLoopModes(source, 11);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(stats, "Step.while");
        var temp = AssertLoopTemp(plan, "A");
        Assert.False(temp.Planned);
        Assert.Equal("unsupported local property with explicit parameters: A", temp.FallbackReason);

        var output = AssertLoopExpression(plan, "output", 0);
        Assert.False(output.Planned);
        Assert.Equal("unsupported call: A", output.FallbackReason);

        var continuation = AssertLoopExpression(plan, "continuation", null);
        Assert.True(continuation.Planned);
        Assert.Equal("LessOrEqual(StateSlot(k), Const(10))", continuation.PlanSummary);
    }

    [Fact]
    public void Eval_LoopStage3A_SquareFreeStyleLoop_PlansInnerIfOutput()
    {
        var source = """
            IsSquareFree(num) = {
                Step = k + 1, s + if(num mod (k * k) == 0, 1, 0), k * k <= num and s <= 0
                Step.while(2, 0):1 == 0
            }
            IsSquareFree(100)
            """;

        var (result, stats) = EvalFullWithLoopDiagnostics(source);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal([0m], result.Value.ToAtoms());

        var plan = AssertSingleLoopPlan(stats, "IsSquareFree.Step.while");
        Assert.Equal("while", plan.Kind);
        Assert.Equal(2, plan.StateArity);

        var output0 = AssertLoopExpression(plan, "output", 0);
        Assert.True(output0.Planned);
        Assert.Equal("Add(StateSlot(k), Const(1))", output0.PlanSummary);

        var output1 = AssertLoopExpression(plan, "output", 1);
        Assert.True(output1.Planned);
        Assert.Contains("If(", output1.PlanSummary, StringComparison.Ordinal);
        Assert.Contains("Mod(CapturedSlot(num), Multiply(StateSlot(k), StateSlot(k)))", output1.PlanSummary, StringComparison.Ordinal);

        var continuation = AssertLoopExpression(plan, "continuation", null);
        Assert.True(continuation.Planned);
        Assert.Contains("And(", continuation.PlanSummary, StringComparison.Ordinal);
        Assert.Contains("CapturedSlot(num)", continuation.PlanSummary, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_LoopStage3A_SquareFreeCountOuterRepeat_ReportsUserCallFallbackInsideIfCondition()
    {
        var source = """
            IsSquareFree(num) = {
                Step = k + 1, s + if(num mod (k * k) == 0, 1, 0), k * k <= num and s <= 0
                Step.while(2, 0):1 == 0
            }

            SquareFreeCount(n) = {
                Step = value + 1, total + if(IsSquareFree(value), 1, 0)
                Step.repeat(n, 1, 0):1
            }

            SquareFreeCount(20)
            """;

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var outerPlan = AssertSingleLoopPlan(stats, "SquareFreeCount.Step.repeat");
        var outerOutput = AssertLoopExpression(outerPlan, "output", 1);
        Assert.False(outerOutput.Planned);
        Assert.Equal("unsupported if condition: unsupported call: IsSquareFree", outerOutput.FallbackReason);

        var innerPlan = AssertSingleLoopPlan(stats, "IsSquareFree.Step.while");
        var innerOutput = AssertLoopExpression(innerPlan, "output", 1);
        Assert.True(innerOutput.Planned);
        Assert.Contains("If(", innerOutput.PlanSummary, StringComparison.Ordinal);
    }

    // â”€â”€ While builtin â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_While_CountDown()
        => AssertEval("while({x - 1, x - 1}, (3))", 1);

    [Fact]
    public void Eval_While_SingleOutputStep_UsesGenericSingletonSemantics()
        => AssertEvalLoopModes("while({x - 1}, 3)", 1);

    [Fact]
    public void Eval_While_GcdDotCall_ProjectsFinalState()
    {
        var source = """
            GcdStep = b, ~a mod b, a mod b != 0
            GcdStep.while(12, 30):1
            """;
        AssertEvalLoopModes(source, 6);
    }

    [Fact]
    public void Eval_While_TerminatingNextStateIsNotCommitted()
    {
        var source = """
            Step = x + 10, x < 3
            Step.while(0)
            """;
        AssertEvalLoopModes(source, 10);
    }

    [Fact]
    public void Eval_While_LocalPropertyRecomputesPerIteration()
    {
        var source = """
            Step = {
                A = x
                A + 1, x < 3
            }
            Step.while(0)
            """;
        AssertEvalLoopModes(source, 3);
    }

    [Fact]
    public void Eval_While_NestedStepCapturesParentParameter()
    {
        var source = """
            Outer(n) = {
                Step = x + n, x < 10
                Step.while(0)
            }
            Outer(2)
            """;
        AssertEvalLoopModes(source, 10);
    }

    [Fact]
    public void Eval_While_NestedStepUsesMutableStateAndCapturedParentValues()
    {
        var source = """
            Outer(limit, offset) = {
                Reached = candidate + offset >= limit
                Step = candidate + 1, not Reached
                Step.while(0)
            }
            Outer(6, 2)
            """;
        AssertEvalLoopModes(source, 4);
    }

    [Fact]
    public void Eval_While_BadContinuationValue_KeepsTypeMismatchMeaning()
    {
        var (_, optimizedError) = AssertEvalFailsInBothLoopModes("while({x + 1, 'keep'}, 0)");
        var error = Innermost(optimizedError);
        var typeMismatch = Assert.IsType<EvalError.TypeMismatch>(error);
        Assert.Contains("Expected a number", typeMismatch.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_Repeat_BadStateArity_KeepsLoopBindingContext()
    {
        var (_, optimizedError) = AssertEvalFailsInBothLoopModes("repeat({x + 1}, 2, 0, 1)");
        var formatted = KatLangError.FromEvalError(optimizedError).Message;
        Assert.Contains("`repeat` step expects 1 state value", formatted, StringComparison.Ordinal);
        Assert.Contains("current loop state has 2 state values", formatted, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_While_EvenFibonacciSum()
    {
        // Sums even Fibonacci numbers <= 100: 2 + 8 + 34 = 44.
        // Grace (~a) reorders detected params [b, a, total] -> [a, b, total].
        // Initial state arguments 1, 2, 0 bind a=1, b=2, total=0.
        // The step with b=144 (first even Fibonacci > 100) triggers cont=0;
        // pre-check semantics return the prior state (total=44), not the updated one.
        var source = """
            Algo = b, ~a + b, total + if(b mod 2 == 0, b, 0), b <= 100
            Sum = Algo.while(1, 2, 0) : 2
            Sum
            """;
        AssertEval(source, 44);
    }

    [Fact]
    public void Eval_While_ImmediateExit()
        => AssertEval("while({x, 0}, (5))", 5);

    [Fact]
    public void Eval_While_DotCall_SumMultiplesOf3Or5()
    {
        var source = """
            Algo = n - 1, result + if(n mod 3==0 or n mod 5==0, n, 0), n > 2
            Sum = Algo.while(x, 0) : 1
            Sum(999)
            """;
        AssertEval(source, 233168);
    }

    // ── While/repeat multi-item init boundaries ──────────────────────────────────

    [Fact]
    public void Eval_While_DotCall_BareComma_Works()
    {
        // Algo.while(x, 0) with bare comma starts with two explicit state slots.
        var source = """
            Algo = n - 1, result + if(n mod 3==0 or n mod 5==0, n, 0), n > 2
            Sum = Algo.while(x, 0) : 1
            Sum(999)
            """;
        AssertEval(source, 233168);
    }

    [Fact]
    public void Eval_While_DotCall_ParenSequenceValueInit_IsOneSlot()
    {
        var source = """
            Algo = n - 1, result + if(n mod 3==0 or n mod 5==0, n, 0), n > 2
            Sum = Algo.while((x, 0)) : 1
            Sum(999)
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_While_DotCall_ExistingInit_ExplicitSelectionsWork()
    {
        var source = """
            Algo = n - 1, result + if(n mod 3==0 or n mod 5==0, n, 0), n > 2
            Init = x, 0
            Sum = Algo.while(Init(x):0, Init(x):1) : 1
            Sum(999)
            """;
        AssertEval(source, 233168);
    }

    [Fact]
    public void Eval_While_DotCall_BareComma_NoParams()
    {
        var source = """
            Algo = n - 1, result + if(n mod 3==0 or n mod 5==0, n, 0), n > 2
            Sum = Algo.while(x, 0) : 1
            Sum(999)
            """;
        AssertEval(source, 233168);
    }

    // â”€â”€ Atoms builtin â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_While_DirectCall_MultiInit()
    {
        // while(Step, s1, s2, ...) starts with one state slot per explicit init arg.
        var source = """
            Step = n - 1, acc + n, n > 1
            while(Step, 5, 0) : 1
            """;
        // 5+4+3+2 = 14 (stops when n=1, cont=0, returns prior state)
        AssertEval(source, 14);
    }

    [Fact]
    public void Eval_Repeat_DirectCall_MultiInit()
    {
        // repeat(Step, n, s1, s2) starts with two explicit state slots.
        var source = """
            Step = a + 1, b + a
            repeat(Step, 3, 0, 0)
            """;
        AssertEval(source, 3, 3);
    }

    [Fact]
    public void Eval_Repeat_DotCall_MultiInit()
    {
        // Step.repeat(n, s1, s2) lexical fallback preserves the explicit state slots.
        var source = """
            Step = a + 1, b + a
            Step.repeat(3, 0, 0)
            """;
        AssertEval(source, 3, 3);
    }

    [Fact]
    public void Eval_While_DotCall_SingleInit_StillWorks()
    {
        var source = """
            Step = x - 1, x - 1
            Step.while(3)
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Repeat_DotCall_SingleInit_StillWorks()
    {
        var source = """
            Step = x + 1
            Step.repeat(3, 0)
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_While_DirectCall_SingleInit_StillWorks()
        => AssertEval("while({x - 1, x - 1}, 3)", 1);

    [Fact]
    public void Eval_Repeat_DirectCall_SingleInit_StillWorks()
        => AssertEval("repeat({x + 1}, 3, 0)", 3);

    [Fact]
    public void Eval_DotCall_TrailingBrace_StillWorks()
    {
        var source = """
            F = x + 1
            F{3}
            """;
        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_DotCall_PropertyPrecedence_WhileShadow()
    {
        // If algorithm A has a real property named while, dotCall must
        // resolve as property call, not lexical builtin fallback packaging
        var source = """
            A = {
                while = x + 1
            }
            A.while(10)
            """;
        AssertEval(source, 11);
    }

    [Fact]
    public void Eval_DotCall_PropertyPrecedence_RepeatShadow()
    {
        var source = """
            A = {
                repeat = x * 2
            }
            A.repeat(5)
            """;
        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_While_DotCall_NoArgs_Fails()
    {
        var source = """
            Step = x - 1, x > 0
            Step.while()
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_Repeat_DotCall_NoArgs_Fails()
    {
        var source = """
            Step = x + 1
            Step.repeat()
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_Repeat_DotCall_OneArg_Fails()
    {
        var source = """
            Step = x + 1
            Step.repeat(3)
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_ParenSubExpr_FirstArg_Works()
    {
        var source = """
            F = a + b
            F((1 + 2) mod 2, 10)
            """;
        AssertEval(source, 11);
    }

    [Fact]
    public void Eval_If_ParenSubExpr_FirstArg_Works()
        => AssertEval("if((1 + 2) mod 2 == 0, 1, 0)", 0);

    [Fact]
    public void Eval_DoubleParens_IsOrdinaryGrouping()
    {
        var source = """
            X = ((1 + 2))
            X
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Atoms_FlattensGroups()
        => AssertEval("atoms(((1, 2), (3, 4)))", 1, 2, 3, 4);

    [Fact]
    public void Eval_Atoms_SingleValue()
        => AssertEval("atoms((5))", 5);

    [Fact]
    public void Eval_Content_NoLongerResolvesAsBuiltin()
    {
        // `content` was removed as a builtin; it now behaves like any other
        // unresolved callable/identifier unless the user defines it.
        AssertEvalFails("content(1)");
        AssertEvalFails("content((1, 2, 3))");
    }

    [Fact]
    public void Eval_Content_UserDefinedCallable_IsNotReserved()
        => AssertEval(
            """
            content(x) = x + 1
            content(1)
            """,
            2);

    [Fact]
    public void Eval_Spread_MultiOutputProperty_OpensIntoOutput()
        => AssertEval(
            """
            X = 1, 2, 3
            X.spread
            """,
            1, 2, 3);

    [Fact]
    public void Eval_Spread_SequenceValueProperty_OpensIntoOutput()
        => AssertEval(
            """
            X = (1, 2, 3)
            X.spread
            """,
            1, 2, 3);

    // ── Range builtin ────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Range_AscendingInclusive()
        => AssertEval("range(1, 10)", 1, 2, 3, 4, 5, 6, 7, 8, 9, 10);

    [Fact]
    public void Eval_Range_DescendingInclusive()
        => AssertEval("range(10, 1)", 10, 9, 8, 7, 6, 5, 4, 3, 2, 1);

    [Fact]
    public void Eval_Range_SingletonWhenEqual()
        => AssertEval("range(5, 5)", 5);

    [Fact]
    public void Eval_Range_NegativeToPositive()
        => AssertEval("range(-2, 2)", -2, -1, 0, 1, 2);

    [Fact]
    public void Eval_Range_NonIntegerStart_Fails()
        => AssertEvalFailsWithIllegalInEval("range(1.5, 5)", "range start must be an integer");

    [Fact]
    public void Eval_Range_NonIntegerStop_Fails()
        => AssertEvalFailsWithIllegalInEval("range(1, 5.2)", "range stop must be an integer");

    [Fact]
    public void Eval_Range_SequenceSpread_PreservesOrdering()
        => AssertEval("range(3, 1).spread 0", 3, 2, 1, 0);

    // ── Filter builtin ───────────────────────────────────────────────────────

    [Fact]
    public void Eval_Filter_DirectCallMultiArgs_KeepsMatchingItems()
    {
        var source = """
            IsEven = x mod 2 == 0
            filter((1, 2, 3, 4, 5, 6), IsEven)
            """;
        AssertEval(source, 2, 4, 6);
    }

    // Variadic-style top-level binding contract.

    [Fact]
    public void Eval_Filter_BoundaryLaw_CommaSeparatedRangeSourceExpandsTopLevelItems()
    {
        var source = """
            IsEven = x mod 2 == 0
            filter((range(3, 6).spread, 8), IsEven)
            """;

        AssertEval(source, 4, 6, 8);
    }

    [Fact]
    public void Eval_Filter_BoundaryLaw_NamedMultiOutputSingleSourceExpands()
    {
        var source = """
            IsEven = x mod 2 == 0
            Data = 3, 4, 5, 6
            filter(Data, IsEven)
            """;

        AssertEval(source, 4, 6);
    }

    [Fact]
    public void Eval_Filter_BoundaryLaw_DotCallReceiverExpandsAsSingleSource()
    {
        var source = """
            IsEven = x mod 2 == 0
            Data = 3, 4, 5, 6
            Data.filter(IsEven)
            """;

        AssertEval(source, 4, 6);
    }

    [Fact]
    public void Eval_Filter_BoundaryLaw_CommaSeparatedNamedMultiOutputExpandsTopLevelItems()
    {
        var source = """
            IsEven = x mod 2 == 0
            Data = 3, 4, 5, 6
            filter((Data.spread, 8), IsEven)
            """;

        AssertEval(source, 4, 6, 8);
    }

    [Fact]
    public void Eval_Filter_RangeArgument_IteratesEmittedItemsForPredicate()
    {
        var source = """
            KeepWholeRange((a, b, c, d, e)) = 1
            KeepWholeRange(x) = 0
            filter(range(1, 5), KeepWholeRange)
            """;

        AssertEval(source);
    }

    [Fact]
    public void Eval_Filter_DirectCallMixedArgs_ExpandsRangeTopLevelItemsForPredicate()
    {
        var source = """
            KeepWideRange((a, b, c, d)) = 1
            KeepWideRange(x) = 0
            filter(((1, 2), range(3, 6).spread), KeepWideRange)
            """;

        AssertEval(source);
    }

    [Fact]
    public void Eval_Filter_SequenceValueElements_ArePreservedWhole()
    {
        var source = """
            KeepPair = pair:0 mod 2 == 0
            filter(((1, 10), (2, 20), (3, 30), (4, 40)), KeepPair)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        // The kept pairs stay whole sequence values, held as exact list elements.
        AssertListOfSequenceValueAtoms(result.Value, [2m, 20m], [4m, 40m]);
    }

    [Fact]
    public void Eval_Filter_MultiOutputPredicate_FailsWithContext()
    {
        var source = """
            Bad(x) = 0, 999
            filter((1, 2, 3), Bad)
            """;

        AssertFilterPredicateShapeFails(source);
    }

    [Fact]
    public void Eval_Filter_SequenceValuePredicateResult_FailsWithContext()
    {
        var source = """
            Bad(x) = (1, 0)
            filter((1, 2, 3), Bad)
            """;

        AssertFilterPredicateShapeFails(source);
    }

    [Fact]
    public void Eval_Filter_EmptyPredicateResult_FailsWithContext()
    {
        var source = """
            Bad(x) = take(1, 0)
            filter((1, 2, 3), Bad)
            """;

        AssertFilterPredicateShapeFails(source);
    }

    [Fact]
    public void Eval_Filter_StringPredicateResult_FailsWithContext()
    {
        var source = """
            Bad(x) = x.string
            filter((1, 2, 3), Bad)
            """;

        AssertFilterPredicateShapeFails(source);
    }

    [Fact]
    public void Eval_Filter_ArityMismatch_FollowsBuiltinConvention()
    {
        // filter(collection, predicate) is an ordinary fixed-arity callable:
        // a zero-argument call is a plain arity error carrying the fixed
        // signature.
        var result = EvalFull("filter()");
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Equal(
            "Callable `filter(collection, predicate)` expects 2 arguments, but was called with 0 arguments.",
            formatted);

        var error = result.Error;
        while (error is EvalError.WithContext wc)
            error = wc.Inner;

        Assert.IsType<EvalError.ArityMismatch>(error);
        Assert.False(error is EvalError.VariadicArityMismatch);
    }

    // ── Map builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Map_DirectCallMultiArgs_TransformsEachItem()
    {
        var source = """
            Double = x * 2
            map((1, 2, 3), Double)
            """;

        AssertEval(source, 2, 4, 6);
    }

    [Fact]
    public void Eval_Map_RangeArgument_IteratesEmittedItemsForHigherOrderIteration()
    {
        var source = """
            TopLevelItemCount(item) = item.count
            map(range(3, 6), TopLevelItemCount)
            """;

        AssertEval(source, 1, 1, 1, 1);
    }

    [Fact]
    public void Eval_Map_PreservesOriginalOrder()
    {
        var source = """
            Tag = x * 10 + 1
            map((5, 4, 3, 2, 1), Tag)
            """;

        AssertEval(source, 51, 41, 31, 21, 11);
    }

    [Fact]
    public void Eval_Map_RangeArgument_WithScalarTransform_MapsEachEmittedItem()
    {
        var source = """
            AddOne = x + 1
            map(range(1, 5), AddOne)
            """;

        AssertEval(source, 2, 3, 4, 5, 6);
    }

    [Fact]
    public void Eval_Map_DirectCallMixedArgs_ExpandsRangeTopLevelItems()
    {
        var source = """
            MarkSequenceValueRange((a, b, c)) = 1
            MarkSequenceValueRange(x) = 0
            map((1, range(2, 4).spread), MarkSequenceValueRange)
            """;

        AssertEval(source, 0, 0, 0, 0);
    }

    [Fact]
    public void Eval_Map_SequenceValueElements_ArePassedWhole()
    {
        var source = """
            TakeValue = pair:1
            map(((1, 10), (2, 20), (3, 30)), TakeValue)
            """;

        AssertEval(source, 10, 20, 30);
    }

    [Fact]
    public void Eval_Map_SequenceValueTransformResult_IsAccepted()
    {
        var source = """
            PairWithSquare(x) = (x, x * x)
            map((1, 2, 3), PairWithSquare)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        // Each mapped sequence value is one exact list element of the map result.
        AssertListOfSequenceValueAtoms(result.Value, [1m, 1m], [2m, 4m], [3m, 9m]);
    }

    [Fact]
    public void Eval_Map_EmptyTransformResult_FailsWithContext()
    {
        // A transform whose body is the truly empty result `()` still fails the
        // strict single-element contract. (A collection builtin like take(1, 0)
        // no longer produces this failure — it returns the empty list [], which
        // is one valid element; see the exact-list acceptance test below.)
        var source = """
            Bad(x) = ()
            map((1, 2, 3), Bad)
            """;

        AssertMapTransformShapeFails(source);
    }

    [Fact]
    public void Eval_Map_EmptyListTransformResult_IsOneMappedElementPerItem()
    {
        // take(1, 0) returns the exact empty list value [] — ONE valid mapped
        // element per item, so the transform succeeds with result [[], [], []].
        AssertEvalCounted(
            """
            EmptyList(x) = take(1, 0)
            map((1, 2, 3), EmptyList)
            """,
            1,
            ListValue(ListValue(), ListValue(), ListValue()));
    }

    [Fact]
    public void Eval_Map_MultiOutputTransformResult_FailsWithContext()
    {
        var source = """
            Bad(x) = x, x * x
            map((1, 2, 3), Bad)
            """;

        AssertMapTransformShapeFails(source);
    }

    // ── Order builtins ──────────────────────────────────────────────────────

    [Fact]
    public void Eval_Order_DirectCallMultiArgs_SortsAscending()
        => AssertEval("order((3, 4, 2, 1, 3, 3))", 1, 2, 3, 3, 3, 4);

    [Fact]
    public void Eval_Order_WrapperMultiOutputArg_ExpandsTopLevelItems()
    {
        var source = """
            Values = 3, 4, 2, 1, 3, 3
            order(Values)
            """;

        AssertEval(source, 1, 2, 3, 3, 3, 4);
    }

    [Fact]
    public void Eval_Order_SingleSequenceValueArg_SortsSequenceItems()
        => AssertEval("order((3, 4, 2, 1, 3, 3))", 1, 2, 3, 3, 3, 4);

    [Fact]
    public void Eval_Order_ProjectedSelection_PlainAndDotCallAgree()
        => AssertEval(
            """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            order(Data:0)
            (Data:0).order
            """,
            1,
            2,
            4,
            6,
            7,
            1,
            2,
            4,
            6,
            7);

    [Fact]
    public void Eval_Order_DirectCallMixedArgs_ExpandsRangeTopLevelItems()
        => AssertEval("order((3, 4, range(1, 5).spread, 7))", 1, 2, 3, 3, 4, 4, 5, 7);

    [Fact]
    public void Eval_Order_DotCallReceiverAsSingleSource_SortsRangeItems()
        => AssertEval("range(5, 1).order", 1, 2, 3, 4, 5);

    [Fact]
    public void Eval_Order_DotCall_InlineParenReceiver_PreservesBoundary()
        => AssertEval("(3, 5, 3, 6, 3).order", 3, 3, 3, 5, 6);

    [Fact]
    public void Eval_Order_DoubleParenReceiver_DotCallSortsSequenceItems()
        => AssertEval("((3, 5, 3, 6, 3)).order", 3, 3, 3, 5, 6);

    [Fact]
    public void Eval_Order_UnsupportedElement_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "order((1, 'hello'))",
            "order expects each collection element to be a single numeric value; item 1 was string value \"hello\"");

    [Fact]
    public void Eval_Order_SequenceValueMultiArgs_FailWithContext()
        => AssertBuiltinFailureWithExactContext(
            "order(((1, 2), (3, 4)))",
            "order expects each collection element to be a single numeric value; item 0 was sequence value");

    [Fact]
    public void Eval_OrderDesc_DirectCallMultiArgs_SortsDescending()
        => AssertEval("orderDesc((3, 4, 2, 1, 3, 3))", 4, 3, 3, 3, 2, 1);

    [Fact]
    public void Eval_OrderDesc_WrapperMultiOutputArg_ExpandsTopLevelItems()
    {
        var source = """
            Values = 3, 4, 2, 1, 3, 3
            orderDesc(Values)
            """;

        AssertEval(source, 4, 3, 3, 3, 2, 1);
    }

    [Fact]
    public void Eval_OrderDesc_SingleSequenceValueArg_SortsSequenceItems()
        => AssertEval("orderDesc((3, 4, 2, 1, 3, 3))", 4, 3, 3, 3, 2, 1);

    [Fact]
    public void Eval_OrderDesc_SequenceValueMultiArgs_FailWithContext()
        => AssertBuiltinFailureWithExactContext(
            "orderDesc(((1, 2), (3, 4)))",
            "orderDesc expects each collection element to be a single numeric value; item 0 was sequence value");

    [Fact]
    public void Eval_Order_IndexedNumericDiagnostic_IncludesItemIndex()
        => AssertBuiltinFailureWithContext(
            "order((1, (2, 3)))",
            "order expects each collection element to be a single numeric value; item 1 was sequence value");

    [Fact]
    public void Eval_OrderDesc_IndexedNumericDiagnostic_IncludesItemIndex()
        => AssertBuiltinFailureWithContext(
            "orderDesc((1, (2, 3)))",
            "orderDesc expects each collection element to be a single numeric value; item 1 was sequence value");

    // ── Count builtin ────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Count_OrdinaryBuiltinCall_CountsRangeTopLevelItems()
        => AssertEval("count(range(1, 5))", 5);

    [Fact]
    public void Eval_Count_DotCall_CountsRangeTopLevelItems()
        => AssertEval("range(1, 5).count", 5);

    [Fact]
    public void Eval_Count_DotCall_EmptyFilterReceiver_ReturnsZero()
        => AssertEval("(1, 5, 3).filter{ n mod 2 == 0 }.count", 0);

    [Fact]
    public void Eval_Filter_DotCallTrailingBlockSpacing_ReturnsEquivalentResults()
    {
        AssertEval("(1, 2, 3, 4).filter{ n > 2 }.count", 2);
        AssertEval("(1, 2, 3, 4).filter { n > 2 }.count", 2);
    }

    [Fact]
    public void Eval_Count_DotCall_EmptyFilterReceiverWithNamedPredicate_ReturnsZero()
    {
        var source = """
            IsEven = n mod 2 == 0
            (1, 5, 3).filter(IsEven).count
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_FusesDotFilterDotCount()
    {
        var source = """
            IsEven = x mod 2 == 0
            CountEven(N) = range(1, N).filter(IsEven).count
            CountEven(10)
            """;

        AssertEvalSequenceModes(source, 5);

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([5m], result.Value.ToAtoms());
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(0, stats.FilterCountFusionFallbacks);
        Assert.Equal(1, stats.DirectRangeFusionHits);
        Assert.Equal(0, stats.DirectRangeFusionFallbacks);
        Assert.Equal(10, stats.FilterCountPredicateCalls);
        Assert.Equal(5, stats.AvoidedFilteredResultMaterializations);
        Assert.Equal(10, stats.AvoidedSourceMaterializations);

        var pipeline = Assert.Single(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.Equal("dot-filter-dot-count", pipeline.Form);
        Assert.Equal("filter.count -> countWhere", pipeline.Fusion);
        Assert.Equal("builtin range", pipeline.SourceKind);
        Assert.Equal("range(...)", pipeline.SourceSummary);
        Assert.Equal("direct range iteration", pipeline.SourceExecution);
        Assert.Null(pipeline.SourceExecutionFallbackReason);
        Assert.Equal("IsEven", pipeline.PredicateSummary);
        Assert.Equal(10, pipeline.SourceItemCount);
        Assert.Equal(10, pipeline.PredicateCalls);
        Assert.Equal(5, pipeline.ResultCount);
        Assert.Equal(10, pipeline.AvoidedSourceMaterializationCount);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_SingleKeptSequenceItem_CountsKeptItem()
    {
        // filter keeps exactly one sequence-valued item. The filter result is the
        // exact list [(1, 2)], and `count` opens the lone list boundary: the count
        // is the kept-item count 1, in both the generic composition and the fused
        // filter.count path.
        var source = """
            KeepFirstPair(pair) = pair:0 == 1
            (((1, 2), (3, 4))).filter(KeepFirstPair).count
            """;

        AssertEvalSequenceModes(source, 1);

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([1m], result.Value.ToAtoms());
        Assert.Equal(1, stats.FilterCountFusionHits);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_SingleKeptEmptyItem_CountsOneKeptItem()
    {
        // A lone kept `()` stays an exact list element ([()]), so the count is
        // the kept-item count 1 in both the generic composition and the fused
        // filter.count path.
        var source = """
            KeepEmpty(x) = x.count == 0
            Values = (), 1
            Values.filter(KeepEmpty).count
            """;

        AssertEvalSequenceModes(source, 1);

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([1m], result.Value.ToAtoms());
        Assert.Equal(1, stats.FilterCountFusionHits);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_FusesPlainCountDotFilter()
    {
        // Under fixed collection-object arity the BARE one-argument form
        // count(src.filter(pred)) is the valid plain composition, and it is
        // the form the filter->count fusion recognizes.
        var source = """
            IsEven = x mod 2 == 0
            CountEven(N) = count(range(1, N).filter(IsEven))
            CountEven(10)
            """;

        AssertEvalSequenceModes(source, 5);

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([5m], result.Value.ToAtoms());
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(0, stats.FilterCountFusionFallbacks);
        Assert.Equal(1, stats.DirectRangeFusionHits);
        Assert.Equal(0, stats.DirectRangeFusionFallbacks);
        Assert.Equal(10, stats.FilterCountPredicateCalls);
        Assert.Equal(5, stats.AvoidedFilteredResultMaterializations);
        Assert.Equal(10, stats.AvoidedSourceMaterializations);

        var pipeline = Assert.Single(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.Equal("plain-count-dot-filter", pipeline.Form);
        Assert.Equal("filter.count -> countWhere", pipeline.Fusion);
        Assert.Equal("builtin range", pipeline.SourceKind);
        Assert.Equal("direct range iteration", pipeline.SourceExecution);
        Assert.Equal("IsEven", pipeline.PredicateSummary);
        Assert.Equal(10, pipeline.PredicateCalls);
        Assert.Equal(5, pipeline.ResultCount);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_FusesPlainCountPlainFilter()
    {
        // The BARE nested plain form count(filter(src, pred)) — filter's exact
        // list result is count's one collection argument — also fuses.
        var source = """
            IsEven = x mod 2 == 0
            CountEven(N) = count(filter(range(1, N), IsEven))
            CountEven(10)
            """;

        AssertEvalSequenceModes(source, 5);

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([5m], result.Value.ToAtoms());
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(0, stats.FilterCountFusionFallbacks);
        Assert.Equal(1, stats.DirectRangeFusionHits);
        Assert.Equal(0, stats.DirectRangeFusionFallbacks);
        Assert.Equal(10, stats.FilterCountPredicateCalls);
        Assert.Equal(5, stats.AvoidedFilteredResultMaterializations);
        Assert.Equal(10, stats.AvoidedSourceMaterializations);

        var pipeline = Assert.Single(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.Equal("plain-count-plain-filter", pipeline.Form);
        Assert.Equal("filter.count -> countWhere", pipeline.Fusion);
        Assert.Equal("builtin range", pipeline.SourceKind);
        Assert.Equal("direct range iteration", pipeline.SourceExecution);
        Assert.Equal("IsEven", pipeline.PredicateSummary);
        Assert.Equal(10, pipeline.PredicateCalls);
        Assert.Equal(5, pipeline.ResultCount);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_DotAndPlainCountFormsAgree()
    {
        var source = """
            IsEven = x mod 2 == 0
            A = range(1, 10).filter(IsEven).count
            B = count(range(1, 10).filter(IsEven))
            A, B
            """;

        AssertEvalSequenceModes(source, 5, 5);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_NoMatches()
    {
        var source = """
            Never(x) = 0
            range(1, 10).filter(Never).count
            """;

        AssertEvalSequenceModes(source, 0);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_AllMatches()
    {
        var source = """
            Always(x) = 1
            range(1, 10).filter(Always).count
            """;

        AssertEvalSequenceModes(source, 10);
    }

    [Fact]
    public void Eval_SequencePipelineS2_FilterCount_DirectRangeDescendingMatchesGeneric()
    {
        var source = """
            IsEven = x mod 2 == 0
            range(10, 1).filter(IsEven).count
            """;

        AssertEvalSequenceModes(source, 5);

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([5m], result.Value.ToAtoms());
        Assert.Equal(1, stats.DirectRangeFusionHits);
        var pipeline = Assert.Single(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.Equal("direct range iteration", pipeline.SourceExecution);
        Assert.Equal(10, pipeline.SourceItemCount);
    }

    [Fact]
    public void Eval_SequencePipelineS2_FilterCount_DirectRangeSingletonMatchesGeneric()
    {
        var source = """
            IsFive = x == 5
            range(5, 5).filter(IsFive).count
            """;

        AssertEvalSequenceModes(source, 1);

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([1m], result.Value.ToAtoms());
        Assert.Equal(1, stats.DirectRangeFusionHits);
        Assert.Equal(1, stats.AvoidedSourceMaterializations);
        var pipeline = Assert.Single(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.Equal(1, pipeline.SourceItemCount);
        Assert.Equal(1, pipeline.AvoidedSourceMaterializationCount);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_SequenceValueItems()
    {
        var source = """
            KeepPair = pair:0 mod 2 == 0
            Data = (1, 10), (2, 20), (3, 30), (4, 40)
            Data.filter(KeepPair).count
            """;

        AssertEvalSequenceModes(source, 2);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_ErrorOrderMatchesGeneric()
    {
        var source = """
            BadOnFive(x) = if(x == 5, 1 / 0, x mod 2 == 0)
            range(1, 10).filter(BadOnFive).count
            """;

        var generic = EvalFull(
            source,
            enableLoopOptimization: true,
            enableSequencePipelineOptimization: false);
        var optimized = EvalFull(
            source,
            enableLoopOptimization: true,
            enableSequencePipelineOptimization: true);

        if (generic.IsOk)
            Assert.Fail($"Expected generic sequence evaluation failure but got: {generic.Value}");
        if (optimized.IsOk)
            Assert.Fail($"Expected optimized sequence evaluation failure but got: {optimized.Value}");

        Assert.IsType<EvalError.DivByZero>(Innermost(generic.Error));
        Assert.IsType<EvalError.DivByZero>(Innermost(optimized.Error));

        var genericMessage = KatLangError.FromEvalError(generic.Error).Message;
        var optimizedMessage = KatLangError.FromEvalError(optimized.Error).Message;
        Assert.Contains("while evaluating filter predicate for item 4: 5", genericMessage);
        Assert.Contains("while evaluating filter predicate for item 4: 5", optimizedMessage);
    }

    [Fact]
    public void Eval_SequencePipelineS2_FilterCount_RangeArgumentErrorOrderMatchesGeneric()
    {
        var source = """
            BadPredicate(x) = 1 / 0
            range(1 / 0, 10).filter(BadPredicate).count
            """;

        var generic = EvalFull(
            source,
            enableLoopOptimization: true,
            enableSequencePipelineOptimization: false);
        var optimized = EvalFull(
            source,
            enableLoopOptimization: true,
            enableSequencePipelineOptimization: true);

        if (generic.IsOk)
            Assert.Fail($"Expected generic sequence evaluation failure but got: {generic.Value}");
        if (optimized.IsOk)
            Assert.Fail($"Expected optimized sequence evaluation failure but got: {optimized.Value}");

        Assert.IsType<EvalError.DivByZero>(Innermost(generic.Error));
        Assert.IsType<EvalError.DivByZero>(Innermost(optimized.Error));
    }

    [Fact]
    public void Eval_SequencePipeline_UnarySpreadReceiver_FusesAndMatchesGeneric()
    {
        // A parenthesized postfix-spread dot receiver `(range(1, 10).spread)` feeds a
        // dot filter/count pipeline. It fuses through the GENERIC dot-receiver
        // source plan (the receiver is iterated by EvaluateDotReceiverIterationItems)
        // — NOT via UnwrapSpread (which only serves the plain-count path)
        // and NOT via direct-range fusion (the receiver is a parenthesized group,
        // not a bare `range(...)` call). The fused result equals the generic one.
        var source = """
            IsEven = x mod 2 == 0
            (range(1, 10).spread).filter(IsEven).count
            """;

        var generic = EvalFull(source, enableLoopOptimization: true, enableSequencePipelineOptimization: false);
        var optimized = EvalFull(source, enableLoopOptimization: true, enableSequencePipelineOptimization: true);
        if (generic.IsError)
            Assert.Fail($"Expected generic success but got error: {generic.Error}");
        if (optimized.IsError)
            Assert.Fail($"Expected optimized success but got error: {optimized.Error}");
        Assert.Equal(generic.Value.ToAtoms(), optimized.Value.ToAtoms());

        var (_, stats) = EvalFullWithSequenceDiagnostics(source);
        Assert.Contains(stats.Pipelines, pipeline => pipeline.Optimized);
        // Exactly one filter-count pipeline runs here, fused via the generic
        // dot-receiver source plan — not direct-range fusion.
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(0, stats.DirectRangeFusionHits);
    }

    [Fact]
    public void Eval_CountFilter_PlainCallCountsFilteredItems_OptimizedMatchesGeneric()
    {
        // Plain count of a filter result: filter returns one exact list value
        // and count opens that lone collection boundary.
        AssertEvalSequenceModes(
            "IsEven = x mod 2 == 0\ncount(filter(range(1, 10), IsEven))",
            5m);

        AssertEvalSequenceModes(
            "IsEven = x mod 2 == 0\nData = range(1, 10)\ncount(filter(Data, IsEven))",
            5m);

        AssertEvalSequenceModes(
            "IsEven = x mod 2 == 0\ncount(range(1, 10).filter(IsEven))",
            5m);

        AssertEvalSequenceModes(
            "IsEven = x mod 2 == 0\nData = range(1, 10)\ncount(Data.filter(IsEven))",
            5m);
    }

    [Fact]
    public void Eval_CountFilter_FilteredItemCountForms_OptimizedMatchesGeneric()
    {
        // The forms whose generic meaning IS the filtered-item count (5). Here the
        // fusion legitimately applies and optimized must equal generic.

        AssertEvalSequenceModes(
            "IsEven = x mod 2 == 0\ncount(filter(range(1, 10), IsEven))",
            5m);

        AssertEvalSequenceModes(
            "IsEven = x mod 2 == 0\nData = range(1, 10)\ncount(filter(Data, IsEven))",
            5m);

        // Dot-call count iterates the receiver = filtered-item count.
        AssertEvalSequenceModes(
            "IsEven = x mod 2 == 0\nrange(1, 10).filter(IsEven).count",
            5m);

        // Dot-filter dot-count over a named source.
        AssertEvalSequenceModes(
            "IsEven = x mod 2 == 0\nData = range(1, 10)\nData.filter(IsEven).count",
            5m);

        AssertEvalSequenceModes(
            "IsEven = x mod 2 == 0\nData = range(1, 10)\ncount(Data.filter(IsEven))",
            5m);
    }

    [Fact]
    public void Eval_SequencePipeline_DirectRangeSource_StillFusesViaDirectRange()
    {
        // The bare plain composition over a direct `range(...)` source fuses
        // via direct-range iteration and matches the generic result.
        var source = """
            IsEven = x mod 2 == 0
            count(filter(range(1, 10), IsEven))
            """;

        var generic = EvalFull(source, enableLoopOptimization: true, enableSequencePipelineOptimization: false);
        var optimized = EvalFull(source, enableLoopOptimization: true, enableSequencePipelineOptimization: true);
        if (generic.IsError)
            Assert.Fail($"Expected generic success but got error: {generic.Error}");
        if (optimized.IsError)
            Assert.Fail($"Expected optimized success but got error: {optimized.Error}");
        Assert.Equal(generic.Value.ToAtoms(), optimized.Value.ToAtoms());
        Assert.Equal([5m], optimized.Value.ToAtoms());

        var (_, stats) = EvalFullWithSequenceDiagnostics(source);
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(1, stats.DirectRangeFusionHits);
    }

    [Fact]
    public void Eval_SequencePipeline_NestedSpreadReceiver_FusesAndMatchesGeneric()
    {
        // A doubly-nested postfix-spread dot receiver `(range(1, 10).spread.spread)`.
        // Like the single-spread case it fuses through the GENERIC dot-receiver
        // source plan (the receiver is iterated by EvaluateDotReceiverIterationItems,
        // which evaluates the nested unary spread to the same items) — NOT via
        // UnwrapSpread and NOT via direct-range fusion. The fused result
        // equals the generic one.
        var source = """
            IsEven = x mod 2 == 0
            (range(1, 10).spread.spread).filter(IsEven).count
            """;

        var generic = EvalFull(source, enableLoopOptimization: true, enableSequencePipelineOptimization: false);
        var optimized = EvalFull(source, enableLoopOptimization: true, enableSequencePipelineOptimization: true);
        if (generic.IsError)
            Assert.Fail($"Expected generic success but got error: {generic.Error}");
        if (optimized.IsError)
            Assert.Fail($"Expected optimized success but got error: {optimized.Error}");
        Assert.Equal(generic.Value.ToAtoms(), optimized.Value.ToAtoms());

        var (_, stats) = EvalFullWithSequenceDiagnostics(source);
        Assert.Contains(stats.Pipelines, pipeline => pipeline.Optimized);
        // Exactly one filter-count pipeline runs here, fused via the generic
        // dot-receiver source plan — not direct-range fusion.
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(0, stats.DirectRangeFusionHits);
    }

    [Fact]
    public void Eval_SequencePipeline_PlainFilterCountFallback_DoesNotEvaluateNonRangeSource()
    {
        // White-box regression for the plain filter-count fallback path: when the
        // filter source is NOT a direct builtin range, the optimizer must defer to
        // the generic evaluator WITHOUT evaluating the source first (otherwise a
        // non-range source would be evaluated once during the failed fusion probe
        // and again during generic fallback — double evaluation).
        //
        // Models `count(filter(Data.spread, IsEven).spread)` with `Data` a non-range
        // (named) source. The counting EvaluateSequenceIterationItems delegate
        // must be invoked exactly zero times.
        var sequenceEvalCount = 0;

        var filterArgs = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [],
            Output:
            [
                new Expr.SequenceSpread(new Expr.Resolve("Data")),
                new Expr.Resolve("IsEven"),
            ]);
        var countArgs = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [],
            Output:
            [
                new Expr.SequenceSpread(
                    new Expr.Call(new Expr.Resolve("filter"), filterArgs)),
            ]);
        var invocation = SequencePipelineInvocation.PlainCall(
            new Expr.Resolve("count"),
            countArgs,
            new Algorithm.Builtin(BuiltinId.@count));

        var services = new SequencePipelineEvaluationServices(
            GetDotCallLexicalBuiltinFallbackReason: (_, _, _) => null,
            EvaluateDotReceiverIterationItems: _ =>
                throw new Xunit.Sdk.XunitException("dot-receiver evaluation must not run for a plain call"),
            EvaluateSequenceIterationItems: _ =>
            {
                sequenceEvalCount++;
                return EvalResult<IReadOnlyList<Evaluator.CountedResult>>.Ok(
                    new List<Evaluator.CountedResult>());
            },
            ResolveArgumentAlgorithms: _ => EvalResult<IReadOnlyList<Algorithm>>.Ok(
                [new Algorithm.User(null, [], [], [], []), new Algorithm.User(null, [], [], [], [])]),
            ResolveAlgorithm: _ => EvalResult<Algorithm>.Ok(new Algorithm.Builtin(BuiltinId.@filter)),
            EvaluateRangeCallArguments: (_, _, _) =>
                throw new Xunit.Sdk.XunitException("range-argument evaluation must not run for a non-range source"));

        var diagnostics = new SequencePipelineDiagnostics();
        var handled = SequencePipelineOptimizer.TryExecute(
            invocation,
            services,
            Evaluator.EvalCtx.Empty,
            [],
            diagnostics,
            out _);

        // The optimizer deferred to generic (did not fuse) WITHOUT evaluating the
        // non-range source even once.
        Assert.False(handled);
        Assert.Equal(0, sequenceEvalCount);
    }

    [Fact]
    public void Eval_SequencePipeline_DotFilterCountFallback_GenericReceiverNotEvaluatedOnPredicateResolutionFailure()
    {
        // White-box regression for the dot-filter/count recognition path: when the
        // filter predicate fails to resolve, the optimizer must fall back to the
        // generic evaluator WITHOUT having evaluated the dot receiver (source).
        //
        // Before the fix the dot path evaluated the source FIRST and only then
        // resolved the predicate, so a predicate-resolution failure (1) caused the
        // generic fallback to re-evaluate the source (double evaluation) and (2)
        // recorded a misleading "not executed" fallback diagnostic for a path that
        // HAD executed the source. The fix resolves the predicate before touching
        // the source, so the source is evaluated exactly once — by the generic
        // re-run — and the "not executed" diagnostic is honest.
        //
        // Models `Data.filter(BadPred).count` with `Data` a non-range (generic)
        // receiver. The counting EvaluateDotReceiverIterationItems delegate must be
        // invoked exactly zero times.
        var dotReceiverEvalCount = 0;

        var filterArgs = new Algorithm.User(
            Parent: null, Parameters: [], Opens: [], Properties: [],
            Output: [new Expr.Resolve("BadPred")]);
        var target = new Expr.DotCall(new Expr.Resolve("Data"), "filter", filterArgs);
        var invocation = SequencePipelineInvocation.DotCall(target, "count", null);

        var services = new SequencePipelineEvaluationServices(
            GetDotCallLexicalBuiltinFallbackReason: (_, _, _) => null,
            EvaluateDotReceiverIterationItems: _ =>
            {
                dotReceiverEvalCount++;
                return EvalResult<IReadOnlyList<Evaluator.CountedResult>>.Ok(
                    new List<Evaluator.CountedResult>());
            },
            EvaluateSequenceIterationItems: _ =>
                throw new Xunit.Sdk.XunitException("plain sequence iteration must not run for a dot call"),
            ResolveArgumentAlgorithms: _ =>
                EvalResult<IReadOnlyList<Algorithm>>.Err(new EvalError.UnknownName("BadPred")),
            ResolveAlgorithm: _ => EvalResult<Algorithm>.Ok(new Algorithm.Builtin(BuiltinId.@filter)),
            EvaluateRangeCallArguments: (_, _, _) =>
                throw new Xunit.Sdk.XunitException("range-argument evaluation must not run for a non-range source"));

        var diagnostics = new SequencePipelineDiagnostics();
        var handled = SequencePipelineOptimizer.TryExecute(
            invocation,
            services,
            PreludeEvalCtx(),
            [],
            diagnostics,
            out _);

        // Predicate resolution failed BEFORE any source evaluation, so the
        // optimizer declined (handled == false → generic fallback) without touching
        // the source.
        Assert.False(handled);
        Assert.Equal(0, dotReceiverEvalCount);

        // No optimized pipeline executed, and the recorded fallback honestly
        // reports the source as not executed (because it genuinely was not).
        var stats = diagnostics.GetSnapshot();
        Assert.Equal(0, stats.FilterCountFusionHits);
        Assert.Equal(1, stats.FilterCountFusionFallbacks);
        Assert.Equal(1, stats.FallbackReasons["filter argument resolution failed"]);
        Assert.DoesNotContain(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.All(stats.Pipelines, pipeline => Assert.Equal("not executed", pipeline.SourceExecution));
    }

    [Fact]
    public void Eval_SequencePipeline_DotFilterCountFallback_DirectRangeNotEvaluatedOnPredicateResolutionFailure()
    {
        // White-box regression for the direct-range dot-filter/count path: a range
        // source's bounds must NOT be evaluated by the recognition probe when the
        // filter predicate fails to resolve. With the predicate resolved before the
        // source, the optimizer falls back without evaluating the range arguments,
        // so the generic re-run evaluates them exactly once (no double evaluation).
        //
        // Models `range(1, 10).filter(BadPred).count`. The counting
        // EvaluateRangeCallArguments delegate must be invoked exactly zero times.
        var rangeEvalCount = 0;

        var rangeSource = new Expr.Call(
            new Expr.Resolve("range"),
            new Algorithm.User(
                Parent: null, Parameters: [], Opens: [], Properties: [],
                Output: [new Expr.Num(1m), new Expr.Num(10m)]));
        var filterArgs = new Algorithm.User(
            Parent: null, Parameters: [], Opens: [], Properties: [],
            Output: [new Expr.Resolve("BadPred")]);
        var target = new Expr.DotCall(rangeSource, "filter", filterArgs);
        var invocation = SequencePipelineInvocation.DotCall(target, "count", null);

        var services = new SequencePipelineEvaluationServices(
            GetDotCallLexicalBuiltinFallbackReason: (_, _, _) => null,
            EvaluateDotReceiverIterationItems: _ =>
                throw new Xunit.Sdk.XunitException("generic dot-receiver iteration must not run for a direct range"),
            EvaluateSequenceIterationItems: _ =>
                throw new Xunit.Sdk.XunitException("plain sequence iteration must not run for a dot call"),
            ResolveArgumentAlgorithms: _ =>
                EvalResult<IReadOnlyList<Algorithm>>.Err(new EvalError.UnknownName("BadPred")),
            ResolveAlgorithm: _ => EvalResult<Algorithm>.Ok(new Algorithm.Builtin(BuiltinId.@range)),
            EvaluateRangeCallArguments: (_, _, _) =>
            {
                rangeEvalCount++;
                return EvalResult<Evaluator.InclusiveRange>.Ok(new Evaluator.InclusiveRange(1, 10));
            });

        var diagnostics = new SequencePipelineDiagnostics();
        var handled = SequencePipelineOptimizer.TryExecute(
            invocation,
            services,
            PreludeEvalCtx(),
            [],
            diagnostics,
            out _);

        // The range arguments were not evaluated by the probe (so the generic
        // fallback evaluates them exactly once), and the optimizer declined.
        Assert.False(handled);
        Assert.Equal(0, rangeEvalCount);

        var stats = diagnostics.GetSnapshot();
        Assert.Equal(0, stats.FilterCountFusionHits);
        Assert.Equal(0, stats.DirectRangeFusionHits);
        Assert.Equal(1, stats.FilterCountFusionFallbacks);
        Assert.Equal(1, stats.FallbackReasons["filter argument resolution failed"]);
        Assert.DoesNotContain(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.All(stats.Pipelines, pipeline => Assert.Equal("not executed", pipeline.SourceExecution));
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_RespectsBuiltinShadowing()
    {
        var filterShadow = """
            filter(source..., predicate) = 123
            IsEven = x mod 2 == 0
            range(1, 10).filter(IsEven).count
            """;

        var (filterResult, filterStats) = EvalFullWithSequenceDiagnostics(filterShadow);
        if (filterResult.IsError)
            Assert.Fail($"Expected success but got error: {filterResult.Error}");

        Assert.Equal([1m], filterResult.Value.ToAtoms());
        Assert.Equal(0, filterStats.FilterCountFusionHits);
        Assert.Equal(1, filterStats.FilterCountFusionFallbacks);
        Assert.Equal(1, filterStats.FallbackReasons["filter does not resolve to builtin"]);

        var structuralFilterShadow = """
            Source = (public filter(predicate) = 42)
            IsEven = x mod 2 == 0
            Source.filter(IsEven).count
            """;

        var (structuralFilterResult, structuralFilterStats) = EvalFullWithSequenceDiagnostics(structuralFilterShadow);
        if (structuralFilterResult.IsError)
            Assert.Fail($"Expected success but got error: {structuralFilterResult.Error}");

        Assert.Equal([1m], structuralFilterResult.Value.ToAtoms());
        Assert.Equal(0, structuralFilterStats.FilterCountFusionHits);
        Assert.Equal(1, structuralFilterStats.FilterCountFusionFallbacks);
        Assert.Equal(1, structuralFilterStats.FallbackReasons["filter is shadowed by a structural property"]);

        var countShadow = """
            count(value) = 999
            IsEven = x mod 2 == 0
            range(1, 10).filter(IsEven).count
            """;

        var (countResult, countStats) = EvalFullWithSequenceDiagnostics(countShadow);
        if (countResult.IsError)
            Assert.Fail($"Expected success but got error: {countResult.Error}");

        Assert.Equal([999m], countResult.Value.ToAtoms());
        Assert.Equal(0, countStats.FilterCountFusionHits);
        Assert.Equal(1, countStats.FilterCountFusionFallbacks);
        Assert.Equal(1, countStats.FallbackReasons["count does not resolve to builtin"]);

        var plainFilterShadow = """
            filter(source..., predicate) = 123
            IsEven = x mod 2 == 0
            count(filter(range(1, 10), IsEven))
            """;

        var (plainFilterResult, plainFilterStats) = EvalFullWithSequenceDiagnostics(plainFilterShadow);
        if (plainFilterResult.IsError)
            Assert.Fail($"Expected success but got error: {plainFilterResult.Error}");

        Assert.Equal([1m], plainFilterResult.Value.ToAtoms());
        Assert.Equal(0, plainFilterStats.FilterCountFusionHits);
        Assert.Equal(1, plainFilterStats.FilterCountFusionFallbacks);
        Assert.Equal(1, plainFilterStats.FallbackReasons["filter does not resolve to builtin"]);

        // User count shadowing keeps the pipeline from using the builtin count
        // fusion and the shadowed count sees the filter result as one argument.
        var plainCountShadow = """
            count(value) = 999
            IsEven = x mod 2 == 0
            count(range(1, 10).filter(IsEven))
            """;

        var (plainCountResult, plainCountStats) = EvalFullWithSequenceDiagnostics(plainCountShadow);
        if (plainCountResult.IsError)
            Assert.Fail($"Expected success but got error: {plainCountResult.Error}");

        Assert.Equal([999m], plainCountResult.Value.ToAtoms());
        Assert.Equal(0, plainCountStats.FilterCountFusionHits);
        Assert.Equal(1, plainCountStats.FilterCountFusionFallbacks);
        Assert.Equal(1, plainCountStats.FallbackReasons["count does not resolve to builtin"]);
    }

    [Fact]
    public void Eval_SequencePipelineS2_FilterCount_RespectsRangeBuiltinShadowing()
    {
        var source = """
            range(start, stop) = 42
            IsEven = x mod 2 == 0
            range(1, 10).filter(IsEven).count
            """;

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([1m], result.Value.ToAtoms());
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(0, stats.DirectRangeFusionHits);
        Assert.Equal(1, stats.DirectRangeFusionFallbacks);
        Assert.Equal(1, stats.FallbackReasons["source is not builtin range"]);

        var pipeline = Assert.Single(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.Equal("generic source", pipeline.SourceKind);
        Assert.Equal("eager source collection", pipeline.SourceExecution);
        Assert.Equal("source is not builtin range", pipeline.SourceExecutionFallbackReason);
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_ExtraCountArgument_IsArityErrorInBothModes()
    {
        // count(collection) is fixed one-argument: an extra argument beside the
        // filter pipeline is an ordinary arity error, and the optimizer must
        // not recognize the over-supplied call in either mode.
        var source = """
            IsEven = x mod 2 == 0
            count(range(1, 10).filter(IsEven), 0)
            """;

        foreach (var enableSequencePipelineOptimization in new[] { false, true })
        {
            var result = EvalFull(
                source,
                enableLoopOptimization: true,
                enableSequencePipelineOptimization: enableSequencePipelineOptimization);
            if (result.IsOk)
                Assert.Fail($"Expected arity failure but got: {result.Value}");

            var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
            Assert.Equal(1, arity.Expected);
            Assert.Equal(2, arity.Actual);
        }
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterExtraArgument_IsArityErrorInBothModes()
    {
        // filter(collection, predicate) is fixed two-argument: the extra `0`
        // over-supplies the call, an ordinary arity error in both the generic
        // and the sequence-pipeline-optimized evaluator.
        var source = """
            IsEven = x mod 2 == 0
            count(filter(range(1, 10), 0, IsEven))
            """;

        foreach (var enableSequencePipelineOptimization in new[] { false, true })
        {
            var result = EvalFull(
                source,
                enableLoopOptimization: true,
                enableSequencePipelineOptimization: enableSequencePipelineOptimization);
            if (result.IsOk)
                Assert.Fail($"Expected arity failure but got: {result.Value}");

            var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
            Assert.Equal(2, arity.Expected);
            Assert.Equal(3, arity.Actual);
        }
    }

    [Fact]
    public void Eval_SequencePipelineS1_FilterCount_SquareFreeCount()
    {
        var source = """
            IsSquareFree(num) = {
                Step = {
                    Square = k * k
                    k + 1, s + if(num mod Square == 0, 1, 0), Square <= num and s <= 0
                }
                Step.while(2, 0):1 == 0
            }

            SquareFreeCount(N) = range(1, N).filter(IsSquareFree).count

            SquareFreeCount(1000)
            """;

        AssertEvalSequenceModes(source, 608);

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([608m], result.Value.ToAtoms());
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(1, stats.DirectRangeFusionHits);
        Assert.Equal(1000, stats.FilterCountPredicateCalls);
        Assert.Equal(1000, stats.AvoidedSourceMaterializations);
        var pipeline = Assert.Single(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.Equal("direct range iteration", pipeline.SourceExecution);
        Assert.Equal(1000, pipeline.SourceItemCount);
        Assert.Equal(608, pipeline.ResultCount);
        Assert.Equal(1000, pipeline.AvoidedSourceMaterializationCount);
    }

    [Fact]
    public void Eval_SequencePipelineS2_FilterCount_ImplicitPropertySquareFreeUsesDirectRange()
    {
        var source = """
            IsSquareFree(num) = {
                Step = {
                    Square = k * k
                    k + 1, s + if(num mod Square == 0, 1, 0), Square <= num and s <= 0
                }
                Step.while(2, 0):1 == 0
            }

            SquareFreeCount = range(1,N).filter(IsSquareFree).count

            SquareFreeCount(1000)
            """;

        var (result, stats) = EvalFullWithSequenceDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([608m], result.Value.ToAtoms());
        Assert.Equal(1, stats.FilterCountFusionHits);
        Assert.Equal(1, stats.DirectRangeFusionHits);
        Assert.Equal(1000, stats.FilterCountPredicateCalls);
        Assert.Equal(1000, stats.AvoidedSourceMaterializations);

        var pipeline = Assert.Single(stats.Pipelines, pipeline => pipeline.Optimized);
        Assert.Equal("dot-filter-dot-count", pipeline.Form);
        Assert.Equal("builtin range", pipeline.SourceKind);
        Assert.Equal("direct range iteration", pipeline.SourceExecution);
        Assert.Equal(1000, pipeline.SourceItemCount);
    }

    [Fact]
    public void Eval_LoopPlanner_CountedCallbackParameterFullyPlansSquareFreeInnerLoop()
    {
        var source = """
            IsSquareFree(num) = {
                Step = {
                    Square = k * k
                    k + 1, s + if(num mod Square == 0, 1, 0), Square <= num and s <= 0
                }
                Step.while(2, 0):1 == 0
            }

            SquareFreeCount = range(1,N).filter(IsSquareFree).count

            SquareFreeCount(100)
            """;

        var generic = EvalFull(
            source,
            enableLoopOptimization: false,
            enableSequencePipelineOptimization: false);
        if (generic.IsError)
            Assert.Fail($"Expected generic success but got error: {generic.Error}");

        var (result, loopStats, sequenceStats) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected optimized success but got error: {result.Error}");

        Assert.Equal(generic.Value.ToAtoms(), result.Value.ToAtoms());
        Assert.Equal(1, sequenceStats.FilterCountFusionHits);
        Assert.Equal(1, sequenceStats.DirectRangeFusionHits);
        Assert.Equal(100, sequenceStats.FilterCountPredicateCalls);
        Assert.Equal(100, sequenceStats.AvoidedSourceMaterializations);
        Assert.Equal(0, loopStats.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.True(loopStats.CountedParameterReferencesPlanned > 0);
        Assert.Equal(0, loopStats.CountedParameterReferencesFallbacks);

        var sequencePipeline = Assert.Single(sequenceStats.Pipelines, pipeline => pipeline.Optimized);
        Assert.Equal("dot-filter-dot-count", sequencePipeline.Form);
        Assert.Equal("direct range iteration", sequencePipeline.SourceExecution);

        var loopPlan = AssertSingleLoopPlan(loopStats, "IsSquareFree.Step.while");
        var squareTemp = AssertLoopTemp(loopPlan, "Square");
        Assert.True(squareTemp.Planned);
        Assert.Equal("Multiply(StateSlot(k), StateSlot(k))", squareTemp.PlanSummary);

        var output0 = AssertLoopExpression(loopPlan, "output", 0);
        var output1 = AssertLoopExpression(loopPlan, "output", 1);
        var continuation = AssertLoopExpression(loopPlan, "continuation", null);

        Assert.True(output0.Planned);
        Assert.Equal("Add(StateSlot(k), Const(1))", output0.PlanSummary);
        Assert.True(output1.Planned);
        Assert.Contains("CountedParamSlot(num)", output1.PlanSummary, StringComparison.Ordinal);
        Assert.True(continuation.Planned);
        Assert.Contains("CountedParamSlot(num)", continuation.PlanSummary, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_LoopPlanner_CountedCallbackParameterPlansMinimalNestedLoop()
    {
        var source = """
            Pred(num) = {
                Step = k + 1, k <= num
                Step.while(1):0 > 0
            }

            range(1,10).filter(Pred).count
            """;

        AssertEvalLoopModes(source, 10);

        var (result, loopStats, sequenceStats) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([10m], result.Value.ToAtoms());
        Assert.Equal(1, sequenceStats.FilterCountFusionHits);
        Assert.Equal(1, sequenceStats.DirectRangeFusionHits);
        Assert.Equal(0, loopStats.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.True(loopStats.CountedParameterReferencesPlanned > 0);
        Assert.Equal(0, loopStats.CountedParameterReferencesFallbacks);

        var plan = AssertSingleLoopPlan(loopStats, "Pred.Step.while");
        var continuation = AssertLoopExpression(plan, "continuation", null);
        Assert.True(continuation.Planned);
        Assert.Equal("LessOrEqual(StateSlot(k), CountedParamSlot(num))", continuation.PlanSummary);
    }

    [Fact]
    public void Eval_LoopPlanner_LoopStateShadowsOuterCountedCallbackParameterInWhile()
    {
        var source = """
            Inner = {
                Step = n + 1, n < limit
                Step.while(limit - limit):0
            }

            UsesInner = Inner(n)

            (2,3).map(UsesInner)
            """;

        AssertEvalLoopModes(source, 2, 3);

        var (result, loopStats, _) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([2m, 3m], result.Value.ToHostAtoms());
        Assert.Equal(0, loopStats.CountedParameterReferencesPlanned);

        var plan = AssertSingleLoopPlan(loopStats, "Inner.Step.while");
        var output = AssertLoopExpression(plan, "output", 0);
        var continuation = AssertLoopExpression(plan, "continuation", null);

        Assert.True(output.Planned);
        Assert.Equal("Add(StateSlot(n), Const(1))", output.PlanSummary);
        Assert.DoesNotContain("CountedParamSlot(n)", output.PlanSummary, StringComparison.Ordinal);

        Assert.True(continuation.Planned);
        Assert.Equal("LessThan(StateSlot(n), CapturedSlot(limit))", continuation.PlanSummary);
        Assert.DoesNotContain("CountedParamSlot(n)", continuation.PlanSummary, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_LoopPlanner_LoopStateShadowsOuterCountedCallbackParameterInRepeat()
    {
        var source = """
            Inner = {
                Step = n + 1
                Step.repeat(limit, 0):0
            }

            UsesInner = Inner(n)

            (2,3).map(UsesInner)
            """;

        AssertEvalLoopModes(source, 2, 3);

        var (result, loopStats, _) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([2m, 3m], result.Value.ToHostAtoms());
        Assert.Equal(0, loopStats.CountedParameterReferencesPlanned);

        var plan = AssertSingleLoopPlan(loopStats, "Inner.Step.repeat");
        var output = AssertLoopExpression(plan, "output", 0);

        Assert.True(output.Planned);
        Assert.Equal("Add(StateSlot(n), Const(1))", output.PlanSummary);
        Assert.DoesNotContain("CountedParamSlot(n)", output.PlanSummary, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_LoopPlanner_LoopStateShadowsOuterCountedCallbackParameterInFilter()
    {
        var source = """
            Inner = {
                Step = n + 1, n < limit
                Step.while(limit - limit):0
            }

            Keep = Inner(n) == n

            Output = (2,3).filter(Keep)
            """;

        AssertEvalLoopModes(source, 2, 3);
    }

    [Fact]
    public void Eval_LoopPlanner_LoopStateShadowsOuterCountedCallbackParameterInReduce()
    {
        var source = """
            Inner = {
                Step = n + 1
                Step.repeat(limit, 0):0
            }

            AddInner(n, acc) = acc + Inner(n)

            (2,3).reduce(AddInner, 0)
            """;

        AssertEvalLoopModes(source, 5);
    }

    [Fact]
    public void Eval_LoopPlanner_OriginalEmirpFilterCallbackNameDoesNotLeakIntoReverseStep()
    {
        var source = """
            IsPrime = {
                Step = {
                    k+1, s + if(n mod k == 0, 1, 0), k <= n div 2 and s <= 0
                }
                n > 1 and Step.while(2,0):1 == 0
            }

            Reverse = {
                Step = Math.Floor(n / 10), rev * 10 + n mod 10, n > 0
                Step.while(x, 0):1
            }

            IsEmirp = n > 11 and IsPrime(n) and IsPrime(Reverse(n))

            (11,12,13,14,15,16,17).filter(IsEmirp)
            """;

        AssertEvalLoopModes(source, 13, 17);

        var (result, loopStats, _) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([13m, 17m], result.Value.ToHostAtoms());

        var reversePlan = AssertSingleLoopPlan(loopStats, "Reverse.Step.while");
        var revOutput = AssertLoopExpression(reversePlan, "output", 1);
        var continuation = AssertLoopExpression(reversePlan, "continuation", null);

        Assert.True(revOutput.Planned);
        Assert.Contains("Mod(StateSlot(n), Const(10))", revOutput.PlanSummary, StringComparison.Ordinal);
        Assert.DoesNotContain("CountedParamSlot(n)", revOutput.PlanSummary, StringComparison.Ordinal);

        Assert.True(continuation.Planned);
        Assert.Equal("GreaterThan(StateSlot(n), Const(0))", continuation.PlanSummary);
    }

    [Fact]
    public void Eval_LoopPlanner_DifferentOuterNameKeepsInnerStateBinding()
    {
        var source = """
            Inner = {
                Step = n + 1, n < limit
                Step.while(limit - limit):0
            }

            UsesInner = Inner(m)

            (2,3).map(UsesInner)
            """;

        AssertEvalLoopModes(source, 2, 3);

        var (result, loopStats, _) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(loopStats, "Inner.Step.while");
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal("Add(StateSlot(n), Const(1))", output.PlanSummary);
    }

    [Fact]
    public void Eval_LoopPlanner_RenamedInnerStateAvoidsCallbackNameCollision()
    {
        var source = """
            Inner = {
                Step = s + 1, s < limit
                Step.while(limit - limit):0
            }

            UsesInner = Inner(n)

            (2,3).map(UsesInner)
            """;

        AssertEvalLoopModes(source, 2, 3);

        var (result, loopStats, _) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var plan = AssertSingleLoopPlan(loopStats, "Inner.Step.while");
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal("Add(StateSlot(s), Const(1))", output.PlanSummary);
    }

    [Fact]
    public void Eval_LoopPlanner_UnshadowedOuterCountedCallbackParameterRemainsVisible()
    {
        var source = """
            UsesLimit = {
                Step = s + 1, s < limit
                Step.while(limit - limit):0
            }

            (2,3).map(UsesLimit)
            """;

        AssertEvalLoopModes(source, 2, 3);

        var (result, loopStats, _) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([2m, 3m], result.Value.ToHostAtoms());
        Assert.True(loopStats.CountedParameterReferencesPlanned > 0);

        var plan = AssertSingleLoopPlan(loopStats, "UsesLimit.Step.while");
        var continuation = AssertLoopExpression(plan, "continuation", null);
        Assert.True(continuation.Planned);
        Assert.Equal("LessThan(StateSlot(s), CountedParamSlot(limit))", continuation.PlanSummary);
    }

    [Fact]
    public void Eval_LoopPlanner_DirectCallCapturedSlotPlanningRemainsUnchanged()
    {
        var source = """
            Pred(num) = {
                Step = k + 1, k <= num
                Step.while(1):0
            }

            Pred(10)
            """;

        AssertEvalLoopModes(source, 11);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([11m], result.Value.ToAtoms());
        Assert.Equal(0, stats.CountedParameterReferencesPlanned);
        Assert.Equal(0, stats.CountedParameterReferencesFallbacks);

        var plan = AssertSingleLoopPlan(stats, "Pred.Step.while");
        var continuation = AssertLoopExpression(plan, "continuation", null);
        Assert.True(continuation.Planned);
        Assert.Equal("LessOrEqual(StateSlot(k), CapturedSlot(num))", continuation.PlanSummary);
        Assert.DoesNotContain("CountedParamSlot", continuation.PlanSummary, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_LoopPlanner_CountedCallbackParameterNonNumericShapeFallsBack()
    {
        var source = """
            Pred(text) = {
                Step = if(text == 'a', k + 1, k + 1), k <= 1
                Step.while(0):0 > 0
            }

            ('a').filter(Pred).count
            """;

        AssertEvalLoopModes(source, 1);

        var (result, loopStats, sequenceStats) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([1m], result.Value.ToAtoms());
        Assert.Equal(1, sequenceStats.FilterCountFusionHits);
        Assert.Equal(1, loopStats.CountedParameterReferencesFallbacks);
        Assert.Contains(
            loopStats.FallbackReasons,
            reason => reason.Key == "unsupported counted parameter value shape: text (counted parameter is non-numeric: 'a')");

        var plan = AssertSingleLoopPlan(loopStats, "Pred.Step.while");
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.False(output.Planned);
        Assert.Equal(
            "unsupported if condition: unsupported counted parameter value shape: text (counted parameter is non-numeric: 'a')",
            output.FallbackReason);
    }

    [Fact]
    public void Eval_LoopPlanner_CountedCallbackParameterSequenceValueMultiEmitShapeFallsBack()
    {
        var source = """
            Pred(item) = {
                Step = if(1, k + 1, item), k <= 1
                Step.while(0):0 > 0
            }

            (((1, 2), (3, 4))).filter(Pred).count
            """;

        AssertEvalLoopModes(source, 2);

        var (result, loopStats, sequenceStats) = EvalFullWithOptimizationDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([2m], result.Value.ToAtoms());
        Assert.Equal(1, sequenceStats.FilterCountFusionHits);
        Assert.Equal(0, loopStats.CountedParameterReferencesPlanned);
        Assert.Equal(2, loopStats.CountedParameterReferencesFallbacks);
        Assert.Contains(
            loopStats.FallbackReasons,
            reason => reason.Key == "unsupported counted parameter value shape: item (counted parameter emitted multiple values (2))");

        var plan = AssertSingleLoopPlan(loopStats, "Pred.Step.while");
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.False(output.Planned);
        Assert.Equal(
            "unsupported if false branch: unsupported counted parameter value shape: item (counted parameter emitted multiple values (2))",
            output.FallbackReason);

        var continuation = AssertLoopExpression(plan, "continuation", null);
        Assert.True(continuation.Planned);
        Assert.Equal("LessOrEqual(StateSlot(k), Const(1))", continuation.PlanSummary);
    }

    [Fact]
    public void Eval_Count_EmptySequence_ReturnsZero()
        => AssertEval("count(())", 0);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_EmptyFilterReceiver_RespectsEmptyPolicies()
    {
        AssertEval("(1, 5, 3).filter{ n mod 2 == 0 }.sum", 0);
        AssertBuiltinFailureWithExactContext(
            "(1, 5, 3).filter{ n mod 2 == 0 }.first",
            "first requires a non-empty collection");
        AssertBuiltinFailureWithExactContext(
            "(1, 5, 3).filter{ n mod 2 == 0 }.last",
            "last requires a non-empty collection");
    }

    [Fact]
    public void Eval_EmptySequence_IsEmptySequenceValue()
        => AssertEvalEmptyOutput("()");

    [Fact]
    public void Eval_EmptySequence_AndNestedEmpty_CanonicalizeToSameValue()
    {
        var empty = Assert.IsType<Result.SequenceValue>(EvalFull("()").Value);
        Assert.Empty(empty.Items);

        var nested = Assert.IsType<Result.SequenceValue>(EvalFull("(())").Value);
        Assert.Empty(nested.Items);

        var deeper = Assert.IsType<Result.SequenceValue>(EvalFull("((()))").Value);
        Assert.Empty(deeper.Items);
    }

    [Fact]
    public void Eval_EmptySequence_CountsAsZeroItems()
    {
        AssertEval("()");
        AssertEval("().count", 0);
        AssertEval("count(())", 0);
    }

    [Fact]
    public void Eval_NestedEmptySequence_CanonicalizesToZeroItems()
    {
        AssertEval("(()).count", 0);
        AssertEval("count((()))", 0);
        AssertEval("A = ()\nA.count", 0);
        AssertEval("A = (())\nA.count", 0);
    }

    // ── Collection builtins return exact immutable list values: kept items stay
    //    exact list elements (a one-element list [item] is NEVER erased to the
    //    item), and zero kept items form the empty list [] ──

    [Fact]
    public void Eval_Filter_NestedEmptyInput_CanonicalizesToEmptyList()
        => AssertEvalCounted(
            """
            AlwaysTrue(x) = 1
            filter((()), AlwaysTrue)
            """,
            1,
            ListValue());

    [Fact]
    public void Eval_Count_FilterNestedEmptyInput_CountsZeroItems()
        => AssertEval(
            """
            AlwaysTrue(x) = 1
            count(filter((()), AlwaysTrue))
            """,
            0);

    [Fact]
    public void Eval_Take_SingleSequenceValueItem_StaysExactListElement()
        => AssertEvalCounted("take(((1, 2), (3, 4)), 1)", 1, ListValue(SequenceValue(Atom(1), Atom(2))));

    [Fact]
    public void Eval_Skip_SingleSequenceValueItem_StaysExactListElement()
        => AssertEvalCounted("skip(((1, 2), (3, 4)), 1)", 1, ListValue(SequenceValue(Atom(3), Atom(4))));

    [Fact]
    public void Eval_Distinct_SingleSequenceValueItem_StaysExactListElement()
        => AssertEvalCounted("distinct(((1, 2), (1, 2)))", 1, ListValue(SequenceValue(Atom(1), Atom(2))));

    [Fact]
    public void Eval_Filter_KeepsSingleNonEmptySequenceValueItem_StaysExactListElement()
    {
        // Filtering a two-item collection down to one kept sequence-valued item
        // keeps that item as an exact list element: the result is [(1, 2)] —
        // no singleton erasure ever applies to list structure.
        var result = EvalFull(
            """
            KeepFirstPair(pair) = pair:0 == 1
            filter(((1, 2), (3, 4)), KeepFirstPair)
            """);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertListOfSequenceValueAtoms(result.Value, [1m, 2m]);
    }

    [Fact]
    public void Eval_Take_SingleKeptItem_ReproAgreesAcrossObservations()
    {
        // T is the exact list [(1, 2)]: display, count(T), T.count, equality, and
        // indexing all observe the same one-element list value. Lists are not
        // equal to sequences, and `:` indexing selects the stored element
        // exactly (T:0 is the kept `(1, 2)` element, projected one level like
        // any selected sequence element).
        AssertEvalCounted("T = take(((1, 2), (3, 4)), 1)\nT", 1, ListValue(SequenceValue(Atom(1), Atom(2))));
        AssertEval("T = take(((1, 2), (3, 4)), 1)\ncount(T)", 1);
        AssertEval("T = take(((1, 2), (3, 4)), 1)\nT.count", 1);
        AssertEval("T = take(((1, 2), (3, 4)), 1)\nT == (1, 2)", 0);
        AssertEval("T = take(((1, 2), (3, 4)), 1)\nT == ((1, 2))", 0);
        AssertEval("T = take(((1, 2), (3, 4)), 1)\nT == [(1, 2)]", 1);
        AssertEvalCounted("T = take(((1, 2), (3, 4)), 1)\nT:0", 2, SequenceValue(Atom(1), Atom(2)));
    }

    [Fact]
    public void Eval_Distinct_SingleKeptEmptyItem_StaysExactListElement()
    {
        // distinct(((), ())) dedups the collection's two equal `()` items to one
        // kept item; the kept `()` stays an exact list element, so the result is
        // [()] (one element, count 1) and is NOT equal to the empty sequence `()`.
        AssertEvalCounted("distinct(((), ()))", 1, ListValue(SequenceValue()));
        AssertEval("count(distinct(((), ())))", 1);
        AssertEval("distinct(((), ())) == ()", 0);

        // The old bare two-argument form over-supplies the fixed
        // distinct(collection) signature.
        AssertEvalFailsWithArityMismatch("distinct((), ())", expected: 1, actual: 2);
    }

    [Fact]
    public void Eval_Take_MultipleEmptyItems_PreservesSiblingBoundaries()
    {
        // Kept empty-sequence items stay exact list elements with their sibling
        // boundaries preserved raw: take(((), ()), 2) is [(), ()] — never
        // collapsed or dropped.
        AssertEvalCounted("take(((), ()), 2)", 1, ListValue(SequenceValue(), SequenceValue()));
        AssertEval("count(take(((), ()), 2))", 2);
        AssertEvalCounted("distinct(((), (), 1))", 1, ListValue(SequenceValue(), Atom(1)));

        // The old bare form supplied the empty items as separate arguments —
        // now an ordinary arity error against take(collection, count).
        AssertEvalFailsWithArityMismatch("take((), (), 2)", expected: 2, actual: 3);
    }

    [Fact]
    public void Eval_Filter_SingleKeptEmptyItem_StaysExactListElement()
    {
        // Filtering down to exactly one kept `()` item returns the exact list
        // [()]: one visible output slot whose one element is the empty sequence.
        AssertEvalCounted(
            """
            KeepEmpty(x) = x.count == 0
            filter(((), 1), KeepEmpty)
            """,
            1,
            ListValue(SequenceValue()));
        AssertEval(
            """
            KeepEmpty(x) = x.count == 0
            count(filter(((), 1), KeepEmpty))
            """,
            1);

        // The old bare three-argument form over-supplies the fixed
        // filter(collection, predicate) signature.
        AssertEvalFailsWithArityMismatch(
            """
            KeepEmpty(x) = x.count == 0
            filter((), 1, KeepEmpty)
            """,
            expected: 2,
            actual: 3);
    }

    [Fact]
    public void Eval_MixedOutput_LeadingNonSpreadEmptyIsVisibleSlot()
    {
        // A normal non-spread `()` output is a visible slot beside `1`, not dropped.
        var result = EvalFull("()\n1");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var outer = Assert.IsType<Result.SequenceValue>(result.Value);
        Assert.Equal(2, outer.Items.Count);
        Assert.Empty(Assert.IsType<Result.SequenceValue>(outer.Items[0]).Items);
        Assert.Equal(1m, Assert.IsType<Result.Atom>(outer.Items[1]).Value);
    }

    [Fact]
    public void Eval_MixedOutput_MiddleNonSpreadEmptyIsVisibleSlot()
    {
        var result = EvalFull("1\n()\n2");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var outer = Assert.IsType<Result.SequenceValue>(result.Value);
        Assert.Equal(3, outer.Items.Count);
        Assert.Equal(1m, Assert.IsType<Result.Atom>(outer.Items[0]).Value);
        Assert.Empty(Assert.IsType<Result.SequenceValue>(outer.Items[1]).Items);
        Assert.Equal(2m, Assert.IsType<Result.Atom>(outer.Items[2]).Value);
    }

    [Fact]
    public void Eval_MixedOutput_SpreadOfEmptyContributesNoSlot()
        // Only an explicit spread drops to zero: `().spread` adds no slot, so `().spread` then `1` is just `1`.
        => AssertEval("().spread\n1", 1);

    [Fact]
    public void Eval_PropertyOnlyProgram_HasNoDefinedOutput()
        => AssertMissingOutputMessage(
            "T = 4",
            RunResult.NoProgramOutput.DefaultMessage);

    [Fact]
    public void Eval_PropertyOnlyProgram_WithTrailingOutput_ReturnsValue()
        => AssertEval("T = 4\nT", 4);

    [Fact]
    public void Eval_PropertyOnlyProgram_WithEmptySequenceOutput_ReturnsEmptySequence()
        => AssertEvalEmptyOutput("T = 4\n()");

    [Fact]
    public void Eval_PropertyValue_DoesNotCompareEqualToEmptySequence()
        => AssertEval("T = 4\nT == ()", 0);

    [Fact]
    public void Eval_MultiplePropertyDefinitionsWithoutOutput_HasNoDefinedOutput()
        => AssertMissingOutputMessage(
            """
            Price = 10
            Tax = 2
            Total = Price + Tax
            """,
            RunResult.NoProgramOutput.DefaultMessage);

    [Fact]
    public void Eval_MultiplePropertyDefinitionsWithOutput_ReturnsValue()
        => AssertEval(
            """
            Price = 10
            Tax = 2
            Total = Price + Tax
            Total
            """,
            12);

    [Fact]
    public void Eval_Empty_IsOrdinaryIdentifier()
        => AssertEval("empty = 123\nempty", 123);

    [Fact]
    public void Eval_EmptySequence_Equality()
    {
        AssertEval("() == ()", 1);
        AssertEval("() != ()", 0);
        AssertEval("() == (())", 1);
        AssertEval("() != (())", 0);
        AssertEval("(()) == (())", 1);
        AssertEval("A = ()\nA == ()", 1);
        // Collection-builtin results are exact lists: the empty list [] is NOT
        // equal to the empty sequence ().
        AssertEval(
            """
            IsEven = x mod 2 == 0
            filter((1, 3, 5), IsEven) == ()
            """,
            0);
        AssertEval(
            """
            IsEven = x mod 2 == 0
            () == filter((1, 3, 5), IsEven)
            """,
            0);
        AssertEval("(0).skip(1) == ()", 0);
    }

    [Fact]
    public void Eval_NoOutputBody_IsNotTheEmptySequenceValue()
    {
        // `{}` and other no-output bodies are not values: they have no defined
        // output and so are not comparable with the empty sequence value `()`.
        foreach (var source in new[]
        {
            "{}",
            "{}.count",
            "count({})",
            "{} == ()",
            "() == {}",
            "C = {}\nC.count",
            "Lib = {\n  Prop = 7\n}\nLib.count",
            "Lib = {\n  Prop = 7\n}\nLib == ()",
        })
        {
            AssertEvalFailsWithMissingOutput(source);
        }
    }

    [Fact]
    public void Eval_EmptySequence_IsAValue_NotMissingOutput()
    {
        // In contrast to no-output bodies, `()` is a real value: it can be stored,
        // counted, and compared.
        AssertEvalEmptyOutput("()");
        AssertEval("().count", 0);
        AssertEval("D = ()\nD.count", 0);
        AssertEval("D = ()\nD == ()", 1);
    }

    [Fact]
    public void Eval_MissingOutput_EmptyBraceBody_UsesEmptySequenceHint()
        => AssertMissingOutputMessage(
            "{}",
            "Algorithm has no defined output.\nAdd an output expression, or use `()` if the empty sequence value was intended.",
            expectedLine: 1,
            expectedColumn: 1);

    [Fact]
    public void Eval_NamedEmptySequenceVersusNoOutputBody_StayDistinct()
    {
        // `()` stored in a property is a real value: returning it directly yields `()`,
        // and it compares equal to `()`.
        AssertEvalEmptyOutput("A = ()\nA");
        AssertEval("A = ()\nA == ()", 1);

        // `{}` stored in a property is no-output: forcing it (directly, or as an operand
        // of `==`) fails with missing-output before any value or equality is produced.
        // It must not behave like `()` — neither `1` nor `0`.
        AssertEvalFailsWithMissingOutput("A = {}\nA");
        AssertEvalFailsWithMissingOutput("A = {}\nA == ()");

        // A no-output body must not become a visible empty-sequence slot in mixed output:
        // evaluating the `{}` slot fails with missing-output rather than contributing `()`.
        AssertEvalFailsWithMissingOutput("{}, 1");
    }

    [Fact]
    public void Eval_Count_DescendingRange_CountsTopLevelItems()
        => AssertEval("count(range(5, 1))", 5);

    [Fact]
    public void Eval_Count_SequenceValueElements_CountsSequenceItems()
        => AssertEval("count(((1, 2), (3, 4)))", 2);

    [Fact]
    public void Eval_Count_SingleAtomicInput_ReturnsOne()
        => AssertEval("count(5)", 1);

    [Fact]
    public void Eval_Count_StringInput_ReturnsOne()
        => AssertEval("count('hello')", 1);

    [Fact]
    public void Eval_Count_DirectCallMultiArgs_CountsTopLevelItems()
        => AssertEval("count((1, 7))", 2);

    [Fact]
    public void Eval_Count_DirectCallMixedArgs_CountsExpandedTopLevelItems()
        => AssertEval("count((3, 4, range(1, 5).spread, 7))", 8);

    [Fact]
    public void Eval_Count_SingleSequenceValueArg_CountsSequenceItems()
        => AssertEval("count((1, 7))", 2);

    [Fact]
    public void Eval_Count_SequenceValueMultiArgs_CountTopLevelGroups()
        => AssertEval("count(((1, 2), (3, 4)))", 2);

    [Fact]
    public void Eval_Count_InlineParenReceiver_DotCallDestructuresSequence()
        => AssertEval("(1, 7).count", 2);

    [Fact]
    public void Eval_SequenceReceiverBoundary_NamedPropertyOutputsPreserveEmittedSlots()
    {
        AssertEval(
            """
            A = 1, 2, 3
            A.take(2)
            """,
            1,
            2);

        AssertEval(
            """
            A = 1, 2, 3
            A.count
            """,
            3);
    }

    [Fact]
    public void Eval_SequenceReceiverBoundary_NamedSequenceValuePropertyIsSequenceValue()
    {
        AssertEval(
            """
            A = (1, 2, 3)
            A.count
            """,
            3);

        var takeResult = EvalFull(
            """
            A = (1, 2, 3)
            A.take(2)
            """);

        if (takeResult.IsError)
            Assert.Fail($"Expected success but got error: {takeResult.Error}");

        AssertEval(
            """
            A = (1, 2, 3)
            A.take(2)
            """,
            1,
            2);
    }

    [Fact]
    public void Eval_SequenceReceiverBoundary_SequenceSpreadPropertyExposesSpreadSlots()
        => AssertEval(
            """
            A = 1.spread 2.spread 3
            A.take(2)
            """,
            1,
            2);

    [Fact]
    public void Eval_SequenceSpread_NamedSequenceValueOperandPreservesEmittedBoundary()
    {
        var result = EvalFull(
            """
            A = (1, 2)
            A.spread 3
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertSequenceValueAtoms(result.Value, 1, 2, 3);
    }

    [Fact]
    public void Eval_SequenceReceiverBoundary_UserCallsPreserveEmittedSlots()
    {
        AssertEval(
            """
            F(x) = x, x + 1, x + 2
            F(1).count
            F(1).take(2)
            """,
            3,
            1,
            2);

        AssertEval(
            """
            G(x) = (x, x + 1, x + 2)
            G(1).count
            """,
            3);
    }

    [Fact]
    public void Eval_SequenceReceiverBoundary_ConditionalBranchesPreserveEmittedSlots()
    {
        AssertEval(
            """
            ChooseMulti(1) = 1, 2, 3
            ChooseMulti(x) = 4, 5, 6
            ChooseSequenceValue(1) = (1, 2, 3)
            ChooseSequenceValue(x) = (4, 5, 6)
            ChooseMulti(1).take(2)
            ChooseSequenceValue(1).count
            """,
            1,
            2,
            3);
    }

    [Fact]
    public void Eval_ParenthesizedSequenceSpread_PropertyEmitsOneSequenceValueResult()
    {
        var source = """
            A = 1, 2
            B = 3, 4
            Test = (A.spread B)
            Test.count
            """;

        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_ParenthesizedSequenceSpread_VariadicCallArgumentIsOneSequenceValue()
    {
        // `(A.spread B)` materializes one sequence value (1, 2, (3, 4)), which the
        // call supplies as one argument: the variadic parameter collects [that value].
        var source = """
            A = 1, 2
            B = 3, 4
            F(values...) = values.count
            F((A.spread B))
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_BareSequenceSpread_AdjacentExpressionBindsItemSupply()
    {
        // A.spread B is three slots (1, 2, (3, 4)); F(values...) binds them as one
        // sequence value of count 3.
        var source = """
            A = 1, 2
            B = 3, 4
            F(values...) = values.count
            F(A.spread B)
            """;

        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_UserDefinedVariadicDotCallReceiver_CountsOneReceiverArgument()
    {
        // The receiver is one leading argument, so the variadic parameter collects the
        // one-element list [(1, 2)]. Lean twin: `(1, 2).CountItems` is 1.
        var source = """
            CountItems(items...) = items.count
            Output = (1, 2).CountItems
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_UserDefinedVariadicDotCallReceiver_SpreadReceiverBindsItemsForBody()
    {
        // The parenthesized-spread receiver pre-expands the sequence's items,
        // so the variadic parameter collects [1, 2] and the numeric body works.
        var source = """
            Mean(vector...) = vector.sum
            Output = ((1, 2).spread).Mean
            """;

        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_UserDefinedVariadicDotCallReceiver_PreservesSingleGroupedValueBeforeSuffixAllocation()
    {
        // Sum(values..., last) receives Values as one argument. `last` receives
        // the sequence value, so the numeric body fails unless Values.spread is used.
        var source = """
            Values = 10, 20
            Sum(values..., last) = values.sum + last
            Values.Sum
            """;

        AssertEvalFails(source);
    }

    // Dot-call receiver symmetry: receiver.F(C, D) == F(receiver, C, D)
    // and (receiver.spread).F(C, D) == F(receiver.spread, C, D). An ordinary
    // receiver is one leading argument slot even for callees with a leading
    // flat variadic parameter; explicit receiver spread spreads the
    // receiver's emitted top-level values. A sequence-valued property such as
    // Pair = (10, 20) emits ONE sequence value, so even its spread spreads a
    // single sequence value (spread preserves named sequence-value operand
    // boundaries); a multi-output property such as Values = 10, 20 is where
    // ordinary-slot allocation and explicit spread observably differ.
    // Lean: CoreTests dot-call receiver symmetry guards.

    [Fact]
    public void Eval_SequenceValueReceiver_LeadingFlatVariadic_IsOneReceiverArgument()
    {
        // The ordinary receiver is one leading argument even for a single-variadic
        // callee, so the capture is the one-element list [(10, 20)].
        var source = """
            NItems(values...) = values.count
            Pair = (10, 20)
            Pair.NItems
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_SequenceValueReceiverSpread_BindsSpreadSlotsAsItemSupply()
    {
        // NItems(values...) consumes an item supply: (Pair.spread) spreads into two
        // slots [10, 20], bound as a sequence value of count 2.
        var source = """
            NItems(values...) = values.count
            Pair = (10, 20)
            (Pair.spread).NItems
            """;

        AssertEval(source, 2);
    }

    [Fact]
    public void Eval_SequenceValueReceiver_LeadingFlatVariadicWithSuffix_IsOneReceiverArgument()
    {
        // Two supplied arguments: the receiver and 99. The suffix binds 99 from
        // the back and the variadic parameter collects the one-element list [(10, 20)].
        var source = """
            BeforeLastCount(values..., last) = values.count
            Pair = (10, 20)
            Pair.BeforeLastCount(99)
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_SequenceValueReceiverSpreadWithSuffix_OverSuppliesVariadicByDeconstruction()
    {
        // BeforeLastCount(values..., last) is a comma deconstruction parameter
        // list, so the spread receiver's two items plus the suffix 99 give three
        // items: the variadic captures [10, 20] (count 2) and last binds 99.
        var source = """
            BeforeLastCount(values..., last) = values.count
            Pair = (10, 20)
            (Pair.spread).BeforeLastCount(99)
            """;

        AssertEval(source, 2);
    }

    [Fact]
    public void Eval_SequenceValueArgument_CanonicalCall_MatchesSequenceValueReceiverDotCall()
    {
        // Canonical-call twin of the dot-call above: Pair is one argument, so
        // the variadic parameter collects [(10, 20)] — count 1, matching Pair.BeforeLastCount(99).
        var source = """
            BeforeLastCount(values..., last) = values.count
            Pair = (10, 20)
            BeforeLastCount(Pair, 99)
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_SequenceValueSpreadArgument_CanonicalCall_OverSuppliesVariadicByDeconstruction()
    {
        // Canonical-call twin: Pair.spread spreads into [10, 20] and 99 fills the
        // suffix, so the deconstruction matcher captures [10, 20] (count 2).
        var source = """
            BeforeLastCount(values..., last) = values.count
            Pair = (10, 20)
            BeforeLastCount(Pair.spread, 99)
            """;

        AssertEval(source, 2);
    }

    [Fact]
    public void Eval_MultiOutputReceiver_DotCallMatchesCanonicalCalls()
    {
        // The dot-call always matches its canonical-call twin. The ordinary forms
        // pass one sequence-valued slot (rest collects [(10, 20)], count 1); the
        // spread forms pass two separate slots (rest collects [10, 20], count 2).
        var define = """
            NItems(values...) = values.count
            Values = 10, 20

            """;
        AssertEval(define + "Values.NItems", 1);
        AssertEval(define + "NItems(Values)", 1);
        AssertEval(define + "(Values.spread).NItems", 2);
        AssertEval(define + "NItems(Values.spread)", 2);
    }

    [Fact]
    public void Eval_MultiOutputReceiverWithSuffix_DotCallMatchesCanonicalCalls()
    {
        var define = """
            BeforeLastCount(values..., last) = values.count
            Values = 10, 20

            """;
        // Each dot-call agrees with its canonical-call twin. The ordinary forms
        // pass one sequence-valued slot plus the suffix (rest collects
        // [(10, 20)], count 1); the spread forms open the receiver before suffix
        // allocation (rest collects [10, 20], count 2).
        AssertEval(define + "Values.BeforeLastCount(99)", 1);
        AssertEval(define + "BeforeLastCount(Values, 99)", 1);
        AssertEval(define + "(Values.spread).BeforeLastCount(99)", 2);
        AssertEval(define + "BeforeLastCount(Values.spread, 99)", 2);
    }

    [Fact]
    public void Eval_OrdinaryMultiOutputArgument_PreservesSingleGroupedValueAtSuffixAllocation()
    {
        // Sum(values..., last) receives Values as one argument. `last` receives
        // the sequence value, so the numeric body fails unless Values.spread is used.
        var source = """
            Sum(values..., last) = values.sum + last
            Values = 10, 20
            Sum(Values)
            """;

        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_SpreadMultiOutputReceiver_BindsWhenSpreadSlotsMatchSuffixShape()
    {
        // Explicit spread spreads 10 and 20 as separate items before slot
        // allocation, so `last` binds 20 and the variadic captures [10].
        var define = """
            Sum(values..., last) = values.sum + last
            Values = 10, 20

            """;
        AssertEval(define + "(Values.spread).Sum", 30);
        AssertEval(define + "Sum(Values.spread)", 30);
    }

    [Fact]
    public void Eval_UserDefinedNonVariadicDotCallReceiver_PassesCanonicalSequenceArgument()
    {
        var source = """
            CountOne(value) = value.count
            Output = (1, 2).CountOne
            """;

        AssertEval(source, 2);
    }

    [Fact]
    public void Eval_ParenthesizedSequenceSpread_DirectDotCallReceiverExpandsOneLayer()
    {
        var source = """
            A = 1, 2
            B = 3, 4
            (A.spread B).count
            """;

        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_DoubleParenthesizedSequenceSpread_DotCallReceiverPreservesNestedLayer()
    {
        var source = """
            A = 1, 2
            B = 3, 4
            ((A.spread B)).count
            """;

        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Count_WrapperMultiOutputBoundary_CountsExpandedTopLevelItems()
    {
        var source = """
            Values = 1, 2, 3
            count(Values)
            """;

        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Count_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            count(Data:0)
            (Data:0).count
            """;

        AssertEval(source, 5, 5);
    }

    [Fact]
    public void Eval_Count_ProjectedExpressionAndNamedProjectionAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            Projected = Data:0
            count(Data:0)
            count(Projected)
            """;

        AssertEval(source, 5, 5);
    }

    // Direct-consumer regressions for variadic-style top-level binding.

    [Fact]
    public void Eval_SequenceBoundaryLaw_NumericDirectConsumersExpandCommaSeparatedNamedSources()
    {
        var dataSource = "Data = 3, 4, 5, 6\n";

        AssertEval(dataSource + "sum(Data)", 18);
        AssertEval(dataSource + "sum((Data.spread, 8))", 26);

        AssertEval(dataSource + "min(Data)", 3);
        AssertEval(dataSource + "min((Data.spread, 8))", 3);

        AssertEval(dataSource + "max(Data)", 6);
        AssertEval(dataSource + "max((Data.spread, 8))", 8);

        AssertEval(dataSource + "avg(Data)", 4.5m);
        AssertEval(dataSource + "avg((Data.spread, 8))", 5.2m);
    }

    [Fact]
    public void Eval_SequenceBoundaryLaw_SlicingDistinctAndOrderingExpandCommaSeparatedNamedSources()
    {
        var dataSource = "Data = 3, 4, 5, 6\n";

        AssertEval(dataSource + "skip(Data, 1)", 4, 5, 6);
        AssertEval(dataSource + "skip((Data.spread, 8), 1)", 4, 5, 6, 8);

        AssertEval(dataSource + "count(distinct(Data))", 4);
        AssertEval(dataSource + "count(distinct((Data.spread, 4)))", 4);

        AssertEval(dataSource + "orderDesc(Data)", 6, 5, 4, 3);
        AssertEval(dataSource + "orderDesc((Data.spread, 8))", 8, 6, 5, 4, 3);
    }

    // ── Contains builtin ─────────────────────────────────────────────────────

    [Fact]
    public void Eval_Contains_OrdinaryBuiltinCall_SearchesExpandedRangeTopLevelItems()
        => AssertEval("contains(range(1, 5), 3)", 1);

    [Fact]
    public void Eval_Contains_OrdinaryBuiltinCall_DoesNotTreatRangeAsOneSequenceValue()
        => AssertEval("contains(range(1, 5), (1, 2, 3, 4, 5))", 0);

    [Fact]
    public void Eval_Contains_DotCall_MatchesPlainCallReceiverSemantics()
        => AssertEval("range(1, 5).contains(4)", 1);

    [Fact]
    public void Eval_Contains_DirectCallMixedArgs_SearchesExpandedRangeTopLevelItems()
        => AssertEval("contains((3, 4, range(1, 5).spread, 7), 5)", 1);

    [Fact]
    public void Eval_Contains_DirectCallMixedArgs_DoesNotMatchExpandedRangeAsSequenceValue()
        => AssertEval("contains((3, 4, range(1, 5).spread, 7), (1, 2, 3, 4, 5))", 0);

    [Fact]
    public void Eval_Contains_SequenceValueItem_UsesOrdinaryValueEquality()
        => AssertEval("contains((1, 2), 1)", 1);

    [Fact]
    public void Eval_Contains_DoesNotSearchInsideNestedSequenceValueMembers()
        => AssertEval("contains(((1, 2), (3, 4)), (1, 2))", 1);

    [Fact]
    public void Eval_Contains_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            contains(Data:0, 4)
            (Data:0).contains(4)
            """;

        AssertEval(source, 1, 1);
    }

    [Fact]
    public void Eval_Contains_MultiOutputSearchedItem_UsesFinalTopLevelItemAsSuffix()
    {
        var source = """
            Item = 1, 2
            contains((1, 2), Item)
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_Contains_OneArgument_IsArityError()
    {
        // contains(collection, item) is fixed two-argument, so contains(1) is
        // an ordinary arity error. Searching nothing is spelled with an
        // explicit empty collection argument and finds nothing.
        AssertEvalFailsWithArityMismatch("contains(1)", expected: 2, actual: 1);
        AssertEval("contains((), 2)", 0m);
    }

    // ── First/last builtins ────────────────────────────────────────────────

    [Fact]
    public void Eval_First_OrdinaryBuiltinCall_ReturnsFirstExpandedRangeItem()
        => AssertEval("first(range(1, 5))", 1);

    [Fact]
    public void Eval_Last_OrdinaryBuiltinCall_ReturnsLastExpandedRangeItem()
        => AssertEval("last(range(1, 5))", 5);

    [Fact]
    public void Eval_First_DotCall_ReturnsFirstExpandedRangeItem()
        => AssertEval("range(1, 5).first", 1);

    [Fact]
    public void Eval_Last_DotCall_ReturnsLastExpandedRangeItem()
        => AssertEval("range(1, 5).last", 5);

    [Fact]
    public void Eval_First_DirectCallMultiResult_Shorthand_ReturnsFirstOutput()
        => AssertEval("first((1, 2, 3))", 1);

    [Fact]
    public void Eval_Last_DirectCallMultiResult_Shorthand_ReturnsLastOutput()
        => AssertEval("last((1, 2, 3))", 3);

    [Fact]
    public void Eval_First_SingleSequenceValueArg_ReturnsFirstSequenceItem()
        => AssertEval("first((1, 2))", 1);

    [Fact]
    public void Eval_First_MultiArgSequenceValueInputs_PreservesFirstGroup()
    {
        var result = EvalFull("first(((1, 2), (3, 4)))");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertSequenceValueAtoms(result.Value, 1, 2);
    }

    [Fact]
    public void Eval_Last_SingleSequenceValueArg_ReturnsLastSequenceItem()
        => AssertEval("last((1, 2))", 2);

    [Fact]
    public void Eval_Last_MultiArgSequenceValueInputs_PreservesLastGroup()
    {
        var result = EvalFull("last(((1, 2), (3, 4)))");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertSequenceValueAtoms(result.Value, 3, 4);
    }

    [Fact]
    public void Eval_First_PropertyOutput_PreservesBoundaryItem()
    {
        var source = """
            Values = 4, 5, 6
            Head = Values.first
            Head
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Last_IntermediateProperty_PreservesBoundaryItem()
    {
        var source = """
            Values = 4, 5, 6
            Tail = Values.last
            Tail
            """;

        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_First_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            first(Data:0)
            (Data:0).first
            """;

        AssertEval(source, 7, 7);
    }

    [Fact]
    public void Eval_Last_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            last(Data:0)
            (Data:0).last
            """;

        AssertEval(source, 1, 1);
    }

    [Fact]
    public void Eval_First_InlineParenReceiver_DotCallPreservesBoundary()
        => AssertEval("(4, 5, 6).first", 4);

    [Fact]
    public void Eval_Last_InlineParenReceiver_DotCallPreservesBoundary()
        => AssertEval("(4, 5, 6).last", 6);

    // ── Distinct builtin ───────────────────────────────────────────────────

    [Fact]
    public void Eval_Distinct_OrdinaryBuiltinCall_RemovesLaterDuplicatesPreservingFirstOccurrence()
        => AssertEval("distinct((3, 1, 3, 2, 1, 2))", 3, 1, 2);

    [Fact]
    public void Eval_Distinct_DotCall_PreservesNamedBoundaryItem()
    {
        var source = """
            Values = 3, 1, 3, 2, 1, 2
            Values.distinct
            """;

        AssertEval(source, 3, 1, 2);
    }

    [Fact]
    public void Eval_Distinct_AllEqualInput_ReturnsSingleValue()
        => AssertEval("distinct((4, 4, 4, 4))", 4);

    [Fact]
    public void Eval_Distinct_AlreadyDistinctInput_PreservesOrder()
        => AssertEval("distinct((1, 2, 3))", 1, 2, 3);

    [Fact]
    public void Eval_Distinct_SequenceValueItems_RemoveDuplicateGroupsByValue()
    {
        var result = EvalFull("distinct(((1, 2), (1, 2), (3, 4)))");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertListOfSequenceValueAtoms(result.Value, [1m, 2m], [3m, 4m]);
    }

    [Fact]
    public void Eval_Distinct_SequenceValueWrapperOutput_PreservesSingleSequenceValueItem()
    {
        var source = """
            Values = ((1, 2), (1, 2), (3, 4))
            distinct(Values)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertListOfSequenceValueAtoms(result.Value, [1m, 2m], [3m, 4m]);
    }

    [Fact]
    public void Eval_Distinct_MultiOutputWrapper_DeduplicatesExpandedTopLevelItems()
    {
        var source = """
            Values = (1, 2), (1, 2), (3, 4)
            distinct(Values)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertListOfSequenceValueAtoms(result.Value, [1m, 2m], [3m, 4m]);
    }

    [Fact]
    public void Eval_Distinct_InlineParenReceiver_DotCallPreservesBoundaryItem()
        => AssertEval("(1, 2, 1, 3).distinct", 1, 2, 3);

    [Fact]
    public void Eval_Distinct_SequenceValueReceiver_DotCallDeduplicatesSequenceItems()
    {
        var source = """
            Values = (1, 2, 1, 3)
            Values.distinct
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertEval(source, 1, 2, 3);
    }

    // ── Take/skip builtins ────────────────────────────────────────────────

    [Fact]
    public void Eval_Take_OrdinaryBuiltinCall_ReturnsLeadingItems()
        => AssertEval("take((1, 2, 3, 4, 5), 3)", 1, 2, 3);

    [Fact]
    public void Eval_Skip_OrdinaryBuiltinCall_ReturnsRemainingItems()
        => AssertEval("skip((1, 2, 3, 4, 5), 3)", 4, 5);

    [Fact]
    public void Eval_Take_DotCall_ReturnsExpandedRangeItems()
        => AssertEval("range(1, 5).take(3)", 1, 2, 3);

    [Fact]
    public void Eval_Take_DotCall_RepeatReceiverUsesFinalStateSlots()
        => AssertEvalLoopModes(
            """
            Step(a, b) = a + 1, b + 10
            Step.repeat(3, 0, 0).take(1)
            """,
            3);

    [Fact]
    public void Eval_Take_DotCall_VariadicRepeatReceiverUsesExpandedFinalStateSlots()
        => AssertEvalLoopModes(
            """
            Grow(history..., tail) = (history.spread, tail + 1), tail + 1
            Grow.repeat(3, 1, 2).take(4)
            """,
            1,
            3,
            4,
            5,
            5);

    [Fact]
    public void Eval_LoopOptimizer_ListValuedStateSlot_MatchesGenericMode()
    {
        // A step expression may produce an exact list state value via a
        // collection builtin; optimized and generic loop modes must carry the
        // same list value through repeat and while state slots.
        AssertEvalResultLoopModes(
            """
            Step(a, b) = take(a, 1), count(a)
            Step.repeat(2, 1, 0)
            """,
            Result.FromItems([ListValue(Atom(1)), Atom(1)]));

        AssertEvalResultLoopModes(
            """
            Step(a, b) = take(a, 1), b + 1, b < 2
            Step.while(5, 0)
            """,
            Result.FromItems([ListValue(Atom(5)), Atom(2)]));
    }

    [Fact]
    public void Eval_LoopOptimizer_CanonicalizesNestedEmptyStateSlot_MatchesGenericMode()
        // A loop whose next-state slot becomes `(())` now carries the canonical
        // empty sequence value, matching the generic loop.
        => AssertEvalLoopModes(
            """
            Step(a, b) = if(a == 1, (()), a.take(1)), count(a)
            Step.repeat(2, 1, 0)
            """,
            0);

    [Fact]
    public void Eval_Take_DotCall_WhileReceiverUsesFinalStateSlots()
        => AssertEvalLoopModes(
            """
            Step(a, b) = a + 1, b + 10, a < 2
            Step.while(0, 0).take(1)
            """,
            2);

    [Fact]
    public void Eval_SequenceReceiverBoundary_WhileReceiverCountsFinalStateSlots()
        => AssertEvalLoopModes(
            """
            Step(a, b) = a + 1, b + 1, 0
            Step.while(1, 2).count
            """,
            2);

    [Fact]
    public void Eval_SequenceReceiverBoundary_WhileSequenceValueStateSlotCountsOneItem()
        => AssertEvalLoopModes(
            """
            Step(x) = (x, x + 1), 0
            Step.while(1).count
            """,
            1);

    [Fact]
    public void Eval_SequenceReceiverBoundary_RepeatReceiverCountsFinalStateSlots()
        => AssertEvalLoopModes(
            """
            Step(a, b) = a + 1, b + 1
            Step.repeat(1, 1, 2).count
            """,
            2);

    [Fact]
    public void Eval_SequenceReceiverBoundary_RepeatSequenceValueStateSlotCountsOneItem()
        => AssertEvalLoopModes(
            """
            Step(x) = (x, x + 1)
            Step.repeat(1, 1).count
            """,
            2);

    [Fact]
    public void Eval_SequenceReceiverBoundary_RepeatReceiverTakeTrimsFinalStateSlots()
        => AssertEvalLoopModes(
            """
            Step(a, b) = a + 1, b + 1
            Step.repeat(1, 1, 2).take(1)
            """,
            2);

    [Fact]
    public void Eval_SequenceReceiverBoundary_YellowstoneSequenceValueHistorySelectionReturnsHistory()
    {
        var expectedPrefix = new decimal[]
        {
            1, 2, 3, 4, 9, 8, 15, 14, 5, 6,
            25, 12, 35, 16, 7, 10, 21, 20, 27, 22,
            39, 11, 13, 33, 26, 45, 28, 51, 32, 17
        };

        AssertEval(
            YellowstoneSource("YSStep.repeat(27, (1, 2, 3), 2, 3):0"),
            expectedPrefix);
    }

    [Fact]
    public void Eval_SequenceReceiverBoundary_YellowstoneWithoutTakeKeepsHelperStateSlots()
    {
        AssertEvalResultLoopModes(
            YellowstoneSource("YSStep.repeat(27, (1, 2, 3), 2, 3)"),
            Result.FromItems([
                ResultFromAtoms(
                    1, 2, 3, 4, 9, 8, 15, 14, 5, 6,
                    25, 12, 35, 16, 7, 10, 21, 20, 27, 22,
                    39, 11, 13, 33, 26, 45, 28, 51, 32, 17),
                new Result.Atom(32),
                new Result.Atom(17),
            ]));
    }

    [Fact]
    public void Eval_SequenceReceiverBoundary_YellowstoneSequenceValueHistoryPassedWhole()
    {
        // `history` holds one grouped sequence value, which is exactly the one
        // collection argument contains(collection, item) expects — the wrapper
        // passes it whole and the collection view opens the lone boundary.
        var expectedHistory = new decimal[]
        {
            1, 2, 3, 4, 9, 8, 15, 14, 5, 6,
            25, 12, 35, 16, 7, 10, 21, 20, 27, 22,
            39, 11, 13, 33, 26, 45, 28, 51, 32, 17
        };

        var source = """
            GcdStep = b, ~a mod b, a mod b != 0
            Gcd = GcdStep.while(a, b):1

            FindNext(history, pre1, pre2) = {
                IsYSCandidate(candidate) = not contains(history, candidate) and
                    Gcd(candidate, pre1) == 1 and Gcd(candidate, pre2) != 1
                FindStep = candidate + 1, not IsYSCandidate(candidate)
                FindStep.while(1):0
            }

            YSStep(history, pre2, pre1) = {
                Next = FindNext(history, pre1, pre2)
                (history.spread, Next), pre1, Next
            }
            """;

        AssertEvalResultLoopModes(
            source + "\nYSStep.repeat(27, (1, 2, 3), 2, 3)",
            Result.FromItems([
                ResultFromAtoms(expectedHistory),
                new Result.Atom(32),
                new Result.Atom(17),
            ]));

        AssertEvalLoopModes(
            source + "\nYSStep.repeat(27, (1, 2, 3), 2, 3):0",
            expectedHistory);
    }

    [Fact]
    public void Eval_Skip_DotCallReceiverAsSingleSource_SkipsExpandedRangeItems()
        => AssertEval("range(1, 5).skip(3)", 4, 5);

    [Fact]
    public void Eval_Take_InlineParenReceiver_DotCallPreservesBoundaryItem()
        => AssertEval("(1, 2, 3).take(2)", 1, 2);

    [Fact]
    public void Eval_Skip_InlineParenReceiver_DotCallDropsBoundaryItem()
        => AssertEval("(1, 2, 3).skip(1)", 2, 3);

    [Fact]
    public void Eval_Take_SequenceValueReceiver_DotCallTakesSequencePrefix()
    {
        var source = """
            Values = (1, 2, 3)
            Values.take(2)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertEval(source, 1, 2);
    }

    [Fact]
    public void Eval_Skip_SequenceValueReceiver_DotCallSkipsSequencePrefix()
    {
        var source = """
            Values = (1, 2, 3)
            Values.skip(1)
            """;

        AssertEval(source, 2, 3);
    }

    [Fact]
    public void Eval_Take_ZeroCount_ReturnsEmpty()
        => AssertEval("take((1, 2, 3), 0)");

    [Fact]
    public void Eval_Skip_ZeroCount_ReturnsOriginalSequence()
        => AssertEval("skip((1, 2, 3), 0)", 1, 2, 3);

    [Fact]
    public void Eval_Take_NegativeCount_ReturnsEmpty()
        => AssertEval("take((1, 2, 3), -2)");

    [Fact]
    public void Eval_Skip_NegativeCount_ReturnsOriginalSequence()
        => AssertEval("skip((1, 2, 3), -2)", 1, 2, 3);

    [Fact]
    public void Eval_Take_CountLargerThanLength_ReturnsWholeSequence()
        => AssertEval("take((1, 2, 3), 10)", 1, 2, 3);

    [Fact]
    public void Eval_Skip_CountLargerThanLength_ReturnsEmpty()
        => AssertEval("skip((1, 2, 3), 10)");

    [Fact]
    public void Eval_Take_SequenceValueItems_KeepsFirstGroupAsExactListElement()
    {
        var result = EvalFull("take(((1, 2), (3, 4)), 1)");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        // The one kept sequence-valued item stays an exact list element: the
        // result is [(1, 2)] (first(...) still selects the item itself).
        AssertListOfSequenceValueAtoms(result.Value, [1m, 2m]);
    }

    [Fact]
    public void Eval_Skip_SequenceValueItems_KeepsSecondGroupAsExactListElement()
    {
        var result = EvalFull("skip(((1, 2), (3, 4)), 1)");
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        // The one remaining sequence-valued item stays an exact list element:
        // the result is [(3, 4)] (last(...) still selects the item itself).
        AssertListOfSequenceValueAtoms(result.Value, [3m, 4m]);
    }

    [Fact]
    public void Eval_Take_SequenceValueWrapperOutput_PreservesSingleSequenceValueItem()
    {
        var source = """
            Values = (1, 2, 3)
            take(Values, 1)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Take_MultiOutputWrapper_KeepsExpandedTopLevelPrefix()
    {
        var source = """
            Values = 1, 2, 3
            take(Values, 1)
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Skip_SequenceValueWrapperOutput_ReturnsEmptyAfterSkippingSingleSequenceValueItem()
    {
        var source = """
            Values = (1, 2, 3)
            skip(Values, 1)
            """;

        AssertEval(source, 2, 3);
    }

    [Fact]
    public void Eval_Skip_MultiOutputWrapper_DropsExpandedTopLevelPrefix()
    {
        var source = """
            Values = 1, 2, 3
            skip(Values, 1)
            """;

        AssertEval(source, 2, 3);
    }

    [Fact]
    public void Eval_Take_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            take(Data:0, 2)
            (Data:0).take(2)
            """;

        AssertEval(source, 7, 6, 7, 6);
    }

    [Fact]
    public void Eval_Skip_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            skip(Data:0, 2)
            (Data:0).skip(2)
            """;

        AssertEval(source, 4, 2, 1, 4, 2, 1);
    }

    [Fact]
    public void Eval_Take_EmptyCountArgument_FailsWithContext()
        => AssertBuiltinFailureWithContext(
            "take((1, 2), take(1, 0))",
            "take count must be exactly one whole-number value");

    [Fact]
    public void Eval_Take_SequenceValueCountArgument_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "take((3, 4), (1, 2))",
            "take count must be exactly one whole-number value");

    [Fact]
    public void Eval_Take_FractionalCountArgument_FailsWithContext()
        => AssertBuiltinFailureWithContext(
            "take((1, 2), 1.5)",
            "take count must be exactly one whole-number value");

    [Fact]
    public void Eval_Skip_StringCountArgument_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "skip((1, 2), 'hello')",
            "skip count must be exactly one whole-number value");

    [Fact]
    public void Eval_Skip_SpreadArguments_FollowOrdinaryFixedArity()
    {
        // Spread has only its ordinary meaning: `Bad.spread` opens to two argument
        // slots, so skip((3, 4), Bad.spread) supplies three arguments to the fixed
        // skip(collection, count) signature — an ordinary arity error.
        var source = """
            Bad = 1, 2
            skip((3, 4), Bad.spread)
            """;

        AssertEvalFailsWithArityMismatch(source, expected: 2, actual: 3);
    }

    // ── Min builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Min_OrdinaryBuiltinCall_ExpandsRangeTopLevelItems()
        => AssertEval("min(range(1, 5))", 1);

    [Fact]
    public void Eval_Min_DotCallReceiverAsSingleSource_ExpandsRangeItems()
        => AssertEval("range(1, 5).min", 1);

    [Fact]
    public void Eval_Min_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            min(Data:0)
            (Data:0).min
            """;

        AssertEval(source, 1, 1);
    }

    [Fact]
    public void Eval_Min_InlineParenReceiver_DotCallPreservesBoundary()
        => AssertEval("(10, 4, 7).min", 4);

    [Fact]
    public void Eval_Min_SequenceValueReceiver_DotCallFindsMinimum()
    {
        var source = """
            Values = (10, 4, 7)
            Values.min
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Min_SingleAtomicInput_ReturnsSameValue()
        => AssertEval("min(5)", 5);

    [Fact]
    public void Eval_Min_DirectCallMultiArgs_FindsMinimum()
        => AssertEval("min((10, 4, 7))", 4);

    [Fact]
    public void Eval_Min_SequenceValueElements_FailWithContext()
        => AssertBuiltinFailureWithExactContext(
            "min(((1, 2), (3, 4)))",
            "min expects each collection element to be a single numeric value; item 0 was sequence value");

    [Fact]
    public void Eval_Min_StringElement_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "min('hello')",
            "min expects each collection element to be a single numeric value; item 0 was string value \"hello\"");

    [Fact]
    public void Eval_Min_IndexedNumericDiagnostic_IncludesItemIndex()
        => AssertBuiltinFailureWithContext(
            "min((1, (2, 3)))",
            "min expects each collection element to be a single numeric value; item 1 was sequence value");

    // ── Max builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Max_OrdinaryBuiltinCall_ExpandsRangeTopLevelItems()
        => AssertEval("max(range(1, 5))", 5);

    [Fact]
    public void Eval_Max_DotCallReceiverAsSingleSource_ExpandsRangeItems()
        => AssertEval("range(1, 5).max", 5);

    [Fact]
    public void Eval_Max_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            max(Data:0)
            (Data:0).max
            """;

        AssertEval(source, 7, 7);
    }

    [Fact]
    public void Eval_Max_InlineBraceReceiver_DotCallPreservesBoundary()
        => AssertEval("{10, 4, 7}.max", 10);

    [Fact]
    public void Eval_Max_SequenceValueReceiver_DotCallFindsMaximum()
    {
        var source = """
            Values = (10, 4, 7)
            Values.max
            """;

        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Max_SingleAtomicInput_ReturnsSameValue()
        => AssertEval("max(5)", 5);

    [Fact]
    public void Eval_Max_DirectCallMultiArgs_FindsMaximum()
        => AssertEval("max((10, 4, 7))", 10);

    [Fact]
    public void Eval_Max_SequenceValueElements_FailWithContext()
        => AssertBuiltinFailureWithExactContext(
            "max(((1, 2), (3, 4)))",
            "max expects each collection element to be a single numeric value; item 0 was sequence value");

    [Fact]
    public void Eval_Max_StringElement_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "max('hello')",
            "max expects each collection element to be a single numeric value; item 0 was string value \"hello\"");

    [Fact]
    public void Eval_Max_IndexedNumericDiagnostic_IncludesItemIndex()
        => AssertBuiltinFailureWithContext(
            "max((1, (2, 3)))",
            "max expects each collection element to be a single numeric value; item 1 was sequence value");

    // ── Sum builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Sum_OrdinaryBuiltinCall_ExpandsRangeTopLevelItems()
        => AssertEval("sum(range(1, 5))", 15);

    [Fact]
    public void Eval_Sum_OrdinaryBuiltinCall_ExpandsLargeRangeTopLevelItems()
        => AssertEval("sum(range(1, 100))", 5050);

    [Fact]
    public void Eval_Sum_WrapperBoundToRange_ExpandsTopLevelItems()
    {
        var source = """
            P = range(1, 100)
            sum(P)
            """;

        AssertEval(source, 5050);
    }

    [Fact]
    public void Eval_Sum_DotCallReceiverAsSingleSource_ExpandsRangeItems()
        => AssertEval("range(1, 5).sum", 15);

    [Fact]
    public void Eval_Sum_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            sum(Data:0)
            (Data:0).sum
            """;

        AssertEval(source, 20, 20);
    }

    [Fact]
    public void Eval_Sum_InlineBraceReceiver_DotCallPreservesBoundary()
        => AssertEval("{3, 5, 3}.sum", 11);

    [Fact]
    public void Eval_Sum_SequenceValueReceiver_DotCallSumsSequenceItems()
    {
        var source = """
            Values = (10, 20, 30)
            Values.sum
            """;

        AssertEval(source, 60);
    }

    [Fact]
    public void Eval_Sum_NestedSequenceValueReceiver_DotCallPreservesNestedSequenceValues()
        => AssertBuiltinFailureWithExactContext(
            "((1, 2), (3, 4)).sum",
            "sum expects each collection element to be a single numeric value; item 0 was sequence value");

    [Fact]
    public void Eval_Sum_SingleAtomicInput_ReturnsSameValue()
        => AssertEval("sum(5)", 5);

    [Fact]
    public void Eval_Sum_DirectCallMultiArgs_AddsValues()
        => AssertEval("sum((10, 20, 30))", 60);

    [Fact]
    public void Eval_Sum_SequenceValueElements_FailWithContext()
        => AssertBuiltinFailureWithExactContext(
            "sum(((1, 2), (3, 4)))",
            "sum expects each collection element to be a single numeric value; item 0 was sequence value");

    [Fact]
    public void Eval_Sum_StringElement_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "sum('hello')",
            "sum expects each collection element to be a single numeric value; item 0 was string value \"hello\"");

    [Fact]
    public void Eval_Sum_IndexedNumericDiagnostic_IncludesItemIndex()
        => AssertBuiltinFailureWithContext(
            "sum((1, (2, 3)))",
            "sum expects each collection element to be a single numeric value; item 1 was sequence value");

    [Fact]
    public void Eval_Sum_ProjectedNestedSequenceValueSelection_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            """
            A = ((1, 2), (3, 4)), ((5, 6), (7, 8))
            sum(A:0)
            """,
            "sum expects each collection element to be a single numeric value; item 0 was sequence value");

    // ── Avg builtin ──────────────────────────────────────────────────────────

    [Fact]
    public void Eval_Avg_OrdinaryBuiltinCall_ExpandsRangeTopLevelItems()
        => AssertEval("avg(range(1, 5))", 3);

    [Fact]
    public void Eval_Avg_DotCallReceiverAsSingleSource_ExpandsRangeItems()
        => AssertEval("range(1, 5).avg", 3);

    [Fact]
    public void Eval_Avg_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            avg(Data:0)
            (Data:0).avg
            """;

        AssertEval(source, 4, 4);
    }

    [Fact]
    public void Eval_Avg_InlineParenReceiver_DotCallPreservesBoundary()
        => AssertEval("(10, 4, 7).avg", 7);

    [Fact]
    public void Eval_Avg_SequenceValueReceiver_DotCallAveragesSequenceItems()
    {
        var source = """
            Values = (10, 20, 30)
            Values.avg
            """;

        AssertEval(source, 20);
    }

    [Fact]
    public void Eval_Avg_NonExactPositiveMean_ReturnsDecimalMean()
        => AssertEval("avg((1, 2))", 1.5m);

    [Fact]
    public void Eval_Avg_NonExactNegativeMean_ReturnsDecimalMean()
        => AssertEval("avg((-1, -2))", -1.5m);

    [Fact]
    public void Eval_Avg_NegativeMeanTowardZero_ReturnsDecimalMean()
        => AssertEval("avg((-1, 0))", -0.5m);

    [Fact]
    public void Eval_Avg_ExactMultiArgMean_ReturnsInteger()
        => AssertEval("avg((1, 2, 3))", 2);

    [Fact]
    public void Eval_Avg_FractionalMeanViaSumOverCount_KeepsDecimal()
        => AssertEval("sum((-1, -2)) / count((-1, -2))", -1.5m);

    [Fact]
    public void Eval_Avg_SingleAtomicInput_ReturnsSameValue()
        => AssertEval("avg(5)", 5);

    [Fact]
    public void Eval_Avg_DirectCallMultiArgs_ComputesMean()
        => AssertEval("avg((10, 20, 30))", 20);

    [Fact]
    public void Eval_Avg_SequenceValueElements_FailWithContext()
        => AssertBuiltinFailureWithExactContext(
            "avg(((1, 2), (3, 4)))",
            "avg expects each collection element to be a single numeric value; item 0 was sequence value");

    [Fact]
    public void Eval_Avg_StringElement_FailsWithContext()
        => AssertBuiltinFailureWithExactContext(
            "avg('hello')",
            "avg expects each collection element to be a single numeric value; item 0 was string value \"hello\"");

    [Fact]
    public void Eval_Avg_IndexedNumericDiagnostic_IncludesItemIndex()
        => AssertBuiltinFailureWithContext(
            "avg((1, (2, 3)))",
            "avg expects each collection element to be a single numeric value; item 1 was sequence value");

    // ── Reduce builtin ───────────────────────────────────────────────────────

    [Fact]
    public void Eval_Reduce_DirectCallMultiArgs_AddsLeftToRight()
    {
        var source = """
            Add = x + total
            reduce((1, 2, 3, 4), Add, 0)
            """;

        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Reduce_RangeArgument_IteratesEmittedItemsForHigherOrderIteration()
    {
        var source = """
            AddItemCount(item, acc) = item.count + acc
            reduce(range(3, 6), AddItemCount, 0)
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Reduce_DirectCallMixedArgs_PreservesRangeBoundary()
    {
        var source = """
            AddItemCount(x, acc) = x.count + acc
            reduce(((1, 2), range(3, 4).spread), AddItemCount, 0)
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Reduce_DirectCallMixedArgs_ExpandsRangeTopLevelItemsForStep()
    {
        var source = """
            AddSequenceValueRange((a, b, c), acc) = acc + 100
            AddSequenceValueRange(x, acc) = acc + x
            reduce((1, range(2, 4).spread), AddSequenceValueRange, 0)
            """;

        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Reduce_NamedMultiOutputArgument_IteratesEmittedItems()
    {
        var source = """
            Left = 3, 4, 2, 1, 3, 3
            Right = 4, 3, 5, 3, 9, 3

            CountMatchStep(element, tt) = {
                T = atoms(tt)
                Output = (T.first, T:1 + if(element == T.first, 1, 0))
            }

            MatchCount = reduce(Right, CountMatchStep, (value, 0)):1
            SimilarityAt = value * MatchCount(value)
            Part2 = Left.map(SimilarityAt).sum
            Part2
            """;

        AssertEval(source, 31);
    }

    [Fact]
    public void Eval_Reduce_IsLeftToRight()
    {
        var source = """
            Digits = x + acc * 10
            reduce((1, 2, 3, 4), Digits, 0)
            """;

        AssertEval(source, 1234);
    }

    [Fact]
    public void Eval_Reduce_ArityMismatch_ReportsFixedThreeArgumentSignature()
    {
        // reduce(collection, reducer, initial) is an ordinary fixed-arity
        // callable: an under-supplied call is a plain arity error carrying the
        // fixed signature.
        var result = EvalFull(
            """
            Add = x + total
            reduce(1)
            """);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Equal(
            "Callable `reduce(collection, reducer, initial)` expects 3 arguments, but was called with 1 argument.",
            formatted);

        var error = result.Error;
        while (error is EvalError.WithContext wc)
            error = wc.Inner;

        Assert.IsType<EvalError.ArityMismatch>(error);
        Assert.False(error is EvalError.VariadicArityMismatch);

        // The old two-argument shape (collection + reducer, no initial) is the
        // same kind of plain arity error — no suffix binding, no hint.
        AssertEvalFailsWithArityMismatch("Add = x + total\nreduce((1, 2, 3), Add)", expected: 3, actual: 2);
    }

    [Fact]
    public void Eval_Reduce_ParameterizedInitialAccumulator_ReportsCallSiteWithHint()
    {
        // A fully supplied reduce(collection, reducer, initial) whose `initial`
        // argument is a parameterized algorithm cannot evaluate the starting
        // accumulator, so the call-site hint fires (rather than a generic
        // unknown-name error).
        var result = EvalFull("Add = x + total\nreduce((1, 2, 3), {a + b}, Add)");
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error);
        Assert.Equal(2, formatted.StartLine);
        Assert.Equal(1, formatted.StartColumn);
        Assert.Contains("the last argument must be an initial accumulator value", formatted.Message);
        Assert.Contains("still needs 'x' and 'total'", formatted.Message);
        Assert.DoesNotContain("Unknown name: x", formatted.Message);
    }

    [Fact]
    public void Eval_Reduce_DotCallParameterizedInitialAccumulator_ReportsCallSiteWithHint()
    {
        var result = EvalFull(
            """
            Add = x + total
            Values = 1, 2, 3
            Values.reduce(Add)
            """);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error);
        Assert.Equal(3, formatted.StartLine);
        Assert.Equal(1, formatted.StartColumn);
        Assert.Contains("`reduce` is `reduce(collection, reducer, initial)`", formatted.Message);
        Assert.Contains("'x' and 'total'", formatted.Message);
        Assert.Contains("add an initial accumulator", formatted.Message);
        Assert.DoesNotContain("Unknown name: x", formatted.Message);
        Assert.DoesNotContain("Bad arity", formatted.Message);
    }

    [Fact]
    public void Eval_Reduce_DotCallOrdinaryValueWithMissingArgument_ReportsFixedArity()
    {
        // The missing-initial hint is specific to the common X.reduce(F)
        // mistake where F is visibly a parameterized reducer. An ordinary
        // value is not misdescribed as an unevaluable initial accumulator.
        var result = EvalFull("Values = 1, 2, 3\nValues.reduce(0)");
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error);
        Assert.Equal(2, formatted.StartLine);
        Assert.Equal(1, formatted.StartColumn);
        Assert.Equal(
            "Property 'reduce' on `Values` expects 3 parameters, but was called with 2 arguments.",
            formatted.Message);
    }

    [Fact]
    public void Eval_Reduce_SequenceValueElements_ArePassedWhole()
    {
        var source = """
            TakeValue((tag, value), acc) = acc + value
            reduce(((1, 10), (2, 20), (3, 30)), TakeValue, 0)
            """;

        AssertEval(source, 60);
    }

    [Fact]
    public void Eval_Reduce_SequenceValueAccumulator_IsAccepted()
    {
        var source = """
            Stats(x, acc) = (x + acc:0, acc:1 + 1)
            reduce((1, 2, 3, 4), Stats, (0, 0))
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var group = Assert.IsType<Result.SequenceValue>(result.Value);
        Assert.Collection(
            group.Items,
            first => Assert.Equal(10m, Assert.IsType<Result.Atom>(first).Value),
            second => Assert.Equal(4m, Assert.IsType<Result.Atom>(second).Value));
    }

    [Fact]
    public void Eval_Reduce_VariadicAccumulatorState_FlattensNaturally()
    {
        var source = """
            Append(item, history...) = (history.spread item)
            reduce((2, 3, 4), Append, 1)
            """;

        AssertEvalResultSequenceModes(source, ResultFromAtoms(1, 2, 3, 4));
    }

    [Fact]
    public void Eval_Reduce_ScalarReducerBehavior_RemainsUnchanged()
    {
        var source = """
            Sum(item, total) = total + item
            reduce((2, 3, 4), Sum, 1)
            """;

        AssertEvalSequenceModes(source, 10);
    }

    [Fact]
    public void Eval_Reduce_NonVariadicAccumulator_PreservesStructuralAccumulator()
    {
        var source = """
            Append(item, history) = (history.spread item)
            reduce((2, 3, 4), Append, 1)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var outer = Assert.IsType<Result.SequenceValue>(result.Value);
        AssertSequenceValueAtoms(outer, 1, 2, 3, 4);
    }

    [Fact]
    public void Eval_Reduce_SequenceValueElements_AndSequenceValueAccumulator_ArePassedWhole()
    {
        var source = """
            TakeStats((tag, value), (sum, count)) = (sum + value, count + 1)
            reduce(((1, 10), (2, 20), (3, 30)), TakeStats, (0, 0))
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var group = Assert.IsType<Result.SequenceValue>(result.Value);
        Assert.Collection(
            group.Items,
            first => Assert.Equal(60m, Assert.IsType<Result.Atom>(first).Value),
            second => Assert.Equal(3m, Assert.IsType<Result.Atom>(second).Value));
    }

    [Fact]
    public void Eval_Reduce_SequenceValueReceiver_DotCall_ProjectsCurrentItemLikeSelection()
    {
        var source = """
            AddItemCount(item, acc) = item.count + acc
            Values = (1, 2, 3)
            Values.reduce(AddItemCount, 0)
            """;

        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Reduce_ProjectedSelection_PlainAndDotCallAgree()
    {
        var source = """
            Add = x + total
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            reduce(Data:0, Add, 0)
            (Data:0).reduce(Add, 0)
            """;

        AssertEval(source, 20, 20);
    }

    [Fact]
    public void Eval_Reduce_CurrentItem_MatchesSelection_PlainAndDotCall()
    {
        var source = """
            Signature(current, acc) = acc * 100 + current.count * 10 + current.sum
            Items = (1, 2), (3, 4)
            (Items:0).count
            (Items:0).sum
            (Items:1).count
            (Items:1).sum
            Items.reduce(Signature, 0)
            reduce(((1, 2), (3, 4)), Signature, 0)
            """;

        AssertEval(source, 2, 3, 2, 7, 2327, 2327);
    }

    [Fact]
    public void Eval_Reduce_CurrentItem_ProjectsOneLevelOnly()
    {
        var source = """
            Signature(current, acc) = acc * 100 + current.count * 10 + (current:0).count
            Items = ((1, 2), (3, 4))
            (Items:0).count
            Items.reduce(Signature, 0)
            reduce(((1, 2), (3, 4)), Signature, 0)
            """;

        AssertEval(source, 2, 2121, 2121);
    }

    [Fact]
    public void Eval_Reduce_Accumulator_DoesNotAutoProject()
    {
        var source = """
            Signature(current, acc) = (acc:0 * 100 + current.count * 10 + acc.count, acc.count)
            Items = (1, 2), (3, 4)
            Items.reduce(Signature, (0, 9, 8))
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        AssertSequenceValueAtoms(result.Value, 2322m, 2m);
    }

    [Fact]
    public void Eval_Reduce_EmptyStepResult_FailsWithContext()
    {
        // A step whose body is the truly empty result `()` still fails the strict
        // single-accumulator contract. (A collection builtin like take(1, 0) no
        // longer produces this failure — it returns the empty list [], which is
        // one valid accumulator value; see the exact-list acceptance test below.)
        var source = """
            Bad(x, acc) = ()
            reduce((1, 2, 3), Bad, 0)
            """;

        AssertReduceStepShapeFails(source);
    }

    [Fact]
    public void Eval_Reduce_ListValuedStepResult_IsAcceptedAsAccumulator()
    {
        // take(a, 1) returns an exact list — ONE valid accumulator value per
        // step, so the final accumulator is the last step's list [3].
        AssertEvalCounted(
            """
            Step(a, acc) = take(a, 1)
            reduce((1, 2, 3), Step, 0)
            """,
            1,
            ListValue(Atom(3)));
    }

    [Fact]
    public void Eval_Reduce_MultiOutputStepResult_FailsWithContext()
    {
        var source = """
            Bad(x, acc) = acc, x
            reduce((1, 2, 3), Bad, 0)
            """;

        AssertReduceStepShapeFails(source);
    }

    // -- Callback runtime binding characterization -------------------------

    [Fact]
    public void Eval_Callback_TopLevelVariadicMap_CollectsOneElementSlotPerInvocation()
    {
        var source = """
            Count(values...) = values.count
            map((1, 2, 3), Count)
            """;

        // A single-variadic callback receives each iterated element as ONE collected
        // slot: values = [element], so values.count is 1 per invocation.
        AssertEvalSequenceModes(source, 1, 1, 1);

        // values.count cannot distinguish scalar binding (values = 7) from
        // list collection (values = [7]); the identity/equality forms below
        // pin the collected list kind exactly.
        var identity = EvalFull(
            """
            Collect(values...) = values
            map((7, 8), Collect)
            """);
        Assert.True(identity.IsOk, $"expected success: {(identity.IsError ? identity.Error.ToString() : "")}");
        var mapped = Assert.IsType<Result.ListValue>(identity.Value);
        Assert.Collection(
            mapped.Items,
            first =>
            {
                var collected = Assert.IsType<Result.ListValue>(first);
                Assert.Equal([new Result.Atom(7)], collected.Items, Result.ValueComparer);
            },
            second =>
            {
                var collected = Assert.IsType<Result.ListValue>(second);
                Assert.Equal([new Result.Atom(8)], collected.Items, Result.ValueComparer);
            });

        AssertEvalSequenceModes(
            """
            IsSingleSeven(values...) = values == [7]
            map((7, 8), IsSingleSeven)
            """,
            1, 0);
    }

    [Fact]
    public void Eval_Callback_TopLevelVariadicFilter_CollectsOneElementSlotPerInvocation()
    {
        var source = """
            One(values...) = values.count == 1
            filter((1, 2, 3), One)
            """;

        // Single-variadic predicate callbacks collect one element slot per
        // invocation, so values.count == 1 succeeds for every source item.
        AssertEvalSequenceModes(source, 1, 2, 3);

        // Kind-sensitive form: the predicate observes the collected LIST
        // [element], not the bare scalar (7 == [7] is false, [7] == [7] true).
        AssertEvalSequenceModes(
            """
            IsSingleSeven(values...) = values == [7]
            filter((7, 8), IsSingleSeven)
            """,
            7);
    }

    [Fact]
    public void Eval_Callback_TopLevelVariadicReduce_CollectsElementSlotBeforeAccumulator()
    {
        var source = """
            Step(values..., acc) = values.count * 10 + acc
            reduce((1, 2, 3), Step, 0)
            """;

        // A reducer variadic parameter in element position collects the projected item as
        // [element] each step; the accumulator stays a separate fixed slot.
        AssertEvalSequenceModes(source, 30);

        // Kind-sensitive form: the step observes the collected list [element].
        AssertEvalSequenceModes(
            """
            Step(values..., acc) = acc + (values == [3])
            reduce((1, 2, 3), Step, 0)
            """,
            1);
    }

    [Fact]
    public void Eval_Callback_FlatFixedArityFailure_PreservesCurrentDiagnosticShape()
    {
        var result = EvalFull(
            """
            NeedTwo(a, b) = a + b
            map((1, 2), NeedTwo)
            """);

        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("while evaluating map transform", formatted);
        Assert.DoesNotContain("NeedTwo", formatted);

        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
        Assert.Equal(2, arity.Expected);
        Assert.Equal(1, arity.Actual);
    }

    [Fact]
    public void Eval_Callback_SequenceValuePatternWrongShape_DoesNotFlattenScalarItems()
    {
        var result = EvalFull(
            """
            PairSum((x, y)) = x + y
            map((1, 2), PairSum)
            """);

        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("while evaluating map transform", formatted);

        Assert.IsType<EvalError.BadArity>(Innermost(result.Error));
    }

    [Fact]
    public void Eval_Callback_RepeatedSequenceValueBinderUsesEqualityConstraint()
    {
        AssertEvalSequenceModes(
            """
            Same((x, x)) = x
            map(((1, 1), (2, 2)), Same)
            """,
            1, 2);

        var result = EvalFull(
            """
            Same((x, x)) = x
            map((1, 2), Same)
            """);
        Assert.True(result.IsError);
        Assert.IsType<EvalError.BadArity>(Innermost(result.Error));
    }

    [Fact]
    public void Eval_Callback_RepeatedConditionalBinderFallsThrough()
    {
        AssertEvalSequenceModes(
            """
            Equal((x, x)) = 1
            Equal((x, y)) = 0
            map(((1, 1), (1, 2)), Equal)
            """,
            1, 0);
    }

    [Fact]
    public void Eval_Callback_ConditionalPredicateNoMatch_PreservesFilterDiagnosticShape()
    {
        var result = EvalFull(
            """
            Keep(0) = 1
            filter(1, Keep)
            """);

        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("while evaluating filter predicate for item 0: 1", formatted, StringComparison.Ordinal);

        var noMatch = Assert.IsType<EvalError.NoMatchingBranch>(Innermost(result.Error));
        Assert.Equal("filter predicate", noMatch.AlgorithmName);
    }

    [Fact]
    public void Eval_Callback_SequenceValueMapPatternWrongGroupArity_PreservesArityMismatch()
    {
        var result = EvalFull(
            """
            PairSum((x, y)) = x + y
            map(((1, 2, 3)), PairSum)
            """);

        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("while evaluating map transform", formatted, StringComparison.Ordinal);

        Assert.IsType<EvalError.BadArity>(Innermost(result.Error));
    }

    [Fact]
    public void Eval_Callback_DoesNotBindAlgorithmChannelForIteratedItems()
    {
        var result = EvalFull(
            """
            Thunk = 42
            Apply(f) = f()
            map(Thunk, Apply)
            """);

        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("while evaluating map transform", formatted, StringComparison.Ordinal);

        var notAlgorithm = Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(result.Error));
        Assert.Equal("param(f)", notAlgorithm.Description);
    }

    [Fact]
    public void Eval_Callback_ConditionalPredicate_UsesConditionalCallbackPath()
    {
        var source = """
            Keep(0) = 0
            Keep(x) = 1
            filter((0, 1, 2), Keep)
            """;

        AssertEvalSequenceModes(source, 1, 2);
    }

    [Fact]
    public void Eval_Callback_BuiltinMapper_UsesCustomBuiltinCountedPath()
    {
        var source = """
            map(((1, 2), (3, 4, 5)), count)
            """;

        AssertEvalSequenceModes(source, 2, 3);
    }

    // ── Higher-order boundary regressions ───────────────────────────────────

    [Fact]
    public void Eval_Filter_InlineBraceReceiver_DotCallPreservesBoundary()
    {
        var source = """
            IsLarge = x > 1
            {1, 2, 3, 4}.filter(IsLarge)
            """;

        AssertEval(source, 2, 3, 4);
    }

    [Fact]
    public void Eval_Filter_SequenceValueReceiver_DotCallIteratesSequenceItems()
    {
        var source = """
            KeepSecondEven(pair) = pair:1 mod 2 == 0
            Values = (1, 2), (3, 5)
            Values.filter(KeepSecondEven)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        // Only (1, 2) is kept; it stays an exact list element, so the result is
        // the exact list [(1, 2)].
        AssertListOfSequenceValueAtoms(result.Value, [1m, 2m]);
    }

    [Fact]
    public void Eval_Map_InlineParenReceiver_DotCallPreservesBoundary()
    {
        var source = """
            AddOne = x + 1
            (1, 2, 3).map(AddOne)
            """;

        AssertEval(source, 2, 3, 4);
    }

    [Fact]
    public void Eval_Map_RecursiveCallback_UsesCurrentValueBinding()
    {
        var source = """
            Factorial = if(n == 0, 1, Factorial(n - 1) * n)
            (0, 1, 2, 3, 4).map(Factorial)
            """;

        AssertEval(source, 1, 1, 2, 6, 24);
    }

    [Fact]
    public void Eval_Reduce_InlineParenReceiver_DotCall_UsesTopLevelItems()
    {
        var source = """
            Add = x + total
            Output = (1, 2, 3).reduce(Add, 0)
            """;

        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_Map_SequenceValueReceiver_DotCall_ProjectsCallbackItemLikeSelection()
    {
        var source = """
            TakeFirst(x) = x:0
            Values = (1, 2, 3)
            Values.map(TakeFirst)
            """;

        AssertEval(source, 1, 2, 3);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_UsesReceiverTopLevelItemsAndProjectedCallbackCounts()
    {
        var source = """
            Items = range(1, 3), 7
            Items.count
            (Items:0).count
            (Items:1).count
            Items.map{x.count}
            """;

        AssertEval(source, 2, 3, 1, 3, 1);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_FilterAndSelectionUseProjectedCallbackItems()
    {
        var source = """
            Items = range(1, 3), 7
            Items.map{x:0}
            Items.filter{x.count == 3}.count
            """;

        // range(1, 3) is an exact list item bound whole to the callback param:
        // `x:0` selects its first stored element (1), while the scalar item 7
        // projects to itself, so the map materializes [1, 7]. filter keeps the
        // one list item whose opened count is 3, and .count reports the
        // kept-item count 1.
        AssertEval(source, 1, 7, 1);
    }

    [Fact]
    public void Eval_HigherOrder_DotCall_SequenceValueNamedReceiver_DoesNotAutoExpand()
    {
        var source = """
            TopLevelItemCount(item) = item.count
            AddTopLevelItemCount(item, acc) = item.count + acc
            Pairs = ((1, 2), (3, 4))
            Pairs.count
            Pairs.map(TopLevelItemCount)
            Pairs.reduce(AddTopLevelItemCount, 0)
            """;

        AssertEval(source, 2, 2, 2, 4);
    }

    [Fact]
    public void Eval_Map_CallbackItem_FirstProjectionMatchesSelection()
    {
        var source = """
            TakeFirst(report) = report:0
            map(((7, 6, 4, 2, 1), (1, 2, 7, 8, 9)), TakeFirst)
            """;

        AssertEval(source, 7, 1);
    }

    [Fact]
    public void Eval_Map_SequenceValuePairs_ProjectOneLevelOnly()
    {
        var source = """
            TakeFirst(x) = x:0
            map(((1, 2), (3, 4)), TakeFirst)
            """;

        AssertEval(source, 1, 3);
    }

    [Fact]
    public void Eval_Filter_PracticalSafeReportStyle_UsesProjectedCallbackReport()
    {
        var source = """
            IsSafe(report) =
                report:0 > report:(0 + 1) and
                report:1 > report:(1 + 1) and
                report:2 > report:(2 + 1) and
                report:3 > report:(3 + 1) and
                report:0 - report:(0 + 1) <= 3 and
                report:1 - report:(1 + 1) <= 3 and
                report:2 - report:(2 + 1) <= 3 and
                report:3 - report:(3 + 1) <= 3
            filter(((7, 6, 4, 2, 1), (1, 2, 7, 8, 9)), IsSafe)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        // Only the first report is kept; it stays an exact list element, so the
        // result is the exact list [(7, 6, 4, 2, 1)].
        AssertListOfSequenceValueAtoms(result.Value, [7m, 6m, 4m, 2m, 1m]);
    }

    [Fact]
    public void Eval_HigherOrder_DotCall_IndexedSequenceValueReceiver_ProjectsOneLevel()
    {
        var source = """
            TopLevelItemCount(item) = item.count
            AddTopLevelItemCount(item, acc) = item.count + acc
            Bags = ((1, 2), (3, 4)), ((5, 6), (7, 8))
            (Bags:0).count
            (Bags:0).map(TopLevelItemCount)
            (Bags:0).reduce(AddTopLevelItemCount, 0)
            """;

        AssertEval(source, 2, 2, 2, 4);
    }

    // ── Uniform counted sequence extraction regressions ────────────────────

    [Fact]
    public void Eval_Filter_WrapperSequenceOutput_IteratesSequenceValueItems()
    {
        var source = """
            KeepSecondEven(pair) = pair:1 mod 2 == 0
            Values = (1, 2), (3, 5)
            filter(Values, KeepSecondEven)
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        // Only (1, 2) is kept; it stays an exact list element, so the result is
        // the exact list [(1, 2)].
        AssertListOfSequenceValueAtoms(result.Value, [1m, 2m]);
    }

    [Fact]
    public void Eval_Map_WrapperSequenceOutput_MapsSequenceValueItems()
    {
        var source = """
            TakeValue(pair) = pair:1
            Values = ((1, 2), (3, 4))
            map(Values, TakeValue)
            """;

        AssertEval(source, 2, 4);
    }

    [Fact]
    public void Eval_Reduce_WrapperSingleSequenceValueOutput_FoldsWholeGroupOnce()
    {
        var source = """
            AddValue(pair, total) = total + pair:1
            Values = ((1, 2), (3, 4))
            reduce(Values, AddValue, 0)
            """;

        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_Sum_WrapperMultiOutput_ExpandsTopLevelItems()
    {
        var source = """
            Values = 10, 20, 30
            sum(Values)
            """;

        AssertEval(source, 60);
    }

    [Fact]
    public void Eval_Min_WrapperMultiOutput_ExpandsTopLevelItems()
    {
        var source = """
            Values = 10, 4, 7
            min(Values)
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_Max_WrapperMultiOutput_ExpandsTopLevelItems()
    {
        var source = """
            Values = 10, 4, 7
            max(Values)
            """;

        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Avg_WrapperMultiOutput_ExpandsTopLevelItems()
    {
        var source = """
            Values = 10, 20, 30
            avg(Values)
            """;

        AssertEval(source, 20);
    }

    // -- Sequence builtin dot-call regression sweep --------------------------

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Count_ExplicitReceiverSweep()
        => AssertEval(
            """
            Values = 1, 2, 3
            SequenceValue = (1, 2, 3)
            Data = (3, 1, 2), (9, 8, 7)
            Values.count
            count(Values)
            SequenceValue.count
            count(SequenceValue)
            (Data:0).count
            count(Data:0)
            """,
            3,
            3,
            3,
            3,
            3,
            3);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Contains_ExplicitReceiverSweep()
        => AssertEval(
            """
            Values = 1, 2, 3
            SequenceValue = (1, 2, 3)
            Data = (3, 1, 2), (9, 8, 7)
            Values.contains(2)
            contains(Values, 2)
            SequenceValue.contains(2)
            SequenceValue.contains((1, 2, 3))
            (Data:0).contains(2)
            contains(Data:0, 2)
            """,
            1,
            1,
            1,
            0,
            1,
            1);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_OrderAndOrderDesc_ProjectionSweep()
        => AssertEval(
            """
            Values = 3, 1, 2
            Data = (3, 1, 2), (9, 8, 7)
            Values.order
            Values.orderDesc
            (Data:0).order
            order(Data:0)
            (Data:0).orderDesc
            orderDesc(Data:0)
            """,
            1,
            2,
            3,
            3,
            2,
            1,
            1,
            2,
            3,
            1,
            2,
            3,
            3,
            2,
            1,
            3,
            2,
            1);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_OrderAndOrderDesc_MultiOutputHelpersMatchPlainCall()
    {
        AssertEval(
            """
            Values = 3, 1, 2
            order(Values)
            orderDesc(Values)
            """,
            1,
            2,
            3,
            3,
            2,
            1);

        AssertEval(
            """
            SequenceValue = (3, 1, 2)
            SequenceValue.order
            """,
            1,
            2,
            3);

        AssertEval(
            """
            SequenceValue = (3, 1, 2)
            SequenceValue.orderDesc
            """,
            3,
            2,
            1);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_FirstAndLast_ProjectionSweep()
        => AssertEval(
            """
            Values = 5, 6, 7
            Data = (9, 8, 7), (3, 2, 1)
            Values.first
            Values.last
            (Data:0).first
            first(Data:0)
            (Data:0).last
            last(Data:0)
            """,
            5,
            7,
            9,
            9,
            7,
            7);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_FirstAndLast_SequenceValueReceiversAgreeWithPlainCall()
    {
        AssertEval(
            """
            SequenceValue = (5, 6, 7)
            SequenceValue.first
            first(SequenceValue)
            SequenceValue.last
            last(SequenceValue)
            """,
            5,
            5,
            7,
            7);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Distinct_ProjectionSweep()
        => AssertEval(
            """
            Values = 1, 2, 1, 3
            Data = (1, 2, 1, 3), (9, 8, 9)
            Values.distinct
            (Data:0).distinct
            distinct(Data:0)
            """,
            1,
            2,
            3,
            1,
            2,
            3,
            1,
            2,
            3);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Distinct_SequenceValueReceiversAgreeWithPlainCall()
    {
        AssertEval(
            """
            SequenceValue = (1, 2, 1, 3)
            SequenceValue.distinct
            distinct(SequenceValue)
            """,
            1,
            2,
            3,
            1,
            2,
            3);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_TakeAndSkip_ExplicitReceiverSweep()
        => AssertEval(
            """
            Values = 1, 2, 3
            Data = (7, 6, 4, 2, 1), (1, 2, 3, 4, 5)
            Values.take(2)
            take(Values, 2)
            Values.skip(1)
            skip(Values, 1)
            (Data:0).take(2)
            take(Data:0, 2)
            (Data:0).skip(2)
            skip(Data:0, 2)
            """,
            1,
            2,
            1,
            2,
            2,
            3,
            2,
            3,
            7,
            6,
            7,
            6,
            4,
            2,
            1,
            4,
            2,
            1);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_TakeAndSkip_SequenceValueReceiversAgreeWithPlainCall()
    {
        AssertEval(
            """
            SequenceValue = (1, 2, 3)
            SequenceValue.take(2)
            take(SequenceValue, 2)
            """,
            1,
            2,
            1,
            2);

        AssertEval(
            """
            SequenceValue = (1, 2, 3)
            SequenceValue.skip(1)
            skip(SequenceValue, 1)
            """,
            2,
            3,
            2,
            3);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_InlineReceiver_StripsOneOuterBlockLayer()
        => AssertEval(
            """
            Add = x + total
            AddOne = x + 1
            IsLarge = x > 1
            (1, 2, 3).count
            (1, 2, 3).contains(2)
            (3, 1, 2).order
            (5, 6, 7).first
            (5, 6, 7).last
            (1, 2, 1, 3).distinct
            (1, 2, 3).take(2)
            (1, 2, 3).skip(1)
            (10, 4, 7).min
            {10, 4, 7}.max
            {3, 5, 3}.sum
            (10, 4, 7).avg
            (1, 2, 3).map(AddOne)
            {1, 2, 3, 4}.filter(IsLarge)
            (1, 2, 3).reduce(Add, 0)
            """,
            3,
            1,
            1,
            2,
            3,
            5,
            7,
            1,
            2,
            3,
            1,
            2,
            2,
            3,
            4,
            10,
            11,
            7,
            2,
            3,
            4,
            2,
            3,
            4,
            6);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_NumericAggregations_ProjectionSweep()
        => AssertEval(
            """
            Values = 1, 2, 3
            Data = (3, 1, 2), (9, 8, 7)
            Values.sum
            Values.avg
            Values.min
            Values.max
            (Data:0).sum
            sum(Data:0)
            (Data:0).avg
            avg(Data:0)
            (Data:0).min
            min(Data:0)
            (Data:0).max
            max(Data:0)
            """,
            6,
            2,
            1,
            3,
            6,
            6,
            2,
            2,
            1,
            1,
            3,
            3);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_NumericAggregations_MultiOutputHelpersMatchPlainCall()
    {
        AssertEval(
            """
            Values = 1, 2, 3
            sum(Values)
            avg(Values)
            min(Values)
            max(Values)
            """,
            6,
            2,
            1,
            3);

        AssertEval(
            """
            SequenceValue = (1, 2, 3)
            SequenceValue.sum
            """,
            6);

        AssertEval(
            """
            SequenceValue = (1, 2, 3)
            SequenceValue.avg
            """,
            2);

        AssertEval(
            """
            SequenceValue = (1, 2, 3)
            SequenceValue.min
            """,
            1);

        AssertEval(
            """
            SequenceValue = (1, 2, 3)
            SequenceValue.max
            """,
            3);
    }

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Map_ExplicitReceiverSweep()
        => AssertEval(
            """
            ItemCount(x) = x.count
            AddOne = x + 1
            Items = (1, 2, 3), 7
            SequenceValue = (1, 2, 3)
            Data = (1, 2, 3), (4, 5, 6)
            Items.map(ItemCount)
            map(Items, ItemCount)
            SequenceValue.map(ItemCount)
            map(SequenceValue, ItemCount)
            (Data:0).map(AddOne)
            map(Data:0, AddOne)
            """,
            3,
            1,
            3,
            1,
            1,
            1,
            1,
            1,
            1,
            1,
            2,
            3,
            4,
            2,
            3,
            4);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Filter_ExplicitReceiverSweep()
        => AssertEval(
            """
            KeepCountThree(x) = x.count == 3
            IsLarge = x > 1
            Items = (1, 2, 3), (4, 5, 6), 7
            SequenceValue = (1, 2, 3)
            Data = (1, 2, 3), (4, 5, 6)
            Items.filter(KeepCountThree).count
            filter(Items, KeepCountThree).count
            SequenceValue.filter(KeepCountThree).count
            filter(SequenceValue, KeepCountThree).count
            (Data:0).filter(IsLarge).count
            filter(Data:0, IsLarge).count
            """,
            2,
            2,
            0,
            0,
            2,
            2);

    [Fact]
    public void Eval_SequenceBuiltinDotCall_Reduce_ExplicitReceiverSweep()
        => AssertEval(
            """
            AddItemCount(item, acc) = item.count + acc
            Add = x + total
            Items = (1, 2, 3), 7
            SequenceValue = (1, 2, 3)
            Data = (1, 2, 3), (4, 5, 6)
            Items.reduce(AddItemCount, 0)
            reduce(Items, AddItemCount, 0)
            SequenceValue.reduce(AddItemCount, 0)
            reduce(SequenceValue, AddItemCount, 0)
            (Data:0).reduce(Add, 0)
            reduce(Data:0, Add, 0)
            """,
            4,
            4,
            3,
            3,
            6,
            6);

    // â”€â”€ User-defined functions â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_UserFunction_SingleParam()
    {
        var source = """
            F = x + 1
            F(5)
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_UserFunction_MultipleParams()
    {
        var source = """
            Add = a + b
            Add(3, 4)
            """;
        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_UserFunction_WithBraces()
    {
        var source = """
            Double = x * 2
            Double{3}
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_UserFunction_ReturnsMultipleOutputs()
    {
        var source = """
            Swap = a, b
            Swap(1, 2)
            """;
        AssertEval(source, 1, 2);
    }

    [Fact]
    public void Eval_UserFunction_Chained()
    {
        var source = """
            F = x + 1
            F(F(1))
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_UserFunction_RecursiveProperty()
    {
        var source = """
            Numbers = 3, 5, 9
            Numbers:0
            """;
        AssertEval(source, 3);
    }

    // â”€â”€ Complex examples â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_SumExample_Returns24()
    {
        var source = """
            Numbers = 3, 5, 9, 1, 0, 6
            Add = a + 1, total + Numbers:a
            Sum = repeat(Add, (6), 0, 0) : 1
            Sum
            """;
        AssertEval(source, 24);
    }

    [Fact]
    public void Eval_Fibonacci()
    {
        var source = """
            Fib = a + b, a
            repeat(Fib, (10), 1, 0):0
            """;
        AssertEval(source, 89);
    }

    [Fact]
    public void Eval_ConditionalMax()
    {
        AssertEval("if(5 > 3, (5), (3))", 5);
        AssertEval("if(2 > 7, (2), (7))", 7);
    }

    // Spread

    [Fact]
    public void Eval_SequenceSpread_SpreadsReferencedResults()
    {
        var source = """
            A = 1, 2
            B = 3, 4
            atoms((A.spread B))
            """;
        AssertEval(source, 1, 2, 3, 4);
    }

    // â”€â”€ Math built-in â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_MathPi_ReturnsMathPI()
    {
        var result = Eval("Math.Pi");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatPi, result.Value[0]);
    }

    [Fact]
    public void Eval_MathE_ReturnsMathE()
    {
        var result = Eval("Math.E");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatE, result.Value[0]);
    }

    [Fact]
    public void Eval_MathPi_InExpression()
    {
        var result = Eval("Math.Pi * 2");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatPi * 2, result.Value[0]);
    }

    [Fact]
    public void Eval_MathE_InExpression()
    {
        var result = Eval("Math.E + 1");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatE + 1, result.Value[0]);
    }

    [Fact]
    public void Eval_MathPi_InPropertyBody()
    {
        var source = """
            Circumference = Math.Pi * 2 * r
            Circumference(5)
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatPi * 2 * 5, result.Value[0]);
    }

    [Fact]
    public void Eval_MathPi_UserPropertyOverrides()
    {
        var source = """
            Math = (Pi = 3
            Pi)
            Math.Pi
            """;
        AssertEval(source, 3);
    }

    // â”€â”€ Math functions â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_MathAbs_Positive()
        => AssertEval("Math.Abs(5)", 5);

    [Fact]
    public void Eval_MathAbs_Negative()
        => AssertEval("Math.Abs(-3)", 3);

    [Fact]
    public void Eval_MathCeil()
        => AssertEval("Math.Ceil(2.3)", 3);

    [Fact]
    public void Eval_MathFloor()
        => AssertEval("Math.Floor(2.7)", 2);

    [Fact]
    public void Eval_MathRound()
        => AssertEval("Math.Round(2.5, 0)", 3);

    [Fact]
    public void Eval_MathRound_Up()
        => AssertEval("Math.Round(3.5, 0)", 4);

    [Fact]
    public void Eval_MathRound_WithDigits()
        => AssertEval("Math.Round(1.234, 2)", 1.23m);

    [Fact]
    public void Eval_MathRound_WithDigits_RoundsMidpointAwayFromZero()
        => AssertEval("Math.Round(1.225, 2)", 1.23m);

    [Fact]
    public void Eval_MathRound_WithDigits_WorksAfterOpenMath()
        => AssertEval("open Math\nRound(1.236, 2)", 1.24m);

    [Fact]
    public void Eval_MathRound_WithFractionalDigits_Fails()
        => AssertEvalFailsWithIllegalInEval("Math.Round(1.234, 2.5)", "digits must be an integer");

    [Fact]
    public void Eval_MathSign_Positive()
        => AssertEval("Math.Sign(42)", 1);

    [Fact]
    public void Eval_MathSign_Negative()
        => AssertEval("Math.Sign(-7)", -1);

    [Fact]
    public void Eval_MathSign_Zero()
        => AssertEval("Math.Sign(0)", 0);

    [Fact]
    public void Eval_MathSqrt()
        => AssertEval("Math.Sqrt(9)", 3);

    [Fact]
    public void Eval_MathPow()
        => AssertEval("Math.Pow(2, 10)", 1024);

    [Fact]
    public void Eval_MathLn()
    {
        var result = Eval("Math.Ln(Math.E)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(1.0m, result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathLg()
    {
        var result = Eval("Math.Lg(1000)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(3.0m, result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathLog()
    {
        var result = Eval("Math.Log(8, 2)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(3.0m, result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathSin()
    {
        var result = Eval("Math.Sin(0)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(0.0m, result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathCos()
    {
        var result = Eval("Math.Cos(0)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(1.0m, result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathAsin()
    {
        var result = Eval("Math.Asin(1)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal((decimal)(Math.PI / 2), result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathAcos()
    {
        var result = Eval("Math.Acos(1)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(0.0m, result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathTan()
    {
        var result = Eval("Math.Tan(0)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(0.0m, result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathTan_NearSingularity_ReturnsLargeValue()
    {
        // Tan(Pi/2) is near a singularity — result is a large finite value.
        // After normalization, it should still be a large number (not zero or error).
        var result = Eval("Math.Tan(Math.Pi/2)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.True(result.Value[0] > 1_000_000_000_000m, "Tan near singularity should be large");
    }

    [Fact]
    public void Eval_MathSin_PiOverSix()
    {
        // Verify trig with Pi-derived args: sin(π/6) ≈ 0.5
        var result = Eval("Math.Sin(Math.Pi/6)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(0.5m, result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathAtan()
    {
        var result = Eval("Math.Atan(1)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal((decimal)(Math.PI / 4), result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathAtan2()
    {
        var result = Eval("Math.Atan2(1, 1)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal((decimal)(Math.PI / 4), result.Value[0], 10);
    }

    // ── Trig normalization (floating-point residue cleanup) ─────────────────

    [Fact]
    public void Eval_MathRandom_ReturnsNumberInUnitInterval()
    {
        var result = Eval("Math.Random(0, 1)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.True(result.Value[0] >= 0m && result.Value[0] < 1m);
    }

    [Fact]
    public void Eval_MathRandom_ReturnsNumberInHalfOpenRange()
    {
        var result = Eval("Math.Random(1, 100)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.True(result.Value[0] >= 1m && result.Value[0] < 100m);
    }

    [Fact]
    public void Eval_MathRandom_RejectsEmptyRange()
        => AssertEvalFailsWithIllegalInEval("Math.Random(1, 1)", "start must be less than end");

    [Fact]
    public void Eval_MathRandom_RequiresBoundsForPropertyStyleAccess()
    {
        var error = GetEvalError("Math.Random");
        Assert.NotNull(error);
        while (error is EvalError.WithContext context)
            error = context.Inner;

        var unresolved = Assert.IsType<EvalError.UnresolvedImplicitParams>(error);
        Assert.Equal(["start", "end"], unresolved.ParamNames);
    }

    [Fact]
    public void Eval_MathRandom_RequiresBoundsForExplicitCall()
        => AssertEvalFailsWithArityMismatch("Math.Random()", expected: 2, actual: 0);

    [Fact]
    public void Eval_MathRandomInt_ReturnsOnlyWholeNumberInPositiveInterval()
        => AssertEval("Math.RandomInt(5, 6)", 5m);

    [Fact]
    public void Eval_MathRandomInt_ReturnsOnlyWholeNumberInNegativeInterval()
        => AssertEval("Math.RandomInt(-5, -4)", -5m);

    [Fact]
    public void Eval_MathRandomInt_DoesNotUseInt32RangeLimits()
        => AssertEval("Math.RandomInt(3000000000, 3000000001)", 3000000000m);

    [Fact]
    public void Eval_MathRandomInt_ReturnsWholeNumberInHalfOpenRange()
    {
        var result = Eval("Math.RandomInt(1, 7)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);

        var value = result.Value[0];
        Assert.Equal(Math.Floor(value), value);
        Assert.True(value >= 1m && value < 7m);
    }

    [Theory]
    [InlineData("Math.RandomInt(2.99, 3.2)")]
    [InlineData("Math.RandomInt(1.5, 10)")]
    [InlineData("Math.RandomInt(1, 10.5)")]
    public void Eval_MathRandomInt_RejectsDecimalBounds(string source)
        => AssertEvalFailsWithIllegalInEval(source, "bounds must be whole numbers");

    [Theory]
    [InlineData("Math.RandomInt(10, 10)")]
    [InlineData("Math.RandomInt(20, 10)")]
    public void Eval_MathRandomInt_RejectsEmptyOrReversedRange(string source)
        => AssertEvalFailsWithIllegalInEval(source, "start must be less than end");

    [Theory]
    [InlineData("Math.RandomInt()", 0)]
    [InlineData("Math.RandomInt(1)", 1)]
    [InlineData("Math.RandomInt(1, 2, 3)", 3)]
    public void Eval_MathRandomInt_RequiresTwoArguments(string source, int actual)
        => AssertEvalFailsWithArityMismatch(source, expected: 2, actual);

    [Fact]
    public void Eval_MathRand_IsUnknownMember()
        => AssertUnknownDotMember("Math.Rand", "Rand");

    [Fact]
    public void Eval_MathRandCall_IsUnknownMember()
        => AssertUnknownDotMember("Math.Rand()", "Rand");

    [Fact]
    public void Eval_MathRandInt_IsUnknownMember()
        => AssertUnknownDotMember("Math.RandInt(1, 7)", "RandInt");

    [Fact]
    public void Eval_ExplicitZeroParameterCall_ReevaluatesRandomPropertyBody()
    {
        const int maxAttempts = 20;
        var source = """
            Fun = Math.Random(0, 1), Math.Random(0, 1)
            Fun(), Fun()
            """;

        for (var attempt = 0; attempt < maxAttempts; attempt++)
        {
            var result = Eval(source);
            Assert.True(result.IsOk);
            Assert.Equal(4, result.Value.Count);
            Assert.All(result.Value, value => Assert.True(value >= 0m && value < 1m));

            if (result.Value.Distinct().Count() == result.Value.Count)
                return;
        }

        Assert.Fail("Expected explicit zero-parameter calls to re-evaluate the random property body.");
    }

    [Fact]
    public void Eval_PropertyStyleZeroParameterAccess_ReusesCachedRandomPropertyBody()
    {
        var result = Eval(
            """
            Fun = Math.Random(0, 1), Math.Random(0, 1)
            Fun, Fun
            """);

        Assert.True(result.IsOk);
        Assert.Equal(4, result.Value.Count);
        Assert.All(result.Value, value => Assert.True(value >= 0m && value < 1m));
        Assert.Equal(result.Value[0], result.Value[2]);
        Assert.Equal(result.Value[1], result.Value[3]);
    }

    [Fact]
    public void Eval_MathSin_Pi_ReturnsZero()
        => AssertEval("Math.Sin(Math.Pi)", 0);

    [Fact]
    public void Eval_MathCos_PiOver2_ReturnsZero()
        => AssertEval("Math.Cos(Math.Pi / 2)", 0);

    [Fact]
    public void Eval_MathTan_Pi_ReturnsZero()
        => AssertEval("Math.Tan(Math.Pi)", 0);

    [Fact]
    public void Eval_MathSin_Zero_ReturnsZero()
        => AssertEval("Math.Sin(0)", 0);

    [Fact]
    public void Eval_MathCos_Zero_ReturnsOne()
        => AssertEval("Math.Cos(0)", 1);

    [Fact]
    public void Eval_MathSin_One_ReturnsApproximate()
    {
        // Sin(1) ≈ 0.8414709848.spread — should be a sensible approximate result
        var result = Eval("Math.Sin(1)");
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(0.841470984807897m, result.Value[0], 10);
    }

    [Fact]
    public void Eval_MathSin_Pi_ViaOpen_ReturnsZero()
    {
        var source = """
            open Math
            Sin(Pi)
            """;
        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_MathSqrt_InExpression()
        => AssertEval("Math.Sqrt(16) + 1", 5);

    [Fact]
    public void Eval_MathFn_ViaOpen()
    {
        var source = """
            open Math
            Abs(-5)
            """;
        AssertEval(source, 5);
    }

    [Fact]
    public void Eval_MathFn_ViaOpen_TwoParam()
    {
        var source = """
            open Math
            Pow(2, 8)
            """;
        AssertEval(source, 256);
    }

    // â”€â”€ Open resolution â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Open_MathPi()
    {
        var source = """
            open Math
            Pi
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatPi, result.Value[0]);
    }

    [Fact]
    public void Eval_Open_MathE()
    {
        var source = """
            open Math
            E
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatE, result.Value[0]);
    }

    [Fact]
    public void Eval_Open_MathInExpression()
    {
        var source = """
            open Math
            Pi * 2
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatPi * 2, result.Value[0]);
    }

    [Fact]
    public void Eval_Open_UserDefinedModule()
    {
        var source = """
            M = (public X = 42
            X)
            open M
            X
            """;
        AssertEvalAllPublic(source, 42);
    }

    [Fact]
    public void Eval_Open_EllipsisTargetFails()
    {
        // `...` is not open-target syntax: the parser rejects it with a
        // targeted diagnostic before evaluation ever runs.
        var source = """
            A = (public X = 1
            X)
            B = (public Y = 2
            Y)
            open A...B
            X + Y
            """;
        var parseResult = Parser.Parse(source);
        Assert.True(parseResult.HasErrors);
        Assert.Contains(
            parseResult.Diagnostics,
            d => d.Message.Contains("`...` is not valid in open targets"));

        AssertEvalAllPublicFails(source);
    }

    [Fact]
    public void Eval_Open_SpreadExpressionTargetFails()
    {
        // A named spread expression is not an open form: the parser rejects
        // it before evaluation ever runs.
        var source = """
            A = (public X = 1
            X)
            open spread(A)
            X
            """;
        var parseResult = Parser.Parse(source);
        Assert.True(parseResult.HasErrors);
        Assert.Contains(
            parseResult.Diagnostics,
            d => d.Message.Contains("Invalid open form: 'spread' is not allowed in open declarations"));

        AssertEvalAllPublicFails(source);
    }

    [Fact]
    public void Eval_Open_MissingProperty_Fails()
    {
        var source = """
            open Math
            Foo
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_Open_InPropertyBody()
    {
        var source = """
            open Math
            Circumference = Pi * 2 * r
            Circumference(5)
            """;
        var result = Eval(source);
        Assert.True(result.IsOk);
        Assert.Single(result.Value);
        Assert.Equal(KatPi * 2 * 5, result.Value[0]);
    }

    [Fact]
    public void Eval_Open_DirectFunctionOpen()
    {
        var source = """
            Lib = (public F = x + 1)
            open Lib
            F(10)
            """;
        AssertEvalAllPublic(source, 11);
    }

    [Fact]
    public void Eval_Open_PublicMemberBodyCanCallBuiltinIf()
    {
        var source = """
            open Vec
            Vec = {
                public Test = if(x > 0, 1, 0)
            }
            Test(35)
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Open_PublicMemberBodyCanCallBuiltinMath()
    {
        var source = """
            open Vec
            Vec = {
                public Magnitude = Math.Sqrt(x * x + y * y)
            }
            Magnitude(3, 4)
            """;
        AssertEval(source, 5);
    }

    [Fact]
    public void Eval_Open_PublicMemberBodyCanCallBuiltinSum()
    {
        var source = """
            open Vec
            Vec = {
                public SumPair = (x, y).sum
            }
            SumPair(3, 4)
            """;
        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_Open_PublicMemberCallMatchesOwnerQualifiedCall()
    {
        var source = """
            open Vec
            Vec = {
                public Test = if(x > 0, 1, 0)
            }
            Direct = Vec.Test(35)
            Opened = Test(35)
            Direct == Opened
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Open_PublicZeroArgMemberBodyCanCallBuiltinIf()
    {
        var source = """
            open Vec
            Vec = {
                public Test = if(1 > 0, 10, 20)
            }
            Test
            """;
        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Open_PublicMemberSeesDefinitionSiteSibling()
    {
        var source = """
            open Vec
            Vec = {
                Helper = 10
                public Test = Helper + x
            }
            Test(5)
            """;
        AssertEval(source, 15);
    }

    [Fact]
    public void Eval_Open_PublicMemberDoesNotSeeOpenerLocalShadow()
    {
        var source = """
            A = 10
            Vec = {
                public Test = A + x
            }
            Scope = {
                open Vec
                A = 100
                Test(5)
            }
            Scope
            """;
        AssertEval(source, 15);
    }

    [Fact]
    public void Eval_Open_PrivateMemberRemainsHidden()
    {
        var source = """
            Vec = {
                Hidden = 10
                public Test = 1
            }
            open Vec
            Hidden
            """;
        var result = Eval(source);
        Assert.True(result.IsError);
    }

    [Fact]
    public void Eval_Open_PublicMemberAmbiguityRemainsAnError()
    {
        var source = """
            A = {
                public Test = 1
            }
            B = {
                public Test = 2
            }
            open A, B
            Test
            """;
        var result = Eval(source);
        Assert.True(result.IsError);
        Assert.IsType<EvalError.AmbiguousOpen>(Innermost(result.Error));
    }

    [Fact]
    public void Eval_Open_DotAccess_NestedResolve()
    {
        var source = """
            Lib = (Helper = x + 1
              UseHelper = Helper(x)
            )
            Lib.UseHelper(10)
            """;
        AssertEval(source, 11);
    }


    [Fact]
    public void Eval_Open_LibraryOpenWithNestedResolve()
    {
        var source = """
            Lib = (public Helper = x + 1
              public UseHelper = Helper(x)
            )
            open Lib
            UseHelper(10)
            """;
        AssertEvalAllPublic(source, 11);
    }

    [Fact]
    public void Eval_Open_LibraryIsolatedFromOpenerScope()
    {
        // In the Opens model, libraries are isolated: they do NOT get access
        // to the opener's scope. Fn lives in Wrapper but is not visible to Lib.
        var source = """
            Lib = (Apply = Fn(x))
            Wrapper = (
              Fn = x * 2
              open Lib
              Apply(5)
            )
            Wrapper
            """;
        AssertEvalAllPublicFails(source);
    }

    [Fact]
    public void Eval_Open_LibraryCannotAccessOpenerProperty()
    {
        // Library's property references a name that only exists in the opening scope.
        // Opens are isolated â€” Factor is not visible to Lib.
        var source = """
            Lib = (Calc = x * Factor)
            Main = (
              Factor = 3
              open Lib
              Calc(5)
            )
            Main
            """;
        AssertEvalAllPublicFails(source);
    }

    [Fact]
    public void Eval_Open_LibraryWithOwnDependencies()
    {
        // A library can reference its own properties (sibling resolution works).
        var source = """
            Lib = (
              public Helper = x + 1
              public UseHelper = Helper(x)
            )
            open Lib
            UseHelper(10)
            """;
        AssertEvalAllPublic(source, 11);
    }

    // â”€â”€ Extension call (dot-call) â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_DotCall_LexicalSingleParam()
    {
        // Lean: resolveAlg on literal fails â†’ use algorithm target instead
        var source = """
            Inc = x + 1
            V = 5
            V.Inc
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_DotCall_LexicalWithArgs()
    {
        // Lean: resolveAlg on literal fails â†’ use algorithm target instead
        var source = """
            Add = a + b
            V = 3
            V.Add(4)
            """;
        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_DotCall_Chaining()
    {
        // Lean: resolveAlg on literal fails â†’ use algorithm target instead
        var source = """
            Inc = x + 1
            Double = x * 2
            V = 3
            V.Inc.Double
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_DotCall_StructuralProperty()
    {
        // 0-param structural property â†’ value access (navigation only)
        var source = """
            X = (Inc = x + 1
            5)
            X.Inc(5)
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_DotCall_StructuralProperty_NoArgs_Fails()
    {
        // Structural property with params but no args â†’ arity mismatch
        // (navigation only: no receiver injection for structural properties)
        var source = """
            X = (Inc = x + 1
            5)
            X.Inc
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_DotCall_StructuralWithArgs()
    {
        // Navigation only: all args must be provided explicitly (no receiver injection)
        var source = """
            X = (Add = a + b
            5)
            X.Add(5, 10)
            """;
        AssertEval(source, 15);
    }

    [Fact]
    public void Eval_DotCall_StructuralNoReceiverInjection()
    {
        // Confirm receiver value is NOT injected as first arg.
        // X has output 42, but F gets args directly: a=10, b=20 â†’ 30 (not 42+10=52)
        var source = """
            X = (F = a + b
            42)
            X.F(10, 20)
            """;
        AssertEval(source, 30);
    }

    [Fact]
    public void Eval_DotCall_LexicalFallback_ReceiverIsLeft()
    {
        // Num.Double: receiver=Num (left), name=Double (right)
        // Lexical fallback: call Double(Num) -> x=3, x*2=6
        var source = """
            Num = 3
            Double = x * 2
            Num.Double
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_DotCall_MissingProperty_UsesKatLangFacingMessage()
    {
        var source = """
            Lib = {
                A = 1
            }
            Lib.B
            """;

        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var contextual = Assert.IsType<EvalError.WithContext>(result.Error);
        var dotContext = Assert.IsType<DotCallContext>(contextual.ErrorContext);
        Assert.Equal("Lib", dotContext.ReceiverDescription);
        Assert.Equal("B", dotContext.PropertyName);
        var unresolved = Assert.IsType<EvalError.UnknownName>(contextual.Inner);
        Assert.Equal("B", unresolved.Name);

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.DoesNotContain("dotCall", formatted);
        Assert.DoesNotContain("Unknown name: B", formatted);
        Assert.Contains("Property 'B' was not found on `Lib`", formatted);
        Assert.Contains("visible algorithm or property named 'B'", formatted);
        Assert.Contains("`Lib` as the first argument", formatted);
    }

    [Fact]
    public void Eval_DotCall_MissingProperty_OnExpression_RendersReceiver()
    {
        var result = EvalFull("(2 + 3).B");
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("`(2 + 3)`", formatted);
        Assert.Contains("Property 'B' was not found", formatted);
    }

    [Fact]
    public void Eval_DotCall_LexicalFallback_WithVisibleName_StillWorks()
    {
        var source = """
            B = x + 1
            5.B
            """;

        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_UnknownName_OutsideDotCall_RemainsPlain()
    {
        var formatted = KatLangError.FromEvalError(new EvalError.UnknownName("B")).Message;
        Assert.Equal("Unknown name: B", formatted);
    }

    [Fact]
    public void Eval_MissingOutput_DefinitionOnlyProgram_FailsWhenResultIsRequested()
        => AssertMissingOutputMessage(
            """
            A = {
                X = 1
            }
            """,
            RunResult.NoProgramOutput.DefaultMessage);

    [Fact]
    public void Eval_MissingOutput_PropertyAccess_RemainsValid()
        => AssertEval(
            """
            A = {
                X = 1
            }
            A.X
            """,
            1);

    [Fact]
    public void Eval_MissingOutput_HigherOrderArgument_RemainsValid()
        => AssertEval(
            """
            Apply(f) = f(4)
            Inc(x) = x + 1
            Apply(Inc)
            """,
            5);

    [Fact]
    public void Eval_MissingOutput_NestedNoOutputProperty_RemainsValidWhenNotForced()
        => AssertEval(
            """
            Holder = {
                F = {
                    X = 1
                }
                0
            }
            Holder
            """,
            0);

    [Fact]
    public void Eval_MissingOutput_FinalPropertyUse_UsesKatLangFacingMessage()
        => AssertMissingOutputMessage(
            """
            A = {
                X = 1
            }
            A
            """,
            $"Property 'A' has no defined output.\nAdd an output expression to 'A', or use `()` if the empty sequence value was intended. To use one of its properties, write `A.X`.",
            expectedLine: 4,
            expectedColumn: 1);

    [Fact]
    public void Eval_MissingOutput_CallUse_UsesKatLangFacingMessage()
        => AssertMissingOutputMessage(
            """
            A = {
                X = 1
            }
            A()
            """,
            $"Cannot call 'A' because it has no defined output.\nAdd an output expression, or use `()` if the empty sequence value was intended. To call one of its properties, use property access instead.",
            expectedLine: 4,
            expectedColumn: 1);

    [Fact]
    public void Eval_MissingOutput_CallUse_CarriesStructuredCallContext()
    {
        var result = EvalFull(
            """
            A = {
                X = 1
            }
            A()
            """);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var contextual = Assert.IsType<EvalError.WithContext>(result.Error);
        var callContext = Assert.IsType<CallContext>(contextual.ErrorContext);
        Assert.Equal("A", callContext.CalleeDescription);
        Assert.IsType<EvalError.MissingOutput>(contextual.Inner);

        Assert.Equal(
            $"Cannot call 'A' because it has no defined output.\nAdd an output expression, or use `()` if the empty sequence value was intended. To call one of its properties, use property access instead.",
            KatLangError.FromEvalError(result.Error).Message);
    }

    [Fact]
    public void Eval_MissingOutput_CallWithArgument_UsesKatLangFacingMessage()
        => AssertMissingOutputMessage(
            """
            Algo = {
                Prop = 7
            }
            Algo(6)
            """,
            $"Cannot call 'Algo' because it has no defined output.\nAdd an output expression, or use `()` if the empty sequence value was intended. To call one of its properties, use property access instead.",
            expectedLine: 4,
            expectedColumn: 1);

    [Fact]
    public void Eval_MissingOutput_BinaryUse_UsesKatLangFacingMessage()
        => AssertMissingOutputMessage(
            """
            A = {
                X = 1
            }
            A + 1
            """,
            $"Property 'A' has no defined output.\nAdd an output expression to 'A', or use `()` if the empty sequence value was intended. To use one of its properties, write `A.X`.",
            expectedLine: 4,
            expectedColumn: 1);

    [Fact]
    public void Eval_MissingOutput_UnaryUse_UsesKatLangFacingMessage()
        => AssertMissingOutputMessage(
            """
            A = {
                X = 1
            }
            -A
            """,
            $"Property 'A' has no defined output.\nAdd an output expression to 'A', or use `()` if the empty sequence value was intended. To use one of its properties, write `A.X`.",
            expectedLine: 4,
            expectedColumn: 2);

    [Fact]
    public void Eval_MissingOutput_AssignmentOnlyFailsWhenForcedLater()
        => AssertMissingOutputMessage(
            """
            A = {
                X = 1
            }
            B = A
            B
            """,
            $"Property 'A' has no defined output.\nAdd an output expression to 'A', or use `()` if the empty sequence value was intended. To use one of its properties, write `A.X`.");

    [Fact]
    public void Eval_MissingOutput_StructuralArgumentUse_CanStillSucceed()
        => AssertEval(
            """
            A = {
                X = 1
            }
            Use(f) = 0
            Use(A)
            """,
            0);

    [Fact]
    public void Eval_DotCall_ReversedReceiver_ProducesError()
    {
        // Double.Num: receiver=Double (parameterised), name=Num (0-param)
        // Lexical fallback: call Num(Double) -> Num has 0 params, 1 arg -> ArityMismatch
        var source = """
            Num = 3
            Double = x * 2
            Double.Num
            """;
        AssertEvalFails(source);
        var err = GetEvalError(source);
        Assert.IsType<EvalError.WithContext>(err);
        var inner = ((EvalError.WithContext)err!).Inner;
        Assert.IsType<EvalError.ArityMismatch>(inner);
        var arity = (EvalError.ArityMismatch)inner;
        Assert.Equal(0, arity.Expected); // Num has 0 params
        Assert.Equal(1, arity.Actual);   // 1 arg (the receiver Double)
    }

    [Fact]
    public void Eval_DotCall_WithArgs_LexicalFallback()
    {
        // V.Add(4): receiver=V, name=Add -> call Add(V, 4) -> a=3, b=4, a+b=7
        var source = """
            Add = a + b
            V = 3
            V.Add(4)
            """;
        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_NormalCallPreservesSequenceValueArgumentBoundary()
    {
        AssertEval(
            """
            F = a + b
            F(3, 7)
            """,
            10);

        AssertEvalFailsWithArityMismatch(
            """
            F = a + b
            F((3, 7))
            """,
            expected: 2,
            actual: 1);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_ScalarReceiverWithExplicitArgStillWorks()
    {
        var source = """
            F = a + b
            Output = (3).F(7)
            """;

        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_MultiOutputReceiverDoesNotSpread()
    {
        var source = """
            F = a + b
            (3, 7).F
            """;

        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_EmptyArgsDoNotSpreadMultiOutputReceiver()
    {
        var source = """
            F = a + b
            (3, 7).F()
            """;

        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_CountedPathDoesNotSpreadMultiOutputReceiver()
    {
        var source = """
            F = a + b
            ((3, 7).F).count
            """;

        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_OneParamReceivesSequenceValueReceiver()
    {
        var result = EvalFull(
            """
            G = x
            Output = (3, 7).G
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        AssertSequenceValueAtoms(result.Value, 3, 7);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_FinalExplicitSequenceValueArgDoesNotUnpack()
    {
        var source = """
            H = a + b + c
            Output = (3).H((4, 5))
            """;

        AssertEvalFailsWithArityMismatch(source, expected: 3, actual: 2);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_SequenceBuiltinsStillExpandReceiverContent()
    {
        AssertEval("(3, 7).sum", 10);
        AssertEval("(3, 7).count", 2);
        AssertEval("(3, 7).first", 3);
        AssertEval("(3, 7).last", 7);
    }

    [Fact]
    public void Eval_DotCall_StructuralProperty_ArityMismatch_Propagated()
    {
        // X.Inc: Inc has params but no args -> ArityMismatch propagated through dotCall
        var source = """
            X = (Inc = x + 1
            5)
            X.Inc
            """;
        AssertEvalFails(source);
        var err = GetEvalError(source);
        Assert.IsType<EvalError.WithContext>(err);
        var inner = ((EvalError.WithContext)err!).Inner;
        Assert.IsType<EvalError.ArityMismatch>(inner);
    }
    // â”€â”€ Division, mod, power â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    // ── Extension properties on arbitrary receiver expressions ───────────────

    [Fact]
    public void Eval_DotCall_IntegerLiteral_Receiver()
    {
        // 5.Square → Square(5) → n*n = 25
        var source = """
            Square = n * n
            5.Square
            """;
        AssertEval(source, 25);
    }

    [Fact]
    public void Eval_DotCall_ParenExpr_Receiver()
    {
        // (2 + 3).Square → Square(5) → n*n = 25
        var source = """
            Square = n * n
            Output = (2 + 3).Square
            """;
        AssertEval(source, 25);
    }

    [Fact]
    public void Eval_DotCall_ArbitraryExprReceiver_AlgorithmReceiver_StillWorks()
    {
        // A = 5; A.Square → Square(5) → 25 (existing behavior preserved)
        var source = """
            Square = n * n
            A = 5
            A.Square
            """;
        AssertEval(source, 25);
    }

    [Fact]
    public void Eval_DotCall_IntegerLiteral_Receiver_WithArgs()
    {
        // 5.Add(3) → Add(5, 3) → a+b = 8
        var source = """
            Add = a + b
            5.Add(3)
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_DotCall_ParenExpr_Receiver_WithArgs()
    {
        // (2 + 3).Add(7) → Add(5, 7) → a+b = 12
        var source = """
            Add = a + b
            Output = (2 + 3).Add(7)
            """;
        AssertEval(source, 12);
    }

    [Fact]
    public void Eval_DotCall_NumberLiteralReceiver()
    {
        var source = """
            Add = a + b
            2.Add(6)
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_DotCall_ParenExprReceiver()
    {
        var source = """
            Add = a + b
            Output = (2).Add(6)
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_DotCall_SameLineAdjacencyJoinsIntoPropertyBody()
    {
        // Same-line adjacency is an implicit comma, so the body is the
        // expression list `a + b, 2.Add(6)`, leaving no root output.
        var source = "Add = a + b 2.Add(6)";
        AssertEvalFailsWithMissingOutput(source);
    }

    [Fact]
    public void Eval_DotCall_DecimalLiteral_Receiver()
    {
        // 2.0.Double → Double(2.0) → x*2 = 4.0
        var source = """
            Double = x * 2
            2.0.Double
            """;
        AssertEval(source, 4.0m);
    }

    [Fact]
    public void Eval_Division()
        => AssertEval("10 / 4", 2.5m);

    [Fact]
    public void Eval_IntegerDivision()
        => AssertEval("10 div 3", 3);

    [Fact]
    public void Eval_IntegerDivision_Truncates()
        => AssertEval("-7 div 2", -3);

    [Fact]
    public void Eval_IntegerDivision_NegativeDivisor_Truncates()
        => AssertEval("7 div -2", -3);

    [Fact]
    public void Eval_DivisionByZero_Fails()
        => AssertEvalFails("5 / 0");

    [Fact]
    public void Eval_IntegerDivisionByZero_Fails()
        => AssertEvalFails("5 div 0");

    [Fact]
    public void Eval_Modulo()
        => AssertEval("10 mod 3", 1);

    // Modulo keeps the sign of the dividend (truncating remainder). The Lean
    // core mirrors this with Int.tmod; see CoreTests truncatingModuloMatchesRuntime.
    [Fact]
    public void Eval_Modulo_NegativeDividend_KeepsDividendSign()
        => AssertEval("-7 mod 2", -1);

    [Fact]
    public void Eval_Modulo_NegativeDivisor_KeepsDividendSign()
        => AssertEval("7 mod -2", 1);

    [Fact]
    public void Eval_Modulo_LeftSequenceValueOperand_ReportsNumericScalarDiagnostic()
        => AssertNumericScalarOperandFailure(
            "(3, 4, 5, 6) mod 2",
            "while evaluating `(3, 4, 5, 6) mod 2`",
            "operator `mod` expects numeric scalar operands",
            "left operand was a sequence value with 4 sequence elements: (3, 4, 5, 6)");

    [Fact]
    public void Eval_Modulo_RightSequenceValueOperand_ReportsNumericScalarDiagnostic()
        => AssertNumericScalarOperandFailure(
            "2 mod (3, 4, 5, 6)",
            "while evaluating `2 mod (3, 4, 5, 6)`",
            "operator `mod` expects numeric scalar operands",
            "right operand was a sequence value with 4 sequence elements: (3, 4, 5, 6)");

    [Fact]
    public void Eval_ModuloByZero_Fails()
        => AssertEvalFails("10 mod 0");

    [Fact]
    public void Eval_Power()
        => AssertEval("2 ^ 10", 1024);

    [Fact]
    public void Eval_Power_ZeroExponent()
        => AssertEval("5 ^ 0", 1);

    [Fact]
    public void Eval_Power_NegativeExponent()
        => AssertEval("2 ^ -3", 0.125m);

    // â”€â”€ Comparison operators â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_LessEqual_True()
        => AssertEval("3 <= 3", 1);

    [Fact]
    public void Eval_LessEqual_False()
        => AssertEval("4 <= 3", 0);

    [Fact]
    public void Eval_GreaterEqual_True()
        => AssertEval("3 >= 3", 1);

    [Fact]
    public void Eval_GreaterEqual_False()
        => AssertEval("2 >= 3", 0);

    [Fact]
    public void Eval_Equal_True()
        => AssertEval("5 == 5", 1);

    [Fact]
    public void Eval_Equal_False()
        => AssertEval("5 == 6", 0);

    [Fact]
    public void Eval_NotEqual_True()
        => AssertEval("5 != 6", 1);

    [Fact]
    public void Eval_NotEqual_False()
        => AssertEval("5 != 5", 0);

    // ── Structural value equality (==, !=) ───────────────────────────────────
    // `==` and `!=` compare KatLang values structurally across all value kinds:
    // numbers by value, strings by exact value, and sequence values by length
    // plus recursive pairwise equality. Different value kinds compare unequal
    // rather than raising a type mismatch. Ordering and arithmetic operators keep
    // their numeric-scalar-only path (covered separately below).

    [Fact]
    public void Eval_Equal_SequenceValue_SameReference_ReturnsOne()
        => AssertEval(
            """
            A = 1, 2
            A == A
            """,
            1);

    [Fact]
    public void Eval_Equal_IndependentSequences_StructurallyEqual_ReturnsOne()
        => AssertEval(
            """
            A = 1, 2
            B = 1, 2
            A == B
            """,
            1);

    [Fact]
    public void Eval_Equal_Sequences_DifferentElement_ReturnsZero()
        => AssertEval(
            """
            A = 1, 2
            B = 1, 3
            A == B
            """,
            0);

    [Fact]
    public void Eval_Equal_Sequences_DifferentLength_ReturnsZero()
        => AssertEval(
            """
            A = 1, 2
            B = 1, 2, 3
            A == B
            """,
            0);

    [Fact]
    public void Eval_Equal_NestedSequences_StructurallyEqual_ReturnsOne()
        => AssertEval(
            """
            A = 1, (2, 3)
            B = 1, (2, 3)
            A == B
            """,
            1);

    [Fact]
    public void Eval_Equal_NestedSequences_DifferentInnerElement_ReturnsZero()
        => AssertEval(
            """
            A = 1, (2, 3)
            B = 1, (2, 4)
            A == B
            """,
            0);

    [Fact]
    public void Eval_Equal_NumberVsSequence_DifferentKinds_ReturnsZero()
        => AssertEval("1 == (1, 2)", 0);

    [Fact]
    public void Eval_NotEqual_NumberVsSequence_DifferentKinds_ReturnsOne()
        => AssertEval("1 != (1, 2)", 1);

    [Fact]
    public void Eval_NotEqual_SequenceValue_SameReference_ReturnsZero()
        => AssertEval(
            """
            A = 1, 2
            A != A
            """,
            0);

    [Fact]
    public void Eval_NotEqual_Sequences_DifferentElement_ReturnsOne()
        => AssertEval(
            """
            A = 1, 2
            B = 1, 3
            A != B
            """,
            1);

    [Fact]
    public void Eval_Equal_GroupedSpread_ComparesAsSingleSequenceValue_ReturnsOne()
        => AssertEval(
            """
            A = 1, 2
            (A.spread) == A
            """,
            1);

    // Spread item supplies must not be silently vectorized by equality. A spread
    // `A.spread` cannot be a binary operand: `A.spread == A.spread` is a parse error (the
    // spread ends its expression, so the following `==` is unexpected). This
    // boundary is owned by the parser and is unchanged by structural equality —
    // equality never turns a spread item supply into an elementwise comparison. The
    // grouped form `(A.spread) == A` (covered above) is the supported way to compare
    // an opened-then-regrouped sequence value.
    [Fact]
    public void Eval_Equal_OpenedItemSupplies_NotSilentlyVectorized_IsParseError()
    {
        var parseResult = Parser.Parse(
            """
            A = 1, 2
            A.spread == A.spread
            """);
        Assert.True(parseResult.HasErrors);
    }

    [Fact]
    public void Eval_Add_SequenceValueOperands_StillRejectedWithNumericScalarDiagnostic()
        => AssertNumericScalarOperandFailure(
            """
            A = 1, 2
            A + A
            """,
            "while evaluating `A + A`",
            "operator `+` expects numeric scalar operands",
            "left operand was a sequence value with 2 sequence elements: (1, 2)");

    [Fact]
    public void Eval_LessThan_SequenceValueOperands_StillRejectedWithNumericScalarDiagnostic()
        => AssertNumericScalarOperandFailure(
            """
            A = 1, 2
            A < A
            """,
            "while evaluating `A < A`",
            "operator `<` expects numeric scalar operands",
            "left operand was a sequence value with 2 sequence elements: (1, 2)");

    // Structural equality preserves nesting; it must not flatten sequence values.
    // (1, (2, 3)) has shape [1, [2, 3]] while ((1, 2), 3) has shape [[1, 2], 3], so
    // even though both flatten to the same atoms they are structurally unequal.
    [Fact]
    public void Eval_Equal_NestedShapesDiffer_NotFlattened_ReturnsZero()
        => AssertEval("(1, (2, 3)) == ((1, 2), 3)", 0);

    // Sequence equality is ordered pairwise structural equality, not set equality.
    [Fact]
    public void Eval_Equal_DifferentOrder_IsOrderSensitive_ReturnsZero()
        => AssertEval("(1, 2) == (2, 1)", 0);

    // Empty sequence equality is stable across independently bound properties:
    // two distinct properties each bound to `()` compare equal.
    [Fact]
    public void Eval_Equal_EmptyPropertiesAcrossBindings_ReturnsOne()
        => AssertEval(
            """
            A = ()
            B = ()
            A == B
            """,
            1);

    [Fact]
    public void Eval_NotEqual_EmptyPropertiesAcrossBindings_ReturnsZero()
        => AssertEval(
            """
            A = ()
            B = ()
            A != B
            """,
            0);

    // Display formatting must not affect equality: equality compares numeric values,
    // so 1.2 and 1.20 are equal regardless of rendered decimal scale. The leading
    // DisplayDecimals directive (a display-only setting) does not change this.
    [Fact]
    public void Eval_Equal_DecimalScaleDoesNotAffectValueEquality_ReturnsOne()
        => AssertEval(
            """
            DisplayDecimals = 0
            1.2 == 1.20
            """,
            1);

    // Optimized-loop parity: a captured sequence value compared with `==` inside an
    // optimized repeat loop must use the same structural equality as normal
    // evaluation. The Equal node is planned (not a generic fallback) and runs entirely
    // inside the optimized loop harness, pinning that ApplyPlannedBinary delegates
    // equality to Evaluator.ApplyBinaryOperator and never reintroduces a numeric-only
    // fast path (which would throw a numeric-scalar type mismatch on the sequence
    // operands). `pair == pair` is 1, so x increments to 5 over 5 iterations.
    [Fact]
    public void Eval_OptimizedLoop_CapturedSequenceValueEquality_UsesStructuralEquality()
    {
        var source = """
            Outer(pair) = {
                Step = x + (pair == pair)
                Step.repeat(5, 0)
            }
            Outer((1, 2))
            """;

        // Generic and optimized modes must agree and both return 5.
        AssertEvalLoopModes(source, 5);

        var (result, stats) = EvalFullWithLoopDiagnostics(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        Assert.Equal([5m], result.Value.ToAtoms());

        // The optimized loop harness ran the equality every iteration with no fallback
        // to generic evaluation, so ApplyPlannedBinary handled the sequence-value Eq.
        Assert.Equal(1, stats.OptimizedLoopHits);
        Assert.Equal(5, stats.PlannedExpressionHits);
        Assert.Equal(0, stats.PlannedExpressionFallbacks);
        Assert.Equal(0, stats.GenericExpressionEvaluationsInsideOptimizedLoops);

        var plan = AssertSingleLoopPlan(stats, "Outer.Step.repeat");
        var output = AssertLoopExpression(plan, "output", 0);
        Assert.True(output.Planned);
        Assert.Equal(
            "Add(StateSlot(x), Equal(CapturedSlot(pair), CapturedSlot(pair)))",
            output.PlanSummary);
        Assert.Null(output.FallbackReason);
    }

    // â”€â”€ Logical operators â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_And_TrueTrue()
        => AssertEval("1 and 1", 1);

    [Fact]
    public void Eval_And_TrueFalse()
        => AssertEval("1 and 0", 0);

    [Fact]
    public void Eval_And_FalseFalse()
        => AssertEval("0 and 0", 0);

    [Fact]
    public void Eval_Or_TrueFalse()
        => AssertEval("1 or 0", 1);

    [Fact]
    public void Eval_Or_FalseFalse()
        => AssertEval("0 or 0", 0);

    [Fact]
    public void Eval_Xor_TrueFalse()
        => AssertEval("1 xor 0", 1);

    [Fact]
    public void Eval_Xor_TrueTrue()
        => AssertEval("1 xor 1", 0);

    [Fact]
    public void Eval_Xor_FalseFalse()
        => AssertEval("0 xor 0", 0);

    [Fact]
    public void Eval_Not_Zero()
        => AssertEval("not 0", 1);

    [Fact]
    public void Eval_Not_NonZero()
        => AssertEval("not 5", 0);

    [Fact]
    public void Eval_Not_DoubleNegation()
        => AssertEval("not not 1", 1);

    // â”€â”€ Operator combinations â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_CompoundExpression_IfWithComparison()
    {
        var source = """
            X = 10
            if(X >= 5, 1, 0)
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_LogicalInIf()
    {
        var source = """
            A = 3
            B = 7
            if(A > 0 and B > 0, 1, 0)
            """;
        AssertEval(source, 1);
    }

    // â”€â”€ Edge cases â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_EmptySource_HasNoDefinedOutput()
        => AssertMissingOutputMessage(
            "",
            RunResult.NoProgramOutput.DefaultMessage);

    [Fact]
    public void Eval_UndefinedProperty_Fails()
        => AssertEvalFails("X");

    [Fact]
    public void Eval_UnknownIdentifier_ReturnsUnresolvedImplicitParams()
    {
        // "Sum" is detected as a parameter by ParameterDetector, so the root
        // block has params=["Sum"].  Block value-position semantics:
        // 1+ params => UnresolvedImplicitParams.
        var err = GetEvalError("Sum");
        Assert.NotNull(err);
        while (err is EvalError.WithContext wc)
            err = wc.Inner;
        var uip = Assert.IsType<EvalError.UnresolvedImplicitParams>(err);
        Assert.Equal(["Sum"], uip.ParamNames);
    }

    [Fact]
    public void Eval_UnknownIdentifier_CarriesStructuredImplicitParameterContext()
    {
        var error = GetEvalError("Sum");
        Assert.NotNull(error);

        var contextual = Assert.IsType<EvalError.WithContext>(error);
        var implicitContext = Assert.IsType<ImplicitParameterContext>(contextual.ErrorContext);
        Assert.Equal(["Sum"], implicitContext.ParamNames);
        Assert.Equal(0, implicitContext.ProvidedArgumentCount);

        var unresolved = Assert.IsType<EvalError.UnresolvedImplicitParams>(contextual.Inner);
        Assert.Equal(["Sum"], unresolved.ParamNames);

        var formatted = KatLangError.FromEvalError(error).Message;
        Assert.Contains("KatLang interprets it as an implicit parameter", formatted);
        Assert.Contains("expected 1 argument, got 0", formatted);
        Assert.DoesNotContain("while evaluating", formatted);
    }

    [Fact]
    public void Eval_UnknownIdentifier_ReturnsUnresolvedImplicitParamsType()
    {
        // "Sum" becomes a parameter → block has 1 param → UnresolvedImplicitParams in value position.
        var err = GetEvalError("Sum");
        Assert.NotNull(err);
        while (err is EvalError.WithContext wc)
            err = wc.Inner;
        Assert.IsType<EvalError.UnresolvedImplicitParams>(err);
    }

    [Fact]
    public void Eval_DivByZero_HasCorrectSpan()
    {
        var err = GetEvalError("5 / 0");
        Assert.NotNull(err);
        Assert.NotNull(err.Span);
        // Binary expression "5 / 0" spans full expression
        Assert.Equal(1, err.Span.StartLineNumber);
        Assert.Equal(1, err.Span.StartColumn);
        Assert.Equal(1, err.Span.EndLineNumber);
        Assert.Equal(5, err.Span.EndColumn);
    }

    [Fact]
    public void Eval_UnknownIdentifier_MultiLine_ReturnsUnresolvedImplicitParams()
    {
        // Y is detected as a parameter → block has 1 param → UnresolvedImplicitParams.
        var source = """
            X = 5
            Y
            """;
        var err = GetEvalError(source);
        Assert.NotNull(err);
        while (err is EvalError.WithContext wc)
            err = wc.Inner;
        Assert.IsType<EvalError.UnresolvedImplicitParams>(err);
    }

    [Fact]
    public void Eval_WrongParamCount_Fails()
    {
        var source = """
            F = a + b
            F(1)
            """;
        AssertEvalFails(source);
    }

        [Fact]
        public void Eval_ArityMismatch_TooManyArguments_UsesUserFacingMessage()
        {
            AssertArityMismatchMessage(
                """
                A = x
                A(1, 2)
                """,
                "Callable `A(x)` expects 1 argument, but was called with 2 arguments.");
        }

        [Fact]
        public void Eval_ArityMismatch_TooFewArguments_UsesUserFacingMessage()
        {
            AssertArityMismatchMessage(
                """
                Add = a + b
                Add(1)
                """,
                "Callable `Add(a, b)` expects 2 arguments, but was called with 1 argument.");
        }

        [Fact]
        public void Eval_ArityMismatch_DirectCall_CarriesStructuredCallContext()
        {
            var source = """
                Add = a + b
                Add(1)
                """;

            var result = EvalFull(source);
            if (result.IsOk)
                Assert.Fail($"Expected evaluation failure but got: {result.Value}");

            var contextual = Assert.IsType<EvalError.WithContext>(result.Error);
            var callContext = Assert.IsType<CallContext>(contextual.ErrorContext);
            Assert.Equal("Add", callContext.CalleeDescription);

            var arity = Assert.IsType<EvalError.ArityMismatch>(contextual.Inner);
            Assert.Equal(2, arity.Expected);
            Assert.Equal(1, arity.Actual);
            Assert.NotNull(arity.Signature);
            Assert.Equal("Add(a, b)", arity.Signature.DisplayText);

            Assert.Equal(
                "Callable `Add(a, b)` expects 2 arguments, but was called with 1 argument.",
                KatLangError.FromEvalError(result.Error).Message);
        }

        [Fact]
        public void Eval_ArityMismatch_CountedFlatFixedDirectCall_UsesSignatureDisplay()
        {
            var source = """
                Add(a, b) = a + b
                Add(1).count
                """;

            var result = EvalFull(source);
            if (result.IsOk)
                Assert.Fail($"Expected evaluation failure but got: {result.Value}");

            var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
            Assert.Equal(2, arity.Expected);
            Assert.Equal(1, arity.Actual);
            Assert.NotNull(arity.Signature);
            Assert.Equal("Add(a, b)", arity.Signature.DisplayText);

            Assert.Contains(
                "Callable `Add(a, b)` expects 2 arguments, but was called with 1 argument.",
                KatLangError.FromEvalError(result.Error).Message,
                StringComparison.Ordinal);
        }

        [Fact]
        public void Eval_ArityMismatch_NoArgumentsProvided_UsesUserFacingMessage()
        {
            var source = """
                A = x
                A
                """;

            var result = EvalFull(source);
            if (result.IsOk)
                Assert.Fail($"Expected evaluation failure but got: {result.Value}");

            var contextual = Assert.IsType<EvalError.WithContext>(result.Error);
            var propertyContext = Assert.IsType<PropertyEvaluationContext>(contextual.ErrorContext);
            Assert.Equal("A", propertyContext.PropertyName);
            var arity = Assert.IsType<EvalError.ArityMismatch>(contextual.Inner);
            Assert.Equal(1, arity.Expected);
            Assert.Equal(0, arity.Actual);

            var formatted = KatLangError.FromEvalError(result.Error).Message;
            Assert.Equal("Property 'A' expects 1 parameter, but was called with 0 arguments.", formatted);
        }

        [Fact]
        public void Eval_ArityMismatch_ZeroParameterPropertyCalledWithArguments_UsesUserFacingMessage()
        {
            AssertArityMismatchMessage(
                """
                A = 1
                A(1)
                """,
                "Callable `A` expects 0 arguments, but was called with 1 argument.");
        }
        [Fact]
        public void Eval_ArityMismatch_InnerCall_SpanPointsToInnerCall()
        {
            // Inner has 0 params; calling Inner(param) inside Outer should produce
            // an error whose span points to Inner(param), not the outer Outer(50000).
            var source = """
                Inner = 5
                Outer = param - Inner(param)
                Outer(50000)
                """;
            var err = GetEvalError(source);
            Assert.NotNull(err);
            Assert.NotNull(err.Span);
            // Span should point to "Inner(param)" on line 2, NOT "Outer(50000)" on line 3.
            Assert.Equal(2, err.Span.StartLineNumber);
        }

    // â”€â”€ Grace operator end-to-end tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_VariadicParameter_DotCallReceiverIsOneCapturedItem()
    {
        // The ordinary receiver is one leading argument, so the variadic parameter is
        // the one-element list [(1, 2, 3)] — explicit receiver spread (below)
        // is what supplies the receiver's items.
        AssertEval(
            """
            Arg = 1, 2, 3
            Collect(list...) = list
            Output = Arg.Collect.count
            """,
            1);
    }

    [Fact]
    public void Eval_VariadicParameter_ExplicitReceiverSpreadCapturesReceiverTopLevelItems()
    {
        AssertEval(
            """
            Arg = 1, 2, 3
            Collect(list...) = list
            Output = (Arg.spread).Collect.count
            """,
            3);
    }

    [Fact]
    public void Eval_NormalParameter_DotCallStillPreservesReceiverBoundary()
    {
        AssertEval(
            """
            Arg = 1, 2, 3
            Collect(list) = list
            Arg.Collect.count
            """,
            3);
    }

    [Fact]
    public void Eval_VariadicParameter_PreservesNestedSequenceValues()
    {
        // The spread receiver supplies the two pair items, and each stays one
        // opaque sequence value inside the collected list: [(1, 2), (3, 4)].
        AssertEval(
            """
            Arg = (1, 2), (3, 4)
            Collect(list...) = list
            Output = (Arg.spread).Collect.count
            """,
            2);
    }

    [Fact]
    public void Eval_VariadicParameter_DoesNotReplaceAtomsRecursiveFlattening()
    {
        AssertEval(
            """
            Arg = (1, 2), (3, 4)
            Collect(list...) = list
            atoms(Arg.Collect).count
            """,
            4);
    }

    [Fact]
    public void Eval_VariadicParameter_WithPrefix_BindsFrontItem()
    {
        AssertEval(
            """
            Arg = 1, 2, 3
            Head(first, rest...) = first
            Head(1, (2, 3))
            """,
            1);
    }

    [Fact]
    public void Eval_VariadicParameter_WithPrefix_CapturesRemainingItems()
    {
        // The spread supplies 2 and 3 as separate slots, so the variadic parameter collects
        // the list [2, 3]. (An unspread `(2, 3)` would be one collected item.)
        AssertEval(
            """
            Arg = 1, 2, 3
            Tail(first, rest...) = rest
            Tail(1, (2, 3).spread).count
            """,
            2);
    }

    [Fact]
    public void Eval_VariadicParameter_WithSuffix_CapturesLeadingItems()
    {
        AssertEval(
            """
            Arg = 1, 2, 3
            Init(init..., last) = init
            Init((1, 2).spread, 3).count
            """,
            2);
    }

    [Fact]
    public void Eval_VariadicParameter_WithSuffix_BindsBackItem()
    {
        AssertEval(
            """
            Arg = 1, 2, 3
            Last(init..., last) = last
            Last(Arg, 3)
            """,
            3);
    }

    [Fact]
    public void Eval_VariadicParameter_BeforeSuffix_SupportsSequenceStyleScale()
    {
        // The spread receiver supplies the items; the suffix binds the factor.
        AssertEval(
            """
            Arg = 1, 2, 3
            Scale(values..., factor) = values.map{n * factor}
            Output = (Arg.spread).Scale(10)
            """,
            10, 20, 30);
    }

    [Fact]
    public void Eval_VariadicParameter_InlineSequenceSpreadDotCallWithSuffixSuppliesReceiverItems()
    {
        AssertEvalSequenceModes(
            """
            TotalWithFee(values..., fee) = values.sum + fee
            Output = ((10, 20, 30).spread).TotalWithFee(5)
            """,
            65);
    }

    [Fact]
    public void Eval_VariadicParameter_NamedMultiOutputSpreadDotCallWithSuffixSuppliesReceiverItems()
    {
        AssertEvalSequenceModes(
            """
            TotalWithFee(values..., fee) = values.sum + fee
            Data = 10, 20, 30
            (Data.spread).TotalWithFee(5)
            """,
            65);
    }

    [Fact]
    public void Eval_VariadicParameter_InlineTupleSpreadDotCallMatchesNamedReceiver()
    {
        AssertEvalSequenceModes(
            """
            TotalWithFee(values..., fee) = values.sum + fee
            Data = 10, 20, 30
            (Data.spread).TotalWithFee(5), ((10, 20, 30).spread).TotalWithFee(5)
            """,
            65, 65);
    }

    [Fact]
    public void Eval_VariadicParameter_NestedInlineTupleDotCall_ReceiverIsOneCollectedItem()
    {
        // The unspread `((10, 20, 30))` receiver is one leading argument, so the
        // rest collects [(10, 20, 30)] and the numeric `values.sum` fails on the
        // sequence-valued element. The spread forms above supply the items.
        var source = """
            TotalWithFee(values..., fee) = values.sum + fee
            Output = ((10, 20, 30)).TotalWithFee(5)
            """;

        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_NormalParameter_InlineTupleDotCallStillPreservesReceiverBoundary()
    {
        AssertEvalSequenceModes(
            """
            Collect(list) = list.count
            Output = (10, 20, 30).Collect
            """,
            3);
    }

    [Fact]
    public void Eval_VariadicParameter_SpreadReceiverExpandsReceiverItems()
    {
        // Only the parenthesized-spread receiver form supplies the receiver's
        // items to a leading flat variadic; the variadic parameter collects [10, 20, 30].
        AssertEvalSequenceModes(
            """
            Collect(list...) = list.count
            Output = ((10, 20, 30).spread).Collect
            """,
            3);
    }

    [Fact]
    public void Eval_SequenceBuiltin_InlineTupleDotCallBehaviorIsUnchanged()
    {
        AssertEvalSequenceModes("(10, 20, 30).sum", 60);

        AssertEvalSequenceModes("((10, 20, 30)).sum", 60);
    }

    [Fact]
    public void Eval_VariadicParameter_BeforeTwoSuffixes_SupportsSequenceStyleFilter()
    {
        AssertEval(
            """
            Arg = 1, 2, 3, 4, 5
            Between(values..., min, max) = values.filter{n >= min and n <= max}
            Output = (Arg.spread).Between(2, 4)
            """,
            2, 3, 4);
    }

    [Fact]
    public void Eval_VariadicParameter_PlainCallBindsListSourceAsOneElement()
    {
        // Arg is the exact list [1, 2, 3]; the plain call passes it as one
        // argument, so the variadic parameter collects [[1, 2, 3]] and the numeric body hits
        // the per-element constraint. Lean twin: Qmean(Vector) numeric error.
        var result = EvalFull(
            """
            Arg = range(1, 3)
            Qmean(values...) = values.sum / values.count
            Qmean(Arg)
            """);

        Assert.True(result.IsError);
        Assert.Contains(
            "sum expects each collection element to be a single numeric value",
            KatLangError.FromEvalError(result.Error).Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_VariadicParameter_ExplicitSpreadCapturesSourceItems()
    {
        AssertEval(
            """
            Arg = range(1, 3)
            Qmean(values...) = values.sum / values.count
            Qmean(Arg.spread)
            """,
            2);
    }

    [Fact]
    public void Eval_VariadicParameter_SpreadReceiverDotCallCapturesRangeItems()
    {
        // The parenthesized-spread receiver opens the range list's one boundary,
        // supplying its items to the variadic parameter.
        AssertEval(
            """
            Arg = range(1, 3)
            Qmean(values...) = values.sum / values.count
            Output = (Arg.spread).Qmean
            """,
            2);
    }

    [Fact]
    public void Eval_NormalParameter_WithSingleSequenceValueRange_RemainsOrdinary()
    {
        var result = EvalFull(
            """
            Arg = range(1, 3)
            Qmean_err(list) = list.sum / list.count
            Qmean_err(Arg)
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.Equal([2m], result.Value.ToAtoms());
    }

    [Fact]
    public void Eval_VariadicParameter_ReportsBindingErrorWhenNormalParametersCannotBind()
    {
        // F(first, rest..., last) is a comma deconstruction parameter list. F(1)
        // supplies one scalar item (not implicitly opened), but the two fixed
        // bindings first and last need at least two items.
        var result = EvalFull(
            """
            F(first, rest..., last) = first, rest, last
            F(1)
            """);

        Assert.True(result.IsError);
        var error = Innermost(result.Error);
        var arity = Assert.IsType<EvalError.VariadicArityMismatch>(error);
        Assert.Equal(2, arity.ExpectedMinimum);
        Assert.Equal(1, arity.Actual);
    }

    [Fact]
    public void Eval_SequenceValueVariadicParameter_CapturesImmediateSequenceValueItems()
    {
        AssertEval(
            """
            F((xs...)) = xs.count
            F((1, 2, 3))
            """,
            3);
    }

    [Fact]
    public void Eval_SequenceValueVariadicParameter_RemovesOnlyOneSequenceValueBoundary()
    {
        AssertEval(
            """
            F((xs...)) = xs.count
            F(((1, 2), 3))
            """,
            2);
    }

    [Fact]
    public void Eval_SequenceValueVariadicParameter_PreservesNestedSequenceValueItem()
    {
        var result = EvalFull(
            """
            F((xs...)) = xs:0
            F(((1, 2), 3))
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.True(
            Result.ValueComparer.Equals(ResultFromAtoms(1, 2), result.Value),
            $"Expected (1, 2) but got {result.Value}");
    }

    [Fact]
    public void Eval_SequenceValueVariadicParameter_RespectsExplicitCallSiteGroupingDepth()
    {
        // Top-level variadic (1): the grouped argument is one collected item, so
        // both call forms count 1. Pattern callees (2, 3) open their declared
        // grouping depth against the written argument: a matching depth exposes
        // the written items (3, or 2 for the two-item groups), while an extra
        // written level around a depth-1 pattern leaves one nested item.
        AssertEval(
            """
            CountSequenceValue1(values...) = values.count
            CountSequenceValue2((values...)) = values.count
            CountSequenceValue3(((values...))) = values.count

            CountSequenceValue1((1, 2, 3))
            CountSequenceValue1(((1, 2, 3)))
            CountSequenceValue2((1, 2, 3))
            CountSequenceValue2(((1, 2, 3)))
            CountSequenceValue2((((1, 2, 3))))
            CountSequenceValue3(((1, 2, 3)))
            CountSequenceValue3((((1, 2, 3))))
            CountSequenceValue2(((1, 2), 3))
            CountSequenceValue2((1, (2, 3)))
            """,
            1, 1, 3, 1, 1, 3, 3, 2, 2);
    }

    [Fact]
    public void Eval_NestedSequenceValueVariadicParameter_RejectsTooShallowExplicitSequenceValue()
    {
        var result = EvalFull(
            """
            CountSequenceValue3(((values...))) = values.count
            CountSequenceValue3((1, 2, 3))
            """);

        Assert.True(result.IsError);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
        Assert.Equal(1, arity.Expected);
        Assert.Equal(3, arity.Actual);
    }

    [Fact]
    public void Eval_SequenceValueVariadicParameter_ExplicitPropertyReferenceGroupingIsSourceBacked()
    {
        // The bare reference supplies Inner's canonical value, which the pattern
        // opens into its three items. Writing extra grouping around the
        // reference adds one written level, so the pattern's single opening
        // leaves Inner itself as the one collected item.
        AssertEval(
            """
            Inner = (1, 2, 3)
            CountSequenceValue2((values...)) = values.count

            CountSequenceValue2(Inner)
            CountSequenceValue2((Inner))
            CountSequenceValue2(((Inner)))
            """,
            3, 1, 1);
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_ParenthesizedScalarPropertyItemIsNotAnOrphanSequenceValue()
    {
        // `(A)` is one written grouping level around a single already-evaluated
        // item, so the bound item is the scalar 5 itself — never a
        // literal-unwritable orphan sequence value displaying as `(5)`.
        var result = EvalFull(
            """
            A = 5
            F((x, y)) = x
            F(((A), 6))
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.True(
            Result.ValueComparer.Equals(new Result.Atom(5), result.Value),
            $"Expected 5 but got {result.Value}");
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_ParenthesizedScalarPropertyItemComparesEqualToScalar()
    {
        AssertEval(
            """
            A = 5
            F((x, y)) = x == 5
            F(((A), 6))
            """,
            1);
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_ParenthesizedSequencePropertyItemStaysOneCanonicalItem()
    {
        // With A = (1, 2), the written grouping `(A)` supplies the canonical
        // value (1, 2) as one item — not an orphan ((1, 2)) — matching
        // assignment deconstruction of the same right-hand side.
        var result = EvalFull(
            """
            A = 1, 2
            F((x, y)) = x
            F(((A), 6))
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.True(
            Result.ValueComparer.Equals(ResultFromAtoms(1, 2), result.Value),
            $"Expected (1, 2) but got {result.Value}");
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_EmptySequenceSiblingItemIsPreserved()
    {
        // A non-spread `()` item is one visible item, exactly as in ordinary
        // sequence-value construction: the pattern sees ((), 6), so x binds ()
        // and y binds 6.
        var result = EvalFull(
            """
            F((x, y)) = x
            F(((), 6))
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.True(
            Result.ValueComparer.Equals(new Result.SequenceValue([]), result.Value),
            $"Expected () but got {result.Value}");

        AssertEval(
            """
            F((x, y)) = y
            F(((), 6))
            """,
            6);
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_GroupedEmptySequenceItemCanonicalizesLikeEmptySequence()
    {
        // `(())` canonicalizes to `()`, so as a written item it behaves exactly
        // like a bare `()` item.
        AssertEval(
            """
            F((x, y)) = y
            F(((()), 6))
            """,
            6);
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_SpreadOfEmptyStillContributesNoItems()
    {
        // Only an explicit spread contributes zero items: E.spread with E = ()
        // vanishes, so the pattern sees the single item 6.
        AssertEval(
            """
            E = ()
            F((xs...)) = xs.count
            F((E.spread, 6))
            """,
            1);
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_LiteralWrappedPairArgumentReportsWrittenSlotArity()
    {
        // `((1, 2))` is one written grouping level around the canonical item
        // (1, 2): the sequence-value pattern receives exactly ONE written slot,
        // so binding (x, y) reports arity 2 vs 1 — it neither mints an orphan
        // ((1, 2)) nor silently opens the single written item.
        AssertEvalFailsWithArityMismatch(
            """
            Wrap((x, y)) = x
            Wrap(((1, 2)))
            """,
            expected: 2,
            actual: 1);

        // Redundant deeper grouping canonicalizes away shallowly at each level
        // and still writes exactly one slot.
        AssertEvalFailsWithArityMismatch(
            """
            Wrap((x, y)) = x
            Wrap((((1, 2))))
            """,
            expected: 2,
            actual: 1);

        // A trailing fixed argument binds normally; the pattern slot itself
        // still reads one written item.
        AssertEvalFailsWithArityMismatch(
            """
            KeepFirst((x, y), z) = x
            KeepFirst(((1, 2)), 3)
            """,
            expected: 2,
            actual: 1);
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_PropertyStoredWrappedPairOpensCanonically()
    {
        // A = ((1, 2)) canonicalizes at construction to (1, 2); Wrap(A) opens
        // the stored canonical value, binds x = 1, and every observation —
        // display, count, .count, equality against both writable spellings,
        // and navigation — agrees on the scalar 1.
        AssertEval(
            """
            Wrap((x, y)) = x
            A = ((1, 2))
            R = Wrap(A)
            R, count(R), R.count, R == (1, 2), R == ((1, 2)), R:0
            """,
            1, 1, 1, 0, 0, 1);
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_SingleCapturePatternBindsWrappedPairAsCanonicalItem()
    {
        // IdSeq((x)) consumes the single written slot of ((1, 2)), and that
        // slot is the canonical (1, 2) — the shallow singleton-erasing combiner
        // never materializes a literal-unwritable orphan ((1, 2)) around it.
        // The structural comparison pins the exact shape.
        var result = EvalFull(
            """
            IdSeq((x)) = x
            IdSeq(((1, 2)))
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.True(
            Result.ValueComparer.Equals(ResultFromAtoms(1, 2), result.Value),
            $"Expected (1, 2) but got {result.Value}");

        // count, .count, equality against both writable literal spellings, and
        // navigation all agree with the canonical (1, 2).
        AssertEval(
            """
            IdSeq((x)) = x
            R = IdSeq(((1, 2)))
            R, count(R), R.count, R == (1, 2), R == ((1, 2)), R:0
            """,
            1, 2, 2, 2, 1, 1, 1);
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_TwoEmptySequenceSiblingItemsBindPositionally()
    {
        // The shallow combiner never drops empty-sequence siblings: ((), ())
        // writes two items, so (x, y) binds both empties positionally and x is
        // the real empty sequence value.
        AssertEval(
            """
            F((x, y)) = x == (), y == ()
            F(((), ()))
            """,
            1, 1);

        var result = EvalFull(
            """
            F((x, y)) = x
            F(((), ()))
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        Assert.True(
            Result.ValueComparer.Equals(new Result.SequenceValue([]), result.Value),
            $"Expected () but got {result.Value}");
    }

    [Fact]
    public void Eval_SequenceValueParameterBinding_WrappedPairReprosAgreeAcrossOptimizerModes()
    {
        // Post-#133 audit follow-up: with the orphan shape unconstructable, the
        // generic, loop-optimized, and sequence-pipeline paths observe
        // identical results through the sequence-value pattern binding repros.
        const string singleCaptureRepro =
            """
            IdSeq((x)) = x
            IdSeq(((1, 2)))
            """;
        AssertEvalResultLoopModes(singleCaptureRepro, ResultFromAtoms(1, 2));
        AssertEvalResultSequenceModes(singleCaptureRepro, ResultFromAtoms(1, 2));

        const string propertyStoredRepro =
            """
            Wrap((x, y)) = x
            A = ((1, 2))
            Wrap(A)
            """;
        AssertEvalResultLoopModes(propertyStoredRepro, Atom(1));
        AssertEvalResultSequenceModes(propertyStoredRepro, Atom(1));
    }

    [Fact]
    public void Eval_SequenceValueVariadicParameter_RequiresSequenceValueArgumentSlot()
    {
        var result = EvalFull(
            """
            F((xs...)) = xs.count
            F(1, 2, 3)
            """);

        Assert.True(result.IsError);
    }

    [Fact]
    public void Eval_NestedSequenceValueParameter_WrongShapeFailsWithInnerArityMismatch()
    {
        var result = EvalFull(
            """
            F(((x, y))) = x + y
            F((1, 2))
            """);

        Assert.True(result.IsError);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
        Assert.Equal(1, arity.Expected);
        Assert.Equal(2, arity.Actual);
    }

    [Fact]
    public void Eval_SequenceValueParameter_ArityMismatchUsesSequenceValueSignatureDisplay()
    {
        var result = EvalFull(
            """
            PairSum((x, y)) = x + y
            PairSum(1, 2)
            """);

        Assert.True(result.IsError);
        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("PairSum((x, y))", formatted, StringComparison.Ordinal);
        Assert.DoesNotContain("PairSum(x, y)", formatted, StringComparison.Ordinal);
        Assert.Equal("Callable `PairSum((x, y))` expects 1 argument, but was called with 2 arguments.", formatted);
    }

    [Fact]
    public void Eval_SequenceValueVariadicParameter_ArityMismatchUsesSequenceValueVariadicSignatureDisplay()
    {
        var result = EvalFull(
            """
            CountSequenceValue((values...)) = values.count
            CountSequenceValue(1, 2, 3)
            """);

        Assert.True(result.IsError);
        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("CountSequenceValue((values...))", formatted, StringComparison.Ordinal);
        Assert.DoesNotContain("CountSequenceValue(values...)", formatted, StringComparison.Ordinal);
        Assert.Equal("Callable `CountSequenceValue((values...))` expects 1 argument, but was called with 3 arguments.", formatted);
    }

    [Fact]
    public void Eval_PatternedUserCall_TopLevelCaptureCanBindAlgorithmChannel()
    {
        AssertEval(
            """
            Apply(f, (x)) = f(x)
            Double(n) = n * 2
            Apply(Double, (4))
            """,
            8);
    }

    [Fact]
    public void Eval_Count_PatternedUserCall_TopLevelCapturePreservesAlgorithmChannel()
    {
        AssertEval(
            """
            Apply(f, (x)) = f(x)
            Pair(n) = n, n + 1
            Apply(Pair, (4)).count
            """,
            2);
    }

    [Fact]
    public void Eval_PatternedUserCall_SequenceValueNestedCaptureDoesNotBindAlgorithmChannel()
    {
        var result = EvalFull(
            """
            ApplySequenceValue((f)) = f()
            Thunk = 42
            ApplySequenceValue((Thunk))
            """);

        Assert.True(result.IsError);
        var notAlgorithm = Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(result.Error));
        Assert.Equal("param(f)", notAlgorithm.Description);
    }

    [Fact]
    public void Eval_PatternedUserCall_SingletonSequenceValuePatternAcceptsScalarFallback()
    {
        AssertEval(
            """
            F((x)) = x
            F(5)
            """,
            5);
    }

    [Fact]
    public void Eval_PatternedUserCall_ExplicitZeroParamBlockExposesSlotsToSequenceValueBinding()
    {
        AssertEval(
            """
            PairSum((x, y)) = x + y
            PairSum({1, 2})
            """,
            3);
    }

    [Fact]
    public void Eval_PatternedCallback_SequenceValueVariadicCaptureKeepsProjectedCountedItems()
    {
        AssertEvalSequenceModes(
            """
            Signature((values...)) = values.count * 10 + values.sum
            map(((1, 2, 3), (4, 5)), Signature)
            """,
            36, 29);
    }

    [Fact]
    public void Eval_PatternedCallback_SequenceValueVariadicCountReceivesEachSequenceValueItem()
    {
        AssertEvalSequenceModes(
            """
            CountSequenceValue((values...)) = values.count
            map(((1, 2), (3, 4)), CountSequenceValue)
            """,
            2, 2);
    }

    [Fact]
    public void Eval_SequenceValueVariadicParameter_WithMixedTopLevelParameters()
    {
        AssertEval(
            """
            F((xs...), a, b) = xs.count, a, b
            F((1, 2, 3), 4, 5)
            """,
            3, 4, 5);
    }

    [Fact]
    public void Eval_SequenceValueParameter_AllowsSeparateVariadicsAtDifferentLevels()
    {
        AssertEval(
            """
            F((inner...), outer...) = inner.count, outer.count
            F((1, 2), 3, 4)
            """,
            2, 2);
    }

    [Fact]
    public void Eval_PlainFlatFixedUserCall_UsesExplicitParameters()
    {
        AssertEval(
            """
            Add(x, y) = x + y
            Add(2, 3)
            """,
            5);
    }

    [Fact]
    public void Eval_PlainFlatFixedUserCall_UsesImplicitParameters()
    {
        AssertEval(
            """
            Add = x + y
            Add(2, 3)
            """,
            5);
    }

    [Fact]
    public void Eval_Count_UserCallFlatFixedMirrorCountsCurrentOutputShape()
    {
        AssertEval(
            """
            Pair(x, y) = x, y
            Pair(2, 3).count
            """,
            2);
    }

    [Fact]
    public void Eval_PlainFlatFixedUserCall_PreservesAlgorithmValueDualBinding()
    {
        AssertEval(
            """
            Apply(f, x) = f(x)
            Double(n) = n * 2
            Apply(Double, 4)
            """,
            8);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_ArgumentExpressionsAreEvaluatedIndependently()
    {
        var result = EvalFull(
            """
            Use(a, b) = a + b
            Use(1, a)
            """);

        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var unresolved = Assert.IsType<EvalError.UnresolvedImplicitParams>(Innermost(result.Error));
        Assert.Equal(["a"], unresolved.ParamNames);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_MultiOutputPropertyReferenceDoesNotUnpack()
    {
        var arity = AssertEvalFailsWithArityMismatch(
            """
            Pair = 10, 20
            Add(x, y) = x + y
            Add(Pair)
            """,
            expected: 2,
            actual: 1);

        Assert.NotNull(arity.Signature);
        Assert.Equal("Add(x, y)", arity.Signature.DisplayText);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_ExplicitSpreadOpensMultiOutputPropertyReference()
    {
        AssertEval(
            """
            Pair = 10, 20
            Add(x, y) = x + y
            Add(Pair.spread)
            """,
            30);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_DotCallMultiOutputDoesNotBecomeArgumentSpreading()
    {
        // A multi-output dot-call expression (here `.atoms`) is still ONE
        // argument expression in a flat fixed call; only the named spread intrinsic opens it.
        AssertEvalFailsWithArityMismatch(
            """
            Pair = (10, 20)
            Add(x, y) = x + y
            Add(Pair.atoms)
            """,
            expected: 2,
            actual: 1);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_SeparateCommaArgumentsStillWork()
    {
        AssertEval(
            """
            Add(x, y) = x + y
            Add(10, 20)
            """,
            30);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_ExplicitIndexingStillWorks()
    {
        AssertEval(
            """
            Pair = 10, 20
            Add(x, y) = x + y
            Add(Pair:0, Pair:1)
            """,
            30);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_MixedPrefixPlusMultiOutputExpressionDoesNotUnpack()
    {
        AssertEvalFailsWithArityMismatch(
            """
            Tail = 2, 3
            Use(a, b, c) = a + b + c
            Use(1, Tail)
            """,
            expected: 3,
            actual: 2);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_ExplicitPropertyBodyBlockPreservesArgumentBoundary()
    {
        AssertEvalFailsWithArityMismatch(
            """
            Tail = { 2, 3 }
            Use(a, b, c) = a + b + c
            Use(1, Tail)
            """,
            expected: 3,
            actual: 2);
    }

    [Fact]
    public void Eval_DotCall_ReceiverBoundary_MultiOutputPropertyReceiverDoesNotUnpack()
    {
        AssertEvalFailsWithArityMismatch(
            """
            Pair = 10, 20
            Add(x, y) = x + y
            Pair.Add
            """,
            expected: 2,
            actual: 1);
    }

    [Fact]
    public void Eval_BlockBoundary_NestedBlockPreservesMultiOutputBoundary()
    {
        var result = EvalFull(
            """
            A = 1, { 2, 3 }
            A
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var outer = Assert.IsType<Result.SequenceValue>(result.Value);
        Assert.Equal(2, outer.Items.Count);
        AssertAtomValue(outer.Items[0], 1);
        AssertSequenceValueAtoms(outer.Items[1], 2, 3);
    }

    [Fact]
    public void Eval_BlockBoundary_ExplicitOuterPropertyBlockIsTransparent()
    {
        var result = EvalFull(
            """
            A = { 1, { 2, 3 } }
            A
            """);

        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        var outer = Assert.IsType<Result.SequenceValue>(result.Value);
        Assert.Equal(2, outer.Items.Count);
        AssertAtomValue(outer.Items[0], 1);
        AssertSequenceValueAtoms(outer.Items[1], 2, 3);
    }

    [Fact]
    public void Eval_BlockBoundary_SequenceSpreadExplicitlyFlattensNestedBlockOutput()
    {
        AssertEval(
            """
            A = spread(1), { 2, 3 }
            A
            """,
            1,
            2,
            3);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_SequenceValueResolvableAsAlgorithmPreservesBoundary()
    {
        AssertEvalFailsWithArityMismatch(
            """
            Pair = (2, 3)
            Use(x, y) = x + y
            Use(Pair)
            """,
            expected: 2,
            actual: 1);
    }

    [Fact]
    public void Eval_FlatFixedUserCall_AlgorithmOnlyFinalArgumentWithRemainingParamsKeepsArityPayload()
    {
        var result = EvalFull(
            """
            Inc(x) = x + 1
            Use(f, x) = f(x)
            Use(Inc)
            """);

        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(result.Error));
        Assert.Equal(1, arity.Expected);
        Assert.Equal(0, arity.Actual);
        Assert.NotNull(arity.Signature);
        Assert.Equal("Use(f, x)", arity.Signature.DisplayText);

        Assert.Contains(
            "Callable `Use(f, x)` expects 2 arguments, but was called with 0 arguments.",
            KatLangError.FromEvalError(result.Error).Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_FlatFixedUserCallInsideCallback_ShadowsOuterCountedCallbackParameter()
    {
        AssertEval(
            """
            Use(n) = n + 1
            Callback(n) = Use(n + 10)
            map((1, 2, 3), Callback)
            """,
            12, 13, 14);
    }

    [Fact]
    public void Eval_Count_UserCallFlatFixedRouteCountsCurrentOutputShape()
    {
        AssertEval(
            """
            F(x, y) = x, y
            F(1, 2).count
            """,
            2);
    }

    [Fact]
    public void Eval_Count_UserCallPatternedRouteCountsCurrentOutputShape()
    {
        AssertEval(
            """
            F((x, y)) = x, y
            F((1, 2)).count
            """,
            2);
    }

    [Fact]
    public void Eval_Count_UserCallFlatVariadicRouteCountsCurrentOutputShape()
    {
        // The grouped call collects one item, so the returned list is [(1, 2, 3)].
        AssertEval(
            """
            F(xs...) = xs
            F((1, 2, 3)).count
            """,
            1);
    }

    [Fact]
    public void Eval_PlainVariadicUserCall_CapturesAllItems()
    {
        // The spread supplies three argument slots; the variadic parameter collects [1, 2, 3].
        AssertEval(
            """
            CountValues(values...) = values.count
            CountValues((1, 2, 3).spread)
            """,
            3);
    }

    [Fact]
    public void Eval_PlainVariadicUserCall_WithSuffixBindsSuffixFromBack()
    {
        AssertEval(
            """
            Scale(items..., factor) = items.map{n * factor}
            Scale((1, 2, 3).spread, 10)
            """,
            10, 20, 30);
    }

    [Fact]
    public void Eval_PlainVariadicUserCall_WithAlgorithmSuffixPreservesAlgorithmChannel()
    {
        AssertEval(
            """
            Apply(values..., f) = f(values:0)
            Inc = a + 1
            Apply((10, 20).spread, Inc)
            """,
            11);
    }

    [Fact]
    public void Eval_PlainVariadicUserCall_WithPrefixAndSuffixCapturesMiddleItems()
    {
        AssertEval(
            """
            F(prefix, values..., suffix) = prefix, values.count, suffix
            F(1, (2, 3).spread, 4)
            """,
            1, 2, 4);
    }

    [Fact]
    public void Eval_PlainVariadicUserCall_WithSuffixReportsSameMinimumArityFailure()
    {
        var result = EvalFull(
            """
            Scale(items..., factor) = items.map{n * factor}
            Scale()
            """);

        Assert.True(result.IsError);
        var arity = Assert.IsType<EvalError.VariadicArityMismatch>(Innermost(result.Error));
        Assert.Equal(1, arity.ExpectedMinimum);
        Assert.Equal(0, arity.Actual);

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains(
            "Callable `Scale(items..., factor)` expects at least 1 item, but received 0 items.",
            formatted,
            StringComparison.Ordinal);
        Assert.NotNull(arity.Signature);
        Assert.Equal("Scale(items..., factor)", arity.Signature.DisplayText);
    }

    [Fact]
    public void Eval_PlainVariadicUserCall_WithPrefixAndSuffixReportsSignatureInMinimumArityFailure()
    {
        var result = EvalFull(
            """
            F(prefix, values..., suffix) = prefix.spread values.spread suffix
            F()
            """);

        Assert.True(result.IsError);
        var arity = Assert.IsType<EvalError.VariadicArityMismatch>(Innermost(result.Error));
        Assert.Equal(2, arity.ExpectedMinimum);
        Assert.Equal(0, arity.Actual);

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("F(prefix, values..., suffix)", formatted, StringComparison.Ordinal);
        Assert.Contains("expects at least 2 items", formatted, StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_Count_UserCallDeconstructionRouteReportsSignatureInMinimumArityFailure()
    {
        // F(xs..., last) is a comma deconstruction parameter list. F() supplies no
        // items, so the matcher cannot bind the single fixed parameter `last`: it
        // needs at least 1 item, reported against the callable signature.
        var result = EvalFull(
            """
            F(xs..., last) = xs.spread last
            F().count
            """);

        Assert.True(result.IsError);
        var arity = Assert.IsType<EvalError.VariadicArityMismatch>(Innermost(result.Error));
        Assert.Equal(1, arity.ExpectedMinimum);
        Assert.Equal(0, arity.Actual);

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Contains("F(xs..., last)", formatted, StringComparison.Ordinal);
        Assert.Contains(
            "Callable `F(xs..., last)` expects at least 1 item, but received 0 items.",
            formatted,
            StringComparison.Ordinal);
    }

    [Fact]
    public void Eval_Count_UserCallPatternedPlusTopLevelVariadicRoutesAsPatterned()
    {
        AssertEval(
            """
            F((inner...), outer...) = inner.spread outer
            F((1, 2), ((3, 4))).count
            """,
            3);
    }

    [Fact]
    public void Eval_SequenceValueParameter_HeadTailPatternBindsWithinOneSlot()
    {
        AssertEval(
            """
            F((head, tail...)) = head, tail.count
            F((1, 2, 3, 4))
            """,
            1, 3);
    }

    [Fact]
    public void Eval_SequenceValueParameter_FirstMiddleLastPatternBindsWithinOneSlot()
    {
        AssertEval(
            """
            F((first, middle..., last)) = first, middle.count, last
            F((1, 2, 3, 4, 5))
            """,
            1, 3, 5);
    }

    [Fact]
    public void Eval_SequenceValueParameter_VariadicWithSuffixInsideSequenceValueBindsWithinOneSlot()
    {
        AssertEval(
            """
            F((history..., pre2), pre1) = history.count, pre2, pre1
            F((1, 2, 3), 4)
            """,
            2, 3, 4);
    }

    [Fact]
    public void Eval_SequenceValueParameter_WithSuffixInsideSequenceValueRequiresSuffixValue()
    {
        var result = EvalFull(
            """
            F((history..., pre2), pre1) = history.count, pre2, pre1
            F((), 4)
            """);

        Assert.True(result.IsError);
    }

    [Fact]
    public void Eval_TopLevelVariadicParameter_GroupedArgumentIsOneCollectedItem()
    {
        // Contrast with the sequence-value pattern below: the top-level variadic parameter
        // collects the grouped argument as one list element ([(1, 2)], count 1),
        // while F((xs...), y) opens the same argument to count 2.
        AssertEval(
            """
            F(xs..., y) = xs.count, y
            F((1, 2), 3)
            """,
            1, 3);
    }

    [Fact]
    public void Eval_SequenceValueVariadicParameter_IsNotTopLevelVariadic()
    {
        AssertEval(
            """
            F((xs...), y) = xs.count, y
            F((1, 2), 3)
            """,
            2, 3);

        var result = EvalFull(
            """
            F((xs...), y) = xs.count, y
            F(1, 2, 3)
            """);

        Assert.True(result.IsError);
    }

    [Fact]
    public void Eval_NonVariadicSequenceValuePattern_DoesNotSpreadArbitraryGroup()
    {
        var result = EvalFull(
            """
            F((x)) = x
            F((1, 2, 3))
            """);

        Assert.True(result.IsError);
    }

    [Fact]
    public void Eval_FlatFixedLoopStep_ExplicitUserStep_PreservesGenericBindingBehavior()
    {
        AssertEvalLoopModes(
            """
            Step(a, b) = b, a + b, a + b < 10
            Step.while(1, 1)
            """,
            5, 8);
    }

    [Fact]
    public void Eval_PatternedLoopStep_WrongTopLevelShapeUsesLoopArityDiagnostic()
    {
        var (generic, optimized) = AssertEvalFailsInBothLoopModes(
            """
            Step((x, y)) = x + y
            Step.repeat(1, 1, 2)
            """);

        foreach (var error in new[] { generic, optimized })
        {
            var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
            Assert.Equal(2, arity.Expected);
            Assert.Equal(2, arity.Actual);

            var formatted = KatLangError.FromEvalError(error).Message;
            Assert.Contains("`repeat` step expects 2 state values", formatted, StringComparison.Ordinal);
            Assert.Contains("current loop state has 2 state values", formatted, StringComparison.Ordinal);
            Assert.DoesNotContain("Callable `Step((x, y))`", formatted, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void Eval_SequenceValueVariadicLoopStep_YellowstoneHistoryNeedsNoCleanup()
    {
        AssertEvalLoopModes(
            """
            GcdStep = b, ~a mod b, a mod b != 0
            Gcd = GcdStep.while(a, b):1

            FindNext(history..., pre1, pre2) = {
                IsYSCandidate(candidate) = not history.contains(candidate) and
                    Gcd(candidate, pre1) == 1 and
                    Gcd(candidate, pre2) != 1

                FindStep = candidate + 1, not IsYSCandidate(candidate)
                FindStep.while(1):0
            }

            YSStep((history...), pre2, pre1) = {
                Next = FindNext(history.spread, pre1, pre2)
                (history.spread, Next), pre1, Next
            }

            YSStep.repeat(27, (1, 2, 3), 2, 3):0
            """,
            1, 2, 3, 4, 9, 8, 15, 14, 5, 6,
            25, 12, 35, 16, 7, 10, 21, 20, 27, 22,
            39, 11, 13, 33, 26, 45, 28, 51, 32, 17);
    }

    [Fact]
    public void Eval_VariadicLoopStep_RepeatOneIterationCapturesStateItems()
    {
        AssertEvalResultLoopModes(
            """
            AppendNext(history...) = history.spread history.atoms.last + 1
            AppendNext.repeat(1, 1, 2, 4)
            """,
            ResultFromAtoms(1, 2, 4, 5));
    }

    [Fact]
    public void Eval_VariadicLoopStep_RepeatTwoIterationsKeepsExpandedState()
    {
        AssertEvalResultLoopModes(
            """
            AppendNext(history...) = history.spread history.atoms.last + 1
            AppendNext.repeat(2, 1, 2, 4)
            """,
            ResultFromAtoms(1, 2, 4, 5, 6));
    }

    [Fact]
    public void Eval_VariadicLoopStep_DirectCallBaselineMatchesRepeatSteps()
    {
        AssertEvalSequenceModes(
            """
            AppendNext(history...) = history.spread history.atoms.last + 1
            AppendNext((1, 2, 4)).spread AppendNext((1, 2, 4, 5))
            """,
            1, 2, 4, 5, 1, 2, 4, 5, 6);
    }

    [Fact]
    public void Eval_VariadicLoopStep_ImplicitOrdinaryRepeatStillFails()
    {
        var (generic, optimized) = AssertEvalFailsInBothLoopModes(
            """
            AppendNext = history.spread history.atoms.last + 1
            AppendNext.repeat(1, 1, 2, 4)
            """);

        foreach (var error in new[] { generic, optimized })
        {
            var formatted = KatLangError.FromEvalError(error).Message;
            Assert.Contains("`repeat` step expects 1 state value", formatted, StringComparison.Ordinal);
            Assert.Contains("current loop state has 3 state values", formatted, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void Eval_VariadicLoopStep_WithPrefix_CapturesRemainingStateItemsAsOneListSlot()
    {
        // The step returns the collected list unspread, so the collected list
        // [2, 3] stays one state slot beside the spread first item.
        AssertEvalResultLoopModes(
            """
            Step(first, rest...) = first.spread rest
            Step.repeat(1, 1, 2, 3)
            """,
            Result.FromItems([Atom(1), ListValue(Atom(2), Atom(3))]));
    }

    [Fact]
    public void Eval_VariadicLoopStep_WithSuffix_CapturesLeadingStateItems()
    {
        AssertEvalResultLoopModes(
            """
            Step(values..., last) = values.spread last
            Step.repeat(1, 1, 2, 3)
            """,
            ResultFromAtoms(1, 2, 3));
    }

    [Fact]
    public void Eval_VariadicLoopStep_WithPrefixAndSuffix_CapturesMiddleStateItems()
    {
        AssertEvalResultLoopModes(
            """
            Step(first, middle..., last) = first.spread middle.spread last
            Step.repeat(1, 1, 2, 3, 4)
            """,
            ResultFromAtoms(1, 2, 3, 4));
    }

    [Fact]
    public void Eval_VariadicLoopStep_ExtraMiddleStateSlots_RepeatTwoIterations()
    {
        // Four state slots bind first=0, middle=[5, 5] (the collected exact list),
        // last=10; the body re-spreads middle with `.spread` so the extra middle slots
        // survive across iterations. Mirrors the Lean guard
        // variadicLoopStepExtraMiddleRepeatsTwice.
        AssertEvalLoopModes(
            """
            Step(first, middle..., last) = first + 1, middle.spread, last + 1
            Step.repeat(2, 0, 5, 5, 10)
            """,
            2, 5, 5, 12);
    }

    [Fact]
    public void Eval_VariadicLoopStep_WithPrefixMiddleSuffix_PreservesDeclarationOrderBindings()
    {
        AssertEvalLoopModes(
            """
            Step(first, middle..., last) = first, middle.count, last
            Step.repeat(1, 10, 20, 30, 40)
            """,
            10, 2, 40);
    }

    [Fact]
    public void Eval_VariadicLoopStep_ReportsMinimumStateArityWhenFixedParametersCannotBind()
    {
        // The minimum for Step(first, rest..., last) is the FIXED parameter
        // count (2), so a single state slot cannot bind first + last. The variadic parameter
        // itself may collect zero slots (see Eval_VariadicLoopStep_TwoStateSlots_*).
        var (generic, optimized) = AssertEvalFailsInBothLoopModes(
            """
            Step(first, rest..., last) = first.spread rest.spread last
            Step.repeat(1, 1)
            """);

        foreach (var error in new[] { generic, optimized })
        {
            var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
            Assert.Equal(2, arity.Expected);
            Assert.Equal(1, arity.Actual);

            var formatted = KatLangError.FromEvalError(error).Message;
            Assert.Contains("`repeat` variadic step expects at least 2 state values", formatted, StringComparison.Ordinal);
            Assert.Contains("for fixed parameter(s) 'first' and 'last'", formatted, StringComparison.Ordinal);
            Assert.Contains("current loop state has 1 state value", formatted, StringComparison.Ordinal);
            Assert.DoesNotContain("Callable `Step(first, rest..., last)`", formatted, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void Eval_VariadicLoopStep_TwoStateSlots_BindEmptyCollectedList()
    {
        // The empty loop-state segment follows the SAME rule as every other collecting
        // receiver: Step(first, middle..., last) with exactly two state slots
        // binds first/last from the ends and middle collects ZERO slots as the
        // exact empty list `[]` (count 0). Pins the parity boundary: 1 slot
        // fails (Eval_VariadicLoopStep_ReportsMinimumStateArity*), 2 bind an
        // empty segment, 3 a singleton, 4+ a multi-item segment. Mirrors the Lean
        // guard variadicLoopStepEmptyMiddleBindsEmptyList.
        AssertEvalLoopModes(
            """
            Step(first, middle..., last) = first, (middle == []), middle.count, last
            Step.repeat(1, 10, 20)
            """,
            10, 1, 0, 20);
    }

    [Fact]
    public void Eval_OptimizedLoop_MultiEmittingStateExpression_MatchesGenericPath()
    {
        // A state expression whose counted supply emits more than one value
        // (an index projection here) grows the generic state-slot vector; the
        // optimizer must observe the identical value shape (it finishes the
        // current iteration once, then hands its assembled state slots to the
        // generic evaluator when an expression does not emit exactly one value).
        AssertEvalLoopModes(
            """
            S = (1, 2), (3, 4)
            repeat({S:0, a + b}, 1, 0, 0)
            """,
            1, 2, 0);

        AssertEvalResultLoopModes(
            """
            S = (1, 2), (3, 4)
            repeat({S:0, a + b}, 1, 0, 0)
            """,
            ResultFromAtoms(1, 2, 0));

        // The first iteration stays on the scalar fast path; only the second
        // projection grows from one emitted item to two. This pins handoff
        // from the already-advanced state rather than from the initial state.
        AssertEvalResultLoopModes(
            """
            S = 1, (2, 3)
            repeat({a + 1, S:(a + b - b)}, 2, 0, 9)
            """,
            ResultFromAtoms(2, 2, 3));
    }

    [Fact]
    public void Eval_OptimizedLoop_MultiEmittingContinuation_MatchesGenericPath()
    {
        // A while continuation expression emitting more than one value changes
        // which generic slot is the continuation flag; the optimizer must
        // defer to generic semantics (state (1, 0) means the last item, 0,
        // stops the loop and the pre-iteration state is returned).
        AssertEvalLoopModes(
            """
            S = (1, 0), (2, 2)
            while({a + 1, S:0}, 9)
            """,
            9);
    }

    [Fact]
    public void Eval_OptimizedLoop_ZeroEmittingStateAndContinuation_MatchGenericPath()
    {
        // A spread empty value contributes no generic state slot. The
        // optimizer must complete that iteration once and hand off the
        // shrunken slot vector without replaying it.
        AssertEvalResultLoopModes(
            "repeat({if(a == 0, (), ()).spread, b}, 1, 0, 9)",
            ResultFromAtoms(9));

        // A spread-empty continuation leaves the preceding numeric output as
        // the generic continuation slot; zero stops and returns the old state.
        AssertEvalResultLoopModes(
            "while({a + 1, if(a == -1, (), ()).spread}, -1)",
            ResultFromAtoms(-1));

        // Non-spread `()` is a visible output slot, so it is an invalid
        // continuation value in both modes rather than disappearing.
        var (generic, optimized) = AssertEvalFailsInBothLoopModes("while({a + 1, ()}, 0)");
        Assert.IsType<EvalError.BadArity>(Innermost(generic));
        Assert.IsType<EvalError.BadArity>(Innermost(optimized));
        Assert.Equal(
            KatLangError.FromEvalError(generic).Message,
            KatLangError.FromEvalError(optimized).Message);
    }

    [Fact]
    public void Eval_OptimizedLoop_MultiEmittingStateExpression_ErrorMatchesGenericPath()
    {
        // Error identity parity: a spread state expression makes the next
        // state three slots against a two-parameter step; both modes must
        // report the same loop-state arity mismatch at the same program point.
        var (generic, optimized) = AssertEvalFailsInBothLoopModes(
            "repeat({(a + 1, a + 2).spread, b}, 2, 0, 9)");

        var genericArity = Assert.IsType<EvalError.ArityMismatch>(Innermost(generic));
        var optimizedArity = Assert.IsType<EvalError.ArityMismatch>(Innermost(optimized));
        Assert.Equal(genericArity.Expected, optimizedArity.Expected);
        Assert.Equal(genericArity.Actual, optimizedArity.Actual);
        Assert.Equal(
            KatLangError.FromEvalError(generic).Message,
            KatLangError.FromEvalError(optimized).Message);

        // One scalar iteration succeeds before the second iteration grows the
        // state from two slots to three; the next bind then fails identically.
        var (laterGeneric, laterOptimized) = AssertEvalFailsInBothLoopModes(
            """
            S = 1, (2, 3)
            repeat({a + 1, S:(a + b - b)}, 3, 0, 9)
            """);
        var laterGenericArity = Assert.IsType<EvalError.ArityMismatch>(Innermost(laterGeneric));
        var laterOptimizedArity = Assert.IsType<EvalError.ArityMismatch>(Innermost(laterOptimized));
        Assert.Equal((2, 3), (laterGenericArity.Expected, laterGenericArity.Actual));
        Assert.Equal(
            KatLangError.FromEvalError(laterGeneric).Message,
            KatLangError.FromEvalError(laterOptimized).Message);
    }

    [Fact]
    public void Eval_OptimizedLoop_ListAndSequenceValuedState_MatchesGenericPath()
    {
        // Structural state slots (exact lists, growing via spread) are bound
        // and rebuilt identically in both loop modes.
        AssertEvalResultLoopModes(
            "repeat({[a.spread, 1]}, 3, [])",
            ListValue(ResultFromAtoms(1), ResultFromAtoms(1), ResultFromAtoms(1)));

        AssertEvalResultLoopModes(
            """
            Step(acc, x...) = acc + x.count, 0
            repeat(Step, 1, 5)
            """,
            SequenceValue(ResultFromAtoms(5), ResultFromAtoms(0)));
    }

    [Fact]
    public void Eval_PatternedAndFlatLoopSteps_ShareTheEmptySegmentRule()
    {
        // The flat variadic loop path and the patterned loop path both allow a
        // variadic parameter that collects zero state slots (the exact empty list `[]`) —
        // the same rule as every other collecting binding.
        AssertEvalResultLoopModes(
            """
            Step(a, rest..., a) = rest, 0
            repeat(Step, 1, 7, 7)
            """,
            SequenceValue(ListValue(), ResultFromAtoms(0)));
    }

    [Fact]
    public void Eval_SingleVariadicLoopStep_MayShrinkStateToZeroSlots()
    {
        // Deliberate consequence of the uniform empty-segment rule: a single-variadic
        // step has zero fixed parameters, so the state vector may shrink all
        // the way to zero slots, and the loop result is then the visible
        // empty sequence value `()`.
        AssertEvalResultLoopModes(
            """
            Step(x...) = x.skip(1).spread
            repeat(Step, 3, 7, 8)
            """,
            SequenceValue());

        AssertEvalResultLoopModes(
            """
            Step(x...) = x.skip(1).spread
            repeat(Step, 1, 7, 8)
            """,
            ResultFromAtoms(8));
    }

    [Fact]
    public void Eval_VariadicLoopStep_WhileUsesExpandedState()
    {
        AssertEvalResultLoopModes(
            """
            AppendWhile(history...) = (history.spread, history.atoms.last + 1), if(history.atoms.last + 1 < 6, 1, 0)
            AppendWhile.while(1, 2, 4)
            """,
            ResultFromAtoms(1, 2, 4, 5));
    }

    [Fact]
    public void Eval_LoopInitial_ManyExplicitArgsCreateManySlots()
    {
        AssertEvalLoopModes(
            """
            Step = a + 1, b + a
            Step.repeat(3, 0, 0)
            """,
            3, 3);
    }

    [Fact]
    public void Eval_LoopInitial_SequenceValuePropertyArgIsOneSlot()
    {
        AssertEvalLoopModes(
            """
            Pair = (1, 2)
            Step = pair:0 + pair:1
            Step.repeat(1, Pair)
            """,
            3);
    }

    [Fact]
    public void Eval_LoopInitial_SequenceValueArgDoesNotSatisfyTwoOrdinaryParams()
    {
        var (generic, optimized) = AssertEvalFailsInBothLoopModes(
            """
            Pair = (1, 2)
            Step = a + b
            Step.repeat(1, Pair)
            """);

        foreach (var error in new[] { generic, optimized })
        {
            var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
            Assert.Equal(2, arity.Expected);
            Assert.Equal(1, arity.Actual);
        }
    }

    [Fact]
    public void Eval_LoopInitial_ExplicitSelectionsSplitSequenceValueArg()
    {
        AssertEvalLoopModes(
            """
            Pair = (1, 2)
            Step = a + b
            Step.repeat(1, Pair:0, Pair:1)
            """,
            3);
    }

    [Fact]
    public void Eval_LoopInitial_SequenceValueHistorySlotCanBePreservedAcrossRepeat()
    {
        AssertEvalLoopModes(
            """
            History = (1, 2, 4)
            Step = (history, history.atoms.last + 1)
            Step.repeat(2, History)
            """,
            1, 2, 4, 5, 6);
    }

    [Fact]
    public void Eval_LoopInitial_SequenceValueStepOutputBecomesOneStateSlot()
        => AssertEvalResultLoopModes(
            """
            History = (1, 2, 4)
            Step = (history.spread, history.atoms.last + 1)
            Step.repeat(2, History)
            """,
            ResultFromAtoms(1, 2, 4, 5, 6));

    [Fact]
    public void Eval_LoopStep_ParenthesizedSequenceSpreadPreservesSequenceValueOperandBoundary()
    {
        // `FindNext(history.spread)` forwards the state sequence's items explicitly;
        // a bare `FindNext(history)` would pass the whole sequence as one
        // collected element.
        var definitions = """
            FindNext(history...) = {
                Tail = history:(history.atoms.count-1)
                IsCandidate(candidate) = not history.contains(candidate)
                FindStep = x + 1, not IsCandidate(x)
                FindStep.while(Tail+1):0
            }
            TestStep = (history.spread FindNext(history.spread))
            LIST = 1, 2, 4
            """;

        AssertEvalResultLoopModes(
            definitions + "\nTestStep.repeat(1, LIST)",
            ResultFromAtoms(1, 2, 4, 5));
    }

    [Fact]
    public void Eval_LoopStep_SequenceValueSequenceSpreadCarriesOneSequenceStateSlot()
        => AssertEvalResultLoopModes(
            """
            FindNext(history...) = {
                Tail = history:(history.atoms.count-1)
                IsCandidate(candidate) = not history.contains(candidate)
                FindStep = x + 1, not IsCandidate(x)
                FindStep.while(Tail+1):0
            }
            TestStep = (history.spread, FindNext(history.spread))
            LIST = 1, 2, 4
            TestStep.repeat(2, LIST)
            """,
            ResultFromAtoms(1, 2, 4, 5, 6));

    [Fact]
    public void Eval_LoopStep_ExplicitVariadicStillAcceptsExpandedState()
    {
        AssertEvalResultLoopModes(
            """
            FindNext(history...) = {
                Tail = history:(history.atoms.count-1)
                IsCandidate(candidate) = not history.contains(candidate)
                FindStep = x + 1, not IsCandidate(x)
                FindStep.while(Tail+1):0
            }
            TestStep(history...) = history.spread FindNext(history.spread)
            TestStep.repeat(2, 1, 2, 4)
            """,
            ResultFromAtoms(1, 2, 4, 5, 6));
    }

    [Fact]
    public void Eval_LoopStep_SequenceValueCommaHistorySlotUsesExplicitSpreadAcrossRepeat()
    {
        const string source = """
            Step((history...), previous) = (history.spread, previous + 1), previous + 1
            Step.repeat(2, (1, 2), 2):0
            """;

        AssertEvalResultLoopModes(source, ResultFromAtoms(1, 2, 3, 4));

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");
        AssertSequenceValueAtoms(result.Value, 1, 2, 3, 4);
    }

    [Fact]
    public void Eval_LoopInitial_MultiOutputPropertyArgIsOneSlot()
    {
        AssertEvalLoopModes(
            """
            Pair = 1, 2
            Step = pair:0 + pair:1
            Step.repeat(1, Pair)
            """,
            3);
    }

    [Fact]
    public void Eval_LoopInitial_ExplicitSelectionsSplitMultiOutputProperty()
    {
        AssertEvalLoopModes(
            """
            Pair = 1, 2
            Step = a + b
            Step.repeat(1, Pair:0, Pair:1)
            """,
            3);
    }

    [Fact]
    public void VariadicUserProperty_MatchesBuiltinSumAndCount()
    {
        // The stream-supplying call forms (spread argument, spread receiver)
        // feed the variadic parameter the items the builtins see.
        AssertEvalSequenceModes(
            """
            Arg = 1, 2, 3
            Mean(values...) = values.sum / values.count
            Mean(Arg.spread), (Arg.spread).Mean
            """,
            2, 2);
    }

    [Fact]
    public void VariadicUserProperty_MatchesDirectBuiltinExpression()
    {
        AssertEvalSequenceModes(
            """
            Arg = 1, 2, 3
            Mean(values...) = values.sum / values.count
            Direct = Arg.sum / Arg.count
            Mean(Arg.spread), Direct
            """,
            2, 2);
    }

    [Fact]
    public void VariadicUserProperty_PreservesNestedSequenceValuesLikeSequenceBuiltins()
    {
        AssertEvalSequenceModes(
            """
            Arg = (1, 2), (3, 4)
            CountViaVariadic(values...) = values.count
            CountViaVariadic(Arg.spread), (Arg.spread).CountViaVariadic, Arg.count
            """,
            2, 2, 2);
    }

    [Fact]
    public void VariadicUserProperty_DistinguishesAtomsRecursiveFlattening()
    {
        AssertEvalSequenceModes(
            """
            Arg = (1, 2), (3, 4)
            CountViaVariadic(values...) = values.count
            CountAtoms(values...) = atoms(values).count
            CountViaVariadic(Arg.spread), CountAtoms(Arg.spread)
            """,
            2, 4);
    }

    [Fact]
    public void VariadicUserProperty_MapWrapperMatchesBuiltinMap()
    {
        AssertEvalSequenceModes(
            """
            Arg = 1, 2, 3
            Scale(values..., factor) = values.map{n * factor}
            Output = (Arg.spread).Scale(10), Arg.map{n * 10}
            """,
            10, 20, 30, 10, 20, 30);
    }

    [Fact]
    public void VariadicUserProperty_FilterWrapperMatchesBuiltinFilter()
    {
        AssertEvalSequenceModes(
            """
            Arg = 1, 2, 3, 4, 5
            KeepBetween(values..., minValue, maxValue) = values.filter{n >= minValue and n <= maxValue}
            Output = (Arg.spread).KeepBetween(2, 4), Arg.filter{n >= 2 and n <= 4}
            """,
            2, 3, 4, 2, 3, 4);
    }

    [Fact]
    public void VariadicUserProperty_TakeWrapperMatchesBuiltinTake()
    {
        AssertEvalSequenceModes(
            """
            Arg = 1, 2, 3, 4
            TakeFirst(values..., itemCount) = values.take(itemCount)
            Output = (Arg.spread).TakeFirst(2), Arg.take(2)
            """,
            1, 2, 1, 2);
    }

    [Fact]
    public void VariadicUserProperty_SkipWrapperMatchesBuiltinSkip()
    {
        AssertEvalSequenceModes(
            """
            Arg = 1, 2, 3, 4
            SkipFirst(values..., itemCount) = values.skip(itemCount)
            Output = (Arg.spread).SkipFirst(2), Arg.skip(2)
            """,
            3, 4, 3, 4);
    }

    [Fact]
    public void OrdinaryParameter_RemainsStructuralAfterVariadicSupport()
    {
        // The fixed parameter binds the receiver value untouched (count 3 via
        // the collection view), while the variadic parameter collects the receiver
        // as one list element (count 1).
        AssertEvalSequenceModes(
            """
            Arg = 1, 2, 3
            Ordinary(list) = list.count
            Variadic(list...) = list.count
            Arg.Ordinary, Arg.Variadic
            """,
            3, 1);
    }

    [Fact]
    public void SequenceBuiltins_PreserveNestedSequenceValuesAndDoNotBehaveLikeAtoms()
    {
        AssertEvalSequenceModes(
            """
            Arg = (1, 2), (3, 4)
            Arg.count, atoms(Arg).count
            """,
            2, 4);
    }

    [Fact]
    public void Eval_GracePrefix_ReordersParams()
    {
        // Without grace: F(a,b) where a=first-appearance â†’ a=2, b=3
        // F = b + ~a * 10 â†’ params [a, b] (a moved left)
        // F(2, 3) â†’ a=2, b=3 â†’ 3 + 2*10 = 23
        var source = """
            F = b + ~a * 10
            F(2, 3)
            """;
        AssertEval(source, 23);
    }

    [Fact]
    public void Eval_GracePostfix_ReordersParams()
    {
        // F = a~ + b â†’ first-appearance [a, b], a~ moves right â†’ params [b, a]
        // F(2, 3) â†’ b=2, a=3 â†’ 3 + 2 = 5
        var source = """
            F = a~ + b
            F(2, 3)
            """;
        AssertEval(source, 5);
    }

    [Fact]
    public void Eval_NoGrace_Baseline()
    {
        // Without grace: F(a,b), a=first â†’ a=2, b=3 â†’ 2 + 3*10 = 32
        var source = """
            F = a + b * 10
            F(2, 3)
            """;
        AssertEval(source, 32);
    }

    [Fact]
    public void Eval_GraceWithImplicitArgs()
    {
        // F = b + ~a â†’ params [a, b]
        // G uses F implicitly: G = F + 1
        // G(2, 3) â†’ F(2,3) + 1 â†’ (3 + 2) + 1 = 6
        var source = """
            F = b + ~a
            G = F + 1
            G(2, 3)
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_GraceDoublePrefixThreeParams()
    {
        // F = c + b + ~~a â†’ first-appearance [c, b, a], ~~a moves a 2 left â†’ [a, c, b]
        // F(1, 2, 3) â†’ a=1, c=2, b=3 â†’ 2 + 3 + 1 = 6
        var source = """
            F = c + b + ~~a
            F(1, 2, 3)
            """;
        AssertEval(source, 6);
    }

    // â”€â”€ Open-specific tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Open_MultipleOpens()
    {
        var source = """
            A = (public X = 1)
            B = (public Y = 2)
            open A, B
            X + Y
            """;
        AssertEvalAllPublic(source, 3);
    }

    [Fact]
    public void Eval_Open_UnbracketedCommaList_ResolvesFromSecondLib()
    {
        // open Lib2, Lib3 → two separate opens; Val3 resolves from Lib3
        var source = """
            Lib2 = (public Val2 = 20)
            Lib3 = (public Val3 = 30)
            open Lib2, Lib3
            Val3
            """;
        AssertEvalAllPublic(source, 30);
    }

    [Fact]
    public void Eval_Open_AmbiguityFails()
    {
        // Both A and B provide X â†’ ambiguity â†’ should fail
        var source = """
            A = (public X = 1)
            B = (public X = 2)
            open A, B
            X
            """;
        AssertEvalAllPublicFails(source);
    }

    [Fact]
    public void Eval_Open_LocalOverridesOpen()
    {
        // Local property takes priority over imported name
        var source = """
            Lib = (public X = 99)
            open Lib
            X = 1
            X
            """;
        AssertEvalAllPublic(source, 1);
    }

    [Fact]
    public void Eval_Open_EllipsisSpellingDoesNotMergeLibraries()
    {
        // Libraries are opened through one comma-separated open declaration
        // (semicolon is not an open-target separator); an `...`-joined
        // spelling is a parse error, not a merged open.
        var source = """
            A = (public X = 1)
            B = (public Y = 2)
            open A...B
            X + Y
            """;
        var parseResult = Parser.Parse(source);
        Assert.True(parseResult.HasErrors);
        Assert.Contains(
            parseResult.Diagnostics,
            d => d.Message.Contains("`...` is not valid in open targets"));

        AssertEvalAllPublicFails(source);
    }

    [Fact]
    public void Eval_Open_CommaList_OpensBothLibraries()
        // Comma is the open-target separator: one open declaration with a
        // comma-separated list opens both libraries, so X + Y = 3.
        => AssertEvalAllPublic("A = (public X = 1)\nB = (public Y = 2)\nopen A, B\nX + Y", 3);

    [Theory]
    [InlineData("A = (public X = 1)\nB = (public Y = 2)\nC = (public Z = 4)\nopen A, B, C\nX + Y + Z")]
    [InlineData("A = (public X = 1)\nB = (public Y = 2)\nC = (public Z = 4)\nopen A,\nB,\nC\nX + Y + Z")]
    [InlineData("A = (public X = 1)\nB = (public Y = 2)\nC = (public Z = 4)\nopen A\n, B\n, C\nX + Y + Z")]
    public void Eval_Open_CommaContinuationAcrossLines_OpensAllTargets(string source)
        // Trailing- and leading-comma continuation are equivalent to the
        // single-line list: all three libraries open, so X + Y + Z = 7.
        => AssertEvalAllPublic(source, 7);

    [Theory]
    [InlineData("Lib = (public Sub = (public V = 7))\nopen Lib.Sub\nV")]
    [InlineData("Lib = (public Sub = (public V = 7))\nopen Lib\n.Sub\nV")]
    public void Eval_Open_DottedTargetWithLeadingDotContinuation_OpensSameTarget(string source)
        // A leading '.' continues the dotted open target across the line,
        // so both spellings open Lib.Sub and V resolves to 7.
        => AssertEvalAllPublic(source, 7);

    [Theory]
    [InlineData("A = (public X = 1)\nB = (public Y = 2)\nopen A ; B\nX + Y")]
    [InlineData("A = (public X = 1)\nB = (public Y = 2)\nopen A B\nX + Y")]
    public void Eval_Open_NonCommaSeparator_IsParseErrorNotTwoOpens(string source)
    {
        // ';' and same-line adjacency are not open-target separators: the
        // parse reports the separator mistake, and B is never opened.
        var parseResult = Parser.Parse(source);
        Assert.True(parseResult.HasErrors);

        AssertEvalAllPublicFails(source);
    }

    [Fact]
    public void Eval_Open_NotTransitive()
    {
        // Lib1's opens should not be visible to the opener
        var source = """
            Inner = (public Z = 42)
            Lib1 = (
                open Inner
                W = Z
            )
            open Lib1
            Z
            """;
        // Z is not transitively visible â†’ fail
        AssertEvalAllPublicFails(source);
    }

    [Fact]
    public void Eval_Open_SelfNameInOpenExpression_Fails()
    {
        // "self" is no longer a keyword — it's now just an identifier.
        // Using it in open position fails because there's no algorithm named "self".
        var source = """
            HiddenLib = (X = 42)
            open self.HiddenLib
            X
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_Open_ChildResolvesFromParentOpens()
    {
        // Lean test: parent-open visibility.
        // Parent opens Lib; Child does NOT open it.
        // Child resolves "X" via parent chain â†’ parent opens â†’ Lib.
        var source = """
            Lib = (public X = 42)
            Main = (
                open Lib
                Child = (X)
                Child
            )
            Main
            """;
        AssertEvalAllPublic(source, 42);
    }

    [Fact]
    public void Eval_Open_StructuralOwnershipTakesPrecedenceOverOpens()
    {
        // Ownership-first model: structural properties in the parent chain
        // always take precedence over opened namespaces.
        //
        // Wrapper resolves "Val" via:
        //   1. Local props â†’ none
        //   2. Parent structural: Main â†’ no Val; Root â†’ Val = 0 found!
        //   3. Opens never consulted (structural wins)
        //
        // Even though Main opens Lib which has Val = 42, the root's
        // structural Val = 0 takes precedence.
        var source = """
            Val = 0
            Main = (
                Lib = (public Val = 42)
                open Lib
                Wrapper = (
                    Val
                )
                Wrapper
            )
            Main
            """;
        AssertEvalAllPublic(source, 0);
    }

    // â”€â”€ Property visibility tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Visibility_OpenCanSeePublicButNotPrivate()
    {
        // Library with one public and one private property.
        // Open should see the public one but not the private one.
        // Lean: opens expose public members only (lookupOpens via lookupPublicProp).
        var source = """
            public Lib = (public X = 42
            Y = 99)
            open Lib
            X
            """;
        AssertEval(source, 42);

        // Now try Y (private) â€” should fail
        var sourceY = """
            public Lib = (public X = 42
            Y = 99)
            open Lib
            Y
            """;
        AssertEvalFails(sourceY);
    }

    [Fact]
    public void Eval_Visibility_NotPublicPropertyOnPrivateIntermediate()
    {
        // open Lib.Sub where Sub exists but is private → NotPublicProperty.
        // Lib doesn't need public (it's in the ownership chain), but Sub must
        // be public because it's an intermediate on the open path.
        var source = """
            Lib = (Sub = (public X = 42
            X))
            open Lib.Sub
            X
            """;
        AssertEvalFails(source);
    }

    // â”€â”€ Open normalization acceptance tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Open_PropPathInOpen_Works()
    {
        // Acceptance A: Lib.Sub in open â†’ prop-path resolves correctly
        var source = """
            public Lib = (public Sub = (public X = 1))
            open Lib.Sub
            X
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Open_DotCallWithArgs_Fails()
    {
        // Acceptance B: Lib.Sub() â†’ call-like dot syntax in open â†’ parse error
        var source = """
            public Lib = (public Sub = (public X = 1))
            open Lib.Sub()
            X
            """;
        // Parser emits diagnostic for invalid open form
        var result = KatLang.Parser.Parse(source);
        Assert.True(result.HasErrors);
    }

    [Fact]
    public void Eval_Open_MultipleOpensCommaForm_Works()
    {
        // Acceptance C: multiple opens with comma-separated form
        var source = """
            public Lib2 = (public Val = 2)
            public Lib3 = (public Val2 = 3)
            open Lib2, Lib3
            Val2
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Open_PrivateIntermediate_Fails()
    {
        // Acceptance D: private intermediate on open path
        var source = """
            Lib = (Sub = (public X = 1))
            open Lib.Sub
            X
            """;
        AssertEvalFails(source);
    }

    [Fact]
    public void Eval_Visibility_OwnershipFirstShadowingBeatsOpens()
    {
        // Structural property in parent chain beats opened property,
        // even when the structural property is private.
        // Opens enforce public-only, but structural always wins first.
        var source = """
            Val = 0
            Main = (
                Lib = (Val = 42)
                open Lib
                Wrapper = (
                    Val
                )
                Wrapper
            )
            Main
            """;
        // Make Lib and its Val public so the open path works
        AssertEvalAllPublic(source, 0);
    }

    [Fact]
    public void Eval_Visibility_AmbiguousOpenWithTwoPublicProviders()
    {
        // Two opens provide the same public name â†’ AmbiguousOpen error
        var source = """
            A = (public X = 1)
            B = (public X = 2)
            open A, B
            X
            """;
        AssertEvalAllPublicFails(source);

        // Verify it's specifically an AmbiguousOpen error
        var ast = Parser.Parse(source).Root;
        var publicAst = MakeAllPublic(ast);
        var result = Evaluator.RunFlat(new Expr.Block(publicAst));
        Assert.True(result.IsError);
        // Unwrap WithContext if present
        var err = result.Error;
        while (err is EvalError.WithContext wc)
            err = wc.Inner;
        Assert.IsType<EvalError.AmbiguousOpen>(err);
    }

    [Fact]
    public void Eval_Visibility_AllParsedPropertiesPrivateByDefault()
    {
        // Parsed properties are private by default.
        // Opening a user-defined library with default visibility should
        // not expose any properties through opens.
        var source = """
            Lib = (X = 42)
            open Lib
            X
            """;
        // Without MakeAllPublic, X should NOT be visible through opens
        AssertEvalFails(source);
    }

    // â”€â”€ Public keyword syntax tests â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_PublicKeyword_OpenCanSeePublicProperty()
    {
        var source = """
            Lib = (public Val = 42)
            open Lib
            Val
            """;
        // Lib itself must also be public for open resolution to find it
        AssertEvalAllPublic(source, 42);
    }

    [Fact]
    public void Eval_PublicKeyword_EndToEnd()
    {
        // Full end-to-end: public keyword makes property visible through opens.
        // Lean: opens expose public members only (lookupOpens via lookupPublicProp).
        var source = """
            public Lib = (public Val = 42)
            open Lib
            Val
            """;
        AssertEval(source, 42);
    }

    [Fact]
    public void Eval_PublicKeyword_PrivateNotVisible()
    {
        // Library with one public and one private property
        // Lean: opens expose public members only (lookupOpens via lookupPublicProp).
        var source = """
            public Lib = (public X = 1
            Y = 2)
            open Lib
            X
            """;
        AssertEval(source, 1);

        // Y is private, should fail
        var sourceY = """
            public Lib = (public X = 1
            Y = 2)
            open Lib
            Y
            """;
        AssertEvalFails(sourceY);
    }

    [Fact]
    public void Eval_PublicKeyword_InBlock()
    {
        // Lean: opens expose public members only (lookupOpens via lookupPublicProp).
        var source = """
            public Lib = {public Val = 42}
            open Lib
            Val
            """;
        AssertEval(source, 42);
    }

    // â”€â”€ Opens-aware parameter detection (Lean: shouldTreatAsImplicitParam) â”€â”€

    [Fact]
    public void Eval_Open_LowercasePublicProperty_ResolvesViaOpen()
    {
        // Lowercase public property visible through opens should NOT become a param.
        // Lean: shouldTreatAsImplicitParam uses lookupLexical which includes opens.
        // Lean: opens expose public members only (lookupOpens via lookupPublicProp).
        var source = """
            public Lib = (public val = 42)
            open Lib
            val
            """;
        AssertEval(source, 42);
    }

    [Fact]
    public void Eval_Open_LowercasePublicFunction_CanBeCalled()
    {
        // Opened lowercase function name: should stay as Resolve, not become param.
        // Lean: opens expose public members only (lookupOpens via lookupPublicProp).
        var source = """
            public Lib = (public inc = x + 1)
            open Lib
            inc(5)
            """;
        AssertEval(source, 6);
    }

    [Fact]
    public void Eval_Open_PropertyBodySeesOpenedNames()
    {
        // "val" in F's body is visible through parent's opens (not a param of F).
        // Lean: opens expose public members only (lookupOpens via lookupPublicProp).
        var source = """
            public Lib = (public val = 42)
            open Lib
            F = val + 1
            F
            """;
        AssertEval(source, 43);
    }

    // -- open visibility: container does not need to be public ----------------
    // Rule: open never requires the opened algorithm itself to be public.
    //       It only requires the algorithm to be available in the current context.
    //       open imports only public members of that algorithm.

    [Fact]
    public void Eval_Open_LocalNonPublicAlgorithm_CanBeOpened()
    {
        // open never requires the opened algorithm itself to be public.
        // It only requires the algorithm to be available in the current context.
        // open imports only public members of that algorithm.
        var source = """
            open Lib
            Lib = {
                public Pi = 3
            }
            Pi
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Open_LocalPublicAlgorithm_CanStillBeOpened()
    {
        // Public open target also works (public is not required, but not harmful).
        var source = """
            open Lib
            public Lib = {
                public Pi = 3
            }
            Pi
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Open_NonPublicMember_NotImported()
    {
        // open imports only public members. Non-public members must not be visible.
        var source = """
            open Lib
            Lib = {
                Pi = 3
            }
            Pi
            """;
        var result = Eval(source);
        Assert.True(result.IsError);
    }

    [Fact]
    public void Eval_Open_QualifiedAccess_StillWorks()
    {
        // Qualified dot-access should keep current intended behavior.
        var source = """
            Lib = {
                public Pi = 3
            }
            Lib.Pi
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Open_NestedLocalOpen_Works()
    {
        // open inside a nested algorithm body can open a sibling definition.
        var source = """
            A = {
                open Lib
                Lib = {
                    public Pi = 3
                }
                Pi
            }
            A
            """;
        AssertEval(source, 3);
    }

    // â”€â”€ BinaryOp.Pow evaluator coverage â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_Pow_IntegerExponentCases_Work()
    {
        AssertEval("2 ^ 0", 1);
        AssertEval("2 ^ 3", 8);
        AssertEval("5 ^ 4", 625);
        AssertEval("(-2) ^ 3", -8);
        AssertEval("(-2) ^ 4", 16);
        AssertEval("0 ^ 5", 0);
        AssertEval("0 ^ 0", 1);
        AssertEval("1 ^ 25", 1);
    }

    [Fact]
    public void Eval_Pow_NegativeIntegerExponentCases_Work()
    {
        AssertEval("2 ^ -3", 0.125m);
        AssertEval("10 ^ -2", 0.01m);
        AssertEval("(-2) ^ -3", -0.125m);
        AssertEval("1 ^ -25", 1);
    }

    [Fact]
    public void Eval_Pow_FractionalExponentCases_UseMathPow()
    {
        AssertEvalApprox("9 ^ 0.5", 3m, precision: 10);
        AssertEvalApprox("27 ^ 1.5", 140.2961154131m, precision: 10);
    }

    [Fact]
    public void Eval_Pow_FractionalExponent_MatchesMathPowNormalization()
    {
        AssertEval("0.0000000000000001 ^ 1.5 == Math.Pow(0.0000000000000001, 1.5)", 1);
    }

    [Fact]
    public void Eval_Pow_ZeroToNegativeInteger_FailsClearly()
    {
        AssertEvalFailsWithIllegalInEval("0 ^ -1", "zero cannot be raised to a negative integer exponent");
    }

    [Fact]
    public void Eval_Pow_ExponentOne_DoesNotOverflowFromFinalSquaring()
    {
        AssertEval("79228162514264337593543950335 ^ 1", 79228162514264337593543950335m);
    }

    // ── Numeric overflow ─────────────────────────────────────────────────────

    [Fact]
    public void Eval_Pow_Overflow_ReturnsNumericOverflow()
    {
        var err = GetEvalError("10 ^ 30");
        Assert.NotNull(err);
        Assert.IsType<EvalError.NumericOverflow>(err);
    }

    [Fact]
    public void Eval_Pow_NormalRange_Succeeds()
    {
        AssertEval("10 ^ 2", 100);
    }

    [Fact]
    public void Eval_Mul_Overflow_ReturnsNumericOverflow()
    {
        // decimal.MaxValue is ~7.9e28; multiplying two large values overflows
        var err = GetEvalError("79228162514264337593543950335 * 2");
        Assert.NotNull(err);
        Assert.IsType<EvalError.NumericOverflow>(err);
    }

    // â”€â”€ call args wiring (Lean: wireToCaller in user-defined call path) â”€â”€

    [Fact]
    public void Eval_CallArgsWiring_PropertyAsArgument()
    {
        // Caller property usable as argument: G resolves in caller scope
        var source = """
            G = 7
            F = x + 1
            F(G)
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_CallArgsWiring_PropertyDotAccessAsArgument()
    {
        // Property with dot-access usable as argument
        var source = """
            G = (public Val = 7)
            F = x + 1
            F(G.Val)
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_CallArgsWiring_MultiplePropertyArgs()
    {
        // Multiple properties as arguments
        var source = """
            A = 3
            B = 5
            Add = x + y
            Add(A, B)
            """;
        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_CallArgsWiring_NestedBlockScopeNotSmuggled()
    {
        // Block introduces its own scope â€” inner names don't leak
        var source = """
            F = x + 1
            F({10})
            """;
        AssertEval(source, 11);
    }

    // â”€â”€ NetSalary scenario (dotCall on parameterised algorithm) â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    [Fact]
    public void Eval_NetSalary_DotCallIncomeTax_FailsWhenOuterParamsAreCaptured()
    {
                var source = @"
                        NetSalary = {
                            SocialSecurityTax = grossSalary * 0.105
                            NonTaxableMinimum = grossSalary - SocialSecurityTax - 75
                            ChildTaxCredit = numberOfChildren * 162
                            TaxableIncome = NonTaxableMinimum - ChildTaxCredit
                            IncomeTax = TaxableIncome * 0.24

                            grossSalary - SocialSecurityTax - IncomeTax
                        }
                        NetSalary.IncomeTax(1000, 2)
                        ";

        AssertLocalOnlyPropertyMessage(
                        source,
                        "Property 'IncomeTax' on `NetSalary` is local-only because it depends on parameter(s) owned by the enclosing algorithm.");
    }

    [Fact]
    public void Eval_NetSalary_DirectCall_UsesAlgorithmParameters()
    {
        // NetSalary(1000, 2) binds the algorithm-level interface directly.
        // Output = 1000 - 105 - 119.04 = 775.96
        var source = """
            NetSalary = {
              SocialSecurityTax = grossSalary * 0.105
              NonTaxableMinimum = grossSalary - SocialSecurityTax - 75
              ChildTaxCredit = numberOfChildren * 162
              TaxableIncome = NonTaxableMinimum - ChildTaxCredit
              IncomeTax = TaxableIncome * 0.24
              
              grossSalary - SocialSecurityTax - IncomeTax
            }
            NetSalary(1000, 2)
            """;
        AssertEval(source, 775.96m);
    }

    [Fact]
    public void Eval_NetSalary_SelfContainedProperty_DotCall()
    {
        // Working approach: IncomeTax explicitly uses its own free variables.
        // grossSalary=1000, numberOfChildren=2:
        // (1000 - 1000*0.105 - 75 - 2*162) * 0.24 = 496 * 0.24 = 119.04
        var source = """
            NetSalary = {
              IncomeTax = (grossSalary - grossSalary * 0.105 - 75 - numberOfChildren * 162) * 0.24
            }
            NetSalary.IncomeTax(1000, 2)
            """;
        AssertEval(source, 119.04m);
    }

    // ── Named spread intrinsic ─────────────────────────────────────

    // A. Existing property detection still works

    [Fact]
    public void Eval_PropertyDetection_TwoPrivateProperties()
    {
        AssertEval("A = 5\nB = 10\nA + B", 15);
    }

    [Fact]
    public void Eval_PropertyDetection_PublicAndPrivateProperties()
    {
        AssertEval("public A = 5\nB = 10\nA + B", 15);
    }

    // B. Comma-only outputs still work

    [Fact]
    public void Eval_CommaOnly_MultipleOutputs()
    {
        AssertEval("1 + 2, 2 + 3", 3, 5);
    }

    [Fact]
    public void Eval_SequenceValue_ParensEmitOneSequenceValue()
    {
        AssertEval("(1, 2)", 1, 2);
    }

    [Fact]
    public void Eval_ReportStyleNewlineBodyContributionsAreOutputRows()
    {
        var implicitSource = """
            SalaryExpenses(gross, tax, pension) = gross, tax, pension
            SalaryExpenses(3800, 1, 0)
            ''
            SalaryExpenses(50, 0, 0)
            """;
        var explicitCommaSource = """
            SalaryExpenses(gross, tax, pension) = gross, tax, pension
            SalaryExpenses(3800, 1, 0), '', SalaryExpenses(50, 0, 0)
            """;

        var implicitResult = EvalFull(implicitSource);
        if (implicitResult.IsError)
            Assert.Fail($"Expected implicit newline join success but got error: {implicitResult.Error}");

        var explicitResult = EvalFull(explicitCommaSource);
        if (explicitResult.IsError)
            Assert.Fail($"Expected explicit comma output success but got error: {explicitResult.Error}");

        Assert.True(Result.ValueComparer.Equals(explicitResult.Value, implicitResult.Value));

        var output = Assert.IsType<Result.SequenceValue>(implicitResult.Value);
        Assert.Equal(3, output.Items.Count);
        AssertSequenceValueAtoms(output.Items[0], 3800m, 1m, 0m);
        Assert.Equal("", Assert.IsType<Result.Str>(output.Items[1]).Value);
        AssertSequenceValueAtoms(output.Items[2], 50m, 0m, 0m);
    }

    [Theory]
    [InlineData("1\n2\n3", "1, 2, 3")]
    [InlineData("{\n1\n2\n3\n}", "{\n1, 2, 3\n}")]
    [InlineData("{\n1, 2\n3\n}", "{\n1, 2, 3\n}")]
    public void Eval_NewlineBodyContextsMatchExplicitComma(
        string implicitSource,
        string explicitSource)
    {
        var implicitResult = EvalFull(implicitSource);
        if (implicitResult.IsError)
            Assert.Fail($"Expected implicit newline join success but got error: {implicitResult.Error}");

        var explicitResult = EvalFull(explicitSource);
        if (explicitResult.IsError)
            Assert.Fail($"Expected explicit comma join success but got error: {explicitResult.Error}");

        Assert.True(Result.ValueComparer.Equals(explicitResult.Value, implicitResult.Value));
    }

    [Fact]
    public void Eval_SequenceConstruct_CommaConstructionDiffersByEmittedSlotCount()
    {
        var expected = Result.FromItems([SequenceValue(Atom(1), Atom(2)), Atom(3)]);

        AssertEvalCounted(
            """
            Pair = 1, 2
            (Pair, 3)
            """,
            expectedEmittedCount: 1,
            expected);

        AssertEvalCounted(
            """
            Pair = 1, 2
            Pair, 3
            """,
            expectedEmittedCount: 2,
            expected);
    }

    [Fact]
    public void Eval_SequenceSpreadAfterSequenceConstruct_AppliesToImmediateExpression()
    {
        // The inner `.spread` binds to `b` only, so both forms supply the ONE
        // sequence-valued argument (1, 2) and the variadic parameter collects [(1, 2)].
        // (Had the spread applied to the whole chain — `X((a, b).spread)` — the
        // call would supply two arguments and collect [1, 2] instead.)
        var concise = EvalFull(
            """
            X(values...) = values
            a = 1
            b = 2
            X((a, b.spread))
            """);
        if (concise.IsError)
            Assert.Fail($"Expected concise success but got error: {concise.Error}");

        var sequenceValueResult = EvalFull(
            """
            X(values...) = values
            a = 1
            b = 2
            X((a, (b.spread)))
            """);
        if (sequenceValueResult.IsError)
            Assert.Fail($"Expected sequence-value success but got error: {sequenceValueResult.Error}");

        Assert.True(Result.ValueComparer.Equals(sequenceValueResult.Value, concise.Value));
        Assert.True(
            Result.ValueComparer.Equals(
                ListValue(SequenceValue(Atom(1), Atom(2))),
                concise.Value),
            $"Expected [(1, 2)] but got {concise.Value}");
    }

    // C. Spread emits immediate results

    [Fact]
    public void Eval_SequenceSpread_TwoFragments()
    {
        AssertEval("1 + 2, 2 + 3.spread 3 + 4", 3, 5, 7);
    }

    [Fact]
    public void Eval_SequenceSpread_MultipleFragments()
    {
        AssertEval("1 + 2, 2 + 3.spread 3 + 4.spread 4 + 5, 5 + 6, 6 + 7", 3, 5, 7, 9, 11, 13);
    }

    [Fact]
    public void Eval_SequenceSpread_LongChain_IsStackSafeForFlatAndCountedEvaluation()
    {
        const int itemCount = 8192;

        // A spread AST over a deep internal sequence-construction chain
        // stays stack-safe and spreads all 8192 items.
        var deepJoin = LongOneJoin(itemCount);
        var spreadJoin = new Expr.SequenceSpread(deepJoin);

        var flatR = Evaluator.RunFlat(spreadJoin);
        if (flatR.IsError)
            Assert.Fail($"Expected success but got error: {flatR.Error}");
        Assert.Equal(Enumerable.Repeat(1m, itemCount), flatR.Value);

        var countedRoot = new Expr.Block(new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("Values", new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: [deepJoin]))],
            Output:
            [
                BuiltinCall("sum", new Expr.Resolve("Values")),
                BuiltinCall("count", new Expr.Resolve("Values"))
            ]));

        var countedR = Evaluator.RunFlat(countedRoot);
        if (countedR.IsError)
            Assert.Fail($"Expected success but got error: {countedR.Error}");
        Assert.Equal([(decimal)itemCount, (decimal)itemCount], countedR.Value);

        // A deeply nested `.spread` chain stays
        // stack-safe; every level spreads the single item of the innermost
        // operand, so the flat result is the one spread value.
        Expr nested = new Expr.Num(1);
        for (var i = 0; i < itemCount; i++)
            nested = new Expr.SequenceSpread(nested);

        var nestedR = Evaluator.RunFlat(nested);
        if (nestedR.IsError)
            Assert.Fail($"Expected success but got error: {nestedR.Error}");
        Assert.Equal([1m], nestedR.Value);

        static Expr LongOneJoin(int count)
        {
            Expr expr = new Expr.Num(1);
            for (var i = 1; i < count; i++)
                expr = new Expr.SequenceConstruct(expr, new Expr.Num(1));
            return expr;
        }

        static Expr BuiltinCall(string name, Expr arg) =>
            new Expr.Call(
                new Expr.Resolve(name),
                new Algorithm.User(
                    Parent: null,
                    Parameters: [],
                    Opens: [],
                    Properties: [],
                    Output: [arg]));
    }

    [Fact]
    public void Eval_SequenceSpread_SourceDrivenPostfixChainAtParserLimit_IsStackSafe()
    {
        // Source-driven coverage (not raw AST construction): `1` followed by `.spread`
        // continuations parses to a deeply-nested unary spread chain
        // `SequenceSpread(SequenceSpread(...(1)))`. Parsing, elaborating, and evaluating it
        // from source stays stack-safe; every level spreads the single item 1, so the flat
        // result is [1].
        //
        // The depth is DERIVED from the parser's own supported ceiling rather than picked:
        // a base primary contributes no expression-chain level and each `.spread`
        // continuation contributes exactly one, so `Parser.MaxExpressionChainDepth` spreads
        // is the deepest chain the parser accepts. Both sides of that boundary are pinned by
        // ParserExpressionChainDepthTests.DotSpreadChain_BoundaryIsExactlyMaxExpressionChainDepth.
        //
        // Evaluator stack safety BEYOND the parser ceiling is a separate guarantee and is
        // already covered by Eval_SequenceSpread_LongChain_IsStackSafeForFlatAndCountedEvaluation
        // above, which builds the same nested spread chain directly as an AST at depth 8192.
        const int spreadCount = Parser.MaxExpressionChainDepth;
        var source = "1" + string.Concat(Enumerable.Repeat(".spread", spreadCount));

        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors);
        Assert.Empty(parsed.Diagnostics);   // in particular, no "chain is too deep" diagnostic

        // The source really produced the chain under test, one spread level per written `.spread`.
        var output = Assert.Single(parsed.Root.Output);
        var nesting = 0;
        var operand = output;
        while (operand is Expr.SequenceSpread(var inner))
        {
            nesting++;
            operand = inner;
        }

        Assert.Equal(spreadCount, nesting);
        Assert.IsType<Expr.Num>(operand);

        AssertEval(source, 1m);
    }

    [Fact]
    public void Eval_SequenceSpread_CommaSimilarityForSimpleConstants()
    {
        var source = """
            A = 1, 2
            B = 1.spread 2
            A.count
            B.count
            """;

        AssertEval(source, 2, 2);
    }

    [Fact]
    public void Eval_SequenceSpread_GroupsSpreadOneLevel()
    {
        AssertEval("(1, 2).spread 3", 1, 2, 3);
        AssertEval("1.spread, (2, 3)", 1, 2, 3);
        AssertEval("(1, 2).spread, (3, 4)", 1, 2, 3, 4);
    }

    [Fact]
    public void Eval_SequenceSpread_NestedSequenceValuesArePreserved()
    {
        var nestedLeft = EvalFull("((1, 2)).spread 3");
        if (nestedLeft.IsError)
            Assert.Fail($"Expected success but got error: {nestedLeft.Error}");

        AssertSequenceValueAtoms(nestedLeft.Value, 1, 2, 3);

        var nestedMiddle = EvalFull("(1, (2, 3)).spread 4");
        if (nestedMiddle.IsError)
            Assert.Fail($"Expected success but got error: {nestedMiddle.Error}");

        var middleGroup = Assert.IsType<Result.SequenceValue>(nestedMiddle.Value);
        Assert.Equal(3, middleGroup.Items.Count);
        AssertAtomValue(middleGroup.Items[0], 1);
        AssertSequenceValueAtoms(middleGroup.Items[1], 2, 3);
        AssertAtomValue(middleGroup.Items[2], 4);
    }

    [Fact]
    public void Eval_SequenceSpread_InlineDotCallCountMatchesComma()
    {
        AssertEval("(1.spread 2).count", 2);
        AssertEval("(1, 2).count", 2);
    }

    [Fact]
    public void Eval_SequenceConstruct_ErrorOrder_StopsAtEarlierContribution()
    {
        // Sequence-value evaluation evaluates contributions left to right and surfaces the
        // first failure: the unknown-name error from `Math.Nope` is reported
        // before the later `1 / 0` divide-by-zero is ever evaluated. (This is an
        // evaluation ordering test — the source contains no spread expression.)
        var error = GetEvalError("(1, Math.Nope, 1 / 0)");
        Assert.NotNull(error);

        var inner = error!;
        while (inner is EvalError.WithContext context)
            inner = context.Inner;

        var unknown = Assert.IsType<EvalError.UnknownName>(inner);
        Assert.Equal("Nope", unknown.Name);
    }

    // D. Spread by reference

    [Fact]
    public void Eval_SequenceSpread_ByReference()
    {
        var source = """
            Property1 = 1
            Property2 = 2, 3
            Property1.spread Property2
            """;
        AssertEval(source, 1, 2, 3);
    }

    // E. Sequence-spreading call outputs with additional expressions

    [Fact]
    public void Eval_SequenceSpread_Extension()
    {
        // Simplified version of the motivating pattern:
        // Spread calls with additional expressions.
        var source = """
            Next = if(a > 5, (a - 1, b + 1), (b - 1, a + 1))
            Result = Next(10, 0).spread 10 > 5
            Result
            """;
        AssertEval(source, 9, 1, 1);
    }

    // F. Nested algorithm with spread

    [Fact]
    public void Eval_SequenceSpread_InParenAlgorithm()
    {
        // (1 + 2.spread 3 + 4) is a parameterless nested algorithm with spread.
        AssertEval("(1 + 2.spread 3 + 4)", 3, 7);
    }

    // G. Capturing algorithm with spread

    [Fact]
    public void Eval_SequenceSpread_InBraceAlgorithm()
    {
        var source = "{ X = 10\nX + 1.spread X + 2 }";
        AssertEval(source, 11, 12);
    }

    // H. Ordinary parenthesized arithmetic expression unchanged

    [Fact]
    public void Eval_ParenGrouping_ArithmeticUnchanged()
    {
        AssertEval("1 + (2 * 3)", 7);
    }

    // I. Multiline formatting with explicit commas remains irrelevant

    [Fact]
    public void Eval_SequenceSpread_MultilineWithExplicitCommasEquivalentToOneline()
    {
        var multiline = """
            1 + 2, 2 + 3.spread,
            3 + 4.spread,
            4 + 5, 5 + 6
            """;
        var oneline = "1 + 2, 2 + 3.spread, 3 + 4.spread, 4 + 5, 5 + 6";
        var r1 = Eval(multiline);
        var r2 = Eval(oneline);
        Assert.Equal(r1.Value, r2.Value);
    }

    [Fact]
    public void Eval_SequenceSpread_DotCallReceiverBoundaryCanBeSpread()
    {
        var commaSource = """
            A = 1, 2
            F = a, 3
            A.F
            """;

        var commaResult = EvalFull(commaSource);
        if (commaResult.IsError)
            Assert.Fail($"Expected success but got error: {commaResult.Error}");

        var commaGroup = Assert.IsType<Result.SequenceValue>(commaResult.Value);
        Assert.Equal(2, commaGroup.Items.Count);
        AssertSequenceValueAtoms(commaGroup.Items[0], 1, 2);
        AssertAtomValue(commaGroup.Items[1], 3);

        var sequenceSpreadSource = """
            A = 1, 2
            F = a.spread 3
            A.F
            """;

        AssertEval(sequenceSpreadSource, 1, 2, 3);
    }

    [Fact]
    public void Eval_SequenceSpread_DoesNotPreserveOrMergeProperties()
    {
        var valueSource = """
            A = {
                X = 1
                10
            }

            B = {
                Y = 2
                20
            }

            C = A.spread B
            C
            """;
        AssertEval(valueSource, 10, 20);

        var xSource = """
            A = {
                X = 1
                10
            }

            B = {
                Y = 2
                20
            }

            C = A.spread B
            C.X
            """;
        AssertEvalFails(xSource);

        var ySource = """
            A = {
                X = 1
                10
            }

            B = {
                Y = 2
                20
            }

            C = A.spread B
            C.Y
            """;
        AssertEvalFails(ySource);
    }

    [Fact]
    public void Eval_SequenceSpread_NoOutputOperandFails()
    {
        // Postfix `Bad.spread` spreads its (only) operand; a no-output operand
        // fails with the spread missing-output diagnostic, whose span
        // points at the offending operand `Bad` (line 5, columns 1-3), not at the
        // whole spread or some synthetic location.
        var operandSource = """
            Bad = {
                X = 1
            }

            Bad.spread
            """;
        AssertSpreadMissingOutput(operandSource, 5, 1, 5, 3);

        // A no-output expression after the spread is an ordinary missing-output
        // failure, not the spread's right operand: `3.spread Bad` is the two
        // expression-list slots `3.spread` and `Bad`.
        var joinedSource = """
            Bad = {
                X = 1
            }

            3.spread Bad
            """;
        AssertEvalFails(joinedSource);
    }

    [Fact]
    public void Eval_SequenceSpreadThenMissingAdjacentExpression_FailsOutsideSpread()
    {
        // `3.spread Bad` is the two expression-list slots `3.spread` and `Bad`. The
        // `3.spread` spread succeeds; `Bad` is a SEPARATE expression-list slot that
        // fails on its own because it has no output. Since `.spread` has no right
        // operand, `Bad` never enters the spread, so the failure is the ordinary
        // missing-output error, NOT SpreadMissingOutput.
        var source = """
            Bad = {
                X = 1
            }

            3.spread Bad
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);

        var inner = error!;
        while (inner is EvalError.WithContext context)
            inner = context.Inner;

        Assert.IsNotType<EvalError.SpreadMissingOutput>(inner);
        Assert.IsType<EvalError.MissingOutput>(inner);
    }

    [Fact]
    public void Eval_Call_SpreadAdjacencyAndCommaBothSupplySeparateArguments()
    {
        // A spread expression has no right operand:
        // `F(X.spread, 2)` is TWO argument slots — `X.spread` spreads X's items (just 1),
        // then `2` — so it binds the two-parameter F to 1 + 2 = 3.
        AssertEval(
            """
            X = 1
            F(a, b) = a + b
            F(X.spread, 2)
            """,
            3m);

        // `F(X.spread 2)` is also TWO argument slots under adjacency-as-expression-list:
        // `X.spread` and `2`.
        AssertEval(
            """
            X = 1
            F(a, b) = a + b
            F(X.spread 2)
            """,
            3m);
    }

    [Fact]
    public void Eval_SequenceSpread_OfEmptySequenceContributesNoItems()
    {
        AssertEval("1, ().spread, 2", 1, 2);
        AssertEval("1, (()).spread, 2", 1, 2);
        AssertEval("().spread, 1", 1);
        AssertEval("1, ().spread", 1);
        AssertEvalEmptyOutput("().spread");
    }

    // Additional: simple spread of two literals

    [Theory]
    [InlineData("A.spread B")]
    [InlineData("A.spread, B")]
    [InlineData("A .spread B")]
    [InlineData("spread(A) B")]
    [InlineData("spread(A), B")]
    [InlineData("A.spread\nB")]
    public void Eval_SpreadThenJoin_CreatesExpressionListSlots(string tail)
    {
        // `A.spread B` is expression-list adjacency after a spread slot, not a
        // binary spread: a spread expression never consumes a right operand,
        // and same-line whitespace before `.spread` stays a postfix
        // continuation. The call form `spread(A) B` joins identically.
        var program = "A = 1, 2\nB = 3, 4\n" + tail;
        AssertEvalCounted(program, 3, Result.FromItems([Atom(1), Atom(2), SequenceValue(Atom(3), Atom(4))]));
    }

    [Fact]
    public void Eval_SequenceSpread_SimpleLiterals()
    {
        AssertEval("1.spread 2", 1, 2);
        AssertEval("1.spread 2.spread 3", 1, 2, 3);
    }

    [Fact]
    public void Eval_SequenceSpread_PropertyBody()
    {
        AssertEval("A = 1.spread 2\nA", 1, 2);
    }

    [Fact]
    public void Eval_SequenceValue_ParensCreateOneSequenceValue()
    {
        AssertEvalCounted(
            "(1, 2, 3)",
            expectedEmittedCount: 1,
            SequenceValue(Atom(1), Atom(2), Atom(3)));
    }

    [Fact]
    public void Eval_SequenceConstruct_CommaCreatesSiblingOutputSlots()
    {
        AssertEvalCounted(
            "1, 2, 3",
            expectedEmittedCount: 3,
            SequenceValue(Atom(1), Atom(2), Atom(3)));
    }

    [Theory]
    [InlineData("Sum((1, 2, 3))")]
    [InlineData("Seq = (1, 2, 3)\nSum(Seq)")]
    [InlineData("Seq = 1, 2, 3\nSum(Seq)")]
    public void Eval_SingleVariadic_GroupedArgumentIsOneCollectedItem(string call)
        // Each call supplies ONE sequence-valued argument, and the collecting binding
        // collects the supplied slots as the one-element list [(1, 2, 3)] — the
        // old grouped/opened display coincidence is intentionally gone.
        => AssertEval(
            $$"""
            Sum(values...) = values.count
            {{call}}
            """,
            1m);

    [Theory]
    [InlineData("Sum(1, 2, 3)")]
    [InlineData("Sum(1 2 3)")]
    public void Eval_SingleVariadic_InlineCommaOrAdjacencyBindsItemSupply(string call)
        // Inline comma and adjacency both supply three argument slots, bound by the
        // item-supply matcher as one sequence value of count 3 — the same as the
        // grouped form `Sum((1, 2, 3))`.
        => AssertEval(
            $$"""
            Sum(values...) = values.count
            {{call}}
            """,
            3m);

    [Theory]
    [InlineData("Pair = (1, 2)\nAdd(Pair)")]
    [InlineData("Pair = 1, 2\nAdd(Pair)")]
    public void Eval_FixedCalls_DoNotDestructureSequenceArgumentWithoutSpread(string call)
        => AssertEvalFailsWithArityMismatch(
            $$"""
            Add(a, b) = a + b
            {{call}}
            """,
            expected: 2,
            actual: 1);

    [Theory]
    [InlineData("Pair = (1, 2)\nAdd(Pair.spread)")]
    [InlineData("Pair = 1, 2\nAdd(Pair.spread)")]
    public void Eval_FixedCalls_ExplicitSpreadDestructuresSequenceArgument(string call)
        => AssertEval(
            $$"""
            Add(a, b) = a + b
            {{call}}
            """,
            3m);

    [Theory]
    [InlineData("F((1, 2, 3), 99)")]
    public void Eval_VariadicWithSuffix_SequenceArgumentStaysOneCollectedItem(string call)
        // F((1, 2, 3), 99) supplies one sequence-valued argument plus the suffix:
        // the variadic parameter collects [(1, 2, 3)] (count 1) and last binds 99. Ordinary
        // calls never implicitly open sequence arguments.
        => AssertEval(
            $$"""
            F(values..., last) = values.count, last
            {{call}}
            """,
            1m,
            99m);

    [Theory]
    [InlineData("F(1, 2, 3, 99)")]
    [InlineData("Seq = (1, 2, 3)\nF(Seq.spread, 99)")]
    public void Eval_VariadicWithSuffix_DeconstructsInlineCommaOrSpreadSlots(string call)
        // F(values..., last) is a comma deconstruction parameter list: the inline
        // comma slots and the spread both supply four items, so the variadic
        // captures [1, 2, 3] (count 3) and last binds 99.
        => AssertEval(
            $$"""
            F(values..., last) = values.count, last
            {{call}}
            """,
            3m,
            99m);

    [Fact]
    public void Eval_SequenceSpread_OpensOneBoundaryAtOutput()
    {
        AssertEval(
            """
            Seq1 = (1, 2, 3)
            Seq2 = (1, 2, 3)
            Seq1.spread
            Seq2.spread
            """,
            1m,
            2m,
            3m,
            1m,
            2m,
            3m);

        AssertEvalResultLoopModes(
            """
            Nested = ((1, 2), 3)
            Nested.spread
            """,
            Result.FromItems([SequenceValue(Atom(1), Atom(2)), Atom(3)]));
    }

    [Theory]
    [InlineData("Add(Pair)", false)]
    [InlineData("Add(Pair.spread)", true)]
    public void Eval_SequenceValue_FixedCallSlotSpreadRequiresEllipsis(string call, bool succeeds)
    {
        var source = $$"""
            Pair = (1, 2)
            Add(a, b) = a + b
            {{call}}
            """;

        if (succeeds)
            AssertEval(source, 3m);
        else
            AssertEvalFailsWithArityMismatch(source, expected: 2, actual: 1);
    }

    [Theory]
    [InlineData("1\n2\n3")]
    [InlineData("1 2 3")]
    public void Eval_Adjacency_IsImplicitExpressionList(string source)
    {
        AssertEvalCounted(
            source,
            expectedEmittedCount: 3,
            ResultFromAtoms(1, 2, 3));
    }

    [Fact]
    public void Eval_DotCallReceiver_RemainsCanonicalOneArgument()
    {
        // The receiver is one argument, so the variadic parameter collects [(1, 2, 3)].
        AssertEval(
            """
            Seq = (1, 2, 3)
            Sum(values...) = values.count
            Seq.Sum()
            """,
            1m);

        AssertEvalFailsWithArityMismatch(
            """
            Pair = (1, 2)
            Add(a, b) = a + b
            Pair.Add()
            """,
            expected: 2,
            actual: 1);
    }

    // ── Higher-Order Algorithm Parameters ────────────────────────────────────

    [Fact]
    public void Eval_HigherOrder_AlgoCallsPassedAlgorithm()
    {
        // Algo = func(9); F = a + 1; Algo(F) → F(9) → 9+1 = 10
        AssertEval("Algo = func(9)\nF = a + 1\nAlgo(F)", 10);
    }

    [Fact]
    public void Eval_HigherOrder_PassAlgorithmWithArgs()
    {
        // Apply = func(x); F = a + 1; Apply(F, 5) → F(5) → 5+1 = 6
        AssertEval("Apply = func(x)\nF = a + 1\nApply(F, 5)", 6);
    }

    [Fact]
    public void Eval_HigherOrder_MultiParamNeedsExplicitCall()
    {
        // Use = func; F = a + 1; Use(F) → F has params, used bare → arityMismatch
        AssertEvalFails("Use = func\nF = a + 1\nUse(F)");
    }

    [Fact]
    public void Eval_HigherOrder_NonAlgorithmArg_NotAnAlgorithm()
    {
        // Algo = func(9); Algo(5) → 5 is not an algorithm → notAnAlgorithm
        AssertEvalFails("Algo = func(9)\nAlgo(5)");
    }

    [Fact]
    public void Eval_HigherOrder_NestedAlgorithmPassing()
    {
        // Outer = func(10); Inner = func(a); F = a * 2; Inner(F, Outer(F))
        // Outer(F) → F(10) → 20; Inner(F, 20) → F(20) → 40
        AssertEval("Outer = func(10)\nInner = func(a)\nF = a * 2\nInner(F, Outer(F))", 40);
    }

    [Fact]
    public void Eval_HigherOrder_AlgorithmWithMultipleParams()
    {
        // Algo = func(3, 4); F = a + b; Algo(F) → F(3, 4) → 7
        AssertEval("Algo = func(3, 4)\nF = a + b\nAlgo(F)", 7);
    }

    [Fact]
    public void Eval_HigherOrder_DualView_BothAlgAndValueMeaning()
    {
        // Named algorithm V = 42 resolves structurally and also evaluates to a value.
        // This is about lexical algorithm lookup, not zero-parameter inline blocks.
        // Use = func; V = 42; Use(V) → ValEnv has func=42, AlgEnv has func=V
        // Param("func") checks ValEnv first → 42
        AssertEval("Use = func\nV = 42\nUse(V)", 42);
    }

    [Fact]
    public void Eval_HigherOrder_DotCall_StructuralPropertyWithHOF()
    {
        // Structural property Apply takes a higher-order func param + value param
        // Must use same dual-view binding logic as normal user-defined calls
        var source = """
            A = (Apply = func(x)
            0)
            F = a + 1
            A.Apply(F, 5)
            """;
        AssertEvalAllPublic(source, 6);
    }

    [Fact]
    public void Eval_HigherOrder_DotCall_StructuralPropertyPassesAlgorithm()
    {
        // Structural property Algo calls a passed algorithm with fixed value
        var source = """
            A = (Algo = func(9)
            0)
            F = a + 1
            A.Algo(F)
            """;
        AssertEvalAllPublic(source, 10);
    }

    [Fact]
    public void Eval_HigherOrder_SequenceValueBeforeAlgorithmOnlyArg_KeepsFilteredGroupCountAsOne()
    {
        var source = """
            OccurrenceCount = filter(values, predicate).count
            OccurrenceCount((1, 2), {n:0 mod 2 == 1})
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_HigherOrder_InlinePredicate_CapturesOuterValueParameter_ReturnsKeptItemAsListElement()
    {
        var source = """
            OccurrenceCount(target) = {
                MatchesTarget(pair) = pair:1 == target:1
                filter(((1, 10), (2, 20), (2, 30)), MatchesTarget)
            }
            OccurrenceCount((2, 20))
            """;

        var result = EvalFull(source);
        if (result.IsError)
            Assert.Fail($"Expected success but got error: {result.Error}");

        // Only (2, 20) matches; it stays an exact list element, and the list
        // [(2, 20)] passes through the user-call boundary unchanged.
        AssertListOfSequenceValueAtoms(result.Value, [2m, 20m]);
    }

    [Fact]
    public void Eval_HigherOrder_FinalSequenceValueAfterAlgorithmOnlyArgumentDoesNotUnpack()
    {
        var source = """
            Inc = x + 1
            UsePair(f, x, y) = f(x) + y
            UsePair(Inc, (10, 20))
            """;

        AssertEvalFailsWithArityMismatch(source, expected: 2, actual: 1);
    }

    [Fact]
    public void Eval_HigherOrder_GraceReordersCallableParameter()
    {
        var source = """
            IsEven = x mod 2 == 0
            Choose = if(predicate~(x), x, 0)
            Choose(3, IsEven)
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_HigherOrder_FlatMultiBinderClause_UsesOrdinaryBinding()
    {
        var source = """
            IsEven = y mod 2 == 0
            Choose(x, predicate) = if(predicate(x), x, 0)
            Choose(4, IsEven)
            """;

        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_HigherOrder_FlatMultiBinderClause_FalsePredicate_UsesElseBranch()
    {
        var source = """
            IsEven = y mod 2 == 0
            Choose(x, predicate) = if(predicate(x), x, 0)
            Choose(3, IsEven)
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_HigherOrder_FlatMultiBinderClause_DotCallUsesOrdinaryBinding()
    {
        var source = """
            Holder = (
                Apply(x, transform) = transform(x)
                Apply
            )
            Increment = y + 1
            Holder.Apply(9, Increment)
            """;

        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_ClauseDefinition_SingleBinder_ElaboratesToOrdinaryAlgorithm()
    {
        var source = """
            Id(x) = x
            Id(7)
            """;

        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_ClauseDefinition_SingleBinder_HigherOrderCallUsesOrdinaryBinding()
    {
        var source = """
            Apply(f) = f(4)
            Double(x) = x * 2
            Apply(Double)
            """;

        AssertEval(source, 8);
    }

    [Fact]
    public void Eval_ClauseDefinition_SingleBinder_RejectsExtraArguments()
    {
        var error = GetEvalError("""
            Id(x) = x
            Id(1, 2)
            """);

        Assert.NotNull(error);

        while (error is EvalError.WithContext withContext)
            error = withContext.Inner;

        var arity = Assert.IsType<EvalError.ArityMismatch>(error);
        Assert.Equal(1, arity.Expected);
        Assert.Equal(2, arity.Actual);
    }

    [Fact]
    public void Eval_DirectCall_UsesAlgorithmLevelExplicitParameters()
    {
        var source = """
            Algo(x) = {
              Output = x + 1
            }
            Algo(6)
            """;

        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_DirectCall_MultiParameterAlgorithmLevelDefinition_SupportsExplicitOutput()
    {
        var source = """
            ImpactOnEarth(mass, height) = {
              Gravity = 9.81
              Output = mass * Gravity * height
            }
            ImpactOnEarth(3, 2)
            """;

        AssertEval(source, 58.86m);
    }

    [Fact]
    public void Eval_DirectCall_ShorthandBodyStillWorks()
    {
        AssertEval(
            """
            Algo(x) = x + 1
            Algo(6)
            """,
            7);
    }

    [Fact]
    public void Eval_DirectCall_UsesAlgorithmArityInDiagnostics()
    {
        AssertArityMismatchMessage(
            """
            Algo(x) = {
              Output = x + 1
            }
            Algo()
            """,
            "Callable `Algo(x)` expects 1 argument, but was called with 0 arguments.");
    }

    [Fact]
    public void Eval_DirectCall_ZeroParamExplicitOutput_PreservesExistingBehavior()
    {
        AssertEval(
            """
            Algo = {
              Output = 5
            }
            Algo()
            """,
            5);

        AssertArityMismatchMessage(
            """
            Algo = {
              Output = 5
            }
            Algo(6)
            """,
            "Callable `Algo` expects 0 arguments, but was called with 1 argument.");
    }

    [Fact]
    public void Eval_DirectCall_DoesNotMakeHelperCallableThroughAlgorithmName()
    {
        AssertArityMismatchMessage(
            """
            Algo = {
              Helper(x) = x * 2
              Output = 5
            }
            Algo(6)
            """,
            "Callable `Algo` expects 0 arguments, but was called with 1 argument.");
    }

    [Fact]
    public void Eval_DirectCall_PreservesHelperDotCall()
    {
        var source = """
            Algo = {
              Helper(x) = x * 2
              Output = 5
            }
            Algo.Helper(6)
            """;

        AssertEval(source, 12);
    }

        [Fact]
        public void Eval_NestedHelperCapture_RemainsCallableLocally()
        {
                AssertEval(
                        """
                        Algo(x) = {
                            Prop = x + 1
                            Prop * 2
                        }
                        Algo(6)
                        """,
                        14);
        }

        [Fact]
        public void Eval_ImplicitAndExplicitOuterOwnership_StayEquivalentForLocalUse()
        {
                AssertEval(
                        """
                        Algo = {
                            Prop = x + 1
                            x
                        }
                        Algo(6)
                        """,
                        6);

                AssertEval(
                        """
                        Algo(x) = {
                            Prop = x + 1
                            x
                        }
                        Algo(6)
                        """,
                        6);
        }

        [Fact]
        public void Eval_CapturedNestedProperty_DotAccess_IsLocalOnly()
        {
                AssertLocalOnlyPropertyMessage(
                        """
                        Algo(x) = {
                            Prop = x + 1
                            x
                        }
                        Algo.Prop
                        """,
                        "Property 'Prop' on `Algo` is local-only because it depends on parameter(s) owned by the enclosing algorithm.");
        }

        [Fact]
        public void Eval_CapturedNestedProperty_DotCall_IsLocalOnly()
        {
                AssertLocalOnlyPropertyMessage(
                        """
                        Algo(x) = {
                            Prop = x + 1
                            x
                        }
                        Algo.Prop(6)
                        """,
                        "Property 'Prop' on `Algo` is local-only because it depends on parameter(s) owned by the enclosing algorithm.");
        }

        [Fact]
        public void Eval_ImplicitlyOwnedCapturedNestedProperty_DotAccess_IsLocalOnly()
        {
                AssertLocalOnlyPropertyMessage(
                        """
                        Algo = {
                            Prop = x + 1
                            x
                        }
                        Algo.Prop
                        """,
                        "Property 'Prop' on `Algo` is local-only because it depends on parameter(s) owned by the enclosing algorithm.");
        }

    [Fact]
    public void Eval_ContainerWithParametrizedChildProperty_RemainsCallable()
    {
        AssertEval(
            """
            Algo = {
              Prop(x, y) = 7
            }
            Algo.Prop(1, 2)
            """,
            7);
    }

    [Fact]
    public void Eval_PlainContainerAlgorithm_RemainsValid()
    {
        AssertEval(
            """
            Algo = {
              Prop = 7
            }
            Algo.Prop
            """,
            7);
    }

    [Fact]
    public void Eval_DirectCall_NestedAlgorithmLevelDefinition_PreservesNestedCalls()
    {
        var source = """
            Outer = {
              Inner(x) = {
                Output = x + 10
              }
              Inner(5)
            }
            Outer, Outer.Inner(5)
            """;

        AssertEval(source, 15, 15);
    }

        [Fact]
        public void Eval_ConditionalBranchProperty_IsLocalOnly()
        {
                AssertLocalOnlyPropertyMessage(
                        """
                        Outer(0) = {
                            Inner = 1
                            0
                        }
                        Outer(x) = {
                            Inner = x + 1
                            x
                        }
                        Outer.Inner
                        """,
                        "Property 'Inner' on `Outer` is local-only because properties defined inside conditional algorithms are not publicly visible.");
        }

        [Fact]
        public void Eval_ConditionalBranchProperties_AreNeverExposedThroughParent()
        {
                AssertLocalOnlyPropertyMessage(
                        """
                        Outer(0) = {
                            First = 1
                            0
                        }
                        Outer(x) = {
                            Second = x + 1
                            x
                        }
                        Outer.Second
                        """,
                        "Property 'Second' on `Outer` is local-only because properties defined inside conditional algorithms are not publicly visible.");
        }

    [Fact]
    public void Eval_ManualAlgorithmWithExplicitParametersWithoutOutput_IsRejected()
    {
        var invalid = new Algorithm.User(
            Parent: null,
            Parameters: Algorithm.NormalParameters(["x"]),
            Opens: [],
            Properties:
            [
                new Property(
                    "Prop",
                    new Algorithm.User(
                        Parent: null,
                        Parameters: [],
                        Opens: [],
                        Properties: [],
                        Output: [new Expr.Num(7m)]))
            ],
            Output: [])
        {
            ExplicitParameters = [new ParameterDeclaration("x", new SourceSpan(1, 6, 1, 6))]
        };

        var result = Evaluator.Run(new Expr.Block(invalid));

        Assert.True(result.IsError);
        Assert.IsType<EvalError.ExplicitParametersRequireOutput>(result.Error);
        Assert.Equal(
            AlgorithmValidation.ExplicitParametersRequireOutputMessage,
            KatLangError.FromEvalError(result.Error).Message);
    }

    [Fact]
    public void Eval_ManualOutputDotCall_IsRejected()
    {
        var callee = new Algorithm.User(
            Parent: null,
            Parameters: Algorithm.NormalParameters(["x"]),
            Opens: [],
            Properties: [],
            Output: [new Expr.Binary(BinaryOp.Add, new Expr.Param("x"), new Expr.Num(1m))]);

        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("Algo", callee)],
            Output:
            [
                new Expr.DotCall(
                    new Expr.Resolve("Algo"),
                    "Output",
                    new Algorithm.User(Parent: null, Parameters: [], Opens: [], Properties: [], Output: [new Expr.Num(6m)]))
            ]);

        var result = Evaluator.Run(new Expr.Block(root));

        Assert.True(result.IsError);
        AssertInnermostSpecialOutputAccess(result.Error);
        Assert.Equal(
            "Output is the designated result of an algorithm and cannot be accessed through property syntax. Call the algorithm directly instead. Instead of `Algo.Output(...)`, write `Algo(...)`.",
            KatLangError.FromEvalError(result.Error).Message);
    }

    [Fact]
    public void Eval_ManualNestedOutputDotCall_UsesReceiverSpecificGuidance()
    {
        var inner = new Algorithm.User(
            Parent: null,
            Parameters: Algorithm.NormalParameters(["x"]),
            Opens: [],
            Properties: [],
            Output: [new Expr.Binary(BinaryOp.Add, new Expr.Param("x"), new Expr.Num(10m))]);

        var outer = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("Inner", inner)],
            Output: []);

        var root = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [new Property("Outer", outer)],
            Output:
            [
                new Expr.DotCall(
                    new Expr.DotCall(new Expr.Resolve("Outer"), "Inner"),
                    "Output",
                    new Algorithm.User(Parent: null, Parameters: [], Opens: [], Properties: [], Output: [new Expr.Num(6m)]))
            ]);

        var result = Evaluator.Run(new Expr.Block(root));

        Assert.True(result.IsError);
        AssertInnermostSpecialOutputAccess(result.Error);
        Assert.Equal(
            "Output is the designated result of an algorithm and cannot be accessed through property syntax. Call the algorithm directly instead. Instead of `Outer.Inner.Output(...)`, write `Outer.Inner(...)`.",
            KatLangError.FromEvalError(result.Error).Message);
    }

    [Fact]
    public void Eval_ClauseDefinition_SequenceValuePattern_RemainsConditionalWholeArgument()
    {
        var source = """
            Stats(x, (acc, counter)) = (x + acc, counter + 1)
            Stats(3, (0, 0))
            """;

        AssertEval(source, 3, 1);
    }

    [Fact]
    public void Eval_ClauseGroup_DoubleParenSequenceValuePattern_MatchesSingleBinderArity()
    {
        var source = """
            MarkSequenceValueRange((a, b, c)) = 1
            MarkSequenceValueRange(x) = 0
            MarkSequenceValueRange(5)
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_ClauseGroup_DoubleParenSequenceValuePattern_FallsThroughForListRangeArgument()
    {
        // range returns an exact list value, and multi-clause conditional
        // sequence-value patterns match sequence values only (list patterns are
        // deferred by design), so the list argument takes the fallback clause.
        var source = """
            MarkSequenceValueRange((a, b, c)) = 1
            MarkSequenceValueRange(x) = 0
            MarkSequenceValueRange(range(1, 3))
            """;

        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_ClauseGroup_DoubleParenSequenceValuePattern_MatchesSpreadRangeArgument()
    {
        // Spreading the range list inside parentheses builds a sequence value
        // (1, 2, 3), which the sequence-value pattern clause matches.
        var source = """
            MarkSequenceValueRange((a, b, c)) = 1
            MarkSequenceValueRange(x) = 0
            MarkSequenceValueRange((range(1, 3).spread))
            """;

        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_ClauseGroup_LiteralThenPlainBinder_RemainsConditional()
    {
        var source = """
            F(0) = 0
            F(x) = 1
            F(2)
            """;

        AssertEval(source, 1);
    }

    // ── Inline block arguments (higher-order) ────────────────────────────────

    [Fact]
    public void Eval_InlineBlock_PassedInParens()
    {
        // Apply = func(x); Apply({a + 1}, 5) → {a+1}(5) → 6
        AssertEval("Apply = func(x)\nApply({a + 1}, 5)", 6);
    }

    [Fact]
    public void Eval_InlineBlock_DotCall_PassedInParens()
    {
        // A.Apply = func(x); A.Apply({a + 1}, 5) → 6
        var source = """
            A = (Apply = func(x)
            0)
            A.Apply({a + 1}, 5)
            """;
        AssertEvalAllPublic(source, 6);
    }

    [Fact]
    public void Eval_InlineBlock_ZeroParamSingleOutputInParens_RemainsValueStructure()
    {
        // Zero-parameter inline blocks stay value/output structures in
        // higher-order argument position.
        AssertEval("Apply(f) = f\nApply({123})", 123);
    }

    [Fact]
    public void Eval_InlineBlock_ZeroParamSingleOutputInParens_IsNotAutoCallable()
    {
        // A zero-parameter inline block does not become callable just because
        // it emits exactly one output.
        AssertEvalFails("Apply(f) = f()\nApply({123})");
    }

    [Fact]
    public void Eval_InlineBlock_ZeroParamMultiOutputInParens_RemainsValueStructure()
    {
        // Output count does not change higher-order binding mode.
        AssertEval("Apply(f) = f\nApply({1, 2})", 1, 2);
    }

    [Fact]
    public void Eval_InlineBlock_ZeroParamMultiOutputInParens_IsNotAutoCallable()
    {
        // Multi-output zero-parameter inline blocks follow the same rule as
        // single-output ones: they stay value/output structures rather than
        // callable higher-order arguments.
        AssertEvalFails("Apply(f) = f()\nApply({1, 2})");
    }

    [Fact]
    public void Eval_InlineBlock_TrailingBrace_SingleArg()
    {
        // Algo = func(9); Algo{a + 1} → {a+1}(9) → 10
        AssertEval("Algo = func(9)\nAlgo{a + 1}", 10);
    }

    [Fact]
    public void Eval_InlineBlock_TrailingBrace_ZeroParam()
    {
        // Use = func; Use{42} → 42
        AssertEval("Use = func\nUse{42}", 42);
    }

    [Fact]
    public void Eval_InlineBlock_TrailingBrace_ArityMismatch()
    {
        // Use = func; Use{a + 1} → block has param a, bare usage → arityMismatch
        AssertEvalFails("Use = func\nUse{a + 1}");
    }

    // ── Explicit output syntax ──────────────────────────────────────────────

    [Fact]
    public void Eval_ExplicitOutput_BasicForm()
    {
        // Explicit: Output = A should work the same as implicit A
        AssertEval("A = 6\nOutput = A", 6);
    }

    [Fact]
    public void Eval_ExplicitOutput_NumericLiteral()
    {
        AssertEval("Output = 42", 42);
    }

    [Fact]
    public void Eval_ExplicitOutput_Expression()
    {
        AssertEval("A = 3\nOutput = A + 1", 4);
    }

    [Fact]
    public void Eval_ExplicitOutput_InMiddleOfProperties()
    {
        // Output defined between properties should still work
        AssertEval("A = 1\nOutput = A + B\nB = 2", 3);
    }

    [Fact]
    public void Eval_ExplicitOutput_MultipleValues()
    {
        AssertEval("Output = 1, 2, 3", 1, 2, 3);
    }

    [Fact]
    public void Eval_ExplicitOutput_EquivalentToImplicit()
    {
        // Both forms should produce the same result
        var implicitResult = Eval("A = 6\nA");
        var explicitResult = Eval("A = 6\nOutput = A");
        Assert.True(implicitResult.IsOk);
        Assert.True(explicitResult.IsOk);
        Assert.Equal(implicitResult.Value, explicitResult.Value);
    }

    [Fact]
    public void Eval_ExplicitOutput_InsideBlock()
    {
        var source = """
            X = {
              A = 3
              Output = A + 1
              B = 2
            }
            X
            """;
        AssertEval(source, 4);
    }

    [Fact]
    public void Eval_ExplicitOutput_WithParametrizedProperty()
    {
        // Explicit output with a property that has implicit params
        AssertEval("Add = x + y\nOutput = Add(3, 4)", 7);
    }

    [Fact]
    public void Eval_ImplicitOutput_StillWorks()
    {
        // Ensure implicit output is unaffected
        AssertEval("A = 6\nA", 6);
    }

    // ── if builtin ───────────────────────────────────────────────────────────────

    [Fact]
    public void Eval_If3_TrueCondition_ReturnsThenBranch()
        => AssertEval("if(1 == 1, 5, 6)", 5);

    [Fact]
    public void Eval_If3_FalseCondition_ReturnsElseBranch()
        => AssertEval("if(1 == 2, 5, 6)", 6);

    [Fact]
    public void Eval_If3_TrueInAddition()
        => AssertEval("10 + if(1 == 1, 5, 0)", 15);

    [Fact]
    public void Eval_If3_FalseInAddition()
        => AssertEval("10 + if(1 == 2, 5, 0)", 10);

    [Fact]
    public void Eval_If3_CompatibleWithEarlierCoverage_True()
        => AssertEval("if(1 == 1, 5, 6)", 5);

    [Fact]
    public void Eval_If3_CompatibleWithEarlierCoverage_False()
        => AssertEval("if(1 == 2, 5, 6)", 6);

    [Fact]
    public void Eval_If2_RuntimeBuiltinCall_FailsWithSignatureArityMessage()
    {
        var expr = new Expr.Call(
            new Expr.Resolve("if"),
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Num(1), new Expr.Num(5)]));

        var result = Evaluator.Run(expr);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Equal(
            "Callable `if(condition, whenTrue, whenFalse)` expects 3 arguments, but was called with 2 arguments.",
            formatted);
    }

    [Fact]
    public void Eval_If2_RuntimeBuiltinCallInBinary_FailsInsteadOfPropagatingEmptyResult()
    {
        var expr = new Expr.Binary(
            BinaryOp.Mul,
            new Expr.Num(10),
            new Expr.Call(
                new Expr.Resolve("if"),
                new Algorithm.User(
                    Parent: null,
                    Parameters: [],
                    Opens: [],
                    Properties: [],
                    Output:
                    [
                        new Expr.Binary(BinaryOp.Lt, new Expr.Num(7), new Expr.Num(6)),
                        new Expr.Num(1),
                    ])));

        var result = Evaluator.Run(expr);
        if (result.IsOk)
            Assert.Fail($"Expected evaluation failure but got: {result.Value}");

        var formatted = KatLangError.FromEvalError(result.Error).Message;
        Assert.Equal(
            "Callable `if(condition, whenTrue, whenFalse)` expects 3 arguments, but was called with 2 arguments.",
            formatted);
    }

    // ── Clause definitions and conditional algorithms ───────────────────────

    [Fact]
    public void Eval_ClauseDefinition_KCombinator_OrdinarySingleClause()
    {
        // K(a, b) = a  ⟹  K(10, 20) => 10
        var source = """
            K(a, b) = a
            K(10, 20)
            """;
        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_ClauseDefinition_SecondProjection_OrdinarySingleClause()
    {
        // Verify we can return the second binding too
        var source = """
            Snd(a, b) = b
            Snd(10, 20)
            """;
        AssertEval(source, 20);
    }

    [Fact]
    public void Eval_RepeatedBinder_OrdinaryArgumentsRequireEquality()
    {
        AssertEval(
            """
            F(x, x) = x
            F(1, 1)
            """,
            1);

        var error = GetEvalError(
            """
            F(x, x) = x
            F(1, 2)
            """);
        Assert.IsType<EvalError.BadArity>(Innermost(error!));
    }

    [Fact]
    public void Eval_RepeatedBinder_SequenceValuePatternRequiresEquality()
    {
        AssertEval(
            """
            F((x, x)) = x
            F((1, 1))
            """,
            1);

        var error = GetEvalError(
            """
            F((x, x)) = x
            F((1, 2))
            """);
        Assert.IsType<EvalError.BadArity>(Innermost(error!));
    }

    [Fact]
    public void Eval_RepeatedBinder_AcrossNestedPatternRequiresEquality()
    {
        AssertEval(
            """
            F(x, (x)) = x
            F(1, (1))
            """,
            1);

        var error = GetEvalError(
            """
            F(x, (x)) = x
            F(1, (2))
            """);
        Assert.IsType<EvalError.BadArity>(Innermost(error!));
    }

    [Fact]
    public void Eval_RepeatedBinder_UsesStructuralSequenceValueEquality()
    {
        AssertEval(
            """
            F(x, x) = x
            F((1, 2), (1, 2))
            """,
            1, 2);

        var error = GetEvalError(
            """
            F(x, x) = x
            F((1, 2), (1, 3))
            """);
        Assert.IsType<EvalError.BadArity>(Innermost(error!));
    }

    [Fact]
    public void Eval_RepeatedBinder_RetainsFirstEqualBinding()
    {
        AssertEvalString(
            """
            F(x, x) = x.string
            F(1.0, 1.00)
            """,
            "1.0");
    }

    [Fact]
    public void Eval_RepeatedBinder_AlgorithmOnlyArgumentsReportUnsupportedEquality()
    {
        var error = GetEvalError(
            """
            Inc(x) = x + 1
            ApplySame(f, f) = f(1)
            ApplySame(Inc, Inc)
            """);

        var typeMismatch = Assert.IsType<EvalError.TypeMismatch>(Innermost(error!));
        Assert.Contains("algorithm-only arguments", typeMismatch.Message);
    }

    [Fact]
    public void Eval_RepeatedBinder_ConditionalFallbackSelectsNextClause()
    {
        AssertEval(
            """
            Equal(x, x) = 1
            Equal(x, y) = 0
            Equal(1, 1)
            Equal(1, 2)
            """,
            1, 0);
    }

    [Fact]
    public void Eval_RepeatedBinder_SequenceValueConditionalFallbackSelectsNextClause()
    {
        AssertEval(
            """
            SamePair((x, x)) = 1
            SamePair((x, y)) = 0
            SamePair((5, 5))
            SamePair((5, 6))
            """,
            1, 0);
    }

    [Fact]
    public void Eval_SameParameterNameInSeparateAlgorithms_RemainsIndependent()
    {
        AssertEval(
            """
            A(x) = x
            B(x) = x + 1
            A(4)
            B(4)
            """,
            4, 5);
    }

    [Fact]
    public void Eval_OrdinarySingletonGroupParameter_RejectsMultiItemGroup()
    {
        // K(a, (b)) = a  ⟹  K(1, (2, 3)) should fail
        // because (b) is a 1-element sequence-value pattern that does not match (2, 3).
        var source = """
            K(a, (b)) = a
            K(1, (2, 3))
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);
        Assert.IsType<EvalError.WithContext>(error);
        var inner = ((EvalError.WithContext)error!).Inner;
        Assert.True(inner is EvalError.ArityMismatch or EvalError.BadArity);
    }

    [Fact]
    public void Eval_ClauseDefinition_OrdinarySingleClause_AcceptsSequenceValueSecondArgument()
    {
        // K(a, b) = a  ⟹  K(1, (2, 3)) => 1
        // Ordinary call binding still accepts a sequence-value second argument as one value.
        var source = """
            K(a, b) = a
            K(1, (2, 3))
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_OrdinarySingletonGroupParameter_MatchesNormalizedSingleton()
    {
        // K(a, (b)) = a  ⟹  K(1, (2)) => 1
        // (2) normalizes to Atom(2); (b) is a 1-element sequence-value pattern
        // that matches the normalized singleton.
        var source = """
            K(a, (b)) = a
            K(1, (2))
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Conditional_MultipleBranches_LiteralMatch()
    {
        // Else(1, (a, b)) = a
        // Else(c, (a, b)) = b
        var source = """
            Else(1, (a, b)) = a
            Else(c, (a, b)) = b
            Else(1, (2, 3))
            """;
        AssertEval(source, 2);
    }

    [Fact]
    public void Eval_Conditional_MultipleBranches_FallbackBranch()
    {
        // Same as above but first branch doesn't match (c != 1)
        var source = """
            Else(1, (a, b)) = a
            Else(c, (a, b)) = b
            Else(0, (2, 3))
            """;
        AssertEval(source, 3);
    }

    [Fact]
    public void Eval_Conditional_NonExhaustive_NoMatch()
    {
        // Sign(1) = 1
        // Sign(-1) = -1
        // Sign(0) should fail with NoMatchingBranch
        var source = """
            Sign(1) = 1
            Sign(-1) = -1
            Sign(0)
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);
        Assert.IsType<EvalError.WithContext>(error);
        var inner = ((EvalError.WithContext)error!).Inner;
        Assert.IsType<EvalError.NoMatchingBranch>(inner);
    }

    [Fact]
    public void Eval_Conditional_NonExhaustive_MatchExists()
    {
        var source = """
            Sign(1) = 100
            Sign(-1) = -100
            Sign(1)
            """;
        AssertEval(source, 100);
    }

    [Fact]
    public void Eval_Conditional_BareReference_NoMatchingBranch()
    {
        // A bare property-style reference to a clause family cannot select a
        // branch; it must fail like no-argument dot-call access instead of
        // silently forcing the conditional's empty output list.
        var source = """
            Sign(1) = 1
            Sign(-1) = -1
            Sign
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);
        Assert.IsType<EvalError.NoMatchingBranch>(Innermost(error!));
    }

    [Fact]
    public void Eval_Conditional_BareReferenceInSequenceBuiltinArg_NoMatchingBranch()
    {
        // Forcing a conditional through a sequence-builtin collection argument
        // fails instead of silently contributing nothing to the collection.
        var source = """
            Sign(1) = 1
            Sign(-1) = -1
            sum(Sign)
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);
        Assert.IsType<EvalError.NoMatchingBranch>(Innermost(error!));
    }

    [Fact]
    public void Eval_Conditional_HigherOrderThunkReference_NoMatchingBranch()
    {
        // A conditional bound as a higher-order argument fails when the callee
        // references it as a bare zero-argument thunk.
        var source = """
            Sign(1) = 1
            Sign(-1) = -1
            Apply = f
            Apply(Sign)
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);
        Assert.IsType<EvalError.NoMatchingBranch>(Innermost(error!));
    }

    [Fact]
    public void Eval_Conditional_FirstMatchWins()
    {
        // F(x) = 1  (catch-all, always matches)
        // F(1) = 2  (never reached)
        // F(1) => 1 (first branch wins)
        var source = """
            F(x) = 1
            F(1) = 2
            F(1)
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_Conditional_NestedPatternShapeMismatch()
    {
        // Else expects (c, (a, b)) but we pass three flat args
        var source = """
            Else(1, (a, b)) = a
            Else(c, (a, b)) = b
            Else(1, 2, 3)
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);
        Assert.IsType<EvalError.WithContext>(error);
        var inner = ((EvalError.WithContext)error!).Inner;
        Assert.IsType<EvalError.NoMatchingBranch>(inner);
    }

    [Fact]
    public void Eval_Conditional_OrdinaryAlgorithmUnchanged()
    {
        // Ordinary (non-conditional) algorithms should still work
        var source = """
            Add = a + b
            Add(3, 4)
            """;
        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_Conditional_BinderUsedInExpression()
    {
        // Branch body can use binders in arithmetic
        var source = """
            Double(x) = x + x
            Double(5)
            """;
        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Conditional_NegativeLiteralPattern()
    {
        var source = """
            F(-1) = 100
            F(x) = 0
            F(-1)
            """;
        AssertEval(source, 100);
    }

    [Fact]
    public void Eval_Conditional_NegativeLiteralPattern_NoMatch()
    {
        var source = """
            F(-1) = 100
            F(x) = 0
            F(5)
            """;
        AssertEval(source, 0);
    }

    [Fact]
    public void Eval_Conditional_MultipleOutputInBranch()
    {
        // Branch body returns multiple values
        var source = """
            Swap(a, b) = b, a
            Swap(1, 2)
            """;
        AssertEval(source, 2, 1);
    }

    [Fact]
    public void Eval_Conditional_DirectCountedCall_PreservesSelectedBranchOutputCount()
    {
        var source = """
            Choose(1) = 10, 20
            Choose(x) = x, x
            Choose(1).count
            """;

        AssertEval(source, 2);
    }

    [Fact]
    public void Eval_Conditional_DotCallAccess()
    {
        // Access conditional property via dot syntax with args
        var source = """
            M = (F(x) = x + 1
            F)
            M.F(10)
            """;
        AssertEval(source, 11);
    }

        [Fact]
        public void Eval_PublicConditional_DotCallAccess()
        {
            var source = """
                Lib = (
                    public Sign(1) = 100
                    public Sign(x) = 0
                )
                Lib.Sign(1), Lib.Sign(2)
                """;

            AssertEval(source, 100, 0);
        }

    [Fact]
    public void Eval_Conditional_SingleArg()
    {
        // Single argument pattern
        var source = """
            Inc(x) = x + 1
            Inc(5)
            """;
        AssertEval(source, 6);
    }

    // ── Regression: conditional branch body accesses enclosing scope (issue #19) ──

    [Fact]
    public void Eval_Conditional_BranchBody_AccessesSiblingProperty()
    {
        // Branch bodies must be able to read sibling properties of the enclosing algorithm.
        // Before the fix, branch.Body had no parent wiring → UnknownName for Price.
        var source = """
            Price = 0.80
            Discount(1) = Price * 0.9
            Discount(x) = Price
            Discount(1)
            """;
        AssertEval(source, 0.72m);
    }

    [Fact]
    public void Eval_Conditional_BranchBody_AccessesSiblingProperty_AllBranches()
    {
        // Verify every branch (not just the first) can access sibling properties.
        var source = """
            TomatoPrice = 1.20
            ApplePrice = 0.80
            CucumberPrice = 0.60
            Expense(1, qty) = TomatoPrice * qty
            Expense(2, qty) = ApplePrice * qty
            Expense(3, qty) = CucumberPrice * qty
            Expense(1, 10), Expense(2, 10), Expense(3, 10)
            """;
        AssertEval(source, 12.0m, 8.0m, 6.0m);
    }

    [Fact]
    public void Eval_Conditional_BranchBody_AccessesGrandparentProperty()
    {
        // Sibling properties defined one level higher than the conditional algorithm
        // must also be reachable from branch bodies.
        var source = """
            Outer = {
                Price = 2.50
                Inner = {
                    F(x) = Price * x
                    F(4)
                }
                Inner
            }
            Outer
            """;
        AssertEval(source, 10.0m);
    }

    [Fact]
    public void Eval_Conditional_BranchBody_BinderAndSiblingCombined()
    {
        // Branch body uses both a pattern binder (qty) and a sibling property (Rate).
        var source = """
            Rate = 1.5
            Scale(qty) = Rate * qty
            Scale(4)
            """;
        AssertEval(source, 6.0m);
    }

    // ── Full-input-specification rule: conditional branch params ─────────

    [Fact]
    public void Eval_ClauseDefinition_OrdinarySingleClause_IgnoredBinderPreserved()
    {
        // K(a, b) = a — b is intentionally unused, no error
        var source = """
            K(a, b) = a
            K(10, 20)
            """;
        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Conditional_FullPattern_StructuredBranches()
    {
        // Each branch pattern fully describes accepted input shape
        var source = """
            Else(1, (a, b)) = a
            Else(c, (a, b)) = b
            Else(1, (20, 30))
            """;
        AssertEval(source, 20);
    }

    [Fact]
    public void Eval_Conditional_FullPattern_CatchAllBranch()
    {
        var source = """
            Else(1, (a, b)) = a
            Else(c, (a, b)) = b
            Else(0, (20, 30))
            """;
        AssertEval(source, 30);
    }

    [Fact]
    public void Eval_Conditional_ExtraImplicitParam_Rejected()
    {
        // F(1, a) = a + b — b is not bound by pattern and not a resolved name
        // This must fail because b is not a pattern binder and not lexically resolvable.
        var source = """
            F(1, a) = a + b
            F(1, 5)
            """;
        var error = GetEvalError(source);
        Assert.NotNull(error);
    }

    [Fact]
    public void Eval_Conditional_FreeIdResolvedLexically_Succeeds()
    {
        // Pattern binder + lexically resolvable name: Rate is a sibling property
        var source = """
            Rate = 2
            F(x) = x * Rate
            F(5)
            """;
        AssertEval(source, 10);
    }

    [Fact]
    public void Eval_Conditional_OrdinaryAlgorithmStillInfersParams()
    {
        // Ordinary (non-conditional) algorithms still infer implicit parameters
        var source = """
            Add = a + b
            Add(3, 4)
            """;
        AssertEval(source, 7);
    }

    [Fact]
    public void Eval_Conditional_OrdinaryAlgorithmGraceStillWorks()
    {
        // Grace still works in ordinary algorithms
        var source = """
            Sub = a - ~b
            Sub(3, 10)
            """;
        AssertEval(source, 7);
    }

    // ── Uniform top-level output arity: valid multi-output branches ─────

    [Fact]
    public void Eval_Conditional_SameOutputArity2_BothBranches()
    {
        // Both branches return top-level arity 2 — valid
        var source = """
            F(1, x) = x, x + 1
            F(2, x) = 0, x
            F(1, 5)
            """;
        AssertEval(source, 5, 6);
    }

    [Fact]
    public void Eval_Conditional_SameOutputArity2_SecondBranch()
    {
        // Second branch matches, also returns arity 2
        var source = """
            F(1, x) = x, x + 1
            F(2, x) = 0, x
            F(2, 5)
            """;
        AssertEval(source, 0, 5);
    }

    [Fact]
    public void Eval_Conditional_SameOutputArity1_WithSiblingProperties()
    {
        // Classic example: same output arity 1 across branches with sibling properties
        var source = """
            TomatoPrice = 1.20
            ApplePrice = 0.80
            Expense(1, qty) = TomatoPrice * qty
            Expense(2, qty) = ApplePrice * qty
            Expense(1, 10)
            """;
        AssertEval(source, 12.0m);
    }

    [Fact]
    public void Eval_Conditional_SameOutputArity2_NestedStructureDiffers()
    {
        // Both branches return top-level arity 2; nested internal structure differs — valid
        var source = """
            G(1, x) = x, (x + 1, x + 2)
            G(2, x) = x, x * 2
            G(1, 10)
            """;
        AssertEval(source, 10, 11, 12);
    }

    // ── Additional conditional algorithm tests ──────────────────────────────

    [Fact]
    public void Eval_Conditional_DefinitionAndCallDisambiguated()
    {
        // First two lines: definitions; third line: call
        var source = """
            F(1) = 100
            F(x) = 0
            F(1)
            """;
        AssertEval(source, 100);
    }

    [Fact]
    public void Eval_Conditional_CallInExpressionContext()
    {
        // G = F(1) is a property definition where F(1) is a call expression
        var source = """
            F(1) = 100
            F(x) = 0
            G = F(1)
            G
            """;
        AssertEval(source, 100);
    }

    [Fact]
    public void Eval_ConditionalSugar_FirstMatchWins()
    {
        var source = """
            F(x) = 1
            F(1) = 2
            F(1)
            """;
        AssertEval(source, 1);
    }

    [Fact]
    public void Eval_ConditionalSugar_ExtraImplicitParam_Rejected()
    {
        // b is not bound in the pattern; should be rejected
        var source = """
            F(1, a) = a + b
            F(2, a) = a
            F(1, 5)
            """;
        var parseResult = Parser.Parse(source);
        Assert.True(parseResult.HasErrors);
        Assert.Contains(parseResult.Diagnostics, d =>
            d.Message.Contains("Identifier 'b' is used in conditional branch 'F'") &&
            d.Message.Contains("not declared in the branch pattern") &&
            d.Message.Contains("A(y) = y"));
    }

    [Fact]
    public void Eval_Conditional_ClauseSyntax_MultipleCallResults()
    {
        // Clause-style branch syntax works for multiple calls
        var source = """
            F(1) = 100
            F(x) = 0
            F(1), F(42)
            """;
        AssertEval(source, 100, 0);
    }

    // ── String literals: first-class value tests ────────────────────────────

    [Fact]
    public void Eval_String_SimpleLiteral()
    {
        AssertEvalString("'hello'", "hello");
    }

    [Fact]
    public void Eval_String_EmptyLiteral()
    {
        AssertEvalString("''", "");
    }

    [Fact]
    public void Eval_String_PropertyBinding()
    {
        AssertEvalString("""
            A = 'hello'
            A
            """, "hello");
    }

    [Fact]
    public void Eval_String_EqualityTrue()
    {
        AssertEval("'a' == 'a'", 1);
    }

    [Fact]
    public void Eval_String_EqualityFalse()
    {
        AssertEval("'a' == 'b'", 0);
    }

    [Fact]
    public void Eval_String_EqualityCaseSensitive()
    {
        // 'Apples' != 'apples' — exact, case-sensitive comparison
        AssertEval("'Apples' == 'apples'", 0);
    }

    [Fact]
    public void Eval_String_Inequality()
    {
        AssertEval("'a' != 'b'", 1);
    }

    [Fact]
    public void Eval_String_InequalitySame()
    {
        AssertEval("'a' != 'a'", 0);
    }

    [Fact]
    public void Eval_String_ArgumentCall()
    {
        // Echo = x, Echo('hello') should return the string
        AssertEvalString("""
            Echo = x
            Echo('hello')
            """, "hello");
    }

    [Fact]
    public void Eval_String_ConditionalDispatch()
    {
        AssertEval("""
            Price('apples') = 0.80
            Price('apples')
            """, 0.80m);
    }

    [Fact]
    public void Eval_String_ConditionalDispatch_MultiBranch()
    {
        AssertEval("""
            Price('tomatoes') = 1.20
            Price('apples') = 0.80
            Price('cucumbers') = 0.60
            Price('cucumbers')
            """, 0.60m);
    }

    [Fact]
    public void Eval_String_ConditionalDispatch_IndirectCall()
    {
        // Item = 'apples', Price('apples') = 0.80, Price(Item) should resolve
        AssertEval("""
            Item = 'apples'
            Price('apples') = 0.80
            Price(Item)
            """, 0.80m);
    }

    [Fact]
    public void Eval_String_ReturnFromAlgorithm()
    {
        AssertEvalString("""
            Name = 'KatLang'
            Name
            """, "KatLang");
    }

    [Fact]
    public void Eval_String_ConditionalExpense()
    {
        // Full example from spec: Price('apples') = 0.80, Expense = Price(item) * quantity
        AssertEval("""
            Price('tomatoes') = 1.20
            Price('apples') = 0.80
            Price('cucumbers') = 0.60
            Expense = Price(item) * quantity
            Expense('apples', 3)
            """, 2.40m);
    }

    [Fact]
    public void Eval_String_ConditionalNoMatch_Fails()
    {
        // Unmatched branch fails with NoMatchingBranch, not a crash
        AssertEvalFails("""
            Price('apples') = 0.80
            Price('bananas')
            """);
    }

    [Fact]
    public void Eval_String_MixedBranches_NumericAndString()
    {
        // Conditional with both numeric and string literal patterns
        AssertEval("""
            F('a') = 1
            F(0) = 2
            F('a')
            """, 1);
    }

    [Fact]
    public void Eval_String_MixedBranches_NumericAndString_MatchNumeric()
    {
        AssertEval("""
            F('a') = 1
            F(0) = 2
            F(0)
            """, 2);
    }

    [Fact]
    public void Eval_String_BinderFallbackAfterStringLiteral()
    {
        // Binder pattern as fallback after string literal patterns
        AssertEval("""
            F('a') = 1
            F(x) = 0
            F('b')
            """, 0);
    }

    // ── String literals: negative/error tests ───────────────────────────────

    [Fact]
    public void Eval_String_MultiplyFails()
    {
        // 'a' * 3 should fail (strings don't support arithmetic)
        AssertEvalFailsWithTypeMismatch("'a' * 3", "string and non-string");
    }

    [Fact]
    public void Eval_String_AddNumberFails()
    {
        // 1 + 'a' should fail (mixed types)
        AssertEvalFailsWithTypeMismatch("1 + 'a'", "string and non-string");
    }

    [Fact]
    public void Eval_String_AddStringsFails()
    {
        // 'a' + 'b' should fail (no string concatenation)
        AssertEvalFailsWithTypeMismatch("'a' + 'b'", "only support == and !=");
    }

    [Fact]
    public void Eval_String_UnaryMinusFails()
    {
        // Unary minus on a string literal should fail
        var strExpr = new Expr.StringLiteral("hello");
        var unaryExpr = new Expr.Unary(UnaryOp.Minus, strExpr);
        var alg = new Algorithm.User(Parent: null, Parameters: [], Opens: [],
            Properties: [], Output: [unaryExpr]);
        var result = Evaluator.Run(new Expr.Block(alg));
        Assert.True(result.IsError);
        var error = result.Error;
        while (error is EvalError.WithContext wc) error = wc.Inner;
        var tm = Assert.IsType<EvalError.TypeMismatch>(error);
        Assert.Contains("not supported for strings", tm.Message);
    }

    [Fact]
    public void Eval_String_ComparisonLtFails()
    {
        // 'a' < 'b' should fail (no string ordering)
        AssertEvalFailsWithTypeMismatch("'a' < 'b'", "only support == and !=");
    }

    [Fact]
    public void Eval_String_MixedEquality_DifferentKinds_ReturnsZero()
    {
        // `==` compares values structurally; a number and a string are different
        // value kinds, so they compare unequal (0) rather than raising a type
        // mismatch. Arithmetic/ordering on mixed string operands still fails.
        AssertEval("1 == 'a'", 0);
    }

    [Fact]
    public void Eval_String_MixedInequality_DifferentKinds_ReturnsOne()
        => AssertEval("1 != 'a'", 1);

    [Fact]
    public void Eval_String_SinFails()
    {
        // Math.Sin('a') should fail with type mismatch (builtin expects numeric argument)
        AssertEvalFailsWithTypeMismatch("Math.Sin('a')", "Expected a number, got a string");
    }

    // ── Top-level unresolved implicit parameters ──

    [Fact]
    public void Eval_TopLevel_SingleImplicitParam_ErrorMessage()
    {
        var result = EvalFull("a + 1");
        if (result.IsOk)
            Assert.Fail($"Expected error but got: {result.Value}");
        var error = result.Error;
        var contextual = Assert.IsType<EvalError.WithContext>(error);
        var implicitContext = Assert.IsType<ImplicitParameterContext>(contextual.ErrorContext);
        Assert.Equal(["a"], implicitContext.ParamNames);
        Assert.Equal(0, implicitContext.ProvidedArgumentCount);

        var uip = Assert.IsType<EvalError.UnresolvedImplicitParams>(contextual.Inner);
        Assert.Equal(["a"], uip.ParamNames);
        var formatted = KatLangError.FromEvalError(error).Message;
        Assert.Contains("Identifier 'a' does not resolve to a property or other visible name here", formatted);
        Assert.Contains("KatLang interprets it as an implicit parameter", formatted);
        Assert.Contains("Its value is provided by the caller", formatted);
        Assert.Contains("No argument was provided", formatted);
        Assert.Contains("expected 1 argument, got 0", formatted);
        Assert.DoesNotContain("not defined in the current scope", formatted);
    }

    [Fact]
    public void Eval_TopLevel_MultipleImplicitParams_ErrorMessage()
    {
        var result = EvalFull("a + b");
        if (result.IsOk)
            Assert.Fail($"Expected error but got: {result.Value}");
        var error = result.Error;
        var contextual = Assert.IsType<EvalError.WithContext>(error);
        var implicitContext = Assert.IsType<ImplicitParameterContext>(contextual.ErrorContext);
        Assert.Equal(["a", "b"], implicitContext.ParamNames);
        Assert.Equal(0, implicitContext.ProvidedArgumentCount);

        var uip = Assert.IsType<EvalError.UnresolvedImplicitParams>(contextual.Inner);
        Assert.Equal(2, uip.ParamNames.Count);
        var formatted = KatLangError.FromEvalError(error).Message;
        Assert.Contains("Identifiers 'a' and 'b' do not resolve to properties or other visible names here", formatted);
        Assert.Contains("KatLang interprets them as implicit parameters", formatted);
        Assert.Contains("Their values are provided by the caller", formatted);
        Assert.Contains("No arguments were provided", formatted);
        Assert.Contains("expected 2 arguments, got 0", formatted);
        Assert.DoesNotContain("not defined in the current scope", formatted);
    }

    [Fact]
    public void Eval_InnerCall_ArityMismatch_StillGeneric()
    {
        // A normal arity mismatch inside a call (too many args) should NOT be UnresolvedImplicitParams
        var source = """
            G(x) = x + 1
            G(1, 2)
            """;
        var result = EvalFull(source);
        if (result.IsOk)
            Assert.Fail($"Expected error but got: {result.Value}");
        var error = result.Error;
        while (error is EvalError.WithContext wc)
            error = wc.Inner;
        Assert.IsNotType<EvalError.UnresolvedImplicitParams>(error);
    }
}
