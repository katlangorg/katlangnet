using System.Text;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// Optimizer-transparency regressions for a PLANNED <c>if</c> inside an optimized
/// loop.
///
/// <para>The loop optimizer plans <c>if(cond, a, b)</c> into
/// <c>LoopExprPlan.If</c> and evaluates it directly, which dropped the
/// <c>while evaluating call to if</c> frame the generic evaluator (and Lean)
/// attach at the ordinary <c>if</c> call boundary. The reported reproducer
/// <c>S(n) = if(n &lt; 3, n + 1, 1 / 0)</c> / <c>repeat(S, 5, 1)</c> produced
/// "while evaluating call to repeat: Division by zero" with the optimizer on and
/// "while evaluating call to repeat: while evaluating call to if: Division by
/// zero" with it off.</para>
///
/// <para>The loop optimizer is a C#-only execution strategy over the generic Lean
/// loop semantics (see <c>src/KatLang/SEMANTIC-ALIGNMENT.md</c>, row "Optimized
/// loops": no Lean update, equivalence tests required), so its contract is pinned
/// here as exact optimized-vs-generic diagnostic equivalence — error kind,
/// complete context chain, and span — never by relaxing either side.</para>
/// </summary>
public class LoopPlannedIfDiagnosticParityTests
{
    private static Expr Program(string source) => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private static EvalResult<Result> Run(string source, bool enableLoopOptimization)
        => Evaluator.Run(
            Program(source),
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization);

    private static (
        EvalResult<Result> Result,
        LoopOptimizationDiagnosticsSnapshot Loop,
        ZeroArgPropertyResultCacheSnapshot Cache) RunObserved(string source, bool enableLoopOptimization)
    {
        var cache = new RunScopedZeroArgPropertyResultCache();
        var loopDiagnostics = new LoopOptimizationDiagnostics();
        var result = Evaluator.Run(Program(source), cache, enableLoopOptimization, loopDiagnostics);
        return (result, loopDiagnostics.GetSnapshot(), cache.GetSnapshot());
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        return error;
    }

    /// <summary>Ordered outermost-to-innermost legacy context spellings.</summary>
    private static IReadOnlyList<string> ContextChain(EvalError error)
    {
        var chain = new List<string>();
        while (error is EvalError.WithContext context)
        {
            chain.Add(context.ErrorContext.ToLegacyString());
            error = context.Inner;
        }

        return chain;
    }

    /// <summary>
    /// Field-wise projection of a cache snapshot. The snapshot record holds an ARRAY
    /// of per-access-kind counters, so record equality would compare that array by
    /// reference; this compares the counters themselves.
    /// </summary>
    private static string CacheCounters(ZeroArgPropertyResultCacheSnapshot snapshot)
        => string.Join(
            "|",
            [
                $"requests={snapshot.TotalRequests}",
                $"hits={snapshot.Hits}",
                $"misses={snapshot.Misses}",
                $"stores={snapshot.Stores}",
                $"keys={snapshot.DistinctKeysCreated}",
                $"repeatedMisses={snapshot.RepeatedMissRequests}",
                $"maxSize={snapshot.MaxCacheSize}",
                .. snapshot.AccessKinds.Select(static access =>
                    $"{access.AccessKind}(r={access.Requests},h={access.Hits},m={access.Misses},s={access.Stores})"),
            ]);

    private static (int? StartLine, int? StartColumn, int? EndLine, int? EndColumn) Span(EvalError error)
    {
        var rendered = KatLangError.FromEvalError(error);
        return (rendered.StartLine, rendered.StartColumn, rendered.EndLine, rendered.EndColumn);
    }

    // ── Structured error-tree normalization ──────────────────────────────────
    //
    // The whole EvalError tree is publicly observable (Evaluator.Run exposes the
    // structured error, and EvalError.WithContext.Inner.Span is public state), so
    // optimizer transparency has to hold NODE BY NODE, not just for the rendered
    // message and the outermost span. Record equality is not reliable across the
    // hierarchy (some payloads are IReadOnlyList references), so equality is
    // asserted over a normalized recursive description that captures, per node:
    // the exact runtime type, span presence and all four coordinates, the full
    // context payload of WithContext frames, and every type-specific payload.
    // Unknown variants/contexts fail loudly instead of comparing as equal.

    private static string DescribeErrorTree(EvalError error)
    {
        var builder = new StringBuilder();
        AppendErrorNode(builder, error, 0);
        return builder.ToString();
    }

    private static void AppendErrorNode(StringBuilder builder, EvalError error, int depth)
    {
        builder.Append(' ', depth * 2);
        builder.Append(error.GetType().Name);
        builder.Append(" span=").Append(SpanText(error.Span));

        if (error is EvalError.WithContext context)
        {
            builder.Append(" context=").Append(DescribeContext(context.ErrorContext));
            builder.AppendLine();
            AppendErrorNode(builder, context.Inner, depth + 1);
            return;
        }

        builder.Append(' ').Append(DescribeLeafPayload(error));
        builder.AppendLine();
    }

    private static string SpanText(SourceSpan? span)
        => span is null
            ? "none"
            : $"({span.StartLineNumber},{span.StartColumn})-({span.EndLineNumber},{span.EndColumn})";

    private static string DescribeContext(ErrorContext context)
        => context switch
        {
            TextErrorContext(var message) => $"Text[{message}]",
            PropertyEvaluationContext(var propertyName) => $"Property[{propertyName}]",
            ProgramEvaluationContext => "Program[]",
            DotCallContext(var receiver, var propertyName) => $"DotCall[{receiver}|{propertyName}]",
            CallContext(var callee) => $"Call[{callee}]",
            ReduceInitialAccumulatorContext(var requiredNames) =>
                $"ReduceInitialAccumulator[{string.Join(",", requiredNames)}]",
            LoopStateBindingContext(var loopName, var stepParams, var actualCount) =>
                $"LoopStateBinding[{loopName}|{string.Join(",", stepParams)}|{actualCount}]",
            VariadicLoopStateBindingContext(var loopName, var stepParams, var expectedMin, var actualCount) =>
                $"VariadicLoopStateBinding[{loopName}|{string.Join(",", stepParams)}|{expectedMin}|{actualCount}]",
            DeconstructionBindingContext(var targets, var hasCollecting) =>
                $"DeconstructionBinding[{string.Join(",", targets)}|{hasCollecting}]",
            SequenceValueParameterBindingContext(var patternDisplayName, var hasCollectingItem) =>
                $"SequenceValueParameterBinding[{patternDisplayName}|{hasCollectingItem}]",
            OpenResolutionContext(var openDescription) => $"Open[{openDescription}]",
            ImplicitParameterContext(var paramNames, var providedCount) =>
                $"ImplicitParameter[{string.Join(",", paramNames)}|{providedCount}]",
            _ => throw new Xunit.Sdk.XunitException(
                $"DescribeContext does not handle context kind '{context.GetType().Name}'; extend it so structured comparisons stay faithful."),
        };

    private static string DescribeLeafPayload(EvalError error)
        => error switch
        {
            EvalError.UnknownName(var name) => $"[{name}]",
            EvalError.UnknownProperty(var objectDesc, var propertyName) => $"[{objectDesc}|{propertyName}]",
            EvalError.NotPublicProperty(var objectDesc, var propertyName) => $"[{objectDesc}|{propertyName}]",
            EvalError.LocalOnlyProperty(var objectDesc, var propertyName, var exposure) => $"[{objectDesc}|{propertyName}|{exposure}]",
            EvalError.NotAnAlgorithm(var description) => $"[{description}]",
            EvalError.IllegalInOpen(var reason) => $"[{reason}]",
            EvalError.BadOpenForm(var reason) => $"[{reason}]",
            EvalError.IllegalInEval(var reason) => $"[{reason}]",
            EvalError.AmbiguousOpen(var name, var providers) => $"[{name}|{string.Join(",", providers)}]",
            EvalError.ArityMismatch(var expected, var actual) { Signature: var signature } =>
                $"[{expected}|{actual}|{signature?.DisplayText ?? "-"}]",
            EvalError.VariadicArityMismatch(var calleeName, var expectedMinimum, var actual) { Signature: var signature } =>
                $"[{calleeName}|{expectedMinimum}|{actual}|{signature?.DisplayText ?? "-"}]",
            EvalError.TypeMismatch(var message) => $"[{message}]",
            EvalError.NoMatchingBranch(var algorithmName) => $"[{algorithmName}]",
            EvalError.BranchArityMismatch(var algorithmName, var expected, var actual) => $"[{algorithmName}|{expected}|{actual}]",
            EvalError.BranchOutputArityMismatch(var algorithmName, var expected, var actual) => $"[{algorithmName}|{expected}|{actual}]",
            EvalError.DuplicateProperty(var name) => $"[{name}]",
            EvalError.UnresolvedImplicitParams(var paramNames) => $"[{string.Join(",", paramNames)}]",
            EvalError.EvaluationDepthExceeded(var limit) => $"[{limit}]",
            EvalError.EvaluationStepLimitExceeded(var limit) => $"[{limit}]",
            EvalError.CollectionSizeLimitExceeded(var limit, var requested) => $"[{limit}|{requested}]",
            EvalError.MaterializationLimitExceeded(var limit) => $"[{limit}]",
            EvalError.StringSizeLimitExceeded(var limit, var requested) => $"[{limit}|{requested}]",
            EvalError.StringMaterializationLimitExceeded(var limit) => $"[{limit}]",
            EvalError.DisplayLengthLimitExceeded(var limit) => $"[{limit}]",
            EvalError.AstDepthLimitExceeded(var limit) => $"[{limit}]",
            EvalError.BadArity
                or EvalError.BadIndex
                or EvalError.DivByZero
                or EvalError.DuplicateBranchPattern
                or EvalError.ExplicitParametersRequireOutput
                or EvalError.MissingOutput
                or EvalError.SpreadMissingOutput
                or EvalError.EvaluationStackExhausted
                or EvalError.AstCycleDetected => "[]",
            _ => throw new Xunit.Sdk.XunitException(
                $"DescribeLeafPayload does not handle error kind '{error.GetType().Name}'; extend it so structured comparisons stay faithful."),
        };

    /// <summary>
    /// The complete observable diagnostic of an optimization-eligible failing
    /// program must be identical with the optimizer on and off: the ENTIRE
    /// structured error tree node by node (types, per-node spans, context
    /// payloads, type-specific payloads), plus the rendered message and span.
    /// </summary>
    private static EvalError AssertOptimizerTransparentFailure(string source)
    {
        var generic = Run(source, enableLoopOptimization: false);
        Assert.True(generic.IsError, $"Expected generic failure but got: {(generic.IsError ? null : generic.Value)}");

        var optimized = Run(source, enableLoopOptimization: true);
        Assert.True(optimized.IsError, $"Expected optimized failure but got: {(optimized.IsError ? null : optimized.Value)}");

        Assert.Equal(Innermost(generic.Error).GetType(), Innermost(optimized.Error).GetType());
        Assert.Equal(ContextChain(generic.Error), ContextChain(optimized.Error));
        Assert.Equal(
            KatLangError.FromEvalError(generic.Error).Message,
            KatLangError.FromEvalError(optimized.Error).Message);
        Assert.Equal(Span(generic.Error), Span(optimized.Error));
        Assert.Equal(DescribeErrorTree(generic.Error), DescribeErrorTree(optimized.Error));

        return optimized.Error;
    }

    // ── The reported reproducer ──────────────────────────────────────────────

    [Fact]
    public void Repeat_PlannedIf_FalseBranchDivisionByZero_KeepsIfCallContextFrame()
    {
        var source = """
            S(n) = if(n < 3, n + 1, 1 / 0)
            repeat(S, 5, 1)
            """;

        var error = AssertOptimizerTransparentFailure(source);

        Assert.IsType<EvalError.DivByZero>(Innermost(error));
        Assert.Equal(
            ["while evaluating call to repeat", "while evaluating call to if"],
            ContextChain(error));
        Assert.Equal(
            "while evaluating call to repeat: while evaluating call to if: Division by zero",
            KatLangError.FromEvalError(error).Message);
    }

    [Fact]
    public void Repeat_PlannedIf_ReproducerUsesThePlannedIfPath()
    {
        // Proves the regression above really exercised LoopExprPlan.If rather than
        // an incidental generic fallback: the loop is optimized, the whole step
        // output is planned as an `If(...)`, and nothing inside it fell back to the
        // generic evaluator.
        var source = """
            S(n) = if(n < 3, n + 1, 1 / 0)
            repeat(S, 5, 1)
            """;

        var (result, loop, _) = RunObserved(source, enableLoopOptimization: true);

        Assert.True(result.IsError);
        Assert.Equal(1, loop.OptimizedLoopHits);
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);

        var plan = Assert.Single(loop.LoopPlans, candidate => candidate.Identity == "S.repeat");
        Assert.True(plan.Optimized, $"Expected an optimized plan, got fallback: {plan.FallbackReason}");
        var output = Assert.Single(plan.Expressions, expression => expression.Role == "output" && expression.Index == 0);
        Assert.True(output.Planned);
        Assert.Equal(
            "If(LessThan(StateSlot(n), Const(3)), Add(StateSlot(n), Const(1)), Divide(Const(1), Const(0)))",
            output.PlanSummary);
    }

    // ── Every logical failure position of a planned `if` ─────────────────────

    public static TheoryData<string, string> PlannedIfFailurePositions()
    {
        var data = new TheoryData<string, string>();

        // Condition failure.
        data.Add(
            "condition",
            """
            S(n) = if(1 / 0, n + 1, n)
            repeat(S, 5, 1)
            """);

        // Selected TRUE branch failure (n starts at 1, so the first iteration takes it).
        data.Add(
            "selected true branch",
            """
            S(n) = if(n < 3, 1 / 0, n)
            repeat(S, 5, 1)
            """);

        // Selected FALSE branch failure (taken once n reaches 3).
        data.Add(
            "selected false branch",
            """
            S(n) = if(n < 3, n + 1, 1 / 0)
            repeat(S, 5, 1)
            """);

        // The `if` itself: a string condition has no truth value.
        data.Add(
            "condition without a truth value",
            """
            S(n) = if('x', n + 1, n)
            repeat(S, 5, 1)
            """);

        return data;
    }

    [Theory]
    [MemberData(nameof(PlannedIfFailurePositions))]
    public void PlannedIf_FailureAtAnyPosition_MatchesGenericDiagnosticExactly(string position, string source)
    {
        Assert.False(string.IsNullOrEmpty(position));

        var error = AssertOptimizerTransparentFailure(source);

        Assert.Equal(
            ["while evaluating call to repeat", "while evaluating call to if"],
            ContextChain(error));
    }

    [Fact]
    public void PlannedIf_InvalidTruthCondition_KeepsBadArityUnspannedInBothStructuredTrees()
    {
        // The `if` truth-value rejection is the one planned failure the plan RAISES
        // itself rather than propagates. The generic builtin returns an UNSPANNED
        // BadArity and lets the surrounding call boundary stamp only the context
        // wrappers, so the planned path must not pre-stamp the innermost error:
        // EvalError.WithContext.Inner.Span is public state, and a spanned innermost
        // BadArity is an observable structured-tree divergence even when the rendered
        // message and outermost span agree.
        var source = """
            S(n) = if('x', n + 1, n)
            repeat(S, 5, 1)
            """;

        // The optimized run really exercises the planned `if` (not a fallback).
        var (optimized, loop, _) = RunObserved(source, enableLoopOptimization: true);
        Assert.True(optimized.IsError);
        Assert.Equal(1, loop.OptimizedLoopHits);
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);
        var plan = Assert.Single(loop.LoopPlans, candidate => candidate.Identity == "S.repeat");
        Assert.True(plan.Optimized, $"Expected an optimized plan, got fallback: {plan.FallbackReason}");
        var output = Assert.Single(plan.Expressions, expression => expression.Role == "output" && expression.Index == 0);
        Assert.True(output.Planned);
        Assert.Equal(
            "If(StringConst(length=1), Add(StateSlot(n), Const(1)), StateSlot(n))",
            output.PlanSummary);

        var generic = Run(source, enableLoopOptimization: false);
        Assert.True(generic.IsError);

        // Complete structured trees are equal, and the innermost BadArity is
        // unspanned on BOTH paths.
        Assert.Equal(DescribeErrorTree(generic.Error), DescribeErrorTree(optimized.Error));
        var genericInnermost = Assert.IsType<EvalError.BadArity>(Innermost(generic.Error));
        var optimizedInnermost = Assert.IsType<EvalError.BadArity>(Innermost(optimized.Error));
        Assert.Null(genericInnermost.Span);
        Assert.Null(optimizedInnermost.Span);

        // The context frames are intact and the enclosing public diagnostic still
        // carries the `if(...)` call expression's span (line 1, columns 8..24).
        Assert.Equal(
            ["while evaluating call to repeat", "while evaluating call to if"],
            ContextChain(optimized.Error));
        Assert.Equal(((int?)1, (int?)8, (int?)1, (int?)24), Span(optimized.Error));
        Assert.Equal(((int?)1, (int?)8, (int?)1, (int?)24), Span(generic.Error));
    }

    [Fact]
    public void PlannedIf_NestedFailingIf_NestsBothCallContextFrames()
    {
        // The inner planned `if` is the operand of the outer planned `if`'s false
        // branch, so the generic composition attaches TWO `if` frames.
        var source = """
            S(n) = if(n < 3, n + 1, if(1, 1 / 0, 0))
            repeat(S, 5, 1)
            """;

        var error = AssertOptimizerTransparentFailure(source);

        Assert.IsType<EvalError.DivByZero>(Innermost(error));
        Assert.Equal(
            [
                "while evaluating call to repeat",
                "while evaluating call to if",
                "while evaluating call to if",
            ],
            ContextChain(error));
    }

    [Fact]
    public void PlannedIf_InsideWhileLoop_AlsoKeepsIfCallContextFrame()
    {
        // The same planned-`if` evaluation serves `while`; its continuation slot is
        // planned too, so pin the loop kind that reaches the plan by a second route.
        var source = """
            S(n) = if(n < 3, n + 1, 1 / 0), n <= 10
            S.while(1):0
            """;

        var error = AssertOptimizerTransparentFailure(source);

        Assert.IsType<EvalError.DivByZero>(Innermost(error));
        Assert.Contains("while evaluating call to if", ContextChain(error));
    }

    [Fact]
    public void PlannedIf_FailureInsideAnEnclosingExpression_KeepsTheInnerFrames()
    {
        // The failing `repeat` sits inside a binary expression inside a property, so
        // several outer evaluator layers run after the planned `if` fails. None of
        // them may replace the `if` frame or re-span the error onto the enclosing
        // line-2 expression.
        var source = """
            S(n) = if(n < 3, n + 1, 1 / 0)
            Total = repeat(S, 5, 1) + 100
            Total
            """;

        var error = AssertOptimizerTransparentFailure(source);

        Assert.IsType<EvalError.DivByZero>(Innermost(error));
        Assert.Equal(
            ["while evaluating call to repeat", "while evaluating call to if"],
            ContextChain(error));

        // The `1 / 0` operand on line 1, not the enclosing line-2 expression.
        var span = Span(error);
        Assert.Equal(1, span.StartLine);
        Assert.Equal(25, span.StartColumn);
        Assert.Equal(1, span.EndLine);
    }

    // ── Preserved behavior: values, laziness, counters, cache ────────────────

    [Fact]
    public void PlannedIf_SuccessfulRuns_AreUnchangedInBothModes()
    {
        // `repeat(S, 2, 1)` never selects the failing false branch, so a lazily
        // evaluated planned `if` succeeds: branch laziness is preserved.
        var source = """
            S(n) = if(n < 3, n + 1, 1 / 0)
            repeat(S, 2, 1)
            """;

        var generic = Run(source, enableLoopOptimization: false);
        Assert.True(generic.IsError == false, $"Expected generic success but got: {(generic.IsError ? generic.Error : null)}");
        Assert.Equal([3m], generic.Value.ToAtoms());

        var optimized = Run(source, enableLoopOptimization: true);
        Assert.True(optimized.IsError == false, $"Expected optimized success but got: {(optimized.IsError ? optimized.Error : null)}");
        Assert.Equal([3m], optimized.Value.ToAtoms());
    }

    [Fact]
    public void PlannedIf_FailingRun_KeepsItsStepCountsAndCacheState()
    {
        // Pins the operational shape of the optimized failing run so adding the
        // missing diagnostic frame cannot change WHEN the loop stops or how much
        // work it does: `n` walks 1 -> 2 -> 3 over two successful iterations and the
        // third iteration selects the failing false branch. The planned-builtin count
        // is one `<`, one `if`, and one `+` per successful iteration, plus the third
        // iteration's `<`, `if`, and failing `/`.
        var source = """
            S(n) = if(n < 3, n + 1, 1 / 0)
            repeat(S, 5, 1)
            """;

        var (result, loop, cache) = RunObserved(source, enableLoopOptimization: true);

        Assert.True(result.IsError);
        Assert.Equal(1, loop.OptimizedLoopHits);
        Assert.Equal(1, loop.LoopPlanBuilds);
        Assert.Equal(3, loop.LoopIterations);
        Assert.Equal(3, loop.PlannedExpressionHits);
        Assert.Equal(0, loop.PlannedExpressionFallbacks);
        Assert.Equal(0, loop.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.Equal(9, loop.PlannedBuiltinOperations);

        // The step is a one-parameter callable, so no zero-argument property cache
        // entry is created on either path; the generic run must agree exactly.
        var (_, _, genericCache) = RunObserved(source, enableLoopOptimization: false);
        Assert.Equal(CacheCounters(genericCache), CacheCounters(cache));
    }
}
